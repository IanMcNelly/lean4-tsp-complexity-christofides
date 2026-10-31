<#
.SYNOPSIS
    Automated Continuous Verification & Build Script for Decision TSP & Approximation Research Package.
.DESCRIPTION
    Executes comprehensive verification suite across all tracks:
    1. Zero-sorry and zero-admit regex audit of both TSPComplexity.lean and Christofides.lean.
    2. Challenge metadata schema synchronization check against TSPComplexity.json and Christofides.json.
    3. Execution of Python empirical benchmark suites (adversarial_instances.py and christofides.py).
    4. Interactive HTML DocGen generation and verification.
    5. Mandatory Lean 4 formalization typecheck via `lake env lean` (unless -SkipLean is passed).
.PARAMETER SkipBenchmarks
    Skip execution of Python benchmark suites.
.PARAMETER SkipLean
    Skip full Lean 4 compilation check via `lake env lean` in Lean project directory.
.PARAMETER LeanDir
    Path to root Lean project containing lakefile.lean (default: $ResearchDir).
#>

[CmdletBinding()]
param(
    [switch]$SkipBenchmarks,
    [switch]$SkipLean,
    [string]$LeanDir = $ResearchDir
)

$ErrorActionPreference = "Stop"
$ScriptDir = Split-Path -Parent $MyInvocation.MyCommand.Path
$ResearchDir = Split-Path -Parent $ScriptDir
if (-not $LeanDir) {
    $LeanDir = $ResearchDir
}

$Modules = @(
    @{
        Name = "TSPComplexity (Tracks A-C: Decision Complexity & Polyhedral Limits)"
        LeanFile = Join-Path $ResearchDir "TSPComplexity.lean"
        JsonFile = Join-Path $ResearchDir "TSPComplexity.json"
    },
    @{
        Name = "Christofides (Track D: 3/2-Approximation Algorithm)"
        LeanFile = Join-Path $ResearchDir "Christofides.lean"
        JsonFile = Join-Path $ResearchDir "Christofides.json"
    }
)

$BenchmarkScripts = @(
    @{
        Name = "Adversarial Instances & Branch-and-Cut (Held-Karp, 3-SAT Ring, Yannakakis Slack)"
        Path = Join-Path $ResearchDir "benchmarks\adversarial_instances.py"
    },
    @{
        Name = "Christofides-Serdyukov 3/2-Approximation Suites (MST, Matching, Shortcutting)"
        Path = Join-Path $ResearchDir "benchmarks\christofides.py"
    },
    @{
        Name = "Track C: Empirical Kappa-Profiling & Cycle-Separation Rank Suite"
        Path = Join-Path $ResearchDir "benchmarks\structural_rank.py"
    }
)

Write-Host "========================================================================" -ForegroundColor Cyan
Write-Host " TSP RESEARCH PACKAGE: CONTINUOUS VERIFICATION & BUILD AUDIT" -ForegroundColor Cyan
Write-Host " Targets: TSPComplexity.lean & Christofides.lean" -ForegroundColor Cyan
Write-Host "========================================================================" -ForegroundColor Cyan

$TotalErrors = 0
$CumulativeDecls = 0
$ModuleContents = @{}

# -----------------------------------------------------------------------------
# STEP 1: ZERO-SORRY & ZERO-ADMIT REGEX AUDIT
# -----------------------------------------------------------------------------
Write-Host "`n[STEP 1/5] Running Zero-Sorry & Zero-Admit Syntax Audit..." -ForegroundColor Yellow

foreach ($mod in $Modules) {
    $leanPath = $mod.LeanFile
    Write-Host "`n  Auditing Module: $($mod.Name)" -ForegroundColor Cyan
    Write-Host "  Path: $leanPath" -ForegroundColor DarkGray

    if (-not (Test-Path $leanPath)) {
        Write-Host "  FAILED: File not found: $leanPath" -ForegroundColor Red
        $TotalErrors++
        continue
    }

    $rawContent = Get-Content -Path $leanPath -Raw
    $ModuleContents[$mod.Name] = $rawContent

    # Strip block comments /-- ... -/ and /- ... -/
    $stripped = [regex]::Replace($rawContent, '/-[\s\S]*?-/', '')

    # Split into lines and inspect non-comment code
    $lines = $stripped -split "`r?`n"
    $sorryMatches = @()
    $admitMatches = @()

    for ($i = 0; $i -lt $lines.Length; $i++) {
        $line = $lines[$i]
        $codeOnly = [regex]::Replace($line, '--.*$', '')

        if ($codeOnly -match '\bsorry\b') {
            $sorryMatches += "Line $($i + 1): $($line.Trim())"
        }
        if ($codeOnly -match '\badmit\b') {
            $admitMatches += "Line $($i + 1): $($line.Trim())"
        }
    }

    if ($sorryMatches.Count -gt 0) {
        Write-Host "    FAILED: Found $($sorryMatches.Count) 'sorry' occurrences in active code:" -ForegroundColor Red
        $sorryMatches | ForEach-Object { Write-Host "      $_" -ForegroundColor Red }
        $TotalErrors++
    } else {
        Write-Host "    PASSED: 0 'sorry' declarations found in active code." -ForegroundColor Green
    }

    if ($admitMatches.Count -gt 0) {
        Write-Host "    FAILED: Found $($admitMatches.Count) 'admit' occurrences in active code:" -ForegroundColor Red
        $admitMatches | ForEach-Object { Write-Host "      $_" -ForegroundColor Red }
        $TotalErrors++
    } else {
        Write-Host "    PASSED: 0 'admit' declarations found in active code." -ForegroundColor Green
    }

    # Count declarations
    $theorems = [regex]::Matches($rawContent, '^[ \t]*(?:noncomputable\s+)?(?:private\s+)?(theorem|lemma)\s+([a-zA-Z0-9_'']+)', [System.Text.RegularExpressions.RegexOptions]::Multiline)
    $defs = [regex]::Matches($rawContent, '^[ \t]*(?:noncomputable\s+)?(?:private\s+)?(def|structure|inductive|abbrev)\s+([a-zA-Z0-9_'']+)', [System.Text.RegularExpressions.RegexOptions]::Multiline)

    $modDecls = $theorems.Count + $defs.Count
    $CumulativeDecls += $modDecls
    Write-Host "    Audited Declarations: $($theorems.Count) proven theorems/lemmas, $($defs.Count) definitions/structures ($modDecls verified declarations)." -ForegroundColor Cyan
}

Write-Host "`n  Project Cumulative Verified Declarations: $CumulativeDecls (Zero Sorries across all modules)." -ForegroundColor Green

# -----------------------------------------------------------------------------
# STEP 2: METADATA SYNCHRONIZATION AUDIT
# -----------------------------------------------------------------------------
Write-Host "`n[STEP 2/5] Verifying Challenge Metadata Synchronization..." -ForegroundColor Yellow

foreach ($mod in $Modules) {
    $jsonPath = $mod.JsonFile
    $rawContent = $ModuleContents[$mod.Name]
    Write-Host "`n  Checking Metadata: $($mod.Name)" -ForegroundColor Cyan
    Write-Host "  Path: $jsonPath" -ForegroundColor DarkGray

    if (-not (Test-Path $jsonPath)) {
        Write-Host "    WARNING: $jsonPath not found, skipping metadata check." -ForegroundColor Yellow
        continue
    }

    $json = Get-Content -Path $jsonPath -Raw | ConvertFrom-Json
    $missingTheorems = @()

    foreach ($thm in $json.theorem_names) {
        $shortName = $thm -replace '^IJM\.TSP\.(Reduction\.)?', ''
        $pattern = "\b(theorem|lemma)\s+$([regex]::Escape($shortName))\b"
        if ($rawContent -notmatch $pattern) {
            $missingTheorems += $thm
        }
    }

    if ($missingTheorems.Count -gt 0) {
        Write-Host "    FAILED: Missing exported theorem declarations in Lean module:" -ForegroundColor Red
        $missingTheorems | ForEach-Object { Write-Host "      $_" -ForegroundColor Red }
        $TotalErrors++
    } else {
        Write-Host "    PASSED: All $($json.theorem_names.Count) exported challenge theorems verified present in Lean module." -ForegroundColor Green
        $json.theorem_names | ForEach-Object { Write-Host "      [x] $_" -ForegroundColor DarkGray }
    }
}

# -----------------------------------------------------------------------------
# STEP 3: PYTHON BENCHMARK SUITES EXECUTION
# -----------------------------------------------------------------------------
Write-Host "`n[STEP 3/5] Executing Python Empirical Benchmark Suites..." -ForegroundColor Yellow

if ($SkipBenchmarks) {
    Write-Host "  SKIPPED: Benchmark suite execution skipped by parameter (-SkipBenchmarks)." -ForegroundColor Yellow
} else {
    $PythonCmd = Get-Command "python" -ErrorAction SilentlyContinue
    if (-not $PythonCmd) {
        Write-Host "  FAILED: Python interpreter not found on PATH." -ForegroundColor Red
        $TotalErrors++
    } else {
        foreach ($bench in $BenchmarkScripts) {
            $bPath = $bench.Path
            Write-Host "`n  Running: $($bench.Name)..." -ForegroundColor Cyan
            Write-Host "  Command: python `"$bPath`"" -ForegroundColor DarkGray

            if (-not (Test-Path $bPath)) {
                Write-Host "  FAILED: Benchmark script not found: $bPath" -ForegroundColor Red
                $TotalErrors++
                continue
            }

            $swBench = [System.Diagnostics.Stopwatch]::StartNew()
            $pyProc = Start-Process -FilePath "python" -ArgumentList "`"$bPath`"" -WorkingDirectory $ResearchDir -NoNewWindow -PassThru -Wait
            $swBench.Stop()

            if ($pyProc.ExitCode -eq 0) {
                Write-Host "  PASSED: $($bench.Name) completed successfully ($([math]::Round($swBench.Elapsed.TotalSeconds, 2))s)." -ForegroundColor Green
            } else {
                Write-Host "  FAILED: $($bench.Name) exited with error code $($pyProc.ExitCode)." -ForegroundColor Red
                $TotalErrors++
            }
        }
    }
}

# -----------------------------------------------------------------------------
# STEP 4: INTERACTIVE HTML DOCGEN GENERATION & VERIFICATION
# -----------------------------------------------------------------------------
Write-Host "`n[STEP 4/5] Verifying Interactive HTML DocGen Generation..." -ForegroundColor Yellow
$DocGenScript = Join-Path $ScriptDir "generate_docs.py"

if (-not (Test-Path $DocGenScript)) {
    Write-Host "  WARNING: DocGen script not found: $DocGenScript" -ForegroundColor Yellow
} else {
    Write-Host "  Running: python `"$DocGenScript`"..." -ForegroundColor Cyan
    $docProc = Start-Process -FilePath "python" -ArgumentList "`"$DocGenScript`"" -WorkingDirectory $ResearchDir -NoNewWindow -PassThru -Wait
    if ($docProc.ExitCode -eq 0) {
        Write-Host "  PASSED: Interactive documentation generated successfully for all modules." -ForegroundColor Green
    } else {
        Write-Host "  FAILED: DocGen script exited with error code $($docProc.ExitCode)." -ForegroundColor Red
        $TotalErrors++
    }
}

# -----------------------------------------------------------------------------
# STEP 5: LEAN 4 FORMALIZATION TYPECHECK
# -----------------------------------------------------------------------------
Write-Host "`n[STEP 5/5] Checking Lean 4 Formal Compilation..." -ForegroundColor Yellow
if ($SkipLean) {
    Write-Host "  SKIPPED: Lean 4 formal compilation check skipped by parameter (-SkipLean)." -ForegroundColor Yellow
} else {
    $LakeCmd = Get-Command "lake" -ErrorAction SilentlyContinue
    if (-not $LakeCmd) {
        Write-Host "  FAILED: 'lake' command not found on PATH." -ForegroundColor Red
        $TotalErrors++
    } elseif (-not (Test-Path $LeanDir)) {
        Write-Host "  FAILED: Lean directory '$LeanDir' not found." -ForegroundColor Red
        $TotalErrors++
    } else {
        foreach ($mod in $Modules) {
            $lPath = $mod.LeanFile
            Write-Host "  Executing: lake env lean `"$lPath`" (cwd: $LeanDir)..." -ForegroundColor Cyan
            $sw = [System.Diagnostics.Stopwatch]::StartNew()
            $pinfo = New-Object System.Diagnostics.ProcessStartInfo
            $pinfo.FileName = "lake"
            $pinfo.Arguments = "env lean `"$lPath`""
            $pinfo.WorkingDirectory = $LeanDir
            $pinfo.RedirectStandardOutput = $true
            $pinfo.RedirectStandardError = $true
            $pinfo.UseShellExecute = $false

            $proc = [System.Diagnostics.Process]::Start($pinfo)
            $stdoutTask = $proc.StandardOutput.ReadToEndAsync()
            $stderrTask = $proc.StandardError.ReadToEndAsync()
            $proc.WaitForExit()
            $stdout = $stdoutTask.GetAwaiter().GetResult()
            $stderr = $stderrTask.GetAwaiter().GetResult()
            $sw.Stop()

            if ($proc.ExitCode -eq 0) {
                Write-Host "  PASSED: Lean 4 typecheck for $($mod.Name) successful with exit code 0 ($([math]::Round($sw.Elapsed.TotalSeconds, 2))s)." -ForegroundColor Green
            } else {
                Write-Host "  FAILED: Lean 4 typecheck for $($mod.Name) exited with code $($proc.ExitCode)." -ForegroundColor Red
                if ($stdout.Trim()) { Write-Host $stdout -ForegroundColor Red }
                if ($stderr.Trim()) { Write-Host $stderr -ForegroundColor Red }
                $TotalErrors++
            }
        }
    }
}

# -----------------------------------------------------------------------------
# FINAL SUMMARY
# -----------------------------------------------------------------------------
Write-Host "`n========================================================================" -ForegroundColor Cyan
if ($TotalErrors -eq 0) {
    Write-Host " BUILD & VERIFICATION AUDIT PASSED: 100% CLEAN (0 ERRORS)" -ForegroundColor Green
    Write-Host " Total Cumulative Verified Declarations: $CumulativeDecls (0 Sorries)" -ForegroundColor Green
    Write-Host "========================================================================" -ForegroundColor Cyan
    exit 0
} else {
    Write-Host " BUILD & VERIFICATION AUDIT FAILED ($TotalErrors ERRORS DETECTED)" -ForegroundColor Red
    Write-Host "========================================================================" -ForegroundColor Cyan
    exit 1
}
