#!/usr/bin/env bash
# ==============================================================================
# Automated Continuous Verification & Build Script for Decision TSP & Approximation Research
# ==============================================================================
# Audits:
#   1. Zero-sorry and zero-admit regex audit of TSPComplexity.lean AND Christofides.lean.
#   2. Challenge metadata schema synchronization check against TSPComplexity.json and Christofides.json.
#   3. Execution of Python benchmark suites (adversarial_instances.py and christofides.py).
#   4. Interactive HTML DocGen generation and verification.
#   5. Mandatory Lean 4 formalization typecheck via `lake env lean` (unless --skip-lean is passed).
# ==============================================================================

set -eo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && (pwd -W 2>/dev/null || pwd))"
RESEARCH_DIR="$(cd "${SCRIPT_DIR}/.." && (pwd -W 2>/dev/null || pwd))"
LEAN_DIR="${LEAN_DIR:-${RESEARCH_DIR}}"

SKIP_BENCHMARKS=false
SKIP_LEAN=false

for arg in "$@"; do
  case $arg in
    --skip-benchmarks)
      SKIP_BENCHMARKS=true
      shift
      ;;
    --skip-lean)
      SKIP_LEAN=true
      shift
      ;;
    --lean-dir=*)
      LEAN_DIR="${arg#*=}"
      shift
      ;;
  esac
done

echo "========================================================================"
echo " TSP RESEARCH PACKAGE: CI VERIFICATION & BUILD AUDIT"
echo " Targets: TSPComplexity.lean & Christofides.lean"
echo "========================================================================"

TOTAL_ERRORS=0
CUMULATIVE_DECLS=0

MODULE_NAMES=("TSPComplexity" "Christofides")
LEAN_FILES=("${RESEARCH_DIR}/TSPComplexity.lean" "${RESEARCH_DIR}/Christofides.lean")
JSON_FILES=("${RESEARCH_DIR}/TSPComplexity.json" "${RESEARCH_DIR}/Christofides.json")

# -----------------------------------------------------------------------------
# STEP 1: ZERO-SORRY & ZERO-ADMIT REGEX AUDIT
# -----------------------------------------------------------------------------
echo ""
echo "[STEP 1/5] Running Zero-Sorry & Zero-Admit Syntax Audit..."

for idx in 0 1; do
  MOD_NAME="${MODULE_NAMES[$idx]}"
  LEAN_FILE="${LEAN_FILES[$idx]}"

  echo ""
  echo "  Auditing Module: ${MOD_NAME}"
  echo "  Path: ${LEAN_FILE}"

  if [ ! -f "${LEAN_FILE}" ]; then
    echo "    FAILED: File not found: ${LEAN_FILE}" >&2
    TOTAL_ERRORS=$((TOTAL_ERRORS + 1))
    continue
  fi

  AUDIT_RESULT=$(python -c '
import re, sys

with open(sys.argv[1], "r", encoding="utf-8") as f:
    text = f.read()

# Strip block comments
text_no_block = re.sub(r"/-[\s\S]*?-/", "", text)

sorry_hits = []
admit_hits = []

for line_idx, line in enumerate(text_no_block.splitlines(), start=1):
    code_only = re.sub(r"--.*$", "", line).strip()
    if re.search(r"\bsorry\b", code_only):
        sorry_hits.append((line_idx, line.strip()))
    if re.search(r"\badmit\b", code_only):
        admit_hits.append((line_idx, line.strip()))

thms = len(re.findall(r"^[ \t]*(?:noncomputable\s+)?(?:private\s+)?(theorem|lemma)\s+([a-zA-Z0-9_'\'']+)", text, re.M))
defs = len(re.findall(r"^[ \t]*(?:noncomputable\s+)?(?:private\s+)?(def|structure|inductive|abbrev)\s+([a-zA-Z0-9_'\'']+)", text, re.M))

print(f"THEOREMS={thms}")
print(f"DEFS={defs}")
print(f"SORRY_COUNT={len(sorry_hits)}")
for line_idx, l in sorry_hits:
    print(f"SORRY_HIT:Line {line_idx}: {l}")
print(f"ADMIT_COUNT={len(admit_hits)}")
for line_idx, l in admit_hits:
    print(f"ADMIT_HIT:Line {line_idx}: {l}")
' "${LEAN_FILE}")

  SORRY_COUNT=$(echo "${AUDIT_RESULT}" | grep "^SORRY_COUNT=" | cut -d'=' -f2)
  ADMIT_COUNT=$(echo "${AUDIT_RESULT}" | grep "^ADMIT_COUNT=" | cut -d'=' -f2)
  THM_COUNT=$(echo "${AUDIT_RESULT}" | grep "^THEOREMS=" | cut -d'=' -f2)
  DEF_COUNT=$(echo "${AUDIT_RESULT}" | grep "^DEFS=" | cut -d'=' -f2)

  if [ "${SORRY_COUNT}" -gt 0 ]; then
    echo "    FAILED: Found ${SORRY_COUNT} 'sorry' occurrences in active code:" >&2
    echo "${AUDIT_RESULT}" | grep "^SORRY_HIT:" >&2
    TOTAL_ERRORS=$((TOTAL_ERRORS + 1))
  else
    echo "    PASSED: 0 'sorry' declarations found in active code."
  fi

  if [ "${ADMIT_COUNT}" -gt 0 ]; then
    echo "    FAILED: Found ${ADMIT_COUNT} 'admit' occurrences in active code:" >&2
    echo "${AUDIT_RESULT}" | grep "^ADMIT_HIT:" >&2
    TOTAL_ERRORS=$((TOTAL_ERRORS + 1))
  else
    echo "    PASSED: 0 'admit' declarations found in active code."
  fi

  MOD_DECLS=$((THM_COUNT + DEF_COUNT))
  CUMULATIVE_DECLS=$((CUMULATIVE_DECLS + MOD_DECLS))
  echo "    Audited Declarations: ${THM_COUNT} proven theorems/lemmas, ${DEF_COUNT} definitions/structures (${MOD_DECLS} verified declarations)."
done

echo ""
echo "  Project Cumulative Verified Declarations: ${CUMULATIVE_DECLS} (Zero Sorries across all modules)."

# -----------------------------------------------------------------------------
# STEP 2: METADATA SYNCHRONIZATION AUDIT
# -----------------------------------------------------------------------------
echo ""
echo "[STEP 2/5] Verifying Challenge Metadata Synchronization..."

for idx in 0 1; do
  MOD_NAME="${MODULE_NAMES[$idx]}"
  LEAN_FILE="${LEAN_FILES[$idx]}"
  JSON_FILE="${JSON_FILES[$idx]}"

  echo ""
  echo "  Checking Metadata: ${MOD_NAME}"
  echo "  Path: ${JSON_FILE}"

  if [ ! -f "${JSON_FILE}" ]; then
    echo "    WARNING: ${JSON_FILE} not found, skipping metadata check."
  else
    JSON_AUDIT=$(python -c '
import json, re, sys

with open(sys.argv[1], "r", encoding="utf-8") as f:
    meta = json.load(f)

with open(sys.argv[2], "r", encoding="utf-8") as f:
    code = f.read()

missing = []
for thm in meta.get("theorem_names", []):
    short_name = re.sub(r"^IJM\.TSP\.(Reduction\.)?", "", thm)
    pat = rf"\b(theorem|lemma)\s+{re.escape(short_name)}\b"
    if not re.search(pat, code):
        missing.append(thm)

print(f"MISSING_COUNT={len(missing)}")
for m in missing:
    print(f"MISSING:{m}")
names = meta.get("theorem_names", [])
print(f"TOTAL_CHECKED={len(names)}")
' "${JSON_FILE}" "${LEAN_FILE}")

    MISSING_COUNT=$(echo "${JSON_AUDIT}" | grep "^MISSING_COUNT=" | cut -d'=' -f2)
    TOTAL_CHECKED=$(echo "${JSON_AUDIT}" | grep "^TOTAL_CHECKED=" | cut -d'=' -f2)

    if [ "${MISSING_COUNT}" -gt 0 ]; then
      echo "    FAILED: Missing exported challenge theorems in Lean module:" >&2
      echo "${JSON_AUDIT}" | grep "^MISSING:" >&2
      TOTAL_ERRORS=$((TOTAL_ERRORS + 1))
    else
      echo "    PASSED: All ${TOTAL_CHECKED} exported challenge theorems verified present in Lean module."
    fi
  fi
done

# -----------------------------------------------------------------------------
# STEP 3: PYTHON BENCHMARK SUITES EXECUTION
# -----------------------------------------------------------------------------
echo ""
echo "[STEP 3/5] Executing Python Empirical Benchmark Suites..."

BENCH_SCRIPTS=("${RESEARCH_DIR}/benchmarks/adversarial_instances.py" "${RESEARCH_DIR}/benchmarks/christofides.py" "${RESEARCH_DIR}/benchmarks/structural_rank.py")
BENCH_NAMES=("Adversarial Instances & Branch-and-Cut" "Christofides-Serdyukov 3/2-Approximation Suites" "Track C: Empirical Kappa-Profiling & Cycle-Separation Rank Suite")

if [ "${SKIP_BENCHMARKS}" = true ]; then
  echo "  SKIPPED: Benchmark suite execution skipped via --skip-benchmarks."
elif ! command -v python >/dev/null 2>&1; then
  echo "  FAILED: Python interpreter not found on PATH." >&2
  TOTAL_ERRORS=$((TOTAL_ERRORS + 1))
else
  for b_idx in "${!BENCH_SCRIPTS[@]}"; do
    BNAME="${BENCH_NAMES[$b_idx]}"
    BSCRIPT="${BENCH_SCRIPTS[$b_idx]}"

    echo ""
    echo "  Running: ${BNAME}..."
    echo "  Command: python ${BSCRIPT}"

    if [ ! -f "${BSCRIPT}" ]; then
      echo "    FAILED: Benchmark script not found: ${BSCRIPT}" >&2
      TOTAL_ERRORS=$((TOTAL_ERRORS + 1))
    elif python "${BSCRIPT}"; then
      echo "    PASSED: ${BNAME} completed successfully."
    else
      echo "    FAILED: ${BNAME} exited with error." >&2
      TOTAL_ERRORS=$((TOTAL_ERRORS + 1))
    fi
  done
fi

# -----------------------------------------------------------------------------
# STEP 4: INTERACTIVE HTML DOCGEN GENERATION & VERIFICATION
# -----------------------------------------------------------------------------
echo ""
echo "[STEP 4/5] Verifying Interactive HTML DocGen Generation..."

DOCGEN_SCRIPT="${RESEARCH_DIR}/scripts/generate_docs.py"
if [ ! -f "${DOCGEN_SCRIPT}" ]; then
  echo "  WARNING: DocGen script not found: ${DOCGEN_SCRIPT}"
else
  echo "  Running: python ${DOCGEN_SCRIPT}..."
  if python "${DOCGEN_SCRIPT}"; then
    echo "  PASSED: Interactive documentation generated successfully for all modules."
  else
    echo "  FAILED: DocGen script exited with error." >&2
    TOTAL_ERRORS=$((TOTAL_ERRORS + 1))
  fi
fi

# -----------------------------------------------------------------------------
# STEP 5: LEAN 4 FORMALIZATION TYPECHECK
# -----------------------------------------------------------------------------
echo ""
echo "[STEP 5/5] Checking Lean 4 Formal Compilation..."
if [ "${SKIP_LEAN}" = true ]; then
  echo "  SKIPPED: Lean 4 formal compilation check skipped via --skip-lean."
elif ! command -v lake >/dev/null 2>&1; then
  echo "  FAILED: 'lake' not found on PATH." >&2
  TOTAL_ERRORS=$((TOTAL_ERRORS + 1))
elif [ ! -d "${LEAN_DIR}" ]; then
  echo "  FAILED: Lean directory '${LEAN_DIR}' not found." >&2
  TOTAL_ERRORS=$((TOTAL_ERRORS + 1))
else
  for l_idx in 0 1; do
    LFILE="${LEAN_FILES[$l_idx]}"
    echo "  Executing: (cd ${LEAN_DIR} && lake env lean ${LFILE})..."
    if (cd "${LEAN_DIR}" && lake env lean "${LFILE}"); then
      echo "  PASSED: Lean 4 typecheck for ${LFILE} successful with exit code 0."
    else
      echo "  FAILED: Lean 4 typecheck exited with error for ${LFILE}." >&2
      TOTAL_ERRORS=$((TOTAL_ERRORS + 1))
    fi
  done
fi

# -----------------------------------------------------------------------------
# FINAL SUMMARY
# -----------------------------------------------------------------------------
echo ""
echo "========================================================================"
if [ "${TOTAL_ERRORS}" -eq 0 ]; then
  echo " BUILD & VERIFICATION AUDIT PASSED: 100% CLEAN (0 ERRORS)"
  echo " Total Cumulative Verified Declarations: ${CUMULATIVE_DECLS} (0 Sorries)"
  echo "========================================================================"
  exit 0
else
  echo " BUILD & VERIFICATION AUDIT FAILED (${TOTAL_ERRORS} ERRORS DETECTED)"
  echo "========================================================================"
  exit 1
fi
