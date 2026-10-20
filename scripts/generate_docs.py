#!/usr/bin/env python3
"""
Interactive Documentation Generator for Decision TSP & Approximation Research (Lean 4)
Generates self-contained, responsive HTML documentation with syntax highlighting,
instant search, kind filtering, section jumping, and collapsible proof trees for
both OAI.TSP.TSPComplexity (196 declarations) and OAI.TSP.Christofides (141 declarations).
"""

import os
import re
import sys
import json
import html

SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
RESEARCH_DIR = os.path.dirname(SCRIPT_DIR)
DOCS_DIR = os.path.join(RESEARCH_DIR, "docs")

MODULE_SPECS = [
    {
        "id": "tsp_complexity",
        "title": "OAI.TSP.TSPComplexity",
        "subtitle": "Computational Complexity Barriers, Certified Branch-and-Cut Semantics, and Polyhedral Limits of Decision TSP",
        "lean_file": "TSPComplexity.lean",
        "json_file": "TSPComplexity.json",
        "html_file": "TSPComplexity.html",
        "badge_desc": "Tracks A-C: Decision Complexity",
    },
    {
        "id": "christofides",
        "title": "OAI.TSP.Christofides",
        "subtitle": "Machine-Checked Formal Verification of the Christofides-Serdyukov 3/2-Approximation Algorithm in Lean 4",
        "lean_file": "Christofides.lean",
        "json_file": "Christofides.json",
        "html_file": "Christofides.html",
        "badge_desc": "Track D: 3/2-Approximation Frontier",
    },
]


def parse_lean_module(lean_path, json_path):
    with open(lean_path, "r", encoding="utf-8") as f:
        lines = f.readlines()

    landmark_theorems = set()
    if os.path.isfile(json_path):
        with open(json_path, "r", encoding="utf-8") as f:
            data = json.load(f)
            for name in data.get("theorem_names", []):
                short = re.sub(r"^OAI\.TSP\.(Reduction\.)?", "", name)
                landmark_theorems.add(short)
                landmark_theorems.add(name)

    current_section = "1. Foundational Specifications"

    decl_pattern = re.compile(
        r"^(noncomputable\s+)?(private\s+)?(theorem|lemma|def|structure|inductive|abbrev)\s+([a-zA-Z0-9_']+)"
    )
    block_terminator_pattern = re.compile(
        r"^(noncomputable\s+)?(private\s+)?(instance\b|set_option\b|namespace\b|end\b|open\b)"
    )

    declarations = []
    i = 0
    total_lines = len(lines)
    docstring = ""

    while i < total_lines:
        line = lines[i]

        # Check for section header
        if line.strip().startswith("/-!"):
            sec_block = []
            while i < total_lines and not lines[i].strip().endswith("-/"):
                sec_block.append(lines[i])
                i += 1
            if i < total_lines:
                sec_block.append(lines[i])
                i += 1
            sec_text = "".join(sec_block)
            sec_match = re.search(r"##\s*([0-9]+\.[^\n\r]+)", sec_text)
            if sec_match:
                current_section = sec_match.group(1).strip()
            elif "The 10-Vertex Petersen Graph Integrality Gap Witness" in sec_text:
                current_section = "6. Continuous Polyhedral Relaxations (Petersen $P_{10}$ Witness)"
            elif "Yannakakis Slack Factorization" in sec_text:
                current_section = "6. Continuous Polyhedral Relaxations (Yannakakis Slack & Lower Bound)"
            docstring = ""
            continue

        # Check for docstring
        if line.strip().startswith("/--"):
            doc_lines = []
            while i < total_lines and not lines[i].strip().endswith("-/"):
                doc_lines.append(lines[i])
                i += 1
            if i < total_lines:
                doc_lines.append(lines[i])
                i += 1
            doc_raw = "".join(doc_lines)
            docstring = re.sub(r"^/--\s*", "", doc_raw)
            docstring = re.sub(r"\s*-/\s*$", "", docstring).strip()
            continue

        match = decl_pattern.match(line)
        if match:
            start_line = i + 1
            is_noncomputable = bool(match.group(1))
            is_private = bool(match.group(2))
            kind = match.group(3)
            name = match.group(4)

            decl_lines = [line]
            i += 1
            while i < total_lines:
                next_line = lines[i]
                if (
                    next_line.strip().startswith("/-!")
                    or next_line.strip().startswith("/--")
                    or decl_pattern.match(next_line)
                    or block_terminator_pattern.match(next_line)
                ):
                    break
                decl_lines.append(next_line)
                i += 1

            full_code = "".join(decl_lines).rstrip()

            sig_part = full_code
            proof_part = ""

            assign_match = re.search(r"(:=\s*(by)?\s*(\n|$))", full_code)
            if assign_match:
                assign_idx = assign_match.start()
                sig_part = full_code[:assign_idx].rstrip()
                proof_part = full_code[assign_idx:].lstrip()
            elif "\nwhere" in full_code:
                where_idx = full_code.find("\nwhere")
                sig_part = full_code[:where_idx].rstrip()
                proof_part = full_code[where_idx:].lstrip()

            is_landmark = (name in landmark_theorems)
            declarations.append({
                "name": name,
                "kind": kind,
                "line": start_line,
                "section": current_section,
                "docstring": docstring,
                "signature": sig_part,
                "proof": proof_part,
                "full_code": full_code,
                "is_landmark": is_landmark,
                "is_noncomputable": is_noncomputable,
            })
            docstring = ""
            continue

        if block_terminator_pattern.match(line):
            docstring = ""

        i += 1

    return declarations


def highlight_lean(code):
    """HTML syntax highlighter for Lean 4 code."""
    escaped = html.escape(code)

    keywords = [
        r"\b(theorem|lemma|def|structure|inductive|abbrev|where|match|with|by|intro|exact|apply|cases|have|obtain|show|let|if|then|else|namespace|end|open|import)\b"
    ]
    for kw in keywords:
        escaped = re.sub(kw, r'<span class="kw">\1</span>', escaped)

    types = [
        r"\b(Prop|Type|Bool|true|false|Nat|Real|List|Fin|Finset|Option|some|none|Graph|CostFunction|IsTour|ValidTourBound|DecidesTSP|SolverState|SearchStatus|StructuralRank|HeldKarpPoint|DFJCut|CNFFormula|TSPGadget|SpanningTree|IsMST|ConnectedInEdges|PerfectMatching|IsMinWeightMatching|EulerianCircuit|MultigraphEdges|IsMetricCost)\b"
    ]
    for ty in types:
        escaped = re.sub(ty, r'<span class="ty">\1</span>', escaped)

    escaped = re.sub(r"(∀|∃|∧|∨|¬|→|↔|≤|≥|≠|∑|∈|∉|⊆|∪|∩)", r'<span class="sym">\1</span>', escaped)
    escaped = re.sub(r"(--[^\n]*)", r'<span class="comment">\1</span>', escaped)

    return escaped


def generate_single_module_html(mod_info, declarations, all_mods, is_root_index=False):
    lean_basename = mod_info["lean_file"]
    thms = [d for d in declarations if d["kind"] in ("theorem", "lemma")]
    defs = [d for d in declarations if d["kind"] in ("def", "structure", "inductive", "abbrev")]
    landmarks = [d for d in declarations if d["is_landmark"]]

    sections = []
    for d in declarations:
        if d["section"] not in sections:
            sections.append(d["section"])

    sections_html = ""
    for sec_idx, sec in enumerate(sections, 1):
        sec_decls = [d for d in declarations if d["section"] == sec]
        sec_thms = len([d for d in sec_decls if d["kind"] in ("theorem", "lemma")])
        sec_defs = len([d for d in sec_decls if d["kind"] in ("def", "structure", "inductive", "abbrev")])
        sec_slug = f"sec-{sec_idx}"

        cards_html = ""
        for d in sec_decls:
            kind_class = f"badge-{d['kind']}"
            landmark_badge = '<span class="badge badge-landmark">Landmark Challenge</span>' if d['is_landmark'] else ""
            noncomp_badge = '<span class="badge badge-noncomp">noncomputable</span>' if d['is_noncomputable'] else ""
            doc_html = f'<div class="docstring">{html.escape(d["docstring"])}</div>' if d["docstring"] else ""

            proof_btn = ""
            proof_block = ""
            if d["proof"]:
                proof_btn = f'''<button class="btn btn-proof" onclick="toggleProof('{d["name"]}')">
                  <span id="btn-text-{d["name"]}">Show Proof</span>
                </button>'''
                proof_block = f'''<div id="proof-{d["name"]}" class="proof-container hidden">
                  <pre class="code-block code-proof"><code>{highlight_lean(d["proof"])}</code></pre>
                </div>'''

            cards_html += f'''
            <div class="decl-card" data-name="{d['name'].lower()}" data-kind="{d['kind']}" data-landmark="{str(d['is_landmark']).lower()}">
              <div class="decl-header">
                <div class="decl-title">
                  <span class="badge {kind_class}">{d['kind']}</span>
                  {noncomp_badge}
                  {landmark_badge}
                  <span class="decl-name">{d['name']}</span>
                </div>
                <div class="decl-meta">
                  <a href="../{lean_basename}#L{d['line']}" target="_blank" class="line-link">Line {d['line']}</a>
                  <button class="btn btn-copy" onclick="copyDecl('{d['name']}')" title="Copy declaration">Copy</button>
                  {proof_btn}
                </div>
              </div>
              {doc_html}
              <div class="signature-container">
                <pre class="code-block" id="code-{d['name']}"><code>{highlight_lean(d['signature'])}</code></pre>
              </div>
              {proof_block}
            </div>
            '''

        sections_html += f'''
        <section class="section-group" id="{sec_slug}">
          <div class="section-header">
            <h2>{html.escape(sec)}</h2>
            <div class="section-counts">
              <span class="count-pill">{len(sec_decls)} Declarations</span>
              <span class="count-pill">{sec_thms} Theorems</span>
              <span class="count-pill">{sec_defs} Definitions</span>
            </div>
          </div>
          <div class="decls-grid">
            {cards_html}
          </div>
        </section>
        '''

    toc_links = ""
    for sec_idx, sec in enumerate(sections, 1):
        sec_decls = [d for d in declarations if d["section"] == sec]
        toc_links += f'<li><a href="#{f"sec-{sec_idx}"}" class="toc-link">{html.escape(sec)} <span class="toc-count">({len(sec_decls)})</span></a></li>'

    # Build Module Navigation Pills
    mod_pills = ""
    for other_m in all_mods:
        is_active = (other_m["id"] == mod_info["id"])
        active_class = "module-pill active" if is_active else "module-pill"
        target_link = other_m["html_file"]
        mod_pills += f'<a href="{target_link}" class="{active_class}"><span class="pill-title">{other_m["title"]}</span><span class="pill-desc">{other_m["badge_desc"]}</span></a>'

    total_decls_count = len(declarations)

    html_content = f'''<!DOCTYPE html>
<html lang="en">
<head>
  <meta charset="UTF-8">
  <meta name="viewport" content="width=device-width, initial-scale=1.0">
  <title>{mod_info["title"]} &mdash; Interactive Lean 4 Documentation</title>
  <style>
    :root {{
      --bg: #0d1117;
      --card-bg: #161b22;
      --border: #30363d;
      --text: #c9d1d9;
      --text-muted: #8b949e;
      --text-bright: #f0f6fc;
      --accent: #58a6ff;
      --accent-hover: #79c0ff;
      --code-bg: #090d13;
      --badge-thm: #1f6feb;
      --badge-lemma: #238636;
      --badge-def: #8957e5;
      --badge-struct: #d29922;
      --badge-landmark: #f0883e;
      --sidebar-w: 320px;
    }}

    [data-theme="light"] {{
      --bg: #f6f8fa;
      --card-bg: #ffffff;
      --border: #d0d7de;
      --text: #24292f;
      --text-muted: #57606a;
      --text-bright: #0969da;
      --accent: #0969da;
      --accent-hover: #218bff;
      --code-bg: #f6f8fa;
      --badge-thm: #0969da;
      --badge-lemma: #1a7f37;
      --badge-def: #8250df;
      --badge-struct: #bf8700;
      --badge-landmark: #bc4c00;
    }}

    * {{ box-sizing: border-box; margin: 0; padding: 0; }}
    body {{
      font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, Helvetica, Arial, sans-serif;
      background: var(--bg);
      color: var(--text);
      line-height: 1.5;
      display: flex;
      min-height: 100vh;
    }}

    /* Sidebar */
    .sidebar {{
      width: var(--sidebar-w);
      background: var(--card-bg);
      border-right: 1px solid var(--border);
      position: fixed;
      top: 0;
      bottom: 0;
      left: 0;
      overflow-y: auto;
      padding: 1.5rem 1rem;
      display: flex;
      flex-direction: column;
      gap: 1.5rem;
      z-index: 100;
    }}

    .sidebar-brand h1 {{
      font-size: 1.1rem;
      font-weight: 700;
      color: var(--text-bright);
    }}
    .sidebar-brand p {{
      font-size: 0.8rem;
      color: var(--text-muted);
    }}

    .module-nav-container {{
      display: flex;
      flex-direction: column;
      gap: 0.5rem;
      background: var(--code-bg);
      padding: 0.6rem;
      border-radius: 8px;
      border: 1px solid var(--border);
    }}
    .module-nav-label {{
      font-size: 0.7rem;
      text-transform: uppercase;
      letter-spacing: 0.5px;
      color: var(--text-muted);
      font-weight: 700;
    }}
    .module-pill {{
      display: flex;
      flex-direction: column;
      padding: 0.45rem 0.6rem;
      border-radius: 6px;
      text-decoration: none;
      border: 1px solid transparent;
      transition: background 0.15s, border-color 0.15s;
    }}
    .module-pill .pill-title {{
      font-size: 0.82rem;
      font-weight: 600;
      color: var(--text-bright);
    }}
    .module-pill .pill-desc {{
      font-size: 0.7rem;
      color: var(--text-muted);
    }}
    .module-pill:hover {{
      background: var(--border);
    }}
    .module-pill.active {{
      background: rgba(88, 166, 255, 0.15);
      border-color: var(--accent);
    }}
    .module-pill.active .pill-title {{
      color: var(--accent);
    }}

    .toc-list {{
      list-style: none;
      display: flex;
      flex-direction: column;
      gap: 0.4rem;
    }}
    .toc-link {{
      color: var(--text-muted);
      text-decoration: none;
      font-size: 0.85rem;
      display: block;
      padding: 0.4rem 0.6rem;
      border-radius: 6px;
      transition: background 0.15s, color 0.15s;
    }}
    .toc-link:hover {{
      background: var(--border);
      color: var(--text-bright);
    }}
    .toc-count {{
      font-size: 0.75rem;
      opacity: 0.7;
    }}

    /* Main Container */
    .main {{
      margin-left: var(--sidebar-w);
      flex: 1;
      padding: 2rem;
      max-width: 1300px;
    }}

    /* Hero Banner */
    .hero {{
      background: var(--card-bg);
      border: 1px solid var(--border);
      border-radius: 10px;
      padding: 1.8rem 2rem;
      margin-bottom: 2rem;
    }}
    .hero-title {{
      font-size: 1.8rem;
      font-weight: 800;
      color: var(--text-bright);
      margin-bottom: 0.5rem;
    }}
    .hero-subtitle {{
      font-size: 1rem;
      color: var(--text-muted);
      margin-bottom: 1.5rem;
    }}

    .metrics-bar {{
      display: grid;
      grid-template-columns: repeat(auto-fit, minmax(160px, 1fr));
      gap: 1rem;
    }}
    .metric-card {{
      background: var(--code-bg);
      border: 1px solid var(--border);
      border-radius: 8px;
      padding: 0.8rem 1rem;
      text-align: center;
    }}
    .metric-val {{
      font-size: 1.6rem;
      font-weight: 800;
      color: var(--accent);
    }}
    .metric-lbl {{
      font-size: 0.75rem;
      color: var(--text-muted);
      text-transform: uppercase;
      letter-spacing: 0.5px;
    }}

    /* Filter Bar */
    .controls {{
      display: flex;
      flex-wrap: wrap;
      gap: 1rem;
      align-items: center;
      justify-content: space-between;
      margin-bottom: 2rem;
      position: sticky;
      top: 1rem;
      background: var(--bg);
      padding: 0.8rem 0;
      z-index: 50;
    }}
    .search-box {{
      flex: 1;
      min-width: 280px;
      position: relative;
    }}
    .search-input {{
      width: 100%;
      background: var(--card-bg);
      border: 1px solid var(--border);
      color: var(--text);
      padding: 0.6rem 1rem;
      border-radius: 8px;
      font-size: 0.95rem;
      outline: none;
    }}
    .search-input:focus {{
      border-color: var(--accent);
    }}

    .filter-chips {{
      display: flex;
      gap: 0.5rem;
    }}
    .chip {{
      background: var(--card-bg);
      border: 1px solid var(--border);
      color: var(--text-muted);
      padding: 0.4rem 0.8rem;
      border-radius: 20px;
      font-size: 0.8rem;
      cursor: pointer;
      user-select: none;
    }}
    .chip.active {{
      background: var(--accent);
      color: #fff;
      border-color: var(--accent);
    }}

    /* Section Groups */
    .section-group {{
      margin-bottom: 3rem;
    }}
    .section-header {{
      display: flex;
      align-items: baseline;
      justify-content: space-between;
      border-bottom: 1px solid var(--border);
      padding-bottom: 0.8rem;
      margin-bottom: 1.5rem;
    }}
    .section-header h2 {{
      font-size: 1.3rem;
      color: var(--text-bright);
    }}
    .section-counts {{
      display: flex;
      gap: 0.5rem;
    }}
    .count-pill {{
      font-size: 0.75rem;
      background: var(--border);
      padding: 0.2rem 0.5rem;
      border-radius: 12px;
      color: var(--text-muted);
    }}

    /* Declaration Cards */
    .decls-grid {{
      display: flex;
      flex-direction: column;
      gap: 1.2rem;
    }}
    .decl-card {{
      background: var(--card-bg);
      border: 1px solid var(--border);
      border-radius: 8px;
      padding: 1.2rem;
      transition: border-color 0.15s;
    }}
    .decl-card:hover {{
      border-color: #58a6ff55;
    }}
    .decl-header {{
      display: flex;
      justify-content: space-between;
      align-items: center;
      margin-bottom: 0.8rem;
      flex-wrap: wrap;
      gap: 0.5rem;
    }}
    .decl-title {{
      display: flex;
      align-items: center;
      gap: 0.6rem;
      flex-wrap: wrap;
    }}
    .decl-name {{
      font-family: ui-monospace, SFMono-Regular, "SF Mono", Menlo, Consolas, monospace;
      font-size: 1.05rem;
      font-weight: 700;
      color: var(--text-bright);
    }}
    .decl-meta {{
      display: flex;
      align-items: center;
      gap: 0.8rem;
    }}
    .line-link {{
      color: var(--text-muted);
      text-decoration: none;
      font-size: 0.8rem;
      font-family: monospace;
    }}
    .line-link:hover {{
      color: var(--accent);
    }}

    /* Badges */
    .badge {{
      font-size: 0.7rem;
      font-weight: 700;
      text-transform: uppercase;
      padding: 0.2rem 0.5rem;
      border-radius: 4px;
      color: #ffffff;
    }}
    .badge-theorem {{ background: var(--badge-thm); }}
    .badge-lemma {{ background: var(--badge-lemma); }}
    .badge-def {{ background: var(--badge-def); }}
    .badge-structure {{ background: var(--badge-struct); }}
    .badge-inductive {{ background: #d29922; }}
    .badge-abbrev {{ background: #8250df; }}
    .badge-noncomp {{ background: #6e7681; }}
    .badge-landmark {{ background: var(--badge-landmark); }}

    /* Docstrings */
    .docstring {{
      background: rgba(110, 118, 129, 0.1);
      border-left: 3px solid var(--accent);
      padding: 0.6rem 0.8rem;
      margin-bottom: 0.8rem;
      font-size: 0.85rem;
      color: var(--text-muted);
      border-radius: 0 4px 4px 0;
      white-space: pre-wrap;
    }}

    /* Code Blocks */
    .code-block {{
      background: var(--code-bg);
      border: 1px solid var(--border);
      border-radius: 6px;
      padding: 0.8rem 1rem;
      overflow-x: auto;
      font-family: ui-monospace, SFMono-Regular, "SF Mono", Menlo, Consolas, monospace;
      font-size: 0.85rem;
      line-height: 1.45;
    }}
    .code-proof {{
      margin-top: 0.8rem;
      border-left: 3px solid #238636;
    }}

    /* Syntax Highlights */
    .kw {{ color: #ff7b72; font-weight: bold; }}
    .ty {{ color: #79c0ff; font-weight: 600; }}
    .sym {{ color: #d2a8ff; }}
    .comment {{ color: #8b949e; font-style: italic; }}

    /* Buttons */
    .btn {{
      background: var(--code-bg);
      border: 1px solid var(--border);
      color: var(--text);
      padding: 0.3rem 0.6rem;
      border-radius: 6px;
      font-size: 0.75rem;
      cursor: pointer;
      transition: background 0.15s, border-color 0.15s;
    }}
    .btn:hover {{
      background: var(--border);
      border-color: var(--accent);
    }}
    .btn-proof {{
      color: var(--accent);
      border-color: #58a6ff44;
    }}

    .hidden {{ display: none !important; }}

    /* Theme Switcher */
    .theme-toggle {{
      position: fixed;
      bottom: 1.5rem;
      left: 1rem;
      width: calc(var(--sidebar-w) - 2rem);
      padding: 0.5rem;
      background: var(--border);
      border: none;
      color: var(--text);
      border-radius: 6px;
      cursor: pointer;
      font-weight: 600;
      font-size: 0.8rem;
    }}

    @media (max-width: 900px) {{
      body {{ flex-direction: column; }}
      .sidebar {{ width: 100%; position: static; height: auto; }}
      .main {{ margin-left: 0; padding: 1rem; }}
      .theme-toggle {{ position: static; width: 100%; margin-top: 1rem; }}
    }}
  </style>
</head>
<body>
  <!-- Sidebar -->
  <aside class="sidebar">
    <div class="sidebar-brand">
      <h1>Decision TSP Research</h1>
      <p>Lean 4 Verified Mathematics</p>
    </div>

    <!-- Multi-Module Navigation Switcher -->
    <div class="module-nav-container">
      <div class="module-nav-label">Select Module</div>
      {mod_pills}
    </div>

    <div class="toc-header">
      <h3 style="font-size: 0.85rem; text-transform: uppercase; letter-spacing: 0.5px; color: var(--text-muted); margin-bottom: 0.5rem;">Sections</h3>
      <ul class="toc-list">
        {toc_links}
      </ul>
    </div>

    <button class="theme-toggle" onclick="toggleTheme()" id="themeBtn">Light Theme</button>
  </aside>

  <!-- Main Content -->
  <main class="main">
    <!-- Hero Banner -->
    <header class="hero">
      <div class="hero-title">{mod_info["title"]}</div>
      <div class="hero-subtitle">{mod_info["subtitle"]}</div>
      <div class="metrics-bar">
        <div class="metric-card">
          <div class="metric-val">{total_decls_count}</div>
          <div class="metric-lbl">Total Declarations</div>
        </div>
        <div class="metric-card">
          <div class="metric-val">{len(thms)}</div>
          <div class="metric-lbl">Theorems &amp; Lemmas</div>
        </div>
        <div class="metric-card">
          <div class="metric-val">{len(defs)}</div>
          <div class="metric-lbl">Defs &amp; Structures</div>
        </div>
        <div class="metric-card">
          <div class="metric-val">{len(landmarks)}</div>
          <div class="metric-lbl">Landmark Exports</div>
        </div>
        <div class="metric-card">
          <div class="metric-val" style="color: #3fb950;">0</div>
          <div class="metric-lbl">Sorries / Admits</div>
        </div>
      </div>
    </header>

    <!-- Controls / Filters -->
    <div class="controls">
      <div class="search-box">
        <input type="text" class="search-input" id="searchInput" placeholder="Search declarations, signatures, or theorems..." onkeyup="filterDecls()">
      </div>
      <div class="filter-chips">
        <div class="chip active" onclick="setKindFilter('all', this)">All ({total_decls_count})</div>
        <div class="chip" onclick="setKindFilter('theorem', this)">Theorems ({len(thms)})</div>
        <div class="chip" onclick="setKindFilter('def', this)">Defs ({len(defs)})</div>
        <div class="chip" onclick="setKindFilter('landmark', this)">Landmarks ({len(landmarks)})</div>
      </div>
    </div>

    <!-- Sections and Declaration Cards -->
    <div id="declsContainer">
      {sections_html}
    </div>
  </main>

  <script>
    let activeKind = 'all';

    function setKindFilter(kind, el) {{
      activeKind = kind;
      document.querySelectorAll('.chip').forEach(c => c.classList.remove('active'));
      el.classList.add('active');
      filterDecls();
    }}

    function filterDecls() {{
      const query = document.getElementById('searchInput').value.toLowerCase().trim();
      const cards = document.querySelectorAll('.decl-card');

      cards.forEach(card => {{
        const name = card.getAttribute('data-name');
        const kind = card.getAttribute('data-kind');
        const isLandmark = card.getAttribute('data-landmark') === 'true';
        const text = card.innerText.toLowerCase();

        const matchesQuery = !query || name.includes(query) || text.includes(query);

        let matchesKind = true;
        if (activeKind === 'theorem') {{
          matchesKind = (kind === 'theorem' || kind === 'lemma');
        }} else if (activeKind === 'def') {{
          matchesKind = (kind === 'def' || kind === 'structure' || kind === 'inductive' || kind === 'abbrev');
        }} else if (activeKind === 'landmark') {{
          matchesKind = isLandmark;
        }}

        if (matchesQuery && matchesKind) {{
          card.classList.remove('hidden');
        }} else {{
          card.classList.add('hidden');
        }}
      }});

      // Hide empty section groups
      document.querySelectorAll('.section-group').forEach(sec => {{
        const visibleCards = sec.querySelectorAll('.decl-card:not(.hidden)');
        if (visibleCards.length === 0) {{
          sec.classList.add('hidden');
        }} else {{
          sec.classList.remove('hidden');
        }}
      }});
    }}

    function toggleProof(name) {{
      const proofEl = document.getElementById('proof-' + name);
      const btnText = document.getElementById('btn-text-' + name);
      if (proofEl.classList.contains('hidden')) {{
        proofEl.classList.remove('hidden');
        btnText.innerText = 'Hide Proof';
      }} else {{
        proofEl.classList.add('hidden');
        btnText.innerText = 'Show Proof';
      }}
    }}

    function copyDecl(name) {{
      const code = document.getElementById('code-' + name).innerText;
      navigator.clipboard.writeText(code).then(() => {{
        alert('Copied ' + name + ' signature to clipboard!');
      }});
    }}

    function toggleTheme() {{
      const body = document.body;
      const btn = document.getElementById('themeBtn');
      if (body.getAttribute('data-theme') === 'light') {{
        body.removeAttribute('data-theme');
        btn.innerText = 'Light Theme';
      }} else {{
        body.setAttribute('data-theme', 'light');
        btn.innerText = 'Dark Theme';
      }}
    }}
  </script>
</body>
</html>
'''
    return html_content


def main():
    os.makedirs(DOCS_DIR, exist_ok=True)
    parsed_modules = {}

    for mod in MODULE_SPECS:
        lean_path = os.path.join(RESEARCH_DIR, mod["lean_file"])
        json_path = os.path.join(RESEARCH_DIR, mod["json_file"])
        print(f"Parsing Lean module: {lean_path}...")
        decls = parse_lean_module(lean_path, json_path)
        thms = len([d for d in decls if d["kind"] in ("theorem", "lemma")])
        defs = len([d for d in decls if d["kind"] in ("def", "structure", "inductive", "abbrev")])
        landmarks = len([d for d in decls if d["is_landmark"]])
        print(f"  [{mod['title']}] Extracted {len(decls)} declarations across {len(set(d['section'] for d in decls))} sections.")
        print(f"    - Theorems & Lemmas: {thms}")
        print(f"    - Definitions & Structures: {defs}")
        print(f"    - Landmark Challenges: {landmarks}")
        parsed_modules[mod["id"]] = decls

    # Generate dedicated pages
    for mod in MODULE_SPECS:
        html_out = os.path.join(DOCS_DIR, mod["html_file"])
        html_content = generate_single_module_html(mod, parsed_modules[mod["id"]], MODULE_SPECS, is_root_index=False)
        with open(html_out, "w", encoding="utf-8") as f:
            f.write(html_content)
        print(f"Generated module documentation: {html_out}")

    # Generate index.html pointing to default module (TSPComplexity) with switcher
    index_out = os.path.join(DOCS_DIR, "index.html")
    index_content = generate_single_module_html(MODULE_SPECS[0], parsed_modules[MODULE_SPECS[0]["id"]], MODULE_SPECS, is_root_index=True)
    with open(index_out, "w", encoding="utf-8") as f:
        f.write(index_content)
    print(f"Generated root index documentation: {index_out}")


if __name__ == "__main__":
    main()
