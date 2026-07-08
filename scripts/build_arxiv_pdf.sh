#!/usr/bin/env bash
# Regenerate arxiv.tex + appendix.tex, compile both PDFs, and dist/arxiv_submit.zip.
#
# The Lean-source appendix (~1400 pages of listings) is compiled separately into
# appendix.pdf.  The main arxiv.tex ends with \includepdf{appendix.pdf}, so
# narrative-only edits recompile only the ~200-page body (target: under 5 minutes).
# arXiv AutoTeX does the same: fast main pass + pre-built pages.
set -euo pipefail
cd "$(dirname "$0")/.."

TEX="arxiv.tex"
PDF="arxiv.pdf"
APPENDIX_TEX="appendix.tex"
APPENDIX_PDF="appendix.pdf"

# shellcheck source=scripts/arxiv_pdf_checks.sh
source "$(dirname "$0")/arxiv_pdf_checks.sh"

pdf_valid() {
  local f="$1"
  [[ -f "$f" ]] || return 1
  pdfinfo "$f" >/dev/null 2>&1 || return 1
  local pages
  pages="$(pdfinfo "$f" 2>/dev/null | awk '/^Pages:/ {print $2}')"
  [[ -n "$pages" && "$pages" -gt 0 ]]
}

compile_tex() {
  local target="$1"
  local clean="${2:-0}"
  if [[ "$clean" -eq 1 ]]; then
    latexmk -C "$target" >/dev/null 2>&1 || true
    rm -f "${target%.tex}.aux" "${target%.tex}.out" "${target%.tex}.toc" "${target%.tex}.lof"
  fi
  latexmk -interaction=nonstopmode -halt-on-error "$target" >/dev/null 2>&1 || {
    echo "latexmk reported errors compiling ${target}; tail of log:" >&2
    tail -n 40 "${target%.tex}.log" >&2 || true
    exit 1
  }
}

echo "==> Regenerating arxiv.tex + appendix.tex + lean-listings/ + figures/"
if [[ "${1:-}" == "--pdf-only" ]]; then
  echo "    (--pdf-only: skipping markdown/tex regeneration)"
else
  bash scripts/build_arxiv_tex.sh
fi

need_appendix=0
if ! pdf_valid "$APPENDIX_PDF"; then
  need_appendix=1
elif [[ "$APPENDIX_TEX" -nt "$APPENDIX_PDF" ]]; then
  need_appendix=1
fi

if [[ "$need_appendix" -eq 1 ]]; then
  echo "==> Compiling appendix PDF (slow pass: Lean listings; LuaLaTeX, see .latexmkrc)"
  rm -f "$APPENDIX_PDF"
  compile_tex "$APPENDIX_TEX" 1
  if ! pdf_valid "$APPENDIX_PDF"; then
    echo "error: ${APPENDIX_PDF} missing or corrupt after compile" >&2
    exit 1
  fi
  echo "wrote $APPENDIX_PDF ($(du -h "$APPENDIX_PDF" | cut -f1), $(pdfinfo "$APPENDIX_PDF" | awk '/Pages:/ {print $2}') pages)"
else
  echo "==> Reusing cached $APPENDIX_PDF ($(du -h "$APPENDIX_PDF" | cut -f1), $(pdfinfo "$APPENDIX_PDF" | awk '/Pages:/ {print $2}') pages)"
fi

echo "==> arXiv preflight: appendix.pdf font embedding"
check_pdf_fonts_embedded "$APPENDIX_PDF" "appendix.pdf"

echo "==> Compiling main PDF (fast pass + pdfpages; LuaLaTeX, see .latexmkrc)"
need_main=1
if pdf_valid "$PDF" \
  && [[ ! "$TEX" -nt "$PDF" ]] \
  && [[ ! "$APPENDIX_PDF" -nt "$PDF" ]] \
  && [[ ! lean-listings -nt "$PDF" ]] \
  && [[ ! figures -nt "$PDF" ]]; then
  need_main=0
fi
if [[ "$need_main" -eq 0 ]]; then
  echo "==> Reusing cached $PDF ($(du -h "$PDF" | cut -f1), $(pdfinfo "$PDF" | awk '/Pages:/ {print $2}') pages; arxiv.tex unchanged)"
else
  start_main=$(date +%s)
  main_clean=0
  if ! pdf_valid "$PDF"; then
    main_clean=1
  fi
  compile_tex "$TEX" "$main_clean"
  end_main=$(date +%s)
  main_secs=$((end_main - start_main))
  if ! pdf_valid "$PDF"; then
    echo "error: ${PDF} missing or corrupt after compile" >&2
    exit 1
  fi
  echo "wrote $PDF ($(du -h "$PDF" | cut -f1), $(pdfinfo "$PDF" | awk '/Pages:/ {print $2}') pages; main compile ${main_secs}s)"
fi

echo "==> Packaging arXiv submission zip"
bash scripts/package_arxiv_submit.sh --skip-tex-build
