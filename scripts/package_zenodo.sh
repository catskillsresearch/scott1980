#!/usr/bin/env bash
# Build a Zenodo deposit zip: PDF (full Lean appendix) + narrative + Lean sources + license.
#
# Layout inside dist/scott1980-zenodo.zip:
#   README-ZENODO.md
#   arxiv.pdf          # paper with complete Lean Code appendix
#   arxiv.md           # narrative / inventory source
#   LICENSE
#   README.md
#   lean-toolchain
#   lakefile.toml
#   lake-manifest.json
#   Scott1980.lean
#   Scott1980/**/*.lean
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

# shellcheck source=scripts/pdf_checks.sh
source "$(dirname "$0")/pdf_checks.sh"

PDF="arxiv.pdf"
OUT_DIR="dist"
STAGE="${OUT_DIR}/zenodo-stage"
ZIP="${OUT_DIR}/scott1980-zenodo.zip"

if [[ "${1:-}" != "--skip-pdf-build" ]]; then
  echo "==> Building PDF with full Lean appendix"
  bash scripts/build_arxiv_pdf.sh
  exit 0
fi

missing=0
if [[ ! -f "$PDF" ]]; then
  echo "error: missing $PDF (run scripts/build_arxiv_pdf.sh first)" >&2
  missing=1
fi
if [[ ! -f arxiv.md ]]; then
  echo "error: missing arxiv.md" >&2
  missing=1
fi
if [[ ! -d Scott1980 ]]; then
  echo "error: missing Scott1980/" >&2
  missing=1
fi
if [[ "$missing" -ne 0 ]]; then
  exit 1
fi

mkdir -p "$OUT_DIR"
rm -rf "$STAGE"
mkdir -p "$STAGE"

cat > "${STAGE}/README-ZENODO.md" <<'EOF'
# scott1980 — Zenodo deposit

Lean 4 formalization of Dana Scott's *Lectures on a Mathematical Theory of Computation*
(PRG-19, 1980/81), with a narrative inventory and the complete Lean sources printed in the PDF
appendix.

## Contents

| Path | Description |
|------|-------------|
| `arxiv.pdf` | Paper PDF: narrative + full Lean Code appendix |
| `arxiv.md` | Markdown source for the narrative / inventory |
| `Scott1980.lean` / `Scott1980/` | Lean 4 library sources |
| `lakefile.toml`, `lake-manifest.json`, `lean-toolchain` | Lake / toolchain pins |
| `LICENSE`, `README.md` | Project license and repository README |

## Rebuild

```bash
lake exe cache get
lake build Scott1980
python3 scripts/generate_lecture_mermaid.py --write
bash scripts/build_arxiv_pdf.sh
```

Repository: https://github.com/catskillsresearch/scott1980
EOF

cp -f "$PDF" "${STAGE}/arxiv.pdf"
cp -f arxiv.md LICENSE README.md "${STAGE}/"
cp -f lean-toolchain lakefile.toml lake-manifest.json Scott1980.lean "${STAGE}/"
mkdir -p "${STAGE}/Scott1980"
# Copy Lean sources only (no build artifacts).
find Scott1980 -type f -name '*.lean' -print0 | while IFS= read -r -d '' f; do
  dest="${STAGE}/${f}"
  mkdir -p "$(dirname "$dest")"
  cp -f "$f" "$dest"
done

rm -f "$ZIP"
(
  cd "$STAGE"
  zip -r "../scott1980-zenodo.zip" . >/dev/null
)

echo "wrote $ZIP ($(du -h "$ZIP" | cut -f1))"
check_pdf_fonts_embedded "$PDF" "arxiv.pdf"
echo "Contents (top):"
zipinfo -1 "$ZIP" | sed 's/^/  /' | head -40
echo "  …"
echo "Upload $ZIP to Zenodo (PDF includes the complete Lean source appendix)."
