# arXiv AutoTeX uses pdfLaTeX. Local preview matches that (PNG figures,
# Palomar-link appendix, short Lean snippets — no longer a pdfTeX memory hog).
$pdf_mode = 1;
$pdflatex = 'pdflatex -interaction=nonstopmode -halt-on-error %O %S';
