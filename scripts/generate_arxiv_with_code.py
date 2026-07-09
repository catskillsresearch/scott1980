#!/usr/bin/env python3
"""Expand Lean hyperlinks and appendix markdown in arxiv.md → arxiv_with_code.md."""

from __future__ import annotations

import re
from datetime import date
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

# GitHub blob links in the Lean Code section, e.g.
# * [Basic.lean](https://github.com/.../blob/main/Scott1980/Neighborhood/Basic.lean)
# Optional trailing annotation (em-dash note) is ignored for expansion matching.
LEAN_LINK_RE = re.compile(
    r"^\* \[([^\]]+\.lean)\]\("
    r"https://github\.com/[^/]+/[^/]+/blob/[^/]+/"
    r"([^)]+)\)"
    r"(?:\s+[—–-].*)?\s*$",
    re.MULTILINE,
)

# Standalone appendix links under ## Appendix A / B, e.g.
# [Exercise722-Composer-Run.md](https://github.com/.../blob/main/Exercise722-Composer-Run.md)
APPENDIX_LINK_RE = re.compile(
    r"^\[([^\]]+\.md)\]\("
    r"https://github\.com/[^/]+/[^/]+/blob/[^/]+/"
    r"([^)]+\.md)\)\s*$",
    re.MULTILINE,
)

# Markdown files inlined when generating arxiv_with_code.md (see arxiv.md appendices A–B).
APPENDIX_INLINE_FILES = frozenset(
    {
        "Exercise722-Composer-Run.md",
        "Exercise722-Composer-Playbook.md",
    }
)


def paper_title(arxiv_text: str) -> str:
    first = arxiv_text.splitlines()[0] if arxiv_text else "# Scott 1980"
    if first.startswith("# "):
        return first[2:].strip()
    return first.strip()


def narrative_body(arxiv_text: str) -> str:
    body = arxiv_text
    if body.startswith("# "):
        idx = body.find("\n---\n")
        if idx != -1:
            body = body[idx + len("\n---\n") :]
        else:
            body = body[body.find("\n") + 1 :]
    return body.rstrip()


def lean_files_from_root() -> list[str]:
    """All library `.lean` files in `Scott1980.lean` import order, plus the root module."""
    root_mod = ROOT / "Scott1980.lean"
    files = ["Scott1980.lean"]
    for line in root_mod.read_text().splitlines():
        line = line.strip()
        if not line.startswith("import "):
            continue
        mod = line.removeprefix("import ").strip()
        if not mod.startswith("Scott1980."):
            continue
        rel = mod.replace(".", "/") + ".lean"
        files.append(rel)
    return files


def sanitize_fence_content(content: str) -> str:
    # Nested ``` in docstrings would break markdown fences in arxiv_with_code.md.
    return content.replace("```", "'''")


def expand_lean_links(text: str) -> str:
    def repl(match: re.Match[str]) -> str:
        name = match.group(1)
        relpath = match.group(2)
        fpath = ROOT / relpath
        if not fpath.is_file():
            raise FileNotFoundError(f"Lean link target missing: {relpath} (from [{name}])")
        content = sanitize_fence_content(fpath.read_text().rstrip()) + "\n"
        n = len(content.splitlines())
        return (
            f"* **{name}** (`{relpath}`) — {n} lines\n\n"
            f"```lean\n"
            f"{content}"
            f"```"
        )

    expanded, count = LEAN_LINK_RE.subn(repl, text)
    if count == 0:
        raise RuntimeError(
            "No GitHub blob `.lean` links found to expand. "
            "Expected bullet lines like "
            "`* [Basic.lean](https://github.com/.../blob/main/Scott1980/Neighborhood/Basic.lean)` "
            "in the Lean Code section of arxiv.md."
        )
    return expanded


def expand_appendix_links(text: str) -> str:
    """Inline appendix markdown (arxiv.md appendices A–B) when present."""
    matches = [
        m
        for m in APPENDIX_LINK_RE.finditer(text)
        if Path(m.group(2)).name in APPENDIX_INLINE_FILES
    ]
    if not matches:
        return text
    if len(matches) != len(APPENDIX_INLINE_FILES):
        found = {Path(m.group(2)).name for m in matches}
        missing = APPENDIX_INLINE_FILES - found
        raise RuntimeError(
            f"Expected {len(APPENDIX_INLINE_FILES)} appendix link(s) in arxiv.md "
            f"(appendices A–B); found {len(matches)}. Missing: {sorted(missing)}."
        )

    def repl(match: re.Match[str]) -> str:
        name = match.group(1)
        relpath = match.group(2)
        if Path(relpath).name not in APPENDIX_INLINE_FILES:
            return match.group(0)
        fpath = ROOT / relpath
        if not fpath.is_file():
            raise FileNotFoundError(f"Appendix link target missing: {relpath} (from [{name}])")
        content = fpath.read_text().rstrip() + "\n"
        n = len(content.splitlines())
        return (
            f"*Inlined from `{relpath}` ({n} lines):*\n\n"
            f"{content}"
        )

    expanded, _ = APPENDIX_LINK_RE.subn(repl, text)
    return expanded


def main() -> None:
    arxiv_path = ROOT / "arxiv.md"
    arxiv = arxiv_path.read_text()
    title = paper_title(arxiv)
    body = narrative_body(arxiv)
    body = expand_appendix_links(body)
    body = expand_lean_links(body)
    files = lean_files_from_root()

    total_lines = sum(len((ROOT / f).read_text().splitlines()) for f in files)
    appendix_lines = sum(
        len((ROOT / name).read_text().splitlines()) for name in APPENDIX_INLINE_FILES
    )

    parts: list[str] = []
    parts.append(
        "<!-- AUTO-GENERATED: run scripts/generate_arxiv_with_code.sh to refresh -->\n"
        "<!-- AGENTS: do not read or grep this file. Use arxiv.md; see .cursorignore -->\n"
    )
    parts.append(f"# {title} — full narrative + complete Lean source\n\n")
    parts.append(
        "> **Generated artifact — not for agents.** Inventory and narrative live in "
        "[`arxiv.md`](arxiv.md). Regenerate with `scripts/generate_arxiv_with_code.sh`. "
        "This file is stale whenever it is older than `arxiv.md` or any listed `.lean` file.\n\n"
    )
    parts.append(
        f"*Generated {date.today().isoformat()} from `arxiv.md` (Lean Code hyperlinks "
        f"expanded inline; appendices A–B inlined) and {len(files)} library `.lean` files "
        f"({total_lines} lines total; appendices {appendix_lines} lines).*\n\n"
    )
    parts.append(
        "**Review copy.** The narrative body matches [`arxiv.md`](arxiv.md) "
        "(excluding the title block through the first `---`), with every "
        "**Lean Code** GitHub hyperlink replaced by the verbatim source file, and "
        "**Appendix A/B** markdown links replaced by the verbatim playbook files.\n\n"
    )
    parts.append("---\n\n")
    parts.append("# Narrative + Lean source (from arxiv.md)\n\n")
    parts.append(body)
    parts.append("\n")

    out = ROOT / "arxiv_with_code.md"
    out.write_text("".join(parts))
    print(f"Wrote {out} ({len(out.read_text().splitlines())} lines)")


if __name__ == "__main__":
    main()
