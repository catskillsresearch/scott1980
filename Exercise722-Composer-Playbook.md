# Exercise 7.22 — Composer Playbook

> **For zero-paste usage, `@Exercise722-Composer-Run.md` instead** — it includes autorun
> instructions and the progress tracker Composer updates. This file is extended reference.

Use this file to finish Scott's **effectively given** decider for `Ssys` in small, revert-safe
Composer sessions. Everything is checked in; if a session fails, revert and retry that chunk only.

**How to run (legacy):** `@Exercise722-Composer-Run.md` — recommended, no pasting.
Or `@Exercise722-Composer-Playbook.md` + paste session prompt below.

**Budget tip:** One session = one paste. Do not ask Composer to "continue through C6." Stop when the
build is green and HANDOFF is appended.

---

## Progress tracker

Mark sessions as you go. **Do not skip ahead** if a prerequisite is unchecked.

| Session | Goal | Status | Notes |
|---------|------|--------|-------|
| **C1** | `instDecidableEqAutState` | ☐ | |
| **C2** | `autStateCard` + bound | ☐ | needs C1 |
| **C3** | `wordsUpTo` + `anyMatchesB` | ☐ | independent of C1–C2 |
| **C4** | short-word bound (pumping) | ☐ | needs C2, C3 |
| **C5** | `decideEmptyB` + `Decidable` | ☐ | needs C4 |
| **C6** | `consistentB` (relation ii) | ☐ | needs C5 |
| **C7a** | document why interEq needs complement | ☐ | needs C5 |
| **C7b** | full equivalence decider | ☐ DEFER | Opus / post-reset |
| **C8** | `SsysX` enumeration | ☐ | needs C5 |
| **C9** | `RecDecidable₂` consistency | ☐ | needs C6, C8 |
| **C10** | `ComputablePresentation` | ☐ | needs C9 |
| **C11** | infinite-word prose | ☐ | independent |
| **C12** | arxiv + final audit | ☐ | needs C6+ at minimum |

**Minimum for Scott B+ → A− on "effectively given":** C1–C6 + C11.  
**Minimum for mechanized Def 7.1 (ii):** C1–C6 + C8–C10.  
**Full Def 7.1 (i)+(ii):** all of the above + C7b (hard).

---

## Stop protocol (read before every session)

Composer must **STOP** (no guessing, no `sorry`, no drive-by refactors) when:

1. **`lake build` fails** after 3 fix attempts on the same error.
2. **30 minutes** elapsed with no green build.
3. Task requires editing a file **not listed** in the session's EDIT block.
4. Task would need **`Classical.choice`** (check with `#print axioms` on new theorems).
5. C4 pumping proof stalls — mark C4 blocked in HANDOFF, skip to **C11** (free win), retry C4 later.

**On STOP:**

```bash
cd /home/catskills/Desktop/domain_theory
git status --short
# Revert only the broken session's files:
git checkout -- Domain/Neighborhood/Exercise722Decide.lean   # example
git clean -fd Domain/Neighborhood/Exercise722Words.lean      # if new file was bad
lake build Domain 2>&1 | grep -vE 'LEAN_PATH|trace:' | tail -5
```

Append to HANDOFF.md:

```
## Checkpoint YYYY-MM-DD — SESSION Cx BLOCKED
Reason: <exact error or stuck goal>
Files touched: <list>
Next: retry Cx / skip to Cy
```

---

## Master preamble (paste at top of EVERY session)

```
You are a Lean 4 proof engineer in /home/catskills/Desktop/domain_theory (mathlib v4.30.0).

RULES (non-negotiable):
1. Read HANDOFF.md "Resume Protocol" (lines 1–18) ONLY — do not read all of HANDOFF or arxiv.md.
2. Read ONLY the files listed in this session's READ block.
3. Touch ONLY the files listed in this session's EDIT block.
4. Zero `sorry`. If blocked after 3 build-fix attempts, STOP per Exercise722-Composer-Playbook.md
   "Stop protocol" — report exact error, do not guess.
5. Choice-free discipline: proofs must audit to ⊆ {propext, Quot.sound}.
   Do NOT use mathlib's DFA.toNFA_correct, DFA.accepts_inter, DFA.accepts_compl
   (they pull Classical.choice). Use our dfaToNFA_accepts, inter_eval, complDFA_accepts.
6. Build: lake build <module> 2>&1 | grep -vE 'LEAN_PATH|trace:' | tail -25
7. On success: append ONE dated checkpoint to the END of HANDOFF.md (do not rewrite the middle).
8. Do NOT git commit unless I ask.
9. Follow proof skeletons in Exercise722-Composer-Playbook.md when provided — fill them in, don't
   redesign the approach.

CONTEXT: Exercise 7.22 — finish the decider so S is "effectively given" (Def 7.1).
Already done (DO NOT REPROVE):
  - Exercise722.lean — algebraic core, Ssys, mulElem, emb
  - Exercise722Regular.lean — SExpr, denote, matchesB, inS_iff_exists_denote, emptyExpr, interEq_iff
  - Exercise722DFA.lean — sigmaDFA, singleDFA, interDFA_accepts, complDFA_accepts
  - Exercise722Cat.lean — catEps, catEps_accepts
  - Exercise722Decide.lean — toNFA, toNFA_accepts, denote_eq_empty_iff, dfaToNFA_accepts
```

---

## Session C1 — `DecidableEq` on automaton states

**READ:** `Domain/Neighborhood/Exercise722Decide.lean` (lines 105–130)  
**EDIT:** `Domain/Neighborhood/Exercise722Decide.lean`  
**BUILD:** `lake build Scott1980.Neighborhood.Exercise722Decide`

```
SESSION C1 — instDecidableEqAutState

TASK:
Add `instDecidableEqAutState : (e : SExpr) → DecidableEq (autState e)` mirroring
`instFintypeAutState` (recursive: Unit, Option (Fin _), ×, ⊕).
Add two `example` lines confirming DecidableEq for `.sigma` and `.single [true, false]`.

DO NOT: touch decide, Recursive, or other files.

SUCCESS: build green, zero sorry.
HANDOFF: append "C1 instDecidableEqAutState green".
```

### Skeleton (C1)

```lean
instance instDecidableEqAutState : (e : SExpr) → DecidableEq (autState e)
  | .sigma => inferInstance
  | .single σ => inferInstance
  | .cap a b => by
      letI := instDecidableEqAutState a; letI := instDecidableEqAutState b
      infer_instance
  | .cat a b => by
      letI := instDecidableEqAutState a; letI := instDecidableEqAutState b
      infer_instance
```

---

## Session C2 — structural state-count bound

**READ:** `Domain/Neighborhood/Exercise722Decide.lean` (`autState`, `instFintypeAutState`)  
**EDIT:** `Domain/Neighborhood/Exercise722Decide.lean`  
**BUILD:** `lake build Scott1980.Neighborhood.Exercise722Decide`  
**Needs:** C1

```
SESSION C2 — autStateCard

TASK:
Define `autStateCard : SExpr → ℕ` recursively:
  .sigma => 1
  .single σ => σ.length + 2
  .cap a b => autStateCard a * autStateCard b
  .cat a b => autStateCard a + autStateCard b
Prove `autStateCard_le_card (e : SExpr) : autStateCard e ≤ Fintype.card (autState e)`.
Import `Mathlib.Data.Fintype.Card` if needed.

DO NOT: implement reachability or emptiness yet.

SUCCESS: build green; `#print axioms autStateCard_le_card` ⊆ {propext, Quot.sound}.
HANDOFF: append "C2 autStateCard + bound green".
```

### Skeleton (C2)

```lean
def autStateCard : SExpr → ℕ
  | .sigma => 1
  | .single σ => σ.length + 2
  | .cap a b => autStateCard a * autStateCard b
  | .cat a b => autStateCard a + autStateCard b

theorem autStateCard_le_card (e : SExpr) : autStateCard e ≤ Fintype.card (autState e) := by
  induction e with
  | sigma => simp [autStateCard, autState]
  | single σ => simp [autStateCard, autState]; exact Nat.le_refl _
  | cap a b ih_a ih_b =>
    simp only [autStateCard, autState, Fintype.card_prod]
    exact Nat.mul_le_mul ih_a ih_b
  | cat a b ih_a ih_b =>
    simp only [autStateCard, autState, Fintype.card_sum]
    exact Nat.add_le_add ih_a ih_b
```

*(Adjust `simp` if card lemmas need explicit `rw [Fintype.card_prod]` etc.)*

---

## Session C3 — short-word enumerator

**READ:** `Domain/Neighborhood/Exercise722Regular.lean` (`matchesB`, `matchesB_iff`)  
**EDIT:** **NEW** `Domain/Neighborhood/Exercise722Words.lean`, wire in `Domain.lean`  
**BUILD:** `lake build Scott1980.Neighborhood.Exercise722Words`  
**Independent** of C1–C2 (can run in parallel)

```
SESSION C3 — wordsUpTo

TASK:
Create Domain/Neighborhood/Exercise722Words.lean importing Exercise722Regular.
Define `wordsUpTo : ℕ → List (List Bool)` — all words of length ≤ n.
Define `anyMatchesB (e : SExpr) (ws : List (List Bool)) : Bool`.
Prove `mem_wordsUpTo {n w} : w ∈ wordsUpTo n ↔ w.length ≤ n`.
Wire import in Domain.lean.

DO NOT: prove pumping lemma yet.

SUCCESS: build green. `#eval anyMatchesB .sigma (wordsUpTo 0)` = true.
HANDOFF: append "C3 wordsUpTo green".
```

### Skeleton (C3)

```lean
import Scott1980.Neighborhood.Exercise722Regular

namespace Scott1980.Neighborhood.Exercise722

/-- All words over `{false,true}` of length ≤ `n`. -/
def wordsUpTo : ℕ → List (List Bool)
  | 0 => [[]]
  | n + 1 =>
    (wordsUpTo n) ++ (wordsUpTo n).flatMap fun w => [[false] ++ w, [true] ++ w]

theorem mem_wordsUpTo {n w : List Bool} : w ∈ wordsUpTo n ↔ w.length ≤ n := by
  sorry -- induction on n; DO NOT leave sorry in final file

def anyMatchesB (e : SExpr) (ws : List (List Bool)) : Bool :=
  ws.any (matchesB e)

end Exercise722
```

*(Composer: replace the `sorry` with induction; typical base `n=0` gives only `[]`.)*

---

## Session C4 — short-word bound via pumping (HARD)

**READ:**
- `.lake/packages/mathlib/Mathlib/Computability/NFA.lean` lines 263–334 (`accepts`, `pumping_lemma`)
- `Domain/Neighborhood/Exercise722Decide.lean` (`toNFA`, `instFintypeAutState`)
- `Domain/Neighborhood/Exercise722Words.lean`
- **Proof skeleton below** in this playbook

**EDIT:** `Domain/Neighborhood/Exercise722Decide.lean` (or `Exercise722Words.lean`)  
**BUILD:** `lake build Scott1980.Neighborhood.Exercise722Decide`  
**Needs:** C2, C3

```
SESSION C4 — accepts_short_word_bound

TASK:
Prove for [Fintype σ] (M : NFA Bool σ):
  nfa_accepts_nonempty_iff_short :
    M.accepts.Nonempty ↔ ∃ w, w ∈ wordsUpTo (Fintype.card σ) ∧ w ∈ M.accepts

Then:
  denote_nonempty_iff_short (e : SExpr) :
    (denote e).Nonempty ↔ ∃ w ∈ wordsUpTo (autStateCard e), matchesB e w = true

Use the proof skeleton in Exercise722-Composer-Playbook.md § "Skeleton C4".
Audit new theorems: ⊆ {propext, Quot.sound}.

DO NOT: implement decideEmptyB yet.

SUCCESS: build green.
HANDOFF: append "C4 short-word bound green" OR "C4 BLOCKED: <reason>".
```

### Skeleton C4 — pumping contrapositive (fill in for Composer)

**Mathematical idea:** If `L = M.accepts` is nonempty, pick any `x ∈ L`. If `|x| ≥ |Q|`, apply
`NFA.pumping_lemma` to get a split `x = a++b++c` with `|a|+|b| ≤ |Q|` and `{a}{b}*{c} ⊆ L`.
Then `a++b` (or `a` if `b` empty — but pumping gives `b ≠ []`) has length `< |Q|` and is in `L`.
So some accepted word has length `< Fintype.card σ`.

**Lean skeleton** (put in `Exercise722Decide.lean` or `Exercise722Words.lean`):

```lean
import Scott1980.Neighborhood.Exercise722Words
import Mathlib.Computability.NFA
import Mathlib.Data.Fintype.Card

namespace Scott1980.Neighborhood.Exercise722

open Computability

variable {σ : Type} [Fintype σ] (M : NFA Bool σ)

/-- If the language is nonempty, some accepted word has length strictly below `|σ|`. -/
theorem exists_accepted_word_short (h : M.accepts.Nonempty) :
    ∃ w, w.length < Fintype.card σ ∧ w ∈ M.accepts := by
  obtain ⟨x, hx⟩ := h
  by_cases hlen : x.length < Fintype.card σ
  · exact ⟨x, hlen, hx⟩
  · -- x.length ≥ card σ: apply pumping
    have hcard : Fintype.card σ ≤ x.length := by omega
    obtain ⟨a, b, c, rfl, hbound, hbne, hpump⟩ := M.pumping_lemma hx hcard
    -- Key: a ++ b is accepted and shorter than x
    have hab : a ++ b ∈ M.accepts := by
      have : x ∈ ({a} : Language Bool) * ({b} : Language Bool)∗ * ({c} : Language Bool) := hpump
      -- extract a++b from the pumped language; use Language.mul/Kleene membership lemmas
      sorry -- COMPOSER: unfold Language membership; use {a}*{b}* sublanguage
    have hshort : (a ++ b).length < Fintype.card σ := by
      have : (a ++ b).length = a.length + b.length := by simp [List.length_append]
      rw [this]
      have := hbound  -- a.length + b.length ≤ Fintype.card σ
      have hbpos : 0 < b.length := List.length_pos.mpr hbne
      omega
    exact ⟨a ++ b, hshort, hab⟩

theorem nfa_accepts_nonempty_iff_short :
    M.accepts.Nonempty ↔ ∃ w, w ∈ wordsUpTo (Fintype.card σ) ∧ w ∈ M.accepts := by
  constructor
  · intro h
    obtain ⟨w, hwlt, hw⟩ := exists_accepted_word_short M h
    refine ⟨w, ?_, hw⟩
    rw [mem_wordsUpTo]
    omega
  · intro ⟨w, _, hw⟩
    exact ⟨w, hw⟩

theorem denote_nonempty_iff_short (e : SExpr) :
    (denote e).Nonempty ↔ ∃ w ∈ wordsUpTo (autStateCard e), matchesB e w = true := by
  have hcard : autStateCard e ≤ Fintype.card (autState e) := autStateCard_le_card e
  constructor
  · intro hne
    rw [← toNFA_accepts e] at hne
    -- M.accepts = denote e; apply nfa_accepts_nonempty_iff_short to toNFA e
    sorry -- COMPOSER: rewrite Language/Set membership carefully
  · intro ⟨w, hwmem, hwmatch⟩
    rw [← toNFA_accepts e]
    sorry -- COMPOSER: use matchesB_iff + mem_wordsUpTo

end Exercise722
```

**C4 gotchas:**
- `NFA.pumping_lemma` uses `Language` (`{a} * {b}∗ * {c}`), not `Set`. Use `Language.mem_mul`,
  `Language.mem_kstar`, or `show w ∈ M.accepts` with `Language`/`Set` defeq.
- `M.pumping_lemma` may pull `Classical.choice` via `toDFA_correct` internally — that's OK in
  **Prop-level** pumping; the **decision function** `decideEmptyB` (C5) stays computable via `matchesB`.
- If `hab` extraction stalls >20 min, try accepting `w.length ≤ card` instead of `< card`.

---

## Session C5 — `decideEmptyB` (the decider)

**READ:** C4 theorems, `Exercise722Regular.lean` (`matchesB_iff`)  
**EDIT:** `Domain/Neighborhood/Exercise722Decide.lean` or `Exercise722Words.lean`  
**BUILD:** `lake build Scott1980.Neighborhood.Exercise722Decide`  
**Needs:** C4

```
SESSION C5 — decideEmptyB

TASK:
Define:
  decideNonemptyB (e : SExpr) : Bool :=
    anyMatchesB e (wordsUpTo (autStateCard e))
  decideEmptyB (e : SExpr) : Bool := !decideNonemptyB e

Prove:
  decideNonemptyB_iff (e) : decideNonemptyB e = true ↔ (denote e).Nonempty
  decideEmptyB_iff (e) : decideEmptyB e = true ↔ denote e = ∅

Derive: instance decidableEmptyDenote (e) : Decidable (denote e = ∅)

Sanity: `#eval decideEmptyB (.cap (.single [false]) (.single [true]))` should be `true`.

SUCCESS: build green, audit choice-free.
HANDOFF: append "C5 decideEmptyB green".
```

### Skeleton (C5)

```lean
def decideNonemptyB (e : SExpr) : Bool :=
  anyMatchesB e (wordsUpTo (autStateCard e))

def decideEmptyB (e : SExpr) : Bool := !decideNonemptyB e

@[simp] theorem decideNonemptyB_iff (e : SExpr) :
    decideNonemptyB e = true ↔ (denote e).Nonempty := by
  simp only [decideNonemptyB, anyMatchesB, List.any_eq_true]
  rw [denote_nonempty_iff_short e]
  constructor <;> rintro ⟨w, hw, hmatch⟩ <;> exact ⟨w, hw, by simpa using hmatch⟩

@[simp] theorem decideEmptyB_iff (e : SExpr) :
    decideEmptyB e = true ↔ denote e = ∅ := by
  simp only [decideEmptyB, Bool.not_eq_true, Set.not_nonempty_iff_eq_empty,
    decideNonemptyB_iff]

instance decidableEmptyDenote (e : SExpr) : Decidable (denote e = ∅) :=
  if h : decideEmptyB e then .isTrue (decideEmptyB_iff e |>.mp h)
  else .isFalse fun he => h (decideEmptyB_iff e |>.mpr he)
```

---

## Session C6 — relation (ii) consistency

**READ:** `Exercise722Regular.lean` (`empty_iff_equiv_emptyExpr`), `Exercise722.lean` (`Ssys_isPositive`)  
**EDIT:** `Domain/Neighborhood/Exercise722Decide.lean`  
**Needs:** C5

```
SESSION C6 — consistentB

TASK:
Define `consistentB (a b : SExpr) : Bool := !decideEmptyB (.cap a b)`.
Prove `consistentB_iff : consistentB a b = true ↔ (denote (.cap a b)).Nonempty`.
Add `capNonempty_iff_consistent` linking to Def 7.1 (ii) via Ssys positivity.

DO NOT: implement interEq / equivalence.

SUCCESS: build green.
HANDOFF: append "C6 consistentB / relation (ii) decidable green".
```

### Skeleton (C6)

```lean
def consistentB (a b : SExpr) : Bool := !decideEmptyB (.cap a b)

theorem consistentB_iff (a b : SExpr) :
    consistentB a b = true ↔ (denote (.cap a b)).Nonempty := by
  simp [consistentB, decideEmptyB_iff, Set.not_nonempty_iff_eq_empty, denote_cap]

-- Link to Def 7.1 (ii): ∃k. X_k ⊆ X_n ∩ X_m  ↔  cap non-empty (by positivity)
-- See Ssys_isPositive in Exercise722.lean
```

---

## Session C7a — document equivalence gap (quick)

**READ:** `Exercise722Regular.lean` (`interEq_iff`, `sigma_ne_containsZero`)  
**EDIT:** `Domain/Neighborhood/Exercise722Decide.lean` (docstring + one lemma if easy)  
**Needs:** C5

```
SESSION C7a — interEq needs complement (document)

TASK:
Add module/docstring section explaining:
  - interEq_iff: relation (i) = language equivalence on SExpr
  - sigma_ne_containsZero: emptiness alone cannot decide equivalence
  - Full interEq decider needs complement / symmetric difference / Finset determinization

Optional: prove `decideCapEqB` ONLY for the special case when you can reduce to
decideEmptyB on `.cap a b` vs `.single [...]` — do NOT claim general equivalence.

DO NOT: implement C7b.

SUCCESS: build green (docstring-only is fine).
HANDOFF: append "C7a interEq gap documented".
```

---

## Session C7b — full equivalence (DEFER)

**Do not run on Composer unless budget reset or Opus available.**

Needs: `Finset`-state determinization, complement DFA, then
`decideCapEq a b k := decideEmptyB (.cap (.cap a b) (compl ...))` style — large sub-project.

---

## Session C8 — enumerate `S`

**READ:** `Definition71.lean`, `Exercise722Regular.lean` (`InS_iff_exists_denote`)  
**EDIT:** **NEW** `Domain/Neighborhood/Exercise722Presentation.lean`, `Domain.lean`  
**Needs:** C5 (for filtering empty)

```
SESSION C8 — SsysX enumeration

TASK:
Create Exercise722Presentation.lean.
Define a simple SExpr listing by size/depth (or `SExpr.encode : SExpr → ℕ` + partial decoder).
Define `SsysX : ℕ → Set (List Bool)` mapping indices to nonempty denotations in S.
Prove `SsysX_mem : ∀ n, InS (SsysX n)` and `SsysX_surj : ∀ {Y}, InS Y → ∃ n, SsysX n = Y`.
Skip indices whose denote is empty (use decideEmptyB).

DO NOT: RecDecidable yet.

SUCCESS: build green.
HANDOFF: append "C8 SsysX enumeration green".
```

### Skeleton (C8)

```lean
import Scott1980.Neighborhood.Exercise722
import Scott1980.Neighborhood.Exercise722Decide
import Scott1980.Neighborhood.Definition71

namespace Scott1980.Neighborhood.Exercise722

/-- Gödel-style size for enumeration (keep simple). -/
def sexprSize : SExpr → ℕ
  | .sigma => 1
  | .single σ => 2 + σ.length
  | .cap a b => 1 + sexprSize a + sexprSize b
  | .cat a b => 1 + sexprSize a + sexprSize b

-- Option A: list all SExprs of size ≤ n (if too hard, use explicit inductive generator)
-- Option B: partial decode from ℕ (preferred for RecDecidable in C9)

def SsysX : ℕ → Set (List Bool) := fun n =>
  match SExpr.decode n with
  | none => Set.univ  -- junk index; or ∅
  | some e => if decideEmptyB e then ∅ else denote e

theorem SsysX_mem (n : ℕ) : InS (SsysX n) := by
  sorry -- use InS_denote_of_nonempty when non-empty

theorem SsysX_surj {Y : Set (List Bool)} (hY : InS Y) : ∃ n, SsysX n = Y := by
  obtain ⟨e, rfl, hne⟩ := inS_iff_exists_denote.mp hY
  sorry -- pick n = encode e

end Exercise722
```

---

## Session C9 — `RecDecidable₂` consistency

**READ:** `Domain/Neighborhood/Recursive.lean` (`RecDecidable`, `RecDecidable.of_iff`)  
**READ:** `Domain/Neighborhood/Example78.lean` (`PNpres.cons_computable` pattern)  
**EDIT:** `Exercise722Presentation.lean`  
**Needs:** C6, C8

```
SESSION C9 — cons_computable

TASK:
Add SExpr.encode / decode as Nat.Primrec (or cite existing if added in C8).
Prove:
  Ssys_cons_computable : RecDecidable₂ (fun n m =>
    ∃ k, SsysX k ⊆ SsysX n ∩ SsysX m)
By positivity + consistentB on decoded expressions.
Pattern: RecDecidable.of_iff + primrec decoder + consistentB.

SUCCESS: build green, #print axioms.
HANDOFF: append "C9 RecDecidable₂ consistency green".
```

### Skeleton (C9)

```lean
theorem Ssys_cons_computable : RecDecidable₂ (fun n m =>
    ∃ k, SsysX k ⊆ SsysX n ∩ SsysX m) := by
  -- By Ssys positivity: ∃k. X_k ⊆ X_n ∩ X_m ↔ (X_n ∩ X_m).Nonempty
  -- ↔ consistentB (decode n) (decode m)
  refine RecDecidable.of_iff (fun t => ?_) (existing_primrec_decider.comp primrec_decode_pair)
  -- COMPOSER: grep Example78.lean and Exercise715.lean for exact of_iff pattern
  sorry
```

---

## Session C10 — `ComputablePresentation`

**READ:** `Definition71.lean`, `Example78.lean` (`PNpres`)  
**EDIT:** `Exercise722Presentation.lean`  
**Needs:** C9

```
SESSION C10 — SsysPresentation

TASK:
Package `def SsysPres : ComputablePresentation Ssys` (match repo naming conventions).
Fields: X := SsysX, mem_X, surj, cons_computable from C9.
For interEq_computable: ONLY if C7b done; else document as open and provide
theorem `Ssys_partially_effectively_given` with (ii) only.

NO sorry.

SUCCESS: build green.
HANDOFF: append "C10 ComputablePresentation (ii) green; (i) open unless C7b done".
```

---

## Session C11 — infinite words (prose, no API burn)

**READ:** `Exercise722.lean` docstring, `sources/PRG19_vision.md` (grep EXERCISE 7.22)  
**EDIT:** `Exercise722.lean` docstring only  
**Independent**

```
SESSION C11 — infinite words investigation (prose)

TASK:
Expand docstring "Infinite words" with Scott's questions answered:
  1. Define σ⃗ as filter {X ∈ S | ∀n, σⁿ ∈ X} (left-infinite power).
  2. σ⃗σ⃗ = σ⃗ ?  — discuss (likely YES for unary σ).
  3. σ⃗σ⃗σ⃗ = σ⃗ ? — discuss.
  4. σ⃗1⃗σ⃗1⃗ = σ⃗1⃗ ? — define 1⃗ first.
  5. 01⃗01⃗01⃗01⃗ = 01⃗01⃗ ? — likely NO (period mismatch).

Optional: `def infLeftPower (σ : List Bool) : Set (Set (List Bool))` if one-liner.

DO NOT: prove equations in Lean unless trivial.
SUCCESS: Exercise722.lean still builds.
HANDOFF: append "C11 infinite-word investigation documented".
```

### Suggested prose answers (Composer can expand)

| Equation | Likely answer | Reason |
|----------|---------------|--------|
| `σ⃗σ⃗ = σ⃗` | **Yes** (for `σ⃗ = ⋃ₙ {σⁿ}`-style filter) | Closed under append of tail |
| `σ⃗σ⃗σ⃗ = σ⃗` | **Yes** | Same idempotence pattern |
| `σ⃗1⃗σ⃗1⃗ = σ⃗1⃗` | **Depends on definition** | Need `1⃗ = infLeftPower [true]` |
| `01⃗…01⃗ = 01⃗01⃗` | **No** | Left vs right infinite concatenation differ |

---

## Session C12 — arxiv + audit

**READ:** HANDOFF tail, `arxiv.md` row for Exercise 7.22 (grep only)  
**EDIT:** `arxiv.md` (one row), HANDOFF Resume Protocol lines 20–44  
**Needs:** at least C6

```
SESSION C12 — inventory sync

TASK:
Update arxiv.md Exercise 7.22 row: decideEmptyB, consistentB, presentation status.
Escape | as \| in table cells.
Run: lake build Domain
Audit: decideEmptyB_iff, consistentB_iff, Ssys_cons_computable (if exist).

HANDOFF: append final checkpoint.
```

---

## Combo prompts (optional shortcuts)

### Combo A — infrastructure only (low risk)

Paste Master Preamble + C1 + C2 + C3 in one session **only if** Composer stops after each green build.

### Combo B — decider core (medium risk)

C4 + C5 together — only after C1–C3 are checked off.

### Combo C — free win while blocked on C4

Run **C11** anytime. Zero dependency on decider.

---

## File map (do not edit unless session says so)

| File | Purpose |
|------|---------|
| `Exercise722.lean` | Algebraic core, Ssys, docstrings |
| `Exercise722Regular.lean` | SExpr, denote, matchesB |
| `Exercise722DFA.lean` | Leaf DFAs, inter/compl |
| `Exercise722Cat.lean` | catEps concatenation |
| `Exercise722Decide.lean` | toNFA, decideEmptyB (C5+) |
| `Exercise722Words.lean` | wordsUpTo (C3+) |
| `Exercise722Presentation.lean` | SsysX, ComputablePresentation (C8+) |
| `Definition71.lean` | ComputablePresentation structure |
| `Recursive.lean` | RecDecidable |

---

## Axiom audit template (after C5+)

Create `Domain/Audit722Decide.lean` temporarily:

```lean
import Scott1980.Neighborhood.Exercise722Decide
open Scott1980.Neighborhood.Exercise722
#print axioms decideEmptyB_iff
#print axioms consistentB_iff
-- delete file after audit
```

Run: `lake build Domain.Audit722Decide`

Expected: `[propext, Quot.sound]` only — no `Classical.choice`.

---

## What "done" looks like

| Scott asks | After which sessions |
|------------|---------------------|
| Positive NS | ✅ already |
| Semigroup + embedding | ✅ already |
| Regular events | ✅ already (`toNFA_accepts`) |
| Effectively given (ii) | C1–C6 (+ C8–C10 for full presentation) |
| Effectively given (i) | C7b (deferred) |
| Infinite words | C11 |

**Realistic Composer outcome:** C1–C6 + C11 = strong A−. C8–C10 = mechanized Def 7.1 (ii). C7b = later.
