# Exercise 7.22 — Composer Autorun (single @ file)

> **You (the agent) were invoked with `@Exercise722-Composer-Run.md` only.**
> **The user will not paste anything else.** Follow § AUTORUN below.

---

## AUTORUN — execute this now

You are a Lean 4 proof engineer in `/home/catskills/Desktop/domain_theory` (mathlib v4.30.0).

### Step 0 — orient (minimal reads)

1. Read `HANDOFF.md` lines 1–18 (Resume Protocol only).
2. Read **this file's Progress tracker** (next section). Find the **first row with status `☐`** whose prerequisites are all `☑` (or empty). That is **YOUR SESSION** — execute **only that one**.
3. If every session is `☑` or `DEFER`, report DONE and stop.
4. If the next session is **C7b** (marked DEFER), skip it and take the next eligible `☐`.
5. If **C4** is blocked in HANDOFF, you may run **C11** instead if still `☐`.

### Step 1 — rules (non-negotiable)

- Read ONLY files listed under YOUR SESSION's **READ**.
- Edit ONLY files listed under YOUR SESSION's **EDIT**.
- Zero `sorry`. After **3 failed build-fix attempts** on the same error → **STOP** (§ Stop protocol).
- Choice-free: new proofs must audit to `⊆ {propext, Quot.sound}`.
  **Do NOT use** mathlib's `DFA.toNFA_correct`, `DFA.accepts_inter`, `DFA.accepts_compl` (they pull `Classical.choice`). Use our `dfaToNFA_accepts`, `inter_eval`, `complDFA_accepts`.
- Build: `lake build <module> 2>&1 | grep -vE 'LEAN_PATH|trace:' | tail -25`
- Do **not** git commit unless the user asks.

### Step 2 — execute YOUR SESSION

- Find the session section below (e.g. `## Session C1`).
- Follow **TASK**, use **Skeleton** if present (fill in, do not redesign).
- Do **not** start the next session in the same chat.

### Step 3 — on SUCCESS

1. Append one dated checkpoint to the **end** of `HANDOFF.md` (do not rewrite its middle).
2. In **this file**, change that session's `☐` → `☑` in the Progress tracker below.
3. Report: session id, files changed, build command, axiom audit if new theorems.

### Step 4 — on STOP / BLOCKED

1. Revert broken files if needed (`git checkout -- <file>`).
2. Append `SESSION Cx BLOCKED` checkpoint to HANDOFF.md with exact error.
3. Leave progress tracker unchanged (stay `☐`).
4. Report what to retry.

### Already done — do NOT reprove

- `Exercise722.lean` — Ssys, mulElem, emb
- `Exercise722Regular.lean` — SExpr, denote, matchesB, inS_iff_exists_denote
- `Exercise722DFA.lean` — sigmaDFA, singleDFA, inter/compl
- `Exercise722Cat.lean` — catEps, catEps_accepts
- `Exercise722Decide.lean` — toNFA, toNFA_accepts, denote_eq_empty_iff, dfaToNFA_accepts

---

## Progress tracker

**Agent: after success, edit `☐` → `☑` in this table.**

| Session | Goal | Status | Needs |
|---------|------|--------|-------|
| C1 | `instDecidableEqAutState` | ☑ | — |
| C2 | `autStateCard` + bound | ☑ | C1 |
| C3 | `wordsUpTo` + `anyMatchesB` | ☑ | — |
| C4 | short-word bound (pumping) | ☑ | C2, C3 |
| C5 | `decideEmptyB` + `Decidable` | ☑ | C4 |
| C6 | `consistentB` (relation ii) | ☑ | C5 |
| C7a | document interEq gap | ☑ | C5 |
| C7b | full equivalence | DEFER | Opus |
| C8 | `SsysX` enumeration | ☑ | C5 |
| C9 | `RecDecidable₂` consistency | ☐ | C6, C8 |
| C10 | `ComputablePresentation` | ☐ | C9 |
| C11 | infinite-word prose | ☑ | — |
| C12 | arxiv + audit | ☑ | C6+ |

**Targets:** C1–C6 + C11 = Scott A−. C1–C6 + C8–C10 = Def 7.1 (ii) mechanized.

---

## Stop protocol

STOP when: 3 build failures on same error · 30 min no green · need file outside EDIT · need `Classical.choice` in proof.

```bash
cd /home/catskills/Desktop/domain_theory
git status --short
git checkout -- Domain/Neighborhood/Exercise722Decide.lean  # example
lake build Domain 2>&1 | grep -vE 'LEAN_PATH|trace:' | tail -5
```

---

## Session C1 — `instDecidableEqAutState`

**READ:** `Domain/Neighborhood/Exercise722Decide.lean` (lines 105–130)  
**EDIT:** `Domain/Neighborhood/Exercise722Decide.lean`  
**BUILD:** `lake build Domain.Neighborhood.Exercise722Decide`

**TASK:** Add `instDecidableEqAutState : (e : SExpr) → DecidableEq (autState e)` mirroring `instFintypeAutState`. Two `example` lines for `.sigma` and `.single [true, false]`.

**Skeleton:**

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

## Session C2 — `autStateCard`

**READ:** `Domain/Neighborhood/Exercise722Decide.lean`  
**EDIT:** `Domain/Neighborhood/Exercise722Decide.lean`  
**BUILD:** `lake build Domain.Neighborhood.Exercise722Decide`  
**Needs:** C1 ☑

**TASK:** Define `autStateCard` (sigma→1, single→|σ|+2, cap→product, cat→sum). Prove `autStateCard_le_card`.

**Skeleton:**

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

---

## Session C3 — `wordsUpTo`

**READ:** `Domain/Neighborhood/Exercise722Regular.lean` (`matchesB`, `matchesB_iff`)  
**EDIT:** **NEW** `Domain/Neighborhood/Exercise722Words.lean`, wire `Domain.lean`  
**BUILD:** `lake build Domain.Neighborhood.Exercise722Words`

**TASK:** `wordsUpTo n`, `anyMatchesB`, prove `mem_wordsUpTo`. `#eval anyMatchesB .sigma (wordsUpTo 0)` = true.

**Skeleton:**

```lean
import Domain.Neighborhood.Exercise722Regular

namespace Domain.Neighborhood.Exercise722

def wordsUpTo : ℕ → List (List Bool)
  | 0 => [[]]
  | n + 1 =>
    (wordsUpTo n) ++ (wordsUpTo n).flatMap fun w => [[false] ++ w, [true] ++ w]

theorem mem_wordsUpTo {n w : List Bool} : w ∈ wordsUpTo n ↔ w.length ≤ n := by
  -- induction on n
  sorry -- MUST NOT remain in final file

def anyMatchesB (e : SExpr) (ws : List (List Bool)) : Bool := ws.any (matchesB e)

end Exercise722
```

---

## Session C4 — short-word bound (HARD)

**READ:** `.lake/packages/mathlib/Mathlib/Computability/NFA.lean` (263–334), `Exercise722Decide.lean`, `Exercise722Words.lean`  
**EDIT:** `Exercise722Decide.lean` and/or `Exercise722Words.lean`  
**BUILD:** `lake build Domain.Neighborhood.Exercise722Decide`  
**Needs:** C2 ☑, C3 ☑

**TASK:** Prove `nfa_accepts_nonempty_iff_short` and `denote_nonempty_iff_short`. Audit choice-free.

**Skeleton:**

```lean
variable {σ : Type} [Fintype σ] (M : NFA Bool σ)

theorem exists_accepted_word_short (h : M.accepts.Nonempty) :
    ∃ w, w.length < Fintype.card σ ∧ w ∈ M.accepts := by
  obtain ⟨x, hx⟩ := h
  by_cases hlen : x.length < Fintype.card σ
  · exact ⟨x, hlen, hx⟩
  · have hcard : Fintype.card σ ≤ x.length := by omega
    obtain ⟨a, b, c, rfl, hbound, hbne, hpump⟩ := M.pumping_lemma hx hcard
    have hab : a ++ b ∈ M.accepts := by
      -- extract from Language {a}*{b}*{c}; see Language.mem_mul, mem_kstar
      sorry
    have hshort : (a ++ b).length < Fintype.card σ := by
      simp only [List.length_append]; omega
    exact ⟨a ++ b, hshort, hab⟩

theorem nfa_accepts_nonempty_iff_short :
    M.accepts.Nonempty ↔ ∃ w, w ∈ wordsUpTo (Fintype.card σ) ∧ w ∈ M.accepts := by
  constructor
  · intro h; obtain ⟨w, hwlt, hw⟩ := exists_accepted_word_short M h
    exact ⟨w, by rw [mem_wordsUpTo]; omega, hw⟩
  · intro ⟨w, _, hw⟩; exact ⟨w, hw⟩

theorem denote_nonempty_iff_short (e : SExpr) :
    (denote e).Nonempty ↔ ∃ w ∈ wordsUpTo (autStateCard e), matchesB e w = true := by
  -- via toNFA_accepts + matchesB_iff; watch Language/Set defeq
  sorry
```

**If stuck >30 min:** STOP, HANDOFF "C4 BLOCKED", user may re-@ for C11.

---

## Session C5 — `decideEmptyB`

**READ:** C4 theorems, `Exercise722Regular.lean`  
**EDIT:** `Exercise722Decide.lean` or `Exercise722Words.lean`  
**BUILD:** `lake build Domain.Neighborhood.Exercise722Decide`  
**Needs:** C4 ☑

**TASK:** `decideNonemptyB`, `decideEmptyB`, iff theorems, `Decidable (denote e = ∅)`. Sanity: `#eval decideEmptyB (.cap (.single [false]) (.single [true]))` = true.

**Skeleton:**

```lean
def decideNonemptyB (e : SExpr) : Bool :=
  anyMatchesB e (wordsUpTo (autStateCard e))
def decideEmptyB (e : SExpr) : Bool := !decideNonemptyB e

@[simp] theorem decideNonemptyB_iff (e : SExpr) :
    decideNonemptyB e = true ↔ (denote e).Nonempty := by
  simp [decideNonemptyB, anyMatchesB, List.any_eq_true, denote_nonempty_iff_short]

@[simp] theorem decideEmptyB_iff (e : SExpr) :
    decideEmptyB e = true ↔ denote e = ∅ := by
  simp [decideEmptyB, Bool.not_eq_true, Set.not_nonempty_iff_eq_empty, decideNonemptyB_iff]

instance decidableEmptyDenote (e : SExpr) : Decidable (denote e = ∅) :=
  if h : decideEmptyB e then .isTrue (decideEmptyB_iff e |>.mp h)
  else .isFalse fun he => h (decideEmptyB_iff e |>.mpr he)
```

---

## Session C6 — `consistentB`

**READ:** `Exercise722Regular.lean`, `Exercise722.lean` (`Ssys_isPositive`)  
**EDIT:** `Exercise722Decide.lean`  
**BUILD:** `lake build Domain.Neighborhood.Exercise722Decide`  
**Needs:** C5 ☑

**TASK:** `consistentB a b := !decideEmptyB (.cap a b)`. Prove `consistentB_iff`. Link to Def 7.1 (ii).

```lean
def consistentB (a b : SExpr) : Bool := !decideEmptyB (.cap a b)
theorem consistentB_iff (a b : SExpr) :
    consistentB a b = true ↔ (denote (.cap a b)).Nonempty := by
  simp [consistentB, decideEmptyB_iff, Set.not_nonempty_iff_eq_empty, denote_cap]
```

---

## Session C7a — interEq gap (document)

**READ:** `Exercise722Regular.lean` (`interEq_iff`, `sigma_ne_containsZero`)  
**EDIT:** `Exercise722Decide.lean` (docstring)  
**BUILD:** `lake build Domain.Neighborhood.Exercise722Decide`  
**Needs:** C5 ☑

**TASK:** Docstring: relation (i) = language equivalence; emptiness insufficient (`sigma_ne_containsZero`); full decider needs complement + C7b.

---

## Session C7b — DEFER

Do not execute unless user explicitly requests and budget allows.

---

## Session C8 — `SsysX`

**READ:** `Definition71.lean`, `Exercise722Regular.lean` (`inS_iff_exists_denote`)  
**EDIT:** **NEW** `Exercise722Presentation.lean`, `Domain.lean`  
**BUILD:** `lake build Domain.Neighborhood.Exercise722Presentation`  
**Needs:** C5 ☑

**TASK:** `SsysX : ℕ → Set (List Bool)`, `SsysX_mem`, `SsysX_surj`. Use `decideEmptyB` to skip empty. Encode/decode SExpr from ℕ.

---

## Session C9 — `RecDecidable₂`

**READ:** `Recursive.lean`, `Example78.lean` (`PNpres.cons_computable`)  
**EDIT:** `Exercise722Presentation.lean`  
**BUILD:** `lake build Domain.Neighborhood.Exercise722Presentation`  
**Needs:** C6 ☑, C8 ☑

**TASK:** `Ssys_cons_computable : RecDecidable₂ (fun n m => ∃ k, SsysX k ⊆ SsysX n ∩ SsysX m)` via `RecDecidable.of_iff` + `ssysConsistentB` + a **`Nat.Primrec`** char (not just `Bool`). Import **`Exercise722Presentation`** decode — do **not** duplicate encode/decode in a monolith. Reuse **`Recursive.lean`** `bExistsFn` / `primrec_ite`. **If stuck >30 min:** STOP, HANDOFF "C9 BLOCKED".

---

## Session C10 — `ComputablePresentation`

**READ:** `Definition71.lean`, `Example78.lean`  
**EDIT:** `Exercise722Presentation.lean`  
**BUILD:** `lake build Domain.Neighborhood.Exercise722Presentation`  
**Needs:** C9 ☑

**TASK:** `SsysPres : ComputablePresentation …` with (ii). interEq only if C7b done; else `Ssys_partially_effectively_given`.

---

## Session C11 — infinite words (prose)

**READ:** `Exercise722.lean` docstring, `sources/PRG19_vision.md` (grep 7.22)  
**EDIT:** `Exercise722.lean` docstring only  
**BUILD:** `lake build Domain.Neighborhood.Exercise722`

**TASK:** Answer Scott's equations in prose. Define σ⃗ as `{X ∈ S | ∀n, σⁿ ∈ X}`. Likely: σ⃗σ⃗=σ⃗ YES; 01⃗…=01⃗01⃗ NO.

---

## Session C12 — arxiv + audit

**READ:** HANDOFF tail; `grep "Exercise 7.22" arxiv.md` (one row)  
**EDIT:** `arxiv.md` (row 7.22), HANDOFF Resume Protocol  
**BUILD:** `lake build Domain`  
**Needs:** C6 ☑ minimum

**TASK:** Update arxiv row (escape `\|` in cells). Audit `decideEmptyB_iff`, `consistentB_iff`.

---

## File map

| File | Touch when |
|------|------------|
| `Exercise722Decide.lean` | C1–C2, C4–C7a |
| `Exercise722Words.lean` | C3–C5 (new in C3) |
| `Exercise722Presentation.lean` | C8–C10 (new in C8) |
| `Exercise722.lean` | C11 docstring only |
| `arxiv.md`, `HANDOFF.md` | C12 + every success |

---

## Axiom audit (after C5)

Temp file `Domain/Audit722Decide.lean`:

```lean
import Domain.Neighborhood.Exercise722Decide
open Domain.Neighborhood.Exercise722
#print axioms decideEmptyB_iff
#print axioms consistentB_iff
```

Delete after audit. Expect `[propext, Quot.sound]` only.
