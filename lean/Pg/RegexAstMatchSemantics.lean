/-
Aion.Db.PgRegexAstMatchSemantics — soundness setup for the
                                     Brzozowski-derivative matcher.

`PgRegexAstMatch` ships a computable `matches : PgRegexAst →
String → Bool`. This module gives it semantic meaning by:

  1. Defining the inductive language relation
     `MatchAst.Accepts : MatchAst → List Char → Prop`.
  2. Proving `nullable_correct` — `r.nullable = true ↔ Accepts r []`.

After this PR, downstream code can *name* `Accepts` in theorems
without depending on the matcher's implementation details. The
remaining derivative-soundness lemmas land in a follow-up PR:

  * `accepts_mkSeq_iff` / `accepts_mkAlt_iff` — smart constructor
    transparency (12+ cases of structural simplification each)
  * `star_invert` — non-emptiness of the head match for star
  * `deriv_correct` — `Accepts (r.deriv c) cs ↔ Accepts r (c::cs)`
  * `matchesChars_iff_Accepts` — the closing soundness theorem

Splitting the soundness proof across two PRs lets the `Accepts`
relation enter the proof chain without waiting on the (tactical
but not conceptually hard) discharge of all derivative cases.
-/

import Pg.RegexAstMatch

namespace Pg.RegexAst

open MatchAst

/-! ## The language relation

`Accepts r cs` holds iff `cs` is in `L(r)` per the standard
inductive regex semantics. -/

inductive Accepts : MatchAst → List Char → Prop where
  /-- `eps` accepts the empty string. -/
  | eps      : Accepts .eps []
  /-- `char c` accepts the singleton `[c]`. -/
  | char     (c : Char) : Accepts (.char c) [c]
  /-- `seq l r` accepts `cs` whenever `cs = a ++ b`, `l` accepts
      `a`, and `r` accepts `b`. Bundling the split equation
      inside the constructor (rather than indexing on `a ++ b`
      directly) keeps inversion via `cases` total — Lean's
      dependent eliminator doesn't have to solve `cs = a ++ b`
      to introduce the equation hypothesis. -/
  | seq      {l r : MatchAst} {a b cs : List Char} :
               cs = a ++ b →
               Accepts l a → Accepts r b → Accepts (.seq l r) cs
  /-- `alt l r` accepts anything `l` accepts. -/
  | altLeft  {l r : MatchAst} {cs : List Char} :
               Accepts l cs → Accepts (.alt l r) cs
  /-- `alt l r` accepts anything `r` accepts. -/
  | altRight {l r : MatchAst} {cs : List Char} :
               Accepts r cs → Accepts (.alt l r) cs
  /-- `star r` accepts the empty string. -/
  | starNil  {r : MatchAst} : Accepts (.star r) []
  /-- `star r` accepts `cs` whenever `cs = a ++ b`, `r` accepts
      `a`, and `.star r` accepts `b`. Same equation-in-the-
      constructor trick as `seq`. -/
  | starCons {r : MatchAst} {a b cs : List Char} :
               cs = a ++ b →
               Accepts r a → Accepts (.star r) b → Accepts (.star r) cs

/-! ## Nullable correctness

This is the base case of the eventual soundness theorem
`matchesChars cs r = true ↔ Accepts r cs`: for empty input,
`matchesChars` reduces to `nullable`, and `Accepts r []` is
exactly the structural condition `nullable r = true` decides. -/

/-- `nullable r = true` iff `r` accepts the empty string. -/
theorem nullable_correct (r : MatchAst) :
    r.nullable = true ↔ Accepts r [] := by
  induction r with
  | empty =>
      simp [nullable]
      intro h; cases h
  | eps =>
      simp [nullable]; exact .eps
  | char c =>
      simp [nullable]
      intro h; cases h
  | seq l r ihl ihr =>
      simp [nullable]
      constructor
      · intro ⟨hl, hr⟩
        exact .seq rfl (ihl.mp hl) (ihr.mp hr)
      · intro h
        cases h with
        | seq heq ha hb =>
          -- heq : [] = a ++ b ⟹ a = [] ∧ b = []
          rename_i a b
          have hab : a = [] ∧ b = [] := by
            cases a with
            | nil =>
              cases b with
              | nil => exact ⟨rfl, rfl⟩
              | cons _ _ => simp at heq
            | cons _ _ => simp at heq
          obtain ⟨ha', hb'⟩ := hab
          subst ha'; subst hb'
          exact ⟨ihl.mpr ha, ihr.mpr hb⟩
  | alt l r ihl ihr =>
      simp [nullable]
      constructor
      · intro h
        cases h with
        | inl hl => exact .altLeft (ihl.mp hl)
        | inr hr => exact .altRight (ihr.mp hr)
      · intro h
        cases h with
        | altLeft hl => exact .inl (ihl.mpr hl)
        | altRight hr => exact .inr (ihr.mpr hr)
  | star r _ =>
      simp [nullable]; exact .starNil

end Pg.RegexAst
