/-
Aion.Db.PgRegexAstMatch — Brzozowski-derivative matcher for
                            `PgRegexAst`.

Companion to `Pg.RegexAst`. The structured regex AST is
emitted as a postgres POSIX regex string, but for kernel
correspondence proofs we also need a Lean-side semantics — a
total `matches : PgRegexAst → String → Bool` function that
downstream theorems can target.

## Approach

Brzozowski derivatives. For each input character `c` and regex
`r`, the derivative `D_c(r)` is a regex matching the strings `s`
such that `c ++ s` is matched by `r`. Then a regex `r` matches a
string `c1 c2 ... cn` iff `D_{cn} ∘ ... ∘ D_{c1}(r)` is nullable
(matches the empty string).

The implementation uses an internal `MatchAst` type richer than
`PgRegexAst` — it adds `empty` (matches ∅) and `eps` (matches
the empty string) as explicit constructors, which keeps the
derivative arms simple and total. `PgRegexAst.toMatchAst` lowers
the public AST into this richer form; `PgRegexAst.matches`
composes the two halves.

## Anchors in full-string mode

`anchorStart` and `anchorEnd` are nullable in `MatchAst` — i.e.
treated as `eps`. This is sound for full-string matching against
anchored patterns (which is what every DOMAIN regex is); for
substring matching against unanchored patterns we'd need a
proper anchor handling, but that's a future PR.

## Soundness goals (separate PRs)

* `matches_iff_starredConcat` style soundness vs the standard
  regex semantics
* Per-DOMAIN correspondence theorems like
  `dns_label_matches_spec : ∀ s,
     dnsLabelRegex.matches s.toList ↔ ValidDnsLabel s`
* Runtime stipulation `PostgresRegexReflects` linking
  `PgRegexAst.matches` to postgres's `~` operator
-/

import Pg.RegexAst

namespace Pg.RegexAst

/-- Internal matcher AST. Richer than `PgRegexAst`: adds
    `empty` (matches no strings) and `eps` (matches only the
    empty string) so derivative arms close cleanly. Repetition is
    expressed by `seq` + `star`; `plus`/`opt`/`group`/`charClass`
    all lower into this surface. -/
inductive MatchAst where
  | empty  : MatchAst
  | eps    : MatchAst
  | char   : Char → MatchAst
  | seq    : MatchAst → MatchAst → MatchAst
  | alt    : MatchAst → MatchAst → MatchAst
  | star   : MatchAst → MatchAst
deriving Inhabited

/-- Algebraic smart constructor for sequencing — absorbs `empty`
    and unfolds `eps`, keeping the derivative trees bounded so
    matching doesn't blow up for moderate-sized inputs. -/
def MatchAst.mkSeq : MatchAst → MatchAst → MatchAst
  | .empty, _ => .empty
  | _, .empty => .empty
  | .eps,   r => r
  | l,    .eps => l
  | l,      r => .seq l r

/-- Algebraic smart constructor for alternation — absorbs the
    `empty` branch and de-duplicates `eps`. -/
def MatchAst.mkAlt : MatchAst → MatchAst → MatchAst
  | .empty, r => r
  | l, .empty => l
  | l,      r => .alt l r

/-- `nullable r = true` iff the empty string is in `L(r)`. -/
def MatchAst.nullable : MatchAst → Bool
  | .empty    => false
  | .eps      => true
  | .char _   => false
  | .seq l r  => l.nullable && r.nullable
  | .alt l r  => l.nullable || r.nullable
  | .star _   => true

/-- Brzozowski derivative of `r` with respect to character `c`.
    `D_c(r)` matches `s` iff `r` matches `c :: s`. -/
def MatchAst.deriv (c : Char) : MatchAst → MatchAst
  | .empty    => .empty
  | .eps      => .empty
  | .char c'  => if c == c' then .eps else .empty
  | .seq l r  =>
      let dl := MatchAst.mkSeq (l.deriv c) r
      if l.nullable then MatchAst.mkAlt dl (r.deriv c) else dl
  | .alt l r  => MatchAst.mkAlt (l.deriv c) (r.deriv c)
  | .star r   => MatchAst.mkSeq (r.deriv c) (.star r)

/-- Fold `deriv` over a character list, returning the residual
    regex after consuming all characters. -/
def MatchAst.derivList (r : MatchAst) : List Char → MatchAst
  | []       => r
  | c :: cs  => (r.deriv c).derivList cs

/-- Full-string match: the regex matches the input iff the
    residual after consuming every character is nullable. -/
def MatchAst.matchesChars (r : MatchAst) (cs : List Char) : Bool :=
  (r.derivList cs).nullable

/-- Build a `MatchAst` covering `lo .. hi` as an alternation of
    single-character `MatchAst.char`s. Used by `CharRange.toMatch`. -/
private def MatchAst.altRange (lo hi : Char) : MatchAst :=
  -- Inclusive range; we walk `lo`'s codepoint up to `hi`'s by
  -- structural recursion on the difference. Bound the recursion
  -- depth by `hi.toNat - lo.toNat + 1` for termination.
  let loN := lo.toNat
  let hiN := hi.toNat
  if loN > hiN then .empty
  else
    let rec build (n : Nat) (cur : Char) : MatchAst :=
      match n with
      | 0       => .char cur
      | k + 1   =>
        let curN := cur.toNat
        if curN == hiN then .char cur
        else .alt (.char cur) (build k (Char.ofNat (curN + 1)))
    build (hiN - loN) lo

/-- Lower a `CharRange` into a `MatchAst`. -/
def CharRange.toMatch : CharRange → MatchAst
  | .single c       => .char c
  | .range lo hi    => MatchAst.altRange lo hi

/-- Lower a non-empty list of `CharRange`s into an alternation. -/
def CharRange.listToMatch : List CharRange → MatchAst
  | []      => .empty
  | [r]     => r.toMatch
  | r :: rs => .alt r.toMatch (CharRange.listToMatch rs)

/-- Lower a `PgRegexAst` into a `MatchAst`.
    `anchorStart` / `anchorEnd` become `eps` — sound for the
    full-string match the public `matches` provides against
    anchored patterns. -/
def PgRegexAst.toMatchAst : PgRegexAst → MatchAst
  | .anchorStart    => .eps
  | .anchorEnd      => .eps
  | .literal c      => .char c
  | .charClass rs   => CharRange.listToMatch rs
  | .concat l r     => MatchAst.mkSeq l.toMatchAst r.toMatchAst
  | .alt    l r     => MatchAst.mkAlt l.toMatchAst r.toMatchAst
  | .star   r       => .star r.toMatchAst
  | .plus   r       =>
      let m := r.toMatchAst
      MatchAst.mkSeq m (.star m)
  | .opt    r       => MatchAst.mkAlt r.toMatchAst .eps
  | .group  r       => r.toMatchAst

/-- The public matcher: does `r` accept `s` in full-string mode?

    For an anchored regex like `^[a-z_][a-z0-9_]*$`, this is the
    natural notion. Substring matching against unanchored
    patterns is a future extension. -/
def PgRegexAst.matches (r : PgRegexAst) (s : String) : Bool :=
  r.toMatchAst.matchesChars s.toList

end Pg.RegexAst
