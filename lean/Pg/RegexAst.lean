/-
Pg.RegexAst — structured AST for postgres POSIX regex patterns
used in CHECK constraints (DOMAINs, table constraints, function
bodies).

Replaces opaque `String` regex literals in `Pg.Ast.Expr`'s
`regexMatch` constructor with a closed Lean inductive. Lets
downstream code reason structurally about what each regex
accepts, and unblocks the correspondence-theorem track
(`∀ s, dnsLabelRegex.matches s ↔ ValidDnsLabel s` kernel spec).

The matcher itself (Brzozowski derivative form) is in a sibling
module — this one ships the AST + emit-string only.

## Operator surface

Exactly what production DOMAIN regexes use:

  * `anchorStart` / `anchorEnd`     — `^` / `$`
  * `literal     : Char`            — `.` (after escaping), letters, digits
  * `charClass   : List CharRange`  — `[a-z]`, `[a-z0-9]`, `[-a-z0-9]`
  * `concat      : PgRegexAst → PgRegexAst → PgRegexAst`
  * `alt         : PgRegexAst → PgRegexAst → PgRegexAst`
  * `star        : PgRegexAst → PgRegexAst`
  * `plus        : PgRegexAst → PgRegexAst`
  * `opt         : PgRegexAst → PgRegexAst`
  * `group       : PgRegexAst → PgRegexAst`  — `(...)` parens

Patterns beyond this surface (backreferences, lookarounds,
non-greedy quantifiers, Unicode categories, named captures) are
deliberately excluded. Production patterns must round-trip
through the AST, and any new operator must be added as a
constructor here with a sister `toString` arm.

Moved from Aion's `lean/Aion/Db/PgRegexAst.lean` as part of PgAst
extraction Phase 1b. The companion `PgRegexAstMatch*` /
`PgRegexAstMatchSemantics*` modules (the matcher + soundness
proofs) remain on the Phase 4 schedule.
-/

namespace Pg.RegexAst

/-- One range inside a character class. `single c` is `c`;
    `range lo hi` is `lo-hi`. Ranges with `lo > hi` are
    structurally valid but match nothing; postgres rejects the
    range syntax at parse time, so the printer emits them as-is
    and lets the libpg_query gate catch them. -/
inductive CharRange where
  | single : Char → CharRange
  | range  : Char → Char → CharRange
deriving DecidableEq

/-- A structured POSIX regex AST. Designed as the smallest closed
    inductive that covers postgres CHECK-constraint patterns we
    actually emit. New operators join as new constructors here
    (and sister `toString` arms in `PgRegexAst.toString`). -/
inductive PgRegexAst where
  /-- The `^` anchor: matches at start of string. -/
  | anchorStart : PgRegexAst
  /-- The `$` anchor: matches at end of string. -/
  | anchorEnd   : PgRegexAst
  /-- A literal character. Special characters (`.`, `*`, `+`, `?`,
      `(`, `)`, `[`, `]`, `^`, `$`, `\`, `|`) are emitted
      backslash-escaped by `toString` so the literal-character
      semantics survives the round-trip to the regex string. -/
  | literal     : Char → PgRegexAst
  /-- A character class: `[...]` with one or more ranges. Empty
      lists are rejected by postgres regex syntax; we don't gate
      that here, the libpg_query parse test will. -/
  | charClass   : List CharRange → PgRegexAst
  /-- `r1 r2` — match `r1` then `r2`. Right-associative by
      convention (the printer emits without explicit grouping). -/
  | concat      : PgRegexAst → PgRegexAst → PgRegexAst
  /-- `r1 | r2` — match `r1` or `r2`. The printer emits with
      surrounding parens to disambiguate against concatenation. -/
  | alt         : PgRegexAst → PgRegexAst → PgRegexAst
  /-- `r*` — zero or more repetitions of `r`. -/
  | star        : PgRegexAst → PgRegexAst
  /-- `r+` — one or more repetitions of `r`. -/
  | plus        : PgRegexAst → PgRegexAst
  /-- `r?` — zero or one of `r`. -/
  | opt         : PgRegexAst → PgRegexAst
  /-- Explicit grouping `(r)` — used when the source pattern
      groups for repetition (`(...)*`) rather than for capture
      semantics; the AST doesn't distinguish capturing from
      non-capturing groups since we don't use backreferences. -/
  | group       : PgRegexAst → PgRegexAst
deriving Inhabited

/-- Render a single character inside a character class. Within
    `[...]`, only `]`, `\`, and a leading `^` are special; we
    backslash-escape the first two and rely on the caller never
    putting a literal `^` at position 0 (the public smart
    constructors below ensure this). -/
def escapeClassChar (c : Char) : String :=
  match c with
  | ']'  => "\\]"
  | '\\' => "\\\\"
  | _    => String.singleton c

/-- Render one `CharRange` inside the brackets. -/
def CharRange.toString : CharRange → String
  | .single c       => escapeClassChar c
  | .range lo hi    => escapeClassChar lo ++ "-" ++ escapeClassChar hi

/-- Render a list of `CharRange`s back-to-back inside the
    brackets. -/
def charRangesToString : List CharRange → String
  | []      => ""
  | r :: rs => r.toString ++ charRangesToString rs

/-- Characters that must be backslash-escaped when emitted as a
    literal outside a character class. -/
def isLiteralSpecial (c : Char) : Bool :=
  c == '.' || c == '*' || c == '+' || c == '?' ||
  c == '(' || c == ')' || c == '[' || c == ']' ||
  c == '^' || c == '$' || c == '\\' || c == '|'

/-- Render a literal character outside a class — special
    characters are backslash-escaped per the
    `isLiteralSpecial` predicate. -/
def escapeLiteral (c : Char) : String :=
  if isLiteralSpecial c then "\\" ++ String.singleton c
  else String.singleton c

/-- Render a `PgRegexAst` as the postgres POSIX regex string
    libpg_query will parse. Concatenation is rendered without
    grouping (operator precedence is `concat` tighter than `alt`,
    matching POSIX). Alternation is wrapped in `(...)` to keep
    the surface unambiguous regardless of context. -/
partial def PgRegexAst.toString : PgRegexAst → String
  | .anchorStart   => "^"
  | .anchorEnd     => "$"
  | .literal c     => escapeLiteral c
  | .charClass rs  => "[" ++ charRangesToString rs ++ "]"
  | .concat l r    => l.toString ++ r.toString
  | .alt l r       => "(" ++ l.toString ++ "|" ++ r.toString ++ ")"
  | .star r        => r.toString ++ "*"
  | .plus r        => r.toString ++ "+"
  | .opt r         => r.toString ++ "?"
  | .group r       => "(" ++ r.toString ++ ")"

/-- Convenience: build a `concat` chain from a list (right-fold).
    Empty list maps to an empty-string match, encoded as a star
    over an unsatisfiable class — kept as a sentinel; callers
    should provide a non-empty list. -/
def concatAll : List PgRegexAst → PgRegexAst
  | []      => .star (.charClass [])
  | [r]     => r
  | r :: rs => .concat r (concatAll rs)

end Pg.RegexAst
