# pgast

**The Postgres dialect AST, in Lean 4 — and the pretty-printer that makes it SQL.**

The writing side of leangres: a small, closed, typed AST whose printed output is
gated against Postgres's own parser. This is the module the provable-migration work
builds on.

Part of [leangres](https://github.com/leangres).

## The extension seam

[`sqlast`](https://github.com/leangres/sqlast) holds the dialect-neutral ANSI
shapes, parameterised over a dialect extension. This module fills that slot:

```lean
abbrev Expr := Polyglot.Sql.Ast.Expr ExprExt
```

contributing 22 Postgres-specific expression constructors (`ilike`, `eqAny`,
`ltreeDescendantOf`, the `jsonb*` family, `regexMatch`, `tgOp`, …), 7
`SelectSource` constructors, and the 29-case PL/pgSQL `BodyStmt`.

## Small and closed, on purpose

[`pgquery`](https://github.com/leangres/pgquery) is complete over Postgres's
grammar and proves nothing — it exists for *reading* SQL. This module is the
opposite trade: deliberately incomplete, because completeness would mean carrying
grammar corners nobody can state a theorem about.

Every constructor here has a printer, a place in an exhaustiveness lock, and a
pinned rendering.

## Two disciplines worth understanding before extending it

**The exhaustiveness lock.** `Pg.ProceduralSurface` classifies every `BodyStmt`
via a non-catchall match, plus a theorem that every case is one of the known
shapes. Adding a constructor **breaks the build** until the printer, the semantics
and the theorem are all updated. Discipline that depends on reviewers remembering
is not discipline.

**The printer pins.** 16 test targets assert *exact* printed output, one per
constructor family. They are surface locks, not theorems: a printer change that
alters bytes fails here loudly. Combined with the lock above, a new constructor
cannot ship un-printed or un-exercised.

## What is here today, and what is missing

`Pg.Stmt.Stmt` has **14 constructors: 13 `CREATE` plus one `alterTable`** whose
action set is four row-level-security toggles.

Missing, and load-bearing for migrations: `DROP` of anything, `RENAME`, real
`ALTER TABLE` (add/drop/alter column, add/drop constraint), `ALTER TYPE … ADD
VALUE`, `GRANT`/`REVOKE`, `COMMENT ON`, views, sequences, extensions — and **all
top-level DML**. `INSERT`/`UPDATE`/`DELETE` exist only *inside* PL/pgSQL function
bodies as `BodyStmt` arms.

`rules_postgres`'s changelog named the gap precisely:

> *"`ADD COLUMN` / `DROP COLUMN` are the obvious next arms and are deliberately
> omitted: a migration DSL that can drop columns raises a different safety
> question, and nothing needs it yet."*

Closing that is the point of this module's next phase, and of
[`pgmigrate`](https://github.com/leangres/pgmigrate) above it.

⛔ **Never add a `raw : String → Stmt` escape hatch.** One raw arm makes every
theorem stated over this AST vacuous for any schema that uses it. The same goes for
`DO $$ … $$` anonymous blocks.

## A trap for anyone writing an evaluator

`Expr Ext` is a **nested inductive** — it carries `List (Expr Ext)`. Structural
recursion is rejected on the list arms; well-founded recursion is accepted but
**does not reduce under `rfl`**, and `simp` with equation lemmas also fails.
Fuel-index the evaluator and prove a fuel-monotonicity lemma before stating
anything universally quantified. Relatedly, `String.splitOn` never reduces — write
a structural splitter over `.data`.

## Contents

| module | what |
|---|---|
| `Pg.Ty` | `PgType` — Postgres's type names |
| `Pg.Ast` | `ExprExt`, `SelectSourceExt`, `BodyStmt`, `Identifier`, `Volatility` |
| `Pg.Stmt` | the `Stmt` inductive + the `Create*Stmt` structures |
| `Pg.AstSmart` | inlined smart constructors for the `Ext` arms |
| `Pg.Pretty` | `printStmt : Stmt → String`, modelled on libpg_query's deparse |
| `Pg.ProceduralSurface` | the exhaustiveness lock |
| `Pg.RegexAst` | a Postgres-internal regex AST |

The printer is pure `String` concatenation with no hashmaps, so output is
bit-identical across runs — which is what makes byte-level pins meaningful.

## Dependencies

`sqlast` (the generic AST) and `pgcatalog` (`Pg.Catalog.QualifiedName` serves as
`Identifier`, so the same value works as an emit input *and* as a key into a
catalog snapshot). Lean core otherwise — no mathlib, no batteries.

Notably **not** `rules_lang`: its atlas also ships `Polyglot.Sql.*`, so depending
on both would put two providers of one module namespace in a single dep closure.
Taking `sqlast` avoids that by construction.

## Consuming it

```python
bazel_dep(name = "pgast", version = "17.6.0")
```

```python
lean_library(
    name = "my_emit",
    srcs = ["MyEmit.lean"],
    deps = ["@pgast//lean:pgast"],
)
```

Published as compiled oleans — pin the same toolchain
(`leanprover/lean4:v4.30.0-rc2`) and select the artifact for your platform.

## Versioning

`<pg_major>.<pg_minor>.<patch>`. `PgType` enumerates Postgres's type names and
`ExprExt` its operators, both of which move between majors.

⚠ A **convention**, not enforced: `compatibility_level` would have been the
mechanism and Bazel 9 made it a no-op. See
[pgcatalog](https://github.com/leangres/pgcatalog)'s `MODULE.bazel` for the two
candidate enforcement mechanisms, neither built yet.

## Provenance

Carved from
[`tomato-bazel/rules_postgres`](https://github.com/tomato-bazel/rules_postgres)
with `git filter-repo`, history preserved.

## License

MIT.
