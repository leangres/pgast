# Changelog

## 17.6.1 — DDL that mutates: the DROP family and a real ALTER TABLE

`Stmt` was 13 `CREATE`s plus an `alterTable` whose action set was four
row-level-security toggles. A migration is a *state transition*, and none of
that could express one.

**`AlterTableAction` 4 → 17.** Columns (`addColumn`, `dropColumn`, `setNotNull`,
`dropNotNull`, `setDefault`, `dropDefault`, `setColumnType` with `USING`),
constraints (`addConstraint`, `validateConstraint`, `dropConstraint`), and
renames/placement (`renameColumn`, `renameTable`, `setSchema`) — alongside the
original four, unchanged.

**`Stmt.dropObject`.** One `DropStmt` carrying a `DropTarget`, rather than a
constructor per object kind — what Postgres's own grammar does. The printer, and
later the hazard classifier and catalog transition, each get one arm with an
inner match, and the exhaustiveness lock still bites because adding a target
kind breaks that match.

Function-like targets carry their argument types and table-scoped ones carry
their table, because Postgres needs both to disambiguate: `DROP FUNCTION f` is
ambiguous wherever two overloads exist.

### The field that matters most

`addConstraint`'s **`notValid`**. `ADD CONSTRAINT ... NOT VALID` takes a brief
lock and does not scan; a plain `ADD CONSTRAINT` takes `ACCESS EXCLUSIVE` and
scans the whole table. On anything large that is the difference between an online
migration and an outage.

It is also what makes the correct backfill ordering expressible at all. Postgres
enforces a `NOT VALID` constraint on new and updated rows *immediately*, so
adding it **before** a backfill closes the race against concurrent writers, and
`validateConstraint` scans afterwards under a weaker lock. The usual
add-column/backfill/`SET NOT NULL` recipe has neither property.

### Rendering moved, byte-for-byte

`AlterTableAction.toSql` could not render the new arms: they carry `Expr`,
`ColumnDef` and `TableConstraint`, whose printers live in `Pg.Pretty`, which
imports `Pg.Stmt`. Rendering moved to `Pg.Pretty.printAlterTableAction`, with
`rlsToSql` kept in `Pg.Stmt` so the four RLS renderings are still defined once.

**The 16 existing printer pins passing unchanged is the evidence that move was
byte-neutral** — they assert exact output, so any drift would have failed them.

`deriving DecidableEq, Repr` is gone from `AlterTableAction`, matching
`ColumnDef` and `TableConstraint`, which already omit it because `Expr` is a
nested inductive.

### New pins

17 in `Pg/AstDropAlterTest.lean`, one per new shape. Two are pinned to output
that reads oddly and is nonetheless correct — `isNotNull` parenthesises its own
operand so a `CHECK` renders doubled parens, and `typeCast` wraps the whole cast.
Pinned as the printer emits, not as it would ideally read: the pin's job is to
catch drift, not to editorialise.

### Still missing

Top-level DML — `INSERT`/`UPDATE`/`DELETE` remain PL/pgSQL-body-only. Also
`ALTER TYPE ... ADD VALUE`, views, sequences, extensions, `GRANT`/`REVOKE`,
`COMMENT ON`. And `Stmt` has no `raw : String` arm; it must never get one, as
that would make every theorem stated over this AST vacuous.

## 17.6.0 — carved out of rules_postgres

`Pg.{Ty,Ast,Stmt,AstSmart,Pretty,ProceduralSurface,RegexAst}` plus the PL/pgSQL
layer and the 16 per-constructor printer pins, extracted from
`tomato-bazel/rules_postgres` with `git filter-repo`, history preserved
(14 commits). 34 files, 5,983 lines, each verified byte-identical to source by
sha256.

**The seam works.** `Pg/Ast.lean` does
`abbrev Expr := Polyglot.Sql.Ast.Expr ExprExt` against `@sqlast`, and
`Pg.Catalog.QualifiedName` from `@pgcatalog` serves as `Identifier` — both arriving
as **compiled oleans**, not sources. All 16 printer pins pass against the compiled
core, which is the load-bearing check: they assert exact printed output, so if
consuming the core as oleans changed anything observable they would fail.

**Not `rules_lang`.** Its atlas also ships `Polyglot.Sql.*`, so depending on both
would put two providers of one module namespace in a single dep closure. Taking
`@sqlast` sidesteps that by construction rather than by coordinating a `rules_lang`
release — which was the one step of the leangres split that looked like it could
not be done additively, and turned out not to need coordinating at all.

**Per-target compile cost.** `rules_postgres` re-listed all ten core sources in
every one of the 16 pin targets. Here each lists only its own file and takes the
compiled core via `deps`: 16 × 11 = 176 file-compiles becomes 7 (once) + 16 = 23.

Requires `rules_lean` 0.6.1 — earlier releases' `lean_olean_archive` fails on linux.
