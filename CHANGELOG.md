# Changelog

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
