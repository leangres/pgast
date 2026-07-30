import Lake
open Lake DSL

-- Minimal Lake workspace: pins the Lean toolchain this module type-checks under.
--
-- Dep-free. The AST layer imports Lean core plus two published leangres modules
-- (sqlast for Polyglot.Sql.Ast, pgcatalog for Pg.Catalog.RegTypes) -- both arriving
-- as compiled oleans, not as Lake packages. So there is no `require` here, and
-- there should not be one: a nominal `require batteries` elsewhere in this
-- ecosystem cost ~15 minutes on every CI run that pulled the module in.
--
-- The toolchain must match every repo whose oleans this consumes or that consumes
-- these. `.olean` is a compacted heap image -- neither Lean-version- nor
-- architecture-portable -- so a mismatch fails hard at use.
package «pgast» where
