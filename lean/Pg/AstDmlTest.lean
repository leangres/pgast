/-
Printer pins for top-level DML.

`INSERT`/`UPDATE`/`DELETE` previously existed only inside PL/pgSQL function
bodies. These pin the top-level forms — the shape the seed and backfill half of
a migration corpus is written in.

Pinned to what the printer actually emits, obtained by running it rather than by
guessing. Two renderings read oddly and are correct: `isNull` and `eq`
parenthesise their own operands, so a WHERE comes out wrapped. A pin's job is to
catch drift, not to editorialise; tightening either is a separate change that
these pins would then catch.
-/

import Pg.Ast
import Pg.Stmt
import Pg.AstSmart
import Pg.Pretty

namespace Pg.AstDmlTest

open Pg.Ast Pg.Stmt Pg.Ty Pg.Pretty

private def resource : Identifier := Identifier.qualified "graph" "resource"

/-! ## INSERT -/

example :
    printStmt (.insert
      { target := resource, columns := ["id", "kind"]
      , source := .values [[.litConst (.int 1), .litConst (.text "user")]] })
      = "INSERT INTO graph.resource (id, kind) VALUES (1, 'user');\n" := by
  native_decide

/-- Multi-row VALUES — the seed-data shape. -/
example :
    printStmt (.insert
      { target := resource, columns := ["id"]
      , source := .values [[.litConst (.int 1)], [.litConst (.int 2)]] })
      = "INSERT INTO graph.resource (id) VALUES (1), (2);\n" := by
  native_decide

/-- `ON CONFLICT DO NOTHING` + `RETURNING` — the idempotent-seed shape, and the
    reason `ON CONFLICT` is shared with the PL/pgSQL arms rather than duplicated. -/
example :
    printStmt (.insert
      { target := resource, columns := ["id"]
      , source := .values [[.litConst (.int 1)]]
      , onConflict := some .doNothing
      , returning := [.var "id"] })
      = "INSERT INTO graph.resource (id) VALUES (1) ON CONFLICT DO NOTHING " ++
        "RETURNING id;\n" := by
  native_decide

/-- `INSERT … SELECT` — the backfill shape. -/
example :
    printStmt (.insert
      { target := resource, columns := ["id"]
      , source := .query
          { projections := [.var "id"]
          , source := .ext (.tableQualified (Identifier.qualified "graph" "legacy") none) } })
      = "INSERT INTO graph.resource (id) SELECT id FROM graph.legacy;\n" := by
  native_decide

/-! ## UPDATE -/

example :
    printStmt (.update
      { target := resource
      , sets := [{ column := "kind", value := .litConst (.text "x") }]
      , whereCond := some (.isNull (.var "kind")) })
      = "UPDATE graph.resource SET kind = 'x' WHERE (kind IS NULL);\n" := by
  native_decide

/-- Multiple SET clauses keep their declared ORDER — which is why `sets` is a
    list rather than a map, since the order is observable in the output. -/
example :
    printStmt (.update
      { target := resource
      , sets := [ { column := "b", value := .litConst (.int 2) }
                , { column := "a", value := .litConst (.int 1) } ] })
      = "UPDATE graph.resource SET b = 2, a = 1;\n" := by
  native_decide

/-! ## DELETE

    No guard against a missing WHERE. An unqualified DELETE is valid SQL and
    occasionally intended; deciding it is dangerous belongs to the hazard
    classifier, not the printer. -/

example :
    printStmt (.delete
      { target := resource
      , whereCond := some (.eq (.var "id") (.litConst (.int 1))) })
      = "DELETE FROM graph.resource WHERE (id = 1);\n" := by
  native_decide

example :
    printStmt (.delete { target := resource })
      = "DELETE FROM graph.resource;\n" := by
  native_decide

end Pg.AstDmlTest
