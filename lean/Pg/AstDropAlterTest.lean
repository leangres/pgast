/-
Printer pins for the DDL-closure arms: the full `AlterTableAction` set and the
`DROP` family.

Surface locks, not theorems. Each asserts the EXACT rendered bytes, so a printer
change that alters output fails here rather than silently shipping different SQL.
Combined with `printAlterTableAction`'s non-catchall match, a new action cannot
reach `Stmt` without both a rendering and a pin.

The RLS arms are pinned in `AstAlterTableTest.lean` and unchanged by this work —
that file passing is what proves moving their rendering out of
`AlterTableAction.toSql` was byte-neutral.
-/

import Pg.Ast
import Pg.Stmt
import Pg.AstSmart
import Pg.Pretty

namespace Pg.AstDropAlterTest

open Pg.Ast Pg.Stmt Pg.Ty Pg.Pretty

/-! ## Columns -/

example :
    printStmt (.alterTable
      { name := Identifier.qualified "graph" "resource"
      , action := .addColumn { name := "archived_at", pgType := .timestamptz } })
      = "ALTER TABLE graph.resource ADD COLUMN archived_at TIMESTAMPTZ;\n" := by
  native_decide

/-- `IF NOT EXISTS` makes the statement idempotent — the shape a re-runnable
    migration wants. -/
example :
    printStmt (.alterTable
      { name := Identifier.qualified "graph" "resource"
      , action := .addColumn { name := "tag", pgType := .text } true })
      = "ALTER TABLE graph.resource ADD COLUMN IF NOT EXISTS tag TEXT;\n" := by
  native_decide

/-- DROP COLUMN defaults to RESTRICT, so a column something still depends on is
    refused rather than silently taking the dependent with it. -/
example :
    printStmt (.alterTable
      { name := Identifier.qualified "graph" "resource"
      , action := .dropColumn "legacy_id" })
      = "ALTER TABLE graph.resource DROP COLUMN legacy_id RESTRICT;\n" := by
  native_decide

example :
    printStmt (.alterTable
      { name := Identifier.qualified "graph" "resource"
      , action := .dropColumn "legacy_id" true .cascade })
      = "ALTER TABLE graph.resource DROP COLUMN IF EXISTS legacy_id CASCADE;\n" := by
  native_decide

example :
    printStmt (.alterTable
      { name := Identifier.qualified "graph" "resource"
      , action := .setNotNull "kind" })
      = "ALTER TABLE graph.resource ALTER COLUMN kind SET NOT NULL;\n" := by
  native_decide

example :
    printStmt (.alterTable
      { name := Identifier.qualified "graph" "resource"
      , action := .setDefault "created_at" (.call "now" []) })
      = "ALTER TABLE graph.resource ALTER COLUMN created_at SET DEFAULT now();\n" := by
  native_decide

/-- `USING` is required whenever the types are not binary-coercible; Postgres
    rejects the statement otherwise, so the AST has to be able to carry it. -/
example :
    printStmt (.alterTable
      { name := Identifier.qualified "graph" "resource"
      , action := .setColumnType "external_id" .text
                    (some (.typeCast (.var "external_id") "TEXT")) })
      -- `typeCast` wraps the whole cast, so it renders `(external_id::TEXT)`.
      = "ALTER TABLE graph.resource ALTER COLUMN external_id TYPE TEXT " ++
        "USING (external_id::TEXT);\n" := by
  native_decide

/-! ## Constraints

    `NOT VALID` is the field that makes an online migration expressible: it adds
    the constraint under a brief lock WITHOUT scanning, while still enforcing on
    new and updated rows — so it can precede a backfill and close the race
    against concurrent writers. `VALIDATE CONSTRAINT` then scans separately. -/

example :
    printStmt (.alterTable
      { name := Identifier.qualified "graph" "resource"
      , action := .addConstraint (.check (.isNotNull (.var "kind")) (some "kind_nn")) true })
      -- `isNotNull` parenthesises its own operand, so the CHECK wrapper yields
      -- a doubled paren. Pinned as the printer actually emits it, not as it
      -- would ideally read — the pin's job is to catch drift, not to editorialise.
      = "ALTER TABLE graph.resource ADD CONSTRAINT kind_nn " ++
        "CHECK ((kind IS NOT NULL)) NOT VALID;\n" := by
  native_decide

example :
    printStmt (.alterTable
      { name := Identifier.qualified "graph" "resource"
      , action := .validateConstraint "kind_nn" })
      = "ALTER TABLE graph.resource VALIDATE CONSTRAINT kind_nn;\n" := by
  native_decide

/-! ## Renames and placement -/

example :
    printStmt (.alterTable
      { name := Identifier.qualified "graph" "resource"
      , action := .renameColumn "external_id" "slug" })
      = "ALTER TABLE graph.resource RENAME COLUMN external_id TO slug;\n" := by
  native_decide

example :
    printStmt (.alterTable
      { name := Identifier.qualified "graph" "resource"
      , action := .renameTable (Identifier.qualified "graph" "entity") })
      = "ALTER TABLE graph.resource RENAME TO graph.entity;\n" := by
  native_decide

/-! ## DROP -/

example :
    printStmt (.dropObject { target := .table (Identifier.qualified "graph" "old") })
      = "DROP TABLE graph.old RESTRICT;\n" := by
  native_decide

example :
    printStmt (.dropObject
      { target := .table (Identifier.qualified "graph" "old")
      , ifExists := true, behavior := .cascade })
      = "DROP TABLE IF EXISTS graph.old CASCADE;\n" := by
  native_decide

/-- CONCURRENTLY sits between the keyword and the name, and only INDEX takes it. -/
example :
    printStmt (.dropObject
      { target := .index (Identifier.qualified "graph" "idx_resource_kind") true
      , ifExists := true })
      = "DROP INDEX CONCURRENTLY IF EXISTS graph.idx_resource_kind RESTRICT;\n" := by
  native_decide

/-- Argument types are part of a function's identity: without them the statement
    is ambiguous wherever two overloads exist. -/
example :
    printStmt (.dropObject
      { target := .function (Identifier.qualified "graph" "has_permission") [.bigint, .text] })
      = "DROP FUNCTION graph.has_permission(BIGINT, TEXT) RESTRICT;\n" := by
  native_decide

/-- Table-scoped objects carry their table for the same reason. -/
example :
    printStmt (.dropObject
      { target := .policy "resource_select" (Identifier.qualified "graph" "resource") })
      = "DROP POLICY resource_select ON graph.resource RESTRICT;\n" := by
  native_decide

example :
    printStmt (.dropObject { target := .schema "legacy", behavior := .cascade })
      = "DROP SCHEMA legacy CASCADE;\n" := by
  native_decide

end Pg.AstDropAlterTest
