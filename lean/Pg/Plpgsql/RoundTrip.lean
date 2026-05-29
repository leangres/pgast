/-
Pg.Plpgsql.RoundTrip — round-trip theorem for the BodyStmt
emit → parse pipeline.

Bridge PR C of three. States the headline correctness property
for the emit ↔ parse chain set up by PRs A (`plpgsql_to_json` C
tool) and B (Lean JSON reader): **printing a BodyStmt list and
then parsing it back recovers the same list, under a named
parser-reflection stipulation.**

## The theorem (informal)

```
parseBody (printBody body) = some body
```

where:
  * `printBody` is `Pg.Pretty.printBody` (PgPretty).
  * `parseBody` is the composition
      C_tool(plpgsql_to_json) ∘ Lean.PlpgsqlJsonReader.readBodyList
    — abstracted here as a `BodyParser` oracle so this module
    doesn't depend on the C tool's wiring or the Lean reader's
    completeness for arbitrary shapes.

## Design: LeafReflects pattern

Same modular pattern used by:
  * `HasPermissionLeafReflects` (#194 — `hasPermission_emit_iff_kernelImpl`)
  * `StatementExistsReflectsKernel` (#311 — `statement_*_iff_kernel`)
  * `KernelStatementOracle` (same)

We parameterise over an abstract `BodyParser` oracle and prove
the round-trip under a `ParserReflects` stipulation. Concrete
parser instances (the C tool + Lean reader composition) discharge
the stipulation per shape; the framework theorem holds for any
parser that satisfies it.

This keeps PR C independent of whether PRs A and B have landed
yet, and lets us prove specific-shape instances incrementally
as the Lean reader's coverage grows.

## What this PR DOESN'T prove

The stipulation `ParserReflects` is exactly the thing we're
naming. We're not proving the C tool + Lean reader composition
satisfies it — that's a property that has to be discharged for
each emit shape via inspection or further proof work.

What we have here is the *formal statement* that, once
discharged, gives us a kernel-checked round-trip. That's
exactly the role `HasPermissionLeafReflects` plays for the
SQL-emit chain.
-/

import Pg.Ast
import Pg.Stmt
import Pg.AstSmart
import Pg.Pretty

namespace Pg.Plpgsql.RoundTrip

open Polyglot.Sql.Ast Pg.Ast Pg.Stmt
open Pg.Pretty

/-! ## Abstract parser oracle -/

/-- A `BodyParser` maps a PL/pgSQL-text input to the BodyStmt
    list it parses into (or `none` on parse error / unsupported
    shape). Concrete instances:
      * The composition `Lean.readBodyList ∘ C_tool.plpgsql_to_json`
        — i.e. what PR A + PR B provide once both land.
      * Hand-rolled mock parsers used in proof instances. -/
abbrev BodyParser := String → Option (List BodyStmt)

/-! ## The stipulation -/

/-- The runtime-stipulation predicate: `parser` recovers `body`
    when fed `body`'s printed form. Named so theorems can require
    it as a hypothesis without committing to which parser is in
    use. -/
def ParserReflects (parser : BodyParser) (body : List BodyStmt) : Prop :=
  parser (printBody body) = some body

/-! ## The headline theorem

The proof is trivial under the stipulation — that's the *point*
of the LeafReflects pattern. What's load-bearing is the theorem
*statement*: it names exactly what would need to hold for the
emit ↔ parse round-trip to be sound. -/

/-- **Round-trip soundness.** Under a parser that reflects the
    given body (the `ParserReflects` stipulation), printing the
    body and then parsing it back recovers the original. -/
theorem body_emit_roundtrips
    (parser : BodyParser) (body : List BodyStmt)
    (h : ParserReflects parser body) :
    parser (printBody body) = some body := h

/-! ## A concrete-instance helper

A specific BodyStmt list one might want to round-trip: the body
of `update_updated_at_column` (the simplest production trigger).
Used by the instance theorem below to demonstrate how to apply
the framework. -/

/-- The body of `update_updated_at_column`: assign NEW.updated_at
    to `now()`, return NEW. Mirrors
    `Aion.Db.V0.AionSchema.TriggerFunctions.updateUpdatedAtColumn.body`. -/
def updateUpdatedAtBody : List BodyStmt :=
  [ .assignNew "updated_at" (.callBuiltin "now" [])
  , .returnRow .newRow ]

/-- A concrete-instance theorem: for ANY parser that reflects
    the `updateUpdatedAtBody` shape, the round-trip holds.
    Specialises `body_emit_roundtrips` to a fixed body —
    callers wiring up the C tool + Lean reader composition
    discharge the stipulation via direct evaluation. -/
theorem updateUpdatedAt_roundtrips
    (parser : BodyParser)
    (h : ParserReflects parser updateUpdatedAtBody) :
    parser (printBody updateUpdatedAtBody) = some updateUpdatedAtBody :=
  body_emit_roundtrips parser updateUpdatedAtBody h

end Pg.Plpgsql.RoundTrip
