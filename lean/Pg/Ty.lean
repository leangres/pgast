/-
Pg.Ty — closed sum of postgres types we model.

The typed-AST discipline replaces raw-`String` type labels on
`FuncParam` / `ColumnDef` / function signatures with this closed
inductive. With `PgType` typed, the typing judgement `HasTy : Expr
→ PgType → Prop` (defined in Pg.Typing / consumers' equivalents)
becomes a real proof obligation rather than a string-shaped wish.

Coverage: every type a column / parameter / callee returns in the
modeled emit surface gets a constructor here. New types add as
constructors before they can be referenced.

Moved from Aion's `lean/Aion/Db/PgTy.lean` as part of PgAst
extraction Phase 1b (see Aion's
`narrative/sql-split-phase-1b-execution-plan.md`).
-/

namespace Pg.Ty

/-- The closed sum of postgres types modeled by the SQL emitter. -/
inductive PgType where
  | bigint      : PgType
  /-- `BIGSERIAL` — Postgres shorthand for `BIGINT NOT NULL DEFAULT
      nextval(...)` with an auto-created sequence. Emitted as a
      type keyword (libpg_query accepts that surface) rather than
      unfolded sugar. -/
  | bigserial   : PgType
  /-- `SERIAL` — same as `BIGSERIAL` but backed by INTEGER. -/
  | serial      : PgType
  | integer     : PgType
  | smallint    : PgType
  | text        : PgType
  | boolean     : PgType
  | ltree       : PgType
  | timestamptz : PgType
  /-- Postgres object-id type. -/
  | oid         : PgType
  /-- Binary JSON (`JSONB`). -/
  | jsonb       : PgType
  /-- Binary blob (`BYTEA`). -/
  | bytea       : PgType
  /-- 128-bit UUID. -/
  | uuid        : PgType
  /-- IPv4/IPv6 network address column. -/
  | inet        : PgType
  /-- Postgres `INTERVAL` — a duration value. The literal surface
      is a text-typed string cast to INTERVAL via `Expr.typeCast`;
      no first-class interval-literal constructor (the cast pattern
      composes cleanly with the existing AST). -/
  | interval    : PgType
  /-- Postgres `REGCLASS` — table-name OID type. Casts from text
      to `regclass` resolve the name to its catalog OID. -/
  | regclass    : PgType
  /-- Postgres `NAME` — internal 64-byte (NAMEDATALEN) identifier
      type. Used for system-catalog columns like role names,
      database names, schema names. -/
  | name        : PgType
  /-- Postgres `CHAR` — single character (`"char"` internal type
      in catalogs, distinct from CHAR(n)). Used by
      `pg_proc.provolatile`, `pg_proc.prokind` etc. as single-
      letter discriminators. -/
  | char        : PgType
  /-- Postgres `NUMERIC` — arbitrary-precision decimal. Used for
      intermediate division results where INTEGER division would
      truncate. -/
  | numeric     : PgType
  /-- Postgres `ACLITEM` — single access-control-list entry, the
      element type of `pg_class.relacl` / `pg_proc.proacl` /
      `pg_namespace.nspacl`. Opaque to user-level SQL beyond
      equality and text conversion. -/
  | aclitem     : PgType
  /-- Postgres `REGROLE` — role-name OID type. A `regrole` value
      is an OID that, when cast from text or numeric, is resolved
      against `pg_authid` to give a role name. -/
  | regrole     : PgType
  /-- A user-defined type referenced by its schema-qualified name. -/
  | userDefined : String → PgType
  /-- Postgres array of another `PgType`: `T[]` in SQL surface. -/
  | array       : PgType → PgType
  /-- Postgres `TRIGGER` pseudo-type — the return type of trigger
      function declarations. -/
  | trigger     : PgType
  /-- Postgres `VOID` pseudo-type — the return type of functions
      that perform side effects without returning a value. Distinct
      from `RETURNS NULL`. -/
  | void        : PgType
deriving DecidableEq, Repr

/-- Render a `PgType` as the postgres surface keyword. -/
def PgType.toSql : PgType → String
  | .bigint         => "BIGINT"
  | .bigserial      => "BIGSERIAL"
  | .serial         => "SERIAL"
  | .integer        => "INTEGER"
  | .smallint       => "SMALLINT"
  | .text           => "TEXT"
  | .boolean        => "BOOLEAN"
  | .ltree          => "LTREE"
  | .timestamptz    => "TIMESTAMPTZ"
  | .oid            => "OID"
  | .jsonb          => "JSONB"
  | .bytea          => "BYTEA"
  | .uuid           => "UUID"
  | .inet           => "INET"
  | .interval       => "INTERVAL"
  | .regclass       => "REGCLASS"
  | .name           => "NAME"
  | .char           => "CHAR"
  | .numeric        => "NUMERIC"
  | .aclitem        => "ACLITEM"
  | .regrole        => "REGROLE"
  | .userDefined n  => n
  | .array t        => t.toSql ++ "[]"
  | .trigger        => "TRIGGER"
  | .void           => "VOID"

end Pg.Ty
