/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import StrataDDM.Integration.Lean

/-!
A command that fails part-way through its bindings must leave the global
context as it was before the command (`GlobalContext.addCommandOrRollback`).
-/

meta section

#dialect
dialect TestRollback;

type int;

@[declare(name, tp)]
op command_const (name : Ident, tp : Type) : Command =>
  "const " name ":" tp ";\n";

@[declare(n1, t1), declare(n2, t2)]
op command_pair (n1 : Ident, t1 : Type, n2 : Ident, t2 : Type) : Command =>
  "pair " n1 ":" t1 ", " n2 ":" t2 ";\n";
#end

-- `pair` defines `A`, then fails on the second `A`. The first `A` must be
-- rolled back, so the later `const A` is not a duplicate.
/--
error: 'A' already defined
-/
#guard_msgs in
def partialBindingRollback :=
#strata
program TestRollback;
  pair A: int, A: int;
  const A: int;
#end

-- Types pre-registered by a `@[preRegisterTypes]` block must be rolled back too.
-- The elaborator rejects such duplicates before `addCommand` runs, so this calls
-- `addCommandOrRollback` directly: the block pre-registers `B`, then fails on `X`,
-- which the context already defines.
#dialect
dialect TestRollbackPre;

metadata declareDatatype (name : Ident, typeParams : Ident,
  constructors : Ident, testerTemplate : FunctionTemplate,
  accessorTemplate : FunctionTemplate);

type int;

category Binding;
@[declare(name, tp)]
op mkBinding (name : Ident, tp : TypeP) : Binding => @[prec(40)] name ":" tp;

category Bindings;
@[scope(bindings)]
op mkBindings (bindings : CommaSepBy Binding) : Bindings => "(" bindings ")";

category Constructor;
category ConstructorList;

@[constructor(name, fields)]
op constructor_mk (name : Ident, fields : Option (CommaSepBy Binding)) : Constructor =>
  name "(" fields ")";

@[constructorListAtom(c)]
op constructorListAtom (c : Constructor) : ConstructorList => c;

@[constructorListPush(cl, c)]
op constructorListPush (cl : ConstructorList, c : Constructor) : ConstructorList =>
  @[prec(30), leftassoc] cl ", " c;

category DatatypeDecl;

@[declareDatatype(name, typeParams, constructors,
    perConstructor([.literal "..is", .constructor],
                   [.datatype], .builtin "bool"),
    perField([.datatype, .literal "..", .field], [.datatype], .fieldType))]
op datatype_decl (name : Ident,
                  typeParams : Option Bindings,
                  @[scopeTVar(typeParams)] constructors : ConstructorList) : DatatypeDecl =>
  "datatype " name typeParams " { " constructors " }";

@[scope(datatypes), preRegisterTypes(datatypes)]
op command_datatypes (datatypes : NewlineSepBy DatatypeDecl) : Command =>
  datatypes ";\n";

@[declare(name, tp)]
op command_const (name : Ident, tp : Type) : Command =>
  "const " name ":" tp ";\n";
#end

def preRegBlock :=
#strata
program TestRollbackPre;
  datatype B { MkB() }
  datatype X { MkX() };
#end

def preRegBase :=
#strata
program TestRollbackPre;
  const X: int;
#end

#guard
  let base := preRegBase.globalContext
  let size := base.vars.size
  let (gctx, error?) := base.addCommandOrRollback preRegBlock.dialects preRegBlock.commands[0]!
  error? == some "'X' already defined" && gctx.vars.size == size &&
    gctx.findIndex? "B" == none && gctx.findIndex? "X" == some 0

end
