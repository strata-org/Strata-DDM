/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import StrataDDM.Integration.Lean

/-!
# Inputs whose shape could make elaboration grow faster than the input

The parser memoizes each category at each position, so it does not parse a shared
subtree twice; the checks here are about the elaborator that runs on its result.

* `amb n`: `n` nested uses of two ops with the same syntax (`h1`, `h2`).
  Every level is ambiguous, so the parser returns nested `choice` nodes whose
  alternatives share their subtrees.
  The error names the alternatives of the outermost `choice`; it must not print the
  trees, which would hold `2^n` leaves.
* The same for two functions (`fn`) with the same syntax, which are elaborated as
  expressions rather than as ops.
* The same for an ambiguous datatype or function inside a block whose names are
  registered before its members are elaborated (`preRegisterTypes`,
  `preRegisterFunctions`).
-/

open StrataDDM

meta section

#dialect
dialect ParseGrowth;

category E;
op atom () : E => "a";

// Two ops with the same syntax: every `h` is ambiguous.
op h1 (x : E) : E => "h " x;
op h2 (x : E) : E => "h " x;

op eval (e : E) : Command => "eval " e ";";

// Two functions with the same syntax.
type T;
fn f1 (x : T) : T => "f " x;
fn f2 (x : T) : T => "f " x;
fn z () : T => "z";
op check (tp : Type, v : tp) : Command => "check " v " : " tp ";";
#end

/-- Elaborates `text` with the dialects of this file and returns the error messages. -/
def elabMessages (text : String) : Lean.CoreM (List String) := do
  let env ← Lean.getEnv
  let input : Lean.Parser.InputContext :=
    { inputString := text, fileName := "<growth>", fileMap := .ofString text }
  match Elab.elabProgram (dialectExt.getState env).loaded env input with
  | .error msgs => msgs.toList.mapM fun m => m.toString
  | .ok _ => return []

def amb (n : Nat) : String :=
  "program ParseGrowth;\neval " ++ String.join (List.replicate n "h ") ++ "a;\n"

-- One ambiguous op: the error names both alternatives, sorted.
/--
info: ["<growth>:2:5: error: Parsing ambiguity: the input parses as each of [ParseGrowth.h1, ParseGrowth.h2]\n"]
-/
#guard_msgs in
#eval elabMessages (amb 1)

-- The message does not grow with the nesting. (A message that printed the trees would
-- double in length at each level.)
/-- info: [[101], [101], [101], [101], [101], [101], [101]] -/
#guard_msgs in
#eval return (← [1, 2, 3, 4, 5, 6, 12].mapM fun n => return ((← elabMessages (amb n)).map String.length))

-- An ambiguous function application gets the same error, and its message does not grow
-- with the nesting either.
#guard_msgs in
#eval do
  let expected := "<growth>:2:6: error: Parsing ambiguity: the input parses as each of [ParseGrowth.f1, ParseGrowth.f2]\n"
  for n in [1, 2, 3, 12] do
    let text := "program ParseGrowth;\ncheck " ++ String.join (List.replicate n "f ") ++ "z : T;\n"
    let msgs ← elabMessages text
    unless msgs == [expected] do throwError "n = {n}: unexpected messages: {msgs}"

#dialect
dialect ParseGrowthBlocks;
metadata declareDatatype (name : Ident, typeParams : Ident,
  constructors : Ident, testerTemplate : FunctionTemplate,
  accessorTemplate : FunctionTemplate);
type T;
fn z () : T => "z";

category Binding;
@[declare(name, tp)]
op mkBinding (name : Ident, tp : TypeP) : Binding => @[prec(40)] name ":" tp;
category Bindings;
@[scope(bindings)]
op mkBindings (bindings : CommaSepBy Binding) : Bindings => "(" bindings ")";

category Constructor;
@[constructor(name, fields)]
op constructor_mk (name : Ident, fields : Option (CommaSepBy Binding)) : Constructor =>
  name "(" fields ")";
category ConstructorList;
@[constructorListAtom(c)]
op constructorListAtom (c : Constructor) : ConstructorList => c;

// Two datatype declarations with the same syntax, in a block that registers the
// datatypes' names first.
category DatatypeDecl;
@[declareDatatype(name, typeParams, constructors,
    perConstructor([.literal "..is", .constructor], [.datatype], .builtin "bool"),
    perField([.datatype, .literal "..", .field], [.datatype], .fieldType))]
op datatype1 (name : Ident, typeParams : Option Bindings,
              @[scopeTVar(typeParams)] constructors : ConstructorList) : DatatypeDecl =>
  "datatype " name typeParams " { " constructors " }";
@[declareDatatype(name, typeParams, constructors,
    perConstructor([.literal "..is", .constructor], [.datatype], .builtin "bool"),
    perField([.datatype, .literal "..", .field], [.datatype], .fieldType))]
op datatype2 (name : Ident, typeParams : Option Bindings,
              @[scopeTVar(typeParams)] constructors : ConstructorList) : DatatypeDecl =>
  "datatype " name typeParams " { " constructors " }";
@[declareDatatype(name, typeParams, constructors,
    perConstructor([.literal "..is", .constructor], [.datatype], .builtin "bool"),
    perField([.datatype, .literal "..", .field], [.datatype], .fieldType))]
op data (name : Ident, typeParams : Option Bindings,
         @[scopeTVar(typeParams)] constructors : ConstructorList) : DatatypeDecl =>
  "data " name typeParams " { " constructors " }";
@[scope(datatypes), preRegisterTypes(datatypes)]
op datatypes (datatypes : NewlineSepBy DatatypeDecl) : Command => datatypes ";\n";

// Two function declarations with the same syntax, in a block that registers the
// functions' names first.
category FnDecl;
@[declareFn(name, b, r)]
op function1 (name : Ident, b : Bindings, r : Type, @[scope(b)] c : r) : FnDecl =>
  "function " name b " : " r " { " c " }";
@[declareFn(name, b, r)]
op function2 (name : Ident, b : Bindings, r : Type, @[scope(b)] c : r) : FnDecl =>
  "function " name b " : " r " { " c " }";
@[declareFn(name, b, r)]
op fun (name : Ident, b : Bindings, r : Type, @[scope(b)] c : r) : FnDecl =>
  "fun " name b " : " r " { " c " }";
@[scope(fns), preRegisterFunctions(fns)]
op functions (fns : NewlineSepBy FnDecl) : Command => "rec " fns ";\n";
#end

-- An ambiguous member of a block gets the same error, once, and nothing else; the names
-- registered before it (`A`, `h`) stay registered, for their own members and for later ones.
/--
info: ["<growth>:3:0: error: Parsing ambiguity: the input parses as each of [ParseGrowthBlocks.datatype1, ParseGrowthBlocks.datatype2]\n"]
-/
#guard_msgs in
#eval elabMessages
  "program ParseGrowthBlocks;\ndata A { MkA(a : A) }\ndatatype D { MkD() }\ndata B { MkB(a : A) };\n"

/--
info: ["<growth>:3:0: error: Parsing ambiguity: the input parses as each of [ParseGrowthBlocks.function1, ParseGrowthBlocks.function2]\n"]
-/
#guard_msgs in
#eval elabMessages
  "program ParseGrowthBlocks;\nrec fun h(x : T) : T { h(x) }\nfunction g(x : T) : T { z }\nfun k(x : T) : T { h(x) };\n"

end
