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
* `neg n`: `n` nested prefix ops (`- - - a`), a spine of depth `n`; `plus n` is a
  left-associative chain (`a + a + a`), a spine down the first children.
  The elaborator asks for the source range of every op node; the parser stamps each op
  node with its range when it builds it (`rangeInfo?`), so that each request is constant
  time instead of a walk down the spine.
  The stamped ranges must be the ones the walk would find, and the stamps must keep the
  whitespace that error positions are computed from. The checks below compare them on
  elaborated programs (spines, lists, absent and present trailing optionals) and on every
  tree of depth at most 2 over a few kinds of leaves.
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

op neg (x : E) : E => @[prec(50)] "-" x;
op plus (x : E, y : E) : E => @[prec(20), leftassoc] x " + " y;
op list (xs : CommaSepBy E) : E => "[" xs "]";

// A trailing optional element.
category Suf;
op suf (x : E) : Suf => "::" x;
op g (x : E, s : Option Suf) : E => "g " x s;

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

def neg (n : Nat) : String :=
  "program ParseGrowth;\neval " ++ String.join (List.replicate n "-") ++ "a;\n"

def plus (n : Nat) : String :=
  "program ParseGrowth;\neval a" ++ String.join (List.replicate n " + a") ++ ";\n"

/-- The name and the source range (byte offsets, end exclusive) of every op in `a`,
outermost first. -/
partial def opRanges (a : Arg) : List (String × Nat × Nat) :=
  match a with
  | .op o => (o.name.name, o.ann.start.byteIdx, o.ann.stop.byteIdx) :: o.args.toList.flatMap opRanges
  | .option _ (some a) => opRanges a
  | .seq _ _ as => as.toList.flatMap opRanges
  | _ => []

/-- The op ranges of every command of `text`, which must elaborate without errors. -/
def elabRanges (text : String) : Lean.CoreM (List (String × Nat × Nat)) := do
  let env ← Lean.getEnv
  let input : Lean.Parser.InputContext :=
    { inputString := text, fileName := "<growth>", fileMap := .ofString text }
  match Elab.elabProgram (dialectExt.getState env).loaded env input with
  | .error msgs => throwError "unexpected errors: {← msgs.toList.mapM (·.toString)}"
  | .ok p => return p.commands.toList.flatMap fun c => opRanges (.op c)

-- Ranges on spines down the last child (`---a`) and the first child (`a + a + a`), in a
-- list, and around absent and present trailing optionals: `g a` ends at `a`, not after
-- the space that follows it. The walk on unstamped trees finds the same ranges.
/--
info: [("eval", 21, 31), ("neg", 26, 30), ("neg", 27, 30), ("neg", 28, 30), ("atom", 29, 30), ("eval", 32, 47),
  ("plus", 37, 46), ("plus", 37, 42), ("atom", 37, 38), ("atom", 41, 42), ("atom", 45, 46), ("eval", 48, 61),
  ("list", 53, 60), ("atom", 54, 55), ("neg", 57, 59), ("atom", 58, 59), ("eval", 62, 74), ("g", 67, 72), ("g", 69, 72),
  ("atom", 71, 72), ("eval", 75, 90), ("g", 80, 89), ("atom", 82, 83), ("suf", 84, 89), ("neg", 87, 89),
  ("atom", 88, 89)]
-/
#guard_msgs in
#eval elabRanges "program ParseGrowth;\neval ---a;\neval a + a + a;\neval [a, -a];\neval g g a ;\neval g a :: -a;\n"

open Lean (Syntax SourceInfo) in
/-- `t'` gives the same `sourceLocPos` and `sourceLocEnd` as `t`, at every subtree. -/
partial def sameRanges (t t' : Syntax) : Bool :=
  sourceLocPos t == sourceLocPos t' && sourceLocEnd t == sourceLocEnd t' &&
    t.getArgs.size == t'.getArgs.size &&
    (t.getArgs.zip t'.getArgs).all fun (a, b) => sameRanges a b

open Lean (Syntax SourceInfo) in
/-- `t'` has the same leading whitespace at its head and trailing whitespace at its tail
as `t` (as positions in the input), at every subtree. -/
partial def sameWhitespace (t t' : Syntax) : Bool :=
  let ws (s : Syntax) :=
    (match s.getHeadInfo with | .original l .. => some (l.startPos, l.stopPos) | _ => none,
     match s.getTailInfo with | .original _ _ tr _ => some (tr.startPos, tr.stopPos) | _ => none)
  ws t == ws t' && t.getArgs.size == t'.getArgs.size &&
    (t.getArgs.zip t'.getArgs).all fun (a, b) => sameWhitespace a b

/-- The text that the leaves of `smallTrees` point into. -/
def smallText : String := "0123456789"

open Lean (Syntax SourceInfo) in
/-- Every tree of depth at most 2 whose nodes have no range of their own and at most two
children, and the same trees under a `choice` node. The leaves span text, have zero
width, are missing, are empty nodes, carry zero-width info over a child (as a zero-width
op does), are themselves a `choice`, carry `.synthetic` info (which the parser never
builds, so that a node over one keeps no stamp), are a node of another kind (as a list
is) over an op and a zero-width leaf, or are zero-width with empty whitespace (as an
absent optional is). Each other leaf with a range `a`–`b` has one character of leading
whitespace before `a` and one of trailing whitespace after `b`. -/
def smallTrees : Array Syntax := Id.run do
  let info (a b : Nat) :=
    SourceInfo.original ⟨smallText, ⟨a - 1⟩, ⟨a⟩⟩ ⟨a⟩ ⟨smallText, ⟨b⟩, ⟨b + 1⟩⟩ ⟨b⟩
  let tok (a b : Nat) : Syntax := .node (info a b) `tok #[]
  let node (cs : List Syntax) : Syntax := .node .none `op cs.toArray
  let choice (t : Syntax) : Syntax := .node .none Lean.choiceKind #[t, t]
  let empty (a : Nat) : Syntax :=
    .node (SourceInfo.original ⟨smallText, ⟨a⟩, ⟨a⟩⟩ ⟨a⟩ ⟨smallText, ⟨a⟩, ⟨a⟩⟩ ⟨a⟩) `tok #[]
  let leaves := [tok 1 2, tok 2 2, .atom (info 3 4) "x", tok 4 4, .missing, node [],
    .node (info 4 4) `op #[node [tok 4 4]], choice (node [tok 1 2]),
    .atom (.synthetic ⟨3⟩ ⟨4⟩) "s", .node .none `lst #[node [tok 1 2], empty 5], empty 5]
  let upTo2 (xs : List Syntax) := [[]] ++ xs.map ([·]) ++ xs.flatMap fun a => xs.map ([a, ·])
  let depth1 := (upTo2 leaves).map node
  let depth2 := (upTo2 (leaves ++ depth1)).map node
  let trees := depth1 ++ depth2
  return (trees ++ trees.map choice).toArray

open Lean (Syntax) in
/-- `t` with each of its `op` nodes that has no info stamped bottom-up with `rangeInfo?`,
as the parser stamps the nodes its ops build; the alternatives of a `choice` are such
nodes, the `choice` node is not. -/
partial def stampOps (t : Syntax) : Syntax :=
  match t with
  | .node info k args =>
    let n := Syntax.node info k (args.map stampOps)
    match info, k == `op with
    | .none, true => match rangeInfo? n with
      | some i => .node i k n.getArgs
      | none => n
    | _, _ => n
  | _ => t

-- Stamping changes no range and no whitespace on any of them; it stamps the root of
-- 13,528 of them.
/-- info: (42028, true, true, 13528) -/
#guard_msgs in
#eval (smallTrees.size, smallTrees.all (fun t => sameRanges t (stampOps t)),
  smallTrees.all (fun t => sameWhitespace t (stampOps t)),
  (smallTrees.filter fun t => match t, stampOps t with
    | .node .none .., .node .none .. => false | _, _ => true).size)

-- A parse error just after an op node is placed before the whitespace that follows the
-- node, as on an unstamped tree: `mkErrorMessage` reads that whitespace from the stamp.
/-- info: ["<growth>:2:11: error: unexpected token 'a'; expected ';'\n"] -/
#guard_msgs in
#eval elabMessages "program ParseGrowth;\neval a + -a   a;\n"

-- The same with a leading op on top, and with a comment in the whitespace: the error moves
-- back over the comment too, to the end of `-a`.
/--
info: ["<growth>:2:7: error: unexpected token 'a'; expected ';'\n",
  "<growth>:2:7: error: unexpected token 'a'; expected ';'\n"]
-/
#guard_msgs in
#eval return (← elabMessages "program ParseGrowth;\neval -a   a;\n") ++
  (← elabMessages "program ParseGrowth;\neval -a // c\n  a;\n")

#dialect
dialect ParseGrowthStamp;
category S;
op sAtom () : S => "a";
op sVar (v : Ident) : S => v;
op sNeg (x : S) : S => @[prec(50)] "-" x;
op sPlus (x : S, y : S) : S => @[prec(20), leftassoc] x " + " y;
op sList (xs : CommaSepBy S) : S => "[" xs "]";
op sNum (n : Num) : S => n;
// Two ops with the same syntax: `h` is ambiguous.
op sH1 (x : S) : S => "h " x;
op sH2 (x : S) : S => "h " x;
category SSuf;
op sSuf (x : S) : SSuf => "::" x;
op sG (x : S, t : Option SSuf) : S => "g " x t;
category STail;
op sNoTail () : STail => ;
op sTail (x : S) : STail => "tl " x;
op sT (x : S, t : STail) : S => "t " x t;
op sEval (e : S) : Command => "stamp " e ";";
#end

/-- The tree that the parser builds for the command `text` of `ParseGrowthStamp`. -/
def parseStamp (text : String) : Lean.CoreM Lean.Syntax := do
  let env ← Lean.getEnv
  let loaded := (dialectExt.getState env).loaded
  let s0 : Elab.DeclState := { openDialects := #[], openDialectSet := {} }
  let s := (s0.ensureLoaded! loaded "Init").ensureLoaded! loaded "ParseGrowthStamp"
  let input : Lean.Parser.InputContext :=
    { inputString := text, fileName := "<stamp>", fileMap := .ofString text }
  let ps := Parser.runCatParser s.tokenTable s.parserMap env input 0 text.rawEndPos q`Init.Command
  if ps.hasError then throwError "parse error in {text}"
  return ps.stxStack.back

/-- Whether `k` is the kind of a node built by an op of `ParseGrowthStamp`. -/
def isStampOp (k : Lean.SyntaxNodeKind) : Bool := k.getRoot == `ParseGrowthStamp

open Lean (Syntax) in
/-- Whether every op node of `t` carries info. -/
partial def opsStamped (t : Syntax) : Bool :=
  (match t with | .node .none k _ => !isStampOp k | _ => true) && t.getArgs.all opsStamped

open Lean (Syntax) in
/-- `t` with the info of every op node removed: the tree as the parser builds it without
`stampFn`. The walk then finds the emptiness of the empty-template op `sNoTail` by
computing its range. -/
partial def unstampOps (t : Syntax) : Syntax :=
  match t with
  | .node info k args => .node (if isStampOp k then .none else info) k (args.map unstampOps)
  | _ => t

-- Every op node the parser builds carries info: leading (`sNeg`), trailing (`sPlus`),
-- passthrough (`sVar`), list (`sList`), over a literal (`sNum`), trailing optional present
-- and absent (`sG`), an empty template (`sNoTail`), and the alternatives of a `choice`,
-- alone and under a trailing op (`sH1`, `sH2`); and the stamps give the ranges and the
-- whitespace of the unstamped tree.
/--
info: [(true, true, true), (true, true, true), (true, true, true), (true, true, true), (true, true, true), (true, true, true),
  (true, true, true), (true, true, true), (true, true, true)]
-/
#guard_msgs in
#eval ["stamp a + -x + [a, -a, x] ;", "stamp a + a + a;", "stamp ---x;", "stamp g a ;",
    "stamp g a :: -a;\n", "stamp t a ;", "stamp t a tl x ;", "stamp h a + 7 ;", "stamp a + h 7 ;"].mapM fun text => do
  let t ← parseStamp text
  return (opsStamped t, sameRanges t (unstampOps t), sameWhitespace t (unstampOps t))

#dialect
dialect ParseGrowthOpt;
category C;
op cVar (n : Ident) : C => n;
op cNoName (n : Option Ident) : C => n;
op cParen (e : C) : C => "(" e ")";
op cEval (e : C) : Command => "opt " e ";";
#end

-- An op whose syntax starts with an optional identifier is tried only before an
-- identifier, so it does not match empty input.
/--
info: ["<growth>:2:5: error: unexpected token ')'; expected ParseGrowthOpt.C\n",
  "<growth>:2:3: error: unexpected token ';'; expected ParseGrowthOpt.C\n"]
-/
#guard_msgs in
#eval return (← elabMessages "program ParseGrowthOpt;\nopt ( );\n") ++
  (← elabMessages "program ParseGrowthOpt;\nopt ;\n")

/-- Small allocations (Lean's heartbeats) made while running `act`. -/
def allocations (act : Lean.CoreM Unit) : Lean.CoreM Nat := do
  let h0 ← IO.getNumHeartbeats
  act
  return (← IO.getNumHeartbeats) - h0

/-- Elaborates `neg n` as a program; it must elaborate without errors. -/
def elabNeg (n : Nat) : Lean.CoreM Unit := do
  let msgs ← elabMessages (neg n)
  unless msgs.isEmpty do throwError "unexpected messages: {msgs}"

/-- Parses and elaborates the command of `neg n` alone, with `parseCategoryFromDialect`. -/
def parseNeg (n : Nat) : Lean.CoreM Unit := do
  let text := "eval " ++ String.join (List.replicate n "-") ++ "a;"
  let input := Parser.stringInputContext "<growth>" text
  let _ ← Elab.parseCategoryFromDialect (dialectExt.getState (← Lean.getEnv)).loaded
    q`Init.Command input

-- The stamps are in place, on both paths: multiplying `n` in `neg n` by 4 must multiply the
-- allocations by less than 8 (about 4 if linear, 16 if quadratic). Without them,
-- finding the end of each node walks down the spine and allocates at every step, so the
-- allocations grow quadratically. (The walk down first children, as in `plus`, does not
-- allocate; only its time grows.) A first call warms up. This check comes first, so that a
-- regression fails here instead of running the deep spines below.
#guard_msgs in
#eval do
  for (path, act) in [("elabProgram", elabNeg), ("parseCategoryFromDialect", parseNeg)] do
    let _ ← allocations (act 1000)
    let a1 ← allocations (act 1000)
    let a4 ← allocations (act 4000)
    unless a4 < 8 * a1 do
      throwError "{path}: allocations grew from {a1} to {a4} when `n` grew from 1,000 to 4,000"
  -- Deep spines elaborate without errors, and without overflowing the stack.
  for text in [neg 10000, plus 10000] do
    let msgs ← elabMessages text
    unless msgs.isEmpty do throwError "unexpected messages: {msgs}"

end
