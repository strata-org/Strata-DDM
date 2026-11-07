/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import StrataDDM.Integration.Lean

open StrataDDM
meta section

namespace StrataDDM.FormatContextReuse.Tests

-- A format context built once from the dialects, then given each program's global context with
-- `FormatContext.withGlobalContext`, prints every program byte for byte as a context built for
-- that program does.
#dialect
dialect FCR;
type int;
category Expression;
op var (name : Ident) : Expression => name;
op add (a : Expression, b : Expression) : Expression => @[prec(10), leftassoc] a " + " b;
op call (f : Ident, a : Expression) : Expression => f "(" a ")";
op oldE (e : Expression) : Expression => "old(" e ")";
op assign (lhs : Ident, rhs : Expression) : Command => lhs:0 " := " rhs ";";
op ret (e : Expression) : Command => "return " e ";";
@[declare(name, tp)]
op varDecl (name : Ident, tp : Type) : Command => "var " name " : " tp ";";
op check (tp : Type, v : tp) : Command => "check " v " : " tp ";";
category Binding;
@[declare(name, tp)]
op mkBinding (name : Ident, tp : Type) : Binding => name ":" tp;
category Bindings;
@[scope(bindings)]
op mkBindings (bindings : CommaSepBy Binding) : Bindings => "(" bindings ")";
@[declareFn(name, b, r)]
op fdecl (name : Ident, b : Bindings, r : Type, @[scope(b)] body : r) : Command =>
  "function " name b " : " r " = " body ";";
#end

def opts : FormatOptions := { quoteKeywords := true }

def fixtures : List Program := [
  (#strata
  program FCR;
  |return| := |return| + returned + x;
  return |return|;
  #end).program,
  (#strata
  program FCR;
  x := |old|(y) + old(z);
  #end).program,
  (#strata
  program FCR;
  var x : int;
  check x : int;
  #end).program,
  -- `check x` is printed before the later declaration of the keyword-named `|check|`.
  (#strata
  program FCR;
  var x : int;
  check x : int;
  var |check| : int;
  check |check| : int;
  #end).program,
  -- A keyword-named bound variable and a keyword-named function.
  (#strata
  program FCR;
  var y : int;
  function |function|(|var| : int) : int = |var|;
  check y : int;
  #end).program
]

/-- Prints the commands of `p` with the format context `c`. -/
def formatWith (c : FormatContext) (p : Program) : String :=
  (p.commands.foldl (init := f!"program {p.dialect};\n") fun f cmd =>
    f ++ (mformat cmd c p.formatState).format).pretty

/-- One context for all fixtures, built from the dialects before any program is printed. -/
def shared : FormatContext :=
  FormatContext.ofDialects (fixtures.head!.dialects) {} opts

#guard fixtures.all fun p =>
  formatWith (shared.withGlobalContext p.globalContext) p == formatWith (p.formatContext opts) p

-- The shared context prints the declared names, keywords quoted.
/--
info: "program FCR;\nvar x : int;check x : int;var |check| : int;check |check| : int;"
-/
#guard_msgs in
#eval formatWith (shared.withGlobalContext fixtures[3]!.globalContext) fixtures[3]!

-- Without the program's global context, its declared names are unknown to the shared context.
#guard formatWith shared fixtures[3]! != formatWith (fixtures[3]!.formatContext opts) fixtures[3]!

end StrataDDM.FormatContextReuse.Tests

end
