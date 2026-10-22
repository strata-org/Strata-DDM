/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import StrataDDM.Integration.Lean

open StrataDDM
meta section
-- With `quoteKeywords`, an identifier that is spelled like one of the dialects' tokens prints
-- pipe-delimited, so that the printed program parses again.  Without it, it prints bare.
#dialect
dialect KeywordIdent;

type int;
fn notE (b : int) : int => "not " b;

category Expression;

op var (name : Ident) : Expression => name;
op add (a : Expression, b : Expression) : Expression => @[prec(10), leftassoc] a " + " b;
op call (f : Ident, a : Expression) : Expression => f "(" a ")";
op oldE (e : Expression) : Expression => "old(" e ")";
op assign (lhs : Ident, rhs : Expression) : Command => lhs:0 " := " rhs ";";
op ret (e : Expression) : Command => "return " e ";";
op block (c : Command) : Command => "begin" indent(2, "loop " c) "end;";

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

namespace KeywordIdent

#strata_gen KeywordIdent

end KeywordIdent

/-- Prints `p` with `quoteKeywords`, reads the printed text back, and checks that it gives the
same commands, source positions aside.  Returns the printed text. -/
def roundTrip (p : Program) : Lean.CoreM Std.Format := do
  let text := (p.format { quoteKeywords := true }).pretty
  let env ← Lean.getEnv
  let input : Lean.Parser.InputContext :=
    { inputString := text, fileName := "<printed>", fileMap := .ofString text }
  match Elab.elabProgram (dialectExt.getState env).loaded env input with
  | .error msgs => throwError Lean.MessageData.joinSep (msgs.toList.map (·.data)) "\n"
  | .ok q =>
    let erase (p : Program) := p.commands.map (·.mapAnn fun _ => ())
    unless erase q == erase p do
      throwError "the printed text reads back as a different program"
    return text

-- `return` is a token of the dialect, so a variable or a target named `return` is quoted.
-- Names that contain a token as a part, such as `returned`, are not quoted.
/--
info: program KeywordIdent;
|return| := |return| + returned + x;return |return|;
-/
#guard_msgs in
#eval roundTrip (#strata
program KeywordIdent;
|return| := |return| + returned + x;
return |return|;
#end).program

-- By default the identifier prints bare.
/--
info: program KeywordIdent;
return := return + returned + x;return return;
-/
#guard_msgs in
#eval (#strata
program KeywordIdent;
|return| := |return| + returned + x;
return |return|;
#end).format

-- The tokens of a function's syntax (`not`), of an indented block (`loop`) and of the Init
-- dialect (`some`, `true`) count too.
/--
info: program KeywordIdent;
|not| := |loop| + |some| + |true| + |begin|;
-/
#guard_msgs in
#eval roundTrip (#strata
program KeywordIdent;
|not| := |loop| + |some| + |true| + |begin|;
#end).program

-- A token that starts like an identifier, `old(`, makes that identifier unreadable: bare,
-- `old(y)` would read as the operation `oldE`, not as a call of `old`.
/--
info: program KeywordIdent;
x := |old|(y);
-/
#guard_msgs in
#eval roundTrip (#strata
program KeywordIdent;
x := |old|(y);
#end).program

-- The names of declared and bound variables are quoted the same way.
/--
info: program KeywordIdent;
var |check| : int;check |check| : int;function f(|function|:int) : int = |function|;
-/
#guard_msgs in
#eval roundTrip (#strata
program KeywordIdent;
var |check| : int;
check |check| : int;
function f(|function| : int) : int = |function|;
#end).program

-- The tokens of an imported dialect count; those of a dialect that is only loaded do not.
#dialect
dialect KeywordOther;
op m (x : Ident) : Command => "module " x ";";
#end

#dialect
dialect KeywordImports;
import KeywordOther;
category Expression;
op var (name : Ident) : Expression => name;
op assign (lhs : Ident, rhs : Expression) : Command => lhs:0 " := " rhs ";";
#end

/--
info: program KeywordImports;
|module| := x;
-/
#guard_msgs in
#eval roundTrip (#strata
program KeywordImports;
|module| := x;
#end).program

/--
info: program KeywordIdent;
module := x;
-/
#guard_msgs in
#eval roundTrip (#strata
program KeywordIdent;
module := x;
#end).program

-- A token can end inside a name that follows other text: the parser reads the longest token there
-- without checking where a name ends.
#dialect
dialect KeywordRuns;
category Expression;
op var (name : Ident) : Expression => name;
op str (s : Str) : Expression => s;
op call (f : Ident, a : Expression) : Expression => f "(" a ")";
op add (a : Expression, b : Expression) : Expression => @[prec(10), leftassoc] a " + " b;
op sel (e : Expression, f : Ident) : Expression => e "." f;
op cast (e : Expression) : Expression => "cast(" e ")";
op castAs (e : Expression) : Expression => "cast(as " e ")";
op len (e : Expression) : Expression => "#len(" e ")";
op hashCall (f : Ident, a : Expression) : Expression => "#" f "(" a ")";
op assign (lhs : Ident, rhs : Expression) : Command => lhs:0 " = " rhs ";";
op assignConst (lhs : Ident, rhs : Expression) : Command => lhs:0 " = const " rhs ";";
#end

-- After `=`, the parser reads the token `= const`: bare, `x = const;` would not parse, and
-- `x = constFoo(y);` would read as `x = const Foo(y);`.  So `const`, and every longer name that
-- starts with it, is quoted.  Names that contain `const` later (`fooconst`), are shorter (`con`), or
-- start with a later part of it (`stack`) are not.
/--
info: program KeywordRuns;
x = |const|;x = |constFoo|(y);x = const fooconst + con + stack;
-/
#guard_msgs in
#eval roundTrip (#strata
program KeywordRuns;
x = |const|;
x = |constFoo|(y);
x = const fooconst + con + stack;
#end).program

-- The same holds after the first word of a token that starts like an identifier: bare,
-- `cast(asked)` would read as `cast(as` and `ked)`.  A word that does not end its token, as `len`
-- in `#len(`, makes only that name unreadable: bare, `#len(y)` would read as the operation `len`,
-- but `#length(y)` reads as it should.
/--
info: program KeywordRuns;
x = cast(|asked|) + cast(as y) + #|len|(y) + #length(y) + #len(y);
-/
#guard_msgs in
#eval roundTrip (#strata
program KeywordRuns;
x = cast(|asked|) + cast(as y) + #|len|(y) + #length(y) + #len(y);
#end).program

-- The tokens of the Init dialect count too: bare, `"a".fields` would read as Init's token `.field`
-- and `s`.
/--
info: program KeywordRuns;
x = "a".|fields| + "a".y;
-/
#guard_msgs in
#eval roundTrip (#strata
program KeywordRuns;
x = "a".|fields| + "a".y;
#end).program

-- A name can also follow a letter or a digit: after a literal that ends with one, as `#a`, or
-- after a number.
#dialect
dialect KeywordAfterWord;
category Expression;
op var (name : Ident) : Expression => name;
op call (f : Ident, a : Expression) : Expression => f "(" a ")";
op add (a : Expression, b : Expression) : Expression => @[prec(10), leftassoc] a " + " b;
op assign (lhs : Ident, rhs : Expression) : Command => lhs:0 " = " rhs ";";
op ha (f : Ident, a : Expression) : Expression => "#a" f "(" a ")";
op hazap (a : Expression) : Expression => "#azap(" a ")";
op pazap (a : Expression) : Expression => "(#azap " a ")";
op hn (n : Num, f : Ident) : Expression => "#" n f;
op n12zip () : Expression => "#12zip";
category Tag;
op tagT () : Tag => "#t";
op tagged (t : Tag, f : Ident) : Expression => t f;
op tgo () : Expression => "#tgo";
category Mark;
op markM () : Mark => "#m";
op marks (ms : Option (CommaSepBy Mark)) : Expression => "[" ms "]";
op mok () : Expression => "#mok";
category Item;
op itemI () : Item => "#i";
op itemName (n : Ident) : Item => n;
op items (is : Seq Item) : Expression => "{" is "}";
op ino () : Expression => "#ino";
op stopC () : Command => "#c";
op block (c : Command) : Command => "{" c "}";
op cup () : Expression => "#cup";
category Opt;
op optP () : Opt => "#p";
op opted (o : Option Opt, f : Ident) : Expression => "<" o f ">";
op pxy () : Expression => "#pxy";
category Inner;
op innerW () : Inner => "#w";
category Outer;
op outerOf (x : Inner) : Outer => x;
op outerUse (o : Outer, f : Ident) : Expression => o f;
op wq () : Expression => "#wq";
category Key;
op keyK () : Key => "#k";
category Arg;
op keyed (k : Key) : Arg => "@" k;
op useArg (a : Arg, f : Ident) : Expression => a:0 f;
op kon () : Expression => "#kon";
type int;
fn fh () : int => "#f";
op useF (v : int, n : Ident) : Command => "use " v n ";";
op fzz () : Expression => "#fzz";
#end

-- Bare, `#azap(y)` would read as the operation `hazap`, `g(#azapper(y))` as `(#azap` and `per`,
-- and `#12zip` as the operation `n12zip`.  `zop` stays bare: no token covers it.
/--
info: program KeywordAfterWord;
x = #a|zap|(y) + #azop(y) + #azap(y) + g(#a|zapper|(y)) + #12|zip| + #12zip;
-/
#guard_msgs in
#eval roundTrip (#strata
program KeywordAfterWord;
x = #a|zap|(y) + #azop(y) + #azap(y) + g(#a|zapper|(y)) + #12|zip| + #12zip;
#end).program

-- A literal that ends its syntax definition counts when a name can follow its category: a name
-- follows a `Tag`, an `Item` in a `Seq`, an `Opt` through its option, an `Inner` through `outerOf`,
-- which prints as its argument, a command, even one that `block` encloses, and a function.  A
-- `Mark` is followed only by `,` and `]`, so `ok` stays bare.
/--
info: program KeywordAfterWord;
x = #t|go| + #tgo + [#m, #m] + ok + #mok + {#i|no|} + #ino + <#p|xy|> + #pxy + #w|q| + #wq;#c|up| = y;use #f|zz|;
-/
#guard_msgs in
#eval roundTrip (#strata
program KeywordAfterWord;
x = #t|go| + #tgo + [#m, #m] + ok + #mok + {#i|no|} + #ino + <#p|xy|> + #pxy + #w|q| + #wq;
#c
|up| = y;
use #f|zz|;
#end).program

-- A name may follow an argument that ends its syntax definition, as `Key` ends `keyed`: bare,
-- `@#kon` would read as `@` and the operation `kon`.
/--
info: program KeywordAfterWord;
x = @#k|on| + #kon;
-/
#guard_msgs in
#eval roundTrip (#strata
program KeywordAfterWord;
x = @#k|on| + #kon;
#end).program

-- The names of type variables and of the dialects' types are quoted the same way.
#dialect
dialect KeywordTypes;
type ret;

category TypeVar;
@[declareTVar(name)]
op typeVar (name : Ident) : TypeVar => name;
category TypeArgs;
@[scope(args)]
op typeArgs (args : CommaSepBy TypeVar) : TypeArgs => "<" args ">";

category Binding;
@[declare(name, tp)]
op mkBinding (name : Ident, tp : TypeP) : Binding => name ":" tp;
category Bindings;
@[scope(bindings)]
op mkBindings (bindings : CommaSepBy Binding) : Bindings => "(" bindings ")";

@[declareFn(name, b, r)]
op fdecl (name : Ident, typeArgs : Option TypeArgs, @[scope(typeArgs)] b : Bindings,
          @[scope(typeArgs)] r : Type) : Command =>
  "function " name typeArgs b " : " r ";";
@[declareType(name, some args)]
op typeFn (name : Ident, args : Option Bindings) : Command => "type_fn " name args ";";
@[declare(name, tp)]
op varDecl (name : Ident, tp : Type) : Command => "var " name " : " tp ";";
op retC (e : ret) : Command => "ret " e ";";
op poly (b : Bindings, @[scope(b)] r : Type) : Command => "poly " b " : " r ";";
#end

-- A type variable is quoted where it is used too: `function` because it is a token, and `a-b`
-- because of its characters.
/--
info: program KeywordTypes;
function identity<|function|>(x:|function|) : |function|;function k<|a-b|>(x:|a-b|) : |a-b|;
-/
#guard_msgs in
#eval roundTrip (#strata
program KeywordTypes;
function identity<|function|>(x : |function|) : |function|;
function k<|a-b|>(x : |a-b|) : |a-b|;
#end).program

-- `ret` is a token, so the dialect's type `ret` is quoted.  The category `Type` is not: the
-- parser reads it through the token `Type`.
/--
info: program KeywordTypes;
var x : |ret|;type_fn Box(a:Type);
-/
#guard_msgs in
#eval roundTrip (#strata
program KeywordTypes;
var x : |ret|;
type_fn Box(a : Type);
#end).program

-- Names in nested type positions are quoted too: a type applied to an argument, the two sides of
-- an arrow, a type that a binder binds, and type variables inside an arrow.
/--
info: program KeywordTypes;
type_fn |function|(a:Type);var y : |function| |ret|;var f : |ret| -> |ret|;poly (|var|:Type) : |var| -> |var|;function g<|function|, |var|>(x:(|function| -> |var|)) : |var|;
-/
#guard_msgs in
#eval roundTrip (#strata
program KeywordTypes;
type_fn |function|(a : Type);
var y : |function| |ret|;
var f : |ret| -> |ret|;
poly (|var| : Type) : |var| -> |var|;
function g<|function|, |var|>(x : |function| -> |var|) : |var|;
#end).program

-- A known limitation: the elaborator reads the type variable `|a.b|` as the qualified name of
-- type `b` in dialect `a`.
/--
error: Undeclared type or category a.b.
---
error: Undeclared type or category a.b.
-/
#guard_msgs in
example := #strata
program KeywordTypes;
function m<|a.b|>(x : |a.b|) : |a.b|;
#end

-- A dialect definition is read with StrataDDL's tokens, not with those of the dialects it
-- defines, so the option does not quote the names in it.
#dialect
dialect KeywordDecl;
type ret;
op retC (ret : ret) : Command => "ret " ret ";";
#end

/--
info: dialect KeywordDecl;
type ret;
op retC (ret : ret) : Command => "ret " ret:0 ";";
-/
#guard_msgs in
#eval (#strata
program KeywordDecl;
#end).program.ppDialect! (opts := { quoteKeywords := true })

end
