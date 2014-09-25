<TeXmacs|1.0.7.18>

<style|article>

<\body>
  <section|Data Structures and Concrete Syntax>

  We have the following nodes in the abstract syntax of patterns and
  expressions:

  <\description>
    <item*|<verbatim|p-Empty>><math|0:> Pattern that never matches. Concrete
    syntax: <verbatim|!>. Constructor: <verbatim|Zero>.

    <item*|<verbatim|p-Wild>><math|1:> Pattern that always matches. Concrete
    syntax: <verbatim|_>. Constructor: <verbatim|One>.

    <item*|<verbatim|p-And>><math|p<rsub|1>\<wedge\>p<rsub|2>>: Conjunctive
    pattern. Concrete syntax: e.g. <verbatim|p1 as p2>. Constructor:
    <verbatim|PAnd>.

    <item*|<verbatim|p-Var>><math|x:> Pattern variable. Concrete syntax:
    lower-case identifier e.g. <verbatim|x>. Constructor: <verbatim|PVar>.

    <item*|<verbatim|p-Cstr>><math|K p<rsub|1>\<ldots\> p<rsub|n>:>
    Constructor pattern. Concrete syntax: e.g. <verbatim|K (p1, p2)>.
    Constructor: <verbatim|PCons>.

    <item*|<verbatim|Var>><math|x:> Variable. Concrete syntax: lower-case
    identifier e.g. <verbatim|x>. Constructor: <verbatim|Var>. External
    functions are represented as variables in global environment.

    <item*|<verbatim|Cstr>><math|K e<rsub|1>\<ldots\> e<rsub|n>:> Constructor
    expression. Concrete syntax: e.g. <verbatim|K (e1, e2)>. Constructor:
    <verbatim|Cons>.

    <item*|<verbatim|App>><math|e<rsub|1> e<rsub|2>:> Application. Concrete
    syntax: e.g. <verbatim|x y>. Constructor: <verbatim|App>.

    <item*|<verbatim|LetRec>><math|<with|math-font-series|bold|letrec>
    x=e<rsub|1> <with|math-font-series|bold|in> e<rsub|2>:> Recursive
    definition. Concrete syntax: e.g. <verbatim|let rec f = function
    >...<verbatim| in >... Constructor: <verbatim|Letrec>.

    <item*|<verbatim|Abs>><math|\<lambda\><around|(|c<rsub|1>\<ldots\>c<rsub|n>|)>:>
    Function defined by cases. Concrete syntax: <verbatim|function
    >...<verbatim| \| >...; for single branching via <verbatim|fun> keyword,
    e.g. <verbatim|fun x y -\<gtr\> f x y> translates as
    <math|\<lambda\><around*|(|x.\<lambda\><around*|(|y.<around*|(|f x|)>
    y|)>|)>>; for multiple branching via <verbatim|match> keyword, e.g.
    <verbatim|match e with >... translates as
    <math|\<lambda\><around*|(|\<ldots\>|)> e>. Constructor: <verbatim|Lam>.

    <item*|<verbatim|Clause>><math|p.e:> Branch of pattern matching. Concrete
    syntax: e.g. <verbatim|p -\<gtr\> e>.

    <item*|<verbatim|ClauseWhen>><math|p<with|math-font-series|bold| when
    >\<wedge\><rsub|i>m<rsub|i>\<leqslant\>n<rsub|i>.e:> Branch of pattern
    matching with a condition. Concrete syntax: e.g. <verbatim|p when a
    \<less\>= b && c \<less\>= d -\<gtr\> e>.

    <item*|<verbatim|CstrIntro>>Does not figure in neither concrete nor
    abstract syntax. Scope of existential types is thought to retroactively
    cover the whole program.

    <item*|<verbatim|ExCases>><math|\<lambda\><around*|[|K|]><around|(|p<rsub|1>.e<rsub|1>\<ldots\>p<rsub|n>.e<rsub|n>|)>:>
    Function defined by cases and abstracting over the type of result.
    Concrete syntax: <verbatim|efunction> and <verbatim|ematch> keywords --
    e.g. <verbatim|efunction Nil -\<gtr\> >...<verbatim| \| Cons (x,xs)
    -\<gtr\> >...; <verbatim|ematch l with >... Parsing introduces a fresh
    identifier for <math|K>, but normalization keeps only one <math|K> for
    nested <verbatim|ExCases> (unless nesting in body of local definition or
    in argument of an application). Constructor: <verbatim|ExLam>.

    <item*|<verbatim|LetIn>, <verbatim|ExLetIn>><math|<with|math-font-series|bold|let>
    p=e<rsub|1> <with|math-font-series|bold|in> e<rsub|2>:> Elimination of
    existentially quantified type. \ Concrete syntax: e.g. <verbatim|let v =
    f e >...<verbatim| in >... Constructor: <verbatim|Letin>.

    <item*|<verbatim|AssertLeq>><math|<with|math-font-series|bold|assert num
    >m\<leqslant\>n;e>: add the inequality to the constraints. Concrete
    syntax: <verbatim|assert num m \<less\>= n; <math|\<ldots\>>>
    Constructor: <verbatim|AssertLeq>. There is a similar construct for
    adding an equation over types of expressions -- concrete syntax:
    <verbatim|assert type m = n; <math|\<ldots\>>> Constructor:
    <verbatim|AssertEqty>.
  </description>

  We also have one sort-specific type of expression, numerals.

  For type and formula connectives, we have ASCII and unicode syntactic
  variants (the difference is only in lexer). Quantified variables can be
  space or comma separated. Variables of various sorts have to start with
  specific letters: <verbatim|a>,<verbatim|b>,<verbatim|c>,<verbatim|r>,<verbatim|s>,<verbatim|t>,
  resp. <verbatim|i>,<verbatim|j>,<verbatim|k>,<verbatim|l>,<verbatim|m>,<verbatim|n>.
  Remaining letters are reserved for future sorts. The table below is
  analogous to information for expressions above. We pass variables
  environment <verbatim|gamma> as function parameters. We keep constructors
  environment <verbatim|sigma> as a global table. Existential type constructs
  introduce fresh identifiers <math|K>, we remember the identifiers in
  <verbatim|ex_types> but store the information in <verbatim|sigma>. Note
  that inferred existential types will not be nested, thanks to normalization
  of nested occurrences of <math|\<lambda\><around*|[|K|]>>. The abstract
  syntax of types is not sort-safe, but type variables carry sorts determined
  by first letter of the variable. In the future, sorts could be inferred
  after parsing. The syntax of types and formulas:

  <block|<tformat|<cwith|1|1|1|1|cell-halign|l>|<cwith|2|2|1|1|cell-halign|l>|<cwith|3|3|2|2|cell-halign|l>|<cwith|2|2|2|2|cell-halign|l>|<cwith|1|1|2|2|cell-halign|l>|<cwith|3|3|4|4|cell-col-span|2>|<cwith|2|2|4|4|cell-col-span|2>|<cwith|1|1|4|4|cell-col-span|2>|<cwith|1|1|4|4|cell-halign|r>|<cwith|2|2|4|4|cell-halign|r>|<cwith|3|3|4|4|cell-halign|r>|<table|<row|<cell|type
  variable: types>|<cell|<math|\<alpha\>,\<beta\>,\<gamma\>,\<tau\>>>|<cell|<verbatim|a>,<verbatim|b>,<verbatim|c>,<verbatim|r>,<verbatim|s>,<verbatim|t>,<verbatim|a1>,...>|<cell|<verbatim|TVar(VNam(Type_sort,>...<verbatim|))>>|<cell|>>|<row|<cell|type
  variable: nums>|<cell|<math|k,m,n>>|<cell|<verbatim|i>,<verbatim|j>,<verbatim|k>,<verbatim|l>,<verbatim|m>,<verbatim|n>,<verbatim|i1>,...>|<cell|<verbatim|TVar(VNam(Num_sort,>...<verbatim|))>>|<cell|>>|<row|<cell|type
  var. with coef.>|<cell|<math|<frac|1|3>n>>|<cell|<verbatim|1/3
  n>>|<cell|<small|<verbatim|Alien(Lin(1,3,VNam(Num_sort,"n")))>>>|<cell|>>|<row|<cell|type
  constructor>|<cell|<math|List>>|<cell|<verbatim|List>>|<cell|>|<cell|<verbatim|TCons(CNamed>...<verbatim|)>>>|<row|<cell|number
  (type)>|<cell|<math|7>>|<cell|<verbatim|7>>|<cell|>|<cell|<verbatim|Alien
  (Cst<math|\<ldots\>>)>>>|<row|<cell|numeral
  (expr.)>|<cell|<math|7>>|<cell|<verbatim|7>>|<cell|>|<cell|<verbatim|Num>>>|<row|<cell|numerical
  sum (type)>|<cell|<math|m+n>>|<cell|<verbatim|m+n>>|<cell|>|<cell|<verbatim|Alien
  (Add<math|\<ldots\>>)>>>|<row|<cell|existential
  type>|<cell|<math|\<exists\>k,n<around*|[|k\<leqslant\>n|]>.\<tau\>>>|<cell|<verbatim|ex
  k n [k\<less\>=n].t>>|<cell|<verbatim|<math|\<exists\>>k,n[k<math|\<leq\>>n].t>>|<cell|<verbatim|TCons(Extype>...<verbatim|)>>>|<row|<cell|type
  sort>|<cell|<math|s<rsub|ty>>>|<cell|<verbatim|type>>|<cell|>|<cell|<verbatim|Type_sort>>>|<row|<cell|number
  sort>|<cell|<math|s<rsub|R>>>|<cell|<verbatim|num>>|<cell|>|<cell|<verbatim|Num_sort>>>|<row|<cell|function
  type>|<cell|<math|\<tau\><rsub|1>\<rightarrow\>\<tau\><rsub|2>>>|<cell|<verbatim|t1
  -\<gtr\> t2>>|<cell|<verbatim|t1 <math|\<rightarrow\>><verbatim|
  t2>>>|<cell|<verbatim|Fun>>>|<row|<cell|equation>|<cell|<math|a<wide|=|\<dot\>>b>>|<cell|<verbatim|a
  = b>>|<cell|>|<cell|<verbatim|Eqty>>>|<row|<cell|inequation>|<cell|<math|k\<leqslant\>n>>|<cell|<verbatim|k
  \<less\>= n>>|<cell|<verbatim|k <math|\<leq\>>
  n>>|<cell|<verbatim|A(Num_atom(Leq<math|\<ldots\>>))>>>|<row|<cell|conjunction>|<cell|<math|\<varphi\><rsub|1>\<wedge\>\<varphi\><rsub|2>>>|<cell|<verbatim|a=b
  && b=a>>|<cell|<verbatim|a=b <math|\<wedge\>> b=a>>|<cell|built-in
  lists>>>>>

  For the syntax of expressions, we discourage non-ASCII symbols. Restating
  the first paragraph, below <math|e,e<rsub|i>> stand for any expression,
  <math|p,p<rsub|i>> stand for any pattern, <math|x> stands for any
  lower-case identifier and <math|K> for an upper-case identifier.

  <block|<tformat|<table|<row|<cell|named
  value>|<cell|<math|x>>|<cell|<verbatim|x> \ --lower-case
  identifier>|<cell|<verbatim|Var>>>|<row|<cell|numeral
  (expr.)>|<cell|<math|7>>|<cell|<verbatim|7>>|<cell|<verbatim|Num>>>|<row|<cell|constructor>|<cell|<math|K>>|<cell|<verbatim|K>
  \ --upper-case identifier>|<cell|<verbatim|Cons>>>|<row|<cell|application>|<cell|<math|e<rsub|1>
  e<rsub|2>>>|<cell|<verbatim|e1 e2>>|<cell|<verbatim|App>>>|<row|<cell|non-br.
  function>|<cell|<math|\<lambda\><around*|(|p<rsub|1>.\<lambda\><around*|(|p<rsub|2>.e|)>|)>>>|<cell|<verbatim|fun
  (p1,p2) p3 -\<gtr\> e>>|<cell|<verbatim|Lam(<math|\<ldots\>>)>>>|<row|<cell|branching
  function>|<cell|<math|\<lambda\><around*|(|p<rsub|1>.e<rsub|1>\<ldots\>p<rsub|n>.e<rsub|n>|)>>>|<cell|<verbatim|function
  p1-\<gtr\>e1 \| >...<verbatim| \| pn-\<gtr\>en>>|<cell|<verbatim|Lam(<math|\<ldots\>>)>>>|<row|<cell|cond.
  branch>|<cell|<math|\<lambda\><around*|(|p<rsub|1><with|math-font-series|bold|
  when >m\<leqslant\>n.e<rsub|1>\<ldots\>|)>>>|<cell|<verbatim|function p1
  when m\<less\>=n-\<gtr\>e1\|>...<verbatim|>>|<cell|<verbatim|Lam(<math|\<ldots\>>)>>>|<row|<cell|pattern
  match>|<cell|<math|\<lambda\><around*|(|p<rsub|1>.e<rsub|1>\<ldots\>p<rsub|n>.e<rsub|n>|)>
  e>>|<cell|<verbatim|match e with p1-\<gtr\>e1 \|
  >...>|<cell|<verbatim|App(Lam>...<verbatim|,e)>>>|<row|<cell|postcond.
  function>|<cell|<math|\<lambda\><around*|[|K|]><around*|(|p<rsub|1>.e<rsub|1>\<ldots\>p<rsub|n>.e<rsub|n>|)>>>|<cell|<verbatim|efunction
  p1-\<gtr\>e1 \| >...>|<cell|<verbatim|ExLam>>>|<row|<cell|postcond.
  match>|<cell|<math|\<lambda\><around*|[|K|]><around*|(|p<rsub|1>.e<rsub|1>\<ldots\>p<rsub|n>.e<rsub|n>|)>
  e>>|<cell|<verbatim|ematch e with p1-\<gtr\>e1 \|
  >...>|<cell|<verbatim|App(ExLam>...<verbatim|)>>>|<row|<cell|rec.
  definition>|<cell|<math|<with|math-font-series|bold|letrec> x=e<rsub|1>
  <with|math-font-series|bold|in> e<rsub|2>>>|<cell|<verbatim|let rec x = e1
  in e2>>|<cell|<verbatim|Letrec>>>|<row|<cell|definition>|<cell|<math|<with|math-font-series|bold|let>
  p=e<rsub|1> <with|math-font-series|bold|in> e<rsub|2>>>|<cell|<verbatim|let
  p1,p2 = e1 in e2>>|<cell|<verbatim|Letin>>>|<row|<cell|asserting dead
  br.>|<cell|<math|\<b-F\>>>|<cell|<verbatim|assert
  false>>|<cell|<verbatim|AssertFalse>>>|<row|<cell|assert equal
  types>|<cell|<math|<with|math-font-series|bold|assert type
  >e<rsub|1><wide|=|\<dot\>>e<rsub|2>;e<rsub|3>>>|<cell|<verbatim|assert type
  e1 = e2; e3>>|<cell|<verbatim|AssertEqty>>>|<row|<cell|assert
  inequality>|<cell|<math|<with|math-font-series|bold|assert num
  >e<rsub|1>\<leqslant\>e<rsub|2>;e<rsub|3>>>|<cell|<verbatim|assert num e1
  \<less\>= e2; e3>>|<cell|<verbatim|AssertLeq>>>>>>

  Parts of the logic hidden from the user:

  <block|<tformat|<table|<row|<cell|unary predicate
  variable>|<cell|<math|\<chi\><around*|(|\<beta\>|)>>>|<cell|<verbatim|PredVarU(chi,TVar
  "b",loc)>>>|<row|<cell|binary predicate
  variable>|<cell|<math|\<chi\><rsub|K><around*|(|\<gamma\>,\<alpha\>|)>>>|<cell|<verbatim|PredVarB(chi,TVar
  "g", TVar "a",loc)>>>|<row|<cell|not an existential
  type>|<cell|<math|<neg|E><around*|(|\<alpha\>|)>>>|<cell|<verbatim|NotEx(TVar
  "a",loc)>>>|<row|<cell|negation <verbatim|assert
  false>>|<cell|<math|\<b-F\>>>|<cell|<verbatim|CFalse loc>>>>>>

  Toplevel expressions (corresponding to structure items in OCaml) introduce
  types, type and value constructors, global variables with given type
  \ (external names) or inferred type (definitions).

  <block|<tformat|<cwith|1|1|2|2|cell-halign|l>|<cwith|1|1|1|1|cell-halign|l>|<table|<row|<cell|type
  constructor>|<cell|<verbatim|datatype List : type *
  num>>|<cell|<verbatim|TypConstr>>>|<row|<cell|value
  constructor>|<cell|<verbatim|datacons Cons : all n a. a *
  List(a,n)--\<gtr\>List(a,n+1)>>|<cell|<verbatim|ValConstr>>>|<row|<cell|>|<cell|<verbatim|datacons
  Cons : <math|\<forall\>>n,a. a * List(a,n) <math|\<longrightarrow\>>
  List(a,n+1)>>|<cell|>>|<row|<cell|declaration>|<cell|<verbatim|external
  filter : <math|\<forall\>>n,a.List(a,n)<math|\<rightarrow\>
  \<exists\>>k[k\<less\>=n].List(a,k)>>|<cell|<verbatim|PrimVal>>>|<row|<cell|let-declaration>|<cell|<verbatim|external
  let mult : Int<math|\<rightarrow\>>Int<math|\<rightarrow\>>Int = "( *
  )">>|<cell|<verbatim|PrimVal>>>|<row|<cell|rec.
  definition>|<cell|<verbatim|let rec f =>...>|<cell|<verbatim|LetRecVal>>>|<row|<cell|non-rec.
  definition>|<cell|<verbatim|let p1,p2 =>...>|<cell|<verbatim|LetVal>>>|<row|<cell|definition
  with test>|<cell|<verbatim|let rec f =>...<verbatim| test e1;
  >...<verbatim|; en>>|<cell|<verbatim|LetRecVal>>>>>>

  Tests list expressions of type <verbatim|Boolean> that at runtime have to
  evaluate to <verbatim|True>. Type inference is affected by the constraints
  generated to typecheck the expressions.

  For simplicity of theory and implementation, mutual non-nested recursion
  and or-patterns are not provided. For mutual recursion, nest one recursive
  definition inside another.

  At any place between lexemes, regular comments encapsulated in
  <verbatim|(*<math|\<ldots\>>*)> can occur. They are ignored during lexing.
  In front of all toplevel definitions and declarations, e.g. before a
  <verbatim|datatype>, <verbatim|datacons>, <verbatim|external>,
  <verbatim|let rec> or <verbatim|let>, and in front of <verbatim|let rec> ..
  <verbatim|in> and <verbatim|let> .. <verbatim|in> nodes in expressions,
  documentation comments <verbatim|(**<math|\<ldots\>>*)> can be put.
  Documentation comments at other places are syntax errors. Documentation
  comments are preserved both in generated interface files and in exported
  source code files. Documentation comments are the first parameters of
  corresponding constructors, and are of type <verbatim|string option>.

  <section|Generating and Normalizing Formulas>

  We inject the existential type and value constructors during parsing for
  user-provided existential types, and during constraint generation for
  inferred existential types, into the list of toplevel items. It faciliates
  exporting inference results as OCaml source code.

  Functions <verbatim|constr_gen_pat> and <verbatim|envfrag_gen_pat> compute
  formulas according to table <reference|IntermInfPat>, and
  <verbatim|constr_gen_expr> computes table <reference|IntermInf>. Due to the
  presentation of the type system, we ensure in <verbatim|ValConstr> that
  bounds on type parameters are introduced in the formula rather than being
  substituted into the result type. We preserve the FOL language presentation
  in the type <verbatim|cnstrnt>, only limiting the expressivity in ways not
  requiring any preprocessing. The toplevel definitions (from type
  <verbatim|struct_item>) <verbatim|LetRecVal> and <verbatim|LetVal> are
  processed by <verbatim|constr_gen_letrec> and <verbatim|constr_gen_let>.
  The constraints generated by <verbatim|constr_gen_letrec>, resp.
  <verbatim|constr_gen_let>, are analogous to those generated for
  <verbatim|Letrec>, resp. for <verbatim|Letin> or a <verbatim|Lam> clause.
  If the LHS pattern of <verbatim|LetVal> is just a name, e.g. <verbatim|let
  x = <math|\<ldots\>>>, then we call <verbatim|constr_gen_letrec>, telling
  it not to bind the name <verbatim|x>, and do the processing in the same way
  as for <verbatim|Letrec>.

  Toplevel definitions are intended as boundaries for constraint solving.
  This way the programmer can decompose functions that could be too complex
  for the solver. <verbatim|LetRecVal> only binds a single identifier, while
  <verbatim|LetVal> binds variables in a pattern. To preserve the flexibility
  of expression-level pattern matching, for <verbatim|LetVal> -- unless it
  just binds a value as discussed above -- we pack the constraints
  <math|<around*|\<llbracket\>|\<Sigma\>\<vdash\>p\<uparrow\>\<alpha\>|\<rrbracket\>>>
  which the pattern makes available, into existential types. Each pattern
  variable is a separate entry to the global environment, therefore the
  connection between them is lost.

  The <verbatim|Letin> syntax has two uses: binding values of existential
  types means ``eliminating the quantification'' -- the programmer has
  control over the scope of the existential constraint. The second use is if
  the value is not of existential type, the constraint is replaced by one
  that would be generated for a pattern matching branch. This recovers the
  common use of the <verbatim|let>...<verbatim|in> syntax, with exception of
  polymorphic <verbatim|let> cases, where <verbatim|let rec> needs to be
  used.

  The second argument of the predicate variable
  <math|\<chi\><rsub|K><around*|(|\<gamma\>,\<alpha\>|)>\<nosymbol\>>
  provides an ``escape route'' for free variables, i.e. precondition
  variables used in postcondition. In the implementation, we have
  user-defined existential types with explicit constraints in addition to
  inferred existential types. We expand the inferred existential types after
  they are solved into the fuller format. In the inferred form, the result
  type has a single parameter <math|\<delta\><rprime|'>>, without loss of
  generality because the actual parameters are passed as a tuple type. In the
  full format we recover after inference, we extract the parameters
  <math|\<delta\><rprime|'><wide|=|\<dot\>><around*|(|<wide|\<beta\>|\<bar\>>|)>>,
  the non-local variables of the existential type, and the partially abstract
  type <math|\<delta\><wide|=|\<dot\>>\<tau\>>, and store them separately,
  i.e. <math|\<varepsilon\><rsub|K><around*|(|<wide|\<beta\>|\<bar\>>|)>=\<forall\><wide|\<beta\>|\<bar\>>\<exists\><wide|\<alpha\>|\<bar\>><around*|[|D|]>.\<tau\>>.
  The variables <math|<wide|\<beta\>|\<bar\>>> are instantiated whenever the
  constructor is used. For <verbatim|LetVal>, we form existential types after
  solving the generated constraint, to have less intermediate variables in
  them.

  Both during parsing and during inference, we inject new structure items to
  the program, which capture the existential types. In parsing, they arise
  only for <verbatim|ValConstr> and <verbatim|PrimVal> and are added by
  <verbatim|Praser>. The inference happens only for <verbatim|LetRecVal> and
  <verbatim|LetVal> and injection is performed in <verbatim|Infer>. During
  printing existential types in concrete syntax
  <math|\<exists\>i:<wide|\<beta\>|\<bar\>><around*|[|\<varphi\>|]>.t> for an
  occurrence <math|\<varepsilon\><rsub|K><around*|(|<around*|(|<wide|r|\<bar\>>|)>|)>>,
  the variables <math|<wide|\<alpha\>|\<bar\>>> coming from
  <math|\<delta\><rprime|'><wide|=|\<dot\>><around*|(|<wide|\<alpha\>|\<bar\>>|)>\<in\>\<varphi\>>
  are substituted-out by <math|<around*|[|<wide|\<alpha\>|\<bar\>>\<assign\><wide|r|\<bar\>>|]>>.

  For simplicity, only toplevel definitions accept type and invariant
  annotations from the user. The constraints are modified according to the
  <math|<around*|\<llbracket\>|\<Gamma\>,\<Sigma\>\<vdash\>ce:\<forall\><wide|\<alpha\>|\<bar\>><around|[|D|]>.\<tau\>|\<rrbracket\>>>
  rule. Where <verbatim|Letrec> uses a fresh variable <math|\<beta\>>,
  <verbatim|LetRecVal> incorporates the type from the annotation. The
  annotation is considered partial, <math|D> becomes part of the constraint
  generated for the recursive function but more constraints will be added if
  needed. The polymorphism of <math|\<forall\><wide|\<alpha\>|\<bar\>>>
  variables from the annotation is preserved since they are universally
  quantified in the generated constraint.

  The constraints solver returns three components: the <em|residue>, which
  implies the constraint when the predicate variables are instantiated, and
  the solutions to unary and binary predicate variables. The residue and the
  predicate variable solutions are separated into <em|solved variables> part,
  which is a substitution, and remaining constraints (which are currently
  limited to linear inequalities). To get a predicate variable solution we
  look for the predicate variable identifier association and apply it to one
  or two type variable identifiers, which will instantiate the parameters of
  the predicate variable. We considered several ways to deal with multiple
  solutions:

  <\enumerate>
    <item>report a failure to the user;

    <item>ask the user for decision;

    <item>silently pick one solution, if the wrong one is picked the
    subsequent program might fail;

    <item>perform backtracking search for the first solution that satisfies
    the subsequent program.
  </enumerate>

  We use approach 3 as it is simplest to implement. Traditional type
  inference workflow rules out approach 2, approach 4 is computationally too
  expensive. We might use approach 1 in a future version of the system. Upon
  ``multiple solutions'' failure -- or currently, when a wrong type or
  invariant is picked -- the user can add <verbatim|assert> clauses (e.g.
  <verbatim|assert false> stating that a program branch is impossible), and
  <verbatim|test> clauses. The <verbatim|test> clauses are boolean
  expressions with operational semantics of run-time tests: the test clauses
  are executed right after the definition is executed, and run-time error is
  reported when a clause returns <verbatim|false>. The constraints from test
  clauses are included in the constraint for the toplevel definition, thus
  propagate more efficiently than backtracking would. The <verbatim|assert>
  clauses are: <verbatim|assert type e1 = e2> which translates as equality of
  types of <verbatim|e1> and <verbatim|e2>, <verbatim|assert false> which
  translates as <verbatim|CFalse>, and <verbatim|assert num e1 \<less\>= e2>,
  which translates as inequality <math|n<rsub|1>\<leqslant\>n<rsub|2>>
  assuming that <verbatim|e1> has type <verbatim|Num n1> and <verbatim|e2>
  has type <verbatim|Num n2>.

  We treat a chain of single branch functions with only <verbatim|assert
  false> in the body of the last function specially. We put all information
  about the type of the functions in the premise of the generated constraint.
  Therefore the user can use them to exclude unintended types. See the
  example <verbatim|equal_assert.gadt>.

  <subsection|Normalization>

  We reduce the constraint to alternation-minimizing prenex-normal form, as
  in the formalization. We explored the option to preserve the scope
  relations, but it was less suited for determining quantifier violations. We
  return a <verbatim|var_scope>-producing variable comparison function. The
  branches we return from normalization have unified conclusions, since we
  need to unify for solving disjunctions anyway.

  Releasing constraints \ from under <verbatim|Or> is done iteratively,
  somewhat similar to how disjunction would be treated in constraint solvers.
  Releasing the sub-constraints is essential for eliminating cases of further
  <verbatim|Or> constraints. When at the end more than one disjunct remains,
  we assume it is the traditional <verbatim|LetIn> rule and select its
  disjunct (the first one in the implementation).

  When one <math|\<lambda\><around*|[|K|]>> expression is a branch of another
  <math|\<lambda\><around*|[|K|]>> expression, the corresponding branch does
  not introduce an <verbatim|Or> constraint -- the case is settled
  syntactically to be the same existential type.

  <subsubsection|Implementation details>

  The unsolved constraints are particularly weak with regard to variables
  constrained by predicate variables. We need to propagate which existential
  type to select for result type of recursive functions, if any. The
  information is collected from implication branches by
  <verbatim|simplify_brs> in <verbatim|normalize>; it is used by
  <verbatim|check_chi_exty>. <verbatim|normalize> starts by flattening
  constraints into implications with conjunctions of atoms as premises and
  conclusions, and disjunctions with disjuncts and additional information.
  <verbatim|flat_dsj> is used to flatten each disjunct in a disjunction, the
  additional information kept is <verbatim|guard_cnj>, conjunction of atoms
  that hold together with the disjunction. <verbatim|solve_dsj> takes the
  result of <verbatim|flat_dsj> and tries to eliminate disjuncts. If only one
  disjunct is left, or we decide to pick <verbatim|LetIn> anyway
  (<verbatim|step\<gtr\>0>), we return the disjunct. Otherwise we return the
  filtered disjunction. <verbatim|prepare_brs> cleans up the initial
  flattened constraints or the constraints released from disjunctions: it
  calls <verbatim|simplify_brs> on implications and <verbatim|flat_dsj> on
  each disjunction.

  We collect information about existential return types of recursive
  definitions in <verbatim|simplify_brs>:

  <\enumerate>
    <item>solving the conclusion of a branch together with additional
    conclusions <verbatim|guard_cnj>, to know the return types of variables,

    <item>registering existential return types for all variables in the
    substitution,

    <item>traversing the premise and conclusion to find new variables that
    are types of recursive definitions,

    <item>registering as ``type of recursive definition'' the return types
    for all variables in the substitution registered as types of recursive
    definitions,

    <item>traversing all variables known to be types of recursive
    definitions, and registering existential type with recursive definition
    (i.e. unary predicate variable) if it has been learned,

    <item>traversing all variables known to be types of recursive definitions
    again, and registering existential type of the recursive definition (if
    any) with the variable.
  </enumerate>

  <subsection|Simplification>

  During normalization, we remove from a nested premise the atoms it is
  conjoined with (as in ``modus ponens'').

  After normalization, we simplify the constraints by removing redundant
  atoms. We remove atoms that bind variables not occurring anywhere else in
  the constraint, and in case of atoms not in premises, not universally
  quantified. The simplification step is not currently proven correct and
  might need refining. We merge implications with the same premise, unless
  one of them is non-recursive and the other is recursive. We call an
  implication branch recursive when an unary predicate variable
  <math|\<chi\>> (not a <math|\<chi\><rsub|K>>) appears in the conclusion
  <em|or> a binary predicate variable <math|\<chi\><rsub|K>> appears in the
  premise.

  <section|Abduction>

  Our formal specification of abduction provides a scheme for combining sorts
  that substitutes number sort subterms from type sort terms with variables,
  so that a single-sort term abduction algorithm can be called. Since we
  implement term abduction over the two-sorted datatype <verbatim|typ>, we
  keep these <em|alien subterms> in terms passed to term abduction.

  <subsection|Simple constraint abduction for terms>

  Our initial implementation of simple constraint abduction for terms follows
  <cite|AbductionSolvMaher> p. 13. The mentioned algorithm only gives
  <em|fully maximal answers> which is loss of generality w.r.t. our
  requirements. To solve <math|D\<Rightarrow\>C> the algorithm starts with
  <math|\<b-U\><around*|(|D\<wedge\>C|)>> and iteratively replaces subterms
  by fresh variables <math|\<alpha\>\<in\><wide|\<alpha\>|\<bar\>>> for a
  final solution <math|\<exists\><wide|\<alpha\>|\<bar\>>.A>. As our primary
  approach to mitigate some of the limitations of fully maximal answers, we
  start from <math|\<b-U\><rsub|><around*|(|<wide|A|~><around*|(|D\<wedge\>C|)>|)>>,
  where <math|\<exists\><wide|\<alpha\>|\<bar\>>.A> is the solution to
  previous problems solved by the joint abduction algorithm, and
  <math|<wide|A|~><around*|(|\<cdummy\>|)>> is the corresponding
  substitution. Moreover, motivated by examples from Chuan-kai Lin
  <cite|PracticalGADTsInfer>, we intruduce variable-variable equations
  <math|\<beta\><rsub|1><wide|=|\<dot\>>\<beta\><rsub|2>>, for
  <math|\<beta\><rsub|1>\<beta\><rsub|2>\<subset\><wide|\<beta\>|\<bar\>>>,
  not implied by <math|<wide|A|~><around*|(|D\<wedge\>C|)>>, as additional
  candidate answer atoms. During abduction
  <math|Abd<around*|(|\<cal-Q\>,<wide|\<beta\>|\<bar\>>,<wide|D<rsub|i>,C<rsub|i>|\<bar\>>|)>>,
  we ensure that the (partial as well as final) answer
  <math|\<exists\><wide|\<alpha\>|\<bar\>>.A> satisfies
  <math|\<vDash\>\<cal-Q\>.A<around*|[|<wide|\<alpha\>|\<bar\>><wide|\<beta\>|\<bar\>>\<assign\><wide|t|\<bar\>>|]>>
  for some <math|<wide|t|\<bar\>>>. We achieve this by normalizing the answer
  using parameterized unification under quantifiers
  <math|\<b-U\><rsub|<wide|\<alpha\>|\<bar\>><wide|\<beta\>|\<bar\>>><around*|(|\<cal-Q\>.A|)>>.
  <math|<wide|\<beta\>|\<bar\>>> are the parameters of the invariants.

  In fact, when performing unification, we check more than
  <math|\<b-U\><rsub|<wide|\<alpha\>|\<bar\>><wide|\<beta\>|\<bar\>>><around*|(|\<cal-Q\>.A|)>>
  requires. We also ensure that the use of parameters will not cause problems
  in the <verbatim|split> phase of the main algorithm. To this effect, we
  forbid substitution of a variable <math|\<beta\><rsub|1>> from
  <math|<wide|\<beta\>|\<bar\>>> with a term containing a universally
  quantified variable that is not in <math|<wide|\<beta\>|\<bar\>>> and to
  the right of <math|\<beta\><rsub|1>> in <math|\<cal-Q\>>.

  In implementing <cite|AbductionSolvMaher> p. 13, we follow a top-down
  approach where bigger subterms are abstracted first -- replaced by a fresh
  variable, \ together with an arbitrary selection of other occurrences of
  the subterm. If dropping the candidate atom maintains
  <math|T<around*|(|F|)>\<vDash\>A\<wedge\>D\<Rightarrow\>C>, we proceed to
  neighboring subterm or next equation. Otherwise, we try all of: replacing
  the subterm by the fresh variable; proceeding to subterms of the subterm;
  preserving the subterm; replacing the subterm by variables corresponding to
  earlier occurrences of the subterm. This results in a single, branching
  pass over all subterms considered. Finally, we clean-up the solution by
  eliminating fresh variables when possible (i.e. substituting-out equations
  <math|x<wide|=|\<dot\>>\<alpha\>> for variable <math|x> and fresh variable
  <math|\<alpha\>>).

  Although there could be an infinite number of abduction answers, there is
  always a finite number of <em|fully maximal> answers, or more generally, a
  finite number of equivalence classes of formulas strictly stronger than a
  given conjunction of equations in the domain <math|T<around*|(|F|)>>. We
  use a search scheme that tests as soon as possible. The simple abduction
  algorithm takes a partial solution -- a conjunction of candidate solutions
  for some other branches -- and checks if the solution being generated is
  satisfiable together with the candidate partial solution. The algorithm
  also takes several indicators to let it select the expected answer:

  <\itemize>
    <item>a number that determines how many correct solutions to skip;

    <item>a validation procedure that checks whether the partial answer meets
    a condition, in joint abduction the condition is consistency with premise
    and conclusion of each branch;

    <item>the parameters and candidates for parameters of the invariants,
    <math|<wide|\<beta\>|\<bar\>>>, updated as we add new atoms to the
    partial answer; existential variables that are not to the left of
    parameters and are connected to parameters become parameters; we process
    atoms containing parameters first;

    <item>the quantifier <math|\<cal-Q\>> (source <verbatim|q>) so that the
    partial answer <math|\<exists\><wide|\<alpha\>|\<bar\>>.A> (source
    <verbatim|vs,ans>) can be checked for validity with parameters:
    <math|\<vDash\>\<cal-Q\>.A<around*|[|<wide|\<alpha\>|\<bar\>>\<assign\><wide|t|\<bar\>>|]>>
    for some <math|<wide|t|\<bar\>>>;

    <item>a discard list of partial answers to avoid (a tabu list) --
    implements backtracking, with answers from abductions raising
    ``fallback'' going there.
  </itemize>

  Since an atom can be mistakenly discarded when some variable could be
  considered an invariant parameter but is not at the time, we process atoms
  incident with candidates for invariant parameters first. A variable becomes
  a candidate for a parameter if there is a parameter that depends on it.
  That is, we process atoms <math|x<wide|=|\<dot\>>t> such that
  <math|x\<in\><wide|\<beta\>|\<bar\>>> first, and if equation
  <math|x<wide|=|\<dot\>>t> is added to the partial solution, we add to
  <math|<wide|\<beta\>|\<bar\>>> existential variables in <math|t>. Note that
  <math|x<wide|=|\<dot\>>t> can stand for either <math|x\<assign\>t>, or
  <math|y\<assign\>x> for <math|t=y>.

  To simplify the search in presence of a quantifier, we preprocess the
  initial candidate by eliminating universally quantified variables:

  <\eqnarray*>
    <tformat|<table|<row|<cell|Rev<rsub|\<forall\>><around*|(|\<cal-Q\>,<wide|\<beta\>|\<bar\>>,D,C|)>>|<cell|=>|<cell|<around*|{|S<around*|(|c|)><mid|\|>c\<in\>C,S=<around*|[|<wide|t<rsub|u>|\<bar\>>\<assign\><wide|t<rprime|'><rsub|u>|\<bar\>>|]><with|mode|text|
    for >FV<around*|(|t<rsub|u>|)>\<cap\><wide|\<beta\><rsub|u>|\<bar\>>\<neq\>\<varnothing\>,<wide|\<forall\>\<beta\><rsub|u>|\<bar\>>\<subset\>\<cal-Q\>,\<cal-M\>\<vDash\>D\<Rightarrow\><wide|S|\<dot\>>,<next-line><with|mode|text|
    \ \ \ \ \ \ \ >\<cal-M\>\<vDash\>\<cal-Q\>.S<around*|(|c|)><around*|[|<wide|\<beta\>|\<bar\>>\<assign\><wide|t|\<bar\>>|]><with|mode|text|
    for some ><wide|t|\<bar\>>|}>>>>>
  </eqnarray*>

  Note that <math|S> above is a substitution of subterms rather than of
  variables. To move further beyond fully maximal answers, we incorporate
  candidates <math|\<beta\><rsub|1><wide|=|\<dot\>>\<beta\><rsub|2>> for
  which the following conditions hold: <math|\<beta\><rsub|1>\<beta\><rsub|2>\<subset\><wide|\<beta\>|\<bar\>>>,
  <math|\<beta\><rsub|1>\<assign\>t<rsub|1>\<in\>\<b-U\><rsub|><around*|(|<wide|A|~><around*|(|D\<wedge\>C|)>|)>>,
  <math|\<beta\><rsub|2>\<assign\>t<rsub|2>\<in\>\<b-U\><rsub|><around*|(|<wide|A|~><around*|(|D\<wedge\>C|)>|)>>
  and <math|t<rsub|1><wide|=|\<dot\>>t<rsub|2>> is satisfiable. We also need
  to include the unifier of <math|t<rsub|1><wide|=|\<dot\>>t<rsub|2>> among
  the candidates, since otherwise the equation
  <math|\<beta\><rsub|1><wide|=|\<dot\>>\<beta\><rsub|2>> would not suffice
  to imply that of the atoms <math|\<beta\><rsub|1><wide|=|\<dot\>>t<rsub|1>>,
  <math|\<beta\><rsub|2><wide|=|\<dot\>>t<rsub|2>> which belongs to the
  conclusion <math|C>. The <em|full candidates>
  <math|\<b-U\><rsub|><around*|(|<wide|A|~><around*|(|D\<wedge\>C|)>|)>> and
  the <em|guess candidates> <math|<wide|\<beta\><rsub|1>\<assign\>\<beta\><rsub|2>;\<b-U\><around*|(|t<rsub|1><wide|=|\<dot\>>t<rsub|2>|)>|\<bar\>>>
  are kept apart, the guess candidates are guessed before the full
  candidates. By default, we additionally limit consideration to atoms
  <math|\<beta\><rsub|1><wide|=|\<dot\>>t<rsub|1>>,
  <math|\<beta\><rsub|2><wide|=|\<dot\>>t<rsub|2>> where
  <math|t<rsub|1>,t<rsub|2>> are not themselves variables.

  To recapitulate, the implementation is:

  <\itemize>
    <item><verbatim|abstract> is the entry point.

    <item>If <verbatim|guess_cand=[]> and <verbatim|full_cand=[]> -- no more
    candidates to add to the partial solution: check for repeated answers,
    skipping, and discarded answers.

    <item>If <verbatim|guess_cand=[]>, pick the next <verbatim|full_cand>
    atom <math|FV<around*|(|c|)>\<cap\><wide|\<beta\>|\<bar\>>\<neq\>\<varnothing\>>
    if any, reordering the candidates until one is found. Otherwise, pick the
    first <verbatim|guess_cand> atom without reordering.

    <item><verbatim|step> works through a single atom of the form <math|x=t>.

    <item>The <verbatim|abstract>/<verbatim|step> choices are:

    <\enumerate>
      <item>Try to drop the atom (if the partial answer + remaining
      candidates can still be completed to a correct answer).

      <item>Replace the current subterm of the atom with a fresh parameter,
      adding the subterm to replacements; if at the root of the atom, check
      connected and validate before proceeding to remaining candidates.

      <item>Step into subterms of the current subterm, if any, and if at the
      sort of types.

      <item>Keep the current part of the atom unchanged; if at the root of
      the atom, check connected and validate before proceeding to remaining
      candidates.

      <item>Replace the current subterm with a parameter introduced for an
      earlier occurrence; branch over all matching parameters; if at the root
      of the atom, check connected and validate before proceeding to
      remaining candidates.

      <item>Keep a variant of the original atom, but with constants
      substituted-out by variable-constant equations from the premise.
      Redundant, and optional: only when <verbatim|revert_cst> is true and
      <verbatim|more_general> is false.
    </enumerate>

    <item>Choices 2-6 are guarded by <verbatim|try>-<verbatim|with>, as tests
    raise <verbatim|Contradiction> if they fail, choice 1 only tests
    <verbatim|implies_concl> which returns a boolean.

    <item>Default ordering of choices is 1, 6, 2, 4, 3, 5 -- pushing 4 up
    minimizes the amount of branching in 5.

    <\itemize>
      <item>There is an option <verbatim|more_general>, which reorders the
      choices to: 1, 6, 4, 2, 3, 5; however the option is not exposed in the
      interface because the cost of this reordering is prohibitive.

      <item>An option <verbatim|richer_answers> reorders the choices to: 6,
      1, 2, 4, 3, 5; it does not increase computational cost but sometimes
      leads to answers that are not most general.

      <item>If choice 6 would lead to more negative constraints contradicted
      than choice 1, we pick choice 6 first for a particular candidate atom.
    </itemize>

    <item>Form initial candidates <math|Rev<rsub|\<forall\>><around*|(|\<cal-Q\>,<wide|\<beta\>|\<bar\>>,\<b-U\><around*|(|D\<wedge\>A<rsub|p>|)>,\<b-U\><around*|(|A<rsub|p>\<wedge\>D\<wedge\>C|)>|)>>.

    <item>Form the substitution of subterms for choice-6 counterparts of
    initial candidate atoms. For <math|\<alpha\><rsub|1><wide|=|\<dot\>>\<tau\>,\<ldots\>,\<alpha\><rsub|n><wide|=|\<dot\>>\<tau\>\<in\>\<b-U\><around*|(|D\<wedge\>A<rsub|p>|)>>,
    form the substitution of subterms <math|\<alpha\><rsub|1>\<assign\>\<alpha\><rsub|i>,\<ldots\>,\<alpha\><rsub|n>\<assign\>\<alpha\><rsub|i>,\<tau\>\<assign\>\<alpha\><rsub|i>>
    (excluding <math|\<alpha\><rsub|i>\<assign\>\<alpha\><rsub|i>>) where
    <math|\<alpha\><rsub|i>> is the most upstream existential variable (or
    parameter) and <math|\<tau\>> is a constant.

    <\itemize>
      <item>Since for efficiency reasons we do not always remove alien
      subterms, we need to mitigate the problem of alien subterm variables
      causing violation of the quantifier prefix. To this effect, we include
      the premise equations from other sorts in the process generating the
      initial candidates and choice 6 candidates, but not as candidates. Not
      to lose generality of answer, we only keep a renaming substitution, in
      particular we try to eliminate universal variables.
    </itemize>

    <item>Sort the initial candidates by decreasing size, because shorter
    answer atoms are more valuable and dropping a candidate from
    participating in an answer is the first choice.

    <\itemize>
      <item>There is an argument in favor of sorting by increasing size: so
      that the replacements of step 2 are formed at a root position before
      they are used in step 5 -- instead of forming a replacement at a
      subterm, and using it in step 5 at a root.

      <item>If ordering in increasing size turns out to be necessary, a
      workaround should be introduced to favor answers that, if possible, do
      not have parameters <math|<wide|\<beta\>|\<bar\>>> as left-hand-sides.
    </itemize>
  </itemize>

  The above ordering of choices ensures that more general answers are tried
  first. Moreover:

  <\itemize>
    <item>choice 1 could be dropped as it is equivalent to choice 2 applied
    on the root term;

    <item>choices 4 and 5 could be reordered but having choice 4 as soon as
    possible is important for efficiency.
  </itemize>

  We perform a two-layer iterative deepening when <verbatim|more_general> is
  false: in the first run we only try choices 1 and 6. It is an imperfect
  optimization since the running time gets longer whenever choices 2-5 are
  needed.

  <subsubsection|Heuristic for better answers to invariants>

  We implement an optional heuristic in forming the candidates proposed by
  choice 6. It may lead to better invariants when multiple maximally general
  types are possible, but also it may lead to getting the most general type
  without the need for backtracking across iterations of the main algorithm,
  which unfortunately often takes prohibitively long.

  We look at the types of substitutions for the invariant-holding variables
  <verbatim|bvs> in partial answer <verbatim|ans>, and try to form the
  initial candidates for choice 6 so that the return type variables cover the
  most of argument types variables, for each <verbatim|bvs> type found. We
  select from the candidates equations between any variable (case
  <verbatim|sb>) or only non-argument-type variable (case <verbatim|b_sb>),
  and a <math|FV<around*|(|<with|mode|text|argument
  types>|)>\\FV<around*|(|<with|mode|text|return type>|)>> variable -- we
  turn the equation so that the latter is the RHS. We locate the equations
  among the candidates that have a <verbatim|bvs> variable or a
  <math|FV<around*|(|<with|mode|text|return
  type>|)>\\FV<around*|(|<with|mode|text|argument types>|)>> variable as LHS.
  We apply the substitution <verbatim|sb> (or <verbatim|b_sb>) to the RHS of
  these equations (<verbatim|b_sb> if the LHS is in <verbatim|bvs>). We
  preserve the order of equations in the candidate list.

  <subsection|Joint constraint abduction>

  We further lose generality by using a heuristic search scheme instead of
  testing all combinations of simple abduction answers. In particular, our
  search scheme returns from joint abduction for types with a single answer,
  which eliminates deeper interaction between the sort of types and other
  sorts. Some amount of interaction is provided by the validation procedure,
  which checks for consistency of the partial answer, the premise and the
  conclusion of each branch, including consistency for other sorts.

  We accumulate simple abduction answers into the partial abduction answer,
  we set aside branches that do not have any answer satisfiable with the
  partial answer so far. After all branches have been tried and the partial
  answer is not an empty conjunction (i.e. not <math|\<top\>>), we retry the
  set-aside branches. If during the retry, any of the set-aside branches
  fails, we add the partial answer to discarded answers -- which are avoided
  during simple abduction -- and restart. Restart puts the set-aside branches
  to be tried first. If, when left with set-aside branches only, the partial
  answer is an empty conjunction, i.e. all the answer-contributing branches
  have been set aside, we fail -- return <math|\<bot\>> from the joint
  abduction. This does not peform complete backtracking (no completeness
  guarantee), but is therefore quicker to report unsolvable cases and does
  sufficient backtracking. After an answer working for all branches has been
  found, we perform additional check, which encapsulates negative constraints
  introduced by the <verbatim|assert false> construct. If the check fails, we
  add the answer to discarded answers and repeat the search.

  If a partial answer becomes as strong as one of the discarded answers
  inside SCA, simple constraint abduction skips to find a different answer.
  The discarded answers are initialized with a discard list passed from the
  main algorithm.

  To check validity of answers, we use a modified variant of unification
  under quantifiers: unification with parameters, where the parameters do not
  interact with the quantifiers and thus can be freely used and eliminated.
  Note that to compute conjunction of the candidate answer with a premise,
  unification does not check for validity under quantifiers.

  Because it would be difficult to track other sort constraints while
  updating the partial answer, we discard numeric sort constraints in simple
  abduction algorithm, and recover them after the final answer for terms
  (i.e. for the type sort) is found.

  Searching for abduction answer can fail in only one way: we have set aside
  all the branches that could contribute to the answer. It is difficult to
  pin-point the culprit. We remember which branch caused the restart when the
  number of set-aside branches was the smallest. We raise exception
  <verbatim|Suspect> that contains the conclusion of that branch.

  The core algorithm shared across sorts is provided in the <verbatim|Joint>
  module.

  <subsection|Abduction for terms with Alien Subterms><label|AlienSubterms>

  The JCAQPAS problem is more complex than simply substituting alien subterms
  with variables and performing joint constraint abduction on resulting
  implications. The ability to ``outsource'' constraints to the alien sorts
  enables more general answers to the target sort, in our case the term
  algebra <math|T<around*|(|F|)>>. Term abduction will offer answers that
  cannot be extended to multisort answers.

  One might mitigate the problem by preserving the joint abduction for terms
  algorithm, and after a solution <math|\<exists\><wide|\<alpha\>|\<bar\>>.A>
  is found, ``<em|dissociating>'' the alien subterms (including variables) in
  <math|A> as follows. We replace every alien subterm <math|n<rsub|s>> in
  <math|A> (including variables, even parameters) with a fresh variable
  <math|\<alpha\><rsub|s>>, which results in <math|A<rprime|'>> (in
  particular <math|A<rprime|'><around*|[|<wide|\<alpha\><rsub|s>|\<bar\>>\<assign\><wide|n<rsub|s>|\<bar\>>|]>=A>).
  Subsets <math|A<rsup|i><rsub|p>\<wedge\>A<rsup|i><rsub|c>=A<rsup|i>\<subset\><wide|\<alpha\><rsub|s><wide|=|\<dot\>>n<rsub|s>|\<bar\>>>
  such that <math|\<exists\><wide|\<alpha\>|\<bar\>><wide|\<alpha\><rsub|s>|\<bar\>>.A<rprime|'>,<wide|A<rsup|i><rsub|p>,A<rsup|i><rsub|c>|\<bar\>>>
  is a JCAQPAS answer will be recovered automatically by a residuum-finding
  process at the end of <verbatim|ans_typ>. [FIXME: this approach might not
  work.] This process is needed regardless of the ``dissociation'' issue, to
  uncover the full content of numeric sort constraints.

  To face efficiency of numerical abduction with many variables, we modify
  the approach. On the first iteration of the main algorithm, we remove alien
  subterms both from the branches and from the answer (the <verbatim|purge>
  function), but we do not perform other-sort abduction at all. On the next
  iteration, we do not purge alien subterms, neither from the branches nor
  from the answer, as we expect the dissociation in the partial answers (to
  predicate variables) from the first step to be sufficient. Other-sort
  abduction algorithms now have less work, because only a fraction of alien
  subterm variables <math|\<alpha\><rsub|s>> remain in the partial answers
  (see main algorithm in section <reference|MainAlgo>). They also have more
  information to work with, present in the instatiation of partial answers.
  However, this optimization violates completeness guarantees of the
  combination of sorts algorithm. To faciliate finding term abduction
  solutions that hold under the quantifiers, we substitute-out other sort
  variables, by variables more to the left in the quantifier, using equations
  from the premise.

  The dissociation interacts with the discard list mechanism. Since
  dissociation introduces fresh variables, no answers with alien subterms
  would be syntactically identical. When checking whether a partial answer
  should be discarded, in case alien subterm dissociation is <em|on>, we
  ignore alien sort subterms in the comparison.

  <subsection|Simple constraint abduction for linear
  arithmetics><label|SCAlinear>

  For checking validity or satisfiability, we use <em|Fourier-Motzkin
  elimination>. To avoid complexities we only handle the rational number
  domain. To extend the algorithm to integers, <em|Omega-test> procedure as
  presented in <cite|ArithQuantElim> needs to be adapted. The major
  operations are:

  <\itemize>
    <item><em|Elimination> of a variable takes an equation and selects a
    variable that is not upstream, i.e. to the left in <math|\<cal-Q\>>
    regarding alternations, of any other variable of the equation, and
    substitutes-out this variable from the rest of the constraint. The solved
    form contains an equation for this variable.

    <item><em|Projection> of a variable takes a variable <math|x> that is not
    upstream of any other variable in the unsolved part of the constraint,
    and reduces all inequalities containing <math|x> to the form
    <math|x<wide|\<leqslant\>|\<dot\>>a> or
    <math|b<wide|\<leqslant\>|\<dot\>>x>, depending on whether the
    coefficient of <math|x> is positive or negative. For each such pair of
    inequalities: if <math|b=a>, we add <math|x<wide|=|\<dot\>>a> to implicit
    equalities; otherwise, we add the inequality
    <math|b<wide|\<leqslant\>|\<dot\>>a> to the unsolved part of the
    constraint.
  </itemize>

  We use elimination to solve all equations before we proceed to
  inequalities. The starting point of our algorithm is <cite|ArithQuantElim>
  section <em|4.2 Online Fourier-Motzkin Elimination for Reals>. We add
  detection of implicit equalities, and more online treatment of equations,
  introducing known inequalities on eliminated variables to the projection
  process. When implicit equalities have been found, we iterate the process
  to normalize them as well.

  Our abduction algorithm follows a familiar incrementally-generate-and-test
  scheme as in term abduction. During the iteration, we build a lazy list of
  possible transformations with linear combinations involving atoms <math|a>
  that will not be part of the answer but are implied by <math|D\<wedge\>C>.

  Abduction algorithm:

  <\enumerate>
    <item>Let <math|C<rsup|=><rprime|'>=<wide|A<rsub|i>|~><around*|(|C<rsup|=>|)>>,
    resp. <math|C<rsup|\<leqslant\>><rprime|'>=<wide|A<rsub|i>|~><around*|(|C<rsup|\<leqslant\>>|)>>
    where <math|C<rsup|=>>, resp. <math|C<rsup|\<leqslant\>>> are the
    equations, resp. inequalities in <math|C> and <math|<wide|A<rsub|i>|~>>
    is the substitution according to equations in <math|A<rsub|i>>. Let
    <math|D<rprime|'>=<wide|A<rsub|i>|~><around*|(|D\<wedge\><no-break>A<rsub|i>|)>>
    and <math|D<rsup|=><rprime|'>> be the equations in <math|D<rprime|'>>,
    i.e. substituted equations and implicit equalities. Let
    <math|D<rsup|\<leqslant\>><rprime|'>=<wide|A<rsub|i>|~><around*|(|D<rsup|\<leqslant\>>|)>>.

    <item>Prepare the initial transformations from atoms in
    <math|D<rsup|=><rprime|'>> and <math|D<rsup|\<leqslant\>><rprime|'>>.

    <\enumerate>
      <item>For equations <math|a>, add combinations <math|k<rsup|s>*a+b> for
      <math|k=-n\<ldots\>n,s=-1,1> to the stack of transformations to be
      tried for atoms <math|b\<in\>C>.

      <item>For inequalities <math|a>, add combinations <math|k<rsup|s>*a+b>
      for <math|k=0\<ldots\>n,s=-1,1> to the stack of trasformations to be
      tried only for inequalities <math|b\<in\>C>.

      <item>The final transformations have the form:
      <math|b\<mapsto\>b+\<Sigma\><rsub|a\<in\>D>k<rsub|a><rsup|s<rsub|a>>a>.
    </enumerate>

    <item>Start from <math|Acc\<assign\><around*|{||}>> and
    <math|C<rsub|0>\<assign\>C<rsup|=><rprime|'>\<wedge\>C<rsup|\<leqslant\>><rprime|'>>.
    Try atoms <math|C<rsub|0>=a C<rsub|0><rprime|'>> in some order.

    <item>Let <math|B=A<rsub|i>\<wedge\>D\<wedge\>C<rsub|0><rprime|'>\<wedge\>Acc>.

    <item>If <math|a> is a tautology (<math|0<wide|=|\<dot\>>0> or
    <math|c\<leq\>0> for <math|c\<leqslant\>0>) or <math|B\<Rightarrow\>C>,
    repeat with <math|C<rsub|0>\<assign\>C<rsub|0><rprime|'>>. Corresponds to
    choice 1 of term abduction.

    <item>If <math|B\<nRightarrow\>C>, for a transformation
    <math|a<rprime|'>> of <math|a>, starting with <math|a>, which passes
    validation against other branches in a joint problem:
    <math|Acc\<assign\>Acc\<cup\><around*|{|a<rprime|'>|}>>, or fail if all
    <math|a<rprime|'>> fail. Choice point, corresponding to choice 4 if
    <math|a> is selected, choice 5 if a later transformation is selected.

    <\enumerate>
      <item>Let <math|a<rprime|'>> be <math|a> with some transformations
      applied.

      <item>If <math|A<rsub|i>\<wedge\><around*|(|Acc\<cup\><around*|{|a<rprime|'>|}>|)>>
      does not pass <verbatim|validate> for all <math|a<rprime|'>>, fail.

      <item>If <math|A<rsub|i>\<wedge\><around*|(|Acc\<cup\><around*|{|a<rprime|'>|}>|)>>
      passes <verbatim|validate>, add <math|a> to transformations as in step
      (2), and repeat with <math|C<rsub|0>\<assign\>C<rsub|0><rprime|'>,Acc\<assign\>Acc\<cup\><around*|{|a<rprime|'>|}>>.
    </enumerate>

    <item>The answers are <math|A<rsub|i+1>=A<rsub|i>\<wedge\>Acc>.
  </enumerate>

  We precompute the tranformation variants to try out. The parameter <math|n>
  is called <verbatim|abd_rotations> and defaults to a small value (currently
  3).

  To check whether <math|B\<Rightarrow\>C>, we check for each
  <math|c\<in\>C>:

  <\itemize>
    <item>if <math|c=x<wide|=|\<dot\>>y>, that
    <math|A<around*|(|x|)>=A<around*|(|y|)>>, where
    <math|A<around*|(|\<cdummy\>|)>> is the substitution corresponding to
    equations and implicit equalities in <math|A>;

    <item>if <math|c=x<wide|\<leqslant\>|\<dot\>>y>, that
    <math|B\<wedge\>y<wide|\<less\>|\<dot\>>x> is not satisfiable.
  </itemize>

  We use the <verbatim|nums> library for exact precision rationals.

  Our algorithm finds only fully maximal answers. This means that for many
  invariant inference problems, some implication branches in initial steps of
  the main algorithm are insolvable. That is, when the instantiations of the
  invariants found so far are not informative enough, the expected answer of
  the JCA problem is not a fully maximal SCA answer to these branches. The
  backtracking mechanism of the joint constraint abduction algorithm
  mitigates the problem.

  We provide an optional optimization: we do not pass, in the first call to
  numerical abduction (the second iteration of the main algorithm), branches
  that contain unary predicate variables in the conclusion, i.e. we only use
  the ``non-recursive'' branches. Other optimizations that we use are:
  iterative deepening on the constant <math|n> used to generate
  <math|k<rsup|s>> factors. We also constrain the algorithm by filtering out
  transformations that contain ``too many'' variables, which can lead to
  missing answers if the setting <verbatim|abd_prune_at> -- ``too many'' --
  is too low. Similarly to term abduction, we count the number of steps of
  the loop and fail if more than <verbatim|abd_timeout_count> steps have been
  taken.

  <section|Constraint Generalization>

  <em|Constraint generalization> answers are the maximally specific
  conjunctions of atoms that are implied by each of a given set of
  conjunction of atoms. In case of term equations the disjunction elimination
  algorithm is based on the <em|anti-unification> algorithm. In case of
  linear arithmetic inequalities, disjunction elimination is exactly finding
  the convex hull of a set of possibly unbounded polyhedra. We employ our
  unification algorithm to separate sorts. Since as a result we do not
  introduce variables for <em|alien subterms>, we include the variables
  introduced by anti-unification in constraints sent to disjunction
  elimination for their respective sorts.

  The adjusted algorithm looks as follows:

  <\enumerate>
    <item>Let <math|\<wedge\><rsub|s>D<rsub|i,s>\<equiv\>\<b-U\><around|(|D<rsub|i>|)>>
    where <math|D<rsub|i,s>> is of sort <math|s>, be the result of our
    sort-separating unification.

    <item>For the sort <math|s<rsub|ty>>:

    <\enumerate>
      <item>Let <math|V=<around*|{|x<rsub|j>,<wide|t<rsub|i,j>|\<bar\>><mid|\|>\<forall\>i\<exists\>t<rsub|i,j>.x<rsub|j><wide|=|\<dot\>>t<rsub|i,j>\<in\>D<rsub|i,s<rsub|ty>>|}>>.

      <item>Let <math|G=<around*|{|<wide|\<alpha\>|\<bar\>><rsub|j>,u<rsub|j>,<wide|\<theta\><rsub|i,j>|\<bar\>><mid|\|>\<theta\><rsub|i,j>=<around*|[|<wide|\<alpha\>|\<bar\>><rsub|j>\<assign\><wide|g|\<bar\>><rsub|j><rsup|i>|]>,\<theta\><rsub|i,j><around*|(|u<rsub|j>|)>=t<rsub|i,j>|}>>
      be the most specific anti-unifiers of <math|<wide|t<rsub|i,j>|\<bar\>>>
      for each <math|j>.

      <item>Let <math|D<rsub|i><rsup|u>=\<wedge\><rsub|j><wide|\<alpha\>|\<bar\>><rsub|j><wide|=|\<dot\>><wide|g|\<bar\>><rsub|j><rsup|i>>
      and <math|D<rsub|i><rsup|g>=D<rsub|i,s<rsub|ty>>\<wedge\>D<rsub|i><rsup|u>>.

      <item>Let <math|D<rsup|v><rsub|i>=<around*|{|x<wide|=|\<dot\>>y<mid|\|>x<wide|=|\<dot\>>t<rsub|1>\<in\>D<rsub|i><rsup|g>,y<wide|=|\<dot\>>t<rsub|2>\<in\>D<rsub|i><rsup|g>,D<rsub|i><rsup|g>\<vDash\>t<rsub|1><wide|=|\<dot\>>t<rsub|2>|}>>.

      <item>Let <math|A<rsub|s<rsub|ty>>=\<wedge\><rsub|j>x<rsub|j><wide|=|\<dot\>>u<rsub|j>\<wedge\><big|cap><rsub|i><around*|(|D<rsub|i><rsup|g>\<wedge\>D<rsub|i><rsup|v>|)>>
      (where conjunctions are treated as sets of conjuncts and equations are
      ordered so that only one of <math|a<wide|=|\<dot\>>b,b<wide|=|\<dot\>>a>
      appears anywhere), and <math|<wide|\<alpha\>|\<bar\>><rsub|s<rsub|ty>>=<wide|<wide|\<alpha\>|\<bar\>><rsub|j>|\<bar\>>>.

      <item>Let <math|\<wedge\><rsub|s>D<rsup|u><rsub|i,s>\<equiv\>D<rsup|u><rsub|i>>
      for <math|D<rsup|u><rsub|i,s>> of sort <math|s>.
    </enumerate>

    <item>For sorts <math|s\<neq\>s<rsub|ty>>, let
    <math|\<exists\><wide|\<alpha\>|\<bar\>><rsub|s>.A<rsub|s>=DisjElim<rsub|s><around*|(|<wide|D<rsub|i><rsup|s>\<wedge\>D<rsup|u><rsub|i,s>|\<bar\>>|)>>.

    <item>The answer is <math|\<exists\><wide|<wide|\<alpha\><rsup|j><rsub|i>|\<bar\>>|\<bar\>><wide|<wide|\<alpha\>|\<bar\>><rsub|s>|\<bar\>>.\<wedge\><rsub|s>A<rsub|s>>.
  </enumerate>

  We simplify the result by substituting-out redundant answer variables.

  We follow the anti-unification algorithm provided in <cite|AntiUnifAlg>,
  fig. 2.

  <subsection|Extended convex hull>

  <cite|ConvexHull> provides a polynomial-time algorithm to find the
  half-space represented convex hull of closed polytopes. It can be
  generalized to unbounded polytopes -- conjunctions of linear inequalities.
  Our implementation is inspired by this algorithm but very much simpler, at
  cost of losing the maximality requirement.

  First we find among the given inequalities those which are also the faces
  of resulting convex hull. The negation of such inequality is not
  satisfiable in conjunction with any of the polytopes -- any of the given
  sets of inequalities. Next we iterate over <em|ridges> touching the
  selected faces: pairs of the selected face and another face from the same
  polytope. We rotate one face towards the other: we compute a convex
  combination of the two faces of a ridge. We add to the result those
  half-spaces whose complements lie outside of the convex hull (i.e. negation
  of the inequality is unsatisfiable in conjunction with every polytope). For
  a given ridge, we add at most one face, the one which is farthest away from
  the already selected face, i.e. the coefficient of the selected face in the
  convex combination is smallest. We check a small number of rotations, where
  the algorithm from <cite|ConvexHull> would solve a linear programming
  problem to find the rotation which exactly touches another one of the
  polytopes.

  When all variables of an equation <math|a<wide|=|\<dot\>>b> appear in all
  branches <math|D<rsub|i>>, we can turn the equation
  <math|a<wide|=|\<dot\>>b> into pair of inequalities
  <math|a\<leqslant\>b\<wedge\>b\<leqslant\>a>. We eliminate all equations
  and implicit equalities which contain a variable not shared by all
  <math|D<rsub|i>>, by substituting out such variables. We pass the resulting
  inequalities to the convex hull algorithm.

  <subsection|Issues in inferring postconditions><label|NumConv>

  Although finding recursive function invariants -- predicate variables
  solved by abduction -- could theoretically fail to converge for both the
  type sort and the numerical sort constraints, neither problem was observed.
  Finding existential type constraints can only fail to converge for
  numerical sort, because solutions are expected to decrease in strength. But
  such diverging numerical constraints are commonplace. The main algorithm
  starts by performing disjunction elimination only on implication branches
  corresponding to non-recursive cases, i.e. without binary predicate
  variables in premise (or unary predicate variables in conclusion). This
  generates a stronger constraint than the correct one. Subsequent iterations
  include all branches in disjunction elimination, weakening the constraints,
  and so still weaker constraints are fed to disjunction elimination in each
  following step. To ensure convergence of the numerical part, starting from
  some step of the main loop, we compare consecutive solutions and
  extrapolate the trend. Currently we simply intersect the sets of atoms, but
  first we expand equations into pairs of inequalities.

  Disjunction elimination limited to non-recursive branches, the initial
  iteration of postcondition inference, will often generate constraints that
  contradict other branches. For another iteration to go through, the partial
  solutions need to be consistent. Therefore we filter the constraints using
  the same validation mechanism as in abduction. We add atoms to a constraint
  greedily, but to favor relevant atoms, we do the filtering while computing
  the connected component of disjunction elimination result. See the details
  of the main algorithm in section <reference|MainAlgoBody>.

  While reading section <reference|MainAlgoBody>, you will notice that
  postconditions are not subjected to stratification. This is because the
  type system does not support nested existential types.

  In <verbatim|simplify_dsjelim>, we try to preserve alien variables that are
  parameters rather than substituting them by constants. A parameter can only
  equal a constant if not all branches have been considered for disjunction
  elimination. The parameter is both as informative as the constant, and less
  likely to contradict other branches.

  <subsection|Abductive disjunction elimination given quantifier prefix>

  <em|Global variables> here are the variables shared by all disjuncts, i.e.
  <math|\<cap\><rsub|i>FV<around*|(|D<rsub|i>|)>>, remaining variables are
  <em|non-global>. Recall that for numerical disjunction elimination, we
  either substitute-out a non-global variable in a branch if it appears in an
  equation, or we drop the inequalities it appers in if it is not part of any
  equation. Non-global variables can also pose problems for the term sort, by
  forcing disjunction elimination answers to be too general. When inferring
  the type for a function, which has a branch that does not use one of
  arguments of the function, the existential type inferred would hide the
  corresponding information in the result, even if the remaining branches
  assume the argument has a single concrete type. We would like the
  corresponding non-local variable to resolve to the concrete type suggested
  by other branches of the resulting constraint.

  We extend the notion of disjunction elimination: substitution <math|U> and
  solved form <math|\<exists\><wide|\<alpha\>|\<bar\>>.A> is an answer to
  <em|abductive disjunction elimination> problem
  <math|<wide|D<rsub|i>|\<bar\>>> given a quantifier prefix <math|\<cal-Q\>>
  when:

  <\enumerate>
    <item><math|<around*|(|\<forall\>i|)>\<vDash\>U<around*|(|D<rsub|i>|)>\<Rightarrow\>\<exists\><wide|\<alpha\>|\<bar\>>\\FV<around*|(|U|)>.A>;

    <item>If <math|\<alpha\>\<in\>Dom<around*|(|U|)>>, then
    <math|<around*|(|\<exists\>\<alpha\>|)>\<in\>\<cal-Q\>> -- variables
    substituted by <math|U> are existentially quantified;

    <item><math|<around*|(|\<forall\>i|)>\<vDash\>\<forall\><around*|(|Dom<around*|(|U|)>|)>\<exists\><around*|(|FV<around*|(|D<rsub|i>|)>\\Dom<around*|(|U|)>|)>.D<rsub|i>>.
  </enumerate>

  The sort-integrating algorithm essentially does not change:

  <\enumerate>
    <item>Let <math|\<wedge\><rsub|s>D<rsub|i,s>\<equiv\>\<b-U\><around|(|D<rsub|i>|)>>
    where <math|D<rsub|i,s>> is of sort <math|s>, be the result of our
    sort-separating unification.

    <item>For the sort <math|s<rsub|ty>>:

    <\enumerate>
      <item>Let <math|V=<around*|{|x<rsub|j>,<wide|t<rsub|i,j>|\<bar\>><mid|\|>\<forall\>i\<exists\>t<rsub|i,j>.x<rsub|j><wide|=|\<dot\>>t<rsub|i,j>\<in\>D<rsub|i,s<rsub|ty>>|}>>.

      <item>Let <math|G=<around*|{|<wide|\<alpha\>|\<bar\>><rsub|j>,g<rsub|j>,u<rsub|j>,<wide|\<theta\><rsub|i,j>|\<bar\>><mid|\|>\<theta\><rsub|i,j>=<around*|[|<wide|\<alpha\>|\<bar\>><rsub|j>\<assign\><wide|g|\<bar\>><rsub|j><rsup|i>|]>,\<theta\><rsub|i,j><around*|(|g<rsub|j>|)>=<around*|(|\<wedge\><rsub|k\<leqslant\>j>u<rsub|k>|)><around*|(|t<rsub|i,j>|)>|}>>
      be the most specific anti-unifiers of
      <math|<wide|<rsub|><around*|(|\<wedge\><rsub|k\<leqslant\>j>u<rsub|k>|)><around*|(|t<rsub|i,j>|)>|\<bar\>>>
      for each <math|j>, where <math|\<wedge\><rsub|j>u<rsub|j>> is the
      resulting <math|U<rsub|>>.

      <item>Let <math|D<rsub|i><rsup|u>=\<wedge\><rsub|j><wide|\<alpha\>|\<bar\>><rsub|j><wide|=|\<dot\>><wide|g|\<bar\>><rsub|j><rsup|i>>
      and <math|D<rsub|i><rsup|g>=D<rsub|i,s<rsub|ty>>\<wedge\>D<rsub|i><rsup|u>>.

      <item>Let <math|D<rsup|v><rsub|i>=<around*|{|x<wide|=|\<dot\>>y<mid|\|>x<wide|=|\<dot\>>t<rsub|1>\<in\>D<rsub|i><rsup|g>,y<wide|=|\<dot\>>t<rsub|2>\<in\>D<rsub|i><rsup|g>,D<rsub|i><rsup|g>\<vDash\>t<rsub|1><wide|=|\<dot\>>t<rsub|2>|}>>.

      <item>Let <math|A<rsub|s<rsub|ty>>=\<wedge\><rsub|j>x<rsub|j><wide|=|\<dot\>>g<rsub|j>\<wedge\><big|cap><rsub|i><around*|(|D<rsub|i><rsup|g>\<wedge\>D<rsub|i><rsup|v>|)>>
      (where conjunctions are treated as sets of conjuncts and equations are
      ordered so that only one of <math|a<wide|=|\<dot\>>b,b<wide|=|\<dot\>>a>
      appears anywhere), and <math|<wide|\<alpha\>|\<bar\>><rsub|s<rsub|ty>>=<wide|<wide|\<alpha\>|\<bar\>><rsub|j>|\<bar\>>>.

      <item>Let <math|\<wedge\><rsub|s>D<rsup|u><rsub|i,s>\<equiv\>D<rsup|u><rsub|i>>
      for <math|D<rsup|u><rsub|i,s>> of sort <math|s>.
    </enumerate>

    <item>For sorts <math|s\<neq\>s<rsub|ty>>, let
    <math|\<exists\><wide|\<alpha\>|\<bar\>><rsub|s>.A<rsub|s>=DisjElim<rsub|s><around*|(|<wide|D<rsub|i><rsup|s>\<wedge\>D<rsup|u><rsub|i,s>|\<bar\>>|)>>.

    <item>The answer is substitution <math|U=\<wedge\><rsub|j>u<rsub|j>> and
    solved form <math|\<exists\><wide|<wide|\<alpha\><rsup|j><rsub|i>|\<bar\>>|\<bar\>><wide|<wide|\<alpha\>|\<bar\>><rsub|s>|\<bar\>>.\<wedge\><rsub|s>A<rsub|s>>.
  </enumerate>

  Our current generalized anti-unification algorithm:

  <\eqnarray*>
    <tformat|<table|<row|<cell|au<rsub|U,G><around*|(|t;\<ldots\>;t|)>>|<cell|=>|<cell|\<varnothing\>,t,U,G>>|<row|<cell|au<rsub|U,G><around*|(|f<around*|(|<wide|t|\<bar\>><rsup|1>|)>;\<ldots\>;f<around*|(|<wide|t|\<bar\>><rsup|n>|)>|)>>|<cell|=>|<cell|<wide|\<alpha\>|\<bar\>>,f<around*|(|<wide|g|\<bar\>>|)>,U<rprime|'>,G<rprime|'>>>|<row|<cell|<with|mode|text|where
    \ ><wide|\<alpha\>|\<bar\>>,<wide|g|\<bar\>>,U<rprime|'>,G<rprime|'>>|<cell|=>|<cell|aun<rsub|U,G><around*|(|<wide|t|\<bar\>><rsup|1>;\<ldots\>;<wide|t|\<bar\>><rsup|n>|)>>>|<row|<cell|au<rsub|U,G><around*|(|t<rsub|1>;\<ldots\>;t<rsub|n>|)>>|<cell|=>|<cell|\<varnothing\>,\<alpha\>,U,G>>|<row|<cell|<with|mode|text|when>>|<cell|>|<cell|<around*|(|<around*|[|t<rsub|1>;\<ldots\>;t<rsub|n>|]>\<mapsto\>\<alpha\>|)>\<in\>G>>|<row|<cell|au<rsub|U,G><around*|(|\<ldots\>;\<beta\><rsub|i>;\<ldots\>;f<around*|(|<wide|t|\<bar\>><rsup|j>|)>;\<ldots\><with|mode|text|
    as ><wide|t|\<bar\>>|)>>|<cell|=>|<cell|<wide|\<alpha\>|\<bar\>><wide|\<alpha\>|\<bar\>><rprime|'>,g,U<rprime|''>,G<rprime|'>>>|<row|<cell|<with|mode|text|where
    \ ><wide|\<alpha\>|\<bar\>><rprime|'>,g,U<rprime|''>,G<rprime|'>>|<cell|=>|<cell|au<rsub|U<rprime|'>,G><around*|(|<wide|t|\<bar\>><around*|[|\<beta\><rsub|i>\<assign\>f<around*|(|<wide|\<alpha\>|\<bar\>>|)>|]>|)>>>|<row|<cell|U<rprime|'>>|<cell|=>|<cell|U<around*|[|\<beta\><rsub|i>\<assign\>f<around*|(|<wide|\<alpha\>|\<bar\>>|)>|]>\<wedge\>\<beta\><rsub|i><wide|=|\<dot\>>f<around*|(|<wide|\<alpha\>|\<bar\>>|)>>>|<row|<cell|<with|mode|text|when>>|<cell|>|<cell|\<exists\>\<beta\><rsub|i>\<in\>\<cal-Q\><with|mode|text|,
    treat ><wide|\<alpha\>|\<bar\>><with|mode|text| as quantified with
    >\<exists\>\<beta\><rsub|i>>>|<row|<cell|au<rsub|U,G><around*|(|\<ldots\>;\<beta\><rsub|i>;\<ldots\>;\<beta\><rsub|j>;\<ldots\><with|mode|text|
    as ><wide|t|\<bar\>>|)>>|<cell|=>|<cell|<wide|\<alpha\>|\<bar\>><rprime|'>,g,U<rprime|''>,G<rprime|'>>>|<row|<cell|<with|mode|text|where
    \ ><wide|\<alpha\>|\<bar\>><rprime|'>,g,U<rprime|''>,G<rprime|'>>|<cell|=>|<cell|au<rsub|U<rprime|'>,G><around*|(|<wide|t|\<bar\>><around*|[|\<beta\><rsub|i>\<assign\>\<beta\><rsub|j>|]>|)>>>|<row|<cell|U<rprime|'>>|<cell|=>|<cell|U<around*|[|\<beta\><rsub|i>\<assign\>\<beta\><rsub|j>|]>\<wedge\>\<beta\><rsub|i><wide|=|\<dot\>>\<beta\><rsub|j>>>|<row|<cell|<with|mode|text|when>>|<cell|>|<cell|\<exists\>\<beta\><rsub|i>\<in\>\<cal-Q\>,\<beta\><rsub|j>\<leqslant\><rsub|\<cal-Q\>>\<beta\><rsub|i>>>|<row|<cell|au<rsub|U,G><around*|(|t<rsub|1>;\<ldots\>;t<rsub|n>|)>>|<cell|=>|<cell|\<alpha\>,\<alpha\>,U,<around*|(|<around*|[|t<rsub|1>;\<ldots\>;t<rsub|n>|]>\<mapsto\>\<alpha\>|)>G>>|<row|<cell|<with|mode|text|otherwise,>>|<cell|>|<cell|<with|mode|text|where
    >\<alpha\>#FV<around*|(|t<rsub|1>;\<ldots\>;t<rsub|n>,U,G|)>>>|<row|<cell|aun<rsub|U,G><around*|(|\<varnothing\>|)>>|<cell|=>|<cell|\<varnothing\>,\<varnothing\>,U,G>>|<row|<cell|aun<rsub|U,G><around*|(|\<varnothing\>;\<ldots\>|)>>|<cell|=>|<cell|\<varnothing\>,\<varnothing\>,U,G>>|<row|<cell|aun<rsub|U,G><around*|(|t<rsup|1><rsub|1>,<wide|t|\<bar\>><rsup|1>;\<ldots\>;t<rsup|n><rsub|1>,<wide|t|\<bar\>><rsup|n>|)>>|<cell|=>|<cell|<wide|\<alpha\>|\<bar\>><wide|\<alpha\>|\<bar\>><rprime|'>,g<wide|g|\<bar\>><rprime|'>,U<rprime|''>,G<rprime|''>>>|<row|<cell|<with|mode|text|where
    \ ><wide|\<alpha\>|\<bar\>>,g,U<rprime|'>,G<rprime|'>>|<cell|=>|<cell|au<rsub|U,G><around*|(|t<rsub|1><rsup|1>;\<ldots\>;t<rsub|1><rsup|n>|)>>>|<row|<cell|<with|mode|text|and
    \ ><wide|\<alpha\>|\<bar\>><rprime|'>,<wide|g|\<bar\>><rprime|'>,U<rprime|''>,G<rprime|''>>|<cell|=>|<cell|aun<rsub|U<rprime|'>,G<rprime|'>><around*|(|<wide|t|\<bar\>><rsup|1>;\<ldots\>;<wide|t|\<bar\>><rsup|n>|)>>>>>
  </eqnarray*>

  The notational shorthand <math|\<ldots\>;\<beta\><rsub|i>;\<ldots\>;f<around*|(|<wide|t|\<bar\>><rsup|j>|)>;\<ldots\>>
  represents the case where all terms are either existential variables or
  start with a function symbol <math|f>. Similarly,
  <math|\<ldots\>;\<beta\><rsub|i>;\<ldots\>;\<beta\><rsub|j>;\<ldots\>>
  represents the case when there is a variable <math|\<beta\><rsub|j>> such
  that all terms are either <math|\<beta\><rsub|j>> or are existential
  variables to the right of <math|\<beta\><rsub|j>> in the quantifier.

  The task of disjunction elimination is to find postconditions. Usually, it
  is beneficial to make the postcondition, i.e. the existential type that is
  the return type of a function, more specific, at the expense of making the
  overal type of the function less general. To this effect, disjunction
  elimination, just as abduction takes invariant parameters
  <math|<wide|\<beta\>|\<bar\>>>. We replace conditions
  <math|\<exists\>\<beta\><rsub|i>\<in\>\<cal-Q\>> above by
  <math|\<beta\><rsub|i>\<in\><wide|\<beta\>|\<bar\>>\<vee\>\<exists\>\<beta\><rsub|i>\<in\>\<cal-Q\>>.
  Recall that the right-hand-side (RHS) variable <math|\<beta\><rsub|j>> can
  in general be universally quantified: <math|\<forall\>\<beta\><rsub|j>\<in\>\<cal-Q\>>.
  We exclude universal non-parameter RHS when a parameter is present: if for
  any <math|\<beta\><rsub|i>>, <math|\<beta\><rsub|i>\<in\><wide|\<beta\>|\<bar\>>>,
  then for all <math|\<beta\><rsub|i>> including RHS,
  <math|\<beta\><rsub|i>\<in\><wide|\<beta\>|\<bar\>>\<vee\>\<exists\>\<beta\><rsub|i>\<in\>\<cal-Q\>>.
  Note that having weaker postconditions also results in correct types, just
  not the intended ones. In rare cases a weaker postcondition but a more
  general invariant can be beneficial. To this effect, the option
  <verbatim|-<no-break>more_existential> turns off generating the
  substitution entries when the RHS is a variable, i.e. the case
  <math|au<rsub|U,G><around*|(|\<ldots\>;\<beta\><rsub|i>;\<ldots\>;\<beta\><rsub|j>;\<ldots\><with|mode|text|
  as ><wide|t|\<bar\>>|)>> is skipped.

  Due to greater flexibility of the numerical domain, abductive extension of
  numerical disjunction elimination does not seem necessary.

  <subsection|Incorporating negative constraints><label|NegElim>

  We call a <em|negative constraint> an implication
  <math|D\<Rightarrow\>\<b-F\>> in the normalized constraint
  <math|\<cal-Q\>.\<wedge\><rsub|i><around*|(|D<rsub|i>\<Rightarrow\>C<rsub|i>|)>>,
  and we call <math|D> the <em|negated constraint>. Such constraints are
  generated for pattern matching branches whose right-hand-side is the
  expression <verbatim|assert false>. A generic approach to account for
  negative constraints is as follows. We check whether the solution found by
  multisort abduction contradicts the negated constraints. If some negated
  constraint is satisfiable, we discard the answer and ``fall back'' to try
  finding another answer. Unfortunately, this approach is insufficient when
  the answer sought for is not among the maximally general answers to the
  remaining, <em|positive part> of the constraint. Therefore, we introduce
  <em|negation elimination>.

  For the numerical sort, our implementation of negation elimination can
  produce too strong constraints when the numerical domain is intended to
  contain non-integer rational numbers, and can be turned off by the
  <verbatim|-no_int_negation> option. It can also produce too weak
  constraints, because it produces at most one atom for a given negated
  constraint. If the abduction answer for terms does already contradict a
  negated constraint <math|D>, we are done. Otherwise, let
  <math|D=c<rsub|1>\<wedge\>\<ldots\>\<wedge\>c<rsub|n>>. For numerical sort
  atoms <math|c<rsub|i>>, either drop them from consideration or convert
  their negation <math|\<neg\>c<rsub|i>> into <math|d<rsub|i>> or
  <math|d<rsub|i<rsub|1>>\<vee\>d<rsub|i<rsub|2>>> as follows. The conversion
  assumes that the numerical domain is integers. We convert an inequality
  <math|w\<leqslant\>0>, e.g. <math|<frac|1|3>x-<frac|1|2>y-2\<leqslant\>0>,
  to <math|*-k*w+1\<leqslant\>0>, e.g. <math|3y-2x+13\<leqslant\>0>, where
  <math|k> is the common denominator so that <math|k*w> has only integer
  numbers. Note that <math|\<neg\><around*|(|w\<leqslant\>0|)>\<Leftrightarrow\>w\<gtr\>0\<Leftrightarrow\>-w\<less\>0\<Leftrightarrow\>-k*w\<less\>0\<Leftarrow\>-k*w+1\<leqslant\>0>.
  Similarly, we convert an equation <math|w<wide|=|\<dot\>>0> to inequalities
  <math|-k*w+1\<leqslant\>0\<vee\>k*w+1\<leqslant\>0>. Note that
  <math|\<neg\><around*|(|w\<geqslant\>0|)>\<Leftrightarrow\>w\<less\>0\<Leftrightarrow\>k*w\<less\>0\<Leftarrow\>k*w+1\<leqslant\>0>.
  In both cases the implications <math|\<Leftarrow\>> would be equivalences
  if the numerical domain was integers rather than rational numbers. At
  present, we ignore <em|opti> atoms. The disjunct <math|d<rsub|i>> is a
  conjunction of inequalities if <math|c<rsub|i>> is a <em|subopti> atom.

  Assuming that each negative constraint points to a single atomic fact, we
  try to find one disjunct <math|d<rsub|i>>, resp. <math|d<rsub|i<rsub|1>>>
  or <math|d<rsub|i<rsub|2>>>, corresponding to <math|\<neg\>c<rsub|i>>,
  discarding those disjuncts that contradict any implication branch.
  Specifically, let <math|\<cal-Q\>.\<wedge\><rsub|i><around*|(|D<rsub|i>\<Rightarrow\>C<rsub|i>|)>>
  be the constraint we solve, and let <math|\<exists\><wide|\<alpha\>|\<bar\>>.A>
  be a term abduction answer for <math|\<cal-Q\>.\<wedge\><rsub|i:C<rsub|i>\<neq\>\<b-F\>><around*|(|D<rsub|i>\<Rightarrow\>C<rsub|i>|)>>.
  We search for <math|i> such that for all <math|k> with
  <math|C<rsub|k>\<neq\>\<b-F\>> and <math|D<rsub|k>> satisfiable,
  <math|d<rsub|i>\<wedge\>A\<wedge\>D<rsub|k>\<wedge\>C<rsub|k>> is
  satisfiable. We provide a function <math|NegElim<around*|(|\<neg\>D,<wide|B<rsub|i>|\<bar\>>|)>=d<rsub|i<rsub|0>>>,
  where <math|d<rsub|i<rsub|0>>> is the biggest, syntactically, such atom,
  and <math|B<rsub|i>=A\<wedge\>D<rsub|i>\<wedge\>C<rsub|i>>.

  Unfortunately, for the sort of terms we do not have well-defined
  representation of dis-equalities not using negations. The generic approach
  of relying on backtracking to find another abduction answer is more useful
  for terms than for the numeric sort. It falls short, however, when negation
  was intended to prevent the answer from being too general. Ideally, we
  would introduce disequation atoms <math|\<tau\><wide|\<neq\>|\<dot\>>\<tau\>>
  and follow the scheme we use for the numerical sort. For now, we only cover
  a very specific use of negation, to discriminate among type-level
  ``enumeration''. We limit negation elimination to considering atoms of the
  form <math|\<beta\><wide|=|\<dot\>>\<varepsilon\><rsub|1>>, and contradict
  them by introducing atoms <math|\<beta\><wide|=|\<dot\>>\<varepsilon\><rsub|2>>,
  for types <math|\<varepsilon\><rsub|1>\<neq\>\<varepsilon\><rsub|2>>
  without parameters which we call <em|phantom enumerations>. The variables
  <math|\<beta\>> are limited to the answer variables generated in the
  previous iteration of the main algorithm. The nullary datatype constructor
  <math|\<varepsilon\><rsub|2>> is picked so that the atom is valid, using
  the same validation procedure as the one passed to the abduction algorithm.
  The heuristic defines phantom enumerations as nullary phantom types that do
  not share datype parameter position (in GADT constructor definitions) with
  non-enumeration types. When the equations derived for different negated
  constraints involve a common variable as the left-hand-side, we select a
  common right-hand-side. In the end, we only introduce the negation
  elimination result to the answer when a single disjunct remains.

  Since the <em|discard> (or taboo) list used by backtracking is based on
  complete answers, it is preferable to perform negation elimination prior to
  abduction. Otherwise, the search might fall into a loop where abduction
  keeps returning the same answer, since it is more general than the
  discarded answer incorporating negation elimination result.

  <section|<em|opti> and <em|subopti>: <em|minimum> and <em|maximum>
  relations in <verbatim|num>><label|OptiAtoms>

  We extend the numerical domain with relations <em|opti> and <em|subopti>
  defined below. Operations <em|min> and <em|max> can then be defined using
  it. Let <math|k,v,w> be any linear combinations. Note that the relations
  are introduced to smuggle in a limited form of disjunction into the solved
  forms.

  <\eqnarray*>
    <tformat|<table|<row|<cell|opti<around*|(|v,w|)>>|<cell|=>|<cell|v\<leqslant\>0\<wedge\>w\<leqslant\>0\<wedge\><around*|(|v<wide|=|\<dot\>>0\<vee\>w<wide|=|\<dot\>>0|)>>>|<row|<cell|k<wide|=|\<dot\>>min<around*|(|v,w|)>>|<cell|\<equiv\>>|<cell|opti<around*|(|k-v,k-w|)>>>|<row|<cell|k<wide|=|\<dot\>>max<around*|(|v,w|)>>|<cell|\<equiv\>>|<cell|opti<around*|(|v-k,w-k|)>>>|<row|<cell|subopti<around*|(|v,w|)>>|<cell|=>|<cell|v\<leqslant\>0\<vee\>w\<leqslant\>0>>|<row|<cell|k\<leqslant\>max<around*|(|v,w|)>>|<cell|\<equiv\>>|<cell|subopti<around*|(|k-v,k-w|)>>>|<row|<cell|min<around*|(|v,w|)>\<leqslant\>k>|<cell|\<equiv\>>|<cell|subopti<around*|(|v-k,w-k|)>>>>>
  </eqnarray*>

  In particular, <math|opti<around*|(|v,w|)>\<equiv\>max<around*|(|v,w|)><wide|=|\<dot\>>0>
  and <math|subopti<around*|(|v,w|)>\<equiv\>min<around*|(|v,w|)>\<leqslant\>0>.
  We call an <em|opti> or <em|subopti> atom <em|directed> when there is a
  variable <math|n> that appears in <math|v> and <math|w> with the same sign.
  We do not prohibit undirected <em|opti> or <em|subopti> atoms, but we do
  not introduce them, to avoid bloat.

  For simplicity, we do not support <em|min> and <em|max> as subterms in
  concrete syntax. Instead, we parse atoms of the form
  <verbatim|k=min(<math|\<ldots\>>,<math|\<ldots\>>)>, resp.
  <verbatim|k=max(<math|\<ldots\>>,<math|\<ldots\>>)> into the corresponding
  <em|opti> atoms, where <verbatim|k> is any numerical term. Similarly for
  <em|subopti>. We also print directed <em|opti> and <em|subopti> atoms using
  the syntax with <math|min> and <math|max>expressions. Not to pollute the
  syntax with a new keyword, we use concrete syntax
  <verbatim|min\|max(<math|\<ldots\>>,<math|\<ldots\>>)> for parsing
  arbitrary, and printing non-directed, <em|opti> atoms, and
  <verbatim|min\|\|max(<math|\<ldots\>>,<math|\<ldots\>>)> for <em|subopti>
  respectively.

  If need arises, in a future version, we can extend <em|opti> to a larger
  arity <math|N>.

  <subsection|Normalization, validity and implication checking>

  In the solved form producing function <verbatim|solve_aux>, we treat
  <em|opti> clauses in an efficient but incomplete manner, doing a single
  step of constraint solving. We include the <em|opti> terms in processed
  inequalities. After equations have been solved, we apply the substitution
  to the <em|opti> and <em|subopti> disjunctions. When one of the <em|opti>
  resp. <em|subopti> disjunct terms becomes contradictory or the disjunct
  terms become equal, we include the other in implicit equalities, resp. in
  inequalities to solve. When one of the <em|opti> or <em|subopti> terms
  becomes tautological, we drop the disjunction. Recall that we iterate calls
  of <verbatim|solve_aux> to propagate implicit equalities.

  We do not perform case splitting on <em|opti> and <em|subopti>
  disjunctions, therefore some contradictions may be undetected. However,
  abduction and disjunction elimination currently perform upfront case
  splitting on <em|opti> and <em|subopti> disjunctions, sometimes leading to
  splits that a smarter solver would avoid.

  <subsection|Abduction>

  We eliminate <em|opti> and <em|subopti> in premises by expanding the
  definition and converting the branch into two branches, e.g.
  <math|D\<wedge\><around*|(|v<wide|=|\<dot\>>0\<vee\>w<wide|=|\<dot\>>0|)>\<Rightarrow\>C>
  into <math|<around*|(|D\<wedge\>v<wide|=|\<dot\>>0\<Rightarrow\>C|)>\<wedge\><around*|(|D\<wedge\>w<wide|=|\<dot\>>0\<Rightarrow\>C|)>>.
  Recall that an <em|opti> atom also implies inequalities
  <math|v\<leqslant\>\<wedge\>w\<leqslant\>0> assumed to be in <math|D>
  above. This is one form of <em|case splitting>: we consider cases
  <math|v<wide|=|\<dot\>>0> and <math|w<wide|=|\<dot\>>0>, resp.
  <math|v\<leqslant\>0> and <math|w\<leqslant\>0>, separately. We do not
  eliminate <em|opti> and <em|subopti> in conclusions. Rather, we consider
  whether to keep or drop it in the answer, like with other candidate atoms.
  The transformations apply to an <em|opti> atom by applying to both its
  arguments.

  Generating a new <em|opti> atom for inclusion in an answer means finding a
  pair of equations such that the following conditions hold. Each equation,
  together with remaining atoms of an answer but without the remaining
  equation selected, is a correct answer to a simple abduction problem. The
  equations selected share a variable and are oriented so that the variable
  appears with the same sign in them. The resulting <em|opti> atom passes the
  validation test for joint constraint abduction. We may implement generating
  new <em|opti> atoms for abduction answers in a future version, when need
  arises. Currently, we only generate new <em|opti> and <em|subopti> atoms
  for postconditions, i.e. during disjunction elimination.

  <subsection|Disjunction elimination>

  We eliminate <em|opti> and <em|subopti> atoms prior to finding the extended
  convex hull of <math|<wide|D<rsub|i>|\<bar\>>> by expanding the definition
  and converting the disjunction <math|\<vee\><rsub|i>D<rsub|i>> to
  disjunctive normal form. This is another form of case splitting.

  In addition to finding the extended convex hull, we need to discover
  <em|opti> relations that are implied by <math|\<vee\><rsub|i>D<rsub|i>>. We
  select these faces of the convex hull which also appear as an equation in
  some disjuncts. Out of these faces, we find all minimal covers of size 2,
  i.e. pairs of faces such that in each disjunct, either one or the other
  linear combination appears as an equation. We only keep pairs of faces that
  share a same-sign variable. For the purposes of detecting <em|opti>
  relations, we need to perform transitive closure of the extended convex
  hull equations and inequalities, because the redundant inequalities might
  be required to find a cover.

  Finding <em|subopti> atoms is similar. We find all minimal covers of size
  2, i.e. pairs of inequalities such that one or the other appears in each
  disjunct. We only keep pairs of inequalities that share a same-sign
  variable.

  We provide an <verbatim|initstep_heur> function for the numerical domain to
  remove <em|opti> atoms of the form <math|k<wide|=|\<dot\>>min<around*|(|c,v|)>>,
  <math|k<wide|=|\<dot\>>min<around*|(|v,c|)>>,
  <math|k<wide|=|\<dot\>>max<around*|(|c,v|)>> or
  <math|k<wide|=|\<dot\>>min<around*|(|v,c|)>> for a constant <math|c>,
  similarly for <em|subopti> atoms, while in initial iterations where
  disjunction elimination is only performed for non-recursive branches.

  <section|Solving for Predicate Variables><label|MainAlgo>

  As we decided to provide the first solution to abduction problems, we
  similarly simplify the task of solving for predicate variables. Instead of
  a tree of solutions being refined, we have a single sequence which we
  unfold until reaching fixpoint or contradiction. Another choice point
  besides abduction in the original algorithm is the selection of invariants
  that leaves a consistent subset of atoms as residuum. Here we also select
  the first solution found. We introduce a form of backtracking, described in
  section <reference|Details>.

  <subsection|Invariant Parameter Candidates>

  We start from the variables <math|\<beta\><rsub|\<chi\>>> that participate
  in negative occurrences of predicate variables:
  <math|\<chi\><around*|(|\<beta\><rsub|\<chi\>>|)>> or
  <math|\<chi\><around*|(|\<beta\><rsub|\<chi\>>,\<alpha\>|)>>. We select
  sets of variables <math|\<beta\><rsub|\<chi\>><wide|\<zeta\>|\<bar\>><rsup|\<chi\>>>,
  the <em|parameter candidates>, by considering all atoms of the generated
  constraints. <math|<wide|\<zeta\>|\<bar\>><rsup|\<chi\>>> are existential
  variables that: are connected with <math|\<beta\><rsub|\<chi\>>> in the
  hypergraph whose nodes are variables and hyperedges are atoms of the
  constraints, and are not connected with
  <math|\<beta\><rsub|\<chi\><rprime|'>>> for any
  <math|\<beta\><rsub|\<chi\><rprime|'>>> that is within scope of
  <math|\<beta\><rsub|\<chi\>>>. If <math|FV<around*|(|c|)>\<cap\>\<beta\><rsub|\<chi\>><wide|\<zeta\>|\<bar\>><rsup|\<chi\>>\<neq\>\<varnothing\>>
  for an atom <math|c>, and <math|\<beta\><rsub|\<chi\>>> is not in the scope
  of <math|\<beta\><rsub|\<chi\><rprime|'>>> for which
  <math|FV<around*|(|c|)>\<cap\>\<beta\><rsub|\<chi\><rprime|'>><wide|\<zeta\>|\<bar\>><rsup|\<chi\><rprime|'>>\<neq\>\<varnothing\>>,
  then <math|c> is a candidate for atoms of the solution of <math|\<chi\>>.

  <subsection|Solving for Predicates in Negative Positions>

  The core of our inference algorithm consists of distributing atoms of an
  abduction answer among the predicate variables. The negative occurrences of
  predicate variables, when instantiated with the updated solution, enrich
  the premises so that the next round of abduction leads to a smaller answer
  (in number of atoms).

  Let us discuss the algorithm for <math|Split<around*|(|\<cal-Q\>,<wide|\<alpha\>|\<bar\>>,A,<wide|<wide|\<beta\>|\<bar\>><rsup|\<chi\>>|\<bar\>>,<wide|A<rsub|\<chi\>><rsup|0>|\<bar\>>|)>>.
  Note that due to existential types predicates, we actually compute
  <math|Split<around*|(|\<cal-Q\>,<wide|\<alpha\>|\<bar\>>,A,<wide|<wide|\<beta\>|\<bar\>><rsup|\<beta\><rsub|\<chi\>>>|\<bar\>>,<wide|A<rsub|\<beta\><rsub|\<chi\>>><rsup|0>|\<bar\>>|)>>,
  i.e. we index by <math|\<beta\><rsub|\<chi\>>> (which can be multiple for a
  single <math|\<chi\>>) rather than <math|\<chi\>>. We retain the notation
  indexing by <math|\<chi\>> as it better conveys the intent. We do not pass
  quantifiers around to reflect the source code: the helper function
  <verbatim|loop avs ans sol> of function <verbatim|split> corresponds to
  <math|Split<around*|(|<wide|\<alpha\>|\<bar\>>,A,<wide|A<rsub|\<beta\><rsub|\<chi\>>><rsup|0>|\<bar\>>|)>>.

  <\eqnarray*>
    <tformat|<table|<row|<cell|\<alpha\>\<prec\>\<beta\>>|<cell|\<equiv\>>|<cell|\<alpha\>\<less\><rsub|\<cal-Q\>>\<beta\>\<vee\><around*|(|\<alpha\>\<leqslant\><rsub|\<cal-Q\>>\<beta\>\<wedge\>\<beta\>\<nless\><rsub|\<cal-Q\>>\<alpha\>\<wedge\>\<alpha\>\<in\><wide|<wide|\<beta\>|\<bar\>><rsup|\<chi\>>|\<bar\>>\<wedge\>\<beta\>\<nin\><wide|<wide|\<beta\>|\<bar\>><rsup|\<chi\>>|\<bar\>>|)>>>|<row|<cell|A<rsub|\<alpha\>\<beta\>>>|<cell|=>|<cell|<around*|{|\<beta\><wide|=|\<dot\>>\<alpha\>\<in\>A<mid|\|>\<beta\>\<in\><wide|<wide|\<beta\>|\<bar\>><rsup|\<chi\>>|\<bar\>>\<wedge\><around*|(|\<exists\>\<alpha\>|)>\<in\>\<cal-Q\>\<wedge\>\<beta\>\<prec\>\<alpha\>|}>>>|<row|<cell|A<rsub|0>>|<cell|=>|<cell|A\\A<rsub|\<alpha\>\<beta\>>>>|<row|<cell|A<rsup|1><rsub|\<chi\>>>|<cell|=>|<cell|<around*|{|c\<in\>A<rsub|0><mid|\|>\<forall\>\<alpha\>\<in\>FV<around*|(|c|)>\\<wide|\<beta\>|\<bar\>><rsup|\<chi\>>.<around*|(|\<exists\>\<alpha\>|)>\<in\>\<cal-Q\>|}>>>|<row|<cell|<with|mode|text|if>>|<cell|>|<cell|\<cal-M\>\<nvDash\>\<cal-Q\>.<around*|(|A\<setminus\>\<cup\><rsub|\<chi\>>A<rsup|1><rsub|\<chi\>>|)><around*|[|<wide|\<alpha\>|\<bar\>>\<assign\><wide|t|\<bar\>>|]><with|mode|text|
    \ for all ><wide|t|\<bar\>>>>|<row|<cell|<with|mode|text|then
    return>>|<cell|>|<cell|\<bot\>>>|<row|<cell|<with|mode|text|for all
    ><wide|A<rsub|\<chi\>><rsup|+>|\<bar\>><with|mode|text| min. w.r.t.
    >\<subset\><with|mode|text| s.t.>>|<cell|>|<cell|\<wedge\><rsub|\<chi\>><around*|(|A<rsub|\<chi\>><rsup|+>\<subset\>A<rsub|\<chi\>><rsup|1>|)>\<wedge\>\<cal-M\>\<vDash\>\<cal-Q\>.<around*|(|A\<setminus\>\<cup\><rsub|\<chi\>>A<rsub|\<chi\>><rsup|+>|)><around*|[|<wide|\<alpha\>|\<bar\>>\<assign\><wide|t|\<bar\>>|]><with|mode|text|
    \ for some ><wide|t|\<bar\>>:>>|<row|<cell|<with|mode|text|if>>|<cell|>|<cell|Strat<around*|(|A<rsup|+><rsub|\<chi\>>,<wide|\<beta\>|\<bar\>><rsup|\<chi\>>|)><with|mode|text|
    \ returns >\<bot\><with|mode|text| for some
    >\<chi\>>>|<row|<cell|<with|mode|text|then
    return>>|<cell|>|<cell|\<bot\>>>|<row|<cell|<with|mode|text|else
    \ ><wide|\<alpha\>|\<bar\>><rsub|+><rsup|\<chi\>>,A<rsub|\<chi\>><rsup|L>,A<rsup|R><rsub|\<chi\>>>|<cell|=>|<cell|Strat<around*|(|A<rsup|+><rsub|\<chi\>>,<wide|\<beta\>|\<bar\>><rsup|\<chi\>>|)>>>|<row|<cell|A<rsub|\<chi\>>>|<cell|=>|<cell|A<rsub|\<chi\>><rsup|0>\<cup\>A<rsub|\<chi\>><rsup|L>>>|<row|<cell|<wide|\<alpha\>|\<bar\>><rsup|\<chi\>><rsub|0>>|<cell|=>|<cell|<wide|\<alpha\>|\<bar\>>\<cap\>FV<around*|(|A<rsub|\<chi\>>|)>>>|<row|<cell|<wide|\<alpha\>|\<bar\>><rsup|\<chi\>>>|<cell|=>|<cell|<around*|(|<wide|\<alpha\>|\<bar\>><rsup|\<chi\>><rsub|0>\<setminus\><big|cup><rsub|\<chi\><rprime|'>\<less\><rsub|\<cal-Q\>>\<chi\>><wide|\<alpha\>|\<bar\>><rsup|\<chi\><rprime|'>><rsub|0>|)><wide|\<alpha\>|\<bar\>><rsub|+><rsup|\<chi\>>>>|<row|<cell|A<rsub|+>>|<cell|=>|<cell|\<cup\><rsub|\<chi\>>A<rsub|\<chi\>><rsup|R>>>|<row|<cell|A<rsub|res>>|<cell|=>|<cell|A<rsub|+>\<cup\><wide|A<rsub|+>|~><around*|(|A\<setminus\>\<cup\><rsub|\<chi\>>A<rsub|\<chi\>><rsup|+>|)>>>|<row|<cell|<with|mode|text|if>>|<cell|>|<cell|\<cup\><rsub|\<chi\>><wide|\<alpha\>|\<bar\>><rsup|\<chi\>>\<neq\>\<varnothing\><with|mode|text|
    \ then>>>|<row|<cell|\<cal-Q\><rprime|'>,A<rsub|res><rprime|'>,<wide|\<exists\><wide|\<alpha\>|\<bar\>><rprime|'><rsup|\<chi\>>.A<rsub|\<chi\>><rprime|'>|\<bar\>>>|<cell|\<in\>>|<cell|Split<around*|(|\<cal-Q\><around*|[|<wide|\<forall\><wide|\<beta\>|\<bar\>><rsup|\<chi\>>|\<bar\>>\<assign\><wide|\<forall\><around*|(|<wide|\<beta\>|\<bar\>><rsup|\<chi\>>\<cup\><wide|\<alpha\>|\<bar\>><rsup|\<chi\>>|)>|\<bar\>>|]>,<wide|\<alpha\>|\<bar\>>\<setminus\>\<cup\><rsub|\<chi\>><wide|\<alpha\>|\<bar\>><rsup|\<chi\>>,A<rsub|res>,<wide|<wide|\<beta\>|\<bar\>><rsup|\<chi\>>\<cup\><wide|\<alpha\>|\<bar\>><rsup|\<chi\>>|\<bar\>>,<wide|A<rsub|\<chi\>>|\<bar\>>|)>>>|<row|<cell|<with|mode|text|return>>|<cell|>|<cell|\<cal-Q\><rprime|'>,A<rsub|\<alpha\>\<beta\>>\<wedge\>A<rsub|res><rprime|'>,<wide|\<exists\><wide|\<alpha\>|\<bar\>><rsup|\<chi\>><wide|\<alpha\>|\<bar\>><rprime|'><rsup|\<chi\>>.A<rsub|\<chi\>><rprime|'>|\<bar\>>>>|<row|<cell|<with|mode|text|else
    return>>|<cell|>|<cell|\<cal-Q\>\<exists\><around*|(|<wide|\<alpha\>|\<bar\>>\<setminus\>\<cup\><rsub|\<chi\>><wide|\<alpha\>|\<bar\>><rsup|\<chi\>>|)>,A<rsub|\<alpha\>\<beta\>>\<wedge\>A<rsub|res>,<wide|\<exists\><wide|\<alpha\>|\<bar\>><rsup|\<chi\>>.A<rsub|\<chi\>>|\<bar\>>>>>>
  </eqnarray*>

  where <math|Strat<around*|(|A,<wide|\<beta\>|\<bar\>><rsup|\<chi\>>|)>> is
  computed as follows: for every <math|c\<in\>A>, and for every
  <math|\<beta\><rsub|2>\<in\>FV<around*|(|c|)>> such that
  <math|\<beta\><rsub|1>\<less\><rsub|\<cal-Q\>>\<beta\><rsub|2>> for
  <math|\<beta\><rsub|1>\<in\><wide|\<beta\>|\<bar\>><rsup|\<chi\>>>, if
  <math|\<beta\><rsub|2>> is universally quantified in <math|\<cal-Q\>>, then
  return <math|\<bot\>>; otherwise, introduce a fresh variable
  <math|\<alpha\><rsub|f>>, replace <math|c\<assign\>c<around*|[|\<beta\><rsub|2>\<assign\>\<alpha\><rsub|f>|]>>,
  add <with|mode|math|\<beta\><rsub|2><wide|=|\<dot\>>\<alpha\><rsub|f>> to
  <with|mode|math|A<rsup|R><rsub|\<chi\>>> and <math|\<alpha\><rsub|f>> to
  <with|mode|math|<wide|\<alpha\>|\<bar\>><rsub|+><rsup|\<chi\>>>, after
  replacing all such <with|mode|math|\<beta\><rsub|2>> add the resulting
  <math|c> to <with|mode|math|A<rsub|\<chi\>><rsup|L>>.

  Description of the algorithm in more detail:

  <\enumerate>
    <item><math|<tabular|<tformat|<table|<row|<cell|\<alpha\>\<prec\>\<beta\>>|<cell|\<equiv\>>|<cell|\<alpha\>\<less\><rsub|\<cal-Q\>>\<beta\>\<vee\><around*|(|\<alpha\>\<leqslant\><rsub|\<cal-Q\>>\<beta\>\<wedge\>\<beta\>\<nless\><rsub|\<cal-Q\>>\<alpha\>\<wedge\>\<alpha\>\<in\><wide|<wide|\<beta\>|\<bar\>><rsup|\<chi\>>|\<bar\>>\<wedge\>\<beta\>\<nin\><wide|<wide|\<beta\>|\<bar\>><rsup|\<chi\>>|\<bar\>>|)>>>>>>>
    The variables <math|<wide|<wide|\<beta\>|\<bar\>><rsup|\<chi\>>|\<bar\>>>
    are the answer variables of the solution from the previous round. We need
    to keep them apart from other variables even when they're not separated
    by quantifier alternation.

    <item><math|<tabular|<tformat|<table|<row|<cell|A<rsub|0>>|<cell|=>|<cell|A\\A<rsub|\<alpha\>\<beta\>>>>>>>>
    where<math|<tabular|<tformat|<table|<row|<cell|A<rsub|\<alpha\>\<beta\>>>|<cell|=>|<cell|<around*|{|\<beta\><wide|=|\<dot\>>\<alpha\>\<in\>A<mid|\|>\<beta\>\<in\><wide|<wide|\<beta\>|\<bar\>><rsup|\<chi\>>|\<bar\>>\<wedge\><around*|(|\<exists\>\<alpha\>|)>\<in\>\<cal-Q\>\<wedge\>\<beta\>\<prec\>\<alpha\>|}>>>>>>>
    Discard the ``scaffolding'' information, in particular the
    <math|A<rsub|+>> equations introduced by <math|Strat> in an earlier
    iteration.

    <item><math|<tabular|<tformat|<table|<row|<cell|A<rsup|1><rsub|\<chi\>>>|<cell|=>|<cell|<around*|{|c\<in\>A<rsub|0><mid|\|>\<forall\>\<alpha\>\<in\>FV<around*|(|c|)>\\<wide|\<beta\>|\<bar\>><rsup|\<chi\>>.<around*|(|\<exists\>\<alpha\>|)>\<in\>\<cal-Q\>|}>>>>>>>
    Gather atoms pertaining to predicate <math|\<chi\>>, which should not
    remain in the residuum.

    <item><math|<tabular|<tformat|<table|<row|<cell|<with|mode|text|if
    >\<cal-M\>\<nvDash\>\<cal-Q\>.<around*|(|A\<setminus\>\<cup\><rsub|\<chi\>>A<rsup|1><rsub|\<chi\>>|)><around*|[|<wide|\<alpha\>|\<bar\>>\<assign\><wide|t|\<bar\>>|]><with|mode|text|
    \ for all ><wide|t|\<bar\>><with|mode|text| then return >\<bot\>>>>>>>:
    Failed solution attempt. A common example is when the use site of
    recursive definition, resp. the existential type introduction site, is
    not in scope of a defining site of recursive definition, resp. an
    existential type elimination site, and has too strong requirements.

    <item><math|<tabular|<tformat|<table|<row|<cell|<with|mode|text|for all
    ><wide|A<rsub|\<chi\>><rsup|+>|\<bar\>><with|mode|text| min. w.r.t.
    >\<subset\><with|mode|text| s.t.>>|<cell|>|<cell|\<wedge\><rsub|\<chi\>><around*|(|A<rsub|\<chi\>><rsup|+>\<subset\>A<rsub|\<chi\>><rsup|1>|)>\<wedge\>\<cal-M\>\<vDash\>\<cal-Q\>.<around*|(|A\<setminus\>\<cup\><rsub|\<chi\>>A<rsub|\<chi\>><rsup|+>|)><around*|[|<wide|\<alpha\>|\<bar\>>\<assign\><wide|t|\<bar\>>|]><with|mode|text|
    \ for some ><wide|t|\<bar\>>:>>>>>> Select invariants such that the
    residuum <math|A\<setminus\>\<cup\><rsub|\<chi\>>A<rsub|\<chi\>><rsup|+>>
    is consistent. The final residuum <math|A<rsub|res>> represents the
    global constraints, the solution for global type variables. The solutions
    <math|A<rsub|\<chi\>><rsup|+>> represent the invariants, the solution for
    invariant type parameters.

    <item><math|<tabular|<tformat|<table|<row|<cell|<with|mode|text|if>>|<cell|>|<cell|Strat<around*|(|A<rsup|+><rsub|\<chi\>>,<wide|\<beta\>|\<bar\>><rsup|\<chi\>>|)><with|mode|text|
    \ returns >\<bot\><with|mode|text| for some
    >\<chi\>>>>>><with|mode|text|then return >\<bot\>> In the implementation,
    we address stratification issues already during abduction.

    <item><math|<wide|\<alpha\>|\<bar\>><rsub|+><rsup|\<chi\>>,A<rsub|\<chi\>><rsup|L>,A<rsup|R><rsub|\<chi\>>=Strat<around*|(|A<rsup|+><rsub|\<chi\>>,<wide|\<beta\>|\<bar\>><rsup|\<chi\>>|)>>
    is computed as follows: for every <math|c\<in\>A<rsup|+><rsub|\<chi\>>>,
    and for every <math|\<beta\><rsub|2>\<in\>FV<around*|(|c|)>> such that
    <math|\<beta\><rsub|1>\<less\><rsub|\<cal-Q\>>\<beta\><rsub|2>> for
    <math|\<beta\><rsub|1>\<in\><wide|\<beta\>|\<bar\>><rsup|\<chi\>>>, if
    <math|\<beta\><rsub|2>> is universally quantified in <math|\<cal-Q\>>,
    then return <math|\<bot\>>; otherwise, introduce a fresh variable
    <math|\<alpha\><rsub|f>>, replace <math|c\<assign\>c<around*|[|\<beta\><rsub|2>\<assign\>\<alpha\><rsub|f>|]>>,
    add <with|mode|math|\<beta\><rsub|2><wide|=|\<dot\>>\<alpha\><rsub|f>> to
    <with|mode|math|A<rsup|R><rsub|\<chi\>>> and <math|\<alpha\><rsub|f>> to
    <with|mode|math|<wide|\<alpha\>|\<bar\>><rsub|+><rsup|\<chi\>>>, after
    replacing all such <with|mode|math|\<beta\><rsub|2>> add the resulting
    <math|c> to <with|mode|math|A<rsub|\<chi\>><rsup|L>>.

    <\itemize>
      <item>We will add <math|<wide|\<alpha\>|\<bar\>><rsub|+><rsup|\<chi\>>>
      to <math|<wide|\<beta\>|\<bar\>><rsup|\<chi\>>>.
    </itemize>

    <item><math|<tabular|<tformat|<table|<row|<cell|A<rsub|\<chi\>>>|<cell|=>|<cell|A<rsub|\<chi\>><rsup|0>\<cup\>A<rsub|\<chi\>><rsup|L>>>>>>>
    is the updated solution formula for <math|\<chi\>>, where
    <math|A<rsub|\<chi\>><rsup|0>> is the solution from previous round.

    <item><math|<tabular|<tformat|<table|<row|<cell|<wide|\<alpha\>|\<bar\>><rsup|\<chi\>><rsub|0>>|<cell|=>|<cell|<wide|\<alpha\>|\<bar\>>\<cap\>FV<around*|(|A<rsub|\<chi\>>|)>>>>>>>
    are the additional solution parameters coming from variables generated by
    abduction.

    <item><math|<tabular|<tformat|<table|<row|<cell|<wide|\<alpha\>|\<bar\>><rsup|\<chi\>>>|<cell|=>|<cell|<around*|(|<wide|\<alpha\>|\<bar\>><rsup|\<chi\>><rsub|0>\<setminus\><big|cup><rsub|\<chi\><rprime|'>\<less\><rsub|\<cal-Q\>>\<chi\>><wide|\<alpha\>|\<bar\>><rsup|\<chi\><rprime|'>><rsub|0>|)><wide|\<alpha\>|\<bar\>><rsub|+><rsup|\<chi\>>>>>>>>
    The final solution parameters also include the variables generated by
    <math|Strat>.

    <item><math|<tabular|<tformat|<table|<row|<cell|A<rsub|+>>|<cell|=>|<cell|\<cup\><rsub|\<chi\>>A<rsub|\<chi\>><rsup|R>>>>>>>
    and <math|<tabular|<tformat|<table|<row|<cell|A<rsub|res>>|<cell|=>|<cell|A<rsub|+>\<cup\><wide|A<rsub|+>|~><around*|(|A\<setminus\>\<cup\><rsub|\<chi\>>A<rsub|\<chi\>><rsup|+>|)>>>>>>>
    is the resulting global constraint, where <math|<wide|A<rsub|+>|~>> is
    the substitution corresponding to <math|A<rsub|+>>.

    <item><math|<tabular|<tformat|<table|<row|<cell|<with|mode|text|if>>|<cell|>|<cell|\<cup\><rsub|\<chi\>><wide|\<alpha\>|\<bar\>><rsup|\<chi\>>\<neq\>\<varnothing\><with|mode|text|
    \ then>>>>>>> -- If new parameters have been introduced, we need to
    redistribute the <math|<wide|A<rsub|+>|~><around*|(|A\<setminus\>\<cup\><rsub|\<chi\>>A<rsub|\<chi\>><rsup|+>|)>>
    atoms to make <math|\<cal-Q\><rprime|'>.A<rsub|res>> valid again.

    <item><math|<tabular|<tformat|<table|<row|<cell|\<cal-Q\><rprime|'>,A<rsub|res><rprime|'>,<wide|\<exists\><wide|\<alpha\>|\<bar\>><rprime|'><rsup|\<chi\>>.A<rsub|\<chi\>><rprime|'>|\<bar\>>>|<cell|\<in\>>|<cell|Split<around*|(|\<cal-Q\><around*|[|<wide|\<forall\><wide|\<beta\>|\<bar\>><rsup|\<chi\>>|\<bar\>>\<assign\><wide|\<forall\><around*|(|<wide|\<beta\>|\<bar\>><rsup|\<chi\>>\<cup\><wide|\<alpha\>|\<bar\>><rsup|\<chi\>>|)>|\<bar\>>|]>,<wide|\<alpha\>|\<bar\>>\<setminus\>\<cup\><rsub|\<chi\>><wide|\<alpha\>|\<bar\>><rsup|\<chi\>>,A<rsub|res>,<wide|<wide|\<beta\>|\<bar\>><rsup|\<chi\>>\<cup\><wide|\<alpha\>|\<bar\>><rsup|\<chi\>>|\<bar\>>,<wide|A<rsub|\<chi\>>|\<bar\>>|)>>>>>>>
    Recursive call includes <math|<wide|\<alpha\>|\<bar\>><rsup|\<chi\>><rsub|+>>
    in <math|<wide|\<beta\>|\<bar\>><rsup|\<chi\>>> so that, among other
    things, <math|A<rsub|+>> are redistributed into <math|A<rsub|\<chi\>>>.

    <item><math|<tabular|<tformat|<table|<row|<cell|<with|mode|text|return>>|<cell|>|<cell|\<cal-Q\><rprime|'>,A<rsub|res><rprime|'>,<wide|\<exists\><wide|\<alpha\>|\<bar\>><rsup|\<chi\>><wide|\<alpha\>|\<bar\>><rprime|'><rsup|\<chi\>>.A<rsub|\<chi\>><rprime|'>|\<bar\>>>>>>>>
    We do not add <math|\<forall\><wide|\<alpha\>|\<bar\>>> in front of
    <math|\<cal-Q\><rprime|'>> because it already includes these variables.
    <math|<wide|<wide|\<alpha\>|\<bar\>><rsub|+><rsup|\<chi\>><wide|\<alpha\><rsub|>|\<bar\>><rsup|\<chi\>><rsub|+><rprime|'>|\<bar\>>>
    lists all variables introduced by <math|Strat>.

    <item><math|<tabular|<tformat|<table|<row|<cell|<with|mode|text|else
    return>>|<cell|>|<cell|\<cal-Q\>\<exists\><around*|(|<wide|\<alpha\>|\<bar\>>\<setminus\>\<cup\><rsub|\<chi\>><wide|\<alpha\>|\<bar\>><rsup|\<chi\>>|)>,A<rsub|res>,<wide|\<exists\><wide|\<alpha\>|\<bar\>><rsup|\<chi\>>.A<rsub|\<chi\>>|\<bar\>>>>>>>>
    Note that <math|<wide|\<alpha\>|\<bar\>>\<setminus\>\<cup\><rsub|\<chi\>><wide|\<alpha\>|\<bar\>><rsup|\<chi\>>>
    does not contain the current <math|<wide|\<beta\>|\<bar\>><rsup|\<chi\>>>,
    because <math|<wide|\<alpha\>|\<bar\>>> does not contain it initially and
    the recursive call maintains that: <math|<wide|\<alpha\>|\<bar\>>\<assign\><wide|\<alpha\>|\<bar\>>\<setminus\>\<cup\><rsub|\<chi\>><wide|\<alpha\>|\<bar\>><rsup|\<chi\>>,<wide|\<beta\>|\<bar\>><rsup|\<chi\>>\<assign\><wide|\<beta\>|\<bar\>><rsup|\<chi\>><wide|\<alpha\>|\<bar\>><rsup|\<chi\>>>.
  </enumerate>

  Finally we define <math|Split<around*|(|<wide|\<alpha\>|\<bar\>>,A|)>\<assign\>Split<around*|(|<wide|\<alpha\>|\<bar\>>,A,<wide|\<b-T\>|\<bar\>>|)>>.
  The complete algorithm for solving predicate variables is presented in the
  next section.

  <subsection|Solving for Existential Types Predicates and Main
  Algorithm><label|MainAlgoBody>

  The general scheme is that we perform disjunction elimination on branches
  with positive occurrences of existential type predicate variables on each
  round. Since the branches are substituted with the solution from previous
  round, disjunction elimination will automatically preserve monotonicity. We
  retain existential types predicate variables in the later abduction step.

  What differentiates existential type predicate variables from recursive
  definition predicate variables is that the former are not local to context
  in our implementation, we ignore the <verbatim|CstrIntro> rule, while the
  latter are treated as local to context in the implementation. It means that
  free variables need to be bound in the former while they are retained in
  the latter.

  In the algorithm we operate on all predicate variables, and perform
  additional operations on existential type predicate variables; there are no
  operations pertaining only to recursive definition predicate variables. The
  equation numbers <math|<around*|(|N|)>> below are matched by comment
  numbers <verbatim|(* N *)> in the source code. Let
  <math|\<chi\><rsub|\<varepsilon\>K>> be the invariant which will constrain
  the existential type <math|\<varepsilon\><rsub|K>>, or <math|\<top\>>. When
  <math|\<chi\><rsub|\<varepsilon\>K>=\<top\>>, then we define
  <math|<wide|\<beta\>|\<bar\>><rsup|\<chi\><rsub|\<varepsilon\>K>,k>=\<varnothing\>>.
  Step <math|k> of the loop of the final algorithm:

  <\eqnarray*>
    <tformat|<cwith|13|13|2|2|cell-valign|c>|<cwith|14|14|3|3|cell-valign|B>|<table|<row|<cell|<wide|\<exists\><wide|\<beta\>|\<bar\>><rsup|\<chi\>,k>.F<rsub|\<chi\>>|\<bar\>>>|<cell|=>|<cell|S<rsub|k>>>|<row|<cell|D<rsub|K><rsup|\<alpha\>>\<Rightarrow\>C<rsub|K><rsup|\<alpha\>>\<in\>R<rsub|k><rsup|->S<rsub|k><around*|(|\<Phi\>|)>>|<cell|=>|<cell|<with|mode|text|all
    such that >\<chi\><rsub|K><around*|(|\<alpha\>,\<alpha\><rsub|\<alpha\>><rsup|K>|)>\<in\>C<rsub|K><rsup|\<alpha\>>,<eq-number>>>|<row|<cell|>|<cell|>|<cell|<wide|C<rsup|\<alpha\>><rsub|j>|\<bar\>>=<around*|{|C<mid|\|>D\<Rightarrow\>C\<in\>S<rsub|k><around*|(|\<Phi\>|)>\<wedge\>D\<subseteq\>D<rsup|\<alpha\>><rsub|K>|}>>>|<row|<cell|U<rsub|\<chi\><rsub|K>>,\<exists\><wide|\<alpha\>|\<bar\>><rsup|\<chi\><rsub|K>><rsub|g>.G<rsub|\<chi\><rsub|K>>>|<cell|>|<cell|DisjElim<around*|(|<wide|\<delta\><wide|=|\<dot\>>\<alpha\>\<wedge\>D<rsup|\<alpha\>><rsub|K>\<wedge\><rsub|j>C<rsup|\<alpha\>><rsub|j>|\<bar\>><rsub|\<alpha\>\<in\><wide|\<alpha\><rsub|3><rsup|i,K>|\<bar\>>>|)><eq-number>>>|<row|<cell|\<exists\><wide|\<alpha\>|\<bar\>><rsup|\<chi\><rsub|K>>.G<rsub|\<chi\><rsub|K>><rprime|'>>|<cell|=>|<cell|Simpl<around*|(|FV<around*|(|G<rsub|\<chi\><rsub|K>>|)>\\\<delta\><wide|\<beta\>|\<bar\>><rsup|\<chi\><rsub|\<varepsilon\>K>,k>.G<rsub|\<chi\><rsub|K>>|)><eq-number>>>|<row|<cell|<wide|\<tau\>|\<vect\>><rsub|\<varepsilon\><rsub|K>>>|<cell|=>|<cell|<wide|<around*|{|\<alpha\>\<in\>FV<around*|(|G<rsub|\<chi\><rsub|K>><rprime|'>|)>\\\<delta\>\<delta\><rprime|'><wide|\<alpha\>|\<bar\>><rsup|\<chi\><rsub|K>><rsub|g><mid|\|><around*|(|\<exists\>\<alpha\>|)>\<in\>\<cal-Q\>\<vee\>\<alpha\>\<in\><wide|\<beta\>|\<bar\>><rsup|\<chi\><rsub|\<varepsilon\>K>,k>|}>|\<vect\>>>>|<row|<cell|\<Xi\><around*|(|\<exists\><wide|\<alpha\>|\<bar\>><rsup|\<chi\><rsub|K>><rsub|g>.G<rsub|\<chi\><rsub|K>>|)>>|<cell|=>|<cell|\<exists\>FV<around*|(|G<rsub|\<chi\><rsub|K>><rprime|'>|)>\\\<delta\>\<delta\><rprime|'>.\<delta\><rprime|'><wide|=|\<dot\>><wide|\<tau\>|\<vect\>><rsub|\<varepsilon\><rsub|K>>\<wedge\>G<rsub|\<chi\><rsub|K>><rprime|'>>>|<row|<cell|R<rsub|g><around*|(|\<chi\><rsub|K>|)>=\<exists\><wide|\<alpha\>|\<bar\>><rsup|\<chi\><rsub|K>>.F<rsub|\<chi\><rsub|K>>>|<cell|=>|<cell|H<around*|(|R<rsub|k><around*|(|\<chi\><rsub|K>|)>,\<Xi\><around*|(|\<exists\><wide|\<alpha\>|\<bar\>><rsub|g><rsup|\<chi\><rsub|K>>.G<rsub|\<chi\><rsub|K>>|)>|)><eq-number><label|Rg>>>|<row|<cell|P<rsub|g><around*|(|\<chi\><rsub|K>|)>>|<cell|=>|<cell|\<delta\><rprime|'><wide|=|\<dot\>><wide|\<tau\>|\<vect\>><rsub|\<varepsilon\><rsub|K>>\<wedge\>\<exists\><wide|\<alpha\>|\<bar\>><rsub|g><rsup|\<chi\><rsub|K>>.F<rsub|\<chi\><rsub|K>>>>|<row|<cell|F<rsub|\<chi\>><rprime|'>>|<cell|=>|<cell|F<rsub|\<chi\>><around*|[|\<varepsilon\><rsub|K><around*|(|\<cdummy\>|)>\<assign\>\<varepsilon\><rsub|K><around*|(|<wide|\<tau\>|\<vect\>><rsub|\<varepsilon\><rsub|K>>|)>|]>>>|<row|<cell|S<rsub|k><rprime|'>>|<cell|=>|<cell|<wide|\<exists\><wide|\<beta\>|\<bar\>><rsup|\<chi\>,k><around*|{|\<alpha\>\<in\>FV<around*|(|F<rprime|'><rsub|\<chi\>>|)><mid|\|>\<beta\><rsub|\<chi\>>\<less\><rsub|\<cal-Q\>>\<alpha\>|}>.F<rprime|'><rsub|\<chi\>><rsup|>|\<bar\>><eq-number>>>|<row|<cell|\<cal-Q\><rprime|'>.\<wedge\><rsub|i><around*|(|D<rsub|i>\<Rightarrow\>C<rsub|i>|)>\<wedge\><rsub|j><around*|(|D<rsub|j><rsup|->\<Rightarrow\>\<b-F\>|)>>|<cell|=>|<cell|R<rsub|g><rsup|->P<rsub|g><rsup|+>S<rsub|k><rprime|'><around*|(|\<Phi\>\<wedge\><rsub|\<chi\><rsub|K>>U<rsub|\<chi\><rsub|K>>|)>>>|<row|<cell|\<exists\><wide|\<alpha\>|\<bar\>>.A<rsub|0>>|<cell|=>|<cell|Abd<around*|(|\<cal-Q\><rprime|'>,<wide|\<beta\>|\<bar\>>=<wide|\<beta\><rsub|\<chi\>><wide|\<beta\><rsup|>|\<bar\>><rsup|\<chi\>>|\<bar\>>,<wide|D<rsub|i>,C<rsub|i>|\<bar\>>|)><eq-number>>>|<row|<cell|A>|<cell|=>|<cell|A<rsub|0>\<wedge\><rsub|j>NegElim<around*|(|\<neg\>Simpl<around*|(|FV<around*|(|D<rsub|j><rsup|->|)>\\<wide|<wide|\<beta\>|\<bar\>><rsup|\<chi\>>|\<bar\>>.D<rsub|j><rsup|->|)>,A<rsub|0>,<wide|D<rsub|i>,C<rsub|i>|\<bar\>>|)>>>|<row|<cell|>|<cell|>|<cell|<with|mode|text|At
    later iterations, check negative constraints.><eq-number>>>|<row|<cell|<around*|(|\<cal-Q\><rsup|k+1>,A<rsub|res>,<wide|\<exists\><wide|\<alpha\>|\<bar\>><rsup|\<beta\><rsub|\<chi\>>>.A<rsub|\<beta\><rsub|\<chi\>>>|\<bar\>>|)>>|<cell|=>|<cell|Split<around*|(|\<cal-Q\><rprime|'>,<wide|\<alpha\>|\<bar\>>,A,<wide|\<beta\><rsub|\<chi\>><wide|\<beta\><rsup|>|\<bar\>><rsup|\<chi\>>|\<bar\>>|)>>>|<row|<cell|<wide|\<tau\>|\<vect\>><rsub|\<varepsilon\><rsub|K>><rprime|'>>|<cell|=>|<cell|<wide|FV<around*|(|<wide|A<rsub|res>|~><around*|(|<wide|\<tau\>|\<vect\>><rsub|\<varepsilon\><rsub|K>>|)>|)>|\<vect\>>>>|<row|<cell|R<rsub|k+1><around*|(|\<chi\><rsub|K>|)>>|<cell|=>|<cell|\<exists\><wide|\<beta\>|\<bar\>><rsup|\<chi\><rsub|K>,k><wide|<wide|\<alpha\>|\<bar\>><rsup|\<beta\><rsub|\<chi\><rsub|K>>>|\<bar\>><wide|\<alpha\>|\<bar\>><rsup|\<chi\><rsub|K>>\\FV<around*|(|<wide|\<tau\>|\<vect\>><rsub|\<varepsilon\><rsub|K>><rprime|'>|)>.\<delta\><rprime|'><wide|=|\<dot\>><wide|\<tau\>|\<vect\>><rsub|\<varepsilon\><rsub|K>><rprime|'>\<wedge\><wide|A<rsub|res>|~><around*|(|F<rsub|\<chi\><rsub|K>>\\\<delta\><rprime|'><wide|=|\<dot\>>\<ldots\>|)><next-line><with|mode|text|
    \ \ \ >\<wedge\><rsub|\<chi\><rsub|K>>A<rsub|\<beta\><rsub|\<chi\><rsub|K>>><around*|[|<wide|\<beta\><rsub|\<chi\><rsub|K>><wide|\<beta\><rsup|>|\<bar\>><rsup|\<beta\><rsub|\<chi\><rsub|K>>>|\<bar\>>\<assign\><wide|\<delta\><wide|\<beta\><rsup|>|\<bar\>><rsup|\<chi\><rsub|K>,k>|\<bar\>>|]><eq-number>>>|<row|<cell|>|<cell|=>|<cell|R<rsub|g><rprime|'><around*|(|\<chi\><rsub|K>|)>>>|<row|<cell|S<rsub|k+1><around*|(|\<chi\>|)>>|<cell|=>|<cell|\<exists\><wide|\<beta\>|\<bar\>><rsup|\<chi\>,k>.Simpl<around*|(|\<exists\><wide|<wide|\<alpha\>|\<bar\>><rsup|\<beta\><rsub|\<chi\>>>|\<bar\>>.F<rsub|\<chi\>><rprime|'>\<wedge\>A<rsub|\<beta\><rsub|\<chi\>>><around*|[|<wide|\<beta\><rsub|\<chi\>><wide|\<beta\><rsup|>|\<bar\>><rsup|\<chi\>>|\<bar\>>\<assign\><wide|\<delta\><wide|\<beta\><rsup|>|\<bar\>><rsup|\<chi\>,k>|\<bar\>>|]>|)><eq-number><label|Skp1>>>|<row|<cell|<with|mode|text|if>>|<cell|>|<cell|<around*|(|\<forall\>\<chi\>|)>S<rsub|k+1><around*|(|\<chi\>|)>\<subseteq\>S<rsub|k><around*|(|\<chi\>|)>,<eq-number>>>|<row|<cell|>|<cell|>|<cell|<around*|(|\<forall\>\<chi\><rsub|K>|)>R<rsub|k+1><around*|(|\<chi\><rsub|K>|)>=R<rsub|k><around*|(|\<chi\><rsub|K>|)>,>>|<row|<cell|>|<cell|>|<cell|<around*|(|\<forall\>\<beta\><rsub|\<chi\><rsub|K>>|)>A<rsub|\<beta\><rsub|\<chi\><rsub|K>>>=\<b-T\>,>>|<row|<cell|>|<cell|>|<cell|k\<gtr\>1>>|<row|<cell|<with|mode|text|then
    return>>|<cell|>|<cell|A<rsub|res>,S<rsub|k+1>,R<rsub|k+1>>>|<row|<cell|<with|mode|text|repeat>>|<cell|>|<cell|k\<assign\>k+1<eq-number>>>>>
  </eqnarray*>

  Note that <math|Split> returns <math|<wide|\<exists\><wide|\<alpha\>|\<bar\>><rsup|\<beta\><rsub|\<chi\>>>.A<rsub|\<beta\><rsub|\<chi\>>>|\<bar\>>>
  rather than <math|<wide|\<exists\><wide|\<alpha\>|\<bar\>><rsup|\<chi\>>.A<rsub|\<chi\>>|\<bar\>>>.
  This is because in case of existential type predicate variables
  <math|\<chi\><rsub|K>>, there can be multiple negative position occurrences
  <math|\<chi\><rsub|K><around*|(|\<beta\><rsub|\<chi\><rsub|K>>,\<cdummy\>|)>>
  with different <math|\<beta\><rsub|\<chi\><rsub|K>>> when the corresponding
  value is used in multiple <math|<with|math-font-series|bold|let> \<ldots\>
  <with|math-font-series|bold|in>> expressions. The variant of the algorithm
  to achieve completeness would compute all answers for variants of
  <math|Abd> and <math|Split> algorithms that return multiple answers. Unary
  predicate variables <math|\<chi\><around*|(|\<beta\><rsub|\<chi\>>|)>> can
  also have multiple negative occurrences in the normalized form, but always
  with the same argument <math|\<beta\><rsub|\<chi\>>>. The substitution
  <math|<around*|[|<wide|\<beta\><rsub|\<chi\><rsub|K>><wide|\<beta\><rsup|>|\<bar\>><rsup|\<beta\><rsub|\<chi\><rsub|K>>>|\<bar\>>\<assign\><wide|\<delta\><wide|\<beta\><rsup|>|\<bar\>><rsup|\<chi\><rsub|K>,k>|\<bar\>>|]>>
  replaces the instance parameters introduced in
  <math|\<chi\><rsub|K><around*|(|\<beta\><rsub|\<chi\><rsub|K>>,\<cdummy\>|)>>
  by the formal parameters used in <math|R<rsub|k><around*|(|\<chi\><rsub|K>|)>>.
  The renamings from instance parameters to formal parameters are stored as
  <verbatim|q.b_renaming>.

  Even for a fixed <math|K>, the same branch
  <math|D<rsub|K><rsup|\<alpha\>>\<Rightarrow\>C<rsub|K><rsup|\<alpha\>>> can
  contribute to multiple disjuncts, with different
  <math|\<alpha\>=\<alpha\><rsub|3><rsup|i,K>>. Substitution
  <math|R<rsub|g><rsup|->> substitutes only negative occurrences of
  <math|\<chi\><rsub|K>>, i.e. it affects only the premises. Substitution
  <math|P<rsub|g><rsup|+>> substitutes only positive occurrences of
  <math|\<chi\><rsub|K>>, i.e. it affects only the conclusions.
  <math|P<rsub|g><rsup|+>> ensures that the parameter instances of the
  postcondition are connected with the argument variables.

  We start with <math|S<rsub|0>\<assign\><wide|\<b-T\>|\<bar\>>> and
  <math|R<rsub|0>\<assign\><wide|\<b-T\>|\<bar\>>>. <math|S<rsub|k>> grow in
  strength by definition. The disjunction elimination parts
  <math|G<rsub|\<chi\><rsub|K>>> of <math|R<rsub|1>> and <math|R<rsub|2>> are
  computed from non-recusrive branches only. Starting from <math|R<rsub|2>>,
  <math|R<rsub|k>> are expected to decrease in strength, but monotonicity is
  not guaranteed because of contributions from abduction: mostly in form of
  <math|A<rsub|\<beta\><rsub|\<chi\><rsub|K>>>>, but also from stronger
  premises due to <math|S<rsub|k>>.

  <math|Connected<around*|(|\<alpha\>,G|)>> is the connected component of
  hypergraph <math|G> containing node <math|\<alpha\>>, where nodes are
  variables <math|FV<around*|(|G|)>> and hyperedges are atoms
  <math|c\<in\>G>. <math|Connected<rsub|0><around*|(|\<delta\>,<around*|(|<wide|\<alpha\>|\<bar\>>,G|)>|)>>
  additionally removes atoms <math|c:FV<around*|(|c|)>#\<delta\><wide|\<alpha\>|\<bar\>>>.
  In initial iterations, when the branches
  <math|D<rsub|K><rsup|\<alpha\>>\<Rightarrow\>C<rsub|K><rsup|\<alpha\>>> are
  selected from non-recursive branches only, we include a connected atom only
  if it is satisfiable in all branches. <math|H<around*|(|R<rsub|k>,R<rsub|k+1>|)>>
  is a convergence improving heuristic, with
  <math|H<around*|(|R<rsub|k>,R<rsub|k+1>|)>=R<rsub|k+1>> for early
  iterations and ``roughly'' <math|H<around*|(|R<rsub|k>,R<rsub|k+1>|)>=R<rsub|k>\<cap\>R<rsub|k+1>>
  later. <math|H<around*|(|R<rsub|k>,R<rsub|k+1>|)>> does not perform
  simplification, only pruning.

  The condition <math|<around*|(|\<forall\>\<beta\><rsub|\<chi\><rsub|K>>|)>A<rsub|\<beta\><rsub|\<chi\><rsub|K>>>=\<b-T\>>
  is required for correctness of returned answer. Fixpoint of postconditions
  <math|R<rsub|k><around*|(|\<chi\><rsub|K>|)>> is not a sufficient stopping
  condition, because it does not imply <math|A<rsub|\<beta\><rsub|\<chi\><rsub|K>>>=\<b-T\>>,
  the same <math|A<rsub|\<beta\><rsub|\<chi\><rsub|K>>>\<neq\>\<b-T\>> may be
  introduced in consecutive iterations. This is not the case for invariants,
  where <math|S<rsub|k><around*|(|\<chi\>|)>> and
  <math|S<rsub|k+1><around*|(|\<chi\>|)>> differ by the portion
  <math|A<rsub|\<beta\><rsub|\<chi\>>>> of abduction answer.

  We introduced the <verbatim|assert false> construct into the programming
  language to indicate that a branch of code should not be reached. Type
  inference generates for it the logical connective <math|\<b-F\>>
  (falsehood). We partition the implication branches
  <math|D<rsub|i>,C<rsub|i>> into <math|<around*|{|D<rsub|i>,C<rsub|i><mid|\|>\<b-F\>\<nin\>C<rsub|i>|}>>
  which are fed to the algorithm and <math|<around*|{|D<rsub|j><rsup|->|}>=<around*|{|D<rsub|i><mid|\|>\<b-F\>\<in\>C<rsub|i>|}>>.
  After the main algorithm ends we check that for each
  <math|D<rsub|j><rsup|->>, \ <math|S<rsub|k><around*|(|D<rsub|i>|)>> fails.
  Optionally, but by default, we perform the check in each iteration,
  starting from third, i.e. <verbatim|iter_no\<gtr\>1>. Turning this option
  <em|on> gives a way to express negative constraints for the term domain.
  The option should be turned <em|off> when a single iteration (plus fallback
  backtracking described below) is insufficient to solve for the invariants.
  Moreover, for domains with negation elimination, i.e. the numerical domain,
  we incorporate negative constraints as described in section
  <reference|NegElim>. The corresponding computation is
  <math|A<rsub|0>\<wedge\><rsub|j>NegElim<around*|(|\<neg\>Simpl<around*|(|FV<around*|(|D<rsub|j><rsup|->|)>\\<wide|<wide|\<beta\>|\<bar\>><rsup|\<chi\>>|\<bar\>>.D<rsub|j><rsup|->|)>,<wide|D<rsub|i>,C<rsub|i>|\<bar\>>|)>>
  in the specification of the main algorithm. The simplification reduces the
  number of atoms in the formula and keeps those that are most relevant to
  finding invariants and postconditions. For convenience, negation
  elimination is called from the <verbatim|Abduction.abd> function, which
  returns <math|\<exists\><wide|\<alpha\>|\<bar\>>.A>.

  We implement backtracking using a tabu-search-like discard list. When
  abduction raises an exception: for example contradiction arises in the
  branches <math|S<rsub|k><around*|(|\<Phi\>|)>> passed to it, or it cannot
  find an answer and raises <verbatim|Suspect> with information on potential
  problem, we fall-back to step <math|k-1>. Similarly, with checking for
  negative constraints <em|on>, when the check of negative branches
  <math|<around*|(|D<rsub|i>,C<rsub|i>|)>\<in\>\<Phi\><rsub|\<b-F\>>>,
  \ <math|\<cal-M\>\<nvDash\>\<exists\>FV<around*|(|S<rsub|k><around*|(|D<rsub|i>|)>|)>.S<rsub|k><around*|(|D<rsub|i>|)>>
  fails. In step <math|k-1>, we maintain a discard list of different answers
  found in this step: initially empty, after fall-back we add there the
  latest answer. We redo step <math|k-1> starting from
  <math|S<rsub|k-1><around*|(|\<Phi\>|)>>. Infinite loop is avoided because
  answers already attempted are discarded. When step <math|k-1> cannot find a
  new answer, we fall back to step <math|k-2>, etc. We store discard lists
  for distinct sorts separately and we only add to the discard list of the
  sort that caused fallback. Unfortunately this means a slight loss of
  completeness, as an error in another sort might be due to bad choice in the
  sort of types. The loss is ``slight'' because of the dissociation step
  described previously. Moreover, the sort information from checking negative
  branches is likewise only approximate.

  <subsection|Stages of iteration>

  Changes in the algorithm between iterations were mentioned above but not
  clearly exposed. Invariant inference and postcondition inference go through
  similar stages. Abduction solves for invariants and helps solve for
  postconditions:

  <\enumerate>
    <item><math|j<rsub|0>\<leqslant\>k\<less\>j<rsub|2>> Only term abduction
    -- invariants of type shapes -- is performed, for all branches.

    <item><math|k\<less\>j<rsub|1>> Do not perform abduction for
    postconditions. Remove atoms with variables containing postcondition
    parameters from conclusions sent to abduction.

    <item><math|j<rsub|2>\<leqslant\>k\<less\>j<rsub|3>> Both term abduction
    and numerical abduction are performed, but numerical abduction only for
    non-recursive branches.

    <item><math|j<rsub|3>\<leqslant\>k> Abduction is performed on all
    branches -- type and numerical invariants are found.
  </enumerate>

  Default settings is <math|<around*|[|j<rsub|0>;j<rsub|1>;j<rsub|2>;j<rsub|3>|]>=<around*|[|0;1;1;2|]>>.
  <math|j<rsub|1>> is not tied to <math|j<rsub|0>,j<rsub|2>,j<rsub|3>>. We
  have options: <verbatim|early_postcond_abd> and
  <verbatim|early_num_abduction> that set <math|j<rsub|1>=0> and
  <math|j<rsub|3>=1> respectively. In a single iteration, disjunction
  elimination precedes abduction.

  <\enumerate>
    <item><math|k<rsub|0>\<leqslant\>k\<less\>k<rsub|1>> Term disjunction
    elimination -- invariants of type shapes -- is performed, only for
    non-recursive branches.

    <item><math|k<rsub|1>\<leqslant\>k\<less\>k<rsub|2>> Both term and
    numerical disjunction elimination are performed, but only for
    non-recursive branches.

    <item><math|k<rsub|2>\<leqslant\>k\<less\>k<rsub|3>> Disjunction
    elimination is performed on all branches -- type and numerical
    postconditions are found.

    <item><math|k<rsub|3>\<leqslant\>k> Additionally, we enforce convergence
    by intersecting the result with the previous-iteration result.
  </enumerate>

  Our current choice of parameters is <math|<around*|[|k<rsub|0>;k<rsub|1>;k<rsub|2>;k<rsub|3>|]>=<around*|[|0;0;2;5|]>>.
  We have an option <verbatim|converge_at> for setting <math|k<rsub|3>>.

  When existential types are used, the expected number of iterations is
  <math|k=5> (six iterations), because the last iteration needs to verify
  that the last-but-one iteration has found the correct answer. The minimal
  number of iterations is <math|k=2> (three iterations), so that all branches
  are considered.

  <subsection|Implementation details><label|Details>

  We represent <math|<wide|\<alpha\>|\<vect\>>> as a tuple type rather than
  as a function type. We modify the quantifier <math|\<cal-Q\>> imperatively,
  because it mostly grows monotonically, and when variables are dropped they
  do not conflict with fresh variables generated later.

  The code that selects <math|\<wedge\><rsub|\<chi\>><around*|(|A<rsub|\<chi\>><rsup|+>\<subset\>A<rsub|\<chi\>><rsup|1>|)>\<wedge\>\<cal-M\>\<vDash\>\<cal-Q\>.A\<setminus\>\<cup\><rsub|\<chi\>>A<rsub|\<chi\>><rsup|+>>
  is an incremental validity checker. It starts with
  <math|A\<setminus\>\<cup\><rsub|\<chi\>>A<rsub|\<chi\>><rsup|1>> and tries
  to add as many atoms <math|c\<in\>\<cup\><rsub|\<chi\>>A<rsub|\<chi\>><rsup|1>>
  as possible to what in effect becomes <math|A<rsub|res>>.

  We count the number of iterations of the main loop, a fallback decreases
  the iteration number to the previous value. The main loop decides whether
  multisort abduction should dissociate alien subterms -- in the first
  iteration of the loop -- or should perform abductions for other sorts -- in
  subsequent iteration. See discussion in subsection
  <reference|AlienSubterms>. In the first two iterations, we remove branches
  that contain unary predicate variables in the conclusion (or binary
  predicate variables in the premise, keeping only <verbatim|nonrec>
  branches), as discussed at the end of subsection <reference|SCAlinear> and
  beginning of subsection <reference|NumConv>. As discussed in subsection
  <reference|NumConv>, starting from iteration <math|k<rsub|3>>, we enforce
  convergence on solutions for binary predicate variables.

  Computing abduction is the ``axis'' of the main loop. If anything fails,
  the previous abduction answer is the culprit. We add the previous answer to
  the discard list and retry, without incrementing the iteration number. If
  abduction and splitting succeeds, we reset the discard list and increment
  the iteration number. We use recursion for backtracking, instead of making
  <verbatim|loop> tail-recursive.

  <section|Generating OCaml/Haskell Source and Interface Code>

  We have a single basis from which to generate all generated output files:
  <verbatim|.gadti>, <verbatim|.ml>, and in the future <verbatim|.hs> --
  <verbatim|annot_item>. It contains a superset of information in
  <verbatim|struct_item>: type scheme annotations on introduced names, and
  source code annotated with type schemes at recursive definition nodes. We
  use <verbatim|type a.> syntax instead of <verbatim|'a.> syntax because the
  former supports inference for GADTs in OCaml. A benefit of the nicer
  <verbatim|type a.> syntax is that nested type schemes can have free
  variables, which will be correctly captured by the outer type scheme. For
  completeness we sometimes need to annotate all <verbatim|function> nodes
  with types. To avoid clutter, we start by only annotating <verbatim|let
  rec> nodes, and in case <verbatim|ocamlc -c> fails on generated code, we
  re-annotate by putting type schemes on <verbatim|let rec> nodes and types
  on <verbatim|function> nodes. If need arises, <verbatim|let-in> node
  annotations can also be introduced in this fallback -- the corresponding
  <verbatim|Lam> constructors store the types. We provide an option to
  annotate the definitions on <verbatim|let-in> nodes. Type annotations are
  optional because they introduce a slight burden on the solver -- the
  corresponding variables cannot be removed by the initial simplification of
  the constraints, in <verbatim|Infer>. <verbatim|let-in> node annotations
  are more burdensome than <verbatim|function> node annotations.

  Annotated items <verbatim|annot_item> use ``nice'' named variables instead
  of identifier-based variables. The renaming is computed by
  <verbatim|nice_ans>, called at the toplevel and at each <verbatim|let rec>
  in the source code.

  In the signature declarations <verbatim|ITypConstr> and
  <verbatim|IValConstr> for existential types, we replace <verbatim|Extype>
  with <verbatim|CNam> as indentifiers of constructors, to get informative
  output for printing the various result files. We print constraint formulas
  and alien subterms in the original InvarGenT syntax, commented out.

  The types <verbatim|Int>, <verbatim|Num> and <verbatim|Bool> should be
  considered built-in. <verbatim|Int> and <verbatim|Bool> follow the general
  scheme of exporting a datatype constructor with the same name, only
  lower-case. However, numerals <verbatim|0>, <verbatim|1>, ... are always
  type-checked as <verbatim|Num 0>, <verbatim|Num 1>... A parameter
  <verbatim|-num_is> decides the type alias definition added in the generated
  code: <verbatim|-num_is bar> adds <verbatim|type num = bar> in front of an
  <verbatim|.ml> file, by default <verbatim|int>. Numerals are exported as
  integers passed to a <verbatim|bar_of_int> function. The variant
  <verbatim|-num_is_mod> exports numerals by passing to a
  <verbatim|Bar.of_int> function. Special treatment for <verbatim|Bool>
  amounts to exporting <verbatim|True> and <verbatim|False> as
  <verbatim|true> and <verbatim|false>, unlike other constants. In addition,
  pattern matching <verbatim|match <math|\<ldots\>> with True -\<gtr\>
  <math|\<ldots\>> \| False -\<gtr\> <math|\<ldots\>>>, i.e. the
  corresponding beta-redex, is exported as <verbatim|if <math|\<ldots\>> then
  <math|\<ldots\>> else <math|\<ldots\>>>.

  In declarations <verbatim|PrimVal>, which have concrete syntax starting
  with the word <verbatim|external>, we provide names assumed to have given
  type scheme. The syntax has two variants, differing in the way the
  declaration is exported. It can be either an <verbatim|external>
  declaration in OCaml, which is the binding mechanism of the <em|foreign
  function interface>. But in the InvarGenT form <verbatim|external let>, the
  declaration provides an OCaml definition, which is exported as the toplevel
  <verbatim|let> definition of OCaml. It has the benefit that the OCaml
  compiler will verify this definition, since InvarGenT calls
  <verbatim|ocamlc -c> to verify the exported code.
</body>

<\initial>
  <\collection>
    <associate|info-flag|minimal>
    <associate|sfactor|4>
  </collection>
</initial>

<\references>
  <\collection>
    <associate|1|<tuple|5.2|?>>
    <associate|AlienSubterms|<tuple|3.3|9>>
    <associate|Details|<tuple|6.5|20>>
    <associate|ImplSubst|<tuple|4|2>>
    <associate|Main Algo|<tuple|5.3|?>>
    <associate|MainAlgo|<tuple|6|15>>
    <associate|MainAlgoBody|<tuple|6.3|18>>
    <associate|NegElim|<tuple|4.4|?>>
    <associate|NumConv|<tuple|4.2|12>>
    <associate|OptiAtoms|<tuple|5|?>>
    <associate|Rg|<tuple|4|18>>
    <associate|SCAlinear|<tuple|3.4|9>>
    <associate|SepProp|<tuple|5|3>>
    <associate|SepProp2|<tuple|6|?>>
    <associate|Skp|<tuple|1|18>>
    <associate|Skp1|<tuple|9|19>>
    <associate|SolSimpl|<tuple|9|12>>
    <associate|SolvedForm|<tuple|4|?>>
    <associate|SolvedFormProj|<tuple|7|?>>
    <associate|auto-1|<tuple|1|1>>
    <associate|auto-10|<tuple|3.3|9>>
    <associate|auto-11|<tuple|3.4|9>>
    <associate|auto-12|<tuple|4|11>>
    <associate|auto-13|<tuple|4.1|11>>
    <associate|auto-14|<tuple|4.2|12>>
    <associate|auto-15|<tuple|4.3|12>>
    <associate|auto-16|<tuple|4.4|14>>
    <associate|auto-17|<tuple|5|14>>
    <associate|auto-18|<tuple|5.1|15>>
    <associate|auto-19|<tuple|5.2|15>>
    <associate|auto-2|<tuple|2|3>>
    <associate|auto-20|<tuple|5.3|15>>
    <associate|auto-21|<tuple|6|15>>
    <associate|auto-22|<tuple|6.1|16>>
    <associate|auto-23|<tuple|6.2|18>>
    <associate|auto-24|<tuple|6.3|20>>
    <associate|auto-25|<tuple|6.4|20>>
    <associate|auto-26|<tuple|6.5|21>>
    <associate|auto-27|<tuple|7|21>>
    <associate|auto-3|<tuple|2.1|4>>
    <associate|auto-4|<tuple|2.1.1|5>>
    <associate|auto-5|<tuple|2.2|5>>
    <associate|auto-6|<tuple|3|5>>
    <associate|auto-7|<tuple|3.1|6>>
    <associate|auto-8|<tuple|3.1.1|8>>
    <associate|auto-9|<tuple|3.2|8>>
    <associate|bib-AbductionSolvMaher|<tuple|3|21>>
    <associate|bib-AntiUnifAlg|<tuple|9|21>>
    <associate|bib-AntiUnifInv|<tuple|2|4>>
    <associate|bib-AntiUnifPlotkin|<tuple|4|4>>
    <associate|bib-AntiUnifReynolds|<tuple|5|4>>
    <associate|bib-ArithQuantElim|<tuple|1|21>>
    <associate|bib-ConvexHull|<tuple|2|21>>
    <associate|bib-DBLP:conf/cccg/2000|<tuple|3|?>>
    <associate|bib-ESOP2014|<tuple|8|21>>
    <associate|bib-UnificationBaader|<tuple|1|4>>
    <associate|bib-disjelimTechRep|<tuple|5|21>>
    <associate|bib-invariantsTechRep2|<tuple|6|21>>
    <associate|bib-jcaqpTechRep|<tuple|8|4>>
    <associate|bib-jcaqpTechRep2|<tuple|7|21>>
    <associate|bib-jcaqpUNIF|<tuple|4|21>>
    <associate|bib-simonet-pottier-hmg-toplas|<tuple|6|4>>
    <associate|bib-systemTechRep|<tuple|5|18>>
  </collection>
</references>

<\auxiliary>
  <\collection>
    <\associate|bib>
      AbductionSolvMaher

      PracticalGADTsInfer

      AbductionSolvMaher

      ArithQuantElim

      ArithQuantElim

      AntiUnifAlg

      ConvexHull

      ConvexHull
    </associate>
    <\associate|toc>
      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|1<space|2spc>Data
      Structures and Concrete Syntax> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-1><vspace|0.5fn>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|2<space|2spc>Generating
      and Normalizing Formulas> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-2><vspace|0.5fn>

      <with|par-left|<quote|1.5fn>|2.1<space|2spc>Normalization
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-3>>

      <with|par-left|<quote|3fn>|2.1.1<space|2spc>Implementation details
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-4>>

      <with|par-left|<quote|1.5fn>|2.2<space|2spc>Simplification
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-5>>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|3<space|2spc>Abduction>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-6><vspace|0.5fn>

      <with|par-left|<quote|1.5fn>|3.1<space|2spc>Simple constraint abduction
      for terms <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-7>>

      <with|par-left|<quote|3fn>|3.1.1<space|2spc>Heuristic for better
      answers to invariants <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-8>>

      <with|par-left|<quote|1.5fn>|3.2<space|2spc>Joint constraint abduction
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-9>>

      <with|par-left|<quote|1.5fn>|3.3<space|2spc>Abduction for terms with
      Alien Subterms <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-10>>

      <with|par-left|<quote|1.5fn>|3.4<space|2spc>Simple constraint abduction
      for linear arithmetics <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-11>>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|4<space|2spc>Constraint
      Generalization> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-12><vspace|0.5fn>

      <with|par-left|<quote|1.5fn>|4.1<space|2spc>Extended convex hull
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-13>>

      <with|par-left|<quote|1.5fn>|4.2<space|2spc>Issues in inferring
      postconditions <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-14>>

      <with|par-left|<quote|1.5fn>|4.3<space|2spc>Abductive disjunction
      elimination given quantifier prefix
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-15>>

      <with|par-left|<quote|1.5fn>|4.4<space|2spc>Incorporating negative
      constraints <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-16>>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|5<space|2spc><with|font-shape|<quote|italic>|opti>
      and <with|font-shape|<quote|italic>|subopti>:
      <with|font-shape|<quote|italic>|minimum> and
      <with|font-shape|<quote|italic>|maximum> relations in
      <with|font-family|<quote|tt>|language|<quote|verbatim>|num>>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-17><vspace|0.5fn>

      <with|par-left|<quote|1.5fn>|5.1<space|2spc>Normalization, validity and
      implication checking <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-18>>

      <with|par-left|<quote|1.5fn>|5.2<space|2spc>Abduction
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-19>>

      <with|par-left|<quote|1.5fn>|5.3<space|2spc>Disjunction elimination
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-20>>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|6<space|2spc>Solving
      for Predicate Variables> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-21><vspace|0.5fn>

      <with|par-left|<quote|1.5fn>|6.1<space|2spc>Invariant Parameter
      Candidates <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-22>>

      <with|par-left|<quote|1.5fn>|6.2<space|2spc>Solving for Predicates in
      Negative Positions <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-23>>

      <with|par-left|<quote|1.5fn>|6.3<space|2spc>Solving for Existential
      Types Predicates and Main Algorithm
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-24>>

      <with|par-left|<quote|1.5fn>|6.4<space|2spc>Stages of iteration
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-25>>

      <with|par-left|<quote|1.5fn>|6.5<space|2spc>Implementation details
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-26>>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|7<space|2spc>Generating
      OCaml/Haskell Source and Interface Code>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-27><vspace|0.5fn>
    </associate>
  </collection>
</auxiliary>