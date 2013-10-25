<TeXmacs|1.0.7.19>

<style|article>

<\body>
  <doc-data|<doc-title|InvarGenT: Implementation>||<doc-author|<author-data|<author-name|Šukasz
  Stafiniak>|<\author-affiliation>
    Institute of Computer Science

    University of Wrocªaw
  </author-affiliation>>>>

  <\abstract>
    InvarGenT is a proof-of-concept system for invariant generation by full
    type inference with Guarded Algebraic Data Types and existential types
    encoded as automatically generated GADTs. This implementation
    documentation focuses on source code, refers to separate technical
    reports on theory and algorithms.
  </abstract>

  <section|Data Structures and Concrete Syntax>

  Following <cite|ESOP2014>, we have the following nodes in the abstract
  syntax of patterns and expressions:

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
  after parsing.

  <block|<tformat|<cwith|1|1|2|2|cell-halign|c>|<cwith|1|1|1|1|cell-halign|l>|<cwith|2|2|2|2|cell-halign|c>|<cwith|2|2|1|1|cell-halign|l>|<table|<row|<cell|type
  variable: types>|<cell|<math|\<alpha\>,\<beta\>,\<gamma\>,\<tau\>>>|<cell|<verbatim|a>,<verbatim|b>,<verbatim|c>,<verbatim|r>,<verbatim|s>,<verbatim|t>,<verbatim|a1>,...>|<cell|>|<cell|<tiny|<verbatim|TVar(VNam(Type_sort,>...<verbatim|))>>>>|<row|<cell|type
  variable: nums>|<cell|<math|k,m,n>>|<cell|<verbatim|i>,<verbatim|j>,<verbatim|k>,<verbatim|l>,<verbatim|m>,<verbatim|n>,<verbatim|i1>,...>|<cell|>|<cell|<tiny|<verbatim|TVar(VNam(Num_sort,>...<verbatim|))>>>>|<row|<cell|type
  constructor>|<cell|<math|List>>|<cell|<verbatim|List>>|<cell|>|<cell|<verbatim|TCons(CNamed>...<verbatim|)>>>|<row|<cell|number
  (type)>|<cell|<math|7>>|<cell|<verbatim|7>>|<cell|>|<cell|<verbatim|NCst>>>|<row|<cell|numeral
  (expr.)>|<cell|<math|7>>|<cell|<verbatim|7>>|<cell|>|<cell|<verbatim|Num>>>|<row|<cell|numerical
  sum (type)>|<cell|<math|m+n>>|<cell|<verbatim|m+n>>|<cell|>|<cell|<verbatim|Nadd>>>|<row|<cell|existential
  type>|<cell|<math|\<exists\>k,n<around*|[|k\<leqslant\>n|]>.\<tau\>>>|<cell|<verbatim|ex
  k n [k\<less\>=n].t>>|<cell|<verbatim|<math|\<exists\>>k,n[k<math|\<leq\>>n].t>>|<cell|<verbatim|TCons(Extype>...<verbatim|)>>>|<row|<cell|type
  sort>|<cell|<math|s<rsub|ty>>>|<cell|<verbatim|type>>|<cell|>|<cell|<verbatim|Type_sort>>>|<row|<cell|number
  sort>|<cell|<math|s<rsub|R>>>|<cell|<verbatim|num>>|<cell|>|<cell|<verbatim|Num_sort>>>|<row|<cell|function
  type>|<cell|<math|\<tau\><rsub|1>\<rightarrow\>\<tau\><rsub|2>>>|<cell|<verbatim|t1
  -\<gtr\> t2>>|<cell|<verbatim|t1 <math|\<rightarrow\>><verbatim|
  t2>>>|<cell|<verbatim|Fun>>>|<row|<cell|equation>|<cell|<math|a<wide|=|\<dot\>>b>>|<cell|<verbatim|a
  = b>>|<cell|>|<cell|<verbatim|Eqty>>>|<row|<cell|inequation>|<cell|<math|k\<leqslant\>n>>|<cell|<verbatim|k
  \<less\>= n>>|<cell|<verbatim|k <math|\<leq\>>
  n>>|<cell|<verbatim|Leq>>>|<row|<cell|conjunction>|<cell|<math|\<varphi\><rsub|1>\<wedge\>\<varphi\><rsub|2>>>|<cell|<verbatim|a=b
  && b=a>>|<cell|<verbatim|a=b <math|\<wedge\>> b=a>>|<cell|built-in
  lists>>>>>

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
  constructor>|<cell|<verbatim|newtype List : type *
  num>>|<cell|<verbatim|TypConstr>>>|<row|<cell|value
  constructor>|<cell|<verbatim|newcons Cons : all n a. a * List(a,n)
  --\<gtr\> List(a,n+1)>>|<cell|<verbatim|ValConstr>>>|<row|<cell|>|<cell|<verbatim|newcons
  Cons : <math|\<forall\>>n,a. a * List(a,n) <math|\<longrightarrow\>>
  List(a,n+1)>>|<cell|>>|<row|<cell|declaration>|<cell|<verbatim|external
  filter : <math|\<forall\>>n,a. List(a,n)<math|\<rightarrow\>
  \<exists\>>k[k\<less\>=n].List(a,k)>>|<cell|<verbatim|PrimVal>>>|<row|<cell|rec.
  definition>|<cell|<verbatim|let rec f =>...>|<cell|<verbatim|LetRecVal>>>|<row|<cell|non-rec.
  definition>|<cell|<verbatim|let v =>...>|<cell|<verbatim|LetVal>>>>>>

  For simplicity of theory and implementation, mutual non-nested recursion
  and or-patterns are not provided. For mutual recursion, nest one recursive
  definition inside another.

  <section|Generating and Normalizing Formulas>

  We inject the existential type and value constructors during parsing for
  user-provided existential types, and during constraint generation for
  inferred existential types, into the list of toplevel items. It faciliates
  exporting inference results as OCaml source code.

  Functions <verbatim|constr_gen_pat> and <verbatim|envfrag_gen_pat> compute
  formulas according to table [?] in <cite|ESOP2014>, and
  <verbatim|constr_gen_expr> computes table [?]. Due to the presentation of
  the type system, we ensure in <verbatim|ValConstr> that bounds on type
  parameters are introduced in the formula rather than being substituted into
  the result type. We preserve the FOL language presentation in the type
  <verbatim|cnstrnt>, only limiting the expressivity in ways not requiring
  any preprocessing. The toplevel definitions (from type
  <verbatim|struct_item>) <verbatim|LetRecVal> and <verbatim|LetVal> are
  processed by <verbatim|constr_gen_letrec> and <verbatim|constr_gen_let>
  respectively. They are analogous to <verbatim|Letrec> and <verbatim|Letin>
  or a <verbatim|Lam> clause. We do not cover toplevel definitions in our
  formalism (without even a rudimentary module system, the toplevel is a
  matter of pragmatics rather than semantics).

  Toplevel definitions are intended as boundaries for constraint solving.
  This way the programmer can decompose functions that could be too complex
  for the solver. <verbatim|LetRecVal> only binds a single identifier, while
  <verbatim|LetVal> binds variables in a pattern. To preserve the flexibility
  of expression-level pattern matching, <verbatim|LetVal> has to pack the
  constraints <math|<around*|\<llbracket\>|\<Sigma\>\<vdash\>p\<uparrow\>\<alpha\>|\<rrbracket\>>>
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
  clauses are: <verbatim|assert = type e1 e2> which translates as equality of
  types of <verbatim|e1> and <verbatim|e2>, <verbatim|assert false> which
  translates as <verbatim|CFalse>, and <verbatim|assert e1 \<less\>= e2>,
  which translates as inequality <math|n<rsub|1>\<leqslant\>n<rsub|2>>
  assuming that <verbatim|e1> has type <verbatim|Num n1> and <verbatim|e2>
  has type <verbatim|Num n2>.

  We treat a chain of single branch functions with only <verbatim|assert
  false> in the body of the last function specially. We put all information
  about the type of the functions in the premise of the generated constraint.
  Therefore the user can use them to exclude unintended types. See the
  example <verbatim|equal_assert.gadt>.

  We make a slight adjustment to constraints
  <math|<around*|\<llbracket\>|\<Gamma\>\<vdash\>K
  p.e<rsub|2>:\<alpha\><rsub|0>\<rightarrow\>\<tau\>|\<rrbracket\>>>
  generated for eliminating an existential type
  <math|\<varepsilon\><rsub|K><around*|(|\<alpha\>|)>> to be inferred, by
  adding a semantically redundant atom <math|v<rsub|K><around*|(|\<alpha\>|)>>
  needed by the solver. Symbolically, <math|<around*|\<llbracket\>|\<vdash\>K
  p\<downarrow\>\<tau\><around*|\<rrbracket\>||\<nobracket\>>|\<nobracket\>>=\<exists\>\<alpha\><rprime|'>.\<varepsilon\><rsub|K><around*|(|\<alpha\><rprime|'>|)><wide|=|\<dot\>>\<tau\>\<wedge\>v<rsub|K><around*|(|\<alpha\><rprime|'>|)>\<wedge\>\<ldots\>>
  in such cases. We use <verbatim|PredVarU> for <math|v<rsub|K>> for
  parsimony, but do not write <math|\<chi\><rsub|K><around*|(|\<cdummy\>|)>>
  to avoid confusion with invariants and with
  <math|\<chi\><rsub|K><around*|(|\<cdummy\>,\<cdummy\>|)>>.

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
  (<verbatim|step\<gtr\>0>), we return it. Otherwise we return the filtered
  disjunction. <verbatim|prepare_brs> cleans up the initial flattened
  constraints or the constraints released from disjunctions: it calls
  <verbatim|simplify_brs> on implications and <verbatim|flat_dsj> on each
  disjunction.

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
  might need refining. We merge implications with the same premise.

  <section|Abduction>

  The formal specification of abduction in <cite|jcaqpUNIF> provides a scheme
  for combining sorts that substitutes number sort subterms from type sort
  terms with variables, so that a single-sort term abduction algorithm can be
  called. Since we implement term abduction over the two-sorted datatype
  <verbatim|typ>, we keep these <em|alien subterms> in terms passed to term
  abduction.

  <subsection|Simple constraint abduction for terms>

  Our initial implementation of simple constraint abduction for terms follows
  <cite|AbductionSolvMaher> p. 13. The mentioned algorithm only gives
  <em|fully maximal answers> which is loss of generality w.r.t. our
  requirements. To solve <math|D\<Rightarrow\>C> the algorithm starts with
  with <math|\<b-U\><around*|(|D\<wedge\>C|)>> and iteratively replaces
  subterms by fresh variables <math|\<alpha\>\<in\><wide|\<alpha\>|\<bar\>>>
  for a final solution <math|\<exists\><wide|\<alpha\>|\<bar\>>.A>. To
  mitigate some of the limitations of fully maximal answers, we start from
  <math|\<b-U\><rsub|><around*|(|D\<wedge\>A\<wedge\>C|)>>, where
  <math|\<exists\><wide|\<alpha\>|\<bar\>>.A> is the solution to previous
  problems solved by the joint abduction algorithm, and
  <math|A<around*|(|\<cdummy\>|)>> is the corresponding substitution. During
  abduction <math|Abd<around*|(|\<cal-Q\>,<wide|\<zeta\>|\<bar\>>,<wide|D<rsub|i>,C<rsub|i>|\<bar\>>|)>>,
  we ensure that the (partial as well as final) answer
  <math|\<exists\><wide|\<alpha\>|\<bar\>>.A> satisfies
  <math|\<vDash\>\<cal-Q\>.A<around*|[|<wide|\<alpha\>|\<bar\>><wide|\<zeta\>|\<bar\>>\<assign\><wide|t|\<bar\>>|]>>
  for some <math|<wide|t|\<bar\>>>. We achieve this by normalizing the answer
  using parameterized unification under quantifiers
  <math|\<b-U\><rsub|<wide|\<alpha\>|\<bar\>><wide|\<zeta\>|\<bar\>>><around*|(|\<cal-Q\>.A|)>>.
  <math|<wide|\<zeta\>|\<bar\>>> are potential parameters of the invariants.

  In fact, when performing unification, we check more than
  <math|\<b-U\><rsub|<wide|\<alpha\>|\<bar\>><wide|\<zeta\>|\<bar\>>><around*|(|\<cal-Q\>.A|)>>
  requires. We also ensure that the use of already found parameters
  (represented by <math|<wide|\<beta\><rsub|\<chi\>><wide|\<beta\><rsup|>|\<bar\>><rsup|\<chi\>>|\<bar\>>>
  in the main algorithm) will not cause problems in the <verbatim|split>
  phase of the main algorithm.

  In implementing <cite|AbductionSolvMaher> p. 13, we follow top-down
  approach where bigger subterms are abstracted first -- replaced by fresh
  variable, \ together with an arbitrary selection of other occurrences of
  the subterm. If dropping the candidate atom maintains
  <math|T<around*|(|F|)>\<vDash\>A\<wedge\>D\<Rightarrow\>C>, we proceed to
  neighboring subterm or next equation. Otherwise, we try all of: replacing
  the subterm by the fresh variable; proceeding to subterms of the subterm;
  preserving the subterm; replacing the subterm by variables corresponding to
  earlier occurrences of the subterm. This results in a single, branching
  pass over all subterms considered. TODO: avoiding branching when
  implication holds might lead to another loss of generality, does it?
  Finally, we clean up the solution by eliminating fresh variables when
  possible (i.e. substituting-out equations <math|x<wide|=|\<dot\>>\<alpha\>>
  for variable <math|x> and fresh variable <math|\<alpha\>>).

  Although there could be an infinite number of abduction answers, there is
  always finite number of <em|fully maximal> answers, one of which we
  compute. We use a search scheme that tests as soon as possible. The simple
  abduction algorithm takes a partial solution -- a conjunction of candidate
  solutions for some other branches -- and checks if the solution being
  generated is satisfiable together with the candidate partial solution. The
  algorithm also takes several indicators to let it select the expected
  answer:

  <\itemize>
    <item>a number that determines how many correct solutions to skip;

    <item>a validation procedure that checks whether the partial answer meets
    a condition, in joint abduction the condition is consistency with premise
    and conclusion of each branch;

    <item>the initial parameters of the invariants (represented by
    <math|<wide|\<beta\><rsub|\<chi\>><wide|\<beta\><rsup|>|\<bar\>><rsup|\<chi\>>|\<bar\>>>
    in the main algorithm) to which all variables of every atom in the answer
    for which <math|FV<around*|(|c|)>\<cap\><wide|\<zeta\>|\<bar\>>\<neq\>\<varnothing\>>
    should be <em|connected>;

    <item>the quantifier <math|\<cal-Q\>> (source <verbatim|q>) so that the
    partial answer <math|\<exists\><wide|\<alpha\>|\<bar\>>.A> (source
    <verbatim|vs,ans>) can be checked for validity with parameters:
    <math|\<vDash\>\<cal-Q\>.A<around*|[|<wide|\<alpha\>|\<bar\>>\<assign\><wide|t|\<bar\>>|]>>
    for some <math|<wide|t|\<bar\>>>;

    <item>a discard list of partial answers to avoid (a tabu list) --
    implements backtracking, with answers from abductions raising
    ``fallback'' going there.
  </itemize>

  To ensure connected variables condition, if an atom
  <math|FV<around*|(|c|)>\<cap\><wide|\<zeta\>|\<bar\>>\<neq\>\<varnothing\>>,
  we only add it to the answer if it contains a connected variable, and since
  then count all its <math|FV<around*|(|c|)>\<cap\><wide|\<zeta\>|\<bar\>>>
  variables as connected. The initially connected variables are the initial
  parameters \ of the invariants. If such atom does not have a connected
  variable, we move it through the candidates past an atom that would make it
  connected. If none would, we drop the atom. In terms of the notation from
  the main algorithm, every <math|<wide|\<zeta\>|\<bar\>><rsup|\<chi\>>> atom
  of the answer has to be connected to a <math|\<beta\><rsub|\<chi\>><wide|\<beta\>|\<bar\>><rsup|\<chi\>>>
  atom using only the atoms in the answer.

  To recapitulate, the implementation is:

  <\itemize>
    <item><verbatim|abstract> is the entry point.

    <item>If <verbatim|cand=[]> -- no more candidates to add to the partial
    solution: check for repeated answers, skipping, and discarded answers.

    <item>Otherwise, pick the next atom and check if it's connected, if no,
    loop with reordered candidates (possibly without the atom).

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

      <item>Keep a variant of the original atom, but with universal variables
      and constants substituted-out. Redundant, and optional: only when
      <verbatim|more_general> is false.
    </enumerate>

    <item>Choices 2-6 are guarded by <verbatim|try>-<verbatim|with>, as tests
    raise <verbatim|Contradiction> if they fail, choice 1 only tests
    <verbatim|implies_concl> which returns a boolean.

    <item>We provide an option <verbatim|more_general>, which when set to
    false reorders the choices into: 1, 6, 4, 2, 3, 5 -- pushing 4 up
    minimizes the amount of branching in 5.

    <item>Recompute modifications of parameters due to partial answer, e.g.
    <verbatim|cparams>, for clarity of joint constraint abduction; we could
    compute them incrementally and pass around.

    <item>Form initial candidates <math|\<b-U\><rsub|><around*|(|D\<wedge\>A\<wedge\>C|)>>.
    Revert substitutions <math|\<alpha\>\<assign\>\<beta\>> for
    <math|\<forall\>\<beta\>\<in\>\<cal-Q\>> and
    <math|\<exists\>\<alpha\>\<in\>\<cal-Q\>> to
    <math|\<beta\>\<assign\>\<alpha\>>. This optimization mitigates
    quantifier violations later, although excludes
    <math|\<alpha\>\<assign\>\<beta\>> from direct participation in the
    answer.

    <\itemize>
      <item>Replace <math|\<alpha\><rsub|1>\<assign\>\<beta\>,\<ldots\>,\<alpha\><rsub|n>\<assign\>\<beta\>>
      with <math|\<beta\>\<assign\>\<alpha\><rsub|i>,\<alpha\><rsub|2>\<assign\>\<alpha\><rsub|i>,\<ldots\>,\<alpha\><rsub|n>\<assign\>\<alpha\><rsub|i>>
      where <math|\<alpha\><rsub|i>> is the most upstream existential
      variable, as in choice 6.
    </itemize>

    <item>Form the choice-6 counterparts of initial candidate atoms. Replace
    <math|\<alpha\><rsub|1>\<assign\>\<tau\>,\<ldots\>,\<alpha\><rsub|n>\<assign\>\<tau\>>
    with <math|\<tau\>\<assign\>\<alpha\><rsub|i>,\<alpha\><rsub|2>\<assign\>\<alpha\><rsub|i>,\<ldots\>,\<alpha\><rsub|n>\<assign\>\<alpha\><rsub|i>>
    where <math|\<alpha\><rsub|i>> is the most upstream existential variable
    and <math|\<tau\>> is a universal variable or constant.

    <item>Sort the initial candidates by decreasing size.
  </itemize>

  The above ordering of choices ensures that more general answers are tried
  first. Moreover:

  <\itemize>
    <item>choice 1 could be dropped as it is equivalent to choice 2 applied
    on the root term;

    <item>choices 4 and 5 could be reordered but having choice 4 as soon as
    possible is important for efficiency.
  </itemize>

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

  <subsection|Joint constraint abduction for terms>

  We further lose generality by using a heuristic search scheme instead of
  testing all combinations of simple abduction answers. In particular, our
  search scheme returns from joint abduction for types with a single answer,
  which eliminates deeper interaction between the sort of types and other
  sorts. Some amount of interaction is provided by the validation procedure,
  which checks for consistency of the partial answer, the premise and the
  conclusion of each branch, including consistency for other sorts.

  We maintain an ordering of branches. We accumulate simple abduction answers
  into the partial abduction answer until we meet branch that does not have
  any answer satisfiable with the partial answer so far. Then we start over,
  but put the branch that failed in front of the sequence. If a branch
  <math|i> is at front for <math|n<rsub|i>>th time, we skip the initial
  <math|n<rsub|i>-1> simple abduction answers in it. If no front branch
  <math|i> has at least <math|n<rsub|i>> answers, the search fails. After an
  answer working for all branches has been found, we perform additional
  check, which encapsulates negative constraints introduced by
  <verbatim|assert false> construct. If the check fails, we increase the skip
  count of the head branch and repeat the search.

  When a branch has no more solutions to offer -- its skip factor
  <math|n<rsub|i>> has reached the number of fully maximal solutions to that
  branch -- we move it to a separate <em|runouts> list and continue search
  starting from a different branch. We do not increase its skip factor, but
  we check the runouts directly after the first branch, so that conflicting
  branches can be located. When the first branch conflicts with the runouts,
  we increase its skip factor and repeat. We keep a count of conflicts for
  the runouts so that in case of overall failure, we can report a branch
  likely to be among those preventing abduction.

  We remember SCA answers when skipping over them, not to return the same
  answer for different skip factors. But we also remember all JCA partial
  answers that led to resetting. If a partial answer becomes as strong as one
  of them, we can reset without further checking. If an empty partial answer
  led to resetting, no answer exists. The failed partial answers are
  initialized with the discarded answers, passed from the main algorithm.

  As described in <cite|jcaqpTechRep2>, to check validity of answers, we use
  a modified variant of unification under quantifiers: unification with
  parameters, where the parameters do not interact with the quantifiers and
  thus can be freely used and eliminated. Note that to compute conjunction of
  the candidate answer with a premise, unification does not check for
  validity under quantifiers.

  Because it would be difficult to track other sort constraints while
  updating the partial answer, we discard numeric sort constraints in simple
  abduction algorithm, and recover them after the final answer for terms
  (i.e. for the type sort) is found.

  When searching for abduction answer fails, we raise exception
  <verbatim|Suspect> that contains the partial answer conjoined with
  conclusion of an implication that failed to produce an answer compatible
  with remaining implications.

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
  process at the end of <verbatim|ans_typ>. This process is needed regardless
  of the ``dissociation'' issue, to uncover the full content of numeric sort
  constraints.

  For efficiency, we use a slightly different approach. On the first
  iteration of the main algorithm, we dissociate alien subterms, but we do
  not perform other-sort abduction at all. On the next iteration, we do not
  perform dissociation, as we expect the dissociation in the partial answers
  (to predicate variables) from the first step to be sufficient. Other-sort
  abduction algorithms now have less work, because only a fraction of alien
  subterm variables <math|\<alpha\><rsub|s>> remain in the partial answers
  (see main algorithm in section <reference|MainAlgo>). They also have more
  information to work with, present in the instatiation of partial answers.

  <subsection|Simple constraint abduction for linear
  arithmetic><label|SCAlinear>

  We use <em|Fourier-Motzkin elimination>. To avoid complexities we only
  handle the rational number domain. To extend the algorithm to integers,
  <em|Omega-test> procedure as presented in <cite|ArithQuantElim> needs to be
  adapted. The major operations are:

  <\itemize>
    <item><em|Elimination> of a variable takes an equation and selects a
    variable that is not upstream of any other variable of the equation, and
    substitutes-out this variable from the rest of the constraint. The solved
    form contains an equation for this variable.

    <item><em|Projection> of a variable takes a variable <math|x> that isn't
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
  process.

  Our algorithm follows a familiar incrementally-generate-and-test scheme:

  <\enumerate>
    <item>Build a lazy list of possible transformations with linear
    combinations involving <math|a\<in\>D>.

    <\enumerate>
      <item>For equations <math|a>, add combinations <math|k<rsup|s>*a+b> for
      <math|k=-n\<ldots\>n,s=-1,1> to the stack of transformations to be
      tried for atoms <math|b\<in\>C>.

      <item>For inequalities <math|a>, add combinations <math|k<rsup|s>*a+b>
      for <math|k=0\<ldots\>n,s=-1,1> to the stack of trasformations to be
      tried only for inequalities <math|b\<in\>C>.
    </enumerate>

    <item>Start from <math|A\<assign\>C,Acc\<assign\><around*|{||}>>. Try
    atoms <math|A=a A<rprime|'>> in some order.

    <item>Let <math|B=A<rsub|i>\<wedge\>D\<wedge\>A<rprime|'>\<wedge\>Acc>.

    <item>If <math|B\<Rightarrow\>C>, repeat with
    <math|A\<assign\>A<rprime|'>>.

    <item>If <math|B\<nRightarrow\>C>, for a transformation
    <math|a<rprime|'>> of <math|a> which passes validation against other
    branches in a joint problem: <math|Acc\<assign\>Acc\<cup\><around*|{|a<rprime|'>|}>>,
    or fail if all <math|a<rprime|'>> fail.

    <\enumerate>
      <item>Let <math|a<rprime|'>> be <math|a> with some transformations
      applied.

      <item>If <math|A<rsub|i>\<wedge\><around*|(|Acc\<cup\><around*|{|a<rprime|'>|}>|)>>
      does not pass <verbatim|validate> for all <math|a<rprime|'>>, fail.

      <item>Optionally, if <math|A<rsub|i>\<wedge\><around*|(|Acc\<cup\><around*|{|a<rprime|'>|}>|)>>
      passes <verbatim|validate> for inequality <math|a>, add combinations to
      the stack of transformations as in step (1b).

      <item>If <math|A<rsub|i>\<wedge\><around*|(|Acc\<cup\><around*|{|a<rprime|'>|}>|)>>
      passes <verbatim|validate>, repeat with
      <math|A\<assign\>A<rprime|'>,Acc\<assign\>Acc\<cup\><around*|{|a<rprime|'>|}>>.
      (Choice point.)
    </enumerate>

    <item>The answers are <math|A<rsub|i+1>=A<rsub|i>\<wedge\>Acc>.
  </enumerate>

  Note that if an equation <math|a\<in\>Acc>, linear combinations with it
  <math|a+b\<wedge\>Acc> would remain equivalent to original
  <math|b\<wedge\>Acc>. For inequalities <math|a\<in\>Acc>, combinations
  <math|a+b\<wedge\>Acc> are weaker than <math|b\<wedge\>Acc>, thus the
  optional step (5c). We precompute the tranformation variants to try out.
  The parameter <math|n> is called <verbatim|abd_rotations> and defaults to a
  small value (2 or 3).

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

  Our algorithm finds only fully maximal answers. Unfortunately this means
  that for many invariant inference problems, some implication branches in
  initial steps of the main algorithm are insolvable. That is, when the
  instantiations of the invariants found so far are not informative enough,
  the expected answer of the JCA problem is not a fully maximal SCA answer to
  these branches. We mitigate this problem by removing, in the first call to
  numerical abduction (the second iteration of the main algorithm), branches
  that contain unary predicate variables in the conclusion, i.e. we only use
  the ``non-recursive'' branches.

  <subsection|Joint constraint abduction for linear arithmetic>

  We follow the scheme we established in joint constraint abduction for
  terms.

  We maintain an ordering of branches. We accumulate simple abduction answers
  into the partial abduction answer until we meet branch that does not have
  any answer satisfiable with the partial answer so far. Then we start over,
  but put the branch that failed in front of the sequence. If a branch
  <math|i> is at front for <math|n<rsub|i>>th time, we skip the initial
  <math|n<rsub|i>-1> simple abduction answers in it. If no front branch
  <math|i> has at least <math|n<rsub|i>> answers, the search fails. [FIXME:
  After an answer working for all branches has been found, we perform
  additional check, which encapsulates negative constraints introduced by
  <verbatim|assert false> construct. If the check fails, we increase the skip
  count of the head branch and repeat the search. -- in term abduction only?]

  When a branch has no more solutions to offer -- its skip factor
  <math|n<rsub|i>> has reached the number of fully maximal solutions to that
  branch -- we move it to a separate <em|runouts> list and continue search
  starting from a different branch. We do not increase its skip factor, but
  we check the runouts directly after the first branch, so that conflicting
  branches can be located. When the first branch conflicts with the runouts,
  we increase its skip factor and repeat. We keep a count of conflicts for
  the runouts so that in case of overall failure, we can report a branch
  likely to be among those preventing abduction.

  We remember SCA answers when skipping over them, not to return the same
  answer for different skip factors. But we also remember all JCA partial
  answers that led to resetting. If a partial answer becomes as strong as one
  of them, we can reset without further checking. If an empty partial answer
  led to resetting, no answer exists. The failed partial answers are
  initialized with the discarded answers, passed from the main algorithm.

  When searching for abduction answer fails, we raise exception
  <verbatim|Suspect> that contains the partial answer conjoined with
  conclusion of an implication that failed to produce an answer compatible
  with remaining implications.

  <section|Disjunction Elimination>

  <em|Disjunction elimination> answers are the maximally specific
  conjunctions of atoms that are implied by each of a given set of
  conjunction of atoms. In case of term equations the disjunction elimination
  algorithm is based on the <em|anti-unification> algorithm. In case of
  linear arithmetic inequalities, disjunction elimination is exactly finding
  the convex hull of a set of possibly unbounded polyhedra. We roughly follow
  <cite|disjelimTechRep>, but depart from the algorithm presented there
  because we employ our unification algorithm to separate sorts. Since as a
  result we do not introduce variables for <em|alien subterms>, we include
  the variables introduced by anti-unification in constraints sent to
  disjunction elimination for their respective sorts.

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

  <subsection|Abductive disjunction elimination under quantifier prefix>

  We extend the notion of disjunction elimination:
  <math|\<exists\><wide|\<alpha\>|\<bar\>>.A> is an answer to <em|abductive
  disjunction elimination under quantifier prefix> problem
  <math|\<cal-Q\>.<wide|D<rsub|i>|\<bar\>>> when there exist
  <math|\<exists\><wide|\<beta\>|\<bar\>><rsub|i,j>.B<rsub|i,j>> and
  <math|U<rsub|i>> such that:

  <\enumerate>
    <item><math|\<vDash\><around*|(|\<exists\><wide|<wide|\<beta\>|\<bar\>><rsub|i,j>|\<bar\>>.D<rsub|i>\<wedge\><rsub|j>B<rsub|i,j>|)>\<Leftrightarrow\><around*|(|D<rsub|i>\<wedge\>U<rsub|i>|)>>;

    <item><math|<around*|(|\<forall\>i|)>\<vDash\>D<rsub|i>\<wedge\>U<rsub|i>\<Rightarrow\>\<exists\><wide|\<alpha\>|\<bar\>>\\FV<around*|(|U<rsub|i>|)>.A>;

    <item><math|<around*|(|\<forall\>i,j|)>\<vDash\>D<rsub|j>\<Rightarrow\>\<exists\><wide|\<beta\>|\<bar\>><rsub|i,j>.B<rsub|i,j>>;

    <item><math|\<vDash\>\<forall\><wide|<wide|\<beta\>|\<bar\>><rsub|i,j>|\<bar\>>\<cal-Q\>.\<wedge\><rsub|i,j>B<rsub|i,j>>
    and <math|\<vDash\>\<cal-Q\>.\<wedge\><rsub|i>U<rsub|i>>.
  </enumerate>

  We currently do not pursue a complete algorithm for abductive disjunction
  elimination. Rather, we extend our algorithms in a natural way, that
  satisfies the requirements of abductive disjunction elimination and
  suffices in practice. The sort-integrating algorithm essentially does not
  change:

  <\enumerate>
    <item>Let <math|\<wedge\><rsub|s>D<rsub|i,s>\<equiv\>\<b-U\><around|(|D<rsub|i>|)>>
    where <math|D<rsub|i,s>> is of sort <math|s>, be the result of our
    sort-separating unification.

    <item>For the sort <math|s<rsub|ty>>:

    <\enumerate>
      <item>Let <math|V=<around*|{|x<rsub|j>,<wide|t<rsub|i,j>|\<bar\>><mid|\|>\<forall\>i\<exists\>t<rsub|i,j>.x<rsub|j><wide|=|\<dot\>>t<rsub|i,j>\<in\>D<rsub|i,s<rsub|ty>>|}>>.

      <item>Let <math|G=<around*|{|<wide|\<alpha\>|\<bar\>><rsub|j>,g<rsub|j>,<wide|u<rsub|i>|\<bar\>>,<wide|\<theta\><rsub|i,j>|\<bar\>><mid|\|>\<theta\><rsub|i,j>=<around*|[|<wide|\<alpha\>|\<bar\>><rsub|j>\<assign\><wide|g|\<bar\>><rsub|j><rsup|i>|]>,\<theta\><rsub|i,j><around*|(|g<rsub|j>|)>=u<rsub|i><around*|(|t<rsub|i,j>|)>|}>>
      be the most specific anti-unifiers of
      <math|<wide|<rsub|>u<rsub|i><around*|(|t<rsub|i,j>|)>|\<bar\>>> for
      each <math|j>, where <math|u<rsub|i>> is a part of
      <math|U<rsub|><rsub|i>>.

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

  Our current generalized anti-unification algorithm:

  <\eqnarray*>
    <tformat|<table|<row|<cell|au<rsub|U,G><around*|(|t;\<ldots\>;t|)>>|<cell|=>|<cell|\<varnothing\>,t,U,G>>|<row|<cell|au<rsub|U,G><around*|(|f<around*|(|<wide|t|\<bar\>><rsup|1>|)>;\<ldots\>;f<around*|(|<wide|t|\<bar\>><rsup|n>|)>|)>>|<cell|=>|<cell|<wide|\<alpha\>|\<bar\>>,f<around*|(|<wide|g|\<bar\>>|)>,U<rprime|'>,G<rprime|'>>>|<row|<cell|<with|mode|text|where
    \ ><wide|\<alpha\>|\<bar\>>,<wide|g|\<bar\>>,U<rprime|'>,G<rprime|'>>|<cell|=>|<cell|aun<rsub|U,G><around*|(|<wide|t|\<bar\>><rsup|1>;\<ldots\>;<wide|t|\<bar\>><rsup|n>|)>>>|<row|<cell|au<rsub|U,G><around*|(|t<rsub|1>;\<ldots\>;t<rsub|n>|)>>|<cell|=>|<cell|\<varnothing\>,\<alpha\>,U,G>>|<row|<cell|<with|mode|text|when>>|<cell|>|<cell|<around*|(|<around*|[|t<rsub|1>;\<ldots\>;t<rsub|n>|]>\<mapsto\>\<alpha\>|)>\<in\>G>>|<row|<cell|au<rsub|U,G><around*|(|\<ldots\>;\<beta\><rsub|i>;\<ldots\>;f<around*|(|<wide|t|\<bar\>><rsup|j>|)>;\<ldots\>|)>>|<cell|=>|<cell|<wide|\<alpha\>|\<bar\>><wide|\<alpha\>|\<bar\>><rprime|'>,g,U<rprime|''>,G<rprime|'>>>|<row|<cell|<with|mode|text|where
    \ ><wide|\<alpha\>|\<bar\>><rprime|'>,g,U<rprime|''>,G<rprime|'>>|<cell|=>|<cell|au<rsub|U<rprime|'>,G><around*|(|\<ldots\>;f<around*|(|<wide|\<alpha\>|\<bar\>>|)>;\<ldots\>;f<around*|(|<wide|t|\<bar\>><rsup|j>|)><around*|[|\<beta\><rsub|i>\<assign\>f<around*|(|<wide|\<alpha\>|\<bar\>>|)>|]>;\<ldots\>|)>>>|<row|<cell|U<rprime|'>>|<cell|=>|<cell|U<around*|[|\<beta\><rsub|i>\<assign\>f<around*|(|<wide|\<alpha\>|\<bar\>>|)>|]>\<wedge\>\<beta\><rsub|i><wide|=|\<dot\>>f<around*|(|<wide|\<alpha\>|\<bar\>>|)>>>|<row|<cell|<with|mode|text|when>>|<cell|>|<cell|\<exists\>\<beta\><rsub|i>\<in\>\<cal-Q\><with|mode|text|,
    treat ><wide|\<alpha\>|\<bar\>><with|mode|text| as quantified with
    >\<exists\>\<beta\><rsub|i>>>|<row|<cell|au<rsub|U,G><around*|(|\<ldots\>;\<beta\><rsub|i>;\<ldots\>;\<beta\><rsub|j>;\<ldots\>|)>>|<cell|=>|<cell|<wide|\<alpha\>|\<bar\>><rprime|'>,g,U<rprime|''>,G<rprime|'>>>|<row|<cell|<with|mode|text|where
    \ ><wide|\<alpha\>|\<bar\>><rprime|'>,g,U<rprime|''>,G<rprime|'>>|<cell|=>|<cell|au<rsub|U<rprime|'>,G><around*|(|\<ldots\>;\<beta\><rsub|j>;\<ldots\>;\<beta\><rsub|j>;\<ldots\>|)>>>|<row|<cell|U<rprime|'>>|<cell|=>|<cell|U<around*|[|\<beta\><rsub|i>\<assign\>\<beta\><rsub|j>|]>\<wedge\>\<beta\><rsub|i><wide|=|\<dot\>>\<beta\><rsub|j>>>|<row|<cell|<with|mode|text|when>>|<cell|>|<cell|\<exists\>\<beta\><rsub|i>\<in\>\<cal-Q\>,\<beta\><rsub|j>\<leqslant\><rsub|\<cal-Q\>>\<beta\><rsub|i>>>|<row|<cell|au<rsub|U,G><around*|(|t<rsub|1>;\<ldots\>;t<rsub|n>|)>>|<cell|=>|<cell|\<alpha\>,\<alpha\>,U,<around*|(|<around*|[|t<rsub|1>;\<ldots\>;t<rsub|n>|]>\<mapsto\>\<alpha\>|)>G>>|<row|<cell|<with|mode|text|otherwise,>>|<cell|>|<cell|<with|mode|text|where
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

  Corresponding extension of disjunction elimination for linear arithmetics
  amounts to processing of the equations that were used to eliminate ``local
  variables''. Recall that before passing inequalities to the convex hull
  algorithm, we eliminate all equations and implicit equalities which contain
  a variable not shared by all <math|D<rsub|i>>. Extended algorithm FIXME:
  TODO those equations that are valid w.r.t. the quantifier.

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

  Let us discuss the algorithm from <cite|InvariantsTechRep2> for
  <math|Split<around*|(|\<cal-Q\>,<wide|\<alpha\>|\<bar\>>,A,<wide|<wide|\<beta\>|\<bar\>><rsup|\<chi\>>|\<bar\>>,<wide|<wide|\<zeta\>|\<bar\>><rsup|\<chi\>>|\<bar\>>,<wide|\<rho\><rsup|\<chi\>>|\<bar\>>,<wide|A<rsub|\<chi\>><rsup|0>|\<bar\>>|)>>.
  Note that due to existential types predicates, we actually compute
  <math|Split<around*|(|\<cal-Q\>,<wide|\<alpha\>|\<bar\>>,A,<wide|<wide|\<beta\>|\<bar\>><rsup|\<beta\><rsub|\<chi\>>>|\<bar\>>,<wide|<wide|\<zeta\>|\<bar\>><rsup|\<beta\><rsub|\<chi\>>>|\<bar\>>,<wide|\<rho\><rsup|\<beta\><rsub|\<chi\>>>|\<bar\>>,<wide|A<rsub|\<beta\><rsub|\<chi\>>><rsup|0>|\<bar\>>|)>>,
  i.e. we index by <math|\<beta\><rsub|\<chi\>>> (which can be multiple for a
  single <math|\<chi\>>) rather than <math|\<chi\>>. We retain the notation
  from <cite|InvariantsTechRep2> here as it better conveys the intent. We do
  not pass quantifiers around to reflect the source code: the helper function
  <verbatim|loop avs ans sol> of function <verbatim|split> corresponds to
  <math|Split<around*|(|<wide|\<alpha\>|\<bar\>>,A,<wide|A<rsub|\<beta\><rsub|\<chi\>>><rsup|0>|\<bar\>>|)>>.

  <\eqnarray*>
    <tformat|<cwith|6|6|3|3|cell-valign|t>|<table|<row|<cell|\<alpha\>\<prec\>\<beta\>>|<cell|\<equiv\>>|<cell|\<alpha\>\<less\><rsub|\<cal-Q\>>\<beta\>\<vee\><around*|(|\<alpha\>\<leqslant\><rsub|\<cal-Q\>>\<beta\>\<wedge\>\<beta\>\<nless\><rsub|\<cal-Q\>>\<alpha\>\<wedge\>\<alpha\>\<in\><wide|<wide|\<beta\>|\<bar\>><rsup|\<chi\>>|\<bar\>>\<wedge\>\<beta\>\<nin\><wide|<wide|\<beta\>|\<bar\>><rsup|\<chi\>>|\<bar\>>|)>>>|<row|<cell|A<rsub|0>>|<cell|=>|<cell|A\\<around*|{|\<beta\><wide|=|\<dot\>>\<alpha\>\<in\>A<mid|\|>\<beta\>\<in\><wide|<wide|\<beta\>|\<bar\>><rsup|\<chi\>>|\<bar\>>\<wedge\><around*|(|\<exists\>\<alpha\>|)>\<in\>\<cal-Q\>\<wedge\>\<beta\>\<prec\>\<alpha\>|}>>>|<row|<cell|A<rsub|\<chi\>><rsup|1>>|<cell|=>|<cell|Connected<around*|(|<wide|\<beta\>|\<bar\>><rsup|\<chi\>>,A<rsub|0>|)>>>|<row|<cell|A<rsub|\<chi\>><rsup|2>>|<cell|=>|<cell|<around*|{|c\<in\>A<rsub|\<chi\>><rsup|1><mid|\|>c<with|mode|text|
    is not localized in branch without >\<chi\><with|mode|text| in
    premise>|}>>>|<row|<cell|A<rsub|\<chi\>><rsup|3>>|<cell|=>|<cell|A<rsub|\<chi\>><rsup|2>\\\<cup\><rsub|\<chi\><rprime|'>\<gtr\><rsub|\<cal-Q\>>\<chi\>>A<rsub|\<chi\><rprime|'>><rsup|2>>>|<row|<cell|A<rsub|\<chi\>><rsup|4>>|<cell|=>|<cell|Connected<around*|(|<wide|\<beta\>|\<bar\>><rsup|\<chi\>>,A<rsub|\<chi\>><rsup|3>|)>>>|<row|<cell|<with|mode|text|if>>|<cell|>|<cell|\<nvDash\>\<forall\><wide|\<alpha\>|\<bar\>>\<cal-Q\>.A\<setminus\>\<cup\><rsub|\<chi\>>A<rsub|\<chi\>><rsup|4>>>|<row|<cell|<with|mode|text|then
    return>>|<cell|>|<cell|\<bot\>>>|<row|<cell|<with|mode|text|for all
    ><wide|A<rsub|\<chi\>><rsup|+>|\<bar\>><with|mode|text| min. w.r.t.
    >\<subset\><with|mode|text| s.t.>>|<cell|>|<cell|\<wedge\><rsub|\<chi\>><around*|(|A<rsub|\<chi\>><rsup|+>\<subset\>A<rsub|\<chi\>><rsup|4>|)>\<wedge\>\<vDash\>\<forall\><wide|\<alpha\>|\<bar\>>\<cal-Q\>.A\<setminus\>\<cup\><rsub|\<chi\>>A<rsub|\<chi\>><rsup|+>:>>|<row|<cell|<with|mode|text|if>>|<cell|>|<cell|Strat<around*|(|A<rsup|+><rsub|\<chi\>>,<wide|\<beta\>|\<bar\>><rsup|\<chi\>>|)><with|mode|text|
    \ returns >\<bot\><with|mode|text| for some
    >\<chi\>>>|<row|<cell|<with|mode|text|then
    return>>|<cell|>|<cell|\<bot\>>>|<row|<cell|<with|mode|text|else
    \ ><wide|\<alpha\>|\<bar\>><rsub|+><rsup|\<chi\>>,A<rsub|\<chi\>><rsup|L>,A<rsup|R><rsub|\<chi\>>>|<cell|=>|<cell|Strat<around*|(|A<rsup|+><rsub|\<chi\>>,<wide|\<beta\>|\<bar\>><rsup|\<chi\>>|)>>>|<row|<cell|A<rsub|\<chi\>>>|<cell|=>|<cell|A<rsub|\<chi\>><rsup|0>\<cup\>A<rsub|\<chi\>><rsup|L>>>|<row|<cell|<wide|\<alpha\>|\<bar\>><rsup|\<chi\>><rsub|0>>|<cell|=>|<cell|<wide|\<alpha\>|\<bar\>>\<cap\>FV<around*|(|A<rsub|\<chi\>>|)>>>|<row|<cell|<wide|\<alpha\>|\<bar\>><rsup|\<chi\>>>|<cell|=>|<cell|<around*|(|<wide|\<alpha\>|\<bar\>><rsup|\<chi\>><rsub|0>\<setminus\><big|cup><rsub|\<chi\><rprime|'>\<less\><rsub|\<cal-Q\>>\<chi\>><wide|\<alpha\>|\<bar\>><rsup|\<chi\><rprime|'>><rsub|0>|)><wide|\<alpha\>|\<bar\>><rsub|+><rsup|\<chi\>>>>|<row|<cell|A<rsub|+>>|<cell|=>|<cell|\<cup\><rsub|\<chi\>>A<rsub|\<chi\>><rsup|R>>>|<row|<cell|A<rsub|res>>|<cell|=>|<cell|A<rsub|+>\<cup\><wide|A<rsub|+>|~><around*|(|A\<setminus\>\<cup\><rsub|\<chi\>>A<rsub|\<chi\>><rsup|+>|)>>>|<row|<cell|<with|mode|text|if>>|<cell|>|<cell|\<cup\><rsub|\<chi\>><wide|\<alpha\>|\<bar\>><rsup|\<chi\>><rsub|+>\<neq\>\<varnothing\><with|mode|text|
    \ then>>>|<row|<cell|\<cal-Q\><rprime|'>,<wide|<wide|\<alpha\><rsub|>|\<bar\>><rsup|\<chi\>><rsub|+><rprime|'>|\<bar\>>,A<rsub|res><rprime|'>,<wide|\<exists\><wide|\<alpha\>|\<bar\>><rprime|'><rsup|\<chi\>>.A<rsub|\<chi\>><rprime|'>|\<bar\>>>|<cell|\<in\>>|<cell|Split<around*|(|\<cal-Q\><around*|[|<wide|\<forall\><wide|\<beta\>|\<bar\>><rsup|\<chi\>>|\<bar\>>\<assign\><wide|\<forall\><around*|(|<wide|\<beta\>|\<bar\>><rsup|\<chi\>>\<cup\><wide|\<alpha\>|\<bar\>><rsup|\<chi\>>|)>|\<bar\>>|]>,<wide|\<alpha\>|\<bar\>>\<setminus\>\<cup\><rsub|\<chi\>><wide|\<alpha\>|\<bar\>><rsup|\<chi\>>,A<rsub|res>,<wide|<wide|\<beta\>|\<bar\>><rsup|\<chi\>>\<cup\><wide|\<alpha\>|\<bar\>><rsup|\<chi\>>|\<bar\>>,<wide|A<rsub|\<chi\>>|\<bar\>>|)>>>|<row|<cell|<with|mode|text|return>>|<cell|>|<cell|\<cal-Q\><rprime|'>,<wide|<wide|\<alpha\>|\<bar\>><rsub|+><rsup|\<chi\>><wide|\<alpha\><rsub|>|\<bar\>><rsup|\<chi\>><rsub|+><rprime|'>|\<bar\>>,A<rsub|res><rprime|'>,<wide|\<exists\><wide|\<alpha\>|\<bar\>><rsup|\<chi\>><wide|\<alpha\>|\<bar\>><rprime|'><rsup|\<chi\>>.A<rsub|\<chi\>><rprime|'>|\<bar\>>>>|<row|<cell|<with|mode|text|else
    return>>|<cell|>|<cell|\<forall\><around*|(|<wide|\<alpha\>|\<bar\>>\<setminus\>\<cup\><rsub|\<chi\>><wide|\<alpha\>|\<bar\>><rsup|\<chi\>>|)>\<cal-Q\>,<wide|<wide|\<alpha\><rsub|>|\<bar\>><rsup|\<chi\>><rsub|+>|\<bar\>>,A<rsub|res>,<wide|\<exists\><wide|\<alpha\>|\<bar\>><rsup|\<chi\>>.A<rsub|\<chi\>>|\<bar\>>>>>>
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

  As an additional measure to detect misleading splits early, we pass an
  approximate information about which branch <math|D<rsub|i>,C<rsub|i>> of
  the JCA problem atoms <math|a\<in\>A> originate from:
  <math|\<rho\><around*|(|a|)>>, and which branches contain <math|\<chi\>> in
  premise: <math|\<rho\><rsup|\<chi\>>>, so that an atom <math|a> is put into
  solution <math|A<rsub|\<chi\>><rsup|+>> only if <math|D<rsub|i>> contains
  <math|\<chi\>>.

  Description of the algorithm in more detail:

  <\enumerate>
    <item><math|<tabular|<tformat|<table|<row|<cell|\<alpha\>\<prec\>\<beta\>>|<cell|\<equiv\>>|<cell|\<alpha\>\<less\><rsub|\<cal-Q\>>\<beta\>\<vee\><around*|(|\<alpha\>\<leqslant\><rsub|\<cal-Q\>>\<beta\>\<wedge\>\<beta\>\<nless\><rsub|\<cal-Q\>>\<alpha\>\<wedge\>\<alpha\>\<in\><wide|<wide|\<beta\>|\<bar\>><rsup|\<chi\>>|\<bar\>>\<wedge\>\<beta\>\<nin\><wide|<wide|\<beta\>|\<bar\>><rsup|\<chi\>>|\<bar\>>|)>>>>>>>
    The variables <math|<wide|<wide|\<beta\>|\<bar\>><rsup|\<chi\>>|\<bar\>>>
    are the answer variables of the solution from the previous round. We need
    to keep them apart from other variables even when they're not separated
    by quantifier alternation.

    <item><math|<tabular|<tformat|<table|<row|<cell|A<rsub|0>>|<cell|=>|<cell|A\\<around*|{|\<beta\><wide|=|\<dot\>>\<alpha\>\<in\>A<mid|\|>\<beta\>\<in\><wide|<wide|\<beta\>|\<bar\>><rsup|\<chi\>>|\<bar\>>\<wedge\><around*|(|\<exists\>\<alpha\>|)>\<in\>\<cal-Q\>\<wedge\>\<beta\>\<prec\>\<alpha\>|}>>>>>>>
    We handle information carried in <math|\<beta\><wide|=|\<dot\>>\<alpha\>>
    by substituting <math|\<alpha\>> with <math|\<beta\>>.

    <item><math|<tabular|<tformat|<table|<row|<cell|A<rsub|\<chi\>><rsup|1>>|<cell|=>|<cell|Connected<around*|(|<wide|\<beta\>|\<bar\>><rsup|\<chi\>>,A<rsub|0>|)>>>>>>>Initial
    filtering of candidates to have less work at later stages.
    <math|Connected<around*|(|<wide|\<beta\>|\<bar\>>,A<rsub|0>|)>> is the
    subset of atoms of <math|A<rsub|0>> reachable from nodes
    <math|<wide|\<beta\>|\<bar\>>>, where atoms are considered directly
    connected when they share a variable.

    <item><math|<tabular|<tformat|<table|<row|<cell|A<rsub|\<chi\>><rsup|2>>|<cell|=>|<cell|<around*|{|c\<in\>A<rsub|\<chi\>><rsup|1><mid|\|>c<with|mode|text|
    is not localized in branch without >\<chi\><with|mode|text| in
    premise>|}>>>>>>>Guard against misplacing abduction answer atoms.
    Unfortunately localization information can be too general for this step
    alone to be sufficient at splitting the answer.

    <item><math|<tabular|<tformat|<table|<row|<cell|A<rsub|\<chi\>><rsup|3>>|<cell|=>|<cell|A<rsub|\<chi\>><rsup|2>\\\<cup\><rsub|\<chi\><rprime|'>\<gtr\><rsub|\<cal-Q\>>\<chi\>>A<rsub|\<chi\><rprime|'>><rsup|2>>>>>>>
    If a premise has an <math|\<chi\><rprime|'>> atom then it has an
    <math|\<chi\>> atom for <math|\<beta\><rsup|\<chi\><rprime|'>>>
    downstream of <math|b<rsup|\<chi\>>>.

    <item><math|<tabular|<tformat|<cwith|1|1|3|3|cell-valign|t>|<table|<row|<cell|A<rsub|\<chi\>><rsup|4>>|<cell|=>|<cell|Connected<around*|(|<wide|\<beta\>|\<bar\>><rsup|\<chi\>>,A<rsub|\<chi\>><rsup|3>|)>>>>>>>Disconnected
    atoms do not contribute to the invariant over the parameters
    <math|<wide|\<beta\>|\<bar\>><rsup|\<chi\>>>. Note that the solution
    atoms are not yet separated from the residuum atoms so the final solution
    might still have disconnected components.

    <item><math|<tabular|<tformat|<table|<row|<cell|<with|mode|text|if>>|<cell|>|<cell|\<nvDash\>\<forall\><wide|\<alpha\>|\<bar\>>\<cal-Q\>.A\<setminus\>\<cup\><rsub|\<chi\>>A<rsub|\<chi\>><rsup|4>>>>>><with|mode|text|
    then return >\<bot\>> Failed solution attempt. A common example is when
    the use site of recursive definition, resp. the existential type
    introduction site, is not in scope of a defining site of recursive
    definition, resp. an existential type elimination site, and has too
    strong requirements.

    <item><math|<tabular|<tformat|<table|<row|<cell|<with|mode|text|for all
    ><wide|A<rsub|\<chi\>><rsup|+>|\<bar\>><with|mode|text| minimal w.r.t.
    >\<subset\><with|mode|text| such that>>|<cell|>|<cell|\<wedge\><rsub|\<chi\>><around*|(|A<rsub|\<chi\>><rsup|+>\<subset\>A<rsub|\<chi\>><rsup|4>|)>\<wedge\>\<vDash\>\<cal-Q\>.A\<setminus\>\<cup\><rsub|\<chi\>>A<rsub|\<chi\>><rsup|+>:>>>>>>
    Select invariants such that the residuum
    <math|A\<setminus\>\<cup\><rsub|\<chi\>>A<rsub|\<chi\>><rsup|+>> is
    consistent. The final residuum <math|A<rsub|res>> represents the global
    constraints, the solution for global type variables. The solutions
    <math|A<rsub|\<chi\>><rsup|+>> represent the invariants, the solution for
    invariant type parameters.

    <item><math|<tabular|<tformat|<table|<row|<cell|<with|mode|text|if>>|<cell|>|<cell|Strat<around*|(|A<rsup|+><rsub|\<chi\>>,<wide|\<beta\>|\<bar\>><rsup|\<chi\>>|)><with|mode|text|
    \ returns >\<bot\><with|mode|text| for some
    >\<chi\>>>>>><with|mode|text|then return >\<bot\>> In the implementation,
    we address stratification issues already during abduction.

    <item><math|<wide|\<alpha\>|\<bar\>><rsub|+><rsup|\<chi\>>,A<rsub|\<chi\>><rsup|L>,A<rsup|R><rsub|\<chi\>>=Strat<around*|(|A<rsub|\<chi\>><rsup|+>,<wide|\<beta\>|\<bar\>><rsup|\<chi\>>|)>>
    is computed as follows: for every <math|c\<in\>A<rsub|\<chi\>><rsup|+>>,
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
      <item>We add <math|<wide|\<alpha\>|\<bar\>><rsub|+><rsup|\<chi\>>> to
      <math|<wide|\<beta\>|\<bar\>><rsup|\<chi\>>>.
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

    <item><math|<tabular|<tformat|<table|<row|<cell|<with|mode|text|if>>|<cell|>|<cell|\<cup\><rsub|\<chi\>><wide|\<alpha\>|\<bar\>><rsup|\<chi\>><rsub|+>\<neq\>\<varnothing\><with|mode|text|
    \ then>>>>>>> -- If <math|Strat> generated new variables, we need to
    redistribute the <math|<wide|A<rsub|+>|~><around*|(|A\<setminus\>\<cup\><rsub|\<chi\>>A<rsub|\<chi\>><rsup|+>|)>>
    atoms to make <math|\<cal-Q\><rprime|'>.A<rsub|res>> valid again.

    <item><math|<tabular|<tformat|<table|<row|<cell|\<cal-Q\><rprime|'>,<wide|<wide|\<alpha\><rsub|>|\<bar\>><rsup|\<chi\>><rsub|+><rprime|'>|\<bar\>>,A<rsub|res><rprime|'>,<wide|\<exists\><wide|\<alpha\>|\<bar\>><rprime|'><rsup|\<chi\>>.A<rsub|\<chi\>><rprime|'>|\<bar\>>>|<cell|\<in\>>|<cell|Split<around*|(|\<cal-Q\><around*|[|<wide|\<forall\><wide|\<beta\>|\<bar\>><rsup|\<chi\>>|\<bar\>>\<assign\><wide|\<forall\><around*|(|<wide|\<beta\>|\<bar\>><rsup|\<chi\>>\<cup\><wide|\<alpha\>|\<bar\>><rsup|\<chi\>>|)>|\<bar\>>|]>,<wide|\<alpha\>|\<bar\>>\<setminus\>\<cup\><rsub|\<chi\>><wide|\<alpha\>|\<bar\>><rsup|\<chi\>>,A<rsub|res>,<wide|<wide|\<beta\>|\<bar\>><rsup|\<chi\>>\<cup\><wide|\<alpha\>|\<bar\>><rsup|\<chi\>>|\<bar\>>,<wide|A<rsub|\<chi\>>|\<bar\>>|)>>>>>>>
    Recursive call includes <math|<wide|\<alpha\>|\<bar\>><rsup|\<chi\>><rsub|+>>
    in <math|<wide|\<beta\>|\<bar\>><rsup|\<chi\>>> so that, among other
    things, <math|A<rsub|+>> are redistributed into <math|A<rsub|\<chi\>>>.

    <item><math|<tabular|<tformat|<table|<row|<cell|<with|mode|text|return>>|<cell|>|<cell|\<cal-Q\><rprime|'>,<wide|<wide|\<alpha\>|\<bar\>><rsub|+><rsup|\<chi\>><wide|\<alpha\><rsub|>|\<bar\>><rsup|\<chi\>><rsub|+><rprime|'>|\<bar\>>,A<rsub|res><rprime|'>,<wide|\<exists\><wide|\<alpha\>|\<bar\>><rsup|\<chi\>><wide|\<alpha\>|\<bar\>><rprime|'><rsup|\<chi\>>.A<rsub|\<chi\>><rprime|'>|\<bar\>>>>>>>>
    We do not add <math|\<forall\><wide|\<alpha\>|\<bar\>>> in front of
    <math|\<cal-Q\><rprime|'>> because it already includes these variables.
    <math|<wide|<wide|\<alpha\>|\<bar\>><rsub|+><rsup|\<chi\>><wide|\<alpha\><rsub|>|\<bar\>><rsup|\<chi\>><rsub|+><rprime|'>|\<bar\>>>
    lists all variables introduced by <math|Strat>.

    <item><math|<tabular|<tformat|<table|<row|<cell|<with|mode|text|else
    return>>|<cell|>|<cell|\<forall\><around*|(|<wide|\<alpha\>|\<bar\>>\<setminus\>\<cup\><rsub|\<chi\>><wide|\<alpha\>|\<bar\>><rsup|\<chi\>>|)>\<cal-Q\>,<wide|<wide|\<alpha\><rsub|>|\<bar\>><rsup|\<chi\>><rsub|+>|\<bar\>>,A<rsub|res>,<wide|\<exists\><wide|\<alpha\>|\<bar\>><rsup|\<chi\>>.A<rsub|\<chi\>>|\<bar\>>>>>>>>
    Note that <math|<wide|\<alpha\>|\<bar\>>\<setminus\>\<cup\><rsub|\<chi\>><wide|\<alpha\>|\<bar\>><rsup|\<chi\>>>
    does not contain the current <math|<wide|\<beta\>|\<bar\>><rsup|\<chi\>>>,
    because <math|<wide|\<alpha\>|\<bar\>>> does not contain it initially and
    the recursive call maintains that: <math|<wide|\<alpha\>|\<bar\>>\<assign\><wide|\<alpha\>|\<bar\>>\<setminus\>\<cup\><rsub|\<chi\>><wide|\<alpha\>|\<bar\>><rsup|\<chi\>>,<wide|\<beta\>|\<bar\>><rsup|\<chi\>>\<assign\><wide|\<beta\>|\<bar\>><rsup|\<chi\>><wide|\<alpha\>|\<bar\>><rsup|\<chi\>>>.
  </enumerate>

  Finally we define <math|Split<around*|(|<wide|\<alpha\>|\<bar\>>,A|)>\<assign\>Split<around*|(|<wide|\<alpha\>|\<bar\>>,A,<wide|\<top\>|\<bar\>>|)>>.
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
  numbers <verbatim|(* N *)> in the source code. Step <math|k> of the loop of
  the final algorithm:

  <\eqnarray*>
    <tformat|<cwith|19|19|2|2|cell-valign|c>|<table|<row|<cell|<wide|\<exists\><wide|\<beta\>|\<bar\>><rsup|\<chi\>,k>.F<rsub|\<chi\>>|\<bar\>>>|<cell|=>|<cell|S<rsub|k>>>|<row|<cell|Prune<around*|(|A|)>>|<cell|=>|<cell|A\\<wide|\<alpha\><rsub|\<alpha\>><rsup|K><wide|=|\<dot\>>\<ldots\>|\<bar\>><eq-number><label|Skp>>>|<row|<cell|S<rsub|k><rprime|'>=<wide|\<exists\><wide|\<beta\>|\<bar\>><rsup|\<chi\>,k>.F<rsub|\<chi\>><rprime|'>|\<bar\>>>|<cell|=>|<cell|<wide|\<exists\><wide|\<beta\>|\<bar\>><rsup|\<chi\>,k>.Prune<around*|(|F<rsub|\<chi\>>|)>|\<bar\>>>>|<row|<cell|D<rsub|K><rsup|\<alpha\>>\<Rightarrow\>C<rsub|K><rsup|\<alpha\>>\<in\>R<rsub|k><rsup|->S<rsub|k><rprime|'><around*|(|\<Phi\>|)>>|<cell|=>|<cell|<with|mode|text|all
    such that >\<chi\><rsub|K><around*|(|\<alpha\>,\<alpha\><rsub|\<alpha\>><rsup|K>|)>\<in\>C<rsub|K><rsup|\<alpha\>>,<eq-number>>>|<row|<cell|>|<cell|>|<cell|<wide|C<rsup|\<alpha\>><rsub|j>|\<bar\>>=<around*|{|C<mid|\|>D\<Rightarrow\>C\<in\>S<rsub|k><around*|(|\<Phi\>|)>\<wedge\>D\<subseteq\>D<rsup|\<alpha\>><rsub|K>|}>>>|<row|<cell|\<exists\><wide|\<alpha\>|\<bar\>><rsup|\<chi\><rsub|K>><rsub|g>.G<rsub|\<chi\><rsub|K>>>|<cell|=>|<cell|Connected<around*|(|\<delta\>,DisjElim<around*|(|<wide|\<delta\><wide|=|\<dot\>>\<alpha\>\<wedge\>D<rsup|\<alpha\>><rsub|K>\<wedge\><rsub|j>C<rsup|\<alpha\>><rsub|j>|\<bar\>><rsub|\<alpha\>\<in\><wide|\<alpha\><rsub|3><rsup|i,K>|\<bar\>>>|)>|)><eq-number>>>|<row|<cell|\<exists\><wide|\<alpha\>|\<bar\>><rsup|\<chi\><rsub|K>>.G<rsub|\<chi\><rsub|K>><rprime|'>>|<cell|=>|<cell|Simpl<around*|(|FV<around*|(|G<rsub|\<chi\><rsub|K>>|)>.G<rsub|\<chi\><rsub|K>>|)><eq-number>>>|<row|<cell|<wide|\<tau\>|\<vect\>><rsub|\<varepsilon\><rsub|K>>>|<cell|=>|<cell|<wide|FV<around*|(|G<rsub|\<chi\><rsub|K>><rprime|'>|)>\\\<delta\>\<delta\><rprime|'><wide|\<alpha\>|\<bar\>><rsup|\<chi\><rsub|K>><rsub|g>|\<vect\>>>>|<row|<cell|\<Xi\><around*|(|\<exists\><wide|\<alpha\>|\<bar\>><rsup|\<chi\><rsub|K>><rsub|g>.G<rsub|\<chi\><rsub|K>>|)>>|<cell|=>|<cell|\<exists\><wide|\<alpha\>|\<bar\>><rsup|\<chi\><rsub|K>>.\<delta\><rprime|'><wide|=|\<dot\>><wide|\<tau\>|\<vect\>><rsub|\<varepsilon\><rsub|K>>\<wedge\>G<rsub|\<chi\><rsub|K>><rprime|'>>>|<row|<cell|R<rsub|g><around*|(|\<chi\><rsub|K>|)>=\<exists\><wide|\<alpha\>|\<bar\>><rsup|\<chi\><rsub|K>>.F<rsub|\<chi\><rsub|K>>>|<cell|=>|<cell|\<Xi\><around*|(|\<exists\><wide|\<alpha\>|\<bar\>><rsub|g><rsup|\<chi\><rsub|K>>.H<around*|(|R<rsub|k><around*|(|\<chi\><rsub|K>|)>,G<rsub|\<chi\><rsub|K>>|)>|)><eq-number><label|Rg>>>|<row|<cell|P<rsub|g><around*|(|\<chi\><rsub|K>|)>>|<cell|=>|<cell|\<delta\><rprime|'><wide|=|\<dot\>><wide|\<tau\>|\<vect\>><rsub|\<varepsilon\><rsub|K>>\<wedge\>\<exists\><wide|\<alpha\>|\<bar\>><rsub|g><rsup|\<chi\><rsub|K>>.F<rsub|\<chi\><rsub|K>>>>|<row|<cell|P<rsub|g><around*|(|v<rsub|K><around*|(|\<beta\>|)>|)>>|<cell|=>|<cell|\<exists\><wide|\<alpha\>|\<bar\>>.\<beta\><wide|=|\<dot\>><wide|\<alpha\>|\<vect\>><with|mode|text|
    \ where \ ><around*|\||<wide|\<tau\>|\<vect\>><rsub|\<varepsilon\><rsub|K>>|\|>=<around*|\||<wide|\<alpha\>|\<vect\>>|\|>>>|<row|<cell|L<rsub|K>>|<cell|=>|<cell|<with|mode|text|reverse
    substitution of alien eqs. and >A<rsub|res><with|mode|text| from previous
    step>>>|<row|<cell|>|<cell|>|<cell|<with|mode|text|such that if
    >\<varepsilon\><rsub|K><around*|(|\<cdummy\>|)><with|mode|text| appears
    in >S<rsub|k><around*|(|\<chi\>|)>>>|<row|<cell|>|<cell|>|<cell|<with|mode|text|then
    >FV<around*|(|L<around*|(|\<varepsilon\><rsub|K><around*|(|<wide|\<tau\>|\<vect\>><rsub|\<varepsilon\><rsub|K>>|)>|)>|)>\<subseteq\><wide|\<beta\>|\<bar\>><rsup|\<chi\>,k>>>|<row|<cell|S<rsub|k><rprime|''>>|<cell|=>|<cell|<wide|\<exists\><wide|\<beta\>|\<bar\>><rsup|\<chi\>,k>.F<rsub|\<chi\>><rprime|'><around*|[|\<varepsilon\><rsub|K><around*|(|\<cdummy\>|)>\<assign\>L<around*|(|\<varepsilon\><rsub|K><around*|(|<wide|\<tau\>|\<vect\>><rsub|\<varepsilon\><rsub|K>>|)>|)>|]>|\<bar\>><eq-number>>>|<row|<cell|\<cal-Q\><rprime|'>.\<wedge\><rsub|i><around*|(|D<rsub|i>\<Rightarrow\>C<rsub|i>|)>>|<cell|=>|<cell|R<rsub|g><rsup|->P<rsub|g><rsup|+>S<rsub|k><rprime|''><around*|(|\<Phi\>|)>>>|<row|<cell|>|<cell|>|<cell|<with|mode|text|At
    later iterations, check negative constraints.><eq-number>>>|<row|<cell|\<exists\><wide|\<alpha\>|\<bar\>>.A>|<cell|=>|<cell|Abd<around*|(|\<cal-Q\><rprime|'>\\<wide|\<forall\>\<beta\><rsub|\<chi\>><wide|\<beta\><rsup|>|\<bar\>><rsup|\<chi\>>|\<bar\>>,<wide|\<beta\><rsub|\<chi\>><wide|\<beta\><rsup|>|\<bar\>><rsup|\<chi\>>,<wide|\<zeta\>|\<bar\>><rsup|\<chi\>>|\<bar\>>,<wide|D<rsub|i>,C<rsub|i>|\<bar\>>|)><eq-number>>>|<row|<cell|<around*|(|\<cal-Q\><rsup|k+1>,<wide|<wide|\<alpha\>|\<bar\>><rsup|\<chi\>><rsub|+>|\<bar\>>,A<rsub|res>,<wide|\<exists\><wide|\<alpha\>|\<bar\>><rsup|\<beta\><rsub|\<chi\>>>.A<rsub|\<beta\><rsub|\<chi\>>>|\<bar\>>|)>>|<cell|=>|<cell|Split<around*|(|\<cal-Q\><rprime|'>,<wide|\<alpha\>|\<bar\>>,A,<wide|\<beta\><rsub|\<chi\>><wide|\<beta\><rsup|>|\<bar\>><rsup|\<chi\>>|\<bar\>>,<wide|<wide|\<zeta\>|\<bar\>><rsup|\<chi\>>|\<bar\>>|)>>>|<row|<cell|<wide|\<tau\>|\<vect\>><rsub|\<varepsilon\><rsub|K>><rprime|'>>|<cell|=>|<cell|<wide|FV<around*|(|<wide|A<rsub|res>|~><around*|(|<wide|\<tau\>|\<vect\>><rsub|\<varepsilon\><rsub|K>>|)>|)>|\<vect\>>>>|<row|<cell|R<rsub|k+1><around*|(|\<chi\><rsub|K>|)>>|<cell|=>|<cell|\<exists\><wide|\<beta\>|\<bar\>><rsup|\<chi\><rsub|K>,k>.\<delta\><rprime|'><wide|=|\<dot\>><wide|\<tau\>|\<vect\>><rsub|\<varepsilon\><rsub|K>><rprime|'>\<wedge\>Simpl<around*|(|\<exists\><wide|\<alpha\>|\<bar\>><rsup|\<chi\><rsub|K>><wide|<wide|\<alpha\>|\<bar\>><rsup|\<beta\><rsub|\<chi\><rsub|K>>>|\<bar\>>.<wide|A<rsub|res>|~><around*|(|F<rsub|\<chi\><rsub|K>>\\\<delta\><rprime|'><wide|=|\<dot\>>\<ldots\>|)><next-line><with|mode|text|
    \ \ \ >\<wedge\><rsub|\<chi\><rsub|K>>A<rsub|\<beta\><rsub|\<chi\><rsub|K>>><around*|[|<wide|\<beta\><rsub|\<chi\><rsub|K>><wide|\<beta\><rsup|>|\<bar\>><rsup|\<beta\><rsub|\<chi\><rsub|K>>>|\<bar\>>\<assign\><wide|\<delta\><wide|\<beta\><rsup|>|\<bar\>><rsup|\<chi\><rsub|K>,k>|\<bar\>>|]>|)><eq-number>>>|<row|<cell|>|<cell|=>|<cell|R<rsub|g><rprime|'><around*|(|\<chi\><rsub|K>|)>>>|<row|<cell|S<rsub|k+1><around*|(|\<chi\>|)>>|<cell|=>|<cell|\<exists\><wide|\<beta\>|\<bar\>><rsup|\<chi\>,k>.Simpl<around*|(|\<exists\><wide|<wide|\<alpha\>|\<bar\>><rsup|\<beta\><rsub|\<chi\>>>|\<bar\>>.F<rsub|\<chi\>><rprime|''><next-line><with|mode|text|
    \ \ \ >\<wedge\>A<rsub|\<beta\><rsub|\<chi\>>><around*|[|<wide|\<beta\><rsub|\<chi\>><wide|\<beta\><rsup|>|\<bar\>><rsup|\<chi\>>|\<bar\>>\<assign\><wide|\<delta\><wide|\<beta\><rsup|>|\<bar\>><rsup|\<chi\>,k>|\<bar\>>|]>|)><eq-number><label|Skp1>>>|<row|<cell|<with|mode|text|if>>|<cell|>|<cell|<around*|(|\<forall\>\<chi\>|)>S<rsub|k+1><around*|(|\<chi\>|)>\<subseteq\>S<rsub|k><around*|(|\<chi\>|)>,<eq-number>>>|<row|<cell|>|<cell|>|<cell|<around*|(|\<forall\>\<chi\><rsub|K>|)>R<rsub|k+1><around*|(|\<chi\><rsub|K>|)>=R<rsub|k><around*|(|\<chi\><rsub|K>|)>,>>|<row|<cell|>|<cell|>|<cell|k\<gtr\>1>>|<row|<cell|<with|mode|text|then
    return>>|<cell|>|<cell|A<rsub|res>,S<rsub|k+1>,R<rsub|k+1>>>|<row|<cell|<with|mode|text|repeat>>|<cell|>|<cell|k\<assign\>k+1<eq-number>>>>>
  </eqnarray*>

  [FIXME: describe where <math|<wide|<wide|\<zeta\>|\<bar\>><rsup|\<chi\>>|\<bar\>>>,
  i.e. <verbatim|zvs>/<verbatim|zparams>, come from.] Note that <math|Split>
  returns <math|<wide|\<exists\><wide|\<alpha\>|\<bar\>><rsup|\<beta\><rsub|\<chi\>>>.A<rsub|\<beta\><rsub|\<chi\>>>|\<bar\>>>
  rather than <math|<wide|\<exists\><wide|\<alpha\>|\<bar\>><rsup|\<chi\>>.A<rsub|\<chi\>>|\<bar\>>>.
  This is because in case of existential type predicate variables
  <math|\<chi\><rsub|K>>, there can be multiple negative position occurrences
  <math|\<chi\><rsub|K><around*|(|\<beta\><rsub|\<chi\><rsub|K>>,\<cdummy\>|)>>
  with different <math|\<beta\><rsub|\<chi\><rsub|K>>> when the corresponding
  value is used in multiple <math|<with|math-font-series|bold|let> \<ldots\>
  <with|math-font-series|bold|in>> expressions. The variant of the algorithm
  to achieve completeness as conjectured in <cite|InvariantsTechRep2> would
  compute all answers for variants of <math|Abd> and <math|Split> algorithms
  that return multiple answers. Unary predicate variables
  <math|\<chi\><around*|(|\<beta\><rsub|\<chi\>>|)>> can also have multiple
  negative occurrences in the normalized form, but always with the same
  argument <math|\<beta\><rsub|\<chi\>>>. The substitution
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
  postcondition are connected with the argument variables. At position
  <reference|Skp> we remove the parameter constraints from solutions, since
  they will be reintroduced by <math|P<rsub|g>> with values adjusted to the
  postconditions derived in the next step.

  We start with <math|S<rsub|0>\<assign\><wide|\<top\>|\<bar\>>> and
  <math|R<rsub|0>\<assign\><wide|\<top\>|\<bar\>>>. <math|S<rsub|k>> grow in
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
  <math|c\<in\>G>. In initial iterations, when the branches
  <math|D<rsub|K><rsup|\<alpha\>>\<Rightarrow\>C<rsub|K><rsup|\<alpha\>>> are
  selected from non-recursive branches only, we include a connected atom only
  if it is satisfiable in all branches. <math|H<around*|(|R<rsub|k>,R<rsub|k+1>|)>>
  is a convergence improving heuristic, with
  <math|H<around*|(|R<rsub|k>,R<rsub|k+1>|)>=R<rsub|k+1>> for early
  iterations and ``roughly'' <math|H<around*|(|R<rsub|k>,R<rsub|k+1>|)>=R<rsub|k>\<cap\>R<rsub|k+1>>
  later.

  We introduced the <verbatim|assert false> construct into the programming
  language to indicate that a branch of code should not be reached. Type
  inference generates for it the logical connective <math|\<b-F\>>
  (falsehood). We partition the implication branches
  <math|D<rsub|i>,C<rsub|i>> into <math|<around*|{|D<rsub|i>,C<rsub|i><mid|\|>\<b-F\>\<nin\>C<rsub|i>|}>>
  which are fed to the algorithm and <math|\<Phi\><rsub|\<b-F\>>=<around*|{|<around*|(|D<rsub|i>,C<rsub|i>|)><mid|\|>\<b-F\>\<in\>C<rsub|i>|}>>.
  After the main algorithm ends we check that for each
  <math|<around*|(|D<rsub|i>,C<rsub|i>|)>\<in\>\<Phi\><rsub|\<b-F\>>>,
  \ <math|S<rsub|k><around*|(|D<rsub|i>|)>> fails. Optionally, but by
  default, we perform the check in each iteration. Turning this option
  <em|on> gives a limited way to express negative constraints. With the
  option <em|off>, the inferred type is the same as it would be without the
  impossible pattern matching branch in the program, but the check statically
  guarantees that the branch is in fact impossible. The option should be
  turned <em|off> when a single iteration (plus fallback backtracking
  described below) is insufficient to solve for the invariants.

  We implement backtracking using a tabu-search-like discard list. When
  abduction raises an exception: for example contradiction arises in the
  branches <math|S<rsub|k><around*|(|\<Phi\>|)>> passed to it, or it cannot
  find an answer and raises <verbatim|Suspect> with information on potential
  problem, we fall-back to step <math|k-1>. Similarly, with checking for
  negative constraints <em|on>, when the check of negative branches
  <math|<around*|(|D<rsub|i>,C<rsub|i>|)>\<in\>\<Phi\><rsub|\<b-F\>>>,
  \ <math|\<nvDash\>\<exists\>FV<around*|(|S<rsub|k><around*|(|D<rsub|i>|)>|)>.S<rsub|k><around*|(|D<rsub|i>|)>>
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
  similar stages. Invariants, solved by abduction:

  <\enumerate>
    <item><math|k=j<rsub|0>=0> Only term abduction -- invariants of type
    shapes -- is performed, for all branches.

    <item><math|k=j<rsub|1>=1> Both term abduction and numerical abduction
    are performed, but numerical abduction only for non-recursive branches.

    <item><math|k\<geqslant\>j<rsub|2>=2> Abduction is performed on all
    branches -- type and numerical invariants are found.
  </enumerate>

  For testing purposes, we have option <verbatim|early_num_abduction> that
  sets <math|j<rsub|2>=1>. In a single iteration, disjunction elimination
  precedes abduction.

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

  Our current choice of parameters is <math|<around*|[|k<rsub|0>;k<rsub|1>;k<rsub|2>;k<rsub|3>|]>=><verbatim|disj_step
  = [\|0;0;1;3\|]>.

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

  The code that selects <math|\<wedge\><rsub|\<chi\>><around*|(|A<rsub|\<chi\>><rsup|+>\<subset\>A<rsub|\<chi\>><rsup|cap>|)>\<wedge\>\<vDash\>\<cal-Q\>.A\<setminus\>\<cup\><rsub|\<chi\>>A<rsub|\<chi\>><rsup|+>>
  is an incremental validity checker. It starts with
  <math|A\<setminus\>\<cup\><rsub|\<chi\>>A<rsub|\<chi\>><rsup|cap>> and
  tries to add as many atoms <math|c\<in\>\<cup\><rsub|\<chi\>>A<rsub|\<chi\>><rsup|cap>>
  as possible to what in effect becomes <math|A<rsub|res>>. The remaining
  atoms are distributed among <math|A<rsub|\<beta\><rsub|\<chi\>>><rsup|+>>
  by putting them into the last <math|\<beta\><rsub|\<chi\>>> in
  <math|\<cal-Q\>>, i.e. the first <verbatim|b> in the <verbatim|q.negbs>
  list, for which <math|x<rsub|\<prec\>><around*|(|<wide|<wide|\<beta\>|\<bar\>><rsup|\<chi\>><wide|\<zeta\>|\<bar\>><rsup|\<chi\>>|\<bar\>>\<cap\>FV<around*|(|c|)>|)>\<cap\><wide|\<beta\>|\<bar\>><rsup|\<chi\>><wide|\<zeta\>|\<bar\>><rsup|\<chi\>>\<neq\>\<varnothing\>>.

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
  <reference|NumConv>, starting from the fourth iteration (<math|k=3>), we
  enforce convergence on solutions for binary predicate variables.

  Computing abduction is the ``axis'' of the main loop. If anything fails,
  the previous abduction answer is the culprit. We add the previous answer to
  the discard list and retry, without incrementing the iteration number. If
  abduction and splitting succeeds, we reset the discard list and increment
  the iteration number. We use recursion for backtracking, instead of making
  <verbatim|loop> tail-recursive.

  <\bibliography|bib|tm-plain|biblio.bib>
    <\bib-list|8>
      <bibitem*|1><label|bib-ArithQuantElim>Sergey<nbsp>Berezin,
      Vijay<nbsp>Ganesh<localize| and >David L.<nbsp>Dill.<newblock> An
      online proof-producing decision procedure for mixed-integer linear
      arithmetic.<newblock> <localize|In ><with|font-shape|italic|Proceedings
      of the 9th international conference on Tools and algorithms for the
      construction and analysis of systems>, TACAS'03, <localize|pages
      >521--536. Berlin, Heidelberg, 2003. Springer-Verlag.<newblock>

      <bibitem*|2><label|bib-ConvexHull>Komei<nbsp>Fukuda, Thomas
      M.<nbsp>Liebling<localize| and >Christine<nbsp>Lütolf.<newblock>
      Extended convex hull.<newblock> <localize|In
      ><with|font-shape|italic|Proceedings of the 12th Canadian Conference on
      Computational Geometry, Fredericton, New Brunswick, Canada, August
      16-19, 2000>. 2000.<newblock>

      <bibitem*|3><label|bib-AbductionSolvMaher>Michael<nbsp>Maher<localize|
      and >Ge<nbsp>Huang.<newblock> On computing constraint abduction
      answers.<newblock> <localize|In >Iliano<nbsp>Cervesato,
      Helmut<nbsp>Veith<localize| and >Andrei<nbsp>Voronkov<localize|,
      editors>, <with|font-shape|italic|Logic for Programming, Artificial
      Intelligence, and Reasoning>, <localize|volume> 5330<localize| of
      ><with|font-shape|italic|Lecture Notes in Computer Science>,
      <localize|pages >421--435. Springer Berlin / Heidelberg,
      2008.<newblock> 10.1007/978-3-540-89439-1<rsub|3>0.<newblock>

      <bibitem*|4><label|bib-jcaqpUNIF>Šukasz<nbsp>Stafiniak.<newblock> Joint
      constraint abduction problems.<newblock>
      <with|font-shape|italic|>2011.<newblock> The International Workshop on
      Unification.<newblock>

      <bibitem*|5><label|bib-systemTechRep>Šukasz<nbsp>Stafiniak.<newblock> A
      gadt system for invariant inference.<newblock> Manuscript,
      2012.<newblock> Available at: <hlink|http://www.ii.uni.wroc.pl/~lukstafi/pubs/EGADTs.pdf|http://www.ii.uni.wroc.pl/~lukstafi/pubs/invariants.pdf>

      <bibitem*|6><label|bib-disjelimTechRep>Šukasz<nbsp>Stafiniak.<newblock>
      Constraint disjunction elimination problems.<newblock> Manuscript,
      2013.<newblock> Available at: <hlink|http://www.ii.uni.wroc.pl/~lukstafi/pubs/disjelim.pdf|http://www.ii.uni.wroc.pl/~lukstafi/pubs/invariants.pdf><newblock>

      <bibitem*|7><label|bib-jcaqpTechRep2>Šukasz<nbsp>Stafiniak.<newblock>
      Joint constraint abduction problems.<newblock> Manuscript, 2013.
      Available at: <hlink|http://www.ii.uni.wroc.pl/~lukstafi/pubs/abduction-revised.pdf|http://www.ii.uni.wroc.pl/~lukstafi/pubs/invariants.pdf><newblock>

      <bibitem*|8><label|bib-AntiUnifAlg>B<nbsp>Østvold.<newblock> A
      functional reconstruction of anti-unification.<newblock>
      <localize|Technical Report>, Norwegian Computing Center, Oslo, Norway,
      2004.<newblock>
    </bib-list>
  </bibliography>
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
    <associate|AlienSubterms|<tuple|3.3|8>>
    <associate|Details|<tuple|5.5|17>>
    <associate|ImplSubst|<tuple|4|2>>
    <associate|Main Algo|<tuple|5.3|?>>
    <associate|MainAlgo|<tuple|5|12>>
    <associate|MainAlgoBody|<tuple|5.3|15>>
    <associate|NumConv|<tuple|4.2|11>>
    <associate|Rg|<tuple|5|15>>
    <associate|SCAlinear|<tuple|3.4|8>>
    <associate|SepProp|<tuple|5|3>>
    <associate|SepProp2|<tuple|6|?>>
    <associate|Skp|<tuple|1|15>>
    <associate|Skp1|<tuple|10|15>>
    <associate|SolSimpl|<tuple|9|12>>
    <associate|SolvedForm|<tuple|4|?>>
    <associate|SolvedFormProj|<tuple|7|?>>
    <associate|auto-1|<tuple|1|1>>
    <associate|auto-10|<tuple|3.3|8>>
    <associate|auto-11|<tuple|3.4|8>>
    <associate|auto-12|<tuple|3.5|9>>
    <associate|auto-13|<tuple|4|10>>
    <associate|auto-14|<tuple|4.1|10>>
    <associate|auto-15|<tuple|4.2|11>>
    <associate|auto-16|<tuple|4.3|11>>
    <associate|auto-17|<tuple|5|12>>
    <associate|auto-18|<tuple|5.1|12>>
    <associate|auto-19|<tuple|5.2|13>>
    <associate|auto-2|<tuple|2|2>>
    <associate|auto-20|<tuple|5.3|15>>
    <associate|auto-21|<tuple|5.4|16>>
    <associate|auto-22|<tuple|5.5|17>>
    <associate|auto-23|<tuple|5.5|17>>
    <associate|auto-3|<tuple|2.1|4>>
    <associate|auto-4|<tuple|2.1.1|4>>
    <associate|auto-5|<tuple|2.2|4>>
    <associate|auto-6|<tuple|3|5>>
    <associate|auto-7|<tuple|3.1|5>>
    <associate|auto-8|<tuple|3.1.1|7>>
    <associate|auto-9|<tuple|3.2|7>>
    <associate|bib-AbductionSolvMaher|<tuple|3|18>>
    <associate|bib-AntiUnifAlg|<tuple|8|18>>
    <associate|bib-AntiUnifInv|<tuple|2|4>>
    <associate|bib-AntiUnifPlotkin|<tuple|4|4>>
    <associate|bib-AntiUnifReynolds|<tuple|5|4>>
    <associate|bib-ArithQuantElim|<tuple|1|17>>
    <associate|bib-ConvexHull|<tuple|2|17>>
    <associate|bib-DBLP:conf/cccg/2000|<tuple|3|?>>
    <associate|bib-UnificationBaader|<tuple|1|4>>
    <associate|bib-disjelimTechRep|<tuple|6|18>>
    <associate|bib-jcaqpTechRep|<tuple|8|4>>
    <associate|bib-jcaqpTechRep2|<tuple|7|18>>
    <associate|bib-jcaqpUNIF|<tuple|4|18>>
    <associate|bib-simonet-pottier-hmg-toplas|<tuple|6|4>>
    <associate|bib-systemTechRep|<tuple|5|18>>
  </collection>
</references>

<\auxiliary>
  <\collection>
    <\associate|bib>
      ESOP2014

      ESOP2014

      jcaqpUNIF

      AbductionSolvMaher

      AbductionSolvMaher

      jcaqpTechRep2

      ArithQuantElim

      ArithQuantElim

      disjelimTechRep

      AntiUnifAlg

      ConvexHull

      ConvexHull

      InvariantsTechRep2

      InvariantsTechRep2

      InvariantsTechRep2
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
      for terms <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-9>>

      <with|par-left|<quote|1.5fn>|3.3<space|2spc>Abduction for terms with
      Alien Subterms <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-10>>

      <with|par-left|<quote|1.5fn>|3.4<space|2spc>Simple constraint abduction
      for linear arithmetic <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-11>>

      <with|par-left|<quote|1.5fn>|3.5<space|2spc>Joint constraint abduction
      for linear arithmetic <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-12>>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|4<space|2spc>Disjunction
      Elimination> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-13><vspace|0.5fn>

      <with|par-left|<quote|1.5fn>|4.1<space|2spc>Extended convex hull
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-14>>

      <with|par-left|<quote|1.5fn>|4.2<space|2spc>Issues in inferring
      postconditions <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-15>>

      <with|par-left|<quote|1.5fn>|4.3<space|2spc>Abductive disjunction
      elimination under quantifier prefix
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-16>>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|5<space|2spc>Solving
      for Predicate Variables> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-17><vspace|0.5fn>

      <with|par-left|<quote|1.5fn>|5.1<space|2spc>Invariant Parameter
      Candidates <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-18>>

      <with|par-left|<quote|1.5fn>|5.2<space|2spc>Solving for Predicates in
      Negative Positions <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-19>>

      <with|par-left|<quote|1.5fn>|5.3<space|2spc>Solving for Existential
      Types Predicates and Main Algorithm
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-20>>

      <with|par-left|<quote|1.5fn>|5.4<space|2spc>Stages of iteration
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-21>>

      <with|par-left|<quote|1.5fn>|5.5<space|2spc>Implementation details
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-22>>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|Bibliography>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-23><vspace|0.5fn>
    </associate>
  </collection>
</auxiliary>