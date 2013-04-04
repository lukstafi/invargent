<TeXmacs|1.0.7.16>

<style|article>

<\body>
  <doc-data|<doc-title|InvarGenT: Implementation>||<doc-author-data|<author-name|Šukasz
  Stafiniak>|<\author-address>
    Institute of Computer Science

    University of Wrocªaw
  </author-address>>>

  <\abstract>
    InvarGenT is a proof-of-concept system for invariant generation by full
    type inference with Guarded Algebraic Data Types and existential types
    encoded as automatically generated GADTs. This implementation
    documentation focuses on source code, refers to separate technical
    reports on theory and algorithms.
  </abstract>

  <section|Data Structures and Concrete Syntax>

  Following <cite|systemTechRep>, we have the following nodes in the abstract
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
    Function defined by cases. Concrete syntax: for single branching via
    <verbatim|fun> keyword, e.g. <verbatim|fun x y -\<gtr\> f x y> translates
    as <math|\<lambda\><around*|(|x.\<lambda\><around*|(|y.<around*|(|f x|)>
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
    Concrete syntax: <verbatim|function> and <verbatim|ematch> keywords --
    e.g. <verbatim|function Nil -\<gtr\> >...<verbatim| \| Cons (x,xs)
    -\<gtr\> >...; <verbatim|ematch l with >... Parsing introduces a fresh
    identifier for <math|K>. Constructor: <verbatim|ExLam>.

    <item*|<verbatim|ExLetIn>><math|<with|math-font-series|bold|let>
    p=e<rsub|1> <with|math-font-series|bold|in> e<rsub|2>:> Elimination of
    existentially quantified type. \ Concrete syntax: e.g. <verbatim|let v =
    f e >...<verbatim| in >... Constructor: <verbatim|Letin>.
  </description>

  We also have one sort-specific type of expression, numerals.

  For type and formula connectives, we have ASCII and unicode syntactic
  variants (the difference is only in lexer). Quantified variables can be
  space or comma separated. The table below is analogous to information for
  expressions above. Existential type construct introduces a fresh identifier
  for <math|K>. The abstract syntax of types is not sort-safe, but type
  variables carry sorts which are inferred after parsing. Existential type
  occurrence in user code introduces a fresh identifier, a new type
  constructor in global environment <verbatim|newtype_env>, and a new value
  constructor in global environment <verbatim|newcons_env> -- the value
  constructor purpose is to store the content of the existential type, it is
  not used in the program.

  <block|<tformat|<cwith|1|1|2|2|cell-halign|c>|<cwith|1|1|1|1|cell-halign|l>|<table|<row|<cell|type
  variable>|<cell|<math|x>>|<cell|<verbatim|x>>|<cell|>|<cell|<verbatim|TVar>>>|<row|<cell|type
  constructor>|<cell|<math|List>>|<cell|<verbatim|List>>|<cell|>|<cell|<verbatim|TCons(CNamed>...<verbatim|)>>>|<row|<cell|number
  (type)>|<cell|<math|7>>|<cell|<verbatim|7>>|<cell|>|<cell|<verbatim|NCst>>>|<row|<cell|numeral
  (expr.)>|<cell|<math|7>>|<cell|<verbatim|7>>|<cell|>|<cell|<verbatim|Num>>>|<row|<cell|numerical
  sum (type)>|<cell|<math|a+b>>|<cell|<verbatim|a+b>>|<cell|>|<cell|<verbatim|Nadd>>>|<row|<cell|existential
  type>|<cell|<math|\<exists\>\<alpha\>\<beta\><around*|[|a\<leqslant\>\<beta\>|]>.\<tau\>>>|<cell|<verbatim|ex
  a b [a\<less\>=b].t>>|<cell|<verbatim|<math|\<exists\>>a,b[a<math|\<leq\>>b].t>>|<cell|<verbatim|TCons(Extype>...<verbatim|)>>>|<row|<cell|type
  sort>|<cell|<math|s<rsub|ty>>>|<cell|<verbatim|type>>|<cell|>|<cell|<verbatim|Type_sort>>>|<row|<cell|number
  sort>|<cell|<math|s<rsub|R>>>|<cell|<verbatim|num>>|<cell|>|<cell|<verbatim|Num_sort>>>|<row|<cell|function
  type>|<cell|<math|\<tau\><rsub|1>\<rightarrow\>\<tau\><rsub|2>>>|<cell|<verbatim|t1
  -\<gtr\> t2>>|<cell|<verbatim|t1 <math|\<rightarrow\>><verbatim|
  t2>>>|<cell|<verbatim|Fun>>>|<row|<cell|equation>|<cell|<math|a<wide|=|\<dot\>>b>>|<cell|<verbatim|a
  = b>>|<cell|>|<cell|<verbatim|Eqty>>>|<row|<cell|inequation>|<cell|<math|a\<leqslant\>b>>|<cell|<verbatim|a
  \<less\>= b>>|<cell|<verbatim|a <math|\<leq\>>
  b>>|<cell|<verbatim|Leq>>>|<row|<cell|conjunction>|<cell|<math|\<varphi\><rsub|1>\<wedge\>\<varphi\><rsub|2>>>|<cell|<verbatim|a=b
  && b=a>>|<cell|<verbatim|a=b <math|\<wedge\>> b=a>>|<cell|built-in
  lists>>>>>

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
  inferred existential types, into the list of toplevel items, which allows
  to follow <cite|systemTechRep> despite removing <verbatim|extype> construct
  from the language. It also faciliates exporting inference results as OCaml
  source code.

  Functions <verbatim|constr_gen_pat> and <verbatim|envfrag_gen_pat> compute
  formulas according to table 2 in <cite|systemTechRep>, and
  <verbatim|constr_gen_expr> computes table 3. We preserve the FOL language
  presentation in the type <verbatim|cnstrnt>, only limiting the expressivity
  in ways not requiring any preprocessing. The toplevel definitions (from
  type <verbatim|struct_item>) <verbatim|LetRecVal> and <verbatim|LetVal> are
  processed by <verbatim|constr_gen_letrec> and <verbatim|constr_gen_let>
  respectively. They are analogous to <verbatim|Letrec> and <verbatim|Letin>
  or a <verbatim|Lam> clause. We do not cover toplevel definitions in our
  formalism (without even a rudimentary module system, the toplevel is a
  matter of pragmatics rather than semantics).

  Toplevel definitions (and in future, structure items) are intended as
  boundaries for constraint solving. This way the programmer can decompose
  functions that could be too complex for the solver. <verbatim|LetRecVal>
  only binds a single identifier, while <verbatim|LetVal> binds variables in
  a pattern. To preserve the flexibility of expression-level pattern
  matching, <verbatim|LetVal> has to pack the constraints
  <math|<around*|\<llbracket\>|\<Sigma\>\<vdash\>p\<uparrow\>\<alpha\>|\<rrbracket\>>>
  which the pattern makes available, into existential types. Each pattern
  variable is a separate entry to the global environment, therefore the
  connection between them is lost.

  The formalism (in interests of parsimony) requires that only values of
  existential types be bound using <verbatim|Letin> syntax. The
  implementation is enhanced in this regard: if the normalization step cannot
  determine which existential type is being eliminated, the constraint is
  replaced by one that would be generated for a pattern matching branch. This
  recovers the common use of the <verbatim|let>...<verbatim|in> syntax, with
  exception of polymorphic <verbatim|let> cases, where <verbatim|let rec>
  still needs to be used.

  In the formalism, we use <math|\<cal-E\>=<around*|{|\<varepsilon\><rsub|K>,\<chi\><rsub|K><mid|\|>K\<colons\>\<forall\>\<alpha\>\<gamma\><around|[|\<chi\><rsub|K><around*|(|\<alpha\>,\<gamma\>|)>|]>.\<gamma\>\<rightarrow\>\<varepsilon\><rsub|K><around*|(|\<alpha\>|)>\<in\>\<Sigma\>|}>>
  for brevity, as if all existential types
  <math|\<varepsilon\><rsub|K><around*|(|\<alpha\>|)>> were related with a
  predicate variable <math|\<chi\><rsub|K><around*|(|\<alpha\>,\<gamma\>|)>\<nosymbol\>>.
  In the implementation, we have user-defined existential types with explicit
  constraints in addition to inferred existential types. We keep track of
  existential types in cell <verbatim|ex_types>, storing arbitrary
  constraints. For <verbatim|LetVal>, we form existential types after solving
  the generated constraint, to have less intermediate variables in them. The
  first argument of the predicate variable
  <math|\<chi\><rsub|K><around*|(|\<alpha\>,\<gamma\>|)>\<nosymbol\>>
  provides an ``escape route'' for free variables, e.g. precondition
  variables used in postcondition. It is used for convenience in the
  formalism. In the implementation, after the constraints are solved, we
  expand it to pass each free variable as a separate parameter, to increase
  readability of exported OCaml code.

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

    <item>perform backtracking search for the first solution that satisfies
    the subsequent program.
  </enumerate>

  We use an enhanced variant of approach 1 as it is closest to traditional
  type inference workflow. Upon ``multiple solutions'' failure the user can
  add <verbatim|assert> clauses (e.g. <verbatim|assert false> stating that a
  program branch is impossible), and <verbatim|test> clauses. The
  <verbatim|test> clauses are boolean expressions with operational semantics
  of run-time tests: the test clauses are executed right after the definition
  is executed, and run-time error is reported when a clause returns
  <verbatim|false>. The constraints from test clauses are included in the
  constraint for the toplevel definition, thus propagate more efficiently
  than backtracking would. The <verbatim|assert> clauses are:
  <verbatim|assert = type e1 e2> which translates as equality of types of
  <verbatim|e1> and <verbatim|e2>, <verbatim|assert false> which translates
  as <verbatim|CFalse>, and <verbatim|assert e1 \<less\>= e2>, which
  translates as inequality <math|n<rsub|1>\<leqslant\>n<rsub|2>> assuming
  that <verbatim|e1> has type <verbatim|Num n1> and <verbatim|e2> has type
  <verbatim|Num n2>.

  <subsection|Normalization>

  Rather than reducing to prenex-normal form as in our formalization, we
  preserve the scope relations and return a <verbatim|var_scope>-producing
  variable comparison function. Also, since we use
  <verbatim|let>-<verbatim|in> syntax to both eliminate existential types and
  for traditional (but not polymorphic) binding, we drop the <verbatim|Or1>
  constraints (in the formalism they ensure that <verbatim|let>-<verbatim|in>
  binds an existential type). During normalization, we compute unifiers of
  the type sort part of conclusions. This faciliates solving of the
  disjunctions in <verbatim|ImplOr2> constraints. We monitor for
  contradiction in conclusions, so that we can stop the
  <verbatim|Contradiction> exception and remove an implication in case the
  premise is also contradictory.

  Releasing constraints \ from under <verbatim|ImplOr2>, when the
  corresponding <verbatim|let>-<verbatim|in> is interpreted as standard
  binding (instead of eliminating existential type), violates
  declarativeness. We cannot include all the released constraints in
  determining whether non-nested <verbatim|ImplOr2> constraints should be
  interpreted as eliminating existential types. While we could be more
  ``aggresive'' (we can modify the implementation to release the constraints
  one-by-one), it shouldn't be problematic, because nesting of
  <verbatim|ImplOr2> corresponds to nesting of <verbatim|let>-<verbatim|in>
  definitions.

  <section|Abduction>

  The formal specification of abduction at <cite|jcaqpUNIF> provides a scheme
  for combining sorts that substitutes number sort subterms from type sort
  terms with variables, so that a single-sort term abduction algorithm can be
  called. Since we implement term abduction over the two-sorted datatype
  <verbatim|typ>, we keep these <em|alien subterms> in terms passed to term
  abduction.

  \;

  <\bibliography|bib|tm-plain|biblio.bib>
    <\bib-list|1>
      <bibitem*|1><label|bib-systemTechRep>Šukasz<nbsp>Stafiniak.<newblock> A
      gadt system for invariant inference.<newblock> Manuscript,
      2012.<newblock> Available at: <hlink|http://www.ii.uni.wroc.pl/~lukstafi/pubs/EGADTs.pdf|http://www.ii.uni.wroc.pl/~lukstafi/pubs/invariants.pdf>
    </bib-list>
  </bibliography>
</body>

<\initial>
  <\collection>
    <associate|sfactor|4>
  </collection>
</initial>

<\references>
  <\collection>
    <associate|ImplSubst|<tuple|4|2>>
    <associate|SepProp|<tuple|5|3>>
    <associate|SepProp2|<tuple|6|?>>
    <associate|SolvedForm|<tuple|4|?>>
    <associate|SolvedFormProj|<tuple|7|?>>
    <associate|auto-1|<tuple|1|1>>
    <associate|auto-2|<tuple|2|2>>
    <associate|auto-3|<tuple|2.1|3>>
    <associate|auto-4|<tuple|3|3>>
    <associate|auto-5|<tuple|3|2>>
    <associate|auto-6|<tuple|3|4>>
    <associate|auto-7|<tuple|3|4>>
    <associate|bib-AntiUnifInv|<tuple|2|4>>
    <associate|bib-AntiUnifPlotkin|<tuple|4|4>>
    <associate|bib-AntiUnifReynolds|<tuple|5|4>>
    <associate|bib-ConvexHull|<tuple|3|4>>
    <associate|bib-DBLP:conf/cccg/2000|<tuple|3|?>>
    <associate|bib-UnificationBaader|<tuple|1|4>>
    <associate|bib-jcaqpTechRep|<tuple|8|4>>
    <associate|bib-jcaqpUNIF|<tuple|7|4>>
    <associate|bib-simonet-pottier-hmg-toplas|<tuple|6|4>>
    <associate|bib-systemTechRep|<tuple|1|3>>
  </collection>
</references>

<\auxiliary>
  <\collection>
    <\associate|bib>
      systemTechRep

      systemTechRep

      systemTechRep
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

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|3<space|2spc>Abduction>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-4><vspace|0.5fn>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|Bibliography>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-5><vspace|0.5fn>
    </associate>
  </collection>
</auxiliary>