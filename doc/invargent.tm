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
  <verbatim|constr_gen_expr> computes table 3. Due to the presentation of the
  type system, we ensure in <verbatim|ValConstr> that bounds on type
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

  The formalism (in interests of parsimony) requires that only values of
  existential types be bound using <verbatim|Letin> syntax. The
  implementation is enhanced in this regard: if the normalization step cannot
  determine which existential type is being eliminated, the constraint is
  replaced by one that would be generated for a pattern matching branch. This
  recovers the common use of the <verbatim|let>...<verbatim|in> syntax, with
  exception of polymorphic <verbatim|let> cases, where <verbatim|let rec>
  still needs to be used.

  In the formalism, we use <math|\<cal-E\>=<around*|{|\<varepsilon\><rsub|K>,\<chi\><rsub|K><mid|\|>K\<colons\>\<forall\>\<alpha\>\<gamma\><around|[|\<chi\><rsub|K><around*|(|\<gamma\>,\<alpha\>|)>|]>.\<gamma\>\<rightarrow\>\<varepsilon\><rsub|K><around*|(|\<alpha\>|)>\<in\>\<Sigma\>|}>>
  for brevity, as if all existential types
  <math|\<varepsilon\><rsub|K><around*|(|\<alpha\>|)>> were related with a
  predicate variable <math|\<chi\><rsub|K><around*|(|\<gamma\>,\<alpha\>|)>\<nosymbol\>>.
  In the implementation, we have user-defined existential types with explicit
  constraints in addition to inferred existential types. We keep track of
  existential types in cell <verbatim|ex_types>, storing arbitrary
  constraints. For <verbatim|LetVal>, we form existential types after solving
  the generated constraint, to have less intermediate variables in them. The
  first argument of the predicate variable
  <math|\<chi\><rsub|K><around*|(|\<gamma\>,\<alpha\>|)>\<nosymbol\>>
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

  We treat a chain of single branch functions with only <verbatim|assert
  false> in the body of the last function specially. We put all information
  about the type of the functions in the premise of the generated constraint.
  Therefore the user can use them to exclude unintended types. See the
  example <verbatim|equal_assert.gadt>.

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

  <subsection|Simplification>

  After normalization, we simplify the constraints by [TODO: explain]
  applying shared constraints, and removing redundant atoms. We remove atoms
  that bind variables not occurring anywhere else in the constraint, and in
  case of atoms not in premises, not universally quantified. The
  simplification step is not currently proven correct and might need
  refining.

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
  <math|\<b-U\><rsub|><around*|(|A<around*|(|D\<wedge\>C|)>|)>>, where
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

  Although our formalism stresses the possibility of infinite number of
  abduction answers, there is always finite number of <em|fully maximal>
  answers, one of which we compute. The formalism suggests computing them
  lazily using streams, and then testing all combinations -- generate and
  test scheme. Instead, we use a search scheme that tests as soon as
  possible. The simple abduction algorithm takes a partial solution -- a
  conjunction of candidate solutions for some other branches -- and checks if
  the solution being generated is satisfiable together with the candidate
  partial solution. The algorithm also takes several indicators to let it
  select the expected answer:

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

    <item>a discard list that contains answer atoms -- substitution terms --
    disallowed in the pursued solution. The main algorithm will pass the
    answer atoms from previous iterations as a discard list.
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

  Besides multisort joint constraint abduction <verbatim|abd> we also provide
  multisort simple fully maximal constraint abduction <verbatim|abd_s>.

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
    </enumerate>

    <item>Choices 2-5 are guarded by <verbatim|try>-<verbatim|with>, as tests
    raise <verbatim|Contradiction> if they fail, choice 1 only tests
    <verbatim|implies_concl> which returns a boolean.

    <item>We provide an option <verbatim|more_general>, which when set to
    false reorders the choices into: 1, 4, 2, 3, 5 -- pushing 4 up minimizes
    the amount of branching in 5.

    <item>We recompute modifications of parameters due to partial answer,
    e.g. <verbatim|cparams>, for clarity of joint constraint abduction; we
    could compute them incrementally and pass around.

    <item>We sort the initial candidates by decreasing size.
  </itemize>

  The above ordering of choices ensures that more general answers are tried
  first. Moreover:

  <\itemize>
    <item>choice 1 could be dropped as it is equivalent to choice 2 applied
    on the root term;

    <item>choices 4 and 5 could be reordered but having choice 4 as soon as
    possible is important for efficiency.
  </itemize>

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

  <subsection|Abduction for terms with Alien Subterms>

  The JCAQPAS problem is more complex than simply substituting alien subterms
  with variables and performing joint constraint abduction on resulting
  implications. The ability to ``outsource'' constraints to the alien sorts
  enables more general answers to the target sort, in our case the term
  algebra <math|T<around*|(|F|)>>. Consider a case where one of the
  implications, for example <math|\<beta\><wide|=|\<dot\>>f<around*|(|\<beta\><rsub|1>,\<beta\><rsub|2>|)>\<Rightarrow\>\<beta\><rsub|1><wide|=|\<dot\>>\<beta\><rsub|2>>,
  requires <math|\<exists\>\<alpha\>.\<beta\><wide|=|\<dot\>>f<around*|(|\<alpha\>,\<alpha\>|)>>
  in the answer. Under JCAQPAS, we can instead answer
  <math|\<exists\>\<alpha\><rsub|1>\<alpha\><rsub|2>.\<beta\><wide|=|\<dot\>>f<around*|(|N<around*|(|\<alpha\><rsub|1>|)>,N<around*|(|\<alpha\><rsub|2>|)>|)>,<around*|(|\<alpha\><rsub|1><wide|=|\<dot\>>\<alpha\><rsub|2>,\<ldots\>|)>>,
  where we output <math|\<alpha\><rsub|1><wide|=|\<dot\>>\<alpha\><rsub|2>>
  as alien subterm equation required for this particular branch. Note that
  the resulting answer is just as general and is independent of which
  <math|N:s<rprime|'>\<rightarrow\>s<rsub|ty>\<in\>F> we pick. As in joint
  constraint abduction in general, the proliferation of simple abduction
  answers is not problematic in itself, but because it enlarges the search
  space when looking for a solution of the joint constraints.

  We solve the problem by preserving the joint abduction for terms algorithm,
  and after a solution <math|\<exists\><wide|\<alpha\>|\<bar\>>.A> is found,
  we ``<em|dissociate>'' the alien subterms (including variables) in <math|A>
  as follows. We replace every alien subterm <math|n<rsub|s>> in <math|A>
  (including variables, even parameters) with a fresh variable
  <math|\<alpha\><rsub|s>>, which results in <math|A<rprime|'>> (in
  particular <math|A<rprime|'><around*|[|<wide|\<alpha\><rsub|s>|\<bar\>>\<assign\><wide|n<rsub|s>|\<bar\>>|]>=A>).
  Subsets <math|A<rsub|i>\<subset\><wide|\<alpha\><rsub|s><wide|=|\<dot\>>n<rsub|s>|\<bar\>>>
  such that <math|\<exists\><wide|\<alpha\>|\<bar\>><wide|\<alpha\><rsub|s>|\<bar\>>.A<rprime|'>,<wide|A<rsub|i>|\<bar\>>>
  is a JCAQPAS answer will be recovered automatically by a residuum-finding
  process at the end of <verbatim|ans_typ>. This process is needed regardless
  of the ``dissociation'' issue, to uncover the full content of numeric sort
  constraints.

  <subsection|Simple constraint abduction for linear arithmetic>

  We use <em|Fourier-Motzkin elimination>. To avoid complexities we initially
  only handle rational number domain, but if need arises we will extend to
  integers using <em|Omega-test> procedure as presented in
  <cite|ArithQuantElim>. The major operations are:

  <\itemize>
    <item><em|Elimination> of a variable takes an equation and selects a
    variable that isn't upstream of any other variable of the equation, and
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

  There are usually infinitely many answers to the simple constraint
  abduction problem whenever equations or implicit equalities are involved.
  The algorithm we develop follows our presentation in <cite|jcaqpTechRep2>,
  but only considers answers achieved from canonical answers (cf.
  <cite|jcaqpTechRep2>) by substitution of some occurrences of variables
  according to some equations in the premise.

  When we derive a substitution from a set of equations, we eliminate
  variables that are maximally downstream, and using a fixed total order
  among variables in the same quantifier alternation. Algorithm:

  <\enumerate>
    <item>Let <math|A<rsub|i>=A<rsup|=><rsub|i>\<wedge\>A<rsup|\<leqslant\>><rsub|i>>
    be the answer to previous SCA problems where <math|A<rsup|=><rsub|i>> are
    equations and <math|A<rsup|\<leqslant\>><rsub|i>> are inequalities, and
    <math|D\<Rightarrow\>C> be the current problem.

    <item>Let <math|D<rsup|<wide|=|\<dot\>>>\<wedge\>D<rsup|=>\<wedge\>D<rsup|\<leqslant\>>=A<rsub|i><rsup|=><around*|(|D|)>>,
    <math|C<rsup|<wide|=|\<dot\>>>\<wedge\>C<rsup|=>\<wedge\>C<rsup|\<leqslant\>>=A<rsub|i><rsup|=><around*|(|C|)>>
    and <math|DC<rsup|<wide|=|\<dot\>>>\<wedge\>DC<rsup|=>\<wedge\>DC<rsup|\<leqslant\>>=A<rsub|i><rsup|=><around*|(|D\<wedge\>C|)>>,
    where <math|D<rsup|<wide|=|\<dot\>>>>, resp.
    <math|C<rsup|<wide|=|\<dot\>>>>, <math|DC<rsup|<wide|=|\<dot\>>>> are
    equations, <math|D<rsup|=>>, resp. <math|C<rsup|=>>, <math|DC<rsup|=>>
    are implicit equalities of <math|A<rsub|i><rsup|=><around*|(|D|)>>, resp.
    <math|A<rsub|i><rsup|=><around*|(|C|)>>,
    <math|A<rsub|i><rsup|=><around*|(|D\<wedge\>C|)>>.

    <item>Let <math|\<theta\>=DC<rsup|<wide|=|\<dot\>>>\<wedge\>DC<rsup|=>>.
    Let <math|D<rprime|'>=\<theta\><around*|(|D<rsup|\<leqslant\>>|)>> and
    <math|C<rprime|'>=\<theta\><around*|(|DC<rsup|\<leqslant\>>|)>>, where
    <math|\<theta\><around*|(|\<nosymbol\>\<cdummy\>|)>> is the substitution
    corresponding to <math|\<theta\>>.

    <item>Let <math|A<rsup|\<leqslant\>>> be a core of <math|C<rprime|'>>
    w.r.t. <math|D<rprime|'>>. (Choice point 1.)

    <item>Let <math|A<rsup|=>=<around*|[|D<rsup|<wide|=|\<dot\>>>\<wedge\>D<rsup|=>|]><around*|(|\<theta\>|)>>,
    where <math|<around*|[|D<rsup|<wide|=|\<dot\>>>\<wedge\>D<rsup|=>|]><around*|(|\<cdot\>|)>>
    is a substitution corresponding to equations in
    <math|D<rsup|<wide|=|\<dot\>>>\<wedge\>D<rsup|=>>.

    <item>Let <math|A<rsup|=><rprime|'>> resp.
    <math|A<rsup|\<leqslant\>><rprime|'>> be <math|A<rsup|=>> resp.
    <math|A<rsup|\<leqslant\>>> with some occurrences of variables
    substituted according to some equations in
    <math|D<rsup|<wide|=|\<dot\>>>\<wedge\>D<rsup|=>>, but disregarding the
    order of variables. In case of single-variable equations, we can also
    substitute some constants using some such equations. (Choice point 2.)

    <item>Check validation condition for <math|A<rsub|i>\<wedge\>A<rsup|\<leqslant\>><rprime|'>\<wedge\>A<rsup|=><rprime|'>>,
    and skipping answers.

    <item>The answers are <math|A<rsub|i+1>=A<rsub|i>\<wedge\>A<rsup|\<leqslant\>><rprime|'>\<wedge\>A<rsup|=><rprime|'>>.
  </enumerate>

  Actually in the initial implementation, in step (6) we discard even more
  solutions. Rather than replacing some occurrences of variables in a given
  choice, we perform a full substitution: either replace all occurrences
  using a given equation, or none. To handle substitutions of constants, we
  split single-variable equations into <em|substitutions of 0>:
  <math|x<wide|=|\<dot\>>0>, and <em|substitutions of 1>:
  <math|x<wide|=|\<dot\>>c> for <math|c\<neq\>0>. To any equation or
  inequality we apply at most one substitution of 0. In case a given equation
  or inequality has a non-zero constant term, we apply at most one
  substitution of 1. Substitutions of 0 and 1 are handled together with the
  standard variable substitutions.

  \ We might revert to a more thorough exploration of various linear
  combinations, exploring more answers indicated in <cite|jcaqpTechRep2>. The
  effort needs to be justified by practical examples.

  We use the <verbatim|nums> library for exact precision rationals.

  <subsection|Joint constraint abduction for linear arithmetic>

  We follow the scheme we established in joint constraint abduction for
  terms.

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
  and implicit inequalities which contain a variable not shared by all
  <math|D<rsub|i>>, by substituting out such variables. We pass the resulting
  inequalities to the convex hull algorithm.

  <section|Solving for Predicate Variables>

  As we decided to provide the first solution to abduction problems, we
  similarly simplify the task of solving for predicate variables. Instead of
  a tree of solutions being refined, we have a single sequence which we
  unfold until reaching fixpoint or contradiction. Another choice point
  besides abduction in the original algorithm is the selection of invariants
  that leaves a consistent subset of atoms as residuum. Here we also select
  the first solution found. In future, we might introduce some form of
  backtracking, if the loss of completeness outweighs the computational cost.

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
  <math|Split<around*|(|\<cal-Q\>,<wide|\<alpha\>|\<bar\>>,A,<wide|<wide|\<beta\>|\<bar\>><rsup|\<chi\>>|\<bar\>>,<wide|<wide|\<zeta\>|\<bar\>><rsup|\<chi\>>|\<bar\>>,<wide|A<rsub|\<chi\>><rsup|0>|\<bar\>>|)>>.
  Note that due to existential types predicates, we actually compute
  <math|Split<around*|(|\<cal-Q\>,<wide|\<alpha\>|\<bar\>>,A,<wide|<wide|\<beta\>|\<bar\>><rsup|\<beta\><rsub|\<chi\>>>|\<bar\>>,<wide|<wide|\<zeta\>|\<bar\>><rsup|\<beta\><rsub|\<chi\>>>|\<bar\>>,<wide|A<rsub|\<beta\><rsub|\<chi\>>><rsup|0>|\<bar\>>|)>>,
  i.e. we index by <math|\<beta\><rsub|\<chi\>>> (which can be multiple for a
  single <math|\<chi\>>) rather than <math|\<chi\>>. We retain the notation
  from <cite|InvariantsTechRep2> here as it better conveys the intent. We do
  not pass quantifiers around to reflect the source code: the helper function
  <verbatim|loop avs ans sol> of function <verbatim|split> corresponds to
  <math|Split<around*|(|<wide|\<alpha\>|\<bar\>>,A,<wide|A<rsub|\<beta\><rsub|\<chi\>>><rsup|0>|\<bar\>>|)>>.

  <\enumerate>
    <item><math|<tabular|<tformat|<table|<row|<cell|\<alpha\>\<prec\>\<beta\>>|<cell|\<equiv\>>|<cell|\<alpha\>\<less\><rsub|\<cal-Q\>>\<beta\>\<vee\><around*|(|\<alpha\>\<leqslant\><rsub|\<cal-Q\>>\<beta\>\<wedge\>\<beta\>\<nless\><rsub|\<cal-Q\>>\<alpha\>\<wedge\>\<alpha\>\<in\><wide|<wide|\<beta\>|\<bar\>><rsup|\<chi\>>|\<bar\>>\<wedge\>\<beta\>\<nin\><wide|<wide|\<beta\>|\<bar\>><rsup|\<chi\>>|\<bar\>>|)>>>>>>>
    The variables <math|<wide|<wide|\<beta\>|\<bar\>><rsup|\<chi\>>|\<bar\>>>
    are the answer variables of the solution from the previous round. We need
    to keep them apart from other variables even when they're not separated
    by quantifier alternation.

    <item><math|<tabular|<tformat|<table|<row|<cell|A<rsub|0>>|<cell|=>|<cell|A\\<around*|{|\<beta\><wide|=|\<dot\>>\<alpha\>\<in\>A<mid|\|>\<beta\>\<in\><wide|<wide|\<beta\>|\<bar\>><rsup|\<chi\>>|\<bar\>>\<wedge\><around*|(|\<exists\>\<alpha\>|)>\<in\>\<cal-Q\>\<wedge\>\<beta\>\<prec\>\<alpha\>|}>>>>>>>
    We handle information carried in <math|\<beta\><wide|=|\<dot\>>\<alpha\>>
    by substituting <math|\<alpha\>> with <math|\<beta\>>.

    <item><math|<tabular|<tformat|<table|<row|<cell|A<rsub|\<chi\>><rsup|cap>>|<cell|=>|<cell|<around*|{|c\<in\>A<rsub|0><mid|\|>max<rsub|\<prec\>><around*|(|<wide|<wide|\<beta\>|\<bar\>><rsup|\<chi\>><wide|\<zeta\>|\<bar\>><rsup|\<chi\>>|\<bar\>>\<cap\>FV<around*|(|c|)>|)>\<cap\><wide|\<beta\>|\<bar\>><rsup|\<chi\>><wide|\<zeta\>|\<bar\>><rsup|\<chi\>>\<neq\>\<varnothing\>|}>>>>>>>
    All of the atoms to consider incorporating in invariants for
    <math|\<chi\>>.

    <item><math|<tabular|<tformat|<table|<row|<cell|<with|mode|text|for one
    ><wide|A<rsub|\<chi\>><rsup|+>|\<bar\>><with|mode|text| minimal w.r.t.
    >\<subset\><with|mode|text| such that>>|<cell|>|<cell|\<wedge\><rsub|\<chi\>><around*|(|A<rsub|\<chi\>><rsup|+>\<subset\>A<rsub|\<chi\>><rsup|cap>|)>\<wedge\>\<vDash\>\<cal-Q\>.A\<setminus\>\<cup\><rsub|\<chi\>>A<rsub|\<chi\>><rsup|+>:>>>>>>
    Select invariants such that the residuum
    <math|A\<setminus\>\<cup\><rsub|\<chi\>>A<rsub|\<chi\>><rsup|+>> is
    consistent. The final residuum <math|A<rsub|res>> represents the global
    constraints, the solution for global type variables. The solutions
    <math|A<rsub|\<chi\>><rsup|+>> represent the invariants, the solution for
    invariant type parameters.

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

    <item><math|<tabular|<tformat|<table|<row|<cell|A<rsub|res><rprime|'>,<wide|\<exists\><wide|\<alpha\>|\<bar\>><rprime|'><rsup|\<chi\>>.A<rsub|\<chi\>><rprime|'>|\<bar\>>>|<cell|=>|<cell|Split<around*|(|<wide|\<alpha\>|\<bar\>>\<setminus\>\<cup\><rsub|\<chi\>><wide|\<alpha\>|\<bar\>><rsup|\<chi\>>,A<rsub|res>,<wide|A<rsub|\<chi\>>|\<bar\>>|)>>>>>>>
    Recursive call includes <math|<wide|\<alpha\>|\<bar\>><rsup|\<chi\>><rsub|+>>
    in <math|<wide|\<beta\>|\<bar\>><rsup|\<chi\>>> so that, among other
    things, <math|A<rsub|+>> are redistributed into <math|A<rsub|\<chi\>>>.

    <item><math|<tabular|<tformat|<table|<row|<cell|<with|mode|text|return>>|<cell|>|<cell|A<rsub|res><rprime|'>,<wide|\<exists\><wide|\<alpha\>|\<bar\>><rsup|\<chi\>><wide|\<alpha\>|\<bar\>><rprime|'><rsup|\<chi\>>.A<rsub|\<chi\>><rprime|'>|\<bar\>>>>>>>>

    <item><math|<tabular|<tformat|<table|<row|<cell|<with|mode|text|else
    return>>|<cell|>|<cell|A<rsub|res>,<wide|\<exists\><wide|\<alpha\>|\<bar\>><rsup|\<chi\>>.A<rsub|\<chi\>>|\<bar\>>>>>>>>
    Note that <math|<wide|\<alpha\>|\<bar\>>\<setminus\>\<cup\><rsub|\<chi\>><wide|\<alpha\>|\<bar\>><rsup|\<chi\>>>
    does not contain the current <math|<wide|\<beta\>|\<bar\>><rsup|\<chi\>>>,
    because <math|<wide|\<alpha\>|\<bar\>>> does not contain it initially and
    the recursive call maintains that: <math|<wide|\<alpha\>|\<bar\>>\<assign\><wide|\<alpha\>|\<bar\>>\<setminus\>\<cup\><rsub|\<chi\>><wide|\<alpha\>|\<bar\>><rsup|\<chi\>>,<wide|\<beta\>|\<bar\>><rsup|\<chi\>>\<assign\><wide|\<beta\>|\<bar\>><rsup|\<chi\>><wide|\<alpha\>|\<bar\>><rsup|\<chi\>>>.
  </enumerate>

  Finally we define <math|Split<around*|(|<wide|\<alpha\>|\<bar\>>,A|)>\<assign\>Split<around*|(|<wide|\<alpha\>|\<bar\>>,A,<wide|\<top\>|\<bar\>>|)>>.
  The complete algorithm for solving predicate variables is presented in the
  next section.

  <subsection|Solving for Existential Types Predicates and Main Algorithm>

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
  final algorithm has the form:

  <\eqnarray*>
    <tformat|<cwith|9|9|2|2|cell-valign|c>|<table|<row|<cell|<wide|\<exists\><wide|\<beta\>|\<bar\>><rsup|\<chi\>,k>.F<rsub|\<chi\>>|\<bar\>>>|<cell|=>|<cell|S<rsub|k>>>|<row|<cell|\<wedge\><rsub|i><around*|(|D<rsub|K><rsup|i>\<Rightarrow\>C<rsub|K><rsup|i>|)>>|<cell|=>|<cell|<with|mode|text|all
    such that >\<chi\><rsub|K><around*|(|\<alpha\><rsub|3><rsup|i>,\<alpha\><rsub|2>|)>\<in\>C<rsub|K><rsup|i><eq-number>>>|<row|<cell|\<exists\><wide|\<alpha\>|\<bar\>><rsup|\<chi\><rsub|K>><rsub|g>.G<rsub|\<chi\><rsub|K>>>|<cell|=>|<cell|Connected<around*|(|\<delta\>,DisjElim<around*|(|<wide|S<rsub|k><around*|(|D<rsup|i><rsub|K>\<wedge\>C<rsup|i><rsub|K>|)>\<wedge\>\<delta\><wide|=|\<dot\>>\<alpha\><rsup|i><rsub|3>|\<bar\>>|)>|)>>>|<row|<cell|\<exists\><wide|\<alpha\>|\<bar\>><rsup|\<chi\><rsub|K>><rsub|g<rprime|'>>.G<rprime|'><rsub|\<chi\><rsub|K>>>|<cell|=>|<cell|AbdS<around*|(|\<cal-Q\>\<exists\><wide|\<alpha\>|\<bar\>><rsub|g><rsup|\<chi\><rsub|K>>,F<rsub|\<chi\><rsub|K>>,G<rsub|\<chi\><rsub|K>>|)><eq-number>>>|<row|<cell|\<exists\><wide|\<alpha\>|\<bar\>><rsup|\<chi\><rsub|K>><rsub|g<rprime|''>>.G<rprime|''><rsub|\<chi\><rsub|K>>>|<cell|=>|<cell|Simpl<around*|(|\<exists\><wide|\<alpha\>|\<bar\>><rsub|g><rsup|\<chi\><rsub|K>><wide|\<alpha\>|\<bar\>><rsup|\<chi\><rsub|K>><rsub|g<rprime|'>>.G<rprime|'><rsub|\<chi\><rsub|K>>|)><eq-number>>>|<row|<cell|<with|mode|text|if>>|<cell|>|<cell|G<rsub|\<chi\><rsub|K>><rprime|''>\<neq\>\<top\>>>|<row|<cell|<with|mode|text|then
    >\<exists\><wide|\<beta\>|\<bar\>><rsup|\<chi\><rsub|K>,k>.F<rsub|\<chi\><rsub|K>>\<assign\>>|<cell|>|<cell|S<rsub|k><around*|(|\<chi\><rsub|K>|)>\<assign\>\<exists\><wide|\<beta\>|\<bar\>><rsup|\<chi\><rsub|K>,k>\<exists\>FV<around*|(|G<rsub|\<chi\><rsub|K>><rprime|''>|)>\<cap\><wide|\<alpha\>|\<bar\>><rsup|\<chi\><rsub|K>><rsub|g<rprime|''>>.F<rsub|\<chi\><rsub|K>>\<wedge\>G<rsub|\<chi\><rsub|K>><rprime|''><eq-number>>>|<row|<cell|\<cal-Q\><rprime|'>.\<wedge\><rsub|i><around*|(|D<rsub|i>\<Rightarrow\>C<rsub|i>|)>>|<cell|=>|<cell|S<rsub|k><around*|(|\<Phi\>|)>>>|<row|<cell|\<exists\><wide|\<alpha\>|\<bar\>>.A>|<cell|=>|<cell|Abd<around*|(|\<cal-Q\><rprime|'>\\<wide|\<forall\>\<beta\><rsub|\<chi\>><wide|\<beta\><rsup|>|\<bar\>><rsup|\<chi\>>|\<bar\>>,<wide|\<beta\><rsub|\<chi\>><wide|\<beta\><rsup|>|\<bar\>><rsup|\<chi\>>,<wide|\<zeta\>|\<bar\>><rsup|\<chi\>>|\<bar\>>,<wide|D<rsub|i>,C<rsub|i>|\<bar\>>|)><eq-number>>>|<row|<cell|<around*|(|\<cal-Q\><rsup|k+1>,<wide|<wide|\<alpha\>|\<bar\>><rsup|\<chi\>><rsub|+>|\<bar\>>,A<rsub|res>,<wide|\<exists\><wide|\<alpha\>|\<bar\>><rsup|\<beta\><rsub|\<chi\>>>.A<rsub|\<beta\><rsub|\<chi\>>>|\<bar\>>|)>>|<cell|=>|<cell|Split<around*|(|\<cal-Q\><rprime|'>,<wide|\<alpha\>|\<bar\>>,A,<wide|\<beta\><rsub|\<chi\>><wide|\<beta\><rsup|>|\<bar\>><rsup|\<chi\>>|\<bar\>>,<wide|<wide|\<zeta\>|\<bar\>><rsup|\<chi\>>|\<bar\>>|)>>>|<row|<cell|\<Xi\><around*|(|\<exists\><wide|\<alpha\>|\<bar\>><rsup|\<chi\><rsub|K>>.F<rsub|\<chi\><rsub|K>>|)>>|<cell|=>|<cell|\<exists\><wide|\<alpha\>|\<bar\>><rsup|\<chi\><rsub|K>>FV<around*|(|F<rsub|\<chi\><rsub|K>>|)>.\<delta\><rprime|'><wide|=|\<dot\>><wide|FV<around*|(|F<rsub|\<chi\><rsub|K>>|)>\\<wide|\<alpha\>|\<bar\>><rsup|\<chi\><rsub|K>>|\<vect\>>\<wedge\>F<rsub|\<chi\><rsub|K>><around*|[|\<alpha\><rsub|2>\<assign\>\<delta\><rprime|'>|]><eq-number>>>|<row|<cell|\<Xi\><around*|(|\<exists\><wide|\<alpha\>|\<bar\>><rsup|\<chi\>>.F<rsub|\<chi\>>|)>>|<cell|=>|<cell|\<exists\><wide|\<alpha\>|\<bar\>><rsup|\<chi\>>.F<rsub|\<chi\>><with|mode|text|
    \ otherwise, i.e. for >\<chi\>\<in\>PV<rsup|1><around*|(|\<Phi\>|)>>>|<row|<cell|<with|mode|text|if>>|<cell|>|<cell|\<wedge\><rsub|\<chi\>>\<wedge\><rsub|\<beta\><rsub|\<chi\>>>A<rsub|\<beta\><rsub|\<chi\>>>=\<top\><eq-number>>>|<row|<cell|<with|mode|text|then:>>|<cell|>|<cell|>>|<row|<cell|\<exists\><wide|\<beta\>|\<bar\>><rsup|\<chi\>><rprime|'>.F<rsub|\<chi\>><rprime|'>>|<cell|=>|<cell|Simpl<around*|(|\<Xi\><around*|(|S<rsub|k>|)>|)><eq-number><label|SolSimpl>>>|<row|<cell|A<rsub|sel>>|<cell|=>|<cell|<around*|{|c\<in\>\<wedge\><rsub|\<chi\>>F<rsub|\<chi\>><rprime|'><mid|\|>FV<around*|(|c|)>\<cap\>\<delta\><wide|<wide|\<beta\>|\<bar\>><rsup|\<chi\>>|\<bar\>>=\<varnothing\>|}>>>|<row|<cell|<with|mode|text|return>>|<cell|>|<cell|A<rsub|res>\<wedge\>A<rsub|sel>,<wide|\<exists\><wide|\<beta\>|\<bar\>><rsup|\<chi\>><rprime|'>.F<rprime|'><rsub|\<chi\>>\\A<rsub|sel>|\<bar\>>>>|<row|<cell|<with|mode|text|else:>>|<cell|>|<cell|>>|<row|<cell|S<rsub|k><rprime|'>>|<cell|=>|<cell|<wide|\<exists\><wide|\<beta\>|\<bar\>><rsup|\<chi\>,k><wide|<wide|\<alpha\>|\<bar\>><rsup|\<beta\><rsub|\<chi\>>>|\<bar\>>.F<rsub|\<chi\>>\<wedge\><rsub|\<beta\><rsub|\<chi\>>>A<rsub|\<beta\><rsub|\<chi\>>><around*|[|<wide|\<beta\><rsub|\<chi\>><wide|\<beta\><rsup|>|\<bar\>><rsup|\<chi\>>|\<bar\>>\<assign\><wide|\<delta\><wide|\<beta\><rsup|>|\<bar\>><rsup|\<chi\>,k>|\<bar\>>|]>|\<bar\>><eq-number>>>|<row|<cell|S<rsub|k+1>>|<cell|=>|<cell|H<around*|(|S<rsub|k-1>,S<rsub|k>,S<rsub|k><rprime|'>|)><eq-number>>>|<row|<cell|<wide|\<beta\><rsup|>|\<bar\>><rsup|\<chi\>,k+1>>|<cell|=>|<cell|<wide|\<beta\><rsup|>|\<bar\>><rsup|\<chi\>,k><wide|\<alpha\>|\<bar\>><rsup|\<chi\>>>>|<row|<cell|<with|mode|text|repeat>>|<cell|>|<cell|k\<assign\>k+1>>>>
  </eqnarray*>

  Note that <math|Split> returns <math|<wide|\<exists\><wide|\<alpha\>|\<bar\>><rsup|\<beta\><rsub|\<chi\>>>.A<rsub|\<beta\><rsub|\<chi\>>>|\<bar\>>>
  rather than <math|<wide|\<exists\><wide|\<alpha\>|\<bar\>><rsup|\<chi\>>.A<rsub|\<chi\>>|\<bar\>>>.
  This is because in case of existential type predicate variables
  <math|\<chi\><rsub|K>>, there can be multiple negative position occurrences
  <math|\<chi\><rsub|K><around*|(|\<beta\><rsub|\<chi\><rsub|K>>,\<cdummy\>|)>>
  with different <math|\<beta\><rsub|\<chi\><rsub|K>>> when the corresponding
  value is used in multiple <math|<with|math-font-series|bold|let> \<ldots\>
  <with|math-font-series|bold|in>> expressions.
  <math|\<wedge\><rsub|\<beta\><rsub|\<chi\>>>A<rsub|\<beta\><rsub|\<chi\>>>>
  is a conjunction that spans all such occurrences. The variant of the
  algorithm to achieve completeness as conjectured in
  <cite|InvariantsTechRep2> would compute all answers for variants of
  <math|Abd> and <math|Split> algorithms that return multiple answers. Unary
  predicate variables <math|\<chi\><around*|(|\<beta\><rsub|\<chi\>>|)>> can
  also have multiple negative occurrences in the normalized form, but always
  with the same argument <math|\<beta\><rsub|\<chi\>>>.

  We start with <math|S<rsub|0>\<assign\><wide|\<top\>|\<bar\>>>.
  <math|Connected<around*|(|\<alpha\>,G|)>> is the connected component of
  hypergraph <math|G> containing node <math|\<alpha\>>, where nodes are
  variables <math|FV<around*|(|G|)>> and hyperedges are atoms
  <math|c\<in\>G>. <math|H<around*|(|S<rsub|a>,S<rsub|b>,S<rsub|c>|)>> is a
  convergence improving heuristic, a dummy implementation is
  <math|H<around*|(|S<rsub|a>,S<rsub|b>,S<rsub|c>|)>=S<rsub|c>>.
  <math|<wide|S|~>> is the substitution of predicate variables
  <math|<wide|\<chi\>|\<bar\>>> corresponding to <math|S>.

  Solutions <math|S<rsub|k>> growing with <math|k> introduce opportunity for
  simplifications not captured when the incremental improvements
  <math|A<rsub|\<beta\><rsub|\<chi\>>>> are derived. In step
  <reference|SolSimpl> we simplify and then prune each
  <math|\<exists\><wide|\<beta\>|\<bar\>><rsup|\<chi\>>.F<rsub|\<chi\>>>. The
  updated residuum <math|\<cal-Q\><rprime|'>.A<rsub|res>\<wedge\>A<rsub|sel>>
  is checked for validity at a later stage.

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

  We implement a simple form of backtracking. When abduction detects
  contradiction in the branches <math|S<rsub|k><around*|(|\<Phi\>|)>> passed
  to it, it uses <verbatim|fallback> branches
  <math|S<rsub|k-1><around*|(|\<Phi\>|)>>. Infinite loop is avoided because
  the discard list for step <math|k> contains answers of step <math|k-1>. In
  case abduction used the fallback branches, we set
  <math|S<rsub|k>\<assign\>S<rsub|k-1>> before going on to compute
  <math|S<rsub|k+1>>. Similarly, with checking for negative constraints
  <em|on>, when the check of negative branches
  <math|<around*|(|D<rsub|i>,C<rsub|i>|)>\<in\>\<Phi\><rsub|\<b-F\>>>,
  \ <math|\<nvDash\>\<exists\>FV<around*|(|S<rsub|k><around*|(|D<rsub|i>|)>|)>.S<rsub|k><around*|(|D<rsub|i>|)>>
  fails, we set <math|S<rsub|k>\<assign\>S<rsub|k-1>> before calling
  abduction.

  <subsection|Implementation details>

  We represent <math|<wide|\<alpha\>|\<vect\>>> as a tuple type rather than
  as a function type. We modify the quantifier <math|\<cal-Q\>> imperatively,
  because it mostly grows monotonically, and when variables are dropped they
  do not conflict with fresh variables generated later. Variables introduced
  by predicate variable substitution are always existential for positive
  occurrences, but for negative occurrences some parts of the algorithm
  assume they are universal, and some use a variant of the quantifier, e.g.
  <math|\<cal-Q\><rprime|'><around*|[|<wide|\<forall\>\<beta\><rsub|\<chi\>><wide|\<beta\><rsup|>|\<bar\>><rsup|\<chi\>>|\<bar\>>\<assign\><wide|\<exists\>\<beta\><rsub|\<chi\>><wide|\<beta\><rsup|>|\<bar\>><rsup|\<chi\>>|\<bar\>>|]>>,
  where they are existential.

  The code that selects <math|\<wedge\><rsub|\<chi\>><around*|(|A<rsub|\<chi\>><rsup|+>\<subset\>A<rsub|\<chi\>><rsup|cap>|)>\<wedge\>\<vDash\>\<cal-Q\>.A\<setminus\>\<cup\><rsub|\<chi\>>A<rsub|\<chi\>><rsup|+>>
  is an incremental validity checker. It starts with
  <math|A\<setminus\>\<cup\><rsub|\<chi\>>A<rsub|\<chi\>><rsup|cap>> and
  tries to add as many atoms <math|c\<in\>\<cup\><rsub|\<chi\>>A<rsub|\<chi\>><rsup|cap>>
  as possible to what in effect becomes <math|A<rsub|res>>. The remaining
  atoms are distributed among <math|A<rsub|\<beta\><rsub|\<chi\>>><rsup|+>>
  by putting them into the last <math|\<beta\><rsub|\<chi\>>> in
  <math|\<cal-Q\>>, i.e. the first <verbatim|b> in the <verbatim|q.negbs>
  list, for which <math|x<rsub|\<prec\>><around*|(|<wide|<wide|\<beta\>|\<bar\>><rsup|\<chi\>><wide|\<zeta\>|\<bar\>><rsup|\<chi\>>|\<bar\>>\<cap\>FV<around*|(|c|)>|)>\<cap\><wide|\<beta\>|\<bar\>><rsup|\<chi\>><wide|\<zeta\>|\<bar\>><rsup|\<chi\>>\<neq\>\<varnothing\>>.

  \;

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
    <associate|sfactor|4>
  </collection>
</initial>

<\references>
  <\collection>
    <associate|1|<tuple|5.2|?>>
    <associate|ImplSubst|<tuple|4|2>>
    <associate|SepProp|<tuple|5|3>>
    <associate|SepProp2|<tuple|6|?>>
    <associate|SolSimpl|<tuple|8|10>>
    <associate|SolvedForm|<tuple|4|?>>
    <associate|SolvedFormProj|<tuple|7|?>>
    <associate|auto-1|<tuple|1|1>>
    <associate|auto-10|<tuple|3.5|7>>
    <associate|auto-11|<tuple|4|8>>
    <associate|auto-12|<tuple|4.1|8>>
    <associate|auto-13|<tuple|5|8>>
    <associate|auto-14|<tuple|5.1|9>>
    <associate|auto-15|<tuple|5.2|10>>
    <associate|auto-16|<tuple|5.3|11>>
    <associate|auto-17|<tuple|5.4|11>>
    <associate|auto-18|<tuple|5.4|?>>
    <associate|auto-2|<tuple|2|2>>
    <associate|auto-3|<tuple|2.1|3>>
    <associate|auto-4|<tuple|2.2|4>>
    <associate|auto-5|<tuple|3|4>>
    <associate|auto-6|<tuple|3.1|4>>
    <associate|auto-7|<tuple|3.2|5>>
    <associate|auto-8|<tuple|3.3|6>>
    <associate|auto-9|<tuple|3.4|6>>
    <associate|bib-AbductionSolvMaher|<tuple|3|11>>
    <associate|bib-AntiUnifAlg|<tuple|8|11>>
    <associate|bib-AntiUnifInv|<tuple|2|4>>
    <associate|bib-AntiUnifPlotkin|<tuple|4|4>>
    <associate|bib-AntiUnifReynolds|<tuple|5|4>>
    <associate|bib-ArithQuantElim|<tuple|1|11>>
    <associate|bib-ConvexHull|<tuple|2|11>>
    <associate|bib-DBLP:conf/cccg/2000|<tuple|3|?>>
    <associate|bib-UnificationBaader|<tuple|1|4>>
    <associate|bib-disjelimTechRep|<tuple|6|11>>
    <associate|bib-jcaqpTechRep|<tuple|8|4>>
    <associate|bib-jcaqpTechRep2|<tuple|7|11>>
    <associate|bib-jcaqpUNIF|<tuple|4|11>>
    <associate|bib-simonet-pottier-hmg-toplas|<tuple|6|4>>
    <associate|bib-systemTechRep|<tuple|5|11>>
  </collection>
</references>

<\auxiliary>
  <\collection>
    <\associate|bib>
      systemTechRep

      systemTechRep

      systemTechRep

      jcaqpUNIF

      AbductionSolvMaher

      AbductionSolvMaher

      jcaqpTechRep2

      ArithQuantElim

      ArithQuantElim

      jcaqpTechRep2

      jcaqpTechRep2

      jcaqpTechRep2

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

      <with|par-left|<quote|1.5fn>|2.2<space|2spc>Simplification
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-4>>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|3<space|2spc>Abduction>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-5><vspace|0.5fn>

      <with|par-left|<quote|1.5fn>|3.1<space|2spc>Simple constraint abduction
      for terms <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-6>>

      <with|par-left|<quote|1.5fn>|3.2<space|2spc>Joint constraint abduction
      for terms <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-7>>

      <with|par-left|<quote|1.5fn>|3.3<space|2spc>Abduction for terms with
      Alien Subterms <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-8>>

      <with|par-left|<quote|1.5fn>|3.4<space|2spc>Joint constraint abduction
      for linear arithmetic <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-9>>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|4<space|2spc>Disjunction
      Elimination> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-10><vspace|0.5fn>

      <with|par-left|<quote|1.5fn>|4.1<space|2spc>Extended convex hull
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-11>>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|5<space|2spc>Solving
      for Predicate Variables> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-12><vspace|0.5fn>

      <with|par-left|<quote|1.5fn>|5.1<space|2spc>Invariant Parameter
      Candidates <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-13>>

      <with|par-left|<quote|1.5fn>|5.2<space|2spc>Solving for Predicates in
      Negative Positions <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-14>>

      <with|par-left|<quote|1.5fn>|5.3<space|2spc>Solving for Existential
      Types Predicates and Main Algorithm
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-15>>

      <with|par-left|<quote|1.5fn>|5.4<space|2spc>Implementation details
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-16>>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|Bibliography>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-17><vspace|0.5fn>
    </associate>
  </collection>
</auxiliary>