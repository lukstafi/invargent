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
  occurrence in user code introduces a fresh identifier and an entry in
  global <em|existential constructor environment> <verbatim|extype_env>.

  <block|<tformat|<cwith|1|1|2|2|cell-halign|c>|<cwith|1|1|1|1|cell-halign|l>|<table|<row|<cell|type
  variable>|<cell|<math|x>>|<cell|<verbatim|x>>|<cell|>|<cell|<verbatim|TVar>>>|<row|<cell|type
  constructor>|<cell|<math|List>>|<cell|<verbatim|List>>|<cell|>|<cell|<verbatim|TCons>>>|<row|<cell|number
  (type)>|<cell|<math|7>>|<cell|<verbatim|7>>|<cell|>|<cell|<verbatim|NCst>>>|<row|<cell|numeral
  (expr.)>|<cell|<math|7>>|<cell|<verbatim|7>>|<cell|>|<cell|<verbatim|Num>>>|<row|<cell|numerical
  sum (type)>|<cell|<math|a+b>>|<cell|<verbatim|a+b>>|<cell|>|<cell|<verbatim|Nadd>>>|<row|<cell|existential
  type>|<cell|<math|\<exists\>\<alpha\>\<beta\><around*|[|a\<leqslant\>\<beta\>|]>.\<tau\>>>|<cell|<verbatim|ex
  a b [a\<less\>=b].t>>|<cell|<verbatim|<math|\<exists\>>a,b[a<math|\<leq\>>b].t>>|<cell|<verbatim|TExCons>>>|<row|<cell|type
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
    <associate|auto-2|<tuple|2|1>>
    <associate|auto-3|<tuple|2|2>>
    <associate|auto-4|<tuple|1.3|2>>
    <associate|auto-5|<tuple|2|2>>
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
    <associate|bib-systemTechRep|<tuple|1|?>>
  </collection>
</references>

<\auxiliary>
  <\collection>
    <\associate|bib>
      systemTechRep
    </associate>
    <\associate|toc>
      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|1<space|2spc>Data
      Structures and Concrete Syntax> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-1><vspace|0.5fn>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|Bibliography>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-2><vspace|0.5fn>
    </associate>
  </collection>
</auxiliary>