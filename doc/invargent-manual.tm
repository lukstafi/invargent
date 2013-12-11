<TeXmacs|1.0.7.21>

<style|article>

<\body>
  <doc-data|<doc-title|InvarGenT -- Manual>||<doc-author|<author-data|<author-name|�ukasz
  Stafiniak>|<\author-affiliation>
    Institute of Computer Science

    University of Wroc�aw
  </author-affiliation>>>>

  <\abstract>
    InvarGenT is a proof-of-concept system for invariant generation by full
    type inference with Guarded Algebraic Data Types and existential types
    encoded as automatically generated GADTs. This user manual discusses
    motivating examples, briefly presents the syntax of the InvarGenT
    language, and describes the parameters of the inference process that can
    be passed to the InvarGenT executable.
  </abstract>

  <section|Introduction>

  Type systems are an established natural deduction-style means to reason
  about programs. Dependent types can represent arbitrarily complex
  properties as they use the same language for both types and programs, the
  type of value returned by a function can itself be a function of the
  argument. Generalized Algebraic Data Types bring some of that expressivity
  to type systems that deal with data-types. Type systems with GADTs
  introduce the ability to reason about return type by case analysis of the
  input value, while keeping the benefits of a simple semantics of types, for
  example deciding equality can be very simple. Existential types hide some
  information conveyed in a type, usually when that information cannot be
  reconstructed in the type system. A part of the type will often fail to be
  expressible in the simple language of types, when the dependence on the
  input to the program is complex. GADTs express existential types by using
  local type variables for the hidden parts of the type encapsulated in a
  GADT.

  The InvarGenT type system for GADTs differs from more pragmatic approaches
  in mainstream functional languages in that we do not require any type
  annotations on expressions, even on recursive functions. The implementation
  also includes linear equations and inequalities over rational numbers in
  the language of types, with the possibility to introduce more domains in
  the future.

  <section|Tutorial>

  The concrete syntax of InvarGenT is similar to that of OCaml. However, it
  does not currently cover records, the module system, objects, and
  polymorphic variant types. It supports higher-order functions, algebraic
  data-types including built-in tuple types, and linear pattern matching. It
  supports conjunctive patterns using the <verbatim|as> keyword, but it does
  not support disjunctive patterns. It does not currently support guarded
  patterns, i.e. no support for the <verbatim|when> keyword of OCaml.

  The sort of a type variable is identified by the first letter of the
  variable. <verbatim|a>,<verbatim|b>,<verbatim|c>,<verbatim|r>,<verbatim|s>,<verbatim|t>,<verbatim|a1>,...
  are in the sort of terms called <verbatim|type>, i.e. ``types proper''.
  <verbatim|i>,<verbatim|j>,<verbatim|k>,<verbatim|l>,<verbatim|m>,<verbatim|n>,<verbatim|i1>,...
  are in the sort of linear arithmetics over rational numbers called
  <verbatim|num>. Remaining letters are reserved for sorts that may be added
  in the future. Type constructors and value constructors have the same
  syntax: capitalized name followed by a tuple of arguments. They are
  introduced by <verbatim|newtype> and <verbatim|newcons> respectively. The
  <verbatim|newtype> declaration might be misleading in that it only lists
  the sorts of the arguments of the type, the resulting sort is always
  <verbatim|type>. Values assumed into the environment are introduced by
  <verbatim|external>. There is a built-in type corresponding to declaration
  <verbatim|newtype Num : num> and definitions of numeric constants
  <verbatim|newcons 0 : Num 0 newcons 1 : Num 1>... The programmer can use
  <verbatim|external> declarations to give the semantics of choice to the
  <verbatim|Num> data-type.

  In examples here we use Unicode characters. For ASCII equivalents, take a
  quick look at the tables in the following section. <verbatim|equal> is a
  function comparing values provided representation of their types:

  <\code>
    newtype Ty : type

    newtype Int

    newtype List : type

    newcons Zero : Int

    newcons Nil : <math|\<forall\>>a. List a

    newcons TInt : Ty Int

    newcons TPair : <math|\<forall\>>a, b. Ty a * Ty b
    <math|\<longrightarrow\>> Ty (a, b)

    newcons TList : <math|\<forall\>>a. Ty a <math|\<longrightarrow\>> Ty
    (List a)

    newtype Boolean

    newcons True : Boolean

    newcons False : Boolean

    external eq_int : Int <math|\<rightarrow\>> Int <math|\<rightarrow\>>
    Bool

    external b_and : Bool <math|\<rightarrow\>> Bool <math|\<rightarrow\>>
    Bool

    external b_not : Bool <math|\<rightarrow\>> Bool

    external forall2 : <math|\<forall\>>a, b. (a <math|\<rightarrow\>> b
    <math|\<rightarrow\>> Bool) <math|\<rightarrow\>> List a
    <math|\<rightarrow\>> List b <math|\<rightarrow\>> Bool

    \;

    let rec equal1 = function

    \ \ \| TInt, TInt -\> fun x y -\> eq_int x y

    \ \ \| TPair (t1, t2), TPair (u1, u2) -\> \ 

    \ \ \ \ (fun (x1, x2) (y1, y2) -\>

    \ \ \ \ \ \ \ \ b_and (equal (t1, u1) x1 y1)

    \ \ \ \ \ \ \ \ \ \ \ \ \ \ (equal (t2, u2) x2 y2))

    \ \ \| TList t, TList u -\> forall2 (equal (t, u))

    \ \ \| _ -\> fun _ _ -\> False
  </code>

  InvarGenT returns an unexpected type: <verbatim|equal1<math|:\<forall\>>a,b.(a,b)<math|\<rightarrow\>>b<math|\<rightarrow\>>b<math|\<rightarrow\>>Bool>,
  one of four maximally general types of <verbatim|equal1>. This illustrates
  that unrestricted type systems with GADTs lack principal typing property.

  InvarGenT commits to a type of a toplevel definition before proceeding to
  the next one, so sometimes we need to provide more information in the
  program. Besides type annotations, there are two means to enrich the
  generated constraints: <verbatim|assert false> syntax for providing
  negative constraints, and <verbatim|test> syntax for including constraints
  of use cases with constraint of a toplevel definition. To ensure only one
  maximally general type for <verbatim|equal>, we use both. We add the lines:

  <\code>
    \ \ \| TInt, TList l -\> (function Nil -\> assert false)

    \ \ \| TList l, TInt -\> (fun _ -\> function Nil -\> assert false)

    test b_not (equal (TInt, TList TInt) Zero Nil)
  </code>

  Actually, InvarGenT returns the expected type
  <verbatim|equal<math|:\<forall\>>a,b.(a,b)<math|\<rightarrow\>>a<math|\<rightarrow\>>b<math|\<rightarrow\>>Bool>
  when either the two <verbatim|assert false> clauses or the <verbatim|test>
  clause is added. When using <verbatim|test>, the program should declare the
  type <verbatim|Boolean> and constant <verbatim|True>. In a future version,
  this will be replaced by a built-in type <verbatim|Bool> with constants
  <verbatim|True> and <verbatim|False>, exported into OCaml as type
  <verbatim|bool> with constants <verbatim|true> and <verbatim|false>.

  Now we demonstrate numerical invariants:

  <\code>
    newtype Binary : num

    newtype Carry : num

    newcons Zero : Binary 0

    newcons PZero : <math|\<forall\>>n[0<math|\<leq\>>n]. Binary(n)
    <math|\<longrightarrow\>> Binary(n+n)

    newcons POne : <math|\<forall\>>n[0<math|\<leq\>>n]. Binary(n)
    <math|\<longrightarrow\>> Binary(n+n+1)

    newcons CZero : Carry 0

    newcons COne : Carry 1

    \;

    let rec plus =

    \ \ function CZero -\>

    \ \ \ \ (function Zero -\> (fun b -\> b)

    \ \ \ \ \ \ \| PZero a1 as a -\>

    \ \ \ \ \ \ \ \ (function Zero -\> a

    \ \ \ \ \ \ \ \ \ \ \| PZero b1 -\> PZero (plus CZero a1 b1)

    \ \ \ \ \ \ \ \ \ \ \| POne b1 -\> POne (plus CZero a1 b1))

    \ \ \ \ \ \ \| POne a1 as a -\>

    \ \ \ \ \ \ \ \ (function Zero -\> a

    \ \ \ \ \ \ \ \ \ \ \| PZero b1 -\> POne (plus CZero a1 b1)

    \ \ \ \ \ \ \ \ \ \ \| POne b1 -\> PZero (plus COne a1 b1)))

    \ \ \ \ \| COne -\>

    \ \ \ \ (function Zero -\>

    \ \ \ \ \ \ \ \ (function Zero -\> POne(Zero)

    \ \ \ \ \ \ \ \ \ \ \| PZero b1 -\> POne b1

    \ \ \ \ \ \ \ \ \ \ \| POne b1 -\> PZero (plus COne Zero b1))

    \ \ \ \ \ \ \| PZero a1 as a -\>

    \ \ \ \ \ \ \ \ (function Zero -\> POne a1

    \ \ \ \ \ \ \ \ \ \ \| PZero b1 -\> POne (plus CZero a1 b1)

    \ \ \ \ \ \ \ \ \ \ \| POne b1 -\> PZero (plus COne a1 b1))

    \ \ \ \ \ \ \| POne a1 as a -\>

    \ \ \ \ \ \ \ \ (function Zero -\> PZero (plus COne a1 Zero)

    \ \ \ \ \ \ \ \ \ \ \| PZero b1 -\> PZero (plus COne a1 b1)

    \ \ \ \ \ \ \ \ \ \ \| POne b1 -\> POne (plus COne a1 b1)))
  </code>

  We get <verbatim|plus<math|:\<forall\>>i,j,k.Carry
  i<math|\<rightarrow\>>Binary j<math|\<rightarrow\>>Binary
  k<math|\<rightarrow\>>Binary (i+j+k)>.

  We can introduce existential types directly in type declarations. To have
  an existential type inferred, we have to use <verbatim|efunction> or
  <verbatim|ematch> expressions, which differ from <verbatim|function> and
  <verbatim|match> only in that the (return) type is an existential type. To
  use a value of an existential type, we have to bind it with a
  <verbatim|let>..<verbatim|in> expression. Otherwise, the existential type
  will not be unpacked. An existential type will be automatically unpacked
  before being ``repackaged'' as another existential type.

  <\code>
    newtype Room

    newtype Yard

    newtype Village

    newtype Castle : type

    newtype Place : type

    newcons Room : Room <math|\<longrightarrow\>> Castle Room

    newcons Yard : Yard <math|\<longrightarrow\>> Castle Yard

    newcons CastleRoom : Room <math|\<longrightarrow\>> Place Room

    newcons CastleYard : Yard <math|\<longrightarrow\>> Place Yard

    newcons Village : Village <math|\<longrightarrow\>> Place Village

    \;

    external wander : <math|\<forall\>>a. Place a <math|\<rightarrow\>>
    <math|\<exists\>>b. Place b

    \;

    let rec find_castle = efunction

    \ \ \| CastleRoom x -\> Room x

    \ \ \| CastleYard x -\> Yard x

    \ \ \| Village _ as x -\>

    \ \ \ \ let y = wander x in

    \ \ \ \ find_castle y
  </code>

  We get <verbatim|find_castle<math|:\<forall\>>a. Place
  a<math|\<rightarrow\>> <math|\<exists\>>b. Castle b>.

  A more practical existential type example:

  <\code>
    newtype Bool

    newcons True : Bool

    newcons False : Bool

    newtype List : type * num

    newcons LNil : <math|\<forall\>>a. List(a, 0)

    newcons LCons : <math|\<forall\>>n,a[0<math|\<leq\>>n]. a * List(a, n)
    <math|\<longrightarrow\>> List(a, n+1)

    \;

    let rec filter = fun f -\>

    \ \ efunction LNil -\> LNil

    \ \ \ \ \| LCons (x, xs) -\>

    \ \ \ \ \ \ ematch f x with

    \ \ \ \ \ \ \ \ \| True -\>

    \ \ \ \ \ \ \ \ \ \ let ys = filter f xs in

    \ \ \ \ \ \ \ \ \ \ LCons (x, ys)

    \ \ \ \ \ \ \ \ \| False -\>

    \ \ \ \ \ \ \ \ \ \ filter f xs
  </code>

  We get <verbatim|filter<math|:\<forall\>>a,i.(a<math|\<rightarrow\>>Bool)<math|\<rightarrow\>>List
  (a, i)<math|\<rightarrow\>> <math|\<exists\>>j[j<math|\<leq\>>i].List (a,
  j)>. Note that we need to use both <verbatim|efunction> and
  <verbatim|ematch> above, since every use of <verbatim|function> or
  <verbatim|match> will force the types of its branches to be equal. In
  particular, for lists with length the resulting length would have to be the
  same in each branch. If the constraint cannot be met, as for
  <verbatim|filter> with either <verbatim|function> or <verbatim|match>, the
  code will not type-check.

  A more complex example that computes bitwise <em|or> -- <verbatim|ub>
  stands for ``upper bound'':

  <\code>
    newtype Binary : num

    newcons Zero : Binary 0

    newcons PZero : <math|\<forall\>>n [0<math|\<leq\>>n]. Binary(n)
    <math|\<longrightarrow\>> Binary(n+n)

    newcons POne : <math|\<forall\>>n [0<math|\<leq\>>n]. Binary(n)
    <math|\<longrightarrow\>> Binary(n+n+1)

    \;

    let rec ub = efunction

    \ \ \| Zero -\>

    \ \ \ \ \ \ (efunction Zero -\> Zero

    \ \ \ \ \ \ \ \ \| PZero b1 as b -\> b

    \ \ \ \ \ \ \ \ \| POne b1 as b -\> b)

    \ \ \| PZero a1 as a -\>

    \ \ \ \ \ \ (efunction Zero -\> a

    \ \ \ \ \ \ \ \ \| PZero b1 -\>

    \ \ \ \ \ \ \ \ \ \ let r = ub a1 b1 in

    \ \ \ \ \ \ \ \ \ \ PZero r

    \ \ \ \ \ \ \ \ \| POne b1 -\>

    \ \ \ \ \ \ \ \ \ \ let r = ub a1 b1 in

    \ \ \ \ \ \ \ \ \ \ POne r)

    \ \ \| POne a1 as a -\>

    \ \ \ \ \ \ (efunction Zero -\> a

    \ \ \ \ \ \ \ \ \| PZero b1 -\>

    \ \ \ \ \ \ \ \ \ \ let r = ub a1 b1 in

    \ \ \ \ \ \ \ \ \ \ POne r

    \ \ \ \ \ \ \ \ \| POne b1 -\>

    \ \ \ \ \ \ \ \ \ \ let r = ub a1 b1 in

    \ \ \ \ \ \ \ \ \ \ POne r)
  </code>

  Type: <verbatim|ub:<math|\<forall\>>k,n.Binary k<math|\<rightarrow\>>Binary
  n<math|\<rightarrow\>><math|\<exists\>>:i[n<math|\<leq\>>i<math|\<wedge\>>k<math|\<leq\>>i<math|\<wedge\>>i<math|\<leq\>>k+n<math|\<wedge\>>0<math|\<leq\>>n<math|\<wedge\>>0<math|\<leq\>>k].Binary
  i>.

  Why cannot we shorten the above code by converting the initial cases to
  <verbatim|Zero -\<gtr\> (efunction b -\<gtr\> b)>? Without pattern
  matching, we do not make the contribution of <verbatim|Binary n> available.
  Knowing <verbatim|n<math|=>i> and not knowing <verbatim|0<math|\<leq\>>n>,
  for the case <verbatim|k<math|=>0>, we get:
  <verbatim|ub:<math|\<forall\>>k,n.Binary k<math|\<rightarrow\>>Binary
  n<math|\<rightarrow\>><math|\<exists\>>:i[n<math|\<leq\>>i<math|\<wedge\>>i<math|\<leq\>>k+n<math|\<wedge\>>0<math|\<leq\>>k].Binary
  i>. <verbatim|n<math|\<leq\><no-break>>i> follows from
  <verbatim|n<math|=>i>, <verbatim|i<math|\<leq\>>k+n> follows from
  <verbatim|n<math|=>i> and <verbatim|0<math|\<leq\>>k>, but
  <verbatim|k<math|\<leq\>>i> cannot be inferred from <verbatim|k<math|=>0>
  and <verbatim|n<math|=>i> without knowing that <verbatim|0<math|\<leq\>>n>.

  In fact, <verbatim|let>...<verbatim|in> expressions are syntactic sugar for
  pattern matching with a single branch.

  Besides displaying types of toplevel definitions, InvarGenT can also export
  an OCaml source file with all the required GADT definitions and type
  annotations.

  <section|Syntax>

  Below we present, using examples, the syntax of InvarGenT: the mathematical
  notation, the concrete syntax in ASCII and the concrete syntax using
  Unicode.

  <block|<tformat|<cwith|1|1|2|2|cell-halign|c>|<cwith|1|1|1|1|cell-halign|l>|<cwith|2|2|2|2|cell-halign|c>|<cwith|2|2|1|1|cell-halign|l>|<table|<row|<cell|type
  variable: types>|<cell|<math|\<alpha\>,\<beta\>,\<gamma\>,\<tau\>>>|<cell|<verbatim|a>,<verbatim|b>,<verbatim|c>,<verbatim|r>,<verbatim|s>,<verbatim|t>,<verbatim|a1>,...>|<cell|>>|<row|<cell|type
  variable: nums>|<cell|<math|k,m,n>>|<cell|<verbatim|i>,<verbatim|j>,<verbatim|k>,<verbatim|l>,<verbatim|m>,<verbatim|n>,<verbatim|i1>,...>|<cell|>>|<row|<cell|type
  constructor>|<cell|<math|List>>|<cell|<verbatim|List>>|<cell|>>|<row|<cell|number
  (type)>|<cell|<math|7>>|<cell|<verbatim|7>>|<cell|>>|<row|<cell|numeral
  (expr.)>|<cell|<math|7>>|<cell|<verbatim|7>>|<cell|>>|<row|<cell|numerical
  sum (type)>|<cell|<math|m+n>>|<cell|<verbatim|m+n>>|<cell|>>|<row|<cell|existential
  type>|<cell|<math|\<exists\>k,n<around*|[|k\<leqslant\>n|]>.\<tau\>>>|<cell|<verbatim|ex
  k n [k\<less\>=n].t>>|<cell|<verbatim|<math|\<exists\>>k,n[k<math|\<leq\>>n].t>>>|<row|<cell|type
  sort>|<cell|<math|s<rsub|ty>>>|<cell|<verbatim|type>>|<cell|>>|<row|<cell|number
  sort>|<cell|<math|s<rsub|R>>>|<cell|<verbatim|num>>|<cell|>>|<row|<cell|function
  type>|<cell|<math|\<tau\><rsub|1>\<rightarrow\>\<tau\><rsub|2>>>|<cell|<verbatim|t1
  -\<gtr\> t2>>|<cell|<verbatim|t1 <math|\<rightarrow\>><verbatim|
  t2>>>>|<row|<cell|equation>|<cell|<math|a<wide|=|\<dot\>>b>>|<cell|<verbatim|a
  = b>>|<cell|>>|<row|<cell|inequation>|<cell|<math|k\<leqslant\>n>>|<cell|<verbatim|k
  \<less\>= n>>|<cell|<verbatim|k <math|\<leq\>>
  n>>>|<row|<cell|conjunction>|<cell|<math|\<varphi\><rsub|1>\<wedge\>\<varphi\><rsub|2>>>|<cell|<verbatim|a=b
  && b=a>>|<cell|<verbatim|a=b <math|\<wedge\>> b=a>>>>>>

  Toplevel expressions (corresponding to structure items in OCaml) introduce
  types, type and value constructors, global variables with given type
  \ (external names) or inferred type (definitions).

  <block|<tformat|<cwith|1|1|2|2|cell-halign|l>|<cwith|1|1|1|1|cell-halign|l>|<table|<row|<cell|type
  constructor>|<cell|<verbatim|newtype List : type * num>>>|<row|<cell|value
  constructor>|<cell|<verbatim|newcons Cons : all n a. a * List(a,n)
  --\<gtr\> List(a,n+1)>>>|<row|<cell|>|<cell|<verbatim|newcons Cons :
  <math|\<forall\>>n,a. a * List(a,n) <math|\<longrightarrow\>>
  List(a,n+1)>>>|<row|<cell|declaration>|<cell|<verbatim|external filter :
  <math|\<forall\>>n,a. List(a,n)<math|\<rightarrow\>
  \<exists\>>k[k\<less\>=n].List(a,k)>>>|<row|<cell|rec.
  definition>|<cell|<verbatim|let rec f =>...>>|<row|<cell|non-rec.
  definition>|<cell|<verbatim|let a, b =>...>>>>>

  Like in OCaml, types of arguments in declarations of constructors are
  separated by asterisks. However, the type constructor for tuples is
  represented by commas, like in Haskell but unlike in OCaml.

  For simplicity of theory and implementation, mutual non-nested recursion
  and or-patterns are not provided. For mutual recursion, nest one recursive
  definition inside another.

  <section|Solver Parameters and CLI>

  \;
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
    <associate|AlienSubterms|<tuple|3.3|8|invargent.tm>>
    <associate|Details|<tuple|5.5|17|invargent.tm>>
    <associate|ImplSubst|<tuple|4|2>>
    <associate|Main Algo|<tuple|5.3|?>>
    <associate|MainAlgo|<tuple|5|12|invargent.tm>>
    <associate|MainAlgoBody|<tuple|5.3|15|invargent.tm>>
    <associate|NumConv|<tuple|4.2|11|invargent.tm>>
    <associate|Rg|<tuple|5|15|invargent.tm>>
    <associate|SCAlinear|<tuple|3.4|8|invargent.tm>>
    <associate|SepProp|<tuple|5|3>>
    <associate|SepProp2|<tuple|6|?>>
    <associate|Skp|<tuple|1|15|invargent.tm>>
    <associate|Skp1|<tuple|10|16|invargent.tm>>
    <associate|SolSimpl|<tuple|9|12>>
    <associate|SolvedForm|<tuple|4|?>>
    <associate|SolvedFormProj|<tuple|7|?>>
    <associate|auto-1|<tuple|1|1>>
    <associate|auto-10|<tuple|3.3|8|invargent.tm>>
    <associate|auto-11|<tuple|3.4|8|invargent.tm>>
    <associate|auto-12|<tuple|4|10|invargent.tm>>
    <associate|auto-13|<tuple|4.1|10|invargent.tm>>
    <associate|auto-14|<tuple|4.2|11|invargent.tm>>
    <associate|auto-15|<tuple|4.3|11|invargent.tm>>
    <associate|auto-16|<tuple|5|12|invargent.tm>>
    <associate|auto-17|<tuple|5.1|12|invargent.tm>>
    <associate|auto-18|<tuple|5.2|13|invargent.tm>>
    <associate|auto-19|<tuple|5.3|15|invargent.tm>>
    <associate|auto-2|<tuple|2|2>>
    <associate|auto-20|<tuple|5.4|17|invargent.tm>>
    <associate|auto-21|<tuple|5.5|17|invargent.tm>>
    <associate|auto-22|<tuple|6|18|invargent.tm>>
    <associate|auto-23|<tuple|6|18|invargent.tm>>
    <associate|auto-24|<tuple|5.5|17>>
    <associate|auto-3|<tuple|3|4>>
    <associate|auto-4|<tuple|4|4>>
    <associate|auto-5|<tuple|2.2|4|invargent.tm>>
    <associate|auto-6|<tuple|3|5|invargent.tm>>
    <associate|auto-7|<tuple|3.1|5|invargent.tm>>
    <associate|auto-8|<tuple|3.1.1|7|invargent.tm>>
    <associate|auto-9|<tuple|3.2|7|invargent.tm>>
    <associate|bib-AbductionSolvMaher|<tuple|3|18|invargent.tm>>
    <associate|bib-AntiUnifAlg|<tuple|9|18|invargent.tm>>
    <associate|bib-AntiUnifInv|<tuple|2|4>>
    <associate|bib-AntiUnifPlotkin|<tuple|4|4>>
    <associate|bib-AntiUnifReynolds|<tuple|5|4>>
    <associate|bib-ArithQuantElim|<tuple|1|18|invargent.tm>>
    <associate|bib-ConvexHull|<tuple|2|18|invargent.tm>>
    <associate|bib-DBLP:conf/cccg/2000|<tuple|3|?>>
    <associate|bib-ESOP2014|<tuple|8|18|invargent.tm>>
    <associate|bib-UnificationBaader|<tuple|1|4>>
    <associate|bib-disjelimTechRep|<tuple|5|18|invargent.tm>>
    <associate|bib-invariantsTechRep2|<tuple|6|18|invargent.tm>>
    <associate|bib-jcaqpTechRep|<tuple|8|4>>
    <associate|bib-jcaqpTechRep2|<tuple|7|18|invargent.tm>>
    <associate|bib-jcaqpUNIF|<tuple|4|18|invargent.tm>>
    <associate|bib-simonet-pottier-hmg-toplas|<tuple|6|4>>
    <associate|bib-systemTechRep|<tuple|5|18>>
  </collection>
</references>

<\auxiliary>
  <\collection>
    <\associate|bib>
      InvarGenT
    </associate>
    <\associate|toc>
      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|1<space|2spc>Introduction>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-1><vspace|0.5fn>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|2<space|2spc>Tutorial>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-2><vspace|0.5fn>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|3<space|2spc>Syntax>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-3><vspace|0.5fn>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|4<space|2spc>Solver
      Parameters and CLI> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-4><vspace|0.5fn>
    </associate>
  </collection>
</auxiliary>