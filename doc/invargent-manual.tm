<TeXmacs|1.0.7.18>

<style|article>

<\body>
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
  supports conjunctive patterns using the <verbatim|as> keyword, but it
  currently does not support disjunctive patterns. It currently has limited
  support for guarded patterns: after <verbatim|when>, only inequality
  <verbatim|\<less\>=> between values of the <verbatim|Num> type are allowed.

  The sort of a type variable is identified by the first letter of the
  variable. <verbatim|a>,<verbatim|b>,<verbatim|c>,<verbatim|r>,<verbatim|s>,<verbatim|t>,<verbatim|a1>,...
  are in the sort of terms called <verbatim|type>, i.e. ``types proper''.
  <verbatim|i>,<verbatim|j>,<verbatim|k>,<verbatim|l>,<verbatim|m>,<verbatim|n>,<verbatim|i1>,...
  are in the sort of linear arithmetics over rational numbers called
  <verbatim|num>. Remaining letters are reserved for sorts that may be added
  in the future. Value constructors (like in OCaml) and type constructors
  (unlike in OCaml) have the same syntax: capitalized name followed by a
  tuple of arguments. They are introduced by <verbatim|datatype> and
  <verbatim|datacons> respectively. The <verbatim|datatype> declaration might
  be misleading in that it only lists the sorts of the arguments of the type,
  the resulting sort is always <verbatim|type>. Values assumed into the
  environment are introduced by <verbatim|external>. There is a built-in type
  corresponding to declaration <verbatim|datatype Num : num> and definitions
  of numeric constants <verbatim|newcons 0 : Num 0 newcons 1 : Num 1>... The
  programmer can use <verbatim|external> declarations to give the semantics
  of choice to the <verbatim|Num> data-type. The type with additional support
  as <verbatim|Num> is the integers.

  When solving negative constraints, arising from <verbatim|assert false>
  clauses, we assume that the intended domain of the sort <verbatim|num> is
  integers. This is a workaround to the lack of strict inequality in the sort
  <verbatim|num>. We do not make the whole sort <verbatim|num> an integer
  domain because it would complicate the algorithms.

  In examples here we use Unicode characters. For ASCII equivalents, take a
  quick look at the tables in the following section.

  We start simple, with a function that can compute a value from a
  representation of an expression -- a ready to use value whether it be
  <verbatim|Int> or <verbatim|Bool>. Prior to the introduction of GADT types,
  we could only implement a function <verbatim|eval : <math|\<forall\>>a.
  Term a <math|\<rightarrow\>> Value> where, using OCaml syntax,
  <verbatim|type value = Int of int \| Bool of bool>.

  <\code>
    datatype Term : type

    external let plus : Int <math|\<rightarrow\>> Int <math|\<rightarrow\>>
    Int = "(+)"

    external let is_zero : Int <math|\<rightarrow\>> Bool = "(=) 0"

    datacons Lit : Int <math|\<longrightarrow\>> Term Int

    datacons Plus : Term Int * Term Int <math|\<longrightarrow\>> Term Int

    datacons IsZero : Term Int <math|\<longrightarrow\>> Term Bool

    datacons If : <math|\<forall\>>a. Term Bool * Term a * Term a
    <math|\<longrightarrow\>> Term a

    \;

    let rec eval = function

    \ \ \| Lit i -\> i

    \ \ \| IsZero x -\> is_zero (eval x)

    \ \ \| Plus (x, y) -\> plus (eval x) (eval y)

    \ \ \| If (b, t, e) -\> if eval b then eval t else eval e
  </code>

  Let us look at the corresponding generated, also called <em|exported>,
  OCaml source code:

  <\code>
    type _ term =

    \ \ \| Lit : int -\> int term

    \ \ \| Plus : int term * int term -\> int term

    \ \ \| IsZero : int term -\> bool term

    \ \ \| If : (*<math|\<forall\>>'a.*)bool term * 'a term * 'a term
    -\<gtr\> 'a term

    \ \ 

    let plus : (int -\> int -\> int) = (+)

    let is_zero : (int -\> bool) = (=) 0

    let rec eval : type a . (a term -\> a) =

    \ \ (function Lit i -\> i \| IsZero x -\> is_zero (eval x)

    \ \ \ \ \| Plus (x, y) -\> plus (eval x) (eval y)

    \ \ \ \ \| If (b, t, e) -\> (if eval b then eval t else eval e))
  </code>

  The <verbatim|Int>, <verbatim|Num> and <verbatim|Bool> types are built-in.
  <verbatim|Int> and <verbatim|Bool> follow the general scheme of exporting a
  datatype constructor with the same name, only lower-case. However, numerals
  <verbatim|0>, <verbatim|1>, ... are always type-checked as <verbatim|Num
  0>, <verbatim|Num 1>... <verbatim|Num> can also be exported as a type other
  than <verbatim|int>, and then numerals are exported via an injection
  function (ending with) <verbatim|of_int>.

  The syntax <verbatim|external let> allows us to name an OCaml library
  function or give an OCaml definition which we opt-out from translating to
  InvarGenT. Such a definition will be verified against the rest of the
  program when InvarGenT calls <verbatim|ocamlc -c> (or Haskell in the
  future) to verify the exported code. Another variant of <verbatim|external>
  (omitting the <verbatim|let> keyword) exports a value using
  <verbatim|external> in OCaml code, which is OCaml source declaration of the
  foreign function interface of OCaml. When we are not interested in linking
  and running the exported code, we can omit the part starting with the
  <verbatim|=> sign. The exported code will reuse the name in the FFI
  definition: <verbatim|external f : >...<verbatim| = "f">.

  The type inferred is <verbatim|eval : <math|\<forall\>>a. Term
  a<math|\<rightarrow\>>a>. GADTs make it possible to reveal that
  <verbatim|IsZero x> is a <verbatim|Term Bool> and therefore the result of
  <verbatim|eval> should in its case be <verbatim|Bool>, <verbatim|Plus (x,
  y)> is a <verbatim|Term Num> and the result of <verbatim|eval> should in
  its case be <verbatim|Num>, etc. The <verbatim|if/eif<math|\<ldots\>>then<math|\<ldots\>>else<math|\<ldots\>>>
  syntax is a syntactic sugar for <verbatim|match<math|/>ematch
  <math|\<ldots\>> with True -\<gtr\> <math|\<ldots\>> \| False -\<gtr\>
  <math|\<ldots\>>>, and any such expressions are exported using
  <verbatim|if> expressions.

  <verbatim|equal> is a function comparing values provided representation of
  their types:

  <\code>
    datatype Ty : type

    datatype Int

    datatype List : type

    datacons Zero : Int

    datacons Nil : <math|\<forall\>>a. List a

    datacons TInt : Ty Int

    datacons TPair : <math|\<forall\>>a, b. Ty a * Ty b
    <math|\<longrightarrow\>> Ty (a, b)

    datacons TList : <math|\<forall\>>a. Ty a <math|\<longrightarrow\>> Ty
    (List a)

    datatype Boolean

    datacons True : Boolean

    datacons False : Boolean

    external eq_int : Int <math|\<rightarrow\>> Int <math|\<rightarrow\>>
    Bool

    external b_and : Bool <math|\<rightarrow\>> Bool <math|\<rightarrow\>>
    Bool

    external b_not : Bool <math|\<rightarrow\>> Bool

    external forall2 : <math|\<forall\>>a, b. (a <math|\<rightarrow\>> b
    <math|\<rightarrow\>> Bool) <math|\<rightarrow\>> List a
    <math|\<rightarrow\>> List b <math|\<rightarrow\>> Bool

    \;

    let rec equal = function

    \ \ \| TInt, TInt -\> fun x y -\> eq_int x y

    \ \ \| TPair (t1, t2), TPair (u1, u2) -\> \ 

    \ \ \ \ (fun (x1, x2) (y1, y2) -\>

    \ \ \ \ \ \ \ \ b_and (equal (t1, u1) x1 y1)

    \ \ \ \ \ \ \ \ \ \ \ \ \ \ (equal (t2, u2) x2 y2))

    \ \ \| TList t, TList u -\> forall2 (equal (t, u))

    \ \ \| _ -\> fun _ _ -\> False
  </code>

  InvarGenT returns an unexpected type: <verbatim|equal<math|:\<forall\>>a,b.(Ty
  a, Ty b)<math|\<rightarrow\>>a<math|\<rightarrow\>>a<math|\<rightarrow\>>Bool>,
  one of four maximally general types of <verbatim|equal> as defined above.
  The other maximally general ``wrong'' types are
  <verbatim|<math|\<forall\>>a,b.(Ty a, Ty
  b)<math|\<rightarrow\>>b<math|\<rightarrow\>>b<math|\<rightarrow\>>Bool>
  and <verbatim|<math|\<forall\>>a,b.(Ty a, Ty
  b)<math|\<rightarrow\>>b<math|\<rightarrow\>>a<math|\<rightarrow\>>Bool>.
  This illustrates that unrestricted type systems with GADTs lack principal
  typing property.

  InvarGenT commits to a type of a toplevel definition before proceeding to
  the next one, so sometimes we need to provide more information in the
  program. Besides type annotations, there are three means to enrich the
  generated constraints: <verbatim|assert false> syntax for providing
  negative constraints, <verbatim|assert type e1 = e2; <math|\<ldots\>>> and
  <verbatim|assert num e1 \<less\>= e2; <math|\<ldots\>>> for positive
  constraints, and <verbatim|test> syntax for including constraints of use
  cases with constraint of a toplevel definition. To ensure only one
  maximally general type for <verbatim|equal>, we use <verbatim|assert false>
  and <verbatim|test>. We can either add the <verbatim|assert false> clauses:

  <\code>
    \ \ \| TInt, TList l -\> (function Nil -\> assert false)

    \ \ \| TList l, TInt -\> (fun _ -\> function Nil -\> assert false)
  </code>

  The first assertion excludes independence of the first encoded type and the
  second argument. The second assertion excludes independence of the second
  encoded type and the third argument. Or we can add the <verbatim|test>
  clause:

  <\code>
    test b_not (equal (TInt, TList TInt) Zero Nil)
  </code>

  The test ensures that arguments of distinct types can be <no-break>given.
  InvarGenT returns the expected type <verbatim|equal<math|:\<forall\>>a,b.(Ty
  a, Ty b)<math|\<rightarrow\>>a<math|\<rightarrow\>>b<math|\<rightarrow\>>Bool>.

  Now we demonstrate numerical invariants:

  <\code>
    datatype Binary : num

    datatype Carry : num

    datacons Zero : Binary 0

    datacons PZero : <math|\<forall\>>n[0<math|\<leq\>>n]. Binary n
    <math|\<longrightarrow\>> Binary(2 n)

    datacons POne : <math|\<forall\>>n[0<math|\<leq\>>n]. Binary n
    <math|\<longrightarrow\>> Binary(2 n + 1)

    datacons CZero : Carry 0

    datacons COne : Carry 1

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

  We get <verbatim|plus<math|:\<forall\>>i,k,n.Carry
  i<math|\<rightarrow\>>Binary k<math|\<rightarrow\>>Binary
  n<math|\<rightarrow\>>Binary (n + k + i)>.

  We can introduce existential types directly in type declarations. To have
  an existential type inferred, we have to use <verbatim|efunction> or
  <verbatim|ematch> expressions, which differ from <verbatim|function> and
  <verbatim|match> only in that the (return) type is an existential type. To
  use a value of an existential type, we have to bind it with a
  <verbatim|let>..<verbatim|in> expression. Otherwise, the existential type
  will not be unpacked. An existential type will be automatically unpacked
  before being ``repackaged'' as another existential type.

  <\code>
    datatype Room

    datatype Yard

    datatype Village

    datatype Castle : type

    datatype Place : type

    datacons Room : Room <math|\<longrightarrow\>> Castle Room

    datacons Yard : Yard <math|\<longrightarrow\>> Castle Yard

    datacons CastleRoom : Room <math|\<longrightarrow\>> Place Room

    datacons CastleYard : Yard <math|\<longrightarrow\>> Place Yard

    datacons Village : Village <math|\<longrightarrow\>> Place Village

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
    datatype Bool

    datacons True : Bool

    datacons False : Bool

    datatype List : type * num

    datacons LNil : <math|\<forall\>>a. List(a, 0)

    datacons LCons : <math|\<forall\>>n,a[0<math|\<leq\>>n]. a * List(a, n)
    <math|\<longrightarrow\>> List(a, n+1)

    \;

    let rec filter = fun f -\>

    \ \ efunction LNil -\> LNil

    \ \ \ \ \| LCons (x, xs) -\>

    \ \ \ \ \ \ eif f x then

    \ \ \ \ \ \ \ \ \ \ let ys = filter f xs in

    \ \ \ \ \ \ \ \ \ \ LCons (x, ys)

    \ \ \ \ \ \ else filter f xs
  </code>

  We get <verbatim|filter<math|:\<forall\>>n,
  a.(a<math|\<rightarrow\>>Bool)<math|\<rightarrow\>>List (a,
  n)<math|\<rightarrow\>> <math|\<exists\>>k[0<math|\<leq\>>n
  <math|\<wedge\>> 0<math|\<leq\>>k <math|\<wedge\>> k<math|\<leq\>>n].List
  (a, k)>. Note that we need to use both <verbatim|efunction> and
  <verbatim|eif> above, since every use of <verbatim|function>,
  <verbatim|match> or <verbatim|if> will force the types of its branches to
  be equal. In particular, for lists with length the resulting length would
  have to be the same in each branch. If the constraint cannot be met, as for
  <verbatim|filter> with either <verbatim|function> or <verbatim|if>, the
  code will not type-check.

  A more complex example that computes bitwise <em|or> -- <verbatim|ub>
  stands for ``upper bound'':

  <\code>
    datatype Binary : num

    datacons Zero : Binary 0

    datacons PZero : <math|\<forall\>>n [0<math|\<leq\>>n]. Binary n
    <math|\<longrightarrow\>> Binary(2 n)

    datacons POne : <math|\<forall\>>n [0<math|\<leq\>>n]. Binary n
    <math|\<longrightarrow\>> Binary(2 n + 1)

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

  <verbatim|ub:<math|\<forall\>>k,n.Binary k<math|\<rightarrow\>>Binary
  n<math|\<rightarrow\>><math|\<exists\>>:i[0<math|\<leq\>>n <math|\<wedge\>>
  0<math|\<leq\>>k <math|\<wedge\>> n<math|\<leq\>>i <math|\<wedge\>>
  k<math|\<leq\>>i <math|\<wedge\>> i<math|\<leq\>>n+k].Binary i>.

  Why cannot we shorten the above code by converting the initial cases to
  <verbatim|Zero -\<gtr\> (efunction b -\<gtr\> b)>? Without pattern
  matching, we do not make the contribution of <verbatim|Binary n> available.
  Knowing <verbatim|n<math|=>i> and not knowing <verbatim|0<math|\<leq\>>n>,
  for the case <verbatim|k<math|=>0>, we get:
  <verbatim|ub:<math|\<forall\>>k,n.Binary k<math|\<rightarrow\>>Binary
  n<math|\<rightarrow\>><math|\<exists\>>i[0<math|\<leq\>>k<math|\<wedge\>>n<math|\<leq\>>i<math|\<wedge\>>i<math|\<leq\>>n+k].Binary
  i>. <verbatim|n<math|\<leq\><no-break>>i> follows from
  <verbatim|n<math|=>i>, <verbatim|i<math|\<leq\>>n+k> follows from
  <verbatim|n<math|=>i> and <verbatim|0<math|\<leq\>>k>, but
  <verbatim|k<math|\<leq\>>i> cannot be inferred from <verbatim|k<math|=>0>
  and <verbatim|n<math|=>i> without knowing that <verbatim|0<math|\<leq\>>n>.

  Besides displaying types of toplevel definitions, InvarGenT can also export
  an OCaml source file with all the required GADT definitions and type
  annotations.

  <section|Syntax>

  Below we present, using examples, the syntax of InvarGenT: the mathematical
  notation, the concrete syntax in ASCII and the concrete syntax using
  Unicode.

  <block|<tformat|<cwith|1|1|2|2|cell-halign|c>|<cwith|1|1|1|1|cell-halign|l>|<cwith|2|2|2|2|cell-halign|c>|<cwith|2|2|1|1|cell-halign|l>|<cwith|3|3|2|2|cell-halign|l>|<table|<row|<cell|type
  variable: types>|<cell|<math|\<alpha\>,\<beta\>,\<gamma\>,\<tau\>>>|<cell|<verbatim|a>,<verbatim|b>,<verbatim|c>,<verbatim|r>,<verbatim|s>,<verbatim|t>,<verbatim|a1>,...>|<cell|>>|<row|<cell|type
  variable: nums>|<cell|<math|k,m,n>>|<cell|<verbatim|i>,<verbatim|j>,<verbatim|k>,<verbatim|l>,<verbatim|m>,<verbatim|n>,<verbatim|i1>,...>|<cell|>>|<row|<cell|type
  var. with coef.>|<cell|<math|<frac|1|3>n>>|<cell|<verbatim|1/3
  n>>|<cell|>>|<row|<cell|type constructor>|<cell|<math|List>>|<cell|<verbatim|List>>|<cell|>>|<row|<cell|number
  (type)>|<cell|<math|7>>|<cell|<verbatim|7>>|<cell|>>|<row|<cell|numerical
  sum (type)>|<cell|<math|m+n>>|<cell|<verbatim|m+n>>|<cell|>>|<row|<cell|existential
  type>|<cell|<math|\<exists\>k,n<around*|[|k\<leqslant\>n|]>.\<tau\>>>|<cell|<verbatim|ex
  k, n [k\<less\>=n].t>>|<cell|<verbatim|<math|\<exists\>>k,n[k<math|\<leq\>>n].t>>>|<row|<cell|type
  sort>|<cell|<math|s<rsub|ty>>>|<cell|<verbatim|type>>|<cell|>>|<row|<cell|number
  sort>|<cell|<math|s<rsub|R>>>|<cell|<verbatim|num>>|<cell|>>|<row|<cell|function
  type>|<cell|<math|\<tau\><rsub|1>\<rightarrow\>\<tau\><rsub|2>>>|<cell|<verbatim|t1
  -\<gtr\> t2>>|<cell|<verbatim|t1 <math|\<rightarrow\>><verbatim|
  t2>>>>|<row|<cell|equation>|<cell|<math|a<wide|=|\<dot\>>b>>|<cell|<verbatim|a
  = b>>|<cell|>>|<row|<cell|inequation>|<cell|<math|k\<leqslant\>n>>|<cell|<verbatim|k
  \<less\>= n>>|<cell|<verbatim|k <math|\<leq\>>
  n>>>|<row|<cell|conjunction>|<cell|<math|\<varphi\><rsub|1>\<wedge\>\<varphi\><rsub|2>>>|<cell|<verbatim|a=b
  && b=a>>|<cell|<verbatim|a=b <math|\<wedge\>> b=a>>>>>>

  For the syntax of expressions, we discourage non-ASCII symbols. Below
  <math|e,e<rsub|i>> stand for any expression, <math|p,p<rsub|i>> stand for
  any pattern, <math|x> stands for any lower-case identifier and <math|K> for
  an upper-case identifier. <math|K<rsub|T>> stands for <verbatim|True>,
  <math|K<rsub|F>> for <verbatim|False>, and <math|K<rsub|u>> for
  <verbatim|()>.

  <block|<tformat|<table|<row|<cell|named
  value>|<cell|<math|x>>|<cell|<verbatim|x> \ --lower-case
  identifier>>|<row|<cell|numeral (expr.)>|<cell|<math|7>>|<cell|<verbatim|7>>>|<row|<cell|constructor>|<cell|<math|K>>|<cell|<verbatim|K>
  \ --upper-case identifier>>|<row|<cell|application>|<cell|<math|e<rsub|1>
  e<rsub|2>>>|<cell|<verbatim|e1 e2>>>|<row|<cell|non-br.
  function>|<cell|<math|\<lambda\><around*|(|p<rsub|1>.\<lambda\><around*|(|p<rsub|2>.e|)>|)>>>|<cell|<verbatim|fun
  (p1,p2) p3 -\<gtr\> e>>>|<row|<cell|branching
  function>|<cell|<math|\<lambda\><around*|(|p<rsub|1>.e<rsub|1>\<ldots\>p<rsub|n>.e<rsub|n>|)>>>|<cell|<verbatim|function
  p1-\<gtr\>e1 \| >...<verbatim| \| pn-\<gtr\>en>>>|<row|<cell|pattern
  match>|<cell|<math|\<lambda\><around*|(|p<rsub|1>.e<rsub|1>\<ldots\>p<rsub|n>.e<rsub|n>|)>
  e>>|<cell|<verbatim|match e with p1-\<gtr\>e1 \| >...<verbatim| \|
  pn-\<gtr\>en>>>|<row|<cell|if-then-else
  clause>|<cell|<math|\<lambda\><around*|(|K<rsub|T>.e<rsub|1>,K<rsub|F>.e<rsub|2>|)>
  e>>|<cell|<verbatim|if e then e1 else e2>>>|<row|<cell|if-then-else
  condition>|<cell|<math|\<lambda\><around*|(|_<with|math-font-series|bold|
  when >m\<leqslant\>n.e<rsub|1>,\<ldots\>|)> K<rsub|u>>>|<cell|<verbatim|if
  m \<less\>= n then e1 else e2>>>|<row|<cell|postcond.
  function>|<cell|<math|\<lambda\><around*|[|K|]><around*|(|p<rsub|1>.e<rsub|1>\<ldots\>p<rsub|n>.e<rsub|n>|)>>>|<cell|<verbatim|efunction
  p1-\<gtr\>e1 \| >...>>|<row|<cell|postcond.
  match>|<cell|<math|\<lambda\><around*|[|K|]><around*|(|p<rsub|1>.e<rsub|1>\<ldots\>p<rsub|n>.e<rsub|n>|)>
  e>>|<cell|<verbatim|ematch e with p1-\<gtr\>e1 \|
  >...>>|<row|<cell|eif-then-else clause>|<cell|<math|\<lambda\><around*|[|K|]><around*|(|K<rsub|T>.e<rsub|1>,K<rsub|F>.e<rsub|2>|)>
  e>>|<cell|<verbatim|eif e then e1 else e2>>>|<row|<cell|eif-then-else
  condition>|<cell|<math|\<lambda\><around*|[|K|]><around*|(|_<with|math-font-series|bold|
  when >m\<leqslant\>n.e<rsub|1>,\<ldots\>|)> K<rsub|u>>>|<cell|<verbatim|eif
  m \<less\>= n then e1 else e2>>>|<row|<cell|rec.
  definition>|<cell|<math|<with|math-font-series|bold|letrec> x=e<rsub|1>
  <with|math-font-series|bold|in> e<rsub|2>>>|<cell|<verbatim|let rec x = e1
  in e2>>>|<row|<cell|definition>|<cell|<math|<with|math-font-series|bold|let>
  p=e<rsub|1> <with|math-font-series|bold|in> e<rsub|2>>>|<cell|<verbatim|let
  p1,p2 = e1 in e2>>>|<row|<cell|asserting dead
  br.>|<cell|<math|\<b-F\>>>|<cell|<verbatim|assert
  false>>>|<row|<cell|assert equal types>|<cell|<math|<with|math-font-series|bold|assert
  type >\<tau\><rsub|e<rsub|1>><wide|=|\<dot\>>\<tau\><rsub|e<rsub|2>>;e<rsub|3>>>|<cell|<verbatim|assert
  type e1 = e2; e3>>>|<row|<cell|assert inequality>|<cell|<math|<with|math-font-series|bold|assert
  num >e<rsub|1>\<leqslant\>e<rsub|2>;e<rsub|3>>>|<cell|<verbatim|assert num
  e1 \<less\>= e2; e3>>>>>>

  Toplevel expressions (corresponding to structure items in OCaml) introduce
  types, type and value constructors, global variables with given type
  \ (external names) or inferred type (definitions).

  <block|<tformat|<cwith|1|1|2|2|cell-halign|l>|<cwith|1|1|1|1|cell-halign|l>|<table|<row|<cell|type
  constructor>|<cell|<verbatim|datatype List : type * num>>>|<row|<cell|value
  constructor>|<cell|<verbatim|datacons Cons : all n a. a * List(a,n)
  --\<gtr\> List(a,n+1)>>>|<row|<cell|>|<cell|<verbatim|datacons Cons :
  <math|\<forall\>>n,a. a * List(a,n) <math|\<longrightarrow\>>
  List(a,n+1)>>>|<row|<cell|declaration>|<cell|<verbatim|external foo :
  <math|\<forall\>>n,a. List(a,n)<math|\<rightarrow\>
  \<exists\>>k[k\<less\>=n].List(a,k)="c_foo">>>|<row|<cell|>|<cell|<verbatim|external
  filter : <math|\<forall\>>n,a. List(a,n)<math|\<rightarrow\>
  \<exists\>>k[k\<less\>=n].List(a,k)>>>|<row|<cell|let-declaration>|<cell|<verbatim|external
  let mult : <math|\<forall\>>n,m. Num n<math|\<rightarrow\>>Num
  m<math|\<rightarrow\> \<exists\>>k.Num k = "( * )">>>|<row|<cell|rec.
  definition>|<cell|<verbatim|let rec f =>...>>|<row|<cell|non-rec.
  definition>|<cell|<verbatim|let a, b =>...>>|<row|<cell|definition with
  test>|<cell|<verbatim|let rec f =>...<verbatim| test e1; >...<verbatim|;
  en>>>>>>

  Tests list expressions of type <verbatim|Bool> that at runtime have to
  evaluate to <verbatim|True>. Type inference is affected by the constraints
  generated to typecheck the expressions.

  There are variants of the if-then-else clause syntax supporting
  <math|<with|math-font-series|bold|when>> conditions:

  <\itemize>
    <item><verbatim|if m1 \<less\>= n1 && m2 \<less\>= n2 && <math|\<ldots\>>
    then e1 else e2> is <math|\<lambda\><around*|(|_<with|math-font-series|bold|
    when >\<wedge\><rsub|i>m<rsub|i>\<leqslant\>n<rsub|i>.e<rsub|1>,_.e<rsub|2>|)>
    K<rsub|u>>,

    <item><verbatim|if m \<less\>= n then e1 else e2> is
    <math|\<lambda\><around*|(|_<with|math-font-series|bold| when
    >m\<leqslant\>n.e<rsub|1>,_<with|math-font-series|bold| when
    >n+1\<leqslant\>m.e<rsub|2>|)> K<rsub|u>> if integer mode is on (as in
    default setting),

    <item>similarly for the <verbatim|eif> variants.
  </itemize>

  We add the standard syntactic sugar for function definitions:

  <\itemize>
    <item><verbatim|let <math|p<rsub|1>> <math|p<rsub|2>> <math|\<ldots\>>
    <math|p<rsub|n>> = <math|e<rsub|1>> in <math|e<rsub|2>>> expands to
    <verbatim|let <math|p<rsub|1>> = fun <math|p<rsub|2>> <math|\<ldots\>>
    <math|p<rsub|n>> -\<gtr\> <math|e<rsub|1>> in <math|e<rsub|2>>>

    <item><verbatim|let rec <math|l<rsub|1>> <math|p<rsub|2>>
    <math|\<ldots\>> <math|p<rsub|n>> = <math|e<rsub|1>> in <math|e<rsub|2>>>
    expands to <verbatim|let rec <math|l<rsub|1>> = fun <math|p<rsub|2>>
    <math|\<ldots\>> <math|p<rsub|n>> -\<gtr\> <math|e<rsub|1>> in
    <math|e<rsub|2>>>

    <item>top-level <verbatim|let> and <verbatim|let rec> definitions expand
    correspondingly.
  </itemize>

  For simplicity of theory and implementation, mutual non-nested recursion
  and or-patterns are not provided. For mutual recursion, nest one recursive
  definition inside another.

  Like in OCaml, types of arguments in declarations of constructors are
  separated by asterisks. However, the type constructor for tuples is
  represented by commas, like in Haskell but unlike in OCaml.

  At any place between lexemes, regular comments encapsulated in
  <verbatim|(*<math|\<ldots\>>*)> can occur. They are ignored during lexing.
  In front of all toplevel definitions and declarations, e.g. before a
  <verbatim|datatype>, <verbatim|datacons>, <verbatim|external>,
  <verbatim|let rec> or <verbatim|let>, and in front of <verbatim|let rec> ..
  <verbatim|in> and <verbatim|let> .. <verbatim|in> nodes in expressions,
  documentation comments <verbatim|(**<math|\<ldots\>>*)> can be put.
  Documentation comments at other places are syntax errors. Documentation
  comments are preserved both in generated interface files and in exported
  source code files.

  <section|Solver Parameters and CLI>

  The default settings of InvarGenT parameters should be sufficient for most
  cases. For example, after downloading InvarGenT source code and changing
  current directory to <verbatim|invargent>, we can enter, assuming a
  Unix-like shell:

  <\code>
    $ make main

    $ ./invargent examples/binary_upper_bound.gadt
  </code>

  To get the inferred types printed on standard output, use the
  <verbatim|-inform> option:

  <\code>
    $ ./invargent -inform examples/binomial_heap_nonrec.gadt
  </code>

  In some situations, hopefully unlikely for simple programs, the default
  parameters of the solver algorithms do not suffice. Consider this example,
  where we use <verbatim|-full_annot> to generate type annotations on
  <verbatim|function> and <verbatim|let>..<verbatim|in> nodes in the
  <verbatim|.ml> file, in addition to annotations on <verbatim|let rec>
  nodes:

  <\code>
    $ ./invargent -inform -full_annot examples/equal_assert.gadt

    File "examples/equal_assert.gadt", line 20, characters 5-103:

    No answer in type: term abduction failed

    \;

    Perhaps increase the -term_abduction_timeout parameter.

    Perhaps increase the -term_abduction_fail parameter.
  </code>

  The <verbatim|Perhaps increase> suggestions are generated only when the
  corresponding limit has actually been exceeded. Remember however that the
  limits will often be exceeded for erroneus programs which should not
  type-check. Here the default number of steps till term abduction timeout,
  which is just <verbatim|700> to speed up failing for actually erroneous
  programs, is too low. The complete output with timeout increased:

  <\code>
    $ ./invargent -inform -full_annot -term_abduction_timeout 4000 \\
    examples/<no-break>equal_assert.gadt

    val equal : <math|\<forall\>>a, b. (Ty a, Ty b) <math|\<rightarrow\>> a
    <math|\<rightarrow\>> b <math|\<rightarrow\>> Bool

    InvarGenT: Generated file examples/equal_assert.gadti

    InvarGenT: Generated file examples/equal_assert.ml

    InvarGenT: Command "ocamlc -c examples/equal_assert.ml" exited with code
    0
  </code>

  To understand the intent of the solver parameters, we need a rough
  ``birds-eye view'' understanding of how InvarGenT works. The invariants and
  postconditions that we solve for are logical formulas and can be ordered by
  strength. Least Upper Bounds (LUBs) and Greatest Lower Bounds (GLBs)
  computations are traditional tools used for solving recursive equations
  over an ordered structure. In case of implicational constraints that are
  generated for type inference with GADTs, constraint abduction is a form of
  LUB computation. <em|Disjunction elimination> is our term for computing the
  GLB wrt. strength for formulas that are conjunctions of atoms. We want the
  invariants of recursive definitions -- i.e. the types of recursive
  functions and formulas constraining their type variables -- to be as weak
  as possible, to make the use of the corresponding definitions as easy as
  possible. The weaker the invariant, the more general the type of
  definition. Therefore the use of LUB, constraint abduction. For
  postconditions -- i.e. the existential types of results computed by
  <verbatim|efunction> expressions and formulas constraining their type
  variables -- we want the strongest possible solutions, because stronger
  postcondition provides more information at use sites of a definition.
  Therefore we use GLB, disjunction elimination, but only if existential
  types have been introduced by <verbatim|efunction> or <verbatim|ematch>.

  Below we discuss all of the InvarGenT options.

  <\description>
    <item*|<verbatim|-inform>>Print type schemes of toplevel definitions as
    they are inferred.

    <item*|<verbatim|-time>>Print the time it took to infer type schemes of
    toplevel definitions.

    <item*|<verbatim|-no_sig>>Do not generate the <verbatim|.gadti> file.

    <item*|<verbatim|-no_ml>>Do not generate the <verbatim|.ml> file.

    <item*|<verbatim|-no_verif>>Do not call <verbatim|ocamlc -c> on the
    generated <verbatim|.ml> file.

    <item*|<verbatim|-num_is>>The exported type for which <verbatim|Num> is
    an alias (default <verbatim|int>). If <verbatim|-num_is bar> for
    <verbatim|bar> different than <verbatim|int>, numerals are exported as
    integers passed to a <verbatim|bar_of_int> function. The variant
    <verbatim|-num_is_mod> exports numerals by passing to a
    <verbatim|Bar.of_int> function.

    <item*|<verbatim|-full_annot>>Annotate the <verbatim|function> and
    <verbatim|let>..<verbatim|in> nodes in generated OCaml code. This
    increases the burden on inference a bit because the variables associated
    with the nodes cannot be eliminated from the constraint during initial
    simplification.

    <item*|<verbatim|-keep_assert_false>>Keep <verbatim|assert false> clauses
    in exported code. When faced with multiple maximally general types of a
    function, we sometimes want to prevent some interpretations by asserting
    that a combination of arguments is not possible. These arguments will not
    be compatible with the type inferred, causing exported code to fail to
    typecheck. Sometimes we indicate unreachable cases just for
    documentation. If the type is tight this will cause exported code to fail
    to typecheck too. This option keeps pattern matching branches with
    <verbatim|assert false> in their bodies in exported code nevertheless.

    <item*|<verbatim|-allow_dead_code>>Allow more programs with dead code
    than would otherwise pass.

    <item*|<verbatim|-force_no_dead_code>>Reject all programs with dead code
    (may misclassify programs using <em|min> or <em|max> atoms). Unreachable
    pattern matching branches lead to unsatisfiable premises of the type
    inference constraint, which we detect. However, sometimes multiple
    implications in the simplified form of the constraint can correspond to
    the same path through the program, in particular when solving constraints
    with <em|min> and <em|max> clauses. Dead code due to datatype mismatch,
    i.e. patterns unreachable without resort to numerical constraints, is
    detected even without using this option.

    <item*|<verbatim|-term_abduction_timeout>>Limit on term simple abduction
    steps (default 700). Simple abduction works with a single implication
    branch, which roughly corresponds to a single branch -- an execution path
    -- of the program.

    <item*|<verbatim|-term_abduction_fail>>Limit on backtracking steps in
    term joint abduction (default 4). Joint abduction combines results for
    all branches of the constraints.

    <item*|<verbatim|-no_alien_prem>>Do not include alien (e.g. numerical)
    premise information in term abduction.

    <item*|<verbatim|-early_num_abduction>>Include recursive branches in
    numerical abduction from the start. By default, in the second iteration
    of solving constraints, which is the first iteration that numerical
    abduction is performed, we only pass non-recursive branches to numerical
    abduction. This makes it faster but less likely to find the correct
    solution.

    <item*|<verbatim|-early_postcond_abd>>Include postconditions from
    recursive calls in abduction from the start. We do not derive
    requirements put on postconditions by recursive calls on first iteration.
    The requirements may turn smaller after some derived invariants are
    included in the premises. This option turns off the special treatment of
    postconditions on first iteration.

    <item*|<verbatim|-num_abduction_rotations>>Numerical abduction:
    coefficients from <math|\<pm\>1/N> to <math|\<pm\>N> (default 3).
    Numerical abduction answers are built, roughly speaking, by adding
    premise equations of a branch with conclusion of a branch to get an
    equation or inequality that does not conflict with other branches, but is
    equivalent to the conclusion equation/inequality. This parameter decides
    what range of coefficients is tried. If the highest coefficient in
    correct answer is greater, abduction might fail.

    <item*|<verbatim|-num_prune_at>>Keep less than <math|N> elements in
    abduction sums (default 6). By elements here we mean distinct variables
    -- lack of constant multipliers in concrete syntax of types is just a
    syntactic shortcoming.

    <item*|<verbatim|-num_abduction_timeout>>Limit on numerical simple
    abduction steps (default 1000).

    <item*|<verbatim|-num_abduction_fail>>Limit on backtracking steps in
    numerical joint abduction (default 10).

    <item*|<verbatim|-affine_penalty>>How much to penalize an abduction
    candidate inequality for containing a constant term (default 1). Too
    small a value may lead to divergence, e.g. in some examples abduction
    will pick an answer <math|a+1>, which in the following step will force an
    answer <math|a+2>, then <math|a+3>, etc.

    <item*|<verbatim|-more_general_num>>Filter out less general abduction
    candidate atoms (does not guarantee overall more general answers). The
    filtering is currently not performed by default to save on computational
    cost.

    <item*|<verbatim|-no_num_abduction>>Turn off numerical abduction; will
    not ensure correctness. Numerical abduction uses a brute-force algorithm
    and will fail to work in reasonable time for complex constraints.
    However, including the effects of <verbatim|assert false> clauses, and
    inference of postconditions, do not rely on numerical abduction. If the
    numerical invariant of a typeable (i.e. correct) function follows from
    <verbatim|assert false> facts alone, a call with
    <verbatim|-no_num_abduction> may still find the correct invariant and
    postcondition.

    <item*|<verbatim|-if_else_no_when>>Do not add <verbatim|when> clause to
    the <verbatim|else> branch of an <verbatim|if> expression with a single
    inequality as condition. Expressions <verbatim|if>, resp. <verbatim|eif>,
    with a single inequality as the condition are expanded into expressions
    <verbatim|match>, resp. <verbatim|ematch>, with <verbatim|when>
    conditions on both the <verbatim|True> branch and the <verbatim|False>
    branch. I.e. <verbatim|if m \<less\>= n then e1 else e2> is expanded into
    <verbatim|match () with _ when m \<less\>= n -\<gtr\> e1 \| _ when n+1
    \<less\>= m -\<gtr\> e2>. Passing <verbatim|-if_else_no_when> will result
    in expansion <verbatim|match () with _ when m \<less\>= n -\<gtr\> e1 \|
    _ -\<gtr\> e2>. The same effect can be achieved for a particular
    expression by artificially incresing the number of inequalities:
    <verbatim|if m \<less\>= n && m \<less\>= n then e1 else e2>.

    <item*|<verbatim|-weaker_pruning>>Do not assume integers as the numerical
    domain when pruning redundant atoms.

    <item*|<verbatim|-stronger_pruning>>Prune atoms that force a numerical
    variable to a single value under certain conditions; exclusive with
    <verbatim|-weaker_pruning>.

    <item*|<verbatim|-disjelim_rotations>>Disjunction elimination: check
    coefficients from <math|1/N> (default 3). Numerical disjunction
    elimination is performed by approximately finding the convex hull of the
    polytopes corresponding to disjuncts. A step in an exact algorithm
    involves rotating a side along a ridge -- an intersection with another
    side -- until the side touches yet another side. We approximate by trying
    out a couple of rotations: convex combinations of the inequalities
    defining the sides. This parameter decides how many rotations to try.

    <item*|<verbatim|-postcond_opti_limit>>Limit the number of atoms
    <math|x=min(a,b)>, <math|x=max(a,b)> in (intermediate and final)
    postconditions (default 4). Unfortunately, inference time is exponential
    in the number of atoms of this form. The final postconditions usually
    have few of these atoms, but a greater number is sometimes needed in the
    intermediate steps of the main loop.\ 

    <item*|<verbatim|-postcond_subopti_limit>>Limit the number of atoms
    <math|min(a,b)\<leqslant\>x>, <math|x\<leqslant\>max(a,b)> in
    (intermediate and final) postconditions (default 4). Unfortunately,
    inference time is exponential in the number of atoms of this form. The
    final postconditions usually have few of these atoms, but a greater
    number is sometimes needed in the intermediate steps of the main loop.

    <item*|<verbatim|-iterations_timeout>>Limit on main algorithm iterations
    (default 6). Answers found in an iteration of the main algorithm are
    propagated to use sites in the next iteration. However, for about four
    initial iterations, each iteration turns on additional processing which
    makes better sense with the results from the previous iteration
    propagated. At least three iterations will always be performed.

    <item*|<verbatim|-richer_answers>>Keep some equations in term abduction
    answers even if redundant. Try keeping an initial guess out of a list of
    candidate equations before trying to drop the equation from
    consideration. We use fully maximal abduction for single branches, which
    cannot find answers not implied by premise and conclusion of a branch.
    But we seed it with partial answer to branches considered so far.
    Sometimes an atom is required to solve another branch although it is
    redundant in given branch. <verbatim|-richer_answers> does not increase
    computational cost but sometimes leads to answers that are not most
    general. This can always be fixed by adding a <verbatim|test> clause to
    the definition which uses a type conflicting with the too specific type.

    <item*|<verbatim|-prefer_guess>>Try to guess equality-between-parameters
    before considering other possibilities. Implied by
    <verbatim|-richer_answers> but less invasive.

    <item*|<verbatim|-more_existential>>More general invariant at expense of
    more existential postcondition. To avoid too abstract postconditions,
    disjunction elimination can infer additional constraints over invariant
    parameters. In rare cases a weaker postcondition but a more general
    invariant can be beneficial.

    <item*|<verbatim|-show_extypes>>Show datatypes encoding existential
    types, and their identifiers with uses of existential types. The type
    system in InvarGenT encodes existential types as GADT types, but this
    representation is hidden from the user. Using <verbatim|-show_extypes>
    exposes the representation as follows. The encodings are exported in
    <verbatim|.gadti> files as regular datatypes named <verbatim|exN>, and
    existential types are printed using syntax
    <verbatim|<math|\<exists\>>N:<math|\<ldots\>>> instead of
    <math|\<exists\>\<ldots\>>, where <verbatim|N> is the identifier of an
    existential type.

    <item*|<verbatim|-passing_ineq_trs>>Include inequalities in conclusion
    when solving numerical abduction. This setting leads to more inequalities
    being tried for addition in numeric abduction answer.

    <item*|<verbatim|-not_annotating_fun>>Do not keep information for
    annotating <verbatim|function> nodes. This may allow eliminating more
    variables during initial constraint simplification.

    <item*|<verbatim|-annotating_letin>>Keep information for annotating
    <verbatim|let>..<verbatim|in> nodes. Will be set automatically anyway
    when <verbatim|-full_annot> is passed.

    <item*|<verbatim|-let_in_fallback>>Annotate <verbatim|let>..<verbatim|in>
    nodes in fallback mode of <verbatim|.ml> generation. When verifying the
    resulting <verbatim|.ml> file fails, a retry is made with
    <verbatim|function> nodes annotated. This option additionally annotates
    <verbatim|let>..<verbatim|in> nodes with types in the regenerated
    <verbatim|.ml> file.
  </description>

  Let us see an example where a parameter allowing the solver do more search
  is needed:

  <\code>
    $ ./invargent -inform -num_abduction_rotations 4
    examples/flatten_quadrs.gadt

    val flatten_quadrs :

    \ \ <math|\<forall\>>n, a. List ((a, a, a, a), n) <math|\<rightarrow\>>
    List (a, 4 n)

    InvarGenT: Generated file examples/flatten_quadrs.gadti

    InvarGenT: Generated file examples/flatten_quadrs.ml

    InvarGenT: Command "ocamlc -c examples/flatten_quadrs.ml" exited with
    code 0
  </code>

  Based on user feedback, we will likely increase the default values of
  parameters in a future version.

  <section|Limitations of Current InvarGenT Inference>

  Type inference for the type system underlying InvarGenT is undecidable. In
  some cases, the failure to infer a type is not at all problematic. Consider
  this example due to Chuan-kai Lin:

  <\code>
    datatype EquLR : type * type * type

    datacons EquL : <math|\<forall\>>a, b. EquLR (a, a, b)

    datacons EquR : <math|\<forall\>>a, b. EquLR (a, b, b)

    datatype Box : type

    datacons Cons : <math|\<forall\>>a. a <math|\<longrightarrow\>> Box a

    external let eq : <math|\<forall\>>a. a <math|\<rightarrow\>> a
    <math|\<rightarrow\>> Bool = "(=)"

    \;

    let vary = fun e y -\<gtr\>

    \ \ match e with

    \ \ \| EquL, EquL -\<gtr\> eq y "c"

    \ \ \| EquR, EquR -\<gtr\> Cons (match y with True -\<gtr\> 5 \| False
    -\<gtr\> 7)
  </code>

  Although <verbatim|vary> has multiple types, it is a contrived example
  unlikely to have an intended type. However, not all cases of failure to
  infer a type for a correct program are due to contrived examples. The
  problems are not insurmountable theoretically. The algorithms used in the
  inference can incorporate heuristics for special cases, and can be modified
  to do a more exhaustive search.

  The following example illustrates a limitation of our numerical abduction
  algorithm that is not intrinsic to the numerical abduction problem. I.e. it
  might be fixed by a smarter algorithm.

  <\code>
    datatype Elem

    datatype List : num

    datacons LNil : List 0

    datacons LCons : <math|\<forall\>>n [0<math|\<leq\>>n]. Elem * List n
    <math|\<longrightarrow\>> List (n+1)

    external length : <math|\<forall\>>n. List n <math|\<rightarrow\>> Num n
    = "length"

    \;

    let rec append =

    \ \ function

    \ \ \ \ \| LNil -\<gtr\>

    \ \ \ \ \ \ (function l when (length l + 1) \<less\>= 0 -\<gtr\> assert
    false \| l -\<gtr\> l)

    \ \ \ \ \| LCons (x, xs) -\<gtr\>

    \ \ \ \ \ \ (function l when (length l + 1) \<less\>= 0 -\<gtr\> assert
    false

    \ \ \ \ \ \ \| l -\<gtr\> LCons (x, append xs l))
  </code>

  The expected type is <verbatim|append : <math|\<forall\>>a, n,
  k[0<math|\<leq\>>k]. List n<math|\<rightarrow\>>List
  k<math|\<rightarrow\>>List (n+k)>. When our algorithm discovers that the
  result is <math|n+k>, rather than <math|n>, it is already committed to
  requiring that the result is no less than <math|1>. The answers on
  successive iterations of the main algorithm do not converge: if the length
  of the tail has to be at least one, then the length of the input list has
  to be at least two, etc.

  The following example is a natural variant of a function from the
  <verbatim|avl_tree.gadt> example.

  <\code>
    let rec add = fun x -\<gtr\> efunction

    \ \ \| Empty -\<gtr\> Node (Empty, x, Empty, 1)

    \ \ \| Node (l, y, r, h) -\<gtr\>

    \ \ \ \ ematch compare x y with

    \ \ \ \ \| EQ -\<gtr\> Node (l, x, r, h)

    \ \ \ \ \| LT -\<gtr\>

    \ \ \ \ \ \ let l' = add x l in

    \ \ \ \ \ \ (ematch height l', height r with

    \ \ \ \ \ \ \ \| hl', hr when hl' \<less\>= hr+2 -\<gtr\> create l' y r

    \ \ \ \ \ \ \ \| hl', hr when hr+3 \<less\>= hl' -\<gtr\> rotr l' y r)

    \ \ \ \ \| GT -\<gtr\>

    \ \ \ \ \ \ let r' = add x r in

    \ \ \ \ \ \ (ematch height r', height l with

    \ \ \ \ \ \ \ \| hr', hl when hr' \<less\>= hl+2 -\<gtr\> create l y r'

    \ \ \ \ \ \ \ \| hr', hl when hl+3 \<less\>= hr' -\<gtr\> rotl l y r')
  </code>

  The difference with the function in the <verbatim|avl_tree.gadt> file
  amounts to computing <verbatim|height r>, resp. <verbatim|height l> near
  the places where they are used. The inference fails because of lack of
  sharing of information about <verbatim|l> due to facts about <verbatim|l' =
  add x l>, resp. about <verbatim|r> due to facts about <verbatim|r' = add x
  r>, with the other branch. The limits on information sharing between
  pattern matching branches can also manifest in more mundane situations.
  Compare for example the sources <verbatim|pointwise_extract.gadt> and
  <verbatim|pointwise_extract2.gadt> from the examples directory. Type
  inference fails for the latter example, which has functions as bodies of
  pattern matching branches, rather than deconstructing a variable introduced
  only once. More sophisticated algorithms might mitigate these shortcomings
  in future versions of InvarGenT.

  We end with an example where there is little hope of improvement. The
  <verbatim|rotr> and <verbatim|rotl> functions in <verbatim|avl_tree.gadt>
  use assertions to convey the preconditions. Ideally, we would like to be
  able to simply write an implementation similar to the following one:

  <\code>
    let rotr = fun l x r -\<gtr\>

    \ \ \ \ ematch l with

    \ \ \ \ \| Empty -\<gtr\> assert false

    \ \ \ \ \| Node (ll, lx, lr, _) -\<gtr\>

    \ \ \ \ \ \ (ematch height ll, height lr with

    \ \ \ \ \ \ \| m, n when n \<less\>= m -\<gtr\>

    \ \ \ \ \ \ \ \ let r' = create lr x r in

    \ \ \ \ \ \ \ \ create ll lx r'

    \ \ \ \ \ \ \| m, n when m+1 \<less\>= n -\<gtr\>

    \ \ \ \ \ \ \ \ (ematch lr with

    \ \ \ \ \ \ \ \ \| Empty -\<gtr\> assert false

    \ \ \ \ \ \ \ \ \| Node (lrl, lrx, lrr, _) -\<gtr\>

    \ \ \ \ \ \ \ \ \ \ let l' = create ll lx lrl in

    \ \ \ \ \ \ \ \ \ \ let r' = create lrr x r in

    \ \ \ \ \ \ \ \ \ \ create l' lrx r'))
  </code>

  Unfortunately, it seems it would require too much ``guesswork'' from the
  inference algorithms.
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
    <associate|auto-2|<tuple|2|1>>
    <associate|auto-20|<tuple|5.4|17|invargent.tm>>
    <associate|auto-21|<tuple|5.5|17|invargent.tm>>
    <associate|auto-22|<tuple|6|18|invargent.tm>>
    <associate|auto-23|<tuple|6|18|invargent.tm>>
    <associate|auto-24|<tuple|5.5|17>>
    <associate|auto-3|<tuple|3|5>>
    <associate|auto-4|<tuple|4|6>>
    <associate|auto-5|<tuple|5|9>>
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

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|5<space|2spc>Limitations
      of Current InvarGenT Inference> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-5><vspace|0.5fn>
    </associate>
  </collection>
</auxiliary>