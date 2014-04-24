<TeXmacs|1.99.1>

<style|beamer>

<\body>
  <screens|<\hidden>
    <tit|GADTs for Invariants and Postconditions>

    <\ornamented>
      <huge|Constraint-based type inference can be used for reconstruction of
      preconditions, invariants and postconditions of recursive functions
      written in languages with GADTs.>
    </ornamented>

    <\itemize>
      <item>InvarGenT infers preconditions and invariants as types of
      recursive definitions, and postconditions as existential types.

      <item>Generalized Algebraic Data Types type system <math|MMG(X)> based
      on François Pottier and Vincent Simonet's <math|HMG(X)> but without
      type annotations.

      <item>Extended to a language with existential types represented as
      implicitly defined and used GADTs.

      <item>Type inference problem as satisfaction of second order
      constraints over a multi-sorted domain.

      <item>Invariants found by <em|Joint Constraint Abduction under
      Quantifier Prefix>, postconditions found by <em|constraint
      generalization> -- anti-unification for terms, extended convex hull.

      <item>A numerical sort with linear equations and inequalities over
      rationals, and <math|k<wide|=|\<dot\>>min<around*|(|m,n|)>>,
      <math|k<wide|=|\<dot\>>max<around*|(|m,n|)>> relations (reconstructed
      only for postconditions).
    </itemize>
  </hidden>|<\hidden>
    <tit|The Type System>

    <\really-tiny>
      <\itemize>
        <item><tabular|<tformat|<table|<row|<cell|Patterns
        (syntax-directed)>|<cell|Clauses>>|<row|<cell|<tabular|<tformat|<table|<row|<cell|<verbatim|p-Empty>>|<cell|>|<cell|<verbatim|p-Wild>>>|<row|<cell|<math|C\<vdash\>0:\<tau\>\<longrightarrow\>\<exists\>\<varnothing\><around|[|\<b-F\>|]><around|{||}>>>|<cell|
        \ \ >|<cell|<math|C\<vdash\>1:\<tau\>\<longrightarrow\>\<exists\>\<varnothing\><around|[|\<b-T\>|]><around|{||}>>>>>>>>|<cell|<tabular|<tformat|<table|<row|<cell|<verbatim|Clause>>>|<row|<cell|<math|<frac|<tabular|<tformat|<cwith|1|1|3|3|cell-valign|c>|<table|<row|<cell|C\<vdash\>p:\<tau\><rsub|1>\<longrightarrow\>\<exists\><wide|\<beta\>|\<bar\>><around|[|D|]>\<Gamma\><rprime|'>>|<cell|C\<wedge\>D,\<Gamma\>\<Gamma\><rprime|'>\<vdash\>e:\<tau\><rsub|2>>|<cell|<wide|\<beta\>|\<bar\>>#FV<around|(|C,\<Gamma\>,\<tau\><rsub|2>|)>>>>>>|C,\<Gamma\>\<vdash\>p.e:\<tau\><rsub|1>\<rightarrow\>\<tau\><rsub|2>>>>>>>>>>|<row|<cell|<tabular|<tformat|<cwith|2|2|1|1|cell-halign|l>|<table|<row|<cell|<verbatim|p-And>>|<cell|>|<cell|>|<cell|<verbatim|p-Var>>>|<row|<cell|<math|<frac|\<forall\>i<with|mode|text|
        \ ><space|0.6spc>C\<vdash\>p<rsub|i>:\<tau\>\<longrightarrow\>\<Delta\><rsub|i>|C\<vdash\>p<rsub|1>\<wedge\>p<rsub|2>:\<tau\>\<longrightarrow\>\<Delta\><rsub|1>\<times\>\<Delta\><rsub|2>>>>|<cell|>|<cell|>|<cell|<math|C\<vdash\>x:\<tau\>\<longrightarrow\>\<exists\>\<varnothing\><around|[|\<b-T\>|]><around|{|x\<mapsto\>\<tau\>|}>>>>>>>>|<cell|<tabular|<tformat|<table|<row|<cell|<verbatim|WhenClause>>>|<row|<cell|<math|<frac|<tabular|<tformat|<cwith|3|3|3|3|cell-valign|c>|<table|<row|<cell|C\<wedge\>D,\<Gamma\>\<Gamma\><rprime|'>\<vdash\>m<rsub|i>:Num<around*|(|\<tau\><rsub|m<rsub|i>>|)>>|<cell|e\<neq\><with|math-font-series|bold|assert
        false>\<wedge\>\<ldots\>\<wedge\>>|<cell|>>|<row|<cell|C\<wedge\>D,\<Gamma\>\<Gamma\><rprime|'>\<vdash\>n<rsub|i>:Num<around*|(|\<tau\><rsub|n<rsub|i>>|)>>|<cell|e\<neq\>\<lambda\><around*|(|p<rprime|'>\<ldots\>\<lambda\><around*|(|p<rprime|''>.<with|math-font-series|bold|assert
        false>|)>|)>>|<cell|>>|<row|<cell|C\<vdash\>p:\<tau\><rsub|1>\<longrightarrow\>\<exists\><wide|\<beta\>|\<bar\>><around|[|D|]>\<Gamma\><rprime|'>>|<cell|C\<wedge\>D\<wedge\><rsub|i>\<tau\><rsub|m<rsub|i>>\<leqslant\>\<tau\><rsub|n<rsub|i>>,\<Gamma\>\<Gamma\><rprime|'>\<vdash\>e:\<tau\><rsub|2>>|<cell|<wide|\<beta\>|\<bar\>>#FV<around|(|C,\<Gamma\>,\<tau\><rsub|2>|)>>>>>>|C,\<Gamma\>\<vdash\>p<with|math-font-series|bold|
        when >\<wedge\><rsub|i>m<rsub|i>\<leqslant\>n<rsub|i>.e:\<tau\><rsub|1>\<rightarrow\>\<tau\><rsub|2>>>>>>>>>>|<row|<cell|<tabular|<tformat|<table|<row|<cell|<verbatim|p-Cstr>>>|<row|<cell|<math|<frac|<tabular|<tformat|<table|<row|<cell|\<forall\>i>|<cell|C\<wedge\>D\<vdash\>p<rsub|i>:\<tau\><rsub|i>\<longrightarrow\>\<Delta\><rsub|i>>|<cell|K\<colons\>\<forall\><wide|\<alpha\>|\<bar\>><wide|\<beta\>|\<bar\>><around|[|D|]>.\<tau\><rsub|1>\<times\>\<ldots\>\<times\>\<tau\><rsub|n>\<rightarrow\>\<varepsilon\><around|(|<wide|\<alpha\>|\<bar\>>|)>>|<cell|<wide|\<beta\>|\<bar\>>#FV<around|(|C|)>>>>>>|C\<vdash\>K
        p<rsub|1>\<ldots\>p<rsub|n>:\<varepsilon\><around|(|<wide|\<alpha\>|\<bar\>>|)>\<longrightarrow\>\<exists\><wide|\<beta\>|\<bar\>><around|[|D|]><around|(|\<Delta\><rsub|1>\<times\>\<ldots\>\<times\>\<Delta\><rsub|n>|)>>>>>>>>>|<cell|<tabular|<tformat|<table|<row|<cell|<verbatim|NegClause>>>|<row|<cell|<math|<frac|<tabular|<tformat|<cwith|3|3|3|3|cell-valign|c>|<table|<row|<cell|C\<wedge\>D,\<Gamma\>\<Gamma\><rprime|'>\<vdash\>m<rsub|i>:Num<around*|(|\<tau\><rsub|m<rsub|i>>|)>>|<cell|e=<with|math-font-series|bold|assert
        false>\<vee\>\<ldots\>\<vee\>>|<cell|>>|<row|<cell|C\<wedge\>D,\<Gamma\>\<Gamma\><rprime|'>\<vdash\>n<rsub|i>:Num<around*|(|\<tau\><rsub|n<rsub|i>>|)>>|<cell|e=\<lambda\><around*|(|p<rprime|'>\<ldots\>\<lambda\><around*|(|p<rprime|''>.<with|math-font-series|bold|assert
        false>|)>|)>>|<cell|>>|<row|<cell|C\<vdash\>p:\<tau\><rsub|3>\<longrightarrow\>\<exists\><wide|\<beta\>|\<bar\>><around|[|D|]>\<Gamma\><rprime|'>>|<cell|C\<wedge\>D\<wedge\>\<tau\><rsub|1><wide|=|\<dot\>>\<tau\><rsub|3>\<wedge\><rsub|i>\<tau\><rsub|m<rsub|i>>\<leqslant\>\<tau\><rsub|n<rsub|i>>,\<Gamma\>\<Gamma\><rprime|'>\<vdash\>e:\<tau\><rsub|2>>|<cell|<wide|\<beta\>|\<bar\>>#FV<around|(|C,\<Gamma\>,\<tau\><rsub|2>|)>>>>>>|C,\<Gamma\>\<vdash\>p<with|math-font-series|bold|
        when >\<wedge\><rsub|i>m<rsub|i>\<leqslant\>n<rsub|i>.e:\<tau\><rsub|1>\<rightarrow\>\<tau\><rsub|2>>>>>>>>>>>>>

        <item><tabular|<tformat|<table|<row|<cell|Patterns
        (non-syntax-directed)>|<cell|Existential Type System extension --
        modified <verbatim|App>, added rules>>|<row|<cell|<tabular|<tformat|<cwith|2|2|1|1|cell-halign|l>|<cwith|2|2|3|3|cell-halign|l>|<table|<row|<cell|<verbatim|p-EqIn>>|<cell|>|<cell|<verbatim|p-SubOut>>|<cell|>|<cell|<verbatim|p-Hide>>>|<row|<cell|<math|<frac|<tabular|<tformat|<table|<row|<cell|C\<vdash\>p:\<tau\><rprime|'>\<longrightarrow\>\<Delta\>>>|<row|<cell|C\<vDash\>\<tau\><wide|=|\<dot\>>\<tau\><rprime|'>>>>>>|C\<vdash\>p:\<tau\>\<longrightarrow\>\<Delta\>>>>|<cell|
        \ \ >|<cell|<math|<frac|<tabular|<tformat|<table|<row|<cell|C\<vdash\>p:\<tau\>\<longrightarrow\>\<Delta\><rprime|'>>>|<row|<cell|C\<vDash\>\<Delta\><rprime|'>\<leqslant\>\<Delta\>>>>>>|C\<vdash\>p:\<tau\>\<longrightarrow\>\<Delta\>>>>|<cell|
        \ \ >|<cell|<math|<frac|<tabular|<tformat|<table|<row|<cell|C\<vdash\>p:\<tau\>\<longrightarrow\>\<Delta\>>>|<row|<cell|<wide|\<alpha\>|\<bar\>>#FV<around|(|\<tau\>,\<Delta\>|)>>>>>>|\<exists\><wide|\<alpha\>|\<bar\>>.C\<vdash\>p:\<tau\>\<longrightarrow\>\<Delta\>>>>>>>>>|<cell|<tabular|<tformat|<cwith|1|1|3|3|cell-col-span|2>|<cwith|2|2|3|3|cell-col-span|2>|<table|<row|<cell|<verbatim|App>>|<cell|>|<cell|<verbatim|ExLetIn>>|<cell|>|<cell|>|<cell|<verbatim|ExIntro>>>|<row|<cell|<math|<frac|<tabular|<tformat|<cwith|1|1|1|1|cell-col-span|2>|<table|<row|<cell|C,\<Gamma\>,\<Sigma\>\<vdash\>e<rsub|1>:\<tau\><rprime|'>\<rightarrow\>\<tau\>>|<cell|>>|<row|<cell|C,\<Gamma\>,\<Sigma\>\<vdash\>e<rsub|2>:\<tau\><rprime|'>>|<cell|C\<vDash\><neg|E><around*|(|\<tau\><rprime|'>|)>>>>>>|C,\<Gamma\>,\<Sigma\>\<vdash\>e<rsub|1>
        e<rsub|2>:\<tau\>>>>|<cell|>|<cell|<math|<frac|<tabular|<tformat|<cwith|2|2|1|1|cell-col-span|2>|<table|<row|<cell|\<varepsilon\><rsub|K><around*|(|<wide|\<alpha\>|\<bar\>>|)><with|mode|text|
        in >\<Sigma\>>|<cell|<with|mode|text|
        >C,\<Gamma\>,\<Sigma\>\<vdash\>e<rsub|1>:\<tau\><rprime|'>>>|<row|<cell|C,\<Gamma\>,\<Sigma\>\<vdash\>K
        p.e<rsub|2>:\<tau\><rprime|'>\<rightarrow\>\<tau\>>|<cell|>>>>>|C,\<Gamma\>,\<Sigma\>\<vdash\><rsup|><with|math-font-series|bold|let>
        p=e<rsub|1> <with|math-font-series|bold|in>
        e<rsub|2>:\<tau\>>>>|<cell|>|<cell|>|<cell|<math|<frac|<tabular|<tformat|<table|<row|<cell|Dom<around*|(|\<Sigma\><rprime|'>|)>\\Dom<around*|(|\<Sigma\>|)>=\<cal-E\><around*|(|e|)>>>|<row|<cell|C,\<Gamma\>,\<Sigma\><rprime|'>\<vdash\>n<around*|(|e|)>:\<tau\>>>>>>|C,\<Gamma\>,\<Sigma\>\<vdash\>e:\<tau\>>>>>>>>>>>>>

        \;

        <item><tabular|<tformat|<table|<row|<cell|Expressions
        (syntax-directed)>>|<row|<cell|<tabular|<tformat|<cwith|2|2|2|2|cell-halign|l>|<cwith|2|2|2|2|cell-valign|B>|<table|<row|<cell|<verbatim|Var>>|<cell|<verbatim|AssertFalse>>|<cell|<verbatim|Cstr>>|<cell|<verbatim|LetIn>>>|<row|<cell|<math|<frac|<tabular|<tformat|<table|<row|<cell|\<Gamma\><around|(|x|)>=\<forall\>\<beta\><around|[|\<exists\><wide|\<alpha\>|\<bar\>>.D|]>.\<beta\>>|<cell|C\<vDash\>D>>>>>|C,\<Gamma\>\<vdash\>x:\<beta\>>>>|<cell|<math|<frac|<tabular|<tformat|<cwith|1|1|1|1|cell-valign|c>|<table|<row|<cell|C\<vDash\>\<b-F\>>>>>>|C,\<Gamma\>\<vdash\><with|math-font-series|bold|assert
        false>:\<tau\><rsub|>>>>|<cell|<math|<frac|<tabular|<tformat|<table|<row|<cell|\<forall\>i
        C,\<Gamma\>\<vdash\>e<rsub|i>:\<tau\><rsub|i><with|mode|text|
        \ \ \ \ \ >C\<vDash\>D>>|<row|<cell|K\<colons\>\<forall\><wide|\<alpha\>|\<bar\>><wide|\<beta\>|\<bar\>><around|[|D|]>.\<tau\><rsub|1>\<ldots\>\<tau\><rsub|n>\<rightarrow\>\<varepsilon\><around|(|<wide|\<alpha\>|\<bar\>>|)>>>>>>|C,\<Gamma\>\<vdash\>K
        e<rsub|1>\<ldots\>e<rsub|n>:\<varepsilon\><around|(|<wide|\<alpha\>|\<bar\>>|)>>>>|<cell|<math|<frac|C,\<Gamma\>\<vdash\>\<lambda\><around*|(|p.e<rsub|2>|)>
        e<rsub|1>:\<tau\>|C,\<Gamma\>\<vdash\><with|math-font-series|bold|let>
        p=e<rsub|1> <with|math-font-series|bold|in>
        e<rsub|2>:\<tau\>>>>>>>>>>|<row|<cell|<tabular|<tformat|<cwith|2|2|4|4|cell-halign|r>|<cwith|2|2|7|7|cell-halign|c>|<table|<row|<cell|<verbatim|App>>|<cell|>|<cell|<verbatim|LetRec>>|<cell|>|<cell|>|<cell|>|<cell|<verbatim|Abs>>>|<row|<cell|<math|<frac|<tabular|<tformat|<table|<row|<cell|C,\<Gamma\>\<vdash\>e<rsub|1>:\<tau\><rprime|'>\<rightarrow\>\<tau\>>>|<row|<cell|C,\<Gamma\>\<vdash\>e<rsub|2>:\<tau\><rprime|'>>>>>>|C,\<Gamma\>\<vdash\>e<rsub|1>
        e<rsub|2>:\<tau\>>>>|<cell| \ \ >|<cell|<math|<frac|<tabular|<tformat|<table|<row|<cell|C,\<Gamma\><rprime|'>\<vdash\>e<rsub|1>:\<sigma\>>|<cell|C,\<Gamma\><rprime|'>\<vdash\>e<rsub|2>:\<tau\>>>|<row|<cell|\<sigma\>=\<forall\>\<beta\><around|[|\<exists\><wide|\<alpha\>|\<bar\>>.D|]>.\<beta\>>|<cell|\<Gamma\><rprime|'>=\<Gamma\><around|{|x\<mapsto\>\<sigma\>|}>>>>>>|C,\<Gamma\>\<vdash\><with|math-font-series|bold|letrec>
        x=e<rsub|1> <with|math-font-series|bold|in>
        e<rsub|2>:\<tau\>>>>|<cell|>|<cell|>|<cell|>|<cell|<math|<frac|\<forall\>i
        C,\<Gamma\>\<vdash\>c<rsub|i>:\<tau\><rsub|1>\<rightarrow\>\<tau\><rsub|2>|C,\<Gamma\>\<vdash\>\<lambda\><around|(|c<rsub|1>\<ldots\>c<rsub|n>|)>:\<tau\><rsub|1>\<rightarrow\>\<tau\><rsub|2>>>>>>>>>>>>>

        <item><tabular|<tformat|<table|<row|<cell|Expressions
        (non-syntax-directed)>|<cell|Existential Type System extension --
        <verbatim|ExIntro> processing>>|<row|<cell|<tabular|<tformat|<cwith|4|4|1|1|cell-halign|l>|<cwith|2|2|1|1|cell-halign|c>|<cwith|4|4|3|3|cell-halign|l>|<table|<row|<cell|<verbatim|Gen>>|<cell|>|<cell|<verbatim|Inst>>|<cell|>|<cell|<verbatim|DisjElim>>>|<row|<cell|<math|<frac|<tabular|<tformat|<table|<row|<cell|C\<wedge\>D,\<Gamma\>\<vdash\>e:\<beta\>>>|<row|<cell|\<beta\><wide|\<alpha\>|\<bar\>>#FV<around|(|\<Gamma\>,C|)>>>>>>|C\<wedge\>\<exists\>\<beta\><wide|\<alpha\>|\<bar\>>.D,\<Gamma\>\<vdash\>e:\<forall\>\<beta\><around|[|\<exists\><wide|\<alpha\>|\<bar\>>.D|]>.\<beta\>>>>|<cell|>|<cell|<math|<frac|<tabular|<tformat|<table|<row|<cell|C,\<Gamma\>\<vdash\>e:\<forall\><wide|\<alpha\>|\<bar\>><around|[|D|]>.\<tau\><rprime|'>>>|<row|<cell|C\<vDash\>D<around|[|<wide|\<alpha\>|\<bar\>>\<assign\><wide|\<tau\>|\<bar\>>|]>>>>>>|C,\<Gamma\>\<vdash\>e:\<tau\><rprime|'><around|[|<wide|\<alpha\>|\<bar\>>\<assign\><wide|\<tau\>|\<bar\>>|]>>>>|<cell|>|<cell|<math|<frac|<tabular|<tformat|<table|<row|<cell|C,\<Gamma\>\<vdash\>e:\<tau\>>|<cell|>|<cell|D,\<Gamma\>\<vdash\>e:\<tau\>>>>>>|C\<vee\>D,\<Gamma\>\<vdash\>e:\<tau\>>>>>|<row|<cell|<verbatim|Hide>>|<cell|>|<cell|<verbatim|Equ>>|<cell|>|<cell|<verbatim|FElim>>>|<row|<cell|<math|<frac|<tabular|<tformat|<table|<row|<cell|C,\<Gamma\>\<vdash\>e:\<tau\>>>|<row|<cell|<wide|\<alpha\>|\<bar\>>#FV<around|(|\<Gamma\>,\<tau\>|)>>>>>>|\<exists\><wide|\<alpha\>|\<bar\>>.C,\<Gamma\>\<vdash\>e:\<tau\>>>>|<cell|
        \ \ >|<cell|<math|<frac|<tabular|<tformat|<table|<row|<cell|C,\<Gamma\>\<vdash\>e:\<tau\>>>|<row|<cell|C\<vDash\>\<tau\><wide|=|\<dot\>>\<tau\><rprime|'>>>>>>|C,\<Gamma\>\<vdash\>e:\<tau\><rprime|'>>>>|<cell|>|<cell|<math|<frac||\<b-F\>,\<Gamma\>\<vdash\>e:\<tau\>>>>>>>>>|<cell|<tabular|<tformat|<cwith|8|8|1|1|cell-col-span|2>|<table|<row|<cell|<math|n<around*|(|e,K<rprime|'>|)>=<with|math-font-series|bold|let>
        x=n<around*|(|e,\<bot\>|)> <with|math-font-series|bold|in
        >K<rprime|'> x>>|<cell|<math|<with|mode|text|for
        >K<rprime|'>\<neq\>\<bot\>\<wedge\>l<around*|(|e|)>=\<b-F\>>>>|<row|<cell|<math|n<around*|(|x,\<bot\>|)>=x>>|<cell|>>|<row|<cell|<math|n<around*|(|\<lambda\><wide|c|\<bar\>>,\<bot\>|)>=\<lambda\><around*|(|<wide|n<around*|(|c,\<bot\>|)>|\<bar\>>|)>>>|<cell|>>|<row|<cell|<math|n<around*|(|e<rsub|1>
        e<rsub|2>,K<rprime|'>|)>=n<around*|(|e<rsub|1>,K<rprime|'>|)>
        n<around*|(|e<rsub|2>,\<bot\>|)>>>|<cell|>>|<row|<cell|<math|n<around*|(|\<lambda\><around*|[|K|]><wide|c|\<bar\>>,\<bot\>|)>=\<lambda\><around*|(|<wide|n<around*|(|c,K|)>|\<bar\>>|)>>>|<cell|>>|<row|<cell|<math|n<around*|(|\<lambda\><around*|[|K|]><wide|c|\<bar\>>,K<rprime|'>|)>=\<lambda\><around*|(|<wide|n<around*|(|c,K<rprime|'>|)>|\<bar\>>|)>>>|<cell|<math|<with|mode|text|for
        >K<rprime|'>\<neq\>\<bot\>>>>|<row|<cell|<math|n<around*|(|p.e,K<rprime|'>|)>=p.n<around*|(|e,K<rprime|'>|)>>>|<cell|>>|<row|<cell|<math|n<around*|(|<with|math-font-series|bold|let>
        p=e<rsub|1> <with|math-font-series|bold|in>
        e<rsub|2>,K<rprime|'>|)>=<with|math-font-series|bold|let>
        p=n<around*|(|e<rsub|1>,\<bot\>|)> <with|math-font-series|bold|in>
        n<around*|(|e<rsub|2>,K<rprime|'>|)>>>|<cell|>>>>>>>>>>
      </itemize>
    </really-tiny>
  </hidden>|<\hidden>
    <tit|AVL Trees -- <verbatim|create>>

    <em|slide9.gadt>:

    <\code>
      datatype Avl : type * num

      datacons Empty : <math|\<forall\>>a. Avl (a, 0)

      datacons Node :

      \ \ <math|\<forall\>>a,k,m,n [k=max(m,n) <math|\<wedge\>>
      0<math|\<leqslant\>>m <math|\<wedge\>> 0<math|\<leqslant\>>n
      <math|\<wedge\>> n<math|\<leqslant\>>m+2 <math|\<wedge\>>
      m<math|\<leqslant\>>n+2].

      \ \ \ \ \ Avl (a, m) * a * Avl (a, n) * Num (k+1)
      <math|\<longrightarrow\>> Avl (a, k+1)

      \;

      let height = function

      \ \ \| Empty -\> 0

      \ \ \| Node (_, _, _, k) -\> k

      \;

      let create = fun l x r -\>

      \ \ ematch height l, height r with

      \ \ \| i, j when j \<less\>= i -\> Node (l, x, r, i+1)

      \ \ \| i, j when i \<less\>= j -\> Node (l, x, r, j+1)
    </code>

    Result:

    <\code>
      val height : <math|\<forall\>>n, a. Avl (a, n) <math|\<rightarrow\>>
      Num n

      val create :

      \ \ <math|\<forall\>>k, n, a[k <math|\<leqslant\>> n + 2
      <math|\<wedge\>> n <math|\<leqslant\>> k + 2 <math|\<wedge\>> 0
      <math|\<leqslant\>> k <math|\<wedge\>> 0 <math|\<leqslant\>> n].

      \ \ Avl (a, k) <math|\<rightarrow\>> a <math|\<rightarrow\>> Avl (a, n)
      <math|\<rightarrow\>> <math|\<exists\>>i[i=max (k + 1, n + 1)].Avl (a,
      i)
    </code>
  </hidden>|<\hidden>
    <tit|AVL Trees -- <verbatim|min_binding>>

    <em|slide11.gadt>:

    <\code>
      datatype Avl : type * num

      datacons Empty : <math|\<forall\>>a. Avl (a, 0)

      datacons Node :

      \ \ <math|\<forall\>>a,k,m,n [k=max(m,n) <math|\<wedge\>>
      0<math|\<leqslant\>>m <math|\<wedge\>> 0<math|\<leqslant\>>n
      <math|\<wedge\>> n<math|\<leqslant\>>m+2 <math|\<wedge\>>
      m<math|\<leqslant\>>n+2].

      \ \ \ \ \ Avl (a, m) * a * Avl (a, n) * Num (k+1)
      <math|\<longrightarrow\>> Avl (a, k+1)

      \;

      let rec min_binding = function

      \ \ \| Empty -\> assert false

      \ \ \| Node (Empty, x, r, _) -\> x

      \ \ \| Node ((Node (_,_,_,_) as l), x, r, _) -\> min_binding l
    </code>

    <em|shell>:

    <\code>
      # invargent slide11.gadt -inform

      val min_binding : <math|\<forall\>>n, a[1 <math|\<leqslant\>> n]. Avl
      (a, n) <math|\<rightarrow\>> a
    </code>
  </hidden>|<\hidden>
    <tit|Issues -- Multiple Maximally General Types>

    <em|equal1_wrong.gadt>: compare two values of types as encoded

    <\small>
      <\code>
        datatype Ty : type

        datatype List : type

        datacons Zero : Int

        datacons Nil : <math|\<forall\>>a. List a

        datacons TInt : Ty Int

        datacons TPair : <math|\<forall\>>a, b. Ty a * Ty b
        <math|\<longrightarrow\>> Ty (a, b)

        datacons TList : <math|\<forall\>>a. Ty a <math|\<longrightarrow\>>
        Ty (List a)

        external let eq_int : Int <math|\<rightarrow\>> Int
        <math|\<rightarrow\>> Bool = "(=)"

        external let b_and : Bool <math|\<rightarrow\>> Bool
        <math|\<rightarrow\>> Bool = "(&&)"

        external let b_not : Bool <math|\<rightarrow\>> Bool = "not"

        external forall2 : <math|\<forall\>>a, b. (a <math|\<rightarrow\>> b
        <math|\<rightarrow\>> Bool) <math|\<rightarrow\>> List a
        <math|\<rightarrow\>> List b <math|\<rightarrow\>> Bool = "forall2"

        \;

        let rec equal1 = function

        \ \ \| TInt, TInt -\> fun x y -\> eq_int x y

        \ \ \| TPair (t1, t2), TPair (u1, u2) -\> \ 

        \ \ \ \ (fun (x1, x2) (y1, y2) -\>

        \ \ \ \ \ \ \ \ b_and (equal1 (t1, u1) x1 y1)

        \ \ \ \ \ \ \ \ \ \ \ \ \ \ (equal1 (t2, u2) x2 y2))

        \ \ \| TList t, TList u -\> forall2 (equal1 (t, u))

        \ \ \| _ -\> fun _ _ -\> False
      </code>
    </small>

    Result: <verbatim|val equal1 : <math|\<forall\>>a, b. (Ty a, Ty b)
    <math|\<rightarrow\>> a <math|\<rightarrow\>> a <math|\<rightarrow\>>
    Bool>

    <\exercise>
      Find remaining three maximally general types of <verbatim|equal1>.
    </exercise>
  </hidden>|<\hidden>
    <tit|Pick Intended Type with <verbatim|assert false>>

    <em|equal_assert.gadt>:

    <\code>
      <math|<around*|[|\<ldots\>|]>>

      \;

      let rec equal = function

      \ \ \| TInt, TInt -\> fun x y -\> eq_int x y

      \ \ \| TPair (t1, t2), TPair (u1, u2) -\> \ 

      \ \ \ \ (fun (x1, x2) (y1, y2) -\>

      \ \ \ \ \ \ \ \ b_and (equal (t1, u1) x1 y1)

      \ \ \ \ \ \ \ \ \ \ \ \ \ \ (equal (t2, u2) x2 y2))

      \ \ \| TList t, TList u -\> forall2 (equal (t, u))

      \ \ \| _ -\> fun _ _ -\> False

      \ \ \| TInt, TList l -\> (function Nil -\> assert false)

      \ \ \| TList l, TInt -\> (fun _ -\> function Nil -\> assert false)
    </code>

    Result:

    <\code>
      val equal : <math|\<forall\>>a, b. (Ty a, Ty b) <math|\<rightarrow\>> a
      <math|\<rightarrow\>> b <math|\<rightarrow\>> Bool
    </code>
  </hidden>|<\hidden>
    <tit|Pick Intended Type with a <verbatim|test> Clause>

    <em|equal_test.gadt>:

    <\code>
      <math|<around*|[|\<ldots\>|]>>

      let rec equal = function

      \ \ \| TInt, TInt -\> fun x y -\> eq_int x y

      \ \ \| TPair (t1, t2), TPair (u1, u2) -\> \ 

      \ \ \ \ (fun (x1, x2) (y1, y2) -\>

      \ \ \ \ \ \ \ \ b_and (equal (t1, u1) x1 y1)

      \ \ \ \ \ \ \ \ \ \ \ \ \ \ (equal (t2, u2) x2 y2))

      \ \ \| TList t, TList u -\> forall2 (equal (t, u))

      \ \ \| _ -\> fun _ _ -\> False

      test b_not (equal (TInt, TList TInt) zero Nil)
    </code>

    OCaml code generated -- <em|equal_test.ml>:

    <\code>
      <math|<around*|[|\<ldots\>|]>>

      let rec equal : type a b . ((a ty * b ty) -\> a -\> b -\> bool) =

      \ \ (function (TInt, TInt) -\> (fun x y -\> eq_int x y)

      \ \ \ \ \| (TPair (t1, t2), TPair (u1, u2)) -\>

      \ \ \ \ \ \ \ \ (fun ((x1, x2)) ((y1, y2)) -\>

      \ \ \ \ \ \ \ \ \ \ b_and (equal ((t1, u1)) x1 y1) (equal ((t2, u2)) x2
      y2))

      \ \ \ \ \| (TList t, TList u) -\> forall2 (equal ((t, u)))

      \ \ \ \ \| _ -\> (fun _ _ -\> false))

      let () = assert (b_not (equal ((TInt, TList TInt)) zero Nil)); ()
    </code>
  </hidden>|<\shown>
    <tit|InvarGenT Handles Many Non-pointwise Cases>

    Chuan-kai Lin developed an efficient type inference algorithm for GADTs,
    however in a type system restricted to so-called pointwise types.

    Toy example -- <em|non_pointwise_split.gadt>:

    <\code>
      datatype Split : type * type

      datacons Whole : Split (Int, Int)

      datacons Parts : <math|\<forall\>>a, b. Split ((Int, a), (b, Bool))

      external let seven : Int = "7"

      external let three : Int = "3"

      \;

      let joint = function

      \ \ \| Whole -\> seven

      \ \ \| Parts -\> three, True
    </code>

    Needs non-default setting -- <em|shell>:

    <\code>
      # invargent non_pointwise_split.gadt -inform -richer_answers

      val joint : <math|\<forall\>>a. Split (a, a) <math|\<rightarrow\>> a
    </code>

    <\exercise>
      Check that this is the correct type.
    </exercise>
  </shown>|<\hidden>
    <tit|InvarGenT does not Handle Some Non-sensible Cases>

    A solution to at least one branch of implications, correspondingly of
    pattern matching, must be implied by the conjunction of the premise and
    the conclusion of the branch. I.e., some branch must be solvable without
    arbitrary guessing. If solving a branch requires guessing, for some
    ordering of branches, the solution to already solved branches must be a
    good guess.

    <em|non_pointwise_vary.gadt>:

    <\code>
      datatype EquLR : type * type * type

      datacons EquL : <math|\<forall\>>a, b. EquLR (a, a, b)

      datacons EquR : <math|\<forall\>>a, b. EquLR (a, b, b)

      datatype Box : type

      datacons Cons : <math|\<forall\>>a. a <math|\<longrightarrow\>> Box a

      external let eq : <math|\<forall\>>a. a <math|\<rightarrow\>> a
      <math|\<rightarrow\>> Bool = "(=)"

      let vary = fun e y -\>

      \ \ match e with

      \ \ \| EquL, EquL -\> eq y "c"

      \ \ \| EquR, EquR -\> Cons (match y with True -\> 5 \| False -\> 7)
    </code>

    <em|shell>:

    <\code>
      # invargent non_pointwise_vary.gadt -inform

      File "non_pointwise_vary.gadt", line 11, characters 18-60:

      No answer in type: term abduction failed
    </code>

    <\exercise>
      Find a type or two for <verbatim|vary>. Check that the type does not
      meet the above requirement.
    </exercise>
  </hidden>|<\hidden>
    <tit|AVL trees -- <verbatim|add>>

    <em|avl_tree.gadt>:

    <\code>
      <math|<around*|[|\<ldots\>|]>>

      let rec add = fun x -\<gtr\> efunction

      \ \ \| Empty -\<gtr\> Node (Empty, x, Empty, 1)

      \ \ \| Node (l, y, r, h) -\<gtr\>

      \ \ \ \ ematch compare x y, height l, height r with

      \ \ \ \ \| EQ, _, _ -\<gtr\> Node (l, x, r, h)

      \ \ \ \ \| LT, hl, hr -\<gtr\>

      \ \ \ \ \ \ let l' = add x l in

      \ \ \ \ \ \ (ematch height l' with

      \ \ \ \ \ \ \ \| hl' when hl' \<less\>= hr+2 -\<gtr\> create l' y r

      \ \ \ \ \ \ \ \| hl' when hr+3 \<less\>= hl' -\<gtr\> rotr (l', y, r))

      \ \ \ \ \| GT, hl, hr -\<gtr\>

      \ \ \ \ \ \ let r' = add x r in

      \ \ \ \ \ \ (ematch height r' with

      \ \ \ \ \ \ \ \| hr' when hr' \<less\>= hl+2 -\<gtr\> create l y r'

      \ \ \ \ \ \ \ \| hr' when hl+3 \<less\>= hr' -\<gtr\> rotl (l, y, r'))
    </code>

    Result:

    <\code>
      val add : <math|\<forall\>>a,n.a<math|\<rightarrow\>>Avl(a,
      n)<math|\<rightarrow\>><math|\<exists\>>k[k <math|\<leq\>> n+1
      <math|\<wedge\>> 1 <math|\<leq\>> k <math|\<wedge\>> n <math|\<leq\>>
      k].Avl(a, k)
    </code>
  </hidden>|<\hidden>
    <tit|Issues -- AVL Trees -- <verbatim|rotr>>

    <em|avl_tree.gadt>:

    <\code>
      <math|<around*|[|\<ldots\>|]>>

      let rotr = efunction

      \ \ \ \ \| Empty, x, r -\<gtr\> assert false

      \ \ \ \ \| Node (ll, lx, lr, hl), x, r -\<gtr\>

      \ \ \ \ \ \ assert num 0 \<less\>= height r; \ <strong|(* Need
      assertions to guide inference *)>

      \ \ \ \ \ \ assert type hl = height r + 3;

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

    Result:

    <\code>
      val rotr : <math|\<forall\>>a,n[0<math|\<leq\>>n].(Avl(a,n+3),a,Avl(a,n))<math|\<rightarrow\>><math|\<exists\>>k[n+3<math|\<leq\>>k<math|\<wedge\>>k<math|\<leq\>>n+4].Avl(a,k)
    </code>
  </hidden>|<\hidden>
    <tit|Correctness and Completeness of Constraint Generation>

    <\large>
      <\theorem>
        <label|InfCorrExpr><em|Correctness> (expressions).
        <math|<around*|\<llbracket\>|\<Gamma\>\<vdash\>ce:\<tau\>|\<rrbracket\>>,\<Gamma\>\<vdash\>ce:\<tau\>>.
      </theorem>

      <\theorem>
        <label|InfComplExpr><em|Completeness> (expressions). If
        <math|PV<around*|(|C,\<Gamma\>|)>=\<varnothing\>> and
        <math|C,<no-break>\<Gamma\>\<vdash\>ce:<no-break>\<tau\>>, then there
        exists an interpretation of predicate variables <math|\<cal-I\>> such
        that <math|\<cal-I\>,<no-break>\<cal-M\>\<vDash\>C\<Rightarrow\><no-break><around*|\<llbracket\>|\<Gamma\>\<vdash\>ce:<no-break>\<tau\>|\<rrbracket\>>>.
      </theorem>
    </large>
  </hidden>|<\hidden>
    <tit|Remarks on Solving>

    <\itemize>
      <item>We use an extension of <em|fully maximal Simple Constraint
      Abduction> -- ``fully maximal'' is the restriction that we do not guess
      facts not implied by premise and conclusion of a given implication.

      <item>Without existential types, the problem in principle is caused by
      the complexity of constraint abduction -- not known to be decidable.
      Given a correct program with appropriate <verbatim|assert false>
      clauses, and using an oracle for Simple Constraint Abduction, the
      intended type scheme will ultimately be found.

      <\itemize>
        <item>This could be shown formally, but the proof is very tedious.
      </itemize>

      <item>Without existential types, the problem in practice is that
      although the <em|fully maximal> restriction, when not imposed on all
      branches but with accumulating the solution as discussed on slide 22,
      seems sufficient for practical programs, fully maximal SCA is still
      exponential in the size of input.

      <item>With existential types, there are no guarantees. The intended
      solution to the postconditions could be missed by the algorithm.

      <\itemize>
        <item>We have not yet found a definite, and practical, such
        counterexample.
      </itemize>
    </itemize>
  </hidden>|<\hidden>
    <tit|Joint Constraint Abduction>

    <\large>
      <math|\<exists\><wide|\<alpha\>|\<bar\>>.A> is a
      JCAQP<rsub|<math|\<cal-M\>>> answer (answer to a <em|Joint Constraint
      Abduction under Quantifier Prefix problem>
      <with|mode|math|\<cal-Q\>.\<wedge\><rsub|i><around*|(|D<rsub|i>\<Rightarrow\>C<rsub|i>|)>>
      for model <math|\<cal-M\>>) when:

      <\itemize>
        <item><math|A> is a conj. of atoms in ``solved form'',

        <item><math|<wide|\<alpha\>|\<bar\>>#FV<around*|(|\<wedge\><rsub|i><around*|(|D<rsub|i>\<Rightarrow\>C<rsub|i>|)>|)>>,

        <item><em|relevance>: <math|\<cal-M\>\<vDash\>\<wedge\><rsub|i><around|(|D<rsub|i>\<wedge\>A\<Rightarrow\>C<rsub|i>|)>>,

        <item><em|validity>: <math|\<cal-M\>\<vDash\>\<forall\><wide|\<alpha\>|\<bar\>>\<cal-Q\>.A>,

        <item><em|consistency>: <math|\<cal-M\>\<vDash\>\<wedge\><rsub|i>\<forall\><wide|\<alpha\>|\<bar\>>\<exists\><around|(|<wide|\<alpha\>|\<bar\>><rsup|c>|)>.D<rsub|i>\<wedge\>A>.
      </itemize>
    </large>

    <\ornamented>
      <very-large|Open problem: decidable?>
    </ornamented>
  </hidden>|<\hidden>
    <tit|Fully Maximal SCA Answers>

    <\large>
      Answer <math|\<exists\><wide|\<alpha\>|\<bar\>>.A> to
      SCAQP<rsub|<math|\<cal-M\>>> problem <math|\<cal-Q\>.D\<Rightarrow\>C>
      is <em|fully maximal> when

      <\equation*>
        \<cal-M\>\<vDash\><around|(|\<exists\><wide|\<alpha\>|\<bar\>>.D\<wedge\>A|)>\<Leftrightarrow\>D\<wedge\>C.
      </equation*>
    </large>

    Nondeterministic algorithm for <math|T<around|(|F|)>>:

    <\verbatim>
      FMA(<math|D>,<math|C>):

      \ \ \ \ if <math|<around|(|D\<Rightarrow\>C|)>> return <math|\<top\>>

      \ \ \ \ let <math|A> be standard form of <math|D\<wedge\>C>

      \ \ \ \ loop

      \ \ \ \ \ \ \ \ let <math|\<cal-A\>> be <math|next<around|(|A|)>>

      \ \ \ \ \ \ \ \ if <math|<around|(|\<forall\>A<rprime|'>\<in\>\<cal-A\>.A<rprime|'>\<wedge\>D\<nRightarrow\>C|)>>
      return <math|A>

      \ \ \ \ \ \ \ \ choose <math|A\<in\>\<cal-A\>> s.t.
      <math|A\<wedge\>D\<Rightarrow\>C>
    </verbatim>

    <math|next<around|(|A|)>=<around*|{|repl<around|(|S,A|)>\|S<with|mode|text|:
    some positions of a term> t|}>>

    <math|repl<around|(|S,A|)>> replaces terms at positions <math|S> by a new
    parameter.
  </hidden>|<\hidden>
    <tit|Joint Constraint Abduction Algorithm>

    <\itemize>
      <item>When solving multiple implications
      <math|\<wedge\><rsub|i><around*|(|D<rsub|i>\<Rightarrow\>C<rsub|i>|)>>,
      keep a partial answer <math|\<exists\><wide|\<alpha\>|\<bar\>><rsub|p>.A<rsub|p>>.

      <item>To solve a particular implication
      <math|D<rsub|i>\<Rightarrow\>C<rsub|i>>, find
      <math|\<exists\><wide|\<alpha\>|\<bar\>>.A> s.t.
      <math|\<exists\><wide|\<alpha\>|\<bar\>><wide|\<alpha\>|\<bar\>><rsub|p>.A\<wedge\>A<rsub|p>>
      is the SCAQP<math|<rsub|\<cal-M\>>> answer:
      <math|\<cal-M\>\<vDash\><around|(|\<exists\><wide|\<alpha\>|\<bar\>><wide|\<alpha\>|\<bar\>><rsub|p>.D\<wedge\>A\<wedge\>A<rsub|p>|)>\<Leftrightarrow\>D\<wedge\>C>
      etc.

      <\itemize>
        <item>In the algorithm for <math|T<around*|(|F|)>> on previous slide,
        the initial <math|A> is still <math|D<rsub|i>\<wedge\>C<rsub|i>>, but
        the implication checks are modified: we check
        <math|A<rprime|'>\<wedge\>A<rsub|p>\<wedge\>D<rsub|>\<nRightarrow\>C>,
        <math|A\<wedge\>A<rsub|p>\<wedge\>D<rsub|i>\<Rightarrow\>C<rsub|i>>.
      </itemize>

      <item>In case of success, <math|\<exists\><wide|\<alpha\>|\<bar\>><rsub|p+1>.A<rsub|p+1>=\<exists\><wide|\<alpha\>|\<bar\>><wide|\<alpha\>|\<bar\>><rsub|p>.A\<wedge\>A<rsub|p>>.

      <item>A general way to deal with failure would be: try all permutations
      <math|i<rsub|1>,\<ldots\>,i<rsub|p>,\<ldots\>>

      <item>In practice we need to give up sooner.

      <\itemize>
        <item>If branch <math|D<rsub|i>\<Rightarrow\>C<rsub|i>> fails when
        approached with partial answer <math|\<exists\><wide|\<alpha\>|\<bar\>><rsub|p>.A<rsub|p>>,
        <math|A<rsub|p>\<neq\>\<top\>>, restart from
        <math|D<rsub|i>\<Rightarrow\>C<rsub|i>> with
        <math|A<rsub|p+1>=\<top\>>.

        <item>If branch <math|D<rsub|i>\<Rightarrow\>C<rsub|i>> fails for
        <math|A<rsub|p>=\<top\>>, restart from the next unsolved branch (e.g.
        <math|D<rsub|i+1>\<Rightarrow\>C<rsub|i+1>>) with
        <math|A<rsub|p+1>=\<top\>> and put
        <math|D<rsub|i>\<Rightarrow\>C<rsub|i>> aside.

        <item>Solve branches set aside after other branches.

        <item><strong|Fail> if solving an aside branch fails.
      </itemize>

      <item>Backtracking: a discard list, aka. taboo list, of visited
      answers.
    </itemize>
  </hidden>|<\hidden>
    <tit|Abduction Under Quantifier Prefix>

    <\large>
      To simplify the search in presence of a quantifier, we preprocess the
      initial candidate by eliminating universally quantified variables:

      <\eqnarray*>
        <tformat|<table|<row|<cell|Rev<rsub|\<forall\>><around*|(|\<cal-Q\>,<wide|\<beta\>|\<bar\>>,D,C|)>>|<cell|=>|<cell|<around*|{|S<around*|(|c|)><mid|\|>c\<in\>D\<wedge\>C,S=<around*|[|<wide|\<beta\><rsub|u>|\<bar\>>\<assign\><wide|t<rsub|u>|\<bar\>>|]><with|mode|text|
        for ><wide|\<forall\>\<beta\><rsub|u>|\<bar\>>\<subset\>\<cal-Q\>,<next-line><with|mode|text|
        \ \ \ \ \ \ \ >\<cal-M\>\<vDash\>D\<Rightarrow\><wide|\<beta\><rsub|u>|\<bar\>><wide|=|\<dot\>><wide|t<rsub|u>|\<bar\>>,\<cal-M\>\<vDash\>\<cal-Q\>.S<around*|(|c|)><around*|[|<wide|\<beta\>|\<bar\>>\<assign\><wide|t|\<bar\>>|]><with|mode|text|
        for some ><wide|t|\<bar\>>|}>>>>>
      </eqnarray*>
    </large>

    <\itemize>
      <item>We cannot use Herbrandization because it does not preserve
      equivalence.

      <\itemize>
        <item>Herbrandization works for general abduction defined by logical
        validity, but not for constraint abduction defined by validity in a
        fixed model.\ 
      </itemize>
    </itemize>
  </hidden>|<\hidden>
    <tit|References>

    <\itemize>
      <item>Vincent<nbsp>Simonet<localize| and
      >Francois<nbsp>Pottier.<newblock> A constraint-based approach to
      guarded algebraic data types.<newblock> <with|font-shape|italic|ACM
      Transactions on Programming Languages and Systems>, 29(1), JAN
      2007.<newblock>

      <item>Michael<nbsp>Maher<localize| and >Ge<nbsp>Huang.<newblock> On
      computing constraint abduction answers.<newblock> <localize|In
      >Iliano<nbsp>Cervesato, Helmut<nbsp>Veith<localize| and
      >Andrei<nbsp>Voronkov<localize|, editors>,
      <with|font-shape|italic|Logic for Programming, Artificial Intelligence,
      and Reasoning>, <localize|volume> 5330<localize| of
      ><with|font-shape|italic|Lecture Notes in Computer Science>,
      <localize|pages >421--435. Springer Berlin / Heidelberg,
      2008.<newblock>

      <item>M.<nbsp>Sulzmann, T.<nbsp>Schrijvers<localize| and >P.
      J.<nbsp>Stuckey.<newblock> Type inference for GADTs via Herbrand
      constraint abduction.

      <item>Kenneth W.<nbsp>Knowles<localize| and
      >Cormac<nbsp>Flanagan.<newblock> Type reconstruction for general
      refinement types.<newblock> <localize|In
      ><with|font-shape|italic|ESOP>, <localize|volume> 4421<localize| of
      ><with|font-shape|italic|Lecture Notes in Computer Science>,
      <localize|pages >505--519. Springer, 2007.<newblock>

      <item>Peter<nbsp>Bulychev, Egor<nbsp>Kostylev<localize| and
      >Vladimir<nbsp>Zakharov.<newblock> Anti-unification algorithms and
      their applications in program analysis.<newblock> <localize|In
      >Amir<nbsp>Pnueli, Irina<nbsp>Virbitskaite<localize| and
      >Andrei<nbsp>Voronkov<localize|, editors>,
      <with|font-shape|italic|Perspectives of Systems Informatics>,
      <localize|volume> 5947<localize| of ><with|font-shape|italic|Lecture
      Notes in Computer Science>, <localize|pages >413--423. Springer Berlin
      / Heidelberg, 2010.

      <item>Komei<nbsp>Fukuda, Thomas M.<nbsp>Liebling<localize| and
      >Christine<nbsp>Lütolf.<newblock> Extended convex hull.<newblock>
      <localize|In ><with|font-shape|italic|Proceedings of the 12th Canadian
      Conference on Computational Geometry, Fredericton, New Brunswick,
      Canada, August 16-19, 2000>.
    </itemize>
  </hidden>>
</body>

<initial|<\collection>
</collection>>

<\references>
  <\collection>
    <associate|InfComplExpr|<tuple|2|12>>
    <associate|InfCorrExpr|<tuple|1|12>>
  </collection>
</references>