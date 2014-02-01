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
      Quantifier Prefix>, postconditions found by <em|disjunction
      elimination> -- e.g. anti-unification for terms, extended convex hull.

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
    <tit|The Type System -- <verbatim|Var>>

    <\equation*>
      <frac|<tabular|<tformat|<table|<row|<cell|\<Gamma\><around|(|x|)>=\<forall\>\<beta\><around|[|\<exists\><wide|\<alpha\>|\<bar\>>.D|]>.\<beta\>>|<cell|C\<vDash\>D>>>>>|C,\<Gamma\>\<vdash\>x:\<beta\>>
    </equation*>

    <\equation*>
      <around*|\<llbracket\>|\<Gamma\>\<vdash\>x:\<tau\>|\<rrbracket\>>=\<exists\>\<beta\><rprime|'><wide|\<alpha\>|\<bar\>><rprime|'>.D<around|[|\<beta\><wide|\<alpha\>|\<bar\>>\<assign\>\<beta\><rprime|'><wide|\<alpha\>|\<bar\>><rprime|'>|]>\<wedge\>\<beta\><rprime|'><wide|=|\<dot\>>\<tau\>
    </equation*>

    <\equation*>
      <text|where >\<Gamma\><around|(|x|)>=\<forall\>\<beta\><around|[|\<exists\><wide|\<alpha\>|\<bar\>>.D|]>.\<beta\>,\<beta\><rprime|'><wide|\<alpha\>|\<bar\>><rprime|'>#FV<around|(|\<Gamma\>,\<tau\>|)>
    </equation*>

    <em|slide3.gadt>:

    <\code>
      newtype Tau

      external x : <math|\<forall\>>b[b = Tau <math|\<rightarrow\>> Tau].b =
      "x"

      \;

      let var_rule = x
    </code>

    <em|shell>:

    <\code>
      # invargent slide3.gadt -inform

      val var_rule : Tau <math|\<rightarrow\>> Tau
    </code>
  </hidden>|<\hidden>
    <tit|The Type System -- <verbatim|App>>

    <\equation*>
      <frac|<tabular|<tformat|<table|<row|<cell|C,\<Gamma\>\<vdash\>e<rsub|1>:\<tau\><rprime|'>\<rightarrow\>\<tau\>>>|<row|<cell|C,\<Gamma\>\<vdash\>e<rsub|2>:\<tau\><rprime|'>>>>>>|C,\<Gamma\>\<vdash\>e<rsub|1>
      e<rsub|2>:\<tau\>>
    </equation*>

    <\equation*>
      <around*|\<llbracket\>|\<Gamma\>\<vdash\>e<rsub|1>
      e<rsub|2>:\<tau\>|\<rrbracket\>>=\<exists\>\<alpha\>.<around*|\<llbracket\>|\<Gamma\>\<vdash\>e<rsub|1>:\<alpha\>\<rightarrow\>\<tau\>|\<rrbracket\>>\<wedge\><around*|\<llbracket\>|\<Gamma\>\<vdash\>e<rsub|2>:\<alpha\>|\<rrbracket\>>,\<alpha\>#FV<around|(|\<Gamma\>,\<tau\>|)>
    </equation*>

    <em|slide4.gadt>:

    <\code>
      newtype Tau

      newtype Tau'

      newcons E2 : Tau'

      external e1 : Tau' <math|\<rightarrow\>> Tau = "e1"

      \;

      let app_rule = e1 E2
    </code>

    <em|shell>:

    <\code>
      # invargent slide4.gadt -inform

      val app_rule : Tau
    </code>
  </hidden>|<\hidden>
    <tit|The Type System -- <verbatim|Abs>>

    <\equation*>
      <frac|\<forall\>i C,\<Gamma\>\<vdash\>c<rsub|i>:\<tau\><rsub|1>\<rightarrow\>\<tau\><rsub|2>|C,\<Gamma\>\<vdash\>\<lambda\><around|(|c<rsub|1>\<ldots\>c<rsub|n>|)>:\<tau\><rsub|1>\<rightarrow\>\<tau\><rsub|2>><with|mode|text|,
      where >c<rsub|i>=p<rsub|i>.e<rsub|i>
    </equation*>

    <\equation*>
      <around*|\<llbracket\>|\<Gamma\>\<vdash\>\<lambda\><wide|c|\<bar\>>:\<tau\>|\<rrbracket\>>=\<exists\>\<alpha\><rsub|1>\<alpha\><rsub|2>.<around*|\<llbracket\>|\<Gamma\>\<vdash\><wide|c|\<bar\>>:\<alpha\><rsub|1>\<rightarrow\>\<alpha\><rsub|2>|\<rrbracket\>>\<wedge\>\<alpha\><rsub|1>\<rightarrow\>\<alpha\><rsub|2><wide|=|\<dot\>>\<tau\>,\<alpha\><rsub|1>\<alpha\><rsub|2>#FV<around|(|\<Gamma\>,\<tau\>|)>
    </equation*>

    <\equation*>
      <frac|<tabular|<tformat|<cwith|1|1|3|3|cell-valign|c>|<table|<row|<cell|C\<vdash\>p:\<tau\><rsub|1>\<longrightarrow\>\<exists\><wide|\<beta\>|\<bar\>><around|[|D|]>\<Gamma\><rprime|'>>|<cell|C\<wedge\>D,\<Gamma\>\<Gamma\><rprime|'>\<vdash\>e:\<tau\><rsub|2>>|<cell|<wide|\<beta\>|\<bar\>>#FV<around|(|C,\<Gamma\>,\<tau\><rsub|2>|)>>>>>>|C,\<Gamma\>\<vdash\>p.e:\<tau\><rsub|1>\<rightarrow\>\<tau\><rsub|2>>
    </equation*>

    \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ <draw-over|<tabular|<tformat|<cwith|3|3|1|1|cell-halign|c>|<cwith|1|1|1|1|cell-halign|c>|<table|<row|<cell|<math|<around*|\<llbracket\>|\<Gamma\>\<vdash\>p.e:\<tau\><rsub|1>\<rightarrow\>\<tau\><rsub|2>|\<rrbracket\>>=<around*|\<llbracket\>|\<vdash\>p\<downarrow\>\<tau\><rsub|1>|\<rrbracket\>>\<wedge\>\<forall\><wide|\<beta\>|\<bar\>>.D\<Rightarrow\><around*|\<llbracket\>|\<Gamma\>\<Gamma\><rprime|'>\<vdash\>e:\<tau\><rsub|2>|\<rrbracket\>>>>>|<row|<cell|>>|<row|<cell|<math|C\<vdash\>x:\<tau\>\<longrightarrow\>\<exists\>\<varnothing\><around|[|\<b-T\>|]><around|{|x\<mapsto\>\<tau\>|}>>>>>>>|<with|gr-color|red|gr-arrow-end|\<gtr\>|<graphics|<with|color|red|arrow-end|\<gtr\>|<line|<point|0.968084|-0.407792>|<point|2.11109273713454|0.438880804339198>>>|<with|color|red|arrow-end|\<gtr\>|<line|<point|2.32276|-0.428959>|<point|4.07960709088504|0.460047625347268>>>>>>

    <em|slide5.gadt>:<math|C\<vdash\>K x:\<tau\>\<longrightarrow\>\<exists\><wide|\<alpha\>|\<bar\>><wide|\<beta\>|\<bar\>><around|[|D|]><around*|{|x\<mapsto\>\<tau\><rsub|1>|}>>

    <\code>
      let abs_gen_rules = fun x -\> x
    </code>

    <em|shell>:

    <\code>
      # invargent slide5.gadt -inform

      val abs_gen_rules : <math|\<forall\>>a. a <math|\<rightarrow\>> a
    </code>

    <\equation*>
      \;
    </equation*>

    <\equation*>
      \;
    </equation*>
  </hidden>|<\hidden>
    <tit|The Type System -- <verbatim|Cstr>>

    <\equation*>
      <frac|<tabular|<tformat|<table|<row|<cell|\<forall\>i
      C,\<Gamma\>\<vdash\>e<rsub|i>:\<tau\><rsub|i><with|mode|text|
      \ \ \ \ \ >C\<vDash\>D>>|<row|<cell|K\<colons\>\<forall\><wide|\<alpha\>|\<bar\>><wide|\<beta\>|\<bar\>><around|[|D|]>.\<tau\><rsub|1>\<ldots\>\<tau\><rsub|n>\<rightarrow\>\<varepsilon\><around|(|<wide|\<alpha\>|\<bar\>>|)>>>>>>|C,\<Gamma\>\<vdash\>K
      e<rsub|1>\<ldots\>e<rsub|n>:\<varepsilon\><around|(|<wide|\<alpha\>|\<bar\>>|)>>
    </equation*>

    <\equation*>
      <around*|\<llbracket\>|\<Gamma\>\<vdash\>K
      e<rsub|1>\<ldots\>e<rsub|n>:\<tau\>|\<rrbracket\>>=\<exists\><wide|\<alpha\>|\<bar\>><rprime|'><wide|\<beta\>|\<bar\>><rprime|'>.(\<wedge\><rsub|i><around*|\<llbracket\>|\<Gamma\>\<vdash\>e<rsub|i>:\<tau\><rsub|i><around|[|<wide|\<alpha\>|\<bar\>><wide|\<beta\>|\<bar\>>\<assign\><wide|\<alpha\>|\<bar\>><rprime|'><wide|\<beta\>|\<bar\>><rprime|'>|]>|\<rrbracket\>>\<wedge\>D<around|[|<wide|\<alpha\>|\<bar\>><wide|\<beta\>|\<bar\>>\<assign\><wide|\<alpha\>|\<bar\>><rprime|'><wide|\<beta\>|\<bar\>><rprime|'>|]>\<wedge\>\<varepsilon\><around|(|<wide|\<alpha\>|\<bar\>><rprime|'>|)><wide|=|\<dot\>>\<tau\>)
    </equation*>

    Type <verbatim|Num> could be defined as:<next-line><verbatim|newtype Num
    : num \ \ newcons 1 : Num 1 \ \ newcons 2 : Num 2 \ \ <math|\<ldots\>>>

    <em|slide6.gadt>:

    <\code>
      newtype Box : num

      newcons Small : <math|\<forall\>>n,k [n <math|\<leqslant\>>
      7<math|\<wedge\>> k = n+6]. Num n <math|\<longrightarrow\>> Box k

      \;

      let gift = Small 4

      let package = fun x -\> Small (x + -3)
    </code>

    <em|shell>:

    <\code>
      # invargent slide6.gadt -inform

      val gift : Box 10

      val package : <math|\<forall\>>n[n <math|\<leqslant\>> 10]. Num n
      <math|\<rightarrow\>> Box (n + 3)
    </code>
  </hidden>|<\hidden>
    <tit|AVL Trees -- <verbatim|singleton>>

    Height of left sibling, <verbatim|m>, differs by at most 2 from height of
    the right sibling, <verbatim|n>.

    Resulting height is <verbatim|max(m,n)+1>. Height value is stored with
    the node.

    <em|slide7.gadt>:

    <\code>
      newtype Avl : type * num

      newcons Empty : <math|\<forall\>>a. Avl (a, 0)

      newcons Node :

      \ \ <math|\<forall\>>a,k,m,n [k=max(m,n) <math|\<wedge\>>
      0<math|\<leqslant\>>m <math|\<wedge\>> 0<math|\<leqslant\>>n
      <math|\<wedge\>> n<math|\<leqslant\>>m+2 <math|\<wedge\>>
      m<math|\<leqslant\>>n+2].

      \ \ \ \ \ Avl (a, m) * a * Avl (a, n) * Num (k+1)
      <math|\<longrightarrow\>> Avl (a, k+1)

      \;

      let singleton = fun x -\> Node (Empty, x, Empty, 1)
    </code>

    <em|shell>:

    <\code>
      # invargent slide7.gadt -inform

      val singleton : <math|\<forall\>>a. a <math|\<rightarrow\>> Avl (a, 1)
    </code>
  </hidden>|<\hidden>
    <tit|The Type System -- <verbatim|WhenClause>>

    <\equation*>
      <frac|<tabular|<tformat|<cwith|3|3|3|3|cell-valign|c>|<table|<row|<cell|C\<wedge\>D,\<Gamma\>\<Gamma\><rprime|'>\<vdash\>m<rsub|i>:Num<around*|(|\<tau\><rsub|m<rsub|i>>|)>>|<cell|e\<neq\><with|math-font-series|bold|assert
      false>\<wedge\>\<ldots\>\<wedge\>>|<cell|>>|<row|<cell|C\<wedge\>D,\<Gamma\>\<Gamma\><rprime|'>\<vdash\>n<rsub|i>:Num<around*|(|\<tau\><rsub|n<rsub|i>>|)>>|<cell|e\<neq\>\<lambda\><around*|(|p<rprime|'>\<ldots\>\<lambda\><around*|(|p<rprime|''>.<with|math-font-series|bold|assert
      false>|)>|)>>|<cell|>>|<row|<cell|C\<vdash\>p:\<tau\><rsub|1>\<longrightarrow\>\<exists\><wide|\<beta\>|\<bar\>><around|[|D|]>\<Gamma\><rprime|'>>|<cell|C\<wedge\>D\<wedge\><rsub|i>\<tau\><rsub|m<rsub|i>>\<leqslant\>\<tau\><rsub|n<rsub|i>>,\<Gamma\>\<Gamma\><rprime|'>\<vdash\>e:\<tau\><rsub|2>>|<cell|<wide|\<beta\>|\<bar\>>#FV<around|(|C,\<Gamma\>,\<tau\><rsub|2>|)>>>>>>|C,\<Gamma\>\<vdash\>p<with|math-font-series|bold|
      when >\<wedge\><rsub|i>m<rsub|i>\<leqslant\>n<rsub|i>.e:\<tau\><rsub|1>\<rightarrow\>\<tau\><rsub|2>>
    </equation*>

    <\eqnarray*>
      <tformat|<table|<row|<cell|<around*|\<llbracket\>|\<Gamma\>\<vdash\>p<with|math-font-series|bold|
      when >\<wedge\><rsub|i>m<rsub|i>\<leqslant\>n<rsub|i>.e:\<tau\><rsub|1>\<rightarrow\>\<tau\><rsub|2>|\<rrbracket\>>>|<cell|=>|<cell|\<exists\><wide|\<alpha\><rsup|1><rsub|i>\<alpha\><rsup|2><rsub|i>|\<bar\>>.<around*|\<llbracket\>|\<vdash\>p\<downarrow\>\<tau\><rsub|1>|\<rrbracket\>>\<wedge\>\<forall\><wide|\<beta\>|\<bar\>>.D\<Rightarrow\>>>|<row|<cell|>|<cell|>|<cell|<with|mode|text|
      \ \ \ \ \ >\<wedge\><rsub|i><around*|\<llbracket\>|\<Gamma\>\<Gamma\><rprime|'>\<vdash\>m<rsub|i>:Num<around*|(|\<alpha\><rsup|1><rsub|i>|)>|\<rrbracket\>>\<wedge\><rsub|i><around*|\<llbracket\>|\<Gamma\>\<Gamma\><rprime|'>\<vdash\>n<rsub|i>:Num<around*|(|\<alpha\><rsup|2><rsub|i>|)>|\<rrbracket\>>>>|<row|<cell|<with|mode|text|when
      >e\<neq\><with|math-font-series|bold|assert
      false>\<wedge\>\<ldots\>\<wedge\>>|<cell|>|<cell|<with|mode|text|
      \ \ \ \ \ >\<wedge\><around*|(|\<wedge\><rsub|i>\<alpha\><rsup|1><rsub|i>\<leqslant\>\<alpha\><rsup|2><rsub|i>\<Rightarrow\><around*|\<llbracket\>|\<Gamma\>\<Gamma\><rprime|'>\<vdash\>e:\<tau\><rsub|2>|\<rrbracket\>>|)>>>|<row|<cell|e\<neq\>\<lambda\><around*|(|p<rprime|'>\<ldots\>\<lambda\><around*|(|p<rprime|''>.<with|math-font-series|bold|assert
      false>|)>|)>>|<cell|>|<cell|<text|where
      >\<exists\><wide|\<beta\>|\<bar\>><around|[|D|]>\<Gamma\><rprime|'><text|
      is ><around*|\<llbracket\>|\<vdash\>p\<uparrow\>\<tau\><rsub|1>|\<rrbracket\>>,<wide|\<beta\>|\<bar\>><wide|\<alpha\><rsup|1><rsub|i>\<alpha\><rsup|2><rsub|i>|\<bar\>>#FV<around|(|\<Gamma\>,\<tau\><rsub|1>,\<tau\><rsub|2>|)>>>>>
    </eqnarray*>

    <em|slide8.gadt>:

    <\code>
      newtype Signed : num

      newcons Pos : <math|\<forall\>>n [0 <math|\<leqslant\>> n]. Num n
      <math|\<longrightarrow\>> Signed n

      newcons Neg : <math|\<forall\>>n [n <math|\<leqslant\>> 0]. Num n
      <math|\<longrightarrow\>> Signed n

      let foo = function

      \ \ \| i when 7 \<less\>= i -\> Pos (i + -7)

      \ \ \| i when i \<less\>= 7 -\> Neg (i + -7)
    </code>

    Result: <verbatim|val foo : <math|\<forall\>>n. Num (n + 7)
    <math|\<rightarrow\>> Signed n>
  </hidden>|<\hidden>
    <tit|AVL Trees -- <verbatim|create>>

    <em|slide9.gadt>:

    <\code>
      newtype Avl : type * num

      newcons Empty : <math|\<forall\>>a. Avl (a, 0)

      newcons Node :

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
    <tit|The Type System -- <verbatim|NegClause>, <verbatim|AssertFalse>>

    <\equation*>
      <frac|<tabular|<tformat|<cwith|3|3|3|3|cell-valign|c>|<table|<row|<cell|C\<wedge\>D,\<Gamma\>\<Gamma\><rprime|'>\<vdash\>m<rsub|i>:Num<around*|(|\<tau\><rsub|m<rsub|i>>|)>>|<cell|e=<with|math-font-series|bold|assert
      false>\<vee\>\<ldots\>\<vee\>>|<cell|>>|<row|<cell|C\<wedge\>D,\<Gamma\>\<Gamma\><rprime|'>\<vdash\>n<rsub|i>:Num<around*|(|\<tau\><rsub|n<rsub|i>>|)>>|<cell|e=\<lambda\><around*|(|p<rprime|'>\<ldots\>\<lambda\><around*|(|p<rprime|''>.<with|math-font-series|bold|assert
      false>|)>|)>>|<cell|>>|<row|<cell|C\<vdash\>p:\<tau\><rsub|3>\<longrightarrow\>\<exists\><wide|\<beta\>|\<bar\>><around|[|D|]>\<Gamma\><rprime|'>>|<cell|C\<wedge\>D\<wedge\>\<tau\><rsub|1><wide|=|\<dot\>>\<tau\><rsub|3>\<wedge\><rsub|i>\<tau\><rsub|m<rsub|i>>\<leqslant\>\<tau\><rsub|n<rsub|i>>,\<Gamma\>\<Gamma\><rprime|'>\<vdash\>e:\<tau\><rsub|2>>|<cell|<wide|\<beta\>|\<bar\>>#FV<around|(|C,\<Gamma\>,\<tau\><rsub|2>|)>>>>>>|C,\<Gamma\>\<vdash\>p<with|math-font-series|bold|
      when >\<wedge\><rsub|i>m<rsub|i>\<leqslant\>n<rsub|i>.e:\<tau\><rsub|1>\<rightarrow\>\<tau\><rsub|2>>
    </equation*>

    <\eqnarray*>
      <tformat|<table|<row|<cell|<around*|\<llbracket\>|\<Gamma\>\<vdash\>p<with|math-font-series|bold|
      when >\<wedge\><rsub|i>m<rsub|i>\<leqslant\>n<rsub|i>.e:\<tau\><rsub|1>\<rightarrow\>\<tau\><rsub|2>|\<rrbracket\>>>|<cell|=>|<cell|\<exists\>\<alpha\><rsub|3><wide|\<alpha\><rsup|1><rsub|i>\<alpha\><rsup|2><rsub|i>|\<bar\>>.<around*|\<llbracket\>|\<vdash\>p\<downarrow\>\<alpha\><rsub|3>|\<rrbracket\>>\<wedge\>\<forall\><wide|\<beta\>|\<bar\>>.D\<Rightarrow\>>>|<row|<cell|>|<cell|>|<cell|<with|mode|text|
      \ \ \ \ \ >\<wedge\><rsub|i><around*|\<llbracket\>|\<Gamma\>\<Gamma\><rprime|'>\<vdash\>m<rsub|i>:Num<around*|(|\<alpha\><rsup|1><rsub|i>|)>|\<rrbracket\>>\<wedge\><rsub|i><around*|\<llbracket\>|\<Gamma\>\<Gamma\><rprime|'>\<vdash\>n<rsub|i>:Num<around*|(|\<alpha\><rsup|2><rsub|i>|)>|\<rrbracket\>>>>|<row|<cell|<with|mode|text|when
      >e=<with|math-font-series|bold|assert
      false>\<vee\>\<ldots\>\<vee\>>|<cell|>|<cell|<with|mode|text|
      \ \ \ \ \ >\<wedge\><around*|(|\<alpha\><rsub|3><wide|=|\<dot\>>\<tau\><rsub|1>\<wedge\><rsub|i>\<alpha\><rsup|1><rsub|i>\<leqslant\>\<alpha\><rsup|2><rsub|i>\<Rightarrow\><around*|\<llbracket\>|\<Gamma\>\<Gamma\><rprime|'>\<vdash\>e:\<tau\><rsub|2>|\<rrbracket\>>|)>>>|<row|<cell|e=\<lambda\><around*|(|p<rprime|'>\<ldots\>\<lambda\><around*|(|p<rprime|''>.<with|math-font-series|bold|assert
      false>|)>|)>>|<cell|>|<cell|>>|<row|<cell|>|<cell|>|<cell|<text|where
      >\<exists\><wide|\<beta\>|\<bar\>><around|[|D|]>\<Gamma\><rprime|'><text|
      is ><around*|\<llbracket\>|\<vdash\>p\<uparrow\>\<alpha\><rsub|3>|\<rrbracket\>>,<wide|\<beta\>|\<bar\>>\<alpha\><rsub|3><wide|\<alpha\><rsup|1><rsub|i>\<alpha\><rsup|2><rsub|i>|\<bar\>>#FV<around|(|\<Gamma\>,\<tau\><rsub|1>,\<tau\><rsub|2>|)>>>>>
    </eqnarray*>

    <\equation*>
      <frac|<tabular|<tformat|<cwith|1|1|1|1|cell-valign|c>|<table|<row|<cell|C\<vDash\>\<b-F\>>>>>>|C,\<Gamma\>\<vdash\><with|math-font-series|bold|assert
      false>:\<tau\><rsub|>>
    </equation*>

    In the solver, we assume for negation, that the numerical domain is
    integers, while in general we take it to be rational numbers.
  </hidden>|<\hidden>
    <tit|AVL Trees -- <verbatim|min_binding>>

    <em|slide11.gadt>:

    <\code>
      newtype Avl : type * num

      newcons Empty : <math|\<forall\>>a. Avl (a, 0)

      newcons Node :

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
    <tit|The Type System -- <verbatim|LetRec>>

    <\equation*>
      <frac|<tabular|<tformat|<table|<row|<cell|C,\<Gamma\><rprime|'>\<vdash\>e<rsub|1>:\<sigma\>>|<cell|C,\<Gamma\><rprime|'>\<vdash\>e<rsub|2>:\<tau\>>>|<row|<cell|\<sigma\>=\<forall\>\<beta\><around|[|\<exists\><wide|\<alpha\>|\<bar\>>.D|]>.\<beta\>>|<cell|\<Gamma\><rprime|'>=\<Gamma\><around|{|x\<mapsto\>\<sigma\>|}>>>>>>|C,\<Gamma\>\<vdash\><with|math-font-series|bold|letrec>
      x=e<rsub|1> <with|math-font-series|bold|in> e<rsub|2>:\<tau\>>
    </equation*>

    <\eqnarray*>
      <tformat|<table|<row|<cell|<around*|\<llbracket\>|\<Gamma\>\<vdash\><with|math-font-series|bold|letrec
      >x=e<rsub|1><with|math-font-series|bold| in
      >e<rsub|2>:\<tau\>|\<rrbracket\>>>|<cell|=>|<cell|<around*|(|\<forall\>\<beta\><around|(|\<chi\><around|(|\<beta\>|)>\<Rightarrow\><around*|\<llbracket\>|\<Gamma\><around|{|x\<mapsto\>\<forall\>\<beta\><around|[|\<chi\><around|(|\<beta\>|)>|]>.\<beta\>|}>\<vdash\>e<rsub|1>:\<beta\>|\<rrbracket\>>|)>|)>\<wedge\>>>|<row|<cell|>|<cell|>|<cell|<around|(|\<exists\>\<alpha\>.\<chi\><around|(|\<alpha\>|)>|)>\<wedge\><around*|\<llbracket\>|\<Gamma\><around|{|x\<mapsto\>\<forall\>\<beta\><around|[|\<chi\><around|(|\<beta\>|)>|]>.\<beta\>|}>\<vdash\>e<rsub|2>:\<tau\>|\<rrbracket\>>>>|<row|<cell|>|<cell|>|<cell|<with|mode|text|where
      >\<beta\>#FV<around|(|\<Gamma\>,\<tau\>|)>,\<chi\>#PV<around*|(|\<Gamma\>|)>>>>>
    </eqnarray*>

    <math|\<chi\><around*|(|\<cdummy\>|)>> is a second order variable.

    <em|slide12.gadt>:

    <\code>
      newtype List : type * num

      newcons LNil : <math|\<forall\>>a. List (a, 0)

      newcons LCons : <math|\<forall\>>a, n [0<math|\<leqslant\>>n]. a * List
      (a, n) <math|\<longrightarrow\>> List (a, n+1)

      \;

      let rec map = fun f -\>

      \ \ function LNil -\> LNil

      \ \ \ \ \| LCons (x, xs) -\> LCons (f x, map f xs)
    </code>

    Result: <verbatim|val map : <math|\<forall\>>n, a, b. (a
    <math|\<rightarrow\>> b) <math|\<rightarrow\>> List (a, n)
    <math|\<rightarrow\>> List (b, n)>
  </hidden>|<\hidden>
    <tit|Binary <verbatim|plus>>

    <em|binary_plus.gadt>:

    <\code>
      newtype Binary : num

      newtype Carry : num

      newcons Zero : Binary 0

      newcons PZero : <math|\<forall\>>n [0<math|\<leqslant\>>n]. Binary n
      <math|\<longrightarrow\>> Binary(2 n)

      newcons POne : <math|\<forall\>>n [0<math|\<leqslant\>>n]. Binary n
      <math|\<longrightarrow\>> Binary(2 n + 1)

      newcons CZero : Carry 0

      newcons COne : Carry 1

      \;

      let rec plus =

      \ \ function CZero -\>

      \ \ \ \ (function

      \ \ \ \ \ \ \| Zero -\>

      \ \ \ \ \ \ \ \ (function Zero -\> Zero <math|<around*|[|\<ldots\>|]>>

      \ \ \ \ \| COne -\>

      \ \ \ \ (function Zero -\>

      \ \ \ \ \ \ \ \ (function Zero -\> POne(Zero)

      \ \ \ \ \ \ \ \ \ \ \| PZero b1 -\> POne b1

      \ \ \ \ \ \ \ \ \ \ \| POne b1 -\> PZero (plus COne Zero b1))
      <math|<around*|[|\<ldots\>|]>>
    </code>

    <em|re.> <verbatim|plus: <math|\<forall\>>i, k, n. Carry i
    <math|\<rightarrow\>> Binary k <math|\<rightarrow\>> Binary n
    <math|\<rightarrow\>> Binary (n + k + i)>
  </hidden>|<\hidden>
    <tit|The Type System -- actual <verbatim|App>>

    <\equation*>
      <frac|<tabular|<tformat|<cwith|1|1|1|1|cell-col-span|2>|<table|<row|<cell|C,\<Gamma\>,\<Sigma\>\<vdash\>e<rsub|1>:\<tau\><rprime|'>\<rightarrow\>\<tau\>>|<cell|>>|<row|<cell|C,\<Gamma\>,\<Sigma\>\<vdash\>e<rsub|2>:\<tau\><rprime|'>>|<cell|C\<vDash\><neg|E><around*|(|\<tau\><rprime|'>|)>>>>>>|C,\<Gamma\>,\<Sigma\>\<vdash\>e<rsub|1>
      e<rsub|2>:\<tau\>>
    </equation*>

    <\equation*>
      <around*|\<llbracket\>|\<Gamma\>\<vdash\>e<rsub|1>
      e<rsub|2>:\<tau\>|\<rrbracket\>>=\<exists\>\<alpha\>.<around*|\<llbracket\>|\<Gamma\>\<vdash\>e<rsub|1>:\<alpha\>\<rightarrow\>\<tau\>|\<rrbracket\>>\<wedge\><around*|\<llbracket\>|\<Gamma\>\<vdash\>e<rsub|2>:\<alpha\>|\<rrbracket\>>\<wedge\><neg|E><around*|(|\<alpha\>|)>,\<alpha\>#FV<around|(|\<Gamma\>,\<tau\>|)>
    </equation*>

    Above, <math|<neg|E><around*|(|\<tau\><rprime|'>|)>> means that
    <math|\<tau\><rprime|'>> is not an existential type. Therefore
    <em|slide14.gadt> fails:

    <\code>
      newtype List : type * num

      newcons LNil : <math|\<forall\>>a. List(a, 0)

      newcons LCons : <math|\<forall\>>n, a [0<math|\<leqslant\>>n]. a *
      List(a, n) <math|\<longrightarrow\>> List(a, n+1)

      let rec filter = fun f -\>

      \ \ efunction LNil -\> LNil

      \ \ \ \ \| LCons (x, xs) -\>

      \ \ \ \ \ \ ematch f x with

      \ \ \ \ \ \ \ \ \| True -\> LCons (x, filter f xs)

      \ \ \ \ \ \ \ \ \| False -\> filter f xs
    </code>

    <em|shell>: unfortunately, error not informative in current
    implementation

    <\code>
      ../invargent slide14.gadt -inform

      File "slide14.gadt", line 5, characters 2-134:

      No answer in type: term abduction failed
    </code>
  </hidden>|<\hidden>
    <tit|Filter a List>

    <em|filter.gadt>:

    <\code>
      newtype List : type * num

      newcons LNil : <math|\<forall\>>a. List(a, 0)

      newcons LCons : <math|\<forall\>>n, a [0<math|\<leqslant\>>n]. a *
      List(a, n) <math|\<longrightarrow\>> List(a, n+1)

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

    We use both <verbatim|efunction> and <verbatim|ematch> (a
    <math|\<beta\>>-redex for <verbatim|efunction>), because
    <verbatim|function> and <verbatim|match> would require the types of
    branch bodies to be equal: to be lists of the same length.

    <\code>
      val filter :

      \ \ <math|\<forall\>>n, a.

      \ \ (a <math|\<rightarrow\>> Bool) <math|\<rightarrow\>> List (a, n)
      <math|\<rightarrow\>> <math|\<exists\>>k[0 <math|\<leqslant\>> k
      <math|\<wedge\>> k <math|\<leqslant\>> n].List (a, k)
    </code>
  </hidden>|<\hidden>
    <tit|TheTypeSystem -- <verbatim|ExLetIn>>

    <\equation*>
      <frac|<tabular|<tformat|<cwith|2|2|1|1|cell-col-span|2>|<table|<row|<cell|\<varepsilon\><rsub|K><around*|(|<wide|\<alpha\>|\<bar\>>|)><with|mode|text|
      in >\<Sigma\>>|<cell|<with|mode|text|
      >C,\<Gamma\>,\<Sigma\>\<vdash\>e<rsub|1>:\<tau\><rprime|'>>>|<row|<cell|C,\<Gamma\>,\<Sigma\>\<vdash\>K
      p.e<rsub|2>:\<tau\><rprime|'>\<rightarrow\>\<tau\>>|<cell|>>>>>|C,\<Gamma\>,\<Sigma\>\<vdash\><rsup|><with|math-font-series|bold|let>
      p=e<rsub|1> <with|math-font-series|bold|in> e<rsub|2>:\<tau\>>
    </equation*>

    <\eqnarray*>
      <tformat|<table|<row|<cell|<around*|\<llbracket\>|\<Gamma\>\<vdash\><with|math-font-series|bold|let>
      p=e<rsub|1> <with|math-font-series|bold|in>
      e<rsub|2>:\<tau\>|\<rrbracket\>>>|<cell|=>|<cell|\<exists\>\<alpha\><rsub|0>.<around*|\<llbracket\>|\<Gamma\>\<vdash\>e<rsub|1>:\<alpha\><rsub|0>|\<rrbracket\>>\<wedge\>>>|<row|<cell|>|<cell|>|<cell|<around*|(|<around*|\<llbracket\>|\<Gamma\>\<vdash\>p.e<rsub|2>:\<alpha\><rsub|0>\<rightarrow\>\<tau\>|\<rrbracket\>>\<wedge\><neg|E><around*|(|\<alpha\><rsub|0>|)>\<vee\><rsub|K\<in\>\<cal-E\>><around*|\<llbracket\>|\<Gamma\>\<vdash\>K
      p.e<rsub|2>:\<alpha\><rsub|0>\<rightarrow\>\<tau\>|\<rrbracket\>>|)>>>|<row|<cell|>|<cell|>|<cell|<text|where
      >\<cal-E\>=<around*|{|K<mid|\|>K\<colons\>\<forall\><wide|\<alpha\>|\<bar\>><wide|\<beta\>|\<bar\>><around|[|E|]>.\<tau\>\<rightarrow\>\<varepsilon\><rsub|K><around*|(|<wide|\<alpha\>|\<bar\>>|)>\<in\>\<Sigma\>|}>>>>>
    </eqnarray*>

    <\small>
      OCaml code generated for <em|filter.gadt> -- <em|filter.ml>:

      <\code>
        type _ list =

        \ \ \| LNil : (*<math|\<forall\>>'a.*) ('a (* 0 *)) list

        \ \ \| LCons : (*<math|\<forall\>>'n, 'a[0 <math|\<leqslant\>>
        n].*)'a * ('a (* n *)) list -\<gtr\>

        \ \ \ \ ('a (* n + 1 *)) list

        <with|color|red|type _ ex2> =

        \ \ \| Ex2 : (*<math|\<forall\>>'k, 'n, 'a[0 <math|\<leqslant\>> k
        <math|\<wedge\>> k <math|\<leqslant\>> n].*)('a (* k *)) list
        -\<gtr\>

        \ \ \ \ ((* n,*) 'a) ex2

        let rec filter :

        \ \ type (*n*) a . (((a -\> bool)) -\> (a (* n *)) list -\> ((* n,*)
        a) ex2) =

        \ \ (fun f -\>

        \ \ \ \ (function LNil -\> let xcase = LNil in Ex2 xcase

        \ \ \ \ \ \ \| LCons (x, xs) -\>

        \ \ \ \ \ \ \ \ \ \ (if f x then

        \ \ \ \ \ \ \ \ \ \ <with|color|red|let Ex2 ys = filter f xs> in let
        xcase = LCons (x, ys) in Ex2 xcase

        \ \ \ \ \ \ \ \ \ \ else let Ex2 xcase = filter f xs in Ex2 xcase)))
      </code>
    </small>
  </hidden>|<\hidden>
    <tit|Issues -- Multiple Maximally General Types>

    <em|equal1_wrong.gadt>: compare two values of types as encoded

    <\small>
      <\code>
        newtype Ty : type

        newtype List : type

        newcons Zero : Int

        newcons Nil : <math|\<forall\>>a. List a

        newcons TInt : Ty Int

        newcons TPair : <math|\<forall\>>a, b. Ty a * Ty b
        <math|\<longrightarrow\>> Ty (a, b)

        newcons TList : <math|\<forall\>>a. Ty a <math|\<longrightarrow\>> Ty
        (List a)

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
  </hidden>|<\hidden>
    <tit|InvarGenT Handles Many Non-pointwise Cases>

    Chuan-kai Lin developed an efficient type inference algorithm for GADTs,
    however in a type system restricted to so-called pointwise types.

    Toy example -- <em|non_pointwise_split.gadt>:

    <\code>
      newtype Split : type * type

      newcons Whole : Split (Int, Int)

      newcons Parts : <math|\<Alpha\>>a, b. Split ((Int, a), (b, Bool))

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
  </hidden>|<\hidden>
    <tit|InvarGenT Handles Sensible Non-pointwise Cases>

    <\small>
      Chuan-kai Lin's system needs a workaround, InvarGenT works with def.
      settings -- <em|non_pointwise_avl.gadt>:

      <\code>
        (** Normally we would use [num], but this is a stress test for
        [type]. *)

        newtype Z

        newtype S : type

        newtype Balance : type * type * type

        newcons Less : <math|\<forall\>>a. Balance (a, S a, S a)

        newcons Same : <math|\<forall\>>a. Balance (a, a, a)

        newcons More : <math|\<forall\>>a. Balance (S a, a, S a)

        newtype AVL : type

        newcons Leaf : AVL Z

        newcons Node :

        \ \ <math|\<forall\>>a, b, c. Balance (a, b, c) * AVL a * Int * AVL b
        <math|\<longrightarrow\>> AVL (S c)

        \;

        newtype Choice : type * type

        newcons Left : <math|\<forall\>>a, b. a <math|\<longrightarrow\>>
        Choice (a, b)

        newcons Right : <math|\<forall\>>a, b. b <math|\<longrightarrow\>>
        Choice (a, b)

        \;

        let rotr = fun z d -\> function

        \ \ \| Leaf -\> assert false

        \ \ \| Node (Less, a, x, Leaf) -\> assert false

        \ \ \| Node (Same, a, x, (Node (_,_,_,_) as b)) -\>

        \ \ \ \ Right (Node (Less, a, x, Node (More, b, z, d)))
        <math|<around*|[|\<ldots\>|]>>
      </code>

      Result: <verbatim|<math|\<forall\>>a.Int <math|\<rightarrow\>> AVL a
      <math|\<rightarrow\>> AVL (S (S a)) <math|\<rightarrow\>> Choice (AVL
      (S (S a)), AVL (S (S (S a))))>
    </small>
  </hidden>|<\hidden>
    <tit|InvarGenT does not Handle Some Non-sensible Cases>

    A solution to at least one branch of implications, correspondingly of
    pattern matching, must be implied by the conjunction of the premise and
    the conclusion of the branch. I.e., some branch must be solvable without
    arbitrary guessing. If solving a branch requires guessing, for some
    ordering of branches, the solution to already solved branches must be a
    good guess.

    <em|non_pointwise_vary.gadt>:

    <\code>
      newtype EquLR : type * type * type

      newcons EquL : <math|\<forall\>>a, b. EquLR (a, a, b)

      newcons EquR : <math|\<forall\>>a, b. EquLR (a, b, b)

      newtype Box : type

      newcons Cons : <math|\<forall\>>a. a <math|\<longrightarrow\>> Box a

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
        that <math|\<cal-I\>,<no-break>C\<vDash\><around*|\<llbracket\>|\<Gamma\>\<vdash\>ce:<no-break>\<tau\>|\<rrbracket\>>>.
      </theorem>
    </large>
  </hidden>|<\shown>
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
  </shown>>
</body>

<initial|<\collection>
</collection>>

<\references>
  <\collection>
    <associate|InfComplExpr|<tuple|2|23|../../../Dropbox/Dokumenty/GADT/invargent-slides-Jan.tm>>
    <associate|InfCorrExpr|<tuple|1|23|../../../Dropbox/Dokumenty/GADT/invargent-slides-Jan.tm>>
  </collection>
</references>