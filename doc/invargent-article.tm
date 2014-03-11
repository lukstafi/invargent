<TeXmacs|1.99.1>

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

  <include|invargent.tm>

  <\bibliography|bib|tm-plain|biblio.bib>
    <\bib-list|4>
      <bibitem*|1><label|bib-ArithQuantElim>Sergey<nbsp>Berezin,
      Vijay<nbsp>Ganesh<localize| and >David L.<nbsp>Dill.<newblock> An
      online proof-producing decision procedure for mixed-integer linear
      arithmetic.<newblock> <localize|In ><with|font-shape|italic|Proceedings
      of the 9th international conference on Tools and algorithms for the
      construction and analysis of systems>, TACAS'03, <localize|pages
      >521--536. Berlin, Heidelberg, 2003. Springer-Verlag.<newblock>

      <bibitem*|2><label|bib-ConvexHull>Komei<nbsp>Fukuda, Thomas
      M.<nbsp>Liebling<localize| and >Christine<nbsp>LÃ¼tolf.<newblock>
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

      <bibitem*|4><label|bib-AntiUnifAlg>B<nbsp>Ã˜stvold.<newblock> A
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
    <associate|AlienSubterms|<tuple|3.3|9|invargent.tm>>
    <associate|Details|<tuple|6.5|20|invargent.tm>>
    <associate|ImplSubst|<tuple|4|2>>
    <associate|Main Algo|<tuple|5.3|?>>
    <associate|MainAlgo|<tuple|6|15|invargent.tm>>
    <associate|MainAlgoBody|<tuple|6.3|18|invargent.tm>>
    <associate|NegElim|<tuple|4.4|13|invargent.tm>>
    <associate|NumConv|<tuple|4.2|12|invargent.tm>>
    <associate|OptiAtoms|<tuple|5|14|invargent.tm>>
    <associate|Rg|<tuple|5|18|invargent.tm>>
    <associate|SCAlinear|<tuple|3.4|9|invargent.tm>>
    <associate|SepProp|<tuple|5|3>>
    <associate|SepProp2|<tuple|6|?>>
    <associate|Skp|<tuple|1|18|invargent.tm>>
    <associate|Skp1|<tuple|10|18|invargent.tm>>
    <associate|SolSimpl|<tuple|9|12>>
    <associate|SolvedForm|<tuple|4|?>>
    <associate|SolvedFormProj|<tuple|7|?>>
    <associate|auto-1|<tuple|1|1|invargent.tm>>
    <associate|auto-10|<tuple|3.3|9|invargent.tm>>
    <associate|auto-11|<tuple|3.4|9|invargent.tm>>
    <associate|auto-12|<tuple|4|11|invargent.tm>>
    <associate|auto-13|<tuple|4.1|11|invargent.tm>>
    <associate|auto-14|<tuple|4.2|12|invargent.tm>>
    <associate|auto-15|<tuple|4.3|12|invargent.tm>>
    <associate|auto-16|<tuple|4.4|13|invargent.tm>>
    <associate|auto-17|<tuple|5|14|invargent.tm>>
    <associate|auto-18|<tuple|5.1|14|invargent.tm>>
    <associate|auto-19|<tuple|5.2|15|invargent.tm>>
    <associate|auto-2|<tuple|2|3|invargent.tm>>
    <associate|auto-20|<tuple|5.3|15|invargent.tm>>
    <associate|auto-21|<tuple|6|15|invargent.tm>>
    <associate|auto-22|<tuple|6.1|15|invargent.tm>>
    <associate|auto-23|<tuple|6.2|16|invargent.tm>>
    <associate|auto-24|<tuple|6.3|18|invargent.tm>>
    <associate|auto-25|<tuple|6.4|20|invargent.tm>>
    <associate|auto-26|<tuple|6.5|20|invargent.tm>>
    <associate|auto-27|<tuple|7|21|invargent.tm>>
    <associate|auto-28|<tuple|7|22>>
    <associate|auto-3|<tuple|2.1|5|invargent.tm>>
    <associate|auto-4|<tuple|2.1.1|5|invargent.tm>>
    <associate|auto-5|<tuple|2.2|5|invargent.tm>>
    <associate|auto-6|<tuple|3|6|invargent.tm>>
    <associate|auto-7|<tuple|3.1|6|invargent.tm>>
    <associate|auto-8|<tuple|3.1.1|8|invargent.tm>>
    <associate|auto-9|<tuple|3.2|8|invargent.tm>>
    <associate|bib-AbductionSolvMaher|<tuple|3|22>>
    <associate|bib-AntiUnifAlg|<tuple|4|22>>
    <associate|bib-AntiUnifInv|<tuple|2|4>>
    <associate|bib-AntiUnifPlotkin|<tuple|4|4>>
    <associate|bib-AntiUnifReynolds|<tuple|5|4>>
    <associate|bib-ArithQuantElim|<tuple|1|22>>
    <associate|bib-ConvexHull|<tuple|2|22>>
    <associate|bib-DBLP:conf/cccg/2000|<tuple|3|?>>
    <associate|bib-ESOP2014|<tuple|9|23>>
    <associate|bib-UnificationBaader|<tuple|1|4>>
    <associate|bib-disjelimTechRep|<tuple|6|23>>
    <associate|bib-invariantsTechRep2|<tuple|7|23>>
    <associate|bib-jcaqpTechRep|<tuple|8|4>>
    <associate|bib-jcaqpTechRep2|<tuple|8|23>>
    <associate|bib-jcaqpUNIF|<tuple|5|23>>
    <associate|bib-simonet-pottier-hmg-toplas|<tuple|6|4>>
    <associate|bib-systemTechRep|<tuple|5|18>>
  </collection>
</references>

<\auxiliary>
  <\collection>
    <\associate|bib>
      AbductionSolvMaher

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

      <with|par-left|<quote|1tab>|2.1<space|2spc>Normalization
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-3>>

      <with|par-left|<quote|2tab>|2.1.1<space|2spc>Implementation details
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-4>>

      <with|par-left|<quote|1tab>|2.2<space|2spc>Simplification
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-5>>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|3<space|2spc>Abduction>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-6><vspace|0.5fn>

      <with|par-left|<quote|1tab>|3.1<space|2spc>Simple constraint abduction
      for terms <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-7>>

      <with|par-left|<quote|2tab>|3.1.1<space|2spc>Heuristic for better
      answers to invariants <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-8>>

      <with|par-left|<quote|1tab>|3.2<space|2spc>Joint constraint abduction
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-9>>

      <with|par-left|<quote|1tab>|3.3<space|2spc>Abduction for terms with
      Alien Subterms <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-10>>

      <with|par-left|<quote|1tab>|3.4<space|2spc>Simple constraint abduction
      for linear arithmetics <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-11>>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|4<space|2spc>Constraint
      Generalization> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-12><vspace|0.5fn>

      <with|par-left|<quote|1tab>|4.1<space|2spc>Extended convex hull
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-13>>

      <with|par-left|<quote|1tab>|4.2<space|2spc>Issues in inferring
      postconditions <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-14>>

      <with|par-left|<quote|1tab>|4.3<space|2spc>Abductive disjunction
      elimination given quantifier prefix
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-15>>

      <with|par-left|<quote|1tab>|4.4<space|2spc>Incorporating negative
      constraints <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-16>>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|5<space|2spc><with|font-shape|<quote|italic>|opti>
      and <with|font-shape|<quote|italic>|subopti>:
      <with|font-shape|<quote|italic>|minimum> and
      <with|font-shape|<quote|italic>|maximum> relations in
      <with|font-family|<quote|tt>|language|<quote|verbatim>|num>>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-17><vspace|0.5fn>

      <with|par-left|<quote|1tab>|5.1<space|2spc>Normalization, validity and
      implication checking <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-18>>

      <with|par-left|<quote|1tab>|5.2<space|2spc>Abduction
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-19>>

      <with|par-left|<quote|1tab>|5.3<space|2spc>Disjunction elimination
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-20>>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|6<space|2spc>Solving
      for Predicate Variables> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-21><vspace|0.5fn>

      <with|par-left|<quote|1tab>|6.1<space|2spc>Invariant Parameter
      Candidates <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-22>>

      <with|par-left|<quote|1tab>|6.2<space|2spc>Solving for Predicates in
      Negative Positions <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-23>>

      <with|par-left|<quote|1tab>|6.3<space|2spc>Solving for Existential
      Types Predicates and Main Algorithm
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-24>>

      <with|par-left|<quote|1tab>|6.4<space|2spc>Stages of iteration
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-25>>

      <with|par-left|<quote|1tab>|6.5<space|2spc>Implementation details
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-26>>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|7<space|2spc>Generating
      OCaml/Haskell Source and Interface Code>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-27><vspace|0.5fn>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|Bibliography>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-28><vspace|0.5fn>
    </associate>
  </collection>
</auxiliary>