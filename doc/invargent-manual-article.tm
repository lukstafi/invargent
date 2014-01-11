<TeXmacs|1.0.7.21>

<style|article>

<\body>
  <doc-data|<doc-title|InvarGenT: Manual>||<doc-author|<author-data|<author-name|Šukasz
  Stafiniak>|<\author-affiliation>
    Institute of Computer Science

    University of Wrocªaw
  </author-affiliation>>>>

  <abstract-data|<abstract|InvarGenT is a proof-of-concept system for
  invariant generation by full type inference with Guarded Algebraic Data
  Types and existential types encoded as automatically generated GADTs. This
  user manual discusses motivating examples, briefly presents the syntax of
  the InvarGenT language, and describes the parameters of the inference
  process that can be passed to the InvarGenT executable.>>

  <include|invargent-manual.tm>

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
    <associate|auto-1|<tuple|1|1|invargent-manual.tm>>
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
    <associate|auto-2|<tuple|2|1|invargent-manual.tm>>
    <associate|auto-20|<tuple|5.4|17|invargent.tm>>
    <associate|auto-21|<tuple|5.5|17|invargent.tm>>
    <associate|auto-22|<tuple|6|18|invargent.tm>>
    <associate|auto-23|<tuple|6|18|invargent.tm>>
    <associate|auto-24|<tuple|5.5|17>>
    <associate|auto-3|<tuple|3|5|invargent-manual.tm>>
    <associate|auto-4|<tuple|4|7|invargent-manual.tm>>
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