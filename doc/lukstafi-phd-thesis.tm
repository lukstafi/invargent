<TeXmacs|1.99.2>

<style|<tuple|tmbook|env-float>>

<\body>
  <\hide-preamble>
    \;

    <assign|by-text|<macro|<localize| >>>

    <assign|abstract|<\macro|body>
      <render-abstract|<arg|body>>
    </macro>>

    <assign|render-abstract|<\macro|body>
      <surround|<no-indent>||<chapter*|<abstract-text>>>

      <surround||<hflush>|<arg|body>>
    </macro>>
  </hide-preamble>

  <doc-data|<doc-title|GADTs for Reconstruction of Invariants and
  Postconditions>|<doc-author|<\author-data|<author-name|Šukasz Stafiniak>>
    \;
  </author-data|<\author-affiliation>
    University of Wrocªaw

    Department of Mathematics and Computer Science

    Institute of Computer Science
  </author-affiliation>>>|<\doc-misc>
    <strong|PhD Thesis>

    <strong|Doctoral advisor: prof. dr hab. Leszek Pacholski>
  </doc-misc>|<doc-date|Wrocªaw 2015>>

  <doc-data|<doc-title|Typy GADT dla rekonstrukcji niezmienników i warunków
  ko«<no-break>cowych>|<doc-author|<author-data|<author-name|Šukasz
  Stafiniak>|<\author-affiliation>
    Uniwersytet Wrocªawski

    Wydziaª Matematyki i Informatyki

    Instytut Informatyki
  </author-affiliation>>>|<\doc-misc>
    <strong|Rozprawa doktorska napisana pod kierunkiem>

    <strong|prof. dra hab. Leszka Pacholskiego>
  </doc-misc>|<doc-date|Wrocªaw 2015>>

  <abstract-data|<\abstract>
    Type systems for programming languages are both a first line of defense
    against programmer mistakes, and an aid in structuring programs around
    data structures and functions that manipulate them. Type systems are a
    natural formalism for language extensions that express those aspects of
    program specifications which can be automatically, statically checked.
    Type inference enhances programmer efficiency and code adaptability by
    providing the types of expressions to the programmer, rather than asking
    the programmer for the types. There is a long line of research on
    automated program analysis and verification by generating specifications
    that a program does obey, for example generating loop invariants. This
    thesis extends a familiar type system for functional programming
    languages and provides a type inference algorithm that generates
    invariants and postconditions of recursive functions.

    Generalized Algebraic Data Types (GADTs) extend polymorphic type systems
    by introducing reasoning by cases into type-checking of definitions by
    cases. We present a GADTs type system <math|MMG(X)> based on François
    Pottier and Vincent Simonet's <math|HMG(X)> but without type annotations.
    We extend it to a language with existential types represented as
    implicitly defined and used GADTs. We show that the type inference
    problem reduces to satisfaction of second order constraints.

    We solve the constraints by iterating: (1) constraint generalization,
    which finds most specific common consequences; and (2) joint constraint
    abduction, which finds most general common explanations. Abduction is
    used to generate invariants, infer and check types. Generalization is
    used to generate existential types, which serve as postconditions. The
    constraints include linear arithmetic (equations and inequalities).

    We called the system implementing these techniques <name|InvarGenT>. It
    solves a vast majority of inference tasks we attempted, without type
    annotations. <name|InvarGenT> solves nearly all meaningful GADTs
    inference tasks we tried, clearly more than all earlier type inference
    implementations for GADTs. It also solves clearly more invariant and
    postcondition inference tasks than the <em|Liquid Types> approach, except
    for some programs with higher-order functions. In addition, we present a
    selection of new inference tasks, for programs manipulating lists with
    length, binary numbers and AVL trees of imbalance 2. These programs can
    serve as baseline tests for future research on invariant and
    postcondition inference.
  </abstract>>

  <surround|||<chapter*|Streszczenie>>

  Systemy typów dla j¦zyków programowania s¡ zarówno pierwsz¡ lini¡ obrony
  przed bª¦dami programistycznymi, jak i pomoc¡ przy strukturowaniu programów
  wokóª struktur danych oraz funkcji które nimi manipuluj¡. Systemy typów to
  dobry formalizm do wyra»ania tych aspektów specyfikacji programów, które
  mog¡ by¢ automatycznie, statycznie sprawdzone. Inferencja typów zwi¦ksza
  wydajno±¢ programisty i adaptowalno±¢ kodu dostarczaj¡c programi±cie typy
  wyra»e«, zamiast wymaga¢ podawania typów. Badania nad automatyczn¡ analiz¡
  i weryfikacj¡ programów od dawna obejmowaªy mi¦dzy innymi generowanie
  specyfikacji speªnianych przez dane programy, na przykªad generowanie
  niezmienników p¦tli. Ta praca rozszerza znany system typów dla j¦zyków
  funkcyjnych i podaje algorytm inferencji typów, generuj¡cy niezmienniki i
  warunki ko«cowe funkcji rekurencyjnych.

  Generalized Algebraic Data Types (GADTs) rozszerzaj¡ systemy typów
  polimorficznych o wnioskowanie przez przypadki podczas sprawdzania typu
  definicji przez przypadki. Prezentuj¦ system typów
  <math|MMG<around*|(|X|)>> z GADTs, oparty o system typów
  <math|HMG<around*|(|X|)>> François Pottiera i Vincenta Simoneta ale bez
  annotacji typami. Rozszerzam go do j¦zyka z typami egzystencjalnymi
  reprezentowanymi jako domy±lnie definiowane i u»ywane struktury GADTs.
  Pokazuj¦ redukcj¦ problemu inferencji typów do speªnialno±ci wi¦zów
  drugiego rz¦du.<hflush>

  Wi¦zy drugiego rz¦du rozwi¡zuj¦ iteruj¡c dwa algorytmy: (1) generalizacj¦
  wi¦zów, znajduj¡c¡ najbardziej specyficzn¡ wspóln¡ konsekwencj¦ wi¦zów; (2)
  ª¡czn¡ abdukcj¦ wi¦zów, zna<no-break>jduj¡ca najogólniejsze wspólne
  obja±nienie, przesªank¦ implikuj¡c¡ wi¦zy. Abdukcji u»ywamy gªównie do
  generowania niezmienników, inferencji i sprawdzania typów. Generalizacji
  u»ywamy do generowania typów egzystencjalnych, sªu»¡cych jako warunki
  ko«cowe. Wi¦zy obejmuj¡ arytmetyk¦ liniow¡ (równania i nierówno±ci).

  System implementuj¡cy te techniki nazwaªem <name|InvarGenT>. Rozwi¡zuje on
  zdecydowan¡ wi¦kszo±¢ zada« inferencji które opracowaªem lub zaadaptowaªem,
  bez annotacji typami. <name|InvarGenT> rozwi¡zuje zdecydowanie wi¦cej zada«
  inferencji typów dla GADTs ni» dotychczasowe systemy. Rozwi¡zuje te» wi¦cej
  problemów inferencji niezmienników i warunków ko«cowych ni» podej±cie
  <em|Liquid Types>, je±li ograniczymy si¦ do zada« nie potrzebuj¡cych
  inferencji niezmienników dla argumentów funkcji wy»szego rz¦du. Dodatkowo,
  prezentuj¦ kilka programów operuj¡cych na listach z dªugo±ci¡, liczbach
  binarnych i drzewach AVL o niezbalansowaniu nie przekraczaj¡cym 2. Te
  programy mog¡ sªu»y¢ jako cz¦±¢ testów dla przyszªych prac nad
  wszechstronnymi systemami inferencji niezmienników i warunków ko«cowych.

  <surround|||<chapter*|Acknowledgements>>

  I thank my advisor Leszek Pacholski for supporting the great opportunity to
  pursue this work despite my excursions to other topics and projects. I
  thank Šukasz Kaiser for feedback and support through the years. My office
  colleague Jan Otop offered discussions early in my work. Dariusz Biernacki
  reviewed and helped improve my conference paper. Filip Sieczkowski, Jakub
  Michaliszyn and Marek Materzok remarks helped improve the thesis
  presentation. All the technical errors are my sole responsibility. Most of
  all, I dedicate this thesis to my parents Maria and Piotr, without whose
  support this work would not have been possible.

  \;

  \;

  \;

  \;

  \;

  <\right-aligned>
    <em|Every problem that is interesting is also soluble.>

    David Deutsch's Law
  </right-aligned>

  <\table-of-contents|toc>
    <vspace*|1fn><with|font-series|bold|math-font-series|bold|font-shape|small-caps|Abstract>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <pageref|auto-1><vspace|0.5fn>

    <vspace*|1fn><with|font-series|bold|math-font-series|bold|font-shape|small-caps|Streszczenie>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <pageref|auto-2><vspace|0.5fn>

    <vspace*|1fn><with|font-series|bold|math-font-series|bold|font-shape|small-caps|Acknowledgements>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <pageref|auto-3><vspace|0.5fn>

    <vspace*|1fn><with|font-series|bold|math-font-series|bold|font-shape|small-caps|1.<space|2spc>Introduction>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <pageref|auto-4><vspace|0.5fn>

    1.1.<space|2spc>Contributions <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-5>

    1.2.<space|2spc>Examples <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-6>

    <vspace*|1fn><with|font-series|bold|math-font-series|bold|font-shape|small-caps|2.<space|2spc>Background
    and Related Work> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <pageref|auto-9><vspace|0.5fn>

    2.1.<space|2spc>The DML System <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-10>

    <with|par-left|1tab|2.1.1.<space|2spc>The Type System
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-11>>

    <with|par-left|1tab|2.1.2.<space|2spc>Bidirectional Type Inference
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-12>>

    <with|par-left|1tab|2.1.3.<space|2spc>Relevance
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-13>>

    2.2.<space|2spc>The <with|mode|math|HMG<around*|(|X|)>> Formalization
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-14>

    <with|par-left|1tab|2.2.1.<space|2spc>The Untyped Calculus
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-15>>

    <with|par-left|1tab|2.2.2.<space|2spc>The
    <with|mode|math|HMG<around*|(|X|)>> Type System
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-19>>

    <with|par-left|1tab|2.2.3.<space|2spc>Constraint Derivation
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-20>>

    <with|par-left|1tab|2.2.4.<space|2spc>Relevance
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-22>>

    2.3.<space|2spc>The <with|mode|math|OutsideIn<around*|(|X|)>> System
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-23>

    <with|par-left|1tab|2.3.1.<space|2spc>Type Inference
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-24>>

    <with|par-left|1tab|2.3.2.<space|2spc>Relevance
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-25>>

    2.4.<space|2spc>Pointwise GADTs <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-26>

    <with|par-left|1tab|2.4.1.<space|2spc>Type Inference
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-27>>

    <with|par-left|1tab|2.4.2.<space|2spc>Relevance
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-28>>

    2.5.<space|2spc>Liquid Types <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-29>

    <with|par-left|1tab|2.5.1.<space|2spc>The Type System
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-30>>

    <with|par-left|1tab|2.5.2.<space|2spc>Liquid Types Inference
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-31>>

    <with|par-left|1tab|2.5.3.<space|2spc>Relevance
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-32>>

    2.6.<space|2spc>Herbrand Constraint Abduction
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-33>

    <with|par-left|1tab|2.6.1.<space|2spc>Relevance
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-35>>

    <vspace*|1fn><with|font-series|bold|math-font-series|bold|font-shape|small-caps|3.<space|2spc>The
    Type System> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <pageref|auto-36><vspace|0.5fn>

    3.1.<space|2spc>The Language of Constraints
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-37>

    3.2.<space|2spc>The Type System with GADTs
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-39>

    3.3.<space|2spc>Type Inference Constraints
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-44>

    3.4.<space|2spc>Existential Types <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-50>

    3.5.<space|2spc>Type Inference Constraints for Existential Types
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-54>

    3.6.<space|2spc>Semantics by Reduction to
    <with|mode|math|HMG<around*|(|X|)>> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-55>

    <vspace*|1fn><with|font-series|bold|math-font-series|bold|font-shape|small-caps|4.<space|2spc>Solving
    Second Order Constraints> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <pageref|auto-56><vspace|0.5fn>

    4.1.<space|2spc>Overview of Solving for Predicate Variables
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-57>

    4.2.<space|2spc>Constraint Abduction <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-58>

    <with|par-left|1tab|4.2.1.<space|2spc>Formulating the Joint Constraint
    Abduction Problem <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-59>>

    <with|par-left|1tab|4.2.2.<space|2spc>Abduction Algorithm for The
    Combination of Domains <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-60>>

    <with|par-left|1tab|4.2.3.<space|2spc>Joint Constraint Abduction
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-62>>

    <with|par-left|1tab|4.2.4.<space|2spc>Simple Constraint Abduction
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-63>>

    <with|par-left|2tab|4.2.4.1.<space|2spc>Abduction for Terms
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-64>>

    <with|par-left|2tab|4.2.4.2.<space|2spc>Abduction for Linear Arithmetic
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-65>>

    4.3.<space|2spc>Constraint Generalization
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-66>

    <with|par-left|1tab|4.3.1.<space|2spc>Algorithm for Combining Domains
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-67>>

    <with|par-left|1tab|4.3.2.<space|2spc>Linear Arithmetic
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-69>>

    <with|par-left|1tab|4.3.3.<space|2spc>Abductive Constraint Generalization
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-70>>

    4.4.<space|2spc>Negative Constraints <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-71>

    4.5.<space|2spc>Details of Solving for Predicate Variables
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-72>

    <vspace*|1fn><with|font-series|bold|math-font-series|bold|font-shape|small-caps|5.<space|2spc><with|font-shape|small-caps|InvarGenT>:
    Tests and Limitations> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <pageref|auto-75><vspace|0.5fn>

    5.1.<space|2spc>Benchmarks <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-76>

    5.2.<space|2spc><with|font-shape|small-caps|InvarGenT> Failure Cases
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-80>

    <with|par-left|1tab|5.2.1.<space|2spc>The Need to Expand Pattern
    Variables <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-81>>

    <with|par-left|1tab|5.2.2.<space|2spc>Constraints Shared by Constructors
    of a Datatype <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-82>>

    <with|par-left|1tab|5.2.3.<space|2spc>Negative Constraints in the Sort of
    Terms <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-83>>

    <with|par-left|1tab|5.2.4.<space|2spc>Insufficient Context to Infer
    Postconditions <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-84>>

    <with|par-left|1tab|5.2.5.<space|2spc>Insufficient Search
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-85>>

    <with|par-left|1tab|5.2.6.<space|2spc>Nested Definitions with Tied
    Postconditions <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-86>>

    <vspace*|1fn><with|font-series|bold|math-font-series|bold|font-shape|small-caps|6.<space|2spc>Conclusions>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <pageref|auto-87><vspace|0.5fn>

    6.1.<space|2spc>Related Work <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-88>

    6.2.<space|2spc>Future Work <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-89>

    6.3.<space|2spc>Summary <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-90>

    <vspace*|1fn><with|font-series|bold|math-font-series|bold|font-shape|small-caps|Bibliography>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <pageref|auto-91><vspace|0.5fn>

    <vspace*|1fn><with|font-series|bold|math-font-series|bold|font-shape|small-caps|Appendix
    A.<space|2spc>Proofs> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <pageref|auto-92><vspace|0.5fn>

    A.1.<space|2spc>The Type System <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-93>

    <with|par-left|1tab|A.1.1.<space|2spc>The Logic of Constraints
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-94>>

    <with|par-left|1tab|A.1.2.<space|2spc>The GADT Type System
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-95>>

    <with|par-left|1tab|A.1.3.<space|2spc>Existential Types
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-96>>

    <with|par-left|1tab|A.1.4.<space|2spc>Semantics by Reduction to
    <with|mode|math|HMG<around*|(|X|)>> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-97>>

    A.2.<space|2spc>Constraint Abduction <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-98>

    <with|par-left|1tab|A.2.1.<space|2spc>Formulating the Joint Constraint
    Abduction Problem <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-99>>

    <with|par-left|1tab|A.2.2.<space|2spc>Abduction Algorithm for The
    Combination of Domains <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-100>>

    A.3.<space|2spc>Constraint Generalization
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-101>

    A.4.<space|2spc>Solving for Predicate Variables
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-102>

    <vspace*|1fn><with|font-series|bold|math-font-series|bold|font-shape|small-caps|Appendix
    B.<space|2spc>Algorithmic Details> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <pageref|auto-103><vspace|0.5fn>

    B.1.<space|2spc>Generating and Normalizing Formulas
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-104>

    <with|par-left|1tab|B.1.1.<space|2spc>Normalization
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-105>>

    <with|par-left|2tab|B.1.1.1.<space|2spc>Implementation Details
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-106>>

    <with|par-left|1tab|B.1.2.<space|2spc>Simplification
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-107>>

    B.2.<space|2spc>Abduction <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-108>

    <with|par-left|1tab|B.2.1.<space|2spc>Abduction for Terms with Alien
    Subterms <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-109>>

    <with|par-left|1tab|B.2.2.<space|2spc>Joint Constraint Abduction
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-110>>

    <with|par-left|1tab|B.2.3.<space|2spc>Simple Constraint Abduction for
    Terms <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-111>>

    <with|par-left|2tab|B.2.3.1.<space|2spc>Heuristic for Better Answers to
    Invariants <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-112>>

    <with|par-left|1tab|B.2.4.<space|2spc>Simple Constraint Abduction for
    Linear Arithmetics <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-113>>

    B.3.<space|2spc>Constraint Generalization
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-114>

    <with|par-left|1tab|B.3.1.<space|2spc>Extended Convex Hull
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-115>>

    <with|par-left|1tab|B.3.2.<space|2spc>Issues in Inferring Postconditions
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-116>>

    <with|par-left|1tab|B.3.3.<space|2spc>Abductive Constraint Generalization
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-117>>

    B.4.<space|2spc>Incorporating Negative Constraints
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-119>

    B.5.<space|2spc><with|font-shape|italic|opti> and
    <with|font-shape|italic|subopti>: <with|font-shape|italic|minimum> and
    <with|font-shape|italic|maximum> Relations in
    <with|font-family|tt|language|verbatim|num>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-120>

    <with|par-left|1tab|B.5.1.<space|2spc>Normalization, Validity and
    Implication Checking <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-121>>

    <with|par-left|1tab|B.5.2.<space|2spc>Abduction
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-122>>

    <with|par-left|1tab|B.5.3.<space|2spc>Constraint Generalization
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-123>>

    B.6.<space|2spc>Solving for Predicate Variables
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-124>

    <with|par-left|1tab|B.6.1.<space|2spc>Solving for Predicates in Premises
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-125>>

    <with|par-left|1tab|B.6.2.<space|2spc>Solving for Existential Types
    Predicates and Main Algorithm <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-126>>

    <with|par-left|1tab|B.6.3.<space|2spc>Stages of Iteration
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-127>>

    <with|par-left|1tab|B.6.4.<space|2spc>Implementation Details
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-128>>

    B.7.<space|2spc>Generating OCaml Source and Interface Code
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-129>

    <vspace*|1fn><with|font-series|bold|math-font-series|bold|font-shape|small-caps|Appendix
    C.<space|2spc>Source Code of Examples>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <pageref|auto-130><vspace|0.5fn>

    C.1.<space|2spc>Incompleteness Example for
    <with|font-family|tt|language|verbatim|OutsideIn>: Function
    <with|font-family|tt|language|verbatim|rx>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-131>

    C.2.<space|2spc>Pointwise Examples <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-132>

    <with|par-left|1tab|C.2.1.<space|2spc>Function
    <with|font-family|tt|language|verbatim|rotate>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-133>>

    <with|par-left|1tab|C.2.2.<space|2spc>Function
    <with|font-family|tt|language|verbatim|zip2>: <with|mode|math|N>-way
    <with|font-family|tt|language|verbatim|zip_with>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-134>>

    <with|par-left|1tab|C.2.3.<space|2spc>Function
    <with|font-family|tt|language|verbatim|rotl>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-135>>

    <with|par-left|1tab|C.2.4.<space|2spc>Function
    <with|font-family|tt|language|verbatim|ins>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-136>>

    <with|par-left|1tab|C.2.5.<space|2spc>Function
    <with|font-family|tt|language|verbatim|extract>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-137>>

    <with|par-left|1tab|C.2.6.<space|2spc>Function
    <with|font-family|tt|language|verbatim|run_state>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-138>>

    C.3.<space|2spc>Non-Pointwise Examples
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-139>

    <with|par-left|1tab|C.3.1.<space|2spc>Function
    <with|font-family|tt|language|verbatim|joint>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-140>>

    <with|par-left|1tab|C.3.2.<space|2spc>Function
    <with|font-family|tt|language|verbatim|rotr>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-141>>

    <with|par-left|1tab|C.3.3.<space|2spc>Function
    <with|font-family|tt|language|verbatim|delmin>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-142>>

    <with|par-left|1tab|C.3.4.<space|2spc>Function
    <with|font-family|tt|language|verbatim|fd_comp>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-143>>

    <with|par-left|1tab|C.3.5.<space|2spc>Function
    <with|font-family|tt|language|verbatim|zip1>: <with|mode|math|N>-way
    <with|font-family|tt|language|verbatim|zip_with>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-144>>

    <with|par-left|1tab|C.3.6.<space|2spc>Function
    <with|font-family|tt|language|verbatim|leq>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-145>>

    <with|par-left|1tab|C.3.7.<space|2spc>Function
    <with|font-family|tt|language|verbatim|run_state>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-146>>

    C.4.<space|2spc>Run-time Type Representations
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-147>

    <with|par-left|1tab|C.4.1.<space|2spc>Function
    <with|font-family|tt|language|verbatim|eval>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-148>>

    <with|par-left|1tab|C.4.2.<space|2spc>Function
    <with|font-family|tt|language|verbatim|equal>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-149>>

    C.5.<space|2spc>Lists with Length <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-150>

    <with|par-left|1tab|C.5.1.<space|2spc>Function
    <with|font-family|tt|language|verbatim|head>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-151>>

    <with|par-left|1tab|C.5.2.<space|2spc>Function
    <with|font-family|tt|language|verbatim|append>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-152>>

    <with|par-left|1tab|C.5.3.<space|2spc>Function
    <with|font-family|tt|language|verbatim|flatten_pairs>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-153>>

    <with|par-left|1tab|C.5.4.<space|2spc>Function
    <with|font-family|tt|language|verbatim|filter>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-154>>

    <with|par-left|1tab|C.5.5.<space|2spc>Function
    <with|font-family|tt|language|verbatim|zip>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-155>>

    C.6.<space|2spc>Binary Numbers <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-156>

    <with|par-left|1tab|C.6.1.<space|2spc>Function
    <with|font-family|tt|language|verbatim|plus>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-157>>

    <with|par-left|1tab|C.6.2.<space|2spc>Function
    <with|font-family|tt|language|verbatim|increment>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-158>>

    <with|par-left|1tab|C.6.3.<space|2spc>Function
    <with|font-family|tt|language|verbatim|bitwise_or>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-159>>

    C.7.<space|2spc>AVL Trees <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-160>

    C.8.<space|2spc>Arrays and Matrices <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-161>

    <with|par-left|1tab|C.8.1.<space|2spc>Program
    <with|font-family|tt|language|verbatim|dotprod>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-162>>

    <with|par-left|1tab|C.8.2.<space|2spc>Program
    <with|font-family|tt|language|verbatim|bcopy>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-163>>

    <with|par-left|1tab|C.8.3.<space|2spc>Program
    <with|font-family|tt|language|verbatim|bsearch>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-164>>

    <with|par-left|1tab|C.8.4.<space|2spc>Function
    <with|font-family|tt|language|verbatim|bsearch2>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-165>>

    <with|par-left|1tab|C.8.5.<space|2spc>Program
    <with|font-family|tt|language|verbatim|queen>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-166>>

    <with|par-left|1tab|C.8.6.<space|2spc>Function
    <with|font-family|tt|language|verbatim|swap_interval>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-167>>

    <with|par-left|1tab|C.8.7.<space|2spc>Program
    <with|font-family|tt|language|verbatim|isort>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-168>>

    <with|par-left|1tab|C.8.8.<space|2spc>Program
    <with|font-family|tt|language|verbatim|tower>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-169>>

    <with|par-left|1tab|C.8.9.<space|2spc>Program
    <with|font-family|tt|language|verbatim|matmult>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-170>>

    <with|par-left|1tab|C.8.10.<space|2spc>Program
    <with|font-family|tt|language|verbatim|heapsort>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-171>>

    <with|par-left|1tab|C.8.11.<space|2spc>Program
    <with|font-family|tt|language|verbatim|simplex>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-172>>

    <with|par-left|1tab|C.8.12.<space|2spc>Program
    <with|font-family|tt|language|verbatim|gauss>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-173>>

    <with|par-left|1tab|C.8.13.<space|2spc>Program
    <with|font-family|tt|language|verbatim|fft>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-174>>

    <vspace*|1fn><with|font-series|bold|math-font-series|bold|font-shape|small-caps|Appendix
    D.<space|2spc><with|font-shape|small-caps|InvarGenT>: Manual>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <pageref|auto-175><vspace|0.5fn>

    D.1.<space|2spc>Introduction <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-176>

    D.2.<space|2spc>Tutorial <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-177>

    D.3.<space|2spc>Syntax <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-178>

    D.4.<space|2spc>Solver Parameters and CLI
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-179>

    D.5.<space|2spc>Limitations of Current
    <with|font-shape|small-caps|InvarGenT> Inference
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-180>
  </table-of-contents>

  <chapter|Introduction><label|Intro>

  Type systems are established natural deduction-style means to specify
  programs. Dependent types can represent arbitrarily complex properties as
  they use the same language for both types and programs. The type of the
  value returned by a function can itself be a function of the argument.
  Generalized Algebraic Data Types (GADTs) bring some of that expressiveness
  to type systems with data-types and parametric polymorphism, by introducing
  the ability to reason about the return type by case analysis on the input
  value. Work over the past decade (Pottier and Régis-Gianas
  <cite|StratifiedGADTs>, Schrijvers, Peyton Jones, Sulzmann<localize| and
  >Vytiniotis <cite|ComplDecidableGADTs>, Lin<localize| and >Sheard
  <cite|PointwiseGADTs>) shows that type systems with GADTs can remain
  tractable from a compiler implementer's perspective if appropriately
  constrained, i.e. have principal typings and efficient type inference. Our
  work is based on Simonet and Pottier <cite|simonet-pottier-hmg-toplas>
  instead, which is the most general presentation of GADTs. Our methods are
  computationally intensive and involve search with backtracking. We expect
  to be able to infer types for more programs than all of the
  efficiency-oriented approaches. Our work could bear the title <em|Type
  Inference for GADTs and Existentials>, but we stress that we do not compete
  with the work of <cite|StratifiedGADTs>, <cite|ComplDecidableGADTs> in
  particular. We are concerned with type inference for recursive definitions
  which are not given their type beforehand. This polymorphic recursion
  problem has been tackled by <cite|PointwiseGADTs> with GADTs, by Schrijvers
  and Bruynooghe <cite|ADTReconstruct> without GADTs. The line of work
  following Unno and Kobayashi <cite|InterpolationInfer> also tackles
  reconstruction of types for recursive definitions, but without ADTs and
  without polymorphic recursion. Our intended usage is that the generated
  types of recursive definitions be integrated into the source code, via
  integration with an IDE.

  Existential types hide some information conveyed in a type. We may opt to
  use them to expose a more abstract interface. However, sometimes we are
  forced to use existential types to hide what cannot be expressed in the
  type system. GADTs provide existential types by using local type variables
  for the hidden parts of the type encapsulated in a GADT. With no other way
  to express existential types, programmers need to introduce by hand
  spurious data-types for them. For example, if we want to hide the length of
  a list in OCaml, we need to define <verbatim|type _ elist = List : ('a, 'b)
  llist -\<gtr\> 'a elist>, where <verbatim|('a, 'b) llist> is the type of
  lists of length <verbatim|'b> with elements of type <verbatim|'a>. The type
  system in Xi<localize| and >Pfenning <cite|DML99> for a language called
  Dependent ML, a precursor for GADTs, has a more light-weight approach:
  explicit existential types. But <cite|DML99> has limited type inference,
  and we find its type system harder to grasp than the more recent
  presentations of GADTs. Knowles<localize| and >Flanagan <cite|KnowlesF07>
  and Unno<localize| and >Kobayashi <cite|InterpolationInfer> can be seen as
  performing type inference for forms of existential types. We provide full
  reconstruction of existential types.

  The feedback provided by type inference makes strongly typed programming
  more convenient in several ways. It softens the learning curve by enabling
  learning of types by experimentation. It facilitates rapid prototyping and
  code refactoring by reporting the types of functions when the programmer
  experiments with invariants of data-types. Besides providing certain
  correctness guarantees, types also serve as documentation -- it is good to
  keep them around. If type inference results are incorporated in the source
  code, type checking might suffice during slow evolution of a code base,
  while the rich types document the code.

  Our type system for GADTs differs from others in that we do not require any
  type annotations on expressions, even on recursive functions. Inference in
  our implementation sometimes requires guidance by <verbatim|assert>
  clauses. Our implementation <name|InvarGenT> includes linear arithmetic in
  the language used to express invariants and postconditions, with the
  possibility to introduce more domains in the future. The arithmetic
  properties are conjunctions of equations and inequalities, where a side can
  be either a linear combination, or a maximum or minimum of (at most two)
  linear combinations.

  <\example>
    We can easily specify the data-type of AVL trees with height imbalance of
    at most 2:

    <\code>
      datatype Avl : type * num

      datacons Empty : <math|\<forall\>>a. Avl (a, 0)

      datacons Node : <math|\<forall\>>a,k,m,n

      \ \ [k=max(m,n) <math|\<wedge\>> 0<math|\<leqslant\>>m <math|\<wedge\>>
      0<math|\<leqslant\>>n <math|\<wedge\>> n<math|\<leqslant\>>m+2
      <math|\<wedge\>> m<math|\<leqslant\><no-break>>n+2].

      \ \ \ \ \ Avl (a, m) * a * Avl (a, n) * Num (k+1)

      \ \ \ \ \ <math|\<longrightarrow\>> Avl (a, k+1)
    </code>

    A similar definition can be given in the DML and ATS languages by Hongwei
    Xi (see <cite|DML99>). Given this type definition and AVL tree
    algorithms, <name|InvarGenT> automatically finds out that the height of a
    tree with added element can be the same as original tree or bigger by 1,
    and that removing an element can decrease the height of a tree by at most
    1, returning, among others, the types:

    <\code>
      add :

      \ \ <math|\<forall\>>a,n.a<math|\<rightarrow\>>Avl(a,
      n)<math|\<rightarrow\>><math|\<exists\>>k[k<math|\<leqslant\>>n+1
      <math|\<wedge\>> 1<math|\<leqslant\>>k <math|\<wedge\>>
      n<math|\<leqslant\>>k].Avl(a, k)

      remove :

      \ \ <math|\<forall\>>a,n.a<math|\<rightarrow\>>Avl(a,
      n)<math|\<rightarrow\>><math|\<exists\>>k[n<math|\<leqslant\>>k+1
      <math|\<wedge\>> 0<math|\<leqslant\>>k <math|\<wedge\>>
      k<math|\<leqslant\>>n].Avl(a, k)
    </code>

    There are no places requiring type annotations or informative assertions
    in the source code of AVL tree algorithms including the above functions
    and their helper functions.
  </example>

  We reduce the type inference task to <em|second order> constraint
  satisfaction, which in addition to finding substitutions for first order
  variables, finds solutions to the predicate unknowns. As the
  predicate-finding techniques that we present in Chapter
  <reference|ChapSolv> (especially abduction) improve, type inference will
  work for more programs. The downside is that we do not specify
  declaratively the limitations of type inference. That is, while we provide
  some guarantees that our approach to inference does not overlook solutions
  (completeness-like result at the end of Section
  <reference|PredVarSolvDetails>), there is no concise formulation of when
  type inference succeeds.

  Constraints appear in three contexts in programs and inferred signatures:

  <\itemize>
    <item>In specifications of value constructors (symbolically
    <math|K\<colons\>\<forall\><wide|\<beta\>|\<bar\>><around*|[|D|]>.\<tau\><rsub|1>\<times\>\<ldots\>\<times\>\<tau\><rsub|n>\<longrightarrow\>\<varepsilon\><around*|(|<wide|\<tau\>|\<bar\>>|)>>).
    We call the constraint (i.e. <math|D>) the invariant (of <math|K>).

    <item>In type schemes, which usually are signatures of values
    (symbolically <math|x:\<forall\><wide|a|\<bar\>><around*|[|D|]>.\<tau\>>).
    We call the constraint (i.e. <math|D>) the invariant or the precondition
    (of <math|x>), interchangeably.

    <item>In existential types (symbolically
    <math|\<exists\><wide|\<alpha\>|\<bar\>><around*|[|D|]>.\<tau\>>);
    existential types usually occur in result positions of function types in
    type schemes. We call the constraint (i.e. <math|D>) the postcondition
    (of the corresponding function or computation).
  </itemize>

  <section|Contributions>

  In order to implement <name|InvarGenT>, we needed to resolve several
  issues, leading to our contributions:

  <\itemize>
    <item>Design a type system that captures invariants (Section
    <reference|TypSys>) and postconditions (Section <reference|ExTypes>).\ 

    <item>Reduce type inference to satisfaction of second order constraints
    (Sections <reference|TypInfCns> and <reference|ExTypesCns>).

    <item>Employ invariant-finding abduction and postcondition-finding
    generalization in an algorithm that reconstructs correct types (Section
    <reference|MainAlg>).

    <item>Develop constraint abduction algorithms that handle universally
    quantified variables (Section <reference|AbdAlg>).

    <item>Develop constraint generalization algorithms. Constraint
    generalization computes anti-unification in case of free terms and
    extended convex hull in case of linear inequalities (Section
    <reference|DisjElim>).
  </itemize>

  To summarize, the novelty of our work lies in:

  <\enumerate>
    <item>performing type inference for GADTs with polymorphic recursion for
    more programs than in prior work (<cite|PointwiseGADTs>),

    <item>introducing existentials into the GADT type system with minimal
    added complexity, by using GADT encodings, and performing type inference
    for them,

    <item>implementing the type inference over a constraint domain with
    linear arithmetics, thus performing numerical precondition and
    postcondition generation for recursive functions (in a different manner
    than in Rondon, Kawaguchi and Jhala <cite|DSolvePaper>).
  </enumerate>

  We discuss related work in Chapter <reference|ChapBackground> and Section
  <reference|SecRelWork>. There remains work to be done, as we discuss in
  Section <reference|FailureCases> and Section <reference|SecFutWork>.

  <name|InvarGenT> can be found at <verbatim|<hlink|https://github.com/lukstafi/invargent|https://github.com/lukstafi/invargent>>.
  It solves a vast majority of inference tasks we attempted, without type
  annotations. <name|InvarGenT> solves all but 3 tasks from Lin
  <cite|PracticalGADTsInfer> (2 unsolved are practical, one of them is solved
  after a slight meaning-preserving modification); the system from
  <cite|PracticalGADTsInfer> does not solve 8 of those tasks (7 unsolved are
  practical). We translated into <name|InvarGenT> all but 3 tasks from
  Rondon, Kawaguchi and Jhala <cite|DSolvePaper> -- all tasks that
  <cite|DSolvePaper> uses for comparison with Xi and Pfenning's DML system
  <cite|DML99>, <cite|DMLArrays>. <name|InvarGenT> solves all but 2 of these
  inference tasks without any type annotation, and solves the remaining 2
  tasks after a slight meaning-preserving change to the programs (still
  without any type annotation). The system <name|DSolve> from
  <cite|DSolvePaper> implementing the <em|Liquid Types> approach needs a type
  annotation for 3 of these inference tasks. The inference times of
  <name|InvarGenT> and <name|DSolve> are of the same order. Overall, the
  <name|InvarGenT> approach solves clearly more inference tasks than the
  <em|Liquid Types> approach, when the programs do not have higher-order
  functions that require universally quantified invariants for arguments,
  including existentially quantified invariants for arguments of arguments.
  In addition, we present a selection of new inference tasks, for programs
  manipulating lists with length, binary numbers and AVL trees of imbalance
  2. They can serve as a baseline for future research. We expect that some of
  them are beyond the capabilities of any current type inference system,
  except <name|InvarGenT>. <name|DSolve> does not introduce new linear
  combinations into generated constraints, therefore will not solve some of
  these inference tasks. The recent system <name|SpecLearn>, see He Zhu,
  Aditya Nori and Suresh Jagannathan <cite|SpecLearnArrays>, cannot solve
  tasks like the AVL trees example, without any type annotations or
  assertions.

  <section|Examples>

  To motivate the language constructs and type system rules, we start with
  some examples. The concrete syntax of <name|InvarGenT> is similar to that
  of OCaml. The sort of a type variable is identified by the first letter of
  the variable. <verbatim|a>,<verbatim|b>,<verbatim|c>,<verbatim|r>,<verbatim|s>,<verbatim|t>,<verbatim|a1>,...
  are in the sort of ``proper'' types. <verbatim|i>,<verbatim|j>,<verbatim|k>,<verbatim|l>,<verbatim|m>,<verbatim|n>,<verbatim|i1>,...
  are in the sort of linear arithmetic over rational numbers. Type
  constructors and value constructors have the same syntax: capitalized name
  followed by a tuple of arguments. They are introduced by the keywords
  <verbatim|datatype> and <verbatim|datacons> respectively. The result sort
  of <verbatim|datatype> is always <verbatim|type> and is omitted. By
  <em|toplevel> of a source file we mean the environment of names available
  for potential code appended to the end of the file. Values assumed into the
  toplevel without <name|InvarGenT> definition are introduced by the keyword
  <verbatim|external>.

  We can introduce existential types directly in type declarations. To have
  an existential type inferred, we have to use <verbatim|efunction>,
  <verbatim|ematch> or <verbatim|eif> expressions, which differ from
  <verbatim|function>, <verbatim|match> and <verbatim|if> correspondingly
  only in that the (return) type is an existential type. To use, i.e. unpack,
  a value of an existential type, we have to bind it with a
  <verbatim|let>..<verbatim|in> expression. An existential type will be
  automatically unpacked before being ``repackaged'' as another existential
  type. In a future version, it might be possible to use existential types
  without explicit introduction (the <verbatim|efunction>, <verbatim|ematch>
  or <verbatim|eif> syntax) and explicit elimination (the need of
  <verbatim|let>..<verbatim|in> expressions) at a cost of longer inference
  times.

  <\example>
    Table <reference|CodeEx2> defines an artificial example using phantom
    types (i.e. types used for type information, without values), resembling
    binary numbers. The function <verbatim|erase_zeros> erases the ``zeros''
    <verbatim|BinaryO> and adds one <verbatim|BinaryI>.<\float|float|t>
      <\big-table>
        <\code>
          <label|CodeEx2>datatype Z

          datatype I : type

          datatype O : type

          datatype Binary : type

          datacons BinaryZ : Binary Z

          datacons BinaryO : <math|\<forall\>>a. Binary a
          <math|\<longrightarrow\>> Binary (O a)

          datacons BinaryI : <math|\<forall\>>a. Binary a
          <math|\<longrightarrow\>> Binary (I a)

          \;

          let rec erase_zeros = efunction

          \ \ \| BinaryZ -\> BinaryI BinaryZ

          \ \ \| BinaryO x -\> erase_zeros x

          \ \ \| BinaryI x -\> let y = erase_zeros x in BinaryI y
        </code>

        \;
      </big-table|Use of existential types>
    </float>

    We get <verbatim|erase_zeros:<math|\<forall\>>a.Binary
    a<math|\<rightarrow\>><math|\<exists\>>a.Binary (I a)>. The resulting
    type forgets the shape of the content, other than the fact that it starts
    with a <verbatim|BinaryI>. The first branch of <verbatim|erase_zeros>
    returns a value directly. The second branch directly performs the
    recursive call -- the existential type of the result is unpacked and
    ``repackaged''. The third branch unpacks the result of the recusrive call
    explicitly. By design, the inlined variant <verbatim|\| BinaryI x -\>
    BinaryI (erase_zeros x)> would not type-check. The type system does not
    allow passing values of existential types as arguments.
  </example>

  <name|InvarGenT> commits to a type of a toplevel definition before
  proceeding to the next one, so sometimes we need to provide more
  information in the program. Besides type annotations, there are three means
  to enrich the generated constraints: <verbatim|assert false> indicates an
  unreachable code location and provides a negative constraint,
  <verbatim|assert num e<math|<rsub|1>>\<less\>=e<math|<rsub|2>>> and
  <verbatim|assert type e<math|<rsub|1>>=e<math|<rsub|2>>> provide positive
  constraints, and the <verbatim|test> syntax includes constraints of the use
  cases appearing after <verbatim|test> with the constraint of a toplevel
  definition.

  <\example>
    Table <reference|CodeEx3> defines a function <verbatim|equal> comparing
    values provided representation of their types. The value constructors
    <verbatim|TInt>, <verbatim|TPair>, <verbatim|TList> are used to represent
    the types of values compared. The function <verbatim|equal> checks
    whether the second and third argument are of the same type, and if so,
    whether they are equal.<\float|float|t>
      <\big-table>
        <\code>
          <label|CodeEx3>datatype List : type

          datacons Nil : <math|\<forall\>>a. List a

          datacons Cons : <math|\<forall\>>a. a * List a
          <math|\<longrightarrow\>> List a

          datatype TypeRepr : type

          datacons TInt : TypeRepr Int

          datacons TPair : <math|\<forall\>>a, b. TypeRepr a * TypeRepr b
          <math|\<longrightarrow\>> TypeRepr (a, b)

          datacons TList : <math|\<forall\>>a. TypeRepr a
          <math|\<longrightarrow\>> TypeRepr (List a)

          external let eq_int : Int <math|\<rightarrow\>> Int
          <math|\<rightarrow\>> Bool = "(=)"

          external let b_and : Bool <math|\<rightarrow\>> Bool
          <math|\<rightarrow\>> Bool = "fun a b -\<gtr\> a && b"

          external let b_not : Bool <math|\<rightarrow\>> Bool = "fun b
          -\<gtr\> not b"

          external let forall2 :

          \ \ <math|\<forall\>>a, b. (a<math|\<rightarrow\>>b<math|\<rightarrow\>>Bool)
          <math|\<rightarrow\>> List a <math|\<rightarrow\>> List b
          <math|\<rightarrow\>> Bool =

          \ \ "fun f a b -\<gtr\> List.for_all2 f a b"

          external let zero : Int = "0"

          \;

          let rec equal = function

          \ \ \| TInt, TInt -\> fun x y -\> eq_int x y

          \ \ \| TPair (t1, t2), TPair (u1, u2) -\> \ 

          \ \ \ \ (fun (x1, x2) (y1, y2) -\>

          \ \ \ \ \ \ \ \ b_and (equal (t1, u1) x1 y1)

          \ \ \ \ \ \ \ \ \ \ \ \ \ \ (equal (t2, u2) x2 y2))

          \ \ \| TList t, TList u -\> forall2 (equal (t, u))

          \ \ \| _ -\> fun _ _ -\> False

          \ \ \| TInt, TList l -\>

          \ \ \ \ (function Nil -\> assert false)

          \ \ \| TList l, TInt -\>

          \ \ \ \ (function _ -\> function Nil -\> assert false)

          test b_not (equal (TInt, TList TInt) zero Nil)
        </code>

        \;
      </big-table|Two ways of constraining types>
    </float>

    We get <verbatim|equal<math|:\<forall\>>a,b.(TypeRepr a, TypeRepr
    b)<math|\<rightarrow\>>a<math|\<rightarrow\>>b<math|\<rightarrow\>>Bool>.
    To ensure only one maximally general type for <verbatim|equal>, it is
    sufficient to provide either the two <verbatim|assert false> clauses, or
    the <verbatim|test> clause; both are illustrated above. The first
    assertion excludes independence of the first encoded type and the second
    argument. The second assertion excludes independence of the second
    encoded type and the third argument. The test ensures that arguments of
    distinct types can be <no-break>given.
  </example>

  Besides displaying types of toplevel definitions, <name|InvarGenT> also
  exports an OCaml source file with all the required GADT definitions and
  type annotations.

  <chapter|Background and Related Work><label|ChapBackground>

  In this chapter, we provide background knowledge and context by taking an
  in-depth look at a selection of related work. Sections
  <reference|HMGSection> and <reference|HerbSection> constitute a proper
  background for later chapters. The remaining sections describe alternative
  approaches to type inferece for GADTs, and more broadly to the task of
  automatic generation and verification of program specifications for
  functional programming languages like OCaml. Readers familiar with the
  works cited below may skip directly to the subsections <em|Relevance>,
  where we contrast the corresponding work with <name|InvarGenT>. The final
  chapter's Section <reference|SecRelWork> provides a broader perspective on
  related work.

  The theoretical underpinnings of type systems for program specification
  trace back to the work on dependent types by Per Martin-Löf, for example
  <cite|MartinLof>. An early example of a practical programming language
  based on dependent types is Cayenne by Lennart Augustsson, <cite|Cayenne>.
  A currently popular example of such language is Idris by Edwin Brady
  <cite|IdrisCurrent>, see also Brady, Herrmann and Hammond
  <cite|IdrisEarly>. But the family of approaches our thesis belongs to,
  maintains the separation of types and values characteristic of languages
  like Pascal, C, OCaml and Haskell. This separation allows to employ
  domain-specific decision procedures to reason about types, and also to
  automatically infer types.

  We start with Hongwei Xi and Frank Pfenning <cite|DML99>, which not only is
  a precursor of GADTs research, but also stresses the importance of
  existential types and type inference. We present the
  <math|HMG<around*|(|X|)>> system from Simonet and Pottier
  <cite|simonet-pottier-hmg-toplas>, to motivate and gain familiarity with
  the formalism of our constraint-based type system. We then present
  Schrijvers, Peyton Jones, Sulzmann and Vytiniotis <cite|OutsideIn>, and Lin
  and Sheard <cite|PointwiseGADTs>, to illustrate one thread of approaches to
  type inference for type systems with GADTs. Then, we switch gears to
  discuss inference of invariants, known as <em|liquid types> from Rondon,
  Kawaguchi and Jhala <cite|DSolvePaper>, expanded in <cite|DSolveTechRep>
  and <cite|DSolveThesis>. Finally, we describe Maher and Huang
  <cite|AbductionSolvMaher>, which provides the basis for our constraint
  abduction algorithm for terms.

  We take liberties with the presentation of the systems described, except
  <math|HMG<around*|(|X|)>> where we stay close to the letter of
  <cite|simonet-pottier-hmg-toplas>. We apologize for any unfortunate
  resulting errors and misunderstandings, and encourage interested readers to
  consult the original publications.

  <section|The DML System><label|DMLSection>

  The work of Hongwei Xi and Frank Pfenning <cite|DML99>, see also
  <cite|DMLThesis>, was at the forefront of research introducing type system
  features modeled on dependent types into practical programming languages of
  the ML family. These features mediate the dependence of types on terms by
  the use of strongly constrained types, including singleton types, i.e.
  types inhabited by single terms. They were later simplified and further
  developed to fit within the polymorphic (non-dependent) type systems.
  Together with an independent work at the time by Christoph Zenger
  <cite|IndexedTypes>, and an earlier work by Konstantin Läufer and Martin
  Odersky <cite|ExTyADTs>, these efforts are the origins of Generalized
  Algebraic Data Types.

  Hongwei Xi's <math|DML<around*|(|X|)>> is parameterized by a constraint
  domain <math|X>, and, like <name|InvarGenT>, the implementation includes
  linear arithmetics. We will discuss a small selection of type system rules
  and then the approach to type inference taken by the DML system. The reader
  should not expect to gain understanding of DML from this short exposition,
  in part because it is a complex system.

  <subsection|The Type System>

  Type judgments in <math|DML<around*|(|X|)>> have naturally a different form
  for patterns than for expressions. For pattern <math|p>, type
  <math|\<tau\>>, formula <math|\<varphi\>>, and environment assigning
  expression variables to types <math|\<Gamma\>>, we write
  <math|p\<downarrow\>\<tau\>\<vartriangleright\><around*|(|\<varphi\>;\<Gamma\>|)>>
  to mean that pattern <math|p>, when matched against an expression of type
  <math|\<tau\>>, allows us to type-check its corresponding branch in the
  context of an environment enriched by <math|\<Gamma\>> and under a
  constraint enriched by <math|\<varphi\>>. In our notation:
  <math|p\<downarrow\>\<tau\>\<longrightarrow\>\<exists\><wide|\<alpha\>|\<bar\>><around*|[|\<varphi\>|]>\<Gamma\>>.
  The fresh type variables <math|<wide|\<alpha\>|\<bar\>>> are in fact
  introduced inside <math|\<varphi\>> in <math|DML<around*|(|X|)>>. For
  expression <math|e>, type <math|\<tau\>>, formula <math|\<varphi\>>, type
  environment <math|\<Delta\>> assigning sorts to type variables, and
  environment <math|\<Gamma\>> assigning types to expression variables, we
  write <math|\<varphi\>;<no-break>\<Delta\>;<no-break>\<Gamma\>\<vdash\>e:<no-break>\<tau\>>
  to mean that expression <math|e> has type <math|\<tau\>> in the context of
  the environments <math|\<Delta\>,\<Gamma\>> and the constraint formula
  <math|\<varphi\>>. In our notation: <math|\<varphi\>;\<Gamma\>\<vdash\>e:\<tau\>>,
  because we discriminate the sorts of type variables by the names of the
  variables.

  One of the most interesting rules of <math|DML<around*|(|X|)>> connects
  these two forms of judgments:

  <\equation*>
    <frac|p\<downarrow\>\<tau\><rsub|1>\<vartriangleright\><around*|(|\<varphi\><rprime|'>;\<Gamma\><rprime|'>|)><with|mode|text|
    \ \ \ >\<varphi\>\<wedge\>\<varphi\><rprime|'>;\<Delta\>;\<Gamma\>\<Gamma\><rprime|'>\<vdash\>e:\<tau\>|\<varphi\>;\<Delta\>;\<Gamma\>\<vdash\>p\<Rightarrow\>e:\<tau\><rsub|1>\<Rightarrow\>\<tau\><rsub|2>>
  </equation*>

  The notation <math|\<tau\><rsub|1>\<Rightarrow\>\<tau\><rsub|2>> is used
  instead of a function type <math|\<tau\><rsub|1>\<rightarrow\>\<tau\><rsub|2>>
  to indicate an ``internal'' use of a pattern matching branch: it is always
  a part of a pattern matching syntactic construct. The premise
  <math|\<varphi\>\<wedge\>\<varphi\><rprime|'>;\<Delta\>;\<Gamma\>\<Gamma\><rprime|'>\<vdash\>e:\<tau\>>
  means that for type-checking the body of a pattern matching branch, we have
  available not only the pattern variables from <math|\<Gamma\><rprime|'>>,
  but also properties <math|\<varphi\><rprime|'>> of their types.

  Another interesting aspect of <math|DML<around*|(|X|)>> is the presence of
  both universal and existential types. Universal types are as in system F.
  Rules for existential types:

  <\equation*>
    <frac|\<varphi\>;\<Delta\>;\<Gamma\>\<vdash\>e:\<tau\><around*|[|\<alpha\>\<assign\>i|]><with|mode|text|
    \ \ \ >\<varphi\>\<vdash\>i:\<gamma\>|\<varphi\>;\<Delta\>;\<Gamma\>\<vdash\><around|\<langle\>|i<mid|\|>e|\<rangle\>>:\<exists\>\<alpha\>:\<gamma\>.\<tau\>><with|mode|text|
    \ introduction>
  </equation*>

  <\equation*>
    <frac|\<varphi\>;\<Delta\>;\<Gamma\>\<vdash\>e<rsub|1>:\<exists\>\<alpha\>:\<gamma\>.\<tau\><rsub|1><with|mode|text|
    \ \ \ >\<varphi\>\<wedge\>\<alpha\>:\<gamma\>;\<Gamma\><around*|{|x:\<tau\><rsub|1>|}>\<vdash\>e<rsub|2>:\<tau\><rsub|2>|\<varphi\>;\<Delta\>;\<Gamma\>\<vdash\><text|<with|font-shape|condensed|<strong|let>>>
    <around|\<langle\>|\<alpha\><mid|\|>x|\<rangle\>>=e<rsub|1>
    <text|<with|font-shape|condensed|<strong|in>>>
    e<rsub|2>:\<tau\><rsub|2>><with|mode|text| \ \ \ elimination>
  </equation*>

  where <math|\<gamma\>> is a sort in the multisorted logic of <math|X>. The
  <math|<around|\<langle\>|i<mid|\|>e|\<rangle\>>> construct pairs an
  expression <math|e> with a witness <math|i> for the existential type
  <math|\<exists\>\<alpha\>:\<gamma\>.\<tau\>>. In fact, the concrete
  language of DML does not have this construct. Rather, it is introduced by
  type inference, as discussed below.

  <subsection|Bidirectional Type Inference>

  To facilitate type inference for the concrete language of DML, the system
  is equipped with two mutually recursive kinds of judgements called
  <em|elaboration judgments>: the <em|synthesizing> judgment
  <math|\<varphi\>;\<Gamma\>\<vDash\>e\<uparrow\>\<tau\>\<Rightarrow\>e<rsup|\<ast\>>>,
  and the <em|checking> judgment <math|\<varphi\>;\<Gamma\>\<vDash\>e\<downarrow\>\<tau\>\<Rightarrow\>e<rsup|\<ast\>>>.
  The synthesizing judgments introduce fresh type variables when needed,
  which are solved from the constraints <math|\<varphi\>>. The types for
  lambda expressions and recursive definition expressions are not
  synthesized. To see the interaction between synthesizing and checking
  judgments, consider the rule for function application:

  <\equation*>
    <frac|\<varphi\>;\<Gamma\>\<vdash\>e<rsub|1>\<uparrow\>\<tau\><rsub|1>\<rightarrow\>\<tau\><rsub|2>\<Rightarrow\>e<rsub|1><rsup|\<ast\>><with|mode|text|
    \ \ \ >\<varphi\>;\<Gamma\>\<vdash\>e<rsub|2>\<downarrow\>\<tau\><rsub|1>\<Rightarrow\>e<rsub|2><rsup|\<ast\>>|\<varphi\>;\<Gamma\>\<vdash\>e<rsub|1>*e<rsub|2>\<uparrow\>\<tau\><rsub|2>\<Rightarrow\>e<rsub|1><rsup|\<ast\>>*e<rsub|2><rsup|\<ast\>>>
  </equation*>

  Since <math|\<tau\><rsub|1>> is synthesized as part of the function type by
  <math|\<varphi\>;\<Gamma\>\<vdash\>e<rsub|1>\<uparrow\>\<tau\><rsub|1>\<rightarrow\>\<tau\><rsub|2>\<Rightarrow\>e<rsub|1>>,
  subsequently it only needs to be checked for the argument <math|e<rsub|2>>.
  Synthesis for variables is done by referring to the environment, and for
  data constructors by referring to the respective datatype definition.
  Checking for variables and data constructors refers back to synthesis, and
  we employ constraint solving to decide whether the types agree:

  <\equation*>
    <frac|\<varphi\>;\<Gamma\>\<vdash\>x\<uparrow\>\<tau\><rsub|1>\<Rightarrow\>e<rsup|\<ast\>><with|mode|text|
    \ \ \ >\<varphi\>\<vDash\>\<tau\><rsub|1><wide|=|\<dot\>>\<tau\><rsub|2>|\<varphi\>;\<Gamma\>\<vdash\>x\<downarrow\>\<tau\><rsub|2>\<Rightarrow\>e<rsup|\<ast\>>>
  </equation*>

  With existential types, the situation is further complicated by the need to
  introduce, during elaboration, ``witnesses'' <math|i> into expressions of
  existential type. DML relies on a judgment <math|coerce>, whose one of most
  interesting rules is:

  <\equation*>
    <frac|\<varphi\>\<vdash\>coerce<around*|(|\<tau\><rsub|1>,\<tau\><around*|[|\<alpha\>\<assign\>i|]>|)>\<Rightarrow\>E<with|mode|text|
    \ \ \ >\<varphi\>\<vdash\>i:\<gamma\>|\<varphi\>\<vdash\>coerce<around*|(|\<tau\><rsub|1>,\<Sigma\><around*|(|\<alpha\>:\<gamma\>|)>.\<tau\>|)>\<Rightarrow\><around|\<langle\>|i<mid|\|>E|\<rangle\>>>
  </equation*>

  where we see existential witness introduced when an existential type is
  encountered. The <math|coerce> judgment is connected to synthesizing
  judgments via checking rules. Let us look at the other rule for function
  application:

  <\equation*>
    <frac|\<varphi\>;\<Gamma\>\<vdash\>e<rsub|1>*e<rsub|2>\<uparrow\>\<tau\><rsub|1>\<Rightarrow\>e<rsup|\<ast\>><with|mode|text|
    \ \ \ >\<varphi\>\<vdash\>coerce<around*|(|\<tau\><rsub|1>,\<tau\><rsub|2>|)>\<Rightarrow\>E|\<varphi\>;\<Gamma\>\<vdash\>e<rsub|1>*e<rsub|2>\<downarrow\>\<tau\><rsub|2>\<Rightarrow\>E<around*|[|e<rsup|\<ast\>>|]>>
  </equation*>

  where <math|E> is an expression context with a single hole.

  <subsection|Relevance>

  The work on <math|DML<around*|(|X|)>> is foundational to <name|InvarGenT>.
  While we chose to build on the more elegant formalism of
  <math|HMG<around*|(|X|)>>, we share some of the goals of DML, diverging on
  one:

  <\enumerate>
    <item>The formalism behind <name|InvarGenT> is parametrized by the domain
    of constraints, just as <math|DML<around*|(|X|)>>. The implementation
    handles linear arithmetic constraints, and can be extended to other
    domains, similarly to DML.

    <item>Both DML and <name|InvarGenT> place emphasis on the seamless use of
    existential types, aided by type inference. However, existential types
    are not synthesized by DML.

    <item>DML and <name|InvarGenT> share concern with covering a sufficient
    portion of ML-family language features, in particular pattern matching
    with deep patterns.

    <item>DML requires type annotations on all functions that cannot be typed
    in the Hindley-Milner type system. In exchange, <math|DML<around*|(|X|)>>
    has the principal type property and type inference in DML is efficient.
    <name|InvarGenT> takes the opposite stance, not requiring any type
    annotations.
  </enumerate>

  Unlike DML, <name|InvarGenT> does not currently support first-class
  universal types, i.e. function arguments which can be used polymorphically,
  with different types within a function. Introducing inferred universal
  types to <name|InvarGenT> is left as future work. The type inference for
  universal types of function arguments would work similarly to how type
  inference for recursive definitions (which admits polymorphic recursion)
  works currently.

  DML performs A-transformation, which is a source level transformation
  introducing <math|<text|<with|font-shape|condensed|<strong|let>>>> bindings
  for subexpressions. In this way, all occurrences of expressions with
  existential types are unpacked, with the existential type eliminated. In
  interests of type inference times, <name|InvarGenT> does not perform
  A-transformation. However, passing expressions of an existential type as
  arguments to functions is prohibited in <name|InvarGenT>'s type system,
  therefore A-transformation would be a conservative extension. This captures
  errors where the programmer forgets to unpack the existential type, without
  limiting expressivity.

  In <name|InvarGenT>, introductions of existential types need to be marked
  in the source by adding a single character to the corresponding concrete
  syntax keywords: <verbatim|function>, <verbatim|match> and <verbatim|if>.
  In DML, existential type introductions do not figure in the concrete
  syntax, but existential types need to be spelled out in type annotations.
  In <name|InvarGenT>, inference of existential types will find out how many
  existential parameters are needed, including the case when none are needed,
  i.e. the type is not in fact existential. Therefore, a more sophisticated
  approach might introduce existential types automatically, at cost of
  increased type inference times.

  <section|The <math|HMG<around*|(|X|)>> Formalization><label|HMGSection>

  In parallel to the development of DML, Martin Odersky, Martin Sulzmann and
  Martin Wehr in <cite|HMX> developed a general framework
  <math|HM<around*|(|X|)>> for expressing type systems extending the
  Hindley-Milner type system and parameterized by a constraint domain.
  Hongwei Xi and collaborators further developed the ideas behind DML into an
  extension of type systems for languages in the ML family -- Standard ML,
  Haskell, OCaml -- they originally called <em|Guarded Recursive Data Types>,
  see <cite|XiGRDTs>, later to become known as <em|Generalized Algebraic Data
  Types> or GADTs. GADTs were independently investigated at that time by
  James Cheney and Ralf Hinze as <em|first-class phantom types> in
  <cite|CheneyHinzePhantomTypes>, and by Tim Sheard as <em|equality qualified
  types> in <cite|Sheard04>. Vincent Simonet and François Pottier in
  <cite|simonet-pottier-hmg-toplas> brought these two lines of research,
  <math|HM<around*|(|X|)>> and GADTs, together, by designing an elegant type
  system <math|HMG<around*|(|X|)>>.

  <subsection|The Untyped Calculus>

  While the <em|indexed types> of Christoph Zenger <cite|IndexedTypes> and
  dependent types of DML refine ML but do not make more ML programs typeable,
  GADTs extend ML, i.e. make some programs typeable -- provided appropriate
  datatype definitions -- that would not type-check otherwise.

  We present the call-by-value <math|\<lambda\>>-calculus behind
  <math|HMG<around*|(|X|)>> since we will defer the semantics of
  <name|InvarGenT> to <math|HMG<around*|(|X|)>>. The rest of this section
  follows closely <cite|simonet-pottier-hmg-toplas>, starting with pages
  12-14.<\float|float|t>
    <\big-table>
      <\math>
        p\<assign\>x<space|0.6spc>\|<space|0.6spc>0<space|0.6spc>\|<space|0.6spc>1<space|0.6spc>\|<space|0.6spc>p\<wedge\>p<space|0.6spc>\|<space|0.6spc>p\<vee\>p<space|0.6spc>\|<space|0.6spc>K
        <wide|p|\<bar\>>

        c\<assign\>p.e

        e\<assign\>x<space|0.6spc>\|<space|0.6spc>K
        <wide|e|\<bar\>><space|0.6spc>\|<space|0.6spc><text|<with|font-shape|condensed|<strong|let>>>
        x=e <text|<with|font-shape|condensed|<strong|in>>>
        e<space|0.6spc>\|<space|0.6spc>e e<space|0.6spc>\|<space|0.6spc>\<lambda\><around*|(|<wide|c|\<bar\>>|)><space|0.6spc>\|<space|0.6spc>\<mu\>
        x.v

        v\<assign\>K <wide|v|\<bar\>><space|0.6spc>\|<space|0.6spc>\<lambda\><around*|(|<wide|c|\<bar\>>|)>
      </math>

      <label|CalcSynHMG>
    </big-table|Syntax of the calculus for <math|HMG<around*|(|X|)>>>
  </float>

  Let <math|x> and <math|K> range over disjoint denumerable sets of variables
  and data constructors, respectively. For every data constructor <math|K>,
  we assume a fixed nonnegative arity. The syntax of patterns, expressions,
  clauses, and values is given in Figure <reference|CalcSynHMG>. Patterns
  include the empty pattern <math|0>, the wildcard pattern <math|1>,
  variables, conjunction and disjunction patterns, and data constructor
  applications. Defined program variables <math|dpv<around*|(|p|)>> are the
  unique variables in <math|p>. The pattern <math|p> is considered ill-formed
  for nonlinear patterns (i.e. patterns with repeating variables).
  Expressions include variables, functions, data constructor or function
  applications, recursive definitions, and local variable definitions.
  Functions are defined by cases: a <math|\<lambda\>>-abstraction, written
  <math|\<lambda\><around*|(|c<rsub|1>,\<ldots\>,c<rsub|n>|)>>, consists of a
  sequence of clauses. A clause <math|c> is made up of a pattern <math|p> and
  an expression <math|e> and is written <math|p.e>; the variables in
  <math|dpv<around*|(|p|)>> are bound within <math|e>. We occasionally use
  <math|ce> to stand for a clause or an expression. Values include functions
  and applications of a data constructor to values. Within patterns,
  expressions, and values, all applications of a data constructor must
  respect its arity: data constructors cannot be partially
  applied.<\float|float|t>
    <\big-table>
      <\eqnarray*>
        <tformat|<table|<row|<cell|<around*|[|0\<assign\>v|]>>|<cell|=>|<cell|<with|mode|text|undefined>>>|<row|<cell|<around*|[|1\<assign\>v|]>>|<cell|=>|<cell|\<varnothing\>>>|<row|<cell|<around*|[|p<rsub|1>\<wedge\>p<rsub|2>\<assign\>v|]>>|<cell|=>|<cell|<around*|[|p<rsub|1>\<assign\>v|]>\<otimes\><around*|[|p<rsub|2>\<assign\>v|]>>>|<row|<cell|<around*|[|p<rsub|1>\<vee\>p<rsub|2>\<assign\>v|]>>|<cell|=>|<cell|<around*|[|p<rsub|1>\<assign\>v|]>\<oplus\><around*|[|p<rsub|2>\<assign\>v|]>>>|<row|<cell|<around*|[|K
        p<rsub|1>\<cdots\>p<rsub|n>\<assign\>K
        v<rsub|1>\<cdots\>v<rsub|n>|]>>|<cell|=>|<cell|<around*|[|p<rsub|1>\<assign\>v<rsub|1>|]>\<otimes\>\<cdots\>\<otimes\><around*|[|p<rsub|n>\<assign\>v<rsub|n>|]>>>>>
      </eqnarray*>

      <label|SubstHMG>
    </big-table|Extended substitution for <math|HMG<around*|(|X|)>>>
  </float>

  Whether a pattern <math|p> matches a value <math|v> is defined by an
  extended substitution <math|<around*|[|p\<assign\>v|]>> that is either
  undefined, which means that <math|p> does not match <math|v>, or a mapping
  of <math|dpv<around*|(|p|)>> to values, which means that <math|p> does
  match <math|v> and describes how its variables become bound. Of course,
  when <math|p> is a variable <math|x>, the extended substitution
  <math|<around*|[|x\<assign\>v|]>> coincides with the ordinary substitution
  <math|<around*|[|x\<assign\>v|]>>, which justifies our abuse of notation.
  Extended substitution for other pattern forms is defined in Figure
  <reference|SubstHMG>. Let us briefly review the definition. The pattern
  <math|0> matches no value, so <math|<around*|[|0\<assign\>v|]>> is always
  undefined. Conversely, the pattern <math|1> matches every value, but binds
  no variables, so <math|<around*|[|1\<assign\>v|]>> is the empty
  substitution. In the case of conjunction patterns, <math|\<otimes\>> stands
  for (disjoint) set-theoretic union, so that the bindings produced by
  <math|p<rsub|1>\<wedge\>p<rsub|2>> are the union of those independently
  produced by <math|p<rsub|1>> and <math|p<rsub|2>>. The operator
  <math|\<otimes\>> is strict\Vthat is, its result is undefined if either of
  its operands is undefined\Vwhich means that a conjunction pattern matches a
  value if and only if both of its members do. In the case of disjunction
  patterns, <math|\<oplus\>> stands for a nonstrict, angelic choice operator
  with left bias: when <math|o<rsub|1>> and <math|o<rsub|2>> are two possibly
  undefined mathematical objects that belong to the same space when defined,
  <math|o<rsub|1>\<oplus\>o<rsub|2>> stands for <math|o<rsub|1>> if it is
  defined and for <math|o<rsub|2>> otherwise. As a result, a disjunction
  pattern matches a value if and only if either of its members does. The set
  of bindings thus produced is that produced by <math|p<rsub|1>>, if defined,
  otherwise that produced by <math|p<rsub|2>>. Last, the pattern <math|K
  p<rsub|1>\<cdots\>p<rsub|n>> matches values of the form <math|K
  v<rsub|1>\<cdots\>v<rsub|n>> only; it matches such a value if and only if
  <math|p<rsub|i>> matches <math|v<rsub|i>> for every
  <math|i\<in\><around*|{|1,\<ldots\>,n|}>>.<\float|float|t>
    <\big-table>
      <\eqnarray*>
        <tformat|<table|<row|<cell|\<lambda\><around*|(|p<rsub|1>.e<rsub|1>\<cdots\>p<rsub|n>.e<rsub|n>|)>
        v>|<cell|\<rightarrow\>>|<cell|<big|oplus><rsub|i=1><rsup|n>e<rsub|i><around*|[|p<rsub|i>\<assign\>v|]>>>|<row|<cell|\<mu\>
        x.v>|<cell|\<rightarrow\>>|<cell|v<around*|[|x\<assign\>\<mu\>
        x.v|]>>>|<row|<cell|<text|<with|font-shape|condensed|<strong|let>>>
        x=v <text|<with|font-shape|condensed|<strong|in>>>
        e>|<cell|\<rightarrow\>>|<cell|e<around*|[|x\<assign\>v|]>>>|<row|<cell|E<around*|[|e|]>>|<cell|\<rightarrow\>>|<cell|E<around*|[|e<rprime|'>|]><text|
        \ if \ >e\<rightarrow\>e<rprime|'>>>|<row|<cell|>|<cell|>|<cell|>>|<row|<cell|E>|<cell|\<assign\>>|<cell|K
        <wide|v|\<bar\>> <around*|[||]> <wide|e|\<bar\>><space|0.6spc>\|<space|0.6spc><around*|[||]>
        e<space|0.6spc>\|<space|0.6spc>v <around*|[||]><space|0.6spc>\|<space|0.6spc><text|<with|font-shape|condensed|<strong|let>>>
        x=<around*|[||]> <text|<with|font-shape|condensed|<strong|in>>> e>>>>
      </eqnarray*>

      <label|SemantHMG>
    </big-table|Operational semantics for <math|HMG<around*|(|X|)>>>
  </float>

  The call-by-value small-step semantics, written <math|\<rightarrow\>>, is
  defined by the rules of Figure <reference|SemantHMG>. It is standard. The
  first rule governs function application and pattern-matching:
  <math|\<lambda\><around*|(|p<rsub|1>.e<rsub|1>\<cdots\>p<rsub|n>.e<rsub|n>|)>>
  reduces to <math|e<rsub|i><around*|[|p<rsub|i>\<assign\>v<rsub|i>|]>>,
  where <math|i> is the least element of <math|<around*|{|1,\<ldots\>,n|}>>
  such that <math|p<rsub|i>> matches <math|v>. Note that this expression is
  stuck (does not reduce) when no such <math|i> exists. The last rule lifts
  reduction to arbitrary evaluation contexts.

  <subsection|The <math|HMG<around*|(|X|)>> Type System>

  <math|HMG<around*|(|X|)>> supports subtyping. The language of constraints
  is as follows:

  <\eqnarray*>
    <tformat|<table|<row|<cell|\<tau\>>|<cell|\<assign\>>|<cell|\<alpha\><space|0.6spc>\|<space|0.6spc>\<tau\>\<rightarrow\>\<tau\><space|0.6spc>\|<space|0.6spc>\<varepsilon\><around*|(|\<tau\>,\<ldots\>,\<tau\>|)>>>|<row|<cell|\<pi\>>|<cell|\<assign\>>|<cell|\<preccurlyeq\><space|0.6spc>\|<space|0.6spc>\<ldots\>>>|<row|<cell|C,D>|<cell|\<assign\>>|<cell|\<pi\>
    <wide|\<tau\>|\<bar\>><space|0.6spc>\|<space|0.6spc>C\<wedge\>C<space|0.6spc>\|<space|0.6spc>C\<vee\>C<space|0.6spc>\|<space|0.6spc>\<exists\>\<alpha\>.C<space|0.6spc>\|<space|0.6spc>\<forall\>\<alpha\>.C<space|0.6spc>\|<space|0.6spc>C\<Rightarrow\>C>>>>
  </eqnarray*>

  where <math|\<tau\>> are types, <math|\<pi\>> are constraint relations and
  <math|\<preccurlyeq\>> is a subtyping relation, <math|C,D> are constraint
  formulas. Environments <math|\<Gamma\>> assign variables to type schemes,
  e.g. <math|<around*|{|x\<mapsto\>\<sigma\>|}>>, where type schemes are
  triples:

  <\equation*>
    \<sigma\>\<assign\>\<forall\><wide|\<alpha\>|\<bar\>><around*|[|C|]>.\<tau\>
  </equation*>

  indicating a value of type <math|\<tau\>> polymorphic wrt. variables
  <math|<wide|\<alpha\>|\<bar\>>>, constrained by formula <math|C>. A novel
  concept is that of an <em|environment fragment>, a triple:

  <\equation*>
    \<Delta\>\<assign\>\<exists\><wide|\<beta\>|\<bar\>><around*|[|D|]>\<Gamma\>
  </equation*>

  where <math|\<Gamma\>> is a <em|simple environment> which assigns variables
  to types (not type schemes). Environment fragments are used to describe the
  static knowledge that is gained by successfully matching a value against a
  pattern. We write <math|\<exists\><wide|\<alpha\>|\<bar\>><around*|[|C|]>\<Delta\>>
  for <math|\<exists\><wide|\<alpha\>|\<bar\>><wide|\<beta\>|\<bar\>><around*|[|C\<wedge\>D|]>\<Gamma\>>,
  and <math|\<Delta\><rsub|1>\<times\>\<Delta\><rsub|2>> for:

  <\equation*>
    \<exists\><wide|\<beta\>|\<bar\>><rsub|1><wide|\<beta\>|\<bar\>><rsub|2><around*|[|D<rsub|1>\<wedge\>D<rsub|2>|]><around*|(|\<Gamma\><rsub|1>\<cup\>\<Gamma\><rsub|2>|)>
  </equation*>

  Structures in which types can be interpreted have to meet three
  requirements, see <cite|simonet-pottier-hmg-toplas> pages 18-19, of which
  we give two. Every constraint of the form
  <math|\<tau\><rsub|1>\<rightarrow\>\<tau\><rsub|2>\<preccurlyeq\>\<varepsilon\><around*|(|<wide|\<tau\>|\<bar\>>|)>>
  or <math|\<varepsilon\><around*|(|<wide|\<tau\>|\<bar\>>|)>\<preccurlyeq\>\<tau\><rsub|1>\<rightarrow\>\<tau\><rsub|2>>
  or <math|\<varepsilon\><around*|(|<wide|\<tau\>|\<bar\>>|)>\<preccurlyeq\>\<varepsilon\><rprime|'><around*|(|<wide|\<tau\>|\<bar\>><rprime|'>|)>>
  for <math|\<varepsilon\>\<neq\>\<varepsilon\><rprime|'>>, is unsatisfiable.
  <math|\<tau\><rsub|1>\<rightarrow\>\<tau\><rsub|2>\<preccurlyeq\>\<tau\><rsub|1><rprime|'>\<rightarrow\>\<tau\><rsub|2><rprime|'>>
  entails <math|\<tau\><rsub|1><rprime|'>\<preccurlyeq\>\<tau\><rsub|1>\<wedge\>\<tau\><rsub|2>\<preccurlyeq\>\<tau\><rsub|2><rprime|'>>.

  Judgments about expressions retain the same form as in
  <math|HM<around*|(|X|)>>: they are written
  <math|C,<no-break>\<Gamma\>\<vdash\>e:\<sigma\>>, where <math|C> represents
  an assumption about the judgment's free type variables, <math|\<Gamma\>>
  assigns type schemes to variables, and <math|\<sigma\>> is the type scheme
  assigned to <math|e>.

  Judgments about patterns are written <math|C\<vdash\>p:\<tau\>\<rightsquigarrow\>\<exists\><wide|\<beta\>|\<bar\>><around*|[|D|]>\<Gamma\>>,
  where the domain of <math|\<Gamma\>> is <math|dpv<around*|(|p|)>>. Such a
  judgment can be read: under assumption <math|C>, it is legal to match a
  value of type <math|\<tau\>> against <math|p>; furthermore, if successful,
  this test guarantees that there exist types <math|<wide|\<beta\>|\<bar\>>>
  that satisfy <math|D> such that <math|\<Gamma\>> is a valid description of
  the values that the variables in <math|dpv<around*|(|p|)>> receive.
  <math|D> carries the information unpacked from guarded data constructors
  <math|K>:

  <\equation*>
    <frac|\<forall\>i<with|mode|text| \ \ >C\<wedge\>D\<vdash\>p<rsub|i>:\<tau\><rsub|i>\<rightsquigarrow\>\<Delta\><rsub|i><with|mode|text|
    \ \ \ >K\<colons\>\<forall\><wide|\<alpha\>|\<bar\>><wide|\<beta\>|\<bar\>><around*|[|D|]>.\<tau\><rsub|1>\<times\>\<cdots\>\<times\>\<tau\><rsub|n>\<rightarrow\>\<varepsilon\><around*|(|<wide|\<alpha\>|\<bar\>>|)><with|mode|text|
    \ \ \ ><wide|\<beta\>|\<bar\>>#FV<around*|(|C|)>|C\<vdash\>K
    p<rsub|1>\<cdots\>p<rsub|n>:\<varepsilon\><around*|(|<wide|\<alpha\>|\<bar\>>|)>\<rightsquigarrow\>\<exists\><wide|\<beta\>|\<bar\>><around*|[|D|]><around*|(|\<Delta\><rsub|1>\<times\>\<cdots\>\<times\>\<Delta\><rsub|n>|)>>
  </equation*>

  Subsequently, the unpacked information is available when type-checking the
  expression in the corresponding branch:

  <\equation>
    <frac|C\<vdash\>p:\<tau\><rprime|'>\<rightsquigarrow\>\<exists\><wide|\<beta\>|\<bar\>><around*|[|D|]>\<Gamma\><rprime|'><with|mode|text|
    \ \ \ >C\<wedge\>D,\<Gamma\>\<Gamma\><rprime|'>\<vdash\>e:\<tau\><with|mode|text|
    \ \ \ ><wide|\<beta\>|\<bar\>>#FV<around*|(|C,\<Gamma\>,\<tau\>|)>|C,\<Gamma\>\<vdash\>p.e:\<tau\><rprime|'>\<rightarrow\>\<tau\>><label|HMGClauseRule>
  </equation>

  The type judgments involving clauses are used to derive types of
  <math|\<lambda\>>-abstractions, i.e. anonymous functions defined by cases:

  <\equation*>
    <frac|\<forall\>i<with|mode|text| \ \ >C,\<Gamma\>\<vdash\>c<rsub|i>:\<tau\>|C,\<Gamma\>\<vdash\>\<lambda\><around*|(|c<rsub|1>\<cdots\>c<rsub|n>|)>:\<tau\>>
  </equation*>

  where <math|\<tau\>> is always of the form
  <math|\<tau\><rsub|1>\<rightarrow\>\<tau\><rsub|2>>.

  Let us look at a selection of remaining rules. Patterns in a disjunction
  need to agree on the information they bring about:

  <\equation*>
    <frac|\<forall\>i<with|mode|text| \ \ >C\<vdash\>p<rsub|i>:\<tau\>\<rightsquigarrow\>\<Delta\>|C\<vdash\>p<rsub|1>\<vee\>p<rsub|2>:\<tau\>\<rightsquigarrow\>\<Delta\>>
  </equation*>

  However, we can make them agree by discarding irrelevant information:

  <\equation*>
    <frac|C\<vdash\>p:\<tau\>\<rightsquigarrow\>\<Delta\><rprime|'><with|mode|text|
    \ \ \ >C\<Vdash\>\<Delta\><rprime|'>\<leqslant\>\<Delta\>|C\<vdash\>p:\<tau\>\<rightsquigarrow\>\<Delta\>>
  </equation*>

  where <math|C\<Vdash\>\<Delta\><rprime|'>\<leqslant\>\<Delta\>> is defined
  in terms of interpreting environment fragments as sets of ground
  environments. Fortunately, we can equivalently define
  <math|C\<Vdash\>\<Delta\><rprime|'>\<leqslant\>\<Delta\>> as
  <math|C\<wedge\>D<rprime|'>\<Vdash\>\<exists\><wide|\<beta\>|\<bar\>>.D\<wedge\>\<Gamma\><rprime|'>\<preccurlyeq\>\<Gamma\>>,
  where <math|\<Gamma\><rprime|'>\<preccurlyeq\>\<Gamma\>> is a shorthand for
  <math|Dom<around*|(|\<Gamma\><rprime|'>|)>=Dom<around*|(|\<Gamma\>|)>\<wedge\><rsub|x\<in\>Dom<around*|(|\<Gamma\><rprime|'>|)>>\<Gamma\><rprime|'><around*|(|x|)>\<preccurlyeq\>\<Gamma\><around*|(|x|)>>
  and <math|\<Delta\>=\<exists\><wide|\<beta\>|\<bar\>><around*|[|D|]>\<Gamma\>>,
  <math|\<Delta\><rprime|'>=\<exists\><wide|\<beta\><rprime|'>|\<bar\>><around*|[|D<rprime|'>|]>\<Gamma\><rprime|'>>.
  Note that <math|C\<Vdash\>D> is defined as
  <math|\<vDash\>C\<Rightarrow\>D>, i.e. holding in the model, rather than
  <math|\<vdash\>C\<Rightarrow\>D>, i.e. provability.

  To construct a value of a GADT, we need to check that the guard, or
  invariant, holds:

  <\equation*>
    <frac|\<forall\>i<with|mode|text| \ \ >C,\<Gamma\>\<vdash\>e<rsub|i>:\<tau\><rsub|i><with|mode|text|
    \ \ \ >K\<colons\>\<forall\><wide|\<alpha\>|\<bar\>><wide|\<beta\>|\<bar\>><around*|[|D|]>.\<tau\><rsub|1>\<cdots\>\<tau\><rsub|n>\<rightarrow\>\<varepsilon\><around*|(|<wide|\<alpha\>|\<bar\>>|)><with|mode|text|
    \ \ \ >C\<Vdash\>D|C,\<Gamma\>\<vdash\>K
    e<rsub|1>\<cdots\>e<rsub|n>:\<varepsilon\><around*|(|<wide|\<alpha\>|\<bar\>>|)>>
  </equation*>

  The use of a variable is type-checked in the same manner, the variable is
  looked up in the environment <math|\<Gamma\>>. The following rule can be
  derived in <math|HMG<around*|(|X|)>> and is a bit more clear than the
  original:

  <\equation>
    <frac|\<Gamma\><around*|(|x|)>=\<forall\><wide|\<alpha\>|\<bar\>><around*|[|D|]>.\<tau\><with|mode|text|
    \ \ >C\<Vdash\>\<exists\><wide|\<alpha\>|\<bar\>>.D|C,\<Gamma\>\<vdash\>x:\<tau\>><label|HMGVarRule>
  </equation>

  The rule for recursive definition is initially given in the Milner-Mycroft
  style to simplify proofs related to semantics rather than type inference:

  <\equation*>
    <frac|C,\<Gamma\><around*|{|x\<mapsto\>\<sigma\>|}>\<vdash\>v:\<sigma\>|C,\<Gamma\>\<vdash\>\<mu\>
    x.v:\<sigma\>>
  </equation*>

  A <math|v> instead of an <math|e> is used to prevent diverging definitions.
  The final form of <math|HMG<around*|(|X|)>>, as employed in proofs of
  equivalence with the constraint derivation-based presentation, enforces the
  type annotation: <math|e\<assign\>\<ldots\><space|0.6spc>\|<space|0.6spc>\<mu\>
  <around*|(|x:\<exists\><wide|\<beta\>|\<bar\>>.\<sigma\>|)>.v>, where
  <math|ftv<around*|(|\<sigma\>|)>\<subseteq\><wide|\<beta\>|\<bar\>>>.

  A closed (i.e. without unbound variables) expression <math|e> is
  <em|well-typed> if and only if <math|C,\<varnothing\>\<vdash\>e:\<sigma\>>
  holds for some satisfiable constraint <math|C>. We have the following type
  soundness results:

  <\theorem>
    <em|(Subject reduction).> <math|C,\<varnothing\>\<vdash\>e:\<sigma\>> and
    <math|e\<rightarrow\>e<rprime|'>> imply
    <math|C,\<varnothing\>\<vdash\>e<rprime|'>:\<sigma\>>.
  </theorem>

  <\theorem>
    <em|(Progress).> If <math|e> is well-typed and contains exhaustive case
    analyses only, then it is either reducible or a value.
  </theorem>

  <\theorem>
    <em|(Type soundness).> If <math|e> is well-typed and contains exhaustive
    case analyses only, then it does not reduce to a stuck
    expression.<label|HMGSoundness>
  </theorem>

  <subsection|Constraint Derivation>

  The type inference for <math|HMG<around*|(|X|)>>, as well as for
  <name|InvarGenT>, starts by generating a constraint for an expression,
  whose satisfiability determines whether the expression is well-typed. The
  rules, or equations, for deriving the constraints form an alternative
  specification of the type system. Both specifications are readable, the
  specification by constraint derivation is actually more concise. As with
  the type system rules, we have constraint derivation equations for
  patterns, expressions, and pattern matching clauses.

  The constraint <math|<around*|\<llbracket\>|p\<downarrow\>\<tau\>|\<rrbracket\>>>
  asserts that it is legal to match a value of type <math|\<tau\>> against
  <math|p>, while the environment fragment
  <math|<around*|\<llbracket\>|p\<uparrow\>\<tau\>|\<rrbracket\>>> represents
  knowledge about the bindings that arise when such a test succeeds. (Note
  that our use of <math|\<downarrow\>> and <math|\<uparrow\>> has nothing to
  do with bidirectional type inference.) The rules for
  <math|<around*|\<llbracket\>|p\<downarrow\>\<tau\>|\<rrbracket\>>> and
  <math|<around*|\<llbracket\>|p\<uparrow\>\<tau\>|\<rrbracket\>>> are the
  same in <name|InvarGenT> as in <math|HMG<around*|(|X|)>>. They are
  described in <cite|simonet-pottier-hmg-toplas> on pages
  32-33.<\float|float|t>
    <\big-table>
      <\eqnarray*>
        <tformat|<table|<row|<cell|<around*|\<llbracket\>|\<Gamma\>\<vdash\>x:\<tau\>|\<rrbracket\>>>|<cell|=>|<cell|\<Gamma\><around*|(|x|)>\<preccurlyeq\>\<tau\>>>|<row|<cell|>|<cell|>|<cell|>>|<row|<cell|<around*|\<llbracket\>|\<Gamma\>\<vdash\>\<lambda\><wide|c|\<bar\>>:\<tau\>|\<rrbracket\>>>|<cell|=>|<cell|\<exists\>\<alpha\><rsub|1>\<alpha\><rsub|2>.\<wedge\><rsub|c><around*|\<llbracket\>|\<Gamma\>\<vdash\>c:\<alpha\><rsub|1>\<rightarrow\>\<alpha\><rsub|2>|\<rrbracket\>>\<wedge\>\<alpha\><rsub|1>\<rightarrow\>\<alpha\><rsub|2>\<preccurlyeq\>\<tau\>>>|<row|<cell|>|<cell|>|<cell|>>|<row|<cell|<around*|\<llbracket\>|\<Gamma\>\<vdash\>e<rsub|1>
        e<rsub|2>:\<tau\>|\<rrbracket\>>>|<cell|=>|<cell|\<exists\>\<alpha\>.<around*|\<llbracket\>|\<Gamma\>\<vdash\>e<rsub|1>:\<alpha\>\<rightarrow\>\<tau\>|\<rrbracket\>>\<wedge\><around*|\<llbracket\>|e<rsub|2>:\<alpha\>|\<rrbracket\>>>>|<row|<cell|>|<cell|>|<cell|>>|<row|<cell|<around*|\<llbracket\>|K
        e<rsub|1>\<cdots\>e<rsub|n>:\<tau\>|\<rrbracket\>>>|<cell|=>|<cell|\<exists\><wide|\<alpha\>|\<bar\>><wide|\<beta\>|\<bar\>>.\<wedge\><rsub|i><around*|\<llbracket\>|\<Gamma\>\<vdash\>e<rsub|i>:\<tau\><rsub|i>|\<rrbracket\>>\<wedge\>D\<wedge\>\<varepsilon\><around*|(|<wide|\<alpha\>|\<bar\>>|)>\<preccurlyeq\>\<tau\>>>|<row|<cell|>|<cell|>|<cell|<with|mode|text|where
        >K\<colons\>\<forall\><wide|\<alpha\>|\<bar\>><wide|\<beta\>|\<bar\>><around*|[|D|]>.\<tau\><rsub|1>\<times\>\<cdots\>\<times\>\<tau\><rsub|n>\<rightarrow\>\<varepsilon\><around*|(|<wide|\<alpha\>|\<bar\>>|)>>>|<row|<cell|>|<cell|>|<cell|>>|<row|<cell|<around*|\<llbracket\>|\<Gamma\>\<vdash\>\<mu\><around*|(|x:\<exists\><wide|\<beta\>|\<bar\>>.\<sigma\>|)>.e:\<tau\>|\<rrbracket\>>>|<cell|=>|<cell|\<exists\><wide|\<beta\>|\<bar\>>.<around*|\<llbracket\>|\<Gamma\><around*|{|x\<mapsto\>\<sigma\>|}>\<vdash\>e:\<sigma\>|\<rrbracket\>>\<wedge\>\<sigma\>\<preccurlyeq\>\<tau\>>>|<row|<cell|>|<cell|>|<cell|>>|<row|<cell|<around*|\<llbracket\>|\<Gamma\>\<vdash\>e:\<forall\><wide|\<gamma\>|\<bar\>><around*|[|C|]>.\<tau\>|\<rrbracket\>>>|<cell|=>|<cell|\<forall\><wide|\<gamma\>|\<bar\>>.C\<Rightarrow\><around*|\<llbracket\>|\<Gamma\>\<vdash\>e:\<tau\>|\<rrbracket\>>>>|<row|<cell|>|<cell|>|<cell|>>|<row|<cell|<around*|\<llbracket\>|<text|<with|font-shape|condensed|<strong|let>>>
        x=e<rsub|1> <text|<with|font-shape|condensed|<strong|in>>>
        e<rsub|2>:\<tau\>|\<rrbracket\>>>|<cell|=>|<cell|<around*|\<llbracket\>|\<Gamma\><around*|{|x\<mapsto\>\<forall\>\<alpha\><around*|[|C|]>.\<alpha\>|}>\<vdash\>e<rsub|2>:\<tau\>|\<rrbracket\>>\<wedge\>\<exists\>\<alpha\>.C>>|<row|<cell|>|<cell|>|<cell|<with|mode|text|where
        >C<with|mode|text| is ><around*|\<llbracket\>|\<Gamma\>\<vdash\>e<rsub|1>:\<alpha\>|\<rrbracket\>>>>|<row|<cell|>|<cell|>|<cell|>>|<row|<cell|<around*|\<llbracket\>|\<Gamma\>\<vdash\>p.e:\<tau\><rsub|1>\<rightarrow\>\<tau\><rsub|2>|\<rrbracket\>>>|<cell|=>|<cell|<around*|\<llbracket\>|p\<downarrow\>\<tau\><rsub|1>|\<rrbracket\>>\<wedge\>\<forall\><wide|\<beta\>|\<bar\>>.D\<Rightarrow\><around*|\<llbracket\>|\<Gamma\>\<Gamma\><rprime|'>\<vdash\>e:\<tau\><rsub|2>|\<rrbracket\>>>>|<row|<cell|>|<cell|>|<cell|<with|mode|text|where
        >\<exists\><wide|\<beta\>|\<bar\>><around*|[|D|]>\<Gamma\><rprime|'><with|mode|text|
        is ><around*|\<llbracket\>|p\<uparrow\>\<tau\><rsub|1>|\<rrbracket\>>>>>>
      </eqnarray*>

      <label|CnDerivHMG>
    </big-table|Constraint derivation for <math|HMG<around*|(|X|)>>:
    expressions and clauses>
  </float>

  We provide the <math|HMG<around*|(|X|)>> constraint derivation rules for
  expressions and clauses in full in Table <reference|CnDerivHMG>, because
  they are analogous to those in <name|InvarGenT>, but more concise. The
  novelty of <math|HMG<around*|(|X|)>> compared to <math|HM<around*|(|X|)>>
  resides in the last rule, which deals with clauses. The following
  description comes from <cite|simonet-pottier-hmg-toplas> page 35. First,
  the function's domain type is required to match the pattern's type, via the
  constraint <math|<around*|\<llbracket\>|p\<downarrow\>\<tau\><rsub|1>|\<rrbracket\>>>.
  Then, the clause's right-hand side <math|e> is required to have type
  <math|\<tau\><rsub|2>> under a context extended with new abstract types
  <math|<wide|\<beta\>|\<bar\>>> and a new typing hypothesis <math|D> and
  under an extended environment <math|\<Gamma\>>, all three of which are
  obtained by evaluating <math|<around*|\<llbracket\>|p\<uparrow\>\<tau\><rsub|1>|\<rrbracket\>>>.

  <subsection|Relevance>

  The specification of the type system in terms of constraints can be seen as
  even more declarative than the specification by natural deduction rules.
  Instead of requiring that the reader builds understanding by analysing the
  possible derivations, the constraint derivation rules reduce the meaning of
  type judgments to that of formulas, whose semantics is already known.

  There are three major differences between <math|HMG<around*|(|X|)>> and
  <name|InvarGenT>. To simplify the already daunting task, <name|InvarGenT>
  does not support subtyping. Recursive definitions do not carry type
  annotations -- we perform type inference for polymorphic recursion. The
  third difference is the requirement in <name|InvarGenT> that the guards, or
  invariants, in type schemes and in value constructor definitions are
  existentially quantified conjunctions of atoms rather than arbitrary
  formulas. This is necessary to limit the space of candidate solutions to
  predicate variables in the task of synthesizing types and invariants of
  recursive definitions. But the restriction is also motivated by the need
  that the invariants be readily understandable to the programmer. Logically
  complex formulas, especially involving implications, are likely to not be
  sufficiently self-explanatory.

  As a consequence of restricting type scheme invariants to conjunctive
  formulas, we cannot use the approach from Table <reference|CnDerivHMG> to
  let-polymorphism. Instead, we perform ``division of labor'': we have
  monomorphic bindings with a pattern on the left-hand-side
  <math|<text|<with|font-shape|condensed|<strong|let>>> p=e
  <text|<with|font-shape|condensed|<strong|in>>> e>, and polymorphic
  bindings, possibly recursive <math|<text|<with|font-shape|condensed|<strong|let
  rec>>> x=e <text|<with|font-shape|condensed|<strong|in>>> e>.

  <section|The <math|OutsideIn<around*|(|X|)>>
  System><label|OutsideInSection>

  The design of the Schrijvers, Peyton Jones, Sulzmann<localize| and
  >Vytiniotis <math|OutsideIn<around*|(|X|)>> <cite|OutsideIn> type system is
  a follow-up to the <name|OutsideIn> algorithm from
  <cite|ComplDecidableGADTs> in a broader context parameterized by a
  constraint logic. The type judgments in <math|OutsideIn<around*|(|X|)>> are
  similar to <math|HMG<around*|(|X|)>>. <math|C,\<Gamma\>\<vdash\>e:\<tau\>>
  means that in a context where the constraint <math|C> is available, and in
  type environment <math|\<Gamma\>>, the term <math|e> has type
  <math|\<tau\>>. The important difference is that <math|C> is a conjunction
  of atoms rather than an arbitrary formula. Therefore, we cannot formulate
  an alternative, constraint derivation based specification of the type
  system, with the elegant connection expressed by results like Theorem
  <reference|InfCorrExpr>. Another difference between
  <math|OutsideIn<around*|(|X|)>> and <math|HMG<around*|(|X|)>> is that
  <math|OutsideIn<around*|(|X|)>> is defined against a background of a proof
  system for checking satisfiability of formulas rather than against an
  abstract model. The relevance is that having a model gives more flexibility
  for the implementer of type inference, while having a proof system (i.e. a
  logic) gives more flexibility for the designer of the type system. The
  third, related difference is that <math|OutsideIn<around*|(|X|)>> uses
  quantifiers sparingly. Instead, it introduces a distinction into
  <em|skolem> type variables and <em|unification> type variables.

  <math|OutsideIn<around*|(|X|)>> has rules for type checking programs as
  well as single expressions. Notably, the rule for un-annotated bindings
  makes use of abduction:

  <\equation*>
    <frac|C<rsub|1>,\<Gamma\>\<vdash\>e:\<tau\><with|mode|text|
    \ \ \ ><wide|\<alpha\>|\<bar\>>=FV<around*|(|C,\<tau\>|)><with|mode|text|
    \ \ \ >\<cal-C\>\<wedge\>C\<Vdash\>C<rsub|1><with|mode|text|
    \ \ \ >\<cal-C\>,\<Gamma\><around*|{|f\<mapsto\>\<forall\><wide|\<alpha\>|\<bar\>><around*|[|C|]>.\<tau\>|}>\<vdash\>prog|<with|mode|text|
    \ \ \ >\<cal-C\>,\<Gamma\>\<vdash\>f=e,prog>
  </equation*>

  We determine the constraint <math|C<rsub|1>> which is required to make e
  typeable with type <math|\<tau\>> in <math|\<Gamma\>>. Next, we allow the
  invariant of <math|f> be a simplified version of <math|C<rsub|1>>, namely
  <math|C>. Intuitively, <math|C> is the \Pextra information\Q, not deducible
  from <math|\<cal-C\>>, that is needed to show the required constraint
  <math|C<rsub|1>> (see <cite|OutsideIn> page 15). In our terms, <math|C> is
  an answer to an abduction problem <math|\<cal-C\>\<Rightarrow\>C<rsub|1>>.

  Constraint generation in <math|OutsideIn<around*|(|X|)>> is similar to that
  in <math|HMG<around*|(|X|)>>, but the formulation is less concise, and the
  generated constraint does not have alternating quantifiers. In our opinion,
  it makes the semantics of the constraints less clear. The constraints are
  also more restrictive than if quantifier scope was used to determine which
  solutions are consistent, even for programs without type families or GADTs.

  <subsection|Type Inference>

  <cite|OutsideIn> page 20 defines a <em|sound solution>, which is equivalent
  to our notion of an answer to a simple abduction problem, and a
  <em|guess-free solution>, which is equivalent to our notion of a fully
  maximal answer to a simple abduction problem. Type inference in
  <math|OutsideIn<around*|(|X|)>> uses a solver of simple abduction problems,
  but the abduction answers are not allowed to participate in the inferred
  types. Instead, for type inference to succeed, the abduction answers to
  implications have to be limited to substitutions of local variables, which
  are subsequently ignored.

  To make the exposition more concrete, we rewrite the solver infrastructure
  specification from <cite|OutsideIn> page 41. Let
  <math|A,D<rsub|i>,C<rsub|i>> be conjunctions of atoms. Let
  <math|A\<in\>Abd<rsub|\<cal-C\>><around*|(|D<rsub|i>,C<rsub|i>|)>> mean
  that <math|A> is an answer to the simple abduction problem
  <math|D<rsub|i>\<Rightarrow\>C<rsub|i>> under theory <math|\<cal-C\>>, i.e.
  <math|\<cal-C\>\<wedge\>D<rsub|i>\<wedge\>A\<Vdash\>C<rsub|i>>. Let
  <math|C\<equiv\>Simple<around*|(|C|)>\<wedge\>Implic<around*|(|C|)>> be a
  decomposition of a constraint <math|C> into a conjunction of atoms
  <math|Simple<around*|(|C|)>> and a conjunction of existentially quantified
  implications <math|Implic<around*|(|C|)>>. For a substitution
  <math|R=<around*|[|<wide|\<alpha\>|\<bar\>>\<assign\><wide|\<tau\>|\<bar\>>|]>=<around*|[|\<alpha\><rsub|1>\<assign\>\<tau\><rsub|1>,\<ldots\>,\<alpha\><rsub|n>\<assign\>\<tau\><rsub|n>|]>>,
  let <math|<wide|R|\<dot\>>=<wide|\<alpha\>|\<bar\>><wide|=|\<dot\>><wide|\<tau\>|\<bar\>>=\<alpha\><rsub|1><wide|=|\<dot\>>\<tau\><rsub|1>\<wedge\>\<ldots\>\<wedge\>\<alpha\><rsub|n><wide|=|\<dot\>>\<tau\><rsub|n>>.
  We define the solver recursively:

  <\equation*>
    <frac|<tabular|<tformat|<table|<row|<cell|C<rsub|r>\<wedge\><wide|R|\<dot\>>\<in\>Abd<rsub|\<cal-C\>><around*|(|C<rsub|g>,Simple<around*|(|C|)>|)><with|mode|text|
    \ \ \ >Dom<around*|(|R|)>\<subseteq\><wide|\<alpha\>|\<bar\>>>>|<row|<cell|\<forall\><around*|(|\<exists\><wide|\<alpha\>|\<bar\>><rsub|i>.D<rsub|i>\<Rightarrow\>C<rsub|i>\<in\>Implic<around*|(|C|)>|)>.Solve<around*|(|\<cal-C\>;C<rsub|g>\<wedge\>C<rsub|r>\<wedge\>D<rsub|i>;<wide|\<alpha\>|\<bar\>><rsub|i>;C<rsub|i>|)>\<rightsquigarrow\><around*|(|\<varnothing\>,R<rsub|i>|)>>>>>>|Solve<around*|(|\<cal-C\>;C<rsub|g>;<wide|\<alpha\>|\<bar\>><rsub|i>;C<rsub|w>|)>\<rightsquigarrow\><around*|(|C<rsub|r>,R|)>>
  </equation*>

  While it appears that the type inference solution is built out of abduction
  answers <math|<around*|(|C<rsub|r>,R|)>>, the interesting simple abduction
  problems <math|D<rsub|i>\<Rightarrow\>C<rsub|i>> are required to have
  abduction answer (<math|<wide|R<rsub|i>|\<dot\>>>) limited to variables
  <math|<wide|\<alpha\>|\<bar\>><rsub|i>>, which can be subsequently ignored.

  Motivated by considerations of efficiency and avoiding ambiguity,
  <cite|OutsideIn> restricts the abduction algorithms to those only searching
  for fully maximal answers. <cite|OutsideIn> conjectures that the algorithm
  they provide is complete wrt. fully maximal answers to simple abduction
  problems. <math|OutsideIn<around*|(|X|)>> might not be able to use the
  abduction algorithm complete wrt. fully maximal answers to simple
  <em|constraint> abduction problems from <cite|AbductionSolvMaher>, even
  when limited to GADTs, because the <math|OutsideIn<around*|(|X|)>> type
  system is based on a logic instead of on fixed models like Herbrand
  structures.

  <subsection|Relevance>

  The <math|OutsideIn<around*|(|X|)>> project exposition <cite|OutsideIn>
  lists multiple challenges as being in its focus. Of these, <name|InvarGenT>
  addresses GADTs, and is open to address <em|units of measure>, although the
  corresponding sort has not been implemented. The other challenges fall
  outside of the scope of <name|InvarGenT>: type-class constraints,
  multi-parameter type classes with functional dependencies, and type
  families with type family axioms. Some of these type system features, when
  implemented directly, violate the requirement on the interpretation of
  types that we preserve from <math|HMG<around*|(|X|)>>: ``Every constraint
  of the form <math|\<tau\><rsub|1>\<rightarrow\>\<tau\><rsub|2>\<preccurlyeq\>\<varepsilon\><around*|(|<wide|\<tau\>|\<bar\>>|)>>
  or <math|\<varepsilon\><around*|(|<wide|\<tau\>|\<bar\>>|)>\<preccurlyeq\>\<tau\><rsub|1>\<rightarrow\>\<tau\><rsub|2>>
  or <math|\<varepsilon\><around*|(|<wide|\<tau\>|\<bar\>>|)>\<preccurlyeq\>\<varepsilon\><rprime|'><around*|(|<wide|\<tau\>|\<bar\>><rprime|'>|)>>
  for <math|\<varepsilon\>\<neq\>\<varepsilon\><rprime|'>>, is
  unsatisfiable.'' (In <name|InvarGenT>, we have equality
  <math|<wide|=|\<dot\>>> instead of subtyping <math|\<preccurlyeq\>>.)

  <cite|OutsideIn> argues strongly against selecting an arbitrary correct
  type when a definition does not have a most general type. <name|InvarGenT>
  does select an arbitrary type without guarantees, although the
  implementation is designed to pick useful types; e.g. if possible, with the
  return type of a function sharing a parameter with an argument type.
  <name|InvarGenT> is intended to provide type signatures for toplevel
  definitions to the programmer. The programmer would then either accept the
  signature, modify the program and re-generate the signature, or modify the
  signature directly.

  <math|OutsideIn<around*|(|X|)>> shares with <name|InvarGenT> the
  restriction of type scheme invariants, and guards of data constructors, to
  conjunctions of atoms. On other points of difference between
  <math|OutsideIn<around*|(|X|)>> and <math|HMG<around*|(|X|)>>,
  <name|InvarGenT> follows <math|HMG<around*|(|X|)>>. Both
  <math|OutsideIn<around*|(|X|)>> and <name|InvarGenT> infer types for
  toplevel definitions one at a time.

  Finally, the type inference algorithm of <math|OutsideIn<around*|(|X|)>> is
  much weaker than that of <name|InvarGenT>, as illustrated in our
  presentation of the central step of the algorithm in terms of abduction.
  While our algorithm uses abduction to search for the solution of the type
  inference problem, <math|OutsideIn<around*|(|X|)>> only uses abduction to
  verify a partial solution found by unification.

  <section|Pointwise GADTs><label|PointwiseSection>

  Chuan-kai Lin in <cite|PracticalGADTsInfer>, see also Lin<localize| and
  >Sheard <cite|PointwiseGADTs>, presents a type inference algorithm for
  GADTs. Just as <name|InvarGenT>, the type system Pointwise GADTs and the
  algorithm <math|\<cal-P\>> from <cite|PracticalGADTsInfer> does not require
  type annotations. The Pointwise GADTs is not a constraint-based type
  system. Also, it does not support deep patterns. Let us look at the two
  most important type system rules. The recursive definition rule captures
  polymorphic recursion:

  <\equation*>
    <frac|<tabular|<tformat|<table|<row|<cell|\<Gamma\><around|{|x\<mapsto\>\<forall\><wide|\<alpha\>|\<bar\>>.\<tau\><rprime|'>|}>\<vdash\>e<rsub|1>:\<tau\><rprime|'>>|<cell|<wide|\<alpha\>|\<bar\>>#FV<around*|(|\<Gamma\>|)>>|<cell|\<Gamma\><around|{|x\<mapsto\>\<sigma\>|}>\<vdash\>e<rsub|2>:\<tau\>>>>>>|\<Gamma\>\<vdash\><text|<with|font-shape|condensed|<strong|let
    rec>>> x=e<rsub|1> <text|<with|font-shape|condensed|<strong|in>>>
    e<rsub|2>:\<tau\>>
  </equation*>

  The rule for pattern matching expressions is straightforward, nearly the
  same as the corresponding derived rule in <math|HMG<around*|(|X|)>>. We
  turn to the pattern matching branch rule:

  <\equation*>
    <frac|<tabular|<tformat|<table|<row|<cell|K\<colons\>\<forall\><wide|\<alpha\>|\<bar\>>.<wide|r|\<bar\>>\<longrightarrow\>\<varepsilon\>
    <wide|s|\<bar\>>>|<cell|>|<cell|<wide|\<alpha\>|\<bar\>>#FV<around*|(|\<Gamma\>,<wide|u|\<bar\>>,\<tau\>|)>>>|<row|<cell|S=\<b-P\>\<b-U\><around*|(|\<varepsilon\>
    <wide|u|\<bar\>><wide|=|\<dot\>>\<varepsilon\>
    <wide|s|\<bar\>>|)>>|<cell|>|<cell|S<around*|(|\<Gamma\><around*|{|<wide|x|\<bar\>>\<assign\><wide|r|\<bar\>>|}>|)>\<vdash\>e:S<around*|(|\<tau\>|)>>>>>>|\<Gamma\>\<vdash\><rsub|p>K
    <wide|x|\<bar\>>.e:\<varepsilon\> <wide|u|\<bar\>>\<rightarrow\>\<tau\>>
  </equation*>

  <math|\<b-P\>\<b-U\>> stands for <em|pointwise unification>. It is a
  limited form of unification. If <math|U=\<b-P\>\<b-U\><around*|(|s<wide|=|\<dot\>>t|)>>,
  then <math|U<around*|(|s|)>=U<around*|(|t|)>>, but also: for
  <math|\<alpha\>\<in\>Dom<around*|(|U|)>>, if
  <math|s\<downharpoonright\><rsub|p>=\<alpha\>>, i.e. <math|s> has variable
  <math|\<alpha\>> at position <math|p>, then
  <math|t\<downharpoonright\><rsub|p>=U<around*|(|\<alpha\>|)>>; similarly,
  if <math|t\<downharpoonright\><rsub|p>=\<alpha\>>, then
  <math|s\<downharpoonright\><rsub|p>=U<around*|(|\<alpha\>|)>>.

  The type inference algorithm <math|\<cal-P\>> is deliberately more
  restrictive than the type system Pointwise GADTs. In particular, it uses
  <em|anti-unification> to infer a tight type for the pattern-matched
  expression, so that the pattern matching has a better chance of being
  exhaustive given the type.

  <subsection|Type Inference>

  Algorithm <math|\<cal-P\>> is based on Robin Milner's algorithm
  <math|\<cal-W\>> as in <cite|Milner78>, and its modification by Alan
  Mycroft to handle polymorphic recursion as in <cite|Mycroft84>. See
  <cite|PracticalGADTsInfer> pages 152-184 for detailed presentation. We
  reproduce details of the algorithm <math|\<cal-P\>>, because \ algorithm
  <math|\<cal-P\>> provides a base-line wrt. which type inference for GADTs
  not relying on type annotations can be compared. We defer the reader who
  finds the current section cryptic to Chuan-kai Lin
  <cite|PracticalGADTsInfer>.

  It might be worthwhile to collect the major pieces of algorithm
  <math|\<cal-P\>> together:

  <\eqnarray*>
    <tformat|<table|<row|<cell|infer<around*|(|\<Gamma\>,e<rsub|1>
    e<rsub|2>|)>>|<cell|=>|<cell|>>|<row|<cell|<around*|(|S<rsub|1>,\<tau\><rsub|1>|)>>|<cell|=>|<cell|infer<around*|(|\<Gamma\>,e<rsub|1>|)>>>|<row|<cell|<around*|(|S<rsub|2>,\<tau\><rsub|2>|)>>|<cell|=>|<cell|infer<around*|(|\<Gamma\>,e<rsub|2>|)>>>|<row|<cell|S<rsub|3>>|<cell|=>|<cell|\<b-U\><around*|(|\<tau\><rsub|1><wide|=|\<dot\>>\<tau\><rsub|2>\<rightarrow\>\<beta\>|)><with|mode|text|,
    >\<beta\><with|mode|text| fresh>>>|<row|<cell|S>|<cell|=
    >|<cell|\<b-C\><around*|(|S<rsub|1>,S<rsub|2>,S<rsub|3>|)>>>|<row|<cell|>|<cell|>|<cell|<around*|(|S,S<around*|(|\<beta\>|)>|)>>>|<row|<cell|>|<cell|>|<cell|>>|<row|<cell|infer<around*|(|\<Gamma\>,<text|<with|font-shape|condensed|<strong|let
    rec>>> x=e|)>>|<cell|=>|<cell|polyrec<around*|(|<around*|{||}>,\<forall\>\<alpha\>.\<alpha\>|)>>>|<row|<cell|polyrec<around*|(|S<rsub|1>,\<sigma\>|)>>|<cell|=>|<cell|>>|<row|<cell|<around*|(|S<rsub|2>,\<tau\>|)>>|<cell|=>|<cell|infer<around*|(|\<Gamma\><around*|{|u\<mapsto\>\<sigma\>|}>,e|)>>>|<row|<cell|<wide|\<beta\>|\<bar\>>>|<cell|=>|<cell|FV<around*|(|\<tau\>|)>\\FV<around*|(|\<Gamma\><around*|{|u\<mapsto\>\<sigma\>|}>|)>>>|<row|<cell|\<sigma\><rprime|'>>|<cell|=>|<cell|\<forall\><wide|\<beta\>|\<bar\>>.\<tau\>>>|<row|<cell|<with|mode|text|if>>|<cell|>|<cell|S<rsub|2><around*|(|\<sigma\>|)>=\<sigma\><rprime|'>>>|<row|<cell|<with|mode|text|then>>|<cell|>|<cell|<around*|(|S<rsub|2>
    S<rsub|1>,\<sigma\><rprime|'>|)>>>|<row|<cell|<with|mode|text|else>>|<cell|>|<cell|polyrec<around*|(|S<rsub|2>
    S<rsub|1>,\<sigma\><rprime|'>|)>>>|<row|<cell|>|<cell|>|<cell|>>|<row|<cell|infer<around*|(|\<Gamma\>,<with|math-font-series|bold|case>
    e <with|math-font-series|bold|of> <wide|p<rsub|i>.e<rsub|i>|\<bar\>>|)>>|<cell|=>|<cell|>>|<row|<cell|<around*|(|S<rsub|0>,u<rsub|0>|)>>|<cell|=>|<cell|infer<around*|(|\<Gamma\>,e|)>>>|<row|<cell|<around*|(|S<rsub|i>,u<rsub|i>,\<tau\><rsub|i>|)>>|<cell|=>|<cell|infer<rsub|ALT><around*|(|\<Gamma\>,\<beta\>,p<rsub|i>.e<rsub|i>|)><with|mode|text|,
    >\<beta\><with|mode|text| fresh>>>|<row|<cell|u>|<cell|=>|<cell|LUB<around*|(|\<tau\><rsub|1>,\<ldots\>,\<tau\><rsub|n>|)>>>|<row|<cell|S>|<cell|=>|<cell|\<b-U\><around*|(|<around*|(|u,\<ldots\>,u|)><wide|=|\<dot\>><around*|(|u<rsub|0>,u<rsub|1>,\<ldots\>,u<rsub|n>|)>|)>>>|<row|<cell|s>|<cell|=>|<cell|S<around*|(|u|)>>>|<row|<cell|R<rsub|i>>|<cell|=>|<cell|\<b-C\><around*|(|S,S<rsub|0>,S<rsub|i>,\<b-U\><around*|(|u<rsub|i><wide|=|\<dot\>>\<tau\><rsub|i>|)>|)>>>|<row|<cell|<wide|\<alpha\>|\<bar\>>>|<cell|=>|<cell|FV<around*|(|s|)>\<cap\><around*|(|\<cup\><rsub|i>Dom<around*|(|R<rsub|i>|)>|)>>>|<row|<cell|<wide|\<beta\>|\<bar\>>>|<cell|=>|<cell|FV<around*|(|s|)>\\<wide|\<alpha\>|\<bar\>>>>|<row|<cell|trt>|<cell|=>|<cell|tabulate<around*|(|<wide|\<alpha\>|\<bar\>>,<wide|R<rsub|i>|\<bar\>>|)>>>|<row|<cell|btt>|<cell|=>|<cell|tabulate<around*|(|\<beta\>FV<around*|(|\<Gamma\>|)>,<wide|R<rsub|i>|\<bar\>>|)>>>|<row|<cell|R>|<cell|=>|<cell|reconcile<around*|(|<wide|\<beta\>|\<bar\>>,trt,btt|)>>>|<row|<cell|>|<cell|>|<cell|<around*|(|R,R<around*|(|\<beta\>|)>|)>>>|<row|<cell|>|<cell|>|<cell|>>|<row|<cell|infer<rsub|ALT><around*|(|\<Gamma\>,\<beta\>,K
    <wide|x|\<bar\>>.e|)>>|<cell|=>|<cell|>>|<row|<cell|\<forall\><wide|\<alpha\>|\<bar\>>.<wide|r|\<bar\>>\<longrightarrow\>\<varepsilon\>
    <wide|s|\<bar\>>>|<cell|=>|<cell|lookup<around*|(|K|)><with|mode|text|
    \ where ><wide|\<alpha\>|\<bar\>><with|mode|text|
    fresh>>>|<row|<cell|<around*|(|S,\<tau\>|)>>|<cell|=>|<cell|infer<around*|(|\<Gamma\><around*|{|<wide|x\<mapsto\>r|\<bar\>>|}>,e|)>>>|<row|<cell|<wide|\<alpha\>|\<bar\>><rprime|'>>|<cell|=>|<cell|<wide|\<alpha\>|\<bar\>>\<cap\><around*|(|Dom<around*|(|S|)>\<cup\>FV<around*|(|Rng<around*|(|S|)>|)>\<cup\>FV<around*|(|\<tau\>|)>|)>>>|<row|<cell|<wide|\<gamma\>|\<bar\>>>|<cell|=>|<cell|<around*|{|\<gamma\><mid|\|>\<gamma\>\<in\><wide|\<alpha\>|\<bar\>>\<wedge\>retain<around*|(|<wide|\<alpha\>|\<bar\>>,S,\<gamma\>|)>|}>>>|<row|<cell|<with|mode|text|if>>|<cell|>|<cell|<wide|\<alpha\>|\<bar\>><rprime|'>\<nsubseteq\>FV<around*|(|<wide|s|\<bar\>>|)>>>|<row|<cell|<with|mode|text|then>>|<cell|>|<cell|\<bot\>>>|<row|<cell|<with|mode|text|else
    if>>|<cell|>|<cell|<wide|\<gamma\>|\<bar\>>=\<varnothing\>>>|<row|<cell|<with|mode|text|then>>|<cell|>|<cell|<around*|(|<around*|[|\<beta\>\<assign\>\<tau\>|]>
    S,\<varepsilon\> <wide|\<gamma\>|\<bar\>><rprime|'>,\<varepsilon\>
    <wide|s|\<bar\>>|)><with|mode|text| where
    ><wide|\<gamma\>|\<bar\>><rprime|'><with|mode|text|
    fresh>>>|<row|<cell|<with|mode|text|else>>|<cell|>|<cell|<around*|(|<around*|[|\<beta\>\<assign\>\<tau\>|]>
    S,S<around*|(|transcb<around*|(|<wide|\<gamma\>|\<bar\>>,\<varepsilon\>
    <wide|s|\<bar\>>|)>|)>,\<varepsilon\>
    <wide|s|\<bar\>>|)>>>|<row|<cell|>|<cell|>|<cell|>>|<row|<cell|retain<around*|(|<wide|\<alpha\>|\<bar\>>,S,\<gamma\>|)>>|<cell|=>|<cell|>>|<row|<cell|S<around*|(|\<gamma\>|)>=\<varepsilon\><rprime|'>
    <wide|r|\<bar\>>>|<cell|\<rightarrow\>>|<cell|\<b-T\>>>|<row|<cell|S<around*|(|\<gamma\>|)>=\<alpha\>>|<cell|\<rightarrow\>>|<cell|\<exists\>\<beta\>\<in\><wide|\<alpha\>|\<bar\>>.\<beta\>\<neq\>\<gamma\>\<wedge\>\<alpha\>\<in\>FV<around*|(|S<around*|(|\<beta\>|)>|)>>>|<row|<cell|>|<cell|>|<cell|>>|<row|<cell|transcb<around*|(|<wide|\<gamma\>|\<bar\>>,\<tau\>|)>>|<cell|=>|<cell|>>|<row|<cell|<with|mode|text|if>>|<cell|>|<cell|<wide|\<gamma\>|\<bar\>>#FV<around*|(|\<tau\>|)>>>|<row|<cell|<with|mode|text|then>>|<cell|>|<cell|\<beta\><with|mode|text|
    where >\<beta\><with|mode|text| fresh>>>|<row|<cell|<with|mode|text|else>>|<cell|>|<cell|>>|<row|<cell|\<tau\>=\<varepsilon\><rprime|'>
    <wide|r|\<bar\>>>|<cell|\<rightarrow\>>|<cell|\<varepsilon\><rprime|'>
    <wide|transcb<around*|(|<wide|\<gamma\>|\<bar\>>,r|)>|\<bar\>>>>|<row|<cell|\<tau\>=\<alpha\>>|<cell|\<rightarrow\>>|<cell|\<alpha\>>>>>
  </eqnarray*>

  The operation <math|\<b-C\>> is a combination of substitutions having the
  effect of unification of the corresponding equations:

  <\equation*>
    \<b-C\><around*|(|S<rsub|1>,\<ldots\>,S<rsub|n>|)>=\<b-U\><around*|(|\<wedge\><rsub|i><wide|S|\<dot\>><rsub|i>|)>=\<b-U\><around*|(|<around|(|<wide|a<rsub|1>|\<bar\>>,\<ldots\>,<wide|\<alpha\><rsub|n>|\<bar\>>|)><wide|=|\<dot\>><around*|(|S<rsub|1><around*|(|<wide|\<alpha\><rsub|1>|\<bar\>>|)>,\<ldots\>,S<rsub|n><around*|(|<wide|\<alpha\><rsub|n>|\<bar\>>|)>|)>|)><with|mode|text|
    where ><wide|\<alpha\><rsub|i>|\<bar\>>=Dom<around*|(|S<rsub|i>|)>
  </equation*>

  \ The algorithm is designed after algorithm <math|\<cal-W\>>. However, it
  is made more modular by the use of <math|\<b-C\>>. This can be seen as a
  ``concealed'' form of constraint derivation based type inference, where the
  partial constraints are solved during collection. The case
  <math|infer<around*|(|\<Gamma\>,<text|<with|font-shape|condensed|<strong|let
  rec>>> x=e|)>> is the Mycroft's modification of algorithm <math|\<cal-W\>>
  to handle polymorphic recursion. It introduces iteration of type inference,
  for each recursive definition separately, till the definition's type
  converges. The <math|LUB<around*|(|\<tau\><rsub|1>,\<ldots\>,\<tau\><rsub|n>|)>>
  subroutine used in <math|infer<around*|(|\<Gamma\>,<no-break><with|math-font-series|bold|case>
  e <with|math-font-series|bold|of> <wide|p<rsub|i>.e<rsub|i>|\<bar\>>|)>> is
  <em|anti-unification>, a special case of what we will call <em|constraint
  generalization>. It computes the type <math|u> for the expression <math|e>
  as specific as possible while agreeing with all types imposed by the
  pattern matching branches. The complications in handling variables in
  <math|infer<rsub|ALT><around*|(|\<Gamma\>,\<beta\>,K
  <wide|x|\<bar\>>.e|)>>, in particular the failure condition
  <math|<wide|\<alpha\>|\<bar\>><rprime|'>\<nsubseteq\>FV<around*|(|<wide|s|\<bar\>>|)>>,
  are analogous to the fact that the variables
  <math|<wide|\<alpha\>|\<bar\>>> would be universally quantified by
  <math|HMG<around*|(|X|)>>, and thus cannot be part of, for example, the
  domain of the resulting substitution.

  The aspect of algorithm <math|\<cal-P\>> that is closest to the intricacies
  of term constraint abduction is the joint use of the <math|tabulate> and
  <math|reconcile> subroutines (not presented above). They decompose
  respectively the pattern-matched expression type, and the pattern-matching
  branch body type, when the types start with the same type constructor
  <math|\<varepsilon\>> across branches. When the types across branches do
  not agree, but a <math|btt> column corresponding to a subterm of the result
  type, i.e. branch bodies type, is unifiable (branch-wise) with exactly one
  <math|trt> column, then the subterm of the result type is replaced by the
  corresponding subterm of the pattern-matched expression type.

  <subsection|Relevance>

  Algorithm <math|\<cal-P\>> is designed to infer types for GADT programs
  without relying on type annotations. This is the major goal of
  <name|InvarGenT>, alongside inference of existential types and ease of
  extension with novel sorts. The type system behind algorithm
  <math|\<cal-P\>> is not constraint based, and in particular, it has no
  mechanism for extension with, for example, numerical invariants. The
  Pointwise GADTs type system is much more restrictive than the plain GADTs
  type system around which <name|InvarGenT> is designed. Algorithm
  <math|\<cal-P\>> is very efficient compared to <name|InvarGenT>, but still
  quite capable. Some inspirations for <name|InvarGenT> can be drawn from
  algorithm <math|\<cal-P\>>.

  The examples from <cite|PracticalGADTsInfer> motivated the extension of
  simple constraint abduction algorithm for terms in <name|InvarGenT> to
  non-fully-maximal answers. The extension allows guessing equations between
  invariant parameters. The use of anti-unification in algorithm
  <math|\<cal-P\>> is interesting and the prospect of using constraint
  generalization in <name|InvarGenT> to infer a tighter type when otherwise a
  pattern matching expression would not be exhaustive, is intriguing, but we
  leave it as future work. Finally, table-based approach to <em|GADT type
  refinements> in algorithm <math|\<cal-P\>>, via the <math|tabulate> and
  <math|reconcile> subroutines, might inspire future work on augmenting the
  sequential approaches to joint constraint abduction, by ``simultaneous''
  stages, operating jointly on all branches.

  <section|Liquid Types><label|LiquidSection>

  Tim Freeman and Frank Pfenning's <em|Refinement Types for ML>
  <cite|RefinementFreemanPfenning> predates even the Odersky, Sulzmann and
  Wehr <cite|HMX>. Refinement types are so called because they refine the ML
  type system, rather than extending it as GADTs do -- they do not make new
  programs typeable. Refinement types became the universally and
  existentially quantified types of DML. More recently, they were
  independently developed in an inference-friendly way by Cormac Flanagan
  <cite|Flanagan06> and Knowles and Flanagan <cite|KnowlesF07>. The work was
  continued by Ranjit Jhala, Patrick Rondon and collaborators, and their
  systems <name|DSolve> <cite|DSolvePaper> and <name|HSolve>
  <cite|AbstractLiquid> have become more popular. They are fully focused on
  automatic invariant inference. The work behind <name|DSolve>
  (<cite|DSolvePaper>, expanded in <cite|DSolveTechRep> and
  <cite|DSolveThesis>) is the topic of this section. <cite|DSolvePaper> cites
  the work on predicate abstraction <cite|AssertionGraphs>,
  <cite|AbstractStateGraphs> as precursory for this kind of invariant
  inference; and Jeffrey Scott Foster on Type Qualifiers
  <cite|TypeQualifiers>, as inspiring some aspects of inference.

  <subsection|The Type System>

  Type refinements can be seen as preconditions (or postconditions) when they
  refine the argument type (or the result type) of a function. The term
  <em|Liquid Types> introduced by <cite|DSolvePaper> comes from ``logically
  qualified types'', a restriction of an otherwise more depent-types-like
  type system, limiting type refinements to conjuctions of atoms from a sort
  of linear inequalities and uninterpreted functions. The refinements are
  over base (i.e. non-function) types, and are written:
  <math|<around*|{|\<nu\>:B<mid|\|>e|}>>, where <math|B> is a base type like
  <verbatim|int>, <math|e> is a conjunction of atoms, and <math|\<nu\>> is a
  singled-out variable constrained by <math|e>. (In the formalism used by
  <name|InvarGenT>, the letter <math|\<delta\>> will play the role of
  <math|\<nu\>> here.) Recall the typing judgment form
  <math|C,\<Gamma\>\<vdash\>e:\<tau\>> we encountered in systems described
  earlier: assuming constraint <math|C> holds, in environment
  <math|\<Gamma\>>, expression <math|e> has type <math|\<tau\>>. Although the
  Liquid Types typing judgment <math|\<Gamma\>\<vdash\>e:T> (where <math|T>
  stands for a liquid type or type scheme) seems simpler, here <math|C> is a
  part of <math|\<Gamma\>>. The assumed constraint is:

  <\equation*>
    <around*|\<llbracket\>|\<Gamma\>|\<rrbracket\>>\<equiv\>\<wedge\><rsub|e\<in\>\<Gamma\>>e\<wedge\><rsub|x:<around*|{|\<nu\>:B<mid|\|>e|}>\<in\>\<Gamma\>>e<around*|[|\<nu\>\<assign\>x|]>
  </equation*>

  The Liquid Types type system is based on subtyping rather than type
  equality. Here, subtyping implicitly captures the requirements on the
  assumed constraint. The subtyping judgment has the form
  <math|\<Gamma\>\<vdash\>T<rsub|1>\<less\>:T<rsub|2>>, which means:
  <math|<around*|\<llbracket\>|\<Gamma\>|\<rrbracket\>>> implies that
  <math|T<rsub|1>> is a subtype of <math|T<rsub|2>>.

  The function type arguments are indexed by the variable corresponding to
  the <math|\<lambda\>>-abstraction introducing the type:
  <math|\<Gamma\>\<vdash\>\<lambda\>x.e:<around*|(|x:T<rsub|x>\<rightarrow\>T|)>>.
  Together with the following rules:

  <\equation*>
    <frac|\<Gamma\><around*|(|x|)>=<around*|{|\<nu\>:B<mid|\|>e|}>|\<Gamma\>\<vdash\>x:<around*|{|\<nu\>:B<mid|\|>\<nu\><wide|=|\<dot\>>x|}>>
  </equation*>

  <\equation*>
    <frac|\<Gamma\>\<vdash\>e<rsub|1>:S<with|mode|text|
    \ \ >\<Gamma\>;x:S\<vdash\>e<rsub|2>:T|\<Gamma\>\<vdash\><text|<with|font-shape|condensed|<strong|let>>>
    x=e<rsub|1> <text|<with|font-shape|condensed|<strong|in>>> e<rsub|2>>
  </equation*>

  this avoids the use of existential quatification in inference constraints.
  The crucial rules relevant for invariants are:

  <\equation*>
    <frac|\<Gamma\>\<vdash\>e<rsub|1>:Bool<with|mode|text|
    \ \ >\<Gamma\>;e<rsub|1>\<vdash\>e<rsub|2>:T<with|mode|text|
    \ \ >\<Gamma\>;\<neg\>e<rsub|1>\<vdash\>e<rsub|3>:T|\<Gamma\>\<vdash\><text|<with|font-shape|condensed|<strong|if>>>
    e<rsub|1> <text|<with|font-shape|condensed|<strong|then>>> e<rsub|2>
    <text|<with|font-shape|condensed|<strong|else>>> e<rsub|3>:T>
  </equation*>

  <\equation*>
    <frac|Valid<around*|(|<around*|\<llbracket\>|\<Gamma\>|\<rrbracket\>>\<wedge\>e<rsub|1>\<Rightarrow\>e<rsub|2>|)>|\<Gamma\>\<vdash\><around*|{|\<nu\>:B<mid|\|>e<rsub|1>|}>\<less\>:<around*|{|\<nu\>:B<mid|\|>e<rsub|2>|}>>
  </equation*>

  In the first rule, the expressions <math|e<rsub|1>> are limited to
  well-formed formulas of the constraint domain. Note how the former rule
  resembles the <math|HMG<around*|(|X|)>> Rule <reference|HMGClauseRule> in
  that the local constraint is enhanced by the information pertaining to the
  conditional branch. The latter rule resembles the Rule
  <reference|HMGVarRule> in that the local constraint is used as a premise to
  ensure the validity of the use of a value.

  <subsection|Liquid Types Inference>

  Similarly to <name|<name|InvarGenT>>, the <name|DSolve> system first
  generates the inference constraint for the whole toplevel expression, and
  then proceeds to solve the constraint. <name|DSolve> uses an oracle to
  solve the Hindley-Milner polymorphic type inference subproblems, and the
  resulting type shapes guide the construction of the constraint. In this
  way, the constraint describes purely the subtyping issues, rather than both
  the typing and subtyping issues. Each subtyping requirement contributes
  what would be an implication in a normalized <name|InvarGenT> constraint.
  The Liquid Type Inference Algorithm, including constraint generation, can
  be found in <cite|DSolvePaper>, page 9, Figure 4. Liquid Types inference
  introduces <em|liquid type variables> <math|\<kappa\>>, standing for
  unknown invariants. (In <name|InvarGenT>, we call them <em|predicate
  variables> <math|\<chi\>>.) The inference task is to find a substitution
  for the liquid type variables such that all the implications corresponding
  to subtyping constraints are valid. We present the liquid type variable
  solving part of the inference algorithm:

  <\eqnarray*>
    <tformat|<table|<row|<cell|Weaken <around*|(|\<Gamma\>\<vdash\><around*|{|\<nu\>:B<mid|\|>\<theta\>\<cdot\>\<kappa\>|}>|)>
    A>|<cell|=>|<cell|A\<circ\><around*|[|\<kappa\>\<assign\><next-line><with|mode|text|
    \ \ ><around*|{|q\<in\>A<around*|(|\<kappa\>|)><mid|\|>\<Gamma\>;\<nu\>:B\<vdash\>\<theta\><around*|(|q|)>:Bool|}>|]><eq-number><label|LiqAlgR1>>>|<row|<cell|Weaken
    <around*|(|\<Gamma\>\<vdash\><around*|{|\<nu\>:B<mid|\|>\<rho\>|}>\<less\>:<around*|{|\<nu\>:B<mid|\|>\<theta\>\<cdot\>\<kappa\>|}>|)>
    A>|<cell|=>|<cell|A\<circ\><around*|[|\<kappa\>\<assign\><next-line><with|mode|text|
    \ \ ><around*|{|q\<in\>A<around*|(|\<kappa\>|)><mid|\|><around*|\<llbracket\>|A<around*|(|\<Gamma\>|)>|\<rrbracket\>>\<wedge\>A<around*|(|\<rho\>|)>\<Rightarrow\>\<theta\><around*|(|q|)>|}>|]><eq-number><label|LiqAlgR2>>>|<row|<cell|Weaken
    _ A>|<cell|=>|<cell|\<bot\><eq-number><label|LiqAlgR3>>>|<row|<cell|>|<cell|>|<cell|>>|<row|<cell|Solve
    C A<with|mode|text| when >\<exists\>c\<in\>C<next-line><with|mode|text|where
    >A<around*|(|c|)><with|mode|text| is not valid>>|<cell|=>|<cell|Solve C
    <around*|(|Weaken c A|)>>>|<row|<cell|Solve _ A>|<cell|=>|<cell|A>>>>
  </eqnarray*>

  The pair <math|\<theta\>\<cdot\>\<kappa\>> of a substitution
  <math|\<theta\>> and liquid type variable <math|\<kappa\>> is a <em|delayed
  substitution>, see Knowles and Flanagan <cite|KnowlesF07>. Entry
  <reference|LiqAlgR1> above ensures that the solution formulas are
  well-formed. Entry <reference|LiqAlgR2> filters out the atoms which are not
  implied by the premise of the implication considered. Entry
  <reference|LiqAlgR3> is the failure case: the offending implication cannot
  be made valid. It cannot be weakened, as it does not contain a liquid type
  variable in the conclusion, and the premise is already as strong as
  possible. The initial call to <math|Solve> passes as the initial solution
  <math|A>, for each liquid type variable <math|\<kappa\>>, a conjunction of
  <em|all> atoms over the potential parameters of invariants appearing in
  constraints.

  <subsection|Relevance>

  It will be illuminating for Chapter <reference|ChapSolv> to compare the
  solver of <name|DSolve> with that of <name|InvarGenT>. In a single
  iteration of the main algorithm of: <name|DSolve>, a single invariant (i.e.
  <math|\<kappa\>> substitution) is updated; <name|InvarGenT>, all invariants
  (i.e. <math|\<chi\>> substitutions) are updated. This makes: in
  <name|DSolve>, a single implication valid, given before-update substitution
  of liquid type variables in premises; in <name|InvarGenT>, all implications
  valid, given before-update substitution of ``liquid type'', i.e. predicate
  variables in conclusions. <name|DSolve> focuses on the role liquid type
  variables play in conclusions, and ignores their role in premises, other
  than to verify validity of implications. <name|InvarGenT> focuses on the
  role all predicate variables play in premises, but also, using a different
  mechanism, on postcondition predicate variables in conclusions.
  <name|DSolve> starts with a full initial solution (a conjuction of all
  atoms, trivially contradictory); <name|InvarGenT> starts with an empty
  initial solution (an empty conjunction, trivially satisfiable).
  <name|DSolve> finds the most specific (least general) solution for all
  invariants. <name|InvarGenT> finds the least specific (most general)
  solution for preconditions, and the most specific solution for
  postconditions given these preconditions.

  Here are three arguments in favor of <name|InvarGenT> over <name|DSolve>.
  The major limitation of <name|DSolve> is the need to generate all the atoms
  as the initial solution; in <name|InvarGenT>, the addition of atoms to the
  solution is driven by the conclusions that need to be explained. Least
  general preconditions are less useful than most general preconditions.
  Furthermore, in principle, there can be solutions that are overlooked by
  solving one invariant at a time.

  There are two shortcomings of <name|InvarGenT> relative to <name|DSolve>
  that should inspire future work; we start with the major one.
  <name|InvarGenT> prohibits passing values of an existentially quantified
  type as arguments, and it does not allow type schemes as argument types.
  Thus functions like <verbatim|ffor> from the <verbatim|fft> example, see
  Appendix <reference|ExamplesCode> Subsection <reference|FFTExample>,
  require manual packing and unpacking for the argument of the function
  passed to the higher-order function. <name|DSolve> manages to infer types
  for such higher-order functions, and this ability is further improved in
  Abstract Refinement Types: Vazou, Rondon and Jhala <cite|AbstractLiquid>.

  The other shortcoming is that, while <name|InvarGenT> is faster with simple
  input programs, <name|DSolve> is faster with more complex programs for
  which it is able to find a solution. There are two reasons. One is that
  <name|DSolve> entirely eliminates variables which cannot be invariant
  parameters before starting the solution process, i.e. intermediate
  variables of the Hindley-Milner inference process. <name|InvarGenT> deploys
  the general mechanism of abduction to solve for all variables. The other
  reason is that <name|DSolve> only checks all constraints for contradiction
  once every update of an invariant <math|\<kappa\>>. <name|InvarGenT> checks
  all constraints for contradiction for every candidate atom to be added
  during an update of invariants.

  <section|Herbrand Constraint Abduction><label|HerbSection>

  We have invoked ``abduction'' multiple times already, it is time to define
  the term. <em|Abduction> is a form of inference where we find an
  explanation of a target formula (often referred to as an observation) given
  background knowledge. Given a signature <math|\<Sigma\>> and a set of
  variables <math|Vars>, a <em|constraint domain> is a pair
  <math|<around*|(|\<cal-D\>,\<cal-L\>|)>> where <math|\<cal-D\>> is a
  <math|\<Sigma\>>-structure and <math|\<cal-L\>> (the language of
  constraints) is a set of <math|\<Sigma\>>-formulas closed under conjunction
  and renaming of free variables. <em|Constraint abduction> is a
  formalization of abduction in the context of a constraint domain.
  <em|Simple Constraint Abduction> is the task of solving an implication
  <math|B\<Rightarrow\>C>, where <math|B,C\<in\>\<cal-L\>> are conjunctions
  of atoms. The constraint abduction answer <math|A\<in\>\<cal-L\>> is a
  solution to the implication <math|B\<Rightarrow\>C> if and only if
  <math|\<cal-D\>\<vDash\><around*|(|A\<wedge\>B|)>\<Rightarrow\>C> and
  <math|\<cal-D\>\<vDash\>\<exists\>FV<around*|(|A,B|)>.A\<wedge\>B>, where
  <math|FV<around*|(|\<cdummy\>|)>> finds the free variables of an
  expression. <math|\<cal-D\>> and <math|B> play the role of background
  knowledge -- <math|\<cal-D\>> general, and <math|B> context specific.
  <math|C> plays the role of observation, and <math|A> of explanation. If
  <math|B\<Rightarrow\>C> is a conjunct in a type inference constraint, then
  <math|B> contains the background information about a particular location in
  a program's source code, coming from the pattern matching patterns that
  ``are the case'' -- the location is in their scope. <math|C> contains the
  requirements imposed by the source at that location, for example the
  preconditions of the functions that are called. The answer <math|A>
  explains what needs to be the case for the requirements to be met.
  <em|Joint Constraint Abduction> is the task of solving implications
  <math|\<wedge\><rsub|i><around*|(|B<rsub|i>\<Rightarrow\>C<rsub|i>|)>>,
  where <math|B<rsub|i>,C<rsub|i>\<in\>\<cal-L\>> are conjunctions of atoms
  and <math|\<wedge\><rsub|i>\<varphi\><rsub|i>> stands for
  <math|\<varphi\><rsub|1>\<wedge\>\<ldots\>\<wedge\>\<varphi\><rsub|n>>. The
  answer <math|A\<in\>\<cal-L\>> to this Joint Constraint Abduction problem
  has to meet the conditions: <math|\<cal-D\>\<vDash\><around*|(|A\<wedge\>B<rsub|i>|)>\<Rightarrow\>C<rsub|i>>
  and <math|\<cal-D\>\<vDash\>\<exists\>FV<around*|(|A,B<rsub|i>|)>.A\<wedge\>B<rsub|i>>,
  for all <math|i>. The suitability of joint constraint abduction for GADTs
  type inference was probably first observed by Martin Sulzmann, Tom
  Schrijvers and Peter J. Stuckey, see <cite|SulzmannAbdGADTsRep> (originally
  <cite|SulzmannAbdGADTs>) and <cite|AbdEADTs>.

  Michael Maher has studied constraint abduction for terms
  (<cite|AbductionMaher>, <cite|AbductionSolvMaher>) and linear arithmetic
  (<cite|AbductionLinArithMaher>). Michael Maher and Ge Huang
  <cite|AbductionSolvMaher> provided the basis for our Simple Constraint
  Abduction algorithm for terms, which we describe in this section. An
  abduction answer <math|A> is <em|maximally general>, when for every other
  abduction answer <math|A<rprime|'>>, if
  <math|\<cal-D\>\<vDash\>A\<Rightarrow\>A<rprime|'>>, then
  <math|\<cal-D\>\<vDash\>A<rprime|'>\<Rightarrow\>A>. An abduction answer
  <math|A> to <math|B\<Rightarrow\>C> is <em|fully maximal>, when it is
  maximally general and <math|\<cal-D\>\<vDash\><around*|(|A\<wedge\>B|)>\<Leftrightarrow\><around*|(|B\<wedge\>C|)>>.
  A fully maximal answer does not ``guess'' any fact not entailed by the
  formulas considered.<\float|float|t>
    <\big-table>
      <tabular|<tformat|<table|<row|<cell|<math|pos<around*|(|t,A|)>>
      \ \ returns the set of positions of the term <math|t> in the
      right-hand-side of <math|A>>>|<row|<cell|<math|repl<around*|(|S,A|)>>
      \ replaces all terms in the right-hand-side of <math|A> occurring at a
      position>>|<row|<cell| \ \ \ \ \ \ \ \ \ \ \ \ \ \ in <math|S> by a new
      variable (that is existentially quantified)>>|<row|<cell|<math|next<around*|(|A|)>>
      \ \ \ is the set <math|<around*|{|repl<around*|(|S,A|)><mid|\|>\<varnothing\>\<subsetneq\>S\<subset\>pos<around*|(|t,A|)>,t\<nin\>Vars|}>>>>|<row|<cell|>>|<row|<cell|<strong|algorithm>
      <math|FMA<around*|(|B,C|)>>>>|<row|<cell|
      \ \ <tabular|<tformat|<table|<row|<cell|<strong|if>
      <math|\<vDash\>B\<Rightarrow\>C> <strong|then return>
      <math|\<top\>>>>|<row|<cell|<strong|let> <math|A> be the standard form
      of <math|B\<wedge\>C>>>|<row|<cell|<strong|do>>>|<row|<cell|
      \ \ <tabular|<tformat|<table|<row|<cell|<strong|let> <math|\<cal-A\>>
      be <math|next<around*|(|A|)>>>>|<row|<cell|<strong|if
      ><math|<around*|(|\<forall\>A<rprime|'>\<in\>\<cal-A\>.\<nvDash\>A<rprime|'>\<wedge\>B\<Rightarrow\>C|)>>
      <strong|then return> <math|A>>>|<row|<cell|<strong|choose>
      <math|A\<in\>\<cal-A\>> such that <math|\<vDash\>A\<wedge\>B\<Rightarrow\>C>>>>>>>>>>>>>|<row|<cell|>>|<row|<cell|<strong|algorithm
      JCA-Solve>>>|<row|<cell| \ \ <tabular|<tformat|<table|<row|<cell|<math|\<cal-M\>\<assign\><around*|{|\<wedge\><rsub|i=1><rsup|n>A<rsub|i><mid|\|>A<rsub|i><with|mode|text|
      is a maximally general answer of the >i<with|mode|text|'th SCA
      problem>|}>>>>|<row|<cell|<strong|while >exist <math|A\<in\>\<cal-M\>>
      and <math|i> s.t. <math|A\<wedge\>B<rsub|i>> is unsatisfiable in
      <math|\<cal-D\>>, <math|\<cal-M\>\<assign\>\<cal-M\>\\<around*|{|A|}>>>>|<row|<cell|<strong|if
      ><math|\<cal-M\>=\<varnothing\>> <strong|then return
      ><math|\<bot\>>>>|<row|<cell|<strong|while> exist
      <math|A,A<rprime|'>\<in\>\<cal-M\>> s.t.
      <math|\<cal-D\>\<vDash\>A\<Rightarrow\>A<rprime|'>> and
      <math|A\<neq\>A<rprime|'>>, <math|\<cal-M\>\<assign\>\<cal-M\>\\<around*|{|A|}>>>>|<row|<cell|<strong|return
      ><math|\<cal-M\>>>>>>>>>>>><label|HerbAbdAlg>
    </big-table|SCA algorithm for computing fully maximal answers, JCA
    algorithm>
  </float>

  Let <math|\<cal-D\>=\<cal-T\>=T<around*|(|\<Sigma\>,Vars|)>> be the free
  algebra of terms over signature <math|\<Sigma\>> with variables <math|Vars>
  and <math|\<cal-L\>=\<cal-F\>\<cal-T\><rsub|\<exists\>>> be existentially
  quantified conjunctions of equations. In Table <reference|HerbAbdAlg> we
  quote the fully maximal abduction algorithm from <cite|AbductionSolvMaher>,
  Figure 4, page 13. The following theorem is Theorem 6 from
  <cite|AbductionSolvMaher>, page 14.

  <\theorem>
    <label|MaherHerbSolve>Algorithm <math|FMA> outputs all fully maximal
    answers to the SCA problem over <math|\<cal-F\>\<cal-T\><rsub|\<exists\>>>
    and terminates.
  </theorem>

  Now let us turn to the joint problem. The following proposition is
  Proposition 8 from <cite|AbductionMaher>, page 9. In Table
  <reference|HerbAbdAlg> we quote the corresponding algorithm
  <strong|JCA-Solve>.

  <\proposition>
    <label|MaherJCASolve>Consider a joint constraint abduction problem
    composed of <math|n> SCA component problems. Let
    <math|\<cal-A\>=<around*|{|\<wedge\><rsub|i=1><rsup|n>A<rsub|i><mid|\|>A<rsub|i><with|mode|text|
    is a maximally general answer of the >i<with|mode|text|'th SCA
    problem>|}>>. If <math|A> is a maximally general answer to the JCA
    problem then <math|A\<in\>\<cal-A\>>. The JCA problem has no answers iff
    no constraint in <math|\<cal-A\>> is an answer.
  </proposition>

  <subsection|Relevance>

  Sulzmann, Schrijvers and Stuckey <cite|SulzmannAbdGADTs> and
  <cite|AbdEADTs> inspired the approach taken by the <name|InvarGenT>
  project. Maher and Huang <cite|AbductionSolvMaher> forms a basis of our
  simple constraint abduction solver for the Herbrand domain. It turns out
  however, that fully maximal answers are insufficient for type and invariant
  inference. We go beyond the algorithms from Table <reference|HerbAbdAlg> as
  follows.

  We extend the <math|FMA<around*|(|B,C|)>> algorithm by considering atoms
  <math|x<wide|=|\<dot\>>y>, where <math|x,y\<in\>Vars>,
  <math|x<wide|=|\<dot\>>t<rsub|x>> and <math|y<wide|=|\<dot\>>t<rsub|y>>
  belong to the solved form of <math|B\<wedge\>C>,
  <math|t<rsub|x>\<nin\>Vars> and <math|t<rsub|y>\<nin\>Vars>, and
  <math|t<rsub|x><wide|=|\<dot\>>t<rsub|y>> is satisfiable. These conditions
  limit the number of pairs of variables to consider. There are many
  potential SCA problems where we still will not be able to find an answer,
  but they appear not to be relevant: we have not encountered a practical
  example where the algorithm would need further extension.

  We extend the <strong|JCA-Solve> algorithm by using the partial solution,
  i.e. starting from <math|B\<wedge\>C\<wedge\><rsub|i=1><rsup|k-1>A<rsub|i>>
  instead of <math|B\<wedge\>C>, when solving the <math|k>th component SCA
  problem.

  We propose a novel algorithm (not based on <cite|AbductionLinArithMaher>)
  for constraint abduction for the linear arithmetic domain.<new-page>

  <chapter|The Type System>

  The main idea of this work is that useful properties of functions can be
  generated by solving ordinary-looking constraints under a quantifier prefix
  (without resorting to Herbrandization), derived via a GADTs-based type
  system. The content of Sections <reference|TypSys> and
  <reference|TypInfCns> is based on Simonet and Pottier
  <cite|simonet-pottier-hmg-toplas>. To our knowledge, the idea behind the
  <name|NegClause> rule is novel. The content of Sections <reference|ExTypes>
  and <reference|ExTypesCns> is novel.

  We start by introducing notation. By the bar <math|<wide|e|\<bar\>>> we
  denote a sequence (or a set, depending on context) of elements <math|e>, by
  <math|#> we mean disjointedness. With a free index <math|i>,
  <math|<wide|e<rsub|i>|\<bar\>>> means <math|<around|(|e<rsub|1>,\<ldots\>,e<rsub|n>|)>>
  for some <math|n> associated with the index <math|i>; i.e.
  <math|<wide|e<rsub|i>|\<bar\>>> or <math|<wide|e|\<bar\>>> is a sequence
  <math|<around|(|e<rsub|1>,\<ldots\>,e<rsub|n>|)>> and <math|e<rsub|i>> is
  an <math|i>th element of the sequence. Similarly,
  <math|\<wedge\><rsub|i>\<Phi\><rsub|i>> denotes
  <math|\<Phi\><rsub|1>\<wedge\>\<ldots\>\<wedge\>\<Phi\><rsub|n>>. For
  convenience, we treat a conjunction of atoms
  <math|\<wedge\><rsub|i>c<rsub|i>> as a set of atoms
  <math|<around*|{|c<rsub|1>,\<ldots\>,c<rsub|n>|}>>. Sometimes we write
  <math|<wide|v|\<bar\>>> for a sequence of variables related to but distinct
  from a variable <math|v>.

  In some contexts, for a quantifier prefix <math|\<cal-Q\>> we write
  <math|\<cal-Q\>> to denote the set of variables quantified by
  <math|\<cal-Q\>>. Let <math|FV> be a generic function returning the free
  variables of any expression. For a quantifier prefix <math|\<cal-Q\>> and
  variables <math|x,y> in <math|\<cal-Q\>>, by
  <math|x\<less\><rsub|\<cal-Q\>>y> we denote that <math|x> is to the left of
  <math|y> in <math|\<cal-Q\>> and they are separated by a quantifier
  alternation, by <math|x\<leqslant\><rsub|\<cal-Q\>>y> that it is not the
  case that <math|y\<less\><rsub|\<cal-Q\>>x>.

  By <math|\<Phi\><around|[|<wide|\<alpha\>|\<bar\>>\<assign\><wide|t|\<bar\>>|]>>,
  <math|\<Phi\><around|[|<wide|\<alpha\>\<assign\>t|\<bar\>>|]>>, or
  <math|\<Phi\><around|[|\<alpha\><rsub|1>\<assign\>t<rsub|1>;\<ldots\>;\<alpha\><rsub|n>\<assign\>t<rsub|n>|]>>,
  we denote a substitution of terms <math|<wide|t|\<bar\>>> for corresponding
  variables <math|<wide|\<alpha\>|\<bar\>>> in the formula <math|\<Phi\>>
  (where <math|<wide|\<alpha\>|\<bar\>>> and <math|<wide|t|\<bar\>>> are
  finite sequences of the same length). Equality with a dot
  <math|<wide|=|\<dot\>>> is an object-level equality, i.e. a relation in the
  language <math|\<cal-L\>> introduced below. Equality <math|=> is a
  meta-level equality, usually syntactic equality on terms or formulas. By
  <math|<wide|s|\<bar\>><wide|=|\<dot\>><wide|t|\<bar\>>> we denote
  <math|\<wedge\><rsub|i>s<rsub|i><wide|=|\<dot\>>t<rsub|i>>, where
  <math|<wide|s|\<bar\>>=<around*|(|s<rsub|1>,\<ldots\>,s<rsub|n>|)>> and
  <math|<wide|t|\<bar\>>=<around*|(|t<rsub|1>,\<ldots\>,t<rsub|n>|)>> for
  some <math|n>. We use letters <math|R,S,U> to denote substitutions. For a
  substitution <math|S=<around|[|<wide|\<alpha\>|\<bar\>>\<assign\><wide|t|\<bar\>>|]>>,
  we write substitution application as <math|S<around*|(|\<Phi\>|)>=\<Phi\><around|[|<wide|\<alpha\>|\<bar\>>\<assign\><wide|t|\<bar\>>|]>>;
  we write <math|<wide|S|\<dot\>>=<wide|\<alpha\>|\<bar\>><wide|=|\<dot\>><wide|t|\<bar\>>>;
  and we denote the substitution <math|S> corresponding to a formula
  <math|A=<wide|S|\<dot\>>=<wide|\<alpha\>|\<bar\>><wide|=|\<dot\>><wide|t|\<bar\>>>
  by <math|<wide|A|~>>. We say that a substitution
  <with|mode|math|<around|[|<wide|\<alpha\>|\<bar\>>\<assign\><wide|t|\<bar\>>|]>>
  agrees with a quantifier prefix <math|\<cal-Q\>>, when
  <math|\<vDash\>\<cal-Q\>.<wide|\<alpha\>|\<bar\>><wide|=|\<dot\>><wide|t|\<bar\>>>
  and in case of <math|\<alpha\><rsub|1><wide|=|\<dot\>>\<alpha\><rsub|2>\<in\><wide|\<alpha\>|\<bar\>><wide|=|\<dot\>><wide|t|\<bar\>>>
  for variables <math|\<alpha\><rsub|1>,\<alpha\><rsub|2>>, we have
  <math|\<alpha\><rsub|2>\<leqslant\><rsub|\<cal-Q\>>\<alpha\><rsub|1>>.
  Syntactically, this means that <math|\<alpha\><rsub|i>> is not to the right
  of variables in <math|t<rsub|i>>: <math|\<forall\>\<beta\>\<in\>FV<around*|(|t<rsub|i>|)>>,
  <math|\<alpha\><rsub|i>\<nless\><rsub|\<cal-Q\>>\<beta\>>. We use letters
  <math|\<tau\>,r,s,t,u> to denote terms and letters
  <math|\<alpha\>,\<beta\>,v,x,y,z> to denote variables.

  <section|The Language of Constraints>

  We are interested in a multi-sorted first order language
  <math|\<cal-L\><rsub|1>> with equality, interpreted in a given, fixed model
  <math|\<cal-M\>>. Even when we write <math|\<vDash\>\<Phi\>>, it is usually
  a shortcut notation for validity of a formula <math|\<Phi\>> in the model
  <math|\<cal-M\>>: <math|\<cal-M\>\<vDash\>\<Phi\>>. The sort of terms or
  ``types proper'', denoted <math|s<rsub|type>> and <verbatim|type> in the
  concrete syntax of <name|InvarGenT>, plays a special role. In the current
  presentation, we abstract from details of the language, posing the
  necessary properties as assumptions.<\float|float|t>
    <\big-table>
      <\equation*>
        <tabular|<tformat|<cwith|7|7|2|2|cell-halign|r>|<cwith|8|8|2|2|cell-halign|r>|<table|<row|<cell|\<tau\><rsub|type>>|<cell|\<assign\>>|<cell|v<rsub|type><space|0.6spc>\|<space|0.6spc>\<tau\><rsub|type>\<rightarrow\>\<tau\><rsub|type><space|0.6spc>\|<space|0.6spc>\<varepsilon\><around*|(|<wide|\<tau\>|\<bar\>>|)><space|0.6spc>\|<space|0.6spc>Num<around*|(|\<tau\><rsub|num>|)>>>|<row|<cell|\<tau\><rsub|num>>|<cell|\<assign\>>|<cell|v<rsub|num><space|0.6spc>\|<space|0.6spc>k*\<tau\><rsub|num><space|0.6spc>\|<space|0.6spc>\<tau\><rsub|num>+\<tau\><rsub|num><space|0.6spc>\|<space|0.6spc>k>>|<row|<cell|k>|<cell|\<assign\>>|<cell|0<space|0.6spc>\|<space|0.6spc>1<space|0.6spc>\|<space|0.6spc>-1<space|0.6spc>\|<space|0.6spc>2<space|0.6spc>\|<space|0.6spc>-2<space|0.6spc>\|<space|0.6spc>\<ldots\>>>|<row|<cell|\<tau\>>|<cell|\<assign\>>|<cell|\<tau\><rsub|type><space|0.6spc>\|<space|0.6spc>\<tau\><rsub|num>>>|<row|<cell|a<rsub|type>>|<cell|\<assign\>>|<cell|\<tau\><rsub|type><wide|=|\<dot\>>\<tau\><rsub|type>>>|<row|<cell|a<rsub|num>>|<cell|\<assign\>>|<cell|\<tau\><rsub|num><wide|=|\<dot\>>\<tau\><rsub|num><space|0.6spc>\|<space|0.6spc>\<tau\><rsub|num>\<leq\>\<tau\><rsub|num>>>|<row|<cell|>|<cell|\|>|<cell|v<rsub|num><wide|=|\<dot\>>max<around*|(|\<tau\><rsub|num>,\<tau\><rsub|num>|)><space|0.6spc>\|<space|0.6spc>v<rsub|num><wide|=|\<dot\>>min<around*|(|\<tau\><rsub|num>,\<tau\><rsub|num>|)>>>|<row|<cell|>|<cell|\|>|<cell|v<rsub|num>\<leq\>max<around*|(|\<tau\><rsub|num>,\<tau\><rsub|num>|)><space|0.6spc>\|<space|0.6spc>min<around*|(|\<tau\><rsub|num>,\<tau\><rsub|num>|)>\<leq\>v<rsub|num>>>|<row|<cell|a>|<cell|\<assign\>>|<cell|a<rsub|type><space|0.6spc>\|<space|0.6spc>a<rsub|num>\|\<chi\><around*|(|\<tau\><rsub|type>|)>\|\<chi\><rsub|K><around*|(|\<tau\><rsub|type>,\<tau\><rsub|type>|)>>>|<row|<cell|v>|<cell|\<assign\>>|<cell|v<rsub|type><space|0.6spc>\|<space|0.6spc>v<rsub|num>=\<alpha\><rsub|i><space|0.6spc>\|<space|0.6spc>\<beta\><rsub|i><space|0.6spc>\|<space|0.6spc>\<ldots\>>>|<row|<cell|\<sigma\>>|<cell|\<assign\>>|<cell|\<forall\>v<rsub|type><rsup|1><around*|[|\<exists\><wide|v|\<bar\>>.<wide|a|\<bar\>>|]>.v<rsub|type><rsup|1><space|0.6spc>\|<space|0.6spc>\<forall\><wide|v|\<bar\>><around*|[|<wide|a|\<bar\>>|]>.\<tau\><rsub|type>>>>>>
      </equation*>

      <label|TypeSyn>
    </big-table|Abstract syntax of types and type schemes>
  </float>

  In Appendix <reference|ChapProofs>, we introduce a Henkin semantics for
  existential second order logic <math|\<cal-L\>> extending
  <math|\<cal-L\><rsub|1>> by predicate symbols
  <math|\<chi\><around*|(|\<cdummy\>|)>> that we call <em|predicate
  variables>. <math|\<cal-L\>> is tailored to our needs of invariant and
  postcondition inference. Let <math|PV<around|(|\<cdummy\>|)>> be the set of
  predicate variables in any expression. We define <em|solved form formulas>
  to be existentially quantified conjunctions of atoms
  <math|\<exists\><wide|\<alpha\>|\<bar\>>.A> without predicate variables. An
  interpretation of predicate variables <math|\<cal-I\>> substitutes
  predicate variables by solved form formulas.

  In Table <reference|TypeSyn>, we present a particular instance of
  <math|\<cal-L\><rsub|1>>, introducing a numerical constraint domain. The
  terms of <math|\<cal-L\><rsub|1>> are <math|\<tau\>>, and <math|a> are the
  atomic formulas, as currently implemented in <name|InvarGenT>. There are
  two sorts: <math|s<rsub|type>> with terms <math|\<tau\><rsub|type>> and
  relations <math|a<rsub|type>>, and <math|s<rsub|num>> with terms
  <math|\<tau\><rsub|num>> and relations <math|a<rsub|num>>. Variables of
  distinct sorts are disjoint; <math|v<rsub|s>> stands for variables of sort
  <math|s>. The remaining entry <math|\<sigma\>> is built on top of
  <math|\<cal-L\><rsub|1>> rather than part of it. The notation
  <math|v<rsub|type><rsup|1>> stands for the same variable of sort
  <math|s<rsub|type>> in both occurrences. Besides <math|\<tau\>>, we also
  use the letter <math|t> for terms of <math|\<cal-L\><rsub|1>>. Rarely, in
  interests of readability we use the letters <math|x,y,z> besides
  <math|\<alpha\>,\<beta\>> to denote variables of <math|\<cal-L\><rsub|1>>.

  <section|The Type System with GADTs><label|TypSys>

  By <em|types> <math|\<tau\>> we mean terms of sort <math|s<rsub|type>>.
  Define <em|type schemes> <math|\<sigma\>> as
  <math|\<forall\>\<beta\><around|[|D|]>.\<beta\>>, where <math|D> is either
  a solved form formula <math|\<exists\><wide|\<alpha\>|\<bar\>>.E> or a
  predicate variable <math|\<chi\><around*|(|\<beta\>|)>>, and
  <math|\<beta\>> is a variable of sort <math|s<rsub|type>>. A <em|simple
  environment> (or <em|monomorphic environment>) maps variables <math|x> to
  types <math|\<tau\>>. An <em|environment> (or <em|polymorphic environment>)
  maps variables <math|x> to type schemes <math|\<sigma\>>. When a simple
  environment is appended to an environment, we identify <math|\<tau\>> and
  <math|\<forall\>\<beta\><around|[|\<beta\><wide|=|\<dot\>>\<tau\>|]>.\<beta\>>
  for <math|\<beta\>\<nin\>FV<around|(|\<tau\>|)>>. When operations
  pertaining to formulas are applied to a type scheme
  <math|\<forall\>\<beta\><around|[|\<exists\><wide|\<alpha\>|\<bar\>>.E|]>.\<beta\>>
  or <math|\<forall\>\<beta\><around|[|\<chi\><around|(|\<beta\>|)>|]>.\<beta\>>,
  they are performed on the formula <math|\<exists\><wide|\<alpha\>|\<bar\>>.E>
  or <math|\<chi\><around|(|\<beta\>|)>>.
  <math|\<forall\>\<beta\><wide|\<alpha\>|\<bar\>><around|[|b<wide|=|\<dot\>>\<tau\>\<wedge\>E|]>.\<tau\>>
  is a notational variant of <math|\<forall\>\<beta\><around|[|\<exists\><wide|\<alpha\>|\<bar\>>.E|]>.\<beta\>>.
  When operations pertaining to type schemes (types) are applied to (simple)
  environments <math|\<Gamma\>>, they are performed on the image of
  <math|\<Gamma\>>. Define <em|environment fragments> <math|\<Delta\>> to be
  triples <math|\<exists\><wide|\<alpha\>|\<bar\>><around|[|D|]>.\<Gamma\>>
  of variables <math|<wide|\<alpha\>|\<bar\>>>, atomic conjunctions <math|D>
  in <math|\<cal-L\>> and simple environment <math|\<Gamma\>>.

  Table <reference|ExprSyn> presents expressions currently in
  <name|InvarGenT>, more domain-specific <math|<with|math-font-series|bold|assert>>
  and <math|<with|math-font-series|bold|when>> clauses can be added. The
  table defines several expression languages, underlying the corresponding
  type systems: <math|MMG<around*|(|X|)>>, its supersets -- in terms of
  expressions <math|e> and system rules -- <math|MMG<around*|(|num|)>> and
  <math|MMG<rsub|\<exists\>><around*|(|X|)>>, and
  <math|MMG<rsub|\<exists\>><around*|(|num|)>> which is a union of
  <math|MMG<around*|(|num|)>> and <math|MMG<rsub|\<exists\>><around*|(|X|)>>.
  The domain-independent languages <math|MMG<around*|(|X|)>> and
  <math|MMG<rsub|\<exists\>><around*|(|X|)>> are extended with some
  expressions specific to the numerical sort in <math|MMG<around*|(|num|)>>
  and <math|MMG<rsub|\<exists\>><around*|(|num|)>>. The language
  <math|\<cal-L\><rsub|1>> and model <math|\<cal-M\>> for
  <math|MMG<around*|(|X|)>> and <math|MMG<rsub|\<exists\>><around*|(|X|)>>
  are arbitrary. We fix the language <math|\<cal-L\><rsub|1>> for
  <math|MMG<around*|(|num|)>> and <math|MMG<rsub|\<exists\>><around*|(|num|)>>
  as having besides <math|s<rsub|type>> only a linear arithmetic sort. We
  discuss the type system <math|MMG<around*|(|num|)>> shortly, and extend it
  to <math|MMG<rsub|\<exists\>><around*|(|num|)>> in Section
  <reference|ExTypes>. Disjunctive patterns are not yet implemented in
  <name|InvarGenT>, we omit them in the presentation for
  brevity.<\float|float|t>
    <\big-table>
      <\math>
        p\<assign\>x<space|0.6spc>\|<space|0.6spc>0<space|0.6spc>\|<space|0.6spc>1<space|0.6spc>\|<space|0.6spc>p\<wedge\>p<space|0.6spc>\|<space|0.6spc>K
        <wide|p|\<bar\>>

        c\<assign\>

        <with|mode|text| \ >MMG<around*|(|X|)>:

        <with|mode|text| \ \ \ \ \ \ >p.e

        <with|mode|text| \ >MMG<around*|(|num|)>:

        <with|mode|text| \ \ \ \ \ >\|<space|0.6spc>p
        <text|<with|font-shape|condensed|<strong|when>>>
        <wide|e\<leqslant\>e|\<bar\>>.e

        e\<assign\>

        <with|mode|text| \ >MMG<around*|(|X|)>:

        <with|mode|text| \ \ \ \ \ >x<space|0.6spc>\|<space|0.6spc>K
        <wide|e|\<bar\>><space|0.6spc>\|<space|0.6spc><text|<with|font-shape|condensed|<strong|let>>>
        p=e <text|<with|font-shape|condensed|<strong|in>>>
        e<space|0.6spc>\|<space|0.6spc>e e<space|0.6spc>\|<space|0.6spc>\<lambda\><around*|(|<wide|c|\<bar\>>|)><space|0.6spc>\|<space|0.6spc><text|<with|font-shape|condensed|<strong|let
        rec>>> x=e <text|<with|font-shape|condensed|<strong|in>>> e

        <with|mode|text| \ \ \ \ >\|<space|0.6spc><text|<with|font-shape|condensed|<strong|assert
        false>>>

        <with|mode|text| \ \ \ \ >\|<space|0.6spc><text|<with|font-shape|condensed|<strong|assert
        type>>> e=e;e

        <with|mode|text| \ \ \ \ >\|<space|0.6spc><text|<with|font-shape|condensed|<strong|runtime
        failure>>> e

        <with|mode|text| \ >MMG<around*|(|num|)>:

        <with|mode|text| \ \ \ \ >\|<space|0.6spc><text|<with|font-shape|condensed|<strong|assert
        num>>> e\<leqslant\>e;e

        <with|mode|text| \ >MMG<rsub|\<exists\>><around*|(|X|)>:

        <with|mode|text| \ \ \ \ >\|<space|0.6spc>\<lambda\><around*|[|K|]><wide|c|\<bar\>>

        <with|mode|text| \ \ \ \ >\|<space|0.6spc>\<lambda\><rsub|K><wide|c|\<bar\>>
      </math>

      <label|ExprSyn>
    </big-table|Abstract syntax of expressions>
  </float>

  First, we present the type system in the standard, natural deduction style.
  The <em|type judgment> <math|C,\<Gamma\>\<vdash\>e:\<tau\>> or
  <math|C,\<Gamma\>\<vdash\>e:\<sigma\>> is composed of a formula <math|C>
  without predicate variables, an environment <math|\<Gamma\>>, an expression
  <math|e> and a type <math|\<tau\>> or type scheme <math|\<sigma\>>. Not
  mentioned explicitly is a set of data constructors <math|\<Sigma\>>, which
  is fixed when typing an expression.<\float|float|t>
    <\big-table>
      Syntax-directed:

      <tabular|<tformat|<cwith|5|5|3|3|cell-halign|l>|<cwith|5|5|1|1|cell-col-span|2>|<table|<row|<cell|<name|p-Empty>>|<cell|<name|p-Wild>>|<cell|<name|p-Var>>>|<row|<cell|<math|C\<vdash\>0:\<tau\>\<longrightarrow\>\<exists\>\<varnothing\><around|[|\<b-F\>|]><around|{||}>>>|<cell|<math|C\<vdash\>1:\<tau\>\<longrightarrow\>\<exists\>\<varnothing\><around|[|\<b-T\>|]><around|{||}>>
      \ \ \ \ \ >|<cell|<math|C\<vdash\>x:\<tau\>\<longrightarrow\>\<exists\>\<varnothing\><around|[|\<b-T\>|]><around|{|x\<mapsto\>\<tau\>|}>>>>|<row|<cell|>|<cell|>|<cell|>>|<row|<cell|<name|p-Cstr>>|<cell|>|<cell|<name|p-And>>>|<row|<cell|<math|<large|<frac|<tabular|<tformat|<table|<row|<cell|\<forall\>i>|<cell|C\<wedge\>D\<vdash\>p<rsub|i>:\<tau\><rsub|i>\<longrightarrow\>\<Delta\><rsub|i>>|<cell|K\<colons\>\<forall\><wide|\<alpha\>|\<bar\>><wide|\<beta\>|\<bar\>><around|[|D|]>.\<tau\><rsub|1>\<times\>\<ldots\>\<times\>\<tau\><rsub|n>\<rightarrow\>\<varepsilon\><around|(|<wide|\<alpha\>|\<bar\>>|)>>|<cell|<wide|\<beta\>|\<bar\>>#FV<around|(|C|)>>>>>>|C\<vdash\>K
      p<rsub|1>\<ldots\>p<rsub|n>:\<varepsilon\><around|(|<wide|\<alpha\>|\<bar\>>|)>\<longrightarrow\>\<exists\><wide|\<beta\>|\<bar\>><around|[|D|]><around|(|\<Delta\><rsub|1>\<times\>\<ldots\>\<times\>\<Delta\><rsub|n>|)>>>>>|<cell|>|<cell|<math|<large|<frac|\<forall\>i<with|mode|text|
      \ ><space|0.6spc>C\<vdash\>p<rsub|i>:\<tau\>\<longrightarrow\>\<Delta\><rsub|i>|C\<vdash\>p<rsub|1>\<wedge\>p<rsub|2>:\<tau\>\<longrightarrow\>\<Delta\><rsub|1>\<times\>\<Delta\><rsub|2>>>>>>>>>

      \;

      \;

      Non-syntax-directed:

      <tabular|<tformat|<cwith|2|2|1|1|cell-halign|l>|<cwith|2|2|3|3|cell-halign|l>|<table|<row|<cell|<name|p-EqIn>>|<cell|>|<cell|<name|p-SubOut>>|<cell|>|<cell|<name|p-Hide>>>|<row|<cell|<math|<large|<frac|<tabular|<tformat|<table|<row|<cell|C\<vdash\>p:\<tau\><rprime|'>\<longrightarrow\>\<Delta\>>>|<row|<cell|C\<vDash\>\<tau\><wide|=|\<dot\>>\<tau\><rprime|'>>>>>>|C\<vdash\>p:\<tau\>\<longrightarrow\>\<Delta\>>>>>|<cell|
      \ \ >|<cell|<math|<large|<frac|<tabular|<tformat|<table|<row|<cell|C\<vdash\>p:\<tau\>\<longrightarrow\>\<Delta\><rprime|'>>>|<row|<cell|C\<vDash\>\<Delta\><rprime|'>\<leqslant\>\<Delta\>>>>>>|C\<vdash\>p:\<tau\>\<longrightarrow\>\<Delta\>>>>>|<cell|
      \ \ >|<cell|<math|<large|<frac|<tabular|<tformat|<table|<row|<cell|C\<vdash\>p:\<tau\>\<longrightarrow\>\<Delta\>>>|<row|<cell|<wide|\<alpha\>|\<bar\>>#FV<around|(|\<tau\>,\<Delta\>|)>>>>>>|\<exists\><wide|\<alpha\>|\<bar\>>.C\<vdash\>p:\<tau\>\<longrightarrow\>\<Delta\>>>>>>>>><label|TypRulPat>
    </big-table|Typing rules for <math|MMG<around*|(|X|)>><math|: patterns>>
  </float><\float|float|t>
    <\big-table>
      Syntax-directed:

      <tabular|<tformat|<cwith|11|11|1|1|cell-halign|l>|<cwith|11|11|1|1|cell-valign|B>|<cwith|11|11|3|3|cell-halign|l>|<cwith|11|11|3|3|cell-valign|B>|<cwith|14|14|1|1|cell-halign|l>|<cwith|14|14|1|1|cell-valign|B>|<cwith|14|14|3|3|cell-halign|l>|<cwith|14|14|3|3|cell-valign|B>|<cwith|5|5|3|3|cell-halign|c>|<table|<row|<cell|<name|Var>>|<cell|>|<cell|<name|Cstr>>>|<row|<cell|<math|<large|<frac|<tabular|<tformat|<table|<row|<cell|\<Gamma\><around|(|x|)>=\<forall\>\<beta\><around|[|\<exists\><wide|\<alpha\>|\<bar\>>.D|]>.\<beta\>>|<cell|C\<vDash\>D>>>>>|C,\<Gamma\>\<vdash\>x:\<beta\>>>>>|<cell|>|<cell|<large|<math|<frac|<tabular|<tformat|<table|<row|<cell|\<forall\>i
      C,\<Gamma\>\<vdash\>e<rsub|i>:\<tau\><rsub|i><with|mode|text|
      \ \ \ \ \ >C\<vDash\>D>>|<row|<cell|K\<colons\>\<forall\><wide|\<alpha\>|\<bar\>><wide|\<beta\>|\<bar\>><around|[|D|]>.\<tau\><rsub|1>\<ldots\>\<tau\><rsub|n>\<rightarrow\>\<varepsilon\><around|(|<wide|\<alpha\>|\<bar\>>|)>>>>>>|C,\<Gamma\>\<vdash\>K
      e<rsub|1>\<ldots\>e<rsub|n>:\<varepsilon\><around|(|<wide|\<alpha\>|\<bar\>>|)>>>>>>|<row|<cell|>|<cell|>|<cell|>>|<row|<cell|<name|App>>|<cell|>|<cell|<name|Abs>>>|<row|<cell|<large|<math|<frac|<tabular|<tformat|<table|<row|<cell|C,\<Gamma\>\<vdash\>e<rsub|1>:\<tau\><rprime|'>\<rightarrow\>\<tau\>>>|<row|<cell|C,\<Gamma\>\<vdash\>e<rsub|2>:\<tau\><rprime|'>>>>>>|C,\<Gamma\>\<vdash\>e<rsub|1>
      e<rsub|2>:\<tau\>>>>>|<cell|>|<cell|<large|<math|<frac|\<forall\>i
      C,\<Gamma\>\<vdash\>c<rsub|i>:\<tau\><rsub|1>\<rightarrow\>\<tau\><rsub|2>|C,\<Gamma\>\<vdash\>\<lambda\><around|(|c<rsub|1>\<ldots\>c<rsub|n>|)>:\<tau\><rsub|1>\<rightarrow\>\<tau\><rsub|2>>>>>>|<row|<cell|>|<cell|>|<cell|>>|<row|<cell|<name|LetIn>>|<cell|>|<cell|<name|LetRec>>>|<row|<cell|<large|<math|<frac|C,\<Gamma\>\<vdash\>\<lambda\><around*|(|p.e<rsub|2>|)>
      e<rsub|1>:\<tau\>|C,\<Gamma\>\<vdash\><text|<with|font-shape|condensed|<strong|let>>>
      p=e<rsub|1> <text|<with|font-shape|condensed|<strong|in>>>
      e<rsub|2>:\<tau\>>>>>|<cell|>|<cell|<math|<large|<frac|<tabular|<tformat|<table|<row|<cell|C,\<Gamma\><rprime|'>\<vdash\>e<rsub|1>:\<sigma\>>|<cell|C,\<Gamma\><rprime|'>\<vdash\>e<rsub|2>:\<tau\>>>|<row|<cell|\<sigma\>=\<forall\>\<beta\><around|[|\<exists\><wide|\<alpha\>|\<bar\>>.D|]>.\<beta\>>|<cell|\<Gamma\><rprime|'>=\<Gamma\><around|{|x\<mapsto\>\<sigma\>|}>>>>>>|C,\<Gamma\>\<vdash\><text|<with|font-shape|condensed|<strong|let
      rec>>> x=e<rsub|1> <text|<with|font-shape|condensed|<strong|in>>>
      e<rsub|2>:\<tau\>>>>>>|<row|<cell|>|<cell|>|<cell|>>|<row|<cell|<name|AssertLeq>>|<cell|>|<cell|<name|AssertEqty>>>|<row|<cell|<math|<large|<frac|<tabular|<tformat|<cwith|2|2|1|1|cell-valign|c>|<table|<row|<cell|C,\<Gamma\>\<vdash\>e<rsub|1>:Num<around*|(|\<tau\><rsub|1>|)>>|<cell|>|<cell|C\<vDash\>\<tau\><rsub|1>\<leq\>\<tau\><rsub|2>>>|<row|<cell|C,\<Gamma\>\<vdash\>e<rsub|2>:Num<around*|(|\<tau\><rsub|2>|)>>|<cell|>|<cell|C,\<Gamma\>\<vdash\>e<rsub|3>:\<tau\>>>>>>|C,\<Gamma\>\<vdash\><text|<with|font-shape|condensed|<strong|assert
      num>>> e<rsub|1>\<leqslant\>e<rsub|2>;e<rsub|3>:\<tau\><rsub|>>>>>|<cell|>|<cell|<math|<large|<frac|<tabular|<tformat|<cwith|2|2|1|1|cell-valign|c>|<table|<row|<cell|C,\<Gamma\>\<vdash\>e<rsub|1>:\<tau\><rsub|1>>|<cell|>|<cell|C\<vDash\>\<tau\><rsub|1><wide|=|\<dot\>>\<tau\><rsub|2>>>|<row|<cell|C,\<Gamma\>\<vdash\>e<rsub|2>:\<tau\><rsub|2>>|<cell|>|<cell|C,\<Gamma\>\<vdash\>e<rsub|3>:\<tau\>>>>>>|C,\<Gamma\>\<vdash\><text|<with|font-shape|condensed|<strong|assert
      type>>> e<rsub|1>=e<rsub|2>;e<rsub|3>:\<tau\><rsub|>>>>>>|<row|<cell|>|<cell|>|<cell|>>|<row|<cell|<name|AssertFalse>>|<cell|>|<cell|<name|RuntimeFailure>>>|<row|<cell|<large|<math|<frac|<tabular|<tformat|<cwith|1|1|1|1|cell-valign|c>|<table|<row|<cell|C\<vDash\>\<b-F\>>>>>>|C,\<Gamma\>\<vdash\><text|<with|font-shape|condensed|<strong|assert
      false>>>:\<tau\><rsub|>>>>>|<cell|>|<cell|<large|<math|<frac|C,\<Gamma\>\<vdash\>s:String|C,\<Gamma\>\<vdash\><text|<with|font-shape|condensed|<strong|runtime
      failure>>> s:\<tau\><rsub|>>>>>>>>>

      \;

      \;

      Non-syntax-directed:

      <tabular|<tformat|<cwith|2|2|1|1|cell-halign|c>|<cwith|2|2|5|5|cell-halign|l>|<cwith|2|2|7|7|cell-halign|l>|<table|<row|<cell|<name|Gen>>|<cell|>|<cell|<name|Inst>>|<cell|>|<cell|<name|Hide>>|<cell|>|<cell|<name|Equ>>>|<row|<cell|<math|<large|<frac|<tabular|<tformat|<table|<row|<cell|C\<wedge\>D,\<Gamma\>\<vdash\>e:\<beta\>>>|<row|<cell|\<beta\><wide|\<alpha\>|\<bar\>>#FV<around|(|\<Gamma\>,C|)>>>>>>|C\<wedge\>\<exists\>\<beta\><wide|\<alpha\>|\<bar\>>.D,\<Gamma\>\<vdash\>e:\<forall\>\<beta\><around|[|\<exists\><wide|\<alpha\>|\<bar\>>.D|]>.\<beta\>>>>>|<cell|>|<cell|<math|<large|<frac|<tabular|<tformat|<table|<row|<cell|C,\<Gamma\>\<vdash\>e:\<forall\><wide|\<alpha\>|\<bar\>><around|[|D|]>.\<tau\><rprime|'>>>|<row|<cell|C\<vDash\>D<around|[|<wide|\<alpha\>|\<bar\>>\<assign\><wide|\<tau\>|\<bar\>>|]>>>>>>|C,\<Gamma\>\<vdash\>e:\<tau\><rprime|'><around|[|<wide|\<alpha\>|\<bar\>>\<assign\><wide|\<tau\>|\<bar\>>|]>>>>>|<cell|>|<cell|<math|<large|<frac|<tabular|<tformat|<table|<row|<cell|C,\<Gamma\>\<vdash\>e:\<tau\>>>|<row|<cell|<wide|\<alpha\>|\<bar\>>#FV<around|(|\<Gamma\>,\<tau\>|)>>>>>>|\<exists\><wide|\<alpha\>|\<bar\>>.C,\<Gamma\>\<vdash\>e:\<tau\>>>>>|<cell|>|<cell|<math|<large|<frac|<tabular|<tformat|<table|<row|<cell|C,\<Gamma\>\<vdash\>e:\<tau\>>>|<row|<cell|C\<vDash\>\<tau\><wide|=|\<dot\>>\<tau\><rprime|'>>>>>>|C,\<Gamma\>\<vdash\>e:\<tau\><rprime|'>>>>>>|<row|<cell|>|<cell|>|<cell|>|<cell|>|<cell|>|<cell|>|<cell|>>|<row|<cell|<name|DisjElim>>|<cell|>|<cell|<name|FElim>>|<cell|>|<cell|>|<cell|>|<cell|>>|<row|<cell|<math|<large|<frac|<tabular|<tformat|<table|<row|<cell|C,\<Gamma\>\<vdash\>e:\<tau\>>|<cell|>|<cell|D,\<Gamma\>\<vdash\>e:\<tau\>>>>>>|C\<vee\>D,\<Gamma\>\<vdash\>e:\<tau\>>>>>|<cell|>|<cell|<math|<large|<frac||\<b-F\>,\<Gamma\>\<vdash\>e:\<tau\>>>>>|<cell|>|<cell|>|<cell|>|<cell|>>>>>

      <label|TypRulExpr>
    </big-table|Typing rules for <math|MMG<around*|(|num|)>>: expressions>
  </float> If alternative sets of constructors are considered, we make them
  explicit by writing <math|C,\<Gamma\>,\<Sigma\>\<vdash\>e:\<tau\>>. By
  <math|\<cal-I\>> we denote substitutions of predicate variables
  <math|\<chi\>>. By interpretations we mean substitutions leading to ground
  formulas, which have truth value in the model. The intended meaning of the
  type judgment <math|C,\<Gamma\>,\<Sigma\>\<vdash\>e:\<tau\>> is: for every
  interpretation <math|\<cal-I\>,R>, if <math|\<cal-I\>,R\<vDash\>C>, then
  the expression <math|e> has a ground type <math|R<around|(|\<tau\>|)>> in a
  ground environment <math|R<around*|(|\<cal-I\><around|(|\<Gamma\>|)>|)>>;
  and with constructors <math|\<cal-I\><around*|(|\<Sigma\>|)>> but this only
  becomes relevant starting from Section <reference|ExTypes>. We define
  derivability of type judgments in Tables <reference|TypRulExpr> and
  <reference|TypRulClaus>, where we use pattern-related derivations from
  Table <reference|TypRulPat>. For example, the rule <name|Var>:
  <math|<frac|<tabular|<tformat|<table|<row|<cell|\<Gamma\><around|(|x|)>=\<forall\>\<beta\><around|[|\<exists\><wide|\<alpha\>|\<bar\>>.D|]>.\<beta\>>|<cell|C\<vDash\>D>>>>>|C,\<Gamma\>\<vdash\>x:\<beta\>>>
  means that we can derive a type <math|\<beta\>> for <math|x>, with
  properties <math|D>, if the properties <math|D> of <math|\<beta\>> are
  implied by the judgement constraint <math|C>. And the standard rule
  <name|App>: <math|<frac|C,\<Gamma\>\<vdash\>e<rsub|1>:\<tau\><rprime|'>\<rightarrow\>\<tau\><space|1.8spc>C,\<Gamma\>\<vdash\>e<rsub|2>:\<tau\><rprime|'>|C,\<Gamma\>\<vdash\>e<rsub|1>
  e<rsub|2>:\<tau\>>> means that a type for an application <math|e<rsub|1>
  e<rsub|2>> can be derived if a function type can be derived for
  <math|e<rsub|1>> and the corresponding argument type can be derived for
  <math|e<rsub|2>>. The type <math|String> is a datatype; we denote datatypes
  in general by the label <math|\<varepsilon\>>.<\float|float|t>
    <\big-table>
      Clauses

      <tabular|<tformat|<cwith|4|4|1|1|cell-halign|l>|<cwith|7|7|1|1|cell-halign|l>|<table|<row|<cell|<name|Clause>>|<cell|>>|<row|<cell|<math|<large|<frac|<tabular|<tformat|<table|<row|<cell|C\<wedge\>D,\<Gamma\>\<Gamma\><rprime|'>\<vdash\>m<rsub|i>:Num<around*|(|\<tau\><rsup|m<rsub|i>>|)>>|<cell|e\<neq\><with|math-font-series|bold|runtime
      failure>\<wedge\>e\<neq\><text|<with|font-shape|condensed|<strong|assert
      false>>>\<wedge\>\<ldots\>\<wedge\>>>|<row|<cell|C\<wedge\>D,\<Gamma\>\<Gamma\><rprime|'>\<vdash\>n<rsub|i>:Num<around*|(|\<tau\><rsup|n<rsub|i>>|)>>|<cell|e\<neq\>\<lambda\><around*|(|p<rprime|'>\<ldots\>\<lambda\><around*|(|p<rprime|''>.<text|<with|font-shape|condensed|<strong|assert
      false>>>|)>|)>>>|<row|<cell|C\<vdash\>p:\<tau\><rsub|1>\<longrightarrow\>\<exists\><wide|\<beta\>|\<bar\>><around|[|D|]>\<Gamma\><rprime|'><with|mode|text|
      ><wide|\<beta\>|\<bar\>>#FV<around|(|C,\<Gamma\>,\<tau\><rsub|2>|)>>|<cell|C\<wedge\>D\<wedge\><rsub|i>\<tau\><rsup|m<rsub|i>>\<leq\>\<tau\><rsup|n<rsub|i>>,\<Gamma\>\<Gamma\><rprime|'>\<vdash\>e:\<tau\><rsub|2>>>>>>|C,\<Gamma\>\<vdash\>p
      <text|<with|font-shape|condensed|<strong|when>>>
      \<wedge\><rsub|i>m<rsub|i>\<leqslant\>n<rsub|i>.e:\<tau\><rsub|1>\<rightarrow\>\<tau\><rsub|2>>>>>|<cell|>>|<row|<cell|>|<cell|>>|<row|<cell|<name|NegClause>>|<cell|>>|<row|<cell|<math|<large|<frac|<tabular|<tformat|<table|<row|<cell|C\<wedge\>D,\<Gamma\>\<Gamma\><rprime|'>\<vdash\>m<rsub|i>:Num<around*|(|\<tau\><rsup|m<rsub|i>>|)>>|<cell|e=<text|<with|font-shape|condensed|<strong|assert
      false>>>\<vee\>\<ldots\>\<vee\>>>|<row|<cell|C\<wedge\>D,\<Gamma\>\<Gamma\><rprime|'>\<vdash\>n<rsub|i>:Num<around*|(|\<tau\><rsup|n<rsub|i>>|)>>|<cell|e=\<lambda\><around*|(|p<rprime|'>\<ldots\>\<lambda\><around*|(|p<rprime|''>.<text|<with|font-shape|condensed|<strong|assert
      false>>>|)>|)>>>|<row|<cell|C\<vdash\>p:\<tau\><rsub|3>\<longrightarrow\>\<exists\><wide|\<beta\>|\<bar\>><around|[|D|]>\<Gamma\><rprime|'><with|mode|text|
      ><wide|\<beta\>|\<bar\>>#FV<around|(|C,\<Gamma\>,\<tau\><rsub|2>|)>>|<cell|C\<wedge\>D\<wedge\>\<tau\><rsub|1><wide|=|\<dot\>>\<tau\><rsub|3>\<wedge\><rsub|i>\<tau\><rsup|m<rsub|i>>\<leq\>\<tau\><rsup|n<rsub|i>>,\<Gamma\>\<Gamma\><rprime|'>\<vdash\>e:\<tau\><rsub|2>>>>>>|C,\<Gamma\>\<vdash\>p
      <text|<with|font-shape|condensed|<strong|when>>>
      \<wedge\><rsub|i>m<rsub|i>\<leqslant\>n<rsub|i>.e:\<tau\><rsub|1>\<rightarrow\>\<tau\><rsub|2>>>>>|<cell|>>|<row|<cell|>|<cell|>>|<row|<cell|<name|FailClause>>|<cell|>>|<row|<cell|<math|<large|<frac|<tabular|<tformat|<table|<row|<cell|C\<wedge\>D,\<Gamma\>\<Gamma\><rprime|'>\<vdash\>m<rsub|i>:Num<around*|(|\<tau\><rsup|m<rsub|i>>|)>>|<cell|C\<vdash\>p:\<tau\><rsub|3>\<longrightarrow\>\<exists\><wide|\<beta\>|\<bar\>><around|[|D|]>\<Gamma\><rprime|'><with|mode|text|
      ><wide|\<beta\>|\<bar\>>#FV<around|(|C,\<Gamma\>|)>>>|<row|<cell|C\<wedge\>D,\<Gamma\>\<Gamma\><rprime|'>\<vdash\>n<rsub|i>:Num<around*|(|\<tau\><rsup|n<rsub|i>>|)>>|<cell|C\<wedge\>D\<wedge\>\<tau\><rsub|1><wide|=|\<dot\>>\<tau\><rsub|3>\<wedge\><rsub|i>\<tau\><rsup|m<rsub|i>>\<leq\>\<tau\><rsup|n<rsub|i>>,\<Gamma\>\<Gamma\><rprime|'>\<vdash\>s:String>>>>>|C,\<Gamma\>\<vdash\>p
      <text|<with|font-shape|condensed|<strong|when>>>
      \<wedge\><rsub|i>m<rsub|i>\<leqslant\>n<rsub|i>.<text|<with|font-shape|condensed|<strong|runtime
      failure>>> s:\<tau\><rsub|1>\<rightarrow\>\<tau\><rsub|2>>>>>|<cell|>>>>>

      <label|TypRulClaus>
    </big-table|Typing rules for <math|MMG<around*|(|num|)>>: clauses>
  </float>

  Top-level definitions introduce new entries into a global value constructor
  environment <math|\<Sigma\>> or a global variable environment
  <math|\<Gamma\>>. Here we present the most interesting case of a recursive
  definition with a test clause. The type information flow from the test
  <math|e<rsub|2>> to the definition <math|e<rsub|1>> is through the shared
  type scheme <math|\<sigma\>> in <math|\<Gamma\><rprime|'>>. Other cases are
  analogous. In particular, toplevel <verbatim|let> definitions, unlike
  <verbatim|let><math|\<ldots\>><verbatim|in> expressions, are polymorphic,
  and, like <verbatim|let><math|\<ldots\>><verbatim|in> expressions, allow
  binding to a pattern.

  <\equation*>
    <frac|<tabular|<tformat|<table|<row|<cell|C,\<Gamma\><rprime|'>\<vdash\>e<rsub|1>:\<sigma\>>|<cell|C,\<Gamma\><rprime|'>\<vdash\>e<rsub|2>:Bool>|<cell|>>|<row|<cell|\<sigma\>=\<forall\>\<beta\><around|[|\<exists\><wide|\<alpha\>|\<bar\>>.D|]>.\<beta\>>|<cell|\<Gamma\><rprime|'>=\<Gamma\><around|{|x\<mapsto\>\<sigma\>|}>>|<cell|\<cal-M\>\<vDash\>C>>>>>|C,\<Gamma\>\<vdash\><text|<with|font-shape|condensed|<strong|let
    rec>>> x=e<rsub|1> <text|<with|font-shape|condensed|<strong|test>>>
    e<rsub|2>\<longrightarrow\>\<Gamma\><rprime|'>>
  </equation*>

  A <em|data constructor> <math|K> for a <em|datatype> <math|\<varepsilon\>>
  (recall that the sort <math|s<rsub|type>> holds two categories of elements:
  datatypes and function types) has definition
  <math|K\<colons\>\<forall\><wide|\<alpha\>|\<bar\>><wide|\<beta\>|\<bar\>><around|[|D|]>.\<tau\><rsub|1>\<times\>\<ldots\>\<times\>\<tau\><rsub|n>\<rightarrow\>\<varepsilon\><around|(|<wide|\<alpha\>|\<bar\>>|)>>
  where <math|FV<around|(|D,\<tau\><rsub|1>,\<ldots\>,\<tau\><rsub|n>|)>\<subseteq\><wide|\<alpha\>|\<bar\>><wide|\<beta\>|\<bar\>>>.
  <math|D> is a conjunction of atoms.

  At this point the construction <name|LetIn> is a syntactic sugar for single
  branch patterns -- if polymorphic <verbatim|let> is needed, use
  <name|LetRec>. We identify clauses <math|p.e> of <math|MMG<around*|(|X|)>>
  with <math|p <text|<with|font-shape|condensed|<strong|when>>> .e> where the
  type system rules are like the rules for <math|p
  <text|<with|font-shape|condensed|<strong|when>>>
  \<wedge\><rsub|i>m<rsub|i>\<leqslant\>n<rsub|i>>, only with the subformula
  <math|\<wedge\><rsub|i>\<tau\><rsup|m<rsub|i>>\<leq\>\<tau\><rsup|n<rsub|i>>>
  removed (i.e. replaced by <math|\<b-T\>>). Note that <name|Gen> and
  <name|DisjElim> are unrelated to Constraint Generalization we introduce in
  the next chapter. Most of the rules in Tables <reference|TypRulPat> and
  <reference|TypRulExpr> are close to <math|HMG<around*|(|X|)>> rules well
  described in Simonet and Pottier <cite|simonet-pottier-hmg-toplas>. A
  salient difference is the rule <name|NegClause> for clauses whose
  right-hand-side is an <verbatim|assert false> expression. Rather than
  unifying the type of the function argument with the type of the pattern, we
  want the discrepancy between these types be a possible reason of
  unreachability of the pattern matching clause. Without the distinct
  treatment of clauses with <verbatim|assert false> as right-hand-side, the
  <verbatim|assert>-based variant of the <verbatim|equal> example would fail.
  The notation using <math|\<ldots\>> in the rules <name|Clause> and
  <name|NegClause> represents a check whether an expression is a cascade of
  function abstractions with a single case (i.e. a single pattern matching
  branch), the last function abstraction having a function body
  <verbatim|assert false>. The similar rule <name|FailClause> is an ``escape
  hatch'' for cases which cannot be ruled out by the type system.

  An expression <math|e> is <em|well typed> given <math|\<Gamma\>,\<Sigma\>>
  when <math|PV<around*|(|\<Gamma\>,\<Sigma\>|)>=\<varnothing\>> and
  <math|C,\<Gamma\>,\<Sigma\>\<vdash\>e:<no-break>\<sigma\>> holds for some
  satisfiable constraint <math|C>. For simplicity, <name|InvarGenT> only
  admits type and invariant annotations from the user on toplevel
  definitions.

  <section|Type Inference Constraints><label|TypInfCns>

  In Tables <reference|IntermInfPat>, <reference|IntermInf> and
  <reference|IntermInfClaus>, we present type judgments declaratively by
  reducing them to constraints. The presentation is a little bit heavy due to
  explicit capture-avoidance conditions. For example,
  <math|<around*|\<llbracket\>|\<Gamma\>\<vdash\>x:\<tau\>|\<rrbracket\>>=\<exists\>\<beta\><rprime|'><wide|\<alpha\>|\<bar\>><rprime|'>.D<around|[|\<beta\><wide|\<alpha\>|\<bar\>>\<assign\>\<beta\><rprime|'><wide|\<alpha\>|\<bar\>><rprime|'>|]>\<wedge\>\<beta\><rprime|'><wide|=|\<dot\>>\<tau\><text|
  where >\<Gamma\><around|(|x|)>=\<forall\>\<beta\><around|[|\<exists\><wide|\<alpha\>|\<bar\>>.D|]>.\<beta\>,\<beta\><rprime|'><wide|\<alpha\>|\<bar\>><rprime|'>#FV<around|(|\<Gamma\>,<no-break>\<tau\>|)>>
  introduces a constraint over the type <math|\<tau\>> required by the
  properties of <math|x> stored in the environment <math|\<Gamma\>>. The
  constraint <math|<around*|\<llbracket\>|\<Gamma\>\<vdash\>e<rsub|1>
  e<rsub|2>:\<tau\>|\<rrbracket\>>=\<exists\>\<alpha\>.<around*|\<llbracket\>|\<Gamma\>\<vdash\>e<rsub|1>:\<alpha\>\<rightarrow\>\<tau\>|\<rrbracket\>>\<wedge\><around*|\<llbracket\>|\<Gamma\>\<vdash\>e<rsub|2>:\<alpha\>|\<rrbracket\>>,<with|mode|text|
  \ >\<alpha\>#FV<around|(|\<Gamma\>,\<tau\>|)>> for typing the result of
  application of <math|e<rsub|1>> to <math|e<rsub|2>>, imposes a function
  type on <math|e<rsub|1>>, and a type on <math|e<rsub|2>> -- represented by
  the fresh variable <math|\<alpha\>> -- that matches the argument type of
  <math|e<rsub|1>>. The constraint for a pattern matching clause without the
  <verbatim|when> guard becomes more readable:
  <math|<around*|\<llbracket\>|\<Gamma\>\<vdash\>p.e:\<tau\><rsub|1>\<rightarrow\>\<tau\><rsub|2>|\<rrbracket\>>=<around*|\<llbracket\>|\<vdash\>p\<downarrow\>\<tau\><rsub|1>|\<rrbracket\>>\<wedge\>\<forall\><wide|\<beta\>|\<bar\>>.D\<Rightarrow\><around*|\<llbracket\>|\<Gamma\>\<Gamma\><rprime|'>\<vdash\>e:\<tau\><rsub|2>|\<rrbracket\>>>
  where <math|\<exists\><wide|\<beta\>|\<bar\>><around|[|D|]>\<Gamma\><rprime|'>=<around*|\<llbracket\>|\<vdash\>p\<uparrow\>\<alpha\><rsub|3>|\<rrbracket\>>>.
  The premise <math|D> derived from the pattern <math|p> provides
  context-specific information for typing the expression <math|e>.\ 

  The two presentations are equivalent, in the sense of the <em|correctness>
  and <em|completeness> theorems. The proofs are in Section
  <reference|GADTProofs>.

  <\theorem>
    <label|InfCorrExpr><em|Correctness> (expressions). For all environments
    <math|\<Gamma\>>, expressions <math|e> and types <math|\<tau\>>,
    <math|<around*|\<llbracket\>|\<Gamma\>\<vdash\>e:\<tau\>|\<rrbracket\>>,\<Gamma\>\<vdash\>e:\<tau\>>
    is derivable.
  </theorem>

  <\theorem>
    <label|InfComplExpr><em|Completeness> (expressions). Let
    <math|\<cal-L\><rsub|1>> be a first order language with equality
    <math|<wide|=|\<dot\>>> and a model <math|\<cal-M\>>. Let
    <math|\<cal-L\>> be an extension of <math|\<cal-L\><rsub|1>> with
    predicate variables <math|\<chi\><around*|(|\<cdummy\>|)>>. Let
    <math|\<Gamma\>> be an environment, <math|C> a formula in
    <math|\<cal-L\>>, <math|e> an expression and <math|\<tau\>> a type. If
    <math|PV<around*|(|C,\<Gamma\>|)>=\<varnothing\>> and
    <math|C,\<Gamma\>\<vdash\>e:\<tau\>> is derivable, then there exists an
    interpretation of predicate variables <math|\<cal-I\>> such that
    <math|\<cal-M\>,\<cal-I\>\<vDash\>C\<Rightarrow\><around*|\<llbracket\>|\<Gamma\>\<vdash\>e:<no-break>\<tau\>|\<rrbracket\>>>.
  </theorem>

  In Theorem <reference|InfComplExpr>, we explicitly introduce all symbols
  used. We often state propositions and theorems in a more compact manner,
  with symbols introduced implicitly.

  <\corollary>
    <label|InfComplCoro>If <math|C,\<Gamma\>\<vdash\>e:\<forall\><wide|\<alpha\>|\<bar\>><around|[|D|]>.\<tau\>>
    and <math|<wide|\<alpha\>|\<bar\>>#FV<around|(|\<Gamma\>|)>>, then there
    is an interpretation <math|\<cal-I\>> such that
    <math|\<cal-M\>,\<cal-I\>\<vDash\>C\<Rightarrow\><around*|(|\<forall\><wide|\<alpha\>|\<bar\>>.D\<Rightarrow\><around*|\<llbracket\>|\<Gamma\>\<vdash\>e:\<tau\>|\<rrbracket\>>|)>>.
  </corollary>

  <\float|float|t>
    <\big-table>
      Constraint generation:

      <\eqnarray*>
        <tformat|<table|<row|<cell|<around*|\<llbracket\>|\<vdash\>0\<downarrow\>\<tau\><around*|\<rrbracket\>||\<nobracket\>>|\<nobracket\>>>|<cell|=>|<cell|\<b-T\>>>|<row|<cell|>|<cell|>|<cell|>>|<row|<cell|<around*|\<llbracket\>|\<vdash\>1\<downarrow\>\<tau\><around*|\<rrbracket\>||\<nobracket\>>|\<nobracket\>>>|<cell|=>|<cell|\<b-T\>>>|<row|<cell|>|<cell|>|<cell|>>|<row|<cell|<around*|\<llbracket\>|\<vdash\>x\<downarrow\>\<tau\><around*|\<rrbracket\>||\<nobracket\>>|\<nobracket\>>>|<cell|=>|<cell|\<b-T\>>>|<row|<cell|>|<cell|>|<cell|>>|<row|<cell|<around*|\<llbracket\>|\<vdash\>p<rsub|1>\<wedge\>p<rsub|2>\<downarrow\>\<tau\><around*|\<rrbracket\>||\<nobracket\>>|\<nobracket\>>>|<cell|=>|<cell|<around*|\<llbracket\>|\<vdash\>p<rsub|1>\<downarrow\>\<tau\><around*|\<rrbracket\>|\<wedge\><around*|\<llbracket\>|\<vdash\>p<rsub|2>\<downarrow\>\<tau\><around*|\<rrbracket\>||\<nobracket\>>|\<nobracket\>>|\<nobracket\>>|\<nobracket\>>>>|<row|<cell|>|<cell|>|<cell|>>|<row|<cell|<around*|\<llbracket\>|\<vdash\>K
        p<rsub|1>\<ldots\>p<rsub|n>\<downarrow\>\<tau\><around*|\<rrbracket\>||\<nobracket\>>|\<nobracket\>>>|<cell|=>|<cell|\<exists\><wide|\<alpha\>|\<bar\>><rprime|'>.\<varepsilon\><around|(|<wide|\<alpha\>|\<bar\>><rprime|'>|)><wide|=|\<dot\>>\<tau\>\<wedge\>\<forall\><wide|\<beta\>|\<bar\>><rprime|'>.D<around|[|<wide|\<alpha\>|\<bar\>><wide|\<beta\>|\<bar\>>\<assign\><wide|\<alpha\>|\<bar\>><rprime|'><wide|\<beta\>|\<bar\>><rprime|'>|]>\<Rightarrow\>\<wedge\><rsub|i><around*|\<llbracket\>|p<rsub|i>\<downarrow\>\<tau\><rsub|i><around|[|<wide|\<alpha\>|\<bar\>><wide|\<beta\>|\<bar\>>\<assign\><wide|\<alpha\>|\<bar\>><rprime|'><wide|\<beta\>|\<bar\>><rprime|'>|]><around*|\<rrbracket\>||\<nobracket\>>|\<nobracket\>>>>|<row|<cell|>|<cell|>|<cell|>>|<row|<cell|>|<cell|>|<cell|<text|where
        >K\<colons\>\<forall\><wide|\<alpha\>|\<bar\>><wide|\<beta\>|\<bar\>><around|[|D|]>.\<tau\><rsub|1>\<times\>\<ldots\>\<times\>\<tau\><rsub|n>\<rightarrow\>\<varepsilon\><around|(|<wide|\<alpha\>|\<bar\>>|)>,<wide|\<alpha\>|\<bar\>><rprime|'><wide|\<beta\>|\<bar\>><rprime|'>#FV<around|(|\<Sigma\>,\<tau\>|)>>>>>
      </eqnarray*>

      Environment fragment generation:

      <\eqnarray*>
        <tformat|<table|<row|<cell|<around*|\<llbracket\>|\<vdash\>0\<uparrow\>\<tau\><around*|\<rrbracket\>||\<nobracket\>>|\<nobracket\>>>|<cell|=>|<cell|\<exists\>\<varnothing\><around|[|\<b-F\>|]><around|{||}>>>|<row|<cell|>|<cell|>|<cell|>>|<row|<cell|<around*|\<llbracket\>|\<vdash\>1\<uparrow\>\<tau\><around*|\<rrbracket\>||\<nobracket\>>|\<nobracket\>>>|<cell|=>|<cell|\<exists\>\<varnothing\><around|[|\<b-T\>|]><around|{||}>>>|<row|<cell|>|<cell|>|<cell|>>|<row|<cell|<around*|\<llbracket\>|\<vdash\>x\<uparrow\>\<tau\><around*|\<rrbracket\>||\<nobracket\>>|\<nobracket\>>>|<cell|=>|<cell|\<exists\>\<varnothing\><around|[|\<b-T\>|]><around|{|x\<mapsto\>\<tau\>|}>>>|<row|<cell|>|<cell|>|<cell|>>|<row|<cell|<around*|\<llbracket\>|\<vdash\>p<rsub|1>\<wedge\>p<rsub|2>\<uparrow\>\<tau\><around*|\<rrbracket\>||\<nobracket\>>|\<nobracket\>>>|<cell|=>|<cell|<around*|\<llbracket\>|\<vdash\>p<rsub|1>\<uparrow\>\<tau\><around*|\<rrbracket\>|\<times\><around*|\<llbracket\>|\<vdash\>p<rsub|2>\<uparrow\>\<tau\><around*|\<rrbracket\>||\<nobracket\>>|\<nobracket\>>|\<nobracket\>>|\<nobracket\>>>>|<row|<cell|>|<cell|>|<cell|>>|<row|<cell|<around*|\<llbracket\>|\<vdash\>K
        p<rsub|1>\<ldots\>p<rsub|n>\<uparrow\>\<tau\><around*|\<rrbracket\>||\<nobracket\>>|\<nobracket\>>>|<cell|=>|<cell|\<exists\><wide|\<alpha\>|\<bar\>><rprime|'><wide|\<beta\>|\<bar\>><rprime|'><around|[|\<varepsilon\><around|(|<wide|\<alpha\>|\<bar\>><rprime|'>|)><wide|=|\<dot\>>\<tau\>\<wedge\>D<around|[|<wide|\<alpha\>|\<bar\>><wide|\<beta\>|\<bar\>>\<assign\><wide|\<alpha\>|\<bar\>><rprime|'><wide|\<beta\>|\<bar\>><rprime|'>|]>|]>(\<times\><rsub|i><around*|\<llbracket\>|p<rsub|i>\<uparrow\>\<tau\><rsub|i><around|[|<wide|\<alpha\>|\<bar\>><wide|\<beta\>|\<bar\>>\<assign\><wide|\<alpha\>|\<bar\>><rprime|'><wide|\<beta\>|\<bar\>><rprime|'>|]><around*|\<rrbracket\>||)>|\<nobracket\>>>>|<row|<cell|>|<cell|>|<cell|>>|<row|<cell|>|<cell|>|<cell|<text|where
        >K\<colons\>\<forall\><wide|\<alpha\>|\<bar\>><wide|\<beta\>|\<bar\>><around|[|D|]>.\<tau\><rsub|1>\<times\>\<ldots\>\<times\>\<tau\><rsub|n>\<rightarrow\>\<varepsilon\><around|(|<wide|\<alpha\>|\<bar\>>|)>,<wide|\<alpha\>|\<bar\>><rprime|'><wide|\<beta\>|\<bar\>><rprime|'>#FV<around|(|\<Sigma\>,\<tau\>|)>>>>>
      </eqnarray*>

      <label|IntermInfPat>
    </big-table|Type inference for patterns>
  </float><\float|float|t>
    <\big-table>
      <\eqnarray*>
        <tformat|<table|<row|<cell|<around*|\<llbracket\>|\<Gamma\>\<vdash\>x:\<tau\>|\<rrbracket\>>>|<cell|=>|<cell|\<b-F\><with|mode|text|
        \ when \ >x\<nin\>Dom<around*|(|\<Gamma\>|)>>>|<row|<cell|>|<cell|>|<cell|>>|<row|<cell|<around*|\<llbracket\>|\<Gamma\>\<vdash\>x:\<tau\>|\<rrbracket\>>>|<cell|=>|<cell|\<exists\>\<beta\><rprime|'><wide|\<alpha\>|\<bar\>><rprime|'>.D<around|[|\<beta\><wide|\<alpha\>|\<bar\>>\<assign\>\<beta\><rprime|'><wide|\<alpha\>|\<bar\>><rprime|'>|]>\<wedge\>\<beta\><rprime|'><wide|=|\<dot\>>\<tau\><text|
        \ where >\<Gamma\><around|(|x|)>=\<forall\>\<beta\><around|[|\<exists\><wide|\<alpha\>|\<bar\>>.D|]>.\<beta\>,\<beta\><rprime|'><wide|\<alpha\>|\<bar\>><rprime|'>#FV<around|(|\<Gamma\>,\<tau\>|)>>>|<row|<cell|>|<cell|>|<cell|>>|<row|<cell|<around*|\<llbracket\>|\<Gamma\>\<vdash\><text|<with|font-shape|condensed|<strong|assert
        false>>>:\<tau\>|\<rrbracket\>>>|<cell|=>|<cell|\<b-F\>>>|<row|<cell|>|<cell|>|<cell|>>|<row|<cell|<around*|\<llbracket\>|\<Gamma\>\<vdash\><text|<with|font-shape|condensed|<strong|runtime
        failure>>> s:\<tau\>|\<rrbracket\>>>|<cell|=>|<cell|<around*|\<llbracket\>|\<Gamma\>\<vdash\>s:String|\<rrbracket\>>>>|<row|<cell|>|<cell|>|<cell|>>|<row|<cell|<around*|\<llbracket\>|\<Gamma\>\<vdash\><text|<with|font-shape|condensed|<strong|assert
        num>>> e<rsub|1>\<leqslant\>e<rsub|2>;e<rsub|3>:\<tau\>|\<rrbracket\>>>|<cell|=>|<cell|\<exists\>\<alpha\><rsup|1>\<alpha\><rsup|2>.<around*|\<llbracket\>|\<Gamma\>\<vdash\>e<rsub|1>:Num<around*|(|\<alpha\><rsup|1>|)>|\<rrbracket\>>\<wedge\><around*|\<llbracket\>|\<Gamma\>\<vdash\>e<rsub|2>:Num<around*|(|\<alpha\><rsup|2>|)>|\<rrbracket\>>\<wedge\>\<alpha\><rsup|1>\<leq\>\<alpha\><rsup|2>\<wedge\><around*|\<llbracket\>|\<Gamma\>\<vdash\>e<rsub|3>:<no-break>\<tau\>|\<rrbracket\>>,\<alpha\><rsub|1>\<alpha\><rsub|2>#FV<around|(|\<Gamma\>,<no-break>\<tau\>|)>>>|<row|<cell|>|<cell|>|<cell|>>|<row|<cell|<around*|\<llbracket\>|\<Gamma\>\<vdash\><text|<with|font-shape|condensed|<strong|assert
        type>>> e<rsub|1>=e<rsub|2>;e<rsub|3>:\<tau\>|\<rrbracket\>>>|<cell|=>|<cell|\<exists\>\<alpha\><rsup|1>\<alpha\><rsup|2>.<around*|\<llbracket\>|\<Gamma\>\<vdash\>e<rsub|1>:\<alpha\><rsup|1>|\<rrbracket\>>\<wedge\><around*|\<llbracket\>|\<Gamma\>\<vdash\>e<rsub|2>:\<alpha\><rsup|2>|\<rrbracket\>>\<wedge\>\<alpha\><rsup|1><wide|=|\<dot\>>\<alpha\><rsup|2>\<wedge\><around*|\<llbracket\>|\<Gamma\>\<vdash\>e<rsub|3>:\<tau\>|\<rrbracket\>>,\<alpha\><rsub|1>\<alpha\><rsub|2>#FV<around|(|\<Gamma\>,\<tau\>|)>>>|<row|<cell|>|<cell|>|<cell|>>|<row|<cell|<around*|\<llbracket\>|\<Gamma\>\<vdash\>\<lambda\><wide|c|\<bar\>>:\<tau\>|\<rrbracket\>>>|<cell|=>|<cell|\<exists\>\<alpha\><rsub|1>\<alpha\><rsub|2>.<around*|\<llbracket\>|\<Gamma\>\<vdash\><wide|c|\<bar\>>:\<alpha\><rsub|1>\<rightarrow\>\<alpha\><rsub|2>|\<rrbracket\>>\<wedge\>\<alpha\><rsub|1>\<rightarrow\>\<alpha\><rsub|2><wide|=|\<dot\>>\<tau\>,<with|mode|text|>\<alpha\><rsub|1>\<alpha\><rsub|2>#FV<around|(|\<Gamma\>,\<tau\>|)>>>|<row|<cell|>|<cell|>|<cell|>>|<row|<cell|<around*|\<llbracket\>|\<Gamma\>\<vdash\>e<rsub|1>
        e<rsub|2>:\<tau\>|\<rrbracket\>>>|<cell|=>|<cell|\<exists\>\<alpha\>.<around*|\<llbracket\>|\<Gamma\>\<vdash\>e<rsub|1>:\<alpha\>\<rightarrow\>\<tau\>|\<rrbracket\>>\<wedge\><around*|\<llbracket\>|\<Gamma\>\<vdash\>e<rsub|2>:\<alpha\>|\<rrbracket\>>,<with|mode|text|
        \ >\<alpha\>#FV<around|(|\<Gamma\>,\<tau\>|)>>>|<row|<cell|>|<cell|>|<cell|>>|<row|<cell|<around*|\<llbracket\>|\<Gamma\>\<vdash\>K
        e<rsub|1>\<ldots\>e<rsub|n>:\<tau\>|\<rrbracket\>>>|<cell|=>|<cell|\<exists\><wide|\<alpha\>|\<bar\>><rprime|'><wide|\<beta\>|\<bar\>><rprime|'>.(\<wedge\><rsub|i><around*|\<llbracket\>|\<Gamma\>\<vdash\>e<rsub|i>:\<tau\><rsub|i><around|[|<wide|\<alpha\>|\<bar\>><wide|\<beta\>|\<bar\>>\<assign\><wide|\<alpha\>|\<bar\>><rprime|'><wide|\<beta\>|\<bar\>><rprime|'>|]>|\<rrbracket\>>\<wedge\>D<around|[|<wide|\<alpha\>|\<bar\>><wide|\<beta\>|\<bar\>>\<assign\><wide|\<alpha\>|\<bar\>><rprime|'><wide|\<beta\>|\<bar\>><rprime|'>|]>\<wedge\>\<varepsilon\><around|(|<wide|\<alpha\>|\<bar\>><rprime|'>|)><wide|=|\<dot\>>\<tau\>)>>|<row|<cell|>|<cell|>|<cell|<text|where
        >\<Sigma\>\<ni\>K\<colons\>\<forall\><wide|\<alpha\>|\<bar\>><wide|\<beta\>|\<bar\>><around|[|D|]>.\<tau\><rsub|1>\<times\>\<ldots\>\<times\>\<tau\><rsub|n>\<rightarrow\>\<varepsilon\><around|(|<wide|\<alpha\>|\<bar\>>|)>,<with|mode|text|
        \ ><wide|\<alpha\>|\<bar\>><rprime|'><wide|\<beta\>|\<bar\>><rprime|'>#FV<around|(|\<Gamma\>,\<tau\>|)>>>|<row|<cell|>|<cell|>|<cell|>>|<row|<cell|<around*|\<llbracket\>|\<Gamma\>\<vdash\><text|<with|font-shape|condensed|<strong|let
        rec>>> x=e<rsub|1><text|<with|font-shape|condensed|<strong|in>>>
        e<rsub|2>:\<tau\>|\<rrbracket\>>>|<cell|=>|<cell|<around*|(|\<forall\>\<beta\><around|(|\<chi\><around|(|\<beta\>|)>\<Rightarrow\><around*|\<llbracket\>|\<Gamma\><around|{|x\<mapsto\>\<forall\>\<beta\><around|[|\<chi\><around|(|\<beta\>|)>|]>.\<beta\>|}>\<vdash\>e<rsub|1>:\<beta\>|\<rrbracket\>>|)>|)>\<wedge\><next-line><around|(|\<exists\>\<alpha\>.\<chi\><around|(|\<alpha\>|)>|)>\<wedge\><around*|\<llbracket\>|\<Gamma\><around|{|x\<mapsto\>\<forall\>\<beta\><around|[|\<chi\><around|(|\<beta\>|)>|]>.\<beta\>|}>\<vdash\>e<rsub|2>:\<tau\>|\<rrbracket\>>>>|<row|<cell|>|<cell|>|<cell|<with|mode|text|where
        >\<beta\>#FV<around|(|\<Gamma\>,\<tau\>|)>,\<chi\>#PV<around*|(|\<Gamma\>|)>>>|<row|<cell|>|<cell|>|<cell|>>|<row|<cell|<around*|\<llbracket\>|\<Gamma\>\<vdash\><wide|c<rsub|i>|\<bar\>>:\<tau\><rsub|1>\<rightarrow\>\<tau\><rsub|2>|\<rrbracket\>>>|<cell|=>|<cell|\<wedge\><rsub|i><around*|\<llbracket\>|\<Gamma\>\<vdash\>c<rsub|i>:\<tau\><rsub|1>\<rightarrow\>\<tau\><rsub|2>|\<rrbracket\>>>>|<row|<cell|>|<cell|>|<cell|>>|<row|<cell|<around*|\<llbracket\>|\<Gamma\>\<vdash\>e:\<forall\><wide|\<alpha\>|\<bar\>><around|[|D|]>.\<tau\>|\<rrbracket\>>>|<cell|=>|<cell|\<forall\><wide|\<alpha\>|\<bar\>><rprime|'>.D<around|[|<wide|\<alpha\>|\<bar\>>\<assign\><wide|\<alpha\>|\<bar\>><rprime|'>|]>\<Rightarrow\><around*|\<llbracket\>|\<Gamma\>\<vdash\>e:\<tau\><around|[|<wide|\<alpha\>|\<bar\>>\<assign\><wide|\<alpha\>|\<bar\>><rprime|'>|]>|\<rrbracket\>>,<with|mode|text|
        \ ><wide|\<alpha\>|\<bar\>><rprime|'>#FV<around|(|\<Gamma\>|)>>>>>
      </eqnarray*>

      <label|IntermInf>
    </big-table|Type inference for expressions>
  </float><\float|float|t>
    <\big-table>
      <\eqnarray*>
        <tformat|<table|<row|<cell|<around*|\<llbracket\>|\<Gamma\>\<vdash\>p
        <text|<with|font-shape|condensed|<strong|when>>>
        \<wedge\><rsub|i>m<rsub|i>\<leqslant\>n<rsub|i>.e:\<tau\><rsub|1>\<rightarrow\>\<tau\><rsub|2>|\<rrbracket\>>>|<cell|=>|<cell|<around*|\<llbracket\>|\<vdash\>p\<downarrow\>\<tau\><rsub|1>|\<rrbracket\>>\<wedge\>\<forall\><wide|\<beta\>|\<bar\>>.\<exists\><wide|\<alpha\><rsup|1><rsub|i>\<alpha\><rsup|2><rsub|i>|\<bar\>>.D\<Rightarrow\><next-line><with|mode|text|
        \ \ \ \ \ >\<wedge\><rsub|i><around*|\<llbracket\>|\<Gamma\>\<Gamma\><rprime|'>\<vdash\>m<rsub|i>:Num<around*|(|\<alpha\><rsup|1><rsub|i>|)>|\<rrbracket\>>\<wedge\><rsub|i><around*|\<llbracket\>|\<Gamma\>\<Gamma\><rprime|'>\<vdash\>n<rsub|i>:Num<around*|(|\<alpha\><rsup|2><rsub|i>|)>|\<rrbracket\>>>>|<row|<cell|<with|mode|text|when
        >e\<neq\><with|math-font-series|bold|runtime
        failure>\<wedge\>>|<cell|>|<cell|<with|mode|text|
        \ \ \ \ \ >\<wedge\><around*|(|\<wedge\><rsub|i>\<alpha\><rsup|1><rsub|i>\<leq\>\<alpha\><rsup|2><rsub|i>\<Rightarrow\><around*|\<llbracket\>|\<Gamma\>\<Gamma\><rprime|'>\<vdash\>e:\<tau\><rsub|2>|\<rrbracket\>>|)>>>|<row|<cell|e\<neq\><text|<with|font-shape|condensed|<strong|assert
        false>>>\<wedge\>\<ldots\>\<wedge\>>|<cell|>|<cell|>>|<row|<cell|e\<neq\>\<lambda\><around*|(|p<rprime|'>\<ldots\>\<lambda\><around*|(|p<rprime|''>.<text|<with|font-shape|condensed|<strong|assert
        false>>>|)>|)>>|<cell|>|<cell|>>|<row|<cell|>|<cell|>|<cell|<text|where
        >\<exists\><wide|\<beta\>|\<bar\>><around|[|D|]>\<Gamma\><rprime|'><text|
        is ><around*|\<llbracket\>|\<vdash\>p\<uparrow\>\<tau\><rsub|1>|\<rrbracket\>>,<wide|\<beta\>|\<bar\>><wide|\<alpha\><rsup|1><rsub|i>\<alpha\><rsup|2><rsub|i>|\<bar\>>#FV<around|(|\<Gamma\>,\<tau\><rsub|1>,\<tau\><rsub|2>|)>>>|<row|<cell|>|<cell|>|<cell|>>|<row|<cell|<around*|\<llbracket\>|\<Gamma\>\<vdash\>p
        <text|<with|font-shape|condensed|<strong|when>>>
        \<wedge\><rsub|i>m<rsub|i>\<leqslant\>n<rsub|i>.e:\<tau\><rsub|1>\<rightarrow\>\<tau\><rsub|2>|\<rrbracket\>>>|<cell|=>|<cell|\<exists\>\<alpha\><rsub|3>.<around*|\<llbracket\>|\<vdash\>p\<downarrow\>\<alpha\><rsub|3>|\<rrbracket\>>\<wedge\>\<forall\><wide|\<beta\>|\<bar\>>.\<exists\><wide|\<alpha\><rsup|1><rsub|i>\<alpha\><rsup|2><rsub|i>|\<bar\>>.D\<Rightarrow\><next-line><with|mode|text|
        \ \ \ \ \ >\<wedge\><rsub|i><around*|\<llbracket\>|\<Gamma\>\<Gamma\><rprime|'>\<vdash\>m<rsub|i>:Num<around*|(|\<alpha\><rsup|1><rsub|i>|)>|\<rrbracket\>>\<wedge\><rsub|i><around*|\<llbracket\>|\<Gamma\>\<Gamma\><rprime|'>\<vdash\>n<rsub|i>:Num<around*|(|\<alpha\><rsup|2><rsub|i>|)>|\<rrbracket\>>>>|<row|<cell|<with|mode|text|when
        >e=<text|<with|font-shape|condensed|<strong|assert
        false>>>\<vee\>\<ldots\>\<vee\>>|<cell|>|<cell|<with|mode|text|
        \ \ \ \ \ >\<wedge\><around*|(|\<alpha\><rsub|3><wide|=|\<dot\>>\<tau\><rsub|1>\<wedge\><rsub|i>\<alpha\><rsup|1><rsub|i>\<leq\>\<alpha\><rsup|2><rsub|i>\<Rightarrow\><around*|\<llbracket\>|\<Gamma\>\<Gamma\><rprime|'>\<vdash\>e:\<tau\><rsub|2>|\<rrbracket\>>|)>>>|<row|<cell|e=\<lambda\><around*|(|p<rprime|'>\<ldots\>\<lambda\><around*|(|p<rprime|''>.<text|<with|font-shape|condensed|<strong|assert
        false>>>|)>|)>>|<cell|>|<cell|>>|<row|<cell|>|<cell|>|<cell|<text|where
        >\<exists\><wide|\<beta\>|\<bar\>><around|[|D|]>\<Gamma\><rprime|'><text|
        is ><around*|\<llbracket\>|\<vdash\>p\<uparrow\>\<alpha\><rsub|3>|\<rrbracket\>>,<wide|\<beta\>|\<bar\>>\<alpha\><rsub|3><wide|\<alpha\><rsup|1><rsub|i>\<alpha\><rsup|2><rsub|i>|\<bar\>>#FV<around|(|\<Gamma\>,\<tau\><rsub|1>,\<tau\><rsub|2>|)>>>|<row|<cell|>|<cell|>|<cell|>>|<row|<cell|<around*|\<llbracket\>|\<Gamma\>\<vdash\>p
        <text|<with|font-shape|condensed|<strong|when>>>
        \<wedge\><rsub|i>m<rsub|i>\<leqslant\>n<rsub|i>.e:\<tau\><rsub|1>\<rightarrow\>\<tau\><rsub|2>|\<rrbracket\>>>|<cell|=>|<cell|\<exists\>\<alpha\><rsub|3>.<around*|\<llbracket\>|\<vdash\>p\<downarrow\>\<alpha\><rsub|3>|\<rrbracket\>>\<wedge\>\<forall\><wide|\<beta\>|\<bar\>>.\<exists\><wide|\<alpha\><rsup|1><rsub|i>\<alpha\><rsup|2><rsub|i>|\<bar\>>.D\<Rightarrow\><next-line><with|mode|text|
        \ \ \ \ \ >\<wedge\><rsub|i><around*|\<llbracket\>|\<Gamma\>\<Gamma\><rprime|'>\<vdash\>m<rsub|i>:Num<around*|(|\<alpha\><rsup|1><rsub|i>|)>|\<rrbracket\>>\<wedge\><rsub|i><around*|\<llbracket\>|\<Gamma\>\<Gamma\><rprime|'>\<vdash\>n<rsub|i>:Num<around*|(|\<alpha\><rsup|2><rsub|i>|)>|\<rrbracket\>>>>|<row|<cell|<with|mode|text|when
        >e=<text|<with|font-shape|condensed|<strong|runtime failure>>>
        s>|<cell|>|<cell|<with|mode|text|
        \ \ \ \ \ >\<wedge\><around*|(|\<alpha\><rsub|3><wide|=|\<dot\>>\<tau\><rsub|1>\<wedge\><rsub|i>\<alpha\><rsup|1><rsub|i>\<leq\>\<alpha\><rsup|2><rsub|i>\<Rightarrow\><around*|\<llbracket\>|\<Gamma\>\<Gamma\><rprime|'>\<vdash\>s:String|\<rrbracket\>>|)>>>|<row|<cell|>|<cell|>|<cell|<text|where
        >\<exists\><wide|\<beta\>|\<bar\>><around|[|D|]>\<Gamma\><rprime|'><text|
        is ><around*|\<llbracket\>|\<vdash\>p\<uparrow\>\<alpha\><rsub|3>|\<rrbracket\>>,<wide|\<beta\>|\<bar\>>\<alpha\><rsub|3><wide|\<alpha\><rsup|1><rsub|i>\<alpha\><rsup|2><rsub|i>|\<bar\>>#FV<around|(|\<Gamma\>,\<tau\><rsub|1>,\<tau\><rsub|2>|)>>>>>
      </eqnarray*>

      <label|IntermInfClaus>
    </big-table|Type inference for clauses>
  </float><\float|float|t>
    <big-table|<math|<tabular|<tformat|<cwith|1|1|1|1|cell-halign|r>|<cwith|2|2|1|1|cell-halign|r>|<cwith|3|3|1|1|cell-halign|r>|<cwith|4|4|1|1|cell-halign|r>|<cwith|5|5|1|1|cell-halign|r>|<cwith|6|6|1|1|cell-halign|r>|<cwith|7|7|1|1|cell-halign|r>|<cwith|8|8|1|1|cell-halign|r>|<cwith|9|9|1|1|cell-halign|r>|<cwith|10|10|1|1|cell-halign|r>|<cwith|11|11|1|1|cell-halign|r>|<table|<row|<cell|l<around*|(|x|)>>|<cell|=>|<cell|\<b-F\>>>|<row|<cell|l<around*|(|\<lambda\><wide|c|\<bar\>>|)>>|<cell|=>|<cell|\<b-F\>>>|<row|<cell|l<around*|(|e<rsub|1>
    e<rsub|2>|)>>|<cell|=>|<cell|l<around*|(|e<rsub|1>|)>>>|<row|<cell|l<around*|(|K
    e<rsub|1>\<ldots\>e<rsub|n>|)>>|<cell|=>|<cell|\<b-F\>>>|<row|<cell|l<around*|(|<text|<with|font-shape|condensed|<strong|let
    rec>>> x=e<rsub|1> <text|<with|font-shape|condensed|<strong|in>>>
    e<rsub|2>|)>>|<cell|=>|<cell|l<around*|(|e<rsub|2>|)>>>|<row|<cell|l<around*|(|\<lambda\><around*|[|K|]><wide|p<rsub|i>.e<rsub|i>|\<bar\>>|)>>|<cell|=>|<cell|\<b-T\>>>|<row|<cell|l<around*|(|<text|<with|font-shape|condensed|<strong|let>>>
    p=e<rsub|1> <text|<with|font-shape|condensed|<strong|in>>>
    e<rsub|2>|)>>|<cell|=>|<cell|\<b-T\>>>|<row|<cell|l<around*|(|<text|<with|font-shape|condensed|<strong|assert
    num>>> e<rsub|1>\<leqslant\>e<rsub|2>;e<rsub|3>|)>>|<cell|=>|<cell|l<around*|(|e<rsub|3>|)>>>|<row|<cell|l<around*|(|<text|<with|font-shape|condensed|<strong|assert
    type>>> e<rsub|1>=e<rsub|2>;e<rsub|3>|)>>|<cell|=>|<cell|l<around*|(|e<rsub|3>|)>>>|<row|<cell|l<around*|(|<text|<with|font-shape|condensed|<strong|runtime
    failure>>> s|)>>|<cell|=>|<cell|\<b-T\>>>|<row|<cell|l<around*|(|<text|<with|font-shape|condensed|<strong|assert
    false>>>|)>>|<cell|=>|<cell|\<b-T\>>>>>>><label|IsExBrs>|Expressions that
    directly handle an existential type>
  </float><\float|float|t>
    <big-table|<math|<tabular|<tformat|<cwith|1|1|1|1|cell-halign|r>|<cwith|2|2|1|1|cell-halign|r>|<cwith|3|3|1|1|cell-halign|r>|<cwith|4|4|1|1|cell-halign|r>|<cwith|5|5|1|1|cell-halign|r>|<cwith|8|8|1|1|cell-halign|r>|<cwith|9|9|1|1|cell-halign|r>|<cwith|10|10|1|1|cell-halign|r>|<cwith|11|11|1|1|cell-halign|r>|<cwith|12|12|1|1|cell-halign|r>|<table|<row|<cell|\<cal-E\><around*|(|x,v|)>>|<cell|=>|<cell|\<varnothing\>>>|<row|<cell|\<cal-E\><around*|(|\<lambda\><wide|c|\<bar\>>,v|)>>|<cell|=>|<cell|\<cup\><wide|\<cal-E\><around*|(|c,\<b-F\>|)>|\<bar\>>>>|<row|<cell|\<cal-E\><around*|(|e<rsub|1>
    e<rsub|2>,v|)>>|<cell|=>|<cell|\<cal-E\><around*|(|e<rsub|1>,v|)>\<cup\>\<cal-E\><around*|(|e<rsub|2>,\<b-F\>|)>>>|<row|<cell|\<cal-E\><around*|(|K
    e<rsub|1>\<ldots\>e<rsub|n>,v|)>>|<cell|=>|<cell|\<cup\><rsub|i>\<cal-E\><around*|(|e<rsub|i>,\<b-F\>|)>>>|<row|<cell|\<cal-E\><around*|(|<text|<with|font-shape|condensed|<strong|let
    rec>>> x=e<rsub|1> <text|<with|font-shape|condensed|<strong|in>>>
    e<rsub|2>,v|)>>|<cell|=>|<cell|\<cal-E\><around*|(|e<rsub|1>,\<b-F\>|)>\<cup\>\<cal-E\><around*|(|e<rsub|2>,v|)>>>|<row|<cell|\<cal-E\><around*|(|p
    <text|<with|font-shape|condensed|<strong|when>>>
    <wide|m<rsub|i>\<leqslant\>n<rsub|i>|\<bar\>>.e,v|)>>|<cell|=>|<cell|\<cup\><rsub|i>\<cal-E\><around*|(|m<rsub|i>,\<b-F\>|)>\<cup\><rsub|i>\<cal-E\><around*|(|n<rsub|i>,\<b-F\>|)>>>|<row|<cell|>|<cell|>|<cell|\<cup\>\<cal-E\><around*|(|e,v|)>>>|<row|<cell|\<cal-E\><around*|(|\<lambda\><around*|[|K|]><wide|c|\<bar\>>,\<b-F\>|)>>|<cell|=>|<cell|<around*|{|K|}>\<cup\><wide|\<cal-E\><around*|(|c,\<b-T\>|)>|\<bar\>>>>|<row|<cell|\<cal-E\><around*|(|\<lambda\><around*|[|K|]><wide|c|\<bar\>>,\<b-T\>|)>>|<cell|=>|<cell|\<cup\><wide|\<cal-E\><around*|(|c,\<b-T\>|)>|\<bar\>>>>|<row|<cell|\<cal-E\><around*|(|<text|<with|font-shape|condensed|<strong|let>>>
    p=e<rsub|1> <text|<with|font-shape|condensed|<strong|in>>>
    e<rsub|2>,v|)>>|<cell|=>|<cell|\<cal-E\><around*|(|e<rsub|1>,\<b-F\>|)>\<cup\>\<cal-E\><around*|(|e<rsub|2>,v|)>>>|<row|<cell|\<cal-E\><around*|(|<text|<with|font-shape|condensed|<strong|assert
    num>>> e<rsub|1>\<leqslant\>e<rsub|2>;e<rsub|3>,K<rprime|'>|)>>|<cell|=>|<cell|\<cal-E\><around*|(|e<rsub|1>,\<b-F\>|)>\<cup\>\<cal-E\><around*|(|e<rsub|2>,\<b-F\>|)>\<cup\>\<cal-E\><around*|(|e<rsub|3>,v|)>>>|<row|<cell|\<cal-E\><around*|(|<text|<with|font-shape|condensed|<strong|assert
    type>>> e<rsub|1>=e<rsub|2>;e<rsub|3>,K<rprime|'>|)>>|<cell|=>|<cell|\<cal-E\><around*|(|e<rsub|1>,\<b-F\>|)>\<cup\>\<cal-E\><around*|(|e<rsub|2>,\<b-F\>|)>\<cup\>\<cal-E\><around*|(|e<rsub|3>,v|)>>>>>>><label|CollectK>|Collect
    introduced value constructors>
  </float>

  In Definition <reference|SolTypInfer>, we describe a class of type
  judgments that is a better target for type inference. First, we introduce a
  normal form of constraints that simplifies formal considerations.

  <\proposition>
    <label|NormalFormProp>For any <math|\<Gamma\>,e,\<tau\>>, the formula
    <math|<around*|\<llbracket\>|\<Gamma\>\<vdash\>e:\<tau\>|\<rrbracket\>>>
    is equivalent to a prenex-normal, normalized form: there is a quantifier
    prefix <math|\<cal-Q\>> and pairs of conjunctions of atoms
    <math|D<rsub|i>,C<rsub|i>>, such that

    <\equation*>
      \<cal-M\>\<vDash\><around*|\<llbracket\>|\<Gamma\>\<vdash\>e:\<tau\>|\<rrbracket\>>\<Leftrightarrow\>\<cal-Q\>.\<wedge\><rsub|i><around*|(|D<rsub|i>\<Rightarrow\>C<rsub|i>|)>
    </equation*>
  </proposition>

  We put <math|NF<around*|(|<around*|\<llbracket\>|\<Gamma\>\<vdash\>e:\<tau\>|\<rrbracket\>>|)>=\<cal-Q\>.\<wedge\><rsub|i><around*|(|D<rsub|i>\<Rightarrow\>C<rsub|i>|)>>.

  <\definition>
    <label|SolTypInfer>We call the formula
    <math|<around*|\<llbracket\>|\<Gamma\>\<vdash\>e:\<tau\>|\<rrbracket\>>>
    the <em|type inference problem> for environment <math|\<Gamma\>>,
    expression <math|e> and type <math|\<tau\>>. Let
    <math|\<cal-M\>\<vDash\><around*|\<llbracket\>|\<Gamma\>\<vdash\>e:<no-break>\<tau\>|\<rrbracket\>>\<Leftrightarrow\>\<cal-Q\>.\<Phi\><rsub|N>>
    with <math|\<Phi\><rsub|N>=\<wedge\><rsub|i><around*|(|D<rsub|i>\<Rightarrow\>C<rsub|i>|)>>
    as in Proposition <reference|NormalFormProp>. Let <math|F<rsub|res>> be a
    conjunction of atoms without predicate variables. We call
    <math|\<exists\><wide|\<alpha\>|\<bar\>><rsub|res>.F<rsub|res>,\<cal-I\>>
    a <em|solution to the type inference problem>
    <math|<around*|\<llbracket\>|\<Gamma\>\<vdash\>e:<no-break>\<tau\>|\<rrbracket\>>>
    when <math|\<cal-I\>,\<cal-M\>\<vDash\>F<rsub|res>\<Rightarrow\>\<Phi\><rsub|N>>
    (i.e. <math|\<cal-M\>\<vDash\>F<rsub|res>\<Rightarrow\>\<cal-I\><around*|(|\<Phi\><rsub|N>|)>>),
    <math|\<cal-M\>\<vDash\>\<cal-Q\>.F<rsub|res><around*|[|<wide|\<alpha\>|\<bar\>><rsub|res>\<assign\><wide|t|\<bar\>>|]>>
    for some <math|<wide|t|\<bar\>>>, and for every implication in
    <math|\<Phi\><rsub|N>>, if <math|\<cal-M\>,\<cal-I\>\<vDash\>\<exists\>FV<around*|(|D<rsub|i>|)>.D<rsub|i>>
    then <math|\<cal-M\>,\<cal-I\>\<vDash\>\<exists\>FV<around*|(|D<rsub|i>,F<rsub|res>|)>.D<rsub|i>\<wedge\>F<rsub|res>>.
  </definition>

  We are more interested in finding an unambiguous, directly given solution
  to a type inference problem, as introduced in Definition
  <reference|SolTypInfer>, than in derivability of a judgement
  <math|C,\<Gamma\>\<vdash\>e:\<tau\>> for some satisfiable <math|C>. By
  Theorems <reference|InfCorrExpr> and <reference|InfComplExpr>, these
  notions are close. Therefore, unlike in <math|HMG<around*|(|X|)>>, we say
  that an expression <math|e> is <em|well-typed> in <math|MMG<around*|(|X|)>>
  under environment <math|\<Gamma\>> with type <math|\<tau\>>, when the type
  inference problem <math|<around*|\<llbracket\>|\<Gamma\>\<vdash\>e:\<tau\>|\<rrbracket\>>>
  has a solution. The class of programs admitting a solution to the type
  inference problem can sometimes be expanded by enriching the languages of
  constraint domains.

  Note that both the derivability of <math|C,\<Gamma\>\<vdash\>e:\<tau\>> and
  the existence of a solution to the type inference problem
  <math|<around*|\<llbracket\>|\<Gamma\>\<vdash\>e:<no-break>\<tau\>|\<rrbracket\>>>
  allows for dead code in <math|e>, i.e. unreachable cases of pattern
  matching. We offer an option to reject programs with dead code, according
  to the following definition: We call <math|\<exists\><wide|\<alpha\>|\<bar\>><rsub|res>.F<rsub|res>,\<cal-I\>>
  a <em|solution without dead code to the type inference problem>
  <math|<around*|\<llbracket\>|\<Gamma\>\<vdash\>e:<no-break>\<tau\>|\<rrbracket\>>>
  when <math|\<cal-I\>,\<cal-M\>\<vDash\>F<rsub|res>\<Rightarrow\>\<Phi\><rsub|N>>
  (i.e. <math|\<cal-M\>\<vDash\>F<rsub|res>\<Rightarrow\>\<cal-I\><around*|(|\<Phi\><rsub|N>|)>>),
  <math|\<cal-M\>\<vDash\>\<cal-Q\>.F<rsub|res><around*|[|<wide|\<alpha\>|\<bar\>><rsub|res>\<assign\><wide|t|\<bar\>>|]>>
  for some <math|<wide|t|\<bar\>>>, and for every implication in
  <math|\<Phi\><rsub|N>>, if <math|C<rsub|i>\<neq\>\<b-F\>> then
  <math|\<cal-M\>,\<cal-I\>\<vDash\>\<exists\>FV<around*|(|D<rsub|i>,<no-break>F<rsub|res>|)>.D<rsub|i>\<wedge\><no-break>F<rsub|res>>.
  However, some datatype-related dead code cases are rejected regardless of
  this option, due to constraints introduced by
  <math|<around*|\<llbracket\>|\<vdash\>p\<downarrow\>\<tau\><around*|\<rrbracket\>||\<nobracket\>>|\<nobracket\>>>
  for patterns <math|p>.

  <section|Existential Types><label|ExTypes>

  In context of GADTs, existential types play a prominent role, beyond the
  traditional role of abstraction in software engineering. Without
  existential types, computations would need to express parameters of the
  output datatype invariant as a function of parameters of the input datatype
  invariant. Since GADTs are introduced to curtail the expressiveness of
  types compared to full dependent type systems, opportunities for such
  functional dependency are rare by design.

  We need the capacity in the type system to express whatever relations it
  can of the resulting datatype parameters to the input datatype parameters.
  Traditionally in GADTs we package the result into a custom datatype. This
  is tedious and contrary to the benefits of type inference. We automate this
  process, in effect introducing inferred existential types to our type
  system. Since the modification of the type system is minimal, formal
  guarantees carry over to it and it will be familiar to users of GADTs.

  Existential quantifiers in (contravariant) argument positions of function
  types are redundant: they can be lifted to be traditional, polymorphic
  variables constrained by the invariant of the function. However, they may
  sometimes be needed in nested positions of higher-order function types. We
  prohibit the use of inferred existential types in argument positions in the
  current version of the type system.

  We introduce a new expression construct
  <math|\<lambda\><around*|[|K|]><wide|c|\<bar\>>>, where <math|K> is a value
  constructor, but is not available in concrete syntax, and
  <math|<wide|c|\<bar\>>> are pattern matching clauses. In the
  implementation, the parser introduces a fresh <math|K> and forms
  <math|\<lambda\><around*|[|K|]><wide|c|\<bar\>>> for <verbatim|efunction
  <math|<wide|c|\<bar\>>>>. We also introduce a corresponding construct
  <math|\<lambda\><rsub|K><wide|c|\<bar\>>>.
  <math|\<lambda\><around*|[|K|]><wide|c|\<bar\>>> is either eliminated or
  replaced by <math|\<lambda\><rsub|K><wide|c|\<bar\>>> in a normalization
  step. When <with|mode|math|K\<colons\>\<forall\><wide|\<alpha\>|\<bar\>><wide|\<beta\>|\<bar\>>\<gamma\><around|[|E|]>.\<gamma\>\<rightarrow\>\<varepsilon\><rsub|K><around*|(|<wide|\<alpha\>|\<bar\>>|)>\<in\>\<Sigma\>>
  is such a data constructor absent from concrete syntax, the pretty-printer
  for types prints <math|\<varepsilon\><rsub|K><around*|(|<wide|\<tau\>|\<bar\>>|)>>
  as <math|\<exists\><wide|\<beta\>|\<bar\>>\<gamma\><around*|[|E<around*|[|<wide|\<alpha\>|\<bar\>>\<assign\><wide|\<tau\>|\<bar\>>|]>|]>.\<gamma\>>,
  or <math|\<exists\><wide|\<beta\>|\<bar\>><around*|[|E<around*|[|<wide|\<alpha\>|\<bar\>>\<assign\><wide|\<tau\>|\<bar\>>|]>|]>.\<tau\><rsub|e>>
  when <math|E> implies <math|\<gamma\><wide|=|\<dot\>>\<tau\><rsub|e>>. We
  also parse <math|\<exists\><wide|\<beta\>|\<bar\>><around*|[|E|]>.\<tau\><rsub|e>>
  generating a fresh <with|mode|math|K\<colons\>\<forall\><wide|\<alpha\>|\<bar\>><wide|\<beta\>|\<bar\>><around|[|E|]>.\<tau\><rsub|e>\<rightarrow\>\<varepsilon\><rsub|K><around*|(|<wide|\<alpha\>|\<bar\>>|)>\<in\>\<Sigma\>>
  in the toplevel <math|\<Sigma\>>, where
  <math|<wide|\<alpha\>|\<bar\>>=<no-break>FV<around*|(|\<tau\><rsub|e>|)>\\<wide|\<beta\>|\<bar\>>>.

  Let <math|l<around*|(|e|)>> defined in Table <reference|IsExBrs> determine
  whether an expression introduces or eliminates an existential type. It is
  used in the normalization process described below.

  Let all occurrences of <math|\<lambda\><around*|[|K|]>> in <math|e> use
  distinct <math|K>. Let <math|n<around*|(|e|)>\<assign\>n<around*|(|e,\<bot\>|)>>,
  defined in Table <reference|NormExpr>, flatten nested introductions of
  existential types. Let <math|\<cal-E\><around*|(|e|)>\<assign\>\<cal-E\><around*|(|e,\<b-F\>|)>>,
  defined in Table <reference|CollectK>, collect value constructors
  introduced for existential types. The normalization-related functions
  <math|n<around*|(|\<cdummy\>,v|)>> and <math|\<cal-E\><around*|(|\<cdummy\>,v|)>>
  are defined for both expressions and clauses.

  The <math|MMG<rsub|\<exists\>><around*|(|X|)>> typing rules that differ
  from <math|MMG<around*|(|X|)>> are provided in Table
  <reference|ExTypingRul>. We put the normalization step into the type system
  as a rule <name|ExIntro>. W.l.o.g. <name|ExIntro> can be used once at the
  beginning of a derivation. <name|ExIntro> performs a normalization of the
  expression and shares the job of introducing existential types with the
  rule <name|ExAbs>. The <math|RetType> relation can be introduced into the
  model <math|\<cal-M\>> by induction on the structure of the first argument:
  <math|RetType<around*|(|\<tau\><rsub|1>\<rightarrow\>\<tau\><rsub|2>,\<tau\><rsub|3>|)>\<Leftrightarrow\>RetType<around*|(|\<tau\><rsub|2>,\<tau\><rsub|3>|)>>
  and <math|RetType<around*|(|\<varepsilon\><around*|(|<wide|\<tau\>|\<bar\>>|)>,\<tau\><rprime|'>|)>\<Leftrightarrow\>\<varepsilon\><around*|(|<wide|\<tau\>|\<bar\>>|)><wide|=|\<dot\>>\<tau\><rprime|'>>.
  <name|ExLetIn> is the elimination rule for existential types. Although
  <name|LetIn> and <name|ExLetIn> resemble ``syntactic sugar'', their
  application is non-deterministic. We include value constructor environment
  in judgments to facilitate the completeness proof. We modify the rule
  <name|App> to exclude function arguments that have existential types. We
  achieve that by introducing a new atomic predicate <math|<neg|E>> to the
  sort <math|s<rsub|type>>: <math|<neg|E><around*|(|\<tau\>|)>> iff
  <math|\<wedge\><rsub|K>\<neg\><no-break>\<exists\><wide|\<alpha\>|\<bar\>>.\<tau\><wide|=|\<dot\>>\<varepsilon\><rsub|K><around*|(|<wide|\<alpha\>|\<bar\>>|)>>,
  i.e. <math|\<tau\>> is not an existential type.<\float|float|t>
    <\big-table>
      <\eqnarray*>
        <tformat|<table|<row|<cell|n<around*|(|e,K<rprime|'>|)>>|<cell|=>|<cell|<text|<with|font-shape|condensed|<strong|let>>>
        x=n<around*|(|e,\<bot\>|)> <text|<with|font-shape|condensed|<strong|in>>>K<rprime|'>
        x>>|<row|<cell|<with|mode|text|when
        >K<rprime|'>\<neq\>\<bot\>\<wedge\>l<around*|(|e|)>=\<b-F\>>|<cell|>|<cell|>>|<row|<cell|n<around*|(|x,\<bot\>|)>>|<cell|=>|<cell|x>>|<row|<cell|n<around*|(|\<lambda\><wide|c|\<bar\>>,\<bot\>|)>>|<cell|=>|<cell|\<lambda\><around*|(|<wide|n<around*|(|c,\<bot\>|)>|\<bar\>>|)>>>|<row|<cell|n<around*|(|e<rsub|1>
        e<rsub|2>,K<rprime|'>|)>>|<cell|=>|<cell|n<around*|(|e<rsub|1>,K<rprime|'>|)>
        n<around*|(|e<rsub|2>,\<bot\>|)>>>|<row|<cell|n<around*|(|K
        e<rsub|1>\<ldots\>e<rsub|n>,\<bot\>|)>>|<cell|=>|<cell|K
        n<around*|(|e<rsub|1>,\<bot\>|)>\<ldots\>n<around*|(|e<rsub|n>,\<bot\>|)>>>|<row|<cell|n<around*|(|<text|<with|font-shape|condensed|<strong|let
        rec>>> x=e<rsub|1> <text|<with|font-shape|condensed|<strong|in>>>
        e<rsub|2>,K<rprime|'>|)>>|<cell|=>|<cell|<text|<with|font-shape|condensed|<strong|let
        rec>>> x=n<around*|(|e<rsub|1>,\<bot\>|)>
        <text|<with|font-shape|condensed|<strong|in>>>
        n<around*|(|e<rsub|2>,K<rprime|'>|)>>>|<row|<cell|n<around*|(|p
        <text|<with|font-shape|condensed|<strong|when>>>
        <wide|m<rsub|i>\<leqslant\>n<rsub|i>|\<bar\>>.e,K<rprime|'>|)>>|<cell|=>|<cell|p
        <text|<with|font-shape|condensed|<strong|when>>>
        <wide|n<around*|(|m<rsub|i>,\<bot\>|)>\<leqslant\>n<around*|(|n<rsub|i>,\<bot\>|)>|\<bar\>>.<text|<with|font-shape|condensed|<strong|runtime
        failure>>> n<around*|(|s,\<bot\>|)>>>|<row|<cell|<with|mode|text|when
        >e=<text|<with|font-shape|condensed|<strong|runtime failure>>>
        s>|<cell|>|<cell|>>|<row|<cell|n<around*|(|p
        <text|<with|font-shape|condensed|<strong|when>>>
        <wide|m<rsub|i>\<leqslant\>n<rsub|i>|\<bar\>>.e,K<rprime|'>|)>>|<cell|=>|<cell|p
        <text|<with|font-shape|condensed|<strong|when>>>
        <wide|n<around*|(|m<rsub|i>,\<bot\>|)>\<leqslant\>n<around*|(|n<rsub|i>,\<bot\>|)>|\<bar\>>.n<around*|(|e,K<rprime|'>|)>>>|<row|<cell|<with|mode|text|when
        >e\<neq\><text|<with|font-shape|condensed|<strong|runtime failure>>>
        s>|<cell|>|<cell|>>|<row|<cell|n<around*|(|\<lambda\><around*|[|K|]><wide|c|\<bar\>>,\<bot\>|)>>|<cell|=>|<cell|\<lambda\><rsub|K><around*|(|<wide|n<around*|(|c,K|)>|\<bar\>>|)>>>|<row|<cell|n<around*|(|\<lambda\><around*|[|K|]><wide|c|\<bar\>>,K<rprime|'>|)>>|<cell|=>|<cell|\<lambda\><around*|(|<wide|n<around*|(|c,K<rprime|'>|)>|\<bar\>>|)>>>|<row|<cell|<with|mode|text|when
        >K<rprime|'>\<neq\>\<bot\>>|<cell|>|<cell|>>|<row|<cell|n<around*|(|<text|<with|font-shape|condensed|<strong|let>>>
        p=e<rsub|1> <text|<with|font-shape|condensed|<strong|in>>>
        e<rsub|2>,K<rprime|'>|)>>|<cell|=>|<cell|<text|<with|font-shape|condensed|<strong|let>>>
        p=n<around*|(|e<rsub|1>,\<bot\>|)>
        <text|<with|font-shape|condensed|<strong|in>>>
        n<around*|(|e<rsub|2>,K<rprime|'>|)>>>|<row|<cell|n<around*|(|<text|<with|font-shape|condensed|<strong|assert
        num>>> e<rsub|1>\<leqslant\>e<rsub|2>;e<rsub|3>,K<rprime|'>|)>>|<cell|=>|<cell|<text|<with|font-shape|condensed|<strong|assert
        num>>> n<around*|(|e<rsub|1>,\<bot\>|)>\<leqslant\>n<around*|(|e<rsub|2>,\<bot\>|)>;n<around*|(|e<rsub|3>,K<rprime|'>|)>>>|<row|<cell|n<around*|(|<text|<with|font-shape|condensed|<strong|assert
        type>>> e<rsub|1>=e<rsub|2>;e<rsub|3>,K<rprime|'>|)>>|<cell|=>|<cell|<text|<with|font-shape|condensed|<strong|assert
        type>>> n<around*|(|e<rsub|1>,\<bot\>|)>=n<around*|(|e<rsub|2>,\<bot\>|)>;n<around*|(|e<rsub|3>,K<rprime|'>|)>>>>>
      </eqnarray*>

      <label|NormExpr>
    </big-table|Flatten nested introductions of existential types>
  </float><\float|float|t>
    <\big-table>
      <\itemize>
        <tabular|<tformat|<cwith|1|1|3|3|cell-col-span|2>|<cwith|2|2|3|3|cell-col-span|2>|<table|<row|<cell|<name|App>>|<cell|>|<cell|<name|ExLetIn>>|<cell|>>|<row|<cell|<math|<large|<frac|<tabular|<tformat|<cwith|1|1|1|1|cell-col-span|2>|<table|<row|<cell|C,\<Gamma\>,\<Sigma\>\<vdash\>e<rsub|1>:\<tau\><rprime|'>\<rightarrow\>\<tau\>>|<cell|>>|<row|<cell|C,\<Gamma\>,\<Sigma\>\<vdash\>e<rsub|2>:\<tau\><rprime|'>>|<cell|C\<vDash\><neg|E><around*|(|\<tau\><rprime|'>|)>>>>>>|C,\<Gamma\>,\<Sigma\>\<vdash\>e<rsub|1>
        e<rsub|2>:\<tau\>>>>>|<cell|>|<cell|<large|<math|<frac|<tabular|<tformat|<cwith|2|2|1|1|cell-col-span|2>|<table|<row|<cell|\<varepsilon\><rsub|K><around*|(|<wide|\<alpha\>|\<bar\>>|)><with|mode|text|
        in >\<Sigma\>>|<cell|<with|mode|text|
        >C,\<Gamma\>,\<Sigma\>\<vdash\>e<rsub|1>:\<tau\><rprime|'>>>|<row|<cell|C,\<Gamma\>,\<Sigma\>\<vdash\>K
        p.e<rsub|2>:\<tau\><rprime|'>\<rightarrow\>\<tau\>>|<cell|>>>>>|C,\<Gamma\>,\<Sigma\>\<vdash\><rsup|><text|<with|font-shape|condensed|<strong|let>>>
        p=e<rsub|1> <text|<with|font-shape|condensed|<strong|in>>>
        e<rsub|2>:\<tau\>>>>>|<cell|>>|<row|<cell|>|<cell|>|<cell|>|<cell|>>|<row|<cell|<name|ExIntro>>|<cell|>|<cell|<name|ExAbs>>|<cell|>>|<row|<cell|<math|<large|<frac|<tabular|<tformat|<table|<row|<cell|Dom<around*|(|\<Sigma\><rprime|'>|)>\\Dom<around*|(|\<Sigma\>|)>=\<cal-E\><around*|(|e|)>>>|<row|<cell|C,\<Gamma\>,\<Sigma\><rprime|'>\<vdash\>n<around*|(|e|)>:\<tau\>>>>>>|C,\<Gamma\>,\<Sigma\>\<vdash\>e:\<tau\>>>>>|<cell|>|<cell|<large|<math|<frac|<tabular|<tformat|<table|<row|<cell|C\<vDash\>RetType<around*|(|\<tau\>,\<varepsilon\><rsub|K><around*|(|\<tau\><rprime|'>|)>|)>>>|<row|<cell|C,\<Gamma\>\<vdash\>\<lambda\><wide|c|\<bar\>>:\<tau\><rsub|>>>>>>|C,\<Gamma\>\<vdash\>\<lambda\><rsub|K><wide|c|\<bar\>>:\<tau\>>>>>|<cell|>>>>>

        \;
      </itemize>

      <label|ExTypingRul>
    </big-table|Typing rules added by <math|MMG<rsub|\<exists\>><around*|(|X|)>>>
  </float><\float|float|t>
    <\big-table>
      <\eqnarray*>
        <tformat|<table|<row|<cell|<around*|\<llbracket\>|\<Gamma\>\<vdash\>e<rsub|1>
        e<rsub|2>:\<tau\>|\<rrbracket\>>>|<cell|=>|<cell|\<exists\>\<alpha\>.<around*|\<llbracket\>|\<Gamma\>\<vdash\>e<rsub|1>:\<alpha\>\<rightarrow\>\<tau\>|\<rrbracket\>>\<wedge\><around*|\<llbracket\>|\<Gamma\>\<vdash\>e<rsub|2>:\<alpha\>|\<rrbracket\>>\<wedge\><neg|E><around*|(|\<alpha\>|)>,\<alpha\>#FV<around|(|\<Gamma\>,\<tau\>|)>>>|<row|<cell|>|<cell|>|<cell|>>|<row|<cell|<around*|\<llbracket\>|\<Gamma\>,\<Sigma\><rsub|0>\<vdash\>e:\<tau\>|\<rrbracket\>>>|<cell|=>|<cell|<around*|\<llbracket\>|\<Gamma\>,\<Sigma\>\<vdash\>n<around*|(|e|)>:\<tau\>|\<rrbracket\>>>>|<row|<cell|<with|mode|text|when
        >\<cal-E\><around*|(|e|)>\<neq\>\<varnothing\>>|<cell|>|<cell|<with|mode|text|where
        >\<Sigma\>=\<Sigma\><rsub|0><wide|K\<colons\>\<forall\>\<alpha\><rsub|K>\<gamma\><rsub|K><around|[|\<chi\><rsub|K><around*|(|\<gamma\><rsub|K>,\<alpha\><rsub|K>|)>|]>.\<gamma\><rsub|K>\<rightarrow\>\<varepsilon\><rsub|K><around*|(|\<alpha\><rsub|K>|)>|\<bar\>><rsub|K\<in\>\<cal-E\><around*|(|e|)>>>>|<row|<cell|>|<cell|>|<cell|>>|<row|<cell|<around*|\<llbracket\>|\<Gamma\>\<vdash\><text|<with|font-shape|condensed|<strong|let>>>
        p=e<rsub|1> <text|<with|font-shape|condensed|<strong|in>>>
        e<rsub|2>:\<tau\>|\<rrbracket\>>>|<cell|=>|<cell|\<exists\>\<alpha\><rsub|0>.<around*|\<llbracket\>|\<Gamma\>\<vdash\>e<rsub|1>:\<alpha\><rsub|0>|\<rrbracket\>>\<wedge\><around*|(|<around*|\<llbracket\>|\<Gamma\>\<vdash\>p.e<rsub|2>:\<alpha\><rsub|0>\<rightarrow\>\<tau\>|\<rrbracket\>>\<wedge\><neg|E><around*|(|\<alpha\><rsub|0>|)><next-line><with|mode|text|
        \ \ \ \ \ >\<vee\><rsub|\<cal-E\>><around*|\<llbracket\>|\<Gamma\>\<vdash\>K
        p.e<rsub|2>:\<alpha\><rsub|0>\<rightarrow\>\<tau\>|\<rrbracket\>>|)>>>|<row|<cell|>|<cell|>|<cell|>>|<row|<cell|>|<cell|>|<cell|<text|where
        >\<cal-E\>=<around*|{|K<mid|\|>K\<colons\>\<forall\><wide|\<alpha\>|\<bar\>><wide|\<beta\>|\<bar\>><around|[|E|]>.\<tau\>\<rightarrow\>\<varepsilon\><rsub|K><around*|(|<wide|\<alpha\>|\<bar\>>|)>\<in\>\<Sigma\>|}>>>|<row|<cell|>|<cell|>|<cell|>>|<row|<cell|<around*|\<llbracket\>|\<Gamma\>\<vdash\>\<lambda\><rsub|K><wide|c|\<bar\>>:\<tau\>|\<rrbracket\>>>|<cell|=>|<cell|\<exists\>\<alpha\><rsub|0>.RetType<around*|(|\<tau\>,\<alpha\><rsub|0>|)>\<wedge\><around*|(|\<exists\>\<alpha\><rsub|1>.\<alpha\><rsub|0><wide|=|\<dot\>>\<varepsilon\><rsub|K><around*|(|\<alpha\><rsub|1>|)>\<wedge\>\<chi\><rsub|K><around*|(|\<alpha\><rsub|1>|)>|)>\<wedge\><around*|\<llbracket\>|\<Gamma\>\<vdash\>\<lambda\><wide|c|\<bar\>>:\<tau\>|\<rrbracket\>>,<with|mode|text|>\<alpha\><rsub|0>\<alpha\><rsub|1>#FV<around|(|\<Gamma\>,\<tau\>|)>>>>>
      </eqnarray*>

      <label|ExIntermInf>
    </big-table|Type inference for the added expressions>
  </float>

  <\definition>
    <label|WellTypedEx>Let <math|\<Sigma\>=\<Sigma\><rsub|0>\<cup\>\<Sigma\><rsub|e>>
    and <math|\<Sigma\><rprime|'>=\<Sigma\><rsub|0>\<cup\>\<Sigma\><rsub|e><rprime|'>>
    be sets of value constructors related to each other as follows:

    <\itemize>
      <item><math|PV<rsup|2><around*|(|\<Sigma\><rsub|0>|)>=\<varnothing\>>,

      <item><math|\<Sigma\><rsub|e>=<wide|K\<colons\>\<forall\>\<alpha\><rsub|K>\<gamma\><rsub|K><around|[|\<chi\><rsub|K><around*|(|\<gamma\><rsub|K>,<no-break>\<alpha\><rsub|K>|)>|]>.\<gamma\><rsub|K>\<rightarrow\>\<varepsilon\><rsub|K><around*|(|\<alpha\><rsub|K>|)>|\<bar\>>>,

      <item>and <math|\<Sigma\><rsub|e><rprime|'>=<wide|K\<colons\>\<forall\><wide|\<alpha\>|\<bar\>><rsub|K><rprime|'><wide|\<beta\>|\<bar\>><rsub|K><rprime|'>\<gamma\><rsub|K><around|[|E<rsub|K>|]>.\<gamma\><rsub|K>\<rightarrow\>\<varepsilon\><rsub|K><around*|(|<wide|\<alpha\>|\<bar\>><rsub|K><rprime|'>|)>|\<bar\>>>
    </itemize>

    where <math|\<exists\><wide|\<alpha\>|\<bar\>><rsub|K><rprime|'><wide|\<beta\>|\<bar\>><rsub|K><rprime|'>\<gamma\><rsub|K>.E<rsub|K>>
    are solved form formulas. Define <math|\<Sigma\><rprime|'>/\<Sigma\>=\<cal-I\><rsub|e>=<around*|[|<wide|\<chi\><rsub|K>|\<bar\>>\<assign\><wide|\<exists\><wide|\<alpha\>|\<bar\>><rsub|K>.F<rsub|K>|\<bar\>>|]>>,
    where <math|F<rsub|K>=E<rsub|K>\<wedge\>\<alpha\><rsub|K><wide|=|\<dot\>><wide|\<alpha\><rsub|K>|\<vect\>><rprime|'>>
    and <math|<wide|\<alpha\>|\<bar\>><rsub|K>=<wide|\<alpha\>|\<bar\>><rsub|K><rprime|'><wide|\<beta\>|\<bar\>><rsub|K><rprime|'>>.
  </definition>

  \ Note that we do not lose generality by using single-argument datatypes
  <math|\<varepsilon\><rsub|K><around*|(|\<alpha\>|)>> rather than the
  general form <math|\<varepsilon\><rsub|K><around*|(|<wide|\<alpha\>|\<bar\>>|)>>.
  Multiple parameters can be captured by providing a constraint
  <math|\<exists\>\<alpha\><rsub|1>\<ldots\>\<alpha\><rsub|n>.\<alpha\><wide|=|\<dot\>>\<alpha\><rsub|1>\<rightarrow\>\<ldots\>\<rightarrow\>\<alpha\><rsub|n>>,
  with existential variables <math|\<alpha\><rsub|1>\<ldots\>\<alpha\><rsub|n>>,
  as part of the constraints of constructors of
  <math|\<varepsilon\><rsub|K><around*|(|\<alpha\>|)>>. The single parameter
  <math|\<tau\><rprime|'>> in condition <math|C\<vDash\>RetType<around*|(|\<tau\>,\<varepsilon\><rsub|K><around*|(|\<tau\><rprime|'>|)>|)>>
  of the rule <name|ExAbs> is not consequential. In the implementation of
  <name|InvarGenT>, we recover the multiple parameter representation
  <math|\<varepsilon\><rsub|K><around*|(|<wide|\<alpha\>|\<bar\>>|)>> of
  existential types, at the end of inference.

  Normalization defined in Table <reference|NormExpr> is responsible for
  introduction of existential types, but it also ensures that existential
  types never directly wrap around other existential types. This flattening
  enables the use of all information available to derive the postcondition,
  i.e. the existential type. To flatten nested existential types, we rename
  constructors <math|K> to <math|K<rprime|'>> in
  <math|n<around*|(|\<lambda\><around*|[|K|]><wide|c|\<bar\>>,K<rprime|'>|)>>,
  and eliminate potential existential type before introducing one in
  <math|n<around*|(|e,K<rprime|'>|)>> when
  <math|K<rprime|'>\<neq\>\<bot\>\<wedge\>l<around*|(|e|)>=\<b-F\>>. Note the
  frequent need to use <verbatim|efunction> (and its syntax sugar forms
  <verbatim|ematch> and <verbatim|eif>) for all branches of a definition, as
  for example in function <verbatim|bsearch2> in Section
  <reference|ExBsearch2>. The branches bound by <verbatim|match> or
  <verbatim|if> would be required to have the exact same type, e.g. the same
  number <verbatim|Num>, height of a tree or length of a list.

  <section|Type Inference Constraints for Existential
  Types><label|ExTypesCns>

  The type inference uses predicate variables to determine the information
  bundled inside existential types. The constraint derivation rules related
  to existential types are provided in Table <reference|ExIntermInf>. For the
  initial call to <math|<around*|\<llbracket\>|\<cdummy\>|\<rrbracket\>>>
  (i.e. case <math|\<cal-E\><around*|(|e|)>\<neq\>\<varnothing\>>), we
  normalize the expression. We shorten <math|<around*|\<llbracket\>|\<Gamma\>,\<Sigma\>\<vdash\>\<cdummy\>:\<tau\>|\<rrbracket\>>>
  to <math|<around*|\<llbracket\>|\<Gamma\>\<vdash\>\<cdummy\>:\<tau\>|\<rrbracket\>>>.

  Our tools for solving second order constraints only handle conjunctions of
  implications. We solve disjunctions early, which is problematic as
  selecting a disjunct may require information hidden in other disjunctions
  or in predicate variables. For example, in the normalization of constraints
  we need to associate each unary predicate variable with at most one
  inferred existential type that can occur as return type in its solution.
  The pragmatics we adopt in <name|InvarGenT> is that whenever the
  <math|<around*|\<llbracket\>|\<Gamma\>\<vdash\>p.e<rsub|2>:\<alpha\><rsub|0>\<rightarrow\>\<tau\>|\<rrbracket\>>>
  disjunct coming from the <name|LetIn> rule is satisfiable with the rest of
  the constraint, we select it for the solution. One can turn the pragmatics
  into semantics by adding the premise <math|C,\<Gamma\>,\<Sigma\>\<nvdash\>\<lambda\><around*|(|p.e<rsub|2>|)>
  e<rsub|1>:\<tau\>> to the <name|ExLetIn> rule, but it would make the
  formalism more complex. The proof of the following theorem is in Section
  <reference|ExGADTsProofs>.

  <\theorem>
    <label|InfCorrComplEx>Theorems <reference|InfCorrExpr> (Correctness) and
    <reference|InfComplExpr> (Completeness) hold for the type system extended
    with <name|ExIntro> and <name|ExLetIn> in the following sense. Recall the
    notation from Theorem <reference|InfComplExpr>.

    Correctness: For all <math|\<Gamma\>,\<Sigma\>,e> and <math|\<tau\>>,
    <math|<around*|\<llbracket\>|\<Gamma\>,\<Sigma\>\<vdash\>e:\<tau\>|\<rrbracket\>>,\<Gamma\>,\<Sigma\>\<vdash\>e:\<tau\>>
    is derivable.

    Completeness: For all <math|\<Gamma\>,\<Sigma\>,e> and <math|\<tau\>>, if
    <math|PV<around*|(|C,\<Gamma\>,\<Sigma\>|)>=\<varnothing\>> and
    <math|C,\<Gamma\>,\<Sigma\>\<vdash\>e:\<tau\>>, then there exist
    interpretations of predicate variables
    <math|\<cal-I\><rsub|u>,\<cal-I\><rsub|e>> such that
    <math|Dom<around*|(|\<cal-I\><rsub|u>|)>> are unary,
    <math|Dom<around*|(|\<cal-I\><rsub|e>|)>=<around*|{|\<chi\><rsub|K><mid|\|>K\<in\>\<cal-E\><around*|(|e|)>|}>>,
    and <math|\<cal-M\>,\<cal-I\><rsub|u>\<vDash\>C\<Rightarrow\>\<cal-I\><rsub|e><around*|(|<around*|\<llbracket\>|\<Gamma\>,\<Sigma\>\<vdash\>e:\<tau\>|\<rrbracket\>>|)><around*|[|<wide|\<varepsilon\><rsub|K><around*|(|<wide|\<tau\>|\<vect\>>|)>|\<bar\>>\<assign\><wide|\<varepsilon\><rsub|K><around*|(|<wide|\<tau\>|\<bar\>>|)>|\<bar\>>|]>>.
  </theorem>

  The set of value constructors is updated in <name|InvarGenT> after a
  toplevel definition with a well typed body: from <math|\<Sigma\><rsub|0>>
  to <math|\<Sigma\><rprime|'>>, using the notation from Definition
  <reference|WellTypedEx>.

  <\example>
    Consider the function <verbatim|filter> for lists with length. The
    <verbatim|eif><math|\<ldots\>><verbatim|then<math|>><math|\<ldots\>><verbatim|else>
    syntax is a syntactic sugar for the <verbatim|ematch><math|\<ldots\>><verbatim|with
    True -\<gtr\>><math|\<ldots\>><verbatim| \| False
    -\<gtr\>><math|\<ldots\>> syntax, which in turn is a syntactic sugar for
    <verbatim|(efunction True -\<gtr\>><math|\<ldots\>><verbatim| \| False
    -\<gtr\>><math|\<ldots\>><verbatim|)><math|\<ldots\>> expressions.

    <\code>
      datatype List : type * num

      datacons LNil : <math|\<forall\>>a. List(a, 0)

      datacons LCons :

      \ \ <math|\<forall\>>n, a [0<math|\<leqslant\>>n]. a * List(a, n)
      <math|\<longrightarrow\>> List(a, n+1)

      \;

      let rec filter = fun f -\<gtr\>

      \ \ efunction LNil -\<gtr\> LNil

      \ \ \| LCons (x, xs) -\<gtr\>

      \ \ \ \ eif f x

      \ \ \ \ then let ys = filter f xs in LCons (x,ys)

      \ \ \ \ else filter f xs
    </code>

    As an aside, an example interaction with <name|InvarGenT> might look as
    follows:

    <\code>
      $ ./invargent -inform examples/filter.gadt

      val filter :

      \ \ <math|\<forall\>>n, a.

      \ \ (a <math|\<rightarrow\>> Bool) <math|\<rightarrow\>> List (a, n)
      <math|\<rightarrow\>> <math|\<exists\>>k[0 <math|\<leqslant\>> k
      <math|\<wedge\>> k <math|\<leqslant\>> n].List (a, k)

      InvarGenT: Generated file examples/filter.gadti

      InvarGenT: Generated file examples/filter.ml

      InvarGenT: Command "ocamlc -w -25 -c examples/filter.ml" exited with
      code 0
    </code>

    Below we show the corresponding type inference constraint, slightly
    simplified by hand for readability. Constructors such as
    <math|\<varepsilon\><rsub|K<rsub|2>><around*|(|\<alpha\><rsub|6>|)>>
    identify an occurrence of an existential type, here
    <math|\<exists\>\<delta\>.\<chi\><rsub|1><around*|(|\<delta\>,\<alpha\><rsub|6>|)>>
    in a constructor environment with <math|K<rsub|2>\<colons\>\<forall\>\<delta\>\<alpha\><around*|[|\<chi\><rsub|1><around*|(|\<delta\>,\<alpha\>|)>|]>.\<delta\>\<rightarrow\>\<varepsilon\><rsub|K<rsub|2>><around*|(|\<alpha\>|)>>.

    <\eqnarray*>
      <tformat|<cwith|1|1|1|1|cell-col-span|3>|<cwith|1|1|1|1|cell-halign|c>|<table|<row|<cell|\<exists\>\<alpha\><rsub|0>.\<forall\>\<beta\><rsub|0>.\<exists\>n<rsub|1>\<alpha\><rsub|1>\<alpha\><rsub|2>\<alpha\><rsub|3>.\<forall\>k<rsub|1>\<beta\><rsub|1>\<beta\><rsub|2>.\<exists\>\<alpha\><rsub|5>\<alpha\><rsub|6>\<alpha\><rsub|7>\<alpha\><rsub|8>\<alpha\><rsub|9>.\<forall\>\<beta\><rsub|3>\<beta\><rsub|4>\<beta\><rsub|5>\<beta\><rsub|6>.\<exists\>n<rsub|2>\<alpha\><rsub|10>\<alpha\><rsub|11>\<alpha\><rsub|12>\<alpha\><rsub|13>.>|<cell|>|<cell|>>|<row|<cell|>|<cell|>|<cell|\<chi\><rsub|2><around*|(|\<alpha\><rsub|0>|)><eq-number><label|ExCnBr1>>>|<row|<cell|>|<cell|\<wedge\>>|<cell|>>|<row|<cell|\<chi\><rsub|2><around*|(|\<beta\>|)>>|<cell|\<Longrightarrow\>>|<cell|\<alpha\><rsub|2><wide|=|\<dot\>>List<around*|(|\<alpha\><rsub|4>,n<rsub|1>|)>\<wedge\>\<beta\><wide|=|\<dot\>>\<alpha\><rsub|1>\<rightarrow\>List<around*|(|\<alpha\><rsub|4>,n<rsub|1>|)>\<rightarrow\>\<alpha\><rsub|3><eq-number><label|ExCnBr2>>>|<row|<cell|>|<cell|\<wedge\>>|<cell|>>|<row|<cell|List<around*|(|\<beta\><rsub|1>,0|)><wide|=|\<dot\>>List<around*|(|\<alpha\><rsub|4>,n<rsub|1>|)>\<wedge\>\<chi\><rsub|2><around*|(|\<beta\>|)>>|<cell|\<Longrightarrow\>>|<cell|\<alpha\><rsub|3><wide|=|\<dot\>>\<varepsilon\><rsub|K<rsub|2>><around*|(|\<alpha\><rsub|6>|)>\<wedge\>\<chi\><rsub|1><around*|(|List<around*|(|\<alpha\><rsub|5>,0|)>,\<alpha\><rsub|6>|)><eq-number><label|ExCnBr3>>>|<row|<cell|>|<cell|\<wedge\>>|<cell|>>|<row|<cell|List<around*|(|\<beta\><rsub|2>,k<rsub|1>+1|)><wide|=|\<dot\>>List<around*|(|\<alpha\><rsub|4>,n<rsub|1>|)>\<wedge\>>|<cell|\<Longrightarrow\>>|<cell|\<alpha\><rsub|1><wide|=|\<dot\>>\<beta\><rsub|2>\<rightarrow\>Bool\<wedge\><eq-number><label|ExCnBr4>>>|<row|<cell|0\<leq\>k<rsub|1>\<wedge\>\<chi\><rsub|2><around*|(|\<beta\>|)>>|<cell|>|<cell|\<chi\><rsub|2><around*|(|\<alpha\><rsub|1>\<rightarrow\>List<around*|(|\<beta\><rsub|2>,k<rsub|1>|)>\<rightarrow\>\<varepsilon\><rsub|K<rsub|2>><around*|(|\<alpha\><rsub|8>|)>|)>\<wedge\>>>|<row|<cell|>|<cell|>|<cell|\<chi\><rsub|2><around*|(|\<alpha\><rsub|1>\<rightarrow\>List<around*|(|\<beta\><rsub|2>,k<rsub|1>|)>\<rightarrow\>\<varepsilon\><rsub|K<rsub|2>><around*|(|\<alpha\><rsub|9>|)>|)>>>|<row|<cell|>|<cell|\<wedge\>>|<cell|>>|<row|<cell|\<varepsilon\><rsub|K<rsub|2>><around*|(|\<beta\><rsub|4>|)><wide|=|\<dot\>>\<varepsilon\><rsub|K<rsub|2>><around*|(|\<alpha\><rsub|8>|)>\<wedge\>\<chi\><rsub|1><around*|(|\<beta\><rsub|3>,\<beta\><rsub|4>|)>\<wedge\>>|<cell|\<Longrightarrow\>>|<cell|\<alpha\><rsub|3><wide|=|\<dot\>>\<varepsilon\><rsub|K<rsub|2>><around*|(|\<alpha\><rsub|8>|)>\<wedge\>\<chi\><rsub|1><around*|(|\<alpha\><rsub|10>,\<alpha\><rsub|11>|)>\<wedge\>\<beta\><rsub|3><wide|=|\<dot\>>List<around*|(|\<beta\><rsub|2>,n<rsub|2>|)>\<wedge\>>>|<row|<cell|List<around*|(|\<beta\><rsub|2>,k<rsub|1>+1|)><wide|=|\<dot\>>List<around*|(|\<alpha\><rsub|4>,n<rsub|1>|)>\<wedge\>>|<cell|>|<cell|\<alpha\><rsub|10><wide|=|\<dot\>>List<around*|(|\<beta\><rsub|2>,n<rsub|2>+1|)>\<wedge\>0\<leq\>n<rsub|2><eq-number><label|ExCnBr5>>>|<row|<cell|0\<leq\>k<rsub|1>\<wedge\>\<chi\><rsub|2><around*|(|\<beta\>|)>>|<cell|>|<cell|>>|<row|<cell|>|<cell|\<wedge\>>|<cell|>>|<row|<cell|\<varepsilon\><rsub|K<rsub|2>><around*|(|\<beta\><rsub|6>|)><wide|=|\<dot\>>\<varepsilon\><rsub|K<rsub|2>><around*|(|\<alpha\><rsub|9>|)>\<wedge\>\<chi\><rsub|1><around*|(|\<beta\><rsub|5>,\<beta\><rsub|6>|)>\<wedge\>>|<cell|\<Longrightarrow\>>|<cell|\<alpha\><rsub|12><wide|=|\<dot\>>\<beta\><rsub|5>\<wedge\>\<alpha\><rsub|3><wide|=|\<dot\>>\<varepsilon\><rsub|K<rsub|2>><around*|(|\<alpha\><rsub|13>|)>\<wedge\>\<chi\><rsub|1><around*|(|\<alpha\><rsub|12>,\<alpha\><rsub|13>|)><eq-number><label|ExCnBr6>>>|<row|<cell|List<around*|(|\<beta\><rsub|2>,k<rsub|1>+1|)><wide|=|\<dot\>>List<around*|(|\<alpha\><rsub|4>,n<rsub|1>|)>\<wedge\>>|<cell|>|<cell|>>|<row|<cell|0\<leq\>k<rsub|1>\<wedge\>\<chi\><rsub|2><around*|(|\<beta\>|)>>|<cell|>|<cell|>>>>
    </eqnarray*>

    Branch <reference|ExCnBr1> ensures that the invariant is satisfiable.
    Branch <reference|ExCnBr2> decomposes the type of the recursive
    definition and ensures that the second argument is a list. Branch
    <reference|ExCnBr3> is the case of empty list. Branch <reference|ExCnBr4>
    handles the two recursive calls. Branch <reference|ExCnBr5> is the case
    of kept element: the recursive call result <math|\<beta\><rsub|3>> has
    length one-shorter than the result <math|\<alpha\><rsub|10>>. Branch
    <reference|ExCnBr6> is the case of a dropped element: the recursive call
    result <math|\<beta\><rsub|5>> and the function result
    <math|\<alpha\><rsub|12>> are the same.
  </example>

  <section|Semantics by Reduction to <math|HMG<around*|(|X|)>>>

  The typing rules that importantly differ between <math|HMG<around*|(|X|)>>
  and <math|MMG<rsub|\<exists\>><around*|(|X|)>> are: <name|NegClause>,
  <name|FailClause>, <name|App>, <name|LetIn>, <name|ExLetIn>,
  <name|ExIntro>, <name|ExAbs>. The remaining, crucial difference lies in
  having predicate variables among constraints. However:

  <\itemize>
    <item><name|ExIntro>, <name|LetIn> and <name|ExLetIn> can be seen as
    ``desugaring'' a program to a core language,

    <item>pattern matching branches that invoke <name|NegClause> are
    unreachable and so can be dropped,

    <item>pattern matching branches that invoke <name|FailClause> can be
    dropped, because they lead to runtime failure, computationally equivalent
    to a match failure,

    <item><name|App> in <math|MMG<rsub|\<exists\>><around*|(|X|)>> is a
    restricted form of its variant from <math|HMG<around*|(|X|)>>.
  </itemize>

  Therefore, if an inference problem constraint
  <math|<around*|\<llbracket\>|\<Gamma\>,\<Sigma\>\<vdash\>e:\<tau\>|\<rrbracket\>>>
  holds, then we can build environment <math|\<Gamma\><rprime|'>>,
  constructor environment <math|\<Sigma\><rprime|'>> and an expression
  <math|e<rprime|'>> such that <math|C<rprime|'>,\<Gamma\><rprime|'>\<vdash\>e<rprime|'>:\<tau\>>
  is derivable in <math|HMG<around*|(|X|)>> for a satisfiable constraint
  <math|C<rprime|'>>. For the reduction to be a convincing argument for
  soundness of the type system, we also need to show that the ``desugared''
  expression <math|e<rprime|'>> preserves the intended meaning of <math|e>.
  For the details of the <math|HMG<around*|(|X|)>> type system, we refer the
  reader to Simonet and Pottier <cite|simonet-pottier-hmg-toplas>.

  <\definition>
    <label|SemNormForm>Consider a constructor environment <math|\<Sigma\>>
    and an <math|HMG<around*|(|X|)>> expression <math|e>. A <em|tag erasure>
    of <math|e> w.r.t. <math|\<Sigma\>> is an expression achieved by
    iteratively replacing each subpattern <math|K p<rsub|1>> of <math|e> with
    <math|K\<nin\>Dom<around*|(|\<Sigma\>|)>> by <math|p<rsub|1>> and each
    subexpression <math|K e<rsub|1>> of <math|e> with
    <math|K\<nin\>Dom<around*|(|\<Sigma\>|)>> by <math|e<rsub|1>>.

    Consider an <math|MMG<rsub|\<exists\>><around*|(|X|)>> expression
    <math|e>. An <em|HMG-form> of <math|e> is an <math|HMG<around*|(|X|)>>
    expression achieved by iteratively replacing each subexpression
    <math|\<lambda\><around*|[|K|]><wide|c|\<bar\>>> and
    <math|\<lambda\><rsub|K><wide|c|\<bar\>>> of <math|e> by
    <math|\<lambda\><wide|c|\<bar\>>>, each subexpression
    <math|<text|<with|font-shape|condensed|<strong|assert type>>>
    e<rsub|1>=e<rsub|2>;e<rsub|3>> of <math|e> by <math|e<rsub|3>>, each
    subexpression <math|<text|<with|font-shape|condensed|<strong|runtime
    failure>>> s> by a function call <math|failwith s>, and each
    subexpression <math|<text|<with|font-shape|condensed|<strong|let rec>>>
    x=e<rsub|1> <text|<with|font-shape|condensed|<strong|in>>> e<rsub|2>> in
    <math|e> by <math|<text|<with|font-shape|condensed|<strong|let>>>
    x=\<mu\> x.e<rsub|1> <text|<with|font-shape|condensed|<strong|in>>>
    e<rsub|2>>.
  </definition>

  The HMG-form from Definition <reference|SemNormForm> captures the intended
  meaning of programs. We provide semantics for the
  <math|\<lambda\>>-calculus underlying <math|MMG<rsub|\<exists\>><around*|(|X|)>>,
  by reducing each expression to its HMG-form and referring to the semantics
  for <math|HMG<around*|(|X|)>> provided in
  <cite|simonet-pottier-hmg-toplas>. In terms of concrete syntax, the
  HMG-form of a program is the program with <verbatim|assert type> clauses
  dropped, keywords <verbatim|efunction> replaced by <verbatim|function>, and
  <verbatim|ematch> replaced by <verbatim|match>.

  <\definition>
    <label|CEquiv>For our purposes, let <em|computational equivalence> be the
    smallest congruence relation <math|\<sim\><rsub|C>> such that
    <math|<text|<with|font-shape|condensed|<strong|let>>> x=e<rsub|1>
    <text|<with|font-shape|condensed|<strong|in>>>
    e<rsub|2>\<sim\><rsub|C><around*|(|\<lambda\>x.e<rsub|2>|)> e<rsub|1>>
    for any expressions <math|e<rsub|1>,e<rsub|2>>, and
    <math|\<lambda\><around*|(|<wide|p<rsub|i>.e<rsub|i>|\<bar\>>|)>\<sim\><rsub|C>\<lambda\><around*|(|<wide|p<rsub|i>.e<rsub|i><rsub|>|\<bar\>><rsub|i:\<neg\>unreach<around*|(|e<rsub|i>|)>\<wedge\>\<neg\>failure<around*|(|e<rsub|i>|)>>|)>>
    for any sequences of clauses <math|<wide|p<rsub|i>.e<rsub|i>|\<bar\>>>.
    The condition is defined by: <math|unreach<around*|(|e|)>\<assign\>e=<text|<with|font-shape|condensed|<strong|assert
    false>>>\<vee\><around*|(|e=\<lambda\><around*|(|p<rsub|1>.e<rsub|1>|)>\<wedge\>unreach<around*|(|e<rsub|1>|)>|)>>
    and <math|failure<around*|(|e|)>\<assign\>e=<text|<with|font-shape|condensed|<strong|runtime
    failure>>> s\<vee\><around*|(|e=\<lambda\><around*|(|p<rsub|1>.e<rsub|1>|)>\<wedge\>failure<around*|(|e<rsub|1>|)>|)>>.
  </definition>

  Expressions <math|<text|<with|font-shape|condensed|<strong|let>>>
  x=e<rsub|1> <text|<with|font-shape|condensed|<strong|in>>> e<rsub|2>> and
  <math|<around*|(|\<lambda\>x.e<rsub|2>|)> e<rsub|1>> have the same result
  of reduction at the outermost context: <math|e<rsub|2><around*|[|x\<assign\>e<rsub|1>|]>>.
  Subexpressions <math|<text|<with|font-shape|condensed|<strong|assert
  false>>>> in a well-typed program are guaranteed to be unreachable in both
  <math|MMG<rsub|\<exists\>><around*|(|X|)>> and <math|HMG<around*|(|X|)>>
  type systems. Subexpressions <math|<text|<with|font-shape|condensed|<strong|runtime
  failure>>> s> are intended to halt a program, so we assume they are
  computationally equivalent to match failures (matching against a value not
  covered by any pattern matching case). The proof of the follwing theorem is
  in Section <reference|SemanticProofs>.

  <\theorem>
    <label|SemRedHMG>Let <math|\<Gamma\>,\<Sigma\>\<vdash\>e:\<tau\>> be a
    typing judgment in <math|MMG<rsub|\<exists\>><around*|(|X|)>>. If
    <math|<around*|\<llbracket\>|\<Gamma\>,\<Sigma\>\<vdash\>e:\<tau\>|\<rrbracket\>>>
    is satisfiable, we can construct a satisfiable constraint
    <math|C<rprime|'>>, an <math|HMG<around*|(|X|)>> environment
    <math|\<Gamma\><rprime|'>>, constructor environment
    <math|\<Sigma\><rprime|'>> and an expression <math|e<rprime|'>> such that
    <math|C<rprime|'>,\<Gamma\><rprime|'>\<vdash\>e<rprime|'>:\<tau\>> is
    derivable in <math|HMG<around*|(|X|)>>, and the tag erasure of
    <math|e<rprime|'>> w.r.t. <math|\<Sigma\>> is computationally equivalent
    to the HMG-form of <math|e> (see Definitions <reference|SemNormForm>,
    <reference|CEquiv>).
  </theorem>

  An expression is <em|closed> when it does not contain variables not bound
  by a <math|<text|<with|font-shape|condensed|<strong|let>>>>- or
  <math|<text|<with|font-shape|condensed|<strong|let rec>>>>-expression, or a
  pattern. A closed expression is <em|stuck> if it is neither reducible nor a
  value, as defined in <cite|simonet-pottier-hmg-toplas>.

  <\corollary>
    <label|TypeSoundness><em|Type soundness>. If a closed expression <math|e>
    is well-typed under some constructor environment, then its HMG-form does
    not reduce to a stuck expression.
  </corollary>

  <chapter|Solving Second Order Constraints><label|ChapSolv>

  Least Upper Bounds and Greatest Lower Bounds computations are the standard
  tools for finding unknowns involved in an order structure, see e.g. Knowles
  and Flanagan <cite|KnowlesF07> Section 6.3. In case of implicational
  constraints, constraint abduction (see Maher and Huang
  <cite|AbductionSolvMaher>, Sulzmann, Schrijvers and Stuckey
  <cite|AbdEADTs>) and constraint generalization belong to this tool-set.
  <em|Simple Constraint Abduction> under Quantifier Prefix is the task of
  finding for an implication <math|\<cal-Q\>.D\<Rightarrow\>C>, where
  <math|\<cal-Q\>> is a quantifier prefix and <math|D,C> are conjunctions of
  atoms, a weakest solved form formula <math|\<exists\><wide|\<alpha\>|\<bar\>>.A>
  such that <math|\<cal-M\>\<vDash\><around*|(|\<exists\><wide|\<alpha\>|\<bar\>>.A|)>\<Rightarrow\><around*|(|D\<Rightarrow\>C|)>>,
  equivalently <math|\<cal-M\>\<vDash\><around*|(|\<exists\><wide|\<alpha\>|\<bar\>>.A|)>\<wedge\>D\<Rightarrow\>C>,
  <math|\<cal-M\>\<vDash\>\<exists\>FV<around*|(|A,D,C|)>.A\<wedge\>D> and
  \ <math|\<cal-M\>\<vDash\>\<cal-Q\>.A<around*|[|<wide|\<alpha\>|\<bar\>>\<assign\><wide|t|\<bar\>>|]>>
  for some <math|<wide|t|\<bar\>>>. <em|Joint Constraint Abduction> under
  Quantifier Prefix handles several implications, i.e.
  <math|\<cal-Q\>.\<wedge\><rsub|i><around*|(|D<rsub|i>\<Rightarrow\>C<rsub|i>|)>>,
  simultaneously: each condition holds for each <math|D<rsub|i>,C<rsub|i>>
  pair. It is used to solve for a predicate variable appearing in multiple
  premises -- where we are interested in the GLB of the corresponding
  conclusions, ``modulo'' the corresponding premises. <em|Constraint
  Generalization> answer to a disjunction <math|\<vee\><rsub|i>D<rsub|i>> of
  conjunctions of atoms is a solved form formula
  <math|\<exists\><wide|\<alpha\>|\<bar\>>.A> such that for each <math|i>,
  <math|\<cal-M\>\<vDash\>D<rsub|i>\<Rightarrow\>\<exists\><wide|\<alpha\>|\<bar\>>.A>.
  It is used to solve for a predicate variable appearing in multiple
  conclusions -- where we are interested in the LUB of the corresponding
  premises.

  <section|Overview of Solving for Predicate
  Variables><label|PredVarOverview>

  Equipped with these tools, consider first solving an un-normalized
  constraint <math|\<Phi\>> for invariants -- unary predicates
  <math|\<chi\><around*|(|\<cdummy\>|)>>. We want the invariants to be as
  weak as possible, to make the use of the corresponding
  <math|MMG<around*|(|X|)>> definitions (toplevel expressions) as easy as
  possible: the weaker the invariant, the more general the type of the
  definition. We solve for the predicate variables in multiple steps,
  maintaining partial solutions <math|<wide|\<exists\><wide|\<beta\>|\<bar\>><rsup|k><rsub|\<chi\>>.F<rsub|\<chi\>><rsup|k>|\<bar\>>>
  and iterating till the solutions converge (see e.g. Cousot and Cousot
  <cite|Cousot77>). We start with <math|k=0>,
  <math|<wide|\<beta\>|\<bar\>><rsup|0><rsub|\<chi\>>=\<varnothing\>>,
  <math|F<rsup|0><rsub|\<chi\>>=\<b-T\>> for
  <math|\<chi\>\<in\>PV<around*|(|\<Phi\>|)>>. In each step, we solve the
  first order constraint <math|\<cal-Q\><rsup|k>.\<wedge\><rsub|i><around*|(|D<rsub|i><rsup|k>\<Rightarrow\>C<rsub|i><rsup|k>|)>>
  achieved by reducing <math|\<Phi\><around*|[|<wide|\<chi\>|\<bar\>>\<assign\><wide|\<exists\><wide|\<beta\>|\<bar\>><rsup|k><rsub|\<chi\>>.<wide|F<rsup|k><rsub|\<chi\>>|\<bar\>>|\<bar\>>|]>>
  to prenex-normal form and duplicating shared premises. Let
  <math|<wide|\<beta\>|\<bar\>><rsup|k>=<wide|<wide|\<beta\>|\<bar\>><rsup|k><rsub|\<chi\>>|\<bar\>>>.
  We perform joint constraint abduction under prefix <math|\<cal-Q\><rsup|k>>
  (with parameters <math|<wide|\<beta\>|\<bar\>><rsup|k>>), let
  <math|\<exists\><wide|\<alpha\>|\<bar\>><rsup|k>.A<rsup|k>> be one of the
  abduction answers. We divide the atoms of the answer
  <math|\<exists\><wide|\<alpha\>|\<bar\>><rsup|k>.A<rsup|k>> into solutions
  to predicate variables <math|A<rsub|\<chi\>><rsup|k>> and a remainder, or
  residuum, <math|A<rsub|res><rsup|k>=A<rsup|k>\\\<cup\><rsub|\<chi\>>A<rsub|\<chi\>><rsup|k>>,
  depending on the variables in the atoms and so that the residuum holds
  under the quantifiers: <math|\<vDash\>\<cal-Q\><rsup|k>.A<rsub|res><rsup|k>>.
  Let <math|\<exists\><wide|\<beta\>|\<bar\>><rsup|k+1><rsub|\<chi\>>.F<rsup|k+1><rsub|\<chi\>>=\<exists\><wide|\<beta\>|\<bar\>><rsup|k><rsub|\<chi\>><wide|\<alpha\>|\<bar\>><rsup|k>.F<rsup|k><rsub|\<chi\>>\<wedge\>A<rsup|k><rsub|\<chi\>><around*|[|\<beta\><rsub|\<chi\>>\<assign\>\<delta\>|]>>.

  If in <math|k>th iteration, <math|A<rsub|res><rsup|k>=A<rsup|k>>, we are
  done. From <math|\<vDash\>\<cal-Q\><rsup|k>.A<rsup|k>> and
  <math|\<vDash\>A<rsup|k>\<Rightarrow\>\<wedge\><rsub|i><around*|(|D<rsub|i><rsup|k>\<Rightarrow\>C<rsub|i><rsup|k>|)>>,
  it follows that the constraint holds: <math|\<cal-I\>\<vDash\>\<Phi\>> for
  <math|\<cal-I\>=<around*|[|<wide|\<chi\>|\<bar\>>\<assign\><wide|\<exists\><wide|\<beta\>|\<bar\>><rsup|k>.<wide|F<rsup|k><rsub|\<chi\>>|\<bar\>>|\<bar\>>|]>>.

  When <math|A<rsup|k><rsub|\<chi\>>\<neq\>\<b-T\>> for some <math|\<chi\>>,
  we need to perform another iteration. It might be that the constraints
  added by a positive occurrence of <math|\<chi\>> -- a recursive call --
  cannot all fit in next iteration's <math|\<vDash\>\<cal-Q\>.A<rsub|res><rsup|k+1>>
  and have to be a part of next iteration's <math|A<rsub|\<chi\>><rsup|k+1>>.

  For postconditions, we want the strongest possible solutions, because a
  stronger postcondition provides more information at use sites of a
  definition. Therefore, in each iteration, we use constraint generalization
  to solve for binary predicate variables
  <math|\<chi\><rsub|K><around*|(|\<cdummy\>,\<cdummy\>|)>> without
  ``hurting'' the constraint. The generalization results
  <math|\<exists\><wide|\<alpha\>|\<bar\>><rsub|\<chi\><rsub|K>><rsup|k>.G<rsub|\<chi\><rsub|K>><rsup|k>>
  are used to get the first order constraints for abduction
  <math|<around*|[|<wide|\<chi\>|\<bar\>>\<assign\><wide|\<exists\><wide|\<beta\>|\<bar\>><rsup|k><rsub|\<chi\>>.F<rsup|k><rsub|\<chi\>>|\<bar\>>;<wide|\<chi\><rsub|K>|\<bar\>>\<assign\><no-break><wide|\<exists\><wide|\<alpha\>|\<bar\>><rsub|\<chi\><rsub|K>><rsup|k>.G<rsub|\<chi\><rsub|K>><rsup|k>|\<bar\>>|]>>.
  However, we have more work when due to recursive calls of functions
  returning values of existential types, <math|A<rsub|\<chi\><rsub|K>><rsup|k>\<neq\>\<b-T\>>.
  Note that postconditions of each iteration are constructed from scratch,
  they do not accumulate. The way we utilize answers
  <math|A<rsub|\<chi\><rsub|K>><rsup|k>> is by performing second-stage
  abduction. Let <math|\<vee\><rsub|i>D<rsub|i><rsup|k,\<chi\><rsub|K>>> be
  the constraint generalization problem resulting in the postcondition
  <math|G<rsub|\<chi\><rsub|K>><rsup|k>>. We form the joint constraint
  abduction problem <math|><math|\<cal-Q\><rsup|k>.\<wedge\><rsub|i><around*|(|D<rsub|i><rsup|k,\<chi\><rsub|K>>\<Rightarrow\>A<rsub|\<chi\><rsub|K>><rsup|k>|)>>,
  and split its answer <math|A<rsup|k,\<chi\><rsub|K>>> in the same way as
  for the first-stage abduction described above. We include the result in the
  partial solutions: <math|\<exists\><wide|\<beta\>|\<bar\>><rsup|k+1><rsub|\<chi\>>.F<rsup|k+1><rsub|\<chi\>>=\<exists\><wide|\<beta\>|\<bar\>><rsup|k><rsub|\<chi\>><wide|\<alpha\>|\<bar\>><rsup|k>.F<rsup|k><rsub|\<chi\>>\<wedge\><around*|(|A<rsup|k><rsub|\<chi\>>\<wedge\><rsub|K>A<rsub|\<chi\>><rsup|k,\<chi\><rsub|K>>|)><around*|[|\<beta\><rsub|\<chi\>>\<assign\>\<delta\>|]>>.
  This way, <math|D<rsub|i><rsup|k+1,\<chi\><rsub|K>>> may be strong enough
  to imply <math|A<rsub|\<chi\><rsub|K>><rsup|k>>, and hopefully
  <math|A<rsub|\<chi\><rsub|K>><rsup|k+1>=\<b-T\>>.

  But we are still in trouble. Without the postcondition already in place,
  branches with recursive calls have too little information to imply what the
  postcondition should be. Therefore, during initial iterations (<math|k=0>
  and <math|k=1>), we only include non-recursive branches in the constraint
  generalization process. This leads to ``overshooting'': the initial
  postconditions may reflect properties specific to base cases. These
  properties get relaxed during successive iterations, and we only end with
  success after reaching a fix-point.

  The termination condition of the iteration might not be met. Actually,
  <name|InvarGenT> reports type inference failure if the solutions
  <math|F<rsub|\<chi\>><rsup|k>> not converge after a fixed number of
  iterations. We have only observed diverging solutions due to numerical
  constraints.

  <section|Constraint Abduction><label|SecAbduction><label|AbdAlg>

  Abduction is a reasoning technique concerned with the search for
  explanations. An abduction problem is usually given by a background theory
  <math|\<Theta\>> and a formula <math|C>, and the answer is a formula
  <math|A> such that <math|\<Theta\>\<cup\><around|{|A|}>\<vDash\>C>
  (relevance), <math|\<Theta\>\<nvDash\>\<neg\>A> (consistency), and <math|A>
  has some restricted syntactical form, see Marta Mayer and Fiora Pirri
  <cite|AbductionSequents>. We are however interested in <em|constraint
  abduction> problems, with constraints expressed over a fixed model
  <math|\<cal-M\>>. A constraint abduction problem is then given by a pair of
  formulas <math|D,C>, and <math|A> is its answer when (at least)
  <math|\<cal-M\>\<vDash\><around|(|D\<wedge\>A|)>\<Rightarrow\>C>
  (relevance) and <math|\<cal-M\>\<vDash\>\<exists\>FV<around|(|D,A|)>.D\<wedge\>A>
  (consistency), see Michael Maher<newblock> <em|Herbrand constraint
  abduction> <cite|AbductionMaher>. We extend the formulation of joint
  constraint abduction (see <cite|AbductionMaher>) to constraints with
  quantifiers. In general abduction, where a model is built as a solution,
  the quantifiers could be eliminated by Herbrandization. However,
  Herbrandization (and Skolemization) are operations on the level of a logic,
  not within a model -- they do not return equivalent formulas and do not
  work in a fixed model. The introduced functions are uninterpreted. We opt
  to keep the model <math|\<cal-M\>> and handle quantification explicitly. We
  develop a combination procedure for abduction algorithms when their domains
  of constraints are combined in a very simple way (yet sufficing for
  type-inference-driven invariant generation).

  <subsection|Formulating the Joint Constraint Abduction Problem>

  In joint, also called simultaneous, problems, we expect a single answer to
  solve several problems, here: to solve a conjunction of implications.

  A <em|solved form> is a syntactically specified class of formulas,
  associated with a class of problems, for which satisfiability is trivial to
  check. We restrict solved forms to existentially quantified conjunctions of
  atoms, <math|\<exists\><wide|\<alpha\>|\<bar\>>.A>. The variables
  <with|mode|math|<wide|\<alpha\>|\<bar\>>> of a solved form
  <math|\<exists\><wide|\<alpha\>|\<bar\>>.A> that is an abduction problem
  answer, are ``free parameters'' of the answer, they are required to be
  ``unconstrained''.

  Due to the iterative nature of the main algorithm, we need to account for
  prior parameters <math|<wide|\<beta\>|\<bar\>>> similar to the new
  parameters <with|mode|math|<wide|\<alpha\>|\<bar\>>>.

  The constraints that we need to solve form a <em|Joint Constraint Abduction
  under a Quantifier Prefix problem> (<em|JCAQP> problem for short) of the
  form <math|\<cal-Q\>.\<wedge\><rsub|i><around*|(|D<rsub|i>\<Rightarrow\>C<rsub|i>|)>>,
  where <math|D<rsub|i>> and <math|C<rsub|i>> are conjunctions of atomic
  formulas, and <math|\<cal-Q\>> is an arbitrary quantifier prefix. We assume
  that <math|FV(\<wedge\><rsub|i><around*|(|D<rsub|i>\<Rightarrow\>C<rsub|i>|)>)\<subseteq\>\<cal-Q\>>.
  We also have a set <math|<wide|\<beta\>|\<bar\>>> of <em|parameters> of the
  invariants. The conditions on abduction answers
  <math|\<exists\><wide|\<alpha\>|\<bar\>>.A> are as follows:

  <\enumerate>
    <item><em|relevance condition>: <math|\<cal-M\>\<vDash\>\<wedge\><rsub|i><around|(|D<rsub|i>\<wedge\>A\<Rightarrow\>C<rsub|i>|)>>,

    <item><em|validity condition>: <math|\<cal-M\>\<vDash\>\<cal-Q\>.A<around*|[|<wide|\<alpha\>|\<bar\>><wide|\<beta\>|\<bar\>>\<assign\><wide|t|\<bar\>>|]>>
    for some <math|<wide|t|\<bar\>>>,

    <item><em|consistency condition>: <math|\<cal-M\>\<vDash\>\<wedge\><rsub|i>\<exists\>FV<around|(|D<rsub|i>\<wedge\>A|)>.D<rsub|i>\<wedge\>A>,

    <item><em|no escaping variables> condition: for all atoms <math|c\<in\>A>
    such that <math|\<cal-M\>\<nvDash\>\<cal-Q\>.c> and
    <math|FV<around*|(|c|)>\<cap\><wide|\<beta\>|\<bar\>>\<neq\>\<varnothing\>>,
    and for all <math|\<beta\><rsub|1>\<in\>FV<around*|(|c|)>> such that
    <math|<around*|(|\<forall\>\<beta\><rsub|1>|)>\<in\>\<cal-Q\>>, there
    exists <math|\<beta\><rsub|2>\<in\>FV<around*|(|c|)>\<cap\><wide|\<beta\>|\<bar\>>>
    such that <math|\<beta\><rsub|1>\<leqslant\><rsub|\<cal-Q\>>\<beta\><rsub|2>>.

    <\enumerate>
      <item><em|Strong no escaping variables condition> is a stronger variant
      we use for sorts whose solved forms are substitutions. For all atoms
      <math|\<beta\><rsub|2><wide|=|\<dot\>>t\<in\>A> such that
      <math|\<beta\><rsub|2>\<in\><wide|\<beta\>|\<bar\>>>, if
      <math|\<beta\><rsub|1>\<in\>FV<around*|(|c|)>> such that
      <math|<around*|(|\<forall\>\<beta\><rsub|1>|)>\<in\>\<cal-Q\>>, then
      <math|\<beta\><rsub|1>\<leqslant\><rsub|\<cal-Q\>>\<beta\><rsub|2>>.
    </enumerate>
  </enumerate>

  <\definition>
    <label|AbdAnsDef><math|\<exists\><wide|\<alpha\>|\<bar\>>.A> is an answer
    to a JCAQP problem <with|mode|math|\<cal-Q\>.\<wedge\><rsub|i><around*|(|D<rsub|i>\<Rightarrow\>C<rsub|i>|)>>
    with parameters <math|<wide|\<beta\>|\<bar\>>> for model
    <math|\<cal-M\>>, written <math|\<exists\><wide|\<alpha\>|\<bar\>>.A\<in\>Abd<around*|(|\<cal-Q\>,<wide|\<beta\>|\<bar\>>,<wide|D<rsub|i>,C<rsub|i>|\<bar\>>|)>>,
    when <math|A> is a conjunction of atoms,
    <math|<wide|\<alpha\>|\<bar\>>#FV<around*|(|\<wedge\><rsub|i><around*|(|D<rsub|i>\<Rightarrow\>C<rsub|i>|)>,<wide|\<beta\>|\<bar\>>|)>>,
    meeting the relevance condition, validity condition, consistency
    condition and <em|no escaping variables> condition.

    We can also consider Joint Abduction under a Quantifier Prefix problems
    for a logic, checking relevance condition:
    <math|\<vDash\>\<wedge\><rsub|i><around|(|D<rsub|i>\<wedge\>A\<Rightarrow\>C<rsub|i>|)>>
    and validity condition: <math|\<vDash\>\<cal-Q\>.A<around*|[|<wide|\<alpha\>|\<bar\>><wide|\<beta\>|\<bar\>>\<assign\><wide|t|\<bar\>>|]>>.
    The consistency conditions: for all <math|i>,
    <math|D<rsub|i>\<nvDash\>\<neg\>A>, are always met.
  </definition>

  The natural setting for constraint abduction problems is with a fixed
  model. Above we extend the definition to the case where instead of a model
  just a logic is given, just to shed light on relations between constraint
  abduction, general abduction, and decision (i.e. validity or
  satisfiability) problems.

  We call a JCAQP problem <with|mode|math|\<cal-Q\>.D\<Rightarrow\>C> (i.e. a
  non-simultaneous problem) a <em|simple constraint abduction under a
  quantifier prefix> problem SCAQP. We write JCAQP<math|<rsub|\<cal-M\>>> to
  indicate the model.

  <\proposition>
    If the JCAQP<rsub|<math|\<cal-M\>>> problem
    <math|\<cal-Q\>.\<wedge\><rsub|i><around*|(|D<rsub|i>\<Rightarrow\>C<rsub|i>|)>>
    without parameters has an answer, then
    <math|\<cal-M\>\<vDash\>\<cal-Q\>.\<wedge\><rsub|i><around*|(|D<rsub|i>\<Rightarrow\>C<rsub|i>|)>>.
  </proposition>

  We say that JCAQP<rsub|<math|\<cal-M\>>> answer
  <math|\<exists\><wide|\<alpha\>|\<bar\>>.A> is <em|more general> than
  <math|\<exists\><wide|\<beta\>|\<bar\>>.B>, when there exist terms
  <math|<wide|t|\<bar\>>> such that <math|\<cal-M\>\<vDash\>B\<Rightarrow\>A<around|[|<wide|\<alpha\>|\<bar\>>\<assign\><wide|t|\<bar\>>|]>>.

  <\example>
    For a free term algebra <math|T<around|(|F|)>> over signature <math|F>
    containing binary functors <math|f,g> and constants <math|a,b>, and
    JCAQP<rsub|<math|T<around|(|F|)>>> problem
    <math|<rsub|>\<exists\>x,y,z.<around|(|y<wide|=|\<dot\>>f<around|(|a,x|)>\<Rightarrow\>z<wide|=|\<dot\>>a|)>\<wedge\><around|(|y<wide|=|\<dot\>>f<around|(|b,x|)>\<Rightarrow\>z<wide|=|\<dot\>>b|)>>,
    the most general answer is <with|mode|math|\<exists\>\<alpha\>.y<wide|=|\<dot\>>f<around|(|z,\<alpha\>|)>>.
    Indeed, <math|\<forall\>\<alpha\>\<exists\>x,y,z.y<wide|=|\<dot\>>f<around|(|z,\<alpha\>|)>\<wedge\>y<wide|=|\<dot\>>f<around|(|a,x|)>>
    holds with <math|x=\<alpha\>,y=f<around|(|a,\<alpha\>|)>,z=a> and
    <math|\<forall\>\<alpha\>\<exists\>x,y,z.y<wide|=|\<dot\>>f<around|(|z,\<alpha\>|)>\<wedge\>y<wide|=|\<dot\>>f<around|(|b,x|)>>
    holds with <math|x=\<alpha\>,y=f<around|(|b,\<alpha\>|)>,z=b>. For the
    SCAQP<rsub|<math|T<around|(|F|)>>> problem
    <math|<rsub|>\<exists\>x,y,z.<around|(|y<wide|=|\<dot\>>f<around|(|a,x|)>\<Rightarrow\>z<wide|=|\<dot\>>a|)>>,
    the set of maximally general answers is
    <with|mode|math|<around|{|\<exists\>\<alpha\>.y<wide|=|\<dot\>>f<around|(|z,\<alpha\>|)>,z<wide|=|\<dot\>>a|}>>.
  </example>

  Consider a conjunction of atoms <math|C> interpreted in any free term
  algebra <math|T<around*|(|F|)>> over a signature <math|F>. If <math|C> is
  satisfiable, let <math|\<b-U\><around|(|C|)>> be a conjunction of equations
  whose left-hand-sides are variables not occurring in any of the
  right-hand-sides, such that <math|T<around*|(|F|)>\<vDash\>C\<Leftrightarrow\>\<b-U\><around|(|C|)>>,
  otherwise let <math|\<b-U\><around|(|C|)>=\<bot\>>. Let
  <math|\<b-U\><around|(|\<cal-Q\>.C|)>> in case
  <math|T<around*|(|F|)><neg|\<vDash\>>\<cal-Q\>.C> be <math|\<bot\>>, and
  otherwise be as before but with equations directed so that variables later
  in the prefix are on the left. <math|\<b-U\><around|(|\<cal-Q\>.C|)>> can
  be computed by unification with linear constant restrictions, see Baader
  and Schulz <cite|UnificationBaader>. In effect: if for some
  <math|x<wide|=|\<dot\>>t\<in\>\<b-U\><around*|(|C|)>> such that
  <math|<around*|(|\<exists\>t|)>\<nin\>\<cal-Q\>> (e.g. <math|t> is not a
  variable) and <math|<around*|(|\<forall\>x|)>\<in\>\<cal-Q\>>, then
  <math|\<b-U\><around|(|\<cal-Q\>.C|)>=\<bot\>>; if for some
  <math|x<wide|=|\<dot\>>t\<in\>\<b-U\><around*|(|C|)>> such that
  <math|<around*|(|\<exists\>x|)>\<in\>\<cal-Q\>>, there is a
  <math|y\<in\>FV<around*|(|t|)>>, <math|<around*|(|\<forall\>y|)>\<in\>\<cal-Q\>>
  and <math|x\<leqslant\><rsub|\<cal-Q\>>y>, then
  <math|\<b-U\><around|(|\<cal-Q\>.C|)>=\<bot\>>; otherwise
  <math|\<b-U\><around|(|\<cal-Q\>.C|)>=\<b-U\><around*|(|C|)>>. Let
  <math|\<b-U\><rsub|<wide|\<alpha\>|\<bar\>>><around|(|\<cal-Q\>.C|)>> be
  <math|\<b-U\><rsub|<wide|\<alpha\>|\<bar\>>><around|(|<around*|(|\<cal-Q\>\\<around*|{|\<forall\><wide|\<alpha\>|\<bar\>>|}>|)>\<exists\><wide|\<alpha\>|\<bar\>>.C|)>>,
  i.e. <math|\<b-U\><rsub|<wide|\<alpha\>|\<bar\>>><around|(|\<cal-Q\>.C|)>=\<b-U\><around|(|\<cal-Q\><rprime|'>.C|)>>
  where variables <math|<wide|\<alpha\>|\<bar\>>> are existentially
  quantified in <math|\<cal-Q\><rprime|'>> and otherwise
  <math|\<cal-Q\><rprime|'>> is like <math|\<cal-Q\>>. Computing
  <math|\<b-U\><rsub|<wide|\<alpha\>|\<bar\>><wide|\<beta\>|\<bar\>>><around*|(|\<cal-Q\>.A|)>>
  decides the validity condition for <math|\<cal-M\>=T<around*|(|F|)>>.

  <\definition>
    <label|CorComplAbd>An abduction algorithm for
    JCAQP<rsub|<math|\<cal-M\>>> with parameters
    <math|<wide|\<beta\>|\<bar\>>>, <math|Abd<around*|(|\<cal-Q\>,<wide|\<beta\>|\<bar\>>,<wide|D<rsub|i>,C<rsub|i>|\<bar\>>|)>>,
    generates a sequence of quantified conjunctions of atoms
    <math|<wide|\<exists\><wide|\<alpha\>|\<bar\>><rsub|j>.A<rsub|j>|\<bar\>>>,
    possibly infinite. The algorithm is <em|correct> if for every <math|j>,
    <math|\<exists\><wide|\<alpha\>|\<bar\>><rsub|j>.A<rsub|j>> is an answer
    to the JCAQP<rsub|<math|\<cal-M\>>> problem
    <math|\<cal-Q\>.\<wedge\><rsub|i><around*|(|D<rsub|i>\<Rightarrow\>C<rsub|i>|)>>
    with parameters <math|<wide|\<beta\>|\<bar\>>>. It is <em|complete> if
    for every JCAQP<rsub|<math|\<cal-M\>>> answer
    <math|\<exists\><wide|\<alpha\>|\<bar\>>.A>, there is a <math|j> and some
    <math|<wide|t|\<bar\>>> such that <math|\<cal-M\>\<vDash\>A\<Rightarrow\>A<rsub|j><around|[|<wide|\<alpha\>|\<bar\>><rsub|j>\<assign\><wide|t|\<bar\>>|]>>
    (with variables renamed so that <math|<wide|\<alpha\>|\<bar\>>#FV<around|(|A<rsub|j>|)>>).
    If the sequence is empty, we write <math|Abd<around*|(|\<cal-Q\>,<wide|\<beta\>|\<bar\>>,<wide|D<rsub|i>,C<rsub|i>|\<bar\>>|)>=\<bot\>>.
  </definition>

  Note that we do not require that only maximally general answers are
  returned. Although this would be preferrable, it is costly to guarantee in
  many constraint domains even with incomplete algorithms.

  <subsection|Abduction Algorithm for The Combination of
  Domains><label|JCAAlienMain>

  We provide a plug-in architecture where to add a new sort to the logic it
  is enough to give an algorithm solving the JCAQP problem. Define an
  <em|alien subterm> (cf. <cite|UnificationBaader>) of a term <math|\<tau\>>
  of sort <math|s<rsub|type>> to be a maximally large subterm <math|t> of
  <math|\<tau\>> of sort <math|s\<neq\>s<rsub|type>>: a subterm <math|t> that
  is not a subterm of a subterm of sort <math|s<rprime|'>\<neq\>s<rsub|type>>.
  Let <math|usorts=sorts\\<around*|{|s<rsub|type>|}>>.

  Let <math|\<cal-L\><rsub|ty>=T<around|(|F,\<cup\><rsub|s\<in\>sorts>X<rsub|s>|)>>
  be a language interpreted in a multi-sorted free term algebra
  <math|T=T<around|(|F\<cup\><rsub|s\<in\>usorts>D<rsub|s>|)>> which, besides
  the term variables <math|X<rsub|s<rsub|type>>>, has <em|alien subterm
  variables> <math|\<cup\><rsub|s\<in\>usorts>X<rsub|s>>.

  Let <math|\<cal-Q\>> be a quantifier prefix and <math|D<rsub|i>,C<rsub|i>>
  be atomic conjunctions in <math|\<cal-L\>> that form a joint abduction
  problem <math|\<cal-Q\>.\<wedge\><rsub|i><around*|(|D<rsub|i>\<Rightarrow\>C<rsub|i>|)>>.
  For the purpose of Theorem <reference|MultisortAbdThm>, let
  <math|Abd<rsub|s>> be complete JCAQP algorithms for <math|s\<in\>usorts>
  and <math|Abd<rsub|T>> be a complete JCAQP algorithm for the free term
  algebra <math|T>. We start the multi-sorted abduction procedure
  <math|Abd<around*|(|\<cal-Q\>,<wide|\<beta\>|\<bar\>>,<wide|D<rsub|i>,C<rsub|i>|\<bar\>>|)>>
  by performing <math|Abd<rsub|T>> on the <math|s<rsub|type>> part of
  constraints with alien subterms replaced by variables. For each JCAQP
  solution <with|mode|math|\<exists\><wide|\<alpha\>|\<bar\>><rsub|j>.A<rsub|j>>,
  we replace the <math|s<rsub|type>> part of the <math|i>th premise by the
  ``residual'' formula <with|mode|math|A<rsub|p><rsup|i><rsub|j>> and of
  <math|i>th conclusion by ``residual'' formula
  <math|A<rsub|c><rsup|i><rsub|j>>, defined in Table
  <reference|MultisortAbd>. We split the resulting JCAQP problem into
  single-sort problems for each sort <math|s\<in\>usorts>, and we solve them
  using <math|Abd<rsub|s>> algorithms. Finally, we build answers as
  conjunctions of answers for each sort.

  Let <math|\<cal-Q\>> be a quantifier prefix and <math|D<rsub|i>,C<rsub|i>>
  be atomic conjunctions in <math|\<cal-L\>> that form a joint abduction
  problem <math|\<cal-Q\>.\<wedge\><rsub|i><around*|(|D<rsub|i>\<Rightarrow\>C<rsub|i>|)>>
  with parameters <math|<wide|\<beta\>|\<bar\>>>, and
  <math|<wide|\<forall\>\<beta\>|\<bar\>>\<subset\>\<cal-Q\>>. Let
  <math|Abd<rsub|s>> be correct and complete JCAQP algorithms for
  <math|s\<in\>usorts> and <math|Abd<rsub|T>> be a correct and complete JCAQP
  algorithm for language <math|\<cal-L\><rsub|ty>=T<around|(|F,\<cup\><rsub|s\<in\>sorts>X<rsub|s>|)>>
  and model <math|T<around|(|F\<cup\><rsub|s\<in\>usorts>D<rsub|s>|)>>. We
  define the algorithm <math|Abd<around*|(|\<cal-Q\>,<wide|\<beta\>|\<bar\>>,<wide|D<rsub|i>,C<rsub|i>|\<bar\>>|)>>
  in Table <reference|MultisortAbd>.<\float|float|t>
    <\big-table>
      <tabular|<tformat|<table|<row|<cell|<strong|let>
      <math|D<rsub|i>\<equiv\>\<wedge\><rsub|s>D<rsub|i><rsup|s>> and
      <math|C<rsub|i>\<equiv\>\<wedge\><rsub|s>C<rsub|i><rsup|s>>, where, for
      <math|s\<in\>sorts>, <math|D<rsub|i><rsup|s>,C<rsub|i><rsup|s>> are
      atomic conjunctions in <math|\<cal-L\><rsub|s>>.>>|<row|<cell|<strong|let>
      <math|D<rsub|i><rsup|t>,C<rsub|i><rsup|t>> be formulas
      <math|D<rsub|i><rsup|s<rsub|type>>,C<rsub|i><rsup|s<rsub|type>>> with
      subterms <math|<wide|r|\<bar\>><rsub|i>> replaced with fresh variables
      <math|<wide|\<alpha\><rsub|r<rsub|i>>|\<bar\>>>>>|<row|<cell|
      \ <tabular|<tformat|<table|<row|<cell|(such that
      <math|\<alpha\><rsub|r>\<in\>X<rsub|s>> for <math|r> of sort
      <math|s>)>>|<row|<cell|where <math|<wide|r|\<bar\>><rsub|i>> are all
      alien subterms in <math|D<rsub|i><rsup|s<rsub|type>>,C<rsub|i><rsup|s<rsub|type>>>>>>>>>>|<row|<cell|<strong|let>
      <math|<wide|<wide|r|\<bar\>>|\<bar\>>=<wide|r<rsub|1>|\<bar\>>\<ldots\><wide|r<rsub|n>|\<bar\>>>,
      <math|<wide|<wide|\<alpha\><rsub|r>|\<bar\>>|\<bar\>>=<wide|\<alpha\><rsub|r<rsub|1>>|\<bar\>>\<ldots\><wide|\<alpha\><rsub|r<rsub|n>>|\<bar\>>>>>|<row|<cell|<strong|if>
      <math|D<rsub|i><rsup|t>> is not satisfiable for some <math|i>,
      <strong|then> <math|Abd<around*|(|\<cal-Q\>,<wide|\<beta\>|\<bar\>>,<wide|D<rsub|i>,C<rsub|i>|\<bar\>>|)>\<assign\>Abd<around*|(|\<cal-Q\>,<wide|\<beta\>|\<bar\>>,<wide|D<rsub|j>,C<rsub|j>|\<bar\>><rsub|j\<neq\>i>|)>>>>|<row|<cell|<strong|else
      if> <math|C<rsub|i><rsup|t>> is not satisfiable for some <math|i>,
      <strong|then return> <math|Abd<around*|(|\<cal-Q\>,<wide|\<beta\>|\<bar\>>,<wide|D<rsub|i>,C<rsub|i>|\<bar\>>|)>\<assign\>\<bot\>>>>|<row|<cell|<strong|else
      let> <math|\<wedge\><rsub|s>D<rsup|t><rsub|i,s>=\<b-U\><around|(|D<rsup|t><rsub|i>|)>>,
      <math|\<wedge\><rsub|s>C<rsup|t><rsub|i,s>=\<b-U\><around|(|C<rsup|t><rsub|i>|)>>
      be solved forms of <math|D<rsup|t><rsub|i>>,
      <math|C<rsup|t><rsub|i>>>>|<row|<cell|Similarly, discard branches
      <math|i> for which <math|D<rsup|t><rsub|i,s>\<wedge\>D<rsub|i><rsup|s>>
      is not satisfiable for some <math|s\<in\>usorts>.>>|<row|<cell|<strong|if>
      <math|Abd<rsub|T><around|(|\<cal-Q\>,<wide|<wide|\<alpha\><rsub|r>|\<bar\>>|\<bar\>><wide|\<beta\>|\<bar\>>,<wide|D<rsub|i,s<rsub|type>><rsup|t>,C<rsub|i,s<rsub|type>><rsup|t>|\<bar\>>|)>=\<bot\>>,
      <strong|then> <math|Abd<around*|(|\<cal-Q\>,<wide|\<beta\>|\<bar\>>,<wide|D<rsub|i>,C<rsub|i>|\<bar\>>|)>\<assign\>\<bot\>>>>|<row|<cell|<strong|else
      let> <math|<wide|\<exists\><wide|\<alpha\><rsub|j><rsup|T>|\<bar\>>.A<rsub|T><rsup|j>|\<bar\>>=Abd<rsub|T><around|(|\<cal-Q\>,<wide|<wide|\<alpha\><rsub|r>|\<bar\>>|\<bar\>><wide|\<beta\>|\<bar\>>,<wide|D<rsub|i,s<rsub|type>><rsup|t>,C<rsub|i,s<rsub|type>><rsup|t>|\<bar\>>|)>>>>|<row|<cell|<strong|let>
      <math|A<rsub|T><rsup|j><rprime|'>> be <math|A<rsub|T><rsup|j>> with
      alien subterms replaced by distinct fresh variables
      <math|<wide|\<alpha\>|\<bar\>><rsub|r><rsup|j>>,
      <math|<wide|\<alpha\><rsub|j><rsup|T>|\<bar\>><rprime|'>=<wide|\<alpha\><rsub|j><rsup|T>|\<bar\>><wide|\<alpha\>|\<bar\>><rsub|r><rsup|j>>>>|<row|<cell|<strong|let>
      <math|A<rsup|i><rsub|p><rsub|j>=<around*|{|x<wide|=|\<dot\>>t\<in\>\<b-U\><around*|(|D<rsub|i,s<rsub|type>><rsup|t>\<wedge\>A<rsub|T><rsup|j><rprime|'>|)>\|x\<in\>X<rsub|s>,s\<neq\>s<rsub|type>|}>>>>|<row|<cell|<strong|let>
      <math|A<rsup|i><rsub|c><rsub|j>=<around*|{|x<wide|=|\<dot\>>t\<in\>\<b-U\><around*|(|D<rsub|i,s<rsub|type>><rsup|t>\<wedge\>C<rsub|i,s<rsub|type>><rsup|t>\<wedge\>A<rsub|T><rsup|j><rprime|'>|)>\|x\<in\>X<rsub|s>,s\<neq\>s<rsub|type>|}>>>>|<row|<cell|<strong|let>
      <math|A<rsup|i><rsub|p/c,j>=\<wedge\><rsub|s>A<rsub|p/c,j,s><rsup|i>>,
      <math|A<rsub|p/c,j,s><rsup|i>\<in\>\<cal-L\><rsub|s>>>>|<row|<cell|<strong|let>
      <math|J<rsub|s>=<around*|{|j<mid|\|>Abd<rsub|s><around|(|\<cal-Q\>,<wide|\<alpha\>|\<bar\>><rsub|r><rsup|j><wide|\<beta\>|\<bar\>>,<wide|D<rsub|i><rsup|s>\<wedge\><around*|(|D<rsup|t><rsub|i,s>\<wedge\>A<rsup|i><rsub|p,j,s>|)><around|[|<wide|<wide|\<alpha\><rsub|r>|\<bar\>>|\<bar\>>\<assign\><wide|<wide|r|\<bar\>>|\<bar\>>|]>,C<rsub|i><rsup|s>\<wedge\><around*|(|C<rsub|i,s><rsup|t>\<wedge\>A<rsup|i><rsub|c,j,s>|)><around|[|<wide|<wide|\<alpha\><rsub|r>|\<bar\>>|\<bar\>>\<assign\><wide|<wide|r|\<bar\>>|\<bar\>>|]>|\<bar\>>|)>\<neq\>\<bot\>|}>>>>|<row|<cell|<strong|let>
      <math|<wide|\<exists\><wide|\<alpha\><rsub|s><rsup|k<rsub|j><rsup|s>>|\<bar\>>.A<rsub|s><rsup|k<rsub|j><rsup|s>>|\<bar\>>=Abd<rsub|s><around|(|\<cal-Q\>,<wide|\<alpha\>|\<bar\>><rsub|r><rsup|j><wide|\<beta\>|\<bar\>>,<wide|D<rsub|i><rsup|s>\<wedge\><around*|(|D<rsup|t><rsub|i,s>\<wedge\>A<rsup|i><rsub|p,j,s>|)><around|[|<wide|<wide|\<alpha\><rsub|r>|\<bar\>>|\<bar\>>\<assign\><wide|<wide|r|\<bar\>>|\<bar\>>|]>,C<rsub|i><rsup|s>\<wedge\><around*|(|C<rsub|i,s><rsup|t>\<wedge\>A<rsup|i><rsub|c,j,s>|)><around|[|<wide|<wide|\<alpha\><rsub|r>|\<bar\>>|\<bar\>>\<assign\><wide|<wide|r|\<bar\>>|\<bar\>>|]>|\<bar\>>|)>>,>>|<row|<cell|
      \ \ \ \ \ \ <math|j\<in\>\<cap\><rsub|s\<in\>usorts>J<rsub|s>>>>|<row|<cell|<strong|if>
      for some <math|s\<in\>usorts>, <math|J<rsub|s>=\<varnothing\>>,
      <strong|then> <math|Abd<around*|(|\<cal-Q\>,<wide|\<beta\>|\<bar\>>,<wide|D<rsub|i>,C<rsub|i>|\<bar\>>|)>\<assign\>\<bot\>>>>|<row|<cell|<strong|return>
      <math|Abd<around*|(|\<cal-Q\>,<wide|\<beta\>|\<bar\>>,<wide|D<rsub|i>,C<rsub|i>|\<bar\>>|)>\<assign\><wide|\<exists\><wide|\<alpha\><rsub|<wide|k<rsub|j><rsup|s>|\<bar\>>>|\<bar\>>.A<rsub|T><rsup|j><rprime|'>\<wedge\><rsub|s>A<rsub|s><rsup|k<rsub|j><rsup|s>>|\<bar\>><rsub|<wide|k<rsub|j><rsup|s>|\<bar\>>:j\<in\>\<cap\><rsub|s>J<rsub|s>>>,>>|<row|<cell|
      \ <tabular|<tformat|<table|<row|<cell|where
      <math|<wide|\<alpha\><rsub|<wide|k<rsub|j><rsup|s>|\<bar\>>>|\<bar\>>>
      are <math|<wide|\<alpha\><rsub|j><rsup|T>|\<bar\>><rprime|'><wide|<wide|\<alpha\><rsub|s><rsup|k<rsub|j><rsup|s>>|\<bar\>>|\<bar\>>\<cap\>FV<around*|(|A<rsub|T><rsup|j><rprime|'>\<wedge\><rsub|s>A<rsub|s><rsup|k<rsub|j><rsup|s>>|)>>,>>|<row|<cell|<math|<wide|<wide|\<alpha\><rsub|s><rsup|k<rsub|j><rsup|s>>|\<bar\>>|\<bar\>>>
      is a concatenation of <math|<wide|\<alpha\><rsub|s><rsup|k<rsub|j><rsup|s>>|\<bar\>>>
      for <math|s\<in\>usorts>,>>|<row|<cell|for
      <math|j\<in\>\<cap\><rsub|s>J<rsub|s>>,
      <math|<wide|k<rsub|j><rsup|s>|\<bar\>>> span the cartesian product
      <math|\<times\><rsub|s\<in\>usorts>Abd<rsub|s>> of solutions for fixed
      <math|j>>>>>>>>>>><label|MultisortAbd>
    </big-table|Complete multi-sorted abduction
    <math|Abd<around*|(|\<cal-Q\>,<wide|\<beta\>|\<bar\>>,<wide|D<rsub|i>,C<rsub|i>|\<bar\>>|)>>>
  </float> In this algorithm, we separate formulas into single-sorted
  formulas, we perform abduction for terms, and we perform abduction for
  other sorts with additional equations due to abduction for terms. The proof
  of the following theorem is in Section <reference|SortCombProof>.

  <\theorem>
    <label|MultisortAbdThm>Assume the conditions listed above. Then
    <math|Abd> meets Definition <reference|CorComplAbd> <em|correct> and
    <em|complete> algorithm conditions.
  </theorem>

  Introducing new variables <math|<wide|\<alpha\>|\<bar\>><rsub|r><rsup|j>>
  puts additional burden on abduction in other sorts. In the current
  implementation of <name|InvarGenT>, we only replace
  <math|A<rsub|T><rsup|j>> with <math|A<rsub|T><rsup|j><rprime|'>> in the
  first iteration, when abduction in other sorts is not performed.

  For the details of the implementation, see Section <reference|JCAAlienAlg>.

  <subsection|Joint Constraint Abduction><label|JCAMain>

  In Table <reference|MultisortAbd>, we assumed abduction algorithms are
  returning sequences of answers, from which the answers of interest are
  extracted. We implement abduction algorithms differently. We maintain a
  <em|discard list> -- a list of answers to avoid, and the algorithms return
  the first answer they find which does not imply any answer in the discard
  list.

  Besides the discard list, the simple abduction algorithms take another
  argument: the partial answer. By starting the search for an answer to an
  implication from the joint solution to already solved implications, we
  ensure by construction that the final answer to the joint constraint
  abduction problem meets validity and consistency conditions. The relevance
  and no escaping variables conditions would be met regardless of starting
  from the partial answer. However, the search is greatly facilitated,
  because simple constraint abduction does not need to rediscover relevant
  parts of the answers to already solved implications.

  Sometimes such rediscovery is not possible. Abduction answer
  <math|\<exists\><wide|\<alpha\>|\<bar\>>.A> to <math|D\<Rightarrow\>C> is
  <em|fully maximal> when <math|\<cal-M\>\<vDash\><around|(|\<exists\><wide|\<alpha\>|\<bar\>>.D\<wedge\>A|)>\<Leftrightarrow\>D\<wedge\>C>.
  The notion was introduced by Michael Maher, see e.g. <cite|AbductionMaher>,
  to curb the difficulty of finding all abduction answers. Even equipped only
  with fully maximal abduction algorithms, by accumulating answers across
  implications we can still solve problems where some implications do not
  have fully maximal answers. To this effect, we vary the order in which
  implications are solved, so that when an implication
  <math|D\<Rightarrow\>C> without fully maximal answers is encountered, the
  answer <math|\<exists\><wide|\<alpha\>|\<bar\>><rsub|p>.A<rsub|p>> to
  previous implications is such that <math|D\<wedge\>A<rsub|p>\<Rightarrow\>C>
  has a fully maximal answer. In fact, our simple constraint abduction
  algorithms go beyond fully maximal answers.

  Rather than testing permutations blindly, we use a search scheme which
  might not capture all opportunities to solve a JCA problem, but detects
  unsolvable JCA problems earlier. We set aside branches that do not have any
  answer extending the partial answer so far. After all branches have been
  tried and the partial answer is not an empty conjunction (i.e. not
  <math|\<b-T\>>), we retry the set-aside branches. If during the retry, any
  of the set-aside branches fails, we add the partial answer to discarded
  answers -- which are avoided during simple abduction -- and restart.
  Restart puts the set-aside branches to be tried first. If, when left with
  set-aside branches only, the partial answer is an empty conjunction, i.e.
  all the answer-contributing branches have been set aside, we fail -- return
  <math|\<bot\>> from the joint abduction.

  Before starting joint constraint abduction, we separate out negative
  constraints, as explained in Section <reference|AbdNegConstrn>. To ensure
  the overall consistency and validity conditions without needless
  backtracking, we pass a validation suite to SCA algorithms. The validation
  ensures that the partial answers are consistent with all implications of
  the constraint. That is, we reject the partial answers <math|A> such that
  <math|\<cal-M\>\<nvDash\>\<wedge\><rsub|i>\<exists\>FV<around|(|D<rsub|i>\<wedge\>C<rsub|i>\<wedge\>A|)>.D<rsub|i>\<wedge\>C<rsub|i>\<wedge\>A>.

  For the details of the algorithm, see Section <reference|JCAAlg>.

  <subsection|Simple Constraint Abduction>

  JCA problems for most interesting domains are unknown to be decidable,
  because the corresponding SCA problems are not known to have effective
  characterizations of the sets of answers. Maher <cite|AbductionMaher>
  introduces subsets of answers which are more amenable to search: abduction
  answer <math|\<exists\><wide|\<alpha\>|\<bar\>>.A> to SCA problem
  <math|D\<Rightarrow\>C> is fully maximal when
  <math|\<cal-M\>\<vDash\><around|(|\<exists\><wide|\<alpha\>|\<bar\>>.D\<wedge\>A|)>\<Leftrightarrow\>D\<wedge\>C>.
  We can search for fully maximal answers using various forms of a
  brute-force approach: starting from an <em|initial candidate>
  <math|D\<wedge\>C> and generalizing until we find a formula, implied by
  <math|D\<wedge\>C>, which meets all conditions for a correct SCA answer and
  all its further generalizations do not imply <math|C>. It turns out that
  fully maximal answers are insufficient. We have come up with two additional
  ways to introduce initial candidates. One is to add -- guess -- atoms
  constraining variables which are already significantly constrained by the
  premise <math|D>. The ``significant constraint'' condition limits the
  number of guesses to try. The other way is to decompose the SCA problem
  <math|D\<Rightarrow\>C> into subproblems <math|d\<Rightarrow\>c> for atoms
  <math|d\<in\>D,c\<in\>C> and add their answers to initial candidates. In
  many domains, all maximally general answers to <math|d\<Rightarrow\>c> can
  be easily enumerated. Even considering all initial candidates described in
  this paragraph does not ensure finding all maximally general answers.

  We preprocess the initial SCA answer candidate <math|C<rsub|a>> by trying
  to eliminate universally quantified variables, using the premise of the SCA
  problem. We define this preprocessing, separately for the different sorts,
  as <math|Rev<rsub|\<forall\>><around*|(|\<cal-Q\>,<wide|\<beta\>|\<bar\>>,D,C<rsub|a>|)>>.
  It makes the valididty condition of the resulting answer,
  <math|\<cal-M\>\<vDash\>\<cal-Q\>.A>, easier to meet. See Dillig, Dillig,
  Li and McMillan <cite|InductLoopInv> for a similar approach.

  <subsubsection|Abduction for Terms><label|SCATermsMain>

  The JAQP problem for first order logic with function symbols and equality
  is undecidable, because it is equivalent, by Herbrandization, to
  simultaneous rigid E-unification (see Degtyarev and Voronkov
  <cite|simulRigidEUnifUndec>): the substitution that is a solution to
  simultaneous rigid E-unification when expressed as a conjunction of
  equations has the same properties as a JCAQP answer (therefore the
  existence of JCAQP answers coincides with intuitionistic satisfiability).
  Remember that outside of Definition <reference|AbdAnsDef>, we use
  <math|\<vDash\>\<Phi\>> as a shorthand for
  <math|\<cal-M\>\<vDash\>\<Phi\>>.

  The decision problem <math|T<around|(|F|)>\<vDash\>\<cal-Q\>.\<wedge\><rsub|i><around*|(|D<rsub|i>\<Rightarrow\>C<rsub|i>|)>>
  is decidable, see Comon <cite|DisunificationComon>. Actually,
  <cite|DisunificationComon> provides a disjunction as a solution, each
  disjunct meeting the relevance and validity conditions of the
  JCAQP<rsub|<math|T<around|(|F|)>>> problem. It is often the case though
  that each disjunct does not meet the consistency condition, despite the
  JCAQP<rsub|<math|T<around|(|F|)>>> problem considered having answers.

  The JCAQP problem for free term algebra <math|T<around*|(|F|)>> is unknown
  to be decidable. A limited form of JCA is to find the fully maximal
  answers, introduced in <cite|AbductionMaher>, using non-simultaneous
  abduction algorithm from Maher and Huang <cite|AbductionSolvMaher>.
  <cite|AbductionMaher> refers to <cite|MaherParamSubstitutions> as
  establishing that there are finitely many fully maximal answers.
  <cite|AbductionSolvMaher> gives an algorithm finding fully maximal answers
  for simple (i.e. non-simultaneous) constraint abduction problems.

  Let us recall why Herbrandization is insufficient and therefore we cannot
  apply the algorithm from <cite|AbductionSolvMaher> without some
  adjustments. Take a formula <math|\<exists\>x.<around*|(|a<wide|=|\<dot\>>b<around*|(|x|)>\<Rightarrow\>x<wide|=|\<dot\>>b<around*|(|x|)>|)>\<wedge\>\<varphi\><around*|(|x|)>>.
  In the original model <math|T<around*|(|F|)>>, the formula is equivalent to
  <math|\<exists\>x.\<varphi\><around*|(|x|)>>, because
  <math|a<wide|=|\<dot\>>b<around*|(|x|)>> is equivalent to falsehood.
  However, it is a Herbrandization of <math|\<exists\>x.<around*|(|\<forall\>b.a<wide|=|\<dot\>>b\<Rightarrow\>x<wide|=|\<dot\>>b|)>\<wedge\>\<varphi\><around*|(|x|)>>,
  which is equivalent to <math|\<varphi\><around*|(|a|)>>.

  Fully maximal answers are not sufficient for the practical application of
  joint constraint abduction. Consider a constructor
  <math|<with|mode|text|<verbatim|Pair>>:\<forall\>\<alpha\>\<beta\>.Term<around|(|\<alpha\>|)>\<times\>Term<around|(|\<beta\>|)>\<longrightarrow\>Term<around|(|<around*|(|\<alpha\>,\<beta\>|)>|)>>
  and a pattern matching branch that we could add to our <verbatim|eval>
  function: <verbatim|\| Pair (y1, y2) -\<gtr\> (eval y1, eval y2)>. It leads
  to an implication:

  <\equation*>
    \<alpha\><wide|=|\<dot\>>Term<around|(|<around*|(|\<alpha\><rprime|'>,\<beta\><rprime|'>|)>|)>\<Rightarrow\>\<beta\><wide|=|\<dot\>><around*|(|\<alpha\><rprime|''>,\<beta\><rprime|''>|)>
  </equation*>

  where <math|\<alpha\><rprime|'>,\<beta\><rprime|'>> are universally
  quantified and <math|\<alpha\><rprime|''>,\<beta\><rprime|''>> are
  existentially quantified. The expected abduction answer
  <math|\<alpha\><wide|=|\<dot\>>Term<around*|(|\<beta\>|)>\<wedge\>\<alpha\><rprime|''><wide|=|\<dot\>>\<alpha\><rprime|'>\<wedge\>\<beta\><rprime|''><wide|=|\<dot\>>\<beta\><rprime|'>>
  is not fully maximal because:

  <\equation*>
    \<alpha\><wide|=|\<dot\>>Term<around|(|<around*|(|\<alpha\><rprime|'>,\<beta\><rprime|'>|)>|)>\<wedge\>\<beta\><wide|=|\<dot\>><around*|(|\<alpha\><rprime|''>,\<beta\><rprime|''>|)>\<nRightarrow\>\<alpha\><rprime|'><wide|=|\<dot\>>\<alpha\><rprime|''>\<wedge\>\<beta\><rprime|'><wide|=|\<dot\>>\<beta\><rprime|''>
  </equation*>

  In the case of <verbatim|eval>, the inference problem is solved by our JCA
  scheme even based on fully maximal abduction. But examples from Chuan-kai
  Lin <cite|PracticalGADTsInfer> (for example the <verbatim|zip2> and
  <verbatim|zip1> functions) motivated a development that goes beyond fully
  maximal answers: guessing equations between variables.

  To show how we eliminate universally quantified variables, we slightly
  abuse notation:

  <\eqnarray*>
    <tformat|<table|<row|<cell|S>|<cell|=>|<cell|<around*|[|<wide|t<rsub|u>|\<bar\>>\<assign\><wide|t<rprime|'><rsub|u>|\<bar\>>|]><with|mode|text|
    for >FV<around*|(|t<rsub|u>|)>\<cap\><wide|\<beta\><rsub|u>|\<bar\>>\<neq\>\<varnothing\>,<wide|\<forall\>\<beta\><rsub|u>|\<bar\>>\<subset\>\<cal-Q\><with|mode|text|
    such that >\<cal-M\>\<vDash\>D\<Rightarrow\><wide|S|\<dot\>>,>>|<row|<cell|S<rprime|'>>|<cell|=>|<cell|<around*|[|<wide|u|\<bar\>>\<assign\><wide|t<rprime|'><rsub|u>|\<bar\>>|]><with|mode|text|
    for ><wide|u|\<bar\>>\<subset\><wide|\<beta\><rsub|u>|\<bar\>>,<wide|\<forall\>\<beta\><rsub|u>|\<bar\>>\<subset\>\<cal-Q\><with|mode|text|
    such that >\<cal-M\>\<vDash\>D\<wedge\>C\<Rightarrow\><wide|S|\<dot\>><rprime|'>,>>|<row|<cell|Rev<rsub|\<forall\>><around*|(|\<cal-Q\>,<wide|\<beta\>|\<bar\>>,D,C|)>>|<cell|=>|<cell|<around*|{|c<rprime|'><mid|\|>c=x<wide|=|\<dot\>>t\<in\>C,<with|mode|text|if
    >x=S<rprime|'><around*|(|t|)><with|mode|text| then
    >c<rprime|'>=S<around*|(|c|)><with|mode|text| else
    >c<rprime|'>=S*S<rprime|'><around*|(|c|)>|}>>>>>
  </eqnarray*>

  <math|S> is a substitution of subterms rather than a regular substitution
  of variables.

  \ To solve <math|D\<Rightarrow\>C> the algorithm from
  <cite|AbductionSolvMaher> page 13, reproduced in Table
  <reference|HerbAbdAlg>, starts with <math|\<b-U\><around*|(|D\<wedge\>C|)>>
  and iteratively replaces subterms by fresh variables
  <math|\<alpha\>\<in\><wide|\<alpha\>|\<bar\>>> for a final solution
  <math|\<exists\><wide|\<alpha\>|\<bar\>>.A>. If the same subterm occurs at
  multiple positions, we try replacing by the same variable at subsets of
  these positions. We start from <math|Rev<rsub|\<forall\>><around*|(|\<cal-Q\>,<wide|\<beta\>|\<bar\>>,\<b-U\><around*|(|D\<wedge\>A<rsub|p>|)>,\<b-U\><around*|(|A<rsub|p>\<wedge\>D\<wedge\>C|)>|)>>,
  where <math|\<exists\><wide|\<alpha\>|\<bar\>><rsub|p>.A<rsub|p>> is the
  solution to previous problems solved by the joint abduction algorithm.
  Optionally, we also substitute-out in the initial candidates, constants
  <math|\<tau\>\<assign\>\<alpha\>> when <math|\<alpha\><wide|=|\<dot\>>\<tau\>\<in\>\<b-U\><around*|(|D\<wedge\>A<rsub|p>|)>>.
  The modification going beyond fully maximal answers, is to consider
  candidate atoms not implied by <math|D\<wedge\>C>, even in the case without
  an initial partial answer: <math|A<rsub|p>=\<b-T\>>. A natural choice is to
  consider equations <math|\<beta\><rsub|1><wide|=|\<dot\>>\<beta\><rsub|2>>
  for parameters <math|\<beta\><rsub|1>\<beta\><rsub|2>\<subseteq\><wide|\<beta\>|\<bar\>>>.
  To curtail the search space, we limit the choices of pairs
  <math|\<beta\><rsub|1>,\<beta\><rsub|2>> to cases
  <math|A<rsub|p>\<wedge\>D\<wedge\>C\<Rightarrow\>\<beta\><rsub|1><wide|=|\<dot\>>\<tau\><rsub|1>\<wedge\>\<beta\><rsub|2><wide|=|\<dot\>>\<tau\><rsub|2>>
  where <math|\<tau\><rsub|1>> and <math|\<tau\><rsub|2>> are not variables
  but are unifiable.

  For the details of the algorithm, see Section <reference|SCATermsAlg>.

  <subsubsection|Abduction for Linear Arithmetic><label|SCANumMain>

  We start with some insights into abduction for linear arithmetic, and then
  discuss our algorithm. Unlike in term abduction, there is no need to
  introduce variables.

  <\proposition>
    The domain of linear arithmetic has the following <em|quantifier
    elimination> property: for every constraint (i.e. conjunction of atoms)
    <math|A> and variables <math|<wide|\<alpha\>|\<bar\>>> there exists a
    constraint <math|A<rprime|'>> such that
    <math|\<cal-M\>\<vDash\><around*|(|\<exists\><wide|\<alpha\>|\<bar\>>.A|)>\<Leftrightarrow\>A<rprime|'>>.
  </proposition>

  With inequalities, it can happen that there are no maximally general
  answers, there can also be infinitely many maximally general answers
  outside of fully maximal answers.

  The <em|implicit equalities> <math|E> of a conjunction <math|C> is a
  conjunction of equations of biggest rank such that
  <math|\<cal-M\>\<vDash\>C\<Rightarrow\>E> and <math|E> are linearly
  independent of equations in <math|C>.

  <\proposition>
    <dueto|<cite|AbductionLinArithMaher> p. 14 Lemma 10>Suppose
    <math|D\<wedge\>C> has implicit equalities <math|E>. Then
    <math|\<vDash\>A\<wedge\><no-break>D\<Rightarrow\>C> iff
    <math|\<vDash\>A\<wedge\>D\<Rightarrow\>E> and
    <math|\<vDash\><wide|E|~><around*|(|A\<wedge\>D|)>\<Rightarrow\><wide|E|~><around*|(|C|)>>.
  </proposition>

  Consider the SCA problem <math|x<wide|=|\<dot\>>2r\<wedge\>y<wide|=|\<dot\>>2s\<Rightarrow\>z<wide|=|\<dot\>>2t>
  and a maximally general answer <math|A=x+<no-break>y<wide|=|\<dot\>>z\<wedge\>r+s<wide|=|\<dot\>>t>.
  It is not fully maximal, because <math|C\<wedge\>D> does not imply any
  relation between <math|x,y> and <math|z>.

  To simplify the search in presence of a quantifier prefix, we preprocess
  the initial candidates by trying to eliminate universally quantified
  variables:

  <\eqnarray*>
    <tformat|<table|<row|<cell|S>|<cell|=>|<cell|<around*|[|<wide|\<beta\><rsub|u>|\<bar\>>\<assign\><wide|t<rsub|u>|\<bar\>>|]><with|mode|text|
    for ><wide|\<forall\>\<beta\><rsub|u>|\<bar\>>\<subset\>\<cal-Q\><with|mode|text|
    such that >\<cal-M\>\<vDash\>D\<Rightarrow\><wide|S|\<dot\>>,>>|<row|<cell|Rev<rsub|\<forall\>><around*|(|\<cal-Q\>,<wide|\<beta\>|\<bar\>>,D,C|)>>|<cell|=>|<cell|<around*|{|c<rprime|'><mid|\|>c\<in\>C,<with|mode|text|if
    >\<cal-M\>\<vDash\>\<cal-Q\>.c<around*|[|<wide|\<beta\>|\<bar\>>\<assign\><wide|t|\<bar\>>|]><with|mode|text|
    for some ><wide|t|\<bar\>><with|mode|text| then
    >c<rprime|'>=c<with|mode|text| else >c<rprime|'>=S<around*|(|c|)>|}>>>>>
  </eqnarray*>

  We approach solving for equations <math|c=t<rsub|1><wide|=|\<dot\>>t<rsub|2>\<in\>C>
  and inequalities <math|c=t<rsub|1>\<leqslant\>t<rsub|2>\<in\>C>
  differently. For equations, we construct initial candidates as linear
  combinations of <math|c> and selected equations from <math|D>. For
  inequalities, we construct the initial candidates by finding the abudction
  answers to <math|d\<Rightarrow\>c> for each inequality <math|d\<in\>D>.

  To find the abduction answers to <math|d\<Rightarrow\>c>, pick a common
  variable <math|\<alpha\>\<in\>FV<around*|(|d|)>\<cap\>FV<around*|(|c|)>> or
  the constant <math|\<alpha\>=1>. We have four possibilities:

  <\enumerate>
    <item><math|d\<Leftrightarrow\>\<alpha\>\<leqslant\>d<rsub|\<alpha\>>>
    and <math|c\<Leftrightarrow\>\<alpha\>\<leqslant\>c<rsub|\<alpha\>>>: the
    abduction answers are <math|c> and <math|d<rsub|\<alpha\>>\<leqslant\>c<rsub|\<alpha\>>>,

    <item><math|d\<Leftrightarrow\>\<alpha\>\<leqslant\>d<rsub|\<alpha\>>>
    and <math|c\<Leftrightarrow\>c<rsub|\<alpha\>>\<leqslant\>\<alpha\>>: the
    abduction answer is only <math|c>,

    <item><math|d\<Leftrightarrow\>d<rsub|\<alpha\>>\<leqslant\>\<alpha\>>
    and <math|c\<Leftrightarrow\>\<alpha\>\<leqslant\>c<rsub|\<alpha\>>>: the
    abduction answer is only <math|c>,

    <item><math|d\<Leftrightarrow\>d<rsub|\<alpha\>>\<leqslant\>\<alpha\>>
    and <math|c\<Leftrightarrow\>c<rsub|\<alpha\>>\<leqslant\>\<alpha\>>: the
    abduction answers are <math|c> and <math|c<rsub|\<alpha\>>\<leqslant\>d<rsub|\<alpha\>>>.
  </enumerate>

  Thanks to cases (1) and (4) above, the abduction algorithm can find some
  answers which are not fully maximal.

  To check whether <math|A\<Rightarrow\>B>, we check for each
  <math|b\<in\>B>:

  <\itemize>
    <item>if <math|b=x<wide|=|\<dot\>>y>, that
    <math|A<around*|(|x|)>=A<around*|(|y|)>>, where
    <math|A<around*|(|\<cdummy\>|)>> is the substitution corresponding to
    equations and implicit equalities in <math|A>;

    <item>if <math|b=x<wide|\<leqslant\>|\<dot\>>y>, that
    <math|A\<wedge\>y<wide|\<less\>|\<dot\>>x> is not satisfiable.
  </itemize>

  For more details of the algorithm, see Section <reference|SCANumAlg>.

  <section|Constraint Generalization><label|ConstrnGenMain>

  We define <em|constraint generalization> as the task of finding common
  consequences, as specific as possible, of conjunctions of atomic formulas.
  Notice that there is at most one maximally specific constraint
  generalization answer. Therefore the completeness condition for constraint
  generalization reduces to requiring most specific answers.

  <\definition>
    <label|CorComplLUB>A quantified conjunction of atoms
    <math|\<exists\><wide|\<alpha\>|\<bar\>>.A\<in\>\<cal-F\>> is a
    <em|constraint generalization answer> to <math|\<vee\><rsub|i>D<rsub|i>>,
    where <math|D<rsub|i>> are conjunctions of atoms in <math|\<cal-L\>>,
    when <math|\<cal-M\>\<vDash\>\<wedge\><rsub|i><around|(|D<rsub|i>\<Rightarrow\>\<exists\><wide|\<alpha\>|\<bar\>>.A|)>>.
    A constraint generalization answer is <em|most specific> when: for every
    solution <math|\<exists\><wide|\<alpha\>|\<bar\>><rsub|s>.A<rsub|s>> with
    <math|\<cal-M\>\<vDash\>\<wedge\><rsub|i><around|(|D<rsub|i>\<Rightarrow\>\<exists\><wide|\<alpha\>|\<bar\>><rsub|s>.A<rsub|s>|)>>,
    <math|\<cal-M\>\<vDash\>A\<Rightarrow\>\<exists\><wide|\<alpha\>|\<bar\>><rsub|s>.A<rsub|s>>
    (with variables renamed so that <math|<wide|\<alpha\>|\<bar\>><rsub|s>#FV<around|(|A|)>>).
    By <math|LUB<around*|(|<wide|D<rsub|i>|\<bar\>>|)>> we denote the most
    general constraint generalization answer to
    <math|\<vee\><rsub|i>D<rsub|i>>, by <math|LUB<around*|(|\<cdot\>|)>> an
    algorithm that computes it.
  </definition>

  Consider an <verbatim|eval>-like example, where the disjuncts include the
  conjunctions of premises and conclusions of a type inference constraint. We
  are interested in finding

  <\eqnarray*>
    <tformat|<table|<row|<cell|LUB<around*|(|<wide|D<rsub|i>\<wedge\>C<rsub|i>|\<bar\>>|)>>|<cell|=<with|mode|text|
    >LUB>|<cell|<around*|(|\<beta\><wide|=|\<dot\>>\<alpha\>\<rightarrow\>\<beta\><rsub|1>\<wedge\>\<alpha\><wide|=|\<dot\>>Term<around|(|Int|)>\<wedge\>\<beta\><rsub|1><wide|=|\<dot\>>Int,<next-line>\<beta\><wide|=|\<dot\>>\<alpha\>\<rightarrow\>\<beta\><rsub|1>\<wedge\>\<alpha\><wide|=|\<dot\>>Term<around|(|Bool|)>\<wedge\>\<beta\><rsub|1><wide|=|\<dot\>>Bool,<next-line>\<beta\><wide|=|\<dot\>>\<alpha\>\<rightarrow\>\<beta\><rsub|1>\<wedge\>\<alpha\><wide|=|\<dot\>>Term<around|(|\<gamma\>|)>\<wedge\>\<beta\><rsub|1><wide|=|\<dot\>>\<gamma\>|)>>>>>
  </eqnarray*>

  for which the solution is <math|\<exists\>\<alpha\><rsub|1>.\<beta\><wide|=|\<dot\>>\<alpha\>\<rightarrow\>\<beta\><rsub|1>\<wedge\>\<alpha\><wide|=|\<dot\>>Term<around*|(|\<alpha\><rsub|1>|)>\<wedge\>\<beta\><rsub|1><wide|=|\<dot\>>\<alpha\><rsub|1>>.

  We discuss issues specific to postcondition inference in Section
  <reference|ConstrnGenAlg>.

  <subsection|Algorithm for Combining Domains>

  First order most specific anti-unifiers are closely related to constraint
  generalization.

  <\definition>
    A sequence of substitutions <math|<wide|S<rsub|i>|\<bar\>>> is an
    <em|anti-unifier> of a same-length sequence of terms
    <math|<wide|t<rsub|i>|\<bar\>>> when there is a term <math|t<rsub|G>>
    such that <math|\<forall\>i,S<rsub|i><around*|(|t<rsub|G>|)>=t<rsub|i>>.
    The term <math|t<rsub|G>> is called a <em|common generalization> of
    <math|<wide|t<rsub|i>|\<bar\>>>.

    An anti-unifier <math|<wide|S<rsub|i>|\<bar\>>> is a <em|most general
    anti-unifier> of <math|<wide|t<rsub|i>|\<bar\>>> when given any other
    anti-unifier <math|<wide|\<eta\><rsub|i>|\<bar\>>> there exists a
    substitution <math|\<rho\>> such that
    <math|\<eta\><rsub|i>=S<rsub|i>\<rho\>>. We call <math|t<rsub|G>> such
    that <math|S<rsub|i><around*|(|t<rsub|G>|)>=t<rsub|i>> the <em|most
    specific generalization> (MSG) of <math|<wide|t<rsub|i>|\<bar\>>>. We
    require, without loss of generality, that variables used by
    anti-unification are fresh: <math|<around*|{|x\<in\>X<mid|\|>S<rsub|i><around*|(|x|)>\<neq\>x|}>#FV<around*|(|<wide|t<rsub|i>|\<bar\>>|)>>.
  </definition>

  We define an <em|alien subterm> (cf. Baader and Schulz
  <cite|UnificationBaader>) of a term <math|\<tau\>> of sort
  <math|s<rsub|type>> to be a maximally large subterm <math|t> of
  <math|\<tau\>> of sort <math|s\<neq\>s<rsub|type>>. Let
  <math|LUB<rsub|s><around*|(|<wide|D<rsub|i><rsup|s>|\<bar\>>|)>> give most
  specific constraint generalization answers to
  <math|\<vee\><rsub|i>D<rsub|i><rsup|s>> for conjunctions of atoms of sort
  <math|s> for <math|s\<neq\>s<rsub|type>>. We define
  <math|LUB<around*|(|<wide|D<rsub|i>|\<bar\>>|)>=\<exists\><wide|\<alpha\>|\<bar\>>.A>
  in Table <reference|LUBAlg>.<\float|float|t>
    <\big-table>
      <tabular|<tformat|<table|<row|<cell|<strong|let>
      <math|\<wedge\><rsub|s>D<rsub|i><rsup|s>\<equiv\>D<rsub|i>> where
      <math|D<rsub|i><rsup|s>> is of sort <math|s>>>|<row|<cell|<strong|let>
      <math|D<rsub|i><rsup|t>> be <math|D<rsub|i><rsup|s<rsub|type>>> with
      all alien subterms <math|<wide|a<rsup|j><rsub|i>|\<bar\>>> replaced by
      fresh variables <math|<wide|\<alpha\><rsup|j><rsub|i>|\<bar\>>> of
      corresp. sorts>>|<row|<cell|<strong|let>
      <math|D<rsup|a><rsub|i>=<wide|\<alpha\><rsup|j><rsub|i>|\<bar\>><wide|=|\<dot\>><wide|a<rsup|j><rsub|i>|\<bar\>>>
      and <math|\<wedge\><rsub|s>D<rsub|i><rsup|t,s>\<equiv\>D<rsub|i><rsup|a>>
      where <math|D<rsub|i><rsup|t,s>> is in sort
      <math|s>>>|<row|<cell|<strong|let> <math|\<wedge\><rsub|s>D<rsup|t><rsub|i,s>\<equiv\>\<b-U\><around|(|D<rsup|t><rsub|i>|)>>
      where <math|D<rsup|t><rsub|i,s>> is of sort <math|s>>>|<row|<cell|For
      the sort <math|s<rsub|type>>:>>|<row|<cell|
      \ <tabular|<tformat|<table|<row|<cell|<strong|let>
      <math|V=<around*|{|x<rsub|j>,<wide|t<rsub|i,j>|\<bar\>><mid|\|>\<forall\>i\<exists\>t<rsub|i,j>.x<rsub|j><wide|=|\<dot\>>t<rsub|i,j>\<in\>D<rsub|i,s<rsub|type>><rsup|t>|}>>>>|<row|<cell|<strong|let>
      <math|G=<around*|{|<wide|\<alpha\>|\<bar\>><rsub|j>,g<rsub|j>,<wide|S<rsub|i,j>|\<bar\>><mid|\|>S<rsub|i,j>=<around*|[|<wide|\<alpha\>|\<bar\>><rsub|j>\<assign\><wide|g|\<bar\>><rsub|j><rsup|i>|]>,S<rsub|i,j><around*|(|g<rsub|j>|)>=t<rsub|i,j>|}>>>>|<row|<cell|
      \ \ \ \ \ be the most specific anti-unifiers of
      <math|<around*|{|<wide|<rsub|>t<rsub|i,j>|\<bar\>><mid|\|><around*|(|x<rsub|j>,<wide|t<rsub|i,j>|\<bar\>>|)>\<in\>V|}>>
      for each <math|j>>>|<row|<cell|<strong|let>
      <math|D<rsub|i><rsup|u>=\<wedge\><rsub|j><wide|\<alpha\>|\<bar\>><rsub|j><wide|=|\<dot\>><wide|g|\<bar\>><rsub|j><rsup|i>>
      and <math|D<rsub|i><rsup|g>=D<rsub|i,s<rsub|type>><rsup|t>\<wedge\>D<rsub|i><rsup|u>>>>|<row|<cell|<strong|let>
      <math|D<rsup|v><rsub|i>=<around*|{|x<wide|=|\<dot\>>y<mid|\|>x<wide|=|\<dot\>>t<rsub|1>\<in\>D<rsub|i><rsup|g>,y<wide|=|\<dot\>>t<rsub|2>\<in\>D<rsub|i><rsup|g>,\<cal-M\>\<vDash\>D<rsub|i><rsup|g>\<Rightarrow\>t<rsub|1><wide|=|\<dot\>>t<rsub|2>|}>>>>|<row|<cell|<strong|let>
      <math|A<rsub|s<rsub|type>>=\<wedge\><rsub|j>x<rsub|j><wide|=|\<dot\>>g<rsub|j>\<wedge\><big|cap><rsub|i><around*|(|D<rsub|i><rsup|g>\<wedge\>D<rsub|i><rsup|v>|)>>>>|<row|<cell|
      \ where equations are ordered so that only one of
      <math|a<wide|=|\<dot\>>b,b<wide|=|\<dot\>>a> appears
      anywhere>>|<row|<cell|<strong|let> <math|<wide|\<alpha\>|\<bar\>><rsub|s<rsub|type>>=<wide|<wide|\<alpha\>|\<bar\>><rsub|j>|\<bar\>>>>>>>>>>|<row|<cell|<strong|let>
      <math|\<wedge\><rsub|s>D<rsup|u><rsub|i,s>\<equiv\>D<rsup|u><rsub|i>>
      for <math|D<rsup|u><rsub|i,s>> of sort <math|s>>>|<row|<cell|For sorts
      <math|s\<neq\>s<rsub|type>>:>>|<row|<cell| \ \ <strong|let>
      <math|\<exists\><wide|\<alpha\>|\<bar\>><rsub|s>.A<rsub|s>=LUB<rsub|s><around*|(|<wide|D<rsub|i><rsup|s>\<wedge\><wide|D<rsup|a><rsub|i>|~><around*|(|D<rsup|t><rsub|i,s>\<wedge\>D<rsup|u><rsub|i,s>|)>|\<bar\>>|)>>>>|<row|<cell|<strong|return>
      <math|\<exists\><wide|<wide|\<alpha\><rsup|j><rsub|i>|\<bar\>>|\<bar\>><wide|<wide|\<alpha\>|\<bar\>><rsub|s>|\<bar\>>.\<wedge\><rsub|s>A<rsub|s>>>>>>><label|LUBAlg>
    </big-table|LUB algorithm <math|LUB<around*|(|<wide|D<rsub|i>|\<bar\>>|)>=\<exists\><wide|\<alpha\>|\<bar\>>.A>>
  </float> The algorithm separates formulas into single-sorted formulas,
  computes anti-unification of terms equal to the same variable in each
  disjunct, and calls constraint generalization for other sorts. It adds to
  the disjuncts passed to generalization for other sorts, equations binding
  the generalization variables (introduced by anti-unification) of the
  particular sort. To find the anti-unifiers, we adapt the anti-unification
  algorithm provided in Østvold <cite|AntiUnifAlg>, fig. 2. The proof of the
  following theorem is in Section <reference|LUBProofs>.

  <\theorem>
    <label|CorComplLUBThm><math|LUB<around*|(|<wide|D<rsub|i>|\<bar\>>|)>>
    from Table <reference|LUBAlg> meets the Definition
    <reference|CorComplLUB> conditions for most specific constraint
    generalization answer to <math|\<vee\><rsub|i>D<rsub|i>>.
  </theorem>

  In our actual implementation, we do not separate alien subterms, i.e. we do
  not compute <math|D<rsub|i><rsup|t>> and <math|D<rsub|i><rsup|a>>. Rather,
  we rely on our implementation of unification <math|\<b-U\>> to separate out
  equations in sorts other than <math|s<rsub|type>>.

  <subsection|Linear Arithmetic>

  Equality under premises within linear arithmetic:
  <math|D\<vDash\>\<alpha\><wide|=|\<dot\>>\<beta\>> can be decided by
  checking whether the polytopes <math|D\<wedge\>\<alpha\>\<less\>\<beta\>>
  and <math|D\<wedge\>\<beta\>\<less\>\<alpha\>> are empty, which can be done
  by Fourier-Motzkin elimination.

  In contrast to the free term algebra, for the logic of linear inequalities
  over real or rational numbers we have the following quantifier elimination
  property. For all <math|\<exists\><wide|\<alpha\>|\<bar\>>.A\<in\>\<cal-F\>>,
  there is a conjunction of atoms <math|A<rprime|'>> such that
  <math|\<cal-M\>\<vDash\>A<rprime|'>\<Leftrightarrow\>\<exists\><wide|\<alpha\>|\<bar\>>.A>.
  Therefore, we need not introduce new variables.

  A system of linear inequalities is <em|full-dimensional> when the set of
  solutions is not contained in an affine subspace of dimension smaller than
  the number of variables. In other words, a full-dimensional system of
  inequalities does not have implicit equalities. The task of constraint
  generalization <math|LUB<around*|(|<wide|D<rsub|i>|\<bar\>>|)>> for
  full-dimensional inequalities is equivalent to finding the convex hull of
  the half-space represented, possibly unbounded polytopes <math|D<rsub|i>>.
  Fukuda, Liebling and Lütolf <cite|ConvexHull> provide a polynomial-time
  algorithm to find the half-space represented convex hull of closed
  polytopes. The algorithm can be generalized to unbounded polytopes.

  When all variables of an equation <math|a<wide|=|\<dot\>>b> appear in all
  branches <math|D<rsub|i>>, we can turn the equation
  <math|a<wide|=|\<dot\>>b> into pair of inequalities
  <math|a\<leqslant\>b\<wedge\>b\<leqslant\>a>. We eliminate all equations
  and implicit equalities which contain a variable not shared by all
  <math|D<rsub|i>>, by substituting out such variables. We conjecture that
  the resulting algorithm meets the correctness and completeness conditions.

  More details of the algorithm implemented in <name|InvarGenT> can be found
  in Section <reference|NumConstrnGenAlg>.

  <subsection|Abductive Constraint Generalization><label|AbdConstrnGenMain>

  It turns out that constraint generalization as we defined it is
  insufficient. Consider replacing <verbatim|function> by
  <verbatim|efunction> in a function of type
  <math|\<tau\><rsub|1>\<rightarrow\>\<tau\><rsub|2>> for which type
  inference works fine. We expect the resulting type to have the form
  <math|\<tau\><rsub|1>\<rightarrow\>\<exists\>.\<tau\><rsub|2>>, i.e.
  without existential type variables. But while unification reconstructs
  <math|\<tau\><rsub|2>> from the result types of the branches, constraint
  generalization will fail to generate <math|\<tau\><rsub|2>> when a branch
  under-constrains the result, does not ``care'' about the specific type. To
  mitigate this problem we introduce <em|abductive constraint generalization>
  and modify our anti-unification algorithm. Constraint generalization in the
  numerical domain does not need such modification.

  We extend the notion of constraint generalization:

  <\definition>
    <label|CorAbdLUB>Substitution <math|U> and solved form formula
    <math|\<exists\><wide|\<alpha\>|\<bar\>>.A> are an answer to
    <em|abductive constraint generalization> problem
    <math|<wide|D<rsub|i>|\<bar\>>> given a quantifier prefix
    <math|\<cal-Q\>> when:

    <\enumerate>
      <item><math|<around*|(|\<forall\>i|)>\<cal-M\>\<vDash\>U<around*|(|D<rsub|i>|)>\<Rightarrow\>\<exists\><wide|\<alpha\>|\<bar\>>\\FV<around*|(|U|)>.A>;

      <item>If <math|\<alpha\>\<in\>Dom<around*|(|U|)>>, then
      <math|<around*|(|\<exists\>\<alpha\>|)>\<in\>\<cal-Q\>> -- variables
      substituted by <math|U> are existentially quantified;

      <item><math|<around*|(|\<forall\>i|)>\<cal-M\>\<vDash\>\<forall\><around*|(|Dom<around*|(|U|)>|)>\<exists\><around*|(|FV<around*|(|D<rsub|i>|)>\\Dom<around*|(|U|)>|)>.D<rsub|i>>.
    </enumerate>
  </definition>

  The sort-integrating algorithm changes only minimally. We adapt the
  anti-unification algorithm to compute the substitution <math|U> from
  Definition <reference|CorAbdLUB>. For details of the algorithms, see
  Section <reference|AbdConstrnGenAlg>.

  <section|Negative Constraints><label|NegElimMain>

  We collect implication branches with conclusion <math|C<rsub|i>=\<b-F\>>
  and do not pass them to abduction or constraint generalization.

  For the numerical sort, optionally but by default, we try to turn the
  negative constraint <math|D<rsub|i><rsup|k>\<Rightarrow\>\<b-F\>> into a
  positive contribution to constraints under assumption that the numerical
  domain is integer numbers rather than rationals. We convert
  <math|\<neg\>D<rsub|i><rsup|k>> into disjunctive normal form, and replace
  strict inequalities <math|w\<gtr\>0> with weak inequalities
  <math|-w\<leq\>-1>, assuming w.l.o.g. integer coefficients in <math|w>. We
  eliminate each disjunct inconsistent with some branch
  <math|D<rsub|j><rsup|k>\<wedge\>C<rsub|j><rsup|k>>. If exactly one disjunct
  remains, it is the solution to the negative constraint
  <math|D<rsub|i><rsup|k>\<Rightarrow\>\<b-F\>>.

  After a joint constraint abduction answer has been found, we check whether
  all negated constraints, i.e. <math|D<rsub|i><rsup|k>> for
  <math|C<rsub|i><rsup|k>=\<b-F\>>, are inconsistent. If not, we backtrack:
  redo abduction with <math|A<rsup|k>> put into the discard list. Moreover,
  we include in simple constraint abduction a heuristic to prefer partial
  answers which make more negated constraints inconsistent.

  For details of the algorithm, see Section <reference|NegElimAlg>.

  <section|Details of Solving for Predicate Variables><label|PredVarMain>

  Faced with an inference problem <math|\<Phi\>>, we solve it using iterated
  abduction. Let

  <\equation*>
    \<exists\>\<delta\>\<Phi\>\<equiv\>\<exists\>\<delta\>\<cal-Q\>.\<wedge\><rsub|i><around*|(|D<rsub|i>\<Rightarrow\>C<rsub|i>|)>=\<exists\>\<delta\>NF<around*|(|\<Phi\>|)>
  </equation*>

  where <math|D<rsub|i>,C<rsub|i>> are conjunctions of atoms, be quantifier
  alternation-minimizing normalization of <math|\<Phi\>> (the variable
  <math|\<delta\>> is used just to bring existentially quantified variables
  to the front, if possible). Using the prenex-normal form simplifies formal
  presentation.

  <\definition>
    <label|AtomizedForm>We will say that a quantifier prefix and a solved
    form formula <math|\<exists\><wide|\<alpha\>|\<bar\>>.A> are in
    <em|atomized form with respect to parameters
    <math|<wide|\<beta\>|\<bar\>>>>, when: variables
    <math|<wide|\<beta\>|\<bar\>>> are in the same quantifier alternation in
    <math|\<cal-Q\>>, <math|\<cal-M\>\<vDash\>\<cal-Q\>.A<around*|[|<wide|\<alpha\>|\<bar\>><wide|\<beta\>|\<bar\>>\<assign\><wide|t|\<bar\>>|]>>
    for some <math|<wide|t|\<bar\>>>, and the following two conditions hold:

    <\enumerate>
      <item>there are no properties expressed in <math|A> in a way
      constraining parameters <math|<wide|\<alpha\>|\<bar\>><wide|\<beta\>|\<bar\>>>
      that can also be expressed without constraining them: if there are
      conjunctions of atoms <math|C,D> such that
      <math|\<cal-M\>\<vDash\>D\<wedge\>C\<Rightarrow\>A> and
      <math|\<cal-M\>\<vDash\>\<cal-Q\>.D>, then there exists a conjunction
      of atoms <math|B> such that <math|B\<subset\>A>,
      <math|\<cal-M\>\<vDash\>\<cal-Q\>.B> and
      <math|\<cal-M\>\<vDash\>C\<Rightarrow\><around*|(|A\\B|)>>, where
      <math|A\\B> is a conjunction of atoms in <math|A> that are not in
      <math|B>;

      <item>all properties expressed in <math|A> in a way constraining
      parameters <math|<wide|\<alpha\>|\<bar\>><wide|\<beta\>|\<bar\>>> are
      also expressed using only variables
      <math|\<cal-Q\><rsub|\<less\>\<beta\>>> (for any
      <math|\<beta\>\<in\><wide|\<beta\>|\<bar\>>>) and
      <math|<wide|\<alpha\>|\<bar\>><wide|\<beta\>|\<bar\>>>: if there is a
      conjunction of atoms <math|C\<subset\>A> such that
      <math|\<cal-M\>\<nvDash\>\<cal-Q\><around*|[|<around*|(|\<forall\><wide|\<beta\>|\<bar\>>|)>\<assign\><around*|(|\<forall\><wide|\<alpha\>|\<bar\>><wide|\<beta\>|\<bar\>>|)>|]>.C>,
      then there is a conjunction of atoms <math|D\<subset\>A> such that
      <math|FV<around*|(|D|)>\<subset\>\<cal-Q\><rsub|\<less\>\<beta\>><wide|\<alpha\>|\<bar\>><wide|\<beta\>|\<bar\>>>
      and <math|\<cal-M\>\<vDash\>\<cal-Q\><around*|[|<around*|(|\<forall\><wide|\<beta\>|\<bar\>>|)>\<assign\><around*|(|\<forall\><wide|\<alpha\>|\<bar\>><wide|\<beta\>|\<bar\>>|)>|]>.D\<Rightarrow\>C>.
    </enumerate>

    The atomized form is <em|with respect to parameters
    <math|<wide|<wide|\<beta\>|\<bar\>><rsup|\<chi\>>|\<bar\>>>> when it is
    an atomized form with respect to parameters
    <math|<wide|\<beta\>|\<bar\>><rsup|\<chi\>>> for all
    <math|<wide|\<beta\>|\<bar\>><rsup|\<chi\>>\<in\><wide|<wide|\<beta\>|\<bar\>><rsup|\<chi\>>|\<bar\>>>.
  </definition>

  <\proposition>
    Let <math|\<cal-Q\>.<wide|\<alpha\>|\<bar\>><rsub|1><wide|=|\<dot\>><wide|t|\<bar\>><rsub|1>\<wedge\><wide|\<alpha\>|\<bar\>><rsub|2><wide|=|\<dot\>><wide|t|\<bar\>><rsub|2>>
    be a formula in <math|\<cal-L\>> with sorts <math|s<rsub|type>> and the
    linear arithmetic sort. If <math|<around*|[|<wide|\<alpha\>|\<bar\>><rsub|1>\<assign\><wide|t|\<bar\>><rsub|1>;<wide|\<alpha\>|\<bar\>><rsub|2>\<assign\><wide|t|\<bar\>><rsub|2>|]>>
    is a substitution, <math|<around*|[|<wide|\<alpha\>|\<bar\>><rsub|1>\<assign\><wide|t|\<bar\>><rsub|1>|]>>
    agrees with quantifier prefix <math|\<cal-Q\>> and
    <math|<wide|\<alpha\>|\<bar\>><rsub|2>\<subseteq\><wide|\<alpha\>|\<bar\>><wide|\<beta\>|\<bar\>>>,
    then <math|\<exists\><wide|\<alpha\>|\<bar\>>.<wide|\<alpha\>|\<bar\>><rsub|1><wide|=|\<dot\>><wide|t|\<bar\>><rsub|1>\<wedge\><wide|\<alpha\>|\<bar\>><rsub|2><wide|=|\<dot\>><wide|t|\<bar\>><rsub|2>>
    is in atomized form w.r.t. parameters <math|<wide|\<beta\>|\<bar\>>>.
  </proposition>

  Symbolically we denote an atomized form that is equivalent to <math|A> by
  <math|Atomized<around*|(|A|)>>. For inequalities,
  <math|Atomized<around*|(|A|)>> can be recovered during the Fourier-Motzkin
  procedure by keeping some of the inequalities implied by <math|A>. Atomized
  forms are required so that we can distribute the constraints among the
  predicate variables -- implicit constraints are made explicit.

  Take a conjunction of atoms <math|A\<in\>\<cal-L\>>, a quantifier prefix
  <math|\<cal-Q\>>, and variables <with|mode|math|<wide|\<alpha\>|\<bar\>>,<wide|<wide|\<beta\>|\<bar\>><rsup|\<chi\>>|\<bar\>>>,
  where <math|\<chi\>> varies over <math|PV<around*|(|\<cal-Q\>|)>>. Let us
  discuss the routine <math|Split<around*|(|\<cal-Q\>,<wide|\<alpha\>|\<bar\>>,A,<wide|<wide|\<beta\>|\<bar\>><rsup|\<chi\>>|\<bar\>>,<wide|A<rsub|\<chi\>><rsup|0>|\<bar\>>|)>>
  defined in Table <reference|SplitAlg><\float|float|t>
    <\big-table>
      <label|SplitAlg><strong|let>

      <\eqnarray*>
        <tformat|<cwith|1|1|2|2|cell-valign|B>|<table|<row|<cell|\<alpha\>\<prec\>\<beta\>>|<cell|=>|<cell|\<alpha\>\<less\><rsub|\<cal-Q\>>\<beta\>\<vee\><around*|(|\<alpha\>\<leqslant\><rsub|\<cal-Q\>>\<beta\>\<wedge\>\<beta\>\<nless\><rsub|\<cal-Q\>>\<alpha\>\<wedge\>\<alpha\>\<in\><wide|<wide|\<beta\>|\<bar\>><rsup|\<chi\>>|\<bar\>>\<wedge\>\<beta\>\<nin\><wide|<wide|\<beta\>|\<bar\>><rsup|\<chi\>>|\<bar\>>|)>>>|<row|<cell|A<rsub|\<alpha\>\<beta\>>>|<cell|=>|<cell|<around*|{|\<beta\><wide|=|\<dot\>>\<alpha\>\<in\>A<mid|\|>\<beta\>\<in\><wide|<wide|\<beta\>|\<bar\>><rsup|\<chi\>>|\<bar\>>\<wedge\><around*|(|\<exists\>\<alpha\>|)>\<in\>\<cal-Q\>\<wedge\>\<beta\>\<prec\>\<alpha\>|}>>>|<row|<cell|A<rsub|0>>|<cell|=>|<cell|A\\A<rsub|\<alpha\>\<beta\>>>>|<row|<cell|A<rsup|1><rsub|\<chi\>>>|<cell|=>|<cell|<around*|{|c\<in\>A<rsub|0><mid|\|>\<forall\>\<alpha\>\<in\>FV<around*|(|c|)>.<around*|(|\<exists\>\<alpha\>|)>\<in\>\<cal-Q\>\<vee\><next-line><with|mode|text|
        \ \ \ >\<alpha\>\<less\><rsub|\<cal-Q\>>\<beta\><rsub|\<chi\>>\<wedge\>\<alpha\>\<nin\>PrimCV<around*|(|c|)>\<vee\>\<alpha\>\<in\><wide|<wide|\<beta\>|\<bar\>><rsup|\<chi\>>|\<bar\>>\<wedge\>\<alpha\>\<in\>PrimCV<around*|(|c|)>|}>>>|<row|<cell|A<rsup|2><rsub|\<chi\>>>|<cell|=>|<cell|Atomized<around*|(|<wide|<wide|\<beta\>|\<bar\>><rsup|\<chi\>>|\<bar\>>,A<rsub|\<chi\>><rsup|1>|)>>>|<row|<cell|A<rsup|3><rsub|\<chi\>>>|<cell|=>|<cell|A<rsup|2><rsub|\<chi\>>\\\<cup\><rsub|\<chi\><rprime|'>>A<rsup|1><rsub|\<chi\><rprime|'>>>>>>
      </eqnarray*>

      <strong|if> <math|\<cal-M\>\<nvDash\>\<cal-Q\>.<around*|(|A\<setminus\>\<cup\><rsub|\<chi\>>A<rsup|2><rsub|\<chi\>>|)><around*|[|<wide|\<alpha\>|\<bar\>>\<assign\><wide|t|\<bar\>>|]><with|mode|text|
      \ for all ><wide|t|\<bar\>>>

      <strong|then return> <math|\<bot\>>

      <strong|for all> <math|<wide|A<rsub|\<chi\>><rsup|+>|\<bar\>><with|mode|text|
      min. w.r.t. >\<subset\><with|mode|text| s.t.
      >\<wedge\><rsub|\<chi\>><around*|(|A<rsub|\<chi\>><rsup|+>\<subset\>A<rsup|2><rsub|\<chi\>>|)><text|
      and >\<cal-M\>\<vDash\>\<cal-Q\>.<around*|(|\<cup\><rsub|\<chi\>>A<rsub|\<chi\>><rsup|+>\<Rightarrow\>A|)><around*|[|<wide|\<alpha\>|\<bar\>>\<assign\><wide|t|\<bar\>>|]><with|mode|text|
      \ for some ><wide|t|\<bar\>>>:

      \ \ \ <strong|if> <math|Strat<around*|(|A<rsup|+><rsub|\<chi\>>,<wide|\<beta\>|\<bar\>><rsup|\<chi\>>|)><with|mode|text|
      \ returns >\<bot\><with|mode|text| for some >\<chi\>>

      \ \ \ <strong|then return> <math|\<bot\>>

      \ \ \ <strong|else let>

      <\eqnarray*>
        <tformat|<table|<row|<cell|<wide|\<alpha\>|\<bar\>><rsub|+><rsup|\<chi\>>,A<rsub|\<chi\>><rsup|L>,A<rsup|R><rsub|\<chi\>>>|<cell|=>|<cell|Strat<around*|(|A<rsup|+><rsub|\<chi\>>,<wide|\<beta\>|\<bar\>><rsup|\<chi\>>|)><with|mode|text|
        \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ >>>|<row|<cell|A<rsub|\<chi\>>>|<cell|=>|<cell|A<rsub|\<chi\>><rsup|0>\<cup\>A<rsub|\<chi\>><rsup|L>>>|<row|<cell|<wide|\<alpha\>|\<bar\>><rsup|\<chi\>><rsub|0>>|<cell|=>|<cell|<wide|\<alpha\>|\<bar\>>\<cap\>FV<around*|(|A<rsub|\<chi\>>|)>>>|<row|<cell|<wide|\<alpha\>|\<bar\>><rsup|\<chi\>>>|<cell|=>|<cell|<around*|(|<wide|\<alpha\>|\<bar\>><rsup|\<chi\>><rsub|0>\<setminus\><big|cup><rsub|\<chi\><rprime|'>\<less\><rsub|\<cal-Q\>>\<chi\>><wide|\<alpha\>|\<bar\>><rsup|\<chi\><rprime|'>><rsub|0>|)><wide|\<alpha\>|\<bar\>><rsub|+><rsup|\<chi\>>>>|<row|<cell|A<rsub|+>>|<cell|=>|<cell|\<cup\><rsub|\<chi\>>A<rsub|\<chi\>><rsup|R>>>|<row|<cell|A<rsub|res>>|<cell|=>|<cell|A<rsub|+>\<cup\><wide|A<rsub|+>|~><around*|(|A\<setminus\>\<cup\><rsub|\<chi\>>A<rsub|\<chi\>><rsup|+>|)>>>>>
      </eqnarray*>

      \ \ \ \ \ \ <strong|if> <math|\<cup\><rsub|\<chi\>><wide|\<alpha\>|\<bar\>><rsup|\<chi\>>\<neq\>\<varnothing\>\<vee\>\<cup\><rsub|\<chi\>>A<rsup|3><rsub|\<chi\>>\<neq\>\<varnothing\>>

      \ \ \ \ \ \ <strong|then>

      \ \ \ \ \ \ \ \ \ <math|\<cal-Q\><rprime|'>,A<rsub|res><rprime|'>,<wide|\<exists\><wide|\<alpha\>|\<bar\>><rprime|'><rsup|\<chi\>>.A<rsub|\<chi\>><rprime|'>|\<bar\>>\<in\>>

      \ \ \ \ \ \ \ \ \ \ \ \ <math|Split<around*|(|\<cal-Q\><around*|[|<wide|\<forall\><wide|\<beta\>|\<bar\>><rsup|\<chi\>>|\<bar\>>\<assign\><wide|\<forall\><around*|(|<wide|\<beta\>|\<bar\>><rsup|\<chi\>>\<cup\><wide|\<alpha\>|\<bar\>><rsup|\<chi\>>|)>|\<bar\>>|]>,<wide|\<alpha\>|\<bar\>>\<setminus\>\<cup\><rsub|\<chi\>><wide|\<alpha\>|\<bar\>><rsup|\<chi\>>,A<rsub|res>\<wedge\><rsub|\<chi\>>A<rsup|3><rsub|\<chi\>>,<wide|<wide|\<beta\>|\<bar\>><rsup|\<chi\>>\<cup\><wide|\<alpha\>|\<bar\>><rsup|\<chi\>>|\<bar\>>,<wide|A<rsub|\<chi\>>|\<bar\>>|)>>

      \ \ \ \ \ \ \ \ \ <strong|return> <math|\<cal-Q\><rprime|'>,A<rsub|\<alpha\>\<beta\>>\<wedge\>A<rsub|res><rprime|'>,<wide|\<exists\><wide|\<alpha\>|\<bar\>><rsup|\<chi\>><wide|\<alpha\>|\<bar\>><rprime|'><rsup|\<chi\>>.A<rsub|\<chi\>><rprime|'>|\<bar\>>>

      \ \ \ \ \ \ <strong|else return> <math|\<cal-Q\>\<exists\><around*|(|<wide|\<alpha\>|\<bar\>>\<setminus\>\<cup\><rsub|\<chi\>><wide|\<alpha\>|\<bar\>><rsup|\<chi\>>|)>,A<rsub|\<alpha\>\<beta\>>\<wedge\>A<rsub|res>,<wide|\<exists\><wide|\<alpha\>|\<bar\>><rsup|\<chi\>>.A<rsub|\<chi\>>|\<bar\>>>

      <strong|where> <math|Strat<around*|(|A,<wide|\<beta\>|\<bar\>><rsup|\<chi\>>|)>>
      is computed as follows:

      <\enumerate>
        <item>for every <math|c\<in\>A>, and for every
        <math|\<beta\><rsub|2>\<in\>FV<around*|(|c|)>> such that
        <math|\<beta\><rsub|1>\<less\><rsub|\<cal-Q\>>\<beta\><rsub|2>> for
        <math|\<beta\><rsub|1>\<in\><wide|\<beta\>|\<bar\>><rsup|\<chi\>>>,

        <item>if <math|\<beta\><rsub|2>> is universally quantified in
        <math|\<cal-Q\>>, then return <math|\<bot\>>;

        <item>otherwise, introduce a fresh variable <math|\<alpha\><rsub|f>>,
        replace <math|c\<assign\>c<around*|[|\<beta\><rsub|2>\<assign\>\<alpha\><rsub|f>|]>>,

        <item>add <with|mode|math|\<beta\><rsub|2><wide|=|\<dot\>>\<alpha\><rsub|f>>
        to <with|mode|math|A<rsup|R><rsub|\<chi\>>> and
        <math|\<alpha\><rsub|f>> to <with|mode|math|<wide|\<alpha\>|\<bar\>><rsub|+><rsup|\<chi\>>>,

        <item>after replacing all such <with|mode|math|\<beta\><rsub|2>> add
        the resulting <math|c> to <with|mode|math|A<rsub|\<chi\>><rsup|L>>.
      </enumerate>

      \;
    </big-table|Split routine <math|Split<around*|(|\<cal-Q\>,<wide|\<alpha\>|\<bar\>>,A,<wide|<wide|\<beta\>|\<bar\>><rsup|\<chi\>>|\<bar\>>,<wide|A<rsub|\<chi\>>|\<bar\>>|)>>>
  </float>. <math|PrimCV<around*|(|c|)>> stands for <em|primary constrained
  variables> of an atom <math|c>. These are the variables that can be
  separated to one side of the atom <math|c>. For the sort of terms and the
  numerical sort, <math|\<alpha\>\<in\>PrimCV<around*|(|c|)>> if and only if:
  <math|c\<Leftrightarrow\>\<alpha\><wide|=|\<dot\>>t>, or
  <math|c\<Leftrightarrow\>\<alpha\>\<leqslant\>t>, or <math|c
  \<Leftrightarrow\>t\<leqslant\>\<alpha\>>, for some <math|t> including
  <math|t=min<around*|(|t<rsub|1>,t<rsub|2>|)>> and
  <math|t=max<around*|(|t<rsub|1>,t<rsub|2>|)>> for some
  <math|t<rsub|1>,t<rsub|2>>. For other sorts, the definition of
  <math|PrimCV<around*|(|\<cdummy\>|)>> needs to be extended analogically.
  The selections of <math|<wide|A<rsub|\<chi\>><rsup|+>|\<bar\>>> we try are
  minimal with respect to pointwise set inclusion, i.e. wrt.
  <math|\<leqslant\>> defined as <math|<wide|A<rsub|\<chi\>><rsup|1>|\<bar\>>\<leqslant\><wide|A<rsub|\<chi\>><rsup|2>|\<bar\>>\<Leftrightarrow\>\<forall\>\<chi\>.A<rsup|1><rsub|\<chi\>>\<subseteq\>A<rsup|2><rsub|\<chi\>>>.
  The routine <math|Split> separates an answer formula into components that
  need to become (parts of) the predicate variable solutions, and the
  residual answer <math|A<rsub|res>>. The residual answer is a satisfiable
  formula, it contains solutions to the existentially quantified variables.
  In particular, the types of expressions of interest can be extracted from
  the final residual answer. Note that due to existential types predicates,
  we actually compute <math|Split<around*|(|\<cal-Q\>,<wide|\<alpha\>|\<bar\>>,A,<wide|<wide|\<beta\>|\<bar\>><rsup|\<beta\><rsub|\<chi\>>>|\<bar\>>,<wide|A<rsub|\<beta\><rsub|\<chi\>>><rsup|0>|\<bar\>>|)>>,
  i.e. we index by <math|\<beta\><rsub|\<chi\>>> (which can be multiple for a
  single <math|\<chi\>>) rather than <math|\<chi\>>. We retain the notation
  indexing by <math|\<chi\>> as it better conveys the intent. Let
  <math|Split<around*|(|\<cal-Q\>,<wide|\<alpha\>|\<bar\>>,A,<wide|<wide|\<beta\>|\<bar\>><rsup|\<chi\>>|\<bar\>>|)>>
  be <math|Split<around*|(|\<cal-Q\>,<wide|\<alpha\>|\<bar\>>,A,<wide|<wide|\<beta\>|\<bar\>><rsup|\<chi\>>|\<bar\>>,<wide|\<b-T\>|\<bar\>>|)>>.

  In Table <reference|MainAlgIter>, we describe a single step of solving for
  predicate variables. The iteration of the algorithm starts by substituting
  the partial solutions to predicate variables from the previous iteration
  (Table <reference|MainAlgIter>, Eq. <reference|MainAlgEnt1>). Next, it
  performs constraint generalization, to find the current solutions for
  postcondition-related predicate variables (Eq. <reference|MainAlgEnt2>).
  The found postconditions are then substituted for predicate variables in
  premises, i.e. at places where a definition returning an existential type
  is used recursively (Eq. <reference|MainAlgEnt3>). Having stronger premises
  simplifies, and sometimes enables, the subsequent abduction (Eq.
  <reference|MainAlgEnt4>). The abduction answer is split into parts (Eq.
  <reference|MainAlgEnt5>), that are added to the partial solutions to
  predicate variables (Eqs. <reference|MainAlgEnt6>,
  <reference|MainAlgEnt8>). When abduction shows we need richer
  postconditions, an auxiliary round of abduction is performed (Eq.
  <reference|MainAlgEnt7>). It infers additional preconditions that enable
  the required postconditions. We add these preconditions to the partial
  solutions (Eq. <reference|MainAlgEnt8>). If the resulting partial solutions
  differ from the initial partial solutions, we continue with another
  iteration of the main algorithm.<\float|float|t>
    <\big-table>
      <label|MainAlgIter>

      <\eqnarray*>
        <tformat|<cwith|16|16|2|2|cell-valign|c>|<cwith|17|17|3|3|cell-valign|B>|<cwith|23|23|2|2|cell-valign|c>|<table|<row|<cell|<wide|\<exists\><wide|\<beta\>|\<bar\>><rsup|\<chi\>,k>.F<rsub|\<chi\>>|\<bar\>>>|<cell|=>|<cell|S<rsub|k>>>|<row|<cell|>|<cell|>|<cell|<with|mode|text|In
        iteration 2, remove non-term-sort
        atoms>>>|<row|<cell|>|<cell|>|<cell|<with|mode|text|containing
        outer-scope parameters from >S<rsub|k>.>>|<row|<cell|D<rsub|K><rsup|\<alpha\>>\<Rightarrow\>C<rsub|K><rsup|\<alpha\>>\<in\>R<rsub|k><rsup|->S<rsub|k><around*|(|\<Phi\>|)>>|<cell|=>|<cell|<with|mode|text|all
        such that >\<chi\><rsub|K><around*|(|\<alpha\>,\<alpha\><rsub|\<alpha\>><rsup|K>|)>\<in\>C<rsub|K><rsup|\<alpha\>>,<eq-number><label|MainAlgEnt1>>>|<row|<cell|>|<cell|>|<cell|<wide|C<rsup|\<alpha\>><rsub|j>|\<bar\>>=<around*|{|C<mid|\|>D\<Rightarrow\>C\<in\>S<rsub|k><around*|(|\<Phi\>|)>\<wedge\>D\<subseteq\>D<rsup|\<alpha\>><rsub|K>|}>>>|<row|<cell|\<alpha\><rsub|K>>|<cell|:>|<cell|\<chi\><rsub|K><around*|(|\<alpha\><rsub|K>|)><with|mode|text|
        is a positive atom in >\<Phi\>>>|<row|<cell|U<rsub|\<chi\><rsub|K>>,\<exists\><wide|\<alpha\>|\<bar\>><rsup|\<chi\><rsub|K>><rsub|g>.G<rsub|\<chi\><rsub|K>>,<wide|B<rsub|d><rsup|K>|\<bar\>>>|<cell|=>|<cell|LUB<around*|(|\<alpha\><rsub|K>,<wide|\<delta\><wide|=|\<dot\>>\<alpha\>\<wedge\>D<rsup|\<alpha\>><rsub|K>\<wedge\><rsub|j>C<rsup|\<alpha\>><rsub|j>|\<bar\>><rsub|\<alpha\>\<in\><wide|\<alpha\><rsub|3><rsup|i,K>|\<bar\>>>|)><eq-number><label|MainAlgEnt2>>>|<row|<cell|<wide|\<tau\>|\<vect\>><rsub|\<varepsilon\><rsub|K>>>|<cell|=>|<cell|<wide|<around*|{|\<alpha\>\<in\>FV<around*|(|G<rsub|\<chi\><rsub|K>>|)>\\\<delta\>\<delta\><rprime|'><wide|\<alpha\>|\<bar\>><rsup|\<chi\><rsub|K>><rsub|g><mid|\|><around*|(|\<exists\>\<alpha\>|)>\<in\>\<cal-Q\>\<vee\>\<alpha\>\<in\><wide|<wide|\<beta\>|\<bar\>><rsup|\<chi\>>|\<bar\>>\\<wide|\<beta\>|\<bar\>><rsup|\<chi\><rsub|K>>|}>|\<vect\>>>>|<row|<cell|\<Xi\><around*|(|\<exists\><wide|\<alpha\>|\<bar\>><rsup|\<chi\><rsub|K>><rsub|g>.G<rsub|\<chi\><rsub|K>>|)>>|<cell|=>|<cell|\<exists\>FV<around*|(|<wide|\<tau\>|\<vect\>><rsub|\<varepsilon\><rsub|K>>,G<rsub|\<chi\><rsub|K>>|)>\\\<delta\>\<delta\><rprime|'>.\<delta\><rprime|'><wide|=|\<dot\>><wide|\<tau\>|\<vect\>><rsub|\<varepsilon\><rsub|K>>\<wedge\>G<rsub|\<chi\><rsub|K>>>>|<row|<cell|<around*|(|\<exists\><wide|\<alpha\>|\<bar\>><rsup|\<chi\><rsub|K>>.F<rsub|\<chi\><rsub|K>>|)>,\<rho\>>|<cell|=>|<cell|H<around*|(|R<rsub|k><around*|(|\<chi\><rsub|K>|)>,\<Xi\><around*|(|\<exists\><wide|\<alpha\>|\<bar\>><rsub|g><rsup|\<chi\><rsub|K>>.G<rsub|\<chi\><rsub|K>>|)>|)>>>|<row|<cell|R<rsub|g><around*|(|\<chi\><rsub|K>|)>>|<cell|=>|<cell|\<exists\><wide|\<alpha\>|\<bar\>><rsup|\<chi\><rsub|K>>.F<rsub|\<chi\><rsub|K>>>>|<row|<cell|P<rsub|g><around*|(|\<chi\><rsub|K><around*|(|\<delta\>,\<delta\><rprime|'>|)>|)>=P<rsub|g><around*|(|\<chi\><rsub|K><around*|(|\<delta\><rprime|'>|)>|)>>|<cell|=>|<cell|\<delta\><rprime|'><wide|=|\<dot\>><wide|\<tau\>|\<vect\>><rsub|\<varepsilon\><rsub|K>>>>|<row|<cell|F<rsub|\<chi\>><rprime|'>>|<cell|=>|<cell|F<rsub|\<chi\>><around*|[|\<varepsilon\><rsub|K><around*|(|<wide|\<tau\>|\<vect\>><rsub|old>|)>\<assign\>\<varepsilon\><rsub|K><around*|(|<wide|\<tau\>|\<vect\>><rsub|\<varepsilon\><rsub|K>>|)><around*|[|recover<around*|(|<wide|\<tau\>|\<vect\>><rsub|\<varepsilon\><rsub|K>>,<wide|\<tau\>|\<vect\>><rsub|old>|)>|]>|]>>>|<row|<cell|S<rsub|k><rprime|'>>|<cell|=>|<cell|<wide|\<exists\><wide|\<beta\>|\<bar\>><rsup|\<chi\>,k><around*|{|\<alpha\>\<in\>FV<around*|(|F<rprime|'><rsub|\<chi\>>|)><mid|\|>\<beta\><rsub|\<chi\>>\<less\><rsub|\<cal-Q\>>\<alpha\>|}>.F<rprime|'><rsub|\<chi\>><rsup|>|\<bar\>>>>|<row|<cell|\<cal-Q\><rprime|'>.\<wedge\><rsub|i><around*|(|D<rsub|i>\<Rightarrow\>C<rsub|i>|)>\<wedge\><rsub|j><around*|(|D<rsub|j><rsup|->\<Rightarrow\>\<b-F\>|)>>|<cell|=>|<cell|R<rsub|g><rsup|->P<rsub|g><rsup|+>S<rsub|k><rprime|'><around*|(|\<Phi\>\<wedge\><rsub|\<chi\><rsub|K>>U<rsub|\<chi\><rsub|K>>|)><eq-number><label|MainAlgEnt3>>>|<row|<cell|\<exists\><wide|\<alpha\>|\<bar\>>.A<rsub|0>>|<cell|=>|<cell|Abd<around*|(|\<cal-Q\><rprime|'>,<wide|\<beta\>|\<bar\>>=<wide|\<beta\><rsub|\<chi\>><wide|\<beta\><rsup|>|\<bar\>><rsup|\<chi\>>|\<bar\>>,<wide|D<rsub|i>,C<rsub|i>|\<bar\>>|)><eq-number><label|MainAlgEnt4>>>|<row|<cell|A>|<cell|=>|<cell|A<rsub|0>\<wedge\><rsub|j>NegElim<around*|(|\<neg\>Simpl<around*|(|FV<around*|(|D<rsub|j><rsup|->|)>\\<wide|<wide|\<beta\>|\<bar\>><rsup|\<chi\>>|\<bar\>>.D<rsub|j><rsup|->|)>,A<rsub|0>,<wide|D<rsub|i>,C<rsub|i>|\<bar\>>|)>>>|<row|<cell|>|<cell|>|<cell|<with|mode|text|In
        later iterations, check negative constraints.>>>|<row|<cell|<around*|(|\<cal-Q\><rsup|k+1>,A<rsub|res>,<wide|\<exists\><wide|\<alpha\>|\<bar\>><rsup|\<beta\><rsub|\<chi\>>>.A<rsub|\<beta\><rsub|\<chi\>>>|\<bar\>>|)>>|<cell|=>|<cell|Split<around*|(|\<cal-Q\><rprime|'>,<wide|\<alpha\>|\<bar\>>,A,<wide|\<beta\><rsub|\<chi\>><wide|\<beta\><rsup|>|\<bar\>><rsup|\<chi\>>|\<bar\>>|)><eq-number><label|MainAlgEnt5>>>|<row|<cell|<wide|\<tau\>|\<vect\>><rsub|\<varepsilon\><rsub|K>><rprime|'>>|<cell|=>|<cell|<wide|FV<around*|(|<wide|A<rsub|res>|~><around*|(|<wide|\<tau\>|\<vect\>><rsub|\<varepsilon\><rsub|K>>|)>|)>|\<vect\>>>>|<row|<cell|R<rsub|k+1><around*|(|\<chi\><rsub|K>|)>>|<cell|=>|<cell|\<exists\><wide|\<beta\>|\<bar\>><rsup|\<chi\><rsub|K>,k><wide|<wide|\<alpha\>|\<bar\>><rsup|\<beta\><rsub|\<chi\><rsub|K>>>|\<bar\>><wide|\<alpha\>|\<bar\>><rsup|\<chi\><rsub|K>>\\FV<around*|(|<wide|\<tau\>|\<vect\>><rsub|\<varepsilon\><rsub|K>><rprime|'>|)>.\<delta\><rprime|'><wide|=|\<dot\>><wide|\<tau\>|\<vect\>><rsub|\<varepsilon\><rsub|K>><rprime|'>\<wedge\><wide|A<rsub|res>|~><around*|(|F<rsub|\<chi\><rsub|K>>\\\<delta\><rprime|'><wide|=|\<dot\>>\<ldots\>|)><next-line><with|mode|text|
        \ \ \ >\<wedge\><rsub|\<chi\><rsub|K>>A<rsub|\<beta\><rsub|\<chi\><rsub|K>>><around*|[|<wide|\<beta\><rsub|\<chi\><rsub|K>><wide|\<beta\><rsup|>|\<bar\>><rsup|\<beta\><rsub|\<chi\><rsub|K>>>|\<bar\>>\<assign\><wide|\<delta\><wide|\<beta\><rsup|>|\<bar\>><rsup|\<chi\><rsub|K>,k>|\<bar\>>|]><eq-number><label|MainAlgEnt6>>>|<row|<cell|A<rsub|K><rsup|d>>|<cell|=>|<cell|<around*|{|c\<in\>A<rsub|\<beta\><rsub|\<chi\><rsub|K>>><around*|[|<wide|\<beta\><rsub|\<chi\><rsub|K>><wide|\<beta\><rsup|>|\<bar\>><rsup|\<beta\><rsub|\<chi\><rsub|K>>>|\<bar\>>\<assign\><wide|\<delta\><wide|\<beta\><rsup|>|\<bar\>><rsup|\<chi\><rsub|K>,k>|\<bar\>>|]><mid|\|><next-line><with|mode|text|
        \ \ \ \ \ >FV<around*|(|c|)>\<subseteq\>FV<around*|(|\<rho\><around*|(|B<rsub|d><rsup|K>|)>|)>|}>>>|<row|<cell|\<exists\><wide|\<alpha\>|\<bar\>><rprime|'><rsub|K>.A<rprime|'><rsub|K>>|<cell|=>|<cell|Abd<around*|(|\<cal-Q\><rprime|'>,<wide|\<beta\><rsub|\<chi\>><wide|\<beta\><rsup|>|\<bar\>><rsup|\<chi\>>|\<bar\>>\\<wide|\<beta\><rsub|\<chi\><rsub|K>><wide|\<beta\><rsup|>|\<bar\>><rsup|\<chi\><rsub|K>>|\<bar\>>,<wide|\<rho\><around*|(|B<rsub|d><rsup|K>|)>,A<rsub|K><rsup|d>|\<bar\>>|)><eq-number><label|MainAlgEnt7>>>|<row|<cell|<around*|(|\<cal-Q\><rsup|k+1>,\<varnothing\>,<wide|\<exists\><wide|\<alpha\>|\<bar\>><rsup|\<beta\><rsub|\<chi\>>><rprime|'>.A<rsub|\<beta\><rsub|\<chi\>>><rprime|'>|\<bar\>>|)>>|<cell|=>|<cell|Split<around*|(|\<cal-Q\><rsup|k+1>,<wide|<wide|\<alpha\>|\<bar\>><rprime|'><rsub|K>|\<bar\>>,\<wedge\><rsub|K>A<rprime|'><rsub|K>,<wide|\<beta\><rsub|\<chi\>><wide|\<beta\><rsup|>|\<bar\>><rsup|\<chi\>>|\<bar\>>\\<wide|\<beta\><rsub|\<chi\><rsub|K>><wide|\<beta\><rsup|>|\<bar\>><rsup|\<chi\><rsub|K>>|\<bar\>>|)>>>|<row|<cell|S<rsub|k+1><around*|(|\<chi\>|)>>|<cell|=>|<cell|\<exists\><wide|\<beta\>|\<bar\>><rsup|\<chi\>,k>.Simpl<around*|(|\<exists\><wide|<wide|\<alpha\>|\<bar\>><rsup|\<beta\><rsub|\<chi\>>>|\<bar\>>.F<rsub|\<chi\>><rprime|'><next-line><with|mode|text|
        \ \ \ \ \ \ \ \ >\<wedge\>A<rsub|\<beta\><rsub|\<chi\>>><around*|[|<wide|\<beta\><rsub|\<chi\>><wide|\<beta\><rsup|>|\<bar\>><rsup|\<chi\>>|\<bar\>>\<assign\><wide|\<delta\><wide|\<beta\><rsup|>|\<bar\>><rsup|\<chi\>,k>|\<bar\>>|]>\<wedge\>A<rsub|\<beta\><rsub|\<chi\>>><rprime|'>|)><eq-number><label|MainAlgEnt8>>>>>
      </eqnarray*>

      \;
    </big-table|Iteration <math|k> of solving for predicate variables>
  </float>

  Recall Definition <reference|SolTypInfer> of solutions to a type inference
  problem <math|\<Phi\>>.

  <\proposition>
    If a solution to the inference problem <math|\<Phi\>> exists, then there
    is an interpretation of predicate variables <math|\<cal-I\>> such that
    <math|\<cal-M\>,\<cal-I\>\<vDash\>\<Phi\>>.
  </proposition>

  Define

  <\equation*>
    \<Psi\><rsub|0>=<around*|{|<around*|(|\<b-T\>,<wide|\<b-T\>|\<bar\>>,<wide|\<b-T\>|\<bar\>>|)>|}><with|mode|text|,
    \ >\<Psi\><rsub|k+1>=<big|cup><rsub|<around*|(|F<rsub|res><rsup|k>,<wide|\<exists\><wide|\<alpha\>|\<bar\>><rsup|\<chi\>,k>.F<rsub|\<chi\>><rsup|k>|\<bar\>>,<wide|\<exists\><wide|\<alpha\>|\<bar\>><rsup|\<chi\><rsub|K>,k>.F<rsub|\<chi\><rsub|K>><rsup|k>|\<bar\>>|)>\<in\>\<Psi\><rsub|k>>\<Psi\><around*|(|k,\<Phi\>,<wide|\<exists\><wide|\<alpha\>|\<bar\>><rsup|\<chi\>,k>.F<rsub|\<chi\>><rsup|k>|\<bar\>>,<wide|\<exists\><wide|\<alpha\>|\<bar\>><rsup|\<chi\><rsub|K>,k>.F<rsub|\<chi\><rsub|K>><rsup|k>|\<bar\>>|)>
  </equation*>

  where the operator <math|\<Psi\>> such that
  <math|<around*|(|\<exists\><wide|\<alpha\>|\<bar\>><rsub|res>.A<rsub|res>,S<rsub|k+1>,R<rsub|k+1>|)>\<in\>\<Psi\><around*|(|k,\<Phi\>,S<rsub|k>,R<rsub|k>|)>>
  for <math|S<rsub|k>=<wide|\<exists\><wide|\<alpha\>|\<bar\>><rsup|\<chi\>,k>.F<rsub|\<chi\>><rsup|k>|\<bar\>>>,
  <math|R<rsub|k>=<wide|\<exists\><wide|\<alpha\>|\<bar\>><rsup|\<chi\><rsub|K>,k>.F<rsub|\<chi\><rsub|K>><rsup|k>|\<bar\>>>,
  is defined in Table <reference|MainAlgIter>. The convergence condition is:

  <\eqnarray*>
    <tformat|<table|<row|<cell|>|<cell|>|<cell|<around*|(|\<forall\>\<chi\>|)>S<rsub|k+1><around*|(|\<chi\>|)>\<subseteq\>S<rsub|k><around*|(|\<chi\>|)>,>>|<row|<cell|>|<cell|\<wedge\>>|<cell|<around*|(|\<forall\>\<chi\><rsub|K>|)>R<rsub|k+1><around*|(|\<chi\><rsub|K>|)>=R<rsub|k><around*|(|\<chi\><rsub|K>|)>,>>|<row|<cell|>|<cell|\<wedge\>>|<cell|<around*|(|\<forall\>\<beta\><rsub|\<chi\><rsub|K>>|)>A<rsub|\<beta\><rsub|\<chi\><rsub|K>>>=\<b-T\>,>>|<row|<cell|>|<cell|\<wedge\>>|<cell|k\<gtr\>1>>>>
  </eqnarray*>

  \ We argue for the truth of the following theorem in Section
  <reference|PredVarProofs>.

  <\theorem>
    <label|ThCorrect><em|Correctness>. Let
    <math|\<cal-I\>=<around*|[|<wide|\<chi\>|\<bar\>>\<assign\><wide|\<exists\><wide|\<alpha\>|\<bar\>><rsub|\<chi\>>.F<rsub|\<chi\>>|\<bar\>>;<wide|\<chi\><rsub|K>|\<bar\>>\<assign\><wide|\<exists\><wide|\<alpha\>|\<bar\>><rsub|K>.F<rsub|K>|\<bar\>>|]>>
    be an interpretation of predicate variables for an inference problem
    <math|\<Phi\>>. If <math|<around*|(|\<exists\><wide|\<alpha\>|\<bar\>><rsub|res><rprime|'>.F<rsub|res><rprime|'>,<wide|\<exists\><wide|\<alpha\>|\<bar\>><rsup|\<chi\>>.F<rsub|\<chi\>>|\<bar\>>,<wide|\<exists\><wide|\<alpha\>|\<bar\>><rsup|\<chi\><rsub|K>>.F<rsub|\<chi\><rsub|K>>|\<bar\>>|)>\<in\>\<Psi\><around|(|\<Phi\>,<wide|\<exists\><wide|\<alpha\>|\<bar\>><rsup|\<chi\>>.F<rsub|\<chi\>>|\<bar\>>,<wide|\<exists\><wide|\<alpha\>|\<bar\>><rsup|\<chi\><rsub|K>>.F<rsub|\<chi\><rsub|K>>|\<bar\>>|)>>,
    then <math|\<cal-M\>,\<cal-I\>\<vDash\>\<Phi\>>.
  </theorem>

  To prove Theorem <reference|InferCompleteness>, we have to assume that
  there are no existential type predicate variables, i.e. for an inference
  problem <math|\<Phi\>>, <math|PV<around*|(|\<Phi\>|)>=PV<rsup|1><around*|(|\<Phi\>|)>>;
  and also that <math|Abd> in the definition of <math|\<Psi\>> is a complete
  abduction algorithm returning an atomized form formula. Since the
  completeness of abduction assumption is not met, Theorem
  <reference|InferCompleteness> does not describe an actual implementation.
  We argue for the truth of Theorem <reference|InferCompleteness> in Section
  <reference|PredVarProofs>.

  <\theorem>
    <label|InferCompleteness>Let <math|<around*|(|\<exists\><wide|\<alpha\>|\<bar\>><rsup|res><rsub|s>.F<rsub|res><rsup|s>,<wide|\<exists\><wide|\<alpha\>|\<bar\>><rsup|\<chi\>><rsub|s>.F<rsub|\<chi\>><rsup|s>|\<bar\>>|)>>
    be any solution to an inference problem <math|\<Phi\>> with
    <math|<wide|\<chi\>|\<bar\>>=PV<around*|(|\<Phi\>|)>=PV<rsup|1><around*|(|\<Phi\>|)>>.
    Assume that <math|Abd> in the definition of <math|\<Psi\>> is a complete
    abduction algorithm returning an atomized form formula. Then there is a
    chain <math|<around*|(|\<exists\><wide|\<alpha\>|\<bar\>><rsup|res><rsub|k>.F<rsub|res><rsup|k>,<wide|\<exists\><wide|\<alpha\>|\<bar\>><rsup|\<chi\>,k>.F<rsub|\<chi\>><rsup|k>|\<bar\>>|)>\<in\>\<Psi\><rsub|k>>,
    with <with|mode|math|<around*|(|<wide|\<exists\><wide|\<alpha\>|\<bar\>><rsup|\<chi\>,k+1>.F<rsub|\<chi\>><rsup|k+1>|\<bar\>>|)>\<in\>\<Psi\><around|(|k,\<Phi\>,<wide|\<exists\><wide|\<alpha\>|\<bar\>><rsup|\<chi\>,k>.F<rsub|\<chi\>><rsup|k>|\<bar\>>|)>>,
    such that for all <math|k\<geqslant\>1>,
    <math|\<cal-M\>\<vDash\>\<wedge\><rsub|\<chi\>>F<rsup|s><rsub|\<chi\>>\<Rightarrow\><around*|(|\<wedge\><rsub|\<chi\>>F<rsup|k><rsub|\<chi\>>|)><around*|[|<wide|<wide|\<alpha\>|\<bar\>><rsup|\<chi\>,k>|\<bar\>>\<assign\><wide|t|\<bar\>>|]>>
    for some <math|<wide|t|\<bar\>>>.
  </theorem>

  For more discussion on the implementation, see Section
  <reference|PredVarAlg>.<new-page>

  <chapter|<name|InvarGenT>: Tests and Limitations><label|Limitations>

  In this chapter we present types and inference times of tested examples,
  measured on a laptop with <em|Intel Core i3> processor at 2.30GHz, 3MB
  cache. The implementation does not use parallelism.

  <section|Benchmarks>

  Table <reference|Experiments> contains examples using the plain GADTs type
  system, without numerical constraints and existential types. Consider the
  examples from Chuan-kai Lin's <cite|PracticalGADTsInfer>. We tested 7
  longer examples where algorithm <math|\<cal-P\>> finds the expected type.
  <name|InvarGenT> does not have problems with these cases either, except the
  <verbatim|head> function. We also reproduce all 8 examples from
  <cite|PracticalGADTsInfer> where algorithm <math|\<cal-P\>> fails, adapting
  them only to accomodate to the type system <math|MMG<around*|(|X|)>> behind
  <name|InvarGenT>. <name|InvarGenT> fails on two examples. One, the function
  <verbatim|vary>, was contrived to not have a clear intended type. The
  other, the function <verbatim|fd_comp>, can be slightly modified to work
  with <name|InvarGenT>'s type inference. There is also one example, function
  <verbatim|leq>, which requires non-default parameter setting (passing a
  parameter <verbatim|-prefer_guess> to <name|InvarGenT>). In a future
  version, <name|InvarGenT> will attempt multiple parameter settings before
  giving up. Overall, we consider the behavior of <name|InvarGenT> on this
  test suite to be a success.<\float|float|t>
    <\big-table>
      \;

      <block|<tformat|<cwith|17|17|1|1|cell-row-span|2>|<cwith|17|17|2|2|cell-width|2cm>|<cwith|17|17|2|2|cell-hmode|min>|<cwith|17|17|2|2|cell-hyphen|t>|<cwith|18|18|2|2|cell-hyphen|t>|<cwith|18|18|2|2|cell-width|2cm>|<cwith|18|18|2|2|cell-hmode|min>|<cwith|17|17|1|1|cell-valign|b>|<cwith|11|11|2|2|cell-hyphen|t>|<cwith|10|10|2|2|cell-hyphen|t>|<cwith|11|11|2|2|cell-width|2cm>|<cwith|11|11|2|2|cell-hmode|min>|<cwith|10|10|2|2|cell-width|10cm>|<cwith|10|10|2|2|cell-hmode|min>|<cwith|3|3|1|1|cell-valign|t>|<cwith|10|10|1|1|cell-row-span|7>|<cwith|10|10|1|1|cell-valign|t>|<cwith|12|12|2|2|cell-hyphen|t>|<cwith|12|12|2|2|cell-width|10>|<cwith|12|12|2|2|cell-hmode|min>|<cwith|13|13|2|2|cell-hyphen|t>|<cwith|13|13|2|2|cell-width|10>|<cwith|13|13|2|2|cell-hmode|min>|<cwith|5|5|2|2|cell-hyphen|t>|<cwith|5|5|2|2|cell-width|10>|<cwith|5|5|2|2|cell-hmode|min>|<cwith|3|3|2|2|cell-hyphen|t>|<cwith|3|3|1|1|cell-width|3>|<cwith|3|3|1|1|cell-hmode|min>|<cwith|10|10|1|1|cell-hyphen|t>|<cwith|10|10|1|1|cell-width|3>|<cwith|10|10|1|1|cell-hmode|min>|<cwith|3|3|1|1|cell-hyphen|t>|<cwith|3|3|1|1|cell-row-span|7>|<cwith|3|3|2|2|cell-width|10cm>|<cwith|3|3|2|2|cell-hmode|min>|<table|<row|<cell|<em|Class
      of examples>>|<cell|<em|Function name: inferred type>>|<cell|<em|Inf.
      time>>>|<row|<cell|incompl. ex. <cite|OutsideIn>>|<cell|<verbatim|rx:
      <math|\<forall\>>a.R a<math|\<rightarrow\>>Int>>|<cell|\<less\>0.01s>>|<row|<\cell>
        examples from <cite|PointwiseGADTs> within the scope of algorithm
        <math|\<cal-P\>>
      </cell>|<\cell>
        <verbatim|rotate: <small|<math|\<forall\>>a.Dir<math|\<rightarrow\>>Int<math|\<rightarrow\>>RoB
        (Black, a)<math|\<rightarrow\>>Dir<math|\<rightarrow\>>Int<math|\<rightarrow\><next-line>>
        RoB (Black, a)<math|\<rightarrow\>>RoB (Red,
        a)<math|\<rightarrow\>>RoB (Black, S a)>>
      </cell>|<cell|0.02s>>|<row|<cell|>|<cell|<verbatim|zip2:
      <small|<math|\<forall\>>a, b.Zip2 (B,
      a)<math|\<rightarrow\>>b<math|\<rightarrow\>>a>>>|<cell|0.16s>>|<row|<cell|>|<\cell>
        <verbatim|rotl: <small|<math|\<forall\>>a.AVL
        a<math|\<rightarrow\>>Int<math|\<rightarrow\>>AVL (S (S
        a))<math|\<rightarrow\>><next-line> Choice (AVL (S (S a)), AVL (S (S
        (S a))))>>
      </cell>|<cell|0.03s>>|<row|<cell|>|<cell|<verbatim|ins:
      <small|<math|\<forall\>>a.Int<math|\<rightarrow\>>AVL
      a<math|\<rightarrow\>>Choice (AVL a, AVL (S
      a))>>>|<cell|0.41s>>|<row|<cell|>|<cell|<verbatim|extract:
      <small|<math|\<forall\>>a, b.Path b<math|\<rightarrow\>>Tree (b,
      a)<math|\<rightarrow\>>a>>>|<cell|0.06s>>|<row|<cell|>|<cell|<verbatim|run_state:
      <small|<math|\<forall\>>a, b.b<math|\<rightarrow\>>State (b,
      a)<math|\<rightarrow\>>(b, a)>>>|<cell|0.01s>>|<row|<cell|>|<cell|<verbatim|head:
      <small|<math|\<forall\>>a, b.List (a, S
      b)<math|\<rightarrow\>>a>>>|<cell|<math|\<infty\>>>>|<row|<\cell>
        examples from <cite|PointwiseGADTs> outside the scope of algorithm
        <math|\<cal-P\>>
      </cell>|<\cell>
        <verbatim|joint: <small|<math|\<forall\>>a.Split (a,
        a)<math|\<rightarrow\>>a>>
      </cell>|<cell|\<less\>0.01s>>|<row|<cell|>|<\cell>
        <verbatim|rotr: <small|<math|\<forall\>>a.Int<math|\<rightarrow\>>AVL
        a<math|\<rightarrow\>>AVL (S (S a))<math|\<rightarrow\>><next-line>
        Choice (AVL (S (S a)), AVL (S (S (S a))))>>
      </cell>|<cell|0.09s>>|<row|<cell|>|<\cell>
        <verbatim|delmin: <small|<math|\<forall\>>a.AVL (S
        a)<math|\<rightarrow\>><next-line> (Int, Choice (AVL a, AVL (S a)))>>
      </cell>|<cell|0.31s>>|<row|<cell|>|<\cell>
        <verbatim|fd_comp: <small|<math|\<forall\>>a, b, c.FunDesc (c,
        b)<math|\<rightarrow\>>FunDesc (b, a)<math|\<rightarrow\>> FunDesc
        (c, a)>>
      </cell>|<cell|0.2s*, 0.1s*>>|<row|<cell|>|<cell|<verbatim|zip1:
      <small|<math|\<forall\>>a, b.Zip1 (List b,
      a)<math|\<rightarrow\>>b<math|\<rightarrow\>>a>>>|<cell|0.08s>>|<row|<cell|>|<cell|<verbatim|leq:
      <small|<math|\<forall\>>a.Nat a<math|\<rightarrow\>>NatLeq (a,
      a)>>>|<cell|\<less\>0.01s**>>|<row|<cell|>|<cell|<verbatim|run_state:
      <small|<math|\<forall\>>a, b.b<math|\<rightarrow\>>State (b,
      a)<math|\<rightarrow\>>(b, a)>>>|<cell|0.03s>>|<row|<cell|<tabular|<tformat|<cwith|1|1|1|1|cell-valign|b>|<table|<row|<cell|run-time
      type>>|<row|<cell|representations>>>>>>|<\cell>
        <verbatim|eval: <small|<math|\<forall\>>a.Term
        a<math|\<rightarrow\>>a>>
      </cell>|<cell|0.06s>>|<row|<cell|>|<\cell>
        <verbatim|equal: <small|<math|\<forall\>>a,b.(Ty a, Ty
        b)<math|\<rightarrow\>>a<math|\<rightarrow\>>b<math|\<rightarrow\>>Bool>>
      </cell>|<cell|0.3s, 2.1s>>>>>

      * Slight meaning-preserving modification of test program

      ** Needs a non-default option <verbatim|-prefer_guess><label|Experiments>
    </big-table|Examples of types and inference times, plain GADTs>
  </float>

  Table <reference|ExperimentsNum> contains examples using numerical
  constraints and existential types. The examples are organized around
  several data structures: lists and arrays with length, binary numbers, AVL
  balanced search trees. We provide the inferred types in the hope that they
  are self-explanatory.<\float|float|t>
    <\big-table>
      \;

      <block|<tformat|<cwith|11|11|1|1|cell-vcorrect|n>|<cwith|11|11|1|1|cell-row-span|3>|<cwith|14|14|2|2|cell-row-span|1>|<cwith|14|14|1|1|cell-valign|t>|<cwith|14|14|1|1|cell-row-span|7>|<cwith|6|6|2|2|cell-hyphen|t>|<cwith|7|7|2|2|cell-hyphen|t>|<cwith|11|11|2|2|cell-hyphen|t>|<cwith|13|13|2|2|cell-hyphen|t>|<cwith|14|14|2|2|cell-hyphen|t>|<cwith|15|15|2|2|cell-hyphen|t>|<cwith|16|16|2|2|cell-hyphen|t>|<cwith|17|17|2|2|cell-hyphen|t>|<cwith|18|18|2|2|cell-hyphen|t>|<cwith|19|19|2|2|cell-hyphen|t>|<cwith|2|2|2|2|cell-width|2cm>|<cwith|2|2|2|2|cell-hmode|min>|<cwith|4|4|2|2|cell-hyphen|t>|<cwith|4|4|2|2|cell-width|2cm>|<cwith|4|4|2|2|cell-hmode|min>|<cwith|6|6|2|2|cell-width|2cm>|<cwith|6|6|2|2|cell-hmode|min>|<cwith|7|7|2|2|cell-width|2cm>|<cwith|7|7|2|2|cell-hmode|min>|<cwith|11|11|2|2|cell-width|2cm>|<cwith|11|11|2|2|cell-hmode|min>|<cwith|12|12|2|2|cell-hyphen|t>|<cwith|12|12|2|2|cell-width|2cm>|<cwith|12|12|2|2|cell-hmode|min>|<cwith|13|13|2|2|cell-width|2cm>|<cwith|13|13|2|2|cell-hmode|min>|<cwith|14|14|2|2|cell-width|2cm>|<cwith|14|14|2|2|cell-hmode|min>|<cwith|15|15|2|2|cell-width|2cm>|<cwith|15|15|2|2|cell-hmode|min>|<cwith|16|16|2|2|cell-width|2cm>|<cwith|16|16|2|2|cell-hmode|min>|<cwith|17|17|2|2|cell-width|2cm>|<cwith|17|17|2|2|cell-hmode|min>|<cwith|18|18|2|2|cell-width|2cm>|<cwith|18|18|2|2|cell-hmode|min>|<cwith|19|19|2|2|cell-width|2cm>|<cwith|19|19|2|2|cell-hmode|min>|<cwith|20|20|2|2|cell-hyphen|t>|<cwith|20|20|2|2|cell-width|2cm>|<cwith|20|20|2|2|cell-hmode|min>|<cwith|2|2|2|2|cell-hyphen|t>|<cwith|3|3|2|2|cell-hyphen|n>|<cwith|2|2|1|1|cell-hyphen|t>|<cwith|14|14|1|1|cell-hyphen|t>|<cwith|14|14|1|1|cell-width|8>|<cwith|14|14|1|1|cell-hmode|exact>|<cwith|2|2|1|1|cell-width|8>|<cwith|2|2|1|1|cell-hmode|exact>|<cwith|8|8|2|2|cell-hyphen|t>|<cwith|8|8|2|2|cell-width|20>|<cwith|8|8|2|2|cell-hmode|exact>|<cwith|9|9|2|2|cell-hyphen|t>|<cwith|9|9|2|2|cell-width|20>|<cwith|9|9|2|2|cell-hmode|exact>|<cwith|10|10|2|2|cell-hyphen|t>|<cwith|10|10|2|2|cell-width|20>|<cwith|10|10|2|2|cell-hmode|exact>|<cwith|2|2|1|1|cell-row-span|9>|<cwith|5|5|2|2|cell-width|20>|<cwith|5|5|2|2|cell-hmode|exact>|<cwith|5|5|2|2|cell-hyphen|t>|<table|<row|<cell|<em|Class
      of examples>>|<cell|<em|Function name: inferred type>>|<cell|<em|Inf.
      time>>>|<row|<\cell>
        lists with length and arrays with static bound checks
      </cell>|<\cell>
        <verbatim|head: <small|<math|\<forall\>>n,a[1<math|\<leqslant\>>n].List
        (a, n)<math|\<rightarrow\>>a>>
      </cell>|<cell|\<less\>0.01s>>|<row|<cell|>|<cell|<verbatim|append:
      <small|<math|\<forall\>>a,n,k.List (a, n)<math|\<rightarrow\>>List (a,
      k)<math|\<rightarrow\>>List(a, n+k)>>>|<cell|0.02s>>|<row|<cell|>|<\cell>
        <verbatim|flatten_pairs: <small|<math|\<forall\>>n, a. List ((a, a),
        n) <math|\<rightarrow\>><next-line> List (a, 2 n)>>
      </cell>|<cell|0.01s>>|<row|<cell|>|<\cell>
        <verbatim|flatten_quadrs: <small|<math|\<forall\>>n, a. List ((a, a,
        a, a), n) <math|\<rightarrow\>> List (a, 4 n)>>
      </cell>|<cell|0.06s>>|<row|<cell|>|<\cell>
        <verbatim|filter: <small|<math|\<forall\>>n, a. (a
        <math|\<rightarrow\>> Bool) <math|\<rightarrow\>> List (a, n)
        <math|\<rightarrow\>><next-line> <math|\<exists\>>k[0
        <math|\<leqslant\>> k <math|\<wedge\>> k <math|\<leqslant\>> n].List
        (a, k)>>
      </cell>|<cell|0.18s>>|<row|<cell|>|<\cell>
        <verbatim|zip: <small|<math|\<forall\>>a,b,n,k.(List (a,n), List
        (b,k))<math|\<rightarrow\>> <math|\<exists\>>i[i=min(n, k)].List
        ((a,b),i)>>
      </cell>|<cell|0.38s>>|<row|<cell|>|<\cell>
        <verbatim|bsearch2: <small|<math|\<forall\>>n, a[0
        <math|\<leqslant\>> n]. a <math|\<rightarrow\>> Array (a, n)
        <math|\<rightarrow\>><next-line> <math|\<exists\>>k[0
        <math|\<leqslant\>> k + 1 <math|\<wedge\>> k + 1 <math|\<leqslant\>>
        n].Num k>> \ <small|(uses assertion)>
      </cell>|<cell|1.39s>>|<row|<cell|>|<\cell>
        <verbatim|swap_interval: <small|<math|\<forall\>>i, j, k, n, a[1
        <math|\<leqslant\>> j <math|\<wedge\>> 0 <math|\<leqslant\>> n
        <math|\<wedge\>><next-line> 0 <math|\<leqslant\>> k <math|\<wedge\>>
        i + k <math|\<leqslant\>> j <math|\<wedge\>> i + n
        <math|\<leqslant\>> j]. Array (a, j) <math|\<rightarrow\>><next-line>
        Num n <math|\<rightarrow\>> Num k <math|\<rightarrow\>> Num i
        <math|\<rightarrow\>> ()>>
      </cell>|<cell|0.27s>>|<row|<cell|>|<\cell>
        <verbatim|matmul: <small|<math|\<forall\>>i, j, k, n[0
        <math|\<leqslant\>> n <math|\<wedge\>> 0 <math|\<leqslant\>> k
        <math|\<wedge\>> 0 <math|\<leqslant\>> j <math|\<wedge\>><next-line>
        j <math|\<leqslant\>> i]. Matrix (n,j) <math|\<rightarrow\>> Matrix
        (i,k) <math|\<rightarrow\>> Matrix (n,k)>>
      </cell>|<cell|0.34s>>|<row|<cell|binary numbers>|<\cell>
        <verbatim|plus: <small|<math|\<forall\>>n,k,i.Carry
        i<math|\<rightarrow\>>Binary k<math|\<rightarrow\>>Binary
        n<math|\<rightarrow\>>Binary (n+k+i)>>
      </cell>|<cell|0.66s>>|<row|<cell|>|<\cell>
        <verbatim|increment: <small|<math|\<forall\>>n.Binary
        n<math|\<rightarrow\>>Binary (n + 1)>>
      </cell>|<cell|0.01s>>|<row|<cell|>|<\cell>
        <verbatim|bitwise_or: <small|<math|\<forall\>>k, n. Binary k
        <math|\<rightarrow\>> Binary n <math|\<rightarrow\>><next-line>
        <math|\<exists\>>i[k <math|\<leqslant\>> i <math|\<wedge\>> n
        <math|\<leqslant\>> i <math|\<wedge\>> i <math|\<leqslant\>> n +
        k].Binary i>>
      </cell>|<cell|1.21s>>|<row|<\cell>
        AVL trees, imbalance of 2
      </cell>|<\cell>
        <verbatim|create: <small|<math|\<forall\>>k, n, a[0
        <math|\<leqslant\>> n <math|\<wedge\>> 0 <math|\<leqslant\>> k
        <math|\<wedge\>> n <math|\<leqslant\>> k + 2
        <math|\<wedge\>><next-line> k <math|\<leqslant\>> n + 2]. Avl (a, k)
        <math|\<rightarrow\>> a <math|\<rightarrow\>> Avl (a, n)
        <math|\<rightarrow\>><next-line> <math|\<exists\>>i[i=max (k + 1, n +
        1)].Avl (a, i)>>
      </cell>|<cell|0.09s>>|<row|<cell|>|<\cell>
        <verbatim|rotr: <small|<math|\<forall\>>k, n, a[0 <math|\<leqslant\>>
        n <math|\<wedge\>> n + 2 <math|\<leqslant\>> k <math|\<wedge\>> k
        <math|\<leqslant\>> n + 3]. Avl (a, k) <math|\<rightarrow\>> a
        <math|\<rightarrow\>> Avl (a, n) <math|\<rightarrow\>><next-line>
        <math|\<exists\>>n[k <math|\<leqslant\>> n <math|\<wedge\>> n
        <math|\<leqslant\>> k + 1].Avl (a, n)>>
      </cell>|<cell|1.07s>>|<row|<cell|>|<\cell>
        <verbatim|add: <small|<math|\<forall\>>n, a. a <math|\<rightarrow\>>
        Avl (a, n) <math|\<rightarrow\>> <math|\<exists\>>k[1
        <math|\<leqslant\>> k <math|\<wedge\>> n <math|\<leqslant\>> k
        <math|\<wedge\>> k <math|\<leqslant\>> n + 1].Avl (a, k)>>
      </cell>|<cell|0.69s>>|<row|<cell|>|<\cell>
        <verbatim|remove_min_binding: <small|<math|\<forall\>>n, a[1
        <math|\<leqslant\>> n]. Avl (a, n) <math|\<rightarrow\>>
        <math|\<exists\>>k[n <math|\<leqslant\>> k + 1 <math|\<wedge\>> k
        <math|\<leqslant\>> n <math|\<wedge\>> k + 2 <math|\<leqslant\>> 2
        n].Avl (a, k)>>
      </cell>|<cell|0.59s>>|<row|<cell|>|<\cell>
        <verbatim|merge: <small|<math|\<forall\>>k, n, a[n
        <math|\<leqslant\>> k + 2 <math|\<wedge\>> k <math|\<leqslant\>> n +
        2]. (Avl (a, n), Avl (a, k)) <math|\<rightarrow\>>
        <math|\<exists\>>i[n <math|\<leqslant\>> i <math|\<wedge\>> k
        <math|\<leqslant\>> i <math|\<wedge\>> i <math|\<leqslant\>> n + k
        <math|\<wedge\>> i<math|\<leqslant\>>max (k + 1, n + 1)].Avl (a, i)>>
      </cell>|<cell|0.93s>>|<row|<cell|>|<\cell>
        <verbatim|remove: <small|<math|\<forall\>>n, a. a
        <math|\<rightarrow\>> Avl (a, n) <math|\<rightarrow\>>
        <math|\<exists\>>k[n <math|\<leqslant\>> k + 1
        <math|\<wedge\>><next-line> 0 <math|\<leqslant\>> k <math|\<wedge\>>
        k <math|\<leqslant\>> n].Avl (a, k)>>
      </cell>|<cell|0.38s>>|<row|<cell|>|<\cell>
        Total time for <verbatim|add>, <verbatim|remove> and helper
        functions:
      </cell>|<cell|4.92s>>>>><label|ExperimentsNum>
    </big-table|Examples of types and inference times, with numerical
    constraints and existentials>
  </float>

  Table <reference|ExperimentsBounds> contains examples of static array (and
  matrix) bounds checking. These tests originally date back to the Hongwei
  Xi's DML system. They were selected, by <cite|DSolvePaper>, to demonstrate
  the abilities of the Liquid Types system inference implementation
  <name|DSolve>. The reported <name|DSolve> times come from
  <cite|DSolvePaper> and <cite|DSolveThesis>. The example <verbatim|isort>
  lists two times: the shorter time is inferred from a program without an
  unused nested definition of <verbatim|vecswap>. We extracted the
  corresponding computation as the example <verbatim|swap_interval> in Table
  <reference|ExperimentsNum>. The shorter time for the example
  <verbatim|simplex> corresponds to a variant where some helper functions are
  separated out as toplevel definitions, while the longer time is for a
  variant with a single toplevel definition. For the example program
  <verbatim|gauss> without assertions we again have two variants, but they
  both simplify the original example. They remove a redundant level of
  nesting in a helper, nested definition <verbatim|rowMax>. One of the
  variants requires passing a non-default option
  <verbatim|-prefer_bound_to_local> to guide inference, the other slightly
  generalizes the algorithm by passing a different matrix dimension in two
  places. Since our type system does not allow existential types as function
  arguments, for the FFT examples we introduce an explicit datatype
  <verbatim|Bounded>. The FFT example with assertion requires non-default
  option <verbatim|-same_with_assertions>. On the whole, we believe that the
  approach taken by <name|InvarGenT> shows promise in this comparison. It is
  clear that <name|InvarGenT> faces increasing difficulties when analysing
  more complex programs. We propose remedies to the issues encountered as
  future work.<\float|float|t>
    <\big-table>
      \;

      <block|<tformat|<cwith|1|1|2|2|cell-hyphen|t>|<cwith|1|1|3|3|cell-hyphen|t>|<table|<row|<cell|<em|Program>>|<\cell>
        <em|Inf. time>
      </cell>|<\cell>
        <em|Time from <cite|DSolvePaper>>
      </cell>>|<row|<cell|<verbatim|dotprod>>|<cell|0.05s>|<cell|0.31s>>|<row|<cell|<verbatim|bcopy>>|<cell|0.03s>|<cell|0.15s>>|<row|<cell|<verbatim|bsearch>>|<cell|0.07s>|<cell|0.46s>>|<row|<cell|<verbatim|queen>>|<cell|0.42s>|<cell|0.7s>>|<row|<cell|<verbatim|isort>>|<cell|0.3s,
      0.37s>|<cell|0.88s>>|<row|<cell|<verbatim|tower> no
      assertions>|<cell|0.84s>|<cell|<math|\<infty\>>>>|<row|<cell|<verbatim|tower>
      with assertion>|<cell|3.93s>|<cell|3.33s>>|<row|<cell|<verbatim|matmult>>|<cell|0.34s>|<cell|1.79s>>|<row|<cell|<verbatim|heapsort>>|<cell|2.34s>|<cell|0.53s>>|<row|<cell|<verbatim|fft>
      no assertions>|<cell|36.4s*>|<cell|?>>|<row|<cell|<verbatim|fft> with
      assertion>|<cell|37.5s*,**>|<cell|9.13s>>|<row|<cell|<verbatim|simplex>>|<cell|8.1s*,
      31.4s>|<cell|7.73s>>|<row|<cell|<verbatim|gauss> no
      assertions>|<cell|2.66s*, 1.02s*,***>|<cell|?>>|<row|<cell|<verbatim|gauss>
      with assertion>|<cell|2.72s>|<cell|3.17s>>>>>

      * Slight meaning-preserving modification of test program

      ** Needs a non-default option <verbatim|-same_with_assertions>

      *** Needs a non-default option <verbatim|-prefer_bound_to_local><label|ExperimentsBounds>
    </big-table|Examples of inference times, bound checking>
  </float>

  The code of examples from Tables <reference|Experiments>,
  <reference|ExperimentsNum> and <reference|ExperimentsBounds> can be found
  in Appendix <reference|ExamplesCode>.

  <section|<name|InvarGenT> Failure Cases><label|FailureCases>

  Type inference for the type system underlying <name|InvarGenT> is
  undecidable. Constraint abduction itself is not known to be decidable.
  Rather than trying to enumerate all possible answers, we devised constraint
  abduction algorithms that only consider answers of restricted forms. The
  <verbatim|vary> example from <cite|PracticalGADTsInfer> fails due to such
  limitation. However, the practical problems we encountered are not of such
  nature. Each subsection below describes a class of problematic cases,
  exhausting the types of inference failures we encountered. Near discuss the
  prospects of improving the situation.

  <subsection|The Need to Expand Pattern Variables>

  The one function from <cite|PracticalGADTsInfer> that needed modification
  to be type-inferred is <verbatim|fd_comp>. Take a look at the fragment of
  original definition that needed modification:

  <\code>
    let fd_comp = fun fd1 fd2 -\>

    \ \ let o = fun f g x -\> f (g x) in

    \ \ match fd1 with

    \ \ \ \ \| FDI -\> fd2

    \ \ \ \ \| FDC b -\> ...
  </code>

  The modified form:

  <\code>
    let fd_comp = fun fd1 fd2 -\><no-page-break>

    \ \ let o = fun f g x -\> f (g x) in<no-page-break>

    \ \ match fd1 with

    \ \ \ \ \| FDI -\>

    \ \ \ \ \ \ (match fd2 with \| FDI -\> fd2 \| FDC _ -\> fd2 \| FDG _ -\>
    fd2)

    \ \ \ \ \| FDC b -\> ...
  </code>

  Type inference needs to know the structure of both arguments to be able to
  infer the resulting type. If this problem proves cumbersome, we can devise
  heuristics for automatic expansion of pattern variables.

  <subsection|Constraints Shared by Constructors of a Datatype>

  The above problem is more pronounced in the numerical domain. Fortunately,
  here it can have a principled solution. Consider the following list
  appending example that does not type-check:

  <\code>
    let rec append =

    \ \ function LNil -\> (fun l -\> l)

    \ \ \ \ \| LCons (x, xs) -\> (fun l -\> LCons (x, append xs l))
  </code>

  We can mitigate the problem by expanding the pattern, as in Example
  <reference|BadFdComp>:

  <\code>
    let rec append =

    \ \ function LNil -\> (function LNil -\> LNil \| LCons (_,_) as l -\> l)

    \ \ \ \ \| LCons (x, xs) -\>

    \ \ \ \ \ \ (function LNil -\> LCons (x, append xs LNil)

    \ \ \ \ \ \ \ \ \| LCons (_,_) as l -\> LCons (x, append xs l))
  </code>

  But we can also provide the ``hidden'' information explicitly, by either a
  positive assertion, or a negative assertion as below:

  <\code>
    let rec append =

    \ \ function

    \ \ \ \ \| LNil -\>

    \ \ \ \ \ \ (function l when (length l + 1) \<= 0 -\> assert false \| l
    -\> l)

    \ \ \ \ \| LCons (x, xs) -\>

    \ \ \ \ \ \ (function l when (length l + 1) \<= 0 -\> assert false

    \ \ \ \ \ \ \| l -\> LCons (x, append xs l))
  </code>

  One can investigate a modification to the type system so that each datatype
  is associated with an invariant common to all constructors of the datatype.
  In case of lists, the shared invariant is that the length of a list is
  non-negative. In the modified type system, when it becomes determined that
  a pattern variable's type is a datatype, the corresponding invariant is
  made available for inference.

  <subsection|Negative Constraints in the Sort of Terms>

  <\example>
    Consider the following variant of the <verbatim|head> example from
    <cite|PracticalGADTsInfer>:

    <\code>
      datatype Z

      datatype S : type

      datatype List : type * num

      datacons LNil : <math|\<forall\>>a. List(a, Z)

      datacons LCons : <math|\<forall\>>a, b. a * List(a, b)
      <math|\<longrightarrow\>> List(a, S b)

      \;

      let head = function

      \ \ \| LCons (x, _) -\> x

      \ \ \| LNil -\> assert false
    </code>

    We introduced the assertion to disallow the overly general type
    <verbatim|<math|\<forall\>>a, b. List (a, b) <math|\<rightarrow\>> a>,
    which is the correct most general type for <verbatim|function LCons (x,
    _) -\> x>, because the type system does not enforce exhaustiveness of
    pattern matching. The above function has type
    <verbatim|<math|\<forall\>>a, b. List (a, S b) <math|\<rightarrow\>> a>,
    but type inference fails to find it. The problem stems from the inability
    to express disequations <math|t<rsub|1>\<neq\>t<rsub|2>> in the sort of
    terms as conjunctions of atoms. We already implemented a workaround in
    <name|InvarGenT> for the case of datatypes with only constant
    constructors.
  </example>

  <subsection|Insufficient Context to Infer Postconditions>

  <\example>
    In the following variant of the <verbatim|bsearch2> example it turns out
    to be too hard to infer the full postcondition.

    <\code>
      datatype Array : type * num

      external let array_make :

      \ \ <math|\<forall\>>n, a [0<math|\<leqslant\>>n]. Num n
      <math|\<rightarrow\>> a <math|\<rightarrow\>> Array (a, n) = "fun a b
      -\<gtr\> Array.make a b"

      external let array_get :

      <math|\<forall\>>n, k, a [0<math|\<leqslant\>>k <math|\<wedge\>>
      k+1<math|\<leqslant\>>n]. Array (a, n) <math|\<rightarrow\>> Num k
      <math|\<rightarrow\>> a =

      \ \ "fun a b -\<gtr\> Array.get a b"

      external let array_length :

      \ \ <math|\<forall\>>n, a [0<math|\<leqslant\>>n]. Array (a, n)
      <math|\<rightarrow\>> Num n = "fun a -\<gtr\> Array.length a"

      datatype LinOrder

      datacons LE : LinOrder

      datacons GT : LinOrder

      datacons EQ : LinOrder

      external let compare : <math|\<forall\>>a. a <math|\<rightarrow\>> a
      <math|\<rightarrow\>> LinOrder =

      \ \ "fun a b -\> let c = Pervasives.compare a b in

      \ \ \ \ \ \ \ \ \ \ \ \ \ \ if c \< 0 then LE else if c \> 0 then GT
      else EQ"

      external let equal : <math|\<forall\>>a. a <math|\<rightarrow\>> a
      <math|\<rightarrow\>> Bool = "fun a b -\<gtr\> a = b"

      external let div2 : <math|\<forall\>>n. Num (2 n) <math|\<rightarrow\>>
      Num n = "fun x -\<gtr\> x / 2"

      \;

      let bsearch key vec =<no-page-break>

      \ \ let rec look key vec lo hi =

      \ \ \ \ eif lo \<less\>= hi then

      \ \ \ \ \ \ \ \ let m = div2 (hi + lo) in

      \ \ \ \ \ \ \ \ let x = array_get vec m in

      \ \ \ \ \ \ \ \ ematch compare key x with

      \ \ \ \ \ \ \ \ \ \ \| LE -\> look key vec lo (m + (-1))

      \ \ \ \ \ \ \ \ \ \ \| GT -\> look key vec (m + 1) hi

      \ \ \ \ \ \ \ \ \ \ \| EQ -\> eif equal key x then m else -1

      \ \ \ \ else -1 in

      \ \ look key vec 0 (array_length vec + (-1))
    </code>

    \ We get the result type <verbatim|<math|\<exists\>>n[0
    <math|\<leqslant\>> n + 1].Num n> instead of
    <verbatim|<math|\<exists\>>k[k <math|\<leqslant\>> n <math|\<wedge\>> 0
    <math|\<leqslant\>> k + 1].Num k>. The inference of the intended type
    succeeds after we introduce an appropriate assertion, e.g.
    <verbatim|assert num -1 \<= hi>. Alternatively, we can include a use case
    for <verbatim|bsearch> where the full postcondition is required. It would
    be challenging to guess the assertion or use-case automatically.
  </example>

  <subsection|Insufficient Search>

  The need to pass options, in examples like the function <verbatim|leq> and
  the function <verbatim|fft> with assertions, stems from the failure of our
  search strategy for partial solutions across iterations of the main
  algorithm (rather than within a single call to abduction). Our search can
  recover from choices leading to contradictions in the following iteration,
  but not from choices leading down blind alleys. The problem might be more
  serious than it appears, because the heuristics (i.e. the default options)
  have been tuned in favor of our test suite. The solution to the problem is
  <em|beam search>: processing a fixed number of partial solutions, those
  with highest scores. A score measures heuristically the quality of a
  partial solution: penalizing complexity, rewarding locality of scope of
  parameters in an atom, etc.

  <subsection|Nested Definitions with Tied Postconditions>

  The variant of the <verbatim|gauss> program without assertions and with
  more nesting illustrates a problem with nested definitions introducing
  existential types. To arrive at the postcondition of the inner definition,
  we need to propagate information from the use-site of the outer definition.
  The postconditions are tied in the sense that the postcondition of the
  outer definition depends on the postcondition of the inner definition. We
  need to further investigate the issue to see what can be done.

  <chapter|Conclusions><label|ChapRelWork>

  In this chapter, we summarize our work in its broader context.

  <section|Related Work><label|SecRelWork>

  Perhaps Xi and Pfenning <cite|DML99> can be considered the earliest work on
  GADTs with invariants over a constraint domain; see Section
  <reference|DMLSection>. Its numerical constraint language contains <em|min>
  and <em|max> operations enabling e.g. a concise definition of AVL trees
  datatype as in Chapter <reference|Intro>. Its presentation of existential
  types is similar to ours. <cite|DML99> opted to automate existential type
  elimination by <em|A-translation>: <math|A<rsub|tr><around*|(|e<rsub|1>
  e<rsub|2>|)>=<around*|(|<text|<with|font-shape|condensed|<strong|let>>>
  x=A<rsub|tr><around*|(|e<rsub|1>|)> <text|<with|font-shape|condensed|<strong|in>>>
  <text|<with|font-shape|condensed|<strong|let>>>y=A<rsub|tr><around*|(|e<rsub|2>|)>
  <text|<with|font-shape|condensed|<strong|in>>> x y|)>>. Thanks to the
  modified <name|App> rule, performing A-translation during the normalization
  step <name|ExIntro> would make strictly more programs typeable in
  <math|MMG<rsub|\<exists\>><around*|(|X|)>>. The DML language from
  <cite|DML99> and its successor the ATS language do not perform type
  inference for recursive functions.

  We base our type system on the <math|HMG<around|(|X|)>> type system from
  Simonet and Pottier <cite|simonet-pottier-hmg-toplas>; see Section
  <reference|HMGSection>. In the tradition of the Milner-Mycroft type system
  (see Henglein <cite|Henglein93>), we drop the type specifications on
  recursive definitions from program terms. We also naturally restrict
  <math|HMG<around|(|X|)>> by limiting the user-specified and inferred
  invariant constraints to use conjunction as the only logical connective. We
  call the resulting type system <math|MMG<around*|(|X|)>>.

  The traditional framework for loop invariant generation of Cousot and
  Cousot <cite|Cousot77> inspired the iterative aspect of our solver.
  Mycroft's modification in <cite|Mycroft84> of algorithm <math|\<cal-W\>> to
  polymorphic recursion is also iterative, but it solves each recursive
  definition separately. We solve all nested definitions jointly in a single
  iteration.

  Initially we were only aware of the work in Knowles and Flanagan
  <cite|KnowlesF07> in the framework of <em|refinement types>, which applies
  Dijkstra's weakest precondition calculus to general refinement types. An
  interesting question is whether work similar to ours could be done by
  application of the weakest precondition calculus to the Hoare logic of
  Regis-Gianas and Pottier <cite|regis-gianas-pottier-08>, with the
  conditions inserted by type inference. Work on <em|Liquid Types> by Rondon,
  Kawaguchi and Jhala <cite|DSolvePaper> is a continuation of this approach
  closer to <name|InvarGenT> in that it does not use weakest precondition
  calculus explicitly; see Section <reference|LiquidSection>. <em|Abstract
  Refinement Types> by Vazou, Rondon and Jhala <cite|AbstractLiquid> is a
  continuation of Liquid Types in an interesting direction beyond the scope
  of current <name|InvarGenT>, opening an area for future work.

  Early work on applying abduction to type inference was an inspiration for
  us. The work by Sulzmann, Schrijvers and Stuckey <cite|AbdEADTs> and
  <cite|SulzmannAbdGADTs> closely relates to our work in their application of
  fully-maximal constraint abduction to GADTs type inference. But without
  annotations, this would ``throw the baby out with the bathwater'' by
  rejecting, as not having an intuitive type, for example any variant of
  <verbatim|eval> that computes for pairs: <verbatim|datacons Pair :
  <math|\<forall\>>a, b. Term a * Term b <math|\<longrightarrow\>> Term (a,
  b)>, <verbatim|datacons Fst : <math|\<forall\>>a, b. Term (a, b)
  <math|\<longrightarrow\>> Term a> and <verbatim|datacons Snd :
  <math|\<forall\>>a, b. Term (a, b) <math|\<longrightarrow\>> Term b>. The
  corresponding implications do not have fully maximal answers.
  <cite|AbdEADTs> and <cite|SulzmannAbdGADTs> use Herbrandization but solve
  the resulting constraints in the free algebra of terms, which we find
  problematic (see Section <reference|AbdUniVars>).

  Maher <cite|AbductionMaher> and Maher and Huang <cite|AbductionSolvMaher>
  introduce fully maximal constraint abduction; see Section
  <reference|HerbSection>. Our algorithm for injective terms with
  multi-sorted <em|alien subterms> is extensible to any constraint domain,
  given algorithms for the new domain, as long as the domains do not
  interact. Allowing the domains to interact would require considerable work,
  Baader and Schulz <cite|UnificationBaader> might be relevant. Abduction
  algorithm for the term algebra is provided in <cite|AbductionSolvMaher>,
  although further work driven by practical issues was needed. The linear
  arithmetic constraint abduction in Maher <cite|AbductionLinArithMaher>
  turned out not to be useful as a basis for an algorithm, our algorithm is
  novel. Maher <cite|HeytingAbdMaher> studies constraint domains where a
  (single) most general Simple Constraint Abduction answer exists, and gives
  a closed formula for SCA answer for the case of Boolean lattices.

  The work in Unno and Kobayashi <cite|InterpolationInfer> can be seen as
  extending Knowles and Flanagan <cite|KnowlesF07> with reasoning by Boolean
  cases. Their programming language and type system is in several ways less
  expressive than the ML language with polymorphic recursion and the full
  GADTs type system: no inductive types (and therefore no pattern matching),
  refinement predicates over integers only instead of over arbitrary domains
  including types.

  The recent <em|counterexample-guided abstraction refinement> work of Zhu
  and Jagannathan <cite|LightDML> (building on Kobayashi, Sato and Unno
  <cite|CEGAR>) pushes the envelope on both expressiveness and efficiency of
  inference of a refinement types based approach. It is further developed in
  Zhu, Nori and Jagannathan <cite|SpecLearnArrays>, the implementation is
  called <name|SpecLearn>. The work includes features beyond the scope of
  <name|InvarGenT>, for example effect tracking. Wrt. invariant inference,
  <name|SpecLearn> is similar to <name|InvarGenT> in that it starts with
  coarse invariants and refines them. However, rather than deriving the
  invariants mostly from the definitions they describe, <name|SpecLearn>
  generates test cases to refine the invariants. It still cannot solve, for
  example, the AVL trees inference task, without assertions in the source
  code. <name|SpecLearn> is slower than <name|InvarGenT>, at least for those
  of the tests reported in <cite|SpecLearnArrays> which belong to our test
  suite (Table <reference|ExperimentsBounds>).

  Schrijvers and Bruynooghe <cite|ADTReconstruct> shares the objective with
  our work: softening the learning curve and facilitating rapid prototyping.
  It reconstructs algebraic data types. An interesting direction of future
  work would be to reconstruct GADTs using the mechanisms already present in
  <name|InvarGenT>. In fact, <name|InvarGenT> reconstructs GADT constructors
  that serve as existential types.

  There is a surge of work on type inference for GADTs over the last decade,
  not contributing to our approach. Works such as Pottier and Régis-Gianas
  <cite|StratifiedGADTs> (older), Schrijvers, Peyton Jones, Sulzmann and
  Vytiniotis <cite|ComplDecidableGADTs>, Lin and Sheard <cite|PointwiseGADTs>
  (see also <cite|PracticalGADTsInfer>) modify the GADTs type system to make
  it more amenable to type inference (rejecting some reasonable programs as
  untypeable), and develop less declarative inference algorithms. These works
  also do not allow other domains (than the free term algebra) to express
  invariants, but Schrijvers, Peyton Jones, Sulzmann<localize| and
  >Vytiniotis <cite|OutsideIn> extends the <name|OutsideIn> system to
  arbitrary domains, see Section <reference|OutsideInSection>.
  <cite|PracticalGADTsInfer> and <cite|ADTReconstruct> stand out from our
  point of view as they handle type inference for polymorphic recursion:
  <cite|PracticalGADTsInfer> by iteration, see Section
  <reference|PointwiseSection>, and <cite|ADTReconstruct> using an algorithm
  by Henglein.

  <em|Inductive loop invariants> from the recent work Dillig, Dillig, Li and
  McMillan <cite|InductLoopInv> are closely related to fully maximal joint
  constraint abduction answers. However, <cite|InductLoopInv> employs a
  richer language of answers, including implications. We decided to limit
  solved forms, thus preconditions and postconditions, to conjunctions of
  atoms, to not tax with complexity both algorithms and users. Exploring
  <cite|InductLoopInv> in context of <name|InvarGenT> may be fruitful, by
  improving on <name|InvarGenT>'s abduction algorithm for linear arithmetic.
  One improvement is to perform quantifier elimination of universal variables
  (as in <cite|InductLoopInv>) when they cannot be substituted out. An
  improvement would be constraint abduction that generates <em|min> and
  <em|max> relations, which in current <name|InvarGenT> are only introduced
  by constraint generalization, but here <cite|InductLoopInv> does not help
  directly. <cite|InductLoopInv> would gain by incorporating ideas from our
  abduction algorithm.

  A related work by Deepak Kapur <cite|LoopQuantElim> is part of an
  interesting research program of Deepak Kapur and Enric Rodríguez Carbonell,
  for example <cite|LoopQuantElim>, <cite|RodriKapurICTAC04>,
  <cite|RodriKapurJSC07>. <cite|LoopQuantElim> generates loop invariants for
  imperative programs, by quantifier elimination. The variables that are not
  eliminated are the invariant parameters. In fact, the generated invariant
  is an abduction answer to the corresponding invariant inference constraint;
  compare how <name|InvarGenT> uses abduction to solve for preconditions. On
  the other hand, <cite|RodriKapurICTAC04> uses constraint generalization,
  iterating it until convergence. This is in effect how <name|InvarGenT>
  solves for postconditions. <cite|RodriKapurICTAC04> and
  <cite|RodriKapurJSC07> use polynomial equations as the language of
  invariants. This suggests, as future work, that including in
  <name|InvarGenT> a domain of polynomial equations.

  In case of the free algebra of terms, constraint generalization reduces to
  anti-unification. Anti-unification was first introduced by Plotkin
  <cite|AntiUnifPlotkin> and Reynolds <cite|AntiUnifReynolds>. Bulychev,
  Kostylev and Zakharov <cite|AntiUnifInv> is a recent work on
  anti-unification, with an example application to invariant inference. Our
  constraint generalization algorithm for linear inequalities has
  inspirations from Fukuda, Liebling<localize| and >Lütolf <cite|ConvexHull>.

  <section|Future Work><label|SecFutWork>

  Let us collect together proposed directions for future work.\ 

  <\itemize>
    <item>Implement beam search, where several answers are maintained and
    inferior answers (less general precondition, less specific
    postcondition), or answers with worse heuristic score (more complex,
    etc.), are dropped.

    <item>Address other issues discussed in Section <reference|FailureCases>:
    handle constraints shared by constructors of a datatype, handle use-site
    constraint propagation for nested definitions with tied postconditions.

    <item>Explore extending the <math|MMG<rsub|\<exists\>><around*|(|X|)>>
    type system to handle the use of invariants in arguments of higher-order
    functions, as in Rondon, Kawaguchi and Jhala <cite|DSolvePaper> and
    especially in abstract refinement types of Vazou, Rondon and Jhala
    <cite|AbstractLiquid>.

    <item>Work on error reporting for <name|InvarGenT>. Trace use-site
    location and program path location associated with implications,
    separately; see Zhu and Jagannathan <cite|LightDML>.

    <item>Integrate <name|InvarGenT> with an IDE.

    <item>Add more constraint domains to <name|InvarGenT>.
  </itemize>

  <section|Summary>

  We presented the type inference problem for <math|MMG<around*|(|X|)>>, a
  Milner-Mycroft style variant of the <math|HMG<around*|(|X|)>> type system
  without subtyping, as satisfaction of second order constraints over a
  multi-sorted domain. We provided a minimal extension
  <math|MMG<rsub|\<exists\>><around*|(|X|)>> of this type system that enables
  inference and easy use of existential types. Although insertions of
  introduction and elimination of existential types are not automated by the
  inference process, they are seamlessly integrated into expressions. We
  demonstrated several use cases using the <name|<name|InvarGenT>> system.

  \ Our Joint Constraint Abduction under Quantifier Prefix algorithm builds
  on the fully maximal Simple Constraint Abduction answers algorithm from
  Maher and Huang <cite|AbductionSolvMaher>, extended to guess equalities of
  parameters. Thanks to aggregating answers during JCA, it can find answers
  to some cases of joint problems where it would fail to solve some of the
  implications independently. Our SCA algorithm for linear arithmetic is
  novel.

  Consider programs not using the numerical sort. Undecidability of type
  inference for polymorphic recursion does not enforce an unbounded number of
  iteration steps of the main algorithm, because there can be infinitely many
  (maximally general but not fully maximal) term abduction answers. We
  encountered examples that need two iteration steps: one to generate a
  solution, and the following step to discard a wrong solution and accept the
  correct one. However, with numerical sort constraints, a series of programs
  can be written needing unbounded number of iteration steps.

  We define the Constraint Generalization problem. In case of free terms it
  is equivalent to anti-unification and in case of linear equations and
  inequalities it is equivalent to finding extended convex hull. In the
  former case, we extend the notion to Abductive Constraint Generalization,
  providing more specific answers. As we do for abduction, we provide a
  combination-of-domains algorithm for constraint generalization.

  We implemented an algorithm solving for predicate variables of the
  existential second order constraints generated for our type system. It uses
  abduction to find requirements on invariants, augmented by constraint
  generalization to find postconditions.

  The inference times in <name|InvarGenT> are sufficient for interactive use
  with toplevel definitions of small-to-moderate size.

  <\bibliography|bib|tm-plain|biblio.bib>
    <\bib-list|61>
      <bibitem*|1><label|bib-AssertionGraphs>Tilak<nbsp>Agerwala<localize|
      and >Jayadev<nbsp>Misra.<newblock> Assertion graphs for verifying and
      synthesizing programs.<newblock> <localize|Technical Report>,
      University of Texas Technical Report 83, 1978.<newblock>

      <bibitem*|2><label|bib-Cayenne>Lennart<nbsp>Augustsson.<newblock>
      Cayenne -- a language with dependent types.<newblock> <localize|In
      ><with|font-shape|italic|Proceedings of the Third ACM SIGPLAN
      International Conference on Functional Programming>, ICFP '98,
      <localize|pages >239--250. New York, NY, USA, 1998. ACM.<newblock>

      <bibitem*|3><label|bib-UnificationBaader>Franz<nbsp>Baader<localize|
      and >Klaus U.<nbsp>Schulz.<newblock> Unification in the union of
      disjoint equational theories: combining decision procedures.<newblock>
      <localize|In ><with|font-shape|italic|Proceedings of the 11th
      International Conference on Automated Deduction: Automated Deduction>,
      CADE-11, <localize|pages >50--65. London, UK, 1992.
      Springer-Verlag.<newblock>

      <bibitem*|4><label|bib-ArithQuantElim>Sergey<nbsp>Berezin,
      Vijay<nbsp>Ganesh<localize| and >David L.<nbsp>Dill.<newblock> An
      online proof-producing decision procedure for mixed-integer linear
      arithmetic.<newblock> <localize|In ><with|font-shape|italic|Proceedings
      of the 9th international conference on Tools and algorithms for the
      construction and analysis of systems>, TACAS'03, <localize|pages
      >521--536. Berlin, Heidelberg, 2003. Springer-Verlag.<newblock>

      <bibitem*|5><label|bib-IdrisCurrent>Edwin<nbsp>Brady.<newblock> Idris,
      a general-purpose dependently typed programming language: design and
      implementation.<newblock> <with|font-shape|italic|Journal of Functional
      Programming>, 23:552--593, 9 2013.<newblock>

      <bibitem*|6><label|bib-IdrisEarly>Edwin<nbsp>Brady, Christoph
      A.<nbsp>Herrmann<localize| and >Kevin<nbsp>Hammond.<newblock>
      Lightweight invariants with full dependent types.<newblock>
      <localize|In ><with|font-shape|italic|Proceedings of the Nineth
      Symposium on Trends in Functional Programming, TFP 2008, Nijmegen, The
      Netherlands, May 26-28, 2008.>, <localize|pages >161--177.
      2008.<newblock>

      <bibitem*|7><label|bib-AntiUnifInv>Peter<nbsp>Bulychev,
      Egor<nbsp>Kostylev<localize| and >Vladimir<nbsp>Zakharov.<newblock>
      Anti-unification algorithms and their applications in program
      analysis.<newblock> <localize|In >Amir<nbsp>Pnueli,
      Irina<nbsp>Virbitskaite<localize| and >Andrei<nbsp>Voronkov<localize|,
      editors>, <with|font-shape|italic|Perspectives of Systems Informatics>,
      <localize|volume> 5947<localize| of ><with|font-shape|italic|Lecture
      Notes in Computer Science>, <localize|pages >413--423. Springer Berlin
      / Heidelberg, 2010.<newblock>

      <bibitem*|8><label|bib-CheneyHinzePhantomTypes>James<nbsp>Cheney<localize|
      and >Ralf<nbsp>Hinze.<newblock> A lightweight implementation of
      generics and dynamics.<newblock> <localize|In
      ><with|font-shape|italic|Proceedings of the 2002 ACM SIGPLAN Workshop
      on Haskell>, Haskell '02, <localize|pages >90--104. New York, NY, USA,
      2002. ACM.<newblock>

      <bibitem*|9><label|bib-DisunificationComon>Hubert<nbsp>Comon.<newblock>
      Disunification: a survey.<newblock> <localize|In
      ><with|font-shape|italic|Computational Logic: Essays in Honor of Alan
      Robinson>, <localize|pages >322--359. MIT Press, 1991.<newblock>

      <bibitem*|10><label|bib-Cousot77>Patrick<nbsp>Cousot<localize| and
      >Radhia<nbsp>Cousot.<newblock> Automatic synthesis of optimal invariant
      assertions: mathematical foundations.<newblock>
      <with|font-shape|italic|SIGPLAN Notices>, 12(8):1--12, aug
      1977.<newblock>

      <bibitem*|11><label|bib-simulRigidEUnifUndec>Anatoli<nbsp>Degtyarev<localize|
      and >Andrei<nbsp>Voronkov.<newblock> Simultaneous rigid e-unification
      is undecidable.<newblock> <localize|In >Hans
      Kleine<nbsp>Büning<localize|, editor>, <with|font-shape|italic|Computer
      Science Logic>, <localize|volume> 1092<localize| of
      ><with|font-shape|italic|Lecture Notes in Computer Science>,
      <localize|pages >178--190. Springer Berlin Heidelberg, 1996.<newblock>

      <bibitem*|12><label|bib-InductLoopInv>Isil<nbsp>Dillig,
      Thomas<nbsp>Dillig, Boyang<nbsp>Li<localize| and
      >Ken<nbsp>McMillan.<newblock> Inductive invariant generation via
      abductive inference.<newblock> <localize|In
      ><with|font-shape|italic|Proceedings of the 2013 ACM SIGPLAN
      International Conference on Object Oriented Programming Systems
      Languages and Applications>, OOPSLA '13, <localize|pages >443--456. New
      York, NY, USA, 2013. ACM.<newblock>

      <bibitem*|13><label|bib-Flanagan06>Cormac<nbsp>Flanagan.<newblock>
      Hybrid type checking.<newblock> <with|font-shape|italic|SIGPLAN Not.>,
      41(1):245--256, jan 2006.<newblock>

      <bibitem*|14><label|bib-TypeQualifiers>Jeffrey
      Scott<nbsp>Foster.<newblock> <with|font-shape|italic|Type Qualifiers:
      Lightweight Specifications to Improve Software Quality>.<newblock> PhD
      dissertation, University of California, Berkeley, Department of
      Computer Science, December 2002.<newblock>

      <bibitem*|15><label|bib-RefinementFreemanPfenning>Tim<nbsp>Freeman<localize|
      and >Frank<nbsp>Pfenning.<newblock> Refinement types for ml (extended
      abstract).<newblock> <localize|In ><with|font-shape|italic|Proc. ACM
      SIGPLAN '91 Conf. on Programming Language Design and Implementation,
      Toronto, Ontario>, <localize|pages >268--277. ACM Press, June
      1991.<newblock>

      <bibitem*|16><label|bib-ConvexHull>Komei<nbsp>Fukuda, Thomas
      M.<nbsp>Liebling<localize| and >Christine<nbsp>Lütolf.<newblock>
      Extended convex hull.<newblock> <localize|In
      ><with|font-shape|italic|Proceedings of the 12th Canadian Conference on
      Computational Geometry, Fredericton, New Brunswick, Canada, August
      16-19, 2000>, <localize|volume><nbsp>20, <localize|pages >13--23.
      2001.<newblock>

      <bibitem*|17><label|bib-AbstractStateGraphs>Susanne<nbsp>Graf<localize|
      and >Hassen<nbsp>Saïdi.<newblock> Construction of abstract state graphs
      with pvs.<newblock> <localize|In ><with|font-shape|italic|Proceedings
      of the 9th International Conference on Computer Aided Verification>,
      CAV '97, <localize|pages >72--83. London, UK, UK, 1997.
      Springer-Verlag.<newblock>

      <bibitem*|18><label|bib-Henglein93>Fritz<nbsp>Henglein.<newblock> Type
      inference with polymorphic recursion.<newblock>
      <with|font-shape|italic|ACM Trans. Program. Lang. Syst.>,
      15(2):253--289, 1993.<newblock>

      <bibitem*|19><label|bib-LoopQuantElim>Deepak<nbsp>Kapur.<newblock>
      Automatically generating loop invariants using quantifier
      elimination.<newblock> <localize|In >Franz<nbsp>Baader,
      Peter<nbsp>Baumgartner, Robert<nbsp>Nieuwenhuis<localize| and
      >Andrei<nbsp>Voronkov<localize|, editors>,
      <with|font-shape|italic|Deduction and Applications>, <localize|number>
      05431<localize| in >Dagstuhl Seminar Proceedings, <localize|pages
      >10--10. Dagstuhl, Germany, 2006. Internationales Begegnungs- und
      Forschungszentrum für Informatik (IBFI), Schloss Dagstuhl,
      Germany.<newblock>

      <bibitem*|20><label|bib-KnowlesF07>Kenneth W.<nbsp>Knowles<localize|
      and >Cormac<nbsp>Flanagan.<newblock> Type reconstruction for general
      refinement types.<newblock> <localize|In
      ><with|font-shape|italic|ESOP>, <localize|volume> 4421<localize| of
      ><with|font-shape|italic|Lecture Notes in Computer Science>,
      <localize|pages >505--519. Springer, 2007.<newblock>

      <bibitem*|21><label|bib-CEGAR>Naoki<nbsp>Kobayashi,
      Ryosuke<nbsp>Sato<localize| and >Hiroshi<nbsp>Unno.<newblock> Predicate
      abstraction and cegar for higher-order model checking.<newblock>
      <localize|In ><with|font-shape|italic|ACM SIGPLAN Notices>,
      <localize|volume><nbsp>46, <localize|pages >222--233. ACM,
      2011.<newblock>

      <bibitem*|22><label|bib-PracticalGADTsInfer>Chuan-kai<nbsp>Lin.<newblock>
      <with|font-shape|italic|Practical type inference for the GADT type
      system>.<newblock> PhD dissertation, Portland State University,
      Department of Computer Science, 2010.<newblock>

      <bibitem*|23><label|bib-PointwiseGADTs>Chuan-kai<nbsp>Lin<localize| and
      >Tim<nbsp>Sheard.<newblock> Pointwise generalized algebraic data
      types.<newblock> <localize|In ><with|font-shape|italic|Proceedings of
      the 5th ACM SIGPLAN workshop on Types in language design and
      implementation>, TLDI '10, <localize|pages >51--62. New York, NY, USA,
      2010. ACM.<newblock>

      <bibitem*|24><label|bib-ExTyADTs>Konstantin<nbsp>Läufer<localize| and
      >Martin<nbsp>Odersky.<newblock> Polymorphic type inference and abstract
      data types.<newblock> <with|font-shape|italic|ACM Trans. Program. Lang.
      Syst.>, 16(5):1411--1430, sep 1994.<newblock>

      <bibitem*|25><label|bib-MaherParamSubstitutions>Michael<nbsp>Maher.<newblock>
      On parameterized substitutions.<newblock> <localize|Technical Report>,
      IBM Research Report RC 16042, 1990.<newblock>

      <bibitem*|26><label|bib-AbductionLinArithMaher>Michael<nbsp>Maher.<newblock>
      Abduction of linear arithmetic constraints.<newblock> <localize|In
      >Maurizio<nbsp>Gabbrielli<localize| and >Gopal<nbsp>Gupta<localize|,
      editors>, <with|font-shape|italic|Logic Programming>, <localize|volume>
      3668<localize| of ><with|font-shape|italic|Lecture Notes in Computer
      Science>, <localize|pages >174--188. Springer Berlin Heidelberg,
      2005.<newblock>

      <bibitem*|27><label|bib-AbductionMaher>Michael<nbsp>Maher.<newblock>
      Herbrand constraint abduction.<newblock> <localize|In
      ><with|font-shape|italic|LICS '05: Proceedings of the 20th Annual IEEE
      Symposium on Logic in Computer Science>, <localize|pages >397--406.
      Washington, DC, USA, 2005. IEEE Computer Society.<newblock>

      <bibitem*|28><label|bib-HeytingAbdMaher>Michael<nbsp>Maher.<newblock>
      Heyting domains for constraint abduction.<newblock> <localize|In
      ><with|font-shape|italic|Proceedings of the 19th Australian Joint
      Conference on Artificial Intelligence: Advances in Artificial
      Intelligence>, AI'06, <localize|pages >9--18. Berlin, Heidelberg, 2006.
      Springer-Verlag.<newblock>

      <bibitem*|29><label|bib-AbductionSolvMaher>Michael<nbsp>Maher<localize|
      and >Ge<nbsp>Huang.<newblock> On computing constraint abduction
      answers.<newblock> <localize|In >Iliano<nbsp>Cervesato,
      Helmut<nbsp>Veith<localize| and >Andrei<nbsp>Voronkov<localize|,
      editors>, <with|font-shape|italic|Logic for Programming, Artificial
      Intelligence, and Reasoning>, <localize|volume> 5330<localize| of
      ><with|font-shape|italic|Lecture Notes in Computer Science>,
      <localize|pages >421--435. Springer Berlin / Heidelberg,
      2008.<newblock>

      <bibitem*|30><label|bib-MartinLof>Per<nbsp>Martin-Löf.<newblock>
      Constructive mathematics and computer programming.<newblock>
      <localize|In ><with|font-shape|italic|Proc. Of a Discussion Meeting of
      the Royal Society of London on Mathematical Logic and Programming
      Languages>, <localize|pages >167--184. Upper Saddle River, NJ, USA,
      1985. Prentice-Hall, Inc.<newblock>

      <bibitem*|31><label|bib-AbductionSequents>Marta
      Cialdea<nbsp>Mayer<localize| and >Fiora<nbsp>Pirri.<newblock> First
      order abduction via tableau and sequent calculi.<newblock>
      <with|font-shape|italic|Logic Journal of IGPL>, 1(1):99--117,
      1993.<newblock>

      <bibitem*|32><label|bib-Milner78>Robin<nbsp>Milner.<newblock> A theory
      of type polymorphism in programming.<newblock>
      <with|font-shape|italic|Journal of Computer and System Sciences>,
      17:348--375, 1978.<newblock>

      <bibitem*|33><label|bib-Mycroft84>Alan<nbsp>Mycroft.<newblock>
      Polymorphic type schemes and recursive definitions.<newblock>
      <localize|In ><with|font-shape|italic|Proceedings of the 6th Colloquium
      on International Symposium on Programming>, <localize|pages >217--228.
      London, UK, UK, 1984. Springer-Verlag.<newblock>

      <bibitem*|34><label|bib-HMX>Martin<nbsp>Odersky,
      Martin<nbsp>Sulzmann<localize| and >Martin<nbsp>Wehr.<newblock> Type
      inference with constrained types.<newblock> <localize|In
      ><with|font-shape|italic|Fourth International Workshop on Foundations
      of Object-Oriented Programming (FOOL)>. 1997.<newblock>

      <bibitem*|35><label|bib-AntiUnifPlotkin>Gordon
      D.<nbsp>Plotkin.<newblock> A note on inductive
      generalization.<newblock> <with|font-shape|italic|Machine
      Intelligence>, 5:153--163, 1970.<newblock>

      <bibitem*|36><label|bib-StratifiedGADTs>François<nbsp>Pottier<localize|
      and >Yann<nbsp>Régis-Gianas.<newblock> Stratified type inference for
      generalized algebraic data types.<newblock> <localize|In
      ><with|font-shape|italic|Conference record of the 33rd ACM
      SIGPLAN-SIGACT symposium on Principles of programming languages>, POPL
      '06, <localize|pages >232--244. New York, NY, USA, 2006. ACM.<newblock>

      <bibitem*|37><label|bib-AntiUnifReynolds>John
      C.<nbsp>Reynolds.<newblock> Transformational systems and the algebraic
      structure of atomic formulas.<newblock> <localize|In
      >Bernard<nbsp>Meltzer<localize| and >Donald<nbsp>Michie<localize|,
      editors>, <with|font-shape|italic|Machine Intelligence>,
      <localize|volume><nbsp>5, <localize|pages >135--151. Edinburgh,
      Scotland, 1969. Edinburgh University Press.<newblock>

      <bibitem*|38><label|bib-RodriKapurICTAC04>Enric<nbsp>Rodrguez-Carbonell<localize|
      and >Deepak<nbsp>Kapur.<newblock> Program verification using automatic
      generation of invariants.<newblock> <localize|In
      ><with|font-shape|italic|1st International Colloquium on Theoretical
      Aspects of Computing (ICTAC'04)>, <localize|volume> 3407<localize| of
      ><with|font-shape|italic|Lecture Notes in Computer Science>,
      <localize|pages >325--340. Springer-Verlag, 2005.<newblock>

      <bibitem*|39><label|bib-RodriKapurJSC07>Enric<nbsp>Rodriguez-Carbonell<localize|
      and >Deepak<nbsp>Kapur.<newblock> Generating all polynomial invariants
      in simple loops.<newblock> <with|font-shape|italic|Journal of Symbolic
      Computation>, 42(4):0, 2007.<newblock>

      <bibitem*|40><label|bib-DSolveThesis>Patrick<nbsp>Rondon.<newblock>
      <with|font-shape|italic|Liquid Types>.<newblock> PhD dissertation,
      University of California, San Diego, Department of Computer Science,
      2012.<newblock>

      <bibitem*|41><label|bib-DSolvePaper>Patrick Maxim<nbsp>Rondon,
      Ming<nbsp>Kawaguchi<localize| and >Ranjit<nbsp>Jhala.<newblock> Liquid
      types.<newblock> <localize|In ><with|font-shape|italic|Proceedings of
      the ACM SIGPLAN 2008 Conference on Programming Language Design and
      Implementation, Tucson, AZ, USA, June 7-13, 2008>, <localize|pages
      >159--169. 2008.<newblock>

      <bibitem*|42><label|bib-DSolveTechRep>Patrick Maxim<nbsp>Rondon,
      Ming<nbsp>Kawaguchi<localize| and >Ranjit<nbsp>Jhala.<newblock> Liquid
      types.<newblock> <localize|Technical Report>, 2008.<newblock>

      <bibitem*|43><label|bib-regis-gianas-pottier-08>Yann<nbsp>Régis-Gianas<localize|
      and >François<nbsp>Pottier.<newblock> A Hoare logic for call-by-value
      functional programs.<newblock> <localize|In
      ><with|font-shape|italic|Proceedings of the Ninth International
      Conference on Mathematics of Program Construction (MPC'08)>,
      <localize|volume> 5133<localize| of ><with|font-shape|italic|Lecture
      Notes in Computer Science>, <localize|pages >305--335. Springer, JUL
      2008.<newblock>

      <bibitem*|44><label|bib-ADTReconstruct>Tom<nbsp>Schrijvers<localize|
      and >Maurice<nbsp>Bruynooghe.<newblock> Polymorphic algebraic data type
      reconstruction.<newblock> <localize|In
      ><with|font-shape|italic|Proceedings of the 8th International ACM
      SIGPLAN Conference on Principles and Practice of Declarative
      Programming, July 10-12, 2006, Venice, Italy>, <localize|pages >85--96.
      2006.<newblock>

      <bibitem*|45><label|bib-ComplDecidableGADTs>Tom<nbsp>Schrijvers, Simon
      Peyton<nbsp>Jones, Martin<nbsp>Sulzmann<localize| and
      >Dimitrios<nbsp>Vytiniotis.<newblock> Complete and decidable type
      inference for gadts.<newblock> <localize|In
      ><with|font-shape|italic|Proceedings of the 14th ACM SIGPLAN
      international conference on Functional programming>, ICFP '09,
      <localize|pages >341--352. New York, NY, USA, 2009. ACM.<newblock>

      <bibitem*|46><label|bib-Sheard04>Tim<nbsp>Sheard.<newblock> Languages
      of the future.<newblock> <localize|In ><with|font-shape|italic|In
      OOPSLA '04: Companion to the 19th annual ACM SIGPLAN conference on
      Object-oriented programming systems, languages, and applications>,
      <localize|pages >116--119. ACM Press, 2004.<newblock>

      <bibitem*|47><label|bib-simonet-pottier-hmg-toplas>Vincent<nbsp>Simonet<localize|
      and >François<nbsp>Pottier.<newblock> A constraint-based approach to
      guarded algebraic data types.<newblock> <with|font-shape|italic|ACM
      Transactions on Programming Languages and Systems>, 29(1), JAN
      2007.<newblock>

      <bibitem*|48><label|bib-SulzmannAbdGADTs>Martin<nbsp>Sulzmann,
      Tom<nbsp>Schrijvers<localize| and >Peter J.<nbsp>Stuckey.<newblock>
      Type inference for GADTs via Herbrand constraint abduction.<newblock>
      Manuscript, July 2006.<newblock>

      <bibitem*|49><label|bib-AbdEADTs>Martin<nbsp>Sulzmann,
      Tom<nbsp>Schrijvers<localize| and >Peter J.<nbsp>Stuckey.<newblock>
      Type inference via constraint abduction for EADTs.<newblock>
      Manuscript, April 2006.<newblock>

      <bibitem*|50><label|bib-SulzmannAbdGADTsRep>Martin<nbsp>Sulzmann,
      Tom<nbsp>Schrijvers<localize| and >Peter J.<nbsp>Stuckey.<newblock>
      Type inference for GADTs via Herbrand constraint abduction.<newblock>
      <localize|Technical Report>, K. U. Leuven Dept. of Computer Science,
      2008.<newblock> Report CW 507.<newblock>

      <bibitem*|51><label|bib-InterpolationInfer>Hiroshi<nbsp>Unno<localize|
      and >Naoki<nbsp>Kobayashi.<newblock> Dependent type inference with
      interpolants.<newblock> <localize|In
      ><with|font-shape|italic|Proceedings of the 11th ACM SIGPLAN conference
      on Principles and practice of declarative programming>, PPDP '09,
      <localize|pages >277--288. New York, NY, USA, 2009. ACM.<newblock>

      <bibitem*|52><label|bib-AbstractLiquid>Niki<nbsp>Vazou, Patrick
      Maxim<nbsp>Rondon<localize| and >Ranjit<nbsp>Jhala.<newblock> Abstract
      refinement types.<newblock> <localize|In
      ><with|font-shape|italic|Programming Languages and Systems - 22nd
      European Symposium on Programming, ESOP 2013, Held as Part of the
      European Joint Conferences on Theory and Practice of Software, ETAPS
      2013, Rome, Italy, March 16-24, 2013. Proceedings>, <localize|pages
      >209--228. 2013.<newblock>

      <bibitem*|53><label|bib-OutsideIn>Dimitrios<nbsp>Vytiniotis, Simon L.
      Peyton<nbsp>Jones, Tom<nbsp>Schrijvers<localize| and
      >Martin<nbsp>Sulzmann.<newblock> Outsidein(x) modular type inference
      with local assumptions.<newblock> <with|font-shape|italic|J. Funct.
      Program.>, 21(4-5):333--412, 2011.<newblock>

      <bibitem*|54><label|bib-DMLThesis>Hongwei<nbsp>Xi.<newblock>
      <with|font-shape|italic|Dependent Types in Practical
      Programming>.<newblock> <localize|PhD thesis>, Department of
      Mathematical Sciences, Carnegie Mellon University, December
      1998.<newblock>

      <bibitem*|55><label|bib-XiGRDTs>Hongwei<nbsp>Xi,
      Chiyan<nbsp>Chen<localize| and >Gang<nbsp>Chen.<newblock> Guarded
      recursive datatype constructors.<newblock> <localize|In
      ><with|font-shape|italic|Proceedings of the 30th ACM SIGPLAN-SIGACT
      Symposium on Principles of Programming Languages>, POPL '03,
      <localize|pages >224--235. New York, NY, USA, 2003. ACM.<newblock>

      <bibitem*|56><label|bib-DMLArrays>Hongwei<nbsp>Xi<localize| and
      >Frank<nbsp>Pfenning.<newblock> Eliminating array bound checking
      through dependent types.<newblock> <localize|In
      ><with|font-shape|italic|Proceedings of the ACM SIGPLAN 1998 Conference
      on Programming Language Design and Implementation>, PLDI '98,
      <localize|pages >249--257. New York, NY, USA, 1998. ACM.<newblock>

      <bibitem*|57><label|bib-DML99>Hongwei<nbsp>Xi<localize| and
      >Frank<nbsp>Pfenning.<newblock> Dependent types in practical
      programming.<newblock> <localize|In
      ><with|font-shape|italic|Proceedings of the 26th ACM SIGPLAN Symposium
      on Principles of Programming Languages>, <localize|pages >214--227. San
      Antonio, January 1999.<newblock>

      <bibitem*|58><label|bib-IndexedTypes>Christoph<nbsp>Zenger.<newblock>
      Indexed types.<newblock> <with|font-shape|italic|Theor. Comput. Sci.>,
      187(1-2):147--165, nov 1997.<newblock>

      <bibitem*|59><label|bib-LightDML>He<nbsp>Zhu<localize| and
      >Suresh<nbsp>Jagannathan.<newblock> Compositional and lightweight
      dependent type inference for ml.<newblock> <localize|In
      >Roberto<nbsp>Giacobazzi, Josh<nbsp>Berdine<localize| and
      >Isabella<nbsp>Mastroeni<localize|, editors>,
      <with|font-shape|italic|Verification, Model Checking, and Abstract
      Interpretation>, <localize|volume> 7737<localize| of
      ><with|font-shape|italic|Lecture Notes in Computer Science>,
      <localize|pages >295--314. Springer, 2013.<newblock>

      <bibitem*|60><label|bib-SpecLearnArrays>He<nbsp>Zhu, Aditya
      V.<nbsp>Nori<localize| and >Suresh<nbsp>Jagannathan.<newblock>
      Dependent array type inference from tests.<newblock> <localize|In
      >Deepak<nbsp>D'Souza, Akash<nbsp>Lal<localize| and >Kim
      Guldstrand<nbsp>Larsen<localize|, editors>,
      <with|font-shape|italic|VMCAI '15: Verification, Model Checking and
      Abstract Interpretation>, <localize|volume> 8931<localize| of
      ><with|font-shape|italic|Lecture Notes in Computer Science>,
      <localize|pages >412--430. Springer, January 2015.<newblock>

      <bibitem*|61><label|bib-AntiUnifAlg>Bjarte M.<nbsp>Østvold.<newblock> A
      functional reconstruction of anti-unification.<newblock>
      <localize|Technical Report>, Norwegian Computing Center, Oslo, Norway,
      2004.<newblock>
    </bib-list>
  </bibliography>

  <appendix|Proofs><label|ChapProofs>

  <section|The Type System>

  <subsection|The Logic of Constraints>

  We work with a first order language <math|\<cal-L\><rsub|1>> interpreted in
  a model <math|\<cal-M\>>, the language of constraints for our type
  inference problem. We assume that the logic is multi-sorted, but the sorts
  are combined only via a sort of finite trees, whose leaves can belong to
  other sorts. I.e., there is a single sort <math|s<rsub|type>> whose terms
  can contain subterms from other sorts and for any its terms
  \ <math|C\<Rightarrow\>f<around*|(|<wide|s<rsub|i>|\<bar\>>|)><wide|=|\<dot\>>g<around*|(|<wide|t<rsub|i>|\<bar\>>|)>>
  implies <math|f=g> and <math|C\<Rightarrow\>\<wedge\><rsub|i>s<rsub|i><wide|=|\<dot\>>t<rsub|i>>.
  The sorts <math|\<cal-L\><rsub|s>,\<cal-M\><rsub|s>> for
  <math|s\<neq\>s<rsub|type>> are single-sorted logics and
  <math|\<cal-L\><rsub|1>=<wide|\<cup\>|\<dot\>><rsub|s>\<cal-L\><rsub|s>>.

  Let <math|\<rho\>> be an interpretation of types, that is an assignment of
  elements of <math|\<cal-M\>> to variables in the corresponding sort,
  extended homomorphically to terms in the standard way. In the main text, we
  used <math|R> rather than <math|\<rho\>> to avoid unnecessary formality.
  For <math|\<Phi\>\<in\>\<cal-L\><rsub|1>>, let
  <math|\<cal-M\>,\<rho\>\<vDash\>\<Phi\>> denote the interpretation of a
  formula <math|\<Phi\>> in the model <math|\<cal-M\>> under the
  interpretation <math|\<rho\>>, in the standard way, for example
  <math|\<cal-M\>,\<rho\>\<vDash\>\<pi\><around*|(|t|)>> if and only if
  <math|\<pi\><around*|(|\<rho\><around*|(|t|)>|)>> holds in
  <math|\<cal-M\>>, where predicate symbol <math|\<pi\>> in
  <math|\<cal-L\><rsub|1>> corresponds to predicate <math|\<pi\>> in
  <math|\<cal-M\>>, etc.

  Of the model <math|\<cal-M\>> of <math|\<cal-L\><rsub|1>> we require the
  following. For the sort of types <math|s<rsub|type>>:

  <\enumerate>
    <item><em|Type conservation.> For any function symbols <math|f,g> such
    that <math|f\<neq\>g>, and arbitrary <math|<wide|s|\<bar\>>,<wide|t|\<bar\>>>,
    there is no interpretation <math|\<rho\>> such that
    <math|\<cal-M\>,\<rho\>\<vDash\>f<around|(|<wide|s|\<bar\>>|)><wide|=|\<dot\>>g<around|(|<wide|t|\<bar\>>|)>>.

    <item><em|Free generation.> For any <math|f\<in\>{\<rightarrow\>}\<cup\><wide|\<varepsilon\>|\<bar\>>>
    and arbitrary <math|<wide|s<rsub|i>|\<bar\>><rsub|1\<leqslant\>i\<leqslant\>ar<around|(|f|)>>,<wide|t<rsub|i>|\<bar\>><rsub|1\<leqslant\>i\<leqslant\>ar<around|(|f|)>>>,
    for any interpretation <math|\<rho\>>, if
    <math|\<cal-M\>,\<rho\>\<vDash\>f<around|(|<wide|s|\<bar\>>|)><wide|=|\<dot\>>f<around|(|<wide|t|\<bar\>>|)>>,
    then <math|\<cal-M\>,\<rho\>\<vDash\>\<wedge\><rsub|1\<leqslant\>i\<leqslant\>ar<around|(|f|)>>s<rsub|i><wide|=|\<dot\>>t<rsub|i>>.
  </enumerate>

  and every sort is nonempty.

  Let <math|\<cal-L\>> be <math|\<cal-L\><rsub|1>> with: a set of unary
  predicates <math|\<chi\><around|(|\<cdummy\>|)>>, which stand for
  invariants of recursive definitions in the constraints we will derive for
  type inference problems. And a set of binary predicates
  <math|\<chi\><rsub|K><around|(|\<cdummy\>,<no-break>\<cdot\>|)>>, which
  will be put as constraints of data constructors <math|K> when we introduce
  inferred existential types. We call <math|\<chi\>> and
  <math|\<chi\><rsub|K>> <em|predicate variables>. Let
  <math|PV<rsup|1><around|(|\<cdummy\>|)>>, resp.
  <math|PV<rsup|2><around|(|\<cdummy\>|)>> be the set of unary, resp. binary
  predicate variables in any expression, and
  <math|PV<around*|(|\<Phi\>|)>=PV<rsup|1><around*|(|\<Phi\>|)>\<cup\>PV<rsup|2><around*|(|\<Phi\>|)>>.
  We define <em|solved form formulas> to be existentially quantified
  conjunctions of atoms <math|\<exists\><wide|\<alpha\>|\<bar\>>.A> without
  predicate variables. Let <math|\<delta\>,\<delta\><rprime|'>> be fixed
  variables of sort <math|s<rsub|type>>.

  <\definition>
    <label|InterprPredVars>For a formula <math|\<Phi\>>, let
    <math|<wide|\<chi\>|\<bar\>>=PV<rsup|1><around*|(|\<Phi\>|)>>, resp.
    <math|<wide|\<chi\><rsub|K>|\<bar\>>=PV<rsup|2><around*|(|\<Phi\>|)>>,
    and let <with|mode|math|<wide|\<chi\><around|(|\<tau\><rsub|\<chi\>,k>|)>|\<bar\>>>,
    resp. <math|<wide|\<chi\><rsub|K><around|(|\<tau\><rsub|K,k>,\<tau\><rsub|K,k><rprime|'>|)>|\<bar\>>>
    be all occurrences of <math|\<chi\>>, resp. <math|\<chi\><rsub|K>> in
    <math|\<Phi\>>. We call an assignment
    <math|\<cal-I\>=<around*|[|<wide|\<chi\>|\<bar\>>\<assign\><wide|\<exists\><wide|\<alpha\>|\<bar\>><rsub|\<chi\>>.F<rsub|\<chi\>>|\<bar\>>;<wide|\<chi\><rsub|K>|\<bar\>>\<assign\><wide|\<exists\><wide|\<alpha\>|\<bar\>><rsub|K>.F<rsub|K>|\<bar\>>|]>>
    an <em|interpretation of predicate variables for <math|\<Phi\>>> when

    <\enumerate>
      <item><math|<wide|\<exists\><wide|\<alpha\>|\<bar\>><rsub|i>.F<rsub|i>|\<bar\>><wide|\<exists\><wide|\<alpha\>|\<bar\>><rsub|j>.F<rsub|j>|\<bar\>>>
      are solved form formulas,

      <item><math|\<delta\><wide|\<alpha\>|\<bar\>><rsub|\<chi\>>#FV<around*|(|\<wedge\><rsub|k>\<tau\><rsub|\<chi\>,k>|)>>
      and <math|\<delta\>\<delta\><rprime|'><wide|\<alpha\>|\<bar\>><rsub|K>#FV<around*|(|\<wedge\><rsub|k>\<tau\><rsub|K,k>\<wedge\><rsub|k>\<tau\><rsub|K,k><rprime|'>|)>>,

      <item>for every variable <math|\<beta\>\<in\>FV<around*|(|F<rsub|\<chi\>>|)>\\\<delta\><wide|\<alpha\>|\<bar\>><rsub|\<chi\>>>,
      there is a quantifier that binds <math|\<beta\>> at every position of
      <math|\<chi\><around|(|\<tau\><rsub|\<chi\>,k>|)>> in <math|\<Phi\>>,

      <item><math|FV<around*|(|F<rsub|K>|)>\<subseteq\>\<delta\>\<delta\><rprime|'><wide|\<alpha\>|\<bar\>><rsub|K>>.
    </enumerate>
  </definition>

  For an interpretation of predicate variables
  <math|\<cal-I\>=<around*|[|<wide|\<chi\>|\<bar\>>\<assign\><wide|\<exists\><wide|\<alpha\>|\<bar\>><rsub|\<chi\>>.F<rsub|\<chi\>>|\<bar\>>;<wide|\<chi\><rsub|K>|\<bar\>>\<assign\><wide|\<exists\><wide|\<alpha\>|\<bar\>><rsub|K>.F<rsub|K>|\<bar\>>|]>>,
  define the corresponding substitution of predicate variables in a formula
  <math|\<Phi\>> by:

  <\eqnarray*>
    <tformat|<table|<row|<cell|\<cal-I\><around*|(|\<chi\><around*|(|\<tau\><rsub|\<chi\>>|)>|)>>|<cell|=>|<cell|\<exists\><wide|\<alpha\>|\<bar\>><rsub|\<chi\>>.F<rsub|\<chi\>><around*|[|\<delta\>\<assign\>\<tau\><rsub|\<chi\>>|]>>>|<row|<cell|\<cal-I\><around*|(|\<chi\><rsub|K><around*|(|\<tau\><rsub|\<chi\>>,\<tau\><rsub|\<chi\>><rprime|'>|)>|)>>|<cell|=>|<cell|\<exists\><wide|\<alpha\>|\<bar\>><rsub|\<chi\>>.F<rsub|\<chi\>><around*|[|\<delta\>\<assign\>\<tau\><rsub|\<chi\>>;\<delta\><rprime|'>\<assign\>\<tau\><rsub|\<chi\>><rprime|'>|]>>>|<row|<cell|\<cal-I\><around*|(|a|)>>|<cell|=>|<cell|a<with|mode|text|
    \ for atom >a\<in\>\<cal-L\><rsub|1>>>|<row|<cell|\<cal-I\><around*|(|\<cal-Q\>.\<Phi\>|)>>|<cell|=>|<cell|\<cal-Q\>.\<cal-I\><around*|(|\<Phi\>|)><with|mode|text|
    \ for any quantifier prefix >\<cal-Q\>>>|<row|<cell|\<cal-I\><around*|(|\<Phi\><rsub|1>\<odot\>\<Phi\><rsub|2>|)>>|<cell|=>|<cell|\<cal-I\><around*|(|\<Phi\><rsub|1>|)>\<odot\>\<cal-I\><around*|(|\<Phi\><rsub|2>|)><with|mode|text|
    \ for any logical connective >\<odot\>>>>>
  </eqnarray*>

  Define a statement <math|\<cal-M\>,\<cal-I\>,\<rho\>\<vDash\>\<Phi\>> by:
  <math|\<cal-I\>> is an interpretation of predicate variables for
  <math|\<Phi\>>, <math|\<rho\>> is an interpretation of types, and
  <math|\<cal-M\>,\<rho\>\<vDash\>\<cal-I\><around*|(|\<Phi\>|)>>. Define
  <math|\<cal-M\>,\<cal-I\>\<vDash\>\<Phi\>> as: for all interpretations of
  types <math|\<rho\>>, <math|\<cal-M\>,\<cal-I\>,\<rho\>\<vDash\>\<Phi\>>.
  Define <math|\<cal-M\>\<vDash\>\<Phi\>> as: for all interpretations of
  predicate variables <math|\<cal-I\>> for <math|\<Phi\>>,
  <math|\<cal-M\>,\<cal-I\>\<vDash\>\<Phi\>>. Sometimes we write
  <math|\<cal-I\>\<vDash\>\<Phi\>>, resp. <math|\<vDash\>\<Phi\>>, instead of
  <math|\<cal-M\>,\<cal-I\>\<vDash\>\<Phi\>>, resp.
  <math|\<cal-M\>\<vDash\>\<Phi\>>, since the model is fixed. We write
  <math|\<cal-I\>,C\<vDash\>\<Phi\>>, resp. <math|C\<vDash\>\<Phi\>>, for
  <math|\<cal-I\>\<vDash\>C\<Rightarrow\>\<Phi\>>, resp.
  <math|\<vDash\>C\<Rightarrow\>\<Phi\>>.

  We say that a formula <math|\<Phi\>> is <em|satisfiable>, if and only if
  there exists an interpretation of predicate variables <math|\<cal-I\>> for
  <math|\<Phi\>>, such that <math|\<cal-I\>\<vDash\>\<exists\>FV<around*|(|\<Phi\>|)>.\<Phi\>>.
  As seen above, we extend the notion of substitution to handle predicate
  variable atoms, where the replacement of each occurrence of a variable
  depends on the argument of that variable. For interpretations of predicate
  variables <math|\<cal-I\><rsub|1>,\<cal-I\><rsub|2>> with disjoint domains,
  we write their composition <math|\<cal-I\><rsub|1>\<cal-I\><rsub|2><around*|(|\<cdummy\>|)>=\<cal-I\><rsub|1><around*|(|\<cal-I\><rsub|2><around*|(|\<cdummy\>|)>|)>>.

  Above we in effect introduce a Henkin semantics for existential second
  order logic, tailored to our needs of invariant and postcondition
  inference.

  <subsection|The GADT Type System><label|GADTProofs>

  Let <math|D\<vDash\>C> mean here <math|\<cal-M\>\<vDash\>D\<Rightarrow\>C>.
  Set <math|\<Delta\>\<assign\>\<exists\><wide|\<beta\>|\<bar\>><around|[|D|]>.\<Gamma\>>
  and <math|\<Delta\><rprime|'>\<assign\>\<exists\><wide|\<beta\>|\<bar\>><rprime|'><around|[|D<rprime|'>|]>.\<Gamma\><rprime|'>>
  such that <math|<wide|\<beta\>|\<bar\>>#FV<around|(|\<Gamma\><rprime|'>|)>>,
  <math|<wide|\<beta\>|\<bar\>><rprime|'>#FV<around|(|\<Delta\>|)>> and
  <math|<wide|\<beta\>|\<bar\>><rprime|'>#C>. Let
  <math|\<Delta\><rprime|'>\<leqslant\>\<Delta\>> denote
  <math|D<rprime|'>\<Rightarrow\>\<exists\><wide|\<beta\>|\<bar\>>.<around*|(|D\<wedge\><rsub|x\<in\>Dom<around|(|\<Gamma\>|)>>\<Gamma\><around|(|x|)><wide|=|\<dot\>>\<Gamma\><rprime|'><around|(|x|)>|)>>
  when <math|Dom<around|(|\<Gamma\>|)>=Dom<around|(|\<Gamma\><rprime|'>|)>>,
  and otherwise a falsehood (compare lemma 3.5 of
  <cite|simonet-pottier-hmg-toplas>). Let
  <math|\<Delta\>\<times\>\<Delta\><rprime|'>> denote
  <math|\<exists\><wide|\<beta\>|\<bar\>><wide|\<beta\><rprime|'>|\<bar\>><around|[|D\<wedge\>D<rprime|'>|]>.\<Gamma\><wide|\<cup\>|\<dot\>>\<Gamma\><rprime|'>>,
  and <math|\<exists\><wide|\<beta\>|\<bar\>><rprime|'><around|[|D<rprime|'>|]>\<Delta\>>
  denote <math|\<exists\><wide|\<beta\>|\<bar\>><wide|\<beta\><rprime|'>|\<bar\>><around|[|D\<wedge\>D<rprime|'>|]>.\<Gamma\>>.

  <\proposition>
    <label|EnvFragProp>Properties of environment fragments (see
    <cite|simonet-pottier-hmg-toplas> lemma 3.15).

    <\description>
      <item*|f-Hide><math|\<vDash\>\<Delta\>\<leqslant\>\<exists\><wide|\<alpha\>|\<bar\>>.\<Delta\>>.

      <item*|f-Imply><math|C<rsub|1>\<Rightarrow\>C<rsub|2>\<vDash\><around*|[|C<rsub|1>|]>\<Delta\>\<leqslant\><around*|[|C<rsub|2>|]>\<Delta\>>.

      <item*|f-Enrich><math|C\<Rightarrow\>\<Delta\><rsub|1>\<leqslant\>\<Delta\><rsub|2>\<vDash\><around*|[|C|]>\<Delta\><rsub|1>\<leqslant\><around*|[|C|]>\<Delta\><rsub|2>>.

      <item*|f-Ex><math|\<forall\><wide|\<alpha\>|\<bar\>>.\<Delta\><rsub|1>\<leqslant\>\<Delta\><rsub|2>\<vDash\><around*|(|\<exists\><wide|\<alpha\>|\<bar\>>.\<Delta\><rsub|1>|)>\<leqslant\><around*|(|\<exists\><wide|\<alpha\>|\<bar\>>.\<Delta\><rsub|2>|)>>.

      <item*|f-And><math|\<Delta\><rsub|1>\<leqslant\>\<Delta\><rsub|2>\<vDash\>\<Delta\>\<times\>\<Delta\><rsub|1>\<leqslant\>\<Delta\>\<times\>\<Delta\><rsub|2>>.
    </description>
  </proposition>

  <\proposition>
    Constructor <math|K\<colons\>\<forall\><wide|\<alpha\>|\<bar\>><wide|\<beta\>|\<bar\>><around|[|D|]>.\<tau\><rsub|1>\<times\>\<ldots\>\<times\>\<tau\><rsub|n>\<rightarrow\>\<varepsilon\><around|(|<wide|\<alpha\>|\<bar\>>|)>>
    where <math|D=\<exists\><wide|\<beta\>|\<bar\>><rprime|'>.A>, is
    equivalent to <math|K\<colons\>\<forall\><wide|\<alpha\>|\<bar\>><wide|\<gamma\><rsub|i>|\<bar\>><around|[|\<exists\><wide|\<beta\>|\<bar\>><wide|\<beta\>|\<bar\>><rprime|'>.<wide|\<gamma\><rsub|i>|\<bar\>><wide|=|\<dot\>><wide|\<tau\><rsub|i>|\<bar\>>\<wedge\>A|]>.\<gamma\><rsub|1>\<times\>\<ldots\>\<times\>\<gamma\><rsub|n>\<rightarrow\>\<varepsilon\><around|(|<wide|\<alpha\>|\<bar\>>|)>>.
  </proposition>

  <\proposition>
    <label|collapse-ty-args>Constructors of the form
    <math|K\<colons\>\<forall\><wide|\<alpha\><rsub|i>|\<bar\>><wide|\<beta\>|\<bar\>><around|[|D|]>.\<tau\><rsub|1>\<times\>\<ldots\>\<times\>\<tau\><rsub|n>\<rightarrow\>\<varepsilon\><around|(|<wide|\<alpha\><rsub|i>|\<bar\>>|)>>
    where <math|D=\<exists\><wide|\<beta\>|\<bar\>><rprime|'>.A>, are
    equivalent to constructors of the form
    <math|K\<colons\>\<forall\>\<alpha\><wide|\<beta\>|\<bar\>><around|[|\<exists\><wide|\<alpha\><rsub|i>|\<bar\>><wide|\<beta\>|\<bar\>><rprime|'>.\<alpha\><wide|=|\<dot\>>\<alpha\><rsub|1>\<rightarrow\>\<ldots\>\<rightarrow\>\<alpha\><rsub|m>\<wedge\>A|]>.\<gamma\><rsub|1>\<times\>\<ldots\>\<times\>\<gamma\><rsub|n>\<rightarrow\>\<varepsilon\><around|(|\<alpha\>|)>>
    when all uses of <math|\<varepsilon\><around*|(|\<tau\><rsub|1>,\<ldots\>,\<tau\><rsub|m>|)>>
    are translated to <math|\<varepsilon\><around*|(|\<tau\><rsub|1>\<rightarrow\>\<ldots\>\<rightarrow\>\<tau\><rsub|m>|)>>.
  </proposition>

  <\lemma>
    <label|Weakening><em|Weakening> (patterns and expressions). Assume
    <math|C<rsub|1>\<vDash\>C<rsub|2>>. If
    <math|C<rsub|2>\<vdash\>p:\<tau\>\<longrightarrow\>\<Delta\>> (resp.
    <math|C<rsub|2>,\<Gamma\>\<vdash\>e:\<tau\>>,
    <math|C<rsub|2>,\<Gamma\>\<vdash\>e:\<sigma\>>) is derivable, then there
    exists a derivation of <math|C<rsub|1>\<vdash\>p:\<tau\>\<longrightarrow\>\<Delta\>>
    (resp. <math|C<rsub|1>,\<Gamma\>\<vdash\>e:\<tau\>>,
    <math|C<rsub|1>,\<Gamma\>\<vdash\>e:\<sigma\>>) of the same structure.
  </lemma>

  The lemma follows from transitivity of <math|\<vDash\>> (<math|A\<vDash\>B>
  and <math|B\<vDash\>C> imply <math|A\<vDash\>C>) by induction on the
  structure of the derivation.

  <\lemma>
    <label|MoreCstrs>If <math|\<Sigma\>\<subset\>\<Sigma\><rprime|'>> and
    <math|C\<vdash\>p:\<tau\>\<longrightarrow\>\<Delta\>> (resp.
    <math|C,\<Gamma\>\<vdash\>e:\<tau\>>,
    <math|C,\<Gamma\>\<vdash\>e:\<sigma\>>) is derivable with constructors
    <math|\<Sigma\>>, then the same derivation works with constructors
    <math|\<Sigma\><rprime|'>>.
  </lemma>

  <\lemma>
    <label|CorrPat><em|Correctness> (patterns).
    <math|<around*|\<llbracket\>|\<vdash\>p\<downarrow\>\<tau\>|\<rrbracket\>>\<vdash\>p:\<tau\>\<longrightarrow\><around*|\<llbracket\>|\<vdash\>p\<uparrow\>\<tau\>|\<rrbracket\>>>.
  </lemma>

  <\proof>
    By induction on the structure of <math|p>.

    <\itemize>
      <item>Cases <math|0>, <math|1> and <math|x>: follow directly from
      <name|p-Empty>, <name|p-Wild> and <name|p-Var> respectively.

      <item>Case <math|p<rsub|1>\<wedge\>p<rsub|2>>.

      <\enumerate>
        <item>By the induction hypothesis,
        <math|<around*|\<llbracket\>|\<vdash\>p<rsub|i>\<downarrow\>\<tau\>|\<rrbracket\>>\<vdash\>p<rsub|i>:\<tau\>\<longrightarrow\><around*|\<llbracket\>|\<vdash\>p<rsub|i>\<uparrow\>\<tau\>|\<rrbracket\>>>
        for <math|i=1,2>.

        <item>By weakening and <name|p-And> we have the goal.
      </enumerate>

      <item>Case <math|K p<rsub|1>\<ldots\>p<rsub|n>>.

      <\enumerate>
        <item>Let <math|\<Sigma\>\<ni\>K\<colons\>\<forall\><wide|\<alpha\>|\<bar\>><wide|\<beta\>|\<bar\>><around|[|D|]>.\<tau\><rsub|1>\<times\>\<ldots\>\<times\>\<tau\><rsub|n>\<rightarrow\>\<varepsilon\><around|(|<wide|\<alpha\>|\<bar\>>|)>>.

        <item>By the induction hypothesis,
        <math|<around*|\<llbracket\>|\<vdash\>p<rsub|i>\<downarrow\>\<tau\><rsub|i>|\<rrbracket\>>\<vdash\>p<rsub|i>:\<tau\><rsub|i>\<longrightarrow\><around*|\<llbracket\>|\<vdash\>p<rsub|i>\<uparrow\>\<tau\><rsub|i>|\<rrbracket\>>>
        for <math|i=1,\<ldots\>,n>.

        <item>The <name|p-Cstr> rule says <math|\<forall\>i
        <around*|(|C\<wedge\>D\<vdash\>p<rsub|i>:\<tau\><rsub|i>\<longrightarrow\>\<Delta\><rsub|i>|)>/<rsub|<with|mode|text|p-Cstr>>C\<vdash\>p:\<varepsilon\><around|(|<wide|\<alpha\>|\<bar\>>|)>\<longrightarrow\>\<exists\><wide|\<beta\>|\<bar\>><around|[|D|]><around|(|\<Delta\><rsub|1>\<times\>\<ldots\>\<times\>\<Delta\><rsub|n>|)>>,
        where <math|\<Delta\><rsub|i>\<assign\><around*|\<llbracket\>|\<vdash\>p<rsub|i>\<uparrow\>\<tau\><rsub|i>|\<rrbracket\>>>.
        Applying it to (2) we get <math|C\<vdash\>p:\<varepsilon\><around|(|<wide|\<alpha\>|\<bar\>>|)>\<longrightarrow\>\<exists\><wide|\<beta\>|\<bar\>><around|[|D|]><around|(|\<Delta\><rsub|1>\<times\>\<ldots\>\<times\>\<Delta\><rsub|n>|)>>
        as long as <math|C\<wedge\>D\<vDash\><around*|\<llbracket\>|\<vdash\>p<rsub|i>\<downarrow\>\<tau\><rsub|i>|\<rrbracket\>>>.

        <item>Let <math|<wide|\<alpha\>|\<bar\>><rprime|'><wide|\<beta\>|\<bar\>><rprime|'>#FV<around|(|\<Sigma\>,\<tau\>|)>>
        and <math|\<tau\><rsub|i><rprime|'>\<assign\>\<tau\><rsub|i><around|[|<wide|\<alpha\>|\<bar\>><wide|\<beta\>|\<bar\>>\<assign\><wide|\<alpha\>|\<bar\>><rprime|'><wide|\<beta\>|\<bar\>><rprime|'>|]>,D<rprime|'>\<assign\>D<around|[|<wide|\<alpha\>|\<bar\>><wide|\<beta\>|\<bar\>>\<assign\><wide|\<alpha\>|\<bar\>><rprime|'><wide|\<beta\>|\<bar\>><rprime|'>|]>>.
        Let <math|\<Delta\><rsub|i><rprime|'>> be <math|\<Delta\><rsub|i>>
        with unbound occurrences of <math|<wide|\<alpha\>|\<bar\>><wide|\<beta\>|\<bar\>>>
        renamed to <math|<wide|\<alpha\>|\<bar\>><rprime|'><wide|\<beta\>|\<bar\>><rprime|'>>.

        <item>By weakening and <name|p-EqIn>, (3) gives
        <math|<wide|\<alpha\>|\<bar\>><wide|\<beta\>|\<bar\>><wide|=|\<dot\>><wide|\<alpha\>|\<bar\>><rprime|'><wide|\<beta\>|\<bar\>><rprime|'>\<wedge\>\<varepsilon\><around|(|<wide|\<alpha\>|\<bar\>><rprime|'>|)><wide|=|\<dot\>>\<tau\>\<wedge\>C\<vdash\>p:\<tau\>\<longrightarrow\>\<exists\><wide|\<beta\>|\<bar\>><around|[|D|]><around|(|\<Delta\><rsub|1>\<times\>\<ldots\>\<times\>\<Delta\><rsub|n>|)>>.
        The conjunction of equations <math|<wide|\<alpha\>|\<bar\>><wide|\<beta\>|\<bar\>><wide|=|\<dot\>><wide|\<alpha\>|\<bar\>><rprime|'><wide|\<beta\>|\<bar\>><rprime|'>>
        allows for renaming of the ``old'' variables
        <math|<wide|\<alpha\>|\<bar\>><wide|\<beta\>|\<bar\>>> by the
        ``fresh'' variables <math|<wide|\<alpha\>|\<bar\>><rprime|'><wide|\<beta\>|\<bar\>><rprime|'>>.

        <item>By proposition <reference|EnvFragProp>, transitivity of
        <math|\<leqslant\>>, and <name|p-SubOut>, we get
        <math|<wide|\<alpha\>|\<bar\>><wide|\<beta\>|\<bar\>><wide|=|\<dot\>><wide|\<alpha\>|\<bar\>><rprime|'><wide|\<beta\>|\<bar\>><rprime|'>\<wedge\>\<varepsilon\><around|(|<wide|\<alpha\>|\<bar\>><rprime|'>|)><wide|=|\<dot\>>\<tau\>\<wedge\>C\<vdash\>p:\<tau\>\<longrightarrow\>\<exists\><wide|\<alpha\>|\<bar\>><rprime|'><wide|\<beta\>|\<bar\>><rprime|'><around|[|D<rprime|'>|]><around|(|\<Delta\><rsub|1><rprime|'>\<times\>\<ldots\>\<times\>\<Delta\><rsub|n><rprime|'>|)>>.

        <item>By applying <name|p-Hide> to (6) with
        <math|C=<wide|\<alpha\>|\<bar\>><wide|=|\<dot\>><wide|\<alpha\>|\<bar\>><rprime|'>\<wedge\>\<forall\><wide|\<beta\>|\<bar\>><rprime|'>.D<rprime|'>\<Rightarrow\>\<wedge\><rsub|i><around*|\<llbracket\>|\<vdash\>p<rsub|i>\<downarrow\>\<tau\><rsub|i><rprime|'>|\<rrbracket\>>>
        and weakening, since w.l.o.g. <math|<wide|\<alpha\>|\<bar\>><wide|\<beta\>|\<bar\>>>
        do not appear unbound in the goal, and
        <math|C\<wedge\>D\<vDash\><around*|\<llbracket\>|\<vdash\>p<rsub|i>\<downarrow\>\<tau\><rsub|i>|\<rrbracket\>>>,
        we get the goal <math|\<exists\><wide|\<alpha\>|\<bar\>><rprime|'>.\<varepsilon\><around|(|<wide|\<alpha\>|\<bar\>><rprime|'>|)><wide|=|\<dot\>>\<tau\>\<wedge\>\<forall\><wide|\<beta\>|\<bar\>><rprime|'>.D<rprime|'>\<Rightarrow\>\<wedge\><rsub|i><around*|\<llbracket\>|\<vdash\>p<rsub|i>\<downarrow\>\<tau\><rsub|i><rprime|'>|\<rrbracket\>>\<vdash\>p:\<tau\>\<longrightarrow\>\<exists\><wide|\<alpha\>|\<bar\>><rprime|'><wide|\<beta\>|\<bar\>><rprime|'><around|[|D<rprime|'>|]><around|(|\<Delta\><rsub|1><rprime|'>\<times\>\<ldots\>\<times\>\<Delta\><rsub|n><rprime|'>|)>>.
      </enumerate>
    </itemize>
  </proof>

  Proof of theorem <reference|InfCorrExpr>.

  <\proof>
    By induction on the structure of <math|e>.

    <\itemize>
      <item>Case <math|e> is <math|x>.

      <\enumerate>
        <item>If <math|x\<nin\>Dom<around*|(|\<Gamma\>|)>>, then the goal
        follows by applying <name|FElim>. Otherwise, let
        <math|\<Gamma\><around|(|x|)>> be
        <math|\<forall\>\<beta\><around|[|\<exists\><wide|\<alpha\>|\<bar\>>.D|]>.\<beta\>>.
        By <name|Var>, <math|D,\<Gamma\>\<vdash\>x:\<beta\>>.

        <item>Let <math|\<beta\><rprime|'><wide|\<alpha\>|\<bar\>><rprime|'>#FV<around|(|\<Gamma\>,\<tau\>|)>>.
        By (1), weakening and <name|Equ>,
        <math|\<beta\><wide|\<alpha\>|\<bar\>><wide|=|\<dot\>>\<beta\><rprime|'><wide|\<alpha\>|\<bar\>><rprime|'>\<wedge\>D<rprime|'>\<wedge\>\<beta\><rprime|'><wide|=|\<dot\>>\<tau\>,\<Gamma\>\<vdash\>x:\<tau\>>,
        where <math|D<rprime|'>\<assign\>D<around|[|\<beta\><wide|\<alpha\>|\<bar\>>\<assign\>\<beta\><rprime|'><wide|\<alpha\>|\<bar\>><rprime|'>|]>>.

        <item>By <name|Hide> and weakening, since w.l.o.g.
        <math|\<beta\><wide|\<alpha\>|\<bar\>>> do not appear unbounded in
        the goal, this implies the goal <math|\<exists\>\<beta\><rprime|'><wide|\<alpha\>|\<bar\>><rprime|'>.<around|(|D<rprime|'>\<wedge\>\<beta\><rprime|'><wide|=|\<dot\>>\<tau\>|)>,\<Gamma\>\<vdash\>x:\<tau\>>.
      </enumerate>

      <item>Case <math|e> is <math|<text|<with|font-shape|condensed|<strong|assert
      false>>>>. The goal follows by <name|FElim>.

      <item>Case <math|e> is <math|<text|<with|font-shape|condensed|<strong|assert
      num>>> m\<leq\>n;e>.

      <\enumerate>
        <item>Let <math|\<alpha\><rsup|1>\<alpha\><rsup|2>#FV<around|(|\<Gamma\>,\<tau\>|)>>.

        <item>By the induction hypothesis, we have
        <math|<around*|\<llbracket\>|\<Gamma\>\<vdash\>e<rsub|1>:Num<around*|(|\<alpha\><rsup|1>|)>|\<rrbracket\>>,\<Gamma\>\<vdash\>e<rsub|1>:Num<around*|(|\<alpha\><rsup|1>|)>>,
        <math|<around*|\<llbracket\>|\<Gamma\>\<vdash\>e<rsub|2>:Num<around*|(|\<alpha\><rsup|2>|)>|\<rrbracket\>>,\<Gamma\>\<vdash\>e<rsub|2>:Num<around*|(|\<alpha\><rsup|2>|)>>
        and <math|<around*|\<llbracket\>|\<Gamma\>\<vdash\>e<rsub|3>:\<tau\>|\<rrbracket\>>,\<Gamma\>\<vdash\>e<rsub|3>:\<tau\>>.

        <item>By weakening and <name|AssertLeq>, this yields
        <math|<around*|\<llbracket\>|\<Gamma\>\<vdash\>e<rsub|1>:Num<around*|(|\<alpha\><rsup|1>|)>|\<rrbracket\>>\<wedge\><around*|\<llbracket\>|\<Gamma\>\<vdash\>e<rsub|2>:Num<around*|(|\<alpha\><rsup|2>|)>|\<rrbracket\>>\<wedge\>\<alpha\><rsup|1>\<leq\>\<alpha\><rsup|2>\<wedge\><around*|\<llbracket\>|\<Gamma\>\<vdash\>e<rsub|3>:<no-break>\<tau\>|\<rrbracket\>>,\<Gamma\>\<vdash\><text|<with|font-shape|condensed|<strong|assert
        num>>> e<rsub|1>\<leq\>e<rsub|2>;e<rsub|3>:\<tau\>>.

        <item>By <name|Hide> using (1), this gives the goal.
      </enumerate>

      <item>Case <math|e> is <math|<text|<with|font-shape|condensed|<strong|assert
      type>>> e<rsub|1>=e<rsub|2>;e<rsub|3>>.

      <\enumerate>
        <item>Let <math|\<alpha\><rsup|1>\<alpha\><rsup|2>#FV<around|(|\<Gamma\>,\<tau\>|)>>.

        <item>By the induction hypothesis, we have
        <math|<around*|\<llbracket\>|\<Gamma\>\<vdash\>e<rsub|1>:\<alpha\><rsup|1>|\<rrbracket\>>,\<Gamma\>\<vdash\>e<rsub|1>:\<alpha\><rsup|1>>,
        <math|<around*|\<llbracket\>|\<Gamma\>\<vdash\>e<rsub|2>:\<alpha\><rsup|2>|\<rrbracket\>>,\<Gamma\>\<vdash\>e<rsub|2>:\<alpha\><rsup|2>>
        and <math|<around*|\<llbracket\>|\<Gamma\>\<vdash\>e<rsub|3>:\<tau\>|\<rrbracket\>>,\<Gamma\>\<vdash\>e<rsub|3>:\<tau\>>.

        <item>By weakening and <name|AssertEqty>, this yields
        <math|<around*|\<llbracket\>|\<Gamma\>\<vdash\>e<rsub|1>:\<alpha\><rsup|1>|\<rrbracket\>>\<wedge\><around*|\<llbracket\>|\<Gamma\>\<vdash\>e<rsub|2>:\<alpha\><rsup|2>|\<rrbracket\>>\<wedge\>\<alpha\><rsup|1><wide|=|\<dot\>>\<alpha\><rsup|2>\<wedge\><around*|\<llbracket\>|\<Gamma\>\<vdash\>e<rsub|3>:<no-break>\<tau\>|\<rrbracket\>>,\<Gamma\>\<vdash\><text|<with|font-shape|condensed|<strong|assert
        type>>> e<rsub|1>=e<rsub|2>;e<rsub|3>:\<tau\>>.

        <item>By <name|Hide> using (1), this gives the goal.
      </enumerate>

      <item>Case <math|e> is <math|<text|<with|font-shape|condensed|<strong|runtime
      failure>>> s>.

      <\enumerate>
        <item>By the induction hypothesis, we have
        <math|<around*|\<llbracket\>|\<Gamma\>\<vdash\>s:String|\<rrbracket\>>,\<Gamma\>\<vdash\>s:String>.

        <item>The goal follows from <name|RuntimeFailure>, since
        <math|<around*|\<llbracket\>|\<Gamma\>\<vdash\><text|<with|font-shape|condensed|<strong|runtime
        failure>>> s:<no-break>\<tau\>|\<rrbracket\>>=<around*|\<llbracket\>|\<Gamma\>\<vdash\>s:String|\<rrbracket\>>>.
      </enumerate>

      <item>Case <math|e> is <math|\<lambda\><wide|c|\<bar\>>> where
      <math|<wide|c|\<bar\>>=<around|(|c<rsub|1>,\<ldots\>,c<rsub|n>|)>>.

      <\enumerate>
        <item>Let <math|\<alpha\><rsub|1>\<alpha\><rsub|2>#FV<around|(|\<Gamma\>,\<tau\>|)>>.

        <item>Induction hypothesis yelds <math|<around*|\<llbracket\>|\<Gamma\>\<vdash\>c<rsub|i>:\<alpha\><rsub|1>\<rightarrow\>\<alpha\><rsub|2>|\<rrbracket\>>,\<Gamma\>\<vdash\>c<rsub|i>:\<alpha\><rsub|1>\<rightarrow\>\<alpha\><rsub|2>>.

        <item>By (2), weakening and <name|Abs>,
        <math|<around*|\<llbracket\>|\<Gamma\>\<vdash\><wide|c|\<bar\>>:\<alpha\><rsub|1>\<rightarrow\>\<alpha\><rsub|2>|\<rrbracket\>>,\<Gamma\>\<vdash\>\<lambda\><wide|c|\<bar\>>:\<alpha\><rsub|1>\<rightarrow\>\<alpha\><rsub|2>>.

        <item>By weakening and <name|Equ>, (3) implies
        <math|<around*|\<llbracket\>|\<Gamma\>\<vdash\><wide|c|\<bar\>>:\<alpha\><rsub|1>\<rightarrow\>\<alpha\><rsub|2>|\<rrbracket\>>\<wedge\>\<alpha\><rsub|1>\<rightarrow\>\<alpha\><rsub|2><wide|=|\<dot\>>\<tau\>,\<Gamma\>\<vdash\>\<lambda\><wide|c|\<bar\>>:\<tau\>>.

        <item>By (1) and <name|Hide>, this implies
        <math|<around*|\<llbracket\>|\<Gamma\>\<vdash\>\<lambda\><wide|c|\<bar\>>:\<tau\>|\<rrbracket\>>,\<Gamma\>\<vdash\>\<lambda\><wide|c|\<bar\>>:\<tau\>>.
      </enumerate>

      <item>Case <math|e> is <math|e<rsub|1>*e<rsub|2>>.

      <\enumerate>
        <item>Let <math|\<alpha\>#FV<around|(|\<Gamma\>,\<tau\>|)>>.

        <item>By the induction hypothesis, we have
        <math|<around*|\<llbracket\>|\<Gamma\>\<vdash\>e<rsub|1>:\<alpha\>\<rightarrow\>\<tau\>|\<rrbracket\>>,\<Gamma\>\<vdash\>e<rsub|1>:\<alpha\>\<rightarrow\>\<tau\>>
        and <math|<around*|\<llbracket\>|\<Gamma\>\<vdash\>e<rsub|2>:\<alpha\>|\<rrbracket\>>,\<Gamma\>\<vdash\>e<rsub|2>:\<alpha\>>.

        <item>By weakening and <name|App>, this yields
        <math|<around*|\<llbracket\>|\<Gamma\>\<vdash\>e<rsub|1>:\<alpha\>\<rightarrow\>\<tau\>|\<rrbracket\>>\<wedge\><around*|\<llbracket\>|\<Gamma\>\<vdash\>e<rsub|2>:\<alpha\>|\<rrbracket\>>,\<Gamma\>\<vdash\>e<rsub|1>*e<rsub|2>:\<tau\>>.

        <item>By <name|Hide> using (1), <math|<around*|\<llbracket\>|\<Gamma\>\<vdash\>e<rsub|1>*e<rsub|2>:\<tau\>|\<rrbracket\>>,\<Gamma\>\<vdash\>e<rsub|1>*e<rsub|2>:\<tau\>>.
      </enumerate>

      <item>Case <math|e> is <math|K*e<rsub|1>*\<ldots\>*e<rsub|n>>.

      <\enumerate>
        <item>Let <math|\<Sigma\>\<ni\>K\<colons\>\<forall\><wide|\<alpha\>|\<bar\>><wide|\<beta\>|\<bar\>><around|[|D|]>.\<tau\><rsub|1>\<times\>\<ldots\>\<times\>\<tau\><rsub|n>\<rightarrow\>\<varepsilon\><around|(|<wide|\<alpha\>|\<bar\>>|)>>.

        <item>By induction hypothesis and weakening for each
        <math|i=1,\<ldots\>,n>

        <\equation*>
          \<wedge\><rsub|j><around*|\<llbracket\>|\<Gamma\>\<vdash\>e<rsub|j>:\<tau\><rsub|j>|\<rrbracket\>>\<wedge\>D\<wedge\>\<varepsilon\><around|(|<wide|\<alpha\>|\<bar\>>|)><wide|=|\<dot\>>\<tau\>,\<Gamma\>\<vdash\>e<rsub|i>:\<tau\><rsub|i>
        </equation*>

        <item>Applying <name|Cstr> to (1) and (3) we obtain

        <\equation*>
          \<wedge\><rsub|i><around*|\<llbracket\>|\<Gamma\>\<vdash\>e<rsub|i>:\<tau\><rsub|i>|\<rrbracket\>>\<wedge\>D\<wedge\>\<varepsilon\><around|(|<wide|\<alpha\>|\<bar\>>|)><wide|=|\<dot\>>\<tau\>,\<Gamma\>\<vdash\>K*e<rsub|1>*\<ldots\>*e<rsub|n>:\<varepsilon\><around|(|<wide|\<alpha\>|\<bar\>>|)>
        </equation*>

        <item>Let <math|<wide|\<alpha\>|\<bar\>><rprime|'><wide|\<beta\>|\<bar\>><rprime|'>#FV<around|(|\<Gamma\>,\<tau\>|)>>
        and <math|\<tau\><rsub|i><rprime|'>\<assign\>\<tau\><rsub|i><around|[|<wide|\<alpha\>|\<bar\>><wide|\<beta\>|\<bar\>>\<assign\><wide|\<alpha\>|\<bar\>><rprime|'><wide|\<beta\>|\<bar\>><rprime|'>|]>>,
        <math|D<rprime|'>\<assign\>D<around|[|\<beta\><wide|\<alpha\>|\<bar\>>\<assign\>\<beta\><rprime|'><wide|\<alpha\>|\<bar\>><rprime|'>|]>>.

        <\equation*>
          <wide|\<alpha\>|\<bar\>><wide|\<beta\>|\<bar\>><wide|=|\<dot\>><wide|\<alpha\>|\<bar\>><rprime|'><wide|\<beta\>|\<bar\>><rprime|'>\<wedge\><rsub|i><around*|\<llbracket\>|\<Gamma\>\<vdash\>e<rsub|i>:\<tau\><rsub|i><rprime|'>|\<rrbracket\>>\<wedge\>D\<wedge\>\<varepsilon\><around|(|<wide|\<alpha\>|\<bar\>><rprime|'>|)><wide|=|\<dot\>>\<tau\>,\<Gamma\>\<vdash\>K*e<rsub|1>*\<ldots\>*e<rsub|n>:\<varepsilon\><around|(|<wide|\<alpha\>|\<bar\>><rprime|'>|)>
        </equation*>

        <item>By <name|Equ>, (1) <name|Hide> and weakening, since w.l.o.g.
        <math|<wide|\<alpha\>|\<bar\>><wide|\<beta\>|\<bar\>>> do not appear
        unbounded in the goal, <math|<around*|\<llbracket\>|\<Gamma\>\<vdash\>K*e<rsub|1>*\<ldots\>*e<rsub|n>:\<tau\>|\<rrbracket\>>,\<Gamma\>\<vdash\>K*e<rsub|1>*\<ldots\>*e<rsub|n>:\<tau\>>.
      </enumerate>

      <item>Case <math|e> is <math|<text|<with|font-shape|condensed|<strong|let
      rec>>> x=e<rsub|1> <text|<with|font-shape|condensed|<strong|in>>>
      e<rsub|2>>.

      <\enumerate>
        <item>Let <math|\<alpha\>\<beta\>#FV<around|(|\<Gamma\>,\<tau\>|)>>
        and <math|\<chi\>#PV<around*|(|\<Gamma\>|)>>.

        <item>Let <math|\<sigma\>=\<forall\>\<beta\><around|[|\<chi\><around*|(|\<beta\>|)>|]>.\<beta\>>,
        <math|\<Gamma\><rprime|'>=\<Gamma\><around|{|x\<mapsto\>\<sigma\>|}>>.
        By the induction hypothesis, <math|<around*|\<llbracket\>|\<Gamma\><rprime|'>\<vdash\>e<rsub|1>:\<beta\>|\<rrbracket\>>,\<Gamma\><rprime|'>\<vdash\>e<rsub|1>:\<beta\>>
        and <math|<around*|\<llbracket\>|\<Gamma\><rprime|'>\<vdash\>e<rsub|2>:\<tau\>|\<rrbracket\>>,\<Gamma\><rprime|'>\<vdash\>e<rsub|2>:\<tau\>>.

        <item>Let <math|D=\<forall\>\<beta\>.<around|(|\<chi\><around*|(|\<beta\>|)>\<Rightarrow\><around*|\<llbracket\>|\<Gamma\><rprime|'>\<vdash\>e<rsub|1>:\<beta\>|\<rrbracket\>>|)>>.
        Since <math|D\<wedge\>\<chi\><around*|(|\<beta\>|)>> implies
        <math|<around*|\<llbracket\>|\<Gamma\><rprime|'>\<vdash\>e<rsub|1>:<no-break>\<beta\>|\<rrbracket\>>>,
        by weakening of (2), we have <math|D\<wedge\>\<chi\><around*|(|\<beta\>|)>,\<Gamma\><rprime|'>\<vdash\>e<rsub|1>:<no-break>\<beta\>>.
        From (1) we have <math|\<alpha\>#FV<around|(|D,\<Gamma\><rprime|'>,\<tau\>|)>>,
        by <name|Gen> we have <math|D\<wedge\>\<exists\>\<beta\>.\<chi\><around*|(|\<beta\>|)>,\<Gamma\><rprime|'>\<vdash\>e<rsub|1>:\<forall\>\<beta\><around|[|\<chi\><around*|(|\<beta\>|)>|]>.\<beta\>>,
        by (1) and renaming we have

        <\equation*>
          D\<wedge\>\<exists\>\<alpha\>.\<chi\><around*|(|\<alpha\>|)>,\<Gamma\><rprime|'>\<vdash\>e<rsub|1>:\<sigma\>.
        </equation*>

        <item>By weakening of both (2) and (3), and by <name|LetRec>, we have
        <math|<around*|\<llbracket\>|\<Gamma\>\<vdash\><text|<with|font-shape|condensed|<strong|let
        rec>>> x=e<rsub|1> <text|<with|font-shape|condensed|<strong|in>>>
        e<rsub|2>:\<tau\>|\<rrbracket\>>,\<Gamma\>\<vdash\><text|<with|font-shape|condensed|<strong|let
        rec>>> x=e<rsub|1> <text|<with|font-shape|condensed|<strong|in>>>
        e<rsub|2>:\<tau\>>.
      </enumerate>

      <item>Case <math|e> is <math|p.e>.

      <\enumerate>
        <item><math|\<tau\>> is of the form
        <math|\<tau\><rsub|1>\<rightarrow\>\<tau\><rsub|2>>. Write
        <math|<around*|\<llbracket\>|\<vdash\>p\<uparrow\>\<tau\><rsub|1>|\<rrbracket\>>>
        as <math|\<exists\><wide|\<beta\>|\<bar\>><around|[|D|]>\<Gamma\><rprime|'>>,
        where <math|<wide|\<beta\>|\<bar\>>#FV<around|(|\<Gamma\>,\<tau\><rsub|1>,\<tau\><rsub|2>|)>>.

        <item>By induction hypothesis, <math|<around*|\<llbracket\>|\<Gamma\>\<Gamma\><rprime|'>\<vdash\>e:\<tau\><rsub|2>|\<rrbracket\>>,\<Gamma\>\<Gamma\><rprime|'>\<vdash\>e:\<tau\><rsub|2>>.

        <item>By lemma <reference|CorrPat> and (1), we have
        <math|<around*|\<llbracket\>|\<vdash\>p\<downarrow\>\<tau\><rsub|1>|\<rrbracket\>>\<vdash\>p:\<tau\><rsub|1>\<longrightarrow\>\<exists\><wide|\<beta\>|\<bar\>><around|[|D|]>\<Gamma\><rprime|'>>.

        <item>By instantiation of <math|<wide|\<beta\>|\<bar\>>> and
        weakening, (2) implies

        <\equation*>
          <around*|\<llbracket\>|\<Gamma\>\<vdash\>p.e:\<tau\>|\<rrbracket\>>\<wedge\>D,\<Gamma\>\<Gamma\><rprime|'>\<vdash\>e:\<tau\><rsub|2>
        </equation*>

        <item>By weakening, (3) implies <math|<around*|\<llbracket\>|\<Gamma\>\<vdash\>p.e:\<tau\>|\<rrbracket\>>\<vdash\>p:\<tau\><rsub|1>\<longrightarrow\>\<exists\><wide|\<beta\>|\<bar\>><around|[|D|]>\<Gamma\><rprime|'>>.

        <item>By (4), (5), (1), and <name|Clause>, we obtain
        <math|<around*|\<llbracket\>|\<Gamma\>\<vdash\>p.e:\<tau\>|\<rrbracket\>>,\<Gamma\>\<vdash\>p.e:\<tau\>>.
      </enumerate>

      <item>Case <math|e> is <math|p <text|<with|font-shape|condensed|<strong|when>>>
      \<wedge\><rsub|i>m<rsub|i>\<leqslant\>n<rsub|i>.e> and
      <math|e\<neq\><text|<with|font-shape|condensed|<strong|assert
      false>>>\<wedge\>\<ldots\>\<wedge\>e\<neq\>\<lambda\><around*|(|p<rprime|'>\<ldots\>\<lambda\><around*|(|p<rprime|''>.<text|<with|font-shape|condensed|<strong|assert
      false>>>|)>|)>>.

      <\enumerate>
        <item>Let <math|<wide|\<beta\>|\<bar\>><wide|\<alpha\><rsup|1><rsub|i>\<alpha\><rsup|2><rsub|i>|\<bar\>>#FV<around|(|\<Gamma\>,\<tau\><rsub|1>,\<tau\><rsub|2>|)>>.
        Recall that <math|<around*|\<llbracket\>|\<Gamma\>\<vdash\>p
        <text|<with|font-shape|condensed|<strong|when>>>
        \<wedge\><rsub|i>m<rsub|i>\<leqslant\>n<rsub|i>.e:\<tau\><rsub|1>\<rightarrow\>\<tau\><rsub|2>|\<rrbracket\>>=\<exists\><wide|\<alpha\><rsup|1><rsub|i>\<alpha\><rsup|2><rsub|i>|\<bar\>>.\<Phi\>>,
        for <math|\<Phi\>=<next-line><around*|\<llbracket\>|\<vdash\>p\<downarrow\>\<tau\><rsub|1>|\<rrbracket\>>\<wedge\>\<forall\><wide|\<beta\>|\<bar\>>.D\<Rightarrow\>\<wedge\><rsub|i><around*|\<llbracket\>|\<Gamma\>\<Gamma\><rprime|'>\<vdash\>m<rsub|i>:Num<around*|(|\<alpha\><rsup|1><rsub|i>|)>|\<rrbracket\>>\<wedge\><rsub|i><next-line><around*|\<llbracket\>|\<Gamma\>\<Gamma\><rprime|'>\<vdash\>n<rsub|i>:Num<around*|(|\<alpha\><rsup|2><rsub|i>|)>|\<rrbracket\>>\<wedge\><around*|(|\<wedge\><rsub|i>\<alpha\><rsup|1><rsub|i>\<leq\>\<alpha\><rsup|2><rsub|i>\<Rightarrow\><around*|\<llbracket\>|\<Gamma\>\<Gamma\><rprime|'>\<vdash\>e:\<tau\><rsub|2>|\<rrbracket\>>|)>>.

        <item><math|\<tau\>> is of the form
        <math|\<tau\><rsub|1>\<rightarrow\>\<tau\><rsub|2>>. Write
        <math|<around*|\<llbracket\>|\<vdash\>p\<uparrow\>\<tau\><rsub|1>|\<rrbracket\>>>
        as <math|\<exists\><wide|\<beta\>|\<bar\>><around|[|D|]>\<Gamma\><rprime|'>>.

        <item>By induction hypothesis, <math|<around*|\<llbracket\>|\<Gamma\>\<Gamma\><rprime|'>\<vdash\>e:\<tau\><rsub|2>|\<rrbracket\>>,\<Gamma\>\<Gamma\><rprime|'>\<vdash\>e:\<tau\><rsub|2>>,
        and also <math|<around*|\<llbracket\>|\<Gamma\>\<Gamma\><rprime|'>\<vdash\>m<rsub|i>:Num<around*|(|\<alpha\><rsub|i><rsup|1>|)>|\<rrbracket\>>,\<Gamma\>\<Gamma\><rprime|'>\<vdash\>m<rsub|i>:Num<around*|(|\<alpha\><rsub|i><rsup|1>|)>>
        and <math|<around*|\<llbracket\>|\<Gamma\>\<Gamma\><rprime|'>\<vdash\>n<rsub|i>:Num<around*|(|\<alpha\><rsub|i><rsup|2>|)>|\<rrbracket\>>,\<Gamma\>\<Gamma\><rprime|'>\<vdash\>n<rsub|i>:Num<around*|(|\<alpha\><rsub|i><rsup|2>|)>>.

        <item>By lemma <reference|CorrPat> and (1), we have
        <math|<around*|\<llbracket\>|\<vdash\>p\<downarrow\>\<tau\><rsub|1>|\<rrbracket\>>\<vdash\>p:\<tau\><rsub|1>\<longrightarrow\>\<exists\><wide|\<beta\>|\<bar\>><around|[|D|]>\<Gamma\><rprime|'>>.

        <item>By instantiation of <math|<wide|\<beta\>|\<bar\>>> and
        weakening, (3) implies

        <\eqnarray*>
          <tformat|<table|<row|<cell|\<Phi\>\<wedge\>D\<wedge\><rsub|i>\<alpha\><rsup|1><rsub|i>\<leq\>\<alpha\><rsup|2><rsub|i>,\<Gamma\>\<Gamma\><rprime|'>>|<cell|\<vdash\>>|<cell|e:\<tau\><rsub|2>>>|<row|<cell|\<Phi\>\<wedge\>D,\<Gamma\>\<Gamma\><rprime|'>>|<cell|\<vdash\>>|<cell|m<rsub|i>:Num<around*|(|\<alpha\><rsup|1><rsub|i>|)>>>|<row|<cell|\<Phi\>\<wedge\>D,\<Gamma\>\<Gamma\><rprime|'>>|<cell|\<vdash\>>|<cell|n<rsub|i>:Num<around*|(|\<alpha\><rsup|2><rsub|i>|)>>>>>
        </eqnarray*>

        <item>By weakening, (4) implies <math|\<Phi\>\<vdash\>p:\<tau\><rsub|1>\<longrightarrow\>\<exists\><wide|\<beta\>|\<bar\>><around|[|D|]>\<Gamma\><rprime|'>>.

        <item>By (5), (6), (1), and <name|Clause>, we obtain
        <math|\<Phi\>,\<Gamma\>\<vdash\>p
        <text|<with|font-shape|condensed|<strong|when>>>
        \<wedge\><rsub|i>m<rsub|i>\<leqslant\>n<rsub|i>.e:\<tau\>>.

        <item>By (7) and <name|Hide>, we get the goal.
      </enumerate>

      <item>Case <math|e> is <math|p <text|<with|font-shape|condensed|<strong|when>>>
      \<wedge\><rsub|i>m<rsub|i>\<leqslant\>n<rsub|i>.e> and
      <math|e=<text|<with|font-shape|condensed|<strong|assert
      false>>>\<vee\>\<ldots\>\<vee\>e=\<lambda\><around*|(|p<rprime|'>\<ldots\>\<lambda\><around*|(|p<rprime|''>.<text|<with|font-shape|condensed|<strong|assert
      false>>>|)>|)>>. The proof is nearly identical to above.

      <\enumerate>
        <item>Let <math|\<alpha\><rsub|3><wide|\<beta\>|\<bar\>><wide|\<alpha\><rsup|1><rsub|i>\<alpha\><rsup|2><rsub|i>|\<bar\>>#FV<around|(|\<Gamma\>,\<tau\><rsub|1>,\<tau\><rsub|2>|)>>.
        Recall that <math|<around*|\<llbracket\>|\<Gamma\>\<vdash\>p
        <text|<with|font-shape|condensed|<strong|when>>>
        \<wedge\><rsub|i>m<rsub|i>\<leqslant\>n<rsub|i>.e:\<tau\><rsub|1>\<rightarrow\>\<tau\><rsub|2>|\<rrbracket\>>=\<exists\>\<alpha\><rsub|3><wide|\<alpha\><rsup|1><rsub|i>\<alpha\><rsup|2><rsub|i>|\<bar\>>.\<Phi\>>,
        for <math|\<Phi\>=<next-line><around*|\<llbracket\>|\<vdash\>p\<downarrow\>\<alpha\><rsub|3>|\<rrbracket\>>\<wedge\>\<forall\><wide|\<beta\>|\<bar\>>.D\<Rightarrow\>\<wedge\><rsub|i><around*|\<llbracket\>|\<Gamma\>\<Gamma\><rprime|'>\<vdash\>m<rsub|i>:Num<around*|(|\<alpha\><rsup|1><rsub|i>|)>|\<rrbracket\>>\<wedge\><rsub|i><around*|\<llbracket\>|\<Gamma\>\<Gamma\><rprime|'>\<vdash\>n<rsub|i>:Num<around*|(|\<alpha\><rsup|2><rsub|i>|)>|\<rrbracket\>><next-line>\<wedge\><around*|(|\<alpha\><rsub|3><wide|=|\<dot\>>\<tau\><rsub|1>\<wedge\><rsub|i>\<alpha\><rsup|1><rsub|i>\<leq\>\<alpha\><rsup|2><rsub|i>\<Rightarrow\><around*|\<llbracket\>|\<Gamma\>\<Gamma\><rprime|'>\<vdash\>e:\<tau\><rsub|2>|\<rrbracket\>>|)>>.

        <item><math|\<tau\>> is of the form
        <math|\<tau\><rsub|1>\<rightarrow\>\<tau\><rsub|2>>. Write
        <math|<around*|\<llbracket\>|\<vdash\>p\<uparrow\>\<alpha\><rsub|3>|\<rrbracket\>>>
        as <math|\<exists\><wide|\<beta\>|\<bar\>><around|[|D|]>\<Gamma\><rprime|'>>.

        <item>By induction hypothesis, <math|<around*|\<llbracket\>|\<Gamma\>\<Gamma\><rprime|'>\<vdash\>e:\<tau\><rsub|2>|\<rrbracket\>>,\<Gamma\>\<Gamma\><rprime|'>\<vdash\>e:\<tau\><rsub|2>>,
        and also <math|<around*|\<llbracket\>|\<Gamma\>\<Gamma\><rprime|'>\<vdash\>m<rsub|i>:Num<around*|(|\<alpha\><rsub|i><rsup|1>|)>|\<rrbracket\>>,\<Gamma\>\<Gamma\><rprime|'>\<vdash\>m<rsub|i>:Num<around*|(|\<alpha\><rsub|i><rsup|1>|)>>
        and <math|<around*|\<llbracket\>|\<Gamma\>\<Gamma\><rprime|'>\<vdash\>n<rsub|i>:Num<around*|(|\<alpha\><rsub|i><rsup|2>|)>|\<rrbracket\>>,\<Gamma\>\<Gamma\><rprime|'>\<vdash\>n<rsub|i>:Num<around*|(|\<alpha\><rsub|i><rsup|2>|)>>.

        <item>By lemma <reference|CorrPat> and (1), we have
        <math|<around*|\<llbracket\>|\<vdash\>p\<downarrow\>\<alpha\><rsub|3>|\<rrbracket\>>\<vdash\>p:\<alpha\><rsub|3>\<longrightarrow\>\<exists\><wide|\<beta\>|\<bar\>><around|[|D|]>\<Gamma\><rprime|'>>.

        <item>By instantiation of <math|<wide|\<beta\>|\<bar\>>> and
        weakening, (3) implies

        <\eqnarray*>
          <tformat|<table|<row|<cell|\<Phi\>\<wedge\>D\<wedge\>\<alpha\><rsub|3><wide|=|\<dot\>>\<tau\><rsub|1>\<wedge\><rsub|i>\<alpha\><rsup|1><rsub|i>\<leq\>\<alpha\><rsup|2><rsub|i>,\<Gamma\>\<Gamma\><rprime|'>>|<cell|\<vdash\>>|<cell|e:\<tau\><rsub|2>>>|<row|<cell|\<Phi\>\<wedge\>D,\<Gamma\>\<Gamma\><rprime|'>>|<cell|\<vdash\>>|<cell|m<rsub|i>:Num<around*|(|\<alpha\><rsup|1><rsub|i>|)>>>|<row|<cell|\<Phi\>\<wedge\>D,\<Gamma\>\<Gamma\><rprime|'>>|<cell|\<vdash\>>|<cell|n<rsub|i>:Num<around*|(|\<alpha\><rsup|2><rsub|i>|)>>>>>
        </eqnarray*>

        <item>By weakening, (4) implies <math|\<Phi\>\<vdash\>p:\<alpha\><rsub|3>\<longrightarrow\>\<exists\><wide|\<beta\>|\<bar\>><around|[|D|]>\<Gamma\><rprime|'>>.

        <item>By (5), (6), (1), and <name|NegClause>, we obtain
        <math|\<Phi\>,\<Gamma\>\<vdash\>p
        <text|<with|font-shape|condensed|<strong|when>>>
        \<wedge\><rsub|i>m<rsub|i>\<leqslant\>n<rsub|i>.e:\<tau\>>.

        <item>By (7) and <name|Hide>, we get the goal.
      </enumerate>
    </itemize>
  </proof>

  <math|\<Gamma\><rprime|'><wide|=|\<dot\>>\<Gamma\><rprime|''>> stands for
  <math|\<forall\>x\<in\>Dom<around|(|\<Gamma\><rprime|'>|)>\<cup\>Dom<around|(|\<Gamma\><rprime|''>|)>.\<Gamma\><rprime|'><around|(|x|)><wide|=|\<dot\>>\<Gamma\><rprime|''><around|(|x|)>>
  and is false when <math|Dom<around|(|\<Gamma\><rprime|'>|)>\<neq\>Dom<around|(|\<Gamma\><rprime|''>|)>>.
  Recall that for <math|\<Delta\>\<assign\>\<exists\><wide|\<beta\>|\<bar\>><around|[|D|]>.\<Gamma\>>
  and <math|\<Delta\><rprime|'>\<assign\>\<exists\><wide|\<beta\>|\<bar\>><rprime|'><around|[|D<rprime|'>|]>.\<Gamma\><rprime|'>>
  such that <math|<wide|\<beta\>|\<bar\>>#FV<around|(|\<Gamma\><rprime|'>|)>>,
  <math|<wide|\<beta\>|\<bar\>><rprime|'>#FV<around|(|\<Delta\>|)>> and
  <math|<wide|\<beta\>|\<bar\>><rprime|'>#C>,
  <math|C\<vDash\>\<Delta\><rprime|'>\<leqslant\>\<Delta\>> denotes
  <math|C\<wedge\>D<rprime|'>\<vDash\>\<exists\><wide|\<beta\>|\<bar\>>.D\<wedge\>\<Gamma\><wide|=|\<dot\>>\<Gamma\><rprime|'>>.
  Observe, that <math|C\<vDash\>\<Delta\><rprime|'>\<leqslant\>\<Delta\>> iff
  <math|C\<vDash\>\<forall\><wide|\<beta\>|\<bar\>><rprime|'>.D<rprime|'>\<Rightarrow\>\<exists\><wide|\<beta\>|\<bar\>>.D\<wedge\>\<Gamma\><wide|=|\<dot\>>\<Gamma\><rprime|'>>.

  <\lemma>
    <label|CompletePat><em|Completeness> (patterns). Let
    <math|\<Delta\>=\<exists\><wide|\<beta\>|\<bar\>><rprime|'><around|[|D<rprime|'>|]>\<Gamma\><rprime|'>>
    and <math|<around*|\<llbracket\>|\<vdash\>p\<uparrow\>\<tau\>|\<rrbracket\>>=\<exists\><wide|\<beta\>|\<bar\>><rprime|''><around|[|D<rprime|''>|]>\<Gamma\><rprime|''>=\<Delta\><rprime|'>>.
    <math|C\<vdash\>p:\<tau\>\<longrightarrow\>\<Delta\>> implies
    <math|C\<vDash\><around*|\<llbracket\>|\<vdash\>p\<downarrow\>\<tau\>|\<rrbracket\>>>
    and <math|C\<vDash\>\<forall\><wide|\<beta\>|\<bar\>><rprime|''>.D<rprime|''>\<Rightarrow\>\<exists\><wide|\<beta\>|\<bar\>><rprime|'>.<around*|(|D<rprime|'>\<wedge\>\<Gamma\><rprime|''><wide|=|\<dot\>>\<Gamma\><rprime|'>|)>>,
    i.e. <math|C\<vDash\>\<Delta\><rprime|'>\<leqslant\>\<Delta\>>.
  </lemma>

  <\proof>
    By induction on the derivation of <math|C\<vdash\>p:\<tau\>\<longrightarrow\>\<Delta\>>.
    To slightly simplify the proof, the induction is actually on the
    lexicographic ordering: (# of applications of <name|p-Cstr>, # of other
    rules applications).

    <\itemize>
      <item>Cases <name|p-Empty>, <name|p-Wild>, <name|p-Var>.
      <math|<around*|\<llbracket\>|\<vdash\>p\<downarrow\>\<tau\>|\<rrbracket\>>=\<b-T\>>.
      <math|<around*|\<llbracket\>|\<vdash\>p\<uparrow\>\<tau\>|\<rrbracket\>>>
      and <math|\<Delta\>> coincide: <math|\<Gamma\><rprime|''>=\<Gamma\><rprime|'>>,
      <math|D<rprime|'>=D<rprime|''>=\<b-T\>> and
      <math|\<vDash\>\<exists\><wide|\<beta\>|\<bar\>>.\<Gamma\><rprime|'><wide|=|\<dot\>>\<Gamma\><rprime|'>>
      holds because sorts are nonempty.

      <item>Case <name|p-And>. In this case
      <math|\<Delta\>=\<Delta\><rsub|1>\<times\>\<Delta\><rsub|2>,<wide|\<beta\>|\<bar\>><rprime|'>=<wide|\<beta\>|\<bar\>><rsub|1><rprime|'><wide|\<beta\>|\<bar\>><rsub|2><rprime|'>,D<rprime|'>=D<rsub|1><rprime|'>\<wedge\>D<rsub|2><rprime|'>,\<Gamma\><rprime|'>=\<Gamma\><rsub|1><rprime|'><wide|\<cup\>|\<dot\>>\<Gamma\><rsub|2><rprime|'>>.

      <\enumerate>
        <item><name|p-And>'s premises are
        <math|C\<vdash\>p<rsub|i>:\<tau\>\<longrightarrow\>\<Delta\><rsub|i>>,
        which by induction hypothesis gives
        <math|C\<vDash\><around*|\<llbracket\>|\<vdash\>p<rsub|i>\<downarrow\>\<tau\>|\<rrbracket\>>>
        and <math|C\<vDash\>\<forall\><wide|\<beta\>|\<bar\>><rprime|''><rsub|i>.D<rsub|i><rprime|''>\<Rightarrow\>\<exists\><wide|\<beta\>|\<bar\>><rsub|i><rprime|'>.<around*|(|D<rsub|i><rprime|'>\<wedge\>\<Gamma\><rsub|i><rprime|''><wide|=|\<dot\>>\<Gamma\><rsub|i><rprime|'>|)>>
        for <math|i=1,2>.

        <item>(1) gives <math|C\<vDash\><around*|\<llbracket\>|\<vdash\>p<rsub|1>\<wedge\>p<rsub|2>\<downarrow\>\<tau\><around*|\<rrbracket\>||\<nobracket\>>|\<nobracket\>>>
        as <math|<around*|\<llbracket\>|\<vdash\>p<rsub|1>\<wedge\>p<rsub|2>\<downarrow\>\<tau\><around*|\<rrbracket\>|=<around*|\<llbracket\>|\<vdash\>p<rsub|1>\<downarrow\>\<tau\>|\<rrbracket\>>\<wedge\><around*|\<llbracket\>|\<vdash\>p<rsub|2>\<downarrow\>\<tau\>|\<rrbracket\>>|\<nobracket\>>|\<nobracket\>>>.

        <item><math|<around*|\<llbracket\>|\<vdash\>p<rsub|1>\<wedge\>p<rsub|2>\<uparrow\>\<tau\><around*|\<rrbracket\>|=<around*|\<llbracket\>|\<vdash\>p<rsub|1>\<uparrow\>\<tau\><around*|\<rrbracket\>|\<times\><around*|\<llbracket\>|\<vdash\>p<rsub|2>\<uparrow\>\<tau\><around*|\<rrbracket\>|=\<exists\><wide|\<beta\>|\<bar\>><rprime|''><rsub|1><wide|\<beta\>|\<bar\>><rsub|2><rprime|''><around|[|D<rsub|1><rprime|''>\<wedge\>D<rsub|2><rprime|''>|]>\<Gamma\><rsub|1><rprime|''><wide|\<cup\>|\<dot\>>\<Gamma\><rsub|2><rprime|''>|\<nobracket\>>|\<nobracket\>>|\<nobracket\>>|\<nobracket\>>|\<nobracket\>>|\<nobracket\>>>.
        We will show <math|C\<vDash\>\<forall\><wide|\<beta\>|\<bar\>><rsub|1><rprime|''><wide|\<beta\>|\<bar\>><rsub|2><rprime|''>.D<rsub|1><rprime|''>\<wedge\>D<rsub|2><rprime|''>\<Rightarrow\>\<exists\><wide|\<beta\>|\<bar\>><rsub|1><rprime|'><wide|\<beta\>|\<bar\>><rsub|2><rprime|'>.<around*|(|D<rsub|1><rprime|'>\<wedge\>D<rsub|2><rprime|'>\<wedge\>\<Gamma\><rsub|1><rprime|''><wide|\<cup\>|\<dot\>>\<Gamma\><rsub|2><rprime|''><wide|=|\<dot\>>\<Gamma\><rsub|1><rprime|'><wide|\<cup\>|\<dot\>>\<Gamma\><rsub|2><rprime|'>|)>>.

        <item>Assume w.l.o.g. <math|<wide|\<beta\>|\<bar\>><rsub|1><rprime|'>#<wide|\<beta\>|\<bar\>><rsub|2><rprime|'>>,
        <math|<wide|\<beta\>|\<bar\>><rsub|1><rprime|''>#<wide|\<beta\>|\<bar\>><rsub|2><rprime|''>>.
        Applying (1) for <math|i=1,2> gives
        <math|C\<vDash\>\<forall\><wide|\<beta\>|\<bar\>><rsub|1><rprime|''><wide|\<beta\>|\<bar\>><rsub|2><rprime|''>.D<rsub|1><rprime|''>\<wedge\>D<rsub|2><rprime|''>\<Rightarrow\>\<exists\><wide|\<beta\>|\<bar\>><rsub|1><rprime|'><wide|\<beta\>|\<bar\>><rsub|2><rprime|'>.<around*|(|D<rsub|1><rprime|'>\<wedge\>D<rsub|2><rprime|'>\<wedge\>\<Gamma\><rsub|1><rprime|''><wide|=|\<dot\>>\<Gamma\><rsub|1><rprime|'>\<wedge\>\<Gamma\><rsub|2><rprime|''><wide|=|\<dot\>>\<Gamma\><rsub|2><rprime|'>|)>>,
        which completes the goal.
      </enumerate>

      <item>Case <name|p-Cstr>. In this case
      <math|\<Delta\>=\<exists\><wide|\<beta\>|\<bar\>><rsub|0><around|[|D<rsub|0>|]><around|(|\<Delta\><rsub|1>\<times\>\<ldots\>\<times\>\<Delta\><rsub|n>|)>>,
      and <math|\<tau\>=\<varepsilon\><around|(|<wide|\<alpha\>|\<bar\>><rsub|0>|)>>,
      where <math|D<rsub|0>\<assign\>D<rsub|K><around|[|<wide|\<alpha\>|\<bar\>><wide|\<beta\>|\<bar\>>\<assign\><wide|\<alpha\>|\<bar\>><rsub|0><wide|\<beta\>|\<bar\>><rsub|0>|]>>
      for <math|\<Sigma\>\<ni\>K\<colons\>\<forall\><wide|\<alpha\>|\<bar\>><wide|\<beta\>|\<bar\>><around|[|D<rsub|K>|]>.\<tau\><rsub|1>\<times\>\<ldots\>\<times\>\<tau\><rsub|n>\<rightarrow\>\<varepsilon\><around|(|<wide|\<alpha\>|\<bar\>>|)>>
      and <math|<wide|\<beta\>|\<bar\>><rsub|0>#FV<around|(|C|)>>.

      <\enumerate>
        <item><name|p-Cstr>'s premises are <math|
        C\<wedge\>D<rsub|0>\<vdash\>p<rsub|i>:\<tau\><rsub|i><around|[|<wide|\<alpha\>|\<bar\>><wide|\<beta\>|\<bar\>>\<assign\><wide|\<alpha\>|\<bar\>><rsub|0><wide|\<beta\>|\<bar\>><rsub|0>|]>\<longrightarrow\>\<Delta\><rsub|i>>.

        <item>Let <math|<wide|\<alpha\>|\<bar\>><rsub|0><rprime|'><wide|\<beta\>|\<bar\>><rsub|0><rprime|'>#FV<around|(|\<tau\>,<wide|\<alpha\>|\<bar\>><wide|\<beta\>|\<bar\>>,<wide|\<alpha\>|\<bar\>><rsub|0><wide|\<beta\>|\<bar\>><rsub|0>,C|)>>.

        <item>Let <math|\<tau\><rsub|i><rprime|'>\<assign\>\<tau\><rsub|i><around|[|<wide|\<alpha\>|\<bar\>><wide|\<beta\>|\<bar\>>\<assign\><wide|\<alpha\>|\<bar\>><rsub|0><rprime|'><wide|\<beta\>|\<bar\>><rsub|0><rprime|'>|]>>.
        By weakening and <name|p-EqIn>, (1) gives <math|
        C\<wedge\>D<rsub|0>\<wedge\><wide|\<alpha\>|\<bar\>><rsub|0><wide|\<beta\>|\<bar\>><rsub|0><wide|=|\<dot\>><wide|\<alpha\>|\<bar\>><rsub|0><rprime|'><wide|\<beta\>|\<bar\>><rsub|0><rprime|'>\<vdash\>p<rsub|i>:\<tau\><rsub|i><rprime|'>\<longrightarrow\>\<Delta\><rsub|i>>.

        <item>By induction hypothesis we have
        <math|C\<wedge\>D<rsub|0>\<wedge\><wide|\<alpha\>|\<bar\>><rsub|0><wide|\<beta\>|\<bar\>><rsub|0><wide|=|\<dot\>><wide|\<alpha\>|\<bar\>><rsub|0><rprime|'><wide|\<beta\>|\<bar\>><rsub|0><rprime|'>\<vDash\><around*|\<llbracket\>|\<vdash\>p<rsub|i>\<downarrow\>\<tau\><rsub|i><rprime|'>|\<rrbracket\>>>
        and <math|C\<wedge\>D<rsub|0>\<wedge\><wide|\<alpha\>|\<bar\>><rsub|0><wide|\<beta\>|\<bar\>><rsub|0><wide|=|\<dot\>><wide|\<alpha\>|\<bar\>><rsub|0><rprime|'><wide|\<beta\>|\<bar\>><rsub|0><rprime|'>\<vDash\>\<forall\><wide|\<beta\>|\<bar\>><rsub|i><rprime|''>.D<rsub|i><rprime|''>\<Rightarrow\>\<exists\><wide|\<beta\>|\<bar\>><rsub|i><rprime|'>.<around*|(|D<rsub|i><rprime|'>\<wedge\>\<Gamma\><rsub|i><rprime|''><wide|=|\<dot\>>\<Gamma\><rsub|i><rprime|'>|)>>
        for <math|i=1,\<ldots\>,n>.

        <item>Let <math|D<rsub|0><rprime|'>\<assign\>D<rsub|K><around|[|<wide|\<alpha\>|\<bar\>><wide|\<beta\>|\<bar\>>\<assign\><wide|\<alpha\>|\<bar\>><rsub|0><rprime|'><wide|\<beta\>|\<bar\>><rsub|0><rprime|'>|]>>.
        From (4) follows <math|C\<wedge\><wide|\<alpha\>|\<bar\>><rsub|0><wide|\<beta\>|\<bar\>><rsub|0><wide|=|\<dot\>><wide|\<alpha\>|\<bar\>><rsub|0><rprime|'><wide|\<beta\>|\<bar\>><rsub|0><rprime|'>\<vDash\>D<rsub|0><rprime|'>\<Rightarrow\>\<wedge\><rsub|i><around*|\<llbracket\>|\<vdash\>p<rsub|i>\<downarrow\>\<tau\><rsub|i><rprime|'>|\<rrbracket\>>>.

        <item>W.l.o.g. <math|<wide|\<alpha\>|\<bar\>><rsub|0><wide|\<beta\>|\<bar\>><rsub|0>#FV<around|(|D<rsub|0><rprime|'>\<Rightarrow\>\<wedge\><rsub|i><around*|\<llbracket\>|\<vdash\>p<rsub|i>\<downarrow\>\<tau\><rsub|i><rprime|'>|\<rrbracket\>>|)>>.
        (5) gives <math|C\<wedge\><wide|\<alpha\>|\<bar\>><rsub|0><wide|=|\<dot\>><wide|\<alpha\>|\<bar\>><rsub|0><rprime|'>\<vDash\>\<forall\><wide|\<beta\>|\<bar\>><rsub|0><rprime|'>.D<rsub|0><rprime|'>\<Rightarrow\>\<wedge\><rsub|i><around*|\<llbracket\>|\<vdash\>p<rsub|i>\<downarrow\>\<tau\><rsub|i><rprime|'>|\<rrbracket\>>>
        because we can drop <math|<wide|\<beta\>|\<bar\>><rsub|0><wide|=|\<dot\>><wide|\<beta\>|\<bar\>><rsub|0><rprime|'>>
        from premises.

        <item>(6) is equivalent to <math|C\<wedge\><wide|\<alpha\>|\<bar\>><rsub|0><wide|=|\<dot\>><wide|\<alpha\>|\<bar\>><rsub|0><rprime|'>\<vDash\>\<varepsilon\><around|(|<wide|\<alpha\>|\<bar\>><rsub|0>|)><wide|=|\<dot\>>\<varepsilon\><around|(|<wide|\<alpha\>|\<bar\>><rsub|0><rprime|'>|)>\<wedge\>\<forall\><wide|\<beta\>|\<bar\>><rsub|0><rprime|'>.D<rsub|0><rprime|'>\<Rightarrow\>\<wedge\><rsub|i><around*|\<llbracket\>|p<rsub|i>\<downarrow\>\<tau\><rsub|i><rprime|'>|\<rrbracket\>>>
        which by the nonempty domain property implies
        <math|C\<wedge\><wide|\<alpha\>|\<bar\>><rsub|0><wide|=|\<dot\>><wide|\<alpha\>|\<bar\>><rsub|0><rprime|'>\<vDash\>\<exists\><wide|\<alpha\>|\<bar\>><rsub|0><rprime|'>.\<varepsilon\><around|(|<wide|\<alpha\>|\<bar\>><rsub|0>|)><wide|=|\<dot\>>\<varepsilon\><around|(|<wide|\<alpha\>|\<bar\>><rsub|0><rprime|'>|)>\<wedge\>\<forall\><wide|\<beta\>|\<bar\>><rsub|0><rprime|'>.D<rsub|0><rprime|'>\<Rightarrow\>\<wedge\><rsub|i><around*|\<llbracket\>|\<vdash\>p<rsub|i>\<downarrow\>\<tau\><rsub|i><rprime|'>|\<rrbracket\>>>.

        <item>Because by (6) we can drop <math|<wide|\<alpha\>|\<bar\>><rsub|0><wide|=|\<dot\>><wide|\<alpha\>|\<bar\>><rsub|0><rprime|'>>
        from premises, (7) is equivalent to
        <math|C\<vDash\>\<exists\><wide|\<alpha\>|\<bar\>><rsub|0><rprime|'>.\<varepsilon\><around|(|<wide|\<alpha\>|\<bar\>><rsub|0>|)><wide|=|\<dot\>>\<varepsilon\><around|(|<wide|\<alpha\>|\<bar\>><rsub|0><rprime|'>|)>\<wedge\>\<forall\><wide|\<beta\>|\<bar\>><rsub|0><rprime|'>.D<rsub|0><rprime|'>\<Rightarrow\>\<wedge\><rsub|i><around*|\<llbracket\>|\<vdash\>p<rsub|i>\<downarrow\>\<tau\><rsub|i><rprime|'>|\<rrbracket\>>>,
        which is the first part of the goal.

        <item>From (4), <math|C\<wedge\><wide|\<alpha\>|\<bar\>><rsub|0><wide|\<beta\>|\<bar\>><rsub|0><wide|=|\<dot\>><wide|\<alpha\>|\<bar\>><rsub|0><rprime|'><wide|\<beta\>|\<bar\>><rsub|0><rprime|'>\<vDash\>D<rsub|0><rprime|'>\<Rightarrow\>\<forall\><wide|\<beta\>|\<bar\>><rsub|1><rprime|''>\<ldots\><wide|\<beta\>|\<bar\>><rsub|n><rprime|''>.\<wedge\><rsub|i>D<rsub|i><rprime|''>\<Rightarrow\>\<exists\><wide|\<beta\>|\<bar\>><rsub|1><rprime|'>\<ldots\><wide|\<beta\>|\<bar\>><rsub|n><rprime|'>.\<wedge\><rsub|i><around*|(|D<rsub|i><rprime|'>\<wedge\>\<Gamma\><rsub|i><rprime|''><wide|=|\<dot\>>\<Gamma\><rsub|i><rprime|'>|)>>.

        <item>From (9) by (2) and (6), <math|C\<vDash\>\<forall\><wide|\<alpha\>|\<bar\>><rsub|0><rprime|'><wide|\<beta\>|\<bar\>><rsub|0><rprime|'>.<wide|\<alpha\>|\<bar\>><rsub|0><wide|\<beta\>|\<bar\>><rsub|0><wide|=|\<dot\>><wide|\<alpha\>|\<bar\>><rsub|0><rprime|'><wide|\<beta\>|\<bar\>><rsub|0><rprime|'>\<wedge\>D<rsub|0><rprime|'>\<Rightarrow\>\<forall\><wide|\<beta\>|\<bar\>><rsub|1><rprime|''>\<ldots\><wide|\<beta\>|\<bar\>><rsub|n><rprime|''>.\<wedge\><rsub|i>D<rsub|i><rprime|''>\<Rightarrow\>\<exists\><wide|\<beta\>|\<bar\>><rsub|1><rprime|'>\<ldots\><wide|\<beta\>|\<bar\>><rsub|n><rprime|'>.\<wedge\><rsub|i><around*|(|D<rsub|i><rprime|'>\<wedge\>\<Gamma\><rsub|i><rprime|''><wide|=|\<dot\>>\<Gamma\><rsub|i><rprime|'>|)>>,
        which is equivalent to

        <\equation*>
          C\<vDash\>\<forall\><wide|\<alpha\>|\<bar\>><rsub|0><rprime|'><wide|\<beta\>|\<bar\>><rsub|0><rprime|'><wide|\<beta\>|\<bar\>><rsub|1><rprime|''>\<ldots\><wide|\<beta\>|\<bar\>><rsub|n><rprime|''>.<wide|\<alpha\>|\<bar\>><rsub|0><wide|\<beta\>|\<bar\>><rsub|0><wide|=|\<dot\>><wide|\<alpha\>|\<bar\>><rsub|0><rprime|'><wide|\<beta\>|\<bar\>><rsub|0><rprime|'>\<wedge\>D<rsub|0><rprime|'>\<wedge\><rsub|i>D<rsub|i><rprime|''>\<Rightarrow\><with|mode|text|
          \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ ><with|mode|text|<next-line>
          \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ >\<exists\><wide|\<beta\>|\<bar\>><rsub|1><rprime|'>\<ldots\><wide|\<beta\>|\<bar\>><rsub|n><rprime|'>.\<wedge\><rsub|i><around*|(|D<rsub|i><rprime|'>\<wedge\><no-break>\<Gamma\><rsub|i><rprime|''><wide|=|\<dot\>>\<Gamma\><rsub|i><rprime|'>|)>
        </equation*>

        <item>Observe, that w.l.o.g. <math|<wide|\<beta\>|\<bar\>><rprime|''>\<assign\><wide|\<alpha\>|\<bar\>><rsub|0><rprime|'><wide|\<beta\>|\<bar\>><rsub|0><rprime|'><wide|\<beta\>|\<bar\>><rsub|1><rprime|''>\<ldots\><wide|\<beta\>|\<bar\>><rsub|n><rprime|''>>.
        Note by definition of <math|<around*|\<llbracket\>|\<vdash\>p\<uparrow\>\<tau\>|\<rrbracket\>>>,
        that <math|D<rprime|''>=\<varepsilon\><around|(|<wide|\<alpha\>|\<bar\>><rsub|0>|)><wide|=|\<dot\>>\<varepsilon\><around|(|<wide|\<alpha\>|\<bar\>><rsub|0><rprime|'>|)>\<wedge\>D<rsub|0><rprime|'>\<wedge\><rsub|i>D<rsub|i><rprime|''>>.
        By the free generation property, <math|\<vDash\>D<rprime|''>\<Rightarrow\><wide|\<alpha\>|\<bar\>><rsub|0><wide|=|\<dot\>><wide|\<alpha\>|\<bar\>><rsub|0><rprime|'>>.

        <item>Observe, that <math|\<Gamma\><rprime|''><wide|=|\<dot\>>\<Gamma\><rprime|'>\<equiv\>\<wedge\><rsub|i><around*|(|\<Gamma\><rsub|i><rprime|''><wide|=|\<dot\>>\<Gamma\><rsub|i><rprime|'>|)>>
        and <math|D<rprime|'>=D<rsub|0>\<wedge\><rsub|i>D<rsub|i><rprime|'>>.
        (10) and (11) imply

        <\equation*>
          C\<vDash\>\<forall\><wide|\<beta\>|\<bar\>><rprime|''>.<wide|\<beta\>|\<bar\>><rsub|0><wide|=|\<dot\>><wide|\<beta\>|\<bar\>><rsub|0><rprime|'>\<wedge\>D<rprime|''>\<Rightarrow\>\<exists\><wide|\<beta\>|\<bar\>><rsub|1><rprime|'>\<ldots\><wide|\<beta\>|\<bar\>><rsub|n><rprime|'>.D<rprime|'>\<wedge\>\<Gamma\><rprime|''><wide|=|\<dot\>>\<Gamma\><rprime|'>
        </equation*>

        <item>Also, <math|<wide|\<beta\>|\<bar\>><rprime|'>=<wide|\<beta\>|\<bar\>><rsub|0><wide|\<beta\>|\<bar\>><rsub|1><rprime|'>\<ldots\><wide|\<beta\>|\<bar\>><rsub|n><rprime|'>>.
        Because <math|<wide|\<beta\>|\<bar\>><rsub|0>#FV<around|(|D<rprime|''>|)>>,
        because sorts are nonempty (12) gives
        <math|C\<vDash\>\<forall\><wide|\<beta\>|\<bar\>><rprime|''>.<wide|\<alpha\>|\<bar\>><rsub|0><wide|=|\<dot\>><wide|\<alpha\>|\<bar\>><rsub|0><rprime|'>\<wedge\>D<rprime|''>\<Rightarrow\>\<exists\><wide|\<beta\>|\<bar\>><rprime|'>.D<rprime|'>\<wedge\>\<Gamma\><rprime|''><wide|=|\<dot\>>\<Gamma\><rprime|'>>,
        the other part of the goal.
      </enumerate>

      <item>Case <name|p-EqIn>.

      <\enumerate>
        <item><name|p-EqIn>'s premises are:
        <math|C\<vdash\>p:\<tau\><rprime|'>\<longrightarrow\>\<Delta\>>,
        which by induction hypothesis gives
        <math|C\<vDash\><around*|\<llbracket\>|\<vdash\>p\<downarrow\>\<tau\><rprime|'>|\<rrbracket\>>>
        and <math|C\<vDash\>\<Delta\><rprime|'><rsub|1>\<leqslant\>\<Delta\>>,
        for <math|\<Delta\><rsub|1><rprime|'>=\<exists\><wide|\<beta\>|\<bar\>><rsub|1><rprime|''><around|[|D<rsub|1><rprime|''>|]>\<Gamma\><rsub|1><rprime|''>>

        <item>and <math|C\<vDash\>\<tau\><wide|=|\<dot\>>\<tau\><rprime|'>>.

        <item>Observe by induction on <math|p>, that
        <math|C\<wedge\>\<tau\><wide|=|\<dot\>>\<tau\><rprime|'>\<vDash\><around*|\<llbracket\>|\<vdash\>p\<downarrow\>\<tau\><rprime|'>|\<rrbracket\>>>
        iff <math|C\<wedge\>\<tau\><wide|=|\<dot\>>\<tau\><rprime|'>\<vDash\><around*|\<llbracket\>|\<vdash\>p\<downarrow\>\<tau\>|\<rrbracket\>>>,
        which by (1) and (2) gives the first part of the goal.

        <item>Observe by induction on <math|p>, that
        <math|C\<wedge\>\<tau\><wide|=|\<dot\>>\<tau\><rprime|'>\<vDash\><around*|\<llbracket\>|\<vdash\>p\<uparrow\>\<tau\>|\<rrbracket\>>\<leqslant\><around*|\<llbracket\>|\<vdash\>p\<uparrow\>\<tau\><rprime|'>|\<rrbracket\>>>,
        i.e. <math|C\<wedge\>\<tau\><wide|=|\<dot\>>\<tau\><rprime|'>\<vDash\>\<Delta\><rprime|'>\<leqslant\>\<Delta\><rprime|'><rsub|1>>,
        which by (1), (2) and transitivity of <math|\<leqslant\>>, proves the
        second part of the goal.
      </enumerate>

      <item>Case <name|p-SubOut> follows by transitivity of
      <math|\<leqslant\>>.

      <item>Case <name|p-Hide>.

      <\enumerate>
        <item><name|p-Hide>'s premises are
        <math|C<rprime|'>\<vdash\>p:\<tau\>\<longrightarrow\>\<Delta\>> and
        <math|<wide|\<alpha\>|\<bar\>><rsub|0>#FV<around|(|\<tau\>,\<Delta\>|)>>
        for <math|C=\<exists\><wide|\<alpha\>|\<bar\>><rsub|0>.C<rprime|'>>.

        <item>By inductive hypothesis, <math|C<rprime|'>\<vDash\><around*|\<llbracket\>|\<vdash\>p\<downarrow\>\<tau\>|\<rrbracket\>>>
        and <math|C<rprime|'>\<vDash\>\<Delta\><rprime|'>\<leqslant\>\<Delta\>>.

        <item>By induction on <math|p>, <math|FV<around|(|<around*|\<llbracket\>|\<vdash\>p\<downarrow\>\<tau\>|\<rrbracket\>>|)>=FV<around|(|\<tau\>|)>>.

        <item>By (1), (2) and (3) we have
        <math|C\<vDash\><around*|\<llbracket\>|\<vdash\>p\<downarrow\>\<tau\>|\<rrbracket\>>>.

        <item>By induction on <math|p>, <math|FV<around|(|D<rprime|''>,\<Gamma\><rprime|''>|)>\<subseteq\>FV<around|(|\<tau\>|)>\<cup\><wide|\<beta\>|\<bar\>><rprime|''>>.

        <item>By (1), (2) and (3) we have
        <math|C\<vDash\>\<Delta\><rprime|'>\<leqslant\>\<Delta\>>.
      </enumerate>
    </itemize>
  </proof>

  <\lemma>
    <label|MonoEnvEq>Let <math|\<Gamma\>> be an environment and
    <math|\<Gamma\><rprime|'>,\<Gamma\><rprime|''>> be simple (i.e.
    monomorphic) environments. For any <math|e,\<tau\>>,
    <math|C\<wedge\>\<Gamma\><rprime|'><wide|=|\<dot\>>\<Gamma\><rprime|''>,\<Gamma\>\<Gamma\><rprime|'>\<vdash\>e:\<tau\>>
    iff <math|C\<wedge\>\<Gamma\><rprime|'><wide|=|\<dot\>>\<Gamma\><rprime|''>,\<Gamma\>\<Gamma\><rprime|''>\<vdash\>e:\<tau\>>.
  </lemma>

  <\proof>
    Consider a derivation of <math|C\<wedge\>\<Gamma\><rprime|'><wide|=|\<dot\>>\<Gamma\><rprime|''>,\<Gamma\>\<Gamma\><rprime|'>\<vdash\>e:\<tau\>>.
    The only case where <math|\<Gamma\><rprime|'>> is referred to, is in the
    <name|Var> rule, which for a monomorphic environment simplifies to:
    <math|\<Gamma\><rprime|'><around|(|x|)>=\<tau\><rprime|'>/C,\<Gamma\>\<Gamma\><rprime|'>\<vdash\>x:\<tau\><rprime|'>>.
    Replace <math|\<Gamma\><rprime|'>> with <math|\<Gamma\><rprime|''>> in
    judgments throughout the derivation. <math|\<Gamma\><rprime|'><around|(|x|)>=\<tau\><rprime|'>/<rsub|Var>C\<wedge\>\<Gamma\><rprime|'><wide|=|\<dot\>>\<Gamma\><rprime|''>,\<Gamma\>\<Gamma\><rprime|''>\<vdash\>x:\<tau\><rprime|'>>
    is not valid, correct it as <math|\<Gamma\><rprime|''><around|(|x|)>=\<tau\><rprime|''>/<rsub|Var>C\<wedge\>\<Gamma\><rprime|'><wide|=|\<dot\>>\<Gamma\><rprime|''>,\<Gamma\>\<Gamma\><rprime|''>\<vdash\>x:\<tau\><rprime|''>/<rsub|Equ>C\<wedge\>\<Gamma\><rprime|'><wide|=|\<dot\>>\<Gamma\><rprime|''>,\<Gamma\>\<Gamma\><rprime|''>\<vdash\>x:\<tau\><rprime|'>>.
    Analogically follows the other direction of the equivalence of
    <math|C\<wedge\>\<Gamma\><rprime|'><wide|=|\<dot\>>\<Gamma\><rprime|''>,\<Gamma\>\<Gamma\><rprime|'>\<vdash\>e:\<tau\>>
    and <math|C\<wedge\>\<Gamma\><rprime|'><wide|=|\<dot\>>\<Gamma\><rprime|''>,\<Gamma\>\<Gamma\><rprime|''>\<vdash\>e:\<tau\>>.
  </proof>

  Proof of theorem <reference|InfComplExpr>.

  <\proof>
    We proceed by induction on the derivation of
    <math|C,\<Gamma\>\<vdash\>e:\<tau\>>. To slightly simplify the proof, the
    induction is actually on the lexicographic ordering: (# of structural
    rule applications <name|Var>, <name|Cstr>, <name|Abs>, <name|App>,
    <name|LetRec>, <name|Clause>; # of nonstructural rule applications
    <name|Equ>, <name|Hide>, <name|FElim>, <name|DisjElim>). (The rules
    <name|FElim> and <name|DisjElim> are not needed when deriving the
    syntax-directed rules.)

    <\itemize>
      <item>Case <name|Var>.

      <\enumerate>
        <item><name|Var>'s first premise is
        <math|\<Gamma\><around|(|x|)>=\<forall\>\<beta\><around|[|\<exists\><wide|\<alpha\>|\<bar\>>.D|]>.\<beta\>>.

        <item><name|Var>'s second premise is <math|C\<vDash\>D>.

        <item>The goal is: <math|\<cal-I\>,C\<vDash\>\<exists\>\<beta\><rprime|'><wide|\<alpha\>|\<bar\>><rprime|'>.<around|(|D<around|[|\<beta\><wide|\<alpha\>|\<bar\>>\<assign\>\<beta\><rprime|'><wide|\<alpha\>|\<bar\>><rprime|'>|]>\<wedge\>\<beta\><rprime|'><wide|=|\<dot\>>\<tau\>|)>>,
        where w.l.o.g. <math|\<beta\><rprime|'><wide|\<alpha\>|\<bar\>><rprime|'>#FV<around|(|C,\<Gamma\>,\<tau\>,\<beta\>,<wide|\<alpha\>|\<bar\>>|)>>.

        <item>(3) follows from (2) by instantiating <math|\<beta\>> to
        <math|\<tau\>>, because we assume that all sorts in <math|\<cal-M\>>
        are non-empty. We can take an empty interpretation
        <math|\<cal-I\>=\<epsilon\>>.
      </enumerate>

      <item>Case <name|AssertFalse>. <name|AssertFalse>'s premise is
      <math|C\<vDash\>\<b-F\>>, we have the goal from
      <math|\<vDash\>\<b-F\>\<Rightarrow\>\<Phi\>> holding for any
      <math|\<Phi\>>, and transitivity of <math|\<vDash\>>.

      <item>Case <name|AssertLeq>.

      <\enumerate>
        <item><name|AssertLeq>'s premises are
        <math|C,\<Gamma\>\<vdash\>e<rsub|1>:Num<around*|(|\<tau\><rsub|1>|)>>,
        <math|C,\<Gamma\>\<vdash\>e<rsub|2>:Num<around*|(|\<tau\><rsub|2>|)>>,
        <math|C\<vDash\>\<tau\><rsub|1>\<leq\>\<tau\><rsub|2>> and
        <math|C,\<Gamma\>\<vdash\>e<rsub|3>:\<tau\>>.

        <item>Pick w.l.o.g. <math|\<alpha\><rsup|1>\<alpha\><rsup|2>\<nin\>FV<around|(|C,\<tau\><rsub|1>,\<tau\><rsub|2>,\<Gamma\>,\<tau\>|)>>.
        By rule <name|Equ>, (1) implies <math|C\<wedge\>\<alpha\><rsup|1><wide|=|\<dot\>>\<tau\><rsub|1>\<wedge\>\<alpha\><rsup|2><wide|=|\<dot\>>\<tau\><rsub|2>,\<Gamma\>\<vdash\>e<rsub|1>:Num<around*|(|\<alpha\><rsup|1>|)>>,
        <math|C\<wedge\>\<alpha\><rsup|1><wide|=|\<dot\>>\<tau\><rsub|1>\<wedge\>\<alpha\><rsup|2><wide|=|\<dot\>>\<tau\><rsub|2>,\<Gamma\>\<vdash\>e<rsub|2>:Num<around*|(|\<alpha\><rsup|2>|)>>
        and <math|C,\<Gamma\>\<vdash\>e<rsub|3>:\<tau\>>.

        <item>By induction hypothesis and weakening, (2) implies
        <math|\<cal-I\><rsub|i>,C\<wedge\>\<alpha\><rsup|1><wide|=|\<dot\>>\<tau\><rsub|1>\<wedge\>\<alpha\><rsup|2><wide|=|\<dot\>>\<tau\><rsub|2>\<wedge\>\<alpha\><rsup|1>\<leq\>\<alpha\><rsup|2>\<vDash\>\<Phi\><rsub|i>>
        for <math|\<Phi\><rsub|i>=<around*|\<llbracket\>|\<Gamma\>\<vdash\>e<rsub|i>:<no-break>Num<around*|(|\<alpha\><rsup|i>|)>|\<rrbracket\>>>,
        <math|i=1,2>, <math|\<Phi\><rsub|3>=<around*|\<llbracket\>|\<Gamma\>\<vdash\>e<rsub|3>:\<tau\>|\<rrbracket\>>>.

        <item>By (2) and nonemptiness of sorts, we have
        <math|C\<vDash\>\<exists\>\<alpha\><rsup|1>\<alpha\><rsup|2>.<around|(|C\<wedge\>\<alpha\><rsup|1><wide|=|\<dot\>>\<tau\><rsub|1>\<wedge\>\<alpha\><rsup|2><wide|=|\<dot\>>\<tau\><rsub|2>\<wedge\>\<alpha\><rsup|1>\<leq\>\<alpha\><rsup|2>|)>>.

        <item>By (3), the premise and because <math|C\<vDash\>D> implies
        <math|\<exists\>\<alpha\>.C\<vDash\>\<exists\>\<alpha\>.D>, we have
        <math|\<cal-I\><rsub|1>\<cal-I\><rsub|2>\<cal-I\><rsub|3>,\<exists\>\<alpha\><rsup|1>\<alpha\><rsup|2>.<around|(|C\<wedge\>\<alpha\><rsup|1><wide|=|\<dot\>>\<tau\><rsub|1>\<wedge\>\<alpha\><rsup|2><wide|=|\<dot\>>\<tau\><rsub|2>\<wedge\>\<alpha\><rsup|1>\<leq\>\<alpha\><rsup|2>|)>\<vDash\>\<exists\>\<alpha\>.<around|(|\<Phi\><rsub|1>\<wedge\>\<Phi\><rsub|2>\<wedge\>\<Phi\><rsub|3>|)>>.

        <item>By (4) and (5), we have the goal
        <math|\<cal-I\>,C\<vDash\><around*|\<llbracket\>|\<Gamma\>\<vdash\><text|<with|font-shape|condensed|<strong|assert
        num>>> e<rsub|1>\<leq\>e<rsub|2>;e<rsub|3>:\<tau\>|\<rrbracket\>>>
        with <math|\<cal-I\>=\<cal-I\><rsub|1>\<cal-I\><rsub|2>\<cal-I\><rsub|3>>.
      </enumerate>

      <item>Case <name|AssertEqty>.

      <\enumerate>
        <item><name|AssertEqty>'s premises are
        <math|C,\<Gamma\>\<vdash\>e<rsub|i>:\<tau\><rsub|i>> for
        <math|i=1,2,3,\<tau\><rsub|3>=\<tau\>> and
        <math|C\<vDash\>\<tau\><rsub|1><wide|=|\<dot\>>\<tau\><rsub|2>>.

        <item>Pick w.l.o.g. <math|\<alpha\><rsup|1>\<alpha\><rsup|2>\<nin\>FV<around|(|C,\<tau\><rsub|1>,\<tau\><rsub|2>,\<Gamma\>,\<tau\>|)>>.
        By rule <name|Equ>, (1) implies <math|C\<wedge\>\<alpha\><rsup|1><wide|=|\<dot\>>\<tau\><rsub|1>\<wedge\>\<alpha\><rsup|2><wide|=|\<dot\>>\<tau\><rsub|2>,\<Gamma\>\<vdash\>e<rsub|i>:\<alpha\><rsup|i>>
        for <math|i=1,2>.

        <item>By induction hypothesis and weakening, (1) and (2) imply
        <math|\<cal-I\><rsub|i>,C\<wedge\>\<alpha\><rsup|1><wide|=|\<dot\>>\<tau\><rsub|1>\<wedge\>\<alpha\><rsup|2><wide|=|\<dot\>>\<tau\><rsub|2>\<wedge\>\<alpha\><rsup|1><wide|=|\<dot\>>\<alpha\><rsup|2>\<vDash\>\<Phi\><rsub|i>>
        for <math|\<Phi\><rsub|i>=<around*|\<llbracket\>|\<Gamma\>\<vdash\>e<rsub|i>:<no-break>\<alpha\><rsup|i>|\<rrbracket\>>>,
        <math|i=1,2>, <math|\<Phi\><rsub|3>=<around*|\<llbracket\>|\<Gamma\>\<vdash\>e<rsub|3>:\<tau\>|\<rrbracket\>>>.

        <item>By (2) and nonemptiness of sorts, we have
        <math|C\<vDash\>\<exists\>\<alpha\><rsup|1>\<alpha\><rsup|2>.<around|(|C\<wedge\>\<alpha\><rsup|1><wide|=|\<dot\>>\<tau\><rsub|1>\<wedge\>\<alpha\><rsup|2><wide|=|\<dot\>>\<tau\><rsub|2>\<wedge\>\<alpha\><rsup|1><wide|=|\<dot\>>\<alpha\><rsup|2>|)>>.

        <item>By (3), the premise and because <math|C\<vDash\>D> implies
        <math|\<exists\>\<alpha\>.C\<vDash\>\<exists\>\<alpha\>.D>, we have
        <math|\<cal-I\><rsub|1>\<cal-I\><rsub|2>\<cal-I\><rsub|3>,\<exists\>\<alpha\><rsup|1>\<alpha\><rsup|2>.<around|(|C\<wedge\>\<alpha\><rsup|1><wide|=|\<dot\>>\<tau\><rsub|1>\<wedge\>\<alpha\><rsup|2><wide|=|\<dot\>>\<tau\><rsub|2>\<wedge\>\<alpha\><rsup|1><wide|=|\<dot\>>\<alpha\><rsup|2>|)>\<vDash\>\<exists\>\<alpha\>.<around|(|\<Phi\><rsub|1>\<wedge\>\<Phi\><rsub|2>\<wedge\>\<Phi\><rsub|3>|)>>.

        <item>By (4) and (5), we have the goal
        <math|\<cal-I\>,C\<vDash\><around*|\<llbracket\>|\<Gamma\>\<vdash\><text|<with|font-shape|condensed|<strong|assert
        type>>> e<rsub|1>=e<rsub|2>;e<rsub|3>:\<tau\>|\<rrbracket\>>> with
        <math|\<cal-I\>=\<cal-I\><rsub|1>\<cal-I\><rsub|2>\<cal-I\><rsub|3>>.
      </enumerate>

      <item>Case <name|RuntimeFailure>.

      <\enumerate>
        <item><name|RuntimeFailure>'s premise is
        <math|C,\<Gamma\>\<vdash\>s:String>.

        <item>By induction hypothesis, (1) implies
        <math|\<cal-I\>,C\<vDash\><around*|\<llbracket\>|\<Gamma\>\<vdash\>s:String|\<rrbracket\>>>
        and thus the goal.
      </enumerate>

      <item>Case <name|Cstr>.

      <\enumerate>
        <item><name|Cst`r>'s premises are <math|
        C,\<Gamma\>\<vdash\>e<rsub|i>:\<tau\><rsub|i>>,
        <math|i=1,\<ldots\>,n>, <math|C\<vDash\>D> and
        <math|K\<colons\>\<forall\><wide|\<alpha\>|\<bar\>><wide|\<beta\>|\<bar\>><around|[|D|]>.\<tau\><rsub|1>\<ldots\>\<tau\><rsub|n>\<rightarrow\>\<varepsilon\><around|(|<wide|\<alpha\>|\<bar\>>|)>>.
        <math|\<tau\>=\<varepsilon\><around|(|<wide|\<alpha\>|\<bar\>>|)>>.

        <item>Let w.l.o.g. <math|<wide|\<alpha\>|\<bar\>><rprime|'><wide|\<beta\>|\<bar\>><rprime|'>#FV<around|(|C,\<Gamma\>,\<tau\>|)>>.
        By weakening and <name|Equ>, (1) gives <math|
        C\<wedge\><wide|\<alpha\>|\<bar\>><rprime|'><wide|\<beta\>|\<bar\>><rprime|'><wide|=|\<dot\>><wide|\<alpha\>|\<bar\>><wide|\<beta\>|\<bar\>>,\<Gamma\>\<vdash\>e<rsub|i>:\<tau\><rsub|i><around|[|<wide|\<alpha\>|\<bar\>><wide|\<beta\>|\<bar\>>\<assign\><wide|\<alpha\>|\<bar\>><rprime|'><wide|\<beta\>|\<bar\>><rprime|'>|]>>.

        <item>Let <math|\<Phi\><rsub|i>=<around*|\<llbracket\>|\<Gamma\>\<vdash\>e<rsub|i>:\<tau\><rsub|i><around|[|<wide|\<alpha\>|\<bar\>><wide|\<beta\>|\<bar\>>\<assign\><wide|\<alpha\>|\<bar\>><rprime|'><wide|\<beta\>|\<bar\>><rprime|'>|]>|\<rrbracket\>>>.
        By induction hypothesis, <math|\<cal-I\><rsub|i>,C\<wedge\><wide|\<alpha\>|\<bar\>><rprime|'><wide|\<beta\>|\<bar\>><rprime|'><wide|=|\<dot\>><wide|\<alpha\>|\<bar\>><wide|\<beta\>|\<bar\>>\<vDash\>\<Phi\><rsub|i>>,
        <math|i=1,\<ldots\>,n>.

        <item>Observe, that (1) and (3) imply
        <math|\<cal-I\><rsub|i>,C\<wedge\><wide|\<alpha\>|\<bar\>><rprime|'><wide|\<beta\>|\<bar\>><rprime|'><wide|=|\<dot\>><wide|\<alpha\>|\<bar\>><wide|\<beta\>|\<bar\>>\<vDash\>\<wedge\><rsub|i>\<Phi\><rsub|i>\<wedge\>D<around|[|<wide|\<alpha\>|\<bar\>><wide|\<beta\>|\<bar\>>\<assign\><no-break><wide|\<alpha\>|\<bar\>><rprime|'><wide|\<beta\>|\<bar\>><rprime|'>|]>\<wedge\>\<varepsilon\><around|(|<wide|\<alpha\>|\<bar\>><rprime|'>|)><wide|=|\<dot\>>\<varepsilon\><around|(|<wide|\<alpha\>|\<bar\>>|)>>.

        <item>By non-emptiness of sorts and because the premise
        <math|PV<around*|(|C,\<Gamma\>|)>=<no-break>\<varnothing\>> gives
        disjoint domains for the <math|\<cal-I\><rsub|i>>, (4) and (2) imply
        <math|\<cal-I\><rsub|1>\<ldots\>\<cal-I\><rsub|n>,C\<vDash\>\<exists\><wide|\<alpha\>|\<bar\>><rprime|'><wide|\<beta\>|\<bar\>><rprime|'>.\<wedge\><rsub|i>\<Phi\><rsub|i>\<wedge\>D<around|[|<wide|\<alpha\>|\<bar\>><wide|\<beta\>|\<bar\>>\<assign\><wide|\<alpha\>|\<bar\>><rprime|'><wide|\<beta\>|\<bar\>><rprime|'>|]>\<wedge\>\<varepsilon\><around|(|<wide|\<alpha\>|\<bar\>><rprime|'>|)><wide|=|\<dot\>>\<varepsilon\><around|(|<wide|\<alpha\>|\<bar\>>|)>>.

        <item>By (1) and (5), <math|\<cal-I\>,C\<vDash\><around*|\<llbracket\>|\<Gamma\>\<vdash\>K
        e<rsub|1>\<ldots\>e<rsub|n>:\<tau\>|\<rrbracket\>>> for
        <math|\<cal-I\>=\<cal-I\><rsub|1>\<ldots\>\<cal-I\><rsub|n>>.
      </enumerate>

      <item>Case <name|Abs>. In this case,
      <math|\<tau\>\<assign\>\<tau\><rsub|1>\<rightarrow\>\<tau\><rsub|2>>.

      <\enumerate>
        <item><name|Abs>' premise is <math|C,\<Gamma\>\<vdash\><wide|c|\<bar\>>:\<tau\><rsub|1>\<rightarrow\>\<tau\><rsub|2>>,
        which by induction hypothesis implies
        <math|\<cal-I\><rsub|i>,C\<vDash\>\<Phi\><rsub|i>> for
        <math|\<Phi\><rsub|i>=<around*|\<llbracket\>|\<Gamma\>\<vdash\>p<rsub|i>.e<rsub|i>:\<tau\><rsub|1>\<rightarrow\>\<tau\><rsub|2>|\<rrbracket\>>>,
        <math|i=1,\<ldots\>,n>.

        <item>Let <math|\<alpha\><rsub|1>\<alpha\><rsub|2>#FV<around|(|C,\<tau\><rsub|1>,\<tau\><rsub|2>|)>>.
        Then, because sorts are nonempty,
        <math|C\<vDash\>\<exists\>\<alpha\><rsub|1>\<alpha\><rsub|2>.<around|(|C\<wedge\>\<alpha\><rsub|1><wide|=|\<dot\>>\<tau\><rsub|1>\<wedge\>\<alpha\><rsub|2><wide|=|\<dot\>>\<tau\><rsub|2>|)>>.

        <item>(1) and the premise implies
        <math|\<cal-I\><rsub|1>\<cal-I\><rsub|2>,C\<wedge\>\<alpha\><rsub|1><wide|=|\<dot\>>\<tau\><rsub|1>\<wedge\>\<alpha\><rsub|2><wide|=|\<dot\>>\<tau\><rsub|2>\<vDash\>\<wedge\><rsub|i>\<Phi\><rsub|i>\<wedge\>\<alpha\><rsub|1>\<rightarrow\>\<alpha\><rsub|2><wide|=|\<dot\>>\<tau\><rsub|1>\<rightarrow\>\<tau\><rsub|2>>.

        <item>Combining (2) and (3), <math|\<cal-I\><rsub|1>\<cal-I\><rsub|2>,C\<vDash\>\<exists\>\<alpha\><rsub|1>\<alpha\><rsub|2>.<around*|(|\<wedge\><rsub|i>\<Phi\><rsub|i>\<wedge\>\<alpha\><rsub|1>\<rightarrow\>\<alpha\><rsub|2><wide|=|\<dot\>>\<tau\><rsub|1>\<rightarrow\>\<tau\><rsub|2>|)>>.

        <item>By (1) and (4), <math|\<cal-I\><rsub|1>\<cal-I\><rsub|2>,C\<vDash\><around*|\<llbracket\>|\<Gamma\>\<vdash\>\<lambda\><wide|c|\<bar\>>:\<tau\>|\<rrbracket\>>>.
      </enumerate>

      <item>Case <name|App>.

      <\enumerate>
        <item><name|App>'s premises are <math|C,\<Gamma\>\<vdash\>e<rsub|1>:\<tau\><rprime|'>\<rightarrow\>\<tau\>>
        and <math|C,\<Gamma\>\<vdash\>e<rsub|2>:\<tau\><rprime|'>>.

        <item>Pick w.l.o.g. <math|\<alpha\>\<nin\>FV<around|(|C,\<tau\><rprime|'>,\<Gamma\>,\<tau\>|)>>.
        By rule <name|Equ>, (1) implies <math|C\<wedge\>\<alpha\><wide|=|\<dot\>>\<tau\><rprime|'>,\<Gamma\>\<vdash\>e<rsub|1>:\<alpha\>\<rightarrow\>\<tau\>>
        and <math|C\<wedge\>\<alpha\><wide|=|\<dot\>>\<tau\><rprime|'>,\<Gamma\>\<vdash\>e<rsub|2>:\<alpha\>>.

        <item>By induction hypothesis, (2) implies
        <math|\<cal-I\><rsub|i>,C\<wedge\>\<alpha\><wide|=|\<dot\>>\<tau\><rprime|'>\<vDash\>\<Phi\><rsub|i>>
        for <math|\<Phi\><rsub|i>=<around*|\<llbracket\>|\<Gamma\>\<vdash\>e<rsub|i>:\<tau\><rsub|i>|\<rrbracket\>>>,
        <math|i=1,2,\<tau\><rsub|1>\<assign\>\<tau\><rprime|'>\<rightarrow\>\<tau\>,\<tau\><rsub|2>\<assign\>\<tau\><rprime|'>>.

        <item>By (2) and nonemptiness of sorts, we have
        <math|C\<vDash\>\<exists\>\<alpha\>.<around|(|C\<wedge\>\<alpha\><wide|=|\<dot\>>\<tau\><rprime|'>|)>>.

        <item>By (3), the premise and because <math|C\<vDash\>D> implies
        <math|\<exists\>\<alpha\>.C\<vDash\>\<exists\>\<alpha\>.D>, we have
        <math|\<cal-I\><rsub|1>\<cal-I\><rsub|2>,\<exists\>\<alpha\>.<around|(|C\<wedge\>\<alpha\><wide|=|\<dot\>>\<tau\><rprime|'>|)>\<vDash\>\<exists\>\<alpha\>.<around|(|\<Phi\><rsub|1>\<wedge\>\<Phi\><rsub|2>|)>>.

        <item>By (4) and (5), we have the goal
        <math|\<cal-I\>,C\<vDash\><around*|\<llbracket\>|\<Gamma\>\<vdash\>e<rsub|1>
        e<rsub|2>:\<tau\>|\<rrbracket\>>> with
        <math|\<cal-I\>=\<cal-I\><rsub|1>\<cal-I\><rsub|2>>.
      </enumerate>

      <item>Case <name|LetRec>. Let <math|\<Gamma\><rprime|'>\<assign\>\<Gamma\><around|{|x\<mapsto\>\<sigma\>|}>>.

      <\enumerate>
        <item><name|LetRec>'s premises are
        <math|C,\<Gamma\><rprime|'>\<vdash\>e<rsub|1>:\<sigma\>>, which can
        only be derived by <name|Gen> from
        <math|C<rprime|'>\<wedge\>D,\<Gamma\><rprime|'>\<vdash\>e<rsub|1>:\<beta\>>,
        where <math|\<sigma\>=\<forall\>\<beta\><around|[|\<exists\><wide|\<alpha\>|\<bar\>>.D|]>.\<beta\>>
        and <math|C=C<rprime|'>\<wedge\>\<exists\>\<beta\><wide|\<alpha\>|\<bar\>>.D>;
        by induction hypothesis we get <math|\<cal-I\><rsub|1>,C<rprime|'>\<wedge\>D\<vDash\>\<Phi\><rsub|1>>
        for <math|\<Phi\><rsub|1>=<around*|\<llbracket\>|\<Gamma\><rprime|'>\<vdash\>e<rsub|1>:\<beta\>|\<rrbracket\>>>;

        <item>and <math|C,\<Gamma\><rprime|'>\<vdash\>e<rsub|2>:\<tau\>>; by
        induction hypothesis we get <math|\<cal-I\><rsub|2>,C\<vDash\>\<Phi\><rsub|2>>
        for <math|\<Phi\><rsub|2>=<around*|\<llbracket\>|\<Gamma\><rprime|'>\<vdash\>e<rsub|2>:\<tau\>|\<rrbracket\>>>.

        <item><math|\<beta\><wide|\<alpha\>|\<bar\>>#FV<around|(|\<Gamma\>,C<rprime|'>|)>>.
        W.l.o.g., assume additionally that
        <math|\<beta\><wide|\<alpha\>|\<bar\>>#FV<around|(|\<tau\>|)>>.

        <item><math|\<cal-I\><rsub|1>,C<rprime|'>\<vDash\>\<forall\>\<beta\>.<around|(|\<exists\><wide|\<alpha\>|\<bar\>>.D|)>\<Rightarrow\>\<Phi\><rsub|1>>
        iff <math|\<cal-I\><rsub|1>,C<rprime|'>\<vDash\><around|(|\<exists\><wide|\<alpha\>|\<bar\>>.D|)>\<Rightarrow\>\<Phi\><rsub|1>>
        iff <math|\<cal-I\><rsub|1>,C<rprime|'>\<vDash\>\<forall\><wide|\<alpha\>|\<bar\>>.D\<Rightarrow\>\<Phi\><rsub|1>>
        iff <math|\<cal-I\><rsub|1>,C<rprime|'>\<vDash\>D\<Rightarrow\>\<Phi\><rsub|1>>
        iff <math|\<cal-I\><rsub|1>,C<rprime|'>\<wedge\>D\<vDash\>\<Phi\><rsub|1>>,
        which is exactly (1).

        <item><math|\<cal-I\><rsub|2>,C<rprime|'>\<wedge\>\<exists\>\<beta\><wide|\<alpha\>|\<bar\>>.D\<vDash\>\<forall\>\<beta\>.<around|(|\<exists\><wide|\<alpha\>|\<bar\>>.D|)>\<Rightarrow\>\<Phi\><rsub|1>>
        follows from (5), <math|\<cal-I\><rsub|2>,C<rprime|'>\<wedge\>\<exists\>\<beta\><wide|\<alpha\>|\<bar\>>.D\<vDash\>\<exists\>\<beta\>.\<exists\><wide|\<alpha\>|\<bar\>>.D>,
        and <math|\<cal-I\><rsub|2>,C\<vDash\>\<Phi\><rsub|2>> is exactly
        (2).

        <item>From (4), (5) and the premise,
        <math|\<cal-I\><rsub|1>\<cal-I\><rsub|2>,C\<vDash\><around*|(|\<forall\>\<beta\>.<around|(|\<exists\><wide|\<alpha\>|\<bar\>>.D|)>\<Rightarrow\>\<Phi\><rsub|1>|)>\<wedge\><around|(|\<exists\>\<beta\>.\<exists\><wide|\<alpha\>|\<bar\>>.D|)>\<wedge\>\<Phi\><rsub|2>>.

        <item>Let <math|\<cal-I\>=\<cal-I\><rsub|1>\<cal-I\><rsub|2>;\<chi\>\<assign\>\<exists\><wide|\<alpha\>|\<bar\>>.D<around|[|\<beta\>\<assign\>\<delta\>|]>>,
        where <math|\<chi\>#PV<around*|(|\<Gamma\>,\<Phi\><rsub|1>,\<Phi\><rsub|2>|)>>.
        (6) gives <math|\<cal-I\>,C\<vDash\><around*|(|\<forall\>\<beta\>.\<chi\><around*|(|\<beta\>|)>\<Rightarrow\>\<Phi\><rsub|1>|)>\<wedge\><around|(|\<exists\>\<beta\>.\<chi\><around*|(|\<beta\>|)>|)>\<wedge\>\<Phi\><rsub|2>>,
        which is <math|\<cal-I\>,<no-break>C\<vDash\><around*|\<llbracket\>|\<Gamma\>\<vdash\><text|<with|font-shape|condensed|<strong|let
        rec>>> x=e<rsub|1> <text|<with|font-shape|condensed|<strong|in>>>
        e<rsub|2>:\<tau\>|\<rrbracket\>>>.
      </enumerate>

      <item>Case <name|Clause>.

      <\enumerate>
        <item><name|Clause>'s premises are:
        <math|C\<vdash\>p:\<tau\><rsub|1>\<longrightarrow\>\<exists\><wide|\<beta\>|\<bar\>><around|[|D|]>\<Gamma\><rprime|'>>,

        <item><math|C\<wedge\>D\<wedge\><rsub|i>\<tau\><rsup|m<rsub|i>>\<leq\>\<tau\><rsup|n<rsub|i>>,\<Gamma\>\<Gamma\><rprime|'>\<vdash\>e:\<tau\><rsub|2>>,

        <item><math|C\<wedge\>D,\<Gamma\>\<Gamma\><rprime|'>\<vdash\>m<rsub|i>:Num<around*|(|\<tau\><rsup|m<rsub|i>>|)>>
        and <math|C\<wedge\>D,\<Gamma\>\<Gamma\><rprime|'>\<vdash\>n<rsub|i>:Num<around*|(|\<tau\><rsup|n<rsub|i>>|)>>,

        <item>and <math|<wide|\<beta\>|\<bar\>>#FV<around|(|C,\<Gamma\>,\<tau\><rsub|2>|)>>.

        <item>Assume w.l.o.g. that <math|<wide|\<beta\>|\<bar\>>#FV<around|(|\<tau\><rsub|1>|)>>.

        <item>Let <math|\<alpha\><rsub|i><rsup|1>\<alpha\><rsub|i><rsup|2>#FV<around|(|C,\<tau\><rsub|1>,\<tau\><rsub|2>,<wide|\<tau\><rsup|m<rsub|i>>,\<tau\><rsup|n<rsub|i>>|\<bar\>>|)>>.

        <item>Let <math|<around*|\<llbracket\>|\<vdash\>p\<uparrow\>\<tau\><rsub|1>|\<rrbracket\>>=\<exists\><wide|\<beta\><rprime|'>|\<bar\>><around|[|D<rprime|'>|]>\<Gamma\><rprime|''>>,
        where <math|<wide|\<beta\><rprime|'>|\<bar\>>#FV<around*|(|\<Gamma\>,C,\<tau\><rsub|1>,\<tau\><rsub|2>,<wide|\<beta\>|\<bar\>>|)>>.

        <item>By lemma <reference|CompletePat>, (1) and (7) gives
        <math|C\<vDash\><around*|\<llbracket\>|\<vdash\>p\<downarrow\>\<tau\><rsub|1>|\<rrbracket\>>>

        <item>and <math|C\<vDash\>\<forall\><wide|\<beta\><rprime|'>|\<bar\>>.D<rprime|'>\<Rightarrow\>\<exists\><wide|\<beta\>|\<bar\>>.D\<wedge\>\<Gamma\><rprime|''><wide|=|\<dot\>>\<Gamma\><rprime|'>>,
        which is equivalent to <math|C\<wedge\>D<rprime|'>\<vDash\>\<exists\><wide|\<beta\>|\<bar\>>.D\<wedge\>\<Gamma\><rprime|''><wide|=|\<dot\>>\<Gamma\><rprime|'>>.

        <item>Recall that <math|<around*|\<llbracket\>|\<Gamma\>\<vdash\>p
        <text|<with|font-shape|condensed|<strong|when>>>
        \<wedge\><rsub|i>m<rsub|i>\<leqslant\>n<rsub|i>.e:\<tau\><rsub|1>\<rightarrow\>\<tau\><rsub|2>|\<rrbracket\>>=\<exists\><wide|\<alpha\><rsup|1><rsub|i>\<alpha\><rsup|2><rsub|i>|\<bar\>>.\<Phi\>>,
        for <math|\<Phi\>=<next-line><around*|\<llbracket\>|\<vdash\>p\<downarrow\>\<tau\><rsub|1>|\<rrbracket\>>\<wedge\>\<forall\><wide|\<beta\>|\<bar\>><rprime|'>.D<rprime|'>\<Rightarrow\>\<wedge\><rsub|i><around*|\<llbracket\>|\<Gamma\>\<Gamma\><rprime|''>\<vdash\>m<rsub|i>:Num<around*|(|\<alpha\><rsup|1><rsub|i>|)>|\<rrbracket\>>\<wedge\><rsub|i><around*|\<llbracket\>|\<Gamma\>\<Gamma\><rprime|''>\<vdash\>n<rsub|i>:Num<around*|(|\<alpha\><rsup|2><rsub|i>|)>|\<rrbracket\>>\<wedge\><around*|(|\<wedge\><rsub|i>\<alpha\><rsup|1><rsub|i>\<leq\>\<alpha\><rsup|2><rsub|i>\<Rightarrow\><around*|\<llbracket\>|\<Gamma\>\<Gamma\><rprime|''>\<vdash\>e:\<tau\><rsub|2>|\<rrbracket\>>|)>>.

        <item>By lemma <reference|MonoEnvEq>, weakening and <name|Equ>, (3)
        implies <math|C\<wedge\>D\<wedge\>\<Gamma\><rprime|''><wide|=|\<dot\>>\<Gamma\><rprime|'>\<wedge\>\<alpha\><rsup|1><rsub|i><wide|=|\<dot\>>\<tau\><rsup|m<rsub|i>>,\<Gamma\>\<Gamma\><rprime|''>\<vdash\>m<rsub|i>:Num<around*|(|\<alpha\><rsup|1><rsub|i>|)>>
        and <math|C\<wedge\>D\<wedge\>\<Gamma\><rprime|''><wide|=|\<dot\>>\<Gamma\><rprime|'>\<wedge\>\<alpha\><rsup|2><rsub|i><wide|=|\<dot\>>\<tau\><rsup|n<rsub|i>>,\<Gamma\>\<Gamma\><rprime|''>\<vdash\>n<rsub|i>:Num<around*|(|\<alpha\><rsup|2><rsub|i>|)>>.

        <item>From (9) we have <math|C\<wedge\>D<rprime|'>\<wedge\>\<alpha\><rsup|1><rsub|i><wide|=|\<dot\>>\<tau\><rsup|m<rsub|i>><rprime|'>\<vDash\>\<exists\><wide|\<beta\>|\<bar\>>.D\<wedge\>\<Gamma\><rprime|''><wide|=|\<dot\>>\<Gamma\><rprime|'>\<wedge\>\<alpha\><rsup|1><rsub|i><wide|=|\<dot\>>\<tau\><rsup|m<rsub|i>>>
        and <math|C\<wedge\>D<rprime|'>\<wedge\>\<alpha\><rsup|2><rsub|i><wide|=|\<dot\>>\<tau\><rsup|n<rsub|i>><rprime|'>\<vDash\>\<exists\><wide|\<beta\>|\<bar\>>.D\<wedge\>\<Gamma\><rprime|''><wide|=|\<dot\>>\<Gamma\><rprime|'>\<wedge\>\<alpha\><rsup|2><rsub|i><wide|=|\<dot\>>\<tau\><rsup|n<rsub|i>>>
        for some <math|\<tau\><rsup|m<rsub|i>><rprime|'>,\<tau\><rsup|n<rsub|i>><rprime|'>>.

        <item>By (11), <name|Hide> and (12), we get
        <math|C\<wedge\>D<rprime|'>\<wedge\>\<alpha\><rsup|1><rsub|i><wide|=|\<dot\>>\<tau\><rsup|m<rsub|i>><rprime|'>,\<Gamma\>\<Gamma\><rprime|''>\<vdash\>m<rsub|i>:Num<around*|(|\<alpha\><rsup|1><rsub|i>|)>>
        and <math|C\<wedge\>D<rprime|'>\<wedge\>\<alpha\><rsup|2><rsub|i><wide|=|\<dot\>>\<tau\><rsup|n<rsub|i>><rprime|'>,\<Gamma\>\<Gamma\><rprime|''>\<vdash\>n<rsub|i>:Num<around*|(|\<alpha\><rsup|2><rsub|i>|)>>.

        <item>By induction hypothesis applied to (13) we have
        <math|\<cal-I\><rsub|i><rsup|1>,C\<wedge\>D<rprime|'>\<wedge\>\<alpha\><rsup|1><rsub|i><wide|=|\<dot\>>\<tau\><rsup|m<rsub|i>><rprime|'>\<vDash\><around*|\<llbracket\>|\<Gamma\>\<Gamma\><rprime|''>\<vdash\>m<rsub|i>:Num<around*|(|\<alpha\><rsup|1><rsub|i>|)>|\<rrbracket\>>>
        and <math|\<cal-I\><rsub|i><rsup|2>,C\<wedge\>D<rprime|'>\<wedge\>\<alpha\><rsup|2><rsub|i><wide|=|\<dot\>>\<tau\><rsup|n<rsub|i>><rprime|'>\<vDash\><around*|\<llbracket\>|\<Gamma\>\<Gamma\><rprime|''>\<vdash\>n<rsub|i>:Num<around*|(|\<alpha\><rsup|2><rsub|i>|)>|\<rrbracket\>>>.

        <item>By lemma <reference|MonoEnvEq> and weakening, (2) implies
        <math|C\<wedge\>D\<wedge\>\<Gamma\><rprime|''><wide|=|\<dot\>>\<Gamma\><rprime|'>\<wedge\><rsub|i>\<alpha\><rsup|1><rsub|i><wide|=|\<dot\>>\<tau\><rsup|m<rsub|i>>\<wedge\><rsub|i>\<alpha\><rsup|2><rsub|i><wide|=|\<dot\>>\<tau\><rsup|n<rsub|i>>\<wedge\><rsub|i>\<alpha\><rsub|i><rsup|1>\<leq\>\<alpha\><rsub|i><rsup|2>,\<Gamma\>\<Gamma\><rprime|''>\<vdash\>e:\<tau\><rsub|2>>.

        <item>By (15), <name|Hide> and (12), we get
        <math|C\<wedge\>D<rprime|'>\<wedge\><rsub|i>\<alpha\><rsup|1><rsub|i><wide|=|\<dot\>>\<tau\><rsup|m<rsub|i>><rprime|'>\<wedge\><rsub|i>\<alpha\><rsup|2><rsub|i><wide|=|\<dot\>>\<tau\><rsup|n<rsub|i>><rprime|'>\<wedge\><rsub|i>\<alpha\><rsub|i><rsup|1>\<leq\>\<alpha\><rsub|i><rsup|2>,\<Gamma\>\<Gamma\><rprime|''>\<vdash\>e:\<tau\><rsub|2>>.

        <item>By induction hypothesis, (16) gives
        <math|\<cal-I\><rsup|3>,C\<wedge\>D<rprime|'>\<wedge\><rsub|i>\<alpha\><rsup|1><rsub|i><wide|=|\<dot\>>\<tau\><rsup|m<rsub|i>><rprime|'>\<wedge\><rsub|i>\<alpha\><rsup|2><rsub|i><wide|=|\<dot\>>\<tau\><rsup|n<rsub|i>><rprime|'>\<wedge\><rsub|i>\<alpha\><rsub|i><rsup|1>\<leq\>\<alpha\><rsub|i><rsup|2>\<vDash\><around*|\<llbracket\>|\<Gamma\>\<Gamma\><rprime|''>\<vdash\>e:\<tau\><rsub|2>|\<rrbracket\>>>.

        <item>By (8), (10), (14) and (17), we get
        <math|<wide|\<cal-I\><rsub|i><rsup|1>|\<bar\>><wide|\<cal-I\><rsub|i><rsup|2>|\<bar\>>\<cal-I\><rsup|3>,C\<wedge\><rsub|i>\<alpha\><rsup|1><rsub|i><wide|=|\<dot\>>\<tau\><rsup|m<rsub|i>><rprime|'>\<wedge\><rsub|i>\<alpha\><rsup|2><rsub|i><wide|=|\<dot\>>\<tau\><rsup|n<rsub|i>><rprime|'>\<vDash\>\<Phi\>>.

        <item>By nonemptiness of the domain, from (18) we get the goal
        <math|<wide|\<cal-I\><rsub|i><rsup|1>|\<bar\>><wide|\<cal-I\><rsub|i><rsup|2>|\<bar\>>\<cal-I\><rsup|3>,C\<vDash\>\<exists\><wide|\<alpha\><rsup|1><rsub|i>\<alpha\><rsup|2><rsub|i>|\<bar\>>.\<Phi\>>.
      </enumerate>

      <item>Case <name|NegClause>. The proof is nearly identical as above.

      <\enumerate>
        <item><name|NegClause>'s premises are:
        <math|C\<vdash\>p:\<tau\><rsub|3>\<longrightarrow\>\<exists\><wide|\<beta\>|\<bar\>><around|[|D|]>\<Gamma\><rprime|'>>,

        <item><math|C\<wedge\>D\<wedge\>\<tau\><rsub|1><wide|=|\<dot\>>\<tau\><rsub|3>\<wedge\><rsub|i>\<tau\><rsup|m<rsub|i>>\<leq\>\<tau\><rsup|n<rsub|i>>,\<Gamma\>\<Gamma\><rprime|'>\<vdash\>e:\<tau\><rsub|2>>,

        <item><math|C\<wedge\>D,\<Gamma\>\<Gamma\><rprime|'>\<vdash\>m<rsub|i>:Num<around*|(|\<tau\><rsup|m<rsub|i>>|)>>
        and <math|C\<wedge\>D,\<Gamma\>\<Gamma\><rprime|'>\<vdash\>n<rsub|i>:Num<around*|(|\<tau\><rsup|n<rsub|i>>|)>>,

        <item>and <math|<wide|\<beta\>|\<bar\>>#FV<around|(|C,\<Gamma\>,\<tau\><rsub|2>|)>>.

        <item>Assume w.l.o.g. that <math|<wide|\<beta\>|\<bar\>>#FV<around|(|\<tau\><rsub|3>|)>>.

        <item>Let <math|\<alpha\><rsub|3>\<alpha\><rsub|i><rsup|1>\<alpha\><rsub|i><rsup|2>#FV<around|(|C,\<tau\><rsub|1>,\<tau\><rsub|2>,\<tau\><rsub|3>,<wide|\<tau\><rsup|m<rsub|i>>,\<tau\><rsup|n<rsub|i>>|\<bar\>>|)>>.

        <item>Let <math|<around*|\<llbracket\>|\<vdash\>p\<uparrow\>\<tau\><rsub|3>|\<rrbracket\>>=\<exists\><wide|\<beta\><rprime|'>|\<bar\>><around|[|D<rprime|'>|]>\<Gamma\><rprime|''>>,
        where <math|<wide|\<beta\><rprime|'>|\<bar\>>#FV<around*|(|\<Gamma\>,C,\<tau\><rsub|1>,\<tau\><rsub|2>,\<tau\><rsub|3>,<wide|\<beta\>|\<bar\>>|)>>.

        <item>By lemma <reference|CompletePat>, (1) and (7) gives
        <math|C\<vDash\><around*|\<llbracket\>|\<vdash\>p\<downarrow\>\<tau\><rsub|3>|\<rrbracket\>>>

        <item>and <math|C\<vDash\>\<forall\><wide|\<beta\><rprime|'>|\<bar\>>.D<rprime|'>\<Rightarrow\>\<exists\><wide|\<beta\>|\<bar\>>.D\<wedge\>\<Gamma\><rprime|''><wide|=|\<dot\>>\<Gamma\><rprime|'>>,
        which is equivalent to <math|C\<wedge\>D<rprime|'>\<vDash\>\<exists\><wide|\<beta\>|\<bar\>>.D\<wedge\>\<Gamma\><rprime|''><wide|=|\<dot\>>\<Gamma\><rprime|'>>.

        <item>Recall that <math|<around*|\<llbracket\>|\<Gamma\>\<vdash\>p
        <text|<with|font-shape|condensed|<strong|when>>>
        \<wedge\><rsub|i>m<rsub|i>\<leqslant\>n<rsub|i>.e:\<tau\><rsub|1>\<rightarrow\>\<tau\><rsub|2>|\<rrbracket\>>=\<exists\>\<alpha\><rsub|3><wide|\<alpha\><rsup|1><rsub|i>\<alpha\><rsup|2><rsub|i>|\<bar\>>.\<Phi\>>,
        for <math|\<Phi\>=<next-line><around*|\<llbracket\>|\<vdash\>p\<downarrow\>\<alpha\><rsub|3>|\<rrbracket\>>\<wedge\>\<forall\><wide|\<beta\>|\<bar\>><rprime|'>.D<rprime|'>\<Rightarrow\>\<wedge\><rsub|i><around*|\<llbracket\>|\<Gamma\>\<Gamma\><rprime|''>\<vdash\>m<rsub|i>:Num<around*|(|\<alpha\><rsup|1><rsub|i>|)>|\<rrbracket\>>\<wedge\><rsub|i><around*|\<llbracket\>|\<Gamma\>\<Gamma\><rprime|''>\<vdash\>n<rsub|i>:Num<around*|(|\<alpha\><rsup|2><rsub|i>|)>|\<rrbracket\>>\<wedge\><next-line><around*|(|\<tau\><rsub|1><wide|=|\<dot\>>\<alpha\><rsub|3>\<wedge\><rsub|i>\<alpha\><rsup|1><rsub|i>\<leq\>\<alpha\><rsup|2><rsub|i>\<Rightarrow\><around*|\<llbracket\>|\<Gamma\>\<Gamma\><rprime|''>\<vdash\>e:\<tau\><rsub|2>|\<rrbracket\>>|)>>.

        <item>By lemma <reference|MonoEnvEq>, weakening and <name|Equ>, (3)
        implies <math|C\<wedge\>D\<wedge\>\<Gamma\><rprime|''><wide|=|\<dot\>>\<Gamma\><rprime|'>\<wedge\>\<alpha\><rsup|1><rsub|i><wide|=|\<dot\>>\<tau\><rsup|m<rsub|i>>,\<Gamma\>\<Gamma\><rprime|''>\<vdash\>m<rsub|i>:Num<around*|(|\<alpha\><rsup|1><rsub|i>|)>>
        and <math|C\<wedge\>D\<wedge\>\<Gamma\><rprime|''><wide|=|\<dot\>>\<Gamma\><rprime|'>\<wedge\>\<alpha\><rsup|2><rsub|i><wide|=|\<dot\>>\<tau\><rsup|n<rsub|i>>,\<Gamma\>\<Gamma\><rprime|''>\<vdash\>n<rsub|i>:Num<around*|(|\<alpha\><rsup|2><rsub|i>|)>>.

        <item>From (9) we have <math|C\<wedge\>D<rprime|'>\<wedge\>\<alpha\><rsup|1><rsub|i><wide|=|\<dot\>>\<tau\><rsup|m<rsub|i>><rprime|'>\<vDash\>\<exists\><wide|\<beta\>|\<bar\>>.D\<wedge\>\<Gamma\><rprime|''><wide|=|\<dot\>>\<Gamma\><rprime|'>\<wedge\>\<alpha\><rsup|1><rsub|i><wide|=|\<dot\>>\<tau\><rsup|m<rsub|i>>>
        and <math|C\<wedge\>D<rprime|'>\<wedge\>\<alpha\><rsup|2><rsub|i><wide|=|\<dot\>>\<tau\><rsup|n<rsub|i>><rprime|'>\<vDash\>\<exists\><wide|\<beta\>|\<bar\>>.D\<wedge\>\<Gamma\><rprime|''><wide|=|\<dot\>>\<Gamma\><rprime|'>\<wedge\>\<alpha\><rsup|2><rsub|i><wide|=|\<dot\>>\<tau\><rsup|n<rsub|i>>>
        for some <math|\<tau\><rsup|m<rsub|i>><rprime|'>,\<tau\><rsup|n<rsub|i>><rprime|'>>.

        <item>By (11), <name|Hide> and (12), we get
        <math|C\<wedge\>D<rprime|'>\<wedge\>\<alpha\><rsup|1><rsub|i><wide|=|\<dot\>>\<tau\><rsup|m<rsub|i>><rprime|'>,\<Gamma\>\<Gamma\><rprime|''>\<vdash\>m<rsub|i>:Num<around*|(|\<alpha\><rsup|1><rsub|i>|)>>
        and <math|C\<wedge\>D<rprime|'>\<wedge\>\<alpha\><rsup|2><rsub|i><wide|=|\<dot\>>\<tau\><rsup|n<rsub|i>><rprime|'>,\<Gamma\>\<Gamma\><rprime|''>\<vdash\>n<rsub|i>:Num<around*|(|\<alpha\><rsup|2><rsub|i>|)>>.

        <item>By induction hypothesis applied to (13) we have
        <math|\<cal-I\><rsub|i><rsup|1>,C\<wedge\>D<rprime|'>\<wedge\>\<alpha\><rsup|1><rsub|i><wide|=|\<dot\>>\<tau\><rsup|m<rsub|i>><rprime|'>\<vDash\><around*|\<llbracket\>|\<Gamma\>\<Gamma\><rprime|''>\<vdash\>m<rsub|i>:Num<around*|(|\<alpha\><rsup|1><rsub|i>|)>|\<rrbracket\>>>
        and <math|\<cal-I\><rsub|i><rsup|2>,C\<wedge\>D<rprime|'>\<wedge\>\<alpha\><rsup|2><rsub|i><wide|=|\<dot\>>\<tau\><rsup|n<rsub|i>><rprime|'>\<vDash\><around*|\<llbracket\>|\<Gamma\>\<Gamma\><rprime|''>\<vdash\>n<rsub|i>:Num<around*|(|\<alpha\><rsup|2><rsub|i>|)>|\<rrbracket\>>>.

        <item>By lemma <reference|MonoEnvEq> and weakening, (2) implies
        <math|C\<wedge\>D\<wedge\>\<Gamma\><rprime|''><wide|=|\<dot\>>\<Gamma\><rprime|'>\<wedge\>\<alpha\><rsub|3><wide|=|\<dot\>>\<tau\><rsub|3>\<wedge\><rsub|i>\<alpha\><rsup|1><rsub|i><wide|=|\<dot\>>\<tau\><rsup|m<rsub|i>>\<wedge\><rsub|i>\<alpha\><rsup|2><rsub|i><wide|=|\<dot\>>\<tau\><rsup|n<rsub|i>>\<wedge\>\<tau\><rsub|1><wide|=|\<dot\>>\<alpha\><rsub|3>\<wedge\><rsub|i>\<alpha\><rsub|i><rsup|1>\<leq\>\<alpha\><rsub|i><rsup|2>,\<Gamma\>\<Gamma\><rprime|''>\<vdash\>e:\<tau\><rsub|2>>.

        <item>By (15), <name|Hide> and (12), we get
        <math|C\<wedge\>D<rprime|'>\<wedge\>\<alpha\><rsub|3><wide|=|\<dot\>>\<tau\><rsub|3>\<wedge\><rsub|i>\<alpha\><rsup|1><rsub|i><wide|=|\<dot\>>\<tau\><rsup|m<rsub|i>><rprime|'>\<wedge\><rsub|i>\<alpha\><rsup|2><rsub|i><wide|=|\<dot\>>\<tau\><rsup|n<rsub|i>><rprime|'>\<wedge\>\<tau\><rsub|1><wide|=|\<dot\>>\<alpha\><rsub|3>\<wedge\><rsub|i>\<alpha\><rsub|i><rsup|1>\<leq\>\<alpha\><rsub|i><rsup|2>,\<Gamma\>\<Gamma\><rprime|''>\<vdash\>e:\<tau\><rsub|2>>.

        <item>By induction hypothesis, (16) gives
        <math|\<cal-I\><rsup|3>,C\<wedge\>D<rprime|'>\<wedge\>\<alpha\><rsub|3><wide|=|\<dot\>>\<tau\><rsub|3>\<wedge\><rsub|i>\<alpha\><rsup|1><rsub|i><wide|=|\<dot\>>\<tau\><rsup|m<rsub|i>><rprime|'>\<wedge\><rsub|i>\<alpha\><rsup|2><rsub|i><wide|=|\<dot\>>\<tau\><rsup|n<rsub|i>><rprime|'>\<wedge\>\<tau\><rsub|1><wide|=|\<dot\>>\<alpha\><rsub|3>\<wedge\><rsub|i>\<alpha\><rsub|i><rsup|1>\<leq\>\<alpha\><rsub|i><rsup|2>\<vDash\><around*|\<llbracket\>|\<Gamma\>\<Gamma\><rprime|''>\<vdash\>e:\<tau\><rsub|2>|\<rrbracket\>>>.

        <item>By (8), (10), (14) and (17), we get
        <math|<wide|\<cal-I\><rsub|i><rsup|1>|\<bar\>><wide|\<cal-I\><rsub|i><rsup|2>|\<bar\>>\<cal-I\><rsup|3>,C\<wedge\>\<alpha\><rsub|3><wide|=|\<dot\>>\<tau\><rsub|3>\<wedge\><rsub|i>\<alpha\><rsup|1><rsub|i><wide|=|\<dot\>>\<tau\><rsup|m<rsub|i>><rprime|'>\<wedge\><rsub|i>\<alpha\><rsup|2><rsub|i><wide|=|\<dot\>>\<tau\><rsub|n<rsub|i>><rprime|'>\<vDash\>\<Phi\>>.

        <item>By nonemptiness of the domains, from (18) we get the goal
        <math|<wide|\<cal-I\><rsub|i><rsup|1>|\<bar\>><wide|\<cal-I\><rsub|i><rsup|2>|\<bar\>>\<cal-I\><rsup|3>,C\<vDash\>\<exists\>\<alpha\><rsub|3><wide|\<alpha\><rsup|1><rsub|i>\<alpha\><rsup|2><rsub|i>|\<bar\>>.\<Phi\>>.
      </enumerate>

      <item>Case <name|FailClause>. The proof is nearly identical as above.

      <\enumerate>
        <item><name|FailClause>'s premises are:
        <math|C\<vdash\>p:\<tau\><rsub|3>\<longrightarrow\>\<exists\><wide|\<beta\>|\<bar\>><around|[|D|]>\<Gamma\><rprime|'>>,

        <item><math|C\<wedge\>D\<wedge\>\<tau\><rsub|1><wide|=|\<dot\>>\<tau\><rsub|3>\<wedge\><rsub|i>\<tau\><rsup|m<rsub|i>>\<leq\>\<tau\><rsup|n<rsub|i>>,\<Gamma\>\<Gamma\><rprime|'>\<vdash\>s:String>,

        <item><math|C\<wedge\>D,\<Gamma\>\<Gamma\><rprime|'>\<vdash\>m<rsub|i>:Num<around*|(|\<tau\><rsup|m<rsub|i>>|)>>
        and <math|C\<wedge\>D,\<Gamma\>\<Gamma\><rprime|'>\<vdash\>n<rsub|i>:Num<around*|(|\<tau\><rsup|n<rsub|i>>|)>>,

        <item>and <math|<wide|\<beta\>|\<bar\>>#FV<around|(|C,\<Gamma\>|)>>.

        <item>Assume w.l.o.g. that <math|<wide|\<beta\>|\<bar\>>#FV<around|(|\<tau\><rsub|3>|)>>.

        <item>Let <math|\<alpha\><rsub|3>\<alpha\><rsub|i><rsup|1>\<alpha\><rsub|i><rsup|2>#FV<around|(|C,\<tau\><rsub|1>,\<tau\><rsub|3>,<wide|\<tau\><rsup|m<rsub|i>>,\<tau\><rsup|n<rsub|i>>|\<bar\>>|)>>.

        <item>Let <math|<around*|\<llbracket\>|\<vdash\>p\<uparrow\>\<tau\><rsub|3>|\<rrbracket\>>=\<exists\><wide|\<beta\><rprime|'>|\<bar\>><around|[|D<rprime|'>|]>\<Gamma\><rprime|''>>,
        where <math|<wide|\<beta\><rprime|'>|\<bar\>>#FV<around*|(|\<Gamma\>,C,\<tau\><rsub|1>,\<tau\><rsub|3>,<wide|\<beta\>|\<bar\>>|)>>.

        <item>By lemma <reference|CompletePat>, (1) and (7) gives
        <math|C\<vDash\><around*|\<llbracket\>|\<vdash\>p\<downarrow\>\<tau\><rsub|3>|\<rrbracket\>>>

        <item>and <math|C\<vDash\>\<forall\><wide|\<beta\><rprime|'>|\<bar\>>.D<rprime|'>\<Rightarrow\>\<exists\><wide|\<beta\>|\<bar\>>.D\<wedge\>\<Gamma\><rprime|''><wide|=|\<dot\>>\<Gamma\><rprime|'>>,
        which is equivalent to <math|C\<wedge\>D<rprime|'>\<vDash\>\<exists\><wide|\<beta\>|\<bar\>>.D\<wedge\>\<Gamma\><rprime|''><wide|=|\<dot\>>\<Gamma\><rprime|'>>.

        <item>Recall that <math|<around*|\<llbracket\>|\<Gamma\>\<vdash\>p
        <text|<with|font-shape|condensed|<strong|when>>>
        \<wedge\><rsub|i>m<rsub|i>\<leqslant\>n<rsub|i>.e:\<tau\><rsub|1>\<rightarrow\>\<tau\><rsub|2>|\<rrbracket\>>=\<exists\>\<alpha\><rsub|3><wide|\<alpha\><rsup|1><rsub|i>\<alpha\><rsup|2><rsub|i>|\<bar\>>.\<Phi\>>,
        for <math|\<Phi\>=<next-line><around*|\<llbracket\>|\<vdash\>p\<downarrow\>\<alpha\><rsub|3>|\<rrbracket\>>\<wedge\>\<forall\><wide|\<beta\>|\<bar\>><rprime|'>.D<rprime|'>\<Rightarrow\>\<wedge\><rsub|i><around*|\<llbracket\>|\<Gamma\>\<Gamma\><rprime|''>\<vdash\>m<rsub|i>:Num<around*|(|\<alpha\><rsup|1><rsub|i>|)>|\<rrbracket\>>\<wedge\><rsub|i><around*|\<llbracket\>|\<Gamma\>\<Gamma\><rprime|''>\<vdash\>n<rsub|i>:Num<around*|(|\<alpha\><rsup|2><rsub|i>|)>|\<rrbracket\>>\<wedge\><next-line><around*|(|\<tau\><rsub|1><wide|=|\<dot\>>\<alpha\><rsub|3>\<wedge\><rsub|i>\<alpha\><rsup|1><rsub|i>\<leq\>\<alpha\><rsup|2><rsub|i>\<Rightarrow\><around*|\<llbracket\>|\<Gamma\>\<Gamma\><rprime|''>\<vdash\>e:\<tau\><rsub|2>|\<rrbracket\>>|)>>.

        <item>By lemma <reference|MonoEnvEq>, weakening and <name|Equ>, (3)
        implies <math|C\<wedge\>D\<wedge\>\<Gamma\><rprime|''><wide|=|\<dot\>>\<Gamma\><rprime|'>\<wedge\>\<alpha\><rsup|1><rsub|i><wide|=|\<dot\>>\<tau\><rsup|m<rsub|i>>,\<Gamma\>\<Gamma\><rprime|''>\<vdash\>m<rsub|i>:Num<around*|(|\<alpha\><rsup|1><rsub|i>|)>>
        and <math|C\<wedge\>D\<wedge\>\<Gamma\><rprime|''><wide|=|\<dot\>>\<Gamma\><rprime|'>\<wedge\>\<alpha\><rsup|2><rsub|i><wide|=|\<dot\>>\<tau\><rsup|n<rsub|i>>,\<Gamma\>\<Gamma\><rprime|''>\<vdash\>n<rsub|i>:Num<around*|(|\<alpha\><rsup|2><rsub|i>|)>>.

        <item>From (9) we have <math|C\<wedge\>D<rprime|'>\<wedge\>\<alpha\><rsup|1><rsub|i><wide|=|\<dot\>>\<tau\><rsup|m<rsub|i>><rprime|'>\<vDash\>\<exists\><wide|\<beta\>|\<bar\>>.D\<wedge\>\<Gamma\><rprime|''><wide|=|\<dot\>>\<Gamma\><rprime|'>\<wedge\>\<alpha\><rsup|1><rsub|i><wide|=|\<dot\>>\<tau\><rsup|m<rsub|i>>>
        and <math|C\<wedge\>D<rprime|'>\<wedge\>\<alpha\><rsup|2><rsub|i><wide|=|\<dot\>>\<tau\><rsup|n<rsub|i>><rprime|'>\<vDash\>\<exists\><wide|\<beta\>|\<bar\>>.D\<wedge\>\<Gamma\><rprime|''><wide|=|\<dot\>>\<Gamma\><rprime|'>\<wedge\>\<alpha\><rsup|2><rsub|i><wide|=|\<dot\>>\<tau\><rsup|n<rsub|i>>>
        for some <math|\<tau\><rsup|m<rsub|i>><rprime|'>,\<tau\><rsup|n<rsub|i>><rprime|'>>.

        <item>By (11), <name|Hide> and (12), we get
        <math|C\<wedge\>D<rprime|'>\<wedge\>\<alpha\><rsup|1><rsub|i><wide|=|\<dot\>>\<tau\><rsup|m<rsub|i>><rprime|'>,\<Gamma\>\<Gamma\><rprime|''>\<vdash\>m<rsub|i>:Num<around*|(|\<alpha\><rsup|1><rsub|i>|)>>
        and <math|C\<wedge\>D<rprime|'>\<wedge\>\<alpha\><rsup|2><rsub|i><wide|=|\<dot\>>\<tau\><rsup|n<rsub|i>><rprime|'>,\<Gamma\>\<Gamma\><rprime|''>\<vdash\>n<rsub|i>:Num<around*|(|\<alpha\><rsup|2><rsub|i>|)>>.

        <item>By induction hypothesis applied to (13) we have
        <math|\<cal-I\><rsub|i><rsup|1>,C\<wedge\>D<rprime|'>\<wedge\>\<alpha\><rsup|1><rsub|i><wide|=|\<dot\>>\<tau\><rsup|m<rsub|i>><rprime|'>\<vDash\><around*|\<llbracket\>|\<Gamma\>\<Gamma\><rprime|''>\<vdash\>m<rsub|i>:Num<around*|(|\<alpha\><rsup|1><rsub|i>|)>|\<rrbracket\>>>
        and <math|\<cal-I\><rsub|i><rsup|2>,C\<wedge\>D<rprime|'>\<wedge\>\<alpha\><rsup|2><rsub|i><wide|=|\<dot\>>\<tau\><rsup|n<rsub|i>><rprime|'>\<vDash\><around*|\<llbracket\>|\<Gamma\>\<Gamma\><rprime|''>\<vdash\>n<rsub|i>:Num<around*|(|\<alpha\><rsup|2><rsub|i>|)>|\<rrbracket\>>>.

        <item>By lemma <reference|MonoEnvEq> and weakening, (2) implies
        <math|C\<wedge\>D\<wedge\>\<Gamma\><rprime|''><wide|=|\<dot\>>\<Gamma\><rprime|'>\<wedge\>\<alpha\><rsub|3><wide|=|\<dot\>>\<tau\><rsub|3>\<wedge\><rsub|i>\<alpha\><rsup|1><rsub|i><wide|=|\<dot\>>\<tau\><rsup|m<rsub|i>>\<wedge\><rsub|i>\<alpha\><rsup|2><rsub|i><wide|=|\<dot\>>\<tau\><rsup|n<rsub|i>>\<wedge\>\<tau\><rsub|1><wide|=|\<dot\>>\<alpha\><rsub|3>\<wedge\><rsub|i>\<alpha\><rsub|i><rsup|1>\<leq\>\<alpha\><rsub|i><rsup|2>,\<Gamma\>\<Gamma\><rprime|''>\<vdash\>s:String>.

        <item>By (15), <name|Hide> and (12), we get
        <math|C\<wedge\>D<rprime|'>\<wedge\>\<alpha\><rsub|3><wide|=|\<dot\>>\<tau\><rsub|3>\<wedge\><rsub|i>\<alpha\><rsup|1><rsub|i><wide|=|\<dot\>>\<tau\><rsup|m<rsub|i>><rprime|'>\<wedge\><rsub|i>\<alpha\><rsup|2><rsub|i><wide|=|\<dot\>>\<tau\><rsup|n<rsub|i>><rprime|'>\<wedge\>\<tau\><rsub|1><wide|=|\<dot\>>\<alpha\><rsub|3>\<wedge\><rsub|i>\<alpha\><rsub|i><rsup|1>\<leq\>\<alpha\><rsub|i><rsup|2>,\<Gamma\>\<Gamma\><rprime|''>\<vdash\>s:String>.

        <item>By induction hypothesis, (16) gives
        <math|\<cal-I\><rsup|3>,C\<wedge\>D<rprime|'>\<wedge\>\<alpha\><rsub|3><wide|=|\<dot\>>\<tau\><rsub|3>\<wedge\><rsub|i>\<alpha\><rsup|1><rsub|i><wide|=|\<dot\>>\<tau\><rsup|m<rsub|i>><rprime|'>\<wedge\><rsub|i>\<alpha\><rsup|2><rsub|i><wide|=|\<dot\>>\<tau\><rsup|n<rsub|i>><rprime|'>\<wedge\>\<tau\><rsub|1><wide|=|\<dot\>>\<alpha\><rsub|3>\<wedge\><rsub|i>\<alpha\><rsub|i><rsup|1>\<leq\>\<alpha\><rsub|i><rsup|2>\<vDash\><around*|\<llbracket\>|\<Gamma\>\<Gamma\><rprime|''>\<vdash\>s:String|\<rrbracket\>>>.

        <item>By (8), (10), (14) and (17), we get
        <math|<wide|\<cal-I\><rsub|i><rsup|1>|\<bar\>><wide|\<cal-I\><rsub|i><rsup|2>|\<bar\>>\<cal-I\><rsup|3>,C\<wedge\>\<alpha\><rsub|3><wide|=|\<dot\>>\<tau\><rsub|3>\<wedge\><rsub|i>\<alpha\><rsup|1><rsub|i><wide|=|\<dot\>>\<tau\><rsup|m<rsub|i>><rprime|'>\<wedge\><rsub|i>\<alpha\><rsup|2><rsub|i><wide|=|\<dot\>>\<tau\><rsup|n<rsub|i>><rprime|'>\<vDash\>\<Phi\>>.

        <item>By nonemptiness of the domains, from (18) we get the goal
        <math|<wide|\<cal-I\><rsub|i><rsup|1>|\<bar\>><wide|\<cal-I\><rsub|i><rsup|2>|\<bar\>>\<cal-I\><rsup|3>,C\<vDash\>\<exists\>\<alpha\><rsub|3><wide|\<alpha\><rsup|1><rsub|i>\<alpha\><rsup|2><rsub|i>|\<bar\>>.\<Phi\>>.
      </enumerate>

      <item>Case <name|Equ>.

      <\enumerate>
        <item><name|Equ>'s premises are <math|C,\<Gamma\>\<vdash\>e:\<tau\><rprime|'>>,
        which by induction hypothesis gives
        <math|\<cal-I\>,C\<vDash\><around*|\<llbracket\>|\<Gamma\>\<vdash\>e:\<tau\><rprime|'>|\<rrbracket\>>>,

        <item>and <math|C\<vDash\>\<tau\><rprime|'><wide|=|\<dot\>>\<tau\>>.

        <item>Let <math|\<Phi\><rsub|\<tau\>>\<assign\><around*|\<llbracket\>|\<Gamma\>\<vdash\>e:\<tau\>|\<rrbracket\>>>.
        Observe, that <math|\<tau\>> occurs in <math|\<Phi\><rsub|\<tau\>>>
        only as a subterm in a side of equation:
        <math|<wide|=|\<dot\>>\<tau\>>, <math|<wide|=|\<dot\>>\<ldots\>\<rightarrow\>\<tau\>>,
        <math|<wide|=|\<dot\>><around|(|\<ldots\>\<rightarrow\><around|(|\<ldots\>\<rightarrow\>\<tau\>|)>\<ldots\>|)>>.
        Therefore, <math|\<tau\><rprime|'><wide|=|\<dot\>>\<tau\>\<vDash\>\<Phi\><rsub|\<tau\><rprime|'>>\<Leftrightarrow\>\<Phi\><rsub|\<tau\>>>.

        <item>(1), (2) and (3) imply that
        <math|\<cal-I\>,C\<vDash\><around*|\<llbracket\>|\<Gamma\>\<vdash\>e:\<tau\>|\<rrbracket\>>>.
      </enumerate>

      <item>Case <name|Hide>.

      <\enumerate>
        <item><name|Hide>'s premises are <math|C,\<Gamma\>\<vdash\>e:\<tau\>>,
        that by induction hypothesis gives
        <math|\<cal-I\>,C\<vDash\><around*|\<llbracket\>|\<Gamma\>\<vdash\>e:\<tau\>|\<rrbracket\>>>,

        <item>and <math|<wide|\<beta\>|\<bar\>>#FV<around|(|\<Gamma\>,\<tau\>|)>>.

        <item>By (2), w.l.o.g. <math|<wide|\<beta\>|\<bar\>>#FV<around|(|<around*|\<llbracket\>|\<Gamma\>\<vdash\>e:\<tau\>|\<rrbracket\>>|)>>.

        <item>(1) implies that <math|\<cal-I\>\<vDash\>\<forall\><wide|\<beta\>|\<bar\>>.<around|(|C\<Rightarrow\>\<Phi\><rsub|1>|)>>
        which by (3) is equivalent to <math|\<cal-I\>,\<exists\><wide|\<beta\>|\<bar\>>.C\<vDash\><around*|\<llbracket\>|\<Gamma\>\<vdash\>e:\<tau\>|\<rrbracket\>>>.
      </enumerate>

      <item>Case <name|FElim>. <math|\<cal-I\>,\<b-F\>\<vDash\>\<Phi\>> holds
      for any <math|\<Phi\>>.

      <item>Case <name|DisjElim>.

      <\enumerate>
        <item><name|DisjElim> premises are
        <math|C,\<Gamma\>\<vdash\>e:\<tau\>> and
        <math|D,\<Gamma\>\<vdash\>e:\<tau\>>. Induction hypothesis gives
        <math|\<cal-I\><rsub|1>,C\<vDash\><around*|\<llbracket\>|\<Gamma\>\<vdash\>e:\<tau\>|\<rrbracket\>>>
        and <math|\<cal-I\><rsub|2>,D\<vDash\><around*|\<llbracket\>|\<Gamma\>\<vdash\>e:\<tau\>|\<rrbracket\>>>
        for some interpretations of predicate variables
        <math|\<cal-I\><rsub|1>,\<cal-I\><rsub|2>>.

        <item>Therefore, we have <math|\<cal-I\>,C\<vee\>D\<vDash\><around*|\<llbracket\>|\<Gamma\>\<vdash\>e:\<tau\>|\<rrbracket\>>>,
        for both <math|\<cal-I\>=\<cal-I\><rsub|1>> and
        <math|\<cal-I\>=\<cal-I\><rsub|2>>.
      </enumerate>
    </itemize>
  </proof>

  Proof of corollary <reference|InfComplCoro>.

  <\proof>
    <math|C,\<Gamma\>\<vdash\>e:\<forall\><wide|\<alpha\>|\<bar\>><around|[|D|]>.\<tau\>>
    can only be derived by the <name|Gen> rule, therefore we have
    <math|C<rprime|'>\<wedge\>D,\<Gamma\>\<vdash\>e:\<tau\>> for
    <math|<wide|\<alpha\>|\<bar\>>#FV<around|(|\<Gamma\>,C<rprime|'>|)>> and
    <math|C=C<rprime|'>\<wedge\>\<exists\><wide|\<alpha\>|\<bar\>>.D>. By
    theorem <reference|InfComplExpr>, there exists an interpretation
    <math|\<cal-I\>> such that <math|\<cal-I\>,C<rprime|'>\<wedge\>D\<vDash\><around*|\<llbracket\>|\<Gamma\>\<vdash\>e:\<tau\>|\<rrbracket\>>>.
    <math|\<cal-I\>,C<rprime|'>\<wedge\>D\<vDash\><around*|\<llbracket\>|\<Gamma\>\<vdash\>e:\<tau\>|\<rrbracket\>>>
    iff <math|\<cal-I\>\<vDash\>C<rprime|'>\<wedge\>D\<Rightarrow\><around*|\<llbracket\>|\<Gamma\>\<vdash\>e:\<tau\>|\<rrbracket\>>>
    iff <math|\<cal-I\>\<vDash\>\<forall\><wide|\<alpha\>|\<bar\>>.C<rprime|'>\<wedge\>D\<Rightarrow\><around*|\<llbracket\>|\<Gamma\>\<vdash\>e:\<tau\>|\<rrbracket\>>>
    iff <math|\<cal-I\>,C<rprime|'>\<vDash\>\<forall\><wide|\<alpha\>|\<bar\>>.D\<Rightarrow\><around*|\<llbracket\>|\<Gamma\>\<vdash\>e:\<tau\>|\<rrbracket\>>>.
    Therefore <math|\<cal-I\>,C\<vDash\>\<forall\><wide|\<alpha\>|\<bar\>>.D\<Rightarrow\><around*|\<llbracket\>|\<Gamma\>\<vdash\>e:\<tau\>|\<rrbracket\>>>.
  </proof>

  <subsection|Existential Types><label|ExGADTsProofs>

  Proof of theorem <reference|InfCorrComplEx>.

  <\proof>
    By inspecting Table <reference|NormExpr>, note that
    <math|\<lambda\><around*|[|K|]>e> subexpressions are absent from
    <math|n<around*|(|e|)>>. Thus <math|\<cal-I\><rsub|e>> is empty in all
    cases other than <name|ExIntro>. We therefore shorten these cases by not
    mentioning <math|\<cal-I\><rsub|e>> and <math|\<Sigma\>>. Below we extend
    the inductive proofs with the cases for expressions introduced by, or
    rule applications of, <name|ExIntro>, <name|LetIn> and <name|ExLetIn>.

    <\itemize>
      <item>Theorem <reference|InfCorrExpr> (Correctness)
      <math|<around*|\<llbracket\>|\<Gamma\>,\<Sigma\><rsub|0>\<vdash\>e:\<tau\>|\<rrbracket\>>,\<Gamma\>,\<Sigma\><rsub|0>\<vdash\>e:\<tau\>>.
      Case: <math|\<cal-E\><around*|(|e|)>\<neq\>\<varnothing\>>.

      <\enumerate>
        <item>Induction hypothesis states
        <math|<around*|\<llbracket\>|\<Gamma\>,\<Sigma\>\<vdash\>n<around*|(|e|)>:\<tau\>|\<rrbracket\>>,\<Gamma\>,\<Sigma\>\<vdash\>n<around*|(|e|)>:\<tau\>>.

        <item>The goal follows by <name|ExIntro>.
      </enumerate>

      <item>Theorem <reference|InfCorrExpr> (Correctness) Case: <math|e> is
      <math|<text|<with|font-shape|condensed|<strong|let>>> p=e<rsub|1>
      <text|<with|font-shape|condensed|<strong|in>>> e<rsub|2>>.

      <\enumerate>
        <item>Induction hypothesis yields
        <math|<around*|\<llbracket\>|\<Gamma\>\<vdash\>K
        p.e<rsub|2>:\<alpha\><rsub|0>\<rightarrow\>\<tau\>|\<rrbracket\>>,\<Gamma\>\<vdash\>K
        p.e<rsub|2>:\<alpha\><rsub|0>\<rightarrow\>\<tau\>>,
        <math|<around*|\<llbracket\>|\<Gamma\>\<vdash\>p.e<rsub|2>:\<alpha\><rsub|0>\<rightarrow\>\<tau\>|\<rrbracket\>>,\<Gamma\>\<vdash\>p.e<rsub|2>:\<alpha\><rsub|0>\<rightarrow\>\<tau\>>
        and <math|<around*|\<llbracket\>|\<Gamma\>\<vdash\>e<rsub|1>:\<alpha\><rsub|0>|\<rrbracket\>>,\<Gamma\>\<vdash\>e<rsub|1>:\<alpha\><rsub|0>>.

        <item>By weakening, (1), <name|Abs> and <name|App>, we get
        <math|<around*|\<llbracket\>|\<Gamma\>\<vdash\>e<rsub|1>:\<alpha\><rsub|0>|\<rrbracket\>>\<wedge\><around*|\<llbracket\>|\<Gamma\>\<vdash\>p.e<rsub|2>:\<alpha\><rsub|0>\<rightarrow\>\<tau\>|\<rrbracket\>>\<wedge\><neg|E><around*|(|\<alpha\><rsub|0>|)>,\<Gamma\>\<vdash\>\<lambda\><around*|(|p.e<rsub|2>|)>e<rsub|1>:\<tau\>>.

        <item>By <name|ExLetIn> we get <math|<around*|\<llbracket\>|\<Gamma\>\<vdash\>e<rsub|1>:\<alpha\><rsub|0>|\<rrbracket\>>\<wedge\><around*|\<llbracket\>|\<Gamma\>\<vdash\>K
        p.e<rsub|2>:\<alpha\><rsub|0>\<rightarrow\>\<tau\>|\<rrbracket\>>,\<Gamma\>\<vdash\><text|<with|font-shape|condensed|<strong|let>>>
        p=e<rsub|1> <text|<with|font-shape|condensed|<strong|in>>>
        e<rsub|2>:\<tau\>>, and by <name|LetIn>:
        <math|<around*|\<llbracket\>|\<Gamma\>\<vdash\>e<rsub|1>:\<alpha\><rsub|0>|\<rrbracket\>>\<wedge\><around*|\<llbracket\>|\<Gamma\>\<vdash\>p.e<rsub|2>:\<alpha\><rsub|0>\<rightarrow\>\<tau\>|\<rrbracket\>>\<wedge\><neg|E><around*|(|\<alpha\><rsub|0>|)>,\<Gamma\>\<vdash\><text|<with|font-shape|condensed|<strong|let>>>
        p=e<rsub|1> <text|<with|font-shape|condensed|<strong|in>>>
        e<rsub|2>:\<tau\>>.

        <item>By (3) and <name|DisjElim> we get
        \ <math|<around*|(|<around*|\<llbracket\>|\<Gamma\>\<vdash\>e<rsub|1>:\<alpha\><rsub|0>|\<rrbracket\>>\<wedge\><around*|\<llbracket\>|\<Gamma\>\<vdash\>p.e<rsub|2>:\<alpha\><rsub|0>\<rightarrow\>\<tau\>|\<rrbracket\>>\<wedge\><neg|E><around*|(|\<alpha\><rsub|0>|)>|)>\<vee\><rsub|\<cal-E\>><around*|(|<around*|\<llbracket\>|\<Gamma\>\<vdash\>e<rsub|1>:\<alpha\><rsub|0>|\<rrbracket\>>\<wedge\><around*|\<llbracket\>|\<Gamma\>\<vdash\>K
        p.e<rsub|2>:\<alpha\><rsub|0>\<rightarrow\>\<tau\>|\<rrbracket\>>|)>,\<Gamma\>\<vdash\><text|<with|font-shape|condensed|<strong|let>>>
        p=e<rsub|1> <text|<with|font-shape|condensed|<strong|in>>>
        e<rsub|2>:<no-break>\<tau\>> for <math|\<cal-E\>=<around*|{|K<mid|\|>K\<colons\>\<forall\><wide|\<alpha\><rsub|K>|\<bar\>><wide|\<beta\>|\<bar\>><around|[|E|]>.\<tau\>\<rightarrow\>\<varepsilon\><rsub|K><around*|(|<wide|\<alpha\><rsub|K>|\<bar\>>|)>|}>>.

        <item>By (4), weakening and <name|Hide>, we get the goal.
      </enumerate>

      <item>Theorem <reference|InfCorrExpr> (Correctness) Case: <math|e> is
      <math|e<rsub|1> e<rsub|2>>.

      <\enumerate>
        <item>Let <math|\<alpha\>#FV<around|(|\<Gamma\>,\<tau\>|)>>.

        <item>By the induction hypothesis, we have
        <math|<around*|\<llbracket\>|\<Gamma\>\<vdash\>e<rsub|1>:\<alpha\>\<rightarrow\>\<tau\>|\<rrbracket\>>,\<Gamma\>\<vdash\>e<rsub|1>:\<alpha\>\<rightarrow\>\<tau\>>
        and <math|<around*|\<llbracket\>|\<Gamma\>\<vdash\>e<rsub|2>:\<alpha\>|\<rrbracket\>>,\<Gamma\>\<vdash\>e<rsub|2>:\<alpha\>>.

        <item>By weakening and <name|App>, this yields
        <math|<around*|\<llbracket\>|\<Gamma\>\<vdash\>e<rsub|1>:\<alpha\>\<rightarrow\>\<tau\>|\<rrbracket\>>\<wedge\><around*|\<llbracket\>|\<Gamma\>\<vdash\>e<rsub|2>:<no-break>\<alpha\>|\<rrbracket\>>\<wedge\><neg|E><around*|(|\<alpha\>|)>,\<Gamma\>\<vdash\>e<rsub|1>*e<rsub|2>:<no-break>\<tau\>>.

        <item>By <name|Hide> using (1), <math|<around*|\<llbracket\>|\<Gamma\>\<vdash\>e<rsub|1>*e<rsub|2>:\<tau\>|\<rrbracket\>>,\<Gamma\>\<vdash\>e<rsub|1>*e<rsub|2>:\<tau\>>.
      </enumerate>

      <item>Theorem <reference|InfCorrExpr> (Correctness) Case: <math|e> is
      <math|\<lambda\><rsub|K><wide|c|\<bar\>>>.

      <\enumerate>
        <item>Let <math|\<alpha\><rsub|0>,\<alpha\><rsub|1>#FV<around|(|\<Gamma\>,\<tau\>|)>>.

        <item>By the induction hypothesis, we have
        <math|<around*|\<llbracket\>|\<Gamma\>\<vdash\>\<lambda\><wide|c|\<bar\>>:\<tau\>|\<rrbracket\>>,\<Gamma\>\<vdash\>\<lambda\><wide|c|\<bar\>>:\<tau\>>.

        <item>By weakening, <name|Equ>, <name|Hide> and <name|ExAbs>, we have
        <math|<around*|\<llbracket\>|\<Gamma\>\<vdash\>\<lambda\><wide|c|\<bar\>>:\<tau\>|\<rrbracket\>>\<wedge\>RetType<around*|(|\<tau\>,<no-break>\<alpha\><rsub|0>|)>\<wedge\>\<exists\>\<alpha\><rsub|1>.\<alpha\><rsub|0><wide|=|\<dot\>>\<varepsilon\><rsub|K><around*|(|\<alpha\><rsub|1>|)>,\<Gamma\>\<vdash\>\<lambda\><rsub|K><wide|c|\<bar\>>:\<tau\>>.

        <item>By weakening, this yields the goal.
      </enumerate>

      <item>Theorem <reference|InfComplExpr> (Completeness) Case
      <name|ExIntro>: premise <math|C,\<Gamma\>,\<Sigma\><rprime|'>\<vdash\>n<around*|(|e|)>:\<tau\>>
      for <math|Dom<around*|(|\<Sigma\><rprime|'>|)>\\Dom<around*|(|\<Sigma\>|)>=\<cal-E\><around*|(|e|)>>.

      <\enumerate>
        <item>By induction hypothesis we have
        <math|\<cal-I\><rsub|u>,C\<vDash\><around*|\<llbracket\>|\<Gamma\>,\<Sigma\><rprime|'>\<vdash\>n<around*|(|e|)>:\<tau\>|\<rrbracket\>>>.

        <item>Let <math|\<Sigma\><rsub|1>=\<Sigma\><wide|K\<colons\>\<forall\>\<alpha\><rsub|K>\<gamma\><rsub|K><around|[|\<chi\><rsub|K><around*|(|\<gamma\><rsub|K>,\<alpha\><rsub|K>|)>|]>.\<gamma\><rsub|K>\<rightarrow\>\<varepsilon\><rsub|K><around*|(|\<alpha\><rsub|K>|)>|\<bar\>>>.
        The goal is <math|\<cal-I\><rsub|u>,C\<vDash\>\<cal-I\><rsub|e><around*|(|<around*|\<llbracket\>|\<Gamma\>,\<Sigma\><rsub|1>\<vdash\>n<around*|(|e|)>:\<tau\>|\<rrbracket\>>|)><around*|[|<wide|\<varepsilon\><rsub|K><around*|(|<wide|\<tau\>|\<vect\>>|)>|\<bar\>>\<assign\><wide|\<varepsilon\><rsub|K><around*|(|<wide|\<tau\>|\<bar\>>|)>|\<bar\>>|]>>.

        <item>The goal follows by setting
        <math|\<cal-I\><rsub|e>=\<Sigma\><rprime|'>/\<Sigma\>>.
      </enumerate>

      <item>Theorem <reference|InfComplExpr> (Completeness) Case <name|App>.

      <\enumerate>
        <item><name|App>'s premises are <math|C,\<Gamma\>\<vdash\>e<rsub|1>:\<tau\><rprime|'>\<rightarrow\>\<tau\>>,
        <math|C,\<Gamma\>\<vdash\>e<rsub|2>:\<tau\><rprime|'>> and
        <math|C\<vDash\><neg|E><around*|(|\<tau\><rprime|'>|)>>.

        <item>Pick w.l.o.g. <math|\<alpha\>\<nin\>FV<around|(|C,\<tau\><rprime|'>,\<Gamma\>,\<tau\>|)>>.
        (1) implies <math|C\<wedge\>\<alpha\><wide|=|\<dot\>>\<tau\><rprime|'>\<vDash\><neg|E><around*|(|\<alpha\>|)>>.
        By rule <name|Equ>, (1) implies <math|C\<wedge\>\<alpha\><wide|=|\<dot\>>\<tau\><rprime|'>,\<Gamma\>\<vdash\>e<rsub|1>:\<alpha\>\<rightarrow\>\<tau\>>
        and <math|C\<wedge\>\<alpha\><wide|=|\<dot\>>\<tau\><rprime|'>,\<Gamma\>\<vdash\>e<rsub|2>:\<alpha\>>.

        <item>By induction hypothesis, (2) implies
        <math|\<cal-I\><rsub|i>,C\<wedge\>\<alpha\><wide|=|\<dot\>>\<tau\><rprime|'>\<vDash\>\<Phi\><rsub|i>>
        for <math|\<Phi\><rsub|i>=<around*|\<llbracket\>|\<Gamma\>\<vdash\>e<rsub|i>:\<tau\><rsub|i>|\<rrbracket\>>>,
        <math|i=1,2,\<tau\><rsub|1>\<assign\>\<tau\><rprime|'>\<rightarrow\>\<tau\>,\<tau\><rsub|2>\<assign\>\<tau\><rprime|'>>.

        <item>By (2) and nonemptiness of sorts, we have
        <math|C\<vDash\>\<exists\>\<alpha\>.<around|(|C\<wedge\>\<alpha\><wide|=|\<dot\>>\<tau\><rprime|'>|)>>.

        <item>By (2), (3), and because <math|C\<vDash\>D> implies
        <math|\<exists\>\<alpha\>.C\<vDash\>\<exists\>\<alpha\>.D>, we have
        <math|\<cal-I\><rsub|1>\<cal-I\><rsub|2>,\<exists\>\<alpha\>.<around|(|C\<wedge\>\<alpha\><wide|=|\<dot\>>\<tau\><rprime|'>|)>\<vDash\>\<exists\>\<alpha\>.<around|(|\<Phi\><rsub|1>\<wedge\>\<Phi\><rsub|2>\<wedge\><neg|E><around*|(|\<alpha\>|)>|)>>.

        <item>By (4) and (5), we have the goal
        <math|\<cal-I\>,C\<vDash\><around*|\<llbracket\>|\<Gamma\>\<vdash\>e<rsub|1>
        e<rsub|2>:\<tau\>|\<rrbracket\>>> with
        <math|\<cal-I\>=\<cal-I\><rsub|1>\<cal-I\><rsub|2>>.
      </enumerate>

      <item>Theorem <reference|InfComplExpr> (Completeness) Case
      <name|LetIn>: premise <math|C,\<Gamma\>\<vdash\><text|<with|font-shape|condensed|<strong|let>>>
      p=e<rsub|1> <text|<with|font-shape|condensed|<strong|in>>>
      e<rsub|2>:\<tau\>>.

      <\enumerate>
        <item><name|LetIn>'s premise is: <math|C,\<Gamma\>\<vdash\>\<lambda\><around*|(|p.e<rsub|2>|)>
        e<rsub|1>:\<tau\>>,

        <item>derived by <name|App> and <name|Abs> from
        <math|C,\<Gamma\>\<vdash\>p.e<rsub|2>:\<tau\><rprime|'>\<rightarrow\>\<tau\>>,
        <math|C,\<Gamma\>\<vdash\>e<rsub|1>:\<tau\><rprime|'>> and
        <math|C\<vDash\><neg|E><around*|(|\<tau\><rprime|'>|)>>.

        <item>Inductive hypothesis gives <math|\<cal-I\><rsub|1>,C\<vDash\><around*|\<llbracket\>|\<Gamma\>\<vdash\>p.e<rsub|2>:\<tau\><rprime|'>\<rightarrow\>\<tau\>|\<rrbracket\>>>
        and <math|\<cal-I\><rsub|2>,C\<vDash\><around*|\<llbracket\>|\<Gamma\>\<vdash\>e<rsub|1>:\<tau\><rprime|'>|\<rrbracket\>>>.

        <item>(1) and (3) imply <math|\<cal-I\><rsub|1>,C\<vDash\><around*|\<llbracket\>|\<Gamma\>\<vdash\>p.e<rsub|2>:\<tau\><rprime|'>\<rightarrow\>\<tau\>|\<rrbracket\>>\<wedge\><neg|E><around*|(|\<tau\><rprime|'>|)>\<vee\><rsub|\<cal-E\>><around*|\<llbracket\>|\<Gamma\>\<vdash\>K
        p.e<rsub|2>:\<alpha\><rsub|0>\<rightarrow\>\<tau\>|\<rrbracket\>>> as
        the first disjunct holds.

        <item>As the premise <math|PV<around*|(|C,\<Gamma\>|)>=\<varnothing\>>
        gives disjoint domains for the <math|\<cal-I\><rsub|i>>, we have
        <math|\<cal-I\>,C\<vDash\><around*|\<llbracket\>|\<Gamma\>\<vdash\>e<rsub|1>:\<tau\><rprime|'>|\<rrbracket\>>\<wedge\><around*|(|<around*|\<llbracket\>|\<Gamma\>\<vdash\>p.e<rsub|2>:\<tau\><rprime|'>\<rightarrow\>\<tau\>|\<rrbracket\>>\<wedge\><neg|E><around*|(|\<tau\><rprime|'>|)>\<vee\><rsub|\<cal-E\>><around*|\<llbracket\>|\<Gamma\>\<vdash\>K
        p.e<rsub|2>:\<tau\><rprime|'>\<rightarrow\>\<tau\>|\<rrbracket\>>|)>>
        for <math|\<cal-I\>=\<cal-I\><rsub|1>\<cal-I\><rsub|2>>.

        <item><math|\<cal-I\>,C\<vDash\>\<exists\>\<alpha\><rsub|0>.<around*|\<llbracket\>|\<Gamma\>\<vdash\>e<rsub|1>:\<alpha\><rsub|0>|\<rrbracket\>>\<wedge\><around*|(|<around*|\<llbracket\>|\<Gamma\>\<vdash\>p.e<rsub|2>:\<alpha\><rsub|0>\<rightarrow\>\<tau\>|\<rrbracket\>>\<wedge\><neg|E><around*|(|\<alpha\><rsub|0>|)>\<vee\><rsub|\<cal-E\>><around*|\<llbracket\>|\<Gamma\>\<vdash\>K
        p.e<rsub|2>:\<alpha\><rsub|0>\<rightarrow\>\<tau\>|\<rrbracket\>>|)>>
        by abstracting <math|\<alpha\><rsub|0>=\<tau\><rprime|'>>.
      </enumerate>

      <item>Theorem <reference|InfComplExpr> (Completeness) Case
      <name|ExLetIn>:<next-line>premise <math|C,\<Gamma\>\<vdash\><text|<with|font-shape|condensed|<strong|let>>>
      p=e<rsub|1> <text|<with|font-shape|condensed|<strong|in>>>
      e<rsub|2>:\<tau\>>.

      <\enumerate>
        <item><name|ExLetIn>'s premises are: <math|C,\<Gamma\>\<vdash\>K
        p.e<rsub|2>:\<tau\><rprime|'>\<rightarrow\>\<tau\>> and
        <math|C,\<Gamma\>\<vdash\>e<rsub|1>:\<tau\><rprime|'>>,

        <item>Inductive hypothesis gives <math|\<cal-I\><rsub|1>,C\<vDash\><around*|\<llbracket\>|\<Gamma\>\<vdash\>K
        p.e<rsub|2>:\<tau\><rprime|'>\<rightarrow\>\<tau\>|\<rrbracket\>>>
        and <math|\<cal-I\><rsub|2>,C\<vDash\><around*|\<llbracket\>|\<Gamma\>\<vdash\>e<rsub|1>:\<tau\><rprime|'>|\<rrbracket\>>>.

        <item>(3) implies <math|\<cal-I\><rsub|1>,C\<vDash\><around*|\<llbracket\>|\<Gamma\>\<vdash\>p.e<rsub|2>:\<tau\><rprime|'>\<rightarrow\>\<tau\>|\<rrbracket\>>\<wedge\><neg|E><around*|(|\<tau\><rprime|'>|)>\<vee\><rsub|\<cal-E\>><around*|\<llbracket\>|\<Gamma\>\<vdash\>K
        p.e<rsub|2>:\<tau\><rprime|'>\<rightarrow\>\<tau\>|\<rrbracket\>>> as
        one of the <math|\<vee\><rsub|\<cal-E\>>> disjuncts holds. The proof
        concludes as in the <name|LetIn> case.
      </enumerate>

      <item>Theorem <reference|InfComplExpr> (Completeness) Case
      <name|ExAbs>: premise <math|C,\<Gamma\>\<vdash\>\<lambda\><rsub|K><wide|c|\<bar\>>:\<tau\>>.

      <\enumerate>
        <item><name|ExAbs>'s premises are: <em|(a)>
        <math|C,\<Gamma\>\<vdash\>\<lambda\><wide|c|\<bar\>>:\<tau\>> and
        <em|(b)> <math|C\<vDash\>RetType<around*|(|\<tau\>,\<varepsilon\><rsub|K><around*|(|<wide|\<tau\>|\<bar\>><rprime|'>|)>|)>>.

        <item>Inductive hypothesis gives <math|\<cal-I\><rsub|1>,C\<vDash\><around*|\<llbracket\>|\<Gamma\>\<vdash\>\<lambda\><wide|c|\<bar\>>:\<tau\>|\<rrbracket\>>>.

        <item>Let <math|\<alpha\><rsub|0>,\<alpha\><rsub|1>#FV<around|(|\<Gamma\>,\<tau\>|)>>.
        (1b) and (2) give <math|\<cal-I\><rsub|1>,C\<vDash\>\<exists\>\<alpha\><rsub|0>.<around*|\<llbracket\>|\<Gamma\>\<vdash\>\<lambda\><wide|c|\<bar\>>:\<tau\>|\<rrbracket\>>\<wedge\>RetType<around*|(|\<tau\>,<no-break>\<alpha\><rsub|0>|)>\<wedge\>\<exists\>\<alpha\><rsub|1>.\<alpha\><rsub|0><wide|=|\<dot\>>\<varepsilon\><rsub|K><around*|(|\<alpha\><rsub|1>|)>\<wedge\>\<alpha\><rsub|1><wide|=|\<dot\>><wide|\<tau\>|\<bar\>><rprime|'>>.

        <item>Let <math|\<cal-I\><rsub|0>=<around*|[|\<chi\><rsub|K><around*|(|\<alpha\>|)>\<assign\>\<alpha\><wide|=|\<dot\>><wide|\<tau\>|\<bar\>><rprime|'>|]>>.
        By (3), <math|\<cal-I\><rsub|0>\<cal-I\><rsub|1>,C\<vDash\>\<exists\>\<alpha\><rsub|0>.RetType<around*|(|\<tau\>,\<alpha\><rsub|0>|)>\<wedge\><around*|(|\<exists\>\<alpha\><rsub|1>.\<alpha\><rsub|0><wide|=|\<dot\>>\<varepsilon\><rsub|K><around*|(|\<alpha\><rsub|1>|)>\<wedge\>\<chi\><rsub|K><around*|(|\<alpha\><rsub|1>|)>|)>\<wedge\><around*|\<llbracket\>|\<Gamma\>\<vdash\>\<lambda\><wide|c|\<bar\>>:\<tau\>|\<rrbracket\>>>
        which is the goal.
      </enumerate>
    </itemize>
  </proof>

  <subsection|Semantics by Reduction to <math|HMG<around*|(|X|)>>><label|SemanticProofs>

  By induction on the structure of the derivation, we can show the following:

  <\proposition>
    <label|PredVarSubstDeriv>Let <math|\<cal-I\>> be an interpretation of
    predicate variables for formula <math|C>, as in Definition
    <reference|InterprPredVars>. If a typing judgment
    <math|C,\<Gamma\>,\<Sigma\>\<vdash\>e:\<tau\>> is derivable in the type
    system <math|MMG<rsub|\<exists\>><around*|(|X|)>>, then
    <math|\<cal-I\><around*|(|C|)>,\<cal-I\><around*|(|\<Gamma\>|)>,\<cal-I\><around*|(|\<Sigma\>|)>\<vdash\>e:\<tau\>>
    is derivable in <math|MMG<rsub|\<exists\>><around*|(|X|)>>.
  </proposition>

  Proof of Theorem <reference|SemRedHMG>.

  <\proof>
    Let <math|\<cal-I\>> be a subsitution of predicate variables such that
    <math|\<cal-M\>,\<cal-I\>\<vDash\>\<exists\>FV<around*|(|\<tau\>|)>.<around*|\<llbracket\>|\<Gamma\>,\<Sigma\>\<vdash\>e:\<tau\>|\<rrbracket\>>>.
    By Theorems <reference|InfCorrExpr> and <reference|InfCorrComplEx>, there
    exists a derivation of <math|<around*|\<llbracket\>|\<Gamma\>,\<Sigma\>\<vdash\>e:\<tau\>|\<rrbracket\>>,\<Gamma\>,\<Sigma\>\<vdash\>e:\<tau\>>.
    Without loss of generality, let <name|ExIntro> be the rule applied at the
    root of the derivation, and let <math|\<Delta\>> be the derivation of the
    premise <math|<around*|\<llbracket\>|\<Gamma\>,\<Sigma\>\<vdash\>e:\<tau\>|\<rrbracket\>>,\<Gamma\>,\<Sigma\><rprime|''>\<vdash\>n<around*|(|e|)>:<no-break>\<tau\>>.
    Let <math|\<Gamma\><rprime|'>=\<cal-I\><around*|(|\<Gamma\>|)>>,
    <math|C=\<cal-I\><around*|(|<around*|\<llbracket\>|\<Gamma\>,\<Sigma\>\<vdash\>e:\<tau\>|\<rrbracket\>>|)>>
    and <math|\<Sigma\><rprime|'>=\<cal-I\><around*|(|\<Sigma\><rprime|''>|)>>.
    By Proposition <reference|PredVarSubstDeriv>, there exists a derivation
    <math|\<Delta\>> of <math|C,\<Gamma\><rprime|'>,\<Sigma\><rprime|'>\<vdash\>e:<no-break>\<tau\>>.
    We need to construct a derivation <math|\<Delta\><rprime|'>> of
    <math|C<rprime|'>,\<Gamma\><rprime|'>\<vdash\>e<rprime|'>:\<tau\>> under
    constructor environment <math|\<Sigma\><rprime|'>> in the
    <math|HMG<around*|(|X|)>> type system. The tag erasure of
    <math|e<rprime|'>> w.r.t. <math|\<Sigma\>> has to be computationally
    equivalent to the HMG-form of <math|e> and <math|C<rprime|'>> has to be
    satisfiable. We will transform <math|\<Delta\>> into a derivation in
    <math|HMG<around*|(|X|)>> while preserving these conditions. We transform
    the resulting constraint, the resulting expression and the derivation
    simultaneously, as follows:

    <\itemize>
      <item>For a derivation node applying rule <name|App>, we erase the
      <math|C\<vDash\><neg|E><around*|(|\<tau\><rprime|'>|)>> condition in
      the premise of the node, and we erase
      <math|<neg|E><around*|(|\<alpha\>|)>> in the corresponding
      <math|<around*|\<llbracket\>|\<Gamma\>\<vdash\>e<rsub|1>
      e<rsub|2>:\<tau\>|\<rrbracket\>>> part of the resulting constraint,
      where <math|C,\<tau\><rprime|'>,\<alpha\>> etc. name the actual pieces
      of the derivation or constraint.

      <item>For a derivation node <name|Abs>, with
      <math|\<lambda\><around*|(|<wide|p<rsub|i>.e<rsub|i>|\<bar\>>|)>> in
      conclusion, we erase derivation subtrees with <name|NegClause> or
      <name|FailClause> nodes at the root. Correspondingly, we replace the
      expression in the conclusion by <math|\<lambda\><around*|(|<wide|<around*|(|p<rsub|i>.e<rsub|i><rprime|'>|)>|\<bar\>><rsub|i:\<neg\>unreach<around*|(|e<rsub|i><rprime|'>|)>\<vee\>failure<around*|(|e<rsub|i>|)>>|)>><math|>,
      which preserves computational equivalence; and we erase the
      <math|<around*|\<llbracket\>|\<Gamma\>\<vdash\>p<rsub|i>.e<rsub|i>:\<tau\><rsub|1>\<rightarrow\>\<tau\><rsub|2>|\<rrbracket\>>>
      conjuncts of the resulting constraint for
      <math|i:unreach<around*|(|e<rsub|i>|)>\<vee\>failure<around*|(|e<rsub|i>|)>>,
      which leads to a weaker formula and thus preserves satisfiability.

      <item>We replace derivation nodes <name|ExLetIn> by applications of the
      <name|App> rule to the premises <math|C,\<Gamma\>\<vdash\><around*|(|K
      p.e<rsub|2>|)> e<rsub|1>:\<tau\><rprime|'>\<rightarrow\>\<tau\>> and
      <math|C,\<Gamma\>\<vdash\>e<rsub|1>:\<tau\><rprime|'>>, and replace the
      corresponding subexpressions <math|<text|<with|font-shape|condensed|<strong|let>>>
      p=e<rsub|1> <text|<with|font-shape|condensed|<strong|in>>> e<rsub|2>>
      of the resulting expression by <math|<around*|(|K p.e<rsub|2>|)>
      e<rsub|1>>. We replace the <math|<around*|\<llbracket\>|\<Gamma\>\<vdash\><text|<with|font-shape|condensed|<strong|let>>>
      p=e<rsub|1> <text|<with|font-shape|condensed|<strong|in>>>
      e<rsub|2>:\<tau\>|\<rrbracket\>>> part of the resulting constraint by
      <math|\<exists\>\<alpha\><rsub|0>.<around*|\<llbracket\>|\<Gamma\>\<vdash\>e<rsub|1>:\<alpha\><rsub|0>|\<rrbracket\>>\<wedge\><around*|\<llbracket\>|\<Gamma\>\<vdash\>K
      p.e<rsub|2>:\<alpha\><rsub|0>\<rightarrow\>\<tau\>|\<rrbracket\>>>. To
      see that the satisfiability of the constraint is preserved, recall that
      <math|<around*|\<llbracket\>|\<Gamma\>\<vdash\><text|<with|font-shape|condensed|<strong|let>>>
      p=e<rsub|1> <text|<with|font-shape|condensed|<strong|in>>>
      e<rsub|2>:\<tau\>|\<rrbracket\>>> is a disjunction where only one
      disjunct is consistent with <math|\<exists\><wide|\<alpha\>|\<bar\>>.\<tau\><rprime|'><wide|=|\<dot\>>\<varepsilon\><rsub|K><around*|(|<wide|\<alpha\>|\<bar\>>|)>>.
      The tag erasure of <math|<around*|(|K p.e<rsub|2>|)> e<rsub|1>> w.r.t.
      the original constructor environment <math|\<Sigma\>> is
      computationally equivalent to <math|<text|<with|font-shape|condensed|<strong|let>>>
      p=e<rsub|1> <text|<with|font-shape|condensed|<strong|in>>> e<rsub|2>>.

      <item>We excise derivation nodes <name|ExAbs>, and remove the
      corresponding <math|RetType> atom from <math|C>, preserving
      computational equivalence and satisfiability.

      <item>For remaining nodes are easy to rearrange into applications of
      the corresponding <math|HMG<around*|(|X|)>> rules.
    </itemize>
  </proof>

  Proof of Corollary <reference|TypeSoundness>.

  <\proof>
    The semantics of expression <math|e> in
    <math|MMG<rsub|\<exists\>><around*|(|X|)>> is given by the semantics of
    its HMG-form in <math|HMG<around*|(|X|)>>. By well-typedness and
    closedness, we have <math|C,\<varnothing\>,\<Sigma\>\<vdash\>e:\<sigma\>>
    is derivable for some type scheme <math|\<sigma\>>, and
    <math|\<cal-M\>\<vDash\>C>. By Theorems <reference|InfComplExpr> and
    <reference|InfCorrComplEx>, there exists an interpretation of predicate
    variables <math|\<cal-I\>> such that <math|\<cal-M\>,\<cal-I\>\<vDash\>C\<Rightarrow\><around*|\<llbracket\>|\<varnothing\>,\<Sigma\>\<vdash\>e:<no-break>\<sigma\>|\<rrbracket\>>>,
    thus <math|\<cal-M\>,\<cal-I\>\<vDash\><around*|\<llbracket\>|\<varnothing\>,\<Sigma\>\<vdash\>e:<no-break>\<sigma\>|\<rrbracket\>>>.

    By Theorem <reference|SemRedHMG>, we have an <math|HMG<around*|(|X|)>>
    environment <math|\<Gamma\><rprime|'>>, constructor environment
    <math|\<Sigma\><rprime|'>> and an expression <math|e<rprime|'>> such that
    <math|C,\<Gamma\><rprime|'>\<vdash\>e<rprime|'>:\<tau\>> is derivable in
    <math|HMG<around*|(|X|)>> for a valid <math|C>, and the tag erasure of
    <math|e<rprime|'>> w.r.t. <math|\<Sigma\>> is computationally equivalent
    to the HMG-form of <math|e>. By <cite|simonet-pottier-hmg-toplas> Theorem
    3.31, see also Theorem <reference|HMGSoundness>, <math|e<rprime|'>> does
    not go wrong. Given the call-by-value semantics presented in
    <cite|simonet-pottier-hmg-toplas>, it is easy to see that the tag erasure
    of <math|e<rprime|'>> does not go wrong. By computational equivalence,
    HMG-form of <math|e> does not go wrong.
  </proof>

  <section|Constraint Abduction>

  <subsection|Formulating the Joint Constraint Abduction Problem>

  <\proposition>
    <label|SolvedForm><em|Solved form property for terms>. Let
    <math|<wide|\<beta\>|\<bar\>>=Dom<around*|(|\<b-U\><around|(|C|)>|)>> be
    all variables occurring on the left-hand sides of solved form equations
    <math|\<b-U\><around|(|C|)>>, and <math|\<alpha\>\<in\>FV(Image<around|(|\<b-U\><around|(|C|)>|)>>
    be a variable occurring on the right-hand side. If
    <math|T\<vDash\>\<cal-Q\>.C> (equivalently
    <math|\<cal-Q\>.\<b-U\><around|(|C|)>>) holds, then
    <math|T\<vDash\>\<cal-Q\>.C<around*|[|\<alpha\>\<assign\>\<tau\>|]>>
    (equivalently <math|T\<vDash\>\<cal-Q\>.\<b-U\><around|(|C|)><around*|[|\<alpha\>\<assign\>\<tau\>|]>>),
    for any <math|\<tau\>> such that for all
    <math|\<alpha\><rprime|'>\<in\>FV<around*|(|\<tau\>|)>>,
    <math|\<alpha\><rprime|'>\<leqslant\><rsub|\<cal-Q\>>\<alpha\>>.
  </proposition>

  <subsection|Abduction Algorithm for The Combination of
  Domains><label|SortCombProof>

  <\lemma>
    <label|SolvedFormProj>For any conjunction of atoms
    <math|D\<in\>\<cal-L\><rsub|s<rsub|type>>>, let <math|D<rsup|t>> be
    <math|D> with all alien subterms <math|<wide|r|\<bar\>>> replaced with
    fresh variables <math|<wide|\<alpha\><rsub|r>|\<bar\>>>,
    <math|D<rsup|t>\<in\>\<cal-L\><rsub|ty>>. Let
    <math|\<wedge\><rsub|s>D<rsub|s><rsup|t>=\<b-U\><around|(|D<rsup|t>|)>>
    be a solved form with <math|D<rsub|s><rsup|t>\<in\>\<cal-L\><rsub|s>>.
    Observe that for any <math|\<Psi\>>, for any
    <math|C\<in\>\<cal-L\><rsub|s>>, if <math|\<cal-M\>\<vDash\>D\<wedge\>\<Psi\>\<Rightarrow\>C>,
    then

    <\enumerate>
      <item><math|\<cal-M\>\<vDash\>D<rsub|s><rsup|t><around|[|<wide|\<alpha\><rsub|r>|\<bar\>>\<assign\><wide|r|\<bar\>>|]>\<wedge\>\<Psi\>\<Rightarrow\>C>
      for <math|s\<neq\>s<rsub|type>>.

      <item>For <math|s=s<rsub|type>>, let
      <math|\<wedge\><rsub|s>C<rsub|s><rsup|t>=\<b-U\><around|(|C<rsup|t>|)>>,
      where <math|C<rsup|t>> is <math|C> with all alien subterms
      <math|<wide|r|\<bar\>><rprime|'>> replaced with fresh variables
      <math|<wide|\<alpha\><rsub|r>|\<bar\>><rprime|'>>. Then there exist a
      conjunction of equations <math|E> over
      <math|<wide|\<alpha\><rsub|r>|\<bar\>><wide|\<alpha\><rsub|r>|\<bar\>><rprime|'>>
      such that <math|T\<vDash\>D<rsub|s<rsub|type>><rsup|t>\<wedge\>E\<wedge\>\<Psi\>\<Rightarrow\>C<rsub|s<rsub|type>><rsup|t>>
      and (for <math|s\<neq\>s<rsub|type>>)
      <math|\<cal-M\>\<vDash\>D<rsub|s><rsup|t><around|[|<wide|\<alpha\><rsub|r>|\<bar\>>\<assign\><wide|r|\<bar\>>|]>\<wedge\>\<Psi\>\<wedge\><wide|\<alpha\><rsub|r><rsup|s>|\<bar\>><wide|=|\<dot\>><wide|r<rsup|s>
      |\<bar\>>\<Rightarrow\>E<rsub|s>> where <math|E<rsub|s>> are
      <math|E\<cap\>\<cal-L\><rsub|s>>.
    </enumerate>
  </lemma>

  The proof uses the <em|type conservation> and <em|free generation>
  (<math|s<rsub|type>> properties) and interpolation techniques. Below
  follows a sketch of a proof of (2).

  <\proof>
    Observe a proof of <math|D<rsup|t><around|[|<wide|\<alpha\><rsub|r>|\<bar\>>\<assign\><wide|r|\<bar\>>|]>\<wedge\>\<Psi\>\<Rightarrow\>C<rsup|t><around|[|<wide|\<alpha\><rsub|r>|\<bar\>><rprime|'>\<assign\><wide|r|\<bar\>><rprime|'>|]>>
    (assuming a complete proof system for <math|\<cal-M\>\<vDash\>>). It can
    be transformed into a proof of <math|D<rsup|t>\<wedge\>\<Psi\>\<wedge\><wide|\<alpha\><rsub|r>|\<bar\>><wide|=|\<dot\>><wide|r|\<bar\>>\<wedge\><wide|\<alpha\><rsub|r>|\<bar\>><rprime|'><wide|=|\<dot\>><wide|r|\<bar\>><rprime|'>\<Rightarrow\>C<rsup|t>>.
    By <math|s<rsub|type>> properties we get
    <math|D<rsup|t><rsub|s<rsub|type>>\<wedge\>\<Psi\>\<wedge\>E<rsub|0>\<wedge\><wide|\<alpha\><rsub|r>|\<bar\>><wide|=|\<dot\>><wide|r|\<bar\>>\<wedge\><wide|\<alpha\><rsub|r>|\<bar\>><rprime|'><wide|=|\<dot\>><wide|r|\<bar\>><rprime|'>\<Rightarrow\>C<rsup|t><rsub|s<rsub|type>>>
    where <math|E<rsub|0>> are equations among
    <math|<wide|\<alpha\><rsub|r>|\<bar\>>>. By interpolation we get
    <math|D<rsub|s<rsub|type>><rsup|t>\<wedge\>E\<wedge\>\<Psi\>\<Rightarrow\>C<rsub|s<rsub|type>><rsup|t>>
    and <math|D<rsup|t>\<wedge\>\<Psi\>\<wedge\><wide|\<alpha\><rsub|r>|\<bar\>><wide|=|\<dot\>><wide|r|\<bar\>>\<wedge\><wide|\<alpha\><rsub|r>|\<bar\>><rprime|'><wide|=|\<dot\>><wide|r|\<bar\>><rprime|'>\<Rightarrow\>E>
    for <math|E<rsub|0>\<subseteq\>E> and <math|E> as required by the
    theorem, since <math|<wide|\<alpha\><rsub|r>|\<bar\>>> are the only
    non-<math|s<rsub|type>> subterms of <math|C<rsup|t><rsub|s<rsub|type>>>.
  </proof>

  Proof of Theorem <reference|MultisortAbdThm>.

  <\proof>
    We use the same notation as in Table <reference|MultisortAbd>. Note, that
    the JCAQP with a branch with unsatisfiable conclusion does not have an
    answer, \ so we do not consider unsatisfiable conclusions.

    Observe that validity of <math|\<cal-L\><rsub|ty>> formula in
    <with|mode|math|T> is equivalent to its validity in <math|\<cal-M\>>. We
    will therefore sometimes drop prefixes
    <with|mode|math|\<cal-M\>\<vDash\>> and <with|mode|math|T\<vDash\>> for
    readability.

    Let us check correctness, i.e. that <math|\<exists\><wide|\<alpha\><rsub|ans>|\<bar\>>.A<rsub|ans>\<in\>Abd<around*|(|\<cal-Q\>,<wide|\<beta\>|\<bar\>>,<wide|D<rsub|i>,C<rsub|i>|\<bar\>>|)>>
    are JCAQP<rsub|<math|\<cal-M\>>> answers.

    <\enumerate>
      <item>We need to show: <math|\<cal-M\>\<vDash\>\<wedge\><rsub|i><around|(|D<rsub|i>\<wedge\>A<rsub|ans>\<Rightarrow\>C<rsub|i>|)>>,

      <item><math|\<cal-M\>\<vDash\>\<cal-Q\>.A<rsub|ans><around*|[|<wide|\<alpha\>|\<bar\>><rsub|ans><wide|\<beta\>|\<bar\>>\<assign\><wide|t|\<bar\>>|]>>
      for some <math|<wide|t|\<bar\>>>,

      <item><math|\<cal-M\>\<vDash\>\<wedge\><rsub|i>\<exists\>FV<around|(|D<rsub|i>\<wedge\>A<rsub|ans>|)>.D<rsub|i>\<wedge\>A<rsub|ans>>,

      <item>for all atoms <math|c\<in\>A<rsub|ans>> such that
      <math|\<cal-M\>\<nvDash\>\<cal-Q\>.c> and
      <math|FV<around*|(|c|)>\<cap\><wide|\<beta\>|\<bar\>>\<neq\>\<varnothing\>>,
      then for all <math|\<beta\><rsub|1>\<in\>FV<around*|(|c|)>> such that
      <math|<around*|(|\<forall\>\<beta\><rsub|1>|)>\<in\>\<cal-Q\>>, there
      exists <math|\<beta\><rsub|2>\<in\>FV<around*|(|c|)>\<cap\><wide|\<beta\>|\<bar\>>>
      such that <math|\<beta\><rsub|1>\<leqslant\><rsub|\<cal-Q\>>\<beta\><rsub|2>>.

      <item>We have: <math|\<cal-M\>\<vDash\>\<wedge\><rsub|i><around|(|D<rsub|i,s<rsub|type>><rsup|t>\<wedge\>A<rsub|T><rsup|j>\<Rightarrow\>C<rsub|i,s<rsub|type>><rsup|t>|)>>,

      <item><math|\<cal-M\>\<vDash\>\<cal-Q\>.A<rsub|T><rsup|j><around*|[|<wide|\<alpha\>|\<bar\>><rsub|j><rsup|T><wide|<wide|\<alpha\><rsub|r>|\<bar\>>|\<bar\>><wide|\<beta\>|\<bar\>>\<assign\><wide|t|\<bar\>><rsub|j><rsup|T>|]>>
      for some <math|<wide|t|\<bar\>><rsub|j><rsup|T>>,

      <item><math|\<cal-M\>\<vDash\>\<wedge\><rsub|i>\<exists\>FV<around|(|D<rsub|i,s<rsub|type>><rsup|t>\<wedge\>A<rsub|T><rsup|j>|)>.D<rsub|i,s<rsub|type>><rsup|t>\<wedge\>A<rsub|T><rsup|j>>,

      <item>for all atoms <math|\<beta\><rsub|2><wide|=|\<dot\>>t\<in\>A<rsub|T><rsup|j>>
      such that <math|\<beta\><rsub|2>\<in\><wide|<wide|\<alpha\><rsub|r>|\<bar\>>|\<bar\>><wide|\<beta\>|\<bar\>>>,
      if <math|\<beta\><rsub|1>\<in\>FV<around*|(|c|)>> such that
      <math|<around*|(|\<forall\>\<beta\><rsub|1>|)>\<in\>\<cal-Q\>>, then
      <math|\<beta\><rsub|1>\<leqslant\><rsub|\<cal-Q\>>\<beta\><rsub|2>>.

      <item>We have: <math|\<cal-M\>\<vDash\>\<wedge\><rsub|i><around|(|D<rsub|i><rsup|s>\<wedge\><around*|(|D<rsup|t><rsub|i,s>\<wedge\>A<rsup|i><rsub|p,j,s>|)><around|[|<wide|<wide|\<alpha\><rsub|r>|\<bar\>>|\<bar\>>\<assign\><wide|<wide|r|\<bar\>>|\<bar\>>|]>\<wedge\>A<rsub|s><rsup|k<rsub|j><rsup|s>>\<Rightarrow\>C<rsub|i><rsup|s>\<wedge\><around*|(|C<rsub|i,s><rsup|t>\<wedge\>A<rsup|i><rsub|c,j,s>|)><around|[|<wide|<wide|\<alpha\><rsub|r>|\<bar\>>|\<bar\>>\<assign\><wide|<wide|r|\<bar\>>|\<bar\>>|]>|)>>,

      <item><math|\<cal-M\>\<vDash\>\<cal-Q\>.A<rsub|s><rsup|k<rsub|j><rsup|s>><around*|[|<wide|\<alpha\><rsub|s><rsup|k<rsub|j><rsup|s>>|\<bar\>><wide|\<alpha\>|\<bar\>><rsub|r><rsup|j><wide|\<beta\>|\<bar\>>\<assign\><wide|t|\<bar\>><rsub|k<rsub|j><rsup|s>>|]>>
      for some <math|<wide|t|\<bar\>><rsub|k<rsub|j><rsup|s>>>,

      <item><math|\<cal-M\>\<vDash\>\<wedge\><rsub|i>\<exists\>FV<around|(|D<rsub|i><rsup|s>\<wedge\><around*|(|D<rsup|t><rsub|i,s>\<wedge\>A<rsup|i><rsub|p,j,s>|)><around|[|<wide|<wide|\<alpha\><rsub|r>|\<bar\>>|\<bar\>>\<assign\><wide|<wide|r|\<bar\>>|\<bar\>>|]>\<wedge\>A<rsub|s><rsup|k<rsub|j><rsup|s>>|)>.D<rsub|i><rsup|s>\<wedge\><around*|(|D<rsup|t><rsub|i,s>\<wedge\>A<rsup|i><rsub|p,j,s>|)><around|[|<wide|<wide|\<alpha\><rsub|r>|\<bar\>>|\<bar\>>\<assign\><wide|<wide|r|\<bar\>>|\<bar\>>|]>\<wedge\>A<rsub|s><rsup|k<rsub|j><rsup|s>>>,

      <item>for all atoms <math|c\<in\>A<rsub|s><rsup|k<rsub|j><rsup|s>>>
      such that <math|\<cal-M\>\<nvDash\>\<cal-Q\>.c> and
      <math|FV<around*|(|c|)>\<cap\><wide|\<beta\>|\<bar\>>\<neq\>\<varnothing\>>,
      then for all <math|\<beta\><rsub|1>\<in\>FV<around*|(|c|)>> such that
      <math|<around*|(|\<forall\>\<beta\><rsub|1>|)>\<in\>\<cal-Q\>>, there
      exists <math|\<beta\><rsub|2>\<in\>FV<around*|(|c|)>\<cap\><wide|\<beta\>|\<bar\>>>
      such that <math|\<beta\><rsub|1>\<leqslant\><rsub|\<cal-Q\>>\<beta\><rsub|2>>.

      <item>We have: <math|D<rsub|i>\<equiv\>\<wedge\><rsub|s>D<rsub|i><rsup|s>>
      and <math|C<rsub|i>\<equiv\>\<wedge\><rsub|s>C<rsub|i><rsup|s>>;
      <math|D<rsub|i><rsup|t><around|[|<wide|<wide|\<alpha\><rsub|r>|\<bar\>>|\<bar\>>\<assign\><wide|<wide|r|\<bar\>>|\<bar\>>|]>=D<rsup|s<rsub|type>><rsub|i>>,
      <math|C<rsub|i><rsup|t><around|[|<wide|<wide|\<alpha\><rsub|r>|\<bar\>>|\<bar\>>\<assign\><wide|<wide|r|\<bar\>>|\<bar\>>|]>=C<rsup|s<rsub|type>><rsub|i>>;
      <math|A<rsup|i><rsub|p><rsub|j>=<around*|{|x<wide|=|\<dot\>>t\<in\>\<b-U\><around*|(|D<rsub|i,s<rsub|type>><rsup|t>\<wedge\>A<rsub|T><rsup|j><rprime|'>|)>\|x\<in\>X<rsub|s>,s\<neq\>s<rsub|type>|}>>
      and <math|A<rsup|i><rsub|c><rsub|j>=<around*|{|x<wide|=|\<dot\>>t\<in\>\<b-U\><around*|(|D<rsub|i,s<rsub|type>><rsup|t>\<wedge\>C<rsub|i,s<rsub|type>><rsup|t>\<wedge\>A<rsub|T><rsup|j><rprime|'>|)>\|x\<in\>X<rsub|s>,s\<neq\>s<rsub|type>|}>>,
      <math|A<rsup|i><rsub|p/c,j>=\<wedge\><rsub|s>A<rsub|p/c,j,s><rsup|i>>,
      where <math|A<rsub|p/c,j,s><rsup|i>\<in\>\<cal-L\><rsub|s>>.

      <item><math|D<rsub|i>\<wedge\><wide|r<rsub|i>|\<bar\>><wide|=|\<dot\>><wide|\<alpha\><rsub|r<rsub|i>>|\<bar\>>\<Rightarrow\>\<wedge\><rsub|s>D<rsub|i><rsup|s>\<wedge\>D<rsub|i,s><rsup|t>>,
      <math|\<wedge\><rsub|s>C<rsub|i><rsup|s>\<wedge\>C<rsub|i,s><rsup|t>\<wedge\><wide|r<rsub|i>|\<bar\>><wide|=|\<dot\>><wide|\<alpha\><rsub|r<rsub|i>>|\<bar\>>\<Rightarrow\>C<rsub|i>>,
      by (13).

      <item>We have: <math|A<rsub|ans>=A<rsub|T><rsup|j><rprime|'>\<wedge\><rsub|s\<in\>usorts>A<rsub|s><rsup|k<rsub|j><rsup|s>>>
      for some <math|j,<wide|k<rsub|j><rsup|s>|\<bar\>>> and
      <math|<wide|\<alpha\>|\<bar\>><rsub|ans>=<wide|\<alpha\><rsub|j><rsup|T>|\<bar\>><rprime|'><wide|<wide|\<alpha\><rsub|s><rsup|k<rsub|j><rsup|s>>|\<bar\>>|\<bar\>>\<cap\>FV<around*|(|A<rsub|T><rsup|j><rprime|'>\<wedge\><rsub|s>A<rsub|s><rsup|k<rsub|j><rsup|s>>|)>>,
      <math|<wide|<wide|\<alpha\><rsub|s><rsup|k<rsub|j><rsup|s>>|\<bar\>>|\<bar\>>>
      is a concatenation of <math|<wide|\<alpha\><rsub|s><rsup|k<rsub|j><rsup|s>>|\<bar\>>>
      for <math|s\<in\>usorts>.

      <item>By type preservation and free generation, (5) we can have
      <math|D<rsub|i,s<rsub|type>><rsup|t>\<wedge\>A<rsub|T><rsup|j><rprime|'>\<Rightarrow\>C<rsub|i,s<rsub|type>><rsup|t><rprime|'>>,
      where <math|C<rsub|i,s<rsub|type>><rsup|t><rprime|'>> differs from
      <math|C<rsub|i,s<rsub|type>><rsup|t>> only at alien subterm positions.
      Pick <math|C<rsub|i,s<rsub|type>><rsup|t><rprime|'>> which differs from
      <math|C<rsub|i,s<rsub|type>><rsup|t>> on the least number of alien
      subterm positions.

      <item>Consider <math|S=<around*|{|x<wide|=|\<dot\>>t\<in\>\<b-U\><around*|(|C<rsub|i,s<rsub|type>><rsup|t>\<wedge\>C<rsub|i,s<rsub|type>><rsup|t><rprime|'>|)>\|x\<in\>X<rsub|s>,s\<neq\>s<rsub|type>|}>>.
      Note that <math|S\<wedge\>C<rsub|i,s<rsub|type>><rsup|t><rprime|'>\<Rightarrow\>C<rsup|t><rsub|i,s<rsub|type>>>.

      <item>By (16) and separation of sorts, we have
      <math|\<b-U\><around*|(|D<rsub|i,s<rsub|type>><rsup|t>\<wedge\>C<rsub|i,s<rsub|type>><rsup|t>\<wedge\>A<rsub|T><rsup|j><rprime|'>|)>\\\<cal-L\><rsub|s<rsub|type>>\<Rightarrow\>\<b-U\><around*|(|C<rsub|i,s<rsub|type>><rsup|t>\<wedge\>C<rsub|i,s<rsub|type>><rsup|t><rprime|'>|)>\\\<cal-L\><rsub|s<rsub|type>>>,
      i.e. <math|A<rsup|i><rsub|c><rsub|j>\<Rightarrow\>S>.

      <item><math|D<rsub|i>\<wedge\>A<rsub|ans>\<wedge\><wide|<wide|r|\<bar\>>|\<bar\>><wide|=|\<dot\>><wide|<wide|\<alpha\><rsub|r>|\<bar\>>|\<bar\>><above|\<Longrightarrow\>|<around|(|13,14|)>>D<rsub|i><rsup|s<rsub|type>>\<wedge\><rsub|s>D<rsub|i><rsup|s>\<wedge\>D<rsub|i,s><rsup|t><around|[|<wide|<wide|\<alpha\><rsub|r>|\<bar\>>|\<bar\>>\<assign\><wide|<wide|r|\<bar\>>|\<bar\>>|]>\<wedge\>A<rsub|T><rsup|j><rprime|'>\<wedge\><rsub|s\<neq\>s<rsub|type>>A<rsub|s><rsup|k<rsub|j><rsup|s>>\<wedge\><wide|<wide|r|\<bar\>>|\<bar\>><wide|=|\<dot\>><wide|<wide|\<alpha\><rsub|r>|\<bar\>>|\<bar\>>>

      <item><math|\<ldots\><above|\<Longrightarrow\>|<around|(|9,13|)>>D<rsub|i,s<rsub|type>><rsup|t>\<wedge\>A<rsub|T><rsup|j><rprime|'>\<wedge\><rsub|s\<neq\>s<rsub|type>>C<rsub|i><rsup|s>\<wedge\>C<rsub|i,s><rsup|t><around|[|<wide|\<alpha\><rsub|r<rsub|i>>|\<bar\>>\<assign\><wide|r<rsub|i>|\<bar\>>|]>\<wedge\>A<rsub|c,j,s><rsup|i><around|[|<wide|<wide|\<alpha\><rsub|r>|\<bar\>>|\<bar\>>\<assign\><wide|<wide|r|\<bar\>>|\<bar\>>|]>\<wedge\><wide|<wide|r|\<bar\>>|\<bar\>><wide|=|\<dot\>><wide|<wide|\<alpha\><rsub|r>|\<bar\>>|\<bar\>>>

      <item><math|\<ldots\><above|\<Longrightarrow\>|<around|(|17-18|)>>C<rsub|i,s<rsub|type>><rsup|t>\<wedge\><rsub|s\<neq\>s<rsub|type>>C<rsub|i><rsup|s>\<wedge\>C<rsub|i,s><rsup|t><around|[|<wide|\<alpha\><rsub|r<rsub|i>>|\<bar\>>\<assign\><wide|r<rsub|i>|\<bar\>>|]>\<wedge\><wide|<wide|r|\<bar\>>|\<bar\>><wide|=|\<dot\>><wide|<wide|\<alpha\><rsub|r>|\<bar\>>|\<bar\>><above|\<Longrightarrow\>|<around|(|13|)>>C<rsub|i>>.

      <item>(19)-(21) and interpolation give the goal (1).

      <item>From type preservation and free generation properties (as in
      Proposition <reference|SolvedForm>), by (6) we get
      <math|\<cal-M\>\<vDash\>\<cal-Q\>.A<rsub|T><rsup|j><around*|[|<wide|\<alpha\>|\<bar\>><rsub|j><rsup|T><around*|(|<wide|\<beta\>|\<bar\>>\<cap\>X<rsub|s<rsub|type>>|)>\<assign\><wide|t|\<bar\>><rsub|j><rsup|T>;<around*|(|<wide|\<beta\>|\<bar\>>\\X<rsub|s<rsub|type>>|)>\<assign\><wide|t|\<bar\>><rsub|j><rsup|b>;<wide|<wide|\<alpha\><rsub|r>|\<bar\>>|\<bar\>>\<assign\><wide|t|\<bar\>><rsub|j><rsup|r>|]>>
      for some <math|<wide|t|\<bar\>><rsub|j><rsup|T>>, for all
      <math|<wide|t|\<bar\>><rsub|j><rsup|r>,<wide|t|\<bar\>><rsub|j><rsup|b>>.

      <item>Since <math|\<cal-L\><rsub|s>> are single-sorted for
      <math|s\<neq\>s<rsub|type>>, by (15), (23) and (10) we get the goal
      (2).

      <item>Similarly, from (3), (7), type preservation and free generation
      properties, and because <math|\<cal-L\><rsub|s>> are single-sorted for
      <math|s\<neq\>s<rsub|type>>, we get the goal (3).

      <item>Consider <math|c\<in\>A<rsub|ans>> such that
      <math|\<cal-M\>\<nvDash\>\<cal-Q\>.c> and
      <math|FV<around*|(|c|)>\<cap\><wide|\<beta\>|\<bar\>>\<neq\>\<varnothing\>>,
      and a <math|\<beta\><rsub|1>\<in\>FV<around*|(|c|)>> such that
      <math|<around*|(|\<forall\>\<beta\><rsub|1>|)>\<in\>\<cal-Q\>>.

      <item>If <math|\<beta\><rsub|1>\<in\><wide|\<beta\>|\<bar\>>>, then
      <math|\<beta\><rsub|2>=\<beta\><rsub|1>> satisfies the goal (4).
      Consider the cases where <math|\<beta\><rsub|1>\<nin\><wide|\<beta\>|\<bar\>>>.

      <item>Consider <math|\<beta\><rsub|1>\<in\>X<rsub|s<rsub|type>>>. By
      (26) <math|\<cal-M\>\<nvDash\>\<cal-Q\>.c>.

      <item>By (6) -- or (24) -- <math|\<cal-M\>\<vDash\>\<cal-Q\>.c<around*|[|<wide|\<alpha\>|\<bar\>><rsub|j><rsup|T><wide|\<beta\>|\<bar\>>\<assign\><wide|t|\<bar\>><rsub|j><rsup|T>|]>>
      for some <math|<wide|t|\<bar\>><rsub|j><rsup|T>>.

      <item>By (15), <math|c> is in solved form
      <math|\<beta\><rsub|3><wide|=|\<dot\>>t>.

      <item>By (28)-(30), <math|\<beta\><rsub|3>\<in\><wide|\<beta\>|\<bar\>>>.
      By (8) we have the goal (4) for case
      <math|\<beta\><rsub|1>\<in\>X<rsub|s<rsub|type>>>.

      <item>Consider <math|\<beta\><rsub|1>\<in\>X<rsub|s>> for
      <math|s\<neq\>s<rsub|type>>. Because <math|\<cal-L\><rsub|s>> are
      single-sorted for <math|s\<neq\>s<rsub|type>>, by (15) we have
      <math|c\<in\>A<rsub|s><rsup|k<rsub|j><rsup|s>>>.

      <item>From (12) we have the goal (4).
    </enumerate>

    Now we sketch a proof of completeness, i.e. that no JCAQP answer ``falls
    through''.

    <\enumerate>
      <item>We need to show that for any JCAQP
      <math|\<cal-Q\>.\<wedge\><rsub|i><around*|(|D<rsub|i>\<Rightarrow\>C<rsub|i>|)>>
      with parameters <math|<wide|\<beta\>|\<bar\>>> answer
      <math|\<exists\><wide|\<alpha\>|\<bar\>>.A>, there is an
      <math|\<exists\><wide|\<alpha\><rsub|ans>|\<bar\>>.A<rsub|ans>\<in\>Abd<around*|(|\<cal-Q\>,<wide|\<beta\>|\<bar\>>,<wide|D<rsub|i>,C<rsub|i>|\<bar\>>|)>>
      and <math|<wide|t|\<bar\>>> such that
      <math|A\<Rightarrow\>A<rsub|ans><around|[|<wide|\<alpha\><rsub|ans>|\<bar\>>\<assign\><wide|t|\<bar\>>|]>>.

      <item>Let <math|A\<equiv\>\<wedge\><rsub|s>A<rsub|s>> where
      <math|A<rsub|s>> has atoms of sort <math|s> only. Let
      <math|A<rprime|'>> be a formula obtained from
      <math|A<rsub|s<rsub|type>>> by substituting all alien subterms
      <math|<wide|r|\<bar\>><rprime|'>> of sorts other than
      <math|s<rsub|type>> by fresh variables
      <math|<wide|\<alpha\><rsub|r>|\<bar\>><rprime|'>>. Let
      <math|\<wedge\><rsub|s>A<rprime|'><rsub|s>=\<b-U\><around|(|A<rprime|'>|)>>
      be solved form of <math|A<rprime|'>> with
      <math|A<rprime|'><rsub|s>\<in\>\<cal-L\><rsub|s>>.

      <item>W.l.o.g., all <math|C<rsub|i>,D<rsub|i>> are satisfiable.
      Observe, that <math|\<vDash\>D<rsub|i>\<wedge\>A\<Rightarrow\>C<rsub|i>>
      implies, by lemma <reference|SolvedFormProj>, that there is a
      conjunction of equations over variables
      <math|<wide|\<alpha\><rsub|r<rsub|i>>|\<bar\>><wide|\<alpha\><rsub|r>|\<bar\>><rprime|'>>:
      <math|A<rprime|''><rsub|i>\<assign\>\<wedge\><rsub|s\<neq\>s<rsub|type>>A<rsub|i,s><rprime|''>>,
      such that:

      <\enumerate>
        <item> <math|D<rsub|i>\<wedge\>A\<wedge\><wide|\<alpha\><rsub|r<rsub|i>>|\<bar\>><wide|\<alpha\><rsub|r>|\<bar\>><rprime|'><wide|=|\<dot\>><wide|r<rsub|i>|\<bar\>><wide|r|\<bar\>><rprime|'>\<Rightarrow\>A<rprime|''><rsub|i>>,

        <item><math|D<rsup|t><rsub|i,s<rsub|type>>\<wedge\>A<rprime|'><rsub|s<rsub|type>>\<wedge\>A<rprime|''><rsub|i>\<Rightarrow\>C<rsup|t><rsub|i,s<rsub|type>>>,

        <item><math|D<rsub|i><rsup|s>\<wedge\>D<rsup|t><rsub|i,s><around|[|<wide|\<alpha\><rsub|r<rsub|i>>|\<bar\>>\<assign\><wide|r<rsub|i>|\<bar\>>|]>\<wedge\>A<rsub|s>\<wedge\>A<rprime|'><rsub|s><around|[|<wide|\<alpha\><rsub|r>|\<bar\>><rprime|'>\<assign\><wide|r|\<bar\>><rprime|'>|]>\<Rightarrow\>C<rsub|i><rsup|s>\<wedge\>C<rsup|t><rsub|i,s><around|[|<wide|\<alpha\><rsub|r<rsub|i>>|\<bar\>>\<assign\><wide|r<rsub|i>|\<bar\>>|]>>
        for <math|s\<neq\>s<rsub|type>>.
      </enumerate>

      <item>(3b) and the assumption about <math|Abd<rsub|T>> give that for
      some <math|<around*|(|\<exists\><wide|\<alpha\><rsub|j><rsup|T>|\<bar\>>.A<rsub|T><rsup|j>|)>\<in\>Abd<rsub|T><around*|(|\<cal-Q\>,<wide|\<beta\>|\<bar\>>,<wide|D<rsub|i,s<rsub|type>><rsup|t>,C<rsub|i,s<rsub|type>><rsup|t>|\<bar\>>|)>>,
      <math|A<rprime|'><rsub|s<rsub|type>>\<wedge\>A<rprime|''><rsub|i>\<Rightarrow\>A<rsub|T><rsup|j><around*|[|<wide|\<alpha\><rsub|j><rsup|T>|\<bar\>>\<assign\><wide|t<rsub|T>|\<bar\>>|]>>
      for some <math|<wide|t<rsub|T>|\<bar\>>>.

      <item>(3a), (3c) and lemma <reference|SolvedFormProj> imply, by
      substituting free variables, <math|D<rsub|i><rsup|s>\<wedge\>D<rsup|t><rsub|i,s><around|[|<wide|\<alpha\><rsub|r<rsub|i>>|\<bar\>>\<assign\><wide|r<rsub|i>|\<bar\>>|]>\<wedge\>A<rsub|s>\<wedge\>A<rprime|'><rsub|s><around|[|<wide|\<alpha\><rsub|r>|\<bar\>><rprime|'>\<assign\><wide|r|\<bar\>><rprime|'>|]>\<Rightarrow\>C<rsub|i><rsup|s>\<wedge\>C<rsup|t><rsub|i,s><around|[|<wide|\<alpha\><rsub|r<rsub|i>>|\<bar\>>\<assign\><wide|r<rsub|i>|\<bar\>>|]>\<wedge\>A<rprime|''><rsub|i,s><around|[|<wide|<wide|\<alpha\><rsub|r>|\<bar\>>|\<bar\>><wide|\<alpha\><rsub|r>|\<bar\>><rprime|'>\<assign\><wide|<wide|r|\<bar\>>|\<bar\>><wide|r|\<bar\>><rprime|'>|]>>.

      <item>To use the assumption about <math|Abd<rsub|s>>, we weaken (5).
      With a stronger premise, we also get a stronger conclusion:
      <math|D<rsub|i><rsup|s>\<wedge\><around*|(|D<rsup|t><rsub|i,s>\<wedge\>A<rsup|i><rsub|p,j,s>\<wedge\>A<rsup|i><rsub|c,j,s>|)><around|[|<wide|<wide|\<alpha\><rsub|r>|\<bar\>>|\<bar\>>\<assign\><wide|<wide|r|\<bar\>>|\<bar\>>|]>\<wedge\>A<rsub|s>\<wedge\>A<rprime|'><rsub|s><around|[|<wide|\<alpha\><rsub|r>|\<bar\>><rprime|'>\<assign\><wide|r|\<bar\>><rprime|'>|]>\<Rightarrow\>C<rsub|i><rsup|s>\<wedge\><around*|(|C<rsup|t><rsub|i,s>\<wedge\>A<rsup|i><rsub|c,j,s>|)><around|[|<wide|\<alpha\><rsub|r<rsub|i>>|\<bar\>>\<assign\><wide|r<rsub|i>|\<bar\>>|]>\<wedge\>A<rprime|''><rsub|i,s><around|[|<wide|<wide|\<alpha\><rsub|r>|\<bar\>>|\<bar\>><wide|\<alpha\><rsub|r>|\<bar\>><rprime|'>\<assign\><wide|<wide|r|\<bar\>>|\<bar\>><wide|r|\<bar\>><rprime|'>|]>>.

      <item>(6) gives by the assumption about <math|Abd<rsub|s>>:
      <math|<around*|(|A<rsup|i><rsub|c,j,s>\\A<rsup|i><rsub|p,j,s>|)><around|[|<wide|<wide|\<alpha\><rsub|r>|\<bar\>>|\<bar\>>\<assign\><wide|<wide|r|\<bar\>>|\<bar\>>|]>\<wedge\>A<rsub|s>\<wedge\>A<rprime|'><rsub|s><around|[|<wide|\<alpha\><rsub|r>|\<bar\>><rprime|'>\<assign\><wide|r|\<bar\>><rprime|'>|]>\<Rightarrow\>A<rsub|s><rsup|k<rsub|j><rsup|s>><around*|[|<wide|\<alpha\><rsub|s><rsup|k<rsub|j><rsup|s>>|\<bar\>>\<assign\><wide|t<rsub|s><rsup|k<rsub|j><rsup|s>>|\<bar\>>|]>>
      for some <math|k<rsub|j><rsup|s>> and
      <math|<wide|t<rsub|s><rsup|k<rsub|j><rsup|s>>|\<bar\>>>.

      <item>Check using (3b) and (4) that
      <math|A<rprime|'><rsub|s<rsub|type>>\<wedge\>A<rprime|''><rsub|i>\<wedge\><wide|\<alpha\><rsub|r<rsub|i>>|\<bar\>><wide|\<alpha\><rsub|r>|\<bar\>><rprime|'><wide|=|\<dot\>><wide|r<rsub|i>|\<bar\>><wide|r|\<bar\>><rprime|'>\<Rightarrow\>\<exists\><wide|\<alpha\>|\<bar\>><rsub|r><rsup|j>.A<rsub|T><rsup|j><rprime|'><around*|[|<wide|\<alpha\><rsub|j><rsup|T>|\<bar\>>\<assign\><wide|t<rsub|T>|\<bar\>>|]>\<wedge\><around*|(|A<rsup|i><rsub|c,j,s>\\A<rsup|i><rsub|p,j,s>|)><around|[|<wide|<wide|\<alpha\><rsub|r>|\<bar\>>|\<bar\>>\<assign\><wide|<wide|r|\<bar\>>|\<bar\>>|]>>.
      The subtraction in <math|<around*|(|A<rsup|i><rsub|c,j,s>\\A<rsup|i><rsub|p,j,s>|)>>
      allows us to drop <math|D<rsup|t><rsub|i,s<rsub|type>>> from the
      premise in (3b).

      <item>Select <math|\<exists\><wide|\<alpha\><rsub|ans>|\<bar\>>.A<rsub|ans>\<assign\>\<exists\><wide|\<alpha\><rsub|<wide|k<rsub|j><rsup|s>|\<bar\>>>|\<bar\>>.A<rsub|T><rsup|j><rprime|'><around|[|<wide|<wide|\<alpha\><rsub|r>|\<bar\>>|\<bar\>>\<assign\><wide|<wide|r|\<bar\>>|\<bar\>>|]>\<wedge\><rsub|s>A<rsub|s><rsup|k<rsub|j><rsup|s>>>
      for <math|<wide|\<alpha\><rsub|<wide|k<rsub|j><rsup|s>|\<bar\>>>|\<bar\>>\<assign\><wide|\<alpha\><rsub|j><rsup|T>|\<bar\>><wide|\<alpha\>|\<bar\>><rsub|r><rsup|j><wide|<wide|\<alpha\><rsub|s><rsup|k<rsub|j><rsup|s>>|\<bar\>>|\<bar\>>\<cap\>FV<around*|(|A<rsub|T><rsup|j><around|[|<wide|\<alpha\><rsub|r>|\<bar\>>\<assign\><wide|r|\<bar\>>|]>\<wedge\><rsub|s>A<rsub|s><rsup|k<rsub|j><rsup|s>>|)>>.
      By (7) and (8), we have <math|A\<wedge\><around|[|<wide|<wide|\<alpha\><rsub|r>|\<bar\>>|\<bar\>><wide|\<alpha\><rsub|r>|\<bar\>><rprime|'><wide|=|\<dot\>><wide|<wide|r|\<bar\>>|\<bar\>><wide|r|\<bar\>><rprime|'>|]>\<Rightarrow\>A<rsub|ans><around*|[|<wide|\<alpha\><rsub|j><rsup|T>|\<bar\>><wide|\<alpha\>|\<bar\>><rsub|r><rsup|j><wide|<wide|\<alpha\><rsub|s><rsup|k<rsub|j><rsup|s>>|\<bar\>>|\<bar\>>\<assign\><wide|t<rsub|T>|\<bar\>><wide|t|\<bar\>><rsub|r><rsup|j><wide|<wide|t<rsub|s><rsup|k<rsub|j><rsup|s>>|\<bar\>>|\<bar\>>|]>>
      for some <math|<wide|t|\<bar\>><rsub|r><rsup|j>>, which implies (1).
    </enumerate>
  </proof>

  <section|Constraint Generalization><label|LUBProofs>

  <\proposition>
    <label|SepProp>Let <math|D<rsub|s>\<in\>\<cal-L\><rsub|s>> for all sorts
    <math|s> such that <math|D<rsub|s<rsub|type>>=\<b-U\><around*|(|D<rsub|s<rsub|type>>|)>>,
    and <math|C<rsub|s<rprime|'>>\<in\>\<cal-L\><rsub|s<rprime|'>>> for
    <math|s<rprime|'>\<neq\>s<rsub|type>>. Then
    <math|\<cal-M\>\<vDash\><around*|(|\<wedge\><rsub|s>D<rsub|s>|)>\<Rightarrow\>C<rsub|s<rprime|'>>>
    if and only if <math|\<cal-M\>\<vDash\>D<rsub|s<rprime|'>>\<Rightarrow\>C<rsub|s<rprime|'>>>.
  </proposition>

  <\proposition>
    <em|(MGU property.)> MGU: <math|T<around*|(|F,X|)>\<vDash\>C\<Leftrightarrow\>\<b-U\><around*|(|C|)>>.
  </proposition>

  <\proposition>
    <label|ImplSubst>Let <math|D> be a conjunction of equations with
    <math|D=\<b-U\><around*|(|D|)>>, let <math|A> be a conjunction of
    equations and <math|<wide|\<alpha\>|\<bar\>>> variables such that
    <math|FV<around*|(|A|)>\<subset\><wide|\<alpha\>|\<bar\>>\<cup\>FV<around*|(|D|)>>.
    <math|T<around*|(|F,X|)>\<vDash\>D\<Rightarrow\>\<exists\><wide|\<alpha\>|\<bar\>>.A>
    if and only if there exists a substitution
    <math|S=<around*|[|<wide|\<alpha\>|\<bar\>>\<assign\><wide|g<rsub|\<alpha\>>|\<bar\>>|]>>
    and a solved form <math|A<rprime|'>\<Leftrightarrow\>A> with
    <math|A<rprime|'>=\<b-U\><around*|(|A<rprime|'>|)>> such that for every
    <math|x<wide|=|\<dot\>>t\<in\>A<rprime|'>>, either
    <math|S<around*|(|x|)>=S<around*|(|t|)>>, or
    <math|x<wide|=|\<dot\>>S<around*|(|t|)>\<in\>D>.
  </proposition>

  Proof of Theorem <reference|CorComplLUBThm>.

  <\proof>
    First, we show <math|\<cal-M\>\<vDash\>\<wedge\><rsub|i><around|(|D<rsub|i>\<Rightarrow\>\<exists\><wide|\<alpha\>|\<bar\>>.A|)>>.

    <\enumerate>
      <item><math|\<cal-M\>\<vDash\>D<rsub|i>\<wedge\>D<rsub|i><rsup|a>\<wedge\>D<rsub|i><rsup|u>\<Rightarrow\>c>,
      for each conjunct <math|c\<in\>A<rsub|s<rsub|type>>>.

      <\enumerate>
        <item>Case <math|c=x<rsub|j><wide|=|\<dot\>>g<rsub|j>>. By properties
        of MGU.

        <item>Case <math|c\<in\>D<rsub|i><rsup|g>> follows from
        <math|D<rsub|i>\<wedge\>D<rsub|i><rsup|a>\<Rightarrow\>D<rsub|i,s<rsub|type>><rsup|t>>.

        <item>Case <math|c\<in\>D<rsub|i><rsup|v>>. The premises are:
        <math|x<wide|=|\<dot\>>t<rsub|1>\<in\>D<rsub|i><rsup|g>,y<wide|=|\<dot\>>t<rsub|2>\<in\>D<rsub|i><rsup|g>,\<cal-M\>\<vDash\>D<rsub|i><rsup|g>\<Rightarrow\>t<rsub|1><wide|=|\<dot\>>t<rsub|2>>.
        The goal follows from <math|D<rsub|i>\<wedge\>D<rsub|i><rsup|a>\<wedge\>D<rsub|i><rsup|u>\<Rightarrow\>D<rsub|i><rsup|g>>,
        by transitivity.\ 
      </enumerate>

      <item>By properties of <math|LUB<rsub|s>>, we have
      <math|\<vDash\>D<rsub|i><rsup|s>\<wedge\>D<rsub|i><rsup|t,s>\<wedge\>D<rsub|i,s>\<Rightarrow\>\<exists\><wide|\<alpha\>|\<bar\>><rsub|s>.A<rsub|s>>
      for <math|s\<neq\>s<rsub|type>>, and therefore
      <math|\<vDash\>D<rsub|i>\<wedge\>D<rsub|i><rsup|a>\<wedge\>D<rsub|i><rsup|u>\<Rightarrow\>\<exists\><wide|\<alpha\>|\<bar\>><rsub|s>.A<rsub|s>>.

      <item>We have <math|\<vDash\>D<rsub|i>\<Rightarrow\>\<exists\><wide|\<alpha\><rsup|j><rsub|i>|\<bar\>>.D<rsub|i>\<wedge\>D<rsub|i><rsup|a>>,
      and by properties of most specific anti-unification,
      <math|\<vDash\>D<rsub|i>\<Rightarrow\>\<exists\><wide|<wide|\<alpha\>|\<bar\>><rsub|j>|\<bar\>>.D<rsub|i>\<wedge\>D<rsub|i><rsup|u>>.

      <item>Collecting the above points, we get
      <math|\<vDash\>D<rsub|i>\<Rightarrow\>\<exists\><wide|\<alpha\><rsup|j><rsub|i>|\<bar\>><wide|<wide|\<alpha\>|\<bar\>><rsub|s>|\<bar\>>.\<wedge\><rsub|s>A<rsub|s>>.
    </enumerate>

    Now, we sketch a proof of: For every <math|\<exists\><wide|\<alpha\>|\<bar\>><rsub|r>.A<rsub|r>>
    such that <math|\<cal-M\>\<vDash\>\<wedge\><rsub|i><around|(|D<rsub|i>\<Rightarrow\>\<exists\><wide|\<alpha\>|\<bar\>><rsub|r>.A<rsub|r>|)>>,
    with variables renamed so that <math|<wide|\<alpha\>|\<bar\>>#FV<around*|(|A<rsub|r>|)>>,
    <math|\<cal-M\>\<vDash\>A\<Rightarrow\>\<exists\><wide|\<alpha\>|\<bar\>><rsub|r>.A<rsub|r>>.

    <\enumerate>
      <item>The assumption is <math|\<cal-M\>\<vDash\>\<wedge\><rsub|i><around|(|D<rsub|i>\<Rightarrow\>\<exists\><wide|\<alpha\>|\<bar\>><rsub|r>.A<rsub|r>|)>>.

      <item>By definition, <math|\<cal-M\>\<vDash\>D<rsub|i>\<wedge\>D<rsub|i><rsup|a>\<Leftrightarrow\>\<wedge\><rsub|s\<neq\>s<rsub|type>>D<rsub|i><rsup|s>\<wedge\><rsub|s>D<rsub|i><rsup|t,s>\<wedge\><rsub|s>D<rsup|t><rsub|i,s>>.

      <item>Let <math|\<exists\><wide|\<alpha\>|\<bar\>><rsub|r>.A<rsub|r>\<Leftrightarrow\>\<exists\><wide|<wide|\<alpha\>|\<bar\>><rsub|t,s><rsup|r>|\<bar\>>.\<wedge\><rsub|s>\<exists\><wide|\<alpha\>|\<bar\>><rsub|r,s>.D<rsub|r,s><rsup|a>\<wedge\>A<rsub|r,s>>
      where <math|\<exists\><wide|\<alpha\>|\<bar\>><rsub|r,s>.A<rsub|r,s>\<in\>\<cal-L\><rsub|s>>,
      <math|<wide|a|\<bar\>><rsub|t,s><rsup|r>> are all alien subterms of
      sort <math|s> in <math|A<rsub|r>>, <math|<wide|\<alpha\>|\<bar\>><rsub|t,s><rsup|r>>
      are fresh variables <math|<wide|\<alpha\>|\<bar\>><rsub|t,s><rsup|r>#FV<around*|(|A<rsub|r>,<wide|D<rsub|i>|\<bar\>>|)>>
      and also all alien subterms in <math|A<rsub|r,s<rsub|type>>>,
      <math|A<rsub|r,s<rsub|type>>=\<b-U\><around*|(|A<rsub|r,s<rsub|type>>|)>>,
      and <math|D<rsub|r,s><rsup|a>=<wide|\<alpha\>|\<bar\>><rsub|t,s><rsup|r><wide|=|\<dot\>><wide|a|\<bar\>><rsub|t,s><rsup|r>>
      for <math|s\<neq\>s<rsub|type>>, <math|D<rsub|r,s<rsub|type>><rsup|a>=\<b-T\>>.

      <item>By Proposition <reference|ImplSubst>, for each branch <math|i>
      there is a substitution <math|\<eta\><rsub|i>> of
      <math|<wide|<wide|\<alpha\>|\<bar\>><rsub|t,s><rsup|r>|\<bar\>><wide|\<alpha\>|\<bar\>><rsub|r,s<rsub|type>>>
      that is an anti-unifier of <math|<wide|t<rsub|i,j><rprime|'>|\<bar\>>>,
      for all <math|x<rsub|j>\<nin\><wide|<wide|\<alpha\>|\<bar\>><rsub|t,s><rsup|r>|\<bar\>><wide|\<alpha\>|\<bar\>><rsub|r,s<rsub|type>>>
      such that <math|x<rsub|j><wide|=|\<dot\>>u<rsub|r,j>\<in\>A<rsub|r,s<rsub|type>>>,
      where <math|x<rsub|j>,<wide|t<rsub|i,j>|\<bar\>>\<in\>V> and
      <math|\<cal-M\>\<vDash\>D<rsub|i>\<Rightarrow\>t<rprime|'><rsub|i,j><wide|=|\<dot\>>t<rsub|i,j>>.
      <math|t<rprime|'><rsub|i,j>> can be made equal to <math|t<rsub|i,j>> up
      to a variable-variable substitution.

      <\itemize>
        <item>I.e. a substitution <math|<around*|[|<wide|\<alpha\>|\<bar\>>\<assign\><wide|\<beta\>|\<bar\>>|]>>
        that can assign the same <math|\<beta\>> to several <math|\<alpha\>>.
      </itemize>

      <item>There exists a substitution <math|\<rho\>> which establishes
      <math|\<cal-M\>\<vDash\>A<rsub|s<rsub|type>>\<Rightarrow\>\<exists\><wide|<wide|\<alpha\>|\<bar\>><rsub|t,s><rsup|r>|\<bar\>>.\<exists\><wide|\<alpha\>|\<bar\>><rsub|r,s<rsub|type>>.<wide|x<rsub|j><wide|=|\<dot\>>u<rsub|r,j>|\<bar\>>>:
      by variable-variable substitution, including alien subterm variables,
      according to <math|\<cal-M\>\<vDash\>D<rsub|i>\<Rightarrow\>t<rprime|'><rsub|i,j><wide|=|\<dot\>>t<rsub|i,j>>,
      and by the factoring via most specific anti-unification.

      <item>Let <math|\<exists\><wide|\<alpha\>|\<bar\>><rsub|s>.A<rsub|s>=LUB<rsub|s><around*|(|<wide|D<rsub|i><rsup|s>\<wedge\><wide|D<rsup|a><rsub|i>|~><around*|(|D<rsup|t><rsub|i,s>\<wedge\>D<rsup|u><rsub|i,s>|)>|\<bar\>>|)>>
      as in the definition of <math|LUB<around*|(|\<cdot\>|)>>.

      <item><math|\<cal-M\>\<vDash\>D<rsub|i>\<Rightarrow\>\<exists\><wide|\<alpha\>|\<bar\>><rsub|r>.A<rsub|r>>
      by (1), <math|\<cal-M\>\<vDash\>D<rsub|i>\<wedge\>D<rsub|i><rsup|a>\<wedge\>D<rsup|u><rsub|i,s>\<Rightarrow\>\<exists\><wide|\<alpha\>|\<bar\>><rsub|r>.A<rsub|r>>
      by weakening on the left, <math|\<cal-M\>\<vDash\>D<rsub|i>\<wedge\>D<rsub|i><rsup|a>\<wedge\>D<rsup|u><rsub|i,s>\<Rightarrow\>\<exists\><wide|<wide|\<alpha\>|\<bar\>><rsub|t,s><rsup|r>|\<bar\>>.\<wedge\><rsub|s>\<exists\><wide|\<alpha\>|\<bar\>><rsub|r,s>.D<rsub|r,s><rsup|a>\<wedge\>A<rsub|r,s>>
      by (3), <math|\<cal-M\>\<vDash\>D<rsub|i>\<wedge\>D<rsub|i><rsup|a>\<wedge\>D<rsup|u><rsub|i,s>\<Rightarrow\>\<exists\><wide|\<alpha\>|\<bar\>><rsub|r,s>.A<rsub|r,s>>
      by weakening on the right, <math|\<cal-M\>\<vDash\>D<rsub|i><rsup|s>\<wedge\>D<rsub|i><rsup|t,s>\<wedge\>D<rsup|t><rsub|i,s>\<wedge\>D<rsup|u><rsub|i,s>\<Rightarrow\>\<exists\><wide|\<alpha\>|\<bar\>><rsub|r,s>.A<rsub|r,s>>
      by (2) and Proposition <reference|SepProp>.

      <item>By (6), (7), interpolation and assumption about
      <math|LUB<rsub|s>>, <math|\<cal-M\>\<vDash\>A<rsub|s>\<Rightarrow\>\<exists\><wide|\<alpha\>|\<bar\>><rsub|r,s>.A<rsub|r,s>>
      for every <math|s\<neq\>s<rsub|type>>.

      <item>More specifically, we need <math|\<cal-M\>\<vDash\>A<rsub|s>\<wedge\>A<rsub|s<rsub|type>>\<Rightarrow\>\<exists\><wide|\<alpha\>|\<bar\>><rsub|r,s>.A<rsub|r,s>\<wedge\>\<rho\><around*|(|<wide|\<alpha\><rsup|r><rsub|t,s>|\<bar\>>|)><wide|=|\<dot\>><wide|a<rsup|r><rsub|t,s>|\<bar\>>>.
      It can be shown by extending the argument for (8) using the fact that
      <math|D<rsup|u><rsub|i,s>> relates <math|\<rho\><around*|(|<wide|\<alpha\><rsup|r><rsub|t,s>|\<bar\>>|)>>
      introduced in (5) to the remaining constraints of branch <math|i>.
    </enumerate>
  </proof>

  <section|Solving for Predicate Variables><label|PredVarProofs>

  In this section, we provide proof sketches for correctness and a limited
  form of completeness of the type inference implemented in <name|InvarGenT>,
  correctness with respect to the type system
  <math|MMG<rsub|\<exists\>><around*|(|X|)>> and the limited form of
  completeness wrt. <math|MMG<around*|(|X|)>>.

  <\lemma>
    <label|SplitProps>Let <math|<around*|(|\<cal-Q\><rprime|'>,<wide|\<alpha\>|\<bar\>><rsub|res>,A<rsub|res>,<wide|\<exists\><wide|\<alpha\>|\<bar\>><rsup|\<chi\>>.A<rsub|\<chi\>>|\<bar\>>|)>\<in\>Split<around*|(|\<cal-Q\>,<wide|\<alpha\>|\<bar\>>,A,<wide|<wide|\<beta\>|\<bar\>><rsup|\<chi\>>|\<bar\>>|)>>.
    Then:

    <\enumerate>
      <item><math|\<cal-M\>\<vDash\>A<rsub|res>\<wedge\><rsub|\<chi\>>A<rsub|\<chi\>>\<Rightarrow\>A>.

      <item><math|\<cal-M\>\<vDash\>A\<Rightarrow\>\<exists\><wide|<wide|\<alpha\>|\<bar\>><rsup|\<chi\>><rsub|+>|\<bar\>>.A<rsub|res>\<wedge\><rsub|\<chi\>>A<rsub|\<chi\>>>.

      <item><math|\<cal-M\>\<vDash\>\<cal-Q\><rprime|'>.A<rsub|res><around*|[|<wide|\<alpha\>|\<bar\>><rsub|res>\<assign\><wide|t|\<bar\>>|]><with|mode|text|
      \ for some ><wide|t|\<bar\>>>.

      <item>If <math|A> only restricts <math|<wide|\<beta\>|\<bar\>><rsup|\<chi\>>>
      in ways that are expressible as <math|\<cal-Q\><rsub|\<less\>\<beta\><rsub|\<chi\>>>\<exists\><wide|\<beta\>|\<bar\>><rsup|\<chi\>><wide|\<beta\>|\<bar\>><rsup|\<chi\>><rsub|1>.\<varphi\>>
      for some <math|<wide|\<beta\>|\<bar\>><rsup|\<chi\>><rsub|1>>, and
      <with|mode|math|\<cal-M\>\<vDash\>\<cal-Q\>.A<around*|[|<wide|\<alpha\>|\<bar\>><wide|<wide|\<beta\>|\<bar\>><rsup|\<chi\>>|\<bar\>>\<assign\><wide|t|\<bar\>>|]>>
      for some <math|<wide|t|\<bar\>>>, then
      <with|mode|math|Split<around*|(|\<cal-Q\>,<wide|\<alpha\>|\<bar\>>,A,<wide|<wide|\<beta\>|\<bar\>><rsup|\<chi\>>|\<bar\>>|)>\<neq\>\<varnothing\>>.

      <item><math|Split> preserves atomized form: if
      <math|\<exists\><wide|\<alpha\>|\<bar\>>.A> is in atomized form with
      respect to <math|\<cal-Q\>> and parameters
      <math|<wide|<wide|\<beta\>|\<bar\>><rsup|\<chi\>>|\<bar\>>>, then
      <math|\<exists\><wide|\<alpha\>|\<bar\>><rsub|res>.A<rsub|res>> is in
      atomized form with respect to <math|\<cal-Q\><rprime|'>> and parameters
      <math|<wide|<wide|\<alpha\>|\<bar\>><rsup|\<chi\>><wide|\<beta\>|\<bar\>><rsup|\<chi\>>|\<bar\>>>.
    </enumerate>
  </lemma>

  <\proof>
    Recall the definition of <math|Split> and the notation used there.

    (1) and (2) follow from the observation that
    <math|A<rsub|\<chi\>><rsup|L>\<wedge\>A<rsup|R><rsub|\<chi\>>\<Rightarrow\>A<rsub|\<chi\>><rsup|+>>
    and <math|A<rsub|\<chi\>><rsup|+>\<Rightarrow\>\<exists\><wide|<wide|\<alpha\>|\<bar\>><rsup|\<chi\>><rsub|+>|\<bar\>>.A<rsub|\<chi\>><rsup|L>\<wedge\>A<rsup|R><rsub|\<chi\>>>.

    (3) follows from <math|\<cal-M\>\<vDash\>\<cal-Q\>.<around*|(|A\<setminus\>\<cup\><rsub|\<chi\>>A<rsub|\<chi\>><rsup|+>|)><around*|[|<wide|\<alpha\>|\<bar\>><rsub|res>\<assign\><wide|t|\<bar\>>|]>>
    for some <math|<wide|t|\<bar\>>> because
    <math|\<cup\><rsub|\<chi\>><wide|\<alpha\>|\<bar\>><rsup|\<chi\>>=\<varnothing\>>
    and <math|A<rsub|res>=A\<setminus\>\<cup\><rsub|\<chi\>>A<rsub|\<chi\>>>,
    in the last iteration.

    For (4) to hold the algorithm should at each recursion level be able to
    find <math|<wide|A<rsub|\<chi\>><rsup|+>|\<bar\>>> for which
    <math|\<cal-M\>\<vDash\>\<cal-Q\>.<around*|(|A\<setminus\><no-break>\<cup\><rsub|\<chi\>>A<rsub|\<chi\>><rsup|+>|)><around*|[|<wide|\<alpha\>|\<bar\>>\<assign\><wide|t|\<bar\>>|]><with|mode|text|
    for some ><wide|t|\<bar\>>> and <math|Strat<around*|(|A<rsup|+><rsub|\<chi\>>,<wide|\<beta\>|\<bar\>><rsup|\<chi\>>|)>>
    does not return <math|\<bot\>> for any <math|\<chi\>>, where
    <math|\<cal-Q\>> and <math|<wide|\<beta\>|\<bar\>><rsup|\<chi\>>> are
    either the initial arguments or the recursive call arguments. The
    algorithm terminates because <math|<wide|\<alpha\>|\<bar\>>> always
    decreases in the recursive call.

    <math|A<rsub|\<chi\>><rsup|+>> contains restrictions on the variables
    <math|<wide|\<beta\>|\<bar\>><rsup|\<chi\>>>. If
    <math|Strat<around*|(|A<rsup|+><rsub|\<chi\>>,<wide|\<beta\>|\<bar\>><rsup|\<chi\>>|)>>
    returns <math|\<bot\>>, then, because <math|A<rsub|\<chi\>><rsup|+>> is
    in atomized form, <math|A<rsub|\<chi\>><rsup|+>> restricts
    <math|<wide|\<beta\>|\<bar\>><rsup|\<chi\>>> in a way not expressible as
    <math|\<cal-Q\><rsub|\<less\>\<beta\><rsub|\<chi\>>>\<exists\><wide|\<beta\>|\<bar\>><rsup|\<chi\>><wide|\<beta\>|\<bar\>><rsup|\<chi\>><rsub|1>.\<varphi\>>.

    The final remark follows from the minimality of
    <math|<wide|A<rsub|\<chi\>><rsup|+>|\<bar\>>> w.r.t. inclusion.
  </proof>

  <\lemma>
    <label|OpCorrectLemma>Let <math|\<Phi\>\<in\>\<cal-L\>>,
    <math|S=<wide|\<exists\><wide|\<alpha\>|\<bar\>><rsup|\<chi\>>.F<rsub|\<chi\>>|\<bar\>>>
    and <math|R=<wide|\<exists\><wide|\<alpha\>|\<bar\>><rsup|\<chi\><rsub|K>>.F<rsub|\<chi\><rsub|K>>|\<bar\>>>.
    Let <math|NF<around*|(|R*S<around*|(|\<Phi\>|)>|)>=\<cal-Q\>.\<wedge\><rsub|i><around*|(|D<rsub|i>\<Rightarrow\>C<rsub|i>|)>=\<cal-Q\>.\<Phi\><rsub|PN>\<in\>\<cal-L\><rsup|>>.

    Let <math|<around|(|\<exists\><wide|\<alpha\>|\<bar\>><rsub|res><rprime|'>.F<rsub|res><rprime|'>,S<rprime|'>,R<rprime|'>|)>\<in\>\<Psi\><around|(|k,\<Phi\>,S,R|)>>
    for any <math|k>. Let

    <\equation*>
      \<cal-Q\><rprime|'>.\<Phi\><rsub|PN><rprime|'>=NF<around*|(|R<rprime|'><rsup|->*S<rprime|'><rsup|->*R<rsup|+>*S<rsup|+><around*|(|\<Phi\>|)>|)>
    </equation*>

    Then <math|\<cal-M\>\<vDash\>F<rsub|res><rprime|'>\<Rightarrow\>\<Phi\><rsub|PN><rsup|<rprime|'>>>
    and <math|\<cal-M\>\<vDash\>\<cal-Q\><rprime|'>.F<rprime|'><rsub|res><around*|[|<wide|\<alpha\>|\<bar\>><rsub|res>\<assign\><wide|t|\<bar\>>|]>>
    for some <math|<wide|t|\<bar\>>>.
  </lemma>

  <\proof>
    We use the notation from the definition of <math|\<Psi\>>, with
    <math|S<rsub|k>=S,R<rsub|k>=R,\<cal-Q\><rprime|'>=\<cal-Q\><rsup|k+1>>.
    We have

    <\equation*>
      \<exists\><wide|\<alpha\>|\<bar\>>.A<rsub|0>\<in\>Abd<around*|(|\<cal-Q\><rsup|k><rprime|'>,<wide|\<beta\><rsub|\<chi\>><wide|\<beta\><rsup|>|\<bar\>><rsup|\<chi\>>|\<bar\>>,<wide|D<rsub|i><rsup|k><rprime|'>,C<rsub|i><rsup|k><rprime|'>|\<bar\>>|)>
    </equation*>

    and therefore <em|(1)> <math|\<cal-M\>\<vDash\>\<wedge\><rsub|i><around|(|D<rsub|i><rsup|k><rprime|'>\<wedge\>A<rsub|0>\<Rightarrow\>C<rsub|i><rsup|k><rprime|'>|)>>.
    Continuing the definition of <math|\<Psi\>>, we have

    <\equation*>
      <around*|(|\<cal-Q\><rsup|k+1>,<wide|\<alpha\>|\<bar\>><rsub|res>,A<rsub|res>,<wide|\<exists\><wide|\<alpha\>|\<bar\>><rsup|\<beta\><rsub|\<chi\>>>.A<rsub|\<beta\><rsub|\<chi\>>>|\<bar\>>|)>\<in\>Split<around*|(|\<cal-Q\><rsup|k><rprime|'>,<wide|\<alpha\>|\<bar\>>,A,<wide|\<beta\><rsub|\<chi\>><wide|\<beta\><rsup|>|\<bar\>><rsup|\<chi\>>|\<bar\>>|)>
    </equation*>

    and <math|S<rprime|'><around*|(|\<chi\>|)>=\<exists\><wide|\<beta\>|\<bar\>><rsup|\<chi\>,k>.Simpl<around*|(|\<exists\><wide|<wide|\<alpha\>|\<bar\>><rsup|\<beta\><rsub|\<chi\>>>|\<bar\>>.F<rsub|\<chi\>><rprime|'>\<wedge\>A<rsub|\<beta\><rsub|\<chi\>>><around*|[|<wide|\<beta\><rsub|\<chi\>><wide|\<beta\><rsup|>|\<bar\>><rsup|\<chi\>>|\<bar\>>\<assign\><wide|\<delta\><wide|\<beta\><rsup|>|\<bar\>><rsup|\<chi\>,k>|\<bar\>>|]>|)>>,
    <math|F<rsub|res><rprime|'>=A<rsub|res>>. Therefore by Lemma
    <reference|SplitProps> point 1, <em|(2)>
    <math|\<cal-M\>\<vDash\>F<rsub|res><rprime|'>\<wedge\><rsub|\<beta\><rsub|\<chi\>>>A<rsub|\<beta\><rsub|\<chi\>>>\<Rightarrow\><no-break>A>,
    and by Lemma <reference|SplitProps> point 3, the goal
    <math|\<cal-M\>\<vDash\>\<cal-Q\><rprime|'>.F<rsub|res><rprime|'><around*|[|<wide|\<alpha\>|\<bar\>><rsub|res>\<assign\><wide|t|\<bar\>>|]><with|mode|text|
    \ for some ><wide|t|\<bar\>>>.

    It remains to show <em|(3)> <math|\<cal-M\>\<vDash\>F<rsub|res><rprime|'>\<Rightarrow\><no-break>\<Phi\><rsub|PN><rsup|<rprime|'>>>.
    Observe that <em|(4)> <math|\<Phi\><rprime|'><rsub|PN>\<equiv\><around*|(|\<wedge\><rsub|\<beta\><rsub|\<chi\>>>A<rsub|\<beta\><rsub|\<chi\>>>\<Rightarrow\>\<Phi\><rsub|PN>\<wedge\><rsub|\<chi\><rsub|K>>U<rsub|\<chi\><rsub|K>>|)>>.
    (1) is <math|\<cal-M\>\<vDash\>A<rsub|0>\<Rightarrow\>\<Phi\><rsub|PN>\<wedge\><rsub|\<chi\><rsub|K>>U<rsub|\<chi\><rsub|K>>>.
    But <math|F<rprime|'><rsub|res>\<wedge\><rsub|\<chi\>>A<rsub|\<beta\><rsub|\<chi\>>>\<Rightarrow\>A<rsub|0>>
    by (2), so (1) and (4) give (3).
  </proof>

  Sketch of proof of Theorem <reference|ThCorrect>.

  <\proof>
    Lemma <reference|OpCorrectLemma> gives the goal
    <math|\<cal-M\>,\<cal-I\>\<vDash\>\<Phi\>> with
    \ <with|mode|math|\<cal-I\><around*|(|\<Phi\>|)>\<equiv\>\<cal-Q\><rprime|'>.\<Phi\><rsub|PN><rprime|'>>,
    because <with|mode|math|S<rprime|'>*R<rprime|'>=S*R> implies
    <math|\<wedge\><rsub|\<beta\><rsub|\<chi\>>>A<rsub|\<beta\><rsub|\<chi\>>>=\<b-T\>>.
  </proof>

  <\axiom>
    (Interpolation property for <math|\<cal-M\>>.) We assume that for
    conjunctions of atoms <math|A> and any quantifier-free formula
    <math|\<Phi\>>, <math|\<cal-M\>\<vDash\>A\<Rightarrow\>\<Phi\>> implies
    that there is a conjunction of atoms <math|B> with
    <math|FV<around*|(|B|)>\<subset\>FV<around*|(|A|)>\<cap\>FV<around*|(|\<Phi\>|)>>,
    <math|\<cal-M\>\<vDash\>A\<Rightarrow\>B> and
    <math|\<cal-M\>\<vDash\>B\<Rightarrow\>\<Phi\>>.
  </axiom>

  <\lemma>
    <label|OpComplLemma>Let <math|NF<around*|(|\<Phi\><around*|[|<wide|\<chi\><around|(|\<tau\>|)>|\<bar\>>\<assign\><wide|\<exists\><wide|\<alpha\>|\<bar\>><rsup|\<chi\>>.F<rsub|\<chi\>><around|[|\<delta\>\<assign\>\<tau\>|]>|\<bar\>>|]>|)>=\<cal-Q\>.\<Phi\><rsub|N><rsup|>>
    and <math|PV<around*|(|\<Phi\>|)>=PV<rsup|1><around*|(|\<Phi\>|)>>. Let

    <\equation*>
      \<cal-Q\><rsup|\<Delta\>>.\<Phi\><rsub|N><rsup|\<Delta\>>=NF<around*|(|\<Phi\><around*|[|<wide|\<chi\><rsup|-><around|(|\<beta\><rsup|\<chi\>>|)>|\<bar\>>\<assign\><wide|\<exists\><wide|\<alpha\>|\<bar\>><rsup|\<chi\>><wide|\<alpha\>|\<bar\>><rsup|\<chi\>><rsub|\<Delta\>>.<around|(|\<Delta\><rsub|\<chi\>>\<wedge\>F<rsub|\<chi\>>|)><around|[|\<delta\>\<assign\>\<beta\><rsup|\<chi\>>|]>|\<bar\>>;<wide|\<chi\><rsup|+><around|(|\<tau\>|)>|\<bar\>>\<assign\><wide|\<exists\><wide|\<alpha\>|\<bar\>><rsup|\<chi\>>.F<rsub|\<chi\>><around|[|\<delta\>\<assign\>\<tau\>|]>|\<bar\>>|]>|)>
    </equation*>

    for variables <math|<wide|<wide|\<alpha\>|\<bar\>><rsup|\<chi\>><rsub|\<Delta\>>|\<bar\>>>
    and conjunctions of atoms <math|<wide|\<Delta\><rsub|\<chi\>>|\<bar\>>\<in\>\<cal-L\>>
    such that the JCAQP<math|<rsub|\<cal-M\>>> problem
    <with|mode|math|\<cal-Q\><rsup|\<Delta\>>.\<Phi\><rsub|N><rsup|\<Delta\>>>
    has a solution. Assume that <math|Abd> in the definition of
    <math|\<Psi\>> is a complete abduction algorithm returning an atomized
    form formula. Then there is <math|<around|(|F<rsub|res><rprime|'>,<no-break><wide|\<exists\><wide|\<alpha\>|\<bar\>><rsup|\<chi\>><rprime|'>.F<rsub|\<chi\>><rprime|'>|\<bar\>>|)>\<in\>\<Psi\><around|(|k,\<Phi\>,<wide|\<exists\><wide|\<alpha\>|\<bar\>><rsup|\<chi\>>.F<rsub|\<chi\>>|\<bar\>>|)>>
    such that

    <\equation*>
      \<cal-M\>\<vDash\>\<wedge\><rsub|\<chi\>>\<Delta\><rsub|\<chi\>><rsup|\<beta\>>\<Rightarrow\><around|(|\<wedge\><rsub|\<chi\>><around*|(|F<rprime|'><rsub|\<chi\>>\<setminus\>F<rsub|\<chi\>>|)>|)><around*|[|<wide|<wide|\<alpha\>|\<bar\>><rsup|\<chi\>><rprime|'>|\<bar\>>\<assign\><wide|t|\<bar\>>|]>
    </equation*>

    for all <math|\<chi\>>, for some <math|<wide|t|\<bar\>>>.
  </lemma>

  <\proof>
    Let <math|\<exists\><wide|\<alpha\>|\<bar\>><rsup|d><rsub|res>.D<rsub|res>>
    be a solution to the JCAQP<math|<rsub|\<cal-M\>>> problem
    <with|mode|math|\<cal-Q\><rsup|\<Delta\>>.\<Phi\><rsub|N><rsup|\<Delta\>>>.
    We have <math|\<cal-M\>\<vDash\>D<rsub|res>\<wedge\><rsub|\<chi\>>\<Delta\><rsub|\<chi\>><rsup|\<beta\>>\<Rightarrow\>\<Phi\><rsub|N>>.
    By the completeness assumption about <math|Abd>, we have
    <math|\<cal-M\>\<vDash\>D<rsub|res>\<wedge\><rsub|\<chi\>>\<Delta\><rsub|\<chi\>><rsup|\<beta\>>\<Rightarrow\>A<around*|[|<wide|\<alpha\>|\<bar\>><wide|<wide|\<alpha\>|\<bar\>><rsup|\<chi\>>|\<bar\>>\<assign\><wide|t|\<bar\>>|]>>
    for some <math|<wide|t|\<bar\>>>. Since <math|D<rsub|res>> does not
    participate in restricting <math|<wide|<wide|\<beta\>|\<bar\>><rsup|\<chi\>>|\<bar\>>>
    and <math|\<Delta\><rsub|\<chi\>><rsup|\<beta\>>> is limited to
    <math|\<cal-Q\><rsub|\<less\>\<beta\><rsub|\<chi\>>><wide|\<alpha\>|\<bar\>><rsup|\<chi\>><wide|\<alpha\>|\<bar\>><rsup|\<chi\>><rsub|\<Delta\>>>
    variables, by atomized form of <math|\<exists\><wide|\<alpha\>|\<bar\>>.A>
    and interpolation, we get the expressiveness constraint needed for Lemma
    <reference|SplitProps> point 4, therefore
    <with|mode|math|Split<around*|(|\<cal-Q\>,<wide|\<alpha\>|\<bar\>>,A,<wide|<wide|\<beta\>|\<bar\>><rsup|\<chi\>>|\<bar\>>|)>\<neq\>\<varnothing\>>.
    Thus by Lemma <reference|SplitProps> point 2,
    <with|mode|math|\<cal-M\>\<vDash\>D<rsub|res>\<wedge\><rsub|\<chi\>>\<Delta\><rsub|\<chi\>><rsup|\<beta\>>\<wedge\><wide|<wide|\<alpha\>|\<bar\>><rsup|\<chi\>><rprime|'>|\<bar\>><wide|=|\<dot\>><wide|t|\<bar\>>\<Rightarrow\>\<exists\><wide|<wide|\<alpha\>|\<bar\>><rsup|\<chi\>><rsub|+>|\<bar\>>.A<rsub|res>\<wedge\><rsub|\<chi\>>A<rsub|\<chi\>>>
    where by definition of <math|\<Psi\>>,
    <math|A<rsub|\<chi\>>=F<rprime|'><rsub|\<chi\>>\<setminus\>F<rsub|\<chi\>>>.
    Since the atomized form is preserved by <math|Split> (Lemma
    <reference|SplitProps> point 5), we have the goal.
  </proof>

  Sketch of proof of Theorem <reference|InferCompleteness>.

  <\proof>
    The thesis <math|\<cal-M\>\<vDash\>\<wedge\><rsub|\<chi\>>F<rsup|s><rsub|\<chi\>>\<Rightarrow\><around*|(|\<wedge\><rsub|\<chi\>>F<rsup|k><rsub|\<chi\>>|)><around*|[|<wide|<wide|\<alpha\>|\<bar\>><rsup|\<chi\>,k>|\<bar\>>\<assign\><wide|t|\<bar\>><rsup|k>|]>>
    is true for <math|k=0>. Assume it holds for arbitrary <math|k>. We need
    to show <math|\<cal-M\>\<vDash\>\<wedge\><rsub|\<chi\>>F<rsup|s><rsub|\<chi\>><around*|[|\<delta\>\<assign\>\<beta\><rsub|\<chi\>>|]>\<Rightarrow\><around*|(|\<wedge\><rsub|\<chi\>>F<rsup|k+1><rsub|\<chi\>><around*|[|\<delta\>\<assign\>\<beta\><rsub|\<chi\>>|]>|)><around*|[|<wide|<wide|\<alpha\>|\<bar\>><rsup|\<chi\>,k+1>|\<bar\>>\<assign\><wide|t|\<bar\>><rsup|k+1>|]>>
    for some <with|mode|math|<around*|(|F<rsub|res><rsup|k+1>,<wide|\<exists\><wide|\<alpha\>|\<bar\>><rsup|\<chi\>,k+1>.F<rsub|\<chi\>><rsup|k+1>|\<bar\>>|)>>
    and a substitution of variables <math|<wide|<wide|\<alpha\>|\<bar\>><rsup|\<chi\>,k+1>|\<bar\>>>.

    By the assumption that <math|<wide|\<chi\>|\<bar\>>=PV<around*|(|\<Phi\>|)>=PV<rsup|1><around*|(|\<Phi\>|)>>,
    definition of <math|\<Psi\>> gives <math|F<rsub|\<chi\>><rsup|k+1>=F<rsub|\<chi\>><rsup|k>\<wedge\>A<rsub|\<chi\>>>.
    We will apply Lemma <reference|OpComplLemma> with
    <math|\<Delta\><rsub|\<chi\>>=F<rsub|\<chi\>><rsup|s>> and
    <math|F<rsub|\<chi\>>=F<rsup|k><rsub|\<chi\>>>. By the inductive
    assumption, JCAQP<math|<rsub|\<cal-M\>>> answer
    <math|\<exists\><wide|\<alpha\>|\<bar\>><rsup|res><rsub|s>.F<rsub|res><rsup|s>>
    to <math|NF<around*|(|\<Phi\><around*|[|<wide|\<chi\><around|(|\<tau\>|)>|\<bar\>>\<assign\><wide|\<exists\><wide|\<alpha\>|\<bar\>><rsup|\<chi\>><rsub|s>.F<rsub|\<chi\>><rsup|s><around|[|\<delta\>\<assign\>\<tau\>|]>|\<bar\>>|]>|)>>
    is also an answer to <math|\<cal-Q\><rsup|\<Delta\>>.\<Phi\><rsub|N><rsup|\<Delta\>>>.
    By Lemma <reference|OpComplLemma>, we get the goal.
  </proof>

  <appendix|Algorithmic Details>

  <section|Generating and Normalizing Formulas><label|NormConstrn>

  We inject the existential type and value constructors during parsing for
  user-provided existential types, and during constraint generation for
  inferred existential types, into the list of toplevel items. It facilitates
  exporting inference results as OCaml source code.

  Toplevel definitions are intended as boundaries for constraint solving.
  This way the programmer can decompose functions that could be too complex
  for the solver. A toplevel <verbatim|let rec> only binds a single
  identifier, while <verbatim|let> binds variables in a pattern. To preserve
  the flexibility of expression-level pattern matching, for <verbatim|let> --
  unless it just binds a value as discussed above -- we pack the constraints
  <math|<around*|\<llbracket\>|\<Sigma\>\<vdash\>p\<uparrow\>\<alpha\>|\<rrbracket\>>>
  which the pattern makes available, into existential types. Each pattern
  variable is a separate entry to the global environment, therefore the
  connection between them is lost.

  The <verbatim|let><math|\<ldots\>><verbatim|in> syntax has two uses:
  binding values of existential types means ``eliminating the
  quantification'' -- the programmer has control over the scope of the
  existential constraint. The second use is if the value is not of
  existential type, the constraint is replaced by one that would be generated
  for a pattern matching branch. This recovers the common use of the
  <verbatim|let>...<verbatim|in> syntax, with exception of polymorphic
  <verbatim|let> cases, where <verbatim|let rec> needs to be used.

  \ We optimize the disjunctive constraint coming from <verbatim|let>
  bindings as follows. Rather than inspecting <math|K> in <math|\<Sigma\>>
  directly, let <math|<around*|\<llbracket\>|\<Sigma\>\<vdash\>K
  x\<uparrow\>\<alpha\><rsub|0>|\<rrbracket\>>=\<exists\><wide|\<beta\>|\<bar\>><around*|[|D|]><around*|{|x\<mapsto\>\<tau\><rprime|'>|}>>.
  <math|<around*|\<llbracket\>|\<Gamma\>\<vdash\>K
  p.e<rsub|2>:<no-break>\<alpha\><rsub|0>\<rightarrow\><no-break>\<tau\>|\<rrbracket\>>>
  is equivalent to, or at least implied by:

  <\equation*>
    <around*|\<llbracket\>|\<Sigma\>\<vdash\>K
    p\<downarrow\>\<alpha\><rsub|0>|\<rrbracket\>>\<wedge\>\<forall\><wide|\<beta\>|\<bar\>>.D\<Rightarrow\><around*|\<llbracket\>|\<Gamma\>\<vdash\>p.e<rsub|2>:\<tau\><rprime|'>\<rightarrow\>\<tau\>|\<rrbracket\>>
  </equation*>

  Let us set <math|\<b-C\><rsub|0>=<neg|E><around*|(|\<alpha\><rsub|0>|)>>,
  <math|\<b-C\><rsub|K>=<around*|\<llbracket\>|\<Sigma\>\<vdash\>K
  p\<downarrow\>\<alpha\><rsub|0>|\<rrbracket\>>>,
  <math|\<b-D\><rsub|0>=\<beta\><rsub|0><wide|=|\<dot\>>\<alpha\><rsub|0>>
  and <math|\<b-D\><rsub|K>=\<beta\><rsub|0><wide|=|\<dot\>>\<tau\><rprime|'>\<wedge\>D>.
  Then,

  <\equation*>
    \<exists\>\<alpha\><rsub|0>.<around*|\<llbracket\>|\<Gamma\>\<vdash\>e<rsub|1>:\<alpha\><rsub|0>|\<rrbracket\>>\<wedge\><around*|(|<around*|\<llbracket\>|\<Gamma\>\<vdash\>p.e<rsub|2>:\<alpha\><rsub|0>\<rightarrow\>\<tau\>|\<rrbracket\>>\<wedge\><neg|E><around*|(|\<alpha\><rsub|0>|)>\<vee\><rsub|\<cal-E\>><around*|\<llbracket\>|\<Gamma\>\<vdash\>K
    p.e<rsub|2>:\<alpha\><rsub|0>\<rightarrow\>\<tau\>|\<rrbracket\>>|)>
  </equation*>

  is equivalent to:

  <\equation*>
    \<exists\>\<alpha\><rsub|0>.<around*|\<llbracket\>|\<Gamma\>\<vdash\>e<rsub|1>:\<alpha\><rsub|0>|\<rrbracket\>>\<wedge\>\<vee\><rsub|i\<in\><around*|{|0|}>\<cup\>\<cal-E\>><around*|(|\<b-C\><rsub|i>\<wedge\>\<forall\><wide|\<beta\>|\<bar\>>\<beta\><rsub|0>.<around*|(|\<b-D\><rsub|i>\<Rightarrow\><around*|\<llbracket\>|\<Gamma\>\<vdash\>p.e<rsub|2>:\<beta\><rsub|0>\<rightarrow\>\<tau\>|\<rrbracket\>>|)>|)>
  </equation*>

  We use the same variable <math|\<beta\><rsub|0>> across disjuncts of the
  same disjunction, so that <math|<around*|\<llbracket\>|\<Gamma\>\<vdash\>p.e<rsub|2>:\<beta\><rsub|0>\<rightarrow\>\<tau\>|\<rrbracket\>>>
  can be derived and simplified only once.

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
  constructor is used. For a toplevel <verbatim|let>, we form existential
  types after solving the generated constraint, to have less intermediate
  variables in them.

  Both during parsing and during inference, we inject new structure items to
  the program, which capture the existential types. During printing
  existential types in concrete syntax <math|\<exists\>i:<wide|\<beta\>|\<bar\>><around*|[|\<varphi\>|]>.t>
  for an occurrence <math|\<varepsilon\><rsub|K><around*|(|<around*|(|<wide|r|\<bar\>>|)>|)>>,
  the variables <math|<wide|\<alpha\>|\<bar\>>> coming from
  <math|\<delta\><rprime|'><wide|=|\<dot\>><around*|(|<wide|\<alpha\>|\<bar\>>|)>\<in\>\<varphi\>>
  are substituted-out by <math|<around*|[|<wide|\<alpha\>|\<bar\>>\<assign\><wide|r|\<bar\>>|]>>.

  For simplicity, only toplevel definitions accept type and invariant
  annotations from the user. The constraints are modified according to the
  <math|<around*|\<llbracket\>|\<Gamma\>,\<Sigma\>\<vdash\>ce:\<forall\><wide|\<alpha\>|\<bar\>><around|[|D|]>.\<tau\>|\<rrbracket\>>>
  rule. Where <verbatim|let rec><math|\<ldots\>><verbatim|in> uses a fresh
  variable <math|\<beta\>>, a toplevel <verbatim|let rec> incorporates the
  type from the annotation. The annotation is considered partial, <math|D>
  becomes part of the constraint generated for the recursive function but
  more constraints will be added if needed. The polymorphism of
  <math|\<forall\><wide|\<alpha\>|\<bar\>>> variables from the annotation is
  preserved since they are universally quantified in the generated
  constraint.

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
  clauses are: <verbatim|assert type e1 = e2> which translates as equality of
  types of <verbatim|e1> and <verbatim|e2>, <verbatim|assert false> which
  translates as <verbatim|CFalse>, and <verbatim|assert num e1 \<less\>= e2>,
  which translates as inequality <math|n<rsub|1>\<leqslant\>n<rsub|2>>
  assuming that <verbatim|e1> has type <verbatim|Num n1> and <verbatim|e2>
  has type <verbatim|Num n2>.

  We treat a chain of single branch functions with only <verbatim|assert
  false> in the body of the last function specially. We put all information
  about the type of the functions in the premise of the generated constraint.
  Therefore the user can use them to exclude unintended types. See the
  example <verbatim|equal_assert.gadt>.

  <subsection|Normalization>

  We reduce the constraint to alternation-minimizing prenex-normal form, as
  in the formalization. We return a variable comparison function. The
  branches we return from normalization have unified conclusions, since we
  need to unify for solving disjunctions anyway.

  Releasing constraints \ from under disjunctions is done iteratively,
  somewhat similar to how disjunction would be treated in constraint solvers.
  Releasing the sub-constraints is essential for eliminating cases of further
  disjunction constraints. When at the end more than one disjunct remains, we
  assume it is the traditional <name|LetIn> rule and select its disjunct.

  When one <math|\<lambda\><around*|[|K|]>> expression is a branch of another
  <math|\<lambda\><around*|[|K|]>> expression, the corresponding branch does
  not introduce a disjunction constraint -- the case is settled syntactically
  to be the same existential type.

  <subsubsection|Implementation Details>

  The unsolved constraints are particularly weak with regard to variables
  constrained by predicate variables. We need to propagate which existential
  type to select for result type of recursive functions, if any.
  Normalization starts by flattening constraints into implications with
  conjunctions of atoms as premises and conclusions, and disjunctions with
  disjuncts and additional information. The additional information kept with
  a disjunct is the conjunction of atoms that hold together with the
  disjunction. We try to eliminate disjuncts by using unification to check
  for contradiction. If only one disjunct is left, or we decide to pick
  <name|LetIn> anyway (when no progress can be made otherwise), we return the
  disjunct. Otherwise we return the filtered disjunction.

  To help eliminate unintended disjuncts, we collect information about
  existential return types of recursive definitions by:

  <\enumerate>
    <item>solving the conclusion of a branch together with additional
    conclusions, to know the return types of variables,

    <item>registering existential return types for all variables in the
    substitution,

    <item>registering existential return types for all <math|RetType> first
    arguments and their substitution instances,

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
  might need refining. We merge implications with the same premise, unless
  one of them is non-recursive and the other is recursive. We call an
  implication branch recursive when an unary predicate variable
  <math|\<chi\>> (not a <math|\<chi\><rsub|K>>) appears in the conclusion
  <em|or> a binary predicate variable <math|\<chi\><rsub|K>> appears in the
  premise.

  <section|Abduction>

  Our formal specification of abduction provides a scheme for combining sorts
  that substitutes number sort subterms from type sort terms with variables,
  so that a single-sort term abduction algorithm can be called. Since we
  implement term abduction over the multisorted datatype <verbatim|typ>, we
  keep these <em|alien subterms> in terms passed to term abduction.

  <subsection|Abduction for Terms with Alien Subterms><label|JCAAlienAlg>

  Here we expand on the overview from Section <reference|JCAAlienMain>. The
  JCAQPAS problem is more complex than simply substituting alien subterms
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
  process after abduction for terms ends. This process is needed regardless
  of the ``dissociation'' issue, to uncover the full content of numeric sort
  constraints.

  To face efficiency of numerical abduction with many variables, we modify
  the approach. On the first iteration of the main algorithm, we remove
  (purge) alien subterms both from the branches and from the answer, but we
  do not perform other-sort abduction at all. On the next iteration, we do
  not purge alien subterms, neither from the branches nor from the answer, as
  we expect the dissociation in the partial solutions (to predicate
  variables) from the first step to be sufficient. Other-sort abduction
  algorithms now have less work, because only a fraction of alien subterm
  variables <math|\<alpha\><rsub|s>> remain in the partial solutions (see
  main algorithm in section <reference|MainAlgo>). They also have more
  information to work with, present in the instatiation of partial solutions.
  However, this optimization violates completeness guarantees of the
  combination of sorts algorithm. To faciliate finding term abduction
  solutions that hold under the quantifiers, we substitute-out other sort
  variables, by variables more to the left in the quantifier, using equations
  from the premise.

  The dissociation interacts with the discard list mechanism. Since
  dissociation introduces fresh variables, no answers with alien subterms
  would be syntactically identical. When checking whether a partial answer
  should be discarded, in case alien subterm dissociation is <em|on>, we
  ignore alien sort subterms in the comparison.

  <subsection|Joint Constraint Abduction><label|JCAAlg>

  Here we expand on the overview from Section <reference|JCAMain>. We further
  lose generality by using a heuristic search scheme instead of testing all
  combinations of simple abduction answers. In particular, our search scheme
  returns from joint abduction for types with a single answer, which
  eliminates deeper interaction between the sort of types and other sorts.
  Some amount of interaction is provided by the validation procedure, which
  checks for consistency of the partial answer, the premise and the
  conclusion of each branch, including consistency for other sorts.

  We accumulate simple abduction answers into the partial abduction answer,
  we set aside branches that do not have any answer satisfiable with the
  partial answer so far. After all branches have been tried and the partial
  answer is not an empty conjunction (i.e. not <math|\<top\>>), we retry the
  set-aside branches. If during the retry, any of the set-aside branches
  fails, we add the partial answer to discarded answers -- which are avoided
  during simple abduction -- and restart. Restart puts the set-aside branches
  to be tried first. If, when left with set-aside branches only, the partial
  answer is an empty conjunction, i.e. all the answer-contributing branches
  have been set aside, we fail -- return <math|\<bot\>> from the joint
  abduction. This does not peform complete backtracking (no completeness
  guarantee), but is therefore quicker to report unsolvable cases and does
  sufficient backtracking. After an answer working for all branches has been
  found, we perform additional check, which encapsulates negative constraints
  introduced by the <verbatim|assert false> construct. If the check fails, we
  add the answer to discarded answers and repeat the search.

  If a partial answer becomes as strong as one of the discarded answers
  inside SCA, simple constraint abduction skips to find a different answer.
  The discarded answers are initialized with a discard list passed from the
  main algorithm.

  To check validity of answers, we use a modified variant of unification
  under quantifiers: unification with parameters, where the parameters do not
  interact with the quantifiers and thus can be freely used and eliminated.
  Note that to compute conjunction of the candidate answer with a premise,
  unification does not check for validity under quantifiers.

  Because it would be difficult to track other sort constraints while
  updating the partial answer, we discard numeric sort constraints in simple
  abduction algorithm, and recover them after the final answer for terms
  (i.e. for the type sort) is found.

  Searching for an abduction answer can fail in only one way: we have set
  aside all the branches that could contribute to the answer. It is difficult
  to pin-point the culprit. We remember which branch caused the restart when
  the number of set-aside branches was the smallest. The conclusion of that
  branch can be used to construct the error report.

  <subsection|Simple Constraint Abduction for Terms><label|SCATermsAlg>

  Here we expand on the overview from Section <reference|SCATermsMain>. Our
  initial implementation of simple constraint abduction for terms follows
  <cite|AbductionSolvMaher> p. 13. The mentioned algorithm only gives
  <em|fully maximal answers> which is loss of generality w.r.t. our
  requirements. To solve <math|D\<Rightarrow\>C> the algorithm starts with
  <math|\<b-U\><around*|(|D\<wedge\>C|)>> and iteratively replaces subterms
  by fresh variables <math|\<alpha\>\<in\><wide|\<alpha\>|\<bar\>>> for a
  final solution <math|\<exists\><wide|\<alpha\>|\<bar\>>.A>. As our primary
  approach to mitigate some of the limitations of fully maximal answers, we
  start from <math|\<b-U\><rsub|><around*|(|<wide|A|~><around*|(|D\<wedge\>C|)>|)>>,
  where <math|\<exists\><wide|\<alpha\>|\<bar\>>.A> is the solution to
  previous problems solved by the joint abduction algorithm, and
  <math|<wide|A|~><around*|(|\<cdummy\>|)>> is the corresponding
  substitution. Moreover, motivated by examples from Chuan-kai Lin
  <cite|PracticalGADTsInfer>, we intruduce variable-variable equations
  <math|\<beta\><rsub|1><wide|=|\<dot\>>\<beta\><rsub|2>>, for
  <math|\<beta\><rsub|1>\<beta\><rsub|2>\<subset\><wide|\<beta\>|\<bar\>>>,
  not implied by <math|<wide|A|~><around*|(|D\<wedge\>C|)>>, as additional
  candidate answer atoms. During abduction
  <math|Abd<around*|(|\<cal-Q\>,<wide|\<beta\>|\<bar\>>,<wide|D<rsub|i>,C<rsub|i>|\<bar\>>|)>>,
  we ensure that the (partial as well as final) answer
  <math|\<exists\><wide|\<alpha\>|\<bar\>>.A> satisfies
  <math|\<vDash\>\<cal-Q\>.A<around*|[|<wide|\<alpha\>|\<bar\>><wide|\<beta\>|\<bar\>>\<assign\><wide|t|\<bar\>>|]>>
  for some <math|<wide|t|\<bar\>>>. We achieve this by normalizing the answer
  using parameterized unification under quantifiers
  <math|\<b-U\><rsub|<wide|\<alpha\>|\<bar\>><wide|\<beta\>|\<bar\>>><around*|(|\<cal-Q\>.A|)>>.
  <math|<wide|\<beta\>|\<bar\>>> are the parameters of the invariants.

  In fact, when performing unification, we check more than
  <math|\<b-U\><rsub|<wide|\<alpha\>|\<bar\>><wide|\<beta\>|\<bar\>>><around*|(|\<cal-Q\>.A|)>>
  requires. We also ensure that the use of parameters will not cause problems
  in the <math|Split> phase of the main algorithm. To this effect, we forbid
  substitution of a variable <math|\<beta\><rsub|1>> from
  <math|<wide|\<beta\>|\<bar\>>> with a term containing a universally
  quantified variable that is not in <math|<wide|\<beta\>|\<bar\>>> and to
  the right of <math|\<beta\><rsub|1>> in <math|\<cal-Q\>>. Also, we forbid
  substitution of a variable <math|\<beta\><rsub|1>> from
  <math|<wide|\<beta\>|\<bar\>><rsup|\<chi\>>> with a term containing a
  variable <math|\<beta\><rsub|2>\<in\><wide|\<beta\>|\<bar\>><rsup|\<chi\><rprime|'>>>
  for <math|\<chi\>\<neq\>\<chi\><rprime|'>>.

  In implementing <cite|AbductionSolvMaher> p. 13, we follow a top-down
  approach where bigger subterms are abstracted first -- replaced by a fresh
  variable, \ together with an arbitrary selection of other occurrences of
  the subterm. If dropping the candidate atom maintains
  <math|T<around*|(|F|)>\<vDash\>A\<wedge\>D\<Rightarrow\>C>, we proceed to
  neighboring subterm or next equation. Otherwise, we try all of: replacing
  the subterm by the fresh variable; proceeding to subterms of the subterm;
  preserving the subterm; replacing the subterm by variables corresponding to
  earlier occurrences of the subterm. This results in a single, branching
  pass over all subterms considered. Finally, we clean-up the solution by
  eliminating fresh variables when possible (i.e. substituting-out equations
  <math|x<wide|=|\<dot\>>\<alpha\>> for variable <math|x> and fresh variable
  <math|\<alpha\>>).

  Although there could be an infinite number of abduction answers, there is
  always a finite number of <em|fully maximal> answers, or more generally, a
  finite number of equivalence classes of formulas strictly stronger than a
  given conjunction of equations in the domain <math|T<around*|(|F|)>>. We
  use a search scheme that tests as soon as possible. The simple abduction
  algorithm takes a partial solution -- a conjunction of candidate solutions
  for some other branches -- and checks if the solution being generated is
  satisfiable together with the candidate partial solution. The algorithm
  also takes several indicators to let it select the expected answer:

  <\itemize>
    <item>a number that determines how many correct solutions to skip;

    <item>a validation procedure that checks whether the partial answer meets
    a condition, in joint abduction the condition is consistency with premise
    and conclusion of each branch;

    <item>the parameters and candidates for parameters of the invariants,
    <math|<wide|\<beta\>|\<bar\>>>, updated as we add new atoms to the
    partial answer; existential variables that are not to the left of
    parameters and are connected to parameters become parameters; we process
    atoms containing parameters first;

    <item>the quantifier <math|\<cal-Q\>> (source <verbatim|q>) so that the
    partial answer <math|\<exists\><wide|\<alpha\>|\<bar\>>.A> (source
    <verbatim|vs,ans>) can be checked for validity with parameters:
    <math|\<vDash\>\<cal-Q\>.A<around*|[|<wide|\<alpha\>|\<bar\>>\<assign\><wide|t|\<bar\>>|]>>
    for some <math|<wide|t|\<bar\>>>;

    <item>a discard list of partial answers to avoid (a tabu list) --
    implements backtracking, with answers from abductions raising
    ``fallback'' going there.
  </itemize>

  Since an atom can be mistakenly discarded when some variable could be
  considered an invariant parameter but is not at the time, we process atoms
  incident with candidates for invariant parameters first. A variable becomes
  a candidate for a parameter if there is a parameter that depends on it.
  That is, we process atoms <math|x<wide|=|\<dot\>>t> such that
  <math|x\<in\><wide|\<beta\>|\<bar\>>> first, and if equation
  <math|x<wide|=|\<dot\>>t> is added to the partial solution, we add to
  <math|<wide|\<beta\>|\<bar\>>> existential variables in <math|t>. Note that
  <math|x<wide|=|\<dot\>>t> can stand for either <math|x\<assign\>t>, or
  <math|y\<assign\>x> for <math|t=y>. For a universally quantified variable
  <math|x\<nin\><wide|\<beta\>|\<bar\>>>, <math|x\<assign\>t> will not be
  part of the answer as it does not hold under the quantifier.

  To simplify the search in presence of a quantifier prefix, we preprocess
  the initial candidate by eliminating universally quantified variables:

  <\eqnarray*>
    <tformat|<table|<row|<cell|S>|<cell|=>|<cell|<around*|[|<wide|t<rsub|u>|\<bar\>>\<assign\><wide|t<rprime|'><rsub|u>|\<bar\>>|]><with|mode|text|
    for >FV<around*|(|t<rsub|u>|)>\<cap\><wide|\<beta\><rsub|u>|\<bar\>>\<neq\>\<varnothing\>,<wide|\<forall\>\<beta\><rsub|u>|\<bar\>>\<subset\>\<cal-Q\><with|mode|text|
    such that >\<cal-M\>\<vDash\>D\<Rightarrow\><wide|S|\<dot\>>,>>|<row|<cell|S<rprime|'>>|<cell|=>|<cell|<around*|[|<wide|u|\<bar\>>\<assign\><wide|t<rprime|'><rsub|u>|\<bar\>>|]><with|mode|text|
    for ><wide|u|\<bar\>>\<subset\><wide|\<beta\><rsub|u>|\<bar\>>,<wide|\<forall\>\<beta\><rsub|u>|\<bar\>>\<subset\>\<cal-Q\><with|mode|text|
    such that >\<cal-M\>\<vDash\>D\<wedge\>C\<Rightarrow\><wide|S|\<dot\>><rprime|'>,>>|<row|<cell|Rev<rsub|\<forall\>><around*|(|\<cal-Q\>,<wide|\<beta\>|\<bar\>>,D,C|)>>|<cell|=>|<cell|<around*|{|c<rprime|'><mid|\|>c=x<wide|=|\<dot\>>t\<in\>C,<with|mode|text|if
    >x=S<rprime|'><around*|(|t|)><with|mode|text| then
    >c<rprime|'>=S<around*|(|c|)><with|mode|text| else
    >c<rprime|'>=S*S<rprime|'><around*|(|c|)>|}>>>>>
  </eqnarray*>

  Note that <math|S> above is a substitution of subterms rather than of
  variables. To move further beyond fully maximal answers, we incorporate
  candidates <math|\<beta\><rsub|1><wide|=|\<dot\>>\<beta\><rsub|2>> for
  which the following conditions hold: <math|\<beta\><rsub|1>\<beta\><rsub|2>\<subset\><wide|\<beta\>|\<bar\>>>,
  <math|\<beta\><rsub|1>\<assign\>t<rsub|1>\<in\>\<b-U\><rsub|><around*|(|<wide|A|~><around*|(|D\<wedge\>C|)>|)>>,
  <math|\<beta\><rsub|2>\<assign\>t<rsub|2>\<in\>\<b-U\><rsub|><around*|(|<wide|A|~><around*|(|D\<wedge\>C|)>|)>>
  and <math|t<rsub|1><wide|=|\<dot\>>t<rsub|2>> is satisfiable. We also need
  to include the unifier of <math|t<rsub|1><wide|=|\<dot\>>t<rsub|2>> among
  the candidates, since otherwise the equation
  <math|\<beta\><rsub|1><wide|=|\<dot\>>\<beta\><rsub|2>> would not suffice
  to imply that of the atoms <math|\<beta\><rsub|1><wide|=|\<dot\>>t<rsub|1>>,
  <math|\<beta\><rsub|2><wide|=|\<dot\>>t<rsub|2>> which belongs to the
  conclusion <math|C>. The <em|full candidates>
  <math|\<b-U\><rsub|><around*|(|<wide|A|~><around*|(|D\<wedge\>C|)>|)>> and
  the <em|guess candidates> <math|<wide|\<beta\><rsub|1>\<assign\>\<beta\><rsub|2>;\<b-U\><around*|(|t<rsub|1><wide|=|\<dot\>>t<rsub|2>|)>|\<bar\>>>
  are kept apart, the guess candidates are guessed before the full
  candidates. By default, we additionally limit consideration to atoms
  <math|\<beta\><rsub|1><wide|=|\<dot\>>t<rsub|1>>,
  <math|\<beta\><rsub|2><wide|=|\<dot\>>t<rsub|2>> where
  <math|t<rsub|1>,t<rsub|2>> are not themselves variables.

  To recapitulate, the implementation is:

  <\itemize>
    <item>If there are no more candidates to add to the partial solution:
    check for repeated answers, skipping, and discarded answers.

    <item>If there are no more guessed candidates, pick the next full
    candidate atom <math|FV<around*|(|c|)>\<cap\><wide|\<beta\>|\<bar\>>\<neq\>\<varnothing\>>
    if any, reordering the candidates until one is found. Otherwise, pick the
    first guess candidate atom without reordering.

    <item>The are 6 mutually exclusive choices through which the algorithm
    loops.

    <\enumerate>
      <item>Try to drop the atom (if the partial answer plus remaining
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

      <item>Keep a variant of the original atom, but with constants
      substituted-out by variable-constant equations from the premise.
      Redundant, not available when the option <verbatim|-more_general> is
      on.
    </enumerate>

    <item>Each iteration is a backtracking point, the choices are tried in
    turn, depending on options selected.

    <item>Default ordering of choices is 1, 6, 2, 4, 3, 5 -- pushing 4 up
    minimizes the amount of branching in 5.

    <\itemize>
      <item>There is an option <verbatim|-more_general>, which reorders the
      choices to: 1, 6, 4, 2, 3, 5; however the option is not exposed in the
      interface because the cost of this reordering is prohibitive.

      <item>An option <verbatim|-richer_answers> reorders the choices to: 6,
      1, 2, 4, 3, 5; it does not increase computational cost but sometimes
      leads to answers that are not most general.

      <item>If choice 6 would lead to more negative constraints contradicted
      than choice 1, we pick choice 6 first for a particular candidate atom.

      <item>An option <verbatim|-prefer_guess> reorders choice 6 prior to
      choice 1, but only for guess candidates.
    </itemize>

    <item>Form initial candidates <math|Rev<rsub|\<forall\>><around*|(|\<cal-Q\>,<wide|\<beta\>|\<bar\>>,\<b-U\><around*|(|D\<wedge\>A<rsub|p>|)>,\<b-U\><around*|(|A<rsub|p>\<wedge\>D\<wedge\>C|)>|)>>.

    <item>Form the substitution of subterms for choice-6 counterparts of
    initial candidate atoms. For <math|\<alpha\><rsub|1><wide|=|\<dot\>>\<tau\>,\<ldots\>,\<alpha\><rsub|n><wide|=|\<dot\>>\<tau\>\<in\>\<b-U\><around*|(|D\<wedge\>A<rsub|p>|)>>,
    form the substitution of subterms <math|\<alpha\><rsub|1>\<assign\>\<alpha\><rsub|i>,\<ldots\>,\<alpha\><rsub|n>\<assign\>\<alpha\><rsub|i>,\<tau\>\<assign\>\<alpha\><rsub|i>>
    (excluding <math|\<alpha\><rsub|i>\<assign\>\<alpha\><rsub|i>>) where
    <math|\<alpha\><rsub|i>> is the most upstream existential variable (or
    parameter) and <math|\<tau\>> is a constant. Note that analogous
    transformation for a universally quantified variable as right-hand-sides
    is performed by <math|Rev<rsub|\<forall\>>>.

    <\itemize>
      <item>Since for efficiency reasons we do not always remove alien
      subterms, we need to mitigate the problem of alien subterm variables
      causing violation of the quantifier prefix. To this effect, we include
      the premise equations from other sorts in the process generating the
      initial candidates and choice 6 candidates, but not as candidates. Not
      to lose generality of answer, we only keep a renaming substitution, in
      particular we try to eliminate universal variables.
    </itemize>

    <item>Sort the initial candidates by decreasing size, because shorter
    answer atoms are more valuable and dropping a candidate from
    participating in an answer is the first choice.

    <\itemize>
      <item>There is an argument in favor of sorting by increasing size: so
      that the replacements of step 2 are formed at a root position before
      they are used in step 5 -- instead of forming a replacement at a
      subterm, and using it in step 5 at a root.

      <item>If ordering in increasing size turns out to be necessary, a
      workaround should be introduced to favor answers that, if possible, do
      not have parameters <math|<wide|\<beta\>|\<bar\>>> as left-hand-sides.
    </itemize>
  </itemize>

  The above ordering of choices ensures that more general answers are tried
  first. Moreover:

  <\itemize>
    <item>choice 1 could be dropped as it is equivalent to choice 2 applied
    on the root term;

    <item>choices 4 and 5 could be reordered but having choice 4 as soon as
    possible is important for efficiency.
  </itemize>

  We perform a two-layer iterative deepening (when without the
  <verbatim|-more_general> option): in the first run we only try choices 1
  and 6. It is an imperfect optimization since the running time gets longer
  whenever choices 2-5 are needed.

  <subsubsection|Heuristic for Better Answers to Invariants>

  We implement an optional heuristic in forming the candidates proposed by
  choice 6. It may lead to better invariants when multiple maximally general
  types are possible, but also it may lead to getting the most general type
  without the need for backtracking across iterations of the main algorithm,
  which unfortunately often takes very long.

  We look at the types of substitutions for the variables that are invariant
  parameters, in the partial answer, and try to form the initial candidates
  for choice 6 so that the return type variables cover the most of argument
  types variables, for each term substituted for an invariant parameter. We
  select from the candidates equations between any variable, or only
  non-argument-type variable, and a <math|FV<around*|(|<with|mode|text|argument
  types>|)>\\FV<around*|(|<with|mode|text|return type>|)>> variable -- we
  turn the equation so that the latter is the RHS. We locate the equations
  among the candidates that have an invariant parameter variable or a
  <math|FV<around*|(|<with|mode|text|return
  type>|)>\\FV<around*|(|<with|mode|text|argument types>|)>> variable as LHS.
  We apply the substitution to the RHS of these equations; if the LHS is an
  invariant parameter, we use the substitution based on equations where one
  side is a non-argument-type variable. We preserve the order of equations in
  the candidate list.

  <subsection|Simple Constraint Abduction for Linear
  Arithmetics><label|SCANumAlg>

  Here we expand on the overview from Section <reference|SCANumMain>. For
  checking validity or satisfiability, we use <em|Fourier-Motzkin
  elimination>. To avoid complexities we only handle the rational number
  domain. To extend the algorithm to integers, <em|Omega-test> procedure as
  presented in <cite|ArithQuantElim> needs to be adapted. The major
  operations are:

  <\itemize>
    <item><em|Elimination> of a variable takes an equation and selects a
    variable that is not upstream, i.e. to the left in <math|\<cal-Q\>>
    regarding alternations, of any other variable of the equation, and
    substitutes-out this variable from the rest of the constraint. The solved
    form contains an equation for this variable.

    <item><em|Projection> of a variable takes a variable <math|x> that is not
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
  process. When implicit equalities have been found, we iterate the process
  to normalize them as well.

  Our abduction algorithm follows a familiar incrementally-generate-and-test
  scheme as in term abduction. There are two new ideas, which can also be
  applied to abduction in other domains. We build a lazy list of possible
  transformations with linear combinations involving equations <math|a>
  implied by <math|D\<wedge\>C>. We pair each inequality <math|c> in <math|C>
  with all inequalities <math|d> implied by <math|D> which share a variable
  with <math|c> and try out the abduction answers to <math|d\<Rightarrow\>c>
  as contributions to the partial abduction answer to
  <math|D\<Rightarrow\>C>.

  To simplify the search in presence of a quantifier prefix, we preprocess
  the initial candidate by eliminating universally quantified variables:

  <\eqnarray*>
    <tformat|<table|<row|<cell|S>|<cell|=>|<cell|<around*|[|<wide|\<beta\><rsub|u>|\<bar\>>\<assign\><wide|t<rsub|u>|\<bar\>>|]><with|mode|text|
    for ><wide|\<forall\>\<beta\><rsub|u>|\<bar\>>\<subset\>\<cal-Q\><with|mode|text|
    such that >\<cal-M\>\<vDash\>D\<Rightarrow\><wide|S|\<dot\>>,>>|<row|<cell|Rev<rsub|\<forall\>><around*|(|\<cal-Q\>,<wide|\<beta\>|\<bar\>>,D,C|)>>|<cell|=>|<cell|<around*|{|c<rprime|'><mid|\|>c\<in\>C,<with|mode|text|if
    >\<cal-M\>\<vDash\>\<cal-Q\>.c<around*|[|<wide|\<beta\>|\<bar\>>\<assign\><wide|t|\<bar\>>|]><with|mode|text|
    for some ><wide|t|\<bar\>><with|mode|text| then
    >c<rprime|'>=c<with|mode|text| else >c<rprime|'>=S<around*|(|c|)>|}>>>>>
  </eqnarray*>

  Before accepting a new atom into the partial answer, we check that it would
  not violate the quantifier conditions from the <em|split> phase of the main
  algorithm, and that the partial answer is satisfiable with all implication
  branches of the joint abduction problem. As part of the quantifier
  conditions, we ensure that the escaping parameters are upward in the
  constraint before prenexization, i.e. are parameters of the type of a
  parent definition (containing a given definition in its body) rather than a
  parallel definition. The check of satisfiability we call <em|validation>.
  For domains other than the term domain, validation also involves
  instantiating use-sites of recursive definitions with parts of the partial
  answer, split in a simplified way.

  Abduction algorithm:

  <\enumerate>
    <item>Let <math|C<rsup|=><rprime|'>=<wide|A<rsub|i>|~><around*|(|C<rsup|=>|)>>,
    resp. <math|C<rsup|\<leqslant\>><rprime|'>=<wide|A<rsub|i>|~><around*|(|C<rsup|\<leqslant\>>|)>>
    where <math|C<rsup|=>>, resp. <math|C<rsup|\<leqslant\>>> are the
    equations, resp. inequalities in <math|C> and <math|<wide|A<rsub|i>|~>>
    is the substitution according to equations in <math|A<rsub|i>>. Let
    <math|D<rprime|'>=<wide|A<rsub|i>|~><around*|(|D\<wedge\><no-break>A<rsub|i>|)>>
    and <math|D<rsup|=><rprime|'>> be the equations in <math|D<rprime|'>>,
    i.e. substituted equations and implicit equalities. Let
    <math|D<rsup|\<leqslant\>><rprime|'>> be a solved form of inequalities.

    <\enumerate>
      <item>Let <math|C<rsup|=><rsub|0>=Rev<rsub|\<forall\>><around*|(|\<cal-Q\>,<wide|\<beta\>|\<bar\>>,D<rsup|=><rprime|'>,C<rsup|=><rprime|'>|)>>
      and <math|C<rsup|\<leqslant\>><rsub|0>=Rev<rsub|\<forall\>><around*|(|\<cal-Q\>,<wide|\<beta\>|\<bar\>>,D<rsup|=><rprime|'>,C<rsup|\<leqslant\>><rprime|'>|)>>.
    </enumerate>

    <item>Prepare the initial transformations from atoms
    <math|a\<in\>D<rsup|=><rprime|'>>:

    <\enumerate>
      <item>Add combinations <math|k<rsup|s>*a+b> for
      <math|k=-n\<ldots\>n,s=-1,1> to the stack of transformations to be
      tried for atoms <math|b>.

      <item>The final transformations have the form:
      <math|b\<mapsto\>b+\<Sigma\><rsub|a\<in\>D>k<rsub|a><rsup|s<rsub|a>>a>.
    </enumerate>

    <item>Modify <math|C<rsup|=><rprime|'>> to promote answers with variables
    rather than constants, as in term abduction: For
    <math|\<alpha\><rsub|1><wide|=|\<dot\>>\<tau\>,\<ldots\>,\<alpha\><rsub|n><wide|=|\<dot\>>\<tau\>\<in\>C<rsup|=><rprime|'>>,
    form the substitution of subterms <math|\<alpha\><rsub|1>\<assign\>\<alpha\><rsub|i>,\<ldots\>,\<alpha\><rsub|n>\<assign\>\<alpha\><rsub|i>,\<tau\>\<assign\>\<alpha\><rsub|i>>
    (excluding <math|\<alpha\><rsub|i>\<assign\>\<alpha\><rsub|i>>) where
    <math|\<alpha\><rsub|i>> is the most upstream existential variable (or
    parameter) and <math|\<tau\>> is a constant.

    <item>Start from <math|Acc\<assign\><around*|{||}>> and
    <math|C<rsub|0>\<assign\>C<rsup|=><rprime|'>\<wedge\>C<rsup|\<leqslant\>><rprime|'>>.
    Handle atoms <math|a> in <math|C<rsub|0>=a C<rsub|0><rprime|'>>,
    equations first.

    <item>Let <math|B=A<rsub|i>\<wedge\>D\<wedge\>C<rsub|0><rprime|'>\<wedge\>Acc>.

    <item>If <math|a> is a tautology (<math|0<wide|=|\<dot\>>0> or
    <math|c\<leq\>0> for <math|c\<leqslant\>0>) or <math|B\<Rightarrow\>C>,
    repeat with <math|C<rsub|0>\<assign\>C<rsub|0><rprime|'>>. Corresponds to
    choice 1 of term abduction.

    <item>If <math|B\<nRightarrow\>C>, for a candidate <math|a<rprime|'>>
    generated for <math|a>, starting with <math|a>, which passes validation
    against other branches in a joint problem:
    <math|Acc\<assign\>Acc\<cup\><around*|{|a<rprime|'>|}>>, or fail if all
    <math|a<rprime|'>> fail.

    <\enumerate>
      <item>If <math|a> is an inequality, let <math|a<rsub|0>> be an
      abduction answer to <math|d\<Rightarrow\>Rev<rsub|\<forall\>><around*|(|\<cal-Q\>,<wide|\<beta\>|\<bar\>>,D<rsup|=><rprime|'>,<wide|Acc<rsup|=>|~><around*|(|a|)>|)>>,
      where <math|d> belongs to the solved form inequalities implied by
      <math|D<rprime|'>>. Otherwise, let <math|a<rsub|0>=<wide|Acc<rsup|=>|~><around*|(|a|)>>.

      <item>Sort the candidates <math|a<rsub|0>> in order of decreasing
      value, described below. Let <math|a<rprime|'>> be <math|a<rsub|0>> with
      some <math|D<rsup|=><rprime|'>>-derived transformation applied.

      <\itemize>
        <item>We increase the value of <math|a<rsub|0>> for each variable
        that is bound by <math|a<rsub|0>> on the side that it is unbound in
        <math|B>. We decrease the value of <math|a<rsub|0>> for:

        <\itemize>
          <item>its size, proportionally to the sum of nominators and
          denominators,

          <item>containing a constant term,

          <item>containing parameters from multiple invariants,

          <item>introducing an implicit equality,

          <item>binding a variable by a constant on the side where it is
          already bounded by <math|B>,

          <item>binding a variable by a constant on the right (i.e. upper
          bound),

          <item>optionally, being less general than some other candidate,
          modulo <math|B>,

          <item>we include the value of inequalities implied by the candidate
          together with the partial answer (but not the partial answer alone)
          and not holding when parameters are universally quantified (see
          <em|atomization>).
        </itemize>

        The score determines the order in which atoms are tried.

        <item>Currently, we do not perform transformations when
        <math|a<rsub|0>> is an inequality, for simplicity and speed at cost
        of missing some answers. However, we eliminate the universal
        variables, i.e. we use <math|Rev<rsub|\<forall\>>> above. If it
        proves necessary, we will also try the transformations for the
        inequalities. For example, by trying all candidates <math|a<rsub|0>>
        before proceeding to the next transformation.
      </itemize>

      <item>If <math|A<rsub|i>\<wedge\><around*|(|Acc\<cup\><around*|{|a<rprime|'>|}>|)>>
      (resp. <math|A<rsub|i>\<wedge\><around*|(|Acc\<cup\><around*|{|a<rprime|''>|}>|)>>)
      does not pass validation for all <math|a<rprime|'>>, backtrack.

      <item>If <math|A<rsub|i>\<wedge\><around*|(|Acc\<cup\><around*|{|a<rprime|'>|}>|)>>
      (resp. <math|A<rsub|i>\<wedge\><around*|(|Acc\<cup\><around*|{|a<rprime|''>|}>|)>>)
      passes validation, repeat from step 5 with
      <math|C<rsub|0>\<assign\>C<rsub|0><rprime|'>,Acc\<assign\>Acc\<cup\><around*|{|a<rprime|'>|}>>
      (resp. <math|Acc\<assign\>Acc\<cup\><around*|{|a<rprime|''>|}>>).
    </enumerate>

    <item>The answers are <math|A<rsub|i+1>=A<rsub|i>\<wedge\>Acc>.
  </enumerate>

  We precompute the tranformation variants to try out. The parameter <math|n>
  is set by option <verbatim|-<no-break>num_abduction_rotations> and defaults
  to a small value (currently 3).

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

  To find the abduction answers to <math|d\<Rightarrow\>c>, pick a common
  variable <math|\<alpha\>\<in\>FV<around*|(|d|)>\<cap\>FV<around*|(|c|)>> or
  the constant <math|\<alpha\>=1>. We have four possibilities:

  <\enumerate>
    <item><math|d\<Leftrightarrow\>\<alpha\>\<leqslant\>d<rsub|\<alpha\>>>
    and <math|c\<Leftrightarrow\>\<alpha\>\<leqslant\>c<rsub|\<alpha\>>>: the
    abduction answers are <math|c> and <math|d<rsub|\<alpha\>>\<leqslant\>c<rsub|\<alpha\>>>,

    <item><math|d\<Leftrightarrow\>\<alpha\>\<leqslant\>d<rsub|\<alpha\>>>
    and <math|c\<Leftrightarrow\>c<rsub|\<alpha\>>\<leqslant\>\<alpha\>>: the
    abduction answer is only <math|c>,

    <item><math|d\<Leftrightarrow\>d<rsub|\<alpha\>>\<leqslant\>\<alpha\>>
    and <math|c\<Leftrightarrow\>\<alpha\>\<leqslant\>c<rsub|\<alpha\>>>: the
    abduction answer is only <math|c>,

    <item><math|d\<Leftrightarrow\>d<rsub|\<alpha\>>\<leqslant\>\<alpha\>>
    and <math|c\<Leftrightarrow\>c<rsub|\<alpha\>>\<leqslant\>\<alpha\>>: the
    abduction answers are <math|c> and <math|c<rsub|\<alpha\>>\<leqslant\>d<rsub|\<alpha\>>>.
  </enumerate>

  Thanks to cases (1) and (4) above, the abduction algorithm can find some
  answers which are not fully maximal. The joint constraint abduction
  algorithm can help in some of the remaining cases where fully maximal
  abduction is insufficient for some implications, by solving simpler
  implications first.

  We provide an optional optimization: we do not pass, in the first call to
  numerical abduction (the second iteration of the main algorithm), branches
  that contain unary predicate variables in the conclusion, i.e. we only use
  the ``non-recursive'' branches. Other optimizations that we use are:
  iterative deepening on the constant <math|n> used to generate
  <math|k<rsup|s>> factors. We also constrain the algorithm by filtering out
  transformations that contain ``too many'' variables, which can lead to
  missing answers if the setting <verbatim|-num_prune_at> -- ``too many'' --
  is too low. Similarly to term abduction, we count the number of steps of
  the loop and fail if more than the option <verbatim|-num_abduction_timeout>
  steps have been taken.

  <section|Constraint Generalization><label|ConstrnGenAlg>

  Here we expand on the exposition from Section <reference|ConstrnGenMain>.
  <em|Constraint generalization> answers are the maximally specific
  conjunctions of atoms that are implied by each of a given set of
  conjunction of atoms. In case of term equations the constraint
  generalization algorithm is based on the <em|anti-unification> algorithm.
  In case of linear arithmetic inequalities, constraint generalization is
  exactly finding the convex hull of a set of possibly unbounded polyhedra.
  We employ our unification algorithm to separate sorts. Since as a result we
  do not introduce variables for <em|alien subterms>, we include the
  variables introduced by anti-unification in constraints sent to constraint
  generalization for their respective sorts.

  The adjusted algorithm looks as follows:

  <\enumerate>
    <item>Let <math|\<wedge\><rsub|s>D<rsub|i,s>\<equiv\>\<b-U\><around|(|D<rsub|i>|)>>
    where <math|D<rsub|i,s>> is of sort <math|s>, be the result of our
    sort-separating unification.

    <item>For the sort <math|s<rsub|type>>:

    <\enumerate>
      <item>Let <math|V=<around*|{|x<rsub|j>,<wide|t<rsub|i,j>|\<bar\>><mid|\|>\<forall\>i\<exists\>t<rsub|i,j>.x<rsub|j><wide|=|\<dot\>>t<rsub|i,j>\<in\>D<rsub|i,s<rsub|type>>|}>>.

      <item>Let <math|G=<around*|{|<wide|\<alpha\>|\<bar\>><rsub|j>,u<rsub|j>,<wide|\<theta\><rsub|i,j>|\<bar\>><mid|\|>\<theta\><rsub|i,j>=<around*|[|<wide|\<alpha\>|\<bar\>><rsub|j>\<assign\><wide|g|\<bar\>><rsub|j><rsup|i>|]>,\<theta\><rsub|i,j><around*|(|u<rsub|j>|)>=t<rsub|i,j>|}>>
      be the most specific anti-unifiers of <math|<wide|t<rsub|i,j>|\<bar\>>>
      for each <math|j>.

      <item>Let <math|D<rsub|i><rsup|u>=\<wedge\><rsub|j><wide|\<alpha\>|\<bar\>><rsub|j><wide|=|\<dot\>><wide|g|\<bar\>><rsub|j><rsup|i>>
      and <math|D<rsub|i><rsup|g>=D<rsub|i,s<rsub|type>>\<wedge\>D<rsub|i><rsup|u>>.

      <item>Let <math|D<rsup|v><rsub|i>=<around*|{|x<wide|=|\<dot\>>y<mid|\|>x<wide|=|\<dot\>>t<rsub|1>\<in\>D<rsub|i><rsup|g>,y<wide|=|\<dot\>>t<rsub|2>\<in\>D<rsub|i><rsup|g>,D<rsub|i><rsup|g>\<vDash\>t<rsub|1><wide|=|\<dot\>>t<rsub|2>|}>>.

      <item>Let <math|A<rsub|s<rsub|type>>=\<wedge\><rsub|j>x<rsub|j><wide|=|\<dot\>>u<rsub|j>\<wedge\><big|cap><rsub|i><around*|(|D<rsub|i><rsup|g>\<wedge\>D<rsub|i><rsup|v>|)>>
      (where conjunctions are treated as sets of conjuncts and equations are
      ordered so that only one of <math|a<wide|=|\<dot\>>b,b<wide|=|\<dot\>>a>
      appears anywhere), and <math|<wide|\<alpha\>|\<bar\>><rsub|s<rsub|type>>=<wide|<wide|\<alpha\>|\<bar\>><rsub|j>|\<bar\>>>.

      <item>Let <math|\<wedge\><rsub|s>D<rsup|u><rsub|i,s>\<equiv\>D<rsup|u><rsub|i>>
      for <math|D<rsup|u><rsub|i,s>> of sort <math|s>.
    </enumerate>

    <item>For sorts <math|s\<neq\>s<rsub|type>>, let
    <math|\<exists\><wide|\<alpha\>|\<bar\>><rsub|s>.A<rsub|s>=LUB<rsub|s><around*|(|<wide|D<rsub|i><rsup|s>\<wedge\>D<rsup|u><rsub|i,s>|\<bar\>>|)>>.

    <item>The answer is <math|\<exists\><wide|<wide|\<alpha\><rsup|j><rsub|i>|\<bar\>>|\<bar\>><wide|<wide|\<alpha\>|\<bar\>><rsub|s>|\<bar\>>.\<wedge\><rsub|s>A<rsub|s>>.
  </enumerate>

  We simplify the result by substituting-out redundant answer variables.

  We follow the anti-unification algorithm provided in <cite|AntiUnifAlg>,
  fig. 2.

  <subsection|Extended Convex Hull><label|NumConstrnGenAlg>

  <cite|ConvexHull> provides a polynomial-time algorithm to find the
  half-space represented convex hull of closed polytopes. It can be
  generalized to unbounded polytopes -- conjunctions of linear inequalities.
  Our implementation is inspired by this algorithm but very much simpler, at
  cost of losing the optimality requirement.

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
  inequalities to the convex hull algorithm. Separately, we compute the
  equations common to all branches, because the convex hull algorithm is not
  guaranteed to recover them.

  <subsection|Issues in Inferring Postconditions><label|NumConv>

  Although finding recursive function invariants -- predicate variables
  solved by abduction -- could theoretically fail to converge for both the
  type sort and the numerical sort constraints, neither problem was observed.
  Finding existential type constraints can only fail to converge for
  numerical sort, because solutions are expected to decrease in strength. But
  such diverging numerical constraints are commonplace. The main algorithm
  starts by performing constraint generalization only on implication branches
  corresponding to non-recursive cases, i.e. without binary predicate
  variables in premise (or unary predicate variables in conclusion). This
  generates a stronger constraint than the correct one. Subsequent iterations
  include all branches in constraint generalization, weakening the
  constraints, and so still weaker constraints are fed to constraint
  generalization in each following step. To ensure convergence of the
  numerical part, starting from some step of the main loop, we compare
  consecutive solutions and extrapolate the trend. Currently we simply
  intersect the sets of atoms, but first we expand equations into pairs of
  inequalities.

  We ``lift'' variables escaping the scope of a postcondition by renaming
  them to fresh variables, which are added to the answer variables of
  generalization. We apply this renaming ater anti-unification, prior to
  performing generalization in other domains. We pass to other domains as
  parameters to preserve only non-escaping variables. The non-escaping
  variables are these which have in their scope a variable
  <math|\<alpha\><rsub|K>>, passed as argument to the generalization
  algorithm.

  Constraint generalization limited to non-recursive branches, the initial
  iteration of postcondition inference, will often generate constraints that
  contradict other branches. For another iteration to go through, the partial
  solutions need to be consistent. Therefore we filter the constraints using
  the same validation mechanism as in abduction. We add atoms to a constraint
  greedily, but to favor relevant atoms, we do the filtering while computing
  the connected component of constraint generalization result. See the
  details of the main algorithm in section <reference|MainAlgoBody>.

  While reading section <reference|MainAlgoBody>, you will notice that
  postconditions are not subjected to stratification. This is because the
  type system does not support nested existential types.

  In the simplification step at the end of constraint generalization, we try
  to preserve alien variables that are parameters rather than substituting
  them by constants. A parameter can only equal a constant if not all
  branches have been considered for constraint generalization. The parameter
  is both as informative as the constant, and less likely to contradict other
  branches.

  <subsection|Abductive Constraint Generalization><label|AbdConstrnGenAlg>

  Here we expand on the overview from Section <reference|AbdConstrnGenMain>.

  <em|Global variables> here are the variables shared by all disjuncts, i.e.
  <math|\<cap\><rsub|i>FV<around*|(|D<rsub|i>|)>>, remaining variables are
  <em|non-global>. Recall that for numerical constraint generalization, we
  either substitute-out a non-global variable in a branch if it appears in an
  equation, or we drop the inequalities it appers in if it is not part of any
  equation. Non-global variables can also pose problems for the term sort, by
  forcing constraint generalization answers to be too general. When inferring
  the type for a function, which has a branch that does not use one of
  arguments of the function, the existential type inferred would hide the
  corresponding information in the result, even if the remaining branches
  assume the argument has a single concrete type. We would like the
  corresponding non-global variable to resolve to the concrete type suggested
  by other branches of the resulting constraint.

  We extend the notion of constraint generalization: substitution <math|U>
  and solved form <math|\<exists\><wide|\<alpha\>|\<bar\>>.A> is an answer to
  <em|abductive constraint generalization> problem
  <math|<wide|D<rsub|i>|\<bar\>>> given a quantifier prefix <math|\<cal-Q\>>
  when:

  <\enumerate>
    <item><math|<around*|(|\<forall\>i|)>\<vDash\>U<around*|(|D<rsub|i>|)>\<Rightarrow\>\<exists\><wide|\<alpha\>|\<bar\>>\\FV<around*|(|U|)>.A>;

    <item>If <math|\<alpha\>\<in\>Dom<around*|(|U|)>>, then
    <math|<around*|(|\<exists\>\<alpha\>|)>\<in\>\<cal-Q\>> -- variables
    substituted by <math|U> are existentially quantified;

    <item><math|<around*|(|\<forall\>i|)>\<vDash\>\<forall\><around*|(|Dom<around*|(|U|)>|)>\<exists\><around*|(|FV<around*|(|D<rsub|i>|)>\\Dom<around*|(|U|)>|)>.D<rsub|i>>.
  </enumerate>

  Our generalized anti-unification algorithm is in Table
  <reference|AntiUnifAlg>.<\float|float|t>
    <\big-table>
      <\eqnarray*>
        <tformat|<table|<row|<cell|au<rsub|U,G><around*|(|t;\<ldots\>;t|)>>|<cell|=>|<cell|\<varnothing\>,t,U,G>>|<row|<cell|au<rsub|U,G><around*|(|f<around*|(|<wide|t|\<bar\>><rsup|1>|)>;\<ldots\>;f<around*|(|<wide|t|\<bar\>><rsup|n>|)>|)>>|<cell|=>|<cell|<wide|\<alpha\>|\<bar\>>,f<around*|(|<wide|g|\<bar\>>|)>,U<rprime|'>,G<rprime|'>>>|<row|<cell|<with|mode|text|where
        \ ><wide|\<alpha\>|\<bar\>>,<wide|g|\<bar\>>,U<rprime|'>,G<rprime|'>>|<cell|=>|<cell|aun<rsub|U,G><around*|(|<wide|t|\<bar\>><rsup|1>;\<ldots\>;<wide|t|\<bar\>><rsup|n>|)>>>|<row|<cell|au<rsub|U,G><around*|(|t<rsub|1>;\<ldots\>;t<rsub|n>|)>>|<cell|=>|<cell|\<varnothing\>,\<alpha\>,U,G>>|<row|<cell|<with|mode|text|when>>|<cell|>|<cell|<around*|(|<around*|[|t<rsub|1>;\<ldots\>;t<rsub|n>|]>\<mapsto\>\<alpha\>|)>\<in\>G>>|<row|<cell|au<rsub|U,G><around*|(|\<ldots\>;\<beta\><rsub|i>;\<ldots\>;f<around*|(|<wide|t|\<bar\>><rsup|j>|)>;\<ldots\><with|mode|text|
        as ><wide|t|\<bar\>>|)>>|<cell|=>|<cell|<wide|\<alpha\>|\<bar\>><wide|\<alpha\>|\<bar\>><rprime|'>,g,U<rprime|''>,G<rprime|'>>>|<row|<cell|<with|mode|text|where
        \ ><wide|\<alpha\>|\<bar\>><rprime|'>,g,U<rprime|''>,G<rprime|'>>|<cell|=>|<cell|au<rsub|U<rprime|'>,G><around*|(|<wide|t|\<bar\>><around*|[|\<beta\><rsub|i>\<assign\>f<around*|(|<wide|\<alpha\>|\<bar\>>|)>|]>|)>>>|<row|<cell|U<rprime|'>>|<cell|=>|<cell|U<around*|[|\<beta\><rsub|i>\<assign\>f<around*|(|<wide|\<alpha\>|\<bar\>>|)>|]>\<wedge\>\<beta\><rsub|i><wide|=|\<dot\>>f<around*|(|<wide|\<alpha\>|\<bar\>>|)>>>|<row|<cell|<with|mode|text|when>>|<cell|>|<cell|<around*|(|\<exists\>\<beta\><rsub|i>|)>\<in\>\<cal-Q\>\<vee\>\<beta\><rsub|i>\<in\><wide|\<beta\>|\<bar\>><with|mode|text|,
        treat ><wide|\<alpha\>|\<bar\>><with|mode|text| as quantified with
        >\<exists\>\<beta\><rsub|i>>>|<row|<cell|au<rsub|U,G><around*|(|\<ldots\>;\<beta\><rsub|i>;\<ldots\>;\<beta\><rsub|j>;\<ldots\><with|mode|text|
        as ><wide|t|\<bar\>>|)>>|<cell|=>|<cell|<wide|\<alpha\>|\<bar\>><rprime|'>,g,U<rprime|''>,G<rprime|'>>>|<row|<cell|<with|mode|text|where
        \ ><wide|\<alpha\>|\<bar\>><rprime|'>,g,U<rprime|''>,G<rprime|'>>|<cell|=>|<cell|au<rsub|U<rprime|'>,G><around*|(|<wide|t|\<bar\>><around*|[|\<beta\><rsub|i>\<assign\>\<beta\><rsub|j>|]>|)>>>|<row|<cell|U<rprime|'>>|<cell|=>|<cell|U<around*|[|\<beta\><rsub|i>\<assign\>\<beta\><rsub|j>|]>\<wedge\>\<beta\><rsub|i><wide|=|\<dot\>>\<beta\><rsub|j>>>|<row|<cell|<with|mode|text|when>>|<cell|>|<cell|\<exists\>\<beta\><rsub|i>\<in\>\<cal-Q\>,\<beta\><rsub|j>\<leqslant\><rsub|\<cal-Q\>>\<beta\><rsub|i>>>|<row|<cell|au<rsub|U,G><around*|(|t<rsub|1>;\<ldots\>;t<rsub|n>|)>>|<cell|=>|<cell|\<alpha\>,\<alpha\>,U,<around*|(|<around*|[|t<rsub|1>;\<ldots\>;t<rsub|n>|]>\<mapsto\>\<alpha\>|)>G>>|<row|<cell|<with|mode|text|otherwise,>>|<cell|>|<cell|<with|mode|text|where
        >\<alpha\>#FV<around*|(|t<rsub|1>;\<ldots\>;t<rsub|n>,U,G|)>>>|<row|<cell|aun<rsub|U,G><around*|(|\<varnothing\>|)>>|<cell|=>|<cell|\<varnothing\>,\<varnothing\>,U,G>>|<row|<cell|aun<rsub|U,G><around*|(|\<varnothing\>;\<ldots\>|)>>|<cell|=>|<cell|\<varnothing\>,\<varnothing\>,U,G>>|<row|<cell|aun<rsub|U,G><around*|(|t<rsup|1><rsub|1>,<wide|t|\<bar\>><rsup|1>;\<ldots\>;t<rsup|n><rsub|1>,<wide|t|\<bar\>><rsup|n>|)>>|<cell|=>|<cell|<wide|\<alpha\>|\<bar\>><wide|\<alpha\>|\<bar\>><rprime|'>,g<wide|g|\<bar\>><rprime|'>,U<rprime|''>,G<rprime|''>>>|<row|<cell|<with|mode|text|where
        \ ><wide|\<alpha\>|\<bar\>>,g,U<rprime|'>,G<rprime|'>>|<cell|=>|<cell|au<rsub|U,G><around*|(|t<rsub|1><rsup|1>;\<ldots\>;t<rsub|1><rsup|n>|)>>>|<row|<cell|<with|mode|text|and
        \ ><wide|\<alpha\>|\<bar\>><rprime|'>,<wide|g|\<bar\>><rprime|'>,U<rprime|''>,G<rprime|''>>|<cell|=>|<cell|aun<rsub|U<rprime|'>,G<rprime|'>><around*|(|<wide|t|\<bar\>><rsup|1>;\<ldots\>;<wide|t|\<bar\>><rsup|n>|)>>>>>
      </eqnarray*>

      <label|AntiUnifAlg>
    </big-table|Abductive anti-unification algorithm>
  </float> The notational shorthand <math|\<ldots\>;\<beta\><rsub|i>;\<ldots\>;f<around*|(|<wide|t|\<bar\>><rsup|j>|)>;\<ldots\>>
  represents the case where all terms are either existential variables or
  start with a function symbol <math|f>. Similarly,
  <math|\<ldots\>;\<beta\><rsub|i>;\<ldots\>;\<beta\><rsub|j>;\<ldots\>>
  represents the case when there is a variable <math|\<beta\><rsub|j>> such
  that all terms are either <math|\<beta\><rsub|j>> or are existential
  variables to the right of <math|\<beta\><rsub|j>> in the quantifier.

  The sort-integrating algorithm essentially does not change:

  <\enumerate>
    <item>Let <math|\<wedge\><rsub|s>D<rsub|i,s>\<equiv\>\<b-U\><around|(|D<rsub|i>|)>>
    where <math|D<rsub|i,s>> is of sort <math|s>, be the result of our
    sort-separating unification.

    <item>For the sort <math|s<rsub|type>>:

    <\enumerate>
      <item>Let <math|V=<around*|{|x<rsub|j>,<wide|t<rsub|i,j>|\<bar\>><mid|\|>\<forall\>i\<exists\>t<rsub|i,j>.x<rsub|j><wide|=|\<dot\>>t<rsub|i,j>\<in\>D<rsub|i,s<rsub|type>>|}>>.

      <item>Let <math|G=<around*|{|<wide|\<alpha\>|\<bar\>><rsub|j>,g<rsub|j>,u<rsub|j>,<wide|\<theta\><rsub|i,j>|\<bar\>><mid|\|>\<theta\><rsub|i,j>=<around*|[|<wide|\<alpha\>|\<bar\>><rsub|j>\<assign\><wide|g|\<bar\>><rsub|j><rsup|i>|]>,\<theta\><rsub|i,j><around*|(|g<rsub|j>|)>=<around*|(|\<wedge\><rsub|k\<leqslant\>j>u<rsub|k>|)><around*|(|t<rsub|i,j>|)>|}>>
      be the most specific anti-unifiers of
      <math|<wide|<rsub|><around*|(|\<wedge\><rsub|k\<leqslant\>j>u<rsub|k>|)><around*|(|t<rsub|i,j>|)>|\<bar\>>>
      for each <math|j>, where <math|\<wedge\><rsub|j>u<rsub|j>> is the
      resulting <math|U<rsub|>>.

      <item>Let <math|D<rsub|i><rsup|u>=\<wedge\><rsub|j><wide|\<alpha\>|\<bar\>><rsub|j><wide|=|\<dot\>><wide|g|\<bar\>><rsub|j><rsup|i>>
      and <math|D<rsub|i><rsup|g>=D<rsub|i,s<rsub|type>>\<wedge\>D<rsub|i><rsup|u>>.

      <item>Let <math|D<rsup|v><rsub|i>=<around*|{|x<wide|=|\<dot\>>y<mid|\|>x<wide|=|\<dot\>>t<rsub|1>\<in\>D<rsub|i><rsup|g>,y<wide|=|\<dot\>>t<rsub|2>\<in\>D<rsub|i><rsup|g>,D<rsub|i><rsup|g>\<vDash\>t<rsub|1><wide|=|\<dot\>>t<rsub|2>|}>>.

      <item>Let <math|A<rsub|s<rsub|type>>=\<wedge\><rsub|j>x<rsub|j><wide|=|\<dot\>>g<rsub|j>\<wedge\><big|cap><rsub|i><around*|(|D<rsub|i><rsup|g>\<wedge\>D<rsub|i><rsup|v>|)>>
      (where conjunctions are treated as sets of conjuncts and equations are
      ordered so that only one of <math|a<wide|=|\<dot\>>b,b<wide|=|\<dot\>>a>
      appears anywhere), and <math|<wide|\<alpha\>|\<bar\>><rsub|s<rsub|type>>=<wide|<wide|\<alpha\>|\<bar\>><rsub|j>|\<bar\>>>.

      <item>Let <math|\<wedge\><rsub|s>D<rsup|u><rsub|i,s>\<equiv\>D<rsup|u><rsub|i>>
      for <math|D<rsup|u><rsub|i,s>> of sort <math|s>.
    </enumerate>

    <item>For sorts <math|s\<neq\>s<rsub|type>>, let
    <math|\<exists\><wide|\<alpha\>|\<bar\>><rsub|s>.A<rsub|s>=LUB<rsub|s><around*|(|<wide|D<rsub|i><rsup|s>\<wedge\>D<rsup|u><rsub|i,s>|\<bar\>>|)>>.

    <item>The answer is substitution <math|U=\<wedge\><rsub|j>u<rsub|j>> and
    solved form <math|\<exists\><wide|<wide|\<alpha\><rsup|j><rsub|i>|\<bar\>>|\<bar\>><wide|<wide|\<alpha\>|\<bar\>><rsub|s>|\<bar\>>.\<wedge\><rsub|s>A<rsub|s>>.
  </enumerate>

  The task of constraint generalization is to find postconditions. Usually,
  it is beneficial to make the postcondition, i.e. the existential type that
  is the return type of a function, more specific, at the expense of making
  the overal type of the function less general. To this effect, constraint
  generalization, just as abduction takes invariant parameters
  <math|<wide|\<beta\>|\<bar\>>>. We replace conditions
  <math|\<exists\>\<beta\><rsub|i>\<in\>\<cal-Q\>> above by
  <math|\<beta\><rsub|i>\<in\><wide|\<beta\>|\<bar\>>\<vee\><around*|(|\<exists\>\<beta\><rsub|i>|)>\<in\>\<cal-Q\>>.
  Recall that the right-hand-side (RHS) variable <math|\<beta\><rsub|j>> can
  in general be universally quantified: <math|\<forall\>\<beta\><rsub|j>\<in\>\<cal-Q\>>.
  We exclude universal non-parameter RHS when a parameter is present: if for
  any <math|\<beta\><rsub|i>>, <math|\<beta\><rsub|i>\<in\><wide|\<beta\>|\<bar\>>>,
  then for all <math|\<beta\><rsub|i>> including RHS,
  <math|\<beta\><rsub|i>\<in\><wide|\<beta\>|\<bar\>>\<vee\>\<exists\>\<beta\><rsub|i>\<in\>\<cal-Q\>>.
  Note that having weaker postconditions also results in correct types, just
  not the intended ones. In rare cases a weaker postcondition but a more
  general invariant can be beneficial. To this effect, the option
  <verbatim|-<no-break>more_existential> turns off generating the
  substitution entries when the RHS is a variable, i.e. the case
  <math|au<rsub|U,G><around*|(|\<ldots\>;\<beta\><rsub|i>;\<ldots\>;\<beta\><rsub|j>;\<ldots\><with|mode|text|
  as ><wide|t|\<bar\>>|)>> is skipped.

  Due to greater flexibility of the numerical domain, abductive extension of
  numerical constraint generalization does not seem necessary and is turned
  off by default. It could take a similar form, we experiment with the
  following heuristic. If atoms specific to a disjunct (i.e. not shared by
  all disjuncts) do not contain a variable, do not include the disjunct when
  considering inclusion of inequalities containing the variable in the
  constraint generalization answer.

  <section|Incorporating Negative Constraints><label|NegElimAlg>

  Here we expand on the overview from Section <reference|NegElimMain>. We
  call a <em|negative constraint> an implication
  <math|D\<Rightarrow\>\<b-F\>> in the normalized constraint
  <math|\<cal-Q\>.\<wedge\><rsub|i><around*|(|D<rsub|i>\<Rightarrow\>C<rsub|i>|)>>,
  and we call <math|D> the <em|negated constraint>. Such constraints are
  generated for pattern matching branches whose right-hand-side is the
  expression <verbatim|assert false>. A generic approach to account for
  negative constraints is as follows. We check whether the solution found by
  multisort abduction contradicts the negated constraints. If some negated
  constraint is satisfiable, we discard the answer and ``fall back'' to try
  finding another answer. Unfortunately, this approach is insufficient when
  the answer sought for is not among the maximally general answers to the
  remaining, <em|positive part> of the constraint. Therefore, we introduce
  <em|negation elimination>.

  For the numerical sort, our implementation of negation elimination can
  produce too strong constraints when the numerical domain is intended to
  contain non-integer rational numbers, and can be turned off by the
  <verbatim|-no_int_negation> option. It can also produce too weak
  constraints, because it produces at most one atom for a given negated
  constraint. If the abduction answer for terms does already contradict a
  negated constraint <math|D>, we are done. Otherwise, let
  <math|D=c<rsub|1>\<wedge\>\<ldots\>\<wedge\>c<rsub|n>>. For numerical sort
  atoms <math|c<rsub|i>>, either drop them from consideration or convert
  their negation <math|\<neg\>c<rsub|i>> into <math|d<rsub|i>> or
  <math|d<rsub|i<rsub|1>>\<vee\>d<rsub|i<rsub|2>>> as follows. The conversion
  assumes that the numerical domain is integers. We convert an inequality
  <math|w\<leqslant\>0>, e.g. <math|<frac|1|3>x-<frac|1|2>y-2\<leqslant\>0>,
  to <math|*-k*w+1\<leqslant\>0>, e.g. <math|3y-2x+13\<leqslant\>0>, where
  <math|k> is the common denominator so that <math|k*w> has only integer
  numbers. Note that <math|\<neg\><around*|(|w\<leqslant\>0|)>\<Leftrightarrow\>w\<gtr\>0\<Leftrightarrow\>-w\<less\>0\<Leftrightarrow\>-k*w\<less\>0\<Leftarrow\>-k*w+1\<leqslant\>0>.
  Similarly, we convert an equation <math|w<wide|=|\<dot\>>0> to inequalities
  <math|-k*w+1\<leqslant\>0\<vee\>k*w+1\<leqslant\>0>. Note that
  <math|\<neg\><around*|(|w\<geqslant\>0|)>\<Leftrightarrow\>w\<less\>0\<Leftrightarrow\>k*w\<less\>0\<Leftarrow\>k*w+1\<leqslant\>0>.
  In both cases the implications <math|\<Leftarrow\>> would be equivalences
  if the numerical domain was integers rather than rational numbers. At
  present, we ignore <em|opti> atoms. The disjunct <math|d<rsub|i>> is a
  conjunction of inequalities if <math|c<rsub|i>> is a <em|subopti> atom.

  Assuming that each negative constraint points to a single atomic fact, we
  try to find one disjunct <math|d<rsub|i>>, resp. <math|d<rsub|i<rsub|1>>>
  or <math|d<rsub|i<rsub|2>>>, corresponding to <math|\<neg\>c<rsub|i>>,
  discarding those disjuncts that contradict any implication branch.
  Specifically, let <math|\<cal-Q\>.\<wedge\><rsub|i><around*|(|D<rsub|i>\<Rightarrow\>C<rsub|i>|)>>
  be the constraint we solve, and let <math|\<exists\><wide|\<alpha\>|\<bar\>>.A>
  be a term abduction answer for <math|\<cal-Q\>.\<wedge\><rsub|i:C<rsub|i>\<neq\>\<b-F\>><around*|(|D<rsub|i>\<Rightarrow\>C<rsub|i>|)>>.
  We search for <math|i> such that for all <math|k> with
  <math|C<rsub|k>\<neq\>\<b-F\>> and <math|D<rsub|k>> satisfiable,
  <math|d<rsub|i>\<wedge\>A\<wedge\>D<rsub|k>\<wedge\>C<rsub|k>> is
  satisfiable. We provide a function <math|NegElim<around*|(|\<neg\>D,<wide|B<rsub|i>|\<bar\>>|)>=d<rsub|i<rsub|0>>>,
  where <math|d<rsub|i<rsub|0>>> is the biggest, syntactically, such atom,
  and <math|B<rsub|i>=A\<wedge\>D<rsub|i>\<wedge\>C<rsub|i>>.

  Unfortunately, for the sort of terms we do not have well-defined
  representation of dis-equalities not using negations. The generic approach
  of relying on backtracking to find another abduction answer is more useful
  for terms than for the numeric sort. It falls short, however, when negation
  was intended to prevent the answer from being too general. Ideally, we
  would introduce disequation atoms <math|\<tau\><wide|\<neq\>|\<dot\>>\<tau\>>
  and follow the scheme we use for the numerical sort. For now, we only cover
  a very specific use of negation, to discriminate among type-level
  ``enumeration''. We limit negation elimination to considering atoms of the
  form <math|\<beta\><wide|=|\<dot\>>\<varepsilon\><rsub|1>>, and contradict
  them by introducing atoms <math|\<beta\><wide|=|\<dot\>>\<varepsilon\><rsub|2>>,
  for types <math|\<varepsilon\><rsub|1>\<neq\>\<varepsilon\><rsub|2>>
  without parameters which we call <em|phantom enumerations>. The variables
  <math|\<beta\>> are limited to the answer variables generated in the
  previous iteration of the main algorithm. The nullary datatype constructor
  <math|\<varepsilon\><rsub|2>> is picked so that the atom is valid, using
  the same validation procedure as the one passed to the abduction algorithm.
  The heuristic defines phantom enumerations as nullary phantom types that do
  not share datype parameter position (in GADT constructor definitions) with
  non-enumeration types. When the equations derived for different negated
  constraints involve a common variable as the left-hand-side, we select a
  common right-hand-side. In the end, we only introduce the negation
  elimination result to the answer when a single disjunct remains.

  Since the <em|discard> (or taboo) list used by backtracking is based on
  complete answers, it is preferable to perform negation elimination prior to
  abduction. Otherwise, the search might fall into a loop where abduction
  keeps returning the same answer, since it is more general than the
  discarded answer incorporating negation elimination result.

  <section|<em|opti> and <em|subopti>: <em|minimum> and <em|maximum>
  Relations in <verbatim|num>><label|OptiAtoms>

  We extend the numerical domain with relations <em|opti> and <em|subopti>
  defined below. Operations <em|min> and <em|max> can then be defined using
  it. Let <math|k,v,w> be any linear combinations. Note that the relations
  are introduced to smuggle in a limited form of disjunction into the solved
  forms.

  <\eqnarray*>
    <tformat|<table|<row|<cell|opti<around*|(|v,w|)>>|<cell|=>|<cell|v\<leqslant\>0\<wedge\>w\<leqslant\>0\<wedge\><around*|(|v<wide|=|\<dot\>>0\<vee\>w<wide|=|\<dot\>>0|)>>>|<row|<cell|k<wide|=|\<dot\>>min<around*|(|v,w|)>>|<cell|=>|<cell|opti<around*|(|k-v,k-w|)>>>|<row|<cell|k<wide|=|\<dot\>>max<around*|(|v,w|)>>|<cell|=>|<cell|opti<around*|(|v-k,w-k|)>>>|<row|<cell|subopti<around*|(|v,w|)>>|<cell|=>|<cell|v\<leqslant\>0\<vee\>w\<leqslant\>0>>|<row|<cell|k\<leqslant\>max<around*|(|v,w|)>>|<cell|=>|<cell|subopti<around*|(|k-v,k-w|)>>>|<row|<cell|min<around*|(|v,w|)>\<leqslant\>k>|<cell|=>|<cell|subopti<around*|(|v-k,w-k|)>>>>>
  </eqnarray*>

  In particular, <math|opti<around*|(|v,w|)>\<equiv\>max<around*|(|v,w|)><wide|=|\<dot\>>0>
  and <math|subopti<around*|(|v,w|)>\<equiv\>min<around*|(|v,w|)>\<leqslant\>0>.
  We call an <em|opti> or <em|subopti> atom <em|directed> when there is a
  variable <math|n> that appears in <math|v> and <math|w> with the same sign.
  We do not prohibit undirected <em|opti> or <em|subopti> atoms, but we do
  not introduce them, to avoid bloat.

  For simplicity, we do not support <em|min> and <em|max> as subterms in
  concrete syntax. Instead, we parse atoms of the form
  <verbatim|k=min(><math|\<ldots\>><verbatim|,><math|\<ldots\>><verbatim|)>,
  resp. <verbatim|k=max(><math|\<ldots\>><verbatim|,><math|\<ldots\>><verbatim|)>
  into the corresponding <em|opti> atoms, where <verbatim|k> is any numerical
  term. Similarly for <em|subopti>. We also print directed <em|opti> and
  <em|subopti> atoms using the syntax with <math|min> and
  <math|max>expressions. Not to pollute the syntax with a new keyword, we use
  concrete syntax <verbatim|min\|max(><math|\<ldots\>><verbatim|,><math|\<ldots\>><verbatim|)>
  for parsing arbitrary, and printing non-directed, <em|opti> atoms, and
  <verbatim|min\|\|max(><math|\<ldots\>><verbatim|,><math|\<ldots\>><verbatim|)>
  for <em|subopti> respectively.

  If need arises, in a future version, we can extend <em|opti> to a larger
  arity <math|N>.

  <subsection|Normalization, Validity and Implication Checking>

  In the function that produces solved forms of numerical constraints, we
  treat <em|opti> clauses in an efficient but incomplete manner, doing a
  single step of constraint solving. We include the <em|opti> terms in
  processed inequalities. After equations have been solved, we apply the
  substitution to the <em|opti> and <em|subopti> disjunctions. When one of
  the <em|opti> resp. <em|subopti> disjunct terms becomes contradictory or
  the disjunct terms become equal, we include the other in implicit
  equalities, resp. in inequalities to solve. When one of the <em|opti> or
  <em|subopti> terms becomes tautological, we drop the disjunction. We
  iterate calls to the solver function to propagate implicit equalities.

  We do not perform case splitting on <em|opti> and <em|subopti>
  disjunctions, therefore some contradictions may be undetected. However,
  abduction and constraint generalization currently perform upfront case
  splitting on <em|opti> and <em|subopti> disjunctions, sometimes leading to
  splits that a smarter solver would avoid.

  <subsection|Abduction>

  We eliminate <em|opti> and <em|subopti> in premises by expanding the
  definition and converting the branch into two branches, e.g.
  <math|D\<wedge\><around*|(|v<wide|=|\<dot\>>0\<vee\>w<wide|=|\<dot\>>0|)>\<Rightarrow\>C>
  into <math|<around*|(|D\<wedge\>v<wide|=|\<dot\>>0\<Rightarrow\>C|)>\<wedge\><around*|(|D\<wedge\>w<wide|=|\<dot\>>0\<Rightarrow\>C|)>>.
  Recall that an <em|opti> atom also implies inequalities
  <math|v\<leqslant\>\<wedge\>w\<leqslant\>0> assumed to be in <math|D>
  above. This is one form of <em|case splitting>: we consider cases
  <math|v<wide|=|\<dot\>>0> and <math|w<wide|=|\<dot\>>0>, resp.
  <math|v\<leqslant\>0> and <math|w\<leqslant\>0>, separately. We do not
  eliminate <em|opti> and <em|subopti> in conclusions. Rather, we consider
  whether to keep or drop it in the answer, like with other candidate atoms.
  The transformations apply to an <em|opti> atom by applying to both its
  arguments.

  Generating a new <em|opti> atom for inclusion in an answer means finding a
  pair of equations such that the following conditions hold. Each equation,
  together with remaining atoms of an answer but without the remaining
  equation selected, is a correct answer to a simple abduction problem. The
  equations selected share a variable and are oriented so that the variable
  appears with the same sign in them. The resulting <em|opti> atom passes the
  validation test for joint constraint abduction. We may implement generating
  new <em|opti> atoms for abduction answers in a future version, when need
  arises. Currently, we only generate new <em|opti> and <em|subopti> atoms
  for postconditions, i.e. during constraint generalization.

  <subsection|Constraint Generalization>

  We eliminate <em|opti> and <em|subopti> atoms prior to finding the extended
  convex hull of <math|<wide|D<rsub|i>|\<bar\>>> by expanding the definition
  and converting the disjunction <math|\<vee\><rsub|i>D<rsub|i>> to
  disjunctive normal form. This is another form of case splitting.

  In addition to finding the extended convex hull, we need to discover
  <em|opti> relations that are implied by <math|\<vee\><rsub|i>D<rsub|i>>. We
  select these faces of the convex hull which also appear as an equation in
  some disjuncts. Out of these faces, we find all minimal covers of size 2,
  i.e. pairs of faces such that in each disjunct, either one or the other
  linear combination appears as an equation. We only keep pairs of faces that
  share a same-sign variable. For the purposes of detecting <em|opti>
  relations, we need to perform transitive closure of the extended convex
  hull equations and inequalities, because the redundant inequalities might
  be required to find a cover.

  Finding <em|subopti> atoms is similar. We find all minimal covers of size
  2, i.e. pairs of inequalities such that one or the other appears in each
  disjunct. We only keep pairs of inequalities that share a same-sign
  variable.

  We provide a function for the numerical domain to remove <em|opti> atoms of
  the form <math|k<wide|=|\<dot\>>min<around*|(|c,v|)>>,
  <math|k<wide|=|\<dot\>>min<around*|(|v,c|)>>,
  <math|k<wide|=|\<dot\>>max<around*|(|c,v|)>> or
  <math|k<wide|=|\<dot\>>min<around*|(|v,c|)>> for a constant <math|c>,
  similarly for <em|subopti> atoms, while in initial iterations where
  constraint generalization is only performed for non-recursive branches.

  We need to further extend the notion of (abductive) constraint
  generalization, to achieve the results required for postcondition
  inference. For constraint branches <math|<wide|D<rsub|i>\<Rightarrow\>C<rsub|i>|\<bar\>>>,
  we need not only the disjuncts <math|<wide|D<rsub|i>\<wedge\>C<rsub|i>|\<bar\>>>,
  but also the premises <math|<wide|D<rsub|i>|\<bar\>>>. We keep <em|opti>
  and <em|subopti> atoms <math|opti<around*|(|v,w|)>,subopti<around*|(|v,w|)>>
  such that either both <math|v\<leqslant\>w> and <math|w\<leqslant\>v> are
  <em|satisfiable with> all <em|implication branches>, or neither is. An atom
  <math|c> is satisfiable with implication
  <math|D<rsub|i>\<Rightarrow\>C<rsub|i>> here, when either
  <math|c\<wedge\>D<rsub|i>> is not satisfiable, or
  <math|c\<wedge\>D<rsub|i>\<wedge\>C<rsub|i>> is satisfiable. The underlying
  idea is that since <em|opti> and <em|subopti> atoms express a disjunction,
  resp. <math|v\<leqslant\>0\<wedge\>w\<leqslant\>0\<wedge\><around*|(|v<wide|=|\<dot\>>0\<vee\>w<wide|=|\<dot\>>0|)>>
  and <math|v\<leqslant\>0\<vee\>w\<leqslant\>0>, they are meaningful when
  both cases of the disjunction can obtain under some circumstances. When
  only one of the atoms, say <math|v\<leqslant\>w>, is satisfiable with all
  implication branches, we make an abductive guess that
  <math|v\<leqslant\>w>.

  <section|Solving for Predicate Variables><label|PredVarAlg>

  Here we discuss the implementation in <name|InvarGenT> of ideas in the
  overview from Section <reference|PredVarOverview> and in the formal
  discussion from Section <reference|PredVarMain>. As we decided to provide
  the first solution to abduction problems, we accordingly simplify the task
  of solving for predicate variables. Instead of a tree of solutions being
  refined, we have a single sequence which we unfold until reaching fixpoint
  or contradiction. Another choice point besides abduction in the original
  algorithm is the selection of invariants that leaves a consistent subset of
  atoms as residuum. Here we also select the first solution found. We
  introduce a form of backtracking, described in section <reference|Details>.

  <subsection|Solving for Predicates in Premises>

  The core of our inference algorithm consists of distributing atoms of an
  abduction answer among the predicate variables. The negative occurrences of
  predicate variables, when instantiated with the updated solution, enrich
  the premises so that the next round of abduction leads to a smaller answer
  (in number of atoms).

  Let us discuss the algorithm for <math|Split<around*|(|\<cal-Q\>,<wide|\<alpha\>|\<bar\>>,A,<wide|<wide|\<beta\>|\<bar\>><rsup|\<chi\>>|\<bar\>>,<wide|A<rsub|\<chi\>><rsup|0>|\<bar\>>|)>>.
  Note that due to existential types predicates, we actually compute
  <math|Split<around*|(|\<cal-Q\>,<wide|\<alpha\>|\<bar\>>,A,<wide|<wide|\<beta\>|\<bar\>><rsup|\<beta\><rsub|\<chi\>>>|\<bar\>>,<wide|A<rsub|\<beta\><rsub|\<chi\>>><rsup|0>|\<bar\>>|)>>,
  i.e. we index by <math|\<beta\><rsub|\<chi\>>> (which can be multiple for a
  single <math|\<chi\>>) rather than <math|\<chi\>>. We retain the notation
  indexing by <math|\<chi\>> as it better conveys the intent. We do not pass
  quantifiers around to reflect the source code: the helper function
  <verbatim|loop avs ans sol> of function <verbatim|split> corresponds to
  <math|Split<around*|(|<wide|\<alpha\>|\<bar\>>,A,<wide|A<rsub|\<beta\><rsub|\<chi\>>><rsup|0>|\<bar\>>|)>>.

  <\eqnarray*>
    <tformat|<table|<row|<cell|\<alpha\>\<prec\>\<beta\>>|<cell|\<equiv\>>|<cell|\<alpha\>\<less\><rsub|\<cal-Q\>>\<beta\>\<vee\><around*|(|\<alpha\>\<leqslant\><rsub|\<cal-Q\>>\<beta\>\<wedge\>\<beta\>\<nless\><rsub|\<cal-Q\>>\<alpha\>\<wedge\>\<alpha\>\<in\><wide|<wide|\<beta\>|\<bar\>><rsup|\<chi\>>|\<bar\>>\<wedge\>\<beta\>\<nin\><wide|<wide|\<beta\>|\<bar\>><rsup|\<chi\>>|\<bar\>>|)>>>|<row|<cell|A<rsub|\<alpha\>\<beta\>>>|<cell|=>|<cell|<around*|{|\<beta\><wide|=|\<dot\>>\<alpha\>\<in\>A<mid|\|>\<beta\>\<in\><wide|<wide|\<beta\>|\<bar\>><rsup|\<chi\>>|\<bar\>>\<wedge\><around*|(|\<exists\>\<alpha\>|)>\<in\>\<cal-Q\>\<wedge\>\<beta\>\<prec\>\<alpha\>|}>>>|<row|<cell|A<rsub|0>>|<cell|=>|<cell|A\\A<rsub|\<alpha\>\<beta\>>>>|<row|<cell|A<rsup|1><rsub|\<chi\>>>|<cell|=>|<cell|<around*|{|c\<in\>A<rsub|0><mid|\|>\<forall\>\<alpha\>\<in\>FV<around*|(|c|)>.<around*|(|\<exists\>\<alpha\>|)>\<in\>\<cal-Q\>\<vee\><next-line><with|mode|text|
    \ \ \ >\<alpha\>\<less\><rsub|\<cal-Q\>>\<beta\><rsub|\<chi\>>\<wedge\>\<alpha\>\<nin\>PrimCV<around*|(|c|)>\<vee\>\<alpha\>\<in\><wide|<wide|\<beta\>|\<bar\>><rsup|\<chi\>>|\<bar\>>\<wedge\>\<alpha\>\<in\>PrimCV<around*|(|c|)>|}>>>|<row|<cell|A<rsup|2><rsub|\<chi\>>>|<cell|=>|<cell|Atomized<around*|(|<wide|<wide|\<beta\>|\<bar\>><rsup|\<chi\>>|\<bar\>>,A<rsub|\<chi\>><rsup|1>|)>>>|<row|<cell|A<rsup|3><rsub|\<chi\>>>|<cell|=>|<cell|A<rsup|2><rsub|\<chi\>>\\\<cup\><rsub|\<chi\><rprime|'>>A<rsup|1><rsub|\<chi\><rprime|'>>>>|<row|<cell|<with|mode|text|if>>|<cell|>|<cell|\<cal-M\>\<nvDash\>\<cal-Q\>.<around*|(|A\<setminus\>\<cup\><rsub|\<chi\>>A<rsup|2><rsub|\<chi\>>|)><around*|[|<wide|\<alpha\>|\<bar\>>\<assign\><wide|t|\<bar\>>|]><with|mode|text|
    \ for all ><wide|t|\<bar\>>>>|<row|<cell|<with|mode|text|then
    return>>|<cell|>|<cell|\<bot\>>>|<row|<cell|<with|mode|text|for all
    ><wide|A<rsub|\<chi\>><rsup|+>|\<bar\>><with|mode|text| min. w.r.t.
    >\<subset\><with|mode|text| s.t.>>|<cell|>|<cell|\<wedge\><rsub|\<chi\>><around*|(|A<rsub|\<chi\>><rsup|+>\<subset\>A<rsup|2><rsub|\<chi\>>|)>\<wedge\>\<cal-M\>\<vDash\>\<cal-Q\>.<around*|(|\<cup\><rsub|\<chi\>>A<rsub|\<chi\>><rsup|+>\<Rightarrow\>A|)><around*|[|<wide|\<alpha\>|\<bar\>>\<assign\><wide|t|\<bar\>>|]><with|mode|text|
    \ for some ><wide|t|\<bar\>>:>>|<row|<cell|<with|mode|text|if>>|<cell|>|<cell|Strat<around*|(|A<rsup|+><rsub|\<chi\>>,<wide|\<beta\>|\<bar\>><rsup|\<chi\>>|)><with|mode|text|
    \ returns >\<bot\><with|mode|text| for some
    >\<chi\>>>|<row|<cell|<with|mode|text|then
    return>>|<cell|>|<cell|\<bot\>>>|<row|<cell|<with|mode|text|else
    \ ><wide|\<alpha\>|\<bar\>><rsub|+><rsup|\<chi\>>,A<rsub|\<chi\>><rsup|L>,A<rsup|R><rsub|\<chi\>>>|<cell|=>|<cell|Strat<around*|(|A<rsup|+><rsub|\<chi\>>,<wide|\<beta\>|\<bar\>><rsup|\<chi\>>|)>>>|<row|<cell|A<rsub|\<chi\>>>|<cell|=>|<cell|A<rsub|\<chi\>><rsup|0>\<cup\>A<rsub|\<chi\>><rsup|L>>>|<row|<cell|<wide|\<alpha\>|\<bar\>><rsup|\<chi\>><rsub|0>>|<cell|=>|<cell|<wide|\<alpha\>|\<bar\>>\<cap\>FV<around*|(|A<rsub|\<chi\>>|)>>>|<row|<cell|<wide|\<alpha\>|\<bar\>><rsup|\<chi\>>>|<cell|=>|<cell|<around*|(|<wide|\<alpha\>|\<bar\>><rsup|\<chi\>><rsub|0>\<setminus\><big|cup><rsub|\<chi\><rprime|'>\<less\><rsub|\<cal-Q\>>\<chi\>><wide|\<alpha\>|\<bar\>><rsup|\<chi\><rprime|'>><rsub|0>|)><wide|\<alpha\>|\<bar\>><rsub|+><rsup|\<chi\>>>>|<row|<cell|A<rsub|+>>|<cell|=>|<cell|\<cup\><rsub|\<chi\>>A<rsub|\<chi\>><rsup|R>>>|<row|<cell|A<rsub|res>>|<cell|=>|<cell|A<rsub|+>\<cup\><wide|A<rsub|+>|~><around*|(|A\<setminus\>\<cup\><rsub|\<chi\>>A<rsub|\<chi\>><rsup|+>|)>>>|<row|<cell|<with|mode|text|if>>|<cell|>|<cell|\<cup\><rsub|\<chi\>><wide|\<alpha\>|\<bar\>><rsup|\<chi\>>\<neq\>\<varnothing\>\<vee\>\<cup\><rsub|\<chi\>>A<rsup|3><rsub|\<chi\>>\<neq\>\<varnothing\><with|mode|text|
    \ then>>>|<row|<cell|\<cal-Q\><rprime|'>,A<rsub|res><rprime|'>,<wide|\<exists\><wide|\<alpha\>|\<bar\>><rprime|'><rsup|\<chi\>>.A<rsub|\<chi\>><rprime|'>|\<bar\>>>|<cell|\<in\>>|<cell|Split<around*|(|\<cal-Q\><around*|[|<wide|\<forall\><wide|\<beta\>|\<bar\>><rsup|\<chi\>>|\<bar\>>\<assign\><wide|\<forall\><around*|(|<wide|\<beta\>|\<bar\>><rsup|\<chi\>>\<cup\><wide|\<alpha\>|\<bar\>><rsup|\<chi\>>|)>|\<bar\>>|]>,<wide|\<alpha\>|\<bar\>>\<setminus\>\<cup\><rsub|\<chi\>><wide|\<alpha\>|\<bar\>><rsup|\<chi\>>,A<rsub|res>\<wedge\><rsub|\<chi\>>A<rsup|3><rsub|\<chi\>>,<next-line><with|mode|text|
    \ \ \ \ \ \ \ ><wide|<wide|\<beta\>|\<bar\>><rsup|\<chi\>>\<cup\><wide|\<alpha\>|\<bar\>><rsup|\<chi\>>|\<bar\>>,<wide|A<rsub|\<chi\>>|\<bar\>>|)>>>|<row|<cell|<with|mode|text|return>>|<cell|>|<cell|\<cal-Q\><rprime|'>,A<rsub|\<alpha\>\<beta\>>\<wedge\>A<rsub|res><rprime|'>,<wide|\<exists\><wide|\<alpha\>|\<bar\>><rsup|\<chi\>><wide|\<alpha\>|\<bar\>><rprime|'><rsup|\<chi\>>.A<rsub|\<chi\>><rprime|'>|\<bar\>>>>|<row|<cell|<with|mode|text|else
    return>>|<cell|>|<cell|\<cal-Q\>\<exists\><around*|(|<wide|\<alpha\>|\<bar\>>\<setminus\>\<cup\><rsub|\<chi\>><wide|\<alpha\>|\<bar\>><rsup|\<chi\>>|)>,A<rsub|\<alpha\>\<beta\>>\<wedge\>A<rsub|res>,<wide|\<exists\><wide|\<alpha\>|\<bar\>><rsup|\<chi\>>.A<rsub|\<chi\>>|\<bar\>>>>>>
  </eqnarray*>

  where <math|Strat<around*|(|A,<wide|\<beta\>|\<bar\>><rsup|\<chi\>>|)>> is
  computed as follows: for every <math|c\<in\>A>, and for every
  <math|\<beta\><rsub|2>\<in\>FV<around*|(|c|)>> such that
  <math|\<beta\><rsub|1>\<less\><rsub|\<cal-Q\>>\<beta\><rsub|2>> for
  <math|\<beta\><rsub|1>\<in\><wide|\<beta\>|\<bar\>><rsup|\<chi\>>>, if
  <math|\<beta\><rsub|2>> is universally quantified in <math|\<cal-Q\>> and
  <math|\<beta\><rsub|2>\<nin\><wide|<wide|\<beta\>|\<bar\>><rsup|\<chi\>>|\<bar\>>>,
  then return <math|\<bot\>>; otherwise, introduce a fresh variable
  <math|\<alpha\><rsub|f>>, replace <math|c\<assign\>c<around*|[|\<beta\><rsub|2>\<assign\>\<alpha\><rsub|f>|]>>,
  add <with|mode|math|\<beta\><rsub|2><wide|=|\<dot\>>\<alpha\><rsub|f>> to
  <with|mode|math|A<rsup|R><rsub|\<chi\>>> and <math|\<alpha\><rsub|f>> to
  <with|mode|math|<wide|\<alpha\>|\<bar\>><rsub|+><rsup|\<chi\>>>, after
  replacing all such <with|mode|math|\<beta\><rsub|2>> add the resulting
  <math|c> to <with|mode|math|A<rsub|\<chi\>><rsup|L>>.
  <math|PrimCV<around*|(|c|)>> stands for <em|primary constrained variables>
  of an atom <math|c>. These are defined as the substituted variables in
  solved forms for term constraints, and in the case of a numerical atom, the
  shared variable of a directed opti or subopti atom, i.e. the variable
  <math|v> in <math|v\<leqslant\>max<around*|(|\<ldots\>|)>>,
  <math|min<around*|(|\<ldots\>|)>\<leqslant\>v>,
  <math|v=max<around*|(|\<ldots\>|)>>, <math|v=min<around*|(|\<ldots\>|)>>.

  Description of the algorithm in more detail:

  <\enumerate>
    <item><math|<tabular|<tformat|<table|<row|<cell|\<alpha\>\<prec\>\<beta\>>|<cell|\<equiv\>>|<cell|\<alpha\>\<less\><rsub|\<cal-Q\>>\<beta\>\<vee\><around*|(|\<alpha\>\<leqslant\><rsub|\<cal-Q\>>\<beta\>\<wedge\>\<beta\>\<nless\><rsub|\<cal-Q\>>\<alpha\>\<wedge\>\<alpha\>\<in\><wide|<wide|\<beta\>|\<bar\>><rsup|\<chi\>>|\<bar\>>\<wedge\>\<beta\>\<nin\><wide|<wide|\<beta\>|\<bar\>><rsup|\<chi\>>|\<bar\>>|)>>>>>>>
    The variables <math|<wide|<wide|\<beta\>|\<bar\>><rsup|\<chi\>>|\<bar\>>>
    are the invariant parameters of the solution from the previous round. We
    need to keep them apart from other variables even when they're not
    separated by quantifier alternation.

    <item><math|<tabular|<tformat|<table|<row|<cell|A<rsub|0>>|<cell|=>|<cell|A\\A<rsub|\<alpha\>\<beta\>>>>>>>>
    where<math|<tabular|<tformat|<table|<row|<cell|A<rsub|\<alpha\>\<beta\>>>|<cell|=>|<cell|<around*|{|\<beta\><wide|=|\<dot\>>\<alpha\>\<in\>A<mid|\|>\<beta\>\<in\><wide|<wide|\<beta\>|\<bar\>><rsup|\<chi\>>|\<bar\>>\<wedge\><around*|(|\<exists\>\<alpha\>|)>\<in\>\<cal-Q\>\<wedge\>\<beta\>\<prec\>\<alpha\>|}>>>>>>>
    Discard the ``scaffolding'' information, in particular the
    <math|A<rsub|+>> equations introduced by <math|Strat> in an earlier
    iteration.

    <item><math|<tabular|<tformat|<table|<row|<cell|A<rsup|1><rsub|\<chi\>>>|<cell|=>|<cell|<around*|{|c\<in\>A<rsub|0><mid|\|>\<forall\>\<alpha\>\<in\>FV<around*|(|c|)>\\<wide|\<beta\>|\<bar\>><rsup|\<chi\>>.<around*|(|\<exists\>\<alpha\>|)>\<in\>\<cal-Q\>\<vee\>\<alpha\>\<less\><rsub|\<cal-Q\>>\<beta\><rsub|\<chi\>>|}>>>>>>>
    Gather atoms pertaining to predicate <math|\<chi\>>, which should not
    remain in the residuum.

    <item><math|<tabular|<tformat|<table|<row|<cell|A<rsup|2><rsub|\<chi\>>>|<cell|=>|<cell|Atomized<around*|(|<wide|<wide|\<beta\>|\<bar\>><rsup|\<chi\>>|\<bar\>>,A<rsub|\<chi\>><rsup|1>|)>>>>>>>
    An atomized form of <math|A<rsub|\<chi\>><rsup|1>> wrt.
    <math|<wide|<wide|\<beta\>|\<bar\>><rsup|\<chi\>>|\<bar\>>>: a
    conjunction of atoms equivalent to <math|A<rsub|\<chi\>><rsup|1>>
    containing some of the implications of <math|A<rsub|\<chi\>><rsup|1>>,
    see the formal exposition of InvarGenT. Actually, rather than computing
    the atomized form upfront, we generate its contribution to
    <math|A<rsub|\<chi\>><rsup|+>> while performing Fourier-Motzkin
    elimination to check <math|\<cal-M\>\<vDash\>\<cal-Q\>.<around*|(|\<cup\><rsub|\<chi\>>A<rsub|\<chi\>><rsup|+>\<Rightarrow\><no-break>A|)>>.

    <item><math|<tabular|<tformat|<table|<row|<cell|A<rsup|3><rsub|\<chi\>>>|<cell|=>|<cell|A<rsup|2><rsub|\<chi\>>\\\<cup\><rsub|\<chi\><rprime|'>>A<rsup|1><rsub|\<chi\><rprime|'>>>>>>>>
    We prune atoms coming from atomization that are already present in the
    invariants. Actually, in the implementation we prune by redundancy with
    the invariants assigned so far.

    <item><math|<tabular|<tformat|<table|<row|<cell|<with|mode|text|if
    >\<cal-M\>\<nvDash\>\<cal-Q\>.<around*|(|A\<setminus\>\<cup\><rsub|\<chi\>>A<rsup|1><rsub|\<chi\>>|)><around*|[|<wide|\<alpha\>|\<bar\>>\<assign\><wide|t|\<bar\>>|]><with|mode|text|
    \ for all ><wide|t|\<bar\>><with|mode|text| then return >\<bot\>>>>>>>:
    Failed solution attempt. A common example is when the use site of
    recursive definition, resp. the existential type introduction site, is
    not in scope of a defining site of recursive definition, resp. an
    existential type elimination site, and has too strong requirements.
    FIXME:

    <item><math|<with|mode|text|for all ><wide|A<rsub|\<chi\>><rsup|+>|\<bar\>><with|mode|text|
    min. w.r.t. >\<subset\><with|mode|text|
    s.t.>\<wedge\><rsub|\<chi\>><around*|(|A<rsub|\<chi\>><rsup|+>\<subset\>A<rsub|\<chi\>><rsup|2>|)>\<wedge\>\<cal-M\>\<vDash\>\<cal-Q\>.<around*|(|\<cup\><rsub|\<chi\>>A<rsub|\<chi\>><rsup|+>\<Rightarrow\>A|)><around*|[|<wide|\<alpha\>|\<bar\>>\<assign\><wide|t|\<bar\>>|]><with|mode|text|
    \ for some ><wide|t|\<bar\>>:> Select invariants such that the residuum
    <math|A\<setminus\>\<cup\><rsub|\<chi\>>A<rsub|\<chi\>><rsup|+>> is
    consistent. The final residuum <math|A<rsub|res>> represents the global
    constraints, the solution for global type variables. The solutions
    <math|A<rsub|\<chi\>><rsup|+>> represent the invariants, the solution for
    invariant type parameters.

    <item><math|<tabular|<tformat|<table|<row|<cell|<with|mode|text|if>>|<cell|>|<cell|Strat<around*|(|A<rsup|+><rsub|\<chi\>>,<wide|\<beta\>|\<bar\>><rsup|\<chi\>>|)><with|mode|text|
    \ returns >\<bot\><with|mode|text| for some
    >\<chi\>>>>>><with|mode|text|then return >\<bot\>> In the implementation,
    we address stratification issues already during abduction.

    <item><math|<wide|\<alpha\>|\<bar\>><rsub|+><rsup|\<chi\>>,A<rsub|\<chi\>><rsup|L>,A<rsup|R><rsub|\<chi\>>=Strat<around*|(|A<rsup|+><rsub|\<chi\>>,<wide|\<beta\>|\<bar\>><rsup|\<chi\>>|)>>
    is computed as follows: for every <math|c\<in\>A<rsup|+><rsub|\<chi\>>>,
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
      <item>We will add <math|<wide|\<alpha\>|\<bar\>><rsub|+><rsup|\<chi\>>>
      to <math|<wide|\<beta\>|\<bar\>><rsup|\<chi\>>>.
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

    <item><math|<tabular|<tformat|<table|<row|<cell|<with|mode|text|if>>|<cell|>|<cell|\<cup\><rsub|\<chi\>><wide|\<alpha\>|\<bar\>><rsup|\<chi\>>\<neq\>\<varnothing\>\<vee\>\<cup\><rsub|\<chi\>>A<rsup|3><rsub|\<chi\>>\<neq\>\<varnothing\><with|mode|text|
    \ then>>>>>>> -- If new parameters or new atoms have been introduced, we
    need to redistribute the remaining atoms to make
    <math|\<cal-Q\><rprime|'>.A<rsub|res>> valid again.

    <item><math|<tabular|<tformat|<table|<row|<cell|\<cal-Q\><rprime|'>,A<rsub|res><rprime|'>,<wide|\<exists\><wide|\<alpha\>|\<bar\>><rprime|'><rsup|\<chi\>>.A<rsub|\<chi\>><rprime|'>|\<bar\>>>|<cell|\<in\>>|<cell|Split<around*|(|\<cal-Q\><around*|[|<wide|\<forall\><wide|\<beta\>|\<bar\>><rsup|\<chi\>>|\<bar\>>\<assign\><wide|\<forall\><around*|(|<wide|\<beta\>|\<bar\>><rsup|\<chi\>>\<cup\><wide|\<alpha\>|\<bar\>><rsup|\<chi\>>|)>|\<bar\>>|]>,<wide|\<alpha\>|\<bar\>>\<setminus\>\<cup\><rsub|\<chi\>><wide|\<alpha\>|\<bar\>><rsup|\<chi\>>,A<rsub|res>\<wedge\><rsub|\<chi\>>A<rsup|3>,<wide|<wide|\<beta\>|\<bar\>><rsup|\<chi\>>\<cup\><wide|\<alpha\>|\<bar\>><rsup|\<chi\>>|\<bar\>>,<wide|A<rsub|\<chi\>>|\<bar\>>|)>>>>>>>
    Recursive call includes <math|<wide|\<alpha\>|\<bar\>><rsup|\<chi\>><rsub|+>>
    in <math|<wide|\<beta\>|\<bar\>><rsup|\<chi\>>> so that, among other
    things, <math|A<rsub|+>> are redistributed into <math|A<rsub|\<chi\>>>.

    <item><math|<tabular|<tformat|<table|<row|<cell|<with|mode|text|return>>|<cell|>|<cell|\<cal-Q\><rprime|'>,A<rsub|res><rprime|'>,<wide|\<exists\><wide|\<alpha\>|\<bar\>><rsup|\<chi\>><wide|\<alpha\>|\<bar\>><rprime|'><rsup|\<chi\>>.A<rsub|\<chi\>><rprime|'>|\<bar\>>>>>>>>
    We do not add <math|\<forall\><wide|\<alpha\>|\<bar\>>> in front of
    <math|\<cal-Q\><rprime|'>> because it already includes these variables.
    <math|<wide|<wide|\<alpha\>|\<bar\>><rsub|+><rsup|\<chi\>><wide|\<alpha\><rsub|>|\<bar\>><rsup|\<chi\>><rsub|+><rprime|'>|\<bar\>>>
    lists all variables introduced by <math|Strat>.

    <item><math|<tabular|<tformat|<table|<row|<cell|<with|mode|text|else
    return>>|<cell|>|<cell|\<cal-Q\>\<exists\><around*|(|<wide|\<alpha\>|\<bar\>>\<setminus\>\<cup\><rsub|\<chi\>><wide|\<alpha\>|\<bar\>><rsup|\<chi\>>|)>,A<rsub|res>,<wide|\<exists\><wide|\<alpha\>|\<bar\>><rsup|\<chi\>>.A<rsub|\<chi\>>|\<bar\>>>>>>>>
    Note that <math|<wide|\<alpha\>|\<bar\>>\<setminus\>\<cup\><rsub|\<chi\>><wide|\<alpha\>|\<bar\>><rsup|\<chi\>>>
    does not contain the current <math|<wide|\<beta\>|\<bar\>><rsup|\<chi\>>>,
    because <math|<wide|\<alpha\>|\<bar\>>> does not contain it initially and
    the recursive call maintains that: <math|<wide|\<alpha\>|\<bar\>>\<assign\><wide|\<alpha\>|\<bar\>>\<setminus\>\<cup\><rsub|\<chi\>><wide|\<alpha\>|\<bar\>><rsup|\<chi\>>,<wide|\<beta\>|\<bar\>><rsup|\<chi\>>\<assign\><wide|\<beta\>|\<bar\>><rsup|\<chi\>><wide|\<alpha\>|\<bar\>><rsup|\<chi\>>>.
  </enumerate>

  Finally we define <math|Split<around*|(|<wide|\<alpha\>|\<bar\>>,A|)>\<assign\>Split<around*|(|<wide|\<alpha\>|\<bar\>>,A,<wide|\<b-T\>|\<bar\>>|)>>.
  The complete algorithm for solving predicate variables is presented in the
  next section.

  <subsection|Solving for Existential Types Predicates and Main
  Algorithm><label|MainAlgoBody>

  The general scheme is that we perform constraint generalization on branches
  with positive occurrences of existential type predicate variables on each
  round. Since the branches are substituted with the solution from previous
  round, constraint generalization will automatically preserve monotonicity.
  We retain existential types predicate variables in the later abduction
  step.

  What differentiates existential type predicate variables from recursive
  definition predicate variables is that the former are not local to context,
  while the latter are treated as local to context. It means that free
  variables need to be bound in the former while they are retained in the
  latter. However, it is just a technical difference because

  In the algorithm we operate on all predicate variables, and perform
  additional operations on existential type predicate variables; there are no
  operations pertaining only to recursive definition predicate variables. The
  equation numbers <math|<around*|(|N|)>> below are matched by comment
  numbers <verbatim|(* N *)> in the source code. Let
  <math|\<chi\><rsub|\<varepsilon\>K>> be the invariant which will constrain
  the existential type <math|\<varepsilon\><rsub|K>>, or <math|\<top\>>. When
  <math|\<chi\><rsub|\<varepsilon\>K>=\<top\>>, then we define
  <math|<wide|\<beta\>|\<bar\>><rsup|\<chi\><rsub|\<varepsilon\>K>,k>=\<varnothing\>>.
  Step <math|k> of the loop of the final algorithm:

  <\eqnarray*>
    <tformat|<cwith|16|16|2|2|cell-valign|c>|<cwith|17|17|3|3|cell-valign|B>|<cwith|23|23|2|2|cell-valign|c>|<table|<row|<cell|<wide|\<exists\><wide|\<beta\>|\<bar\>><rsup|\<chi\>,k>.F<rsub|\<chi\>>|\<bar\>>>|<cell|=>|<cell|S<rsub|k>>>|<row|<cell|>|<cell|>|<cell|<with|mode|text|In
    iteration 2, remove non-term-sort atoms>>>|<row|<cell|>|<cell|>|<cell|<with|mode|text|containing
    outer-scope parameters from >S<rsub|k>.>>|<row|<cell|D<rsub|K><rsup|\<alpha\>>\<Rightarrow\>C<rsub|K><rsup|\<alpha\>>\<in\>R<rsub|k><rsup|->S<rsub|k><around*|(|\<Phi\>|)>>|<cell|=>|<cell|<with|mode|text|all
    such that >\<chi\><rsub|K><around*|(|\<alpha\>,\<alpha\><rsub|\<alpha\>><rsup|K>|)>\<in\>C<rsub|K><rsup|\<alpha\>>,<eq-number>>>|<row|<cell|>|<cell|>|<cell|<wide|C<rsup|\<alpha\>><rsub|j>|\<bar\>>=<around*|{|C<mid|\|>D\<Rightarrow\>C\<in\>S<rsub|k><around*|(|\<Phi\>|)>\<wedge\>D\<subseteq\>D<rsup|\<alpha\>><rsub|K>|}>>>|<row|<cell|\<alpha\><rsub|K>>|<cell|:>|<cell|\<chi\><rsub|K><around*|(|\<alpha\><rsub|K>|)><with|mode|text|
    is a positive atom in >\<Phi\>>>|<row|<cell|U<rsub|\<chi\><rsub|K>>,\<exists\><wide|\<alpha\>|\<bar\>><rsup|\<chi\><rsub|K>><rsub|g>.G<rsub|\<chi\><rsub|K>>,<wide|B<rsub|d><rsup|K>|\<bar\>>>|<cell|=>|<cell|LUB<around*|(|\<alpha\><rsub|K>,<wide|\<delta\><wide|=|\<dot\>>\<alpha\>\<wedge\>D<rsup|\<alpha\>><rsub|K>\<wedge\><rsub|j>C<rsup|\<alpha\>><rsub|j>|\<bar\>><rsub|\<alpha\>\<in\><wide|\<alpha\><rsub|3><rsup|i,K>|\<bar\>>>|)><eq-number>>>|<row|<cell|<wide|\<tau\>|\<vect\>><rsub|\<varepsilon\><rsub|K>>>|<cell|=>|<cell|<wide|<around*|{|\<alpha\>\<in\>FV<around*|(|G<rsub|\<chi\><rsub|K>>|)>\\\<delta\>\<delta\><rprime|'><wide|\<alpha\>|\<bar\>><rsup|\<chi\><rsub|K>><rsub|g><mid|\|><around*|(|\<exists\>\<alpha\>|)>\<in\>\<cal-Q\>\<vee\>\<alpha\>\<in\><wide|<wide|\<beta\>|\<bar\>><rsup|\<chi\>>|\<bar\>>\\<wide|\<beta\>|\<bar\>><rsup|\<chi\><rsub|K>>|}>|\<vect\>>>>|<row|<cell|\<Xi\><around*|(|\<exists\><wide|\<alpha\>|\<bar\>><rsup|\<chi\><rsub|K>><rsub|g>.G<rsub|\<chi\><rsub|K>>|)>>|<cell|=>|<cell|\<exists\>FV<around*|(|<wide|\<tau\>|\<vect\>><rsub|\<varepsilon\><rsub|K>>,G<rsub|\<chi\><rsub|K>>|)>\\\<delta\>\<delta\><rprime|'>.\<delta\><rprime|'><wide|=|\<dot\>><wide|\<tau\>|\<vect\>><rsub|\<varepsilon\><rsub|K>>\<wedge\>G<rsub|\<chi\><rsub|K>>>>|<row|<cell|<around*|(|\<exists\><wide|\<alpha\>|\<bar\>><rsup|\<chi\><rsub|K>>.F<rsub|\<chi\><rsub|K>>|)>,\<rho\>>|<cell|=>|<cell|H<around*|(|R<rsub|k><around*|(|\<chi\><rsub|K>|)>,\<Xi\><around*|(|\<exists\><wide|\<alpha\>|\<bar\>><rsub|g><rsup|\<chi\><rsub|K>>.G<rsub|\<chi\><rsub|K>>|)>|)><eq-number><label|Rg>>>|<row|<cell|R<rsub|g><around*|(|\<chi\><rsub|K>|)>>|<cell|=>|<cell|\<exists\><wide|\<alpha\>|\<bar\>><rsup|\<chi\><rsub|K>>.F<rsub|\<chi\><rsub|K>>>>|<row|<cell|P<rsub|g><around*|(|\<chi\><rsub|K><around*|(|\<delta\>,\<delta\><rprime|'>|)>|)>=P<rsub|g><around*|(|\<chi\><rsub|K><around*|(|\<delta\><rprime|'>|)>|)>>|<cell|=>|<cell|\<delta\><rprime|'><wide|=|\<dot\>><wide|\<tau\>|\<vect\>><rsub|\<varepsilon\><rsub|K>>>>|<row|<cell|F<rsub|\<chi\>><rprime|'>>|<cell|=>|<cell|F<rsub|\<chi\>><around*|[|\<varepsilon\><rsub|K><around*|(|<wide|\<tau\>|\<vect\>><rsub|old>|)>\<assign\>\<varepsilon\><rsub|K><around*|(|<wide|\<tau\>|\<vect\>><rsub|\<varepsilon\><rsub|K>>|)><around*|[|recover<around*|(|<wide|\<tau\>|\<vect\>><rsub|\<varepsilon\><rsub|K>>,<wide|\<tau\>|\<vect\>><rsub|old>|)>|]>|]>>>|<row|<cell|S<rsub|k><rprime|'>>|<cell|=>|<cell|<wide|\<exists\><wide|\<beta\>|\<bar\>><rsup|\<chi\>,k><around*|{|\<alpha\>\<in\>FV<around*|(|F<rprime|'><rsub|\<chi\>>|)><mid|\|>\<beta\><rsub|\<chi\>>\<less\><rsub|\<cal-Q\>>\<alpha\>|}>.F<rprime|'><rsub|\<chi\>><rsup|>|\<bar\>><eq-number><label|CaptureEscParams>>>|<row|<cell|\<cal-Q\><rprime|'>.\<wedge\><rsub|i><around*|(|D<rsub|i>\<Rightarrow\>C<rsub|i>|)>\<wedge\><rsub|j><around*|(|D<rsub|j><rsup|->\<Rightarrow\>\<b-F\>|)>>|<cell|=>|<cell|R<rsub|g><rsup|->P<rsub|g><rsup|+>S<rsub|k><rprime|'><around*|(|\<Phi\>\<wedge\><rsub|\<chi\><rsub|K>>U<rsub|\<chi\><rsub|K>>|)>>>|<row|<cell|\<exists\><wide|\<alpha\>|\<bar\>>.A<rsub|0>>|<cell|=>|<cell|Abd<around*|(|\<cal-Q\><rprime|'>,<wide|\<beta\>|\<bar\>>=<wide|\<beta\><rsub|\<chi\>><wide|\<beta\><rsup|>|\<bar\>><rsup|\<chi\>>|\<bar\>>,<wide|D<rsub|i>,C<rsub|i>|\<bar\>>|)><eq-number>>>|<row|<cell|A>|<cell|=>|<cell|A<rsub|0>\<wedge\><rsub|j>NegElim<around*|(|\<neg\>Simpl<around*|(|FV<around*|(|D<rsub|j><rsup|->|)>\\<wide|<wide|\<beta\>|\<bar\>><rsup|\<chi\>>|\<bar\>>.D<rsub|j><rsup|->|)>,A<rsub|0>,<wide|D<rsub|i>,C<rsub|i>|\<bar\>>|)>>>|<row|<cell|>|<cell|>|<cell|<with|mode|text|In
    later iterations, check negative constraints.><eq-number>>>|<row|<cell|<around*|(|\<cal-Q\><rsup|k+1>,A<rsub|res>,<wide|\<exists\><wide|\<alpha\>|\<bar\>><rsup|\<beta\><rsub|\<chi\>>>.A<rsub|\<beta\><rsub|\<chi\>>>|\<bar\>>|)>>|<cell|=>|<cell|Split<around*|(|\<cal-Q\><rprime|'>,<wide|\<alpha\>|\<bar\>>,A,<wide|\<beta\><rsub|\<chi\>><wide|\<beta\><rsup|>|\<bar\>><rsup|\<chi\>>|\<bar\>>|)>>>|<row|<cell|<wide|\<tau\>|\<vect\>><rsub|\<varepsilon\><rsub|K>><rprime|'>>|<cell|=>|<cell|<wide|FV<around*|(|<wide|A<rsub|res>|~><around*|(|<wide|\<tau\>|\<vect\>><rsub|\<varepsilon\><rsub|K>>|)>|)>|\<vect\>>>>|<row|<cell|R<rsub|k+1><around*|(|\<chi\><rsub|K>|)>>|<cell|=>|<cell|\<exists\><wide|\<beta\>|\<bar\>><rsup|\<chi\><rsub|K>,k><wide|<wide|\<alpha\>|\<bar\>><rsup|\<beta\><rsub|\<chi\><rsub|K>>>|\<bar\>><wide|\<alpha\>|\<bar\>><rsup|\<chi\><rsub|K>>\\FV<around*|(|<wide|\<tau\>|\<vect\>><rsub|\<varepsilon\><rsub|K>><rprime|'>|)>.\<delta\><rprime|'><wide|=|\<dot\>><wide|\<tau\>|\<vect\>><rsub|\<varepsilon\><rsub|K>><rprime|'>\<wedge\><wide|A<rsub|res>|~><around*|(|F<rsub|\<chi\><rsub|K>>\\\<delta\><rprime|'><wide|=|\<dot\>>\<ldots\>|)><next-line><with|mode|text|
    \ \ \ >\<wedge\><rsub|\<chi\><rsub|K>>A<rsub|\<beta\><rsub|\<chi\><rsub|K>>><around*|[|<wide|\<beta\><rsub|\<chi\><rsub|K>><wide|\<beta\><rsup|>|\<bar\>><rsup|\<beta\><rsub|\<chi\><rsub|K>>>|\<bar\>>\<assign\><wide|\<delta\><wide|\<beta\><rsup|>|\<bar\>><rsup|\<chi\><rsub|K>,k>|\<bar\>>|]><eq-number>>>|<row|<cell|A<rsub|K><rsup|d>>|<cell|=>|<cell|<around*|{|c\<in\>A<rsub|\<beta\><rsub|\<chi\><rsub|K>>><around*|[|<wide|\<beta\><rsub|\<chi\><rsub|K>><wide|\<beta\><rsup|>|\<bar\>><rsup|\<beta\><rsub|\<chi\><rsub|K>>>|\<bar\>>\<assign\><wide|\<delta\><wide|\<beta\><rsup|>|\<bar\>><rsup|\<chi\><rsub|K>,k>|\<bar\>>|]><mid|\|><next-line><with|mode|text|
    \ \ \ \ \ >FV<around*|(|c|)>\<subseteq\>FV<around*|(|\<rho\><around*|(|B<rsub|d><rsup|K>|)>|)>|}>>>|<row|<cell|\<exists\><wide|\<alpha\>|\<bar\>><rprime|'><rsub|K>.A<rprime|'><rsub|K>>|<cell|=>|<cell|Abd<around*|(|\<cal-Q\><rprime|'>,<wide|\<beta\><rsub|\<chi\>><wide|\<beta\><rsup|>|\<bar\>><rsup|\<chi\>>|\<bar\>>\\<wide|\<beta\><rsub|\<chi\><rsub|K>><wide|\<beta\><rsup|>|\<bar\>><rsup|\<chi\><rsub|K>>|\<bar\>>,<wide|\<rho\><around*|(|B<rsub|d><rsup|K>|)>,A<rsub|K><rsup|d>|\<bar\>>|)><eq-number>>>|<row|<cell|<around*|(|\<cal-Q\><rsup|k+1>,\<varnothing\>,<wide|\<exists\><wide|\<alpha\>|\<bar\>><rsup|\<beta\><rsub|\<chi\>>><rprime|'>.A<rsub|\<beta\><rsub|\<chi\>>><rprime|'>|\<bar\>>|)>>|<cell|=>|<cell|Split<around*|(|\<cal-Q\><rsup|k+1>,<wide|<wide|\<alpha\>|\<bar\>><rprime|'><rsub|K>|\<bar\>>,\<wedge\><rsub|K>A<rprime|'><rsub|K>,<wide|\<beta\><rsub|\<chi\>><wide|\<beta\><rsup|>|\<bar\>><rsup|\<chi\>>|\<bar\>>\\<wide|\<beta\><rsub|\<chi\><rsub|K>><wide|\<beta\><rsup|>|\<bar\>><rsup|\<chi\><rsub|K>>|\<bar\>>|)>>>|<row|<cell|S<rsub|k+1><around*|(|\<chi\>|)>>|<cell|=>|<cell|\<exists\><wide|\<beta\>|\<bar\>><rsup|\<chi\>,k>.Simpl<around*|(|\<exists\><wide|<wide|\<alpha\>|\<bar\>><rsup|\<beta\><rsub|\<chi\>>>|\<bar\>>.F<rsub|\<chi\>><rprime|'><next-line><with|mode|text|
    \ \ \ \ \ \ \ \ >\<wedge\>A<rsub|\<beta\><rsub|\<chi\>>><around*|[|<wide|\<beta\><rsub|\<chi\>><wide|\<beta\><rsup|>|\<bar\>><rsup|\<chi\>>|\<bar\>>\<assign\><wide|\<delta\><wide|\<beta\><rsup|>|\<bar\>><rsup|\<chi\>,k>|\<bar\>>|]>\<wedge\>A<rsub|\<beta\><rsub|\<chi\>>><rprime|'>|)><eq-number><label|Skp1>>>|<row|<cell|<with|mode|text|if>>|<cell|>|<cell|<around*|(|\<forall\>\<chi\>|)>S<rsub|k+1><around*|(|\<chi\>|)>\<subseteq\>S<rsub|k><around*|(|\<chi\>|)>,<eq-number>>>|<row|<cell|>|<cell|>|<cell|<around*|(|\<forall\>\<chi\><rsub|K>|)>R<rsub|k+1><around*|(|\<chi\><rsub|K>|)>=R<rsub|k><around*|(|\<chi\><rsub|K>|)>,>>|<row|<cell|>|<cell|>|<cell|<around*|(|\<forall\>\<beta\><rsub|\<chi\><rsub|K>>|)>A<rsub|\<beta\><rsub|\<chi\><rsub|K>>>=\<b-T\>,>>|<row|<cell|>|<cell|>|<cell|k\<gtr\>1>>|<row|<cell|<with|mode|text|then
    return>>|<cell|>|<cell|A<rsub|res>,S<rsub|k+1>,R<rsub|k+1>>>|<row|<cell|<with|mode|text|repeat>>|<cell|>|<cell|k\<assign\>k+1>>>>
  </eqnarray*>

  Note that <math|Split> returns <math|<wide|\<exists\><wide|\<alpha\>|\<bar\>><rsup|\<beta\><rsub|\<chi\>>>.A<rsub|\<beta\><rsub|\<chi\>>>|\<bar\>>>
  rather than <math|<wide|\<exists\><wide|\<alpha\>|\<bar\>><rsup|\<chi\>>.A<rsub|\<chi\>>|\<bar\>>>.
  This is because in case of existential type predicate variables
  <math|\<chi\><rsub|K>>, there can be multiple negative position occurrences
  <math|\<chi\><rsub|K><around*|(|\<beta\><rsub|\<chi\><rsub|K>>,\<cdummy\>|)>>
  with different <math|\<beta\><rsub|\<chi\><rsub|K>>> when the corresponding
  value is used in multiple <math|<text|<with|font-shape|condensed|<strong|let>>>
  \<ldots\> <text|<with|font-shape|condensed|<strong|in>>>> expressions. The
  variant of the algorithm to achieve completeness would compute all answers
  for variants of <math|Abd> and <math|Split> algorithms that return multiple
  answers. Unary predicate variables <math|\<chi\><around*|(|\<beta\><rsub|\<chi\>>|)>>
  can also have multiple negative occurrences in the normalized form, but
  always with the same argument <math|\<beta\><rsub|\<chi\>>>. The
  substitution <math|<around*|[|<wide|\<beta\><rsub|\<chi\><rsub|K>><wide|\<beta\><rsup|>|\<bar\>><rsup|\<beta\><rsub|\<chi\><rsub|K>>>|\<bar\>>\<assign\><wide|\<delta\><wide|\<beta\><rsup|>|\<bar\>><rsup|\<chi\><rsub|K>,k>|\<bar\>>|]>>
  replaces the instance parameters introduced in
  <math|\<chi\><rsub|K><around*|(|\<beta\><rsub|\<chi\><rsub|K>>,\<cdummy\>|)>>
  by the formal parameters used in <math|R<rsub|k><around*|(|\<chi\><rsub|K>|)>>.

  Even for a fixed <math|K>, the same branch
  <math|D<rsub|K><rsup|\<alpha\>>\<Rightarrow\>C<rsub|K><rsup|\<alpha\>>> can
  contribute to multiple disjuncts, with different
  <math|\<alpha\>=\<alpha\><rsub|3><rsup|i,K>>. Substitution
  <math|R<rsub|g><rsup|->> substitutes only negative occurrences of
  <math|\<chi\><rsub|K>>, i.e. it affects only the premises. Substitution
  <math|P<rsub|g><rsup|+>> substitutes only positive occurrences of
  <math|\<chi\><rsub|K>>, i.e. it affects only the conclusions.
  <math|P<rsub|g><rsup|+>> ensures that the parameter instances of the
  postcondition are connected with the argument variables. As a matter of
  implementation, the substitution <math|recover<around*|(|<wide|\<tau\>|\<vect\>><rsub|\<varepsilon\><rsub|K>>,<wide|\<tau\>|\<vect\>><rsub|old>|)>>
  is actually derived from the way the variables are freshened in step
  <reference|CaptureEscParams> above. Its effect is currently implemented as
  a substitution over the intermediate formula
  <math|F<rsub|\<chi\>><around*|[|\<varepsilon\><rsub|K><around*|(|<wide|\<tau\>|\<vect\>><rsub|old>|)>\<assign\>\<varepsilon\><rsub|K><around*|(|<wide|\<tau\>|\<vect\>><rsub|\<varepsilon\><rsub|K>>|)>|]>>.

  We start with <math|S<rsub|0>\<assign\><wide|\<b-T\>|\<bar\>>> and
  <math|R<rsub|0>\<assign\><wide|\<b-T\>|\<bar\>>>. <math|S<rsub|k>> grow in
  strength by definition. The constraint generalization parts
  <math|G<rsub|\<chi\><rsub|K>>> of <math|R<rsub|1>> and <math|R<rsub|2>> are
  computed from non-recusrive branches only. Starting from <math|R<rsub|2>>,
  <math|R<rsub|k>> are expected to decrease in strength, but monotonicity is
  not guaranteed because of contributions from abduction: mostly in form of
  <math|A<rsub|\<beta\><rsub|\<chi\><rsub|K>>>>, but also from stronger
  premises due to <math|S<rsub|k>>. We remove non-term-sort atoms containing
  containing outer-scope parameters from <math|S<rsub|2>>, to enable
  considering a different solution when new facts about outer-scope
  parameters propagate.

  <math|Connected<around*|(|\<alpha\>,G|)>> is the connected component of
  hypergraph <math|G> containing node <math|\<alpha\>>, where nodes are
  variables <math|FV<around*|(|G|)>> and hyperedges are atoms
  <math|c\<in\>G>. <math|Connected<rsub|0><around*|(|\<delta\>,<around*|(|<wide|\<alpha\>|\<bar\>>,G|)>|)>>
  additionally removes atoms <math|c:FV<around*|(|c|)>#\<delta\><wide|\<alpha\>|\<bar\>>>.
  In initial iterations, when the branches
  <math|D<rsub|K><rsup|\<alpha\>>\<Rightarrow\>C<rsub|K><rsup|\<alpha\>>> are
  selected from non-recursive branches only, we include a connected atom only
  if it is satisfiable in all branches. <math|H<around*|(|R<rsub|k>,R<rsub|k+1>|)>>
  is a convergence improving heuristic, with
  <math|H<around*|(|R<rsub|k>,R<rsub|k+1>|)>=\<rho\><around*|(|R<rsub|g>|)>>
  for early iterations and ``roughly'' <math|H<around*|(|R<rsub|k>,R<rsub|g>|)>=R<rsub|k>\<cap\>\<rho\><around*|(|R<rsub|g>|)>>
  later. The substitution <math|H>, also computed by the function <math|H>,
  is a renaming that replaces the variables introduced by constraint
  generalization in the current iteration, by the corresponding variables
  introduced by constraint generalization in the previous iteration.

  The use sites of definitions with postconditions can introduce requirements
  <math|A<rsub|\<beta\><rsub|\<chi\><rsub|K>>>> on postconditions. The
  inferred postconditions can only meet those requirements which are
  guaranteed by all defining cases. We use abduction again to strengthen the
  preconditions, so that the postconditions meet the requirements. Abduction
  is applied directly to the constraint branches preprocessed by constraint
  generalization, so that the required postconditions will follow in the next
  iteration.

  The condition <math|<around*|(|\<forall\>\<beta\><rsub|\<chi\><rsub|K>>|)>A<rsub|\<beta\><rsub|\<chi\><rsub|K>>>=\<b-T\>>
  is required for correctness of returned solution. Fixpoint of
  postconditions <math|R<rsub|k><around*|(|\<chi\><rsub|K>|)>> is not a
  sufficient stopping condition, because it does not imply
  <math|A<rsub|\<beta\><rsub|\<chi\><rsub|K>>>=\<b-T\>>, the same
  <math|A<rsub|\<beta\><rsub|\<chi\><rsub|K>>>\<neq\>\<b-T\>> may be
  introduced in consecutive iterations. This is not the case for invariants,
  where <math|S<rsub|k><around*|(|\<chi\>|)>> and
  <math|S<rsub|k+1><around*|(|\<chi\>|)>> differ by the portion
  <math|A<rsub|\<beta\><rsub|\<chi\>>>> of abduction answer.

  We introduced the <verbatim|assert false> construct into the programming
  language to indicate that a branch of code should not be reached. Type
  inference generates for it the logical connective <math|\<b-F\>>
  (falsehood). We partition the implication branches
  <math|D<rsub|i>,C<rsub|i>> into <math|<around*|{|D<rsub|i>,C<rsub|i><mid|\|>\<b-F\>\<nin\>C<rsub|i>|}>>
  which are fed to the algorithm and <math|<around*|{|D<rsub|j><rsup|->|}>=<around*|{|D<rsub|i><mid|\|>\<b-F\>\<in\>C<rsub|i>|}>>.
  After the main algorithm ends we check that for each
  <math|D<rsub|j><rsup|->>, \ <math|S<rsub|k><around*|(|D<rsub|i>|)>> fails.
  Optionally, but by default, we perform the check in each iteration,
  starting from the third iteration, i.e. <math|k\<gtr\>1>. Turning this
  option <em|on> gives a way to express negative constraints for the term
  domain. The option should be turned <em|off> when a single iteration (plus
  fallback backtracking described below) is insufficient to solve for the
  invariants. Moreover, for domains with negation elimination, i.e. the
  numerical domain, we incorporate negative constraints as described in
  section <reference|NegElim>. The corresponding computation is
  <math|A<rsub|0>\<wedge\><rsub|j>NegElim<around*|(|\<neg\>Simpl<around*|(|FV<around*|(|D<rsub|j><rsup|->|)>\\<wide|<wide|\<beta\>|\<bar\>><rsup|\<chi\>>|\<bar\>>.D<rsub|j><rsup|->|)>,<wide|D<rsub|i>,C<rsub|i>|\<bar\>>|)>>
  in the specification of the main algorithm. The simplification reduces the
  number of atoms in the formula and keeps those that are most relevant to
  finding invariants and postconditions. For convenience, negation
  elimination is called from the function that computes the abduction answer.

  We implement backtracking using a tabu-search-like discard list. When
  abduction raises an exception: for example contradiction arises in the
  branches <math|S<rsub|k><around*|(|\<Phi\>|)>> passed to it, or it cannot
  find an answer and raises <verbatim|Suspect> with information on potential
  problem, we fall-back to step <math|k-1>. Similarly, with checking for
  negative constraints <em|on>, when the check of negative branches
  <math|D<rsub|i>\<in\>\<Phi\><rsub|\<b-F\>>>,
  \ <math|\<cal-M\>\<nvDash\>\<exists\>FV<around*|(|S<rsub|k><around*|(|D<rsub|i>|)>|)>.S<rsub|k><around*|(|D<rsub|i>|)>>
  fails. In step <math|k-1>, we maintain a discard list of different answers
  found not to work in this step and previous steps: initially empty, after
  fall-back we add there the latest partial solution. We redo step <math|k-1>
  starting from <math|S<rsub|k-1><around*|(|\<Phi\>|)>>. Infinite loop is
  avoided because answers already attempted are discarded. When step
  <math|k-1> cannot find a new partial solution, we fall back to step
  <math|k-2>, etc. We store discard lists for distinct sorts separately and
  we only add to the discard list of the sort that caused fallback.
  Unfortunately this means a slight loss of completeness, as an error in
  another sort might be due to bad choice in the sort of types. The loss is
  ``slight'' because of the dissociation step described previously. Moreover,
  the sort information from checking negative branches is likewise only
  approximate.

  <subsection|Stages of Iteration>

  Changes in the algorithm between iterations were mentioned above but not
  clearly exposed. We divide iterations into multiple stages, demarcated by
  parameters <math|j<rsub|k>> we now describe.

  <\enumerate>
    <item><math|j<rsub|0>> is when inferring any postconditions starts; we
    use the initial iteration to infer the shape of types using abduction.\ 

    <item><math|j<rsub|1>> is when inferring numerical postconditions starts.

    <item><math|j<rsub|2>> is when using all branches of the constraint in
    inference starts; before <math|j<rsub|2>>, we only use the branches of
    the constraint that do not contain requirements derived from recursive
    calls. If we use all branches too early, we suffer from missing
    information.

    <item><math|j<rsub|3>> is when second-phase abduction, to enrich
    preconditions based on postconditions, starts.

    <item><math|j<rsub|4>> is when any forms of guessing in constraint
    generation should end; we have not yet implemented any such guessing
    mechanisms.

    <item><math|j<rsub|5>> is when convergence of postconditions is enforced;
    from this step onward, a solution to postconditions in an iteration is
    truncated to contain only atoms matching atoms from the previous
    iteration.

    <item><math|j<rsub|6>> is the last iteration; if the fixpoint is not
    reached, we signal an error <em|``Answers do not converge''>.
  </enumerate>

  Default settings are <math|<around*|[|j<rsub|0>;j<rsub|1>;j<rsub|2>;j<rsub|3>;j<rsub|4>;j<rsub|5>;j<rsub|6>|]>=<around*|[|1;1;2;3;4;8;11|]>>
  where the initial iteration has index 0. In a single iteration, constraint
  generalization precedes abduction.

  When existential types are used, the expected number of iterations is
  <math|k=5> (six iterations), because the last iteration needs to verify
  that the last-but-one iteration has found the correct solution. The minimal
  number of iterations is <math|k=2> (three iterations), so that all branches
  are considered.

  <subsection|Implementation Details><label|Details>

  We represent <math|<wide|\<alpha\>|\<vect\>>> as a tuple type rather than
  as a function type. We modify the quantifier <math|\<cal-Q\>> imperatively,
  because it mostly grows monotonically, and when variables are dropped they
  do not conflict with fresh variables generated later.

  The code that selects <math|<wide|A<rsub|\<chi\>><rsup|+>|\<bar\>>> by
  <math|\<wedge\><rsub|\<chi\>><around*|(|A<rsub|\<chi\>><rsup|+>\<subset\>A<rsub|\<chi\>><rsup|1>|)>
  and \<cal-M\>\<vDash\>\<cal-Q\>.A\<setminus\>\<cup\><rsub|\<chi\>>A<rsub|\<chi\>><rsup|+>>
  is an incremental validity checker. It starts with
  <math|A\<setminus\>\<cup\><rsub|\<chi\>>A<rsub|\<chi\>><rsup|1>> and tries
  to add as many atoms <math|c\<in\>\<cup\><rsub|\<chi\>>A<rsub|\<chi\>><rsup|1>>
  as possible to what in effect becomes <math|A<rsub|res>>.

  We count the number of iterations of the main loop, a fallback decreases
  the iteration number to the previous value. The main loop decides whether
  multisort abduction should dissociate alien subterms -- in the first
  iteration of the loop -- or should perform abductions for other sorts -- in
  subsequent iteration. See discussion in subsection
  <reference|AlienSubterms>. In the first two iterations, we remove branches
  that contain unary predicate variables in the conclusion (or binary
  predicate variables in the premise, keeping only non-recursive branches),
  as discussed at the end of subsection <reference|SCAlinear> and beginning
  of subsection <reference|NumConv>. As discussed in subsection
  <reference|NumConv>, starting from iteration <math|k<rsub|3>>, we enforce
  convergence on solutions for binary predicate variables.

  Computing abduction is the ``axis'' of the main loop. If anything fails,
  the previous abduction answer is the culprit. We add the previous answer to
  the discard list and retry, without incrementing the iteration number. If
  abduction and splitting succeeds, we reset the discard list and increment
  the iteration number. We use recursion for backtracking, instead of making
  <verbatim|loop> tail-recursive.

  <section|Generating OCaml Source and Interface Code>

  We have a single basis from which to generate all generated output files:
  <verbatim|.gadti>, <verbatim|.ml> -- <verbatim|annot_item>. It contains a
  superset of information in <verbatim|struct_item>: type scheme annotations
  on introduced names, and source code annotated with type schemes at
  recursive definition nodes. We use <verbatim|type a.> syntax instead of
  <verbatim|'a.> syntax because the former supports inference for GADTs in
  OCaml. A benefit of the nicer <verbatim|type a.> syntax is that nested type
  schemes can have free variables, which will be correctly captured by the
  outer type scheme. For completeness we sometimes need to annotate all
  <verbatim|function> nodes with types. To avoid clutter, we start by only
  annotating <verbatim|let rec> nodes, and in case <verbatim|ocamlc -c> fails
  on generated code, we re-annotate by putting type schemes on <verbatim|let
  rec> nodes and types on <verbatim|function> nodes. If need arises,
  <verbatim|let-in> node annotations can also be introduced in this fallback
  -- we provide an option to annotate the definitions on <verbatim|let-in>
  nodes. Type annotations are optional because they introduce a slight burden
  on the solver -- the corresponding variables cannot be removed by the
  initial simplification of the constraints. <verbatim|let-in> node
  annotations are more burdensome than <verbatim|function> node annotations.

  In the signature declarations for existential types, we replace existential
  identifiers with regular indentifiers of constructors, to get informative
  output for printing the various result files. We print constraint formulas
  and alien subterms in the original InvarGenT syntax, commented out.

  The types <verbatim|Int>, <verbatim|Num>, <verbatim|Bool> and
  <verbatim|String> should be considered built-in. <verbatim|Int>,
  <verbatim|Bool> and <verbatim|String> follow the general scheme of
  exporting a datatype constructor with the same name, only lower-case.
  However, numerals <verbatim|0>, <verbatim|1>, ... are always type-checked
  as <verbatim|Num 0>, <verbatim|Num 1>... A parameter <verbatim|-num_is>
  decides the type alias definition added in the generated code:
  <verbatim|-num_is bar> adds <verbatim|type num = bar> in front of an
  <verbatim|.ml> file, by default <verbatim|int>. Numerals are exported as
  integers passed to a <verbatim|bar_of_int> function. The variant
  <verbatim|-num_is_mod> exports numerals by passing to a
  <verbatim|Bar.of_int> function. Special treatment for <verbatim|Bool>
  amounts to exporting <verbatim|True> and <verbatim|False> as
  <verbatim|true> and <verbatim|false>, unlike other constants. In addition,
  pattern matching <verbatim|match><math|\<ldots\>><verbatim| with True
  -\<gtr\>><math|\<ldots\>><verbatim| \| False -\<gtr\>><math|\<ldots\>>,
  i.e. the corresponding beta-redex, is exported as the
  <verbatim|if><math|\<ldots\>><verbatim| then><math|\<ldots\>><verbatim|
  else><math|\<ldots\>> expression.

  In declarations which have concrete syntax starting with the word
  <verbatim|external>, we provide names assumed to have given type scheme.
  The syntax has two variants, differing in the way the declaration is
  exported. It can be either an <verbatim|external> declaration in OCaml,
  which is the binding mechanism of the <em|foreign function interface>. But
  in the InvarGenT form <verbatim|external let>, the declaration provides an
  OCaml definition, which is exported as the toplevel <verbatim|let>
  definition of OCaml. It has the benefit that the OCaml compiler will verify
  this definition, since InvarGenT calls <verbatim|ocamlc -c> to verify the
  exported code.<new-page>

  <appendix|Source Code of Examples><label|ExamplesCode>

  Subsection titles start with ``Function'' for examples from Tables
  <reference|Experiments> and <reference|ExperimentsNum>, and ``Program'' for
  examples from Table <reference|ExperimentsBounds>.

  <section|Incompleteness Example for <verbatim|OutsideIn>: Function
  <verbatim|rx>>

  Example from <cite|OutsideIn>, described on page 50. Source file
  <em|non_outsidein_rx.gadt>:

  <\code>
    datatype R : type

    datacons RBool : R Bool

    external let fortytwo : Int = "42"

    \;

    let rx = function RBool -\> fortytwo
  </code>

  Value items from <em|non_outsidein_rx.gadti.target>:

  <\code>
    val rx : <math|\<forall\>>a. R a <math|\<rightarrow\>> Int
  </code>

  <section|Pointwise Examples>

  These are the longer examples from <cite|PointwiseGADTs> within the scope
  of algorithm <math|\<cal-P\>>.

  <subsection|Function <verbatim|rotate>>

  Example from <cite|PracticalGADTsInfer>, described on pages 193-194. Source
  file <em|pointwise_rbtree_rotate.gadt>:

  <\code>
    datatype Z

    datatype S : type

    \;

    datatype RoB : type * type

    datatype Black

    datatype Red

    datacons Leaf : RoB (Black, Z)

    datacons RNode : <math|\<forall\>>a. RoB (Black, a) * Int * RoB (Black,
    a) <math|\<longrightarrow\>> RoB (Red, a)

    datacons BNode :

    \ \ <math|\<forall\>>a, b, c. RoB (a, c) * Int * RoB (b, c)
    <math|\<longrightarrow\>> RoB (Black, S c)

    \;

    datatype Dir

    datacons LeftD : Dir

    datacons RightD : Dir

    \;

    let rotate = fun dir1 p_e sib dir2 g_e uncle -\> function

    \| RNode (x, e, y) -\>

    \ \ (match dir1, dir2 with

    \ \ \| RightD, RightD -\> BNode (RNode (x, e, y), p_e, RNode (sib, g_e,
    uncle))

    \ \ \| RightD, LeftD -\> BNode (RNode (uncle, g_e, x), e, RNode (y, p_e,
    sib))

    \ \ \| LeftD, RightD -\> BNode (RNode (sib, p_e, x), e, RNode (y, g_e,
    uncle))

    \ \ \| LeftD, LeftD -\> BNode (RNode (uncle, g_e, sib), p_e, RNode (x, e,
    y)))

    \| BNode (_, _, _) -\> assert false
  </code>

  Value items from <em|pointwise_rbtree_rotate.gadti.target>:

  <\code>
    val rotate :

    \ \ \ <math|\<forall\>>a.

    \ \ \ Dir <math|\<rightarrow\>> Int <math|\<rightarrow\>> RoB (Black, a)
    <math|\<rightarrow\>> Dir <math|\<rightarrow\>> Int <math|\<rightarrow\>>
    RoB (Black, a) <math|\<rightarrow\>>

    \ \ \ \ \ RoB (Red, a) <math|\<rightarrow\>> RoB (Black, S a)
  </code>

  <subsection|Function <verbatim|zip2>: <math|N>-way <verbatim|zip_with>>

  Example from <cite|PracticalGADTsInfer>, provided on page 206. The
  definition of <verbatim|z2> is <math|\<eta\>>-expanded here to fit the
  call-by-value semantics of <name|InvarGenT>. Source file
  <em|pointwise_zip2.gadt>:

  <\code>
    datatype List : type

    datacons N : <math|\<forall\>>a. List a

    datacons C : <math|\<forall\>>a. a * List a <math|\<longrightarrow\>>
    List a

    \;

    datatype Zip2 : type * type

    datacons Zero2 : <math|\<forall\>>a. Zip2 (a, List a)

    datacons Succ2 :

    \ \ <math|\<forall\>>a, b, c. Zip2 (a, b) <math|\<longrightarrow\>> Zip2
    ((c <math|\<rightarrow\>> a), (List c <math|\<rightarrow\>> b))

    \;

    let zip2 =

    \ \ let rec zipZ = function

    \ \ \ \ \| Zero2 -\> N

    \ \ \ \ \| Succ2 n -\> fun _ -\> zipZ n in

    \ \ let rec zipS = fun f r -\> function

    \ \ \ \ \| Zero2 -\> C (f, r)

    \ \ \ \ \| Succ2 n -\> function

    \ \ \ \ \ \ \| N -\> zipZ n

    \ \ \ \ \ \ \| C (z, zs) -\> zipS (f z) (r zs) n in

    \ \ let rec z2 = fun n f -\> zipS f (z2 n f) n in

    \ \ z2
  </code>

  Value items from <em|pointwise_zip2.gadti.target>:

  <\code>
    val zip2 : <math|\<forall\>>a, b. Zip2 (b, a) <math|\<rightarrow\>> b
    <math|\<rightarrow\>> a
  </code>

  <subsection|Function <verbatim|rotl>>

  Example from <cite|PracticalGADTsInfer>, described on pages 198-199. Source
  file <em|pointwise_avl_rotl.gadt>:

  <\code>
    datatype Z

    datatype S : type

    datatype AVL : type

    datacons Tip : AVL Z

    datacons LNode : <math|\<forall\>>a. AVL a * Int * AVL (S a)
    <math|\<longrightarrow\>> AVL (S (S a))

    datacons SNode : <math|\<forall\>>a. AVL a * Int * AVL a
    <math|\<longrightarrow\>> AVL (S a)

    datacons MNode : <math|\<forall\>>a. AVL (S a) * Int * AVL a
    <math|\<longrightarrow\>> AVL (S (S a))

    \;

    datatype Choice : type * type

    datacons L : <math|\<forall\>>a, b. a <math|\<longrightarrow\>> Choice
    (a, b)

    datacons R : <math|\<forall\>>a, b. b <math|\<longrightarrow\>> Choice
    (a, b)

    \;

    let rotl = fun u v -\> function

    \ \ \| Tip -\> assert false

    \ \ \| SNode (a, x, b) -\> R (MNode (LNode (u, v, a), x, b))

    \ \ \| LNode (a, x, b) -\> L (SNode (SNode (u, v, a), x, b))

    \ \ \| MNode (k, y, c) -\>

    \ \ \ \ (match k with

    \ \ \ \ \ \ \| SNode (a, x, b) -\> L (SNode (SNode (u, v, a), x, SNode
    (b, y, c)))

    \ \ \ \ \ \ \| LNode (a, x, b) -\> L (SNode (MNode (u, v, a), x, SNode
    (b, y, c)))

    \ \ \ \ \ \ \| MNode (a, x, b) -\> L (SNode (SNode (u, v, a), x, LNode
    (b, y, c))))
  </code>

  Value items from <em|pointwise_avl_rotl.gadti.target>:

  <\code>
    val rotl :

    \ \ \ <math|\<forall\>>a.

    \ \ \ AVL a <math|\<rightarrow\>> Int <math|\<rightarrow\>> AVL (S (S a))
    <math|\<rightarrow\>>

    \ \ \ \ \ Choice (AVL (S (S a)), AVL (S (S (S a))))
  </code>

  <subsection|Function <verbatim|ins>>

  Example from <cite|PracticalGADTsInfer>, provided on page 209. Source file
  <em|pointwise_avl_ins.gadt>:

  <\code>
    datatype Z

    datatype S : type

    datatype AVL : type

    datacons Tip : AVL Z

    datacons LNode : <math|\<forall\>>a. AVL a * Int * AVL (S a)
    <math|\<longrightarrow\>> AVL (S (S a))

    datacons SNode : <math|\<forall\>>a. AVL a * Int * AVL a
    <math|\<longrightarrow\>> AVL (S a)

    datacons MNode : <math|\<forall\>>a. AVL (S a) * Int * AVL a
    <math|\<longrightarrow\>> AVL (S (S a))

    \;

    datatype Choice : type * type

    datacons L : <math|\<forall\>>a, b. a <math|\<longrightarrow\>> Choice
    (a, b)

    datacons R : <math|\<forall\>>a, b. b <math|\<longrightarrow\>> Choice
    (a, b)

    \;

    datatype LinOrder

    datacons LT : LinOrder

    datacons EQ : LinOrder

    datacons GT : LinOrder

    external let compare : <math|\<forall\>>a. a <math|\<rightarrow\>> a
    <math|\<rightarrow\>> LinOrder =

    \ \ "fun x y -\> let c=Pervasives.compare x y in

    \ \ \ \ \ \ \ \ \ \ \ \ \ \ if c\<less\>0 then LT else if c=0 then EQ
    else GT"

    \;

    external rotl :

    \ \ <math|\<forall\>>a. AVL a <math|\<rightarrow\>> Int
    <math|\<rightarrow\>> AVL (S (S a)) <math|\<rightarrow\>>

    \ \ \ \ Choice (AVL (S (S a)), AVL (S (S (S a))))

    \;

    external rotr :

    \ \ <math|\<forall\>>a. AVL (S (S a)) <math|\<rightarrow\>> Int
    <math|\<rightarrow\>> AVL a <math|\<rightarrow\>>

    \ \ \ \ Choice (AVL (S (S a)), AVL (S (S (S a))))

    \;

    let rec ins = fun i -\> function

    \ \ \| Tip -\> R (SNode (Tip, i, Tip))

    \ \ \| SNode (a, x, b) as t -\>

    \ \ \ \ (match compare i x with

    \ \ \ \ \ \ \| EQ -\> L t

    \ \ \ \ \ \ \| LT -\>

    \ \ \ \ \ \ \ \ (match ins i a with

    \ \ \ \ \ \ \ \ \ \ \| L a -\> L (SNode (a, x, b))

    \ \ \ \ \ \ \ \ \ \ \| R a -\> R (MNode (a, x, b)))

    \ \ \ \ \ \ \| GT -\>

    \ \ \ \ \ \ \ \ (match ins i b with

    \ \ \ \ \ \ \ \ \ \ \| L b -\> L (SNode (a, x, b))

    \ \ \ \ \ \ \ \ \ \ \| R b -\> R (LNode (a, x, b))))

    \ \ \| LNode (a, x, b) as t -\>

    \ \ \ \ (match compare i x with

    \ \ \ \ \ \ \| EQ -\> L t

    \ \ \ \ \ \ \| LT -\>

    \ \ \ \ \ \ \ \ (match ins i a with

    \ \ \ \ \ \ \ \ \ \ \| L a -\> L (LNode (a, x, b))

    \ \ \ \ \ \ \ \ \ \ \| R a -\> L (SNode (a, x, b)))

    \ \ \ \ \ \ \| GT -\>

    \ \ \ \ \ \ \ \ (match ins i b with

    \ \ \ \ \ \ \ \ \ \ \| L b -\> L (LNode (a, x, b))

    \ \ \ \ \ \ \ \ \ \ \| R b -\> rotl a x b))

    \ \ \| MNode (a, x, b) as t -\>

    \ \ \ \ (match compare i x with

    \ \ \ \ \ \ \| EQ -\> L t

    \ \ \ \ \ \ \| LT -\>

    \ \ \ \ \ \ \ \ (match ins i a with

    \ \ \ \ \ \ \ \ \ \ \| L a -\> L (MNode (a, x, b))

    \ \ \ \ \ \ \ \ \ \ \| R a -\> rotr a x b)

    \ \ \ \ \ \ \| GT -\>

    \ \ \ \ \ \ \ \ (match ins i b with

    \ \ \ \ \ \ \ \ \ \ \| L b -\> L (MNode (a, x, b))

    \ \ \ \ \ \ \ \ \ \ \| R b -\> L (SNode (a, x, b))))
  </code>

  Value items from <em|pointwise_avl_ins.gadti.target>:

  <\code>
    val ins : <math|\<forall\>>a. Int <math|\<rightarrow\>> AVL a
    <math|\<rightarrow\>> Choice (AVL a, AVL (S a))
  </code>

  <subsection|Function <verbatim|extract>>

  Example from <cite|PracticalGADTsInfer>, provided on page 207. Source file
  <em|pointwise_extract.gadt>:

  <\code>
    datatype List : type

    datacons N : <math|\<forall\>>a. List a

    datacons C : <math|\<forall\>>a. a * List a <math|\<longrightarrow\>>
    List a

    \;

    datatype Nd

    datatype Fk : type * type

    \;

    datatype Tree : type * type

    datacons End : <math|\<forall\>>a. a <math|\<longrightarrow\>> Tree (Nd,
    a)

    datacons Fork : <math|\<forall\>>a, b, c. Tree (a, c) * Tree (b, c)
    <math|\<longrightarrow\>> Tree (Fk (a, b), c)

    \;

    datatype Path : type

    datacons Here : Path Nd

    datacons ForkL : <math|\<forall\>>a, b. Path a <math|\<longrightarrow\>>
    Path (Fk (a, b))

    datacons ForkR : <math|\<forall\>>a, b. Path b <math|\<longrightarrow\>>
    Path (Fk (a, b))

    \;

    external append : <math|\<forall\>>a. List a <math|\<rightarrow\>> List a
    <math|\<rightarrow\>> List a

    external map : <math|\<forall\>>a, b. (a <math|\<rightarrow\>> b)
    <math|\<rightarrow\>> List a <math|\<rightarrow\>> List b

    \;

    let rec find f = function

    \ \ \| End m -\> if f m then C (Here, N) else N

    \ \ \| Fork (x, y) -\> append (map (fun y -\> ForkL y) (find f x))

    \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ (map (fun y -\> ForkR
    y) (find f y))

    \;

    let rec extract = fun p t -\>

    \ \ match p with

    \ \ \ \ \| Here -\> (match t with End m -\> m \| Fork (_, _) -\> assert
    false)

    \ \ \ \ \| ForkL p1 -\> (match t with Fork (x, y) -\> extract p1 x)

    \ \ \ \ \| ForkR p1 -\> (match t with Fork (x, y) -\> extract p1 y)
  </code>

  Value items from <em|pointwise_extract.gadti.target>:

  <\code>
    val find : <math|\<forall\>>a, b. (a <math|\<rightarrow\>> Bool)
    <math|\<rightarrow\>> Tree (b, a) <math|\<rightarrow\>> List (Path b)

    \;

    val extract : <math|\<forall\>>a, b. Path b <math|\<rightarrow\>> Tree
    (b, a) <math|\<rightarrow\>> a
  </code>

  <subsection|Function <verbatim|run_state>>

  Example from <cite|PracticalGADTsInfer>, provided on page 208. Source file
  <em|pointwise_run_state.gadt>:

  <\code>
    datatype State : type * type

    datacons Bind :

    \ \ <math|\<forall\>>a, b, s. State (s, a) * (a <math|\<rightarrow\>>
    State (s, b)) <math|\<longrightarrow\>> State (s, b)

    datacons Return : <math|\<forall\>>a, s. a <math|\<longrightarrow\>>
    State (s, a)

    datacons Get : <math|\<forall\>>s. State (s, s)

    datacons Put : <math|\<forall\>>s. s <math|\<longrightarrow\>> State (s,
    ())

    \;

    let rec run_state = fun s -\> function

    \ \ \| Return a -\> (s, a)

    \ \ \| Get -\> (s, s)

    \ \ \| Put u -\> (u, ())

    \ \ \| Bind (m, k) -\>

    \ \ \ \ let s1, a1 = run_state s m in

    \ \ \ \ run_state s1 (k a1)
  </code>

  Value items from <em|pointwise_run_state.gadti.target>:

  <\code>
    val run_state : <math|\<forall\>>a, b. a <math|\<rightarrow\>> State (a,
    b) <math|\<rightarrow\>> (a, b)
  </code>

  <section|Non-Pointwise Examples>

  These are the examples from <cite|PointwiseGADTs> falling outside the scope
  of algorithm <math|\<cal-P\>>.

  <subsection|Function <verbatim|joint>>

  Example from <cite|PracticalGADTsInfer>, described on page 86. Source file
  <em|non_pointwise_split.gadt>:

  <\code>
    datatype Split : type * type

    datacons Whole : Split (Int, Int)

    datacons Parts : <math|\<forall\>>a, b. Split ((Int, a), (b, Bool))

    external let seven : Int = "7"

    external let three : Int = "3"

    \;

    let joint = function

    \ \ \| Whole -\<gtr\> seven

    \ \ \| Parts -\<gtr\> three, True
  </code>

  Value items from <em|non_pointwise_split.gadti.target>:

  <\code>
    val joint : <math|\<forall\>>a. Split (a, a) <math|\<rightarrow\>> a
  </code>

  <subsection|Function <verbatim|rotr>>

  Example from <cite|PracticalGADTsInfer>, described on page 88. Source file
  <em|non_pointwise_avl.gadt>:

  <\code>
    (** Normally we would use [num], but this is a stress test for [type]. *)

    datatype Z

    datatype S : type

    datatype Balance : type * type * type

    datacons Less : <math|\<forall\>>a. Balance (a, S a, S a)

    datacons Same : <math|\<forall\>>a. Balance (a, a, a)

    datacons More : <math|\<forall\>>a. Balance (S a, a, S a)

    datatype AVL : type

    datacons Leaf : AVL Z

    datacons Node :

    \ \ <math|\<forall\>>a, b, c. Balance (a, b, c) * AVL a * Int * AVL b
    <math|\<longrightarrow\>> AVL (S c)

    \;

    datatype Choice : type * type

    datacons Left : <math|\<forall\>>a, b. a <math|\<longrightarrow\>> Choice
    (a, b)

    datacons Right : <math|\<forall\>>a, b. b <math|\<longrightarrow\>>
    Choice (a, b)

    \;

    let rotr = fun z d -\<gtr\> function

    \ \ \| Leaf -\<gtr\> assert false

    \ \ \| Node (Less, a, x, Leaf) -\<gtr\> assert false

    \ \ \| Node (Same, a, x, (Node (_,_,_,_) as b)) -\<gtr\>

    \ \ \ \ Right (Node (Less, a, x, Node (More, b, z, d)))

    \ \ \| Node (More, a, x, (Node (_,_,_,_) as b)) -\<gtr\>

    \ \ \ \ Left (Node (Same, a, x, Node (Same, b, z, d)))

    \ \ \| Node (Less, a, x, Node (Same, b, y, c)) -\<gtr\>

    \ \ \ \ Left (Node (Same, Node (Same, a, x, b), y, Node (Same, c, z, d)))

    \ \ \| Node (Less, a, x, Node (Less, b, y, c)) -\<gtr\>

    \ \ \ \ Left (Node (Same, Node (More, a, x, b), y, Node (Same, c, z, d)))

    \ \ \| Node (Less, a, x, Node (More, b, y, c)) -\<gtr\>

    \ \ \ \ Left (Node (Same, Node (Same, a, x, b), y, Node (Less, c, z, d)))
  </code>

  Value items from <em|non_pointwise_avl.gadti.target>:

  <\code>
    val rotr :

    \ \ \ <math|\<forall\>>a.

    \ \ \ Int <math|\<rightarrow\>> AVL a <math|\<rightarrow\>> AVL (S (S a))
    <math|\<rightarrow\>>

    \ \ \ \ \ Choice (AVL (S (S a)), AVL (S (S (S a))))
  </code>

  <subsection|Function <verbatim|delmin>>

  Example from <cite|PracticalGADTsInfer>, described on pages 212-213. Source
  file <em|non_pointwise_avl_delmin.gadt>:

  <\code>
    (** Normally we would use [num], but this is a stress test for [type]. *)

    datatype Z

    datatype S : type

    (** This datatype definition is modified to make type inference for

    \ \ \ \ rotr, rotl, ins functions pointwise. *)

    datatype AVL : type

    datacons Tip : AVL Z

    datacons LNode : <math|\<forall\>>a. AVL a * Int * AVL (S a)
    <math|\<longrightarrow\>> AVL (S (S a))

    datacons SNode : <math|\<forall\>>a. AVL a * Int * AVL a
    <math|\<longrightarrow\>> AVL (S a)

    datacons MNode : <math|\<forall\>>a. AVL (S a) * Int * AVL a
    <math|\<longrightarrow\>> AVL (S (S a))

    \;

    datatype Choice : type * type

    datacons L : <math|\<forall\>>a, b. a <math|\<longrightarrow\>> Choice
    (a, b)

    datacons R : <math|\<forall\>>a, b. b <math|\<longrightarrow\>> Choice
    (a, b)

    \;

    datatype Zero : type

    datacons IsZ : Zero Z

    datacons NotZ : <math|\<forall\>>a. Zero (S a)

    \;

    external rotl :

    \ \ <math|\<forall\>>a. AVL a <math|\<rightarrow\>> Int
    <math|\<rightarrow\>> AVL (S (S a)) <math|\<rightarrow\>> Choice (AVL (S
    (S a)),

    \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ AVL
    (S (S (S a))))

    \;

    external rotr :

    \ \ <math|\<forall\>>a. AVL (S (S a)) <math|\<rightarrow\>> Int
    <math|\<rightarrow\>> AVL a <math|\<rightarrow\>> Choice (AVL (S (S a)),

    \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ AVL
    (S (S (S a))))

    \;

    let empty = function

    \ \ \| Tip -\> IsZ

    \ \ \| LNode (_, _, _) -\> NotZ

    \ \ \| SNode (_, _, _) -\> NotZ

    \ \ \| MNode (_, _, _) -\> NotZ

    \;

    let rec delmin = function

    \ \ \| LNode (a, x, b) -\>

    \ \ \ \ (match empty a with

    \ \ \ \ \ \ \| IsZ -\> x, L b

    \ \ \ \ \ \ \| NotZ -\>

    \ \ \ \ \ \ \ \ (match delmin a with

    \ \ \ \ \ \ \ \ \ \ y, k -\>

    \ \ \ \ \ \ \ \ \ \ (match k with

    \ \ \ \ \ \ \ \ \ \ \ \ \| L a -\> y, rotl a x b

    \ \ \ \ \ \ \ \ \ \ \ \ \| R a -\> y, R (LNode (a, x, b)))))

    \ \ \| SNode (a, x, b) -\>

    \ \ \ \ (match empty a with

    \ \ \ \ \ \ \| IsZ -\> x, L b

    \ \ \ \ \ \ \| NotZ -\>

    \ \ \ \ \ \ \ \ (match delmin a with

    \ \ \ \ \ \ \ \ \ \ y, k -\>

    \ \ \ \ \ \ \ \ \ \ (match k with

    \ \ \ \ \ \ \ \ \ \ \ \ \| L a -\> y, R (LNode (a, x, b))

    \ \ \ \ \ \ \ \ \ \ \ \ \| R a -\> y, R (SNode (a, x, b)))))

    \ \ \| MNode (a, x, b) -\>

    \ \ \ \ (match delmin a with

    \ \ \ \ \ \ y, k -\>

    \ \ \ \ \ \ (match k with

    \ \ \ \ \ \ \ \ \| L a -\> y, L (SNode (a, x, b))

    \ \ \ \ \ \ \ \ \| R a -\> y, R (MNode (a, x, b))))
  </code>

  Value items from <em|non_pointwise_avl_delmin.gadti.target>:

  <\code>
    val empty : <math|\<forall\>>a. AVL a <math|\<rightarrow\>> Zero a

    \;

    val delmin : <math|\<forall\>>a. AVL (S a) <math|\<rightarrow\>> (Int,
    Choice (AVL a, AVL (S a)))
  </code>

  <subsection|Function <verbatim|fd_comp>>

  Example from <cite|PracticalGADTsInfer>, described on pages 213-215. The
  only difference is that the original has <verbatim|\| FDI -\<gtr\> fd2> as
  the fourth line of <verbatim|fd_comp> instead of our expanded <verbatim|\|
  FDI -\> (match fd2 with \| FDI -\> fd2 \| FDC _ -\> fd2 \| FDG _ -\> fd2)>.
  Source file <em|non_pointwise_fd_comp.gadt>:

  <\code>
    datatype FunDesc : type * type

    datacons FDI : <math|\<forall\>>a. FunDesc (a, a)

    datacons FDC : <math|\<forall\>>a, b. b <math|\<longrightarrow\>> FunDesc
    (a, b)

    datacons FDG : <math|\<forall\>>a, b. (a <math|\<rightarrow\>> b)
    <math|\<longrightarrow\>> FunDesc (a, b)

    \;

    external fd_fun : <math|\<forall\>>a, b. FunDesc (a, b)
    <math|\<rightarrow\>> a <math|\<rightarrow\>> b

    \;

    let fd_comp = fun fd1 fd2 -\>

    \ \ let o = fun f g x -\> f (g x) in

    \ \ match fd1 with

    \ \ \ \ \| FDI -\> (match fd2 with \| FDI -\> fd2 \| FDC _ -\> fd2 \| FDG
    _ -\> fd2)

    \ \ \ \ \| FDC b -\>\ 

    \ \ \ \ \ \ (match fd2 with

    \ \ \ \ \ \ \ \ \| FDI -\> fd1

    \ \ \ \ \ \ \ \ \| FDC c -\> FDC (fd_fun fd2 b)

    \ \ \ \ \ \ \ \ \| FDG g -\> FDC (fd_fun fd2 b))

    \ \ \ \ \| FDG f -\>

    \ \ \ \ \ \ (match fd2 with

    \ \ \ \ \ \ \ \ \| FDI -\> fd1

    \ \ \ \ \ \ \ \ \| FDC c -\> FDC c

    \ \ \ \ \ \ \ \ \| FDG g -\> FDG (o (fd_fun fd2) f))
  </code>

  Compare also the example <em|non_pointwise_fd_comp2.gadt>:

  <\code>
    datatype FunDesc : type * type

    datacons FDI : <math|\<forall\>>a. FunDesc (a, a)

    datacons FDC : <math|\<forall\>>a, b. b <math|\<longrightarrow\>> FunDesc
    (a, b)

    datacons FDG : <math|\<forall\>>a, b. (a <math|\<rightarrow\>> b)
    <math|\<longrightarrow\>> FunDesc (a, b)

    \;

    external fd_fun : <math|\<forall\>>a, b. FunDesc (a, b)
    <math|\<rightarrow\>> a <math|\<rightarrow\>> b

    \;

    let o = fun f g x -\> f (g x)

    \;

    let fd_comp =

    \ \ function

    \ \ \ \ \| FDI -\> (function FDI -\> FDI \| FDC c -\> FDC c \| FDG g -\>
    FDG g)

    \ \ \ \ \| FDC b as fd1 -\>

    \ \ \ \ \ \ (function

    \ \ \ \ \ \ \ \ \| FDI -\> fd1

    \ \ \ \ \ \ \ \ \| FDC c as fd2 -\> FDC (fd_fun fd2 b)

    \ \ \ \ \ \ \ \ \| FDG g as fd2 -\> FDC (fd_fun fd2 b))

    \ \ \ \ \| FDG f as fd1 -\>

    \ \ \ \ \ \ (function

    \ \ \ \ \ \ \ \ \| FDI -\> fd1

    \ \ \ \ \ \ \ \ \| FDC c -\> FDC c

    \ \ \ \ \ \ \ \ \| FDG g as fd2 -\> FDG (o (fd_fun fd2) f))
  </code>

  Value items from <em|non_pointwise_fd_comp2.gadti.target>:

  <\code>
    val o : <math|\<forall\>>a, b, c. (b <math|\<rightarrow\>> a)
    <math|\<rightarrow\>> (c <math|\<rightarrow\>> b) <math|\<rightarrow\>> c
    <math|\<rightarrow\>> a

    \;

    val fd_comp :

    \ \ \ <math|\<forall\>>a, b, c. FunDesc (b, c) <math|\<rightarrow\>>
    FunDesc (c, a) <math|\<rightarrow\>> FunDesc (b, a)
  </code>

  <subsection|Function <verbatim|zip1>: <math|N>-way <verbatim|zip_with>>

  Example from <cite|PracticalGADTsInfer>, described on pages 216-217. The
  local definition of <verbatim|apply> is a <verbatim|let rec> here because
  it needs to be polymorphic. Source file <em|non_pointwise_zip1.gadt>:

  <\code>
    datatype List : type

    datacons N : <math|\<forall\>>a. List a

    datacons C : <math|\<forall\>>a. a * List a <math|\<longrightarrow\>>
    List a

    \;

    datatype Zip1 : type * type

    datacons Zero1 : <math|\<forall\>>a. Zip1 (List a, List a)

    datacons Succ1 :

    \ \ <math|\<forall\>>a, b, c. Zip1 (List a, b) <math|\<longrightarrow\>>
    Zip1 (List (c <math|\<rightarrow\>> a), (List c <math|\<rightarrow\>> b))

    \;

    external zip_with : <math|\<forall\>>a, b, c. (a <math|\<rightarrow\>> b
    <math|\<rightarrow\>> c) <math|\<rightarrow\>> List a
    <math|\<rightarrow\>> List b <math|\<rightarrow\>> List c

    \;

    external repeat : <math|\<forall\>>a. a <math|\<rightarrow\>> List a

    \;

    let zip1 =

    \ \ let rec apply = fun f x -\> f x in

    \ \ let rec z1 = fun fs -\> function

    \ \ \ \ \| Zero1 -\> fs

    \ \ \ \ \| Succ1 n2 -\> fun xs -\> z1 (zip_with apply fs xs) n2 in

    \ \ fun n f -\> z1 (repeat f) n
  </code>

  Value items from <em|non_pointwise_zip1.gadt>:

  <\code>
    val zip1 : <math|\<forall\>>a, b. Zip1 (List b, a) <math|\<rightarrow\>>
    b <math|\<rightarrow\>> a
  </code>

  <subsection|Function <verbatim|leq>>

  Example from <cite|PracticalGADTsInfer>, described on pages 217-219. Source
  file <em|non_pointwise_leq.gadt>, requires option <verbatim|-prefer_guess>
  for inference:

  <\code>
    datatype Z

    datatype S : type

    \;

    datatype Nat : type

    datacons Zn : Nat Z

    datacons Sn : <math|\<forall\>>a. Nat a <math|\<longrightarrow\>> Nat (S
    a)

    \;

    datatype NatLeq : type * type

    datacons LeZ : <math|\<forall\>>a. NatLeq (Z, a)

    datacons LeS : <math|\<forall\>>a, b. NatLeq (a, b)
    \ <math|\<longrightarrow\>> NatLeq (S a, S b)

    \;

    let rec leq = function

    \ \ \| Zn -\> LeZ

    \ \ \| Sn n -\> LeS (leq n)
  </code>

  Value items from <em|non_pointwise_leq.gadti.target>:

  <\code>
    val leq : <math|\<forall\>>a. Nat a <math|\<rightarrow\>> NatLeq (a, a)
  </code>

  <subsection|Function <verbatim|run_state>>

  Example from <cite|PracticalGADTsInfer>, described on pages 219-220. Source
  file <em|non_pointwise_run_state.gadt>:

  <\code>
    datatype State : type * type

    datacons Bind :

    \ \ <math|\<forall\>>a, b, s. State (s, a) * (a <math|\<rightarrow\>>
    State (s, b)) <math|\<longrightarrow\>> State (s, b)

    datacons Return : <math|\<forall\>>a, s. a <math|\<longrightarrow\>>
    State (s, a)

    datacons Get : <math|\<forall\>>s. State (s, s)

    datacons Put : <math|\<forall\>>s. s <math|\<longrightarrow\>> State (s,
    ())

    \;

    let rec run_state = fun s -\> function

    \ \ \| Return a -\> (s, a)

    \ \ \| Get -\> (s, s)

    \ \ \| Put u -\> (u, ())

    \ \ \| Bind (m, k) -\>

    \ \ \ \ match m with

    \ \ \ \ \ \ \| Return a -\> run_state s (k a)

    \ \ \ \ \ \ \| Get -\> run_state s (k s)

    \ \ \ \ \ \ \| Put u -\> run_state u (k ())

    \ \ \ \ \ \ \| Bind (n, j) -\> run_state s (Bind (n, fun x -\> Bind (j x,
    k)))
  </code>

  Value items from <em|non_pointwise_run_state.gadti.target>:

  <\code>
    val run_state : <math|\<forall\>>a, b. a <math|\<rightarrow\>> State (a,
    b) <math|\<rightarrow\>> (a, b)
  </code>

  <section|Run-time Type Representations>

  <subsection|Function <verbatim|eval>>

  Source file <em|eval.gadt>:

  <\code>
    datatype Term : type

    \;

    external let plus : Int <math|\<rightarrow\>> Int <math|\<rightarrow\>>
    Int = "(+)"

    external let is_zero : Int <math|\<rightarrow\>> Bool = "(=) 0"

    \;

    datacons Lit : Int <math|\<longrightarrow\>> Term Int

    datacons Plus : Term Int * Term Int <math|\<longrightarrow\>> Term Int

    datacons IsZero : Term Int <math|\<longrightarrow\>> Term Bool

    datacons If : <math|\<forall\>>a. Term Bool * Term a * Term a
    <math|\<longrightarrow\>> Term a

    datacons Pair : <math|\<forall\>>a, b. Term a * Term b
    <math|\<longrightarrow\>> Term (a, b)

    datacons Fst : <math|\<forall\>>a, b. Term (a, b)
    <math|\<longrightarrow\>> Term a

    datacons Snd : <math|\<forall\>>a, b. Term (a, b)
    <math|\<longrightarrow\>> Term b

    \;

    let rec eval = function

    \ \ \| Lit i -\<gtr\> i

    \ \ \| IsZero x -\<gtr\> is_zero (eval x)

    \ \ \| Plus (x, y) -\<gtr\> plus (eval x) (eval y)

    \ \ \| If (b, t, e) -\<gtr\> (match eval b with True -\<gtr\> eval t \|
    False -\<gtr\> eval e)

    \ \ \| Pair (x, y) -\<gtr\> eval x, eval y

    \ \ \| Fst p -\<gtr\> (match eval p with x, y -\<gtr\> x)

    \ \ \| Snd p -\<gtr\> (match eval p with x, y -\<gtr\> y)
  </code>

  Value items from <em|eval.gadti.target>:

  <\code>
    val eval : <math|\<forall\>>a. Term a <math|\<rightarrow\>> a
  </code>

  Exported OCaml source file <em|eval.ml.target>:

  <\code>
    type num = int

    type _ term =

    \ \ \| Lit : int -\> int term

    \ \ \| Plus : int term * int term -\> int term

    \ \ \| IsZero : int term -\> bool term

    \ \ \| If : (*<math|\<forall\>>'a.*)bool term * 'a term * 'a term
    -\<gtr\> 'a term

    \ \ \| Pair : (*<math|\<forall\>>'a, 'b.*)'a term * 'b term -\<gtr\> (('a
    * 'b)) term

    \ \ \| Fst : (*<math|\<forall\>>'a, 'b.*)(('a * 'b)) term -\<gtr\> 'a
    term

    \ \ \| Snd : (*<math|\<forall\>>'a, 'b.*)(('a * 'b)) term -\<gtr\> 'b
    term

    let plus : (int -\> int -\> int) = (+)

    let is_zero : (int -\> bool) = (=) 0

    let rec eval : type a . (a term -\> a) =

    \ \ ((function Lit i -\> i \| IsZero x -\> is_zero (eval x)

    \ \ \ \ \| Plus (x, y) -\> plus (eval x) (eval y)

    \ \ \ \ \| If (b, t, e) -\> (if eval b then eval t else eval e)

    \ \ \ \ \| Pair (x, y) -\> (eval x, eval y)

    \ \ \ \ \| Fst p -\> let ((x, y): (a * _)) = eval p in x

    \ \ \ \ \| Snd p -\> let ((x, y): (_ * a)) = eval p in y): a term -\> a)
  </code>

  <subsection|Function <verbatim|equal>>

  Source file <em|equal_assert.gadt>:

  <\code>
    datatype Ty : type

    datatype List : type

    datacons Zero : Int

    datacons Nil : <math|\<forall\>>a. List a

    datacons TInt : Ty Int

    datacons TPair : <math|\<forall\>>a, b. Ty a * Ty b
    <math|\<longrightarrow\>> Ty (a, b)

    datacons TList : <math|\<forall\>>a. Ty a <math|\<longrightarrow\>> Ty
    (List a)

    external let eq_int : Int <math|\<rightarrow\>> Int <math|\<rightarrow\>>
    Bool = "(=)"

    external let b_and : Bool <math|\<rightarrow\>> Bool
    <math|\<rightarrow\>> Bool = "(&&)"

    external let b_not : Bool <math|\<rightarrow\>> Bool = "not"

    external forall2 : <math|\<forall\>>a, b. (a <math|\<rightarrow\>> b
    <math|\<rightarrow\>> Bool) <math|\<rightarrow\>> List a
    <math|\<rightarrow\>> List b <math|\<rightarrow\>> Bool

    \;

    let rec equal = function

    \ \ \| TInt, TInt -\<gtr\> fun x y -\<gtr\> eq_int x y

    \ \ \| TPair (t1, t2), TPair (u1, u2) -\<gtr\> \ 

    \ \ \ \ (fun (x1, x2) (y1, y2) -\<gtr\>

    \ \ \ \ \ \ \ \ b_and (equal (t1, u1) x1 y1)

    \ \ \ \ \ \ \ \ \ \ \ \ \ \ (equal (t2, u2) x2 y2))

    \ \ \| TList t, TList u -\<gtr\> forall2 (equal (t, u))

    \ \ \| _ -\<gtr\> fun _ _ -\<gtr\> False

    \ \ \| TInt, TList l -\<gtr\> (function Nil -\<gtr\> assert false)

    \ \ \| TList l, TInt -\<gtr\> (fun _ -\<gtr\> function Nil -\<gtr\>
    assert false)
  </code>

  Source file <em|equal_test.gadt>:

  <\code>
    datatype Ty : type

    datatype List : type

    datacons Nil : <math|\<forall\>>a. List a

    datacons TInt : Ty Int

    datacons TPair : <math|\<forall\>>a, b. Ty a * Ty b
    <math|\<longrightarrow\>> Ty (a, b)

    datacons TList : <math|\<forall\>>a. Ty a <math|\<longrightarrow\>> Ty
    (List a)

    external let zero : Int = "0"

    external let eq_int : Int <math|\<rightarrow\>> Int <math|\<rightarrow\>>
    Bool = "(=)"

    external let b_and : Bool <math|\<rightarrow\>> Bool
    <math|\<rightarrow\>> Bool = "(&&)"

    external let b_not : Bool <math|\<rightarrow\>> Bool = "not"

    external forall2 : <math|\<forall\>>a, b. (a <math|\<rightarrow\>> b
    <math|\<rightarrow\>> Bool) <math|\<rightarrow\>> List a
    <math|\<rightarrow\>> List b <math|\<rightarrow\>> Bool

    \;

    let rec equal = function

    \ \ \| TInt, TInt -\<gtr\> fun x y -\<gtr\> eq_int x y

    \ \ \| TPair (t1, t2), TPair (u1, u2) -\<gtr\> \ 

    \ \ \ \ (fun (x1, x2) (y1, y2) -\<gtr\>

    \ \ \ \ \ \ \ \ b_and (equal (t1, u1) x1 y1)

    \ \ \ \ \ \ \ \ \ \ \ \ \ \ (equal (t2, u2) x2 y2))

    \ \ \| TList t, TList u -\<gtr\> forall2 (equal (t, u))

    \ \ \| _ -\<gtr\> fun _ _ -\<gtr\> False

    test b_not (equal (TInt, TList TInt) zero Nil)
  </code>

  Value items from <em|equal_test.gadti.target>:

  <\code>
    val equal : <math|\<forall\>>a, b. (Ty a, Ty b) <math|\<rightarrow\>> a
    <math|\<rightarrow\>> b <math|\<rightarrow\>> Bool
  </code>

  <section|Lists with Length>

  <subsection|Function <verbatim|head>>

  Source file <em|list_head.gadt>:

  <\code>
    datatype List : type * num

    datacons LNil : <math|\<forall\>>a. List(a, 0)

    datacons LCons : <math|\<forall\>>n, a [0<math|\<leqslant\>>n]. a *
    List(a, n) <math|\<longrightarrow\>> List(a, n+1)

    \;

    let head = function

    \ \ \| LCons (x, _) -\> x

    \ \ \| LNil -\> assert false
  </code>

  Value items from <em|list_head.gadti.target>:

  <\code>
    val head : <math|\<forall\>>n, a[1 <math|\<leqslant\>> n]. List (a, n)
    <math|\<rightarrow\>> a
  </code>

  <subsection|Function <verbatim|append>>

  This example is not featured in the <em|examples> directory. The natural
  solution would be to propagate one of the arguments when the other list is
  empty: <verbatim|function LNil -\<gtr\> (fun l -<no-break>\<gtr\> l)
  \|><math|\<ldots\>> This currently leads to the problem of insufficient
  information about <verbatim|l>. We can expand all cases of both arguments:

  <\code>
    datatype Elem

    datatype List : num

    datacons LNil : List 0

    datacons LCons : <math|\<forall\>>n [0<math|\<leqslant\>>n]. Elem * List
    n <math|\<longrightarrow\>> List (n+1)

    \;

    let rec append =

    \ \ function LNil -\<gtr\> (function LNil -\<gtr\> LNil \| LCons (_,_) as
    l -\<gtr\> l)

    \ \ \ \ \| LCons (x, xs) -\<gtr\>

    \ \ \ \ \ \ (function LNil -\<gtr\> LCons (x, append xs LNil)

    \ \ \ \ \ \ \ \ \| LCons (_,_) as l -\<gtr\> LCons (x, append xs l))
  </code>

  Inferred type:

  <\code>
    val append : <math|\<forall\>>n, k. List (a, k) <math|\<rightarrow\>>
    List (a, n) <math|\<rightarrow\>> List (n + k)
  </code>

  We can also use assertions:

  <\code>
    let rec append =

    \ \ function

    \ \ \ \ \| LNil -\>

    \ \ \ \ \ \ (function l when (length l + 1) \<less\>= 0 -\> assert false
    \| l -\> l)

    \ \ \ \ \| LCons (x, xs) -\>

    \ \ \ \ \ \ (function l when (length l + 1) \<less\>= 0 -\> assert false

    \ \ \ \ \ \ \| l -\> LCons (x, append xs l))
  </code>

  Inferred type:

  <\code>
    val append : <math|\<forall\>>n, k[0<math|\<leqslant\>>n <math|\<wedge\>>
    0<math|\<leqslant\>>n + k]. List(a, k) <math|\<rightarrow\>> List(a, n)
    <math|\<rightarrow\>> List(n + k)
  </code>

  <subsection|Function <verbatim|flatten_pairs>>

  Source file <em|flatten_pairs.gadt>:

  <\code>
    datatype List : type * num

    datacons LNil : <math|\<forall\>>a. List(a, 0)

    datacons LCons : <math|\<forall\>>n, a [0<math|\<leqslant\>>n]. a *
    List(a, n) <math|\<longrightarrow\>> List(a, n+1)

    \;

    let rec flatten_pairs =

    \ \ function LNil -\<gtr\> LNil

    \ \ \ \ \| LCons ((x, y), l) -\<gtr\>

    \ \ \ \ \ \ LCons (x, LCons (y, flatten_pairs l))
  </code>

  Value items from <em|flatten_pairs.gadti.target>:

  <\code>
    val flatten_pairs : <math|\<forall\>>n, a. List ((a, a), n)
    <math|\<rightarrow\>> List (a, 2 n)
  </code>

  <subsection|Function <verbatim|filter>>

  Source file <em|filter.gadt>:

  <\code>
    datatype List : type * num

    datacons LNil : <math|\<forall\>>a. List(a, 0)

    datacons LCons : <math|\<forall\>>n, a [0<math|\<leqslant\>>n]. a *
    List(a, n) <math|\<longrightarrow\>> List(a, n+1)

    \;

    let rec filter = fun f -\<gtr\>

    \ \ efunction LNil -\<gtr\> LNil

    \ \ \ \ \| LCons (x, xs) -\<gtr\>

    \ \ \ \ \ \ ematch f x with

    \ \ \ \ \ \ \ \ \| True -\<gtr\>

    \ \ \ \ \ \ \ \ \ \ let ys = filter f xs in

    \ \ \ \ \ \ \ \ \ \ LCons (x, ys)

    \ \ \ \ \ \ \ \ \| False -\<gtr\>

    \ \ \ \ \ \ \ \ \ \ filter f xs
  </code>

  Value items from <em|filter.gadti.target>:

  <\code>
    val filter :

    \ \ \ <math|\<forall\>>n, a.

    \ \ \ (a <math|\<rightarrow\>> Bool) <math|\<rightarrow\>> List (a, n)
    <math|\<rightarrow\>> <math|\<exists\>>k[0 <math|\<leqslant\>> k
    <math|\<wedge\>> k <math|\<leqslant\>> n].List (a, k)
  </code>

  <subsection|Function <verbatim|zip>>

  Source file <em|zip.gadt>:

  <\code>
    datatype List : type * num

    datacons LNil : <math|\<forall\>>a. List(a, 0)

    datacons LCons : <math|\<forall\>>n, a [0<math|\<leqslant\>>n]. a *
    List(a, n) <math|\<longrightarrow\>> List(a, n+1)

    \;

    let rec zip =

    \ \ efunction

    \ \ \ \ \| LNil, LNil -\<gtr\> LNil

    \ \ \ \ \| LNil, LCons (_, _) -\<gtr\> LNil

    \ \ \ \ \| LCons (_, _), LNil -\<gtr\> LNil

    \ \ \ \ \| LCons (x, xs), LCons (y, ys) -\<gtr\>

    \ \ \ \ \ \ let zs = zip (xs, ys) in

    \ \ \ \ \ \ LCons ((x, y), zs)
  </code>

  The inferred type is:

  <\code>
    val <math|\<forall\>>n, k, a, b. (List (a, n), List (b, k))
    <math|\<rightarrow\>>

    \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ <math|\<exists\>>i[i=min (k, n)].List
    ((a, b), i)
  </code>

  <section|Binary Numbers>

  <subsection|Function <verbatim|plus>>

  Source file <em|binary_plus.gadt>:

  <\code>
    datatype Binary : num

    datatype Carry : num

    \;

    datacons Zero : Binary 0

    datacons PZero : <math|\<forall\>>n [0<math|\<leqslant\>>n]. Binary n
    <math|\<longrightarrow\>> Binary(2 n)

    datacons POne : <math|\<forall\>>n [0<math|\<leqslant\>>n]. Binary n
    <math|\<longrightarrow\>> Binary(2 n + 1)

    \;

    datacons CZero : Carry 0

    datacons COne : Carry 1

    \;

    let rec plus =

    \ \ function CZero -\<gtr\>

    \ \ \ \ (function

    \ \ \ \ \ \ \| Zero -\<gtr\>

    \ \ \ \ \ \ \ \ (function Zero -\<gtr\> Zero

    \ \ \ \ \ \ \ \ \ \ \| PZero _ as b -\<gtr\> b

    \ \ \ \ \ \ \ \ \ \ \| POne _ as b -\<gtr\> b)

    \ \ \ \ \ \ \| PZero a1 as a -\<gtr\>

    \ \ \ \ \ \ \ \ (function Zero -\<gtr\> a

    \ \ \ \ \ \ \ \ \ \ \| PZero b1 -\<gtr\> PZero (plus CZero a1 b1)

    \ \ \ \ \ \ \ \ \ \ \| POne b1 -\<gtr\> POne (plus CZero a1 b1))

    \ \ \ \ \ \ \| POne a1 as a -\<gtr\>

    \ \ \ \ \ \ \ \ (function Zero -\<gtr\> a

    \ \ \ \ \ \ \ \ \ \ \| PZero b1 -\<gtr\> POne (plus CZero a1 b1)

    \ \ \ \ \ \ \ \ \ \ \| POne b1 -\<gtr\> PZero (plus COne a1 b1)))

    \ \ \ \ \| COne -\<gtr\>

    \ \ \ \ (function Zero -\<gtr\>

    \ \ \ \ \ \ \ \ (function Zero -\<gtr\> POne(Zero)

    \ \ \ \ \ \ \ \ \ \ \| PZero b1 -\<gtr\> POne b1

    \ \ \ \ \ \ \ \ \ \ \| POne b1 -\<gtr\> PZero (plus COne Zero b1))

    \ \ \ \ \ \ \| PZero a1 -\<gtr\>

    \ \ \ \ \ \ \ \ (function Zero -\<gtr\> POne a1

    \ \ \ \ \ \ \ \ \ \ \| PZero b1 -\<gtr\> POne (plus CZero a1 b1)

    \ \ \ \ \ \ \ \ \ \ \| POne b1 -\<gtr\> PZero (plus COne a1 b1))

    \ \ \ \ \ \ \| POne a1 -\<gtr\>

    \ \ \ \ \ \ \ \ (function Zero -\<gtr\> PZero (plus COne a1 Zero)

    \ \ \ \ \ \ \ \ \ \ \| PZero b1 -\<gtr\> PZero (plus COne a1 b1)

    \ \ \ \ \ \ \ \ \ \ \| POne b1 -\<gtr\> POne (plus COne a1 b1)))
  </code>

  Value items from <em|binary_plus.gadti.target>:

  <\code>
    val plus :

    \ \ \ <math|\<forall\>>i, k, n. Carry i <math|\<rightarrow\>> Binary k
    <math|\<rightarrow\>> Binary n <math|\<rightarrow\>> Binary (n + k + i)
  </code>

  <subsection|Function <verbatim|increment>>

  This example is not featured in the <em|examples> directory.

  <\code>
    datatype Binary : num

    \;

    datacons Zero : Binary 0

    datacons PZero : <math|\<forall\>>n [0<math|\<leqslant\>>n]. Binary n
    <math|\<longrightarrow\>> Binary(2 n)

    datacons POne : <math|\<forall\>>n [0<math|\<leqslant\>>n]. Binary n
    <math|\<longrightarrow\>> Binary(2 n + 1)

    \;

    let rec increment =

    \ \ function Zero -\<gtr\> POne Zero

    \ \ \ \ \| PZero a1 -\<gtr\> POne a1

    \ \ \ \ \| POne a1 -\<gtr\> PZero (increment a1)
  </code>

  Inferred type:

  <\code>
    val increment : <math|\<forall\>>n. Binary n <math|\<rightarrow\>> Binary
    (n + 1)
  </code>

  <subsection|Function <verbatim|bitwise_or>>

  For brevity, the function is named <verbatim|ub> rather than
  <verbatim|bitwise_or> in the code example. Source file
  <em|binary_upper_bound.gadt>:

  <\code>
    datatype Binary : num

    datacons Zero : Binary 0

    datacons PZero : <math|\<forall\>>n [0<math|\<leqslant\>>n]. Binary n
    <math|\<longrightarrow\>> Binary(2 n)

    datacons POne : <math|\<forall\>>n [0<math|\<leqslant\>>n]. Binary n
    <math|\<longrightarrow\>> Binary(2 n + 1)

    \;

    let rec ub = efunction

    \ \ \| Zero -\<gtr\>

    \ \ \ \ \ \ (efunction Zero -\<gtr\> Zero

    \ \ \ \ \ \ \ \ \| PZero b1 as b -\<gtr\> b

    \ \ \ \ \ \ \ \ \| POne b1 as b -\<gtr\> b)

    \ \ \| PZero a1 as a -\<gtr\>

    \ \ \ \ \ \ (efunction Zero -\<gtr\> a

    \ \ \ \ \ \ \ \ \| PZero b1 -\<gtr\>

    \ \ \ \ \ \ \ \ \ \ let r = ub a1 b1 in

    \ \ \ \ \ \ \ \ \ \ PZero r

    \ \ \ \ \ \ \ \ \| POne b1 -\<gtr\>

    \ \ \ \ \ \ \ \ \ \ let r = ub a1 b1 in

    \ \ \ \ \ \ \ \ \ \ POne r)

    \ \ \| POne a1 as a -\<gtr\>

    \ \ \ \ \ \ (efunction Zero -\<gtr\> a

    \ \ \ \ \ \ \ \ \| PZero b1 -\<gtr\>

    \ \ \ \ \ \ \ \ \ \ let r = ub a1 b1 in

    \ \ \ \ \ \ \ \ \ \ POne r

    \ \ \ \ \ \ \ \ \| POne b1 -\<gtr\>

    \ \ \ \ \ \ \ \ \ \ let r = ub a1 b1 in

    \ \ \ \ \ \ \ \ \ \ POne r)
  </code>

  Value items from\ 

  <\code>
    val plus :

    \ \ \ <math|\<forall\>>i, k, n. Carry i <math|\<rightarrow\>> Binary k
    <math|\<rightarrow\>> Binary n <math|\<rightarrow\>> Binary (n + k + i)
  </code>

  <section|AVL Trees>

  Source file <em|avl_tree.gadt>:

  <\code>
    (** We follow the AVL tree algorithm from OCaml Standard Library, where\ 

    \ \ \ \ the branches of a node are allowed to differ in height by at most
    2. *)

    \;

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

    datatype LinOrder

    datacons LT : LinOrder

    datacons EQ : LinOrder

    datacons GT : LinOrder

    external let compare : <math|\<forall\>>a. a <math|\<rightarrow\>> a
    <math|\<rightarrow\>> LinOrder =

    \ \ "fun x y -\> let c=Pervasives.compare x y in

    \ \ \ \ \ \ \ \ \ \ \ \ \ \ if c\<less\>0 then LT else if c=0 then EQ
    else GT"

    \;

    let height = function

    \ \ \| Empty -\> 0

    \ \ \| Node (_, _, _, k) -\> k

    \;

    let create = fun l x r -\>

    \ \ eif height l \<less\>= height r then Node (l, x, r, height r + 1)

    \ \ else Node (l, x, r, height l + 1)

    \;

    let singleton x = Node (Empty, x, Empty, 1)

    \;

    let rotr = fun l x r -\>

    \ \ \ \ ematch l with

    \ \ \ \ \| Empty -\> assert false

    \ \ \ \ \| Node (ll, lx, lr, _) -\>

    \ \ \ \ \ \ eif height lr \<less\>= height ll then

    \ \ \ \ \ \ \ \ let r' = create lr x r in

    \ \ \ \ \ \ \ \ create ll lx r'

    \ \ \ \ \ \ else

    \ \ \ \ \ \ \ \ ematch lr with

    \ \ \ \ \ \ \ \ \| Empty -\> assert false

    \ \ \ \ \ \ \ \ \| Node (lrl, lrx, lrr, _) -\>

    \ \ \ \ \ \ \ \ \ \ let l' = create ll lx lrl in

    \ \ \ \ \ \ \ \ \ \ let r' = create lrr x r in

    \ \ \ \ \ \ \ \ \ \ create l' lrx r'

    \;

    let rotl = fun l x r -\>

    \ \ \ \ ematch r with

    \ \ \ \ \| Empty -\> assert false

    \ \ \ \ \| Node (rl, rx, rr, _) -\>

    \ \ \ \ \ \ eif height rl \<less\>= height rr then

    \ \ \ \ \ \ \ \ let l' = create l x rl in

    \ \ \ \ \ \ \ \ create l' rx rr

    \ \ \ \ \ \ else

    \ \ \ \ \ \ \ \ ematch rl with

    \ \ \ \ \ \ \ \ \| Empty -\> assert false

    \ \ \ \ \ \ \ \ \| Node (rll, rlx, rlr, _) -\>

    \ \ \ \ \ \ \ \ \ \ let l' = create l x rll in

    \ \ \ \ \ \ \ \ \ \ let r' = create rlr rx rr in

    \ \ \ \ \ \ \ \ \ \ create l' rlx r'

    \;

    let rec add x = efunction

    \ \ \| Empty -\> Node (Empty, x, Empty, 1)

    \ \ \| Node (l, y, r, h) -\>

    \ \ \ \ ematch compare x y, height l, height r with

    \ \ \ \ \| EQ, _, _ -\> Node (l, x, r, h)

    \ \ \ \ \| LT, hl, hr -\>

    \ \ \ \ \ \ let l' = add x l in

    \ \ \ \ \ \ eif height l' \<less\>= hr+2 then create l' y r else rotr l'
    y r

    \ \ \ \ \| GT, hl, hr -\>

    \ \ \ \ \ \ let r' = add x r in

    \ \ \ \ \ \ eif height r' \<less\>= hl+2 then create l y r' else rotl l y
    r'

    \;

    let rec mem x = function

    \ \ \| Empty -\> False

    \ \ \| Node (l, y, r, _) -\>

    \ \ \ \ match compare x y with

    \ \ \ \ \| LT -\> mem x l

    \ \ \ \ \| EQ -\> True

    \ \ \ \ \| GT -\> mem x r

    \;

    let rec min_binding = function

    \ \ \| Empty -\> assert false

    \ \ \| Node (Empty, x, r, _) -\> x

    \ \ \| Node ((Node (_,_,_,_) as l), x, r, _) -\> min_binding l

    \;

    let rec remove_min_binding = efunction

    \ \ \| Empty -\> assert false

    \ \ \| Node (Empty, x, r, _) -\> r

    \ \ \| Node ((Node (_,_,_,_) as l), x, r, _) -\>

    \ \ \ \ let l' = remove_min_binding l in

    \ \ \ \ eif height r \<less\>= height l' + 2 then create l' x r

    \ \ \ \ else rotl l' x r

    \;

    let merge = efunction

    \ \ \| Empty, Empty -\> Empty

    \ \ \| Empty, (Node (_,_,_,_) as t) -\> t

    \ \ \| (Node (_,_,_,_) as t), Empty -\> t

    \ \ \| (Node (_,_,_,_) as t1), (Node (_,_,_,_) as t2) -\>

    \ \ \ \ let x = min_binding t2 in

    \ \ \ \ let t2' = remove_min_binding t2 in

    \ \ \ \ eif height t1 \<less\>= height t2' + 2 then create t1 x t2'

    \ \ \ \ else rotr t1 x t2'

    \;

    let rec remove = fun x -\> efunction

    \ \ \| Empty -\> Empty

    \ \ \| Node (l, y, r, h) -\>

    \ \ \ \ ematch compare x y with

    \ \ \ \ \| EQ -\> merge (l, r)

    \ \ \ \ \| LT -\>

    \ \ \ \ \ \ let l' = remove x l in

    \ \ \ \ \ \ eif height r \<less\>= height l' + 2 then create l' y r

    \ \ \ \ \ \ else rotl l' y r

    \ \ \ \ \| GT -\>

    \ \ \ \ \ \ let r' = remove x r in

    \ \ \ \ \ \ eif height l \<less\>= height r' + 2 then create l y r'

    \ \ \ \ \ \ else rotr l y r'
  </code>

  Value items from <em|avl_tree.gadti.target>:

  <\code>
    val height : <math|\<forall\>>n, a. Avl (a, n) <math|\<rightarrow\>> Num
    n

    \;

    val create :

    \ \ \ <math|\<forall\>>k, n, a[0 <math|\<leqslant\>> n <math|\<wedge\>> 0
    <math|\<leqslant\>> k <math|\<wedge\>> n <math|\<leqslant\>> k + 2
    <math|\<wedge\>> k <math|\<leqslant\>> n + 2].

    \ \ \ Avl (a, k) <math|\<rightarrow\>> a <math|\<rightarrow\>> Avl (a, n)
    <math|\<rightarrow\>> <math|\<exists\>>i[i=max (k + 1, n + 1)].Avl (a, i)

    \;

    val singleton : <math|\<forall\>>a. a <math|\<rightarrow\>> Avl (a, 1)

    \;

    val rotr :

    \ \ \ <math|\<forall\>>k, n, a[0 <math|\<leqslant\>> n <math|\<wedge\>> n
    + 2 <math|\<leqslant\>> k <math|\<wedge\>> k <math|\<leqslant\>> n + 3].

    \ \ \ Avl (a, k) <math|\<rightarrow\>> a <math|\<rightarrow\>> Avl (a, n)
    <math|\<rightarrow\>> <math|\<exists\>>n[k <math|\<leqslant\>> n
    <math|\<wedge\>>

    \ \ \ \ \ n <math|\<leqslant\>> k + 1].Avl (a, n)

    \;

    val rotl :

    \ \ \ <math|\<forall\>>k, n, a[0 <math|\<leqslant\>> k <math|\<wedge\>> n
    <math|\<leqslant\>> k + 3 <math|\<wedge\>> k + 2 <math|\<leqslant\>> n].

    \ \ \ Avl (a, k) <math|\<rightarrow\>> a <math|\<rightarrow\>> Avl (a, n)
    <math|\<rightarrow\>> <math|\<exists\>>k[k <math|\<leqslant\>> n + 1
    <math|\<wedge\>>

    \ \ \ \ \ n <math|\<leqslant\>> k].Avl (a, k)

    \;

    val add :

    \ \ \ <math|\<forall\>>n, a.

    \ \ \ a <math|\<rightarrow\>> Avl (a, n) <math|\<rightarrow\>>
    <math|\<exists\>>k[1 <math|\<leqslant\>> k <math|\<wedge\>> n
    <math|\<leqslant\>> k <math|\<wedge\>> k <math|\<leqslant\>> n + 1].Avl
    (a, k)

    \;

    val mem : <math|\<forall\>>n, a. a <math|\<rightarrow\>> Avl (a, n)
    <math|\<rightarrow\>> Bool

    \;

    val min_binding : <math|\<forall\>>n, a[1 <math|\<leqslant\>> n]. Avl (a,
    n) <math|\<rightarrow\>> a

    \;

    val remove_min_binding :

    \ \ \ <math|\<forall\>>n, a[1 <math|\<leqslant\>> n].

    \ \ \ Avl (a, n) <math|\<rightarrow\>> <math|\<exists\>>k[n
    <math|\<leqslant\>> k + 1 <math|\<wedge\>> k <math|\<leqslant\>> n
    <math|\<wedge\>> k + 2 <math|\<leqslant\>> 2 n].Avl (a, k)

    \;

    val merge :

    \ \ \ <math|\<forall\>>k, n, a[n <math|\<leqslant\>> k + 2
    <math|\<wedge\>> k <math|\<leqslant\>> n + 2].

    \ \ \ (Avl (a, n), Avl (a, k)) <math|\<rightarrow\>> <math|\<exists\>>i[n
    <math|\<leqslant\>> i <math|\<wedge\>> k <math|\<leqslant\>> i
    <math|\<wedge\>> i <math|\<leqslant\>> n + k <math|\<wedge\>>

    \ \ \ \ \ i<math|\<leqslant\>>max (k + 1, n + 1)].Avl (a, i)

    \;

    val remove :

    \ \ \ <math|\<forall\>>n, a.

    \ \ \ a <math|\<rightarrow\>> Avl (a, n) <math|\<rightarrow\>>
    <math|\<exists\>>k[n <math|\<leqslant\>> k + 1 <math|\<wedge\>> 0
    <math|\<leqslant\>> k <math|\<wedge\>> k <math|\<leqslant\>> n].Avl (a,
    k)
  </code>

  <section|Arrays and Matrices>

  For clarity, we present the array and matrix operations prelude separately
  here. Arrays are polymorphic, matrices only store floating point numbers.

  <\code>
    datatype Array : type * num

    external let array_make :

    \ \ <math|\<forall\>>n, a [0<math|\<leqslant\>>n]. Num n
    <math|\<rightarrow\>> a <math|\<rightarrow\>> Array (a, n) = "fun a b
    -\<gtr\> Array.make a b"

    external let array_get :

    \ \ <math|\<forall\>>n, k, a [0<math|\<leqslant\>>k <math|\<wedge\>>
    k+1<math|\<leqslant\>>n]. Array (a, n) <math|\<rightarrow\>> Num k
    <math|\<rightarrow\>> a = "fun a b -\<gtr\> Array.get a b"

    external let array_set :

    \ \ <math|\<forall\>>n, k, a [0<math|\<leqslant\>>k <math|\<wedge\>>
    k+1<math|\<leqslant\>>n]. Array (a, n) <math|\<rightarrow\>> Num k
    <math|\<rightarrow\>> a <math|\<rightarrow\>> () =

    \ \ "fun a b c -\> Array.set a b c"

    external let array_length :

    \ \ <math|\<forall\>>n, a. Array (a, n) <math|\<rightarrow\>> Num n =
    "fun a -\<gtr\> Array.length a"

    \;

    external type Matrix : num * num =

    \ \ "(int, Bigarray.int_elt, Bigarray.c_layout) Bigarray.Array2.t"

    external let matrix_make :

    \ \ <math|\<forall\>>n, k [0<math|\<leqslant\>>n <math|\<wedge\>>
    0<math|\<leqslant\>>k]. Num n <math|\<rightarrow\>> Num k
    <math|\<rightarrow\>> Matrix (n, k) =

    \ \ "fun a b -\> Bigarray.Array2.create Bigarray.int Bigarray.c_layout a
    b"

    external let matrix_get :

    \ \ <math|\<forall\>>n, k, i, j [0<math|\<leqslant\>>i <math|\<wedge\>>
    i+1<math|\<leqslant\>>n <math|\<wedge\>> 0<math|\<leqslant\>>j
    <math|\<wedge\>> j+1<math|\<leqslant\>>k].

    \ \ \ Matrix (n, k) <math|\<rightarrow\>> Num i <math|\<rightarrow\>> Num
    j <math|\<rightarrow\>> Int = "Bigarray.Array2.get"

    external let matrix_set :

    \ \ <math|\<forall\>>n, k, i, j [0<math|\<leqslant\>>i <math|\<wedge\>>
    i+1<math|\<leqslant\>>n <math|\<wedge\>> 0<math|\<leqslant\>>j
    <math|\<wedge\>> j+1<math|\<leqslant\>>k].

    \ \ \ Matrix (n, k) <math|\<rightarrow\>> Num i <math|\<rightarrow\>> Num
    j <math|\<rightarrow\>> Int <math|\<rightarrow\>> () =
    "Bigarray.Array2.set"

    external let matrix_dim1 :

    \ \ <math|\<forall\>>n, k [0<math|\<leqslant\>>n <math|\<wedge\>>
    0<math|\<leqslant\>>k]. Matrix (n, k) <math|\<rightarrow\>> Num n =
    "Bigarray.Array2.dim1"

    external let matrix_dim2 :

    \ \ <math|\<forall\>>n, k [0<math|\<leqslant\>>n <math|\<wedge\>>
    0<math|\<leqslant\>>k]. Matrix (n, k) <math|\<rightarrow\>> Num k =
    "Bigarray.Array2.dim2"
  </code>

  <subsection|Program <verbatim|dotprod>>

  Source file <em|liquid_dotprod.gadt>:

  <\code>
    external let add : Int <math|\<rightarrow\>> Int <math|\<rightarrow\>>
    Int = "fun n k -\<gtr\> n + k"

    external let prod : Int <math|\<rightarrow\>> Int <math|\<rightarrow\>>
    Int = "fun n k -\<gtr\> n * k"

    external let int0 : Int = "0"

    \;

    let dotprod v1 v2 =

    \ \ let rec loop n sum i =

    \ \ \ \ if n \<less\>= i then sum else

    \ \ \ \ \ \ \ \ loop n (add (prod (array_get v1 i) (array_get v2 i)) sum)

    \ \ \ \ \ \ \ \ \ \ (i + 1) in

    \ \ loop (array_length v1) int0 0
  </code>

  Value items from <em|liquid_dotprod.gadti.target>:

  <\code>
    val dotprod : <math|\<forall\>>k, n[k <math|\<leqslant\>> n]. Array (Int,
    k) <math|\<rightarrow\>> Array (Int, n) <math|\<rightarrow\>> Int
  </code>

  <subsection|Program <verbatim|bcopy>>

  Source file <em|liquid_bcopy.gadt>:

  <\code>
    let rec bcopy_aux src des = function

    \ \ \| i, m when m \<less\>= i -\> ()

    \ \ \| i, m when i+1 \<less\>= m -\>

    \ \ \ \ \ \ let n = array_get src i in

    \ \ \ \ \ \ array_set des i n;

    \ \ \ \ \ \ let j = i + 1 in

    \ \ \ \ \ \ bcopy_aux src des (j, m)

    \;

    let bcopy src des =

    \ \ let sz = array_length src in

    \ \ bcopy_aux src des (0, sz)
  </code>

  Value items from <em|liquid_bcopy.gadti.target>:

  <\code>
    val bcopy_aux :

    \ \ \ <math|\<forall\>>i, j, k, n, a[0 <math|\<leqslant\>> n
    <math|\<wedge\>> k <math|\<leqslant\>> i <math|\<wedge\>> k
    <math|\<leqslant\>> j].

    \ \ \ Array (a, j) <math|\<rightarrow\>> Array (a, i)
    <math|\<rightarrow\>> (Num n, Num k) <math|\<rightarrow\>> ()

    \;

    val bcopy : <math|\<forall\>>k, n, a[k <math|\<leqslant\>> n]. Array (a,
    k) <math|\<rightarrow\>> Array (a, n) <math|\<rightarrow\>> ()
  </code>

  <subsection|Program <verbatim|bsearch>>

  Source file <em|liquid_bsearch_harder.gadt>:

  <\code>
    datatype LinOrder

    datacons LE : LinOrder

    datacons GT : LinOrder

    datacons EQ : LinOrder

    \;

    external let compare : <math|\<forall\>>a. a <math|\<rightarrow\>> a
    <math|\<rightarrow\>> LinOrder =

    \ \ "fun a b -\> let c = Pervasives.compare a b in

    \ \ \ \ \ \ \ \ \ \ \ \ \ \ if c \<less\> 0 then LE else if c \> 0 then
    GT else EQ"

    external let equal : <math|\<forall\>>a. a <math|\<rightarrow\>> a
    <math|\<rightarrow\>> Bool = "fun a b -\<gtr\> a = b"

    \;

    external let div2 : <math|\<forall\>>n. Num (2 n) <math|\<rightarrow\>>
    Num n = "fun x -\<gtr\> x / 2"

    \;

    datatype Answer : type

    datacons NotFound : <math|\<forall\>>a. Answer a

    datacons Found : <math|\<forall\>>a. a <math|\<longrightarrow\>> Answer a

    \;

    let bsearch key vec =

    \ \ let rec look lo hi =

    \ \ \ \ if lo \<less\>= hi then

    \ \ \ \ \ \ \ \ let m = div2 (hi + lo) in

    \ \ \ \ \ \ \ \ let x = array_get vec m in

    \ \ \ \ \ \ \ \ match compare key x with

    \ \ \ \ \ \ \ \ \ \ \| LE -\> look lo (m + (-1))

    \ \ \ \ \ \ \ \ \ \ \| GT -\> look (m + 1) hi

    \ \ \ \ \ \ \ \ \ \ \| EQ -\> if equal key x then Found x else NotFound

    \ \ \ \ else NotFound in

    \ \ look 0 (array_length vec + (-1))
  </code>

  Value items from <em|liquid_bsearch_harder.gadti.target>:

  <\code>
    val bsearch : <math|\<forall\>>n, a[0 <math|\<leqslant\>> n]. a
    <math|\<rightarrow\>> Array (a, n) <math|\<rightarrow\>> Answer a
  </code>

  <subsection|Function <verbatim|bsearch2>><label|ExBsearch2>

  Source file <em|liquid_bsearch2_harder3.gadt>:

  <\code>
    datatype LinOrder

    datacons LE : LinOrder

    datacons GT : LinOrder

    datacons EQ : LinOrder

    \;

    external let compare : <math|\<forall\>>a. a <math|\<rightarrow\>> a
    <math|\<rightarrow\>> LinOrder =

    \ \ "fun a b -\> let c = Pervasives.compare a b in

    \ \ \ \ \ \ \ \ \ \ \ \ \ \ if c \<less\> 0 then LE else if c \> 0 then
    GT else EQ"

    external let equal : <math|\<forall\>>a. a <math|\<rightarrow\>> a
    <math|\<rightarrow\>> Bool = "fun a b -\<gtr\> a = b"

    \;

    external let div2 : <math|\<forall\>>n. Num (2 n) <math|\<rightarrow\>>
    Num n = "fun x -\<gtr\> x / 2"

    \;

    let bsearch key = efunction vec -\>

    \ \ let rec look key vec lo hi =

    \ \ \ \ assert num -1 \<less\>= hi;

    \ \ \ \ eif lo \<less\>= hi then

    \ \ \ \ \ \ \ \ let m = div2 (hi + lo) in

    \ \ \ \ \ \ \ \ let x = array_get vec m in

    \ \ \ \ \ \ \ \ ematch compare key x with

    \ \ \ \ \ \ \ \ \ \ \| LE -\> look key vec lo (m + (-1))

    \ \ \ \ \ \ \ \ \ \ \| GT -\> look key vec (m + 1) hi

    \ \ \ \ \ \ \ \ \ \ \| EQ -\> eif equal key x then m else -1

    \ \ \ \ else -1 in

    \ \ look key vec 0 (array_length vec + (-1))
  </code>

  Value items from <em|liquid_bsearch2_harder3.gadti.target>:

  <\code>
    val bsearch :

    \ \ \ <math|\<forall\>>n, a[0 <math|\<leqslant\>> n].

    \ \ \ a <math|\<rightarrow\>> Array (a, n) <math|\<rightarrow\>>
    <math|\<exists\>>k[0 <math|\<leqslant\>> k + 1 <math|\<wedge\>> k + 1
    <math|\<leqslant\>> n].Num k
  </code>

  Exported OCaml source <em|liquid_bsearch2_harder3.ml.target>:

  <\code>
    type num = int

    (** type _ array = built-in *)

    let array_make : (*0 <math|\<leqslant\>> n*) ((* n *) num -\<gtr\> 'a
    -\<gtr\> ('a (* n *)) array) =

    \ \ fun a b -\> Array.make a b

    let array_get :

    \ \ (*0 <math|\<leqslant\>> k <math|\<wedge\>> k + 1 <math|\<leqslant\>>
    n*) (('a (* n *)) array -\<gtr\> (* k *) num -\<gtr\> 'a) =

    \ \ fun a b -\> Array.get a b

    let array_set :

    \ \ (*0 <math|\<leqslant\>> k <math|\<wedge\>> k + 1 <math|\<leqslant\>>
    n*)

    \ \ (('a (* n *)) array -\> (* k *) num -\> 'a -\> unit) =

    \ \ fun a b c -\> Array.set a b c

    let array_length : (*0 <math|\<leqslant\>> n*) (('a (* n *)) array
    -\<gtr\> (* n *) num) =

    \ \ fun a -\> Array.length a

    type linOrder =

    \ \ \| LE : linOrder

    \ \ \| GT : linOrder

    \ \ \| EQ : linOrder

    let compare : ('a -\> 'a -\> linOrder) =

    \ \ fun a b -\> let c = Pervasives.compare a b in

    \ \ \ \ \ \ \ \ \ \ \ \ \ \ if c \< 0 then LE else if c \> 0 then GT else
    EQ

    let equal : ('a -\> 'a -\> bool) = fun a b -\> a = b

    let div2 : ((* 2 n *) num -\> (* n *) num) = fun x -\> x / 2

    type ex4 =

    \ \ \| Ex4 : (*<math|\<forall\>>'k, 'n[0 <math|\<leqslant\>> k + 1
    <math|\<wedge\>> k + 1 <math|\<leqslant\>> n].*)(* k *) num -\<gtr\>

    \ \ \ \ (* n *) ex4

    type ex3 =

    \ \ \| Ex3 : (*<math|\<forall\>>'k, 'n[0 <math|\<leqslant\>> k + 1
    <math|\<wedge\>> k <math|\<leqslant\>> n].*)(* k *) num -\<gtr\> (* n *)
    ex3

    let bsearch

    \ \ : type (*n*) a (*0 <math|\<leqslant\>> n*). (a -\<gtr\> (a (* n *))
    array -\<gtr\> (* n *) ex4) =

    \ \ (fun key vec -\>

    \ \ \ \ let Ex3 xcase =

    \ \ \ \ let rec look :

    \ \ \ \ type (*i*) (*j*) (*k*) b (*0 <math|\<leqslant\>> k + 1
    <math|\<wedge\>> 0 <math|\<leqslant\>> i <math|\<wedge\>>

    \ \ \ \ k + 1 <math|\<leqslant\>> j*). (b -\<gtr\> (b (* j *)) array
    -\<gtr\> (* i *) num -\<gtr\> (* k *) num -\<gtr\>

    \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ (* k *) ex3)

    \ \ \ \ =

    \ \ \ \ (fun key vec lo hi -\>

    \ \ \ \ \ \ (if lo \<less\>= hi then

    \ \ \ \ \ \ let m = div2 (hi + lo) in

    \ \ \ \ \ \ let x = array_get vec m in

    \ \ \ \ \ \ (((match (compare key x: linOrder) with

    \ \ \ \ \ \ LE -\> let Ex3 xcase = look key vec lo (m + -1) in Ex3 xcase

    \ \ \ \ \ \ \ \ \| GT -\> let Ex3 xcase = look key vec (m + 1) hi in Ex3
    xcase

    \ \ \ \ \ \ \ \ \| EQ -\>

    \ \ \ \ \ \ \ \ \ \ \ \ (if equal key x then let xcase = m in Ex3 xcase
    else

    \ \ \ \ \ \ \ \ \ \ \ \ let xcase = -1 in Ex3 xcase))) :

    \ \ \ \ \ \ (* k *) ex3) else let xcase = -1 in Ex3 xcase)) in

    \ \ \ \ look key vec 0 (array_length vec + -1) in Ex4 xcase)
  </code>

  <subsection|Program <verbatim|queen>>

  Source file <em|liquid_queen.gadt>:

  <\code>
    external let n2i : <math|\<forall\>>n. Num n <math|\<rightarrow\>> Int =
    "fun i -\<gtr\> i"

    external let equal : <math|\<forall\>>a. a <math|\<rightarrow\>> a
    <math|\<rightarrow\>> Bool = "fun x y -\<gtr\> x = y"

    external let leq : <math|\<forall\>>a. a <math|\<rightarrow\>> a
    <math|\<rightarrow\>> Bool = "fun x y -\<gtr\> x \<less\>= y"

    \;

    external let print : String <math|\<rightarrow\>> () = "print_string"

    external let string_make : Int <math|\<rightarrow\>> String
    <math|\<rightarrow\>> String =

    \ \ "fun n s -\> String.make n s.[0]"

    external let abs : Int <math|\<rightarrow\>> Int = "fun i -\<gtr\> if i
    \<less\> 0 then ~-i else i"

    external let minus : Int <math|\<rightarrow\>> Int <math|\<rightarrow\>>
    Int = "(-)"

    external let plus : Int <math|\<rightarrow\>> Int <math|\<rightarrow\>>
    Int = "(+)"

    \;

    let queens size =

    \ \ let board = array_make size (n2i 0) in

    \ \ let print_row pos =

    \ \ \ \ print (string_make (minus pos (n2i 1)) "."); print "Q";

    \ \ \ \ print (string_make (minus (n2i size) pos) ".") in

    \ \ let print_queens () =

    \ \ \ \ let rec aux row =

    \ \ \ \ \ \ if size \<less\>= row then ()

    \ \ \ \ \ \ else (print_row (array_get board row); aux (row + 1)) in

    \ \ \ \ aux 0 in

    \ \ let rec solved j =

    \ \ \ \ let q2j = array_get board j in

    \ \ \ \ let rec aux i =

    \ \ \ \ \ \ if i + 1 \<less\>= j then

    \ \ \ \ \ \ \ \ let q2i = array_get board i in

    \ \ \ \ \ \ \ \ let qdiff = abs (minus q2j q2i) in

    \ \ \ \ \ \ \ \ if equal q2i q2j then False

    \ \ \ \ \ \ \ \ else if equal qdiff (n2i (j - i)) then False

    \ \ \ \ \ \ \ \ else aux (i + 1)

    \ \ \ \ \ \ else True in

    \ \ \ \ aux 0 in

    \ \ let rec loop row =

    \ \ \ \ let next = plus (array_get board row) (n2i 1) in

    \ \ \ \ if leq (n2i (size + 1)) next then (

    \ \ \ \ \ \ array_set board row (n2i 0);

    \ \ \ \ \ \ if row \<less\>= 0 then () else loop (row - 1))

    \ \ \ \ else (

    \ \ \ \ \ \ array_set board row next;

    \ \ \ \ \ \ if solved row then

    \ \ \ \ \ \ \ \ if size \<less\>= row + 1 then (print_queens (); loop
    row)

    \ \ \ \ \ \ \ \ else loop (row + 1)

    \ \ \ \ \ \ else loop row) in

    \ \ loop 0
  </code>

  Value items from <em|liquid_queen.gadti.target>:

  <\code>
    val queens : <math|\<forall\>>n[1 <math|\<leqslant\>> n]. Num n
    <math|\<rightarrow\>> ()
  </code>

  <subsection|Function <verbatim|swap_interval>>

  Source file <em|liquid_vecswap.gadt>:

  <\code>
    let swap_interval arr start middle n =

    \ \ let rec item i = array_get arr i in

    \ \ let rec swap i j =

    \ \ \ \ let tmpj = item j in

    \ \ \ \ let tmpi = item i in

    \ \ \ \ array_set arr i tmpj; array_set arr j tmpi in

    \ \ let rec vecswap i j n =

    \ \ \ \ if n \<less\>= 0 then () else (

    \ \ \ \ \ \ swap i j; vecswap (i + 1) (j + 1) (n - 1)) in

    \ \ vecswap start middle n
  </code>

  Value items from <em|liquid_vecswap.gadti.target>:

  <\code>
    val swap_interval :

    \ \ \ <math|\<forall\>>i, j, k, n, a[1 <math|\<leqslant\>> j
    <math|\<wedge\>> 0 <math|\<leqslant\>> n <math|\<wedge\>> 0
    <math|\<leqslant\>> k <math|\<wedge\>> i + k <math|\<leqslant\>> j
    <math|\<wedge\>>

    \ \ \ i + n <math|\<leqslant\>> j]. Array (a, j) <math|\<rightarrow\>>
    Num n <math|\<rightarrow\>> Num k <math|\<rightarrow\>> Num i
    <math|\<rightarrow\>> ()
  </code>

  <subsection|Program <verbatim|isort>>

  Source file <em|liquid_isort_harder.gadt>:

  <\code>
    datatype LinOrder

    datacons LE : LinOrder

    datacons GT : LinOrder

    datacons EQ : LinOrder

    \;

    external let compare : <math|\<forall\>>a. a <math|\<rightarrow\>> a
    <math|\<rightarrow\>> LinOrder =

    \ \ "fun a b -\> let c = Pervasives.compare a b in

    \ \ \ \ \ \ \ \ \ \ \ \ \ \ if c \<less\> 0 then LE else if c \> 0 then
    GT else EQ"

    external let equal : <math|\<forall\>>a. a <math|\<rightarrow\>> a
    <math|\<rightarrow\>> Bool = "fun a b -\<gtr\> a = b"

    \;

    let rec insertSort arr start n =

    \ \ let rec item i = array_get arr i in

    \ \ let rec swap i j =

    \ \ \ \ let tmpj = item j in

    \ \ \ \ let tmpi = item i in

    \ \ \ \ array_set arr i tmpj; array_set arr j tmpi in

    \ \ let rec outer i =

    \ \ \ \ if start + n \<less\>= i then ()

    \ \ \ \ else

    \ \ \ \ \ \ let rec inner j =

    \ \ \ \ \ \ \ \ if j \<less\>= start then outer (i + 1)

    \ \ \ \ \ \ \ \ else if equal (compare (item j) (item (j - 1))) LE

    \ \ \ \ \ \ \ \ then (swap j (j - 1); inner (j - 1))

    \ \ \ \ \ \ \ \ else outer (i + 1) in

    \ \ \ \ \ \ inner i in

    \ \ outer (start + 1)
  </code>

  Value items from <em|liquid_isort_harder.gadti.target>:

  <\code>
    val insertSort :

    \ \ \ <math|\<forall\>>i, k, n, a[0 <math|\<leqslant\>> k
    <math|\<wedge\>> 1 <math|\<leqslant\>> i <math|\<wedge\>> k + n
    <math|\<leqslant\>> i].

    \ \ \ Array (a, i) <math|\<rightarrow\>> Num k <math|\<rightarrow\>> Num
    n <math|\<rightarrow\>> ()
  </code>

  <subsection|Program <verbatim|tower>>

  Source file <em|liquid_tower.gadt>:

  <\code>
    external let n2i : <math|\<forall\>>n. Num n <math|\<rightarrow\>> Int =
    "fun i -\<gtr\> i"

    external let equal : <math|\<forall\>>a. a <math|\<rightarrow\>> a
    <math|\<rightarrow\>> Bool = "fun x y -\<gtr\> x = y"

    external let leq : <math|\<forall\>>a. a <math|\<rightarrow\>> a
    <math|\<rightarrow\>> Bool = "fun x y -\<gtr\> x \<less\>= y"

    \;

    external let print : String <math|\<rightarrow\>> () = "print_string"

    external let string_make : Int <math|\<rightarrow\>> String
    <math|\<rightarrow\>> String =

    \ \ "fun n s -\> String.make n s.[0]"

    external let string_of_int : Int <math|\<rightarrow\>> String =
    "string_of_int"

    \;

    external let abs : Int <math|\<rightarrow\>> Int = "fun i -\<gtr\> if i
    \<less\> 0 then ~-i else i"

    external let minus : Int <math|\<rightarrow\>> Int <math|\<rightarrow\>>
    Int = "(-)"

    external let plus : Int <math|\<rightarrow\>> Int <math|\<rightarrow\>>
    Int = "(+)"

    external let int0 : Int = "0"

    \;

    let play sz =

    \ \ let leftPost = array_make sz int0 in

    \ \ let middlePost = array_make sz int0 in

    \ \ let rightPost = array_make sz int0 in

    \;

    \ \ let initialize post =

    \ \ \ \ let rec init_rec i =

    \ \ \ \ \ \ if i + 1 \<less\>= sz - 1 then (

    \ \ \ \ \ \ \ \ array_set post i (n2i (i+1));

    \ \ \ \ \ \ \ \ init_rec (i+1))

    \ \ \ \ \ \ else () in

    \ \ \ \ init_rec 0 in

    \;

    \ \ let showpiece n =

    \ \ \ \ let rec r_rec i =

    \ \ \ \ \ \ if leq (plus i (n2i 2)) n then (

    \ \ \ \ \ \ \ \ print " "; r_rec (plus i (n2i 1)))

    \ \ \ \ \ \ else () in

    \ \ \ \ let rec r2_rec j =

    \ \ \ \ \ \ if leq (plus j (n2i 1)) (n2i sz)

    \ \ \ \ \ \ then (print "#"; r2_rec (plus j (n2i 1)))

    \ \ \ \ \ \ else () in

    \ \ \ \ r_rec (n2i 1);

    \ \ \ \ r2_rec (plus n (n2i 1)) in

    \;

    \ \ let showposts () =

    \ \ \ \ let rec show_rec i =

    \ \ \ \ \ \ if i + 1 \<less\>= sz - 1 then (

    \ \ \ \ \ \ \ \ showpiece (array_get leftPost i); print " ";

    \ \ \ \ \ \ \ \ showpiece (array_get middlePost i); print " ";

    \ \ \ \ \ \ \ \ showpiece (array_get rightPost i); print "\\n";

    \ \ \ \ \ \ \ \ show_rec (i+1))

    \ \ \ \ \ \ else () in

    \ \ \ \ show_rec 0; print "\\n" in

    \;

    \ \ initialize leftPost;

    \ \ let rec move n source s post p post' p' =

    \ \ \ \ if n \<less\>= 1 then (

    \ \ \ \ \ \ array_set post (p - 1) (array_get source s);

    \ \ \ \ \ \ array_set source s int0; showposts ())

    \ \ \ \ else (

    \ \ \ \ \ \ move (n - 1) source s post' p' post p;

    \ \ \ \ \ \ array_set post (p - 1) (array_get source (s + n - 1));

    \ \ \ \ \ \ array_set source (s + n - 1) int0;

    \ \ \ \ \ \ showposts ();

    \ \ \ \ \ \ move (n - 1) post' ((p' - n) + 1) post (p - 1) source (s +
    n)) in

    \;

    \ \ showposts ();

    \ \ move sz leftPost 0 rightPost sz middlePost sz
  </code>

  Value items from <em|liquid_tower.gadti.target>:

  <\code>
    val play : <math|\<forall\>>n[1 <math|\<leqslant\>> n]. Num n
    <math|\<rightarrow\>> ()
  </code>

  <subsection|Program <verbatim|matmult>>

  Source file <em|liquid_matmult.gadt>:

  <\code>
    external let n2i : <math|\<forall\>>n. Num n <math|\<rightarrow\>> Int =
    "fun i -\<gtr\> i"

    external let equal : <math|\<forall\>>a. a <math|\<rightarrow\>> a
    <math|\<rightarrow\>> Bool = "fun x y -\<gtr\> x = y"

    external let leq : <math|\<forall\>>a. a <math|\<rightarrow\>> a
    <math|\<rightarrow\>> Bool = "fun x y -\<gtr\> x \<less\>= y"

    \;

    external let abs : Int <math|\<rightarrow\>> Int = "fun i -\<gtr\> if i
    \<less\> 0 then ~-i else i"

    external let minus : Int <math|\<rightarrow\>> Int <math|\<rightarrow\>>
    Int = "(-)"

    external let plus : Int <math|\<rightarrow\>> Int <math|\<rightarrow\>>
    Int = "(+)"

    external let mult : Int <math|\<rightarrow\>> Int <math|\<rightarrow\>>
    Int = "( * )"

    external let int0 : Int = "0"

    \;

    let fillar arr2 fill =

    \ \ let d1 = matrix_dim1 arr2 in

    \ \ let d2 = matrix_dim2 arr2 in

    \ \ let rec loop i =

    \ \ \ \ if i + 1 \<less\>= d1\ 

    \ \ \ \ then

    \ \ \ \ \ \ let rec loopi j =

    \ \ \ \ \ \ \ \ if j + 1 \<less\>= d2 then (

    \ \ \ \ \ \ \ \ \ \ matrix_set arr2 i j (fill ());

    \ \ \ \ \ \ \ \ \ \ loopi (j + 1))

    \ \ \ \ \ \ \ \ else () in

    \ \ \ \ \ \ loopi 0

    \ \ \ \ else loop (i + 1) in

    \ \ loop 0

    \;

    let matmul a b =

    \ \ let p = matrix_dim1 a in

    \ \ let q = matrix_dim2 a in

    \ \ let r = matrix_dim2 b in

    \;

    \ \ let cdata = matrix_make p r in

    \ \ let callback0 () = int0 in

    \ \ fillar cdata callback0;

    \;

    \ \ let rec loop1 i =

    \ \ \ \ if i + 1 \<less\>= p then (

    \ \ \ \ \ \ let rec loop2 j =

    \ \ \ \ \ \ \ \ if j + 1 \<less\>= r then (

    \ \ \ \ \ \ \ \ \ \ let rec loop3 k sum =

    \ \ \ \ \ \ \ \ \ \ \ \ if k + 1 \<less\>= q then (

    \ \ \ \ \ \ \ \ \ \ \ \ \ \ let sum_p =

    \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ plus sum (mult (matrix_get a i k)
    (matrix_get b k j)) in

    \ \ \ \ \ \ \ \ \ \ \ \ \ \ loop3 (k + 1) sum_p)

    \ \ \ \ \ \ \ \ \ \ \ \ else sum in

    \ \ \ \ \ \ \ \ \ \ let l3 = loop3 0 int0 in

    \ \ \ \ \ \ \ \ \ \ matrix_set cdata i j l3;

    \ \ \ \ \ \ \ \ \ \ loop2 (j + 1))

    \ \ \ \ \ \ \ \ else () in

    \ \ \ \ \ \ loop2 0;

    \ \ \ \ \ \ loop1 (i + 1))

    \ \ \ \ else () in

    \ \ loop1 0;

    \ \ cdata
  </code>

  Value items from <em|liquid_matmult.gadti.target>:

  <\code>
    val fillar :

    \ \ \ <math|\<forall\>>k, n[0 <math|\<leqslant\>> n <math|\<wedge\>> 0
    <math|\<leqslant\>> k]. Matrix (n, k) <math|\<rightarrow\>> (()
    <math|\<rightarrow\>> Int) <math|\<rightarrow\>> ()

    \;

    val matmul :

    \ \ \ <math|\<forall\>>i, j, k, n[0 <math|\<leqslant\>> n
    <math|\<wedge\>> 0 <math|\<leqslant\>> k <math|\<wedge\>> 0
    <math|\<leqslant\>> j <math|\<wedge\>> j <math|\<leqslant\>> i].

    \ \ \ Matrix (n, j) <math|\<rightarrow\>> Matrix (i, k)
    <math|\<rightarrow\>> Matrix (n, k)
  </code>

  <subsection|Program <verbatim|heapsort>>

  Source file <em|liquid_heapsort.gadt>:

  <\code>
    external let div2 : <math|\<forall\>>n. Num (2 n) <math|\<rightarrow\>>
    Num n = "fun x -\<gtr\> x / 2"

    \;

    external let n2i : <math|\<forall\>>n. Num n <math|\<rightarrow\>> Int =
    "fun i -\<gtr\> i"

    external let equal : <math|\<forall\>>a. a <math|\<rightarrow\>> a
    <math|\<rightarrow\>> Bool = "fun x y -\<gtr\> x = y"

    external let leq : <math|\<forall\>>a. a <math|\<rightarrow\>> a
    <math|\<rightarrow\>> Bool = "fun x y -\<gtr\> x \<less\>= y"

    external let less : <math|\<forall\>>a. a <math|\<rightarrow\>> a
    <math|\<rightarrow\>> Bool = "fun x y -\<gtr\> x \<less\> y"

    \;

    external let print : String <math|\<rightarrow\>> () = "print_string"

    external let string_make : Int <math|\<rightarrow\>> String
    <math|\<rightarrow\>> String =

    \ \ "fun n s -\> String.make n s.[0]"

    external let string_of_int : Int <math|\<rightarrow\>> String =
    "string_of_int"

    \;

    external let abs : Int <math|\<rightarrow\>> Int = "fun i -\<gtr\> if i
    \<less\> 0 then ~-i else i"

    external let minus : Int <math|\<rightarrow\>> Int <math|\<rightarrow\>>
    Int = "(-)"

    external let plus : Int <math|\<rightarrow\>> Int <math|\<rightarrow\>>
    Int = "(+)"

    external let int0 : Int = "0"

    \;

    let rec heapify size data i =

    \ \ let left = 2 * i + 1 in

    \ \ let right = 2 * i + 2 in

    \ \ let largest1 =

    \ \ \ \ eif left + 1 \<less\>= size then

    \ \ \ \ \ \ eif less (array_get data i) (array_get data left)

    \ \ \ \ \ \ then left else i

    \ \ \ \ else i in

    \ \ let largest2 =

    \ \ \ \ eif right + 1 \<less\>= size then

    \ \ \ \ \ \ eif less (array_get data largest1) (array_get data right)
    then right

    \ \ \ \ \ \ else largest1

    \ \ \ \ else largest1 in

    \ \ if i + 1 \<less\>= largest2 then

    \ \ \ \ let temp = array_get data i in

    \ \ \ \ let temp2 = array_get data largest2 in

    \ \ \ \ array_set data i temp2;

    \ \ \ \ array_set data largest2 temp;

    \ \ \ \ heapify size data largest2

    \ \ else ()

    (* We do not get the constraint [i + 1 \<= size], because if [i] is
    larger,

    \ \ \ the last [else] branch is entered. *)

    \;

    let buildheap size data =

    \ \ let rec loop i =

    \ \ \ \ if 0 \<less\>= i then (

    \ \ \ \ \ \ heapify size data i;

    \ \ \ \ \ \ loop (i - 1))

    \ \ \ \ else () in

    \ \ loop (div2 size - 1)

    \;

    let heapsort maxx size data =

    \ \ buildheap size data;

    \ \ let rec loop i =

    \ \ \ \ if 1 \<less\>= i then

    \ \ \ \ \ \ let temp = array_get data i in

    \ \ \ \ \ \ array_set data i (array_get data 0);

    \ \ \ \ \ \ array_set data 0 temp;

    \ \ \ \ \ \ heapify i data 0;

    \ \ \ \ \ \ loop (i - 1)

    \ \ \ \ else () in

    \ \ loop (maxx - 1)

    \;

    let print_array data i j =

    \ \ let rec loop k =

    \ \ \ \ if k + 1 \<less\>= j then (

    \ \ \ \ \ \ print (array_get data k);

    \ \ \ \ \ \ loop (k + 1))

    \ \ \ \ else () in

    \ \ loop i
  </code>

  Value items from <em|liquid_heapsort.gadti.target>:

  <\code>
    val heapify :

    \ \ \ <math|\<forall\>>i, k, n, a[0 <math|\<leqslant\>> n
    <math|\<wedge\>> i <math|\<leqslant\>> k].

    \ \ \ Num i <math|\<rightarrow\>> Array (a, k) <math|\<rightarrow\>> Num
    n <math|\<rightarrow\>> ()

    \;

    val buildheap : <math|\<forall\>>k, n, a[k <math|\<leqslant\>> n]. Num k
    <math|\<rightarrow\>> Array (a, n) <math|\<rightarrow\>> ()

    \;

    val heapsort :

    \ \ \ <math|\<forall\>>i, k, n, a[k <math|\<leqslant\>> n
    <math|\<wedge\>> i <math|\<leqslant\>> k].

    \ \ \ Num i <math|\<rightarrow\>> Num k <math|\<rightarrow\>> Array (a,
    n) <math|\<rightarrow\>> ()

    \;

    val print_array :

    \ \ \ <math|\<forall\>>i, k, n[k <math|\<leqslant\>> i <math|\<wedge\>> 0
    <math|\<leqslant\>> n].

    \ \ \ Array (String, i) <math|\<rightarrow\>> Num n <math|\<rightarrow\>>
    Num k <math|\<rightarrow\>> ()
  </code>

  <subsection|Program <verbatim|simplex>>

  Source file <em|liquid_simplex.gadt>:

  <\code>
    external let n2f : <math|\<forall\>>n. Num n <math|\<rightarrow\>> Float
    = "float_of_int"

    external let equal : <math|\<forall\>>a. a <math|\<rightarrow\>> a
    <math|\<rightarrow\>> Bool = "fun x y -\<gtr\> x = y"

    external let leq : <math|\<forall\>>a. a <math|\<rightarrow\>> a
    <math|\<rightarrow\>> Bool = "fun x y -\<gtr\> x \<less\>= y"

    external let less : <math|\<forall\>>a. a <math|\<rightarrow\>> a
    <math|\<rightarrow\>> Bool = "fun x y -\<gtr\> x \<less\> y"

    \;

    external let minus : Float <math|\<rightarrow\>> Float
    <math|\<rightarrow\>> Float = "(-.)"

    external let plus : Float <math|\<rightarrow\>> Float
    <math|\<rightarrow\>> Float = "(+.)"

    external let mult : Float <math|\<rightarrow\>> Float
    <math|\<rightarrow\>> Float = "( *. )"

    external let div : Float <math|\<rightarrow\>> Float
    <math|\<rightarrow\>> Float = "( /. )"

    external let fl0 : Float = "0.0"

    \;

    (* step 1 *)

    \;

    let rec is_neg_aux a j =

    \ \ if j + 2 \<less\>= matrix_dim2 a then

    \ \ \ \ if less (matrix_get a 0 j) fl0 then True

    \ \ \ \ else is_neg_aux a (j+1)

    \ \ else False

    \;

    let is_neg a = is_neg_aux a 1

    \;

    (* step 2 *)

    \;

    let rec unb1 a i j =

    \ \ let rec unb2 a i j =

    \ \ \ \ if i + 1 \<less\>= matrix_dim1 a then

    \ \ \ \ \ \ if less (matrix_get a i j) fl0

    \ \ \ \ \ \ then unb2 a (i+1) j

    \ \ \ \ \ \ else unb1 a 0 (j+1)

    \ \ \ \ else True in

    \;

    \ \ if j + 2 \<less\>= matrix_dim2 a then

    \ \ \ \ if less (matrix_get a 0 j) fl0

    \ \ \ \ then unb2 a (i+1) j

    \ \ \ \ else unb1 a 0 (j+1)

    \ \ else False

    \;

    (* step 6 *)

    \;

    let rec norm_aux a i c j =

    \ \ if j + 1 \<less\>= matrix_dim2 a then (

    \ \ \ \ matrix_set a i j (div (matrix_get a i j) c);

    \ \ \ \ norm_aux a i c (j+1))

    \ \ else ()

    \;

    let rec norm a i j =

    \ \ let c = matrix_get a i j in

    \ \ norm_aux a i c 1

    \;

    let rec row_op_aux1 a i i' c j =

    \ \ if j + 1 \<less\>= matrix_dim2 a then

    \ \ \ \ matrix_set a i' j

    \ \ \ \ \ \ (minus (matrix_get a i' j)

    \ \ \ \ \ \ \ \ (mult (matrix_get a i j) c));

    \ \ \ \ row_op_aux1 a i i' c (j+1)

    \ \ else ()

    \;

    let rec row_op_aux2 a i i' j =

    \ \ row_op_aux1 a i i' (matrix_get a i' j) 1

    \;

    let rec row_op_aux3 a i j i' =

    \ \ if i' + 1 \<less\>= matrix_dim1 a then

    \ \ \ \ if i' \<less\>= i && i \<less\>= i' then (

    \ \ \ \ \ \ row_op_aux2 a i i' j;

    \ \ \ \ \ \ row_op_aux3 a i j (i'+1))

    \ \ \ \ else row_op_aux3 a i j (i'+1)

    \ \ else ()

    \;

    let rec row_op a i j =

    \ \ norm a i j;

    \ \ row_op_aux3 a i j 0

    \;

    let rec simplex a =

    \;

    \ \ (* step 3 *)

    \;

    \ \ let rec enter_var j c j' =

    \ \ \ \ eif j' + 2 \<less\>= matrix_dim2 a then

    \ \ \ \ \ \ let c' = matrix_get a 0 j' in

    \ \ \ \ \ \ eif less c' c then enter_var j' c' (j'+1)

    \ \ \ \ \ \ else enter_var j c (j'+1)

    \ \ \ \ else j in

    \;

    \ \ (* step 4 *)

    \;

    \ \ let rec depart_var j i r i' =

    \ \ \ \ eif i' + 1 \<less\>= matrix_dim1 a then

    \ \ \ \ \ \ let c' = matrix_get a i' j in

    \ \ \ \ \ \ eif less fl0 c' then

    \ \ \ \ \ \ \ \ let r' = div (matrix_get a i' (matrix_dim2 a + (-1))) c'
    in

    \ \ \ \ \ \ \ \ eif less r' r then depart_var j i' r' (i'+1)

    \ \ \ \ \ \ \ \ else depart_var j i r (i'+1)

    \ \ \ \ \ \ else depart_var j i r (i'+1)

    \ \ \ \ else i in

    \;

    \ \ (* step 5 *)

    \;

    \ \ let rec init_ratio j i =

    \ \ \ \ eif i + 1 \<less\>= matrix_dim1 a then

    \ \ \ \ \ \ let c = matrix_get a i j in

    \ \ \ \ \ \ eif less fl0 c then i, div (matrix_get a i (matrix_dim2 a +
    (-1))) c

    \ \ \ \ \ \ else init_ratio j (i+1)

    \ \ \ \ else runtime_failure "init_ratio: no variable found" in

    \;

    \ \ (* step 7 *)

    \;

    \ \ if is_neg a then

    \ \ \ \ if unb1 a 0 1 then () (* assert false *)

    \ \ \ \ else

    \ \ \ \ \ \ let j = enter_var 1 (matrix_get a 0 1) 2 in

    \ \ \ \ \ \ let i, r = init_ratio j 1 in

    \ \ \ \ \ \ let i = depart_var j i r (i+1) in

    \ \ \ \ \ \ row_op a i j;

    \ \ \ \ \ \ simplex a

    \ \ else ()
  </code>

  The file <em|liquid_simplex_harder.gadt> has the above steps in order as
  part of a single toplevel definition. Value items from
  <em|liquid_simplex.gadti.target>:

  <\code>
    val is_neg_aux :

    \ \ \ <math|\<forall\>>i, k, n[0 <math|\<leqslant\>> n <math|\<wedge\>> 1
    <math|\<leqslant\>> k <math|\<wedge\>> 0 <math|\<leqslant\>> i].

    \ \ \ Matrix (k, i) <math|\<rightarrow\>> Num n <math|\<rightarrow\>>
    Bool

    \;

    val is_neg : <math|\<forall\>>k, n[1 <math|\<leqslant\>> n
    <math|\<wedge\>> 0 <math|\<leqslant\>> k]. Matrix (n, k)
    <math|\<rightarrow\>> Bool

    \;

    val unb1 :

    \ \ \ <math|\<forall\>>i, j, k, n[0 <math|\<leqslant\>> n
    <math|\<wedge\>> 0 <math|\<leqslant\>> k + 1 <math|\<wedge\>> 1
    <math|\<leqslant\>> i <math|\<wedge\>> 0 <math|\<leqslant\>> j].

    \ \ \ Matrix (i, j) <math|\<rightarrow\>> Num k <math|\<rightarrow\>> Num
    n <math|\<rightarrow\>> Bool

    \;

    val norm_aux :

    \ \ \ <math|\<forall\>>i, j, k, n[0 <math|\<leqslant\>> n
    <math|\<wedge\>> 0 <math|\<leqslant\>> k <math|\<wedge\>> k + 1
    <math|\<leqslant\>> i <math|\<wedge\>> 0 <math|\<leqslant\>> j].

    \ \ \ Matrix (i, j) <math|\<rightarrow\>> Num k <math|\<rightarrow\>>
    Float <math|\<rightarrow\>> Num n <math|\<rightarrow\>> ()

    \;

    val norm :

    \ \ \ <math|\<forall\>>i, j, k, n[0 <math|\<leqslant\>> n
    <math|\<wedge\>> 0 <math|\<leqslant\>> k <math|\<wedge\>> k + 1
    <math|\<leqslant\>> i <math|\<wedge\>> n + 1 <math|\<leqslant\>> j].

    \ \ \ Matrix (i, j) <math|\<rightarrow\>> Num k <math|\<rightarrow\>> Num
    n <math|\<rightarrow\>> ()

    \;

    val row_op_aux1 :

    \ \ \ <math|\<forall\>>i, j, k, m, n[0 <math|\<leqslant\>> n
    <math|\<wedge\>> 0 <math|\<leqslant\>> k <math|\<wedge\>> 0
    <math|\<leqslant\>> i <math|\<wedge\>> i + 1 <math|\<leqslant\>> j
    <math|\<wedge\>>

    \ \ \ k + 1 <math|\<leqslant\>> j <math|\<wedge\>> 0 <math|\<leqslant\>>
    m].

    \ \ \ Matrix (j, m) <math|\<rightarrow\>> Num i <math|\<rightarrow\>> Num
    k <math|\<rightarrow\>> Float <math|\<rightarrow\>> Num n
    <math|\<rightarrow\>> ()

    \;

    val row_op_aux2 :

    \ \ \ <math|\<forall\>>i, j, k, m, n[0 <math|\<leqslant\>> n
    <math|\<wedge\>> 0 <math|\<leqslant\>> k <math|\<wedge\>> 0
    <math|\<leqslant\>> i <math|\<wedge\>> i + 1 <math|\<leqslant\>> j
    <math|\<wedge\>>

    \ \ \ k + 1 <math|\<leqslant\>> j <math|\<wedge\>> n + 1
    <math|\<leqslant\>> m].

    \ \ \ Matrix (j, m) <math|\<rightarrow\>> Num i <math|\<rightarrow\>> Num
    k <math|\<rightarrow\>> Num n <math|\<rightarrow\>> ()

    \;

    val row_op_aux3 :

    \ \ \ <math|\<forall\>>i, j, k, m, n[0 <math|\<leqslant\>> k
    <math|\<wedge\>> 0 <math|\<leqslant\>> i <math|\<wedge\>> 0
    <math|\<leqslant\>> j <math|\<wedge\>> k + 1 <math|\<leqslant\>> m].

    \ \ \ Matrix (j, m) <math|\<rightarrow\>> Num i <math|\<rightarrow\>> Num
    k <math|\<rightarrow\>> Num n <math|\<rightarrow\>> ()

    \;

    val row_op :

    \ \ \ <math|\<forall\>>i, j, k, n[0 <math|\<leqslant\>> n
    <math|\<wedge\>> 0 <math|\<leqslant\>> k <math|\<wedge\>> k + 1
    <math|\<leqslant\>> i <math|\<wedge\>> n + 1 <math|\<leqslant\>> j].

    \ \ \ Matrix (i, j) <math|\<rightarrow\>> Num k <math|\<rightarrow\>> Num
    n <math|\<rightarrow\>> ()

    \;

    val simplex : <math|\<forall\>>k, n[1 <math|\<leqslant\>> n
    <math|\<wedge\>> 2 <math|\<leqslant\>> k]. Matrix (n, k)
    <math|\<rightarrow\>> ()
  </code>

  Exported OCaml source <em|liquid_simplex.ml.target>:

  <\code>
    type num = int

    type matrix =

    \ \ (float, Bigarray.float64_elt, Bigarray.c_layout) Bigarray.Array2.t

    let matrix_make :

    \ \ (*0 <math|\<leqslant\>> n <math|\<wedge\>> 0 <math|\<leqslant\>> k*)
    ((* n *) num -\<gtr\> (* k *) num -\<gtr\> (* n, k *) matrix) =

    \ \ fun a b -\> Bigarray.Array2.create Bigarray.float64 Bigarray.c_layout
    a b

    let matrix_get :

    \ \ (*0 <math|\<leqslant\>> i <math|\<wedge\>> i + 1 <math|\<leqslant\>>
    n <math|\<wedge\>> 0 <math|\<leqslant\>> j <math|\<wedge\>> j + 1
    <math|\<leqslant\>> k*)

    \ \ ((* n, k *) matrix -\> (* i *) num -\> (* j *) num -\> float) =

    \ \ Bigarray.Array2.get

    let matrix_set :

    \ \ (*0 <math|\<leqslant\>> i <math|\<wedge\>> i + 1 <math|\<leqslant\>>
    n <math|\<wedge\>> 0 <math|\<leqslant\>> j <math|\<wedge\>> j + 1
    <math|\<leqslant\>> k*)

    \ \ ((* n, k *) matrix -\> (* i *) num -\> (* j *) num -\> float -\>
    unit) =

    \ \ Bigarray.Array2.set

    let matrix_dim1 :

    \ \ (*0 <math|\<leqslant\>> n <math|\<wedge\>> 0 <math|\<leqslant\>> k*)
    ((* n, k *) matrix -\<gtr\> (* n *) num) =

    \ \ Bigarray.Array2.dim1

    let matrix_dim2 :

    \ \ (*0 <math|\<leqslant\>> n <math|\<wedge\>> 0 <math|\<leqslant\>> k*)
    ((* n, k *) matrix -\<gtr\> (* k *) num) =

    \ \ Bigarray.Array2.dim2

    let n2f : ((* n *) num -\> float) = float_of_int

    let equal : ('a -\> 'a -\> bool) = fun x y -\> x = y

    let leq : ('a -\> 'a -\> bool) = fun x y -\> x \<= y

    let less : ('a -\> 'a -\> bool) = fun x y -\> x \< y

    let minus : (float -\> float -\> float) = (-.)

    let plus : (float -\> float -\> float) = (+.)

    let mult : (float -\> float -\> float) = ( *. )

    let div : (float -\> float -\> float) = ( /. )

    let fl0 : float = 0.0

    let rec is_neg_aux :

    \ \ (*type i k n [0 <math|\<leqslant\>> n <math|\<wedge\>> 1
    <math|\<leqslant\>> k <math|\<wedge\>>

    \ \ \ \ 0 <math|\<leqslant\>> i].*) ((* k, i *) matrix -\<gtr\> (* n *)
    num -\<gtr\> bool) =

    \ \ (fun a j -\>

    \ \ \ \ (if j + 2 \<less\>= matrix_dim2 a then

    \ \ \ \ (if less (matrix_get a 0 j) fl0 then true else is_neg_aux a (j +
    1)) else

    \ \ \ \ false))

    let is_neg

    \ \ : (*type k n [1 <math|\<leqslant\>> n <math|\<wedge\>> 0
    <math|\<leqslant\>> k].*) ((* n, k *) matrix -\<gtr\> bool) =

    \ \ (fun a -\> is_neg_aux a 1)

    let rec unb1 :

    \ \ (*type i j k n [0 <math|\<leqslant\>> n <math|\<wedge\>> 0
    <math|\<leqslant\>> k + 1 <math|\<wedge\>> 1 <math|\<leqslant\>> i
    <math|\<wedge\>>

    \ \ \ \ 0 <math|\<leqslant\>> j].*) ((* i, j *) matrix -\<gtr\> (* k *)
    num -\<gtr\> (* n *) num -\<gtr\> bool) =

    \ \ (fun a i j -\>

    \ \ \ \ let rec unb2 :

    \ \ \ \ (*type k1 l m n1 [0 <math|\<leqslant\>> m <math|\<wedge\>> 0
    <math|\<leqslant\>> l <math|\<wedge\>> 0 <math|\<leqslant\>> n1
    <math|\<wedge\>>

    \ \ \ \ \ \ m + 1 <math|\<leqslant\>> k1].*) ((* n1, k1 *) matrix
    -\<gtr\> (* l *) num -\<gtr\> (* m *) num -\<gtr\>

    \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ bool)

    \ \ \ \ =

    \ \ \ \ (fun a i j -\>

    \ \ \ \ \ \ (if i + 1 \<less\>= matrix_dim1 a then

    \ \ \ \ \ \ (if less (matrix_get a i j) fl0 then unb2 a (i + 1) j else

    \ \ \ \ \ \ unb1 a 0 (j + 1)) else true)) in

    \ \ \ \ (if j + 2 \<less\>= matrix_dim2 a then

    \ \ \ \ (if less (matrix_get a 0 j) fl0 then unb2 a (i + 1) j else

    \ \ \ \ unb1 a 0 (j + 1)) else false))

    let rec norm_aux :

    \ \ (*type i j k n [0 <math|\<leqslant\>> n <math|\<wedge\>> 0
    <math|\<leqslant\>> k <math|\<wedge\>> k + 1 <math|\<leqslant\>> i
    <math|\<wedge\>>

    \ \ \ \ 0 <math|\<leqslant\>> j].*) ((* i, j *) matrix -\<gtr\> (* k *)
    num -\<gtr\> float -\<gtr\> (* n *) num -\<gtr\>

    \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ unit) =

    \ \ (fun a i c j -\>

    \ \ \ \ (if j + 1 \<less\>= matrix_dim2 a then

    \ \ \ \ (matrix_set a i j (div (matrix_get a i j) c) ; norm_aux a i c (j
    + 1))

    \ \ \ \ else ()))

    let rec norm :

    \ \ (*type i j k n [0 <math|\<leqslant\>> n <math|\<wedge\>> 0
    <math|\<leqslant\>> k <math|\<wedge\>> k + 1 <math|\<leqslant\>> i
    <math|\<wedge\>>

    \ \ \ \ n + 1 <math|\<leqslant\>> j].*) ((* i, j *) matrix -\<gtr\> (* k
    *) num -\<gtr\> (* n *) num -\<gtr\> unit) =

    \ \ (fun a i j -\> let c = matrix_get a i j in norm_aux a i c 1)

    let rec row_op_aux1 :

    \ \ (*type i j k m n [0 <math|\<leqslant\>> n <math|\<wedge\>> 0
    <math|\<leqslant\>> k <math|\<wedge\>> 0 <math|\<leqslant\>> i
    <math|\<wedge\>> i + 1 <math|\<leqslant\>> j <math|\<wedge\>>

    \ \ \ \ k + 1 <math|\<leqslant\>> j <math|\<wedge\>>

    \ \ \ \ 0 <math|\<leqslant\>> m].*) ((* j, m *) matrix -\<gtr\> (* i *)
    num -\<gtr\> (* k *) num -\<gtr\> float -\<gtr\>

    \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ (* n *) num -\> unit) =

    \ \ (fun a i i' c j -\>

    \ \ \ \ (if j + 1 \<less\>= matrix_dim2 a then

    \ \ \ \ (matrix_set a i' j

    \ \ \ \ \ \ \ (minus (matrix_get a i' j) (mult (matrix_get a i j) c))

    \ \ \ \ ; row_op_aux1 a i i' c (j + 1)) else ()))

    let rec row_op_aux2 :

    \ \ (*type i j k m n [0 <math|\<leqslant\>> n <math|\<wedge\>> 0
    <math|\<leqslant\>> k <math|\<wedge\>> 0 <math|\<leqslant\>> i
    <math|\<wedge\>> i + 1 <math|\<leqslant\>> j <math|\<wedge\>>

    \ \ \ \ k + 1 <math|\<leqslant\>> j <math|\<wedge\>>

    \ \ \ \ n + 1 <math|\<leqslant\>> m].*) ((* j, m *) matrix -\<gtr\> (* i
    *) num -\<gtr\> (* k *) num -\<gtr\>

    \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ (* n *) num -\> unit) =

    \ \ (fun a i i' j -\> row_op_aux1 a i i' (matrix_get a i' j) 1)

    let rec row_op_aux3 :

    \ \ (*type i j k m n [0 <math|\<leqslant\>> k <math|\<wedge\>> 0
    <math|\<leqslant\>> i <math|\<wedge\>> 0 <math|\<leqslant\>> j
    <math|\<wedge\>>

    \ \ \ \ k + 1 <math|\<leqslant\>> m].*) ((* j, m *) matrix -\<gtr\> (* i
    *) num -\<gtr\> (* k *) num -\<gtr\>

    \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ (* n *) num -\> unit) =

    \ \ (fun a i j i' -\>

    \ \ \ \ (if i' + 1 \<less\>= matrix_dim1 a then

    \ \ \ \ (if i \<less\>= i'&& i' \<less\>= i then

    \ \ \ \ (row_op_aux2 a i i' j ; row_op_aux3 a i j (i' + 1)) else

    \ \ \ \ row_op_aux3 a i j (i' + 1)) else ()))

    let rec row_op :

    \ \ (*type i j k n [0 <math|\<leqslant\>> n <math|\<wedge\>> 0
    <math|\<leqslant\>> k <math|\<wedge\>> k + 1 <math|\<leqslant\>> i
    <math|\<wedge\>>

    \ \ \ \ n + 1 <math|\<leqslant\>> j].*) ((* i, j *) matrix -\<gtr\> (* k
    *) num -\<gtr\> (* n *) num -\<gtr\> unit) =

    \ \ (fun a i j -\> (norm a i j ; row_op_aux3 a i j 0))

    type ex7 =

    \ \ \| Ex7 : (*<math|\<forall\>>'i, 'k, 'n[k <math|\<leqslant\>> i
    <math|\<wedge\>> i + 1 <math|\<leqslant\>> n].*)((* i *) num * float)
    -\<gtr\>

    \ \ \ \ (* n, k *) ex7

    type ex5 =

    \ \ \| Ex5 : (*<math|\<forall\>>'i, 'k, 'n[0 <math|\<leqslant\>> k
    <math|\<wedge\>> k<math|\<leqslant\>>max (i, n + -1)].*)(* k *) num
    -\<gtr\>

    \ \ \ \ (* n, i *) ex5

    type ex2 =

    \ \ \| Ex2 : (*<math|\<forall\>>'i, 'k, 'n[0 <math|\<leqslant\>> k
    <math|\<wedge\>> k<math|\<leqslant\>>max (i, n + -1)].*)(* k *) num
    -\<gtr\>

    \ \ \ \ (* n, i *) ex2

    let rec simplex :

    \ \ (*type k n [1 <math|\<leqslant\>> n <math|\<wedge\>> 2
    <math|\<leqslant\>> k].*) ((* n, k *) matrix -\<gtr\> unit) =

    \ \ (fun a -\>

    \ \ \ \ let rec enter_var :

    \ \ \ \ (*type i j [0 <math|\<leqslant\>> j <math|\<wedge\>>

    \ \ \ \ \ \ 0 <math|\<leqslant\>> i].*) ((* i *) num -\<gtr\> float
    -\<gtr\> (* j *) num -\<gtr\> (* k, i *) ex2)

    \ \ \ \ =

    \ \ \ \ (fun j c j' -\>

    \ \ \ \ \ \ (if j' + 2 \<less\>= matrix_dim2 a then

    \ \ \ \ \ \ let c' = matrix_get a 0 j' in

    \ \ \ \ \ \ (if less c' c then

    \ \ \ \ \ \ let Ex2 xcase = enter_var j' c' (j' + 1) in Ex2 xcase else

    \ \ \ \ \ \ let Ex2 xcase = enter_var j c (j' + 1) in Ex2 xcase) else

    \ \ \ \ \ \ let xcase = j in Ex2 xcase)) in

    \ \ \ \ let rec depart_var :

    \ \ \ \ (*type l m n1 [0 <math|\<leqslant\>> l <math|\<wedge\>> 0
    <math|\<leqslant\>> n1 <math|\<wedge\>> n1 + 1 <math|\<leqslant\>> k
    <math|\<wedge\>>

    \ \ \ \ \ \ 0 <math|\<leqslant\>> m].*) ((* n1 *) num -\<gtr\> (* m *)
    num -\<gtr\> float -\<gtr\> (* l *) num -\<gtr\>

    \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ (* n, m *) ex5)

    \ \ \ \ =

    \ \ \ \ (fun j i r i' -\>

    \ \ \ \ \ \ (if i' + 1 \<less\>= matrix_dim1 a then

    \ \ \ \ \ \ let c' = matrix_get a i' j in

    \ \ \ \ \ \ (if less fl0 c' then

    \ \ \ \ \ \ let r' = div (matrix_get a i' (matrix_dim2 a + -1)) c' in

    \ \ \ \ \ \ (if less r' r then

    \ \ \ \ \ \ let Ex5 xcase = depart_var j i' r' (i' + 1) in Ex5 xcase else

    \ \ \ \ \ \ let Ex5 xcase = depart_var j i r (i' + 1) in Ex5 xcase) else

    \ \ \ \ \ \ let Ex5 xcase = depart_var j i r (i' + 1) in Ex5 xcase) else

    \ \ \ \ \ \ let xcase = i in Ex5 xcase)) in

    \ \ \ \ let rec init_ratio :

    \ \ \ \ (*type i1 k1 [0 <math|\<leqslant\>> k1 <math|\<wedge\>> 0
    <math|\<leqslant\>> i1 <math|\<wedge\>>

    \ \ \ \ \ \ i1 + 1 <math|\<leqslant\>> k].*) ((* i1 *) num -\<gtr\> (* k1
    *) num -\<gtr\> (* n, k1 *) ex7)

    \ \ \ \ =

    \ \ \ \ (fun j i -\>

    \ \ \ \ \ \ (if i + 1 \<less\>= matrix_dim1 a then

    \ \ \ \ \ \ \ \ let c = matrix_get a i j in

    \ \ \ \ \ \ \ \ (if less fl0 c then

    \ \ \ \ \ \ \ \ let xcase = (i, div (matrix_get a i (matrix_dim2 a + -1))
    c) in

    \ \ \ \ \ \ \ \ Ex7 xcase else let Ex7 xcase = init_ratio j (i + 1) in
    Ex7 xcase)

    \ \ \ \ \ \ else

    \ \ \ \ \ \ \ \ (failwith "init_ratio: no variable found"))) in

    \ \ \ \ (if is_neg a then

    \ \ \ \ (if unb1 a 0 1 then () else

    \ \ \ \ \ \ let Ex2 j = enter_var 1 (matrix_get a 0 1) 2 in

    \ \ \ \ \ \ let Ex7 (i, r) = init_ratio j 1 in

    \ \ \ \ \ \ let Ex5 i = depart_var j i r (i + 1) in (row_op a i j ;
    simplex a))

    \ \ \ \ else

    \ \ \ \ \ \ ()))
  </code>

  <subsection|Program <verbatim|gauss>>

  Source file <em|liquid_gauss.gadt>:

  <\code>
    external let n2f : <math|\<forall\>>n. Num n <math|\<rightarrow\>> Float
    = "float_of_int"

    external let equal : <math|\<forall\>>a. a <math|\<rightarrow\>> a
    <math|\<rightarrow\>> Bool = "fun x y -\<gtr\> x = y"

    external let leq : <math|\<forall\>>a. a <math|\<rightarrow\>> a
    <math|\<rightarrow\>> Bool = "fun x y -\<gtr\> x \<less\>= y"

    external let less : <math|\<forall\>>a. a <math|\<rightarrow\>> a
    <math|\<rightarrow\>> Bool = "fun x y -\<gtr\> x \<less\> y"

    \;

    external let minus : Float <math|\<rightarrow\>> Float
    <math|\<rightarrow\>> Float = "(-.)"

    external let plus : Float <math|\<rightarrow\>> Float
    <math|\<rightarrow\>> Float = "(+.)"

    external let mult : Float <math|\<rightarrow\>> Float
    <math|\<rightarrow\>> Float = "( *. )"

    external let div : Float <math|\<rightarrow\>> Float
    <math|\<rightarrow\>> Float = "( /. )"

    external let fabs : Float <math|\<rightarrow\>> Float = "abs_float"

    external let fl0 : Float = "0.0"

    external let fl1 : Float = "1.0"

    \;

    let getRow data i =

    \ \ let stride = matrix_dim2 data in

    \ \ let rowData = array_make stride fl0 in

    \ \ let rec extract j =

    \ \ \ \ if j + 1 \<less\>= stride then (

    \ \ \ \ \ \ array_set rowData j (matrix_get data i j);

    \ \ \ \ \ \ (* lukstafi: the call below missing in the original source?
    *)

    \ \ \ \ \ \ extract (j + 1))

    \ \ \ \ else () in

    \ \ extract 0;

    \ \ rowData

    \;

    let putRow data i row =

    \ \ let stride = array_length row in

    \ \ let rec put j =

    \ \ \ \ if j + 1 \<less\>= stride then (

    \ \ \ \ \ \ matrix_set data i j (array_get row j);

    \ \ \ \ \ \ (* lukstafi: the call below missing in the original source?
    *)

    \ \ \ \ \ \ put (j + 1))

    \ \ \ \ else () in

    \ \ put 0

    \;

    let rowSwap data i j =

    \ \ let temp = getRow data i in

    \ \ putRow data i (getRow data j);

    \ \ putRow data j temp

    \;

    let norm r n i =

    \ \ let x = array_get r i in

    \ \ array_set r i fl1;

    \ \ let rec loop k =

    \ \ \ \ if k + 1 \<less\>= n then (

    \ \ \ \ \ \ array_set r k (div (array_get r k) x);

    \ \ \ \ \ \ loop (k+1))

    \ \ \ \ else () in

    \ \ loop (i+1)

    \;

    let rowElim r s n i =

    \ \ let x = array_get s i in

    \ \ array_set s i fl0;

    \ \ let rec loop k =

    \ \ \ \ if k + 1 \<less\>= n then (

    \ \ \ \ \ \ array_set s k (minus (array_get s k) (mult x (array_get r
    k)));

    \ \ \ \ \ \ loop (k+1))

    \ \ \ \ else () in

    \ \ loop (i+1)

    \;

    let gauss data =

    \ \ let n = matrix_dim1 data in

    \ \ let m = matrix_dim2 data in

    \;

    \ \ let rec rowMax i j x mx =

    \ \ \ \ eif j + 1 \<less\>= n then

    \ \ \ \ \ \ let y = fabs (matrix_get data j i) in

    \ \ \ \ \ \ eif (less x y) then rowMax i (j+1) y j

    \ \ \ \ \ \ else rowMax i (j+1) x mx

    \ \ \ \ else mx in

    \;

    \ \ let rec loop1 i =

    \ \ \ \ if i + 1 \<less\>= n then

    \ \ \ \ \ \ let x = fabs (matrix_get data i i) in

    \ \ \ \ \ \ let mx = rowMax i (i+1) x i in

    \ \ \ \ \ \ norm (getRow data mx) m i;

    \ \ \ \ \ \ rowSwap data i mx;

    \ \ \ \ \ \ let rec loop2 j =

    \ \ \ \ \ \ \ \ if j + 1 \<less\>= n then (

    \ \ \ \ \ \ \ \ \ \ rowElim (getRow data i) (getRow data j) m i;

    \ \ \ \ \ \ \ \ \ \ loop2 (j+1))

    \ \ \ \ \ \ \ \ else () in

    \ \ \ \ \ \ loop2 (i+1);

    \ \ \ \ \ \ loop1 (i+1)

    \ \ \ \ else () in

    \ \ loop1 0
  </code>

  Value items from <em|liquid_gauss.gadti.target>:

  <\code>
    val getRow :

    \ \ \ <math|\<forall\>>i, k, n[0 <math|\<leqslant\>> n <math|\<wedge\>> 0
    <math|\<leqslant\>> k <math|\<wedge\>> k + 1 <math|\<leqslant\>> i].

    \ \ \ Matrix (i, n) <math|\<rightarrow\>> Num k <math|\<rightarrow\>>
    Array (Float, n)

    \;

    val putRow :

    \ \ \ <math|\<forall\>>i, j, k, n[0 <math|\<leqslant\>> n
    <math|\<wedge\>> 0 <math|\<leqslant\>> k <math|\<wedge\>> k + 1
    <math|\<leqslant\>> i <math|\<wedge\>> n <math|\<leqslant\>> j].

    \ \ \ Matrix (i, j) <math|\<rightarrow\>> Num k <math|\<rightarrow\>>
    Array (Float, n) <math|\<rightarrow\>> ()

    \;

    val rowSwap :

    \ \ \ <math|\<forall\>>i, j, k, n[0 <math|\<leqslant\>> n
    <math|\<wedge\>> 0 <math|\<leqslant\>> k <math|\<wedge\>> k + 1
    <math|\<leqslant\>> i <math|\<wedge\>> n + 1 <math|\<leqslant\>> i
    <math|\<wedge\>>

    \ \ \ 0 <math|\<leqslant\>> j]. Matrix (i, j) <math|\<rightarrow\>> Num k
    <math|\<rightarrow\>> Num n <math|\<rightarrow\>> ()

    \;

    val norm :

    \ \ \ <math|\<forall\>>i, k, n[0 <math|\<leqslant\>> n <math|\<wedge\>> n
    + 1 <math|\<leqslant\>> i <math|\<wedge\>> k <math|\<leqslant\>> i].

    \ \ \ Array (Float, i) <math|\<rightarrow\>> Num k <math|\<rightarrow\>>
    Num n <math|\<rightarrow\>> ()

    \;

    val rowElim :

    \ \ \ <math|\<forall\>>i, j, k, n[0 <math|\<leqslant\>> n
    <math|\<wedge\>> n + 1 <math|\<leqslant\>> i <math|\<wedge\>> k
    <math|\<leqslant\>> i <math|\<wedge\>> k <math|\<leqslant\>> j].

    \ \ \ Array (Float, j) <math|\<rightarrow\>> Array (Float, i)
    <math|\<rightarrow\>> Num k <math|\<rightarrow\>> Num n
    <math|\<rightarrow\>> ()

    \;

    val gauss : <math|\<forall\>>k, n[0 <math|\<leqslant\>> n
    <math|\<wedge\>> 1 <math|\<leqslant\>> k <math|\<wedge\>> n
    <math|\<leqslant\>> k]. Matrix (n, k) <math|\<rightarrow\>> ()
  </code>

  The last toplevel definition from <em|liquid_gauss2.gadt>, requires
  <verbatim|-prefer_bound_to_local>:

  <\code>
    let gauss data =

    \ \ let n = matrix_dim1 data in

    \;

    \ \ let rec rowMax i j x mx =

    \ \ \ \ eif j + 1 \<= n then

    \ \ \ \ \ \ let y = fabs (matrix_get data j i) in

    \ \ \ \ \ \ eif (less x y) then rowMax i (j+1) y j

    \ \ \ \ \ \ else rowMax i (j+1) x mx

    \ \ \ \ else mx in

    \;

    \ \ let rec loop1 i =

    \ \ \ \ if i + 1 \<= n then

    \ \ \ \ \ \ let x = fabs (matrix_get data i i) in

    \ \ \ \ \ \ let mx = rowMax i (i+1) x i in

    \ \ \ \ \ \ norm (getRow data mx) (n+1) i;

    \ \ \ \ \ \ rowSwap data i mx;

    \ \ \ \ \ \ let rec loop2 j =

    \ \ \ \ \ \ \ \ if j + 1 \<= n then (

    \ \ \ \ \ \ \ \ \ \ rowElim (getRow data i) (getRow data j) (n+1) i;

    \ \ \ \ \ \ \ \ \ \ loop2 (j+1))

    \ \ \ \ \ \ \ \ else () in

    \ \ \ \ \ \ loop2 (i+1);

    \ \ \ \ \ \ loop1 (i+1)

    \ \ \ \ else () in

    \ \ loop1 0
  </code>

  The inferred types do not differ from the <em|liquid_gauss.gadt> case.

  The last toplevel definition from <em|liquid_gauss_harder_asserted.gadt>:

  <\code>
    let gauss data =

    \ \ let n = matrix_dim1 data in

    \;

    \ \ let rec rowMax = efunction i -\>

    \ \ \ \ let x = fabs (matrix_get data i i) in

    \ \ \ \ let rec loop j x mx =

    \ \ \ \ \ \ assert num mx + 1 \<= n;

    \ \ \ \ \ \ eif j + 1 \<= n then

    \ \ \ \ \ \ \ \ let y = fabs (matrix_get data j i) in

    \ \ \ \ \ \ \ \ eif (less x y) then loop (j+1) y j

    \ \ \ \ \ \ \ \ else loop (j+1) x mx

    \ \ \ \ \ \ else mx in

    \ \ \ \ loop (i+1) x i in

    \;

    \ \ let rec loop1 i =

    \ \ \ \ if i + 1 \<= n then

    \ \ \ \ \ \ let mx = rowMax i in

    \ \ \ \ \ \ norm (getRow data mx) (n+1) i;

    \ \ \ \ \ \ rowSwap data i mx;

    \ \ \ \ \ \ let rec loop2 j =

    \ \ \ \ \ \ \ \ if j + 1 \<= n then (

    \ \ \ \ \ \ \ \ \ \ rowElim (getRow data i) (getRow data j) (n+1) i;

    \ \ \ \ \ \ \ \ \ \ loop2 (j+1))

    \ \ \ \ \ \ \ \ else () in

    \ \ \ \ \ \ loop2 (i+1);

    \ \ \ \ \ \ loop1 (i+1)

    \ \ \ \ else () in

    \ \ loop1 0
  </code>

  The inferred types do not differ from the <em|liquid_gauss.gadt> case.

  <subsection|Program <verbatim|fft>><label|FFTExample>

  Source file <em|liquid_fft_full.gadt>:

  <\code>
    external let n2i : <math|\<forall\>>n. Num n <math|\<rightarrow\>> Int =
    "fun i -\<gtr\> i"

    external let div2 : <math|\<forall\>>n. Num (2 n) <math|\<rightarrow\>>
    Num n = "fun i -\<gtr\> i / 2"

    external let div4 : <math|\<forall\>>n. Num (4 n) <math|\<rightarrow\>>
    Num n = "fun i -\<gtr\> i / 4"

    external let n2f : <math|\<forall\>>n. Num n <math|\<rightarrow\>> Float
    = "float_of_int"

    external let equal : <math|\<forall\>>a. a <math|\<rightarrow\>> a
    <math|\<rightarrow\>> Bool = "fun x y -\<gtr\> x = y"

    external let leq : <math|\<forall\>>a. a <math|\<rightarrow\>> a
    <math|\<rightarrow\>> Bool = "fun x y -\<gtr\> x \<less\>= y"

    external let less : <math|\<forall\>>a. a <math|\<rightarrow\>> a
    <math|\<rightarrow\>> Bool = "fun x y -\<gtr\> x \<less\> y"

    external let ignore : <math|\<forall\>>a. a <math|\<rightarrow\>> () =
    "ignore"

    \;

    external let abs : Float <math|\<rightarrow\>> Float = "abs_float"

    external let cos : Float <math|\<rightarrow\>> Float = "cos"

    external let sin : Float <math|\<rightarrow\>> Float = "sin"

    external let neg : Float <math|\<rightarrow\>> Float = "(~-.)"

    external let minus : Float <math|\<rightarrow\>> Float
    <math|\<rightarrow\>> Float = "(-.)"

    external let plus : Float <math|\<rightarrow\>> Float
    <math|\<rightarrow\>> Float = "(+.)"

    external let mult : Float <math|\<rightarrow\>> Float
    <math|\<rightarrow\>> Float = "( *. )"

    external let div : Float <math|\<rightarrow\>> Float
    <math|\<rightarrow\>> Float = "( /. )"

    external let fl0 : Float = "0.0"

    external let fl05 : Float = "0.5"

    external let fl1 : Float = "1.0"

    external let fl2 : Float = "2.0"

    external let fl3 : Float = "3.0"

    external let fl4 : Float = "4.0"

    external let pi : Float = "4.0 *. atan 1.0"

    external let two_pi : Float = "8.0 *. atan 1.0"

    \;

    datatype Bounded : num * num

    datacons Index : <math|\<forall\>>i, k, n[n <math|\<leqslant\>> i
    <math|\<wedge\>> i <math|\<leqslant\>> k].Num i \<longrightarrow\>
    Bounded (n, k)

    \;

    let ffor s d body =

    \ \ let rec loop i =

    \ \ \ \ if i \<= d then (body (Index i); loop (i + 1)) else () in

    \ \ loop s

    \;

    external let ref : <math|\<forall\>>a. a <math|\<rightarrow\>> Ref a =
    "fun a -\<gtr\> ref a"

    external let asgn : <math|\<forall\>>a. Ref a <math|\<rightarrow\>> a
    <math|\<rightarrow\>> () = "fun a b -\<gtr\> a := b"

    external let deref : <math|\<forall\>>a. Ref a <math|\<rightarrow\>> a =
    "(!)"

    \;

    let fft px py = (* n must be a power of 2! *)

    \ \ let n = array_length px + (-1) in

    \ \ let rec loop n2 n4 =

    \ \ \ \ if n2 \<= 2 then () else (* the case n2 = 2 is treated below *)

    \ \ \ \ let e = div two_pi (n2f n2) in

    \ \ \ \ let e3 = mult fl3 e in

    \ \ \ \ let a = ref fl0 in

    \ \ \ \ let a3 = ref fl0 in

    \ \ \ \ let rec forbod j' =

    \ \ \ \ match j' with Index j -\>

    \ \ \ \ (*for j = 1 to n4 do*)

    \ \ \ \ \ \ let cc1 = cos (deref a) in

    \ \ \ \ \ \ let ss1 = sin (deref a) in

    \ \ \ \ \ \ let cc3 = cos (deref a3) in

    \ \ \ \ \ \ let ss3 = sin (deref a3) in

    \ \ \ \ \ \ asgn a (plus (deref a) e);

    \ \ \ \ \ \ asgn a3 (plus (deref a3) e3);

    \ \ \ \ \ \ let rec loop1 i0 i1 i2 i3 id =

    \ \ \ \ \ \ \ \ if n + 1 \<= i3 then () else (* out_of_bounds *)

    \ \ \ \ \ \ \ \ let g_px_i0 = array_get px i0 in

    \ \ \ \ \ \ \ \ let g_px_i2 = array_get px i2 in

    \ \ \ \ \ \ \ \ let r1 = minus g_px_i0 g_px_i2 in

    \ \ \ \ \ \ \ \ let r1' = plus g_px_i0 g_px_i2 in

    \ \ \ \ \ \ \ \ array_set px i0 r1';

    \ \ \ \ \ \ \ \ let g_px_i1 = array_get px i1 in

    \ \ \ \ \ \ \ \ let g_px_i3 = array_get px i3 in

    \ \ \ \ \ \ \ \ let r2 = minus g_px_i1 g_px_i3 in

    \ \ \ \ \ \ \ \ let r2' = plus g_px_i1 g_px_i3 in

    \ \ \ \ \ \ \ \ array_set px i1 r2';

    \ \ \ \ \ \ \ \ let g_py_i0 = array_get py i0 in

    \ \ \ \ \ \ \ \ let g_py_i2 = array_get py i2 in

    \ \ \ \ \ \ \ \ let s1 = minus g_py_i0 g_py_i2 in

    \ \ \ \ \ \ \ \ let s1' = plus g_py_i0 g_py_i2 in

    \ \ \ \ \ \ \ \ array_set py i0 s1';

    \ \ \ \ \ \ \ \ let g_py_i1 = array_get py i1 in

    \ \ \ \ \ \ \ \ let g_py_i3 = array_get py i3 in

    \ \ \ \ \ \ \ \ let s2 = minus g_py_i1 g_py_i3 in

    \ \ \ \ \ \ \ \ let s2' = plus g_py_i1 g_py_i3 in

    \ \ \ \ \ \ \ \ array_set py i1 s2';

    \ \ \ \ \ \ \ \ let s3 = minus r1 s2 in\ 

    \ \ \ \ \ \ \ \ let r1 = plus r1 s2 in

    \ \ \ \ \ \ \ \ let s2 = minus r2 s1 in

    \ \ \ \ \ \ \ \ let r2 = plus r2 s1 in

    \ \ \ \ \ \ \ \ array_set px i2 (minus (mult r1 cc1) (mult s2 ss1));

    \ \ \ \ \ \ \ \ array_set py i2 (minus (mult (neg s2) cc1) (mult r1
    ss1));

    \ \ \ \ \ \ \ \ array_set px i3 (plus (mult s3 cc3) (mult r2 ss3));

    \ \ \ \ \ \ \ \ array_set py i3 (minus (mult r2 cc3) (mult s3 ss3));

    \ \ \ \ \ \ \ \ loop1 (i0 + id) (i1 + id) (i2 + id) (i3 + id) id in

    \ \ \ \ \ \ let rec loop2 is id =

    \ \ \ \ \ \ \ \ if n \<= is then ()

    \ \ \ \ \ \ \ \ else (

    \ \ \ \ \ \ \ \ \ \ let i1 = is + n4 in

    \ \ \ \ \ \ \ \ \ \ let i2 = i1 + n4 in

    \ \ \ \ \ \ \ \ \ \ let i3 = i2 + n4 in

    \ \ \ \ \ \ \ \ \ \ loop1 is i1 i2 i3 id;

    \ \ \ \ \ \ \ \ \ \ loop2 (2 * id + j - n2) (4 * id)) in

    \ \ \ \ \ \ loop2 j (2 * n2) in

    \ \ \ \ ffor 1 n4 forbod;\ 

    \ \ \ \ loop (div2 n2) (div2 n4) in

    \ \ loop n (div4 n);

    \;

    \ \ let rec loop1 i0 i1 id =

    \ \ \ \ if n + 1 \<= i1 then () else

    \ \ \ \ let r1 = array_get px i0 in

    \ \ \ \ array_set px i0 (plus r1 (array_get px i1));

    \ \ \ \ array_set px i1 (minus r1 (array_get px i1));

    \ \ \ \ let r1 = array_get py i0 in

    \ \ \ \ array_set py i0 (plus r1 (array_get py i1));

    \ \ \ \ array_set py i1 (minus r1 (array_get py i1));

    \ \ \ \ loop1 (i0 + id) (i1 + id) id in

    \ \ let rec loop2 is id =

    \ \ \ \ if n \<= is then () else (

    \ \ \ \ \ \ loop1 is (is + 1) id;

    \ \ \ \ \ \ loop2 (2 * id + (-1)) (4 * id)) in

    \ \ loop2 1 4;

    \;

    \ \ let rec loop1 j k =

    \ \ \ \ eif j \<= k then j + k

    \ \ \ \ else loop1 (j - k) (div2 k) in

    \;

    \ \ let rec loop2 i j =

    \ \ \ \ if n \<= i then () else (

    \ \ \ \ \ \ if j \<= i then () else (

    \ \ \ \ \ \ \ \ let xt = array_get px j in

    \ \ \ \ \ \ \ \ array_set px j (array_get px i); array_set px i (xt);

    \ \ \ \ \ \ \ \ let xt = array_get py j in

    \ \ \ \ \ \ \ \ array_set py j (array_get py i); array_set py i (xt));

    \ \ \ \ \ \ let j' = loop1 j (div2 n) in

    \ \ \ \ \ \ loop2 (i + 1) j') in

    \ \ loop2 1 1; n

    \;

    let ffttest np =

    \ \ let enp = n2f np in

    \ \ let n2 = div2 np in

    \ \ let npm = n2 - 1 in

    \ \ let pxr = array_make (np+1) fl0 in

    \ \ let pxi = array_make (np+1) fl0 in

    \ \ let t = div pi enp in

    \ \ array_set pxr 1 (mult (minus enp fl1) fl05);

    \ \ array_set pxi 1 (fl0);

    \ \ array_set pxr (n2+1) (neg (mult fl1 fl05));

    \ \ array_set pxi (n2+1) fl0;

    \ \ let rec forbod i =

    \ \ \ \ if i \<= npm then

    \ \ \ \ \ \ let j = np - i in

    \ \ \ \ \ \ array_set pxr (i+1) (neg (mult fl1 fl05));

    \ \ \ \ \ \ array_set pxr (j+1) (neg (mult fl1 fl05));

    \ \ \ \ \ \ let z = mult t (n2f i) in

    \ \ \ \ \ \ let y = mult (div (cos z) (sin z)) fl05 in

    \ \ \ \ \ \ array_set pxi (i+1) (neg y); array_set pxi (j+1) (y)

    \ \ \ \ else () in

    \ \ forbod 1;

    \ \ ignore (fft pxr pxi);

    \ \ (* lukstafi: kr and ki are placeholders? *)

    \ \ let rec loop i zr zi kr ki =

    \ \ \ \ if np \<= i then (zr, zi) else

    \ \ \ \ \ \ let a = abs (minus (array_get pxr (i+1)) (n2f i)) in

    \ \ \ \ \ \ let b = less zr a in

    \ \ \ \ \ \ let zr = if b then a else zr in

    \ \ \ \ \ \ let kr = eif b then i else kr in

    \ \ \ \ \ \ let a = abs (array_get pxi (i+1)) in

    \ \ \ \ \ \ let b = less zi a in

    \ \ \ \ \ \ let zi = if b then a else zi in

    \ \ \ \ \ \ let ki = eif b then i else ki in

    \ \ \ \ \ \ loop (i+1) zr zi kr ki in

    \ \ let zr, zi = loop 0 fl0 fl0 0 0 in

    \ \ let zm = if less (abs zr) (abs zi) then zi else zr in

    \ \ (*in print_float zm; print_newline ()*) zm

    \;

    let rec loop_np i np =

    \ \ if 17 \<= i then () else

    \ \ ( ignore (ffttest np); loop_np (i + 1) (2 * np) )

    \;

    let doit _ = loop_np 4 16
  </code>

  Value items from <em|liquid_fft_full.gadti.target>:

  <\code>
    val ffor :

    \ \ \ <math|\<forall\>>i, j, k, n[j <math|\<leqslant\>> i
    <math|\<wedge\>> k <math|\<leqslant\>> n].

    \ \ \ Num n <math|\<rightarrow\>> Num j <math|\<rightarrow\>> (Bounded
    (k, i) <math|\<rightarrow\>> ()) <math|\<rightarrow\>> ()

    \;

    val fft :

    \ \ \ <math|\<forall\>>k, n[1 <math|\<leqslant\>> n <math|\<wedge\>> n +
    1 <math|\<leqslant\>> k].

    \ \ \ Array (Float, n + 1) <math|\<rightarrow\>> Array (Float, k)
    <math|\<rightarrow\>> Num n

    \;

    val ffttest : <math|\<forall\>>n[2 <math|\<leqslant\>> n]. Num n
    <math|\<rightarrow\>> Float

    \;

    val loop_np : <math|\<forall\>>k, n[2 <math|\<leqslant\>> n]. Num k
    <math|\<rightarrow\>> Num n <math|\<rightarrow\>> ()

    \;

    val doit : <math|\<forall\>>a. a <math|\<rightarrow\>> ()
  </code>

  <appendix|<name|InvarGenT>: Manual>

  <section|Introduction>

  Type systems are an established natural deduction-style means to reason
  about programs. Dependent types can represent arbitrarily complex
  properties as they use the same language for both types and programs, the
  type of value returned by a function can itself be a function of the
  argument. Generalized Algebraic Data Types bring some of that expressivity
  to type systems that deal with data-types. Type systems with GADTs
  introduce the ability to reason about return type by case analysis of the
  input value, while keeping the benefits of a simple semantics of types, for
  example deciding equality between types can be very simple. Existential
  types hide some information conveyed in a type, usually when that
  information cannot be reconstructed in the type system. A part of the type
  will often fail to be expressible in the simple language of types, when the
  dependence on the input to the program is complex. GADTs express
  existential types by using local type variables for the hidden parts of the
  type encapsulated in a GADT.

  The <name|InvarGenT> type system for GADTs differs from more pragmatic
  approaches in mainstream functional languages in that we do not require any
  type annotations on expressions, even on recursive functions. The
  implementation also includes linear equations and inequalities over
  rational numbers in the language of types, with the possibility to
  introduce more domains in the future.

  <section|Tutorial>

  The concrete syntax of <name|InvarGenT> is similar to that of OCaml.
  However, it does not currently cover records, the module system, objects,
  and polymorphic variant types. It supports higher-order functions,
  algebraic data-types including built-in tuple types, and linear pattern
  matching. It supports conjunctive patterns using the <verbatim|as> keyword,
  but it currently does not support disjunctive patterns. It currently has
  limited support for guarded patterns: after <verbatim|when>, only
  inequality <verbatim|\<less\>=> between values of the <verbatim|Num> type
  are allowed.

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

  We start with a simple example, a function that can compute a value from a
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
  <name|InvarGenT>. Such a definition will be verified against the rest of
  the program when <name|InvarGenT> calls <verbatim|ocamlc -c> to verify the
  exported code. Another variant of <verbatim|external> (omitting the
  <verbatim|let> keyword) exports a value using <verbatim|external> in OCaml
  code, which is OCaml source declaration of the foreign function interface
  of OCaml. When we are not interested in linking and running the exported
  code, we can omit the part starting with the <verbatim|=> sign. The
  exported code will reuse the name in the FFI definition: <verbatim|external
  f : >...<verbatim| = "f">.

  The type inferred for the above example is <verbatim|eval :
  <math|\<forall\>>a. Term a<math|\<rightarrow\>>a>. GADTs make it possible
  to reveal that <verbatim|IsZero x> is a <verbatim|Term Bool> and therefore
  the result of <verbatim|eval> should in its case be <verbatim|Bool>,
  <verbatim|Plus (x, y)> is a <verbatim|Term Num> and the result of
  <verbatim|eval> should in its case be <verbatim|Num>, etc. The
  <verbatim|if/eif><math|\<ldots\>><verbatim|then><math|\<ldots\>><verbatim|else><math|\<ldots\>>
  syntax is a syntactic sugar for <verbatim|match<math|/>ematch><math|\<ldots\>><verbatim|with
  True -\<gtr\>><math|\<ldots\>><verbatim| \| False
  -\<gtr\>><math|\<ldots\>>, and any such expressions are exported using
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

  <name|InvarGenT> returns an unexpected type:
  <verbatim|equal<math|:\<forall\>>a,b.(Ty a, Ty
  b)<math|\<rightarrow\>>a<math|\<rightarrow\>>a<math|\<rightarrow\>>Bool>,
  one of four maximally general types of <verbatim|equal> as defined above.
  The other maximally general ``wrong'' types are
  <verbatim|<math|\<forall\>>a,b.(Ty a, Ty
  b)<math|\<rightarrow\>>b<math|\<rightarrow\>>b<math|\<rightarrow\>>Bool>
  and <verbatim|<math|\<forall\>>a,b.(Ty a, Ty
  b)<math|\<rightarrow\>>b<math|\<rightarrow\>>a<math|\<rightarrow\>>Bool>.
  This illustrates that unrestricted type systems with GADTs lack principal
  typing property.

  <name|InvarGenT> commits to a type of a toplevel definition before
  proceeding to the next one, so sometimes we need to provide more
  information in the program. Besides type annotations, there are three means
  to enrich the generated constraints: <verbatim|assert false> syntax for
  providing negative constraints, <verbatim|assert type e1 =
  e2;><math|\<ldots\>> and <verbatim|assert num e1 \<less\>=
  e2;><math|\<ldots\>> for positive constraints, and <verbatim|test> syntax
  for including constraints of use cases with constraint of a toplevel
  definition. To ensure only one maximally general type for <verbatim|equal>,
  we use <verbatim|assert false> and <verbatim|test>. We can either add the
  <verbatim|assert false> clauses:

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
  <name|InvarGenT> returns the expected type
  <verbatim|equal<math|:\<forall\>>a,b.(Ty a, Ty
  b)<math|\<rightarrow\>>a<math|\<rightarrow\>>b<math|\<rightarrow\>>Bool>.

  Now we demonstrate numerical invariants:

  <\code>
    datatype Binary : num

    datatype Carry : num

    datacons Zero : Binary 0

    datacons PZero : <math|\<forall\>>n[0<math|\<leqslant\>>n]. Binary n
    <math|\<longrightarrow\>> Binary(2 n)

    datacons POne : <math|\<forall\>>n[0<math|\<leqslant\>>n]. Binary n
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
  an existential type inferred, we have to use <verbatim|efunction>,
  <verbatim|ematch> or <verbatim|eif> expressions, which differ from
  <verbatim|function>, <verbatim|match>, <verbatim|eif> respectively in that
  the (return) type is an existential type. To use a value of an existential
  type, we have to bind it with a <verbatim|let>..<verbatim|in> expression.
  Otherwise, the existential type will not be unpacked. An existential type
  will be automatically unpacked before being ``repackaged'' as another
  existential type. In the following artificial example, we abstract away the
  particular resulting location.

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
  a<math|\<rightarrow\>> <math|\<exists\>>b. Castle b>. Next consider a
  slightly less artificial, toy example of computer hardware configuration.
  It illustrates many aspects of existential types in <name|InvarGenT>. We
  introduce functions <verbatim|config_mem_board> and <verbatim|config_gpu>
  as external, i.e., ones whose definition is not type-checked by
  <name|InvarGenT>. Their types illustrate that existential types can be used
  in type annotations. Types <verbatim|Slow> and <verbatim|Fast>, although
  declared as data-types, are phantom types, i.e. are not inhabited and
  convey information as parameters of other types.

  <\code>
    datatype Slow \ datatype Fast \ datatype Budget

    datacons Small : Budget \ datacons Medium : Budget \ datacons Large :
    Budget

    datatype Memory : type \ datacons Best_mem : Memory Fast

    datatype Motherboard : type \ datacons Best_board : Motherboard Fast

    external config_mem_board : Budget <math|\<rightarrow\>>
    <math|\<exists\>>a. (Memory a, Motherboard a)

    datatype CPU : type

    datacons FastCPU : CPU Fast \ datacons SlowCPU : CPU Slow

    datatype GPU : type

    datacons FastGPU : GPU Fast \ datacons SlowGPU : GPU Slow

    external config_gpu : Budget <math|\<rightarrow\>> <math|\<exists\>>a.
    GPU a

    datatype PC : type * type * type * type

    datacons PC :

    \ \ <math|\<forall\>>a,b,c,r. CPU a * GPU b * Memory c * Motherboard r
    <math|\<longrightarrow\>> PC (a,b,c,r)

    datatype Usecase \ datacons Gaming : Usecase

    datacons Scientific : Usecase \ datacons Office : Usecase

    \;

    let budget_to_cpu = efunction

    \ \ \| Small -\<gtr\> SlowCPU \| Medium -\<gtr\> FastCPU \| Large
    -\<gtr\> FastCPU

    let usecase_to_gpu budget = efunction

    \ \ \| Gaming -\<gtr\> FastGPU \| Scientific -\<gtr\> FastGPU

    \ \ \| Office -\<gtr\> config_gpu budget

    let rec configure = efunction

    \ \ \| Small, Gaming -\<gtr\> configure (Small, Office)

    \ \ \| Large, Gaming -\<gtr\> PC (FastCPU, FastGPU, Best_mem, Best_board)

    \ \ \| budget, usecase -\<gtr\>

    \ \ \ \ let mem, board = config_mem_board budget in

    \ \ \ \ let cpu = budget_to_cpu budget in

    \ \ \ \ let gpu = usecase_to_gpu budget usecase in

    \ \ \ \ PC (cpu, gpu, mem, board)
  </code>

  <name|InvarGenT> infers the following types:

  <\code>
    budget_to_cpu : Size <math|\<rightarrow\>> <math|\<exists\>>a.CPU a

    usecase_to_gpu : Usecase <math|\<rightarrow\>> <math|\<exists\>>a.GPU a

    configure : (Size, Usecase) <math|\<rightarrow\>> <math|\<exists\>>a, b,
    c.PC (a, b, c, c)
  </code>

  The definition of <verbatim|configure> illustrates explicit elimination of
  existential types by <verbatim|let>..<verbatim|in> definitions: by design,
  inlining of <verbatim|cpu> or <verbatim|gpu> definitions would make the
  function not typeable. The call to <verbatim|config_gpu> and the recursive
  call to <verbatim|configure> illustrate implicit elimination of existential
  types in return positions.

  A more practical existential type example:

  <\code>
    datatype Bool

    datacons True : Bool

    datacons False : Bool

    datatype List : type * num

    datacons LNil : <math|\<forall\>>a. List(a, 0)

    datacons LCons : <math|\<forall\>>n,a[0<math|\<leqslant\>>n]. a * List(a,
    n) <math|\<longrightarrow\>> List(a, n+1)

    \;

    let rec filter f =

    \ \ efunction LNil -\> LNil

    \ \ \ \ \| LCons (x, xs) -\>

    \ \ \ \ \ \ eif f x then

    \ \ \ \ \ \ \ \ \ \ let ys = filter f xs in

    \ \ \ \ \ \ \ \ \ \ LCons (x, ys)

    \ \ \ \ \ \ else filter f xs
  </code>

  We get <verbatim|filter<math|:\<forall\>>n,
  a.(a<math|\<rightarrow\>>Bool)<math|\<rightarrow\>>List (a,
  n)<math|\<rightarrow\>> <math|\<exists\>>k[0<math|\<leqslant\>>k
  <math|\<wedge\>> k<math|\<leqslant\>>n].List (a, k)>. Note that we need to
  use both <verbatim|efunction> and <verbatim|eif> above, since every use of
  <verbatim|function>, <verbatim|match> or <verbatim|if> will force the types
  of its branches to be equal. In particular, for lists with length the
  resulting length would have to be the same in each branch. If the
  constraint cannot be met, as for <verbatim|filter> with either
  <verbatim|function> or <verbatim|if>, the code will not type-check.

  A more complex example that computes bitwise <em|or> -- <verbatim|ub>
  stands for ``upper bound'':

  <\code>
    datatype Binary : num

    datacons Zero : Binary 0

    datacons PZero : <math|\<forall\>>n [0<math|\<leqslant\>>n]. Binary n
    <math|\<longrightarrow\>> Binary(2 n)

    datacons POne : <math|\<forall\>>n [0<math|\<leqslant\>>n]. Binary n
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
  n<math|\<rightarrow\>><math|\<exists\>>:i[0<math|\<leqslant\>>n
  <math|\<wedge\>> 0<math|\<leqslant\>>k <math|\<wedge\>>
  n<math|\<leqslant\>>i <math|\<wedge\>> k<math|\<leqslant\>>i
  <math|\<wedge\>> i<math|\<leqslant\>>n+k].Binary i>.

  Why cannot we shorten the above code by converting the initial cases to
  <verbatim|Zero -\<gtr\> (efunction b -\<gtr\> b)>? Without pattern
  matching, we do not make the contribution of <verbatim|Binary n> available.
  Knowing <verbatim|n<math|=>i> and not knowing
  <verbatim|0<math|\<leqslant\>>n>, for the case <verbatim|k<math|=>0>, we
  get: <verbatim|ub:<math|\<forall\>>k,n.Binary k<math|\<rightarrow\>>Binary
  n<math|\<rightarrow\>><math|\<exists\>>i[0<math|\<leqslant\>>k<math|\<wedge\>>n<math|\<leqslant\>>i<math|\<wedge\>>i<math|\<leqslant\>>n+k].Binary
  i>. <verbatim|n<math|\<leq\><no-break>>i> follows from
  <verbatim|n<math|=>i>, <verbatim|i<math|\<leqslant\>>n+k> follows from
  <verbatim|n<math|=>i> and <verbatim|0<math|\<leqslant\>>k>, but
  <verbatim|k<math|\<leqslant\>>i> cannot be inferred from
  <verbatim|k<math|=>0> and <verbatim|n<math|=>i> without knowing that
  <verbatim|0<math|\<leqslant\>>n>.

  Besides displaying types of toplevel definitions, <name|InvarGenT> can also
  export an OCaml source file with all the required GADT definitions and type
  annotations.

  <section|Syntax>

  Below we present, using examples, the syntax of <name|InvarGenT>: the
  mathematical notation, the concrete syntax in ASCII and the concrete syntax
  using Unicode.

  <block|<tformat|<cwith|1|1|2|2|cell-halign|c>|<cwith|1|1|1|1|cell-halign|l>|<cwith|2|2|2|2|cell-halign|c>|<cwith|2|2|1|1|cell-halign|l>|<cwith|3|3|2|2|cell-halign|l>|<table|<row|<cell|type
  variable: types>|<cell|<math|\<alpha\>,\<beta\>,\<gamma\>,\<tau\>>>|<cell|<verbatim|a>,<verbatim|b>,<verbatim|c>,<verbatim|r>,<verbatim|s>,<verbatim|t>,<verbatim|a1>,...>|<cell|>>|<row|<cell|type
  variable: nums>|<cell|<math|k,m,n>>|<cell|<verbatim|i>,<verbatim|j>,<verbatim|k>,<verbatim|l>,<verbatim|m>,<verbatim|n>,<verbatim|i1>,...>|<cell|>>|<row|<cell|type
  var. with coef.>|<cell|<math|<frac|1|3>n>>|<cell|<verbatim|1/3
  n>>|<cell|>>|<row|<cell|type constructor>|<cell|<math|List>>|<cell|<verbatim|List>>|<cell|>>|<row|<cell|number
  (type)>|<cell|<math|7>>|<cell|<verbatim|7>>|<cell|>>|<row|<cell|numerical
  sum (type)>|<cell|<math|m+n>>|<cell|<verbatim|m+n>>|<cell|>>|<row|<cell|existential
  type>|<cell|<math|\<exists\>k,n<around*|[|k\<leqslant\>n|]>.\<tau\>>>|<cell|<verbatim|ex
  k, n [k\<less\>=n].t>>|<cell|<verbatim|<math|\<exists\>>k,n[k<math|\<leqslant\>>n].t>>>|<row|<cell|type
  sort>|<cell|<math|s<rsub|type>>>|<cell|<verbatim|type>>|<cell|>>|<row|<cell|number
  sort>|<cell|<math|s<rsub|R>>>|<cell|<verbatim|num>>|<cell|>>|<row|<cell|function
  type>|<cell|<math|\<tau\><rsub|1>\<rightarrow\>\<tau\><rsub|2>>>|<cell|<verbatim|t1
  -\<gtr\> t2>>|<cell|<verbatim|t1 <math|\<rightarrow\>><verbatim|
  t2>>>>|<row|<cell|equation>|<cell|<math|a<wide|=|\<dot\>>b>>|<cell|<verbatim|a
  = b>>|<cell|>>|<row|<cell|inequation>|<cell|<math|k\<leqslant\>n>>|<cell|<verbatim|k
  \<less\>= n>>|<cell|<verbatim|k <math|\<leqslant\>>
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
  e>>|<cell|<verbatim|match e with p1-\<gtr\>e1 \|
  >...<verbatim|>>>|<row|<cell|if-then-else
  clause>|<cell|<math|\<lambda\><around*|(|K<rsub|T>.e<rsub|1>,K<rsub|F>.e<rsub|2>|)>
  e>>|<cell|<verbatim|if e then e1 else e2>>>|<row|<cell|if-then-else
  condition>|<cell|<math|\<lambda\><around*|(|_
  <text|<with|font-shape|condensed|<strong|when>>>
  m\<leqslant\>n.e<rsub|1>,\<ldots\>|)> K<rsub|u>>>|<cell|<verbatim|if m
  \<less\>= n then e1 else e2>>>|<row|<cell|postcond.
  function>|<cell|<math|\<lambda\><around*|[|K|]><around*|(|p<rsub|1>.e<rsub|1>\<ldots\>p<rsub|n>.e<rsub|n>|)>>>|<cell|<verbatim|efunction
  p1-\<gtr\>e1 \| >...>>|<row|<cell|postcond.
  match>|<cell|<math|\<lambda\><around*|[|K|]><around*|(|p<rsub|1>.e<rsub|1>\<ldots\>p<rsub|n>.e<rsub|n>|)>
  e>>|<cell|<verbatim|ematch e with p1-\<gtr\>e1 \|
  >...>>|<row|<cell|eif-then-else clause>|<cell|<math|\<lambda\><around*|[|K|]><around*|(|K<rsub|T>.e<rsub|1>,K<rsub|F>.e<rsub|2>|)>
  e>>|<cell|<verbatim|eif e then e1 else e2>>>|<row|<cell|eif-then-else
  condition>|<cell|<math|\<lambda\><around*|[|K|]><around*|(|_
  <text|<with|font-shape|condensed|<strong|when>>>
  m\<leqslant\>n.e<rsub|1>,\<ldots\>|)> K<rsub|u>>>|<cell|<verbatim|eif m
  \<less\>= n then e1 else e2>>>|<row|<cell|rec.
  definition>|<cell|<math|<text|<with|font-shape|condensed|<strong|let rec>>>
  x=e<rsub|1> <text|<with|font-shape|condensed|<strong|in>>>
  e<rsub|2>>>|<cell|<verbatim|let rec x = e1 in
  e2>>>|<row|<cell|definition>|<cell|<math|<text|<with|font-shape|condensed|<strong|let>>>
  p=e<rsub|1> <text|<with|font-shape|condensed|<strong|in>>>
  e<rsub|2>>>|<cell|<verbatim|let p1,p2 = e1 in e2>>>|<row|<cell|asserting
  dead br.>|<cell|<math|<text|<with|font-shape|condensed|<strong|assert
  false>>>>>|<cell|<verbatim|assert false>>>|<row|<cell|runtime
  failure>|<cell|<math|<with|math-font-series|bold|runtime failure>
  s>>|<cell|<verbatim|runtime_failure s>>>|<row|<cell|assert equal
  types>|<cell|<math|<text|<with|font-shape|condensed|<strong|assert type>>>
  \<tau\><rsub|e<rsub|1>><wide|=|\<dot\>>\<tau\><rsub|e<rsub|2>>;e<rsub|3>>>|<cell|<verbatim|assert
  type e1 = e2; e3>>>|<row|<cell|assert inequality>|<cell|<math|<text|<with|font-shape|condensed|<strong|assert
  num>>> e<rsub|1>\<leqslant\>e<rsub|2>;e<rsub|3>>>|<cell|<verbatim|assert
  num e1 \<less\>= e2; e3>>>>>>

  A built-in fail at runtime with the given text message is only needed for
  introducing existential types: a user-defined equivalent of
  <verbatim|runtime_failure> would introduce a spurious branch for
  generalization.

  Toplevel expressions (corresponding to structure items in OCaml) introduce
  types, type and value constructors, global variables with given type
  \ (external names) or inferred type (definitions).

  <block|<tformat|<cwith|1|1|2|2|cell-halign|l>|<cwith|1|1|1|1|cell-halign|l>|<cwith|2|2|1|1|cell-row-span|2>|<cwith|4|4|1|1|cell-row-span|2>|<table|<row|<cell|type
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

  Toplevel non-recursive <verbatim|let> definitions are polymorphic as an
  exception. In expressions, <verbatim|let><math|\<ldots\>><verbatim|in>
  definitions are monomorphic, one should use the <verbatim|let
  rec><math|\<ldots\>><verbatim|in> syntax to get a polymorphic
  <verbatim|let>-binding.

  Tests list expressions of type <verbatim|Bool> that at runtime have to
  evaluate to <verbatim|True>. Type inference is affected by the constraints
  generated to typecheck the expressions.

  There are variants of the if-then-else clause syntax supporting
  <math|<with|math-font-series|bold|when>> conditions:

  <\itemize>
    <item><verbatim|if m1 \<less\>= n1 && m2 \<less\>= n2
    &&><math|\<ldots\>><verbatim| then e1 else e2> is
    <math|\<lambda\><around*|(|_ <text|<with|font-shape|condensed|<strong|when>>>
    \<wedge\><rsub|i>m<rsub|i>\<leqslant\>n<rsub|i>.e<rsub|1>,_.e<rsub|2>|)>
    K<rsub|u>>,

    <item><verbatim|if m \<less\>= n then e1 else e2> is
    <math|\<lambda\><around*|(|_ <text|<with|font-shape|condensed|<strong|when>>>
    m\<leqslant\>n.e<rsub|1>,_ <text|<with|font-shape|condensed|<strong|when>>>
    n+1\<leqslant\>m.e<rsub|2>|)> K<rsub|u>> if integer mode is on (as in
    default setting),

    <item>similarly for the <verbatim|eif> variants.
  </itemize>

  We add the standard syntactic sugar for function definitions:

  <\itemize>
    <item><verbatim|let <math|p<rsub|1>> <math|p<rsub|2>>><math|\<ldots\>><verbatim|
    <math|p<rsub|n>> = <math|e<rsub|1>> in <math|e<rsub|2>>> expands to
    <verbatim|let <math|p<rsub|1>> = fun <math|p<rsub|2>>><math|\<ldots\>><verbatim|
    <math|p<rsub|n>> -\<gtr\> <math|e<rsub|1>> in <math|e<rsub|2>>>

    <item><verbatim|let rec <math|l<rsub|1>>
    <math|p<rsub|2>>><math|\<ldots\>><verbatim| <math|p<rsub|n>> =
    <math|e<rsub|1>> in <math|e<rsub|2>>> expands to <verbatim|let rec
    <math|l<rsub|1>> = fun <math|p<rsub|2>>><math|\<ldots\>><verbatim|
    <math|p<rsub|n>> -\<gtr\> <math|e<rsub|1>> in <math|e<rsub|2>>>

    <item>toplevel <verbatim|let> and <verbatim|let rec> definitions expand
    correspondingly.
  </itemize>

  For simplicity of theory and implementation, mutual non-nested recursion
  and or-patterns are not provided. For mutual recursion, nest one recursive
  definition inside another.

  Like in OCaml, types of arguments in declarations of constructors are
  separated by asterisks. However, the type constructor for tuples is
  represented by commas, like in Haskell but unlike in OCaml.

  At any place between lexemes, regular comments encapsulated in
  <verbatim|(*><math|\<ldots\>><verbatim|*)> can occur. They are ignored
  during lexing. In front of all toplevel definitions and declarations, e.g.
  before a <verbatim|datatype>, <verbatim|datacons>, <verbatim|external>,
  <verbatim|let rec> or <verbatim|let>, and in front of <verbatim|let
  rec><math|\<ldots\>><verbatim|in> and <verbatim|let><math|\<ldots\>><verbatim|in>
  nodes in expressions, documentation comments
  <verbatim|(**><math|\<ldots\>><verbatim|*)> can be put. Documentation
  comments at other places are syntax errors. Documentation comments are
  preserved both in generated interface files and in exported source code
  files.

  <section|Solver Parameters and CLI>

  The default settings of <name|InvarGenT> parameters should be sufficient
  for most cases. For example, after downloading <name|InvarGenT> source code
  and changing current directory to <verbatim|invargent>, we can enter,
  assuming a Unix-like shell:

  <\code>
    $ make main

    $ ./invargent examples/binary_upper_bound.gadt
  </code>

  To get the inferred types printed on standard output, use the
  <verbatim|-inform> option:

  <\code>
    $ ./invargent -inform examples/avl_tree.gadt
  </code>

  Below we demonstrate what happens with insufficiently high parameter
  setting. Consider this example:

  <\code>
    $ ./invargent -inform examples/flatten_septs.gadt

    File "examples/flatten_septs.gadt", line 8, characters 6-104:

    No answer in type: term abduction failed

    \;

    Perhaps increase the -term_abduction_timeout parameter.

    Perhaps increase the -term_abduction_fail parameter.

    $ ./invargent -inform -term_abduction_timeout 3000
    examples/flatten_septs.gadt

    File "examples/flatten_septs.gadt", line 3, characters 26-261:

    No answer in num: numerical abduction failed

    \;

    Perhaps do not pass the -no_dead_code flag.

    Perhaps increase the -num_abduction_timeout parameter.

    Perhaps increase the -num_abduction_fail parameter.

    $ ./invargent -inform -term_abduction_timeout 3000 \\

    \ \ -num_abduction_rotations 4 examples/flatten_septs.gadt

    val flatten_septs :

    \ \ <math|\<forall\>>n, a. List ((a, a, a, a, a, a, a), n)
    <math|\<rightarrow\>> List (a, 7 n)

    InvarGenT: Generated file examples/flatten_septs.gadti

    InvarGenT: Generated file examples/flatten_septs.ml

    InvarGenT: Command "ocamlc -w -25 -c examples/flatten_septs.ml" exited
    with code 0
  </code>

  The <verbatim|Perhaps increase> suggestions are generated only when the
  corresponding limit has actually been exceeded. Remember however that the
  limits will often be exceeded for erroneus programs which should not
  type-check. Moreover, as illustrated above, other settings might be the
  culprit.

  To understand the intent of the solver parameters, we need a rough
  ``birds-eye view'' understanding of how <name|InvarGenT> works. The
  invariants and postconditions that we solve for are logical formulas and
  can be ordered by strength. Least Upper Bounds (LUBs) and Greatest Lower
  Bounds (GLBs) computations are traditional tools used for solving recursive
  equations over an ordered structure. In case of implicational constraints
  that are generated for type inference with GADTs, constraint abduction is a
  form of LUB computation. <em|Constraint generalization> is our term for
  computing the GLB wrt. strength for formulas that are conjunctions of
  atoms. We want the invariants of recursive definitions -- i.e. the types of
  recursive functions and formulas constraining their type variables -- to be
  as weak as possible, to make the use of the corresponding definitions as
  easy as possible. The weaker the invariant, the more general the type of
  definition. Therefore the use of LUB, constraint abduction. For
  postconditions -- i.e. the existential types of results computed by
  <verbatim|efunction> expressions and formulas constraining their type
  variables -- we want the strongest possible solutions, because stronger
  postcondition provides more information at use sites of a definition.
  Therefore we use GLB, constraint generalization, but only if existential
  types have been introduced by <verbatim|efunction> or <verbatim|ematch>.

  Below we discuss all of the <name|InvarGenT> options. We use the technical
  term <em|terms> to mean type shapes, types without the concern for the sort
  of numbers (or other sorts to come in the future).

  <\description>
    <item*|<verbatim|-inform>>Print type schemes of toplevel definitions as
    they are inferred.

    <item*|<verbatim|-time>>Print the time it took to infer type schemes of
    toplevel definitions.

    <item*|<verbatim|-no_sig>>Do not generate the <verbatim|.gadti> file.

    <item*|<verbatim|-no_ml>>Do not generate the <verbatim|.ml> file.

    <item*|<verbatim|-overwrite_ml>>Overwrite the <verbatim|.ml> file if it
    already exists.

    <item*|<verbatim|-ml_file>>Generate the exported OCaml file under the
    provided name.

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

    <item*|<verbatim|-convergence_step>>The iteration at which to start
    truncating postconditions by only keeping atoms present in the previous
    iteration, to force convergence (default 8).

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
    correct answer is greater, abduction might fail. However, it often
    succeeds because of other mechanisms used by the abduction algorithm.

    <item*|<verbatim|-num_prune_at>>Keep less than <math|N> elements in
    abduction sums (default 6). By elements here we mean distinct variables
    -- lack of constant multipliers in concrete syntax of types is just a
    syntactic shortcoming.

    <item*|<verbatim|-num_abduction_timeout>>Limit on numerical simple
    abduction steps (default 1000).

    <item*|<verbatim|-num_abduction_fail>>Limit on backtracking steps in
    numerical joint abduction (default 10).

    <item*|<verbatim|-affine_penalty>>How much to penalize an abduction
    candidate inequality for containing a constant term (default 4). Too
    small a value may lead to divergence, e.g. in some examples abduction
    will pick an answer <math|a+1>, which in the following step will force an
    answer <math|a+2>, then <math|a+3>, etc.

    <item*|<verbatim|-reward_constrn>>How much to reward introducing a
    constraint on so-far unconstrained varialbe, or penalize if negative
    (default 2).

    <item*|<verbatim|-complexity_penalty>>How much to penalize an abduction
    candidate inequality for complexity of its coefficients; the coefficient
    of either the linear or power scaling of the coefficients (default 2.5).

    <item*|<verbatim|-abd_lin_thres_scaling>>Scale the complexity cost of
    coefficients linearly with a jump of the given height after coefficient 1
    (default 2.0).

    <item*|<strong|<verbatim|-abd_pow_scaling>>>Scale the complexity cost of
    coefficients according to the given power.

    <item*|<verbatim|-prefer_bound_to_local>>Prefer a bound coming from outer
    scope, to inequality between two local parameters. In numerical abduction
    heuristic, such bounds are usually doubly penalized: for having a
    constant, and non-locality of parameters.

    <item*|<verbatim|-prefer_bound_to_outer>>Prefer a bound coming from outer
    scope, to inequality between two outer scope parameters. Outer-scope
    constraints sometimes lead to a solution not general enough.

    <item*|<verbatim|-only_off_by_1>>Limit the effect of
    <verbatim|-prefer_bound_to_local> and
    <verbatim|-<no-break>prefer_bound_to_outer> to inequalities with a
    constant 1. This corresponds to an upper bound of an index into a
    zero-indexed array/matrix/etc.

    <item*|<verbatim|-same_with_assertions>>Do not treat definitions with
    positive assertions (<verbatim|assert num>, <verbatim|assert type>)
    specially. The special treatment is currently equivalent to passing
    <verbatim|-<no-break>reward_constrn -1> and
    <verbatim|-prefer_bound_to_local>.

    <item*|<verbatim|-concl_abd_penalty>>Penalize abductive guess when the
    supporting argument comes from the partial answer, instead of from the
    current premise (default 4). Guesses involving the partial answer are
    less secure, for example they depend on the order in which the constraint
    to explain is being processed.

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

    <item*|<verbatim|-postcond_rotations>>In postconditions, check
    coefficients from <math|1/N> (default 3). Numerical constraint
    generalization is performed by approximately finding the convex hull of
    the polytopes corresponding to disjuncts. A step in an exact algorithm
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
    constraint generalization can infer additional constraints over invariant
    parameters. In rare cases a weaker postcondition but a more general
    invariant can be beneficial.

    <item*|<verbatim|-show_extypes>>Show datatypes encoding existential
    types, and their identifiers with uses of existential types. The type
    system in <name|InvarGenT> encodes existential types as GADT types, but
    this representation is hidden from the user. Using
    <verbatim|-show_extypes> exposes the representation as follows. The
    encodings are exported in <verbatim|.gadti> files as regular datatypes
    named <verbatim|exN>, and existential types are printed using syntax
    <verbatim|<math|\<exists\>>N:><math|\<ldots\>> instead of
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

  Let us have a look at tests from the <verbatim|examples> direcotory that
  need a non-default parameter setting. The program
  <verbatim|examples/flatten_septs.gadt> has already been shown above. It is
  the only example that needs the <verbatim|-term_abduction_timeout> and
  <verbatim|-num_abduction_rotations> settings. The need for
  <verbatim|-num_abduction_rotations> comes from having an equation with
  large coefficient in the answer. The need for
  <verbatim|-<no-break>term_abduction_timeout> comes from having bigger type
  shapes to handle during term, i.e. type shape, abduction.

  <\code>
    $ ./invargent -inform examples/non_pointwise_leq.gadt

    File "examples/non_pointwise_leq.gadt", line 12, characters 14-60:

    No answer in type: Answers do not converge

    \;

    Perhaps increase the -iterations_timeout parameter or try one of the
    options: -<no-break>more_existential, -prefer_guess,
    -prefer_bound_to_local.

    $ ./invargent -inform -prefer_guess examples/non_pointwise_leq.gadt

    val leq : <math|\<forall\>>a. Nat a <math|\<rightarrow\>> NatLeq (a, a)

    InvarGenT: Generated file examples/non_pointwise_leq.gadti

    InvarGenT: Generated file examples/non_pointwise_leq.ml

    InvarGenT: Command "ocamlc -w -25 -c examples/non_pointwise_leq.ml"
    exited with code 0
  </code>

  Other examples that need the <verbatim|-prefer_guess> option:
  <verbatim|non_pointwise_zip1_simpler.gadt>,
  <verbatim|non_pointwise_zip1_simpler2.gadt>,
  <verbatim|non_pointwise_zip1_modified.gadt>. On the other hand,
  <verbatim|non_pointwise_zip1.gadt> is inferred with default settings.

  The response from the system does not always include an option which would
  make the inference succeed.

  <\code>
    $ ./invargent -inform examples/liquid_simplex_step_3a.gadt

    File "examples/liquid_simplex_step_3a.gadt", line 7, characters 49-1651:

    No answer in type: Answers do not converge

    \;

    Perhaps do not pass the -no_dead_code flag.

    Perhaps increase the -iterations_timeout parameter or try one of the
    options: -<no-break>more_existential, -prefer_guess,
    -prefer_bound_to_local.

    Perhaps some definition is used with requirements on

    its inferred postcondition not warranted by the definition.

    $ ./invargent -inform -prefer_bound_to_local -only_off_by_1 \\

    examples/liquid_simplex_step_3a.gadt

    val main_step3_test : <math|\<forall\>>k, n[1 <math|\<leqslant\>> n
    <math|\<wedge\>> 3 <math|\<leqslant\>> k]. Matrix (n, k)
    <math|\<rightarrow\>> Float

    InvarGenT: Generated file examples/liquid_simplex_step_3a.gadti

    InvarGenT: Generated file examples/liquid_simplex_step_3a.ml

    File "examples/liquid_simplex_step_3a.ml", line 43, characters 8-9:

    Warning 26: unused variable m.

    InvarGenT: Command "ocamlc -w -25 -c examples/liquid_simplex_step_3a.ml"
    exited with code 0
  </code>

  The other examples that need the <verbatim|-prefer_bound_to_local> option,
  but not the <verbatim|-<no-break>only_off_by_1> option:
  <verbatim|liquid_simplex_step_6a_2.gadt>,
  <verbatim|liquid_tower_harder.gadt>, <verbatim|liquid_gauss2.gadt>.

  <\code>
    $ ./invargent -inform examples/pointwise_zip2_harder.gadt

    val zip2 : <math|\<forall\>>a, b. Zip2 (a, b) <math|\<rightarrow\>> a
    <math|\<rightarrow\>> b

    InvarGenT: Generated file examples/pointwise_zip2_harder.gadti

    InvarGenT: Generated file examples/pointwise_zip2_harder.ml

    File "examples/pointwise_zip2_harder.ml", line 19, characters 21-32:

    Error: This kind of expression is not allowed as right-hand side of `let
    rec'

    InvarGenT: Command "ocamlc -w -25 -c examples/pointwise_zip2_harder.ml"
    exited with code 2

    InvarGenT: Regenerated file examples/pointwise_zip2_harder.ml

    File "examples/pointwise_zip2_harder.ml", line 21, characters 21-32:

    Error: This kind of expression is not allowed as right-hand side of `let
    rec'

    InvarGenT: Command "ocamlc -w -25 -c examples/pointwise_zip2_harder.ml"
    exited with code 2

    $ ./invargent -inform -no_ml examples/pointwise_zip2_harder.gadt

    val zip2 : <math|\<forall\>>a, b. Zip2 (a, b) <math|\<rightarrow\>> a
    <math|\<rightarrow\>> b

    InvarGenT: Generated file examples/pointwise_zip2_harder.gadti
  </code>

  The example <verbatim|pointwise_zip2_harder.gadt> is not compatible with
  the pass-by-value semantics. We can avoid the complaint of the OCaml
  compiler by passing either the <verbatim|-no_ml> flag or the
  <verbatim|-no_verif> flag. More interestingly, we can notice that the file
  <verbatim|pointwise_zip2_harder.ml> is generated twice. This happens
  because <name|InvarGenT>, noticing the failure, generates an OCaml source
  with more type information, as if the <verbatim|-full_annot> option was
  used.

  The examples <verbatim|liquid_fft_simpler.gadt> and
  <verbatim|liquid_fft_full_asserted.gadt> contain assertions, but are nearly
  as hard as <verbatim|liquid_fft.gadt>, <verbatim|liquid_fft_full.gadt>
  respectively. They need the option <verbatim|-same_with_assertions> to not
  switch to settings tuned for cases where assertions capture the harder
  aspects of the invariants to infer.

  Unfortunately, inference fails for some examples regardless of parameters
  setting. We discuss them in the next section.

  <section|Limitations of Current <name|InvarGenT> Inference>

  Type inference for the type system underlying <name|InvarGenT> is
  undecidable. In some cases, the failure to infer a type is not at all
  problematic. Consider this example due to Chuan-kai Lin:

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

  The example <verbatim|pointwise_head.gadt> fails because of the limitations
  of the <verbatim|type> sort in representing disequalities.

  <\code>
    datatype Z

    datatype S : type

    datatype List : type * num

    datacons LNil : <math|\<forall\>>a. List(a, Z)

    datacons LCons : <math|\<forall\>>a, b. a * List(a, b)
    <math|\<longrightarrow\>> List(a, S b)

    \;

    let head = function

    \ \ \| LCons (x, _) -\> x

    \ \ \| LNil -\> assert false
  </code>

  If we omit the <verbatim|LNil> branch, we get the technically correct but
  inadequate type <verbatim|<math|\<forall\>>a, b. List(a, b)
  <math|\<rightarrow\>> a>, because the type system does not guarantee
  exhaustiveness of the pattern matching. The intended type is
  <verbatim|<math|\<forall\>>a, b. List(a, S b) <math|\<rightarrow\>> a>.

  The example <verbatim|non_pointwise_fd_comp_harder.gadt> is inferred an
  insufficiently general type <verbatim|<math|\<forall\>>a, b. FunDesc (b, b)
  <math|\<rightarrow\>> FunDesc (b, a) <math|\<rightarrow\>> FunDesc (b, a)>.

  <\code>
    datatype FunDesc : type * type

    datacons FDI : <math|\<forall\>>a. FunDesc (a, a)

    datacons FDC : <math|\<forall\>>a, b. b <math|\<longrightarrow\>> FunDesc
    (a, b)

    datacons FDG : <math|\<forall\>>a, b. (a <math|\<rightarrow\>> b)
    <math|\<longrightarrow\>> FunDesc (a, b)

    external fd_fun : <math|\<forall\>>a, b. FunDesc (a, b)
    <math|\<rightarrow\>> a <math|\<rightarrow\>> b

    \;

    let fd_comp fd1 fd2 =

    \ \ let o f g x = f (g x) in

    \ \ match fd1 with

    \ \ \ \ \| FDI -\> fd2

    \ \ \ \ \| FDC b -\>\ 

    \ \ \ \ \ \ (match fd2 with

    \ \ \ \ \ \ \ \ \| FDI -\> fd1

    \ \ \ \ \ \ \ \ \| FDC c -\> FDC (fd_fun fd2 b)

    \ \ \ \ \ \ \ \ \| FDG g -\> FDC (fd_fun fd2 b))

    \ \ \ \ \| FDG f -\>

    \ \ \ \ \ \ (match fd2 with

    \ \ \ \ \ \ \ \ \| FDI -\> fd1

    \ \ \ \ \ \ \ \ \| FDC c -\> FDC c

    \ \ \ \ \ \ \ \ \| FDG g -\> FDG (o (fd_fun fd2) f))
  </code>

  This happens because the second argument <verbatim|fd2> is not expanded
  when <verbatim|fd1> is equal to <verbatim|FDI>. Type inference cannot carry
  out the different reasoning steps leading to the more general type.

  In the example <verbatim|liquid_bsearch2_harder4.gadt> it turns out to be
  too hard to infer the full postcondition.

  <\code>
    datatype Array : type * num

    external let array_make :

    \ \ <math|\<forall\>>n, a [0<math|\<leqslant\>>n]. Num n
    <math|\<rightarrow\>> a <math|\<rightarrow\>> Array (a, n) = "fun a b
    -\<gtr\> Array.make a b"

    external let array_get :

    <math|\<forall\>>n, k, a [0<math|\<leqslant\>>k <math|\<wedge\>>
    k+1<math|\<leqslant\>>n]. Array (a, n) <math|\<rightarrow\>> Num k
    <math|\<rightarrow\>> a =

    \ \ "fun a b -\<gtr\> Array.get a b"

    external let array_length :

    \ \ <math|\<forall\>>n, a [0<math|\<leqslant\>>n]. Array (a, n)
    <math|\<rightarrow\>> Num n = "fun a -\<gtr\> Array.length a"

    datatype LinOrder

    datacons LE : LinOrder

    datacons GT : LinOrder

    datacons EQ : LinOrder

    external let compare : <math|\<forall\>>a. a <math|\<rightarrow\>> a
    <math|\<rightarrow\>> LinOrder =

    \ \ "fun a b -\> let c = Pervasives.compare a b in

    \ \ \ \ \ \ \ \ \ \ \ \ \ \ if c \< 0 then LE else if c \> 0 then GT else
    EQ"

    external let equal : <math|\<forall\>>a. a <math|\<rightarrow\>> a
    <math|\<rightarrow\>> Bool = "fun a b -\<gtr\> a = b"

    external let div2 : <math|\<forall\>>n. Num (2 n) <math|\<rightarrow\>>
    Num n = "fun x -\<gtr\> x / 2"

    \;

    let bsearch key vec =

    \ \ let rec look key vec lo hi =

    \ \ \ \ eif lo \<= hi then

    \ \ \ \ \ \ \ \ let m = div2 (hi + lo) in

    \ \ \ \ \ \ \ \ let x = array_get vec m in

    \ \ \ \ \ \ \ \ ematch compare key x with

    \ \ \ \ \ \ \ \ \ \ \| LE -\> look key vec lo (m + (-1))

    \ \ \ \ \ \ \ \ \ \ \| GT -\> look key vec (m + 1) hi

    \ \ \ \ \ \ \ \ \ \ \| EQ -\> eif equal key x then m else -1

    \ \ \ \ else -1 in

    \ \ look key vec 0 (array_length vec + (-1))
  </code>

  \ We get the result type <verbatim|<math|\<exists\>>n[0 <math|\<leqslant\>>
  n + 1].Num n> instead of <verbatim|<math|\<exists\>>k[k <math|\<leqslant\>>
  n <math|\<wedge\>> 0 <math|\<leqslant\>> k + 1].Num k>. The inference of
  the intended type succeeds after we introduce an appropriate assertion,
  e.g. <verbatim|assert num -1 \<= hi>. Alternatively, we could include a use
  case for <verbatim|bsearch> where the full postcondition is required.

  Examples <verbatim|liquid_simplex_step_3.gadt>,
  <verbatim|liquid_simplex_step_4.gadt> and
  <verbatim|liquid_gauss_rowMax.gadt> result in uninformative, empty
  postconditions, because to tell more would require inspecting the behavior
  of the respective function across recursive calls. To save space, we list
  just the function definition from <verbatim|liquid_simplex_step_3.gadt>:

  <\code>
    let rec enter_var arr2 n j c j' =

    \ \ eif j' + 2 \<= n then

    \ \ \ \ let c' = matrix_get arr2 0 j' in

    \ \ \ \ eif less c' c then enter_var arr2 n j' c' (j'+1)

    \ \ \ \ else enter_var arr2 n j c (j'+1)

    \ \ else j
  </code>

  Fortunately, if the function is used in the same toplevel definition in
  which it is defined, use-site requirements facilitate the inference of the
  intended postcondition.

  The example <verbatim|liquid_gauss_harder.gadt> poses too big a challenge
  for <name|InvarGenT>. To get it pass the inference, we streamline one of
  the nested definitions, to not introduce another, unnecessary level of
  nesting. This gives the example <verbatim|liquid_gauss2.gadt>, which needs
  to be run with the option <verbatim|-prefer_bound_to_local>. Additionally,
  we can relax the constraint on the processed portion of the matrix, coming
  from the restriction on the matrix size intended in the original source of
  the <verbatim|liquid_gauss_harder.gadt> example. In
  <verbatim|liquid_gauss.gadt>, the whole matrix is processed and the
  inferred type is most general, under the default settings -- no need to
  pass any options to <name|InvarGenT>. The reason
  <verbatim|liquid_gauss_harder.gadt> is too difficult for <name|InvarGenT>
  is that the nesting interferes with the propagation of use-site constraints
  to the postcondition of the nested definition (the <verbatim|loop> inside
  <verbatim|rowMax>). Inference works for
  <verbatim|liquid_gauss_harder_asserted.gadt>, because the assertion
  provides the required information to infer the <verbatim|rowMax> invariants
  directly.
</body>

<\initial>
  <\collection>
    <associate|font-base-size|12>
    <associate|page-breaking|professional>
    <associate|page-medium|paper>
    <associate|page-type|letter>
    <associate|preamble|false>
  </collection>
</initial>

<\references>
  <\collection>
    <associate|AUAlg|<tuple|4.3|69>>
    <associate|AbdAlg|<tuple|4.2|58>>
    <associate|AbdAnsDef|<tuple|4.1|59>>
    <associate|AbdConstrnGenAlg|<tuple|B.3.3|126>>
    <associate|AbdConstrnGenMain|<tuple|4.3.3|68>>
    <associate|AbdNegConstrn|<tuple|4.3|?>>
    <associate|AbdNegMain|<tuple|4.3|?>>
    <associate|AbdUniVars|<tuple|4.2.1|15>>
    <associate|AlienSubterms|<tuple|B.2.1|123>>
    <associate|AntiUnifAlg|<tuple|B.1|127>>
    <associate|AppendAFEx|<tuple|5.3|72>>
    <associate|AtomizedForm|<tuple|4.12|69>>
    <associate|BadAVLAdd|<tuple|5.3|71>>
    <associate|BadExtract2|<tuple|5.2|70>>
    <associate|BadFdComp|<tuple|5.1|73>>
    <associate|CEquiv|<tuple|3.10|56>>
    <associate|CalcSynHMG|<tuple|2.1|25>>
    <associate|CaptureEscParams|<tuple|B.4|135>>
    <associate|ChapBackground|<tuple|2|21>>
    <associate|ChapProofs|<tuple|A|89>>
    <associate|ChapRelWork|<tuple|6|81>>
    <associate|ChapSolv|<tuple|4|57>>
    <associate|CnDerivHMG|<tuple|2.4|29>>
    <associate|CodeEx2|<tuple|1.1|19>>
    <associate|CodeEx3|<tuple|1.2|20>>
    <associate|CollectK|<tuple|3.10|50>>
    <associate|CompletePat|<tuple|A.8|95>>
    <associate|ConstrnGenAlg|<tuple|B.3|124>>
    <associate|ConstrnGenMain|<tuple|4.3|65>>
    <associate|CorAbdLUB|<tuple|4.11|68>>
    <associate|CorComplAbd|<tuple|4.4|60>>
    <associate|CorComplLUB|<tuple|4.8|66>>
    <associate|CorComplLUBThm|<tuple|4.10|66>>
    <associate|CorrPat|<tuple|A.7|91>>
    <associate|DMLSection|<tuple|2.1|21>>
    <associate|Details|<tuple|B.6.4|138>>
    <associate|DisjElim|<tuple|4.3|65>>
    <associate|DomainProp|<tuple|21|?>>
    <associate|EnvFragProp|<tuple|A.2|90>>
    <associate|ExBsearch2|<tuple|C.8.4|165>>
    <associate|ExCnBr1|<tuple|3.1|55>>
    <associate|ExCnBr2|<tuple|3.2|55>>
    <associate|ExCnBr3|<tuple|3.3|55>>
    <associate|ExCnBr4|<tuple|3.4|55>>
    <associate|ExCnBr5|<tuple|3.5|55>>
    <associate|ExCnBr6|<tuple|3.6|55>>
    <associate|ExGADTsProofs|<tuple|A.1.3|102>>
    <associate|ExIntermInf|<tuple|3.13|53>>
    <associate|ExTypes|<tuple|3.4|51>>
    <associate|ExTypesCns|<tuple|3.5|53>>
    <associate|ExTypesRed|<tuple|13|25>>
    <associate|ExTypingRul|<tuple|3.12|53>>
    <associate|ExamplesCode|<tuple|C|141>>
    <associate|Experiments|<tuple|5.1|74>>
    <associate|ExperimentsBounds|<tuple|5.3|76>>
    <associate|ExperimentsNum|<tuple|5.2|75>>
    <associate|ExprSyn|<tuple|3.2|43>>
    <associate|FFTExample|<tuple|C.8.13|185>>
    <associate|FailureCases|<tuple|5.2|76>>
    <associate|FdCompFail|<tuple|5.1|?>>
    <associate|GADTProofs|<tuple|A.1.2|90>>
    <associate|HMGClauseRule|<tuple|2.1|27>>
    <associate|HMGSection|<tuple|2.2|24>>
    <associate|HMGSoundness|<tuple|2.3|28>>
    <associate|HMGVarRule|<tuple|2.2|28>>
    <associate|HerbAbdAlg|<tuple|2.5|39>>
    <associate|HerbSection|<tuple|2.6|38>>
    <associate|ImplSubst|<tuple|A.15|109>>
    <associate|ImplUnderQ|<tuple|1|7|invargent-thesis.tm>>
    <associate|InfComplCoro|<tuple|3.3|47>>
    <associate|InfComplExpr|<tuple|3.2|46>>
    <associate|InfCorrComplEx|<tuple|3.7|54>>
    <associate|InfCorrExpr|<tuple|3.1|46>>
    <associate|InferCompleteness|<tuple|4.16|71>>
    <associate|IntermInf|<tuple|3.7|48>>
    <associate|IntermInfClaus|<tuple|3.8|49>>
    <associate|IntermInfPat|<tuple|3.6|47>>
    <associate|InterprPredVars|<tuple|A.1|89>>
    <associate|Intro|<tuple|1|15>>
    <associate|IsExBrs|<tuple|3.9|49>>
    <associate|JCA|<tuple|4.2.2|15>>
    <associate|JCAAlg|<tuple|B.2.2|117>>
    <associate|JCAAlienAlg|<tuple|B.2.1|116>>
    <associate|JCAAlienMain|<tuple|4.2.2|60>>
    <associate|JCAMain|<tuple|4.2.3|61>>
    <associate|LUBAlg|<tuple|4.2|67>>
    <associate|LUBProofs|<tuple|A.3|109>>
    <associate|Limitations|<tuple|5|73>>
    <associate|LiqAlgR1|<tuple|2.3|36>>
    <associate|LiqAlgR2|<tuple|2.4|36>>
    <associate|LiqAlgR3|<tuple|2.5|36>>
    <associate|LiqAlgR4|<tuple|2.6|?>>
    <associate|LiquidSection|<tuple|2.5|35>>
    <associate|LiquidTypeAlg|<tuple|2.5|?>>
    <associate|MSODef|<tuple|3.1|5>>
    <associate|MaherHerbSolve|<tuple|2.4|38>>
    <associate|MaherJCASolve|<tuple|2.5|38>>
    <associate|MainAlg|<tuple|4.1|57>>
    <associate|MainAlgEnt1|<tuple|4.1|72>>
    <associate|MainAlgEnt2|<tuple|4.2|72>>
    <associate|MainAlgEnt3|<tuple|4.3|72>>
    <associate|MainAlgEnt4|<tuple|4.4|72>>
    <associate|MainAlgEnt5|<tuple|4.5|72>>
    <associate|MainAlgEnt6|<tuple|4.6|72>>
    <associate|MainAlgEnt7|<tuple|4.7|72>>
    <associate|MainAlgEnt8|<tuple|4.8|72>>
    <associate|MainAlgIter|<tuple|4.4|72>>
    <associate|MainAlgo|<tuple|B.6|134>>
    <associate|MainAlgoBody|<tuple|B.6.2|134>>
    <associate|ModelDef|<tuple|20|?>>
    <associate|MonoEnvEq|<tuple|A.9|96>>
    <associate|MoreCstrs|<tuple|A.6|91>>
    <associate|MultisortAbd|<tuple|4.1|62>>
    <associate|MultisortAbdLemma|<tuple|11|17>>
    <associate|MultisortAbdThm|<tuple|4.5|61>>
    <associate|NegElim|<tuple|B.4|131>>
    <associate|NegElimAlg|<tuple|B.4|128>>
    <associate|NegElimMain|<tuple|4.4|68>>
    <associate|NormConstrn|<tuple|B.1|113>>
    <associate|NormExpr|<tuple|3.11|52>>
    <associate|NormalFormProp|<tuple|3.4|50>>
    <associate|NumAbdAlg|<tuple|4.2|66>>
    <associate|NumAbdCorr|<tuple|4.8|65>>
    <associate|NumConstrnGenAlg|<tuple|B.3.1|125>>
    <associate|NumConv|<tuple|B.3.2|125>>
    <associate|OpComplLemma|<tuple|A.19|111>>
    <associate|OpCorrectLemma|<tuple|A.17|111>>
    <associate|OptiAtoms|<tuple|B.5|129>>
    <associate|OutsideInSection|<tuple|2.3|30>>
    <associate|PointwiseSection|<tuple|2.4|32>>
    <associate|PredVarAlg|<tuple|B.6|131>>
    <associate|PredVarMain|<tuple|4.5|68>>
    <associate|PredVarOverview|<tuple|4.1|57>>
    <associate|PredVarProofs|<tuple|A.4|110>>
    <associate|PredVarSolvDetails|<tuple|4.5|70>>
    <associate|PredVarSubstDeriv|<tuple|A.10|104>>
    <associate|Rg|<tuple|B.3|135>>
    <associate|SCANumAlg|<tuple|B.2.4|121>>
    <associate|SCANumMain|<tuple|4.2.4.2|64>>
    <associate|SCATerms|<tuple|4.2.4.1|119>>
    <associate|SCATermsAlg|<tuple|B.2.3|118>>
    <associate|SCATermsMain|<tuple|4.2.4.1|63>>
    <associate|SCAlinear|<tuple|B.2.4|124>>
    <associate|SecAbduction|<tuple|4.2|58>>
    <associate|SecFutWork|<tuple|6.2|83>>
    <associate|SecRelWork|<tuple|6.1|81>>
    <associate|SemNormForm|<tuple|3.9|56>>
    <associate|SemRedHMG|<tuple|3.11|56>>
    <associate|SemantHMG|<tuple|2.3|27>>
    <associate|SemanticProofs|<tuple|A.1.4|104>>
    <associate|SepProp|<tuple|A.13|109>>
    <associate|Skp|<tuple|1|18|invargent-thesis.tm>>
    <associate|Skp1|<tuple|B.9|135>>
    <associate|SolTypInfer|<tuple|3.5|50>>
    <associate|SolvedForm|<tuple|A.11|106>>
    <associate|SolvedFormProj|<tuple|A.12|106>>
    <associate|SortCombProof|<tuple|A.2.2|106>>
    <associate|SplitAlg|<tuple|4.3|70>>
    <associate|SplitProps|<tuple|A.16|110>>
    <associate|SubstHMG|<tuple|2.2|25>>
    <associate|ThCorrect|<tuple|4.15|71>>
    <associate|TypInfCns|<tuple|3.3|46>>
    <associate|TypRulClaus|<tuple|3.5|45>>
    <associate|TypRulExpr|<tuple|3.4|44>>
    <associate|TypRulPat|<tuple|3.3|43>>
    <associate|TypSys|<tuple|3.2|42>>
    <associate|TypeSoundness|<tuple|3.12|56>>
    <associate|TypeSyn|<tuple|3.1|42>>
    <associate|TypingRul|<tuple|<with|mode|<quote|math>|\<bullet\>>|5>>
    <associate|TypingRul1|<tuple|4|6>>
    <associate|Weakening|<tuple|A.5|91>>
    <associate|WellTypedEx|<tuple|3.6|52>>
    <associate|auto-1|<tuple|?|5>>
    <associate|auto-10|<tuple|2.1|21>>
    <associate|auto-100|<tuple|A.2.2|106>>
    <associate|auto-101|<tuple|A.3|109>>
    <associate|auto-102|<tuple|A.4|110>>
    <associate|auto-103|<tuple|B|113>>
    <associate|auto-104|<tuple|B.1|113>>
    <associate|auto-105|<tuple|B.1.1|115>>
    <associate|auto-106|<tuple|B.1.1.1|115>>
    <associate|auto-107|<tuple|B.1.2|115>>
    <associate|auto-108|<tuple|B.2|116>>
    <associate|auto-109|<tuple|B.2.1|116>>
    <associate|auto-11|<tuple|2.1.1|22>>
    <associate|auto-110|<tuple|B.2.2|117>>
    <associate|auto-111|<tuple|B.2.3|118>>
    <associate|auto-112|<tuple|B.2.3.1|121>>
    <associate|auto-113|<tuple|B.2.4|121>>
    <associate|auto-114|<tuple|B.3|124>>
    <associate|auto-115|<tuple|B.3.1|125>>
    <associate|auto-116|<tuple|B.3.2|125>>
    <associate|auto-117|<tuple|B.3.3|126>>
    <associate|auto-118|<tuple|B.1|127>>
    <associate|auto-119|<tuple|B.4|128>>
    <associate|auto-12|<tuple|2.1.2|23>>
    <associate|auto-120|<tuple|B.5|129>>
    <associate|auto-121|<tuple|B.5.1|130>>
    <associate|auto-122|<tuple|B.5.2|130>>
    <associate|auto-123|<tuple|B.5.3|131>>
    <associate|auto-124|<tuple|B.6|131>>
    <associate|auto-125|<tuple|B.6.1|132>>
    <associate|auto-126|<tuple|B.6.2|134>>
    <associate|auto-127|<tuple|B.6.3|137>>
    <associate|auto-128|<tuple|B.6.4|138>>
    <associate|auto-129|<tuple|B.7|139>>
    <associate|auto-13|<tuple|2.1.3|23>>
    <associate|auto-130|<tuple|C|141>>
    <associate|auto-131|<tuple|C.1|141>>
    <associate|auto-132|<tuple|C.2|141>>
    <associate|auto-133|<tuple|C.2.1|141>>
    <associate|auto-134|<tuple|C.2.2|142>>
    <associate|auto-135|<tuple|C.2.3|143>>
    <associate|auto-136|<tuple|C.2.4|143>>
    <associate|auto-137|<tuple|C.2.5|145>>
    <associate|auto-138|<tuple|C.2.6|146>>
    <associate|auto-139|<tuple|C.3|146>>
    <associate|auto-14|<tuple|2.2|24>>
    <associate|auto-140|<tuple|C.3.1|146>>
    <associate|auto-141|<tuple|C.3.2|147>>
    <associate|auto-142|<tuple|C.3.3|148>>
    <associate|auto-143|<tuple|C.3.4|149>>
    <associate|auto-144|<tuple|C.3.5|150>>
    <associate|auto-145|<tuple|C.3.6|151>>
    <associate|auto-146|<tuple|C.3.7|152>>
    <associate|auto-147|<tuple|C.4|152>>
    <associate|auto-148|<tuple|C.4.1|152>>
    <associate|auto-149|<tuple|C.4.2|153>>
    <associate|auto-15|<tuple|2.2.1|24>>
    <associate|auto-150|<tuple|C.5|154>>
    <associate|auto-151|<tuple|C.5.1|154>>
    <associate|auto-152|<tuple|C.5.2|155>>
    <associate|auto-153|<tuple|C.5.3|156>>
    <associate|auto-154|<tuple|C.5.4|156>>
    <associate|auto-155|<tuple|C.5.5|156>>
    <associate|auto-156|<tuple|C.6|157>>
    <associate|auto-157|<tuple|C.6.1|157>>
    <associate|auto-158|<tuple|C.6.2|158>>
    <associate|auto-159|<tuple|C.6.3|158>>
    <associate|auto-16|<tuple|2.1|25>>
    <associate|auto-160|<tuple|C.7|159>>
    <associate|auto-161|<tuple|C.8|163>>
    <associate|auto-162|<tuple|C.8.1|163>>
    <associate|auto-163|<tuple|C.8.2|164>>
    <associate|auto-164|<tuple|C.8.3|164>>
    <associate|auto-165|<tuple|C.8.4|165>>
    <associate|auto-166|<tuple|C.8.5|167>>
    <associate|auto-167|<tuple|C.8.6|168>>
    <associate|auto-168|<tuple|C.8.7|169>>
    <associate|auto-169|<tuple|C.8.8|169>>
    <associate|auto-17|<tuple|2.2|25>>
    <associate|auto-170|<tuple|C.8.9|171>>
    <associate|auto-171|<tuple|C.8.10|172>>
    <associate|auto-172|<tuple|C.8.11|174>>
    <associate|auto-173|<tuple|C.8.12|181>>
    <associate|auto-174|<tuple|C.8.13|185>>
    <associate|auto-175|<tuple|D|191>>
    <associate|auto-176|<tuple|D.1|191>>
    <associate|auto-177|<tuple|D.2|191>>
    <associate|auto-178|<tuple|D.3|198>>
    <associate|auto-179|<tuple|D.4|200>>
    <associate|auto-18|<tuple|2.3|27>>
    <associate|auto-180|<tuple|D.5|207>>
    <associate|auto-181|<tuple|D.5|211>>
    <associate|auto-19|<tuple|2.2.2|26>>
    <associate|auto-2|<tuple|?|7>>
    <associate|auto-20|<tuple|2.2.3|28>>
    <associate|auto-21|<tuple|2.4|29>>
    <associate|auto-22|<tuple|2.2.4|29>>
    <associate|auto-23|<tuple|2.3|30>>
    <associate|auto-24|<tuple|2.3.1|30>>
    <associate|auto-25|<tuple|2.3.2|31>>
    <associate|auto-26|<tuple|2.4|32>>
    <associate|auto-27|<tuple|2.4.1|32>>
    <associate|auto-28|<tuple|2.4.2|34>>
    <associate|auto-29|<tuple|2.5|35>>
    <associate|auto-3|<tuple|?|9>>
    <associate|auto-30|<tuple|2.5.1|35>>
    <associate|auto-31|<tuple|2.5.2|36>>
    <associate|auto-32|<tuple|2.5.3|37>>
    <associate|auto-33|<tuple|2.6|38>>
    <associate|auto-34|<tuple|2.5|39>>
    <associate|auto-35|<tuple|2.6.1|39>>
    <associate|auto-36|<tuple|3|41>>
    <associate|auto-37|<tuple|3.1|41>>
    <associate|auto-38|<tuple|3.1|42>>
    <associate|auto-39|<tuple|3.2|42>>
    <associate|auto-4|<tuple|1|15>>
    <associate|auto-40|<tuple|3.2|43>>
    <associate|auto-41|<tuple|3.3|43>>
    <associate|auto-42|<tuple|3.4|44>>
    <associate|auto-43|<tuple|3.5|45>>
    <associate|auto-44|<tuple|3.3|46>>
    <associate|auto-45|<tuple|3.6|47>>
    <associate|auto-46|<tuple|3.7|48>>
    <associate|auto-47|<tuple|3.8|49>>
    <associate|auto-48|<tuple|3.9|49>>
    <associate|auto-49|<tuple|3.10|50>>
    <associate|auto-5|<tuple|1.1|17>>
    <associate|auto-50|<tuple|3.4|51>>
    <associate|auto-51|<tuple|3.11|52>>
    <associate|auto-52|<tuple|3.12|53>>
    <associate|auto-53|<tuple|3.13|53>>
    <associate|auto-54|<tuple|3.5|53>>
    <associate|auto-55|<tuple|3.6|55>>
    <associate|auto-56|<tuple|4|57>>
    <associate|auto-57|<tuple|4.1|57>>
    <associate|auto-58|<tuple|4.2|58>>
    <associate|auto-59|<tuple|4.2.1|59>>
    <associate|auto-6|<tuple|1.2|18>>
    <associate|auto-60|<tuple|4.2.2|60>>
    <associate|auto-61|<tuple|4.1|62>>
    <associate|auto-62|<tuple|4.2.3|61>>
    <associate|auto-63|<tuple|4.2.4|63>>
    <associate|auto-64|<tuple|4.2.4.1|63>>
    <associate|auto-65|<tuple|4.2.4.2|64>>
    <associate|auto-66|<tuple|4.3|65>>
    <associate|auto-67|<tuple|4.3.1|66>>
    <associate|auto-68|<tuple|4.2|67>>
    <associate|auto-69|<tuple|4.3.2|67>>
    <associate|auto-7|<tuple|1.1|19>>
    <associate|auto-70|<tuple|4.3.3|68>>
    <associate|auto-71|<tuple|4.4|68>>
    <associate|auto-72|<tuple|4.5|68>>
    <associate|auto-73|<tuple|5|70>>
    <associate|auto-74|<tuple|4.8|72>>
    <associate|auto-75|<tuple|5|73>>
    <associate|auto-76|<tuple|5.1|73>>
    <associate|auto-77|<tuple|5.1|74>>
    <associate|auto-78|<tuple|5.2|75>>
    <associate|auto-79|<tuple|5.3|76>>
    <associate|auto-8|<tuple|1.2|20>>
    <associate|auto-80|<tuple|5.2|76>>
    <associate|auto-81|<tuple|5.2.1|76>>
    <associate|auto-82|<tuple|5.2.2|77>>
    <associate|auto-83|<tuple|5.2.3|78>>
    <associate|auto-84|<tuple|5.2.4|78>>
    <associate|auto-85|<tuple|5.2.5|79>>
    <associate|auto-86|<tuple|5.2.6|79>>
    <associate|auto-87|<tuple|6|81>>
    <associate|auto-88|<tuple|6.1|81>>
    <associate|auto-89|<tuple|6.2|83>>
    <associate|auto-9|<tuple|2|21>>
    <associate|auto-90|<tuple|6.3|84>>
    <associate|auto-91|<tuple|6.3|85>>
    <associate|auto-92|<tuple|A|89>>
    <associate|auto-93|<tuple|A.1|89>>
    <associate|auto-94|<tuple|A.1.1|89>>
    <associate|auto-95|<tuple|A.1.2|90>>
    <associate|auto-96|<tuple|A.1.3|102>>
    <associate|auto-97|<tuple|A.1.4|104>>
    <associate|auto-98|<tuple|A.2|106>>
    <associate|auto-99|<tuple|A.2.1|106>>
    <associate|bib-ADTReconstruct|<tuple|44|87>>
    <associate|bib-AbdEADTs|<tuple|49|87>>
    <associate|bib-AbductionLinArithMaher|<tuple|26|86>>
    <associate|bib-AbductionMaher|<tuple|27|86>>
    <associate|bib-AbductionSequents|<tuple|31|86>>
    <associate|bib-AbductionSolvMaher|<tuple|29|86>>
    <associate|bib-AbstractLiquid|<tuple|52|87>>
    <associate|bib-AbstractStateGraphs|<tuple|17|86>>
    <associate|bib-AntiUnifAlg|<tuple|61|88>>
    <associate|bib-AntiUnifInv|<tuple|7|85>>
    <associate|bib-AntiUnifPlotkin|<tuple|35|86>>
    <associate|bib-AntiUnifReynolds|<tuple|37|86>>
    <associate|bib-ArithQuantElim|<tuple|4|85>>
    <associate|bib-AssertionGraphs|<tuple|1|85>>
    <associate|bib-CEGAR|<tuple|21|86>>
    <associate|bib-Cayenne|<tuple|2|85>>
    <associate|bib-CheneyHinzePhantomTypes|<tuple|8|85>>
    <associate|bib-ComplDecidableGADTs|<tuple|45|87>>
    <associate|bib-ConvexHull|<tuple|16|85>>
    <associate|bib-Cousot77|<tuple|10|85>>
    <associate|bib-DBLP:conf/ppdp/2006|<tuple|2|14>>
    <associate|bib-DML99|<tuple|57|87>>
    <associate|bib-DMLArrays|<tuple|56|87>>
    <associate|bib-DMLThesis|<tuple|54|87>>
    <associate|bib-DSolvePaper|<tuple|41|87>>
    <associate|bib-DSolveTechRep|<tuple|42|87>>
    <associate|bib-DSolveThesis|<tuple|40|87>>
    <associate|bib-DecidableGADTs|<tuple|41|89>>
    <associate|bib-DisunificationComon|<tuple|9|85>>
    <associate|bib-ExTyADTs|<tuple|24|86>>
    <associate|bib-Flanagan06|<tuple|13|85>>
    <associate|bib-HMX|<tuple|34|86>>
    <associate|bib-Henglein93|<tuple|18|86>>
    <associate|bib-HeytingAbdMaher|<tuple|28|86>>
    <associate|bib-IdrisCurrent|<tuple|5|85>>
    <associate|bib-IdrisEarly|<tuple|6|85>>
    <associate|bib-IndexedTypes|<tuple|58|88>>
    <associate|bib-InductLoopInv|<tuple|12|85>>
    <associate|bib-InterpolationInfer|<tuple|51|87>>
    <associate|bib-InvarGenT|<tuple|24|12>>
    <associate|bib-InvarGenTMan|<tuple|25|12>>
    <associate|bib-KnowlesF07|<tuple|20|86>>
    <associate|bib-LightDML|<tuple|59|88>>
    <associate|bib-LoopQuantElim|<tuple|19|86>>
    <associate|bib-MaherParamSubstitutions|<tuple|25|86>>
    <associate|bib-MartinLof|<tuple|30|86>>
    <associate|bib-Milner78|<tuple|32|86>>
    <associate|bib-Mycroft84|<tuple|33|86>>
    <associate|bib-OutsideIn|<tuple|53|87>>
    <associate|bib-PointwiseGADTs|<tuple|23|86>>
    <associate|bib-PracticalGADTsInfer|<tuple|22|86>>
    <associate|bib-RefinementFreemanPfenning|<tuple|15|85>>
    <associate|bib-RodriKapurICTAC04|<tuple|38|87>>
    <associate|bib-RodriKapurJSC07|<tuple|39|87>>
    <associate|bib-Sheard04|<tuple|46|87>>
    <associate|bib-SpecLearnArrays|<tuple|60|88>>
    <associate|bib-StratifiedGADTs|<tuple|36|86>>
    <associate|bib-SulzmannAbdGADTs|<tuple|48|87>>
    <associate|bib-SulzmannAbdGADTsRep|<tuple|50|87>>
    <associate|bib-TypeQualifiers|<tuple|14|85>>
    <associate|bib-UnificationBaader|<tuple|3|85>>
    <associate|bib-XiGRDTs|<tuple|55|87>>
    <associate|bib-disjelimTechRep|<tuple|27|57|invargent-thesis.tm>>
    <associate|bib-invariantsTechRep|<tuple|18|?>>
    <associate|bib-jcaqpTechRep|<tuple|28|57>>
    <associate|bib-jcaqpUNIF|<tuple|18|12>>
    <associate|bib-regis-gianas-pottier-08|<tuple|43|87>>
    <associate|bib-simonet-pottier-hmg-toplas|<tuple|47|87>>
    <associate|bib-simulRigidEUnifUndec|<tuple|11|85>>
    <associate|bib-systemTechRep|<tuple|26|57|invargent-thesis.tm>>
    <associate|collapse-ty-args|<tuple|A.4|91>>
    <associate|firstHeading|<tuple|3|?>>
  </collection>
</references>

<\auxiliary>
  <\collection>
    <\associate|bib>
      StratifiedGADTs

      ComplDecidableGADTs

      PointwiseGADTs

      simonet-pottier-hmg-toplas

      StratifiedGADTs

      ComplDecidableGADTs

      PointwiseGADTs

      ADTReconstruct

      InterpolationInfer

      DML99

      DML99

      KnowlesF07

      InterpolationInfer

      DML99

      PointwiseGADTs

      DSolvePaper

      PracticalGADTsInfer

      PracticalGADTsInfer

      DSolvePaper

      DSolvePaper

      DML99

      DMLArrays

      DSolvePaper

      SpecLearnArrays

      MartinLof

      Cayenne

      IdrisCurrent

      IdrisEarly

      DML99

      simonet-pottier-hmg-toplas

      OutsideIn

      PointwiseGADTs

      DSolvePaper

      DSolveTechRep

      DSolveThesis

      AbductionSolvMaher

      simonet-pottier-hmg-toplas

      DML99

      DMLThesis

      IndexedTypes

      ExTyADTs

      HMX

      XiGRDTs

      CheneyHinzePhantomTypes

      Sheard04

      simonet-pottier-hmg-toplas

      IndexedTypes

      simonet-pottier-hmg-toplas

      simonet-pottier-hmg-toplas

      simonet-pottier-hmg-toplas

      simonet-pottier-hmg-toplas

      OutsideIn

      ComplDecidableGADTs

      OutsideIn

      OutsideIn

      OutsideIn

      OutsideIn

      OutsideIn

      AbductionSolvMaher

      OutsideIn

      OutsideIn

      PracticalGADTsInfer

      PointwiseGADTs

      PracticalGADTsInfer

      Milner78

      Mycroft84

      PracticalGADTsInfer

      PracticalGADTsInfer

      PracticalGADTsInfer

      RefinementFreemanPfenning

      HMX

      Flanagan06

      KnowlesF07

      DSolvePaper

      AbstractLiquid

      DSolvePaper

      DSolveTechRep

      DSolveThesis

      DSolvePaper

      AssertionGraphs

      AbstractStateGraphs

      TypeQualifiers

      DSolvePaper

      DSolvePaper

      KnowlesF07

      AbstractLiquid

      SulzmannAbdGADTsRep

      SulzmannAbdGADTs

      AbdEADTs

      AbductionMaher

      AbductionSolvMaher

      AbductionLinArithMaher

      AbductionSolvMaher

      AbductionSolvMaher

      AbductionSolvMaher

      AbductionMaher

      SulzmannAbdGADTs

      AbdEADTs

      AbductionSolvMaher

      AbductionLinArithMaher

      simonet-pottier-hmg-toplas

      simonet-pottier-hmg-toplas

      simonet-pottier-hmg-toplas

      simonet-pottier-hmg-toplas

      simonet-pottier-hmg-toplas

      KnowlesF07

      AbductionSolvMaher

      AbdEADTs

      Cousot77

      AbductionSequents

      AbductionMaher

      AbductionMaher

      UnificationBaader

      UnificationBaader

      AbductionMaher

      AbductionMaher

      InductLoopInv

      simulRigidEUnifUndec

      DisunificationComon

      DisunificationComon

      AbductionMaher

      AbductionSolvMaher

      AbductionMaher

      MaherParamSubstitutions

      AbductionSolvMaher

      AbductionSolvMaher

      PracticalGADTsInfer

      AbductionSolvMaher

      AbductionLinArithMaher

      UnificationBaader

      AntiUnifAlg

      ConvexHull

      PracticalGADTsInfer

      PracticalGADTsInfer

      OutsideIn

      PointwiseGADTs

      PointwiseGADTs

      DSolvePaper

      DSolvePaper

      DSolveThesis

      DSolvePaper

      PracticalGADTsInfer

      PracticalGADTsInfer

      PracticalGADTsInfer

      DML99

      DML99

      DML99

      simonet-pottier-hmg-toplas

      Henglein93

      Cousot77

      Mycroft84

      KnowlesF07

      regis-gianas-pottier-08

      DSolvePaper

      AbstractLiquid

      AbdEADTs

      SulzmannAbdGADTs

      AbdEADTs

      SulzmannAbdGADTs

      AbductionMaher

      AbductionSolvMaher

      UnificationBaader

      AbductionSolvMaher

      AbductionLinArithMaher

      HeytingAbdMaher

      InterpolationInfer

      KnowlesF07

      LightDML

      CEGAR

      SpecLearnArrays

      SpecLearnArrays

      ADTReconstruct

      StratifiedGADTs

      ComplDecidableGADTs

      PointwiseGADTs

      PracticalGADTsInfer

      OutsideIn

      PracticalGADTsInfer

      ADTReconstruct

      PracticalGADTsInfer

      ADTReconstruct

      InductLoopInv

      InductLoopInv

      InductLoopInv

      InductLoopInv

      InductLoopInv

      InductLoopInv

      LoopQuantElim

      LoopQuantElim

      RodriKapurICTAC04

      RodriKapurJSC07

      LoopQuantElim

      RodriKapurICTAC04

      RodriKapurICTAC04

      RodriKapurJSC07

      AntiUnifPlotkin

      AntiUnifReynolds

      AntiUnifInv

      ConvexHull

      DSolvePaper

      AbstractLiquid

      LightDML

      AbductionSolvMaher

      simonet-pottier-hmg-toplas

      simonet-pottier-hmg-toplas

      simonet-pottier-hmg-toplas

      simonet-pottier-hmg-toplas

      AbductionSolvMaher

      PracticalGADTsInfer

      AbductionSolvMaher

      ArithQuantElim

      ArithQuantElim

      AntiUnifAlg

      ConvexHull

      ConvexHull

      OutsideIn

      PointwiseGADTs

      PracticalGADTsInfer

      PracticalGADTsInfer

      PracticalGADTsInfer

      PracticalGADTsInfer

      PracticalGADTsInfer

      PracticalGADTsInfer

      PointwiseGADTs

      PracticalGADTsInfer

      PracticalGADTsInfer

      PracticalGADTsInfer

      PracticalGADTsInfer

      PracticalGADTsInfer

      PracticalGADTsInfer

      PracticalGADTsInfer
    </associate>
    <\associate|table>
      <tuple|normal|Use of existential types|<pageref|auto-7>>

      <tuple|normal|Two ways of constraining types|<pageref|auto-8>>

      <tuple|normal|Syntax of the calculus for
      <with|mode|<quote|math>|HMG<around*|(|X|)>>|<pageref|auto-16>>

      <tuple|normal|Extended substitution for
      <with|mode|<quote|math>|HMG<around*|(|X|)>>|<pageref|auto-17>>

      <tuple|normal|Operational semantics for
      <with|mode|<quote|math>|HMG<around*|(|X|)>>|<pageref|auto-18>>

      <tuple|normal|Constraint derivation for
      <with|mode|<quote|math>|HMG<around*|(|X|)>>: expressions and
      clauses|<pageref|auto-21>>

      <tuple|normal|SCA algorithm for computing fully maximal answers, JCA
      algorithm|<pageref|auto-34>>

      <tuple|normal|Abstract syntax of types and type
      schemes|<pageref|auto-38>>

      <tuple|normal|Abstract syntax of expressions|<pageref|auto-40>>

      <tuple|normal|Typing rules for <with|mode|<quote|math>|MMG<around*|(|X|)>><with|mode|<quote|math>|:
      patterns>|<pageref|auto-41>>

      <tuple|normal|Typing rules for <with|mode|<quote|math>|MMG<around*|(|num|)>>:
      expressions|<pageref|auto-42>>

      <tuple|normal|Typing rules for <with|mode|<quote|math>|MMG<around*|(|num|)>>:
      clauses|<pageref|auto-43>>

      <tuple|normal|Type inference for patterns|<pageref|auto-45>>

      <tuple|normal|Type inference for expressions|<pageref|auto-46>>

      <tuple|normal|Type inference for clauses|<pageref|auto-47>>

      <tuple|normal|Expressions that directly handle an existential
      type|<pageref|auto-48>>

      <tuple|normal|Collect introduced value constructors|<pageref|auto-49>>

      <tuple|normal|Flatten nested introductions of existential
      types|<pageref|auto-51>>

      <tuple|normal|Typing rules added by
      <with|mode|<quote|math>|MMG<rsub|\<exists\>><around*|(|X|)>>|<pageref|auto-52>>

      <tuple|normal|Type inference for the added
      expressions|<pageref|auto-53>>

      <tuple|normal|Complete multi-sorted abduction
      <with|mode|<quote|math>|Abd<around*|(|\<cal-Q\>,<wide|\<beta\>|\<bar\>>,<wide|D<rsub|i>,C<rsub|i>|\<bar\>>|)>>|<pageref|auto-61>>

      <tuple|normal|LUB algorithm <with|mode|<quote|math>|LUB<around*|(|<wide|D<rsub|i>|\<bar\>>|)>=\<exists\><wide|\<alpha\>|\<bar\>>.A>|<pageref|auto-68>>

      <tuple|normal|Split routine <with|mode|<quote|math>|Split<around*|(|\<cal-Q\>,<wide|\<alpha\>|\<bar\>>,A,<wide|<wide|\<beta\>|\<bar\>><rsup|\<chi\>>|\<bar\>>,<wide|A<rsub|\<chi\>>|\<bar\>>|)>>|<pageref|auto-73>>

      <tuple|normal|Iteration <with|mode|<quote|math>|k> of solving for
      predicate variables|<pageref|auto-74>>

      <tuple|normal|Examples of types and inference times, plain
      GADTs|<pageref|auto-77>>

      <tuple|normal|Examples of types and inference times, with numerical
      constraints and existentials|<pageref|auto-78>>

      <tuple|normal|Examples of inference times, bound
      checking|<pageref|auto-79>>

      <tuple|normal|Abductive anti-unification algorithm|<pageref|auto-118>>
    </associate>
    <\associate|toc>
      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|font-shape|<quote|small-caps>|Abstract>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <pageref|auto-1><vspace|0.5fn>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|font-shape|<quote|small-caps>|Streszczenie>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <pageref|auto-2><vspace|0.5fn>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|font-shape|<quote|small-caps>|Acknowledgements>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <pageref|auto-3><vspace|0.5fn>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|font-shape|<quote|small-caps>|1.<space|2spc>Introduction>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <pageref|auto-4><vspace|0.5fn>

      1.1.<space|2spc>Contributions <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-5>

      1.2.<space|2spc>Examples <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-6>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|font-shape|<quote|small-caps>|2.<space|2spc>Background
      and Related Work> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <pageref|auto-9><vspace|0.5fn>

      2.1.<space|2spc>The DML System <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-10>

      <with|par-left|<quote|1tab>|2.1.1.<space|2spc>The Type System
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-11>>

      <with|par-left|<quote|1tab>|2.1.2.<space|2spc>Bidirectional Type
      Inference <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-12>>

      <with|par-left|<quote|1tab>|2.1.3.<space|2spc>Relevance
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-13>>

      2.2.<space|2spc>The <with|mode|<quote|math>|HMG<around*|(|X|)>>
      Formalization <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-14>

      <with|par-left|<quote|1tab>|2.2.1.<space|2spc>The Untyped Calculus
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-15>>

      <with|par-left|<quote|1tab>|2.2.2.<space|2spc>The
      <with|mode|<quote|math>|HMG<around*|(|X|)>> Type System
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-19>>

      <with|par-left|<quote|1tab>|2.2.3.<space|2spc>Constraint Derivation
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-20>>

      <with|par-left|<quote|1tab>|2.2.4.<space|2spc>Relevance
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-22>>

      2.3.<space|2spc>The <with|mode|<quote|math>|OutsideIn<around*|(|X|)>>
      System <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-23>

      <with|par-left|<quote|1tab>|2.3.1.<space|2spc>Type Inference
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-24>>

      <with|par-left|<quote|1tab>|2.3.2.<space|2spc>Relevance
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-25>>

      2.4.<space|2spc>Pointwise GADTs <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-26>

      <with|par-left|<quote|1tab>|2.4.1.<space|2spc>Type Inference
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-27>>

      <with|par-left|<quote|1tab>|2.4.2.<space|2spc>Relevance
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-28>>

      2.5.<space|2spc>Liquid Types <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-29>

      <with|par-left|<quote|1tab>|2.5.1.<space|2spc>The Type System
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-30>>

      <with|par-left|<quote|1tab>|2.5.2.<space|2spc>Liquid Types Inference
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-31>>

      <with|par-left|<quote|1tab>|2.5.3.<space|2spc>Relevance
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-32>>

      2.6.<space|2spc>Herbrand Constraint Abduction
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-33>

      <with|par-left|<quote|1tab>|2.6.1.<space|2spc>Relevance
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-35>>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|font-shape|<quote|small-caps>|3.<space|2spc>The
      Type System> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <pageref|auto-36><vspace|0.5fn>

      3.1.<space|2spc>The Language of Constraints
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-37>

      3.2.<space|2spc>The Type System with GADTs
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-39>

      3.3.<space|2spc>Type Inference Constraints
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-44>

      3.4.<space|2spc>Existential Types <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-50>

      3.5.<space|2spc>Type Inference Constraints for Existential Types
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-54>

      3.6.<space|2spc>Semantics by Reduction to
      <with|mode|<quote|math>|HMG<around*|(|X|)>>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-55>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|font-shape|<quote|small-caps>|4.<space|2spc>Solving
      Second Order Constraints> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <pageref|auto-56><vspace|0.5fn>

      4.1.<space|2spc>Overview of Solving for Predicate Variables
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-57>

      4.2.<space|2spc>Constraint Abduction
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-58>

      <with|par-left|<quote|1tab>|4.2.1.<space|2spc>Formulating the Joint
      Constraint Abduction Problem <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-59>>

      <with|par-left|<quote|1tab>|4.2.2.<space|2spc>Abduction Algorithm for
      The Combination of Domains <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-60>>

      <with|par-left|<quote|1tab>|4.2.3.<space|2spc>Joint Constraint
      Abduction <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-62>>

      <with|par-left|<quote|1tab>|4.2.4.<space|2spc>Simple Constraint
      Abduction <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-63>>

      <with|par-left|<quote|2tab>|4.2.4.1.<space|2spc>Abduction for Terms
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-64>>

      <with|par-left|<quote|2tab>|4.2.4.2.<space|2spc>Abduction for Linear
      Arithmetic <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-65>>

      4.3.<space|2spc>Constraint Generalization
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-66>

      <with|par-left|<quote|1tab>|4.3.1.<space|2spc>Algorithm for Combining
      Domains <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-67>>

      <with|par-left|<quote|1tab>|4.3.2.<space|2spc>Linear Arithmetic
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-69>>

      <with|par-left|<quote|1tab>|4.3.3.<space|2spc>Abductive Constraint
      Generalization <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-70>>

      4.4.<space|2spc>Negative Constraints
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-71>

      4.5.<space|2spc>Details of Solving for Predicate Variables
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-72>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|font-shape|<quote|small-caps>|5.<space|2spc><with|font-shape|<quote|small-caps>|InvarGenT>:
      Tests and Limitations> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <pageref|auto-75><vspace|0.5fn>

      5.1.<space|2spc>Benchmarks <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-76>

      5.2.<space|2spc><with|font-shape|<quote|small-caps>|InvarGenT> Failure
      Cases <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-80>

      <with|par-left|<quote|1tab>|5.2.1.<space|2spc>The Need to Expand
      Pattern Variables <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-81>>

      <with|par-left|<quote|1tab>|5.2.2.<space|2spc>Constraints Shared by
      Constructors of a Datatype <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-82>>

      <with|par-left|<quote|1tab>|5.2.3.<space|2spc>Negative Constraints in
      the Sort of Terms <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-83>>

      <with|par-left|<quote|1tab>|5.2.4.<space|2spc>Insufficient Context to
      Infer Postconditions <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-84>>

      <with|par-left|<quote|1tab>|5.2.5.<space|2spc>Insufficient Search
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-85>>

      <with|par-left|<quote|1tab>|5.2.6.<space|2spc>Nested Definitions with
      Tied Postconditions <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-86>>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|font-shape|<quote|small-caps>|6.<space|2spc>Conclusions>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <pageref|auto-87><vspace|0.5fn>

      6.1.<space|2spc>Related Work <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-88>

      6.2.<space|2spc>Future Work <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-89>

      6.3.<space|2spc>Summary <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-90>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|font-shape|<quote|small-caps>|Bibliography>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <pageref|auto-91><vspace|0.5fn>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|font-shape|<quote|small-caps>|Appendix
      A.<space|2spc>Proofs> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <pageref|auto-92><vspace|0.5fn>

      A.1.<space|2spc>The Type System <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-93>

      <with|par-left|<quote|1tab>|A.1.1.<space|2spc>The Logic of Constraints
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-94>>

      <with|par-left|<quote|1tab>|A.1.2.<space|2spc>The GADT Type System
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-95>>

      <with|par-left|<quote|1tab>|A.1.3.<space|2spc>Existential Types
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-96>>

      <with|par-left|<quote|1tab>|A.1.4.<space|2spc>Semantics by Reduction to
      <with|mode|<quote|math>|HMG<around*|(|X|)>>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-97>>

      A.2.<space|2spc>Constraint Abduction
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-98>

      <with|par-left|<quote|1tab>|A.2.1.<space|2spc>Formulating the Joint
      Constraint Abduction Problem <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-99>>

      <with|par-left|<quote|1tab>|A.2.2.<space|2spc>Abduction Algorithm for
      The Combination of Domains <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-100>>

      A.3.<space|2spc>Constraint Generalization
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-101>

      A.4.<space|2spc>Solving for Predicate Variables
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-102>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|font-shape|<quote|small-caps>|Appendix
      B.<space|2spc>Algorithmic Details> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <pageref|auto-103><vspace|0.5fn>

      B.1.<space|2spc>Generating and Normalizing Formulas
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-104>

      <with|par-left|<quote|1tab>|B.1.1.<space|2spc>Normalization
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-105>>

      <with|par-left|<quote|2tab>|B.1.1.1.<space|2spc>Implementation Details
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-106>>

      <with|par-left|<quote|1tab>|B.1.2.<space|2spc>Simplification
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-107>>

      B.2.<space|2spc>Abduction <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-108>

      <with|par-left|<quote|1tab>|B.2.1.<space|2spc>Abduction for Terms with
      Alien Subterms <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-109>>

      <with|par-left|<quote|1tab>|B.2.2.<space|2spc>Joint Constraint
      Abduction <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-110>>

      <with|par-left|<quote|1tab>|B.2.3.<space|2spc>Simple Constraint
      Abduction for Terms <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-111>>

      <with|par-left|<quote|2tab>|B.2.3.1.<space|2spc>Heuristic for Better
      Answers to Invariants <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-112>>

      <with|par-left|<quote|1tab>|B.2.4.<space|2spc>Simple Constraint
      Abduction for Linear Arithmetics <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-113>>

      B.3.<space|2spc>Constraint Generalization
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-114>

      <with|par-left|<quote|1tab>|B.3.1.<space|2spc>Extended Convex Hull
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-115>>

      <with|par-left|<quote|1tab>|B.3.2.<space|2spc>Issues in Inferring
      Postconditions <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-116>>

      <with|par-left|<quote|1tab>|B.3.3.<space|2spc>Abductive Constraint
      Generalization <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-117>>

      B.4.<space|2spc>Incorporating Negative Constraints
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-119>

      B.5.<space|2spc><with|font-shape|<quote|italic>|opti> and
      <with|font-shape|<quote|italic>|subopti>:
      <with|font-shape|<quote|italic>|minimum> and
      <with|font-shape|<quote|italic>|maximum> Relations in
      <with|font-family|<quote|tt>|language|<quote|verbatim>|num>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-120>

      <with|par-left|<quote|1tab>|B.5.1.<space|2spc>Normalization, Validity
      and Implication Checking <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-121>>

      <with|par-left|<quote|1tab>|B.5.2.<space|2spc>Abduction
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-122>>

      <with|par-left|<quote|1tab>|B.5.3.<space|2spc>Constraint Generalization
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-123>>

      B.6.<space|2spc>Solving for Predicate Variables
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-124>

      <with|par-left|<quote|1tab>|B.6.1.<space|2spc>Solving for Predicates in
      Premises <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-125>>

      <with|par-left|<quote|1tab>|B.6.2.<space|2spc>Solving for Existential
      Types Predicates and Main Algorithm
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-126>>

      <with|par-left|<quote|1tab>|B.6.3.<space|2spc>Stages of Iteration
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-127>>

      <with|par-left|<quote|1tab>|B.6.4.<space|2spc>Implementation Details
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-128>>

      B.7.<space|2spc>Generating OCaml Source and Interface Code
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-129>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|font-shape|<quote|small-caps>|Appendix
      C.<space|2spc>Source Code of Examples>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <pageref|auto-130><vspace|0.5fn>

      C.1.<space|2spc>Incompleteness Example for
      <with|font-family|<quote|tt>|language|<quote|verbatim>|OutsideIn>:
      Function <with|font-family|<quote|tt>|language|<quote|verbatim>|rx>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-131>

      C.2.<space|2spc>Pointwise Examples <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-132>

      <with|par-left|<quote|1tab>|C.2.1.<space|2spc>Function
      <with|font-family|<quote|tt>|language|<quote|verbatim>|rotate>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-133>>

      <with|par-left|<quote|1tab>|C.2.2.<space|2spc>Function
      <with|font-family|<quote|tt>|language|<quote|verbatim>|zip2>:
      <with|mode|<quote|math>|N>-way <with|font-family|<quote|tt>|language|<quote|verbatim>|zip_with>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-134>>

      <with|par-left|<quote|1tab>|C.2.3.<space|2spc>Function
      <with|font-family|<quote|tt>|language|<quote|verbatim>|rotl>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-135>>

      <with|par-left|<quote|1tab>|C.2.4.<space|2spc>Function
      <with|font-family|<quote|tt>|language|<quote|verbatim>|ins>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-136>>

      <with|par-left|<quote|1tab>|C.2.5.<space|2spc>Function
      <with|font-family|<quote|tt>|language|<quote|verbatim>|extract>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-137>>

      <with|par-left|<quote|1tab>|C.2.6.<space|2spc>Function
      <with|font-family|<quote|tt>|language|<quote|verbatim>|run_state>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-138>>

      C.3.<space|2spc>Non-Pointwise Examples
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-139>

      <with|par-left|<quote|1tab>|C.3.1.<space|2spc>Function
      <with|font-family|<quote|tt>|language|<quote|verbatim>|joint>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-140>>

      <with|par-left|<quote|1tab>|C.3.2.<space|2spc>Function
      <with|font-family|<quote|tt>|language|<quote|verbatim>|rotr>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-141>>

      <with|par-left|<quote|1tab>|C.3.3.<space|2spc>Function
      <with|font-family|<quote|tt>|language|<quote|verbatim>|delmin>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-142>>

      <with|par-left|<quote|1tab>|C.3.4.<space|2spc>Function
      <with|font-family|<quote|tt>|language|<quote|verbatim>|fd_comp>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-143>>

      <with|par-left|<quote|1tab>|C.3.5.<space|2spc>Function
      <with|font-family|<quote|tt>|language|<quote|verbatim>|zip1>:
      <with|mode|<quote|math>|N>-way <with|font-family|<quote|tt>|language|<quote|verbatim>|zip_with>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-144>>

      <with|par-left|<quote|1tab>|C.3.6.<space|2spc>Function
      <with|font-family|<quote|tt>|language|<quote|verbatim>|leq>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-145>>

      <with|par-left|<quote|1tab>|C.3.7.<space|2spc>Function
      <with|font-family|<quote|tt>|language|<quote|verbatim>|run_state>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-146>>

      C.4.<space|2spc>Run-time Type Representations
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-147>

      <with|par-left|<quote|1tab>|C.4.1.<space|2spc>Function
      <with|font-family|<quote|tt>|language|<quote|verbatim>|eval>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-148>>

      <with|par-left|<quote|1tab>|C.4.2.<space|2spc>Function
      <with|font-family|<quote|tt>|language|<quote|verbatim>|equal>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-149>>

      C.5.<space|2spc>Lists with Length <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-150>

      <with|par-left|<quote|1tab>|C.5.1.<space|2spc>Function
      <with|font-family|<quote|tt>|language|<quote|verbatim>|head>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-151>>

      <with|par-left|<quote|1tab>|C.5.2.<space|2spc>Function
      <with|font-family|<quote|tt>|language|<quote|verbatim>|append>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-152>>

      <with|par-left|<quote|1tab>|C.5.3.<space|2spc>Function
      <with|font-family|<quote|tt>|language|<quote|verbatim>|flatten_pairs>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-153>>

      <with|par-left|<quote|1tab>|C.5.4.<space|2spc>Function
      <with|font-family|<quote|tt>|language|<quote|verbatim>|filter>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-154>>

      <with|par-left|<quote|1tab>|C.5.5.<space|2spc>Function
      <with|font-family|<quote|tt>|language|<quote|verbatim>|zip>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-155>>

      C.6.<space|2spc>Binary Numbers <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-156>

      <with|par-left|<quote|1tab>|C.6.1.<space|2spc>Function
      <with|font-family|<quote|tt>|language|<quote|verbatim>|plus>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-157>>

      <with|par-left|<quote|1tab>|C.6.2.<space|2spc>Function
      <with|font-family|<quote|tt>|language|<quote|verbatim>|increment>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-158>>

      <with|par-left|<quote|1tab>|C.6.3.<space|2spc>Function
      <with|font-family|<quote|tt>|language|<quote|verbatim>|bitwise_or>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-159>>

      C.7.<space|2spc>AVL Trees <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-160>

      C.8.<space|2spc>Arrays and Matrices
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-161>

      <with|par-left|<quote|1tab>|C.8.1.<space|2spc>Program
      <with|font-family|<quote|tt>|language|<quote|verbatim>|dotprod>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-162>>

      <with|par-left|<quote|1tab>|C.8.2.<space|2spc>Program
      <with|font-family|<quote|tt>|language|<quote|verbatim>|bcopy>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-163>>

      <with|par-left|<quote|1tab>|C.8.3.<space|2spc>Program
      <with|font-family|<quote|tt>|language|<quote|verbatim>|bsearch>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-164>>

      <with|par-left|<quote|1tab>|C.8.4.<space|2spc>Function
      <with|font-family|<quote|tt>|language|<quote|verbatim>|bsearch2>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-165>>

      <with|par-left|<quote|1tab>|C.8.5.<space|2spc>Program
      <with|font-family|<quote|tt>|language|<quote|verbatim>|queen>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-166>>

      <with|par-left|<quote|1tab>|C.8.6.<space|2spc>Function
      <with|font-family|<quote|tt>|language|<quote|verbatim>|swap_interval>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-167>>

      <with|par-left|<quote|1tab>|C.8.7.<space|2spc>Program
      <with|font-family|<quote|tt>|language|<quote|verbatim>|isort>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-168>>

      <with|par-left|<quote|1tab>|C.8.8.<space|2spc>Program
      <with|font-family|<quote|tt>|language|<quote|verbatim>|tower>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-169>>

      <with|par-left|<quote|1tab>|C.8.9.<space|2spc>Program
      <with|font-family|<quote|tt>|language|<quote|verbatim>|matmult>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-170>>

      <with|par-left|<quote|1tab>|C.8.10.<space|2spc>Program
      <with|font-family|<quote|tt>|language|<quote|verbatim>|heapsort>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-171>>

      <with|par-left|<quote|1tab>|C.8.11.<space|2spc>Program
      <with|font-family|<quote|tt>|language|<quote|verbatim>|simplex>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-172>>

      <with|par-left|<quote|1tab>|C.8.12.<space|2spc>Program
      <with|font-family|<quote|tt>|language|<quote|verbatim>|gauss>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-173>>

      <with|par-left|<quote|1tab>|C.8.13.<space|2spc>Program
      <with|font-family|<quote|tt>|language|<quote|verbatim>|fft>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-174>>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|font-shape|<quote|small-caps>|Appendix
      D.<space|2spc><with|font-shape|<quote|small-caps>|InvarGenT>: Manual>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <pageref|auto-175><vspace|0.5fn>

      D.1.<space|2spc>Introduction <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-176>

      D.2.<space|2spc>Tutorial <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-177>

      D.3.<space|2spc>Syntax <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-178>

      D.4.<space|2spc>Solver Parameters and CLI
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-179>

      D.5.<space|2spc>Limitations of Current
      <with|font-shape|<quote|small-caps>|InvarGenT> Inference
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-180>
    </associate>
  </collection>
</auxiliary>