# FStar-PHOAS

This is a reimplementation of Adam Chlipala's Parametric Higher Order Abstract Syntax in F*. The original paper can be found at http://adam.chlipala.net/papers/PhoasICFP08/PhoasICFP08.pdf.

Some reflections on the project.

- As the project went on, I got substantially better at understanding the state
  of the SMT solver and using tactics to guide it. I did the DApp case of the
  correctness lemma last and it is cleaner compared to the DLam case which
  in turn is much cleaner than LetTermCorrect. If I revisit this project I would
  likely rewrite LetTermCorrect just for aesthetic reasons. The chain of
  assertions there can almost certainly be replaced by one assertion with
  appropriate tactics.

- F* not unfolding match statements forced the inclusion of various unwrapping
  functions to be able to apply functions resulting from match statements.
  Not a significant bother, but somewhat inelegant.

- The SMT solver sometimes had to have its hand held through normalizing
  terms as F* is not strongly normalizing like Coq for instance. The best
  example is the DLam case of the correctness_lemma which, because the delta
  norm step does not expand terms inside recursive functions, requires seven(!)
  separate names to be named under the delta_only norm_step.

- That one painful normalization example aside, the SMT solver did avoid the
  need for any tedious cleanup once the core of the proof was done.

- Superficially, the lack of functional extensionality in F* would appear to
  present a significant obstruction to implementing PHOAS. In fact, with
  judicious application of the on_domain function from the
  FunctionalExtensionality module the problems are largely navigated though it
  did necessitate an extensionality lemma for denote_cpstyp.

- The DApp case of correctness_lemma required the concrete map in the Arrow case
  of denote_typ_equiv to construce the candidate required for correctness_lemma.
  This led to a redesign of the whole CPSifyCorrect module to take a more
  constructive bent and largely eliminate squashed types. Potentially, one could
  have worked non-constructively by unsquashing inside tactic assertions
  however this seemed less clear to me and constructive proofs are more
  appealing to my aesthetic sensibilities.

- I am not entirely sure why term_translate0 required so many type annotations.

- My proofs are nowhere near as slick as Chlipala's. This is a combination of
  his *much* greater skill with tactics as well as Coq's normalization behavior
  being a significant asset for these sorts of problems.

- The constructive version of correctness_lemma took significantly longer to
  verify than the non-constructive version. Looking at the proof state, the
  hypotheses being taken as parameters appeared to add significantly more
  binders especially in the DApp case.