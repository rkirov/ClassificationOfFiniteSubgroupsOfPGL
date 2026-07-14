# Classification of finite subgroups of $\textrm{PGL}_2(\bar{\mathbb{F}}_p)$

[![Comparator verification](../../actions/workflows/verify.yml/badge.svg)](../../actions/workflows/verify.yml)

**Status: the formalization is complete and sorry-free.** The three final theorems
(`dicksons_classification_theorem_class_I`, `dicksons_classification_theorem_class_II`,
`FLT_classification_fin_subgroups_of_PGL2_over_AlgClosure_ZMod`) are machine-verified with
`#print axioms` = `[propext, Classical.choice, Quot.sound]` — no `sorryAx`, no custom axioms.
Divergences from Butler's exposition are recorded in [`DIVERGENCES.md`](DIVERGENCES.md).

## ⚠ Disclaimer — AI-produced, unreviewed by a mathematician

The endgame of this formalization (Chapter 7: the six case proofs, the recognition lemmas, the
Todd–Coxeter presented-group bounds, and the final theorems) was produced by **Claude**
(Anthropic's LLM) across many sessions with light human scoping/steering, on top of the
human-authored blueprint and earlier chapters. The one hard guarantee is **Lean's kernel**.
Statement-level trust is addressed by the independent-verification setup below.

## Independent verification (`comparator/`, `challenge.lean` pattern)

You do **not** need to read the ~20k-line development to check *what* was proven:

- [`comparator/Challenge.lean`](comparator/Challenge.lean) — the **independently auditable
  statements** of the three headline theorems: the FLT-facing `PGL₂` classification
  (`dickson_classification_PGL2`) and Dickson's two seminal `SL₂` theorems — Class I, the
  binary-polyhedral list (`dickson_classification_SL2_coprime`: cyclic, dicyclic, `SL(2,𝔽₃)`,
  binary octahedral `2O`, `SL(2,𝔽₅)`), and Class II, the modular case
  (`dickson_classification_SL2_dvd`: Borel, `SL(2,𝔽_{p^k})`, and the twisted index-2 extension).
  The file imports only Mathlib, defines everything it needs explicitly (the `PGL2`/`PSL2`
  quotients, the `2O` presentation `⟨x, y | x⁴ = y³ = (xy)²⟩` from first principles, the diagonal
  twist matrix), spells out every disjunct in plain Mathlib vocabulary, and ends each theorem in
  `sorry`. **Read this file** — it is the whole trust surface. (The `SL₂` statements are fully
  general — no `-1 ∈ G` normalization: any finite subgroup, via the `G·⟨−1⟩` lift.)
- [`comparator/Solution.lean`](comparator/Solution.lean) — restates the identical statement
  and discharges it from this repository's main theorem (one small definitional bridge).
- [`verify.sh`](verify.sh) — runs the official
  [`leanprover/comparator`](https://github.com/leanprover/comparator) against the pair:
  statement match between Challenge and Solution, permitted-axiom check
  (`propext`, `Classical.choice`, `Quot.sound` only), and an **independent kernel replay**
  of the entire proof term via `lean4export`, in a sandbox. The library's proofs are not
  trusted — they are re-checked.

Trust required: the Lean kernel, Mathlib, `comparator/Challenge.lean` (read it), and the
comparator tool itself.

## Content of this project

This project contains the $\LaTeX$ blueprint and the Lean formalization of the classification of finite subgroups of $\textrm{PGL}_2(F)$.

Which states:

- If $H$ is finite subgroup of $\textrm{PGL}\_2(\mathbb{C})$ then $H$ is isomorphic to one of the following groups: the cyclic group $C_n$ of order $n$ ($n \in Z_{>0}$), the dihedral group $D_{2n}$ of order $2n$ ($n \in Z_{>1}$), $A_4$, $S_4$ or $A_5$.
- If $H$ is a finite subgroup of $\textrm{PGL}_2(\bar{F}_p)$ then one of the following holds:
  1. $H$ is conjugate to a subgroup of the upper triangular matrices;
  2. $H$ is conjugate to $\textrm{PGL}\_2 (F_{\ell^r})$ and $\textrm{PSL}\_2 (F\_{\ell^r})$ for some $r \in Z_{>0}$;
  3. $H$ is isomorphic to $A_4$, $S_4$, $A_5$ or the dihedral group $D_{2r}$ of order $2r$ for some $r \in Z_{>1}$ not divisible by $\ell$

Where $\ell$ is assumed to be an odd prime.

## The big picture

This project is a contribution towards the formalization of Fermat's Last Theorem (see https://github.com/ImperialCollegeLondon/FLT), the result formalized covers Theorem 2.47 in [FermatLastTheorem](https://www.math.mcgill.ca/darmon/pub/Articles/Expository/05.DDT/paper.pdf)

## Acknowledgements

I thank my supervisor Prof. David Jordan for his invaluable support and guidance throughout the project, 

I would also like to thank Christopher Butler for providing the $\LaTeX$ code so I could easily set up the blueprint.

I would also like to thank Prof. Kevin Buzzard for his support and patience.

Finally, I would like to thank the many members of the Lean Zulip community who have provided insightful ideas and comments that have helped me progress much faster than otherwise.

## Contributing

Contributions are welcome! If you would like to contribute, I recommend looking through the reference below and contacting me via zulip so I can find you a suitable task. 
At the time of writing, I am formalising lemma 2.3 iv) b); and hope to be soon formalising the inequality on page 35, which will lead to the case split on the classification of the arbitrary finite group.

## Source reference

`CB` : [ChristopherButlerExpositionOfDicksonsClassificationTheorem](https://lup.lub.lu.se/student-papers/record/8998907/file/8998908.pdf)


