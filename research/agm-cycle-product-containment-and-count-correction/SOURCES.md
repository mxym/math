# Sources and scope audit

* **[LM] Juan Jesús León and Vicente Muñoz,** *On some non-linear
  recurrences over finite fields linked to isogeny graphs*,
  [IACR ePrint 2025/608](https://eprint.iacr.org/2025/608),
  [source PDF](https://eprint.iacr.org/2025/608.pdf) and
  [readable archived copy](https://opencryptology.org/2025/608/versions/20260428T172000Z.pdf).
  Section 2 restricts p to 7 mod 12. Section 10, pp. 22–26,
  distinguishes simple non-backtracking j-cycles, excludes self-loops,
  and in Theorem 10.1 excludes double edges when associating the
  periodic v-lift. Equations (31) and (32) fix the recurrence and the
  Legendre j mapping. The boxed Conjecture 10.2, equation (33), is
  the one-sided product vanishing verified here. The nearby
  root-realization and numerical count are separate prose assertions;
  see the precise counterexamples in PROOF.md §5. Proposition 10.3
  has an already-known reciprocal-product symmetry for reversed cycles.
* **June Kayath, Connor Lane, Ben Neifeld, Tianyu Ni, and Hui Xue,**
  *AGM aquariums and elliptic curves over arbitrary finite fields*,
  [arXiv:2410.17969](https://arxiv.org/abs/2410.17969). Lemma 2.8(2)
  and (3) gives the AGM 2-isogeny on Legendre curves and its dual
  kernel; Lemma 2.3 describes 4-torsion x-coordinates. Their
  Legendre-coordinate formula chooses the negative of the y-sign in
  PROOF.md (3) after the natural scalings. The 2-isogeny and basic
  4-torsion parametrization are classical. Their Frobenius-trace
  conditions (e.g. Lemma 6.2) differ from the trace of the signed
  AGM monodromy endomorphism here.
* **John E. Cremona and Thotsaphon Thongjunthug,** *The complex AGM,
  periods of elliptic curves over C and complex elliptic logarithms*,
  [J. Number Theory 133 (2013)](https://doi.org/10.1016/j.jnt.2013.02.002),
  [arXiv:1011.0914](https://arxiv.org/abs/1011.0914), especially
  Proposition 9 and Theorem 10. Their complex period-lattice framework
  already tracks cyclic order-four subgroups up to sign. We work
  directly with a signed generator, not via a period-lattice transfer
  to odd characteristic.
* **Christophe Ritzenthaler,** [*AGM for point counting* notes](https://ritzenth.pages.math.cnrs.fr/web/cours/agm.pdf),
  §§2.1–2.4, especially Proposition 2.1 (Satoh). These close analogues
  recover a Frobenius trace from a differential multiplier of its
  ordinary characteristic-two canonical lift; the notes also use
  order-four torsion to fix a Frobenius sign in their setting.
  Here the endomorphism is instead the normalized product of an
  arbitrary nonsingular AGM cycle, directly in characteristic not two.
* **Joseph H. Silverman,** *The Arithmetic of Elliptic Curves*, 2nd ed.
  (2009), [Springer](https://doi.org/10.1007/978-0-387-09494-6),
  III.4 for origin-preserving maps, III.8.6 for the Tate module degree
  formula, and V.4.1 for the Legendre supersingularity criterion.
  These are the standard elliptic-curve facts used in the proof.

Focused duplicate searches on 2026-11-27 for the exact title, Conjecture
10.2, v-cycle signed product, AGM monodromy trace and fixed 4-torsion
did not find a solution of the boxed statement or the N=3 correction
in the sources consulted. The classical ingredients and their adjacent
literature are explicitly credited; no claim is made that AGM isogenies,
cyclic kernels, or Tate module trace bounds are new. The analysis is a
pure mathematical result, with no algorithmic isogeny-path or security
implication claimed.
