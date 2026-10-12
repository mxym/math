Comparison of the Assouad two compact obstruction with earlier work
7 October 2026

The precise contribution of the note is the simultaneous conclusion: in every infinite-dimensional real Banach space, a countable compact subset with zero upper box dimension, Assouad dimension exactly two, a universally bounded doubling constant, and no bi-Lipschitz embedding into any finite-dimensional real normed space. The comparison below distinguishes that conjunction from individual properties already available. It is a bounded literature comparison, not a publication-priority or optimality claim.

Direct overlap with the source construction

The OpenAI preprint cited by the note already gives a doubling Hilbert subset with no finite-dimensional Euclidean bi-Lipschitz embedding, and in Section 7 transfers finite witnesses to every infinite-dimensional real Banach space by Dvoretzky's theorem. Its compact assembly is a countable union of finite clusters and one limit point. Thus compactness, countability, Hausdorff dimension zero, the Banach-space quantifier, and a universal doubling bound are inherited. The derivative and crossing mechanism is also inherited. The present note explicitly credits these dependencies.

The added estimates are the superlacunary schedule's exact Assouad dimension and the sparse placement's zero upper box dimension, maintained simultaneously through finite witnesses and transfer. Zero upper box dimension is a refinement of the finite-cluster placement, rather than a new nonembedding mechanism. The refined local covering estimate, followed by the preservation argument for the compact assembly, is the main additional dimensional content.

The original geometric schedule is not already exact two

For the source's full sheet space S with rho_j = 1000^(-j), an elementary packing gives

  dim_A S >= 2 + log(2)/log(1000) = 2.100343...

At scale rho_m, choose rho_m-separated planar grid points in a fixed unit square, with their y-coordinates avoiding all level-1-through-m strip boundaries. Above each point, independently choose zero or its permitted horizontal-strip displacement at each of these m levels. There are at least c rho_m^(-2) 2^m resulting points, all in a fixed-radius ball, with pairwise separation at least rho_m. A radius-rho_m/3 ball covers at most one. Comparing with C(R/r)^s and letting m grow proves the displayed lower bound.

This concerns the full source S. It does not determine the exact dimension of an arbitrary finite-witness compact assembly from the source: a chosen collection of witnesses need not retain these particular packings. It does show that replacing geometric scales by superlacunary scales removes a real dimensional excess, rather than merely proving an already-valid exact-two assertion about the same S. [1]

Earlier embedding and nonembedding results

Lafforgue and Naor's Theorem 1.1 gives doubling subsets of L_p for p>2 with no bi-Lipschitz embedding into any finite-dimensional Euclidean space. Theorem 1.2 even rules out certain infinite-dimensional L_q targets, q<p. Their paper records the contemporaneous independent construction of Bartal, Gottlieb and Neiman. These are genuine qualitative predecessors, but the ambient restriction p>2 does not give the Hilbert case or the every-Banach-space statement. Stronger target obstructions for some ambient spaces are not equivalent to the present simultaneous dimensional conclusion. [2]

Schioppa's 2017 preprint announced the Hilbert obstruction, but its arXiv record explicitly marks it withdrawn because of a possible issue with the duality argument. It should be described as a withdrawn announcement, not cited as an established equivalent theorem. [3]

A January 2025 primary paper of Movahedi-Lankarani and Wells still describes the doubling-Hilbert question as open and proves positive embedding criteria under additional hypotheses. That is useful historical corroboration, not evidence that no later or unindexed exact-dimensional construction exists. This search did not locate an established primary result matching or strengthening the full conjunction under comparison. No universal absence claim follows from that search outcome. [4]

The genuine lower barrier is one, not a proved optimum of two

If a metric space has Assouad dimension strictly less than one, it is uniformly disconnected and bi-Lipschitz equivalent to an ultrametric space of the same Assouad dimension. Luukkainen and Movahedi-Lankarani's Theorem 3.8 embeds that ultrametric into R. Thus no obstruction of the present type can have Assouad dimension below one. The endpoint one and the interval from one to two are not settled by this reasoning; it does not prove that two is optimal. The standard chain of implications is also recorded explicitly in the proof of Corollary 1.3 of Honeycutt, Vellis and Zimmerman. [5,6]

Metrics and dimensions must be kept separate

Assouad's embedding theorem and Naor-Neiman's dimension-independent refinement apply to a snowflake distance d^alpha, 0<alpha<1. They do not give an embedding of the original distance d with uniform finite distortion as alpha tends to one. Therefore they do not contradict the obstruction. [7]

Upper box dimension controls global small-scale covers; Assouad dimension requires a uniform estimate over all pairs of local scales. Quasi-Assouad dimension and the Assouad spectrum restrict how those scales are compared. Indeed, zero upper box dimension forces every fixed-parameter Assouad spectrum here to be zero, and a direct covering argument also gives quasi-Assouad dimension zero, while the full Assouad dimension is two. The spectrum bound of Fraser and Yu and the distinction explained by Fraser, Hare, Hare, Troscheit and Yu make this separation explicit. These zero-spectrum consequences are automatic dimensional consequences, not further nonembedding mechanisms. [8,9]

References

[1] OpenAI, A doubling Hilbert subset with no finite-dimensional bi-Lipschitz embedding, 25 September 2026, pinned source commit adc7f1241b42e322a6451854ab7e4b4c146bf78a, Sections 2-7.
https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-doubling-Hilbert-subset-with-no-finite-dimensional-bi-Lipschitz-embedding-September-25-2026/build/main.tex

[2] V. Lafforgue and A. Naor, A doubling subset of L_p for p>2 that is inherently infinite dimensional, Theorems 1.1-1.3 and the paragraph after Theorem 1.1.
https://web.math.princeton.edu/~naor/homepage%20files/Lp-doubling.pdf

[3] A. Schioppa, An example of a doubling "inherently" infinite-dimensional subset of l_2, arXiv:1703.10265; version 2 withdrawn 22 April 2017.
https://arxiv.org/abs/1703.10265

[4] H. Movahedi-Lankarani and R. Wells, Bi-Lipschitz embeddings revisited, arXiv:2501.07648v1, discussion after Theorem 4.3 and Proposition 7.3.
https://arxiv.org/html/2501.07648v1

[5] J. Luukkainen and H. Movahedi-Lankarani, Minimal bi-Lipschitz embedding dimension of ultrametric spaces, Fundamenta Mathematicae 144 (1994), 181-193, Theorem 3.8.
https://eudml.org/doc/212022
https://matwbn.icm.edu.pl/ksiazki/fm/fm144/fm14426.pdf

[6] J. Honeycutt, V. Vellis and S. Zimmerman, Bi-Lipschitz arcs in metric spaces with controlled geometry, Revista Matematica Iberoamericana 40 (2024), 1887-1916, proof of Corollary 1.3, pp. 1889-1890; references to David-Semmes, Lemma 15.2 and Proposition 15.7.
https://ems.press/content/serial-article-files/48442?nt=1
https://doi.org/10.4171/RMI/1484

[7] A. Naor and O. Neiman, Assouad's theorem with dimension independent of the snowflaking, arXiv:1012.2307.
https://arxiv.org/abs/1012.2307

[8] J. M. Fraser and H. Yu, New dimension spectra: finer information on scaling and homogeneity, Proposition 3.1.
https://arxiv.org/abs/1610.02334
https://research-repository.st-andrews.ac.uk/bitstream/handle/10023/17146/AssouadSpectra.pdf?sequence=1

[9] J. M. Fraser, K. E. Hare, K. G. Hare, S. Troscheit and H. Yu, The Assouad spectrum and the quasi-Assouad dimension: a tale of two spectra, Annales Academiae Scientiarum Fennicae Mathematica 44 (2019), 379-387.
https://www.acadsci.fi/mathematica/Vol44/vol44pp0379-0387.pdf
