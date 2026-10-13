# Lacunary common-measure energy and uniform band compactness

## Exact theorem and remaining scope

Fix a finite descending list of positive real labels d with 2*e<d for each earlier d and later e. Let nonnegative energies e(d) be bounded above by B>=0. For any probability measure mu on the nonnegative reals, with product measure mu x mu, Lean proves

    2 sum_d sqrt(e(d) (mu x mu){x+y=d}/2)
      <= sqrt(sum_d e(d)) + sqrt(2B).

The measure may have infinitely many atoms and a nonatomic part. All levels use the SAME measure. The theorem neither assumes a favorable atomic graph nor chooses a separate extremizing measure at each level.

For probability measures on [0,1], every epsilon>0 admits ONE eta>0 such that the same bound plus epsilon holds for ALL these probability measures and ALL bands |x+y-d|<=t with t<=eta. The number of levels, labels and energies are fixed before eta is chosen. This is the actual uniform compactness statement, not merely convergence along a supplied measure sequence.

These theorems replace the common-measure/forest-operator step of MULTISCALE.md (T7-T9) with a direct measure argument. They do NOT yet prove the preceding finite graph localization, the final graph spectral limit, the physical nested-state construction, the coefficient eight, the stronger optimal-hierarchy formula, entropy minima or asymptotic rigidity.

## Mathematical dependency chain

1. LacunaryColor constructs a Borel binary partition recursively. For the leading label d, retain the smaller-level color when x<=d/2, and reverse the color at the reflected coordinate d-x when x>d/2. If x,y>=0 are distinct and x+y is a label, they have opposite colors. Smaller-label endpoints are below d/2; the leading-label endpoints are reflections. Positivity and distinctness of labels are established.
2. LacunaryMeasure bounds the union of ALL off-diagonal interaction lines by the two cross rectangles of this one partition. Their product-measure mass is at most 2*a*(1-a)<=1/2. Distinct lines are disjoint. The diagonal part of line d is exactly the point (d/2,d/2), of mass mu{d/2}^2. The distinct loop-atom masses sum to at most one. No countable atomic enumeration or infinite-dimensional adjacency operator is needed.
3. LacunaryEnergy and LacunaryProbability apply exact square-root splitting and finite Cauchy--Schwarz. Off-diagonal half-masses have sum at most 1/4. Loop contributions are bounded by sqrt(B/2) times the total loop mass. This proves the displayed inequality, including empty lists and zero energies.
4. MovingScaleBand encodes a varying band width as a Dirac mark. The set {((x,y),t): |x+y-d|<=t} is fixed and closed. Continuity of probability-measure products and Dirac measures, followed by the actual closed-set Portmanteau theorem, gives the moving-strip weak upper bound. There is no unsupported application of a fixed-set theorem to varying sets.
5. LacunaryWeakLimit keeps one common convergent measure sequence for every level. Finite conjunction and continuity of a positive perturbation of the square-root objective give the eventual summed bound. LacunaryUniformBand uses compactness of probability measures on [0,1] to rule out a sequence of violating measures at widths 1/(n+1). A single convergent subsequence and the vanishing marked width give a contradiction.

## Negative controls and verification

The rational scales 3/5,1/2,2/5 admit a triangle on 7/20,1/4,3/20; Lean proves no binary coloring separates those three edges. This rejects the unsupported removal of the factor-two separation in the coloring argument (not a claim that every relaxed energy bound is false). The actual probability measure delta_1 gives full mass to line x+y=2, and disproves the energy bound with the loop term omitted. Empty-scale behavior is also tested.

Fresh local build, original trust-zero replay, and all retained physical controls passed. Independent run 38337062170 verified exact source 66f32a995d793bdbfe233e68ef4f851eaf3ea90a: 3,124 Lake tasks, 50,471 declarations, 326 audit roots, 121 pinned inputs and only propext, Classical.choice, Quot.sound. Twenty-one corrupted theorem proofs were rejected with their exact types preserved, including the final uniform band theorem, arbitrary-measure energy theorem and moving-band theorem. Downloaded source files, stage logs and hashes matched. Evidence is in verification/ci-66f32a99/. Imported declarations are included in the count; these are not 50,471 new theorems.

Mathlib supplies the proved measure product, weak topology, Portmanteau and probability compactness dependencies. Their actual proof closure is replayed; none is introduced as a custom axiom. Standard finite graph localization and the new empirical/log-coordinate bridges are being developed separately and are not certified by this checkpoint. No preprint, Release or original quantum definition is changed.
