# Multiple-leak tree realization — partial formalization

This extension is distinct from the completed single-leak theorem family.
The current new certified scope must be read in the source-bound CI receipt;
local compilation is not an independent trust-zero certificate.

## Model and target

A fixed finite labelled bidirected tree has positive internal rates and an
independent nonnegative external loss at every vertex. Input and inventory
observation are collocated at o. The intended complete fibre theorem concerns
N distinct positive target pole rates and positive weights summing to one.
It does not claim automatic positivity of every signed multi-leak competitor.

## First proved Lean block

`MultiLeakSimplex` constructs an explicit equivalence between the standard
nonnegative simplex and all positive normalized diagonal scales h for which
the ACTUAL transformed matrix diag(h) B diag(h)^(-1) has nonnegative column
losses. Its intermediate general matrix theorem explicitly assumes that the
actual residence inverse (-B)^(-1) is strictly positive and B is nonsingular.
`SingleLeakResidence` DISCHARGES those assumptions for every actual positive
single-leak finite tree, even with repeated or hidden modes, by exact inverse
row identities and the already proved positive leak relocation.

For R=(-B)^(-1) and p_i>=0 with sum p_i=1,

    h_j = sum_i (p_i/R_io) R_ij,       h_o=1,
    A = diag(h) B diag(h)^(-1),
    loss_j(A) = p_j/(R_jo h_j).

Both directions of the simplex/scale equivalence are proved. `ResidenceGauge`
proves actual inverse transport, normalized matrix-gauge injectivity, the exact
stationary state equation, loss_j(A)*(-A)^(-1)_(j,o)=p_j, and the equivalence
between a zero loss and a zero simplex coordinate. The boundary faces are kept.

This block is not yet a claim that every multi-leak model belongs to one of
these gauge classes. Exhaustive original-matrix and original-rate reconstruction,
response-only equivalence, the finite disjoint-simplex classification and its
topological statement are separate proof obligations below.

## Remaining intended statements

1. Define the original rate vector with one loss per vertex, construct its
   actual matrix, and prove rate/matrix reconstruction without added assumptions.
2. Prove every physical full-target multi-leak matrix has a unique single-root
   reference and a unique simplex share vector; identify the discrete references
   with the existing recursive pole-allocation type and its exact hook count.
3. Prove the actual parameter/response fibre is homeomorphic, not just set-
   equivalent, to that finite discrete index times the closed simplex.
4. Transfer the statement to actual continuous-input trajectories and characterize
   zero-loss faces and physical steady-state fractions.
5. Formalize the separately proposed total-storage sampling theorem, sharp N-1
   sample count, and sharp residual finite ambiguity. Those remain written
   deductions, not Lean-certified results of this checkpoint.

## Provenance and novelty

Yongxian Zhang (张永贤), School of Computer Science and Engineering, South China
University of Technology; mxymmxym1@gmail.com; ORCID 0009-0000-3864-3536.
No external funding; AI-assisted research. Existing repository and third-party
notices remain in force; original additions retain all rights not otherwise
licensed. No completion Release or new DOI is claimed for this partial extension.

Diagonal rescaling and multi-leak unidentifiability are prior art, including
Meshkat–Sullivant, Identifiable reparametrizations of linear compartment models,
Journal of Symbolic Computation 63 (2014), 46–67, DOI 10.1016/j.jsc.2013.11.002.
The proposed simplex geometry, exact physical loss coordinates and sampling
claims require theorem-level comparison before any historical-priority claim.
