# The threshold for affine counterexamples to effective hypercube Nullstellensatz

Up to four nonzero real affine forms on a Boolean cube that have no common zero and whose zero sets jointly cover the cube always admit a partition-of-unity certificate of reduced product degree at most 80, uniformly in the dimension. Combined with Rajagopalan–Saurabh's five-form example, the least number of real affine forms allowing unbounded degree is exactly five.

The proof reduces to an inclusion-minimal zero cover. Its indispensable forms each have a large enough zero set that they depend on only a bounded number of variables. Every relevant variable is shared by at least two of those forms. For four forms this leaves at most one uncontrolled form unless two already give a certificate.

We also determine the exact degree n, not merely a lower bound of n, for the two published counterexample families on 2n variables: five affine forms and three quadratics. The families and their lower-bound method are prior results. The bound of 80 for four is an upper bound, not claimed to be optimal. Only the degrees of the reduced products h_i g_i are bounded, as in the original conjecture; no bound on separate multipliers h_i is asserted.

Run `sh replay.sh | diff -u RESULTS.txt -` with Python 3. The proof uses no computation; the checks replay exact small hyperplane covers and independent rank checks of the published hard separation.
