# Exact alternating quantum max-flow for the three-dimensional twelve-cycle

**Yongxian Zhang.** AI-assisted proof development and internal checks; no external peer review claimed.

The complex periodic twelve-cycle, using the same site tensor on all twelve sites and physical and bond dimensions both three, has maximum alternating flattening rank **728**. This gives one dimension of the twelve-cycle, not a general theorem for that length.

The upper bound \(3^6-1\) follows from [Gesmundo–Landsberg–Walter, Theorem I.3](https://arxiv.org/html/1801.09106#S1.SS4). For attainment put \(A_i=e_i\,K_{i,:}\), where
\[
 K=\begin{pmatrix}1&1&1\\1&2&3\\1&4&5\end{pmatrix}.
\]
The trace at the interleaving of words \(u,v\in\{0,1,2\}^6\) is \(\prod_{j=0}^5 K_{u_j,v_j}K_{v_j,u_{j+1}}\), with cyclic indices. Index both word bases in increasing base-three order, with position 0 least significant, and omit index 1 from both. The resulting \(728\times728\) integral minor has determinant \(727\bmod1009\), using exact finite-field elimination with the first available nonzero pivot. Its first eight pivots are \(1,4,1,1007,16,1007,494,294\); its last eight are \(816,176,583,463,545,383,331,706\). The accompanying Node.js script constructs and checks the full minor. Its nonzero modular determinant proves that the same minor over \(\mathbb C\) is nonsingular.
