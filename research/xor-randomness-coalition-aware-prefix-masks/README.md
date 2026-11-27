# Randomness for perfect private XOR

For \(n\) input holders and any \(1\le t<n\), one binary XOR can
be computed with perfect correctness and perfect static
semi-honest privacy using \(O(t^2+t\log n)\) local random bits.
Exactly the first \(t\) parties can be the only random sources.
The construction uses a balanced two-block tree and logarithmically
many rounds, with fixed public binary matrices chosen by an
existence proof. A path version improves the finite constant.

For \(2\le t<n\), combining the upper bound with established
lower bounds gives \(\Theta(t^2+t\log(n/t))\) randomness in the
**additive-message-masking** class of Gál–Rosén. In the unrestricted
protocol model it matches the \(\Omega(t^2)\) lower bound when
\(t\ge\log_2 n\); intermediate parameters are not all settled.

A separate polynomial-time explicit construction uses the fact
that every subtree in ordered traversal is a contiguous interval,
hence needs only two prefix masks. It gives an
\(O(t^2\log n)\) bound without the extra depth factor from
the layerwise generator in Goyal–Ishai–Song. This is not a
uniformly explicit \(O(t^2\log(n/t))\) result.

All statements concern a single XOR bit in the private-channel
mathematical model. No pre-shared randomness, trusted dealer, active
corruption, or deployment guarantee is assumed. Run `sh replay.sh`
with Python 3; the checks compare full coalition views and also
verify the tree interval and rank arguments.
