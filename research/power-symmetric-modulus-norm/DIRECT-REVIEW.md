# Independent check of the direct finite witnesses

PASS on the frozen DIRECT.md SHA 897a7af517b834c09760c352b8c1024c9b07ac32ff89fe70c9429b868c12afc3. The exact counterexamples replace, rather than depend on, any large rank-one-isolation limit. Internal AI review only.

For 1≤p<2, s=2^(−2/(2−p)) implies s^(p−2)=4 and s≤1/4. Since 0<c≤1, c^p≥c²=1−s²≥15/16. Each endpoint's top eigenvalue in the pre-root block is (3+sqrt(1+8s²))/2 by trace 3 and determinant 2(1−s²); applying sqrt(1+x)≤1+x/2 gives at most 2+2s². At the midpoint it is 2+(cs)^p≥2+(15/4)s²>2+2s². Applying a positive pth root preserves strict order, and the two endpoint values coincide.

For p>2, T=2^((p+2)/(p−2)) gives T^(p−2)=2^(p+2). The first endpoint has largest pre-root eigenvalue T^p because T>T−1/T, and the second has T^p+1. The midpoint Rayleigh quotient in the second coordinate exceeds T^p+2: the positive eigenspace of eigenvalue T/2 contributes at least (T/2)^p/(T²+1)=4T²/(T²+1)>2 to that coordinate of the pth absolute power. The rest is nonnegative. Thus even the larger endpoint is strictly beaten after the pth root and scaling. These are actual finite matrices for every fixed real parameter; no claim on a uniform bound as p tends to 2.
