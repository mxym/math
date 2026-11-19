# Optional shorter finite-parameter proof for all exponents (separately frozen)

Use the block formula (1) of PROOF.md with N the operator norm, i.e. the p-th power of the norm candidate at X(A,B) is λ_max(|A|^p+|B|^p)/2. We show the value at the midpoint of two blocks is strictly larger than at **both** endpoints.

For 1≤p<2, take s=2^(−2/(2−p)), c=sqrt(1−s²), e=(0,1) and P=ee*. As in the main proof, set A_1=(c,s)(c,s)^T, A_2=−(c,−s)(c,−s)^T, with columns interpreted as vectors. Choose B=2^(1/p)P. Both endpoint top eigenvalues before the normalization 1/2 are (3+sqrt(1+8s²))/2 ≤ 2+2s² (use sqrt(1+x)≤1+x/2). At the midpoint the top eigenvalue is exactly 2+(cs)^p. Here s≤1/4, c^p≥c²≥15/16, and s^(p−2)=4. Thus (cs)^p/s²≥15/4>2, giving the strict midpoint failure.

For 2<p<∞, take T=2^((p+2)/(p−2))>1, B=TP, A_1=diag(T−1/T,0), and A_2=[[0,1],[1,0]]. The endpoint top eigenvalues are T^p and T^p+1 respectively. The first follows from (T−1/T)^p<T^p, and the second from |A_2|=I. The midpoint M=(A_1+A_2)/2 has eigenpair T/2,(T,1)/sqrt(T²+1). Hence 
         
     e*|M|^p e ≥ (T/2)^p/(T²+1) = 4T²/(T²+1) > 2.

The midpoint top eigenvalue is at least e*(|M|^p+|B|^p)e>T^p+2, strictly larger than both endpoints. The p=2 proof and explicit p=1 integer example in PROOF.md are unchanged.

These two direct calculations prove all negative cases with finite parameters and no operator-convexity theorem, eigenvalue perturbation, or passage to a limit.
