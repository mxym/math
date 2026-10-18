# Actual all-rank Haar principal-minor moments

Status: BUILD_ONLY; independent replay/audit remains separate. This continuation scope does not enlarge any frozen audit.

ColumnProjectionMoments.lean derives exact beta moments of the squared norm of a genuine Haar column projected onto a coordinate s-subspace, from the actual rank-one Haar average.

HaarSubgroupAverage.lean constructs an actual unitary fixing the first coordinate, proves right invariance of the normalized Haar probability by uniqueness, proves genuine double averaging by Fubini, and constructs a unitary aligning any column via equality of actual Gram matrices.

HaarMinorMoments.lean defines haarMinorMoment D s k hsD as the literal normalized Haar integral of |det(U_[s],[s])|^(2k). The internal first-column stabilizer argument proves the actual recursion

M(n+1,s+1,k)=C(s+k,k)/C(n+k,k) * M(n,s,k),

and the exact finite product

M(t+s,s,k)=product_{i=0}^{s-1} C(i+k,k)/C(t+i+k,k).

The construction covers zero rank, degree zero, zero projected first columns, and full rank. No Jacobi law, minor-moment certificate, rectangular Schur dimension, Young decomposition or concentration conclusion is assumed. This is an exact principal-minor moment theorem and is not yet the general-rank actual Haar purity asymptotic or the full general-rank support-dimension theorem.

Remaining obligations: derive the polynomial moment constant; establish the actual determinant/trace overlap inequalities; justify the binomial transform asymptotic with a proved low-tail bound; prove the matching general-rank support upper bound by multiple-pattern straightening/automaton counting or another complete route; connect to target-uniform physical minimax.
