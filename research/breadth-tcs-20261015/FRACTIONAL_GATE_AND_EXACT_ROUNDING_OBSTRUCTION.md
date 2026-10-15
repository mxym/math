# The fractional gate and its exact rounding limitation

15 October 2026, Asia/Shanghai. Yongxian Zhang (张永贤), South China
University of Technology. No external funding. OpenAI AI assistants assisted.
Original material all rights reserved; third-party rights retained.

**Status:** elementary reformulation and route controls, not a proof or
refutation of the full strong size-VC compression conjecture. No new major
result, novelty priority, independent review or Lean proof is asserted.

## 1. A precise fractional relaxation of the full finite decoder problem

For a finite total class C on n coordinates and a proposed size k, let
K=K(C) contain EVERY realizable labeled partial sample. Let M contain
every realizable T of size at most k. For each T, let H(T) be ALL total
Boolean hypotheses extending T, including those outside C. Introduce
nonnegative numbers p(T,h) satisfying

    sum_{h in H(T)} p(T,h) <= 1                   for every T in M,
    sum_{T subset S} sum_{h extending S} p(T,h) >= 1   for every S in K.
                                                        (FG-1)

There is no properness restriction, extra bit or message-domain side
channel. Restricting the p values to 0 and 1 is exactly the original finite
compression feasibility question at size k: one may choose at most one
decoder h for each T, and every S has at least one successful message.
Unused decoder messages may be completed arbitrarily. Missing mass in
the fractional version may likewise be filled on any h extending T,
so using equality rather than the first inequality does not affect
fractional feasibility.

This relaxation only asks that the EXPECTED NUMBER of successful messages
is at least one, if the p values are interpreted as decoder marginals.
It does not ensure probability one of at least one successful message for
each S. It is not itself a zero-error randomized compression scheme and
does not prove SC0.

## 2. The exact weighted dual condition

For nonnegative weights w(S) on K define

    W_T(w) = max_{h in H(T)}
                sum_{S in K: T subset S subset graph(h)} w(S).

Then (FG-1) is feasible if and only if, for EVERY nonnegative w,

    sum_{S in K} w(S) <= sum_{T in M} W_T(w).       (FG-2)

Necessity follows by multiplying the coverage inequalities by w(S),
summing, and bounding each message group's weighted contribution by its
largest W_T(w), since its total mass is at most one. For sufficiency,
the achievable coverage vectors from the first set of constraints form
a compact convex set. If none dominates the all-one vector, strict
finite-dimensional convex separation from the upper orthant supplies
a nonnegative separating w. Maximizing the weighted coverage over p
separates independently over each T and gives exactly sum_T W_T(w),
contradicting (FG-2). Equivalently this is finite linear-program duality.

The condition must hold for arbitrary weights on the entire partial-sample
poset. Checking only weights on complete rows returns a matching condition
and leaves the original missing partial-sample gate. Choosing uniform
conditional proper-decoder marginals is one particular attempted solution;
the private-copy example in the continued notes proves that those marginals
can fail (FG-1) even at VC two.

There is currently no proof in this packet that (FG-2) holds for every
total VC-d class at k=d. Nor is a legal weighted dual violation at that
parameter exhibited. Either would be a substantive statement requiring
its full domain and assumptions to be proved, not inferred from listed
finite experiments.

## 3. The actual relaxation need not have integral vertices, even at k=d=1

Let X={0,1,2} and C be its three singleton concepts, so VC(C)=1.
The realizable samples are exactly those with at most one positive label,
except that the all-negative sample on all three coordinates is absent.
In particular the three all-negative pairs S_{01},S_{12},S_{02} occur.

Consider the following face of the FULL polytope (FG-1). Fix the empty
decoder to the all-one hypothesis. For each positive singleton message
(i,1), fix its decoder to the i-th singleton concept. For each negative
singleton message T_i=(i,0), permit only the two total hypotheses

    g_i = the all-zero hypothesis,
    b_i = the hypothesis zero at i and one at the other two points.

Set p(T_i,g_i)=x_i and p(T_i,b_i)=1-x_i, with 0<=x_i<=1. All other
decoder variables are set to zero. These are genuine faces of (FG-1):
each prohibited p is fixed at its nonnegative lower bound, and a fixed
message output has its group capacity saturated at one.

Every sample with a positive literal is already covered with weight one
by its positive singleton decoder. Single negative literals are covered
with weight one by their own message, under BOTH g_i and b_i. The empty
sample is covered as well. For a negative pair S_{ij}, the only eligible
nonempty messages are T_i,T_j. The empty decoder fails, and b_i,b_j fail
on the other coordinate. Thus its coverage inequality is exactly

    x_0+x_1>=1,  x_1+x_2>=1,  x_0+x_2>=1.         (FG-3)

There are no further uncovered samples in K. The point x_0=x_1=x_2=1/2
is a vertex: all three inequalities (FG-3) are equalities and their
3-by-3 coefficient matrix has determinant two, so their unique common
solution is that point. The listed coordinate restrictions define a face
of the full polytope, so a vertex of this face is also a vertex of the
full polytope. It is fractional. The restricted objective x_0+x_1+x_2
has fractional minimum 3/2 and integer minimum two.

Consequently an assertion that the natural full decoder relaxation is
always integral merely from VC=k would be false, already at VC one.
This is not an infeasibility result. The same face has integer feasible
points, for example (1,1,0), and C has a general size-one compression
scheme. It also does not disprove a carefully chosen existence-preserving
rounding theorem. It rules out automatic polytope integrality and arbitrary
rounding as an unproved bridge from fractional solutions to SC0.

## 4. A sharper lower-size check for the Warmuth class

At k=1 below VC(C)=2, the ten-row Warmuth class from the single-shift note
is infeasible even for (FG-1). Here is a short exact check that also keeps
this lower-size route separate from SC0.

Every four-coordinate projection has nine distinct patterns and exactly
nine eligible size-one messages. Summing their nine coverage inequalities
therefore saturates every available message's unit capacity, and assigns
no mass to hypotheses with a forbidden pattern on that projection. The
forbidden-triple argument in the single-shift note implies that every
nonzero p(T,h) is supported on h in C. Thus each of the eleven message
groups has total mass one on C.

Write w_c for the total mass decoding to a fixed concept c over all its
eligible messages, so w_c>=1 by the complete-row constraint, and put
s_c=w_c-1>=0. Since the eleven groups have total mass eleven while C
has ten concepts,

    sum_{c in C} s_c = 1.                         (FG-4)

Each c has exactly one one-inclusion neighbor, in coordinate j(c), as
listed in the single-shift note. For any i!=j(c), the projection deleting
i uniquely identifies c among the rows of C. Its saturated coverage
inequality contains exactly those messages of c not using i, and equals
one. Consequently

    p((i,c(i)),c) = w_c-1 = s_c,  i!=j(c).         (FG-5)

Every c has a teaching triple B, by direct evaluation of the ten listed
rows (the complete finite controls also give minimum teaching size three).
This B contains j(c), since otherwise its neighbor would agree on B.
Its two omitted coordinates are therefore both different from j(c).
Only output c can extend this teaching sample. Its coverage mass equals

    w_c - 2*s_c = 1-s_c.

The coverage inequality requires at least one, so s_c=0 for every c,
contradicting (FG-4). This proves the stated fractional lower-size
infeasibility. It concerns k=1 while the original target permits k=2 on
this VC-two class, so it is not a dual violation at the target parameter.

For an additional entirely integer verification, the control file records
a weighted dual with total sample weight 125 and total message capacity
115. Its weights are constant on five sample orbits under the twenty cube
automorphisms

    i -> a*i+b mod 5,

where a in {1,2,3,4}, b in {0,1,2,3,4}, and all supplied labels are flipped
precisely when a is 2 or 3. These transformations preserve C. In the
integer mask notation of the single-shift note the weighted orbits are:

| Representative (domain mask, labels) | Orbit size | Weight per sample |
|---|---:|---:|
| (3,3) | 10 | 1 |
| (7,0) | 10 | 2 |
| (7,2) | 10 | 4 |
| (15,1) | 20 | 2 |
| (15,6) | 5 | 3 |

Every other sample has weight zero. Thus the total is 10+20+40+40+15=125.
The empty message has maximum weighted coverage fifteen, over ALL 32
total hypotheses. To check this compactly, those hypotheses have four
orbits represented by 0,1,3,5, with coverage respectively 15,15,15,10.
The ten singleton messages form one automorphism orbit. For the singleton literal
(coordinate 0, label 0), whose domain mask is 1 and label mask is 0,
enumerate its sixteen possible decoder outputs in increasing integer
order 0,2,4,...,30. Their weighted coverages are respectively

    8,10,9,10,9,5,10,4,10,10,5,10,10,10,4,8.

So each singleton message has maximum ten, and the total possible weighted
coverage of all eleven messages is at most 15+10*10=115<125. This is an
explicit strict violation of (FG-2) at k=1, verified directly by integer
enumeration including improper hypotheses. It corroborates the analytic
lower-size argument, while preserving the same k<VC limitation.

## 5. The original task remains unclosed

The full target needs a deterministic single total decoder per labeled
message for every total VC-d class, with k=d. A fractional formulation,
its exact dual, an actual fractional vertex, or a lower-bound example at
k<VC does not supply that theorem. No original gate is marked solved by
these route controls. New major solved results remain zero.
