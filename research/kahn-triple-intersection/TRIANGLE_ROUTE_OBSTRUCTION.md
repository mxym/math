# A concrete local triangle obstruction to a rounding route

This is an explicit design realization of Kahn's existing local
triangle obstruction, not a new claimed research theorem.

Let s be a fixed prime power, N>=2, and V=F_s^N with v=s^N points.
Its affine-line design has block size s, replication
r0=(v-1)/(s-1), and b=v r0/s lines. Replace each point x by
three auxiliary points (x,0),(x,1),(x,2). For every affine line L
and each omitted label a in {0,1,2}, create the auxiliary block

```
B(L,a) = {(x,i): x in L and i != a}.
```

It has size 2s. Every auxiliary point has degree 2r0. Any two
points in the same triple share r0 blocks; points in different
triples share either one or two blocks, since their affine line
is unique. Thus every pair shares a block. Every triple of distinct
auxiliary points shares at most two blocks: all three local labels
at one x share none; otherwise a shared block has a uniquely
determined affine line and at most two possible omissions.

Take the incidence dual H: its edges are auxiliary points and
its vertices are the block identities. It is a simple intersecting
r-uniform hypergraph with

```
r=2r0, m=3v, maximum triple intersection <=2,
maximum pair intersection = r0 = r/2.
```

Simplicity follows because same-triple points have different omission
sets, while different-triple points share at most two vertices and
r=2r0>=6. The family is outside the small-pair-intersection setting
and inside the small-triple-intersection setting as N increases.

A vertex cover of H corresponds to a collection of auxiliary blocks
covering all triples. Each triple needs at least two selected blocks,
since a block contains at most two of its three points. Each block
meets s triples. Double counting selected block/triple incidences
therefore gives tau>=2v/s. An affine parallel class partitions V
into v/s lines; select two different omissions on each line.
This covers every triple, attaining

```
tau(H)=2v/s.
```

Uniform dual fractional weights 1/(2s) on H's m edges are feasible,
since each original vertex has degree 2s. Uniform primal weights
1/r on its 3b vertices cover every edge and have total 3b/r=3v/(2s).
Their objective values coincide, certifying exactly

```
tau*(H)=3v/(2s), tau(H)/tau*(H)=4/3.
```

As N increases,

```
m/r -> c=3(s-1)/2,
tau/r -> (s-1)/s,
c/(c+1) - (s-1)/s = (s-1)/(s(3s-1)) >0.
```

Thus the construction does not contradict Kahn's harmonic conjecture.
It rules out the proposed route “small triple intersections imply
rounding of any optimal fractional cover with negligible loss.”
Kahn explicitly described the 0-or-2-on-each-triple mechanism and
its factor 4/3 in Section 5. The geometric realization and exact
diagnostic below make that known obstacle concrete for this project;
they are not offered as an originality claim.
