# Exact imaginary compensation for the fixed rank-four real part

15 October 2026. Yongxian Zhang, South China University of Technology.
No external funding. OpenAI AI assistants assisted. Original rights
reserved; attributed external results retain their rights. Author-written
calculation only, without independent review or formal verification.

This calculation explains the failed Hermitian relaxation in checkpoint4.
It is a restricted case of already-known two-copy Werner undistillability,
whose full theorem is attributed to
[Bharti–Gajjala–Haug](https://arxiv.org/html/2607.24479v1).
It is not a new solved major problem, a new priority claim, or an arbitrary-
copy result. N0 remains open in this packet.

Let p_i=|i,0> and q_i=|0,i>, i=1,2, and order their span as
(p_1,p_2,q_1,q_2). The fixed real part

    H=I_3 tensor |0><0|-|0><0| tensor I_3

is diag(I_2,-I_2) on this four-dimensional span. It vanishes outside it.
Every complex rank-two C=H+iK with this real part has its entire support
inside this span: range H is contained in range C+range C*, and both
spaces have dimension four. The joint compatibility argument in
checkpoint4 therefore gives KHK=-H on this span.

Write K in Hermitian two-by-two blocks as

    K=[ E   F  ],   E=E*, G=G*.
      [ F*  G  ]

The compatibility equation implies

    FF*=I+E^2,    F*F=I+G^2,    EF=FG.

In particular F is invertible. Its polar decomposition is
F=sqrt(I+E^2) U with U unitary. E commutes with sqrt(I+E^2), so
EF=FG gives G=U* E U. Put s=Tr(E^2)>=0 and t=Tr E (real). Then

    ||K||_HS^2=4+4s,
    ||Tr_1 K||_HS^2+||Tr_2 K||_HS^2=2s+2t^2,
    Tr K=2t.

The partial-trace identities follow directly from the support: the
diagonal p-block contributes Tr E at |0><0| on the second site and E on
the nonzero labels of the first site; the q-block contributes G and
Tr G in the complementary way. The off-diagonal p/q blocks have zero
partial trace because both site labels differ.

Consequently the exact Werner form is

    Q_2(lambda,K)=4+(4-2lambda)s+(4lambda^2-2lambda)t^2.

For 0<=lambda<=1/2, the coefficient of t^2 is nonpositive and the
two-dimensional trace inequality gives t^2<=2s. Hence

    Q_2(lambda,K)
       >=4+(4-6lambda+8lambda^2)s
       =4+[8(lambda-3/8)^2+23/8]s >=4.

Since Q_2(lambda,H)=4-12lambda and the Hermitian cross contribution
vanishes, every rank-two completion of this fixed H satisfies

    Q_2(lambda,H+iK)>=8-12lambda>=2.

The bound is attained: take E=G=0 and any unitary F=U. The resulting
[[I,iU],[iU*,-I]] has rank two and square zero. Thus this particular
rank-four negative real part cannot produce a physical negative
rank-two Werner witness by choosing a different imaginary completion.
The generic rank-two target allows other real parts in growing Hilbert
spaces; those are not controlled by this calculation.

SIGNATURE_COMPLETION_CONTROL.json and its portable source check the
matrix, rank, partial traces and polynomial identity exactly on three
adversarial examples, including a noncommuting rotated block and a
complex Hermitian block. The universal bound above follows from the
displayed block argument and trace inequality, not from those samples.
