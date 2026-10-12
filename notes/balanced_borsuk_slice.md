# A nine-piece cover of a balanced projector slice

**Status:** elementary complete argument; not peer reviewed or formally verified. This excludes only one proposed eight-dimensional Borsuk witness.

Consider rank-one projectors $P_x=xx^T$ with $x\in\mathbb R^4$, $\|x\|=1$, and $x_1^2+x_2^2=x_3^2+x_4^2=1/2$. They lie in an affine space of dimension eight. Write

$$x=2^{-1/2}(\cos\theta,\sin\theta,\cos\phi,\sin\phi),\quad u=(\theta+\phi)/2,\quad v=(\theta-\phi)/2.$$

The projector is parametrized by $(u,v)\in(\mathbb R/\pi\mathbb Z)^2$; adding $\pi$ to either parameter sends $x$ to $-x$ and leaves $P_x$ fixed. The cosine addition identity gives

$$\langle x,x'\rangle=\cos(u-u')\cos(v-v'),\qquad \|P_x-P_{x'}\|_F^2=2(1-\langle x,x'\rangle^2).$$

Cover each circle of circumference $\pi$ by three closed arcs of length $\pi/3$. The nine product rectangles cover the parameter torus. Lift two points of each rectangle to its defining arcs; the two parameter differences have absolute value at most $\pi/3$. Consequently $|\langle x,x'\rangle|\ge1/4$ and every piece has squared diameter at most $15/8<2$. An orthogonal pair occurs when $u$ differs by $\pi/2$ and $v$ is unchanged, so the whole slice has squared diameter exactly $2$.

Thus this particular slice cannot be a Borsuk counterexample. No claim is made about other eight-dimensional sets, optimality of nine pieces, or the validity of the full upstream nine-dimensional obstruction.

**Source of the projector construction:** OpenAI, *A nine-dimensional counterexample to Borsuk's covering assertion*, September 23, 2026, family 156 in `openai/math`, pinned snapshot `adc7f1241b42e322a6451854ab7e4b4c146bf78a`. The covering proof above does not use the upstream obstruction theorem.
