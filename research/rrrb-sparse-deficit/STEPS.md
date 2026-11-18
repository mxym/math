# How many classes are needed?

Suppose the graphon $W$ is constant on each product of two parts of one measurable partition into at most $s$ classes, and $p>0$. Then
$$
\frac12-\frac{F(W)}{p^2}\ge\frac{1}{4s}.
$$

Use the two oriented red edges from [the proof](PROOF.md). Write $A_i$ for class $i$, $w_i(y)$ for its common row up to null sets, and $d_i=\int w_i$. The class of the first endpoint of a random red edge has probabilities $\pi_i=|A_i|d_i/p$. Consider only classes with $\pi_i>0$. Given $X,U\in A_i$, the endpoints $Y,V$ are independent with common density $w_i/d_i$. The parameters of the two bridge colours are exactly $w_i(Y)$ and $w_i(V)$, since $X,U$ have the same row. These parameters are independent and identically distributed. The independent colour samplings on distinct pairs therefore give two independent Bernoulli variables of common mean $t_i=\int w_i^2/d_i$. Neither the two parameters nor the two colours are assumed independent without the conditioning. Given this event the probability of the same colour is $t_i^2+(1-t_i)^2\ge1/2$. Summing and using the half in the deficit identity,
$$
\Delta(W)\ge\tfrac14\sum_i\pi_i^2\ge\tfrac{1}{4s}.
$$
This also handles non-binary graphons and parts of unequal mass.

If $W_p$ is a family with at most $s(p)$ classes and $\Delta(W_p)\le C/\log(1/p)$, this gives $s(p)\ge\log(1/p)/(4C)$. Conversely the explicit family in the proof uses $2k$ classes before dilution and at most $2k+1=O(\log(1/p))$ afterwards. Thus logarithmically many classes are necessary and sufficient **in order** for attaining the deficit order. This neither asserts optimality of the numerical factor $1/4$ as $s$ varies nor determines the structure of an exact extremizer at any individual fixed density.
