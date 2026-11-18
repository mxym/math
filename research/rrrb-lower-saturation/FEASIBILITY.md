# The upper part of the unequal-class interval

Here $1/3\le p<1/2$ and the notation is as in [the proof](PROOF.md). In particular $x=4p-1>0$, $a=2p-4p^2>0$, $0<r<x/8\le1/8$, $C=a+xr-4r^2$ and $q=C/4$. Take $h^2=(p-r)/(1-p+r)$ and $P=p(1-p)$.

To check $L\ge0$ and $H\le1$ it is enough to check $D\ge0$. Expanding and regrouping,
$$
D=p(3p-1)[P-(3-4p)r]+r^2[-18p^2+14p-1+(12p-5)r-3r^2].
$$
The first term is nonnegative: $P\ge2/9$ while $(3-4p)r\le5/24<2/9$. In the bracket the concave quadratic $-18p^2+14p-1$ has minimum at least $3/2$ at the endpoints of this interval, $(12p-5)r\ge-1/8$, and $-3r^2\ge-3/64$. The bracket is strictly positive.

The reverse constraints are straightforward: $L\le p$, and $H\ge0$ since $r+r^2\le x/8+x^2/64<p^2$, equivalent to $r/h^2<p$. Also $7/17\le h^2\le1$ because $p-r\ge(4p+1)/8\ge7/24$. Hence $0\le1/h-h\le10/\sqrt{119}<1$. Since $C\le a+x^2/16\le1/4$, the cross entry $p+r+(\sqrt C/2)(1/h-h)$ lies between $p$ and $p+1/8+1/4<1$. Thus all three kernel entries are admissible.
