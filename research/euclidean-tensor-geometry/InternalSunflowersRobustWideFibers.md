# Sharp full internal witnessing on robust wide-fiber triple systems

**Yongxian Zhang.** AI-assisted proof development and internal checks; no external peer review claimed.

This is a restricted, high-degree case of [Janzer–Jin–Sudakov–Wu, §6](https://link.springer.com/article/10.1007/s00493-026-00222-1#Sec6), not the unrestricted theorem. Consider a simple tripartite triple system on \(A,B,C\) with \(E>0\) triples. Fix integers \(m\ge2\) and \(1\le D\le m\). Assume:

1. Both the \(AB\) and \(BC\) projections have codegree at most \(D\).
2. Every occupied \(AC\) pair has a fiber of size at least \(2048Dm\), and every active \(B\) vertex has degree at least \(2048Dm\).
3. At each \(A\) or \(C\) vertex, sum the sizes of its \(m\) largest incident \(AC\) fibers (or all if fewer). The sum of these quantities over both parts is at most \(E/64\).

**Theorem.** Some subfamily of size at least \(E/(64D)\) witnesses every realized intersection, including the empty one, by an internal \(m\)-petal sunflower. The order \(1/D\) of the retained fraction is sharp uniformly in \(D\le m\). The hypotheses bound two pair codegrees but do not impose an upper bound on any vertex degree or on the third pair codegree.

## Sample and prune

Sample each triple independently at probability \(p=1/(16D)\). Delete all sampled triples that share an \(AB\) or \(BC\) pair with another sampled triple. Also delete every sampled triple of an \(AC\) fiber if that fiber received more than \(4pf\) sampled triples, where \(f\) is its original size. These decisions can both be taken in the original sample. Conditional on a particular edge being sampled, its probability of the first deletion is at most \(2(D-1)p\). Its probability of the second is at most \((1+pf)/(4pf)\) by Markov's inequality, since the conditional expected sample size in its fiber is at most \(1+pf\). Here \(pf\ge128m\); the sum of the loss probabilities is below \(1/2\). Fix an outcome keeping at least \(pE/2\) triples. Both small projections are now injective; each surviving \(AC\) fiber has size at most \(4pf\).

In this outcome repeatedly perform any applicable deletion:

- Delete the triples of an occupied \(AC\) pair of current degree less than \(m\).
- Delete the triples of an active \(B\) vertex of current degree less than \(m\).
- Delete the triples of an active \(A\) or \(C\) vertex with fewer than \(m\) neighbors in the current \(AC\) support.

Each charged object disappears at its first deletion and never returns. The first two types each cost at most \(E/(2048D)=pE/128\): there are at most \(E/(2048Dm)\) original objects of the relevant type. The third costs at most \(4p(E/64)=pE/16\) by the cap on surviving fibers and the original top-\(m\) mass assumption. Total loss is at most \(5pE/64\), so more than \(pE/4\) survives.

Every repeated nonempty pair is an \(AC\) pair with at least \(m\) petals in its fiber. At any surviving \(B\) vertex its entire link is a matching by both injectivities and has size at least \(m\). At an \(A\) vertex choose \(m\) different \(C\) neighbors and choose a distinct \(B\) completion greedily from each \(AC\) fiber of size at least \(m\). The argument at \(C\) is symmetric. Finally, there are at least \(m\) active \(A\) vertices because any active \(C\) vertex has at least \(m\) such neighbors. Greedily choose a disjoint \(m\)-matching of triples: at each step choose an unused active \(A\), then an unused \(C\) neighbor in its support, then an unused \(B\) completion. This certifies the empty kernel.

## Sharpness

Put \(t=\min(D,m-1)\). Partition \(A\) and \(C\) into \(K\) labeled blocks of size \(t\), with block indices modulo \(K\); use \(B=\{(j,\ell):j\in\mathbb Z/K\mathbb Z,\ 1\le\ell\le L\}\). At a vertex \(b=(j,\ell)\) take all pairs in \(A_i\times C_{i+j}\), for every block \(i\). Then every occupied \(AB\) and \(BC\) pair has codegree \(t\); each \(AC\) fiber has size \(L\); and each \(B\) degree is \(Kt^2\). The two-part top-\(m\) mass fraction is at most \(2m/(Kt)\). Choose integer \(L\ge2048Dm\) and \(K\) such that \(Kt^2\ge2048Dm\) and \(Kt\ge128m\). All hypotheses hold. No \(AB\) pair can occur twice in a valid extraction, since its entire original fiber has \(t<m\) triples. Thus every valid subfamily has size at most \(E/t\le2E/D\), giving the claimed order.

The heavy-support robustness assumption is substantive. The general [capped-projection frontier](InternalSunflowersCappedFrontier.md) allows both unbounded top-fiber mass and no second capped projection; the theorem here does not resolve that case.
