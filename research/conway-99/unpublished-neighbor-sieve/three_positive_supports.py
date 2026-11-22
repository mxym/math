"""Enumerate the 28 marked vertices, fixing the three positive names in each signature.

Requires python-flint for the exact positive semidefiniteness checks.
"""
from collections import Counter
from itertools import combinations, combinations_with_replacement, permutations, product
from flint import fmpz_mat
from three_positive import members, signature, survivors

COLORS = ((0,0),(1,1),(2,2),(0,1),(0,2),(1,2))


def matching_types(leaves):
    for a,b,c in product(*(range(k//2+1) for k in leaves)):
        u,v,w = [k-2*t for k,t in zip(leaves,(a,b,c))]
        if (u+v+w)%2:
            continue
        between = ((u+v-w)//2,(u+w-v)//2,(v+w-u)//2)
        if min(between)>=0:
            yield (a,b,c,*between)


def support_graph(positive,high,isolates,edges,attachments,matching):
    masks = positive+high+[0]*isolates
    pairs = [(i,j) for i,j in combinations(range(3),2) if j in members(positive[i])]
    pairs.extend((3+i,3+j) for i,j in edges)
    for i,colors in enumerate(attachments):
        for color in colors:
            pairs.append((len(masks),3+i))
            masks.append(1<<color)
    for (u,v),count in zip(COLORS,matching):
        for _ in range(count):
            pairs.append((len(masks),len(masks)+1))
            masks.extend((1<<u,1<<v))
    assert len(masks)==28
    for j,mask in enumerate(masks[3:],3):
        pairs.extend((i,j) for i in members(mask))
    rows = [0]*28
    for i,j in pairs:
        rows[i] |= 1<<j
        rows[j] |= 1<<i
    return rows


def support_graphs(positive,neg):
    high = [m for m in (3,5,6,7) for _ in range(neg[m])]
    leaves = [neg[1<<i] for i in range(3)]
    feasible_pairs = [(i,j) for i,j in combinations(range(len(high)),2)
                      if (high[i]&high[j]).bit_count()<=1]
    perm_groups = [list(permutations([i for i,m in enumerate(high) if m==v]))
                   for v in sorted(set(high))]
    reorderings = []
    for blocks in product(*perm_groups):
        p = [i for block in blocks for i in block]
        reorderings.append((p,{v:i for i,v in enumerate(p)}))
    for flags in product((0,1),repeat=len(feasible_pairs)):
        edges = [pair for pair,keep in zip(feasible_pairs,flags) if keep]
        neighbors = [[] for _ in high]
        for i,j in edges:
            neighbors[i].append(j)
            neighbors[j].append(i)
        options = []
        for mask,others in zip(high,neighbors):
            degree = mask.bit_count()-len(others)
            if degree<0:
                break
            choices = []
            for colors in combinations_with_replacement(range(3),degree):
                if all((positive[p]&mask).bit_count()+sum(p in members(high[j]) for j in others)
                       +colors.count(p)<=2-int(p in members(mask)) for p in range(3)):
                    choices.append(colors)
            if not choices:
                break
            options.append(choices)
        if len(options)!=len(high):
            continue
        for attachments in product(*options):
            left = [k-sum(a.count(i) for a in attachments) for i,k in enumerate(leaves)]
            if min(left)<0:
                continue
            tag = (tuple(tuple(ns) for ns in neighbors),attachments)
            if any((tuple(tuple(sorted(inv[k] for k in neighbors[j])) for j in p),
                    tuple(attachments[j] for j in p))<tag for p,inv in reorderings):
                continue
            for matching in matching_types(left):
                yield support_graph(positive,high,neg[0],edges,attachments,matching)


def valid_pairs(rows):
    return all((rows[i]&rows[j]).bit_count()<=2-((rows[i]>>j)&1)
               for i,j in combinations(range(28),2))


def parent_pairs(rows,p):
    known = [i for i in range(28) if rows[p] & (1<<i)]
    free = {i for i in known if not rows[i]&rows[p]}
    unnamed = 14-len(known)
    left = unnamed-len(free)
    if left<0 or left%2:
        return False
    used = Counter(rows[i]&rows[p] for i in range(28) if i!=p and i not in known)
    if used[0]>unnamed*(unnamed-1)//2-left//2:
        return False
    return all(used[1<<i]<=unnamed-int(i in free) for i in known)


def outside_rounding(rows):
    # For each subset of positives, give it weight -2. Give weight one to
    # negatives missing that whole subset. The 71 outside evaluations are integers.
    for selected in range(1,8):
        weight = [-2*int(bool(selected & (1<<i))) if i<3 else int(not (row&selected))
                  for i,row in enumerate(rows)]
        evaluated = [sum(weight[j] for j in range(28) if row & (1<<j)) for row in rows]
        total = 14*sum(weight)-sum(evaluated)
        square = (12*sum(v*v for v in weight)+2*sum(weight)**2
                  -sum(v*w for v,w in zip(weight,evaluated))-sum(w*w for w in evaluated))
        low,more = divmod(total,71)
        if square<(71-more)*low**2+more*(low+1)**2:
            return False
    return True


def spectral(rows):
    # Both polynomials are det(tI+B) of real symmetric integer matrices B.
    # A negative eigenvalue gives a positive root. For PSD all coefficients
    # are elementary symmetric polynomials in nonnegative eigenvalues.
    for scale,diagonal,constant in ((-9,27,1),(11,44,-2)):
        minus_gram = fmpz_mat([[-(scale*((row>>j)&1)+diagonal*(i==j)+constant)
                               for j in range(28)] for i,row in enumerate(rows)])
        if any(c<0 for c in minus_gram.charpoly()):
            return False
    return True


def census():
    total = Counter()
    for g,size,neg in survivors():
        counts = Counter()
        for rows in support_graphs(g,neg):
            counts['generated'] += 1
            if valid_pairs(rows):
                counts['pairs'] += 1
                if spectral(rows):
                    counts['spectral'] += 1
                    if all(parent_pairs(rows,p) for p in range(3)) and outside_rounding(rows):
                        counts['outside'] += 1
        total += counts
        print(signature(g,size,neg),counts['pairs'],counts['spectral'],counts['outside'],flush=True)
    print('Totals',total)
    return total


if __name__=='__main__':
    counts = census()
    assert counts=={'generated':21911,'pairs':20985,'spectral':16229,'outside':13606}
