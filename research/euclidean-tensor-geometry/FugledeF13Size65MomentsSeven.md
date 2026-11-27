# Size 65 in F_13^3: all mixed moments through degree seven

Use the preceding [degree-six argument](FugledeF13Size65MomentsSix.md) for the elementary spectral-pair notation and exact degree-six rigidity. In particular either member has affine line cap five, affine plane cap thirteen, no full projective line in its normal set U, and at most one layered normal (five occupancies of thirteen and eight zero). We prove no nonzero degree-seven homogeneous form F can vanish on D(B) for either member B. This is a partial result, not an exclusion of size 65.

## A four-direction planar bound and four-blocking

Over F_13 there is no noncollinear six-point planar set with at most four directions. The standalone [verify-fuglede-f13-size65-moments7.js](verify-fuglede-f13-size65-moments7.js) checker fixes a triangle 0,e_1,e_2, adds in turn one of the eleven possible slopes to its three slopes, and tries all triples of further points. The check even allows unrestricted collinear occupancy once the marked triangle is present.

If some projective line has at most three points of D(B), the parallel five-collinear-slice argument of the preceding note produces four distinct rational factors of F through a common parallel axis d. A nonfactor line through d then has at most 1+7−4=4 zeros and therefore at most four points of D(B). Every affine slice of that direction plane has at most five sites (six would be noncollinear by line cap five), and the total forces uniform occupancy five. At least seven of the fourteen projective lines through d are nonfactors. Thus a pencil through the actual five-point affine support line of direction d has occupancy at most 7·5+7·13=126, less than 130. This contradiction proves that each projective line contains at least four points of D(B).

## Heavy factors

Put N=|D(B)| and n_L=|D(B)∩L|. Incidence gives
sum_L (n_L−4)(n_L−7) = N²−141N+5124 ≥154.
Only rational line factors can contribute positive values. Call one heavy when n_L≥11; a non-heavy factor contributes at most 18, a heavy factor at most 54. Hence at least one heavy factor is required.

Any projective line with at least eleven uniform normals for one member has exactly thirteen, with the unique nonuniform normal layered. Indeed at most three nonuniform profiles remain in the two-dimensional Radon identity (as in the size-91 weighted-profile proof). Its homogeneous-degree Vandermonde relations make the residues at most affine in each profile. A nonconstant affine residue profile has integer mass 78 or 91 under plane cap thirteen, not 65. A nonuniform constant residue is therefore zero (its occupancies are zero or thirteen). The constant congruence of the Radon identity then forces the number of remaining nonuniform profiles to be one, as 5(b−1)≡0 and b∈{1,2,3}.

As D(B)⊂U of the partner, all heavy factors contain the sole layered normal P of that partner, and P is not in D(B). There cannot be four factors through P: a nonfactor through it would have at most three other zeros. Thus there are one, two, or three heavy factors. Write k for the number of distinct rational line factors. If k=6, stripping all rational factors with multiplicities leaves no nonconstant residual, because residual degree would otherwise be one and its line also a factor. The same six-line union certificate used in the preceding proof rules out any four-blocking proper-on-each-line subset of that union. So k≠6.

## A seven-factor arrangement cannot have a missing triple point

If k=7, any point of the factor union outside D(B) is on at most two factors. Four or more forces a radial nonfactor line with at most three other zeros. If three factors pass through a missing point Q, every intersection of two of the other four factors must belong to one of the first three factors; otherwise the line from Q to that intersection is a nonfactor and sees at most three D(B) points. Thus all six pairs of the four outer lines have their intersections on the three lines through Q.

If four outer lines concur, their intersection cannot belong to a Q-factor, since five concurrent factors contradict four-blocking even at a point of D(B). If three outer lines meet at T and the fourth does not, the three distinct intersections of the fourth with those three lie on distinct lines through Q: two cannot share a Q-line because their joining line is the fourth outer line. The point T cannot belong to any of those Q-lines because each of its connections to the three points is already an outer line. Finally, if the four outer lines are in general position, the three Q-lines must cover their six intersections with opposite pairs on each (joining two intersections that share an outer factor would produce that outer factor). The three diagonal lines of a complete quadrilateral are not concurrent in odd characteristic: taking the four outer lines to be x=0,y=0,z=0,x+y+z=0 gives diagonals x+y=0,x+z=0,y+z=0, whose determinant is ±2. This proves the missing-triple assertion.

## Case of one heavy factor

At most 54+18(k−1) is available in the incidence inequality, so k=7. The maximum 162 is only eight above the absolute minimum 154. The heavy factor must have n=13 (n=12 loses fourteen), and the other six n=10 except possibly one with n=9 (loss eight). It follows N∈{68,...,73}. The nonfactor occupancy belongs to {4,5,6,7}, with at most four lines of size 5 or 6, since each such line costs two in the incidence total.

Any missing point Q has multiplicity m=1 or 2 by the missing-triple assertion. No radial nonfactor through it has seven D(B) points. Let e_Q sum (n_L−4) over radial nonfactor lines, so
N = sum_{factor L through Q} n_L + 4(14−m)+e_Q.
A nonfactor line with n_L=5 contains at most two missing points and one with n_L=6 contains at most one, because any nonfactor line meets the union in at most seven distinct points. Consequently sum_Q e_Q≤2(a_5+a_6)≤8, where a_i counts nonfactors of size i. At least 25 factor incidences are omitted, hence there are at least thirteen distinct missing points. Except for the unique missing point on the heavy factor, the displayed baseline is at most 68 (at most 62 for a simple point). Thus N≥69 already costs at least twelve, impossible. If N=68, the factor contribution must be 162 and a_5+a_6=1; there are exactly 25 omitted incidences. No simple missing point can occur: the baseline of a simple low point is 62 and of a simple high point is 65, both requiring more than the total budget two. An odd total number of omitted incidences cannot consist solely of doubles. Contradiction.

## Case of three heavy factors

All three meet at missing P, and there is no fourth factor there. If k=7, the missing-triple argument applies. If 3≤k≤6, each of eleven nonfactor lines through P needs at least four D(B) points, with at most k−3 supplied by the other factors. Thus at least 11(7−k) distinct points must be supplied by the residual off P. After stripping all rational factors, including multiplicities, the residual has degree d≤7−k≤4 and no rational line factor. If it has a rational point, each of the fourteen lines through it sees at most d−1 other zeros, for at most 1+14(d−1) points, smaller than 11(7−k). A constant residual has none. Contradiction.

## Case of two heavy factors

For k≤4 the contribution does not reach 154. If k=5, the upper total 162 forces both highs to have n=13 and the other three have n≤10. At most one of the low factors passes the common missing P, as otherwise four factors pass P. Every low not through P meets both highs at points of D(B), costing at least four in counting the summed occupancies as distinct points. At most 52 points of D(B) are therefore on the factor union. The residual of degree at most two with no rational line factor contributes at most 15 points, so N≤67; but from the bound 162 we need N≥68.

It remains k=7. The two highs meet at missing P and the missing-triple assertion says none of the five low factors passes P. If the two high occupancies are n_1,n_2≥11, the twelve nonfactor lines through P have at least four points each. Hence N≥n_1+n_2+48≥70. The five low factors have ten total pair incidences with the highs (counting multiplicity). Apart from P, there are exactly 26−n_1−n_2 missing points on the highs. Each meets at most one low factor, again by no missing triple. Thus at least n_1+n_2−16 high-low pair incidences occur in D(B). Each contributes one to the excess when summing line occupancies rather than counting distinct points: if a D(B) point on a high lies on several lows, their count is exactly its excess. Therefore N≤n_1+n_2+50−(n_1+n_2−16)=66, contradiction.

All branches are impossible. As M_7 of each member vanishes on its uniform normals and hence on the other member's difference directions, both seventh moment forms vanish; all their mixed degree-seven moments follow by comparing multinomial coefficients in characteristic thirteen.
