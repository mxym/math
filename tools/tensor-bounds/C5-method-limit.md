# Why splicing plus three-part grouping stops at 49/12 on C5

This is a workbench method check, not a result about the unrestricted optimum. It applies to any sequence of capacity-respecting rational splices and one final grouping into at most three parts. A splice never increases the capacity of any cut. Indeed, if its endpoints are on different sides, the new edge replaces exactly one equally weighted cut edge; if they are on the same side, it creates no cut edge. This remains true for every singleton or union of final groups, regardless of the order of operations.

Write the exact rectangular exponent function for decreasing weights X,Y,Z as

```
R = X+Y + max((X+Y)Z−XY,0)^2/(4XYZ).
```

On zero coordinate planes the correction is zero. The function is coordinatewise nondecreasing, since reducing any edge bundle is a local restriction. It is also bounded by the sum of the weights (the coordinate decomposition). This uses the same pinned theorem and model as the tool.

For group sizes 2+2+1, let x denote the weight between the larger parts and y,z the two edges to the singleton, with y≥z by symmetry. The original cut of each larger part has capacity at most 4, and the singleton capacity 2. Thus x+y≤4, x+z≤4 and y+z≤2. By monotonicity increase x to 4−y. Now x≥y≥z, x+y=4, and 0≤z≤1. For fixed z the correction is nonincreasing as y increases from z: y(4−y) is nondecreasing for y≤2 and occurs as a subtraction in the numerator and a factor in the denominator. So take y=z=t. The correction becomes t²/(4(4−t)), at most 1/12. At z=0 the bound is 4 by the zero-plane formula. The unspliced partition with weights (3,1,1) attains 49/12.

For group sizes 3+1+1, use z for the edge between singleton groups. Their cut capacities give x+z≤2 and y+z≤2. If z≥2/3, the sum of weights is at most 4−z<4. If 0≤z≤2/3, increase both x,y to 2−z. They are the two largest weights and the correction vanishes, since 2z≤2−z, giving at most 4. A two-part grouping is bounded by the original max cut 4.

Therefore the best bound obtainable by this combined method on C5 is exactly 49/12, assuming the external rectangular theorem. An improvement needs a certificate outside this family, such as one retaining four or more parties or passing through a non-graph tensor.
