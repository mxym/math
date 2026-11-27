# Exact simplex-spike calculator

Save simplex-spike.cjs and simplex-spike.test.cjs next to each other. Node 18+; no npm dependencies. 

    printf '%s\n' '{"lambda":["1/2","1/2",0],"a":["1/2","1/2",-1]}' | node simplex-spike.cjs
    node simplex-spike.test.cjs

The arrays are barycentric: lambda has nonnegative entries summing to 1 and at least one zero, a sums to 0. JSON numbers are accepted only when parsed as safe integers; for full exactness always quote integers/fractions, especially long values or decimals, which should be represented as fractions. See the [derivation and coordinate conventions](simplex-spike-polar-response.md). The output polarLossCoefficient is the normalized loss at the original centering, relative to the original polar volume. santaloShiftCoefficient is the coordinate vector in the sum-zero hyperplane; recenterGainCoefficient is the normalized extra decrease when moving to that optimal center. Orders are the exponents associated to the reported coefficients, not a claim of nonzero coefficients for non-outgoing inputs. At least one negative a entry outside supp(lambda) guarantees an outgoing spike and a nonzero polar loss.

## Exact evaluation

Let q=|J| and x_j=-a_j on J. Put f(x)=x_+^(k+q-1), a C^(q-1) function because k>=1. Hermite–Genocchi writes the divided difference f[x_1,...,x_q] as the integral of f^(q-1)(sum gamma_j x_j) over the simplex of gamma, using Lebesgue measure in its q-1 independent barycentric coordinates. That simplex has coordinate volume 1/(q-1)!. The derivative is (k+q-1)!/k! times (sum gamma_j x_j)_+^k, so the desired probability expectation is 1/binomial(k+q-1,k) times the divided difference. At repeated nodes the confluent difference is f^(r)(x)/r! when all r+1 nodes are equal. Sorting ensures all such equal nodes are contiguous, including zero, at which all derivatives of orders used vanish.

For E[gamma_j b^k], normalize the density gamma_j by multiplying by q. The result is a Dirichlet distribution with parameter 2 at j and 1 elsewhere. Equivalently, start with q+1 uniform barycentrics and add the last coordinate to coordinate j: fixing the sum, integration over the split gives density proportional to that sum. Duplicating x_j and dividing the resulting expectation by q therefore gives the normalized moment. This identity also works for q=1. CLI evaluation uses only exact BigInt rational operations; among all moment calls it uses O(q^3) arithmetic operations in the worst case, ignoring bit-length costs.

## Verification

The CLI test suite includes six exact examples and four error checks. Run the test command above to reproduce them.
