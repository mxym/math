// Exact parameter check for triangle-free orientations of primitive SRGs with d > n/4.
// Run with Node.js. Counts after each filter are printed below.
const limit = 19305;
const smallestPrime = new Int32Array(limit + 2);
for (let prime = 2; prime < smallestPrime.length; prime++) {
  if (smallestPrime[prime]) continue;
  for (let n = prime; n < smallestPrime.length; n += prime) {
    if (!smallestPrime[n]) smallestPrime[n] = prime;
  }
}

function divisorsOfProduct(...factors) {
  const primePowers = new Map();
  for (let factor of factors) {
    while (factor > 1) {
      const prime = smallestPrime[factor];
      primePowers.set(prime, (primePowers.get(prime) || 0) + 1);
      factor /= prime;
    }
  }
  const divisors = [1];
  for (const [prime, exponent] of primePowers) {
    const baseLength = divisors.length;
    let power = 1;
    for (let j = 1; j <= exponent; j++) {
      power *= prime;
      for (let i = 0; i < baseLength; i++) divisors.push(divisors[i] * power);
    }
  }
  return divisors;
}

const counts = Array(7).fill(0);
const surviving = [];
for (let r = 1; r <= limit / 2; r++) {
  for (let t = 2; r * t <= limit; t++) {
    const a = (r + 1) * (t - 1);
    const product = r * t;
    if (a + product + 2 > limit) break;
    for (const mu of divisorsOfProduct(r, t, r + 1, t - 1)) {
      const k = product + mu;
      const ell = a + a * product / mu;
      const n = k + ell + 1;
      if (n > limit || 2 * k <= n) continue;
      const target = Math.floor(n / 4) + 1;
      const lambda = mu + r - t;
      const d = Math.max(target, 1 + Math.floor(2000 * (target - (k-1-lambda)) / 693));
      if (2 * d > k || k > n - 1) continue; 
      if (lambda < 0 || lambda >= k || n - 2 - 2 * k + mu < 0 || mu >= k) continue;
      counts[0]++;

      const fNumerator = (n - 1) * t - k;
      if (fNumerator % (r + t)) continue;
      const f = fNumerator / (r + t);
      const g = n - 1 - f;
      if (f <= 0 || g <= 0 || Math.min(f * (f + 3), g * (g + 3)) < 2 * n) continue;
      counts[1]++;
      if ((r + 1) * (k + r - 2 * r * t) > (k + r) * (t - 1) ** 2) continue;
      if ((1 - t) * (k - t - 2 * r * t) > (k - t) * (r + 1) ** 2) continue;
      counts[2]++;

      const [N,K,L,R,T,D] = [n,k,lambda,r,t,d].map(BigInt);
      const den = 3n * (K + T);
      const varianceNumerator = K*K*(K+T) + 2n*K*K*T + 3n*K*T*T
          - 8n*D**3n - 12n*D*D*T - 6n*D*T*T;
      if (varianceNumerator < 0n || 3n*varianceNumerator < den*N*(L-3n*R)) continue;
      counts[3]++;
      if (L > R && 3n*(L-R)*varianceNumerator < den*K*K*(L-3n*R)) continue;
      counts[4]++;
      if (L > R && K*(L-3n*R) > 3n*(L-R)*(K-2n*D)) continue;
      counts[5]++;

      let previous = 0n;
      let squaredIncrements = 0n;
      for (let i = 1n; i <= N; i++) {
        const total = N*N*(K-2n*D);
        const individual = 2n*N*(K-D)*i;
        const spectral = N*(2n*(K-D)+T)*i - (K+T)*i*i;
        const prefix = [total, individual, spectral].reduce((x,y) => x < y ? x : y);
        squaredIncrements += (prefix-previous)**2n;
        previous = prefix;
      }
      const varianceDiscrete = squaredIncrements - (K-2n*D)**2n*N**3n;
      if (3n*varianceDiscrete < N**4n*(L-3n*R)) continue;
      if (L > R && 3n*(L-R)*varianceDiscrete < N**3n*K*K*(L-3n*R)) continue;
      counts[6]++;
      surviving.push({n,k,lambda,mu,r,t,f,g,d});
    }
  }
}
surviving.sort((a,b) => a.n-b.n || a.k-b.k || a.lambda-b.lambda);
const orders=surviving.map(o=>o.n);
if (String(counts)!=="698197,33482,32419,27,20,20,20" || String(orders)!=="10,15,27,35,75,81,95,96,105,112,120,125,126,154,162,175,176,243,253,275") throw Error("Unexpected surviving parameters");
console.log({counts, surviving});
