const order = 15;

function choose(n, k) {
    if (k < 0 || k > n) return 0;
    let result = 1;
    for (let i = 1; i <= k; i++) result = result * (n - i + 1) / i;
    return result;
}

function triangleLower(n, edges) {
    if (n === 0) return 0;
    return Math.max(0, Math.ceil((4 * edges * edges - n * n * edges) / (3 * n)));
}

// Ordinary Kruskal–Katona upper bound, by binomial expansion.
function kruskalKatona(count, rank) {
    let result = 0;
    while (count > 0) {
        let top = rank;
        while (choose(top + 1, rank) <= count) top++;
        count -= choose(top, rank);
        result += choose(top, rank + 1);
        rank--;
    }
    return result;
}

function* degreeLists(length, limit, smallest = 0, prefix = []) {
    if (length === 0) {
        yield prefix;
        return;
    }
    for (let degree = smallest; degree <= limit; degree++) {
        yield* degreeLists(length - 1, limit, degree, [...prefix, degree]);
    }
}

function pairValues(degrees, score) {
    return degrees.flatMap((degree, i) => degrees.slice(i + 1).map(other => score(degree, other)));
}

// For any admissible colex prefix, count the next-rank faces supported by it.
function coloredUpper(n, r) {
    const faces = Array.from({length: r + 1}, () => []);
    for (let mask = 1; mask < (1 << n); mask++) {
        let colors = 0;
        let rank = 0;
        for (let i = 0; i < n; i++) {
            if ((mask & (1 << i)) === 0) continue;
            colors |= 1 << (i % r);
            rank++;
        }
        let distinct = 0;
        for (; colors; colors &= colors - 1) distinct++;
        if (distinct === rank) faces[rank].push(mask);
    }
    return faces.map((row, rank) => {
        const indices = new Map(row.map((mask, i) => [mask, i + 1]));
        const counts = Array(row.length + 1).fill(0);
        for (const larger of faces[rank + 1] ?? []) {
            const largestSubface = larger ^ (larger & -larger);
            const i = indices.get(largestSubface);
            if (i !== undefined) counts[i]++;
        }
        for (let i = 1; i < counts.length; i++) counts[i] += counts[i - 1];
        return counts;
    });
}

function cliqueLower(n, r) {
    const outside = n - r;
    const lower = [];
    for (const degrees of degreeLists(outside, r - 1)) {
        let initialEdges = choose(r, 2) + degrees.reduce((sum, d) => sum + d, 0);
        let base = Array.from({length: r - 2}, (_, i) =>
            choose(r, i + 3) + degrees.reduce((sum, d) => sum + choose(d, i + 2), 0));
        const intersections = pairValues(degrees, (a, b) => Math.max(0, a + b - r)).sort((a, b) => a - b);
        for (let e = 0; e <= intersections.length; e++) {
            const m = initialEdges + e;
            const bound = base.slice();
            bound[0] = Math.max(bound[0] + triangleLower(outside, e), triangleLower(n, m));
            lower[m] = lower[m] ? bound.map((v, i) => Math.min(v, lower[m][i])) : bound;
            if (e < intersections.length) {
                base = base.map((v, i) => v + choose(intersections[e], i + 1));
            }
        }
    }
    return lower;
}

// Each surviving edge count maps to a superset of (rise transition rank, current count).
function possibleCrossings(n, r) {
    const upper = coloredUpper(n, r);
    const lower = cliqueLower(n, r);
    const possible = new Map();
    for (let edges = choose(r, 2); edges <= upper[1][n]; edges++) {
        let states = new Map([[3 * edges + Number(edges < n), n]]);
        const crossings = new Set();
        for (let k = 2; k < r; k++) {
            const next = new Map();
            for (const [state, previous] of states) {
                const current = Math.floor(state / 3);
                const flag = state % 3;
                const mm = Math.ceil((k * k * current * current - n * current * previous) /
                    ((k * k - 1) * previous));
                const start = Math.max(lower[edges][k - 2], mm);
                for (let x = start; x <= upper[k][current]; x++) {
                    const newFlag = flag === 2 || (flag === 1 && x > current)
                        ? 2 : Number(flag === 1 || x < current);
                    if (flag === 1 && newFlag === 2) crossings.add(k + "," + current);
                    const key = 3 * x + newFlag;
                    if (current > (next.get(key) ?? 0)) next.set(key, current);
                }
            }
            states = next;
        }
        if ([...states.keys()].some(key => key % 3 === 2)) possible.set(edges, [...crossings]);
    }
    return possible;
}

function maximumFourCliques(n, r, edges, triangles) {
    const q = n - r;
    let maximum = -1;
    for (const degrees of degreeLists(q, r - 1)) {
        const e = edges - choose(r, 2) - degrees.reduce((sum, d) => sum + d, 0);
        if (e < 0 || e > choose(q, 2)) continue;
        const oneOutsideThree = degrees.reduce((sum, d) => sum + choose(d, 2), 0);
        const oneOutsideFour = degrees.reduce((sum, d) => sum + choose(d, 3), 0);
        const leftoverTriangles = triangles - choose(r, 3) - oneOutsideThree;
        const minIntersections = pairValues(degrees, (a, b) => Math.max(0, a + b - r)).sort((a, b) => a - b);
        const minTwo = minIntersections.slice(0, e).reduce((sum, d) => sum + d, 0);
        const caps = pairValues(degrees, (a, b) => Math.min(a, b, r - 2)).sort((a, b) => b - a).slice(0, e);
        const first = triangleLower(q, e);
        const last = Math.min(kruskalKatona(e, 2), leftoverTriangles - minTwo);
        for (let u = first; u <= last; u++) {
            const twoTriangles = leftoverTriangles - u;
            let left = twoTriangles;
            let twoFour = 0;
            for (const cap of caps) {
                const filled = Math.min(cap, left);
                twoFour += choose(filled, 2);
                left -= filled;
            }
            if (left !== 0) continue;
            const threeFour = Math.min(kruskalKatona(twoTriangles, 2),
                Math.floor((q - 2) * twoTriangles / 3), u * Math.min(r - 3, degrees[q - 3]));
            const fourFour = Math.min(kruskalKatona(u, 3), Math.floor((q - 3) * u / 4));
            maximum = Math.max(maximum, choose(r, 4) + oneOutsideFour + twoFour + threeFour + fourFour);
        }
    }
    return maximum;
}

function check(condition, description) {
    if (!condition) throw new Error(description);
}

function main() {
    const raw = new Map();
    for (let r = 3; r <= order; r++) {
        const result = possibleCrossings(order, r);
        if (result.size) raw.set(r, result);
    }
    check([...raw.keys()].join() === "5,6,7,9", "Unexpected clique-number branch");
    const five = raw.get(5);
    check(five.size === 1 && five.get(14)?.join() === "2,14", "Unexpected rank-five branch");
    for (const [edges, crossings] of raw.get(9)) {
        check(edges < 84 && crossings.every(x => x.startsWith("4,")), "Unexpected rank-nine branch");
    }
    for (const r of [6, 7]) {
        let checked = 0;
        let tightest = -Infinity;
        for (const [edges, crossings] of raw.get(r)) {
            for (const crossing of crossings) {
                const [k, triangles] = crossing.split(",").map(Number);
                check(k === 3 && triangles < edges, "Unexpected ranks in residual branch");
                const maxFour = maximumFourCliques(order, r, edges, triangles);
                check(maxFour <= triangles, "Residual case not excluded");
                checked++;
                if (maxFour >= 0) tightest = Math.max(tightest, maxFour - triangles);
            }
        }
        console.log("Clique number", r, "| checked", checked, "| largest upper bound minus triangles", tightest);
    }
    console.log("Rank-five edge count", [...five.keys()]);
    console.log("Rank-nine edge counts", [...raw.get(9).keys()]);
    return raw;
}
main();
