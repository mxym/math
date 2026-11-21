// Run with node. All quadrature enclosures are integers with explicit rounding.
const scale = 10n ** 14n;
const piLower = 314159265358970n;
const piMid = 314159265358980n;
const piUpper = 314159265358990n;
const stepDenominator = 40n;
const powerScale = 10n ** 6n;
const ceil = (a, b) => (a + b - 1n) / b;
const abs = n => n < 0n ? -n : n;
const factorial = [1n];
for (let j = 1; j <= 65; j++) factorial.push(factorial[j - 1] * BigInt(j));
function upperPower(j) {
    const numerator = 689n * BigInt(j + 1);
    const denominator = 310n * stepDenominator;
    if (numerator <= denominator) return powerScale;
    const target = numerator ** 51n * powerScale ** 40n;
    const factor = denominator ** 51n;
    let low = powerScale;
    let high = 10_000_000_000n;
    while (high - low > 1n) {
        const mid = (low + high) / 2n;
        if (mid ** 40n * factor >= target) high = mid;
        else low = mid;
    }
    return high;
}
let sum = 0n;
for (let j = 0; j < 800; j++) {
    const center = BigInt(2 * j + 1) * scale / (2n * stepDenominator);
    const arg = (center - piMid) / 2n;
    const square = arg * arg;
    const scaleSquare = scale * scale;
    let numerator = 1n;
    let denominator = 1n;
    let sinc = 0n;
    let sincDerivative = 0n;
    for (let k = 0; k < 24; k++) {
        const sign = k % 2 ? -1n : 1n;
        const termDenominator = denominator * factorial[2 * k + 1];
        sinc += sign * (numerator * scale / termDenominator);
        if (k > 0)
            sincDerivative += sign * (numerator * BigInt(2 * k) * scaleSquare / (termDenominator * arg));
        numerator *= square;
        denominator *= scaleSquare;
    }
    const localSincUpper = abs(sinc) + scale / (8n * stepDenominator) + 10000n;
    const upperSinc = localSincUpper < scale ? localSincUpper : scale;
    const upperDerivative = abs(sincDerivative) + ceil(scale, 12n * stepDenominator) + 10000n;
    const den = BigInt(j) * scale / stepDenominator + piLower;
    const G = ceil(2n * piUpper ** 2n * upperSinc ** 2n, den ** 2n * scale);
    const Gprime =
        ceil(2n * piUpper ** 2n * upperSinc * upperDerivative, den ** 2n * scale) +
        ceil(4n * piUpper ** 2n * upperSinc ** 2n, den ** 3n);
    const W = ceil((100n * G + 31n * Gprime) * scale, 100n * piLower);
    const envelope = ceil(10000n * upperPower(j) * scale, 679n * powerScale);
    sum += ceil(W * envelope, stepDenominator * scale);
}
if (sum * 1000n >= 167751n * scale) throw new Error("Quadrature bound failed");
if (689n ** 51n >= 3n ** 40n * 310n ** 51n) throw new Error("Tail exponent bound failed");
if (20n ** 69n * (8n * 69n) ** 40n <= (2250n * 40n) ** 40n)
    throw new Error("Tail integral bound failed");
process.stdout.write("Certified integral on [0,20] below 167.751, tail below 8.\n");
