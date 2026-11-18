# Flatness in a complete Pauli MUB through four logical qubits

A pure state is *flat on a support* if the nonzero outcome probabilities of that measurement are all equal. The [conjecture of Klimov, Muñoz and Sainz](https://arxiv.org/html/2610.10471v2) asks whether flatness in every basis of **one complete stabilizer MUB** characterizes stabilizer states for any number of qubits.

**Partial result.** Let the stabilizer nullity be the number of qubits minus the binary dimension of the state's Pauli stabilizer subgroup (ignoring scalar phases). At nullity at most four, flatness in every basis of one complete stabilizer MUB forces a pure state to be a stabilizer state. The same conclusion holds for the positive-weight contexts of any fractional cover of the nonidentity Pauli labels by maximal commuting Pauli groups. The nullity bound applies after eliminating all stabilizer qubits: the ambient number of qubits is unrestricted. The proof through three logical qubits is analytic; the fourth uses a finite certificate.

For an **actual complete spread**, whether or not the nullity is small, there are further restrictions: an odd-sized support must be a singleton; the bitwise sum (XOR) of the support is zero whenever its size is divisible by four; and each prime congruent to 3 modulo 4 occurs in all support sizes to the same exponent. Support labels here are the binary characters of the measured commuting group, not an arbitrary relabeling. Together the results show that a nonstabilizer counterexample, if one exists, must have nullity at least five and even support size at least eight in every measured basis.

**What is not proved.** This is not a resolution in unrestricted nullity. The authors of the conjecture already establish the affine-support branch and the cases of one and two qubits, exclude three-point supports in all dimensions, and explicitly discuss an extension to three qubits without giving its full derivation. No first-result claim is made for three qubits. The result for all Clifford measurements, rather than one complete set of bases, has a different hypothesis. See the [literature and scope](STATUS.md) and [internal audit](REVIEW.md).

**中文摘要。** 对同一组完整稳定子互无偏基，如果每次测量的非零概率都相等，那么稳定子零度不超过四的纯态一定是稳定子态。前三个逻辑比特有解析证明，第四个使用两套独立的整数枚举。不限零度的原猜想仍未解决。

### Proof and reproducibility

1. [Logical reduction and three-qubit argument](THREE.md): quotient by the stabilizers, obtain a fractional cover, and exclude the remaining three-qubit support by Pauli incidence counts.
2. [Four logical qubits](FOUR.md): reduce phases and supports to eight affine support orbits and 4,223,337 parameter patterns. Exactly 225 survive the first screen. A missing Pauli label excludes 217 immediately; one forced context exposes a missing label in each of the other eight.
3. [Arithmetic for a single complete spread](ARITHMETIC.md): derive the parity, XOR and prime-valuation statements.
4. [Independent verification](REVIEW.md): the second implementation uses an orbit traversal and actual eigenbras rather than the first implementation's inverse Walsh transform. It checks 2,295 contexts and matches the individual surviving parameter tuples.

Run both exact implementations on Linux with Python 3.10+, NumPy, a C++20 compiler, GNU coreutils and a POSIX shell, from this directory:

```sh
sha256sum -c SHA256SUMS
sh replay.sh
```

The script compiles in a temporary directory, compares the original certificate byte-for-byte, compares the two independently generated survivor lists as sets of integer tuples, and tests both cover exclusions. It does not access the network.

The arguments, code and checks were developed with AI assistance. The separate technical audit was an internal AI review, not independent human peer review or formal proof verification. Literature searches do not establish historical priority. Third-party works are cited for their own results; no third-party paper or source code is reproduced or relicensed by this note.
