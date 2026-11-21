"""Exact eigenprojections, seed capacities and weight-22 coefficient identity."""
from fractions import Fraction as Q
from itertools import combinations, product
from pathlib import Path
import runpy

previous = Path(__file__).resolve().parents[1] / "rank-34-short-support" / "verify.py"
arithmetic = runpy.run_path(str(previous))
series, multiply = arithmetic["series"], arithmetic["multiply"]
pairs = list(combinations(range(4), 2))


def projection_energy(chosen, all_six):
    labels = list(range(6)) if all_six else list(chosen)
    n = 14 + len(labels)
    edges = {(i, i + 1) for i in range(0, 14, 2)}
    for i, label in enumerate(labels, 14):
        edges.update((2*a, i) for a in pairs[label])
    values = [-int(i in (0, 2, 4, 6)) for i in range(14)]
    values.extend(int(label in chosen) for label in labels)
    # 63 E = 27 I - 9 A + J. Solve (63 E) u = values.
    matrix = [[Q(27*int(i == j) - 9*int(tuple(sorted((i, j))) in edges) + 1)
               for j in range(n)] + [Q(values[i])] for i in range(n)]
    for i in range(n):
        pivot = next(j for j in range(i, n) if matrix[j][i])
        matrix[i], matrix[pivot] = matrix[pivot], matrix[i]
        matrix[i] = [v/matrix[i][i] for v in matrix[i]]
        for j in range(n):
            if j != i and matrix[j][i]:
                factor = matrix[j][i]
                matrix[j] = [v-factor*w for v, w in zip(matrix[j], matrix[i])]
    return 63*sum(v*r[-1] for v, r in zip(values, matrix))


def seed_bounds():
    by_type = {}
    for chosen in [(0, 1, 2, 3), (0, 1, 4, 5), (0, 1, 2, 3, 4), tuple(range(6))]:
        missing = set(range(6)) - set(chosen)
        hits = {a for i in missing for a in pairs[i]}
        key = (len(chosen), len(hits))
        delta = 14 if len(hits) == 4 else 16
        energies = [projection_energy(chosen, all_six) for all_six in (True, False)]
        by_type[key] = tuple(int(delta/(delta-36+2*d)) for d in energies)
        print(key, *map(str, energies), by_type[key])
    assert by_type == {(4, 3): (2, 4), (4, 4): (5, 12),
                       (5, 2): (2, 3), (6, 0): (2, 2)}
    caps = []
    for edge in ((), (0, 1), (0, 5)):
        total = 0
        for size in (4, 5, 6):
            for chosen in combinations(range(6), size):
                if edge and set(edge) <= set(chosen):
                    continue
                hits = {a for i in range(6) if i not in chosen for a in pairs[i]}
                total += by_type[size, len(hits)][bool(edge)]
        caps.append(total)
    assert caps == [53, 58, 50]
    assert 99*560*max(caps)//9 == 357280


def theta_bound():
    correction = (-78795448739, -28040798234, -9508092231, -3043912550,
                  -908471795, -248073595, -60256182)
    for a, left, right in product(range(3, 12, 2), (False, True), (False, True)):
        b = 22-a
        x = multiply(series(a, left), series(b, right))
        scale = Q(7)**(6 + (2*left-1)*((a-1)//2) + (2*right-1)*((b-1)//2))
        y = [scale*v for v in multiply(series(a, not left), series(b, not right))]
        lhs = 12343996*x[7] + 1922857*x[8] + 135344*x[9]
        rhs = 22827*x[10] + 8987*x[11] + 9440291*y[2] + 962507*y[3] + 40082*y[4]
        assert lhs == rhs + sum(c*v for c, v in zip(correction, x)) - 1479919805*y[0]
    constant = correction[0]-1479919805
    rhs = constant + 9440291*462 + 962507*41058 + 40082*3156588
    # Use the real-valued relaxation of the even integer packing bounds.
    cap = Q(12343996)*990 + Q(1922857, 8)*(77616+24*851-14*990)
    assert 12343996 > Q(14*1922857, 8)
    lower = (rhs-cap)/135344
    assert lower == Q(115346399395, 270688) and 426122 < lower < 426124
    print("Rank 34 requires N18 >= 426124; every graph has N18 <= 357280")


if __name__ == "__main__":
    arithmetic["verify_modular_relation"]()
    seed_bounds()
    theta_bound()
