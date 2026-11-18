"""Check the seven-grid contradiction by enumerating residual matrix rows over Z."""

from itertools import product


def rank_mod_three(rows):
    basis = {}
    for row in rows:
        vector = list(row)
        for index in range(len(vector)):
            lead = vector[index]
            if lead == 0:
                continue
            if index not in basis:
                # Both nonzero scalars of F_3 are their own inverse.
                basis[index] = [(lead * x) % 3 for x in vector]
                break
            vector = [(x - lead * y) % 3 for x, y in zip(vector, basis[index])]
    return len(basis)


def cycle_partitions(total, minimum=3):
    if total == 0:
        yield ()
    for length in range(minimum, total + 1):
        if length != 4:
            for tail in cycle_partitions(total - length, length):
                yield (length,) + tail


def count_completions(cycles):
    size = 12
    matrix = [[0] * size for _ in range(size)]
    offset = 0
    for length in cycles:
        for k in range(length):
            i = offset + k
            j = offset + (k + 1) % length
            matrix[i][j] = matrix[j][i] = 2
        offset += length
    for i in range(offset, size):
        matrix[i][i] = 2

    def admissible(last):
        present = range(last + 1)
        for i in present:
            # Every later entry is undecided (0 or 1) or is a prescribed 2.
            missing = 7 - sum(matrix[i])
            unassigned = sum(x != 2 for x in matrix[i][last + 1 :])
            if not 0 <= missing <= unassigned:
                return False
            for j in range(i):
                paths = sum(matrix[i][k] * matrix[j][k] for k in present)
                if paths + matrix[i][j] > 6:
                    return False

        def h(i, j):
            return matrix[i][j] + (i == j)

        gram = [
            [(h(i, j) - h(i, 0) - h(j, 0) + h(0, 0)) % 3 for j in range(1, last + 1)]
            for i in range(1, last + 1)
        ]
        rank = rank_mod_three(gram)
        if rank > 4:
            return False
        if rank == 4:
            # The points span the entire nondegenerate four-space.
            # Pairings against a spanning family distinguish them, including the origin.
            signatures = {tuple(row) for row in gram}
            signatures.add((0,) * last)
            if len(signatures) != last + 1:
                return False
        return True

    def extend(i):
        if i == size:
            return 1
        free = [j for j in range(i) if matrix[i][j] != 2]
        count = 0
        for values in product((0, 1), repeat=len(free)):
            for j, value in zip(free, values):
                matrix[i][j] = matrix[j][i] = value
            if admissible(i):
                count += extend(i + 1)
        for j in free:
            matrix[i][j] = matrix[j][i] = 0
        return count

    return extend(0)


if __name__ == "__main__":
    for total in (6, 9, 12):
        for cycles in cycle_partitions(total):
            count = count_completions(cycles)
            print(f"{cycles}  {count}", flush=True)
            if count:
                raise SystemExit("A residual matrix survived the stated necessary conditions.")
