"""Certify an integer-time readout law for P8. Requires numpy and mpmath."""

from itertools import combinations

import numpy as np
from mpmath import iv


TIMES = (2, 7, 10, 30, 31, 66, 78, 81, 90, 105, 119, 126, 130, 132, 148, 155, 159)
PAIRS = [(a, b) for a, b in combinations(range(1, 9), 2) if a + b <= 9]


def interval_dyadics(array):
    """Freeze numerical guesses as exact rationals with denominator 2**40."""
    scale = 2**40
    return iv.matrix([[iv.mpf(int(round(x * scale))) / scale for x in row] for row in array])


def upper_infinity_norm(matrix):
    return max(sum(abs(matrix[i, j]) for j in range(matrix.cols)).b for i in range(matrix.rows))


def main():
    iv.dps = 50
    energy = {a: 2 * iv.cos(iv.pi * a / 9) for a in range(1, 9)}
    moment_matrix = iv.matrix([[1] * len(TIMES)] + [
        [iv.cos((energy[a] - energy[b]) * t) for t in TIMES] for a, b in PAIRS
    ])
    target = iv.matrix([1] + [-0.125 if (a - b) % 2 == 0 else 0 for a, b in PAIRS])
    approximate = np.array([[float(x.mid) for x in row] for row in moment_matrix.tolist()])
    rhs = np.array(target.tolist(), dtype=float)
    preconditioner = interval_dyadics(np.linalg.inv(approximate))
    guess = interval_dyadics(np.linalg.solve(approximate, rhs))
    defect = upper_infinity_norm(iv.eye(len(TIMES)) - preconditioner * moment_matrix)
    residual = upper_infinity_norm(preconditioner * (target - moment_matrix * guess))
    assert defect < iv.mpf("1e-8")
    error = residual / (1 - defect)
    assert error < iv.mpf("1e-8")
    assert min(w.a for w in guess) - error > iv.mpf("0.02022")
    print("Certified: matrix invertible, every weight > 0.02022")
    print("Infinity-norm defect upper bound:", defect)
    print("Infinity-norm weight error upper bound:", error)
    print("time   weight (rounded)")
    for t, w in zip(TIMES, guess):
        print(f"{t:4d}   {float(w):.10f}")

    # Independent physical check in the site basis, using the adjacency matrix.
    adjacency = np.diag(np.ones(7), 1) + np.diag(np.ones(7), -1)
    energies, vectors = np.linalg.eigh(adjacency)
    average = np.zeros((8, 8))
    for t, w in zip(TIMES, guess):
        evolution = (vectors * np.exp(1j * t * energies)) @ vectors.T
        average += float(w) * abs(evolution)**2
    deviation = np.max(np.abs(average - 1 / 8))
    assert deviation < 1e-10
    print("Site-basis maximum absolute deviation (floating point):", deviation)


if __name__ == "__main__":
    main()
