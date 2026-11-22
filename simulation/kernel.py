"""The hub-spoke kernel of Section 6 of the paper.

H is the ledger entry of the hub token and B[k] that of spoke k. An event of pool k in direction eta with residual
eps has imbalance

    A = Lw + eta * (B[k] - H)

and leaves c0 * |A| * |eps| on the hub if eta * A * eps > 0, on the spoke otherwise. The other of the two entries
becomes zero and no other entry changes. The paper has c0 = 1.
"""
import numpy as np


class Chains:
    """C independent copies of the N-pool chain, started from an empty ledger."""

    def __init__(self, C, N, law, seed, Lw=1.0, c0=1.0):
        self.C, self.N, self.law, self.Lw, self.c0 = C, N, law, Lw, c0
        self.rng = np.random.default_rng(seed)
        self.H = np.zeros(C)
        self.B = np.zeros((C, N))
        self._rows = np.arange(C)

    def draw(self):
        """Firing pool, direction and residual of one event in every chain."""
        k = self.rng.integers(0, self.N, self.C)
        eta = np.where(self.rng.random(self.C) < self.law.p_plus, 1.0, -1.0)
        eps = self.law.sample(eta, self.rng)
        return k, eta, eps

    def step(self, marks=None):
        """One event in every chain. Returns (k, old spoke entry, new spoke entry, new hub entry)."""
        k, eta, eps = self.draw() if marks is None else marks
        Bk = self.B[self._rows, k]
        A = self.Lw + eta * (Bk - self.H)
        u = self.c0 * eta * A * eps
        Hn = np.maximum(u, 0.0)
        Bn = np.maximum(-u, 0.0)
        self.B[self._rows, k] = Bn
        self.H = Hn
        return k, Bk, Bn, Hn


def exact_event(Lw, h, b, eta, eps, c0=1):
    """The same rule on Fractions. Returns the new hub and spoke entries."""
    A = Lw + eta * (b - h)
    left = c0 * abs(A) * abs(eps)
    if eta * A * eps > 0:
        return left, 0 * left
    return 0 * left, left
