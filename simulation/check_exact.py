"""The float64 kernel against exact rational arithmetic. On the exact path, at every event:

  - one of the two touched entries is zero, the spoke's exactly when eta eps >= 0;
  - every balance is at most b* = K Lw / (1 - K) and the imbalance is positive;
  - for two ledgers under the same event, the l1 distance over the touched entries is |eps| times the
    difference of their imbalances (the identity behind Lemma 2).
"""
import random
from fractions import Fraction as F

import numpy as np

from kernel import Chains, exact_event
from laws import LAWS

N, EVENTS, SEED = 5, 4_000, 20261121


def main():
    rnd = random.Random(SEED)
    law = LAWS['skewed']
    K = F(3, 10)
    b_star = K / (1 - K)
    Lw = F(1)
    # two ledgers under the same events, one starting empty
    H = [F(0), F(1, 7)]
    B = [[F(0)] * N, [F(k + 1, 20) for k in range(N)]]
    ch = Chains(1, N, law, SEED)
    worst = 0.0
    for _ in range(EVENTS):
        k = rnd.randrange(N)
        eta = 1 if rnd.random() < 0.5 else -1
        lo, hi = (F(-2, 100), F(30, 100)) if eta > 0 else (F(-25, 100), F(25, 100))
        eps = lo + (hi - lo) * F(rnd.randrange(10 ** 6 + 1), 10 ** 6)
        A = [Lw + eta * (B[i][k] - H[i]) for i in range(2)]
        assert A[0] > 0 and A[1] > 0, 'imbalance not positive'
        new = [exact_event(Lw, H[i], B[i][k], eta, eps) for i in range(2)]
        for h, b in new:
            assert h == 0 or b == 0, 'both entries non-zero'
            assert (b == 0) == (eta * eps >= 0), 'side rule'
            assert h <= b_star and b <= b_star, 'bound b* exceeded'
        assert abs(new[0][0] - new[1][0]) + abs(new[0][1] - new[1][1]) == abs(eps) * abs(A[0] - A[1]), 'l1 identity'
        for i in range(2):
            H[i], B[i][k] = new[i]
        # float kernel, same marks, against the first ledger
        ch.step((np.array([k]), np.array([float(eta)]), np.array([float(eps)])))
        worst = max(worst, abs(ch.H[0] - float(H[0])), max(abs(ch.B[0, j] - float(B[0][j])) for j in range(N)))
    assert worst < 1e-12, worst
    gap = abs(H[0] - H[1]) + sum(abs(x - y) for x, y in zip(B[0], B[1]))
    print(f'{EVENTS:,} events, N = {N}: side rule, bound b* and the l1 identity hold exactly at every event;')
    assert gap > 0
    log2 = gap.numerator.bit_length() - gap.denominator.bit_length()
    print(f'float64 kernel within {worst:.1e} of the exact ledger; the two ledgers, 0.89 apart at the start, '
          f'end about 2^{log2} apart.')


if __name__ == '__main__':
    main()
