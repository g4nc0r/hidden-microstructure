"""The model-chain results of Section 7.1 of the paper and Tables S1 and S2 of its supplement, at laptop scale.

    python3 reproduce.py            about four minutes
    python3 reproduce.py --quick    under a minute
    python3 reproduce.py --long     about half an hour, N up to 256

  1. mass at zero against q (Proposition 3), and the mean balances
  2. N Cov(B1, B2) and N Cov(H, B) against the Remark after Proposition 2; N rho against Table S2
  3. the Gaussian case at N = 1024 against the half-normal law (Table S1)
  4. the contraction rate against Lemma 2 (Table 3)

Standard errors are across 16 groups of chains. The paper's runs were longer, so agreement is within those errors.
"""
import argparse
import math
import time

import numpy as np

from kernel import Chains
from laws import LAWS, half_normal

SEED = 20261121
GROUPS = 16
# N rho_N from Table S2 (balances under the skewed law, squared balances under the uniform)
RECORDED = {
    'skewed': {2: -0.0201, 4: -0.0199, 8: -0.0199, 16: -0.0198, 32: -0.0199, 64: -0.0197, 128: -0.0198, 256: -0.0199},
    'uniform': {2: -0.0031, 4: -0.0030, 8: -0.0031, 16: -0.0032, 32: -0.0032, 64: -0.0032, 128: -0.0032, 256: -0.0034},
}

# N x contraction rate from Table 3, the range over N from 16 to 1024
RECORDED_RATE = {'gaussian': '0.98 to 1.08', 'uniform': '0.87 to 0.95', 'skewed': '0.92 to 1.11'}


def contraction(law, N, seed, cells=1 << 22):
    """Two ledgers under the same events, one empty and one at b*. Returns N times the decay rate of their mean
    l1 distance and its largest ratio to the bound of Lemma 2, both read while the distance is above 1e-4 of its
    start. Below that the mean rests on the few chains with a pool still unfired."""
    c = law.constants()
    C = cells // N
    a, b = Chains(C, N, law, seed), Chains(C, N, law, seed + 1)
    b.H[:] = c['b_star']; b.B[:] = c['b_star']
    d0 = (N + 1) * c['b_star']
    n_max = math.ceil(N * math.log(1e4) / (1 - c['kappa1']))
    every = max(1, N // 8)
    ns, dist = [], []
    for n in range(1, n_max + 1):
        marks = a.draw()
        a.step(marks); b.step(marks)
        if n % every == 0 or n == n_max:
            ns.append(n)
            dist.append((np.abs(a.H - b.H) + np.abs(a.B - b.B).sum(1)).mean() / d0)
    ns, dist = np.array(ns, dtype=float), np.array(dist)
    bound = np.exp(ns * math.log1p(-(1 - c['kappa1']) / N))
    seen = dist > 1e-4
    window = seen & (dist < 1e-1)
    rate = -np.polyfit(ns[window], np.log(dist[window]), 1)[0]
    return N * rate, float((dist[seen] / bound[seen]).max())


def stationary_moments(law, N, C, steps, seed):
    """Stationary estimates and their standard errors from C chains of N pools."""
    ch = Chains(C, N, law, seed)
    for _ in range(30 * N + 200):                      # burn-in: every spoke has fired
        ch.step()
    S1, S2, S4 = ch.B.sum(1), (ch.B ** 2).sum(1), (ch.B ** 4).sum(1)
    Z = (ch.B == 0).sum(1).astype(float)
    acc = {k: np.zeros(C) for k in ('H', 'S1', 'S2', 'S4', 'pairs', 'pairs_sq', 'HS1', 'Z')}
    for t in range(steps):
        k, Bk, Bn, Hn = ch.step()
        S1 += Bn - Bk
        S2 += Bn ** 2 - Bk ** 2
        S4 += Bn ** 4 - Bk ** 4
        Z += (Bn == 0).astype(float) - (Bk == 0)
        if t % 4096 == 4095:                           # recompute against rounding drift
            S1, S2, S4 = ch.B.sum(1), (ch.B ** 2).sum(1), (ch.B ** 4).sum(1)
        acc['H'] += Hn; acc['S1'] += S1; acc['S2'] += S2; acc['S4'] += S4; acc['Z'] += Z
        acc['pairs'] += S1 * S1 - S2                   # sum of B_i B_j over i != j
        acc['pairs_sq'] += S2 * S2 - S4                # the same for squared balances
        acc['HS1'] += Hn * S1

    def estimates(rows):
        m = {k: v[rows].mean() / steps for k, v in acc.items()}
        b, h, b2 = m['S1'] / N, m['H'], m['S2'] / N
        var = b2 - b * b
        cov_bb = m['pairs'] / (N * (N - 1)) - b * b
        cov_sq = m['pairs_sq'] / (N * (N - 1)) - b2 * b2
        var_sq = m['S4'] / N - b2 * b2
        return dict(atom=m['Z'] / N, h=h, b=b, cov_bb=cov_bb, cov_hb=m['HS1'] / N - h * b,
                    rho=cov_bb / var, rho_sq=cov_sq / var_sq)

    full = estimates(slice(None))
    parts = [estimates(g) for g in np.array_split(np.arange(C), GROUPS)]
    se = {k: np.std([p[k] for p in parts], ddof=1) / np.sqrt(GROUPS) for k in full}
    return full, se


def slack_side(law, N, C, steps, seed):
    """Non-zero spoke balances after the spoke's own event, and the share of events leaving zero."""
    ch = Chains(C, N, law, seed)
    for _ in range(20 * N):
        ch.step()
    out, zeros, total = [], 0, 0
    for _ in range(steps):
        _, _, Bn, _ = ch.step()
        out.append(Bn[Bn > 0])
        zeros += int((Bn == 0).sum()); total += Bn.size
    return np.concatenate(out), zeros / total


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('--quick', action='store_true')
    ap.add_argument('--long', action='store_true')
    a = ap.parse_args()
    C, steps, sizes = (2048, 20_000, (2, 8, 32)) if a.quick else (4096, 200_000, (2, 4, 8, 16, 32, 64, 128, 256)) \
        if a.long else (4096, 40_000, (2, 4, 8, 16, 32, 64))
    t0 = time.time()

    print('1. Mass at zero and mean balances (Lw = 1, c0 = 1); standard errors in brackets\n')
    print(f"{'law':9s} {'N':>4s}  {'P(B = 0)':>18s} {'q':>7s}  {'mean spoke':>19s} {'exact':>8s}  {'mean hub':>19s} {'exact':>8s}")
    results = {}
    for name in ('gaussian', 'uniform', 'skewed'):
        law, c = LAWS[name], LAWS[name].constants()
        for N in sizes:
            est, se = stationary_moments(law, N, C, steps, SEED + 1000 * N + len(name))
            results[name, N] = (est, se)
            print(f"{name:9s} {N:4d}  {est['atom']:.5f} ({se['atom']:.5f}) {c['q']:7.4f}  "
                  f"{est['b']:.6f} ({se['b']:.6f}) {c['b_bar']:8.5f}  {est['h']:.6f} ({se['h']:.6f}) {c['h_bar']:8.5f}")

    print('\n2. Dependence between balances, each times N\n')
    print(f"{'law':9s} {'N':>4s}  {'N Cov(B1,B2)':>21s} {'exact':>10s}  {'N Cov(H,B)':>21s} {'exact':>10s}  "
          f"{'N rho':>17s} {'Table S2':>9s}")
    for name in ('gaussian', 'uniform', 'skewed'):
        law = LAWS[name]
        for N in sizes:
            est, se = results[name, N]
            ebb, ehb = law.exact_covariances(N)
            key = 'rho_sq' if name == 'uniform' else 'rho'
            rec = RECORDED.get(name, {}).get(N)
            print(f"{name:9s} {N:4d}  {N * est['cov_bb']:+.6f} ({N * se['cov_bb']:.6f}) {N * ebb:+10.6f}  "
                  f"{N * est['cov_hb']:+.6f} ({N * se['cov_hb']:.6f}) {N * ehb:+10.6f}  "
                  f"{N * est[key]:+.4f} ({N * se[key]:.4f}) {'' if rec is None else format(rec, '+9.4f')}")
    print('\n   N rho: correlation of two spoke balances; of their squares under the uniform law, as in Table S2.')

    print('\n3. The Gaussian case at N = 1024 against the half-normal law of scale 0.05 (Table S1)\n')
    x, zero_share = slack_side(LAWS['gaussian'], 1024, 4096, 400 if a.quick else 2000, SEED + 7)
    mean, var, quantile = half_normal(0.05)
    rows = [('P(b = 0)', zero_share, 0.5), ('E[b | b > 0]', x.mean(), mean), ('Var(b | b > 0)', x.var(), var)]
    rows += [(f'quantile {p:.2f}', float(np.quantile(x, p)), quantile(p)) for p in (0.10, 0.25, 0.50, 0.75, 0.90)]
    print(f"{'quantity':16s} {'simulated':>11s} {'closed form':>12s} {'ratio':>7s}")
    for label, sim, exact in rows:
        print(f"{label:16s} {sim:11.4e} {exact:12.4e} {sim / exact:7.4f}")
    print(f'\n   {x.size:,} non-zero balances.')

    print('\n4. Contraction of two ledgers under the same events (Lemma 2 and Table 3 of the paper)\n')
    print(f"{'law':9s} {'N':>4s}  {'N x rate':>9s} {'1 - kappa1':>11s} {'largest distance / bound':>25s}  {'Table 3, N x rate':>18s}")
    for name in ('gaussian', 'uniform', 'skewed'):
        law = LAWS[name]
        for N in (16, 64, 256):
            rate, worst = contraction(law, N, SEED + 31 * N, cells=1 << 20 if a.quick else 1 << 22)
            print(f"{name:9s} {N:4d}  {rate:9.3f} {1 - law.constants()['kappa1']:11.3f} {worst:25.3f}  {RECORDED_RATE[name]:>18s}")
    print('\n   Lemma 2: the mean distance is at most (1 - (1 - kappa1) / N)^n, so N x rate >= 1 - kappa1.')
    print(f'\nDone in {time.time() - t0:.0f} s.')


if __name__ == '__main__':
    main()
