"""Residual laws of Section 7.1 of the paper, with their exact constants.

    gaussian   eps ~ N(0, 0.05^2) conditioned to [-0.45, 0.45], in both directions
    uniform    eps ~ U[-0.45, 0.45], in both directions
    skewed     eps ~ U[-0.02, 0.30] when eta = +1, U[-0.25, 0.25] when eta = -1

The paper's measured law is not published. With c0 = 1, u+ = max(u, 0) and u- = max(-u, 0):

    q        = P(eta eps >= 0)        mass at zero of a spoke's balance (Proposition 3)
    kappa1   = E|eps|                 contraction rate of Lemma 2
    gamma+-  = E[(eta eps)+-]         mean leftover reaching the hub (+) and the spoke (-)
    chi+-    = E[(eta eps)+- eta]     enter the exact means and covariances (Remark after Proposition 2)
"""
import math
from dataclasses import dataclass
from statistics import NormalDist

import numpy as np


@dataclass(frozen=True)
class Uniform:
    lo: float
    hi: float

    def sample(self, n, rng):
        return self.lo + (self.hi - self.lo) * rng.random(n)

    def moments(self):
        """P(eps >= 0), P(eps <= 0), E[eps+], E[eps-], sup|eps|."""
        lo, hi, L = self.lo, self.hi, self.hi - self.lo
        pos = (max(hi, 0) ** 2 - max(lo, 0) ** 2) / (2 * L)
        neg = (min(lo, 0) ** 2 - min(hi, 0) ** 2) / (2 * L)
        return (max(hi, 0) - max(lo, 0)) / L, (min(hi, 0) - min(lo, 0)) / L, pos, neg, max(abs(lo), abs(hi))


@dataclass(frozen=True)
class TruncatedGaussian:
    sd: float
    cut: float

    def sample(self, n, rng):
        x = self.sd * rng.standard_normal(n)
        bad = np.abs(x) > self.cut
        while bad.any():
            x[bad] = self.sd * rng.standard_normal(int(bad.sum()))
            bad = np.abs(x) > self.cut
        return x

    def moments(self):
        t = self.cut / self.sd
        mass = math.erf(t / math.sqrt(2))
        half = self.sd * (1 - math.exp(-t * t / 2)) / math.sqrt(2 * math.pi) / mass
        return 0.5, 0.5, half, half, self.cut


@dataclass(frozen=True)
class Law:
    name: str
    p_plus: float
    plus: object     # law of eps when eta = +1
    minus: object    # law of eps when eta = -1

    def sample(self, eta, rng):
        n = eta.size
        return np.where(eta > 0, self.plus.sample(n, rng), self.minus.sample(n, rng))

    def constants(self, Lw=1.0):
        """Exact constants and stationary mean balances (c0 = 1)."""
        pp, pm = self.p_plus, 1 - self.p_plus
        ge_p, le_p, pos_p, neg_p, sup_p = self.plus.moments()
        ge_m, le_m, pos_m, neg_m, sup_m = self.minus.moments()
        K = max(sup_p, sup_m)
        gamma_plus = pp * pos_p + pm * neg_m       # E[(eta eps)+]
        gamma_minus = pp * neg_p + pm * pos_m      # E[(eta eps)-]
        chi_plus = pp * pos_p - pm * neg_m         # E[(eta eps)+ eta]
        chi_minus = pp * neg_p - pm * pos_m        # E[(eta eps)- eta]
        # means: h = gamma+ Lw + chi+ (b - h),  b = gamma- Lw + chi- (b - h)
        gap = (gamma_minus - gamma_plus) * Lw / (1 - chi_minus + chi_plus)
        return dict(q=pp * ge_p + pm * le_m, K=K, kappa1=gamma_plus + gamma_minus, b_star=K * Lw / (1 - K),
                    gamma_plus=gamma_plus, gamma_minus=gamma_minus, chi_plus=chi_plus, chi_minus=chi_minus,
                    h_bar=gamma_plus * Lw + chi_plus * gap, b_bar=gamma_minus * Lw + chi_minus * gap)

    def exact_covariances(self, N, Lw=1.0):
        """Stationary Cov(B_1, B_2) and Cov(H, B_1) at N pools (Remark after Proposition 2)."""
        c = self.constants(Lw)
        den = 1 - c['chi_minus'] + (1 - 1 / N) * c['chi_plus']
        scale = c['h_bar'] * c['b_bar'] / N
        return scale * c['chi_minus'] / den, -scale * (1 - c['chi_minus']) / den


LAWS = {
    'gaussian': Law('gaussian', 0.5, TruncatedGaussian(0.05, 0.45), TruncatedGaussian(0.05, 0.45)),
    'uniform': Law('uniform', 0.5, Uniform(-0.45, 0.45), Uniform(-0.45, 0.45)),
    'skewed': Law('skewed', 0.5, Uniform(-0.02, 0.30), Uniform(-0.25, 0.25)),
}


def half_normal(sd):
    """Mean, variance and quantile function of the half-normal law of scale sd."""
    nd = NormalDist()
    return sd * math.sqrt(2 / math.pi), sd * sd * (1 - 2 / math.pi), lambda p: sd * nd.inv_cdf((1 + p) / 2)


if __name__ == '__main__':
    for name, law in LAWS.items():
        c = law.constants()
        print(f"{name:9s} q = {c['q']:.4f}  kappa1 = {c['kappa1']:.4f}  K = {c['K']:.2f}  b* = {c['b_star']:.4f}  "
              f"gamma+ = {c['gamma_plus']:.4f}  gamma- = {c['gamma_minus']:.4f}  "
              f"chi+ = {c['chi_plus']:+.4f}  chi- = {c['chi_minus']:+.4f}  h = {c['h_bar']:.5f}  b = {c['b_bar']:.5f}")
