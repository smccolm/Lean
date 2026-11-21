"""Check Robin's and Lagarias's inequalities using exact sums and decimal intervals."""

import json
import math
from decimal import Decimal, getcontext
from pathlib import Path
from time import monotonic


def loglog_lower(n):
    return Decimal(n).ln().next_minus().ln().next_minus()


def loglog_upper(n):
    return Decimal(n).ln().next_plus().ln().next_plus()


def main():
    getcontext().prec = 45
    start = monotonic()
    limit = 1_000_000
    sigma = [0] * (limit + 1)
    for divisor in range(1, limit + 1):
        for n in range(divisor, limit + 1, divisor):
            sigma[n] += divisor

    # Integral bounds on the tail give H_m - log(m) - 1/m < gamma < H_m - log(m).
    m = 65_536
    harmonic_lower = harmonic_upper = Decimal(0)
    lagarias_direct = 0
    assert sigma[1] == 1  # H_1 = 1, log(1) = 0, hence equality exactly.
    for n in range(1, m + 1):
        step = Decimal(1) / n
        harmonic_lower = (harmonic_lower + step.next_minus()).next_minus()
        harmonic_upper = (harmonic_upper + step.next_plus()).next_plus()
        if 2 <= n <= 5040:
            product_lower = harmonic_lower.exp().next_minus() * harmonic_lower.ln().next_minus()
            rhs_lower = (harmonic_lower + product_lower.next_minus()).next_minus()
            assert sigma[n] < rhs_lower, n
            lagarias_direct += 1
    gamma_lower = ((harmonic_lower - Decimal(m).ln().next_plus()).next_minus()
                   - (Decimal(1) / m).next_plus()).next_minus()
    gamma_upper = (harmonic_upper - Decimal(m).ln().next_minus()).next_plus()
    assert gamma_lower > 0
    exp_gamma_lower = gamma_lower.exp().next_minus()
    exp_gamma_upper = gamma_upper.exp().next_plus()
    at_cutoff_upper = (Decimal(5040) * (exp_gamma_upper * loglog_upper(5040)).next_plus()).next_plus()
    assert sigma[5040] > at_cutoff_upper

    # Float arithmetic proposes a maximizer. The interval checks below certify the
    # candidate beats every other integer, independent of how it was selected.
    candidate = max(range(5041, limit + 1),
                    key=lambda n: sigma[n] / n / math.log(math.log(n)))
    density = Decimal(sigma[candidate]) / candidate
    ratio_lower = (density.next_minus() / loglog_upper(candidate)).next_minus()
    ratio_upper = (density.next_plus() / loglog_lower(candidate)).next_plus()
    assert ratio_upper < exp_gamma_lower
    blocks = 0
    certified = 1

    def certify(first, last):
        nonlocal blocks, certified
        best = first
        for n in range(first + 1, last + 1):
            if sigma[n] * best > sigma[best] * n:
                best = n
        density_upper = (Decimal(sigma[best]) / best).next_plus()
        threshold = (ratio_lower * loglog_lower(first)).next_minus()
        if density_upper < threshold:
            blocks += 1
            certified += last - first + 1
        elif first == last:
            raise ArithmeticError(f"Unable to certify the proposed maximizer against {first}")
        else:
            middle = (first + last) // 2
            certify(first, middle)
            certify(middle + 1, last)

    for first, last in [(5041, candidate - 1), (candidate + 1, limit)]:
        for n in range(first, last + 1, 256):
            certify(n, min(n + 255, last))
    assert certified == limit - 5040

    # For n > 5040, H_n > log(n) + gamma and gamma > 0 imply
    # e^(H_n) log(H_n) > n e^gamma log(log(n)), so Robin implies Lagarias here.
    record = {
        "precision_decimal_digits": getcontext().prec,
        "gamma_from_H_m": m,
        "gamma_lo": str(gamma_lower),
        "gamma_hi": str(gamma_upper),
        "robin_range": [5041, limit],
        "robin_integers_checked": certified,
        "certified_blocks_excluding_maximizer": blocks,
        "maximum_sigma_over_n_loglog_n": {
            "n": candidate,
            "sigma": sigma[candidate],
            "ratio_lower": str(ratio_lower),
            "ratio_upper": str(ratio_upper),
            "fraction_of_robin_rhs_lower": str((ratio_lower / exp_gamma_upper).next_minus()),
            "fraction_of_robin_rhs_upper": str((ratio_upper / exp_gamma_lower).next_plus()),
        },
        "robin_at_5040": {"sigma": sigma[5040], "upper_bound_for_rhs": str(at_cutoff_upper)},
        "lagarias_at_1": "exact equality",
        "lagarias_direct_strict_checks": lagarias_direct,
        "lagarias_by_robin": [5041, limit],
        "elapsed_seconds": round(monotonic() - start, 2),
    }
    print(json.dumps(record, indent=2))
    Path(__file__).with_name("finite-checks.json").write_text(
        json.dumps(record, indent=2) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
