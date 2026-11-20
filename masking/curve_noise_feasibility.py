"""Exact arithmetic for a conditional common-mass bound, not a Rocq security proof.

The bank must be independently canonically re-shared conditional on history and
its clear values at every observation. All stored secrets must be included.
Default bank: 255 scalar bits, previous bit, four coordinates, affine accumulator,
and 32 core slots. Public fields contribute a common offset. The default horizon
is illustrative; no masked Quartz implementation with that schedule is claimed.
"""

import argparse
from fractions import Fraction
import json
from math import comb
import unittest


def common_overlap(hw_width, word_noise):
    """Common mass of h + Binomial(word_noise, 1/2), for every h in 0..hw_width."""
    if hw_width < 0 or word_noise < 0:
        raise ValueError("HW range and noise count must be nonnegative")
    if hw_width == 0:
        return Fraction(1)
    if word_noise < hw_width:
        return Fraction(0)
    low = (word_noise - hw_width) // 2 + 1
    high = (word_noise + hw_width) // 2
    coefficient = comb(word_noise, low)
    mass = coefficient
    for k in range(low, high):
        coefficient = coefficient * (word_noise - k) // (k + 1)
        mass += coefficient
    return 1 - Fraction(mass, 1 << word_noise)


def round_up_dyadic(value, precision):
    if precision < 1 or value < 0:
        raise ValueError("precision must be positive and value nonnegative")
    denominator = 1 << precision
    numerator = (value.numerator * denominator + value.denominator - 1) // value.denominator
    return Fraction(numerator, denominator)


def ceil_log2(value):
    if value <= 0:
        raise ValueError("logarithm requires a positive value")
    exponent = value.numerator.bit_length() - value.denominator.bit_length()
    if value > Fraction(2) ** exponent:
        exponent += 1
    return exponent


def allocate_noise(total_noise, bank, shares):
    if total_noise < 0 or bank < 1 or shares < 1:
        raise ValueError("noise must be nonnegative; bank and shares must be positive")
    return divmod(total_noise, bank * shares)


def certificate(hw_width, bank, shares, total_noise, snapshots, repetitions, precision=80):
    if snapshots < 0 or repetitions < 0:
        raise ValueError("snapshots and repetitions must be nonnegative")
    word_noise, remainder = allocate_noise(total_noise, bank, shares)
    alpha = common_overlap(hw_width, word_noise)
    delta_upper = round_up_dyadic(1 - alpha, precision)
    bound = repetitions * snapshots * bank * delta_upper ** shares
    capped = min(Fraction(1), bound)
    exponent = ceil_log2(capped) if capped else None
    return {
        "hw_range": [0, hw_width],
        "bank_values": bank,
        "shares_per_value": shares,
        "stored_field_words": bank * shares,
        "total_noise_bits_per_snapshot": total_noise,
        "noise_bits_per_word": word_noise,
        "remaining_aggregate_noise_bits": remainder,
        "snapshots": snapshots,
        "independent_repetitions": repetitions,
        "dyadic_precision_bits": precision,
        "common_overlap_zero": alpha == 0,
        "delta_upper": {
            "numerator": delta_upper.numerator,
            "denominator": delta_upper.denominator,
        },
        "composition_upper_at_least_one": bound >= 1,
        "conditional_TV_upper_certificate": "0" if not capped else f"2^{exponent}",
        "status": "No improvement over TV <= 1" if exponent == 0 else "Conditional upper bound",
    }


class Checks(unittest.TestCase):
    def test_overlap_against_direct_minimum(self):
        for width in range(7):
            for noise in range(9):
                def mass(k):
                    return comb(noise, k) if 0 <= k <= noise else 0

                direct = Fraction(sum(min(mass(y - h) for h in range(width + 1))
                                      for y in range(noise + width + 1)), 1 << noise)
                self.assertEqual(common_overlap(width, noise), direct)

    def test_disjoint_support_and_boundary(self):
        for width in range(1, 12):
            for noise in range(width):
                self.assertEqual(common_overlap(width, noise), 0)
            self.assertEqual(common_overlap(width, width), Fraction(1, 1 << width))
        self.assertEqual(common_overlap(1, 1), Fraction(1, 2))

    def test_fixed_total_allocation(self):
        for total in (0, 8, 100, 1000):
            for bank in (1, 3, 293):
                for shares in (1, 2, 4, 64):
                    word, extra = allocate_noise(total, bank, shares)
                    self.assertEqual(word * bank * shares + extra, total)
                    self.assertLess(extra, bank * shares)

    def test_upward_rounding_and_power_certificate(self):
        for numerator in range(1, 30):
            value = Fraction(numerator, 37)
            rounded = round_up_dyadic(value, 5)
            self.assertGreaterEqual(rounded, value)
            self.assertLess(rounded - value, Fraction(1, 32))
            upper = Fraction(2) ** ceil_log2(value)
            self.assertGreaterEqual(upper, value)
            self.assertLess(upper / 2, value)
        for exponent in range(-10, 11):
            self.assertEqual(ceil_log2(Fraction(2) ** exponent), exponent)

    def test_small_composition_certificate(self):
        result = certificate(1, 2, 8, 32, 1, 1, 5)
        delta = 1 - common_overlap(1, 2)
        exact_bound = 2 * delta ** 8
        self.assertEqual(result["conditional_TV_upper_certificate"], "2^-7")
        self.assertLessEqual(exact_bound, Fraction(1, 128))
        self.assertEqual(certificate(254, 293, 64, 8, 5613, 1)["status"],
                         "No improvement over TV <= 1")

    def test_zero_budget(self):
        for snapshots, repetitions in ((0, 1), (1, 0)):
            self.assertEqual(certificate(254, 293, 64, 8, snapshots, repetitions)
                             ["conditional_TV_upper_certificate"], "0")

    def test_invalid_parameters(self):
        for width, noise in ((-1, 0), (0, -1)):
            with self.assertRaises(ValueError):
                common_overlap(width, noise)
        for noise, bank, shares in ((-1, 1, 1), (0, 0, 1), (0, 1, 0)):
            with self.assertRaises(ValueError):
                allocate_noise(noise, bank, shares)
        with self.assertRaises(ValueError):
            certificate(1, 1, 2, 8, -1, 1)
        with self.assertRaises(ValueError):
            round_up_dyadic(Fraction(1, 2), 0)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--test", action="store_true")
    parser.add_argument("--width", type=int, default=254, help="maximum HW, not encoding bit width")
    parser.add_argument("--bank", type=int, default=293, help="number of shared live values")
    parser.add_argument("--shares", type=int, nargs="+", default=[32, 64, 128])
    parser.add_argument("--noise", type=int, nargs="+", default=[1 << 30], help="fixed total noise N")
    parser.add_argument("--snapshots", "--T", type=int, default=5613)
    parser.add_argument("--repetitions", "--q", type=int, default=1)
    parser.add_argument("--precision", type=int, default=80)
    args = parser.parse_args()
    if args.test:
        unittest.main(argv=[__file__])
        return
    print(json.dumps({
        "model": "aggregate stored HW + independent Binomial(N, 1/2) at each snapshot",
        "premise": "whole bank freshly independently shared conditional on history and clear values",
        "formula": "min(1, q*T*bank*(1-alpha)^shares)",
        "warning": "Exact arithmetic calculation, not a Rocq proof or physical calibration. "
                   "A vacuous certificate is not an insecurity result.",
    }), flush=True)
    try:
        for noise in args.noise:
            for shares in args.shares:
                result = certificate(args.width, args.bank, shares, noise, args.snapshots,
                                     args.repetitions, args.precision)
                print(json.dumps(result), flush=True)
    except ValueError as error:
        parser.error(str(error))


if __name__ == "__main__":
    main()
