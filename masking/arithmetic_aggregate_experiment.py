"""Exact fresh-share aggregate-HW snapshots, not an execution-security proof.

Dynamic programming counts tuples by modular sum and total HW. Conditioning on
the sum gives uniform additive sharing, including the last dependent share.
Noise is a fixed total Binomial(N, 1/2), independent of the sharing.
"""

import argparse
from collections import Counter
from fractions import Fraction
from itertools import product
import json
from math import comb
import unittest

from curve_noise_feasibility import common_overlap


def tuple_counts(modulus, shares):
    if modulus < 2 or shares < 1:
        raise ValueError("modulus must be at least two; shares must be positive")
    counts = {(0, 0): 1}
    for _ in range(shares):
        next_counts = Counter()
        for (residue, weight), count in counts.items():
            for value in range(modulus):
                next_counts[((residue + value) % modulus, weight + value.bit_count())] += count
        counts = next_counts
    return counts


def noisy_histograms(modulus, shares, noise):
    if noise < 0:
        raise ValueError("noise count must be nonnegative")
    counts = tuple_counts(modulus, shares)
    laws = [Counter() for _ in range(modulus)]
    kernel = [comb(noise, k) for k in range(noise + 1)]
    for (secret, weight), count in counts.items():
        for added, multiplicity in enumerate(kernel):
            laws[secret][weight + added] += count * multiplicity
    denominator = modulus ** (shares - 1) * (1 << noise)
    if any(sum(law.values()) != denominator for law in laws):
        raise AssertionError("conditional sharing mass is not normalized")
    return laws, denominator


def tv_counts(left, right, denominator):
    return Fraction(sum(abs(left[k] - right[k]) for k in left.keys() | right.keys()), 2 * denominator)


def experiment(modulus, shares, noise):
    laws, denominator = noisy_histograms(modulus, shares, noise)
    distance, pair = max((tv_counts(laws[s], laws[t], denominator), (s, t))
                         for s in range(modulus) for t in range(s + 1, modulus))
    maximum_hw = max(value.bit_count() for value in range(modulus))
    word_noise, leftover = divmod(noise, shares)
    minorization = (1 - common_overlap(maximum_hw, word_noise)) ** shares
    if distance > minorization:
        raise AssertionError("exact distance exceeds the conditional common-mass bound")
    return {
        "modulus": modulus,
        "shares": shares,
        "fixed_total_noise_bits": noise,
        "max_snapshot_TV": str(distance),
        "maximizing_secrets": pair,
        "common_mass_upper": str(minorization),
        "per_share_noise_allocation": word_noise,
        "leftover_aggregate_noise": leftover,
        "scope": "one fresh canonical-sharing snapshot; no temporal or Curve25519 claim",
    }


class Checks(unittest.TestCase):
    def test_counts_against_exhaustive_tuples(self):
        for modulus in (2, 3, 5, 7):
            for shares in (1, 2, 3):
                brute = Counter((sum(values) % modulus, sum(x.bit_count() for x in values))
                                for values in product(range(modulus), repeat=shares))
                self.assertEqual(tuple_counts(modulus, shares), brute)

    def test_actual_dependent_share_and_noise(self):
        for modulus in (3, 5):
            for shares in (1, 2, 3):
                laws, denominator = noisy_histograms(modulus, shares, 3)
                self.assertEqual(denominator, modulus ** (shares - 1) * 8)
                for secret in range(modulus):
                    brute = Counter()
                    for masks in product(range(modulus), repeat=shares - 1):
                        last = (secret - sum(masks)) % modulus
                        weight = sum(x.bit_count() for x in masks) + last.bit_count()
                        for bits in product((0, 1), repeat=3):
                            brute[weight + sum(bits)] += 1
                    self.assertEqual(laws[secret], brute)

    def test_one_share_and_f2_parity(self):
        laws, denominator = noisy_histograms(3, 1, 0)
        self.assertEqual(tv_counts(laws[0], laws[1], denominator), 1)
        for shares in (1, 2, 8):
            laws, denominator = noisy_histograms(2, shares, 0)
            self.assertEqual(tv_counts(laws[0], laws[1], denominator), 1)

    def test_fixed_noise_and_data_processing(self):
        for modulus in (3, 5, 7):
            for shares in (2, 3, 4):
                previous = Fraction(1)
                for noise in range(9):
                    result = experiment(modulus, shares, noise)
                    distance = Fraction(result["max_snapshot_TV"])
                    self.assertLessEqual(distance, previous)
                    previous = distance

    def test_invalid_parameters(self):
        for modulus, shares in ((1, 2), (3, 0)):
            with self.assertRaises(ValueError):
                tuple_counts(modulus, shares)
        with self.assertRaises(ValueError):
            noisy_histograms(3, 2, -1)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--test", action="store_true")
    parser.add_argument("--modulus", type=int, nargs="+", default=[3, 5, 7])
    parser.add_argument("--shares", type=int, nargs="+", default=[2, 4, 8])
    parser.add_argument("--noise", type=int, nargs="+", default=[0, 8])
    args = parser.parse_args()
    if args.test:
        unittest.main(argv=[__file__])
        return
    try:
        for modulus in args.modulus:
            for noise in args.noise:
                for shares in args.shares:
                    print(json.dumps(experiment(modulus, shares, noise)), flush=True)
    except ValueError as error:
        parser.error(str(error))


if __name__ == "__main__":
    main()
