"""Exact small-field projections, not a Rocq proof or a full noisy-trace bound."""

import argparse
from collections import Counter
from fractions import Fraction
from itertools import combinations, product
import json
from math import comb
import unittest


def square_trace(prime, shares, secret, randomness):
    """Arithmetic shares, refreshed second operand, pairwise product corrections."""
    expected = 2 * (shares - 1) + shares * (shares - 1) // 2
    if shares < 2 or len(randomness) != expected:
        raise ValueError("incorrect share or randomness count")
    random = iter(randomness)
    a = [next(random) for _ in range(shares - 1)]
    a.append((secret - sum(a)) % prime)
    bank = a + [0] * (2 * shares + 3)
    mask, temp, cross = 3 * shares, 3 * shares + 1, 3 * shares + 2
    observations = [sum(x.bit_count() for x in bank)]
    labels = ["initial"]

    def write(slot, value, label):
        bank[slot] = value % prime
        observations.append(sum(x.bit_count() for x in bank))
        labels.append(label)

    # Refresh while copying; no unrefreshed duplicate of the complete input bank.
    last_b = 2 * shares - 1
    write(last_b, bank[shares - 1], "copy_last")
    for i in range(shares - 1):
        write(mask, next(random), "refresh_mask")
        write(shares + i, bank[i] + bank[mask], "refresh_copy")
        write(last_b, bank[last_b] - bank[mask], "refresh_last")
        write(mask, 0, "clear_refresh_mask")
    assert sum(bank[shares:2 * shares]) % prime == secret

    for i in range(shares):
        write(2 * shares + i, bank[i] * bank[shares + i], "diagonal")
    for i in range(shares):
        for j in range(i + 1, shares):
            ci, cj = 2 * shares + i, 2 * shares + j
            write(mask, next(random), "product_mask")
            write(ci, bank[ci] - bank[mask], "mask_output")
            write(temp, bank[i] * bank[shares + j], "cross_product_left")
            write(cross, bank[mask] + bank[temp], "cross_accumulate_left")
            write(temp, bank[j] * bank[shares + i], "cross_product_right")
            write(cross, bank[cross] + bank[temp], "cross_accumulate_right")
            write(cj, bank[cj] + bank[cross], "correct_output")
            write(mask, 0, "clear_product_mask")
            write(temp, 0, "clear_product_temp")
            write(cross, 0, "clear_product_cross")
        write(i, 0, "clear_operand_a")
        write(shares + i, 0, "clear_operand_b")
    assert sum(bank[2 * shares:3 * shares]) % prime == secret * secret % prime
    assert len(observations) == 7 * shares - 2 + 10 * comb(shares, 2)
    assert all(x == 0 for x in bank[:2 * shares] + bank[3 * shares:])
    return tuple(observations), tuple(labels)


def raw_projections(prime, shares, secret, max_worlds):
    count = 2 * (shares - 1) + comb(shares, 2)
    worlds = prime ** count
    if worlds > max_worlds:
        raise ValueError(f"{worlds} worlds exceed the explicit limit {max_worlds}")
    singles = None
    pairs = {}
    for randomness in product(range(prime), repeat=count):
        trace, labels = square_trace(prime, shares, secret, randomness)
        if singles is None:
            singles = [Counter() for _ in trace]
            # Publicly selected projections; no claim to optimize over all attacks.
            points = {0, len(trace) - 1}
            points.update(i for i, label in enumerate(labels) if label == "diagonal")
            pairs = {pair: Counter() for pair in combinations(sorted(points), 2)}
        for histogram, value in zip(singles, trace):
            histogram[(value,)] += 1
        for (i, j), histogram in pairs.items():
            histogram[(trace[i], trace[j])] += 1
    return worlds, labels, singles, pairs


def noisy_counts(histogram, noise):
    """Integer weights for independent Binomial(noise, 1/2) noise per observation."""
    result = Counter()
    dimensions = len(next(iter(histogram)))
    coefficients = [comb(noise, k) for k in range(noise + 1)]
    for signal, weight in histogram.items():
        for offsets in product(range(noise + 1), repeat=dimensions):
            total = weight
            for offset in offsets:
                total *= coefficients[offset]
            result[tuple(x + y for x, y in zip(signal, offsets))] += total
    return result


def tv(left, right):
    assert sum(left.values()) == sum(right.values())
    distance = sum(abs(left[key] - right[key]) for key in left.keys() | right.keys())
    return Fraction(distance, 2 * sum(left.values()))


def compare(prime, shares, noise, secrets, max_worlds):
    left = raw_projections(prime, shares, secrets[0], max_worlds)
    right = raw_projections(prime, shares, secrets[1], max_worlds)
    assert left[:2] == right[:2]
    singles = [tv(noisy_counts(a, noise), noisy_counts(b, noise))
               for a, b in zip(left[2], right[2])]
    pairs = {ij: tv(noisy_counts(a, noise), noisy_counts(right[3][ij], noise))
             for ij, a in left[3].items()}
    best = max(range(len(singles)), key=singles.__getitem__)
    best_pair = max(pairs, key=pairs.__getitem__)
    return {
        "prime": prime, "shares": shares, "noise_bits_per_snapshot": noise,
        "secrets": secrets, "random_worlds_per_secret": left[0],
        "snapshots": len(singles), "stored_words": 3 * shares + 3,
        "max_single_projection_TV": str(singles[best]),
        "single_snapshot": [best, left[1][best]],
        "max_selected_pair_projection_TV": str(pairs[best_pair]),
        "pair_snapshots": [[i, left[1][i]] for i in best_pair],
        "full_trace_TV_lower_bound": str(max(singles[best], pairs[best_pair])),
        "full_trace_TV_upper_bound": None,
    }


class Checks(unittest.TestCase):
    def test_known_noise_tv(self):
        self.assertEqual(tv(noisy_counts(Counter({(0,): 1, (4,): 1}), 2),
                            noisy_counts(Counter({(2,): 2}), 2)), Fraction(3, 4))

    def test_noise_preserves_mass(self):
        h = Counter({(0, 2): 3, (1, 4): 5})
        self.assertEqual(sum(noisy_counts(h, 4).values()), 8 * 2 ** 8)

    def test_exhaustive_odd_field_square(self):
        for shares in (2, 3):
            for secret in range(3):
                worlds, labels, singles, pairs = raw_projections(3, shares, secret, 10000)
                self.assertTrue(all(sum(h.values()) == worlds for h in singles))
                self.assertTrue(all(sum(h.values()) == worlds for h in pairs.values()))
                self.assertEqual(labels[-1], "clear_operand_b")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--test", action="store_true")
    parser.add_argument("--prime", type=int, choices=(3, 5, 7), default=3)
    parser.add_argument("--shares", type=int, nargs="+", default=[2, 3])
    parser.add_argument("--noise", type=int, nargs="+", default=[2, 8])
    parser.add_argument("--max-worlds", type=int, default=100000)
    args = parser.parse_args()
    if args.test:
        unittest.main(argv=[__file__])
        return
    if any(n < 0 for n in args.noise):
        parser.error("noise counts must be nonnegative")
    for noise in args.noise:
        for shares in args.shares:
            print(json.dumps(compare(args.prime, shares, noise, [0, 1], args.max_worlds)), flush=True)


if __name__ == "__main__":
    main()
