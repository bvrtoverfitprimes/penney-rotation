from collections import defaultdict
from fractions import Fraction
from math import factorial


def standardize(xs):
    ranks = {v: j for j, v in enumerate(sorted(xs))}
    return tuple(ranks[x] for x in xs)


def rotate(a):
    return a[-1:] + a[:-1]


def coefficients(a, max_n):
    a = tuple(a)
    k = len(a)
    b = rotate(a)
    states = defaultdict(int)
    for p in (a, b):
        states[p[1:], 0, 1] += 1
    coeffs = [0] * (max_n - k + 1)
    arrivals = [[0] * k for _ in coeffs]
    mask = (1 << k) - 1
    for n in range(k, max_n):
        nxt = defaultdict(int)
        start = n + 1 - k
        for (tail, age, bits), count in states.items():
            gap = age + 1
            if gap >= k:
                continue
            for rank in range(n + 1):
                window = tuple(x + (x >= rank) for x in tail) + (rank,)
                pat = standardize(window)
                is_a, is_b = pat == a, pat == b
                if is_a or is_b:
                    new_bit = (bits >> (k - 1)) & 1
                    signed = (bits & 1) - new_bit
                    coeffs[start] += count * signed * (1 if is_a else -1)
                    arrivals[start][gap] += count
                    new_age = 0
                else:
                    new_bit = bits & 1
                    new_age = gap
                    if new_age >= k - 1:
                        continue
                new_bits = ((bits << 1) | new_bit) & mask
                nxt[window[1:], new_age, new_bits] += count
        states = nxt
    return coeffs, arrivals


def certificate(a, h):
    k = len(a)
    R = h + 2 * k - 2
    N = k + R - 1
    cs, arrivals = coefficients(a, N)
    prefix = sum((Fraction(arrivals[i][gap], factorial(k + i))
                  for i in range(h, h + k - 1)
                  for gap in range(i - h + 1, k)), Fraction())
    partial = sum((Fraction(c, factorial(k + d)) for d, c in enumerate(cs)), Fraction())
    bound = Fraction(4 * (k - 1), factorial(k) - 2 * (k - 1)) * prefix
    return dict(a=tuple(x + 1 for x in a), h=h, c=cs[1:],
                prefix_count=prefix * factorial(R),
                partial=partial, tail=bound, lower=partial - bound)
