import csv
import json
from fractions import Fraction as F
from itertools import permutations
from math import comb, factorial
from pathlib import Path

from cluster_dp import certificate, coefficients, rotate, standardize

ROOT = Path(__file__).resolve().parent.parent
DATA = ROOT / 'data'


def representatives(k):
    for a in permutations(range(k)):
        if a < tuple(k - 1 - x for x in a):
            yield a


def overlap(u, v, d):
    k = len(u)
    shared = sorted(zip(u[d:], v[:k - d]))
    old_u = old_v = -1
    ways = 1
    for x, y in shared + [(k, k)]:
        if y <= old_v:
            return 0
        left, right = x - old_u - 1, y - old_v - 1
        ways *= comb(left + right, left)
        old_u, old_v = x, y
    return ways


def leading(a):
    b = rotate(a)
    return overlap(a, a, 1) + overlap(b, a, 1) - overlap(a, b, 1) - overlap(b, b, 1)


def pair_bound(a):
    k = len(a)
    b = rotate(a)
    lower = F(leading(a), k + 1)
    for d in range(2, k):
        lower -= F((overlap(a, b, d) + overlap(b, b, d)) * factorial(k), factorial(k + d))
    lower -= F(8 * (k - 1), factorial(k) - 2 * (k - 1))
    return lower


def check_convolution(max_n=8):
    for k in (3, 4):
        for a in permutations(range(k)):
            b = rotate(a)
            cs, _ = coefficients(a, max_n)
            avoid = []
            for n in range(max_n + 1):
                counts = [0, 0]
                av = 0
                for p in permutations(range(n)):
                    winner = at = None
                    for i in range(n - k + 1):
                        pat = standardize(p[i:i + k])
                        if pat in (a, b):
                            winner, at = int(pat == b), i + k
                            break
                    if winner is None:
                        av += 1
                    elif at == n:
                        counts[winner] += 1
                avoid.append(av)
                predicted = sum(comb(n, j) * avoid[n - j] * cs[j - k] for j in range(k, n + 1))
                assert predicted == counts[1] - counts[0], (a, n)
    print('Cluster convolution agrees with direct enumeration through n =', max_n)


def word(a):
    return ''.join(str(x + 1) for x in a)


def main():
    DATA.mkdir(exist_ok=True)
    check_convolution()
    output = {'refined': [], 'pair_bound_minima': []}
    for k, h in [(3, 13), (4, 4), (5, 1)]:
        results = []
        for a in representatives(k):
            c = certificate(a, h)
            assert c['lower'] > 0, a
            assert c['prefix_count'].denominator == 1
            lower = c['lower'] * factorial(k)
            output['refined'].append({
                'k': k, 'h': h, 'a': list(c['a']), 'b': [x + 1 for x in rotate(a)],
                'd': c['c'], 'prefix_count': int(c['prefix_count']),
                'lower_kfact_D': str(lower)})
            results.append(lower)
        assert len(results) == factorial(k) // 2
        print('k =', k, 'representatives =', len(results), 'minimum =', min(results))
    for k in (6, 7):
        rows = []
        for a in representatives(k):
            rows.append((pair_bound(a), a))
        assert len(rows) == factorial(k) // 2
        assert all(v > 0 for v, _ in rows)
        rows.sort()
        with open(DATA / f'pair_bounds_k{k}.csv', 'w', newline='') as fh:
            w = csv.writer(fh)
            w.writerow(['A', 'B', 'd_k_plus_1', 'J', 'J_decimal'])
            for v, a in rows:
                w.writerow([word(a), word(rotate(a)), leading(a), str(v), f'{float(v):.6f}'])
        least = rows[0]
        output['pair_bound_minima'].append({'k': k, 'representatives': len(rows),
                                            'lower_kfact_D': str(least[0]),
                                            'a': [x + 1 for x in least[1]]})
        print('k =', k, 'representatives =', len(rows), 'minimum =', least[0])
    constant = F(33, 35) + F(3, 10) * F(4, 11) ** 5 + F(504, 40306)
    assert constant < 1
    output['large_k_constant'] = str(constant)
    print('Constant for k >= 8:', constant, '< 1')
    (DATA / 'certificates.json').write_text(json.dumps(output, indent=1) + '\n')
    print('All exact checks passed.')


if __name__ == '__main__':
    main()
