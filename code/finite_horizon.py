import json
import re
import subprocess
import sys
from itertools import permutations
from pathlib import Path

from cluster_dp import standardize

ROOT = Path(__file__).resolve().parent.parent
EXE = ROOT / 'code' / ('first_counts.exe' if sys.platform == 'win32' else 'first_counts')
FIELDS = ('k', 'n', 'minimum', 'index', 'a', 'b', 'negative', 'zero')


def python_counts(k, n):
    pats = list(permutations(range(k)))
    index = {p: i for i, p in enumerate(pats)}
    a = [0] * len(pats)
    b = [0] * len(pats)
    for p in permutations(range(n)):
        windows = [standardize(p[i:i + k]) for i in range(n - k + 1)]
        final = windows[-1]
        if final in windows[:-1]:
            continue
        right = final[-1:] + final[:-1]
        left = final[1:] + final[:1]
        if right not in windows[:-1]:
            a[index[final]] += 1
        if left not in windows[:-1]:
            b[index[left]] += 1
    diffs = [y - x for x, y in zip(a, b)]
    low = min(diffs)
    at = diffs.index(low)
    return dict(k=k, n=n, minimum=low, index=at, a=a[at], b=b[at],
                negative=sum(d < 0 for d in diffs), zero=sum(d == 0 for d in diffs))


def cpp_counts(k, n):
    line = subprocess.check_output([str(EXE), str(k), str(n)], text=True)
    match = re.fullmatch(r'k=(\d+) n=(\d+) min\(b-a\)=(-?\d+) id=(\d+) a=(\d+) b=(\d+) '
                         r'negative=(\d+) zero=(\d+)\s*', line)
    assert match, line
    return dict(zip(FIELDS, map(int, match.groups())))


def main():
    for k, n in [(3, 4), (3, 7), (4, 7), (5, 7)]:
        assert python_counts(k, n) == cpp_counts(k, n), (k, n)
    print('Python and C++ enumerations agree on four cases.')
    results = []
    for n in range(4, 12):
        for k in range(3, n):
            result = cpp_counts(k, n)
            assert result['minimum'] > 0, result
            results.append(result)
        print('n =', n, 'minima', [r['minimum'] for r in results if r['n'] == n])
    (ROOT / 'data' / 'finite_horizon.json').write_text(json.dumps(results, indent=1) + '\n')
    print('b_n - a_n > 0 for every A and every 3 <= k < n <= 11.')


if __name__ == '__main__':
    main()
