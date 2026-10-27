import json
import subprocess
import sys
from pathlib import Path

from cluster_dp import certificate

ROOT = Path(__file__).resolve().parent.parent
EXE = ROOT / 'code' / ('linear_extensions.exe' if sys.platform == 'win32' else 'linear_extensions')


def main():
    for k, h in [(4, 4), (5, 1)]:
        out = subprocess.check_output([str(EXE), str(k), str(h)], text=True)
        cases = json.loads(out)['cases']
        assert len(cases) > 0
        for case in cases:
            a = tuple(x - 1 for x in case['a'])
            c = certificate(a, h)
            assert c['c'] == case['c'], case['a']
            assert int(c['prefix_count']) == case['prefix_count'], case['a']
        print('k =', k, 'h =', h, ':', len(cases), 'representatives agree')
    print('Linear-extension enumeration agrees with the insertion recurrence.')


if __name__ == '__main__':
    main()
