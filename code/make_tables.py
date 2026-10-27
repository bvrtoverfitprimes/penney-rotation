import csv
import json
from fractions import Fraction as F
from math import floor
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
DATA = ROOT / 'data'
TABLES = ROOT / 'tables'


def trunc(x, p=4):
    return f'{floor(F(x) * 10 ** p) / 10 ** p:.{p}f}'


def word(a):
    return ''.join(str(x) for x in a)


def frac(x):
    x = F(x)
    return f'${x.numerator}/{x.denominator}$'


def approx(x):
    x = F(x)
    return f'${x.numerator}/{x.denominator}\\approx{trunc(x)}$'


def write(name, lines):
    (TABLES / name).write_text('\n'.join(lines) + '\n')


def main():
    TABLES.mkdir(exist_ok=True)
    cert = json.loads((DATA / 'certificates.json').read_text())
    refined = cert['refined']
    pairs = {k: list(csv.DictReader(open(DATA / f'pair_bounds_k{k}.csv'))) for k in (6, 7)}

    lines = [r'\begin{tabular}{@{}rrrrl@{}}', r'\toprule',
             r'$k$&Representatives&$h$&Largest length&Minimum lower bound for $k!D$\\', r'\midrule']
    for k in (3, 4, 5):
        rows = [r for r in refined if r['k'] == k]
        h = rows[0]['h']
        low = min(F(r['lower_kfact_D']) for r in rows)
        lines.append(f'{k}&{len(rows)}&{h}&{3 * k + h - 3}&{approx(low)}\\\\')
    for k in (6, 7):
        low = F(pairs[k][0]['J'])
        lines.append(f'{k}&{len(pairs[k])}&\\multicolumn{{2}}{{c}}{{$J(A)$}}&{approx(low)}\\\\')
    lines += [r'\bottomrule', r'\end{tabular}']
    write('certificates.tex', lines)

    lines = [r'\begin{tabular}{@{}llrr@{}}', r'\toprule', r'$A$&$B$&$d_{k+1}$&Bound\\', r'\midrule']
    for r in refined:
        if r['k'] in (3, 4):
            lines.append(f"{word(r['a'])}&{word(r['b'])}&{r['d'][0]}&{trunc(r['lower_kfact_D'])}\\\\")
    lines += [r'\bottomrule', r'\end{tabular}']
    write('refined_k3_k4.tex', lines)

    lines = [r'\begin{tabular}{@{}llrr@{}}', r'\toprule', r'$A$&$B$&$d_6$&Bound\\', r'\midrule']
    for r in refined:
        if r['k'] == 5:
            lines.append(f"{word(r['a'])}&{word(r['b'])}&{r['d'][0]}&{trunc(r['lower_kfact_D'])}\\\\")
    lines += [r'\bottomrule', r'\end{tabular}']
    write('refined_k5.tex', lines)

    lines = [r'\begin{tabular}{@{}llll@{}}', r'\toprule', r'$A$&$B$&$J(A)$&Decimal\\', r'\midrule']
    for k in (6, 7):
        if k == 7:
            lines.append(r'\midrule')
        for row in pairs[k][:5]:
            lines.append(f"{row['A']}&{row['B']}&{frac(row['J'])}&{trunc(row['J'])}\\\\")
    lines += [r'\bottomrule', r'\end{tabular}']
    write('smallest_k6_k7.tex', lines)

    fh = {(r['k'], r['n']): r['minimum'] for r in json.loads((DATA / 'finite_horizon.json').read_text())}
    lines = [r'\begin{tabular}{@{}r|rrrrrrrr@{}}', r'\toprule',
             r'$n\backslash k$&' + '&'.join(str(k) for k in range(3, 11)) + r'\\', r'\midrule']
    for n in range(4, 12):
        cells = [str(fh[(k, n)]) if k < n else '' for k in range(3, 11)]
        lines.append(f'{n}&' + '&'.join(cells) + r'\\')
    lines += [r'\bottomrule', r'\end{tabular}']
    write('finite_horizon.tex', lines)
    print('Wrote', len(list(TABLES.glob('*.tex'))), 'tables.')


if __name__ == '__main__':
    main()
