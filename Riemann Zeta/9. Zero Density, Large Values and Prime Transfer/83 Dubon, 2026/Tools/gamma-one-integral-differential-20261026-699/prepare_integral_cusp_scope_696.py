from pathlib import Path
import json, hashlib, re

p = Path(r'E:\Lean\.tmp\dubon83')
prod = Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')
mods = ['SourceWeierstrassIntegralDenominator', 'SourceBoundedIntegralSeriesProduct',
 'SourceIntegralEisensteinSix', 'SourceBoundedIntegralSeriesConstant',
 'SourceFrickeNumeratorIntegralBound', 'SourceBoundedRationalSeriesImage',
 'SourceLaurentSpanDescent', 'SourceFrickeLaurentSpanDescent',
 'SourceRationalCuspWeightLaurent', 'SourceRationalCuspWeightIntegrality',
 'SourceIntegralRationalLaurentSeries', 'SourceBoundedIntegralLaurentAlgebra',
 'SourceBoundedRationalLaurentImage', 'SourceCyclotomicLaurentTrace',
 'SourceBoundedRationalLaurentIntegral', 'SourceBoundedCyclotomicLaurentFraction',
 'SourceBoundedCyclotomicLaurentGenerators', 'SourceBoundedFrickeLaurentField',
 'SourceBoundedRationalJAlgebra', 'SourceBoundedRationalCuspImage',
 'SourceIntegralLaurentWeightFactors', 'SourceRationalCuspWeightCancellation',
 'SourceGammaOneRationalBoundedDenominators']
assert len(mods) == len(set(mods)) == 23
for m in mods:
 f = p / (m + '.lean')
 assert f.exists() and not (prod / f.name).exists(), m
 assert f.with_suffix('.exit').read_text().strip() == '0', m
 assert f.with_suffix('.log').stat().st_size == 0, m
 assert f.with_suffix('.olean').stat().st_mtime >= f.stat().st_mtime, m
sha = lambda f: hashlib.sha256(f.read_bytes()).hexdigest().upper()
archive = p / 'deferred-power-series-route-696'
assert not archive.exists()
archive.mkdir()
saved = []
fallback = ['SourceIntegralRationalPowerSeries', 'SourceCyclotomicSeriesTrace',
 'SourceBoundedCyclotomicFractionTrace', 'SourceBoundedRationalSeriesIntegral']
for m in fallback + ['SourceBoundedRationalSeriesImage', 'SourceBoundedIntegralLaurentAlgebra']:
 for suffix in ['.lean', '.olean', '.log', '.exit']:
  f = p / (m + suffix)
  assert f.is_file()
  dest = archive / (f.name + ('.txt' if suffix == '.lean' else ''))
  dest.write_bytes(f.read_bytes())
  assert sha(dest) == sha(f)
  saved.append(dict(path=str(dest), sha256=sha(dest)))
# Keep the fully compiled alternative as non-production text; no discarded
# helper is retained in the selected Lean import graph.
for m in fallback:
 f = (p / (m + '.lean')).resolve()
 dest = (p / (m + '.lean.txt')).resolve()
 assert f.parent == p.resolve() == dest.parent and not dest.exists()
 f.rename(dest)
f = p / 'SourceBoundedRationalSeriesImage.lean'
s = f.read_text(encoding='utf-8')
a = s.index('\ntheorem hasBoundedIntegralCoefficients_of_integer_series\n')
b = s.index('\nend\n', a)
f.write_text(s[:a] + s[b:], encoding='utf-8')
f = p / 'SourceBoundedIntegralLaurentAlgebra.lean'
s = f.read_text(encoding='utf-8')
needle = '\ndef HasBoundedIntegralLaurentCoefficients'
assert s.count(needle) == 1
s = s.replace(needle, '\n/-- One nonzero integer makes every Laurent coefficient integral over the integers. -/\ndef HasBoundedIntegralLaurentCoefficients')
f.write_text(s, encoding='utf-8')
out = p / 'integral-cusp-selected-scope-696.json'
assert not out.exists()
out.write_text(json.dumps(dict(modules=mods, deferred=fallback, preserved=saved,
 status='Unaudited development selection. Recompile changed modules and their selected consumers before exhaustive audit. No frozen or production mathematical source changed.',
 rationale='Native Laurent localization avoids a duplicate power-series denominator route. The reverse rational power-series bound lemma had no consumer on the selected chain; retain only the forward integer-series construction needed for the actual cusp-form result.'), indent=2) + '\n', encoding='utf-8')
print(json.dumps(dict(selected=len(mods), deferred=len(fallback), preserved=len(saved), manifest=str(out))))
