from pathlib import Path
import datetime, hashlib, json

p = Path(__file__).parent
repo = Path(r'E:\Lean\Riemann Zeta')
paper = repo / '9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026'
mathlib = repo / '.lake/packages/mathlib/Mathlib'
sha = lambda f: hashlib.sha256(f.read_bytes()).hexdigest().upper()
native = [mathlib / s for s in ['RingTheory/LaurentSeries.lean',
    'RingTheory/IntegralClosure/IntegrallyClosed.lean', 'RingTheory/HahnSeries/Basic.lean',
    'RingTheory/Trace/Basic.lean']]
local = [paper / 'Extension/Dubon2026' / s for s in
    ['SourceModularJSeries.lean', 'SourceLaurentIntegralDescent.lean',
     'SourceFrickeCyclotomicLaurentLifts.lean', 'NumberFieldPositiveIntegralMultiple.lean']]
data = dict(recordedUTC=datetime.datetime.now(datetime.timezone.utc).isoformat(), scope=695,
    dependency='DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> original all-weight characteristic-zero association -> actual finite Gamma1 Hecke-character realization -> actual Picard/H1, full/parabolic, transpose/diamond comparison retaining the homogeneous coefficient endomorphism -> actual differential/cusp comparison -> arbitrary cusp differential realization -> original integral-ratio field membership -> bounded denominators for rational Fourier cusp forms.',
    route='Keep the original rational Laurent germ throughout. Native localization makes integer Laurent series normal. Clear the finite integer coefficient bounds in its monic relation, descend its actual bounded cyclotomic fraction by normalized coefficientwise trace, and apply Laurent normality. Cancel the original integral Eisenstein unit factors and discriminant powers to recover the original Fourier series.',
    reuseAssessment='This avoids choosing separate nonnegative pole-clearing exponents for every polynomial coefficient, developing new Laurent convolutions for trace, or taking the product of all conjugate denominators. The native sum-of-automorphisms trace identity establishes rational Laurent multiplication compatibility. Existing literal integer j, eta unit and inverse, and original Fricke numerator proofs provide the exact generator data.',
    nativeEvidence=[dict(path=str(f), sha256=sha(f)) for f in native],
    localEvidence=[dict(path=str(f), sha256=sha(f)) for f in local],
    sourceEntry='The new SourceFrickeLaurentSpanDescent, SourceRationalCuspWeightLaurent and SourceRationalCuspWeightIntegrality derive original holomorphic Fricke membership and rational j-integrality from the actual Gamma1 cusp form and its rational Fourier series. Their proofs compiled cleanly again after exact frozen-source restoration.',
    derivedAlgebra='SourceIntegralRationalLaurentSeries, SourceBoundedIntegralLaurentAlgebra, SourceBoundedRationalLaurentImage, SourceCyclotomicLaurentTrace, SourceBoundedRationalLaurentIntegral and SourceBoundedCyclotomicLaurentFraction have clean direct compilation. They remain unaudited development until their exact source consumer and exhaustive audits are assembled.',
    next='Finish bounded fractions for the original Fricke generators and their actual intermediate field; combine them with the already proved source monic relation; cancel the original weight factors and obtain a literal integer Fourier series after one nonzero integer scaling.',
    deferredPowerSeriesOnlyRoute=['SourceIntegralRationalPowerSeries', 'SourceCyclotomicSeriesTrace',
        'SourceBoundedCyclotomicFractionTrace', 'SourceBoundedRationalSeriesIntegral'],
    retainedPowerSeriesInputs='The actual torsion/E4/E6 Fricke-numerator bounds, bounded power-series product and constant results, and rational-to-integer power-series image bridge remain useful to the original generators and final Fourier-series output.',
    namingCorrection='Scope 694 new Laurent/function descent is SourceFrickeLaurentSpanDescent. The frozen SourceOriginalFrickeSpanDescent was restored to its exact original source and olean hashes; all 61 frozen module pairs in 10 receipts matched. See scratch-name-collision-restoration-verification-695.json; the canonical production source and assembled 8471 verification were unaffected.',
    status='Route review; no new development module in this scope has been promoted or exhaustively audited. Full scope remains 16/20; DUB-17--20 OPEN. All-weight arithmetic association and every original gate remain required. No source repair, root pin, proof limit, or linter change.')
for name in ['SourceIntegralRationalLaurentSeries', 'SourceBoundedIntegralLaurentAlgebra',
             'SourceBoundedRationalLaurentImage', 'SourceCyclotomicLaurentTrace',
             'SourceBoundedRationalLaurentIntegral', 'SourceBoundedCyclotomicLaurentFraction',
             'SourceFrickeLaurentSpanDescent', 'SourceRationalCuspWeightLaurent',
             'SourceRationalCuspWeightIntegrality']:
    assert (p / (name + '.exit')).read_text().strip() == '0', name
    assert (p / (name + '.log')).stat().st_size == 0, name
target = p / 'laurent-denominator-reuse-route-695.json'
with target.open('x', encoding='utf-8', newline='\n') as f:
    json.dump(data, f, indent=2); f.write('\n')
print(json.dumps(dict(path=str(target), sha256=sha(target))))
