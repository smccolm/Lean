from pathlib import Path
import datetime, hashlib, json

p = Path(__file__).parent
repo = Path(r'E:\Lean\Riemann Zeta')
prod = repo / '9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026/Extension/Dubon2026'
mathlib = repo / '.lake/packages/mathlib/Mathlib'
chain = ('DUB-17 Theorem 2.6 and DUB-18 Corollary 8.2 -> literal higher symmetric-power '
         'continuation -> arithmetic automorphy -> original all-weight characteristic-zero '
         'association -> actual finite Gamma1 Hecke-character realization -> actual Picard/H1 '
         'and full/parabolic transpose/diamond comparison retaining the homogeneous coefficient '
         'endomorphism -> actual differential/cusp comparison -> arbitrary cusp differential '
         'realization -> rational Fourier structure and original integral-ratio field membership '
         '-> bounded Fourier denominators.')

def evidence(path):
    return dict(path=str(path), sha256=hashlib.sha256(path.read_bytes()).hexdigest().upper())

records = {
    693: dict(
        route='Normalize a nonzero denominator coefficient, then trace numerator and denominator.',
        reviewedPrimary='Bounded-denominator core snapshot 690, galois_descent and exists_int_multiple; fixed anthropics commit 6e837e75355538c7f80bab5b956861e86c4eacc2.',
        comparison='The primary proof takes the product of all conjugate denominators. The local route instead takes the trace after multiplying by the inverse of one nonzero coefficient. That trace coefficient is the positive field degree, so the denominator remains nonzero. No Galois product or fixed-field coefficient descent is needed.',
        provedInputs=[evidence(mathlib / 'RingTheory/Trace/Basic.lean'), evidence(mathlib / 'RingTheory/Trace/Defs.lean'), evidence(prod / 'NumberFieldPositiveIntegralMultiple.lean')],
        developmentModules=['SourceCyclotomicSeriesTrace', 'SourceBoundedCyclotomicFractionTrace', 'SourceBoundedRationalSeriesImage', 'SourceBoundedRationalSeriesIntegral'],
        discharged='For an actual rational series represented by bounded cyclotomic numerator/denominator, construct a bounded rational fraction. Independently, a monic relation with bounded coefficients plus such a fraction yields a uniform integer coefficient bound.',
        remaining='Derive both the monic relation and fraction data from the actual modular function; cancel the exact discriminant and Eisenstein factors to reach its original Fourier series.'),
    694: dict(
        route='Use a coefficientwise linear retraction to descend the actual Laurent span, then recover the original holomorphic function fraction.',
        comparison='Reuse the same native coefficient retraction already used by SourceLaurentIntegralDescent. Descend a finite complex span directly; no new full fixed-point or faithful-flatness development is needed.',
        provedInputs=[evidence(prod / 'SourceLaurentIntegralDescent.lean'), evidence(prod / 'SourceFrickeCyclotomicLaurentLifts.lean'), evidence(prod / 'SourceCuspLaurentLinearRelations.lean'), evidence(prod / 'SourceCuspWeightImageSpan.lean')],
        developmentModules=['SourceLaurentSpanDescent', 'SourceOriginalFrickeSpanDescent'],
        discharged='The first lemma descends span membership. The analytic consumer is under development: literal cyclotomic Laurent coefficients and existing complex Fricke-span membership should give original cyclotomic holomorphic fraction membership.',
        remaining='Construct the literal Laurent germ from the original rational Fourier cusp form and its exact weight-lowering factors. Then derive its monic relation and bounded fraction, with no image-membership hypothesis retained.')
}
for scope, data in records.items():
    target = p / f'shorter-denominator-route-{scope}.json'
    assert not target.exists(), target
    data.update(scope=scope, recordedUTC=datetime.datetime.now(datetime.timezone.utc).isoformat(),
                dependency=chain, gateStatus='16/20; DUB-17--20 OPEN; all original acceptance criteria retained.',
                status='Route review only. Development modules are not yet exhaustively audited or promoted. No full goal completion claim.')
    target.write_text(json.dumps(data, indent=2) + '\n', encoding='utf-8')
    print(json.dumps(evidence(target)))
