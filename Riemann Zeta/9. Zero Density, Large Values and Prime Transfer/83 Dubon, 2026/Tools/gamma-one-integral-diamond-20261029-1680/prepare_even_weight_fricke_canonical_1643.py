from pathlib import Path
import ast
p = Path(__file__).parent
for name in ['SourceEvenWeightFrickeTracePreflight1638','SourceEvenWeightFrickeTraceValuePreflight1638']:
    assert (p/(name+'.exit')).read_text().strip() == '0'
s = (p/'run_prepare_actual_peaked_canonical_1625.py').read_text(encoding='utf-8')
a=s.index("report='"); b=s.index("rf='",a)
middle="""report='Dubon Even Weight Fricke Trace Assessment 2026-10-28.md'
write(report,'''# Even-weight Fricke trace — 28 October 2026

The exact unresolved chain is DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 → literal higher continuation → automorphy → original all-weight characteristic-zero association → original Gamma1 degree/genus preservation → reduced field action → uniform level-power slash integrality. This scope applies the constructed actual peaked auxiliary to the even-weight trace on the correct conjugate subgroup. Acceptance remains 16/20; DUB-17–20 OPEN.

The theorem even_weight_coeff_slash_fricke_mem_RN proves that every actual Fricke Fourier coefficient becomes an algebraic integer after multiplication by some power of N, for every N≥2 and every even-weight Gamma1 modular form whose original Fourier coefficients have a common level-clearing power. Its proof constructs the actual translated forms, proves their required congruence invariance and coefficient identities, and consumes exists_gamma1_peaked_auxiliary_form_twelve_dvd. There is no remaining auxiliary, decay, leading-unit or trace-decomposition premise.

The exponent in that theorem may depend on the coefficient. The separately conditional even_weight_level_power_fricke_of_common_denominator proves that a supplied nonzero common integer denominator D gives the single level exponent D for every coefficient. The Bezout/factorization argument is proved. Construction of that common integer denominator remains required; the uniform theorem is not yet unconditional.

The [pinned source](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_exists_isIntegral_level_pow_mul_qExpansion_slash_fricke_coeff.lean) is adapted using the repository's actual frickeMatrix, triangular Hecke slash formula, subgroup restriction, S-square identity, strict periods, coefficient uniqueness and even-weight negation. The conjugate subgroup is defined directly by the SL2 conjugation comap, with its literal membership identity proved. The original integral-ratio field admits even-weight representatives, so odd-weight auxiliary machinery is not needed on this dependency chain.

All six versioned modules passed exhaustive axiom checks, sixteen linters each and all 44 required proof-value dependency checks. Canonical scratch ownership, axiom and dependency receipts are recorded separately. The checked scope has 25 public theorems and seven definitions. No proof limits, root pins or source contract changed; no external build or direct import is claimed.

This scope awaits production promotion and assembled verification. A common denominator, the uniform full slash theorem, reduced field action on every rational relation, the signed-index lower bound and original degree/genus preservation remain open. Integral parabolic transfer, characteristic-zero realization, automorphy and literal higher continuation remain required. No Dubon acceptance gate is claimed closed.
''')
route=dict(recordedUTC=datetime.now(timezone.utc).isoformat(),chain='DUB-17 Theorem2.6 / DUB-18 Cor8.2 -> literal higher continuation -> automorphy -> original characteristic-zero association -> original Gamma1 degree/genus -> reduced field action -> uniform level-power slash integrality -> actual even-weight Fricke trace.',reuseChecked=[dict(path=str(s/n),sha256=sha(s/n)) for n in ['fricke-trace-reuse-review-1630.json','fricke-trace-minimality-review-1636.json',report]],shorterRoute='Reuse actual Fricke and triangular Hecke matrices, native subgroup restriction, S-square identity, strict periods and even-weight negation. Direct SL2 conjugation comap avoids a GL-injectivity detour. Apply the constructed twelve-divisible auxiliary; the original even-weight ratio theorem removes any need for an odd-weight branch.',assumptionsToDischarge=['The actual trace subgroup has finite index and both required translations.','The original transformed forms have the exact Fourier normalization and slash identities.','The constructed actual auxiliary discharges all auxiliary inputs in the even-weight Fricke trace.','Every actual Fricke coefficient is integral after a coefficient-dependent level power.','A common nonzero integer denominator implies one common level exponent by proved Bezout and factorization.'],remaining='Construct the common integer denominator and assemble uniform full slash integrality. Reduced field action, signed-index lower bound, original degree/genus preservation, integral parabolic transfer, characteristic-zero realization, automorphy and literal higher continuation remain open. Acceptance remains 16/20; DUB-17--20 OPEN.',externalBuild=False,externalImport=False,rootPinsChanged=False,proofLimitsChanged=False)
"""
s=s[:a]+middle+s[b:]
s=s.replace('actual-peaked-auxiliary','even-weight-fricke-trace').replace('SourceActualPeakedAuxiliary','SourceEvenWeightFrickeTrace').replace('ACTUAL PEAKED AUXILIARY','EVEN WEIGHT FRICKE TRACE').replace('1625','1643').replace('1624','1638').replace('actual_peaked_auxiliary','even_weight_fricke_trace')
ast.parse(s)
f=p/'run_prepare_even_weight_fricke_canonical_1643.py';assert not f.exists();f.write_text(s,encoding='utf-8')
exec(compile(s,str(f),'exec'))
