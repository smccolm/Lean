from pathlib import Path
import ast,re,json
s=Path(__file__).parent
for n in ['SourceEvenWeightFrickeUniformPreflight1652','SourceEvenWeightFrickeUniformValuePreflight1652']:
 assert (s/(n+'.exit')).read_text().strip()=='0'
 t=(s/(n+'.log')).read_text(encoding='utf-16')
 assert not re.search(r'warning:|error:|sorryAx|PANIC|Found [1-9]',t)
c=(s/'run_prepare_even_weight_fricke_canonical_1643.py').read_text(encoding='utf-8')
for a,b in [('even-weight-fricke-trace','even-weight-fricke-uniform'),('EvenWeightFrickeTrace','EvenWeightFrickeUniform'),('even_weight_fricke_trace','even_weight_fricke_uniform'),('Even Weight Fricke Trace','Even Weight Fricke Uniform'),('EVEN WEIGHT FRICKE TRACE','EVEN WEIGHT FRICKE UNIFORM'),('1643','1653'),('1638','1652')]:
 c=c.replace(a,b)
c=c.replace('even-weight-fricke-uniform-versions-1652.json','even-weight-fricke-uniform-versions-1651.json')
c=c.replace('localModules=mods,','localModules=mods+list(json.loads((s/\'even-weight-fricke-trace-versions-1643.json\').read_text(encoding=\'utf-8\'))),')
report='''# Uniform even-weight Fricke integrality — 28 October 2026

The exact unresolved chain is DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 → literal higher continuation → automorphy → original all-weight characteristic-zero association → original Gamma1 degree/genus preservation → reduced field action → uniform level-power slash integrality. Acceptance remains 16/20; DUB-17–20 OPEN.

The theorem exists_level_power_integral_even_fricke_coefficients proves that, at every nonzero level N and every even integer weight, an actual Gamma1(N) modular form whose Fourier coefficients are cleared by a single power of N has the same property after its actual Fricke transform. The exponent is uniform over every coefficient. No common-denominator, transformed-algebraicity, auxiliary-existence, decay or trace-decomposition premise remains. Level one is proved directly from modular invariance; negative even weights are included.

The actual trace supplies pointwise level-power integrality and hence algebraicity of every transformed coefficient. Existing integral Gamma1 cusp forms span the cusp space. A finite scalar combination with algebraic coefficients descends to the algebraic subfield by a linear retraction; native integral-multiple algebra clears the finitely many scalars. Multiplication by the actual discriminant reduces a modular form to that cusp case, and its proved integral Euler-product inverse cancels the discriminant. An elementary even-weight balance constructs all required nonnegative exponents. The existing Bezout and factorization argument turns the resulting common integer denominator into one level power.

The [pinned scalar-descent source](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_PowerSeries_exists_sum_smul_eq_of_forall_coeff_mem.lean) is adapted using native LinearMap.exists_leftInverse_of_injective. The repository's integral cusp span and actual discriminant cancellation give a shorter route than constructing another rational basis of every modular-form space. The original integral-ratio field already admits even-weight representatives, so an odd-weight auxiliary branch is not required.

Eight versioned modules pass public/exhaustive axiom checks and sixteen linters each. All 24 required dependency checks pass in the declaration-value closure of the uniform theorem, including the actual constructed auxiliary and trace. The first value audit stopped at six canonical scratch imports; its evidence is preserved and a fresh audit traverses those imports without dropping any edge. Canonical ownership and receipts are recorded separately. The scope contains eleven public theorems and one definition; no proof limits, root pins or source contract changed.

Production promotion and assembled verification of this scope remain pending. Full SL2 slash integrality, reduced field action on every rational relation, the signed-index lower bound, original degree/genus preservation, integral parabolic transfer, characteristic-zero realization, automorphy and literal higher continuation remain required. No Dubon acceptance gate is claimed closed.
'''
start=c.index("write(report,'''" ); end=c.index("''')",start)+4
c=c[:start]+'write(report,'+repr(report)+')'+c[end:]
start=c.index('route=dict(');end=c.index("\nrf=",start)
route="""route=dict(recordedUTC=datetime.now(timezone.utc).isoformat(),chain='DUB-17 Theorem2.6 / DUB-18 Cor8.2 -> literal higher continuation -> automorphy -> original characteristic-zero association -> original Gamma1 degree/genus -> reduced field action -> uniform level-power SL2 slash integrality -> uniform even-weight Fricke integrality.',reuseChecked=[dict(path=str(s/n),sha256=sha(s/n)) for n in ['fricke-common-denominator-shorter-route-1642.json','even-weight-fricke-uniform-audit-correction-1652.json',report]],shorterRoute='Native integral cusp span, linear retraction to the algebraic coefficient field, native finite integral multiples and the actual integral discriminant inverse construct the denominator. The actual trace supplies coefficient algebraicity; no separate rational modular basis is needed. Even-weight integral ratios preserve the original field.',assumptionsToDischarge=['The actual even-weight Fricke transform is a Gamma1 modular form.','The actual trace proves every transformed coefficient algebraic.','Native integral cusp span and scalar descent construct a common integer denominator.','The actual discriminant and its integral inverse extend the denominator from cusp forms to modular forms.','Even integer weights admit the required nonnegative balance, including negative weights.','A single power of the level clears every actual even-weight Fricke coefficient at every nonzero level.'],remaining='Full SL2 slash integrality, reduced field action, signed-index lower bound, original degree/genus preservation, integral parabolic transfer, characteristic-zero realization, automorphy and literal higher continuation remain open. Acceptance remains 16/20; DUB-17--20 OPEN.',externalBuild=False,externalImport=False,rootPinsChanged=False,proofLimitsChanged=False)"""
c=c[:start]+route+c[end:]
ast.parse(c)
p=s/'prepare_even_weight_fricke_uniform_canonical_1653.py'; assert not p.exists();p.write_text(c,encoding='utf-8')
exec(compile(c,str(p),'exec'))
