from pathlib import Path
import ast
s=Path(__file__).parent
c=(s/'prepare_siegel_expansion_canonical_1598.py').read_text(encoding='utf-8')
a=c.index('versions=old|');b=c.index('\nmods=',a);c=c[:a]+'versions=old.copy()'+c[b:]
a=c.index("unused='");b=c.index('cfg.update(',a);c=c[:a]+c[b:]
c=c.replace(" c=c.replace('#print axioms '+unused+'\\n','')\n",'')
a=c.index("report='");b=c.index("rf='",a)
middle="""report='Dubon Finite Siegel Product Expansion Assessment 2026-10-28.md'
write(report,'''# Finite Siegel product expansion reuse assessment — 28 October 2026

DUB-17 Theorem 2.6 and DUB-18 Corollary 8.2 still require literal higher continuation through automorphy and original all-weight characteristic-zero association. This scope serves original Gamma1 degree/genus preservation through reduced field action, level-power slash integrality and actual peaked auxiliary existence. Acceptance remains 16/20; DUB-17–20 OPEN.

The [pinned finite-product source](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_SiegelUnit_exists_isIntegral_hasSum_prod_siegelFun_pow.lean) is adapted using existing native q-series multiplication and cusp limits, and audited trace coefficient multiplication/power lemmas. The explicit single-factor coefficients represent every residue pair, including the zero pair. Its exponent zero removes that factor directly. This avoids the candidate's chosen coefficient family, dummy series and duplicated coefficient algebra. Its raised heartbeat setting is not adopted.

The exact finite product has integral coefficients, the specified nonzero cyclotomic leading coefficient, an integral level-power multiple of its inverse, the literal constant phase with Nth power one, the source normalized HasSum and cusp limit. The final source consumer derives these from e(0,0)=0. Neither product convergence, coefficient integrality, nonvanishing, inverse integrality nor phase normalization is assumed.

All five versioned modules passed exhaustive axiom checks, sixteen linters per module and the value-only dependency audit. Canonical scratch ownership, axiom and value-dependency evidence are recorded separately. The single-factor existential wrapper is deliberately not needed by the finite-product proof: the actual explicit coefficients and their proved HasSum/integrality/constant-term properties are consumed directly. That shorter route retains the exact source conclusion. No external build, direct import or root-pin change is claimed.

Discriminant adjustment, exact auxiliary q-expansions, source cusp orders and decay estimates remain before the actual peaked auxiliary exists. Reduced field action, degree/genus preservation, integral parabolic transfer, characteristic-zero realization, automorphy and literal higher continuation remain required. This is a scratch scope pending production promotion and assembled verification.
''')
route=dict(recordedUTC=datetime.now(timezone.utc).isoformat(),chain='DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher continuation -> automorphy -> original all-weight characteristic-zero association -> original Gamma1 degree/genus preservation -> reduced field action -> level-power slash integrality -> actual peaked auxiliary -> exact integral finite Siegel product expansion.',reuseChecked=[dict(path=str(s/n),sha256=sha(s/n)) for n in ['siegel-finite-product-route-review-1596.json',report]],shorterRoute='Use explicit actual coefficients for every residue pair and handle the zero pair by exponent zero. Reuse native q-series multiplication/cusp limits and audited trace coefficient algebra. Split literal phase, leading inverse and exact source assembly with default proof limits.',assumptionsToDischarge=['Actual finite Siegel product has the exact normalized series with integral coefficients.','Its specified constant coefficient is nonzero from e(0,0)=0.','The specified level power times its leading inverse is integral.','The literal constant phase has Nth power one.','The normalized actual finite product tends to its leading coefficient at the cusp.'],remaining='Discriminant adjustment, exact auxiliary q-expansions, cusp order/decay estimates and actual peaked auxiliary existence. Reduced field action, degree/genus preservation, integral parabolic transfer, characteristic-zero realization, automorphy and literal higher continuation remain. Acceptance remains 16/20; DUB-17--20 OPEN.',externalBuild=False,externalImport=False,rootPinsChanged=False,proofLimitsChanged=False)
"""
c=c[:a]+middle+c[b:]
c=c.replace('siegel-expansion','siegel-finite-product').replace('SourceSiegelExpansion','SourceSiegelFiniteProduct').replace('SIEGEL EXPANSION','SIEGEL FINITE PRODUCT').replace('1598','1608').replace('1594','1602')
ast.parse(c)
f=s/'run_prepare_siegel_finite_product_canonical_1608.py';assert not f.exists();f.write_text(c,encoding='utf-8')
exec(compile(c,str(f),'exec'))
