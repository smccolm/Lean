from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,re
s=Path(__file__).parent;sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
src=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')
ml=Path(r'E:\Lean\Riemann Zeta\.lake\packages\mathlib\Mathlib')
files=[]
for row in json.loads((s/'anthropic-siegel-dependencies-1553/fetch-manifest.json').read_text(encoding='utf-8'))['files']:
 f=Path(row['local']);assert sha(f)==row['sha256'];t=f.read_text(encoding='utf-8')
 code=re.sub(r'--[^\n]*','',re.sub(r'/\-.*?\-/','',t,flags=re.S))
 files.append(dict(**row,lexicalMatches=re.findall(r'\b(?:sorry|admit|axiom|unsafe|native_decide|implemented_by)\b',code),nondefaultOptions=[dict(line=i,text=l) for i,l in enumerate(t.splitlines(),1) if re.search(r'set_option\s+(?:linter\.|maxHeartbeats|synthInstance\.maxHeartbeats|maxRecDepth)',l)]))
assert not any(f['lexicalMatches'] for f in files)
native=[src/'SourcePowerSeriesProduct.lean',src/'SourceRealizedPowerSeries.lean',ml/'NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean',ml/'NumberTheory/ModularForms/DedekindEta.lean',ml/'Analysis/Normed/Group/Tannery.lean']
route=dict(recordedUTC=datetime.now(timezone.utc).isoformat(),chain='DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher continuation -> arithmetic automorphy -> original all-weight characteristic-zero association -> original Gamma1 degree/genus preservation -> reduced field action -> level-power slash integrality -> peaked auxiliary existence -> actual Siegel-product holomorphy and SL2 transformation -> Jacobi theta triple-product identity -> finite Gaussian product identity and dominated finite-sum limit.',sources=files,nativeReuse=[dict(path=str(f),sha256=sha(f)) for f in native],assessment='The exact q-expansion product theorem and cusp-limit theorem already exist natively and will be reused. Native Jacobi theta supplies its analytic and modular transformation API, and native eta supplies geometric-product convergence. Searches found no Jacobi triple-product identity or Gaussian q-binomial API in the pinned native tree. The source product identity supplies the missing equality between the literal Siegel infinite product and the existing analytic theta function; prove only its finite identity, convergence bounds and theta specialization, retaining the native source objects. No broader q-series theory is planned.',assumptionsToDischarge=['The actual Jacobi theta series equals the required convergent infinite product.','The actual Siegel function defined by its literal product has the needed holomorphy and SL2 transformation law.'],boundary='A route review, not a proof of the Siegel product or a closed acceptance gate. The finite exponent theorem is separately proved; actual product expansions, leading units and auxiliary existence remain open. External source texts are not imported, and no external transitive audit is claimed.',externalBuild=False,externalImport=False,productionMutation=False)
def write(n,t):
 f=s/n;assert not f.exists();f.write_text(t,encoding='utf-8')
write('siegel-jacobi-route-review-1557.json',json.dumps(route,indent=2)+'\n')
t=(s/'anthropic-siegel-dependencies-1553/S_jacobiTheta_two_eq_tprod.lean.txt').read_text(encoding='utf-8')
ns='Dubon2026.SourceFunctionField.GammaOne.PeakedAuxiliary.JacobiProduct'
header='''/-! DUB-17/18 -> original Gamma1 degree/genus preservation -> level-power
slash integrality -> peaked auxiliary existence -> literal Siegel-product
holomorphy and SL2 transformation -> Jacobi theta product identity. The
finite Gaussian identity is the source finite approximation needed to
identify the actual product with Mathlib's analytic theta function.
Native q-series multiplication and cusp limits are already proved and
will be reused. No abstract q-series generalization is introduced.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, revision
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_jacobiTheta_two_eq_tprod. -/
'''
body=t[t.index('def qfact '):t.index('theorem gauss_q ')]
body=body.replace('def qfact ', '/-- The finite Euler product in the source Gaussian identity. -/\ndef qfact ',1).replace('def qbinom ', '/-- The actual Gaussian quotient of finite Euler products. -/\ndef qbinom ',1)
body=body.replace('@[scoped simp] theorem','theorem')
write('SourceSiegelJacobiFiniteProducts1557a.lean','''import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable
import Mathlib.Tactic

'''+header+'namespace '+ns+'\nnoncomputable section\nopen Finset\n\n'+body+'\nend\nend '+ns+'\n')
body=t[t.index('theorem gauss_q '):t.index('private theorem prod_zpow\' ')]
write('SourceSiegelJacobiGaussProduct1558a.lean','import SourceSiegelJacobiFiniteProducts1557a\n\n'+header+'namespace '+ns+'\nopen Finset\n\n'+body+'\nend '+ns+'\n')
body=t[t.index('private theorem prod_zpow\' '):t.index('\nend JTPEngine')]
write('SourceSiegelJacobiFiniteIdentity1559a.lean','import SourceSiegelJacobiGaussProduct1558a\n\n'+header+'namespace '+ns+'\nopen Finset\n\n'+body+'\nend '+ns+'\n')
print(json.dumps(dict(review='siegel-jacobi-route-review-1557.json',sources=len(files),nativeExactReuse=['SourcePowerSeriesProduct.Realized.hasSum_qParam_mul','SourceRealizedPowerSeries.Realized.tendsto_atImInfty'],preparedModules=3)))
