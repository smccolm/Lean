from pathlib import Path
from datetime import datetime, timezone
import hashlib,json
p=Path(__file__).parent
r=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')
names=['SourceCoefficientDualAction.lean','SourceGammaOneBinaryGaloisHecke.lean','MatrixPolynomialAction.lean','GL2UnitDiagonalPair.lean','HomogeneousDeterminantTwist.lean','PrimitiveRootCyclotomicContinuity.lean','RationalArithmeticCyclotomicCharacter.lean','SourceOriginalCyclotomicLocal.lean']
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
data=dict(recordedUTC=datetime.now(timezone.utc).isoformat(),chain='DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher continuation -> original all-weight arithmetic association -> actual finite Gamma1 Hecke-character realization -> genuine homogeneous-valued Tate Galois action matching the derived inverse-action Frobenius polynomial.',reuse=[dict(path=str(r/n),sha256=sha(r/n)) for n in names],selected='Reuse the actual homogeneous GL representation and two-unit diagonal multiplication to obtain the coefficient action u times diag(u,1). Pair it with inverse precomposition on the existing actual Tate action. Reuse native primitive-root cyclotomic exponent and continuity theorems for the global character; do not reconstruct cyclotomic characters or Tate spaces.',discharge='Construct the global coefficient/twisted dual action and its Hecke compatibility, then identify actual Frobenius and inertia using the already derived original Tate identities.',remaining='Coordinate-degree and genus preservation, combined-diamond and original finite Hecke-character realization, original global arithmetic/unramified descent, two-dimensional association, automorphy and literal higher continuation remain. 16/20; DUB-17--20 OPEN.',productionMutation=False,proofLimitsChanged=False)
t=p/'gamma-one-global-coefficient-route-1399.json';assert not t.exists();t.write_text(json.dumps(data,indent=2)+'\n',encoding='utf-8')
s=(p/'build_gamma_one_inertia_1359.ps1').read_text(encoding='utf-8')
s=s.replace("@('SourceGammaOneArithmeticCharts1359a','SourceGammaOneSpecializationCharts1360a')","@('SourceTwistedCoefficientDualAction1398a','SourceCyclotomicHomogeneousAction1399a')")
t=p/'build_gamma_one_global_coefficient_1399.ps1';assert not t.exists();t.write_text(s,encoding='utf-8')
