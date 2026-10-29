from pathlib import Path
from datetime import datetime,timezone
import json,hashlib
p=Path(__file__).parent
r=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')
files=[p/(n+'.lean') for n in ['SourceTwistedCoefficientDualAction','SourceCyclotomicHomogeneousHecke','SourceGammaOneTwistedGaloisFrobenius']]+[r/(n+'.lean') for n in ['SourceGammaOneDiamondCoefficientMatrix','SourceGammaOneArithmeticTateOperators','SourceGammaOneBinaryNormalizerTate']]
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
route=dict(recordedUTC=datetime.now(timezone.utc).isoformat(),chain='DUB-17/18 -> original all-weight association -> finite Hecke-character Galois realization -> Frobenius polynomial throughout the Galois orbit of original parabolic classes.',reuse=[dict(path=str(f),sha256=sha(f)) for f in files],selected='Reuse the existing twisted-dual operator commutation and literal Picard diamond commutation. The native normalizer coefficient is a diagonal matrix; extend only the already proved diagonal coefficient commutation to its two actual entries. Then derive stability of diamond fixedness and consume the original Frobenius polynomial on every Galois translate.',remaining='Original coordinate degree/genus equalities, nonzero character realization and parabolic transfer remain; these lemmas do not construct a two-dimensional realization or close DUB-17--20.',productionMutation=False)
t=p/'gamma-one-twisted-diamond-reuse-1426.json';assert not t.exists();t.write_text(json.dumps(route,indent=2)+'\n',encoding='utf-8')
s=(p/'SourceCyclotomicHomogeneousHecke.lean').read_text(encoding='utf-8')
s=s.replace('sourceCyclotomicHomogeneousAction_commute (u : Rˣ) (d : R)', 'sourceCyclotomicHomogeneousAction_diagonal_commute (u : Rˣ) (a b : R)')
s=s.replace('![d, 1]', '![a, b]')
s=s.replace('diagonal Hecke coefficient matrix.', 'diagonal normalizer coefficient matrix.')
t=p/'SourceCyclotomicHomogeneousDiamond1426a.lean';assert not t.exists();t.write_text(s,encoding='utf-8')
s=(p/'build_gamma_one_arithmetic_descent_1425c.ps1').read_text(encoding='utf-8').replace('SourceGammaOneTwistedArithmeticDescent1425c',"SourceCyclotomicHomogeneousDiamond1426a','SourceGammaOneTwistedGaloisDiamond1427a")
t=p/'build_gamma_one_twisted_diamond_1426.ps1';assert not t.exists();t.write_text(s,encoding='utf-8')
