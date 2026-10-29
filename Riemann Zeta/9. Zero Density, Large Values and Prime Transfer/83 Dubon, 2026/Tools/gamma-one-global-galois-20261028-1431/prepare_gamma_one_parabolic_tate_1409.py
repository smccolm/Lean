from pathlib import Path
from datetime import datetime,timezone
import hashlib,json
p=Path(__file__).parent
r=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')
names=['SourceGammaOneParabolicRestriction.lean','SourceGammaOneDiamondRestriction.lean','SourceGammaOneBinaryTateH1.lean','SourceGammaOneBinaryDiamondTateH1.lean','SourceGammaOneBinaryNormalizerTate.lean']
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
data=dict(recordedUTC=datetime.now(timezone.utc).isoformat(),chain='DUB-17/18 -> original all-weight arithmetic association -> original finite Hecke-character realization -> actual source parabolic H1 restriction in the homogeneous-valued Tate dual -> combined-diamond fixedness for the derived Frobenius polynomial.',reuse=[dict(path=str(r/n),sha256=sha(r/n)) for n in names],selected='Use the already proved literal restriction into binary parabolic H1 and the native Tate/H1 equivalence. The native restriction diamond theorem and Tate/H1 diamond square derive fixedness of its actual Tate preimage. No new cohomology or period model is necessary.',discharge='Produce the actual Tate preimage of each original source parabolic class and derive combined-diamond fixedness for every actual normalizer.',remaining='The comparison retains 3<p. Nonvanishing and the finite Hecke-character transfer remain; no nonzero class or surjectivity of restriction is claimed. Actual degree/genus, exceptional primes, finite realization, all-weight association, automorphy and literal higher continuation remain. 16/20; DUB-17--20 OPEN.',productionMutation=False)
t=p/'gamma-one-parabolic-tate-reuse-1409.json';assert not t.exists();t.write_text(json.dumps(data,indent=2)+'\n',encoding='utf-8')
s=(p/'build_gamma_one_picard_descent_1381f.ps1').read_text(encoding='utf-8').replace('SourceGammaOneHeckePicardDescent1381f','SourceGammaOneParabolicTateLift1409a')
t=p/'build_gamma_one_parabolic_tate_1409.ps1';assert not t.exists();t.write_text(s,encoding='utf-8')
