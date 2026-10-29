from pathlib import Path
from datetime import datetime,timezone
import json,hashlib
p=Path(__file__).parent
r=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')
names=['SourceValuationFrobeniusRoots.lean','SourceValuationCyclotomicFrobenius.lean','SourceLocalCyclotomicAction.lean','LocalResidueRootSeparation.lean','SourceGammaOneResidueArithmetic.lean']
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
data=dict(recordedUTC=datetime.now(timezone.utc).isoformat(),chain='DUB-17/18 -> original all-weight arithmetic association -> actual Gamma1 finite Hecke-character realization -> genuine cyclotomic/Tate Galois action with actual Frobenius and inertia.',reuse=[dict(path=str(r/n),sha256=sha(r/n)) for n in names],selected='Native valuation_frobenius_root already applies to every residue-invertible root order at the exact arbitrary source valuation. Apply the primitive-root exponent characterization directly; set q=1 for inertia. No new valuation-root integrality, root separation, local field, or cyclotomic foundation is needed.',discharge='Derive the actual finite cyclotomic exponent at original residue Frobenius and its triviality on original inertia. These discharge the cyclotomic-value hypothesis in the genuine Galois/Frobenius comparison and its inertia consumer.',remaining='Coordinate-degree and genus preservation, combined-diamond and finite Hecke-character realization, original arithmetic/unramified descent, all-weight two-dimensional association, automorphy and literal higher continuation remain. 16/20; DUB-17--20 OPEN.',productionMutation=False)
t=p/'gamma-one-cyclotomic-local-reuse-1405.json';assert not t.exists();t.write_text(json.dumps(data,indent=2)+'\n',encoding='utf-8')
s=(p/'build_gamma_one_picard_descent_1381f.ps1').read_text(encoding='utf-8').replace('SourceGammaOneHeckePicardDescent1381f','SourceAbsoluteCyclotomicLocal1405a')
t=p/'build_gamma_one_cyclotomic_local_1405.ps1';assert not t.exists();t.write_text(s,encoding='utf-8')
