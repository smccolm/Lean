from pathlib import Path
from datetime import datetime,timezone
import json,hashlib
p=Path(__file__).parent
r=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')
files=[r/(n+'.lean') for n in ['SourceRationalLocalValuation','SourceOriginalTateInertia','SourceAbsoluteArithmeticDescent','SourceAbsoluteFiniteUnramified']]
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
route=dict(recordedUTC=datetime.now(timezone.utc).isoformat(),chain='DUB-17/18 -> original all-weight association -> finite homogeneous-coefficient Galois action -> original prescribed-support arithmetic descent.',reuse=[dict(path=str(f),sha256=sha(f)) for f in files],selected='Use the already proved exact pulled-back local valuation and transport of norm inertia. Native residue characteristic derives invertibility of the coefficient prime away from Q*p. Apply the existing original Gamma1 inertia result at that exact valuation, then target the existing continuous prescribed-support descent theorem; no new local field or ramification theory is needed.',remaining='The actual coordinate-degree and genus equalities remain as separate explicit geometric inputs at each original valuation. Original character transfer/nonvanishing, two-dimensional realization, automorphy and literal higher continuation remain. 16/20; DUB-17--20 OPEN.',productionMutation=False)
t=p/'gamma-one-arithmetic-descent-reuse-1424.json';assert not t.exists();t.write_text(json.dumps(route,indent=2)+'\n',encoding='utf-8')
s=(p/'build_gamma_one_function_definition_1413.ps1').read_text(encoding='utf-8').replace('SourceGammaOneFunctionFieldDefinition1413a','SourceGammaOneTwistedNormInertia1424a')
t=p/'build_gamma_one_norm_inertia_1424.ps1';assert not t.exists();t.write_text(s,encoding='utf-8')
