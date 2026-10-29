from pathlib import Path
from datetime import datetime,timezone
import hashlib,json
p=Path(__file__).parent
r=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')
files=[r/(n+'.lean') for n in ['ContinuousGaloisFaithfulFiniteFactor','SourceRationalLocalValuation','SourceAbsoluteArithmeticDescent','SourceAbsoluteFiniteUnramified']]
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
route=dict(recordedUTC=datetime.now(timezone.utc).isoformat(),chain='DUB-17/18 -> original all-weight arithmetic association -> genuine finite homogeneous-coefficient Galois realization -> actual faithful finite Galois factor and original unramified descent.',reuse=[dict(path=str(f),sha256=sha(f)) for f in files],selected='Reuse the already proved faithful open-kernel fixed-field construction. Actual Tate-dual continuity supplies the open kernel; the group-source representation takes values in units automatically. Retain the faithful factor needed by the existing original arithmetic-descent theorem instead of rebuilding finite Galois or ramification foundations.',remaining='Original degree/genus equalities, parabolic character transfer/nonvanishing, two-dimensional association, exceptional primes, automorphy and literal higher continuation remain. 16/20; DUB-17--20 OPEN.',productionMutation=False)
t=p/'gamma-one-twisted-factor-reuse-1421.json';assert not t.exists();t.write_text(json.dumps(route,indent=2)+'\n',encoding='utf-8')
s=(p/'build_gamma_one_function_definition_1413.ps1').read_text(encoding='utf-8').replace('SourceGammaOneFunctionFieldDefinition1413a','SourceGammaOneTwistedFiniteFactor1421a')
t=p/'build_gamma_one_twisted_factor_1421.ps1';assert not t.exists();t.write_text(s,encoding='utf-8')
