from pathlib import Path
from datetime import datetime,timezone
import json,hashlib
p=Path(__file__).parent
r=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')
names=['SourceOriginalFiniteFieldOfDefinition','SourceOriginalFinitePlaceOrbit','SourceOriginalPlaceFieldOfDefinition','SourceOriginalPicardFieldOfDefinition','SourceOriginalTateAdicContinuity','SourceTateProjections','SourceGammaOneArithmeticDivisors','SourceGammaOneArithmeticTateOperators','SourceGammaOneArithmeticPeriodInclusion','SourceGammaOneBinaryTateH1','SourceCurveCoordinateValues','SourceCurveSeparatingFunctionSupport']
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
route=dict(recordedUTC=datetime.now(timezone.utc).isoformat(),chain='DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher continuation -> original all-weight arithmetic association -> actual finite homogeneous-coefficient Hecke-character realization -> continuity of the genuine Gamma1 cyclotomic/Tate Galois action.',reuse=[dict(path=str(r/(n+'.lean')),sha256=sha(r/(n+'.lean'))) for n in names],selected='Adapt the already proved original finite-field-of-definition argument to the exact Gamma1 integral-ratio field. Reuse finite separating-coordinate support and residue fields to bound place orbits, finite support to fix Picard classes, the exact Tate projection kernel, and the existing period base-change finite generation. Derive open stabilizers of the finite dual; no new topological Tate theory or general scheme descent is needed.',discharge='Prove continuity of the genuine Galois action on the finite coefficient-valued Tate dual from actual finite fields of definition, rather than assuming continuity of an abstract representation.',remaining='Coordinate-degree/genus, original parabolic character transfer/nonvanishing, exceptional coefficient primes, two-dimensional realization, automorphy and literal higher continuation remain. 16/20; DUB-17--20 OPEN.',productionMutation=False)
def write(n,s):
    t=p/n;assert not t.exists();t.write_text(s,encoding='utf-8')
write('gamma-one-continuity-reuse-1413.json',json.dumps(route,indent=2)+'\n')
s=(r/'SourceOriginalFiniteFieldOfDefinition.lean').read_text(encoding='utf-8')
s=s.replace('import Dubon2026.SourceOriginalArithmeticFieldAction','import Dubon2026.SourceGammaOneArithmeticField\nimport Dubon2026.SourceOriginalArithmeticFieldAction')
start=s.index('/-!');end=s.index('-/',start)+2
s=s[:start]+'''/-! DUB-17/18 -> original all-weight arithmetic association -> continuous
finite homogeneous-valued Tate Galois action -> finite fields of definition
of the actual Gamma1 functions. Adapt the existing finite compositum proof
on literal Laurent base change. Its rational-generator coefficient identity
is reused directly. Place and Picard stabilizers are the next consumers. -/'''+s[end:]
s=s.replace('namespace Dubon2026.SourceFunctionField','namespace Dubon2026.SourceFunctionField.GammaOne').replace('end Dubon2026.SourceFunctionField','end Dubon2026.SourceFunctionField.GammaOne')
s=s.replace('noncomputable section','noncomputable section\nopen CongruenceSubgroup')
s=s.replace('original_laurent_fieldOfDefinition','gammaOne_laurent_fieldOfDefinition').replace('original_function_fieldOfDefinition','gammaOne_function_fieldOfDefinition')
s=s.replace('modularFunctionFieldOver N Qbar','functionFieldOver (Gamma1 N) Qbar').replace('modularFunctionFieldFull N','qExpFunctionFieldC ℚ (Gamma1 N)').replace('originalArithmeticRingAut N','arithmeticRingAut (Gamma1 N)')
write('SourceGammaOneFunctionFieldDefinition1413a.lean',s)
s=(p/'build_gamma_one_parabolic_frobenius_1410b.ps1').read_text(encoding='utf-8').replace('SourceGammaOneParabolicGaloisFrobenius1410b','SourceGammaOneFunctionFieldDefinition1413a')
write('build_gamma_one_function_definition_1413.ps1',s)
print('Prepared exact-source continuity route and first function-field lemma.')
