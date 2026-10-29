from pathlib import Path
p=Path(__file__).parent
r=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')
s=(r/'SourceOriginalPlaceFieldOfDefinition.lean').read_text(encoding='utf-8')
s=s.replace('import Dubon2026.SourceOriginalFiniteFieldOfDefinition','import SourceGammaOneFunctionFieldDefinition1413a').replace('import Dubon2026.SourceOriginalFinitePlaceOrbit','import SourceGammaOneFinitePlaceOrbit1414a')
start=s.index('/-!');end=s.index('-/',start)+2
s=s[:start]+'''/-! DUB-17/18 -> original all-weight arithmetic association -> continuous
finite homogeneous-valued Tate action -> finite fields of definition of
actual Gamma1 places. Reuse the original finite-orbit separation argument,
with the proved exact Gamma1 function and orbit inputs. A finite compositum
fixes the literal valuation ring; no finite-orbit continuity is assumed. -/'''+s[end:]
s=s.replace('namespace Dubon2026.SourceFunctionField','namespace Dubon2026.SourceFunctionField.GammaOne').replace('end Dubon2026.SourceFunctionField','end Dubon2026.SourceFunctionField.GammaOne')
s=s.replace('open SourceCurve','open SourceCurve CongruenceSubgroup')
for a,b in [('original_place_fieldOfDefinition','gammaOne_place_fieldOfDefinition'),('original_function_fieldOfDefinition','gammaOne_function_fieldOfDefinition'),('original_place_galois_orbit_finite','gammaOne_place_galois_orbit_finite'),('modularFunctionFieldOver N Qbar','functionFieldOver (Gamma1 N) Qbar'),('originalArithmeticPlace N','arithmeticPlace (Gamma1 N)'),('originalArithmeticRingAut N','arithmeticRingAut (Gamma1 N)')]:s=s.replace(a,b)
t=p/'SourceGammaOnePlaceFieldDefinition1415a.lean';assert not t.exists();t.write_text(s,encoding='utf-8')
s=(p/'build_gamma_one_function_definition_1413.ps1').read_text(encoding='utf-8').replace('SourceGammaOneFunctionFieldDefinition1413a','SourceGammaOnePlaceFieldDefinition1415a')
t=p/'build_gamma_one_place_definition_1415.ps1';assert not t.exists();t.write_text(s,encoding='utf-8')
