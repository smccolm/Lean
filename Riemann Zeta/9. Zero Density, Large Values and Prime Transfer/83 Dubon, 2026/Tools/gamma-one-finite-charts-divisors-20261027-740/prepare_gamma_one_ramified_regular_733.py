from pathlib import Path
import hashlib,json,re
p=Path(__file__).parent
d=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')
for name in ['RegularParameter','RegularOrder']:
 src=d/('SourceOriginalRamified'+name+'.lean')
 dst=p/('SourceGammaOneRamified'+name+'.lean')
 assert not dst.exists() and not (d/dst.name).exists()
 t=src.read_text(encoding='utf-8')
 t=t.replace('namespace Dubon2026.SourceFunctionField','namespace Dubon2026.SourceFunctionField.GammaOne')
 t=t.replace('end Dubon2026.SourceFunctionField','end Dubon2026.SourceFunctionField.GammaOne')
 t=t.replace('open UpperHalfPlane Filter EllipticCoordinate','open UpperHalfPlane Filter EllipticCoordinate CongruenceSubgroup')
 t=t.replace('[NeZero N]', '[NeZero N] (hT : ModularGroup.T \u2208 Gamma1 N)')
 t=t.replace('originalRamifiedPlace N', 'ramifiedPlace N hT')
 for a,b in [('originalRamifiedPlace_regular_analytic N','ramifiedPlace_regular_analytic N hT'),('originalRamifiedPlace_regular_order','ramifiedPlace_regular_order'),('originalRamifiedPlace_zero','ramifiedPlace_zero'),('originalRamifiedPlace_regular_analytic','ramifiedPlace_regular_analytic'),('originalRamifiedPlace','ramifiedPlace'),('originalAnalyticRamification_pos N','analyticRamification_pos hT'),('originalAnalyticRamification N','analyticRamification hT'),('originalAnalyticPlace N','analyticPlace hT'),('modularFunctionFieldOver N','functionFieldOver (Gamma1 N)'),('originalPlaceEval_meromorphicOrderAt N','placeEval_meromorphicOrderAt hT'),('originalPlaceEval_analyticAt_iff N','placeEval_analyticAt_iff hT'),('originalPlaceEval N \u2102','placeEval hT'),('place_eq_of_coord_power_eq N','place_eq_of_coord_power_eq N hT')]:t=t.replace(a,b)
 t=t.replace('import Dubon2026.SourceOriginalAnalyticEvaluation','import Dubon2026.SourceGammaOneAnalyticEvaluation')
 t=t.replace('import Dubon2026.SourceOriginalEllipticFibers','import SourceGammaOneEllipticFibers')
 t=t.replace('import Dubon2026.SourceOriginalRamifiedRegularParameter','import SourceGammaOneRamifiedRegularParameter')
 t=t.replace('original torsion cardinality','actual Gamma1 period comparison')
 t=t.replace('Actual original places','Actual Gamma1 places')
 t=t.replace('original regular function','actual Gamma1 regular function')
 # No old field-specific declarations may survive the adaptation.
 assert not re.search(r'\boriginal[A-Z]',t)
 with dst.open('x',encoding='utf-8',newline='\n') as f:f.write(t)
inputs=[d/('SourceOriginalRamified'+n+'.lean') for n in ['RegularParameter','RegularOrder']]
inputs += [d/n for n in ['SourceOriginalEllipticFibers.lean','SourcePowerFiberAnalyticDescent.lean','SourceGammaOneAnalyticEvaluation.lean','SourceGammaOnePlusMinus.lean']]
inputs += [p/'SourceGammaOneExactRamification.lean']
route=dict(chain='DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> original all-weight arithmetic association -> actual finite Gamma1 Hecke-character realization -> Picard/H1/period/Hecke/diamond comparison -> actual ramified charts -> analytic regular descent and exact normalized order.',reuseChecked=[dict(path=str(f),sha256=hashlib.sha256(f.read_bytes()).hexdigest().upper()) for f in inputs],shorterRoute='Reuse the existing centered elliptic coordinate and analytic power descent. Exact all-level Gamma1 ramification makes stabilizer multipliers exhaust all roots of unity; actual plus/minus place invariance discharges power-fiber invariance. Apply the existing analytic descent and cancel the proved positive ramification factor in the actual residue-value order identity. No new analytic descent framework or level restriction is needed.',assumptionsToDischarge=['Actual Gamma1 places are constant on every centered-coordinate power fiber, at all nonzero levels and all analytic centers.','Every actual function regular at the center has analytic residue values on the descended actual-place family, whose order is exactly the original normalized valuation order.'],remaining='Extend the exact descended order to poles and to one common chart neighborhood, then cusp/global charts and actual periods, full Hecke/diamond/Picard/H1 arithmetic comparison, original all-weight association and literal higher symmetric-power continuation. 16/20; DUB-17--20 OPEN.',rootPinsChanged=False,proofLimitsChanged=False)
with (p/'gamma-one-ramified-regular-route-733.json').open('x',encoding='utf-8') as f:json.dump(route,f,indent=2);f.write('\n')
print('Prepared actual Gamma1 regular ramified descent and normalized order.')
