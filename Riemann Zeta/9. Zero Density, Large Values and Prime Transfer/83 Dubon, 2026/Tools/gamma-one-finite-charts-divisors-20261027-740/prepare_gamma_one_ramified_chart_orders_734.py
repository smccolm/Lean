from pathlib import Path
import hashlib,json,re
p=Path(__file__).parent
d=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')
pairs=[('SourceOriginalRamifiedMeromorphicOrder','SourceGammaOneRamifiedMeromorphicOrder'),('SourceOriginalNearbyOrders','SourceGammaOneNearbyOrders'),('SourceOriginalRamifiedChartOrders','SourceGammaOneRamifiedChartOrders')]
for old,new in pairs:
 src=d/(old+'.lean');dst=p/(new+'.lean')
 assert not dst.exists() and not (d/dst.name).exists()
 t=src.read_text(encoding='utf-8')
 t=t.replace('namespace Dubon2026.SourceFunctionField','namespace Dubon2026.SourceFunctionField.GammaOne')
 t=t.replace('end Dubon2026.SourceFunctionField','end Dubon2026.SourceFunctionField.GammaOne')
 t=t.replace('open UpperHalfPlane','open UpperHalfPlane CongruenceSubgroup')
 t=t.replace('[NeZero N]', '[NeZero N] (hT : ModularGroup.T \u2208 Gamma1 N)')
 for a,b in [('originalRamifiedPlace_regular_analytic N','ramifiedPlace_regular_analytic N hT'),('originalRamifiedPlace_regular_order N','ramifiedPlace_regular_order N hT'),('originalRamifiedPlace_meromorphicOrderAt N','ramifiedPlace_meromorphicOrderAt N hT'),('originalRamifiedPlace_nearby_orders N','ramifiedPlace_nearby_orders N hT'),('meromorphicAt_originalRamifiedPlace_eval N','meromorphicAt_ramifiedPlace_eval N hT'),('originalRamifiedPlace N','ramifiedPlace N hT'),('meromorphicAt_originalRamifiedPlace_eval','meromorphicAt_ramifiedPlace_eval'),('originalRamifiedPlace','ramifiedPlace'),('originalAnalyticRamification_param_eventually_one N','analyticRamification_param_eventually_one hT'),('originalAnalyticRamification_pos N','analyticRamification_pos hT'),('originalAnalyticRamification N','analyticRamification hT'),('originalAnalyticPlace N','analyticPlace hT'),('modularFunctionFieldOver N','functionFieldOver (Gamma1 N)'),('meromorphicNFAt_originalPlaceEval N','meromorphicNFAt_placeEval hT'),('originalPlaceEval_meromorphicOrderAt N','placeEval_meromorphicOrderAt hT'),('originalPlaceEval_analyticAt_iff N','placeEval_analyticAt_iff hT'),('originalPlaceEval N \u2102','placeEval hT'),('originalPlaceEval_inv','placeEval, SourceCurve.Place.rationalEval_inv'),('place_eq_of_coord_power_eq N','place_eq_of_coord_power_eq N hT')]:t=t.replace(a,b)
 for a,b in [('Dubon2026.SourceOriginalRamifiedRegularOrder','SourceGammaOneRamifiedRegularOrder'),('Dubon2026.SourceOriginalPlaceInverseValues','Dubon2026.SourceCurveRationalChartValues'),('Dubon2026.SourceOriginalRamifiedMeromorphicOrder','SourceGammaOneRamifiedMeromorphicOrder'),('Dubon2026.SourceOriginalNearbyOrders','SourceGammaOneNearbyOrders'),('Dubon2026.SourceOriginalRamificationIsolated','Dubon2026.SourceGammaOneRamificationIsolation')]:t=t.replace('import '+a,'import '+b)
 t=t.replace('original torsion cardinality','actual Gamma1 period comparison')
 assert not re.search(r'\boriginal[A-Z]',t)
 if new=='SourceGammaOneRamifiedChartOrders':
  t=t.replace('open scoped Topology','open scoped Topology MatrixGroups')
  marker='theorem ramifiedPlace_chart_orders'
  lemma='''theorem analyticRamification_param_eventually_one {\u0393 : Subgroup SL(2, \u2124)}
    (hT : ModularGroup.T \u2208 \u0393) (\u03c4 : \u210d) :
    \u2200\u1da0 u in \ud835\udcdd[\u2260] (0 : \u2102),
      analyticRamification hT (ofComplex (EllipticCoordinate.param \u03c4 u)) = 1 := by
  have ht := (EllipticCoordinate.hasDerivAt_param \u03c4).tendsto_nhdsNE
    (sub_ne_zero.mpr (EllipticCoordinate.upper_ne_conj \u03c4 \u03c4))
  rw [EllipticCoordinate.param_zero] at ht
  exact ht.eventually (analyticRamification_eventually_one hT \u03c4)

'''.encode('utf-16','surrogatepass').decode('utf-16')
  t=t.replace(marker,lemma+marker)
 with dst.open('x',encoding='utf-8',newline='\n') as f:f.write(t)
inputs=[d/(old+'.lean') for old,_ in pairs]
inputs += [d/n for n in ['SourceCurveRationalChartValues.lean','SourceGammaOneRamificationIsolation.lean','SourceOriginalRamificationIsolated.lean','SourcePowerDescentLocalBranch.lean','SourceEllipticParameterLocal.lean']]
inputs += [p/'SourceGammaOneRamifiedRegularOrder.lean',p/'SourceGammaOneRamifiedRegularParameter.lean',p/'SourceGammaOneEllipticFibers.lean']
route=dict(chain='DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> original all-weight arithmetic association -> actual finite Gamma1 Hecke-character realization -> Picard/H1/period/Hecke/diamond comparison -> actual ramified charts -> exact orders for all functions on a common neighborhood.',reuseChecked=[dict(path=str(f),sha256=hashlib.sha256(f.read_bytes()).hexdigest().upper()) for f in inputs],shorterRoute='The already proved generic rational residue inversion law handles poles without repeating the original residue-ring proof. Reuse the existing analytic local power branch and centered coordinate. The previously proved Gamma1 ramification isolation supplies one radius independent of the function, so the original nearby-order argument removes the ramification factor throughout that radius.',assumptionsToDischarge=['All actual rational functions, including poles, have meromorphic residue values on the descended Gamma1 place family with exactly the normalized valuation order at the center.','One positive radius works for every nonzero function and every chart point; regular functions have analytic values throughout that common neighborhood.'],remaining='Normalize charts by actual uniformizers, construct cusp/global place charts and actual periods, discharge full Hecke/diamond/Picard/H1 arithmetic comparison, original all-weight association and literal higher symmetric-power continuation. 16/20; DUB-17--20 OPEN.',rootPinsChanged=False,proofLimitsChanged=False)
with (p/'gamma-one-ramified-chart-orders-route-734.json').open('x',encoding='utf-8') as f:json.dump(route,f,indent=2);f.write('\n')
print('Prepared actual Gamma1 ramified meromorphic and common-neighborhood order proofs.')
