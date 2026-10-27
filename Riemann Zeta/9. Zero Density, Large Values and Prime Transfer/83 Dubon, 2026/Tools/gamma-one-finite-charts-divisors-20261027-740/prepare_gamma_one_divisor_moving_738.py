from pathlib import Path
import hashlib, json, re
p=Path(__file__).parent
d=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
checked=['SourceOriginalFinitePlaceSeparation','SourceCurveRationalPlaceSeparation',
 'SourceCurvePrescribedOrders','SourceOriginalAnalyticDivisorMoving','SourceGammaOneFinitePlaceExhaustion',
 'SourceGammaOneCurveGeometry','SourceCurveFiniteSupport','SourceGammaOneAnalyticResidues']
route=dict(chain='DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> original all-weight arithmetic association -> actual finite Gamma1 Hecke-character realization -> full Picard/H1/Hecke/diamond comparison -> reduction of every actual degree-zero divisor class to a finite analytic divisor.',
 reuseChecked=[dict(path=str(d/(n+'.lean')),sha256=sha(d/(n+'.lean'))) for n in checked],
 reuseSearch='Inspected the existing original divisor-moving proof, generic rational residue separation and prescribed-order indicators, actual Gamma1 finite-place exhaustion and finite-coordinate curve geometry. Searched pinned Mathlib valuation/approximation files; the existing proved project indicators directly satisfy the required order contract. No new general valuation approximation theory is needed.',
 shorterRoute='Reuse actual closed residues for pairwise separation, adapt the finite induction already proved for the original Gamma0 field, and apply the generic prescribed-order indicators. Subtract the actual principal divisor with the prescribed orders on the finite support of j, then use actual finite-place exhaustion. This serves both the existing global-chart route and the candidate modular-period route; no cusp atlas is required for this moving step.',
 assumptionsToDischarge=['Prescribe arbitrary integral orders at a finite set of actual Gamma1 places without an approximation certificate.',
 'Every actual divisor is a principal degree-zero divisor plus a pushforward from upper-half-plane points; if the original degree is zero then the analytic coefficient sum is zero.'],
 remaining='Actual Picard/period isomorphism, Hecke/diamond/full-parabolic arithmetic comparison, original all-weight characteristic-zero association and literal higher symmetric-power continuation. The candidate modular-period route still requires proved period surjectivity, reciprocity, field realization and cusp-order control. 16/20; DUB-17--20 OPEN.',
 sourceContract='Actual integral-ratio function fields and places, all nonzero levels, original divisor degrees and principal relation. No supplied divisor-moving result, approximation or analytic exhaustion.',rootPinsChanged=False,proofLimitsChanged=False)
with (p/'gamma-one-divisor-moving-route-738.json').open('x',encoding='utf-8') as f:json.dump(route,f,indent=2);f.write('\n')
s=(d/'SourceOriginalFinitePlaceSeparation.lean').read_text(encoding='utf-8')
s=s[s.index('theorem exists_original_polar_regular_separator'):s.index('\nend\n')]
s=s.replace('exists_original_polar_regular_separator','exists_polar_regular_separator')
s=s.replace('modularFunctionFieldOver N ℂ','functionFieldOver Γ ℂ')
s=s.replace('original_places_separating_function N w₀ v hvw₀.symm',
 'Place.exists_order_separating_function w₀ v (place_residue_bijective hT w₀) hvw₀.symm')
header='''import Dubon2026.SourceGammaOneAnalyticResidues
import Dubon2026.SourceCurveRationalPlaceSeparation
import Dubon2026.SourceCurvePrescribedOrders
import Dubon2026.SourceCurveOrderUnitPerturbation

/-! DUB-17/18 -> actual Gamma1 Picard-period comparison -> moving divisors
away from the j poles. Reuse the existing original finite-separation induction,
actual closed residues and proved finite-place indicators. No approximation
hypothesis or new general valuation framework is introduced.
The original induction was adapted from anthropics/fermats-last-theorem,
Apache-2.0, commit 6e837e75355538c7f80bab5b956861e86c4eacc2,
S_AlgebraicCurve_Place_exists_forall_ord_eq. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open SourceCurve
open scoped MatrixGroups
variable {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)

'''
tail='''
theorem exists_prescribed_place_orders
    (S : Finset (Place ℂ (functionFieldOver Γ ℂ)))
    (n : Place ℂ (functionFieldOver Γ ℂ) → ℤ) :
    ∃ f : functionFieldOver Γ ℂ, f ≠ 0 ∧ ∀ v ∈ S, v.ord f = n v := by
  classical
  apply Place.exists_forall_ord_eq_of_sep S n
  intro v _
  obtain ⟨z, hz, hw⟩ := exists_polar_regular_separator hT (S.erase v)
    (Finset.notMem_erase v S)
  exact ⟨z, hz, fun w hwS hwv => hw w (Finset.mem_erase.mpr ⟨hwv, hwS⟩)⟩

end
end Dubon2026.SourceFunctionField.GammaOne
'''
with (p/'SourceGammaOnePrescribedPlaceOrders.lean').open('x',encoding='utf-8',newline='\n') as f:f.write(header+s+tail)
print(json.dumps(dict(route='gamma-one-divisor-moving-route-738.json',module='SourceGammaOnePrescribedPlaceOrders',productionMutation=False)))
