import Dubon2026.SourceGammaOneAnalyticResidues
import Dubon2026.SourceCurveRationalResidueTrace
import Dubon2026.SourceCurveCoordinateDerivation
import Dubon2026.SourceCurveCanonicalResidueData

/-! DUB-17/18 -> original Gamma1 Picard/H1 -> principal-divisor converse ->
prescribed meromorphic function -> prescribed-residue differential.
Instantiate the native canonical local residue and linear differential
coefficient at the actual subgroup field. This is the existing original
and cover residue argument, with the actual proved subgroup-field
differential generation and rational residue fields. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open SourceCurve KaehlerDifferential
open scoped MatrixGroups
variable {Γ: Subgroup SL(2, ℤ)} [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)
local notation "EE" => functionFieldOver Γ ℂ

/-- Canonical local residue data at a place of the actual subgroup field. -/
def differentialCanonicalLocalResidueData (v : Place ℂ EE) : v.CanonicalLocalResidueDataK :=
  v.canonicalLocalResidueData (place_residue_bijective hT v).2

/-- The existing local coefficient map on the actual subgroup differential space. -/
def differentialCoeff (v : Place ℂ EE) : Ω[EE⁄ℂ] →ₗ[ℂ] EE := by
  letI := functionFieldOver_dCoordGenerates Γ ℂ hT v
  letI := nontrivial_of_ne _ _ (D_jCoordinateOver_ne_zero Γ ℂ)
  exact v.differentialCoeffLinearMap.restrictScalars ℂ

theorem differentialCoeff_apply (v : Place ℂ EE) (ω : Ω[EE⁄ℂ]) :
    differentialCoeff hT v ω = v.differentialCoeff ω := rfl

/-- The actual complex residue of a differential of the actual subgroup field, with trace to constants. -/
def differentialResidue (v : Place ℂ EE) : Ω[EE⁄ℂ] →ₗ[ℂ] ℂ :=
  (Algebra.trace ℂ v.ResidueField).comp
    ((differentialCanonicalLocalResidueData hT v).res.comp (differentialCoeff hT v))

theorem differentialResidue_apply (v : Place ℂ EE) (ω : Ω[EE⁄ℂ]) :
    differentialResidue hT v ω =
      Algebra.trace ℂ v.ResidueField
        ((differentialCanonicalLocalResidueData hT v).res (v.differentialCoeff ω)) := rfl

omit [Γ.FiniteIndex] in
theorem simple_pole_bound_iff (v : Place ℂ EE) (ω : Ω[EE⁄ℂ]) :
    -1 ≤ v.ordDifferential ω ↔ v.uniformizer * v.differentialCoeff ω ∈ v.toValuationSubring := by
  by_cases hc : v.differentialCoeff ω = 0
  · simp only [Place.ordDifferential, hc, v.ord_zero, mul_zero]
    exact ⟨fun _ => zero_mem _, fun _ => by norm_num⟩
  have he := v.ord_mul v.uniformizer_ne_zero hc
  rw [v.ord_uniformizer] at he
  constructor
  · intro h
    apply v.mem_of_ord_nonneg
    rw [he]
    change -1 ≤ v.ord (v.differentialCoeff ω) at h
    omega
  · intro h
    have ho := v.ord_nonneg_of_mem h
    rw [he] at ho
    change -1 ≤ v.ord (v.differentialCoeff ω)
    omega

theorem differentialResidue_simplePole (v : Place ℂ EE) (ω : Ω[EE⁄ℂ])
    (hω : -1 ≤ v.ordDifferential ω) :
    differentialResidue hT v ω =
      v.rationalEval (place_residue_bijective hT v) (v.uniformizer * v.differentialCoeff ω) := by
  have hm := (simple_pole_bound_iff v ω).mp hω
  rw [differentialResidue_apply,
    (differentialCanonicalLocalResidueData hT v).res_simplePole _ hm,
    v.trace_residue_eq_rationalEval (place_residue_bijective hT v) _ hm]

theorem differentialResidue_eq_zero_of_regular (v : Place ℂ EE) (ω : Ω[EE⁄ℂ])
    (hω : 0 ≤ v.ordDifferential ω) : differentialResidue hT v ω = 0 := by
  rw [differentialResidue_apply,
    (differentialCanonicalLocalResidueData hT v).res_of_mem _ (v.mem_of_ord_nonneg hω), map_zero]

theorem differentialResidue_ne_zero_of_simplePole (v : Place ℂ EE) (ω : Ω[EE⁄ℂ])
    (hω : v.ordDifferential ω = -1) : differentialResidue hT v ω ≠ 0 := by
  have hc : v.differentialCoeff ω ≠ 0 := by
    intro he
    simp only [Place.ordDifferential, he, v.ord_zero] at hω
    norm_num at hω
  have ho : v.ord (v.uniformizer * v.differentialCoeff ω) = 0 := by
    rw [v.ord_mul v.uniformizer_ne_zero hc, v.ord_uniformizer]
    change 1 + v.ordDifferential ω = 0
    rw [hω]
    norm_num
  rw [differentialResidue_simplePole hT v ω (by omega)]
  intro he
  have hp := (v.rationalEval_eq_zero_iff_ord_pos (place_residue_bijective hT v)
    ((simple_pole_bound_iff v ω).mp (by omega))
    (mul_ne_zero v.uniformizer_ne_zero hc)).mp he
  rw [ho] at hp
  exact (lt_irrefl 0) hp


end
end Dubon2026.SourceFunctionField.GammaOne
