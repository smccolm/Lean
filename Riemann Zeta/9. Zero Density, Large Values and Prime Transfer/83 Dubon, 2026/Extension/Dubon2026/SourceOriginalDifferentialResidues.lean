import Dubon2026.SourceOriginalSimpleFiberSum
import Dubon2026.SourceCurveCoordinateDerivation

/-! DUB-17/18 -> original torsion cardinality -> Abel-Jacobi converse ->
prescribed residues. Reuse the native local differential coefficient map,
the original canonical local residue and trace. Their composition is linear
on all original differentials. At simple poles it is the literal value of
the uniformizer times the coefficient, as required by the converse argument.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve KaehlerDifferential
variable (N : ℕ) [NeZero N]
local notation "F" => modularFunctionFieldOver N ℂ

/-- The existing local coefficient map on the original differential space. -/
def originalDifferentialCoeff (v : Place ℂ F) : Ω[F⁄ℂ] →ₗ[ℂ] F := by
  letI := original_place_dCoordGenerates N ℂ v
  letI : Nontrivial Ω[F⁄ℂ] :=
    Module.nontrivial_of_finrank_eq_succ (n := 0) (finrank_original_differentials N ℂ)
  exact v.differentialCoeffLinearMap.restrictScalars ℂ

theorem originalDifferentialCoeff_apply (v : Place ℂ F) (ω : Ω[F⁄ℂ]) :
    originalDifferentialCoeff N v ω = v.differentialCoeff ω := rfl

/-- The actual complex residue of an original differential, with trace to constants. -/
def originalDifferentialResidue (v : Place ℂ F) : Ω[F⁄ℂ] →ₗ[ℂ] ℂ :=
  (Algebra.trace ℂ v.ResidueField).comp
    ((originalCanonicalLocalResidueData N ℂ v).res.comp (originalDifferentialCoeff N v))

theorem originalDifferentialResidue_apply (v : Place ℂ F) (ω : Ω[F⁄ℂ]) :
    originalDifferentialResidue N v ω =
      Algebra.trace ℂ v.ResidueField
        ((originalCanonicalLocalResidueData N ℂ v).res (v.differentialCoeff ω)) := rfl

omit [NeZero N] in
theorem original_simple_pole_bound_iff (v : Place ℂ F) (ω : Ω[F⁄ℂ]) :
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

theorem originalDifferentialResidue_simplePole (v : Place ℂ F) (ω : Ω[F⁄ℂ])
    (hω : -1 ≤ v.ordDifferential ω) :
    originalDifferentialResidue N v ω =
      originalPlaceEval N ℂ v (v.uniformizer * v.differentialCoeff ω) := by
  have hm := (original_simple_pole_bound_iff N v ω).mp hω
  rw [originalDifferentialResidue_apply,
    original_canonicalLocalResidue_simplePole N ℂ v _ hm,
    original_trace_residue_eq_eval N v _ hm]

theorem originalDifferentialResidue_eq_zero_of_regular (v : Place ℂ F) (ω : Ω[F⁄ℂ])
    (hω : 0 ≤ v.ordDifferential ω) : originalDifferentialResidue N v ω = 0 := by
  rw [originalDifferentialResidue_apply,
    (originalCanonicalLocalResidueData N ℂ v).res_of_mem _ (v.mem_of_ord_nonneg hω), map_zero]

theorem originalDifferentialResidue_ne_zero_of_simplePole (v : Place ℂ F) (ω : Ω[F⁄ℂ])
    (hω : v.ordDifferential ω = -1) : originalDifferentialResidue N v ω ≠ 0 := by
  have hc : v.differentialCoeff ω ≠ 0 := by
    intro he
    simp only [Place.ordDifferential, he, v.ord_zero] at hω
    norm_num at hω
  have ho : v.ord (v.uniformizer * v.differentialCoeff ω) = 0 := by
    rw [v.ord_mul v.uniformizer_ne_zero hc, v.ord_uniformizer]
    change 1 + v.ordDifferential ω = 0
    rw [hω]
    norm_num
  rw [originalDifferentialResidue_simplePole N v ω (by omega)]
  intro he
  have hp := (originalPlaceEval_eq_zero_iff_ord_pos N ℂ v
    ((original_simple_pole_bound_iff N v ω).mp (by omega))
    (mul_ne_zero v.uniformizer_ne_zero hc)).mp he
  rw [ho] at hp
  exact (lt_irrefl 0) hp

end
end Dubon2026.SourceFunctionField
