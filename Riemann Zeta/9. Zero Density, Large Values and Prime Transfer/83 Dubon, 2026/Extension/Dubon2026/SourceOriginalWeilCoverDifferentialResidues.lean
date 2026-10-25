import Dubon2026.SourceOriginalWeilCoverLocalDifferentials
import Dubon2026.SourceCurveRationalResidueTrace
import Dubon2026.SourceCurveCoordinateDerivation
import Dubon2026.SourceCurveCanonicalResidueData
import Dubon2026.SourceCurveRationalResidueValues

/-! DUB-17/18 -> auxiliary point division -> cover Abel converse -> prescribed
residues. Native canonical residue data and actual rational residue evaluation
give the linear residue functional and its exact simple-pole formula. -/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve KaehlerDifferential
variable (N : ℕ) [NeZero N] (n : ℕ) (r : modularFunctionFieldOver N ℂ)
local notation "FF" => modularFunctionFieldOver N ℂ
local notation "EE" => Polynomial.SplittingField (Polynomial.X ^ n - Polynomial.C r : Polynomial FF)

/-- Canonical local residue data at a place of the actual cover. -/
def coverCanonicalLocalResidueData (v : Place ℂ EE) : v.CanonicalLocalResidueDataK :=
  v.canonicalLocalResidueData (originalWeilKummerCover_residue_bijective N ℂ n r v).2

/-- The existing local coefficient map on the cover differential space. -/
def coverDifferentialCoeff (v : Place ℂ EE) : Ω[EE⁄ℂ] →ₗ[ℂ] EE := by
  letI := cover_place_dCoordGenerates N n r v
  letI := cover_differentials_nontrivial N n r
  exact v.differentialCoeffLinearMap.restrictScalars ℂ

theorem coverDifferentialCoeff_apply (v : Place ℂ EE) (ω : Ω[EE⁄ℂ]) :
    coverDifferentialCoeff N n r v ω = v.differentialCoeff ω := rfl

/-- The actual complex residue of an cover differential, with trace to constants. -/
def coverDifferentialResidue (v : Place ℂ EE) : Ω[EE⁄ℂ] →ₗ[ℂ] ℂ :=
  (Algebra.trace ℂ v.ResidueField).comp
    ((coverCanonicalLocalResidueData N n r v).res.comp (coverDifferentialCoeff N n r v))

theorem coverDifferentialResidue_apply (v : Place ℂ EE) (ω : Ω[EE⁄ℂ]) :
    coverDifferentialResidue N n r v ω =
      Algebra.trace ℂ v.ResidueField
        ((coverCanonicalLocalResidueData N n r v).res (v.differentialCoeff ω)) := rfl

omit [NeZero N] in
theorem cover_simple_pole_bound_iff (v : Place ℂ EE) (ω : Ω[EE⁄ℂ]) :
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

theorem coverDifferentialResidue_simplePole (v : Place ℂ EE) (ω : Ω[EE⁄ℂ])
    (hω : -1 ≤ v.ordDifferential ω) :
    coverDifferentialResidue N n r v ω =
      v.rationalEval (originalWeilKummerCover_residue_bijective N ℂ n r v) (v.uniformizer * v.differentialCoeff ω) := by
  have hm := (cover_simple_pole_bound_iff N n r v ω).mp hω
  rw [coverDifferentialResidue_apply,
    (coverCanonicalLocalResidueData N n r v).res_simplePole _ hm,
    v.trace_residue_eq_rationalEval (originalWeilKummerCover_residue_bijective N ℂ n r v) _ hm]

theorem coverDifferentialResidue_eq_zero_of_regular (v : Place ℂ EE) (ω : Ω[EE⁄ℂ])
    (hω : 0 ≤ v.ordDifferential ω) : coverDifferentialResidue N n r v ω = 0 := by
  rw [coverDifferentialResidue_apply,
    (coverCanonicalLocalResidueData N n r v).res_of_mem _ (v.mem_of_ord_nonneg hω), map_zero]

theorem coverDifferentialResidue_ne_zero_of_simplePole (v : Place ℂ EE) (ω : Ω[EE⁄ℂ])
    (hω : v.ordDifferential ω = -1) : coverDifferentialResidue N n r v ω ≠ 0 := by
  have hc : v.differentialCoeff ω ≠ 0 := by
    intro he
    simp only [Place.ordDifferential, he, v.ord_zero] at hω
    norm_num at hω
  have ho : v.ord (v.uniformizer * v.differentialCoeff ω) = 0 := by
    rw [v.ord_mul v.uniformizer_ne_zero hc, v.ord_uniformizer]
    change 1 + v.ordDifferential ω = 0
    rw [hω]
    norm_num
  rw [coverDifferentialResidue_simplePole N n r v ω (by omega)]
  intro he
  have hp := (v.rationalEval_eq_zero_iff_ord_pos (originalWeilKummerCover_residue_bijective N ℂ n r v)
    ((cover_simple_pole_bound_iff N n r v ω).mp (by omega))
    (mul_ne_zero v.uniformizer_ne_zero hc)).mp he
  rw [ho] at hp
  exact (lt_irrefl 0) hp


end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
