import Dubon2026.SourceModularCoefficientLocalFinite
import Dubon2026.SourceCurveIntegralDerivatives

/-! DUB-17/18 -> good reduction -> reverse genus inequality -> actual
residue differential orders. Finiteness on the two j charts and separable
residue constants generate the integral local differentials. Since j and
its inverse have nonzero differentials, the actual uniformizer differential
is nonzero at every place. The proved rank-one theorem then supplies its
spanning property, without a new uniformizer-separability development. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve KaehlerDifferential
variable (N : ℕ) [NeZero N] (K : Type*) [Field K] [PerfectField K]

theorem coeff_place_dCoord_ne_zero (v : Place K (modularFunctionFieldCoeff N K)) :
    v.dCoord ≠ 0 := by
  haveI := finite_coeff_place_differentials N K v
  haveI := coeff_place_residue_isAlgebraic N K v
  haveI : Algebra.IsSeparable K v.ResidueField := inferInstance
  intro hz
  have hzero : ∀ f : modularFunctionFieldCoeff N K, f ∈ v.toValuationSubring →
      D K (modularFunctionFieldCoeff N K) f = 0 := by
    intro f hf
    obtain ⟨g, _, hg⟩ := v.exists_integral_D_eq_smul_dCoord hf
    rw [hg, hz, smul_zero]
  rcases v.toValuationSubring.mem_or_inv_mem (jCoeff N K) with hj | hj
  · exact D_jCoeff_ne_zero N K (hzero _ hj)
  · have hi := hzero _ hj
    rw [Derivation.leibniz_inv] at hi
    have hj0 : jCoeff N K ≠ 0 := fun h => transcendental_jCoeff N K (h ▸ isAlgebraic_zero)
    exact D_jCoeff_ne_zero N K ((smul_eq_zero.mp hi).resolve_left
      (neg_ne_zero.mpr (pow_ne_zero _ (inv_ne_zero hj0))))

theorem coeff_place_dCoordGenerates (v : Place K (modularFunctionFieldCoeff N K)) :
    v.DCoordGenerates :=
  ⟨(finrank_eq_one_iff_of_nonzero _ (coeff_place_dCoord_ne_zero N K v)).mp
    (finrank_coeff_differentials N K)⟩

theorem coeff_place_integral_derivative_nonneg (v : Place K (modularFunctionFieldCoeff N K))
    {f : modularFunctionFieldCoeff N K} (hf : f ∈ v.toValuationSubring) :
    0 ≤ v.ordDifferential (D K (modularFunctionFieldCoeff N K) f) := by
  haveI := finite_coeff_place_differentials N K v
  haveI := coeff_place_residue_isAlgebraic N K v
  haveI : Algebra.IsSeparable K v.ResidueField := inferInstance
  haveI := coeff_place_dCoordGenerates N K v
  haveI : Nontrivial Ω[modularFunctionFieldCoeff N K⁄K] :=
    Module.nontrivial_of_finrank_eq_succ (n := 0) (finrank_coeff_differentials N K)
  exact v.ordDifferential_D_nonneg_of_mem hf

end
end Dubon2026.SourceFunctionField
