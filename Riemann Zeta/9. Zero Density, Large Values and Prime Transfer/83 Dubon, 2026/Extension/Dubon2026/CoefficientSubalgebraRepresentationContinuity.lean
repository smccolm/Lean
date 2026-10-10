import Dubon2026.MatrixRepresentationStrictConjugacy
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Topology.Algebra.Algebra

/-! # Genuine continuity descends through the original coefficient-subalgebra inclusion -/

namespace Dubon2026
noncomputable section
open Matrix

variable {G ι O R : Type*} [Fintype ι] [DecidableEq ι]
  [CommRing O] [CommRing R] [Algebra O R]
  [TopologicalSpace G] [TopologicalSpace R]

/-- The genuine original coefficient-subalgebra topology reflects continuity of whole invertible-matrix families, including both matrix and inverse entries. -/
theorem generalLinearSubalgebra_continuous (S : Subalgebra O R)
    (τ : G → GeneralLinearGroup ι S)
    (hτ : Continuous (fun g => GeneralLinearGroup.map S.val.toRingHom (τ g))) :
    Continuous τ := by
  apply Units.continuous_iff.mpr
  constructor
  · apply continuous_matrix
    intro i j
    exact (((continuous_apply_apply i j).comp
      ((Units.continuous_val (M := Matrix ι ι R)).comp hτ))).subtype_mk _
  · apply continuous_matrix
    intro i j
    exact (((continuous_apply_apply i j).comp
      ((Units.continuous_coe_inv (M := Matrix ι ι R)).comp hτ))).subtype_mk _

/-- If the original continuous representation is strictly conjugate to the actual coefficient extension of a whole subalgebra representation, that same subalgebra representation is continuous in its inherited original topology. -/
theorem matrixStrictlyConjugate_subalgebra_continuous [Group G] [IsTopologicalRing R]
    {K : Type*} [CommRing K] (r : R →+* K)
    (S : Subalgebra O R) (ρ : G →* GeneralLinearGroup ι R) (hρ : Continuous ρ)
    (τ : G →* GeneralLinearGroup ι S)
    (h : MatrixStrictlyConjugate r ((GeneralLinearGroup.map S.val.toRingHom).comp τ) ρ) :
    Continuous τ := by
  obtain ⟨U, _hU, h⟩ := h
  apply generalLinearSubalgebra_continuous S τ
  have heq : (fun g => GeneralLinearGroup.map S.val.toRingHom (τ g)) =
      (fun g => U⁻¹ * ρ g * U) := by
    funext g
    rw [h g]
    simp only [MonoidHom.comp_apply, mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]
  rw [heq]
  exact (continuous_const.mul hρ).mul continuous_const

end
end Dubon2026
