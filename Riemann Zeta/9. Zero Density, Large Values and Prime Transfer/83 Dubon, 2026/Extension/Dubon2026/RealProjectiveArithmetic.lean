import Dubon2026.RealProjectiveOrbit
import Dubon2026.ProjectiveEisensteinCosets

/-! # The actual arithmetic action and genuine projective fundamental domain -/

namespace Dubon2026

noncomputable section
open Matrix Matrix.SpecialLinearGroup UpperHalfPlane MeasureTheory
open scoped MatrixGroups Pointwise

/-- Actual integer matrix extension into the real determinant-one group. -/
def integralToRealSL : SL(2, ℤ) →* SL(2, ℝ) :=
  Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)

/-- Actual extension preserves the negative scalar identity. -/
theorem integralToRealSL_neg_one : integralToRealSL (-1) = -1 := by
  ext i j
  by_cases hij : i = j <;>
    simp [integralToRealSL, Matrix.SpecialLinearGroup.map, coe_neg, hij]

/-- The real projective homomorphism is induced by the original integer matrix extension. -/
def integralToRealPSL : PSL(2, ℤ) →* PSL(2, ℝ) :=
  QuotientGroup.lift (Subgroup.center SL(2, ℤ))
    ((QuotientGroup.mk' (Subgroup.center SL(2, ℝ))).comp integralToRealSL) (by
      intro g hg
      change (QuotientGroup.mk (integralToRealSL g) : PSL(2, ℝ)) = 1
      apply (QuotientGroup.eq_one_iff _).mpr
      rw [realSL2_center_eq_signs]
      rcases SL2_center_eq_one_or_neg_one g hg with rfl | rfl
      · exact Or.inl (map_one integralToRealSL)
      · exact Or.inr integralToRealSL_neg_one)

/-- The actual projective integral map uses the original matrix representative. -/
theorem integralToRealPSL_mk (g : SL(2, ℤ)) :
    integralToRealPSL (QuotientGroup.mk g) = QuotientGroup.mk (integralToRealSL g) := rfl

/-- The original real action agrees with the original integer action after coefficient extension. -/
theorem integralToRealSL_smul (g : SL(2, ℤ)) (z : ℍ) : integralToRealSL g • z = g • z := by
  rfl

instance realProjectiveModularAction : MulAction PSL(2, ℤ) PSL(2, ℝ) :=
  MulAction.compHom _ integralToRealPSL

instance realProjective_modularContinuousConstSMul : ContinuousConstSMul PSL(2, ℤ) PSL(2, ℝ) where
  continuous_const_smul g := show Continuous (fun q => integralToRealPSL g * q) from
    continuous_const.mul continuous_id

instance realProjective_modularInvariantMeasure :
    SMulInvariantMeasure PSL(2, ℤ) PSL(2, ℝ) realProjectiveMeasure where
  measure_preimage_smul g S _hS :=
    measure_preimage_mul realProjectiveMeasure (integralToRealPSL g) S

/-- The true quotient orbit intertwines the actual arithmetic actions. -/
theorem realProjectiveOrbit_integral_smul (g : PSL(2, ℤ)) (q : PSL(2, ℝ)) :
    realProjectiveOrbit (g • q) = g • realProjectiveOrbit q := by
  induction g using Quotient.inductionOn with | h a => ?_
  change realProjectiveOrbit (QuotientGroup.mk (integralToRealSL a) * q) =
    a • realProjectiveOrbit q
  rw [realProjectiveOrbit_mul, integralToRealSL_smul]

/-- The full compact fiber over the original base domain, now in the genuine central quotient. -/
def realProjectiveGamma0Domain (Q : ℕ) : Set PSL(2, ℝ) :=
  realProjectiveOrbit ⁻¹' gamma0FundamentalDomain Q

/-- The actual projective group integration region is open and hence Borel measurable. -/
theorem realProjectiveGamma0Domain_isOpen (Q : ℕ) :
    IsOpen (realProjectiveGamma0Domain Q) := by
  apply realProjectiveOrbit_continuous.isOpen_preimage
  exact isOpen_iUnion (fun q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 Q =>
    ModularGroup.isOpen_fdo.smul ((q.out : SL(2, ℤ))⁻¹))

/-- The original projective arithmetic tiling lifts to an actual projective group fundamental domain. -/
theorem realProjectiveGamma0Domain_isFundamental (Q : ℕ) [NeZero Q] :
    IsFundamentalDomain (projectiveGamma0 Q) (realProjectiveGamma0Domain Q)
      realProjectiveMeasure := by
  apply (isFundamentalDomain_gamma0 Q).preimage_of_equiv
    realProjectiveOrbit_measurePreserving.quasiMeasurePreserving (Function.bijective_id)
  intro g q
  exact realProjectiveOrbit_integral_smul g.val q

/-- The actual projective group fundamental domain has the original finite hyperbolic volume. -/
theorem realProjectiveGamma0Domain_volume (Q : ℕ) [NeZero Q] :
    realProjectiveMeasure (realProjectiveGamma0Domain Q) = volume (gamma0FundamentalDomain Q) :=
  realProjectiveOrbit_measurePreserving.measure_preimage
    (isFundamentalDomain_gamma0 Q).nullMeasurableSet

/-- The genuine projective arithmetic quotient has a finite-volume fundamental domain. -/
theorem realProjectiveGamma0Domain_volume_lt_top (Q : ℕ) [NeZero Q] :
    realProjectiveMeasure (realProjectiveGamma0Domain Q) < ⊤ := by
  rw [realProjectiveGamma0Domain_volume]
  exact gamma0FundamentalDomain_volume_lt_top Q

end
end Dubon2026
