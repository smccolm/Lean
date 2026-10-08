import Dubon2026.RealProjectivePetersson
import Mathlib.MeasureTheory.Function.L2Space

/-! # Faithful L2 realization of the original cyclic representation -/

namespace Dubon2026

noncomputable section
open UpperHalfPlane Matrix.SpecialLinearGroup CongruenceSubgroup MeasureTheory
open scoped MatrixGroups Pointwise

/-- A continuous arithmetic-invariant function vanishing almost everywhere on the genuine domain vanishes everywhere. -/
theorem realProjective_invariant_eq_zero {Q : ℕ} [NeZero Q] {F : PSL(2, ℝ) → ℂ}
    (hF : Continuous F) (hInv : ∀ (γ : projectiveGamma0 Q) q, F (γ • q) = F q)
    (hz : F =ᵐ[realProjectiveMeasure.restrict (realProjectiveGamma0Domain Q)] 0) : F = 0 := by
  have hT : MeasurableSet {q : PSL(2, ℝ) | F q ≠ 0} :=
    (isOpen_ne_fun hF continuous_const).measurableSet
  have hnull : realProjectiveMeasure
      ({q : PSL(2, ℝ) | F q ≠ 0} ∩ realProjectiveGamma0Domain Q) = 0 := by
    have he := ae_iff.mp hz
    change (realProjectiveMeasure.restrict (realProjectiveGamma0Domain Q))
      {q : PSL(2, ℝ) | F q ≠ 0} = 0 at he
    rwa [Measure.restrict_apply hT] at he
  have hall := (realProjectiveGamma0Domain_isFundamental Q).measure_zero_of_invariant
    {q : PSL(2, ℝ) | F q ≠ 0} (fun γ => by
      ext q
      rw [Set.mem_smul_set_iff_inv_smul_mem]
      change F (γ⁻¹ • q) ≠ 0 ↔ F q ≠ 0
      rw [hInv]) hnull
  exact Measure.eq_of_ae_eq (ae_iff.mpr hall) hF continuous_const

/-- Descent preserves the original vector-space addition pointwise. -/
theorem realProjectiveCyclicVector_add {Q : ℕ} {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k)
    (v w : (realLiftCyclicRepresentation k f).toSubmodule) :
    realProjectiveCyclicVector f (v + w) =
      realProjectiveCyclicVector f v + realProjectiveCyclicVector f w := by
  funext q
  induction q using Quotient.inductionOn with | h g => rfl

/-- Descent preserves the original scalar multiplication pointwise. -/
theorem realProjectiveCyclicVector_smul {Q : ℕ} {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k)
    (c : ℂ) (v : (realLiftCyclicRepresentation k f).toSubmodule) :
    realProjectiveCyclicVector f (c • v) = c • realProjectiveCyclicVector f v := by
  funext q
  induction q using Quotient.inductionOn with | h g => rfl

/-- The literal cyclic cusp representation maps linearly into actual L2 on the true arithmetic domain. -/
def realProjectiveCyclicToL2 {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k) :
    (realLiftCyclicRepresentation k f).toSubmodule →ₗ[ℂ]
      Lp ℂ 2 (realProjectiveMeasure.restrict (realProjectiveGamma0Domain Q)) where
  toFun v := (realProjectiveCyclicVector_memLp_two f v).toLp (realProjectiveCyclicVector f v)
  map_add' v w := by
    rw [← MemLp.toLp_add]
    apply MemLp.toLp_congr
    exact Filter.Eventually.of_forall (congrFun (realProjectiveCyclicVector_add f v w))
  map_smul' c v := by
    rw [← MemLp.toLp_const_smul]
    apply MemLp.toLp_congr
    exact Filter.Eventually.of_forall (congrFun (realProjectiveCyclicVector_smul f c v))

/-- No original cyclic vector disappears in the actual quotient L2 realization. -/
theorem realProjectiveCyclicToL2_injective {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k) :
    Function.Injective (realProjectiveCyclicToL2 f) := by
  intro v w he
  have hae : realProjectiveCyclicVector f v =ᵐ[
      realProjectiveMeasure.restrict (realProjectiveGamma0Domain Q)] realProjectiveCyclicVector f w :=
    (MemLp.toLp_eq_toLp_iff (realProjectiveCyclicVector_memLp_two f v)
      (realProjectiveCyclicVector_memLp_two f w)).mp he
  have hz : realProjectiveCyclicVector f v - realProjectiveCyclicVector f w = 0 := by
    apply realProjective_invariant_eq_zero (Q := Q)
      ((realProjectiveCyclicVector_continuous f v).sub (realProjectiveCyclicVector_continuous f w))
    · intro γ q
      simp only [realProjectiveCyclicVector_arithmetic]
    · filter_upwards [hae] with q hq
      simp only [hq, sub_self, Pi.zero_apply]
  apply Subtype.ext
  funext g
  have h := congrFun hz (QuotientGroup.mk g)
  exact sub_eq_zero.mp h

end
end Dubon2026
