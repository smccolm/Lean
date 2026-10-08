import Dubon2026.AdelicProjectivePairing
import Mathlib.MeasureTheory.Function.L2Space

/-! # Faithful genuine L2 realization of the original full adelic cyclic space -/

namespace Dubon2026

noncomputable section
open UpperHalfPlane Matrix.SpecialLinearGroup CongruenceSubgroup MeasureTheory
open scoped MatrixGroups Pointwise

/-- A continuous invariant original adelic function vanishing almost everywhere on the genuine arithmetic domain vanishes everywhere. -/
theorem adelicProjective_invariant_eq_zero {N : ℕ} [NeZero N] {F : AdelicProjectiveGroup → ℂ}
    (hF : Continuous F) (hInv : ∀ (γ : adelicProjectiveArithmetic) p, F (γ • p) = F p)
    (hz : F =ᵐ[adelicProjectiveMeasure.restrict (adelicProjectiveGamma0Domain N)] 0) : F = 0 := by
  have hT : MeasurableSet {p : AdelicProjectiveGroup | F p ≠ 0} :=
    (isOpen_ne_fun hF continuous_const).measurableSet
  have hnull : adelicProjectiveMeasure
      ({p : AdelicProjectiveGroup | F p ≠ 0} ∩ adelicProjectiveGamma0Domain N) = 0 := by
    have he := ae_iff.mp hz
    change (adelicProjectiveMeasure.restrict (adelicProjectiveGamma0Domain N))
      {p : AdelicProjectiveGroup | F p ≠ 0} = 0 at he
    rwa [Measure.restrict_apply hT] at he
  have hall := (adelicProjectiveGamma0Domain_isFundamental N).measure_zero_of_invariant
    {p : AdelicProjectiveGroup | F p ≠ 0} (fun γ => by
      ext p
      rw [Set.mem_smul_set_iff_inv_smul_mem]
      change F (γ⁻¹ • p) ≠ 0 ↔ F p ≠ 0
      rw [hInv]) hnull
  exact Measure.eq_of_ae_eq (ae_iff.mpr hall) hF continuous_const

/-- The original algebraic full adelic cyclic space maps linearly into actual L2 on its genuine arithmetic domain. -/
def adelicProjectiveCyclicToL2 (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) :
    (adelicLiftCyclicRepresentation N k f).toSubmodule →ₗ[ℂ]
      Lp ℂ 2 (adelicProjectiveMeasure.restrict (adelicProjectiveGamma0Domain N)) where
  toFun v := (adelicCyclicProjectiveFunction_memLp_two N f v).toLp (adelicCyclicProjectiveFunction N f v)
  map_add' v w := by
    rw [← MemLp.toLp_add]
    apply MemLp.toLp_congr
    apply Filter.Eventually.of_forall
    intro p
    exact congrArg (fun F : C(AdelicProjectiveGroup, ℂ) => F p)
      ((adelicCyclicProjectiveLinear N f).map_add v w)
  map_smul' c v := by
    rw [← MemLp.toLp_const_smul]
    apply MemLp.toLp_congr
    apply Filter.Eventually.of_forall
    intro p
    exact congrArg (fun F : C(AdelicProjectiveGroup, ℂ) => F p)
      ((adelicCyclicProjectiveLinear N f).map_smul c v)

/-- The genuine adelic quotient L2 realization loses no original algebraic cyclic vector. -/
theorem adelicProjectiveCyclicToL2_injective (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) :
    Function.Injective (adelicProjectiveCyclicToL2 N f) := by
  intro v w he
  have hae : adelicCyclicProjectiveFunction N f v =ᵐ[
      adelicProjectiveMeasure.restrict (adelicProjectiveGamma0Domain N)]
        adelicCyclicProjectiveFunction N f w :=
    (MemLp.toLp_eq_toLp_iff (adelicCyclicProjectiveFunction_memLp_two N f v)
      (adelicCyclicProjectiveFunction_memLp_two N f w)).mp he
  have hz : adelicCyclicProjectiveFunction N f v - adelicCyclicProjectiveFunction N f w = 0 := by
    apply adelicProjective_invariant_eq_zero (N := N)
      ((adelicCyclicProjectiveFunction_continuous N f v).sub
        (adelicCyclicProjectiveFunction_continuous N f w))
    · intro γ p
      change adelicCyclicProjectiveFunction N f v (γ.val * p) -
        adelicCyclicProjectiveFunction N f w (γ.val * p) = _
      rw [adelicCyclicProjectiveFunction_arithmetic_invariant,
        adelicCyclicProjectiveFunction_arithmetic_invariant]
    · filter_upwards [hae] with p hp
      simp only [hp, sub_self, Pi.zero_apply]
  exact adelicCyclicProjectiveFunction_injective N f (sub_eq_zero.mp hz)

/-- The original adelic integral pairing is exactly the inherited genuine L2 inner product. -/
theorem adelicProjectiveCyclicToL2_inner (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)
    (v w : (adelicLiftCyclicRepresentation N k f).toSubmodule) :
    inner ℂ (adelicProjectiveCyclicToL2 N f v) (adelicProjectiveCyclicToL2 N f w) =
      adelicProjectiveCyclicPairing N f v w := by
  change (∫ p, inner ℂ (adelicProjectiveCyclicToL2 N f v p)
    (adelicProjectiveCyclicToL2 N f w p) ∂(adelicProjectiveMeasure.restrict
      (adelicProjectiveGamma0Domain N))) = _
  apply integral_congr_ae
  filter_upwards [(adelicCyclicProjectiveFunction_memLp_two N f v).coeFn_toLp,
    (adelicCyclicProjectiveFunction_memLp_two N f w).coeFn_toLp] with p hv hw
  change inner ℂ (((adelicCyclicProjectiveFunction_memLp_two N f v).toLp _) p)
    (((adelicCyclicProjectiveFunction_memLp_two N f w).toLp _) p) = _
  rw [hv, hw, RCLike.inner_apply, mul_comm]

end
end Dubon2026
