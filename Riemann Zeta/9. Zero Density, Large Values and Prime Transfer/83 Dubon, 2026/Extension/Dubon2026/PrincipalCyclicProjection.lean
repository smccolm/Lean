import Dubon2026.PrincipalDivisorProjection
import Dubon2026.FiniteCyclicRepresentation

/-! # The actual divisor averages on finite-dimensional principal cusp orbits -/

namespace Dubon2026

open Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

noncomputable section
attribute [local instance] principalNormal

/-- The finite congruence element giving positive translation by N/d in the inverse-slash action. -/
def principalCyclicGenerator (N d : ℕ) : SL(2, ℤ) ⧸ Gamma N :=
  QuotientGroup.mk (ModularGroup.T ^ (-((N / d : ℕ) : ℤ)))

/-- Its d-th power is actually trivial in the principal congruence quotient. -/
theorem principalCyclicGenerator_pow {N d : ℕ} (hd : d ∣ N) :
    principalCyclicGenerator N d ^ d = 1 := by
  unfold principalCyclicGenerator
  rw [← QuotientGroup.mk_pow, ← zpow_natCast, ← zpow_mul]
  have he : -((N / d : ℕ) : ℤ) * (d : ℤ) = -(N : ℤ) := by
    rw [neg_mul, ← Nat.cast_mul, Nat.div_mul_cancel hd]
  rw [he]
  apply (QuotientGroup.eq_one_iff _).mpr
  simpa only [Int.natAbs_natCast] using
    ModularGroup_T_pow_mem_Gamma (N : ℤ) (-(N : ℤ)) (dvd_neg.mpr (dvd_refl _))

/-- Natural powers of the finite generator have the exact integral translation representative. -/
theorem principalCyclicGenerator_pow_mk (N d b : ℕ) :
    principalCyclicGenerator N d ^ b =
      QuotientGroup.mk ((ModularGroup.T ^ ((b * (N / d) : ℕ) : ℤ))⁻¹) := by
  unfold principalCyclicGenerator
  rw [← QuotientGroup.mk_pow]
  congr 1
  rw [← zpow_natCast, ← zpow_mul, ← zpow_neg]
  congr 1
  push_cast
  ring1

/-- The cyclic representation on actual principal forms recovers every literal translation summand. -/
theorem principalCyclicRepresentation_natCast {N d : ℕ} (hd : d ∣ N) (k : ℤ) (b : ℕ) :
    finiteCyclicRepresentation (principalCuspRepresentation N k) d (principalCyclicGenerator N d)
      (principalCyclicGenerator_pow hd) (Multiplicative.ofAdd (b : ZMod d)) =
        principalTranslation N k (b * (N / d) : ℕ) := by
  have h := finiteCyclicHom_intCast d (principalCyclicGenerator N d)
    (principalCyclicGenerator_pow hd) (b : ℤ)
  simp only [Int.cast_natCast, zpow_natCast] at h
  simp only [finiteCyclicRepresentation, MonoidHom.comp_apply, h, principalCyclicGenerator_pow_mk]
  rfl

/-- The coefficient-extracting translation average is exactly Mathlib's finite cyclic-group projection. -/
theorem principalDivisorProjection_eq_group {N d : ℕ} [NeZero d] (hd : d ∣ N) (k : ℤ) :
    principalDivisorProjection N k d =
      finiteGroupProjection (finiteCyclicRepresentation (principalCuspRepresentation N k) d
        (principalCyclicGenerator N d) (principalCyclicGenerator_pow hd)) := by
  rw [finiteCyclicProjection_eq]
  unfold principalDivisorProjection
  apply congrArg (fun A : Module.End ℂ (CuspForm ((Gamma N).map (mapGL ℝ)) k) => (d : ℂ)⁻¹ • A)
  apply Finset.sum_congr rfl
  intro b _
  rw [principalCyclicGenerator_pow_mk]
  rfl

/-- The same cyclic average acts on the actual finite-dimensional orbit span. -/
def principalOrbitDivisorProjection {N d : ℕ} [NeZero d] (hd : d ∣ N) (k : ℤ)
    (f : CuspForm ((Gamma N).map (mapGL ℝ)) k) :
    principalCuspOrbit N k f →ₗ[ℂ] principalCuspOrbit N k f :=
  finiteGroupProjection (finiteCyclicRepresentation (principalCuspOrbitRepresentation N k f) d
    (principalCyclicGenerator N d) (principalCyclicGenerator_pow hd))

/-- The restricted finite-dimensional average has exactly the same underlying cusp form. -/
theorem principalOrbitDivisorProjection_val {N d : ℕ} [NeZero d] (hd : d ∣ N) (k : ℤ)
    (f : CuspForm ((Gamma N).map (mapGL ℝ)) k) (v : principalCuspOrbit N k f) :
    (principalOrbitDivisorProjection hd k f v).val = principalDivisorProjection N k d v.val := by
  unfold principalOrbitDivisorProjection
  rw [finiteCyclicProjection_eq, principalDivisorProjection_eq_group hd, finiteCyclicProjection_eq]
  simp only [LinearMap.smul_apply, LinearMap.sum_apply, Submodule.coe_smul,
    Submodule.coe_sum, principalCuspOrbitRepresentation, Representation.subrepresentation_apply]
  rfl

end
end Dubon2026
