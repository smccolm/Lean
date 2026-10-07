import Dubon2026.ModularDegeneracy
import Dubon2026.ModularCosetProjection

/-! # The genuine mixed congruence subgroup from rectangular lattice rescaling -/

namespace Dubon2026

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

noncomputable section

/-- The actual integral subgroup whose upper-right entry is divisible by a and lower-left entry by b. -/
def rectangularCongruenceSubgroup (a b : ℕ) : Subgroup SL(2, ℤ) where
  carrier := {g | (a : ℤ) ∣ g 0 1 ∧ (b : ℤ) ∣ g 1 0}
  one_mem' := by simp
  mul_mem' := by
    intro g h hg hh
    change (a : ℤ) ∣ (g * h) 0 1 ∧ (b : ℤ) ∣ (g * h) 1 0
    simp only [coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    exact ⟨dvd_add (dvd_mul_of_dvd_right hh.1 _) (dvd_mul_of_dvd_left hg.1 _),
      dvd_add (dvd_mul_of_dvd_left hg.2 _) (dvd_mul_of_dvd_right hh.2 _)⟩
  inv_mem' := by
    intro g hg
    change (a : ℤ) ∣ g⁻¹ 0 1 ∧ (b : ℤ) ∣ g⁻¹ 1 0
    rw [SL2_inv_expl g]
    simpa using And.intro (dvd_neg.mpr hg.1) (dvd_neg.mpr hg.2)

/-- Membership retains both literal divisibility conditions. -/
theorem mem_rectangularCongruenceSubgroup (a b : ℕ) (g : SL(2, ℤ)) :
    g ∈ rectangularCongruenceSubgroup a b ↔ (a : ℤ) ∣ g 0 1 ∧ (b : ℤ) ∣ g 1 0 := Iff.rfl

/-- The mixed rescaled subgroup contains the genuine principal subgroup at the product level. -/
theorem Gamma_le_rectangularCongruenceSubgroup (a b : ℕ) :
    Gamma (a * b) ≤ rectangularCongruenceSubgroup a b := by
  intro g hg
  have hm := Gamma_mem.mp hg
  have ha := (ZMod.intCast_zmod_eq_zero_iff_dvd (g 0 1) (a * b)).mp hm.2.1
  have hb := (ZMod.intCast_zmod_eq_zero_iff_dvd (g 1 0) (a * b)).mp hm.2.2.1
  exact ⟨dvd_trans (by exact_mod_cast (dvd_mul_right a b)) ha,
    dvd_trans (by exact_mod_cast (dvd_mul_left b a)) hb⟩

/-- Every positive rectangular rescaling has a genuinely finite coset space. -/
instance rectangularCongruenceSubgroup_finiteIndex (a b : ℕ) [NeZero a] [NeZero b] :
    (rectangularCongruenceSubgroup a b).FiniteIndex :=
  Subgroup.finiteIndex_of_le (Gamma_le_rectangularCongruenceSubgroup a b)

/-- The actual mixed subgroup absorbs the center, so its integral and projective cosets have equal multiplicity. -/
theorem center_SL_le_rectangularCongruenceSubgroup (a b : ℕ) :
    Subgroup.center SL(2, ℤ) ≤ rectangularCongruenceSubgroup a b := by
  intro g hg
  obtain ⟨r, _, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hg
  have h01 : g 0 1 = 0 := by
    have he := congrFun (congrFun hr 0) 1
    simpa [Matrix.scalar] using he.symm
  have h10 : g 1 0 = 0 := by
    have he := congrFun (congrFun hr 1) 0
    simpa [Matrix.scalar] using he.symm
  change (a : ℤ) ∣ g 0 1 ∧ (b : ℤ) ∣ g 1 0
  simp [h01, h10]

/-- The existing integral conjugation matrix maps the original Gamma0(ab) into the exact mixed subgroup. -/
theorem levelRaiseConjOfDvd_mem_rectangularCongruence (a b : ℕ) [NeZero a]
    (g : SL(2, ℤ)) (hg : g ∈ Gamma0 (a * b)) :
    levelRaiseConjOfDvd a g (Gamma0_dmul_lower_left_dvd a b g hg) ∈ rectangularCongruenceSubgroup a b := by
  change (a : ℤ) ∣ a * g 0 1 ∧ (b : ℤ) ∣ g 1 0 / a
  constructor
  · exact dvd_mul_right _ _
  · obtain ⟨j, hj⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp hg)
    refine ⟨j, ?_⟩
    rw [hj]
    push_cast
    rw [mul_assoc, Int.mul_ediv_cancel_left _ (Nat.cast_ne_zero.mpr (NeZero.ne a))]

end
end Dubon2026
