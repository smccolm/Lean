import Dubon2026.SourceLaurentCoefficientMap

/-! DUB-17/18 -> parabolic Hecke realization -> period surjectivity ->
matching cusp-form lower dimension bound -> regular differential realization.
This selects the original Laurent-series modular function field and its
literal j series. The analytic modularity and finite extension are assembled in
SourceOriginalDifferentialInjectivity. Regularity, geometric genus and
cusp-form realization remain separate proof obligations.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
Definitions/Def_ModularCurve_X0.lean, QExpand section.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open HahnSeries IntermediateField

section QExpand

variable {R : Type*} [CommRing R]

variable (R) in

/-- The original substitution q to q raised to the nonzero level. -/
def qExpand (N : ℕ) [NeZero N] : LaurentSeries R →+* LaurentSeries R :=
  HahnSeries.embDomainRingHom (AddMonoidHom.mulLeft (N : ℤ))
    (mul_right_injective₀ (by exact_mod_cast NeZero.ne N))
    (fun g g' => mul_le_mul_iff_of_pos_left
      (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)))

variable (N : ℕ) [NeZero N]

@[simp]
theorem qExpand_coeff_mul (f : LaurentSeries R) (k : ℤ) :
    (qExpand R N f).coeff ((N : ℤ) * k) = f.coeff k :=
  HahnSeries.embDomain_coeff

theorem qExpand_coeff_of_not_dvd (f : LaurentSeries R) {k : ℤ} (hk : ¬ (N : ℤ) ∣ k) :
    (qExpand R N f).coeff k = 0 := by
  refine HahnSeries.embDomain_notin_range ?_
  rintro ⟨m, rfl⟩
  exact hk ⟨m, rfl⟩

@[simp]
theorem qExpand_single (k : ℤ) (r : R) :
    qExpand R N (HahnSeries.single k r) = HahnSeries.single ((N : ℤ) * k) r :=
  HahnSeries.embDomain_single

theorem qExpand_injective : Function.Injective (qExpand R N) :=
  HahnSeries.embDomain_injective

theorem qExpand_one_apply (f : LaurentSeries R) : qExpand R 1 f = f := by
  ext k
  have h : ((1 : ℕ) : ℤ) * k = k := by simp
  conv_lhs => rw [← h]
  rw [qExpand_coeff_mul]

theorem qExpand_congr {M K : ℕ} [NeZero M] [NeZero K] (h : M = K) (f : LaurentSeries R) :
    qExpand R M f = qExpand R K f := by
  subst h; rfl

theorem qExpand_qExpand (M : ℕ) [NeZero M] (f : LaurentSeries R) :
    qExpand R M (qExpand R N f) = qExpand R (M * N) f := by
  ext k
  by_cases hk : ((M : ℤ) * N) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    trans f.coeff m
    · rw [show (M : ℤ) * N * m = (M : ℤ) * ((N : ℤ) * m) by ring, qExpand_coeff_mul,
        qExpand_coeff_mul]
    · rw [show (M : ℤ) * N * m = (((M * N : ℕ) : ℤ)) * m by push_cast; ring,
        qExpand_coeff_mul]
  · rw [qExpand_coeff_of_not_dvd (M * N) f (by push_cast; exact hk)]
    by_cases hkM : (M : ℤ) ∣ k
    · obtain ⟨m, rfl⟩ := hkM
      rw [qExpand_coeff_mul M _ m]
      refine qExpand_coeff_of_not_dvd N _ ?_
      rintro ⟨c, hc⟩
      exact hk ⟨c, by rw [hc]; ring⟩
    · exact qExpand_coeff_of_not_dvd M _ hkM

end QExpand

end
end Dubon2026.SourceFunctionField
