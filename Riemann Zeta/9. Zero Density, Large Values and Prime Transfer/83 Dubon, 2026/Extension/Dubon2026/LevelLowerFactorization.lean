/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors

Selected integral level-lowering factorization from LevelRaise.lean,
LeanModularForms 7c41b9b1747d47298f76bdb51f07031087702198.
-/
import Dubon2026.ModularDegeneracy
import Mathlib.Data.Nat.PrimeFin

/-! # Actual integral factorization at lower Gamma0 levels -/

namespace Dubon2026
open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups ModularForm Pointwise
noncomputable section

private noncomputable def primeProductCoprime (a : ℤ) (l : ℕ) : ℤ :=
  ((l.primeFactors.filter (fun (p : ℕ) ↦ ¬ ((p : ℤ) ∣ a))).prod id : ℕ)

private lemma dvd_primeProductCoprime_of_not_dvd
    {a : ℤ} {l : ℕ} {p : ℕ} (hp : p ∈ l.primeFactors) (hpa : ¬ ((p : ℤ) ∣ a)) :
    (p : ℤ) ∣ primeProductCoprime a l := by
  unfold primeProductCoprime
  exact_mod_cast Finset.dvd_prod_of_mem id (Finset.mem_filter.mpr ⟨hp, hpa⟩)

private lemma not_dvd_primeProductCoprime_of_dvd
    {a : ℤ} {l : ℕ} {p : ℕ} (hp_prime : p.Prime) (hpa : (p : ℤ) ∣ a) :
    ¬ ((p : ℤ) ∣ primeProductCoprime a l) := by
  unfold primeProductCoprime
  intro h_dvd
  obtain ⟨q, hq_mem, hq_dvd⟩ := (Prime.dvd_finsetProd_iff (Nat.prime_iff.mp hp_prime) id).mp
    (by exact_mod_cast h_dvd)
  obtain ⟨hq_pf, hqa⟩ := Finset.mem_filter.mp hq_mem
  exact hqa ((Nat.prime_dvd_prime_iff_eq hp_prime
    (Nat.prime_of_mem_primeFactors hq_pf)).mp hq_dvd ▸ hpa)

private lemma exists_shift_isCoprime (a c : ℤ) (l : ℕ) [NeZero l]
    (hac : IsCoprime a c) :
    IsCoprime (a - primeProductCoprime a l * c) (l : ℤ) := by
  rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd, Int.natAbs_natCast]
  by_contra h_ne_one
  obtain ⟨p, hp_prime, hp_dvd⟩ := Nat.exists_prime_and_dvd h_ne_one
  rw [Nat.dvd_gcd_iff] at hp_dvd
  obtain ⟨hp_dvd_x, hp_dvd_l⟩ := hp_dvd
  have hp_dvd_x_int : (p : ℤ) ∣ (a - primeProductCoprime a l * c) := by
    rwa [← Int.natAbs_dvd_natAbs, Int.natAbs_natCast]
  have hp_isPrime : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp_prime
  by_cases hpa : (p : ℤ) ∣ a
  · rcases hp_isPrime.dvd_mul.mp (by simpa using dvd_sub hpa hp_dvd_x_int) with h | h
    · exact not_dvd_primeProductCoprime_of_dvd hp_prime hpa h
    · exact hp_isPrime.not_unit (hac.isUnit_of_dvd' hpa h)
  · refine hpa ?_
    simpa using dvd_add hp_dvd_x_int
      ((dvd_primeProductCoprime_of_not_dvd
        (Nat.mem_primeFactors.mpr ⟨hp_prime, hp_dvd_l, NeZero.ne l⟩) hpa).mul_right c)

private noncomputable def shiftJ (α β : ℤ) (l : ℤ) : ℤ :=
  Int.gcdA α l * β

private lemma shiftJ_spec {α β : ℤ} {l : ℕ} (h : Int.gcd α (l : ℤ) = 1) :
    (l : ℤ) ∣ (β - shiftJ α β (l : ℤ) * α) := by
  unfold shiftJ
  have hBezout := Int.gcd_eq_gcd_ab α (l : ℤ)
  rw [show ((Int.gcd α (l : ℤ) : ℕ) : ℤ) = 1 by exact_mod_cast h] at hBezout
  exact ⟨β * Int.gcdB α (l : ℤ), by linear_combination β * hBezout⟩

private lemma dvd_lower_left_of_dvd {l N : ℕ} (h_dvd : l ∣ N) {γ : SL(2, ℤ)}
    (hγ : γ ∈ Gamma0 N) : (l : ℤ) ∣ γ.val 1 0 :=
  (Int.natCast_dvd_natCast.mpr h_dvd).trans
    ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp hγ))

private lemma natCast_dvd_levelRaiseConj_lower_left {l N : ℕ} (h_dvd : l ∣ N) {c : ℤ}
    (hc : ((N / l : ℕ) : ℤ) ∣ c) : (N : ℤ) ∣ (l : ℤ) * c := by
  rw [show (N : ℤ) = (l : ℤ) * ((N / l : ℕ) : ℤ) by
    rw [← Nat.cast_mul, Nat.mul_div_cancel' h_dvd]]
  exact mul_dvd_mul_left _ hc

private lemma eq_T_zpow_mul_levelRaiseConj_mul_T_zpow
    (l : ℕ) [NeZero l] (a b c d i j k : ℤ) (M γ : SL(2, ℤ))
    (hMval : (M.val : Matrix (Fin 2) (Fin 2) ℤ) = !![a, b; c, d])
    (hγval : (γ.val : Matrix (Fin 2) (Fin 2) ℤ) = !![a - i * c, k; (l : ℤ) * c, d - c * j])
    (hk : b - i * d - j * (a - i * c) = (l : ℤ) * k)
    (hdvd : (l : ℤ) ∣ γ.val 1 0) :
    M = ModularGroup.T ^ i * levelRaiseConjOfDvd l γ hdvd * ModularGroup.T ^ j := by
  apply Subtype.ext
  rw [hMval, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    ModularGroup.coe_T_zpow, ModularGroup.coe_T_zpow]
  apply Matrix.ext
  intro p q
  fin_cases p <;> fin_cases q <;>
    (simp [Matrix.mul_apply, Fin.sum_univ_two, levelRaiseConjOfDvd, hγval,
      Int.mul_ediv_cancel_left c (Nat.cast_ne_zero.mpr (NeZero.ne l))];
     try linear_combination hk)

/-- **Lower-level T-factorisation.** Every `γ' ∈ Γ₀(N/l)` can be written as
`T^i · (levelRaiseConjOfDvd l γ ...) · T^j` for explicit integers `i, j`
and an explicit `γ ∈ Γ₀(N)`. -/
lemma exists_T_levelRaiseConj_T_factor (l N : ℕ) [NeZero l] [NeZero N] (h_dvd : l ∣ N)
    (γ' : SL(2, ℤ)) (hγ' : γ' ∈ Gamma0 (N / l)) :
    ∃ (i j : ℤ) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 N),
      γ' = ModularGroup.T ^ i *
            (levelRaiseConjOfDvd l γ (dvd_lower_left_of_dvd h_dvd hγ)) *
            ModularGroup.T ^ j ∧
      γ.val 1 1 = γ'.val 1 1 - γ'.val 1 0 * j := by
  set a := γ'.val 0 0
  set b := γ'.val 0 1
  set c := γ'.val 1 0
  set d := γ'.val 1 1
  have hdet : a * d - b * c = 1 := by
    have hp := γ'.property; rw [Matrix.det_fin_two] at hp; simpa using hp
  set i := primeProductCoprime a l
  set α := a - i * c
  set β := b - i * d
  set j := shiftJ α β (l : ℤ)
  obtain ⟨k, hk⟩ := shiftJ_spec (β := β) (Int.isCoprime_iff_gcd_eq_one.mp
    (exists_shift_isCoprime a c l ⟨d, -b, by linear_combination hdet⟩))
  refine ⟨i, j, ⟨!![α, k; (l : ℤ) * c, d - c * j], ?det⟩,
    ?gamma0_mem, ?eq, ?diag⟩
  · rw [Matrix.det_fin_two_of]
    change α * (d - c * j) - k * ((l : ℤ) * c) = 1
    linear_combination hdet + c * hk
  · rw [Gamma0_mem]
    change (((l : ℤ) * c : ℤ) : ZMod N) = 0
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact natCast_dvd_levelRaiseConj_lower_left h_dvd
      ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp hγ'))
  · refine eq_T_zpow_mul_levelRaiseConj_mul_T_zpow l a b c d i j k γ' _
      (Matrix.eta_fin_two γ'.val) rfl ?_ _
    change β - j * α = (l : ℤ) * k
    linear_combination hk
  · rfl


end
end Dubon2026
