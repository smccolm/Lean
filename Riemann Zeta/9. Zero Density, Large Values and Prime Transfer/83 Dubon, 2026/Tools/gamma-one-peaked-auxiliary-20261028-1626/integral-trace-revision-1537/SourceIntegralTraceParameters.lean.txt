import Mathlib.Tactic

/-! DUB-17/18 -> original Gamma1 degree preservation -> even-weight
slash integrality -> peaked auxiliary trace. These are the exact numerical
and coefficient prerequisites used to isolate one slash coefficient from
the trace. Adapted from anthropics/fermats-last-theorem, Apache-2.0,
revision 6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularForm_qExpansion_slash_coeff_mem_of_peaked_auxiliary. -/
namespace Dubon2026.SourceFunctionField.IntegralTrace
private theorem exists_four_mul_add_six_mul {N : ℤ} (hN : Even N) (h4 : 4 ≤ N) :
    ∃ a b : ℕ, 4 * (a : ℤ) + 6 * (b : ℤ) = N := by
  obtain ⟨M, hM⟩ := hN
  rcases Int.even_or_odd M with ⟨t, ht⟩ | ⟨t, ht⟩
  ·
    refine ⟨t.toNat, 0, ?_⟩
    have ht0 : 0 ≤ t := by omega
    rw [Int.toNat_of_nonneg ht0]
    push_cast
    omega
  ·
    refine ⟨(t - 1).toNat, 1, ?_⟩
    have ht1 : 0 ≤ t - 1 := by omega
    rw [Int.toNat_of_nonneg ht1]
    push_cast
    omega

theorem exists_trace_parameters {k w : ℤ} (hkw : Even (k + w)) (m₀ : ℕ) (hm₀ : w < 12 * (m₀ : ℤ)) (hm₀' : 0 < m₀)
    (δ : ℝ) (hδ : 0 < δ) (n : ℕ) :
    ∃ r a b d : ℕ, Odd r ∧ 4 * (a : ℤ) + 6 * (b : ℤ) = 12 * (d : ℤ) - (k + (r : ℤ) * w) ∧ d < r * m₀ ∧ (n : ℝ) < r * δ := by

  obtain ⟨R₁, hR₁⟩ := exists_nat_gt ((n : ℝ) / δ)
  let R : ℕ := max R₁ (Int.toNat (k + 16))
  let r : ℕ := 2 * R + 1
  have hrodd : Odd r := ⟨R, rfl⟩
  have hRr : R ≤ r := by simp only [r]; omega
  have hrR₁ : R₁ ≤ r := (le_max_left _ _).trans hRr
  have hrk : k + 16 ≤ (r : ℤ) := by
    have h1 : k + 16 ≤ ((Int.toNat (k + 16) : ℕ) : ℤ) := Int.self_le_toNat (k + 16)
    have h2 : (Int.toNat (k + 16) : ℤ) ≤ (R : ℤ) := by exact_mod_cast le_max_right R₁ (Int.toNat (k + 16))
    have h3 : (R : ℤ) ≤ (r : ℤ) := by simp only [r]; push_cast; omega
    omega
  have hrδ : (n : ℝ) < r * δ := by
    have : (n : ℝ) / δ < r := hR₁.trans_le (by exact_mod_cast hrR₁)
    rwa [div_lt_iff₀ hδ] at this

  have hrm : 1 ≤ r * m₀ := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  let d : ℕ := r * m₀ - 1
  have hd : d < r * m₀ := Nat.sub_one_lt_of_le hrm le_rfl
  have hdZ : (d : ℤ) = (r : ℤ) * m₀ - 1 := by
    simp only [d]; rw [Nat.cast_sub hrm]; push_cast; ring

  have hN4 : 4 ≤ 12 * (d : ℤ) - (k + (r : ℤ) * w) := by
    rw [hdZ]
    have hc : 1 ≤ 12 * (m₀ : ℤ) - w := by omega
    have hr0 : (0 : ℤ) ≤ r := by positivity
    nlinarith
  have hNeven : Even (12 * (d : ℤ) - (k + (r : ℤ) * w)) := by
    obtain ⟨R', hR'⟩ := hrodd
    have hr' : (r : ℤ) = 2 * R' + 1 := by exact_mod_cast hR'
    rw [hr']
    obtain ⟨s, hs⟩ := hkw
    refine ⟨6 * (d : ℤ) - s - R' * w, ?_⟩
    linear_combination -hs
  obtain ⟨a, b, hab⟩ := exists_four_mul_add_six_mul hNeven hN4
  exact ⟨r, a, b, d, ⟨R, rfl⟩, hab, hd, hrδ⟩

end Dubon2026.SourceFunctionField.IntegralTrace
