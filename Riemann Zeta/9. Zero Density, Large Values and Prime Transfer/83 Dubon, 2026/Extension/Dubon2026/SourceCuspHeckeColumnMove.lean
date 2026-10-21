import Dubon2026.SourceCuspBoundaryValues

/-! DUB-17/18 -> residual Galois association -> the full boundary Hecke
formula. This derives the divisible-column representative required by the
proved orbit calculation from every original cusp. Principal congruence
preserves the already proved original cusp value and its residue column.
-/
namespace Dubon2026.SourceCuspBoundary
open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups
variable {N : ℕ}

/-- An actual principal-congruence translation of a cusp makes its first coordinate divisible by the good prime. -/
theorem exists_Gamma_mul_dvd {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (δ : SL(2, ℤ)) :
    ∃ g ∈ Gamma N, (ℓ : ℤ) ∣ (g * δ) 0 0 := by
  have hprime : Prime (ℓ : ℤ) := Nat.prime_iff_prime_int.mp hℓ
  have hNℓ : ¬ (ℓ : ℤ) ∣ (N : ℤ) := fun h => hℓN (Int.natCast_dvd_natCast.mp h)

  have step : ∀ δ : SL(2, ℤ), ¬ (ℓ : ℤ) ∣ δ 1 0 → ∃ g ∈ Gamma N, (ℓ : ℤ) ∣ (g * δ) 0 0 := by
    intro δ hc
    have hcop : IsCoprime ((N : ℤ) * δ 1 0) (ℓ : ℤ) := by
      apply IsCoprime.mul_left
      · exact (Prime.coprime_iff_not_dvd hprime).mpr hNℓ |>.symm
      · exact (Prime.coprime_iff_not_dvd hprime).mpr hc |>.symm
    obtain ⟨x, y, hxy⟩ := hcop
    refine ⟨ModularGroup.T ^ ((N : ℤ) * (-(δ 0 0 * x))), ?_, ?_⟩
    · have := ModularGroup_T_pow_mem_Gamma (N : ℤ) ((N : ℤ) * (-(δ 0 0 * x))) (dvd_mul_right _ _)
      rwa [Int.natAbs_natCast] at this
    · rw [Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_T_zpow]
      simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, one_mul]
      exact ⟨δ 0 0 * y, by linear_combination (-(δ 0 0)) * hxy⟩
  by_cases hc : (ℓ : ℤ) ∣ δ 1 0
  ·
    have ha : ¬ (ℓ : ℤ) ∣ δ 0 0 := by
      intro ha
      obtain ⟨x, y, hxy⟩ := isCoprime_col δ
      have h1 : (ℓ : ℤ) ∣ 1 := by
        rw [← hxy]; exact dvd_add (dvd_mul_of_dvd_right ha _) (dvd_mul_of_dvd_right hc _)
      exact hprime.not_dvd_one h1
    set L : SL(2, ℤ) := ⟨!![1, 0; (N : ℤ), 1], by rw [Matrix.det_fin_two_of]; ring⟩ with hL
    have hLmem : L ∈ Gamma N := by
      rw [Gamma_mem, hL]; simp
    have hLδ10 : (L * δ) 1 0 = N * δ 0 0 + δ 1 0 := by
      rw [hL, Matrix.SpecialLinearGroup.coe_mul]
      simp [Matrix.mul_apply, Fin.sum_univ_two]
    have hc' : ¬ (ℓ : ℤ) ∣ (L * δ) 1 0 := by
      rw [hLδ10]
      intro h
      have : (ℓ : ℤ) ∣ (N : ℤ) * δ 0 0 := by simpa using dvd_sub h hc
      rcases hprime.dvd_or_dvd this with h' | h'
      · exact hNℓ h'
      · exact ha h'
    obtain ⟨g, hg, hdvd⟩ := step (L * δ) hc'
    exact ⟨g * L, mul_mem hg hLmem, by rwa [mul_assoc]⟩
  · exact step δ hc


end Dubon2026.SourceCuspBoundary
