import Dubon2026.PrimitiveFirstSpectralConvergence

/-! # Unconditional absolute convergence of the actual symmetric-square spectral factors -/

namespace Dubon2026

noncomputable section

/-- The actual three-dimensional symmetric-square roots are controlled by the original coefficient square, with no purity premise. -/
theorem primitive_second_spectral_norm_le_square {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (p : Nat.Primes) (i : Fin 3) :
    ‖primitiveSymmetricSpectralRoots f 2 p i‖ ≤
      2 * (‖normalizedCuspCoefficients f.toCuspForm p‖ ^ 2 + 1) := by
  by_cases hpQ : (p : ℕ) ∣ Q
  · simp only [primitiveSymmetricSpectralRoots, if_pos hpQ, norm_zero]
    positivity
  · obtain ⟨ha,hb⟩ := primitiveSatake_norms_le_trace f p
    have hα : ‖primitiveSatakePlus f p‖ ^ 2 ≤
        2 * (‖normalizedCuspCoefficients f.toCuspForm p‖ ^ 2 + 1) := by
      nlinarith [norm_nonneg (primitiveSatakePlus f p),
        norm_nonneg (normalizedCuspCoefficients f.toCuspForm p),
        sq_nonneg (‖normalizedCuspCoefficients f.toCuspForm p‖ - 1)]
    have hβ : ‖primitiveSatakeMinus f p‖ ^ 2 ≤
        2 * (‖normalizedCuspCoefficients f.toCuspForm p‖ ^ 2 + 1) := by
      nlinarith [norm_nonneg (primitiveSatakeMinus f p),
        norm_nonneg (normalizedCuspCoefficients f.toCuspForm p),
        sq_nonneg (‖normalizedCuspCoefficients f.toCuspForm p‖ - 1)]
    fin_cases i
    · simpa [primitiveSymmetricSpectralRoots, hpQ, norm_pow] using hβ
    · simp only [primitiveSymmetricSpectralRoots, if_neg hpQ]
      norm_num
      rw [← norm_mul, (primitiveSatake_trace_det f p).2, norm_one]
      nlinarith [sq_nonneg ‖normalizedCuspCoefficients f.toCuspForm p‖]
    · simpa [primitiveSymmetricSpectralRoots, hpQ, norm_pow] using hα

/-- The proved original square Dirichlet series controls every genuine symmetric-square root perturbation on Re(s)>1, independently of Deligne. -/
theorem summable_norm_primitive_second_spectral {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 0 ≤ k) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun v : Nat.Primes × Fin 3 =>
      ‖-(primitiveSymmetricSpectralRoots f 2 v.1 v.2 * (((v.1 : ℕ) : ℂ) ^ (-s)))‖) := by
  have ha := (summable_normalized_cusp_square_dirichlet f.toCuspForm hk hs).norm.comp_injective
    (show Function.Injective (fun p : Nat.Primes => (p : ℕ)) from Subtype.val_injective)
  have hz : Summable (fun p : Nat.Primes => ‖(((p : ℕ) : ℂ) ^ (-s))‖) :=
    (summable_riemannZetaSummand hs).comp_injective
      (show Function.Injective (fun p : Nat.Primes => (p : ℕ)) from Subtype.val_injective)
  have ht : Summable (fun p : Nat.Primes =>
      (2 * (‖normalizedCuspCoefficients f.toCuspForm p‖ ^ 2 + 1)) * ‖(((p : ℕ) : ℂ) ^ (-s))‖) := by
    convert (ha.add hz).mul_left 2 using 1
    funext p
    simp only [Function.comp_def, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_sq]
    ring
  have hmajor : Summable (fun v : Nat.Primes × Fin 3 =>
      (2 * (‖normalizedCuspCoefficients f.toCuspForm v.1‖ ^ 2 + 1)) * ‖(((v.1 : ℕ) : ℂ) ^ (-s))‖) := by
    apply (summable_prod_of_nonneg (fun v : Nat.Primes × Fin 3 => by positivity)).mpr
    exact ⟨fun _ => Summable.of_finite, by simpa using ht.mul_left 3⟩
  apply hmajor.of_nonneg_of_le (fun _ => norm_nonneg _)
  intro v
  simp only [norm_neg, norm_mul]
  exact mul_le_mul_of_nonneg_right (primitive_second_spectral_norm_le_square f v.1 v.2) (norm_nonneg _)

end
end Dubon2026
