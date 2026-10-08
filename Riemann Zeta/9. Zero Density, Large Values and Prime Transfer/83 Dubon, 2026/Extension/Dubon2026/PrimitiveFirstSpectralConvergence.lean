import Dubon2026.PrimitiveFullEulerProduct
import Dubon2026.PrimitiveSymmetricSpectral

/-! # Unconditional absolute convergence of the genuine first spectral Euler product -/

namespace Dubon2026

noncomputable section

/-- Trace and determinant one give a coarse local root bound without any purity assumption. -/
theorem norm_le_trace_add_one_of_product_one {α β : ℂ} (hp : α * β = 1) :
    ‖α‖ ≤ ‖α + β‖ + 1 := by
  by_cases ha : ‖α‖ ≤ 1
  · exact ha.trans (by linarith [norm_nonneg (α + β)])
  · have hn : ‖α‖ * ‖β‖ = 1 := by simpa only [norm_mul, norm_one] using congrArg norm hp
    have hb : ‖β‖ ≤ 1 := by nlinarith [norm_nonneg β]
    have ht : ‖α‖ ≤ ‖α + β‖ + ‖β‖ := by
      simpa only [add_sub_cancel_right] using norm_sub_le (α + β) β
    linarith

/-- Both actual roots have the unconditional trace-size bound. -/
theorem primitiveSatake_norms_le_trace {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (p : ℕ) :
    ‖primitiveSatakePlus f p‖ ≤ ‖normalizedCuspCoefficients f.toCuspForm p‖ + 1 ∧
    ‖primitiveSatakeMinus f p‖ ≤ ‖normalizedCuspCoefficients f.toCuspForm p‖ + 1 := by
  obtain ⟨hs,hp⟩ := primitiveSatake_trace_det f p
  constructor
  · simpa only [hs] using norm_le_trace_add_one_of_product_one hp
  · have hs' : primitiveSatakeMinus f p + primitiveSatakePlus f p =
        normalizedCuspCoefficients f.toCuspForm p := by rw [add_comm, hs]
    have hp' : primitiveSatakeMinus f p * primitiveSatakePlus f p = 1 := by rw [mul_comm, hp]
    simpa only [hs'] using norm_le_trace_add_one_of_product_one hp'

/-- The actual two-dimensional incomplete spectral system obeys the trace bound even at omitted primes. -/
theorem primitive_first_spectral_norm_le_trace {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (p : Nat.Primes) (i : Fin 2) :
    ‖primitiveSymmetricSpectralRoots f 1 p i‖ ≤ ‖normalizedCuspCoefficients f.toCuspForm p‖ + 1 := by
  by_cases hpQ : (p : ℕ) ∣ Q
  · simp only [primitiveSymmetricSpectralRoots, if_pos hpQ, norm_zero]
    positivity
  · obtain ⟨ha,hb⟩ := primitiveSatake_norms_le_trace f p
    fin_cases i
    · simpa [primitiveSymmetricSpectralRoots, hpQ] using hb
    · simpa [primitiveSymmetricSpectralRoots, hpQ] using ha

/-- The genuine cusp L-series supplies absolute convergence of both first-order local root perturbations without Deligne. -/
theorem summable_norm_primitive_first_spectral {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 0 ≤ k) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun v : Nat.Primes × Fin 2 =>
      ‖-(primitiveSymmetricSpectralRoots f 1 v.1 v.2 * (((v.1 : ℕ) : ℂ) ^ (-s)))‖) := by
  have ha := (summable_norm_cusp_dirichlet f.toCuspForm hk hs).comp_injective
    (show Function.Injective (fun p : Nat.Primes => (p : ℕ)) from Subtype.val_injective)
  have hz := (summable_riemannZetaSummand hs).comp_injective
    (show Function.Injective (fun p : Nat.Primes => (p : ℕ)) from Subtype.val_injective)
  have ht : Summable (fun p : Nat.Primes =>
      (‖normalizedCuspCoefficients f.toCuspForm p‖ + 1) * ‖(((p : ℕ) : ℂ) ^ (-s))‖) := by
    simpa only [Function.comp_def, norm_mul, add_mul, one_mul] using ha.add hz
  have hmajor : Summable (fun v : Nat.Primes × Fin 2 =>
      (‖normalizedCuspCoefficients f.toCuspForm v.1‖ + 1) * ‖(((v.1 : ℕ) : ℂ) ^ (-s))‖) := by
    apply (summable_prod_of_nonneg (fun v : Nat.Primes × Fin 2 => by positivity)).mpr
    exact ⟨fun _ => Summable.of_finite, by simpa using ht.mul_left 2⟩
  apply hmajor.of_nonneg_of_le (fun _ => norm_nonneg _)
  intro v
  simp only [norm_neg, norm_mul]
  exact mul_le_mul_of_nonneg_right (primitive_first_spectral_norm_le_trace f v.1 v.2) (norm_nonneg _)

/-- Actual normalized cusp L-series are holomorphic throughout Re(s)>1 by the proved absolute convergence. -/
theorem normalized_cusp_lseries_analyticOnNhd {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 Q).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (hk : 0 ≤ k) :
    AnalyticOnNhd ℂ (LSeries (normalizedCuspCoefficients f)) {s : ℂ | 1 < s.re} := by
  have hb : LSeries.abscissaOfAbsConv (normalizedCuspCoefficients f) ≤ (1 : ℝ) :=
    LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
      (fun y hy => normalized_cusp_lseries_summable f hk (s := (y : ℂ)) hy)
  apply (LSeries_analyticOnNhd _).mono
  intro s hs
  exact hb.trans_lt (by exact_mod_cast hs)

end
end Dubon2026
