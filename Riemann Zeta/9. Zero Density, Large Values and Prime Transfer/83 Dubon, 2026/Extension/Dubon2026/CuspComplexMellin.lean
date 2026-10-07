import Dubon2026.CuspMellinEnergy

/-! # Complex Mellin transform of the actual horizontal cusp energy -/

namespace Dubon2026

open UpperHalfPlane CongruenceSubgroup MeasureTheory Set
open scoped MatrixGroups CongruenceSubgroup

noncomputable section

/-- The genuine Fourier term in the complex Mellin integral. -/
def cuspComplexMellinTerm {Q : ℕ} {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k)
    (s : ℂ) (n : ℕ) (y : ℝ) : ℂ :=
  ((‖cuspCoefficients f n‖ ^ 2 : ℝ) : ℂ) *
    ((y : ℂ) ^ (s - 1) * (Real.exp (-4 * Real.pi * n * y) : ℂ))

/-- On positive heights, the complex term has exactly the real Mellin majorant. -/
theorem norm_cuspComplexMellinTerm {Q : ℕ} {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k)
    (s : ℂ) (n : ℕ) {y : ℝ} (hy : 0 < y) :
    ‖cuspComplexMellinTerm f s n y‖ = ‖cuspCoefficients f n‖ ^ 2 *
      (y ^ (s.re - 1) * Real.exp (-4 * Real.pi * n * y)) := by
  simp only [cuspComplexMellinTerm, norm_mul, Complex.norm_of_nonneg (sq_nonneg _),
    Complex.norm_of_nonneg (Real.exp_pos _).le,
    Complex.norm_cpow_eq_rpow_re_of_pos hy, Complex.sub_re, Complex.one_re]

/-- Every genuine complex Mellin term is absolutely integrable in its natural half-plane. -/
theorem integrableOn_cuspComplexMellinTerm {Q : ℕ} {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k)
    {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    IntegrableOn (cuspComplexMellinTerm f s n) (Ioi 0) := by
  constructor
  · apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
    apply continuousOn_of_forall_continuousAt
    intro y hy
    unfold cuspComplexMellinTerm
    apply ContinuousAt.const_mul
    apply ContinuousAt.mul
    · exact Complex.continuousAt_ofReal_cpow_const y (s - 1) (Or.inr (ne_of_gt hy))
    · fun_prop
  · rw [← hasFiniteIntegral_norm_iff]
    apply (integrableOn_cusp_mellin_term f hs n).2.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact (norm_cuspComplexMellinTerm f s n hy).symm

/-- The actual square-coefficient Dirichlet series converges absolutely for Re(s)>k. -/
theorem summable_cusp_complex_square_dirichlet {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k) (hk : 0 ≤ k)
    {s : ℂ} (hs : (k : ℝ) < s.re) :
    Summable (fun n : ℕ => ((‖cuspCoefficients f n‖ ^ 2 : ℝ) : ℂ) * (n : ℂ) ^ (-s)) := by
  apply Summable.of_norm
  apply (summable_cusp_square_dirichlet f hk hs).congr
  intro n
  by_cases hn : n = 0
  · subst n
    simp [cuspCoefficients_zero]
  · rw [norm_mul, Complex.norm_of_nonneg (sq_nonneg _),
      show (n : ℂ) = ((n : ℝ) : ℂ) from rfl,
      Complex.norm_cpow_eq_rpow_re_of_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)),
      Complex.neg_re]

/-- The complex Fourier term has the exact Mellin integral and Gamma factor. -/
theorem integral_cuspComplexMellinTerm {Q : ℕ} {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k)
    {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    (∫ y : ℝ in Ioi 0, cuspComplexMellinTerm f s n y) =
      ((4 * Real.pi : ℂ) ^ (-s) * Complex.Gamma s) *
        (((‖cuspCoefficients f n‖ ^ 2 : ℝ) : ℂ) * (n : ℂ) ^ (-s)) := by
  by_cases hn : n = 0
  · subst n
    simp [cuspComplexMellinTerm, cuspCoefficients_zero]
  · have hb : 0 < 4 * Real.pi * (n : ℝ) := by positivity
    have hi := Complex.integral_cpow_mul_exp_neg_mul_Ioi hs hb
    have he (y : ℝ) : (Real.exp (-4 * Real.pi * n * y) : ℂ) =
        Complex.exp (-((4 * Real.pi * (n : ℝ) : ℝ) : ℂ) * y) := by
      rw [Complex.ofReal_exp]
      congr 1
      push_cast
      ring
    simp only [cuspComplexMellinTerm, integral_const_mul]
    simp_rw [he]
    simp_rw [neg_mul]
    rw [hi, one_div, Complex.inv_cpow _ _ (by
      rw [Complex.arg_ofReal_of_nonneg hb.le]
      exact Real.pi_ne_zero.symm), ← Complex.cpow_neg]
    rw [show ((4 * Real.pi * (n : ℝ) : ℝ) : ℂ) =
        ((4 * Real.pi : ℝ) : ℂ) * ((n : ℝ) : ℂ) by push_cast; rfl,
      Complex.mul_cpow_ofReal_nonneg (by positivity : 0 ≤ 4 * Real.pi) (Nat.cast_nonneg n)]
    push_cast
    ring

/-- The actual horizontal energy is the complex Fourier sum at every positive height. -/
theorem tsum_cuspComplexMellinTerm {Q : ℕ} {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k)
    (s : ℂ) {y : ℝ} (hy : 0 < y) :
    (∑' n : ℕ, cuspComplexMellinTerm f s n y) =
      (y : ℂ) ^ (s - 1) * (cuspHorizontalEnergy f y : ℂ) := by
  rw [cuspHorizontalEnergy_eq_tsum f hy, Complex.ofReal_tsum, ← tsum_mul_left]
  apply tsum_congr
  intro n
  simp only [cuspComplexMellinTerm, Complex.ofReal_mul]
  ring

/-- The true complex Mellin integral converges absolutely for Re(s)>k. -/
theorem integrableOn_cusp_complex_mellin_energy {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k) (hk : 0 ≤ k)
    {s : ℂ} (hs : (k : ℝ) < s.re) :
    IntegrableOn (fun y : ℝ => (y : ℂ) ^ (s - 1) * (cuspHorizontalEnergy f y : ℂ)) (Ioi 0) := by
  have hs0 : 0 < s.re := lt_of_le_of_lt (by exact_mod_cast hk) hs
  constructor
  · have hm : AEMeasurable (fun y => ∑' n : ℕ, cuspComplexMellinTerm f s n y)
        (volume.restrict (Ioi 0)) := AEMeasurable.tsum (fun n =>
      (integrableOn_cuspComplexMellinTerm f hs0 n).aemeasurable)
    apply hm.aestronglyMeasurable.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact tsum_cuspComplexMellinTerm f s hy
  · rw [← hasFiniteIntegral_norm_iff]
    apply (integrableOn_cusp_mellin_energy f hk hs).2.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have he : 0 ≤ cuspHorizontalEnergy f y := by
      rw [cuspHorizontalEnergy_eq_tsum f hy]
      exact tsum_nonneg (fun n => by positivity)
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy,
      Complex.sub_re, Complex.one_re, Complex.norm_of_nonneg he]

/-- Termwise integration gives the exact complex Mellin identity for genuine cusp coefficients. -/
theorem cusp_complex_mellin_energy_identity {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k) (hk : 0 ≤ k)
    {s : ℂ} (hs : (k : ℝ) < s.re) :
    (∫ y : ℝ in Ioi 0, (y : ℂ) ^ (s - 1) * (cuspHorizontalEnergy f y : ℂ)) =
      ((4 * Real.pi : ℂ) ^ (-s) * Complex.Gamma s) *
        ∑' n : ℕ, ((‖cuspCoefficients f n‖ ^ 2 : ℝ) : ℂ) * (n : ℂ) ^ (-s) := by
  have hs0 : 0 < s.re := lt_of_le_of_lt (by exact_mod_cast hk) hs
  have hn (n : ℕ) : (∫ y : ℝ in Ioi 0, ‖cuspComplexMellinTerm f s n y‖) =
      ((4 * Real.pi) ^ (-s.re) * Real.Gamma s.re) *
        (‖cuspCoefficients f n‖ ^ 2 * (n : ℝ) ^ (-s.re)) := by
    rw [← integral_cusp_mellin_term f hs0 n]
    exact setIntegral_congr_fun measurableSet_Ioi (fun y hy => norm_cuspComplexMellinTerm f s n hy)
  have hi := hasSum_integral_of_summable_integral_norm
    (integrableOn_cuspComplexMellinTerm f hs0)
    (by simp_rw [hn]; exact (summable_cusp_square_dirichlet f hk hs).mul_left _)
  have he : (∫ y : ℝ in Ioi 0, ∑' n, cuspComplexMellinTerm f s n y) =
      ∫ y : ℝ in Ioi 0, (y : ℂ) ^ (s - 1) * (cuspHorizontalEnergy f y : ℂ) :=
    setIntegral_congr_fun measurableSet_Ioi (fun y hy => tsum_cuspComplexMellinTerm f s hy)
  change HasSum (fun n => ∫ y : ℝ in Ioi 0, cuspComplexMellinTerm f s n y) _ at hi
  rw [he] at hi
  simp_rw [integral_cuspComplexMellinTerm f hs0] at hi
  exact hi.unique ((summable_cusp_complex_square_dirichlet f hk hs).hasSum.mul_left _)

end
end Dubon2026
