import GafniTao.PintzDetectedPolynomial
import RiemannZeta.GuthMaynard.ClassicalLargeValues

/-!
# Pintz equation (4.12): exact finite expansion

The declarations here expose the two Cauchy--Schwarz factors and expand the
second factor into the literal shifted zeta polynomial.  Diagonal and
off-diagonal pairs remain separately accessible for the subsequent estimate.
-/

open Complex Finset Set
open scoped ArithmeticFunction.Moebius BigOperators ComplexConjugate

namespace GafniTao

open RiemannZeta.GuthMaynard

noncomputable section

/-- The source polynomial written without the `LSeries.term` zero convention. -/
noncomputable def pintzDetectedPolynomialIcc
    (xi : ℝ) (Y : ℕ) (u : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 Y,
    ((ArithmeticFunction.moebius n : ℤ) : ℂ) *
      (n : ℂ) ^ (-((1 - xi : ℝ) + I * u))

theorem pintzDetectedPolynomial_eq_Icc (xi lambda u : ℝ) :
    pintzDetectedPolynomial xi lambda u =
      pintzDetectedPolynomialIcc xi (pintzMobiusCutoff lambda) u := by
  unfold pintzDetectedPolynomial pintzDetectedPolynomialIcc
  rw [← Finset.sum_subset (s₁ := Finset.Icc 1 (pintzMobiusCutoff lambda))
    (s₂ := Finset.range (pintzMobiusCutoff lambda + 1))]
  · apply Finset.sum_congr rfl
    intro n hn
    have hn0 : n ≠ 0 := by
      have := (Finset.mem_Icc.mp hn).1
      omega
    rw [LSeries.term_def]
    simp only [if_neg hn0]
    rw [div_eq_mul_inv, ← Complex.cpow_neg]
  · intro n hn
    simp only [Finset.mem_Icc, Finset.mem_range] at hn ⊢
    omega
  · intro n hnRange hnIcc
    simp only [Finset.mem_range] at hnRange
    simp only [Finset.mem_Icc, not_and_or, not_le] at hnIcc
    have hn0 : n = 0 := by omega
    subst n
    simp

/-- The square-root split used before Cauchy--Schwarz in (4.12). -/
noncomputable def pintzMobiusSqrtCoefficient (n : ℕ) : ℂ :=
  ((ArithmeticFunction.moebius n : ℤ) : ℂ) *
    (n : ℂ) ^ (-(1 / 2 : ℂ))

noncomputable def pintzDualSum
    (W : Finset ℝ) (alpha : ℝ → ℂ) (n : ℕ) : ℂ :=
  ∑ u ∈ W, alpha u * (n : ℂ) ^ (-(u : ℂ) * I)

noncomputable def pintzWeightedDualTerm
    (xi : ℝ) (W : Finset ℝ) (alpha : ℝ → ℂ) (n : ℕ) : ℂ :=
  (n : ℂ) ^ ((xi - 1 / 2 : ℝ) : ℂ) * pintzDualSum W alpha n

/-- Exact interchange and square-root factorization behind the first line of
Pintz (4.12). -/
theorem pintz_sum_detectedPolynomial_eq_sqrt_split
    (xi : ℝ) (Y : ℕ) (W : Finset ℝ) (alpha : ℝ → ℂ) :
    ∑ u ∈ W, alpha u * pintzDetectedPolynomialIcc xi Y u =
      ∑ n ∈ Finset.Icc 1 Y,
        pintzMobiusSqrtCoefficient n *
          pintzWeightedDualTerm xi W alpha n := by
  classical
  unfold pintzDetectedPolynomialIcc
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  have hnPos : 0 < n := by
    have := (Finset.mem_Icc.mp hn).1
    omega
  unfold pintzMobiusSqrtCoefficient pintzWeightedDualTerm pintzDualSum
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  have hpow :
      (n : ℂ) ^ (-((1 - xi : ℝ) + I * u)) =
        (n : ℂ) ^ (-(1 / 2 : ℂ)) *
          ((n : ℂ) ^ ((xi - 1 / 2 : ℝ) : ℂ) *
            (n : ℂ) ^ (-(u : ℂ) * I)) := by
    rw [← Complex.cpow_add, ← Complex.cpow_add]
    · congr 2
      apply Complex.ext
      · simp
        ring
      · simp
    · exact_mod_cast hnPos.ne'
    · exact_mod_cast hnPos.ne'
  rw [hpow]
  ring

/-- The literal Cauchy--Schwarz inequality in equation (4.12). -/
theorem pintz_equation_4_12_cauchy
    (xi : ℝ) (Y : ℕ) (W : Finset ℝ) (alpha : ℝ → ℂ) :
    ‖∑ u ∈ W, alpha u * pintzDetectedPolynomialIcc xi Y u‖ ^ 2 <=
      (∑ n ∈ Finset.Icc 1 Y, ‖pintzMobiusSqrtCoefficient n‖ ^ 2) *
        (∑ n ∈ Finset.Icc 1 Y,
          ‖pintzWeightedDualTerm xi W alpha n‖ ^ 2) := by
  rw [pintz_sum_detectedPolynomial_eq_sqrt_split]
  exact norm_sum_mul_sq_le (Finset.Icc 1 Y)
    pintzMobiusSqrtCoefficient (pintzWeightedDualTerm xi W alpha)

/-- The vector whose Gram matrix is the shifted zeta polynomial in (4.12). -/
noncomputable def pintzGramVector (xi t : ℝ) (n : ℕ) : ℂ :=
  (n : ℂ) ^ ((xi - 1 / 2 : ℝ) : ℂ) *
    (n : ℂ) ^ (-(t : ℂ) * I)

noncomputable def pintzGramCorrelation
    (xi : ℝ) (Y : ℕ) (t u : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 Y,
    conj (pintzGramVector xi t n) * pintzGramVector xi u n

/-- Each Gram entry is the source shifted monomial
`n^(-(1-2*xi+i(u-t)))`. -/
theorem conj_pintzGramVector_mul
    {n : ℕ} (hn : 0 < n) (xi t u : ℝ) :
    conj (pintzGramVector xi t n) * pintzGramVector xi u n =
      (n : ℂ) ^ (-((1 - 2 * xi : ℝ) + I * (u - t))) := by
  have hnNe : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hnArg : ((n : ℂ)).arg ≠ Real.pi := by
    change ((((n : ℝ) : ℂ)).arg ≠ Real.pi)
    rw [Complex.arg_ofReal_of_nonneg (by positivity : (0 : ℝ) <= n)]
    exact Real.pi_ne_zero.symm
  have hreal := Complex.cpow_conj (n : ℂ)
    ((xi - 1 / 2 : ℝ) : ℂ) hnArg
  have hphase := Complex.cpow_conj (n : ℂ) (-(t : ℂ) * I) hnArg
  have hreal' :
      conj ((n : ℂ) ^ ((xi - 1 / 2 : ℝ) : ℂ)) =
        (n : ℂ) ^ ((xi - 1 / 2 : ℝ) : ℂ) := by
    have hexp : conj (((xi - 1 / 2 : ℝ) : ℂ)) =
        ((xi - 1 / 2 : ℝ) : ℂ) := Complex.conj_ofReal _
    rw [hexp] at hreal
    have hbase : conj (n : ℂ) = (n : ℂ) := by simp
    rw [hbase] at hreal
    exact hreal.symm
  have hphase' :
      conj ((n : ℂ) ^ (-(t : ℂ) * I)) =
        (n : ℂ) ^ ((t : ℂ) * I) := by
    simpa using hphase.symm
  unfold pintzGramVector
  rw [map_mul, hreal', hphase']
  rw [← Complex.cpow_add, ← Complex.cpow_add, ← Complex.cpow_add]
  · congr 2
    apply Complex.ext
    · simp
      ring
    · simp
      ring
  all_goals exact hnNe

/-- Literal shifted-zeta-polynomial form of every Gram entry. -/
theorem pintzGramCorrelation_eq_shifted_sum
    (xi : ℝ) (Y : ℕ) (t u : ℝ) :
    pintzGramCorrelation xi Y t u =
      ∑ n ∈ Finset.Icc 1 Y,
        (n : ℂ) ^ (-((1 - 2 * xi : ℝ) + I * (u - t))) := by
  unfold pintzGramCorrelation
  apply Finset.sum_congr rfl
  intro n hn
  apply conj_pintzGramVector_mul
  have := (Finset.mem_Icc.mp hn).1
  omega

theorem pintzWeightedDualTerm_eq_sum_gramVector
    (xi : ℝ) (W : Finset ℝ) (alpha : ℝ → ℂ) (n : ℕ) :
    pintzWeightedDualTerm xi W alpha n =
      ∑ t ∈ W, alpha t * pintzGramVector xi t n := by
  unfold pintzWeightedDualTerm pintzDualSum pintzGramVector
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  ring

/-- Exact complex Gram expansion in the second line of Pintz (4.12).

Unlike the norm majorant below, this identity preserves the phases of all
off-diagonal entries.  Pintz's Halász estimate is applied to this signed
aggregate, so exposing this equality is essential for the source argument. -/
theorem pintz_equation_4_12_gram_identity
    (xi : ℝ) (Y : ℕ) (W : Finset ℝ) (alpha : ℝ → ℂ) :
    ((∑ n ∈ Finset.Icc 1 Y,
        ‖pintzWeightedDualTerm xi W alpha n‖ ^ 2 : ℝ) : ℂ) =
      ∑ t ∈ W, ∑ u ∈ W,
        conj (alpha t) * alpha u * pintzGramCorrelation xi Y t u := by
  have hpoint (n : ℕ) :
      ((‖∑ t ∈ W, alpha t * pintzGramVector xi t n‖ ^ 2 : ℝ) : ℂ) =
        conj (∑ t ∈ W, alpha t * pintzGramVector xi t n) *
          (∑ t ∈ W, alpha t * pintzGramVector xi t n) := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
  have hcast :
      ((∑ n ∈ Finset.Icc 1 Y,
          ‖∑ t ∈ W, alpha t * pintzGramVector xi t n‖ ^ 2 : ℝ) : ℂ) =
        ∑ n ∈ Finset.Icc 1 Y,
          ((‖∑ t ∈ W, alpha t * pintzGramVector xi t n‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    rfl
  simp_rw [pintzWeightedDualTerm_eq_sum_gramVector]
  rw [hcast]
  simp_rw [hpoint]
  simp only [map_sum, map_mul]
  simp_rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u hu
  unfold pintzGramCorrelation
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  ring

/-- Real form of the exact Gram expansion.  Its right side is automatically
real and nonnegative because it equals a sum of squared norms. -/
theorem pintz_equation_4_12_gram_real
    (xi : ℝ) (Y : ℕ) (W : Finset ℝ) (alpha : ℝ → ℂ) :
    (∑ n ∈ Finset.Icc 1 Y,
        ‖pintzWeightedDualTerm xi W alpha n‖ ^ 2) =
      Complex.re (∑ t ∈ W, ∑ u ∈ W,
        conj (alpha t) * alpha u * pintzGramCorrelation xi Y t u) := by
  exact congrArg Complex.re
    (pintz_equation_4_12_gram_identity xi Y W alpha)

/-- Positivity of the signed Gram aggregate, recorded in the form used when
the diagonal and off-diagonal terms are estimated separately. -/
theorem pintz_gram_aggregate_nonneg
    (xi : ℝ) (Y : ℕ) (W : Finset ℝ) (alpha : ℝ → ℂ) :
    0 <= Complex.re (∑ t ∈ W, ∑ u ∈ W,
      conj (alpha t) * alpha u * pintzGramCorrelation xi Y t u) := by
  rw [← pintz_equation_4_12_gram_real]
  positivity

/-- The second Cauchy--Schwarz factor is bounded by the complete literal
Gram matrix.  This is the finite, kernel-checked form of the second line of
(4.12), before separating diagonal and off-diagonal pairs. -/
theorem pintz_equation_4_12_gram
    (xi : ℝ) (Y : ℕ) (W : Finset ℝ) (alpha : ℝ → ℂ)
    (halpha : ∀ t ∈ W, ‖alpha t‖ <= 1) :
    (∑ n ∈ Finset.Icc 1 Y,
        ‖pintzWeightedDualTerm xi W alpha n‖ ^ 2) <=
      ∑ t ∈ W, ∑ u ∈ W, ‖pintzGramCorrelation xi Y t u‖ := by
  simpa only [pintzWeightedDualTerm_eq_sum_gramVector,
      pintzGramCorrelation] using
    (sum_norm_sq_sum_le_gram (Finset.Icc 1 Y) W alpha
      (pintzGramVector xi) halpha)

/-- Equation (4.12) through its complete finite Gram expansion. -/
theorem pintz_equation_4_12
    (xi : ℝ) (Y : ℕ) (W : Finset ℝ) (alpha : ℝ → ℂ)
    (halpha : ∀ t ∈ W, ‖alpha t‖ <= 1) :
    ‖∑ u ∈ W, alpha u * pintzDetectedPolynomialIcc xi Y u‖ ^ 2 <=
      (∑ n ∈ Finset.Icc 1 Y, ‖pintzMobiusSqrtCoefficient n‖ ^ 2) *
        (∑ t ∈ W, ∑ u ∈ W, ‖pintzGramCorrelation xi Y t u‖) := by
  exact (pintz_equation_4_12_cauchy xi Y W alpha).trans
    (mul_le_mul_of_nonneg_left (pintz_equation_4_12_gram xi Y W alpha halpha)
      (Finset.sum_nonneg fun n hn => sq_nonneg _))

/-- The first Cauchy factor is at most the ordinary harmonic sum. -/
theorem pintzMobiusSqrtCoefficient_mass_le_harmonic (Y : ℕ) :
    (∑ n ∈ Finset.Icc 1 Y, ‖pintzMobiusSqrtCoefficient n‖ ^ 2) <=
      (harmonic Y : ℝ) := by
  rw [harmonic_eq_sum_Icc]
  push_cast
  apply Finset.sum_le_sum
  intro n hn
  have hnOne : (1 : ℝ) <= n := by
    exact_mod_cast (Finset.mem_Icc.mp hn).1
  have hnPos : (0 : ℝ) < n := zero_lt_one.trans_le hnOne
  have hmu := moebius_coeff_norm_le_one n
  unfold pintzMobiusSqrtCoefficient
  rw [norm_mul]
  rw [show (n : ℂ) = ((n : ℝ) : ℂ) by norm_num]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hnPos]
  have hexp : (-((1 / 2 : ℂ))).re = -(1 / 2 : ℝ) := by
    norm_num [Complex.div_re]
  rw [hexp]
  have hpowNonneg : 0 <= (n : ℝ) ^ (-(1 / 2 : ℝ)) := by positivity
  calc
    (‖((ArithmeticFunction.moebius n : ℤ) : ℂ)‖ *
        (n : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 <=
      (1 * (n : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 := by
        gcongr
        simpa using hmu
    _ = (n : ℝ)⁻¹ := by
      rw [mul_comm, mul_one, ← Real.rpow_natCast,
        ← Real.rpow_mul hnPos.le]
      norm_num
      exact Real.rpow_neg_one _

/-- A logarithmic diagonal majorant, sufficient for Pintz's argument and
uniform at `xi=0`. -/
theorem norm_pintzGramCorrelation_self_le
    {xi : ℝ} {Y : ℕ} (hxi : 0 <= xi) (t : ℝ) :
    ‖pintzGramCorrelation xi Y t t‖ <=
      (Y : ℝ) ^ (2 * xi) * (harmonic Y : ℝ) := by
  rw [pintzGramCorrelation_eq_shifted_sum]
  simp only [sub_self, mul_zero, add_zero]
  calc
    ‖∑ n ∈ Finset.Icc 1 Y,
        (n : ℂ) ^ (-((1 - 2 * xi : ℝ) : ℂ))‖ <=
      ∑ n ∈ Finset.Icc 1 Y,
        ‖(n : ℂ) ^ (-((1 - 2 * xi : ℝ) : ℂ))‖ := norm_sum_le _ _
    _ <= ∑ n ∈ Finset.Icc 1 Y,
        (Y : ℝ) ^ (2 * xi) * (n : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro n hn
      have hnOne : (1 : ℝ) <= n := by
        exact_mod_cast (Finset.mem_Icc.mp hn).1
      have hnY : (n : ℝ) <= Y := by
        exact_mod_cast (Finset.mem_Icc.mp hn).2
      have hnPos : (0 : ℝ) < n := zero_lt_one.trans_le hnOne
      rw [show (n : ℂ) = ((n : ℝ) : ℂ) by norm_num]
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hnPos]
      have hexp : (-(((1 - 2 * xi : ℝ) : ℂ))).re = -(1 - 2 * xi) := by
        norm_num
      rw [hexp]
      rw [show -(1 - 2 * xi) = 2 * xi + (-1) by ring,
        Real.rpow_add hnPos]
      rw [Real.rpow_neg_one]
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow hnPos.le hnY
          (show 0 <= 2 * xi by positivity)) (by positivity)
    _ = (Y : ℝ) ^ (2 * xi) * (harmonic Y : ℝ) := by
      rw [← Finset.mul_sum, harmonic_eq_sum_Icc]
      push_cast
      congr 2

/-- Diagonal/off-diagonal decomposition of the Gram sum.  The harmless
coarse `card^2*M` form keeps the exact diagonal term separately visible. -/
theorem pintzGram_double_sum_le
    {xi M D : ℝ} {Y : ℕ} {W : Finset ℝ}
    (hM : 0 <= M)
    (hoff : ∀ t ∈ W, ∀ u ∈ W, t ≠ u →
      ‖pintzGramCorrelation xi Y t u‖ <= M)
    (hdiag : ∀ t ∈ W, ‖pintzGramCorrelation xi Y t t‖ <= D) :
    (∑ t ∈ W, ∑ u ∈ W, ‖pintzGramCorrelation xi Y t u‖) <=
      (W.card : ℝ) ^ 2 * M + (W.card : ℝ) * D := by
  calc
    (∑ t ∈ W, ∑ u ∈ W, ‖pintzGramCorrelation xi Y t u‖) <=
      ∑ t ∈ W, ∑ u ∈ W, (M + if u = t then D else 0) := by
        apply Finset.sum_le_sum
        intro t ht
        apply Finset.sum_le_sum
        intro u hu
        by_cases hut : u = t
        · subst u
          simp only [ite_true]
          exact (hdiag t ht).trans (le_add_of_nonneg_left hM)
        · simp only [hut, ite_false, add_zero]
          exact hoff t ht u hu (Ne.symm hut)
    _ = (W.card : ℝ) ^ 2 * M + (W.card : ℝ) * D := by
      simp [Finset.sum_add_distrib]
      ring

/-- Aligning the selected values converts the pointwise equation-(4.10)
lower bound into the left side of (4.12). -/
theorem pintz_phase_aligned_lower
    {xi V : ℝ} {Y : ℕ} {W : Finset ℝ} (hV : 0 <= V)
    (hlarge : ∀ t ∈ W, V <= ‖pintzDetectedPolynomialIcc xi Y t‖) :
    ((W.card : ℝ) * V) ^ 2 <=
      ‖∑ t ∈ W, phaseAlign (pintzDetectedPolynomialIcc xi Y t) *
        pintzDetectedPolynomialIcc xi Y t‖ ^ 2 := by
  have hsum : (W.card : ℝ) * V <=
      ∑ t ∈ W, ‖pintzDetectedPolynomialIcc xi Y t‖ := by
    calc
      (W.card : ℝ) * V = ∑ t ∈ W, V := by simp
      _ <= _ := Finset.sum_le_sum fun t ht => hlarge t ht
  have halign :
      ‖∑ t ∈ W, phaseAlign (pintzDetectedPolynomialIcc xi Y t) *
          pintzDetectedPolynomialIcc xi Y t‖ =
        ∑ t ∈ W, ‖pintzDetectedPolynomialIcc xi Y t‖ := by
    have heq :
        (∑ t ∈ W, phaseAlign (pintzDetectedPolynomialIcc xi Y t) *
          pintzDetectedPolynomialIcc xi Y t) =
        (((∑ t ∈ W, ‖pintzDetectedPolynomialIcc xi Y t‖) : ℝ) : ℂ) := by
      push_cast
      apply Finset.sum_congr rfl
      intro t ht
      exact phaseAlign_mul _
    rw [heq, norm_real, Real.norm_eq_abs, abs_of_nonneg]
    positivity
  rw [halign]
  gcongr

/-- Complete finite inequality corresponding to Pintz (4.12), with both
source error channels explicit. -/
theorem pintz_equation_4_12_bounded
    {xi V M D : ℝ} {Y : ℕ} {W : Finset ℝ}
    (hV : 0 <= V) (hM : 0 <= M)
    (hlarge : ∀ t ∈ W, V <= ‖pintzDetectedPolynomialIcc xi Y t‖)
    (hoff : ∀ t ∈ W, ∀ u ∈ W, t ≠ u →
      ‖pintzGramCorrelation xi Y t u‖ <= M)
    (hdiag : ∀ t ∈ W, ‖pintzGramCorrelation xi Y t t‖ <= D) :
    ((W.card : ℝ) * V) ^ 2 <=
      (harmonic Y : ℝ) *
        ((W.card : ℝ) ^ 2 * M + (W.card : ℝ) * D) := by
  let alpha : ℝ → ℂ := fun t => phaseAlign (pintzDetectedPolynomialIcc xi Y t)
  calc
    ((W.card : ℝ) * V) ^ 2 <=
      ‖∑ t ∈ W, alpha t * pintzDetectedPolynomialIcc xi Y t‖ ^ 2 :=
        pintz_phase_aligned_lower hV hlarge
    _ <= (∑ n ∈ Finset.Icc 1 Y, ‖pintzMobiusSqrtCoefficient n‖ ^ 2) *
        (∑ t ∈ W, ∑ u ∈ W, ‖pintzGramCorrelation xi Y t u‖) :=
      pintz_equation_4_12 xi Y W alpha
        (fun t ht => norm_phaseAlign_le_one _)
    _ <= (harmonic Y : ℝ) *
        ((W.card : ℝ) ^ 2 * M + (W.card : ℝ) * D) := by
      exact mul_le_mul (pintzMobiusSqrtCoefficient_mass_le_harmonic Y)
        (pintzGram_double_sum_le hM hoff hdiag)
        (Finset.sum_nonneg fun t ht => Finset.sum_nonneg fun u hu => norm_nonneg _)
        (by
          rw [harmonic_eq_sum_Icc]
          push_cast
          positivity)

#print axioms pintzDetectedPolynomial_eq_Icc
#print axioms pintz_sum_detectedPolynomial_eq_sqrt_split
#print axioms pintz_equation_4_12_cauchy
#print axioms pintzGramCorrelation_eq_shifted_sum
#print axioms pintz_equation_4_12_gram_identity
#print axioms pintz_equation_4_12_gram_real
#print axioms pintz_gram_aggregate_nonneg
#print axioms pintz_equation_4_12_gram
#print axioms pintz_equation_4_12
#print axioms pintzMobiusSqrtCoefficient_mass_le_harmonic
#print axioms norm_pintzGramCorrelation_self_le
#print axioms pintzGram_double_sum_le
#print axioms pintz_equation_4_12_bounded

end

end GafniTao
