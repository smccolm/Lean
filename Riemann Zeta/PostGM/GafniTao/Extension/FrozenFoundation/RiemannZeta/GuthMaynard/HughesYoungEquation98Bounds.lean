import RiemannZeta.GuthMaynard.HughesYoungEquation96Jet
import RiemannZeta.GuthMaynard.DFIDivisorEpsilon

open Complex Finset Metric Set
open scoped BigOperators Topology

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# Uniform bounds for the Hughes--Young equation-(98) Euler factors

On the vertical source line the two denominators in equation (100) stay a
fixed distance from zero.  Consequently each local factor is bounded by an
absolute constant, uniformly in the prime exponent and in the height.  This
is the arithmetic estimate needed before applying Cauchy's inequalities to
the equation-(96) jet.
-/

/-- A fixed finite absolute-series constant for the half-plane
`Re s ≥ 3/2`.  Its numerical value is irrelevant; finiteness and uniformity
in the vertical height are what the Hughes--Young contour requires. -/
noncomputable def hughesYoungZetaHalfPlaneMajorant : ℝ :=
  ∑' n : ℕ, ‖LSeries.term (1 : ℕ → ℂ) (3 / 2 : ℂ) n‖

theorem summable_hughesYoungZetaHalfPlaneMajorant :
    Summable (fun n : ℕ => ‖LSeries.term (1 : ℕ → ℂ) (3 / 2 : ℂ) n‖) := by
  exact (LSeriesSummable_one_iff.mpr (by norm_num :
    (1 : ℝ) < (3 / 2 : ℂ).re)).norm

theorem norm_riemannZeta_le_hughesYoungZetaHalfPlaneMajorant
    {s : ℂ} (hs : (3 / 2 : ℝ) ≤ s.re) :
    ‖riemannZeta s‖ ≤ hughesYoungZetaHalfPlaneMajorant := by
  have hs1 : 1 < s.re := by linarith
  have hsum : LSeriesSummable (1 : ℕ → ℂ) s :=
    LSeriesSummable_one_iff.mpr hs1
  have hs' : ((3 / 2 : ℂ).re) ≤ s.re := by norm_num; exact hs
  rw [← LSeries_one_eq_riemannZeta hs1, LSeries]
  calc
    ‖∑' n, LSeries.term (1 : ℕ → ℂ) s n‖ ≤
        ∑' n, ‖LSeries.term (1 : ℕ → ℂ) s n‖ :=
      norm_tsum_le_tsum_norm hsum.norm
    _ ≤ ∑' n, ‖LSeries.term (1 : ℕ → ℂ) (3 / 2 : ℂ) n‖ := by
      exact hsum.norm.tsum_le_tsum
        (fun n => LSeries.norm_term_le_of_re_le_re (1 : ℕ → ℂ) hs' n)
        summable_hughesYoungZetaHalfPlaneMajorant
    _ = hughesYoungZetaHalfPlaneMajorant := rfl

theorem norm_moebiusLSeries_le_hughesYoungZetaHalfPlaneMajorant
    {s : ℂ} (hs : (3 / 2 : ℝ) ≤ s.re) :
    ‖LSeries (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ)) s‖ ≤
      hughesYoungZetaHalfPlaneMajorant := by
  have hs1 : 1 < s.re := by linarith
  have hsum : LSeriesSummable
      (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ)) s :=
    ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs1
  have hs' : ((3 / 2 : ℂ).re) ≤ s.re := by norm_num; exact hs
  rw [LSeries]
  calc
    ‖∑' n, LSeries.term
        (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ)) s n‖ ≤
        ∑' n, ‖LSeries.term
          (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ)) s n‖ :=
      norm_tsum_le_tsum_norm hsum.norm
    _ ≤ ∑' n, ‖LSeries.term (1 : ℕ → ℂ) (3 / 2 : ℂ) n‖ := by
      apply hsum.norm.tsum_le_tsum _
        summable_hughesYoungZetaHalfPlaneMajorant
      intro n
      calc
        ‖LSeries.term
            (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ)) s n‖ ≤
            ‖LSeries.term (1 : ℕ → ℂ) s n‖ :=
          LSeries.norm_term_le s (moebius_coeff_norm_le_one n)
        _ ≤ ‖LSeries.term (1 : ℕ → ℂ) (3 / 2 : ℂ) n‖ :=
          LSeries.norm_term_le_of_re_le_re (1 : ℕ → ℂ) hs' n
    _ = hughesYoungZetaHalfPlaneMajorant := rfl

theorem riemannZeta_inv_eq_moebiusLSeries
    {s : ℂ} (hs : 1 < s.re) :
    (riemannZeta s)⁻¹ =
      LSeries (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ)) s := by
  have hmul : LSeries (1 : ℕ → ℂ) s *
      LSeries (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ)) s = 1 := by
    simpa using LSeries_one_mul_Lseries_moebius hs
  rw [LSeries_one_eq_riemannZeta hs] at hmul
  have hz : riemannZeta s ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re hs.le
  apply mul_left_cancel₀ hz
  rw [mul_inv_cancel₀ hz, hmul]

theorem norm_riemannZeta_inv_le_hughesYoungZetaHalfPlaneMajorant
    {s : ℂ} (hs : (3 / 2 : ℝ) ≤ s.re) :
    ‖(riemannZeta s)⁻¹‖ ≤ hughesYoungZetaHalfPlaneMajorant := by
  rw [riemannZeta_inv_eq_moebiusLSeries (by linarith)]
  exact norm_moebiusLSeries_le_hughesYoungZetaHalfPlaneMajorant hs

theorem norm_prime_cpow_le_one_of_re_nonpos
    (p : Nat.Primes) {s : ℂ} (hs : s.re ≤ 0) :
    ‖(p : ℂ) ^ s‖ ≤ 1 := by
  rw [Complex.norm_natCast_cpow_of_pos p.2.pos]
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast p.2.one_le
  calc
    ((p : ℕ) : ℝ) ^ s.re ≤ ((p : ℕ) : ℝ) ^ (0 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hp1 hs
    _ = 1 := by simp

theorem norm_prime_cpow_le_half_of_re_le_neg_one
    (p : Nat.Primes) {s : ℂ} (hs : s.re ≤ -1) :
    ‖(p : ℂ) ^ s‖ ≤ 1 / 2 := by
  rw [Complex.norm_natCast_cpow_of_pos p.2.pos]
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast p.2.one_le
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast p.2.two_le
  calc
    ((p : ℕ) : ℝ) ^ s.re ≤ ((p : ℕ) : ℝ) ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hp1 hs
    _ = (((p : ℕ) : ℝ))⁻¹ := by rw [Real.rpow_neg_one]
    _ ≤ (2 : ℝ)⁻¹ := by exact inv_anti₀ (by norm_num) hp2
    _ = 1 / 2 := by norm_num

theorem half_le_norm_one_sub_of_norm_le_half {x : ℂ}
    (hx : ‖x‖ ≤ 1 / 2) :
    (1 / 2 : ℝ) ≤ ‖1 - x‖ := by
  have hrev := norm_sub_norm_le (1 : ℂ) x
  rw [norm_one] at hrev
  linarith

theorem norm_prime_cpow_mul_prime_cpow_le_one
    (p : Nat.Primes) {a b : ℂ} (hab : (a + b).re ≤ 0) :
    ‖(p : ℂ) ^ a * (p : ℂ) ^ b‖ ≤ 1 := by
  rw [← Complex.cpow_add _ _ (by exact_mod_cast p.2.ne_zero)]
  exact norm_prime_cpow_le_one_of_re_nonpos p hab

theorem norm_prime_cpow_three_mul_le_one
    (p : Nat.Primes) {a b c : ℂ} (habc : (a + b + c).re ≤ 0) :
    ‖(p : ℂ) ^ a * (p : ℂ) ^ b * (p : ℂ) ^ c‖ ≤ 1 := by
  rw [← Complex.cpow_add _ _ (by exact_mod_cast p.2.ne_zero),
    ← Complex.cpow_add _ _ (by exact_mod_cast p.2.ne_zero)]
  exact norm_prime_cpow_le_one_of_re_nonpos p habc

/-- Uniform local equation-(100) bound on the bidisc used for the vertical
equation-(96) jet. -/
theorem norm_hughesYoungCPrimeFactor_shiftedJet_le
    (e : ℕ) (p : Nat.Primes) {q z w : ℂ} (hq : -(1 / 4 : ℝ) ≤ q.re)
    (hz : ‖z‖ ≤ 1 / 8) (hw : ‖w‖ ≤ 1 / 8) :
    ‖hughesYoungCPrimeFactor e p (-z) z (-w) w (1 + q / 2)‖ ≤ 32 := by
  let x : ℂ := (p : ℂ) ^ (z - w - 2 - q)
  let r : ℂ := (p : ℂ) ^ (-2 - 2 * z - 2 * w)
  let u : ℂ := (p : ℂ) ^ (-2 * w)
  let v : ℂ := (p : ℂ) ^ (-2 * z)
  have hzRe : |z.re| ≤ (1 / 8 : ℝ) := (abs_re_le_norm z).trans hz
  have hwRe : |w.re| ≤ (1 / 8 : ℝ) := (abs_re_le_norm w).trans hw
  have hxExp : (z - w - 2 - q).re ≤ -1 := by
    norm_num [Complex.mul_re]
    linarith [le_abs_self z.re, neg_abs_le w.re]
  have hrExp : (-2 - 2 * z - 2 * w : ℂ).re ≤ -1 := by
    norm_num [Complex.mul_re]
    linarith [neg_abs_le z.re, neg_abs_le w.re]
  have hxNorm : ‖x‖ ≤ 1 / 2 := by
    dsimp only [x]
    exact norm_prime_cpow_le_half_of_re_le_neg_one p hxExp
  have hrNorm : ‖r‖ ≤ 1 / 2 := by
    dsimp only [r]
    exact norm_prime_cpow_le_half_of_re_le_neg_one p hrExp
  have hxPow (n : ℕ) : ‖x ^ n‖ ≤ 1 := by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg x) (hxNorm.trans (by norm_num))
  have hC0 : ‖hughesYoungC0 e x‖ ≤ 2 := by
    unfold hughesYoungC0
    exact (norm_sub_le _ _).trans (by rw [norm_one]; linarith [hxPow (1 + e)])
  have hOneSubPow : ‖1 - x ^ e‖ ≤ 2 :=
    (norm_sub_le _ _).trans (by rw [norm_one]; linarith [hxPow e])
  have hpu : ‖(p : ℂ) ^ (-1 : ℂ) * u‖ ≤ 1 := by
    dsimp only [u]
    apply norm_prime_cpow_mul_prime_cpow_le_one p
    norm_num [Complex.mul_re]
    linarith [neg_abs_le w.re]
  have hpvx : ‖(p : ℂ) ^ (-1 : ℂ) * (v * x)‖ ≤ 1 := by
    dsimp only [v, x]
    rw [← mul_assoc]
    apply norm_prime_cpow_three_mul_le_one p
    norm_num [Complex.mul_re]
    linarith [neg_abs_le z.re, neg_abs_le w.re]
  have hC1 :
      ‖(p : ℂ) ^ (-1 : ℂ) * hughesYoungC1 e u v x‖ ≤ 4 := by
    unfold hughesYoungC1
    rw [show (p : ℂ) ^ (-1 : ℂ) * ((u + v * x) * (1 - x ^ e)) =
        ((p : ℂ) ^ (-1 : ℂ) * (u + v * x)) * (1 - x ^ e) by ring,
      norm_mul]
    calc
      ‖(p : ℂ) ^ (-1 : ℂ) * (u + v * x)‖ * ‖1 - x ^ e‖ ≤
          (‖(p : ℂ) ^ (-1 : ℂ) * u‖ +
            ‖(p : ℂ) ^ (-1 : ℂ) * (v * x)‖) * 2 := by
        gcongr
        rw [mul_add]
        exact norm_add_le _ _
      _ ≤ (1 + 1) * 2 := by gcongr
      _ = 4 := by norm_num
  have hregMonomial :
      ‖(p : ℂ) ^ (-2 : ℂ) * (p : ℂ) ^ (-2 * z - 2 * w)‖ ≤ 1 := by
    apply norm_prime_cpow_mul_prime_cpow_le_one p
    norm_num [Complex.mul_re]
    linarith [neg_abs_le z.re, neg_abs_le w.re]
  have hC2raw : ‖hughesYoungC2 e x‖ ≤ 2 := by
    unfold hughesYoungC2
    exact (norm_sub_le _ _).trans (by linarith [hxNorm, hxPow e])
  have hC2 :
      ‖(p : ℂ) ^ (-2 : ℂ) *
          ((p : ℂ) ^ (-2 * z - 2 * w) * hughesYoungC2 e x)‖ ≤ 2 := by
    rw [← mul_assoc, norm_mul]
    exact (mul_le_mul hregMonomial hC2raw (norm_nonneg _)
      (by positivity)).trans (by norm_num)
  have hnum :
      ‖hughesYoungC0 e x - (p : ℂ) ^ (-1 : ℂ) * hughesYoungC1 e u v x +
          (p : ℂ) ^ (-2 : ℂ) *
            ((p : ℂ) ^ (-2 * z - 2 * w) * hughesYoungC2 e x)‖ ≤ 8 := by
    calc
      _ ≤ ‖hughesYoungC0 e x‖ +
          ‖(p : ℂ) ^ (-1 : ℂ) * hughesYoungC1 e u v x‖ +
          ‖(p : ℂ) ^ (-2 : ℂ) *
            ((p : ℂ) ^ (-2 * z - 2 * w) * hughesYoungC2 e x)‖ := by
        exact (norm_add_le _ _).trans
          (add_le_add (norm_sub_le _ _) le_rfl)
      _ ≤ 2 + 4 + 2 := by gcongr
      _ = 8 := by norm_num
  have hdenR : (1 / 2 : ℝ) ≤ ‖1 - r‖ :=
    half_le_norm_one_sub_of_norm_le_half hrNorm
  have hdenX : (1 / 2 : ℝ) ≤ ‖1 - x‖ :=
    half_le_norm_one_sub_of_norm_le_half hxNorm
  unfold hughesYoungCPrimeFactor hughesYoungCPrimeNumerator
  dsimp only
  rw [show -(-z) - w - 2 * (1 + q / 2) = z - w - 2 - q by ring]
  rw [show -2 + (-z) - z + (-w) - w = -2 - 2 * z - 2 * w by ring]
  rw [show (-w) - w = -2 * w by ring,
    show (-z) - z = -2 * z by ring,
    show -2 * z + (-w) - w = -2 * z - 2 * w by ring]
  change ‖(hughesYoungC0 e x - (p : ℂ) ^ (-1 : ℂ) *
      hughesYoungC1 e u v x + (p : ℂ) ^ (-2 : ℂ) *
        ((p : ℂ) ^ (-2 * z - 2 * w) * hughesYoungC2 e x)) /
      ((1 - r) * (1 - x))‖ ≤ 32
  rw [norm_div, norm_mul]
  apply (div_le_iff₀ (mul_pos (by linarith) (by linarith))).2
  nlinarith [mul_le_mul hdenR hdenX (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by linarith : (0 : ℝ) ≤ ‖1 - r‖)]

/-- The source-line Euler-factor estimate is the zero-real-part
specialization of the shifted-strip estimate. -/
theorem norm_hughesYoungCPrimeFactor_verticalJet_le
    (e : ℕ) (p : Nat.Primes) {q z w : ℂ} (hq : q.re = 0)
    (hz : ‖z‖ ≤ 1 / 8) (hw : ‖w‖ ≤ 1 / 8) :
    ‖hughesYoungCPrimeFactor e p (-z) z (-w) w (1 + q / 2)‖ ≤ 32 := by
  apply norm_hughesYoungCPrimeFactor_shiftedJet_le e p
  · rw [hq]
    norm_num
  · exact hz
  · exact hw

/-- The complete finite correction factor costs at most the fifth power of
the divisor count, uniformly in the vertical height and both jet variables. -/
theorem norm_hughesYoungC_shiftedJet_le_divisorsCard_pow_five
    {h : ℕ} (hh : 0 < h) {q z w : ℂ} (hq : -(1 / 4 : ℝ) ≤ q.re)
    (hz : ‖z‖ ≤ 1 / 8) (hw : ‖w‖ ≤ 1 / 8) :
    ‖hughesYoungC h (-z) z (-w) w (1 + q / 2)‖ ≤
      ((h.divisors.card : ℝ) ^ 5) := by
  unfold hughesYoungC
  rw [norm_prod]
  calc
    (∏ p ∈ hughesYoungPrimeFactors h,
        ‖hughesYoungCPrimeFactor (h.factorization p) p
          (-z) z (-w) w (1 + q / 2)‖) ≤
      ∏ p ∈ hughesYoungPrimeFactors h,
        (((h.factorization p : ℕ) + 1 : ℕ) : ℝ) ^ 5 := by
      apply Finset.prod_le_prod
      · intro p _hp
        positivity
      · intro p hp
        have hpdvd : (p : ℕ) ∣ h :=
          Nat.dvd_of_mem_primeFactors (mem_hughesYoungPrimeFactors.mp hp)
        have he : 1 ≤ h.factorization p :=
          (p.2.dvd_iff_one_le_factorization hh.ne').mp hpdvd
        calc
          ‖hughesYoungCPrimeFactor (h.factorization p) p
              (-z) z (-w) w (1 + q / 2)‖ ≤ 32 :=
            norm_hughesYoungCPrimeFactor_shiftedJet_le
              (h.factorization p) p hq hz hw
          _ ≤ (((h.factorization p : ℕ) + 1 : ℕ) : ℝ) ^ 5 := by
            have htwo : (2 : ℝ) ≤ (h.factorization p + 1 : ℕ) := by
              exact_mod_cast Nat.succ_le_succ he
            nlinarith [sq_nonneg
              (((h.factorization p + 1 : ℕ) : ℝ) - 2),
              sq_nonneg ((((h.factorization p + 1 : ℕ) : ℝ) ^ 2) - 4)]
    _ = (∏ p ∈ h.primeFactors,
          (((h.factorization p : ℕ) + 1 : ℕ) : ℝ)) ^ 5 := by
      have heq :
          (∏ p ∈ hughesYoungPrimeFactors h,
              ((((h.factorization p : ℕ) + 1 : ℕ) : ℝ) ^ 5)) =
            ∏ p ∈ h.primeFactors,
              ((((h.factorization p : ℕ) + 1 : ℕ) : ℝ) ^ 5) := by
        unfold hughesYoungPrimeFactors
        rw [prod_map]
        simpa using (Finset.prod_attach h.primeFactors
          (fun p => ((((h.factorization p : ℕ) + 1 : ℕ) : ℝ) ^ 5)))
      rw [heq]
      rw [Finset.prod_pow]
    _ = ((h.divisors.card : ℝ) ^ 5) := by
      rw [Nat.card_divisors hh.ne']
      norm_cast

theorem norm_hughesYoungC_verticalJet_le_divisorsCard_pow_five
    {h : ℕ} (hh : 0 < h) {q z w : ℂ} (hq : q.re = 0)
    (hz : ‖z‖ ≤ 1 / 8) (hw : ‖w‖ ≤ 1 / 8) :
    ‖hughesYoungC h (-z) z (-w) w (1 + q / 2)‖ ≤
      ((h.divisors.card : ℝ) ^ 5) := by
  apply norm_hughesYoungC_shiftedJet_le_divisorsCard_pow_five hh
  · rw [hq]
    norm_num
  · exact hz
  · exact hw

theorem norm_hughesYoungC_shiftedJet_le_const_mul_rpow
    {ε : ℝ} (hε : 0 < ε) {h : ℕ} (hh : 0 < h)
    {q z w : ℂ} (hq : -(1 / 4 : ℝ) ≤ q.re)
    (hz : ‖z‖ ≤ 1 / 8) (hw : ‖w‖ ≤ 1 / 8) :
    ‖hughesYoungC h (-z) z (-w) w (1 + q / 2)‖ ≤
      (divisorEpsilonConstant (ε / 5)) ^ 5 * (h : ℝ) ^ ε := by
  have hε5 : 0 < ε / 5 := by positivity
  have hdiv := card_divisors_le_const_mul_rpow hε5 hh.ne'
  have hpow : ((h.divisors.card : ℝ) ^ 5) ≤
      (divisorEpsilonConstant (ε / 5) * (h : ℝ) ^ (ε / 5)) ^ 5 :=
    pow_le_pow_left₀ (by positivity) hdiv 5
  calc
    ‖hughesYoungC h (-z) z (-w) w (1 + q / 2)‖ ≤
        ((h.divisors.card : ℝ) ^ 5) :=
      norm_hughesYoungC_shiftedJet_le_divisorsCard_pow_five hh hq hz hw
    _ ≤ (divisorEpsilonConstant (ε / 5) *
        (h : ℝ) ^ (ε / 5)) ^ 5 := hpow
    _ = (divisorEpsilonConstant (ε / 5)) ^ 5 * (h : ℝ) ^ ε := by
      rw [mul_pow]
      have hh0 : 0 ≤ (h : ℝ) := by positivity
      have hbase : ((h : ℝ) ^ (ε / 5)) ^ (5 : ℕ) = (h : ℝ) ^ ε := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hh0]
        congr 1
        norm_num
      rw [hbase]

theorem norm_hughesYoungC_verticalJet_le_const_mul_rpow
    {ε : ℝ} (hε : 0 < ε) {h : ℕ} (hh : 0 < h)
    {q z w : ℂ} (hq : q.re = 0)
    (hz : ‖z‖ ≤ 1 / 8) (hw : ‖w‖ ≤ 1 / 8) :
    ‖hughesYoungC h (-z) z (-w) w (1 + q / 2)‖ ≤
      (divisorEpsilonConstant (ε / 5)) ^ 5 * (h : ℝ) ^ ε := by
  apply norm_hughesYoungC_shiftedJet_le_const_mul_rpow hε hh
  · rw [hq]
    norm_num
  · exact hz
  · exact hw

theorem norm_hughesYoungEquation96LeftConstant_le
    {h : ℕ} (hh : 0 < h) :
    ‖hughesYoungEquation96LeftConstant h‖ ≤
      2 * |Real.eulerMascheroniConstant| + Real.log h := by
  unfold hughesYoungEquation96LeftConstant
  have hh1 : (1 : ℝ) ≤ h := by exact_mod_cast hh
  calc
    ‖2 * (Real.eulerMascheroniConstant : ℂ) - Complex.log (h : ℂ)‖ ≤
        ‖2 * (Real.eulerMascheroniConstant : ℂ)‖ +
          ‖Complex.log (h : ℂ)‖ := norm_sub_le _ _
    _ = 2 * |Real.eulerMascheroniConstant| + Real.log h := by
      rw [norm_mul, ← Complex.natCast_log, Complex.norm_real,
        Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (Real.log_nonneg hh1)]
      norm_num

theorem norm_hughesYoungEquation96RightConstant_le
    {k : ℕ} (hk : 0 < k) :
    ‖hughesYoungEquation96RightConstant k‖ ≤
      2 * |Real.eulerMascheroniConstant| + Real.log k := by
  simpa only [hughesYoungEquation96RightConstant,
    hughesYoungEquation96LeftConstant] using
      norm_hughesYoungEquation96LeftConstant_le hk

theorem norm_hughesYoungEquation96JetExponential_le
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    {r : ℝ} (hr : 0 ≤ r) {z w : ℂ} (hz : ‖z‖ ≤ r) (hw : ‖w‖ ≤ r) :
    ‖Complex.exp
        (z * hughesYoungEquation96LeftConstant h +
          w * hughesYoungEquation96RightConstant k)‖ ≤
      Real.exp (4 * r * |Real.eulerMascheroniConstant|) *
        (h : ℝ) ^ r * (k : ℝ) ^ r := by
  have hL := norm_hughesYoungEquation96LeftConstant_le hh
  have hR := norm_hughesYoungEquation96RightConstant_le hk
  rw [Complex.norm_exp]
  have hRe :
      (z * hughesYoungEquation96LeftConstant h +
          w * hughesYoungEquation96RightConstant k).re ≤
        r * (4 * |Real.eulerMascheroniConstant| +
          Real.log h + Real.log k) := by
    calc
      _ ≤ ‖z * hughesYoungEquation96LeftConstant h +
          w * hughesYoungEquation96RightConstant k‖ := Complex.re_le_norm _
      _ ≤ ‖z‖ * ‖hughesYoungEquation96LeftConstant h‖ +
          ‖w‖ * ‖hughesYoungEquation96RightConstant k‖ := by
        simpa only [norm_mul] using norm_add_le
          (z * hughesYoungEquation96LeftConstant h)
          (w * hughesYoungEquation96RightConstant k)
      _ ≤ r * (2 * |Real.eulerMascheroniConstant| + Real.log h) +
          r * (2 * |Real.eulerMascheroniConstant| + Real.log k) := by
        exact add_le_add
          (mul_le_mul hz hL (norm_nonneg _) hr)
          (mul_le_mul hw hR (norm_nonneg _) hr)
      _ = _ := by ring
  calc
    Real.exp
        (z * hughesYoungEquation96LeftConstant h +
          w * hughesYoungEquation96RightConstant k).re ≤
        Real.exp (r * (4 * |Real.eulerMascheroniConstant| +
          Real.log h + Real.log k)) := Real.exp_le_exp.mpr hRe
    _ = Real.exp (4 * r * |Real.eulerMascheroniConstant|) *
          (h : ℝ) ^ r * (k : ℝ) ^ r := by
      have hhR : (0 : ℝ) < h := by exact_mod_cast hh
      have hkR : (0 : ℝ) < k := by exact_mod_cast hk
      rw [show r * (4 * |Real.eulerMascheroniConstant| +
          Real.log h + Real.log k) =
        4 * r * |Real.eulerMascheroniConstant| +
          Real.log h * r + Real.log k * r by ring]
      rw [Real.exp_add, Real.exp_add, Real.rpow_def_of_pos hhR,
        Real.rpow_def_of_pos hkR]

/-- Uniform equation-(98) bound for the complete vertical jet.  The radius
and divisor exponents remain parameters so that they can later be chosen as
small fractions of the requested epsilon. -/
theorem norm_hughesYoungEquation96Jet_le_rpow
    {ε r : ℝ} (hε : 0 < ε) (hr0 : 0 ≤ r) (hr8 : r < 1 / 8)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (hhk : h.Coprime k)
    {q z w : ℂ} (hq : q.re = 0) (hz : ‖z‖ ≤ r) (hw : ‖w‖ ≤ r) :
    ‖hughesYoungEquation96Jet h k q z w‖ ≤
      (Real.exp (4 * r * |Real.eulerMascheroniConstant|) *
          hughesYoungZetaHalfPlaneMajorant ^ 3 *
          (divisorEpsilonConstant (ε / 5)) ^ 10) *
        ((h : ℝ) ^ (r + ε) * (k : ℝ) ^ (r + ε)) := by
  have hz8 : ‖z‖ < (1 / 8 : ℝ) := hz.trans_lt hr8
  have hw8 : ‖w‖ < (1 / 8 : ℝ) := hw.trans_lt hr8
  have hzRe : |z.re| ≤ r := (abs_re_le_norm z).trans hz
  have hwRe : |w.re| ≤ r := (abs_re_le_norm w).trans hw
  have hs1 : (3 / 2 : ℝ) ≤ (2 + q - z - w : ℂ).re := by
    norm_num [Complex.mul_re]
    rw [hq]
    linarith [le_abs_self z.re, le_abs_self w.re]
  have hs2 : (3 / 2 : ℝ) ≤ (3 + q + z + w : ℂ).re := by
    norm_num [Complex.mul_re]
    rw [hq]
    linarith [neg_abs_le z.re, neg_abs_le w.re]
  have hs3 : (3 / 2 : ℝ) ≤ (2 + 2 * z + 2 * w : ℂ).re := by
    norm_num [Complex.mul_re]
    linarith [neg_abs_le z.re, neg_abs_le w.re]
  have hzeta1 := norm_riemannZeta_le_hughesYoungZetaHalfPlaneMajorant hs1
  have hzeta2 := norm_riemannZeta_le_hughesYoungZetaHalfPlaneMajorant hs2
  have hzeta3 := norm_riemannZeta_inv_le_hughesYoungZetaHalfPlaneMajorant hs3
  have hCh := norm_hughesYoungC_verticalJet_le_const_mul_rpow
    hε hh hq (hz.trans (le_of_lt hr8)) (hw.trans (le_of_lt hr8))
  have hCk := norm_hughesYoungC_verticalJet_le_const_mul_rpow
    hε hk hq (hw.trans (le_of_lt hr8)) (hz.trans (le_of_lt hr8))
  have hExp := norm_hughesYoungEquation96JetExponential_le hh hk hr0 hz hw
  rw [hughesYoungEquation96Jet_eq_equation98_of_norm_lt
    hh hk hhk hq hz8 hw8]
  rw [div_eq_mul_inv]
  simp only [norm_mul]
  have hZ0 : 0 ≤ hughesYoungZetaHalfPlaneMajorant := by
    unfold hughesYoungZetaHalfPlaneMajorant
    positivity
  have hD0 : 0 ≤ divisorEpsilonConstant (ε / 5) := by
    exact (divisorEpsilonConstant_pos _).le
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  calc
    ‖Complex.exp
          (z * hughesYoungEquation96LeftConstant h +
            w * hughesYoungEquation96RightConstant k)‖ *
        (‖riemannZeta (2 + q - z - w)‖ *
          ‖riemannZeta (3 + q + z + w)‖ *
          ‖(riemannZeta (2 + 2 * z + 2 * w))⁻¹‖ *
          (‖hughesYoungC h (-z) z (-w) w (1 + q / 2)‖ *
            ‖hughesYoungC k (-w) w (-z) z (1 + q / 2)‖)) ≤
      (Real.exp (4 * r * |Real.eulerMascheroniConstant|) *
          (h : ℝ) ^ r * (k : ℝ) ^ r) *
        (hughesYoungZetaHalfPlaneMajorant *
          hughesYoungZetaHalfPlaneMajorant *
          hughesYoungZetaHalfPlaneMajorant *
          (((divisorEpsilonConstant (ε / 5)) ^ 5 * (h : ℝ) ^ ε) *
            ((divisorEpsilonConstant (ε / 5)) ^ 5 * (k : ℝ) ^ ε))) := by
        gcongr
    _ = (Real.exp (4 * r * |Real.eulerMascheroniConstant|) *
          hughesYoungZetaHalfPlaneMajorant ^ 3 *
          (divisorEpsilonConstant (ε / 5)) ^ 10) *
        ((h : ℝ) ^ (r + ε) * (k : ℝ) ^ (r + ε)) := by
      rw [Real.rpow_add hhR, Real.rpow_add hkR]
      ring

private noncomputable def hughesYoungJetLocalMajorantConstant
    (h k : ℕ) : ℝ :=
  Real.exp ((‖hughesYoungEquation96LeftConstant h‖ +
      ‖hughesYoungEquation96RightConstant k‖) / 32) *
    (hughesYoungGCDCPowBound h 2 * hughesYoungGCDCPowBound k 2) *
    (1 + 384 + 2 * |Real.eulerMascheroniConstant|) ^ 2 *
    ((h : ℝ) ^ (1 / 64 : ℝ) * (k : ℝ) ^ (1 / 64 : ℝ))

private theorem summable_hughesYoungJetLocalMajorant (h k : ℕ) :
    Summable (fun y : ℕ+ × ℕ+ =>
      hughesYoungJetLocalMajorantConstant h k *
        hughesYoungPositivePairMajorant (59 / 32) (29 / 32) y) :=
  (summable_hughesYoungPositivePairMajorant
    (show (1 : ℝ) < 59 / 32 by norm_num)
    (show (0 : ℝ) < 29 / 32 by norm_num)).mul_left
      (hughesYoungJetLocalMajorantConstant h k)

private theorem summable_hughesYoungEquation96JetTerm_of_mem_ball
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) {q z w : ℂ} (hq : q.re = 0)
    (hz : z ∈ Metric.ball (0 : ℂ) (1 / 32 : ℝ))
    (hw : w ∈ Metric.ball (0 : ℂ) (1 / 32 : ℝ)) :
    Summable (fun y : ℕ+ × ℕ+ =>
      hughesYoungEquation96JetTerm h k q z w y) := by
  apply Summable.of_norm_bounded (summable_hughesYoungJetLocalMajorant h k)
  intro y
  simpa [hughesYoungJetLocalMajorantConstant,
    hughesYoungDFIPositiveLogSelectorLeft,
    hughesYoungDFIPositiveLogSelectorRight] using
      norm_hughesYoungEquation96JetTerm_mul_logSelectors_le
        false false hh hk hq hz hw y

set_option maxHeartbeats 800000 in
theorem hasDerivAt_hughesYoungEquation96Jet_left_of_mem_ball
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) {q z w : ℂ} (hq : q.re = 0)
    (hz : z ∈ Metric.ball (0 : ℂ) (1 / 32 : ℝ))
    (hw : w ∈ Metric.ball (0 : ℂ) (1 / 32 : ℝ)) :
    HasDerivAt (fun v => hughesYoungEquation96Jet h k q v w)
      (∑' y : ℕ+ × ℕ+,
        hughesYoungEquation96JetTerm h k q z w y *
          hughesYoungDFIPositiveLogFactorLeft h y) z := by
  let u : ℕ+ × ℕ+ → ℝ := fun y =>
    hughesYoungJetLocalMajorantConstant h k *
      hughesYoungPositivePairMajorant (59 / 32) (29 / 32) y
  have hu : Summable u := summable_hughesYoungJetLocalMajorant h k
  have hzero : (0 : ℂ) ∈ Metric.ball 0 (1 / 32 : ℝ) := by
    simp [Metric.mem_ball]
  have hpoint := summable_hughesYoungEquation96JetTerm_of_mem_ball
    hh hk hq hzero hw
  have hsum := hasDerivAt_tsum_of_isPreconnected hu Metric.isOpen_ball
    Metric.isPreconnected_ball
    (fun y v _hv => hasDerivAt_hughesYoungEquation96JetTerm_left hh hk q v w y)
    (fun y v hv => by
      simpa [u, hughesYoungJetLocalMajorantConstant,
        hughesYoungDFIPositiveLogSelectorLeft,
        hughesYoungDFIPositiveLogSelectorRight] using
        norm_hughesYoungEquation96JetTerm_mul_logSelectors_le
          true false hh hk hq hv hw y)
    hzero hpoint hz
  simpa only [hughesYoungEquation96Jet] using hsum

set_option maxHeartbeats 800000 in
theorem hasDerivAt_hughesYoungEquation96Jet_right_of_mem_ball
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) {q z w : ℂ} (hq : q.re = 0)
    (hz : z ∈ Metric.ball (0 : ℂ) (1 / 32 : ℝ))
    (hw : w ∈ Metric.ball (0 : ℂ) (1 / 32 : ℝ)) :
    HasDerivAt (fun v => hughesYoungEquation96Jet h k q z v)
      (∑' y : ℕ+ × ℕ+,
        hughesYoungEquation96JetTerm h k q z w y *
          hughesYoungDFIPositiveLogFactorRight k y) w := by
  let u : ℕ+ × ℕ+ → ℝ := fun y =>
    hughesYoungJetLocalMajorantConstant h k *
      hughesYoungPositivePairMajorant (59 / 32) (29 / 32) y
  have hu : Summable u := summable_hughesYoungJetLocalMajorant h k
  have hzero : (0 : ℂ) ∈ Metric.ball 0 (1 / 32 : ℝ) := by
    simp [Metric.mem_ball]
  have hpoint := summable_hughesYoungEquation96JetTerm_of_mem_ball
    hh hk hq hz hzero
  have hsum := hasDerivAt_tsum_of_isPreconnected hu Metric.isOpen_ball
    Metric.isPreconnected_ball
    (fun y v _hv => hasDerivAt_hughesYoungEquation96JetTerm_right hh hk q z v y)
    (fun y v hv => by
      simpa [u, hughesYoungJetLocalMajorantConstant,
        hughesYoungDFIPositiveLogSelectorLeft,
        hughesYoungDFIPositiveLogSelectorRight] using
        norm_hughesYoungEquation96JetTerm_mul_logSelectors_le
          false true hh hk hq hz hv y)
    hzero hpoint hw
  simpa only [hughesYoungEquation96Jet] using hsum

set_option maxHeartbeats 800000 in
theorem hasDerivAt_hughesYoungEquation96JetLeftSeries_of_mem_ball
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) {q w : ℂ} (hq : q.re = 0)
    (hw : w ∈ Metric.ball (0 : ℂ) (1 / 32 : ℝ)) :
    HasDerivAt
      (fun v => ∑' y : ℕ+ × ℕ+,
        hughesYoungEquation96JetTerm h k q 0 v y *
          hughesYoungDFIPositiveLogFactorLeft h y)
      (∑' y : ℕ+ × ℕ+,
        hughesYoungEquation96JetTerm h k q 0 w y *
          hughesYoungDFIPositiveLogFactorLeft h y *
          hughesYoungDFIPositiveLogFactorRight k y) w := by
  let u : ℕ+ × ℕ+ → ℝ := fun y =>
    hughesYoungJetLocalMajorantConstant h k *
      hughesYoungPositivePairMajorant (59 / 32) (29 / 32) y
  have hu : Summable u := summable_hughesYoungJetLocalMajorant h k
  have hzero : (0 : ℂ) ∈ Metric.ball 0 (1 / 32 : ℝ) := by
    simp [Metric.mem_ball]
  have hpoint : Summable (fun y : ℕ+ × ℕ+ =>
      hughesYoungEquation96JetTerm h k q 0 0 y *
        hughesYoungDFIPositiveLogFactorLeft h y) := by
    simpa [hughesYoungDFIPositiveLogSelectorLeft,
      hughesYoungDFIPositiveLogSelectorRight] using
      summable_hughesYoungEquation96JetTerm_mul_logSelectors_zero
        true false hh hk hq
  exact hasDerivAt_tsum_of_isPreconnected hu Metric.isOpen_ball
    Metric.isPreconnected_ball
    (fun y v _hv => hasDerivAt_hughesYoungEquation96JetTerm_mixed hh hk q 0 v y)
    (fun y v hv => by
      simpa [u, hughesYoungJetLocalMajorantConstant,
        hughesYoungDFIPositiveLogSelectorLeft,
        hughesYoungDFIPositiveLogSelectorRight] using
        norm_hughesYoungEquation96JetTerm_mul_logSelectors_le
          true true hh hk hq hzero hv y)
    hzero hpoint hw

theorem diffContOnCl_hughesYoungEquation96Jet_left
    {r : ℝ} (hr32 : r < 1 / 32)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) {q w : ℂ} (hq : q.re = 0)
    (hw : ‖w‖ ≤ r) :
    DiffContOnCl ℂ (fun z => hughesYoungEquation96Jet h k q z w)
      (Metric.ball (0 : ℂ) r) := by
  apply DifferentiableOn.diffContOnCl
  intro z hz
  have hzClosed : z ∈ Metric.closedBall (0 : ℂ) r :=
    closure_ball_subset_closedBall hz
  have hzNorm : ‖z‖ ≤ r := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hzClosed
  have hzBig : z ∈ Metric.ball (0 : ℂ) (1 / 32 : ℝ) := by
    simpa [Metric.mem_ball, dist_zero_right] using hzNorm.trans_lt hr32
  have hwBig : w ∈ Metric.ball (0 : ℂ) (1 / 32 : ℝ) := by
    simpa [Metric.mem_ball, dist_zero_right] using hw.trans_lt hr32
  exact (hasDerivAt_hughesYoungEquation96Jet_left_of_mem_ball
    hh hk hq hzBig hwBig).differentiableAt.differentiableWithinAt

theorem diffContOnCl_hughesYoungEquation96Jet_right
    {r : ℝ} (hr32 : r < 1 / 32)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) {q z : ℂ} (hq : q.re = 0)
    (hz : ‖z‖ ≤ r) :
    DiffContOnCl ℂ (fun w => hughesYoungEquation96Jet h k q z w)
      (Metric.ball (0 : ℂ) r) := by
  apply DifferentiableOn.diffContOnCl
  intro w hw
  have hwClosed : w ∈ Metric.closedBall (0 : ℂ) r :=
    closure_ball_subset_closedBall hw
  have hwNorm : ‖w‖ ≤ r := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hwClosed
  have hzBig : z ∈ Metric.ball (0 : ℂ) (1 / 32 : ℝ) := by
    simpa [Metric.mem_ball, dist_zero_right] using hz.trans_lt hr32
  have hwBig : w ∈ Metric.ball (0 : ℂ) (1 / 32 : ℝ) := by
    simpa [Metric.mem_ball, dist_zero_right] using hwNorm.trans_lt hr32
  exact (hasDerivAt_hughesYoungEquation96Jet_right_of_mem_ball
    hh hk hq hzBig hwBig).differentiableAt.differentiableWithinAt

theorem diffContOnCl_hughesYoungEquation96JetLeftSeries
    {r : ℝ} (hr32 : r < 1 / 32)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) {q : ℂ} (hq : q.re = 0) :
    DiffContOnCl ℂ
      (fun w => ∑' y : ℕ+ × ℕ+,
        hughesYoungEquation96JetTerm h k q 0 w y *
          hughesYoungDFIPositiveLogFactorLeft h y)
      (Metric.ball (0 : ℂ) r) := by
  apply DifferentiableOn.diffContOnCl
  intro w hw
  have hwClosed : w ∈ Metric.closedBall (0 : ℂ) r :=
    closure_ball_subset_closedBall hw
  have hwNorm : ‖w‖ ≤ r := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hwClosed
  have hwBig : w ∈ Metric.ball (0 : ℂ) (1 / 32 : ℝ) := by
    simpa [Metric.mem_ball, dist_zero_right] using hwNorm.trans_lt hr32
  exact (hasDerivAt_hughesYoungEquation96JetLeftSeries_of_mem_ball
    hh hk hq hwBig).differentiableAt.differentiableWithinAt

/-- Cauchy's inequalities turn the uniform equation-(98) estimate into one
bound for all four arithmetic coefficients in equation (84). -/
theorem norm_hughesYoungEquation96JetCoefficient_le_rpow
    (i j : Bool) {ε r : ℝ} (hε : 0 < ε) (hr0 : 0 < r)
    (hr32 : r < 1 / 32) {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    (hhk : h.Coprime k) {q : ℂ} (hq : q.re = 0) :
    ‖hughesYoungEquation96JetCoefficient h k q i j‖ ≤
      ((Real.exp (4 * r * |Real.eulerMascheroniConstant|) *
          hughesYoungZetaHalfPlaneMajorant ^ 3 *
          (divisorEpsilonConstant (ε / 5)) ^ 10) *
        ((h : ℝ) ^ (r + ε) * (k : ℝ) ^ (r + ε))) / r ^ 2 := by
  let B : ℝ :=
    (Real.exp (4 * r * |Real.eulerMascheroniConstant|) *
        hughesYoungZetaHalfPlaneMajorant ^ 3 *
        (divisorEpsilonConstant (ε / 5)) ^ 10) *
      ((h : ℝ) ^ (r + ε) * (k : ℝ) ^ (r + ε))
  have hB0 : 0 ≤ B := by
    have hZ0 : 0 ≤ hughesYoungZetaHalfPlaneMajorant := by
      unfold hughesYoungZetaHalfPlaneMajorant
      positivity
    have hD0 : 0 ≤ divisorEpsilonConstant (ε / 5) :=
      (divisorEpsilonConstant_pos _).le
    dsimp only [B]
    positivity
  have hr1 : r ≤ 1 := (le_of_lt hr32).trans (by norm_num)
  have hrsq_le_r : r ^ 2 ≤ r := by nlinarith
  have hrsq_le_one : r ^ 2 ≤ 1 := hrsq_le_r.trans hr1
  have hJet (z w : ℂ) (hz : ‖z‖ ≤ r) (hw : ‖w‖ ≤ r) :
      ‖hughesYoungEquation96Jet h k q z w‖ ≤ B := by
    simpa only [B] using norm_hughesYoungEquation96Jet_le_rpow
      hε hr0.le (hr32.trans (by norm_num)) hh hk hhk hq hz hw
  have hzero : ‖(0 : ℂ)‖ ≤ r := by simp [hr0.le]
  cases i <;> cases j
  · rw [hughesYoungEquation96JetCoefficient_false_false h k q]
    exact (hJet 0 0 hzero hzero).trans (by
      apply (le_div_iff₀ (sq_pos_of_pos hr0)).2
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hrsq_le_one hB0)
  · rw [hughesYoungEquation96JetCoefficient_false_true_eq_deriv hh hk hq]
    have hCauchy := norm_deriv_le_of_forall_mem_sphere_norm_le hr0
      (diffContOnCl_hughesYoungEquation96Jet_left hr32 hh hk hq hzero)
      (fun z hz => hJet z 0 (by
        simpa [Metric.mem_sphere, dist_zero_right] using hz.le) hzero)
    exact hCauchy.trans (by
      change B / r ≤ B / r ^ 2
      exact div_le_div_of_nonneg_left hB0 (sq_pos_of_pos hr0) hrsq_le_r)
  · rw [hughesYoungEquation96JetCoefficient_true_false_eq_deriv hh hk hq]
    have hCauchy := norm_deriv_le_of_forall_mem_sphere_norm_le hr0
      (diffContOnCl_hughesYoungEquation96Jet_right hr32 hh hk hq hzero)
      (fun w hw => hJet 0 w hzero (by
        simpa [Metric.mem_sphere, dist_zero_right] using hw.le))
    exact hCauchy.trans (by
      change B / r ≤ B / r ^ 2
      exact div_le_div_of_nonneg_left hB0 (sq_pos_of_pos hr0) hrsq_le_r)
  · rw [hughesYoungEquation96JetCoefficient_true_true_eq_deriv hh hk hq]
    let g : ℂ → ℂ := fun w => ∑' y : ℕ+ × ℕ+,
      hughesYoungEquation96JetTerm h k q 0 w y *
        hughesYoungDFIPositiveLogFactorLeft h y
    have hgBound (w : ℂ) (hw : w ∈ Metric.sphere (0 : ℂ) r) :
        ‖g w‖ ≤ B / r := by
      have hwNorm : ‖w‖ ≤ r := by
        simpa [Metric.mem_sphere, dist_zero_right] using hw.le
      have hwBig : w ∈ Metric.ball (0 : ℂ) (1 / 32 : ℝ) := by
        simpa [Metric.mem_ball, dist_zero_right] using hwNorm.trans_lt hr32
      have hzBig : (0 : ℂ) ∈ Metric.ball 0 (1 / 32 : ℝ) := by
        simp [Metric.mem_ball]
      have hd := (hasDerivAt_hughesYoungEquation96Jet_left_of_mem_ball
        hh hk hq hzBig hwBig).deriv
      have hEq : g w = deriv (fun z =>
          hughesYoungEquation96Jet h k q z w) 0 := by
        dsimp only [g]
        rw [hd]
      rw [hEq]
      exact norm_deriv_le_of_forall_mem_sphere_norm_le hr0
        (diffContOnCl_hughesYoungEquation96Jet_left
          hr32 hh hk hq hwNorm)
        (fun z hz => hJet z w (by
          simpa [Metric.mem_sphere, dist_zero_right] using hz.le) hwNorm)
    have hCauchy := norm_deriv_le_of_forall_mem_sphere_norm_le hr0
      (diffContOnCl_hughesYoungEquation96JetLeftSeries
        hr32 hh hk hq) hgBound
    simpa only [g, div_div, pow_two] using hCauchy

/-- Uniform epsilon-power form of the differentiated equation-(98) bound.
The constant is independent of the vertical ordinate and of the coprime
arithmetic parameters. -/
theorem exists_uniform_norm_hughesYoungEquation96JetCoefficient_le
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (i j : Bool) {h k : ℕ},
      0 < h → 0 < k → h.Coprime k → ∀ {q : ℂ}, q.re = 0 →
      ‖hughesYoungEquation96JetCoefficient h k q i j‖ ≤
        C * (h : ℝ) ^ δ * (k : ℝ) ^ δ := by
  let r : ℝ := min (δ / 4) (1 / 64)
  let η : ℝ := δ / 2
  let A : ℝ :=
    (Real.exp (4 * r * |Real.eulerMascheroniConstant|) *
        hughesYoungZetaHalfPlaneMajorant ^ 3 *
        (divisorEpsilonConstant (η / 5)) ^ 10) / r ^ 2
  let C : ℝ := A + 1
  have hr0 : 0 < r := lt_min (div_pos hδ (by norm_num)) (by norm_num)
  have hr32 : r < 1 / 32 :=
    (min_le_right (δ / 4) (1 / 64)).trans_lt (by norm_num)
  have hη : 0 < η := div_pos hδ (by norm_num)
  have hrexp : r + η ≤ δ := by
    dsimp only [r, η]
    have hrδ : min (δ / 4) (1 / 64) ≤ δ / 4 := min_le_left _ _
    linarith
  have hA0 : 0 ≤ A := by
    have hZ0 : 0 ≤ hughesYoungZetaHalfPlaneMajorant := by
      unfold hughesYoungZetaHalfPlaneMajorant
      positivity
    have hD0 : 0 ≤ divisorEpsilonConstant (η / 5) :=
      (divisorEpsilonConstant_pos _).le
    dsimp only [A]
    positivity
  have hC : 0 < C := by dsimp only [C]; linarith
  refine ⟨C, hC, ?_⟩
  intro i j h k hh hk hhk q hq
  have hh1 : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hhpow : (h : ℝ) ^ (r + η) ≤ (h : ℝ) ^ δ :=
    Real.rpow_le_rpow_of_exponent_le hh1 hrexp
  have hkpow : (k : ℝ) ^ (r + η) ≤ (k : ℝ) ^ δ :=
    Real.rpow_le_rpow_of_exponent_le hk1 hrexp
  calc
    ‖hughesYoungEquation96JetCoefficient h k q i j‖ ≤
        ((Real.exp (4 * r * |Real.eulerMascheroniConstant|) *
            hughesYoungZetaHalfPlaneMajorant ^ 3 *
            (divisorEpsilonConstant (η / 5)) ^ 10) *
          ((h : ℝ) ^ (r + η) * (k : ℝ) ^ (r + η))) / r ^ 2 :=
      norm_hughesYoungEquation96JetCoefficient_le_rpow
        i j hη hr0 hr32 hh hk hhk hq
    _ = A * (h : ℝ) ^ (r + η) * (k : ℝ) ^ (r + η) := by
      dsimp only [A]
      field_simp
    _ ≤ C * (h : ℝ) ^ δ * (k : ℝ) ^ δ := by
      have hAC : A ≤ C := by dsimp only [C]; linarith
      gcongr

/-- Equation (84)'s four complete vertical arithmetic moments inherit the
same ordinate-uniform epsilon-power bound. -/
theorem exists_uniform_norm_hughesYoungEquation84CompletePositiveMomentAt_le
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (i j : Bool) {h k : ℕ},
      0 < h → 0 < k → h.Coprime k → ∀ u : ℝ,
      ‖hughesYoungEquation84CompletePositiveMomentAt h k i j u‖ ≤
        C * (h : ℝ) ^ δ * (k : ℝ) ^ δ := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_uniform_norm_hughesYoungEquation96JetCoefficient_le hδ
  refine ⟨C, hC, ?_⟩
  intro i j h k hh hk hhk u
  rw [hughesYoungEquation84CompletePositiveMomentAt_eq_jetCoefficient
    i j u hh hk hhk]
  apply hbound i j hh hk hhk
  simp

end RiemannZeta.GuthMaynard
