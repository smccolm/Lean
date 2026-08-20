import RiemannZeta.GuthMaynard.HughesYoungCentralResidue

open Complex Filter MeasureTheory Metric Set
open scoped BigOperators Interval Topology

noncomputable section

set_option maxHeartbeats 4000000

namespace RiemannZeta.GuthMaynard

/-!
# Infinite-height form of the Hughes--Young moving-pole shift

The finite rectangle theorem crosses the unique equation-(98) pole.  This
file supplies the uniform strip bounds needed to let its height tend to
infinity while the two auxiliary shifts remain generic.
-/

/-- The equation-(100) local-factor constant on a strip beginning at
`Re W = δ`.  The denominator margin is the source quantity
`1 - 2 ^ (-3δ/2)`. -/
noncomputable def hughesYoungCentralLocalFactorBound (δ : ℝ) : ℝ :=
  16 / (1 - (2 : ℝ) ^ (-(3 * δ / 2)))

private theorem hughesYoungCentralRho_lt_one {δ : ℝ} (hδ : 0 < δ) :
    (2 : ℝ) ^ (-(3 * δ / 2)) < 1 := by
  rw [Real.rpow_lt_one_iff_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact Or.inl ⟨by norm_num, by linarith⟩

private theorem norm_one_sub_ge_one_sub_of_norm_le {x : ℂ} {ρ : ℝ}
    (hx : ‖x‖ ≤ ρ) :
    1 - ρ ≤ ‖1 - x‖ := by
  have hrev := norm_sub_norm_le (1 : ℂ) x
  rw [norm_one] at hrev
  linarith

/-- Uniform equation-(100) prime-factor bound on the complete low strip.
It is independent of the contour height and of the prime exponent. -/
theorem norm_hughesYoungCPrimeFactor_centralStrip_le
    (e : ℕ) (p : Nat.Primes) {δ x y : ℝ} {z w : ℂ}
    (hδ0 : 0 < δ) (hδ4 : δ < 1 / 4)
    (hxδ : δ ≤ x) (hz : ‖z‖ ≤ δ / 4) (hw : ‖w‖ ≤ δ / 4) :
    ‖hughesYoungCPrimeFactor e p (-z) z (-w) w
        ((x : ℂ) + (y : ℂ) * I)‖ ≤
      hughesYoungCentralLocalFactorBound δ := by
  let W : ℂ := (x : ℂ) + (y : ℂ) * I
  let ξ : ℂ := (p : ℂ) ^ (z - w - 2 * W)
  let r : ℂ := (p : ℂ) ^ (-2 - 2 * z - 2 * w)
  let u : ℂ := (p : ℂ) ^ (-2 * w)
  let v : ℂ := (p : ℂ) ^ (-2 * z)
  let ρ : ℝ := (2 : ℝ) ^ (-(3 * δ / 2))
  have hzRe : |z.re| ≤ δ / 4 := (abs_re_le_norm z).trans hz
  have hwRe : |w.re| ≤ δ / 4 := (abs_re_le_norm w).trans hw
  have hξExp : (z - w - 2 * W).re ≤ -(3 * δ / 2) := by
    dsimp only [W]
    norm_num [Complex.mul_re]
    linarith [le_abs_self z.re, neg_abs_le w.re]
  have hδneg : -(3 * δ / 2) ≤ 0 := by linarith
  have hpOne : (1 : ℝ) ≤ p := by exact_mod_cast p.2.one_le
  have hpTwo : (2 : ℝ) ≤ p := by exact_mod_cast p.2.two_le
  have hξNorm : ‖ξ‖ ≤ ρ := by
    dsimp only [ξ, ρ]
    rw [Complex.norm_natCast_cpow_of_pos p.2.pos]
    calc
      ((p : ℕ) : ℝ) ^ (z - w - 2 * W).re ≤
          ((p : ℕ) : ℝ) ^ (-(3 * δ / 2)) :=
        Real.rpow_le_rpow_of_exponent_le hpOne hξExp
      _ ≤ (2 : ℝ) ^ (-(3 * δ / 2)) :=
        Real.antitoneOn_rpow_Ioi_of_exponent_nonpos hδneg
          (by norm_num) (show ((p : ℕ) : ℝ) ∈ Set.Ioi 0 by
            change 0 < ((p : ℕ) : ℝ)
            exact_mod_cast p.2.pos) hpTwo
  have hρ0 : 0 ≤ ρ := Real.rpow_nonneg (by norm_num) _
  have hρ1 : ρ < 1 := hughesYoungCentralRho_lt_one hδ0
  have hξOne : ‖ξ‖ ≤ 1 := hξNorm.trans hρ1.le
  have hξPow (n : ℕ) : ‖ξ ^ n‖ ≤ 1 := by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg ξ) hξOne
  have hrExp : (-2 - 2 * z - 2 * w : ℂ).re ≤ -1 := by
    norm_num [Complex.mul_re]
    linarith [neg_abs_le z.re, neg_abs_le w.re]
  have hrNorm : ‖r‖ ≤ 1 / 2 := by
    dsimp only [r]
    exact norm_prime_cpow_le_half_of_re_le_neg_one p hrExp
  have hC0 : ‖hughesYoungC0 e ξ‖ ≤ 2 := by
    unfold hughesYoungC0
    exact (norm_sub_le _ _).trans (by rw [norm_one]; linarith [hξPow (1 + e)])
  have hOneSubPow : ‖1 - ξ ^ e‖ ≤ 2 :=
    (norm_sub_le _ _).trans (by rw [norm_one]; linarith [hξPow e])
  have hpu : ‖(p : ℂ) ^ (-1 : ℂ) * u‖ ≤ 1 := by
    dsimp only [u]
    apply norm_prime_cpow_mul_prime_cpow_le_one p
    norm_num [Complex.mul_re]
    linarith [neg_abs_le w.re]
  have hpvξ : ‖(p : ℂ) ^ (-1 : ℂ) * (v * ξ)‖ ≤ 1 := by
    dsimp only [v, ξ, W]
    rw [← mul_assoc]
    apply norm_prime_cpow_three_mul_le_one p
    norm_num [Complex.mul_re]
    linarith [neg_abs_le z.re, neg_abs_le w.re]
  have hC1 :
      ‖(p : ℂ) ^ (-1 : ℂ) * hughesYoungC1 e u v ξ‖ ≤ 4 := by
    unfold hughesYoungC1
    rw [show (p : ℂ) ^ (-1 : ℂ) * ((u + v * ξ) * (1 - ξ ^ e)) =
        ((p : ℂ) ^ (-1 : ℂ) * (u + v * ξ)) * (1 - ξ ^ e) by ring,
      norm_mul]
    calc
      ‖(p : ℂ) ^ (-1 : ℂ) * (u + v * ξ)‖ * ‖1 - ξ ^ e‖ ≤
          (‖(p : ℂ) ^ (-1 : ℂ) * u‖ +
            ‖(p : ℂ) ^ (-1 : ℂ) * (v * ξ)‖) * 2 := by
        gcongr
        rw [mul_add]
        exact norm_add_le _ _
      _ ≤ (1 + 1) * 2 := by gcongr
      _ = 4 := by norm_num
  have hregularMonomial :
      ‖(p : ℂ) ^ (-2 : ℂ) * (p : ℂ) ^ (-2 * z - 2 * w)‖ ≤ 1 := by
    apply norm_prime_cpow_mul_prime_cpow_le_one p
    norm_num [Complex.mul_re]
    linarith [neg_abs_le z.re, neg_abs_le w.re]
  have hC2raw : ‖hughesYoungC2 e ξ‖ ≤ 2 := by
    unfold hughesYoungC2
    exact (norm_sub_le _ _).trans (by linarith [hξNorm, hρ1.le, hξPow e])
  have hC2 :
      ‖(p : ℂ) ^ (-2 : ℂ) *
          ((p : ℂ) ^ (-2 * z - 2 * w) * hughesYoungC2 e ξ)‖ ≤ 2 := by
    rw [← mul_assoc, norm_mul]
    exact (mul_le_mul hregularMonomial hC2raw (norm_nonneg _)
      (by positivity)).trans (by norm_num)
  have hnum :
      ‖hughesYoungC0 e ξ - (p : ℂ) ^ (-1 : ℂ) * hughesYoungC1 e u v ξ +
          (p : ℂ) ^ (-2 : ℂ) *
            ((p : ℂ) ^ (-2 * z - 2 * w) * hughesYoungC2 e ξ)‖ ≤ 8 := by
    calc
      _ ≤ ‖hughesYoungC0 e ξ‖ +
          ‖(p : ℂ) ^ (-1 : ℂ) * hughesYoungC1 e u v ξ‖ +
          ‖(p : ℂ) ^ (-2 : ℂ) *
            ((p : ℂ) ^ (-2 * z - 2 * w) * hughesYoungC2 e ξ)‖ := by
        exact (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
      _ ≤ 2 + 4 + 2 := by gcongr
      _ = 8 := by norm_num
  have hdenR : (1 / 2 : ℝ) ≤ ‖1 - r‖ :=
    half_le_norm_one_sub_of_norm_le_half hrNorm
  have hdenXi : 1 - ρ ≤ ‖1 - ξ‖ :=
    norm_one_sub_ge_one_sub_of_norm_le hξNorm
  have hmargin : 0 < 1 - ρ := sub_pos.mpr hρ1
  unfold hughesYoungCPrimeFactor hughesYoungCPrimeNumerator
  dsimp only
  rw [show -(-z) - w - 2 * ((x : ℂ) + (y : ℂ) * I) =
      z - w - 2 * W by dsimp [W]; ring]
  rw [show -2 + (-z) - z + (-w) - w = -2 - 2 * z - 2 * w by ring]
  rw [show (-w) - w = -2 * w by ring,
    show (-z) - z = -2 * z by ring,
    show -2 * z + (-w) - w = -2 * z - 2 * w by ring]
  change ‖(hughesYoungC0 e ξ - (p : ℂ) ^ (-1 : ℂ) *
      hughesYoungC1 e u v ξ + (p : ℂ) ^ (-2 : ℂ) *
        ((p : ℂ) ^ (-2 * z - 2 * w) * hughesYoungC2 e ξ)) /
      ((1 - r) * (1 - ξ))‖ ≤ hughesYoungCentralLocalFactorBound δ
  rw [norm_div, norm_mul]
  unfold hughesYoungCentralLocalFactorBound
  dsimp only [ρ] at hmargin hdenXi ⊢
  let m : ℝ := 1 - (2 : ℝ) ^ (-(3 * δ / 2))
  let D : ℝ := ‖1 - r‖ * ‖1 - ξ‖
  have hDlower : (1 / 2 : ℝ) * m ≤ D := by
    dsimp only [m, D]
    exact mul_le_mul hdenR hdenXi hmargin.le (norm_nonneg (1 - r))
  have hDpos : 0 < D := (mul_pos (by norm_num) (by simpa only [m] using hmargin)).trans_le hDlower
  apply (div_le_iff₀ hDpos).2
  apply hnum.trans
  have h8 : 8 * m ≤ 16 * D := by nlinarith
  calc
    (8 : ℝ) ≤ (16 * D) / m := (le_div_iff₀ (by simpa only [m] using hmargin)).2 h8
    _ = (16 / m) * D := by ring

/-- The complete finite equation-(100) Euler correction inherits the
primewise strip bound. -/
theorem norm_hughesYoungC_centralStrip_le
    (n : ℕ) {δ x y : ℝ} {z w : ℂ}
    (hδ0 : 0 < δ) (hδ4 : δ < 1 / 4)
    (hxδ : δ ≤ x) (hz : ‖z‖ ≤ δ / 4) (hw : ‖w‖ ≤ δ / 4) :
    ‖hughesYoungC n (-z) z (-w) w ((x : ℂ) + (y : ℂ) * I)‖ ≤
      (max 1 (hughesYoungCentralLocalFactorBound δ)) ^
        (hughesYoungPrimeFactors n).card := by
  unfold hughesYoungC
  rw [norm_prod]
  calc
    (∏ p ∈ hughesYoungPrimeFactors n,
        ‖hughesYoungCPrimeFactor (n.factorization p) p
          (-z) z (-w) w ((x : ℂ) + (y : ℂ) * I)‖) ≤
        ∏ _p ∈ hughesYoungPrimeFactors n,
          max 1 (hughesYoungCentralLocalFactorBound δ) := by
      apply Finset.prod_le_prod
      · intro p hp
        positivity
      · intro p hp
        have hlocal := norm_hughesYoungCPrimeFactor_centralStrip_le
          (n.factorization p) p (y := y) hδ0 hδ4 hxδ hz hw
        exact hlocal.trans
          (le_max_right 1 (hughesYoungCentralLocalFactorBound δ))
    _ = _ := by simp

/-- Abel's formula gives a strip-uniform polynomial bound for zeta at any
fixed positive distance from the imaginary axis. -/
theorem norm_riemannZeta_le_one_add_inv_mul_norm
    {δ : ℝ} (hδ0 : 0 < δ) {s : ℂ}
    (hsδ : δ ≤ s.re) (hsIm : 1 ≤ |s.im|) :
    ‖riemannZeta s‖ ≤ (1 + 1 / δ) * ‖s‖ := by
  have hs0 : 0 < s.re := hδ0.trans_le hsδ
  have hs1 : s ≠ 1 := by
    intro h
    subst s
    norm_num at hsIm
  have hden : 1 ≤ ‖s - 1‖ := by
    calc
      1 ≤ |(s - 1).im| := by simpa using hsIm
      _ ≤ ‖s - 1‖ := abs_im_le_norm _
  have hrem : ‖abelZetaRemainder s‖ ≤ 1 / δ := by
    calc
      ‖abelZetaRemainder s‖ ≤ 1 / s.re := norm_abelZetaRemainder_le hs0
      _ ≤ 1 / δ := by
        exact (one_div_le_one_div_of_le hδ0 hsδ)
  rw [riemannZeta_eq_abel hs0 hs1]
  calc
    ‖s / (s - 1) - s * abelZetaRemainder s‖ ≤
        ‖s / (s - 1)‖ + ‖s * abelZetaRemainder s‖ := norm_sub_le _ _
    _ = ‖s‖ / ‖s - 1‖ + ‖s‖ * ‖abelZetaRemainder s‖ := by
      rw [norm_div, norm_mul]
    _ ≤ ‖s‖ + ‖s‖ * (1 / δ) := by
      gcongr
      exact div_le_self (norm_nonneg s) hden
    _ = (1 + 1 / δ) * ‖s‖ := by ring

/-- The reversed four-coefficient kernel has the same Gaussian envelope as
its four constituent equation-(84) kernels. -/
theorem exists_norm_hughesYoungCentralReverseKernelPolynomial_horizontal_le
    (t : ℝ) {δ : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ {z w : ℂ},
      ‖z‖ ≤ δ / 4 → ‖w‖ ≤ δ / 4 → ∀ (y : ℝ),
        1 ≤ |y| → |t| + 1 ≤ |y| → ∀ x ∈ Set.Icc δ 1,
          ‖hughesYoungCentralReverseKernelPolynomial t
              ((x : ℂ) + (y : ℂ) * I) z w‖ ≤
            C * Real.exp (100 - 60 * y ^ 2) *
              (3 + |t| + |y|) ^ 9 := by
  obtain ⟨B, hB, hK⟩ :=
    exists_norm_hughesYoungEquation84KernelCoefficients_horizontal_le
      t hδ0 (by norm_num : (1 : ℝ) < 3 / 2) hδ1
  let A : ℝ := 1 + δ / 4 + δ / 4 + (δ / 4) * (δ / 4)
  let C : ℝ := A * B
  have hA : 0 < A := by dsimp [A]; nlinarith
  refine ⟨C, mul_pos hA hB, ?_⟩
  intro z w hz hw y hy hty x hx
  rcases hK y hy hty x hx with ⟨h00, h10, h01, h11⟩
  let G : ℝ := Real.exp (100 - 60 * y ^ 2)
  let R : ℝ := (3 + |t| + |y|) ^ 9
  have hG : 0 ≤ G := by dsimp [G]; positivity
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hbase :
      B * Real.exp (100 * (1 : ℝ) ^ 2 - 60 * y ^ 2) *
          (2 + |t| + (1 : ℝ) + |y|) ^ 9 = B * G * R := by
    dsimp [G, R]
    have he : 100 * (1 : ℝ) ^ 2 - 60 * y ^ 2 = 100 - 60 * y ^ 2 := by ring
    have hr : 2 + |t| + (1 : ℝ) + |y| = 3 + |t| + |y| := by ring
    rw [he, hr]
  rw [hbase] at h00 h10 h01 h11
  unfold hughesYoungCentralReverseKernelPolynomial
  calc
    ‖hughesYoungEquation84Kernel11 t ((x : ℂ) + (y : ℂ) * I) +
        z * hughesYoungEquation84Kernel10 t ((x : ℂ) + (y : ℂ) * I) +
        w * hughesYoungEquation84Kernel01 t ((x : ℂ) + (y : ℂ) * I) +
        z * w * hughesYoungEquation84Kernel00 t ((x : ℂ) + (y : ℂ) * I)‖ ≤
      ‖hughesYoungEquation84Kernel11 t ((x : ℂ) + (y : ℂ) * I)‖ +
        ‖z‖ * ‖hughesYoungEquation84Kernel10 t ((x : ℂ) + (y : ℂ) * I)‖ +
        ‖w‖ * ‖hughesYoungEquation84Kernel01 t ((x : ℂ) + (y : ℂ) * I)‖ +
        (‖z‖ * ‖w‖) *
          ‖hughesYoungEquation84Kernel00 t ((x : ℂ) + (y : ℂ) * I)‖ := by
      calc
        _ ≤ ‖_ + _ + _‖ + ‖_‖ := norm_add_le _ _
        _ ≤ (‖_ + _‖ + ‖_‖) + ‖_‖ := by gcongr; exact norm_add_le _ _
        _ ≤ ((‖_‖ + ‖_‖) + ‖_‖) + ‖_‖ := by gcongr; exact norm_add_le _ _
        _ = _ := by simp only [norm_mul]
    _ ≤ B * G * R + ‖z‖ * (B * G * R) +
        ‖w‖ * (B * G * R) + (‖z‖ * ‖w‖) * (B * G * R) := by
      have hsum :=
        add_le_add (add_le_add (add_le_add h11
          (mul_le_mul_of_nonneg_left h10 (norm_nonneg z)))
          (mul_le_mul_of_nonneg_left h01 (norm_nonneg w)))
          (mul_le_mul_of_nonneg_left h00
            (mul_nonneg (norm_nonneg z) (norm_nonneg w)))
      simpa only [add_assoc] using hsum
    _ ≤ B * G * R + (δ / 4) * (B * G * R) +
        (δ / 4) * (B * G * R) +
          ((δ / 4) * (δ / 4)) * (B * G * R) := by
      gcongr
    _ = C * Real.exp (100 - 60 * y ^ 2) * (3 + |t| + |y|) ^ 9 := by
      dsimp [C, A, G, R]
      ring

/-- The reduced Mellin and mollifier factor is independent of the vertical
height in norm and hence uniformly bounded on the closed real-part strip. -/
theorem exists_uniform_norm_hughesYoungCompleteCentralStatic
    (T t : ℝ) (h k a b : ℕ) {δ : ℝ} :
    ∃ C : ℝ, 0 < C ∧ ∀ (y x : ℝ), x ∈ Set.Icc δ 1 →
      ‖(((a : ℂ) * b)⁻¹) *
        hughesYoungReducedMellinStaticComplex T t h k
          ((x : ℂ) + (y : ℂ) * I)‖ ≤ C := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_uniform_norm_hughesYoungCentralOuterFactor
      T t h k 1 (((a : ℂ) * b)⁻¹) (c₀ := δ) (c₁ := 1)
  refine ⟨C, hC, ?_⟩
  intro y x hx
  have h := hbound y x hx
  simpa [hughesYoungCentralShiftPower] using h

/-- The complete generic-shift master has a Gaussian horizontal envelope
on the whole residue-crossing strip.  The extra degree two, relative to the
kernel bound, is exactly the cost of the two numerator zeta factors. -/
theorem exists_uniform_norm_hughesYoungCompletePositiveCentralMeromorphic_horizontal_le
    (T t : ℝ) (h k a b : ℕ) {δ : ℝ}
    (hδ0 : 0 < δ) (hδ4 : δ < 1 / 4) :
    ∃ C : ℝ, 0 < C ∧ ∀ {z w : ℂ},
      ‖z‖ ≤ δ / 4 → ‖w‖ ≤ δ / 4 → ∀ (y : ℝ),
      1 ≤ |y| → |t| + 1 ≤ |y| → ∀ x ∈ Set.Icc δ 1,
        ‖hughesYoungCompletePositiveCentralMeromorphic
            T t h k a b z w ((x : ℂ) + (y : ℂ) * I)‖ ≤
          C * Real.exp (100 - 60 * y ^ 2) *
            (3 + |t| + |y|) ^ 11 := by
  have hδ1 : δ ≤ 1 := hδ4.le.trans (by norm_num)
  obtain ⟨K, hK, hStatic⟩ :=
    exists_uniform_norm_hughesYoungCompleteCentralStatic
      T t h k a b (δ := δ)
  obtain ⟨B, hB, hKernel⟩ :=
    exists_norm_hughesYoungCentralReverseKernelPolynomial_horizontal_le
      t hδ0 hδ1
  let E : ℝ := Real.exp ((δ / 4) *
    (‖hughesYoungEquation96LeftConstant a‖ +
      ‖hughesYoungEquation96RightConstant b‖))
  let Z : ℝ := 1 + 1 / (3 * δ / 2)
  let D : ℝ := max 1 hughesYoungZetaHalfPlaneMajorant
  let A : ℝ := (max 1 (hughesYoungCentralLocalFactorBound δ)) ^
    (hughesYoungPrimeFactors a).card
  let Cb : ℝ := (max 1 (hughesYoungCentralLocalFactorBound δ)) ^
    (hughesYoungPrimeFactors b).card
  let C : ℝ := K * E * (4 * Z) ^ 2 * D * A * Cb * B
  have hE : 0 < E := by dsimp [E]; positivity
  have hZ : 0 < Z := by
    dsimp [Z]
    have : 0 < 3 * δ / 2 := by positivity
    positivity
  have hD : 0 < D := lt_max_of_lt_left zero_lt_one
  have hA : 0 < A := by
    dsimp [A]
    exact pow_pos (lt_max_of_lt_left zero_lt_one) _
  have hCb : 0 < Cb := by
    dsimp [Cb]
    exact pow_pos (lt_max_of_lt_left zero_lt_one) _
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro z w hz hw y hy hty x hx
  let W : ℂ := (x : ℂ) + (y : ℂ) * I
  let s₁ : ℂ := 2 * W - z - w
  let s₂ : ℂ := 1 + 2 * W + z + w
  let s₃ : ℂ := 2 + 2 * z + 2 * w
  let R : ℝ := 3 + |t| + |y|
  let G : ℝ := Real.exp (100 - 60 * y ^ 2)
  have hx0 : 0 ≤ x := hδ0.le.trans hx.1
  have hWnorm : ‖W‖ ≤ 1 + |y| := by
    calc
      ‖W‖ ≤ |W.re| + |W.im| := Complex.norm_le_abs_re_add_abs_im W
      _ = |x| + |y| := by simp [W]
      _ ≤ 1 + |y| := by rw [abs_of_nonneg hx0]; gcongr; exact hx.2
  have hzRe : |z.re| ≤ δ / 4 := (abs_re_le_norm z).trans hz
  have hwRe : |w.re| ≤ δ / 4 := (abs_re_le_norm w).trans hw
  have hzIm : |z.im| ≤ δ / 4 := (abs_im_le_norm z).trans hz
  have hwIm : |w.im| ≤ δ / 4 := (abs_im_le_norm w).trans hw
  have himSmall : |z.im + w.im| ≤ δ / 2 := by
    calc
      |z.im + w.im| ≤ |z.im| + |w.im| := abs_add_le _ _
      _ ≤ δ / 4 + δ / 4 := add_le_add hzIm hwIm
      _ = δ / 2 := by ring
  have hs₁Re : 3 * δ / 2 ≤ s₁.re := by
    dsimp [s₁, W]
    norm_num [Complex.mul_re]
    linarith [hx.1, le_abs_self z.re, le_abs_self w.re]
  have hs₂Re : 3 * δ / 2 ≤ s₂.re := by
    dsimp [s₂, W]
    norm_num [Complex.mul_re]
    linarith [hx.1, neg_abs_le z.re, neg_abs_le w.re]
  have hs₃Re : (3 / 2 : ℝ) ≤ s₃.re := by
    dsimp [s₃]
    norm_num [Complex.mul_re]
    linarith [neg_abs_le z.re, neg_abs_le w.re]
  have hs₁Im : 1 ≤ |s₁.im| := by
    have htri : |2 * y| ≤ |s₁.im| + |z.im + w.im| := by
      have := abs_add_le (s₁.im) (z.im + w.im)
      have heq : s₁.im + (z.im + w.im) = 2 * y := by
        dsimp [s₁, W]
        norm_num [Complex.mul_im]
      rwa [heq] at this
    rw [abs_mul] at htri
    norm_num at htri
    nlinarith [hδ4]
  have hs₂Im : 1 ≤ |s₂.im| := by
    have htri : |2 * y| ≤ |s₂.im| + |z.im + w.im| := by
      have hsum := abs_add_le (s₂.im) (-(z.im + w.im))
      have heq : s₂.im + (-(z.im + w.im)) = 2 * y := by
        dsimp [s₂, W]
        norm_num [Complex.mul_im]
      rw [heq, abs_neg] at hsum
      exact hsum
    rw [abs_mul] at htri
    norm_num at htri
    nlinarith [hδ4]
  have hR1 : 1 ≤ R := by
    dsimp [R]
    nlinarith [abs_nonneg t, abs_nonneg y]
  have hs₁Norm : ‖s₁‖ ≤ 4 * R := by
    have htri : ‖s₁‖ ≤ 2 * ‖W‖ + ‖z‖ + ‖w‖ := by
      dsimp [s₁]
      calc
        ‖2 * W - z - w‖ ≤ ‖2 * W‖ + ‖z‖ + ‖w‖ := by
          exact (norm_sub_le _ _).trans
            (add_le_add (norm_sub_le _ _) le_rfl)
        _ = 2 * ‖W‖ + ‖z‖ + ‖w‖ := by norm_num
    dsimp [R]
    nlinarith [hWnorm, hz, hw, abs_nonneg t, abs_nonneg y, hδ4]
  have hs₂Norm : ‖s₂‖ ≤ 4 * R := by
    have htri : ‖s₂‖ ≤ 1 + 2 * ‖W‖ + ‖z‖ + ‖w‖ := by
      dsimp [s₂]
      calc
        ‖1 + 2 * W + z + w‖ ≤ ‖1 + 2 * W + z‖ + ‖w‖ := norm_add_le _ _
        _ ≤ (‖1 + 2 * W‖ + ‖z‖) + ‖w‖ := by
          gcongr
          exact norm_add_le _ _
        _ ≤ (‖(1 : ℂ)‖ + ‖2 * W‖ + ‖z‖) + ‖w‖ := by
          gcongr
          exact norm_add_le _ _
        _ = 1 + 2 * ‖W‖ + ‖z‖ + ‖w‖ := by norm_num
    dsimp [R]
    nlinarith [hWnorm, hz, hw, abs_nonneg t, abs_nonneg y, hδ4]
  have hzeta₁ : ‖riemannZeta s₁‖ ≤ (4 * Z) * R := by
    have hzeta := norm_riemannZeta_le_one_add_inv_mul_norm
      (show 0 < 3 * δ / 2 by positivity) hs₁Re hs₁Im
    calc
      ‖riemannZeta s₁‖ ≤ Z * ‖s₁‖ := by simpa only [Z] using hzeta
      _ ≤ Z * (4 * R) := mul_le_mul_of_nonneg_left hs₁Norm hZ.le
      _ = (4 * Z) * R := by ring
  have hzeta₂ : ‖riemannZeta s₂‖ ≤ (4 * Z) * R := by
    have hzeta := norm_riemannZeta_le_one_add_inv_mul_norm
      (show 0 < 3 * δ / 2 by positivity) hs₂Re hs₂Im
    calc
      ‖riemannZeta s₂‖ ≤ Z * ‖s₂‖ := by simpa only [Z] using hzeta
      _ ≤ Z * (4 * R) := mul_le_mul_of_nonneg_left hs₂Norm hZ.le
      _ = (4 * Z) * R := by ring
  have hzeta₃ : ‖(riemannZeta s₃)⁻¹‖ ≤ D :=
    (norm_riemannZeta_inv_le_hughesYoungZetaHalfPlaneMajorant hs₃Re).trans
      (le_max_right 1 hughesYoungZetaHalfPlaneMajorant)
  have hCa : ‖hughesYoungC a (-z) z (-w) w W‖ ≤ A := by
    simpa only [A, W] using norm_hughesYoungC_centralStrip_le
      a hδ0 hδ4 hx.1 hz hw
  have hCb' : ‖hughesYoungC b (-w) w (-z) z W‖ ≤ Cb := by
    simpa only [Cb, W, add_comm] using norm_hughesYoungC_centralStrip_le
      b (z := w) (w := z) hδ0 hδ4 hx.1 hw hz
  have hstatic : ‖(((a : ℂ) * b)⁻¹)‖ *
      ‖hughesYoungReducedMellinStaticComplex T t h k W‖ ≤ K := by
    simpa only [norm_mul, W] using hStatic y x hx
  have hkernel : ‖hughesYoungCentralReverseKernelPolynomial t W z w‖ ≤
      B * G * R ^ 9 := by
    simpa only [W, G, R] using hKernel hz hw y hy hty x hx
  have hexp : ‖Complex.exp
      (z * hughesYoungEquation96LeftConstant a +
        w * hughesYoungEquation96RightConstant b)‖ ≤ E := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    calc
      (z * hughesYoungEquation96LeftConstant a +
          w * hughesYoungEquation96RightConstant b).re ≤
          ‖z * hughesYoungEquation96LeftConstant a +
            w * hughesYoungEquation96RightConstant b‖ :=
        Complex.re_le_norm _
      _ ≤ ‖z‖ * ‖hughesYoungEquation96LeftConstant a‖ +
          ‖w‖ * ‖hughesYoungEquation96RightConstant b‖ := by
        simpa only [norm_mul] using norm_add_le
          (z * hughesYoungEquation96LeftConstant a)
          (w * hughesYoungEquation96RightConstant b)
      _ ≤ (δ / 4) * ‖hughesYoungEquation96LeftConstant a‖ +
          (δ / 4) * ‖hughesYoungEquation96RightConstant b‖ := by
        gcongr
      _ = (δ / 4) *
          (‖hughesYoungEquation96LeftConstant a‖ +
            ‖hughesYoungEquation96RightConstant b‖) := by ring
  have hG : 0 ≤ G := by dsimp [G]; positivity
  have hR : 0 ≤ R := by dsimp [R]; positivity
  unfold hughesYoungCompletePositiveCentralMeromorphic
    hughesYoungCompletePositiveCentralPoleFree
    hughesYoungEquation96PoleFreeMasterJet
  rw [div_eq_mul_inv]
  simp only [norm_mul]
  change ‖riemannZeta s₁‖ *
      ((‖(((a : ℂ) * b)⁻¹)‖ *
          ‖hughesYoungReducedMellinStaticComplex T t h k W‖) *
        (‖Complex.exp
            (z * hughesYoungEquation96LeftConstant a +
              w * hughesYoungEquation96RightConstant b)‖ *
          ((‖riemannZeta s₂‖ * ‖(riemannZeta s₃)⁻¹‖) *
            (‖hughesYoungC a (-z) z (-w) w W‖ *
              ‖hughesYoungC b (-w) w (-z) z W‖)) *
          ‖hughesYoungCentralReverseKernelPolynomial t W z w‖)) ≤ _
  calc
    _ ≤ (4 * Z * R) *
        (K * (E * (((4 * Z * R) * D) * (A * Cb)) *
          (B * G * R ^ 9))) := by gcongr
    _ = C * Real.exp (100 - 60 * y ^ 2) *
        (3 + |t| + |y|) ^ 11 := by
      dsimp [C, G, R]
      ring

/-- Fixed-shift specialization of the locally uniform bidisc estimate. -/
theorem exists_norm_hughesYoungCompletePositiveCentralMeromorphic_horizontal_le
    (T t : ℝ) (h k a b : ℕ) {δ : ℝ} {z w : ℂ}
    (hδ0 : 0 < δ) (hδ4 : δ < 1 / 4)
    (hz : ‖z‖ ≤ δ / 4) (hw : ‖w‖ ≤ δ / 4) :
    ∃ C : ℝ, 0 < C ∧ ∀ (y : ℝ),
      1 ≤ |y| → |t| + 1 ≤ |y| → ∀ x ∈ Set.Icc δ 1,
        ‖hughesYoungCompletePositiveCentralMeromorphic
            T t h k a b z w ((x : ℂ) + (y : ℂ) * I)‖ ≤
          C * Real.exp (100 - 60 * y ^ 2) *
            (3 + |t| + |y|) ^ 11 := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_uniform_norm_hughesYoungCompletePositiveCentralMeromorphic_horizontal_le
      T t h k a b hδ0 hδ4
  exact ⟨C, hC, hbound hz hw⟩

/-- An eleventh-degree polynomial is still dominated by the Gaussian
appearing in the completed-zeta contour kernel. -/
theorem tendsto_const_mul_exp_sub_sixty_sq_mul_shift_pow_eleven
    (C A B : ℝ) (hC : 0 ≤ C) (hB : 0 ≤ B) :
    Tendsto (fun H : ℝ =>
      C * Real.exp (A - 60 * H ^ 2) * (B + H) ^ 11) atTop (nhds 0) := by
  have hExp : Tendsto (fun H : ℝ => Real.exp (-(1 / 2 : ℝ) * H))
      atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg
        (by norm_num : (-(1 / 2 : ℝ)) < 0))
  have hbaseRpow : Tendsto (fun H : ℝ =>
      H ^ (11 : ℝ) * Real.exp (-60 * H ^ 2)) atTop (nhds 0) :=
    (rpow_mul_exp_neg_mul_sq_isLittleO_exp_neg
      (by norm_num : (0 : ℝ) < 60) 11).tendsto_zero_of_tendsto hExp
  have hbase : Tendsto (fun H : ℝ =>
      H ^ 11 * Real.exp (-60 * H ^ 2)) atTop (nhds 0) := by
    simpa only [← Real.rpow_natCast] using hbaseRpow
  let D : ℝ := C * Real.exp A * 2048
  have hmajor : Tendsto (fun H : ℝ =>
      D * (H ^ 11 * Real.exp (-60 * H ^ 2))) atTop (nhds 0) := by
    simpa only [mul_zero] using hbase.const_mul D
  apply squeeze_zero'
    (show ∀ᶠ H : ℝ in atTop,
      0 ≤ C * Real.exp (A - 60 * H ^ 2) * (B + H) ^ 11 by
      filter_upwards [eventually_ge_atTop (max 1 B)] with H hH
      have hH0 : 0 ≤ H := zero_le_one.trans ((le_max_left 1 B).trans hH)
      exact mul_nonneg (mul_nonneg hC (Real.exp_pos _).le)
        (pow_nonneg (add_nonneg hB hH0) 11))
    (show ∀ᶠ H : ℝ in atTop,
      C * Real.exp (A - 60 * H ^ 2) * (B + H) ^ 11 ≤
        D * (H ^ 11 * Real.exp (-60 * H ^ 2)) by
      filter_upwards [eventually_ge_atTop (max 1 B)] with H hH
      have hH1 : 1 ≤ H := (le_max_left 1 B).trans hH
      have hHB : B ≤ H := (le_max_right 1 B).trans hH
      have hH0 : 0 ≤ H := zero_le_one.trans hH1
      have hshift : B + H ≤ 2 * H := by linarith
      have hpow : (B + H) ^ 11 ≤ 2048 * H ^ 11 := by
        calc
          (B + H) ^ 11 ≤ (2 * H) ^ 11 := by gcongr
          _ = 2048 * H ^ 11 := by ring
      have hexp : Real.exp (A - 60 * H ^ 2) =
          Real.exp A * Real.exp (-60 * H ^ 2) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [hexp]
      dsimp [D]
      calc
        C * (Real.exp A * Real.exp (-60 * H ^ 2)) * (B + H) ^ 11 ≤
            C * (Real.exp A * Real.exp (-60 * H ^ 2)) *
              (2048 * H ^ 11) := by gcongr
        _ = C * Real.exp A * 2048 *
              (H ^ 11 * Real.exp (-60 * H ^ 2)) := by ring)
  exact hmajor

private theorem tendsto_HIntegral_top_zero_of_central_horizontal_bound_eleven
    (f : ℂ → ℂ) (t δ : ℝ) (hδ1 : δ ≤ 1)
    (hbound : ∃ C : ℝ, 0 < C ∧ ∀ (y : ℝ),
      1 ≤ |y| → |t| + 1 ≤ |y| → ∀ x ∈ Set.Icc δ 1,
        ‖f ((x : ℂ) + (y : ℂ) * I)‖ ≤
          C * Real.exp (100 - 60 * y ^ 2) *
            (3 + |t| + |y|) ^ 11) :
    Tendsto (fun H : ℝ => HIntegral f δ 1 H) atTop (nhds 0) := by
  obtain ⟨C, hC, hCbound⟩ := hbound
  let envelope : ℝ → ℝ := fun H =>
    C * Real.exp (100 - 60 * H ^ 2) * (3 + |t| + H) ^ 11
  have henv : Tendsto envelope atTop (nhds 0) :=
    tendsto_const_mul_exp_sub_sixty_sq_mul_shift_pow_eleven
      C 100 (3 + |t|) hC.le (by positivity)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    (show ∀ᶠ H : ℝ in atTop,
      ‖HIntegral f δ 1 H‖ ≤ envelope H * |1 - δ| by
      filter_upwards [eventually_ge_atTop (max 1 (|t| + 1))] with H hH
      have hH1 : 1 ≤ H := (le_max_left _ _).trans hH
      have hHt : |t| + 1 ≤ H := (le_max_right _ _).trans hH
      have hH0 : 0 ≤ H := zero_le_one.trans hH1
      unfold HIntegral
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro x hx
      have hx' : x ∈ Set.Icc δ 1 := by
        rw [← uIcc_of_le hδ1]
        exact Set.uIoc_subset_uIcc hx
      have hpoint := hCbound H
        (by simpa [abs_of_nonneg hH0] using hH1)
        (by simpa [abs_of_nonneg hH0] using hHt) x hx'
      simpa [envelope, abs_of_nonneg hH0, add_assoc] using hpoint)
  simpa using henv.mul_const |1 - δ|

private theorem tendsto_HIntegral_bottom_zero_of_central_horizontal_bound_eleven
    (f : ℂ → ℂ) (t δ : ℝ) (hδ1 : δ ≤ 1)
    (hbound : ∃ C : ℝ, 0 < C ∧ ∀ (y : ℝ),
      1 ≤ |y| → |t| + 1 ≤ |y| → ∀ x ∈ Set.Icc δ 1,
        ‖f ((x : ℂ) + (y : ℂ) * I)‖ ≤
          C * Real.exp (100 - 60 * y ^ 2) *
            (3 + |t| + |y|) ^ 11) :
    Tendsto (fun H : ℝ => HIntegral f δ 1 (-H)) atTop (nhds 0) := by
  obtain ⟨C, hC, hCbound⟩ := hbound
  let envelope : ℝ → ℝ := fun H =>
    C * Real.exp (100 - 60 * H ^ 2) * (3 + |t| + H) ^ 11
  have henv : Tendsto envelope atTop (nhds 0) :=
    tendsto_const_mul_exp_sub_sixty_sq_mul_shift_pow_eleven
      C 100 (3 + |t|) hC.le (by positivity)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    (show ∀ᶠ H : ℝ in atTop,
      ‖HIntegral f δ 1 (-H)‖ ≤ envelope H * |1 - δ| by
      filter_upwards [eventually_ge_atTop (max 1 (|t| + 1))] with H hH
      have hH1 : 1 ≤ H := (le_max_left _ _).trans hH
      have hHt : |t| + 1 ≤ H := (le_max_right _ _).trans hH
      have hH0 : 0 ≤ H := zero_le_one.trans hH1
      unfold HIntegral
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro x hx
      have hx' : x ∈ Set.Icc δ 1 := by
        rw [← uIcc_of_le hδ1]
        exact Set.uIoc_subset_uIcc hx
      have hpoint := hCbound (-H)
        (by simpa [abs_of_nonneg hH0] using hH1)
        (by simpa [abs_of_nonneg hH0] using hHt) x hx'
      simpa [envelope, abs_of_nonneg hH0, add_assoc] using hpoint)
  simpa using henv.mul_const |1 - δ|

/-- Both horizontal edges in the moving-pole rectangle vanish. -/
theorem tendsto_hughesYoungCompletePositiveCentralMeromorphic_horizontal_edges
    (T t : ℝ) (h k a b : ℕ) {δ : ℝ} {z w : ℂ}
    (hδ0 : 0 < δ) (hδ4 : δ < 1 / 4)
    (hz : ‖z‖ ≤ δ / 4) (hw : ‖w‖ ≤ δ / 4) :
    Tendsto (fun H : ℝ => HIntegral
        (hughesYoungCompletePositiveCentralMeromorphic T t h k a b z w)
        δ 1 H) atTop (nhds 0) ∧
      Tendsto (fun H : ℝ => HIntegral
        (hughesYoungCompletePositiveCentralMeromorphic T t h k a b z w)
        δ 1 (-H)) atTop (nhds 0) := by
  have hbound :=
    exists_norm_hughesYoungCompletePositiveCentralMeromorphic_horizontal_le
      T t h k a b hδ0 hδ4 hz hw
  have hδ1 : δ ≤ 1 := hδ4.le.trans (by norm_num)
  exact ⟨
    tendsto_HIntegral_top_zero_of_central_horizontal_bound_eleven
      _ t δ hδ1 hbound,
    tendsto_HIntegral_bottom_zero_of_central_horizontal_bound_eleven
      _ t δ hδ1 hbound⟩

/-- Infinite-height contour displacement in limit form.  The auxiliary
shifts remain generic, and the only surviving term is the exact residue at
`W = (1+z+w)/2`. -/
theorem tendsto_hughesYoungCompletePositiveCentralMaster_verticalShift
    (T t : ℝ) (h k a b : ℕ) {δ : ℝ} {z w : ℂ}
    (hδ0 : 0 < δ) (hδ4 : δ < 1 / 4)
    (hz : ‖z‖ < δ / 4) (hw : ‖w‖ < δ / 4) :
    Tendsto (fun H : ℝ =>
      (((1 / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ u in (-H)..H,
            hughesYoungCompletePositiveCentralMeromorphic T t h k a b z w
              ((1 : ℂ) + (u : ℂ) * I)) -
        (((1 / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ u in (-H)..H,
            hughesYoungCompletePositiveCentralMeromorphic T t h k a b z w
              ((δ : ℂ) + (u : ℂ) * I)))
      atTop (nhds ((2 : ℂ)⁻¹ *
        hughesYoungCompletePositiveCentralPoleFree T t h k a b
          (hughesYoungCentralMovingPole z w) z w)) := by
  have hedges :=
    tendsto_hughesYoungCompletePositiveCentralMeromorphic_horizontal_edges
      T t h k a b hδ0 hδ4 hz.le hw.le
  have htop' : Tendsto (fun H : ℝ => HIntegral'
      (hughesYoungCompletePositiveCentralMeromorphic T t h k a b z w)
      δ 1 H) atTop (nhds 0) := by
    unfold HIntegral'
    simpa using (Tendsto.smul
      (tendsto_const_nhds
        (x := (1 / (2 * (Real.pi : ℂ) * I) : ℂ))) hedges.1)
  have hbottom' : Tendsto (fun H : ℝ => HIntegral'
      (hughesYoungCompletePositiveCentralMeromorphic T t h k a b z w)
      δ 1 (-H)) atTop (nhds 0) := by
    unfold HIntegral'
    simpa using (Tendsto.smul
      (tendsto_const_nhds
        (x := (1 / (2 * (Real.pi : ℂ) * I) : ℂ))) hedges.2)
  have hrhs : Tendsto (fun H : ℝ =>
      (2 : ℂ)⁻¹ *
          hughesYoungCompletePositiveCentralPoleFree T t h k a b
            (hughesYoungCentralMovingPole z w) z w -
        HIntegral'
          (hughesYoungCompletePositiveCentralMeromorphic T t h k a b z w)
          δ 1 (-H) +
        HIntegral'
          (hughesYoungCompletePositiveCentralMeromorphic T t h k a b z w)
          δ 1 H)
      atTop (nhds ((2 : ℂ)⁻¹ *
        hughesYoungCompletePositiveCentralPoleFree T t h k a b
          (hughesYoungCentralMovingPole z w) z w)) := by
    simpa using (tendsto_const_nhds.sub hbottom').add htop'
  apply hrhs.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with H hH
  exact (hughesYoungCompletePositiveCentralMaster_finiteVerticalShift
    T t h k a b hδ0 hδ4 hz hw hH).symm

theorem continuous_hughesYoungCompletePositiveCentralMeromorphic_vertical
    (T t : ℝ) (h k a b : ℕ) {δ c : ℝ} {z w : ℂ}
    (hδ0 : 0 < δ) (hδ4 : δ < 1 / 4)
    (hz : ‖z‖ ≤ δ / 4) (hw : ‖w‖ ≤ δ / 4)
    (hc : c = δ ∨ c = 1) :
    Continuous (fun u : ℝ =>
      hughesYoungCompletePositiveCentralMeromorphic T t h k a b z w
        ((c : ℂ) + (u : ℂ) * I)) := by
  apply continuous_iff_continuousAt.mpr
  intro u
  let W : ℂ := (c : ℂ) + (u : ℂ) * I
  have hzRe : |z.re| ≤ δ / 4 := (abs_re_le_norm z).trans hz
  have hwRe : |w.re| ≤ δ / 4 := (abs_re_le_norm w).trans hw
  have hc0 : 0 < c := by rcases hc with rfl | rfl <;> norm_num [hδ0]
  have hc3 : c < 3 / 2 := by
    rcases hc with rfl | rfl
    · linarith
    · norm_num
  have hsPole : 2 * W - z - w ≠ 1 := by
    intro heq
    have hre := congrArg Complex.re heq
    dsimp only [W] at hre
    norm_num [Complex.mul_re] at hre
    rcases hc with rfl | rfl
    · linarith [neg_le_abs z.re, neg_le_abs w.re]
    · linarith [le_abs_self z.re, le_abs_self w.re]
  have hzeta : 1 < (1 + 2 * W + z + w : ℂ).re := by
    dsimp only [W]
    norm_num [Complex.mul_re]
    rcases hc with rfl | rfl
    · linarith [neg_abs_le z.re, neg_abs_le w.re]
    · linarith [neg_abs_le z.re, neg_abs_le w.re]
  have hzetaDen : 1 ≤ (2 + 2 * z + 2 * w : ℂ).re := by
    norm_num [Complex.mul_re]
    linarith [neg_abs_le z.re, neg_abs_le w.re]
  have hregular : (-2 - 2 * z - 2 * w : ℂ).re < 0 := by
    norm_num [Complex.mul_re]
    linarith [neg_abs_le z.re, neg_abs_le w.re]
  have hleft : (z - w - 2 * W : ℂ).re < 0 := by
    dsimp only [W]
    norm_num [Complex.mul_re]
    rcases hc with rfl | rfl
    · linarith [le_abs_self z.re, neg_abs_le w.re]
    · linarith [le_abs_self z.re, neg_abs_le w.re]
  have hright : (w - z - 2 * W : ℂ).re < 0 := by
    dsimp only [W]
    norm_num [Complex.mul_re]
    rcases hc with rfl | rfl
    · linarith [le_abs_self w.re, neg_abs_le z.re]
    · linarith [le_abs_self w.re, neg_abs_le z.re]
  have houter : ContinuousAt
      (hughesYoungCompletePositiveCentralMeromorphic T t h k a b z w) W := by
    unfold hughesYoungCompletePositiveCentralMeromorphic
    exact (((differentiableAt_riemannZeta hsPole).comp W (by fun_prop)).mul
      (differentiableAt_hughesYoungCompletePositiveCentralPoleFree
        T t h k a b (by simpa [W] using hc0) (by simpa [W] using hc3)
          hzeta hzetaDen hregular hleft hright)).continuousAt
  have hinner : ContinuousAt (fun v : ℝ => (c : ℂ) + (v : ℂ) * I) u := by
    fun_prop
  simpa only [W, Function.comp_apply] using
    houter.comp (x := u) (f := fun v : ℝ => (c : ℂ) + (v : ℂ) * I) hinner

/-- Absolute integrability of both generic-shift vertical lines in the
residue rectangle. -/
theorem integrable_hughesYoungCompletePositiveCentralMeromorphic_vertical
    (T t : ℝ) (h k a b : ℕ) {δ c : ℝ} {z w : ℂ}
    (hδ0 : 0 < δ) (hδ4 : δ < 1 / 4)
    (hz : ‖z‖ ≤ δ / 4) (hw : ‖w‖ ≤ δ / 4)
    (hc : c = δ ∨ c = 1) :
    Integrable (fun u : ℝ =>
      hughesYoungCompletePositiveCentralMeromorphic T t h k a b z w
        ((c : ℂ) + (u : ℂ) * I)) := by
  obtain ⟨C, _hC, hbound⟩ :=
    exists_norm_hughesYoungCompletePositiveCentralMeromorphic_horizontal_le
      T t h k a b hδ0 hδ4 hz hw
  let L : ℝ := max 1 (|t| + 1)
  have hL : 0 < L := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  apply integrable_of_continuous_of_norm_le_gaussian_tail
    (fun u : ℝ =>
      hughesYoungCompletePositiveCentralMeromorphic T t h k a b z w
        ((c : ℂ) + (u : ℂ) * I))
    (continuous_hughesYoungCompletePositiveCentralMeromorphic_vertical
      T t h k a b hδ0 hδ4 hz hw hc)
    (C := C) (A := 100) (B := 60) (D := 3 + |t|) (j := 11)
    hL (by norm_num : (0 : ℝ) < 60)
  intro u hu
  have hu1 : 1 ≤ |u| := (le_max_left 1 (|t| + 1)).trans hu
  have hut : |t| + 1 ≤ |u| := (le_max_right 1 (|t| + 1)).trans hu
  have hcIcc : c ∈ Set.Icc δ 1 := by
    rcases hc with rfl | rfl
    · exact ⟨le_rfl, hδ4.le.trans (by norm_num)⟩
    · exact ⟨hδ4.le.trans (by norm_num), le_rfl⟩
  simpa only [add_assoc] using hbound u hu1 hut c hcIcc

/-- Exact whole-line contour shift across the moving pole. -/
theorem hughesYoungCompletePositiveCentralMaster_verticalIntegral_shift
    (T t : ℝ) (h k a b : ℕ) {δ : ℝ} {z w : ℂ}
    (hδ0 : 0 < δ) (hδ4 : δ < 1 / 4)
    (hz : ‖z‖ < δ / 4) (hw : ‖w‖ < δ / 4) :
    (((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ u : ℝ,
          hughesYoungCompletePositiveCentralMeromorphic T t h k a b z w
            ((1 : ℂ) + (u : ℂ) * I)) -
      (((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ u : ℝ,
          hughesYoungCompletePositiveCentralMeromorphic T t h k a b z w
            ((δ : ℂ) + (u : ℂ) * I)) =
      (2 : ℂ)⁻¹ *
        hughesYoungCompletePositiveCentralPoleFree T t h k a b
          (hughesYoungCentralMovingPole z w) z w := by
  have hright := MeasureTheory.intervalIntegral_tendsto_integral
    (integrable_hughesYoungCompletePositiveCentralMeromorphic_vertical
      T t h k a b hδ0 hδ4 hz.le hw.le (Or.inr rfl))
    tendsto_neg_atTop_atBot tendsto_id
  have hleft := MeasureTheory.intervalIntegral_tendsto_integral
    (integrable_hughesYoungCompletePositiveCentralMeromorphic_vertical
      T t h k a b hδ0 hδ4 hz.le hw.le (Or.inl rfl))
    tendsto_neg_atTop_atBot tendsto_id
  let c : ℂ := ((1 / (2 * Real.pi) : ℝ) : ℂ)
  have hwhole : Tendsto (fun H : ℝ =>
      c * (∫ u in (-H)..H,
          hughesYoungCompletePositiveCentralMeromorphic T t h k a b z w
            ((1 : ℂ) + (u : ℂ) * I)) -
        c * (∫ u in (-H)..H,
          hughesYoungCompletePositiveCentralMeromorphic T t h k a b z w
            ((δ : ℂ) + (u : ℂ) * I))) atTop
      (nhds (c * (∫ u : ℝ,
          hughesYoungCompletePositiveCentralMeromorphic T t h k a b z w
            ((1 : ℂ) + (u : ℂ) * I)) -
        c * (∫ u : ℝ,
          hughesYoungCompletePositiveCentralMeromorphic T t h k a b z w
            ((δ : ℂ) + (u : ℂ) * I)))) :=
    (tendsto_const_nhds.mul hright).sub (tendsto_const_nhds.mul hleft)
  have hres := tendsto_hughesYoungCompletePositiveCentralMaster_verticalShift
    T t h k a b hδ0 hδ4 hz hw
  exact tendsto_nhds_unique hwhole (by simpa only [c] using hres)

end RiemannZeta.GuthMaynard
