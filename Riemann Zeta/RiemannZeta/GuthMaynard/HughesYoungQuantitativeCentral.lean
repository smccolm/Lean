import RiemannZeta.GuthMaynard.HughesYoungCentralDifferentiation
import RiemannZeta.GuthMaynard.HughesYoungGlobalBounds
import RiemannZeta.GuthMaynard.HughesYoungSharpGammaRatio

open Complex Filter MeasureTheory Metric Set
open scoped BigOperators Topology

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# Quantitative central-source estimates

This file turns the cancellation-preserving Hughes--Young central contour
identity into bounds with constants uniform in the physical height.  The
first step records the exact real-power content of the reduced Mellin
factor; retaining this identity is what produces the summable
`gcd(h,k)/(hk)` weight at the moving pole.
-/

/-- Exact norm of the reduced Mellin factor after the DFI coprime
normalization.  The ordinate variables contribute only phases. -/
theorem norm_inv_reduced_mul_hughesYoungReducedMellinStaticComplex_eq
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (T t c u : ℝ) :
    ‖((((hughesYoungReducedLeft h k : ℕ) : ℂ) *
          (hughesYoungReducedRight h k : ℕ))⁻¹ *
        hughesYoungReducedMellinStaticComplex T t h k
          ((c : ℂ) + (u : ℂ) * I))‖ =
      ‖hughesYoungLocalizedStaticScalar T h k‖ *
        (hughesYoungReducedLeft h k : ℝ) ^ (c - 1 / 2) *
        (hughesYoungReducedRight h k : ℝ) ^ (c - 1 / 2) := by
  have ha : 0 < hughesYoungReducedLeft h k :=
    hughesYoungReducedLeft_pos hh
  have hb : 0 < hughesYoungReducedRight h k :=
    hughesYoungReducedRight_pos hh hk
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have haR : (0 : ℝ) < hughesYoungReducedLeft h k := by exact_mod_cast ha
  have hbR : (0 : ℝ) < hughesYoungReducedRight h k := by exact_mod_cast hb
  have hExpA :
      ‖Complex.exp
          ((afeCriticalPoint t + ((c : ℂ) + (u : ℂ) * I)) *
            (Real.log (hughesYoungReducedLeft h k : ℝ) : ℂ))‖ =
        (hughesYoungReducedLeft h k : ℝ) ^ (1 / 2 + c) := by
    have hReA :
        (((afeCriticalPoint t + ((c : ℂ) + (u : ℂ) * I)) *
          (Real.log (hughesYoungReducedLeft h k : ℝ) : ℂ)).re) =
            (1 / 2 + c) * Real.log (hughesYoungReducedLeft h k : ℝ) := by
      simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im]
      simp [afeCriticalPoint]
    rw [Complex.norm_exp]
    rw [hReA]
    rw [Real.rpow_def_of_pos haR]
    congr 1
    ring
  have hExpB :
      ‖Complex.exp
          ((afeCriticalPoint (-t) + ((c : ℂ) + (u : ℂ) * I)) *
            (Real.log (hughesYoungReducedRight h k : ℝ) : ℂ))‖ =
        (hughesYoungReducedRight h k : ℝ) ^ (1 / 2 + c) := by
    have hReB :
        (((afeCriticalPoint (-t) + ((c : ℂ) + (u : ℂ) * I)) *
          (Real.log (hughesYoungReducedRight h k : ℝ) : ℂ)).re) =
            (1 / 2 + c) * Real.log (hughesYoungReducedRight h k : ℝ) := by
      simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im]
      simp [afeCriticalPoint]
    rw [Complex.norm_exp]
    rw [hReB]
    rw [Real.rpow_def_of_pos hbR]
    congr 1
    ring
  have hPowH :
      ‖((h : ℂ) ^ (-afeCriticalPoint t))‖ =
        (h : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [← Complex.ofReal_natCast,
      norm_cpow_eq_rpow_re_of_pos hhR]
    simp [afeCriticalPoint]
  have hPowK :
      ‖((k : ℂ) ^ (-afeCriticalPoint (-t)))‖ =
        (k : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [← Complex.ofReal_natCast,
      norm_cpow_eq_rpow_re_of_pos hkR]
    simp [afeCriticalPoint]
  have hAcombine :
      (hughesYoungReducedLeft h k : ℝ)⁻¹ *
          (hughesYoungReducedLeft h k : ℝ) ^ (1 / 2 + c) =
        (hughesYoungReducedLeft h k : ℝ) ^ (c - 1 / 2) := by
    rw [← Real.rpow_neg_one (hughesYoungReducedLeft h k : ℝ),
      ← Real.rpow_add haR]
    congr 1
    ring
  have hBcombine :
      (hughesYoungReducedRight h k : ℝ)⁻¹ *
          (hughesYoungReducedRight h k : ℝ) ^ (1 / 2 + c) =
        (hughesYoungReducedRight h k : ℝ) ^ (c - 1 / 2) := by
    rw [← Real.rpow_neg_one (hughesYoungReducedRight h k : ℝ),
      ← Real.rpow_add hbR]
    congr 1
    ring
  unfold hughesYoungReducedMellinStaticComplex
  dsimp only
  rw [norm_mul, norm_inv, norm_mul, Complex.norm_natCast, Complex.norm_natCast,
    norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, norm_mul,
    hPowH, hPowK, hExpA, hExpB]
  simp only [norm_div, norm_one, norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos]
  rw [norm_hughesYoungLocalizedStaticScalar_eq_coefficients_mul_rpow hh hk]
  rw [mul_inv_rev]
  rw [← hAcombine, ← hBcombine]
  ring

/-- Abel's formula uniformly controls zeta to the right of its pole when
the real part stays a prescribed positive distance from one. -/
theorem norm_riemannZeta_le_two_mul_inv_mul_norm_of_one_add_le_re
    {δ : ℝ} (hδ : 0 < δ) {s : ℂ} (hs : 1 + δ ≤ s.re) :
    ‖riemannZeta s‖ ≤ 2 * δ⁻¹ * ‖s‖ := by
  have hs0 : 0 < s.re := by linarith
  have hs1 : s ≠ 1 := by
    intro heq
    subst s
    norm_num at hs
    linarith
  have hden : δ ≤ ‖s - 1‖ := by
    calc
      δ ≤ (s - 1).re := by
        simp only [sub_re, one_re]
        linarith
      _ ≤ |(s - 1).re| := le_abs_self _
      _ ≤ ‖s - 1‖ := abs_re_le_norm _
  have hrem : ‖abelZetaRemainder s‖ ≤ δ⁻¹ := by
    calc
      _ ≤ 1 / s.re := norm_abelZetaRemainder_le hs0
      _ ≤ 1 / δ := one_div_le_one_div_of_le hδ (by linarith)
      _ = δ⁻¹ := one_div _
  rw [riemannZeta_eq_abel hs0 hs1]
  calc
    ‖s / (s - 1) - s * abelZetaRemainder s‖ ≤
        ‖s / (s - 1)‖ + ‖s * abelZetaRemainder s‖ := norm_sub_le _ _
    _ = ‖s‖ / ‖s - 1‖ + ‖s‖ * ‖abelZetaRemainder s‖ := by
      rw [norm_div, norm_mul]
    _ ≤ ‖s‖ / δ + ‖s‖ * δ⁻¹ := by
      gcongr
    _ = 2 * δ⁻¹ * ‖s‖ := by
      rw [div_eq_mul_inv]
      ring

/-- On the low-contour moving-zeta strip, the point stays uniformly left
of the pole and a positive distance right of the imaginary axis. -/
theorem norm_riemannZeta_le_four_mul_inv_mul_norm_of_low_strip
    {δ : ℝ} (hδ : 0 < δ) (hδ4 : δ < 1 / 4) {s : ℂ}
    (hsLow : 3 * δ / 2 ≤ s.re) (hsHigh : s.re ≤ 5 * δ / 2) :
    ‖riemannZeta s‖ ≤ 4 * δ⁻¹ * ‖s‖ := by
  have hs0 : 0 < s.re := hδ.trans_le (by nlinarith)
  have hsGap : s.re ≤ 5 / 8 := by nlinarith
  have hs1 : s ≠ 1 := by
    intro heq
    subst s
    norm_num at hsGap
  have hden : (3 / 8 : ℝ) ≤ ‖s - 1‖ := by
    calc
      (3 / 8 : ℝ) ≤ 1 - s.re := by linarith
      _ = |(s - 1).re| := by
        rw [abs_of_nonpos]
        · simp
        · simp only [sub_re, one_re]
          linarith
      _ ≤ ‖s - 1‖ := abs_re_le_norm _
  have hrem : ‖abelZetaRemainder s‖ ≤ (2 / (3 * δ)) := by
    calc
      _ ≤ 1 / s.re := norm_abelZetaRemainder_le hs0
      _ ≤ 1 / (3 * δ / 2) :=
        one_div_le_one_div_of_le (by positivity) hsLow
      _ = 2 / (3 * δ) := by field_simp
  have hδ1 : δ ≤ 1 := hδ4.le.trans (by norm_num)
  have hfront : (8 / 3 : ℝ) + 2 / (3 * δ) ≤ 4 * δ⁻¹ := by
    have hδinv : 1 ≤ δ⁻¹ := (one_le_inv₀ hδ).mpr hδ1
    have hfrac : 2 / (3 * δ) = (2 / 3 : ℝ) * δ⁻¹ := by
      field_simp
    rw [hfrac]
    nlinarith
  rw [riemannZeta_eq_abel hs0 hs1]
  calc
    ‖s / (s - 1) - s * abelZetaRemainder s‖ ≤
        ‖s / (s - 1)‖ + ‖s * abelZetaRemainder s‖ := norm_sub_le _ _
    _ = ‖s‖ / ‖s - 1‖ + ‖s‖ * ‖abelZetaRemainder s‖ := by
      rw [norm_div, norm_mul]
    _ ≤ ‖s‖ / (3 / 8) + ‖s‖ * (2 / (3 * δ)) := by
      gcongr
    _ = ((8 / 3 : ℝ) + 2 / (3 * δ)) * ‖s‖ := by ring
    _ ≤ 4 * δ⁻¹ * ‖s‖ := mul_le_mul_of_nonneg_right hfront (norm_nonneg s)

/-- Every distinct prime divisor contributes at least a factor two to the
divisor-count product. -/
theorem two_pow_card_primeFactors_le_card_divisors
    {n : ℕ} (hn : 0 < n) :
    ((2 : ℝ) ^ n.primeFactors.card) ≤ (n.divisors.card : ℝ) := by
  have hnat : 2 ^ n.primeFactors.card ≤ n.divisors.card := by
    rw [Nat.card_divisors hn.ne']
    calc
      2 ^ n.primeFactors.card = ∏ _p ∈ n.primeFactors, 2 := by simp
      _ ≤ ∏ p ∈ n.primeFactors, (n.factorization p + 1) := by
        apply Finset.prod_le_prod
        · intro p hp
          omega
        · intro p hp
          have hpData := Nat.mem_primeFactors.mp hp
          have hfac : 0 < n.factorization p :=
            hpData.1.factorization_pos_of_dvd hn.ne' hpData.2.1
          omega
  exact_mod_cast hnat

/-- A fixed positive local Euler-factor bound raised to the number of
prime divisors is `n^ε`, with a constant depending only on the fixed bound
and `ε`. -/
theorem exists_pow_card_primeFactors_le_const_mul_rpow
    {A ε : ℝ} (hA : 0 < A) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {n : ℕ}, 0 < n →
      A ^ n.primeFactors.card ≤ C * (n : ℝ) ^ ε := by
  obtain ⟨m, hm⟩ := exists_nat_gt A
  have hm0 : 0 < m := by
    by_contra hm0
    have : m = 0 := Nat.eq_zero_of_not_pos hm0
    subst m
    norm_num at hm
    linarith
  have hmTwoNat : m ≤ 2 ^ m := by
    simpa using Nat.choose_le_two_pow m 1
  have hA2 : A ≤ ((2 : ℝ) ^ m) := by
    calc
      A ≤ (m : ℝ) := hm.le
      _ ≤ ((2 : ℕ) ^ m : ℕ) := by exact_mod_cast hmTwoNat
      _ = (2 : ℝ) ^ m := by norm_num
  let η : ℝ := ε / m
  have hη : 0 < η := by
    dsimp only [η]
    positivity
  let C : ℝ := (divisorEpsilonConstant η) ^ m
  have hC : 0 < C := by
    dsimp only [C]
    exact pow_pos (divisorEpsilonConstant_pos η) m
  refine ⟨C, hC, ?_⟩
  intro n hn
  have htwo := two_pow_card_primeFactors_le_card_divisors hn
  have hdiv := card_divisors_le_const_mul_rpow hη hn.ne'
  have hpowA : A ^ n.primeFactors.card ≤
      (((2 : ℝ) ^ m) ^ n.primeFactors.card) := by
    exact pow_le_pow_left₀ hA.le hA2 _
  have hreorder : (((2 : ℝ) ^ m) ^ n.primeFactors.card) =
      (((2 : ℝ) ^ n.primeFactors.card) ^ m) := by
    rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  have hdivpow : (((2 : ℝ) ^ n.primeFactors.card) ^ m) ≤
      ((n.divisors.card : ℝ) ^ m) :=
    pow_le_pow_left₀ (by positivity) htwo m
  have hboundpow : ((n.divisors.card : ℝ) ^ m) ≤
      (divisorEpsilonConstant η * (n : ℝ) ^ η) ^ m :=
    pow_le_pow_left₀ (by positivity) hdiv m
  calc
    A ^ n.primeFactors.card ≤
        (((2 : ℝ) ^ m) ^ n.primeFactors.card) := hpowA
    _ = (((2 : ℝ) ^ n.primeFactors.card) ^ m) := hreorder
    _ ≤ ((n.divisors.card : ℝ) ^ m) := hdivpow
    _ ≤ (divisorEpsilonConstant η * (n : ℝ) ^ η) ^ m := hboundpow
    _ = C * (n : ℝ) ^ ε := by
      rw [mul_pow]
      have hnR : (0 : ℝ) ≤ n := by positivity
      have heta : ((n : ℝ) ^ η) ^ m = (n : ℝ) ^ ε := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hnR]
        congr 1
        dsimp only [η]
        field_simp
      rw [heta]

/-- The finite equation-(100) Euler correction on an arbitrarily low
positive contour has the required arbitrary epsilon growth, uniformly in
the contour ordinate and in the auxiliary bidisc. -/
theorem exists_norm_hughesYoungC_centralStrip_le_const_mul_rpow
    {δ ε : ℝ} (hδ0 : 0 < δ) (hδ4 : δ < 1 / 4) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {n : ℕ}, 0 < n → ∀ {x y : ℝ} {z w : ℂ},
      δ ≤ x → ‖z‖ ≤ δ / 4 → ‖w‖ ≤ δ / 4 →
      ‖hughesYoungC n (-z) z (-w) w ((x : ℂ) + (y : ℂ) * I)‖ ≤
        C * (n : ℝ) ^ ε := by
  let A : ℝ := max 1 (hughesYoungCentralLocalFactorBound δ)
  have hA : 0 < A := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  obtain ⟨C, hC, hpow⟩ :=
    exists_pow_card_primeFactors_le_const_mul_rpow hA hε
  refine ⟨C, hC, ?_⟩
  intro n hn x y z w hx hz hw
  have hlocal := norm_hughesYoungC_centralStrip_le
    n (y := y) hδ0 hδ4 hx hz hw
  have hcard : (hughesYoungPrimeFactors n).card = n.primeFactors.card := by
    simp [hughesYoungPrimeFactors]
  rw [hcard] at hlocal
  exact hlocal.trans (hpow hn)

/-! ## A height-uniform beta-integral bound on the low contour -/

/-- On a fixed low positive contour, the complete affine two-logarithm beta
kernel is bounded independently of both vertical ordinates.  This is the
quantitative form of the source beta-integral argument: after taking norms,
the imaginary parts of the two exponents disappear exactly. -/
theorem exists_norm_hughesYoungAffineLogBetaContinuation_critical_le
    {c : ℝ} (hc : 0 < c) (hcHalf : c < 1 / 2) :
    ∃ B : ℝ, 0 < B ∧ ∀ (t u : ℝ) (CX COne : ℂ),
      ‖hughesYoungAffineLogBetaContinuation
          (-(afeCriticalPoint (-t) + ((c : ℂ) + (u : ℂ) * I)))
          (-(afeCriticalPoint t + ((c : ℂ) + (u : ℂ) * I)))
          CX COne‖ ≤ B * (1 + ‖CX‖ + ‖COne‖) ^ 2 := by
  let A₀ : ℂ := -((1 / 2 + c : ℝ) : ℂ)
  let B₀ : ℂ := -((1 / 2 + c : ℝ) : ℂ)
  let f₀ : ℝ → ℂ := fun x =>
    (x : ℂ) ^ A₀ * (1 + (x : ℂ)) ^ B₀
  let fX : ℝ → ℂ := fun x => (Real.log x : ℂ) * f₀ x
  let fOne : ℝ → ℂ := fun x => (Real.log (1 + x) : ℂ) * f₀ x
  let fMix : ℝ → ℂ := fun x =>
    (Real.log x : ℂ) * (Real.log (1 + x) : ℂ) * f₀ x
  let g : ℝ → ℝ := fun x =>
    ‖fMix x‖ + ‖fX x‖ + ‖fOne x‖ + ‖f₀ x‖
  have hA₀ : 0 < (A₀ + 1).re := by
    dsimp only [A₀]
    simp only [neg_re, ofReal_re, add_re, one_re]
    linarith
  have hAB₀ : (A₀ + B₀ + 1).re < 0 := by
    dsimp only [A₀, B₀]
    simp only [neg_re, ofReal_re, add_re, one_re]
    linarith
  have hf₀ : IntegrableOn f₀ (Set.Ioi 0) := by
    simpa only [f₀] using integrableOn_hughesYoungBeta hA₀ hAB₀
  have hfX : IntegrableOn fX (Set.Ioi 0) := by
    simpa only [fX, f₀] using
      integrableOn_hughesYoungLogXBeta hA₀ hAB₀
  have hfOne : IntegrableOn fOne (Set.Ioi 0) := by
    simpa only [fOne, f₀] using
      integrableOn_hughesYoungLogOneAddBeta hA₀ hAB₀
  have hfMix : IntegrableOn fMix (Set.Ioi 0) := by
    simpa only [fMix, f₀] using
      integrableOn_hughesYoungMixedLogBeta hA₀ hAB₀
  have hg : IntegrableOn g (Set.Ioi 0) := by
    exact ((hfMix.norm.add hfX.norm).add hfOne.norm).add hf₀.norm
  have hgNonneg : ∀ x, 0 ≤ g x := by
    intro x
    dsimp only [g]
    positivity
  let B : ℝ := 1 + ∫ x in Set.Ioi (0 : ℝ), g x
  have hIntegralNonneg : 0 ≤ ∫ x in Set.Ioi (0 : ℝ), g x :=
    integral_nonneg hgNonneg
  have hB : 0 < B := by
    dsimp only [B]
    linarith
  refine ⟨B, hB, ?_⟩
  intro t u CX COne
  let w : ℂ := (c : ℂ) + (u : ℂ) * I
  let A : ℂ := -(afeCriticalPoint (-t) + w)
  let D : ℂ := -(afeCriticalPoint t + w)
  have hstrip := hughesYoungEquation83_exponents_in_betaStrip
    t u hc hcHalf
  have hA : 0 < (A + 1).re := by
    simpa only [A, w] using hstrip.1
  have hAD : (A + D + 1).re < 0 := by
    simpa only [A, D, w] using hstrip.2
  rw [← hughesYoungAffineLogBetaIntegral_eq_continuation hA hAD]
  let S : ℝ := 1 + ‖CX‖ + ‖COne‖
  have hS : 1 ≤ S := by
    dsimp only [S]
    linarith [norm_nonneg CX, norm_nonneg COne]
  have hS₀ : 0 ≤ S := zero_le_one.trans hS
  have hSsq : 1 ≤ S ^ 2 := by nlinarith [sq_nonneg S]
  have hCX : ‖CX‖ ≤ S ^ 2 := by
    have : ‖CX‖ ≤ S := by
      dsimp only [S]
      linarith [norm_nonneg COne]
    exact this.trans (by nlinarith)
  have hCOne : ‖COne‖ ≤ S ^ 2 := by
    have : ‖COne‖ ≤ S := by
      dsimp only [S]
      linarith [norm_nonneg CX]
    exact this.trans (by nlinarith)
  have hProd : ‖CX‖ * ‖COne‖ ≤ S ^ 2 := by
    have hCX' : ‖CX‖ ≤ S := by
      dsimp only [S]
      linarith [norm_nonneg COne]
    have hCOne' : ‖COne‖ ≤ S := by
      dsimp only [S]
      linarith [norm_nonneg CX]
    simpa only [pow_two] using
      mul_le_mul hCX' hCOne' (norm_nonneg COne) hS₀
  have hpoint : ∀ᵐ x ∂volume.restrict (Set.Ioi (0 : ℝ)),
      ‖((Real.log x : ℂ) + CX) *
          ((Real.log (1 + x) : ℂ) + COne) *
          ((x : ℂ) ^ A * (1 + (x : ℂ)) ^ D)‖ ≤
        S ^ 2 * g x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx₀ : 0 < x := hx
    have hone₀ : 0 < 1 + x := by linarith
    have hone : 1 + (x : ℂ) = ((1 + x : ℝ) : ℂ) := by
      push_cast
      rfl
    have hAre : A.re = A₀.re := by
      dsimp only [A, A₀, w, afeCriticalPoint]
      simp
    have hDre : D.re = B₀.re := by
      dsimp only [D, B₀, w, afeCriticalPoint]
      simp
    have hpowX : ‖(x : ℂ) ^ A‖ = ‖(x : ℂ) ^ A₀‖ := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx₀,
        Complex.norm_cpow_eq_rpow_re_of_pos hx₀, hAre]
    have hpowOne : ‖(1 + (x : ℂ)) ^ D‖ =
        ‖(1 + (x : ℂ)) ^ B₀‖ := by
      rw [hone, Complex.norm_cpow_eq_rpow_re_of_pos hone₀,
        Complex.norm_cpow_eq_rpow_re_of_pos hone₀, hDre]
    have hbase :
        ‖(x : ℂ) ^ A * (1 + (x : ℂ)) ^ D‖ = ‖f₀ x‖ := by
      simp only [norm_mul, f₀, hpowX, hpowOne]
    have hlogX :
        ‖(Real.log x : ℂ) + CX‖ ≤
          ‖(Real.log x : ℂ)‖ + ‖CX‖ := norm_add_le _ _
    have hlogOne :
        ‖(Real.log (1 + x) : ℂ) + COne‖ ≤
          ‖(Real.log (1 + x) : ℂ)‖ + ‖COne‖ := norm_add_le _ _
    rw [norm_mul, norm_mul, hbase]
    calc
      ‖(Real.log x : ℂ) + CX‖ *
            ‖(Real.log (1 + x) : ℂ) + COne‖ * ‖f₀ x‖ ≤
          (‖(Real.log x : ℂ)‖ + ‖CX‖) *
            (‖(Real.log (1 + x) : ℂ)‖ + ‖COne‖) * ‖f₀ x‖ := by
              gcongr
      _ = ‖fMix x‖ + ‖COne‖ * ‖fX x‖ +
            ‖CX‖ * ‖fOne x‖ + ‖CX‖ * ‖COne‖ * ‖f₀ x‖ := by
          simp only [fMix, fX, fOne, norm_mul]
          ring
      _ ≤ S ^ 2 * ‖fMix x‖ + S ^ 2 * ‖fX x‖ +
            S ^ 2 * ‖fOne x‖ + S ^ 2 * ‖f₀ x‖ := by
          apply add_le_add
          · apply add_le_add
            · apply add_le_add
              · simpa only [one_mul] using
                  mul_le_mul_of_nonneg_right hSsq (norm_nonneg (fMix x))
              · exact mul_le_mul_of_nonneg_right hCOne (norm_nonneg (fX x))
            · exact mul_le_mul_of_nonneg_right hCX (norm_nonneg (fOne x))
          · exact mul_le_mul_of_nonneg_right hProd (norm_nonneg (f₀ x))
      _ = S ^ 2 * g x := by
          dsimp only [g]
          ring
  have hScaledIntegrable : IntegrableOn (fun x => S ^ 2 * g x) (Set.Ioi 0) :=
    hg.const_mul (S ^ 2)
  have hnorm := norm_integral_le_of_norm_le hScaledIntegrable hpoint
  rw [MeasureTheory.integral_const_mul] at hnorm
  calc
    _ ≤ S ^ 2 * (∫ x in Set.Ioi (0 : ℝ), g x) := hnorm
    _ ≤ B * S ^ 2 := by
      dsimp only [B]
      nlinarith [sq_nonneg S]
    _ = B * (1 + ‖CX‖ + ‖COne‖) ^ 2 := by rfl

/-- The source equation-(84) beta kernel therefore has the same uniform
low-contour bound.  This theorem is stated for the literal critical beta
kernel so it composes directly with the opened AFE contour weight. -/
theorem exists_norm_hughesYoungEquation84CriticalBetaKernel_low_le
    {c : ℝ} (hc : 0 < c) (hcHalf : c < 1 / 2) :
    ∃ B : ℝ, 0 < B ∧ ∀ (t u : ℝ) (CX COne : ℂ),
      ‖hughesYoungEquation84CriticalBetaKernel t
          ((c : ℂ) + (u : ℂ) * I) CX COne‖ ≤
        B * (1 + ‖CX‖ + ‖COne‖) ^ 2 := by
  obtain ⟨B, hB, hbound⟩ :=
    exists_norm_hughesYoungAffineLogBetaContinuation_critical_le hc hcHalf
  refine ⟨B, hB, ?_⟩
  intro t u CX COne
  let w : ℂ := (c : ℂ) + (u : ℂ) * I
  have hLeft : 0 < (afeCriticalPoint t - w).re := by
    dsimp only [w, afeCriticalPoint]
    simp
    linarith
  have hW : 0 < w.re := by simp [w, hc]
  have heq := hughesYoungAffineLogBetaContinuation_critical_eq_explicit
    (t := t) (w := w) (CX := CX) (COne := COne) hLeft hW
  have hbound' := hbound t u CX COne
  change ‖hughesYoungAffineLogBetaContinuation
      (-(afeCriticalPoint (-t) + w))
      (-(afeCriticalPoint t + w)) CX COne‖ ≤
        B * (1 + ‖CX‖ + ‖COne‖) ^ 2 at hbound'
  rw [heq] at hbound'
  simpa only [w, hughesYoungEquation84CriticalBetaKernel] using
    hbound'

/-- The low-contour height-power estimate is even in the physical ordinate.
The source weight is invariant under `t ↦ -t`, so the natural quantitative
interface is the dyadic condition on `|t|`. -/
theorem exists_norm_hughesYoungRightContourWeight_shift_le_abs_height_power :
    ∃ C : ℝ, 0 < C ∧ ∀ (T t u c : ℝ), 1 ≤ T →
      |t| ∈ Set.Icc (T / 4) (4 * T) → 0 < c → c ≤ 1 →
      ‖hughesYoungRightContourWeight t c u‖ ≤
        c⁻¹ * T ^ (4 * C * c) *
          (Real.exp
            (100 * c ^ 2 - 84 * u ^ 2 +
              4 * C * c * Real.log (6 * (|u| + 1))) *
            (25 + 8 * u ^ 2) ^ 8) := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_norm_hughesYoungRightContourWeight_shift_le_height_power
  refine ⟨C, hC, ?_⟩
  intro T t u c hT ht hc hc1
  by_cases ht0 : 0 ≤ t
  · exact hbound T t u c hT (by simpa [abs_of_nonneg ht0] using ht) hc hc1
  · have htneg : t < 0 := lt_of_not_ge ht0
    have hraw := hbound T (-t) u c hT
      (by simpa [abs_of_neg htneg] using ht) hc hc1
    have heq : hughesYoungRightContourWeight t c u =
        hughesYoungRightContourWeight (-t) c u := by
      rw [← hughesYoungRightContourWeightComplex_vertical,
        hughesYoungRightContourWeightComplex_neg,
        hughesYoungRightContourWeightComplex_vertical]
    rw [heq]
    exact hraw

/-- The complete regularized equation-(84) kernel inherits the low-contour
height power and Gaussian ordinate decay from the opened AFE weight, with no
additional dependence on the physical height from the beta integral. -/
theorem exists_norm_hughesYoungEquation84RegularizedContourKernel_low_le_of_heightConstant
    (C : ℝ)
    (hweight : ∀ (T t u c : ℝ), 1 ≤ T →
      |t| ∈ Set.Icc (T / 4) (4 * T) → 0 < c → c ≤ 1 →
      ‖hughesYoungRightContourWeight t c u‖ ≤
        c⁻¹ * T ^ (4 * C * c) *
          (Real.exp
            (100 * c ^ 2 - 84 * u ^ 2 +
              4 * C * c * Real.log (6 * (|u| + 1))) *
            (25 + 8 * u ^ 2) ^ 8))
    {c : ℝ} (hc : 0 < c) (hcHalf : c < 1 / 2) :
    ∃ B : ℝ, 0 < B ∧ ∀ (T t u : ℝ), 1 ≤ T →
      |t| ∈ Set.Icc (T / 4) (4 * T) → ∀ (CX COne : ℂ),
      ‖hughesYoungEquation84RegularizedContourKernel t
          ((c : ℂ) + (u : ℂ) * I) CX COne‖ ≤
        B * (1 + ‖CX‖ + ‖COne‖) ^ 2 *
          (c⁻¹ * T ^ (4 * C * c) *
            (Real.exp
              (100 * c ^ 2 - 84 * u ^ 2 +
                4 * C * c * Real.log (6 * (|u| + 1))) *
              (25 + 8 * u ^ 2) ^ 8)) := by
  obtain ⟨B, hB, hbeta⟩ :=
    exists_norm_hughesYoungEquation84CriticalBetaKernel_low_le hc hcHalf
  refine ⟨B, hB, ?_⟩
  intro T t u hT ht CX COne
  let w : ℂ := (c : ℂ) + (u : ℂ) * I
  have hc1 : c ≤ 1 := by linarith
  have hz : 0 < (afeCriticalPoint t - w).re := by
    dsimp only [w, afeCriticalPoint]
    simp
    linarith
  have hproduct :=
    hughesYoungRightContourWeightComplex_mul_equation84_eq_regularized
      (t := t) (w := w) (CX := CX) (COne := COne) hz
  rw [← hproduct, norm_mul,
    hughesYoungRightContourWeightComplex_vertical]
  have hw := hweight T t u c hT ht hc hc1
  have hb := hbeta t u CX COne
  exact (mul_le_mul hw hb (norm_nonneg _) (by positivity)).trans_eq (by ring)

theorem exists_norm_hughesYoungEquation84RegularizedContourKernel_low_le
    {c : ℝ} (hc : 0 < c) (hcHalf : c < 1 / 2) :
    ∃ C B : ℝ, 0 < C ∧ 0 < B ∧ ∀ (T t u : ℝ), 1 ≤ T →
      |t| ∈ Set.Icc (T / 4) (4 * T) → ∀ (CX COne : ℂ),
      ‖hughesYoungEquation84RegularizedContourKernel t
          ((c : ℂ) + (u : ℂ) * I) CX COne‖ ≤
        B * (1 + ‖CX‖ + ‖COne‖) ^ 2 *
          (c⁻¹ * T ^ (4 * C * c) *
            (Real.exp
              (100 * c ^ 2 - 84 * u ^ 2 +
                4 * C * c * Real.log (6 * (|u| + 1))) *
              (25 + 8 * u ^ 2) ^ 8)) := by
  obtain ⟨C, hC, hweight⟩ :=
    exists_norm_hughesYoungRightContourWeight_shift_le_abs_height_power
  obtain ⟨B, hB, hbound⟩ :=
    exists_norm_hughesYoungEquation84RegularizedContourKernel_low_le_of_heightConstant
      C hweight hc hcHalf
  exact ⟨C, B, hC, hB, hbound⟩

/-- All four affine finite-difference coefficients of equation (84) share
one height-uniform low-contour envelope.  This is the quantitative kernel
input used by the reverse-polynomial auxiliary function. -/
theorem exists_norm_hughesYoungEquation84KernelCoefficients_low_le_of_heightConstant
    (C : ℝ)
    (hweight : ∀ (T t u c : ℝ), 1 ≤ T →
      |t| ∈ Set.Icc (T / 4) (4 * T) → 0 < c → c ≤ 1 →
      ‖hughesYoungRightContourWeight t c u‖ ≤
        c⁻¹ * T ^ (4 * C * c) *
          (Real.exp
            (100 * c ^ 2 - 84 * u ^ 2 +
              4 * C * c * Real.log (6 * (|u| + 1))) *
            (25 + 8 * u ^ 2) ^ 8))
    {c : ℝ} (hc : 0 < c) (hcHalf : c < 1 / 2) :
    ∃ B : ℝ, 0 < B ∧ ∀ (T t u : ℝ), 1 ≤ T →
      |t| ∈ Set.Icc (T / 4) (4 * T) →
      let E := c⁻¹ * T ^ (4 * C * c) *
        (Real.exp
          (100 * c ^ 2 - 84 * u ^ 2 +
            4 * C * c * Real.log (6 * (|u| + 1))) *
          (25 + 8 * u ^ 2) ^ 8)
      ‖hughesYoungEquation84Kernel00 t ((c : ℂ) + (u : ℂ) * I)‖ ≤ B * E ∧
      ‖hughesYoungEquation84Kernel10 t ((c : ℂ) + (u : ℂ) * I)‖ ≤ B * E ∧
      ‖hughesYoungEquation84Kernel01 t ((c : ℂ) + (u : ℂ) * I)‖ ≤ B * E ∧
      ‖hughesYoungEquation84Kernel11 t ((c : ℂ) + (u : ℂ) * I)‖ ≤ B * E := by
  obtain ⟨B₀, hB₀, hkernel⟩ :=
    exists_norm_hughesYoungEquation84RegularizedContourKernel_low_le_of_heightConstant
      C hweight hc hcHalf
  let B : ℝ := 36 * B₀
  have hB : 0 < B := by dsimp only [B]; positivity
  refine ⟨B, hB, ?_⟩
  intro T t u hT ht
  let w : ℂ := (c : ℂ) + (u : ℂ) * I
  let E : ℝ := c⁻¹ * T ^ (4 * C * c) *
    (Real.exp
      (100 * c ^ 2 - 84 * u ^ 2 +
        4 * C * c * Real.log (6 * (|u| + 1))) *
      (25 + 8 * u ^ 2) ^ 8)
  have hE : 0 ≤ E := by
    dsimp only [E]
    positivity
  have h₀₀ :
      ‖hughesYoungEquation84RegularizedContourKernel t w 0 0‖ ≤ B₀ * E := by
    have h := hkernel T t u hT ht (0 : ℂ) (0 : ℂ)
    simpa only [w, E, norm_zero, add_zero, one_pow, mul_one] using h
  have h₁₀ :
      ‖hughesYoungEquation84RegularizedContourKernel t w 1 0‖ ≤ 4 * B₀ * E := by
    have h := hkernel T t u hT ht (1 : ℂ) (0 : ℂ)
    norm_num at h ⊢
    change ‖hughesYoungEquation84RegularizedContourKernel t w 1 0‖ ≤
      B₀ * 4 * E at h
    exact h.trans_eq (by ring)
  have h₀₁ :
      ‖hughesYoungEquation84RegularizedContourKernel t w 0 1‖ ≤ 4 * B₀ * E := by
    have h := hkernel T t u hT ht (0 : ℂ) (1 : ℂ)
    norm_num at h ⊢
    change ‖hughesYoungEquation84RegularizedContourKernel t w 0 1‖ ≤
      B₀ * 4 * E at h
    exact h.trans_eq (by ring)
  have h₁₁ :
      ‖hughesYoungEquation84RegularizedContourKernel t w 1 1‖ ≤ 9 * B₀ * E := by
    have h := hkernel T t u hT ht (1 : ℂ) (1 : ℂ)
    norm_num at h ⊢
    change ‖hughesYoungEquation84RegularizedContourKernel t w 1 1‖ ≤
      B₀ * 9 * E at h
    exact h.trans_eq (by ring)
  dsimp only
  constructor
  · change ‖hughesYoungEquation84RegularizedContourKernel t w 0 0‖ ≤ B * E
    exact h₀₀.trans (mul_le_mul_of_nonneg_right (by dsimp only [B]; linarith) hE)
  constructor
  · change ‖hughesYoungEquation84RegularizedContourKernel t w 1 0 -
        hughesYoungEquation84RegularizedContourKernel t w 0 0‖ ≤ B * E
    calc
      _ ≤ ‖hughesYoungEquation84RegularizedContourKernel t w 1 0‖ +
          ‖hughesYoungEquation84RegularizedContourKernel t w 0 0‖ := norm_sub_le _ _
      _ ≤ (4 * B₀ + B₀) * E := by
        calc
          _ ≤ 4 * B₀ * E + B₀ * E := add_le_add h₁₀ h₀₀
          _ = _ := by ring
      _ ≤ B * E := mul_le_mul_of_nonneg_right (by dsimp only [B]; linarith) hE
  constructor
  · change ‖hughesYoungEquation84RegularizedContourKernel t w 0 1 -
        hughesYoungEquation84RegularizedContourKernel t w 0 0‖ ≤ B * E
    calc
      _ ≤ ‖hughesYoungEquation84RegularizedContourKernel t w 0 1‖ +
          ‖hughesYoungEquation84RegularizedContourKernel t w 0 0‖ := norm_sub_le _ _
      _ ≤ (4 * B₀ + B₀) * E := by
        calc
          _ ≤ 4 * B₀ * E + B₀ * E := add_le_add h₀₁ h₀₀
          _ = _ := by ring
      _ ≤ B * E := mul_le_mul_of_nonneg_right (by dsimp only [B]; linarith) hE
  · change ‖hughesYoungEquation84RegularizedContourKernel t w 1 1 -
        (hughesYoungEquation84RegularizedContourKernel t w 1 0 -
          hughesYoungEquation84RegularizedContourKernel t w 0 0) -
        (hughesYoungEquation84RegularizedContourKernel t w 0 1 -
          hughesYoungEquation84RegularizedContourKernel t w 0 0) -
        hughesYoungEquation84RegularizedContourKernel t w 0 0‖ ≤ B * E
    rw [show
      hughesYoungEquation84RegularizedContourKernel t w 1 1 -
          (hughesYoungEquation84RegularizedContourKernel t w 1 0 -
            hughesYoungEquation84RegularizedContourKernel t w 0 0) -
          (hughesYoungEquation84RegularizedContourKernel t w 0 1 -
            hughesYoungEquation84RegularizedContourKernel t w 0 0) -
          hughesYoungEquation84RegularizedContourKernel t w 0 0 =
        (hughesYoungEquation84RegularizedContourKernel t w 1 1 -
            hughesYoungEquation84RegularizedContourKernel t w 1 0 -
            hughesYoungEquation84RegularizedContourKernel t w 0 1) +
          hughesYoungEquation84RegularizedContourKernel t w 0 0 by ring]
    calc
      _ ≤ ‖hughesYoungEquation84RegularizedContourKernel t w 1 1 -
              hughesYoungEquation84RegularizedContourKernel t w 1 0 -
              hughesYoungEquation84RegularizedContourKernel t w 0 1‖ +
            ‖hughesYoungEquation84RegularizedContourKernel t w 0 0‖ :=
          norm_add_le _ _
      _ ≤ (‖hughesYoungEquation84RegularizedContourKernel t w 1 1 -
              hughesYoungEquation84RegularizedContourKernel t w 1 0‖ +
            ‖hughesYoungEquation84RegularizedContourKernel t w 0 1‖) +
            ‖hughesYoungEquation84RegularizedContourKernel t w 0 0‖ := by
          gcongr
          exact norm_sub_le _ _
      _ ≤ ((‖hughesYoungEquation84RegularizedContourKernel t w 1 1‖ +
              ‖hughesYoungEquation84RegularizedContourKernel t w 1 0‖) +
            ‖hughesYoungEquation84RegularizedContourKernel t w 0 1‖) +
            ‖hughesYoungEquation84RegularizedContourKernel t w 0 0‖ := by
          gcongr
          exact norm_sub_le _ _
      _ ≤ (9 * B₀ + 4 * B₀ + 4 * B₀ + B₀) * E := by
        calc
          _ ≤ (9 * B₀ * E + 4 * B₀ * E) + 4 * B₀ * E + B₀ * E := by
              gcongr
          _ = _ := by ring
      _ ≤ B * E := mul_le_mul_of_nonneg_right (by dsimp only [B]; linarith) hE

theorem exists_norm_hughesYoungEquation84KernelCoefficients_low_le
    {c : ℝ} (hc : 0 < c) (hcHalf : c < 1 / 2) :
    ∃ C B : ℝ, 0 < C ∧ 0 < B ∧ ∀ (T t u : ℝ), 1 ≤ T →
      |t| ∈ Set.Icc (T / 4) (4 * T) →
      let E := c⁻¹ * T ^ (4 * C * c) *
        (Real.exp
          (100 * c ^ 2 - 84 * u ^ 2 +
            4 * C * c * Real.log (6 * (|u| + 1))) *
          (25 + 8 * u ^ 2) ^ 8)
      ‖hughesYoungEquation84Kernel00 t ((c : ℂ) + (u : ℂ) * I)‖ ≤ B * E ∧
      ‖hughesYoungEquation84Kernel10 t ((c : ℂ) + (u : ℂ) * I)‖ ≤ B * E ∧
      ‖hughesYoungEquation84Kernel01 t ((c : ℂ) + (u : ℂ) * I)‖ ≤ B * E ∧
      ‖hughesYoungEquation84Kernel11 t ((c : ℂ) + (u : ℂ) * I)‖ ≤ B * E := by
  obtain ⟨C, hC, hweight⟩ :=
    exists_norm_hughesYoungRightContourWeight_shift_le_abs_height_power
  obtain ⟨B, hB, hbound⟩ :=
    exists_norm_hughesYoungEquation84KernelCoefficients_low_le_of_heightConstant
      C hweight hc hcHalf
  exact ⟨C, B, hC, hB, hbound⟩

/-- The reversed equation-(84) polynomial is uniformly controlled on the
auxiliary bidisc whose radius is proportional to the low contour. -/
theorem exists_norm_hughesYoungCentralReverseKernelPolynomial_low_le_of_heightConstant
    (C : ℝ)
    (hweight : ∀ (T t u c : ℝ), 1 ≤ T →
      |t| ∈ Set.Icc (T / 4) (4 * T) → 0 < c → c ≤ 1 →
      ‖hughesYoungRightContourWeight t c u‖ ≤
        c⁻¹ * T ^ (4 * C * c) *
          (Real.exp
            (100 * c ^ 2 - 84 * u ^ 2 +
              4 * C * c * Real.log (6 * (|u| + 1))) *
            (25 + 8 * u ^ 2) ^ 8))
    {c : ℝ} (hc : 0 < c) (hcHalf : c < 1 / 2) :
    ∃ B : ℝ, 0 < B ∧ ∀ (T t u : ℝ), 1 ≤ T →
      |t| ∈ Set.Icc (T / 4) (4 * T) → ∀ {z w : ℂ},
      ‖z‖ ≤ c / 4 → ‖w‖ ≤ c / 4 →
      ‖hughesYoungCentralReverseKernelPolynomial t
          ((c : ℂ) + (u : ℂ) * I) z w‖ ≤
        B * (c⁻¹ * T ^ (4 * C * c) *
          (Real.exp
            (100 * c ^ 2 - 84 * u ^ 2 +
              4 * C * c * Real.log (6 * (|u| + 1))) *
            (25 + 8 * u ^ 2) ^ 8)) := by
  obtain ⟨B₀, hB₀, hcoeff⟩ :=
    exists_norm_hughesYoungEquation84KernelCoefficients_low_le_of_heightConstant
      C hweight hc hcHalf
  let B : ℝ := 4 * B₀
  have hB : 0 < B := by dsimp only [B]; positivity
  refine ⟨B, hB, ?_⟩
  intro T t u hT ht z w hz hw
  let W : ℂ := (c : ℂ) + (u : ℂ) * I
  let E : ℝ := c⁻¹ * T ^ (4 * C * c) *
    (Real.exp
      (100 * c ^ 2 - 84 * u ^ 2 +
        4 * C * c * Real.log (6 * (|u| + 1))) *
      (25 + 8 * u ^ 2) ^ 8)
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hc4 : c / 4 ≤ 1 := by linarith
  have hz1 : ‖z‖ ≤ 1 := hz.trans hc4
  have hw1 : ‖w‖ ≤ 1 := hw.trans hc4
  have hzw1 : ‖z‖ * ‖w‖ ≤ 1 := by nlinarith [norm_nonneg z, norm_nonneg w]
  obtain ⟨h00, h10, h01, h11⟩ := hcoeff T t u hT ht
  change ‖hughesYoungEquation84Kernel00 t W‖ ≤ B₀ * E at h00
  change ‖hughesYoungEquation84Kernel10 t W‖ ≤ B₀ * E at h10
  change ‖hughesYoungEquation84Kernel01 t W‖ ≤ B₀ * E at h01
  change ‖hughesYoungEquation84Kernel11 t W‖ ≤ B₀ * E at h11
  have hzTerm : ‖z‖ * ‖hughesYoungEquation84Kernel10 t W‖ ≤ B₀ * E := by
    calc
      _ ≤ 1 * (B₀ * E) := mul_le_mul hz1 h10 (norm_nonneg _) zero_le_one
      _ = _ := one_mul _
  have hwTerm : ‖w‖ * ‖hughesYoungEquation84Kernel01 t W‖ ≤ B₀ * E := by
    calc
      _ ≤ 1 * (B₀ * E) := mul_le_mul hw1 h01 (norm_nonneg _) zero_le_one
      _ = _ := one_mul _
  have hzwTerm :
      (‖z‖ * ‖w‖) * ‖hughesYoungEquation84Kernel00 t W‖ ≤ B₀ * E := by
    calc
      _ ≤ 1 * (B₀ * E) := mul_le_mul hzw1 h00 (norm_nonneg _) zero_le_one
      _ = _ := one_mul _
  change ‖hughesYoungCentralReverseKernelPolynomial t W z w‖ ≤ B * E
  unfold hughesYoungCentralReverseKernelPolynomial
  calc
    _ ≤ ‖hughesYoungEquation84Kernel11 t W‖ +
          ‖z * hughesYoungEquation84Kernel10 t W‖ +
          ‖w * hughesYoungEquation84Kernel01 t W‖ +
          ‖z * w * hughesYoungEquation84Kernel00 t W‖ := by
        calc
          _ ≤ ‖hughesYoungEquation84Kernel11 t W +
                z * hughesYoungEquation84Kernel10 t W +
                w * hughesYoungEquation84Kernel01 t W‖ +
              ‖z * w * hughesYoungEquation84Kernel00 t W‖ := norm_add_le _ _
          _ ≤ (‖hughesYoungEquation84Kernel11 t W +
                z * hughesYoungEquation84Kernel10 t W‖ +
              ‖w * hughesYoungEquation84Kernel01 t W‖) +
              ‖z * w * hughesYoungEquation84Kernel00 t W‖ := by
                gcongr
                exact norm_add_le _ _
          _ ≤ ((‖hughesYoungEquation84Kernel11 t W‖ +
                ‖z * hughesYoungEquation84Kernel10 t W‖) +
              ‖w * hughesYoungEquation84Kernel01 t W‖) +
              ‖z * w * hughesYoungEquation84Kernel00 t W‖ := by
                gcongr
                exact norm_add_le _ _
    _ = ‖hughesYoungEquation84Kernel11 t W‖ +
          ‖z‖ * ‖hughesYoungEquation84Kernel10 t W‖ +
          ‖w‖ * ‖hughesYoungEquation84Kernel01 t W‖ +
          (‖z‖ * ‖w‖) * ‖hughesYoungEquation84Kernel00 t W‖ := by
        simp only [norm_mul]
    _ ≤ B₀ * E + B₀ * E + B₀ * E + B₀ * E := by
        exact add_le_add (add_le_add (add_le_add h11 hzTerm) hwTerm) hzwTerm
    _ = B * E := by dsimp only [B]; ring

/-- The pole-free equation-(96) jet has only one inverse-contour loss and
one polynomial factor in the Mellin ordinate on the low contour. -/
theorem exists_norm_hughesYoungEquation96PoleFreeMasterJet_low_le
    {c ε : ℝ} (hc : 0 < c) (hc4 : c < 1 / 4) (hε : 0 < ε) :
    ∃ A : ℝ, 0 < A ∧ ∀ {a b : ℕ}, 0 < a → 0 < b → ∀ (u : ℝ) {z w : ℂ},
      ‖z‖ ≤ c / 4 → ‖w‖ ≤ c / 4 →
      ‖hughesYoungEquation96PoleFreeMasterJet a b
          ((c : ℂ) + (u : ℂ) * I) z w‖ ≤
        A * c⁻¹ * (1 + |u|) *
          (((a : ℝ) ^ (c / 4) * (a : ℝ) ^ ε) *
            ((b : ℝ) ^ (c / 4) * (b : ℝ) ^ ε)) := by
  obtain ⟨Ce, hCe, hCbound⟩ :=
    exists_norm_hughesYoungC_centralStrip_le_const_mul_rpow hc hc4 hε
  let D : ℝ := max 1 hughesYoungZetaHalfPlaneMajorant
  let A : ℝ := 4 * Real.exp (c * |Real.eulerMascheroniConstant|) * D * Ce ^ 2
  have hD : 0 < D := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hA : 0 < A := by dsimp only [A]; positivity
  refine ⟨A, hA, ?_⟩
  intro a b ha hb u z w hz hw
  let W : ℂ := (c : ℂ) + (u : ℂ) * I
  let s₂ : ℂ := 1 + 2 * W + z + w
  let s₃ : ℂ := 2 + 2 * z + 2 * w
  have hWnorm : ‖W‖ ≤ c + |u| := by
    calc
      ‖W‖ ≤ |W.re| + |W.im| := Complex.norm_le_abs_re_add_abs_im W
      _ = c + |u| := by simp [W, abs_of_pos hc]
  have hzRe : |z.re| ≤ c / 4 := (abs_re_le_norm z).trans hz
  have hwRe : |w.re| ≤ c / 4 := (abs_re_le_norm w).trans hw
  have hs₂Re : 1 + 3 * c / 2 ≤ s₂.re := by
    dsimp only [s₂, W]
    norm_num [Complex.mul_re]
    linarith [neg_abs_le z.re, neg_abs_le w.re]
  have hs₂Norm : ‖s₂‖ ≤ 2 * (1 + |u|) := by
    have htri : ‖s₂‖ ≤ 1 + 2 * ‖W‖ + ‖z‖ + ‖w‖ := by
      dsimp only [s₂]
      calc
        ‖1 + 2 * W + z + w‖ ≤ ‖1 + 2 * W + z‖ + ‖w‖ := norm_add_le _ _
        _ ≤ (‖1 + 2 * W‖ + ‖z‖) + ‖w‖ := by
          gcongr
          exact norm_add_le _ _
        _ ≤ (‖(1 : ℂ)‖ + ‖2 * W‖ + ‖z‖) + ‖w‖ := by
          gcongr
          exact norm_add_le _ _
        _ = 1 + 2 * ‖W‖ + ‖z‖ + ‖w‖ := by norm_num
    nlinarith [abs_nonneg u]
  have hzeta₂ : ‖riemannZeta s₂‖ ≤ 4 * c⁻¹ * (1 + |u|) := by
    have hzeta := norm_riemannZeta_le_two_mul_inv_mul_norm_of_one_add_le_re
      (show 0 < 3 * c / 2 by positivity) hs₂Re
    calc
      _ ≤ 2 * (3 * c / 2)⁻¹ * ‖s₂‖ := hzeta
      _ ≤ 2 * (3 * c / 2)⁻¹ * (2 * (1 + |u|)) := by gcongr
      _ ≤ 4 * c⁻¹ * (1 + |u|) := by
        have hcInv : 0 ≤ c⁻¹ := inv_nonneg.mpr hc.le
        have hu : 0 ≤ 1 + |u| := by positivity
        field_simp [hc.ne']
        nlinarith
  have hs₃Re : (3 / 2 : ℝ) ≤ s₃.re := by
    dsimp only [s₃]
    norm_num [Complex.mul_re]
    linarith [neg_abs_le z.re, neg_abs_le w.re]
  have hzeta₃ : ‖(riemannZeta s₃)⁻¹‖ ≤ D :=
    (norm_riemannZeta_inv_le_hughesYoungZetaHalfPlaneMajorant hs₃Re).trans
      (le_max_right _ _)
  have hCa : ‖hughesYoungC a (-z) z (-w) w W‖ ≤ Ce * (a : ℝ) ^ ε := by
    simpa only [W] using hCbound ha le_rfl hz hw
  have hCb : ‖hughesYoungC b (-w) w (-z) z W‖ ≤ Ce * (b : ℝ) ^ ε := by
    simpa only [W, add_comm] using hCbound hb le_rfl hw hz
  have hExp : ‖Complex.exp
      (z * hughesYoungEquation96LeftConstant a +
        w * hughesYoungEquation96RightConstant b)‖ ≤
      Real.exp (c * |Real.eulerMascheroniConstant|) *
        (a : ℝ) ^ (c / 4) * (b : ℝ) ^ (c / 4) := by
    simpa only [show 4 * (c / 4) = c by ring] using
      norm_hughesYoungEquation96JetExponential_le ha hb
        (show 0 ≤ c / 4 by positivity) hz hw
  unfold hughesYoungEquation96PoleFreeMasterJet
  rw [div_eq_mul_inv]
  simp only [norm_mul]
  change ‖Complex.exp
      (z * hughesYoungEquation96LeftConstant a +
        w * hughesYoungEquation96RightConstant b)‖ *
      ((‖riemannZeta s₂‖ * ‖(riemannZeta s₃)⁻¹‖) *
        (‖hughesYoungC a (-z) z (-w) w W‖ *
          ‖hughesYoungC b (-w) w (-z) z W‖)) ≤ _
  calc
    _ ≤ (Real.exp (c * |Real.eulerMascheroniConstant|) *
          (a : ℝ) ^ (c / 4) * (b : ℝ) ^ (c / 4)) *
        (((4 * c⁻¹ * (1 + |u|)) * D) *
          ((Ce * (a : ℝ) ^ ε) * (Ce * (b : ℝ) ^ ε))) := by gcongr
    _ = A * c⁻¹ * (1 + |u|) *
          (((a : ℝ) ^ (c / 4) * (a : ℝ) ^ ε) *
            ((b : ℝ) ^ (c / 4) * (b : ℝ) ^ ε)) := by
      dsimp only [A]
      ring

theorem exists_norm_hughesYoungCentralReverseKernelPolynomial_low_le
    {c : ℝ} (hc : 0 < c) (hcHalf : c < 1 / 2) :
    ∃ C B : ℝ, 0 < C ∧ 0 < B ∧ ∀ (T t u : ℝ), 1 ≤ T →
      |t| ∈ Set.Icc (T / 4) (4 * T) → ∀ {z w : ℂ},
      ‖z‖ ≤ c / 4 → ‖w‖ ≤ c / 4 →
      ‖hughesYoungCentralReverseKernelPolynomial t
          ((c : ℂ) + (u : ℂ) * I) z w‖ ≤
        B * (c⁻¹ * T ^ (4 * C * c) *
          (Real.exp
            (100 * c ^ 2 - 84 * u ^ 2 +
              4 * C * c * Real.log (6 * (|u| + 1))) *
            (25 + 8 * u ^ 2) ^ 8)) := by
  obtain ⟨C, hC, hweight⟩ :=
    exists_norm_hughesYoungRightContourWeight_shift_le_abs_height_power
  obtain ⟨B, hB, hbound⟩ :=
    exists_norm_hughesYoungCentralReverseKernelPolynomial_low_le_of_heightConstant
      C hweight hc hcHalf
  exact ⟨C, B, hC, hB, hbound⟩

/-- Complete pointwise low-contour bound for the cancellation-preserving
meromorphic central integrand, specialized to the actual reduced coprime
parameters coming from the mollifier indices. -/
theorem exists_norm_hughesYoungCompletePositiveCentralMeromorphic_low_le_of_heightConstant
    (C : ℝ)
    (hweight : ∀ (T t u c : ℝ), 1 ≤ T →
      |t| ∈ Set.Icc (T / 4) (4 * T) → 0 < c → c ≤ 1 →
      ‖hughesYoungRightContourWeight t c u‖ ≤
        c⁻¹ * T ^ (4 * C * c) *
          (Real.exp
            (100 * c ^ 2 - 84 * u ^ 2 +
              4 * C * c * Real.log (6 * (|u| + 1))) *
            (25 + 8 * u ^ 2) ^ 8))
    {c ε : ℝ} (hc : 0 < c) (hc4 : c < 1 / 4) (hε : 0 < ε) :
    ∃ A : ℝ, 0 < A ∧ ∀ (T t u : ℝ), 1 ≤ T →
      |t| ∈ Set.Icc (T / 4) (4 * T) → ∀ {h k : ℕ}, 0 < h → 0 < k →
      ∀ {z w : ℂ}, ‖z‖ ≤ c / 4 → ‖w‖ ≤ c / 4 →
      let a := hughesYoungReducedLeft h k
      let b := hughesYoungReducedRight h k
      ‖hughesYoungCompletePositiveCentralMeromorphic
          T t h k a b z w ((c : ℂ) + (u : ℂ) * I)‖ ≤
        A * ‖hughesYoungLocalizedStaticScalar T h k‖ *
          ((a : ℝ) ^ (c - 1 / 2) * (b : ℝ) ^ (c - 1 / 2)) *
          (((a : ℝ) ^ (c / 4) * (a : ℝ) ^ ε) *
            ((b : ℝ) ^ (c / 4) * (b : ℝ) ^ ε)) *
          (c⁻¹ ^ 3 * T ^ (4 * C * c) * (1 + |u|) ^ 2 *
            (Real.exp
              (100 * c ^ 2 - 84 * u ^ 2 +
                4 * C * c * Real.log (6 * (|u| + 1))) *
              (25 + 8 * u ^ 2) ^ 8)) := by
  obtain ⟨B, hB, hkernel⟩ :=
    exists_norm_hughesYoungCentralReverseKernelPolynomial_low_le_of_heightConstant
      C hweight hc (hc4.trans (by norm_num))
  obtain ⟨J, hJ, hjet⟩ :=
    exists_norm_hughesYoungEquation96PoleFreeMasterJet_low_le hc hc4 hε
  let A : ℝ := 12 * J * B
  have hA : 0 < A := by dsimp only [A]; positivity
  refine ⟨A, hA, ?_⟩
  intro T t u hT ht h k hh hk z w hz hw
  let a : ℕ := hughesYoungReducedLeft h k
  let b : ℕ := hughesYoungReducedRight h k
  let W : ℂ := (c : ℂ) + (u : ℂ) * I
  let s₁ : ℂ := 2 * W - z - w
  have ha : 0 < a := hughesYoungReducedLeft_pos hh
  have hb : 0 < b := hughesYoungReducedRight_pos hh hk
  have hWnorm : ‖W‖ ≤ c + |u| := by
    calc
      ‖W‖ ≤ |W.re| + |W.im| := Complex.norm_le_abs_re_add_abs_im W
      _ = c + |u| := by simp [W, abs_of_pos hc]
  have hzRe : |z.re| ≤ c / 4 := (abs_re_le_norm z).trans hz
  have hwRe : |w.re| ≤ c / 4 := (abs_re_le_norm w).trans hw
  have hs₁Low : 3 * c / 2 ≤ s₁.re := by
    dsimp only [s₁, W]
    norm_num [Complex.mul_re]
    linarith [le_abs_self z.re, le_abs_self w.re]
  have hs₁High : s₁.re ≤ 5 * c / 2 := by
    dsimp only [s₁, W]
    norm_num [Complex.mul_re]
    linarith [neg_abs_le z.re, neg_abs_le w.re]
  have hs₁Norm : ‖s₁‖ ≤ 3 * (1 + |u|) := by
    have htri : ‖s₁‖ ≤ 2 * ‖W‖ + ‖z‖ + ‖w‖ := by
      dsimp only [s₁]
      calc
        ‖2 * W - z - w‖ ≤ ‖2 * W - z‖ + ‖w‖ := norm_sub_le _ _
        _ ≤ (‖2 * W‖ + ‖z‖) + ‖w‖ := by
          gcongr
          exact norm_sub_le _ _
        _ = 2 * ‖W‖ + ‖z‖ + ‖w‖ := by norm_num
    nlinarith [abs_nonneg u]
  have hzeta₁ : ‖riemannZeta s₁‖ ≤ 12 * c⁻¹ * (1 + |u|) := by
    have hzeta := norm_riemannZeta_le_four_mul_inv_mul_norm_of_low_strip
      hc hc4 hs₁Low hs₁High
    calc
      _ ≤ 4 * c⁻¹ * ‖s₁‖ := hzeta
      _ ≤ 4 * c⁻¹ * (3 * (1 + |u|)) := by gcongr
      _ = 12 * c⁻¹ * (1 + |u|) := by ring
  have hstatic :
      ‖(((a : ℂ) * b)⁻¹ *
          hughesYoungReducedMellinStaticComplex T t h k W)‖ =
        ‖hughesYoungLocalizedStaticScalar T h k‖ *
          (a : ℝ) ^ (c - 1 / 2) * (b : ℝ) ^ (c - 1 / 2) := by
    simpa only [a, b, W, mul_assoc] using
      norm_inv_reduced_mul_hughesYoungReducedMellinStaticComplex_eq
        hh hk T t c u
  have hstaticSplit :
      ‖((a : ℂ) * b)⁻¹‖ *
          ‖hughesYoungReducedMellinStaticComplex T t h k W‖ =
        ‖hughesYoungLocalizedStaticScalar T h k‖ *
          (a : ℝ) ^ (c - 1 / 2) * (b : ℝ) ^ (c - 1 / 2) := by
    rw [← norm_mul]
    exact hstatic
  have hjet' :
      ‖hughesYoungEquation96PoleFreeMasterJet a b W z w‖ ≤
        J * c⁻¹ * (1 + |u|) *
          (((a : ℝ) ^ (c / 4) * (a : ℝ) ^ ε) *
            ((b : ℝ) ^ (c / 4) * (b : ℝ) ^ ε)) := by
    simpa only [W] using hjet ha hb u hz hw
  have hkernel' :
      ‖hughesYoungCentralReverseKernelPolynomial t W z w‖ ≤
        B * (c⁻¹ * T ^ (4 * C * c) *
          (Real.exp
            (100 * c ^ 2 - 84 * u ^ 2 +
              4 * C * c * Real.log (6 * (|u| + 1))) *
            (25 + 8 * u ^ 2) ^ 8)) := by
    simpa only [W] using hkernel T t u hT ht hz hw
  dsimp only
  unfold hughesYoungCompletePositiveCentralMeromorphic
    hughesYoungCompletePositiveCentralPoleFree
  simp only [norm_mul]
  change ‖riemannZeta s₁‖ *
      ((‖((a : ℂ) * b)⁻¹‖ *
          ‖hughesYoungReducedMellinStaticComplex T t h k W‖) *
        (‖hughesYoungEquation96PoleFreeMasterJet a b W z w‖ *
          ‖hughesYoungCentralReverseKernelPolynomial t W z w‖)) ≤ _
  rw [hstaticSplit]
  calc
    _ ≤ (12 * c⁻¹ * (1 + |u|)) *
        ((‖hughesYoungLocalizedStaticScalar T h k‖ *
            (a : ℝ) ^ (c - 1 / 2) * (b : ℝ) ^ (c - 1 / 2)) *
          ((J * c⁻¹ * (1 + |u|) *
              (((a : ℝ) ^ (c / 4) * (a : ℝ) ^ ε) *
                ((b : ℝ) ^ (c / 4) * (b : ℝ) ^ ε))) *
            (B * (c⁻¹ * T ^ (4 * C * c) *
              (Real.exp
                (100 * c ^ 2 - 84 * u ^ 2 +
                  4 * C * c * Real.log (6 * (|u| + 1))) *
                (25 + 8 * u ^ 2) ^ 8))))) := by gcongr
    _ = A * ‖hughesYoungLocalizedStaticScalar T h k‖ *
          ((a : ℝ) ^ (c - 1 / 2) * (b : ℝ) ^ (c - 1 / 2)) *
          (((a : ℝ) ^ (c / 4) * (a : ℝ) ^ ε) *
            ((b : ℝ) ^ (c / 4) * (b : ℝ) ^ ε)) *
          (c⁻¹ ^ 3 * T ^ (4 * C * c) * (1 + |u|) ^ 2 *
            (Real.exp
              (100 * c ^ 2 - 84 * u ^ 2 +
                4 * C * c * Real.log (6 * (|u| + 1))) *
              (25 + 8 * u ^ 2) ^ 8)) := by
      dsimp only [A]
      ring

theorem exists_norm_hughesYoungCompletePositiveCentralMeromorphic_low_le
    {c ε : ℝ} (hc : 0 < c) (hc4 : c < 1 / 4) (hε : 0 < ε) :
    ∃ C A : ℝ, 0 < C ∧ 0 < A ∧ ∀ (T t u : ℝ), 1 ≤ T →
      |t| ∈ Set.Icc (T / 4) (4 * T) → ∀ {h k : ℕ}, 0 < h → 0 < k →
      ∀ {z w : ℂ}, ‖z‖ ≤ c / 4 → ‖w‖ ≤ c / 4 →
      let a := hughesYoungReducedLeft h k
      let b := hughesYoungReducedRight h k
      ‖hughesYoungCompletePositiveCentralMeromorphic
          T t h k a b z w ((c : ℂ) + (u : ℂ) * I)‖ ≤
        A * ‖hughesYoungLocalizedStaticScalar T h k‖ *
          ((a : ℝ) ^ (c - 1 / 2) * (b : ℝ) ^ (c - 1 / 2)) *
          (((a : ℝ) ^ (c / 4) * (a : ℝ) ^ ε) *
            ((b : ℝ) ^ (c / 4) * (b : ℝ) ^ ε)) *
          (c⁻¹ ^ 3 * T ^ (4 * C * c) * (1 + |u|) ^ 2 *
            (Real.exp
              (100 * c ^ 2 - 84 * u ^ 2 +
                4 * C * c * Real.log (6 * (|u| + 1))) *
              (25 + 8 * u ^ 2) ^ 8)) := by
  obtain ⟨C, hC, hweight⟩ :=
    exists_norm_hughesYoungRightContourWeight_shift_le_abs_height_power
  obtain ⟨A, hA, hbound⟩ :=
    exists_norm_hughesYoungCompletePositiveCentralMeromorphic_low_le_of_heightConstant
      C hweight hc hc4 hε
  exact ⟨C, A, hC, hA, hbound⟩

/-- Cauchy's inequalities convert the complete bidisc bound into the exact
mixed auxiliary derivative occurring after the Hughes--Young contour shift. -/
theorem exists_norm_mixedDeriv_hughesYoungCompletePositiveCentralMeromorphic_low_le_of_heightConstant
    (C : ℝ)
    (hweight : ∀ (T t u c : ℝ), 1 ≤ T →
      |t| ∈ Set.Icc (T / 4) (4 * T) → 0 < c → c ≤ 1 →
      ‖hughesYoungRightContourWeight t c u‖ ≤
        c⁻¹ * T ^ (4 * C * c) *
          (Real.exp
            (100 * c ^ 2 - 84 * u ^ 2 +
              4 * C * c * Real.log (6 * (|u| + 1))) *
            (25 + 8 * u ^ 2) ^ 8))
    {c ε : ℝ} (hc : 0 < c) (hc4 : c < 1 / 4) (hε : 0 < ε) :
    ∃ A : ℝ, 0 < A ∧ ∀ (T t u : ℝ), 1 ≤ T →
      |t| ∈ Set.Icc (T / 4) (4 * T) → ∀ {h k : ℕ}, 0 < h → 0 < k →
      let a := hughesYoungReducedLeft h k
      let b := hughesYoungReducedRight h k
      ‖deriv (fun w => deriv (fun z =>
          hughesYoungCompletePositiveCentralMeromorphic
            T t h k a b z w ((c : ℂ) + (u : ℂ) * I)) 0) 0‖ ≤
        A * ‖hughesYoungLocalizedStaticScalar T h k‖ *
          ((a : ℝ) ^ (c - 1 / 2) * (b : ℝ) ^ (c - 1 / 2)) *
          (((a : ℝ) ^ (c / 4) * (a : ℝ) ^ ε) *
            ((b : ℝ) ^ (c / 4) * (b : ℝ) ^ ε)) *
          (c⁻¹ ^ 5 * T ^ (4 * C * c) * (1 + |u|) ^ 2 *
            (Real.exp
              (100 * c ^ 2 - 84 * u ^ 2 +
                4 * C * c * Real.log (6 * (|u| + 1))) *
              (25 + 8 * u ^ 2) ^ 8)) := by
  obtain ⟨A₀, hA₀, hpoint⟩ :=
    exists_norm_hughesYoungCompletePositiveCentralMeromorphic_low_le_of_heightConstant
      C hweight hc hc4 hε
  let A : ℝ := 128 * A₀
  have hA : 0 < A := by dsimp only [A]; positivity
  refine ⟨A, hA, ?_⟩
  intro T t u hT ht h k hh hk
  let a : ℕ := hughesYoungReducedLeft h k
  let b : ℕ := hughesYoungReducedRight h k
  let W : ℂ := (c : ℂ) + (u : ℂ) * I
  let R : ℝ := c / 4
  let H : ℝ := A₀ * ‖hughesYoungLocalizedStaticScalar T h k‖ *
    ((a : ℝ) ^ (c - 1 / 2) * (b : ℝ) ^ (c - 1 / 2)) *
    (((a : ℝ) ^ (c / 4) * (a : ℝ) ^ ε) *
      ((b : ℝ) ^ (c / 4) * (b : ℝ) ^ ε)) *
    (c⁻¹ ^ 3 * T ^ (4 * C * c) * (1 + |u|) ^ 2 *
      (Real.exp
        (100 * c ^ 2 - 84 * u ^ 2 +
          4 * C * c * Real.log (6 * (|u| + 1))) *
        (25 + 8 * u ^ 2) ^ 8))
  let F : ℂ → ℂ → ℂ := fun z w =>
    hughesYoungCompletePositiveCentralMeromorphic T t h k a b z w W
  have hR : 0 < R := by dsimp only [R]; positivity
  have hAnalytic : ∀ z ∈ ball (0 : ℂ) R, ∀ w ∈ ball (0 : ℂ) R,
      AnalyticAt ℂ (fun p : ℂ × ℂ => F p.1 p.2) (z, w) := by
    intro z hz w hw
    have hz' : ‖z‖ < c / 4 := by
      simpa only [R, mem_ball, dist_zero_right] using hz
    have hw' : ‖w‖ < c / 4 := by
      simpa only [R, mem_ball, dist_zero_right] using hw
    simpa only [F, W, a, b] using
      analyticAt_hughesYoungCompletePositiveCentralMeromorphic_lowAuxiliary
        T t h k a b hc hc4 hz' hw'
  have hBound : ∀ z ∈ ball (0 : ℂ) R, ∀ w ∈ ball (0 : ℂ) R,
      ‖F z w‖ ≤ H := by
    intro z hz w hw
    have hz' : ‖z‖ ≤ c / 4 := by
      have hzlt : ‖z‖ < c / 4 := by
        simpa only [R, mem_ball, dist_zero_right] using hz
      exact hzlt.le
    have hw' : ‖w‖ ≤ c / 4 := by
      have hwlt : ‖w‖ < c / 4 := by
        simpa only [R, mem_ball, dist_zero_right] using hw
      exact hwlt.le
    simpa only [F, W, H, a, b] using hpoint T t u hT ht hh hk hz' hw'
  have hcauchy := norm_deriv_right_deriv_left_le_of_analyticOn_bidisc
    F hR hAnalytic hBound
  change ‖deriv (fun w => deriv (fun z => F z w) 0) 0‖ ≤ _
  calc
    _ ≤ (H / (R / 2)) / (R / 4) := hcauchy
    _ = A * ‖hughesYoungLocalizedStaticScalar T h k‖ *
          ((a : ℝ) ^ (c - 1 / 2) * (b : ℝ) ^ (c - 1 / 2)) *
          (((a : ℝ) ^ (c / 4) * (a : ℝ) ^ ε) *
            ((b : ℝ) ^ (c / 4) * (b : ℝ) ^ ε)) *
          (c⁻¹ ^ 5 * T ^ (4 * C * c) * (1 + |u|) ^ 2 *
            (Real.exp
              (100 * c ^ 2 - 84 * u ^ 2 +
                4 * C * c * Real.log (6 * (|u| + 1))) *
              (25 + 8 * u ^ 2) ^ 8)) := by
      dsimp only [H, R, A]
      field_simp [hc.ne']
      ring

theorem exists_norm_mixedDeriv_hughesYoungCompletePositiveCentralMeromorphic_low_le
    {c ε : ℝ} (hc : 0 < c) (hc4 : c < 1 / 4) (hε : 0 < ε) :
    ∃ C A : ℝ, 0 < C ∧ 0 < A ∧ ∀ (T t u : ℝ), 1 ≤ T →
      |t| ∈ Set.Icc (T / 4) (4 * T) → ∀ {h k : ℕ}, 0 < h → 0 < k →
      let a := hughesYoungReducedLeft h k
      let b := hughesYoungReducedRight h k
      ‖deriv (fun w => deriv (fun z =>
          hughesYoungCompletePositiveCentralMeromorphic
            T t h k a b z w ((c : ℂ) + (u : ℂ) * I)) 0) 0‖ ≤
        A * ‖hughesYoungLocalizedStaticScalar T h k‖ *
          ((a : ℝ) ^ (c - 1 / 2) * (b : ℝ) ^ (c - 1 / 2)) *
          (((a : ℝ) ^ (c / 4) * (a : ℝ) ^ ε) *
            ((b : ℝ) ^ (c / 4) * (b : ℝ) ^ ε)) *
          (c⁻¹ ^ 5 * T ^ (4 * C * c) * (1 + |u|) ^ 2 *
            (Real.exp
              (100 * c ^ 2 - 84 * u ^ 2 +
                4 * C * c * Real.log (6 * (|u| + 1))) *
              (25 + 8 * u ^ 2) ^ 8)) := by
  obtain ⟨C, hC, hweight⟩ :=
    exists_norm_hughesYoungRightContourWeight_shift_le_abs_height_power
  obtain ⟨A, hA, hbound⟩ :=
    exists_norm_mixedDeriv_hughesYoungCompletePositiveCentralMeromorphic_low_le_of_heightConstant
      C hweight hc hc4 hε
  exact ⟨C, A, hC, hA, hbound⟩

/-- A parameterized complex derivative at the origin is measurable when
all sufficiently small finite-difference slices are continuous.  This
local formulation is useful for meromorphic families: it never extends
the auxiliary variable beyond the pole-free disc on which the derivative
is taken. -/
theorem aestronglyMeasurable_deriv_zero_of_measurable_slices
    (F : ℂ → ℝ → ℂ) {r : ℝ} (hr : 0 < r)
    (hmeas : ∀ z : ℂ, ‖z‖ ≤ r → AEStronglyMeasurable (F z))
    (hdiff : ∀ u : ℝ, DifferentiableAt ℂ (fun z ↦ F z u) 0) :
    AEStronglyMeasurable (fun u : ℝ ↦ deriv (fun z ↦ F z u) 0) := by
  let q : ℕ → ℂ := fun n ↦
    ((r : ℂ) * ((1 / ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ))
  let A : ℕ → ℝ → ℂ := fun n u ↦
    (q n)⁻¹ • (F (0 + q n) u - F 0 u)
  have hqNorm : ∀ n : ℕ, ‖q n‖ ≤ r := by
    intro n
    have hn : (1 : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    have hn0 : (0 : ℝ) < (n + 1 : ℕ) := lt_of_lt_of_le zero_lt_one hn
    have hdiv : 1 / ((n + 1 : ℕ) : ℝ) ≤ 1 := (div_le_one hn0).2 hn
    simp only [q, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hr, abs_of_pos (one_div_pos.mpr hn0)]
    nlinarith [one_div_pos.mpr hn0]
  have hqNe : ∀ n : ℕ, q n ≠ 0 := by
    intro n
    have hn0 : (0 : ℝ) < (n + 1 : ℕ) := by positivity
    dsimp only [q]
    exact mul_ne_zero (ofReal_ne_zero.mpr hr.ne')
      (ofReal_ne_zero.mpr (one_div_ne_zero hn0.ne'))
  have hq0 : Tendsto q atTop (nhds 0) := by
    have hreal : Tendsto (fun n : ℕ ↦ (1 / ((n + 1 : ℕ) : ℝ) : ℝ))
        atTop (nhds 0) := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        (tendsto_one_div_add_atTop_nhds_zero_nat :
          Tendsto (fun n : ℕ ↦ (1 / (n + 1 : ℝ) : ℝ)) atTop (nhds 0))
    have hcomplex : Tendsto (fun n : ℕ ↦
        (((1 / ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ))) atTop (nhds 0) := by
      exact (Complex.continuous_ofReal.tendsto 0).comp hreal
    simpa only [q, mul_zero] using tendsto_const_nhds.mul hcomplex
  have hqPunctured : Tendsto q atTop (nhdsWithin 0 ({0} : Set ℂ)ᶜ) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨hq0, ?_⟩
    filter_upwards with n
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hqNe n
  have hA : ∀ n : ℕ, AEStronglyMeasurable (A n) := by
    intro n
    have hmq := hmeas (q n) (hqNorm n)
    have hm0 := hmeas 0 (by simpa using hr.le)
    dsimp only [A]
    simpa only [zero_add] using (hmq.sub hm0).const_smul (q n)⁻¹
  have hlim : ∀ u : ℝ, Tendsto (fun n ↦ A n u) atTop
      (nhds (deriv (fun z ↦ F z u) 0)) := by
    intro u
    have hslope := (hdiff u).hasDerivAt.tendsto_slope_zero.comp hqPunctured
    simpa only [A] using hslope
  exact aestronglyMeasurable_of_tendsto_ae atTop hA
    (Filter.Eventually.of_forall hlim)

theorem aestronglyMeasurable_deriv_zero_of_continuous_slices
    (F : ℂ → ℝ → ℂ) {r : ℝ} (hr : 0 < r)
    (hcont : ∀ z : ℂ, ‖z‖ ≤ r → Continuous (F z))
    (hdiff : ∀ u : ℝ, DifferentiableAt ℂ (fun z ↦ F z u) 0) :
    AEStronglyMeasurable (fun u : ℝ ↦ deriv (fun z ↦ F z u) 0) :=
  aestronglyMeasurable_deriv_zero_of_measurable_slices F hr
    (fun z hz ↦ (hcont z hz).aestronglyMeasurable) hdiff

/-- The ordinate factor left by the two auxiliary Cauchy derivatives on
the low contour.  The extra quadratic weight is paid for by two of the
four Gaussian powers retained in the exact equation-(84) kernel. -/
noncomputable def hughesYoungCentralDerivativeOrdinateFactor
    (C c u : ℝ) : ℝ :=
  (1 + |u|) ^ 2 *
    (Real.exp
      (100 * c ^ 2 - 84 * u ^ 2 +
        4 * C * c * Real.log (6 * (|u| + 1))) *
      (25 + 8 * u ^ 2) ^ 8)

theorem continuous_hughesYoungCentralDerivativeOrdinateFactor
    (C c : ℝ) : Continuous (hughesYoungCentralDerivativeOrdinateFactor C c) := by
  unfold hughesYoungCentralDerivativeOrdinateFactor
  have harg : Continuous (fun u : ℝ ↦ 6 * (|u| + 1)) := by fun_prop
  have hlog : Continuous (fun u : ℝ ↦ Real.log (6 * (|u| + 1))) :=
    harg.log (fun u ↦ by positivity)
  exact ((continuous_const.add continuous_abs).pow 2).mul
    ((Real.continuous_exp.comp
      (((continuous_const.sub
        (continuous_const.mul (continuous_id.pow 2))).add
          (continuous_const.mul hlog)))).mul
      ((continuous_const.add
        (continuous_const.mul (continuous_id.pow 2))).pow 8))

/-- The derivative ordinate factor is uniformly dominated by the already
integrable Hughes--Young small-line factor. -/
theorem hughesYoungCentralDerivativeOrdinateFactor_le_integrated
    (C c u : ℝ) :
    hughesYoungCentralDerivativeOrdinateFactor C c u ≤
      (4 * hughesYoungGaussianPowerConstant 2) *
        hughesYoungIntegratedOrdinateFactor C c u := by
  have hpoly := abs_add_pow_le_gaussian u 1 (by norm_num) 2
  have hExpNeg : Real.exp (-u ^ 2) ≤ 1 := by
    exact Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg u])
  have hweight : (1 + |u|) ^ 2 * Real.exp (-2 * u ^ 2) ≤
      4 * hughesYoungGaussianPowerConstant 2 := by
    have hpoly' : (1 + |u|) ^ 2 ≤
        4 * hughesYoungGaussianPowerConstant 2 * Real.exp (u ^ 2) := by
      calc
        (1 + |u|) ^ 2 = (|u| + 1) ^ 2 := by ring
        _ ≤ (1 + 1) ^ 2 * hughesYoungGaussianPowerConstant 2 *
            Real.exp (u ^ 2) := hpoly
        _ = 4 * hughesYoungGaussianPowerConstant 2 * Real.exp (u ^ 2) := by
          norm_num
    calc
      (1 + |u|) ^ 2 * Real.exp (-2 * u ^ 2) ≤
          (4 * hughesYoungGaussianPowerConstant 2 * Real.exp (u ^ 2)) *
            Real.exp (-2 * u ^ 2) := by
        exact mul_le_mul_of_nonneg_right hpoly' (Real.exp_pos _).le
      _ = (4 * hughesYoungGaussianPowerConstant 2) * Real.exp (-u ^ 2) := by
        calc
          _ = (4 * hughesYoungGaussianPowerConstant 2) *
              (Real.exp (u ^ 2) * Real.exp (-2 * u ^ 2)) := by ring
          _ = (4 * hughesYoungGaussianPowerConstant 2) *
              Real.exp (u ^ 2 + (-2 * u ^ 2)) := by rw [Real.exp_add]
          _ = _ := by
            congr 2
            ring
      _ ≤ 4 * hughesYoungGaussianPowerConstant 2 := by
        calc
          _ ≤ (4 * hughesYoungGaussianPowerConstant 2) * 1 := by
            exact mul_le_mul_of_nonneg_left hExpNeg
              (mul_nonneg (by norm_num) (hughesYoungGaussianPowerConstant_pos 2).le)
          _ = _ := mul_one _
  unfold hughesYoungCentralDerivativeOrdinateFactor
    hughesYoungIntegratedOrdinateFactor
  rw [show
      100 * c ^ 2 - 84 * u ^ 2 +
          4 * C * c * Real.log (6 * (|u| + 1)) =
        (100 * c ^ 2 - 82 * u ^ 2 +
          4 * C * c * Real.log (6 * (|u| + 1))) + (-2 * u ^ 2) by ring,
    Real.exp_add]
  have hbase : 0 ≤ Real.exp
      (100 * c ^ 2 - 82 * u ^ 2 +
        4 * C * c * Real.log (6 * (|u| + 1))) *
      (25 + 8 * u ^ 2) ^ 8 := by positivity
  calc
    (1 + |u|) ^ 2 *
          (Real.exp
              (100 * c ^ 2 - 82 * u ^ 2 +
                4 * C * c * Real.log (6 * (|u| + 1))) *
              Real.exp (-2 * u ^ 2) *
            (25 + 8 * u ^ 2) ^ 8) =
        ((1 + |u|) ^ 2 * Real.exp (-2 * u ^ 2)) *
          (Real.exp
              (100 * c ^ 2 - 82 * u ^ 2 +
                4 * C * c * Real.log (6 * (|u| + 1))) *
            (25 + 8 * u ^ 2) ^ 8) := by ring
    _ ≤ (4 * hughesYoungGaussianPowerConstant 2) *
          (Real.exp
              (100 * c ^ 2 - 82 * u ^ 2 +
                4 * C * c * Real.log (6 * (|u| + 1))) *
            (25 + 8 * u ^ 2) ^ 8) :=
      mul_le_mul_of_nonneg_right hweight hbase

theorem integrable_hughesYoungCentralDerivativeOrdinateFactor
    {C : ℝ} (hC : 0 < C) {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) :
    Integrable (hughesYoungCentralDerivativeOrdinateFactor C c) := by
  have hmajor : Integrable (fun u : ℝ ↦
      (4 * hughesYoungGaussianPowerConstant 2) *
        hughesYoungIntegratedOrdinateFactor C c u) :=
    (integrable_hughesYoungIntegratedOrdinateFactor hC hc hc1).const_mul _
  apply hmajor.mono'
  · exact (continuous_hughesYoungCentralDerivativeOrdinateFactor C c).aestronglyMeasurable
  · filter_upwards with u
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · exact hughesYoungCentralDerivativeOrdinateFactor_le_integrated C c u
    · unfold hughesYoungCentralDerivativeOrdinateFactor
      positivity

/-- The whole-line mass of the differentiated central ordinate factor is
uniform in every positive contour abscissa at most one. -/
theorem exists_uniform_integral_hughesYoungCentralDerivativeOrdinateFactor_le
    {C : ℝ} (hC : 0 < C) :
    ∃ L : ℝ, 0 < L ∧ ∀ {c : ℝ}, 0 < c → c ≤ 1 →
      (∫ u : ℝ, hughesYoungCentralDerivativeOrdinateFactor C c u) ≤ L := by
  obtain ⟨K, hK, hgaussian⟩ :=
    exists_hughesYoungIntegratedOrdinateFactor_le_gaussian hC
  let q : ℝ → ℝ := fun u ↦
    (4 * hughesYoungGaussianPowerConstant 2) * K * Real.exp (-80 * u ^ 2)
  let L : ℝ := 1 + ∫ u : ℝ, q u
  have hqInt : Integrable q := by
    have h := ((integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 80)).const_mul K).const_mul
      (4 * hughesYoungGaussianPowerConstant 2)
    simpa only [q, mul_assoc] using h
  have hqNonneg : 0 ≤ ∫ u : ℝ, q u := integral_nonneg (fun u ↦ by
    dsimp only [q]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num) (hughesYoungGaussianPowerConstant_pos 2).le)
        hK.le)
      (Real.exp_pos _).le)
  have hL : 0 < L := by dsimp only [L]; linarith
  refine ⟨L, hL, ?_⟩
  intro c hc hc1
  have hfInt := integrable_hughesYoungCentralDerivativeOrdinateFactor hC hc hc1
  have hpoint : ∀ u : ℝ,
      hughesYoungCentralDerivativeOrdinateFactor C c u ≤ q u := by
    intro u
    calc
      hughesYoungCentralDerivativeOrdinateFactor C c u ≤
          (4 * hughesYoungGaussianPowerConstant 2) *
            hughesYoungIntegratedOrdinateFactor C c u :=
        hughesYoungCentralDerivativeOrdinateFactor_le_integrated C c u
      _ ≤ (4 * hughesYoungGaussianPowerConstant 2) *
          (K * Real.exp (-80 * u ^ 2)) := by
        exact mul_le_mul_of_nonneg_left (hgaussian hc hc1 u)
          (mul_nonneg (by norm_num) (hughesYoungGaussianPowerConstant_pos 2).le)
      _ = q u := by dsimp only [q]; ring
  calc
    (∫ u : ℝ, hughesYoungCentralDerivativeOrdinateFactor C c u) ≤
        ∫ u : ℝ, q u := integral_mono hfInt hqInt hpoint
    _ ≤ L := by dsimp only [L]; linarith

/-- On the actual positive low contour, both Hughes--Young auxiliary
derivatives commute with the whole-line Mellin integral.  All
measurability is obtained from finite difference quotients inside the
pole-free auxiliary bidisc, while the quantitative equation-(96) bound
supplies one common integrable envelope. -/
theorem hughesYoungCompletePositiveCentralMeromorphic_low_differentiation_package
    {c ε : ℝ} (hc : 0 < c) (hc4 : c < 1 / 4) (hε : 0 < ε)
    (T t : ℝ) (hT : 1 ≤ T) (ht : |t| ∈ Set.Icc (T / 4) (4 * T))
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) :
    let a := hughesYoungReducedLeft h k
    let b := hughesYoungReducedRight h k
    (HasDerivAt (fun w ↦ deriv (fun z ↦ ∫ u : ℝ,
        hughesYoungCompletePositiveCentralMeromorphic T t h k a b z w
          ((c : ℂ) + (u : ℂ) * I)) 0)
        (∫ u : ℝ, deriv (fun w ↦ deriv (fun z ↦
          hughesYoungCompletePositiveCentralMeromorphic T t h k a b z w
            ((c : ℂ) + (u : ℂ) * I)) 0) 0) 0) ∧
      (∀ w ∈ ball (0 : ℂ) (c / 16),
        DifferentiableAt ℂ (fun z ↦ ∫ u : ℝ,
          hughesYoungCompletePositiveCentralMeromorphic T t h k a b z w
            ((c : ℂ) + (u : ℂ) * I)) 0) := by
  let a : ℕ := hughesYoungReducedLeft h k
  let b : ℕ := hughesYoungReducedRight h k
  let R : ℝ := c / 4
  let F : ℂ → ℂ → ℝ → ℂ := fun z w u ↦
    hughesYoungCompletePositiveCentralMeromorphic T t h k a b z w
      ((c : ℂ) + (u : ℂ) * I)
  obtain ⟨C, A, hC, hA, hpoint⟩ :=
    exists_norm_hughesYoungCompletePositiveCentralMeromorphic_low_le hc hc4 hε
  let D : ℝ := A * ‖hughesYoungLocalizedStaticScalar T h k‖ *
    ((a : ℝ) ^ (c - 1 / 2) * (b : ℝ) ^ (c - 1 / 2)) *
    (((a : ℝ) ^ (c / 4) * (a : ℝ) ^ ε) *
      ((b : ℝ) ^ (c / 4) * (b : ℝ) ^ ε)) *
    (c⁻¹ ^ 3 * T ^ (4 * C * c))
  let g : ℝ → ℝ := fun u ↦
    D * hughesYoungCentralDerivativeOrdinateFactor C c u
  have hR : 0 < R := by dsimp only [R]; positivity
  have hc1 : c ≤ 1 := hc4.le.trans (by norm_num)
  have hg : Integrable g := by
    simpa only [g] using
      (integrable_hughesYoungCentralDerivativeOrdinateFactor hC hc hc1).const_mul D
  have hAnalytic : ∀ u : ℝ, ∀ z ∈ ball (0 : ℂ) R,
      ∀ w ∈ ball (0 : ℂ) R,
        AnalyticAt ℂ (fun p : ℂ × ℂ ↦ F p.1 p.2 u) (z, w) := by
    intro u z hz w hw
    have hz' : ‖z‖ < c / 4 := by
      simpa only [R, mem_ball, dist_zero_right] using hz
    have hw' : ‖w‖ < c / 4 := by
      simpa only [R, mem_ball, dist_zero_right] using hw
    simpa only [F, a, b] using
      analyticAt_hughesYoungCompletePositiveCentralMeromorphic_lowAuxiliary
        T t h k a b hc hc4 hz' hw'
  have hFmeas : ∀ z ∈ ball (0 : ℂ) R, ∀ w ∈ ball (0 : ℂ) R,
      AEStronglyMeasurable (F z w) := by
    intro z hz w hw
    have hz' : ‖z‖ ≤ c / 4 := by
      have := show ‖z‖ < c / 4 by
        simpa only [R, mem_ball, dist_zero_right] using hz
      exact this.le
    have hw' : ‖w‖ ≤ c / 4 := by
      have := show ‖w‖ < c / 4 by
        simpa only [R, mem_ball, dist_zero_right] using hw
      exact this.le
    simpa only [F, a, b] using
      (continuous_hughesYoungCompletePositiveCentralMeromorphic_vertical
        T t h k a b hc hc4 hz' hw' (Or.inl rfl)).aestronglyMeasurable
  have hFzmeas : ∀ w ∈ ball (0 : ℂ) (R / 4),
      AEStronglyMeasurable
        (fun u ↦ deriv (fun z ↦ F z w u) 0) := by
    intro w hw
    have hw' : ‖w‖ < c / 4 := by
      have hsmall : ‖w‖ < R / 4 := by
        simpa only [mem_ball, dist_zero_right] using hw
      dsimp only [R] at hsmall
      linarith
    apply aestronglyMeasurable_deriv_zero_of_continuous_slices
      (fun z u ↦ F z w u) (r := c / 4) (by positivity)
    · intro z hz
      simpa only [F, a, b] using
        continuous_hughesYoungCompletePositiveCentralMeromorphic_vertical
          T t h k a b hc hc4 hz hw'.le (Or.inl rfl)
    · intro u
      exact (analyticAt_hughesYoungCompletePositiveCentralMeromorphic_lowAuxiliary
        T t h k a b hc hc4 (by simpa using hc) hw').curry_left.differentiableAt
  have hFzwmeas : AEStronglyMeasurable
      (fun u ↦ deriv (fun w ↦ deriv (fun z ↦ F z w u) 0) 0) := by
    let G : ℂ → ℝ → ℂ := fun w u ↦ deriv (fun z ↦ F z w u) 0
    have hGmeas : ∀ w : ℂ, ‖w‖ ≤ c / 32 → AEStronglyMeasurable (G w) := by
      intro w hw
      apply hFzmeas w
      have : ‖w‖ < R / 4 := by
        dsimp only [R]
        linarith
      simpa only [mem_ball, dist_zero_right] using this
    have hGdiff : ∀ u : ℝ, DifferentiableAt ℂ (fun w ↦ G w u) 0 := by
      intro u
      have hjoint := analyticAt_hughesYoungCompletePositiveCentralMeromorphic_lowAuxiliary
        T t h k a b hc hc4 (z := (0 : ℂ)) (w := (0 : ℂ))
          (u := u)
          (by simpa using hc) (by simpa using hc)
      simpa only [G, F] using (AnalyticAt.deriv_fst_curry hjoint).differentiableAt
    simpa only [G] using
      aestronglyMeasurable_deriv_zero_of_measurable_slices
        G (r := c / 32) (by positivity) hGmeas hGdiff
  have hEnvelope : ∀ u : ℝ, ∀ z ∈ ball (0 : ℂ) R,
      ∀ w ∈ ball (0 : ℂ) R, ‖F z w u‖ ≤ g u := by
    intro u z hz w hw
    have hz' : ‖z‖ ≤ c / 4 := by
      have := show ‖z‖ < c / 4 by
        simpa only [R, mem_ball, dist_zero_right] using hz
      exact this.le
    have hw' : ‖w‖ ≤ c / 4 := by
      have := show ‖w‖ < c / 4 by
        simpa only [R, mem_ball, dist_zero_right] using hw
      exact this.le
    have hbnd := hpoint T t u hT ht hh hk hz' hw'
    change ‖hughesYoungCompletePositiveCentralMeromorphic T t h k a b z w
      ((c : ℂ) + (u : ℂ) * I)‖ ≤ g u
    apply hbnd.trans_eq
    dsimp only [g, D, hughesYoungCentralDerivativeOrdinateFactor]
    ring
  constructor
  · exact hasDerivAt_right_deriv_left_integral_of_analytic_dominated
      F hR hAnalytic hFmeas hFzmeas hFzwmeas g hg hEnvelope
  · intro w hw
    have hw' : w ∈ ball (0 : ℂ) (R / 4) := by
      have hradius : R / 4 = c / 16 := by
        dsimp only [R]
        ring
      rwa [hradius]
    exact differentiableAt_left_integral_of_analytic_dominated
      F hR hAnalytic hFmeas hFzmeas g hg hEnvelope hw'

theorem hasDerivAt_right_deriv_left_integral_hughesYoungCompletePositiveCentralMeromorphic_low
    {c ε : ℝ} (hc : 0 < c) (hc4 : c < 1 / 4) (hε : 0 < ε)
    (T t : ℝ) (hT : 1 ≤ T) (ht : |t| ∈ Set.Icc (T / 4) (4 * T))
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) :
    let a := hughesYoungReducedLeft h k
    let b := hughesYoungReducedRight h k
    HasDerivAt (fun w ↦ deriv (fun z ↦ ∫ u : ℝ,
      hughesYoungCompletePositiveCentralMeromorphic T t h k a b z w
        ((c : ℂ) + (u : ℂ) * I)) 0)
      (∫ u : ℝ, deriv (fun w ↦ deriv (fun z ↦
        hughesYoungCompletePositiveCentralMeromorphic T t h k a b z w
          ((c : ℂ) + (u : ℂ) * I)) 0) 0) 0 :=
  (hughesYoungCompletePositiveCentralMeromorphic_low_differentiation_package
    hc hc4 hε T t hT ht hh hk).1

/-- Value form of the quantitative low-contour derivative interchange. -/
theorem deriv_right_deriv_left_integral_hughesYoungCompletePositiveCentralMeromorphic_low
    {c ε : ℝ} (hc : 0 < c) (hc4 : c < 1 / 4) (hε : 0 < ε)
    (T t : ℝ) (hT : 1 ≤ T) (ht : |t| ∈ Set.Icc (T / 4) (4 * T))
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) :
    let a := hughesYoungReducedLeft h k
    let b := hughesYoungReducedRight h k
    deriv (fun w ↦ deriv (fun z ↦ ∫ u : ℝ,
      hughesYoungCompletePositiveCentralMeromorphic T t h k a b z w
        ((c : ℂ) + (u : ℂ) * I)) 0) 0 =
      ∫ u : ℝ, deriv (fun w ↦ deriv (fun z ↦
        hughesYoungCompletePositiveCentralMeromorphic T t h k a b z w
          ((c : ℂ) + (u : ℂ) * I)) 0) 0 :=
  (hasDerivAt_right_deriv_left_integral_hughesYoungCompletePositiveCentralMeromorphic_low
    hc hc4 hε T t hT ht hh hk).deriv

/-- The differentiated residue crossing followed by the exact
fourth-order auxiliary cancellation identifies the source-line
Hughes--Young coefficient with the mixed derivative integral on the
positive low contour. -/
theorem integral_hughesYoungCompletePositiveCentralContinuation_eq_integral_mixedDeriv_low
    {c ε : ℝ} (hc : 0 < c) (hc4 : c < 1 / 4) (hε : 0 < ε)
    (T t : ℝ) (hT : 1 ≤ T) (ht : |t| ∈ Set.Icc (T / 4) (4 * T))
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) :
    let a := hughesYoungReducedLeft h k
    let b := hughesYoungReducedRight h k
    (∫ u : ℝ, hughesYoungCompletePositiveCentralContinuation
        T t h k a b ((1 : ℂ) + (u : ℂ) * I)) =
      ∫ u : ℝ, deriv (fun w ↦ deriv (fun z ↦
        hughesYoungCompletePositiveCentralMeromorphic T t h k a b z w
          ((c : ℂ) + (u : ℂ) * I)) 0) 0 := by
  let a : ℕ := hughesYoungReducedLeft h k
  let b : ℕ := hughesYoungReducedRight h k
  let B : ℂ → ℂ → ℂ := fun z w ↦ ∫ u : ℝ,
    hughesYoungCompletePositiveCentralMeromorphic T t h k a b z w
      ((c : ℂ) + (u : ℂ) * I)
  let P : ℂ → ℂ → ℂ := fun z w ↦
    hughesYoungCompletePositiveCentralPoleFree T t h k a b
      (hughesYoungCentralMovingPole z w) z w
  have ha : 0 < a := hughesYoungReducedLeft_pos hh
  have hb : 0 < b := hughesYoungReducedRight_pos hh hk
  have hpack :=
    hughesYoungCompletePositiveCentralMeromorphic_low_differentiation_package
      hc hc4 hε T t hT ht hh hk
  have hBouter : HasDerivAt (fun w ↦ deriv (fun z ↦ B z w) 0)
      (∫ u : ℝ, deriv (fun w ↦ deriv (fun z ↦
        hughesYoungCompletePositiveCentralMeromorphic T t h k a b z w
          ((c : ℂ) + (u : ℂ) * I)) 0) 0) 0 := by
    simpa only [B, a, b] using hpack.1
  have hBnear : ∀ᶠ w in nhds (0 : ℂ),
      DifferentiableAt ℂ (fun z ↦ B z w) 0 := by
    filter_upwards [ball_mem_nhds (0 : ℂ) (by positivity : 0 < c / 16)] with w hw
    simpa only [B, a, b] using hpack.2 w hw
  have hPanalytic : AnalyticAt ℂ
      (fun p : ℂ × ℂ ↦ P p.1 p.2) (0, 0) := by
    simpa only [P] using
      analyticAt_hughesYoungCompletePositiveCentralPoleFree_movingPole
        T t h k a b
  have hPnear : ∀ᶠ w in nhds (0 : ℂ),
      AnalyticAt ℂ (fun p : ℂ × ℂ ↦ P p.1 p.2) (0, w) := by
    have hmap : Tendsto (fun w : ℂ ↦ ((0 : ℂ), w)) (nhds 0) (nhds (0, 0)) := by
      exact (continuous_const.prodMk continuous_id).continuousAt.tendsto
    exact hmap hPanalytic.eventually_analyticAt
  have hInnerEq :
      (fun w ↦ deriv (fun z ↦ B z w + (Real.pi : ℂ) * P z w) 0) =ᶠ[nhds 0]
        fun w ↦ deriv (fun z ↦ B z w) 0 +
          (Real.pi : ℂ) * deriv (fun z ↦ P z w) 0 := by
    filter_upwards [hBnear, hPnear] with w hBw hPw
    have hPz : DifferentiableAt ℂ (fun z ↦ P z w) 0 :=
      hPw.curry_left.differentiableAt
    simpa using (hBw.hasDerivAt.add (hPz.hasDerivAt.const_mul (Real.pi : ℂ))).deriv
  have hPouterAnalytic : AnalyticAt ℂ
      (fun w ↦ deriv (fun z ↦ P z w) 0) 0 := by
    simpa only [P] using AnalyticAt.deriv_fst_curry hPanalytic
  have hPzero : deriv (fun w ↦ deriv (fun z ↦ P z w) 0) 0 = 0 := by
    simpa only [P] using
      deriv_right_deriv_left_hughesYoungCompletePositiveCentralPoleFree_movingPole_zero
        T t h k a b
  have hPouter : HasDerivAt (fun w ↦ deriv (fun z ↦ P z w) 0) 0 0 :=
    hPouterAnalytic.differentiableAt.hasDerivAt.congr_deriv hPzero
  have hSum : HasDerivAt
      (fun w ↦ deriv (fun z ↦ B z w) 0 +
        (Real.pi : ℂ) * deriv (fun z ↦ P z w) 0)
      (∫ u : ℝ, deriv (fun w ↦ deriv (fun z ↦
        hughesYoungCompletePositiveCentralMeromorphic T t h k a b z w
          ((c : ℂ) + (u : ℂ) * I)) 0) 0) 0 := by
    simpa using hBouter.add (hPouter.const_mul (Real.pi : ℂ))
  have hCombined : HasDerivAt
      (fun w ↦ deriv (fun z ↦ B z w + (Real.pi : ℂ) * P z w) 0)
      (∫ u : ℝ, deriv (fun w ↦ deriv (fun z ↦
        hughesYoungCompletePositiveCentralMeromorphic T t h k a b z w
          ((c : ℂ) + (u : ℂ) * I)) 0) 0) 0 :=
    hSum.congr_of_eventuallyEq hInnerEq
  have hshift :=
    integral_hughesYoungCompletePositiveCentralContinuation_eq_mixedDeriv_low_add_residue
      T t h k ha hb hc hc4
  calc
    (∫ u : ℝ, hughesYoungCompletePositiveCentralContinuation
        T t h k a b ((1 : ℂ) + (u : ℂ) * I)) =
        deriv (fun w ↦ deriv (fun z ↦ B z w +
          (Real.pi : ℂ) * P z w) 0) 0 := by
            simpa only [B, P, a, b] using hshift
    _ = ∫ u : ℝ, deriv (fun w ↦ deriv (fun z ↦
        hughesYoungCompletePositiveCentralMeromorphic T t h k a b z w
          ((c : ℂ) + (u : ℂ) * I)) 0) 0 := hCombined.deriv

/-- Uniform quantitative bound for the actual source-line central
coefficient after the positive low-contour shift and auxiliary
differentiation. -/
theorem exists_norm_integral_hughesYoungCompletePositiveCentralContinuation_le_of_heightConstant
    (C : ℝ) (hC : 0 < C)
    (hweight : ∀ (T t u c : ℝ), 1 ≤ T →
      |t| ∈ Set.Icc (T / 4) (4 * T) → 0 < c → c ≤ 1 →
      ‖hughesYoungRightContourWeight t c u‖ ≤
        c⁻¹ * T ^ (4 * C * c) *
          (Real.exp
            (100 * c ^ 2 - 84 * u ^ 2 +
              4 * C * c * Real.log (6 * (|u| + 1))) *
            (25 + 8 * u ^ 2) ^ 8))
    {c ε : ℝ} (hc : 0 < c) (hc4 : c < 1 / 4) (hε : 0 < ε) :
    ∃ A : ℝ, 0 < A ∧ ∀ (T t : ℝ), 1 ≤ T →
      |t| ∈ Set.Icc (T / 4) (4 * T) → ∀ {h k : ℕ}, 0 < h → 0 < k →
      let a := hughesYoungReducedLeft h k
      let b := hughesYoungReducedRight h k
      ‖∫ u : ℝ, hughesYoungCompletePositiveCentralContinuation
          T t h k a b ((1 : ℂ) + (u : ℂ) * I)‖ ≤
        A * ‖hughesYoungLocalizedStaticScalar T h k‖ *
          ((a : ℝ) ^ (c - 1 / 2) * (b : ℝ) ^ (c - 1 / 2)) *
          (((a : ℝ) ^ (c / 4) * (a : ℝ) ^ ε) *
            ((b : ℝ) ^ (c / 4) * (b : ℝ) ^ ε)) *
          (c⁻¹ ^ 5 * T ^ (4 * C * c)) := by
  obtain ⟨A₀, hA₀, hpoint⟩ :=
    exists_norm_mixedDeriv_hughesYoungCompletePositiveCentralMeromorphic_low_le_of_heightConstant
      C hweight hc hc4 hε
  obtain ⟨L, hL, hmass⟩ :=
    exists_uniform_integral_hughesYoungCentralDerivativeOrdinateFactor_le hC
  let A : ℝ := A₀ * L
  have hA : 0 < A := mul_pos hA₀ hL
  refine ⟨A, hA, ?_⟩
  intro T t hT ht h k hh hk
  let a : ℕ := hughesYoungReducedLeft h k
  let b : ℕ := hughesYoungReducedRight h k
  let D : ℝ := A₀ * ‖hughesYoungLocalizedStaticScalar T h k‖ *
    ((a : ℝ) ^ (c - 1 / 2) * (b : ℝ) ^ (c - 1 / 2)) *
    (((a : ℝ) ^ (c / 4) * (a : ℝ) ^ ε) *
      ((b : ℝ) ^ (c / 4) * (b : ℝ) ^ ε)) *
    (c⁻¹ ^ 5 * T ^ (4 * C * c))
  let M : ℝ → ℝ := fun u ↦
    D * hughesYoungCentralDerivativeOrdinateFactor C c u
  have ha : 0 < a := hughesYoungReducedLeft_pos hh
  have hb : 0 < b := hughesYoungReducedRight_pos hh hk
  have hD0 : 0 ≤ D := by
    dsimp only [D]
    have hT0 : 0 < T := zero_lt_one.trans_le hT
    positivity
  have hMInt : Integrable M := by
    simpa only [M] using
      (integrable_hughesYoungCentralDerivativeOrdinateFactor hC hc
        (hc4.le.trans (by norm_num))).const_mul D
  have hmajor : ∀ u : ℝ,
      ‖deriv (fun w ↦ deriv (fun z ↦
        hughesYoungCompletePositiveCentralMeromorphic T t h k a b z w
          ((c : ℂ) + (u : ℂ) * I)) 0) 0‖ ≤ M u := by
    intro u
    have hbnd := hpoint T t u hT ht hh hk
    apply hbnd.trans_eq
    dsimp only [M, D, hughesYoungCentralDerivativeOrdinateFactor, a, b]
    ring
  have hnorm := norm_integral_le_of_norm_le hMInt
    (Filter.Eventually.of_forall hmajor)
  have hEq :=
    integral_hughesYoungCompletePositiveCentralContinuation_eq_integral_mixedDeriv_low
      hc hc4 hε T t hT ht hh hk
  have hmass' :
      (∫ u : ℝ, hughesYoungCentralDerivativeOrdinateFactor C c u) ≤ L :=
    hmass hc (hc4.le.trans (by norm_num))
  dsimp only at hEq ⊢
  rw [hEq]
  calc
    ‖∫ u : ℝ, deriv (fun w ↦ deriv (fun z ↦
          hughesYoungCompletePositiveCentralMeromorphic T t h k a b z w
            ((c : ℂ) + (u : ℂ) * I)) 0) 0‖ ≤
        ∫ u : ℝ, M u := hnorm
    _ = D * (∫ u : ℝ,
        hughesYoungCentralDerivativeOrdinateFactor C c u) := by
      dsimp only [M]
      rw [integral_const_mul]
    _ ≤ D * L := mul_le_mul_of_nonneg_left hmass' hD0
    _ = A * ‖hughesYoungLocalizedStaticScalar T h k‖ *
          ((a : ℝ) ^ (c - 1 / 2) * (b : ℝ) ^ (c - 1 / 2)) *
          (((a : ℝ) ^ (c / 4) * (a : ℝ) ^ ε) *
            ((b : ℝ) ^ (c / 4) * (b : ℝ) ^ ε)) *
          (c⁻¹ ^ 5 * T ^ (4 * C * c)) := by
      dsimp only [D, A]
      ring

theorem exists_norm_integral_hughesYoungCompletePositiveCentralContinuation_le
    {c ε : ℝ} (hc : 0 < c) (hc4 : c < 1 / 4) (hε : 0 < ε) :
    ∃ C A : ℝ, 0 < C ∧ 0 < A ∧ ∀ (T t : ℝ), 1 ≤ T →
      |t| ∈ Set.Icc (T / 4) (4 * T) → ∀ {h k : ℕ}, 0 < h → 0 < k →
      let a := hughesYoungReducedLeft h k
      let b := hughesYoungReducedRight h k
      ‖∫ u : ℝ, hughesYoungCompletePositiveCentralContinuation
          T t h k a b ((1 : ℂ) + (u : ℂ) * I)‖ ≤
        A * ‖hughesYoungLocalizedStaticScalar T h k‖ *
          ((a : ℝ) ^ (c - 1 / 2) * (b : ℝ) ^ (c - 1 / 2)) *
          (((a : ℝ) ^ (c / 4) * (a : ℝ) ^ ε) *
            ((b : ℝ) ^ (c / 4) * (b : ℝ) ^ ε)) *
          (c⁻¹ ^ 5 * T ^ (4 * C * c)) := by
  obtain ⟨C, hC, hweight⟩ :=
    exists_norm_hughesYoungRightContourWeight_shift_le_abs_height_power
  obtain ⟨A, hA, hbound⟩ :=
    exists_norm_integral_hughesYoungCompletePositiveCentralContinuation_le_of_heightConstant
      C hC hweight hc hc4 hε
  exact ⟨C, A, hC, hA, hbound⟩

theorem hughesYoungReducedLeft_swap (h k : ℕ) :
    hughesYoungReducedLeft k h = hughesYoungReducedRight h k := by
  unfold hughesYoungReducedLeft hughesYoungReducedRight
    hughesYoungCommonDivisor
  rw [Nat.gcd_comm]

theorem hughesYoungReducedRight_swap (h k : ℕ) :
    hughesYoungReducedRight k h = hughesYoungReducedLeft h k := by
  unfold hughesYoungReducedLeft hughesYoungReducedRight
    hughesYoungCommonDivisor
  rw [Nat.gcd_comm]

theorem hughesYoungLocalizedStaticScalar_swap (T : ℝ) (h k : ℕ) :
    hughesYoungLocalizedStaticScalar T k h =
      hughesYoungLocalizedStaticScalar T h k := by
  unfold hughesYoungLocalizedStaticScalar
  ring

/-- The negative signed equation-(84) branch obeys the same quantitative
bound as the positive branch.  This is a genuine symmetry consequence,
including the dyadic range at `-t` and the swap of the reduced moduli. -/
theorem exists_norm_integral_hughesYoungCompleteNegativeCentralContinuation_le_of_heightConstant
    (C : ℝ) (hC : 0 < C)
    (hweight : ∀ (T t u c : ℝ), 1 ≤ T →
      |t| ∈ Set.Icc (T / 4) (4 * T) → 0 < c → c ≤ 1 →
      ‖hughesYoungRightContourWeight t c u‖ ≤
        c⁻¹ * T ^ (4 * C * c) *
          (Real.exp
            (100 * c ^ 2 - 84 * u ^ 2 +
              4 * C * c * Real.log (6 * (|u| + 1))) *
            (25 + 8 * u ^ 2) ^ 8))
    {c ε : ℝ} (hc : 0 < c) (hc4 : c < 1 / 4) (hε : 0 < ε) :
    ∃ A : ℝ, 0 < A ∧ ∀ (T t : ℝ), 1 ≤ T →
      |t| ∈ Set.Icc (T / 4) (4 * T) → ∀ {h k : ℕ}, 0 < h → 0 < k →
      let a := hughesYoungReducedLeft h k
      let b := hughesYoungReducedRight h k
      ‖∫ u : ℝ, hughesYoungCompleteNegativeCentralContinuation
          T t h k a b ((1 : ℂ) + (u : ℂ) * I)‖ ≤
        A * ‖hughesYoungLocalizedStaticScalar T h k‖ *
          ((a : ℝ) ^ (c - 1 / 2) * (b : ℝ) ^ (c - 1 / 2)) *
          (((a : ℝ) ^ (c / 4) * (a : ℝ) ^ ε) *
            ((b : ℝ) ^ (c / 4) * (b : ℝ) ^ ε)) *
          (c⁻¹ ^ 5 * T ^ (4 * C * c)) := by
  obtain ⟨A, hA, hpositive⟩ :=
    exists_norm_integral_hughesYoungCompletePositiveCentralContinuation_le_of_heightConstant
      C hC hweight hc hc4 hε
  refine ⟨A, hA, ?_⟩
  intro T t hT ht h k hh hk
  have hraw := hpositive T (-t) hT (by simpa only [abs_neg] using ht) hk hh
  dsimp only at hraw ⊢
  rw [show (∫ u : ℝ, hughesYoungCompleteNegativeCentralContinuation
      T t h k (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
        ((1 : ℂ) + (u : ℂ) * I)) =
      ∫ u : ℝ, hughesYoungCompletePositiveCentralContinuation
        T (-t) k h (hughesYoungReducedRight h k)
          (hughesYoungReducedLeft h k) ((1 : ℂ) + (u : ℂ) * I) by
    apply integral_congr_ae
    filter_upwards [] with u
    exact hughesYoungCompleteNegativeCentralContinuation_eq_swap
      T t h k (hughesYoungReducedLeft h k)
        (hughesYoungReducedRight h k) ((1 : ℂ) + (u : ℂ) * I)]
  rw [hughesYoungReducedLeft_swap h k, hughesYoungReducedRight_swap h k,
    hughesYoungLocalizedStaticScalar_swap T h k] at hraw
  simpa only [mul_comm, mul_left_comm, mul_assoc] using hraw

theorem exists_norm_integral_hughesYoungCompleteNegativeCentralContinuation_le
    {c ε : ℝ} (hc : 0 < c) (hc4 : c < 1 / 4) (hε : 0 < ε) :
    ∃ C A : ℝ, 0 < C ∧ 0 < A ∧ ∀ (T t : ℝ), 1 ≤ T →
      |t| ∈ Set.Icc (T / 4) (4 * T) → ∀ {h k : ℕ}, 0 < h → 0 < k →
      let a := hughesYoungReducedLeft h k
      let b := hughesYoungReducedRight h k
      ‖∫ u : ℝ, hughesYoungCompleteNegativeCentralContinuation
          T t h k a b ((1 : ℂ) + (u : ℂ) * I)‖ ≤
        A * ‖hughesYoungLocalizedStaticScalar T h k‖ *
          ((a : ℝ) ^ (c - 1 / 2) * (b : ℝ) ^ (c - 1 / 2)) *
          (((a : ℝ) ^ (c / 4) * (a : ℝ) ^ ε) *
            ((b : ℝ) ^ (c / 4) * (b : ℝ) ^ ε)) *
          (c⁻¹ ^ 5 * T ^ (4 * C * c)) := by
  obtain ⟨C, hC, hweight⟩ :=
    exists_norm_hughesYoungRightContourWeight_shift_le_abs_height_power
  obtain ⟨A, hA, hbound⟩ :=
    exists_norm_integral_hughesYoungCompleteNegativeCentralContinuation_le_of_heightConstant
      C hC hweight hc hc4 hε
  exact ⟨C, A, hC, hA, hbound⟩

end RiemannZeta.GuthMaynard
