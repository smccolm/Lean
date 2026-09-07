import RiemannZeta.GuthMaynard.HughesYoungEquation96DFIBridge

open Complex Finset
open scoped BigOperators

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# Coprime source-line bound for Hughes--Young equation (96)

The reduced twisting integers in Hughes--Young are coprime.  Consequently
the two gcd factors in equation (96) must be combined *before* interpolation:

`gcd(h,l) gcd(k,l) = gcd(hk,l)`.

This removes the spurious square-root loss caused by interpolating the two
factors separately.  The result below is the uniform arithmetic estimate
needed in the equation-(84) source-line consumer.
-/

theorem gcd_mul_gcd_eq_gcd_mul_of_coprime
    {h k l : ℕ} (hhk : h.Coprime k) :
    Nat.gcd h l * Nat.gcd k l = Nat.gcd (h * k) l := by
  have hs := hhk.gcd_mul l
  simpa only [Nat.gcd_comm] using hs.symm

/-- Sharp pointwise equation-(96) majorant for coprime twists.  One
interpolation of `gcd(hk,l)` replaces the two independent square-root
interpolations in the older general-purpose bound. -/
theorem norm_hughesYoungEquation96PositiveTerm_one_one_le_coprime
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (hhk : h.Coprime k)
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (c : ℂ) (y : ℕ+ × ℕ+) :
    ‖hughesYoungEquation96PositiveTerm h k 1 1 (1 + c) y‖ ≤
      (((h * k : ℕ) : ℝ) ^ θ) *
        hughesYoungCommonDivisorMajorant (1 + θ) c.re y := by
  letI : NeZero (y.1 : ℕ) := ⟨y.1.2.ne'⟩
  have hram := norm_ramanujanSum_le_sum_gcd_divisors
    (y.1 : ℕ) (y.2 : ℕ)
  have hlpos : 0 < (((y.1 : ℕ) : ℝ)) := by exact_mod_cast y.1.2
  have hrpos : 0 < (((y.2 : ℕ) : ℝ)) := by exact_mod_cast y.2.2
  have hgcdh : 0 < Nat.gcd h (y.1 : ℕ) :=
    Nat.gcd_pos_of_pos_left _ hh
  have hgcdk : 0 < Nat.gcd k (y.1 : ℕ) :=
    Nat.gcd_pos_of_pos_left _ hk
  have hhkpos : 0 < h * k := Nat.mul_pos hh hk
  have hcombined := natCast_gcd_le_rpow_interpolation
    hhkpos y.1.2 hθ0 hθ1
  have hgcdEq :
      (Nat.gcd h (y.1 : ℕ) : ℝ) * (Nat.gcd k (y.1 : ℕ) : ℝ) =
        (Nat.gcd (h * k) (y.1 : ℕ) : ℝ) := by
    exact_mod_cast gcd_mul_gcd_eq_gcd_mul_of_coprime
      (l := (y.1 : ℕ)) hhk
  have hden1 : 0 < (((y.1 : ℕ) : ℝ) ^ (2 : ℝ)) :=
    Real.rpow_pos_of_pos hlpos _
  have hden2 : 0 < (((y.2 : ℕ) : ℝ) ^ (1 + c.re)) :=
    Real.rpow_pos_of_pos hrpos _
  have hlnorm : ‖(((y.1 : ℕ) : ℂ) ^ ((1 : ℂ) + 1))‖ =
      (((y.1 : ℕ) : ℝ) ^ (2 : ℝ)) := by
    have ht := Complex.norm_natCast_cpow_of_pos
      (n := (y.1 : ℕ)) y.1.2 ((1 : ℂ) + 1)
    norm_num at ht ⊢
  have hrnorm : ‖(((y.2 : ℕ) : ℂ) ^ (1 + c))‖ =
      (((y.2 : ℕ) : ℝ) ^ (1 + c.re)) := by
    simpa only [add_re, one_re] using
      (Complex.norm_natCast_cpow_of_pos
        (n := (y.2 : ℕ)) y.2.2 (1 + c))
  have hhNorm : ‖(((Nat.gcd h (y.1 : ℕ) : ℕ) : ℂ) ^ (1 : ℂ))‖ =
      (Nat.gcd h (y.1 : ℕ) : ℝ) := by
    rw [Complex.norm_natCast_cpow_of_pos hgcdh]
    norm_num
  have hkNorm : ‖(((Nat.gcd k (y.1 : ℕ) : ℕ) : ℂ) ^ (1 : ℂ))‖ =
      (Nat.gcd k (y.1 : ℕ) : ℝ) := by
    rw [Complex.norm_natCast_cpow_of_pos hgcdk]
    norm_num
  have hdenNorm :
      ‖(((y.1 : ℕ) : ℂ) ^ ((1 : ℂ) + 1)) *
          (((y.2 : ℕ) : ℂ) ^ (1 + c))‖ =
        (((y.1 : ℕ) : ℝ) ^ (2 : ℝ)) *
          (((y.2 : ℕ) : ℝ) ^ (1 + c.re)) := by
    rw [norm_mul, hlnorm, hrnorm]
  unfold hughesYoungEquation96PositiveTerm
  rw [norm_div, hdenNorm]
  simp only [norm_mul, hhNorm, hkNorm]
  unfold hughesYoungCommonDivisorMajorant
  rw [← Finset.sum_div, ← Finset.sum_div]
  rw [mul_assoc, hgcdEq]
  calc
    ‖ramanujanSum (y.1 : ℕ) (y.2 : ℕ)‖ *
          (Nat.gcd (h * k) (y.1 : ℕ) : ℝ) /
        ((((y.1 : ℕ) : ℝ) ^ (2 : ℝ)) *
          (((y.2 : ℕ) : ℝ) ^ (1 + c.re))) ≤
      (∑ d ∈ (Nat.gcd (y.1 : ℕ) (y.2 : ℕ)).divisors, (d : ℝ)) *
          ((((h * k : ℕ) : ℝ) ^ θ) *
            (((y.1 : ℕ) : ℝ) ^ (1 - θ))) /
        ((((y.1 : ℕ) : ℝ) ^ (2 : ℝ)) *
          (((y.2 : ℕ) : ℝ) ^ (1 + c.re))) := by
      gcongr
      exact hcombined
    _ = (((h * k : ℕ) : ℝ) ^ θ) *
        ((∑ d ∈ (Nat.gcd (y.1 : ℕ) (y.2 : ℕ)).divisors, (d : ℝ)) /
          (((y.1 : ℕ) : ℝ) ^ (1 + θ)) /
          (((y.2 : ℕ) : ℝ) ^ (1 + c.re))) := by
      rw [show ((y.1 : ℕ) : ℝ) ^ (2 : ℝ) =
          ((y.1 : ℕ) : ℝ) ^ (1 + θ) *
            ((y.1 : ℕ) : ℝ) ^ (1 - θ) by
        rw [← Real.rpow_add hlpos]
        congr 1
        ring]
      field_simp [hden1.ne', hden2.ne',
        (Real.rpow_pos_of_pos hlpos (1 + θ)).ne',
        (Real.rpow_pos_of_pos hlpos (1 - θ)).ne']

/-- Pointwise source-line estimate after either choice of the two DFI
logarithmic operators. -/
theorem norm_hughesYoungEquation96VerticalTerm_mul_logSelectors_le_coprime
    (i j : Bool) (u : ℝ) {h k : ℕ}
    (hh : 0 < h) (hk : 0 < k) (hhk : h.Coprime k)
    {η : ℝ} (hη : 0 < η) (hη4 : η < 1 / 4)
    (y : ℕ+ × ℕ+) :
    ‖hughesYoungEquation96PositiveTerm h k 1 1
          ((2 : ℂ) + (2 * u : ℂ) * I) y *
        hughesYoungDFIPositiveLogSelectorLeft i h y *
        hughesYoungDFIPositiveLogSelectorRight j k y‖ ≤
      ((((h * k : ℕ) : ℝ) ^ (3 * η)) *
          (1 + 6 * η⁻¹ + 2 * |Real.eulerMascheroniConstant|) ^ 2 *
          ((h : ℝ) ^ η * (k : ℝ) ^ η)) *
        hughesYoungPositivePairMajorant (1 + η) (1 - 2 * η) y := by
  let D : ℝ := 1 + 6 * η⁻¹ + 2 * |Real.eulerMascheroniConstant|
  let K : ℝ := (((h * k : ℕ) : ℝ) ^ (3 * η)) * D ^ 2 *
    ((h : ℝ) ^ η * (k : ℝ) ^ η)
  have hθ0 : 0 ≤ 3 * η := by positivity
  have hθ1 : 3 * η ≤ 1 := by linarith
  have hA : 1 < 1 + η := by linarith
  have hC : 0 < 1 - 2 * η := by linarith
  have hterm0 := norm_hughesYoungEquation96PositiveTerm_one_one_le_coprime
    hh hk hhk hθ0 hθ1 (1 : ℂ) y
  have hterm :
      ‖hughesYoungEquation96PositiveTerm h k 1 1
          ((2 : ℂ) + (2 * u : ℂ) * I) y‖ ≤
        (((h * k : ℕ) : ℝ) ^ (3 * η)) *
          hughesYoungCommonDivisorMajorant (1 + 3 * η) 1 y := by
    rw [norm_hughesYoungEquation96PositiveTerm_vertical_eq h k u y]
    convert hterm0 using 1
    all_goals norm_num
  have hleft := norm_hughesYoungDFIPositiveLogSelectorLeft_le i hη hh y
  have hright := norm_hughesYoungDFIPositiveLogSelectorRight_le j hη hk y
  have hcommon0 : 0 ≤ hughesYoungCommonDivisorMajorant (1 + 3 * η) 1 y := by
    unfold hughesYoungCommonDivisorMajorant
    positivity
  rw [norm_mul, norm_mul]
  calc
    ‖hughesYoungEquation96PositiveTerm h k 1 1
          ((2 : ℂ) + (2 * u : ℂ) * I) y‖ *
        ‖hughesYoungDFIPositiveLogSelectorLeft i h y‖ *
        ‖hughesYoungDFIPositiveLogSelectorRight j k y‖ ≤
      ((((h * k : ℕ) : ℝ) ^ (3 * η)) *
          hughesYoungCommonDivisorMajorant (1 + 3 * η) 1 y) *
        (D * (h : ℝ) ^ η * ((y.1 : ℕ) : ℝ) ^ η * ((y.2 : ℕ) : ℝ) ^ η) *
        (D * (k : ℝ) ^ η * ((y.1 : ℕ) : ℝ) ^ η * ((y.2 : ℕ) : ℝ) ^ η) := by
      gcongr
    _ = K * (((((y.1 : ℕ) : ℝ) ^ (2 * η)) *
          (((y.2 : ℕ) : ℝ) ^ (2 * η))) *
        hughesYoungCommonDivisorMajorant (1 + 3 * η) 1 y) := by
      have hl : 0 < (((y.1 : ℕ) : ℝ)) := by exact_mod_cast y.1.2
      have hr : 0 < (((y.2 : ℕ) : ℝ)) := by exact_mod_cast y.2.2
      rw [show (((y.1 : ℕ) : ℝ) ^ (2 * η)) =
          (((y.1 : ℕ) : ℝ) ^ η) * (((y.1 : ℕ) : ℝ) ^ η) by
        rw [← Real.rpow_add hl]; congr 1; ring]
      rw [show (((y.2 : ℕ) : ℝ) ^ (2 * η)) =
          (((y.2 : ℕ) : ℝ) ^ η) * (((y.2 : ℕ) : ℝ) ^ η) by
        rw [← Real.rpow_add hr]; congr 1; ring]
      dsimp only [K]
      ring
    _ = K * hughesYoungCommonDivisorMajorant (1 + η) (1 - 2 * η) y := by
      rw [mul_rpow_commonDivisorMajorant_eq]
      congr 2
      ring
    _ ≤ K * hughesYoungPositivePairMajorant (1 + η) (1 - 2 * η) y := by
      have hK : 0 ≤ K := by dsimp [K, D]; positivity
      exact mul_le_mul_of_nonneg_left
        (hughesYoungCommonDivisorMajorant_le_pairMajorant hA hC y) hK
    _ = _ := by rfl

theorem summable_hughesYoungEquation96VerticalTerm_mul_logSelectors_coprime
    (i j : Bool) (u : ℝ) {h k : ℕ}
    (hh : 0 < h) (hk : 0 < k) (hhk : h.Coprime k)
    {η : ℝ} (hη : 0 < η) (hη4 : η < 1 / 4) :
    Summable (fun y : ℕ+ × ℕ+ =>
      hughesYoungEquation96PositiveTerm h k 1 1
          ((2 : ℂ) + (2 * u : ℂ) * I) y *
        hughesYoungDFIPositiveLogSelectorLeft i h y *
        hughesYoungDFIPositiveLogSelectorRight j k y) := by
  let K : ℝ := (((h * k : ℕ) : ℝ) ^ (3 * η)) *
    (1 + 6 * η⁻¹ + 2 * |Real.eulerMascheroniConstant|) ^ 2 *
    ((h : ℝ) ^ η * (k : ℝ) ^ η)
  have hA : 1 < 1 + η := by linarith
  have hC : 0 < 1 - 2 * η := by linarith
  have hm : Summable (fun y : ℕ+ × ℕ+ =>
      K * hughesYoungPositivePairMajorant (1 + η) (1 - 2 * η) y) :=
    (summable_hughesYoungPositivePairMajorant hA hC).mul_left K
  exact Summable.of_norm_bounded hm fun y =>
    norm_hughesYoungEquation96VerticalTerm_mul_logSelectors_le_coprime
      i j u hh hk hhk hη hη4 y

/-- Uniform norm bound for every one of the four equation-(84) arithmetic
moments, with only an arbitrarily small power of the coprime twists. -/
theorem norm_tsum_hughesYoungEquation96VerticalTerm_mul_logSelectors_le_coprime
    (i j : Bool) (u : ℝ) {h k : ℕ}
    (hh : 0 < h) (hk : 0 < k) (hhk : h.Coprime k)
    {η : ℝ} (hη : 0 < η) (hη4 : η < 1 / 4) :
    ‖∑' y : ℕ+ × ℕ+,
        hughesYoungEquation96PositiveTerm h k 1 1
            ((2 : ℂ) + (2 * u : ℂ) * I) y *
          hughesYoungDFIPositiveLogSelectorLeft i h y *
          hughesYoungDFIPositiveLogSelectorRight j k y‖ ≤
      ((((h * k : ℕ) : ℝ) ^ (3 * η)) *
          (1 + 6 * η⁻¹ + 2 * |Real.eulerMascheroniConstant|) ^ 2 *
          ((h : ℝ) ^ η * (k : ℝ) ^ η)) *
        ∑' y : ℕ+ × ℕ+,
          hughesYoungPositivePairMajorant (1 + η) (1 - 2 * η) y := by
  let K : ℝ := (((h * k : ℕ) : ℝ) ^ (3 * η)) *
    (1 + 6 * η⁻¹ + 2 * |Real.eulerMascheroniConstant|) ^ 2 *
    ((h : ℝ) ^ η * (k : ℝ) ^ η)
  have hA : 1 < 1 + η := by linarith
  have hC : 0 < 1 - 2 * η := by linarith
  have hs := summable_hughesYoungEquation96VerticalTerm_mul_logSelectors_coprime
    i j u hh hk hhk hη hη4
  have hm : Summable (fun y : ℕ+ × ℕ+ =>
      K * hughesYoungPositivePairMajorant (1 + η) (1 - 2 * η) y) :=
    (summable_hughesYoungPositivePairMajorant hA hC).mul_left K
  calc
    _ ≤ ∑' y : ℕ+ × ℕ+,
        ‖hughesYoungEquation96PositiveTerm h k 1 1
            ((2 : ℂ) + (2 * u : ℂ) * I) y *
          hughesYoungDFIPositiveLogSelectorLeft i h y *
          hughesYoungDFIPositiveLogSelectorRight j k y‖ :=
      norm_tsum_le_tsum_norm hs.norm
    _ ≤ ∑' y : ℕ+ × ℕ+,
        K * hughesYoungPositivePairMajorant (1 + η) (1 - 2 * η) y :=
      hs.norm.tsum_le_tsum
        (fun y => norm_hughesYoungEquation96VerticalTerm_mul_logSelectors_le_coprime
          i j u hh hk hhk hη hη4 y) hm
    _ = _ := by rw [tsum_mul_left]

/-- The sharp common majorant used for all four equation-(84) moments. -/
noncomputable def hughesYoungEquation84CoprimeArithmeticMomentMajorant
    (h k : ℕ) (η : ℝ) : ℝ :=
  ((((h * k : ℕ) : ℝ) ^ (3 * η)) *
      (1 + 6 * η⁻¹ + 2 * |Real.eulerMascheroniConstant|) ^ 2 *
      ((h : ℝ) ^ η * (k : ℝ) ^ η)) *
    ∑' y : ℕ+ × ℕ+,
      hughesYoungPositivePairMajorant (1 + η) (1 - 2 * η) y

theorem norm_hughesYoungEquation84CompletePositiveMomentAt_le_coprime
    (i j : Bool) (u : ℝ) {h k : ℕ}
    (hh : 0 < h) (hk : 0 < k) (hhk : h.Coprime k)
    {η : ℝ} (hη : 0 < η) (hη4 : η < 1 / 4) :
    ‖hughesYoungEquation84CompletePositiveMomentAt h k i j u‖ ≤
      hughesYoungEquation84CoprimeArithmeticMomentMajorant h k η := by
  rw [hughesYoungEquation84CompletePositiveMomentAt_eq_equation96 i j u hhk]
  exact norm_tsum_hughesYoungEquation96VerticalTerm_mul_logSelectors_le_coprime
    j i u hh hk hhk hη hη4

end RiemannZeta.GuthMaynard
