import RiemannZeta.GuthMaynard.NativeZeroDensity

open Complex Finset Set

namespace RiemannZeta.GuthMaynard

/-!
# Publication-facing contracts

This module freezes the statements used for release comparison with the
published Guth--Maynard paper.  The older `GuthMaynardZeroDensity` definition
is the high-range (`sigma >= 7/10`) Section 13.1 output; it is intentionally
retained as an internal interface and is not the full statement of published
Theorem 1.2.
-/

/-- Guth--Maynard Theorem 1.1 with the literal closed sum `N <= n <= 2N`,
positive phase, one-separated ordinates in `[0,T]`, and the coefficient bound
restricted to the actual support of the polynomial. -/
def PublishedGuthMaynardLargeValues : Prop :=
  ∀ (epsilon : ℝ), epsilon > 0 →
    ∃ (C T₀ : ℝ), 0 < C ∧ 1 ≤ T₀ ∧
    ∀ (N : ℕ) (V T : ℝ) (b : ℕ → ℂ) (W : Finset ℝ),
      0 < N → T₀ ≤ T → 0 < V →
      (∀ n ∈ publishedDyadicInterval N, ‖b n‖ ≤ 1) →
      IsSeparated 1 W →
      InBaseInterval T W →
      (∀ t ∈ W, V ≤ ‖publishedSourceDirichletPoly N b t‖) →
      (W.card : ℝ) ≤ C * T ^ epsilon *
        ((N : ℝ) ^ 2 * V ^ (-2 : ℝ) +
          (N : ℝ) ^ (18 / 5 : ℝ) * V ^ (-4 : ℝ) +
          T * (N : ℝ) ^ (12 / 5 : ℝ) * V ^ (-4 : ℝ))

/-- The full-range statement of Guth--Maynard Theorem 1.2. -/
def PublishedGuthMaynardZeroDensity
    (zeroCount : ℝ → ℝ → ℕ) : Prop :=
  ∀ sigma : ℝ, 1 / 2 ≤ sigma → sigma ≤ 1 →
    EpsilonPowerBound
      (fun T => (zeroCount sigma T : ℝ))
      (fun T => T ^ (15 * (1 - sigma) / (3 + 5 * sigma)))

/-- Publication-facing form of Ingham's zero-density estimate. -/
def PublishedInghamZeroDensity
    (zeroCount : ℝ → ℝ → ℕ) : Prop :=
  ∀ sigma : ℝ, 1 / 2 ≤ sigma → sigma ≤ 1 →
    EpsilonPowerBound
      (fun T => (zeroCount sigma T : ℝ))
      (fun T => T ^ (3 * (1 - sigma) / (2 - sigma)))

/-- Publication-facing form of Huxley's zero-density estimate. -/
def PublishedHuxleyZeroDensity
    (zeroCount : ℝ → ℝ → ℕ) : Prop :=
  ∀ sigma : ℝ, 3 / 4 ≤ sigma → sigma ≤ 1 →
    EpsilonPowerBound
      (fun T => (zeroCount sigma T : ℝ))
      (fun T => T ^ (3 * (1 - sigma) / (3 * sigma - 1)))

/-- Publication-facing combined `30/13` zero-density estimate. -/
def PublishedCombinedZeroDensity
    (zeroCount : ℝ → ℝ → ℕ) : Prop :=
  ∀ sigma : ℝ, 1 / 2 ≤ sigma → sigma ≤ 1 →
    EpsilonPowerBound
      (fun T => (zeroCount sigma T : ℝ))
      (fun T => T ^ (30 * (1 - sigma) / 13))

private noncomputable def restrictDyadicCoeffs
    (N : ℕ) (b : ℕ → ℂ) (n : ℕ) : ℂ :=
  if n ∈ dyadicInterval N then b n else 0

private theorem norm_restrictDyadicCoeffs_le_one
    {N : ℕ} {b : ℕ → ℂ}
    (hb : ∀ n ∈ publishedDyadicInterval N, ‖b n‖ ≤ 1) (n : ℕ) :
    ‖restrictDyadicCoeffs N b n‖ ≤ 1 := by
  by_cases hn : n ∈ dyadicInterval N
  · rw [restrictDyadicCoeffs, if_pos hn]
    apply hb n
    rw [dyadicInterval, Finset.mem_Ioc] at hn
    rw [publishedDyadicInterval, Finset.mem_Icc]
    exact ⟨hn.1.le, hn.2⟩
  · simp [restrictDyadicCoeffs, hn]

private theorem sourceDirichletPoly_restrictDyadicCoeffs
    (N : ℕ) (b : ℕ → ℂ) (t : ℝ) :
    sourceDirichletPoly N (restrictDyadicCoeffs N b) t =
      sourceDirichletPoly N b t := by
  unfold sourceDirichletPoly
  apply Finset.sum_congr rfl
  intro n hn
  simp [restrictDyadicCoeffs, hn]

/-- A one-separated finite set in `[0,T]` contains at most `floor T + 1`
points.  This is used only for the bounded-value endpoint term in the literal
closed-sum version of Theorem 1.1. -/
private theorem separated_card_le_floor_add_one
    {T : ℝ} {W : Finset ℝ}
    (hT : 0 ≤ T) (hSeparated : IsSeparated 1 W)
    (hInterval : InBaseInterval T W) :
    (W.card : ℝ) ≤ (⌊T⌋ : ℝ) + 1 := by
  have hFloorInjective : Set.InjOn (fun x : ℝ => ⌊x⌋) ↑W := by
    intro x hx y hy hxy
    by_contra hne
    have hSep := hSeparated x (by simpa using hx) y (by simpa using hy) hne
    rw [Real.dist_eq] at hSep
    have hxLower : (⌊x⌋ : ℝ) ≤ x := Int.floor_le x
    have hxUpper : x < (⌊x⌋ : ℝ) + 1 := Int.lt_floor_add_one x
    have hyLower : (⌊y⌋ : ℝ) ≤ y := Int.floor_le y
    have hyUpper : y < (⌊y⌋ : ℝ) + 1 := Int.lt_floor_add_one y
    change ⌊x⌋ = ⌊y⌋ at hxy
    rw [← hxy] at hyLower hyUpper
    have : |x - y| < 1 := by
      rw [abs_lt]
      constructor <;> linarith
    linarith
  have hCardImage : (W.image fun x : ℝ => ⌊x⌋).card = W.card := by
    exact Finset.card_image_iff.mpr hFloorInjective
  have hSubset : W.image (fun x : ℝ => ⌊x⌋) ⊆ Finset.Icc 0 ⌊T⌋ := by
    intro z hz
    rw [Finset.mem_image] at hz
    obtain ⟨x, hxW, rfl⟩ := hz
    have hx := hInterval x hxW
    rw [Set.mem_Icc] at hx
    rw [Finset.mem_Icc]
    exact ⟨Int.floor_nonneg.mpr hx.1, Int.floor_mono hx.2⟩
  have hCardNat : (W.image fun x : ℝ => ⌊x⌋).card ≤
      (Finset.Icc (0 : ℤ) ⌊T⌋).card := Finset.card_le_card hSubset
  have hFloorNonneg : (0 : ℤ) ≤ ⌊T⌋ := Int.floor_nonneg.mpr hT
  have hCardInt : (W.card : ℤ) ≤ ⌊T⌋ + 1 := by
    rw [← hCardImage]
    calc
      ((W.image fun x : ℝ => ⌊x⌋).card : ℤ) ≤
          ((Finset.Icc (0 : ℤ) ⌊T⌋).card : ℤ) := by exact_mod_cast hCardNat
      _ = ⌊T⌋ + 1 := by
        rw [Int.card_Icc_of_le]
        · ring
        · omega
  exact_mod_cast hCardInt

private theorem separated_card_le_two_mul
    {T : ℝ} {W : Finset ℝ} (hT : 1 ≤ T)
    (hSeparated : IsSeparated 1 W) (hInterval : InBaseInterval T W) :
    (W.card : ℝ) ≤ 2 * T := by
  calc
    (W.card : ℝ) ≤ (⌊T⌋ : ℝ) + 1 :=
      separated_card_le_floor_add_one (by linarith) hSeparated hInterval
    _ ≤ T + 1 := by linarith [Int.floor_le T]
    _ ≤ 2 * T := by linarith

/-- Native realization of the literal publication-facing Theorem 1.1. -/
theorem guthMaynardLargeValues_published_native :
    PublishedGuthMaynardLargeValues := by
  intro epsilon hepsilon
  obtain ⟨C₀, T₀, hC₀, hT₀, hLarge⟩ :=
    guthMaynardLargeValues_native epsilon hepsilon
  refine ⟨64 * (C₀ + 1), T₀, by positivity, hT₀, ?_⟩
  intro N V T b W hN hT hV hb hSeparated hInterval hValues
  have hTOne : 1 ≤ T := hT₀.trans hT
  have hNOne : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hTPow : 1 ≤ T ^ epsilon := Real.one_le_rpow hTOne hepsilon.le
  have hNPow : 1 ≤ (N : ℝ) ^ (12 / 5 : ℝ) := by
    exact Real.one_le_rpow hNOne (by norm_num)
  let B : ℝ :=
    (N : ℝ) ^ 2 * V ^ (-2 : ℝ) +
      (N : ℝ) ^ (18 / 5 : ℝ) * V ^ (-4 : ℝ) +
      T * (N : ℝ) ^ (12 / 5 : ℝ) * V ^ (-4 : ℝ)
  have hBNonneg : 0 ≤ B := by
    dsimp [B]
    positivity
  by_cases hVTwo : V ≤ 2
  · have hVPower : (2 : ℝ) ^ (-4 : ℝ) ≤ V ^ (-4 : ℝ) :=
      Real.rpow_le_rpow_of_nonpos hV hVTwo (by norm_num)
    have hVPowerConcrete : (1 : ℝ) / 16 ≤ V ^ (-4 : ℝ) := by
      norm_num at hVPower ⊢
      exact hVPower
    have hTTerm : T / 16 ≤
        T * (N : ℝ) ^ (12 / 5 : ℝ) * V ^ (-4 : ℝ) := by
      have hTNonneg : 0 ≤ T := by linarith
      have hTN : T ≤ T * (N : ℝ) ^ (12 / 5 : ℝ) := by
        nlinarith
      have hTNNonneg : 0 ≤ T * (N : ℝ) ^ (12 / 5 : ℝ) := by positivity
      have hInv := mul_le_mul_of_nonneg_left hVPowerConcrete hTNNonneg
      nlinarith
    have hCard : (W.card : ℝ) ≤ 2 * T :=
      separated_card_le_two_mul hTOne hSeparated hInterval
    have hBLower : T / 16 ≤ B := by
      dsimp [B]
      have hFirst : 0 ≤ (N : ℝ) ^ 2 * V ^ (-2 : ℝ) := by positivity
      have hSecond : 0 ≤ (N : ℝ) ^ (18 / 5 : ℝ) * V ^ (-4 : ℝ) := by
        positivity
      linarith
    calc
      (W.card : ℝ) ≤ 2 * T := hCard
      _ ≤ 32 * B := by nlinarith
      _ ≤ 64 * (C₀ + 1) * T ^ epsilon * B := by
        have hFactor : 32 ≤ 64 * (C₀ + 1) * T ^ epsilon := by
          nlinarith [hC₀, hTPow]
        exact mul_le_mul_of_nonneg_right hFactor hBNonneg
  · have hVTwo : 2 < V := lt_of_not_ge hVTwo
    have hValuesOpen : ∀ t ∈ W,
        V / 2 ≤ ‖sourceDirichletPoly N (restrictDyadicCoeffs N b) t‖ := by
      intro t ht
      rw [sourceDirichletPoly_restrictDyadicCoeffs]
      have hClosed := hValues t ht
      rw [publishedSourceDirichletPoly_eq_left_add] at hClosed
      have hLeft : ‖b N * (N : ℂ) ^ (t * I)‖ ≤ 1 := by
        rw [norm_mul]
        have hNMem : N ∈ publishedDyadicInterval N := by
          rw [publishedDyadicInterval, Finset.mem_Icc]
          omega
        have hbN := hb N hNMem
        have hNRealPos : (0 : ℝ) < N := by exact_mod_cast hN
        change ‖b N‖ * ‖((N : ℝ) : ℂ) ^ (t * I)‖ ≤ 1
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hNRealPos]
        simp only [mul_re, ofReal_re, I_re, ofReal_im, I_im, mul_zero,
          sub_zero, Real.rpow_zero, mul_one]
        exact hbN
      have hTriangle := norm_add_le
        (b N * (N : ℂ) ^ (t * I)) (sourceDirichletPoly N b t)
      linarith
    have hApplied := hLarge N (V / 2) T (restrictDyadicCoeffs N b) W
      hN hT (by positivity) (norm_restrictDyadicCoeffs_le_one hb)
      hSeparated hInterval hValuesOpen
    have hHalf2 : (V / 2) ^ (-2 : ℝ) = 4 * V ^ (-2 : ℝ) := by
      rw [Real.div_rpow (le_of_lt hV) (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num [Real.rpow_neg (le_of_lt hV)]
      ring
    have hHalf4 : (V / 2) ^ (-4 : ℝ) = 16 * V ^ (-4 : ℝ) := by
      rw [Real.div_rpow (le_of_lt hV) (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num [Real.rpow_neg (le_of_lt hV)]
      ring
    rw [hHalf2, hHalf4] at hApplied
    have hScaled :
        (N : ℝ) ^ 2 * (4 * V ^ (-2 : ℝ)) +
            (N : ℝ) ^ (18 / 5 : ℝ) * (16 * V ^ (-4 : ℝ)) +
            T * (N : ℝ) ^ (12 / 5 : ℝ) * (16 * V ^ (-4 : ℝ)) ≤
          16 * B := by
      dsimp [B]
      have h1 : 0 ≤ (N : ℝ) ^ 2 * V ^ (-2 : ℝ) := by positivity
      have h2 : 0 ≤ (N : ℝ) ^ (18 / 5 : ℝ) * V ^ (-4 : ℝ) := by positivity
      have h3 : 0 ≤ T * (N : ℝ) ^ (12 / 5 : ℝ) * V ^ (-4 : ℝ) := by
        positivity
      nlinarith
    calc
      (W.card : ℝ) ≤ C₀ * T ^ epsilon *
          ((N : ℝ) ^ 2 * (4 * V ^ (-2 : ℝ)) +
            (N : ℝ) ^ (18 / 5 : ℝ) * (16 * V ^ (-4 : ℝ)) +
            T * (N : ℝ) ^ (12 / 5 : ℝ) * (16 * V ^ (-4 : ℝ))) := hApplied
      _ ≤ C₀ * T ^ epsilon * (16 * B) := by
        exact mul_le_mul_of_nonneg_left hScaled
          (mul_nonneg hC₀.le (Real.rpow_nonneg (by linarith) _))
      _ ≤ 64 * (C₀ + 1) * T ^ epsilon * B := by
        have hTPowNonneg := Real.rpow_nonneg (by linarith : 0 ≤ T) epsilon
        have hCoeff : 16 * C₀ ≤ 64 * (C₀ + 1) := by nlinarith
        calc
          C₀ * T ^ epsilon * (16 * B) =
              (16 * C₀) * (T ^ epsilon * B) := by ring
          _ ≤ (64 * (C₀ + 1)) * (T ^ epsilon * B) :=
            mul_le_mul_of_nonneg_right hCoeff (mul_nonneg hTPowNonneg hBNonneg)
          _ = 64 * (C₀ + 1) * T ^ epsilon * B := by ring

/-- In the low range, Ingham's exponent is no larger than the published
Guth--Maynard exponent. -/
theorem ingham_exponent_le_guthMaynard_exponent
    {sigma : ℝ} (hHalf : 1 / 2 ≤ sigma) (hSevenTenths : sigma ≤ 7 / 10) :
    3 * (1 - sigma) / (2 - sigma) ≤
      15 * (1 - sigma) / (3 + 5 * sigma) := by
  have hLeftDen : 0 < 2 - sigma := by linarith
  have hRightDen : 0 < 3 + 5 * sigma := by linarith
  rw [div_le_div_iff₀ hLeftDen hRightDen]
  nlinarith

/-- Native realization of the full-range published Guth--Maynard Theorem 1.2. -/
theorem guthMaynardZeroDensity_published_native :
    PublishedGuthMaynardZeroDensity (fun sigma T => N sigma T) := by
  intro sigma hHalf hOne
  by_cases hLow : sigma ≤ 7 / 10
  · have hIngham := ingham_zero_density_native sigma hHalf hOne
    apply EpsilonPowerBound_mono _ _ _ hIngham
    intro T hT
    rw [abs_of_nonneg (Real.rpow_nonneg (by linarith) _),
      abs_of_nonneg (Real.rpow_nonneg (by linarith) _)]
    apply Real.rpow_le_rpow_of_exponent_le (by linarith)
    exact ingham_exponent_le_guthMaynard_exponent hHalf hLow
  · exact guthMaynardZeroDensity_native sigma (by linarith) hOne

/-- Native realization of the exact publication-facing Ingham contract. -/
theorem inghamZeroDensity_published_native :
    PublishedInghamZeroDensity (fun sigma T => N sigma T) := by
  exact ingham_zero_density_native

/-- Native realization of the exact publication-facing Huxley contract. -/
theorem huxleyZeroDensity_published_native :
    PublishedHuxleyZeroDensity (fun sigma T => N sigma T) := by
  exact huxley_zero_density_native

/-- Native realization of the exact publication-facing combined contract. -/
theorem combinedZeroDensity_published_native :
    PublishedCombinedZeroDensity (fun sigma T => N sigma T) := by
  exact combined_zero_density_native

end RiemannZeta.GuthMaynard
