import PublicationContract
import TaoTrudgianYang2025.LargeValueExponent

/-!
# Guth--Maynard large-value bridge

This module converts the exact large-value patterns used by
Tao--Trudgian--Yang to the publication-facing Guth--Maynard Theorem 1.1.
The conversion reflects the ordinate interval and applies a unit-modulus
coefficient twist, thereby reconciling the negative and positive phase
conventions without changing the large values or their cardinality.
-/

open Complex Finset Set

noncomputable section

namespace TaoTrudgianYang2025

/-- Reflection of the ordinate set into an interval starting at zero. -/
def LargeValuePattern.reflectedOrdinates (P : LargeValuePattern) : Finset ℝ :=
  P.ordinates.image (fun t => P.intervalRight - t)

/-- The coefficient twist which changes the reflected positive phase into
the negative phase of `LargeValuePattern`. -/
def LargeValuePattern.reflectedCoeffs (P : LargeValuePattern) (n : ℕ) : ℂ :=
  P.coeff n * (n : ℂ) ^ (-(I * (P.intervalRight : ℂ)))

theorem LargeValuePattern.indices_eq_publishedDyadicInterval
    (P : LargeValuePattern) :
    P.indices = RiemannZeta.GuthMaynard.publishedDyadicInterval P.scale := by
  ext n
  rw [P.mem_indices_iff]
  simp only [RiemannZeta.GuthMaynard.publishedDyadicInterval, Finset.mem_Icc]
  rw [P.N_eq_scale]
  norm_cast

theorem LargeValuePattern.scale_pos (P : LargeValuePattern) : 0 < P.scale := by
  have : (1 : ℝ) < (P.scale : ℝ) := by simpa [P.N_eq_scale] using P.one_lt_N
  exact_mod_cast (show (0 : ℝ) < (P.scale : ℝ) by linarith)

theorem LargeValuePattern.reflectedOrdinates_card (P : LargeValuePattern) :
    P.reflectedOrdinates.card = P.ordinates.card := by
  apply Finset.card_image_of_injective
  intro x y hxy
  linarith

theorem LargeValuePattern.reflectedOrdinates_inBaseInterval
    (P : LargeValuePattern) :
    RiemannZeta.GuthMaynard.InBaseInterval P.T P.reflectedOrdinates := by
  intro u hu
  rw [LargeValuePattern.reflectedOrdinates, Finset.mem_image] at hu
  obtain ⟨t, ht, rfl⟩ := hu
  have hit := P.ordinates_in_interval t ht
  rw [Set.mem_Icc, ← P.interval_length]
  constructor <;> linarith

theorem LargeValuePattern.reflectedOrdinates_isSeparated
    (P : LargeValuePattern) :
    RiemannZeta.GuthMaynard.IsSeparated 1 P.reflectedOrdinates := by
  intro x hx y hy hxy
  rw [LargeValuePattern.reflectedOrdinates, Finset.mem_image] at hx hy
  obtain ⟨t, ht, rfl⟩ := hx
  obtain ⟨u, hu, rfl⟩ := hy
  have htu : t ≠ u := by
    intro h
    apply hxy
    rw [h]
  have hsep := P.ordinates_oneSeparated t ht u hu htu
  rw [Real.dist_eq]
  have heq : P.intervalRight - t - (P.intervalRight - u) = u - t := by ring
  rw [heq, abs_sub_comm]
  exact hsep

theorem LargeValuePattern.norm_reflectedCoeffs
    (P : LargeValuePattern) {n : ℕ}
    (hn : n ∈ RiemannZeta.GuthMaynard.publishedDyadicInterval P.scale) :
    ‖P.reflectedCoeffs n‖ = ‖P.coeff n‖ := by
  have hnScale : P.scale ≤ n := by
    exact (Finset.mem_Icc.mp (by
      simpa [RiemannZeta.GuthMaynard.publishedDyadicInterval] using hn)).1
  have hnPos : 0 < n := lt_of_lt_of_le P.scale_pos hnScale
  rw [LargeValuePattern.reflectedCoeffs, norm_mul]
  change ‖P.coeff n‖ * ‖((n : ℝ) : ℂ) ^ (-(I * (P.intervalRight : ℂ)))‖ =
    ‖P.coeff n‖
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hnPos)]
  simp

theorem LargeValuePattern.reflectedCoeffs_one_bounded
    (P : LargeValuePattern) :
    ∀ n ∈ RiemannZeta.GuthMaynard.publishedDyadicInterval P.scale,
      ‖P.reflectedCoeffs n‖ ≤ 1 := by
  intro n hn
  rw [P.norm_reflectedCoeffs hn]
  apply P.coeff_one_bounded n
  rw [P.indices_eq_publishedDyadicInterval]
  exact hn

/-- The reflected positive-phase summand is exactly the original
negative-phase summand. -/
theorem LargeValuePattern.reflectedTerm_eq
    (P : LargeValuePattern) {n : ℕ}
    (hn : n ∈ RiemannZeta.GuthMaynard.publishedDyadicInterval P.scale)
    (t : ℝ) :
    P.reflectedCoeffs n *
        (n : ℂ) ^ (((P.intervalRight - t : ℝ) : ℂ) * I) =
      P.coeff n * dirichletPhase n t := by
  have hnScale : P.scale ≤ n := by
    exact (Finset.mem_Icc.mp (by
      simpa [RiemannZeta.GuthMaynard.publishedDyadicInterval] using hn)).1
  have hnPos : 0 < n := lt_of_lt_of_le P.scale_pos hnScale
  have hnNe : (n : ℂ) ≠ 0 := by exact_mod_cast hnPos.ne'
  rw [LargeValuePattern.reflectedCoeffs, dirichletPhase, mul_assoc,
    ← Complex.cpow_add _ _ hnNe]
  congr 2
  push_cast
  ring

/-- Exact polynomial identity implementing the phase-convention bridge. -/
theorem LargeValuePattern.reflectedPolynomial_eq
    (P : LargeValuePattern) (t : ℝ) :
    RiemannZeta.GuthMaynard.publishedSourceDirichletPoly P.scale
        P.reflectedCoeffs (P.intervalRight - t) =
      ∑ n ∈ P.indices, P.coeff n * dirichletPhase n t := by
  rw [RiemannZeta.GuthMaynard.publishedSourceDirichletPoly,
    ← P.indices_eq_publishedDyadicInterval]
  apply Finset.sum_congr rfl
  intro n hn
  apply P.reflectedTerm_eq
  rwa [← P.indices_eq_publishedDyadicInterval]

/-- Guth--Maynard Theorem 1.1 transferred verbatim to an arbitrary
`LargeValuePattern`.  This is the non-asymptotic source bridge; all three
terms and the epsilon loss remain visible. -/
theorem guthMaynard_largeValuePattern_estimate :
    ∀ ε : ℝ, 0 < ε →
      ∃ C T₀ : ℝ, 0 < C ∧ 1 ≤ T₀ ∧
        ∀ P : LargeValuePattern, T₀ ≤ P.T →
          (P.ordinates.card : ℝ) ≤ C * P.T ^ ε *
            (P.N ^ 2 * P.V ^ (-2 : ℝ) +
              P.N ^ (18 / 5 : ℝ) * P.V ^ (-4 : ℝ) +
              P.T * P.N ^ (12 / 5 : ℝ) * P.V ^ (-4 : ℝ)) := by
  intro ε hε
  obtain ⟨C, T₀, hC, hT₀, hGM⟩ :=
    RiemannZeta.GuthMaynard.guthMaynardLargeValues_published_native ε hε
  refine ⟨C, T₀, hC, hT₀, ?_⟩
  intro P hT
  have hLarge : ∀ u ∈ P.reflectedOrdinates,
      P.V ≤ ‖RiemannZeta.GuthMaynard.publishedSourceDirichletPoly P.scale
        P.reflectedCoeffs u‖ := by
    intro u hu
    rw [LargeValuePattern.reflectedOrdinates, Finset.mem_image] at hu
    obtain ⟨t, ht, rfl⟩ := hu
    rw [P.reflectedPolynomial_eq]
    exact P.large t ht
  have hBound := hGM P.scale P.V P.T P.reflectedCoeffs
    P.reflectedOrdinates P.scale_pos hT P.V_pos
    P.reflectedCoeffs_one_bounded P.reflectedOrdinates_isSeparated
    P.reflectedOrdinates_inBaseInterval hLarge
  rw [P.reflectedOrdinates_card] at hBound
  simpa [P.N_eq_scale] using hBound

/-- The three affine exponents in `guth-maynard-lvt`. -/
def guthMaynardLargeValueExponent (σ τ : ℝ) : ℝ :=
  max (2 - 2 * σ)
    (max (18 / 5 - 4 * σ) (τ + 12 / 5 - 4 * σ))

private theorem guthMaynard_terms_le
    {σ τ δ : ℝ} (hδ : 0 ≤ δ) (P : LargeValuePattern)
    (hTUpper : P.T ≤ P.N ^ (τ + δ))
    (hVLower : P.N ^ (σ - δ) ≤ P.V) :
    P.N ^ 2 * P.V ^ (-2 : ℝ) +
        P.N ^ (18 / 5 : ℝ) * P.V ^ (-4 : ℝ) +
        P.T * P.N ^ (12 / 5 : ℝ) * P.V ^ (-4 : ℝ) ≤
      3 * P.N ^ (guthMaynardLargeValueExponent σ τ + 5 * δ) := by
  have hNPos : 0 < P.N := lt_trans zero_lt_one P.one_lt_N
  have hNOne : 1 ≤ P.N := P.one_lt_N.le
  have hLowerPos : 0 < P.N ^ (σ - δ) := Real.rpow_pos_of_pos hNPos _
  have hVTwo : P.V ^ (-2 : ℝ) ≤ P.N ^ (-2 * σ + 2 * δ) := by
    calc
      P.V ^ (-2 : ℝ) ≤ (P.N ^ (σ - δ)) ^ (-2 : ℝ) :=
        Real.rpow_le_rpow_of_nonpos hLowerPos hVLower (by norm_num)
      _ = P.N ^ ((σ - δ) * (-2 : ℝ)) :=
        (Real.rpow_mul hNPos.le _ _).symm
      _ = P.N ^ (-2 * σ + 2 * δ) := by ring_nf
  have hVFour : P.V ^ (-4 : ℝ) ≤ P.N ^ (-4 * σ + 4 * δ) := by
    calc
      P.V ^ (-4 : ℝ) ≤ (P.N ^ (σ - δ)) ^ (-4 : ℝ) :=
        Real.rpow_le_rpow_of_nonpos hLowerPos hVLower (by norm_num)
      _ = P.N ^ ((σ - δ) * (-4 : ℝ)) :=
        (Real.rpow_mul hNPos.le _ _).symm
      _ = P.N ^ (-4 * σ + 4 * δ) := by ring_nf
  let B := P.N ^ (guthMaynardLargeValueExponent σ τ + 5 * δ)
  have hFirst : P.N ^ 2 * P.V ^ (-2 : ℝ) ≤ B := by
    calc
      P.N ^ 2 * P.V ^ (-2 : ℝ) ≤
          P.N ^ 2 * P.N ^ (-2 * σ + 2 * δ) := by gcongr
      _ = P.N ^ (2 - 2 * σ + 2 * δ) := by
        rw [← Real.rpow_two, ← Real.rpow_add hNPos]
        congr 1
        ring
      _ ≤ B := by
        apply Real.rpow_le_rpow_of_exponent_le hNOne
        dsimp [B, guthMaynardLargeValueExponent]
        have hmain : 2 - 2 * σ ≤
            max (2 - 2 * σ)
              (max (18 / 5 - 4 * σ) (τ + 12 / 5 - 4 * σ)) := le_max_left _ _
        linarith
  have hSecond : P.N ^ (18 / 5 : ℝ) * P.V ^ (-4 : ℝ) ≤ B := by
    calc
      P.N ^ (18 / 5 : ℝ) * P.V ^ (-4 : ℝ) ≤
          P.N ^ (18 / 5 : ℝ) * P.N ^ (-4 * σ + 4 * δ) := by gcongr
      _ = P.N ^ (18 / 5 - 4 * σ + 4 * δ) := by
        rw [← Real.rpow_add hNPos]
        congr 1
        ring
      _ ≤ B := by
        apply Real.rpow_le_rpow_of_exponent_le hNOne
        dsimp [B, guthMaynardLargeValueExponent]
        have hmain : 18 / 5 - 4 * σ ≤
            max (2 - 2 * σ)
              (max (18 / 5 - 4 * σ) (τ + 12 / 5 - 4 * σ)) :=
          le_trans (le_max_left _ _) (le_max_right _ _)
        linarith
  have hThird :
      P.T * P.N ^ (12 / 5 : ℝ) * P.V ^ (-4 : ℝ) ≤ B := by
    have hVFourNonneg : 0 ≤ P.V ^ (-4 : ℝ) := Real.rpow_nonneg P.V_pos.le _
    calc
      P.T * P.N ^ (12 / 5 : ℝ) * P.V ^ (-4 : ℝ) ≤
          P.N ^ (τ + δ) * P.N ^ (12 / 5 : ℝ) *
            P.N ^ (-4 * σ + 4 * δ) := by gcongr
      _ = P.N ^ (τ + 12 / 5 - 4 * σ + 5 * δ) := by
        rw [← Real.rpow_add hNPos, ← Real.rpow_add hNPos]
        congr 1
        ring
      _ ≤ B := by
        apply Real.rpow_le_rpow_of_exponent_le hNOne
        dsimp [B, guthMaynardLargeValueExponent]
        have hmain : τ + 12 / 5 - 4 * σ ≤
            max (2 - 2 * σ)
              (max (18 / 5 - 4 * σ) (τ + 12 / 5 - 4 * σ)) :=
          le_trans (le_max_right _ _) (le_max_right _ _)
        linarith
  calc
    P.N ^ 2 * P.V ^ (-2 : ℝ) +
          P.N ^ (18 / 5 : ℝ) * P.V ^ (-4 : ℝ) +
          P.T * P.N ^ (12 / 5 : ℝ) * P.V ^ (-4 : ℝ)
        ≤ B + B + B := add_le_add (add_le_add hFirst hSecond) hThird
    _ = 3 * B := by ring

/-- Equation `guth-maynard-lvt` in the paper's non-asymptotic large-value
interface.  The hypotheses are exactly the declared domain of `LV(σ,τ)`. -/
theorem guthMaynard_largeValueBound
    {σ τ : ℝ} (_hσLower : 1 / 2 ≤ σ) (hσUpper : σ ≤ 1) (hτ : 0 ≤ τ) :
    IsLargeValueBound σ τ (guthMaynardLargeValueExponent σ τ) := by
  intro ε hε
  let δ : ℝ := min 1 (ε / 40)
  let η : ℝ := ε / (8 * (τ + 1))
  have hτOne : 0 < τ + 1 := by linarith
  have hη : 0 < η := by
    dsimp [η]
    positivity
  have hδ : 0 < δ := by
    dsimp [δ]
    exact lt_min zero_lt_one (div_pos hε (by norm_num))
  have hδOne : δ ≤ 1 := by exact min_le_left _ _
  have hδEpsilon : δ ≤ ε / 40 := by exact min_le_right _ _
  have hηLoss : (τ + 1) * η = ε / 8 := by
    dsimp [η]
    field_simp
  have hLoss : (τ + δ) * η + 5 * δ ≤ ε := by
    have hτδ : τ + δ ≤ τ + 1 := by linarith
    have hPart : (τ + δ) * η ≤ ε / 8 := by
      calc
        (τ + δ) * η ≤ (τ + 1) * η :=
          mul_le_mul_of_nonneg_right hτδ hη.le
        _ = ε / 8 := hηLoss
    linarith
  obtain ⟨C₀, T₀, hC₀, hT₀, hRaw⟩ :=
    guthMaynard_largeValuePattern_estimate η hη
  let C : ℝ := max 1 (max (T₀ + 1) (3 * C₀))
  have hC : 1 ≤ C := le_max_left _ _
  have hCNonneg : 0 ≤ C := le_trans zero_le_one hC
  have hTConstant : T₀ + 1 ≤ C :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have hRawConstant : 3 * C₀ ≤ C :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨C, hC, δ, hδ, ?_⟩
  intro P _ _ hTUpper hVLower _
  have hNPos : 0 < P.N := lt_trans zero_lt_one P.one_lt_N
  have hNOne : 1 ≤ P.N := P.one_lt_N.le
  have hRhoNonneg : 0 ≤ guthMaynardLargeValueExponent σ τ := by
    dsimp [guthMaynardLargeValueExponent]
    have hFirst : 0 ≤ 2 - 2 * σ := by linarith
    exact le_trans hFirst (le_max_left _ _)
  have hTargetPowOne : 1 ≤
      P.N ^ (guthMaynardLargeValueExponent σ τ + ε) :=
    Real.one_le_rpow hNOne (by linarith)
  by_cases hLargeT : T₀ ≤ P.T
  · have hBound := hRaw P hLargeT
    have hTerms := guthMaynard_terms_le hδ.le P hTUpper hVLower
    have hTermsNonneg : 0 ≤
        P.N ^ 2 * P.V ^ (-2 : ℝ) +
          P.N ^ (18 / 5 : ℝ) * P.V ^ (-4 : ℝ) +
          P.T * P.N ^ (12 / 5 : ℝ) * P.V ^ (-4 : ℝ) := by
      have hVTwoNonneg : 0 ≤ P.V ^ (-2 : ℝ) :=
        Real.rpow_nonneg P.V_pos.le _
      have hVFourNonneg : 0 ≤ P.V ^ (-4 : ℝ) :=
        Real.rpow_nonneg P.V_pos.le _
      have hNTwoNonneg : 0 ≤ P.N ^ 2 := sq_nonneg P.N
      have hNEighteenNonneg : 0 ≤ P.N ^ (18 / 5 : ℝ) :=
        Real.rpow_nonneg hNPos.le _
      have hNTwelveNonneg : 0 ≤ P.N ^ (12 / 5 : ℝ) :=
        Real.rpow_nonneg hNPos.le _
      exact add_nonneg
        (add_nonneg (mul_nonneg hNTwoNonneg hVTwoNonneg)
          (mul_nonneg hNEighteenNonneg hVFourNonneg))
        (mul_nonneg (mul_nonneg P.T_pos.le hNTwelveNonneg) hVFourNonneg)
    have hTPow : P.T ^ η ≤ P.N ^ ((τ + δ) * η) := by
      calc
        P.T ^ η ≤ (P.N ^ (τ + δ)) ^ η :=
          Real.rpow_le_rpow P.T_pos.le hTUpper hη.le
        _ = P.N ^ ((τ + δ) * η) :=
          (Real.rpow_mul hNPos.le _ _).symm
    have hExponent :
        (τ + δ) * η +
            (guthMaynardLargeValueExponent σ τ + 5 * δ) ≤
          guthMaynardLargeValueExponent σ τ + ε := by
      linarith
    calc
      (P.ordinates.card : ℝ) ≤ C₀ * P.T ^ η *
          (P.N ^ 2 * P.V ^ (-2 : ℝ) +
            P.N ^ (18 / 5 : ℝ) * P.V ^ (-4 : ℝ) +
            P.T * P.N ^ (12 / 5 : ℝ) * P.V ^ (-4 : ℝ)) := hBound
      _ ≤ C₀ * P.N ^ ((τ + δ) * η) *
          (3 * P.N ^ (guthMaynardLargeValueExponent σ τ + 5 * δ)) := by
        gcongr
      _ = (3 * C₀) *
          (P.N ^ ((τ + δ) * η) *
            P.N ^ (guthMaynardLargeValueExponent σ τ + 5 * δ)) := by ring
      _ = (3 * C₀) * P.N ^
          ((τ + δ) * η +
            (guthMaynardLargeValueExponent σ τ + 5 * δ)) := by
        apply congrArg (fun x : ℝ => (3 * C₀) * x)
        exact (Real.rpow_add hNPos ((τ + δ) * η)
          (guthMaynardLargeValueExponent σ τ + 5 * δ)).symm
      _ ≤ C * P.N ^ (guthMaynardLargeValueExponent σ τ + ε) := by
        exact mul_le_mul hRawConstant
          (Real.rpow_le_rpow_of_exponent_le hNOne hExponent)
          (Real.rpow_nonneg hNPos.le _) (by positivity)
  · have hCard : (P.ordinates.card : ℝ) ≤ P.T + 1 := P.ordinate_card_cast_le
    have hSmall : P.T + 1 ≤ T₀ + 1 := by linarith
    calc
      (P.ordinates.card : ℝ) ≤ P.T + 1 := hCard
      _ ≤ T₀ + 1 := hSmall
      _ ≤ C := hTConstant
      _ ≤ C * P.N ^ (guthMaynardLargeValueExponent σ τ + ε) := by
        nlinarith

theorem largeValueExponent_le_guthMaynard
    {σ τ : ℝ} (hσLower : 1 / 2 ≤ σ) (hσUpper : σ ≤ 1) (hτ : 0 ≤ τ) :
    largeValueExponent σ τ ≤ (guthMaynardLargeValueExponent σ τ : EReal) :=
  largeValueExponent_le_of_bound
    (guthMaynard_largeValueBound hσLower hσUpper hτ)

theorem zetaLargeValueExponent_le_guthMaynard
    {σ τ : ℝ} (hσLower : 1 / 2 ≤ σ) (hσUpper : σ ≤ 1) (hτ : 0 ≤ τ) :
    zetaLargeValueExponent σ τ ≤
      (guthMaynardLargeValueExponent σ τ : EReal) :=
  zetaLargeValueExponent_le_of_bound
    (guthMaynard_largeValueBound hσLower hσUpper hτ).toZeta

end TaoTrudgianYang2025
