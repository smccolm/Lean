import RiemannZeta.GuthMaynard.LargeValuesEnergyFinal
import RiemannZeta.GuthMaynard.LargeValuesLocalization
import RiemannZeta.GuthMaynard.ClassicalLargeValues

open Complex Finset Real
open scoped BigOperators Matrix.Norms.L2Operator

namespace RiemannZeta.GuthMaynard

/-!
# Guth--Maynard Sections 4 and 12: native large-values assembly

This file joins the source sampling matrix to the already proved first- and
third-trace Poisson formulas.  The first step below keeps the common diagonal
mass explicit; this is the quantity whose cube cancels the diagonal zero mode
in Proposition 4.6.
-/

/-- The `gmCutoffColumnMass` definition used by the source-facing construction in `LargeValuesFinal`. -/
noncomputable def gmCutoffColumnMass (cutoff : GMSmoothCutoff) (N : ℕ) : ℝ :=
  ∑ n : GMColumn N, cutoff ((n : ℝ) / N) ^ 2

theorem gmCutoffColumnMass_nonneg (cutoff : GMSmoothCutoff) (N : ℕ) :
    0 ≤ gmCutoffColumnMass cutoff N := by
  unfold gmCutoffColumnMass
  positivity

theorem gmCutoffColumnMass_le (cutoff : GMSmoothCutoff) (N : ℕ) :
    gmCutoffColumnMass cutoff N ≤ N := by
  unfold gmCutoffColumnMass
  calc
    (∑ n : GMColumn N, cutoff ((n : ℝ) / N) ^ 2) ≤
        ∑ _n : GMColumn N, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      have h0 := cutoff.nonneg ((n : ℝ) / N)
      have h1 := cutoff.bounded ((n : ℝ) / N)
      nlinarith
    _ = N := by simp [gmDyadicInterval_card]

theorem gmMatrix_first_spectral_moment_eq
    (cutoff : GMSmoothCutoff) (N : ℕ) (W : Finset ℝ) :
    (∑ i : GMRow W,
        (gmMatrix_gram_isHermitian cutoff N W).eigenvalues i) =
      (W.card : ℝ) * gmCutoffColumnMass cutoff N := by
  let H := gmMatrix_gram_isHermitian cutoff N W
  have hspectral := H.trace_eq_sum_eigenvalues
  have htrace := gmMatrix_gram_trace_eq_cutoff_sum cutoff N W
  rw [htrace] at hspectral
  apply Complex.ofReal_injective
  simpa only [gmCutoffColumnMass, Complex.ofReal_mul, Complex.ofReal_natCast,
    Complex.ofReal_sum, Complex.ofReal_pow] using hspectral.symm

theorem gmMatrix_first_spectral_moment_nonneg
    (cutoff : GMSmoothCutoff) (N : ℕ) (W : Finset ℝ) :
    0 ≤ ∑ i : GMRow W,
      (gmMatrix_gram_isHermitian cutoff N W).eigenvalues i := by
  rw [gmMatrix_first_spectral_moment_eq]
  exact mul_nonneg (Nat.cast_nonneg W.card)
    (gmCutoffColumnMass_nonneg cutoff N)

theorem gmMatrix_first_spectral_moment_le
    (cutoff : GMSmoothCutoff) (N : ℕ) (W : Finset ℝ) :
    (∑ i : GMRow W,
        (gmMatrix_gram_isHermitian cutoff N W).eigenvalues i) ≤
      (W.card : ℝ) * N := by
  rw [gmMatrix_first_spectral_moment_eq]
  exact mul_le_mul_of_nonneg_left (gmCutoffColumnMass_le cutoff N)
    (Nat.cast_nonneg W.card)

/-- The `gmCubicSpectralDispersion` definition used by the source-facing construction in `LargeValuesFinal`. -/
noncomputable def gmCubicSpectralDispersion
    (cutoff : GMSmoothCutoff) (N : ℕ) (W : Finset ℝ) : ℝ :=
  (∑ i : GMRow W,
      (gmMatrix_gram_isHermitian cutoff N W).eigenvalues i ^ 3) -
    (∑ i : GMRow W,
      (gmMatrix_gram_isHermitian cutoff N W).eigenvalues i) ^ 3 /
      (W.card : ℝ) ^ 2

theorem gmCubicSpectralDispersion_nonneg
    (cutoff : GMSmoothCutoff) (N : ℕ) (W : Finset ℝ) (hW : W.Nonempty) :
    0 ≤ gmCubicSpectralDispersion cutoff N W := by
  let s : Finset (GMRow W) := Finset.univ
  let x : GMRow W → ℝ := gmMatrixSingularValue cutoff N W
  have hs : s.Nonempty := by
    rcases hW with ⟨t, ht⟩
    exact ⟨⟨t, ht⟩, Finset.mem_univ _⟩
  have h := sixthMoment_dispersion_nonneg s x hs
  have hsquare : ∀ i : GMRow W, x i ^ 2 =
      (gmMatrix_gram_isHermitian cutoff N W).eigenvalues i := by
    intro i
    exact gmMatrixSingularValue_sq cutoff N W i
  have hsixth : ∀ i : GMRow W, x i ^ 6 =
      (gmMatrix_gram_isHermitian cutoff N W).eigenvalues i ^ 3 := by
    intro i
    exact gmMatrixSingularValue_sixth cutoff N W i
  simpa only [gmCubicSpectralDispersion, s, x, Finset.card_univ,
    Fintype.card_coe, hsquare, hsixth] using h

theorem gmCubicSpectralDispersion_le_trace_pieces
    (cutoff : GMSmoothCutoff) (N : ℕ) (hN : 0 < N)
    (W : Finset ℝ) (hW : W.Nonempty) :
    gmCubicSpectralDispersion cutoff N W ≤
      ‖gmCubicZeroMode cutoff N W - gmCubicDiagonalMain cutoff N W‖ +
      ‖gmCubicS1 cutoff N W‖ + ‖gmCubicS2 cutoff N W‖ +
      ‖gmCubicS3 cutoff N W‖ +
      ‖gmCubicDiagonalMain cutoff N W -
        (((∑ i : GMRow W,
          (gmMatrix_gram_isHermitian cutoff N W).eigenvalues i) ^ 3 /
            (W.card : ℝ) ^ 2 : ℝ) : ℂ)‖ := by
  let H := gmMatrix_gram_isHermitian cutoff N W
  let D := gmCubicSpectralDispersion cutoff N W
  let A : ℝ :=
    (∑ i : GMRow W, H.eigenvalues i) ^ 3 / (W.card : ℝ) ^ 2
  have hCube := Matrix.IsHermitian.trace_cube_eq_sum_eigenvalues_cube H
  have hSplit := gmMatrix_cubic_trace_split cutoff N hN W
  have hComplex : (D : ℂ) =
      (gmCubicZeroMode cutoff N W - gmCubicDiagonalMain cutoff N W) +
      gmCubicS1 cutoff N W + gmCubicS2 cutoff N W +
      gmCubicS3 cutoff N W +
      (gmCubicDiagonalMain cutoff N W - (A : ℂ)) := by
    dsimp only [D, gmCubicSpectralDispersion, A]
    push_cast
    rw [← hCube, hSplit]
    ring
  calc
    D = ‖(D : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (gmCubicSpectralDispersion_nonneg cutoff N W hW)]
    _ = ‖(gmCubicZeroMode cutoff N W - gmCubicDiagonalMain cutoff N W) +
          gmCubicS1 cutoff N W + gmCubicS2 cutoff N W +
          gmCubicS3 cutoff N W +
          (gmCubicDiagonalMain cutoff N W - (A : ℂ))‖ :=
      congrArg norm hComplex
    _ ≤ ‖gmCubicZeroMode cutoff N W - gmCubicDiagonalMain cutoff N W‖ +
          ‖gmCubicS1 cutoff N W‖ + ‖gmCubicS2 cutoff N W‖ +
          ‖gmCubicS3 cutoff N W‖ +
          ‖gmCubicDiagonalMain cutoff N W - (A : ℂ)‖ := by
      calc
        _ ≤ ‖(gmCubicZeroMode cutoff N W - gmCubicDiagonalMain cutoff N W) +
              gmCubicS1 cutoff N W + gmCubicS2 cutoff N W +
              gmCubicS3 cutoff N W‖ +
              ‖gmCubicDiagonalMain cutoff N W - (A : ℂ)‖ := norm_add_le _ _
        _ ≤ (‖(gmCubicZeroMode cutoff N W - gmCubicDiagonalMain cutoff N W) +
                gmCubicS1 cutoff N W + gmCubicS2 cutoff N W‖ +
                ‖gmCubicS3 cutoff N W‖) +
              ‖gmCubicDiagonalMain cutoff N W - (A : ℂ)‖ := by
          gcongr
          exact norm_add_le _ _
        _ ≤ ((‖(gmCubicZeroMode cutoff N W - gmCubicDiagonalMain cutoff N W) +
                gmCubicS1 cutoff N W‖ + ‖gmCubicS2 cutoff N W‖) +
                ‖gmCubicS3 cutoff N W‖) +
              ‖gmCubicDiagonalMain cutoff N W - (A : ℂ)‖ := by
          gcongr
          exact norm_add_le _ _
        _ ≤ (((‖gmCubicZeroMode cutoff N W - gmCubicDiagonalMain cutoff N W‖ +
                ‖gmCubicS1 cutoff N W‖) + ‖gmCubicS2 cutoff N W‖) +
                ‖gmCubicS3 cutoff N W‖) +
              ‖gmCubicDiagonalMain cutoff N W - (A : ℂ)‖ := by
          gcongr
          exact norm_add_le _ _
    _ = _ := rfl

/-- The diagonal zero mode cancels the cube of the first spectral moment.
The remaining discrepancy is uniformly bounded once the first-trace Poisson
remainder is invoked.  This is the quantitative cancellation in Proposition
4.6, not a separate estimate on either large term. -/
theorem gmCubicDiagonalMain_sub_spectralAverage_bounded
    (cutoff : GMSmoothCutoff) :
    ∃ K : ℝ, 0 < K ∧ ∀ (N : ℕ) (W : Finset ℝ),
      0 < N → (W.card : ℝ) ≤ (N : ℝ) ^ 3 → W.Nonempty →
      ‖gmCubicDiagonalMain cutoff N W -
        (((∑ i : GMRow W,
          (gmMatrix_gram_isHermitian cutoff N W).eigenvalues i) ^ 3 /
            (W.card : ℝ) ^ 2 : ℝ) : ℂ)‖ ≤ K := by
  obtain ⟨K₀, hK₀, hFirst⟩ :=
    gmMatrix_hilbertSchmidt_trace_estimate cutoff 3 2 (by norm_num)
  let L : ℝ := |gmCutoffL2Sq cutoff| + 1
  let K : ℝ := 3 * K₀ * L ^ 2 + 1
  refine ⟨K, by dsimp only [K, L]; positivity, ?_⟩
  intro N W hN hCard hW
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hnOne : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hwNat : 0 < W.card := hW.card_pos
  have hw : (0 : ℝ) < W.card := by exact_mod_cast hwNat
  have hwne : (W.card : ℝ) ≠ 0 := hw.ne'
  let t₀ : GMRow W := ⟨hW.choose, hW.choose_spec⟩
  let n₀ : GMColumn N := ⟨N + 1, by
    simp only [dyadicInterval, Finset.mem_Ioc]
    omega⟩
  letI : Nonempty (GMRow W) := ⟨t₀⟩
  letI : Nonempty (GMColumn N) := ⟨n₀⟩
  let a : ℝ := gmCutoffColumnMass cutoff N
  let b : ℝ := (N : ℝ) * gmCutoffL2Sq cutoff
  have ha0 : 0 ≤ a := by
    dsimp only [a]
    exact gmCutoffColumnMass_nonneg cutoff N
  have ha : a ≤ (N : ℝ) := by
    dsimp only [a]
    exact gmCutoffColumnMass_le cutoff N
  have hL : 1 ≤ L := by
    dsimp only [L]
    linarith [abs_nonneg (gmCutoffL2Sq cutoff)]
  have hbabs : |b| ≤ (N : ℝ) * L := by
    dsimp only [b, L]
    rw [abs_mul, abs_of_pos hn]
    exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) hn.le
  have haabs : |a| ≤ (N : ℝ) * L := by
    rw [abs_of_nonneg ha0]
    exact ha.trans (by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hL hn.le)
  have hFirstAt := hFirst N W hN hCard
  have hTraceDiff :
      (W.card : ℝ) * |a - b| ≤ K₀ / (N : ℝ) ^ 2 := by
    rw [gmMatrix_gram_trace_eq_cutoff_sum] at hFirstAt
    have hMassCast :
        (∑ n : GMColumn N,
          (cutoff ((n : ℝ) / N) ^ 2 : ℂ)) = (a : ℂ) := by
      dsimp only [a, gmCutoffColumnMass]
      push_cast
      rfl
    rw [hMassCast] at hFirstAt
    have hArg :
        (W.card : ℂ) * (a : ℂ) -
            (N : ℂ) * (W.card : ℂ) * (gmCutoffL2Sq cutoff : ℂ) =
          (((W.card : ℝ) * (a - b) : ℝ) : ℂ) := by
      dsimp only [b]
      push_cast
      ring
    rw [hArg, Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (Nat.cast_nonneg W.card)] at hFirstAt
    exact hFirstAt
  have hfactor : |b ^ 3 - a ^ 3| ≤
      |b - a| * (3 * ((N : ℝ) * L) ^ 2) := by
    rw [show b ^ 3 - a ^ 3 = (b - a) * (b ^ 2 + b * a + a ^ 2) by ring,
      abs_mul]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    have hM0 : 0 ≤ (N : ℝ) * L := mul_nonneg hn.le (zero_le_one.trans hL)
    have hb2 : |b ^ 2| ≤ ((N : ℝ) * L) ^ 2 := by
      simpa only [abs_pow] using pow_le_pow_left₀ (abs_nonneg b) hbabs 2
    have hbaMul : |b * a| ≤ ((N : ℝ) * L) ^ 2 := by
      rw [abs_mul, pow_two]
      exact mul_le_mul hbabs haabs (abs_nonneg a) hM0
    have ha2 : |a ^ 2| ≤ ((N : ℝ) * L) ^ 2 := by
      simpa only [abs_pow] using pow_le_pow_left₀ (abs_nonneg a) haabs 2
    calc
      |b ^ 2 + b * a + a ^ 2| ≤ |b ^ 2| + |b * a| + |a ^ 2| := by
        linarith [abs_add_le (b ^ 2) (b * a),
          abs_add_le (b ^ 2 + b * a) (a ^ 2)]
      _ ≤ ((N : ℝ) * L) ^ 2 + ((N : ℝ) * L) ^ 2 +
          ((N : ℝ) * L) ^ 2 := by linarith
      _ = 3 * ((N : ℝ) * L) ^ 2 := by ring
  have hExact :
      ‖gmCubicDiagonalMain cutoff N W -
        (((∑ i : GMRow W,
          (gmMatrix_gram_isHermitian cutoff N W).eigenvalues i) ^ 3 /
            (W.card : ℝ) ^ 2 : ℝ) : ℂ)‖ =
        (W.card : ℝ) * |b ^ 3 - a ^ 3| := by
    rw [gmMatrix_first_spectral_moment_eq]
    dsimp only [gmCubicDiagonalMain, a, b]
    have hInside :
        (N : ℂ) ^ 3 * (W.card : ℂ) * (gmCutoffL2Sq cutoff : ℂ) ^ 3 -
            ((((W.card : ℝ) * gmCutoffColumnMass cutoff N) ^ 3 /
              (W.card : ℝ) ^ 2 : ℝ) : ℂ) =
          (((W.card : ℝ) *
            (((N : ℝ) * gmCutoffL2Sq cutoff) ^ 3 -
              gmCutoffColumnMass cutoff N ^ 3) : ℝ) : ℂ) := by
      push_cast
      field_simp [hwne]
    rw [hInside, Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (Nat.cast_nonneg W.card)]
  rw [hExact]
  have hba : |b - a| = |a - b| := by rw [abs_sub_comm]
  calc
    (W.card : ℝ) * |b ^ 3 - a ^ 3| ≤
        (W.card : ℝ) * (|b - a| * (3 * ((N : ℝ) * L) ^ 2)) :=
      mul_le_mul_of_nonneg_left hfactor (Nat.cast_nonneg W.card)
    _ = ((W.card : ℝ) * |a - b|) *
        (3 * ((N : ℝ) * L) ^ 2) := by rw [hba]; ring
    _ ≤ (K₀ / (N : ℝ) ^ 2) * (3 * ((N : ℝ) * L) ^ 2) :=
      mul_le_mul_of_nonneg_right hTraceDiff (by positivity)
    _ = 3 * K₀ * L ^ 2 := by field_simp
    _ ≤ K := by dsimp only [K]; linarith

/-- The `gmCutoffCoeffs` definition used by the source-facing construction in `LargeValuesFinal`. -/
noncomputable def gmCutoffCoeffs (cutoff : GMSmoothCutoff) (N : ℕ)
    (b : ℕ → ℂ) (n : ℕ) : ℂ :=
  cutoff ((n : ℝ) / N) * b n

theorem sourceDirichletPoly_gmCutoffCoeffs
    (cutoff : GMSmoothCutoff) (N : ℕ) (b : ℕ → ℂ) (t : ℝ) :
    sourceDirichletPoly N (gmCutoffCoeffs cutoff N b) t =
      gmSmoothDirichletPoly cutoff N b t := by
  unfold sourceDirichletPoly gmSmoothDirichletPoly gmCutoffCoeffs
  apply Finset.sum_congr rfl
  intro n hn
  ring

theorem norm_gmCutoffCoeffs_le_one
    (cutoff : GMSmoothCutoff) (N : ℕ) (b : ℕ → ℂ)
    (hb : ∀ n ∈ dyadicInterval N, ‖b n‖ ≤ 1) :
    ∀ n ∈ dyadicInterval N, ‖gmCutoffCoeffs cutoff N b n‖ ≤ 1 := by
  intro n hn
  rw [gmCutoffCoeffs, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (cutoff.nonneg _)]
  calc
    cutoff ((n : ℝ) / N) * ‖b n‖ ≤ 1 * 1 :=
      mul_le_mul (cutoff.bounded _) (hb n hn) (norm_nonneg _) (by norm_num)
    _ = 1 := by norm_num

theorem rpow_log_div_log
    {x y : ℝ} (hx : 1 < x) (hy : 0 < y) :
    x ^ (Real.log y / Real.log x) = y := by
  rw [Real.rpow_def_of_pos (zero_lt_one.trans hx)]
  have hlog : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  rw [show Real.log x * (Real.log y / Real.log x) = Real.log y by
    field_simp]
  exact Real.exp_log hy

theorem rpow_three_sub_two_log_ratio
    {x y : ℝ} (hx : 1 < x) (hy : 0 < y) :
    x ^ (3 - 2 * (Real.log y / Real.log x)) = x ^ 3 * y ^ (-2 : ℝ) := by
  let ρ := Real.log y / Real.log x
  have hxy : x ^ ρ = y := rpow_log_div_log hx hy
  have hxpos : 0 < x := zero_lt_one.trans hx
  have hx0 : 0 ≤ x := hxpos.le
  calc
    x ^ (3 - 2 * ρ) = x ^ (3 : ℝ) / x ^ (2 * ρ) := by
      rw [Real.rpow_sub hxpos]
    _ = x ^ (3 : ℝ) / (x ^ ρ) ^ (2 : ℝ) := by
      rw [show 2 * ρ = ρ * 2 by ring, Real.rpow_mul hx0]
    _ = x ^ (3 : ℝ) / y ^ (2 : ℝ) := by rw [hxy]
    _ = x ^ (3 : ℝ) * y ^ (-2 : ℝ) := by
      rw [Real.rpow_neg hy.le]
      ring
    _ = x ^ 3 * y ^ (-2 : ℝ) := by norm_num [Real.rpow_natCast]

theorem rpow_three_halves_sub_log_ratio
    {x y : ℝ} (hx : 1 < x) (hy : 0 < y) :
    x ^ (3 / 2 - Real.log y / Real.log x) =
      x ^ (3 / 2 : ℝ) * y ^ (-1 : ℝ) := by
  let ρ := Real.log y / Real.log x
  have hxy : x ^ ρ = y := rpow_log_div_log hx hy
  have hxpos : 0 < x := zero_lt_one.trans hx
  have hx0 : 0 ≤ x := hxpos.le
  calc
    x ^ (3 / 2 - ρ) = x ^ (3 / 2 : ℝ) / x ^ ρ := by
      rw [Real.rpow_sub hxpos]
    _ = x ^ (3 / 2 : ℝ) / y := by rw [hxy]
    _ = x ^ (3 / 2 : ℝ) * y ^ (-1 : ℝ) := by
      rw [Real.rpow_neg_one]
      ring

/-- Proposition 11.2 in the matrix-facing normalization used after source
localization.  The physical threshold `V` is converted to the logarithmic
paper exponent and then converted back exactly in the conclusion. -/
theorem gmCubicS3_prop11_2_smooth
    (cutoff : GMSmoothCutoff) (ε : ℝ) (hε : 0 < ε) :
    ∃ C T₀ : ℝ, 0 < C ∧ 4096 ≤ T₀ ∧
      ∀ (N : ℕ) (T V : ℝ) (W : Finset ℝ) (b : ℕ → ℂ),
      1 < N → T₀ ≤ T → (N : ℝ) ≤ T →
      T ^ (3 / 4 : ℝ) ≤ (N : ℝ) →
      IsSeparated 1 W → InBaseInterval T W →
      (∀ n ∈ dyadicInterval N, ‖b n‖ ≤ 1) →
      0 < V →
      (∀ t ∈ W, V ≤ ‖gmSmoothDirichletPoly cutoff N b t‖) →
      ‖gmCubicS3 cutoff N W‖ ≤
        C * T ^ ε *
          (T ^ 2 * (W.card : ℝ) ^ (3 / 2 : ℝ) +
            T * (W.card : ℝ) * (N : ℝ) ^ 3 * V ^ (-2 : ℝ) +
            T * (W.card : ℝ) ^ 2 * (N : ℝ) ^ (3 / 2 : ℝ) *
              V ^ (-1 : ℝ) +
            T ^ (9 / 8 : ℝ) * (W.card : ℝ) ^ (29 / 16 : ℝ) *
              (N : ℝ) ^ (3 / 2 : ℝ) * V ^ (-1 : ℝ)) + C / T ^ 90 := by
  obtain ⟨C, T₀, hC, hT₀, hS3⟩ :=
    gmCubicS3_prop11_2_native cutoff ε hε
  refine ⟨C, T₀, hC, hT₀, ?_⟩
  intro N T V W b hN hT hNT hNscale hSep hBase hb hV hLarge
  have hNnat : 0 < N := Nat.zero_lt_of_lt hN
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN
  let ρ : ℝ := Real.log V / Real.log (N : ℝ)
  let c : ℕ → ℂ := gmCutoffCoeffs cutoff N b
  have hCoeff : ∀ n ∈ dyadicInterval N, ‖c n‖ ≤ 1 := by
    dsimp only [c]
    exact norm_gmCutoffCoeffs_le_one cutoff N b hb
  have hScale : (N : ℝ) ^ ρ = V := by
    dsimp only [ρ]
    exact rpow_log_div_log hNr hV
  have hLarge' : ∀ t ∈ W,
      (N : ℝ) ^ ρ ≤ ‖sourceDirichletPoly N c t‖ := by
    intro t ht
    rw [hScale]
    dsimp only [c]
    rw [sourceDirichletPoly_gmCutoffCoeffs]
    exact hLarge t ht
  have hs := hS3 N T ρ W c hNnat hT hNT hNscale hSep hBase hCoeff hLarge'
  rw [rpow_three_sub_two_log_ratio hNr hV,
    rpow_three_halves_sub_log_ratio hNr hV] at hs
  simpa only [ρ, mul_assoc] using hs

/-- Guth--Maynard Proposition 4.6 before the individual `S₁/S₂/S₃`
estimates are inserted.  The sampling-matrix large-value inequality and the
sixth-moment dispersion alternative are both consumed here. -/
theorem gm_largeValues_raw_dispersion
    (cutoff : GMSmoothCutoff) (N : ℕ) (W : Finset ℝ)
    (b : ℕ → ℂ) (V : ℝ)
    (hN : 0 < N) (hV : 0 < V) (hW : W.Nonempty)
    (hb : ∀ n ∈ dyadicInterval N, ‖b n‖ ≤ 1)
    (hLarge : ∀ t ∈ W, V ≤ ‖gmSmoothDirichletPoly cutoff N b t‖) :
    (W.card : ℝ) ^ 3 * V ^ 6 / (N : ℝ) ^ 3 ≤
      4 * gmCubicSpectralDispersion cutoff N W + 8 * (N : ℝ) ^ 3 := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hwNat : 0 < W.card := hW.card_pos
  have hw : (0 : ℝ) < W.card := by exact_mod_cast hwNat
  have hwne : (W.card : ℝ) ≠ 0 := hw.ne'
  have hCard := gm_largeValues_card_le_operatorNorm cutoff N W b V hV hb hLarge
  obtain ⟨j, hj⟩ := exists_gmMatrixOperatorNorm_le_singularValue cutoff N W hW
  have hOp0 : 0 ≤ gmMatrixOperatorNorm cutoff N W := by
    change 0 ≤ ‖gmMatrix cutoff N W‖
    exact norm_nonneg (gmMatrix cutoff N W)
  have hSing0 : 0 ≤ gmMatrixSingularValue cutoff N W j :=
    gmMatrixSingularValue_nonneg cutoff N W j
  have hCardCube : (W.card : ℝ) ^ 3 ≤
      ((N : ℝ) * gmMatrixOperatorNorm cutoff N W ^ 2 / V ^ 2) ^ 3 :=
    pow_le_pow_left₀ (Nat.cast_nonneg W.card) hCard 3
  have hToOp : (W.card : ℝ) ^ 3 * V ^ 6 / (N : ℝ) ^ 3 ≤
      gmMatrixOperatorNorm cutoff N W ^ 6 := by
    calc
      (W.card : ℝ) ^ 3 * V ^ 6 / (N : ℝ) ^ 3 ≤
          ((N : ℝ) * gmMatrixOperatorNorm cutoff N W ^ 2 / V ^ 2) ^ 3 *
            V ^ 6 / (N : ℝ) ^ 3 := by
        gcongr
      _ = gmMatrixOperatorNorm cutoff N W ^ 6 := by
        field_simp [hn.ne', hV.ne']
  have hOpSing : gmMatrixOperatorNorm cutoff N W ^ 6 ≤
      gmMatrixSingularValue cutoff N W j ^ 6 :=
    pow_le_pow_left₀ hOp0 hj 6
  have hDisp := gmMatrix_singularValue_sixth_le_dispersion_max cutoff N W j
  have hAverage :
      (∑ i : GMRow W,
          (gmMatrix_gram_isHermitian cutoff N W).eigenvalues i) ^ 3 /
          (W.card : ℝ) ^ 3 ≤ (N : ℝ) ^ 3 := by
    rw [gmMatrix_first_spectral_moment_eq]
    field_simp [hwne]
    exact pow_le_pow_left₀ (gmCutoffColumnMass_nonneg cutoff N)
      (gmCutoffColumnMass_le cutoff N) 3
  have hD0 := gmCubicSpectralDispersion_nonneg cutoff N W hW
  calc
    (W.card : ℝ) ^ 3 * V ^ 6 / (N : ℝ) ^ 3 ≤
        gmMatrixOperatorNorm cutoff N W ^ 6 := hToOp
    _ ≤ gmMatrixSingularValue cutoff N W j ^ 6 := hOpSing
    _ ≤ max (4 * gmCubicSpectralDispersion cutoff N W)
          (8 * (∑ i : GMRow W,
            (gmMatrix_gram_isHermitian cutoff N W).eigenvalues i) ^ 3 /
              (W.card : ℝ) ^ 3) := by
      simpa only [gmCubicSpectralDispersion] using hDisp
    _ ≤ 4 * gmCubicSpectralDispersion cutoff N W + 8 * (N : ℝ) ^ 3 := by
      apply max_le
      · exact le_add_of_nonneg_right
          (mul_nonneg (show (0 : ℝ) ≤ 8 by norm_num) (by positivity))
      · calc
          8 * (∑ i : GMRow W,
              (gmMatrix_gram_isHermitian cutoff N W).eigenvalues i) ^ 3 /
                (W.card : ℝ) ^ 3 =
              8 * ((∑ i : GMRow W,
                (gmMatrix_gram_isHermitian cutoff N W).eigenvalues i) ^ 3 /
                  (W.card : ℝ) ^ 3) := by ring
          _ ≤ 8 * (N : ℝ) ^ 3 :=
            mul_le_mul_of_nonneg_left hAverage (show (0 : ℝ) ≤ 8 by norm_num)
          _ ≤ 4 * gmCubicSpectralDispersion cutoff N W + 8 * (N : ℝ) ^ 3 :=
            le_add_of_nonneg_left (mul_nonneg (by norm_num) hD0)

/-- The `gmS3PhysicalShape` definition used by the source-facing construction in `LargeValuesFinal`. -/
noncomputable def gmS3PhysicalShape
    (N : ℕ) (T V : ℝ) (W : Finset ℝ) : ℝ :=
  T ^ 2 * (W.card : ℝ) ^ (3 / 2 : ℝ) +
    T * (W.card : ℝ) * (N : ℝ) ^ 3 * V ^ (-2 : ℝ) +
    T * (W.card : ℝ) ^ 2 * (N : ℝ) ^ (3 / 2 : ℝ) * V ^ (-1 : ℝ) +
    T ^ (9 / 8 : ℝ) * (W.card : ℝ) ^ (29 / 16 : ℝ) *
      (N : ℝ) ^ (3 / 2 : ℝ) * V ^ (-1 : ℝ)

/-- The `gmSection12RawShape` definition used by the source-facing construction in `LargeValuesFinal`. -/
noncomputable def gmSection12RawShape
    (N : ℕ) (T V : ℝ) (W : Finset ℝ) : ℝ :=
  (N : ℝ) ^ 3 + gmS2PaperShape 4 N T W +
    gmS3PhysicalShape N T V W

theorem gmS3PhysicalShape_nonneg
    {N : ℕ} {T V : ℝ} {W : Finset ℝ} (hT : 0 ≤ T) (hV : 0 ≤ V) :
    0 ≤ gmS3PhysicalShape N T V W := by
  unfold gmS3PhysicalShape
  positivity

theorem gmSection12RawShape_nonneg
    {N : ℕ} {T V : ℝ} {W : Finset ℝ} (hT : 0 ≤ T) (hV : 0 ≤ V) :
    0 ≤ gmSection12RawShape N T V W := by
  unfold gmSection12RawShape
  exact add_nonneg (add_nonneg (by positivity) (gmS2PaperShape_nonneg hT))
    (gmS3PhysicalShape_nonneg hT hV)

set_option maxHeartbeats 1000000 in
/-- The complete inequality at the start of Guth--Maynard Section 12, with
`k=4` and a physical large-value threshold.  It consumes Proposition 4.6,
Propositions 5.1, 6.1, and 11.2 in the same theorem chain. -/
theorem gmSection12_raw_smooth
    (cutoff : GMSmoothCutoff) (ε : ℝ) (hε : 0 < ε) :
    ∃ C T₀ : ℝ, 0 < C ∧ 4096 ≤ T₀ ∧
      ∀ (N : ℕ) (T V : ℝ) (W : Finset ℝ) (b : ℕ → ℂ),
      1 < N → T₀ ≤ T → (N : ℝ) ≤ T → T ≤ (N : ℝ) ^ 2 →
      T ^ (3 / 4 : ℝ) ≤ (N : ℝ) →
      IsSeparated (T ^ ε) W → InBaseInterval T W →
      (∀ n ∈ dyadicInterval N, ‖b n‖ ≤ 1) → 0 < V →
      (∀ t ∈ W, V ≤ ‖gmSmoothDirichletPoly cutoff N b t‖) →
      (W.card : ℝ) ^ 3 * V ^ 6 / (N : ℝ) ^ 3 ≤
        C * T ^ ε * gmSection12RawShape N T V W := by
  obtain ⟨Kzero, hKzero, hZero⟩ := gmCubicZeroMode_main_term cutoff ε hε
  obtain ⟨Kone, hKone, hOne⟩ := gmCubicS1_estimate cutoff ε hε
  obtain ⟨Ctwo, Ttwo, hCtwo, hTtwo, hTwo⟩ :=
    gmCubicS2_estimate cutoff (k := 4) (by norm_num) ε hε
  obtain ⟨Cthree, Tthree, hCthree, hTthree, hThree⟩ :=
    gmCubicS3_prop11_2_smooth cutoff ε hε
  obtain ⟨Kdiag, hKdiag, hDiag⟩ :=
    gmCubicDiagonalMain_sub_spectralAverage_bounded cutoff
  let T₀ := max Ttwo Tthree
  let Ksum := Kzero + Kone + Ctwo + 2 * Cthree + Kdiag
  let C := 4 * Ksum + 8 + 1
  have hKsum : 0 < Ksum := by dsimp only [Ksum]; positivity
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, T₀, hC, ?_, ?_⟩
  · exact hTthree.trans (le_max_right _ _)
  intro N T V W b hN hT hNT hTN hNscale hSep hBase hb hV hLarge
  have hNnat : 0 < N := Nat.zero_lt_of_lt hN
  have hnTwo : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hnOne : (1 : ℝ) ≤ N := one_le_two.trans hnTwo
  have hTtwoAt : Ttwo ≤ T := (le_max_left _ _).trans hT
  have hTthreeAt : Tthree ≤ T := (le_max_right _ _).trans hT
  have hTone : (1 : ℝ) ≤ T := hnOne.trans hNT
  have hTpos : 0 < T := zero_lt_one.trans_le hTone
  have hTε : 1 ≤ T ^ ε := Real.one_le_rpow hTone hε.le
  have hTε0 : 0 ≤ T ^ ε := (zero_le_one.trans hTε)
  have hSepOne : IsSeparated 1 W := by
    intro x hx y hy hxy
    exact hTε.trans (hSep x hx y hy hxy)
  by_cases hWempty : W = ∅
  · subst W
    simp [gmSection12RawShape, gmS2PaperShape, gmS2TracePaperShape,
      gmS3PhysicalShape]
    positivity
  have hW : W.Nonempty := Finset.nonempty_iff_ne_empty.mpr hWempty
  have hCardTwoT := gmSeparated_card_le_two_height hTone hSepOne hBase
  have hCardCube : (W.card : ℝ) ≤ (N : ℝ) ^ 3 := by
    calc
      (W.card : ℝ) ≤ 2 * T := hCardTwoT
      _ ≤ 2 * (N : ℝ) ^ 2 := by gcongr
      _ ≤ (N : ℝ) ^ 3 := by
        nlinarith [sq_nonneg ((N : ℝ) - 2)]
  have hRaw := gm_largeValues_raw_dispersion cutoff N W b V hNnat hV hW hb hLarge
  have hTracePieces :=
    gmCubicSpectralDispersion_le_trace_pieces cutoff N hNnat W hW
  have hzero := hZero N W hNnat hTone hNT hSep hBase
  have hone := hOne N W hNnat hnOne hTone hNT hTN hSep hBase
  have htwo := hTwo W hNnat hTtwoAt hNT hSep hBase
  have hthree := hThree N T V W b hN hTthreeAt hNT hNscale hSepOne hBase hb hV hLarge
  have hdiag := hDiag N W hNnat hCardCube hW
  let R := gmSection12RawShape N T V W
  have hR0 : 0 ≤ R := by
    dsimp only [R]
    exact gmSection12RawShape_nonneg hTpos.le hV.le
  have hRone : 1 ≤ R := by
    dsimp only [R, gmSection12RawShape]
    have hNcube : 1 ≤ (N : ℝ) ^ 3 := one_le_pow₀ hnOne
    have hS2 : 0 ≤ gmS2PaperShape 4 N T W := gmS2PaperShape_nonneg hTpos.le
    have hS3 : 0 ≤ gmS3PhysicalShape N T V W :=
      gmS3PhysicalShape_nonneg hTpos.le hV.le
    linarith
  have hS2R : gmS2PaperShape 4 N T W ≤ R := by
    dsimp only [R, gmSection12RawShape]
    have hS3 := gmS3PhysicalShape_nonneg (N := N) (V := V) (W := W)
      hTpos.le hV.le
    have hN3 : 0 ≤ (N : ℝ) ^ 3 := by positivity
    linarith
  have hS3R : gmS3PhysicalShape N T V W ≤ R := by
    dsimp only [R, gmSection12RawShape]
    have hS2 := gmS2PaperShape_nonneg (k := 4) (N := N) (W := W) hTpos.le
    have hN3 : 0 ≤ (N : ℝ) ^ 3 := by positivity
    linarith
  have hSmall (K : ℝ) (hK : 0 ≤ K) {q : ℕ} : K / T ^ q ≤ K * T ^ ε * R := by
    have hden : 1 ≤ T ^ q := one_le_pow₀ hTone
    have hdiv : K / T ^ q ≤ K := by
      exact (div_le_iff₀ (pow_pos hTpos q)).2 (by nlinarith [mul_le_mul_of_nonneg_left hden hK])
    calc
      K / T ^ q ≤ K := hdiv
      _ ≤ K * T ^ ε * R := by
        have hTRone : 1 ≤ T ^ ε * R :=
          one_le_mul_of_one_le_of_one_le hTε hRone
        calc
          K = K * 1 := by ring
          _ ≤ K * (T ^ ε * R) := mul_le_mul_of_nonneg_left hTRone hK
          _ = K * T ^ ε * R := by ring
  have hzeroR :
      ‖gmCubicZeroMode cutoff N W - gmCubicDiagonalMain cutoff N W‖ ≤
        Kzero * T ^ ε * R := hzero.trans (hSmall Kzero hKzero.le)
  have honeR : ‖gmCubicS1 cutoff N W‖ ≤ Kone * T ^ ε * R :=
    hone.trans (hSmall Kone hKone.le)
  have htwoR : ‖gmCubicS2 cutoff N W‖ ≤ Ctwo * T ^ ε * R := by
    exact htwo.trans (mul_le_mul_of_nonneg_left hS2R (by positivity))
  have hthreeR : ‖gmCubicS3 cutoff N W‖ ≤ 2 * Cthree * T ^ ε * R := by
    have htailR : Cthree / T ^ 90 ≤ Cthree * T ^ ε * R :=
      hSmall Cthree hCthree.le
    have hmainR : Cthree * T ^ ε * gmS3PhysicalShape N T V W ≤
        Cthree * T ^ ε * R := mul_le_mul_of_nonneg_left hS3R (by positivity)
    have hthree' : ‖gmCubicS3 cutoff N W‖ ≤
        Cthree * T ^ ε * gmS3PhysicalShape N T V W + Cthree / T ^ 90 := by
      simpa only [gmS3PhysicalShape] using hthree
    calc
      ‖gmCubicS3 cutoff N W‖ ≤
          Cthree * T ^ ε * gmS3PhysicalShape N T V W + Cthree / T ^ 90 := hthree'
      _ ≤ Cthree * T ^ ε * R + Cthree * T ^ ε * R :=
        add_le_add hmainR htailR
      _ = 2 * Cthree * T ^ ε * R := by ring
  have hdiagR :
      ‖gmCubicDiagonalMain cutoff N W -
        (((∑ i : GMRow W,
          (gmMatrix_gram_isHermitian cutoff N W).eigenvalues i) ^ 3 /
            (W.card : ℝ) ^ 2 : ℝ) : ℂ)‖ ≤ Kdiag * T ^ ε * R := by
    exact hdiag.trans (by
      have hKR : 1 ≤ T ^ ε * R := one_le_mul_of_one_le_of_one_le hTε hRone
      calc
        Kdiag = Kdiag * 1 := by ring
        _ ≤ Kdiag * (T ^ ε * R) := mul_le_mul_of_nonneg_left hKR hKdiag.le
        _ = Kdiag * T ^ ε * R := by ring)
  have hDispR : gmCubicSpectralDispersion cutoff N W ≤ Ksum * T ^ ε * R := by
    calc
      gmCubicSpectralDispersion cutoff N W ≤
          ‖gmCubicZeroMode cutoff N W - gmCubicDiagonalMain cutoff N W‖ +
          ‖gmCubicS1 cutoff N W‖ + ‖gmCubicS2 cutoff N W‖ +
          ‖gmCubicS3 cutoff N W‖ +
          ‖gmCubicDiagonalMain cutoff N W -
            (((∑ i : GMRow W,
              (gmMatrix_gram_isHermitian cutoff N W).eigenvalues i) ^ 3 /
                (W.card : ℝ) ^ 2 : ℝ) : ℂ)‖ := hTracePieces
      _ ≤ Kzero * T ^ ε * R + Kone * T ^ ε * R +
          Ctwo * T ^ ε * R + 2 * Cthree * T ^ ε * R +
          Kdiag * T ^ ε * R := by linarith
      _ = Ksum * T ^ ε * R := by dsimp only [Ksum]; ring
  calc
    (W.card : ℝ) ^ 3 * V ^ 6 / (N : ℝ) ^ 3 ≤
        4 * gmCubicSpectralDispersion cutoff N W + 8 * (N : ℝ) ^ 3 := hRaw
    _ ≤ 4 * (Ksum * T ^ ε * R) + 8 * (T ^ ε * R) := by
      have hNR : (N : ℝ) ^ 3 ≤ T ^ ε * R := by
        dsimp only [R, gmSection12RawShape]
        have hrest : 0 ≤ gmS2PaperShape 4 N T W + gmS3PhysicalShape N T V W := by
          exact add_nonneg (gmS2PaperShape_nonneg hTpos.le)
            (gmS3PhysicalShape_nonneg hTpos.le hV.le)
        have : (N : ℝ) ^ 3 ≤ R := by dsimp only [R, gmSection12RawShape]; linarith
        exact this.trans (by
          calc
            R = 1 * R := by ring
            _ ≤ T ^ ε * R := mul_le_mul_of_nonneg_right hTε hR0)
      gcongr
    _ ≤ C * T ^ ε * gmSection12RawShape N T V W := by
      dsimp only [C, R]
      have hTR : 0 ≤ T ^ ε * gmSection12RawShape N T V W :=
        mul_nonneg hTε0 (gmSection12RawShape_nonneg hTpos.le hV.le)
      nlinarith

/-! ## Equation (12.1): extraction of the eight Section 12 monomials -/

/-- If a positive power of `x` is bounded by `B`, taking the positive
reciprocal power gives the corresponding bound for `x`.  This is the common
algebraic step in all eight terms of Guth--Maynard equation (12.1). -/
theorem gm_rpow_root_bound
    {x B d : ℝ} (hx : 0 < x) (hd : 0 < d) (h : x ^ d ≤ B) :
    x ≤ B ^ (1 / d) := by
  have hpow := Real.rpow_le_rpow (Real.rpow_nonneg hx.le d) h (by positivity : 0 ≤ 1 / d)
  calc
    x = x ^ (1 : ℝ) := by rw [Real.rpow_one]
    _ = x ^ (d * (1 / d)) := by rw [show d * (1 / d) = 1 by field_simp]
    _ = (x ^ d) ^ (1 / d) := Real.rpow_mul hx.le d (1 / d)
    _ ≤ B ^ (1 / d) := hpow

/-- Divide a positive monomial inequality by both the physical weight and the
lower power of the cardinality, then take the remaining positive root. -/
theorem gm_solve_monomial
    {x D A E p q : ℝ}
    (hx : 0 < x) (hD : 0 < D) (hpq : 0 < p - q)
    (h : x ^ p * D ≤ A * (x ^ q * E)) :
    x ≤ (A * E / D) ^ (1 / (p - q)) := by
  have hxq : 0 < x ^ q := Real.rpow_pos_of_pos hx q
  have hp : x ^ p ≤ A * (x ^ q * E) / D := (le_div_iff₀ hD).2 h
  have hquot : x ^ p / x ^ q ≤ (A * E / D) := by
    calc
      x ^ p / x ^ q ≤ (A * (x ^ q * E) / D) / x ^ q :=
        (div_le_div_iff_of_pos_right hxq).2 hp
      _ = A * E / D := by field_simp [hxq.ne']
  apply gm_rpow_root_bound hx hpq
  simpa only [Real.rpow_sub hx p q] using hquot

/-- Eight-term finite pigeonhole in the normalization used in Section 12. -/
theorem gm_le_one_of_eight_terms
    {L A a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ : ℝ}
    (h : L ≤ A * (a₁ + a₂ + a₃ + a₄ + a₅ + a₆ + a₇ + a₈)) :
    L ≤ 8 * A * a₁ ∨ L ≤ 8 * A * a₂ ∨ L ≤ 8 * A * a₃ ∨
      L ≤ 8 * A * a₄ ∨ L ≤ 8 * A * a₅ ∨ L ≤ 8 * A * a₆ ∨
      L ≤ 8 * A * a₇ ∨ L ≤ 8 * A * a₈ := by
  by_contra hn
  push Not at hn
  rcases hn with ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈⟩
  nlinarith

theorem gm_each_le_eight_sum
    {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ : ℝ}
    (h₁ : 0 ≤ a₁) (h₂ : 0 ≤ a₂) (h₃ : 0 ≤ a₃) (h₄ : 0 ≤ a₄)
    (h₅ : 0 ≤ a₅) (h₆ : 0 ≤ a₆) (h₇ : 0 ≤ a₇) (h₈ : 0 ≤ a₈) :
    a₁ ≤ a₁ + a₂ + a₃ + a₄ + a₅ + a₆ + a₇ + a₈ ∧
    a₂ ≤ a₁ + a₂ + a₃ + a₄ + a₅ + a₆ + a₇ + a₈ ∧
    a₃ ≤ a₁ + a₂ + a₃ + a₄ + a₅ + a₆ + a₇ + a₈ ∧
    a₄ ≤ a₁ + a₂ + a₃ + a₄ + a₅ + a₆ + a₇ + a₈ ∧
    a₅ ≤ a₁ + a₂ + a₃ + a₄ + a₅ + a₆ + a₇ + a₈ ∧
    a₆ ≤ a₁ + a₂ + a₃ + a₄ + a₅ + a₆ + a₇ + a₈ ∧
    a₇ ≤ a₁ + a₂ + a₃ + a₄ + a₅ + a₆ + a₇ + a₈ ∧
    a₈ ≤ a₁ + a₂ + a₃ + a₄ + a₅ + a₆ + a₇ + a₈ := by
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem gmSection12RawShape_eq_eight
    (N : ℕ) (T V : ℝ) (W : Finset ℝ) :
    gmSection12RawShape N T V W =
      (N : ℝ) ^ 3 +
      (N : ℝ) ^ 2 * (W.card : ℝ) ^ 2 +
      T * (N : ℝ) * (W.card : ℝ) ^ (7 / 4 : ℝ) +
      (N : ℝ) ^ 2 * (W.card : ℝ) ^ (29 / 16 : ℝ) * T ^ (1 / 8 : ℝ) +
      T ^ 2 * (W.card : ℝ) ^ (3 / 2 : ℝ) +
      T * (W.card : ℝ) * (N : ℝ) ^ 3 * V ^ (-2 : ℝ) +
      T * (W.card : ℝ) ^ 2 * (N : ℝ) ^ (3 / 2 : ℝ) * V ^ (-1 : ℝ) +
      T ^ (9 / 8 : ℝ) * (W.card : ℝ) ^ (29 / 16 : ℝ) *
        (N : ℝ) ^ (3 / 2 : ℝ) * V ^ (-1 : ℝ) := by
  rw [gmSection12RawShape, gmS2PaperShape_eq]
  unfold gmS3PhysicalShape
  norm_num
  ring

/-- Equation (12.1) before distributing the physical monomials.  Each summand
is exactly the root obtained from one of the eight terms in the inequality at
the start of Section 12. -/
noncomputable def gmSection12RootShape
    (A : ℝ) (N : ℕ) (T V : ℝ) : ℝ :=
  let D := V ^ 6 / (N : ℝ) ^ 3
  ((8 * A) * (N : ℝ) ^ 3 / D) ^ (1 / 3 : ℝ) +
  ((8 * A) * (N : ℝ) ^ 2 / D) +
  ((8 * A) * (T * (N : ℝ)) / D) ^ (4 / 5 : ℝ) +
  ((8 * A) * ((N : ℝ) ^ 2 * T ^ (1 / 8 : ℝ)) / D) ^ (16 / 19 : ℝ) +
  ((8 * A) * T ^ 2 / D) ^ (2 / 3 : ℝ) +
  ((8 * A) * (T * (N : ℝ) ^ 3 * V ^ (-2 : ℝ)) / D) ^ (1 / 2 : ℝ) +
  ((8 * A) * (T * (N : ℝ) ^ (3 / 2 : ℝ) * V ^ (-1 : ℝ)) / D) +
  ((8 * A) * (T ^ (9 / 8 : ℝ) * (N : ℝ) ^ (3 / 2 : ℝ) *
    V ^ (-1 : ℝ)) / D) ^ (16 / 19 : ℝ)

theorem gmSection12_eq12_1_roots
    {A T V : ℝ} {N : ℕ} {W : Finset ℝ}
    (hA : 0 < A) (hN : 0 < N) (hT : 0 < T) (hV : 0 < V) (hW : W.Nonempty)
    (hraw : (W.card : ℝ) ^ 3 * V ^ 6 / (N : ℝ) ^ 3 ≤
      A * gmSection12RawShape N T V W) :
    (W.card : ℝ) ≤ gmSection12RootShape A N T V := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hw : (0 : ℝ) < W.card := by exact_mod_cast hW.card_pos
  let D : ℝ := V ^ 6 / (N : ℝ) ^ 3
  have hD : 0 < D := div_pos (pow_pos hV 6) (pow_pos hn 3)
  let r₁ := ((8 * A) * (N : ℝ) ^ 3 / D) ^ (1 / 3 : ℝ)
  let r₂ := ((8 * A) * (N : ℝ) ^ 2 / D)
  let r₃ := ((8 * A) * (T * (N : ℝ)) / D) ^ (4 / 5 : ℝ)
  let r₄ := ((8 * A) * ((N : ℝ) ^ 2 * T ^ (1 / 8 : ℝ)) / D) ^ (16 / 19 : ℝ)
  let r₅ := ((8 * A) * T ^ 2 / D) ^ (2 / 3 : ℝ)
  let r₆ := ((8 * A) * (T * (N : ℝ) ^ 3 * V ^ (-2 : ℝ)) / D) ^ (1 / 2 : ℝ)
  let r₇ := ((8 * A) * (T * (N : ℝ) ^ (3 / 2 : ℝ) * V ^ (-1 : ℝ)) / D)
  let r₈ := ((8 * A) * (T ^ (9 / 8 : ℝ) * (N : ℝ) ^ (3 / 2 : ℝ) *
    V ^ (-1 : ℝ)) / D) ^ (16 / 19 : ℝ)
  have hr₁ : 0 ≤ r₁ := by dsimp only [r₁]; positivity
  have hr₂ : 0 ≤ r₂ := by dsimp only [r₂]; positivity
  have hr₃ : 0 ≤ r₃ := by dsimp only [r₃]; positivity
  have hr₄ : 0 ≤ r₄ := by dsimp only [r₄]; positivity
  have hr₅ : 0 ≤ r₅ := by dsimp only [r₅]; positivity
  have hr₆ : 0 ≤ r₆ := by dsimp only [r₆]; positivity
  have hr₇ : 0 ≤ r₇ := by dsimp only [r₇]; positivity
  have hr₈ : 0 ≤ r₈ := by dsimp only [r₈]; positivity
  have hrs := gm_each_le_eight_sum hr₁ hr₂ hr₃ hr₄ hr₅ hr₆ hr₇ hr₈
  have hraw' : (W.card : ℝ) ^ 3 * D ≤ A * (
      (N : ℝ) ^ 3 +
      (N : ℝ) ^ 2 * (W.card : ℝ) ^ 2 +
      T * (N : ℝ) * (W.card : ℝ) ^ (7 / 4 : ℝ) +
      (N : ℝ) ^ 2 * (W.card : ℝ) ^ (29 / 16 : ℝ) * T ^ (1 / 8 : ℝ) +
      T ^ 2 * (W.card : ℝ) ^ (3 / 2 : ℝ) +
      T * (W.card : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ 3 * V ^ (-2 : ℝ) +
      T * (W.card : ℝ) ^ 2 * (N : ℝ) ^ (3 / 2 : ℝ) * V ^ (-1 : ℝ) +
      T ^ (9 / 8 : ℝ) * (W.card : ℝ) ^ (29 / 16 : ℝ) *
        (N : ℝ) ^ (3 / 2 : ℝ) * V ^ (-1 : ℝ)) := by
    rw [gmSection12RawShape_eq_eight] at hraw
    simpa only [D, Real.rpow_one, mul_div_assoc] using hraw
  obtain h₁ | h₂ | h₃ | h₄ | h₅ | h₆ | h₇ | h₈ :=
    gm_le_one_of_eight_terms hraw'
  · have hb := gm_solve_monomial hw hD (by norm_num : 0 < (3 : ℝ) - 0)
        (p := 3) (q := 0) (A := 8 * A) (E := (N : ℝ) ^ 3) (by
          rw [show (W.card : ℝ) ^ (3 : ℝ) = (W.card : ℝ) ^ 3 by
            exact Real.rpow_natCast _ 3]
          rw [Real.rpow_zero, one_mul]
          exact h₁)
    norm_num at hb
    change (W.card : ℝ) ≤ r₁ at hb
    change (W.card : ℝ) ≤ r₁ + r₂ + r₃ + r₄ + r₅ + r₆ + r₇ + r₈
    exact hb.trans hrs.1
  · have hb := gm_solve_monomial hw hD (by norm_num : 0 < (3 : ℝ) - 2)
        (p := 3) (q := 2) (A := 8 * A) (E := (N : ℝ) ^ 2) (by
          rw [show (W.card : ℝ) ^ (3 : ℝ) = (W.card : ℝ) ^ 3 by
            exact Real.rpow_natCast _ 3,
            show (W.card : ℝ) ^ (2 : ℝ) = (W.card : ℝ) ^ 2 by
              exact Real.rpow_natCast _ 2]
          calc
            (W.card : ℝ) ^ 3 * D ≤ 8 * A * ((N : ℝ) ^ 2 * (W.card : ℝ) ^ 2) := h₂
            _ = (8 * A) * ((W.card : ℝ) ^ 2 * (N : ℝ) ^ 2) := by ring)
    norm_num at hb
    change (W.card : ℝ) ≤ r₂ at hb
    change (W.card : ℝ) ≤ r₁ + r₂ + r₃ + r₄ + r₅ + r₆ + r₇ + r₈
    exact hb.trans hrs.2.1
  · have hb := gm_solve_monomial hw hD (by norm_num : 0 < (3 : ℝ) - 7 / 4)
        (p := 3) (q := 7 / 4) (A := 8 * A) (E := T * (N : ℝ)) (by
          rw [show (W.card : ℝ) ^ (3 : ℝ) = (W.card : ℝ) ^ 3 by
            exact Real.rpow_natCast _ 3]
          calc
            (W.card : ℝ) ^ 3 * D ≤
                8 * A * (T * (N : ℝ) * (W.card : ℝ) ^ (7 / 4 : ℝ)) := h₃
            _ = (8 * A) * ((W.card : ℝ) ^ (7 / 4 : ℝ) * (T * (N : ℝ))) := by ring)
    norm_num at hb
    change (W.card : ℝ) ≤ r₃ at hb
    change (W.card : ℝ) ≤ r₁ + r₂ + r₃ + r₄ + r₅ + r₆ + r₇ + r₈
    exact hb.trans hrs.2.2.1
  · have hb := gm_solve_monomial hw hD (by norm_num : 0 < (3 : ℝ) - 29 / 16)
        (p := 3) (q := 29 / 16) (A := 8 * A)
        (E := (N : ℝ) ^ 2 * T ^ (1 / 8 : ℝ)) (by
          rw [show (W.card : ℝ) ^ (3 : ℝ) = (W.card : ℝ) ^ 3 by
            exact Real.rpow_natCast _ 3]
          calc
            (W.card : ℝ) ^ 3 * D ≤ 8 * A *
                ((N : ℝ) ^ 2 * (W.card : ℝ) ^ (29 / 16 : ℝ) * T ^ (1 / 8 : ℝ)) := h₄
            _ = (8 * A) * ((W.card : ℝ) ^ (29 / 16 : ℝ) *
                ((N : ℝ) ^ 2 * T ^ (1 / 8 : ℝ))) := by ring)
    norm_num at hb
    change (W.card : ℝ) ≤ r₄ at hb
    change (W.card : ℝ) ≤ r₁ + r₂ + r₃ + r₄ + r₅ + r₆ + r₇ + r₈
    exact hb.trans hrs.2.2.2.1
  · have hb := gm_solve_monomial hw hD (by norm_num : 0 < (3 : ℝ) - 3 / 2)
        (p := 3) (q := 3 / 2) (A := 8 * A) (E := T ^ 2) (by
          rw [show (W.card : ℝ) ^ (3 : ℝ) = (W.card : ℝ) ^ 3 by
            exact Real.rpow_natCast _ 3]
          calc
            (W.card : ℝ) ^ 3 * D ≤ 8 * A *
                (T ^ 2 * (W.card : ℝ) ^ (3 / 2 : ℝ)) := h₅
            _ = (8 * A) * ((W.card : ℝ) ^ (3 / 2 : ℝ) * T ^ 2) := by ring)
    norm_num at hb
    change (W.card : ℝ) ≤ r₅ at hb
    change (W.card : ℝ) ≤ r₁ + r₂ + r₃ + r₄ + r₅ + r₆ + r₇ + r₈
    exact hb.trans hrs.2.2.2.2.1
  · have hb := gm_solve_monomial hw hD (by norm_num : 0 < (3 : ℝ) - 1)
        (p := 3) (q := 1) (A := 8 * A)
        (E := T * (N : ℝ) ^ 3 * V ^ (-2 : ℝ)) (by
          rw [show (W.card : ℝ) ^ (3 : ℝ) = (W.card : ℝ) ^ 3 by
            exact Real.rpow_natCast _ 3]
          calc
            (W.card : ℝ) ^ 3 * D ≤ 8 * A *
                (T * (W.card : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ 3 * V ^ (-2 : ℝ)) := h₆
            _ = (8 * A) * ((W.card : ℝ) ^ (1 : ℝ) *
                (T * (N : ℝ) ^ 3 * V ^ (-2 : ℝ))) := by ring)
    rw [show (1 : ℝ) / (3 - 1) = 1 / 2 by norm_num] at hb
    have hb' : (W.card : ℝ) ≤ r₆ := by simpa only [r₆] using hb
    change (W.card : ℝ) ≤ r₁ + r₂ + r₃ + r₄ + r₅ + r₆ + r₇ + r₈
    exact hb'.trans hrs.2.2.2.2.2.1
  · have hb := gm_solve_monomial hw hD (by norm_num : 0 < (3 : ℝ) - 2)
        (p := 3) (q := 2) (A := 8 * A)
        (E := T * (N : ℝ) ^ (3 / 2 : ℝ) * V ^ (-1 : ℝ)) (by
          rw [show (W.card : ℝ) ^ (3 : ℝ) = (W.card : ℝ) ^ 3 by
            exact Real.rpow_natCast _ 3,
            show (W.card : ℝ) ^ (2 : ℝ) = (W.card : ℝ) ^ 2 by
              exact Real.rpow_natCast _ 2]
          calc
            (W.card : ℝ) ^ 3 * D ≤ 8 * A *
                (T * (W.card : ℝ) ^ 2 * (N : ℝ) ^ (3 / 2 : ℝ) * V ^ (-1 : ℝ)) := h₇
            _ = (8 * A) * ((W.card : ℝ) ^ 2 *
                (T * (N : ℝ) ^ (3 / 2 : ℝ) * V ^ (-1 : ℝ))) := by ring)
    norm_num at hb
    change (W.card : ℝ) ≤ r₇ at hb
    change (W.card : ℝ) ≤ r₁ + r₂ + r₃ + r₄ + r₅ + r₆ + r₇ + r₈
    exact hb.trans hrs.2.2.2.2.2.2.1
  · have hb := gm_solve_monomial hw hD (by norm_num : 0 < (3 : ℝ) - 29 / 16)
        (p := 3) (q := 29 / 16) (A := 8 * A)
        (E := T ^ (9 / 8 : ℝ) * (N : ℝ) ^ (3 / 2 : ℝ) *
          V ^ (-1 : ℝ)) (by
            rw [show (W.card : ℝ) ^ (3 : ℝ) = (W.card : ℝ) ^ 3 by
              exact Real.rpow_natCast _ 3]
            calc
              (W.card : ℝ) ^ 3 * D ≤ 8 * A *
                  (T ^ (9 / 8 : ℝ) * (W.card : ℝ) ^ (29 / 16 : ℝ) *
                    (N : ℝ) ^ (3 / 2 : ℝ) * V ^ (-1 : ℝ)) := h₈
              _ = (8 * A) * ((W.card : ℝ) ^ (29 / 16 : ℝ) *
                  (T ^ (9 / 8 : ℝ) * (N : ℝ) ^ (3 / 2 : ℝ) *
                    V ^ (-1 : ℝ))) := by ring)
    norm_num at hb
    change (W.card : ℝ) ≤ r₈ at hb
    change (W.card : ℝ) ≤ r₁ + r₂ + r₃ + r₄ + r₅ + r₆ + r₇ + r₈
    exact hb.trans hrs.2.2.2.2.2.2.2

/-- The eight physical roots in equation (12.1), with the common analytic
the constant removed. -/
noncomputable def gmEquation12PhysicalRootShape
    (N : ℕ) (T V : ℝ) : ℝ :=
  let D := V ^ 6 / (N : ℝ) ^ 3
  ((N : ℝ) ^ 3 / D) ^ (1 / 3 : ℝ) +
  ((N : ℝ) ^ 2 / D) +
  ((T * (N : ℝ)) / D) ^ (4 / 5 : ℝ) +
  (((N : ℝ) ^ 2 * T ^ (1 / 8 : ℝ)) / D) ^ (16 / 19 : ℝ) +
  (T ^ 2 / D) ^ (2 / 3 : ℝ) +
  ((T * (N : ℝ) ^ 3 * V ^ (-2 : ℝ)) / D) ^ (1 / 2 : ℝ) +
  ((T * (N : ℝ) ^ (3 / 2 : ℝ) * V ^ (-1 : ℝ)) / D) +
  ((T ^ (9 / 8 : ℝ) * (N : ℝ) ^ (3 / 2 : ℝ) *
    V ^ (-1 : ℝ)) / D) ^ (16 / 19 : ℝ)

theorem gm_mul_rpow_le_mul
    {B Q r : ℝ} (hB : 1 ≤ B) (hQ : 0 ≤ Q) (hr₁ : r ≤ 1) :
    (B * Q) ^ r ≤ B * Q ^ r := by
  rw [Real.mul_rpow (zero_le_one.trans hB) hQ]
  gcongr
  calc
    B ^ r ≤ B ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hB hr₁
    _ = B := Real.rpow_one B

theorem gmSection12RootShape_le_physical
    {A T V : ℝ} {N : ℕ}
    (hA : 1 ≤ A) (hN : 0 < N) (hT : 0 < T) (hV : 0 < V) :
    gmSection12RootShape A N T V ≤
      8 * A * gmEquation12PhysicalRootShape N T V := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  let D : ℝ := V ^ 6 / (N : ℝ) ^ 3
  have hD : 0 < D := div_pos (pow_pos hV 6) (pow_pos hn 3)
  have hB : 1 ≤ 8 * A := by nlinarith
  let q₁ := (N : ℝ) ^ 3 / D
  let q₂ := (N : ℝ) ^ 2 / D
  let q₃ := (T * (N : ℝ)) / D
  let q₄ := ((N : ℝ) ^ 2 * T ^ (1 / 8 : ℝ)) / D
  let q₅ := T ^ 2 / D
  let q₆ := (T * (N : ℝ) ^ 3 * V ^ (-2 : ℝ)) / D
  let q₇ := (T * (N : ℝ) ^ (3 / 2 : ℝ) * V ^ (-1 : ℝ)) / D
  let q₈ := (T ^ (9 / 8 : ℝ) * (N : ℝ) ^ (3 / 2 : ℝ) *
    V ^ (-1 : ℝ)) / D
  have hq₁ : 0 ≤ q₁ := by dsimp only [q₁]; positivity
  have hq₂ : 0 ≤ q₂ := by dsimp only [q₂]; positivity
  have hq₃ : 0 ≤ q₃ := by dsimp only [q₃]; positivity
  have hq₄ : 0 ≤ q₄ := by dsimp only [q₄]; positivity
  have hq₅ : 0 ≤ q₅ := by dsimp only [q₅]; positivity
  have hq₆ : 0 ≤ q₆ := by dsimp only [q₆]; positivity
  have hq₇ : 0 ≤ q₇ := by dsimp only [q₇]; positivity
  have hq₈ : 0 ≤ q₈ := by dsimp only [q₈]; positivity
  have e₁ : ((8 * A) * (N : ℝ) ^ 3 / D) ^ (1 / 3 : ℝ) ≤
      8 * A * q₁ ^ (1 / 3 : ℝ) := by
    rw [show (8 * A) * (N : ℝ) ^ 3 / D = (8 * A) * q₁ by dsimp [q₁]; ring]
    exact gm_mul_rpow_le_mul hB hq₁ (by norm_num)
  have e₂ : (8 * A) * (N : ℝ) ^ 2 / D ≤ 8 * A * q₂ := by
    dsimp only [q₂]
    ring_nf
    exact le_rfl
  have e₃ : ((8 * A) * (T * (N : ℝ)) / D) ^ (4 / 5 : ℝ) ≤
      8 * A * q₃ ^ (4 / 5 : ℝ) := by
    rw [show (8 * A) * (T * (N : ℝ)) / D = (8 * A) * q₃ by dsimp [q₃]; ring]
    exact gm_mul_rpow_le_mul hB hq₃ (by norm_num)
  have e₄ : ((8 * A) * ((N : ℝ) ^ 2 * T ^ (1 / 8 : ℝ)) / D) ^
      (16 / 19 : ℝ) ≤ 8 * A * q₄ ^ (16 / 19 : ℝ) := by
    rw [show (8 * A) * ((N : ℝ) ^ 2 * T ^ (1 / 8 : ℝ)) / D =
      (8 * A) * q₄ by dsimp [q₄]; ring]
    exact gm_mul_rpow_le_mul hB hq₄ (by norm_num)
  have e₅ : ((8 * A) * T ^ 2 / D) ^ (2 / 3 : ℝ) ≤
      8 * A * q₅ ^ (2 / 3 : ℝ) := by
    rw [show (8 * A) * T ^ 2 / D = (8 * A) * q₅ by dsimp [q₅]; ring]
    exact gm_mul_rpow_le_mul hB hq₅ (by norm_num)
  have e₆ : ((8 * A) * (T * (N : ℝ) ^ 3 * V ^ (-2 : ℝ)) / D) ^
      (1 / 2 : ℝ) ≤ 8 * A * q₆ ^ (1 / 2 : ℝ) := by
    rw [show (8 * A) * (T * (N : ℝ) ^ 3 * V ^ (-2 : ℝ)) / D =
      (8 * A) * q₆ by dsimp [q₆]; ring]
    exact gm_mul_rpow_le_mul hB hq₆ (by norm_num)
  have e₇ : (8 * A) * (T * (N : ℝ) ^ (3 / 2 : ℝ) * V ^ (-1 : ℝ)) / D ≤
      8 * A * q₇ := by
    dsimp only [q₇]
    ring_nf
    exact le_rfl
  have e₈ : ((8 * A) * (T ^ (9 / 8 : ℝ) * (N : ℝ) ^ (3 / 2 : ℝ) *
      V ^ (-1 : ℝ)) / D) ^ (16 / 19 : ℝ) ≤
      8 * A * q₈ ^ (16 / 19 : ℝ) := by
    rw [show (8 * A) * (T ^ (9 / 8 : ℝ) * (N : ℝ) ^ (3 / 2 : ℝ) *
      V ^ (-1 : ℝ)) / D = (8 * A) * q₈ by dsimp [q₈]; ring]
    exact gm_mul_rpow_le_mul hB hq₈ (by norm_num)
  dsimp only [gmSection12RootShape, gmEquation12PhysicalRootShape, D]
  dsimp only [q₁, q₂, q₃, q₄, q₅, q₆, q₇, q₈] at e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈
  calc
    _ ≤ 8 * A * ((N : ℝ) ^ 3 / D) ^ (1 / 3 : ℝ) +
        8 * A * ((N : ℝ) ^ 2 / D) +
        8 * A * ((T * (N : ℝ)) / D) ^ (4 / 5 : ℝ) +
        8 * A * (((N : ℝ) ^ 2 * T ^ (1 / 8 : ℝ)) / D) ^ (16 / 19 : ℝ) +
        8 * A * (T ^ 2 / D) ^ (2 / 3 : ℝ) +
        8 * A * ((T * (N : ℝ) ^ 3 * V ^ (-2 : ℝ)) / D) ^ (1 / 2 : ℝ) +
        8 * A * ((T * (N : ℝ) ^ (3 / 2 : ℝ) * V ^ (-1 : ℝ)) / D) +
        8 * A * ((T ^ (9 / 8 : ℝ) * (N : ℝ) ^ (3 / 2 : ℝ) *
          V ^ (-1 : ℝ)) / D) ^ (16 / 19 : ℝ) := by gcongr
    _ = _ := by ring

set_option maxHeartbeats 1000000 in
/-- Guth--Maynard equation (12.1) in its exact eight-root physical form.  This
theorem is a direct consumer of the complete Section 12 trace inequality. -/
theorem gmSection12_equation12_1_smooth
    (cutoff : GMSmoothCutoff) (ε : ℝ) (hε : 0 < ε) :
    ∃ C T₀ : ℝ, 0 < C ∧ 4096 ≤ T₀ ∧
      ∀ (N : ℕ) (T V : ℝ) (W : Finset ℝ) (b : ℕ → ℂ),
      1 < N → T₀ ≤ T → (N : ℝ) ≤ T → T ≤ (N : ℝ) ^ 2 →
      T ^ (3 / 4 : ℝ) ≤ (N : ℝ) →
      IsSeparated (T ^ ε) W → InBaseInterval T W →
      (∀ n ∈ dyadicInterval N, ‖b n‖ ≤ 1) → 0 < V →
      (∀ t ∈ W, V ≤ ‖gmSmoothDirichletPoly cutoff N b t‖) →
      (W.card : ℝ) ≤ C * T ^ ε * gmEquation12PhysicalRootShape N T V := by
  obtain ⟨C₀, T₀, hC₀, hT₀, hraw⟩ := gmSection12_raw_smooth cutoff ε hε
  let C := 8 * (C₀ + 1)
  refine ⟨C, T₀, by dsimp only [C]; positivity, hT₀, ?_⟩
  intro N T V W b hN hT hNT hTN hScale hSep hBase hb hV hLarge
  have hNnat : 0 < N := Nat.zero_lt_of_lt hN
  have hnOne : (1 : ℝ) ≤ N := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hNnat.ne')
  have hTone : (1 : ℝ) ≤ T := hnOne.trans hNT
  have hTpos : 0 < T := zero_lt_one.trans_le hTone
  have hTε : 1 ≤ T ^ ε := Real.one_le_rpow hTone hε.le
  by_cases hWe : W = ∅
  · subst W
    simp
    exact mul_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg hTpos.le ε))
      (by unfold gmEquation12PhysicalRootShape; positivity)
  have hW : W.Nonempty := Finset.nonempty_iff_ne_empty.mpr hWe
  have hraw₀ := hraw N T V W b hN hT hNT hTN hScale hSep hBase hb hV hLarge
  let A := (C₀ + 1) * T ^ ε
  have hAone : 1 ≤ A := by
    dsimp only [A]
    have hCone : 1 ≤ C₀ + 1 := by linarith
    exact one_le_mul_of_one_le_of_one_le hCone hTε
  have hshape₀ : 0 ≤ gmSection12RawShape N T V W :=
    gmSection12RawShape_nonneg hTpos.le hV.le
  have hrawA : (W.card : ℝ) ^ 3 * V ^ 6 / (N : ℝ) ^ 3 ≤
      A * gmSection12RawShape N T V W := by
    calc
      _ ≤ C₀ * T ^ ε * gmSection12RawShape N T V W := hraw₀
      _ ≤ A * gmSection12RawShape N T V W := by
        apply mul_le_mul_of_nonneg_right _ hshape₀
        dsimp only [A]
        have hTε0 : 0 ≤ T ^ ε := Real.rpow_nonneg hTpos.le ε
        nlinarith
  have hroot := gmSection12_eq12_1_roots (zero_lt_one.trans_le hAone) hNnat hTpos hV hW hrawA
  have hphysical := gmSection12RootShape_le_physical hAone hNnat hTpos hV
  calc
    (W.card : ℝ) ≤ gmSection12RootShape A N T V := hroot
    _ ≤ 8 * A * gmEquation12PhysicalRootShape N T V := hphysical
    _ = C * T ^ ε * gmEquation12PhysicalRootShape N T V := by
      dsimp only [A, C]
      ring

theorem gm_rpow_div_root
    {x a b c : ℝ} (hx : 0 < x) :
    (x ^ a / x ^ b) ^ c = x ^ ((a - b) * c) := by
  rw [← Real.rpow_sub hx a b]
  exact (Real.rpow_mul hx.le (a - b) c).symm

/-- Exact substitution `T=N^(6/5)`, `V=N^σ` into the eight roots of
equation (12.1). -/
theorem gmEquation12PhysicalRootShape_specialize
    {N : ℕ} { σ : ℝ} (hN : 0 < N) :
    gmEquation12PhysicalRootShape N ((N : ℝ) ^ (6 / 5 : ℝ)) ((N : ℝ) ^ σ) =
      (N : ℝ) ^ (2 - 2 * σ) +
      (N : ℝ) ^ (5 - 6 * σ) +
      (N : ℝ) ^ (104 / 25 - 24 * σ / 5) +
      (N : ℝ) ^ (412 / 95 - 96 * σ / 19) +
      (N : ℝ) ^ (18 / 5 - 4 * σ) +
      (N : ℝ) ^ (18 / 5 - 4 * σ) +
      (N : ℝ) ^ (57 / 10 - 7 * σ) +
      (N : ℝ) ^ (468 / 95 - 112 * σ / 19) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  let x : ℝ := N
  have hx : 0 < x := by simpa only [x] using hn
  have hD : (x ^ σ) ^ 6 / x ^ 3 = x ^ (6 * σ - 3) := by
    rw [← Real.rpow_natCast (x ^ σ) 6, ← Real.rpow_mul hx.le]
    rw [← Real.rpow_natCast x 3, ← Real.rpow_sub hx]
    congr 1
    ring
  have hp3 : x ^ 3 = x ^ (3 : ℝ) := (Real.rpow_natCast x 3).symm
  have hp2 : x ^ 2 = x ^ (2 : ℝ) := (Real.rpow_natCast x 2).symm
  have hn3 : x ^ (6 / 5 : ℝ) * x = x ^ (11 / 5 : ℝ) := by
    calc
      x ^ (6 / 5 : ℝ) * x = x ^ (6 / 5 : ℝ) * x ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = x ^ ((6 / 5 : ℝ) + 1) := (Real.rpow_add hx _ _).symm
      _ = x ^ (11 / 5 : ℝ) := by
        congr 1
        ring
  have hn4 : x ^ 2 * (x ^ (6 / 5 : ℝ)) ^ (1 / 8 : ℝ) =
      x ^ (43 / 20 : ℝ) := by
    rw [hp2, ← Real.rpow_mul hx.le, ← Real.rpow_add hx]
    congr 1
    ring
  have hn5 : (x ^ (6 / 5 : ℝ)) ^ 2 = x ^ (12 / 5 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]
    congr 1
    ring
  have hn6 : x ^ (6 / 5 : ℝ) * x ^ 3 * (x ^ σ) ^ (-2 : ℝ) =
      x ^ (21 / 5 - 2 * σ) := by
    rw [hp3, ← Real.rpow_mul hx.le, ← Real.rpow_add hx, ← Real.rpow_add hx]
    congr 1
    ring
  have hn7 : x ^ (6 / 5 : ℝ) * x ^ (3 / 2 : ℝ) * (x ^ σ) ^ (-1 : ℝ) =
      x ^ (27 / 10 - σ) := by
    rw [← Real.rpow_mul hx.le, ← Real.rpow_add hx, ← Real.rpow_add hx]
    congr 1
    ring
  have hn8 : (x ^ (6 / 5 : ℝ)) ^ (9 / 8 : ℝ) * x ^ (3 / 2 : ℝ) *
      (x ^ σ) ^ (-1 : ℝ) = x ^ (57 / 20 - σ) := by
    rw [← Real.rpow_mul hx.le, ← Real.rpow_mul hx.le, ← Real.rpow_add hx,
      ← Real.rpow_add hx]
    congr 1
    ring
  dsimp only [x] at hx hp3 hp2 hn3 hn4 hn5 hn6 hn7 hn8
  unfold gmEquation12PhysicalRootShape
  dsimp only
  rw [show ((N : ℝ) ^ σ) ^ 6 / (N : ℝ) ^ 3 =
    (N : ℝ) ^ (6 * σ - 3) by simpa only [x] using hD]
  rw [hn3, hn4, hn5, hn6, hn7, hn8, hp3, hp2]
  rw [gm_rpow_div_root hx, gm_rpow_div_root hx, gm_rpow_div_root hx,
    gm_rpow_div_root hx, gm_rpow_div_root hx, gm_rpow_div_root hx,
    ← Real.rpow_sub hx, ← Real.rpow_sub hx]
  congr 1 <;> ring_nf

theorem gmEquation12PhysicalRootShape_specialize_le
    {N : ℕ} {σ : ℝ} (hN : 1 < N) (hσL : 7 / 10 ≤ σ) (hσU : σ ≤ 4 / 5) :
    gmEquation12PhysicalRootShape N ((N : ℝ) ^ (6 / 5 : ℝ)) ((N : ℝ) ^ σ) ≤
      8 * (N : ℝ) ^ (18 / 5 - 4 * σ) := by
  rw [gmEquation12PhysicalRootShape_specialize (Nat.zero_lt_of_lt hN)]
  have hnOne : (1 : ℝ) ≤ N := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.zero_lt_of_lt hN).ne')
  let E : ℝ := 18 / 5 - 4 * σ
  have h₁ : (N : ℝ) ^ (2 - 2 * σ) ≤ (N : ℝ) ^ E := by
    apply Real.rpow_le_rpow_of_exponent_le hnOne
    dsimp only [E]
    linarith
  have h₂ : (N : ℝ) ^ (5 - 6 * σ) ≤ (N : ℝ) ^ E := by
    apply Real.rpow_le_rpow_of_exponent_le hnOne
    dsimp only [E]
    linarith
  have h₃ : (N : ℝ) ^ (104 / 25 - 24 * σ / 5) ≤ (N : ℝ) ^ E := by
    apply Real.rpow_le_rpow_of_exponent_le hnOne
    dsimp only [E]
    linarith
  have h₄ : (N : ℝ) ^ (412 / 95 - 96 * σ / 19) ≤ (N : ℝ) ^ E := by
    apply Real.rpow_le_rpow_of_exponent_le hnOne
    dsimp only [E]
    linarith
  have h₇ : (N : ℝ) ^ (57 / 10 - 7 * σ) ≤ (N : ℝ) ^ E := by
    apply Real.rpow_le_rpow_of_exponent_le hnOne
    dsimp only [E]
    linarith
  have h₈ : (N : ℝ) ^ (468 / 95 - 112 * σ / 19) ≤ (N : ℝ) ^ E := by
    apply Real.rpow_le_rpow_of_exponent_le hnOne
    dsimp only [E]
    linarith
  dsimp only [E] at h₁ h₂ h₃ h₄ h₇ h₈ ⊢
  nlinarith

set_option maxHeartbeats 1000000 in
/-- Guth--Maynard Proposition 3.1 for the localized smooth polynomial.  The
proof specializes equation (12.1) with `k=4` and `T=N^(6/5)`. -/
theorem gmProposition3_1_smooth
    (cutoff : GMSmoothCutoff) (ε : ℝ) (hε : 0 < ε) :
    ∃ C T₀ : ℝ, 0 < C ∧ 4096 ≤ T₀ ∧
      ∀ (N : ℕ) (σ : ℝ) (W : Finset ℝ) (b : ℕ → ℂ),
      1 < N → T₀ ≤ (N : ℝ) ^ (6 / 5 : ℝ) →
      7 / 10 ≤ σ → σ ≤ 4 / 5 →
      IsSeparated (((N : ℝ) ^ (6 / 5 : ℝ)) ^ ε) W →
      InBaseInterval ((N : ℝ) ^ (6 / 5 : ℝ)) W →
      (∀ n ∈ dyadicInterval N, ‖b n‖ ≤ 1) →
      (∀ t ∈ W, (N : ℝ) ^ σ ≤ ‖gmSmoothDirichletPoly cutoff N b t‖) →
      (W.card : ℝ) ≤
        C * ((N : ℝ) ^ (6 / 5 : ℝ)) ^ ε *
          ((N : ℝ) ^ (6 / 5 : ℝ) * (N : ℝ) ^ ((12 - 20 * σ) / 5)) := by
  obtain ⟨C₀, T₀, hC₀, hT₀, hEq⟩ := gmSection12_equation12_1_smooth cutoff ε hε
  let C := 8 * C₀
  refine ⟨C, T₀, by dsimp only [C]; positivity, hT₀, ?_⟩
  intro N σ W b hN hT hσL hσU hSep hBase hb hLarge
  have hNnat : 0 < N := Nat.zero_lt_of_lt hN
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hNnat.ne')
  have hnpos : (0 : ℝ) < N := zero_lt_one.trans_le hn
  let T : ℝ := (N : ℝ) ^ (6 / 5 : ℝ)
  let V : ℝ := (N : ℝ) ^ σ
  have hTpos : 0 < T := Real.rpow_pos_of_pos hnpos _
  have hVpos : 0 < V := Real.rpow_pos_of_pos hnpos _
  have hNT : (N : ℝ) ≤ T := by
    dsimp only [T]
    simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_le hn (show (1 : ℝ) ≤ 6 / 5 by norm_num))
  have hTN : T ≤ (N : ℝ) ^ 2 := by
    dsimp only [T]
    calc
      (N : ℝ) ^ (6 / 5 : ℝ) ≤ (N : ℝ) ^ (2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hn (by norm_num)
      _ = (N : ℝ) ^ 2 := Real.rpow_natCast _ 2
  have hScale : T ^ (3 / 4 : ℝ) ≤ (N : ℝ) := by
    dsimp only [T]
    calc
      ((N : ℝ) ^ (6 / 5 : ℝ)) ^ (3 / 4 : ℝ) =
          (N : ℝ) ^ ((6 / 5 : ℝ) * (3 / 4 : ℝ)) :=
        (Real.rpow_mul hnpos.le _ _).symm
      _ ≤ (N : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hn (by norm_num)
      _ = (N : ℝ) := Real.rpow_one _
  have hcard := hEq N T V W b hN hT hNT hTN hScale hSep hBase hb hVpos hLarge
  have hshape := gmEquation12PhysicalRootShape_specialize_le hN hσL hσU
  have htarget : (N : ℝ) ^ (18 / 5 - 4 * σ) =
      (N : ℝ) ^ (6 / 5 : ℝ) * (N : ℝ) ^ ((12 - 20 * σ) / 5) := by
    rw [← Real.rpow_add hnpos]
    congr 1
    ring
  calc
    (W.card : ℝ) ≤ C₀ * T ^ ε * gmEquation12PhysicalRootShape N T V := hcard
    _ ≤ C₀ * T ^ ε * (8 * (N : ℝ) ^ (18 / 5 - 4 * σ)) := by
      gcongr
    _ = C * ((N : ℝ) ^ (6 / 5 : ℝ)) ^ ε *
        ((N : ℝ) ^ (6 / 5 : ℝ) * (N : ℝ) ^ ((12 - 20 * σ) / 5)) := by
      rw [htarget]
      dsimp only [C, T]
      ring

set_option maxHeartbeats 1000000 in
/-- Physical-threshold form of Guth--Maynard Proposition 3.1.  This is the
form needed after source localization: the large-value threshold is an
arbitrary `V` in the critical range, rather than a separately supplied
logarithmic exponent. -/
theorem gmProposition3_1_smooth_physical
    (cutoff : GMSmoothCutoff) (ε : ℝ) (hε : 0 < ε) :
    ∃ C T₀ : ℝ, 0 < C ∧ 4096 ≤ T₀ ∧
      ∀ (N : ℕ) (V : ℝ) (W : Finset ℝ) (b : ℕ → ℂ),
      1 < N → T₀ ≤ (N : ℝ) ^ (6 / 5 : ℝ) → 0 < V →
      (N : ℝ) ^ (7 / 10 : ℝ) ≤ V → V ≤ (N : ℝ) ^ (4 / 5 : ℝ) →
      IsSeparated (((N : ℝ) ^ (6 / 5 : ℝ)) ^ ε) W →
      InBaseInterval ((N : ℝ) ^ (6 / 5 : ℝ)) W →
      (∀ n ∈ dyadicInterval N, ‖b n‖ ≤ 1) →
      (∀ t ∈ W, V ≤ ‖gmSmoothDirichletPoly cutoff N b t‖) →
      (W.card : ℝ) ≤
        C * ((N : ℝ) ^ (6 / 5 : ℝ)) ^ ε *
          ((N : ℝ) ^ (6 / 5 : ℝ) * (N : ℝ) ^ (12 / 5 : ℝ) *
            V ^ (-4 : ℝ)) := by
  obtain ⟨C, T₀, hC, hT₀, hProp⟩ := gmProposition3_1_smooth cutoff ε hε
  refine ⟨C, T₀, hC, hT₀, ?_⟩
  intro N V W b hN hT hV hVL hVU hSep hBase hb hLarge
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_lt_of_lt hN)
  have hNone : (1 : ℝ) < N := by exact_mod_cast hN
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos hNone
  let σ : ℝ := Real.log V / Real.log (N : ℝ)
  have hNσ : (N : ℝ) ^ σ = V := rpow_log_div_log hNone hV
  have hσL : 7 / 10 ≤ σ := by
    rw [le_div_iff₀ hlogN]
    have hlog := (Real.log_le_log_iff
      (Real.rpow_pos_of_pos hNpos _) hV).2 hVL
    rw [Real.log_rpow hNpos] at hlog
    simpa only [σ] using hlog
  have hσU : σ ≤ 4 / 5 := by
    rw [div_le_iff₀ hlogN]
    have hlog := (Real.log_le_log_iff hV
      (Real.rpow_pos_of_pos hNpos _)).2 hVU
    rw [Real.log_rpow hNpos] at hlog
    simpa only [σ] using hlog
  have hcard := hProp N σ W b hN hT hσL hσU hSep hBase hb (by
    intro t ht
    simpa only [hNσ] using hLarge t ht)
  have hscale : (N : ℝ) ^ ((12 - 20 * σ) / 5) =
      (N : ℝ) ^ (12 / 5 : ℝ) * V ^ (-4 : ℝ) := by
    rw [← hNσ, ← Real.rpow_mul hNpos.le, ← Real.rpow_add hNpos]
    congr 1
    ring
  simpa only [hscale, mul_assoc] using hcard

/-! ### The finite `T^η`-separation extraction used in Section 3 -/

/-- The `gmScaleSet` definition used by the source-facing construction in `LargeValuesFinal`. -/
noncomputable def gmScaleSet (δ : ℝ) (W : Finset ℝ) : Finset ℝ :=
  W.image fun t => t / δ

theorem gmScaleSet_card {W : Finset ℝ} {δ : ℝ} (hδ : 0 < δ) :
    (gmScaleSet δ W).card = W.card := by
  unfold gmScaleSet
  apply Finset.card_image_of_injective
  intro x y hxy
  exact (div_left_inj' hδ.ne').mp hxy

theorem gmScaleSet_unit_bin_card_le
    {W : Finset ℝ} {δ : ℝ} (hδ : 0 < δ) (hSep : IsSeparated 1 W) (z : ℤ) :
    ((gmScaleSet δ W).filter fun u => (z : ℝ) ≤ u ∧ u < (z : ℝ) + 1).card ≤
      2 * Nat.ceil δ + 1 := by
  let F := (gmScaleSet δ W).filter fun u => (z : ℝ) ≤ u ∧ u < (z : ℝ) + 1
  let G := W.filter fun t => |t - δ * (z : ℝ)| ≤ δ
  have himageCard : (F.image fun u => u * δ).card = F.card := by
    apply Finset.card_image_of_injective
    intro x y hxy
    exact (mul_right_cancel₀ hδ.ne' hxy)
  have hsub : F.image (fun u => u * δ) ⊆ G := by
    intro t ht
    rw [Finset.mem_image] at ht
    obtain ⟨u, huF, rfl⟩ := ht
    have huScale := (Finset.mem_filter.mp huF).1
    have huBin := (Finset.mem_filter.mp huF).2
    rw [gmScaleSet, Finset.mem_image] at huScale
    obtain ⟨x, hxW, rfl⟩ := huScale
    have hrecover : x / δ * δ = x := div_mul_cancel₀ x hδ.ne'
    rw [Finset.mem_filter, hrecover]
    refine ⟨hxW, ?_⟩
    rw [abs_le]
    constructor
    · have hleft := huBin.1
      rw [le_div_iff₀ hδ] at hleft
      nlinarith
    · have hright := huBin.2
      rw [div_lt_iff₀ hδ] at hright
      nlinarith
  have hpack : G.card ≤ 2 * Nat.ceil (δ / 1) + 1 := by
    apply card_filter_abs_sub_le_two_mul_ceil_add_one W (δ := 1)
      (by norm_num : (0 : ℝ) < 1) (center := δ * (z : ℝ)) (r := δ)
    · intro x hx y hy hxy
      simpa only [Real.dist_eq] using hSep x hx y hy hxy
    · exact hδ.le
  change F.card ≤ _
  rw [← himageCard]
  exact (Finset.card_le_card hsub).trans (by simpa using hpack)

/-- From a one-separated finite family, extract a `δ`-separated subfamily,
paying only the explicit one-dimensional packing loss. -/
theorem exists_dilated_separated_subset
    {W : Finset ℝ} {δ : ℝ} (hδ : 0 < δ) (hSep : IsSeparated 1 W) :
    ∃ W' ⊆ W, IsSeparated δ W' ∧
      W.card ≤ 2 * (2 * Nat.ceil δ + 1) * W'.card := by
  let S := gmScaleSet δ W
  obtain ⟨U, hUS, hUsep, hcardU⟩ := separated_selection S (2 * Nat.ceil δ + 1) (by
    intro z
    exact gmScaleSet_unit_bin_card_le hδ hSep z)
  let W' := U.image fun u => u * δ
  have hUcard : W'.card = U.card := by
    dsimp only [W']
    apply Finset.card_image_of_injective
    intro x y hxy
    exact mul_right_cancel₀ hδ.ne' hxy
  have hScard : S.card = W.card := gmScaleSet_card hδ
  refine ⟨W', ?_, ?_, ?_⟩
  · intro x hx
    dsimp only [W'] at hx
    rw [Finset.mem_image] at hx
    obtain ⟨u, huU, rfl⟩ := hx
    have huS : u ∈ S := hUS huU
    dsimp only [S] at huS
    rw [gmScaleSet, Finset.mem_image] at huS
    obtain ⟨t, htW, rfl⟩ := huS
    simpa only [div_mul_cancel₀ t hδ.ne'] using htW
  · intro x hx y hy hxy
    dsimp only [W'] at hx hy
    rw [Finset.mem_image] at hx hy
    obtain ⟨u, huU, rfl⟩ := hx
    obtain ⟨v, hvU, rfl⟩ := hy
    have huv : u ≠ v := by
      intro huv
      subst v
      exact hxy rfl
    have hdist := hUsep u huU v hvU huv
    rw [Real.dist_eq] at hdist
    rw [Real.dist_eq, ← sub_mul, abs_mul, abs_of_pos hδ]
    nlinarith [abs_nonneg (u - v)]
  · rw [← hScard, hUcard]
    exact hcardU

set_option maxHeartbeats 1000000 in
/-- Proposition 3.1 with the paper's preliminary separation extraction
performed internally.  The two factors `L^(ε/2)` (packing and Proposition
3.1) are combined exactly into `L^ε`. -/
theorem gmProposition3_1_smooth_oneSeparated
    (cutoff : GMSmoothCutoff) (ε : ℝ) (hε : 0 < ε) :
    ∃ C T₀ : ℝ, 0 < C ∧ 4096 ≤ T₀ ∧
      ∀ (N : ℕ) (V : ℝ) (W : Finset ℝ) (b : ℕ → ℂ),
      1 < N → T₀ ≤ (N : ℝ) ^ (6 / 5 : ℝ) → 0 < V →
      (N : ℝ) ^ (7 / 10 : ℝ) ≤ V → V ≤ (N : ℝ) ^ (4 / 5 : ℝ) →
      IsSeparated 1 W → InBaseInterval ((N : ℝ) ^ (6 / 5 : ℝ)) W →
      (∀ n ∈ dyadicInterval N, ‖b n‖ ≤ 1) →
      (∀ t ∈ W, V ≤ ‖gmSmoothDirichletPoly cutoff N b t‖) →
      (W.card : ℝ) ≤
        C * ((N : ℝ) ^ (6 / 5 : ℝ)) ^ ε *
          ((N : ℝ) ^ (6 / 5 : ℝ) * (N : ℝ) ^ (12 / 5 : ℝ) *
            V ^ (-4 : ℝ)) := by
  let η := ε / 2
  have hη : 0 < η := by dsimp only [η]; linarith
  obtain ⟨C₀, T₀, hC₀, hT₀, hProp⟩ :=
    gmProposition3_1_smooth_physical cutoff η hη
  let C := 10 * C₀
  refine ⟨C, T₀, by dsimp only [C]; positivity, hT₀, ?_⟩
  intro N V W b hN hT hV hVL hVU hSep hBase hb hLarge
  let L : ℝ := (N : ℝ) ^ (6 / 5 : ℝ)
  let δ : ℝ := L ^ η
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_lt_of_lt hN)
  have hNone : (1 : ℝ) ≤ N := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.zero_lt_of_lt hN).ne')
  have hLpos : 0 < L := Real.rpow_pos_of_pos hNpos _
  have hLone : 1 ≤ L := by
    dsimp only [L]
    exact Real.one_le_rpow hNone (by norm_num)
  have hδpos : 0 < δ := Real.rpow_pos_of_pos hLpos _
  have hδone : 1 ≤ δ := Real.one_le_rpow hLone hη.le
  obtain ⟨W', hsub, hSep', hcardNat⟩ := exists_dilated_separated_subset hδpos hSep
  have hcardReal : (W.card : ℝ) ≤
      (2 * (2 * Nat.ceil δ + 1) : ℕ) * (W'.card : ℝ) := by
    exact_mod_cast hcardNat
  have hceil : (Nat.ceil δ : ℝ) < δ + 1 := Nat.ceil_lt_add_one hδpos.le
  have hpacking : ((2 * (2 * Nat.ceil δ + 1) : ℕ) : ℝ) ≤ 10 * δ := by
    push_cast
    nlinarith
  have hBase' : InBaseInterval L W' := by
    intro t ht
    exact hBase t (hsub ht)
  have hLarge' : ∀ t ∈ W', V ≤ ‖gmSmoothDirichletPoly cutoff N b t‖ := by
    intro t ht
    exact hLarge t (hsub ht)
  have hselected := hProp N V W' b hN hT hV hVL hVU hSep'
    (by simpa only [L] using hBase') hb hLarge'
  have hcore : 0 ≤ L * (N : ℝ) ^ (12 / 5 : ℝ) * V ^ (-4 : ℝ) := by
    positivity
  have hδsq : δ * L ^ η = L ^ ε := by
    dsimp only [δ, η]
    rw [← Real.rpow_add hLpos]
    congr 1
    ring
  calc
    (W.card : ℝ) ≤ ((2 * (2 * Nat.ceil δ + 1) : ℕ) : ℝ) * W'.card := hcardReal
    _ ≤ (10 * δ) * W'.card := by gcongr
    _ ≤ (10 * δ) *
        (C₀ * L ^ η * (L * (N : ℝ) ^ (12 / 5 : ℝ) * V ^ (-4 : ℝ))) := by
      exact mul_le_mul_of_nonneg_left (by simpa only [L] using hselected) (by positivity)
    _ = C * L ^ ε *
        (L * (N : ℝ) ^ (12 / 5 : ℝ) * V ^ (-4 : ℝ)) := by
      rw [← hδsq]
      dsimp only [C]
      ring
    _ = C * ((N : ℝ) ^ (6 / 5 : ℝ)) ^ ε *
        ((N : ℝ) ^ (6 / 5 : ℝ) * (N : ℝ) ^ (12 / 5 : ℝ) *
          V ^ (-4 : ℝ)) := by rfl

/-- The `gmShiftCoeffs` definition used by the source-facing construction in `LargeValuesFinal`. -/
noncomputable def gmShiftCoeffs (s : ℝ) (b : ℕ → ℂ) (n : ℕ) : ℂ :=
  b n * (n : ℂ) ^ ((s : ℂ) * I)

theorem gmSmoothDirichletPoly_shift_eq
    (cutoff : GMSmoothCutoff) {N : ℕ} (hN : 0 < N)
    (b : ℕ → ℂ) (s u : ℝ) :
    gmSmoothDirichletPoly cutoff N (gmShiftCoeffs s b) u =
      gmSmoothDirichletPoly cutoff N b (u + s) := by
  unfold gmSmoothDirichletPoly gmShiftCoeffs
  apply Finset.sum_congr rfl
  intro n hn
  have hnpos : 0 < n := hN.trans (Finset.mem_Ioc.mp hn).1
  have hnne : (n : ℂ) ≠ 0 := by exact_mod_cast hnpos.ne'
  calc
    _ = cutoff ((n : ℝ) / N) * b n *
        ((n : ℂ) ^ ((s : ℂ) * I) * (n : ℂ) ^ ((u : ℂ) * I)) := by ring
    _ = cutoff ((n : ℝ) / N) * b n *
        (n : ℂ) ^ (((s : ℂ) * I) + ((u : ℂ) * I)) := by
      rw [Complex.cpow_add _ _ hnne]
    _ = _ := by
      congr 2
      push_cast
      ring

theorem norm_gmShiftCoeffs_le_one
    {N : ℕ} (hN : 0 < N) (b : ℕ → ℂ) (s : ℝ)
    (hb : ∀ n ∈ dyadicInterval N, ‖b n‖ ≤ 1) :
    ∀ n ∈ dyadicInterval N, ‖gmShiftCoeffs s b n‖ ≤ 1 := by
  intro n hn
  have hnpos : 0 < n := hN.trans (Finset.mem_Ioc.mp hn).1
  rw [gmShiftCoeffs, norm_mul, Complex.norm_natCast_cpow_of_pos hnpos]
  simpa using hb n hn

set_option maxHeartbeats 1000000 in
/-- Translation-invariant interval form of the one-separated Proposition
3.1.  The ordinate displacement is absorbed by an exact unit-modulus twist
of the fixed coefficients. -/
theorem gmProposition3_1_smooth_interval
    (cutoff : GMSmoothCutoff) (ε : ℝ) (hε : 0 < ε) :
    ∃ C T₀ : ℝ, 0 < C ∧ 4096 ≤ T₀ ∧
      ∀ (N : ℕ) (V a : ℝ) (W : Finset ℝ) (b : ℕ → ℂ),
      1 < N → T₀ ≤ (N : ℝ) ^ (6 / 5 : ℝ) → 0 < V →
      (N : ℝ) ^ (7 / 10 : ℝ) ≤ V → V ≤ (N : ℝ) ^ (4 / 5 : ℝ) →
      IsSeparated 1 W →
      (∀ t ∈ W, t ∈ Set.Icc a (a + (N : ℝ) ^ (6 / 5 : ℝ))) →
      (∀ n ∈ dyadicInterval N, ‖b n‖ ≤ 1) →
      (∀ t ∈ W, V ≤ ‖gmSmoothDirichletPoly cutoff N b t‖) →
      (W.card : ℝ) ≤
        C * ((N : ℝ) ^ (6 / 5 : ℝ)) ^ ε *
          ((N : ℝ) ^ (6 / 5 : ℝ) * (N : ℝ) ^ (12 / 5 : ℝ) *
            V ^ (-4 : ℝ)) := by
  obtain ⟨C, T₀, hC, hT₀, hProp⟩ :=
    gmProposition3_1_smooth_oneSeparated cutoff ε hε
  refine ⟨C, T₀, hC, hT₀, ?_⟩
  intro N V a W b hN hT hV hVL hVU hSep hInterval hb hLarge
  let W' := translateSet a W
  let b' := gmShiftCoeffs a b
  have hNpos : 0 < N := Nat.zero_lt_of_lt hN
  have hSep' : IsSeparated 1 W' := by
    dsimp only [W']
    exact isSeparated_translate 1 a W hSep
  have hBase' : InBaseInterval ((N : ℝ) ^ (6 / 5 : ℝ)) W' := by
    intro u hu
    dsimp only [W'] at hu
    rw [translateSet, Finset.mem_image] at hu
    obtain ⟨t, ht, rfl⟩ := hu
    have hit := hInterval t ht
    rcases hit with ⟨hitL, hitU⟩
    constructor <;> linarith
  have hb' : ∀ n ∈ dyadicInterval N, ‖b' n‖ ≤ 1 := by
    dsimp only [b']
    exact norm_gmShiftCoeffs_le_one hNpos b a hb
  have hLarge' : ∀ u ∈ W', V ≤ ‖gmSmoothDirichletPoly cutoff N b' u‖ := by
    intro u hu
    dsimp only [W'] at hu
    rw [translateSet, Finset.mem_image] at hu
    obtain ⟨t, ht, rfl⟩ := hu
    change V ≤ ‖gmSmoothDirichletPoly cutoff N (gmShiftCoeffs a b) (t - a)‖
    rw [gmSmoothDirichletPoly_shift_eq cutoff hNpos]
    simpa only [sub_add_cancel] using hLarge t ht
  have hcard := hProp N V W' b' hN hT hV hVL hVU hSep' hBase' hb' hLarge'
  simpa only [W', translateSet_card] using hcard

set_option maxHeartbeats 1000000 in
/-- Full-height version of Proposition 3.1.  The family is partitioned into
intervals of length `N^(6/5)`, translated with an exact coefficient twist,
and the fiber cardinalities are summed without overlap. -/
theorem gmProposition3_1_smooth_fullHeight
    (cutoff : GMSmoothCutoff) (ε : ℝ) (hε : 0 < ε) :
    ∃ C T₀ : ℝ, 0 < C ∧ 4096 ≤ T₀ ∧
      ∀ (N : ℕ) (V T : ℝ) (W : Finset ℝ) (b : ℕ → ℂ),
      1 < N → T₀ ≤ (N : ℝ) ^ (6 / 5 : ℝ) → (N : ℝ) ≤ T →
      0 < V → (N : ℝ) ^ (7 / 10 : ℝ) ≤ V →
      V ≤ (N : ℝ) ^ (4 / 5 : ℝ) →
      IsSeparated 1 W → InBaseInterval T W →
      (∀ n ∈ dyadicInterval N, ‖b n‖ ≤ 1) →
      (∀ t ∈ W, V ≤ ‖gmSmoothDirichletPoly cutoff N b t‖) →
      (W.card : ℝ) ≤ C * T ^ ε *
        ((N : ℝ) ^ (18 / 5 : ℝ) * V ^ (-4 : ℝ) +
          T * (N : ℝ) ^ (12 / 5 : ℝ) * V ^ (-4 : ℝ)) := by
  let η := ε / 2
  have hη : 0 < η := by dsimp only [η]; linarith
  obtain ⟨C₀, T₀, hC₀, hT₀, hInterval⟩ :=
    gmProposition3_1_smooth_interval cutoff η hη
  refine ⟨C₀, T₀, hC₀, hT₀, ?_⟩
  intro N V T W b hN hT₀N hNT hV hVL hVU hSep hBase hb hLarge
  let L : ℝ := (N : ℝ) ^ (6 / 5 : ℝ)
  let bin : ℝ → ℕ := fun t => Nat.floor (t / L)
  let K : ℕ := Nat.floor (T / L) + 1
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_lt_of_lt hN)
  have hNone : (1 : ℝ) ≤ N := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.zero_lt_of_lt hN).ne')
  have hLpos : 0 < L := Real.rpow_pos_of_pos hNpos _
  have hTpos : 0 < T := hNpos.trans_le hNT
  have hmaps : ∀ t ∈ W, bin t ∈ Finset.range K := by
    intro t ht
    have htBase := hBase t ht
    have hquot : t / L ≤ T / L := (div_le_div_iff_of_pos_right hLpos).2 htBase.2
    have hfloor := Nat.floor_mono hquot
    dsimp only [bin, K]
    rw [Finset.mem_range]
    omega
  have hfiber (k : ℕ) (hk : k ∈ Finset.range K) :
      (({t ∈ W | bin t = k}).card : ℝ) ≤
        C₀ * L ^ η *
          (L * (N : ℝ) ^ (12 / 5 : ℝ) * V ^ (-4 : ℝ)) := by
    let Wk := {t ∈ W | bin t = k}
    have hWkSep : IsSeparated 1 Wk := by
      intro x hx y hy hxy
      exact hSep x (Finset.mem_filter.mp hx).1 y (Finset.mem_filter.mp hy).1 hxy
    have hWkInterval : ∀ t ∈ Wk, t ∈ Set.Icc ((k : ℝ) * L) ((k : ℝ) * L + L) := by
      intro t ht
      have htData := Finset.mem_filter.mp ht
      have htBase := hBase t htData.1
      have hbin := htData.2
      have hquotNonneg : 0 ≤ t / L := div_nonneg htBase.1 hLpos.le
      have hlowFloor : ((bin t : ℕ) : ℝ) ≤ t / L := Nat.floor_le hquotNonneg
      have hhighFloor : t / L < ((bin t : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
      constructor
      · rw [hbin] at hlowFloor
        exact (le_div_iff₀ hLpos).mp hlowFloor
      · rw [hbin] at hhighFloor
        have hh := (div_lt_iff₀ hLpos).mp hhighFloor
        linarith
    have hWkLarge : ∀ t ∈ Wk, V ≤ ‖gmSmoothDirichletPoly cutoff N b t‖ := by
      intro t ht
      exact hLarge t (Finset.mem_filter.mp ht).1
    change (Wk.card : ℝ) ≤ _
    simpa only [L] using hInterval N V ((k : ℝ) * L) Wk b hN hT₀N hV hVL hVU
      hWkSep (by simpa only [add_comm, add_left_comm, add_assoc, L] using hWkInterval)
      hb hWkLarge
  have hcard : W.card = ∑ k ∈ Finset.range K, ({t ∈ W | bin t = k}).card :=
    Finset.card_eq_sum_card_fiberwise hmaps
  have hsum : (W.card : ℝ) ≤
      (K : ℝ) *
        (C₀ * L ^ η * (L * (N : ℝ) ^ (12 / 5 : ℝ) * V ^ (-4 : ℝ))) := by
    calc
      (W.card : ℝ) = ∑ k ∈ Finset.range K,
          (({t ∈ W | bin t = k}).card : ℝ) := by exact_mod_cast hcard
      _ ≤ ∑ _k ∈ Finset.range K,
          (C₀ * L ^ η * (L * (N : ℝ) ^ (12 / 5 : ℝ) * V ^ (-4 : ℝ))) := by
        exact Finset.sum_le_sum hfiber
      _ = (K : ℝ) *
          (C₀ * L ^ η * (L * (N : ℝ) ^ (12 / 5 : ℝ) * V ^ (-4 : ℝ))) := by
        simp only [sum_const, card_range, nsmul_eq_mul]
  have hqNonneg : 0 ≤ T / L := div_nonneg hTpos.le hLpos.le
  have hK : (K : ℝ) ≤ T / L + 1 := by
    dsimp only [K]
    have hf := Nat.floor_le hqNonneg
    push_cast
    linarith
  have hLηT : L ^ η ≤ T ^ ε := by
    have hNexp : (N : ℝ) ^ ((6 / 5 : ℝ) * η) ≤ (N : ℝ) ^ ε := by
      apply Real.rpow_le_rpow_of_exponent_le hNone
      dsimp only [η]
      linarith
    calc
      L ^ η = (N : ℝ) ^ ((6 / 5 : ℝ) * η) := by
        dsimp only [L]
        rw [Real.rpow_mul hNpos.le]
      _ ≤ (N : ℝ) ^ ε := hNexp
      _ ≤ T ^ ε := Real.rpow_le_rpow hNpos.le hNT hε.le
  have hLscale : L * (N : ℝ) ^ (12 / 5 : ℝ) =
      (N : ℝ) ^ (18 / 5 : ℝ) := by
    dsimp only [L]
    rw [← Real.rpow_add hNpos]
    congr 1
    ring
  have hcore : 0 ≤ (N : ℝ) ^ (12 / 5 : ℝ) * V ^ (-4 : ℝ) := by
    positivity
  calc
    (W.card : ℝ) ≤ (K : ℝ) *
        (C₀ * L ^ η * (L * (N : ℝ) ^ (12 / 5 : ℝ) * V ^ (-4 : ℝ))) := hsum
    _ ≤ (T / L + 1) *
        (C₀ * L ^ η * (L * (N : ℝ) ^ (12 / 5 : ℝ) * V ^ (-4 : ℝ))) := by
      gcongr
    _ ≤ (T / L + 1) *
        (C₀ * T ^ ε * (L * (N : ℝ) ^ (12 / 5 : ℝ) * V ^ (-4 : ℝ))) := by
      gcongr
    _ = C₀ * T ^ ε *
        ((N : ℝ) ^ (18 / 5 : ℝ) * V ^ (-4 : ℝ) +
          T * (N : ℝ) ^ (12 / 5 : ℝ) * V ^ (-4 : ℝ)) := by
      rw [← hLscale]
      field_simp [hLpos.ne']
      ring

/-! ### Classical complementary ranges in the source sign convention -/

theorem gm_inv_rpow_two {V : ℝ} (hV : 0 < V) :
    V ^ (-2 : ℝ) = 1 / V ^ 2 := by
  rw [Real.rpow_neg hV.le, Real.rpow_two, inv_eq_one_div]

theorem gm_inv_rpow_four {V : ℝ} (hV : 0 < V) :
    V ^ (-4 : ℝ) = 1 / V ^ 4 := by
  rw [Real.rpow_neg hV.le, ← Real.rpow_natCast]
  norm_num

theorem gm_classical_min_low
    {N : ℕ} {V B : ℝ} (hN : 0 < N) (hV : 0 < V)
    (hLow : V ≤ B * (N : ℝ) ^ (7 / 10 : ℝ)) :
    min ((N : ℝ) / V ^ 2) ((N : ℝ) ^ 4 / V ^ 6) ≤
      B ^ 2 * (N : ℝ) ^ (12 / 5 : ℝ) * V ^ (-4 : ℝ) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hpowSeven : ((N : ℝ) ^ (7 / 10 : ℝ)) ^ 2 =
      (N : ℝ) ^ (7 / 5 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn.le]
    congr 1
    ring
  have hVsq : V ^ 2 ≤ B ^ 2 * (N : ℝ) ^ (7 / 5 : ℝ) := by
    have hs := pow_le_pow_left₀ hV.le hLow 2
    calc
      V ^ 2 ≤ (B * (N : ℝ) ^ (7 / 10 : ℝ)) ^ 2 := hs
      _ = B ^ 2 * (N : ℝ) ^ (7 / 5 : ℝ) := by
        rw [mul_pow, hpowSeven]
  have hpowTwelve : (N : ℝ) * (N : ℝ) ^ (7 / 5 : ℝ) =
      (N : ℝ) ^ (12 / 5 : ℝ) := by
    calc
      (N : ℝ) * (N : ℝ) ^ (7 / 5 : ℝ) =
          (N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ (7 / 5 : ℝ) := by
            rw [Real.rpow_one]
      _ = (N : ℝ) ^ ((1 : ℝ) + 7 / 5) := (Real.rpow_add hn _ _).symm
      _ = (N : ℝ) ^ (12 / 5 : ℝ) := by
        congr 1
        ring
  have hnum : (N : ℝ) * V ^ 2 ≤ B ^ 2 * (N : ℝ) ^ (12 / 5 : ℝ) := by
    calc
      (N : ℝ) * V ^ 2 ≤ (N : ℝ) *
          (B ^ 2 * (N : ℝ) ^ (7 / 5 : ℝ)) := by gcongr
      _ = B ^ 2 * (N : ℝ) ^ (12 / 5 : ℝ) := by
        rw [← hpowTwelve]
        ring
  calc
    min ((N : ℝ) / V ^ 2) ((N : ℝ) ^ 4 / V ^ 6) ≤ (N : ℝ) / V ^ 2 := min_le_left _ _
    _ ≤ B ^ 2 * (N : ℝ) ^ (12 / 5 : ℝ) / V ^ 4 := by
      rw [show (N : ℝ) / V ^ 2 = ((N : ℝ) * V ^ 2) / V ^ 4 by
        field_simp [hV.ne']]
      apply (div_le_div_iff_of_pos_right (pow_pos hV 4)).2
      exact hnum
    _ = B ^ 2 * (N : ℝ) ^ (12 / 5 : ℝ) * V ^ (-4 : ℝ) := by
      rw [gm_inv_rpow_four hV]
      ring

theorem gm_classical_min_high
    {N : ℕ} {V : ℝ} (hN : 0 < N) (hV : 0 < V)
    (hHigh : (1 / 2 : ℝ) * (N : ℝ) ^ (4 / 5 : ℝ) ≤ V) :
    min ((N : ℝ) / V ^ 2) ((N : ℝ) ^ 4 / V ^ 6) ≤
      4 * (N : ℝ) ^ (12 / 5 : ℝ) * V ^ (-4 : ℝ) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hpowEight : ((N : ℝ) ^ (4 / 5 : ℝ)) ^ 2 =
      (N : ℝ) ^ (8 / 5 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn.le]
    congr 1
    ring
  have hNsq : (N : ℝ) ^ (8 / 5 : ℝ) ≤ 4 * V ^ 2 := by
    have hs := pow_le_pow_left₀ (by positivity : 0 ≤ (1 / 2 : ℝ) *
      (N : ℝ) ^ (4 / 5 : ℝ)) hHigh 2
    calc
      (N : ℝ) ^ (8 / 5 : ℝ) =
          4 * ((1 / 2 : ℝ) * (N : ℝ) ^ (4 / 5 : ℝ)) ^ 2 := by
        rw [mul_pow, hpowEight]
        ring
      _ ≤ 4 * V ^ 2 := by gcongr
  have hnum : (N : ℝ) ^ 4 ≤
      4 * (N : ℝ) ^ (12 / 5 : ℝ) * V ^ 2 := by
    calc
      (N : ℝ) ^ 4 = (N : ℝ) ^ (12 / 5 : ℝ) *
          (N : ℝ) ^ (8 / 5 : ℝ) := by
        rw [← Real.rpow_add hn]
        norm_num [Real.rpow_natCast]
      _ ≤ (N : ℝ) ^ (12 / 5 : ℝ) * (4 * V ^ 2) := by gcongr
      _ = 4 * (N : ℝ) ^ (12 / 5 : ℝ) * V ^ 2 := by ring
  calc
    min ((N : ℝ) / V ^ 2) ((N : ℝ) ^ 4 / V ^ 6) ≤
        (N : ℝ) ^ 4 / V ^ 6 := min_le_right _ _
    _ ≤ 4 * (N : ℝ) ^ (12 / 5 : ℝ) / V ^ 4 := by
      field_simp [hV.ne']
      nlinarith
    _ = 4 * (N : ℝ) ^ (12 / 5 : ℝ) * V ^ (-4 : ℝ) := by
      rw [gm_inv_rpow_four hV]
      ring

set_option maxHeartbeats 1000000 in
theorem gm_classical_source_low
    (ε B : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N : ℕ) (V T : ℝ) (b : ℕ → ℂ) (W : Finset ℝ),
      0 < N → 1 ≤ T → (N : ℝ) ≤ T → 0 < V →
      V ≤ B * (N : ℝ) ^ (7 / 10 : ℝ) →
      (∀ n, ‖b n‖ ≤ 1) → IsSeparated 1 W → InBaseInterval T W →
      (∀ t ∈ W, V ≤ ‖sourceDirichletPoly N b t‖) →
      (W.card : ℝ) ≤ C * T ^ ε *
        ((N : ℝ) ^ 2 * V ^ (-2 : ℝ) +
          (N : ℝ) ^ (18 / 5 : ℝ) * V ^ (-4 : ℝ) +
          T * (N : ℝ) ^ (12 / 5 : ℝ) * V ^ (-4 : ℝ)) := by
  obtain ⟨C₀, hC₀, hMHH⟩ := classical_montgomery_halasz_huxley_native ε hε
  let C := C₀ * (1 + B ^ 2)
  refine ⟨C, by dsimp only [C]; positivity, ?_⟩
  intro N V T b W hN hT hNT hV hLow hb hSep hBase hLarge
  have hb' : ∀ n ∈ dyadicInterval N, ‖conjugateCoeffs b n‖ ≤ 1 := by
    intro n hn
    rw [norm_conjugateCoeffs]
    exact hb n
  have hLarge' : ∀ t ∈ W, V ≤ ‖dirichletPoly N (conjugateCoeffs b) t‖ := by
    intro t ht
    rw [← norm_sourceDirichletPoly_eq_dirichletPoly_conjugateCoeffs]
    exact hLarge t ht
  have hraw := hMHH N T V W (conjugateCoeffs b) hN hT hNT hV hb' hSep hBase hLarge'
  have hmin := gm_classical_min_low hN hV hLow
  have hBsq : 0 ≤ B ^ 2 := sq_nonneg B
  have hfirst : (N : ℝ) ^ 2 / V ^ 2 = (N : ℝ) ^ 2 * V ^ (-2 : ℝ) := by
    rw [gm_inv_rpow_two hV]
    ring
  let X : ℝ := (N : ℝ) ^ 2 * V ^ (-2 : ℝ)
  let Y : ℝ := (N : ℝ) ^ (18 / 5 : ℝ) * V ^ (-4 : ℝ)
  let Z : ℝ := T * (N : ℝ) ^ (12 / 5 : ℝ) * V ^ (-4 : ℝ)
  have hX : 0 ≤ X := by dsimp only [X]; positivity
  have hY : 0 ≤ Y := by dsimp only [Y]; positivity
  have hZ : 0 ≤ Z := by dsimp only [Z]; positivity
  have hinner₁ : (N : ℝ) ^ 2 / V ^ 2 +
      T * min ((N : ℝ) / V ^ 2) ((N : ℝ) ^ 4 / V ^ 6) ≤ X + B ^ 2 * Z := by
    rw [hfirst]
    dsimp only [X, Z]
    have hm := mul_le_mul_of_nonneg_left hmin (zero_le_one.trans hT)
    nlinarith
  have hinner₂ : X + B ^ 2 * Z ≤ (1 + B ^ 2) * (X + Y + Z) := by
    nlinarith [mul_nonneg hBsq hZ]
  calc
    (W.card : ℝ) ≤ C₀ * T ^ ε *
        ((N : ℝ) ^ 2 / V ^ 2 +
          T * min ((N : ℝ) / V ^ 2) ((N : ℝ) ^ 4 / V ^ 6)) := hraw
    _ ≤ C₀ * T ^ ε * (X + B ^ 2 * Z) :=
      mul_le_mul_of_nonneg_left hinner₁
        (mul_nonneg hC₀.le (Real.rpow_nonneg (zero_le_one.trans hT) ε))
    _ ≤ C * T ^ ε *
        ((N : ℝ) ^ 2 * V ^ (-2 : ℝ) +
          (N : ℝ) ^ (18 / 5 : ℝ) * V ^ (-4 : ℝ) +
          T * (N : ℝ) ^ (12 / 5 : ℝ) * V ^ (-4 : ℝ)) := by
      dsimp only [C]
      dsimp only [X, Y, Z] at hinner₂ ⊢
      nlinarith [mul_nonneg (mul_nonneg hC₀.le
        (Real.rpow_nonneg (zero_le_one.trans hT) ε))
        (sub_nonneg.mpr hinner₂)]

set_option maxHeartbeats 1000000 in
theorem gm_classical_source_high
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N : ℕ) (V T : ℝ) (b : ℕ → ℂ) (W : Finset ℝ),
      0 < N → 1 ≤ T → (N : ℝ) ≤ T → 0 < V →
      (1 / 2 : ℝ) * (N : ℝ) ^ (4 / 5 : ℝ) ≤ V →
      (∀ n, ‖b n‖ ≤ 1) → IsSeparated 1 W → InBaseInterval T W →
      (∀ t ∈ W, V ≤ ‖sourceDirichletPoly N b t‖) →
      (W.card : ℝ) ≤ C * T ^ ε *
        ((N : ℝ) ^ 2 * V ^ (-2 : ℝ) +
          (N : ℝ) ^ (18 / 5 : ℝ) * V ^ (-4 : ℝ) +
          T * (N : ℝ) ^ (12 / 5 : ℝ) * V ^ (-4 : ℝ)) := by
  obtain ⟨C₀, hC₀, hMHH⟩ := classical_montgomery_halasz_huxley_native ε hε
  let C := 5 * C₀
  refine ⟨C, by dsimp only [C]; positivity, ?_⟩
  intro N V T b W hN hT hNT hV hHigh hb hSep hBase hLarge
  have hb' : ∀ n ∈ dyadicInterval N, ‖conjugateCoeffs b n‖ ≤ 1 := by
    intro n hn
    rw [norm_conjugateCoeffs]
    exact hb n
  have hLarge' : ∀ t ∈ W, V ≤ ‖dirichletPoly N (conjugateCoeffs b) t‖ := by
    intro t ht
    rw [← norm_sourceDirichletPoly_eq_dirichletPoly_conjugateCoeffs]
    exact hLarge t ht
  have hraw := hMHH N T V W (conjugateCoeffs b) hN hT hNT hV hb' hSep hBase hLarge'
  have hmin := gm_classical_min_high hN hV hHigh
  have hfirst : (N : ℝ) ^ 2 / V ^ 2 = (N : ℝ) ^ 2 * V ^ (-2 : ℝ) := by
    rw [gm_inv_rpow_two hV]
    ring
  let X : ℝ := (N : ℝ) ^ 2 * V ^ (-2 : ℝ)
  let Y : ℝ := (N : ℝ) ^ (18 / 5 : ℝ) * V ^ (-4 : ℝ)
  let Z : ℝ := T * (N : ℝ) ^ (12 / 5 : ℝ) * V ^ (-4 : ℝ)
  have hX : 0 ≤ X := by dsimp only [X]; positivity
  have hY : 0 ≤ Y := by dsimp only [Y]; positivity
  have hZ : 0 ≤ Z := by dsimp only [Z]; positivity
  have hinner₁ : (N : ℝ) ^ 2 / V ^ 2 +
      T * min ((N : ℝ) / V ^ 2) ((N : ℝ) ^ 4 / V ^ 6) ≤ X + 4 * Z := by
    rw [hfirst]
    dsimp only [X, Z]
    have hm := mul_le_mul_of_nonneg_left hmin (zero_le_one.trans hT)
    nlinarith
  have hinner₂ : X + 4 * Z ≤ 5 * (X + Y + Z) := by nlinarith
  calc
    (W.card : ℝ) ≤ C₀ * T ^ ε *
        ((N : ℝ) ^ 2 / V ^ 2 +
          T * min ((N : ℝ) / V ^ 2) ((N : ℝ) ^ 4 / V ^ 6)) := hraw
    _ ≤ C₀ * T ^ ε * (X + 4 * Z) :=
      mul_le_mul_of_nonneg_left hinner₁
        (mul_nonneg hC₀.le (Real.rpow_nonneg (zero_le_one.trans hT) ε))
    _ ≤ C * T ^ ε * (X + Y + Z) := by
      dsimp only [C]
      nlinarith [mul_nonneg (mul_nonneg hC₀.le
        (Real.rpow_nonneg (zero_le_one.trans hT) ε))
        (sub_nonneg.mpr hinner₂)]
    _ = C * T ^ ε *
        ((N : ℝ) ^ 2 * V ^ (-2 : ℝ) +
          (N : ℝ) ^ (18 / 5 : ℝ) * V ^ (-4 : ℝ) +
          T * (N : ℝ) ^ (12 / 5 : ℝ) * V ^ (-4 : ℝ)) := by rfl

set_option maxHeartbeats 1000000 in
theorem gm_classical_source_near_height
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N : ℕ) (V T : ℝ) (b : ℕ → ℂ) (W : Finset ℝ),
      0 < N → 1 ≤ T → T ≤ 2 * (N : ℝ) → 0 < V →
      (∀ n, ‖b n‖ ≤ 1) → IsSeparated 1 W → InBaseInterval T W →
      (∀ t ∈ W, V ≤ ‖sourceDirichletPoly N b t‖) →
      (W.card : ℝ) ≤ C * T ^ ε *
        ((N : ℝ) ^ 2 * V ^ (-2 : ℝ) +
          (N : ℝ) ^ (18 / 5 : ℝ) * V ^ (-4 : ℝ) +
          T * (N : ℝ) ^ (12 / 5 : ℝ) * V ^ (-4 : ℝ)) := by
  obtain ⟨C₀, hC₀, hSecond⟩ := classical_large_values_second_branch_unrestricted
  let C := 3 * C₀
  refine ⟨C, by dsimp only [C]; positivity, ?_⟩
  intro N V T b W hN hT hTN hV hb hSep hBase hLarge
  have hb' : ∀ n ∈ dyadicInterval N, ‖conjugateCoeffs b n‖ ≤ 1 := by
    intro n hn
    rw [norm_conjugateCoeffs]
    exact hb n
  have hLarge' : ∀ t ∈ W, V ≤ ‖dirichletPoly N (conjugateCoeffs b) t‖ := by
    intro t ht
    rw [← norm_sourceDirichletPoly_eq_dirichletPoly_conjugateCoeffs]
    exact hLarge t ht
  have hraw := hSecond N T V W (conjugateCoeffs b) hN hT hV hb' hSep hBase hLarge'
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hfirst : (N : ℝ) ^ 2 / V ^ 2 = (N : ℝ) ^ 2 * V ^ (-2 : ℝ) := by
    rw [gm_inv_rpow_two hV]
    ring
  have hsecond : T * (N : ℝ) / V ^ 2 ≤
      2 * ((N : ℝ) ^ 2 * V ^ (-2 : ℝ)) := by
    rw [gm_inv_rpow_two hV]
    have hmul := mul_le_mul_of_nonneg_right hTN hn.le
    field_simp [hV.ne']
    nlinarith
  have hTone : 1 ≤ T ^ ε := Real.one_le_rpow hT hε.le
  let X : ℝ := (N : ℝ) ^ 2 * V ^ (-2 : ℝ)
  let Y : ℝ := (N : ℝ) ^ (18 / 5 : ℝ) * V ^ (-4 : ℝ)
  let Z : ℝ := T * (N : ℝ) ^ (12 / 5 : ℝ) * V ^ (-4 : ℝ)
  have hX : 0 ≤ X := by dsimp only [X]; positivity
  have hY : 0 ≤ Y := by dsimp only [Y]; positivity
  have hZ : 0 ≤ Z := by dsimp only [Z]; positivity
  have hinner₁ : (N : ℝ) ^ 2 / V ^ 2 + T * (N : ℝ) / V ^ 2 ≤ 3 * X := by
    rw [hfirst]
    dsimp only [X]
    nlinarith
  have hinner₂ : 3 * X ≤ 3 * T ^ ε * (X + Y + Z) := by
    nlinarith [mul_nonneg (zero_le_one.trans hTone) (add_nonneg (add_nonneg hX hY) hZ)]
  calc
    (W.card : ℝ) ≤ C₀ * ((N : ℝ) ^ 2 / V ^ 2 + T * (N : ℝ) / V ^ 2) := hraw
    _ ≤ C₀ * (3 * X) := mul_le_mul_of_nonneg_left hinner₁ hC₀.le
    _ ≤ C * T ^ ε * (X + Y + Z) := by
      dsimp only [C]
      nlinarith [mul_nonneg hC₀.le (sub_nonneg.mpr hinner₂)]
    _ = C * T ^ ε *
        ((N : ℝ) ^ 2 * V ^ (-2 : ℝ) +
          (N : ℝ) ^ (18 / 5 : ℝ) * V ^ (-4 : ℝ) +
          T * (N : ℝ) ^ (12 / 5 : ℝ) * V ^ (-4 : ℝ)) := by rfl

theorem gm_source_scale_bounds
    {N Q : ℕ} (hN : 30 ≤ N)
    (hQ : Q = gmSourceLeftScale N ∨ Q = N ∨ Q = gmSourceRightScale N) :
    N ≤ 2 * Q ∧ Q ≤ 2 * N := by
  rcases hQ with hQ | hQ | hQ
  · subst Q
    dsimp only [gmSourceLeftScale]
    omega
  · subst Q
    omega
  · subst Q
    dsimp only [gmSourceRightScale]
    omega

theorem gm_source_scale_gt_one
    {N Q : ℕ} (hN : 30 ≤ N)
    (hQ : Q = gmSourceLeftScale N ∨ Q = N ∨ Q = gmSourceRightScale N) :
    1 < Q := by
  have h := (gm_source_scale_bounds hN hQ).1
  omega

theorem gm_rpow_scale_le_sixteen
    {N Q : ℕ} (hQ : Q ≤ 2 * N) :
    (Q : ℝ) ^ (18 / 5 : ℝ) ≤ 16 * (N : ℝ) ^ (18 / 5 : ℝ) := by
  have hn : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hcast : (Q : ℝ) ≤ 2 * (N : ℝ) := by exact_mod_cast hQ
  calc
    (Q : ℝ) ^ (18 / 5 : ℝ) ≤ (2 * (N : ℝ)) ^ (18 / 5 : ℝ) :=
      Real.rpow_le_rpow (Nat.cast_nonneg Q) hcast (by norm_num)
    _ = (2 : ℝ) ^ (18 / 5 : ℝ) * (N : ℝ) ^ (18 / 5 : ℝ) :=
      Real.mul_rpow (by norm_num) hn
    _ ≤ 16 * (N : ℝ) ^ (18 / 5 : ℝ) := by
      have hpow : (2 : ℝ) ^ (18 / 5 : ℝ) ≤ (2 : ℝ) ^ (4 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      have hpow' : (2 : ℝ) ^ (18 / 5 : ℝ) ≤ 16 := hpow.trans_eq (by norm_num)
      exact mul_le_mul_of_nonneg_right hpow' (Real.rpow_nonneg hn _)

theorem gm_rpow_scale_le_eight
    {N Q : ℕ} (hQ : Q ≤ 2 * N) :
    (Q : ℝ) ^ (12 / 5 : ℝ) ≤ 8 * (N : ℝ) ^ (12 / 5 : ℝ) := by
  have hn : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hcast : (Q : ℝ) ≤ 2 * (N : ℝ) := by exact_mod_cast hQ
  calc
    (Q : ℝ) ^ (12 / 5 : ℝ) ≤ (2 * (N : ℝ)) ^ (12 / 5 : ℝ) :=
      Real.rpow_le_rpow (Nat.cast_nonneg Q) hcast (by norm_num)
    _ = (2 : ℝ) ^ (12 / 5 : ℝ) * (N : ℝ) ^ (12 / 5 : ℝ) :=
      Real.mul_rpow (by norm_num) hn
    _ ≤ 8 * (N : ℝ) ^ (12 / 5 : ℝ) := by
      have hpow : (2 : ℝ) ^ (12 / 5 : ℝ) ≤ (2 : ℝ) ^ (3 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      have hpow' : (2 : ℝ) ^ (12 / 5 : ℝ) ≤ 8 := hpow.trans_eq (by norm_num)
      exact mul_le_mul_of_nonneg_right hpow' (Real.rpow_nonneg hn _)

theorem gm_source_scale_critical_lower
    {N Q : ℕ} {V : ℝ} (hQ : Q ≤ 2 * N)
    (hLow : 6 * (N : ℝ) ^ (7 / 10 : ℝ) ≤ V) :
    (Q : ℝ) ^ (7 / 10 : ℝ) ≤ V / 3 := by
  have hcast : (Q : ℝ) ≤ 2 * (N : ℝ) := by exact_mod_cast hQ
  have hn : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hq := Real.rpow_le_rpow (Nat.cast_nonneg Q) hcast (by norm_num : (0 : ℝ) ≤ 7 / 10)
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hn] at hq
  have htwo : (2 : ℝ) ^ (7 / 10 : ℝ) ≤ 2 := by
    calc
      (2 : ℝ) ^ (7 / 10 : ℝ) ≤ (2 : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 2 := Real.rpow_one _
  have hmid : (Q : ℝ) ^ (7 / 10 : ℝ) ≤
      2 * (N : ℝ) ^ (7 / 10 : ℝ) :=
    hq.trans (mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg hn _))
  linarith

theorem gm_source_scale_critical_upper
    {N Q : ℕ} {V : ℝ} (hQ : N ≤ 2 * Q)
    (hHigh : V ≤ (1 / 2 : ℝ) * (N : ℝ) ^ (4 / 5 : ℝ)) :
    V / 3 ≤ (Q : ℝ) ^ (4 / 5 : ℝ) := by
  have hcast : (N : ℝ) ≤ 2 * (Q : ℝ) := by exact_mod_cast hQ
  have hq0 : (0 : ℝ) ≤ Q := Nat.cast_nonneg Q
  have hnq := Real.rpow_le_rpow (Nat.cast_nonneg N) hcast (by norm_num : (0 : ℝ) ≤ 4 / 5)
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hq0] at hnq
  have htwo : (2 : ℝ) ^ (4 / 5 : ℝ) ≤ 2 := by
    calc
      (2 : ℝ) ^ (4 / 5 : ℝ) ≤ (2 : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 2 := Real.rpow_one _
  have hmid : (N : ℝ) ^ (4 / 5 : ℝ) ≤
      2 * (Q : ℝ) ^ (4 / 5 : ℝ) :=
    hnq.trans (mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg hq0 _))
  linarith [Real.rpow_nonneg hq0 (4 / 5 : ℝ)]

theorem gm_div_three_rpow_neg_four {V : ℝ} (hV : 0 < V) :
    (V / 3) ^ (-4 : ℝ) = 81 * V ^ (-4 : ℝ) := by
  rw [gm_inv_rpow_four (div_pos hV (by norm_num)), gm_inv_rpow_four hV]
  field_simp [hV.ne']
  ring

set_option maxHeartbeats 1000000 in
/-- The genuinely Guth--Maynard part of Theorem 1.1 after the exact
three-piece source localization.  The hypotheses are the central range in
which all three localized scales satisfy Proposition 3.1. -/
theorem gm_source_large_values_critical
    (cutoff : GMSmoothCutoff) (ε : ℝ) (hε : 0 < ε) :
    ∃ C T₀ : ℝ, 0 < C ∧ 4096 ≤ T₀ ∧
      ∀ (N : ℕ) (V T : ℝ) (b : ℕ → ℂ) (W : Finset ℝ),
      30 ≤ N → 2 * T₀ ≤ (N : ℝ) → 2 * (N : ℝ) ≤ T → 0 < V →
      6 * (N : ℝ) ^ (7 / 10 : ℝ) ≤ V →
      V ≤ (1 / 2 : ℝ) * (N : ℝ) ^ (4 / 5 : ℝ) →
      (∀ n, ‖b n‖ ≤ 1) → IsSeparated 1 W → InBaseInterval T W →
      (∀ t ∈ W, V ≤ ‖sourceDirichletPoly N b t‖) →
      (W.card : ℝ) ≤ C * T ^ ε *
        ((N : ℝ) ^ (18 / 5 : ℝ) * V ^ (-4 : ℝ) +
          T * (N : ℝ) ^ (12 / 5 : ℝ) * V ^ (-4 : ℝ)) := by
  obtain ⟨C₀, T₀, hC₀, hT₀, hFull⟩ :=
    gmProposition3_1_smooth_fullHeight cutoff ε hε
  let C := 3888 * C₀
  refine ⟨C, T₀, by dsimp only [C]; positivity, hT₀, ?_⟩
  intro N V T b W hN hNlarge hNT hV hLow hHigh hb hSep hBase hLarge
  have hNpos : 0 < N := by omega
  have hbDyadic : ∀ n ∈ dyadicInterval N, ‖b n‖ ≤ 1 := by
    intro n hn
    exact hb n
  obtain ⟨W', Q, c, hsub, hcardNat, hcase, hc, hlarge, hmatrix⟩ :=
    source_large_values_localize_to_matrix cutoff hN b W V hV hbDyadic hLarge
  have hQcase : Q = gmSourceLeftScale N ∨ Q = N ∨ Q = gmSourceRightScale N := by
    rcases hcase with ⟨hQ, hcEq⟩ | ⟨hQ, hcEq⟩ | ⟨hQ, hcEq⟩
    · exact Or.inl hQ
    · exact Or.inr (Or.inl hQ)
    · exact Or.inr (Or.inr hQ)
  have hQB := gm_source_scale_bounds hN hQcase
  have hQgt : 1 < Q := gm_source_scale_gt_one hN hQcase
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast (Nat.zero_lt_of_lt hQgt)
  have hQone : (1 : ℝ) ≤ Q := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.zero_lt_of_lt hQgt).ne')
  have hT₀Q : T₀ ≤ (Q : ℝ) ^ (6 / 5 : ℝ) := by
    have hNQ : (N : ℝ) ≤ 2 * Q := by exact_mod_cast hQB.1
    have hT₀leQ : T₀ ≤ (Q : ℝ) := by linarith
    exact hT₀leQ.trans (by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hQone (by norm_num : (1 : ℝ) ≤ 6 / 5))
  have hQT : (Q : ℝ) ≤ T := by
    have hQN : (Q : ℝ) ≤ 2 * N := by exact_mod_cast hQB.2
    exact hQN.trans hNT
  have hVL : (Q : ℝ) ^ (7 / 10 : ℝ) ≤ V / 3 :=
    gm_source_scale_critical_lower hQB.2 hLow
  have hVU : V / 3 ≤ (Q : ℝ) ^ (4 / 5 : ℝ) :=
    gm_source_scale_critical_upper hQB.1 hHigh
  have hSep' : IsSeparated 1 W' := by
    intro x hx y hy hxy
    exact hSep x (hsub hx) y (hsub hy) hxy
  have hBase' : InBaseInterval T W' := by
    intro t ht
    exact hBase t (hsub ht)
  have hfull := hFull Q (V / 3) T W' c hQgt hT₀Q hQT
    (div_pos hV (by norm_num)) hVL hVU hSep' hBase' hc hlarge
  have hcardReal : (W.card : ℝ) ≤ 3 * (W'.card : ℝ) := by exact_mod_cast hcardNat
  have hQ18 := gm_rpow_scale_le_sixteen hQB.2
  have hQ12 := gm_rpow_scale_le_eight hQB.2
  have htail : 0 ≤ T := hQpos.le.trans hQT
  have hshape :
      (Q : ℝ) ^ (18 / 5 : ℝ) * (V / 3) ^ (-4 : ℝ) +
          T * (Q : ℝ) ^ (12 / 5 : ℝ) * (V / 3) ^ (-4 : ℝ) ≤
        1296 * ((N : ℝ) ^ (18 / 5 : ℝ) * V ^ (-4 : ℝ) +
          T * (N : ℝ) ^ (12 / 5 : ℝ) * V ^ (-4 : ℝ)) := by
    rw [gm_div_three_rpow_neg_four hV]
    have hV4 : 0 ≤ V ^ (-4 : ℝ) := Real.rpow_nonneg hV.le _
    have h₁ : (Q : ℝ) ^ (18 / 5 : ℝ) * (81 * V ^ (-4 : ℝ)) ≤
        1296 * ((N : ℝ) ^ (18 / 5 : ℝ) * V ^ (-4 : ℝ)) := by
      have hm := mul_le_mul_of_nonneg_right hQ18
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 81) hV4)
      nlinarith
    have h₂ : T * (Q : ℝ) ^ (12 / 5 : ℝ) * (81 * V ^ (-4 : ℝ)) ≤
        648 * (T * (N : ℝ) ^ (12 / 5 : ℝ) * V ^ (-4 : ℝ)) := by
      have hm := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hQ12 htail)
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 81) hV4)
      nlinarith
    nlinarith [h₁, h₂, mul_nonneg htail
      (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) (12 / 5 : ℝ)) hV4)]
  calc
    (W.card : ℝ) ≤ 3 * (W'.card : ℝ) := hcardReal
    _ ≤ 3 * (C₀ * T ^ ε *
        ((Q : ℝ) ^ (18 / 5 : ℝ) * (V / 3) ^ (-4 : ℝ) +
          T * (Q : ℝ) ^ (12 / 5 : ℝ) * (V / 3) ^ (-4 : ℝ))) := by
      gcongr
    _ ≤ C * T ^ ε *
        ((N : ℝ) ^ (18 / 5 : ℝ) * V ^ (-4 : ℝ) +
          T * (N : ℝ) ^ (12 / 5 : ℝ) * V ^ (-4 : ℝ)) := by
      dsimp only [C]
      have hcoef : 0 ≤ 3 * (C₀ * T ^ ε) := by positivity
      nlinarith [mul_nonneg hcoef (sub_nonneg.mpr hshape)]

set_option maxHeartbeats 2000000 in
/-- Guth--Maynard Theorem 1.1, with every source reduction and complementary
range discharged.  The proof uses the native Section 12 theorem in the
central range and the native Montgomery--Halasz--Huxley estimates elsewhere. -/
theorem guthMaynardLargeValues_native : GuthMaynardLargeValues := by
  intro ε hε
  let cutoff : GMSmoothCutoff := Classical.choice exists_gmSmoothCutoff
  obtain ⟨Ccrit, Tcrit, hCcrit, hTcrit, hCrit⟩ :=
    gm_source_large_values_critical cutoff ε hε
  let B : ℝ := 2 * Tcrit + 30
  obtain ⟨Clow, hClow, hLowBound⟩ := gm_classical_source_low ε B hε
  obtain ⟨Chigh, hChigh, hHighBound⟩ := gm_classical_source_high ε hε
  obtain ⟨Cnear, hCnear, hNearBound⟩ := gm_classical_source_near_height ε hε
  let C : ℝ := Ccrit + Clow + Chigh + Cnear
  refine ⟨C, 1, by dsimp only [C]; positivity, le_rfl, ?_⟩
  intro N V T b W hN hT hV hb hSep hBase hLarge
  have hTnonneg : 0 ≤ T := zero_le_one.trans hT
  have hTpow : 0 ≤ T ^ ε := Real.rpow_nonneg hTnonneg _
  let S : ℝ :=
    (N : ℝ) ^ 2 * V ^ (-2 : ℝ) +
      (N : ℝ) ^ (18 / 5 : ℝ) * V ^ (-4 : ℝ) +
      T * (N : ℝ) ^ (12 / 5 : ℝ) * V ^ (-4 : ℝ)
  have hS : 0 ≤ S := by dsimp only [S]; positivity
  have hCcritC : Ccrit ≤ C := by dsimp only [C]; linarith
  have hClowC : Clow ≤ C := by dsimp only [C]; linarith
  have hChighC : Chigh ≤ C := by dsimp only [C]; linarith
  have hCnearC : Cnear ≤ C := by dsimp only [C]; linarith
  by_cases hNear : T ≤ 2 * (N : ℝ)
  · have hbound := hNearBound N V T b W hN hT hNear hV hb hSep hBase hLarge
    have hcoef : Cnear * T ^ ε ≤ C * T ^ ε :=
      mul_le_mul_of_nonneg_right hCnearC hTpow
    exact hbound.trans (by
      dsimp only [S] at hS ⊢
      exact mul_le_mul_of_nonneg_right hcoef hS)
  have hTwoNT : 2 * (N : ℝ) ≤ T := (le_of_not_ge hNear)
  have hNT : (N : ℝ) ≤ T := by
    have hn : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    linarith
  by_cases hHigh : (1 / 2 : ℝ) * (N : ℝ) ^ (4 / 5 : ℝ) ≤ V
  · have hbound := hHighBound N V T b W hN hT hNT hV hHigh hb hSep hBase hLarge
    have hcoef : Chigh * T ^ ε ≤ C * T ^ ε :=
      mul_le_mul_of_nonneg_right hChighC hTpow
    exact hbound.trans (by
      dsimp only [S] at hS ⊢
      exact mul_le_mul_of_nonneg_right hcoef hS)
  have hNotHigh : V < (1 / 2 : ℝ) * (N : ℝ) ^ (4 / 5 : ℝ) := lt_of_not_ge hHigh
  by_cases hLow : V ≤ 6 * (N : ℝ) ^ (7 / 10 : ℝ)
  · have hBle : (6 : ℝ) ≤ B := by
      dsimp only [B]
      linarith [hTcrit]
    have hLowB : V ≤ B * (N : ℝ) ^ (7 / 10 : ℝ) := by
      exact hLow.trans (mul_le_mul_of_nonneg_right hBle
        (Real.rpow_nonneg (Nat.cast_nonneg N) _))
    have hbound := hLowBound N V T b W hN hT hNT hV hLowB hb hSep hBase hLarge
    have hcoef : Clow * T ^ ε ≤ C * T ^ ε :=
      mul_le_mul_of_nonneg_right hClowC hTpow
    exact hbound.trans (by
      dsimp only [S] at hS ⊢
      exact mul_le_mul_of_nonneg_right hcoef hS)
  have hCentralLow : 6 * (N : ℝ) ^ (7 / 10 : ℝ) ≤ V := le_of_not_ge hLow
  by_cases hN30 : 30 ≤ N
  · by_cases hNlarge : 2 * Tcrit ≤ (N : ℝ)
    · have hbound := hCrit N V T b W hN30 hNlarge hTwoNT hV hCentralLow
          hNotHigh.le hb hSep hBase hLarge
      have hcriticalShape :
          (N : ℝ) ^ (18 / 5 : ℝ) * V ^ (-4 : ℝ) +
            T * (N : ℝ) ^ (12 / 5 : ℝ) * V ^ (-4 : ℝ) ≤ S := by
        dsimp only [S]
        have hfirst : 0 ≤ (N : ℝ) ^ 2 * V ^ (-2 : ℝ) := by positivity
        linarith
      have hbound' : (W.card : ℝ) ≤ Ccrit * T ^ ε * S :=
        hbound.trans (mul_le_mul_of_nonneg_left hcriticalShape
          (mul_nonneg hCcrit.le hTpow))
      have hcoef : Ccrit * T ^ ε ≤ C * T ^ ε :=
        mul_le_mul_of_nonneg_right hCcritC hTpow
      exact hbound'.trans (mul_le_mul_of_nonneg_right hcoef hS)
    · have hNltB : (N : ℝ) < B := by
        dsimp only [B]
        linarith [lt_of_not_ge hNlarge]
      have hNone : (1 : ℝ) ≤ N := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hN.ne')
      have hpowLeN : (N : ℝ) ^ (4 / 5 : ℝ) ≤ (N : ℝ) := by
        simpa only [Real.rpow_one] using
          Real.rpow_le_rpow_of_exponent_le hNone (by norm_num : (4 / 5 : ℝ) ≤ 1)
      have hpowOne : 1 ≤ (N : ℝ) ^ (7 / 10 : ℝ) :=
        Real.one_le_rpow hNone (by norm_num)
      have hLowB : V ≤ B * (N : ℝ) ^ (7 / 10 : ℝ) := by
        have hBpos : 0 < B := by dsimp only [B]; linarith [hTcrit]
        nlinarith [mul_le_mul_of_nonneg_left hpowOne hBpos.le]
      have hbound := hLowBound N V T b W hN hT hNT hV hLowB hb hSep hBase hLarge
      have hcoef : Clow * T ^ ε ≤ C * T ^ ε :=
        mul_le_mul_of_nonneg_right hClowC hTpow
      exact hbound.trans (by
        dsimp only [S] at hS ⊢
        exact mul_le_mul_of_nonneg_right hcoef hS)
  · have hNltB : (N : ℝ) < B := by
      have hNlt : N < 30 := lt_of_not_ge hN30
      have hcast : (N : ℝ) < 30 := by exact_mod_cast hNlt
      dsimp only [B]
      linarith [hTcrit]
    have hNone : (1 : ℝ) ≤ N := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hN.ne')
    have hpowLeN : (N : ℝ) ^ (4 / 5 : ℝ) ≤ (N : ℝ) := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hNone (by norm_num : (4 / 5 : ℝ) ≤ 1)
    have hpowOne : 1 ≤ (N : ℝ) ^ (7 / 10 : ℝ) :=
      Real.one_le_rpow hNone (by norm_num)
    have hLowB : V ≤ B * (N : ℝ) ^ (7 / 10 : ℝ) := by
      have hBpos : 0 < B := by dsimp only [B]; linarith [hTcrit]
      nlinarith [mul_le_mul_of_nonneg_left hpowOne hBpos.le]
    have hbound := hLowBound N V T b W hN hT hNT hV hLowB hb hSep hBase hLarge
    have hcoef : Clow * T ^ ε ≤ C * T ^ ε :=
      mul_le_mul_of_nonneg_right hClowC hTpow
    exact hbound.trans (by
      dsimp only [S] at hS ⊢
      exact mul_le_mul_of_nonneg_right hcoef hS)

end RiemannZeta.GuthMaynard
