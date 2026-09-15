import Tao2026.BurgessOptimization
import Tao2026.VinogradovMeanValue
import Mathlib.Analysis.Fourier.ZMod

/-!
# Pólya--Vinogradov completion for the large Burgess range

This module develops the finite Fourier bridge used after the rounded Burgess
induction reaches its quadratic no-wrap limit.  The first layer records the
exact primitive Gauss-sum norm and Fourier inversion identity on `ZMod q`.
-/

namespace Tao2026

open Finset Complex
open scoped BigOperators

noncomputable section

/-- A nonprincipal Dirichlet character cannot have level one. -/
theorem one_lt_level_of_dirichletCharacter_ne_one
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) : 1 < q := by
  have hq1 : q ≠ 1 := by
    intro hq
    subst q
    exact hχ (Subsingleton.elim χ 1)
  have hq0 : q ≠ 0 := NeZero.ne q
  omega

/-- The standard Gauss sum of a primitive character has exact
norm `sqrt q`. -/
theorem norm_gaussSum_stdAddChar_eq_sqrt
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hprimitive : DirichletCharacter.IsPrimitive χ) :
    ‖gaussSum χ (ZMod.stdAddChar (N := q))‖ = Real.sqrt q := by
  let τ : ℂ := gaussSum χ (ZMod.stdAddChar (N := q))
  have hfrequency :
      (∑ j : ZMod q, ZMod.stdAddChar j * χ⁻¹ (-j)) = star τ := by
    calc
      (∑ j : ZMod q, ZMod.stdAddChar j * χ⁻¹ (-j)) =
          ∑ j : ZMod q, χ⁻¹ j * (ZMod.stdAddChar j)⁻¹ := by
        exact Fintype.sum_equiv (Equiv.neg (ZMod q)) _ _ (fun j => by
          simp only [Equiv.neg_apply, AddChar.map_neg_eq_inv, inv_inv]
          ring)
      _ = gaussSum χ⁻¹ (ZMod.stdAddChar (N := q))⁻¹ := by
        simp only [gaussSum, AddChar.inv_apply, AddChar.map_neg_eq_inv]
      _ = star τ := by
        simpa only [τ] using
          (star_gaussSum_eq χ (ZMod.stdAddChar (N := q))).symm
  have hdft :
      ZMod.dft (ZMod.dft χ) (-1) = τ * star τ := by
    rw [ZMod.dft_apply]
    simp_rw [hprimitive.fourierTransform_eq_inv_mul_gaussSum]
    simp only [mul_neg, neg_neg, smul_eq_mul, mul_one]
    simp_rw [← mul_assoc]
    rw [← Finset.sum_mul, hfrequency]
    dsimp only [τ]
    ring
  have hdftInv := congrFun (ZMod.dft_dft χ) (-1)
  have hprod : τ * star τ = (q : ℂ) := by
    rw [hdft] at hdftInv
    simpa only [neg_neg, map_one, smul_eq_mul, mul_one] using hdftInv
  have hnorm := congrArg norm hprod
  have hsq : ‖τ‖ ^ 2 = (q : ℝ) := by
    simpa only [norm_mul, norm_star, pow_two, Complex.norm_natCast] using hnorm
  calc
    ‖gaussSum χ (ZMod.stdAddChar (N := q))‖ = ‖τ‖ := by rfl
    _ = Real.sqrt (‖τ‖ ^ 2) := by rw [Real.sqrt_sq (norm_nonneg τ)]
    _ = Real.sqrt q := by rw [hsq]

/-- Exact finite Fourier inversion of a primitive Dirichlet character. -/
theorem primitiveDirichletCharacter_fourier_inversion
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hprimitive : DirichletCharacter.IsPrimitive χ) (n : ZMod q) :
    χ n = (q : ℂ)⁻¹ *
      ∑ k : ZMod q, ZMod.stdAddChar (k * n) *
        (χ⁻¹ (-k) * gaussSum χ (ZMod.stdAddChar (N := q))) := by
  calc
    χ n = (ZMod.dft.symm (ZMod.dft χ)) n := by
      rw [ZMod.dft.symm_apply_apply]
    _ = (q : ℂ)⁻¹ •
        ∑ k : ZMod q, ZMod.stdAddChar (k * n) • ZMod.dft χ k := by
      rw [ZMod.invDFT_apply]
    _ = (q : ℂ)⁻¹ *
        ∑ k : ZMod q, ZMod.stdAddChar (k * n) *
          (χ⁻¹ (-k) * gaussSum χ (ZMod.stdAddChar (N := q))) := by
      simp_rw [hprimitive.fourierTransform_eq_inv_mul_gaussSum]
      simp only [smul_eq_mul]

/-- Exact Fourier completion of a shifted interval character sum. -/
theorem burgessIntervalCharacterSum_eq_fourierCompletion
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hprimitive : DirichletCharacter.IsPrimitive χ) (N H : ℕ) :
    burgessIntervalCharacterSum χ N H =
      (q : ℂ)⁻¹ * gaussSum χ (ZMod.stdAddChar (N := q)) *
        ∑ k : ZMod q, χ⁻¹ (-k) *
          ∑ i ∈ Finset.range H,
            ZMod.stdAddChar (k * ((N + i + 1 : ℕ) : ZMod q)) := by
  unfold burgessIntervalCharacterSum
  calc
    (∑ i ∈ Finset.range H, χ ((N + i + 1 : ℕ) : ZMod q)) =
        ∑ i ∈ Finset.range H, (q : ℂ)⁻¹ *
          ∑ k : ZMod q, ZMod.stdAddChar (k * ((N + i + 1 : ℕ) : ZMod q)) *
            (χ⁻¹ (-k) * gaussSum χ (ZMod.stdAddChar (N := q))) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact primitiveDirichletCharacter_fourier_inversion χ hprimitive _
    _ = (q : ℂ)⁻¹ *
        ∑ i ∈ Finset.range H,
          ∑ k : ZMod q, ZMod.stdAddChar (k * ((N + i + 1 : ℕ) : ZMod q)) *
            (χ⁻¹ (-k) * gaussSum χ (ZMod.stdAddChar (N := q))) := by
      rw [Finset.mul_sum]
    _ = (q : ℂ)⁻¹ *
        ∑ k : ZMod q,
          ∑ i ∈ Finset.range H,
            ZMod.stdAddChar (k * ((N + i + 1 : ℕ) : ZMod q)) *
              (χ⁻¹ (-k) * gaussSum χ (ZMod.stdAddChar (N := q))) := by
      congr 1
      rw [Finset.sum_comm]
    _ = (q : ℂ)⁻¹ * gaussSum χ (ZMod.stdAddChar (N := q)) *
        ∑ k : ZMod q, χ⁻¹ (-k) *
          ∑ i ∈ Finset.range H,
            ZMod.stdAddChar (k * ((N + i + 1 : ℕ) : ZMod q)) := by
      rw [mul_assoc]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      calc
        (∑ i ∈ Finset.range H,
            ZMod.stdAddChar (k * ((N + i + 1 : ℕ) : ZMod q)) *
              (χ⁻¹ (-k) * gaussSum χ (ZMod.stdAddChar (N := q)))) =
            ∑ i ∈ Finset.range H,
              (gaussSum χ (ZMod.stdAddChar (N := q)) * χ⁻¹ (-k)) *
                ZMod.stdAddChar (k * ((N + i + 1 : ℕ) : ZMod q)) := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ = (gaussSum χ (ZMod.stdAddChar (N := q)) * χ⁻¹ (-k)) *
            ∑ i ∈ Finset.range H,
              ZMod.stdAddChar (k * ((N + i + 1 : ℕ) : ZMod q)) := by
          rw [Finset.mul_sum]
        _ = gaussSum χ (ZMod.stdAddChar (N := q)) *
            (χ⁻¹ (-k) * ∑ i ∈ Finset.range H,
              ZMod.stdAddChar (k * ((N + i + 1 : ℕ) : ZMod q))) := by ring

/-- The standard additive character on `ZMod q`, evaluated at a natural
multiple, is the real additive character at the corresponding rational
phase. -/
theorem stdAddChar_mul_natCast_eq_standardAdditiveCharacter
    {q : ℕ} [NeZero q] (k : ZMod q) (n : ℕ) :
    ZMod.stdAddChar (k * (n : ZMod q)) =
      standardAdditiveCharacter ((k.val : ℝ) * (n : ℝ) / (q : ℝ)) := by
  conv_lhs => rw [← ZMod.natCast_zmod_val k]
  norm_cast
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_natCast]
  unfold standardAdditiveCharacter
  push_cast
  congr 1
  ring

/-- Each completed interval kernel is bounded by the uniform geometric-series
majorant at frequency `k / q`. -/
theorem norm_sum_interval_stdAddChar_le_geometricBound
    {q : ℕ} [NeZero q] (k : ZMod q) (N H : ℕ) :
    ‖∑ i ∈ Finset.range H,
        ZMod.stdAddChar (k * ((N + i + 1 : ℕ) : ZMod q))‖ ≤
      vinogradovGeometricSumBound H ((k.val : ℝ) / (q : ℝ)) := by
  have heq :
      (∑ i ∈ Finset.range H,
          ZMod.stdAddChar (k * ((N + i + 1 : ℕ) : ZMod q))) =
        phaseExponentialSum
          (fun i => (i : ℝ) * ((k.val : ℝ) / (q : ℝ)) +
            ((N + 1 : ℕ) : ℝ) * ((k.val : ℝ) / (q : ℝ))) H := by
    unfold phaseExponentialSum phaseExponentialSequence
    apply Finset.sum_congr rfl
    intro i hi
    rw [stdAddChar_mul_natCast_eq_standardAdditiveCharacter]
    congr 1
    push_cast
    ring
  rw [heq]
  unfold vinogradovGeometricSumBound
  by_cases hdist : nearestIntegerDistance ((k.val : ℝ) / (q : ℝ)) = 0
  · rw [if_pos hdist]
    exact norm_phaseExponentialSum_le _ H
  · rw [if_neg hdist]
    exact norm_phaseExponentialSum_affine_le_min_nearestIntegerDistance
      ((k.val : ℝ) / (q : ℝ))
      (((N + 1 : ℕ) : ℝ) * ((k.val : ℝ) / (q : ℝ))) H
      (lt_of_le_of_ne (nearestIntegerDistance_nonneg _) (Ne.symm hdist))

/-- Reindex a sum of residue-frequency majorants by canonical representatives
in `[0,q)`. -/
theorem sum_zmod_vinogradovGeometricSumBound_eq_range
    {q H : ℕ} [NeZero q] :
    (∑ k : ZMod q,
      vinogradovGeometricSumBound H ((k.val : ℝ) / (q : ℝ))) =
      ∑ k ∈ Finset.range q,
        vinogradovGeometricSumBound H ((k : ℝ) / (q : ℝ)) := by
  refine Finset.sum_bij (fun k _ => k.val) ?_ ?_ ?_ ?_
  · intro k hk
    simpa only [Finset.mem_range] using ZMod.val_lt k
  · intro a ha b hb hab
    exact ZMod.val_injective q hab
  · intro n hn
    refine ⟨(n : ZMod q), Finset.mem_univ _, ?_⟩
    exact ZMod.val_cast_of_lt (Finset.mem_range.mp hn)
  · intro k hk
    rfl

/-- Raw symmetric integral-test bound for the `L¹` norm of all residue
frequencies. -/
theorem sum_zmod_vinogradovGeometricSumBound_le_raw
    {q H : ℕ} [NeZero q] (hq : 1 < q) :
    (∑ k : ZMod q,
      vinogradovGeometricSumBound H ((k.val : ℝ) / (q : ℝ))) ≤
      (2 * Nat.ceil (|(1 : ℝ) / (q : ℝ)| * (q : ℝ) + 1 / 2) + 1 : ℝ) *
        (2 * (H : ℝ) + 2 / |(1 : ℝ) / (q : ℝ)| *
          (((harmonic (Nat.ceil (1 / (2 * |(1 : ℝ) / (q : ℝ)|))) : ℚ) : ℝ))) := by
  rw [sum_zmod_vinogradovGeometricSumBound_eq_range]
  let W : Finset ℤ := (Finset.range q).image (fun k : ℕ => (k : ℤ))
  have hsum :
      (∑ k ∈ Finset.range q,
          vinogradovGeometricSumBound H ((k : ℝ) / (q : ℝ))) =
        ∑ x ∈ W,
          vinogradovGeometricSumBound H (((1 : ℝ) / (q : ℝ)) * (x : ℝ)) := by
    dsimp only [W]
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro k hk
      congr 2
      push_cast
      ring
    · intro a ha b hb hab
      exact Int.ofNat_injective hab
  rw [hsum]
  refine (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_).trans
    (sum_vinogradovGeometricSumBound_le H q ((1 : ℝ) / (q : ℝ)) ?_)
  · intro x hx
    dsimp only [W] at hx
    rw [Finset.mem_image] at hx
    rcases hx with ⟨n, hn, rfl⟩
    rw [Finset.mem_Icc]
    have hnlt := Finset.mem_range.mp hn
    constructor
    · omega
    · omega
  · intro x hx hnot
    exact vinogradovGeometricSumBound_nonneg H _
  · positivity

/-- Explicit logarithmic `L¹` frequency estimate.  The deliberately generous
coefficient `10` comes from embedding `[0,q)` into the symmetric interval
`[-q,q]`. -/
theorem sum_zmod_vinogradovGeometricSumBound_le
    {q H : ℕ} [NeZero q] (hq : 1 < q) :
    (∑ k : ZMod q,
      vinogradovGeometricSumBound H ((k.val : ℝ) / (q : ℝ))) ≤
      10 * ((H : ℝ) + (q : ℝ) * (((harmonic q : ℚ) : ℝ))) := by
  have hqreal : (0 : ℝ) < (q : ℝ) := by positivity
  have habs : |(1 : ℝ) / (q : ℝ)| = 1 / (q : ℝ) := abs_of_pos (by positivity)
  have hceilOuter : Nat.ceil
      (|(1 : ℝ) / (q : ℝ)| * (q : ℝ) + 1 / 2) = 2 := by
    rw [habs]
    have hqne : (q : ℝ) ≠ 0 := ne_of_gt hqreal
    field_simp
    norm_num
  have hceilInner : Nat.ceil (1 / (2 * |(1 : ℝ) / (q : ℝ)|)) ≤ q := by
    rw [Nat.ceil_le, habs]
    have hqne : (q : ℝ) ≠ 0 := ne_of_gt hqreal
    field_simp
    norm_num
  have hharm :
      (((harmonic (Nat.ceil (1 / (2 * |(1 : ℝ) / (q : ℝ)|))) : ℚ) : ℝ)) ≤
        (((harmonic q : ℚ) : ℝ)) := by
    exact_mod_cast harmonic_mono_nat hceilInner
  refine (sum_zmod_vinogradovGeometricSumBound_le_raw (H := H) hq).trans ?_
  rw [hceilOuter, habs]
  rw [habs] at hharm
  have hqne : (q : ℝ) ≠ 0 := ne_of_gt hqreal
  have hdiv : 2 / (1 / (q : ℝ)) = 2 * (q : ℝ) := by field_simp
  rw [hdiv]
  have hH : 0 ≤ (H : ℝ) := by positivity
  have hharm0 : 0 ≤ (((harmonic q : ℚ) : ℝ)) := by
    exact_mod_cast (show (0 : ℚ) ≤ harmonic q by
      unfold harmonic
      positivity)
  nlinarith

/-- Pólya--Vinogradov completion for primitive nonprincipal characters, with
an explicit absolute coefficient. -/
theorem norm_burgessIntervalCharacterSum_le_polyaVinogradov
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hprimitive : DirichletCharacter.IsPrimitive χ) (hχ : χ ≠ 1)
    (N H : ℕ) (hHq : H < q) :
    ‖burgessIntervalCharacterSum χ N H‖ ≤
      10 * Real.sqrt (q : ℝ) *
        (1 + (((harmonic q : ℚ) : ℝ))) := by
  have hq : 1 < q := one_lt_level_of_dirichletCharacter_ne_one χ hχ
  rw [burgessIntervalCharacterSum_eq_fourierCompletion χ hprimitive N H]
  have hfreq :
      ‖∑ k : ZMod q, χ⁻¹ (-k) *
          ∑ i ∈ Finset.range H,
            ZMod.stdAddChar (k * ((N + i + 1 : ℕ) : ZMod q))‖ ≤
        10 * ((H : ℝ) + (q : ℝ) * (((harmonic q : ℚ) : ℝ))) := by
    calc
      ‖∑ k : ZMod q, χ⁻¹ (-k) *
          ∑ i ∈ Finset.range H,
            ZMod.stdAddChar (k * ((N + i + 1 : ℕ) : ZMod q))‖ ≤
          ∑ k : ZMod q, ‖χ⁻¹ (-k) *
            ∑ i ∈ Finset.range H,
              ZMod.stdAddChar (k * ((N + i + 1 : ℕ) : ZMod q))‖ :=
        norm_sum_le _ _
      _ ≤ ∑ k : ZMod q,
          vinogradovGeometricSumBound H ((k.val : ℝ) / (q : ℝ)) := by
        apply Finset.sum_le_sum
        intro k hk
        rw [norm_mul]
        calc
          ‖χ⁻¹ (-k)‖ * ‖∑ i ∈ Finset.range H,
              ZMod.stdAddChar (k * ((N + i + 1 : ℕ) : ZMod q))‖ ≤
              1 * ‖∑ i ∈ Finset.range H,
                ZMod.stdAddChar (k * ((N + i + 1 : ℕ) : ZMod q))‖ := by
            gcongr
            exact DirichletCharacter.norm_le_one χ⁻¹ (-k)
          _ ≤ vinogradovGeometricSumBound H ((k.val : ℝ) / (q : ℝ)) := by
            simpa using norm_sum_interval_stdAddChar_le_geometricBound k N H
      _ ≤ 10 * ((H : ℝ) + (q : ℝ) * (((harmonic q : ℚ) : ℝ))) :=
        sum_zmod_vinogradovGeometricSumBound_le hq
  rw [norm_mul, norm_mul, norm_inv,
    norm_gaussSum_stdAddChar_eq_sqrt χ hprimitive, Complex.norm_natCast]
  have hqreal : (0 : ℝ) < (q : ℝ) := by positivity
  have hHreal : (H : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.le_of_lt hHq
  have hharm : 0 ≤ (((harmonic q : ℚ) : ℝ)) := by
    exact_mod_cast (show (0 : ℚ) ≤ harmonic q by
      unfold harmonic
      positivity)
  have hsqrt : 0 ≤ Real.sqrt (q : ℝ) := Real.sqrt_nonneg _
  calc
    (↑q)⁻¹ * Real.sqrt (q : ℝ) *
        ‖∑ k : ZMod q, χ⁻¹ (-k) *
          ∑ i ∈ Finset.range H,
            ZMod.stdAddChar (k * ((N + i + 1 : ℕ) : ZMod q))‖ ≤
      (↑q)⁻¹ * Real.sqrt (q : ℝ) *
        (10 * ((H : ℝ) + (q : ℝ) * (((harmonic q : ℚ) : ℝ)))) := by
      gcongr
    _ ≤ 10 * Real.sqrt (q : ℝ) *
        (1 + (((harmonic q : ℚ) : ℝ))) := by
      apply le_of_mul_le_mul_left ?_ hqreal
      field_simp
      nlinarith

/-- Absorb the logarithmic Pólya--Vinogradov loss into an arbitrary positive
conductor power. -/
theorem norm_burgessIntervalCharacterSum_le_polyaVinogradov_rpow
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hprimitive : DirichletCharacter.IsPrimitive χ) (hχ : χ ≠ 1)
    {η : ℝ} (hη : 0 < η) (N H : ℕ) (hHq : H < q) :
    ‖burgessIntervalCharacterSum χ N H‖ ≤
      (10 * (2 + η⁻¹)) * (q : ℝ) ^ ((1 / 2 : ℝ) + η) := by
  have hq : 1 ≤ q := (one_lt_level_of_dirichletCharacter_ne_one χ hχ).le
  have hqpos : (0 : ℝ) < (q : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hharm := harmonic_cast_le_const_mul_rpow_of_le hη (A := q) (q := q) le_rfl hq
  have hqpowOne : (1 : ℝ) ≤ (q : ℝ) ^ η := by
    exact Real.one_le_rpow (by exact_mod_cast hq) hη.le
  have honeHarm :
      1 + (((harmonic q : ℚ) : ℝ)) ≤ (2 + η⁻¹) * (q : ℝ) ^ η := by
    nlinarith [inv_nonneg.mpr hη.le]
  refine (norm_burgessIntervalCharacterSum_le_polyaVinogradov
    χ hprimitive hχ N H hHq).trans ?_
  calc
    10 * Real.sqrt (q : ℝ) * (1 + (((harmonic q : ℚ) : ℝ))) ≤
        10 * Real.sqrt (q : ℝ) * ((2 + η⁻¹) * (q : ℝ) ^ η) := by
      gcongr
    _ = (10 * (2 + η⁻¹)) * (q : ℝ) ^ ((1 / 2 : ℝ) + η) := by
      rw [Real.sqrt_eq_rpow, Real.rpow_add hqpos]
      ring

/-- Failure of the quadratic no-wrap condition supplies precisely the
`q^(45/98)` length factor needed to turn Pólya--Vinogradov into the `r = 7`
Burgess monomial. -/
theorem burgessFourteenthLargeRange_rpow_le
    {q H : ℕ} [NeZero q] (η : ℝ)
    (hB : (q : ℝ) ^ (1 / 14 : ℝ) / 2 ≤
      (burgessFourteenthShiftLength q : ℝ))
    (hnotquad : ¬ 2 * H * H ≤ q * 128 * burgessFourteenthShiftLength q) :
    (q : ℝ) ^ ((1 / 2 : ℝ) + η) ≤
      (H : ℝ) ^ (6 / 7 : ℝ) * (q : ℝ) ^ ((2 / 49 : ℝ) + η) := by
  have hqpos : (0 : ℝ) < (q : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hquadlt : q * 128 * burgessFourteenthShiftLength q < 2 * H * H :=
    Nat.lt_of_not_ge hnotquad
  have hquadltR :
      (q : ℝ) * 128 * (burgessFourteenthShiftLength q : ℝ) <
        2 * (H : ℝ) * (H : ℝ) := by exact_mod_cast hquadlt
  have hscaleProduct :
      (q : ℝ) * (q : ℝ) ^ (1 / 14 : ℝ) ≤ (H : ℝ) * (H : ℝ) := by
    have hnonneg : 0 ≤ (q : ℝ) * (q : ℝ) ^ (1 / 14 : ℝ) := by positivity
    have hlower :
        (q : ℝ) * 128 * ((q : ℝ) ^ (1 / 14 : ℝ) / 2) ≤
          (q : ℝ) * 128 * (burgessFourteenthShiftLength q : ℝ) := by
      gcongr
    nlinarith
  have hscale :
      (q : ℝ) ^ (15 / 14 : ℝ) ≤ (H : ℝ) ^ (2 : ℝ) := by
    calc
      (q : ℝ) ^ (15 / 14 : ℝ) =
          (q : ℝ) * (q : ℝ) ^ (1 / 14 : ℝ) := by
        rw [show (15 / 14 : ℝ) = 1 + 1 / 14 by norm_num,
          Real.rpow_add hqpos, Real.rpow_one]
      _ ≤ (H : ℝ) * (H : ℝ) := hscaleProduct
      _ = (H : ℝ) ^ (2 : ℝ) := by rw [Real.rpow_two]; ring
  have hroot := Real.rpow_le_rpow (Real.rpow_nonneg (Nat.cast_nonneg q) _)
    hscale (show (0 : ℝ) ≤ 3 / 7 by norm_num)
  rw [← Real.rpow_mul (Nat.cast_nonneg q),
    ← Real.rpow_mul (Nat.cast_nonneg H)] at hroot
  have hleft : (15 / 14 : ℝ) * (3 / 7 : ℝ) = 45 / 98 := by norm_num
  have hright : (2 : ℝ) * (3 / 7 : ℝ) = 6 / 7 := by norm_num
  rw [hleft, hright] at hroot
  calc
    (q : ℝ) ^ ((1 / 2 : ℝ) + η) =
        (q : ℝ) ^ (45 / 98 : ℝ) *
          (q : ℝ) ^ ((2 / 49 : ℝ) + η) := by
      rw [← Real.rpow_add hqpos]
      congr 1
      ring
    _ ≤ (H : ℝ) ^ (6 / 7 : ℝ) *
          (q : ℝ) ^ ((2 / 49 : ℝ) + η) := by
      gcongr

/-- Eventually, Pólya--Vinogradov closes every primitive interval beyond the
quadratic no-wrap range, with the same Burgess monomial. -/
theorem eventually_norm_burgessIntervalCharacterSum_le_large
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ q : ℕ in Filter.atTop, ∀ (χ : DirichletCharacter ℂ q),
      DirichletCharacter.IsPrimitive χ → χ ≠ 1 →
      ∀ H N : ℕ, H < q →
        ¬ 2 * H * H ≤ q * 128 * burgessFourteenthShiftLength q →
        ‖burgessIntervalCharacterSum χ N H‖ ≤
          (10 * (2 + η⁻¹)) * (H : ℝ) ^ (6 / 7 : ℝ) *
            (q : ℝ) ^ ((2 / 49 : ℝ) + η) := by
  filter_upwards [eventually_burgessFourteenthShiftLength_bounds] with q hB
  intro χ hprimitive hχ H N hHq hnotquad
  have hq0 : q ≠ 0 := by
    intro h
    subst q
    omega
  letI : NeZero q := ⟨hq0⟩
  refine (norm_burgessIntervalCharacterSum_le_polyaVinogradov_rpow
    χ hprimitive hχ hη N H hHq).trans ?_
  have hconstant : 0 ≤ 10 * (2 + η⁻¹) := by
    have hinv : 0 < η⁻¹ := inv_pos.mpr hη
    positivity
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
    (burgessFourteenthLargeRange_rpow_le η hB.2 hnotquad) hconstant

/-- The complete-Weil input and Pólya--Vinogradov together cover the entire
eventual primitive Burgess core range. -/
theorem exists_eventually_norm_burgessIntervalCharacterSum_le_core_of_completeWeil
    (hweil : TaoPrimitiveCubefreeBurgessCompleteWeilBoundRSeven)
    {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ᶠ q : ℕ in Filter.atTop, ∀ (χ : DirichletCharacter ℂ q),
        TaoCubefree q → DirichletCharacter.IsPrimitive χ → χ ≠ 1 →
        ∀ H N : ℕ, H < q →
          (q : ℝ) ^ ((2 / 49 : ℝ) + η) <
            (H : ℝ) ^ (1 / 7 : ℝ) →
          ‖burgessIntervalCharacterSum χ N H‖ ≤
            C * (H : ℝ) ^ (6 / 7 : ℝ) *
              (q : ℝ) ^ ((2 / 49 : ℝ) + η) := by
  obtain ⟨Cm, hCm, hmedium⟩ :=
    exists_eventually_norm_burgessIntervalCharacterSum_le_medium_of_completeWeil
      hweil hη
  let Cl : ℝ := 10 * (2 + η⁻¹)
  let C : ℝ := max 1 (max Cm Cl)
  have hC : 1 ≤ C := le_max_left _ _
  refine ⟨C, hC, ?_⟩
  filter_upwards [hmedium,
    eventually_norm_burgessIntervalCharacterSum_le_large hη] with q hmediumq hlargeq
  intro χ hcube hprimitive hχ H N hHq hcore
  by_cases hquad : 2 * H * H ≤ q * 128 * burgessFourteenthShiftLength q
  · have hbound := hmediumq χ hcube hprimitive H N hHq hcore hquad
    have hCmC : Cm ≤ C := le_trans (le_max_left _ _) (le_max_right _ _)
    exact hbound.trans (by
      have hHpow : 0 ≤ (H : ℝ) ^ (6 / 7 : ℝ) := by positivity
      have hqpow : 0 ≤ (q : ℝ) ^ ((2 / 49 : ℝ) + η) := by positivity
      gcongr)

  · have hbound := hlargeq χ hprimitive hχ H N hHq hquad
    have hClC : Cl ≤ C := le_trans (le_max_right _ _) (le_max_right _ _)
    exact hbound.trans (by
      dsimp only [Cl] at hClC ⊢
      have hHpow : 0 ≤ (H : ℝ) ^ (6 / 7 : ℝ) := by positivity
      have hqpow : 0 ≤ (q : ℝ) ^ ((2 / 49 : ℝ) + η) := by positivity
      gcongr)

/-- On a bounded conductor range, the trivial interval estimate is absorbed
by the Burgess monomial with a coefficient equal to the conductor cutoff. -/
theorem natCast_le_cutoff_mul_burgessMonomial
    {Q H q : ℕ} {η : ℝ} (hη : 0 < η)
    (hqOne : 1 ≤ q) (hHq : H < q) (hqQ : q ≤ Q) :
    (H : ℝ) ≤ (Q : ℝ) * (H : ℝ) ^ (6 / 7 : ℝ) *
      (q : ℝ) ^ ((2 / 49 : ℝ) + η) := by
  by_cases hH0 : H = 0
  · simp [hH0]
  have hHpos : (0 : ℝ) < (H : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hH0
  have hHqR : (H : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.le_of_lt hHq
  have hqOneR : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hqOne
  have hqQR : (q : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hqQ
  have hrootHq :
      (H : ℝ) ^ (1 / 7 : ℝ) ≤ (q : ℝ) ^ (1 / 7 : ℝ) :=
    Real.rpow_le_rpow hHpos.le hHqR (by norm_num)
  have hrootq : (q : ℝ) ^ (1 / 7 : ℝ) ≤ (q : ℝ) :=
    Real.rpow_le_self_of_one_le hqOneR (by norm_num)
  have hqpowOne : (1 : ℝ) ≤ (q : ℝ) ^ ((2 / 49 : ℝ) + η) :=
    Real.one_le_rpow hqOneR (by linarith)
  have hrootBound :
      (H : ℝ) ^ (1 / 7 : ℝ) ≤
        (Q : ℝ) * (q : ℝ) ^ ((2 / 49 : ℝ) + η) := by
    calc
      (H : ℝ) ^ (1 / 7 : ℝ) ≤ (q : ℝ) ^ (1 / 7 : ℝ) := hrootHq
      _ ≤ (q : ℝ) := hrootq
      _ ≤ (Q : ℝ) := hqQR
      _ ≤ (Q : ℝ) * (q : ℝ) ^ ((2 / 49 : ℝ) + η) := by
        nlinarith
  calc
    (H : ℝ) = (H : ℝ) ^ (6 / 7 : ℝ) * (H : ℝ) ^ (1 / 7 : ℝ) := by
      rw [← Real.rpow_add hHpos]
      norm_num
    _ ≤ (H : ℝ) ^ (6 / 7 : ℝ) *
        ((Q : ℝ) * (q : ℝ) ^ ((2 / 49 : ℝ) + η)) := by
      gcongr
    _ = (Q : ℝ) * (H : ℝ) ^ (6 / 7 : ℝ) *
        (q : ℝ) ^ ((2 / 49 : ℝ) + η) := by ring

/-- Remove the eventual-conductor qualifier by absorbing the finitely many
small conductors into the Burgess coefficient. -/
theorem exists_taoPrimitiveCubefreeBurgessRSevenCoreBound_of_completeWeil
    (hweil : TaoPrimitiveCubefreeBurgessCompleteWeilBoundRSeven)
    {η : ℝ} (hη : 0 < η) :
    ∃ A : ℝ, 1 ≤ A ∧ TaoPrimitiveCubefreeBurgessRSevenCoreBound A η := by
  obtain ⟨C, hC, hevent⟩ :=
    exists_eventually_norm_burgessIntervalCharacterSum_le_core_of_completeWeil
      hweil hη
  rw [Filter.eventually_atTop] at hevent
  obtain ⟨Q, hQ⟩ := hevent
  let A : ℝ := max C (Q : ℝ)
  have hA : 1 ≤ A := hC.trans (le_max_left _ _)
  refine ⟨A, hA, ?_⟩
  intro H q χ hcube hprimitive hχ hHq hcore
  have hq0 : q ≠ 0 := hcube.ne_zero
  letI : NeZero q := ⟨hq0⟩
  rw [← burgessIntervalCharacterSum_zero]
  by_cases hlarge : Q ≤ q
  · exact hQ q hlarge χ hcube hprimitive hχ H 0 hHq hcore |>.trans (by
      have hCA : C ≤ A := le_max_left _ _
      have hHpow : 0 ≤ (H : ℝ) ^ (6 / 7 : ℝ) := by positivity
      have hqpow : 0 ≤ (q : ℝ) ^ ((2 / 49 : ℝ) + η) := by positivity
      gcongr)
  · have hqQ : q ≤ Q := Nat.le_of_lt (Nat.lt_of_not_ge hlarge)
    calc
      ‖burgessIntervalCharacterSum χ 0 H‖ ≤ (H : ℝ) :=
        norm_burgessIntervalCharacterSum_le χ
      _ ≤ (Q : ℝ) * (H : ℝ) ^ (6 / 7 : ℝ) *
          (q : ℝ) ^ ((2 / 49 : ℝ) + η) :=
        natCast_le_cutoff_mul_burgessMonomial hη
          (Nat.one_le_iff_ne_zero.mpr hq0) hHq hqQ
      _ ≤ A * (H : ℝ) ^ (6 / 7 : ℝ) *
          (q : ℝ) ^ ((2 / 49 : ℝ) + η) := by
        have hQA : (Q : ℝ) ≤ A := le_max_right _ _
        have hHpow : 0 ≤ (H : ℝ) ^ (6 / 7 : ℝ) := by positivity
        have hqpow : 0 ≤ (q : ℝ) ^ ((2 / 49 : ℝ) + η) := by positivity
        gcongr

/-- Complete-Weil plus Fourier completion yields the full primitive cubefree
`r = 7` Burgess estimate, uniformly for every prefix. -/
theorem exists_taoPrimitiveCubefreeBurgessRSevenBound_of_completeWeil
    (hweil : TaoPrimitiveCubefreeBurgessCompleteWeilBoundRSeven)
    {η : ℝ} (hη : 0 < η) :
    ∃ A : ℝ, 1 ≤ A ∧ TaoPrimitiveCubefreeBurgessRSevenBound A η := by
  obtain ⟨A, hA, hcore⟩ :=
    exists_taoPrimitiveCubefreeBurgessRSevenCoreBound_of_completeWeil hweil hη
  exact ⟨A, hA, hcore.toAllPrefixes hA⟩

/-- The same result transferred from primitive to all cubefree characters. -/
theorem exists_taoCubefreeBurgessRSevenBound_of_completeWeil
    (hweil : TaoPrimitiveCubefreeBurgessCompleteWeilBoundRSeven)
    {η : ℝ} (hη : 0 < η) :
    ∃ A : ℝ, ∃ H₀ : ℕ, TaoCubefreeBurgessRSevenBound A η H₀ := by
  obtain ⟨Ap, hAp, hp⟩ :=
    exists_taoPrimitiveCubefreeBurgessRSevenBound_of_completeWeil
      hweil (half_pos hη)
  exact ⟨_, _, hp.toAllCharacters (zero_le_one.trans hAp) hη⟩

/-- Complete-Weil therefore supplies the exact decimal Burgess contract used
by Tao's exceptional-character sieve. -/
theorem exists_taoExplicitCubefreeBurgessBound_of_completeWeil
    (hweil : TaoPrimitiveCubefreeBurgessCompleteWeilBoundRSeven) :
    ∃ C : ℝ, TaoExplicitCubefreeBurgessBound C 1 := by
  have hη : 0 < taoBurgessRSevenEpsilon / 2 := by
    norm_num [taoBurgessRSevenEpsilon]
  obtain ⟨A, hA, hburgess⟩ :=
    exists_taoPrimitiveCubefreeBurgessRSevenBound_of_completeWeil hweil hη
  exact ⟨_, hburgess.toExplicit (zero_le_one.trans hA)⟩

end

end Tao2026
