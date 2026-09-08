import RiemannZeta.GuthMaynard.ExtractSeparated
import Mathlib.Analysis.Complex.PhragmenLindelof
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

open Complex Set
open scoped BigOperators

namespace RiemannZeta.GuthMaynard

open Filter Asymptotics PhragmenLindelof

/-- The sum of the norms of the coefficients of one detector polynomial. -/
noncomputable def detectorMass (N : ℕ) (T : ℝ) : ℝ :=
  ∑ n ∈ Finset.Ioc N (2 * N), ‖detectorCoeff n T‖

/-- In the closed right half-plane, the detector is bounded by its coefficient mass. -/
lemma norm_detectPoly_le_detectorMass (N : ℕ) (s : ℂ) (T : ℝ) (hs : 0 ≤ s.re) :
    ‖detectPoly N s T‖ ≤ detectorMass N T := by
  unfold detectPoly detectorMass
  calc
    ‖∑ n ∈ Finset.Ioc N (2 * N), detectorCoeff n T * (n : ℂ) ^ (-s)‖
        ≤ ∑ n ∈ Finset.Ioc N (2 * N),
            ‖detectorCoeff n T * (n : ℂ) ^ (-s)‖ := by
          exact norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Ioc N (2 * N), ‖detectorCoeff n T‖ := by
      gcongr with n hn
      rw [norm_mul, Complex.norm_natCast_cpow_of_pos]
      · exact mul_le_of_le_one_right (norm_nonneg _) <|
          Real.rpow_le_one_of_one_le_of_nonpos (by
            rw [Finset.mem_Ioc] at hn
            have : 1 ≤ n := by omega
            exact_mod_cast this) (by simp [hs])
      · rw [Finset.mem_Ioc] at hn
        have : 0 < n := by omega
        exact_mod_cast this

/-- Translating the complex argument of a finite detector polynomial gives an entire function. -/
lemma differentiable_detectPoly_add (N : ℕ) (z : ℂ) (T : ℝ) :
    Differentiable ℂ (fun w : ℂ => detectPoly N (z + w) T) := by
  unfold detectPoly
  fun_prop (disch := aesop)

/-- The rationally localized detector used to move a large value to a fixed vertical line. -/
noncomputable def localizedDetector
    (N k : ℕ) (z : ℂ) (T H : ℝ) (w : ℂ) : ℂ :=
  (((H : ℂ) / (H + w)) ^ k) * detectPoly N (z + w) T

/-- The rational localization factor has norm at most one in the closed right half-plane. -/
lemma localizer_norm_le_one (k : ℕ) (H : ℝ) (hH : 0 < H) (w : ℂ)
    (hw : 0 ≤ w.re) : ‖((H : ℂ) / (H + w)) ^ k‖ ≤ 1 := by
  rw [norm_pow, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hH]
  have hden : H ≤ ‖(H : ℂ) + w‖ := by
    calc
      H ≤ |H + w.re| := by
        rw [abs_of_nonneg (by linarith)]
        linarith
      _ = |((H : ℂ) + w).re| := by simp
      _ ≤ ‖(H : ℂ) + w‖ := abs_re_le_norm _
  have hratio : H / ‖(H : ℂ) + w‖ ≤ 1 :=
    (div_le_one (hH.trans_le hden)).mpr hden
  exact pow_le_one₀ (by positivity) hratio

/-- The localized detector remains bounded by the detector coefficient mass. -/
lemma localizedDetector_le_detectorMass (N k : ℕ) (z w : ℂ) (T H : ℝ)
    (hH : 0 < H) (hz : 0 ≤ z.re) (hw : 0 ≤ w.re) :
    ‖localizedDetector N k z T H w‖ ≤ detectorMass N T := by
  rw [localizedDetector, norm_mul]
  calc
    ‖((H : ℂ) / (H + w)) ^ k‖ * ‖detectPoly N (z + w) T‖
        ≤ 1 * detectorMass N T := by
      gcongr
      · exact localizer_norm_le_one k H hH w hw
      · exact norm_detectPoly_le_detectorMass N (z + w) T (by simp; linarith)
    _ = detectorMass N T := one_mul _

/-- Phragmén--Lindelöf transfers a uniform boundary estimate to the right half-plane. -/
theorem localizedDetector_halfPlane_bound
    (N k : ℕ) (z : ℂ) (T H C : ℝ) (hH : 0 < H) (hz : 0 ≤ z.re)
    (hBoundary : ∀ y : ℝ, ‖localizedDetector N k z T H (y * I)‖ ≤ C)
    (w : ℂ) (hw : 0 ≤ w.re) :
    ‖localizedDetector N k z T H w‖ ≤ C := by
  apply PhragmenLindelof.right_half_plane_of_bounded_on_real
      (f := localizedDetector N k z T H)
  · exact (by
      unfold localizedDetector
      apply DifferentiableOn.diffContOnCl
      intro u hu
      have hne : (H : ℂ) + u ≠ 0 := by
        intro h
        have hre := congrArg Complex.re h
        simp only [add_re, ofReal_re, zero_re] at hre
        rw [closure_setOf_lt_re] at hu
        change 0 ≤ u.re at hu
        linarith
      exact ((((differentiableAt_const (c := (H : ℂ))).div
        ((differentiableAt_const (c := (H : ℂ))).add differentiableAt_id) hne).pow k).mul
          (differentiable_detectPoly_add N z T u)).differentiableWithinAt)
  · refine ⟨1, by norm_num, 0, ?_⟩
    apply Asymptotics.IsBigO.of_bound (detectorMass N T)
    have hopen : ∀ᶠ u in (Bornology.cobounded ℂ ⊓ Filter.principal {u : ℂ | 0 < u.re}),
        0 < u.re := Filter.le_principal_iff.mp inf_le_right
    filter_upwards [hopen] with u hu
    simp only [zero_mul, Real.exp_zero, norm_one, mul_one]
    exact localizedDetector_le_detectorMass N k z u T H hH hz hu.le
  · refine ⟨detectorMass N T, ?_⟩
    rw [eventually_map]
    exact Filter.eventually_atTop.mpr ⟨0, fun x hx =>
      localizedDetector_le_detectorMass N k z x T H hH hz (by simpa using hx)⟩
  · exact hBoundary
  · exact hw

/-- Away from the central boundary segment, the rational localizer decays polynomially. -/
lemma localizer_norm_boundary_le (k : ℕ) (H R y : ℝ)
    (hH : 0 < H) (hR : 0 < R) (hy : R ≤ |y|) :
    ‖((H : ℂ) / (H + (y : ℂ) * I)) ^ k‖ ≤ (H / R) ^ k := by
  rw [norm_pow, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hH]
  have hden : |y| ≤ ‖(H : ℂ) + (y : ℂ) * I‖ := by
    calc
      |y| = |((H : ℂ) + (y : ℂ) * I).im| := by simp
      _ ≤ ‖(H : ℂ) + (y : ℂ) * I‖ := abs_im_le_norm _
  have hdenPos : 0 < ‖(H : ℂ) + (y : ℂ) * I‖ :=
    lt_of_lt_of_le (hR.trans_le hy) hden
  have hratio : H / ‖(H : ℂ) + (y : ℂ) * I‖ ≤ H / R := by
    exact div_le_div_of_nonneg_left hH.le hR (hy.trans hden)
  exact pow_le_pow_left₀ (by positivity) hratio k

/--
If the localized detector is large at a nonnegative real displacement and the
exterior boundary contribution is smaller, a comparably large boundary value
occurs within distance `R`.
-/
theorem exists_nearby_large_value
    (N k : ℕ) (z : ℂ) (T H R A : ℝ) (a : ℝ)
    (hH : 0 < H) (hR : 0 < R) (hA : 0 < A) (hz : 0 ≤ z.re) (ha : 0 ≤ a)
    (hLarge : A ≤ ‖detectPoly N (z + a) T‖)
    (hFactor : 3 / 4 < ‖((H : ℂ) / (H + (a : ℂ))) ^ k‖)
    (hExterior : detectorMass N T * (H / R) ^ k < (3 / 4) * A) :
    ∃ y : ℝ, |y| ≤ R ∧ (3 / 4) * A ≤ ‖detectPoly N (z + y * I) T‖ := by
  by_contra! hNo
  have hBoundary : ∀ y : ℝ,
      ‖localizedDetector N k z T H (y * I)‖ ≤ (3 / 4) * A := by
    intro y
    rw [localizedDetector, norm_mul]
    by_cases hy : |y| ≤ R
    · calc
        ‖((H : ℂ) / (H + (y : ℂ) * I)) ^ k‖ *
              ‖detectPoly N (z + (y : ℂ) * I) T‖
            ≤ 1 * ((3 / 4) * A) := by
              gcongr
              · exact localizer_norm_le_one k H hH (y * I) (by simp)
              · exact (hNo y hy).le
        _ = (3 / 4) * A := one_mul _
    · have hyR : R ≤ |y| := le_of_lt (lt_of_not_ge hy)
      calc
        ‖((H : ℂ) / (H + (y : ℂ) * I)) ^ k‖ *
              ‖detectPoly N (z + (y : ℂ) * I) T‖
            ≤ (H / R) ^ k * detectorMass N T := by
              gcongr
              · exact localizer_norm_boundary_le k H R y hH hR hyR
              · exact norm_detectPoly_le_detectorMass N (z + y * I) T (by simp [hz])
        _ = detectorMass N T * (H / R) ^ k := by ring
        _ ≤ (3 / 4) * A := hExterior.le
  have hPL := localizedDetector_halfPlane_bound N k z T H ((3 / 4) * A)
    hH hz hBoundary (a : ℂ) (by simpa using ha)
  rw [localizedDetector, norm_mul] at hPL
  have hStrict : (3 / 4) * A <
      ‖((H : ℂ) / (H + (a : ℂ))) ^ k‖ * ‖detectPoly N (z + a) T‖ := by
    calc
      (3 / 4) * A < ‖((H : ℂ) / (H + (a : ℂ))) ^ k‖ * A := by
        gcongr
      _ ≤ ‖((H : ℂ) / (H + (a : ℂ))) ^ k‖ *
          ‖detectPoly N (z + a) T‖ := by gcongr
  exact (not_lt_of_ge hPL) hStrict

/-- The detector cutoff is at most `3T` once `T ≥ 1`. -/
lemma detectorCutoff_le_three_mul (T : ℝ) (hT : 1 ≤ T) :
    (detectorCutoff T : ℝ) ≤ 3 * T := by
  have hT0 : 0 ≤ T := zero_le_one.trans hT
  have hpow0 : 0 ≤ T ^ (1 / 100 : ℝ) := Real.rpow_nonneg hT0 _
  have hpow : T ^ (1 / 100 : ℝ) ≤ T := by
    calc
      T ^ (1 / 100 : ℝ) ≤ T ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hT (by norm_num)
      _ = T := by simp
  rw [detectorCutoff]
  push_cast
  calc
    (⌊2 * T ^ (1 / 100 : ℝ)⌋₊ : ℝ) + 1
        ≤ 2 * T ^ (1 / 100 : ℝ) + 1 := by
          gcongr
          exact Nat.floor_le (by positivity)
    _ ≤ 2 * T + T := by linarith
    _ = 3 * T := by ring

/-- At every admissible Type-I scale, the detector coefficient mass is at most `T⁷`. -/
lemma detectorMass_le_pow_seven (T : ℝ) (N : ℕ)
    (hT : Real.exp 2 ≤ T) (hN : (N : ℝ) ≤ detectorScaleUpper T) :
    detectorMass N T ≤ T ^ (7 : ℕ) := by
  have hT1 : 1 ≤ T := by
    have : (1 : ℝ) < Real.exp 2 := by
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.mpr (by norm_num)
    exact (this.trans_le hT).le
  have hUpper : detectorScaleUpper T ≤ T ^ (3 : ℕ) := by
    calc
      detectorScaleUpper T ≤ T ^ (5 / 2 : ℝ) := detectorScaleUpper_le_rpow T hT1
      _ ≤ T ^ (3 : ℝ) := Real.rpow_le_rpow_of_exponent_le hT1 (by norm_num)
      _ = T ^ (3 : ℕ) := by norm_num
  have hCut := detectorCutoff_le_three_mul T hT1
  calc
    detectorMass N T
        ≤ ∑ _n ∈ Finset.Ioc N (2 * N), (detectorCutoff T : ℝ) := by
          apply Finset.sum_le_sum
          intro n hn
          exact norm_detectorCoeff_le_cutoff n T hT1
    _ = N * (detectorCutoff T : ℝ) := by
      have hcard : (Finset.Ioc N (2 * N)).card = N := by
        rw [Nat.card_Ioc]
        omega
      simp [hcard]
    _ ≤ T ^ (3 : ℕ) * (3 * T) := by
      gcongr
      exact hN.trans hUpper
    _ ≤ T ^ (3 : ℕ) * T ^ (4 : ℕ) := by
      gcongr
      nlinarith [show (3 : ℝ) ≤ T ^ 3 by
        calc
          3 ≤ Real.exp 2 := by
            convert (Real.add_one_lt_exp (by norm_num : (2 : ℝ) ≠ 0)).le using 1
            norm_num
          _ ≤ T := hT
          _ ≤ T ^ 3 := by nlinarith [hT1, sq_nonneg T]]
    _ = T ^ (7 : ℕ) := by ring

/-- For a bounded horizontal displacement, the localizer loses less than one quarter. -/
lemma localizer_factor_gt_three_fourths (k : ℕ) (H a : ℝ)
    (hH : 0 < H) (ha : 0 ≤ a) (haOne : a ≤ 1) (hHk : 4 * (k : ℝ) < H) :
    3 / 4 < ‖((H : ℂ) / (H + (a : ℂ))) ^ k‖ := by
  have hHa : 0 < H + a := by linarith
  rw [norm_pow, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hH]
  have hnorm : ‖(H : ℂ) + (a : ℂ)‖ = H + a := by
    rw [← ofReal_add, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hHa]
  rw [hnorm]
  let r : ℝ := H / (H + a)
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hBernoulli : 1 + (k : ℝ) * (r - 1) ≤ r ^ k := by
    exact one_add_mul_sub_le_pow (by linarith) k
  have hFrac : (k : ℝ) * a / (H + a) < 1 / 4 := by
    have hkA : (k : ℝ) * a ≤ k := by
      have hk0 : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
      nlinarith
    have hDiv : (k : ℝ) * a / (H + a) ≤ (k : ℝ) / H := by
      rw [div_le_div_iff₀ hHa hH]
      have hk0 : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
      nlinarith [mul_nonneg hk0 ha]
    have hkDiv : (k : ℝ) / H < 1 / 4 := by
      rw [div_lt_iff₀ hH]
      nlinarith
    exact hDiv.trans_lt hkDiv
  have hrSub : r - 1 = -a / (H + a) := by
    dsimp [r]
    field_simp
    ring
  rw [hrSub] at hBernoulli
  have : 3 / 4 < 1 + (k : ℝ) * (-a / (H + a)) := by
    have hrewrite : (k : ℝ) * (-a / (H + a)) = -((k : ℝ) * a / (H + a)) := by
      ring
    rw [hrewrite]
    linarith
  exact this.trans_le hBernoulli

/-- The exterior boundary contribution is below the exact `1/(4 log T)` threshold. -/
lemma detectorMass_mul_localizer_lt (N k : ℕ) (T δ : ℝ)
    (hT : Real.exp 4 ≤ T) (hN : N ≤ detectorScaleUpper T)
    (hExponent : 18 ≤ δ * (k : ℝ)) :
    detectorMass N T * (T ^ (δ / 2) / T ^ δ) ^ k <
      1 / (4 * Real.log T) := by
  have hExpPos : 0 < Real.exp 4 := Real.exp_pos 4
  have hTpos : 0 < T := hExpPos.trans_le hT
  have hTone : 1 ≤ T := by
    calc
      1 ≤ Real.exp 4 := by
        rw [← Real.exp_zero]
        exact Real.exp_monotone (by norm_num)
      _ ≤ T := hT
  have hTexp2 : Real.exp 2 ≤ T := by
    calc
      Real.exp 2 ≤ Real.exp 4 := Real.exp_monotone (by norm_num)
      _ ≤ T := hT
  have hMass := detectorMass_le_pow_seven T N hTexp2 hN
  have hRatio : (T ^ (δ / 2) / T ^ δ) ^ k =
      T ^ ((-(δ / 2)) * (k : ℝ)) := by
    rw [← Real.rpow_sub hTpos]
    have hsub : δ / 2 - δ = -(δ / 2) := by ring
    rw [hsub, ← Real.rpow_natCast, ← Real.rpow_mul hTpos.le]
  have hPower : T ^ (7 : ℕ) * (T ^ (δ / 2) / T ^ δ) ^ k ≤ T ^ (-2 : ℝ) := by
    rw [hRatio, ← Real.rpow_natCast, ← Real.rpow_add hTpos]
    apply Real.rpow_le_rpow_of_exponent_le hTone
    nlinarith
  have hTFour : 4 < T := by
    have : 4 < Real.exp 4 := by
      calc
        4 < 1 + 4 := by norm_num
        _ < Real.exp 4 := by
          rw [add_comm]
          exact Real.add_one_lt_exp (by norm_num)
    exact this.trans_le hT
  have hLogPos : 0 < Real.log T := Real.log_pos (by linarith)
  have hLogBound : Real.log T ≤ T - 1 := Real.log_le_sub_one_of_pos hTpos
  have hDenom : 4 * Real.log T < T ^ 2 := by
    nlinarith [sq_nonneg (T - 2)]
  have hReciprocal : T ^ (-2 : ℝ) < 1 / (4 * Real.log T) := by
    have hInv := one_div_lt_one_div_of_lt (mul_pos (by norm_num) hLogPos) hDenom
    rw [Real.rpow_neg hTpos.le, Real.rpow_two]
    simpa [one_div] using hInv
  calc
    detectorMass N T * (T ^ (δ / 2) / T ^ δ) ^ k
        ≤ T ^ (7 : ℕ) * (T ^ (δ / 2) / T ^ δ) ^ k := by
          exact mul_le_mul_of_nonneg_right hMass (pow_nonneg (by positivity) k)
    _ ≤ T ^ (-2 : ℝ) := hPower
    _ < 1 / (4 * Real.log T) := hReciprocal

/--
F-04: beta dependence removal for the actual detector and actual Type-I zeros.
The proof uses rational boundary localization and Phragmén--Lindelöf instead of
the agenda's Fourier-cutoff presentation; it proves the same fixed-line output
with the exact `T^δ` displacement and `1/(4 log T)` lower bound.
-/
theorem beta_dependence_removal : DetectorBetaShiftProp := by
  classical
  intro δ hδ
  obtain ⟨k, hk⟩ := exists_nat_gt (18 / δ)
  have hExponent : 18 < δ * (k : ℝ) := by
    rw [div_lt_iff₀ hδ] at hk
    nlinarith
  have hPowTendsto : Tendsto (fun T : ℝ => T ^ (δ / 2)) atTop atTop :=
    tendsto_rpow_atTop (by positivity)
  have hEventually : ∀ᶠ T : ℝ in atTop, 4 * (k : ℝ) < T ^ (δ / 2) :=
    hPowTendsto.eventually (eventually_gt_atTop (4 * (k : ℝ)))
  rw [eventually_atTop] at hEventually
  obtain ⟨Tfactor, hTfactor⟩ := hEventually
  let T₀ := max (Real.exp 4) Tfactor
  refine ⟨T₀, ?_, ?_⟩
  · exact (show Real.exp 2 ≤ Real.exp 4 from Real.exp_monotone (by norm_num)).trans
      (le_max_left _ _)
  · intro σ T hσLower _hσUpper hT ρ hρ
    have hT4 : Real.exp 4 ≤ T := (le_max_left _ _).trans hT
    have hTFactor : Tfactor ≤ T := (le_max_right _ _).trans hT
    have hTpos : 0 < T := (Real.exp_pos 4).trans_le hT4
    have hLogPos : 0 < Real.log T := Real.log_pos (by
      have : 1 < Real.exp 4 := by
        rw [← Real.exp_zero]
        exact Real.exp_lt_exp.mpr (by norm_num)
      exact this.trans_le hT4)
    have hRpos : 0 < T ^ δ := Real.rpow_pos_of_pos hTpos δ
    have hHpos : 0 < T ^ (δ / 2) := Real.rpow_pos_of_pos hTpos (δ / 2)
    have hTypeI : IsTypeIZero ρ T := (Finset.mem_filter.mp hρ).2
    have hScale := chosenTypeIScale_spec ρ T hTypeI
    have hScaleUpper : ((2 ^ chosenTypeIScale ρ T : ℕ) : ℝ) ≤ detectorScaleUpper T := by
      have := (mem_admissibleDyadicIndices T (chosenTypeIScale ρ T)).mp hScale.1
      exact_mod_cast this.2
    have hRect : ρ ∈ zerosInRect σ 1 T (2 * T) := (Finset.mem_filter.mp hρ).1
    rw [zerosInRect, Set.Finite.mem_toFinset, Set.mem_inter_iff, mem_ZeroRectangle] at hRect
    let a : ℝ := ρ.re - σ
    let z : ℂ := σ + I * ρ.im
    have ha : 0 ≤ a := by dsimp [a]; linarith [hRect.1.1]
    have haOne : a ≤ 1 := by dsimp [a]; linarith [hRect.1.2, hσLower]
    have hz : 0 ≤ z.re := by dsimp [z]; simp; linarith
    have hza : z + (a : ℂ) = ρ := by
      apply Complex.ext
      · simp [z, a]
      · simp [z, a]
    have hLarge : 1 / (3 * Real.log T) ≤
        ‖detectPoly (2 ^ chosenTypeIScale ρ T) (z + (a : ℂ)) T‖ := by
      rw [hza]
      exact hScale.2
    have hFactor : 3 / 4 <
        ‖(((T ^ (δ / 2) : ℝ) : ℂ) /
          (((T ^ (δ / 2) : ℝ) : ℂ) + (a : ℂ))) ^ k‖ :=
      localizer_factor_gt_three_fourths k (T ^ (δ / 2)) a hHpos ha haOne
        (hTfactor T hTFactor)
    have hExterior : detectorMass (2 ^ chosenTypeIScale ρ T) T *
        (T ^ (δ / 2) / T ^ δ) ^ k <
          (3 / 4) * (1 / (3 * Real.log T)) := by
      have hBound := detectorMass_mul_localizer_lt
        (2 ^ chosenTypeIScale ρ T) k T δ hT4 hScaleUpper hExponent.le
      have hThreshold : (3 / 4) * (1 / (3 * Real.log T)) =
          1 / (4 * Real.log T) := by
        field_simp
      rw [hThreshold]
      exact hBound
    obtain ⟨y, hy, hyLarge⟩ := exists_nearby_large_value
      (2 ^ chosenTypeIScale ρ T) k z T (T ^ (δ / 2)) (T ^ δ)
        (1 / (3 * Real.log T)) a hHpos hRpos (by positivity) hz ha hLarge hFactor hExterior
    refine ⟨ρ.im + y, ?_, ?_⟩
    · simpa only [sub_add_cancel_left, abs_neg] using hy
    · change 1 / (4 * Real.log T) ≤
        ‖detectPoly (2 ^ chosenTypeIScale ρ T)
          ((σ : ℂ) + I * ((ρ.im + y : ℝ) : ℂ)) T‖
      have hPoint : z + (y : ℂ) * I =
          (σ : ℂ) + I * ((ρ.im + y : ℝ) : ℂ) := by
        dsimp [z]
        rw [ofReal_add]
        ring
      rw [← hPoint]
      have hThreshold : (3 / 4) * (1 / (3 * Real.log T)) =
          1 / (4 * Real.log T) := by
        field_simp
      rw [← hThreshold]
      exact hyLarge

/-- The separated Type-I extraction theorem with beta removal and multiplicity control discharged. -/
theorem extractSeparated_native : ExtractSeparatedTarget :=
  extractSeparated_of_beta_shift beta_dependence_removal

end RiemannZeta.GuthMaynard
