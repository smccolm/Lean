import Tao2026.FactorialEquidistribution

/-!
# Shrinking-band geometry for the low-`P` factorial branch

This module develops the real-scale analogue of the two changes of variables
used in Lemma 3.1.  The first fractional-coordinate band now has width
`1 / (60 log² N)`, exactly matching the normalized factorial plateau.
-/

open Filter Set MeasureTheory

namespace Tao2026

noncomputable section

/-- Inner prime-scale set on which the low-`P` cutoff has a fixed positive
quadratic factor and its first factor is exactly one. -/
def factorialLowInnerPrimeScaleSet (N : ℕ) (P : ℝ) : Set ℝ :=
  Ioo P (2 * P) ∩
    {t | factorialPlateauArcLeft N ≤ Int.fract ((N : ℝ) / t) ∧
      Int.fract ((N : ℝ) / t) ≤ factorialPlateauArcRight N ∧
      (1 / 100 : ℝ) ≤ Int.fract ((N : ℝ) / t ^ 2) ∧
      Int.fract ((N : ℝ) / t ^ 2) ≤ 89 / 100}

theorem measurableSet_factorialLowInnerPrimeScaleSet (N : ℕ) (P : ℝ) :
    MeasurableSet (factorialLowInnerPrimeScaleSet N P) := by
  unfold factorialLowInnerPrimeScaleSet
  measurability

/-- The inner set after the reciprocal substitution `s=N/t`. -/
def factorialLowInnerReciprocalScaleSet (N : ℕ) (P : ℝ) : Set ℝ :=
  Ioo ((N : ℝ) / (2 * P)) ((N : ℝ) / P) ∩
    {s | factorialPlateauArcLeft N ≤ Int.fract s ∧
      Int.fract s ≤ factorialPlateauArcRight N ∧
      (1 / 100 : ℝ) ≤ Int.fract (s ^ 2 / N) ∧
      Int.fract (s ^ 2 / N) ≤ 89 / 100}

theorem measurableSet_factorialLowInnerReciprocalScaleSet (N : ℕ) (P : ℝ) :
    MeasurableSet (factorialLowInnerReciprocalScaleSet N P) := by
  unfold factorialLowInnerReciprocalScaleSet
  measurability

/-- Forget the shrinking first coordinate while retaining a margin in the
quadratic coordinate. -/
def factorialLowQuadraticReciprocalScaleSet (N : ℕ) (P : ℝ) : Set ℝ :=
  Ioo ((N : ℝ) / (2 * P)) ((N : ℝ) / P) ∩
    {s | (2 / 100 : ℝ) ≤ Int.fract (s ^ 2 / N) ∧
      Int.fract (s ^ 2 / N) ≤ 88 / 100}

def factorialLowQuadraticSliceSet (N : ℕ) (P : ℝ) : Set ℝ :=
  Ioo ((N : ℝ) / (4 * P ^ 2)) ((N : ℝ) / P ^ 2) ∩
    veryBadQuadraticFractionalBand

theorem measurableSet_factorialLowQuadraticReciprocalScaleSet
    (N : ℕ) (P : ℝ) :
    MeasurableSet (factorialLowQuadraticReciprocalScaleSet N P) := by
  unfold factorialLowQuadraticReciprocalScaleSet
  measurability

theorem measurableSet_factorialLowQuadraticSliceSet (N : ℕ) (P : ℝ) :
    MeasurableSet (factorialLowQuadraticSliceSet N P) := by
  unfold factorialLowQuadraticSliceSet veryBadQuadraticFractionalBand
  measurability

/-- Exact interval and band transport under `u=s²/N` at a real prime scale. -/
theorem mem_factorialLowQuadraticReciprocalScaleSet_iff_square_div_mem
    {N : ℕ} {P s : ℝ} (hN : 0 < N) (hP : 0 < P) (hs : 0 < s) :
    s ∈ factorialLowQuadraticReciprocalScaleSet N P ↔
      s ^ 2 / (N : ℝ) ∈ factorialLowQuadraticSliceSet N P := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have h2P : 0 < 2 * P := by positivity
  have hlow : 0 ≤ (N : ℝ) / (2 * P) := (div_pos hNr h2P).le
  have hupp : 0 ≤ (N : ℝ) / P := (div_pos hNr hP).le
  have hlowerId : ((N : ℝ) / (4 * P ^ 2)) =
      (((N : ℝ) / (2 * P)) ^ 2) / N := by field_simp; ring
  have hupperId : ((N : ℝ) / P ^ 2) =
      (((N : ℝ) / P) ^ 2) / N := by field_simp
  rw [factorialLowQuadraticReciprocalScaleSet,
    factorialLowQuadraticSliceSet, veryBadQuadraticFractionalBand]
  constructor
  · rintro ⟨hsI, hylo, hyhi⟩
    refine ⟨⟨?_, ?_⟩, hylo, hyhi⟩
    · rw [hlowerId, div_lt_div_iff_of_pos_right hNr]
      exact (sq_lt_sq₀ hlow hs.le).mpr hsI.1
    · rw [hupperId, div_lt_div_iff_of_pos_right hNr]
      exact (sq_lt_sq₀ hs.le hupp).mpr hsI.2
  · rintro ⟨huI, hylo, hyhi⟩
    refine ⟨⟨?_, ?_⟩, hylo, hyhi⟩
    · have huLower := huI.1
      rw [hlowerId, div_lt_div_iff_of_pos_right hNr] at huLower
      exact (sq_lt_sq₀ hlow hs.le).mp huLower
    · have huUpper := huI.2
      rw [hupperId, div_lt_div_iff_of_pos_right hNr] at huUpper
      exact (sq_lt_sq₀ hs.le hupp).mp huUpper

theorem factorialLowQuadraticSliceSet_eq_normalized
    {N : ℕ} {P : ℝ} (hP : 0 < P) :
    factorialLowQuadraticSliceSet N P =
      veryBadNormalizedQuadraticSliceSet ((N : ℝ) / P ^ 2) := by
  have hleft : (N : ℝ) / (4 * P ^ 2) = ((N : ℝ) / P ^ 2) / 4 := by
    field_simp
  unfold factorialLowQuadraticSliceSet veryBadNormalizedQuadraticSliceSet
  rw [hleft]

/-- Uniform lower bound for the quadratic slice whenever `P≤√(2N)`. -/
theorem factorialLowQuadraticSlice_measure_lower
    {N : ℕ} {P : ℝ} (hP : 0 < P)
    (hscale : (1 / 2 : ℝ) ≤ (N : ℝ) / P ^ 2) :
    (N : ℝ) / (8 * P ^ 2) ≤
      (volume (factorialLowQuadraticSliceSet N P)).toReal := by
  have hmain := normalizedQuadraticSlice_measure_lower hscale
  rw [← factorialLowQuadraticSliceSet_eq_normalized hP] at hmain
  calc
    (N : ℝ) / (8 * P ^ 2) = ((N : ℝ) / P ^ 2) / 8 := by field_simp
    _ ≤ (volume (factorialLowQuadraticSliceSet N P)).toReal := hmain

/-- Exact measure transport under the low-`P` quadratic substitution
`u=s²/N`. -/
theorem volume_factorialLowQuadraticSliceSet_eq_integral_squareJacobian
    {N : ℕ} {P : ℝ} (hN : 0 < N) (hP : 0 < P) :
    (volume (factorialLowQuadraticSliceSet N P)).toReal =
      ∫ s in factorialLowQuadraticReciprocalScaleSet N P,
        2 * s / (N : ℝ) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have h2P : 0 < 2 * P := by positivity
  have hlowPos : (0 : ℝ) < (N : ℝ) / (2 * P) := div_pos hNr h2P
  have hab : (N : ℝ) / (2 * P) ≤ (N : ℝ) / P :=
    div_le_div_of_nonneg_left hNr.le hP (by linarith)
  have hfcont : ContinuousOn (fun s : ℝ => s ^ 2 / (N : ℝ))
      (uIcc ((N : ℝ) / (2 * P)) ((N : ℝ) / P)) := by fun_prop
  have hfderiv : ∀ s ∈ Ioo
      (min ((N : ℝ) / (2 * P)) ((N : ℝ) / P))
      (max ((N : ℝ) / (2 * P)) ((N : ℝ) / P)),
      HasDerivAt (fun u : ℝ => u ^ 2 / (N : ℝ)) (2 * s / N) s := by
    intro s _hs
    exact hasDerivAt_square_div_const (N : ℝ) s
  have hfnonneg : ∀ s ∈ Ioo
      (min ((N : ℝ) / (2 * P)) ((N : ℝ) / P))
      (max ((N : ℝ) / (2 * P)) ((N : ℝ) / P)),
      (0 : ℝ) ≤ 2 * s / N := by
    intro s hs
    rw [min_eq_left hab, max_eq_right hab] at hs
    exact div_nonneg (mul_nonneg (by norm_num) (hlowPos.trans hs.1).le) hNr.le
  have hfa : (((N : ℝ) / (2 * P)) ^ 2 / N) =
      (N : ℝ) / (4 * P ^ 2) := by field_simp; ring
  have hfb : (((N : ℝ) / P) ^ 2 / N) =
      (N : ℝ) / P ^ 2 := by field_simp
  have hsubst :
      (∫ s in (N : ℝ) / (2 * P)..(N : ℝ) / P,
        (2 * s / N : ℝ) *
          (factorialLowQuadraticSliceSet N P).indicator (fun _ => (1 : ℝ))
            (s ^ 2 / (N : ℝ))) =
      ∫ u in (N : ℝ) / (4 * P ^ 2)..(N : ℝ) / P ^ 2,
        (factorialLowQuadraticSliceSet N P).indicator (fun _ => (1 : ℝ)) u := by
    simpa only [smul_eq_mul, Function.comp_apply, hfa, hfb] using
      (intervalIntegral.integral_deriv_smul_comp_of_deriv_nonneg
        (g := (factorialLowQuadraticSliceSet N P).indicator
          (fun _ => (1 : ℝ))) hfcont hfderiv hfnonneg)
  have huab : (N : ℝ) / (4 * P ^ 2) ≤ (N : ℝ) / P ^ 2 := by
    rw [← hfa, ← hfb]
    exact div_le_div_of_nonneg_right (sq_le_sq₀
      (div_nonneg hNr.le h2P.le) (div_nonneg hNr.le hP.le) |>.mpr
        (div_le_div_of_nonneg_left hNr.le hP (by linarith))) hNr.le
  have hUsubsetIoc : factorialLowQuadraticSliceSet N P ⊆
      Ioc ((N : ℝ) / (4 * P ^ 2)) ((N : ℝ) / P ^ 2) := by
    intro u hu
    exact ⟨hu.1.1, hu.1.2.le⟩
  have hright :
      (∫ u in (N : ℝ) / (4 * P ^ 2)..(N : ℝ) / P ^ 2,
        (factorialLowQuadraticSliceSet N P).indicator (fun _ => (1 : ℝ)) u) =
      (volume (factorialLowQuadraticSliceSet N P)).toReal := by
    rw [intervalIntegral.integral_of_le huab,
      MeasureTheory.integral_indicator
        (measurableSet_factorialLowQuadraticSliceSet N P),
      setIntegral_const, Measure.real_def,
      Measure.restrict_apply (measurableSet_factorialLowQuadraticSliceSet N P),
      inter_eq_left.mpr hUsubsetIoc]
    simp
  have hYsubsetIoc : factorialLowQuadraticReciprocalScaleSet N P ⊆
      Ioc ((N : ℝ) / (2 * P)) ((N : ℝ) / P) := by
    intro s hs
    exact ⟨hs.1.1, hs.1.2.le⟩
  have hweightedInterval :
      (∫ s in (N : ℝ) / (2 * P)..(N : ℝ) / P,
        (factorialLowQuadraticReciprocalScaleSet N P).indicator
          (fun s => 2 * s / (N : ℝ)) s) =
      ∫ s in factorialLowQuadraticReciprocalScaleSet N P,
        2 * s / (N : ℝ) := by
    rw [intervalIntegral.integral_of_le hab,
      MeasureTheory.integral_indicator
        (measurableSet_factorialLowQuadraticReciprocalScaleSet N P),
      Measure.restrict_restrict
        (measurableSet_factorialLowQuadraticReciprocalScaleSet N P),
      inter_eq_left.mpr hYsubsetIoc]
  have hleft :
      (∫ s in (N : ℝ) / (2 * P)..(N : ℝ) / P,
        (2 * s / N : ℝ) *
          (factorialLowQuadraticSliceSet N P).indicator (fun _ => (1 : ℝ))
            (s ^ 2 / (N : ℝ))) =
      ∫ s in factorialLowQuadraticReciprocalScaleSet N P,
        2 * s / (N : ℝ) := by
    calc
      _ = ∫ s in (N : ℝ) / (2 * P)..(N : ℝ) / P,
          (factorialLowQuadraticReciprocalScaleSet N P).indicator
            (fun s => 2 * s / (N : ℝ)) s := by
        apply intervalIntegral.integral_congr
        intro s hs
        rw [uIcc_of_le hab] at hs
        have hspos : 0 < s := hlowPos.trans_le hs.1
        have hmem :=
          mem_factorialLowQuadraticReciprocalScaleSet_iff_square_div_mem
            hN hP hspos
        by_cases hsY : s ∈ factorialLowQuadraticReciprocalScaleSet N P
        · have huU := hmem.mp hsY
          simp [Set.indicator_of_mem hsY, Set.indicator_of_mem huU]
        · have huU : s ^ 2 / (N : ℝ) ∉ factorialLowQuadraticSliceSet N P :=
            fun hu => hsY (hmem.mpr hu)
          simp [Set.indicator, hsY, huU]
      _ = _ := hweightedInterval
  rw [hleft, hright] at hsubst
  exact hsubst.symm

theorem factorialLow_squareJacobian_upper_on_sourceInterval
    {N : ℕ} {P s : ℝ} (hN : 0 < N) (hP : 0 < P)
    (hsle : s ≤ (N : ℝ) / P) :
    2 * s / (N : ℝ) ≤ 2 / P := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hmul : s * P ≤ N := (le_div_iff₀ hP).mp hsle
  rw [div_le_div_iff₀ hNr hP]
  nlinarith

theorem integrableOn_factorialLow_squareJacobian
    {N : ℕ} {P : ℝ} (hN : 0 < N) :
    IntegrableOn (fun s : ℝ => 2 * s / (N : ℝ))
      (factorialLowQuadraticReciprocalScaleSet N P) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hcont : Continuous (fun s : ℝ => 2 * s / (N : ℝ)) := by fun_prop
  apply (hcont.continuousOn.integrableOn_compact isCompact_Icc).mono_set
  intro s hs
  exact ⟨hs.1.1.le, hs.1.2.le⟩

theorem factorialLowQuadraticSlice_measure_le_two_div_scale_mul_reciprocal
    {N : ℕ} {P : ℝ} (hN : 0 < N) (hP : 0 < P) :
    (volume (factorialLowQuadraticSliceSet N P)).toReal ≤
      2 / P *
        (volume (factorialLowQuadraticReciprocalScaleSet N P)).toReal := by
  have hjac : Integrable (fun s : ℝ => 2 * s / (N : ℝ))
      (volume.restrict (factorialLowQuadraticReciprocalScaleSet N P)) :=
    integrableOn_factorialLow_squareJacobian hN
  have hconst : Integrable (fun _ : ℝ => 2 / P)
      (volume.restrict (factorialLowQuadraticReciprocalScaleSet N P)) :=
    (continuousOn_const.integrableOn_compact isCompact_Icc).mono_set (by
      intro s hs
      exact ⟨hs.1.1.le, hs.1.2.le⟩)
  have hmono : (fun s : ℝ => 2 * s / (N : ℝ)) ≤ᶠ[ae
      (volume.restrict (factorialLowQuadraticReciprocalScaleSet N P))]
      (fun _ : ℝ => 2 / P) := by
    filter_upwards [ae_restrict_mem
      (measurableSet_factorialLowQuadraticReciprocalScaleSet N P)] with s hs
    exact factorialLow_squareJacobian_upper_on_sourceInterval hN hP hs.1.2.le
  have hmain := integral_mono_ae hjac hconst hmono
  rw [setIntegral_const, Measure.real_def, smul_eq_mul] at hmain
  rw [volume_factorialLowQuadraticSliceSet_eq_integral_squareJacobian hN hP]
  simpa [mul_comm] using hmain

/-- The quadratic reciprocal set occupies at least a fixed proportion of
the prime scale before inserting the shrinking first-coordinate band. -/
theorem factorialLowQuadraticReciprocalScale_measure_lower
    {N : ℕ} {P : ℝ} (hN : 0 < N) (hP : 0 < P)
    (hscale : (1 / 2 : ℝ) ≤ (N : ℝ) / P ^ 2) :
    P / 32 ≤
      (volume (factorialLowQuadraticReciprocalScaleSet N P)).toReal := by
  have hlower := factorialLowQuadraticSlice_measure_lower hP hscale
  have hupper :=
    factorialLowQuadraticSlice_measure_le_two_div_scale_mul_reciprocal hN hP
  have hchain : (N : ℝ) / (8 * P ^ 2) ≤
      2 / P *
        (volume (factorialLowQuadraticReciprocalScaleSet N P)).toReal :=
    hlower.trans hupper
  have hscale' : P ^ 2 / 2 ≤ N := by
    rw [le_div_iff₀ (sq_pos_of_pos hP)] at hscale
    nlinarith
  have hchain' : (N : ℝ) ≤ 16 * P *
      (volume (factorialLowQuadraticReciprocalScaleSet N P)).toReal := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 8 * P ^ 2)] at hchain
    field_simp at hchain
    nlinarith
  nlinarith

/-- Source-normalized form of the preceding lower bound. -/
theorem factorialLowQuadraticReciprocalScale_measure_lower_source
    {N : ℕ} {P : ℝ} (hN : 0 < N) (hP : 0 < P)
    (hscale : (1 / 2 : ℝ) ≤ (N : ℝ) / P ^ 2) :
    (N : ℝ) / (16 * P) ≤
      (volume (factorialLowQuadraticReciprocalScaleSet N P)).toReal := by
  have hlower := factorialLowQuadraticSlice_measure_lower hP hscale
  have hupper :=
    factorialLowQuadraticSlice_measure_le_two_div_scale_mul_reciprocal hN hP
  have hchain : (N : ℝ) / (8 * P ^ 2) ≤
      2 / P *
        (volume (factorialLowQuadraticReciprocalScaleSet N P)).toReal :=
    hlower.trans hupper
  have hchain' : (N : ℝ) ≤ 16 * P *
      (volume (factorialLowQuadraticReciprocalScaleSet N P)).toReal := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 8 * P ^ 2)] at hchain
    field_simp at hchain
    nlinarith
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < 16 * P)]
  simpa [mul_comm, mul_left_comm, mul_assoc] using hchain'

/-- Remove the two endpoint unit cells before inserting the shrinking
first-coordinate band. -/
def factorialLowQuadraticReciprocalInteriorSet (N : ℕ) (P : ℝ) : Set ℝ :=
  Ioo ((N : ℝ) / (2 * P) + 1) ((N : ℝ) / P - 1) ∩
    {s | (2 / 100 : ℝ) ≤ Int.fract (s ^ 2 / N) ∧
      Int.fract (s ^ 2 / N) ≤ 88 / 100}

theorem measurableSet_factorialLowQuadraticReciprocalInteriorSet
    (N : ℕ) (P : ℝ) :
    MeasurableSet (factorialLowQuadraticReciprocalInteriorSet N P) := by
  unfold factorialLowQuadraticReciprocalInteriorSet
  measurability

theorem factorialLowQuadraticReciprocal_measure_le_interior_add_two
    {N : ℕ} {P : ℝ} :
    (volume (factorialLowQuadraticReciprocalScaleSet N P)).toReal ≤
      (volume (factorialLowQuadraticReciprocalInteriorSet N P)).toReal + 2 := by
  let a : ℝ := (N : ℝ) / (2 * P)
  let b : ℝ := (N : ℝ) / P
  let L : Set ℝ := Icc a (a + 1)
  let R : Set ℝ := Icc (b - 1) b
  have hcover : factorialLowQuadraticReciprocalScaleSet N P ⊆
      (factorialLowQuadraticReciprocalInteriorSet N P ∪ L) ∪ R := by
    intro t ht
    by_cases htI : a + 1 < t ∧ t < b - 1
    · left
      left
      exact ⟨htI, ht.2⟩
    · simp only [not_and_or, not_lt] at htI
      rcases htI with htleft | htright
      · left
        right
        exact ⟨ht.1.1.le, htleft⟩
      · right
        exact ⟨htright, ht.1.2.le⟩
  have hIfinite : volume (factorialLowQuadraticReciprocalInteriorSet N P) ≠ ⊤ :=
    (calc
      volume (factorialLowQuadraticReciprocalInteriorSet N P) ≤
          volume (Ioo (a + 1) (b - 1)) := measure_mono inter_subset_left
      _ < ⊤ := measure_Ioo_lt_top).ne
  have hLfinite : volume L ≠ ⊤ := by
    dsimp [L]
    exact measure_Icc_lt_top.ne
  have hRfinite : volume R ≠ ⊤ := by
    dsimp [R]
    exact measure_Icc_lt_top.ne
  have hunionfinite :
      volume ((factorialLowQuadraticReciprocalInteriorSet N P ∪ L) ∪ R) ≠ ⊤ :=
    measure_union_ne_top (measure_union_ne_top hIfinite hLfinite) hRfinite
  calc
    (volume (factorialLowQuadraticReciprocalScaleSet N P)).toReal ≤
        (volume ((factorialLowQuadraticReciprocalInteriorSet N P ∪ L) ∪ R)).toReal :=
      measureReal_mono hcover hunionfinite
    _ ≤ (volume (factorialLowQuadraticReciprocalInteriorSet N P ∪ L)).toReal +
        (volume R).toReal := measureReal_union_le _ _
    _ ≤ ((volume (factorialLowQuadraticReciprocalInteriorSet N P)).toReal +
        (volume L).toReal) + (volume R).toReal := by
      gcongr
      exact measureReal_union_le _ _
    _ = (volume (factorialLowQuadraticReciprocalInteriorSet N P)).toReal + 2 := by
      dsimp [L, R, a, b]
      simp [Real.volume_Icc]
      ring

theorem factorialLowQuadraticReciprocalInterior_measure_lower
    {N : ℕ} {P : ℝ} (hN : 0 < N) (hP : 200 ≤ P)
    (hscale : (1 / 2 : ℝ) ≤ (N : ℝ) / P ^ 2) :
    (N : ℝ) / (32 * P) ≤
      (volume (factorialLowQuadraticReciprocalInteriorSet N P)).toReal := by
  have hPpos : 0 < P := lt_of_lt_of_le (by norm_num) hP
  have hy := factorialLowQuadraticReciprocalScale_measure_lower_source
    hN hPpos hscale
  have htrim :=
    factorialLowQuadraticReciprocal_measure_le_interior_add_two
      (N := N) (P := P)
  have hscale' : P ^ 2 / 2 ≤ N := by
    rw [le_div_iff₀ (sq_pos_of_pos hPpos)] at hscale
    nlinarith
  have hratio : (64 : ℝ) ≤ (N : ℝ) / P := by
    rw [le_div_iff₀ hPpos]
    nlinarith
  have hdiff : (N : ℝ) / (32 * P) + 2 ≤ (N : ℝ) / (16 * P) := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 16 * P)]
    field_simp
    nlinarith
  linarith

/-- On the reciprocal source interval, `s ↦ s²/N` varies by at most `2/P`
between two points at distance at most one. -/
theorem factorialLow_abs_square_div_sub_square_div_le_two_div_scale
    {N : ℕ} {P s t : ℝ} (hN : 0 < N) (hP : 0 < P)
    (hs0 : 0 ≤ s) (ht0 : 0 ≤ t)
    (hs : s ≤ (N : ℝ) / P) (ht : t ≤ (N : ℝ) / P)
    (hst : |s - t| ≤ 1) :
    |s ^ 2 / (N : ℝ) - t ^ 2 / N| ≤ 2 / P := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hsum : s + t ≤ 2 * (N : ℝ) / P := by
    rw [le_div_iff₀ hP]
    have hs' : s * P ≤ N := (le_div_iff₀ hP).mp hs
    have ht' : t * P ≤ N := (le_div_iff₀ hP).mp ht
    nlinarith
  have hsum0 : 0 ≤ s + t := add_nonneg hs0 ht0
  rw [← sub_div, sq_sub_sq, abs_div, abs_mul,
    abs_of_pos hNr, abs_of_nonneg hsum0]
  calc
    (s + t) * |s - t| / (N : ℝ) ≤
        (2 * (N : ℝ) / P) * 1 / N := by gcongr
    _ = 2 / P := by field_simp

theorem factorialLow_quadratic_fract_mem_innerBand_of_same_unit_cell
    {N : ℕ} {P s t : ℝ} (hN : 0 < N) (hP : 200 ≤ P)
    (hs0 : 0 ≤ s) (ht0 : 0 ≤ t)
    (hs : s ≤ (N : ℝ) / P) (ht : t ≤ (N : ℝ) / P)
    (hst : |s - t| ≤ 1)
    (htlo : (2 / 100 : ℝ) ≤ Int.fract (t ^ 2 / N))
    (hthi : Int.fract (t ^ 2 / N) ≤ 88 / 100) :
    (1 / 100 : ℝ) ≤ Int.fract (s ^ 2 / N) ∧
      Int.fract (s ^ 2 / N) ≤ 89 / 100 := by
  have hPpos : 0 < P := lt_of_lt_of_le (by norm_num) hP
  have hslow := factorialLow_abs_square_div_sub_square_div_le_two_div_scale
    hN hPpos hs0 ht0 hs ht hst
  have htwo : 2 / P ≤ (1 / 100 : ℝ) := by
    rw [div_le_iff₀ hPpos]
    nlinarith
  exact fract_mem_veryBad_innerBand_of_abs_sub_le
    (hslow.trans htwo) htlo hthi

/-- Every point in the shrinking first band of a unit cell meeting the
quadratic interior belongs to the full two-coordinate reciprocal set. -/
theorem factorialLow_firstBandCell_subset_innerReciprocal_of_witness
    {N : ℕ} {P t : ℝ} (hN : 0 < N) (hP : 200 ≤ P)
    (hlog : 1 < Real.log (N : ℝ))
    (htY : t ∈ factorialLowQuadraticReciprocalScaleSet N P)
    (htLower : (N : ℝ) / (2 * P) + 1 < t)
    (htUpper : t < (N : ℝ) / P - 1) :
    Icc ((⌊t⌋ : ℝ) + factorialPlateauArcLeft N)
        ((⌊t⌋ : ℝ) + factorialPlateauArcRight N) ⊆
      factorialLowInnerReciprocalScaleSet N P := by
  intro s hsCell
  have hPpos : 0 < P := lt_of_lt_of_le (by norm_num) hP
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨hleft0, hleftRight, hright1⟩ := factorialPlateauArc_bounds hlog
  have htId : Int.fract t + (⌊t⌋ : ℝ) = t := Int.fract_add_floor t
  have htFract0 : (0 : ℝ) ≤ Int.fract t := Int.fract_nonneg t
  have htFract1 : Int.fract t < 1 := Int.fract_lt_one t
  have hdist : |s - t| ≤ 1 := by
    rw [abs_le]
    constructor
    · linarith [hsCell.1]
    · linarith [hsCell.2]
  have hsLower : (N : ℝ) / (2 * P) < s := by
    rw [abs_le] at hdist
    linarith [hdist.1]
  have hsUpper : s < (N : ℝ) / P := by
    rw [abs_le] at hdist
    linarith [hdist.2]
  have hsCellIco : s ∈ Ico (⌊t⌋ : ℝ) ((⌊t⌋ : ℝ) + 1) := by
    constructor
    · linarith [hsCell.1]
    · linarith [hsCell.2]
  have hsFloor : ⌊s⌋ = ⌊t⌋ := Int.floor_eq_iff.mpr hsCellIco
  have hsFloorR : (⌊s⌋ : ℝ) = (⌊t⌋ : ℝ) := congrArg Int.cast hsFloor
  have hsId : Int.fract s + (⌊s⌋ : ℝ) = s := Int.fract_add_floor s
  have hsFractLo : factorialPlateauArcLeft N ≤ Int.fract s := by
    linarith [hsCell.1]
  have hsFractHi : Int.fract s ≤ factorialPlateauArcRight N := by
    linarith [hsCell.2]
  have hsourceLower0 : (0 : ℝ) ≤ (N : ℝ) / (2 * P) := by positivity
  have hs0 : (0 : ℝ) ≤ s := hsourceLower0.trans hsLower.le
  have ht0 : (0 : ℝ) ≤ t := hsourceLower0.trans htY.1.1.le
  have hquad := factorialLow_quadratic_fract_mem_innerBand_of_same_unit_cell
    hN hP hs0 ht0 hsUpper.le htY.1.2.le hdist htY.2.1 htY.2.2
  exact ⟨⟨hsLower, hsUpper⟩, hsFractLo, hsFractHi, hquad.1, hquad.2⟩

noncomputable def factorialLowOccupiedInteriorCells
    (N : ℕ) (P : ℝ) : Finset ℤ := by
  classical
  exact (Finset.Icc
      ⌊(N : ℝ) / (2 * P) + 1⌋
      ⌊(N : ℝ) / P - 1⌋).filter
        (fun k => ∃ t ∈ factorialLowQuadraticReciprocalInteriorSet N P,
          ⌊t⌋ = k)

def factorialLowUnitCell (k : ℤ) : Set ℝ :=
  Ico (k : ℝ) ((k : ℝ) + 1)

def factorialLowFirstBandCell (N : ℕ) (k : ℤ) : Set ℝ :=
  Ioo ((k : ℝ) + factorialPlateauArcLeft N)
    ((k : ℝ) + factorialPlateauArcRight N)

theorem factorialLowQuadraticInterior_subset_occupiedCells
    {N : ℕ} {P : ℝ} :
    factorialLowQuadraticReciprocalInteriorSet N P ⊆
      ⋃ k ∈ factorialLowOccupiedInteriorCells N P, factorialLowUnitCell k := by
  classical
  intro t ht
  have hklo : ⌊(N : ℝ) / (2 * P) + 1⌋ ≤ ⌊t⌋ :=
    Int.floor_mono ht.1.1.le
  have hkhi : ⌊t⌋ ≤ ⌊(N : ℝ) / P - 1⌋ :=
    Int.floor_mono ht.1.2.le
  have hk : ⌊t⌋ ∈ factorialLowOccupiedInteriorCells N P := by
    simp only [factorialLowOccupiedInteriorCells, Finset.mem_filter,
      Finset.mem_Icc]
    exact ⟨⟨hklo, hkhi⟩, t, ht, rfl⟩
  simp only [mem_iUnion]
  refine ⟨⌊t⌋, ⟨hk, ?_⟩⟩
  exact ⟨Int.floor_le t, Int.lt_floor_add_one t⟩

theorem factorialLowQuadraticInterior_measure_le_occupiedCell_card
    {N : ℕ} {P : ℝ} :
    (volume (factorialLowQuadraticReciprocalInteriorSet N P)).toReal ≤
      (factorialLowOccupiedInteriorCells N P).card := by
  classical
  let U : Set ℝ := ⋃ k ∈ factorialLowOccupiedInteriorCells N P,
    factorialLowUnitCell k
  have hUfinite : volume U ≠ ⊤ := (measure_biUnion_finset_le
      (μ := volume) (factorialLowOccupiedInteriorCells N P)
        factorialLowUnitCell).trans_lt
    (ENNReal.sum_lt_top.mpr (fun k hk => measure_Ico_lt_top)) |>.ne
  calc
    (volume (factorialLowQuadraticReciprocalInteriorSet N P)).toReal ≤
        (volume U).toReal :=
      measureReal_mono factorialLowQuadraticInterior_subset_occupiedCells hUfinite
    _ ≤ ∑ k ∈ factorialLowOccupiedInteriorCells N P,
        (volume (factorialLowUnitCell k)).toReal :=
      measureReal_biUnion_finset_le _ _
    _ = (factorialLowOccupiedInteriorCells N P).card := by
      simp [factorialLowUnitCell, Real.volume_Ico]

theorem factorialLowFirstBandCells_pairwiseDisjoint
    {N : ℕ} {P : ℝ} (hlog : 1 < Real.log (N : ℝ)) :
    Set.PairwiseDisjoint (↑(factorialLowOccupiedInteriorCells N P))
      (factorialLowFirstBandCell N) := by
  intro k hk l hl hkl
  change Disjoint (factorialLowFirstBandCell N k)
    (factorialLowFirstBandCell N l)
  rw [Set.disjoint_left]
  intro s hsk hsl
  obtain ⟨hleft0, _hleftRight, hright1⟩ := factorialPlateauArc_bounds hlog
  rcases lt_or_gt_of_ne hkl with hkl' | hlk'
  · have hcast : (k : ℝ) + 1 ≤ (l : ℝ) := by exact_mod_cast hkl'
    exact (not_lt_of_ge (by linarith [hcast, hleft0, hright1, hsl.1])) hsk.2
  · have hcast : (l : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast hlk'
    exact (not_lt_of_ge (by linarith [hcast, hleft0, hright1, hsk.1])) hsl.2

theorem factorialLowFirstBandUnion_measure
    {N : ℕ} {P : ℝ} (hlog : 1 < Real.log (N : ℝ)) :
    (volume (⋃ k ∈ factorialLowOccupiedInteriorCells N P,
      factorialLowFirstBandCell N k)).toReal =
      1 / (60 * (Real.log N) ^ 2) *
        (factorialLowOccupiedInteriorCells N P).card := by
  classical
  change volume.real (⋃ k ∈ factorialLowOccupiedInteriorCells N P,
    factorialLowFirstBandCell N k) = _
  rw [measureReal_biUnion_finset
    (factorialLowFirstBandCells_pairwiseDisjoint hlog)
    (fun k hk => measurableSet_Ioo)
    (h := fun k hk => measure_Ioo_lt_top.ne)]
  have hwidth := factorialPlateauArc_length hlog
  have hwidthNonneg : 0 ≤
      factorialPlateauArcRight N - factorialPlateauArcLeft N := by
    rw [hwidth]
    positivity
  simp only [factorialLowFirstBandCell, Measure.real_def, Real.volume_Ioo,
    add_sub_add_left_eq_sub]
  rw [hwidth]
  have hnonneg : 0 ≤ 1 / (60 * (Real.log N) ^ 2) := by positivity
  simp only [ENNReal.toReal_ofReal hnonneg, Finset.sum_const, nsmul_eq_mul]
  ring

theorem factorialLowFirstBandUnion_subset_innerReciprocal
    {N : ℕ} {P : ℝ} (hN : 0 < N) (hP : 200 ≤ P)
    (hlog : 1 < Real.log (N : ℝ)) :
    (⋃ k ∈ factorialLowOccupiedInteriorCells N P,
      factorialLowFirstBandCell N k) ⊆
        factorialLowInnerReciprocalScaleSet N P := by
  classical
  intro s hs
  simp only [mem_iUnion] at hs
  obtain ⟨k, hk, hsBand⟩ := hs
  have hkOcc := (Finset.mem_filter.mp hk).2
  obtain ⟨t, ht, htfloor⟩ := hkOcc
  have htY : t ∈ factorialLowQuadraticReciprocalScaleSet N P := by
    exact ⟨⟨by linarith [ht.1.1], by linarith [ht.1.2]⟩, ht.2⟩
  have hcell := factorialLow_firstBandCell_subset_innerReciprocal_of_witness
    hN hP hlog htY ht.1.1 ht.1.2
  rw [htfloor] at hcell
  exact hcell ⟨hsBand.1.le, hsBand.2.le⟩

/-- Inserting the shrinking band loses exactly its unit-cell width and no
additional power of `N` or `P`. -/
theorem factorialLowInnerReciprocal_measure_lower_by_quadraticInterior
    {N : ℕ} {P : ℝ} (hN : 0 < N) (hP : 200 ≤ P)
    (hlog : 1 < Real.log (N : ℝ)) :
    1 / (60 * (Real.log N) ^ 2) *
        (volume (factorialLowQuadraticReciprocalInteriorSet N P)).toReal ≤
      (volume (factorialLowInnerReciprocalScaleSet N P)).toReal := by
  have hSfinite : volume (factorialLowInnerReciprocalScaleSet N P) ≠ ⊤ :=
    (calc
      volume (factorialLowInnerReciprocalScaleSet N P) ≤
          volume (Ioo ((N : ℝ) / (2 * P)) ((N : ℝ) / P)) :=
        measure_mono inter_subset_left
      _ < ⊤ := measure_Ioo_lt_top).ne
  have hmono := measureReal_mono
    (factorialLowFirstBandUnion_subset_innerReciprocal hN hP hlog) hSfinite
  change (volume (⋃ k ∈ factorialLowOccupiedInteriorCells N P,
    factorialLowFirstBandCell N k)).toReal ≤
      (volume (factorialLowInnerReciprocalScaleSet N P)).toReal at hmono
  rw [factorialLowFirstBandUnion_measure hlog] at hmono
  have hcard := factorialLowQuadraticInterior_measure_le_occupiedCell_card
    (N := N) (P := P)
  have hwidthNonneg : 0 ≤ 1 / (60 * (Real.log N) ^ 2) := by positivity
  exact (mul_le_mul_of_nonneg_left hcard hwidthNonneg).trans hmono

/-- Explicit reciprocal-scale lower bound after inserting the shrinking
first-coordinate band. -/
theorem factorialLowInnerReciprocalScale_measure_lower
    {N : ℕ} {P : ℝ} (hN : 0 < N) (hP : 200 ≤ P)
    (hlog : 1 < Real.log (N : ℝ))
    (hscale : (1 / 2 : ℝ) ≤ (N : ℝ) / P ^ 2) :
    (N : ℝ) / (1920 * P * (Real.log N) ^ 2) ≤
      (volume (factorialLowInnerReciprocalScaleSet N P)).toReal := by
  have hPpos : 0 < P := lt_of_lt_of_le (by norm_num) hP
  have hlogne : Real.log (N : ℝ) ≠ 0 := ne_of_gt (lt_trans (by norm_num) hlog)
  have hinterior := factorialLowQuadraticReciprocalInterior_measure_lower
    hN hP hscale
  have hinsert :=
    factorialLowInnerReciprocal_measure_lower_by_quadraticInterior hN hP hlog
  calc
    (N : ℝ) / (1920 * P * (Real.log N) ^ 2) =
        1 / (60 * (Real.log N) ^ 2) * ((N : ℝ) / (32 * P)) := by
      field_simp
      ring
    _ ≤ 1 / (60 * (Real.log N) ^ 2) *
        (volume (factorialLowQuadraticReciprocalInteriorSet N P)).toReal := by
      exact mul_le_mul_of_nonneg_left hinterior (by positivity)
    _ ≤ (volume (factorialLowInnerReciprocalScaleSet N P)).toReal := hinsert

/-- Exact pointwise transport of the low-factorial inner set by `s=N/t`. -/
theorem mem_factorialLowInnerPrimeScaleSet_iff_reciprocal_mem
    {N : ℕ} {P t : ℝ} (hN : 0 < N) (hP : 0 < P) (ht : 0 < t) :
    t ∈ factorialLowInnerPrimeScaleSet N P ↔
      (N : ℝ) / t ∈ factorialLowInnerReciprocalScaleSet N P := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have h2P : (0 : ℝ) < 2 * P := by positivity
  have hcoord : (((N : ℝ) / t) ^ 2 / (N : ℝ)) = (N : ℝ) / t ^ 2 := by
    field_simp
  rw [factorialLowInnerPrimeScaleSet, factorialLowInnerReciprocalScaleSet]
  constructor
  · rintro ⟨htI, hxlo, hxhi, hylo, hyhi⟩
    refine ⟨⟨?_, ?_⟩, hxlo, hxhi, ?_, ?_⟩
    · exact (div_lt_div_iff_of_pos_left hNr h2P ht).mpr htI.2
    · exact (div_lt_div_iff_of_pos_left hNr ht hP).mpr htI.1
    · simpa only [hcoord] using hylo
    · simpa only [hcoord] using hyhi
  · rintro ⟨hsI, hxlo, hxhi, hylo, hyhi⟩
    refine ⟨⟨?_, ?_⟩, hxlo, hxhi, ?_, ?_⟩
    · exact (div_lt_div_iff_of_pos_left hNr ht hP).mp hsI.2
    · exact (div_lt_div_iff_of_pos_left hNr h2P ht).mp hsI.1
    · simpa only [hcoord] using hylo
    · simpa only [hcoord] using hyhi

theorem reciprocal_mem_factorialLowInnerPrimeScaleSet_iff
    {N : ℕ} {P s : ℝ} (hN : 0 < N) (hP : 0 < P) (hs : 0 < s) :
    (N : ℝ) / s ∈ factorialLowInnerPrimeScaleSet N P ↔
      s ∈ factorialLowInnerReciprocalScaleSet N P := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have h := mem_factorialLowInnerPrimeScaleSet_iff_reciprocal_mem
    hN hP (div_pos hNr hs)
  have hinv : (N : ℝ) / ((N : ℝ) / s) = s := by field_simp
  simpa only [hinv] using h

/-- Exact measure transport under the reciprocal substitution `s=N/t`. -/
theorem volume_factorialLowInnerPrimeScaleSet_eq_integral_reciprocal
    {N : ℕ} {P : ℝ} (hN : 0 < N) (hP : 0 < P) :
    (volume (factorialLowInnerPrimeScaleSet N P)).toReal =
      ∫ s in factorialLowInnerReciprocalScaleSet N P, (N : ℝ) / s ^ 2 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have h2P : (0 : ℝ) < 2 * P := by positivity
  have hlowPos : (0 : ℝ) < (N : ℝ) / (2 * P) := div_pos hNr h2P
  have hab : (N : ℝ) / (2 * P) ≤ (N : ℝ) / P :=
    div_le_div_of_nonneg_left hNr.le hP (by linarith)
  have hfa : (N : ℝ) / ((N : ℝ) / (2 * P)) = 2 * P := by field_simp
  have hfb : (N : ℝ) / ((N : ℝ) / P) = P := by field_simp
  have hfcont : ContinuousOn (fun s : ℝ => (N : ℝ) / s)
      (uIcc ((N : ℝ) / (2 * P)) ((N : ℝ) / P)) := by
    rw [uIcc_of_le hab]
    intro s hs
    exact (continuousAt_const.div continuousAt_id
      (ne_of_gt (hlowPos.trans_le hs.1))).continuousWithinAt
  have hfderiv : ∀ s ∈ Ioo
      (min ((N : ℝ) / (2 * P)) ((N : ℝ) / P))
      (max ((N : ℝ) / (2 * P)) ((N : ℝ) / P)),
      HasDerivAt (fun u : ℝ => (N : ℝ) / u) (-N / s ^ 2) s := by
    intro s hs
    rw [min_eq_left hab, max_eq_right hab] at hs
    exact hasDerivAt_real_const_div (N : ℝ)
      (ne_of_gt (hlowPos.trans hs.1))
  have hfnonpos : ∀ s ∈ Ioo
      (min ((N : ℝ) / (2 * P)) ((N : ℝ) / P))
      (max ((N : ℝ) / (2 * P)) ((N : ℝ) / P)),
      (-N / s ^ 2 : ℝ) ≤ 0 := by
    intro s hs
    exact div_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (Nat.cast_nonneg N)) (sq_nonneg s)
  have hsubst :
      (∫ s in (N : ℝ) / (2 * P)..(N : ℝ) / P,
        (-N / s ^ 2 : ℝ) *
          (factorialLowInnerPrimeScaleSet N P).indicator (fun _ => (1 : ℝ))
            ((N : ℝ) / s)) =
      ∫ t in 2 * P..P,
        (factorialLowInnerPrimeScaleSet N P).indicator (fun _ => (1 : ℝ)) t := by
    simpa only [smul_eq_mul, Function.comp_apply, hfa, hfb] using
      (intervalIntegral.integral_deriv_smul_comp_of_deriv_nonpos
        (g := (factorialLowInnerPrimeScaleSet N P).indicator
          (fun _ => (1 : ℝ))) hfcont hfderiv hfnonpos)
  have hTsubsetIoc : factorialLowInnerPrimeScaleSet N P ⊆ Ioc P (2 * P) :=
    (inter_subset_left.trans Ioo_subset_Ioc_self)
  have hpositiveInterval :
      (∫ t in P..2 * P,
        (factorialLowInnerPrimeScaleSet N P).indicator (fun _ => (1 : ℝ)) t) =
      (volume (factorialLowInnerPrimeScaleSet N P)).toReal := by
    rw [intervalIntegral.integral_of_le (by linarith),
      MeasureTheory.integral_indicator
        (measurableSet_factorialLowInnerPrimeScaleSet N P),
      setIntegral_const, Measure.real_def,
      Measure.restrict_apply (measurableSet_factorialLowInnerPrimeScaleSet N P),
      inter_eq_left.mpr hTsubsetIoc]
    simp
  have hright :
      (∫ t in 2 * P..P,
        (factorialLowInnerPrimeScaleSet N P).indicator (fun _ => (1 : ℝ)) t) =
      -(volume (factorialLowInnerPrimeScaleSet N P)).toReal := by
    rw [intervalIntegral.integral_symm, hpositiveInterval]
  have hSsubsetIoc : factorialLowInnerReciprocalScaleSet N P ⊆
      Ioc ((N : ℝ) / (2 * P)) ((N : ℝ) / P) := by
    intro s hs
    exact ⟨hs.1.1, hs.1.2.le⟩
  have hweightedInterval :
      (∫ s in (N : ℝ) / (2 * P)..(N : ℝ) / P,
        (factorialLowInnerReciprocalScaleSet N P).indicator
          (fun s => (N : ℝ) / s ^ 2) s) =
      ∫ s in factorialLowInnerReciprocalScaleSet N P, (N : ℝ) / s ^ 2 := by
    rw [intervalIntegral.integral_of_le hab,
      MeasureTheory.integral_indicator
        (measurableSet_factorialLowInnerReciprocalScaleSet N P),
      Measure.restrict_restrict
        (measurableSet_factorialLowInnerReciprocalScaleSet N P),
      inter_eq_left.mpr hSsubsetIoc]
  have hleft :
      (∫ s in (N : ℝ) / (2 * P)..(N : ℝ) / P,
        (-N / s ^ 2 : ℝ) *
          (factorialLowInnerPrimeScaleSet N P).indicator (fun _ => (1 : ℝ))
            ((N : ℝ) / s)) =
      -(∫ s in factorialLowInnerReciprocalScaleSet N P, (N : ℝ) / s ^ 2) := by
    calc
      _ = ∫ s in (N : ℝ) / (2 * P)..(N : ℝ) / P,
          -((factorialLowInnerReciprocalScaleSet N P).indicator
            (fun s => (N : ℝ) / s ^ 2) s) := by
        apply intervalIntegral.integral_congr
        intro s hs
        rw [uIcc_of_le hab] at hs
        have hspos : 0 < s := hlowPos.trans_le hs.1
        have hmem := reciprocal_mem_factorialLowInnerPrimeScaleSet_iff
          hN hP hspos
        by_cases hsS : s ∈ factorialLowInnerReciprocalScaleSet N P
        · have htT := hmem.mpr hsS
          simp [Set.indicator_of_mem hsS, Set.indicator_of_mem htT, neg_div]
        · have htT : (N : ℝ) / s ∉ factorialLowInnerPrimeScaleSet N P :=
            fun ht => hsS (hmem.mp ht)
          simp [Set.indicator, hsS, htT]
      _ = -(∫ s in (N : ℝ) / (2 * P)..(N : ℝ) / P,
          (factorialLowInnerReciprocalScaleSet N P).indicator
            (fun s => (N : ℝ) / s ^ 2) s) := by
        rw [intervalIntegral.integral_neg]
      _ = _ := by rw [hweightedInterval]
  rw [hleft, hright] at hsubst
  linarith

theorem factorialLow_reciprocalJacobian_lower_on_sourceInterval
    {N : ℕ} {P s : ℝ} (hN : 0 < N) (hP : 0 < P)
    (hspos : 0 < s) (hsle : s ≤ (N : ℝ) / P) :
    P ^ 2 / N ≤ (N : ℝ) / s ^ 2 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hmul : s * P ≤ N := (le_div_iff₀ hP).mp hsle
  rw [div_le_div_iff₀ hNr (sq_pos_of_pos hspos)]
  nlinarith [mul_self_le_mul_self (mul_nonneg hspos.le hP.le) hmul]

theorem integrableOn_factorialLow_reciprocalJacobian_innerScaleSet
    {N : ℕ} {P : ℝ} (hN : 0 < N) (hP : 0 < P) :
    IntegrableOn (fun s : ℝ => (N : ℝ) / s ^ 2)
      (factorialLowInnerReciprocalScaleSet N P) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have h2P : (0 : ℝ) < 2 * P := by positivity
  have hlowPos : (0 : ℝ) < (N : ℝ) / (2 * P) := div_pos hNr h2P
  have hcont : ContinuousOn (fun s : ℝ => (N : ℝ) / s ^ 2)
      (Icc ((N : ℝ) / (2 * P)) ((N : ℝ) / P)) := by
    intro s hs
    exact (continuousAt_const.div (continuousAt_id.pow 2)
      (pow_ne_zero 2 (ne_of_gt (hlowPos.trans_le hs.1)))).continuousWithinAt
  apply (hcont.integrableOn_compact isCompact_Icc).mono_set
  intro s hs
  exact ⟨hs.1.1.le, hs.1.2.le⟩

/-- The first reciprocal Jacobian converts the reciprocal-set measure into
prime-scale measure without any additional logarithmic loss. -/
theorem factorialLow_reciprocalScale_measure_mul_jacobian_le_primeScale_measure
    {N : ℕ} {P : ℝ} (hN : 0 < N) (hP : 0 < P) :
    P ^ 2 / N *
        (volume (factorialLowInnerReciprocalScaleSet N P)).toReal ≤
      (volume (factorialLowInnerPrimeScaleSet N P)).toReal := by
  have hconst : Integrable (fun _ : ℝ => P ^ 2 / N)
      (volume.restrict (factorialLowInnerReciprocalScaleSet N P)) :=
    (continuousOn_const.integrableOn_compact isCompact_Icc).mono_set (by
      intro s hs
      exact ⟨hs.1.1.le, hs.1.2.le⟩)
  have hjac : Integrable (fun s : ℝ => (N : ℝ) / s ^ 2)
      (volume.restrict (factorialLowInnerReciprocalScaleSet N P)) :=
    integrableOn_factorialLow_reciprocalJacobian_innerScaleSet hN hP
  have hmono : (fun _ : ℝ => P ^ 2 / N) ≤ᶠ[ae
      (volume.restrict (factorialLowInnerReciprocalScaleSet N P))]
      (fun s : ℝ => (N : ℝ) / s ^ 2) := by
    filter_upwards [ae_restrict_mem
      (measurableSet_factorialLowInnerReciprocalScaleSet N P)] with s hs
    have hlow : (0 : ℝ) < (N : ℝ) / (2 * P) := by positivity
    exact factorialLow_reciprocalJacobian_lower_on_sourceInterval hN hP
      (hlow.trans hs.1.1) hs.1.2.le
  have hmain := integral_mono_ae hconst hjac hmono
  rw [setIntegral_const, Measure.real_def, smul_eq_mul] at hmain
  rw [volume_factorialLowInnerPrimeScaleSet_eq_integral_reciprocal hN hP]
  simpa [mul_comm] using hmain

/-- Complete shrinking-band geometry at a real prime scale. -/
theorem factorialLowInnerPrimeScale_measure_lower
    {N : ℕ} {P : ℝ} (hN : 0 < N) (hP : 200 ≤ P)
    (hlog : 1 < Real.log (N : ℝ))
    (hscale : (1 / 2 : ℝ) ≤ (N : ℝ) / P ^ 2) :
    P / (1920 * (Real.log N) ^ 2) ≤
      (volume (factorialLowInnerPrimeScaleSet N P)).toReal := by
  have hPpos : 0 < P := lt_of_lt_of_le (by norm_num) hP
  have hlogne : Real.log (N : ℝ) ≠ 0 := ne_of_gt (lt_trans (by norm_num) hlog)
  have hrecip := factorialLowInnerReciprocalScale_measure_lower
    hN hP hlog hscale
  have hjac :=
    factorialLow_reciprocalScale_measure_mul_jacobian_le_primeScale_measure
      hN hPpos
  calc
    P / (1920 * (Real.log N) ^ 2) =
        P ^ 2 / N * ((N : ℝ) / (1920 * P * (Real.log N) ^ 2)) := by
      have hNne : (N : ℝ) ≠ 0 := by positivity
      field_simp
    _ ≤ P ^ 2 / N *
        (volume (factorialLowInnerReciprocalScaleSet N P)).toReal := by
      exact mul_le_mul_of_nonneg_left hrecip (by positivity)
    _ ≤ (volume (factorialLowInnerPrimeScaleSet N P)).toReal := hjac

/-- At Tao's scale `P=H log² N`, the shrinking first band is exactly offset
by the logarithmic enlargement of the prime interval. -/
theorem factorialLowInnerPrimeScale_measure_lower_at_factorialPrimeScale
    {N H : ℕ} (hN : 0 < N) (hH : 0 < H)
    (hlog : 1 < Real.log (N : ℝ))
    (hP200 : 200 ≤ factorialPrimeScale N H)
    (hlow : factorialPrimeScale N H ≤ Real.sqrt (2 * (N : ℝ))) :
    (H : ℝ) / 1920 ≤
      (volume (factorialLowInnerPrimeScaleSet N
        (factorialPrimeScale N H))).toReal := by
  have hLpos : 0 < Real.log (N : ℝ) := lt_trans (by norm_num) hlog
  have hPpos : 0 < factorialPrimeScale N H := by
    rw [factorialPrimeScale]
    positivity
  have hsqrtSq : (Real.sqrt (2 * (N : ℝ))) ^ 2 = 2 * (N : ℝ) := by
    rw [Real.sq_sqrt]
    positivity
  have hPsq : (factorialPrimeScale N H) ^ 2 ≤ 2 * (N : ℝ) := by
    have := (sq_le_sq₀ hPpos.le (Real.sqrt_nonneg _)).mpr hlow
    rwa [hsqrtSq] at this
  have hscale : (1 / 2 : ℝ) ≤
      (N : ℝ) / (factorialPrimeScale N H) ^ 2 := by
    rw [le_div_iff₀ (sq_pos_of_pos hPpos)]
    nlinarith
  have hlower := factorialLowInnerPrimeScale_measure_lower
    hN hP200 hlog hscale
  calc
    (H : ℝ) / 1920 = factorialPrimeScale N H /
        (1920 * (Real.log N) ^ 2) := by
      rw [factorialPrimeScale]
      field_simp
    _ ≤ (volume (factorialLowInnerPrimeScaleSet N
        (factorialPrimeScale N H))).toReal := hlower

theorem factorialQuadraticBump_pos_of_mem_innerInterval
    {y : ℝ} (hylo : (1 / 100 : ℝ) ≤ y) (hyhi : y ≤ 89 / 100) :
    0 < smoothPeriodicIntervalBump 0 (9 / 10) y := by
  simp only [smoothPeriodicIntervalBump]
  apply expNegInvGlue.pos_of_pos
  apply mul_pos
  · apply Real.sin_pos_of_pos_of_lt_pi
    · exact mul_pos Real.pi_pos (by norm_num at hylo ⊢; linarith)
    · have := mul_lt_mul_of_pos_left
        (show y - 0 < (1 : ℝ) by norm_num at hyhi ⊢; linarith)
        Real.pi_pos
      simpa using this
  · apply Real.sin_pos_of_pos_of_lt_pi
    · exact mul_pos Real.pi_pos (by norm_num at hyhi ⊢; linarith)
    · have := mul_lt_mul_of_pos_left
        (show 9 / 10 - y < (1 : ℝ) by norm_num at hylo ⊢; linarith)
        Real.pi_pos
      simpa using this

/-- The fixed quadratic bump has a positive uniform minimum on the smaller
fractional band used in the geometric construction. -/
theorem exists_pos_le_factorialQuadraticBump_of_innerFractionalBand :
    ∃ c : ℝ, 0 < c ∧ ∀ y : ℝ,
      (1 / 100 : ℝ) ≤ Int.fract y → Int.fract y ≤ 89 / 100 →
      c ≤ smoothPeriodicIntervalBump 0 (9 / 10) y := by
  let J : Set ℝ := Icc (1 / 100 : ℝ) (89 / 100 : ℝ)
  have hcompact : IsCompact J := isCompact_Icc
  have hne : J.Nonempty := by
    exact ⟨(1 / 2 : ℝ), by constructor <;> norm_num⟩
  have hcont : Continuous (smoothPeriodicIntervalBump 0 (9 / 10)) :=
    (smoothPeriodicIntervalBump_contDiff 0 (9 / 10)).continuous
  obtain ⟨z, hz, hmin⟩ := hcompact.exists_isMinOn hne hcont.continuousOn
  refine ⟨smoothPeriodicIntervalBump 0 (9 / 10) z,
    factorialQuadraticBump_pos_of_mem_innerInterval hz.1 hz.2, ?_⟩
  intro y hylo hyhi
  have hperiod := smoothPeriodicIntervalBump_add_int
    0 (9 / 10) (Int.fract y) ⌊y⌋
  have heq : smoothPeriodicIntervalBump 0 (9 / 10) y =
      smoothPeriodicIntervalBump 0 (9 / 10) (Int.fract y) := by
    simpa only [Int.fract_add_floor] using hperiod
  rw [heq]
  exact hmin ⟨hylo, hyhi⟩

theorem factorialLowPrimeIntegralIntegrand_re_nonneg
    (N : ℕ) {t : ℝ} (ht : 1 < t) :
    0 ≤ (factorialLowObstructionWeight N
      ((N : ℝ) / t, (N : ℝ) / t ^ 2) / Real.log t).re := by
  change 0 ≤ (Complex.ofReal
    (factorialNormalizedPlateauWeight N ((N : ℝ) / t) *
      smoothPeriodicIntervalBump 0 (9 / 10) ((N : ℝ) / t ^ 2)) /
        Complex.ofReal (Real.log t)).re
  rw [← Complex.ofReal_div, Complex.ofReal_re]
  exact div_nonneg
    (mul_nonneg (factorialNormalizedPlateauWeight_nonneg N _)
      (expNegInvGlue.nonneg _))
    (Real.log_nonneg ht.le)

theorem integrableOn_factorialLowPrimeIntegralIntegrand
    {N : ℕ} {P : ℝ} (hP : 2 ≤ P) :
    IntegrableOn (fun t : ℝ =>
      factorialLowObstructionWeight N
        ((N : ℝ) / t, (N : ℝ) / t ^ 2) / Real.log t)
      (Ioo P (2 * P)) := by
  have hPpos : 0 < P := lt_of_lt_of_le (by norm_num) hP
  have hcont : ContinuousOn (fun t : ℝ =>
      factorialLowObstructionWeight N
        ((N : ℝ) / t, (N : ℝ) / t ^ 2) / Real.log t)
      (Icc P (2 * P)) := by
    intro t ht
    have htOne : (1 : ℝ) < t := lt_of_lt_of_le (by norm_num)
      (hP.trans ht.1)
    have htne : t ≠ 0 := ne_of_gt (lt_trans (by norm_num) htOne)
    have hlogne : Real.log t ≠ 0 := ne_of_gt (Real.log_pos htOne)
    apply ContinuousAt.continuousWithinAt
    have hpair : ContinuousAt (fun u : ℝ =>
        ((N : ℝ) / u, (N : ℝ) / u ^ 2)) t :=
      (continuousAt_const.div continuousAt_id htne).prodMk
        (continuousAt_const.div (continuousAt_id.pow 2) (pow_ne_zero 2 htne))
    have hnum : ContinuousAt (fun u : ℝ =>
        factorialLowObstructionWeight N
          ((N : ℝ) / u, (N : ℝ) / u ^ 2)) t :=
      (factorialLowObstructionWeight_contDiff N).continuous.continuousAt.comp hpair
    have hden : ContinuousAt (fun u : ℝ => (Real.log u : ℂ)) t := by
      fun_prop
    exact hnum.div hden (by simpa only [Complex.ofReal_ne_zero] using hlogne)
  exact (hcont.integrableOn_compact isCompact_Icc).mono_set Ioo_subset_Icc_self

/-- The actual low-`P` obstruction integral dominates the measure of its
inner geometric set. -/
theorem norm_factorialLowPrimeEquidistributionIntegral_lower_bound_by_innerMeasure
    (c : ℝ)
    (hcB : ∀ y : ℝ,
      (1 / 100 : ℝ) ≤ Int.fract y → Int.fract y ≤ 89 / 100 →
      c ≤ smoothPeriodicIntervalBump 0 (9 / 10) y)
    {N : ℕ} {P : ℝ} (hP : 2 ≤ P)
    (hlog : 1 < Real.log (N : ℝ)) :
    c / Real.log (2 * P) *
        (volume (factorialLowInnerPrimeScaleSet N P)).toReal ≤
      ‖primeEquidistributionIntegral (Ioo P (2 * P))
        (factorialLowObstructionWeight N) (N : ℝ) (N : ℝ) 2‖ := by
  let f : ℝ → ℝ := fun t =>
    (factorialLowObstructionWeight N
      ((N : ℝ) / t, (N : ℝ) / t ^ 2) / Real.log t).re
  let g : ℝ → ℝ := (factorialLowInnerPrimeScaleSet N P).indicator
    (fun _ => c / Real.log (2 * P))
  have hf : Integrable f (volume.restrict (Ioo P (2 * P))) :=
    (integrableOn_factorialLowPrimeIntegralIntegrand hP).re
  have hg : Integrable g (volume.restrict (Ioo P (2 * P))) :=
    (integrable_const (c / Real.log (2 * P))).indicator
      (measurableSet_factorialLowInnerPrimeScaleSet N P)
  have hmono : g ≤ᶠ[ae (volume.restrict (Ioo P (2 * P)))] f := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t htI
    by_cases htGood : t ∈ factorialLowInnerPrimeScaleSet N P
    · dsimp [g]
      rw [Set.indicator_of_mem htGood]
      rcases htGood.2 with ⟨hxlo, hxhi, hylo, hyhi⟩
      have hplateau := (factorialNormalizedPlateauWeight_spec hlog).plateau
        ((N : ℝ) / t) hxlo hxhi
      have hbump := hcB ((N : ℝ) / t ^ 2) hylo hyhi
      have hweight : c ≤ (factorialLowObstructionWeight N
          ((N : ℝ) / t, (N : ℝ) / t ^ 2)).re := by
        simp only [factorialLowObstructionWeight, Complex.ofReal_re, hplateau,
          one_mul]
        exact hbump
      have htOne : (1 : ℝ) < t := lt_of_lt_of_le (by norm_num)
        (hP.trans htI.1.le)
      have hlogt : 0 < Real.log t := Real.log_pos htOne
      have hlogLe : Real.log t ≤ Real.log (2 * P) :=
        Real.strictMonoOn_log.monotoneOn (lt_trans (by norm_num) htOne)
          (mul_pos (by norm_num) (lt_of_lt_of_le (by norm_num) hP)) htI.2.le
      dsimp [f]
      change c / Real.log (2 * P) ≤
        (Complex.ofReal (factorialLowObstructionWeight N
          ((N : ℝ) / t, (N : ℝ) / t ^ 2)).re /
            Complex.ofReal (Real.log t)).re
      rw [← Complex.ofReal_div, Complex.ofReal_re]
      exact div_le_div₀ (factorialLowObstructionWeight_re_nonneg N _)
        hweight hlogt hlogLe
    · dsimp [g]
      simp only [Set.indicator, htGood, ↓reduceIte]
      dsimp [f]
      exact factorialLowPrimeIntegralIntegrand_re_nonneg N
        (lt_of_lt_of_le (by norm_num) (hP.trans htI.1.le))
  have hmain := integral_mono_ae hg hf hmono
  dsimp [g] at hmain
  have hsubset : factorialLowInnerPrimeScaleSet N P ⊆ Ioo P (2 * P) :=
    inter_subset_left
  rw [integral_indicator (measurableSet_factorialLowInnerPrimeScaleSet N P),
    setIntegral_const, Measure.real_def,
    Measure.restrict_apply (measurableSet_factorialLowInnerPrimeScaleSet N P),
    inter_eq_left.mpr hsubset] at hmain
  simp only [smul_eq_mul] at hmain
  calc
    c / Real.log (2 * P) *
        (volume (factorialLowInnerPrimeScaleSet N P)).toReal =
      (volume (factorialLowInnerPrimeScaleSet N P)).toReal *
        (c / Real.log (2 * P)) := by ring
    _ ≤ ∫ t in Ioo P (2 * P), f t := hmain
    _ = (primeEquidistributionIntegral (Ioo P (2 * P))
          (factorialLowObstructionWeight N) (N : ℝ) (N : ℝ) 2).re := by
      rw [primeEquidistributionIntegral, ← Complex.reCLM_apply,
        ← Complex.reCLM.integral_comp_comm
          (integrableOn_factorialLowPrimeIntegralIntegrand hP)]
      rfl
    _ ≤ ‖primeEquidistributionIntegral (Ioo P (2 * P))
          (factorialLowObstructionWeight N) (N : ℝ) (N : ℝ) 2‖ :=
      Complex.re_le_norm _

theorem exists_norm_factorialLowPrimeEquidistributionIntegral_lower_bound_by_innerMeasure
    {N : ℕ} {P : ℝ} (hP : 2 ≤ P)
    (hlog : 1 < Real.log (N : ℝ)) :
    ∃ c : ℝ, 0 < c ∧
      c / Real.log (2 * P) *
          (volume (factorialLowInnerPrimeScaleSet N P)).toReal ≤
        ‖primeEquidistributionIntegral (Ioo P (2 * P))
          (factorialLowObstructionWeight N) (N : ℝ) (N : ℝ) 2‖ := by
  obtain ⟨c, hc, hcB⟩ :=
    exists_pos_le_factorialQuadraticBump_of_innerFractionalBand
  exact ⟨c, hc,
    norm_factorialLowPrimeEquidistributionIntegral_lower_bound_by_innerMeasure
      c hcB hP hlog⟩

/-- Quantitative lower bound for the actual low-`P` obstruction integral at
Tao's enlarged prime scale. -/
theorem factorialLowPrimeEquidistributionIntegral_norm_lower
    (c : ℝ) (hc : 0 < c)
    (hcB : ∀ y : ℝ,
      (1 / 100 : ℝ) ≤ Int.fract y → Int.fract y ≤ 89 / 100 →
      c ≤ smoothPeriodicIntervalBump 0 (9 / 10) y)
    {N H : ℕ} (hN : 0 < N) (hH : 0 < H)
    (hlog : 1 < Real.log (N : ℝ))
    (hP200 : 200 ≤ factorialPrimeScale N H)
    (hlow : factorialPrimeScale N H ≤ Real.sqrt (2 * (N : ℝ))) :
    c * (H : ℝ) /
        (1920 * Real.log (2 * factorialPrimeScale N H)) ≤
      ‖primeEquidistributionIntegral
        (Ioo (factorialPrimeScale N H) (2 * factorialPrimeScale N H))
        (factorialLowObstructionWeight N) (N : ℝ) (N : ℝ) 2‖ := by
  have hP2 : 2 ≤ factorialPrimeScale N H := by linarith
  have hPpos : 0 < factorialPrimeScale N H :=
    lt_of_lt_of_le (by norm_num) hP2
  have hlog2Ppos : 0 < Real.log (2 * factorialPrimeScale N H) :=
    Real.log_pos (by nlinarith)
  have hmeasure :=
    factorialLowInnerPrimeScale_measure_lower_at_factorialPrimeScale
      hN hH hlog hP200 hlow
  have hweighted :=
    norm_factorialLowPrimeEquidistributionIntegral_lower_bound_by_innerMeasure
      c hcB hP2 hlog
  calc
    c * (H : ℝ) / (1920 * Real.log (2 * factorialPrimeScale N H)) =
        c / Real.log (2 * factorialPrimeScale N H) * ((H : ℝ) / 1920) := by
      field_simp
    _ ≤ c / Real.log (2 * factorialPrimeScale N H) *
        (volume (factorialLowInnerPrimeScaleSet N
          (factorialPrimeScale N H))).toReal := by
      exact mul_le_mul_of_nonneg_left hmeasure (div_nonneg hc.le hlog2Ppos.le)
    _ ≤ ‖primeEquidistributionIntegral
        (Ioo (factorialPrimeScale N H) (2 * factorialPrimeScale N H))
        (factorialLowObstructionWeight N) (N : ℝ) (N : ℝ) 2‖ := hweighted

/-- Completion of Tao's low-`P` contradiction, conditional on the same
upper-scale inequality used in the high-`P` branch. -/
theorem eventually_not_factorialThree_of_low_primeScale_and_growth
    (h25 : TaoTheorem25SpecializedConclusion) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop, ∀ {H a : ℕ},
      2 ≤ H → 1 ≤ a → a < N →
      squarefreeComponent (consecutiveProduct N H) =
        squarefreeComponent a.factorial →
      factorialPrimeScale N H ≤ Real.sqrt (2 * (N : ℝ)) →
      2 ≤ factorialPrimeScale N H →
      4 * factorialPrimeScale N H ≤ (N : ℝ) →
      Real.exp ((Real.log N) ^ (2 / 3 + η)) < H → False := by
  obtain ⟨c, hc, hcB⟩ :=
    exists_pos_le_factorialQuadraticBump_of_innerFractionalBand
  obtain ⟨K, hK, hupper⟩ :=
    exists_eventually_factorialLowObstructionPolynomialUpper_of_growth
      h25 hη (by norm_num : (0 : ℝ) < 30)
  have hlogPowTop : Tendsto (fun N : ℕ => (Real.log N) ^ 5) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (5 : ℕ) ≠ 0)).comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hlargeLog : ∀ᶠ N : ℕ in atTop,
      1920 * K / c < (Real.log N) ^ 5 :=
    hlogPowTop.eventually (eventually_gt_atTop _)
  filter_upwards [hupper, hlargeLog, eventually_one_lt_log_nat,
    eventually_two_hundred_le_of_veryBad_growth hη,
    eventually_ge_atTop (1 : ℕ)] with
      N hupperN hlargeLogN hlog hH200 hN
  intro H a hH ha haN hcomponent hlow hP hfour hgrowth
  let P : ℝ := factorialPrimeScale N H
  let L : ℝ := Real.log N
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast hN
  have hHreal : 0 < (H : ℝ) := by positivity
  have hPpos : 0 < P := lt_of_lt_of_le (by norm_num) hP
  have hLpos : 0 < L := by
    dsimp only [L]
    linarith
  have hlogPpos : 0 < Real.log P :=
    Real.log_pos (lt_of_lt_of_le (by norm_num) hP)
  have hlog2Ppos : 0 < Real.log (2 * P) :=
    Real.log_pos (by nlinarith)
  have hLsqOne : (1 : ℝ) ≤ L ^ 2 := by nlinarith
  have hPformula : P = (H : ℝ) * L ^ 2 := by
    rfl
  have hHleP : (H : ℝ) ≤ P := by
    rw [hPformula]
    nlinarith
  have hP200 : 200 ≤ factorialPrimeScale N H := by
    have hH200' : (200 : ℝ) ≤ H := by exact_mod_cast hH200 H hgrowth
    simpa only [P] using hH200'.trans hHleP
  have hlower := factorialLowPrimeEquidistributionIntegral_norm_lower
    c hc hcB (by omega : 0 < N) (by omega : 0 < H) hlog hP200 hlow
  have hupperRaw := hupperN hH ha haN hcomponent hP hgrowth
  have hupperNat :
      ‖primeEquidistributionIntegral (Ioo P (2 * P))
          (factorialLowObstructionWeight N) (N : ℝ) (N : ℝ) 2‖ ≤
        K * L ^ 12 * P / (Real.log P) ^ (30 : ℕ) := by
    have hpow : (Real.log P) ^ (30 : ℝ) =
        (Real.log P) ^ (30 : ℕ) := Real.rpow_natCast _ _
    simpa only [P, L, hpow] using hupperRaw
  have hs : c * (H : ℝ) / (1920 * Real.log (2 * P)) ≤
      K * L ^ 12 * P / (Real.log P) ^ (30 : ℕ) := by
    have hlowerP : c * (H : ℝ) / (1920 * Real.log (2 * P)) ≤
        ‖primeEquidistributionIntegral (Ioo P (2 * P))
          (factorialLowObstructionWeight N) (N : ℝ) (N : ℝ) 2‖ := by
      simpa only [P] using hlower
    exact hlowerP.trans hupperNat
  have hleftDen : 0 < 1920 * Real.log (2 * P) := by positivity
  have hrightDen : 0 < (Real.log P) ^ (30 : ℕ) := by positivity
  have hcross :
      (c * (H : ℝ)) * (Real.log P) ^ (30 : ℕ) ≤
        (K * L ^ 12 * P) * (1920 * Real.log (2 * P)) :=
    (div_le_div_iff₀ hleftDen hrightDen).mp hs
  have hcancel : c * (Real.log P) ^ (30 : ℕ) ≤
      (K * L ^ 12 * L ^ 2) * (1920 * Real.log (2 * P)) := by
    apply (mul_le_mul_iff_of_pos_right hHreal).mp
    calc
      (c * (Real.log P) ^ (30 : ℕ)) * (H : ℝ) =
          (c * (H : ℝ)) * (Real.log P) ^ (30 : ℕ) := by ring
      _ ≤ (K * L ^ 12 * P) * (1920 * Real.log (2 * P)) := hcross
      _ = ((K * L ^ 12 * L ^ 2) * (1920 * Real.log (2 * P))) *
          (H : ℝ) := by
        rw [hPformula]
        ring
  have htwoPLe : 2 * P ≤ (N : ℝ) := by
    dsimp only [P] at hfour ⊢
    nlinarith
  have hlog2PLe : Real.log (2 * P) ≤ L := by
    dsimp only [L]
    exact Real.strictMonoOn_log.monotoneOn (mul_pos (by norm_num) hPpos)
      hNpos htwoPLe
  have hdenUpper : c * (Real.log P) ^ (30 : ℕ) ≤
      1920 * K * L ^ 15 := by
    calc
      c * (Real.log P) ^ (30 : ℕ) ≤
          (K * L ^ 12 * L ^ 2) * (1920 * Real.log (2 * P)) := hcancel
      _ ≤ (K * L ^ 12 * L ^ 2) * (1920 * L) := by
        gcongr
      _ = 1920 * K * L ^ 15 := by ring
  have hlogH : L ^ (2 / 3 + η) < Real.log (H : ℝ) :=
    (Real.lt_log_iff_exp_lt hHreal).mpr (by exact_mod_cast hgrowth)
  have hlogHleP : Real.log (H : ℝ) ≤ Real.log P :=
    Real.strictMonoOn_log.monotoneOn hHreal hPpos hHleP
  have hbaseGrowth : L ^ (2 / 3 : ℝ) ≤ L ^ (2 / 3 + η) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ L) (by linarith)
  have hlogLower : L ^ (2 / 3 : ℝ) < Real.log P :=
    hbaseGrowth.trans_lt (hlogH.trans_le hlogHleP)
  have hpowRaised := pow_lt_pow_left₀ hlogLower
    (Real.rpow_nonneg hLpos.le _) (by norm_num : (30 : ℕ) ≠ 0)
  have hpowLower : L ^ (20 : ℕ) < (Real.log P) ^ (30 : ℕ) := by
    have heqR : (L ^ (2 / 3 : ℝ)) ^ (30 : ℝ) = L ^ (20 : ℝ) := by
      rw [← Real.rpow_mul hLpos.le]
      norm_num
    calc
      L ^ (20 : ℕ) = L ^ (20 : ℝ) := (Real.rpow_natCast L 20).symm
      _ = (L ^ (2 / 3 : ℝ)) ^ (30 : ℝ) := heqR.symm
      _ = (L ^ (2 / 3 : ℝ)) ^ (30 : ℕ) :=
        Real.rpow_natCast (L ^ (2 / 3 : ℝ)) 30
      _ < (Real.log P) ^ (30 : ℕ) := hpowRaised
  have hmain : c * L ^ 20 ≤ 1920 * K * L ^ 15 :=
    (mul_le_mul_of_nonneg_left hpowLower.le hc.le).trans hdenUpper
  have hfactor : (c * L ^ 5) * L ^ 15 ≤ (1920 * K) * L ^ 15 := by
    calc
      (c * L ^ 5) * L ^ 15 = c * L ^ 20 := by ring
      _ ≤ 1920 * K * L ^ 15 := hmain
  have hboundedMul : c * L ^ 5 ≤ 1920 * K :=
    (mul_le_mul_iff_of_pos_right (pow_pos hLpos 15)).mp hfactor
  have hbounded : L ^ 5 ≤ 1920 * K / c := by
    rw [le_div_iff₀ hc]
    simpa only [mul_comm] using hboundedMul
  exact (not_lt_of_ge hbounded) (by simpa only [L] using hlargeLogN)

/-- Low-`P` half of Lemma 4.2 with the Baker--Harman--Pintz upper scale
discharged through the exact Proposition 2.3(ii) interface. -/
theorem eventually_not_factorialThree_of_low_primeScale_and_growth_of_inputs
    (h25 : TaoTheorem25SpecializedConclusion)
    (h23ii : TaoProposition23iiConclusion) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop, ∀ {H a : ℕ},
      2 ≤ H → 1 ≤ a → a < N →
      squarefreeComponent (consecutiveProduct N H) =
        squarefreeComponent a.factorial →
      factorialPrimeScale N H ≤ Real.sqrt (2 * (N : ℝ)) →
      2 ≤ factorialPrimeScale N H →
      Real.exp ((Real.log N) ^ (2 / 3 + η)) < H → False := by
  filter_upwards
    [eventually_not_factorialThree_of_low_primeScale_and_growth h25 hη,
      eventually_four_factorialPrimeScale_le_of_taoProposition23ii h23ii] with
      N hcontra hupper
  intro H a hH ha haN hcomponent hlow hP hgrowth
  exact hcontra hH ha haN hcomponent hlow hP
    (hupper hH ha haN hcomponent) hgrowth

/-- Full analytic contradiction in Lemma 4.2, obtained by splitting at
`P = √(2N)` and invoking the now-complete low- and high-scale arguments. -/
theorem eventually_not_factorialThree_of_growth_of_inputs
    (h25 : TaoTheorem25SpecializedConclusion)
    (h23ii : TaoProposition23iiConclusion) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop, ∀ {H a : ℕ},
      2 ≤ H → 1 ≤ a → a < N →
      squarefreeComponent (consecutiveProduct N H) =
        squarefreeComponent a.factorial →
      2 ≤ factorialPrimeScale N H →
      Real.exp ((Real.log N) ^ (2 / 3 + η)) < H → False := by
  filter_upwards
    [eventually_not_factorialThree_of_low_primeScale_and_growth_of_inputs
      h25 h23ii hη,
      eventually_not_factorialThree_of_large_primeScale_and_growth_of_inputs
        h25 h23ii hη] with N hlowContra hhighContra
  intro H a hH ha haN hcomponent hP hgrowth
  rcases le_or_gt (factorialPrimeScale N H)
      (Real.sqrt (2 * (N : ℝ))) with hlow | hhigh
  · exact hlowContra hH ha haN hcomponent hlow hP hgrowth
  · exact hhighContra hH ha haN hcomponent hhigh hP hgrowth

/-- Exact fixed-slack formulation of Tao's Lemma 4.2.  Quantifying over every
positive `η` is the formal `2/3+o(1)` exponent convention used downstream. -/
def TaoLemma42Conclusion : Prop :=
  ∀ η : ℝ, 0 < η →
    ∀ᶠ N : ℕ in atTop, ∀ {H a : ℕ},
      2 ≤ H → 1 ≤ a → a < N →
      squarefreeComponent (consecutiveProduct N H) =
        squarefreeComponent a.factorial →
      (H : ℝ) ≤ Real.exp ((Real.log N) ^ (2 / 3 + η))

/-- The specialized Theorem 2.5 and Tao's Proposition 2.3(ii) imply the full
fixed-slack statement of Lemma 4.2. -/
theorem taoLemma42_of_inputs
    (h25 : TaoTheorem25SpecializedConclusion)
    (h23ii : TaoProposition23iiConclusion) :
    TaoLemma42Conclusion := by
  intro η hη
  filter_upwards
    [eventually_not_factorialThree_of_growth_of_inputs h25 h23ii hη,
      eventually_one_lt_log_nat] with N hcontra hlog
  intro H a hH ha haN hcomponent
  have hP : 2 ≤ factorialPrimeScale N H := by
    rw [factorialPrimeScale]
    have hHreal : (2 : ℝ) ≤ H := by exact_mod_cast hH
    have hlogSq : (1 : ℝ) < (Real.log (N : ℝ)) ^ 2 := by nlinarith
    nlinarith
  by_contra hbound
  exact hcontra hH ha haN hcomponent hP (lt_of_not_ge hbound)

/-- Source-facing Lemma 4.2 closure.  After the endpoint transfer proved in
`PrimeIntervals`, the only BHP hypothesis is the cited backward-interval
Theorem 1 statement itself. -/
theorem taoLemma42_of_bakerHarmanPintz
    (h25 : TaoTheorem25SpecializedConclusion)
    (hBHP : BakerHarmanPintzTheorem1Conclusion) :
    TaoLemma42Conclusion :=
  taoLemma42_of_inputs h25 (taoProposition23ii_of_bakerHarmanPintz hBHP)

end

end Tao2026
