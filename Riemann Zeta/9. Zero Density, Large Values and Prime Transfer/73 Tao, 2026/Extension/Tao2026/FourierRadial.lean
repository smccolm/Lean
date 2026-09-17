import Tao2026.FourierSlices

/-!
# Radial Fourier decay from directional estimates

This module performs the elementary final combination in the Fourier-decay
step of Tao's Proposition 1.12(ii).  Cubic decay in either nonzero coordinate,
together with the zero-frequency bound, implies the source's radial
`(1 + |n| + |m|) ^ (-3)` envelope.  The explicit constant `27` comes from
`1 + |n| + |m| ≤ 3 * max (1, |n|, |m|)`.
-/

namespace Tao2026

noncomputable section

open scoped ContDiff

/-- Every iterated Fréchet derivative of a `ℤ²`-periodic weight is itself
` ℤ²`-periodic. -/
theorem iteratedFDeriv_isZ2Periodic
    (W : ℝ × ℝ → ℂ) (hper : IsZ2Periodic W)
    (i : ℕ) (x y : ℝ) (m n : ℤ) :
    iteratedFDeriv ℝ i W (x + m, y + n) = iteratedFDeriv ℝ i W (x, y) := by
  let a : ℝ × ℝ := ((m : ℝ), (n : ℝ))
  have htranslate : (fun z : ℝ × ℝ => W (a + z)) = W := by
    funext z
    dsimp [a]
    simpa [add_comm] using hper z.1 z.2 m n
  have h := iteratedFDeriv_comp_add_left (𝕜 := ℝ) (f := W) i a (x, y)
  rw [htranslate] at h
  simpa [a, add_comm] using h.symm

/-- Smooth `ℤ²`-periodicity makes every derivative-norm range bounded:
translate an arbitrary point to the compact fundamental square and use
continuity there. -/
theorem bddAbove_iteratedFDeriv_norm_range
    (W : ℝ × ℝ → ℂ) (hW : ContDiff ℝ ∞ W)
    (hper : IsZ2Periodic W) (i : ℕ) :
    BddAbove {r : ℝ | ∃ x : ℝ × ℝ, r = ‖iteratedFDeriv ℝ i W x‖} := by
  let f : ℝ × ℝ → ℝ := fun x => ‖iteratedFDeriv ℝ i W x‖
  have hi : (i : ℕ∞ω) < ∞ :=
    WithTop.coe_lt_coe.mpr (ENat.coe_lt_top i)
  have hf : Continuous f := (hW.continuous_iteratedFDeriv hi.le).norm
  have hbdd : BddAbove (f '' Set.Icc ((0 : ℝ), (0 : ℝ)) (1, 1)) :=
    isCompact_Icc.bddAbove_image hf.continuousOn
  apply BddAbove.mono _ hbdd
  rintro r ⟨x, rfl⟩
  refine ⟨(Int.fract x.1, Int.fract x.2), ?_, ?_⟩
  · exact ⟨⟨Int.fract_nonneg _, Int.fract_nonneg _⟩,
      ⟨(Int.fract_lt_one _).le, (Int.fract_lt_one _).le⟩⟩
  · dsimp [f]
    have hp := iteratedFDeriv_isZ2Periodic W hper i
      (Int.fract x.1) (Int.fract x.2) ⌊x.1⌋ ⌊x.2⌋
    simpa only [Int.fract_add_floor] using congrArg norm hp.symm

/-- Evaluate the `i`th Fréchet derivative repeatedly in one fixed coordinate
direction. -/
def pureCoordinateIteratedFDeriv
    (W : ℝ × ℝ → ℂ) (i : ℕ) (e : ℝ × ℝ)
    (x : ℝ × ℝ) : ℂ :=
  iteratedFDeriv ℝ i W x (fun _ => e)

/-- Pure coordinate derivatives inherit `ℤ²`-periodicity. -/
theorem pureCoordinateIteratedFDeriv_isZ2Periodic
    (W : ℝ × ℝ → ℂ) (hper : IsZ2Periodic W)
    (i : ℕ) (e : ℝ × ℝ) :
    IsZ2Periodic (pureCoordinateIteratedFDeriv W i e) := by
  intro x y m n
  unfold pureCoordinateIteratedFDeriv
  rw [iteratedFDeriv_isZ2Periodic W hper i x y m n]

/-- Pure coordinate derivatives of a smooth weight are continuous. -/
theorem continuous_pureCoordinateIteratedFDeriv
    (W : ℝ × ℝ → ℂ) (hW : ContDiff ℝ ∞ W)
    (i : ℕ) (e : ℝ × ℝ) :
    Continuous (pureCoordinateIteratedFDeriv W i e) := by
  have hi : (i : ℕ∞ω) < ∞ :=
    WithTop.coe_lt_coe.mpr (ENat.coe_lt_top i)
  have hd : Differentiable ℝ (iteratedFDeriv ℝ i W) := fun x =>
    hW.contDiffAt.differentiableAt_iteratedFDeriv hi
  exact (hd.continuousMultilinear_apply_const (fun _ : Fin i => e)).continuous

/-- Successive pure first-coordinate derivatives form the slice chain needed
for periodic integration by parts. -/
theorem hasDerivAt_pureCoordinateIteratedFDeriv_first
    (W : ℝ × ℝ → ℂ) (hW : ContDiff ℝ ∞ W)
    (i : ℕ) (x y : ℝ) :
    HasDerivAt (fun t => pureCoordinateIteratedFDeriv W i (1, 0) (t, y))
      (pureCoordinateIteratedFDeriv W (i + 1) (1, 0) (x, y)) x := by
  have hi : (i : ℕ∞ω) < ∞ :=
    WithTop.coe_lt_coe.mpr (ENat.coe_lt_top i)
  have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ i W) (x, y) :=
    hW.contDiffAt.differentiableAt_iteratedFDeriv hi
  have hp := hd.hasFDerivAt.continuousMultilinear_apply_const
    (fun _ : Fin i => ((1 : ℝ), (0 : ℝ)))
  have hline : HasDerivAt (fun t : ℝ => (t, y)) ((1 : ℝ), (0 : ℝ)) x :=
    (hasDerivAt_id x).prodMk (hasDerivAt_const x y)
  have hc := hp.comp_hasDerivAt x hline
  simpa [pureCoordinateIteratedFDeriv, Function.comp_def,
    iteratedFDeriv_succ_apply_left] using hc

/-- The symmetric pure second-coordinate derivative chain. -/
theorem hasDerivAt_pureCoordinateIteratedFDeriv_second
    (W : ℝ × ℝ → ℂ) (hW : ContDiff ℝ ∞ W)
    (i : ℕ) (x y : ℝ) :
    HasDerivAt (fun t => pureCoordinateIteratedFDeriv W i (0, 1) (x, t))
      (pureCoordinateIteratedFDeriv W (i + 1) (0, 1) (x, y)) y := by
  have hi : (i : ℕ∞ω) < ∞ :=
    WithTop.coe_lt_coe.mpr (ENat.coe_lt_top i)
  have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ i W) (x, y) :=
    hW.contDiffAt.differentiableAt_iteratedFDeriv hi
  have hp := hd.hasFDerivAt.continuousMultilinear_apply_const
    (fun _ : Fin i => ((0 : ℝ), (1 : ℝ)))
  have hline : HasDerivAt (fun t : ℝ => (x, t)) ((0 : ℝ), (1 : ℝ)) y :=
    (hasDerivAt_const y x).prodMk (hasDerivAt_id y)
  have hc := hp.comp_hasDerivAt y hline
  simpa [pureCoordinateIteratedFDeriv, Function.comp_def,
    iteratedFDeriv_succ_apply_left] using hc

/-- Every derivative term occurring in `taoC3Norm` is bounded by the full
norm, once its defining range is known to be bounded above. -/
theorem norm_iteratedFDeriv_le_taoC3Norm_of_bddAbove
    (W : ℝ × ℝ → ℂ)
    (hbdd : ∀ i ∈ Finset.range 4,
      BddAbove {r : ℝ | ∃ x : ℝ × ℝ, r = ‖iteratedFDeriv ℝ i W x‖})
    {i : ℕ} (hi : i ∈ Finset.range 4) (x : ℝ × ℝ) :
    ‖iteratedFDeriv ℝ i W x‖ ≤ taoC3Norm W := by
  have hterm : ‖iteratedFDeriv ℝ i W x‖ ≤
      sSup {r : ℝ | ∃ y : ℝ × ℝ, r = ‖iteratedFDeriv ℝ i W y‖} :=
    le_csSup (hbdd i hi) ⟨x, rfl⟩
  rw [taoC3Norm]
  exact hterm.trans (Finset.single_le_sum
    (fun j hj => (norm_nonneg (iteratedFDeriv ℝ j W x)).trans
      (le_csSup (hbdd j hj) ⟨x, rfl⟩)) hi)

/-- The zeroth-order term is controlled by `taoC3Norm`. -/
theorem norm_le_taoC3Norm_of_bddAbove
    (W : ℝ × ℝ → ℂ)
    (hbdd : ∀ i ∈ Finset.range 4,
      BddAbove {r : ℝ | ∃ x : ℝ × ℝ, r = ‖iteratedFDeriv ℝ i W x‖})
    (x : ℝ × ℝ) : ‖W x‖ ≤ taoC3Norm W := by
  simpa only [norm_iteratedFDeriv_zero] using
    norm_iteratedFDeriv_le_taoC3Norm_of_bddAbove W hbdd (i := 0) (by simp) x

/-- Evaluating the third Fréchet derivative three times in a unit direction
is controlled by `taoC3Norm`. -/
theorem norm_iteratedFDeriv_three_apply_le_taoC3Norm_of_bddAbove
    (W : ℝ × ℝ → ℂ)
    (hbdd : ∀ i ∈ Finset.range 4,
      BddAbove {r : ℝ | ∃ x : ℝ × ℝ, r = ‖iteratedFDeriv ℝ i W x‖})
    (e : ℝ × ℝ) (he : ‖e‖ ≤ 1) (x : ℝ × ℝ) :
    ‖iteratedFDeriv ℝ 3 W x (fun _ => e)‖ ≤ taoC3Norm W := by
  calc
    ‖iteratedFDeriv ℝ 3 W x (fun _ => e)‖ ≤
        ‖iteratedFDeriv ℝ 3 W x‖ :=
      (iteratedFDeriv ℝ 3 W x).unit_le_opNorm (by simpa using he)
    _ ≤ taoC3Norm W :=
      norm_iteratedFDeriv_le_taoC3Norm_of_bddAbove W hbdd (i := 3) (by simp) x

/-- The reciprocal cubic multiplier in a dominating coordinate is bounded by
`27` times Tao's radial cubic weight. -/
theorem fourierDerivativeMultiplier_cube_le_radial
    (a b : ℝ) (ha : 1 ≤ a) (hb : 0 ≤ b) (hba : b ≤ a) :
    (2 * Real.pi * a)⁻¹ ^ 3 ≤
      27 * (1 + a + b) ^ (-(3 : ℝ)) := by
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hpi : 1 ≤ 2 * Real.pi := by
    nlinarith [Real.pi_gt_three]
  have hmul : a ≤ 2 * Real.pi * a := by nlinarith
  have hinv : (2 * Real.pi * a)⁻¹ ≤ a⁻¹ := by
    exact (inv_le_inv₀ (by positivity) ha0).2 hmul
  have hinvpow : (2 * Real.pi * a)⁻¹ ^ 3 ≤ a⁻¹ ^ 3 :=
    pow_le_pow_left₀ (by positivity) hinv 3
  have hz : 1 + a + b ≤ 3 * a := by nlinarith
  have hzpos : 0 < 1 + a + b := by positivity
  have hpow : (1 + a + b) ^ 3 ≤ (3 * a) ^ 3 :=
    pow_le_pow_left₀ hzpos.le hz 3
  have hinv2 : ((3 * a) ^ 3)⁻¹ ≤ ((1 + a + b) ^ 3)⁻¹ := by
    exact (inv_le_inv₀ (by positivity) (by positivity)).2 hpow
  have hscale : a⁻¹ ^ 3 = 27 * ((3 * a) ^ 3)⁻¹ := by
    field_simp
    ring
  have hrpow : (1 + a + b) ^ (-(3 : ℝ)) = ((1 + a + b) ^ 3)⁻¹ := by
    rw [Real.rpow_neg hzpos.le]
    norm_num [Real.rpow_natCast]
  rw [hrpow]
  calc
    (2 * Real.pi * a)⁻¹ ^ 3 ≤ a⁻¹ ^ 3 := hinvpow
    _ = 27 * ((3 * a) ^ 3)⁻¹ := hscale
    _ ≤ 27 * ((1 + a + b) ^ 3)⁻¹ :=
      mul_le_mul_of_nonneg_left hinv2 (by norm_num)

/-- A zero-mode bound and the two directional cubic estimates combine into
Tao's radial `ℤ²` Fourier envelope. -/
theorem norm_le_twentySeven_mul_fourierDecayWeight
    (c : ℤ × ℤ → ℂ) {B : ℝ} (hB : 0 ≤ B)
    (hbase : ∀ q, ‖c q‖ ≤ B)
    (hfirst : ∀ q, q.1 ≠ 0 →
      ‖c q‖ ≤ (2 * Real.pi * |(q.1 : ℝ)|)⁻¹ ^ 3 * B)
    (hsecond : ∀ q, q.2 ≠ 0 →
      ‖c q‖ ≤ (2 * Real.pi * |(q.2 : ℝ)|)⁻¹ ^ 3 * B)
    (q : ℤ × ℤ) :
    ‖c q‖ ≤ 27 * B * fourierDecayWeight q := by
  by_cases hq₁ : q.1 = 0
  · by_cases hq₂ : q.2 = 0
    · have h := hbase q
      simp only [fourierDecayWeight, hq₁, hq₂, Int.cast_zero, abs_zero,
        add_zero, Real.one_rpow, mul_one]
      nlinarith
    · have ha : 1 ≤ |(q.2 : ℝ)| := by
        exact_mod_cast Int.one_le_abs hq₂
      have hr := fourierDerivativeMultiplier_cube_le_radial
        |(q.2 : ℝ)| |(q.1 : ℝ)| ha (abs_nonneg _) (by simp [hq₁])
      calc
        ‖c q‖ ≤ (2 * Real.pi * |(q.2 : ℝ)|)⁻¹ ^ 3 * B := hsecond q hq₂
        _ ≤ (27 * fourierDecayWeight q) * B := by
          apply mul_le_mul_of_nonneg_right _ hB
          simpa [fourierDecayWeight, add_comm, add_left_comm, add_assoc] using hr
        _ = 27 * B * fourierDecayWeight q := by ring
  · by_cases hcmp : |(q.2 : ℝ)| ≤ |(q.1 : ℝ)|
    · have ha : 1 ≤ |(q.1 : ℝ)| := by
        exact_mod_cast Int.one_le_abs hq₁
      have hr := fourierDerivativeMultiplier_cube_le_radial
        |(q.1 : ℝ)| |(q.2 : ℝ)| ha (abs_nonneg _) hcmp
      calc
        ‖c q‖ ≤ (2 * Real.pi * |(q.1 : ℝ)|)⁻¹ ^ 3 * B := hfirst q hq₁
        _ ≤ (27 * fourierDecayWeight q) * B := by
          exact mul_le_mul_of_nonneg_right
            (by simpa [fourierDecayWeight] using hr) hB
        _ = 27 * B * fourierDecayWeight q := by ring
    · have hq₂ : q.2 ≠ 0 := by
        intro hzero
        simp [hzero] at hcmp
      have ha : 1 ≤ |(q.2 : ℝ)| := by
        exact_mod_cast Int.one_le_abs hq₂
      have hrev : |(q.1 : ℝ)| ≤ |(q.2 : ℝ)| := le_of_not_ge hcmp
      have hr := fourierDerivativeMultiplier_cube_le_radial
        |(q.2 : ℝ)| |(q.1 : ℝ)| ha (abs_nonneg _) hrev
      calc
        ‖c q‖ ≤ (2 * Real.pi * |(q.2 : ℝ)|)⁻¹ ^ 3 * B := hsecond q hq₂
        _ ≤ (27 * fourierDecayWeight q) * B := by
          apply mul_le_mul_of_nonneg_right _ hB
          simpa [fourierDecayWeight, add_comm, add_left_comm, add_assoc] using hr
        _ = 27 * B * fourierDecayWeight q := by ring

/-- The source-shaped two-dimensional form: uniform bounds for the weight and
for its two pure third-coordinate derivatives imply radial cubic decay of its
actual torus Fourier coefficients. -/
theorem norm_taoFourierCoeff_le_radial_thirdDerivatives
    (W₀ W₁ W₂ W₃ V₁ V₂ V₃ : ℝ × ℝ → ℂ)
    (hper₀ : IsZ2Periodic W₀)
    (hperW₁ : IsZ2Periodic W₁) (hperW₂ : IsZ2Periodic W₂)
    (hperV₁ : IsZ2Periodic V₁) (hperV₂ : IsZ2Periodic V₂)
    (hcont₀ : Continuous W₀)
    (hcontW₁ : Continuous W₁) (hcontW₂ : Continuous W₂)
    (hcontW₃ : Continuous W₃)
    (hcontV₁ : Continuous V₁) (hcontV₂ : Continuous V₂)
    (hcontV₃ : Continuous V₃)
    (hderivW₀ : ∀ x y, HasDerivAt (fun t => W₀ (t, y)) (W₁ (x, y)) x)
    (hderivW₁ : ∀ x y, HasDerivAt (fun t => W₁ (t, y)) (W₂ (x, y)) x)
    (hderivW₂ : ∀ x y, HasDerivAt (fun t => W₂ (t, y)) (W₃ (x, y)) x)
    (hderivV₀ : ∀ x y, HasDerivAt (fun t => W₀ (x, t)) (V₁ (x, y)) y)
    (hderivV₁ : ∀ x y, HasDerivAt (fun t => V₁ (x, t)) (V₂ (x, y)) y)
    (hderivV₂ : ∀ x y, HasDerivAt (fun t => V₂ (x, t)) (V₃ (x, y)) y)
    {B : ℝ} (hB : 0 ≤ B)
    (hbound₀ : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      ‖W₀ (x, y)‖ ≤ B)
    (hboundW₃ : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      ‖W₃ (x, y)‖ ≤ B)
    (hboundV₃ : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      ‖V₃ (x, y)‖ ≤ B)
    (q : ℤ × ℤ) :
    ‖taoFourierCoeff W₀ hper₀ hcont₀ q‖ ≤
      27 * B * fourierDecayWeight q := by
  apply norm_le_twentySeven_mul_fourierDecayWeight
      (fun q => taoFourierCoeff W₀ hper₀ hcont₀ q) hB
  · intro r
    rw [taoFourierCoeff_eq_iterated W₀ hper₀ hcont₀ r]
    apply norm_fourierCoeff_le_of_norm_le
    intro y
    apply norm_fourierCoeff_le_of_norm_le
    intro x
    obtain ⟨xr, hxr, rfl⟩ := AddCircle.eq_coe_Ioc x
    obtain ⟨yr, hyr, rfl⟩ := AddCircle.eq_coe_Ioc y
    change ‖torusLift W₀ hper₀ (realPairToUnitTorus (xr, yr))‖ ≤ B
    rw [torusLift_realPairToUnitTorus]
    exact hbound₀ xr ⟨hxr.1.le, hxr.2⟩ yr ⟨hyr.1.le, hyr.2⟩
  · intro r hr
    exact norm_taoFourierCoeff_le_first_thirdDerivative
      W₀ W₁ W₂ W₃ hper₀ hperW₁ hperW₂ hcont₀ hcontW₁
      hcontW₂ hcontW₃ hderivW₀ hderivW₁ hderivW₂ hboundW₃ r hr
  · intro r hr
    exact norm_taoFourierCoeff_le_second_thirdDerivative
      W₀ V₁ V₂ V₃ hper₀ hperV₁ hperV₂ hcont₀ hcontV₁
      hcontV₂ hcontV₃ hderivV₀ hderivV₁ hderivV₂ hboundV₃ r hr

/-- The radial derivative theorem with its envelope expressed using the
project's literal `taoC3Norm`.  The two terminal slice derivatives are
identified with the corresponding pure third Fréchet derivatives. -/
theorem norm_taoFourierCoeff_le_taoC3Norm_mul_fourierDecayWeight
    (W W₁ W₂ W₃ V₁ V₂ V₃ : ℝ × ℝ → ℂ)
    (hper : IsZ2Periodic W)
    (hperW₁ : IsZ2Periodic W₁) (hperW₂ : IsZ2Periodic W₂)
    (hperV₁ : IsZ2Periodic V₁) (hperV₂ : IsZ2Periodic V₂)
    (hcont : Continuous W)
    (hcontW₁ : Continuous W₁) (hcontW₂ : Continuous W₂)
    (hcontW₃ : Continuous W₃)
    (hcontV₁ : Continuous V₁) (hcontV₂ : Continuous V₂)
    (hcontV₃ : Continuous V₃)
    (hderivW₀ : ∀ x y, HasDerivAt (fun t => W (t, y)) (W₁ (x, y)) x)
    (hderivW₁ : ∀ x y, HasDerivAt (fun t => W₁ (t, y)) (W₂ (x, y)) x)
    (hderivW₂ : ∀ x y, HasDerivAt (fun t => W₂ (t, y)) (W₃ (x, y)) x)
    (hderivV₀ : ∀ x y, HasDerivAt (fun t => W (x, t)) (V₁ (x, y)) y)
    (hderivV₁ : ∀ x y, HasDerivAt (fun t => V₁ (x, t)) (V₂ (x, y)) y)
    (hderivV₂ : ∀ x y, HasDerivAt (fun t => V₂ (x, t)) (V₃ (x, y)) y)
    (hbdd : ∀ i ∈ Finset.range 4,
      BddAbove {r : ℝ | ∃ x : ℝ × ℝ, r = ‖iteratedFDeriv ℝ i W x‖})
    (hW₃ : ∀ x, W₃ x =
      iteratedFDeriv ℝ 3 W x (fun _ => ((1 : ℝ), (0 : ℝ))))
    (hV₃ : ∀ x, V₃ x =
      iteratedFDeriv ℝ 3 W x (fun _ => ((0 : ℝ), (1 : ℝ))))
    (q : ℤ × ℤ) :
    ‖taoFourierCoeff W hper hcont q‖ ≤
      27 * taoC3Norm W * fourierDecayWeight q := by
  apply norm_taoFourierCoeff_le_radial_thirdDerivatives
    W W₁ W₂ W₃ V₁ V₂ V₃ hper hperW₁ hperW₂ hperV₁ hperV₂
    hcont hcontW₁ hcontW₂ hcontW₃ hcontV₁ hcontV₂ hcontV₃
    hderivW₀ hderivW₁ hderivW₂ hderivV₀ hderivV₁ hderivV₂
  · exact (norm_nonneg (W (0, 0))).trans (norm_le_taoC3Norm_of_bddAbove W hbdd (0, 0))
  · intro x _ y _
    exact norm_le_taoC3Norm_of_bddAbove W hbdd (x, y)
  · intro x _ y _
    rw [hW₃]
    exact norm_iteratedFDeriv_three_apply_le_taoC3Norm_of_bddAbove W hbdd
      ((1 : ℝ), (0 : ℝ)) (by simp) (x, y)
  · intro x _ y _
    rw [hV₃]
    exact norm_iteratedFDeriv_three_apply_le_taoC3Norm_of_bddAbove W hbdd
      ((0 : ℝ), (1 : ℝ)) (by simp) (x, y)

/-- Smooth periodic weights automatically satisfy the bounded-range premise
in the preceding `taoC3Norm` comparison. -/
theorem norm_taoFourierCoeff_le_taoC3Norm_mul_fourierDecayWeight_of_contDiff
    (W W₁ W₂ W₃ V₁ V₂ V₃ : ℝ × ℝ → ℂ)
    (hW : ContDiff ℝ ∞ W)
    (hper : IsZ2Periodic W)
    (hperW₁ : IsZ2Periodic W₁) (hperW₂ : IsZ2Periodic W₂)
    (hperV₁ : IsZ2Periodic V₁) (hperV₂ : IsZ2Periodic V₂)
    (hcontW₁ : Continuous W₁) (hcontW₂ : Continuous W₂)
    (hcontW₃ : Continuous W₃)
    (hcontV₁ : Continuous V₁) (hcontV₂ : Continuous V₂)
    (hcontV₃ : Continuous V₃)
    (hderivW₀ : ∀ x y, HasDerivAt (fun t => W (t, y)) (W₁ (x, y)) x)
    (hderivW₁ : ∀ x y, HasDerivAt (fun t => W₁ (t, y)) (W₂ (x, y)) x)
    (hderivW₂ : ∀ x y, HasDerivAt (fun t => W₂ (t, y)) (W₃ (x, y)) x)
    (hderivV₀ : ∀ x y, HasDerivAt (fun t => W (x, t)) (V₁ (x, y)) y)
    (hderivV₁ : ∀ x y, HasDerivAt (fun t => V₁ (x, t)) (V₂ (x, y)) y)
    (hderivV₂ : ∀ x y, HasDerivAt (fun t => V₂ (x, t)) (V₃ (x, y)) y)
    (hW₃ : ∀ x, W₃ x =
      iteratedFDeriv ℝ 3 W x (fun _ => ((1 : ℝ), (0 : ℝ))))
    (hV₃ : ∀ x, V₃ x =
      iteratedFDeriv ℝ 3 W x (fun _ => ((0 : ℝ), (1 : ℝ))))
    (q : ℤ × ℤ) :
    ‖taoFourierCoeff W hper hW.continuous q‖ ≤
      27 * taoC3Norm W * fourierDecayWeight q := by
  exact norm_taoFourierCoeff_le_taoC3Norm_mul_fourierDecayWeight
    W W₁ W₂ W₃ V₁ V₂ V₃ hper hperW₁ hperW₂ hperV₁ hperV₂
    hW.continuous hcontW₁ hcontW₂ hcontW₃ hcontV₁ hcontV₂ hcontV₃
    hderivW₀ hderivW₁ hderivW₂ hderivV₀ hderivV₁ hderivV₂
    (fun i _ => bddAbove_iteratedFDeriv_norm_range W hW hper i) hW₃ hV₃ q

/-- Unconditional source-facing Fourier decay: the exact public smoothness and
periodicity hypotheses imply Tao's radial cubic coefficient envelope. -/
theorem norm_taoFourierCoeff_le_taoC3Norm_mul_fourierDecayWeight_of_smooth
    (W : ℝ × ℝ → ℂ) (hW : ContDiff ℝ ∞ W)
    (hper : IsZ2Periodic W) (q : ℤ × ℤ) :
    ‖taoFourierCoeff W hper hW.continuous q‖ ≤
      27 * taoC3Norm W * fourierDecayWeight q := by
  apply norm_taoFourierCoeff_le_taoC3Norm_mul_fourierDecayWeight_of_contDiff
    W (pureCoordinateIteratedFDeriv W 1 (1, 0))
      (pureCoordinateIteratedFDeriv W 2 (1, 0))
      (pureCoordinateIteratedFDeriv W 3 (1, 0))
      (pureCoordinateIteratedFDeriv W 1 (0, 1))
      (pureCoordinateIteratedFDeriv W 2 (0, 1))
      (pureCoordinateIteratedFDeriv W 3 (0, 1)) hW hper
  · exact pureCoordinateIteratedFDeriv_isZ2Periodic W hper 1 (1, 0)
  · exact pureCoordinateIteratedFDeriv_isZ2Periodic W hper 2 (1, 0)
  · exact pureCoordinateIteratedFDeriv_isZ2Periodic W hper 1 (0, 1)
  · exact pureCoordinateIteratedFDeriv_isZ2Periodic W hper 2 (0, 1)
  · exact continuous_pureCoordinateIteratedFDeriv W hW 1 (1, 0)
  · exact continuous_pureCoordinateIteratedFDeriv W hW 2 (1, 0)
  · exact continuous_pureCoordinateIteratedFDeriv W hW 3 (1, 0)
  · exact continuous_pureCoordinateIteratedFDeriv W hW 1 (0, 1)
  · exact continuous_pureCoordinateIteratedFDeriv W hW 2 (0, 1)
  · exact continuous_pureCoordinateIteratedFDeriv W hW 3 (0, 1)
  · intro x y
    simpa [pureCoordinateIteratedFDeriv] using
      hasDerivAt_pureCoordinateIteratedFDeriv_first W hW 0 x y
  · intro x y
    simpa using hasDerivAt_pureCoordinateIteratedFDeriv_first W hW 1 x y
  · intro x y
    simpa using hasDerivAt_pureCoordinateIteratedFDeriv_first W hW 2 x y
  · intro x y
    simpa [pureCoordinateIteratedFDeriv] using
      hasDerivAt_pureCoordinateIteratedFDeriv_second W hW 0 x y
  · intro x y
    simpa using hasDerivAt_pureCoordinateIteratedFDeriv_second W hW 1 x y
  · intro x y
    simpa using hasDerivAt_pureCoordinateIteratedFDeriv_second W hW 2 x y
  · intro x
    rfl
  · intro x
    rfl

/-- The exact coefficient mass outside a square Fourier box inherits the
smooth weight's radial cubic `C³` envelope. -/
theorem taoFourierCoefficientTail_le_taoC3Norm_mul_decayTail
    (W : ℝ × ℝ → ℂ) (hW : ContDiff ℝ ∞ W)
    (hper : IsZ2Periodic W) (R : ℕ) :
    (∑' q : {q // q ∉ fourierFrequencyBox R},
        ‖taoFourierCoeff W hper hW.continuous q‖) ≤
      27 * taoC3Norm W *
        (∑' q : {q // q ∉ fourierFrequencyBox R}, fourierDecayWeight q) := by
  let c := taoFourierCoeff W hper hW.continuous
  have hc : Summable (fun q => ‖c q‖) :=
    summable_norm_of_fourierDecay c
      (norm_taoFourierCoeff_le_taoC3Norm_mul_fourierDecayWeight_of_smooth
        W hW hper)
  have hdecay : Summable
      (fun q : {q // q ∉ fourierFrequencyBox R} => fourierDecayWeight q) :=
    summable_fourierDecayWeight.subtype _
  have hmajor : Summable
      (fun q : {q // q ∉ fourierFrequencyBox R} =>
        27 * taoC3Norm W * fourierDecayWeight q) :=
    hdecay.mul_left _
  calc
    (∑' q : {q // q ∉ fourierFrequencyBox R}, ‖c q‖) ≤
        ∑' q : {q // q ∉ fourierFrequencyBox R},
          27 * taoC3Norm W * fourierDecayWeight q := by
      exact (hc.subtype _).tsum_le_tsum
        (fun q =>
          norm_taoFourierCoeff_le_taoC3Norm_mul_fourierDecayWeight_of_smooth
            W hW hper q)
        hmajor
    _ = 27 * taoC3Norm W *
        (∑' q : {q // q ∉ fourierFrequencyBox R}, fourierDecayWeight q) := by
      simpa only [mul_assoc] using
        hdecay.tsum_mul_left (27 * taoC3Norm W)

end

end Tao2026
