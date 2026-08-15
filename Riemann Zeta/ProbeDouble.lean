import RiemannZeta.GuthMaynard.DFIErrorTerms

open Complex Set MeasureTheory
open scoped BigOperators ContDiff
open Classical

namespace RiemannZeta.GuthMaynard

@[simp] theorem probe_dualTerm_zero_function
    (q : ℕ) [NeZero q] (branch : DFIVoronoiDualBranch) (n : ℕ) :
    dfiVoronoiDualTerm q branch (fun _ ↦ 0) n = 0 := by
  cases branch <;>
    simp [dfiVoronoiDualTerm, dfiVoronoiMinusTransform,
      dfiVoronoiPlusTransform, VerticalIntegral', VerticalIntegral, mellin]

noncomputable def probe_dualTerm_family_test
    {E : ℝ → ℝ → ℂ} {A B C D : ℝ}
    (hE : ContDiff ℝ ∞ (Function.uncurry E))
    (hA : 0 < A) (hAB : A ≤ B) (hC : 0 < C) (hCD : C ≤ D)
    (hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc A B ×ˢ Set.Icc C D)
    (q : ℕ) [NeZero q] (branch : DFIVoronoiDualBranch) (n : ℕ) :
    DFIVoronoiTestFunction
      (fun x ↦ dfiVoronoiDualTerm q branch (E x) n) := by
  by_cases hn : n = 0
  · subst n
    refine {
      lower := A
      upper := B
      lower_pos := hA
      lower_le_upper := hAB
      smooth := ?_
      support_subset := ?_ }
    · simpa only [dfiVoronoiDualTerm_zero] using
        (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ ↦ (0 : ℂ)))
    · intro x hx
      exfalso
      change dfiVoronoiDualTerm q branch (E x) 0 ≠ 0 at hx
      rw [dfiVoronoiDualTerm_zero] at hx
      exact hx rfl
  have hnPos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  let P : ℝ → ℂ := fun u ↦
    (n : ℂ) ^ (-(1 - (((-(1 / 2 : ℝ) : ℂ) + (u : ℂ) * I))))
  let W : ℝ → ℂ := fun u ↦ divisorWeight n * P u *
    dfiDualBranchMultiplier q branch
      (((-(1 / 2 : ℝ) : ℂ) + (u : ℂ) * I))
  let Cw : ℝ := ‖divisorWeight n‖ *
    (32 * q * dfiArchimedeanScale q ^ 2)
  have hPcont : Continuous P := by
    have hExponent : Continuous (fun u : ℝ ↦
        -(1 - (((-(1 / 2 : ℝ) : ℂ) + (u : ℂ) * I)))) := by fun_prop
    exact hExponent.const_cpow
      (Or.inl (Nat.cast_ne_zero.mpr hn))
  have hPnorm (u : ℝ) : ‖P u‖ ≤ 1 := by
    dsimp [P]
    rw [← Complex.ofReal_natCast]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hnPos]
    apply Real.rpow_le_one_of_one_le_of_nonpos
    · exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    · norm_num
  have hWcont : Continuous W := by
    apply (continuous_const.mul hPcont).mul
    simpa only [Complex.ofReal_neg, Complex.ofReal_div,
      Complex.ofReal_one] using
      (continuous_dfiDualBranchMultiplier_leftLine q branch)
  have hCw : 0 ≤ Cw := by dsimp [Cw]; positivity
  have hWbound (u : ℝ) : ‖W u‖ ≤ Cw * (1 + |u|) ^ 2 := by
    dsimp [W, Cw]
    rw [norm_mul, norm_mul]
    calc
      ‖divisorWeight n‖ * ‖P u‖ *
          ‖dfiDualBranchMultiplier q branch
            (((-(1 / 2 : ℝ) : ℂ) + (u : ℂ) * I))‖ ≤
          ‖divisorWeight n‖ * 1 *
            (32 * q * dfiArchimedeanScale q ^ 2 * (1 + |u|) ^ 2) := by
        gcongr
        · exact hPnorm u
        · simpa only [Complex.ofReal_neg, Complex.ofReal_div,
            Complex.ofReal_one] using
            (norm_dfiDualBranchMultiplier_le q branch u)
      _ = (‖divisorWeight n‖ *
          (32 * q * dfiArchimedeanScale q ^ 2)) * (1 + |u|) ^ 2 := by ring
  have hVerticalSmooth : ContDiff ℝ ∞
      (dfiParametricVerticalIntegralDeriv 0 W (-(1 / 2 : ℝ)) E) :=
    contDiff_dfiParametricVerticalIntegral hE hC hCD hSupport
      hWcont hCw hWbound _
  have hEq :
      (fun x ↦ dfiVoronoiDualTerm q branch (E x) n) =
        fun x ↦ (1 / (2 * Real.pi * I) : ℂ) *
          (I * dfiParametricVerticalIntegralDeriv 0 W
            (-(1 / 2 : ℝ)) E x) := by
    funext x
    rw [dfiVoronoiDualTerm_eq_divisorWeight_mul_initial]
    rw [← dfiEquation29TransformAt_initial]
    unfold dfiEquation29TransformAt VerticalIntegral' VerticalIntegral
      dfiEquation29Integrand dfiEquation29Multiplier
      dfiParametricVerticalIntegralDeriv W P
    simp only [smul_eq_mul, iteratedDeriv_zero]
    cases branch <;>
      simp only [dfiDualBranchMultiplier,
        Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_one] <;>
      simp_rw [← MeasureTheory.integral_const_mul] <;>
      apply MeasureTheory.integral_congr_ae <;>
      filter_upwards with u <;>
      ring
  refine {
    lower := A
    upper := B
    lower_pos := hA
    lower_le_upper := hAB
    smooth := ?_
    support_subset := ?_ }
  · rw [hEq]
    exact contDiff_const.mul (contDiff_const.mul hVerticalSmooth)
  · intro x hx
    by_contra hxnot
    have hxE : E x = fun _ ↦ 0 := by
      funext y
      by_contra hne
      exact hxnot (hSupport (show
        (x, y) ∈ Function.support (Function.uncurry E) by
          simpa only [Function.mem_support, Function.uncurry_apply_pair] using hne)).1
    change dfiVoronoiDualTerm q branch (E x) n ≠ 0 at hx
    rw [hxE, probe_dualTerm_zero_function] at hx
    exact hx rfl

theorem probe_exists_dualTerm_physical_bound
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (q : ℕ) (_hq : NeZero q)
      (branch : DFIVoronoiDualBranch) (g : ℝ → ℂ)
      (hg : DFIVoronoiTestFunction g) (n : ℕ), 0 < n →
      ‖dfiVoronoiDualTerm q branch g n‖ ≤
        K * (q : ℝ) ^ (-(1 / 2 : ℝ)) *
          dfiBesselQuarterBaseNorm g * (n : ℝ) ^ (ε - 1 / 4) := by
  obtain ⟨D, hD, hDivisor⟩ := divisorCountBound_native ε hε
  let C : ℝ := 14 * Real.pi + 8
  refine ⟨D * C, mul_nonneg hD.le (by dsimp [C]; positivity), ?_⟩
  intro q hq branch g hg n hn
  letI : NeZero q := hq
  have hqR : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hqScale : (Real.sqrt q)⁻¹ =
      (q : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hqR.le]
  have hWeight : ‖divisorWeight n‖ ≤ D * (n : ℝ) ^ ε := by
    simpa [divisorWeight] using hDivisor n hn
  have hPhysical :=
    hg.norm_dfiEquation29InitialTransform_le_besselQuarterNorm
      q branch hn (hg.integrableOn_besselQuarterWeight_mul_nat n hn)
  rw [dfiBesselQuarterNorm_eq_rpow_mul_base g n hn,
    div_eq_mul_inv, hqScale] at hPhysical
  have hTransform : ‖dfiEquation29InitialTransform q branch g n‖ ≤
      C * (q : ℝ) ^ (-(1 / 2 : ℝ)) *
        dfiBesselQuarterBaseNorm g * (n : ℝ) ^ (-(1 / 4 : ℝ)) := by
    simpa [C, mul_assoc, mul_left_comm, mul_comm] using hPhysical
  rw [dfiVoronoiDualTerm_eq_divisorWeight_mul_initial, norm_mul]
  calc
    ‖divisorWeight n‖ * ‖dfiEquation29InitialTransform q branch g n‖ ≤
        (D * (n : ℝ) ^ ε) *
          (C * (q : ℝ) ^ (-(1 / 2 : ℝ)) *
            dfiBesselQuarterBaseNorm g * (n : ℝ) ^ (-(1 / 4 : ℝ))) :=
      mul_le_mul hWeight hTransform (norm_nonneg _)
        (mul_nonneg hD.le (Real.rpow_nonneg (Nat.cast_nonneg n) _))
    _ = (D * C) * (q : ℝ) ^ (-(1 / 2 : ℝ)) *
        dfiBesselQuarterBaseNorm g *
          ((n : ℝ) ^ ε * (n : ℝ) ^ (-(1 / 4 : ℝ))) := by ring
    _ = (D * C) * (q : ℝ) ^ (-(1 / 2 : ℝ)) *
        dfiBesselQuarterBaseNorm g * (n : ℝ) ^ (ε - 1 / 4) := by
      rw [← Real.rpow_add (Nat.cast_pos.mpr hn)]
      ring_nf

theorem probe_exists_dualTerm_family_baseNorm_bound
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ {E : ℝ → ℝ → ℂ} {A B C D : ℝ},
        ContDiff ℝ ∞ (Function.uncurry E) →
        0 < A → A ≤ B → 0 < C → C ≤ D →
        Function.support (Function.uncurry E) ⊆
          Set.Icc A B ×ˢ Set.Icc C D →
        ∀ (q : ℕ) (_hq : NeZero q) (branch : DFIVoronoiDualBranch)
          (n : ℕ), 0 < n →
          dfiBesselQuarterBaseNorm
              (fun x ↦ dfiVoronoiDualTerm q branch (E x) n) ≤
            K * (q : ℝ) ^ (-(1 / 2 : ℝ)) *
              A ^ (-(1 / 4 : ℝ)) * C ^ (-(1 / 4 : ℝ)) *
              (∫ x in Set.Icc A B, ∫ y in Set.Icc C D, ‖E x y‖) *
              (n : ℝ) ^ (ε - 1 / 4) := by
  obtain ⟨K, hK, hPointwise⟩ := probe_exists_dualTerm_physical_bound ε hε
  refine ⟨K, hK, ?_⟩
  intro E A B C D hE hA hAB hC hCD hSupport q hq branch n hn
  letI : NeZero q := hq
  have hFamily : DFIVoronoiTestFunction
      (fun x ↦ dfiVoronoiDualTerm q branch (E x) n) :=
    dfiVoronoiDualTerm_family_testFunction
      hE hA hAB hC hCD hSupport q branch n
  have hFamilySupport : Function.support
      (fun x ↦ dfiVoronoiDualTerm q branch (E x) n) ⊆ Set.Icc A B := by
    intro x hx
    by_contra hxnot
    have hxE : E x = fun _ ↦ 0 := by
      funext y
      by_contra hne
      exact hxnot (hSupport (show
        (x, y) ∈ Function.support (Function.uncurry E) by
          simpa only [Function.mem_support,
            Function.uncurry_apply_pair] using hne)).1
    change dfiVoronoiDualTerm q branch (E x) n ≠ 0 at hx
    rw [hxE, dfiVoronoiDualTerm_zero_function] at hx
    exact hx rfl
  have hSliceSupport (x : ℝ) :
      Function.support (E x) ⊆ Set.Icc C D := by
    intro y hy
    exact (hSupport (show
      (x, y) ∈ Function.support (Function.uncurry E) by
        simpa only [Function.mem_support,
          Function.uncurry_apply_pair] using hy)).2
  have hSlice (x : ℝ) : DFIVoronoiTestFunction (E x) := {
    lower := C
    upper := D
    lower_pos := hC
    lower_le_upper := hCD
    smooth := hE.comp (contDiff_prodMk_right x)
    support_subset := hSliceSupport x }
  let R : ℝ := K * (q : ℝ) ^ (-(1 / 2 : ℝ)) *
    C ^ (-(1 / 4 : ℝ)) * (n : ℝ) ^ (ε - 1 / 4)
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hInnerContinuous : Continuous (fun x : ℝ ↦
      ∫ y in Set.Icc C D, ‖E x y‖) :=
    continuous_parametric_integral_of_continuous
      hE.continuous.norm isCompact_Icc
  have hLeft : IntegrableOn (fun x : ℝ ↦
      ‖dfiVoronoiDualTerm q branch (E x) n‖) (Set.Icc A B) :=
    hFamily.continuous.norm.continuousOn.integrableOn_compact isCompact_Icc
  have hRight : IntegrableOn (fun x : ℝ ↦
      R * (∫ y in Set.Icc C D, ‖E x y‖)) (Set.Icc A B) :=
    (hInnerContinuous.const_mul R).continuousOn
      |>.integrableOn_compact isCompact_Icc
  have hPoint (x : ℝ) :
      ‖dfiVoronoiDualTerm q branch (E x) n‖ ≤
        R * (∫ y in Set.Icc C D, ‖E x y‖) := by
    have hDual := hPointwise q inferInstance branch (E x) (hSlice x) n hn
    have hBase := dfiBesselQuarterBaseNorm_le_lower_rpow_mul_integral_norm
      hC (hSlice x) (hSliceSupport x)
    calc
      ‖dfiVoronoiDualTerm q branch (E x) n‖ ≤
          K * (q : ℝ) ^ (-(1 / 2 : ℝ)) *
            dfiBesselQuarterBaseNorm (E x) * (n : ℝ) ^ (ε - 1 / 4) := hDual
      _ ≤ K * (q : ℝ) ^ (-(1 / 2 : ℝ)) *
            (C ^ (-(1 / 4 : ℝ)) *
              (∫ y in Set.Icc C D, ‖E x y‖)) *
            (n : ℝ) ^ (ε - 1 / 4) := by
          gcongr
      _ = R * (∫ y in Set.Icc C D, ‖E x y‖) := by
          dsimp [R]
          ring
  have hIntegral :
      (∫ x in Set.Icc A B,
          ‖dfiVoronoiDualTerm q branch (E x) n‖) ≤
        ∫ x in Set.Icc A B,
          R * (∫ y in Set.Icc C D, ‖E x y‖) := by
    apply integral_mono_ae hLeft hRight
    filter_upwards with x
    exact hPoint x
  calc
    dfiBesselQuarterBaseNorm
        (fun x ↦ dfiVoronoiDualTerm q branch (E x) n) ≤
        A ^ (-(1 / 4 : ℝ)) *
          (∫ x in Set.Icc A B,
            ‖dfiVoronoiDualTerm q branch (E x) n‖) :=
      dfiBesselQuarterBaseNorm_le_lower_rpow_mul_integral_norm
        hA hFamily hFamilySupport
    _ ≤ A ^ (-(1 / 4 : ℝ)) *
        (∫ x in Set.Icc A B,
          R * (∫ y in Set.Icc C D, ‖E x y‖)) := by
      exact mul_le_mul_of_nonneg_left hIntegral
        (Real.rpow_nonneg hA.le _)
    _ = K * (q : ℝ) ^ (-(1 / 2 : ℝ)) *
        A ^ (-(1 / 4 : ℝ)) * C ^ (-(1 / 4 : ℝ)) *
        (∫ x in Set.Icc A B, ∫ y in Set.Icc C D, ‖E x y‖) *
        (n : ℝ) ^ (ε - 1 / 4) := by
      rw [integral_const_mul]
      dsimp [R]
      ring

theorem probe_exists_doubleDualMellinAmplitude_physical_bound
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ {E : ℝ → ℝ → ℂ} {A B C D : ℝ},
        ContDiff ℝ ∞ (Function.uncurry E) →
        0 < A → A ≤ B → 0 < C → C ≤ D →
        Function.support (Function.uncurry E) ⊆
          Set.Icc A B ×ˢ Set.Icc C D →
        ∀ (qx qy : ℕ) (_hqx : NeZero qx) (_hqy : NeZero qy)
          (xBranch yBranch : DFIVoronoiDualBranch) (m n : ℕ),
          0 < m → 0 < n →
          ‖dfiEquation24DoubleDualMellinAmplitude
              qx xBranch qy yBranch E m n‖ ≤
            K * (qx : ℝ) ^ (-(1 / 2 : ℝ)) *
              (qy : ℝ) ^ (-(1 / 2 : ℝ)) *
              A ^ (-(1 / 4 : ℝ)) * C ^ (-(1 / 4 : ℝ)) *
              (∫ x in Set.Icc A B, ∫ y in Set.Icc C D, ‖E x y‖) *
              (m : ℝ) ^ (ε / 2 - 1 / 4) *
              (n : ℝ) ^ (ε / 2 - 1 / 4) := by
  have hHalf : 0 < ε / 2 := by linarith
  obtain ⟨K₁, hK₁, hOuter⟩ :=
    exists_dfiVoronoiDualTerm_physical_bound (ε / 2) hHalf
  obtain ⟨K₂, hK₂, hFamily⟩ :=
    exists_dfiVoronoiDualTerm_family_besselQuarterBaseNorm_bound
      (ε / 2) hHalf
  refine ⟨K₁ * K₂, mul_nonneg hK₁ hK₂, ?_⟩
  intro E A B C D hE hA hAB hC hCD hSupport
    qx qy hqx hqy xBranch yBranch m n hm hn
  letI : NeZero qx := hqx
  letI : NeZero qy := hqy
  let G : ℝ → ℂ := fun x ↦ dfiVoronoiDualTerm qy yBranch (E x) n
  have hG : DFIVoronoiTestFunction G :=
    dfiVoronoiDualTerm_family_testFunction
      hE hA hAB hC hCD hSupport qy yBranch n
  have hOuterBound := hOuter qx inferInstance xBranch G hG m hm
  have hFamilyBound := hFamily hE hA hAB hC hCD hSupport
    qy inferInstance yBranch n hn
  rw [dfiEquation24DoubleDualMellinAmplitude_eq_iteratedDualTerm
    hE hA hAB hC hCD hSupport qx qy xBranch yBranch m n]
  calc
    ‖dfiVoronoiDualTerm qx xBranch G m‖ ≤
        K₁ * (qx : ℝ) ^ (-(1 / 2 : ℝ)) *
          dfiBesselQuarterBaseNorm G *
          (m : ℝ) ^ (ε / 2 - 1 / 4) := hOuterBound
    _ ≤ K₁ * (qx : ℝ) ^ (-(1 / 2 : ℝ)) *
          (K₂ * (qy : ℝ) ^ (-(1 / 2 : ℝ)) *
            A ^ (-(1 / 4 : ℝ)) * C ^ (-(1 / 4 : ℝ)) *
            (∫ x in Set.Icc A B, ∫ y in Set.Icc C D, ‖E x y‖) *
            (n : ℝ) ^ (ε / 2 - 1 / 4)) *
          (m : ℝ) ^ (ε / 2 - 1 / 4) := by
      gcongr
    _ = (K₁ * K₂) * (qx : ℝ) ^ (-(1 / 2 : ℝ)) *
          (qy : ℝ) ^ (-(1 / 2 : ℝ)) *
          A ^ (-(1 / 4 : ℝ)) * C ^ (-(1 / 4 : ℝ)) *
          (∫ x in Set.Icc A B, ∫ y in Set.Icc C D, ‖E x y‖) *
          (m : ℝ) ^ (ε / 2 - 1 / 4) *
          (n : ℝ) ^ (ε / 2 - 1 / 4) := by ring

theorem probe_exists_doubleDualMellinAmplitude_retained_bound
    (ε : ℝ) (hε : 0 < ε) (hεlt : ε < 1 / 2) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ {E : ℝ → ℝ → ℂ} {A B C D : ℝ},
        ContDiff ℝ ∞ (Function.uncurry E) →
        0 < A → A ≤ B → 0 < C → C ≤ D →
        Function.support (Function.uncurry E) ⊆
          Set.Icc A B ×ˢ Set.Icc C D →
        ∀ (qx qy : ℕ) (_hqx : NeZero qx) (_hqy : NeZero qy)
          (xBranch yBranch : DFIVoronoiDualBranch) (Lx Ly : ℕ),
          (∑ m ∈ Finset.Icc 1 Lx, ∑ n ∈ Finset.Icc 1 Ly,
            ‖dfiEquation24DoubleDualMellinAmplitude
              qx xBranch qy yBranch E m n‖) ≤
            K * (qx : ℝ) ^ (-(1 / 2 : ℝ)) *
              (qy : ℝ) ^ (-(1 / 2 : ℝ)) *
              A ^ (-(1 / 4 : ℝ)) * C ^ (-(1 / 4 : ℝ)) *
              (∫ x in Set.Icc A B, ∫ y in Set.Icc C D, ‖E x y‖) *
              (Lx : ℝ) ^ (3 / 4 + ε / 2) *
              (Ly : ℝ) ^ (3 / 4 + ε / 2) := by
  obtain ⟨K, hK, hPoint⟩ :=
    exists_dfiEquation24DoubleDualMellinAmplitude_physical_bound ε hε
  let c : ℝ := (3 / 4 + ε / 2)⁻¹
  have hc : 0 ≤ c := by dsimp [c]; positivity
  refine ⟨K * c ^ 2, mul_nonneg hK (sq_nonneg c), ?_⟩
  intro E A B C D hE hA hAB hC hCD hSupport
    qx qy hqx hqy xBranch yBranch Lx Ly
  letI : NeZero qx := hqx
  letI : NeZero qy := hqy
  let R : ℝ := K * (qx : ℝ) ^ (-(1 / 2 : ℝ)) *
    (qy : ℝ) ^ (-(1 / 2 : ℝ)) *
    A ^ (-(1 / 4 : ℝ)) * C ^ (-(1 / 4 : ℝ)) *
    (∫ x in Set.Icc A B, ∫ y in Set.Icc C D, ‖E x y‖)
  have hMass : 0 ≤ ∫ x in Set.Icc A B,
      ∫ y in Set.Icc C D, ‖E x y‖ := by
    apply integral_nonneg
    intro x
    exact integral_nonneg fun _ ↦ norm_nonneg _
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hSumX : ∑ m ∈ Finset.Icc 1 Lx,
      (m : ℝ) ^ (ε / 2 - 1 / 4) ≤
      c * (Lx : ℝ) ^ (3 / 4 + ε / 2) := by
    simpa [c] using sum_Icc_natCast_rpow_sub_quarter_le
      (by positivity : 0 ≤ ε / 2) (by linarith : ε / 2 < 1 / 4) Lx
  have hSumY : ∑ n ∈ Finset.Icc 1 Ly,
      (n : ℝ) ^ (ε / 2 - 1 / 4) ≤
      c * (Ly : ℝ) ^ (3 / 4 + ε / 2) := by
    simpa [c] using sum_Icc_natCast_rpow_sub_quarter_le
      (by positivity : 0 ≤ ε / 2) (by linarith : ε / 2 < 1 / 4) Ly
  calc
    (∑ m ∈ Finset.Icc 1 Lx, ∑ n ∈ Finset.Icc 1 Ly,
        ‖dfiEquation24DoubleDualMellinAmplitude
          qx xBranch qy yBranch E m n‖) ≤
      ∑ m ∈ Finset.Icc 1 Lx, ∑ n ∈ Finset.Icc 1 Ly,
        R * (m : ℝ) ^ (ε / 2 - 1 / 4) *
          (n : ℝ) ^ (ε / 2 - 1 / 4) := by
      apply Finset.sum_le_sum
      intro m hmMem
      apply Finset.sum_le_sum
      intro n hnMem
      have hm : 0 < m := by
        have := (Finset.mem_Icc.mp hmMem).1
        omega
      have hn : 0 < n := by
        have := (Finset.mem_Icc.mp hnMem).1
        omega
      simpa only [R, mul_assoc] using
        hPoint hE hA hAB hC hCD hSupport qx qy
          inferInstance inferInstance xBranch yBranch m n hm hn
    _ = R *
        (∑ m ∈ Finset.Icc 1 Lx, (m : ℝ) ^ (ε / 2 - 1 / 4)) *
        (∑ n ∈ Finset.Icc 1 Ly, (n : ℝ) ^ (ε / 2 - 1 / 4)) := by
      have hInner (m : ℕ) :
          (∑ n ∈ Finset.Icc 1 Ly,
            R * (m : ℝ) ^ (ε / 2 - 1 / 4) *
              (n : ℝ) ^ (ε / 2 - 1 / 4)) =
            (R * (m : ℝ) ^ (ε / 2 - 1 / 4)) *
              (∑ n ∈ Finset.Icc 1 Ly,
                (n : ℝ) ^ (ε / 2 - 1 / 4)) := by
        rw [Finset.mul_sum]
      simp_rw [hInner]
      rw [← Finset.sum_mul, ← Finset.mul_sum]
    _ ≤ R * (c * (Lx : ℝ) ^ (3 / 4 + ε / 2)) *
        (c * (Ly : ℝ) ^ (3 / 4 + ε / 2)) := by
      gcongr
    _ = (K * c ^ 2) * (qx : ℝ) ^ (-(1 / 2 : ℝ)) *
        (qy : ℝ) ^ (-(1 / 2 : ℝ)) *
        A ^ (-(1 / 4 : ℝ)) * C ^ (-(1 / 4 : ℝ)) *
        (∫ x in Set.Icc A B, ∫ y in Set.Icc C D, ‖E x y‖) *
        (Lx : ℝ) ^ (3 / 4 + ε / 2) *
        (Ly : ℝ) ^ (3 / 4 + ε / 2) := by
      dsimp [R]
      ring

set_option maxHeartbeats 1000000 in
theorem probe_doubleAmplitude_eq_iteratedDualTerm
    {E : ℝ → ℝ → ℂ} {A B C D : ℝ}
    (hE : ContDiff ℝ ∞ (Function.uncurry E))
    (hA : 0 < A) (hAB : A ≤ B) (hC : 0 < C) (hCD : C ≤ D)
    (hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc A B ×ˢ Set.Icc C D)
    (qx qy : ℕ) [NeZero qx] [NeZero qy]
    (xBranch yBranch : DFIVoronoiDualBranch) (m n : ℕ) :
    dfiEquation24DoubleDualMellinAmplitude
        qx xBranch qy yBranch E m n =
      dfiVoronoiDualTerm qx xBranch
        (fun x ↦ dfiVoronoiDualTerm qy yBranch (E x) n) m := by
  by_cases hm : m = 0
  · subst m
    rw [dfiVoronoiDualTerm_zero]
    simp [dfiEquation24DoubleDualMellinAmplitude,
      dfiEquation24DoubleDualAmplitudeIntegrand,
      divisorWeight]
  by_cases hn : n = 0
  · subst n
    have hzero : (fun x ↦ dfiVoronoiDualTerm qy yBranch (E x) 0) =
        (fun _ ↦ 0) := by funext x; exact dfiVoronoiDualTerm_zero qy yBranch (E x)
    rw [hzero]
    simp [dfiEquation24DoubleDualMellinAmplitude,
      dfiEquation24DoubleDualAmplitudeIntegrand,
      probe_dualTerm_zero_function, divisorWeight]
  have hMellin (z : ℂ) :
      mellin (fun x ↦ dfiVoronoiDualTerm qy yBranch (E x) n) z =
      dfiVoronoiDualTerm qy yBranch
        (fun y ↦ mellin (fun x ↦ E x y) z) n := by
    simpa using mellin_dfiVoronoiDualTerm_family
      hE hA hC hCD hSupport qy yBranch n z
  have hAmpInt : Integrable (dfiEquation24DoubleDualAmplitudeIntegrand
      qx xBranch qy yBranch E m n) := by
    rw [← show (fun p ↦ dfiEquation24DoubleMellinTerm
        qx (fun _ ↦ 1) xBranch qy (fun _ ↦ 1) yBranch E m n p) =
        dfiEquation24DoubleDualAmplitudeIntegrand
          qx xBranch qy yBranch E m n by
      funext p
      exact dfiEquation24DoubleMellinTerm_one_eq_amplitudeIntegrand
        qx xBranch qy yBranch E m n p]
    exact integrable_dfiEquation24DoubleMellinTerm
        hE hA hAB hC hCD hSupport
        qx (fun _ ↦ 1) xBranch qy (fun _ ↦ 1) yBranch m n
  rw [dfiVoronoiDualTerm_eq_divisorWeight_mul_initial]
  rw [← dfiEquation29TransformAt_initial]
  unfold dfiEquation29TransformAt VerticalIntegral'
  simp only [smul_eq_mul]
  unfold dfiEquation29Integrand
  simp_rw [hMellin]
  simp_rw [dfiVoronoiDualTerm_eq_divisorWeight_mul_initial]
  simp_rw [← dfiEquation29TransformAt_initial]
  unfold dfiEquation29TransformAt VerticalIntegral'
  simp only [smul_eq_mul]
  unfold dfiEquation29Integrand VerticalIntegral
  simp only [smul_eq_mul]
  have hBi (z w : ℂ) :
      mellin (fun y ↦ mellin (fun x ↦ E x y) z) w =
        dfiBiMellin E z w := by
    simpa [dfiBiMellin] using
      (mellin_mellin_comm_of_rectangular_support
        hE hA hC hSupport z w).symm
  simp_rw [hBi]
  unfold dfiEquation24DoubleDualMellinAmplitude
  rw [Measure.volume_eq_prod ℝ ℝ,
    MeasureTheory.integral_prod _ hAmpInt]
  unfold dfiEquation24DoubleDualAmplitudeIntegrand
    dfiEquation29Multiplier
    dfiDualBranchMultiplier
  cases xBranch <;> cases yBranch
  all_goals
    simp only [Complex.ofReal_neg, Complex.ofReal_div,
      Complex.ofReal_one]
    norm_num only
    simp_rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with u
    apply MeasureTheory.integral_congr_ae
    filter_upwards with v
    have hu : (-(1 / 2 : ℂ) + (u : ℂ) * I) =
        (-(1 / (((2 : ℝ) : ℂ))) + (u : ℂ) * I) := by norm_num
    have hv : (-(1 / 2 : ℂ) + (v : ℂ) * I) =
        (-(1 / (((2 : ℝ) : ℂ))) + (v : ℂ) * I) := by norm_num
    rw [hu, hv]
    ring

end RiemannZeta.GuthMaynard
