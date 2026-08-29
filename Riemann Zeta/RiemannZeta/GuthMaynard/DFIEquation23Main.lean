import RiemannZeta.GuthMaynard.DFIParametricMellin

/-!
# The logarithmic-main branch in DFI equation (23)

This file proves that the first Voronoi main term, regarded as a function of
the remaining variable, is again a positive smooth compactly supported test
function.  It is the first of the three concrete admissibility branches.
-/

open Complex Set Filter Topology MeasureTheory
open scoped ContDiff Topology

namespace RiemannZeta.GuthMaynard

/-- A globally continuous version of `log`, equal to `log` on `[A,∞)` when
`A > 0`. -/
noncomputable def dfiSafeLog (A y : ℝ) : ℝ := Real.log (max A y)

theorem continuous_dfiSafeLog {A : ℝ} (hA : 0 < A) :
    Continuous (dfiSafeLog A) := by
  rw [continuous_iff_continuousAt]
  intro y
  apply (Real.continuousAt_log ?_).comp
    (continuousAt_const.max continuousAt_id)
  exact ne_of_gt (hA.trans_le (le_max_left A y))

theorem dfiSafeLog_eq_log {A y : ℝ} (hy : A ≤ y) :
    dfiSafeLog A y = Real.log y := by
  simp [dfiSafeLog, max_eq_right hy]

theorem integral_Ioi_eq_Icc_of_support {A B : ℝ} (hA : 0 < A)
    {g : ℝ → ℂ} (hg : Function.support g ⊆ Set.Icc A B)
    (w : ℝ → ℂ) :
    (∫ y in Set.Ioi 0, w y * g y) = ∫ y in Set.Icc A B, w y * g y := by
  apply setIntegral_eq_of_subset_of_forall_diff_eq_zero measurableSet_Ioi
  · intro y hy
    exact hA.trans_le hy.1
  · intro y hy
    have hgy : g y = 0 := by
      by_contra hne
      exact hy.2 (hg hne)
    simp [hgy]

theorem dfiVoronoiMainTerm_eq_Icc {A B : ℝ} (hA : 0 < A)
    (q : ℕ) {g : ℝ → ℂ} (hg : Function.support g ⊆ Set.Icc A B) :
    dfiVoronoiMainTerm q g =
      (q : ℂ)⁻¹ * ∫ y in Set.Icc A B,
        ((dfiSafeLog A y : ℂ) + 2 * Real.eulerMascheroniConstant -
          2 * Complex.log (q : ℂ)) * g y := by
  unfold dfiVoronoiMainTerm
  congr 1
  rw [integral_Ioi_eq_Icc_of_support hA hg]
  apply setIntegral_congr_fun measurableSet_Icc
  intro y hy
  change (((Real.log y : ℂ) + 2 * Real.eulerMascheroniConstant -
      2 * Complex.log (q : ℂ)) * g y) =
    (((dfiSafeLog A y : ℂ) + 2 * Real.eulerMascheroniConstant -
      2 * Complex.log (q : ℂ)) * g y)
  rw [dfiSafeLog_eq_log hy.1]

theorem dfiVoronoiMainTerm_eq_zero {q : ℕ} :
    dfiVoronoiMainTerm q (fun _ : ℝ => 0) = 0 := by
  simp [dfiVoronoiMainTerm]

/-- The two non-main branches of the divisor Voronoi formula. -/
inductive DFIVoronoiDualBranch where
  | minusTerm
  | plusTerm
  deriving DecidableEq, Fintype

/-- Inclusion of a dual branch into the three-branch Voronoi expansion. -/
def DFIVoronoiDualBranch.toBranch : DFIVoronoiDualBranch → DFIVoronoiBranch
  | .minusTerm => .minusTerm
  | .plusTerm => .plusTerm

/-- Absolute convergence on `Re s = 3/2` gives a bound for the periodic
Estermann series uniform in the ordinate. -/
theorem exists_periodicEstermann_three_half_sub_mul_I_bound
    (q : ℕ) [NeZero q] (Φ : ZMod q → ℂ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ u : ℝ,
      ‖periodicEstermann q Φ ((3 / 2 : ℂ) - (u : ℂ) * I)‖ ≤ B := by
  let B : ℝ := ∑' n : ℕ,
    ‖LSeries.term (periodicDivisorCoeff q Φ) (3 / 2 : ℂ) n‖
  have hCoeff : LSeriesSummable (periodicDivisorCoeff q Φ) (3 / 2 : ℂ) :=
    periodicDivisorCoeff_LSeriesSummable q Φ (by norm_num)
  have hB : 0 ≤ B := tsum_nonneg fun _ => norm_nonneg _
  refine ⟨B, hB, ?_⟩
  intro u
  have hs : 1 < (((3 / 2 : ℂ) - (u : ℂ) * I).re) := by norm_num
  rw [periodicEstermann_eq_LSeries q Φ hs]
  have hCoeffU : LSeriesSummable (periodicDivisorCoeff q Φ)
      ((3 / 2 : ℂ) - (u : ℂ) * I) :=
    hCoeff.of_re_le_re (by simp)
  unfold LSeries B
  calc
    ‖∑' n : ℕ, LSeries.term (periodicDivisorCoeff q Φ)
        ((3 / 2 : ℂ) - (u : ℂ) * I) n‖ ≤
      ∑' n : ℕ, ‖LSeries.term (periodicDivisorCoeff q Φ)
        ((3 / 2 : ℂ) - (u : ℂ) * I) n‖ :=
      norm_tsum_le_tsum_norm hCoeffU.norm
    _ = ∑' n : ℕ,
        ‖LSeries.term (periodicDivisorCoeff q Φ) (3 / 2 : ℂ) n‖ := by
      apply tsum_congr
      intro n
      rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
      norm_num

/-- The ordinate-dependent factor in one individual transformed branch of
DFI (23), excluding only the Mellin transform of the source slice. -/
noncomputable def dfiDualBranchVerticalWeight
    (q : ℕ) [NeZero q] (d : ZMod q)
    (branch : DFIVoronoiDualBranch) (u : ℝ) : ℂ :=
  match branch with
  | .minusTerm =>
      periodicEstermann q (dfiVoronoiCharacter q (-d⁻¹))
          ((3 / 2 : ℂ) - (u : ℂ) * I) *
        dfiVoronoiMinusMultiplier q
          (-(1 / 2 : ℂ) + (u : ℂ) * I)
  | .plusTerm =>
      periodicEstermann q (dfiVoronoiCharacter q d⁻¹)
          ((3 / 2 : ℂ) - (u : ℂ) * I) *
        dfiVoronoiPlusMultiplier q
          (-(1 / 2 : ℂ) + (u : ℂ) * I)

theorem continuous_dfiDualBranchVerticalWeight
    (q : ℕ) [NeZero q] (d : ZMod q)
    (branch : DFIVoronoiDualBranch) :
    Continuous (dfiDualBranchVerticalWeight q d branch) := by
  cases branch with
  | minusTerm =>
      apply Continuous.mul
      · rw [continuous_iff_continuousAt]
        intro u
        have hne : ((3 / 2 : ℂ) - (u : ℂ) * I) ≠ 1 := by
          intro hz
          have hre := congrArg Complex.re hz
          norm_num at hre
        exact (differentiableAt_periodicEstermann q
          (dfiVoronoiCharacter q (-d⁻¹)) hne).continuousAt.comp_of_eq
            (by fun_prop) rfl
      · exact continuous_dfiVoronoiMinusMultiplier_leftLine q
  | plusTerm =>
      apply Continuous.mul
      · rw [continuous_iff_continuousAt]
        intro u
        have hne : ((3 / 2 : ℂ) - (u : ℂ) * I) ≠ 1 := by
          intro hz
          have hre := congrArg Complex.re hz
          norm_num at hre
        exact (differentiableAt_periodicEstermann q
          (dfiVoronoiCharacter q d⁻¹) hne).continuousAt.comp_of_eq
            (by fun_prop) rfl
      · exact continuous_dfiVoronoiPlusMultiplier_leftLine q

theorem exists_dfiDualBranchVerticalWeight_quadratic_bound
    (q : ℕ) [NeZero q] (d : ZMod q)
    (branch : DFIVoronoiDualBranch) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ,
      ‖dfiDualBranchVerticalWeight q d branch u‖ ≤
        C * (1 + |u|) ^ 2 := by
  let C₀ : ℝ := 32 * q * dfiArchimedeanScale q ^ 2
  have hC₀ : 0 ≤ C₀ := by positivity
  cases branch with
  | minusTerm =>
      obtain ⟨B, hB, hBound⟩ :=
        exists_periodicEstermann_three_half_sub_mul_I_bound q
          (dfiVoronoiCharacter q (-d⁻¹))
      refine ⟨B * C₀, mul_nonneg hB hC₀, ?_⟩
      intro u
      rw [dfiDualBranchVerticalWeight, norm_mul]
      calc
        ‖periodicEstermann q (dfiVoronoiCharacter q (-d⁻¹))
            ((3 / 2 : ℂ) - (u : ℂ) * I)‖ *
            ‖dfiVoronoiMinusMultiplier q
              (-(1 / 2 : ℂ) + (u : ℂ) * I)‖ ≤
          B * (C₀ * (1 + |u|) ^ 2) :=
            mul_le_mul (hBound u) (norm_dfiVoronoiMinusMultiplier_le q u)
              (norm_nonneg _) hB
        _ = (B * C₀) * (1 + |u|) ^ 2 := by ring
  | plusTerm =>
      obtain ⟨B, hB, hBound⟩ :=
        exists_periodicEstermann_three_half_sub_mul_I_bound q
          (dfiVoronoiCharacter q d⁻¹)
      refine ⟨B * C₀, mul_nonneg hB hC₀, ?_⟩
      intro u
      rw [dfiDualBranchVerticalWeight, norm_mul]
      calc
        ‖periodicEstermann q (dfiVoronoiCharacter q d⁻¹)
            ((3 / 2 : ℂ) - (u : ℂ) * I)‖ *
            ‖dfiVoronoiPlusMultiplier q
              (-(1 / 2 : ℂ) + (u : ℂ) * I)‖ ≤
          B * (C₀ * (1 + |u|) ^ 2) :=
            mul_le_mul (hBound u) (norm_dfiVoronoiPlusMultiplier_le q u)
              (norm_nonneg _) hB
        _ = (B * C₀) * (1 + |u|) ^ 2 := by ring

/-- One individual transformed branch is exactly its reflected
Estermann vertical integral, rather than merely a summand of the grouped
remainder. -/
theorem DFIVoronoiTestFunction.dualBranch_eq_verticalIntegral
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    (q : ℕ) [NeZero q] (d : ZMod q)
    (branch : DFIVoronoiDualBranch) :
    dfiVoronoiBranchValue q d branch.toBranch g =
      VerticalIntegral' (fun z : ℂ ↦ match branch with
        | .minusTerm => dfiMinusBranchIntegrand q d g z
        | .plusTerm => dfiPlusBranchIntegrand q d g z)
        (-(1 / 2 : ℝ)) := by
  cases branch with
  | minusTerm =>
      symm
      simpa [DFIVoronoiDualBranch.toBranch, dfiVoronoiBranchValue,
        periodicDivisorCoeff_voronoiCharacter, mul_assoc] using
          hg.minusIntegral_voronoiCharacter q d
  | plusTerm =>
      symm
      simpa [DFIVoronoiDualBranch.toBranch, dfiVoronoiBranchValue,
        periodicDivisorCoeff_voronoiCharacter, mul_assoc] using
          hg.plusIntegral_voronoiCharacter q d

/-- Source-line form of one dual Voronoi branch: the normalized vertical
integral is expanded into the residue-independent vertical weight and the
Mellin transform of the test function. -/
theorem DFIVoronoiTestFunction.dualBranch_eq_weightedMellinIntegral
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    (q : ℕ) [NeZero q] (d : ZMod q)
    (branch : DFIVoronoiDualBranch) :
    dfiVoronoiBranchValue q d branch.toBranch g =
      (1 / (2 * Real.pi * I) : ℂ) *
        (I * ∫ u : ℝ, dfiDualBranchVerticalWeight q d branch u *
          mellin g (-(1 / 2 : ℂ) + (u : ℂ) * I)) := by
  rw [hg.dualBranch_eq_verticalIntegral q d branch]
  unfold VerticalIntegral' VerticalIntegral
  simp only [smul_eq_mul]
  congr 2
  apply MeasureTheory.integral_congr_ae
  filter_upwards with u
  have hPhase : 1 - (-(1 / 2 : ℂ) + (u : ℂ) * I) =
      (3 / 2 : ℂ) - (u : ℂ) * I := by ring
  have hHalf : -(1 / (((2 : ℝ) : ℂ))) = -(1 / 2 : ℂ) := by norm_num
  cases branch with
  | minusTerm =>
      simp only [dfiMinusBranchIntegrand,
        dfiDualBranchVerticalWeight]
      norm_num only [Complex.ofReal_neg, Complex.ofReal_div,
        Complex.ofReal_one]
      rw [hHalf, hPhase]
  | plusTerm =>
      simp only [dfiPlusBranchIntegrand,
        dfiDualBranchVerticalWeight]
      norm_num only [Complex.ofReal_neg, Complex.ofReal_div,
        Complex.ofReal_one]
      rw [hHalf, hPhase]

/-- Parameter-smoothness and compact support of either individual dual
Voronoi branch.  This is the analytic source-entry obligation that was
missing from the earlier grouped equation-(23) proof. -/
-- Source-equation compatibility keeps this established public name.
@[nolint defsWithUnderscore]
noncomputable def dfiEquation23_dualBranchTestFunction
    {E : ℝ → ℝ → ℂ} {A B C D : ℝ}
    (hE : ContDiff ℝ ∞ (Function.uncurry E))
    (hA : 0 < A) (hAB : A ≤ B) (hC : 0 < C) (hCD : C ≤ D)
    (hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc A B ×ˢ Set.Icc C D)
    (q : ℕ) [NeZero q] (d : ZMod q)
    (branch : DFIVoronoiDualBranch) :
    DFIVoronoiTestFunction
      (fun x ↦ dfiVoronoiBranchValue q d branch.toBranch (E x)) := by
  have hyTest (x : ℝ) : DFIVoronoiTestFunction (E x) := {
    lower := C
    upper := D
    lower_pos := hC
    lower_le_upper := hCD
    smooth := hE.comp (contDiff_prodMk_right x)
    support_subset := by
      intro y hy
      exact (hSupport (show (x, y) ∈ Function.support (Function.uncurry E) by
        simpa only [Function.mem_support, Function.uncurry_apply_pair] using hy)).2 }
  let hExists := exists_dfiDualBranchVerticalWeight_quadratic_bound q d branch
  let Cw : ℝ := Classical.choose hExists
  have hCw : 0 ≤ Cw := (Classical.choose_spec hExists).1
  have hWeight : ∀ u : ℝ,
      ‖dfiDualBranchVerticalWeight q d branch u‖ ≤
        Cw * (1 + |u|) ^ 2 := (Classical.choose_spec hExists).2
  have hVerticalSmooth : ContDiff ℝ ∞
      (dfiParametricVerticalIntegralDeriv 0
        (dfiDualBranchVerticalWeight q d branch) (-(1 / 2 : ℝ)) E) :=
    contDiff_dfiParametricVerticalIntegral hE hC hCD hSupport
      (continuous_dfiDualBranchVerticalWeight q d branch) hCw hWeight _
  have hEq :
      (fun x ↦ dfiVoronoiBranchValue q d branch.toBranch (E x)) =
      fun x ↦ (1 / (2 * Real.pi * I) : ℂ) *
        (I * dfiParametricVerticalIntegralDeriv 0
          (dfiDualBranchVerticalWeight q d branch)
          (-(1 / 2 : ℝ)) E x) := by
    funext x
    rw [(hyTest x).dualBranch_eq_verticalIntegral q d branch]
    unfold VerticalIntegral' VerticalIntegral
    simp only [smul_eq_mul]
    congr 2
    apply MeasureTheory.integral_congr_ae
    filter_upwards with u
    have hPhase : 1 - (-(1 / 2 : ℂ) + (u : ℂ) * I) =
        (3 / 2 : ℂ) - (u : ℂ) * I := by ring
    have hHalf : -(1 / (((2 : ℝ) : ℂ))) = -(1 / 2 : ℂ) := by norm_num
    cases branch with
    | minusTerm =>
        simp only [dfiMinusBranchIntegrand,
          dfiDualBranchVerticalWeight, iteratedDeriv_zero]
        norm_num only [Complex.ofReal_neg, Complex.ofReal_div,
          Complex.ofReal_one]
        rw [hHalf]
        rw [hPhase]
    | plusTerm =>
        simp only [dfiPlusBranchIntegrand,
          dfiDualBranchVerticalWeight, iteratedDeriv_zero]
        norm_num only [Complex.ofReal_neg, Complex.ofReal_div,
          Complex.ofReal_one]
        rw [hHalf]
        rw [hPhase]
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
    change dfiVoronoiBranchValue q d branch.toBranch (E x) ≠ 0 at hx
    rw [hxE, dfiVoronoiBranchValue_zero] at hx
    exact hx rfl

/-- The main/main entry of equation (23) has the exact test-function
regularity required for the second Voronoi application. -/
-- Source-equation compatibility keeps this established public name.
@[nolint defsWithUnderscore]
noncomputable def dfiEquation23Weight_mainBranch
    {Q P X Y U : ℝ} (w : DFIDeltaWeight Q)
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U)
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (h : ℤ)
    (q₀ : ℕ) (hq₀ : 0 < q₀) (qᵥ : ℕ) [NeZero qᵥ] (dy : ZMod qᵥ) :
    DFIVoronoiTestFunction (fun x =>
      dfiVoronoiBranchValue qᵥ dy DFIVoronoiBranch.mainTerm
        (dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q₀ x)) := by
  let E := dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q₀
  let A : ℝ := Y / b
  let B : ℝ := 2 * Y / b
  let C : ℝ := X / a
  let D : ℝ := 2 * X / a
  have hA : 0 < A := div_pos (zero_lt_one.trans_le hf.one_le_Y) (by exact_mod_cast hb)
  have hC : 0 < C := div_pos (zero_lt_one.trans_le hf.one_le_X) (by exact_mod_cast ha)
  have hAB : A ≤ B := (div_le_div_iff_of_pos_right (by exact_mod_cast hb)).2
    (by nlinarith [hf.one_le_Y])
  have hCD : C ≤ D := (div_le_div_iff_of_pos_right (by exact_mod_cast ha)).2
    (by nlinarith [hf.one_le_X])
  have hE : ContDiff ℝ ∞ (Function.uncurry E) :=
    contDiff_uncurry_dfiEquation23Weight w hf hφ a b h q₀ hq₀
  have hySupport (x : ℝ) : Function.support (E x) ⊆ Set.Icc A B :=
    (dfiEquation23Weight_ySlice w hf hbox hφ a b hb h q₀ hq₀ x).support_subset
  let W : ℝ → ℂ := fun y =>
    (dfiSafeLog A y : ℂ) + 2 * Real.eulerMascheroniConstant -
      2 * Complex.log (qᵥ : ℂ)
  have hW : Continuous W := by
    unfold W
    exact (Complex.ofRealCLM.continuous.comp (continuous_dfiSafeLog hA)).add
      continuous_const |>.sub continuous_const
  have hsmoothIntegral : ContDiff ℝ ∞
      (fun x => ∫ y in Set.Icc A B, W y * E x y) :=
    contDiff_integral_Icc_right_mul_left hW hE
  refine {
    lower := C
    upper := D
    lower_pos := hC
    lower_le_upper := hCD
    smooth := ?_
    support_subset := ?_ }
  · have heq : (fun x => dfiVoronoiBranchValue qᵥ dy
        DFIVoronoiBranch.mainTerm (E x)) =
      fun x => (qᵥ : ℂ)⁻¹ * ∫ y in Set.Icc A B, W y * E x y := by
      funext x
      change dfiVoronoiMainTerm qᵥ (E x) = _
      simpa [W] using dfiVoronoiMainTerm_eq_Icc hA qᵥ (hySupport x)
    rw [heq]
    fun_prop
  · intro x hx
    by_contra hxnot
    have hxE : ∀ y : ℝ, E x y = 0 := by
      intro y
      by_contra hne
      have hp := dfiEquation23Weight_support_subset w hbox a b h q₀
        (show (x, y) ∈ Function.support (Function.uncurry E) from hne)
      have haR : (0 : ℝ) < a := by exact_mod_cast ha
      have hxmem : x ∈ Set.Icc C D := by
        constructor
        · exact (div_le_iff₀ haR).2 (by simpa [mul_comm] using hp.1.1)
        · exact (le_div_iff₀ haR).2 (by simpa [mul_comm] using hp.1.2)
      exact hxnot hxmem
    change dfiVoronoiMainTerm qᵥ (E x) ≠ 0 at hx
    have hzero : E x = fun _ => 0 := funext hxE
    rw [hzero, dfiVoronoiMainTerm_eq_zero] at hx
    exact hx rfl

theorem dfiEquation23Weight_support_rectangle
    {Q X Y : ℝ} (w : DFIDeltaWeight Q)
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    (hbox : DFILocalizedBox f X Y)
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (h : ℤ) (q : ℕ) :
    Function.support (Function.uncurry
      (dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q)) ⊆
      Set.Icc (X / a) (2 * X / a) ×ˢ
        Set.Icc (Y / b) (2 * Y / b) := by
  intro p hp
  have hscaled := dfiEquation23Weight_support_subset w hbox a b h q hp
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  constructor
  · constructor
    · exact (div_le_iff₀ haR).2 (by simpa [mul_comm] using hscaled.1.1)
    · exact (le_div_iff₀ haR).2 (by simpa [mul_comm] using hscaled.1.2)
  · constructor
    · exact (div_le_iff₀ hbR).2 (by simpa [mul_comm] using hscaled.2.1)
    · exact (le_div_iff₀ hbR).2 (by simpa [mul_comm] using hscaled.2.2)

/-- Either individual transformed `y`-branch of the concrete source weight
is a genuine test function in `x`. -/
-- Source-equation compatibility keeps this established public name.
@[nolint defsWithUnderscore]
noncomputable def dfiEquation23Weight_dualBranch
    {Q P X Y U : ℝ} (w : DFIDeltaWeight Q)
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U)
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (h : ℤ)
    (q₀ : ℕ) (hq₀ : 0 < q₀)
    (qᵧ : ℕ) [NeZero qᵧ] (dy : ZMod qᵧ)
    (branch : DFIVoronoiDualBranch) :
    DFIVoronoiTestFunction (fun x ↦
      dfiVoronoiBranchValue qᵧ dy branch.toBranch
        (dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q₀ x)) := by
  let E := dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q₀
  have hE : ContDiff ℝ ∞ (Function.uncurry E) :=
    contDiff_uncurry_dfiEquation23Weight w hf hφ a b h q₀ hq₀
  have hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc (X / a) (2 * X / a) ×ˢ
        Set.Icc (Y / b) (2 * Y / b) :=
    dfiEquation23Weight_support_rectangle w hbox a b ha hb h q₀
  have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  exact dfiEquation23_dualBranchTestFunction
    (A := X / a) (B := 2 * X / a)
    (C := Y / b) (D := 2 * Y / b)
    hE
    (div_pos (zero_lt_one.trans_le hf.one_le_X) haR)
    ((div_le_div_iff_of_pos_right haR).2 (by nlinarith [hf.one_le_X]))
    (div_pos (zero_lt_one.trans_le hf.one_le_Y) hbR)
    ((div_le_div_iff_of_pos_right hbR).2 (by nlinarith [hf.one_le_Y]))
    hSupport qᵧ dy branch

/-- The concrete equation-(23) source satisfies the full ungrouped
three-by-three admissibility condition. -/
-- Source-equation compatibility keeps this established public name.
@[nolint defsWithUnderscore]
noncomputable def dfiEquation23Weight_admissible
    {Q P X Y U : ℝ} (w : DFIDeltaWeight Q)
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U)
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (h : ℤ)
    (q : ℕ) [NeZero q] (hq : 0 < q) (dy : ZMod q) :
    DFIEquation23Admissible q dy
      (dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q) where
  ySlice := dfiEquation23Weight_ySlice w hf hbox hφ a b hb h q hq
  xAfterYBranch := by
    intro branch
    cases branch with
    | mainTerm =>
        exact dfiEquation23Weight_mainBranch
          w hf hbox hφ a b ha hb h q hq q dy
    | minusTerm =>
        exact dfiEquation23Weight_dualBranch
          w hf hbox hφ a b ha hb h q hq q dy .minusTerm
    | plusTerm =>
        exact dfiEquation23Weight_dualBranch
          w hf hbox hφ a b ha hb h q hq q dy .plusTerm

theorem dfiEquation23Weight_ungrouped
    {Q P X Y U : ℝ} (w : DFIDeltaWeight Q)
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U)
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (h : ℤ)
    (q : ℕ) [NeZero q] (hq : 0 < q)
    (dx dy : ZMod q) (hdx : IsUnit dx) (hdy : IsUnit dy) :
    dfiEquation23Left q dx dy
      (dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q) =
    dfiEquation23Right q dx dy
      (dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q) := by
  exact dfiEquation23_of_admissible q dx dy hdx hdy _
    (dfiEquation23Weight_admissible
      w hf hbox hφ a b ha hb h q hq dy)

theorem periodicDivisorWeightedSum_eq_range_of_support
    {q : ℕ} (Phi : ZMod q → ℂ) {B : ℝ} {g : ℝ → ℂ}
    (hg : Function.support g ⊆ Set.Iic B) :
    periodicDivisorWeightedSum q Phi g =
      ∑ n ∈ Finset.range (⌈B⌉₊ + 1), periodicDivisorCoeff q Phi n * g n := by
  unfold periodicDivisorWeightedSum
  rw [tsum_eq_sum (s := Finset.range (⌈B⌉₊ + 1))]
  intro n hn
  have hnlarge : ⌈B⌉₊ + 1 ≤ n := by simpa using hn
  have hBceil : B ≤ (⌈B⌉₊ : ℝ) := Nat.le_ceil B
  have hzero : g n = 0 := by
    by_contra hne
    have hnB : (n : ℝ) ≤ B := hg hne
    exact (not_lt_of_ge hnB) (lt_of_le_of_lt hBceil (by exact_mod_cast hnlarge))
  simp [hzero]

/-- The grouped transformed remainder is a test function because native
Proposition 1 identifies it with the original finite divisor sum minus the
already-controlled logarithmic main term. -/
-- Source-equation compatibility keeps this established public name.
@[nolint defsWithUnderscore]
noncomputable def dfiEquation23Weight_remainderBranch
    {Q P X Y U : ℝ} (w : DFIDeltaWeight Q)
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U)
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (h : ℤ)
    (q₀ : ℕ) (hq₀ : 0 < q₀) (qᵥ : ℕ) [NeZero qᵥ]
    (dy : ZMod qᵥ) (hdy : IsUnit dy) :
    DFIVoronoiTestFunction (fun x =>
      dfiVoronoiRemainderValue qᵥ dy
        (dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q₀ x)) := by
  let E := dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q₀
  let A : ℝ := Y / b
  let B : ℝ := 2 * Y / b
  let C : ℝ := X / a
  let D : ℝ := 2 * X / a
  let N : ℕ := ⌈B⌉₊ + 1
  have hC : 0 < C := div_pos (zero_lt_one.trans_le hf.one_le_X) (by exact_mod_cast ha)
  have hCD : C ≤ D := (div_le_div_iff_of_pos_right (by exact_mod_cast ha)).2
    (by nlinarith [hf.one_le_X])
  have hE : ContDiff ℝ ∞ (Function.uncurry E) :=
    contDiff_uncurry_dfiEquation23Weight w hf hφ a b h q₀ hq₀
  have hyTest (x : ℝ) : DFIVoronoiTestFunction (E x) :=
    dfiEquation23Weight_ySlice w hf hbox hφ a b hb h q₀ hq₀ x
  let S : ℝ → ℂ := fun x => periodicDivisorWeightedSum qᵥ
    (dfiVoronoiCharacter qᵥ dy) (E x)
  have hSfinite : S = fun x => ∑ n ∈ Finset.range N,
      periodicDivisorCoeff qᵥ (dfiVoronoiCharacter qᵥ dy) n * E x n := by
    funext x
    apply periodicDivisorWeightedSum_eq_range_of_support
    intro y hy
    have hp := dfiEquation23Weight_support_subset w hbox a b h q₀
      (show (x, y) ∈ Function.support (Function.uncurry E) from hy)
    have hbR : (0 : ℝ) < b := by exact_mod_cast hb
    exact (le_div_iff₀ hbR).2 (by simpa [B, mul_comm] using hp.2.2)
  have hSsmooth : ContDiff ℝ ∞ S := by
    rw [hSfinite]
    refine ContDiff.sum ?_
    intro n hn
    exact contDiff_const.mul
      (hE.comp (by fun_prop : ContDiff ℝ ∞ (fun x : ℝ => (x, (n : ℝ)))))
  have hMain := dfiEquation23Weight_mainBranch
    w hf hbox hφ a b ha hb h q₀ hq₀ qᵥ dy
  have hremEq : (fun x => dfiVoronoiRemainderValue qᵥ dy (E x)) =
      fun x => S x - dfiVoronoiBranchValue qᵥ dy .mainTerm (E x) := by
    funext x
    have hv := (hyTest x).dfiProposition1_native_branch_sum qᵥ dy hdy
    rw [sum_dfiVoronoiBranchValue_eq_main_add_remainder] at hv
    dsimp [S]
    rw [hv]
    ring
  refine {
    lower := C
    upper := D
    lower_pos := hC
    lower_le_upper := hCD
    smooth := ?_
    support_subset := ?_ }
  · rw [hremEq]
    exact hSsmooth.sub hMain.smooth
  · intro x hx
    by_contra hxnot
    have hxE : ∀ y : ℝ, E x y = 0 := by
      intro y
      by_contra hne
      have hp := dfiEquation23Weight_support_subset w hbox a b h q₀
        (show (x, y) ∈ Function.support (Function.uncurry E) from hne)
      have haR : (0 : ℝ) < a := by exact_mod_cast ha
      have hxmem : x ∈ Set.Icc C D := by
        constructor
        · exact (div_le_iff₀ haR).2 (by simpa [mul_comm] using hp.1.1)
        · exact (le_div_iff₀ haR).2 (by simpa [mul_comm] using hp.1.2)
      exact hxnot hxmem
    have hzero : E x = fun _ => 0 := funext hxE
    change dfiVoronoiRemainderValue qᵥ dy (E x) ≠ 0 at hx
    simp [hzero, dfiVoronoiRemainderValue] at hx

/-- The concrete localized equation-(21) weight satisfies every analytic
condition needed by the grouped two-variable Voronoi expansion. -/
-- Source-equation compatibility keeps this established public name.
@[nolint defsWithUnderscore]
noncomputable def dfiEquation23Weight_groupedAdmissible
    {Q P X Y U : ℝ} (w : DFIDeltaWeight Q)
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U)
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (h : ℤ)
    (q : ℕ) [NeZero q] (hq : 0 < q) (dy : ZMod q) (hdy : IsUnit dy) :
    DFIEquation23GroupedAdmissible q dy
      (dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q) where
  ySlice := dfiEquation23Weight_ySlice w hf hbox hφ a b hb h q hq
  xMain := dfiEquation23Weight_mainBranch w hf hbox hφ a b ha hb h q hq q dy
  xRemainder := dfiEquation23Weight_remainderBranch
    w hf hbox hφ a b ha hb h q hq q dy hdy

theorem dfiEquation23Weight_grouped
    {Q P X Y U : ℝ} (w : DFIDeltaWeight Q)
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U)
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (h : ℤ)
    (q : ℕ) [NeZero q] (hq : 0 < q)
    (dx dy : ZMod q) (hdx : IsUnit dx) (hdy : IsUnit dy) :
    dfiEquation23Left q dx dy
      (dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q) =
    dfiEquation23GroupedRight q dx dy
      (dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q) := by
  exact dfiEquation23_grouped_of_admissible q dx dy hdx hdy _
    (dfiEquation23Weight_groupedAdmissible
      w hf hbox hφ a b ha hb h q hq dy hdy)

end RiemannZeta.GuthMaynard
