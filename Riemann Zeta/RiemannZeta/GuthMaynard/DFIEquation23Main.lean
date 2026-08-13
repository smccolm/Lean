import RiemannZeta.GuthMaynard.DFIParametricSmooth

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

/-- The main/main entry of equation (23) has the exact test-function
regularity required for the second Voronoi application. -/
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
