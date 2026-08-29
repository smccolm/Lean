import RiemannZeta.GuthMaynard.DFIEquation23

/-!
# The concrete two-variable weight entering DFI equation (23)

This file connects the exact equation-(22) summand to the real-variable test
function used by the two Voronoi applications.  In particular it proves, from
the equation-(2), dyadic-box, redundant-cutoff, and delta-weight data, that
every slice in either variable is a positive smooth compactly supported
Voronoi test function.
-/

open Complex Finset Set Filter Topology MeasureTheory
open scoped BigOperators ContDiff Topology
open Classical

namespace RiemannZeta.GuthMaynard

theorem contDiff_uncurry_dfiLocalizedWeight
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U h : ℝ}
    (hf : DFIEquation2 f P X Y) (hφ : DFIRedundantCutoff φ U) :
    ContDiff ℝ ∞ (Function.uncurry (dfiLocalizedWeight f φ h)) := by
  unfold dfiLocalizedWeight Function.uncurry
  exact hf.smooth.mul (hφ.smooth.comp (by fun_prop))

theorem support_uncurry_dfiLocalizedWeight_subset
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {X Y h : ℝ}
    (hbox : DFILocalizedBox f X Y) :
    Function.support (Function.uncurry (dfiLocalizedWeight f φ h)) ⊆
      Set.Icc X (2 * X) ×ˢ Set.Icc Y (2 * Y) := by
  intro p hp
  have hfne : f p.1 p.2 ≠ 0 := by
    intro hz
    exact hp (by simp [Function.uncurry, dfiLocalizedWeight, hz])
  exact hbox.support_subset hfne

/-- The real-variable form of the source quantity `E(m,n)` below equation
(22), before restriction to integer arguments. -/
noncomputable def dfiEquation23Weight {Q : ℝ} (w : DFIDeltaWeight Q)
    (F : ℝ → ℝ → ℂ) (a b : ℕ) (h : ℤ) (q : ℕ)
    (x y : ℝ) : ℂ :=
  F ((a : ℝ) * x) ((b : ℝ) * y) *
    (dfiDeltaKernel w q ((a : ℝ) * x - (b : ℝ) * y - h) : ℂ)

/-- The real-variable equation-(23) weight restricts exactly to the
equation-(22) arithmetic summand. -/
theorem dfiEquation23Weight_natCast
    {Q : ℝ} (w : DFIDeltaWeight Q) (F : ℝ → ℝ → ℂ)
    (a b : ℕ) (h : ℤ) (q m n : ℕ) :
    dfiEquation23Weight w F a b h q m n =
      dfiEquation22Weight w F a b h q m n := by
  unfold dfiEquation23Weight dfiEquation22Weight quadraticDivisorShift
  push_cast
  rfl

theorem contDiff_uncurry_dfiEquation23Weight
    {Q P X Y U : ℝ} (w : DFIDeltaWeight Q)
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    (hf : DFIEquation2 f P X Y) (hφ : DFIRedundantCutoff φ U)
    (a b : ℕ) (h : ℤ) (q : ℕ) (hq : 0 < q) :
    ContDiff ℝ ∞ (Function.uncurry
      (dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q)) := by
  have hF := contDiff_uncurry_dfiLocalizedWeight (h := (h : ℝ)) hf hφ
  have hscale : ContDiff ℝ ∞ (fun p : ℝ × ℝ =>
      ((a : ℝ) * p.1, (b : ℝ) * p.2)) := by fun_prop
  have hlocalized : ContDiff ℝ ∞ (fun p : ℝ × ℝ =>
      dfiLocalizedWeight f φ h ((a : ℝ) * p.1) ((b : ℝ) * p.2)) :=
    hF.comp hscale
  have hshift : ContDiff ℝ ∞ (fun p : ℝ × ℝ =>
      (a : ℝ) * p.1 - (b : ℝ) * p.2 - (h : ℝ)) := by fun_prop
  have hdelta : ContDiff ℝ ∞ (fun p : ℝ × ℝ =>
      (dfiDeltaKernel w q
        ((a : ℝ) * p.1 - (b : ℝ) * p.2 - (h : ℝ)) : ℂ)) := by
    exact Complex.ofRealCLM.contDiff.comp
      ((contDiff_dfiDeltaKernel w q hq).comp hshift)
  exact hlocalized.mul hdelta

theorem dfiEquation23Weight_support_subset
    {Q X Y : ℝ} (w : DFIDeltaWeight Q)
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    (hbox : DFILocalizedBox f X Y) (a b : ℕ)
    (h : ℤ) (q : ℕ) :
    Function.support (Function.uncurry
      (dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q)) ⊆
      {p : ℝ × ℝ |
        ((a : ℝ) * p.1, (b : ℝ) * p.2) ∈
          Set.Icc X (2 * X) ×ˢ Set.Icc Y (2 * Y)} := by
  intro p hp
  have hlocalne : dfiLocalizedWeight f φ h
      ((a : ℝ) * p.1) ((b : ℝ) * p.2) ≠ 0 := by
    intro hz
    exact hp (by simp [Function.uncurry, dfiEquation23Weight, hz])
  simpa only [Set.mem_setOf_eq] using
    (support_uncurry_dfiLocalizedWeight_subset hbox hlocalne)

/-- Every second-variable slice of the concrete equation-(23) weight is an
admissible positive Voronoi test function. -/
-- Source-equation compatibility keeps this established public name.
@[nolint defsWithUnderscore]
noncomputable def dfiEquation23Weight_ySlice
    {Q P X Y U : ℝ} (w : DFIDeltaWeight Q)
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U)
    (a b : ℕ) (hb : 0 < b) (h : ℤ) (q : ℕ) (hq : 0 < q)
    (x : ℝ) :
    DFIVoronoiTestFunction
      (dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q x) := by
  have hglobal := contDiff_uncurry_dfiEquation23Weight w hf hφ a b h q hq
  refine {
    lower := Y / b
    upper := 2 * Y / b
    lower_pos := div_pos (zero_lt_one.trans_le hf.one_le_Y) (by exact_mod_cast hb)
    lower_le_upper := by
      exact (div_le_div_iff_of_pos_right (by exact_mod_cast hb)).2
        (by nlinarith [hf.one_le_Y])
    smooth := hglobal.comp (by fun_prop :
      ContDiff ℝ ∞ (fun y : ℝ => (x, y)))
    support_subset := ?_ }
  intro y hy
  change dfiEquation23Weight w (dfiLocalizedWeight f φ ↑h) a b h q x y ≠ 0 at hy
  have hp : (x, y) ∈ Function.support (Function.uncurry
      (dfiEquation23Weight w (dfiLocalizedWeight f φ ↑h) a b h q)) := hy
  have hmem := dfiEquation23Weight_support_subset w hbox a b h q hp
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  constructor
  · exact (div_le_iff₀ hbR).2 (by simpa [mul_comm] using hmem.2.1)
  · exact (le_div_iff₀ hbR).2 (by simpa [mul_comm] using hmem.2.2)

/-- The symmetric first-variable slice theorem. -/
-- Source-equation compatibility keeps this established public name.
@[nolint defsWithUnderscore]
noncomputable def dfiEquation23Weight_xSlice
    {Q P X Y U : ℝ} (w : DFIDeltaWeight Q)
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U)
    (a b : ℕ) (ha : 0 < a) (h : ℤ) (q : ℕ) (hq : 0 < q)
    (y : ℝ) :
    DFIVoronoiTestFunction
      (fun x => dfiEquation23Weight w
        (dfiLocalizedWeight f φ h) a b h q x y) := by
  have hglobal := contDiff_uncurry_dfiEquation23Weight w hf hφ a b h q hq
  refine {
    lower := X / a
    upper := 2 * X / a
    lower_pos := div_pos (zero_lt_one.trans_le hf.one_le_X) (by exact_mod_cast ha)
    lower_le_upper := by
      exact (div_le_div_iff_of_pos_right (by exact_mod_cast ha)).2
        (by nlinarith [hf.one_le_X])
    smooth := hglobal.comp (by fun_prop :
      ContDiff ℝ ∞ (fun x : ℝ => (x, y)))
    support_subset := ?_ }
  intro x hx
  change dfiEquation23Weight w (dfiLocalizedWeight f φ ↑h) a b h q x y ≠ 0 at hx
  have hp : (x, y) ∈ Function.support (Function.uncurry
      (dfiEquation23Weight w (dfiLocalizedWeight f φ ↑h) a b h q)) := hx
  have hmem := dfiEquation23Weight_support_subset w hbox a b h q hp
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  constructor
  · exact (div_le_iff₀ haR).2 (by simpa [mul_comm] using hmem.1.1)
  · exact (le_div_iff₀ haR).2 (by simpa [mul_comm] using hmem.1.2)

end RiemannZeta.GuthMaynard
