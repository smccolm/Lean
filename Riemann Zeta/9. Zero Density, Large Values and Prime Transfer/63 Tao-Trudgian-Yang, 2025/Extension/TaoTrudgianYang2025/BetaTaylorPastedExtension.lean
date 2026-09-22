import TaoTrudgianYang2025.BetaLegendreTaylorTransition

/-!
# A globally smooth, exact moving-endpoint Taylor extension

The original function is used only under the actual buffered cutoff.
Outside the moving interval the constructed function uses its finite
Taylor polynomials. No exterior smoothness of the original is assumed.
-/

noncomputable section

open Set Filter
open scoped ContDiff Topology

namespace TaoTrudgianYang2025

def taylorLeftTransition (l h x : ℝ) : ℝ :=
  Real.smoothTransition ((x-l)/h-1)

def taylorRightTransition (r h x : ℝ) : ℝ :=
  Real.smoothTransition ((r-x)/h-1)

def taylorPastedExtension (f : ℝ → ℝ) (Q : ℕ) (l r h x : ℝ) : ℝ :=
  modelPhaseBufferedCutoff l r h x*f x+
    (1-taylorLeftTransition l h x)*finiteTaylorPolynomial f Q (l+2*h) x+
    (1-taylorRightTransition r h x)*finiteTaylorPolynomial f Q (r-2*h) x

theorem taylorLeftTransition_one {l h x : ℝ} (hh : 0 < h) (hx : l+2*h ≤ x) :
    taylorLeftTransition l h x = 1 := by
  apply Real.smoothTransition.one_of_one_le
  have hp : 2 ≤ (x-l)/h := (le_div_iff₀ hh).mpr (by linarith)
  linarith

theorem taylorRightTransition_one {r h x : ℝ} (hh : 0 < h) (hx : x ≤ r-2*h) :
    taylorRightTransition r h x = 1 := by
  apply Real.smoothTransition.one_of_one_le
  have hp : 2 ≤ (r-x)/h := (le_div_iff₀ hh).mpr (by linarith)
  linarith

theorem taylorLeftTransition_zero {l h x : ℝ} (hh : 0 < h) (hx : x ≤ l+h) :
    taylorLeftTransition l h x = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  have hp : (x-l)/h ≤ 1 := (div_le_one hh).mpr (by linarith)
  linarith

theorem taylorRightTransition_zero {r h x : ℝ} (hh : 0 < h) (hx : r-h ≤ x) :
    taylorRightTransition r h x = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  have hp : (r-x)/h ≤ 1 := (div_le_one hh).mpr (by linarith)
  linarith

theorem taylorPastedExtension_contDiff
    {f : ℝ → ℝ} {l r h : ℝ} (hh : 0 < h)
    (hf : ∀ x ∈ Ioo l r, ContDiffAt ℝ ∞ f x) (Q : ℕ) :
    ContDiff ℝ ∞ (taylorPastedExtension f Q l r h) := by
  have hprod : ContDiff ℝ ∞ (fun x => modelPhaseBufferedCutoff l r h x*f x) := by
    apply smoothCutoff_mul_contDiff (modelPhaseBufferedCutoff_contDiff l r h)
    intro x hx
    have hs := modelPhaseBufferedCutoff_tsupport hh hx
    exact hf x ⟨by linarith [hs.1],by linarith [hs.2]⟩
  have hL : ContDiff ℝ ∞ (taylorLeftTransition l h) :=
    Real.smoothTransition.contDiff.comp (by fun_prop)
  have hR : ContDiff ℝ ∞ (taylorRightTransition r h) :=
    Real.smoothTransition.contDiff.comp (by fun_prop)
  exact (hprod.add ((contDiff_const.sub hL).mul (finiteTaylorPolynomial_contDiff f Q (l+2*h)))).add
    ((contDiff_const.sub hR).mul (finiteTaylorPolynomial_contDiff f Q (r-2*h)))

theorem taylorPastedExtension_agrees
    (f : ℝ → ℝ) (Q : ℕ) {l r h x : ℝ} (hh : 0 < h)
    (hx : x ∈ Icc (l+2*h) (r-2*h)) :
    taylorPastedExtension f Q l r h x = f x := by
  rw [taylorPastedExtension,modelPhaseBufferedCutoff_one hh hx.1 hx.2,
    taylorLeftTransition_one hh hx.1,taylorRightTransition_one hh hx.2]
  ring

theorem taylorPastedExtension_left_formula
    (f : ℝ → ℝ) (Q : ℕ) {l r h x : ℝ} (hh : 0 < h)
    (hx : x ≤ r-2*h) :
    taylorPastedExtension f Q l r h x =
      finiteTaylorPolynomial f Q (l+2*h) x+
        taylorLeftTransition l h x*(f x-finiteTaylorPolynomial f Q (l+2*h) x) := by
  have hprod : modelPhaseBufferedCutoff l r h x =
      taylorLeftTransition l h x*taylorRightTransition r h x := rfl
  rw [taylorPastedExtension,hprod,taylorRightTransition_one hh hx]
  ring

theorem taylorPastedExtension_right_formula
    (f : ℝ → ℝ) (Q : ℕ) {l r h x : ℝ} (hh : 0 < h)
    (hx : l+2*h ≤ x) :
    taylorPastedExtension f Q l r h x =
      finiteTaylorPolynomial f Q (r-2*h) x+
        taylorRightTransition r h x*(f x-finiteTaylorPolynomial f Q (r-2*h) x) := by
  have hprod : modelPhaseBufferedCutoff l r h x =
      taylorLeftTransition l h x*taylorRightTransition r h x := rfl
  rw [taylorPastedExtension,hprod,taylorLeftTransition_one hh hx]
  ring

theorem taylorPastedExtension_eventuallyEq_left_formula
    (f : ℝ → ℝ) (Q : ℕ) {l r h x : ℝ} (hh : 0 < h)
    (hx : x < r-2*h) :
    taylorPastedExtension f Q l r h =ᶠ[𝓝 x]
      (fun y => finiteTaylorPolynomial f Q (l+2*h) y+
        taylorLeftTransition l h y*(f y-finiteTaylorPolynomial f Q (l+2*h) y)) := by
  filter_upwards [Iio_mem_nhds hx] with y hy
  exact taylorPastedExtension_left_formula f Q hh hy.le

theorem taylorPastedExtension_eventuallyEq_right_formula
    (f : ℝ → ℝ) (Q : ℕ) {l r h x : ℝ} (hh : 0 < h)
    (hx : l+2*h < x) :
    taylorPastedExtension f Q l r h =ᶠ[𝓝 x]
      (fun y => finiteTaylorPolynomial f Q (r-2*h) y+
        taylorRightTransition r h y*(f y-finiteTaylorPolynomial f Q (r-2*h) y)) := by
  filter_upwards [Ioi_mem_nhds hx] with y hy
  exact taylorPastedExtension_right_formula f Q hh hy.le

theorem taylorPastedExtension_eventuallyEq_plateau
    (f : ℝ → ℝ) (Q : ℕ) {l r h x : ℝ} (hh : 0 < h)
    (hx : x ∈ Ioo (l+2*h) (r-2*h)) :
    taylorPastedExtension f Q l r h =ᶠ[𝓝 x] f := by
  filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
  exact taylorPastedExtension_agrees f Q hh ⟨hy.1.le,hy.2.le⟩

theorem taylorPastedExtension_eventuallyEq_left_polynomial
    (f : ℝ → ℝ) (Q : ℕ) {l r h x : ℝ} (hh : 0 < h)
    (hgap : l+4*h < r) (hx : x < l+h) :
    taylorPastedExtension f Q l r h =ᶠ[𝓝 x]
      finiteTaylorPolynomial f Q (l+2*h) := by
  filter_upwards [Iio_mem_nhds hx] with y hy
  change y < l+h at hy
  rw [taylorPastedExtension_left_formula f Q hh (show y ≤ r-2*h by linarith),
    taylorLeftTransition_zero hh hy.le,zero_mul,add_zero]

theorem taylorPastedExtension_eventuallyEq_right_polynomial
    (f : ℝ → ℝ) (Q : ℕ) {l r h x : ℝ} (hh : 0 < h)
    (hgap : l+4*h < r) (hx : r-h < x) :
    taylorPastedExtension f Q l r h =ᶠ[𝓝 x]
      finiteTaylorPolynomial f Q (r-2*h) := by
  filter_upwards [Ioi_mem_nhds hx] with y hy
  change r-h < y at hy
  rw [taylorPastedExtension_right_formula f Q hh (show l+2*h ≤ y by linarith),
    taylorRightTransition_zero hh hy.le,zero_mul,add_zero]

end TaoTrudgianYang2025
