import Dubon2026.SourceCellSixArcTrigonometry
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-! DUB-17/18 -> original Abel-Jacobi -> actual boundary pairing.
Opposite sides require a decreasing C1 reparametrization; square-to-window
sides require an increasing one before reciprocal reversal. Exact endpoint
and loop identities are retained for the lifted original-cell pairing.
The two external reparametrization files contain the same shared proof;
adapt it once, reusing the existing shifted tangent and cotangent lemmas.
Unused affine-transport generalizations are omitted.
Source: anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.SegmentTransport
noncomputable section
open scoped Real
open Set

theorem arcIcc_eq (R : RadialRegion) (k : Fin R.N) :
    R.arcIcc k = Set.Icc (R.φs k.castSucc) (R.φs k.succ) := rfl

theorem loop_re (R : RadialRegion) (s : ℝ) : (R.loop s).re = R.q.re + R.r s * Real.cos s := by
  show (R.q + (R.r s : ℂ) * Complex.exp ((s : ℂ) * Complex.I)).re = _
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, zero_mul, sub_zero]

theorem loop_im (R : RadialRegion) (s : ℝ) : (R.loop s).im = R.q.im + R.r s * Real.sin s := by
  show (R.q + (R.r s : ℂ) * Complex.exp ((s : ℂ) * Complex.I)).im = _
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, zero_mul, add_zero]

/-- Point at a prescribed height on a vertical line. -/
noncomputable def vert (x₀ y : ℝ) : ℂ := ⟨x₀, y⟩

/-- Point at a prescribed abscissa on a horizontal line. -/
noncomputable def horiz (y₀ x : ℝ) : ℂ := ⟨x, y₀⟩

theorem vert_re (x₀ y : ℝ) : (vert x₀ y).re = x₀ := rfl
theorem vert_im (x₀ y : ℝ) : (vert x₀ y).im = y := rfl
theorem horiz_re (y₀ x : ℝ) : (horiz y₀ x).re = x := rfl
theorem horiz_im (y₀ x : ℝ) : (horiz y₀ x).im = y₀ := rfl

theorem vert_injective (x₀ : ℝ) : Function.Injective (vert x₀) := by
  intro y y' hyy'
  have h := congrArg Complex.im hyy'
  rwa [vert_im, vert_im] at h

theorem horiz_injective (y₀ : ℝ) : Function.Injective (horiz y₀) := by
  intro x x' hxx'
  have h := congrArg Complex.re hxx'
  rwa [horiz_re, horiz_re] at h

theorem eq_vert {z : ℂ} {x₀ y : ℝ} (hre : z.re = x₀) (him : z.im = y) : z = vert x₀ y := by
  apply Complex.ext
  · rw [vert_re]
    exact hre
  · rw [vert_im]
    exact him

theorem eq_horiz {z : ℂ} {y₀ x : ℝ} (hre : z.re = x) (him : z.im = y₀) : z = horiz y₀ x := by
  apply Complex.ext
  · rw [horiz_re]
    exact hre
  · rw [horiz_im]
    exact him

theorem comp_anti_of_mono_anti {g f : ℝ → ℝ} {J : Set ℝ} (hg : StrictMono g)
    (hf : StrictAntiOn f J) : StrictAntiOn (fun t => g (f t)) J := by
  intro t ht t' ht' htt'
  exact hg (hf ht ht' htt')

theorem comp_anti_of_anti_mono {g f : ℝ → ℝ} {J : Set ℝ} (hg : StrictAnti g)
    (hf : StrictMonoOn f J) : StrictAntiOn (fun t => g (f t)) J := by
  intro t ht t' ht' htt'
  exact hg (hf ht ht' htt')

theorem comp_mono_of_mono_mono {g f : ℝ → ℝ} {J : Set ℝ} (hg : StrictMono g)
    (hf : StrictMonoOn f J) : StrictMonoOn (fun t => g (f t)) J := by
  intro t ht t' ht' htt'
  exact hg (hf ht ht' htt')

theorem comp_mono_of_anti_anti {g f : ℝ → ℝ} {J : Set ℝ} (hg : StrictAnti g)
    (hf : StrictAntiOn f J) : StrictMonoOn (fun t => g (f t)) J := by
  intro t ht t' ht' htt'
  exact hg (hf ht ht' htt')

theorem tan_lt_tan_shifted {x y : ℝ} (hx : π / 2 < x) (hy : y < 3 * π / 2) (hxy : x < y) :
    Real.tan x < Real.tan y :=
  RectSixArcs.r6_tan_strictMonoOn_shifted ⟨hx, hxy.trans hy⟩ ⟨hx.trans hxy, hy⟩ hxy

theorem cot_lt_cot {u u' : ℝ} (h0 : 0 < u) (hπ : u' < π) (huu : u < u') :
    Real.cos u' / Real.sin u' < Real.cos u / Real.sin u :=
  RectSixArcs.r6_cot_lt_cot h0 hπ huu

theorem cot_sub_pi (t : ℝ) : Real.cos t / Real.sin t = Real.cos (t - π) / Real.sin (t - π) :=
  (RectSixArcs.r6_cot_sub_pi t).symm

theorem cot_eq_tan_pi_div_two_sub (x : ℝ) : Real.cos x / Real.sin x = Real.tan (π / 2 - x) := by
  rw [Real.tan_eq_sin_div_cos, Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]

theorem cot_pi_div_two_sub (v : ℝ) :
    Real.cos (π / 2 - v) / Real.sin (π / 2 - v) = Real.tan v := by
  rw [Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub, ← Real.tan_eq_sin_div_cos]

theorem exists_shift {J : Set ℝ}
    (hJ : J ⊆ Set.Ioo (-(π / 2)) (π / 2) ∨ J ⊆ Set.Ioo (3 * π / 2) (5 * π / 2)) :
    ∃ c : ℝ, (∀ s ∈ J, -(π / 2) < s - c ∧ s - c < π / 2) ∧
      (∀ x : ℝ, Real.cos (x - c) = Real.cos x) ∧ (∀ x : ℝ, Real.tan (x - c) = Real.tan x) := by
  rcases hJ with hJ | hJ
  · refine ⟨0, fun s hs => ?_, fun x => by rw [sub_zero], fun x => by rw [sub_zero]⟩
    have h := hJ hs
    have h1 := h.1
    have h2 := h.2
    exact ⟨by linarith, by linarith⟩
  · refine ⟨2 * π, fun s hs => ?_, fun x => Real.cos_sub_two_pi x, fun x => ?_⟩
    · have h := hJ hs
      have h1 := h.1
      have h2 := h.2
      exact ⟨by linarith, by linarith⟩
    · rw [show x - 2 * π = x - π - π by ring, Real.tan_sub_pi, Real.tan_sub_pi]


end
end Dubon2026.SourceFunctionField.CellGeometry.SegmentTransport
