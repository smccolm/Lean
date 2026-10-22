import Dubon2026.SourceCellVerticalSegmentShapes

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

theorem top_shape (R : RadialRegion) (k : Fin R.N) {c y₀ : ℝ} (hc : 0 < c)
    (hy : R.q.im + c = y₀)
    (hr : ∀ t ∈ R.arcIcc k, R.r t = (Real.sin t / c)⁻¹)
    (hw : R.arcIcc k ⊆ Set.Ioo 0 π) :
    ∃ h g : ℝ → ℝ,
      (∀ s ∈ R.arcIcc k, R.loop s = horiz y₀ (h s)) ∧
      StrictAntiOn h (R.arcIcc k) ∧ ContDiffOn ℝ 1 h (R.arcIcc k) ∧
      (∀ s ∈ R.arcIcc k, g (h s) = s) ∧ (∀ x : ℝ, h (g x) = x) ∧
      StrictAnti g ∧
      (∀ (f : ℝ → ℝ) (J : Set ℝ), ContDiffOn ℝ 1 f J → ContDiffOn ℝ 1 (fun t => g (f t)) J) := by
  have hsin : ∀ s ∈ R.arcIcc k, 0 < Real.sin s := fun s hs =>
    Real.sin_pos_of_pos_of_lt_pi (hw hs).1 (hw hs).2
  refine ⟨fun s => R.q.re + c * (Real.cos s / Real.sin s),
    fun x => π / 2 - Real.arctan ((x - R.q.re) / c), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs
    have hs0 : Real.sin s ≠ 0 := (hsin s hs).ne'
    show R.loop s = horiz y₀ (R.q.re + c * (Real.cos s / Real.sin s))
    apply eq_horiz
    · rw [loop_re, hr s hs, inv_div]
      ring
    · rw [loop_im, hr s hs, inv_div, div_mul_cancel₀ _ hs0]
      exact hy
  · intro s hs s' hs' hss'
    have h1 : Real.cos s' / Real.sin s' < Real.cos s / Real.sin s :=
      cot_lt_cot (hw hs).1 (hw hs').2 hss'
    have h2 := mul_lt_mul_of_pos_left h1 hc
    show R.q.re + c * (Real.cos s' / Real.sin s') < R.q.re + c * (Real.cos s / Real.sin s)
    linarith
  · refine ContDiffOn.add contDiffOn_const ?_
    refine ContDiffOn.mul contDiffOn_const ?_
    exact ContDiffOn.div Real.contDiff_cos.contDiffOn Real.contDiff_sin.contDiffOn
      (fun s hs => (hsin s hs).ne')
  · intro s hs
    have h1 := (hw hs).1
    have h2 := (hw hs).2
    have hat : Real.arctan (Real.tan (π / 2 - s)) = π / 2 - s :=
      Real.arctan_tan (by linarith) (by linarith)
    have e : R.q.re + c * (Real.cos s / Real.sin s) - R.q.re = c * (Real.cos s / Real.sin s) := by
      ring
    show π / 2 - Real.arctan ((R.q.re + c * (Real.cos s / Real.sin s) - R.q.re) / c) = s
    rw [e, mul_div_cancel_left₀ _ hc.ne', cot_eq_tan_pi_div_two_sub, hat]
    ring
  · intro x
    show R.q.re + c * (Real.cos (π / 2 - Real.arctan ((x - R.q.re) / c)) /
        Real.sin (π / 2 - Real.arctan ((x - R.q.re) / c))) = x
    rw [cot_pi_div_two_sub, Real.tan_arctan, mul_div_cancel₀ _ hc.ne']
    ring
  · intro x x' hxx'
    have h1 : (x - R.q.re) / c < (x' - R.q.re) / c := div_lt_div_of_pos_right (by linarith) hc
    have h2 := Real.arctan_strictMono h1
    show π / 2 - Real.arctan ((x' - R.q.re) / c) < π / 2 - Real.arctan ((x - R.q.re) / c)
    linarith
  · intro f J hf
    have hinner : ContDiffOn ℝ 1 (fun t => (f t - R.q.re) / c) J := by
      refine ContDiffOn.div_const ?_ c
      exact ContDiffOn.sub hf contDiffOn_const
    show ContDiffOn ℝ 1 (fun t => π / 2 - Real.arctan ((f t - R.q.re) / c)) J
    refine ContDiffOn.sub contDiffOn_const ?_
    exact Real.contDiff_arctan.comp_contDiffOn hinner

theorem bottom_shape (R : RadialRegion) (k : Fin R.N) {d y₀ : ℝ} (hd : 0 < d)
    (hy : R.q.im - d = y₀)
    (hr : ∀ t ∈ R.arcIcc k, R.r t = (-Real.sin t / d)⁻¹)
    (hw : R.arcIcc k ⊆ Set.Ioo π (2 * π)) :
    ∃ h g : ℝ → ℝ,
      (∀ s ∈ R.arcIcc k, R.loop s = horiz y₀ (h s)) ∧
      StrictMonoOn h (R.arcIcc k) ∧ ContDiffOn ℝ 1 h (R.arcIcc k) ∧
      (∀ s ∈ R.arcIcc k, g (h s) = s) ∧ (∀ x : ℝ, h (g x) = x) ∧
      StrictMono g ∧
      (∀ (f : ℝ → ℝ) (J : Set ℝ), ContDiffOn ℝ 1 f J → ContDiffOn ℝ 1 (fun t => g (f t)) J) := by
  have hsin : ∀ s ∈ R.arcIcc k, Real.sin s < 0 := by
    intro s hs
    have h1 := (hw hs).1
    have h2 := (hw hs).2
    have h3 : 0 < Real.sin (s - π) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
    rw [Real.sin_sub_pi] at h3
    linarith
  refine ⟨fun s => R.q.re - d * (Real.cos s / Real.sin s),
    fun x => π / 2 - Real.arctan ((R.q.re - x) / d) + π, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs
    have hs0 : Real.sin s ≠ 0 := (hsin s hs).ne
    show R.loop s = horiz y₀ (R.q.re - d * (Real.cos s / Real.sin s))
    apply eq_horiz
    · have h1 : d / -Real.sin s * Real.cos s = -(d * (Real.cos s / Real.sin s)) := by
        field_simp
      rw [loop_re, hr s hs, inv_div]
      linarith
    · have h2 : d / -Real.sin s * Real.sin s = -d := by
        field_simp
      rw [loop_im, hr s hs, inv_div]
      linarith
  · intro s hs s' hs' hss'
    have h1 : Real.cos s' / Real.sin s' < Real.cos s / Real.sin s := by
      have hs1 := (hw hs).1
      have hs2 := (hw hs').2
      rw [cot_sub_pi s, cot_sub_pi s']
      exact cot_lt_cot (by linarith) (by linarith) (by linarith)
    have h2 := mul_lt_mul_of_pos_left h1 hd
    show R.q.re - d * (Real.cos s / Real.sin s) < R.q.re - d * (Real.cos s' / Real.sin s')
    linarith
  · refine ContDiffOn.sub contDiffOn_const ?_
    refine ContDiffOn.mul contDiffOn_const ?_
    exact ContDiffOn.div Real.contDiff_cos.contDiffOn Real.contDiff_sin.contDiffOn
      (fun s hs => (hsin s hs).ne)
  · intro s hs
    have h1 := (hw hs).1
    have h2 := (hw hs).2
    have hat : Real.arctan (Real.tan (π / 2 - (s - π))) = π / 2 - (s - π) :=
      Real.arctan_tan (by linarith) (by linarith)
    have e : R.q.re - (R.q.re - d * (Real.cos s / Real.sin s)) = d * (Real.cos s / Real.sin s) := by
      ring
    show π / 2 - Real.arctan ((R.q.re - (R.q.re - d * (Real.cos s / Real.sin s))) / d) + π = s
    rw [e, mul_div_cancel_left₀ _ hd.ne', cot_sub_pi s, cot_eq_tan_pi_div_two_sub, hat]
    ring
  · intro x
    show R.q.re - d * (Real.cos (π / 2 - Real.arctan ((R.q.re - x) / d) + π) /
        Real.sin (π / 2 - Real.arctan ((R.q.re - x) / d) + π)) = x
    rw [Real.cos_add_pi, Real.sin_add_pi, neg_div_neg_eq, cot_pi_div_two_sub, Real.tan_arctan,
      mul_div_cancel₀ _ hd.ne']
    ring
  · intro x x' hxx'
    have h1 : (R.q.re - x') / d < (R.q.re - x) / d := div_lt_div_of_pos_right (by linarith) hd
    have h2 := Real.arctan_strictMono h1
    show π / 2 - Real.arctan ((R.q.re - x) / d) + π < π / 2 - Real.arctan ((R.q.re - x') / d) + π
    linarith
  · intro f J hf
    have hinner : ContDiffOn ℝ 1 (fun t => (R.q.re - f t) / d) J := by
      refine ContDiffOn.div_const ?_ d
      exact ContDiffOn.sub contDiffOn_const hf
    show ContDiffOn ℝ 1 (fun t => π / 2 - Real.arctan ((R.q.re - f t) / d) + π) J
    refine ContDiffOn.add ?_ contDiffOn_const
    refine ContDiffOn.sub contDiffOn_const ?_
    exact Real.contDiff_arctan.comp_contDiffOn hinner


end
end Dubon2026.SourceFunctionField.CellGeometry.SegmentTransport
