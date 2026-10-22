import Dubon2026.SourceCellSegmentCoordinates

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

theorem right_shape (R : RadialRegion) (k : Fin R.N) {a x₀ : ℝ} (ha : 0 < a)
    (hx : R.q.re + a = x₀)
    (hr : ∀ t ∈ R.arcIcc k, R.r t = (Real.cos t / a)⁻¹)
    (hw : R.arcIcc k ⊆ Set.Ioo (-(π / 2)) (π / 2) ∨ R.arcIcc k ⊆ Set.Ioo (3 * π / 2) (5 * π / 2)) :
    ∃ h g : ℝ → ℝ,
      (∀ s ∈ R.arcIcc k, R.loop s = vert x₀ (h s)) ∧
      StrictMonoOn h (R.arcIcc k) ∧ ContDiffOn ℝ 1 h (R.arcIcc k) ∧
      (∀ s ∈ R.arcIcc k, g (h s) = s) ∧ (∀ y : ℝ, h (g y) = y) ∧
      StrictMono g ∧
      (∀ (f : ℝ → ℝ) (J : Set ℝ), ContDiffOn ℝ 1 f J → ContDiffOn ℝ 1 (fun t => g (f t)) J) := by
  obtain ⟨c, hwin, hcosc, htanc⟩ := exists_shift hw
  have hmem : ∀ s ∈ R.arcIcc k, s - c ∈ Set.Ioo (-(π / 2)) (π / 2) := fun s hs =>
    ⟨(hwin s hs).1, (hwin s hs).2⟩
  have hcos : ∀ s ∈ R.arcIcc k, 0 < Real.cos s := by
    intro s hs
    rw [← hcosc s]
    exact Real.cos_pos_of_mem_Ioo (hmem s hs)
  refine ⟨fun s => R.q.im + a * Real.tan s, fun y => Real.arctan ((y - R.q.im) / a) + c,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs
    have hc : Real.cos s ≠ 0 := (hcos s hs).ne'
    show R.loop s = vert x₀ (R.q.im + a * Real.tan s)
    apply eq_vert
    · rw [loop_re, hr s hs, inv_div, div_mul_cancel₀ _ hc]
      exact hx
    · rw [loop_im, hr s hs, inv_div, Real.tan_eq_sin_div_cos]
      ring
  · intro s hs s' hs' hss'
    have h1 : Real.tan s < Real.tan s' := by
      rw [← htanc s, ← htanc s']
      exact Real.strictMonoOn_tan (hmem s hs) (hmem s' hs') (by linarith)
    have h2 := mul_lt_mul_of_pos_left h1 ha
    show R.q.im + a * Real.tan s < R.q.im + a * Real.tan s'
    linarith
  · refine ContDiffOn.add contDiffOn_const ?_
    refine ContDiffOn.mul contDiffOn_const ?_
    exact fun s hs => (Real.contDiffAt_tan.mpr (hcos s hs).ne').contDiffWithinAt
  · intro s hs
    have h1 := (hwin s hs).1
    have h2 := (hwin s hs).2
    have hat : Real.arctan (Real.tan (s - c)) = s - c := Real.arctan_tan h1 h2
    show Real.arctan ((R.q.im + a * Real.tan s - R.q.im) / a) + c = s
    rw [show R.q.im + a * Real.tan s - R.q.im = a * Real.tan s by ring,
      mul_div_cancel_left₀ _ ha.ne', ← htanc s, hat]
    ring
  · intro y
    have ht : Real.tan (Real.arctan ((y - R.q.im) / a) + c) = (y - R.q.im) / a := by
      rw [← htanc (Real.arctan ((y - R.q.im) / a) + c),
        show Real.arctan ((y - R.q.im) / a) + c - c = Real.arctan ((y - R.q.im) / a) by ring,
        Real.tan_arctan]
    show R.q.im + a * Real.tan (Real.arctan ((y - R.q.im) / a) + c) = y
    rw [ht, mul_div_cancel₀ _ ha.ne']
    ring
  · intro y y' hyy'
    have h1 : (y - R.q.im) / a < (y' - R.q.im) / a := div_lt_div_of_pos_right (by linarith) ha
    have h2 := Real.arctan_strictMono h1
    show Real.arctan ((y - R.q.im) / a) + c < Real.arctan ((y' - R.q.im) / a) + c
    linarith
  · intro f J hf
    have hinner : ContDiffOn ℝ 1 (fun t => (f t - R.q.im) / a) J := by
      refine ContDiffOn.div_const ?_ a
      exact ContDiffOn.sub hf contDiffOn_const
    show ContDiffOn ℝ 1 (fun t => Real.arctan ((f t - R.q.im) / a) + c) J
    refine ContDiffOn.add ?_ contDiffOn_const
    exact Real.contDiff_arctan.comp_contDiffOn hinner

theorem left_shape (R : RadialRegion) (k : Fin R.N) {b x₀ : ℝ} (hb : 0 < b)
    (hx : R.q.re - b = x₀)
    (hr : ∀ t ∈ R.arcIcc k, R.r t = (-Real.cos t / b)⁻¹)
    (hw : R.arcIcc k ⊆ Set.Ioo (π / 2) (3 * π / 2)) :
    ∃ h g : ℝ → ℝ,
      (∀ s ∈ R.arcIcc k, R.loop s = vert x₀ (h s)) ∧
      StrictAntiOn h (R.arcIcc k) ∧ ContDiffOn ℝ 1 h (R.arcIcc k) ∧
      (∀ s ∈ R.arcIcc k, g (h s) = s) ∧ (∀ y : ℝ, h (g y) = y) ∧
      StrictAnti g ∧
      (∀ (f : ℝ → ℝ) (J : Set ℝ), ContDiffOn ℝ 1 f J → ContDiffOn ℝ 1 (fun t => g (f t)) J) := by
  have hcos : ∀ s ∈ R.arcIcc k, Real.cos s < 0 := by
    intro s hs
    have h1 := (hw hs).1
    have h2 := (hw hs).2
    exact Real.cos_neg_of_pi_div_two_lt_of_lt h1 (by linarith)
  refine ⟨fun s => R.q.im - b * Real.tan s, fun y => Real.arctan ((R.q.im - y) / b) + π,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs
    have hc : Real.cos s ≠ 0 := (hcos s hs).ne
    show R.loop s = vert x₀ (R.q.im - b * Real.tan s)
    apply eq_vert
    · have h1 : b / -Real.cos s * Real.cos s = -b := by
        field_simp
      rw [loop_re, hr s hs, inv_div, h1]
      linarith
    · have h2 : b / -Real.cos s * Real.sin s = -(b * Real.tan s) := by
        rw [Real.tan_eq_sin_div_cos]
        field_simp
      rw [loop_im, hr s hs, inv_div]
      linarith
  · intro s hs s' hs' hss'
    have h1 : Real.tan s < Real.tan s' := tan_lt_tan_shifted (hw hs).1 (hw hs').2 hss'
    have h2 := mul_lt_mul_of_pos_left h1 hb
    show R.q.im - b * Real.tan s' < R.q.im - b * Real.tan s
    linarith
  · refine ContDiffOn.sub contDiffOn_const ?_
    refine ContDiffOn.mul contDiffOn_const ?_
    exact fun s hs => (Real.contDiffAt_tan.mpr (hcos s hs).ne).contDiffWithinAt
  · intro s hs
    have h1 := (hw hs).1
    have h2 := (hw hs).2
    have hat : Real.arctan (Real.tan (s - π)) = s - π :=
      Real.arctan_tan (by linarith) (by linarith)
    show Real.arctan ((R.q.im - (R.q.im - b * Real.tan s)) / b) + π = s
    rw [show R.q.im - (R.q.im - b * Real.tan s) = b * Real.tan s by ring,
      mul_div_cancel_left₀ _ hb.ne', ← Real.tan_sub_pi s, hat]
    ring
  · intro y
    show R.q.im - b * Real.tan (Real.arctan ((R.q.im - y) / b) + π) = y
    rw [Real.tan_add_pi, Real.tan_arctan, mul_div_cancel₀ _ hb.ne']
    ring
  · intro y y' hyy'
    have h1 : (R.q.im - y') / b < (R.q.im - y) / b := div_lt_div_of_pos_right (by linarith) hb
    have h2 := Real.arctan_strictMono h1
    show Real.arctan ((R.q.im - y') / b) + π < Real.arctan ((R.q.im - y) / b) + π
    linarith
  · intro f J hf
    have hinner : ContDiffOn ℝ 1 (fun t => (R.q.im - f t) / b) J := by
      refine ContDiffOn.div_const ?_ b
      exact ContDiffOn.sub contDiffOn_const hf
    show ContDiffOn ℝ 1 (fun t => Real.arctan ((R.q.im - f t) / b) + π) J
    refine ContDiffOn.add ?_ contDiffOn_const
    exact Real.contDiff_arctan.comp_contDiffOn hinner


end
end Dubon2026.SourceFunctionField.CellGeometry.SegmentTransport
