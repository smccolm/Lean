import Dubon2026.SourceCellRadialRegion
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Tactic

/-! DUB-17/18 -> original Abel-Jacobi -> paired analytic cell dissection.
Rectangle corner angles identify the smooth branches of the actual radial
radius. These are used by the required six-arc rectangle construction.
Adapted from anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.RectRadial
open Real
variable {u v : ℝ}

/- As constructed below. -/
/-- The positive-quadrant angle locating a rectangle corner. -/
noncomputable def cornerAngle (u v : ℝ) : ℝ := Real.arctan (v / u)

theorem cornerAngle_pos (hu : 0 < u) (hv : 0 < v) : 0 < cornerAngle u v :=
  Real.arctan_pos.mpr (div_pos hv hu)

theorem cornerAngle_lt_pi_div_two (u v : ℝ) : cornerAngle u v < π / 2 :=
  Real.arctan_lt_pi_div_two _

theorem pivot (hu : 0 < u) (hv : 0 < v) :
    u * Real.sin (cornerAngle u v) = v * Real.cos (cornerAngle u v) := by
  rw [cornerAngle, Real.sin_arctan, Real.cos_arctan]
  have h1 : Real.sqrt (1 + (v / u) ^ 2) ≠ 0 := by positivity
  field_simp

theorem core_cos (hu : 0 < u) (hv : 0 < v) {s : ℝ} (hs : |s| ≤ cornerAngle u v) :
    u * |Real.sin s| ≤ v * Real.cos s := by
  have hψ2 := cornerAngle_lt_pi_div_two u v
  have hψ0 := cornerAngle_pos hu hv
  have habs1 : |s| < π / 2 := lt_of_le_of_lt hs hψ2
  have hmem : |s| ∈ Set.Icc (-(π / 2)) (π / 2) :=
    ⟨by linarith [abs_nonneg s], habs1.le⟩
  have hψmem : cornerAngle u v ∈ Set.Icc (-(π / 2)) (π / 2) :=
    ⟨by linarith, hψ2.le⟩
  have hsin : |Real.sin s| = Real.sin |s| := by
    rcases le_total 0 s with h | h
    · rw [abs_of_nonneg h, abs_of_nonneg
        (Real.sin_nonneg_of_nonneg_of_le_pi h (by linarith [abs_of_nonneg h, pi_pos]))]
    · rcases h.lt_or_eq with h' | h'
      · have hsneg : Real.sin s < 0 := by
          have h1 : -(π / 2) < s := by
            have := abs_lt.mp habs1
            linarith [this.1]
          exact Real.sin_neg_of_neg_of_neg_pi_lt h' (by linarith [pi_pos])
        rw [abs_of_neg h', abs_of_neg hsneg, Real.sin_neg]
      · subst h'
        simp
  have hcos : Real.cos s = Real.cos |s| := (Real.cos_abs s).symm
  rw [hsin, hcos]
  have h1 : Real.sin |s| ≤ Real.sin (cornerAngle u v) :=
    Real.strictMonoOn_sin.monotoneOn hmem hψmem hs
  have h2 : Real.cos (cornerAngle u v) ≤ Real.cos |s| := by
    rcases eq_or_lt_of_le hs with h | h
    · rw [h]
    · exact (Real.strictAntiOn_cos ⟨abs_nonneg s, by linarith [pi_pos]⟩
        ⟨hψ0.le, by linarith [pi_pos]⟩ h).le
  calc u * Real.sin |s| ≤ u * Real.sin (cornerAngle u v) := by gcongr
  _ = v * Real.cos (cornerAngle u v) := pivot hu hv
  _ ≤ v * Real.cos |s| := by gcongr

theorem core_sin (hu : 0 < u) (hv : 0 < v) {s : ℝ}
    (h1 : cornerAngle u v ≤ s) (h2 : s ≤ π - cornerAngle u v) :
    v * |Real.cos s| ≤ u * Real.sin s := by
  have hψ2 := cornerAngle_lt_pi_div_two u v
  have hψ0 := cornerAngle_pos hu hv

  rcases le_total s (π / 2) with hhalf | hhalf
  · have hccos : 0 ≤ Real.cos s :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith, hhalf⟩
    rw [abs_of_nonneg hccos]
    have hc1 : Real.cos s ≤ Real.cos (cornerAngle u v) := by
      rcases eq_or_lt_of_le h1 with h | h
      · rw [← h]
      · exact (Real.strictAntiOn_cos ⟨hψ0.le, by linarith [pi_pos]⟩
          ⟨by linarith, by linarith [pi_pos]⟩ h).le
    have hs1 : Real.sin (cornerAngle u v) ≤ Real.sin s :=
      Real.strictMonoOn_sin.monotoneOn ⟨by linarith, hψ2.le⟩
        ⟨by linarith, hhalf⟩ h1
    calc v * Real.cos s ≤ v * Real.cos (cornerAngle u v) := by gcongr
    _ = u * Real.sin (cornerAngle u v) := (pivot hu hv).symm
    _ ≤ u * Real.sin s := by gcongr
  · rcases hhalf.lt_or_eq with hhalf' | hhalf'
    swap
    · rw [← hhalf']
      simp [Real.cos_pi_div_two, Real.sin_pi_div_two]
      positivity
    have h1' : cornerAngle u v ≤ π - s := by linarith
    have h2' : π - s ≤ π / 2 := by linarith
    have hccos : Real.cos (π - s) = -Real.cos s := by
      simp [Real.cos_sub, Real.cos_pi, Real.sin_pi]
    have hssin : Real.sin (π - s) = Real.sin s := by
      simp [Real.sin_sub, Real.cos_pi, Real.sin_pi]
    have hcneg : Real.cos s < 0 :=
      Real.cos_neg_of_pi_div_two_lt_of_lt hhalf' (by linarith [pi_pos])
    rw [abs_of_neg hcneg]
    have hccos' : 0 ≤ Real.cos (π - s) := by rw [hccos]; linarith
    have hc1 : Real.cos (π - s) ≤ Real.cos (cornerAngle u v) := by
      rcases eq_or_lt_of_le h1' with h | h
      · rw [← h]
      · exact (Real.strictAntiOn_cos ⟨hψ0.le, by linarith [pi_pos]⟩
          ⟨by linarith, by linarith [pi_pos]⟩ h).le
    have hs1 : Real.sin (cornerAngle u v) ≤ Real.sin (π - s) :=
      Real.strictMonoOn_sin.monotoneOn ⟨by linarith, hψ2.le⟩
        ⟨by linarith, h2'⟩ h1'
    have hkey : v * -Real.cos s ≤ u * Real.sin s := by
      calc v * -Real.cos s = v * Real.cos (π - s) := by rw [hccos]
      _ ≤ v * Real.cos (cornerAngle u v) := by gcongr
      _ = u * Real.sin (cornerAngle u v) := (pivot hu hv).symm
      _ ≤ u * Real.sin (π - s) := by gcongr
      _ = u * Real.sin s := by rw [hssin]
    exact hkey


end Dubon2026.SourceFunctionField.CellGeometry.RectRadial
