import RiemannZeta.GuthMaynard.DFIErrorTerms

open Complex Finset Set Filter Topology MeasureTheory
open scoped BigOperators Topology Interval ContDiff
open Classical

namespace RiemannZeta.GuthMaynard

theorem probe_x_profile
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U)
    (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hUQ : U = Q ^ 2) (J : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a b q : ℕ), 0 < a → 0 < b → 0 < q →
        (q : ℝ) ≤ 2 * Q → ∀ (h : ℤ) (y : ℝ) (r : ℕ), r ≤ J →
        ∀ x : ℝ,
        ‖iteratedDeriv r
          (fun x => dfiEquation23Weight w (dfiLocalizedWeight f φ h)
            a b h q x y) x‖ ≤
          C * ((q : ℝ) * Q)⁻¹ *
            ((a : ℝ) / ((q : ℝ) * Q)) ^ r := by
  have hEach : ∀ r : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ (a b q : ℕ), 0 < a → 0 < b → 0 < q →
        (q : ℝ) ≤ 2 * Q → ∀ (h : ℤ) (x y : ℝ),
        ‖dfiMixedDeriv r 0
          (dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q) x y‖ ≤
          C * ((q : ℝ) * Q)⁻¹ *
            ((a : ℝ) / ((q : ℝ) * Q)) ^ r := by
    intro r
    obtain ⟨C, hC, hbound⟩ :=
      dfiEquation28_separated_uniform hf hbox hφ hscale w hUQ r 0
    refine ⟨C, hC, ?_⟩
    intro a b q ha hb hq hqQ h x y
    simpa using hbound a b q ha hb hq hqQ h x y
  choose C hC hbound using hEach
  let Csum : ℝ := ∑ r ∈ Finset.range (J + 1), C r
  have hCsum : 0 < Csum := by
    dsimp [Csum]
    exact Finset.sum_pos (fun r _ => hC r) ⟨0, by simp⟩
  refine ⟨Csum, hCsum, ?_⟩
  intro a b q ha hb hq hqQ h y r hr x
  have hrmem : r ∈ Finset.range (J + 1) := by simp [hr]
  have hCle : C r ≤ Csum := by
    dsimp [Csum]
    exact Finset.single_le_sum (fun s _ => (hC s).le) hrmem
  have hraw := hbound r a b q ha hb hq hqQ h x y
  have hQ : 0 < Q := w.Q_pos
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hcoarse : C r * ((q : ℝ) * Q)⁻¹ *
        ((a : ℝ) / ((q : ℝ) * Q)) ^ r ≤
      Csum * ((q : ℝ) * Q)⁻¹ *
        ((a : ℝ) / ((q : ℝ) * Q)) ^ r := by
    gcongr
  simpa [dfiMixedDeriv] using hraw.trans hcoarse

theorem probe_y_profile
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U)
    (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hUQ : U = Q ^ 2) (J : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a b q : ℕ), 0 < a → 0 < b → 0 < q →
        (q : ℝ) ≤ 2 * Q → ∀ (h : ℤ) (x : ℝ) (r : ℕ), r ≤ J →
        ∀ y : ℝ,
        ‖iteratedDeriv r
          (dfiEquation23Weight w (dfiLocalizedWeight f φ h)
            a b h q x) y‖ ≤
          C * ((q : ℝ) * Q)⁻¹ *
            ((b : ℝ) / ((q : ℝ) * Q)) ^ r := by
  have hEach : ∀ r : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ (a b q : ℕ), 0 < a → 0 < b → 0 < q →
        (q : ℝ) ≤ 2 * Q → ∀ (h : ℤ) (x y : ℝ),
        ‖dfiMixedDeriv 0 r
          (dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q) x y‖ ≤
          C * ((q : ℝ) * Q)⁻¹ *
            ((b : ℝ) / ((q : ℝ) * Q)) ^ r := by
    intro r
    obtain ⟨C, hC, hbound⟩ :=
      dfiEquation28_separated_uniform hf hbox hφ hscale w hUQ 0 r
    refine ⟨C, hC, ?_⟩
    intro a b q ha hb hq hqQ h x y
    simpa using hbound a b q ha hb hq hqQ h x y
  choose C hC hbound using hEach
  let Csum : ℝ := ∑ r ∈ Finset.range (J + 1), C r
  have hCsum : 0 < Csum := by
    dsimp [Csum]
    exact Finset.sum_pos (fun r _ => hC r) ⟨0, by simp⟩
  refine ⟨Csum, hCsum, ?_⟩
  intro a b q ha hb hq hqQ h x r hr y
  have hrmem : r ∈ Finset.range (J + 1) := by simp [hr]
  have hCle : C r ≤ Csum := by
    dsimp [Csum]
    exact Finset.single_le_sum (fun s _ => (hC s).le) hrmem
  have hraw := hbound r a b q ha hb hq hqQ h x y
  have hQ : 0 < Q := w.Q_pos
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hcoarse : C r * ((q : ℝ) * Q)⁻¹ *
        ((b : ℝ) / ((q : ℝ) * Q)) ^ r ≤
      Csum * ((q : ℝ) * Q)⁻¹ *
        ((b : ℝ) / ((q : ℝ) * Q)) ^ r := by
    gcongr
  change ‖iteratedDeriv r
      (dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q x) y‖ ≤
    C r * ((q : ℝ) * Q)⁻¹ *
      ((b : ℝ) / ((q : ℝ) * Q)) ^ r at hraw
  exact hraw.trans hcoarse

end RiemannZeta.GuthMaynard
