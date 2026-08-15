import RiemannZeta.GuthMaynard.DFIErrorTerms

open Complex Finset Set Filter Topology MeasureTheory
open scoped BigOperators Topology Interval ContDiff
open Classical

namespace RiemannZeta.GuthMaynard

theorem probe_x_tail
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U)
    (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hUQ : U = Q ^ 2) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a b q : ℕ), 0 < a → 0 < b → (_hq : NeZero q) →
        (q : ℝ) ≤ 2 * Q → ∀ (h : ℤ) (y : ℝ)
        (branch : DFIVoronoiDualBranch) (n : ℕ), 0 < n →
        ‖dfiEquation29InitialTransform q branch
          (fun x => dfiEquation23Weight w (dfiLocalizedWeight f φ h)
            a b h q x y) n‖ ≤
          (((q : ℝ) / (2 * Real.pi)) ^ 2 / (n : ℝ)) ^ k *
            ((14 * Real.pi + 8) / Real.sqrt q *
              (((X / a) ^ (-(1 / 4 : ℝ)) *
                ((X / a) *
                  (C * ((q : ℝ) * Q)⁻¹ *
                    (((2 * k + 3 : ℕ) : ℝ) * (X / a) *
                      (2 * ((a : ℝ) / ((q : ℝ) * Q))) ^ 2) ^ k))) *
                (n : ℝ) ^ (-(1 / 4 : ℝ)))) := by
  obtain ⟨C, hC, hprofile⟩ :=
    exists_dfiEquation28_xSlice_derivative_profile
      hf hbox hφ hscale w hUQ (2 * k)
  refine ⟨C, hC, ?_⟩
  intro a b q ha hb hqInst hqQ h y branch n hn
  letI : NeZero q := hqInst
  have hq : 0 < q := NeZero.pos q
  let g : ℝ → ℂ := fun x => dfiEquation23Weight w
    (dfiLocalizedWeight f φ h) a b h q x y
  have hg : DFIVoronoiTestFunction g := by
    simpa [g] using dfiEquation23Weight_xSlice w hf hbox hφ a b ha h q hq y
  have hQ : 0 < Q := w.Q_pos
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hX : 0 < X := zero_lt_one.trans_le hf.one_le_X
  have hP : 0 < P := zero_lt_one.trans_le hf.one_le_P
  have hUleX : U ≤ X := by
    have hPinv : P⁻¹ ≤ 1 := by
      rw [inv_le_one₀ hP]
      exact hf.one_le_P
    have hmin0 : 0 ≤ min X Y := le_min
      (zero_le_one.trans hf.one_le_X) (zero_le_one.trans hf.one_le_Y)
    have hminX : min X Y ≤ X := min_le_left _ _
    exact hscale.trans ((mul_le_of_le_one_left hmin0 hPinv).trans hminX)
  have hqQle : (q : ℝ) * Q ≤ 2 * X := by
    calc
      (q : ℝ) * Q ≤ (2 * Q) * Q := by gcongr
      _ = 2 * U := by rw [hUQ]; ring
      _ ≤ 2 * X := by linarith
  have hS : 0 < X / (a : ℝ) := div_pos hX haR
  have hB : 0 ≤ 2 * ((a : ℝ) / ((q : ℝ) * Q)) := by positivity
  have hSB : 1 ≤ (X / (a : ℝ)) *
      (2 * ((a : ℝ) / ((q : ℝ) * Q))) := by
    have hqQpos : 0 < (q : ℝ) * Q := mul_pos hqR hQ
    rw [show (X / (a : ℝ)) *
        (2 * ((a : ℝ) / ((q : ℝ) * Q))) =
      2 * X / ((q : ℝ) * Q) by field_simp]
    exact (le_div_iff₀ hqQpos).2 (by simpa [mul_comm] using hqQle)
  have hSupport : Function.support g ⊆
      Set.Icc (X / (a : ℝ)) (2 * (X / (a : ℝ))) := by
    intro x hx
    have hp : (x, y) ∈ Function.support (Function.uncurry
        (dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q)) := by
      simpa only [g, Function.mem_support,
        Function.uncurry_apply_pair] using hx
    have hmem := dfiEquation23Weight_support_subset w hbox a b h q hp
    constructor
    · exact (div_le_iff₀ haR).2 (by simpa [mul_comm] using hmem.1.1)
    · calc
        x ≤ (2 * X) / (a : ℝ) :=
          (le_div_iff₀ haR).2 (by simpa [mul_comm] using hmem.1.2)
        _ = 2 * (X / (a : ℝ)) := by ring
  have hDeriv : ∀ r ≤ 2 * k, ∀ x : ℝ,
      ‖iteratedDeriv r g x‖ ≤
        (C * ((q : ℝ) * Q)⁻¹) *
          (2 * ((a : ℝ) / ((q : ℝ) * Q))) ^ r := by
    intro r hr x
    have hraw := hprofile a b q ha hb hq hqQ h y r hr x
    have hratio : 0 ≤ (a : ℝ) / ((q : ℝ) * Q) := by positivity
    dsimp [g]
    calc
      ‖iteratedDeriv r
          (fun x => dfiEquation23Weight w (dfiLocalizedWeight f φ h)
            a b h q x y) x‖ ≤
          C * ((q : ℝ) * Q)⁻¹ *
            ((a : ℝ) / ((q : ℝ) * Q)) ^ r := hraw
      _ ≤ (C * ((q : ℝ) * Q)⁻¹) *
          (2 * ((a : ℝ) / ((q : ℝ) * Q))) ^ r := by
        have hratio_le : (a : ℝ) / ((q : ℝ) * Q) ≤
            2 * ((a : ℝ) / ((q : ℝ) * Q)) := by linarith
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ hratio hratio_le r) (by positivity)
  have hout := hg.norm_dfiEquation29InitialTransform_le_recurrence_profile
    (A := C * ((q : ℝ) * Q)⁻¹)
    (B := 2 * ((a : ℝ) / ((q : ℝ) * Q)))
    (S := X / (a : ℝ)) (D := ((2 * k + 3 : ℕ) : ℝ))
    (show 0 ≤ C * ((q : ℝ) * Q)⁻¹ by positivity) hB hS hSB hSupport
    q branch hn k (by exact_mod_cast (le_refl (2 * k + 3))) hDeriv
  simpa [g] using hout

theorem probe_y_tail
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U)
    (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hUQ : U = Q ^ 2) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a b q : ℕ), 0 < a → 0 < b → (_hq : NeZero q) →
        (q : ℝ) ≤ 2 * Q → ∀ (h : ℤ) (x : ℝ)
        (branch : DFIVoronoiDualBranch) (n : ℕ), 0 < n →
        ‖dfiEquation29InitialTransform q branch
          (dfiEquation23Weight w (dfiLocalizedWeight f φ h)
            a b h q x) n‖ ≤
          (((q : ℝ) / (2 * Real.pi)) ^ 2 / (n : ℝ)) ^ k *
            ((14 * Real.pi + 8) / Real.sqrt q *
              (((Y / b) ^ (-(1 / 4 : ℝ)) *
                ((Y / b) *
                  (C * ((q : ℝ) * Q)⁻¹ *
                    (((2 * k + 3 : ℕ) : ℝ) * (Y / b) *
                      (2 * ((b : ℝ) / ((q : ℝ) * Q))) ^ 2) ^ k))) *
                (n : ℝ) ^ (-(1 / 4 : ℝ)))) := by
  obtain ⟨C, hC, hprofile⟩ :=
    exists_dfiEquation28_ySlice_derivative_profile
      hf hbox hφ hscale w hUQ (2 * k)
  refine ⟨C, hC, ?_⟩
  intro a b q ha hb hqInst hqQ h x branch n hn
  letI : NeZero q := hqInst
  have hq : 0 < q := NeZero.pos q
  let g : ℝ → ℂ := dfiEquation23Weight w
    (dfiLocalizedWeight f φ h) a b h q x
  have hg : DFIVoronoiTestFunction g := by
    simpa [g] using dfiEquation23Weight_ySlice w hf hbox hφ a b hb h q hq x
  have hQ : 0 < Q := w.Q_pos
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hY : 0 < Y := zero_lt_one.trans_le hf.one_le_Y
  have hP : 0 < P := zero_lt_one.trans_le hf.one_le_P
  have hUleY : U ≤ Y := by
    have hPinv : P⁻¹ ≤ 1 := by
      rw [inv_le_one₀ hP]
      exact hf.one_le_P
    have hmin0 : 0 ≤ min X Y := le_min
      (zero_le_one.trans hf.one_le_X) (zero_le_one.trans hf.one_le_Y)
    have hminY : min X Y ≤ Y := min_le_right _ _
    exact hscale.trans ((mul_le_of_le_one_left hmin0 hPinv).trans hminY)
  have hqQle : (q : ℝ) * Q ≤ 2 * Y := by
    calc
      (q : ℝ) * Q ≤ (2 * Q) * Q := by gcongr
      _ = 2 * U := by rw [hUQ]; ring
      _ ≤ 2 * Y := by linarith
  have hS : 0 < Y / (b : ℝ) := div_pos hY hbR
  have hB : 0 ≤ 2 * ((b : ℝ) / ((q : ℝ) * Q)) := by positivity
  have hSB : 1 ≤ (Y / (b : ℝ)) *
      (2 * ((b : ℝ) / ((q : ℝ) * Q))) := by
    have hqQpos : 0 < (q : ℝ) * Q := mul_pos hqR hQ
    rw [show (Y / (b : ℝ)) *
        (2 * ((b : ℝ) / ((q : ℝ) * Q))) =
      2 * Y / ((q : ℝ) * Q) by field_simp]
    exact (le_div_iff₀ hqQpos).2 (by simpa [mul_comm] using hqQle)
  have hSupport : Function.support g ⊆
      Set.Icc (Y / (b : ℝ)) (2 * (Y / (b : ℝ))) := by
    intro y hy
    have hp : (x, y) ∈ Function.support (Function.uncurry
        (dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q)) := by
      simpa only [g, Function.mem_support,
        Function.uncurry_apply_pair] using hy
    have hmem := dfiEquation23Weight_support_subset w hbox a b h q hp
    constructor
    · exact (div_le_iff₀ hbR).2 (by simpa [mul_comm] using hmem.2.1)
    · calc
        y ≤ (2 * Y) / (b : ℝ) :=
          (le_div_iff₀ hbR).2 (by simpa [mul_comm] using hmem.2.2)
        _ = 2 * (Y / (b : ℝ)) := by ring
  have hDeriv : ∀ r ≤ 2 * k, ∀ y : ℝ,
      ‖iteratedDeriv r g y‖ ≤
        (C * ((q : ℝ) * Q)⁻¹) *
          (2 * ((b : ℝ) / ((q : ℝ) * Q))) ^ r := by
    intro r hr y
    have hraw := hprofile a b q ha hb hq hqQ h x r hr y
    have hratio : 0 ≤ (b : ℝ) / ((q : ℝ) * Q) := by positivity
    dsimp [g]
    calc
      ‖iteratedDeriv r
          (dfiEquation23Weight w (dfiLocalizedWeight f φ h)
            a b h q x) y‖ ≤
          C * ((q : ℝ) * Q)⁻¹ *
            ((b : ℝ) / ((q : ℝ) * Q)) ^ r := hraw
      _ ≤ (C * ((q : ℝ) * Q)⁻¹) *
          (2 * ((b : ℝ) / ((q : ℝ) * Q))) ^ r := by
        have hratio_le : (b : ℝ) / ((q : ℝ) * Q) ≤
            2 * ((b : ℝ) / ((q : ℝ) * Q)) := by linarith
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ hratio hratio_le r) (by positivity)
  have hout := hg.norm_dfiEquation29InitialTransform_le_recurrence_profile
    (A := C * ((q : ℝ) * Q)⁻¹)
    (B := 2 * ((b : ℝ) / ((q : ℝ) * Q)))
    (S := Y / (b : ℝ)) (D := ((2 * k + 3 : ℕ) : ℝ))
    (show 0 ≤ C * ((q : ℝ) * Q)⁻¹ by positivity) hB hS hSB hSupport
    q branch hn k (by exact_mod_cast (le_refl (2 * k + 3))) hDeriv
  simpa [g] using hout

theorem probe_x_tail_ratio
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U)
    (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hUQ : U = Q ^ 2) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a b q : ℕ), 0 < a → 0 < b → (_hq : NeZero q) →
        (q : ℝ) ≤ 2 * Q → ∀ (h : ℤ) (y : ℝ)
        (branch : DFIVoronoiDualBranch) (n : ℕ), 0 < n →
        ‖dfiEquation29InitialTransform q branch
          (fun x => dfiEquation23Weight w (dfiLocalizedWeight f φ h)
            a b h q x y) n‖ ≤
          ((((2 * k + 3 : ℕ) : ℝ) / Real.pi ^ 2) *
              (((a : ℝ) * X) / ((n : ℝ) * Q ^ 2))) ^ k *
            ((14 * Real.pi + 8) / Real.sqrt q *
              (((X / a) ^ (-(1 / 4 : ℝ)) *
                ((X / a) * (C * ((q : ℝ) * Q)⁻¹))) *
                (n : ℝ) ^ (-(1 / 4 : ℝ)))) := by
  obtain ⟨C, hC, hbound⟩ := probe_x_tail
    hf hbox hφ hscale w hUQ k
  refine ⟨C, hC, ?_⟩
  intro a b q ha hb hqInst hqQ h y branch n hn
  letI : NeZero q := hqInst
  have hq : 0 < q := NeZero.pos q
  have hraw := hbound a b q ha hb hqInst hqQ h y branch n hn
  have hQ : 0 < Q := w.Q_pos
  calc
    ‖dfiEquation29InitialTransform q branch
        (fun x => dfiEquation23Weight w (dfiLocalizedWeight f φ h)
          a b h q x y) n‖ ≤ _ := hraw
    _ = (((((q : ℝ) / (2 * Real.pi)) ^ 2 / (n : ℝ)) ^ k *
          ((((2 * k + 3 : ℕ) : ℝ) * (X / a) *
            (2 * ((a : ℝ) / ((q : ℝ) * Q))) ^ 2) ^ k)) *
          ((14 * Real.pi + 8) / Real.sqrt q *
            (((X / a) ^ (-(1 / 4 : ℝ)) *
              ((X / a) * (C * ((q : ℝ) * Q)⁻¹))) *
              (n : ℝ) ^ (-(1 / 4 : ℝ))))) := by ring
    _ = _ := by
      rw [dfiEquation29_recurrence_ratio hQ ha hq hn
        (((2 * k + 3 : ℕ) : ℝ)) k]

end RiemannZeta.GuthMaynard
