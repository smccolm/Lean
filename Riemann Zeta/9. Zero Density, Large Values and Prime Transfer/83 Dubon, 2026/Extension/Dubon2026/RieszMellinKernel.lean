import Dubon2026.RieszSecondKernel
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! # The exact Mellin transform of the quadratic Riesz cutoff -/

namespace Dubon2026

open Complex Set MeasureTheory

noncomputable section

/-- The literal compact quadratic cutoff used for the second Riesz mean. -/
def rieszMellinCutoff : ℝ → ℂ :=
  indicator (Ioc 0 1) (fun x => (1 - (x : ℂ)) ^ 2 / 2)

/-- The exact rational Mellin symbol of the factorial-normalized quadratic cutoff. -/
def rieszMellinSymbol (s : ℂ) : ℂ := 1 / (s * (s + 1) * (s + 2))

/-- The actual cutoff agrees with the positive quadratic kernel at every positive argument. -/
theorem rieszMellinCutoff_eq {x : ℝ} (hx : 0 < x) :
    rieszMellinCutoff x = (rieszSecondKernel (1 - x) : ℂ) := by
  by_cases hx1 : x ≤ 1
  · rw [rieszMellinCutoff, indicator_of_mem (show x ∈ Ioc (0 : ℝ) 1 from ⟨hx, hx1⟩),
      rieszSecondKernel_eq (by linarith)]
    push_cast
    ring
  · have hn : x ∉ Ioc (0 : ℝ) 1 := fun hh => hx1 hh.2
    rw [rieszMellinCutoff, indicator_of_notMem hn,
      rieszSecondKernel_eq_zero (by linarith)]
    simp

/-- The genuine quadratic cutoff is Mellin-convergent and has exactly the rational cubic-denominator symbol. -/
theorem hasMellin_rieszMellinCutoff {s : ℂ} (hs : 0 < s.re) :
    HasMellin rieszMellinCutoff s (rieszMellinSymbol s) := by
  let A : ℝ → ℂ := indicator (Ioc 0 1) (fun _ => 1)
  let B : ℝ → ℂ := indicator (Ioc 0 1) (fun x => (x : ℂ) ^ (1 : ℂ))
  let C : ℝ → ℂ := indicator (Ioc 0 1) (fun x => (x : ℂ) ^ (2 : ℂ))
  have hA : HasMellin A s (1 / s) := hasMellin_one_Ioc hs
  have hB : HasMellin B s (1 / (s + 1)) := hasMellin_cpow_Ioc 1 (by simp; linarith)
  have hC : HasMellin C s (1 / (s + 2)) := hasMellin_cpow_Ioc 2 (by simp; linarith)
  have hB2 : MellinConvergent (fun x => (2 : ℂ) • B x) s := hB.1.const_smul 2
  have hAB := hasMellin_sub hA.1 hB2
  have hABC := hasMellin_add hAB.1 hC.1
  have he : rieszMellinCutoff = fun x => (A x - (2 : ℂ) • B x + C x) / 2 := by
    funext x
    by_cases hx : x ∈ Ioc (0 : ℝ) 1
    · simp [rieszMellinCutoff, A, B, C, hx, smul_eq_mul]
      ring
    · simp [rieszMellinCutoff, A, B, C, hx]
  rw [he]
  refine ⟨hABC.1.div_const 2, ?_⟩
  rw [mellin_div_const, hABC.2, hAB.2, mellin_const_smul, hA.2, hB.2, hC.2, smul_eq_mul]
  have hs0 : s ≠ 0 := by intro h; simp only [h, zero_re] at hs; linarith
  have hs1 : s + 1 ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    simp only [add_re, one_re, zero_re] at hh
    linarith
  have hs2 : s + 2 ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    norm_num at hh
    linarith
  unfold rieszMellinSymbol
  field_simp
  ring

end
end Dubon2026
