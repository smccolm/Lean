import Dubon2026.CoefficientShift
import Dubon2026.JessenProbability

/-! # Translation of the actual Jessen derivative measure under coefficient normalization -/

namespace Dubon2026

open Set MeasureTheory

theorem jessen_rightDeriv_shiftedCoefficients {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (c x : ℝ) :
    derivWithin (jessenFunction (shiftedCoefficients a c) N) (Ioi x) x =
      derivWithin (jessenFunction a N) (Ioi (x - c)) (x - c) := by
  have hf := (convexOn_jessenFunction hN ha).hasDerivWithinAt_rightDeriv_of_mem_interior
    (by simp : x - c ∈ interior (univ : Set ℝ))
  have hg : HasDerivWithinAt (fun y : ℝ => y - c) 1 (Ioi x) x :=
    ((hasDerivAt_id x).sub_const c).hasDerivWithinAt
  have hm : MapsTo (fun y : ℝ => y - c) (Ioi x) (Ioi (x - c)) := by
    intro y hy
    exact sub_lt_sub_right hy c
  have hd := hf.comp x hg hm
  have he : jessenFunction (shiftedCoefficients a c) N =
      jessenFunction a N ∘ (fun y : ℝ => y - c) :=
    funext (jessenFunction_shiftedCoefficients a N c)
  rw [he]
  simpa only [mul_one] using hd.derivWithin (uniqueDiffWithinAt_Ioi x)

theorem jessenMeasure_shiftedCoefficients {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (c : ℝ) :
    jessenMeasure (a := shiftedCoefficients a c) hN (by rwa [shiftedCoefficients_one]) =
      Measure.map (fun x : ℝ => x + c) (jessenMeasure hN ha) := by
  apply Measure.ext_of_Ioc
  intro l u _
  have hm : Measurable (fun x : ℝ => x + c) := measurable_id.add_const c
  rw [Measure.map_apply hm measurableSet_Ioc]
  have he : (fun x : ℝ => x + c) ⁻¹' Ioc l u = Ioc (l - c) (u - c) := by
    ext x
    simp only [mem_preimage, mem_Ioc]
    constructor <;> rintro ⟨hl, hu⟩ <;> constructor <;> linarith
  rw [he, jessenMeasure_Ioc, jessenMeasure_Ioc,
    jessen_rightDeriv_shiftedCoefficients hN ha, jessen_rightDeriv_shiftedCoefficients hN ha]

theorem normalizedJessenMeasure_shiftedCoefficients {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (c : ℝ) :
    normalizedJessenMeasure (a := shiftedCoefficients a c) hN
      (by rwa [shiftedCoefficients_one]) =
        Measure.map (fun x : ℝ => x + c) (normalizedJessenMeasure hN ha) := by
  rw [normalizedJessenMeasure, normalizedJessenMeasure, lastIndex_shiftedCoefficients,
    jessenMeasure_shiftedCoefficients hN ha, Measure.map_smul]

end Dubon2026
