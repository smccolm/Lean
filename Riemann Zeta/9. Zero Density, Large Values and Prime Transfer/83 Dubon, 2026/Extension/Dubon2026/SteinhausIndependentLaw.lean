import Dubon2026.SteinhausLaw
import Mathlib.Probability.Independence.Basic

/-! # Transfer from arbitrary independent unit-circle variables to the actual Haar sum -/

namespace Dubon2026

open MeasureTheory ProbabilityTheory

noncomputable section

/-- The probability law of a uniform complex unit-circle point. -/
def uniformSteinhausLaw : Measure ℂ :=
  AddCircle.haarAddCircle.map (fun z : UnitAddCircle => fourier 1 z)

instance uniformSteinhausLaw_isProbabilityMeasure : IsProbabilityMeasure uniformSteinhausLaw :=
  Measure.isProbabilityMeasure_map (fourier (T := (1 : ℝ)) 1).continuous.measurable.aemeasurable

theorem steinhausLaw_eq_map_pi {κ : Type*} [Fintype κ] (c : κ → ℝ) :
    steinhausLaw c = (Measure.pi (fun _ : κ => uniformSteinhausLaw)).map
      (fun w : κ → ℂ => ∑ i, (c i : ℂ) * w i) := by
  have hp := Measure.pi_map_pi (μ := fun _ : κ => AddCircle.haarAddCircle)
    (f := fun _ : κ => fun z : UnitAddCircle => fourier 1 z)
    (fun _ => (fourier (T := (1 : ℝ)) 1).continuous.measurable.aemeasurable)
  unfold uniformSteinhausLaw
  rw [← hp, Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

theorem independent_steinhaus_sum_law {Ω κ : Type*} [MeasurableSpace Ω] [Fintype κ]
    {P : Measure Ω} [IsProbabilityMeasure P] (Z : κ → Ω → ℂ)
    (hZ : ∀ i, Measurable (Z i)) (hind : iIndepFun Z P)
    (hlaw : ∀ i, P.map (Z i) = uniformSteinhausLaw) (c : κ → ℝ) :
    P.map (fun ω => ∑ i, (c i : ℂ) * Z i ω) = steinhausLaw c := by
  rw [steinhausLaw_eq_map_pi]
  have hjoint := iIndepFun.map_fun_eq_pi_map (fun i => (hZ i).aemeasurable) hind
  calc
    P.map (fun ω => ∑ i, (c i : ℂ) * Z i ω) =
        (P.map (fun ω i => Z i ω)).map (fun w : κ → ℂ => ∑ i, (c i : ℂ) * w i) := by
      rw [Measure.map_map (by fun_prop) (measurable_pi_lambda _ hZ)]
      rfl
    _ = (Measure.pi (fun _ : κ => uniformSteinhausLaw)).map
        (fun w : κ → ℂ => ∑ i, (c i : ℂ) * w i) := by
      rw [hjoint]
      simp_rw [hlaw]

end

end Dubon2026
