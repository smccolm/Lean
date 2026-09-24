import TaoTrudgianYang2025.ZetaReflectionValueBands

/-! One actual common-shift mass represents the sum of localized convolutions. -/

noncomputable section
open Complex Filter MeasureTheory Set
open scoped Classical Interval
namespace TaoTrudgianYang2025

def reflectionShiftMass (W : Finset ℝ) (S : Finset ℕ) (T u : ℝ) : ℝ :=
  ∑ t ∈ W, (zetaMellinSourceWindow T t).indicator
    (fun v => ‖∑ n ∈ S, dirichletPhase n (t+v)‖) u

theorem reflectionShiftMass_nonneg (W : Finset ℝ) (S : Finset ℕ) (T u : ℝ) :
    0 ≤ reflectionShiftMass W S T u := by
  apply Finset.sum_nonneg
  intro t _
  by_cases hu : u ∈ zetaMellinSourceWindow T t
  · simp only [Set.indicator_of_mem hu]
    exact norm_nonneg _
  · simp only [Set.indicator_of_notMem hu,le_refl]

theorem reflectionShiftMass_eq_sum_filter (W : Finset ℝ) (S : Finset ℕ) (T u : ℝ) :
    reflectionShiftMass W S T u =
      ∑ t ∈ W.filter (fun t => t+u ∈ Icc (T/2) (3*T)),
        ‖∑ n ∈ S, dirichletPhase n (t+u)‖ := by
  rw [reflectionShiftMass,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro t _
  have he : u ∈ zetaMellinSourceWindow T t ↔ t+u ∈ Icc (T/2) (3*T) := by
    change (T/2-t ≤ u ∧ u ≤ 3*T-t) ↔ (T/2 ≤ t+u ∧ t+u ≤ 3*T)
    constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]
  by_cases hu : u ∈ zetaMellinSourceWindow T t
  · simp [hu,he.mp hu]
  · simp [hu,(not_iff_not.mpr he).mp hu]

theorem reflectionShiftMass_weighted_eq (W : Finset ℝ) (S : Finset ℕ) (T u : ℝ) :
    reflectionShiftMass W S T u/(1+|u|) =
      ∑ t ∈ W, (zetaMellinSourceWindow T t).indicator
        (fun v => ‖∑ n ∈ S, dirichletPhase n (t+v)‖/(1+|v|)) u := by
  rw [reflectionShiftMass,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro t _
  by_cases hu : u ∈ zetaMellinSourceWindow T t <;> simp [hu]

theorem integrable_reflectionShiftMass_weighted (W : Finset ℝ) (S : Finset ℕ)
    (hS : ∀ n ∈ S, n ≠ 0) (T : ℝ) :
    Integrable (fun u => reflectionShiftMass W S T u/(1+|u|)) := by
  simp_rw [reflectionShiftMass_weighted_eq]
  exact integrable_finsetSum W (fun t _ =>
    (integrableOn_zetaReflectionConvolution S hS T t).integrable_indicator measurableSet_Icc)

theorem sum_reflectionConvolution_eq_integral_shiftMass (W : Finset ℝ) (S : Finset ℕ)
    (hS : ∀ n ∈ S, n ≠ 0) (T : ℝ) :
    (∑ t ∈ W, zetaReflectionConvolution S T t) =
      ∫ u : ℝ, reflectionShiftMass W S T u/(1+|u|) := by
  simp_rw [reflectionShiftMass_weighted_eq]
  rw [integral_finsetSum W (fun t _ =>
    (integrableOn_zetaReflectionConvolution S hS T t).integrable_indicator measurableSet_Icc)]
  apply Finset.sum_congr rfl
  intro t _
  exact (integral_indicator measurableSet_Icc).symm

theorem zetaMellinSourceWindow_subset_commonShiftWindow {T t : ℝ}
    (hT : 0 < T) (ht : t ∈ Icc T (2*T)) :
    zetaMellinSourceWindow T t ⊆ Icc (-(2*T)) (2*T) := by
  intro u hu
  change T/2-t ≤ u ∧ u ≤ 3*T-t at hu
  constructor <;> linarith [hu.1,hu.2,ht.1,ht.2]

theorem reflectionShiftMass_eq_zero_outside {W : Finset ℝ} {S : Finset ℕ} {T u : ℝ}
    (hT : 0 < T) (hW : ∀ t ∈ W, t ∈ Icc T (2*T))
    (hu : u ∉ Icc (-(2*T)) (2*T)) : reflectionShiftMass W S T u = 0 := by
  apply Finset.sum_eq_zero
  intro t ht
  exact Set.indicator_of_notMem (fun h =>
    hu (zetaMellinSourceWindow_subset_commonShiftWindow hT (hW t ht) h)) _

theorem sum_reflectionConvolution_eq_commonShift_integral
    (W : Finset ℝ) (S : Finset ℕ) (hS : ∀ n ∈ S, n ≠ 0) {T : ℝ}
    (hT : 0 < T) (hW : ∀ t ∈ W, t ∈ Icc T (2*T)) :
    (∑ t ∈ W, zetaReflectionConvolution S T t) =
      ∫ u : ℝ in Icc (-(2*T)) (2*T), reflectionShiftMass W S T u/(1+|u|) := by
  rw [sum_reflectionConvolution_eq_integral_shiftMass W S hS T]
  rw [← integral_indicator measurableSet_Icc]
  apply integral_congr_ae
  filter_upwards with u
  by_cases hu : u ∈ Icc (-(2*T)) (2*T)
  · simp [hu]
  · simp [hu,reflectionShiftMass_eq_zero_outside hT hW hu]

end TaoTrudgianYang2025
