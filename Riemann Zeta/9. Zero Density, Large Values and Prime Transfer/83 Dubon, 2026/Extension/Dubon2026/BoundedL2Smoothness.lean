import Dubon2026.BoundedL2Differentiation
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.MeanValue

/-! # Smooth genuine L2 curves from proved bounded original jet families -/

namespace Dubon2026

noncomputable section
open MeasureTheory
open scoped ContDiff

/-- Uniform bounds on the actual pointwise derivative promote the original curve derivative to genuine L2 at every parameter. -/
theorem hasDerivAt_toLp_of_uniform_derivative_bound {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasure μ] (F D : ℝ → X → ℂ)
    (hF : ∀ t, MemLp (F t) 2 μ) (hD : ∀ t, MemLp (D t) 2 μ)
    (hd : ∀ t x, HasDerivAt (fun u : ℝ => F u x) (D t x) t)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ t x, ‖D t x‖ ≤ C) (t : ℝ) :
    HasDerivAt (fun u : ℝ => (hF u).toLp (F u)) ((hD t).toLp (D t)) t := by
  have hpoint (x : X) : HasDerivAt (fun u : ℝ => F (t + u) x) (D t x) 0 := by
    simpa using (hd t x).scomp_of_eq 0 ((hasDerivAt_id 0).const_add t) (by simp)
  have hinc (u : ℝ) (x : X) : ‖F (t + u) x - F (t + 0) x‖ ≤ C * |u| := by
    have hb := (convex_univ : Convex ℝ (Set.univ : Set ℝ)).norm_image_sub_le_of_norm_deriv_le
      (fun s _ => (hd s x).differentiableAt)
      (fun s _ => by rw [(hd s x).deriv]; exact hC s x)
      (Set.mem_univ (t + 0)) (Set.mem_univ (t + u))
    simpa only [Real.norm_eq_abs, add_sub_add_left_eq_sub, sub_zero] using hb
  have hz := hasDerivAt_toLp_of_bounded_difference_quotients (fun u => F (t + u)) (D t)
    (fun u => hF (t + u)) (hD t) hpoint (by positivity : 0 ≤ 2 * C)
    (fun u x => difference_quotient_error_bound (fun s => F (t + s) x) (D t x)
      hC0 (fun s => hinc s x) (hC t x) u)
  have ht := hz.scomp_of_eq t ((hasDerivAt_id t).sub_const t) (by simp)
  simpa only [Function.comp_def, id_eq, add_sub_cancel, one_smul] using ht

/-- Actual successive pointwise derivatives are measurable and square-integrable when each original jet has a proved uniform bound. -/
theorem memLp_bounded_jet_family {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasure μ] (J : ℕ → ℝ → X → ℂ)
    (hJ0 : ∀ t, AEStronglyMeasurable (J 0 t) μ)
    (hd : ∀ n t x, HasDerivAt (fun u : ℝ => J n u x) (J (n + 1) t x) t)
    (hB : ∀ n, ∃ C : ℝ, ∀ t x, ‖J n t x‖ ≤ C) :
    ∀ n t, MemLp (J n t) 2 μ := by
  have hm (n : ℕ) : ∀ t, AEStronglyMeasurable (J n t) μ := by
    induction n with
    | zero => exact hJ0
    | succ n ih =>
      intro t
      apply aestronglyMeasurable_pointwise_derivative (fun u => J n (t + u)) (J (n + 1) t)
        (fun u => ih (t + u))
      intro x
      simpa using (hd n t x).scomp_of_eq 0 ((hasDerivAt_id 0).const_add t) (by simp)
  intro n t
  obtain ⟨C, hC⟩ := hB n
  exact MemLp.of_bound (hm n t) C (ae_of_all μ (hC t))

/-- A proved hierarchy of original bounded pointwise jets makes the actual original L2 curve smooth to every order. -/
theorem contDiff_toLp_of_bounded_jet_family {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasure μ] (J : ℕ → ℝ → X → ℂ)
    (hJ : ∀ n t, MemLp (J n t) 2 μ)
    (hd : ∀ n t x, HasDerivAt (fun u : ℝ => J n u x) (J (n + 1) t x) t)
    (hB : ∀ n, ∃ C : ℝ, 0 ≤ C ∧ ∀ t x, ‖J n t x‖ ≤ C) :
    ContDiff ℝ ∞ (fun t : ℝ => (hJ 0 t).toLp (J 0 t)) := by
  let L := fun n t => (hJ n t).toLp (J n t)
  have hL (n : ℕ) (t : ℝ) : HasDerivAt (L n) (L (n + 1) t) t := by
    obtain ⟨C, hC0, hC⟩ := hB (n + 1)
    exact hasDerivAt_toLp_of_uniform_derivative_bound (J n) (J (n + 1))
      (hJ n) (hJ (n + 1)) (hd n) hC0 hC t
  have hdiff (n : ℕ) : Differentiable ℝ (L n) := fun t => (hL n t).differentiableAt
  have he (n : ℕ) : deriv (L n) = L (n + 1) := funext (fun t => (hL n t).deriv)
  have hall (m : ℕ) : ∀ n : ℕ, ContDiff ℝ m (L n) := by
    induction m with
    | zero => intro n; exact contDiff_zero.mpr (hdiff n).continuous
    | succ m ih =>
      intro n
      rw [Nat.cast_add, Nat.cast_one, contDiff_succ_iff_deriv, he]
      exact ⟨hdiff n, by simp, ih (n + 1)⟩
  exact contDiff_infty.mpr (fun m => hall m 0)

end
end Dubon2026
