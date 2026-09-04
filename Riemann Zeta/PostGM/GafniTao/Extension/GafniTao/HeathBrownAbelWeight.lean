import GafniTao.HeathBrownTaylorPhaseDerivative
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# The oscillatory weight in Heath-Brown's Abel step

We prove a Lipschitz estimate for `e(g_n(x))` and sum its consecutive
differences on the literal source interval `1 ≤ h ≤ H`.
-/

open Complex Finset Set
open scoped BigOperators

namespace GafniTao

noncomputable section

theorem norm_heathBrownPhase_sub_le (a b : ℝ) :
    ‖heathBrownPhase a - heathBrownPhase b‖ ≤
      2 * Real.pi * |a - b| := by
  have hfactor :
      heathBrownPhase a = heathBrownPhase b * heathBrownPhase (a - b) := by
    rw [← heathBrownPhase_add]
    congr 1
    ring
  rw [hfactor]
  have hmul :
      heathBrownPhase b * heathBrownPhase (a - b) - heathBrownPhase b =
        heathBrownPhase b * (heathBrownPhase (a - b) - 1) := by ring
  rw [hmul, norm_mul, norm_heathBrownPhase, one_mul]
  have h := Real.norm_exp_I_mul_ofReal_sub_one_le
    (x := 2 * Real.pi * (a - b))
  unfold heathBrownPhase
  have hexp :
      Complex.exp ((((2 * Real.pi * (a - b) : ℝ) : ℂ)) * Complex.I) =
        Complex.exp (Complex.I * (2 * Real.pi * (a - b) : ℝ)) := by
    congr 1
    push_cast
    ring
  rw [hexp]
  calc
    ‖Complex.exp (Complex.I * (2 * Real.pi * (a - b) : ℝ)) - 1‖ ≤
        ‖(2 * Real.pi * (a - b) : ℝ)‖ := h
    _ = 2 * Real.pi * |a - b| := by
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (2 : ℝ)),
        abs_of_nonneg Real.pi_pos.le]

/-- Mean-value estimate in the exact form used between consecutive integer
arguments of the Abel weight. -/
theorem norm_image_sub_le_of_hasDerivAt_bound
    {g : ℝ → ℝ} {a b C : ℝ} (hab : a ≤ b)
    (hg : ∀ x ∈ Set.Icc a b, HasDerivAt g (deriv g x) x)
    (hbound : ∀ x ∈ Set.Ico a b, ‖deriv g x‖ ≤ C) :
    ‖g b - g a‖ ≤ C * (b - a) := by
  have hwithin : ∀ x ∈ Set.Icc a b,
      HasDerivWithinAt g (deriv g x) (Set.Icc a b) x :=
    fun x hx => (hg x hx).hasDerivWithinAt
  exact norm_image_sub_le_of_norm_deriv_le_segment' hwithin hbound b
    (right_mem_Icc.mpr hab)

/-- One consecutive phase difference, with the source derivative scale. -/
theorem norm_heathBrownTaylorError_phase_succ_sub_le
    {k : ℕ} {f : ℝ → ℝ} {n C : ℝ} (j : ℕ)
    (hg : ∀ x ∈ Set.Icc (j : ℝ) (j + 1 : ℝ),
      HasDerivAt (fun y => heathBrownTaylorError k f n y)
        (deriv (fun y => heathBrownTaylorError k f n y) x) x)
    (hbound : ∀ x ∈ Set.Ico (j : ℝ) (j + 1 : ℝ),
      ‖deriv (fun y => heathBrownTaylorError k f n y) x‖ ≤ C) :
    ‖heathBrownPhase (heathBrownTaylorError k f n ((j + 1 : ℕ) : ℝ)) -
        heathBrownPhase (heathBrownTaylorError k f n j)‖ ≤
      2 * Real.pi * C := by
  have hgdiff := norm_image_sub_le_of_hasDerivAt_bound
    (g := fun y => heathBrownTaylorError k f n y)
    (a := (j : ℝ)) (b := (j + 1 : ℝ)) (C := C)
      (by exact_mod_cast Nat.le_succ j) hg hbound
  have hphase := norm_heathBrownPhase_sub_le
    (heathBrownTaylorError k f n ((j + 1 : ℕ) : ℝ))
    (heathBrownTaylorError k f n j)
  calc
    ‖heathBrownPhase (heathBrownTaylorError k f n ((j + 1 : ℕ) : ℝ)) -
        heathBrownPhase (heathBrownTaylorError k f n j)‖ ≤
      2 * Real.pi *
        |heathBrownTaylorError k f n ((j + 1 : ℕ) : ℝ) -
          heathBrownTaylorError k f n j| := hphase
    _ = 2 * Real.pi *
        ‖heathBrownTaylorError k f n ((j + 1 : ℕ) : ℝ) -
          heathBrownTaylorError k f n j‖ := by rw [Real.norm_eq_abs]
    _ ≤ 2 * Real.pi * C := by
      gcongr
      simpa using hgdiff

/-- Total variation over the genuine source edges `1→2,...,(H-1)→H`. -/
theorem sum_norm_heathBrownTaylorError_phase_succ_sub_le
    {k H : ℕ} {f : ℝ → ℝ} {n C : ℝ} (hC : 0 ≤ C)
    (hedge : ∀ j ∈ Finset.Ico 1 H,
      ‖heathBrownPhase (heathBrownTaylorError k f n ((j + 1 : ℕ) : ℝ)) -
          heathBrownPhase (heathBrownTaylorError k f n j)‖ ≤
        2 * Real.pi * C) :
    (∑ j ∈ Finset.Ico 1 H,
      ‖heathBrownPhase (heathBrownTaylorError k f n ((j + 1 : ℕ) : ℝ)) -
          heathBrownPhase (heathBrownTaylorError k f n j)‖) ≤
      (H : ℝ) * (2 * Real.pi * C) := by
  calc
    (∑ j ∈ Finset.Ico 1 H,
      ‖heathBrownPhase (heathBrownTaylorError k f n ((j + 1 : ℕ) : ℝ)) -
          heathBrownPhase (heathBrownTaylorError k f n j)‖) ≤
        ∑ _j ∈ Finset.Ico 1 H, 2 * Real.pi * C := by
      exact Finset.sum_le_sum fun j hj => hedge j hj
    _ = ((Finset.Ico 1 H).card : ℝ) * (2 * Real.pi * C) := by simp
    _ ≤ (H : ℝ) * (2 * Real.pi * C) := by
      have hcard : (Finset.Ico 1 H).card ≤ H := by simp
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)

#print axioms norm_heathBrownPhase_sub_le
#print axioms norm_image_sub_le_of_hasDerivAt_bound
#print axioms norm_heathBrownTaylorError_phase_succ_sub_le
#print axioms sum_norm_heathBrownTaylorError_phase_succ_sub_le

end

end GafniTao
