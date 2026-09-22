import TaoTrudgianYang2025.ZetaCutoffDerivatives
import Mathlib.Data.Nat.Choose.Sum

/-!
# Uniform jets of smooth transitions and controlled-width cutoffs

One fixed smooth transition supplies all varying interval cutoffs.
Its finite derivative budget is chosen before the interval endpoints
and transition width. No minimum distance from the integer lattice is used.
-/

noncomputable section

open Set Filter
open scoped ContDiff BigOperators

namespace TaoTrudgianYang2025

theorem smoothTransition_finite_jet_bound (Q : ℕ) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ x : ℝ, ∀ j ≤ Q,
      |iteratedDeriv j Real.smoothTransition x| ≤ M := by
  let B : ℝ → ℝ := fun x =>
    ∑ j ∈ Finset.range (Q+1), |iteratedDeriv j Real.smoothTransition x|
  have hB : Continuous B := continuous_finsetSum _ fun j _ =>
    (Real.smoothTransition.contDiff.continuous_iteratedDeriv' j).abs
  obtain ⟨M,hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (0 : ℝ) 1) hB.continuousOn
  refine ⟨max M 1,le_max_right _ _,?_⟩
  intro x j hj
  by_cases hx : x ∈ Icc (0 : ℝ) 1
  · have hb : |iteratedDeriv j Real.smoothTransition x| ≤ B x :=
      Finset.single_le_sum (fun k _ => abs_nonneg (iteratedDeriv k Real.smoothTransition x))
        (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hj))
    exact hb.trans ((le_abs_self _).trans ((hM x hx).trans (le_max_left _ _)))
  · by_cases hj₀ : j = 0
    · subst j
      simpa only [iteratedDeriv_zero,abs_of_nonneg (Real.smoothTransition.nonneg x)] using
        (Real.smoothTransition.le_one x).trans (le_max_right M 1)
    · have hz : iteratedDeriv j Real.smoothTransition x = 0 :=
        Function.notMem_support.mp (fun h => hx
          (support_iteratedDeriv_smoothTransition (Nat.pos_of_ne_zero hj₀) h))
      rw [hz,abs_zero]
      exact zero_le_one.trans (le_max_right _ _)

def modelPhaseBufferedCutoff (l r η u : ℝ) : ℝ :=
  Real.smoothTransition ((u-l)/η-1) *
    Real.smoothTransition ((r-u)/η-1)

theorem modelPhaseBufferedCutoff_nonneg (l r η u : ℝ) :
    0 ≤ modelPhaseBufferedCutoff l r η u :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

theorem modelPhaseBufferedCutoff_le_one (l r η u : ℝ) :
    modelPhaseBufferedCutoff l r η u ≤ 1 := by
  exact (mul_le_mul (Real.smoothTransition.le_one _)
    (Real.smoothTransition.le_one _) (Real.smoothTransition.nonneg _)
    zero_le_one).trans_eq (one_mul 1)

theorem modelPhaseBufferedCutoff_contDiff (l r η : ℝ) :
    ContDiff ℝ ∞ (modelPhaseBufferedCutoff l r η) :=
  (Real.smoothTransition.contDiff.comp (by fun_prop)).mul
    (Real.smoothTransition.contDiff.comp (by fun_prop))

theorem modelPhaseBufferedCutoff_zero_left {l r η u : ℝ}
    (hη : 0 < η) (hu : u ≤ l+η) :
    modelPhaseBufferedCutoff l r η u = 0 := by
  unfold modelPhaseBufferedCutoff
  rw [Real.smoothTransition.zero_of_nonpos
    (show (u-l)/η-1 ≤ 0 by
      have h := (div_le_one hη).mpr (show u-l ≤ η by linarith)
      linarith),zero_mul]

theorem modelPhaseBufferedCutoff_zero_right {l r η u : ℝ}
    (hη : 0 < η) (hu : r-η ≤ u) :
    modelPhaseBufferedCutoff l r η u = 0 := by
  unfold modelPhaseBufferedCutoff
  rw [Real.smoothTransition.zero_of_nonpos
    (show (r-u)/η-1 ≤ 0 by
      have h := (div_le_one hη).mpr (show r-u ≤ η by linarith)
      linarith),mul_zero]

theorem modelPhaseBufferedCutoff_one {l r η u : ℝ}
    (hη : 0 < η) (hl : l+2*η ≤ u) (hr : u ≤ r-2*η) :
    modelPhaseBufferedCutoff l r η u = 1 := by
  unfold modelPhaseBufferedCutoff
  rw [Real.smoothTransition.one_of_one_le
      (show 1 ≤ (u-l)/η-1 by
        have h := (le_div_iff₀ hη).mpr (show 2*η ≤ u-l by linarith)
        linarith),
    Real.smoothTransition.one_of_one_le
      (show 1 ≤ (r-u)/η-1 by
        have h := (le_div_iff₀ hη).mpr (show 2*η ≤ r-u by linarith)
        linarith),one_mul]

theorem modelPhaseBufferedCutoff_tsupport {l r η : ℝ} (hη : 0 < η) :
    tsupport (modelPhaseBufferedCutoff l r η) ⊆ Icc (l+η) (r-η) := by
  apply closure_minimal _ isClosed_Icc
  intro u hu
  constructor
  · by_contra h
    exact hu (modelPhaseBufferedCutoff_zero_left hη (le_of_not_ge h))
  · by_contra h
    exact hu (modelPhaseBufferedCutoff_zero_right hη (le_of_not_ge h))

theorem modelPhaseBufferedCutoff_hasCompactSupport {l r η : ℝ} (hη : 0 < η) :
    HasCompactSupport (modelPhaseBufferedCutoff l r η) :=
  isCompact_Icc.of_isClosed_subset isClosed_closure (modelPhaseBufferedCutoff_tsupport hη)

theorem modelPhaseBufferedCutoff_tsupport_model {l r η : ℝ}
    (hη : 0 < η) (hl : 1 ≤ l) (hr : r ≤ 2) :
    tsupport (modelPhaseBufferedCutoff l r η) ⊆ Ioo (1 : ℝ) 2 := by
  intro u hu
  have h := modelPhaseBufferedCutoff_tsupport hη hu
  constructor <;> linarith [h.1,h.2]

end TaoTrudgianYang2025
