import GafniTao.FordLemma63Torus

/-!
# Ford Lemma 6.3: weighted overlap on the phase torus

This is the measure-theoretic form of Ford's overlap argument.  It retains the
literal phase boxes and bounds their sum by the exact real constant `W`.
-/

open Finset Set MeasureTheory
open scoped BigOperators

namespace GafniTao

noncomputable section

theorem fordLemma63_sum_indicators_eq_card_mul
    (N k M : ℕ) (u t : ℝ) (α : UnitAddTorus (Fin k)) (F : ℝ) :
    (∑ n ∈ Finset.Ioc N (2 * N - 1),
      (fordLemma63TorusOmega k M n u t).indicator (fun _ => F) α) =
      ((fordLemma63TorusOmegaFiber N k M u t α).card : ℝ) * F := by
  classical
  unfold fordLemma63TorusOmegaFiber
  have hgen (s : Finset ℕ) :
      (∑ n ∈ s,
        if α ∈ fordLemma63TorusOmega k M n u t then F else 0) =
        ((s.filter fun n =>
          α ∈ fordLemma63TorusOmega k M n u t).card : ℝ) * F := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
        by_cases hmem : α ∈ fordLemma63TorusOmega k M a u t
        · simp [Finset.filter_insert, ha, hmem, ih]
          ring
        · simp [Finset.filter_insert, ha, hmem, ih]
  simpa only [Set.indicator_apply] using hgen (Finset.Ioc N (2 * N - 1))

theorem fordLemma63_sum_indicators_le_W_mul
    {N k M : ℕ} {u t : ℝ}
    (hk : 2 ≤ k) (hM : 1 ≤ M) (hN : 1 ≤ N)
    (hu0 : 0 < u) (hu1 : u ≤ 1) (ht : 0 < t)
    (htN : t ≤ (N : ℝ) ^ k)
    (F : UnitAddTorus (Fin k) → ℝ) (hF : ∀ α, 0 ≤ F α)
    (α : UnitAddTorus (Fin k)) :
    (∑ n ∈ Finset.Ioc N (2 * N - 1),
      (fordLemma63TorusOmega k M n u t).indicator F α) ≤
      fordLemma63W N k M t * F α := by
  have heq :
      (∑ n ∈ Finset.Ioc N (2 * N - 1),
        (fordLemma63TorusOmega k M n u t).indicator F α) =
        ((fordLemma63TorusOmegaFiber N k M u t α).card : ℝ) * F α := by
    simpa only [Set.indicator_apply] using
      fordLemma63_sum_indicators_eq_card_mul N k M u t α (F α)
  rw [heq]
  exact mul_le_mul_of_nonneg_right
    (fordLemma63TorusOmegaFiber_card_le_W hk hM hN hu0 hu1 ht htN)
    (hF α)

theorem fordLemma63_sum_setIntegral_le_W_mul
    {N k M : ℕ} {u t : ℝ}
    (hk : 2 ≤ k) (hM : 1 ≤ M) (hN : 1 ≤ N)
    (hu0 : 0 < u) (hu1 : u ≤ 1) (ht : 0 < t)
    (htN : t ≤ (N : ℝ) ^ k)
    {F : UnitAddTorus (Fin k) → ℝ}
    (hFint : Integrable F
      (Measure.pi (fun _ : Fin k => AddCircle.haarAddCircle)))
    (hF : ∀ α, 0 ≤ F α) :
    (∑ n ∈ Finset.Ioc N (2 * N - 1),
      ∫ α in fordLemma63TorusOmega k M n u t, F α
        ∂Measure.pi (fun _ : Fin k => AddCircle.haarAddCircle)) ≤
      fordLemma63W N k M t *
        ∫ α : UnitAddTorus (Fin k), F α
          ∂Measure.pi (fun _ : Fin k => AddCircle.haarAddCircle) := by
  let μ : Measure (UnitAddTorus (Fin k)) :=
    Measure.pi (fun _ : Fin k => AddCircle.haarAddCircle)
  have hind (n : ℕ) : Integrable
      ((fordLemma63TorusOmega k M n u t).indicator F) μ :=
    hFint.indicator (measurableSet_fordLemma63TorusOmega k M n u t)
  have hsum : Integrable
      (fun α => ∑ n ∈ Finset.Ioc N (2 * N - 1),
        (fordLemma63TorusOmega k M n u t).indicator F α) μ :=
    integrable_finsetSum _ fun n _hn => hind n
  have hconst : Integrable (fun α => fordLemma63W N k M t * F α) μ :=
    hFint.const_mul _
  have hint := integral_mono hsum hconst
    (fordLemma63_sum_indicators_le_W_mul hk hM hN hu0 hu1 ht htN F hF)
  change
    (∑ n ∈ Finset.Ioc N (2 * N - 1),
      ∫ α in fordLemma63TorusOmega k M n u t, F α ∂μ) ≤
      fordLemma63W N k M t * ∫ α, F α ∂μ
  calc
    (∑ n ∈ Finset.Ioc N (2 * N - 1),
      ∫ α in fordLemma63TorusOmega k M n u t, F α ∂μ) =
        ∑ n ∈ Finset.Ioc N (2 * N - 1),
          ∫ α, (fordLemma63TorusOmega k M n u t).indicator F α ∂μ := by
      apply Finset.sum_congr rfl
      intro n _hn
      exact (integral_indicator
        (measurableSet_fordLemma63TorusOmega k M n u t)).symm
    _ =
        ∫ α, ∑ n ∈ Finset.Ioc N (2 * N - 1),
          (fordLemma63TorusOmega k M n u t).indicator F α ∂μ := by
      exact (integral_finsetSum _ (fun n _hn => hind n)).symm
    _ ≤ ∫ α, fordLemma63W N k M t * F α ∂μ := hint
    _ = fordLemma63W N k M t * ∫ α, F α ∂μ :=
      integral_const_mul (fordLemma63W N k M t) F

#print axioms fordLemma63_sum_indicators_eq_card_mul
#print axioms fordLemma63_sum_indicators_le_W_mul
#print axioms fordLemma63_sum_setIntegral_le_W_mul

end

end GafniTao
