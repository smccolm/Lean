import Dubon2026.SourceOriginalEvaluationClosedMap
import Dubon2026.SourceOriginalUnramifiedEvaluationChart
import Dubon2026.SourceOriginalFiniteRamification
import Dubon2026.SourceOriginalJDegreeSums

/-! DUB-17/18 -> geometric cell dissection -> ordinary sheets.
The actual original j map is a covering off its two proved exceptional
values. Its fiber cardinal is the already proved all-level j degree.
The generic external critical-point and finite-extension reconstructions
are unnecessary: consume the exact original ramification and degree results.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve Set
attribute [local instance] placeTopology
variable (N : ℕ) [NeZero N]
local notation "F" => modularFunctionFieldOver N ℂ

theorem isCoveringMapOn_original_j :
    IsCoveringMapOn
      (fun P : {P : Place ℂ F // jOver N ℂ ∈ P.toValuationSubring} =>
        originalPlaceEval N ℂ P.1 (jOver N ℂ)) ({0, 1728} : Set ℂ)ᶜ := by
  letI := place_t2Space N
  have hj : ∀ c : ℂ, jOver N ℂ ≠ algebraMap ℂ F c :=
    fun c h => transcendental_jOver N ℂ (h ▸ isAlgebraic_algebraMap c)
  apply (isClosedMap_original_regular_evaluation N hj).isCoveringMapOn_of_openPartialHomeomorph
  · intro b _
    have hfin := finite_original_regular_eval_fiber N (sub_ne_zero.mpr (hj b))
    exact (hfin.preimage Subtype.val_injective.injOn).subset fun P hP => ⟨P.2, hP⟩
  · intro P hP
    have hb : originalPlaceEval N ℂ P.1 (jOver N ℂ) ≠ 0 ∧
        originalPlaceEval N ℂ P.1 (jOver N ℂ) ≠ 1728 := by
      simpa only [mem_preimage, mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or] using hP
    have hm := (mem_originalPositiveFiber_iff_regular_eval N (sub_ne_zero.mpr (hj _)) P.1).mpr
      ⟨P.2, rfl⟩
    have ho := original_finite_j_fiber_order_one N P.1 _ hb.1 hb.2
      ((mem_originalPositiveFiber N (jOver N ℂ) _ P.1).mp hm)
    exact exists_original_unramified_evaluation_chart N hj P ho

theorem card_original_j_regular_fiber (b : ℂ) (hb0 : b ≠ 0) (hb1728 : b ≠ 1728) :
    Nat.card {P : Place ℂ F // jOver N ℂ ∈ P.toValuationSubring ∧
      originalPlaceEval N ℂ P (jOver N ℂ) = b} = SourceLevelProjective.dedekindPsi N := by
  classical
  let S := originalPositiveFiber N (jOver N ℂ) b
  have hne : jOver N ℂ - algebraMap ℂ F b ≠ 0 := by
    intro h
    exact transcendental_jOver N ℂ (sub_eq_zero.mp h ▸ isAlgebraic_algebraMap b)
  let e : {P : Place ℂ F // jOver N ℂ ∈ P.toValuationSubring ∧
      originalPlaceEval N ℂ P (jOver N ℂ) = b} ≃ S :=
    Equiv.subtypeEquivRight fun P => (mem_originalPositiveFiber_iff_regular_eval N hne P).symm
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe]
  have hs := sum_original_j_fiber_orders_finset N ℂ b S (mem_originalPositiveFiber N (jOver N ℂ) b)
  have hone : ∀ P ∈ S, P.ord (jOver N ℂ - algebraMap ℂ F b) = 1 := fun P hP =>
    original_finite_j_fiber_order_one N P b hb0 hb1728
      ((mem_originalPositiveFiber N (jOver N ℂ) b P).mp hP)
  rw [Finset.sum_congr rfl hone] at hs
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hs
  exact_mod_cast hs

end
end Dubon2026.SourceFunctionField.OriginalChart
