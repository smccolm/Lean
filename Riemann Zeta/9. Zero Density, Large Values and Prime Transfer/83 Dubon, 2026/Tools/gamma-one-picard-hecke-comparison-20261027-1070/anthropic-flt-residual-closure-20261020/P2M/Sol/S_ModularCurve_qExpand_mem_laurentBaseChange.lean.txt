import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_X0
import Theorems.Thm_ModularCurve_coeffEmb_qExpand
import P2M.Util
namespace P2MW.S_ModularCurve_qExpand_mem_laurentBaseChange

open ModularCurve IntermediateField HahnSeries

theorem solution {L : Type*} [Field L] [Algebra ℚ L] {F₀ : IntermediateField ℚ (LaurentSeries ℚ)} (n : ℕ) [NeZero n] {F₁ : IntermediateField ℚ (LaurentSeries ℚ)} (hF : ∀ y ∈ F₀, ModularCurve.qExpand ℚ n y ∈ F₁) {x : LaurentSeries L} (hx : x ∈ ModularCurve.laurentBaseChange L F₀) : ModularCurve.qExpand L n x ∈ ModularCurve.laurentBaseChange L F₁ :=
  by
  rw [mem_laurentBaseChange_iff] at hx
  induction hx using Subfield.closure_induction with
  | mem y hy =>
      rcases hy with ⟨a, rfl⟩ | ⟨z, hz, rfl⟩
      · rw [algebraMap_laurentSeries_eq_single, qExpand_single, mul_zero,
          ← algebraMap_laurentSeries_eq_single]
        exact (laurentBaseChange L F₁).algebraMap_mem _
      · rw [← coeffEmb_qExpand]
        exact coeffEmb_mem_laurentBaseChange L (hF z hz)
  | one => simp
  | add x y _ _ hx hy => simpa using add_mem hx hy
  | neg x _ hx => simpa using neg_mem hx
  | inv x _ hx => simpa using inv_mem hx
  | mul x y _ _ hx hy => simpa using mul_mem hx hy
