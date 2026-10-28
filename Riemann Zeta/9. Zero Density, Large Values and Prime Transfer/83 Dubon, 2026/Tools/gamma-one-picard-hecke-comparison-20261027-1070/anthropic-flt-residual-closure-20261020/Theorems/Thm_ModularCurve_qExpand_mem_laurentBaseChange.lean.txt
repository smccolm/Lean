import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_X0
import P2M.Util
import P2M.Sol.S_ModularCurve_qExpand_mem_laurentBaseChange

theorem ModularCurve.qExpand_mem_laurentBaseChange {L : Type*} [Field L] [Algebra ℚ L] {F₀ : IntermediateField ℚ (LaurentSeries ℚ)} (n : ℕ) [NeZero n] {F₁ : IntermediateField ℚ (LaurentSeries ℚ)} (hF : ∀ y ∈ F₀, ModularCurve.qExpand ℚ n y ∈ F₁) {x : LaurentSeries L} (hx : x ∈ ModularCurve.laurentBaseChange L F₀) : ModularCurve.qExpand L n x ∈ ModularCurve.laurentBaseChange L F₁ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_qExpand_mem_laurentBaseChange.solution
