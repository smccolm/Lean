import Definitions.Def_ModularCurve_X0
import Theorems.Thm_ModularCurve_aeval_jq_eq_zero
import P2M.Util
namespace P2MW.S_ModularCurve_transcendental_jqN

open ModularCurve IntermediateField

noncomputable section

theorem solution (N : ℕ) [NeZero N] : Transcendental ℚ (jqN N) :=by
  refine transcendental_iff.mpr fun p hp => ?_
  refine ModularCurve.aeval_jq_eq_zero (p := p) (qExpand_injective N ?_)
  rw [map_zero]
  calc qExpand ℚ N (Polynomial.aeval jq p)
      = qExpandₐ N (Polynomial.aeval jq p) := rfl
    _ = Polynomial.aeval (qExpandₐ N jq) p := (Polynomial.aeval_algHom_apply _ _ _).symm
    _ = Polynomial.aeval (jqN N) p := rfl
    _ = 0 := hp

end
