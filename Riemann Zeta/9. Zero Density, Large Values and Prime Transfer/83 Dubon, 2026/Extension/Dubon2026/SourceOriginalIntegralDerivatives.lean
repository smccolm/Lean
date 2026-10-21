import Dubon2026.SourceCurveIntegralDerivatives
import Dubon2026.SourceOriginalLocalFinite
import Dubon2026.SourceOriginalResidueFinite
import Dubon2026.SourceOriginalLocalDifferentials

/-! DUB-17/18 -> canonical divisors and actual derivative orders.
The original valuation rings have finite local differential modules and
algebraic, hence characteristic-zero separable, residues. Thus their actual
uniformizer differentials generate integrally, and derivatives of integral
functions have nonnegative local differential order. No local unramifiedness,
local generation, finite-type or residue-separability input is assumed.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve KaehlerDifferential

variable (N : ℕ) [NeZero N] (L : Type*) [Field L] [Algebra ℚ L]

theorem span_original_integral_uniformizer_differential
    (v : Place L (modularFunctionFieldOver N L)) :
    Submodule.span v.toValuationSubring {D L v.toValuationSubring v.uniformizerSubring} = ⊤ := by
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
  haveI := finite_original_place_differentials N L v
  haveI := original_place_residue_isAlgebraic N L v
  exact v.span_integral_uniformizer_differential

theorem original_differentialCoeff_D_mem_of_mem
    (v : Place L (modularFunctionFieldOver N L)) {f : modularFunctionFieldOver N L}
    (hf : f ∈ v.toValuationSubring) :
    v.differentialCoeff (D L (modularFunctionFieldOver N L) f) ∈ v.toValuationSubring := by
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
  haveI := finite_original_place_differentials N L v
  haveI := original_place_residue_isAlgebraic N L v
  haveI := original_place_dCoordGenerates N L v
  haveI : Nontrivial Ω[modularFunctionFieldOver N L⁄L] :=
    Module.nontrivial_of_finrank_eq_succ (n := 0) (finrank_original_differentials N L)
  exact v.differentialCoeff_D_mem_of_mem hf

theorem original_ordDifferential_D_nonneg_of_mem
    (v : Place L (modularFunctionFieldOver N L)) {f : modularFunctionFieldOver N L}
    (hf : f ∈ v.toValuationSubring) :
    0 ≤ v.ordDifferential (D L (modularFunctionFieldOver N L) f) :=
  v.ord_nonneg_of_mem (original_differentialCoeff_D_mem_of_mem N L v hf)

end
end Dubon2026.SourceFunctionField
