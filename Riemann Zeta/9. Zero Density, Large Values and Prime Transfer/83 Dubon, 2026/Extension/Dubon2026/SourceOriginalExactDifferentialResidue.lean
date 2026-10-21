import Dubon2026.SourceCurveExactDifferentialResidue
import Dubon2026.SourceOriginalLocalResidues
import Dubon2026.SourceOriginalIntegralDerivatives

/-! DUB-17/18 -> function-field Riemann--Roch -> global residue identity
-> local differential/residue compatibility. Exact differentials have zero
residue at every actual original place. The original field supplies every
local finiteness, separability, generation and rational-residue input.
The global residue theorem for arbitrary differentials remains required.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve KaehlerDifferential
variable (N : ℕ) [NeZero N] (L : Type*) [Field L] [Algebra ℚ L] [IsAlgClosed L]

theorem original_localResidue_exactDifferential
    (v : Place L (modularFunctionFieldOver N L)) (f : modularFunctionFieldOver N L) :
    (originalCanonicalLocalResidueData N L v).res
      (v.differentialCoeff (D L (modularFunctionFieldOver N L) f)) = 0 := by
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
  haveI := finite_original_place_differentials N L v
  haveI := original_place_residue_isAlgebraic N L v
  haveI := original_place_dCoordGenerates N L v
  haveI : Nontrivial Ω[modularFunctionFieldOver N L⁄L] :=
    Module.nontrivial_of_finrank_eq_succ (n := 0) (finrank_original_differentials N L)
  exact v.canonicalLocalResidueData_exactDifferential
    (original_place_residue_algebraMap_bijective N L v) (originalCanonicalLocalResidueData N L v) f

end
end Dubon2026.SourceFunctionField
