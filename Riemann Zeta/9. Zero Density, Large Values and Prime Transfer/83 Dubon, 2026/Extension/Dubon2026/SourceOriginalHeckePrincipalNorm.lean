import Dubon2026.SourceCurveCorrespondencePrincipalOrder
import Dubon2026.SourceOriginalHeckePicard
import Dubon2026.SourceOriginalPrincipalDivisors

/-! DUB-17/18 -> original Hecke reduction on torsion. The literal original
Hecke divisor correspondence sends div(f) to div(norm_alpha(beta(f))).
All finite-map and residue-field hypotheses are discharged by the existing
original modular-curve theorems. This supplies the exact principal divisor
needed by the proved integral norm reduction. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve
variable (L : Type*) [Field L] [Algebra ℚ L] [CharZero L] [IsAlgClosed L]
variable (N p : ℕ) [NeZero N] [NeZero p]
local notation "FF" => modularFunctionFieldOver N L

theorem originalHeckeDivisor_principal_norm (f : FF) (hf : f ≠ 0) :
    letI := algebraAlong (originalHeckeAlpha L N p)
    originalHeckeDivisor L N p (originalPrincipalDivisor N L f) =
      originalPrincipalDivisor N L (Algebra.norm FF (originalHeckeBeta L N p f)) := by
  letI := algebraAlong (originalHeckeAlpha L N p)
  ext P
  exact Divisor.geometricCorrespondence_order (originalHeckeBeta L N p)
    (originalHeckeAlpha L N p) (originalHeckeBeta_finite L N p)
    (originalHeckeAlpha_finite L N p) (original_place_residue_algebraMap_bijective N L)
    (original_place_residue_algebraMap_bijective (N * p) L)
    (originalPrincipalDivisor N L f) f hf (fun _ => rfl) P

end
end Dubon2026.SourceFunctionField
