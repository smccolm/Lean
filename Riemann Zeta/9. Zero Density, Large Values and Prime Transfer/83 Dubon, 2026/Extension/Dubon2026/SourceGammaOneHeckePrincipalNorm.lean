import Dubon2026.SourceCurveCorrespondencePrincipalOrder
import Dubon2026.SourceGammaOneHeckePicard
import Dubon2026.SourceGammaOnePrincipalDivisors
import Dubon2026.SourceGammaOneHeckeNormEmbeddings

/-! DUB-17/18 -> original Gamma1 Tate Frobenius quadratic -> Hecke
specialization on torsion. The actual finite divisor correspondence sends
the original principal divisor to the principal divisor of the actual alpha
norm of beta. Native ramification, residue fields and norm order suffice. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open SourceCurve ConstantField
attribute [local instance] HeckeNorm.alphaAlgebra HeckeNorm.alphaModule
variable (L : Type*) [Field L] [Algebra ℚ L] [CharZero L] [IsAlgClosed L]
variable (M p : ℕ) [NeZero M] [Fact p.Prime]
local notation "FF" => laurentBaseChange L (x1FunctionField M)

theorem heckeDivisor_principal_norm (f : FF) (hf : f ≠ 0) :
    heckeDivisor L M p (principalDivisor M L f) =
      principalDivisor M L (Algebra.norm FF (heckeBeta L M p f)) := by
  ext P
  exact Divisor.geometricCorrespondence_order (heckeBeta L M p)
    (heckeAlpha L M p) (heckeBeta_finite L M p) (heckeAlpha_finite L M p)
    (gamma1_place_residue_bijective L M)
    (gamma1_hecke_place_residue_bijective L M (p * M))
    (principalDivisor M L f) f hf (fun _ => rfl) P

end
end Dubon2026.SourceFunctionField.GammaOne
