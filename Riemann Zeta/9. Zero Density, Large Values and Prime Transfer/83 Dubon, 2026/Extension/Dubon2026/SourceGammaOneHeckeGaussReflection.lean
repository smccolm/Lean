import Dubon2026.SourceReductionMapReflection
import Dubon2026.SourceGammaOneHeckeGauss

/-! DUB-17/18 -> original Gamma1 Tate Frobenius -> norm reduction for
integral fractions. The actual beta map preserves the original Gauss ring.
Primitive normalization now reflects integrality through this same map,
without a coefficientwise-integral representative or a degree hypothesis. -/
namespace Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction
noncomputable section
open CongruenceSubgroup SourceCurve
variable {L : Type*} [Field L] [Algebra ℚ L] (A : ValuationSubring L)
  (M d : ℕ) [NeZero d]
local notation "Γ" => Gamma1 M
local notation "Δ" => Gamma1 M ⊓ Gamma0 (d * M)
local notation "FF" => functionFieldOver Γ L

theorem heckeBeta_mem_gaussRing_iff (f : FF) :
    heckeBeta L M d f ∈ coefficientGaussRing Δ A ↔ f ∈ coefficientGaussRing Γ A := by
  exact (regularProlongation A Γ).map_mem_iff_of_preserves_integers
    (regularProlongation A Δ) (heckeBeta L M d)
    (fun f hf => heckeBeta_mem_gaussRing A M d ⟨f, hf⟩) f

end
end Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction
