import Dubon2026.SourceArithmeticPadicCyclotomicReduction
import Dubon2026.SourceArithmeticWeightTwist

/-! DUB-17/18 -> arithmetic automorphy -> the actual fixed-determinant
deformation problem. Map the genuine p-adic cyclotomic character through
the injective native Witt scalar map, and identify its exact reduction
with the already proved original finite cyclotomic character. -/
namespace Dubon2026
noncomputable section
open scoped NumberField
open IsLocalRing
variable (p : ℕ) [Fact p.Prime]
  (K : Type) [Field K] [Finite K] [CharP K p]

/-- The actual p-adic cyclotomic character in the original Witt coefficient ring. -/
def sourceArithmeticWittCyclotomicCharacter (a : 𝓞 ℚ) :
    rationalArithmeticGaloisGroup a →* (WittVector p K)ˣ :=
  (Units.map (sourcePadicWittCoefficient p K).toMonoidHom).comp
    (sourceArithmeticPadicCyclotomicCharacter a p).toMonoidHom

theorem sourceArithmeticWittCyclotomicCharacter_reduction
    [NeZero p] [TopologicalSpace K]
    (a : 𝓞 ℚ) (hpa : (p : 𝓞 ℚ) ∣ a)
    (g : rationalArithmeticGaloisGroup a) :
    sourceResidualWittResidueEquiv p K
      (residue (WittVector p K) (sourceArithmeticWittCyclotomicCharacter p K a g : WittVector p K)) =
      (sourceArithmeticCyclotomicUnitCharacter (F := K) p a hpa g : K) := by
  change sourceResidualWittResidueEquiv p K
    (residue (WittVector p K) (sourcePadicWittCoefficient p K
      (sourceArithmeticPadicCyclotomicCharacter a p g : ℤ_[p]))) = _
  rw [sourcePadicWittCoefficient_residue,
    sourceArithmeticPadicCyclotomicCharacter_reduction a p hpa]
  rfl

end
end Dubon2026
