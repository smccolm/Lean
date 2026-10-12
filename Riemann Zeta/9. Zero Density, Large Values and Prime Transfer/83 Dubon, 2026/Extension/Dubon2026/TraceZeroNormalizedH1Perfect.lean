import Dubon2026.TraceZeroCharacterDualH1Comparison
import Mathlib.LinearAlgebra.PerfectPairing.Basic

/-! # Transfer actual coefficient duality to the original deformation cup

This bridge uses the original matrix trace, continuous H1 quotients and H2
normalization. Its explicit coefficient-duality and H1-finiteness inputs will
be discharged by the proved local arithmetic theorems, closing that precise
dependency of DUB-17's local deformation pairing.
-/

namespace Dubon2026
noncomputable section
open Matrix

attribute [local instance] characterDualSequenceContinuousSMul

variable {G ι k : Type} [Group G] [Fintype ι] [DecidableEq ι] [Field k] [Finite k]
  [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
  (ρ : G →* GeneralLinearGroup ι k) (hρ : Continuous ρ)
  (χ : G →* k) (hχ : Continuous χ)
  (σ : ContinuousRepresentationH2 (coefficientCharacterRep χ)
    (coefficientCharacterAction_continuous χ hχ) ≃ₗ[k] k)

/-- Normalize the original deformation trace cup by the specified actual
scalar coordinate on its original character-valued H2. -/
def matrixTraceZeroNormalizedH1Cup :
    ContinuousRepresentationH1 (matrixTraceZeroCharacterRep ρ χ)
      (matrixTraceZeroCharacterAction_continuous ρ hρ χ hχ) →ₗ[k]
      ContinuousTraceZeroAdjointH1 ρ hρ →ₗ[k] k :=
  (matrixTraceZeroCharacterH1Cup ρ hρ χ hχ).compr₂ σ.toLinearMap

variable (hn : (Fintype.card ι : k) ≠ 0)
  [TopologicalSpace (characterDualCoefficientRep (matrixTraceZeroAdjointRep ρ) χ)]
  [DiscreteTopology (characterDualCoefficientRep (matrixTraceZeroAdjointRep ρ) χ)]

/-- The exact normalization preserves the original cup's negative swapped
comparison, rather than changing its matrix arguments or orientation. -/
theorem matrixTraceZeroNormalizedH1Cup_dual
    (x : ContinuousRepresentationH1 (matrixTraceZeroCharacterRep ρ χ)
      (matrixTraceZeroCharacterAction_continuous ρ hρ χ hχ))
    (y : ContinuousTraceZeroAdjointH1 ρ hρ) :
    matrixTraceZeroNormalizedH1Cup ρ hρ χ hχ σ x y =
      -((continuousCharacterDualH1Cup (matrixTraceZeroAdjointRep ρ) χ hχ
        (matrixTraceZeroAdjointAction_continuous ρ hρ)).compr₂ σ.toLinearMap)
        (continuousTraceZeroH1GeneralEquiv ρ hρ y)
        (matrixTraceZeroCharacterDualH1Equiv hn ρ hρ χ hχ x) := by
  exact (congrArg σ (matrixTraceZeroCharacterH1Cup_dual hn ρ hρ χ hχ x y)).trans (map_neg σ _)

variable [Module.Finite k (ContinuousTraceZeroAdjointH1 ρ hρ)]

include hn in
/-- Proved coefficient-dual perfectness and actual deformation H1 finiteness
imply perfectness of the original normalized matrix trace cup. -/
theorem matrixTraceZeroNormalizedH1Cup_isPerfPair
    (hdual : ((continuousCharacterDualH1Cup (matrixTraceZeroAdjointRep ρ) χ hχ
      (matrixTraceZeroAdjointAction_continuous ρ hρ)).compr₂ σ.toLinearMap).IsPerfPair) :
    (matrixTraceZeroNormalizedH1Cup ρ hρ χ hχ σ).IsPerfPair := by
  apply LinearMap.IsPerfPair.of_injective'
  · intro x y h
    apply (matrixTraceZeroCharacterDualH1Equiv hn ρ hρ χ hχ).injective
    apply hdual.bijective_right.injective
    apply LinearMap.ext
    intro z
    obtain ⟨z, rfl⟩ := (continuousTraceZeroH1GeneralEquiv ρ hρ).surjective z
    apply neg_injective
    exact (matrixTraceZeroNormalizedH1Cup_dual ρ hρ χ hχ σ hn x z).symm.trans
      ((DFunLike.congr_fun h z).trans (matrixTraceZeroNormalizedH1Cup_dual ρ hρ χ hχ σ hn y z))
  · intro x y h
    apply (continuousTraceZeroH1GeneralEquiv ρ hρ).injective
    apply hdual.bijective_left.injective
    apply LinearMap.ext
    intro z
    obtain ⟨z, rfl⟩ := (matrixTraceZeroCharacterDualH1Equiv hn ρ hρ χ hχ).surjective z
    apply neg_injective
    exact (matrixTraceZeroNormalizedH1Cup_dual ρ hρ χ hχ σ hn z x).symm.trans
      ((DFunLike.congr_fun h z).trans (matrixTraceZeroNormalizedH1Cup_dual ρ hρ χ hχ σ hn z y))

end
end Dubon2026
