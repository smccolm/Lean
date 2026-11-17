import Dubon2026.SourceFiniteLinearTwistedKernel

/-! Exact original twisted-cohomology kernel detection supplied by the finite
subfield bounds, serving DUB-17/18's regular auxiliary-prime construction. -/
namespace Dubon2026.SourceDickson
noncomputable section
open Matrix

/-- Nonzero original twisted classes are detected on the joint original kernel
whenever the original character has a nontrivial squared value. -/
def HasOriginalSymmetricTwistedKernelDetection
    {G F : Type} [Group G] [Field F]
    [TopologicalSpace G] [TopologicalSpace F] [IsTopologicalRing F]
    (ρ : G →* GeneralLinearGroup (Fin 2) F) : Prop :=
  ∀ (B : Type) (_ : CommGroup B) (χ : G →* B) (ω : B →* F)
    (g : G), ω (χ g) ^ 2 ≠ 1 → ∀ n : ℕ,
    ∀ hA : Continuous (fun z : G × matrixTraceZeroSubmodule (Fin (n + 1)) F =>
      (matrixTraceZeroCharacterRep ((homogeneousSymmetricGL n).comp ρ) (ω.comp χ)).ρ z.1 z.2),
    ∀ c : continuousRepresentationCocyclesOne
      (matrixTraceZeroCharacterRep ((homogeneousSymmetricGL n).comp ρ) (ω.comp χ)),
    (Submodule.Quotient.mk c : ContinuousRepresentationH1
      (matrixTraceZeroCharacterRep ((homogeneousSymmetricGL n).comp ρ) (ω.comp χ)) hA) ≠ 0 →
    ∃ τ, ρ τ = 1 ∧ χ τ = 1 ∧ c.val τ ≠ 0

/-- The constructed finite subfield bounds supply the exact original detection
property; no finite-image H1-vanishing certificate is supplied. -/
theorem finite_linear_bounds_original_symmetric_twisted_kernel_detection
    (p : ℕ) [Fact p.Prime]
    {G F : Type} [Group G] [Field F]
    [TopologicalSpace G] [TopologicalSpace F] [IsTopologicalRing F]
    (j : F →+* K p) (ρ : G →* GeneralLinearGroup (Fin 2) F)
    (hp3 : 3 < p) (h : HasFiniteLinearSubfieldBounds p j ρ) :
    HasOriginalSymmetricTwistedKernelDetection ρ := by
  intro B hB χ ω g hg n hA c hc
  exact finite_linear_bounds_symmetricTwistedH1_exists_nonzero_joint_kernel
    p n j ρ χ ω hp3 h g hg hA c hc

end
end Dubon2026.SourceDickson
