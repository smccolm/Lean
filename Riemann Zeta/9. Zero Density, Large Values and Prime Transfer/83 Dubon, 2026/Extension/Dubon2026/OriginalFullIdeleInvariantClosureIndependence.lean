import Dubon2026.LocalFieldFiniteInvariantClosureIndependence
import Dubon2026.OriginalFullIdeleCompletionInvariant

/-! # The original idele completion invariant is independent of the closure

Apply the proved closure independence to the same actual finite-completion
class. The comparison map is constructed in that theorem. This removes
the closure-choice premise from DUB-17's canonical prime-total assembly.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [-instance] UniformSpace.Completion.instSMul
attribute [local instance] originalCompletionCarryAlgebra originalCompletionCarryFinite
  originalCompletionCarryGalois originalCompletionCarryValuation originalCompletionCarryLocalField
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
  (w : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
  (Ω Ξ : Type) [Field Ω] [Field Ξ]
  [Algebra (v.adicCompletion K) Ω] [Algebra (w.adicCompletion L) Ω]
  [Algebra (v.adicCompletion K) Ξ] [Algebra (w.adicCompletion L) Ξ]
  [IsScalarTower (v.adicCompletion K) (w.adicCompletion L) Ω]
  [IsScalarTower (v.adicCompletion K) (w.adicCompletion L) Ξ]
  [IsGalois (v.adicCompletion K) Ω] [IsSepClosed Ω]
  [IsGalois (v.adicCompletion K) Ξ] [IsSepClosed Ξ]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) Ω)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) Ξ)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) Ξ)]

/-- The same actual full-idele completion class has the same normalized value in either chosen compatible separably closed Galois field. -/
theorem originalFullIdeleCompletionInvariant_closure_independent
    (x : groupCohomology (originalFullIdeleRep K L) 2) :
    originalFullIdeleCompletionInvariant K L v w Ξ x =
      originalFullIdeleCompletionInvariant K L v w Ω x := by
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) (w.adicCompletion L)) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) (w.adicCompletion L)) := ⟨rfl⟩
  exact localFieldFiniteInvariant_closure_independent
    (v.adicCompletion K) (w.adicCompletion L) Ω Ξ
    ((continuousDiscreteH2Equiv
      (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) (w.adicCompletion L))
      (discreteGaloisUnitAction_continuous (K := v.adicCompletion K)
        (Ω := w.adicCompletion L))).symm (originalFullIdeleCompletionH2 K L v w x))

end
end Dubon2026
