import Dubon2026.OriginalUniversalLocalRestrictions
import Dubon2026.ArithmeticRelativePrimeCompletionComparison
import Dubon2026.OriginalFiniteCompletionLocalClass

/-! # Global restrictions in the original finite-completion normalization

Use the proved prime-coordinate realization and finite completion transport
to consume any supplied normalized original local class. This preserves one
global class across all original primes, compatible closures and normalized
finite-completion classes, as required by DUB-17's local compatibility input.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [-instance] UniformSpace.Completion.instSMul
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2
attribute [local instance] originalCompletionCarryAlgebra originalCompletionCarryFinite
  originalCompletionCarryGalois originalCompletionCarryValuation originalCompletionCarryLocalField

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- The fixed original global class restricts to every normalized finite-completion class through the actual completion/decomposition and local-to-class maps; this proposition alone asserts no compatibility. -/
def OriginalCompletionClassRestrictions
    (u : groupCohomology (originalIdeleClassRep K L) 2) : Prop :=
    ∀ (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
      (w : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
      (Ω : Type) [Field Ω]
      [Algebra (v.adicCompletion K) Ω] [Algebra (w.adicCompletion L) Ω]
      [IsScalarTower (v.adicCompletion K) (w.adicCompletion L) Ω]
      [IsGalois (v.adicCompletion K) Ω] [IsSepClosed Ω]
      [TopologicalSpace (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) Ω)]
      [DiscreteTopology (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) Ω)],
      letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) (w.adicCompletion L)) := ⊥
      letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) (w.adicCompletion L)) := ⟨rfl⟩
      ∀ y : GaloisUnitContinuousH2 (K := v.adicCompletion K) (Ω := w.adicCompletion L),
        localFieldContinuousH2InvariantEquiv (v.adicCompletion K) Ω
          (continuousGaloisUnitBaseChangeH2 (v.adicCompletion K) (v.adicCompletion K)
            (w.adicCompletion L) Ω y) =
          (↑((1 : ℚ) / Module.finrank (v.adicCompletion K) (w.adicCompletion L)) : AddCircle (1 : ℚ)) →
        (groupCohomology.map (OriginalFiniteDecompositionGroup K L w).subtype
          (𝟙 (Rep.res (OriginalFiniteDecompositionGroup K L w).subtype
            (originalIdeleClassRep K L))) 2).hom u =
          (groupCohomology.functor ℤ (OriginalFiniteDecompositionGroup K L w) 2).map
            ((Rep.resFunctor (OriginalFiniteDecompositionGroup K L w).subtype).map
              (originalFullClassRepHom K L))
            ((groupCohomology.functor ℤ (OriginalFiniteDecompositionGroup K L w) 2).map
              (originalIdeleSingleFiniteRepHom K L w) (originalFiniteCompletionLocalClass K L v w y))

/-- Canonical prime realization upgrades the common global class to compatibility with every supplied normalized original finite-completion class and every compatible closure. -/
theorem originalIdeleClass_exists_completion_local_restrictions
    (primeInvariant : IsDedekindDomain.HeightOneSpectrum (𝓞 K) →
      groupCohomology (originalFullIdeleRep K L) 2 →+ AddCircle (1 : ℚ))
    (hr : OriginalPrimeInvariantRealization K L primeInvariant)
    (hc : OriginalUniversalNormalizedLocalRestrictions K L
      (fun w => primeInvariant (originalFinitePrimeBelow K L w))) :
    ∃ u : groupCohomology (originalIdeleClassRep K L) 2,
      addOrderOf u = Module.finrank K L ∧ OriginalCompletionClassRestrictions K L u := by
  obtain ⟨u, hu, hl⟩ := hc
  refine ⟨u, hu, ?_⟩
  intro v w hw Ω _ _ _ _ _ _ _ _
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) (w.adicCompletion L)) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) (w.adicCompletion L)) := ⟨rfl⟩
  dsimp only
  intro y hy
  letI : Fintype (Gal(L/K) ⧸ OriginalFiniteDecompositionGroup K L w) := Fintype.ofFinite _
  let z := originalFiniteCompletionLocalClass K L v w y
  let x := originalSinglePrimeIdeleH2Lift K L w z
  have hn : primeInvariant (originalFinitePrimeBelow K L w) x =
      (↑((1 : ℚ) / Nat.card (OriginalFiniteDecompositionGroup K L w)) : AddCircle (1 : ℚ)) := by
    have hb := congrArg (fun v => primeInvariant v x) (originalFinitePrimeBelow_eq_of_liesOver K L v w)
    have hi := originalFiniteCompletionLocalClass_trace_invariant K L v w Ω y
    have hd := congrArg (fun n : ℕ => (↑((1 : ℚ) / n) : AddCircle (1 : ℚ)))
      (originalAdicBaseChange_finrank_eq_decomposition_card K L v w)
    exact hb.trans ((hr v w Ω x).trans (hi.trans (hy.trans hd)))
  exact (hl w).2 z hn

end
end Dubon2026
