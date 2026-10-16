import Dubon2026.OriginalFullIdeleCompletionH2
import Dubon2026.OriginalCompletionCarryInvariant

/-! # The normalized original completion invariant on full ideles

Compose the literal full-idele localization with the existing continuous
comparison, ambient inflation and normalized local invariant. Its value
on principal classes is the existing global completion invariant. This
is the exact principal-kernel comparison needed to descend the proved
odd-primary sum toward DUB-17's normalized full-order class invariant.
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
  (Ω : Type) [Field Ω]
  [Algebra (v.adicCompletion K) Ω] [Algebra (w.adicCompletion L) Ω]
  [IsScalarTower (v.adicCompletion K) (w.adicCompletion L) Ω]
  [IsGalois (v.adicCompletion K) Ω] [IsSepClosed Ω]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) Ω)]

/-- The existing normalized local invariant composed with the actual original full-idele localization. -/
def originalFullIdeleCompletionInvariant :
    groupCohomology (originalFullIdeleRep K L) 2 →+ AddCircle (1 : ℚ) := by
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) (w.adicCompletion L)) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) (w.adicCompletion L)) := ⟨rfl⟩
  exact (localFieldContinuousH2InvariantEquiv (v.adicCompletion K) Ω).toAddMonoidHom.comp
    ((continuousGaloisUnitBaseChangeH2 (v.adicCompletion K) (v.adicCompletion K)
      (w.adicCompletion L) Ω).toAddMonoidHom.comp
      ((continuousDiscreteH2Equiv
        (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) (w.adicCompletion L))
        (discreteGaloisUnitAction_continuous (K := v.adicCompletion K)
          (Ω := w.adicCompletion L))).symm.toAddMonoidHom.comp
          (originalFullIdeleCompletionH2 K L v w).toAddMonoidHom))

/-- On the actual principal image the normalized full-idele invariant is precisely the original global completion invariant. -/
theorem originalFullIdeleCompletionInvariant_principal
    (x : groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) :
    originalFullIdeleCompletionInvariant K L v w Ω
      ((groupCohomology.functor ℤ Gal(L/K) 2).map (originalFullPrincipalRepHom K L) x) =
      originalGlobalCompletionInvariant K L v w Ω x := by
  unfold originalFullIdeleCompletionInvariant originalGlobalCompletionInvariant
  simp only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe]
  rw [originalFullIdeleCompletionH2_principal]
  rfl

/-- Actual local vanishing forces the normalized full-idele completion invariant to vanish. -/
theorem originalFullIdeleCompletionInvariant_eq_zero_of_adic
    (x : groupCohomology (originalFullIdeleRep K L) 2)
    (hx : originalFullIdeleAdicH2 K L w x = 0) :
    originalFullIdeleCompletionInvariant K L v w Ω x = 0 := by
  unfold originalFullIdeleCompletionInvariant
  simp only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe]
  rw [originalFullIdeleCompletionH2_eq_zero_of_adic K L v w x hx]
  simp only [map_zero]

end
end Dubon2026
