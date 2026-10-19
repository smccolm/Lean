import Dubon2026.ArithmeticPrimeUnitDualConnecting
import Dubon2026.RationalTraceOriginalLocalAction

/-! The actual completion-group change of the finite local unit Hom.
This supplies all three terms of the dual connecting diagram needed for
DUB-17's original source-local/global-class comparison. -/
namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance 1100] Rep.hV1 Rep.hV2
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitFieldRationalAlgebra
  arithmeticOrbitCompletionNumberField arithmeticOrbitCompletionBaseAlgebra
  arithmeticOrbitCompletionValuation arithmeticOrbitCompletionTopology arithmeticOrbitCompletionLocalField
  arithmeticOrbitCompletionValuationExtension arithmeticOrbitCompletionUniformity arithmeticOrbitCompletionUniformAdd
  arithmeticOrbitCompletionTargetAlgebra arithmeticOrbitCompletionClosureAlgebra
  arithmeticOrbitCompletionGlobalAlgebra
  rationalOriginalCompletionTargetAlgebra rationalOriginalCompletionClosureAlgebra
  rationalOriginalCompletionClosureTower rationalOriginalCompletionGalois rationalArithmeticOriginalPrimeLiesOver
  originalAdicRelationCompletionAlgebra originalAdicLocalRelationGalois originalAdicLocalRelationCupFinite
  rationalArithmeticOriginalCompletion_closureTower rationalArithmeticOriginalFiniteGalois
  rationalTraceCompletionArithmeticGalois



variable (a : 𝓞 ℚ)
  (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
  (p : ℕ) (hp : p.Prime)

/-- Reindexing the original completion group gives exactly the finite
arithmetic restriction, before any coefficient representation is chosen. -/
theorem rationalArithmeticOriginalCompletion_reindex_restriction
    (g : Gal(rationalPrimeLocalClosure p hp / (rationalOriginalPrimePlace p hp).adicCompletion ℚ)) :
    AlgEquiv.restrictNormalHom F
      (rationalPrimeArithmeticRestriction a p hp ((rationalOriginalCompletionGaloisEquiv p hp).symm g)) =
    originalAdicCompletionGaloisInclusion ℚ F (rationalOriginalPrimePlace p hp)
      (rationalArithmeticOriginalPrime a p hp F)
      (AlgEquiv.restrictNormalHom ((rationalArithmeticOriginalPrime a p hp F).adicCompletion F) g) := by
  have h := rationalArithmeticOriginalCompletion_galois_restriction a p hp F
    ((rationalOriginalCompletionGaloisEquiv p hp).symm g)
  have hg : galoisBaseChangeRestriction ((rationalOriginalPrimePlace p hp).adicCompletion ℚ)
      (rationalPrimeLocalField p hp) ((rationalArithmeticOriginalPrime a p hp F).adicCompletion F)
      (rationalPrimeLocalClosure p hp) ((rationalOriginalCompletionGaloisEquiv p hp).symm g) =
      AlgEquiv.restrictNormalHom ((rationalArithmeticOriginalPrime a p hp F).adicCompletion F) g := by
    change AlgEquiv.restrictNormalHom ((rationalArithmeticOriginalPrime a p hp F).adicCompletion F)
      (rationalOriginalCompletionGaloisEquiv p hp ((rationalOriginalCompletionGaloisEquiv p hp).symm g)) = _
    rw [MulEquiv.apply_symm_apply]
  exact h.symm.trans (congrArg (originalAdicCompletionGaloisInclusion ℚ F (rationalOriginalPrimePlace p hp)
      (rationalArithmeticOriginalPrime a p hp F)) hg)

private theorem reindexedHomAction
    {G H V W : Type} [Group G] [Group H]
    [AddCommGroup V] [Module ℤ V] [AddCommGroup W] [Module ℤ W]
    (ρ : Representation ℤ G V) (ρ' : Representation ℤ H V)
    (τ : Representation ℤ G W) (τ' : Representation ℤ H W)
    (j : H →* G) (hρ : ∀ g x, ρ (j g) x = ρ' g x)
    (hτ : ∀ g x, τ (j g) x = τ' g x) (g : H) (f : V →ₗ[ℤ] W) :
    Representation.linHom ρ τ (j g) f = Representation.linHom ρ' τ' g f := by
  apply LinearMap.ext
  intro x
  change τ (j g) (f (ρ (j g)⁻¹ x)) = τ' g (f (ρ' g⁻¹ x))
  rw [← map_inv j g, hρ, hτ]

variable (B : Rep.{0} ℤ Gal(F/ℚ))

/-- The actual local Hom map retains the literal linear function while
changing from the prime-local to the original-completion group. -/
def rationalArithmeticOriginalCompletionHomMap :
    Rep.res (rationalOriginalCompletionGaloisEquiv p hp).symm.toMonoidHom
      (arithmeticPrimeRestrictedUnitHom a F B p hp) ⟶
      originalAdicLocalCoefficientUnitHom ℚ F (rationalOriginalPrimePlace p hp)
      (rationalArithmeticOriginalPrime a p hp F) (rationalPrimeLocalClosure p hp) B :=
  Rep.ofHom ⟨LinearMap.id, fun g => by
    apply LinearMap.ext
    intro f
    exact reindexedHomAction
      (B.ρ.comp ((AlgEquiv.restrictNormalHom F : rationalArithmeticGaloisGroup a →* Gal(F/ℚ)).comp
        (rationalPrimeArithmeticRestriction a p hp).toMonoidHom))
      (B.ρ.comp ((originalAdicCompletionGaloisInclusion ℚ F (rationalOriginalPrimePlace p hp)
      (rationalArithmeticOriginalPrime a p hp F)).comp
        (AlgEquiv.restrictNormalHom ((rationalArithmeticOriginalPrime a p hp F).adicCompletion F))))
      (Rep.ofAlgebraAutOnUnits (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp)).ρ
      (Rep.ofAlgebraAutOnUnits ((rationalOriginalPrimePlace p hp).adicCompletion ℚ)
        (rationalPrimeLocalClosure p hp)).ρ
      (rationalOriginalCompletionGaloisEquiv p hp).symm.toMonoidHom
      (fun u x => congrArg (fun v => B.ρ v x)
        (rationalArithmeticOriginalCompletion_reindex_restriction a F p hp u))
      (fun _ _ => rfl) g f⟩

end
end Dubon2026
