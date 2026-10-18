import Dubon2026.RationalTraceFiniteCompletionAction
import Dubon2026.RationalOriginalCompletionGaloisEquiv
import Dubon2026.RationalPrimeTraceUnitCohomology

/-! Identify the descended coefficient and its unit Hom on the original
number-field completion's continuous Galois group. This retains the
literal matrix and unit values needed to transport the original Cartier
cocycles into DUB-17's constructed local relation family. -/
namespace Dubon2026
noncomputable section
open scoped NumberField

private theorem linearHom_action_of_restriction
    {G H V W : Type} [Group G] [Group H]
    [AddCommGroup V] [Module ℤ V] [AddCommGroup W] [Module ℤ W]
    (ρ : Representation ℤ G V) (ρ' : Representation ℤ H V)
    (τ : Representation ℤ G W) (τ' : Representation ℤ H W)
    (j : G →* H) (hρ : ∀ g x, ρ g x = ρ' (j g) x)
    (hτ : ∀ g x, τ g x = τ' (j g) x) (g : G) (f : V →ₗ[ℤ] W) :
    Representation.linHom ρ τ g f = Representation.linHom ρ' τ' (j g) f := by
  apply LinearMap.ext
  intro x
  change τ g (f (ρ g⁻¹ x)) = τ' (j g) (f (ρ' (j g)⁻¹ x))
  rw [hρ, map_inv, hτ]

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

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  (a : 𝓞 ℚ) (q : ℕ) [Fact q.Prime]
  (σ : rationalArithmeticGaloisGroup a →* Matrix.GeneralLinearGroup ι (ZMod q))
  (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
  (hker : ∀ u : rationalArithmeticGaloisGroup a,
    AlgEquiv.restrictNormalHom F u = 1 →
    ∀ x : rationalArithmeticTraceZeroIntegerRep a q σ,
      (rationalArithmeticTraceZeroIntegerRep a q σ).ρ u x = x)
  (p : ℕ) (hp : p.Prime)

/-- The original finite coefficient representation, retaining the same
trace-zero matrices and the native descended action. -/
abbrev rationalTraceOriginalFiniteRep : Rep.{0} ℤ Gal(F/ℚ) :=
  Rep.of (finiteStageCoefficientRepresentation (rationalArithmeticTraceZeroIntegerRep a q σ) F hker)

/-- On the original completion group the descended action is the literal
prime-local trace action through the proved continuous base equivalence. -/
theorem rationalTraceOriginalCompletion_action
    (g : Gal(rationalPrimeLocalClosure p hp / (rationalOriginalPrimePlace p hp).adicCompletion ℚ))
    (x : rationalArithmeticTraceZeroIntegerRep a q σ) :
    (rationalTraceOriginalFiniteRep a q σ F hker).ρ
      (originalAdicCompletionGaloisInclusion ℚ F (rationalOriginalPrimePlace p hp)
        (rationalArithmeticOriginalPrime a p hp F)
        (AlgEquiv.restrictNormalHom ((rationalArithmeticOriginalPrime a p hp F).adicCompletion F) g)) x =
      (rationalPrimeTraceZeroIntegerRep p hp q (σ.comp (rationalPrimeArithmeticRestriction a p hp))).ρ
        ((rationalOriginalCompletionGaloisEquiv p hp).symm g) x := by
  have h := rationalTraceFiniteCompletion_action a q σ F hker p hp
    ((rationalOriginalCompletionGaloisEquiv p hp).symm g) x
  have hg : galoisBaseChangeRestriction ((rationalOriginalPrimePlace p hp).adicCompletion ℚ)
      (rationalPrimeLocalField p hp) ((rationalArithmeticOriginalPrime a p hp F).adicCompletion F)
      (rationalPrimeLocalClosure p hp) ((rationalOriginalCompletionGaloisEquiv p hp).symm g) =
      AlgEquiv.restrictNormalHom ((rationalArithmeticOriginalPrime a p hp F).adicCompletion F) g := by
    change AlgEquiv.restrictNormalHom ((rationalArithmeticOriginalPrime a p hp F).adicCompletion F)
      (rationalOriginalCompletionGaloisEquiv p hp ((rationalOriginalCompletionGaloisEquiv p hp).symm g)) = _
    rw [MulEquiv.apply_symm_apply]
  rw [hg] at h
  exact h

/-- The same unit-valued linear map has exactly the same action in the
finite-relation Hom coefficient and the original prime-local Cartier Hom. -/
theorem rationalTraceOriginalCompletionHom_action
    (g : Gal(rationalPrimeLocalClosure p hp / (rationalOriginalPrimePlace p hp).adicCompletion ℚ))
    (f : rationalPrimeTraceUnitHomRep p hp q (σ.comp (rationalPrimeArithmeticRestriction a p hp))) :
    (originalAdicLocalCoefficientUnitHom ℚ F (rationalOriginalPrimePlace p hp)
      (rationalArithmeticOriginalPrime a p hp F) (rationalPrimeLocalClosure p hp)
      (rationalTraceOriginalFiniteRep a q σ F hker)).ρ g f =
    (rationalPrimeTraceUnitHomRep p hp q (σ.comp (rationalPrimeArithmeticRestriction a p hp))).ρ
      ((rationalOriginalCompletionGaloisEquiv p hp).symm g) f := by
  exact linearHom_action_of_restriction
    ((rationalTraceOriginalFiniteRep a q σ F hker).ρ.comp
      ((originalAdicCompletionGaloisInclusion ℚ F (rationalOriginalPrimePlace p hp)
        (rationalArithmeticOriginalPrime a p hp F)).comp
        (AlgEquiv.restrictNormalHom ((rationalArithmeticOriginalPrime a p hp F).adicCompletion F))))
    (rationalPrimeTraceZeroIntegerRep p hp q (σ.comp (rationalPrimeArithmeticRestriction a p hp))).ρ
    (Rep.ofAlgebraAutOnUnits ((rationalOriginalPrimePlace p hp).adicCompletion ℚ)
      (rationalPrimeLocalClosure p hp)).ρ
    (Rep.ofAlgebraAutOnUnits (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp)).ρ
    (rationalOriginalCompletionGaloisEquiv p hp).symm.toMonoidHom
    (rationalTraceOriginalCompletion_action a q σ F hker p hp) (fun _ _ => rfl) g f

end
end Dubon2026
