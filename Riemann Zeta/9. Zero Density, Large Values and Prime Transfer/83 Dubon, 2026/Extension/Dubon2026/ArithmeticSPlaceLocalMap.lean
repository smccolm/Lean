import Dubon2026.RationalExceptionalIndexedPrimes
import Dubon2026.RationalArithmeticOriginalCompletionRestriction
import Dubon2026.OriginalSPlaceRelationCompletionObstruction
import Dubon2026.ArithmeticSPlaceFiniteStages

/-! Evaluate the actual finite S-place coefficient at its original
exceptional prime and embed that completion in the fixed local closure.
Its equivariance is the coefficient input for removing DUB-17's finite
free correction after localization. -/
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
  arithmeticOrbitCompletionTargetAlgebra arithmeticOrbitCompletionClosureAlgebra arithmeticOrbitCompletionGlobalAlgebra
  rationalOriginalCompletionTargetAlgebra rationalOriginalCompletionClosureAlgebra
  rationalOriginalCompletionClosureTower rationalArithmeticOriginalPrimeLiesOver
  originalAdicRelationCompletionAlgebra originalAdicLocalRelationGalois originalAdicLocalRelationCupFinite
  rationalArithmeticOriginalCompletion_closureTower rationalArithmeticOriginalFiniteGalois
  rationalExceptionalIndexedPrimeLiesOver

private theorem localMapEquivariantOfRestriction {G H : Type} [Group G] [Group H]
    (A : Rep.{0} ℤ H) (D : Rep.{0} ℤ G) (π ψ : G →* H)
    (f : Rep.res π A ⟶ D) (m : A →ₗ[ℤ] D)
    (hm : ∀ x, f.hom x = m x) (hπ : ∀ g, π g = ψ g) (g : G) (x : A) :
    m (A.ρ (ψ g) x) = D.ρ g (m x) := by
  have h := Rep.hom_comm_apply f g x
  have he := congrArg (fun t => f.hom (A.ρ t x)) (hπ g)
  exact (hm _).symm.trans (he.symm.trans (h.trans (congrArg (D.ρ g) (hm x))))

variable (a : 𝓞 ℚ) (ha : a ≠ 0)
  (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
  (p : rationalArithmeticExceptionalPrimes a ha)

/-- The existing original idele localization restricted to the finite
S-place coefficient, before its completion is embedded into the closure. -/
def rationalArithmeticSPlaceCompletionMorphism :
    let v := rationalExceptionalIndexedBasePrime a ha p
    let w := rationalExceptionalIndexedUpperPrime a ha F p
    Rep.res (originalAdicCompletionGaloisInclusion ℚ F v w.val)
      (ArithmeticSPlaceFiniteStageRep ℚ (AlgebraicClosure ℚ) a ha F) ⟶
        Rep.ofAlgebraAutOnUnits (v.adicCompletion ℚ) (w.val.adicCompletion F) :=
  let v := rationalExceptionalIndexedBasePrime a ha p
  let w := rationalExceptionalIndexedUpperPrime a ha F p
  let ν := originalAdicCompletionGaloisInclusion ℚ F v w.val
  (Rep.resFunctor ν).map (originalSPlaceFullIdeleInclusion ℚ F
    (arithmeticSUnitFiniteStageSupport ℚ (AlgebraicClosure ℚ) a ha F)
    (originalExceptionalIntegerSupport_galoisStable F ℚ a ha)) ≫
      originalFullIdeleCompletionRepHom ℚ F v w.val

/-- The finite completion morphism retains the exact selected S-place unit. -/
theorem rationalArithmeticSPlaceCompletionMorphism_apply
    (x : ArithmeticSPlaceFiniteStageRep ℚ (AlgebraicClosure ℚ) a ha F) :
    (rationalArithmeticSPlaceCompletionMorphism a ha F p).hom x =
      x (Sum.inr (rationalExceptionalIndexedUpperPrime a ha F p)) :=
  originalSPlaceFullIdeleInclusion_finite ℚ F
    (arithmeticSUnitFiniteStageSupport ℚ (AlgebraicClosure ℚ) a ha F)
    (originalExceptionalIntegerSupport_galoisStable F ℚ a ha) x
    (rationalExceptionalIndexedUpperPrime a ha F p)

/-- The original finite S-place unit at the selected prime, in its literal local closure. -/
def rationalArithmeticSPlaceLocalMap :
    ArithmeticSPlaceFiniteStageRep ℚ (AlgebraicClosure ℚ) a ha F →ₗ[ℤ]
      Rep.ofAlgebraAutOnUnits (rationalPrimeLocalField p.val.val p.val.property)
        (rationalPrimeLocalClosure p.val.val p.val.property) :=
  let w := rationalExceptionalIndexedUpperPrime a ha F p
  (Units.map (algebraMap (w.val.adicCompletion F)
    (rationalPrimeLocalClosure p.val.val p.val.property)).toMonoidHom).toAdditive.toIntLinearMap.comp
      (LinearMap.proj (R := ℤ) (Sum.inr w))

/-- Embed the original finite completion morphism through the existing
unit base-change morphism into the fixed local closure. -/
def rationalArithmeticSPlaceClosureMorphism :
    let v := rationalExceptionalIndexedBasePrime a ha p
    let w := rationalExceptionalIndexedUpperPrime a ha F p
    let κ := galoisBaseChangeRestriction (v.adicCompletion ℚ)
      (rationalPrimeLocalField p.val.val p.val.property) (w.val.adicCompletion F)
      (rationalPrimeLocalClosure p.val.val p.val.property)
    Rep.res ((originalAdicCompletionGaloisInclusion ℚ F v w.val).comp κ)
      (ArithmeticSPlaceFiniteStageRep ℚ (AlgebraicClosure ℚ) a ha F) ⟶
        Rep.ofAlgebraAutOnUnits (rationalPrimeLocalField p.val.val p.val.property)
          (rationalPrimeLocalClosure p.val.val p.val.property) :=
  let v := rationalExceptionalIndexedBasePrime a ha p
  let w := rationalExceptionalIndexedUpperPrime a ha F p
  let κ := galoisBaseChangeRestriction (v.adicCompletion ℚ)
    (rationalPrimeLocalField p.val.val p.val.property) (w.val.adicCompletion F)
    (rationalPrimeLocalClosure p.val.val p.val.property)
  (Rep.resFunctor κ).map (rationalArithmeticSPlaceCompletionMorphism a ha F p) ≫
    galoisUnitBaseChangeInclusion (v.adicCompletion ℚ)
      (rationalPrimeLocalField p.val.val p.val.property) (w.val.adicCompletion F)
      (rationalPrimeLocalClosure p.val.val p.val.property)

/-- The composed original morphism has exactly the specified prime value. -/
theorem rationalArithmeticSPlaceClosureMorphism_apply
    (x : ArithmeticSPlaceFiniteStageRep ℚ (AlgebraicClosure ℚ) a ha F) :
    (rationalArithmeticSPlaceClosureMorphism a ha F p).hom x =
      rationalArithmeticSPlaceLocalMap a ha F p x := by
  let w := rationalExceptionalIndexedUpperPrime a ha F p
  exact congrArg ((Units.map (algebraMap (w.val.adicCompletion F)
    (rationalPrimeLocalClosure p.val.val p.val.property)).toMonoidHom).toAdditive)
      (rationalArithmeticSPlaceCompletionMorphism_apply a ha F p x)

/-- Local evaluation intertwines the actual arithmetic restriction and
the original local Galois unit action; no action comparison is assumed. -/
theorem rationalArithmeticSPlaceLocalMap_equivariant
    (g : Gal(rationalPrimeLocalClosure p.val.val p.val.property /
      rationalPrimeLocalField p.val.val p.val.property))
    (x : ArithmeticSPlaceFiniteStageRep ℚ (AlgebraicClosure ℚ) a ha F) :
    rationalArithmeticSPlaceLocalMap a ha F p
      ((ArithmeticSPlaceFiniteStageRep ℚ (AlgebraicClosure ℚ) a ha F).ρ
        (AlgEquiv.restrictNormalHom F (rationalPrimeArithmeticRestriction a p.val.val p.val.property g)) x) =
      (Rep.ofAlgebraAutOnUnits (rationalPrimeLocalField p.val.val p.val.property)
        (rationalPrimeLocalClosure p.val.val p.val.property)).ρ g
          (rationalArithmeticSPlaceLocalMap a ha F p x) := by
  exact localMapEquivariantOfRestriction
    (ArithmeticSPlaceFiniteStageRep ℚ (AlgebraicClosure ℚ) a ha F)
    (Rep.ofAlgebraAutOnUnits (rationalPrimeLocalField p.val.val p.val.property)
      (rationalPrimeLocalClosure p.val.val p.val.property)) _
    ((AlgEquiv.restrictNormalHom F : rationalArithmeticGaloisGroup a →* Gal(F/ℚ)).comp
      (rationalPrimeArithmeticRestriction a p.val.val p.val.property).toMonoidHom)
    (rationalArithmeticSPlaceClosureMorphism a ha F p)
    (rationalArithmeticSPlaceLocalMap a ha F p)
    (rationalArithmeticSPlaceClosureMorphism_apply a ha F p)
    (rationalArithmeticOriginalCompletion_galois_restriction a p.val.val p.val.property F) g x

/-- The original S-place localization is a morphism of the actual restricted representations. -/
def rationalArithmeticSPlaceLocalMorphism :
    Rep.res ((AlgEquiv.restrictNormalHom F : rationalArithmeticGaloisGroup a →* Gal(F/ℚ)).comp
      (rationalPrimeArithmeticRestriction a p.val.val p.val.property).toMonoidHom)
      (ArithmeticSPlaceFiniteStageRep ℚ (AlgebraicClosure ℚ) a ha F) ⟶
        Rep.ofAlgebraAutOnUnits (rationalPrimeLocalField p.val.val p.val.property)
          (rationalPrimeLocalClosure p.val.val p.val.property) :=
  Rep.ofHom ⟨rationalArithmeticSPlaceLocalMap a ha F p, fun g => by
    apply LinearMap.ext
    intro x
    exact rationalArithmeticSPlaceLocalMap_equivariant a ha F p g x⟩

end
end Dubon2026
