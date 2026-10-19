import Dubon2026.ArithmeticSPlaceLocalMap
import Dubon2026.RationalArithmeticOriginalCompletionDualDiagram
import Dubon2026.GaloisTowerLocalUnitDualConnecting
import Dubon2026.OriginalIndexedPrimeSPlaceRelation

/-! The assembled original exceptional S-place relation recovers each
literal local relation invariant in the fixed local closure. This supplies
the source-family evaluation edge in DUB-17's constructed-class recovery. -/
namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField Classical
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




attribute [local instance] rationalExceptionalIndexedPrimeLiesOver
variable (a : 𝓞 ℚ) (ha : a ≠ 0)
  (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
  (B : Rep.{0} ℤ Gal(F/ℚ))
  (ψ : ∀ p : rationalArithmeticExceptionalPrimes a ha,
    Rep.res (originalAdicCompletionGaloisInclusion ℚ F
      (rationalExceptionalIndexedBasePrime a ha p) (rationalExceptionalIndexedUpperPrime a ha F p).val)
      (originalRelationModule B) ⟶
    Rep.ofAlgebraAutOnUnits ((rationalExceptionalIndexedBasePrime a ha p).adicCompletion ℚ)
      ((rationalExceptionalIndexedUpperPrime a ha F p).val.adicCompletion F))

/-- The existing indexed assembly, with the actual exceptional support and local units. -/
abbrev rationalExceptionalSPlaceRelation :=
  originalIndexedPrimeSPlaceRelation ℚ F (arithmeticSUnitFiniteStageSupport ℚ (AlgebraicClosure ℚ) a ha F)
    (originalExceptionalIntegerSupport_galoisStable F ℚ a ha)
    (rationalArithmeticExceptionalPrimes a ha) (rationalExceptionalIndexedUpperPrime a ha F) B (fun p => originalAdicUnitRelationMorphism ℚ F
      (rationalExceptionalIndexedBasePrime a ha p) (rationalExceptionalIndexedUpperPrime a ha F p).val B (ψ p))

/-- Evaluation at the selected original prime recovers the same local
relation, embedded through its actual finite completion. -/
theorem rationalExceptionalSPlaceRelation_local_value
    (p : rationalArithmeticExceptionalPrimes a ha) (x : originalRelationModule B) :
    rationalArithmeticSPlaceLocalMap a ha F p ((rationalExceptionalSPlaceRelation a ha F B ψ).hom x) =
      (Units.map (algebraMap ((rationalExceptionalIndexedUpperPrime a ha F p).val.adicCompletion F)
        (rationalPrimeLocalClosure p.val.val p.val.property)).toMonoidHom).toAdditive ((ψ p).hom x) := by
  have hw : Function.Injective (fun p : rationalArithmeticExceptionalPrimes a ha =>
      originalFinitePrimeBelow ℚ F (rationalExceptionalIndexedUpperPrime a ha F p).val) := by
    intro p r h
    apply rationalExceptionalIndexedBasePrime_injective a ha
    exact (rationalExceptionalIndexedUpperPrime_below a ha F p).symm.trans
      (h.trans (rationalExceptionalIndexedUpperPrime_below a ha F r))
  have he := originalIndexedPrimeSPlaceRelation_evaluation ℚ F (arithmeticSUnitFiniteStageSupport ℚ (AlgebraicClosure ℚ) a ha F)
    (originalExceptionalIntegerSupport_galoisStable F ℚ a ha)
    (rationalArithmeticExceptionalPrimes a ha) (rationalExceptionalIndexedUpperPrime a ha F) B hw (fun p => originalAdicUnitRelationMorphism ℚ F
      (rationalExceptionalIndexedBasePrime a ha p) (rationalExceptionalIndexedUpperPrime a ha F p).val B (ψ p)) p x
  exact congrArg
    (fun z => (Units.map (algebraMap ((rationalExceptionalIndexedUpperPrime a ha F p).val.adicCompletion F)
      (rationalPrimeLocalClosure p.val.val p.val.property)).toMonoidHom).toAdditive z) he

/-- The same local value identifies the actual dual invariant after the
completion-group change; no source-family compatibility is assumed. -/
theorem rationalExceptionalSPlaceRelation_local_invariant
    (p : rationalArithmeticExceptionalPrimes a ha) :
    let π := (AlgEquiv.restrictNormalHom F : rationalArithmeticGaloisGroup a →* Gal(F/ℚ)).comp
      (rationalPrimeArithmeticRestriction a p.val.val p.val.property).toMonoidHom
    let Φ := rationalExceptionalSPlaceRelation a ha F B ψ
    let φ := (Rep.resFunctor π).map Φ ≫ rationalArithmeticSPlaceLocalMorphism a ha F p
    let d := rationalArithmeticOriginalCompletionDualDiagram a F p.val.val p.val.property B
    d.τ₃.hom ((Representation.linHom.invariantsEquivRepHom _ _).symm φ).val =
      (galoisTowerLocalUnitRelationInvariant
        ((rationalExceptionalIndexedBasePrime a ha p).adicCompletion ℚ)
        ((rationalExceptionalIndexedUpperPrime a ha F p).val.adicCompletion F)
        (rationalPrimeLocalClosure p.val.val p.val.property) Gal(F/ℚ)
        (originalAdicCompletionGaloisInclusion ℚ F
          (rationalExceptionalIndexedBasePrime a ha p) (rationalExceptionalIndexedUpperPrime a ha F p).val)
        B (ψ p)).val := by
  apply LinearMap.ext
  intro x
  exact rationalExceptionalSPlaceRelation_local_value a ha F B ψ p x

end
end Dubon2026
