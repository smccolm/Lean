import Dubon2026.RationalTraceOriginalCoefficientCocycle
import Dubon2026.RationalTraceFiniteSourceH1
/-! The original arithmetic source and actual finite completion restrictions
form the same algebraic H1 square. This identifies the constructed finite
local lifts with the source classes whose trace cups are tested in DUB-17. -/
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

private theorem h1_map_comp_of_pointwise
    {G H J : Type} [Group G] [Group H] [Group J]
    (A : Rep.{0} ℤ G) (B : Rep.{0} ℤ H) (C : Rep.{0} ℤ J)
    (π : H →* G) (j : J →* H) (β : J →* G)
    (φ : Rep.res π A ⟶ B) (ψ : Rep.res j B ⟶ C) (θ : Rep.res β A ⟶ C)
    (hg : ∀ g, π (j g) = β g)
    (hc : ∀ x : A, ψ.hom (φ.hom x) = θ.hom x)
    (y : groupCohomology A 1) :
    groupCohomology.map j ψ 1 (groupCohomology.map π φ 1 y) =
      groupCohomology.map β θ 1 y := by
  induction y using groupCohomology.H1_induction_on with
  | h c =>
    simp only [groupCohomology.H1π_comp_map_apply]
    apply congrArg (groupCohomology.H1π C)
    apply Subtype.ext
    funext g
    change ψ.hom (φ.hom (c (π (j g)))) = θ.hom (c (β g))
    rw [hg, hc]

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  (a : 𝓞 ℚ) (q : ℕ) [Fact q.Prime]
  (σ : rationalArithmeticGaloisGroup a →* Matrix.GeneralLinearGroup ι (ZMod q))
  (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
  (hker : ∀ u : rationalArithmeticGaloisGroup a,
    AlgEquiv.restrictNormalHom F u = 1 →
    ∀ x : rationalArithmeticTraceZeroIntegerRep a q σ,
      (rationalArithmeticTraceZeroIntegerRep a q σ).ρ u x = x)
  (p : ℕ) (hp : p.Prime)

/-- The actual source restriction on the original completion group. -/
abbrev rationalTraceOriginalSourceRestriction :
    Gal(rationalPrimeLocalClosure p hp / (rationalOriginalPrimePlace p hp).adicCompletion ℚ) →*
      rationalArithmeticGaloisGroup a :=
  (rationalPrimeArithmeticRestriction a p hp).toMonoidHom.comp
    (rationalOriginalCompletionGaloisEquiv p hp).symm.toMonoidHom

/-- Original finite completion restriction is precisely original
arithmetic restriction followed by restriction to the same finite field. -/
theorem rationalTraceOriginalCompletion_source_restriction
    (g : Gal(rationalPrimeLocalClosure p hp / (rationalOriginalPrimePlace p hp).adicCompletion ℚ)) :
    originalAdicCompletionGaloisInclusion ℚ F (rationalOriginalPrimePlace p hp)
      (rationalArithmeticOriginalPrime a p hp F)
      (AlgEquiv.restrictNormalHom ((rationalArithmeticOriginalPrime a p hp F).adicCompletion F) g) =
    AlgEquiv.restrictNormalHom F (rationalTraceOriginalSourceRestriction a p hp g) := by
  have h := rationalArithmeticOriginalCompletion_galois_restriction a p hp F
    ((rationalOriginalCompletionGaloisEquiv p hp).symm g)
  have hg : galoisBaseChangeRestriction ((rationalOriginalPrimePlace p hp).adicCompletion ℚ)
      (rationalPrimeLocalField p hp) ((rationalArithmeticOriginalPrime a p hp F).adicCompletion F)
      (rationalPrimeLocalClosure p hp) ((rationalOriginalCompletionGaloisEquiv p hp).symm g) =
      AlgEquiv.restrictNormalHom ((rationalArithmeticOriginalPrime a p hp F).adicCompletion F) g := by
    change AlgEquiv.restrictNormalHom ((rationalArithmeticOriginalPrime a p hp F).adicCompletion F)
      (rationalOriginalCompletionGaloisEquiv p hp ((rationalOriginalCompletionGaloisEquiv p hp).symm g)) = _
    rw [MulEquiv.apply_symm_apply]
  rw [hg] at h
  exact h

/-- Original source coefficients restrict to the finite-completion
coefficient by the literal identity on the same trace-zero matrices. -/
def rationalTraceOriginalSourceCoefficientMap :
    Rep.res (rationalTraceOriginalSourceRestriction a p hp)
      (rationalArithmeticTraceZeroIntegerRep a q σ) ⟶
      rationalTraceOriginalLocalCoefficientRep a q σ F hker p hp :=
  Rep.ofHom {
    toLinearMap := LinearMap.id
    isIntertwining' g := by
      apply LinearMap.ext
      intro x
      change (rationalArithmeticTraceZeroIntegerRep a q σ).ρ
          (rationalTraceOriginalSourceRestriction a p hp g) x =
        (rationalTraceOriginalFiniteRep a q σ F hker).ρ
          (originalAdicCompletionGaloisInclusion ℚ F (rationalOriginalPrimePlace p hp)
            (rationalArithmeticOriginalPrime a p hp F)
            (AlgEquiv.restrictNormalHom ((rationalArithmeticOriginalPrime a p hp F).adicCompletion F) g)) x
      rw [rationalTraceOriginalCompletion_source_restriction a F p hp]
      exact (finiteStageCoefficientRepresentation_apply (rationalArithmeticTraceZeroIntegerRep a q σ)
        F hker (rationalTraceOriginalSourceRestriction a p hp g) x).symm }

/-- The actual finite H1 class has exactly the same local image through
the original arithmetic source as through the finite completion. -/
theorem rationalTraceFiniteSourceH1_original_restriction
    (y : groupCohomology (rationalTraceOriginalFiniteRep a q σ F hker) 1) :
    groupCohomology.map (rationalTraceOriginalSourceRestriction a p hp)
      (rationalTraceOriginalSourceCoefficientMap a q σ F hker p hp) 1
      (groupCohomology.map (AlgEquiv.restrictNormalHom F)
        (rationalTraceFiniteSourceCoefficientMap a q σ F hker) 1 y) =
    groupCohomology.map
      ((originalAdicCompletionGaloisInclusion ℚ F (rationalOriginalPrimePlace p hp)
        (rationalArithmeticOriginalPrime a p hp F)).comp
          (AlgEquiv.restrictNormalHom ((rationalArithmeticOriginalPrime a p hp F).adicCompletion F)))
      (𝟙 (rationalTraceOriginalLocalCoefficientRep a q σ F hker p hp)) 1 y := by
  exact h1_map_comp_of_pointwise (rationalTraceOriginalFiniteRep a q σ F hker)
    (rationalArithmeticTraceZeroIntegerRep a q σ)
    (rationalTraceOriginalLocalCoefficientRep a q σ F hker p hp)
    (AlgEquiv.restrictNormalHom F) (rationalTraceOriginalSourceRestriction a p hp)
    ((originalAdicCompletionGaloisInclusion ℚ F (rationalOriginalPrimePlace p hp)
      (rationalArithmeticOriginalPrime a p hp F)).comp
        (AlgEquiv.restrictNormalHom ((rationalArithmeticOriginalPrime a p hp F).adicCompletion F)))
    (rationalTraceFiniteSourceCoefficientMap a q σ F hker)
    (rationalTraceOriginalSourceCoefficientMap a q σ F hker p hp)
    (𝟙 (rationalTraceOriginalLocalCoefficientRep a q σ F hker p hp))
    (fun g => (rationalTraceOriginalCompletion_source_restriction a F p hp g).symm)
    (fun _ => rfl) y

end
end Dubon2026
