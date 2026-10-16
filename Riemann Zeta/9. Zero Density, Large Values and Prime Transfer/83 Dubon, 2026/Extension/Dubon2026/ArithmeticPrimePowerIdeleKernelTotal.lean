import Dubon2026.ArithmeticRelativeStageClassProjection
import Dubon2026.OriginalCyclicClassH2Surjectivity
import Dubon2026.ContinuousFiniteH2CardAnnihilation

/-! # Principal reciprocity on the actual odd-primary class-map kernel

The original exact sequence supplies a principal lift. Finite group-order
annihilation proves its required torsion, so the existing reciprocity theorem
kills its canonical total without cyclicity of the field extension. This
is the principal-lift comparison used in DUB-17's class normalization.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance 1100] Submodule.Quotient.module
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField arithmeticRelativeStageIdeleAddCommGroup
  arithmeticRelativeStageClassAddCommGroup

private theorem finiteDegree_annihilates
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)] [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)]
    (n : ℕ) (hn : Module.finrank K L = n)
    (x : GaloisUnitContinuousH2 (K := K) (Ω := L)) : n • x = 0 := by
  letI : Fintype Gal(L/K) := Fintype.ofFinite _
  have hz := continuousFiniteH2_card_nsmul_eq_zero (Rep.ofAlgebraAutOnUnits K L)
    (discreteGaloisUnitAction_continuous (K := K) (Ω := L)) x
  have he : Fintype.card Gal(L/K) = n :=
    Nat.card_eq_fintype_card.symm.trans ((IsGalois.card_aut_eq_finrank K L).trans hn)
  exact he ▸ hz

private theorem finitePrimePower_annihilates
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)] [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)]
    (q t : ℕ) (hn : Module.finrank K L = q ^ t)
    (x : GaloisUnitContinuousH2 (K := K) (Ω := L)) : q ^ (t + 1) • x = 0 := by
  have hz := finiteDegree_annihilates K L (q ^ t) hn x
  rw [pow_succ, mul_nsmul, hz, nsmul_zero]

private theorem total_zero_of_kernel
    (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
    (total : groupCohomology (originalFullIdeleRep K L) 2 →+ AddCircle (1 : ℚ))
    (hc : ∀ c : groupCohomology.cocycles₂ (Rep.ofAlgebraAutOnUnits K L),
      total ((groupCohomology.functor ℤ Gal(L/K) 2).map (originalFullPrincipalRepHom K L)
        (groupCohomology.H2π _ c)) = 0)
    (x : groupCohomology (originalFullIdeleRep K L) 2)
    (hx : (groupCohomology.functor ℤ Gal(L/K) 2).map (originalFullClassRepHom K L) x = 0) :
    total x = 0 := by
  have hk : x ∈ LinearMap.ker
      ((groupCohomology.functor ℤ Gal(L/K) 2).map (originalFullClassRepHom K L)).hom := hx
  rw [originalFullClassH2_ker_eq_principal_range K L] at hk
  obtain ⟨y, rfl⟩ := hk
  induction y using groupCohomology.H2_induction_on with
  | h c => exact hc c

variable (a : 𝓞 ℚ)
  (K E : IntermediateField ℚ (rationalUnramifiedExtension a))
  [FiniteDimensional ℚ K] [FiniteDimensional ℚ E] (hKE : K ≤ E)
  [hGalKE : letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
    IsGalois K E]

/-- The canonical total kills the original class-projection kernel at every actual odd-prime-power stage, without a cyclicity hypothesis. -/
theorem rationalArithmeticRelativePrimePower_total_zero_of_class_zero
    (q t : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) (hqa : (q : 𝓞 ℚ) ∣ a)
    (hdegree : letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
      letI : Module K E := Algebra.toModule
      Module.finrank K E = q ^ t)
    (x : rationalArithmeticRelativeStageIdeleH2 a K E hKE)
    (hx : rationalArithmeticRelativeStageClassProjection a K E hKE x = 0) :
    rationalArithmeticRelativeStageIdeleTotalInvariant a K E hKE x = 0 := by
  letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
  letI : Module K E := Algebra.toModule
  letI : SMul K E := ((IntermediateField.inclusion hKE).toAlgebra).toSMul
  letI : IsScalarTower ℚ K E := IsScalarTower.of_algHom (IntermediateField.inclusion hKE)
  letI : FiniteDimensional K E := FiniteDimensional.right ℚ K E
  letI : IsGalois K E := hGalKE
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K E) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K E) := ⟨rfl⟩
  apply total_zero_of_kernel K E (rationalArithmeticRelativeStageIdeleTotalInvariant a K E hKE) ?_ x hx
  intro c
  let z : continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits K E) :=
    ⟨c, continuous_of_discreteTopology⟩
  have hz := finitePrimePower_annihilates K E q t hdegree (Submodule.Quotient.mk z)
  exact rationalArithmeticRelativeStageIdeleTotalInvariant_principal a K E hKE q t hq hq2 hqa z hz

/-- Equal original class projections have equal canonical totals at the same actual odd-primary stage. -/
theorem rationalArithmeticRelativePrimePower_total_eq_of_class_eq
    (q t : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) (hqa : (q : 𝓞 ℚ) ∣ a)
    (hdegree : letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
      letI : Module K E := Algebra.toModule
      Module.finrank K E = q ^ t)
    (x y : rationalArithmeticRelativeStageIdeleH2 a K E hKE)
    (hxy : rationalArithmeticRelativeStageClassProjection a K E hKE x =
      rationalArithmeticRelativeStageClassProjection a K E hKE y) :
    rationalArithmeticRelativeStageIdeleTotalInvariant a K E hKE x =
      rationalArithmeticRelativeStageIdeleTotalInvariant a K E hKE y := by
  have hz := rationalArithmeticRelativePrimePower_total_zero_of_class_zero
    a K E hKE q t hq hq2 hqa hdegree (x - y) (by rw [map_sub, hxy, sub_self])
  exact sub_eq_zero.mp ((map_sub (rationalArithmeticRelativeStageIdeleTotalInvariant a K E hKE) x y).symm.trans hz)

end
end Dubon2026
