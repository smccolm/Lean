import Dubon2026.OriginalTwoPrimaryContinuousDescent
import Dubon2026.OriginalFiniteGaloisStageLift
import Dubon2026.ContinuousGaloisH2TorsionFiniteStage

/-! # Every original two-primary continuous class has a cyclic subfield

Existing finite-stage torsion descent and literal ambient lifting feed
the constructed cyclic splitting theorem. The result is the same actual
continuous class, with its original annihilator, over a cyclic totally
complex subfield inside the unchanged arithmetic union. This supplies
the missing two-primary source entry for DUB-17's invariant sum formula.
-/
namespace Dubon2026
noncomputable section
open NumberField
open scoped NumberField Classical
attribute [-instance] UniformSpace.Completion.instSMul DivisionRing.toRatAlgebra SubfieldClass.instSMulRat
  AlgebraicClosure.instSMulOfIsScalarTower
attribute [local instance] originalContinuousCyclicUnionGalois

variable {Ω : Type} [Field Ω] [CharZero Ω] [Algebra ℚ Ω] [IsSepClosed Ω]
  (a : 𝓞 ℚ)
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))]

/-- Every actual two-primary continuous class is the original inflation
of a constructed cyclic totally complex finite-field class in the same union. -/
theorem originalUnramifiedUnitH2_exists_two_primary_cyclic_subfield
    (r : ℕ) (h2a : (2 : 𝓞 ℚ) ∣ a)
    (x : GaloisUnitContinuousH2 (K := ℚ) (Ω := originalUnramifiedGaloisUnion (Ω := Ω) a))
    (hx : 2 ^ (r + 1) • x = 0) :
    let U := originalUnramifiedGaloisUnion (Ω := Ω) a
    ∃ (k : ℕ) (F : FiniteGaloisIntermediateField ℚ Ω),
      r + 2 ≤ k ∧ IsCyclotomicExtension {2 ^ (k + 1)} ℚ F ∧
      ∃ hF : F.toIntermediateField ≤ U,
      ∃ E : IntermediateField ℚ F, ∃ hgal : IsGalois ℚ E,
      letI := hgal
      IsCyclic Gal(E/ℚ) ∧ IsTotallyComplex E ∧
      let iE := (IntermediateField.inclusion hF).comp E.val
      letI : Algebra E U := iE.toAlgebra
      letI : SMul E U := iE.toAlgebra.toSMul
      letI : IsScalarTower ℚ E U := IsScalarTower.of_algHom iE
      ∃ y : groupCohomology (Rep.ofAlgebraAutOnUnits ℚ E) 2,
        2 ^ (r + 1) • y = 0 ∧
        originalAlgebraicContinuousInflation ℚ E U y = x := by
  let U := originalUnramifiedGaloisUnion (Ω := Ω) a
  obtain ⟨P, y, hyq, hy⟩ := continuousGaloisUnitH2_exists_torsion_finite_stage (2 ^ (r + 1)) x hx
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits ℚ P) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits ℚ P) := ⟨rfl⟩
  let A := originalFiniteGaloisStageLift U P
  letI := originalFiniteGaloisStageLiftAlgebra U P
  letI := originalFiniteGaloisStageLiftUpperAlgebra U P
  letI := originalFiniteGaloisStageLift_baseTower U P
  letI := originalFiniteGaloisStageLift_upperBaseTower U P
  letI := originalFiniteGaloisStageLift_upperTower U P
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits ℚ A) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits ℚ A) := ⟨rfl⟩
  let yA := finiteGaloisUnitBaseChangeH2 ℚ ℚ P A y
  have hyA : 2 ^ (r + 1) • yA = 0 := by
    have h := congrArg (finiteGaloisUnitBaseChangeH2 ℚ ℚ P A) hyq
    simpa only [map_nsmul, map_zero] using h
  let e := continuousDiscreteH2Equiv (Rep.ofAlgebraAutOnUnits ℚ A)
    (discreteGaloisUnitAction_continuous (K := ℚ) (Ω := A))
  let z := e yA
  have hz : 2 ^ (r + 1) • z = 0 := by
    have h := congrArg e hyA
    simpa only [map_nsmul, map_zero] using h
  have hdes := originalUnramifiedUnion_exists_two_primary_continuous_descent
    (Ω := Ω) a A r h2a (originalFiniteGaloisStageLift_le U P) z hz
  obtain ⟨k, F, hk, hcyclo, hF, E, hgal, hcyclic, hcomplex, t, ht, hInfl⟩ := hdes
  refine ⟨k, F, hk, hcyclo, hF, E, hgal, hcyclic, hcomplex, t, ht, ?_⟩
  have he : e.symm z = yA := e.symm_apply_apply yA
  have hA := originalFiniteGaloisStageLift_inflation U P y
  have hsame : continuousGaloisUnitBaseChangeH2 ℚ ℚ A U (e.symm z) = x :=
    (congrArg (continuousGaloisUnitBaseChangeH2 ℚ ℚ A U) he).trans (hA.trans hy)
  exact hInfl.trans hsame

end
end Dubon2026
