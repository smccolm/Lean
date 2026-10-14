import Dubon2026.OriginalCyclotomicContinuousH2Descent
import Dubon2026.OriginalFiniteGaloisStageLift
import Dubon2026.ContinuousGaloisH2TorsionFiniteStage

/-! # Every original odd-primary continuous arithmetic class has a cyclic stage

Actual finite descent, literal ambient lifting, and the constructed cyclic
descent are assembled on the same original continuous unit-H2 class. No
finite-stage, containment or torsion-preservation premise remains. This is
the continuous source entry for DUB-17's arithmetic invariant sum-zero.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField Classical
attribute [-instance] UniformSpace.Completion.instSMul DivisionRing.toRatAlgebra SubfieldClass.instSMulRat
attribute [local instance] originalContinuousCyclicUnionGalois

variable {Ω : Type} [Field Ω] [CharZero Ω] [Algebra ℚ Ω] [IsSepClosed Ω]
  (a : 𝓞 ℚ)
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))]

/-- Every original odd-prime torsion continuous unit-H2 class is the actual inflation of a constructed cyclic cyclotomic finite-stage class inside the same unramified union. -/
theorem originalUnramifiedUnitH2_exists_cyclic_stage
    (q : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) (hqa : (q : 𝓞 ℚ) ∣ a)
    (x : GaloisUnitContinuousH2 (K := ℚ) (Ω := originalUnramifiedGaloisUnion (Ω := Ω) a))
    (hx : q • x = 0) :
    let U := originalUnramifiedGaloisUnion (Ω := Ω) a
    ∃ (k : ℕ) (F : FiniteGaloisIntermediateField ℚ Ω),
      1 ≤ k ∧ IsCyclotomicExtension {q ^ (k + 1)} ℚ F ∧ IsCyclic Gal(F/ℚ) ∧
      ∃ hF : F.toIntermediateField ≤ U,
        letI : Algebra F U := (IntermediateField.inclusion hF).toAlgebra
        letI : IsScalarTower ℚ F U := IsScalarTower.of_algHom (IntermediateField.inclusion hF)
        letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits ℚ F) := ⊥
        letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits ℚ F) := ⟨rfl⟩
        ∃ y : groupCohomology (Rep.ofAlgebraAutOnUnits ℚ F) 2, q • y = 0 ∧
          continuousGaloisUnitBaseChangeH2 ℚ ℚ F U
            ((continuousDiscreteH2Equiv (Rep.ofAlgebraAutOnUnits ℚ F)
              (discreteGaloisUnitAction_continuous (K := ℚ) (Ω := F))).symm y) = x := by
  let U := originalUnramifiedGaloisUnion (Ω := Ω) a
  obtain ⟨F, y, hyq, hy⟩ := continuousGaloisUnitH2_exists_torsion_finite_stage q x hx
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits ℚ F) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits ℚ F) := ⟨rfl⟩
  let E := originalFiniteGaloisStageLift U F
  letI := originalFiniteGaloisStageLiftAlgebra U F
  letI := originalFiniteGaloisStageLiftUpperAlgebra U F
  letI := originalFiniteGaloisStageLift_baseTower U F
  letI := originalFiniteGaloisStageLift_upperBaseTower U F
  letI := originalFiniteGaloisStageLift_upperTower U F
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits ℚ E) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits ℚ E) := ⟨rfl⟩
  let yE := finiteGaloisUnitBaseChangeH2 ℚ ℚ F E y
  have hyE : q • yE = 0 := by
    have h := congrArg (finiteGaloisUnitBaseChangeH2 ℚ ℚ F E) hyq
    simpa only [map_nsmul, map_zero] using h
  let e := continuousDiscreteH2Equiv (Rep.ofAlgebraAutOnUnits ℚ E)
    (discreteGaloisUnitAction_continuous (K := ℚ) (Ω := E))
  let z := e yE
  have hz : q • z = 0 := by
    have h := congrArg e hyE
    simpa only [map_nsmul, map_zero] using h
  have hdes := originalCyclotomic_exists_continuousH2_descent_stage
    (Ω := Ω) a E q hq hq2 hqa (originalFiniteGaloisStageLift_le U F) z hz
  obtain ⟨k, T, hk, hcyc, hCyclic, hT, t, ht, hInfl⟩ := hdes
  refine ⟨k, T, hk, hcyc, hCyclic, hT, t, ht, ?_⟩
  have he : e.symm z = yE := e.symm_apply_apply yE
  have hE := originalFiniteGaloisStageLift_inflation U F y
  have hsame : continuousGaloisUnitBaseChangeH2 ℚ ℚ E U (e.symm z) = x :=
    (congrArg (continuousGaloisUnitBaseChangeH2 ℚ ℚ E U) he).trans (hE.trans hy)
  exact hInfl.trans hsame

end
end Dubon2026
