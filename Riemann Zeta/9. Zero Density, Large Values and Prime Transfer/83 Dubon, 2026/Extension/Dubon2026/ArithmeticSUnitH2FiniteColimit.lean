import Dubon2026.ArithmeticSUnitH2FiniteDirectedSystem
import Dubon2026.ArithmeticSUnitH2FiniteZeroDetection

/-! # Original continuous arithmetic S-unit H2 is its actual finite-stage colimit

Finite descent of original cocycles proves surjectivity; descent of their
original continuous S-unit coboundary witnesses proves injectivity. The map
retains the literal field inclusions and restriction of Galois automorphisms.
This closes the arithmetic coefficient H2 comparison used by the DUB-17
duality route; it does not assert the idele-class comparison or localization exactness.
-/

namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [local instance 1100] Rep.hV2

variable (K Ω : Type) [Field K] [Field Ω] [NumberField K] [Algebra K Ω]
  (a : 𝓞 K) (ha : a ≠ 0)
  [DecidableEq (FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))]

/-- The actual module direct limit of original finite Galois S-unit H2. -/
abbrev ArithmeticSUnitH2FiniteColimit :=
  Module.DirectLimit (ArithmeticSUnitH2Stage K Ω a ha) (arithmeticSUnitH2Transition K Ω a ha)

variable [TopologicalSpace (originalArithmeticSUnitRepresentation K Ω a ha)]
  [DiscreteTopology (originalArithmeticSUnitRepresentation K Ω a ha)]

/-- Literal global inflation from the original fixed discrete finite-stage quotient. -/
def arithmeticSUnitH2StageMap
    (F : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a)) :
    ArithmeticSUnitH2Stage K Ω a ha F →ₗ[ℤ] ArithmeticSUnitContinuousH2 K Ω a ha := by
  letI : TopologicalSpace (arithmeticSUnitFiniteStageRep K Ω a ha F) := ⊥
  letI : DiscreteTopology (arithmeticSUnitFiniteStageRep K Ω a ha F) := ⟨rfl⟩
  exact arithmeticSUnitFiniteStageH2Inflation K Ω a ha F

omit [DecidableEq (FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))] in
/-- The original inflation maps respect the proved finite-stage transition system. -/
theorem arithmeticSUnitH2StageMap_transition
    (E F : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
    (hEF : E ≤ F) (x : ArithmeticSUnitH2Stage K Ω a ha E) :
    arithmeticSUnitH2StageMap K Ω a ha F (arithmeticSUnitH2Transition K Ω a ha E F hEF x) =
      arithmeticSUnitH2StageMap K Ω a ha E x := by
  letI : TopologicalSpace (arithmeticSUnitFiniteStageRep K Ω a ha E) := ⊥
  letI : DiscreteTopology (arithmeticSUnitFiniteStageRep K Ω a ha E) := ⟨rfl⟩
  letI : TopologicalSpace (arithmeticSUnitFiniteStageRep K Ω a ha F) := ⊥
  letI : DiscreteTopology (arithmeticSUnitFiniteStageRep K Ω a ha F) := ⟨rfl⟩
  exact (arithmeticSUnitFiniteStageH2Inflation_tower K Ω a ha E F hEF x).symm

/-- The actual universal colimit map to original continuous arithmetic S-unit H2. -/
def arithmeticSUnitH2FiniteColimitToH2 :
    ArithmeticSUnitH2FiniteColimit K Ω a ha →ₗ[ℤ] ArithmeticSUnitContinuousH2 K Ω a ha :=
  Module.DirectLimit.lift ℤ
    (FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
    (ArithmeticSUnitH2Stage K Ω a ha) (arithmeticSUnitH2Transition K Ω a ha)
    (arithmeticSUnitH2StageMap K Ω a ha) (arithmeticSUnitH2StageMap_transition K Ω a ha)

/-- Each original finite-stage colimit representative maps to its literal inflation. -/
theorem arithmeticSUnitH2FiniteColimitToH2_of
    (F : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
    (x : ArithmeticSUnitH2Stage K Ω a ha F) :
    arithmeticSUnitH2FiniteColimitToH2 K Ω a ha
      (Module.DirectLimit.of ℤ
        (FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
        (ArithmeticSUnitH2Stage K Ω a ha) (arithmeticSUnitH2Transition K Ω a ha) F x) =
      arithmeticSUnitH2StageMap K Ω a ha F x :=
  Module.DirectLimit.lift_of _ _ x

/-- Exact finite descent of actual continuous S-unit cocycles makes the original colimit map surjective. -/
theorem arithmeticSUnitH2FiniteColimitToH2_surjective :
    Function.Surjective (arithmeticSUnitH2FiniteColimitToH2 K Ω a ha) := by
  intro x
  obtain ⟨F, y, hy⟩ := arithmeticSUnitContinuousH2_exists_finiteStage K Ω a ha x
  refine ⟨Module.DirectLimit.of ℤ
    (FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
    (ArithmeticSUnitH2Stage K Ω a ha) (arithmeticSUnitH2Transition K Ω a ha) F y, ?_⟩
  exact (arithmeticSUnitH2FiniteColimitToH2_of K Ω a ha F y).trans hy

/-- The original continuous S-unit coboundary witness descends, so the actual colimit map is injective. Individual finite-stage maps need not be injective. -/
theorem arithmeticSUnitH2FiniteColimitToH2_injective :
    Function.Injective (arithmeticSUnitH2FiniteColimitToH2 K Ω a ha) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  obtain ⟨E, y, rfl⟩ := Module.DirectLimit.exists_of x
  rw [arithmeticSUnitH2FiniteColimitToH2_of K Ω a ha E y] at hx
  letI : TopologicalSpace (arithmeticSUnitFiniteStageRep K Ω a ha E) := ⊥
  letI : DiscreteTopology (arithmeticSUnitFiniteStageRep K Ω a ha E) := ⟨rfl⟩
  obtain ⟨F, hEF, hy⟩ := arithmeticSUnitContinuousH2_zero_detected_at_finiteStage K Ω a ha E y hx
  have hy' : arithmeticSUnitH2Transition K Ω a ha E F hEF y = 0 := hy
  rw [← Module.DirectLimit.of_f (hij := hEF), hy', map_zero]

/-- The actual finite-stage S-unit H2 colimit equals original continuous arithmetic S-unit H2, with no assumed colimit or vanishing certificate. -/
def arithmeticSUnitH2FiniteColimitEquiv :
    ArithmeticSUnitH2FiniteColimit K Ω a ha ≃ₗ[ℤ] ArithmeticSUnitContinuousH2 K Ω a ha :=
  LinearEquiv.ofBijective (arithmeticSUnitH2FiniteColimitToH2 K Ω a ha)
    ⟨arithmeticSUnitH2FiniteColimitToH2_injective K Ω a ha,
      arithmeticSUnitH2FiniteColimitToH2_surjective K Ω a ha⟩

/-- The proved equivalence preserves each original finite-stage class under its literal inflation. -/
theorem arithmeticSUnitH2FiniteColimitEquiv_of
    (F : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
    (x : ArithmeticSUnitH2Stage K Ω a ha F) :
    arithmeticSUnitH2FiniteColimitEquiv K Ω a ha
      (Module.DirectLimit.of ℤ
        (FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
        (ArithmeticSUnitH2Stage K Ω a ha) (arithmeticSUnitH2Transition K Ω a ha) F x) =
      arithmeticSUnitH2StageMap K Ω a ha F x :=
  arithmeticSUnitH2FiniteColimitToH2_of K Ω a ha F x

end
end Dubon2026
