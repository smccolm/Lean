import Dubon2026.ArithmeticSUnitH2FiniteTransitions
import Mathlib.Algebra.Colimit.Module

/-! # The original arithmetic S-unit H2 directed system

These are the actual finite Galois S-unit coefficients, with their original
actions and transition maps. The two directed-system laws are proved on
literal cocycle values, so the subsequent colimit adds no compatibility premise.
-/

namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [local instance 1100] Rep.hV2

variable (K Ω : Type) [Field K] [Field Ω] [NumberField K] [Algebra K Ω]
  (a : 𝓞 K) (ha : a ≠ 0)

/-- The original finite-stage S-unit H2 with discrete coefficients. -/
abbrev ArithmeticSUnitH2Stage
    (F : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a)) :=
  letI : TopologicalSpace (arithmeticSUnitFiniteStageRep K Ω a ha F) := ⊥
  letI : DiscreteTopology (arithmeticSUnitFiniteStageRep K Ω a ha F) := ⟨rfl⟩
  ArithmeticSUnitFiniteStageH2 K Ω a ha F

/-- The actual finite-stage transition on the fixed discrete cohomology quotients. -/
def arithmeticSUnitH2Transition
    (E F : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
    (hEF : E ≤ F) : ArithmeticSUnitH2Stage K Ω a ha E →ₗ[ℤ] ArithmeticSUnitH2Stage K Ω a ha F := by
  letI : TopologicalSpace (arithmeticSUnitFiniteStageRep K Ω a ha E) := ⊥
  letI : DiscreteTopology (arithmeticSUnitFiniteStageRep K Ω a ha E) := ⟨rfl⟩
  letI : TopologicalSpace (arithmeticSUnitFiniteStageRep K Ω a ha F) := ⊥
  letI : DiscreteTopology (arithmeticSUnitFiniteStageRep K Ω a ha F) := ⟨rfl⟩
  exact arithmeticSUnitFiniteTowerH2Inflation K Ω a ha E F hEF

/-- The original same-stage S-unit H2 transition is the identity. -/
theorem arithmeticSUnitH2Transition_self
    (E : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
    (x : ArithmeticSUnitH2Stage K Ω a ha E) :
    arithmeticSUnitH2Transition K Ω a ha E E le_rfl x = x := by
  letI : Algebra E E := (IntermediateField.inclusion (le_refl E.toIntermediateField)).toAlgebra
  letI : TopologicalSpace (arithmeticSUnitFiniteStageRep K Ω a ha E) := ⊥
  letI : DiscreteTopology (arithmeticSUnitFiniteStageRep K Ω a ha E) := ⟨rfl⟩
  have hj (g : Gal(E/K)) : AlgEquiv.restrictNormalHom E g = g := by
    apply AlgEquiv.ext
    intro y
    exact AlgEquiv.restrictNormal_commutes g E y
  induction x using Submodule.Quotient.induction_on with
  | H c =>
    change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
    congr 1
    apply Subtype.ext
    apply Subtype.ext
    funext z
    apply Additive.toMul.injective
    change arithmeticSUnitFiniteTransitionMap K Ω a ha E E le_rfl
      (c.val (AlgEquiv.restrictNormalHom E z.1, AlgEquiv.restrictNormalHom E z.2)).toMul =
        (c.val z).toMul
    have hz : (AlgEquiv.restrictNormalHom E z.1, AlgEquiv.restrictNormalHom E z.2) = z :=
      Prod.ext (hj z.1) (hj z.2)
    exact (arithmeticSUnitFiniteTransitionMap_refl K Ω a ha E _).trans
      (congrArg (fun w => (c.val w).toMul) hz)

/-- Actual S-unit H2 transitions compose along the same inclusions of finite fields. -/
theorem arithmeticSUnitH2Transition_comp
    (E F P : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
    (hEF : E ≤ F) (hFP : F ≤ P) (x : ArithmeticSUnitH2Stage K Ω a ha E) :
    arithmeticSUnitH2Transition K Ω a ha F P hFP
      (arithmeticSUnitH2Transition K Ω a ha E F hEF x) =
        arithmeticSUnitH2Transition K Ω a ha E P (hEF.trans hFP) x := by
  letI : Algebra E F := (IntermediateField.inclusion hEF).toAlgebra
  letI : Algebra F P := (IntermediateField.inclusion hFP).toAlgebra
  letI : Algebra E P := (IntermediateField.inclusion (hEF.trans hFP)).toAlgebra
  haveI : IsScalarTower E F P := .of_algebraMap_eq' rfl
  letI : TopologicalSpace (arithmeticSUnitFiniteStageRep K Ω a ha E) := ⊥
  letI : DiscreteTopology (arithmeticSUnitFiniteStageRep K Ω a ha E) := ⟨rfl⟩
  letI : TopologicalSpace (arithmeticSUnitFiniteStageRep K Ω a ha F) := ⊥
  letI : DiscreteTopology (arithmeticSUnitFiniteStageRep K Ω a ha F) := ⟨rfl⟩
  letI : TopologicalSpace (arithmeticSUnitFiniteStageRep K Ω a ha P) := ⊥
  letI : DiscreteTopology (arithmeticSUnitFiniteStageRep K Ω a ha P) := ⟨rfl⟩
  induction x using Submodule.Quotient.induction_on with
  | H c =>
    change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
    congr 1
    apply Subtype.ext
    apply Subtype.ext
    funext z
    apply Additive.toMul.injective
    change arithmeticSUnitFiniteTransitionMap K Ω a ha F P hFP
      (arithmeticSUnitFiniteTransitionMap K Ω a ha E F hEF
        (c.val (AlgEquiv.restrictNormalHom E (AlgEquiv.restrictNormalHom F z.1),
          AlgEquiv.restrictNormalHom E (AlgEquiv.restrictNormalHom F z.2))).toMul) =
      arithmeticSUnitFiniteTransitionMap K Ω a ha E P (hEF.trans hFP)
        (c.val (AlgEquiv.restrictNormalHom E z.1, AlgEquiv.restrictNormalHom E z.2)).toMul
    have hz : (AlgEquiv.restrictNormalHom E z.1, AlgEquiv.restrictNormalHom E z.2) =
        (AlgEquiv.restrictNormalHom E (AlgEquiv.restrictNormalHom F z.1),
          AlgEquiv.restrictNormalHom E (AlgEquiv.restrictNormalHom F z.2)) := Prod.ext
      (IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply E F z.1)
      (IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply E F z.2)
    exact (arithmeticSUnitFiniteTransitionMap_trans K Ω a ha E F hEF P hFP _).trans
      (congrArg (fun w => arithmeticSUnitFiniteTransitionMap K Ω a ha E P (hEF.trans hFP)
        (c.val w).toMul) hz.symm)

/-- The original arithmetic S-unit H2 maps satisfy both directed-system laws. -/
instance arithmeticSUnitH2DirectedSystem :
    DirectedSystem (ArithmeticSUnitH2Stage K Ω a ha)
      (fun E F h => arithmeticSUnitH2Transition K Ω a ha E F h) where
  map_self := fun {E} x => arithmeticSUnitH2Transition_self K Ω a ha E x
  map_map := fun {P F E} hEF hFP x => arithmeticSUnitH2Transition_comp K Ω a ha E F P hEF hFP x

end
end Dubon2026
