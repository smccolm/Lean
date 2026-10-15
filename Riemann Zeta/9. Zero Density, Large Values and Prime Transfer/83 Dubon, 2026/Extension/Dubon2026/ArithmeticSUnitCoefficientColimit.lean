import Dubon2026.ArithmeticSUnitCochainFiniteDescent
import Dubon2026.ArithmeticSUnitFiniteTransitions
import Mathlib.Algebra.Colimit.Module

/-! # The actual arithmetic S-unit coefficient is its finite-stage colimit

Literal finite-stage coefficient inclusions identify the directed limit with
the original arithmetic integral-closure units. A constant continuous cochain
reuses the proved finite-stage descent; no new field construction is needed.
This supplies the ES term of the actual source coefficient sequence required
for DUB-17's global-duality route, separately from the cohomology comparison.
-/

namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [local instance 1100] Rep.hV2

variable (K Ω : Type) [Field K] [Field Ω] [NumberField K] [Algebra K Ω]
  (a : 𝓞 K) (ha : a ≠ 0)

/-- The original finite S-unit coefficient transition as an integer-linear map. -/
def arithmeticSUnitCoefficientTransition
    (E F : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
    (hEF : E ≤ F) : arithmeticSUnitFiniteStageRep K Ω a ha E →ₗ[ℤ]
      arithmeticSUnitFiniteStageRep K Ω a ha F :=
  (arithmeticSUnitFiniteTransitionMap K Ω a ha E F hEF).toAdditive.toIntLinearMap

/-- Original finite S-unit coefficient maps have the same-stage identity law. -/
theorem arithmeticSUnitCoefficientTransition_self
    (E : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
    (x : arithmeticSUnitFiniteStageRep K Ω a ha E) :
    arithmeticSUnitCoefficientTransition K Ω a ha E E le_rfl x = x :=
  congrArg Additive.ofMul (arithmeticSUnitFiniteTransitionMap_refl K Ω a ha E x.toMul)

/-- Original finite S-unit coefficient maps compose under actual field inclusion. -/
theorem arithmeticSUnitCoefficientTransition_comp
    (E F P : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
    (hEF : E ≤ F) (hFP : F ≤ P) (x : arithmeticSUnitFiniteStageRep K Ω a ha E) :
    arithmeticSUnitCoefficientTransition K Ω a ha F P hFP
      (arithmeticSUnitCoefficientTransition K Ω a ha E F hEF x) =
        arithmeticSUnitCoefficientTransition K Ω a ha E P (hEF.trans hFP) x :=
  congrArg Additive.ofMul (arithmeticSUnitFiniteTransitionMap_trans K Ω a ha E F hEF P hFP x.toMul)

/-- The actual S-unit coefficients form their original directed system. -/
instance arithmeticSUnitCoefficientDirectedSystem :
    DirectedSystem (fun F => arithmeticSUnitFiniteStageRep K Ω a ha F)
      (fun E F h => arithmeticSUnitCoefficientTransition K Ω a ha E F h) where
  map_self := fun {E} x => arithmeticSUnitCoefficientTransition_self K Ω a ha E x
  map_map := fun {P F E} hEF hFP x => arithmeticSUnitCoefficientTransition_comp K Ω a ha E F P hEF hFP x

/-- The finite-stage coefficient inclusions preserve their original global values along every transition. -/
theorem arithmeticSUnitCoefficientInclusion_transition
    (E F : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
    (hEF : E ≤ F) (x : arithmeticSUnitFiniteStageRep K Ω a ha E) :
    (arithmeticSUnitFiniteStageInclusion K Ω a ha F).hom
      (arithmeticSUnitCoefficientTransition K Ω a ha E F hEF x) =
        (arithmeticSUnitFiniteStageInclusion K Ω a ha E).hom x :=
  congrArg Additive.ofMul (arithmeticSUnitFiniteTransitionMap_global K Ω a ha E F hEF x.toMul)

/-- Every original arithmetic S-unit coefficient has an actual finite-stage representative. -/
theorem arithmeticSUnitCoefficient_exists_finiteStage
    (x : originalArithmeticSUnitRepresentation K Ω a ha) :
    ∃ F : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a),
      ∃ y : arithmeticSUnitFiniteStageRep K Ω a ha F,
        (arithmeticSUnitFiniteStageInclusion K Ω a ha F).hom y = x := by
  letI : TopologicalSpace (originalArithmeticSUnitRepresentation K Ω a ha) := ⊥
  letI : DiscreteTopology (originalArithmeticSUnitRepresentation K Ω a ha) := ⟨rfl⟩
  let b : C(Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K),
      originalArithmeticSUnitRepresentation K Ω a ha) := ContinuousMap.const _ x
  have hd := arithmeticSUnitCochain_exists_finite_descent K Ω a ha ⊥ b
  let F := hd.choose
  let f := hd.choose_spec.2.choose
  have hf := hd.choose_spec.2.choose_spec
  exact ⟨F, Additive.ofMul (f (AlgEquiv.restrictNormalHom F 1)), congrArg Additive.ofMul (hf 1)⟩

variable [DecidableEq (FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))]

/-- The actual module direct limit of the original finite S-unit coefficients. -/
abbrev ArithmeticSUnitCoefficientColimit :=
  Module.DirectLimit (fun F => arithmeticSUnitFiniteStageRep K Ω a ha F)
    (arithmeticSUnitCoefficientTransition K Ω a ha)

/-- The universal map induced by the literal original arithmetic coefficient inclusions. -/
def arithmeticSUnitCoefficientColimitToGlobal :
    ArithmeticSUnitCoefficientColimit K Ω a ha →ₗ[ℤ] originalArithmeticSUnitRepresentation K Ω a ha :=
  Module.DirectLimit.lift ℤ
    (FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
    (fun F => arithmeticSUnitFiniteStageRep K Ω a ha F) (arithmeticSUnitCoefficientTransition K Ω a ha)
    (fun F => (arithmeticSUnitFiniteStageInclusion K Ω a ha F).hom.toLinearMap)
    (arithmeticSUnitCoefficientInclusion_transition K Ω a ha)

/-- The original coefficient-colimit map has the literal finite-stage field inclusion as its representative formula. -/
theorem arithmeticSUnitCoefficientColimitToGlobal_of
    (F : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
    (x : arithmeticSUnitFiniteStageRep K Ω a ha F) :
    arithmeticSUnitCoefficientColimitToGlobal K Ω a ha
      (Module.DirectLimit.of ℤ
        (FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
        (fun F => arithmeticSUnitFiniteStageRep K Ω a ha F)
        (arithmeticSUnitCoefficientTransition K Ω a ha) F x) =
      (arithmeticSUnitFiniteStageInclusion K Ω a ha F).hom x :=
  Module.DirectLimit.lift_of
    (R := ℤ)
    (ι := FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
    (G := fun F => arithmeticSUnitFiniteStageRep K Ω a ha F)
    (f := arithmeticSUnitCoefficientTransition K Ω a ha)
    (fun F => (arithmeticSUnitFiniteStageInclusion K Ω a ha F).hom.toLinearMap)
    (arithmeticSUnitCoefficientInclusion_transition K Ω a ha) (i := F) x

/-- Actual finite-stage S-unit descent proves that the original coefficient-colimit map is onto. -/
theorem arithmeticSUnitCoefficientColimitToGlobal_surjective :
    Function.Surjective (arithmeticSUnitCoefficientColimitToGlobal K Ω a ha) := by
  intro x
  obtain ⟨F, y, hy⟩ := arithmeticSUnitCoefficient_exists_finiteStage K Ω a ha x
  exact ⟨Module.DirectLimit.of ℤ
    (FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
    (fun F => arithmeticSUnitFiniteStageRep K Ω a ha F)
    (arithmeticSUnitCoefficientTransition K Ω a ha) F y,
    (arithmeticSUnitCoefficientColimitToGlobal_of K Ω a ha F y).trans hy⟩

/-- Actual finite-stage field injectivity proves that the original coefficient-colimit map is injective. -/
theorem arithmeticSUnitCoefficientColimitToGlobal_injective :
    Function.Injective (arithmeticSUnitCoefficientColimitToGlobal K Ω a ha) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  obtain ⟨F, y, rfl⟩ := Module.DirectLimit.exists_of x
  rw [arithmeticSUnitCoefficientColimitToGlobal_of K Ω a ha F y] at hx
  have hy : y = 0 := by
    apply Additive.toMul.injective
    apply arithmeticSUnitFiniteStageUnitMap_injective K Ω a ha F
    exact congrArg Additive.toMul
      (hx.trans (map_zero (arithmeticSUnitFiniteStageInclusion K Ω a ha F).hom).symm)
  rw [hy, map_zero]

/-- The actual arithmetic S-unit coefficient equals its original finite-stage module colimit. -/
def arithmeticSUnitCoefficientColimitEquiv :
    ArithmeticSUnitCoefficientColimit K Ω a ha ≃ₗ[ℤ] originalArithmeticSUnitRepresentation K Ω a ha :=
  LinearEquiv.ofBijective (arithmeticSUnitCoefficientColimitToGlobal K Ω a ha)
    ⟨arithmeticSUnitCoefficientColimitToGlobal_injective K Ω a ha,
      arithmeticSUnitCoefficientColimitToGlobal_surjective K Ω a ha⟩

end
end Dubon2026
