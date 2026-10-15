import Dubon2026.ArithmeticSUnitDivisibility
import Dubon2026.DiscreteGaloisUnitActionContinuity
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

/-! # The original discrete arithmetic S-unit representation

The global-duality coefficient is the actual S-unit group, with its original
Galois action and discrete topology. Pinned integral-closure actions and the
existing open-stabilizer theorem discharge stability and action continuity.
The proved root construction makes the actual q-power coefficient map onto.
These supply coefficient inputs; they do not assert global localization exactness.
-/

namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField

variable (K Ω : Type) [Field K] [Field Ω] [NumberField K] [Algebra K Ω]
  (a : 𝓞 K) (ha : a ≠ 0)

/-- Original arithmetic automorphisms fix the original localized base scalars. -/
local instance arithmeticSUnitScalarComm :
    @SMulCommClass Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K)
      (originalLocalizedIntegers K a ha) (originalUnramifiedGaloisUnion (Ω := Ω) a)
      inferInstance
      (inferInstance : Algebra (originalLocalizedIntegers K a ha)
        (originalUnramifiedGaloisUnion (Ω := Ω) a)).toSMul where
  smul_comm g r x := by
    simp only [AlgEquiv.smul_def, Algebra.smul_def]
    rw [map_mul]
    exact congrArg (fun z => z * g x) (g.commutes r.val)

/-- Pinned integral-closure and unit actions restrict the original field automorphisms. -/
local instance arithmeticSUnitAction :
    MulDistribMulAction Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K)
      (OriginalArithmeticSUnitRing K Ω a ha)ˣ :=
  Units.mulDistribMulActionRight

/-- The original S-unit group carries its actual integer-linear arithmetic Galois action. -/
def originalArithmeticSUnitRepresentation :
    Rep ℤ Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K) :=
  Rep.ofMulDistribMulAction Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K)
    (OriginalArithmeticSUnitRing K Ω a ha)ˣ

/-- The genuine coefficient inclusion sends each S-unit to its original field unit. -/
def originalArithmeticSUnitInclusion :
    originalArithmeticSUnitRepresentation K Ω a ha ⟶
      Rep.ofAlgebraAutOnUnits K (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
  Rep.ofHom {
    toLinearMap := (Units.map (OriginalArithmeticSUnitRing K Ω a ha).val.toMonoidHom).toAdditive.toIntLinearMap
    isIntertwining' g := by
      apply LinearMap.ext
      intro x
      rfl }

/-- The original arithmetic S-unit coefficient inclusion is injective. -/
theorem originalArithmeticSUnitInclusion_injective :
    Function.Injective (originalArithmeticSUnitInclusion K Ω a ha).hom.toLinearMap := by
  intro x y h
  apply Rep.toAdditive.injective
  apply Additive.toMul.injective
  apply Units.ext
  apply Subtype.ext
  exact congrArg (fun z => (Additive.toMul (Rep.toAdditive z)).val) h

/-- Its discrete actual Galois action is continuous by algebraic open stabilizers. -/
theorem originalArithmeticSUnitAction_continuous
    [TopologicalSpace (originalArithmeticSUnitRepresentation K Ω a ha)]
    [DiscreteTopology (originalArithmeticSUnitRepresentation K Ω a ha)] :
    Continuous (fun z : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K) ×
      originalArithmeticSUnitRepresentation K Ω a ha =>
        (originalArithmeticSUnitRepresentation K Ω a ha).ρ z.1 z.2) := by
  letI : SMul Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K)
      (OriginalArithmeticSUnitRing K Ω a ha)ˣ :=
    (arithmeticSUnitAction K Ω a ha).toMulAction.toSMul
  letI : MulAction Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K)
      (OriginalArithmeticSUnitRing K Ω a ha)ˣ :=
    (arithmeticSUnitAction K Ω a ha).toMulAction
  letI : IsGalois K (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
    originalUnramifiedGaloisUnion_isGalois a
  letI : TopologicalSpace (OriginalArithmeticSUnitRing K Ω a ha)ˣ :=
    inferInstanceAs (TopologicalSpace (originalArithmeticSUnitRepresentation K Ω a ha))
  letI : DiscreteTopology (OriginalArithmeticSUnitRing K Ω a ha)ˣ :=
    inferInstanceAs (DiscreteTopology (originalArithmeticSUnitRepresentation K Ω a ha))
  letI : ContinuousSMul Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K)
      (OriginalArithmeticSUnitRing K Ω a ha)ˣ :=
    (continuousSMul_iff_stabilizer_isOpen).mpr (by
      intro u
      have he : (MulAction.stabilizer Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K) u :
          Set Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K)) =
          (MulAction.stabilizer Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K) u.val.val :
            Set Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K)) := by
        ext g
        change g • u = u ↔ g u.val.val = u.val.val
        constructor
        · intro h
          exact congrArg (fun v : (OriginalArithmeticSUnitRing K Ω a ha)ˣ => v.val.val) h
        · intro h
          exact Units.ext (Subtype.ext h)
      rw [he]
      exact stabilizer_isOpen_of_isIntegral (K := K) u.val.val)
  exact (show Continuous (fun z : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K) ×
    (OriginalArithmeticSUnitRing K Ω a ha)ˣ => z.1 • z.2) from continuous_smul)

/-- The literal q-power map is an endomorphism of the original S-unit representation. -/
def originalArithmeticSUnitPower (q : ℕ) :
    originalArithmeticSUnitRepresentation K Ω a ha ⟶
      originalArithmeticSUnitRepresentation K Ω a ha :=
  Rep.ofHom {
    toLinearMap := (powMonoidHom q : (OriginalArithmeticSUnitRing K Ω a ha)ˣ →*
      (OriginalArithmeticSUnitRing K Ω a ha)ˣ).toAdditive.toIntLinearMap
    isIntertwining' g := by
      apply LinearMap.ext
      intro x
      exact (smul_pow' g x.toMul q).symm }

/-- The actual coefficient power map is surjective by the proved arithmetic S-unit roots. -/
theorem originalArithmeticSUnitPower_surjective [IsAlgClosure K Ω]
    (q : ℕ) [Fact q.Prime] (hqa : (q : 𝓞 K) ∣ a) :
    Function.Surjective (originalArithmeticSUnitPower K Ω a ha q).hom.toLinearMap := by
  intro x
  obtain ⟨u, hu⟩ := originalArithmeticSUnit_pow_surjective K Ω a ha q hqa
    (Additive.toMul (Rep.toAdditive x))
  exact ⟨Rep.toAdditive.symm (Additive.ofMul u), hu⟩

end
end Dubon2026
