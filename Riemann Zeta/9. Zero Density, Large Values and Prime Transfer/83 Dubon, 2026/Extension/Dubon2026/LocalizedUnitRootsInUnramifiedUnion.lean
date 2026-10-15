import Dubon2026.LocalizedUnitKummerAlgebra
import Dubon2026.UnramifiedNormalClosure
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Actual localized-unit roots in the original unramified Galois union

This is the root-containment step for the S-unit coefficients in DUB-17's
global-duality dependency. The finite root field, its generation and its
unramified normal closure are all derived from the literal root equation.
The full S-unit divisibility and cohomological comparisons remain separate.
-/

namespace Dubon2026
noncomputable section
open IntermediateField
open scoped NumberField

variable (K Ω : Type) [Field K] [Field Ω] [NumberField K]
  [Algebra K Ω] [IsAlgClosure K Ω]
  (a : 𝓞 K) (ha : a ≠ 0) (q : ℕ) [Fact q.Prime] (hqa : (q : 𝓞 K) ∣ a)

include hqa in
/-- Every actual qth root of an original localized integer unit belongs to the
original unramified Galois union when the exceptional integer contains q. -/
theorem originalLocalizedUnit_root_mem_unramifiedUnion
    (u : (originalLocalizedIntegers K a ha)ˣ) (β : Ω)
    (hβ : β ^ q = algebraMap K Ω u.val.val) :
    β ∈ originalUnramifiedGaloisUnion (Ω := Ω) a := by
  let E := IntermediateField.adjoin K {β}
  have hi : IsIntegral K β := Algebra.IsIntegral.isIntegral β
  letI : FiniteDimensional K E := IntermediateField.adjoin.finiteDimensional hi
  letI : NumberField E := NumberField.of_module_finite K E
  let b : E := AdjoinSimple.gen K β
  have hb : b ^ q = algebraMap (originalLocalizedIntegers K a ha) E u.val := by
    apply E.val.injective
    exact hβ
  have hgen : IntermediateField.adjoin K {b} = ⊤ :=
    IntermediateField.adjoin_eq_top_of_algebra K {b}
      (IntermediateField.adjoin.powerBasis hi).adjoin_gen_eq_top
  have hE : E ≤ originalUnramifiedGaloisUnion (Ω := Ω) a :=
    (originalUnramifiedUnion_finite_le_iff a ha E).mpr
      (originalLocalizedUnitKummer_unramifiedAway K a ha q E u b hb hqa hgen)
  exact hE (IntermediateField.subset_adjoin K {β} (Set.mem_singleton β))

include hqa in
/-- A qth root of each original localized unit exists in the actual arithmetic
extension itself; no unramifiedness or root-containment premise remains. -/
theorem originalLocalizedUnit_exists_root_in_unramifiedUnion
    (u : (originalLocalizedIntegers K a ha)ˣ) :
    ∃ β : originalUnramifiedGaloisUnion (Ω := Ω) a,
      β ^ q = algebraMap K (originalUnramifiedGaloisUnion (Ω := Ω) a) u.val.val := by
  letI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  obtain ⟨β, hβ⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap K Ω u.val.val)
    (Fact.out : q.Prime).pos
  refine ⟨⟨β, originalLocalizedUnit_root_mem_unramifiedUnion K Ω a ha q hqa u β hβ⟩, ?_⟩
  exact Subtype.ext hβ

include hqa in
/-- Roots of actual localized units at any original finite arithmetic stage
remain in the original base-field unramified Galois union. The original tower
indices and normal closure discharge the change-of-base containment. -/
theorem originalLocalizedFiniteStageUnit_root_mem_unramifiedUnion
    (E : IntermediateField K Ω) [FiniteDimensional K E] [NumberField E]
    (hE : E ≤ originalUnramifiedGaloisUnion (Ω := Ω) a)
    (u : (originalLocalizedIntegers E (algebraMap (𝓞 K) (𝓞 E) a)
      (originalIntegerMap_ne_zero (L := E) a ha))ˣ)
    (β : Ω) (hβ : β ^ q = algebraMap E Ω u.val.val) :
    β ∈ originalUnramifiedGaloisUnion (Ω := Ω) a := by
  let aE := algebraMap (𝓞 K) (𝓞 E) a
  have haE : aE ≠ 0 := originalIntegerMap_ne_zero (L := E) a ha
  have hqE : (q : 𝓞 E) ∣ aE := by
    simpa only [map_natCast] using map_dvd (algebraMap (𝓞 K) (𝓞 E)) hqa
  let F := IntermediateField.adjoin E {β}
  have hi : IsIntegral E β := (Algebra.IsIntegral.isIntegral (R := K) β).tower_top
  letI : FiniteDimensional E F := IntermediateField.adjoin.finiteDimensional hi
  letI : NumberField F := NumberField.of_module_finite E F
  letI : Algebra K F := Algebra.compHom F (algebraMap K E)
  letI : IsScalarTower K E F := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower K F Ω := IsScalarTower.of_algebraMap_eq' rfl
  letI : FiniteDimensional K F := Module.Finite.trans E F
  let b : F := AdjoinSimple.gen E β
  have hb : b ^ q = algebraMap (originalLocalizedIntegers E aE haE) F u.val := by
    apply F.val.injective
    exact hβ
  have hgen : IntermediateField.adjoin E {b} = ⊤ :=
    IntermediateField.adjoin_eq_top_of_algebra E {b}
      (IntermediateField.adjoin.powerBasis hi).adjoin_gen_eq_top
  have hF := numberField_unramified_tower (K := K) (L := E) (M := F) a
    (originalUnramifiedUnion_ambient_finite_ramification a ha E hE)
    (originalLocalizedUnitKummer_unramifiedAway E aE haE q F u b hb hqE hgen)
  letI : IsGalois K (normalClosure K F Ω) := {}
  let N : FiniteGaloisIntermediateField K Ω := ⟨normalClosure K F Ω⟩
  have hN := numberField_normalClosure_unramified (Ω := Ω) a ha hF
  have hbN : β ∈ N.toIntermediateField :=
    (F.val.restrictScalars K).fieldRange_le_normalClosure ⟨b, rfl⟩
  exact originalUnramifiedGaloisStage_le_union a ⟨N, hN⟩ hbN

end
end Dubon2026
