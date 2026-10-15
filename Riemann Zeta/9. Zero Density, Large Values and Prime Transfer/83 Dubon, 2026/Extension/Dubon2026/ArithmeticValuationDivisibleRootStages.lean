import Dubon2026.ValuationDivisibleRootsInUnramifiedUnion
import Dubon2026.UnramifiedUnionFiniteRamification

/-! # Valuation-divisible roots at the literal arithmetic finite stages

The original finite Galois field is enlarged inside the same arithmetic
union to contain a qth root of a field unit with q-divisible outside
valuations. The root equation retains the original inclusion map. This is
the finite-stage input for lifting q-torsion full classes into source classes.
-/

namespace Dubon2026
noncomputable section
open IsDedekindDomain IntermediateField
open scoped NumberField

variable (K Ω : Type) [Field K] [Field Ω] [NumberField K] [Algebra K Ω]
  [IsAlgClosure K Ω] (a : 𝓞 K) (ha : a ≠ 0)
  (q : ℕ) [Fact q.Prime] (hqa : (q : 𝓞 K) ∣ a)
  (E : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))

/-- The original finite arithmetic extension is a number field. -/
local instance valuationRootStageNumberField : NumberField E := NumberField.of_module_finite K E

include ha hqa in
/-- Actual q-divisible outside valuations give an original qth root in a larger actual finite Galois stage of the same union. -/
theorem arithmeticValuationDivisibleUnit_exists_root_stage
    (u : Eˣ)
    (hu : ∀ v : HeightOneSpectrum (𝓞 E), algebraMap (𝓞 K) (𝓞 E) a ∉ v.asIdeal →
      ∃ c : Eˣ, v.valuation E (u : E) = v.valuation E (c : E) ^ q) :
    ∃ (F : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
      (hEF : E ≤ F) (β : Fˣ),
      β ^ q = Units.map (IntermediateField.inclusion hEF).toMonoidHom u := by
  let Γ := originalUnramifiedGaloisUnion (Ω := Ω) a
  letI : IsGalois K Γ := originalUnramifiedGaloisUnion_isGalois a
  let j : E →ₐ[K] Ω := Γ.val.comp E.toIntermediateField.val
  letI : Algebra E Ω := j.toAlgebra
  haveI : IsScalarTower K E Ω := IsScalarTower.of_algHom j
  letI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  obtain ⟨β, hβ⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap E Ω (u : E))
    (Fact.out : q.Prime).pos
  have hβ0 : β ≠ 0 := by
    intro h
    have he := hβ
    rw [h, zero_pow (Fact.out : q.Prime).ne_zero] at he
    exact (map_ne_zero (algebraMap E Ω)).mpr u.ne_zero he.symm
  have hmem : β ∈ Γ := by
    let F := IntermediateField.adjoin E {β}
    have hi : IsIntegral E β := (Algebra.IsIntegral.isIntegral (R := K) β).tower_top
    letI : FiniteDimensional E F := IntermediateField.adjoin.finiteDimensional hi
    letI : NumberField F := NumberField.of_module_finite E F
    letI : Algebra K F := Algebra.compHom F (algebraMap K E)
    letI : IsScalarTower K E F := IsScalarTower.of_algebraMap_eq' rfl
    letI : IsScalarTower K F Ω := IsScalarTower.of_algebraMap_eq' rfl
    letI : FiniteDimensional K F := Module.Finite.trans E F
    let b : F := AdjoinSimple.gen E β
    have hb : b ^ q = algebraMap E F (u : E) := by
      apply F.val.injective
      exact hβ
    have hgen : IntermediateField.adjoin E {b} = ⊤ :=
      IntermediateField.adjoin_eq_top_of_algebra E {b}
        (IntermediateField.adjoin.powerBasis hi).adjoin_gen_eq_top
    have hqE : (q : 𝓞 E) ∣ algebraMap (𝓞 K) (𝓞 E) a := by
      simpa only [map_natCast] using map_dvd (algebraMap (𝓞 K) (𝓞 E)) hqa
    have hF := numberField_unramified_tower (K := K) (L := E) (M := F) a
      (originalUnramifiedUnion_finite_ramification a ha E.toIntermediateField)
      (originalValuationDivisibleKummer_unramifiedAway E F _ q hqE u hu b hb hgen)
    letI : IsGalois K (normalClosure K F Ω) := {}
    let N : FiniteGaloisIntermediateField K Ω := ⟨normalClosure K F Ω⟩
    have hN := numberField_normalClosure_unramified (K := K) (L := F) (Ω := Ω) a ha hF
    let i : F →ₐ[K] Ω := { F.val.toRingHom with commutes' := fun _ => rfl }
    have hbN : β ∈ N.toIntermediateField :=
      i.fieldRange_le_normalClosure ⟨b, rfl⟩
    exact originalUnramifiedGaloisStage_le_union a ⟨N, hN⟩ hbN
  let b : Γ := ⟨β, hmem⟩
  let F := E ⊔ FiniteGaloisIntermediateField.adjoin K {b}
  have hbF : b ∈ F.toIntermediateField :=
    (show (FiniteGaloisIntermediateField.adjoin K {b}).toIntermediateField ≤ F.toIntermediateField from le_sup_right)
      (FiniteGaloisIntermediateField.subset_adjoin K {b} (Set.mem_singleton b))
  have hb0 : (⟨b, hbF⟩ : F) ≠ 0 := by
    intro h
    exact hβ0 (congrArg (fun x : F => x.val.val) h)
  refine ⟨F, le_sup_left, Units.mk0 ⟨b, hbF⟩ hb0, ?_⟩
  apply Units.ext
  apply Subtype.ext
  apply Subtype.ext
  exact hβ

end
end Dubon2026
