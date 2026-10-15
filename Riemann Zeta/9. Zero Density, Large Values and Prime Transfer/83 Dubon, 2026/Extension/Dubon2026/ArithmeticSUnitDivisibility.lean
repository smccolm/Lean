import Dubon2026.LocalizedUnitRootsInUnramifiedUnion

/-! # Divisibility of the actual arithmetic S-unit coefficients

The coefficient ring is the integral closure of the original localized integer
ring in the constructed unramified Galois union. Its units are q-divisible when
q divides the exceptional integer. Finite-stage descent, unramified root
containment and integrality of roots are proved, rather than postulated.
This supplies the S-unit coefficient input for DUB-17's global-duality route;
the Ext/cohomology comparison and localization exactness are still separate.
-/

namespace Dubon2026
noncomputable section
open IntermediateField
open scoped NumberField

private theorem integralUnit_preimage {R E L : Type} [CommRing R] [Field E] [Field L]
    [Algebra R E] [Algebra R L] (j : E →ₐ[R] L)
    (u : (integralClosure R L)ˣ) (b : E) (hb : j b = u.val.val) :
    ∃ v : (integralClosure R E)ˣ, v.val.val = b := by
  let z : Lˣ := Units.map (integralClosure R L).val.toMonoidHom u
  have hb0 : b ≠ 0 := by
    intro h
    apply z.ne_zero
    change u.val.val = 0
    rw [← hb, h, map_zero]
  have hbI : IsIntegral R b :=
    (isIntegral_algHom_iff j j.injective).mp (hb.symm ▸ u.val.property)
  have hbInv : IsIntegral R b⁻¹ := by
    apply (isIntegral_algHom_iff j j.injective).mp
    rw [map_inv₀, hb]
    exact (Units.val_inv_eq_inv_val z) ▸ (u⁻¹).val.property
  let v : (integralClosure R E)ˣ := {
    val := ⟨b, hbI⟩
    inv := ⟨b⁻¹, hbInv⟩
    val_inv := Subtype.ext (mul_inv_cancel₀ hb0)
    inv_val := Subtype.ext (inv_mul_cancel₀ hb0) }
  exact ⟨v, rfl⟩

private theorem integralUnit_root {R L : Type} [CommRing R] [Field L] [Algebra R L]
    (q : ℕ) (hq : 0 < q) (u : (integralClosure R L)ˣ)
    (z : L) (hz : z ^ q = u.val.val) :
    ∃ v : (integralClosure R L)ˣ, v ^ q = u := by
  have hzI : IsIntegral R z := IsIntegral.of_pow hq (hz.symm ▸ u.val.property)
  let zA : integralClosure R L := ⟨z, hzI⟩
  have hzA : zA ^ q = u.val := Subtype.ext hz
  have hzU : IsUnit zA := (isUnit_pow_iff (Nat.ne_of_gt hq)).mp (hzA.symm ▸ u.isUnit)
  obtain ⟨v, hv⟩ := hzU
  exact ⟨v, Units.ext ((congrArg (fun w : integralClosure R L => w ^ q) hv).trans hzA)⟩

variable (K Ω : Type) [Field K] [Field Ω] [NumberField K]
  [Algebra K Ω] [IsAlgClosure K Ω] (a : 𝓞 K) (ha : a ≠ 0)

/-- The actual integral closure of the localized integer ring in the original
unramified Galois union; its unit group is the arithmetic S-unit coefficient. -/
abbrev OriginalArithmeticSUnitRing :=
  integralClosure (originalLocalizedIntegers K a ha)
    (originalUnramifiedGaloisUnion (Ω := Ω) a)

/-- Every actual arithmetic S-unit descends to a unit of an original localized
integer ring at a constructed finite stage, with its original field value. -/
theorem originalArithmeticSUnit_exists_finiteStage
    (u : (OriginalArithmeticSUnitRing K Ω a ha)ˣ) :
    ∃ (E : IntermediateField K Ω) (hfin : FiniteDimensional K E),
      letI := hfin
      letI : NumberField E := NumberField.of_module_finite K E
      ∃ v : (originalLocalizedIntegers E (algebraMap (𝓞 K) (𝓞 E) a)
          (originalIntegerMap_ne_zero (L := E) a ha))ˣ,
        E ≤ originalUnramifiedGaloisUnion (Ω := Ω) a ∧
          algebraMap E Ω v.val.val = u.val.val.val := by
  let R := originalLocalizedIntegers K a ha
  let Γ := originalUnramifiedGaloisUnion (Ω := Ω) a
  let i : Γ →ₐ[R] Ω := { Γ.val.toRingHom with commutes' := fun _ => rfl }
  let x : Ω := i u.val.val
  let E := IntermediateField.adjoin K {x}
  have hi : IsIntegral K x := Algebra.IsIntegral.isIntegral x
  letI : FiniteDimensional K E := IntermediateField.adjoin.finiteDimensional hi
  letI : NumberField E := NumberField.of_module_finite K E
  have hE : E ≤ Γ := IntermediateField.adjoin_le_iff.mpr
    (Set.singleton_subset_iff.mpr u.val.val.property)
  let b : E := AdjoinSimple.gen K x
  let j : E →ₐ[R] Ω := { E.val.toRingHom with commutes' := fun _ => rfl }
  let uΩ : (integralClosure R Ω)ˣ := Units.map i.mapIntegralClosure.toMonoidHom u
  obtain ⟨vE, hvE⟩ := integralUnit_preimage j uΩ b rfl
  let aE := algebraMap (𝓞 K) (𝓞 E) a
  have haE : aE ≠ 0 := originalIntegerMap_ne_zero (L := E) a ha
  let S := originalLocalizedIntegers E aE haE
  letI : Algebra R S := (originalLocalizedIntegersMap (L := E) a ha).toRingHom.toAlgebra
  letI : IsScalarTower R S E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : IsIntegralClosure S R E := (canonicalLocalizedIntegerAlgebra_data (L := E) a ha).2.1
  let e := IsIntegralClosure.equiv R (integralClosure R E) E S
  let vS : Sˣ := Units.map e.toMonoidHom vE
  have hvS : vS.val.val = b :=
    (IsIntegralClosure.algebraMap_equiv R (integralClosure R E) E S vE.val).trans hvE
  exact ⟨E, inferInstance, vS, hE, congrArg E.val hvS⟩

/-- Every actual arithmetic S-unit has an actual qth root in the same unit group.
Only the original exceptional integer and its coefficient-prime divisibility
are required. Unrestricted field units are not asserted to be q-divisible. -/
theorem originalArithmeticSUnit_pow_surjective
    (q : ℕ) [Fact q.Prime] (hqa : (q : 𝓞 K) ∣ a) :
    Function.Surjective (fun u : (OriginalArithmeticSUnitRing K Ω a ha)ˣ => u ^ q) := by
  intro u
  let Γ := originalUnramifiedGaloisUnion (Ω := Ω) a
  obtain ⟨E, hfin, h⟩ := originalArithmeticSUnit_exists_finiteStage K Ω a ha u
  letI := hfin
  letI : NumberField E := NumberField.of_module_finite K E
  obtain ⟨vS, hE, hvS⟩ := h
  let x : Ω := u.val.val.val
  letI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  obtain ⟨β, hβ⟩ := IsAlgClosed.exists_pow_nat_eq x (Fact.out : q.Prime).pos
  have hβS : β ^ q = algebraMap E Ω vS.val.val :=
    hβ.trans hvS.symm
  have hβΓ := originalLocalizedFiniteStageUnit_root_mem_unramifiedUnion
    K Ω a ha q hqa E hE vS β hβS
  let z : Γ := ⟨β, hβΓ⟩
  have hz : z ^ q = u.val.val := Subtype.ext hβ
  exact integralUnit_root q (Fact.out : q.Prime).pos u z hz

end
end Dubon2026
