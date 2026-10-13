import Dubon2026.OriginalKummerRadicalField
import Dubon2026.GaloisRadicalRatioHom

/-! # Abelianity and the exact exponent of the original radical Galois group

Equality is tested on the actual generating roots, using the existing
base-root fixedness and the constructed ratio characters. These discharge
the group-structure inputs for the original S-unit Kummer extension in
the global norm-index and reciprocity route to DUB-17.
-/

namespace Dubon2026
noncomputable section
variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]

/-- An actual prescribed root is a unit in the original field that it helps generate. -/
def originalKummerRootUnit (n : ℕ) [NeZero n] (Δ : Subgroup Kˣ)
    (β : originalKummerRootSet (Ω := Ω) n Δ) : (originalKummerRadicalField (Ω := Ω) n Δ)ˣ :=
  Units.mk0 ⟨β.val, IntermediateField.subset_adjoin K _ β.property⟩ (by
    intro hz
    have hβ : β.val = 0 := congrArg Subtype.val hz
    obtain ⟨a, ha⟩ := β.property
    rw [hβ, zero_pow (NeZero.ne n)] at ha
    exact ((map_ne_zero (algebraMap K Ω)).mpr a.val.ne_zero) ha.symm)

/-- The original root unit retains its prescribed original base-field power. -/
theorem originalKummerRootUnit_pow (n : ℕ) [NeZero n] (Δ : Subgroup Kˣ)
    (β : originalKummerRootSet (Ω := Ω) n Δ) :
    originalKummerRootUnit n Δ β ^ n =
      Units.map (algebraMap K (originalKummerRadicalField (Ω := Ω) n Δ)).toMonoidHom
        β.property.choose.val := by
  apply Units.ext
  apply Subtype.ext
  exact β.property.choose_spec

/-- The Galois group of the actual original radical field is commutative when the base contains μn. -/
theorem originalKummerRadicalField_galois_commutative
    (n : ℕ) [NeZero n] (hζ : (primitiveRoots n K).Nonempty) (Δ : Subgroup Kˣ) :
    IsMulCommutative Gal(originalKummerRadicalField (Ω := Ω) n Δ/K) := by
  refine ⟨⟨fun σ τ => ?_⟩⟩
  apply AlgEquiv.coe_algHom_injective
  apply IntermediateField.adjoin_algHom_ext K
  intro β hβ
  let b : originalKummerRootSet (Ω := Ω) n Δ := ⟨β, hβ⟩
  let u := originalKummerRootUnit n Δ b
  let f := galoisRadicalRatioHom n hζ b.property.choose.val u (originalKummerRootUnit_pow n Δ b)
  have h : f (σ * τ) = f (τ * σ) := by rw [map_mul, map_mul, mul_comm]
  have hu : (σ * τ) • u = (τ * σ) • u := div_left_inj.mp h
  exact congrArg Units.val hu

/-- Every automorphism of the original radical field has nth power equal to the identity. -/
theorem originalKummerRadicalField_galois_pow_eq_one
    (n : ℕ) [NeZero n] (hζ : (primitiveRoots n K).Nonempty) (Δ : Subgroup Kˣ)
    (σ : Gal(originalKummerRadicalField (Ω := Ω) n Δ/K)) : σ ^ n = 1 := by
  apply AlgEquiv.coe_algHom_injective
  apply IntermediateField.adjoin_algHom_ext K
  intro β hβ
  let b : originalKummerRootSet (Ω := Ω) n Δ := ⟨β, hβ⟩
  exact congrArg Units.val (galoisRadicalRatio_pow_fixes n hζ b.property.choose.val
    (originalKummerRootUnit n Δ b) (originalKummerRootUnit_pow n Δ b) σ)

end
end Dubon2026
