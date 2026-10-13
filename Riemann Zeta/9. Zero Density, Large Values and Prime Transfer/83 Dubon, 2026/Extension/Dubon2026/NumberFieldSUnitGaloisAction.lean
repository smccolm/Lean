/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the upstream LICENSE.
S-unit stability adapted from NYLL ClassFieldTheory, commit
dc55774a7fe03e742f2b4c6114aab5e7d01edfb1,
Nyll/ClassFieldTheory/AlgebraicNumberTheory/SUnit/GaloisAction.lean.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Dubon2026.NumberFieldGaloisValuation
import Mathlib.RingTheory.DedekindDomain.SInteger
import Mathlib.FieldTheory.Galois.Basic

/-! # The actual Galois action on the original S-unit group

The proved simultaneous valuation transport restricts the usual original
field-unit action to a stable S. Finite original Galois orbits supply such
a finite enlargement of every prescribed support. This is the coefficient
action required by DUB-17's supported-idele cohomology, not a trivial action.
-/

namespace Dubon2026
noncomputable section
open IsDedekindDomain
open scoped NumberField
variable (K L : Type) [Field K] [Field L] [Algebra K L]

/-- The original field-unit action preserves the original S-units for an actual stable support. -/
theorem numberField_sUnit_galois_mem [NumberField L]
    (S : Set (HeightOneSpectrum (𝓞 L)))
    (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)
    (σ : Gal(L/K)) (x : Lˣ) (hx : x ∈ S.unit L) : σ • x ∈ S.unit L := by
  intro v hv
  let w := numberFieldGaloisPlaceEquiv K L σ⁻¹ v
  have hw : w ∉ S := fun h => hv ((hS σ⁻¹ v).mpr h)
  have hval := numberFieldGaloisPlace_valuation K L σ w x.val
  have hvw : numberFieldGaloisPlaceEquiv K L σ w = v := by
    rw [← numberFieldGaloisPlaceEquiv_mul, mul_inv_cancel, numberFieldGaloisPlaceEquiv_one]
  rw [hvw] at hval
  change v.valuation L (σ x.val) = 1
  exact hval.trans (hx w hw)

/-- The usual original Galois action restricted to the original S-unit subgroup. -/
@[reducible]
def numberFieldSUnitGaloisAction [NumberField L]
    (S : Set (HeightOneSpectrum (𝓞 L)))
    (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S) :
    MulDistribMulAction Gal(L/K) (S.unit L) where
  smul σ x := ⟨σ • x.val, numberField_sUnit_galois_mem K L S hS σ x.val x.property⟩
  one_smul x := Subtype.ext (one_smul _ x.val)
  mul_smul σ τ x := Subtype.ext (mul_smul σ τ x.val)
  smul_one σ := Subtype.ext (smul_one σ)
  smul_mul σ x y := Subtype.ext (smul_mul' σ x.val y.val)

/-- Finitely many original Galois orbits give a finite stable enlargement of every prescribed support. -/
theorem numberField_exists_finite_galoisStable_support [FiniteDimensional K L]
    (S₀ : Finset (HeightOneSpectrum (𝓞 L))) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 L)), S₀ ⊆ S ∧
      ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S := by
  classical
  letI : Fintype Gal(L/K) := Fintype.ofFinite _
  let S := Finset.univ.biUnion fun σ : Gal(L/K) => S₀.image (numberFieldGaloisPlaceEquiv K L σ)
  have hmul (σ : Gal(L/K)) {v : HeightOneSpectrum (𝓞 L)} (hv : v ∈ S) :
      numberFieldGaloisPlaceEquiv K L σ v ∈ S := by
    obtain ⟨τ, _, hv⟩ := Finset.mem_biUnion.mp hv
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
    exact Finset.mem_biUnion.mpr ⟨σ * τ, Finset.mem_univ _,
      Finset.mem_image.mpr ⟨u, hu, numberFieldGaloisPlaceEquiv_mul K L σ τ u⟩⟩
  refine ⟨S, ?_, ?_⟩
  · intro v hv
    exact Finset.mem_biUnion.mpr ⟨1, Finset.mem_univ _,
      Finset.mem_image.mpr ⟨v, hv, numberFieldGaloisPlaceEquiv_one K L v⟩⟩
  · intro σ v
    refine ⟨hmul σ, fun h => ?_⟩
    have h' := hmul σ⁻¹ h
    rw [← numberFieldGaloisPlaceEquiv_mul, inv_mul_cancel, numberFieldGaloisPlaceEquiv_one] at h'
    exact h'

end
end Dubon2026
