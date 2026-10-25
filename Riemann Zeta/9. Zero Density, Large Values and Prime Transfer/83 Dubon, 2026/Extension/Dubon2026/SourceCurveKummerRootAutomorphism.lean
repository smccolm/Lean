import Mathlib.FieldTheory.KummerExtension
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-! DUB-17/18 -> Weil nondegeneracy -> the actual Kummer cover witness.
Adapt the root/automorphism step from anthropics/fermats-last-theorem,
Apache-2.0, commit 6e837e75355538c7f80bab5b956861e86c4eacc2,
S_AlgebraicCurve_DivisorialWeilPairingData_toHom_injective_of_divisible.
Pinned Galois fixed-field and roots-of-unity results produce the witness;
no Picard divisibility or nondegeneracy is asserted here. -/
namespace Dubon2026.SourceCurve.KummerCover
noncomputable section
open Polynomial

theorem root_of_unity_mem_constant_range {K E : Type*} [Field K] [Field E]
    [Algebra K E] (n : ℕ) [NeZero n] [HasEnoughRootsOfUnity K n]
    {u : E} (hu : u ^ n = 1) : u ∈ Set.range (algebraMap K E) := by
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K n
  obtain ⟨i, -, rfl⟩ :=
    (hζ.map_of_injective (algebraMap K E).injective).eq_pow_of_pow_eq_one hu
  exact ⟨ζ ^ i, map_pow _ _ _⟩

theorem exists_root_moved_by_constant (K F : Type*) [Field K] [Field F]
    [Algebra K F] [IsAlgClosed K] [CharZero K] (n : ℕ) [NeZero n]
    (f : F) (hf : f ≠ 0) (hnp : ∀ g : F, g ^ n ≠ f) :
    ∃ (h : (X ^ n - C f).SplittingField)
      (σ : (X ^ n - C f).SplittingField ≃ₐ[F] (X ^ n - C f).SplittingField) (ζ : K),
      ζ ≠ 1 ∧ h ^ n = algebraMap F (X ^ n - C f).SplittingField f ∧
        σ h = algebraMap K (X ^ n - C f).SplittingField ζ * h := by
  haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  haveI : NeZero (n : K) := NeZero.charZero
  let E := (X ^ n - C f).SplittingField
  let h : E := rootOfSplitsXPowSubC (NeZero.pos n) f E
  have hh : h ^ n = algebraMap F E f := rootOfSplitsXPowSubC_pow f E
  have hh0 : h ≠ 0 := by
    intro hz
    rw [hz, zero_pow (NeZero.ne n)] at hh
    exact hf ((algebraMap F E).injective (hh.symm.trans (map_zero _).symm))
  haveI : IsGalois F E := IsGalois.of_separable_splitting_field
    (separable_X_pow_sub_C f (by exact_mod_cast NeZero.ne n) hf)
  have hmove : ∃ σ : E ≃ₐ[F] E, σ h ≠ h := by
    by_contra hall
    push Not at hall
    obtain ⟨a, ha⟩ := (IsGalois.mem_range_algebraMap_iff_fixed h).mpr hall
    have hp : algebraMap F E (a ^ n) = algebraMap F E f := by rw [map_pow, ha, hh]
    exact hnp a ((algebraMap F E).injective hp)
  obtain ⟨σ, hσ⟩ := hmove
  have hroot : (σ h * h⁻¹) ^ n = 1 := by
    rw [mul_pow, inv_pow, ← map_pow, hh, AlgEquiv.commutes, mul_inv_cancel₀]
    exact (_root_.map_ne_zero _).mpr hf
  obtain ⟨ζ, hζ⟩ := root_of_unity_mem_constant_range (K := K) n hroot
  refine ⟨h, σ, ζ, ?_, hh, ?_⟩
  · intro he
    rw [he, map_one, eq_comm, mul_inv_eq_one₀ hh0] at hζ
    exact hσ hζ
  · rw [hζ, inv_mul_cancel_right₀ hh0]

end
end Dubon2026.SourceCurve.KummerCover
