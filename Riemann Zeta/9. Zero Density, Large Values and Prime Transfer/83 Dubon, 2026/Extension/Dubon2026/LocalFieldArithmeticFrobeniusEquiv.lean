import Dubon2026.LocalFieldArithmeticFrobeniusUniqueness
import Dubon2026.LocalFieldIntegerAlgEquiv

namespace Dubon2026
noncomputable section
open scoped ValuativeRel

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

/-- Conjugate a Galois automorphism through compatible equivalences of the
base and extension fields. -/
def localFieldGaloisConjugate
    {K E₀ M₀ E M : Type}
    [Field K] [Field E₀] [Field M₀] [Field E] [Field M]
    [Algebra K E₀] [Algebra K M₀] [Algebra E₀ M₀]
    [Algebra K E] [Algebra K M] [Algebra E M]
    (eE : E₀ ≃ₐ[K] E) (eM : M₀ ≃ₐ[K] M)
    (hcompat : ∀ z : E₀,
      eM (algebraMap E₀ M₀ z) = algebraMap E M (eE z))
    (g₀ : Gal(M₀/E₀)) : Gal(M/E) := {
  toFun := fun z => eM (g₀ (eM.symm z))
  invFun := fun z => eM (g₀.symm (eM.symm z))
  left_inv := by intro z; simp
  right_inv := by intro z; simp
  map_mul' := by intro z w; simp
  map_add' := by intro z w; simp
  commutes' := by
    intro z
    have hinv : eM.symm (algebraMap E M z) =
        algebraMap E₀ M₀ (eE.symm z) := by
      apply eM.injective
      rw [eM.apply_symm_apply]
      calc
        algebraMap E M z = algebraMap E M (eE (eE.symm z)) := by
          rw [eE.apply_symm_apply]
        _ = eM (algebraMap E₀ M₀ (eE.symm z)) := (hcompat _).symm
    rw [hinv, g₀.commutes]
    calc
      eM (algebraMap E₀ M₀ (eE.symm z)) =
          algebraMap E M (eE (eE.symm z)) := hcompat _
      _ = algebraMap E M z := by rw [eE.apply_symm_apply]
}

@[simp] theorem localFieldGaloisConjugate_apply
    {K E₀ M₀ E M : Type}
    [Field K] [Field E₀] [Field M₀] [Field E] [Field M]
    [Algebra K E₀] [Algebra K M₀] [Algebra E₀ M₀]
    [Algebra K E] [Algebra K M] [Algebra E M]
    (eE : E₀ ≃ₐ[K] E) (eM : M₀ ≃ₐ[K] M)
    (hcompat : ∀ z : E₀,
      eM (algebraMap E₀ M₀ z) = algebraMap E M (eE z))
    (g₀ : Gal(M₀/E₀)) (z : M) :
    localFieldGaloisConjugate eE eM hcompat g₀ z = eM (g₀ (eM.symm z)) :=
  rfl

/-- Integer-ring restriction commutes with Galois conjugation through a
compatible equivalence of local-field towers. -/
theorem localFieldIntegerGaloisEquiv_conjugate
    {K E₀ M₀ E M : Type}
    [Field K] [Field E₀] [Field M₀] [Field E] [Field M]
    [Algebra K E₀] [Algebra K M₀] [Algebra E₀ M₀]
    [Algebra K E] [Algebra K M] [Algebra E M]
    [ValuativeRel K] [ValuativeRel E₀] [ValuativeRel M₀]
    [ValuativeRel E] [ValuativeRel M]
    [TopologicalSpace K] [TopologicalSpace E₀] [TopologicalSpace M₀]
    [TopologicalSpace E] [TopologicalSpace M]
    [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField E₀]
    [IsNonarchimedeanLocalField M₀] [IsNonarchimedeanLocalField E]
    [IsNonarchimedeanLocalField M]
    [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation E₀)]
    [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation M₀)]
    [(ValuativeRel.valuation E₀).HasExtension (ValuativeRel.valuation M₀)]
    [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation E)]
    [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation M)]
    [(ValuativeRel.valuation E).HasExtension (ValuativeRel.valuation M)]
    (eE : E₀ ≃ₐ[K] E) (eM : M₀ ≃ₐ[K] M)
    (hcompat : ∀ z : E₀,
      eM (algebraMap E₀ M₀ z) = algebraMap E M (eE z))
    (g₀ : Gal(M₀/E₀)) (z : 𝒪[M₀]) :
    localFieldIntegerGaloisEquiv E M
        (localFieldGaloisConjugate eE eM hcompat g₀)
        (localFieldIntegerAlgEquiv K M₀ M eM z) =
      localFieldIntegerAlgEquiv K M₀ M eM
        (localFieldIntegerGaloisEquiv E₀ M₀ g₀ z) := by
  let eOM := localFieldIntegerAlgEquiv K M₀ M eM
  let g := localFieldGaloisConjugate eE eM hcompat g₀
  apply Subtype.ext
  change algebraMap 𝒪[M] M (localFieldIntegerGaloisEquiv E M g (eOM z)) =
    algebraMap 𝒪[M] M (eOM (localFieldIntegerGaloisEquiv E₀ M₀ g₀ z))
  calc
    _ = g (algebraMap 𝒪[M] M (eOM z)) :=
      localFieldIntegerGaloisEquiv_apply E M g (eOM z)
    _ = eM (g₀ (eM.symm (eM (algebraMap 𝒪[M₀] M₀ z)))) := by
      rw [localFieldIntegerAlgEquiv_coefficient K M₀ M eM]
      rfl
    _ = eM (g₀ (algebraMap 𝒪[M₀] M₀ z)) := by
      rw [eM.symm_apply_apply]
    _ = eM (algebraMap 𝒪[M₀] M₀
        (localFieldIntegerGaloisEquiv E₀ M₀ g₀ z)) := by
      rw [localFieldIntegerGaloisEquiv_apply]
    _ = algebraMap 𝒪[M] M
        (eOM (localFieldIntegerGaloisEquiv E₀ M₀ g₀ z)) :=
      (localFieldIntegerAlgEquiv_coefficient K M₀ M eM _).symm

/-- Arithmetic Frobenius is preserved by compatible equivalences of
unramified local-field towers. -/
theorem localFieldArithmeticFrobenius_conjugate
    {K E₀ M₀ E M : Type}
    [Field K] [Field E₀] [Field M₀] [Field E] [Field M]
    [Algebra K E₀] [Algebra K M₀] [Algebra E₀ M₀]
    [Algebra K E] [Algebra K M] [Algebra E M]
    [IsGalois E₀ M₀] [IsGalois E M]
    [ValuativeRel K] [ValuativeRel E₀] [ValuativeRel M₀]
    [ValuativeRel E] [ValuativeRel M]
    [TopologicalSpace K] [TopologicalSpace E₀] [TopologicalSpace M₀]
    [TopologicalSpace E] [TopologicalSpace M]
    [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField E₀]
    [IsNonarchimedeanLocalField M₀] [IsNonarchimedeanLocalField E]
    [IsNonarchimedeanLocalField M]
    [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation E₀)]
    [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation M₀)]
    [(ValuativeRel.valuation E₀).HasExtension (ValuativeRel.valuation M₀)]
    [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation E)]
    [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation M)]
    [(ValuativeRel.valuation E).HasExtension (ValuativeRel.valuation M)]
    [Algebra.FormallyUnramified 𝒪[E₀] 𝒪[M₀]]
    [Algebra.FormallyUnramified 𝒪[E] 𝒪[M]]
    (eE : E₀ ≃ₐ[K] E) (eM : M₀ ≃ₐ[K] M)
    (hcompat : ∀ z : E₀,
      eM (algebraMap E₀ M₀ z) = algebraMap E M (eE z)) :
    localFieldGaloisConjugate eE eM hcompat
        (localFieldArithmeticFrobenius E₀ M₀) =
      localFieldArithmeticFrobenius E M := by
  let eOE := localFieldIntegerAlgEquiv K E₀ E eE
  let eOM := localFieldIntegerAlgEquiv K M₀ M eM
  letI : IsLocalHom eOM.toRingEquiv.toRingHom :=
    IsLocalHom.of_surjective eOM.toRingEquiv.toRingHom eOM.surjective
  let g₀ := localFieldArithmeticFrobenius E₀ M₀
  let g := localFieldGaloisConjugate eE eM hcompat g₀
  have hcard : Nat.card 𝓀[E₀] = Nat.card 𝓀[E] := by
    exact Nat.card_congr (IsLocalRing.ResidueField.mapEquiv eOE.toRingEquiv).toEquiv
  apply localFieldArithmeticFrobenius_eq_of_residue
  intro z
  let z₀ := eOM.symm z
  have hz : z = eOM z₀ := by simp [z₀]
  calc
    IsLocalRing.residue 𝒪[M] (localFieldIntegerGaloisEquiv E M g z) =
        IsLocalRing.residue 𝒪[M]
          (localFieldIntegerGaloisEquiv E M g (eOM z₀)) := by rw [← hz]
    _ = IsLocalRing.residue 𝒪[M]
          (eOM (localFieldIntegerGaloisEquiv E₀ M₀ g₀ z₀)) := by
      rw [localFieldIntegerGaloisEquiv_conjugate]
    _ = IsLocalRing.residue 𝒪[M] (eOM z₀) ^ Nat.card 𝓀[E] := by
      change IsLocalRing.residue 𝒪[M]
          (eOM.toRingEquiv.toRingHom (localFieldIntegerGaloisEquiv E₀ M₀ g₀ z₀)) =
        IsLocalRing.residue 𝒪[M] (eOM.toRingEquiv.toRingHom z₀) ^ Nat.card 𝓀[E]
      rw [← IsLocalRing.ResidueField.map_residue eOM.toRingEquiv.toRingHom,
        localFieldArithmeticFrobenius_residue E₀ M₀, map_pow, hcard,
        IsLocalRing.ResidueField.map_residue]
    _ = IsLocalRing.residue 𝒪[M] z ^ Nat.card 𝓀[E] := by rw [hz]

end
end Dubon2026

