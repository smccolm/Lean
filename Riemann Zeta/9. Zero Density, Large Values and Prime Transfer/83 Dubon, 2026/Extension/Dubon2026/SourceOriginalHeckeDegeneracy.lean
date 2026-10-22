import Dubon2026.SourceOriginalFieldTowerDegree
import Dubon2026.SourceOriginalSlotRange
import Dubon2026.SourceLaurentCoefficientReindex

/-! DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> arithmetic modular Galois
association -> Hecke/Frobenius comparison -> the actual original Picard Hecke
correspondence. These are its two literal function-field maps. Existing
divisor-field inclusion and Laurent substitution supply the maps directly.
Finiteness, divisor pullback/pushforward and period compatibility are separate.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
Definitions/Def_ModularCurve_HeckeOperator.lean and Def_ModularCurve_X0.lean.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open IntermediateField

theorem original_full_degeneracy_map_le (N ℓ : ℕ) [NeZero ℓ] :
    (modularFunctionFieldFull N).map (qExpandAlgHom ℚ ℓ) ≤
      modularFunctionFieldFull (N * ℓ) := by
  rw [modularFunctionFieldFull, adjoin_map, adjoin_le_iff]
  rintro x ⟨y, ⟨d, hd, hdN, rfl⟩, rfl⟩
  haveI := hd
  change qExpand ℚ ℓ (qExpand ℚ d jq) ∈ _
  rw [qExpand_qExpand]
  exact jqd_mem_full (N * ℓ)
    ((mul_dvd_mul_left ℓ hdN).trans (dvd_of_eq (mul_comm ℓ N)))

variable (L : Type*) [Field L] [Algebra ℚ L]

theorem original_over_mono_of_dvd {M N : ℕ} (hMN : M ∣ N) :
    modularFunctionFieldOver M L ≤ modularFunctionFieldOver N L := by
  rw [modularFunctionFieldOver, laurentBaseChange, adjoin_le_iff]
  rintro x ⟨y, hy, rfl⟩
  exact coeffEmb_mem_laurentBaseChange L (original_full_mono_of_dvd hMN hy)

theorem original_over_degeneracy_map_le (N ℓ : ℕ) [NeZero ℓ] :
    (modularFunctionFieldOver N L).map (qExpandAlgHom L ℓ) ≤
      modularFunctionFieldOver (N * ℓ) L := by
  rw [modularFunctionFieldOver, laurentBaseChange, adjoin_map, adjoin_le_iff]
  rintro x ⟨y, ⟨z, hz, rfl⟩, rfl⟩
  change qExpand L ℓ (coeffMap (algebraMap ℚ L) z) ∈ _
  rw [← coeffMap_qExpand]
  exact coeffEmb_mem_laurentBaseChange L
    (original_full_degeneracy_map_le N ℓ ⟨z, hz, rfl⟩)

/-- The original first degeneracy map is the literal inclusion of Laurent fields. -/
def originalHeckeAlpha (N ℓ : ℕ) :
    modularFunctionFieldOver N L →ₐ[L] modularFunctionFieldOver (N * ℓ) L :=
  IntermediateField.inclusion (original_over_mono_of_dvd L (dvd_mul_right N ℓ))

@[simp] theorem originalHeckeAlpha_coe (N ℓ : ℕ) (x : modularFunctionFieldOver N L) :
    (originalHeckeAlpha L N ℓ x : LaurentSeries L) = (x : LaurentSeries L) :=
  IntermediateField.coe_inclusion _ x

/-- The original second degeneracy map substitutes q to q raised to ℓ. -/
def originalHeckeBeta (N ℓ : ℕ) [NeZero ℓ] :
    modularFunctionFieldOver N L →ₐ[L] modularFunctionFieldOver (N * ℓ) L where
  toFun x := ⟨qExpand L ℓ x,
    original_over_degeneracy_map_le L N ℓ ⟨x, x.2, rfl⟩⟩
  map_one' := Subtype.ext (map_one (qExpand L ℓ))
  map_mul' x y := Subtype.ext (map_mul (qExpand L ℓ) (x : LaurentSeries L) (y : LaurentSeries L))
  map_zero' := Subtype.ext (map_zero (qExpand L ℓ))
  map_add' x y := Subtype.ext (map_add (qExpand L ℓ) (x : LaurentSeries L) (y : LaurentSeries L))
  commutes' c := Subtype.ext ((qExpandAlgHom L ℓ).commutes c)

@[simp] theorem originalHeckeBeta_coe (N ℓ : ℕ) [NeZero ℓ]
    (x : modularFunctionFieldOver N L) :
    (originalHeckeBeta L N ℓ x : LaurentSeries L) = qExpand L ℓ x := rfl

end
end Dubon2026.SourceFunctionField
