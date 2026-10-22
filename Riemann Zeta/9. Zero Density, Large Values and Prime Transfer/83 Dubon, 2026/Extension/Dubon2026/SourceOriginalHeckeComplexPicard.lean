import Dubon2026.SourceOriginalHeckeComplexDivisors
import Dubon2026.SourceOriginalHeckePicard
import Dubon2026.SourceOriginalComplexPicardMap

/-! DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> modular residual
Galois association -> original Tate Hecke realization. The already proved
coefficient identities for the actual alpha and beta maps discharge the
field-commutation premises of conorm naturality. Consequently the literal
arithmetic-to-complex Picard map intertwines the genuine Hecke operators.
-/
namespace Dubon2026.SourceFunctionField.OriginalConstantField
noncomputable section
open SourceCurve
local notation "Qbar" => AlgebraicClosure ℚ
variable (N ℓ : ℕ) [NeZero N] [NeZero ℓ]

theorem conorm_originalHeckeDivisor (D : Divisor Qbar (modularFunctionFieldOver N Qbar)) :
    conorm N (originalHeckeDivisor Qbar N ℓ D) =
      originalHeckeDivisor ℂ N ℓ (conorm N D) := by
  change conorm N (Divisor.geometricPushforwardAlong (originalHeckeAlpha Qbar N ℓ)
    (originalHeckeAlpha_finite Qbar N ℓ)
    (Divisor.finitePullbackAlong (originalHeckeBeta Qbar N ℓ)
      (originalHeckeBeta_finite Qbar N ℓ) D)) = _
  rw [geometricPushforwardAlong_conorm N (N * ℓ)
    (originalHeckeAlpha Qbar N ℓ) (originalHeckeAlpha ℂ N ℓ)
    (originalHeckeAlpha_finite Qbar N ℓ) (originalHeckeAlpha_finite ℂ N ℓ)
    (originalHeckeAlpha_fieldMap N ℓ)]
  rw [finitePullbackAlong_conorm N (N * ℓ)
    (originalHeckeBeta Qbar N ℓ) (originalHeckeBeta ℂ N ℓ)
    (originalHeckeBeta_finite Qbar N ℓ) (originalHeckeBeta_finite ℂ N ℓ)
    (originalHeckeBeta_fieldMap N ℓ)]
  rfl

theorem complexPicardMap_originalHeckePicard (x : originalJZero N) :
    complexPicardMap N (originalHeckePicard Qbar N ℓ x) =
      originalHeckePicard ℂ N ℓ (complexPicardMap N x) := by
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective x
  rw [originalHeckePicard_mk, complexPicardMap_mk,
    complexPicardMap_mk, originalHeckePicard_mk]
  apply congrArg Pic0.mk
  apply Subtype.ext
  exact conorm_originalHeckeDivisor N ℓ D.val

end
end Dubon2026.SourceFunctionField.OriginalConstantField
