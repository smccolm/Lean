import Dubon2026.SourceCurvePicardCorrespondence
import Dubon2026.SourceOriginalHeckeFinite
import Dubon2026.SourceOriginalResidueFinite

/-! DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> modular residual Galois
association -> Hecke/Frobenius comparison -> the actual original Picard
Hecke operator. The two literal degeneracy maps are finite by the original
j-coordinate theory. Every actual residue field equals the algebraically
closed constants. The proved pullback-degree and pushforward-norm identities
therefore define the source correspondence on the actual Picard group.
Arithmetic equivariance, period compatibility, rank-two realization and
Frobenius/inertia identities remain separate obligations.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
Definitions/Def_ModularCurve_HeckeOperator.lean, heckeDivBar and heckePic0Bar.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve
variable (L : Type*) [Field L] [Algebra ℚ L] [CharZero L] [IsAlgClosed L]
variable (N ℓ : ℕ) [NeZero N] [NeZero ℓ]

/-- The literal original Hecke divisor correspondence, β pullback followed by α pushforward. -/
def originalHeckeDivisor :
    Divisor L (modularFunctionFieldOver N L) →+ Divisor L (modularFunctionFieldOver N L) :=
  Divisor.geometricCorrespondence (originalHeckeBeta L N ℓ) (originalHeckeAlpha L N ℓ)
    (originalHeckeBeta_finite L N ℓ) (originalHeckeAlpha_finite L N ℓ)

theorem originalHeckeDivisor_mem_degZero {D : Divisor L (modularFunctionFieldOver N L)}
    (hD : D ∈ Divisor.degZero) : originalHeckeDivisor L N ℓ D ∈ Divisor.degZero :=
  Divisor.geometricCorrespondence_mem_degZero _ _ _ _
    (original_place_residue_algebraMap_bijective N L)
    (original_place_residue_algebraMap_bijective (N * ℓ) L) hD

theorem isPrincipal_originalHeckeDivisor {D : Divisor L (modularFunctionFieldOver N L)}
    (hD : Divisor.IsPrincipal D) : Divisor.IsPrincipal (originalHeckeDivisor L N ℓ D) :=
  Divisor.isPrincipal_geometricCorrespondence _ _ _ _
    (original_place_residue_algebraMap_bijective N L)
    (original_place_residue_algebraMap_bijective (N * ℓ) L) hD

/-- The original Hecke endomorphism of genuine degree-zero divisor classes. -/
def originalHeckePicard :
    Pic0 L (modularFunctionFieldOver N L) →+ Pic0 L (modularFunctionFieldOver N L) :=
  Pic0.geometricCorrespondence (originalHeckeBeta L N ℓ) (originalHeckeAlpha L N ℓ)
    (originalHeckeBeta_finite L N ℓ) (originalHeckeAlpha_finite L N ℓ)
    (original_place_residue_algebraMap_bijective N L)
    (original_place_residue_algebraMap_bijective (N * ℓ) L)

theorem originalHeckePicard_mk (D : Divisor.degZero (K := L) (F := modularFunctionFieldOver N L)) :
    originalHeckePicard L N ℓ (Pic0.mk D) =
      Pic0.mk ⟨originalHeckeDivisor L N ℓ D.val, originalHeckeDivisor_mem_degZero L N ℓ D.2⟩ :=
  Pic0.geometricCorrespondence_mk _ _ _ _ _ _ D

end
end Dubon2026.SourceFunctionField
