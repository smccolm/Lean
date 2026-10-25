import Dubon2026.SourceOriginalWeilCorrespondenceAdjunction
import Dubon2026.SourceOriginalHeckePicard

/-! DUB-17/18 -> the actual original Hecke-adjoint Tate pairing.
Identify the finite-torsion norm-after-pullback operator with the already
defined original Picard Hecke correspondence. Its adjoint is the literal
transposed degeneracy correspondence; equality of that transpose with
the required Hecke operator remains a separate obligation. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve
attribute [local instance] originalNormCharZero
variable (L : Type*) [Field L] [Algebra ℚ L] [IsAlgClosed L]
variable (N ℓ : ℕ) [NeZero N] [NeZero ℓ] (n : ℕ)

/-- The original Hecke correspondence acting on actual finite Picard torsion. -/
def originalWeilHeckeTorsion :
    Pic0.torsion (K := L) (F := modularFunctionFieldOver N L) n →+
      Pic0.torsion (K := L) (F := modularFunctionFieldOver N L) n :=
  (originalPicardNormTorsion L N (N * ℓ) (originalHeckeAlpha L N ℓ) n).comp
    (originalPicardPullbackTorsion L N (N * ℓ) (originalHeckeBeta L N ℓ) n)

/-- The literal transposed degeneracy correspondence on actual Picard torsion. -/
def originalWeilHeckeTransposeTorsion :
    Pic0.torsion (K := L) (F := modularFunctionFieldOver N L) n →+
      Pic0.torsion (K := L) (F := modularFunctionFieldOver N L) n :=
  (originalPicardNormTorsion L N (N * ℓ) (originalHeckeBeta L N ℓ) n).comp
    (originalPicardPullbackTorsion L N (N * ℓ) (originalHeckeAlpha L N ℓ) n)

theorem originalWeilHeckeTorsion_val
    (x : Pic0.torsion (K := L) (F := modularFunctionFieldOver N L) n) :
    (originalWeilHeckeTorsion L N ℓ n x).val = originalHeckePicard L N ℓ x.val := by
  obtain ⟨D, hD⟩ := Pic0.mk_surjective x.val
  change originalPicardNorm L N (N * ℓ) (originalHeckeAlpha L N ℓ)
    (originalPicardPullback L N (N * ℓ) (originalHeckeBeta L N ℓ) x.val) = _
  rw [← hD, originalPicardPullback_mk, originalPicardNorm_mk, originalHeckePicard_mk]
  rfl

theorem originalWeilPairing_hecke_transpose [NeZero n]
    (x y : Pic0.torsion (K := L) (F := modularFunctionFieldOver N L) n) :
    originalWeilPairing N L n (originalWeilHeckeTorsion L N ℓ n x) y =
      originalWeilPairing N L n x (originalWeilHeckeTransposeTorsion L N ℓ n y) :=
  originalWeilPairing_correspondence_adjunction L N (N * ℓ) n
    (originalHeckeBeta L N ℓ) (originalHeckeAlpha L N ℓ) x y

end
end Dubon2026.SourceFunctionField
