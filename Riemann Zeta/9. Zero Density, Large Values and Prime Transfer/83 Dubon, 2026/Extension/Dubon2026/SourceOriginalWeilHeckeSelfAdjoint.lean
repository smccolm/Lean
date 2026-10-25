import Dubon2026.SourceOriginalWeilHeckeTranspose
import Dubon2026.SourceCurveCorrespondenceSwap
import Dubon2026.SourceOriginalAtkinCoefficientExtensionR2

/-! DUB-17/18 -> self-adjointness of the actual arithmetic Hecke
operator. Reuse the proved Atkin-Lehner involution that exchanges the
original degeneracy maps. The transpose identity is derived on actual
divisors and descends through the same Picard quotient. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve
attribute [local instance] originalNormCharZero
variable (L : Type*) [Field L] [Algebra ℚ L] [IsAlgClosed L] [Algebra.IsAlgebraic ℚ L]
variable (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime] (n : ℕ)

theorem originalWeilHeckeTranspose_eq (hℓN : ¬ ℓ ∣ N) :
    originalWeilHeckeTransposeTorsion L N ℓ n = originalWeilHeckeTorsion L N ℓ n := by
  obtain ⟨σ, _, hα, hβ⟩ := exists_original_atkin_over L N ℓ hℓN
  apply AddMonoidHom.ext
  intro x
  apply Subtype.ext
  rw [originalWeilHeckeTorsion_val]
  obtain ⟨D, hD⟩ := Pic0.mk_surjective x.val
  change originalPicardNorm L N (N * ℓ) (originalHeckeBeta L N ℓ)
    (originalPicardPullback L N (N * ℓ) (originalHeckeAlpha L N ℓ) x.val) = _
  rw [← hD, originalPicardPullback_mk, originalPicardNorm_mk, originalHeckePicard_mk]
  apply congrArg Pic0.mk
  apply Subtype.ext
  exact Divisor.geometricCorrespondence_swap_of_equiv
    (originalHeckeBeta L N ℓ) (originalHeckeAlpha L N ℓ)
    (originalHeckeBeta_finite L N ℓ) (originalHeckeAlpha_finite L N ℓ) σ hβ hα D.val

theorem originalWeilPairing_hecke_self_adjoint [NeZero n] (hℓN : ¬ ℓ ∣ N)
    (x y : Pic0.torsion (K := L) (F := modularFunctionFieldOver N L) n) :
    originalWeilPairing N L n (originalWeilHeckeTorsion L N ℓ n x) y =
      originalWeilPairing N L n x (originalWeilHeckeTorsion L N ℓ n y) := by
  rw [originalWeilPairing_hecke_transpose, originalWeilHeckeTranspose_eq L N ℓ n hℓN]

end
end Dubon2026.SourceFunctionField
