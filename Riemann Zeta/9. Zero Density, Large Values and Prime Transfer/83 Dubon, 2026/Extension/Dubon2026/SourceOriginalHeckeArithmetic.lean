import Dubon2026.SourceOriginalHeckeArithmeticDivisors

/-! DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> modular residual
Galois association -> original Tate Hecke realization. The literal alpha
and beta maps commute with coefficient automorphisms. Their proved divisor
naturality therefore makes the actual original Picard Hecke operator
arithmetic-equivariant, without a correspondence-naturality premise.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve
variable {L : Type*} [Field L] [Algebra ℚ L] [CharZero L] [IsAlgClosed L]
variable (N ℓ : ℕ) [NeZero N] [NeZero ℓ]

omit [IsAlgClosed L] in
theorem originalHeckeDivisor_arithmetic (σ : L ≃ₐ[ℚ] L)
    (D : Divisor L (modularFunctionFieldOver N L)) :
    originalArithmeticDivisorEquiv N σ (originalHeckeDivisor L N ℓ D) =
      originalHeckeDivisor L N ℓ (originalArithmeticDivisorEquiv N σ D) := by
  change originalArithmeticDivisorEquiv N σ
    (Divisor.geometricPushforwardAlong (originalHeckeAlpha L N ℓ)
      (originalHeckeAlpha_finite L N ℓ)
      (Divisor.finitePullbackAlong (originalHeckeBeta L N ℓ)
        (originalHeckeBeta_finite L N ℓ) D)) = _
  rw [← original_geometricPushforwardAlong_arithmetic N (N * ℓ)
    (originalHeckeAlpha L N ℓ) (originalHeckeAlpha_finite L N ℓ)
    (originalHeckeAlpha_arithmetic N ℓ)]
  rw [original_finitePullbackAlong_arithmetic N (N * ℓ)
    (originalHeckeBeta L N ℓ) (originalHeckeBeta_finite L N ℓ)
    (originalHeckeBeta_arithmetic N ℓ)]
  rfl

theorem originalHeckePicard_arithmetic (σ : L ≃ₐ[ℚ] L)
    (x : Pic0 L (modularFunctionFieldOver N L)) :
    originalArithmeticPicard N σ (originalHeckePicard L N ℓ x) =
      originalHeckePicard L N ℓ (originalArithmeticPicard N σ x) := by
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective x
  rw [originalHeckePicard_mk, originalArithmeticPicard_mk,
    originalArithmeticPicard_mk, originalHeckePicard_mk]
  apply congrArg Pic0.mk
  apply Subtype.ext
  exact originalHeckeDivisor_arithmetic N ℓ σ D.val

end
end Dubon2026.SourceFunctionField
