import Dubon2026.SourceOriginalWeilAdjunction

/-! DUB-17/18 -> original Hecke-adjoint Tate pairing. A finite
correspondence and its transpose are adjoint for the actual Picard Weil
pairing. Both maps are the constructed norm-after-pullback operators. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve
variable (L : Type*) [Field L] [Algebra ℚ L] [IsAlgClosed L]
variable (N M : ℕ) [NeZero N] [NeZero M] (n : ℕ) [NeZero n]

theorem originalWeilPairing_correspondence_adjunction
    (φ ψ : modularFunctionFieldOver N L →ₐ[L] modularFunctionFieldOver M L)
    (x y : Pic0.torsion (K := L) (F := modularFunctionFieldOver N L) n) :
    originalWeilPairing N L n
      (originalPicardNormTorsion L N M ψ n (originalPicardPullbackTorsion L N M φ n x)) y =
    originalWeilPairing N L n x
      (originalPicardNormTorsion L N M φ n (originalPicardPullbackTorsion L N M ψ n y)) := by
  calc
    _ = originalWeilPairing M L n
        (originalPicardPullbackTorsion L N M φ n x)
        (originalPicardPullbackTorsion L N M ψ n y) :=
      (originalWeilPairing_pullback_adjunction L N M n ψ y
        (originalPicardPullbackTorsion L N M φ n x)).symm
    _ = _ := (originalWeilPairing_norm_adjunction L N M n φ x
      (originalPicardPullbackTorsion L N M ψ n y)).symm

end
end Dubon2026.SourceFunctionField
