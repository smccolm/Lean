import Dubon2026.SourceOriginalWeilAdjunctionRepresentatives

/-! DUB-17/18 -> Hecke-adjoint original Tate pairing. Finite pullback
and norm are adjoint for the actual root-valued pairing on original
Picard torsion. Compatible representatives, norm identities, disjointness
and all geometric premises are proved dependencies. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve
variable (L : Type*) [Field L] [Algebra ℚ L] [IsAlgClosed L]
variable (N M : ℕ) [NeZero N] [NeZero M] (n : ℕ) [NeZero n]

theorem originalWeilPairing_norm_adjunction
    (φ : modularFunctionFieldOver N L →ₐ[L] modularFunctionFieldOver M L)
    (x : Pic0.torsion (K := L) (F := modularFunctionFieldOver N L) n)
    (y : Pic0.torsion (K := L) (F := modularFunctionFieldOver M L) n) :
    originalWeilPairing N L n x (originalPicardNormTorsion L N M φ n y) =
      originalWeilPairing M L n (originalPicardPullbackTorsion L N M φ n x) y := by
  obtain ⟨d, e, hx, hy, hp, hn, he⟩ := exists_original_weil_adjunction_representatives L N M n φ x y
  have hx' : d.classLeft = x := Subtype.ext hx
  have hy' : e.classRight = y := Subtype.ext hy
  have hp' : e.classLeft = originalPicardPullbackTorsion L N M φ n x := Subtype.ext hp
  have hn' : d.classRight = originalPicardNormTorsion L N M φ n y := Subtype.ext hn
  apply Subtype.ext
  apply Units.ext
  rw [← hn', ← hp', ← hx', ← hy', originalWeilPairing_eq_pairing, originalWeilPairing_eq_pairing, he]

theorem originalWeilPairing_pullback_adjunction
    (φ : modularFunctionFieldOver N L →ₐ[L] modularFunctionFieldOver M L)
    (x : Pic0.torsion (K := L) (F := modularFunctionFieldOver N L) n)
    (y : Pic0.torsion (K := L) (F := modularFunctionFieldOver M L) n) :
    originalWeilPairing M L n y (originalPicardPullbackTorsion L N M φ n x) =
      originalWeilPairing N L n (originalPicardNormTorsion L N M φ n y) x := by
  rw [originalWeilPairing_symm M L n, originalWeilPairing_symm N L n,
    originalWeilPairing_norm_adjunction]

end
end Dubon2026.SourceFunctionField
