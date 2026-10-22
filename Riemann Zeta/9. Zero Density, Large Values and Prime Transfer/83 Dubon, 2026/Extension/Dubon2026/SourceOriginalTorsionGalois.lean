import Dubon2026.SourceOriginalArithmeticPicard
import Mathlib.Algebra.Module.ZMod

/-! DUB-17/18 -> actual modular Galois association -> the original
Jacobian Tate module. The actual n-torsion of the same degree-zero divisor
quotient has its native ZMod n structure and the genuine coefficient
Galois action. Finiteness, continuity, rank two on the Hecke component,
Frobenius and inertia identities remain separate obligations.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve

/-- The actual n-torsion in the original modular divisor-class group over Qbar. -/
abbrev originalJZeroTorsion (N n : ℕ) :=
  Pic0.torsion (K := AlgebraicClosure ℚ)
    (F := modularFunctionFieldOver N (AlgebraicClosure ℚ)) n

/-- Scalar multiplication on the actual n-torsion is its native ZMod n action. -/
instance originalJZeroTorsionModule (N n : ℕ) : Module (ZMod n) (originalJZeroTorsion N n) :=
  AddCommGroup.zmodModule (fun x => Subtype.ext (Pic0.mem_torsion_iff.mp x.property))

/-- The original arithmetic action restricted to its genuine torsion subgroup. -/
def originalJZeroTorsionAddHom (N : ℕ) [NeZero N] (n : ℕ)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    originalJZeroTorsion N n →+ originalJZeroTorsion N n where
  toFun x := ⟨originalArithmeticPicard N σ x.val, originalArithmeticPicard_torsion N σ n x.val x.property⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' x y := Subtype.ext (map_add _ x.val y.val)

/-- The actual arithmetic Galois representation on original modular divisor-class n-torsion. -/
def originalJZeroTorsionGaloisRep (N : ℕ) [NeZero N] (n : ℕ) :
    (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →*
      Module.End (ZMod n) (originalJZeroTorsion N n) where
  toFun σ := (originalJZeroTorsionAddHom N n σ).toZModLinearMap n
  map_one' := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact DFunLike.congr_fun (originalArithmeticPicardRep N (L := AlgebraicClosure ℚ)).map_one x.val
  map_mul' σ τ := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact DFunLike.congr_fun ((originalArithmeticPicardRep N (L := AlgebraicClosure ℚ)).map_mul σ τ) x.val

theorem originalJZeroTorsionGaloisRep_apply (N : ℕ) [NeZero N] (n : ℕ)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : originalJZeroTorsion N n) :
    (originalJZeroTorsionGaloisRep N n σ x : originalJZero N) =
      originalArithmeticPicard N σ x.val := rfl

end
end Dubon2026.SourceFunctionField
