import Dubon2026.SourceTateEndomorphisms
import Dubon2026.SourceOriginalTorsionContinuity

/-! DUB-17/18 -> original modular Galois realization -> the actual Tate action.
Apply the Tate functor to the original coefficient Galois action on Picard
classes. Each coordinate is the previously constructed torsion representation,
whose continuity follows from the proved finite fields of definition.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve
local notation "Qbar" => AlgebraicClosure ℚ
variable (N : ℕ) [NeZero N] (p : ℕ) [Fact p.Prime]

/-- The original arithmetic Galois representation on genuine Tate sequences. -/
def originalTateGaloisRep : (Qbar ≃ₐ[ℚ] Qbar) →*
    Module.End ℤ_[p] (TateModule p (originalJZero N)) :=
  (TateModule.mapEnd p (originalJZero N)).toMonoidHom.comp (originalArithmeticPicardRep N)

theorem originalTateGaloisRep_apply (σ : Qbar ≃ₐ[ℚ] Qbar)
    (x : TateModule p (originalJZero N)) (n : ℕ) :
    ((originalTateGaloisRep N p σ x : TateModule p (originalJZero N)) : ℕ → originalJZero N) n =
      originalArithmeticPicard N σ ((x : ℕ → originalJZero N) n) := rfl

/-- The actual n-th finite-torsion coordinate of the original Tate module. -/
def originalTateTorsionCoordinate (n : ℕ) :
    TateModule p (originalJZero N) →+ originalJZeroTorsion N (p ^ n) where
  toFun x := ⟨(x : ℕ → originalJZero N) n, Pic0.mem_torsion_iff.mpr (by
    rw [← Nat.cast_smul_eq_nsmul ℤ]
    exact TateModule.torsion x n)⟩
  map_zero' := rfl
  map_add' _ _ := rfl

theorem originalTateTorsionCoordinate_galois (n : ℕ) (σ : Qbar ≃ₐ[ℚ] Qbar)
    (x : TateModule p (originalJZero N)) :
    originalTateTorsionCoordinate N p n (originalTateGaloisRep N p σ x) =
      originalJZeroTorsionGaloisRep N (p ^ n) σ (originalTateTorsionCoordinate N p n x) := rfl

theorem originalTateGaloisRep_coordinate_continuous (n : ℕ)
    (x : TateModule p (originalJZero N)) :
    Continuous (fun σ : Qbar ≃ₐ[ℚ] Qbar =>
      originalTateTorsionCoordinate N p n (originalTateGaloisRep N p σ x)) := by
  simp only [originalTateTorsionCoordinate_galois]
  exact originalJZeroTorsionGaloisRep_continuous_apply N (p ^ n)
    (originalTateTorsionCoordinate N p n x)

end
end Dubon2026.SourceFunctionField
