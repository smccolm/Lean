import Dubon2026.SourceOriginalTateWeilLinearity
import Dubon2026.SourceOriginalWeilArithmetic

/-! DUB-17/18 -> Frobenius determinant -> arithmetic covariance.
The target action is induced by the actual coefficient action on units;
the identity is proved coordinatewise using the descended divisorial pairing. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
local notation "Qbar" => AlgebraicClosure ℚ
variable (N : ℕ) [NeZero N] (p : ℕ) [Fact p.Prime]

/-- Coefficient Galois action on the actual Tate module of roots of unity. -/
def originalTateRootsGalois (σ : Qbar ≃ₐ[ℚ] Qbar) :
    Module.End ℤ_[p] (TateModule p (Additive Qbarˣ)) :=
  TateModule.tateMap p (Units.map σ.toMonoidHom).toAdditive

theorem originalTateWeilPairing_galois (σ : Qbar ≃ₐ[ℚ] Qbar)
    (x y : TateModule p (originalJZero N)) :
    originalTateWeilPairing N p (originalTateGaloisRep N p σ x)
      (originalTateGaloisRep N p σ y) =
      originalTateRootsGalois p σ (originalTateWeilPairing N p x y) := by
  apply Subtype.ext
  funext k
  apply Additive.toMul.injective
  apply Units.ext
  change ((originalWeilPairing N Qbar (p ^ k)
    (originalTateTorsionCoordinate N p k (originalTateGaloisRep N p σ x))
    (originalTateTorsionCoordinate N p k (originalTateGaloisRep N p σ y)) : Qbarˣ) : Qbar) =
      σ ((originalWeilPairing N Qbar (p ^ k)
        (originalTateTorsionCoordinate N p k x) (originalTateTorsionCoordinate N p k y) : Qbarˣ) : Qbar)
  rw [originalTateTorsionCoordinate_galois, originalTateTorsionCoordinate_galois]
  exact originalWeilPairing_originalGalois σ _ _

end
end Dubon2026.SourceFunctionField
