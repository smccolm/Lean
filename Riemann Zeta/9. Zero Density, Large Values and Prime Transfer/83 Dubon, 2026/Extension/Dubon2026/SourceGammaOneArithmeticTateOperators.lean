import Dubon2026.SourceGammaOneDiamondGaloisPicard
import Dubon2026.SourceTateEndomorphisms

/-! DUB-17/18 -> original all-weight association -> finite Gamma1
Frobenius realization. Name the actual Tate functor images on one common
original field, retaining arithmetic Galois multiplication and the already
proved Picard Hecke/diamond commutation. This normal form avoids repeated
expansion of the two definitionally equal native field presentations.
-/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open SourceCurve CongruenceSubgroup
variable (M p : ℕ) [NeZero M] [Fact p.Prime]
local notation "Qbar" => AlgebraicClosure ℚ
local notation "J" => Pic0 Qbar (functionFieldOver (Gamma1 M) Qbar)
local notation "T" => TateModule p J

/-- The original Gamma1 coefficient Galois action on actual Tate sequences. -/
def arithmeticTateGaloisRep : (Qbar ≃ₐ[ℚ] Qbar) →* Module.End ℤ_[p] T :=
  (TateModule.mapEnd p J).toMonoidHom.comp (gamma1ArithmeticPicardRep Qbar M)

/-- The literal original Picard Hecke correspondence on the same Tate module. -/
def arithmeticHeckeTate (d : ℕ) [NeZero d] : Module.End ℤ_[p] T :=
  TateModule.tateMap p (heckePicard Qbar M d)

/-- The literal original arithmetic diamond on the same Tate module. -/
def arithmeticDiamondTate (g : Gamma0 M) : Module.End ℤ_[p] T :=
  TateModule.tateMap p (arithmeticDiamondPicard M g).toAddMonoidHom

theorem arithmeticTateGaloisRep_hecke (d : ℕ) [NeZero d]
    (σ : Qbar ≃ₐ[ℚ] Qbar) :
    Commute (arithmeticTateGaloisRep M p σ) (arithmeticHeckeTate M p d) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  funext n
  exact heckePicard_arithmetic M d σ ((x : ℕ → J) n)

theorem arithmeticTateGaloisRep_diamond (g : Gamma0 M)
    (σ : Qbar ≃ₐ[ℚ] Qbar) :
    Commute (arithmeticTateGaloisRep M p σ) (arithmeticDiamondTate M p g) := by
  apply LinearMap.ext
  intro x
  exact arithmeticDiamondTate_galois M g σ p x

end
end Dubon2026.SourceFunctionField.GammaOne
