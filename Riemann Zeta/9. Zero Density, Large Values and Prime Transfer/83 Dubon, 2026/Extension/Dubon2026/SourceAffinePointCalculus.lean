import Dubon2026.SourceAffineFunctionRepresentation
import Dubon2026.HeckeUpperCosets

/-! Actual prime-field point calculations for the nonvanishing evaluation map.
DUB-17/18 -> residual modular Galois association -> character-to-weight-two
reduction -> injective evaluation of full-function H1 at the raised level.
The point identities are adapted from anthropics/fermats-last-theorem,
revision 6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_HeckeEis_exists_isEigensystemH1_one_of_isEigensystemH1_gamma0NebenRep.lean.txt
(Apache-2.0; retained LICENSE and NOTICE). Existing actual binary characters
and integral upper translations replace duplicated matrix constructions.
-/

namespace Dubon2026
noncomputable section
open CongruenceSubgroup

variable (p Q : ℕ) [Fact p.Prime]

/-- The original upper diagonal is multiplicative at the residue-prime level. -/
theorem sourceAffine_a_mul (hpQ : p ∣ Q) (g h : Gamma0 Q) :
    sourceAffineA p Q (g * h) = sourceAffineA p Q g * sourceAffineA p Q h := by
  simpa [sourceBinaryFlagCharacter] using
    (sourceBinaryFlagCharacter (ZMod p) p Q hpQ 1 1).map_mul g h

/-- The original inverse's upper diagonal is the original lower diagonal. -/
theorem sourceAffine_a_inv (g : Gamma0 Q) :
    sourceAffineA p Q g⁻¹ = sourceAffineD p Q g := by
  change (((g.val⁻¹).val 0 0 : ℤ) : ZMod p) = _
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
  rfl

/-- The original inverse negates the upper-right entry. -/
theorem sourceAffine_b_inv (g : Gamma0 Q) :
    sourceAffineB p Q g⁻¹ = -sourceAffineB p Q g := by
  change (((g.val⁻¹).val 0 1 : ℤ) : ZMod p) = _
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
  exact Int.cast_neg _

/-- The original inverse's lower diagonal is the original upper diagonal. -/
theorem sourceAffine_d_inv (g : Gamma0 Q) :
    sourceAffineD p Q g⁻¹ = sourceAffineA p Q g := by
  change (((g.val⁻¹).val 1 1 : ℤ) : ZMod p) = _
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
  rfl

/-- The original affine point attached to an actual Gamma0 matrix. -/
def sourceAffinePoint (g : Gamma0 Q) : ZMod p :=
  sourceAffineA p Q g * sourceAffineB p Q g

/-- Actual matrix multiplication gives the precise affine motion of the original point. -/
theorem sourceAffinePoint_move (hpQ : p ∣ Q) (g h : Gamma0 Q) :
    sourceAffinePoint p Q (g⁻¹ * h) =
      sourceAffineD p Q g *
        (sourceAffineD p Q g * sourceAffinePoint p Q h - sourceAffineB p Q g) := by
  rw [sourceAffinePoint, sourceAffine_a_mul p Q hpQ, sourceAffine_b_mul,
    sourceAffine_a_inv, sourceAffine_b_inv, sourceAffinePoint]
  linear_combination (-(sourceAffineD p Q g * sourceAffineB p Q g)) * sourceAffine_ad p Q hpQ h

/-- The original inverse affine motion returns every actual prime-field point. -/
theorem sourceAffinePoint_inverse (hpQ : p ∣ Q) (g : Gamma0 Q) (u : ZMod p) :
    sourceAffineD p Q g⁻¹ *
      (sourceAffineD p Q g⁻¹ *
        (sourceAffineD p Q g * (sourceAffineD p Q g * u - sourceAffineB p Q g)) -
        sourceAffineB p Q g⁻¹) = u := by
  rw [sourceAffine_d_inv, sourceAffine_b_inv]
  linear_combination
    (sourceAffineA p Q g * sourceAffineD p Q g * u + u -
      sourceAffineA p Q g * sourceAffineB p Q g) * sourceAffine_ad p Q hpQ g

/-- Every original prime-field point is reached by an actual integral translation. -/
theorem sourceAffinePoint_translation (n : ℤ) :
    sourceAffinePoint p Q (heckeUpperTranslation Q n) = (n : ZMod p) := by
  simp [sourceAffinePoint, sourceAffineA, sourceAffineB, heckeUpperTranslation]

end
end Dubon2026
