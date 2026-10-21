import Dubon2026.SourceBinaryFlagQuotientRepresentation
import Dubon2026.SourceFiniteFunctionBasis

/-! The actual finite-function representation used to remove the residual character.
DUB-17/18 -> residual modular Galois association -> character-to-weight-two
reduction -> lifting the character into the original affine function action.
The action formula is adapted from anthropics/fermats-last-theorem,
revision 6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_HeckeEis_exists_isEigensystemH1_one_of_isEigensystemH1_gamma0NebenRep.lean.txt
(Apache-2.0; retained LICENSE and NOTICE). The existing actual binary
character gives diagonal multiplicativity; the representation is native Rep.
-/

namespace Dubon2026
noncomputable section
open CongruenceSubgroup

variable (p Q : ℕ) [Fact p.Prime]

/-- The actual upper-left congruence-group entry reduced to the prime field. -/
abbrev sourceAffineA (g : Gamma0 Q) : ZMod p := ((g.val 0 0 : ℤ) : ZMod p)
/-- The actual upper-right congruence-group entry reduced to the prime field. -/
abbrev sourceAffineB (g : Gamma0 Q) : ZMod p := ((g.val 0 1 : ℤ) : ZMod p)
/-- The actual lower-right congruence-group entry reduced to the prime field. -/
abbrev sourceAffineD (g : Gamma0 Q) : ZMod p := ((g.val 1 1 : ℤ) : ZMod p)

/-- The original determinant relation makes the reduced diagonal entries inverse. -/
theorem sourceAffine_ad (hpQ : p ∣ Q) (g : Gamma0 Q) :
    sourceAffineA p Q g * sourceAffineD p Q g = 1 := by
  have hdet := Matrix.det_fin_two g.val.val
  rw [g.val.property] at hdet
  have h := congrArg (fun z : ℤ => (z : ZMod p)) hdet
  simp only [Int.cast_one, Int.cast_sub, Int.cast_mul,
    sourceBinaryFlag_lower_zero (ZMod p) p Q hpQ g, mul_zero, sub_zero] at h
  exact h.symm

/-- The actual lower diagonal is multiplicative at a prime-divisible level. -/
theorem sourceAffine_d_mul (hpQ : p ∣ Q) (g h : Gamma0 Q) :
    sourceAffineD p Q (g * h) = sourceAffineD p Q g * sourceAffineD p Q h := by
  simpa [sourceBinaryFlagCharacter] using
    (sourceBinaryFlagCharacter (ZMod p) p Q hpQ 1 0).map_mul g h

/-- The original upper-right entry has the literal matrix-product formula. -/
theorem sourceAffine_b_mul (g h : Gamma0 Q) :
    sourceAffineB p Q (g * h) =
      sourceAffineA p Q g * sourceAffineB p Q h + sourceAffineB p Q g * sourceAffineD p Q h := by
  change (((g.val.val * h.val.val) 0 1 : ℤ) : ZMod p) = _
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Int.cast_add, Int.cast_mul]

variable (F : Type) [Field F]

/-- The exact affine pullback on original prime-field functions. -/
def sourceAffineFunctionAction (g : Gamma0 Q) : Module.End F (ZMod p → F) where
  toFun f u := f (sourceAffineD p Q g * (sourceAffineD p Q g * u - sourceAffineB p Q g))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The original affine pullbacks form an actual representation. -/
def sourceAffineFunctionRepresentation (hpQ : p ∣ Q) :
    Representation F (Gamma0 Q) (ZMod p → F) where
  toFun := sourceAffineFunctionAction p Q F
  map_one' := by
    apply LinearMap.ext
    intro f
    funext u
    simp [sourceAffineFunctionAction, sourceAffineD, sourceAffineB]
  map_mul' g h := by
    apply LinearMap.ext
    intro f
    funext u
    change f (sourceAffineD p Q (g * h) *
      (sourceAffineD p Q (g * h) * u - sourceAffineB p Q (g * h))) =
      f (sourceAffineD p Q h * (sourceAffineD p Q h *
        (sourceAffineD p Q g * (sourceAffineD p Q g * u - sourceAffineB p Q g)) -
        sourceAffineB p Q h))
    rw [sourceAffine_d_mul p Q hpQ, sourceAffine_b_mul]
    congr 1
    linear_combination (-(sourceAffineD p Q h * sourceAffineB p Q h)) *
      sourceAffine_ad p Q hpQ g

/-- Native Rep object for the actual finite-function coefficients. -/
def sourceAffineFunctionRep (hpQ : p ∣ Q) : Rep F (Gamma0 Q) :=
  Rep.of (sourceAffineFunctionRepresentation p Q F hpQ)

/-- The native representation acts by the original affine formula. -/
theorem sourceAffineFunctionRep_apply (hpQ : p ∣ Q) (g : Gamma0 Q)
    (f : ZMod p → F) (u : ZMod p) :
    (sourceAffineFunctionRep p Q F hpQ).ρ g f u =
      f (sourceAffineD p Q g * (sourceAffineD p Q g * u - sourceAffineB p Q g)) := rfl

/-- The actual Hecke coefficient map rescales the prime-field argument. -/
def sourceAffineFunctionDiagonal (ell : ℕ) : Module.End F (ZMod p → F) where
  toFun f u := f ((ell : ZMod p)⁻¹ * u)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The original coefficient rescaling evaluates at the exact inverse-scaled point. -/
theorem sourceAffineFunctionDiagonal_apply (ell : ℕ) (f : ZMod p → F) (u : ZMod p) :
    sourceAffineFunctionDiagonal p F ell f u = f ((ell : ZMod p)⁻¹ * u) := rfl

/-- All original finite-function coefficient rescalings commute. -/
theorem sourceAffineFunctionDiagonal_commute (a b : ℕ) :
    (sourceAffineFunctionDiagonal p F a).comp (sourceAffineFunctionDiagonal p F b) =
      (sourceAffineFunctionDiagonal p F b).comp (sourceAffineFunctionDiagonal p F a) := by
  apply LinearMap.ext
  intro f
  funext u
  change f ((b : ZMod p)⁻¹ * ((a : ZMod p)⁻¹ * u)) =
    f ((a : ZMod p)⁻¹ * ((b : ZMod p)⁻¹ * u))
  rw [mul_left_comm]

end
end Dubon2026
