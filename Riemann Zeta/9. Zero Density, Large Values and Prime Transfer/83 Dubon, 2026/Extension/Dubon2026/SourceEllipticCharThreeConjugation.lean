import Dubon2026.SourceEllipticCharThreeTranslation

/-! The actual quartic and cubic exceptional automorphisms satisfy the
dihedral conjugation relation. Existing point coordinates suffice; no
new variable-change action or point-cast framework is introduced.
This relation serves the DUB-17/18 cubic fixed-point count and census. -/
namespace Dubon2026.SourceEllipticExceptional
open WeierstrassCurve WeierstrassCurve.Affine SourceEllipticVariableChange
open SourceEllipticStabilizer
noncomputable section
variable {K : Type*} [Field K] [DecidableEq K] [CharP K 3]

theorem charThreeTranslation_conjugation (u : Kˣ) (hu : (u : K) ^ 2 = -1)
    (T : (EA (-1 : K)).toAffine.Point) :
    let α := stabilizerPointEquiv (EA (-1 : K)) ⟨u, 0, 0, 0⟩ (quartic_change_fixes u hu (-1))
    α (charThreeTranslation T) = charThreeTranslation (charThreeTranslation (α T)) := by
  dsimp only
  have hi2 : ((u⁻¹ : Kˣ) : K) ^ 2 = -1 := by
    rw [Units.val_inv_eq_inv_val, inv_pow, hu, inv_neg, inv_one]
  apply xy_injective
  rw [xy_stabilizerPointEquiv, xy_charThreeTranslation, xy_charThreeTranslation,
    xy_charThreeTranslation, xy_stabilizerPointEquiv]
  rcases xy T with _ | ⟨x, y⟩
  · rfl
  · simp only [Option.map_some, vcXInv, vcYInv, sub_zero, zero_mul,
      Option.some.injEq, Prod.mk.injEq]
    constructor
    · rw [hi2]
      linear_combination CharP.cast_eq_zero K 3
    · trivial

end
end Dubon2026.SourceEllipticExceptional
