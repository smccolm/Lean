import Dubon2026.SourceEllipticCharThreeConjugation
import Dubon2026.SourceEllipticShortStabilizer

/-! Only the affine coordinate-change identities needed for the six
actual subgroup actions in the DUB-17/18 characteristic-three census.
Existing optional coordinates and subgroup negation are reused. -/
namespace Dubon2026.SourceEllipticExceptional
open WeierstrassCurve SourceEllipticVariableChange SourceEllipticStabilizer
open SourceEllipticReduction
noncomputable section
variable {K : Type*} [Field K] [CharP K 3]

theorem char_three_affine_fixes (u : Kˣ) (r : K)
    (hu : (u : K) ^ 4 = 1) (hr : r ^ 3 = r) :
    (⟨u, r, 0, 0⟩ : VariableChange K) • EA (-1 : K) = EA (-1 : K) := by
  have h3 : (3 : K) = 0 := CharP.cast_eq_zero K 3
  refine WeierstrassCurve.ext ?_ ?_ ?_ ?_ ?_ <;>
    simp [variableChange_a₁, variableChange_a₂, variableChange_a₃,
      variableChange_a₄, variableChange_a₆, EA, h3, Units.val_inv_eq_inv_val, inv_pow, hu, hr]

variable [DecidableEq K]

omit [CharP K 3] in
theorem char_three_affine_subgroup_map_eq_of_sign (u v : Kˣ) (r : K)
    (hu : (⟨u, r, 0, 0⟩ : VariableChange K) • EA (-1 : K) = EA (-1 : K))
    (hv : (⟨v, r, 0, 0⟩ : VariableChange K) • EA (-1 : K) = EA (-1 : K))
    (hs : (u : K) = v ∨ (u : K) = -(v : K)) (H : AddSubgroup (EA (-1 : K)).toAffine.Point) :
    H.map (stabilizerPointEquiv (EA (-1 : K)) ⟨u, r, 0, 0⟩ hu).toAddMonoidHom =
      H.map (stabilizerPointEquiv (EA (-1 : K)) ⟨v, r, 0, 0⟩ hv).toAddMonoidHom := by
  apply subgroup_map_eq_of_eq_or_neg
  rcases hs with hs | hs
  · left
    have he : u = v := Units.ext hs
    subst v
    exact fun _ => rfl
  · right
    intro P
    apply xy_injective
    change xy (stabilizerPointEquiv (EA (-1 : K)) ⟨u, r, 0, 0⟩ hu P) =
      xy (-(stabilizerPointEquiv (EA (-1 : K)) ⟨v, r, 0, 0⟩ hv P))
    rw [xy_stabilizerPointEquiv, xy_neg, xy_stabilizerPointEquiv]
    have hi : ((u⁻¹ : Kˣ) : K) = -((v⁻¹ : Kˣ) : K) := by
      rw [Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, hs, inv_neg]
    rcases xy P with _ | ⟨x, y⟩
    · rfl
    · simp only [Option.map_some, vcXInv, vcYInv, sub_zero, zero_mul,
        Affine.negY, hi, Option.some.injEq, Prod.mk.injEq]
      constructor <;> ring

omit [CharP K 3] in
theorem char_three_affine_point_factor (u : Kˣ) (r : K)
    (hu : (⟨u, 0, 0, 0⟩ : VariableChange K) • EA (-1 : K) = EA (-1 : K))
    (hr : (⟨1, r, 0, 0⟩ : VariableChange K) • EA (-1 : K) = EA (-1 : K))
    (hur : (⟨u, r, 0, 0⟩ : VariableChange K) • EA (-1 : K) = EA (-1 : K))
    (P : (EA (-1 : K)).toAffine.Point) :
    stabilizerPointEquiv (EA (-1 : K)) ⟨u, r, 0, 0⟩ hur P =
      stabilizerPointEquiv (EA (-1 : K)) ⟨u, 0, 0, 0⟩ hu
        (stabilizerPointEquiv (EA (-1 : K)) ⟨1, r, 0, 0⟩ hr P) := by
  apply xy_injective
  rw [xy_stabilizerPointEquiv, xy_stabilizerPointEquiv, xy_stabilizerPointEquiv]
  rcases xy P with _ | ⟨x, y⟩
  · rfl
  · simp [vcXInv, vcYInv]

theorem char_three_translation_neg_one_point
    (h : (⟨1, -1, 0, 0⟩ : VariableChange K) • EA (-1 : K) = EA (-1 : K))
    (P : (EA (-1 : K)).toAffine.Point) :
    stabilizerPointEquiv (EA (-1 : K)) ⟨1, -1, 0, 0⟩ h P =
      charThreeTranslation (charThreeTranslation P) := by
  apply xy_injective
  rw [xy_stabilizerPointEquiv, xy_charThreeTranslation, xy_charThreeTranslation]
  rcases xy P with _ | ⟨x, y⟩
  · rfl
  · simp only [Option.map_some, vcXInv, vcYInv, inv_one, Units.val_one, one_pow,
      one_mul, zero_mul, sub_zero, Option.some.injEq, Prod.mk.injEq]
    constructor
    · linear_combination CharP.cast_eq_zero K 3
    · trivial

end
end Dubon2026.SourceEllipticExceptional
