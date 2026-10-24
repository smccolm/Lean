import Dubon2026.SourceEllipticThreeTorsionFlex
import Dubon2026.SourceEllipticFiniteTorsionField

/-! DUB-17/18 -> characteristic-two modular genus/Picard -> faithful inertia.
The actual finite Deuring generator field is adapted from
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_WeierstrassCurve_exists_isGalois_goodModel_inertia_faithful_of_three_ne_zero.
Existing local division-field and exact torsion-cardinality proofs are reused. -/
namespace Dubon2026.SourceEllipticDeuring
open WeierstrassCurve WeierstrassCurve.Affine Polynomial
open SourceEllipticDivisionField
noncomputable section
variable {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] [DecidableEq Ω]

variable (E : WeierstrassCurve F)

/-- The actual affine second division value; infinity contributes zero. -/
def psi2 : (E.baseChange Ω).toAffine.Point → Ω
  | .zero => 0
  | .some x y _ => 2 * y + (E.baseChange Ω).a₁ * x + (E.baseChange Ω).a₃

omit [DecidableEq Ω] in
lemma psi2_some {x y : Ω} (h : (E.baseChange Ω).toAffine.Nonsingular x y) :
    psi2 E (.some x y h) = 2 * y + (E.baseChange Ω).a₁ * x + (E.baseChange Ω).a₃ := rfl

lemma psi2_ne_zero {x y : Ω} (h : (E.baseChange Ω).toAffine.Nonsingular x y)
    (h3 : (3 : ℕ) • Point.some x y h = 0) : psi2 E (.some x y h) ≠ 0 :=
  (flex_of_order_three (E.baseChange Ω) h h3).1

lemma psi2_map (φ : Ω →ₐ[F] Ω) (P : (E.baseChange Ω).toAffine.Point) :
    psi2 E (Point.map φ P) = φ (psi2 E P) := by
  rcases P with _ | ⟨x, y, h⟩
  · show psi2 E 0 = φ 0
    rw [map_zero]; rfl
  · rw [Point.map_some, psi2_some, psi2_some]
    have ha₁ : φ (E.baseChange Ω).a₁ = (E.baseChange Ω).a₁ := φ.commutes E.a₁
    have ha₃ : φ (E.baseChange Ω).a₃ = (E.baseChange Ω).a₃ := φ.commutes E.a₃
    rw [map_add, map_add, map_mul, map_mul, map_ofNat, ha₁, ha₃]


variable [E.IsElliptic] [IsAlgClosed Ω] (h3 : (3 : F) ≠ 0)

include h3 in

lemma card_three_torsion : Nat.card {P : (E.baseChange Ω).toAffine.Point // (3 : ℕ) • P = 0} = 9 := by
  change Nat.card ({P : (E.baseChange Ω).toAffine.Point | (3 : ℕ) • P = 0} : Set _) = 9
  rw [Nat.card_coe_set_eq]
  exact (finite_and_ncard_torsion E (natCast_ne_zero_of_ne_zero h3)).2

include h3 in
lemma finite_three_torsion : Finite {P : (E.baseChange Ω).toAffine.Point // (3 : ℕ) • P = 0} :=
  Nat.finite_of_card_ne_zero (by rw [card_three_torsion E h3]; norm_num)

include h3 in

lemma exists_three_torsion : ∃ P : (E.baseChange Ω).toAffine.Point, (3 : ℕ) • P = 0 ∧ P ≠ 0 := by
  haveI := finite_three_torsion (Ω := Ω) E h3
  have h9 : 1 < Nat.card {P : (E.baseChange Ω).toAffine.Point // (3 : ℕ) • P = 0} := by
    rw [card_three_torsion E h3]; norm_num
  haveI := (Finite.one_lt_card_iff_nontrivial).mp h9
  obtain ⟨⟨P, hP⟩, hne⟩ := exists_ne
    (⟨0, by rw [smul_zero]⟩ : {P : (E.baseChange Ω).toAffine.Point // (3 : ℕ) • P = 0})
  exact ⟨P, hP, fun h => hne (Subtype.ext h)⟩

end
end Dubon2026.SourceEllipticDeuring
