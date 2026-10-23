import Dubon2026.SourceEllipticOddNormSpecialization
import Dubon2026.SourceEllipticOddChordIdentities
import Dubon2026.SourceEllipticOddSummingSet

/-! Actual odd-orbit coordinate inputs for quotient ellipticity.
The native point group and already proved coordinate identities supply
distinct translated roots and the two-torsion fiber factorization. These
serve the explicit quotient discriminant, prime quotient products and
cyclic-subgroup inertia census required by DUB-17 / DUB-18.
Adapted from the selected odd-order quotient discriminant proof,
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2. Native finite-order nonvanishing
replaces the duplicate divisibility proof. -/
namespace Dubon2026.SourceEllipticVelu.OddDiscriminant
open WeierstrassCurve Polynomial
open Algebra
noncomputable section
variable {F : Type*} [Field F] [DecidableEq F] {V : WeierstrassCurve F}
theorem two_torsion_chord_factor (ha1 : V.a₁ = 0) (ha3 : V.a₃ = 0) {e xq yq : F}
    (he : V.toAffine.Equation e 0) (hq : V.toAffine.Equation xq yq) (hex : e ≠ xq) :
    C ((e - xq) ^ 2) * X ^ 2 - C (2 * xq * (e - xq) ^ 2 + veluT V xq yq * (e - xq)
        + veluU V xq yq) * X + C ((e * xq - V.a₄) ^ 2 - 4 * V.a₆ * (e + xq + V.a₂))
      = C ((e - xq) ^ 2) * (X - C (V.toAffine.addX e xq (V.toAffine.slope e xq 0 yq))) ^ 2 := by
  have hsum := chord_sum' V he hq hex
  have hprod := chord_prod V ha1 ha3 he hq hex
  have hτ : V.toAffine.addX e xq (V.toAffine.slope e xq 0 (V.toAffine.negY xq yq))
      = V.toAffine.addX e xq (V.toAffine.slope e xq 0 yq) := by
    rw [Affine.slope_of_X_ne hex, Affine.slope_of_X_ne hex]
    simp only [Affine.addX, Affine.negY, toAffine, ha1, ha3]
    ring
  rw [hτ] at hsum hprod
  rw [pow_two (X - C _), ← mul_assoc]
  exact chord_factor e xq _ _ V.a₂ V.a₄ V.a₆ _ _ hex hsum hprod


omit [DecidableEq F] in
theorem affine_decomp {V : WeierstrassCurve F} (P : V.toAffine.Point) (hP : P ≠ 0) :
    ∃ h : V.toAffine.Nonsingular ((coordsOrZero P)).1 ((coordsOrZero P)).2,
      P = .some ((coordsOrZero P)).1 ((coordsOrZero P)).2 h := by
  rcases P with _ | ⟨a, b, h⟩
  · exact absurd rfl hP
  · exact ⟨h, rfl⟩


theorem kernel_ne_zero {Q : V.toAffine.Point} {n : ℕ}
    (hQ : addOrderOf Q = 2 * n + 1) {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ 2 * n) :
    k • Q ≠ 0 :=
  nsmul_ne_zero_of_lt_addOrderOf (by omega) (by rw [hQ]; omega)

omit [DecidableEq F] in
theorem b_model {V : WeierstrassCurve F} (ha₁ : V.a₁ = 0) (ha₃ : V.a₃ = 0) :
    V.b₂ = 4 * V.a₂ ∧ V.b₄ = 2 * V.a₄ ∧ V.b₆ = 4 * V.a₆ ∧ V.b₈ = 4 * V.a₂ * V.a₆ - V.a₄ ^ 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [b₂, ha₁]; ring
  · rw [b₄, ha₁, ha₃]; ring
  · rw [b₆, ha₃]; ring
  · rw [b₈, ha₁, ha₃]; ring

omit [DecidableEq F] in
theorem Ψ₂Sq_b_model {V : WeierstrassCurve F} (ha₁ : V.a₁ = 0) (ha₃ : V.a₃ = 0) :
    V.Ψ₂Sq = fP (4 * V.a₂) (2 * V.a₄) (4 * V.a₆) := by
  obtain ⟨hb2, hb4, hb6, -⟩ := b_model ha₁ ha₃
  rw [Ψ₂Sq, hb2, hb4, hb6, fP]


end
end Dubon2026.SourceEllipticVelu.OddDiscriminant
