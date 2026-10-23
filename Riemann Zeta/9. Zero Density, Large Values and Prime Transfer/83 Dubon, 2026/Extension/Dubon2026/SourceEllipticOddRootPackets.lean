import Dubon2026.SourceEllipticOddTwoTorsionTranslation

/-! Coordinate identities on the required odd-degree quotient
discriminant chain: actual quotient ellipticity -> odd-prime quotient maps
and products -> cyclic-subgroup root interpretation -> inertia census ->
reverse genus and good reduction -> DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2.
The native affine addition formulas are retained. Adapted from the selected
odd-order quotient discriminant proof, anthropics/fermats-last-theorem,
Apache-2.0, commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
The doubling numerator is supplied separately by the already proved actual
division-polynomial multiplication formula, omitting its duplicate certificate. -/
namespace Dubon2026.SourceEllipticVelu.OddDiscriminant
open WeierstrassCurve
noncomputable section
variable {F : Type*} [Field F] [DecidableEq F]
variable {V : WeierstrassCurve F}
section PackSigma

variable (ha1 : V.a₁ = 0) (ha3 : V.a₃ = 0) {e₁ e₂ e₃ xq yq d : F}
  (hσ1 : e₁ + e₂ + e₃ = -V.a₂) (hσ2 : e₁ * e₂ + e₁ * e₃ + e₂ * e₃ = V.a₄)
  (hσ3 : e₁ * e₂ * e₃ = -V.a₆) (hq : V.toAffine.Equation xq yq)
  (h1 : xq ≠ e₁) (h2 : xq ≠ e₂) (h3 : xq ≠ e₃)
  (hd : d * (4 * xq ^ 3 + V.b₂ * xq ^ 2 + 2 * V.b₄ * xq + V.b₆)
      = xq ^ 4 - V.b₄ * xq ^ 2 - 2 * V.b₆ * xq - V.b₈)

/-- Actual x-coordinate after translating by a two-torsion point. -/
def xiAt (W' : WeierstrassCurve F) (e xq yq : F) : F :=
  W'.toAffine.addX e xq (W'.toAffine.slope e xq 0 yq)

include ha1 ha3 hσ1 hσ2 hσ3 hq h1 h2 h3 in

theorem xiAt_closed :
    xiAt V e₁ xq yq = e₁ + (e₁ - e₂) * (e₁ - e₃) / (xq - e₁) ∧
    xiAt V e₂ xq yq = e₂ + (e₂ - e₁) * (e₂ - e₃) / (xq - e₂) ∧
    xiAt V e₃ xq yq = e₃ + (e₃ - e₁) * (e₃ - e₂) / (xq - e₃) := by
  refine ⟨?_, ?_, ?_⟩
  · have t := addX_two_torsion_sub_self ha1 ha3 hσ1 hσ2 hσ3 hq h1
    unfold xiAt
    linear_combination t
  · have hσ1' : e₂ + e₁ + e₃ = -V.a₂ := by linear_combination hσ1
    have hσ2' : e₂ * e₁ + e₂ * e₃ + e₁ * e₃ = V.a₄ := by linear_combination hσ2
    have hσ3' : e₂ * e₁ * e₃ = -V.a₆ := by linear_combination hσ3
    have t := addX_two_torsion_sub_self ha1 ha3 hσ1' hσ2' hσ3' hq h2
    unfold xiAt
    linear_combination t
  · have hσ1' : e₃ + e₁ + e₂ = -V.a₂ := by linear_combination hσ1
    have hσ2' : e₃ * e₁ + e₃ * e₂ + e₁ * e₂ = V.a₄ := by linear_combination hσ2
    have hσ3' : e₃ * e₁ * e₂ = -V.a₆ := by linear_combination hσ3
    have t := addX_two_torsion_sub_self ha1 ha3 hσ1' hσ2' hσ3' hq h3
    unfold xiAt
    linear_combination t

include ha1 ha3 hσ1 hσ2 hσ3 hq h1 h2 h3 hd in

theorem pack_esymm1 :
    xiAt V e₁ xq yq + xiAt V e₂ xq yq + xiAt V e₃ xq yq + xq = 4 * d := by
  obtain ⟨t1, t2, t3⟩ := xiAt_closed ha1 ha3 hσ1 hσ2 hσ3 hq h1 h2 h3
  have hd1 : xq - e₁ ≠ 0 := sub_ne_zero.mpr h1
  have hd2 : xq - e₂ ≠ 0 := sub_ne_zero.mpr h2
  have hd3 : xq - e₃ ≠ 0 := sub_ne_zero.mpr h3
  rw [t1, t2, t3]
  simp only [b₂, b₄, b₆, b₈, ha1, ha3, zero_mul, mul_zero, sub_zero, add_zero] at hd
  field_simp
  linear_combination (norm := ring_nf)
    (-1) * hd
    + (4 * xq ^ 2 * d + 4 * V.a₆) * hσ1
    + (-4 * xq * d - 2 * xq ^ 2 + e₂ * e₃ + e₁ * e₃ + e₁ * e₂ + V.a₄) * hσ2
    + (4 * d + 8 * xq - 4 * e₃ - 4 * e₂ - 4 * e₁) * hσ3

include ha1 ha3 hσ1 hσ2 hσ3 hq h1 h2 h3 hd in

theorem pack_esymm2 :
    xiAt V e₁ xq yq * xiAt V e₂ xq yq + xiAt V e₁ xq yq * xiAt V e₃ xq yq
        + xiAt V e₂ xq yq * xiAt V e₃ xq yq
        + xq * (xiAt V e₁ xq yq + xiAt V e₂ xq yq + xiAt V e₃ xq yq)
      = -(V.b₄ + V.b₂ * d) := by
  obtain ⟨t1, t2, t3⟩ := xiAt_closed ha1 ha3 hσ1 hσ2 hσ3 hq h1 h2 h3
  have hd1 : xq - e₁ ≠ 0 := sub_ne_zero.mpr h1
  have hd2 : xq - e₂ ≠ 0 := sub_ne_zero.mpr h2
  have hd3 : xq - e₃ ≠ 0 := sub_ne_zero.mpr h3
  rw [t1, t2, t3]
  simp only [b₂, b₄, b₆, b₈, ha1, ha3, zero_mul, mul_zero, sub_zero, add_zero] at hd ⊢
  field_simp
  linear_combination (norm := ring_nf)
    (-e₃ - e₂ - e₁) * hd
    + (4 * xq ^ 3 * d + 4 * e₂ * e₃ * xq * d + 4 * e₁ * e₃ * xq * d + 4 * e₁ * e₂ * xq * d
      - 4 * e₁ * e₂ * e₃ * d + 4 * V.a₆ * e₃ + 4 * V.a₆ * e₂ + 4 * V.a₆ * e₁) * hσ1
    + (-2 * xq ^ 3 - 4 * e₃ * xq * d - 4 * e₂ * xq * d - 2 * e₂ * e₃ * xq + e₂ * e₃ ^ 2
      + e₂ ^ 2 * e₃ - 4 * e₁ * xq * d - 2 * e₁ * e₃ * xq + e₁ * e₃ ^ 2 - 2 * e₁ * e₂ * xq
      + 5 * e₁ * e₂ * e₃ + e₁ * e₂ ^ 2 + e₁ ^ 2 * e₃ + e₁ ^ 2 * e₂ + V.a₄ * e₃ + V.a₄ * e₂
      + V.a₄ * e₁) * hσ2
    + (4 * e₃ * d + 8 * e₃ * xq - 4 * e₃ ^ 2 + 4 * e₂ * d + 8 * e₂ * xq - 8 * e₂ * e₃ - 4 * e₂ ^ 2
      + 4 * e₁ * d + 8 * e₁ * xq - 8 * e₁ * e₃ - 8 * e₁ * e₂ - 4 * e₁ ^ 2) * hσ3

include ha1 ha3 hσ1 hσ2 hσ3 hq h1 h2 h3 hd in

theorem pack_esymm3 :
    xiAt V e₁ xq yq * xiAt V e₂ xq yq * xiAt V e₃ xq yq
        + xq * (xiAt V e₁ xq yq * xiAt V e₂ xq yq + xiAt V e₁ xq yq * xiAt V e₃ xq yq
          + xiAt V e₂ xq yq * xiAt V e₃ xq yq)
      = 2 * V.b₆ + 2 * V.b₄ * d := by
  obtain ⟨t1, t2, t3⟩ := xiAt_closed ha1 ha3 hσ1 hσ2 hσ3 hq h1 h2 h3
  have hd1 : xq - e₁ ≠ 0 := sub_ne_zero.mpr h1
  have hd2 : xq - e₂ ≠ 0 := sub_ne_zero.mpr h2
  have hd3 : xq - e₃ ≠ 0 := sub_ne_zero.mpr h3
  rw [t1, t2, t3]
  simp only [b₂, b₄, b₆, b₈, ha1, ha3, zero_mul, mul_zero, sub_zero, add_zero] at hd ⊢
  field_simp
  linear_combination (norm := ring_nf)
    (-e₂ * e₃ - e₁ * e₃ - e₁ * e₂) * hd
    + (4 * e₂ * e₃ * xq ^ 2 * d + 4 * e₁ * e₃ * xq ^ 2 * d + 4 * e₁ * e₂ * xq ^ 2 * d
      + 4 * V.a₆ * e₂ * e₃ + 4 * V.a₆ * e₁ * e₃ + 4 * V.a₆ * e₁ * e₂) * hσ1
    + (4 * xq ^ 3 * d - 4 * e₃ * xq ^ 2 * d - 4 * e₂ * xq ^ 2 * d - 2 * e₂ * e₃ * xq ^ 2
      + e₂ ^ 2 * e₃ ^ 2 - 4 * e₁ * xq ^ 2 * d - 2 * e₁ * e₃ * xq ^ 2 - 2 * e₁ * e₂ * xq ^ 2
      - 4 * e₁ * e₂ * e₃ * d + 2 * e₁ * e₂ * e₃ ^ 2 + 2 * e₁ * e₂ ^ 2 * e₃ + e₁ ^ 2 * e₃ ^ 2
      + 2 * e₁ ^ 2 * e₂ * e₃ + e₁ ^ 2 * e₂ ^ 2 + V.a₄ * e₂ * e₃ + V.a₄ * e₁ * e₃ + V.a₄ * e₁ * e₂) * hσ2
    + (-8 * xq ^ 3 + 8 * e₃ * xq ^ 2 + 8 * e₂ * xq ^ 2 + 4 * e₂ * e₃ * d - 4 * e₂ * e₃ ^ 2
      - 4 * e₂ ^ 2 * e₃ + 8 * e₁ * xq ^ 2 + 4 * e₁ * e₃ * d - 4 * e₁ * e₃ ^ 2 + 4 * e₁ * e₂ * d
      - 4 * e₁ * e₂ * e₃ - 4 * e₁ * e₂ ^ 2 - 4 * e₁ ^ 2 * e₃ - 4 * e₁ ^ 2 * e₂) * hσ3

include ha1 ha3 hσ1 hσ2 hσ3 hq h1 h2 h3 hd in

theorem pack_esymm4 :
    xiAt V e₁ xq yq * xiAt V e₂ xq yq * xiAt V e₃ xq yq * xq = -(V.b₈ + V.b₆ * d) := by
  obtain ⟨t1, t2, t3⟩ := xiAt_closed ha1 ha3 hσ1 hσ2 hσ3 hq h1 h2 h3
  have hd1 : xq - e₁ ≠ 0 := sub_ne_zero.mpr h1
  have hd2 : xq - e₂ ≠ 0 := sub_ne_zero.mpr h2
  have hd3 : xq - e₃ ≠ 0 := sub_ne_zero.mpr h3
  rw [t1, t2, t3]
  simp only [b₂, b₄, b₆, b₈, ha1, ha3, zero_mul, mul_zero, sub_zero, add_zero] at hd ⊢
  field_simp
  linear_combination (norm := ring_nf)
    (-e₁ * e₂ * e₃) * hd
    + (4 * e₁ * e₂ * e₃ * xq ^ 2 * d + 4 * V.a₆ * xq ^ 3 - 4 * V.a₆ * e₃ * xq ^ 2
      - 4 * V.a₆ * e₂ * xq ^ 2 + 4 * V.a₆ * e₂ * e₃ * xq - 4 * V.a₆ * e₁ * xq ^ 2
      + 4 * V.a₆ * e₁ * e₃ * xq + 4 * V.a₆ * e₁ * e₂ * xq) * hσ1
    + (e₂ * e₃ * xq ^ 3 - e₂ * e₃ ^ 2 * xq ^ 2 - e₂ ^ 2 * e₃ * xq ^ 2 + e₂ ^ 2 * e₃ ^ 2 * xq
      + e₁ * e₃ * xq ^ 3 - e₁ * e₃ ^ 2 * xq ^ 2 + e₁ * e₂ * xq ^ 3 - 4 * e₁ * e₂ * e₃ * xq * d
      - 5 * e₁ * e₂ * e₃ * xq ^ 2 + 2 * e₁ * e₂ * e₃ ^ 2 * xq - e₁ * e₂ ^ 2 * xq ^ 2
      + 2 * e₁ * e₂ ^ 2 * e₃ * xq - e₁ ^ 2 * e₃ * xq ^ 2 + e₁ ^ 2 * e₃ ^ 2 * xq
      - e₁ ^ 2 * e₂ * xq ^ 2 + 2 * e₁ ^ 2 * e₂ * e₃ * xq + e₁ ^ 2 * e₂ ^ 2 * xq + V.a₄ * xq ^ 3
      - V.a₄ * e₃ * xq ^ 2 - V.a₄ * e₂ * xq ^ 2 + V.a₄ * e₂ * e₃ * xq - V.a₄ * e₁ * xq ^ 2
      + V.a₄ * e₁ * e₃ * xq + V.a₄ * e₁ * e₂ * xq) * hσ2
    + (4 * xq ^ 3 * d - 4 * e₃ * xq ^ 2 * d - 4 * e₃ * xq ^ 3 + 4 * e₃ ^ 2 * xq ^ 2
      - 4 * e₂ * xq ^ 2 * d - 4 * e₂ * xq ^ 3 + 4 * e₂ * e₃ * xq * d + 8 * e₂ * e₃ * xq ^ 2
      - 4 * e₂ * e₃ ^ 2 * xq + 4 * e₂ ^ 2 * xq ^ 2 - 4 * e₂ ^ 2 * e₃ * xq - 4 * e₁ * xq ^ 2 * d
      - 4 * e₁ * xq ^ 3 + 4 * e₁ * e₃ * xq * d + 8 * e₁ * e₃ * xq ^ 2 - 4 * e₁ * e₃ ^ 2 * xq
      + 4 * e₁ * e₂ * xq * d + 8 * e₁ * e₂ * xq ^ 2 - 4 * e₁ * e₂ * e₃ * xq - 4 * e₁ * e₂ ^ 2 * xq
      + 4 * e₁ ^ 2 * xq ^ 2 - 4 * e₁ ^ 2 * e₃ * xq - 4 * e₁ ^ 2 * e₂ * xq) * hσ3

end PackSigma

end
end Dubon2026.SourceEllipticVelu.OddDiscriminant
