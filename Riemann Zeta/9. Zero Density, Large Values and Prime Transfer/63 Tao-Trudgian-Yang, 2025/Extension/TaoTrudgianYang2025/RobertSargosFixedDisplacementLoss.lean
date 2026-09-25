import TaoTrudgianYang2025.PrimitiveDivisorGrowth
import TaoTrudgianYang2025.RobertSargosFixedDisplacementConic
import TaoTrudgianYang2025.RobertSargosFixedDisplacementLinear

/-! Uniform epsilon-loss forms of the two actual fixed-displacement counts. -/

noncomputable section
namespace TaoTrudgianYang2025

theorem exists_robertSargos_fixed_displacement_conic_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (S : Finset (ℤ × ℤ × ℤ)) (d q₁ q₂ : ℤ) (H Q δ : ℝ),
      Int.gcd (Int.gcd d q₁ : ℤ) q₂ = 1 → d ≠ 0 →
      0 < H → 0 < Q → 0 ≤ δ →
      Q ≤ |(q₁:ℝ)| → Q ≤ |(q₂:ℝ)| → 0 < q₁*q₂ →
      (∀ p ∈ S, (p.1:ℝ) ∈ Set.Icc H (2*H)) →
      (∀ p ∈ S, (p.2.1:ℝ) ∈ Set.Icc H (2*H)) →
      (∀ p ∈ S, Int.gcd (Int.gcd p.2.2 p.1 : ℤ) p.2.1 = 1) →
      (∀ p ∈ S, p.2.2*d+q₁*p.1-q₂*p.2.1 = 0) →
      (∀ p ∈ S, |robertSargosReduced p.2.2 q₁ q₂ p.1 p.2.1 d| ≤ δ*H*Q^2) →
      (S.card:ℝ) ≤ C*(d.natAbs:ℝ)^ε*(1+8*H^2*δ/d.natAbs) := by
  obtain ⟨C,hC,hdiv⟩ := exists_primitive_divisor_bound ε hε
  refine ⟨C,hC,?_⟩
  intro S d q₁ q₂ H Q δ hc hd hH hQ hδ hq₁ hq₂ hs hh₁ hh₂ hp hl hn
  exact (robertSargos_fixed_displacement_conic_card_le S hc hd hH hQ hδ hq₁ hq₂ hs
    hh₁ hh₂ hp hl hn).trans (hdiv d.natAbs (8*H^2*δ) (Int.natAbs_pos.mpr hd) (by positivity))

theorem exists_robertSargos_fixed_displacement_linear_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (S : Finset (ℤ × ℤ × ℤ)) (d q₁ q₂ : ℤ) (R H Q δ : ℝ),
      Int.gcd (Int.gcd d q₁ : ℤ) q₂ = 1 → d ≠ 0 →
      0 ≤ R → 0 < H → 0 < Q → δ ≤ 1 →
      |(q₁:ℝ)| ∈ Set.Icc Q (2*Q) → |(q₂:ℝ)| ∈ Set.Icc Q (2*Q) → 0 < q₁*q₂ →
      (∀ p ∈ S, (p.1:ℝ) ∈ Set.Icc H (2*H)) →
      (∀ p ∈ S, (p.2.1:ℝ) ∈ Set.Icc H (2*H)) →
      (∀ p ∈ S, |(p.2.2:ℝ)| ≤ R) →
      (∀ p ∈ S, Int.gcd (Int.gcd p.2.2 p.1 : ℤ) p.2.1 = 1) →
      (∀ p ∈ S, p.2.2*d+q₁*p.1-q₂*p.2.1 = 0) →
      (∀ p ∈ S, |robertSargosReduced p.2.2 q₁ q₂ p.1 p.2.1 d| ≤ δ*H*Q^2) →
      (S.card:ℝ) ≤ C*(d.natAbs:ℝ)^ε*(1+72*H*R/d.natAbs) := by
  obtain ⟨C,hC,hdiv⟩ := exists_primitive_divisor_bound ε hε
  refine ⟨C,hC,?_⟩
  intro S d q₁ q₂ R H Q δ hc hd hR hH hQ hδ hq₁ hq₂ hs hh₁ hh₂ hr hp hl hn
  exact (robertSargos_fixed_displacement_linear_card_le S hc hd hR hH hQ hδ hq₁ hq₂ hs
    hh₁ hh₂ hr hp hl hn).trans (hdiv d.natAbs (72*H*R) (Int.natAbs_pos.mpr hd) (by positivity))

end TaoTrudgianYang2025

