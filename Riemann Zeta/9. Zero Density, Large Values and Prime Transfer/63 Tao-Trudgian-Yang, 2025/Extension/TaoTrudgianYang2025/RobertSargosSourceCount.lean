import TaoTrudgianYang2025.RobertSargosSevenCount

/-! Literal half-open source entry for Robert--Sargos (2002), Theorem 2. -/

noncomputable section
namespace TaoTrudgianYang2025

theorem robertSargos_sevenSystem_of_source_bounds
    {R H Q N δ : ℝ} {p : RobertSargosSevenPoint}
    (hr : 0 < |(p.r:ℝ)| ∧ |(p.r:ℝ)| < R)
    (hq₁ : |(p.q₁:ℝ)| ∈ Set.Ico Q (2*Q))
    (hq₂ : |(p.q₂:ℝ)| ∈ Set.Ico Q (2*Q))
    (hh₁ : (p.h₁:ℝ) ∈ Set.Ico H (2*H))
    (hh₂ : (p.h₂:ℝ) ∈ Set.Ico H (2*H))
    (hn₁ : (p.n₁:ℝ) ∈ Set.Icc 1 N) (hn₂ : (p.n₂:ℝ) ∈ Set.Icc 1 N)
    (hsign : 0 < p.q₁*p.q₂)
    (hline : p.r*p.n₁+p.h₁*p.q₁ = p.r*p.n₂+p.h₂*p.q₂)
    (hnear : |robertSargosQuadratic p.r p.q₁ p.h₁ p.n₁-
      robertSargosQuadratic p.r p.q₂ p.h₂ p.n₂| ≤ δ*H*Q^2) :
    RobertSargosSevenSystem R H Q N δ p := by
  have hrn : p.r ≠ 0 := by exact_mod_cast abs_pos.mp hr.1
  exact ⟨hrn,hr.2.le,⟨hq₁.1,hq₁.2.le⟩,⟨hq₂.1,hq₂.2.le⟩,
    ⟨hh₁.1,hh₁.2.le⟩,⟨hh₂.1,hh₂.2.le⟩,hn₁,hn₂,hsign,hline,hnear⟩

theorem exists_robertSargos_source_count (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset RobertSargosSevenPoint) (R H Q N δ : ℝ),
      1 ≤ R → 1 ≤ H → 1 ≤ Q → 1 ≤ N → 0 < δ → R ≤ H/2 →
      (∀ p ∈ S, 0 < |(p.r:ℝ)| ∧ |(p.r:ℝ)| < R) →
      (∀ p ∈ S, |(p.q₁:ℝ)| ∈ Set.Ico Q (2*Q)) →
      (∀ p ∈ S, |(p.q₂:ℝ)| ∈ Set.Ico Q (2*Q)) →
      (∀ p ∈ S, (p.h₁:ℝ) ∈ Set.Ico H (2*H)) →
      (∀ p ∈ S, (p.h₂:ℝ) ∈ Set.Ico H (2*H)) →
      (∀ p ∈ S, (p.n₁:ℝ) ∈ Set.Icc 1 N) →
      (∀ p ∈ S, (p.n₂:ℝ) ∈ Set.Icc 1 N) →
      (∀ p ∈ S, 0 < p.q₁*p.q₂) →
      (∀ p ∈ S, p.r*p.n₁+p.h₁*p.q₁ = p.r*p.n₂+p.h₂*p.q₂) →
      (∀ p ∈ S, |robertSargosQuadratic p.r p.q₁ p.h₁ p.n₁-
        robertSargosQuadratic p.r p.q₂ p.h₂ p.n₂| ≤ δ*H*Q^2) →
      (S.card:ℝ) ≤ C*(R*N*H*Q)^(1+ε)*(1+δ*Q) := by
  obtain ⟨C,hC,hcount⟩ := exists_robertSargos_seven_count ε hε
  refine ⟨C,hC,?_⟩
  intro S R H Q N δ hR hH hQ hN hδ hRH hr hq₁ hq₂ hh₁ hh₂ hn₁ hn₂ hsign hline hnear
  apply hcount S R H Q N δ hR hH hQ hN hδ.le hRH
  intro p hp
  exact robertSargos_sevenSystem_of_source_bounds (hr p hp) (hq₁ p hp) (hq₂ p hp)
    (hh₁ p hp) (hh₂ p hp) (hn₁ p hp) (hn₂ p hp) (hsign p hp) (hline p hp) (hnear p hp)

end TaoTrudgianYang2025

