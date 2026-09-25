import TaoTrudgianYang2025.RobertSargosWeightedGcdFibers
import TaoTrudgianYang2025.RobertSargosGcdProjection
import TaoTrudgianYang2025.RobertSargosGcdSums

/-! Full six-variable count before gcd normalization, for every nonzero displacement. -/

noncomputable section
namespace TaoTrudgianYang2025

theorem exists_robertSargos_reduced_count (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset RobertSargosPoint) (R H Q δ : ℝ),
      1 ≤ R → 1 ≤ H → 1 ≤ Q → 0 ≤ δ → R ≤ H/2 →
      (∀ p ∈ S, RobertSargosReducedSystem R H Q δ p) →
      (S.card:ℝ) ≤ C*(R*H*Q)^(1+ε)*(1+δ*Q) := by
  classical
  have hη : 0 < ε/2 := by linarith
  obtain ⟨Cf,hCf,hfiber⟩ := exists_robertSargos_weighted_gcd_fiber_count (ε/2) hη
  obtain ⟨Ch,hCh,hharmonic⟩ := exists_robertSargos_gcd_harmonic_bound (ε/2) hη
  refine ⟨Cf*Ch,by positivity,?_⟩
  intro S R H Q δ hR hH hQ hδ hRH hmem
  have hQp : 0 < Q := by linarith
  have hB : 0 < R*H*Q := by positivity
  let F : Finset (ℕ × ℕ) := (Finset.Icc 1 ⌊R⌋₊) ×ˢ (Finset.Icc 1 ⌊2*Q⌋₊)
  let M : ℝ := Cf*(R*H*Q)^(1+ε/2)*(1+δ*Q)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hmaps : Set.MapsTo robertSargosGcdKey S F := by
    intro p hp
    exact (hmem p hp).gcd_key_mem hQp
  have hcardR : (S.card:ℝ) =
      ∑ z ∈ F, ((S.filter (fun p => robertSargosGcdKey p = z)).card:ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_fiberwise hmaps
  have hf : ∀ z ∈ F, ((S.filter (fun p => robertSargosGcdKey p = z)).card:ℝ) ≤
      M*((1:ℝ)/((z.1:ℝ)*(z.2:ℝ))) := by
    intro z hz
    have h₁ := Finset.mem_Icc.mp (Finset.mem_product.mp hz).1
    have h₂ := Finset.mem_Icc.mp (Finset.mem_product.mp hz).2
    have hkQ : (z.2:ℝ) ≤ 2*Q :=
      (Nat.le_floor_iff (by positivity : 0 ≤ 2*Q)).mp h₂.2
    have hb := hfiber (S.filter (fun p => robertSargosGcdKey p = z))
      R H Q δ z.1 z.2 hR hH hQ hδ hRH h₁.1 h₂.1 hkQ
      (fun p hp => hmem p (Finset.mem_filter.mp hp).1)
      (fun p hp => (congrArg (fun z : ℕ × ℕ => z.1) (Finset.mem_filter.mp hp).2).symm)
      (fun p hp => (congrArg (fun z : ℕ × ℕ => z.2) (Finset.mem_filter.mp hp).2).symm)
    simpa only [M,div_eq_mul_inv,one_mul] using hb
  have hw : (∑ z ∈ F, (1:ℝ)/((z.1:ℝ)*(z.2:ℝ))) =
      (harmonic ⌊R⌋₊:ℝ)*(harmonic ⌊2*Q⌋₊:ℝ) := by
    dsimp [F]
    rw [Finset.sum_product]
    exact sum_inverse_gcd_product _ _
  have hpow : (R*H*Q)^(1+ε/2)*(R*H*Q)^(ε/2) = (R*H*Q)^(1+ε) := by
    rw [← Real.rpow_add hB]
    congr 1
    ring
  calc
    _ = _ := hcardR
    _ ≤ ∑ z ∈ F, M*((1:ℝ)/((z.1:ℝ)*(z.2:ℝ))) := Finset.sum_le_sum hf
    _ = M*(∑ z ∈ F, (1:ℝ)/((z.1:ℝ)*(z.2:ℝ))) := by rw [Finset.mul_sum]
    _ = M*((harmonic ⌊R⌋₊:ℝ)*(harmonic ⌊2*Q⌋₊:ℝ)) := by rw [hw]
    _ ≤ M*(Ch*(R*H*Q)^(ε/2)) :=
      mul_le_mul_of_nonneg_left (hharmonic R H Q hR hH hQ) hM
    _ = (Cf*Ch)*((R*H*Q)^(1+ε/2)*(R*H*Q)^(ε/2))*(1+δ*Q) := by
      dsimp [M]
      ring
    _ = _ := by rw [hpow]

end TaoTrudgianYang2025

