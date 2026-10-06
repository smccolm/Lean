import Dubon2026.PrimeSelection
import Dubon2026.IsolatedPrimeSupport

/-! # The isolated-prime Jessen lower bound with the literal source block and compact quantifiers -/

namespace Dubon2026

open Filter Set

noncomputable section

theorem exists_uniform_isolated_prime_lower {K : ℝ} (hK : 1 ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : ℕ → ℂ) (N : ℕ), 1 ≤ N → a 1 ≠ 0 →
      ∀ (σ : ℝ) (Q : Finset ℕ),
      (∀ p ∈ Q, Nat.Prime p ∧ (N : ℝ) / 2 < p ∧ p ≤ N) → 5 ≤ Q.card →
      (∀ p ∈ Q, a p ≠ 0) →
      (∀ p ∈ Q, ∀ q ∈ Q, (‖a p‖ * (p : ℝ) ^ (-σ)) / (‖a q‖ * (q : ℝ) ^ (-σ)) ≤ K) →
      (1 / 2 : ℝ) * Real.log (∑ p ∈ Q, ‖a p‖ ^ 2 * (p : ℝ) ^ (-2 * σ)) - C ≤
        jessenFunction a N σ := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_isolated_jessen_lower hK
  refine ⟨C, hC, ?_⟩
  intro a N hN ha σ Q hQ hm hap hcomp
  let S := selectedPrimeCoordinates N Q
  have hQ' : ∀ p ∈ Q, Nat.Prime p ∧ p ≤ N := fun p hp => ⟨(hQ p hp).1, (hQ p hp).2.2⟩
  have hcard : 5 ≤ Fintype.card ↥S := by
    rw [card_selectedPrimeCoordinates N Q hQ']
    exact hm
  letI : Nonempty ↥S := Fintype.card_pos_iff.mp (by omega)
  have hS : ∀ p ∈ S, N < 2 * p.val := by
    intro p hp
    have hhalf := (hQ p.val (mem_selectedPrimeCoordinates.mp hp)).2.1
    have hh : (N : ℝ) < 2 * (p.val : ℝ) := by linarith
    exact_mod_cast hh
  have hcoeff : ∀ p : ↥S, a p.val.val ≠ 0 := fun p =>
    hap p.val.val (mem_selectedPrimeCoordinates.mp p.property)
  have hc : steinhausMaxCoefficient (fun p : ↥S => ‖a p.val.val‖ * (p.val.val : ℝ) ^ (-σ)) /
      steinhausMinCoefficient (fun p : ↥S => ‖a p.val.val‖ * (p.val.val : ℝ) ^ (-σ)) ≤ K := by
    apply steinhaus_max_min_le_of_pairwise
    intro p q
    exact hcomp p.val.val (mem_selectedPrimeCoordinates.mp p.property)
      q.val.val (mem_selectedPrimeCoordinates.mp q.property)
  have hl := hbound a N hN ha σ S hS hcard hcoeff hc
  rw [sum_selectedPrimeCoordinates N Q hQ' (fun p : ℕ => ‖a p‖ ^ 2 * (p : ℝ) ^ (-2 * σ))] at hl
  exact hl

/-- The compact-uniform Proposition 5.1 bound from the source's actual H2 comparability. -/
theorem eventually_isolated_jessen_lower {a : ℕ → ℂ} {Q : ℕ → Finset ℕ} {α : ℝ}
    (ha : a 1 = 1) (hQ : IsolatedPrimeBlocks Q)
    (hcard : Tendsto (fun N => (Q N).card) atTop atTop)
    (hc : PrimeCoefficientComparability a Q α) {l u : ℝ} (hlu : l ≤ u) (hu : u < α) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop, ∀ σ ∈ Icc l u,
      (1 / 2 : ℝ) * Real.log (∑ p ∈ Q N, ‖a p‖ ^ 2 * (p : ℝ) ^ (-2 * σ)) - C ≤
        jessenFunction a N σ := by
  obtain ⟨K, hK, hcomp⟩ := hc l u hlu hu
  obtain ⟨C, hC, hbound⟩ := exists_uniform_isolated_prime_lower hK
  refine ⟨C, hC, ?_⟩
  filter_upwards [hcomp, eventually_primeBlock_coefficients_ne_zero hc,
    hcard.eventually_ge_atTop 5, eventually_ge_atTop (1 : ℕ)] with N hcompN hcoeff hcardN hN
  intro σ hσ
  exact hbound a N hN (ha.trans_ne one_ne_zero) σ (Q N) (hQ N) hcardN hcoeff
    (fun p hp q hq => (hcompN σ hσ p hp q hq).2)

/-- Finite-block form with the source's literal maximum/minimum ratio. -/
theorem exists_uniform_isolated_prime_lower_max_min {K : ℝ} (hK : 1 ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : ℕ → ℂ) (N : ℕ), 1 ≤ N → a 1 ≠ 0 →
      ∀ (σ : ℝ) (Q : Finset ℕ) [Nonempty ↥Q],
      (∀ p ∈ Q, Nat.Prime p ∧ (N : ℝ) / 2 < p ∧ p ≤ N) → 5 ≤ Q.card →
      (∀ p ∈ Q, a p ≠ 0) →
      (Finset.univ.sup' Finset.univ_nonempty (fun p : ↥Q => ‖a p.val‖ * (p.val : ℝ) ^ (-σ))) /
        (Finset.univ.inf' Finset.univ_nonempty (fun p : ↥Q => ‖a p.val‖ * (p.val : ℝ) ^ (-σ))) ≤ K →
      (1 / 2 : ℝ) * Real.log (∑ p ∈ Q, ‖a p‖ ^ 2 * (p : ℝ) ^ (-2 * σ)) - C ≤
        jessenFunction a N σ := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_isolated_prime_lower hK
  refine ⟨C, hC, ?_⟩
  intro a N hN ha σ Q _ hQ hm hap hcomp
  have hb : ∀ p : ↥Q, 0 < ‖a p.val‖ * (p.val : ℝ) ^ (-σ) := fun p =>
    mul_pos (norm_pos_iff.mpr (hap p.val p.property))
      (Real.rpow_pos_of_pos (by exact_mod_cast (hQ p.val p.property).1.pos) _)
  have hpairs := steinhaus_pairwise_of_max_min
    (fun p : ↥Q => ‖a p.val‖ * (p.val : ℝ) ^ (-σ)) hb hK hcomp
  apply hbound a N hN ha σ Q hQ hm hap
  intro p hp q hq
  exact (div_le_iff₀ (hb ⟨q, hq⟩)).mpr (hpairs ⟨p, hp⟩ ⟨q, hq⟩)

end

end Dubon2026
