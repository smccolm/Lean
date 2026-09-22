import TaoTrudgianYang2025.BetaPoissonBoundary

/-!
# Exact stationary sums in canonical dual coordinates

The physical stationary exponents are linked to the literal canonical
exponential sum, including conjugation and the unit common phase.
These are exact identities, not stationary-phase approximations.
-/

noncomputable section

open Set Expdb
open scoped FourierTransform BigOperators

namespace TaoTrudgianYang2025

theorem modelPhaseStationaryPoint_weighted_sum_canonical
    {χ F : ℝ → ℝ} {σ A w T N : ℝ}
    (hA : 0 < A) (hw : 0 < w) (hT : T ≠ 0) (hN : N ≠ 0)
    (S : Finset ℤ) (c : ℤ → ℝ)
    (hv : ∀ r ∈ S, 0 < (r : ℝ)*N/T)
    (hχ : ∀ r ∈ S, χ ((r : ℝ)*N/T) = 1) :
    (∑ r ∈ S, (c r : ℂ) *
      (𝐞 (modelPhaseFrequencyPhase F T N r (modelPhaseStationaryPoint F T N r)) : ℂ)) =
      (𝐞 (modelPhaseDualOffset F σ A w T) : ℂ) *
        starRingEnd ℂ (∑ r ∈ S, (c r : ℂ) *
          (𝐞 (modelPhaseDualParameter σ A T *
            canonicalLegendrePhase χ F σ A w ((r : ℝ)/modelPhaseDualScale A T N)) : ℂ)) := by
  rw [map_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  rw [modelPhaseStationaryPoint_canonical_fourier hA hw hT hN (hv r hr) (hχ r hr)]
  simp only [map_mul,Complex.conj_ofReal]
  ring

theorem norm_modelPhaseStationaryPoint_weighted_sum
    {χ F : ℝ → ℝ} {σ A w T N : ℝ}
    (hA : 0 < A) (hw : 0 < w) (hT : T ≠ 0) (hN : N ≠ 0)
    (S : Finset ℤ) (c : ℤ → ℝ)
    (hv : ∀ r ∈ S, 0 < (r : ℝ)*N/T)
    (hχ : ∀ r ∈ S, χ ((r : ℝ)*N/T) = 1) :
    ‖∑ r ∈ S, (c r : ℂ) *
      (𝐞 (modelPhaseFrequencyPhase F T N r (modelPhaseStationaryPoint F T N r)) : ℂ)‖ =
      ‖∑ r ∈ S, (c r : ℂ) *
        (𝐞 (modelPhaseDualParameter σ A T *
          canonicalLegendrePhase χ F σ A w ((r : ℝ)/modelPhaseDualScale A T N)) : ℂ)‖ := by
  rw [modelPhaseStationaryPoint_weighted_sum_canonical hA hw hT hN S c hv hχ,
    norm_mul,Circle.norm_coe,one_mul]
  exact Complex.norm_conj _

theorem modelPhaseStationaryPoint_interval_canonical
    {χ F : ℝ → ℝ} {σ A w T N : ℝ}
    (hA : 0 < A) (hw : 0 < w) (hT : T ≠ 0) (hN : N ≠ 0)
    (a b : ℕ)
    (hv : ∀ r ∈ Finset.Icc (a : ℤ) (b : ℤ), 0 < (r : ℝ)*N/T)
    (hχ : ∀ r ∈ Finset.Icc (a : ℤ) (b : ℤ), χ ((r : ℝ)*N/T) = 1) :
    (∑ r ∈ Finset.Icc (a : ℤ) (b : ℤ),
      (𝐞 (modelPhaseFrequencyPhase F T N r (modelPhaseStationaryPoint F T N r)) : ℂ)) =
      (𝐞 (modelPhaseDualOffset F σ A w T) : ℂ) *
        starRingEnd ℂ (exponentialSumAt (canonicalLegendrePhase χ F σ A w)
          (modelPhaseDualParameter σ A T) (modelPhaseDualScale A T N) a b) := by
  rw [exponentialSumAt_eq_int_sum]
  simpa only [Complex.ofReal_one,one_mul] using
    modelPhaseStationaryPoint_weighted_sum_canonical hA hw hT hN
      (Finset.Icc (a : ℤ) (b : ℤ)) (fun _ => 1) hv hχ

theorem norm_modelPhaseStationaryPoint_interval
    {χ F : ℝ → ℝ} {σ A w T N : ℝ}
    (hA : 0 < A) (hw : 0 < w) (hT : T ≠ 0) (hN : N ≠ 0)
    (a b : ℕ)
    (hv : ∀ r ∈ Finset.Icc (a : ℤ) (b : ℤ), 0 < (r : ℝ)*N/T)
    (hχ : ∀ r ∈ Finset.Icc (a : ℤ) (b : ℤ), χ ((r : ℝ)*N/T) = 1) :
    ‖∑ r ∈ Finset.Icc (a : ℤ) (b : ℤ),
      (𝐞 (modelPhaseFrequencyPhase F T N r (modelPhaseStationaryPoint F T N r)) : ℂ)‖ =
      ‖exponentialSumAt (canonicalLegendrePhase χ F σ A w)
        (modelPhaseDualParameter σ A T) (modelPhaseDualScale A T N) a b‖ := by
  rw [modelPhaseStationaryPoint_interval_canonical hA hw hT hN a b hv hχ,
    norm_mul,Circle.norm_coe,one_mul]
  exact Complex.norm_conj _

end TaoTrudgianYang2025
