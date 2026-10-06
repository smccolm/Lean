import DhimanKadiriQuesadaHerrera2026.StationaryCapped

namespace DhimanKadiriQuesadaHerrera2026
open MeasureTheory

/-- The actual finite family of stationary integral errors sums with its exact cardinality and endpoint gaps. -/
theorem stationary_sum_gap_bound {f : ℝ → ℝ} {a b D ℓ : ℝ} (S : Finset ℕ) (ξ : ℕ → ℝ)
    (hℓ : 0 < ℓ)
    (hξ : ∀ ν ∈ S, ξ ν ∈ Set.Icc a b ∧ deriv f (ξ ν) = (ν : ℝ))
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hcurv : ∀ u ∈ Set.Icc a b, deriv (deriv f) u ≤ -ℓ)
    (hD : ∀ u ∈ Set.Icc a b, |deriv (deriv (deriv f)) u| ≤ D) :
    ‖(∑ ν ∈ S, ∫ u in a..b,
        Complex.exp (2 * Real.pi * Complex.I * ((f u - (ν : ℝ) * u : ℝ) : ℂ))) -
      ∑ ν ∈ S, Complex.exp (2 * Real.pi * Complex.I * ((f (ξ ν) - (ν : ℝ) * ξ ν - 1 / 8 : ℝ) : ℂ)) /
        (Real.sqrt |deriv (deriv f) (ξ ν)| : ℂ)‖ ≤
      (S.card : ℝ) * ((2 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * D ^ (1 / 3 : ℝ) / ℓ) +
        ∑ ν ∈ S, (stationaryEndpointCap ℓ (deriv f a - (ν : ℝ)) + stationaryEndpointCap ℓ (deriv f b - (ν : ℝ))) := by
  rw [← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  have h := Finset.sum_le_sum (s := S) (fun ν hν =>
    stationary_phase_gap_bound hℓ (hξ ν hν).1.1 (hξ ν hν).1.2 (hξ ν hν).2 hf hf' hf'' hcurv hD)
  apply h.trans_eq
  simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
  ring


/-- The actual full Fourier sum is compared with the complete stationary family, including its last frequency and endpoint critical points. -/
theorem exists_full_stationary_gap_bound {f : ℝ → ℝ} {a b D ℓ : ℝ}
    (hab : a < b) (hℓ : 0 < ℓ) (hαpos : 0 ≤ deriv f b) (hα : deriv f b < 1)
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hanti : StrictAntiOn (deriv f) (Set.Icc a b))
    (hlower : ∀ u ∈ Set.Icc a b, ℓ ≤ |deriv (deriv f) u|)
    (hD : ∀ u ∈ Set.Icc a b, |deriv (deriv (deriv f)) u| ≤ D) :
    ∃ ξ : ℕ → ℝ, (∀ ν ∈ Finset.Icc 1 ⌊deriv f a⌋₊,
      ξ ν ∈ Set.Icc a b ∧ deriv f (ξ ν) = (ν : ℝ)) ∧
    ‖(∑ ν ∈ Finset.Icc 0 ⌊deriv f a⌋₊, ∫ u in a..b,
        Complex.exp (2 * Real.pi * Complex.I * ((f u - (ν : ℝ) * u : ℝ) : ℂ))) -
      ∑ ν ∈ Finset.Icc 1 ⌊deriv f a⌋₊,
        Complex.exp (2 * Real.pi * Complex.I * ((f (ξ ν) - (ν : ℝ) * ξ ν - 1 / 8 : ℝ) : ℂ)) /
          (Real.sqrt |deriv (deriv f) (ξ ν)| : ℂ)‖ ≤
      0.6715 / Real.sqrt ℓ + (⌊deriv f a⌋₊ : ℝ) *
        ((2 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * D ^ (1 / 3 : ℝ) / ℓ) +
        ∑ ν ∈ Finset.Icc 1 ⌊deriv f a⌋₊,
          (stationaryEndpointCap ℓ (deriv f a - (ν : ℝ)) + stationaryEndpointCap ℓ (deriv f b - (ν : ℝ))) := by
  have hfc : ContinuousOn (deriv f) (Set.Icc a b) :=
    fun u hu => (hf' u hu).continuousAt.continuousWithinAt
  obtain ⟨ξ, hξ⟩ := exists_stationary_family hab.le hfc hanti hα
  refine ⟨ξ, hξ, ?_⟩
  have hi := stationary_sum_gap_bound (Finset.Icc 1 ⌊deriv f a⌋₊) ξ hℓ hξ hf hf' hf''
    (stationary_curvature_of_antitone hab hf' hanti.antitoneOn hlower) hD
  have hcard : (Finset.Icc 1 ⌊deriv f a⌋₊).card = ⌊deriv f a⌋₊ := by rw [Nat.card_Icc]; omega
  rw [hcard] at hi
  have hz := kershner_zero_frequency hab hℓ hf hf' hf'' hanti hαpos hlower
  have hs : Finset.Icc 0 ⌊deriv f a⌋₊ = insert 0 (Finset.Icc 1 ⌊deriv f a⌋₊) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  rw [hs, Finset.sum_insert (by simp)]
  simp only [Nat.cast_zero, zero_mul, sub_zero]
  rw [add_sub_assoc]
  exact (norm_add_le _ _).trans ((add_le_add hz hi).trans_eq (by ring))

end DhimanKadiriQuesadaHerrera2026
