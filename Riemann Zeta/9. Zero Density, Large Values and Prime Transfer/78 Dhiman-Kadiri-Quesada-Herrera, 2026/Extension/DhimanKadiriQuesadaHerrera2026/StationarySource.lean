import DhimanKadiriQuesadaHerrera2026.StationaryHarmonic

namespace DhimanKadiriQuesadaHerrera2026

/-- The source's decreasing derivative and absolute curvature bound imply the required signed bound, including the endpoints. -/
theorem stationary_curvature_of_antitone {f : ℝ → ℝ} {a b ℓ : ℝ} (hab : a < b)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hanti : AntitoneOn (deriv f) (Set.Icc a b))
    (hlower : ∀ u ∈ Set.Icc a b, ℓ ≤ |deriv (deriv f) u|) :
    ∀ u ∈ Set.Icc a b, deriv (deriv f) u ≤ -ℓ := by
  intro u hu
  have hn := hanti.derivWithin_nonpos (x := u)
  rw [(hf' u hu).hasDerivAt.hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc hab u hu)] at hn
  have hl := hlower u hu
  rw [abs_of_nonpos hn] at hl
  linarith

/-- All positive frequencies through the upper floor have actual stationary points from the source derivative range. -/
theorem exists_stationary_family {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hfc : ContinuousOn (deriv f) (Set.Icc a b))
    (hanti : StrictAntiOn (deriv f) (Set.Icc a b)) (hα : deriv f b < 1) :
    ∃ ξ : ℕ → ℝ, ∀ ν ∈ Finset.Icc 1 ⌊deriv f a⌋₊,
      ξ ν ∈ Set.Icc a b ∧ deriv f (ξ ν) = (ν : ℝ) := by
  classical
  have hp : ∀ ν : ℕ, ∃ x : ℝ, ν ∈ Finset.Icc 1 ⌊deriv f a⌋₊ →
      x ∈ Set.Icc a b ∧ deriv f x = (ν : ℝ) := by
    intro ν
    by_cases hν : ν ∈ Finset.Icc 1 ⌊deriv f a⌋₊
    · have hn := Finset.mem_Icc.mp hν
      have hν1 : (1 : ℝ) ≤ ν := by exact_mod_cast hn.1
      have hm : 1 ≤ ⌊deriv f a⌋₊ := hn.1.trans hn.2
      have hβ : 0 ≤ deriv f a := (by norm_num : (0 : ℝ) ≤ 1).trans (Nat.floor_pos.mp hm)
      have hνβ : (ν : ℝ) ≤ deriv f a := (by exact_mod_cast hn.2 : (ν : ℝ) ≤ (⌊deriv f a⌋₊ : ℝ)).trans (Nat.floor_le hβ)
      obtain ⟨x, hx, _⟩ := existsUnique_stationaryPoint hab hfc hanti ⟨by linarith, hνβ⟩
      exact ⟨x, fun _ => hx⟩
    · exact ⟨a, fun hn => (hν hn).elim⟩
  choose ξ hξ using hp
  exact ⟨ξ, hξ⟩

/-- A stationary point can coincide with the upper-derivative endpoint exactly at that endpoint frequency. -/
theorem stationary_point_endpoint_iff {f : ℝ → ℝ} {a b x ν : ℝ}
    (hab : a ≤ b) (hanti : StrictAntiOn (deriv f) (Set.Icc a b))
    (hx : x ∈ Set.Icc a b) (hν : deriv f x = ν) :
    (x = a ↔ ν = deriv f a) ∧ (x = b ↔ ν = deriv f b) := by
  constructor
  · constructor
    · intro he; simpa [he] using hν.symm
    · intro he
      exact hanti.injOn hx (Set.left_mem_Icc.mpr hab) (hν.trans he)
  · constructor
    · intro he; simpa [he] using hν.symm
    · intro he
      exact hanti.injOn hx (Set.right_mem_Icc.mpr hab) (hν.trans he)

/-- The source derivatives construct the full positive stationary family and consume it in the actual interior integral estimate. -/
theorem exists_stationary_interior_digamma {f : ℝ → ℝ} {a b D ℓ h₂ : ℝ}
    (hab : a < b) (hℓ : 0 < ℓ) (hαpos : 0 < deriv f b) (hα : deriv f b < 1)
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hanti : StrictAntiOn (deriv f) (Set.Icc a b))
    (hlower : ∀ u ∈ Set.Icc a b, ℓ ≤ |deriv (deriv f) u|)
    (hupper : ∀ u ∈ Set.Icc a b, |deriv (deriv f) u| ≤ h₂ * ℓ)
    (hD : ∀ u ∈ Set.Icc a b, |deriv (deriv (deriv f)) u| ≤ D) :
    ∃ ξ : ℕ → ℝ, (∀ ν ∈ Finset.Icc 1 ⌊deriv f a⌋₊,
      ξ ν ∈ Set.Icc a b ∧ deriv f (ξ ν) = (ν : ℝ)) ∧
    ‖(∑ ν ∈ Finset.Icc 1 (⌊deriv f a⌋₊ - 1), ∫ u in a..b,
        Complex.exp (2 * Real.pi * Complex.I * ((f u - (ν : ℝ) * u : ℝ) : ℂ))) -
      ∑ ν ∈ Finset.Icc 1 (⌊deriv f a⌋₊ - 1),
        Complex.exp (2 * Real.pi * Complex.I * ((f (ξ ν) - (ν : ℝ) * ξ ν - 1 / 8 : ℝ) : ℂ)) /
          (Real.sqrt |deriv (deriv f) (ξ ν)| : ℂ)‖ ≤
      (2 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * h₂ * D ^ (1 / 3 : ℝ) * (b - a) +
        1 / Real.pi * (
          (Complex.digamma ((deriv f a : ℝ) : ℂ)).re -
            (Complex.digamma ((deriv f a - (⌊deriv f a⌋₊ - 1 : ℕ) : ℝ) : ℂ)).re +
          (Complex.digamma (((⌊deriv f a⌋₊ - 1 : ℕ) + 1 - deriv f b : ℝ) : ℂ)).re -
            (Complex.digamma ((1 - deriv f b : ℝ) : ℂ)).re) := by
  have hcurv := stationary_curvature_of_antitone hab hf' hanti.antitoneOn hlower
  have hfc : ContinuousOn (deriv f) (Set.Icc a b) :=
    fun u hu => (hf' u hu).continuousAt.continuousWithinAt
  obtain ⟨ξ, hξ⟩ := exists_stationary_family hab.le hfc hanti hα
  refine ⟨ξ, hξ, ?_⟩
  apply stationary_interior_digamma_bound ξ hab hℓ hαpos hα (fun ν hν => hξ ν ?_) hf hf' hf'' hcurv hupper hD
  have hh := Finset.mem_Icc.mp hν
  exact Finset.mem_Icc.mpr ⟨hh.1, by omega⟩

/-- The source derivatives construct the full positive stationary family and consume it in the actual interior integral estimate. -/
theorem exists_stationary_interior_log {f : ℝ → ℝ} {a b D ℓ h₂ : ℝ}
    (hab : a < b) (hℓ : 0 < ℓ) (hαpos : 0 < deriv f b) (hα : deriv f b ≤ 1 / 2) (hβ : 1 ≤ deriv f a)
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hanti : StrictAntiOn (deriv f) (Set.Icc a b))
    (hlower : ∀ u ∈ Set.Icc a b, ℓ ≤ |deriv (deriv f) u|)
    (hupper : ∀ u ∈ Set.Icc a b, |deriv (deriv f) u| ≤ h₂ * ℓ)
    (hD : ∀ u ∈ Set.Icc a b, |deriv (deriv (deriv f)) u| ≤ D) :
    ∃ ξ : ℕ → ℝ, (∀ ν ∈ Finset.Icc 1 ⌊deriv f a⌋₊,
      ξ ν ∈ Set.Icc a b ∧ deriv f (ξ ν) = (ν : ℝ)) ∧
    ‖(∑ ν ∈ Finset.Icc 1 (⌊deriv f a⌋₊ - 1), ∫ u in a..b,
        Complex.exp (2 * Real.pi * Complex.I * ((f u - (ν : ℝ) * u : ℝ) : ℂ))) -
      ∑ ν ∈ Finset.Icc 1 (⌊deriv f a⌋₊ - 1),
        Complex.exp (2 * Real.pi * Complex.I * ((f (ξ ν) - (ν : ℝ) * ξ ν - 1 / 8 : ℝ) : ℂ)) /
          (Real.sqrt |deriv (deriv f) (ξ ν)| : ℂ)‖ ≤
      (2 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * h₂ * D ^ (1 / 3 : ℝ) * (b - a) +
        (2 / Real.pi * Real.log (deriv f a - deriv f b) + 1.251) := by
  have hcurv := stationary_curvature_of_antitone hab hf' hanti.antitoneOn hlower
  have hfc : ContinuousOn (deriv f) (Set.Icc a b) :=
    fun u hu => (hf' u hu).continuousAt.continuousWithinAt
  obtain ⟨ξ, hξ⟩ := exists_stationary_family hab.le hfc hanti (by linarith : deriv f b < 1)
  refine ⟨ξ, hξ, ?_⟩
  apply stationary_interior_log_bound ξ hab hℓ hαpos hα hβ (fun ν hν => hξ ν ?_) hf hf' hf'' hcurv hupper hD
  have hh := Finset.mem_Icc.mp hν
  exact Finset.mem_Icc.mpr ⟨hh.1, by omega⟩

end DhimanKadiriQuesadaHerrera2026
