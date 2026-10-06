import DhimanKadiriQuesadaHerrera2026.ChiReflection
import DhimanKadiriQuesadaHerrera2026.ZetaTruncation
import DhimanKadiriQuesadaHerrera2026.AFEFirstRealCutoff

namespace DhimanKadiriQuesadaHerrera2026

/-- The actual sharp positive-integer polynomial is the source integer interval sum, including the unit term. -/
theorem sharpZetaSum_eq_integer_source {x : ℝ} (hx : 0 ≤ x) (s : ℂ) :
    sharpZetaSum s x = ∑ n ∈ Finset.Ioc (0 : ℤ) ⌊x⌋, (n : ℂ) ^ (-s) := by
  have h := sum_int_Ioc_eq_nat_Ioc (fun u : ℝ => (u : ℂ) ^ (-s)) 0 ⌊x⌋₊
  simp only [Nat.cast_zero, Int.natCast_floor_eq_floor hx, Complex.ofReal_intCast,
    Complex.ofReal_natCast] at h
  rw [h]
  unfold sharpZetaSum zetaTerm
  congr 1

/-- The literal two-polynomial remainder agrees with the original integer-indexed source expression. -/
theorem afeRemainder_eq_integer_source {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (σ t : ℝ) :
    afeRemainder ((σ : ℂ) + (t : ℂ) * Complex.I) x y =
      riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) -
        (∑ n ∈ Finset.Ioc (0 : ℤ) ⌊x⌋, (n : ℂ) ^ (-(σ : ℂ) - (t : ℂ) * Complex.I)) -
        chi ((σ : ℂ) + (t : ℂ) * Complex.I) *
          (∑ m ∈ Finset.Ioc (0 : ℤ) ⌊y⌋, (m : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I - 1)) := by
  unfold afeRemainder
  rw [sharpZetaSum_eq_integer_source hx, sharpZetaSum_eq_integer_source hy]
  have h₁ : -((σ : ℂ) + (t : ℂ) * Complex.I) = -(σ : ℂ) - (t : ℂ) * Complex.I := by ring
  have h₂ : -(1 - ((σ : ℂ) + (t : ℂ) * Complex.I)) = (σ : ℂ) + (t : ℂ) * Complex.I - 1 := by ring
  rw [h₁, h₂]

/-- The physical logarithmic wave is exactly the conjugate principal-power Dirichlet summand. -/
theorem actual_wave_principal_power {u : ℝ} (hu : 0 < u) (σ t : ℝ) :
    starRingEnd ℂ ((u ^ (-σ) : ℝ) * Complex.exp
      (2 * Real.pi * Complex.I * ((t / (2 * Real.pi) * Real.log u : ℝ) : ℂ))) =
        (u : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I)) := by
  have h := conj_weightedWave_afe σ t hu
  simpa only [weightedWave, afePhase, afeWeight, neg_add_rev, add_comm] using h

/-- The source lower and upper sample endpoints are exactly open and closed, including negative samples. -/
theorem integer_sample_endpoints (a b : ℝ) (n : ℤ) :
    n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋ ↔ a < (n : ℝ) ∧ (n : ℝ) ≤ b := by
  exact mem_source_sample_interval a b n

/-- Replacing a nonnegative real cutoff by its half-integer representative preserves the actual integer sum. -/
theorem integer_source_half_cutoff {x : ℝ} (hx : 0 ≤ x) (s : ℂ) :
    (∑ n ∈ Finset.Ioc (0 : ℤ) ⌊afeHalfCutoff x⌋, (n : ℂ) ^ (-s)) =
      ∑ n ∈ Finset.Ioc (0 : ℤ) ⌊x⌋, (n : ℂ) ^ (-s) := by
  have hhalf : 0 ≤ afeHalfCutoff x := by unfold afeHalfCutoff; positivity
  rw [← sharpZetaSum_eq_integer_source hhalf, ← sharpZetaSum_eq_integer_source hx]
  exact sharpZetaSum_afeHalfCutoff s x

end DhimanKadiriQuesadaHerrera2026
