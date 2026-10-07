import Dubon2026.SatoTateCharacters
import Dubon2026.CompactPolynomialConvergence

/-! # The polynomial character criterion for the actual Sato--Tate coefficient law

This proves the analytic convergence bridge. The prime character averages and
the arithmetic coefficient bound still require their genuine arithmetic proofs.
-/

namespace Dubon2026

open Polynomial Set MeasureTheory Filter
open scoped Topology

noncomputable section

/-- Every real polynomial is a finite linear combination of the genuine symmetric-power character polynomials. -/
theorem polynomial_mem_span_satoTate_characters (p : Polynomial ℝ) :
    p ∈ Submodule.span ℝ (Set.range (fun n : ℕ => Chebyshev.S ℝ (n : ℤ))) := by
  let S := Submodule.span ℝ (Set.range (fun n : ℕ => Chebyshev.S ℝ (n : ℤ)))
  have hgen (n : ℕ) : Chebyshev.S ℝ (n : ℤ) ∈ S := Submodule.subset_span ⟨n, rfl⟩
  have hX : ∀ q ∈ S, X * q ∈ S := by
    intro q hq
    induction hq using Submodule.span_induction with
    | mem q hq =>
      obtain ⟨n, rfl⟩ := hq
      cases n with
      | zero => simpa only [Nat.cast_zero, Chebyshev.S_zero, mul_one,
          Nat.cast_one, Chebyshev.S_one] using hgen 1
      | succ n =>
        have he : X * Chebyshev.S ℝ ((n : ℤ) + 1) =
            Chebyshev.S ℝ ((n : ℤ) + 2) + Chebyshev.S ℝ (n : ℤ) := by
          rw [Chebyshev.S_add_two]
          ring
        simp only [Nat.cast_succ]
        rw [he]
        exact S.add_mem (by simpa only [Nat.cast_add, Nat.cast_ofNat] using hgen (n + 2)) (hgen n)
    | zero => simpa only [mul_zero] using S.zero_mem
    | add q r _ _ hq hr => simpa only [mul_add] using S.add_mem hq hr
    | smul c q _ hq => simpa only [mul_smul_comm] using S.smul_mem c hq
  have hpow (n : ℕ) : (X : Polynomial ℝ) ^ n ∈ S := by
    induction n with
    | zero => simpa only [pow_zero, Nat.cast_zero, Chebyshev.S_zero] using hgen 0
    | succ n ih => simpa only [pow_succ'] using hX _ ih
  change p ∈ S
  induction p using Polynomial.induction_on' with
  | add p q hp hq => exact S.add_mem hp hq
  | monomial n a =>
    simpa only [Polynomial.smul_eq_C_mul, C_mul_X_pow_eq_monomial] using S.smul_mem a (hpow n)

/-- The actual coefficient law is supported on the closed Ramanujan interval. -/
theorem satoTateProbability_ae_mem :
    ∀ᵐ x ∂(satoTateProbability : Measure ℝ), x ∈ Icc (-2) 2 := by
  change ∀ᵐ x ∂Measure.map (fun θ : ℝ => 2 * Real.cos θ) satoTateAngleMeasure,
    x ∈ Icc (-2) 2
  apply (ae_map_iff (p := fun x : ℝ => x ∈ Icc (-2) 2)
    (show Measurable (fun θ : ℝ => 2 * Real.cos θ) by fun_prop).aemeasurable
    measurableSet_Icc).mpr
  apply ae_of_all
  intro θ
  exact ⟨by linarith [Real.neg_one_le_cos θ], by linarith [Real.cos_le_one θ]⟩

/-- The exact character averages imply weak convergence to the actual Sato--Tate measure for probabilities on any fixed interval containing its support. -/
theorem satoTate_tendsto_of_character_integrals {μs : ℕ → ProbabilityMeasure ℝ}
    {a b : ℝ} (ha : a ≤ -2) (hb : 2 ≤ b)
    (hs : ∀ N, ∀ᵐ x ∂(μs N : Measure ℝ), x ∈ Icc a b)
    (hchar : ∀ n : ℕ,
      Tendsto (fun N => ∫ x, (Chebyshev.S ℝ (n : ℤ)).eval x ∂(μs N : Measure ℝ))
        atTop (𝓝 (if n = 0 then 1 else 0))) :
    Tendsto μs atTop (𝓝 satoTateProbability) := by
  have hμ : ∀ᵐ x ∂(satoTateProbability : Measure ℝ), x ∈ Icc a b := by
    filter_upwards [satoTateProbability_ae_mem] with x hx
    exact ⟨ha.trans hx.1, hx.2.trans hb⟩
  apply probability_tendsto_of_polynomial_integrals hs hμ
  intro p
  have hp := polynomial_mem_span_satoTate_characters p
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨n, rfl⟩ := hp
    rw [integral_satoTate_character]
    exact hchar n
  | zero => simpa only [eval_zero, integral_zero] using (tendsto_const_nhds (x := (0 : ℝ)))
  | add p q _ _ hp hq =>
    have he (ν : ProbabilityMeasure ℝ) (hν : ∀ᵐ x ∂(ν : Measure ℝ), x ∈ Icc a b) :
        (∫ x, (p + q).eval x ∂(ν : Measure ℝ)) =
          (∫ x, p.eval x ∂(ν : Measure ℝ)) + ∫ x, q.eval x ∂(ν : Measure ℝ) := by
      simp only [eval_add]
      exact integral_add (continuous_integrable_of_ae_mem_Icc hν p.continuous)
        (continuous_integrable_of_ae_mem_Icc hν q.continuous)
    simpa only [he _ hμ, he _ (hs _)] using hp.add hq
  | smul c p _ hp =>
    simpa only [eval_smul, smul_eq_mul, integral_const_mul] using hp.const_mul c

end
end Dubon2026
