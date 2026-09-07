import PrimeShell.ShiftGrid

namespace PrimeShell

noncomputable section

open scoped BigOperators

/-- Every endpoint in a uniform shift grid lies in the published GM
fixed-length range as soon as the two extreme endpoints do. -/
theorem shiftGridLengths_in_gm_range
    {eps : ℝ} {N L W q : ℕ}
    (hLower : (N : ℝ) ^ (2 / 15 + eps) ≤ (L : ℝ))
    (hUpper : ((L + q * W : ℕ) : ℝ) ≤
      (N : ℝ) ^ (99 / 100 : ℝ)) :
    ∀ H ∈ shiftGridLengths L W q,
      (N : ℝ) ^ (2 / 15 + eps) ≤ (H : ℝ) ∧
      (H : ℝ) ≤ (N : ℝ) ^ (99 / 100 : ℝ) := by
  intro H hH
  have hBounds := shiftGridLengths_mem_bounds hH
  have hLH : (L : ℝ) ≤ (H : ℝ) := by exact_mod_cast hBounds.1
  have hHFinal : (H : ℝ) ≤ ((L + q * W : ℕ) : ℝ) := by
    exact_mod_cast hBounds.2
  constructor
  · exact hLower.trans hLH
  · exact hHFinal.trans hUpper

/-- The explicit grid error ledger after replacing the literal simultaneous
exceptional-set cardinality by the finite-union consequence of GM
Corollary 1.4.  The remaining summands are the already proved arithmetic,
normalization, kernel-variation, and right-boundary losses. -/
def gmDyadicShiftGridErrorBudget
    (Phi : ℝ → ℝ) (T C : ℝ) (N L W q : ℕ) : ℝ :=
  ∑ i ∈ Finset.range q,
    ((∑ n ∈ goodInteriorRows C N (shiftGridRight L W i)
          (shiftGridLengths L W q),
        goodRowShiftBlockErrorBudget Phi T C N N n
          (shiftGridLeft L W i) (shiftGridRight L W i)) +
      (((2 * q : ℕ) : ℝ) * (C * N * gmDecay N) +
          (shiftGridRight L W i : ℕ)) *
        (((shiftGridRight L W i - shiftGridLeft L W i : ℕ) : ℝ) *
          dyadicAcoefMajorant N ^ 2 *
          (2 * T * ∫ x, Phi x ^ 2)))

/-- The published fixed-length GM interface controls the literal uniform-grid
trace, including the cost of making all endpoint exceptional sets
simultaneous.  This is a genuine consumer of `GMCorollary14LambdaFinite`;
it is intentionally still conditional until that arithmetic theorem is
formalized natively. -/
theorem gm_corollary14_controls_dyadicShiftGrid
    (hGM : GMCorollary14LambdaFinite)
    {eps : ℝ} (heps : 0 < eps) :
    ∃ X0 : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ (Phi : ℝ → ℝ) (T : ℝ) (N L W q : ℕ),
        X0 ≤ N → 2 ≤ N →
        (N : ℝ) ^ (2 / 15 + eps) ≤ (L : ℝ) →
        ((L + q * W : ℕ) : ℝ) ≤ (N : ℝ) ^ (99 / 100 : ℝ) →
        L + q * W ≤ N → 0 ≤ T →
        Continuous Phi →
        MeasureTheory.Integrable (fun x => Phi x ^ 2) →
        MeasureTheory.Integrable (fun x => Phi x ^ 2 * |x|) →
        |(∑ h ∈ Finset.Ioc L (L + q * W),
            ∑ n ∈ Finset.Ioc N (2 * N),
              if n + h ∈ Finset.Ioc N (2 * N) then
                dyadicLambdaWeight n h * dyadicShiftKernel Phi T n h
              else 0) -
          goodDyadicShiftGridMain Phi T C N L W q| ≤
            gmDyadicShiftGridErrorBudget Phi T C N L W q := by
  obtain ⟨X0, C, hC, hUnion⟩ :=
    card_gmSimultaneousLambdaBadSet_le_of_corollary14 hGM heps
  refine ⟨X0, C, hC, ?_⟩
  intro Phi T N L W q hX hNtwo hLower hUpper hFinal hT hPhi hPhi2 hPhiAbs
  have hN : 1 ≤ N := by omega
  have hRanges := shiftGridLengths_in_gm_range hLower hUpper
  have hCardBase := hUnion N (shiftGridLengths L W q) hX hNtwo hRanges
  have hFactor : 0 ≤ C * (N : ℝ) * gmDecay N := by
    have hDecay : 0 < gmDecay N := Real.exp_pos _
    positivity
  have hCard :
      ((gmSimultaneousLambdaBadSet C N
          (shiftGridLengths L W q)).card : ℝ) ≤
        ((2 * q : ℕ) : ℝ) * (C * N * gmDecay N) := by
    calc
      ((gmSimultaneousLambdaBadSet C N
          (shiftGridLengths L W q)).card : ℝ) ≤
          ((shiftGridLengths L W q).card : ℝ) *
            (C * N * gmDecay N) := hCardBase
      _ ≤ ((2 * q : ℕ) : ℝ) * (C * N * gmDecay N) := by
        apply mul_le_mul_of_nonneg_right _ hFactor
        exact_mod_cast card_shiftGridLengths_le L W q
  refine (abs_dyadicShiftGridSum_sub_goodMain_le hT hC.le hN hFinal
    hPhi hPhi2 hPhiAbs).trans ?_
  unfold dyadicShiftGridErrorBudget gmDyadicShiftGridErrorBudget
  apply Finset.sum_le_sum
  intro i hi
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_right
  · have hCard' := add_le_add_right hCard (shiftGridRight L W i : ℝ)
    simpa only [Nat.cast_add, Nat.cast_ofNat, add_comm] using hCard'
  · positivity

end

end PrimeShell
