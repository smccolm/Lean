import GafniTao.HeathBrownLemmaOneAverage

/-!
# Heath-Brown Lemma 1: exact finite pre-VMVT statement

The common-range truncation error `H^2` is now combined with both Abel
summations.  This is the final finite analytic inequality before inserting
the Vinogradov mean-value and derivative-pair-count estimates.
-/

open Complex Finset Set
open scoped BigOperators ENNReal

namespace GafniTao

noncomputable section

theorem heathBrown_H_mul_exponentialSum_norm_le
    {N H : ℕ} (hHN : H ≤ N) (f : ℝ → ℝ) :
    (H : ℝ) * ‖heathBrownExponentialSum N f‖ ≤
      ‖∑ h ∈ Finset.Icc 1 H, heathBrownSourceShiftSum N H f h‖ +
        (H : ℝ) ^ 2 := by
  have herror := norm_heathBrown_source_average_sub_le hHN f
  have htri := norm_le_norm_add_norm_sub
    (∑ h ∈ Finset.Icc 1 H, heathBrownSourceShiftSum N H f h)
    ((H : ℂ) * heathBrownExponentialSum N f)
  rw [norm_mul, norm_natCast] at htri
  rw [norm_sub_rev] at htri
  exact htri.trans (add_le_add le_rfl herror)

/-- Source-faithful finite form of Heath-Brown Lemma 1 prior to the two
number-theoretic inputs.  Every factor is literal and all endpoint loss is
the exact `H^2` obtained from the common source interval. -/
theorem heathBrown_lemma_one_finite_preVMVT
    {N k H s : ℕ} (hk : 2 ≤ k) (hH : 2 ≤ H) (hHN : H ≤ N)
    {f : ℝ → ℝ} {A lambda : ℝ} (hAlambda : 0 ≤ A * lambda)
    (hs : 1 ≤ s)
    (hlocal : ∀ n ∈ heathBrownInteriorIndices N H,
      ContDiffAt ℝ (k - 2 : ℕ) (deriv f) n ∧
      (∀ x ∈ Set.Icc (1 : ℝ) H,
        HasDerivAt f (deriv f ((n : ℝ) + x)) ((n : ℝ) + x)) ∧
      (∀ x ∈ Set.Icc (1 : ℝ) H,
        ContDiffOn ℝ (k - 1 : ℕ) (deriv f)
          (Set.Icc (n : ℝ) ((n : ℝ) + x))) ∧
      (∀ x ∈ Set.Icc (1 : ℝ) H,
        ∀ ξ ∈ Set.Ioo (n : ℝ) ((n : ℝ) + x),
        ‖iteratedDeriv k f ξ‖ ≤ A * lambda)) :
    let V : ENNReal := ENNReal.ofReal
      ((2 : ℝ) ^ (k - 1) *
        (((H : ℝ) ^ heathBrownCriticalMoment k)⁻¹))
    V * H * ENNReal.ofReal ‖heathBrownExponentialSum N f‖ ≤
      (1 + ENNReal.ofReal
          (2 * Real.pi * (A * lambda * (H : ℝ) ^ (k - 1))) * H) *
        (1 + ENNReal.ofReal
          (2 * Real.pi * ((k : ℝ) ^ 2 / H)) * H) *
        heathBrownIntegratedMajorant N k H s f +
      V * ENNReal.ofReal ((H : ℝ) ^ 2) := by
  dsimp only
  let V : ENNReal := ENNReal.ofReal
    ((2 : ℝ) ^ (k - 1) *
      (((H : ℝ) ^ heathBrownCriticalMoment k)⁻¹))
  have hbase := heathBrown_H_mul_exponentialSum_norm_le hHN f
  have hbaseE := ENNReal.ofReal_le_ofReal hbase
  rw [ENNReal.ofReal_add (norm_nonneg _) (sq_nonneg _)] at hbaseE
  rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ H)] at hbaseE
  have havg := heathBrown_source_shift_double_sum_preVMVT
    (N := N) (k := k) (H := H) (s := s) hk hH hAlambda hs hlocal
  calc
    V * H * ENNReal.ofReal ‖heathBrownExponentialSum N f‖ =
        V * (ENNReal.ofReal (H : ℝ) *
          ENNReal.ofReal ‖heathBrownExponentialSum N f‖) := by
      norm_num
      ring
    _ ≤ V * (ENNReal.ofReal
          ‖∑ h ∈ Finset.Icc 1 H, heathBrownSourceShiftSum N H f h‖ +
        ENNReal.ofReal ((H : ℝ) ^ 2)) := by gcongr
    _ = V * ENNReal.ofReal
          ‖∑ h ∈ Finset.Icc 1 H, heathBrownSourceShiftSum N H f h‖ +
        V * ENNReal.ofReal ((H : ℝ) ^ 2) := by ring
    _ ≤ (1 + ENNReal.ofReal
          (2 * Real.pi * (A * lambda * (H : ℝ) ^ (k - 1))) * H) *
        (1 + ENNReal.ofReal
          (2 * Real.pi * ((k : ℝ) ^ 2 / H)) * H) *
        heathBrownIntegratedMajorant N k H s f +
      V * ENNReal.ofReal ((H : ℝ) ^ 2) := by gcongr

#print axioms heathBrown_H_mul_exponentialSum_norm_le
#print axioms heathBrown_lemma_one_finite_preVMVT

end

end GafniTao
