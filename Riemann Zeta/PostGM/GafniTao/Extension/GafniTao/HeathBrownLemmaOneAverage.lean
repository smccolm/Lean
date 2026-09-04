import GafniTao.HeathBrownLemmaOnePreVMVT
import GafniTao.HeathBrownCenterWeyl

/-!
# The two Abel summations assembled

This file sums the first Abel inequality over the literal interior source
indices and connects all polynomial partial sums to the coefficient-torus
Weyl sums.  The local regularity hypotheses are displayed here; a later entry
bridge derives them from the global source interval.
-/

open Complex Finset Set
open scoped BigOperators ENNReal

namespace GafniTao

noncomputable section

noncomputable def heathBrownCenterNormSum
    (N k H Q : ℕ) (f : ℝ → ℝ) : ℝ :=
  ∑ n ∈ heathBrownInteriorIndices N H,
    ‖heathBrownWeylSum k Q (heathBrownCoefficientCenter k f n)‖

theorem heathBrown_source_shift_double_sum
    (N H : ℕ) (f : ℝ → ℝ) :
    ∑ h ∈ Finset.Icc 1 H, heathBrownSourceShiftSum N H f h =
      ∑ n ∈ heathBrownInteriorIndices N H,
        ∑ h ∈ Finset.Icc 1 H,
          heathBrownPhase (f ((n + h : ℕ) : ℝ)) := by
  unfold heathBrownSourceShiftSum heathBrownInteriorIndices
  rw [Finset.sum_comm]

/-- The first Abel summation after summing over all interior source indices. -/
theorem norm_heathBrown_source_shift_double_sum_le
    {N k H : ℕ} (hk : 2 ≤ k) (hH : 1 ≤ H) {f : ℝ → ℝ}
    {A lambda : ℝ}
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
    ‖∑ h ∈ Finset.Icc 1 H, heathBrownSourceShiftSum N H f h‖ ≤
      heathBrownCenterNormSum N k H H f +
        (2 * Real.pi * (A * lambda * (H : ℝ) ^ (k - 1))) *
          ∑ j ∈ Finset.Ico 1 H, heathBrownCenterNormSum N k H j f := by
  rw [heathBrown_source_shift_double_sum]
  calc
    _ ≤ ∑ n ∈ heathBrownInteriorIndices N H,
        ‖∑ h ∈ Finset.Icc 1 H,
          heathBrownPhase (f ((n + h : ℕ) : ℝ))‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ heathBrownInteriorIndices N H,
        (‖heathBrownTaylorPolynomialSum k H f n‖ +
          (2 * Real.pi * (A * lambda * (H : ℝ) ^ (k - 1))) *
            ∑ j ∈ Finset.Ico 1 H,
              ‖heathBrownTaylorPolynomialSum k j f n‖) := by
      apply Finset.sum_le_sum
      intro n hn
      simpa only [Nat.cast_add] using
        (heathBrown_shifted_source_sum_norm_le_partial hk hH
          (hlocal n hn).1 (hlocal n hn).2.1 (hlocal n hn).2.2.1
          (hlocal n hn).2.2.2)
    _ = heathBrownCenterNormSum N k H H f +
        (2 * Real.pi * (A * lambda * (H : ℝ) ^ (k - 1))) *
          ∑ j ∈ Finset.Ico 1 H, heathBrownCenterNormSum N k H j f := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      unfold heathBrownCenterNormSum
      simp_rw [norm_heathBrownWeylSum_center_eq_TaylorPolynomialSum
        (show 1 ≤ k by omega)]
      rw [Finset.sum_comm]

/-- Both Abel steps and coefficient-cell averaging, still before inserting
the VMVT and pair-count estimates. -/
theorem heathBrown_source_shift_double_sum_preVMVT
    {N k H s : ℕ} (hk : 2 ≤ k) (hH : 2 ≤ H) {f : ℝ → ℝ}
    {A lambda : ℝ} (hAlambda : 0 ≤ A * lambda)
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
    ENNReal.ofReal
        ((2 : ℝ) ^ (k - 1) *
          (((H : ℝ) ^ heathBrownCriticalMoment k)⁻¹)) *
        ENNReal.ofReal
          ‖∑ h ∈ Finset.Icc 1 H, heathBrownSourceShiftSum N H f h‖ ≤
      (1 + ENNReal.ofReal
          (2 * Real.pi * (A * lambda * (H : ℝ) ^ (k - 1))) * H) *
        (1 + ENNReal.ofReal
          (2 * Real.pi * ((k : ℝ) ^ 2 / H)) * H) *
        heathBrownIntegratedMajorant N k H s f := by
  let V : ENNReal := ENNReal.ofReal
    ((2 : ℝ) ^ (k - 1) *
      (((H : ℝ) ^ heathBrownCriticalMoment k)⁻¹))
  let c₁ : ℝ := 2 * Real.pi * (A * lambda * (H : ℝ) ^ (k - 1))
  let B : ENNReal := heathBrownIntegratedMajorant N k H s f
  have hc₁ : 0 ≤ c₁ := by dsimp only [c₁]; positivity
  have hsource := ENNReal.ofReal_le_ofReal
    (norm_heathBrown_source_shift_double_sum_le
      (N := N) (k := k) (H := H) hk (by omega) hlocal)
  have hcenterNonneg (Q : ℕ) : 0 ≤ heathBrownCenterNormSum N k H Q f := by
    unfold heathBrownCenterNormSum
    exact Finset.sum_nonneg fun n hn => norm_nonneg _
  rw [ENNReal.ofReal_add (hcenterNonneg H)
    (mul_nonneg hc₁ (Finset.sum_nonneg fun j hj => hcenterNonneg j))] at hsource
  rw [ENNReal.ofReal_mul hc₁] at hsource
  have hcenterOfReal (Q : ℕ) :
      ENNReal.ofReal (heathBrownCenterNormSum N k H Q f) =
        ∑ n ∈ heathBrownInteriorIndices N H,
          ENNReal.ofReal ‖heathBrownWeylSum k Q
            (heathBrownCoefficientCenter k f n)‖ := by
    unfold heathBrownCenterNormSum
    exact ENNReal.ofReal_sum_of_nonneg fun n hn => norm_nonneg _
  have houterOfReal :
      ENNReal.ofReal
          (∑ j ∈ Finset.Ico 1 H, heathBrownCenterNormSum N k H j f) =
        ∑ j ∈ Finset.Ico 1 H,
          ENNReal.ofReal (heathBrownCenterNormSum N k H j f) :=
    ENNReal.ofReal_sum_of_nonneg fun j hj => hcenterNonneg j
  rw [hcenterOfReal H, houterOfReal] at hsource
  simp_rw [hcenterOfReal] at hsource
  have hHcenter := heathBrown_centerWeyl_sum_preVMVT
    (N := N) (k := k) (H := H) (Q := H) (s := s)
    hH (by omega) le_rfl hs f
  have hjcenter (j : ℕ) (hj : j ∈ Finset.Ico 1 H) :=
    heathBrown_centerWeyl_sum_preVMVT
      (N := N) (k := k) (H := H) (Q := j) (s := s)
      hH (Finset.mem_Ico.mp hj).1
      (Finset.mem_Ico.mp hj).2.le hs f
  have hsumCenter :
      V * (∑ j ∈ Finset.Ico 1 H,
        ∑ n ∈ heathBrownInteriorIndices N H,
          ENNReal.ofReal ‖heathBrownWeylSum k j
            (heathBrownCoefficientCenter k f n)‖) ≤
        H * ((1 + ENNReal.ofReal
          (2 * Real.pi * ((k : ℝ) ^ 2 / H)) * H) * B) := by
    rw [Finset.mul_sum]
    calc
      _ ≤ ∑ _j ∈ Finset.Ico 1 H,
          ((1 + ENNReal.ofReal
            (2 * Real.pi * ((k : ℝ) ^ 2 / H)) * H) * B) := by
        apply Finset.sum_le_sum
        intro j hj
        exact (hjcenter j hj).trans (by
          gcongr
          exact_mod_cast (Finset.mem_Ico.mp hj).2.le)
      _ = (Finset.Ico 1 H).card *
          ((1 + ENNReal.ofReal
            (2 * Real.pi * ((k : ℝ) ^ 2 / H)) * H) * B) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ H * ((1 + ENNReal.ofReal
            (2 * Real.pi * ((k : ℝ) ^ 2 / H)) * H) * B) := by
        gcongr
        exact_mod_cast card_Ico_one_le H
  calc
    V * ENNReal.ofReal
        ‖∑ h ∈ Finset.Icc 1 H,
          heathBrownSourceShiftSum N H f h‖ ≤
      V * ((∑ n ∈ heathBrownInteriorIndices N H,
          ENNReal.ofReal ‖heathBrownWeylSum k H
            (heathBrownCoefficientCenter k f n)‖) +
        ENNReal.ofReal c₁ *
          ∑ j ∈ Finset.Ico 1 H,
            ∑ n ∈ heathBrownInteriorIndices N H,
              ENNReal.ofReal ‖heathBrownWeylSum k j
                (heathBrownCoefficientCenter k f n)‖) := by
        gcongr
    _ = V * (∑ n ∈ heathBrownInteriorIndices N H,
          ENNReal.ofReal ‖heathBrownWeylSum k H
            (heathBrownCoefficientCenter k f n)‖) +
        ENNReal.ofReal c₁ *
          (V * ∑ j ∈ Finset.Ico 1 H,
            ∑ n ∈ heathBrownInteriorIndices N H,
              ENNReal.ofReal ‖heathBrownWeylSum k j
                (heathBrownCoefficientCenter k f n)‖) := by ring
    _ ≤ ((1 + ENNReal.ofReal
          (2 * Real.pi * ((k : ℝ) ^ 2 / H)) * H) * B) +
        ENNReal.ofReal c₁ *
          (H * ((1 + ENNReal.ofReal
            (2 * Real.pi * ((k : ℝ) ^ 2 / H)) * H) * B)) := by
        gcongr
    _ = (1 + ENNReal.ofReal c₁ * H) *
        (1 + ENNReal.ofReal
          (2 * Real.pi * ((k : ℝ) ^ 2 / H)) * H) * B := by ring
    _ = _ := by rfl

#print axioms heathBrown_source_shift_double_sum
#print axioms norm_heathBrown_source_shift_double_sum_le
#print axioms heathBrown_source_shift_double_sum_preVMVT

end

end GafniTao
