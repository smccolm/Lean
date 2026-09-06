import GafniTao.Pintz2023HalaszAbel

/-!
# Pintz (2023), equation (4.23)

This is the small-block estimate with the literal kernel from (4.18).  The
factor `L/N` is obtained from the proved monotonicity and (4.22); the two
terms in parentheses are exactly those left by Corollary 2.
-/

namespace GafniTao

noncomputable section

/-- The Corollary-2 majorant in the source range, rewritten in the exact
shape displayed in (4.23). -/
theorem pintz2023CorollaryTwoMajorant_le_equation423
    {r L : ℕ} {epsilon xi t : ℝ}
    (hr : 3 ≤ r) (hL : 0 < L) (ht : 0 < t)
    (hxi : xi ≤ pintz2023HBAlpha r - 6 * epsilon) :
    pintz2023CorollaryTwoMajorant r L epsilon xi t ≤
      (L : ℝ) ^ (-3 * epsilon) *
        (1 + t ^ pintz2023HBAlpha r / (L : ℝ) ^ (1 / (r : ℝ))) := by
  have hrReal : (3 : ℝ) ≤ r := by exact_mod_cast hr
  have hrPos : (0 : ℝ) < r := by linarith
  have hrSubPos : (0 : ℝ) < (r : ℝ) - 1 := by linarith
  have hLReal : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hExp :
      xi - 1 / ((r : ℝ) - 1) + 3 * epsilon ≤
        -3 * epsilon - 1 / (r : ℝ) := by
    unfold pintz2023HBAlpha at hxi
    have hIdentity :
        1 / ((r : ℝ) * ((r : ℝ) - 1)) -
            1 / ((r : ℝ) - 1) = -1 / (r : ℝ) := by
      field_simp
      ring
    calc
      xi - 1 / ((r : ℝ) - 1) + 3 * epsilon ≤
          (1 / ((r : ℝ) * ((r : ℝ) - 1)) - 6 * epsilon) -
            1 / ((r : ℝ) - 1) + 3 * epsilon := by linarith
      _ = (1 / ((r : ℝ) * ((r : ℝ) - 1)) -
            1 / ((r : ℝ) - 1)) - 3 * epsilon := by ring
      _ = -3 * epsilon - 1 / (r : ℝ) := by rw [hIdentity]; ring
  have hPow := Real.rpow_le_rpow_of_exponent_le hLReal hExp
  have hLPos : (0 : ℝ) < L := by exact_mod_cast hL
  have hFactor :
      (L : ℝ) ^ (-3 * epsilon - 1 / (r : ℝ)) =
        (L : ℝ) ^ (-3 * epsilon) /
          (L : ℝ) ^ (1 / (r : ℝ)) := by
    rw [sub_eq_add_neg, Real.rpow_add hLPos,
      Real.rpow_neg hLPos.le]
    exact (div_eq_mul_inv _ _).symm
  have hTPow : 0 ≤ t ^ pintz2023HBAlpha r := Real.rpow_nonneg ht.le _
  unfold pintz2023CorollaryTwoMajorant
  calc
    (L : ℝ) ^ (xi - 1 / ((r : ℝ) - 1) + 3 * epsilon) *
          t ^ pintz2023HBAlpha r + (L : ℝ) ^ (-3 * epsilon) ≤
        (L : ℝ) ^ (-3 * epsilon - 1 / (r : ℝ)) *
          t ^ pintz2023HBAlpha r + (L : ℝ) ^ (-3 * epsilon) := by
      gcongr
    _ = (L : ℝ) ^ (-3 * epsilon) *
        (1 + t ^ pintz2023HBAlpha r / (L : ℝ) ^ (1 / (r : ℝ))) := by
      rw [hFactor]
      field_simp
      ring

/-- Pintz (4.23), on a literal half-open dyadic block `(L,R]` below the
ambient smoothing scale `N`.  The implied scale constant in Corollary 2 is
kept explicit as `B`. -/
theorem pintz2023_equation423_native
    (r : ℕ) (epsilon B : ℝ) (hr : 3 ≤ r)
    (hepsilon : 0 < epsilon) (hB : 0 < B) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N L R : ℕ) (xi t : ℝ),
        0 < N → 0 < L → L < R → R ≤ 2 * L → R ≤ N →
        0 < t →
        xi ≤ pintz2023HBAlpha r - 6 * epsilon →
        (L : ℝ) ≤ B * t ^ (2 / (r : ℝ)) →
        ‖pintz2023HalaszKernelWeightedBlock N xi L R t‖ ≤
          C * ((L : ℝ) / N) * (L : ℝ) ^ (-3 * epsilon) *
            (1 + t ^ pintz2023HBAlpha r /
              (L : ℝ) ^ (1 / (r : ℝ))) := by
  obtain ⟨C₀, hC₀, hCor⟩ :=
    pintz2023_corollary_two_native r epsilon B hr hepsilon hB
  refine ⟨2 * C₀, mul_pos (by norm_num) hC₀, ?_⟩
  intro N L R xi t hN hL hLR hR hRN ht hxi hscale
  have hPartial : ∀ j, j ≤ R - L →
      ‖pintz2023WeightedBlock xi L (L + j) t‖ ≤
        C₀ * pintz2023CorollaryTwoMajorant r L epsilon xi t := by
    intro j hj
    by_cases hj0 : j = 0
    · subst j
      simp [pintz2023WeightedBlock]
      unfold pintz2023CorollaryTwoMajorant
      positivity
    · exact hCor xi L (L + j) t hxi hL (by omega)
        (by omega) ht hscale
  have hKernel :=
    norm_pintz2023HalaszKernelWeightedBlock_le_div_of_prefix
      hN hL hLR hRN hPartial
  have hMajorant := pintz2023CorollaryTwoMajorant_le_equation423
    hr hL ht hxi
  have hRDiv : (R : ℝ) / N ≤ 2 * ((L : ℝ) / N) := by
    have hNReal : (0 : ℝ) < N := by exact_mod_cast hN
    have hRReal : (R : ℝ) ≤ 2 * (L : ℝ) := by exact_mod_cast hR
    calc
      (R : ℝ) / N ≤ (2 * (L : ℝ)) / N :=
        div_le_div_of_nonneg_right hRReal hNReal.le
      _ = 2 * ((L : ℝ) / N) := by ring
  have hShapeNonneg : 0 ≤
      (L : ℝ) ^ (-3 * epsilon) *
        (1 + t ^ pintz2023HBAlpha r / (L : ℝ) ^ (1 / (r : ℝ))) := by
    positivity
  calc
    ‖pintz2023HalaszKernelWeightedBlock N xi L R t‖ ≤
        ((R : ℝ) / N) *
          (C₀ * pintz2023CorollaryTwoMajorant r L epsilon xi t) := hKernel
    _ ≤ ((R : ℝ) / N) *
          (C₀ * ((L : ℝ) ^ (-3 * epsilon) *
            (1 + t ^ pintz2023HBAlpha r /
              (L : ℝ) ^ (1 / (r : ℝ))))) := by
      gcongr
    _ ≤ 2 * ((L : ℝ) / N) *
          (C₀ * ((L : ℝ) ^ (-3 * epsilon) *
            (1 + t ^ pintz2023HBAlpha r /
              (L : ℝ) ^ (1 / (r : ℝ))))) := by
      exact mul_le_mul_of_nonneg_right hRDiv (mul_nonneg hC₀.le hShapeNonneg)
    _ = (2 * C₀) * ((L : ℝ) / N) * (L : ℝ) ^ (-3 * epsilon) *
          (1 + t ^ pintz2023HBAlpha r /
            (L : ℝ) ^ (1 / (r : ℝ))) := by ring

/-- The pre-simplification form of (4.23).  Retaining the exact Corollary-2
majorant is essential when the low shells are transported to `A_h`: its
first monomial contains the `xi` power which is subsequently cancelled by
the critical-scale inequality. -/
theorem pintz2023_equation423_shift_four_eta_raw_native
    (r : ℕ) (epsilon B : ℝ) (hr : 3 ≤ r)
    (hepsilon : 0 < epsilon) (hB : 0 < B) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N L R : ℕ) (xi eta t : ℝ),
        0 < N → 0 < L → L < R → R ≤ 2 * L → R ≤ N →
        0 ≤ eta → 0 < t →
        xi ≤ pintz2023HBAlpha r - 6 * epsilon →
        (L : ℝ) ≤ B * t ^ (2 / (r : ℝ)) →
        ‖pintz2023HalaszKernelWeightedBlock N (xi + 4 * eta) L R t‖ ≤
          C * ((L : ℝ) / N) * (R : ℝ) ^ (4 * eta) *
            pintz2023CorollaryTwoMajorant r L epsilon xi t := by
  obtain ⟨C₀, hC₀, hCor⟩ :=
    pintz2023_corollary_two_native r epsilon B hr hepsilon hB
  refine ⟨4 * C₀, mul_pos (by norm_num) hC₀, ?_⟩
  intro N L R xi eta t hN hL hLR hR hRN heta ht hxi hscale
  have hPartial : ∀ j, j ≤ R - L →
      ‖pintz2023WeightedBlock xi L (L + j) t‖ ≤
        C₀ * pintz2023CorollaryTwoMajorant r L epsilon xi t := by
    intro j hj
    by_cases hj0 : j = 0
    · subst j
      simp [pintz2023WeightedBlock]
      unfold pintz2023CorollaryTwoMajorant
      positivity
    · exact hCor xi L (L + j) t hxi hL (by omega) (by omega) ht hscale
  have hKernel :=
    norm_pintz2023HalaszKernelWeightedBlock_shift_le_of_prefix
      hN hL hLR hRN (show 0 ≤ 4 * eta by positivity) hPartial
  have hNReal : (0 : ℝ) < N := by exact_mod_cast hN
  have hRReal : (R : ℝ) ≤ 2 * (L : ℝ) := by exact_mod_cast hR
  have hRDiv : (R : ℝ) / N ≤ 2 * ((L : ℝ) / N) := by
    calc
      (R : ℝ) / N ≤ (2 * (L : ℝ)) / N :=
        div_le_div_of_nonneg_right hRReal hNReal.le
      _ = 2 * ((L : ℝ) / N) := by ring
  have hMajorantNonneg : 0 ≤
      pintz2023CorollaryTwoMajorant r L epsilon xi t := by
    unfold pintz2023CorollaryTwoMajorant
    positivity
  calc
    ‖pintz2023HalaszKernelWeightedBlock N (xi + 4 * eta) L R t‖ ≤
        2 * ((R : ℝ) / N) * (R : ℝ) ^ (4 * eta) *
          (C₀ * pintz2023CorollaryTwoMajorant r L epsilon xi t) := hKernel
    _ ≤ 2 * (2 * ((L : ℝ) / N)) * (R : ℝ) ^ (4 * eta) *
          (C₀ * pintz2023CorollaryTwoMajorant r L epsilon xi t) := by
      gcongr
    _ = (4 * C₀) * ((L : ℝ) / N) * (R : ℝ) ^ (4 * eta) *
          pintz2023CorollaryTwoMajorant r L epsilon xi t := by ring

/-- Equation (4.23) after restoring the `n^(4 eta)` factor that occurs in
the actual Gram entry (4.19).  The factor is displayed rather than hidden in
an implied constant. -/
theorem pintz2023_equation423_shift_four_eta_native
    (r : ℕ) (epsilon B : ℝ) (hr : 3 ≤ r)
    (hepsilon : 0 < epsilon) (hB : 0 < B) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N L R : ℕ) (xi eta t : ℝ),
        0 < N → 0 < L → L < R → R ≤ 2 * L → R ≤ N →
        0 ≤ eta → 0 < t →
        xi ≤ pintz2023HBAlpha r - 6 * epsilon →
        (L : ℝ) ≤ B * t ^ (2 / (r : ℝ)) →
        ‖pintz2023HalaszKernelWeightedBlock N (xi + 4 * eta) L R t‖ ≤
          C * ((L : ℝ) / N) * (R : ℝ) ^ (4 * eta) *
            (L : ℝ) ^ (-3 * epsilon) *
              (1 + t ^ pintz2023HBAlpha r /
                (L : ℝ) ^ (1 / (r : ℝ))) := by
  obtain ⟨C₀, hC₀, hCor⟩ :=
    pintz2023_corollary_two_native r epsilon B hr hepsilon hB
  refine ⟨4 * C₀, mul_pos (by norm_num) hC₀, ?_⟩
  intro N L R xi eta t hN hL hLR hR hRN heta ht hxi hscale
  have hPartial : ∀ j, j ≤ R - L →
      ‖pintz2023WeightedBlock xi L (L + j) t‖ ≤
        C₀ * pintz2023CorollaryTwoMajorant r L epsilon xi t := by
    intro j hj
    by_cases hj0 : j = 0
    · subst j
      simp [pintz2023WeightedBlock]
      unfold pintz2023CorollaryTwoMajorant
      positivity
    · exact hCor xi L (L + j) t hxi hL (by omega)
        (by omega) ht hscale
  have hKernel :=
    norm_pintz2023HalaszKernelWeightedBlock_shift_le_of_prefix
      hN hL hLR hRN (show 0 ≤ 4 * eta by positivity) hPartial
  have hMajorant := pintz2023CorollaryTwoMajorant_le_equation423
    hr hL ht hxi
  have hNReal : (0 : ℝ) < N := by exact_mod_cast hN
  have hRReal : (R : ℝ) ≤ 2 * (L : ℝ) := by exact_mod_cast hR
  have hRDiv : (R : ℝ) / N ≤ 2 * ((L : ℝ) / N) := by
    calc
      (R : ℝ) / N ≤ (2 * (L : ℝ)) / N :=
        div_le_div_of_nonneg_right hRReal hNReal.le
      _ = 2 * ((L : ℝ) / N) := by ring
  have hTailNonneg : 0 ≤
      (R : ℝ) ^ (4 * eta) *
        (C₀ * pintz2023CorollaryTwoMajorant r L epsilon xi t) := by
    have hMajorantNonneg : 0 ≤
        pintz2023CorollaryTwoMajorant r L epsilon xi t := by
      unfold pintz2023CorollaryTwoMajorant
      positivity
    positivity
  calc
    ‖pintz2023HalaszKernelWeightedBlock N (xi + 4 * eta) L R t‖ ≤
        2 * ((R : ℝ) / N) * (R : ℝ) ^ (4 * eta) *
          (C₀ * pintz2023CorollaryTwoMajorant r L epsilon xi t) := hKernel
    _ ≤ 2 * (2 * ((L : ℝ) / N)) * (R : ℝ) ^ (4 * eta) *
          (C₀ * pintz2023CorollaryTwoMajorant r L epsilon xi t) := by
      nlinarith
    _ ≤ 2 * (2 * ((L : ℝ) / N)) * (R : ℝ) ^ (4 * eta) *
          (C₀ * ((L : ℝ) ^ (-3 * epsilon) *
            (1 + t ^ pintz2023HBAlpha r /
              (L : ℝ) ^ (1 / (r : ℝ))))) := by
      gcongr
    _ = (4 * C₀) * ((L : ℝ) / N) * (R : ℝ) ^ (4 * eta) *
          (L : ℝ) ^ (-3 * epsilon) *
            (1 + t ^ pintz2023HBAlpha r /
              (L : ℝ) ^ (1 / (r : ℝ))) := by ring

#print axioms pintz2023CorollaryTwoMajorant_le_equation423
#print axioms pintz2023_equation423_native
#print axioms pintz2023_equation423_shift_four_eta_raw_native
#print axioms pintz2023_equation423_shift_four_eta_native

end

end GafniTao
