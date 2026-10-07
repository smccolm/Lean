import Dubon2026.LatticeMellinMajorant

/-! # Exact upper-tail splitting of the actual regularized lattice Mellin transform -/

namespace Dubon2026

open UpperHalfPlane MeasureTheory Set

noncomputable section

/-- The genuine theta remainder supported on the upper integration interval. -/
def latticeThetaUpperCutoff (z : ℍ) : ℝ → ℂ :=
  (Ioi 1).indicator (fun t => (latticeThetaRemainder z t : ℂ))

/-- The actual cutoff Mellin integrand is the indicator of the entire-tail kernel. -/
theorem latticeThetaUpperCutoff_kernel (z : ℍ) (s : ℂ) :
    (fun t : ℝ => (t : ℂ) ^ (s - 1) • latticeThetaUpperCutoff z t) =
      (Ioi 1).indicator (latticeThetaMellinKernel z s) := by
  funext t
  simp only [latticeThetaUpperCutoff, Set.indicator_apply, smul_eq_mul, latticeThetaMellinKernel]
  split_ifs <;> simp

/-- The actual upper cutoff has an absolutely convergent Mellin transform at every parameter. -/
theorem mellinConvergent_latticeThetaUpperCutoff (z : ℍ) (s : ℂ) :
    MellinConvergent (latticeThetaUpperCutoff z) s := by
  rw [MellinConvergent, latticeThetaUpperCutoff_kernel]
  exact ((integrableOn_latticeThetaMellinKernel z s).integrable_indicator measurableSet_Ioi).integrableOn

/-- The Mellin transform of the literal cutoff is exactly the already constructed entire tail. -/
theorem mellin_latticeThetaUpperCutoff (z : ℍ) (s : ℂ) :
    mellin (latticeThetaUpperCutoff z) s = latticeThetaMellinTail z s := by
  rw [mellin, latticeThetaUpperCutoff_kernel, setIntegral_indicator measurableSet_Ioi]
  rw [inter_eq_right.mpr (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))]
  rfl

/-- The reciprocal cutoff is Mellin-convergent at every parameter, by the actual change of variable. -/
theorem mellinConvergent_latticeThetaReciprocalCutoff (z : ℍ) (s : ℂ) :
    MellinConvergent (fun t : ℝ => (t : ℂ) ^ (-(1 : ℂ)) • latticeThetaUpperCutoff z t⁻¹) s := by
  rw [MellinConvergent.cpow_smul]
  have h := (MellinConvergent.comp_rpow (f := latticeThetaUpperCutoff z)
    (s := s + -(1 : ℂ)) (a := -1) (by norm_num)).mpr
      (mellinConvergent_latticeThetaUpperCutoff z _)
  simpa only [Real.rpow_neg_one] using h

/-- Poisson transformation expresses the actual modified theta function as its two cutoff pieces. -/
theorem latticeThetaFEPair_modified_cutoff (z : ℍ) {t : ℝ} (ht : 0 < t) :
    (latticeThetaFEPair z).f_modif t = latticeThetaUpperCutoff z t +
      (t : ℂ) ^ (-(1 : ℂ)) • latticeThetaUpperCutoff z t⁻¹ := by
  rcases lt_trichotomy t 1 with ht1 | rfl | ht1
  · have hi : 1 < t⁻¹ := (one_lt_inv₀ ht).mpr ht1
    have hr := congrArg Complex.ofReal (latticeTheta_reciprocal z ht)
    simp only [Complex.ofReal_mul, Complex.ofReal_inv] at hr
    simp only [WeakFEPair.f_modif, latticeThetaFEPair, Pi.add_apply, Set.indicator_apply,
      Set.mem_Ioi, Set.mem_Ioo, ht1.not_gt, ht, ht1, and_self, ite_false, ite_true, zero_add,
      Real.rpow_neg_one, Complex.ofReal_inv, one_mul, smul_eq_mul, mul_one,
      latticeThetaUpperCutoff, hi, Complex.cpow_neg_one]
    rw [latticeThetaRemainder_eq z (inv_pos.mpr ht), Complex.ofReal_sub, Complex.ofReal_one, hr]
    ring
  · simp [WeakFEPair.f_modif, latticeThetaFEPair, latticeThetaUpperCutoff]
  · have hi : t⁻¹ < 1 := (inv_lt_one₀ ht).mpr ht1
    simp only [WeakFEPair.f_modif, latticeThetaFEPair, Pi.add_apply, Set.indicator_apply,
      Set.mem_Ioi, Set.mem_Ioo, ht1, ht1.not_gt, and_false, ite_false, ite_true, add_zero,
      latticeThetaUpperCutoff, hi.not_gt, smul_zero]
    rw [latticeThetaRemainder_eq z ht, Complex.ofReal_sub, Complex.ofReal_one]

/-- The actual regularized lattice continuation is half the sum of the two entire upper tails. -/
theorem latticeCompletedMellinRegular_eq_tails (z : ℍ) (s : ℂ) :
    latticeCompletedMellinRegular z s =
      (latticeThetaMellinTail z s + latticeThetaMellinTail z (1 - s)) / 2 := by
  have he : (latticeThetaFEPair z).Λ₀ s =
      mellin (latticeThetaUpperCutoff z) s +
        mellin (fun t : ℝ => (t : ℂ) ^ (-(1 : ℂ)) • latticeThetaUpperCutoff z t⁻¹) s := by
    change (∫ t : ℝ in Ioi 0, (t : ℂ) ^ (s - 1) • (latticeThetaFEPair z).f_modif t) = _
    calc
      _ = ∫ t : ℝ in Ioi 0,
          ((t : ℂ) ^ (s - 1) • latticeThetaUpperCutoff z t +
            (t : ℂ) ^ (s - 1) • ((t : ℂ) ^ (-(1 : ℂ)) • latticeThetaUpperCutoff z t⁻¹)) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        dsimp only
        rw [latticeThetaFEPair_modified_cutoff z ht, smul_add]
      _ = _ := integral_add (mellinConvergent_latticeThetaUpperCutoff z s)
        (mellinConvergent_latticeThetaReciprocalCutoff z s)
  rw [latticeCompletedMellinRegular, he, mellin_cpow_smul, mellin_comp_inv]
  simp only [neg_add_rev, neg_neg, sub_eq_add_neg, mellin_latticeThetaUpperCutoff]

/-- On every closed vertical strip, the genuine entire regular part has a positive lattice majorant. -/
theorem norm_latticeCompletedMellinRegular_le (z : ℍ) {s : ℂ} {σ : ℝ}
    (hσ : 1 < σ) (hs : s.re ≤ σ) (hs' : 1 - s.re ≤ σ) :
    ‖latticeCompletedMellinRegular z s‖ ≤ 2 * (latticeCompletedMellin z (σ : ℂ)).re := by
  rw [latticeCompletedMellinRegular_eq_tails, norm_div, Complex.norm_ofNat]
  have h1 := norm_latticeThetaMellinTail_le_completed z hσ hs
  have h2 := norm_latticeThetaMellinTail_le_completed z hσ (s := 1 - s)
    (by simpa only [Complex.sub_re, Complex.one_re] using hs')
  have h3 := norm_add_le (latticeThetaMellinTail z s) (latticeThetaMellinTail z (1 - s))
  linarith

end
end Dubon2026
