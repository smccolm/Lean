import Dubon2026.RealCyclicL2
import Dubon2026.RealLiftInfinitesimal
import Mathlib.Analysis.Complex.Liouville

/-! # Uniform genuine holomorphic jet bounds for all original real slash transforms -/

namespace Dubon2026

noncomputable section
open UpperHalfPlane Matrix.SpecialLinearGroup
open scoped MatrixGroups ModularForm Manifold

/-- The actual closed half-radius disk around i stays in the upper half-plane with controlled height. -/
theorem half_disk_im_bounds {z : ℂ} (hz : z ∈ Metric.closedBall Complex.I (1 / 2 : ℝ)) :
    (1 / 2 : ℝ) ≤ z.im ∧ z.im ≤ 3 / 2 := by
  have hn : ‖z - Complex.I‖ ≤ (1 / 2 : ℝ) := mem_closedBall_iff_norm.mp hz
  have hi := (Complex.abs_im_le_norm (z - Complex.I)).trans hn
  simp only [Complex.sub_im, Complex.I_im] at hi
  obtain ⟨ha, hb⟩ := abs_le.mp hi
  constructor <;> linarith

/-- The actual reciprocal half-weight factor is bounded uniformly on the closed positive height interval. -/
theorem reciprocal_half_weight_bounded (k : ℤ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y ∈ Set.Icc (1 / 2 : ℝ) (3 / 2),
      ‖((Real.sqrt y : ℝ) : ℂ) ^ (-k)‖ ≤ B := by
  have hc : ContinuousOn (fun y : ℝ => ‖((Real.sqrt y : ℝ) : ℂ) ^ (-k)‖)
      (Set.Icc (1 / 2 : ℝ) (3 / 2)) := by
    apply ContinuousOn.norm
    apply ((Complex.continuous_ofReal.comp Real.continuous_sqrt).continuousOn).zpow₀
    intro y hy
    exact Or.inl (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by linarith [hy.1])).ne')
  obtain ⟨y, hy, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (show (Set.Icc (1 / 2 : ℝ) (3 / 2)).Nonempty from ⟨1, by norm_num⟩) hc
  exact ⟨_, norm_nonneg _, fun z hz => hmax hz⟩

/-- The original globally bounded cusp lift bounds every actual slash transform on the same fixed complex disk. -/
theorem realWeightLift_slash_disk_bounded {Γ : Subgroup (GL (Fin 2) ℝ)}
    [Γ.IsArithmetic] {k : ℤ} (f : CuspForm Γ k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : SL(2, ℝ), ∀ z ∈ Metric.closedBall Complex.I (1 / 2 : ℝ),
      ‖((f ∣[k] (mapGL ℝ g)) ∘ ofComplex) z‖ ≤ C := by
  obtain ⟨A, hA0, hA⟩ := realWeightLift_bounded f
  obtain ⟨B, hB0, hB⟩ := reciprocal_half_weight_bounded k
  refine ⟨A * B, mul_nonneg hA0 hB0, ?_⟩
  intro g z hz
  have hzi := half_disk_im_bounds hz
  have hzp : 0 < z.im := by linarith [hzi.1]
  let w : ℍ := ⟨z, hzp⟩
  have he := realWeightLift_mul k f g w.toSL2R
  rw [realWeightLift_section] at he
  have hn : ((Real.sqrt w.im : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr w.im_pos).ne'
  have hs : ((f : ℍ → ℂ) ∣[k] (mapGL ℝ g)) w =
      realWeightLift k f (g * w.toSL2R) * ((Real.sqrt w.im : ℝ) : ℂ) ^ (-k) := by
    rw [he, mul_assoc, ← zpow_add₀ hn, add_neg_cancel, zpow_zero, mul_one]
  rw [Function.comp_apply, ofComplex_apply_of_im_pos hzp]
  change ‖((f : ℍ → ℂ) ∣[k] (mapGL ℝ g)) w‖ ≤ A * B
  rw [hs, norm_mul]
  exact mul_le_mul (hA _) (hB z.im hzi) (norm_nonneg _) hA0

/-- Cauchy's genuine derivative estimate gives uniform bounds for every order and every original real translate. -/
theorem realWeightLift_slash_jets_bounded {Γ : Subgroup (GL (Fin 2) ℝ)}
    [Γ.IsArithmetic] {k : ℤ} (f : CuspForm Γ k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∀ g : SL(2, ℝ),
      ‖iteratedDeriv n ((f ∣[k] (mapGL ℝ g)) ∘ ofComplex) Complex.I‖ ≤
        (n.factorial : ℝ) * C / (1 / 2 : ℝ) ^ n := by
  obtain ⟨C, hC0, hC⟩ := realWeightLift_slash_disk_bounded f
  refine ⟨C, hC0, ?_⟩
  intro n g
  apply Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n (by norm_num)
  · apply (UpperHalfPlane.mdifferentiable_iff.mp
      ((ModularFormClass.holo f).slash k (mapGL ℝ g))).diffContOnCl_ball
    intro z hz
    change 0 < z.im
    linarith [(half_disk_im_bounds hz).1]
  · intro z hz
    exact hC g z (Metric.sphere_subset_closedBall hz)

end
end Dubon2026
