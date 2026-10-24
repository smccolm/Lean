import Dubon2026.SourceJointChartResidueAlgebras

/-! DUB-17/18 -> Kummer genus inequality -> common residue-chart constants.
This is the exact residue-idempotent step. Finite generation of the actual
overlap quotient remains an explicit upstream hypothesis; it is not a
completion claim. The original-chart equalizer, nonunit normalization,
Krull-dimension power divisibility and abstract gluing inputs are proved.
Adapted from Apache-2.0 FLT commit
6e837e75355538c7f80bab5b956861e86c4eacc2. -/
namespace Dubon2026.SourceCurve.RegularProlongation.JointChartConstants
noncomputable section

section Lagrange

variable {k : Type*} [Field k] {ι : Type*} [Fintype ι] {Fb : ι → Type*} [∀ i, Field (Fb i)]
  [∀ i, Algebra k (Fb i)]

theorem exists_indicator (M : Submodule k (∀ i, Fb i))
    (hmul : ∀ x ∈ M, ∀ y ∈ M, x * y ∈ M)
    (hconst : ∀ c : k, (fun i => algebraMap k (Fb i) c) ∈ M)
    (h : ∀ i, Fb i) (hM : h ∈ M) (cv : ι → k) (hcv : ∀ i, h i = algebraMap k (Fb i) (cv i))
    (i₀ : ι) :
    ∃ e ∈ M, (∀ i, e i = 0 ∨ e i = 1) ∧ e i₀ = 1 ∧ ∀ i, e i = 1 → cv i = cv i₀ := by
  classical
  set sV : Finset k := (Finset.univ.image cv).erase (cv i₀) with hsV
  set φ : k → (∀ i, Fb i) := fun c => (cv i₀ - c)⁻¹ • (h - fun i => algebraMap k (Fb i) c)
    with hφ_def
  have hφ : ∀ c i, φ c i = algebraMap k (Fb i) ((cv i₀ - c)⁻¹ * (cv i - c)) := fun c i => by
    show ((cv i₀ - c)⁻¹ • (h - fun i => algebraMap k (Fb i) c)) i = _
    rw [Pi.smul_apply, Pi.sub_apply, hcv i, Algebra.smul_def]
    simp only [map_mul, map_sub, map_inv₀]
  set e : ∀ i, Fb i := ∏ c ∈ sV, φ c with he_def
  have he : ∀ i, e i = algebraMap k (Fb i) (∏ c ∈ sV, (cv i₀ - c)⁻¹ * (cv i - c)) := fun i => by
    rw [he_def, Finset.prod_apply, map_prod]
    exact Finset.prod_congr rfl fun c _ => hφ c i
  have hone : ∀ i, cv i = cv i₀ → e i = 1 := fun i hi => by
    rw [he, hi, Finset.prod_eq_one fun c hc => ?_, map_one]
    exact inv_mul_cancel₀ (sub_ne_zero.mpr (Ne.symm (Finset.mem_erase.mp hc).1))
  have hzero : ∀ i, cv i ≠ cv i₀ → e i = 0 := fun i hi => by
    rw [he, Finset.prod_eq_zero (i := cv i)
      (Finset.mem_erase.mpr ⟨hi, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩)
      (by rw [sub_self, mul_zero]), map_zero]
  refine ⟨e, ?_, fun i => ?_, hone i₀ rfl, fun i hi => ?_⟩
  · rw [he_def]
    refine Finset.prod_induction _ (· ∈ M) (fun x y hx hy => hmul x hx y hy) ?_ fun c _ => ?_
    · have : (1 : ∀ i, Fb i) = fun i => algebraMap k (Fb i) 1 := funext fun i => by simp
      rw [this]; exact hconst 1
    · exact M.smul_mem _ (M.sub_mem hM (hconst c))
  · by_cases hi : cv i = cv i₀
    · exact Or.inr (hone i hi)
    · exact Or.inl (hzero i hi)
  · by_contra hne
    rw [hzero i hne] at hi
    exact zero_ne_one hi

end Lagrange

end
end Dubon2026.SourceCurve.RegularProlongation.JointChartConstants
