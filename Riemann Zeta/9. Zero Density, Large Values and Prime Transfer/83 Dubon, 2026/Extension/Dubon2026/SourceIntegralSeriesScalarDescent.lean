import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic

/-! DUB-17/18 -> original Gamma1 degree/genus -> uniform level-power
slash integrality -> common integral denominator. Descend a finite
series combination to its actual coefficient subfield using a native
linear left inverse. This avoids a separate finite coefficient matrix
and determinant argument. Its intended consumer combines the already
proved integral cusp-form span with algebraicity of actual Fourier
coefficients, then clears only finitely many scalar denominators.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, revision
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_PowerSeries_exists_sum_smul_eq_of_forall_coeff_mem. -/
namespace Dubon2026.SourceFunctionField.IntegralFricke
noncomputable section

theorem exists_sum_smul_eq_of_forall_coeff_mem
    {L : Type} [Field L] (K₀ : Subfield L) {ι : Type*} [Fintype ι] (g : ι → PowerSeries L)
    (hg : ∀ (i : ι) (m : ℕ), (g i).coeff m ∈ K₀)
    (c : ι → L) (h : ∀ m : ℕ, (∑ i, c i • g i).coeff m ∈ K₀) :
    ∃ c' : ι → L, (∀ i, c' i ∈ K₀) ∧ ∑ i, c' i • g i = ∑ i, c i • g i := by
  classical

  let ι : K₀ →ₗ[K₀] L := (Algebra.linearMap K₀ L)
  have hι : Function.Injective ι := fun x y h => Subtype.ext (by simpa [ι] using h)
  obtain ⟨π, hπ⟩ := LinearMap.exists_leftInverse_of_injective ι (LinearMap.ker_eq_bot.mpr hι)
  have hπι : ∀ z : K₀, π (z : L) = z := fun z => by
    have := congrArg (fun f => f z) hπ
    simp [ι] at this
    exact this
  refine ⟨fun i => (π (c i) : L), fun i => (π (c i)).2, ?_⟩
  ext m
  simp only [map_sum, map_smul, smul_eq_mul]

  have hm := h m
  simp only [map_sum, map_smul, smul_eq_mul] at hm

  have key : (π (∑ i, c i * (g i).coeff m) : L) = ∑ i, (π (c i) : L) * (g i).coeff m := by
    rw [map_sum]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    have : c i * (g i).coeff m = ((⟨(g i).coeff m, hg i m⟩ : K₀) : K₀) • c i := by
      rw [Subfield.smul_def]; exact mul_comm _ _
    rw [this, map_smul]

    rw [show (((⟨(g i).coeff m, hg i m⟩ : K₀) • π (c i) : K₀) : L) = ((g i).coeff m) * (π (c i) : L) from rfl]
    exact mul_comm _ _
  rw [← key, hπι ⟨_, hm⟩]

end
end Dubon2026.SourceFunctionField.IntegralFricke
