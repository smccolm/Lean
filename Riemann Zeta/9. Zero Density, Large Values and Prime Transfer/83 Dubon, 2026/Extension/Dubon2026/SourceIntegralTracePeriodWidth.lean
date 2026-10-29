import Dubon2026.SourceQExpansionPeriodWidth
import Mathlib.Tactic

/-! DUB-17/18 -> original Gamma1 degree preservation -> even-weight
slash integrality -> peaked auxiliary trace. Compare the minimal cusp
width with the original integral expansion width. Reuse the existing
sparse-series reindexing proof of SourceQExpansionPeriodWidth; the only
extension needed is a positive base width other than one. The matching
pinned Anthropic source is S_UpperHalfPlane_qExpansion_coeff_mul_width,
revision 6e837e75355538c7f80bab5b956861e86c4eacc2 (Apache-2.0). -/
namespace Dubon2026.SourceFunctionField.IntegralTrace
noncomputable section
open UpperHalfPlane
open scoped Manifold

private theorem qParam_multiple_width_pow (h : ℝ) {N : ℕ} (hN : N ≠ 0) (z : ℂ) :
    Function.Periodic.qParam ((N : ℝ) * h) z ^ N = Function.Periodic.qParam h z := by
  have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast hN
  simp only [Function.Periodic.qParam]
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  field_simp

theorem qExpansion_coeff_multiple_width (f : ℍ → ℂ) (h : ℝ) (hh : 0 < h)
    {N : ℕ} (hN : N ≠ 0) (hper : Function.Periodic (f ∘ ofComplex) h)
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (hbd : IsBoundedAtImInfty f) (n : ℕ) :
    (qExpansion ((N : ℝ) * h) f).coeff n =
      if N ∣ n then (qExpansion h f).coeff (n / N) else 0 := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hperN : Function.Periodic (f ∘ ofComplex) (((N : ℝ) * h : ℝ) : ℂ) := by
    simpa using hper.nat_mul N
  let f' : C(ℍ, ℂ) := ⟨f, hhol.continuous⟩
  have hfan : AnalyticAt ℂ (cuspFunction ((N : ℝ) * h) f') 0 :=
    analyticAt_cuspFunction_zero (mul_pos hN' hh) hperN hhol hbd
  have hf : ∀ τ : ℍ, HasSum (fun m : ℕ =>
      (if N ∣ m then (qExpansion h f).coeff (m / N) else 0) •
        Function.Periodic.qParam ((N : ℝ) * h) τ ^ m) (f' τ) := by
    intro τ
    have hs := hasSum_qExpansion hh hper hhol hbd τ
    rw [← qParam_multiple_width_pow h hN] at hs
    have hs' := Dubon2026.hasSum_pow_dvd_reindex (Nat.pos_of_ne_zero hN) hs
    convert hs' using 1
    funext m
    split_ifs <;> simp
  exact (UpperHalfPlane.qExpansion_coeff_unique f' (mul_pos hN' hh) hfan hf n).symm

end
end Dubon2026.SourceFunctionField.IntegralTrace
