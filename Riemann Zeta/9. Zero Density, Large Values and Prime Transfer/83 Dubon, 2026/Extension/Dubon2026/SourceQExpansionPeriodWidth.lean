import Dubon2026.ModularDegeneracyCoefficients

/-! DUB-17/18 -> higher continuation -> arithmetic automorphy -> original
all-weight association -> finite Gamma1 character realization -> Picard/H1
and diamond comparison -> cusp differential realization -> rational Fourier
structure -> Fricke coefficient transport. Reuses the native Eisenstein
q-expansion and the existing sparse-series reindexing. No rationality or
analytic conjugation premise substitutes for a proof. -/
namespace Dubon2026.SourceFricke
noncomputable section
open UpperHalfPlane ModularForm SlashInvariantFormClass ModularFormClass
open scoped Manifold MatrixGroups ModularForm ArithmeticFunction.sigma

theorem qParam_one_eq_pow {N : ℕ} (hN : N ≠ 0) (τ : ℂ) :
    Function.Periodic.qParam 1 τ = Function.Periodic.qParam N τ ^ N := by
  have : (N : ℂ) ≠ 0 := by exact_mod_cast hN
  simp only [Function.Periodic.qParam, Complex.ofReal_one, div_one, Complex.ofReal_natCast]
  rw [← Complex.exp_nat_mul]
  congr 1
  field_simp

theorem qExpansion_coeff_width (f : ℍ → ℂ) {N : ℕ} (hN : N ≠ 0)
    (hper : Function.Periodic (f ∘ ofComplex) 1) (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hbd : IsBoundedAtImInfty f) (n : ℕ) :
    (qExpansion N f).coeff n =
      if N ∣ n then (qExpansion 1 f).coeff (n / N) else 0 := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hperN : Function.Periodic (f ∘ ofComplex) N := by
    simpa using hper.nat_mul N
  let f' : C(ℍ, ℂ) := ⟨f, hhol.continuous⟩
  have hfan : AnalyticAt ℂ (cuspFunction N f') 0 :=
    analyticAt_cuspFunction_zero hN' hperN hhol hbd
  have hf : ∀ τ : ℍ, HasSum (fun m : ℕ =>
      (if N ∣ m then (qExpansion 1 f).coeff (m / N) else 0) •
        Function.Periodic.qParam N τ ^ m) (f' τ) := by
    intro τ
    have hs := hasSum_qExpansion one_pos hper hhol hbd τ
    rw [qParam_one_eq_pow hN] at hs
    have hs' := Dubon2026.hasSum_pow_dvd_reindex (Nat.pos_of_ne_zero hN) hs
    convert hs' using 1
    funext m
    split_ifs <;> simp
  exact (UpperHalfPlane.qExpansion_coeff_unique f' hN' hfan hf n).symm

end
end Dubon2026.SourceFricke
