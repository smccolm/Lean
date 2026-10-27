import Dubon2026.SourceLaurentPolynomialRealization
import Dubon2026.SourceModularJSeries
import Mathlib.NumberTheory.ModularForms.QExpansion

/-! DUB-17/18 -> original all-weight association -> finite Gamma1
characters -> Picard/H1 and diamond comparison -> differential realization
-> rational Fourier structure -> Fricke level field -> invariant fractions.
Transfer the existing exact Laurent-series level-one polynomial reduction
to the actual analytic functions using already proved convergent Laurent
products. No polynomial representation is assumed. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open UpperHalfPlane
open scoped MatrixGroups ModularForm Manifold

namespace RealL

theorem pow {h : ℝ} (hh : 0 < h) {A : LaurentSeries ℂ} {F : ℍ → ℂ}
    (hA : RealL h A F) (n : ℕ) : RealL h (A ^ n) (F ^ n) := by
  induction n with
  | zero => simpa only [pow_zero] using RealL.one h
  | succ n ih => simpa only [pow_succ] using ih.mul hh hA

theorem aeval {h : ℝ} (hh : 0 < h) {A : LaurentSeries ℂ} {F : ℍ → ℂ}
    (hA : RealL h A F) (P : Polynomial ℂ) :
    RealL h (Polynomial.aeval A P) (fun τ => P.eval (F τ)) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    simpa only [map_add, Polynomial.eval_add] using hP.add hQ
  | monomial n c =>
    simpa only [Polynomial.aeval_monomial, Polynomial.eval_monomial,
      HahnSeries.algebraMap_apply', PowerSeries.algebraMap_eq, HahnSeries.ofPowerSeries_C] using
      (RealL.C h c).mul hh (hA.pow hh n)

end RealL

theorem realL_qExpansion {h : ℝ} (hh : 0 < h) (F : ℍ → ℂ)
    (hper : Function.Periodic (F ∘ ofComplex) h)
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F) (hbd : IsBoundedAtImInfty F) :
    RealL h (qExpansion h F : LaurentSeries ℂ) F := by
  intro τ
  rw [← (Nat.cast_injective (R := ℤ)).hasSum_iff]
  · change HasSum (fun n : ℕ => (qExpansion h F : LaurentSeries ℂ).coeff (n : ℤ) *
      Function.Periodic.qParam h (τ : ℂ) ^ (n : ℤ)) (F τ)
    simpa only [HahnSeries.ofPowerSeries_apply_coeff, zpow_natCast, smul_eq_mul]
      using hasSum_qExpansion hh hper hhol hbd τ
  · intro m hm
    have hm' : m < 0 := by
      by_contra hge
      push Not at hge
      exact hm ⟨m.toNat, Int.toNat_of_nonneg hge⟩
    rw [ofPowerSeries_coeff_of_neg _ hm', zero_mul]

end
end Dubon2026.SourceFunctionField
