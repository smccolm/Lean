import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! DUB-17/18 -> original torsion cardinality -> Abel-Jacobi -> compact original curve.
Local analytic multiplicity supplies sufficiently many nearby preimages.
Together with the already proved total original j-fiber degree, it will
exclude additional places outside the chosen finite chart neighborhoods.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_AlgebraicCurve_Place_exists_finset_forall_exists_localParam_eq_complex.
-/
namespace Dubon2026.SourceFunctionField.AnalyticFiber
noncomputable section
open Filter Set Metric Polynomial
open scoped Topology

theorem exists_analyticAt_pow_eq {h : ℂ → ℂ} (hh : AnalyticAt ℂ h 0) (h0 : h 0 ≠ 0) {e : ℕ}
    (he : 0 < e) :
    ∃ k : ℂ → ℂ, AnalyticAt ℂ k 0 ∧ k 0 ≠ 0 ∧ ∀ᶠ u in 𝓝 0, k u ^ e = h u := by
  obtain ⟨β, hβ⟩ := IsAlgClosed.exists_pow_nat_eq (h 0) he
  have hβ0 : β ≠ 0 := by
    rintro rfl
    rw [zero_pow he.ne'] at hβ
    exact h0 hβ.symm
  have he0 : (e : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr he.ne'
  refine ⟨fun u => β * Complex.exp (Complex.log (h u / h 0) / e), ?_, ?_, ?_⟩
  · have h1 : AnalyticAt ℂ (fun u => h u / h 0) 0 := hh.div analyticAt_const h0
    have hslit : (fun u => h u / h 0) 0 ∈ Complex.slitPlane := by
      simp only [div_self h0]
      exact Complex.one_mem_slitPlane
    have h2 : AnalyticAt ℂ (fun u => Complex.log (h u / h 0) / e) 0 :=
      (h1.clog hslit).div analyticAt_const he0
    exact analyticAt_const.mul h2.cexp'
  · simp only [div_self h0, Complex.log_one, zero_div, Complex.exp_zero, mul_one]
    exact hβ0
  · filter_upwards [hh.continuousAt.eventually_ne h0] with u hu
    rw [mul_pow, ← Complex.exp_nat_mul, mul_div_cancel₀ _ he0,
      Complex.exp_log (div_ne_zero hu h0), hβ, mul_div_cancel₀ _ h0]


end
end Dubon2026.SourceFunctionField.AnalyticFiber
