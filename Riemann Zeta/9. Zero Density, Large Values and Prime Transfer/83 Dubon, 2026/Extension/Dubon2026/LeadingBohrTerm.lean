import Dubon2026.JessenRightLimit

/-! # Uniform terminal-term dominance on the prime torus -/

namespace Dubon2026

open Filter
open scoped Topology BigOperators

noncomputable section

/-- The actual Bohr polynomial multiplied by the positive terminal exponential. -/
def scaledBohr (a : ℕ → ℂ) (N : ℕ) (σ : ℝ) : C(PrimeTorus N, ℂ) :=
  ∑ n ∈ Finset.Icc 1 N,
    (a n * (Real.exp (σ * (Real.log (lastIndex a N) - Real.log n)) : ℂ)) •
      UnitAddTorus.mFourier (primeExponent N n)

theorem exp_mul_nat_cpow_neg {n : ℕ} (hn : 1 ≤ n) (σ L : ℝ) :
    (Real.exp (σ * L) : ℂ) * (n : ℂ) ^ (-(σ : ℂ)) =
      (Real.exp (σ * (L - Real.log n)) : ℂ) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hc := Complex.ofReal_cpow (x := (n : ℝ)) hnpos.le (y := -σ)
  rw [Complex.ofReal_neg, Complex.ofReal_natCast] at hc
  rw [← hc, ← Complex.ofReal_mul, Real.rpow_def_of_pos hnpos, ← Real.exp_add]
  congr 2
  ring

theorem scaledBohr_eq_smul (a : ℕ → ℂ) (N : ℕ) (σ : ℝ) :
    scaledBohr a N σ = (Real.exp (σ * Real.log (lastIndex a N)) : ℂ) •
      bohrOnTorus a N σ := by
  ext z
  simp only [scaledBohr, ContinuousMap.sum_apply, ContinuousMap.smul_apply, smul_eq_mul,
    bohrOnTorus_eq_fourier_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [← exp_mul_nat_cpow_neg (Finset.mem_Icc.mp hn).1]
  ring

theorem tendsto_scaledBohr_atBot {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) :
    Tendsto (scaledBohr a N) atBot
      (𝓝 (a (lastIndex a N) • UnitAddTorus.mFourier (primeExponent N (lastIndex a N)))) := by
  classical
  let M := lastIndex a N
  have hM : M ∈ Finset.Icc 1 N :=
    Finset.mem_Icc.mpr ⟨one_le_lastIndex hN ha, lastIndex_le a N⟩
  have ht (n : ℕ) (hn : n ∈ Finset.Icc 1 N) :
      Tendsto (fun σ : ℝ =>
        (a n * (Real.exp (σ * (Real.log M - Real.log n)) : ℂ)) •
          UnitAddTorus.mFourier (primeExponent N n)) atBot
        (𝓝 (if n = M then a n • UnitAddTorus.mFourier (primeExponent N n) else 0)) := by
    have hzero : (0 : ℂ) • UnitAddTorus.mFourier (primeExponent N n) =
        (0 : C(PrimeTorus N, ℂ)) := by
      ext z
      simp only [ContinuousMap.smul_apply, smul_eq_mul, zero_mul, ContinuousMap.zero_apply]
    rcases lt_trichotomy n M with hnm | rfl | hmn
    · have hnpos : (0 : ℝ) < n := by
        exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hn).1)
      have hlog : 0 < Real.log (M : ℝ) - Real.log n :=
        sub_pos.mpr (Real.strictMonoOn_log hnpos
          (show (0 : ℝ) < M from hnpos.trans (by exact_mod_cast hnm))
          (by exact_mod_cast hnm))
      have he := Real.tendsto_exp_atBot.comp (tendsto_id.atBot_mul_const hlog)
      have hc := (Complex.continuous_ofReal.continuousAt.tendsto.comp he).const_mul (a n)
      simpa only [Complex.ofReal_zero, mul_zero, if_neg hnm.ne, hzero] using
        hc.smul_const (UnitAddTorus.mFourier (primeExponent N n))
    · simp only [sub_self, mul_zero, Real.exp_zero, Complex.ofReal_one, mul_one, ite_true]
      exact tendsto_const_nhds
    · have hz := coefficient_eq_zero_of_lastIndex_lt (Finset.mem_Icc.mp hn).2 hmn
      simpa only [hz, zero_mul, if_neg hmn.ne', hzero] using
        (tendsto_const_nhds (x := (0 : C(PrimeTorus N, ℂ))) (f := (atBot : Filter ℝ)))
  change Tendsto (fun σ => scaledBohr a N σ) _ _
  simpa only [scaledBohr, M, Finset.sum_ite_eq', hM, if_pos] using
    tendsto_finsetSum (Finset.Icc 1 N) ht

theorem norm_mFourier_apply (N : ℕ) (k : PrimeCoordinate N → ℤ) (z : PrimeTorus N) :
    ‖UnitAddTorus.mFourier k z‖ = 1 := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, norm_prod, fourier_apply,
    Circle.norm_coe, Finset.prod_const_one]

theorem norm_terminal_bohr_term (a : ℕ → ℂ) (N : ℕ) (z : PrimeTorus N) :
    ‖(a (lastIndex a N) • UnitAddTorus.mFourier (primeExponent N (lastIndex a N))) z‖ =
      ‖a (lastIndex a N)‖ := by
  simp only [ContinuousMap.smul_apply, smul_eq_mul, norm_mul, norm_mFourier_apply, mul_one]

end

end Dubon2026
