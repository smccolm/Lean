import Dubon2026.RectangleZeroPolynomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import Mathlib.Data.Multiset.Fintype

/-! # Newton's identities for actual zero multisets and analytic elementary symmetric functions -/

namespace Dubon2026

open scoped BigOperators

noncomputable section

theorem multiset_esymm_newton (s : Multiset ℂ) (k : ℕ) :
    (k : ℂ) * s.esymm k = (-1) ^ (k + 1) *
      ∑ a ∈ Finset.antidiagonal k with a.1 < k,
        (-1) ^ a.1 * s.esymm a.1 * (s.map (fun z => z ^ a.2)).sum := by
  classical
  let e : MvPolynomial s ℂ →ₐ[ℂ] ℂ := MvPolynomial.aeval (fun z : s => (z : ℂ))
  have he (j : ℕ) : e (MvPolynomial.esymm s ℂ j) = s.esymm j := by
    simp only [e, MvPolynomial.aeval_esymm_eq_multiset_esymm, Multiset.map_univ_coe]
  have hp (j : ℕ) : e (MvPolynomial.psum s ℂ j) = (s.map (fun z => z ^ j)).sum := by
    simp only [e, MvPolynomial.psum, map_sum, map_pow, MvPolynomial.aeval_X]
    change ((Finset.univ : Finset s).val.map (fun z : s => (z : ℂ) ^ j)).sum = _
    rw [Multiset.map_univ s (fun z : ℂ => z ^ j)]
  have hh := congrArg e (MvPolynomial.mul_esymm_eq_sum s ℂ k)
  simpa only [map_mul, map_natCast, map_pow, map_neg, map_one, map_sum, he, hp] using hh

theorem analyticAt_multiset_esymm_of_power_sums {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {f : E → Multiset ℂ} {x : E}
    (hp : ∀ j : ℕ, 0 < j → AnalyticAt ℂ (fun y => ((f y).map (fun z => z ^ j)).sum) x)
    (k : ℕ) : AnalyticAt ℂ (fun y => (f y).esymm k) x := by
  classical
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases hk : k = 0
    · subst k
      simpa [Multiset.esymm] using (analyticAt_const (𝕜 := ℂ) (x := x) (v := (1 : ℂ)))
    · have hk0 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hk
      have he : (fun y => (f y).esymm k) = (fun y => (k : ℂ)⁻¹ * ((-1 : ℂ) ^ (k + 1) *
          ∑ a ∈ Finset.antidiagonal k with a.1 < k,
            (-1) ^ a.1 * (f y).esymm a.1 * ((f y).map (fun z => z ^ a.2)).sum)) := by
        funext y
        rw [← multiset_esymm_newton, ← mul_assoc, inv_mul_cancel₀ hk0, one_mul]
      rw [he]
      apply analyticAt_const.mul
      apply analyticAt_const.mul
      apply Finset.analyticAt_fun_sum
      intro a ha
      obtain ⟨ha, hak⟩ := Finset.mem_filter.mp ha
      have haeq := Finset.mem_antidiagonal.mp ha
      exact (analyticAt_const.mul (ih a.1 hak)).mul (hp a.2 (by omega))

theorem analyticAt_complexPhaseZero_esymm {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (x : PrimeCoordinate N → ℂ)
    {l u T : ℝ} (hlu : l ≤ u) (hT : 0 ≤ T)
    (hn : ∀ s ∈ RectangleBorder (⟨l, -T⟩ : ℂ) (⟨u, T⟩ : ℂ),
      complexPhaseFamily a N (x, s) ≠ 0) (k : ℕ) :
    AnalyticAt ℂ (fun y => (rectangleZeroMultiset (complexPhaseCoefficients a N y) N hN
      (by rwa [complexPhaseCoefficients_one]) l u T).esymm k) x := by
  apply analyticAt_multiset_esymm_of_power_sums
  intro j _
  simpa only [rectangleZeroMultiset_power_sum, complexPhaseZeroPowerSum] using
    analyticAt_complexPhaseZeroPowerSum hN ha x hlu hT hn j

end

end Dubon2026
