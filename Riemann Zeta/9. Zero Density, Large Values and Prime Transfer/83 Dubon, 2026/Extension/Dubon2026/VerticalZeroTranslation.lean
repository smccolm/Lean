import Dubon2026.UniformTwistZeroBound
import Dubon2026.UnitLogTail

/-! # Vertical translation preserves the actual zeros and their analytic multiplicities -/

namespace Dubon2026

open Complex

theorem dirichletSum_twist_height (a : ℕ → ℂ) (N : ℕ) (τ : ℝ) (s : ℂ) :
    dirichletSum (twistedCoefficients a N (primeTorusFlow N τ)) N s =
      dirichletSum a N (s + Complex.I * τ) := by
  have hs : (s.re : ℂ) + Complex.I * s.im = s := by
    rw [mul_comm Complex.I, Complex.re_add_im]
  calc
    _ = verticalFamily a N s.re (primeTorusFlow N τ) s.im := by rw [verticalFamily, hs]
    _ = verticalFamily a N s.re 0 (s.im + τ) := by
      rw [verticalFamily_add_height, zero_add]
    _ = dirichletSum a N ((s.re : ℂ) + Complex.I * ((s.im + τ : ℝ) : ℂ)) :=
      verticalFamily_zero_phase a N s.re (s.im + τ)
    _ = dirichletSum a N (s + Complex.I * τ) := by
      rw [Complex.ofReal_add, mul_add, ← add_assoc, hs]

theorem zeroMultiplicity_twist_height (a : ℕ → ℂ) (N : ℕ) (τ : ℝ) (s : ℂ) :
    zeroMultiplicity (twistedCoefficients a N (primeTorusFlow N τ)) N s =
      zeroMultiplicity a N (s + Complex.I * τ) := by
  have he : dirichletSum (twistedCoefficients a N (primeTorusFlow N τ)) N =
      dirichletSum a N ∘ (fun w : ℂ => w + Complex.I * τ) :=
    funext (dirichletSum_twist_height a N τ)
  have hg : AnalyticAt ℂ (fun w : ℂ => w + Complex.I * τ) s :=
    analyticAt_id.add analyticAt_const
  have hd : deriv (fun w : ℂ => w + Complex.I * τ) s ≠ 0 := by
    have hd₀ : HasDerivAt (fun w : ℂ => w + Complex.I * τ) 1 s :=
      (hasDerivAt_id s).add_const _
    rw [hd₀.deriv]
    exact one_ne_zero
  simp only [zeroMultiplicity, analyticOrderNatAt, he,
    analyticOrderAt_comp_of_deriv_ne_zero hg hd]

end Dubon2026
