import Dubon2026.Gamma0CompletedCusp

/-! # The genuine primitive Eisenstein continuation under the cusp integral -/

namespace Dubon2026

open UpperHalfPlane MeasureTheory CongruenceSubgroup Matrix.SpecialLinearGroup Filter
open scoped Topology

noncomputable section

/-- The actual continued primitive Eisenstein kernel is integrable against the true cusp density. -/
theorem integrableOn_gamma0EisensteinContinuation_petersson {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (s : ℂ) :
    IntegrableOn (fun z : ℍ => gamma0EisensteinContinuation Q z s * petersson k f f z)
      (gamma0FundamentalDomain Q) := by
  simpa only [gamma0EisensteinContinuation, div_mul_eq_mul_div] using
    (integrableOn_gamma0CompletedLattice_petersson f s).div_const (gamma0CompletionFactor Q s)

/-- The literal integral of the continued primitive Eisenstein series against the actual cusp form. -/
def gamma0CuspEisensteinContinuation {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (s : ℂ) : ℂ :=
  ∫ z : ℍ in gamma0FundamentalDomain Q,
    gamma0EisensteinContinuation Q z s * petersson k f f z

/-- The true continued cusp integral is the proved completed lattice integral divided by its exact factor. -/
theorem gamma0CuspEisensteinContinuation_eq_div {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (s : ℂ) :
    gamma0CuspEisensteinContinuation f s = gamma0CompletedCusp f s / gamma0CompletionFactor Q s := by
  simp only [gamma0CuspEisensteinContinuation, gamma0EisensteinContinuation,
    div_mul_eq_mul_div, integral_div, gamma0CompletedCusp]

/-- In the convergence half-plane the continued integral is the actual primitive Eisenstein integral. -/
theorem gamma0CuspEisensteinContinuation_eq_integral {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) {s : ℂ} (hs : 1 < s.re) :
    gamma0CuspEisensteinContinuation f s =
      ∫ z : ℍ in gamma0FundamentalDomain Q, gamma0Eisenstein Q s z * petersson k f f z := by
  unfold gamma0CuspEisensteinContinuation
  simp only [gamma0EisensteinContinuation_eq Q _ hs]

/-- The actual continued primitive Eisenstein cusp integral is holomorphic in Re(s)>1/2 away from 1. -/
theorem differentiableAt_gamma0CuspEisensteinContinuation {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) {s : ℂ} (hs : 1 / 2 < s.re) (hs1 : s ≠ 1) :
    DifferentiableAt ℂ (gamma0CuspEisensteinContinuation f) s := by
  have hs0 : s ≠ 0 := by
    intro h
    simp only [h, Complex.zero_re] at hs
    linarith
  rw [funext (gamma0CuspEisensteinContinuation_eq_div f)]
  exact (differentiableAt_gamma0CompletedCusp f hs0 hs1).div
    (differentiableAt_gamma0CompletionFactor Q hs) (gamma0CompletionFactor_ne_zero Q hs)

/-- The actual primitive Eisenstein cusp integral has the explicit Petersson pole coefficient. -/
theorem gamma0CuspEisensteinContinuation_residue_one {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) :
    Tendsto (fun s : ℂ => (s - 1) * gamma0CuspEisensteinContinuation f s) (𝓝[≠] 1)
      (𝓝 ((gamma0EisensteinResidue Q : ℂ) * cuspPetersson f f)) := by
  have hd : Tendsto (gamma0CompletionFactor Q) (𝓝[≠] (1 : ℂ))
      (𝓝 (gamma0CompletionFactor Q 1)) :=
    (differentiableAt_gamma0CompletionFactor Q (s := 1) (by norm_num)).continuousAt.tendsto
      |>.mono_left nhdsWithin_le_nhds
  have h := (gamma0CompletedCusp_residue_one f).div hd
    (gamma0CompletionFactor_ne_zero Q (s := 1) (by norm_num))
  change Tendsto (fun s : ℂ => ((s - 1) * gamma0CompletedCusp f s) / gamma0CompletionFactor Q s)
    (𝓝[≠] 1) (𝓝 ((((Q.totient : ℂ) / (2 * (Q : ℂ) ^ 2)) * cuspPetersson f f) /
      gamma0CompletionFactor Q 1)) at h
  have hL : ((DirichletCharacter.LFunctionTrivChar Q 2).re : ℂ) =
      DirichletCharacter.LFunctionTrivChar Q 2 := by
    apply Complex.ext
    · simp
    · simp [LFunctionTrivChar_two_im]
  have he : (((Q.totient : ℂ) / (2 * (Q : ℂ) ^ 2)) * cuspPetersson f f) /
      gamma0CompletionFactor Q 1 = (gamma0EisensteinResidue Q : ℂ) * cuspPetersson f f := by
    rw [gamma0CompletionFactor_one, gamma0EisensteinResidue]
    push_cast
    rw [hL]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
    ring
  simpa only [he, gamma0CuspEisensteinContinuation_eq_div, mul_div_assoc] using h

end
end Dubon2026
