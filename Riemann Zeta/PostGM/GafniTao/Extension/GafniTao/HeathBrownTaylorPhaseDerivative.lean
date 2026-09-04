import GafniTao.HeathBrownTaylorPolynomialBridge

/-!
# Differentiating Heath-Brown's Taylor phase

The source's summation-by-parts step uses
`g_n(x)=f(n+x)-f_n(x)`.  Here the finite polynomial `f_n` is the literal
source polynomial, and its derivative is identified with the shifted Taylor
polynomial of `f'` used by the Lagrange-remainder theorem.
-/

open Set

namespace GafniTao

noncomputable section

noncomputable def heathBrownTaylorError
    (k : ℕ) (f : ℝ → ℝ) (n x : ℝ) : ℝ :=
  f (n + x) - heathBrownTaylorPolynomial k f n x

theorem hasDerivAt_heathBrownTaylorPolynomial
    {k : ℕ} (hk : 2 ≤ k) (f : ℝ → ℝ) (n x : ℝ) :
    HasDerivAt (fun y => heathBrownTaylorPolynomial k f n y)
      (heathBrownTaylorDerivativePolynomial k f n x) x := by
  have horder : k - 2 + 1 = k - 1 := by omega
  have ht := hasDerivAt_taylorWithinEval_succ
    (f := f) (s := Set.univ) (x₀ := n) (x := n + x) (n := k - 2)
  have hshift : HasDerivAt (fun y : ℝ => n + y) 1 x :=
    by simpa using (hasDerivAt_const x n).add (hasDerivAt_id x)
  have hcomp := ht.comp x hshift
  rw [derivWithin_univ] at hcomp
  have hvalue :
      taylorWithinEval (deriv f) (k - 2) Set.univ n (n + x) =
        heathBrownTaylorDerivativePolynomial k f n x := by
    rw [taylor_within_apply]
    unfold heathBrownTaylorDerivativePolynomial
    rw [horder]
    apply Finset.sum_congr rfl
    intro j hj
    rw [iteratedDerivWithin_univ, iteratedDeriv_deriv_eq_succ]
    simp only [smul_eq_mul]
    ring
  have hfun :
      (fun y : ℝ => taylorWithinEval f (k - 2 + 1) Set.univ n (n + y)) =
        (fun y : ℝ => heathBrownTaylorPolynomial k f n y) := by
    funext y
    rw [horder]
    have hkform : k - 1 + 1 = k := by omega
    rw [← hkform]
    exact taylorWithinEval_univ_eq_heathBrownTaylorPolynomial
      (k - 1) f n y
  change HasDerivAt
    (fun y : ℝ => taylorWithinEval f (k - 2 + 1) Set.univ n (n + y))
    _ x at hcomp
  rw [hfun, hvalue, mul_one] at hcomp
  exact hcomp

theorem hasDerivAt_heathBrownTaylorError
    {k : ℕ} (hk : 2 ≤ k) {f : ℝ → ℝ} {n x : ℝ}
    (hf : HasDerivAt f (deriv f (n + x)) (n + x)) :
    HasDerivAt (fun y => heathBrownTaylorError k f n y)
      (deriv f (n + x) - heathBrownTaylorDerivativePolynomial k f n x) x := by
  unfold heathBrownTaylorError
  have hshift : HasDerivAt (fun y : ℝ => n + y) 1 x := by
    simpa using (hasDerivAt_const x n).add (hasDerivAt_id x)
  have hcomp := hf.comp x hshift
  change HasDerivAt (fun y : ℝ => f (n + y)) _ x at hcomp
  simpa using hcomp.sub (hasDerivAt_heathBrownTaylorPolynomial hk f n x)

theorem deriv_heathBrownTaylorError
    {k : ℕ} (hk : 2 ≤ k) {f : ℝ → ℝ} {n x : ℝ}
    (hf : HasDerivAt f (deriv f (n + x)) (n + x)) :
    deriv (fun y => heathBrownTaylorError k f n y) x =
      deriv f (n + x) - heathBrownTaylorDerivativePolynomial k f n x :=
  (hasDerivAt_heathBrownTaylorError hk hf).deriv

/-- The exact source derivative error, with the factorial still present. -/
theorem norm_heathBrownTaylorError_derivative_le
    {k : ℕ} (hk : 2 ≤ k) {f : ℝ → ℝ} {n x A lambda : ℝ}
    (hx : 0 < x)
    (hfat : ContDiffAt ℝ (k - 2 : ℕ) (deriv f) n)
    (hfon : ContDiffOn ℝ (k - 1 : ℕ) (deriv f) (Set.Icc n (n + x)))
    (hderiv : ∀ ξ ∈ Set.Ioo n (n + x),
      ‖iteratedDeriv k f ξ‖ ≤ A * lambda) :
    ‖deriv f (n + x) - heathBrownTaylorDerivativePolynomial k f n x‖ ≤
      A * lambda * x ^ (k - 1) / (k - 1).factorial := by
  rw [← taylorWithinEval_deriv_eq_heathBrownTaylorDerivativePolynomial
    hk hx hfat]
  exact norm_heathBrown_deriv_taylor_remainder_le hk hx hfon hderiv

/-- The derivative of `g_n` has the uniform source bound on `0 < x ≤ H`. -/
theorem norm_deriv_heathBrownTaylorError_le_scale
    {k : ℕ} (hk : 2 ≤ k) {f : ℝ → ℝ} {n x A lambda H : ℝ}
    (hx : 0 < x) (hxH : x ≤ H)
    (hfd : HasDerivAt f (deriv f (n + x)) (n + x))
    (hfat : ContDiffAt ℝ (k - 2 : ℕ) (deriv f) n)
    (hfon : ContDiffOn ℝ (k - 1 : ℕ) (deriv f) (Set.Icc n (n + x)))
    (hderiv : ∀ ξ ∈ Set.Ioo n (n + x),
      ‖iteratedDeriv k f ξ‖ ≤ A * lambda) :
    ‖deriv (fun y => heathBrownTaylorError k f n y) x‖ ≤
      A * lambda * H ^ (k - 1) := by
  rw [deriv_heathBrownTaylorError hk hfd]
  rw [← taylorWithinEval_deriv_eq_heathBrownTaylorDerivativePolynomial
    hk hx hfat]
  exact norm_heathBrown_deriv_taylor_remainder_le_scale
    hk hx hxH hfon hderiv

#print axioms hasDerivAt_heathBrownTaylorPolynomial
#print axioms hasDerivAt_heathBrownTaylorError
#print axioms deriv_heathBrownTaylorError
#print axioms norm_heathBrownTaylorError_derivative_le
#print axioms norm_deriv_heathBrownTaylorError_le_scale

end

end GafniTao
