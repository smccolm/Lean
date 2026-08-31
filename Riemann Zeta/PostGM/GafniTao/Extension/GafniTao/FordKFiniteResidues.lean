import GafniTao.FordLeftLineIntegral
import GafniTao.SharpPerronRectangle

/-!
# Finite residues in Ford's `K(s)` contour

Ford's logarithmic-derivative integrand is represented with the entire
surrogate `(w - 1) ζ(w)`.  This separates the pole at one from the actual
multiplicity-weighted nontrivial-zero residues before any infinite-height
limit is taken.
-/

open Complex Filter Set Topology Asymptotics
open RiemannZeta.GuthMaynard

namespace GafniTao

noncomputable section

/-- Surrogate presentation of Ford's `K(s)` contour integrand. -/
noncomputable def fordKSurrogateIntegrand
    (s : ℂ) (F₀ : ℂ → ℂ) (w : ℂ) : ℂ :=
  (-F₀ (s - w)) * logDeriv sharpZetaSurrogate w +
    F₀ (s - w) / (w - 1)

/-- Away from the pole and zeros, the surrogate presentation is literally
`-ζ'/ζ(w) F₀(s-w)`. -/
theorem fordKSurrogateIntegrand_eq
    {s w : ℂ} {F₀ : ℂ → ℂ}
    (hw1 : w ≠ 1) (hzeta : riemannZeta w ≠ 0) :
    fordKSurrogateIntegrand s F₀ w =
      -(logDeriv riemannZeta w) * F₀ (s - w) := by
  rw [fordKSurrogateIntegrand,
    logDeriv_sharpZetaSurrogate_eq hw1 hzeta]
  field_simp [sub_ne_zero.mpr hw1]
  ring

private theorem differentiableAt_fordKWeight
    {s p : ℂ} {F₀ : ℂ → ℂ}
    (hF₀ : DifferentiableAt ℂ F₀ (s - p)) :
    DifferentiableAt ℂ (fun w => F₀ (s - w)) p := by
  exact hF₀.comp p (by fun_prop)

/-- Away from the pole at one and the zeros of the entire surrogate, Ford's
finite contour integrand is differentiable. -/
theorem differentiableAt_fordKSurrogateIntegrand
    {s w : ℂ} {F₀ : ℂ → ℂ}
    (hF₀ : DifferentiableAt ℂ F₀ (s - w))
    (hw1 : w ≠ 1) (hsur : sharpZetaSurrogate w ≠ 0) :
    DifferentiableAt ℂ (fordKSurrogateIntegrand s F₀) w := by
  have hweight : DifferentiableAt ℂ (fun q => F₀ (s - q)) w :=
    differentiableAt_fordKWeight hF₀
  have hlog : DifferentiableAt ℂ (logDeriv sharpZetaSurrogate) w :=
    differentiableAt_logDeriv_sharpZetaSurrogate hsur
  unfold fordKSurrogateIntegrand
  exact (hweight.neg.mul hlog).add
    (hweight.div (by fun_prop) (sub_ne_zero.mpr hw1))

/-- At a genuine zeta zero, Ford's finite contour has coefficient
`-m(ρ) F₀(s-ρ)`, including analytic multiplicity. -/
theorem fordKSurrogateIntegrand_near_zero
    {s rho : ℂ} {F₀ : ℂ → ℂ}
    (hrho : riemannZeta rho = 0)
    (hF₀ : DifferentiableAt ℂ F₀ (s - rho)) :
    (fordKSurrogateIntegrand s F₀ - fun w =>
        (-(analyticVanishingOrder riemannZeta rho : ℂ) *
          F₀ (s - rho)) / (w - rho))
      =O[𝓝[≠] rho] (1 : ℂ → ℂ) := by
  have hrho1 : rho ≠ 1 := by
    intro h
    subst rho
    exact riemannZeta_one_ne_zero hrho
  let m : ℤ := analyticVanishingOrder riemannZeta rho
  have hord : meromorphicOrderAt sharpZetaSurrogate rho =
      (m : WithTop ℤ) := by
    simpa [m] using
      meromorphicOrderAt_sharpZetaSurrogate_eq_multiplicity hrho1
  have hweight : DifferentiableAt ℂ (fun w => -F₀ (s - w)) rho :=
    (differentiableAt_fordKWeight hF₀).neg
  have hlog := weightedLogDeriv_sub_principal_isBigO_one
    (sharpZetaSurrogate_analytic rho (by simp)).meromorphicAt hord hweight
  have hcorrDiff : DifferentiableAt ℂ
      (fun w => F₀ (s - w) / (w - 1)) rho :=
    (differentiableAt_fordKWeight hF₀).div (by fun_prop)
      (sub_ne_zero.mpr hrho1)
  have hcorr : (fun w => F₀ (s - w) / (w - 1))
      =O[𝓝[≠] rho] (1 : ℂ → ℂ) :=
    (hcorrDiff.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).isBigO_one ℂ
  have hsum := hlog.add hcorr
  refine hsum.congr' ?_ EventuallyEq.rfl
  filter_upwards with w
  simp only [fordKSurrogateIntegrand, Pi.sub_apply]
  dsimp [m]
  push_cast
  ring

/-- At the zeta pole, Ford's finite contour has coefficient `F₀(s-1)`. -/
theorem fordKSurrogateIntegrand_near_one
    {s : ℂ} {F₀ : ℂ → ℂ}
    (hF₀ : DifferentiableAt ℂ F₀ (s - 1)) :
    (fordKSurrogateIntegrand s F₀ - fun w =>
        F₀ (s - 1) / (w - 1))
      =O[𝓝[≠] (1 : ℂ)] (1 : ℂ → ℂ) := by
  have hweight := differentiableAt_fordKWeight hF₀
  have hprincipal :
      ((fun w : ℂ => 1 / (w - 1)) -
          fun w => (1 : ℂ) / (w - 1))
        =O[𝓝[≠] (1 : ℂ)] (1 : ℂ → ℂ) := by
    simpa using (isBigO_zero (1 : ℂ → ℂ) (𝓝[≠] (1 : ℂ)))
  have hcorr := mul_sub_principal_isBigO_one hprincipal hweight
  have hsurNonzero : sharpZetaSurrogate 1 ≠ 0 := by norm_num
  have hfirstDiff : DifferentiableAt ℂ
      (fun w => (-F₀ (s - w)) * logDeriv sharpZetaSurrogate w) 1 :=
    hweight.neg.mul (differentiableAt_logDeriv_sharpZetaSurrogate hsurNonzero)
  have hfirst : (fun w =>
      (-F₀ (s - w)) * logDeriv sharpZetaSurrogate w)
      =O[𝓝[≠] (1 : ℂ)] (1 : ℂ → ℂ) :=
    (hfirstDiff.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).isBigO_one ℂ
  have hsum := hfirst.add hcorr
  refine hsum.congr' ?_ EventuallyEq.rfl
  filter_upwards with w
  simp only [fordKSurrogateIntegrand, Pi.sub_apply]
  ring

end

end GafniTao
