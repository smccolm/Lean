import GafniTao.SharpPerronContour
import GafniTao.SharpPerronResidueProduct

/-!
# Exact local residues of the sharp zeta Perron integrand

The zeta logarithmic derivative is written using the entire surrogate.  The
two summands below retain the genuine sign and isolate the pole at one:

`-ζ'/ζ · y^s/s = -(F'/F) · y^s/s + y^s/(s(s-1))`,

where `F(s)=(s-1)ζ(s)` with the removable point patched at `s=1`.
-/

open Complex Filter Set Topology Asymptotics
open RiemannZeta.GuthMaynard

noncomputable section

namespace GafniTao

/-- The monomial factor in Perron's formula. -/
noncomputable def sharpPerronMonomial (y : ℝ) (s : ℂ) : ℂ :=
  (y : ℂ) ^ s / s

/-- The entire-surrogate logarithmic-derivative part. -/
noncomputable def sharpSurrogateLogPerron (y : ℝ) (s : ℂ) : ℂ :=
  -(sharpPerronMonomial y s) * logDeriv sharpZetaSurrogate s

/-- The rational correction that restores `-ζ'/ζ`. -/
noncomputable def sharpPerronPoleCorrection (y : ℝ) (s : ℂ) : ℂ :=
  sharpPerronMonomial y s / (s - 1)

/-- The full surrogate presentation of the sharp zeta Perron integrand. -/
noncomputable def sharpZetaPerronIntegrand (y : ℝ) (s : ℂ) : ℂ :=
  sharpSurrogateLogPerron y s + sharpPerronPoleCorrection y s

/-- Away from the zeta pole and zeros, the surrogate logarithmic derivative
is `1/(s-1) + ζ'/ζ`. -/
theorem logDeriv_sharpZetaSurrogate_eq
    {s : ℂ} (hs1 : s ≠ 1) (hzeta : riemannZeta s ≠ 0) :
    logDeriv sharpZetaSurrogate s =
      1 / (s - 1) + logDeriv riemannZeta s := by
  let P : ℂ → ℂ := fun w => (w - 1) * riemannZeta w
  have heq : sharpZetaSurrogate =ᶠ[𝓝 s] P := by
    simpa [P] using sharpZetaSurrogate_eventuallyEq hs1
  have hlogeq : logDeriv sharpZetaSurrogate s = logDeriv P s := by
    simp only [logDeriv_apply]
    rw [heq.deriv_eq, heq.self_of_nhds]
  have hlin : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hmul := logDeriv_mul (f := fun w : ℂ => w - 1)
    (g := riemannZeta) s hlin hzeta
    (differentiableAt_id.sub (differentiableAt_const (c := (1 : ℂ))))
    (differentiableAt_riemannZeta hs1)
  have hlinLog : logDeriv (fun w : ℂ => w - 1) s = 1 / (s - 1) := by
    rw [logDeriv_apply]
    have hderiv : deriv (fun w : ℂ => w - 1) s = 1 := by
      exact ((hasDerivAt_id s).sub_const (1 : ℂ)).deriv
    rw [hderiv]
  rw [hlogeq, hmul, hlinLog]

/-- The surrogate presentation is literally the classical sharp Perron
integrand wherever the logarithmic derivative is regular. -/
theorem sharpZetaPerronIntegrand_eq
    {y : ℝ} {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hzeta : riemannZeta s ≠ 0) :
    sharpZetaPerronIntegrand y s =
      -(logDeriv riemannZeta s) * ((y : ℂ) ^ s / s) := by
  rw [sharpZetaPerronIntegrand, sharpSurrogateLogPerron,
    sharpPerronPoleCorrection, sharpPerronMonomial,
    logDeriv_sharpZetaSurrogate_eq hs1 hzeta]
  field_simp [hs0, sub_ne_zero.mpr hs1]
  ring

theorem differentiableAt_sharpPerronMonomial
    {y : ℝ} (hy : 0 < y) {s : ℂ} (hs : s ≠ 0) :
    DifferentiableAt ℂ (sharpPerronMonomial y) s := by
  have hy0 : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  unfold sharpPerronMonomial
  exact (differentiableAt_fun_id.const_cpow (.inl hy0)).div
    differentiableAt_id hs

theorem differentiableAt_logDeriv_sharpZetaSurrogate
    {s : ℂ} (hs : sharpZetaSurrogate s ≠ 0) :
    DifferentiableAt ℂ (logDeriv sharpZetaSurrogate) s := by
  have ha : AnalyticAt ℂ sharpZetaSurrogate s :=
    sharpZetaSurrogate_analytic s (by simp)
  simpa only [logDeriv_apply] using
    ha.deriv.differentiableAt.div ha.differentiableAt hs

/-- At a zeta zero, the surrogate part has residue
`-m(ρ)y^ρ/ρ`, with the exact analytic multiplicity. -/
theorem sharpSurrogateLogPerron_near_zero
    {y : ℝ} (hy : 0 < y) {rho : ℂ} (hrho : riemannZeta rho = 0) :
    (sharpSurrogateLogPerron y - fun s =>
        (-(analyticVanishingOrder riemannZeta rho : ℂ) *
          sharpPerronMonomial y rho) / (s - rho))
      =O[𝓝[≠] rho] (1 : ℂ → ℂ) := by
  have hrho0 : rho ≠ 0 := by
    intro h
    subst rho
    rw [riemannZeta_zero] at hrho
    norm_num at hrho
  have hrho1 : rho ≠ 1 := by
    intro h
    subst rho
    exact riemannZeta_one_ne_zero hrho
  let m : ℤ := analyticVanishingOrder riemannZeta rho
  have hord : meromorphicOrderAt sharpZetaSurrogate rho =
      (m : WithTop ℤ) := by
    simpa [m] using
      meromorphicOrderAt_sharpZetaSurrogate_eq_multiplicity hrho1
  have hweight : DifferentiableAt ℂ
      (fun s => -(sharpPerronMonomial y s)) rho :=
    (differentiableAt_sharpPerronMonomial hy hrho0).neg
  have hlocal := weightedLogDeriv_sub_principal_isBigO_one
    (sharpZetaSurrogate_analytic rho (by simp)).meromorphicAt hord hweight
  refine hlocal.congr' ?_ EventuallyEq.rfl
  filter_upwards with s
  simp only [sharpSurrogateLogPerron, Pi.sub_apply]
  dsimp [m]
  push_cast
  ring

/-- The origin residue of the surrogate logarithmic-derivative part is the
literal value `-F'/F(0)`. -/
theorem sharpSurrogateLogPerron_near_origin
    {y : ℝ} (hy : 0 < y) :
    (sharpSurrogateLogPerron y - fun s =>
        (-logDeriv sharpZetaSurrogate 0) / (s - 0))
      =O[𝓝[≠] (0 : ℂ)] (1 : ℂ → ℂ) := by
  have hmono :
      (sharpPerronMonomial y - fun s : ℂ => 1 / (s - 0))
        =O[𝓝[≠] (0 : ℂ)] (1 : ℂ → ℂ) := by
    simpa [sharpPerronMonomial] using sharpPerronMonomial_near_zero hy
  have hlog : DifferentiableAt ℂ
      (fun s => -logDeriv sharpZetaSurrogate s) 0 :=
    (differentiableAt_logDeriv_sharpZetaSurrogate (by norm_num)).neg
  have hlocal := mul_sub_principal_isBigO_one hmono hlog
  refine hlocal.congr' ?_ ?_
  · filter_upwards with s
    simp only [sharpSurrogateLogPerron, Pi.sub_apply]
    ring
  · filter_upwards with s
    simp

/-- The rational correction has residue `-1` at the origin. -/
theorem sharpPerronPoleCorrection_near_origin
    {y : ℝ} (hy : 0 < y) :
    (sharpPerronPoleCorrection y - fun s => (-1 : ℂ) / (s - 0))
      =O[𝓝[≠] (0 : ℂ)] (1 : ℂ → ℂ) := by
  have hmono :
      (sharpPerronMonomial y - fun s : ℂ => 1 / (s - 0))
        =O[𝓝[≠] (0 : ℂ)] (1 : ℂ → ℂ) := by
    simpa [sharpPerronMonomial] using sharpPerronMonomial_near_zero hy
  have hfactor : DifferentiableAt ℂ (fun s : ℂ => 1 / (s - 1)) 0 := by
    exact (differentiableAt_const (c := (1 : ℂ))).div
      (differentiableAt_id.sub
        (differentiableAt_const (c := (1 : ℂ)))) (by norm_num)
  have hlocal := mul_sub_principal_isBigO_one hmono hfactor
  refine hlocal.congr' ?_ ?_
  · filter_upwards with s
    simp only [sharpPerronPoleCorrection, sharpPerronMonomial, Pi.sub_apply]
    ring
  · filter_upwards with s
    simp

/-- The rational correction has residue `y` at the zeta pole `s=1`. -/
theorem sharpPerronPoleCorrection_near_one
    {y : ℝ} (hy : 0 < y) :
    (sharpPerronPoleCorrection y - fun s => (y : ℂ) / (s - 1))
      =O[𝓝[≠] (1 : ℂ)] (1 : ℂ → ℂ) := by
  have hweight := differentiableAt_sharpPerronMonomial hy
    (by norm_num : (1 : ℂ) ≠ 0)
  have hprincipal :
      ((fun s : ℂ => 1 / (s - 1)) - fun s => (1 : ℂ) / (s - 1))
        =O[𝓝[≠] (1 : ℂ)] (1 : ℂ → ℂ) := by
    simpa using (isBigO_zero (1 : ℂ → ℂ) (𝓝[≠] (1 : ℂ)))
  have hlocal := mul_sub_principal_isBigO_one hprincipal hweight
  have hone : sharpPerronMonomial y 1 = (y : ℂ) := by
    simp [sharpPerronMonomial]
  simpa [sharpPerronPoleCorrection, Pi.sub_apply, hone, mul_comm,
    mul_left_comm, mul_assoc] using hlocal

end GafniTao
