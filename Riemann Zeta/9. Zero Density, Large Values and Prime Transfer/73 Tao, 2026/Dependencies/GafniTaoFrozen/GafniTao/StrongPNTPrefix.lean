/-
Copyright (c) 2024 Mathlib Initiative. All rights reserved.
Released under Apache 2.0 license.
Adapted from PrimeNumberTheoremAnd/StrongPNT.lean at revision
4ecb950126c4290293c5662dfe0e884123171df5. Only the proved analytic prefix
through FinalBound is retained; the monolithic source's later provisional
sections are deliberately not imported.
-/
import Architect
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Data.Rat.Cast.OfScientific
import Mathlib.Data.Real.StarOrdered
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Normed.Module.Connected

namespace GafniTao

open Nat Filter Set Function Complex Real ComplexConjugate MeasureTheory

@[blueprint "AnalyticOn.norm_le_of_norm_le_on_sphere"
  (title := "AnalyticOn.norm-le-of-norm-le-on-sphere")
  (statement := /--
    An application of the Maximum modulus principle.
  -/)
  (proof := /--
    This is standard in the literature.
  -/)
  (latexEnv := "lemma")]
lemma AnalyticOn.norm_le_of_norm_le_on_sphere {C r R : ℝ} {f : ℂ → ℂ} {w c : ℂ}
    (hyp_r : r ≤ R)
    (analytic : AnalyticOn ℂ f (Metric.closedBall c R))
    (cond : ∀ z ∈ Metric.sphere c r, ‖f z‖ ≤ C)
    (wInS : w ∈ Metric.closedBall c r) :
    ‖f w‖ ≤ C := by
  apply Complex.norm_le_of_forall_mem_frontier_norm_le
    (U := Metric.closedBall c r) Metric.isBounded_closedBall
  · apply DifferentiableOn.diffContOnCl
    rw [Metric.closure_closedBall]
    exact AnalyticOn.differentiableOn
      (AnalyticOn.mono analytic
        (Metric.closedBall_subset_closedBall hyp_r))
  · rw [frontier_closedBall']
    exact cond
  · rw [Metric.closure_closedBall]
    exact wInS



@[blueprint "borelCaratheodory'"
  (title := "borelCaratheodory'")
  (statement := /--
    An application of
    \begin{verbatim}
      Complex.borelCaratheodory_zero.
    \end{verbatim}
  -/)
  (proof := /--
    This is standard in the literature.
  -/)
  (latexEnv := "theorem")]
theorem borelCaratheodory' {M r R : ℝ} {f : ℂ → ℂ} {z : ℂ}
    (Mpos : 0 < M) (Rpos : 0 < R) (hyp_r : r < R)
    (analytic : AnalyticOn ℂ f (Metric.ball 0 R))
    (zeroAtZero : f 0 = 0)
    (realPartBounded : ∀ z ∈ Metric.ball 0 R, (f z).re ≤ M)
    (hyp_z : z ∈ Metric.closedBall 0 r) :
    ‖f z‖ ≤ (2 * M * r) / (R - r) := by
  have h_borelCaratheodory : ∀ ε > 0, ‖f z‖ ≤ (2 * (M + ε) * ‖z‖) / (R - ‖z‖) := by
    intro ε εpos;
    apply Complex.borelCaratheodory_zero;
    exacts [by linarith, analytic.differentiableOn, fun z hz => by rw [Set.mem_setOf_eq]; linarith [realPartBounded z hz], Rpos, by exact Metric.mem_ball.mpr ( lt_of_le_of_lt ( Metric.mem_closedBall.mp hyp_z ) hyp_r ), zeroAtZero]
  have h_limit : ‖f z‖ ≤ (2 * M * ‖z‖) / (R - ‖z‖) := by
    have h_limit : Filter.Tendsto (fun ε => (2 * (M + ε) * ‖z‖) / (R - ‖z‖)) (nhdsWithin 0 (Set.Ioi 0)) (nhds ((2 * M * ‖z‖) / (R - ‖z‖))) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds (Continuous.tendsto' ?_ _ _ (by ring_nf))
      exact ((continuous_const.mul (continuous_const.add continuous_id)).mul continuous_const).div_const _
    exact le_of_tendsto_of_tendsto tendsto_const_nhds h_limit ( Filter.eventually_of_mem self_mem_nhdsWithin fun ε hε => h_borelCaratheodory ε hε );
  rw [mem_closedBall_iff_norm, sub_zero] at hyp_z
  refine le_trans h_limit ?_;
  gcongr
  · exact mul_nonneg (mul_nonneg (zero_le_two) (le_of_lt Mpos)) (le_trans (norm_nonneg z) hyp_z)



blueprint_comment /--
    This upstreamed from https://github.com/math-inc/strongpnt/tree/main
-/



@[blueprint "cauchy_formula_deriv"
  (title := "cauchy-formula-deriv")
  (statement := /--
    Let $f$ be analytic on $|z|\leq R$. For any $z$ with $|z|\leq r$ and any $r'$
    with $0 < r < r' < R$ we have
    $$f'(z)=\frac{1}{2\pi i}\oint_{|w|=r'}\frac{f(w)}{(w-z)^2}\,dw=\frac{1}{2\pi}
    \int_0^{2\pi}\frac{r'e^{it}\,f(r'e^{it})}{(r'e^{it}-z)^2}\,dt.$$
  -/)
  (proof := /--
    This is just Cauchy's integral formula for derivatives.
  -/)
  (latexEnv := "lemma")]
lemma cauchy_formula_deriv {r r' R : ℝ} {f : ℂ → ℂ} {z : ℂ}
    (r_lt_r' : r < r') (r'_lt_R : r' < R)
    (hf_on_ball : DifferentiableOn ℂ f (Metric.ball 0 R))
    (hz : z ∈ Metric.closedBall 0 r) :
    deriv f z = (1 / (2 * Real.pi * I)) • ∮ w in C(0, r'), (w - z)⁻¹ ^ 2 • f w := by
  have hz_in_ball : z ∈ Metric.ball 0 r' :=
    Metric.mem_ball.mpr <| (Metric.mem_closedBall.mp hz).trans_lt r_lt_r'
  simp [← Complex.two_pi_I_inv_smul_circleIntegral_sub_sq_inv_smul_of_differentiable
      Metric.isOpen_ball (Metric.closedBall_subset_ball r'_lt_R) hf_on_ball hz_in_ball]



@[blueprint "DerivativeBound"
  (title := "DerivativeBound")
  (statement := /--
    Let $R,\,M>0$ and $0 < r < r' < R$. Let $f$ be analytic on $|z|\leq R$ such that
    $f(0)=0$ and suppose $\Re f(z)\leq M$ for all $|z|\leq R$. Then we have that
    $$|f'(z)|\leq\frac{2M(r')^2}{(R-r')(r'-r)^2}$$
    for all $|z|\leq r$.
  -/)
  (proof := /--
    By Lemma \ref{cauchy_formula_deriv} we know that
    $$f'(z)=\frac{1}{2\pi i}\oint_{|w|=r'}\frac{f(w)}{(w-z)^2}\,dw
      =\frac{1}{2\pi }\int_0^{2\pi}\frac{r'e^{it}\,f(r'e^{it})}{(r'e^{it}-z)^2}\,dt.$$
    Thus,
    \begin{equation}\label{pickupPoint1}
        |f'(z)|=\left|\frac{1}{2\pi}\int_0^{2\pi}
          \frac{r'e^{it}\,f(r'e^{it})}{(r'e^{it}-z)^2}\,dt\right|
          \leq\frac{1}{2\pi}\int_0^{2\pi}
          \left|\frac{r'e^{it}\,f(r'e^{it})}{(r'e^{it}-z)^2}\right|\,dt.
    \end{equation}
    Now applying Theorem \ref{borelCaratheodory-closedBall}, and noting that
    $r'-r\leq|r'e^{it}-z|$, we have that
    $$\left|\frac{r'e^{it}\,f(r'e^{it})}{(r'e^{it}-z)^2}\right|
      \leq\frac{2M(r')^2}{(R-r')(r'-r)^2}.$$
    Substituting this into Equation (\ref{pickupPoint1}) and evaluating the integral
    completes the proof.
  -/)
  (latexEnv := "lemma")]
lemma DerivativeBound {M r r' R : ℝ} {f : ℂ → ℂ} {z : ℂ}
    (Mpos : 0 < M) (pos_r : 0 < r) (r_lt_r' : r < r') (r'_lt_R : r' < R)
    (analytic_f : AnalyticOn ℂ f (Metric.ball 0 R))
    (f_zero_at_zero : f 0 = 0)
    (re_f_le_M : ∀ z ∈ Metric.ball 0 R, (f z).re ≤ M)
    (z_in_r : z ∈ Metric.closedBall 0 r) :
    ‖(deriv f) z‖ ≤ 2 * M * (r') ^ 2 / ((R - r') * (r' - r) ^ 2) := by
  rw [cauchy_formula_deriv r_lt_r' r'_lt_R analytic_f.differentiableOn  z_in_r, one_div]
  grw [circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const (by linarith) (C := 2 * M * r' / ((R - r') * (r' - r) ^ 2))]
  · exact le_of_eq (by ring)
  · intro z' hz'
    rw [smul_eq_mul, norm_mul]
    grw[borelCaratheodory' Mpos (by grind) r'_lt_R analytic_f f_zero_at_zero  re_f_le_M
      (Metric.sphere_subset_closedBall hz')]
    suffices ‖(z' - z)⁻¹ ^ 2‖ ≤ 1 / (r' - r) ^ 2 by
      grw [this]
      · exact le_of_eq (by field)
      · refine mul_nonneg (mul_nonneg ?_ ?_) (inv_nonneg.mpr ?_) <;> linarith
    have hdist : r' - r ≤ ‖z' - z‖ := by
      simp only [mem_sphere_iff_norm, sub_zero, Metric.mem_closedBall,
        dist_zero_right] at hz' z_in_r
      rw [← hz']
      exact le_trans (by linarith) (norm_sub_norm_le z' z)
    rw [norm_pow, norm_inv, one_div, inv_pow]
    gcongr



@[blueprint "BorelCaratheodoryDeriv"
  (title := "BorelCaratheodoryDeriv")
  (statement := /--
    Let $R,\,M>0$. Let $f$ be analytic on $|z|\leq R$ such that $f(0)=0$ and suppose
    $\Re f(z)\leq M$ for all $|z|\leq R$. Then for any $0 < r < R$,
    $$|f'(z)|\leq\frac{16MR^2}{(R-r)^3}$$
    for all $|z|\leq r$.
  -/)
  (proof := /--
    Using Lemma \ref{DerivativeBound} with $r'=(R+r)/2$, and noting that $r < R$,
    we have that
    $$|f'(z)|\leq\frac{4M(R+r)^2}{(R-r)^3}\leq\frac{16MR^2}{(R-r)^3}.$$
  -/)
  (latexEnv := "theorem")]
theorem BorelCaratheodoryDeriv {M r R : ℝ} {f : ℂ → ℂ} {z : ℂ}
    (Mpos : 0 < M) (rpos : 0 < r) (hyp_r : r < R)
    (analytic_f : AnalyticOn ℂ f (Metric.ball 0 R))
    (zeroAtZero : f 0 = 0)
    (realPartBounded : ∀ z ∈ Metric.ball 0 R, (f z).re ≤ M)
    (hyp_z : z ∈ Metric.closedBall 0 r) :
    ‖deriv f z‖ ≤ 16 * M * R ^ 2 / (R - r) ^ 3 := by
  have hr' : 2 * M * ((R + r) / 2) ^ 2 / ((R - (R + r) / 2) * ((R + r) / 2 - r) ^ 2) =
      4 * M * (R + r) ^ 2 / (R - r) ^ 3 := by field_simp; ring
  calc ‖deriv f z‖
      _ ≤ 4 * M * (R + r) ^ 2 / (R - r) ^ 3 := hr' ▸
          DerivativeBound Mpos rpos (by linarith) (by linarith) analytic_f zeroAtZero realPartBounded hyp_z
      _ ≤ 16 * M * R ^ 2 / (R - r) ^ 3 := by
          have : 16 * M * R ^ 2 = 4 * M * (2 * R) ^ 2 := by ring_nf
          rw [this]; bound



blueprint_comment /--
\begin{definition}[TaxicabIntegral]\label{TaxicabIntegral}
  Let $0 < R$. Let $f:\overline{\mathbb{D}_R}\to\mathbb{C}$ be analytic on neighborhoods of points
  in $\overline{\mathbb{D}_R}$. Define the functon $I_f:\mathbb{D}_R\to\mathbb{C}$ by
    $$I_f(z)=z\int_0^1f(tz)\,dt.$$
\end{definition}
-/



@[blueprint "LogOfAnalyticFunction"
  (title := "LogOfAnalyticFunction")
  (statement := /--
    Let $0<r<R$. Let $B:\overline{\mathbb{D}_{R}}\to\mathbb{C}$ be analytic on neighborhoods of
    points in $\overline{\mathbb{D}_{R}}$ with $B(z)\neq 0$ for all
    $z\in\overline{\mathbb{D}_{R}}$.Then there exists $J_B:\mathbb{D}_R\to\mathbb{C}$ that is
    analytic on neighborhoods of points in $\mathbb{D}_R$ such that
    \begin{itemize}
        \item $J_B(0)=0$
        \item $J_B'(z)=B'(z)/B(z)$ for all $z\in\overline{\mathbb{D}_r}$
        \item $\log|B(z)|-\log|B(0)|=\mathfrak{R}J_B(z)$ for all $z\in\mathbb{D}_R$.
    \end{itemize}
  -/)
  (proof := /--
    We let $J_B(z)=I_{B'/B}(z)$. Then clearly, $J_B(0)=0$. Now note that
    \begin{align*}
        I_{B'/B}(z)=z\int_0^1(B'/B)(tz)\,dt=\int_0^z(B'/B)(u)\,du.
    \end{align*}
    Thus by the fundamental theorem of calculus we have that $J_B'(z)=B'(z)/B(z)$. Now let
    $H(z)=\exp(J_B(z))/B(z)$ and note that
    $$H'(z)=(B(z)\,J_B'(z)-B'(z))\left(\frac{\exp(J_B(z))}{(B(z))^2}\right).$$
    Thus, $H$ is constant since we know that $B(z)\,J_B'(z)-B(z)=0$ from $J_B'(z)=B'(z)/B(z)$. So
    since $H(0)=\exp(J_B(0))/B(0)=1/B(0)$ we know $H(z)=1/B(0)$ for all $z$. So we have,
    $$\frac{1}{B(0)}=\frac{\exp(J_B(z))}{B(z)}\implies\left|\frac{B(z)}{B(0)}\right|
      =\exp(\mathfrak{R}J_B(z)).$$
    Taking the logarithm of both sides completes the proof.
  -/)
  (latexEnv := "theorem")]
theorem LogOfAnalyticFunction {r R : ℝ} {B : ℂ → ℂ}
    (zero_lt_r : 0 < r) (r_lt_R : r < R)
    (BanalyticOnNhdOfDR : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (Bnonzero : ∀ z ∈ Metric.closedBall (0 : ℂ) R, B z ≠ 0) :
    ∃ (J_B : ℂ → ℂ), (AnalyticOnNhd ℂ J_B (Metric.ball 0 R)) ∧
      (J_B 0 = 0) ∧
      (∀ z ∈ Metric.closedBall 0 r, (deriv J_B) z = (deriv B) z / (B z)) ∧
      (∀ z ∈ Metric.ball 0 R, Real.log ‖B z‖ - Real.log ‖B 0‖ = (J_B z).re) := by
  obtain ⟨J_B, hJB⟩ : ∃ J_B : ℂ → ℂ, (∀ z ∈ Metric.ball 0 R, (HasDerivAt J_B (deriv B z / B z) z)) ∧ J_B 0 = 0 ∧ (∀ z ∈ Metric.ball 0 R, Real.log ‖B z‖ - Real.log ‖B 0‖ = (J_B z).re) := by
    set f : ℂ → ℂ := fun z => deriv B z / B z;
    have hf : AnalyticOnNhd ℂ f (Metric.ball 0 R) :=
      (BanalyticOnNhdOfDR.deriv.mono Metric.ball_subset_closedBall).div
        (BanalyticOnNhdOfDR.mono Metric.ball_subset_closedBall)
        (fun z hz => Bnonzero z <| Metric.ball_subset_closedBall hz)
    obtain ⟨J, hJ⟩ := DifferentiableOn.isExactOn_ball hf.differentiableOn
    refine ⟨fun z ↦ J z - J 0, fun z hz ↦ (hJ z hz).sub_const _, by simp, ?_⟩
    set H : ℂ → ℂ := fun z => Complex.exp (J z - J 0) / B z
    have hJB_deriv : ∀ z ∈ Metric.ball 0 R, HasDerivAt (fun z ↦ J z - J 0) (f z) z :=
      fun z hz ↦ (hJ z hz).sub_const _
    have hH_deriv : ∀ z ∈ Metric.ball 0 R, HasDerivAt H 0 z := by
      intro z hz
      have := (Complex.hasDerivAt_exp _).comp z (hJB_deriv z hz)
      convert this.div (BanalyticOnNhdOfDR.differentiableOn.differentiableAt
        (Metric.closedBall_mem_nhds_of_mem hz) |>.hasDerivAt)
        (Bnonzero z <| Metric.ball_subset_closedBall hz) using 1
      ring_nf!; grind
    have hH_const : ∀ z ∈ Metric.ball 0 R, H z = H 0 := by
      intro z hz
      have h_diffOn : DifferentiableOn ℂ H (Metric.ball 0 R) :=
        fun z hz ↦ (hH_deriv z hz).differentiableAt.differentiableWithinAt
      refine Convex.is_const_of_fderivWithin_eq_zero (convex_ball 0 R) h_diffOn ?_ hz
        (Metric.mem_ball_self (Metric.pos_of_mem_ball hz))
      intro x hx
      rw [fderivWithin_of_isOpen Metric.isOpen_ball hx,
        ← ContinuousLinearMap.toSpanSingleton_zero]
      exact (hH_deriv x hx).hasFDerivAt.fderiv
    have h_exp_re : ∀ z ∈ Metric.ball 0 R, Real.exp (J z - J 0).re = ‖B z‖ / ‖B 0‖ := by
      intro z hz
      have hc := hH_const z hz
      simp only [H, sub_self, Complex.exp_zero, one_div] at hc
      rw [div_eq_iff (Bnonzero z (Metric.ball_subset_closedBall hz)), mul_comm] at hc
      rw [← Complex.norm_exp, ← norm_div, div_eq_mul_inv]
      exact enorm_eq_iff_norm_eq.mp (congrArg enorm hc)
    intro z hz
    have hBz := Bnonzero z (Metric.ball_subset_closedBall hz)
    have hB0 := Bnonzero 0 (by norm_num; linarith)
    rw [← Real.log_div (norm_ne_zero_iff.mpr hBz) (norm_ne_zero_iff.mpr hB0),
      ← h_exp_re z hz, Real.log_exp]
  have hmem : ∀ z, z ∈ Metric.ball (0 : ℂ) r → z ∈ Metric.closedBall (0 : ℂ) R := by
    intro z hz
    apply Metric.mem_closedBall.mpr
    rw [Metric.mem_ball] at hz
    linarith
  refine ⟨J_B, ?_, hJB.2.1, ?_, hJB.2.2⟩
  · intro z hz
    exact DifferentiableOn.analyticAt (fun w hw ↦ (hJB.1 w hw).differentiableAt.differentiableWithinAt) (IsOpen.mem_nhds Metric.isOpen_ball hz)
  · intro z hz
    exact (hJB.1 z (Metric.closedBall_subset_ball r_lt_R hz)).deriv



@[blueprint "LogOfAnalyticFunction'"
  (title := "LogOfAnalyticFunction'")
  (statement := /--
    A wrapper of the above theorem that will be useful later on.
  -/)
  (proof := /--
    See above.
  -/)
  (latexEnv := "theorem")]
theorem LogOfAnalyticFunction' {r' r R : ℝ} {B : ℂ → ℂ}
    (r'_pos : 0 < r') (r'_lt_r : r' < r) (r_lt_R : r < R)
    (BanalyticOnNhdOfDR : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (Bnonzero : ∀ z ∈ Metric.closedBall (0 : ℂ) r, B z ≠ 0) :
    ∃ (J_B : ℂ → ℂ), (AnalyticOnNhd ℂ J_B (Metric.ball 0 r)) ∧
      (J_B 0 = 0) ∧
      (∀ z ∈ Metric.closedBall 0 r', (deriv J_B) z = (deriv B) z / (B z)) ∧
      (∀ z ∈ Metric.ball 0 r, Real.log ‖B z‖ - Real.log ‖B 0‖ = (J_B z).re) := by
  have BanalyticOnNhdOfDr : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) r) := BanalyticOnNhdOfDR.mono (Metric.closedBall_subset_closedBall r_lt_R.le)
  exact LogOfAnalyticFunction r'_pos r'_lt_r BanalyticOnNhdOfDr Bnonzero



@[blueprint "SetOfZeros"
  (title := "SetOfZeros")
  (statement := /--
    Let $R>0$ and $f:\mathbb{C}\to\mathbb{C}$. Define the set of zeros
    $\mathcal{K}_f(R)=\{\rho\in\mathbb{C}:|\rho|\leq R,\,f(\rho)=0\}$.
  -/)]
def SetOfZeros (R : ℝ) (f : ℂ → ℂ) : Set ℂ := {ρ : ℂ | ‖ρ‖ ≤ R ∧ f ρ = 0}



lemma finiteSetOfZeros_mono {r : ℝ} {f : ℂ → ℂ}
    (r_lt_one : r < 1)
    (finiteZeros : (SetOfZeros 1 f).Finite) :
    (SetOfZeros r f).Finite := by
  apply Set.Finite.subset finiteZeros
  unfold SetOfZeros
  refine setOf_subset_setOf.mpr ?_
  intro z hz
  exact ⟨by linarith, hz.2⟩



blueprint_comment /--
\begin{definition}[ZeroOrder]\label{ZeroOrder}
  Let $f:\mathbb{C}\to\mathbb{C}$.
  We define $m_f(\rho)$ as the order of the zero $\rho$ w.r.t $f$.
\end{definition}
  In LEAN, this corresponds exactly with analyticOrderAt/analyticOrderNatAt.
-/



open Classical
@[blueprint "ZeroFactor"
  (title := "ZeroFactor")
  (statement := /--
    Let $f:\mathbb{C}\to\mathbb{C}$ and $\rho\in\mathbb{C}$. Then there exists $h_\rho$ such that
    $$f(z)=(z-\rho)^{m_f(\rho)}\,h_\rho(z).$$
    In LEAN, this corresponds exactly with (-.analyticOrderAt-ne-top.mp -).choose,
    but this serves as a wrapper of that with the necessary conditions.
  -/)]
noncomputable def ZeroFactor (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  if h1 : AnalyticAt ℂ f z then
    if h2 : analyticOrderAt f z ≠ ⊤ then
      (h1.analyticOrderAt_ne_top.mp h2).choose z
    else 0
  else 0



@[blueprint "ZeroFactorization"
  (title := "ZeroFactorization")
  (statement := /--
    Let $f:\mathbb{C}\to\mathbb{C}$ be analytic on $\overline{\mathbb{D}_1}$ with $f(0)\neq 0$.
    For all $\rho\in\mathcal{K}_f(R)$ with $R<1$ there exists $h_\rho(z)$ such that
    $h_\rho(z)$ is analytic at $\rho$, $h_\rho(\rho)\neq 0$, and
    $f(z)=(z-\rho)^{m_f(\rho)}\,h_\rho(z)$.
  -/)
  (proof := /--
    Since $f$ is analytic on neighborhoods of points in $\overline{\mathbb{D}_1}$ we know
    that there exists a series expansion about $\rho$:
    $$f(z)=\sum_{0\leq n}a_n\,(z-\rho)^n.$$
    Now if we let $m$ be the smallest number such that $a_m\neq 0$, then
    $$f(z)=\sum_{0\leq n}a_n\,(z-\rho)^n=\sum_{m\leq n}a_n\,(z-\rho)^n
      =(z-\rho)^m\sum_{m\leq n}a_n\,(z-\rho)^{n-m}=(z-\rho)^m\,h_\rho(z).$$
    Trivially, $h_\rho(z)$ is analytic at $\rho$ (we have written down the series
    expansion); now note that
    $$h_\rho(\rho)=\sum_{m\leq n}a_n(\rho-\rho)^{n-m}=\sum_{m\leq n}a_n0^{n-m}=a_m\neq 0.$$
  -/)
  (latexEnv := "lemma")]
lemma ZeroFactorization {R : ℝ} {f : ℂ → ℂ} {ρ : ℂ}
    (RleOne : R < 1)
    (hfAnalytic : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1))
    (hf_neq_zero_at_zero : f 0 ≠ 0)
    (hρ : ρ ∈ SetOfZeros R f) :
    ∃ h_ρ : ℂ → ℂ, AnalyticAt ℂ h_ρ ρ ∧ h_ρ ρ ≠ 0 ∧ ZeroFactor f ρ = h_ρ ρ ∧
      f =ᶠ[nhds ρ] fun z ↦ (z - ρ) ^ analyticOrderNatAt f ρ * h_ρ z := by
  have zero_mem_closedBall : 0 ∈ Metric.closedBall (0 : ℂ) 1 := by
    rw[mem_closedBall_iff_norm, sub_zero, norm_zero]
    exact zero_le_one
  have ρ_mem_closedBall : ρ ∈ Metric.closedBall (0 : ℂ) 1 := by
    rw[mem_closedBall_iff_norm, sub_zero]
    linarith[hρ.1]
  have orderAtZeroIsZero : analyticOrderAt f 0 = 0 := by
    rw[analyticOrderAt_eq_zero]
    exact Or.symm (Decidable.not_or_of_imp fun a a_1 ↦ hf_neq_zero_at_zero a)
  have finiteOrder : analyticOrderAt f ρ ≠ ⊤ := by
    refine AnalyticOnNhd.analyticOrderAt_ne_top_of_isPreconnected hfAnalytic (Metric.isPreconnected_closedBall) zero_mem_closedBall ρ_mem_closedBall (lt_top_iff_ne_top.mp ?_)
    rw[orderAtZeroIsZero]
    exact ENat.top_pos
  have AnalyticAt_ρ : AnalyticAt ℂ f ρ := by exact (hfAnalytic ρ ρ_mem_closedBall)
  obtain ⟨h_ρ, h_ρ_neq_zero_at_zero, f_eq⟩ := (AnalyticAt_ρ.analyticOrderAt_ne_top.mp finiteOrder).choose_spec
  set g := (AnalyticAt_ρ.analyticOrderAt_ne_top.mp finiteOrder).choose
  refine ⟨g, h_ρ, h_ρ_neq_zero_at_zero, ?_, f_eq⟩
  simp only [ZeroFactor, AnalyticAt_ρ, ↓reduceDIte, ne_eq, finiteOrder, not_false_eq_true,
    smul_eq_mul, g]



@[blueprint "CFunction"
  (title := "CFunction")
  (statement := /--
    Let $0 < r < 1$, and $f:\mathbb{C}\to\mathbb{C}$ be analytic on $\overline{\mathbb{D}_1}$ with
    $f(0)\neq 0$. We define a function $C_f:\mathbb{C}\to\mathbb{C}$ as follows. This function is
    constructed by dividing $f(z)$ by a polynomial whose roots are the zeros of $f$ inside
    $\overline{\mathbb{D}_r}$.
    $$C_f(z)=\begin{cases}
        \displaystyle\frac{f(z)}{\prod_{\rho\in\mathcal{K}_f(r)}(z-\rho)^{m_f(\rho)}}
          \qquad\text{for }z\not\in\mathcal{K}_f(r) \\
        \displaystyle\frac{h_z(z)}{\prod_{\rho\in\mathcal{K}_f(r)\setminus\{z\}}
          (z-\rho)^{m_f(\rho)}}\qquad\text{for }z\in\mathcal{K}_f(r)
    \end{cases}$$
    where $h_z(z)$ comes from Lemma \ref{ZeroFactorization}.
  -/)]
noncomputable def Cf (r : ℝ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  if finite_zeros_mono : (SetOfZeros r f).Finite then
    if _ : z ∈ SetOfZeros r f then
      ZeroFactor f z / ∏ ρ ∈ (finite_zeros_mono.toFinset \ {z}), (z - ρ) ^ (analyticOrderNatAt f ρ)
    else
      f z / ∏ ρ ∈ (finite_zeros_mono.toFinset), (z - ρ) ^ (analyticOrderNatAt f ρ)
  else 1



lemma analyticAt_finset_prod_sub_pow (s : Finset ℂ) (g : ℂ → ℕ) (w : ℂ) :
    AnalyticAt ℂ (fun z => ∏ ρ ∈ s, (z - ρ) ^ g ρ) w := by
  induction s using Finset.induction with
  | empty =>
    simp only [Finset.prod_empty]
    exact analyticAt_const
  | @insert a s' hne ih =>
    have : (fun z => ∏ ρ ∈ insert a s', (z - ρ) ^ g ρ) = fun z => (z - a) ^ g a * ∏ ρ ∈ s', (z - ρ) ^ g ρ :=
      funext fun z => Finset.prod_insert hne
    rw [this]
    exact ((analyticAt_id.sub analyticAt_const).pow _).mul ih



@[blueprint "CfAnalytic"
  (title := "CfAnalytic")
  (statement := /--
    If $f:\mathbb{C}\to\mathbb{C}$ is analytic on $\overline{\mathbb{D}_1}$ then so too is $C_f$.
  -/)
  (proof := /--
    Look at the definition of $C_f$ and apply ZeroFactorization.
  -/)
  (latexEnv := "lemma")]
lemma CfAnalytic {r R : ℝ} {f : ℂ → ℂ}
    (r_lt_R : r < R) (R_lt_one : R < 1)
    (hfAnalytic : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1))
    (hf_neq_zero_at_zero : f 0 ≠ 0) :
    AnalyticOnNhd ℂ (Cf r f) (Metric.closedBall (0 : ℂ) R) := by
  intro w hw
  unfold Cf
  by_cases finite_zeros_mono : (SetOfZeros r f).Finite
  · simp only [finite_zeros_mono, ↓reduceDIte]
    by_cases w_in_zeros : w ∈ SetOfZeros r f
    · obtain ⟨h_w, hh_w_analytic, hh_w_w_ne_zero, hh_w_eq⟩ := ZeroFactorization (by linarith) (hfAnalytic.mono (Metric.closedBall_subset_closedBall (by linarith))) hf_neq_zero_at_zero w_in_zeros;
      have h_eq : ∀ᶠ z in nhds w, (if h : z ∈ SetOfZeros r f then ZeroFactor f z / ∏ ρ ∈ finite_zeros_mono.toFinset \ {z}, (z - ρ) ^ analyticOrderNatAt f ρ else f z / ∏ ρ ∈ finite_zeros_mono.toFinset, (z - ρ) ^ analyticOrderNatAt f ρ) = h_w z / ∏ ρ ∈ finite_zeros_mono.toFinset \ {w}, (z - ρ) ^ analyticOrderNatAt f ρ := by
        filter_upwards [ hh_w_eq.2, hh_w_analytic.continuousAt.eventually_ne hh_w_w_ne_zero ] with z hz hz';
        by_cases h : z = w
        · subst h
          rw [dif_pos w_in_zeros]
          congr 1
          exact hh_w_eq.1
        · have z_not_in : z ∉ SetOfZeros r f := by
            intro hmem
            have hfz : f z = 0 := hmem.2
            rw [hz] at hfz
            exact absurd hfz (mul_ne_zero (pow_ne_zero _ (sub_ne_zero_of_ne h)) hz')
          rw [dif_neg z_not_in, hz]
          have hw_mem : w ∈ finite_zeros_mono.toFinset := finite_zeros_mono.mem_toFinset.mpr w_in_zeros
          rw [Finset.prod_eq_prod_diff_singleton_mul hw_mem (fun ρ => (z - ρ) ^ analyticOrderNatAt f ρ)]
          rw [mul_comm ((z - w) ^ analyticOrderNatAt f w) (h_w z)]
          rw [mul_div_mul_right _ _ (pow_ne_zero _ (sub_ne_zero_of_ne h))]
      apply hh_w_analytic.div _ _ |> fun h => h.congr _;
      · use fun z => ∏ ρ ∈ finite_zeros_mono.toFinset \ { w }, ( z - ρ ) ^ analyticOrderNatAt f ρ;
      · exact analyticAt_finset_prod_sub_pow _ _ _
      · simp only [Finset.prod_eq_zero_iff, ne_eq, pow_eq_zero_iff', Finset.mem_sdiff, Finite.mem_toFinset, Finset.mem_singleton, not_exists, not_and,
          Decidable.not_not, and_imp]
        intro x _ h_ne_w
        exact fun h_eq_w => absurd (sub_eq_zero.mp h_eq_w).symm h_ne_w
      · filter_upwards [ h_eq ] with z hz using hz.symm
    · apply AnalyticAt.congr _ _
      · exact fun z => f z / ∏ ρ ∈ finite_zeros_mono.toFinset, ( z - ρ ) ^ analyticOrderNatAt f ρ
      · refine AnalyticAt.div ?_ ?_ ?_
        · exact hfAnalytic w ( Metric.mem_closedBall.mpr <| le_trans hw.out <| by linarith )
        · exact analyticAt_finset_prod_sub_pow _ _ _
        · simp only [ ne_eq, Finset.prod_eq_zero_iff, Finite.mem_toFinset, pow_eq_zero_iff',
          sub_eq_zero, ↓existsAndEq, true_and, not_and, Decidable.not_not]
          exact fun h => absurd h w_in_zeros
      · filter_upwards [ IsOpen.mem_nhds ( isOpen_compl_iff.mpr finite_zeros_mono.isClosed ) w_in_zeros ] with z hz
        split_ifs with h
        · exact absurd h hz
        · rfl
  · simp only [finite_zeros_mono, ↓reduceDIte]
    exact analyticAt_const



@[blueprint "BlaschkeB"
  (title := "BlaschkeB")
  (statement := /--
    Let $0 < r < R < 1$, and $f:\mathbb{C}\to\mathbb{C}$ be analytic $\overline{\mathbb{D}_1}$ with
    $f(0)\neq 0$. We define a function $B_f:\mathbb{C}\to\mathbb{C}$ as follows.
    $$B_f(z)=C_f(z)\prod_{\rho\in\mathcal{K}_f(r)}
      \left(R-\frac{z\overline{\rho}}{R}\right)^{m_f(\rho)}$$
  -/)]
noncomputable def BlaschkeB (r R : ℝ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  if finite_zeros_mono : (SetOfZeros r f).Finite then
    (Cf r f) z * (∏ ρ ∈ finite_zeros_mono.toFinset, (R - z * (conj ρ) / R) ^ (analyticOrderNatAt f ρ))
  else 1



@[blueprint "BlaschkeAnalytic"
  (title := "BlaschkeAnalytic")
  (statement := /--
    If $f:\mathbb{C}\to\mathbb{C}$ is analytic on $\overline{\mathbb{D}_R}$ then so too is $B_f$.
  -/)
  (proof := /--
    Expand out $B_f$ as a product, and observe that each part is analytic on $\overline{\mathbb{D}_R}$.
  -/)
  (latexEnv := "lemma")]
lemma BlaschkeAnalytic {r R : ℝ} {f : ℂ → ℂ}
    (r_pos : 0 < r) (r_lt_R : r < R) (R_lt_one : R < 1)
    (finiteZeros : (SetOfZeros 1 f).Finite)
    (hfAnalytic : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1))
    (hf_neq_zero_at_zero : f 0 ≠ 0) :
    AnalyticOnNhd ℂ (BlaschkeB r R f) (Metric.closedBall (0 : ℂ) R) := by
  have R_pos : 0 < R := lt_trans r_pos r_lt_R
  have r_lt_one : r < 1 := lt_trans r_lt_R R_lt_one
  unfold BlaschkeB
  by_cases finite_zeros_mono : (SetOfZeros r f).Finite
  · simp only [finite_zeros_mono, ↓reduceDIte]
    refine AnalyticOnNhd.mul (CfAnalytic r_lt_R R_lt_one hfAnalytic hf_neq_zero_at_zero) (Finset.analyticOnNhd_fun_prod (finiteSetOfZeros_mono r_lt_one finiteZeros).toFinset ?_)
    intro w hw
    refine AnalyticOnNhd.fun_pow (AnalyticOnNhd.sub (analyticOnNhd_const) (AnalyticOnNhd.div (AnalyticOnNhd.mul (analyticOnNhd_id) (analyticOnNhd_const)) (analyticOnNhd_const) ?_)) (analyticOrderAt f w).toNat
    intro w' hw'
    exact_mod_cast ne_of_gt R_pos
  · simp only [finite_zeros_mono, ↓reduceDIte]
    exact analyticOnNhd_const



@[blueprint "BlaschkeOfZero"
  (title := "BlaschkeOfZero")
  (statement := /--
    Let $0 < r < R<1$, and $f:\mathbb{C}\to\mathbb{C}$ be analytic on $\overline{\mathbb{D}_1}$ with
    $f(0)\neq 0$. Then
    $$|B_f(0)|=|f(0)|\prod_{\rho\in\mathcal{K}_f(r)}
      \left(\frac{R}{|\rho|}\right)^{m_f(\rho)}.$$
  -/)
  (proof := /--
    Since $f(0)\neq 0$, we know that $0\not\in\mathcal{K}_f(r)$. Thus,
    $$C_f(0)=\frac{f(0)}{\displaystyle\prod_{\rho\in\mathcal{K}_f(r)}(-\rho)^{m_f(\rho)}}.$$
    Thus, substituting this into Definition \ref{BlaschkeB},
    $$|B_f(0)|=|C_f(0)|\prod_{\rho\in\mathcal{K}_f(r)}R^{m_f(\rho)}
      =|f(0)|\prod_{\rho\in\mathcal{K}_f(r)}\left(\frac{R}{|\rho|}\right)^{m_f(\rho)}.$$
  -/)
  (latexEnv := "lemma")]
lemma BlaschkeOfZero {r R : ℝ} {f : ℂ → ℂ}
    (r_pos : 0 < r) (r_lt_one : r < 1) (r_lt_R : r < R)
    (finiteZeros : (SetOfZeros 1 f).Finite)
    (hf_neq_zero_at_zero : f 0 ≠ 0) :
    ‖BlaschkeB r R f 0‖ =
      ‖f 0‖ * (∏ ρ ∈ (finiteSetOfZeros_mono r_lt_one finiteZeros).toFinset, (R / ‖ρ‖) ^ (analyticOrderNatAt f ρ)) := by
  have zero_not_zero : ¬(0 ∈ SetOfZeros r f) := by
    apply notMem_setOf_iff.mpr
    simp only [norm_zero, not_and]
    intro r
    exact mem_support.mp hf_neq_zero_at_zero
  unfold BlaschkeB Cf
  simp only [finiteSetOfZeros_mono r_lt_one finiteZeros, zero_not_zero, ↓reduceDIte, zero_sub, zero_mul, zero_div, sub_zero,
    Complex.norm_mul, Complex.norm_div, norm_prod, norm_pow, norm_neg, norm_real, norm_eq_abs]
  rw[div_eq_mul_inv, mul_assoc, abs_of_pos (by linarith)]
  refine (mul_right_inj' (norm_ne_zero_iff.mpr hf_neq_zero_at_zero)).mpr ?_
  rw[← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
  simp only [div_eq_inv_mul, mul_pow, inv_pow]



@[blueprint "norm_fOfZero_le_norm_BlaschkeOfZero"
  (title := "norm-fOfZero-le-norm-BlaschkeOfZero")
  (statement := /--
    Let $0 < r < R<1$, and $f:\mathbb{C}\to\mathbb{C}$ be analytic on $\overline{\mathbb{D}_1}$ with
    $f(0)\neq 0$. Then
    $$|f(0)|\leq|B_f(0)|.$$
  -/)
  (proof := /--
    Applying lemma \ref{BlaschkeOfZero} we know that
    $$|B_f(0)|=|f(0)|\prod_{\rho\in\mathcal{K}_f(r)}
      \left(\frac{R}{|\rho|}\right)^{m_f(\rho)}.$$
    Note that for all $\rho\in\mathcal{K}_f(r)$ that $1<R/|\rho|$ since $r<R$.
    Thus, the result follows.
  -/)
  (latexEnv := "lemma")]
lemma norm_fOfZero_le_norm_BlaschkeOfZero {r R : ℝ} {f : ℂ → ℂ}
    (r_pos : 0 < r) (r_lt_R : r < R) (R_lt_one : R < 1)
    (finiteZeros : (SetOfZeros 1 f).Finite)
    (hf_neq_zero_at_zero : f 0 ≠ 0) :
    ‖f 0‖ ≤ ‖BlaschkeB r R f 0‖ := by
  have r_lt_one : r < 1 := lt_trans r_lt_R R_lt_one
  rw [BlaschkeOfZero r_pos r_lt_one r_lt_R finiteZeros hf_neq_zero_at_zero, ← mul_one ‖f 0‖]
  refine mul_le_mul (by rw[mul_one]) ?_ (zero_le_one) (mul_nonneg (norm_nonneg (f 0)) zero_le_one)
  rw [← Finset.prod_const_one (s := (finiteSetOfZeros_mono r_lt_one finiteZeros).toFinset)]
  apply Finset.prod_le_prod
  · intro ρ hρ
    exact zero_le_one
  · intro ρ hρ
    simp only [SetOfZeros, Finite.mem_toFinset, mem_setOf_eq] at hρ
    apply one_le_pow₀
    rw[one_le_div]
    · linarith
    · rw [norm_pos_iff]
      by_contra h
      rw [h] at hρ
      exact hf_neq_zero_at_zero hρ.2



@[blueprint "DiskBound"
  (title := "DiskBound")
  (statement := /--
    Let $0 < r < R<1$. If $f:\mathbb{C}\to\mathbb{C}$ is a function analytic on
    $\overline{\mathbb{D}_1}$ with $f(0)\neq0$ such that $|f(z)|\leq B$ for $|z|\leq R$,
    then $|B_f(z)|\leq B$ for $|z|\leq R$ also.
  -/)
  (proof := /--
    For $|z|=R$, we know that $z\not\in\mathcal{K}_f(r)$. Thus,
    $$C_f(z)=\frac{f(z)}{\displaystyle\prod_{\rho\in\mathcal{K}_f(r)}(z-\rho)^{m_f(\rho)}}.$$
    Thus, substituting this into Definition \ref{BlaschkeB},
    $$|B_f(z)|=|f(z)|\prod_{\rho\in\mathcal{K}_f(r)}
      \left|\frac{R-z\overline{\rho}/R}{z-\rho}\right|^{m_f(\rho)}.$$
    But note that
    $$\left|\frac{R-z\overline{\rho}/R}{z-\rho}\right|
      =\frac{|R^2-z\overline{\rho}|/R}{|z-\rho|}
      =\frac{|z|\cdot|\overline{z-\rho}|/R}{|z-\rho|}=1.$$
    So we have that $|B_f(z)|=|f(z)|\leq B$ when $|z|=R$. Now by the maximum modulus
    principle, we know that the maximum of $|B_f|$ must occur on the boundary where
    $|z|=R$. Thus $|B_f(z)|\leq B$ for all $|z|\leq R$.
  -/)
  (latexEnv := "lemma")]
lemma DiskBound {B r R : ℝ} {f : ℂ → ℂ} {z : ℂ}
    (r_pos : 0 < r) (r_lt_R : r < R) (R_lt_one : R < 1)
    (finiteZeros : (SetOfZeros 1 f).Finite)
    (hfAnalytic : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1))
    (hf_neq_zero_at_zero : f 0 ≠ 0) (fz_bound : ∀ (z : ℂ), ‖z‖ ≤ R → ‖f z‖ ≤ B)
    (hz : z ∈ Metric.closedBall (0 : ℂ) R) :
    ‖BlaschkeB r R f z‖ ≤ B := by
  have r_lt_one : r < 1 := lt_trans r_lt_R R_lt_one
  have R_pos : 0 < R := lt_trans r_pos r_lt_R
  refine AnalyticOn.norm_le_of_norm_le_on_sphere (Std.IsPreorder.le_refl R) (AnalyticOnNhd.analyticOn (BlaschkeAnalytic r_pos r_lt_R R_lt_one finiteZeros hfAnalytic hf_neq_zero_at_zero)) ?_ hz
  intro w hw
  rw[mem_sphere_iff_norm, sub_zero] at hw
  have hw_not_in : ¬(w ∈ SetOfZeros r f) := by
    apply notMem_setOf_iff.mpr
    intro le_r
    linarith
  have Bf_eq_f_at_w : ‖BlaschkeB r R f w‖ = ‖f w‖ := by
    unfold BlaschkeB Cf
    simp only [finiteSetOfZeros_mono r_lt_one finiteZeros, hw_not_in, ↓reduceDIte, Complex.norm_mul, Complex.norm_div, norm_prod, norm_pow]
    rw[div_eq_mul_inv, mul_assoc, mul_right_eq_self₀]
    by_cases fw_normZero : ‖f w‖ = 0
    · exact Or.inr fw_normZero
    · apply Or.inl
      rw[← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
      apply Finset.prod_eq_one
      intro w' hw'_in
      have hfact : (R : ℂ) - w * starRingEnd ℂ w' / R = (conj w - conj w') * w / R := by
        rw[sub_mul, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hw, ofReal_pow]
        field_simp
      rw [hfact, norm_div, norm_mul, ← map_sub, norm_conj, Complex.norm_real, hw, Real.norm_of_nonneg (le_of_lt R_pos)]
      field_simp
      rw[← div_pow, div_self, one_pow]
      rw[Set.Finite.mem_toFinset] at hw'_in
      exact norm_ne_zero_iff.mpr (sub_ne_zero.mpr (fun h => hw_not_in (h ▸ hw'_in)))
  rw[Bf_eq_f_at_w]
  exact fz_bound w (le_of_eq hw)



@[blueprint "BlaschkeNonZero"
  (title := "BlaschkeNonZero")
  (statement := /--
    Let $0 < r < R<1$ and $f:\overline{\mathbb{D}_1}\to\mathbb{C}$ be analytic on
    neighborhoods of points in $\overline{\mathbb{D}_1}$ with $f(0)\neq 0$. Then $B_f(z)\neq 0$
    for all $z\in\overline{\mathbb{D}_r}$.
  -/)
  (proof := /--
    Suppose that $z\in\mathcal{K}_f(r)$. Then we have that
    $$C_f(z)=\frac{h_z(z)}{\displaystyle\prod_{\rho\in\mathcal{K}_f(r)\setminus\{z\}}
      (z-\rho)^{m_f(\rho)}}.$$
    where $h_z(z)\neq 0$ according to Lemma \ref{ZeroFactorization}. Thus, substituting
    this into Definition \ref{BlaschkeB},
    \begin{equation}\label{pickupPoint2}
        |B_f(z)|=|h_z(z)|\cdot\left|R-\frac{|z|^2}{R}\right|^{m_f(z)}
          \prod_{\rho\in\mathcal{K}_f(r)\setminus\{z\}}
          \left|\frac{R-z\overline{\rho}/R}{z-\rho}\right|^{m_f(\rho)}.
    \end{equation}
    Trivially, $|h_z(z)|\neq 0$. Now note that
    $$\left|R-\frac{|z|^2}{R}\right|=0\implies|z|=R.$$
    However, this is a contradiction because $z\in\overline{\mathbb{D}_r}$ tells us that
    $|z|\leq r < R$. Similarly, note that
    $$\left|\frac{R-z\overline{\rho}/R}{z-\rho}\right|=0\implies|z|=\frac{R^2}{|\overline{\rho}|}.$$
    However, this is also a contradiction because $\rho\in\mathcal{K}_f(r)$ tells us that
    $R < R^2/|\overline{\rho}|=|z|$, but $z\in\overline{\mathbb{D}_r}$ tells us that
    $|z|\leq r < R$. So, we know that
    $$\left|R-\frac{|z|^2}{R}\right|\neq 0\qquad\text{and}\qquad
      \left|\frac{R-z\overline{\rho}/R}{z-\rho}\right|\neq 0
      \quad\text{for all}\quad\rho\in\mathcal{K}_f(r)\setminus\{z\}.$$
    Applying this to Equation (\ref{pickupPoint2}) we have that $|B_f(z)|\neq 0$.
    So, $B_f(z)\neq 0$.

    Now suppose that $z\not\in\mathcal{K}_f(r)$. Then we have that
    $$C_f(z)=\frac{f(z)}{\displaystyle\prod_{\rho\in\mathcal{K}_f(r)}(z-\rho)^{m_f(\rho)}}.$$
    Thus, substituting this into Definition \ref{BlaschkeB},
    \begin{equation}\label{pickupPoint3}
        |B_f(z)|=|f(z)|\prod_{\rho\in\mathcal{K}_f(r)}
          \left|\frac{R-z\overline{\rho}/R}{z-\rho}\right|^{m_f(\rho)}.
    \end{equation}
    We know that $|f(z)|\neq 0$ since $z\not\in\mathcal{K}_f(r)$. Now note that
    $$\left|\frac{R-z\overline{\rho}/R}{z-\rho}\right|=0\implies|z|=\frac{R^2}{|\overline{\rho}|}.$$
    However, this is a contradiction because $\rho\in\mathcal{K}_f(r)$ tells us that
    $R < R^2/|\overline{\rho}|=|z|$, but $z\in\overline{\mathbb{D}_r}$ tells us that
    $|z|\leq r < R$. So, we know that
    $$\left|\frac{R-z\overline{\rho}/R}{z-\rho}\right|\neq 0
      \quad\text{for all}\quad\rho\in\mathcal{K}_f(r).$$
    Applying this to Equation (\ref{pickupPoint3}) we have that $|B_f(z)|\neq 0$.
    So, $B_f(z)\neq 0$.

    We have shown that $B_f(z)\neq 0$ for both $z\in\mathcal{K}_f(r)$ and
    $z\not\in\mathcal{K}_f(r)$, so the result follows.
  -/)
  (latexEnv := "lemma")]
lemma BlaschkeNonzero {r R : ℝ} {f : ℂ → ℂ}
    (r_pos : 0 < r) (r_lt_R : r < R) (R_lt_one : R < 1)
    (finiteZeros : (SetOfZeros 1 f).Finite)
    (hfAnalytic : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1))
    (hf_neq_zero_at_zero : f 0 ≠ 0) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r, BlaschkeB r R f z ≠ 0 := by
  have r_lt_one : r < 1 := lt_trans r_lt_R R_lt_one
  have R_pos : 0 < R := lt_trans r_pos r_lt_R
  intro z hz
  have hz_norm_le_r : ‖z‖ ≤ r := by rwa [mem_closedBall_iff_norm, sub_zero] at hz
  have hz_norm_lt_R : ‖z‖ < R := by linarith
  let hFin := finiteSetOfZeros_mono r_lt_one finiteZeros
  have hBProd : ∏ ρ ∈ hFin.toFinset,
      (↑R - z * (starRingEnd ℂ) ρ / ↑R) ^ analyticOrderNatAt f ρ ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro ρ hρ
    apply pow_ne_zero
    norm_num [ sub_eq_zero, Complex.ext_iff ];
    simp only [SetOfZeros, Finite.mem_toFinset, mem_setOf_eq] at hρ
    rw [ eq_div_iff ] <;> norm_num [ Complex.normSq, Complex.norm_def ] at *;
    · rw [Real.sqrt_lt' (by linarith)] at hz_norm_lt_R
      rw [ Real.sqrt_le_iff ] at hρ
      exact fun h => absurd h ( by nlinarith [ sq_nonneg ( z.re - ρ.re ), sq_nonneg ( z.im - ρ.im ), mul_lt_mul_of_pos_left r_lt_R R_pos ] )
    · linarith
  unfold BlaschkeB Cf
  by_cases z_in_zeros : z ∈ SetOfZeros r f
  · simp only [hFin, z_in_zeros, ↓reduceDIte]
    obtain ⟨_, _, hne, heq⟩ :=
      ZeroFactorization (by linarith) (hfAnalytic.mono (Metric.closedBall_subset_closedBall (by linarith)))
        hf_neq_zero_at_zero z_in_zeros
    rw [heq.1]
    refine mul_ne_zero (div_ne_zero hne (Finset.prod_ne_zero_iff.mpr fun ρ hρ =>
      pow_ne_zero _ (sub_ne_zero.mpr fun h =>
        (Finset.mem_sdiff.mp hρ).2 (Finset.mem_singleton.mpr h.symm)))) hBProd
  · simp only [hFin, z_in_zeros, ↓reduceDIte]
    refine mul_ne_zero (div_ne_zero (fun hfz => z_in_zeros ⟨hz_norm_le_r, hfz⟩)
      (Finset.prod_ne_zero_iff.mpr fun ρ hρ =>
        pow_ne_zero _ (sub_ne_zero.mpr fun h => z_in_zeros (h ▸ hFin.mem_toFinset.mp hρ)))) hBProd



@[blueprint "ZerosBound"
  (title := "ZerosBound")
  (statement := /--
    Let $0< r < R<1$. If $f:\mathbb{C}\to\mathbb{C}$ is a function analytic on
    neighborhoods of points in $\overline{\mathbb{D}_1}$ with $f(0)=1$ and $|f(z)|\leq B$
    for $|z|\leq R$, then
    $$\sum_{\rho\in\mathcal{K}_f(r)}m_f(\rho)\leq\frac{\log B}{\log(R/r)}.$$
  -/)
   (proof := /--
    Since $f(0)=1$, by Lemma \ref{BlaschkeOfZero} we know that
    $$|B_f(0)|
      =|f(0)|\prod_{\rho\in\mathcal{K}_f(r)}\left(\frac{R}{|\rho|}\right)^{m_f(\rho)}
      =\prod_{\rho\in\mathcal{K}_f(r)}\left(\frac{R}{|\rho|}\right)^{m_f(\rho)}.$$
    Thus, substituting this into Definition \ref{BlaschkeB},
    $$(R/r)^{\sum_{\rho\in\mathcal{K}_f(r)}m_f(\rho)}
      =\prod_{\rho\in\mathcal{K}_f(r)}\left(\frac{R}{r}\right)^{m_f(\rho)}
      \leq\prod_{\rho\in\mathcal{K}_f(r)}\left(\frac{R}{|\rho|}\right)^{m_f(\rho)}
      =|B_f(0)|\leq B$$
    whereby Lemma \ref{DiskBound} we know that $|B_f(z)|\leq B$ for all $|z|\leq R$.
    Taking the logarithm of both sides and rearranging gives the desired result.
  -/)
  (latexEnv := "theorem")]
theorem ZerosBound {B r R : ℝ} {f : ℂ → ℂ}
    (r_pos : 0 < r) (r_lt_one : r < 1) (r_lt_R : r < R) (R_lt_one : R < 1)
    (hfAnalytic : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1)) (hf0_eq_one : f 0 = 1)
    (finiteZeros : (SetOfZeros 1 f).Finite) (fz_bound : ∀ z : ℂ, ‖z‖ ≤ R → ‖f z‖ ≤ B) :
    ∑ ρ ∈ (finiteSetOfZeros_mono r_lt_one finiteZeros).toFinset, analyticOrderNatAt f ρ ≤
      1 / Real.log (R / r) * Real.log B := by
  have R_pos : 0 < R := lt_trans r_pos r_lt_R
  have hf0_ne_zero : f 0 ≠ 0 := by rw [hf0_eq_one]; exact one_ne_zero
  have blaschke_eq := BlaschkeOfZero r_pos r_lt_one r_lt_R finiteZeros hf0_ne_zero
  rw[hf0_eq_one, norm_one, one_mul] at blaschke_eq
  rw [one_div, inv_mul_eq_div, le_div_iff₀ (Real.log_pos (by simp only [lt_div_iff₀ r_pos, one_mul, r_lt_R])), ← Real.log_pow]
  refine Real.log_le_log (pow_pos (div_pos R_pos r_pos) _) ?_
  calc (R / r) ^ ∑ ρ ∈ (finiteSetOfZeros_mono r_lt_one finiteZeros).toFinset, analyticOrderNatAt f ρ
      = ∏ ρ ∈ (finiteSetOfZeros_mono r_lt_one finiteZeros).toFinset, (R / r) ^ analyticOrderNatAt f ρ := by
        rw [Finset.prod_pow_eq_pow_sum]
    _ ≤ ∏ ρ ∈ (finiteSetOfZeros_mono r_lt_one finiteZeros).toFinset, (R / ‖ρ‖) ^ analyticOrderNatAt f ρ := by
      apply Finset.prod_le_prod
      · intro ρ _
        exact pow_nonneg (div_nonneg (le_of_lt R_pos) (le_of_lt r_pos)) _
      · intro ρ hρ
        have hρ_mem := (finiteSetOfZeros_mono r_lt_one finiteZeros).mem_toFinset.mp hρ
        refine pow_le_pow_left₀ (div_nonneg (le_of_lt R_pos) (le_of_lt r_pos)) ?_ _
        refine div_le_div_of_nonneg_left (le_of_lt R_pos) (norm_pos_iff.mpr ?_) (hρ_mem.1)
        rintro rfl
        exact hf0_ne_zero hρ_mem.2
    _ ≤ B := by
      rw[← blaschke_eq]
      exact DiskBound r_pos r_lt_R R_lt_one finiteZeros hfAnalytic
        hf0_ne_zero fz_bound (Metric.mem_closedBall_self (le_of_lt R_pos))



@[blueprint "JBlaschke"
  (title := "JBlaschke")
  (statement := /--
    Let $0 < r < R<1$. If $f:\mathbb{C}\to\mathbb{C}$ is a function analytic on
    neighborhoods of points in $\overline{\mathbb{D}_1}$ with $f(0)=1$, define
    $L_f(z)=J_{B_f}(z)$ where $J$ is from Theorem \ref{LogOfAnalyticFunction} and $B_f$
    is from Definition \ref{BlaschkeB}.
  -/)]
noncomputable def JBlaschke {r' r R : ℝ} {f : ℂ → ℂ}
  (r'_pos : 0 < r') (r'_lt_r : r' < r) (r_pos : 0 < r) (r_lt_R : r < R) (R_lt_one : R < 1)
  (hfAnalytic : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1)) (hf0_eq_one : f 0 = 1)
  (finiteZeros : (SetOfZeros 1 f).Finite)
  (z : ℂ) : ℂ :=
  (LogOfAnalyticFunction' r'_pos r'_lt_r r_lt_R
    (BlaschkeAnalytic r_pos r_lt_R R_lt_one finiteZeros hfAnalytic (hf0_eq_one ▸ one_ne_zero))
    (BlaschkeNonzero r_pos r_lt_R R_lt_one finiteZeros hfAnalytic (hf0_eq_one ▸ one_ne_zero))).choose z



@[blueprint "JBlaschkeDerivBound"
  (title := "JBlaschkeDerivBound")
  (statement := /--
    Let $B>1$ and $0 < r' < r < R<1$. If $f:\mathbb{C}\to\mathbb{C}$ is a function analytic
    on neighborhoods of points in $\overline{\mathbb{D}_1}$ with $f(0)=1$ and $|f(z)|\leq B$
    for all $|z|\leq R$, then for all $|z|\leq r'$
    $$|L_f'(z)|\leq\frac{16\log(B)\,r^2}{(r-r')^3}.$$
  -/)
  (proof := /--
    By Lemma \ref{DiskBound} we immediately know that $|B_f(z)|\leq B$ for all $|z|\leq R$.
    Now since $L_f=J_{B_f}$ by Definition \ref{JBlaschke}, by Theorem
    \ref{LogOfAnalyticFunction} we know that
    $$L_f(0)=0\qquad\text{and}\qquad
      \Re L_f(z)=\log|B_f(z)|-\log|B_f(0)|\leq\log|B_f(z)|\leq\log B$$
    for all $|z|\leq r$. Note that in the above
    $$0=\log|f(0)|\leq\log|B_f(0)|$$
    because of Lemma \ref{norm-fOfZero-le-norm-BlaschkeOfZero}. So by Theorem \ref{BorelCaratheodoryDeriv}, it follows that
    $$|L_f'(z)|\leq\frac{16\log(B)\,r^2}{(r-r')^3}$$
    for all $|z|\leq r'$.
  -/)
  (latexEnv := "theorem")]
theorem JBlaschkeDerivBound {B r' r R : ℝ} {f : ℂ → ℂ} {z : ℂ}
    (one_lt_B : 1 < B) (r'_pos : 0 < r') (r'_lt_r : r' < r) (r_pos : 0 < r) (r_lt_R : r < R) (R_lt_one : R < 1)
    (hfAnalytic : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1)) (hf0_eq_one : f 0 = 1)
    (finiteZeros : (SetOfZeros 1 f).Finite) (fz_bound : ∀ z : ℂ, ‖z‖ ≤ R → ‖f z‖ ≤ B)
    (hz : z ∈ Metric.closedBall (0 : ℂ) r') :
    ‖deriv (JBlaschke r'_pos r'_lt_r r_pos r_lt_R R_lt_one hfAnalytic hf0_eq_one finiteZeros) z‖
      ≤ 16 * Real.log (B) * r ^ 2 / (r - r') ^ 3 := by
  have r_pos : 0 < r := lt_trans r'_pos r'_lt_r
  let blaschkeAnalytic := BlaschkeAnalytic r_pos r_lt_R R_lt_one finiteZeros hfAnalytic (hf0_eq_one ▸ one_ne_zero)
  let blaschkeNonzero := BlaschkeNonzero r_pos r_lt_R R_lt_one finiteZeros hfAnalytic (hf0_eq_one ▸ one_ne_zero)
  let logOfAnalytic := LogOfAnalyticFunction' r'_pos r'_lt_r r_lt_R blaschkeAnalytic blaschkeNonzero
  set JB := logOfAnalytic.choose with JB_def
  obtain ⟨JB_Analytic, JB_0_eq_0, deriv_JB_eq, JB_re⟩ := logOfAnalytic.choose_spec
  rw [← JB_def] at JB_Analytic JB_0_eq_0 deriv_JB_eq JB_re
  have JB_def' : JB = (JBlaschke r'_pos r'_lt_r r_pos r_lt_R R_lt_one hfAnalytic hf0_eq_one finiteZeros) := by
    unfold JBlaschke
    rw [← JB_def]
  rw[← JB_def']
  refine BorelCaratheodoryDeriv (Real.log_pos one_lt_B) r'_pos r'_lt_r (JB_Analytic.analyticOn) JB_0_eq_0 ?_ hz
  intro w hw
  rw[← JB_re w hw]
  have hwr : w ∈ Metric.closedBall (0 : ℂ) r := by exact Metric.ball_subset_closedBall hw
  have hlog : 0 ≤ Real.log ‖BlaschkeB r R f 0‖ := by
    rw [← Real.log_one]
    apply Real.log_le_log zero_lt_one
    rw [← norm_one (α := ℂ), ← hf0_eq_one]
    exact norm_fOfZero_le_norm_BlaschkeOfZero r_pos r_lt_R R_lt_one finiteZeros (hf0_eq_one ▸ one_ne_zero)
  suffices h : Real.log ‖BlaschkeB r R f w‖ ≤ Real.log B by linarith
  exact Real.log_le_log (norm_pos_iff.mpr (blaschkeNonzero w hwr))
    (DiskBound r_pos r_lt_R R_lt_one finiteZeros hfAnalytic (hf0_eq_one ▸ one_ne_zero) fz_bound (Metric.closedBall_subset_closedBall r_lt_R.le hwr))



@[blueprint "FinalBound"
  (title := "FinalBound")
  (statement := /--
    Let $B>1$ and $0 < r' < r < R' < R<1$. If $f:\mathbb{C}\to\mathbb{C}$ is a function
    analytic on neighborhoods of points in $\overline{\mathbb{D}_1}$ with $f(0)=1$ and
    $|f(z)|\leq B$ for all $|z|\leq R$, then for all
    $z\in\overline{\mathbb{D}_{r'}}\setminus\mathcal{K}_f(R')$ we have
    $$\left|\frac{f'}{f}(z)-\sum_{\rho\in\mathcal{K}_f(r)}\frac{m_f(\rho)}{z-\rho}\right|
      \leq\left(\frac{16r^2}{(r-r')^3}+\frac{1}{(R^2/R'-R')\,\log(R/R')}\right)\log B.$$
  -/)
  (proof := /--
    Since $z\in\overline{\mathbb{D}_{r'}}\setminus\mathcal{K}_f(R')$ we know that
    $z\not\in\mathcal{K}_f(R')$; thus, by Definition \ref{CFunction} we know that
    $$C_f(z)=\frac{f(z)}{\displaystyle\prod_{\rho\in\mathcal{K}_f(r)}(z-\rho)^{m_f(\rho)}}.$$
    Substituting this into Definition \ref{BlaschkeB} we have that
    $$B_f(z)=f(z)\prod_{\rho\in\mathcal{K}_f(r)}
      \left(\frac{R-z\overline{\rho}/R}{z-\rho}\right)^{m_f(\rho)}.$$
    Taking the complex logarithm of both sides we have that
    $$\mathrm{Log}\,B_f(z)=\mathrm{Log}\,f(z)
      +\sum_{\rho\in\mathcal{K}_f(r)}m_f(\rho)\,\mathrm{Log}(R-z\overline{\rho}/R)
      -\sum_{\rho\in\mathcal{K}_f(r)}m_f(\rho)\,\mathrm{Log}(z-\rho).$$
    Taking the derivative of both sides we have that
    $$\frac{B_f'}{B_f}(z)=\frac{f'}{f}(z)
      +\sum_{\rho\in\mathcal{K}_f(r)}\frac{m_f(\rho)}{z-R^2/\overline{\rho}}
      -\sum_{\rho\in\mathcal{K}_f(r)}\frac{m_f(\rho)}{z-\rho}.$$
    By Definition \ref{JBlaschke} and Theorem \ref{LogOfAnalyticFunction},
    since $L_f(z)=J_{B_f}(z)$ we have $L_f'(z)=J'_{B_f}(z)=(B_f'/B_f)(z)$. Thus,
    $$\frac{f'}{f}(z)-\sum_{\rho\in\mathcal{K}_f(r)}\frac{m_f(\rho)}{z-\rho}
      =L_f'(z)-\sum_{\rho\in\mathcal{K}_f(r)}\frac{m_f(\rho)}{z-R^2/\overline{\rho}}.$$
    Now since $z\in\overline{\mathbb{D}_{r'}}\subseteq\overline{\mathbb{D}_{R'}}$ and $\rho\in\mathcal{K}_f(r)\subseteq\mathcal{K}_f(R')$, we know that
    $R^2/R'-R'\leq|z-R^2/\overline{\rho}|$. Thus by the triangle inequality we have
    $$\left|\frac{f'}{f}(z)-\sum_{\rho\in\mathcal{K}_f(r)}\frac{m_f(\rho)}{z-\rho}\right|
      \leq|L_f'(z)|+\left(\frac{1}{R^2/R'-R'}\right)\sum_{\rho\in\mathcal{K}_f(r)}m_f(\rho).$$
    Now by Theorem \ref{ZerosBound} and \ref{JBlaschkeDerivBound} we get our desired result
    with a little algebraic manipulation.
  -/)
  (latexEnv := "theorem")]
theorem FinalBound {B r' r R' R : ℝ} {f : ℂ → ℂ} {z : ℂ}
    (one_lt_B : 1 < B) (r'_pos : 0 < r') (r'_lt_r : r' < r) (r_lt_one : r < 1) (r_lt_R' : r < R') (R'_lt_R : R' < R) (R_lt_one : R < 1)
    (hfAnalytic : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1)) (hf0_eq_one : f 0 = 1)
    (finiteZeros : (SetOfZeros 1 f).Finite) (fz_bound : ∀ z : ℂ, ‖z‖ ≤ R → ‖f z‖ ≤ B)
    (hz : z ∈ Metric.closedBall (0 : ℂ) r' \ SetOfZeros R' f) :
    ‖(deriv f z / f z) - ∑ ρ ∈ (finiteSetOfZeros_mono r_lt_one finiteZeros).toFinset, analyticOrderNatAt f ρ / (z - ρ)‖ ≤
      (16 * r ^ 2 / (r - r') ^ 3 + 1 / ((R ^ 2 / R' - R') * Real.log (R / R'))) * Real.log B := by
  have r'_lt_one : r' < 1 := lt_trans r'_lt_r r_lt_one
  have r_pos : 0 < r := lt_trans r'_pos r'_lt_r
  have R'_pos : 0 < R' := lt_trans r_pos r_lt_R'
  have R_pos : 0 < R := lt_trans R'_pos R'_lt_R
  have r_lt_R : r < R := lt_trans r_lt_R' R'_lt_R
  have r'_lt_R : r' < R := lt_trans r'_lt_r r_lt_R
  have rFiniteZeros: (SetOfZeros r f).Finite := finiteSetOfZeros_mono r_lt_one finiteZeros
  have zNotInZeros : ¬(z ∈ SetOfZeros r f) := (fun hmem => hz.2 ⟨hmem.1.trans r_lt_R'.le, hmem.2⟩)
  have z_norm : ‖z‖ ≤ r' := by simpa [Metric.mem_closedBall, dist_zero_right] using hz.1
  have ρ_mem : ∀ ρ ∈ rFiniteZeros.toFinset, ‖ρ‖ ≤ r ∧ f ρ = 0 := fun ρ hρ => rFiniteZeros.mem_toFinset.mp hρ
  have ρ_ne_zero : ∀ ρ ∈ rFiniteZeros.toFinset, ρ ≠ 0 := fun ρ hρ h => one_ne_zero (hf0_eq_one ▸ h ▸ (ρ_mem ρ hρ).2)
  have blaschke_sub_ne : ∀ ρ ∈ rFiniteZeros.toFinset, (↑R : ℂ) - z * (starRingEnd ℂ) ρ / ↑R ≠ 0 := by
    intro ρ hρ h
    have : ‖z * (starRingEnd ℂ) ρ / (↑R : ℂ)‖ < R := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos R_pos, div_lt_iff₀ R_pos, norm_mul, norm_conj]
      exact mul_lt_mul (z_norm.trans_lt r'_lt_R) ((ρ_mem ρ hρ).1.trans_lt r_lt_R).le
        (norm_pos_iff.mpr (ρ_ne_zero ρ hρ)) R_pos.le
    rw [← sub_eq_zero.mp h] at this
    simp [Complex.norm_real, abs_of_pos R_pos] at this
  have fz_ne : f z ≠ 0 := fun h => zNotInZeros ⟨z_norm.trans r'_lt_r.le, h⟩
  have blaschke_prod_ne : ∀ ρ ∈ rFiniteZeros.toFinset, ((↑R : ℂ) - z * (starRingEnd ℂ) ρ / ↑R) ^ analyticOrderNatAt f ρ ≠ 0 := fun ρ hρ => pow_ne_zero _ (blaschke_sub_ne ρ hρ)
  have hDiff_blaschke : ∀ ρ ∈ rFiniteZeros.toFinset, DifferentiableAt ℂ (fun w => ((↑R : ℂ) - w * (starRingEnd ℂ) ρ / ↑R) ^ analyticOrderNatAt f ρ) z := fun ρ _ => ((differentiableAt_const _).sub ((differentiableAt_id.mul_const _).div_const _)).pow _
  have hDiff_sub : ∀ ρ ∈ rFiniteZeros.toFinset, DifferentiableAt ℂ (fun w => (w - (ρ : ℂ)) ^ analyticOrderNatAt f ρ) z := fun ρ _ => (differentiableAt_id.sub (differentiableAt_const _)).pow _
  have hpos : 0 < R ^ 2 / R' - R' := by
    rw [sub_pos, lt_div_iff₀ R'_pos, ← sq]
    apply pow_lt_pow_left₀ R'_lt_R R'_pos.le two_ne_zero
  have LfBound := JBlaschkeDerivBound one_lt_B r'_pos r'_lt_r r_pos r_lt_R R_lt_one hfAnalytic hf0_eq_one finiteZeros fz_bound hz.1
  have zerosBound : ↑(∑ ρ ∈ (finiteSetOfZeros_mono r_lt_one finiteZeros).toFinset, analyticOrderNatAt f ρ) ≤ 1 / Real.log (R / R') * Real.log B := by
    apply (ZerosBound r_pos r_lt_one r_lt_R R_lt_one hfAnalytic hf0_eq_one finiteZeros fz_bound).trans
    refine mul_le_mul_of_nonneg_right (one_div_le_one_div_of_le ?_ ?_) (Real.log_nonneg (le_of_lt one_lt_B))
    · rw [← Real.log_one, Real.log_lt_log_iff zero_lt_one (div_pos R_pos R'_pos), one_lt_div R'_pos]
      exact R'_lt_R
    · rw [Real.log_le_log_iff (div_pos R_pos R'_pos) (div_pos R_pos r_pos)]
      exact div_le_div_of_nonneg_left (le_of_lt R_pos) r_pos (le_of_lt r_lt_R')
  suffices h1 : ‖deriv f z / f z - ∑ ρ ∈ (finiteSetOfZeros_mono r_lt_one finiteZeros).toFinset, ↑(analyticOrderNatAt f ρ) / (z - ρ)‖ ≤ ‖deriv (JBlaschke r'_pos r'_lt_r r_pos r_lt_R R_lt_one hfAnalytic hf0_eq_one finiteZeros) z‖ + 1 / (R ^ 2 / R' - R') * ↑(∑ ρ ∈ (finiteSetOfZeros_mono r_lt_one finiteZeros).toFinset, analyticOrderNatAt f ρ) by
    calc ‖deriv f z / f z - ∑ ρ ∈ (finiteSetOfZeros_mono r_lt_one finiteZeros).toFinset, ↑(analyticOrderNatAt f ρ) / (z - ρ)‖
      ≤ ‖deriv (JBlaschke r'_pos r'_lt_r r_pos r_lt_R R_lt_one hfAnalytic hf0_eq_one finiteZeros) z‖ + 1 / (R ^ 2 / R' - R') * ↑(∑ ρ ∈ (finiteSetOfZeros_mono r_lt_one finiteZeros).toFinset, analyticOrderNatAt f ρ) := h1
    _ ≤ 16 * Real.log B * r ^ 2 / (r - r') ^ 3 + 1 / (R ^ 2 / R' - R') * (1 / Real.log (R / R') * Real.log B) := by
      linarith [mul_le_mul_of_nonneg_left zerosBound (div_nonneg zero_le_one (le_of_lt hpos))]
    _ = (16 * r ^ 2 / (r - r') ^ 3 + 1 / ((R ^ 2 / R' - R') * Real.log (R / R'))) * Real.log B := by
      field_simp
  suffices h2 : deriv f z / f z - ∑ ρ ∈ (finiteSetOfZeros_mono r_lt_one finiteZeros).toFinset, ↑(analyticOrderNatAt f ρ) / (z - ρ) =
    deriv (JBlaschke r'_pos r'_lt_r r_pos r_lt_R R_lt_one hfAnalytic hf0_eq_one finiteZeros) z - ∑ ρ ∈ (finiteSetOfZeros_mono r_lt_one finiteZeros).toFinset, ↑(analyticOrderNatAt f ρ) / (z - R ^ 2 / conj ρ) by
    rw [h2, sub_eq_add_neg]
    apply norm_add_le_of_le (le_rfl)
    simp only [norm_neg]
    calc
      ‖∑ ρ ∈ (finiteSetOfZeros_mono r_lt_one finiteZeros).toFinset,
          ↑(analyticOrderNatAt f ρ) / (z - R ^ 2 / conj ρ)‖
          ≤ ∑ ρ ∈ (finiteSetOfZeros_mono r_lt_one finiteZeros).toFinset,
              ‖↑(analyticOrderNatAt f ρ) / (z - R ^ 2 / conj ρ)‖ := norm_sum_le _ _
      _ ≤ ∑ ρ ∈ (finiteSetOfZeros_mono r_lt_one finiteZeros).toFinset,
              ↑(analyticOrderNatAt f ρ) / (R ^ 2 / R' - R') := by
          refine Finset.sum_le_sum (fun ρ hρ => ?_)
          rw [norm_div, RCLike.norm_natCast]
          apply div_le_div_of_nonneg_left (Nat.cast_nonneg _) hpos
          simp only [mem_diff, Metric.mem_closedBall, dist_zero_right, SetOfZeros,
            Finite.mem_toFinset, mem_setOf_eq] at hρ hz
          rw [norm_sub_rev]
          calc R ^ 2 / R' - R'
              ≤ ‖↑R ^ 2 / conj ρ‖ - ‖z‖ := by
                refine sub_le_sub ?_ (hz.1.trans (r'_lt_r.le.trans r_lt_R'.le))
                rw [norm_div, norm_pow, norm_real, norm_eq_abs,
                  abs_of_nonneg (le_of_lt R_pos)]
                apply div_le_div_of_nonneg_left (sq_nonneg R)
                  (norm_pos_iff.mpr (star_ne_zero.mpr
                    (fun h => one_ne_zero (hf0_eq_one ▸ h ▸ hρ.2))))
                rw [norm_star]
                linarith [hρ.1]
            _ ≤ ‖↑R ^ 2 / conj ρ - z‖ := norm_sub_norm_le _ _
      _ = 1 / (R ^ 2 / R' - R') *
              ↑(∑ ρ ∈ (finiteSetOfZeros_mono r_lt_one finiteZeros).toFinset,
                analyticOrderNatAt f ρ) := by
          rw [Nat.cast_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl (fun _ _ => ?_)
          field_simp
  suffices h3 : deriv (BlaschkeB r R f) z / BlaschkeB r R f z = deriv f z / f z
    + ∑ ρ ∈ (finiteSetOfZeros_mono r_lt_one finiteZeros).toFinset, ↑(analyticOrderNatAt f ρ) / (z - R ^ 2 / conj ρ)
    - ∑ ρ ∈ (finiteSetOfZeros_mono r_lt_one finiteZeros).toFinset, ↑(analyticOrderNatAt f ρ) / (z - ρ) by
    let blaschkeAnalytic := BlaschkeAnalytic r_pos r_lt_R R_lt_one finiteZeros hfAnalytic (hf0_eq_one ▸ one_ne_zero)
    let blaschkeNonzero := BlaschkeNonzero r_pos r_lt_R R_lt_one finiteZeros hfAnalytic (hf0_eq_one ▸ one_ne_zero)
    let logOfAnalytic := LogOfAnalyticFunction' r'_pos r'_lt_r r_lt_R blaschkeAnalytic blaschkeNonzero
    set JB := logOfAnalytic.choose with JB_def
    obtain ⟨JB_Analytic, JB_0_eq_0, deriv_JB_eq, JB_re⟩ := logOfAnalytic.choose_spec
    rw [← JB_def] at JB_Analytic JB_0_eq_0 deriv_JB_eq JB_re
    have JB_def' : JB = (JBlaschke r'_pos r'_lt_r r_pos r_lt_R R_lt_one hfAnalytic hf0_eq_one finiteZeros) := by
      unfold JBlaschke
      rw [JB_def]
    rw [eq_sub_iff_add_eq, sub_add_eq_add_sub, ← h3, ← JB_def', eq_comm]
    exact deriv_JB_eq z hz.1
  suffices h4 : BlaschkeB r R f z = f z * ∏ ρ ∈ (finiteSetOfZeros_mono r_lt_one finiteZeros).toFinset, ((R - z * conj ρ / R) / (z - ρ)) ^ (analyticOrderNatAt f ρ) by
    have sum1LD : ∑ ρ ∈ (finiteSetOfZeros_mono r_lt_one finiteZeros).toFinset, logDeriv (fun z ↦ (R - z * conj ρ / R) ^ ↑(analyticOrderNatAt f ρ)) z = ∑ ρ ∈ (finiteSetOfZeros_mono r_lt_one finiteZeros).toFinset, ↑(analyticOrderNatAt f ρ) / (z - R ^ 2 / conj ρ) := by
      refine Finset.sum_congr rfl (fun ρ hρ => ?_)
      rw [← logDeriv_pow, logDeriv_fun_pow, logDeriv_fun_pow, logDeriv_id', mul_eq_mul_left_iff]
      · left
        simp only [logDeriv, Pi.div_apply]
        rw [deriv_fun_sub (differentiableAt_const _) ?_, deriv_div_const, deriv_mul_const (differentiableAt_fun_id)]
        · simp only [deriv_const', deriv_id'', one_mul, zero_sub]
          rw [div_eq_div_iff (blaschke_sub_ne ρ hρ), one_mul, neg_mul, mul_sub, mul_div, neg_sub, mul_comm _ z, ← mul_div_assoc, sub_left_inj]
          · field_simp
            exact mul_div_cancel_left₀ _ (star_ne_zero.mpr (ρ_ne_zero ρ hρ))
          · intro h; apply blaschke_sub_ne ρ hρ
            have hconj : (starRingEnd ℂ) ρ ≠ 0 := star_ne_zero.mpr (ρ_ne_zero ρ hρ)
            have hR : (↑R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt R_pos)
            rw [sub_eq_zero.mp h, div_mul_cancel₀ _ hconj, sq, mul_div_cancel_right₀ _ hR, sub_self]
        · simp only [differentiableAt_fun_id, differentiableAt_const, DifferentiableAt.fun_mul,
          DifferentiableAt.div_const]
      · simp only [differentiableAt_fun_id]
      · simp only [differentiableAt_const, DifferentiableAt.fun_sub_iff_right,
          differentiableAt_fun_id, DifferentiableAt.fun_mul, DifferentiableAt.div_const]
    have sum2LD : ∑ ρ ∈ (finiteSetOfZeros_mono r_lt_one finiteZeros).toFinset, logDeriv (fun z ↦ (z - ρ) ^ ↑(analyticOrderNatAt f ρ)) z =  ∑ ρ ∈ (finiteSetOfZeros_mono r_lt_one finiteZeros).toFinset, ↑(analyticOrderNatAt f ρ) / (z - ρ) := by
      refine Finset.sum_congr rfl (fun ρ _ => ?_)
      have : (fun z ↦ (z - ρ) ^ analyticOrderNatAt f ρ) =
        (fun x ↦ x ^ analyticOrderNatAt f ρ) ∘ (fun z ↦ z - ρ) := by rfl
      rw[← logDeriv_pow, this, logDeriv_comp]
      · simp only [logDeriv_pow, differentiableAt_fun_id, differentiableAt_const, deriv_fun_sub,
          deriv_id'', deriv_const', sub_zero, mul_one]
      · simp only [differentiableAt_fun_id, DifferentiableAt.fun_pow]
      · simp only [differentiableAt_fun_id, differentiableAt_const, DifferentiableAt.fun_sub]
    unfold BlaschkeB Cf
    simp only [rFiniteZeros, ↓reduceDIte, dite_eq_ite, ite_mul, ← logDeriv_apply, ← sum1LD, ← sum2LD]
    rw [← logDeriv_prod blaschke_prod_ne hDiff_blaschke,
      ← logDeriv_prod ?_ hDiff_sub,
      ← logDeriv_mul _ fz_ne (Finset.prod_ne_zero_iff.mpr blaschke_prod_ne) ((hfAnalytic z (Metric.closedBall_subset_closedBall r'_lt_one.le hz.1)).differentiableAt) (DifferentiableAt.fun_finsetProd hDiff_blaschke),
      ← logDeriv_div _ ?_ ?_ ?_ (DifferentiableAt.fun_finsetProd hDiff_sub)]
    · have h_eq : ∀ᶠ w in nhds z, (if w ∈ SetOfZeros r f then (ZeroFactor f w / ∏ ρ ∈ rFiniteZeros.toFinset \ {w}, (w - ρ) ^ analyticOrderNatAt f ρ) * ∏ ρ ∈ rFiniteZeros.toFinset, (R - w * (starRingEnd ℂ) ρ / R) ^ analyticOrderNatAt f ρ else (f w / ∏ ρ ∈ rFiniteZeros.toFinset, (w - ρ) ^ analyticOrderNatAt f ρ) * ∏ ρ ∈ rFiniteZeros.toFinset, (R - w * (starRingEnd ℂ) ρ / R) ^ analyticOrderNatAt f ρ) = (f w * ∏ ρ ∈ rFiniteZeros.toFinset, (R - w * (starRingEnd ℂ) ρ / R) ^ analyticOrderNatAt f ρ) / ∏ ρ ∈ rFiniteZeros.toFinset, (w - ρ) ^ analyticOrderNatAt f ρ := by
        filter_upwards [(isOpen_compl_iff.mpr rFiniteZeros.isClosed).mem_nhds zNotInZeros] with w hw using by rw [if_neg hw]; ring
      simp only [logDeriv, Pi.div_apply]
      congr 1
      · apply Filter.EventuallyEq.deriv_eq h_eq
      · convert h_eq.self_of_nhds using 1
    · exact mul_ne_zero fz_ne (Finset.prod_ne_zero_iff.mpr blaschke_prod_ne)
    · simp only [ne_eq, Finset.prod_eq_zero_iff, Finite.mem_toFinset, pow_eq_zero_iff',
        sub_eq_zero, ↓existsAndEq, zNotInZeros, true_and, false_and, not_false_eq_true]
    · exact ((hfAnalytic z (Metric.closedBall_subset_closedBall r'_lt_one.le hz.1)).differentiableAt).mul (DifferentiableAt.fun_finsetProd hDiff_blaschke)
    · exact (fun ρ hρ => pow_ne_zero _ (sub_ne_zero.mpr fun h => zNotInZeros (h ▸ rFiniteZeros.mem_toFinset.mp hρ)))
  simp only [BlaschkeB, Cf, rFiniteZeros, ↓reduceDIte, zNotInZeros, div_mul_eq_mul_div, mul_div_assoc, ← Finset.prod_div_distrib, div_pow]




end GafniTao
