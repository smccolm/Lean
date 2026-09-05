import GafniTao.WooleySection10ActualStep
import GafniTao.WooleySection4Arithmetic

/-!
# Quantitative selection of Wooley's Section 6 hierarchy

This file replaces the paper's nested `epsilon << tau << delta << mu`
notation by explicit strict inequalities and finite thresholds.  The two
integer parameters are exactly those in (6.5) and (6.10).
-/

namespace GafniTao

noncomputable section

/-- The integer `theta = ceil(mu H)` from source equation (6.10). -/
def wooleyIterationTheta (mu : ℝ) (H : ℕ) : ℕ :=
  ⌈mu * (H : ℝ)⌉₊

theorem wooley_iterationTheta_lower
    {mu : ℝ} {H : ℕ} :
    mu * (H : ℝ) ≤ (wooleyIterationTheta mu H : ℝ) := by
  exact Nat.le_ceil _

theorem wooley_iterationTheta_lt_add_one
    {mu : ℝ} {H : ℕ} (hmu : 0 ≤ mu) :
    (wooleyIterationTheta mu H : ℝ) < mu * (H : ℝ) + 1 := by
  exact Nat.ceil_lt_add_one (mul_nonneg hmu (Nat.cast_nonneg H))

theorem wooley_initialNu_lt_add_one
    {epsilon Lambda : ℝ} {H : ℕ}
    (hepsilon : 0 ≤ epsilon) (hLambda : 0 < Lambda) :
    (wooleyInitialNu epsilon Lambda H : ℝ) <
      4 * epsilon * (H : ℝ) / Lambda + 1 := by
  exact Nat.ceil_lt_add_one
    (div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hepsilon)
      (Nat.cast_nonneg H)) hLambda.le)

/-- A positive gap between two linear slopes eventually absorbs a fixed
nonnegative additive loss. -/
theorem wooley_eventually_linear_gap
    {a b c : ℝ} (hab : a < b) :
    ∃ H0 : ℕ, ∀ H : ℕ, H0 ≤ H →
      a * (H : ℝ) + c ≤ b * (H : ℝ) := by
  obtain ⟨H0 : ℕ, hH0⟩ := exists_nat_ge (c / (b - a))
  refine ⟨H0, ?_⟩
  intro H hH
  have hgap : 0 < b - a := sub_pos.mpr hab
  have hH0H : (H0 : ℝ) ≤ H := by exact_mod_cast hH
  have hquot : c / (b - a) ≤ (H : ℝ) := hH0.trans hH0H
  have hcGap : c ≤ (b - a) * (H : ℝ) := by
    rw [div_le_iff₀ hgap] at hquot
    simpa [mul_comm] using hquot
  nlinarith

/-- Strict version of `wooley_eventually_linear_gap`; the extra unit is
the explicit reserve used to turn ceiling upper bounds into strict source
inequalities. -/
theorem wooley_eventually_linear_gap_strict
    {a b c : ℝ} (hab : a < b) :
    ∃ H0 : ℕ, ∀ H : ℕ, H0 ≤ H →
      a * (H : ℝ) + c < b * (H : ℝ) := by
  obtain ⟨H0, hH0⟩ := wooley_eventually_linear_gap (c := c + 1) hab
  refine ⟨H0, ?_⟩
  intro H hH
  have h := hH0 H hH
  linarith

/-- The ceiling-defined initial depth is eventually no larger than the
ceiling-defined iteration scale whenever its limiting slope is smaller. -/
theorem wooley_initialNu_le_iterationTheta_eventually
    {epsilon Lambda mu : ℝ}
    (hepsilon : 0 ≤ epsilon) (hLambda : 0 < Lambda)
    (hslope : 4 * epsilon / Lambda < mu) :
    ∃ H0 : ℕ, ∀ H : ℕ, H0 ≤ H →
      wooleyInitialNu epsilon Lambda H ≤ wooleyIterationTheta mu H := by
  obtain ⟨H0, hH0⟩ := wooley_eventually_linear_gap (c := 1) hslope
  refine ⟨H0, ?_⟩
  intro H hH
  have hnu := (wooley_initialNu_lt_add_one
    (H := H) hepsilon hLambda).le
  have hlin := hH0 H hH
  have htheta := wooley_iterationTheta_lower (mu := mu) (H := H)
  have hrewrite : 4 * epsilon * (H : ℝ) / Lambda =
      (4 * epsilon / Lambda) * (H : ℝ) := by
    field_simp
  rw [hrewrite] at hnu
  have hreal : (wooleyInitialNu epsilon Lambda H : ℝ) ≤
      (wooleyIterationTheta mu H : ℝ) := hnu.trans (hlin.trans htheta)
  exact_mod_cast hreal

/-- The source inequality `epsilon H <= theta` follows without an eventual
threshold when `epsilon <= mu`. -/
theorem wooley_H_mul_epsilon_le_iterationTheta
    {epsilon mu : ℝ} {H : ℕ} (hepsilonMu : epsilon ≤ mu) :
    (H : ℝ) * epsilon ≤ (wooleyIterationTheta mu H : ℝ) := by
  calc
    (H : ℝ) * epsilon ≤ (H : ℝ) * mu :=
      mul_le_mul_of_nonneg_left hepsilonMu (Nat.cast_nonneg H)
    _ = mu * (H : ℝ) := by ring
    _ ≤ (wooleyIterationTheta mu H : ℝ) := wooley_iterationTheta_lower

/-- A sufficiently small limiting iteration slope gives the maximal
Section-10 depth bound `k^(2N+1) theta <= H`. -/
theorem wooley_iterationTheta_scale_eventually
    {k N : ℕ} {mu : ℝ} (hmu : 0 ≤ mu)
    (hslope : (k : ℝ) ^ (2 * N + 1) * mu < 1) :
    ∃ H0 : ℕ, ∀ H : ℕ, H0 ≤ H →
      k ^ (2 * N + 1) * wooleyIterationTheta mu H ≤ H := by
  have hpow : (0 : ℝ) ≤ (k : ℝ) ^ (2 * N + 1) := by positivity
  obtain ⟨H0, hH0⟩ := wooley_eventually_linear_gap
    (c := (k : ℝ) ^ (2 * N + 1)) hslope
  refine ⟨H0, ?_⟩
  intro H hH
  have htheta := (wooley_iterationTheta_lt_add_one
    (H := H) hmu).le
  have hmul := mul_le_mul_of_nonneg_left htheta hpow
  have hlin := hH0 H hH
  have hreal : ((k ^ (2 * N + 1) * wooleyIterationTheta mu H : ℕ) : ℝ) ≤
      (H : ℝ) := by
    push_cast
    calc
      (k : ℝ) ^ (2 * N + 1) * (wooleyIterationTheta mu H : ℝ) ≤
          (k : ℝ) ^ (2 * N + 1) * (mu * (H : ℝ) + 1) := hmul
      _ = ((k : ℝ) ^ (2 * N + 1) * mu) * (H : ℝ) +
          (k : ℝ) ^ (2 * N + 1) := by ring
      _ ≤ (H : ℝ) := by simpa only [one_mul] using hlin
  exact_mod_cast hreal

/-- The strengthened maximal-scale estimate retains one integral unit.  In
combination with `k * ceil(B/k) < B+k`, this is exactly what converts the
height bound into the modulus bound required by Lemma 9.1. -/
theorem wooley_iterationTheta_scale_succ_eventually
    {k N : ℕ} {mu : ℝ} (hmu : 0 ≤ mu)
    (hslope : (k : ℝ) ^ (2 * N + 1) * mu < 1) :
    ∃ H0 : ℕ, ∀ H : ℕ, H0 ≤ H →
      k ^ (2 * N + 1) * wooleyIterationTheta mu H + 1 ≤ H := by
  have hpow : (0 : ℝ) ≤ (k : ℝ) ^ (2 * N + 1) := by positivity
  obtain ⟨H0, hH0⟩ := wooley_eventually_linear_gap
    (c := (k : ℝ) ^ (2 * N + 1) + 1) hslope
  refine ⟨H0, ?_⟩
  intro H hH
  have htheta := (wooley_iterationTheta_lt_add_one
    (H := H) hmu).le
  have hmul := mul_le_mul_of_nonneg_left htheta hpow
  have hlin := hH0 H hH
  have hreal :
      ((k ^ (2 * N + 1) * wooleyIterationTheta mu H + 1 : ℕ) : ℝ) ≤
        (H : ℝ) := by
    push_cast
    calc
      (k : ℝ) ^ (2 * N + 1) * (wooleyIterationTheta mu H : ℝ) + 1 ≤
          (k : ℝ) ^ (2 * N + 1) * (mu * (H : ℝ) + 1) + 1 :=
        by simpa only [add_comm] using add_le_add_right hmul 1
      _ = ((k : ℝ) ^ (2 * N + 1) * mu) * (H : ℝ) +
          ((k : ℝ) ^ (2 * N + 1) + 1) := by ring
      _ ≤ (H : ℝ) := by simpa only [one_mul] using hlin
  exact_mod_cast hreal

/-- A twofold reserve at the maximal recursion scale.  This is the form
used to absorb the uniform Lemma-4.1 constant, since every queried depth is
then at most `H/2`. -/
theorem wooley_iterationTheta_double_scale_succ_eventually
    {k N : ℕ} {mu : ℝ} (hmu : 0 ≤ mu)
    (hslope : 2 * (k : ℝ) ^ (2 * N + 1) * mu < 1) :
    ∃ H0 : ℕ, ∀ H : ℕ, H0 ≤ H →
      2 * (k ^ (2 * N + 1) * wooleyIterationTheta mu H) + 1 ≤ H := by
  have hpow : (0 : ℝ) ≤ 2 * (k : ℝ) ^ (2 * N + 1) := by positivity
  obtain ⟨H0, hH0⟩ := wooley_eventually_linear_gap
    (c := 2 * (k : ℝ) ^ (2 * N + 1) + 1) hslope
  refine ⟨H0, ?_⟩
  intro H hH
  have htheta := (wooley_iterationTheta_lt_add_one
    (H := H) hmu).le
  have hmul := mul_le_mul_of_nonneg_left htheta hpow
  have hlin := hH0 H hH
  have hreal :
      ((2 * (k ^ (2 * N + 1) * wooleyIterationTheta mu H) + 1 : ℕ) : ℝ) ≤
        (H : ℝ) := by
    push_cast
    calc
      2 * ((k : ℝ) ^ (2 * N + 1) *
          (wooleyIterationTheta mu H : ℝ)) + 1 ≤
        (2 * (k : ℝ) ^ (2 * N + 1)) * (mu * (H : ℝ) + 1) + 1 := by
          nlinarith
      _ = (2 * (k : ℝ) ^ (2 * N + 1) * mu) * (H : ℝ) +
          (2 * (k : ℝ) ^ (2 * N + 1) + 1) := by ring
      _ ≤ (H : ℝ) := by simpa only [one_mul] using hlin
  exact_mod_cast hreal

/-- Simultaneous ceiling ledger.  This single estimate is reused for the
four scale inequalities whose left sides are nonnegative linear
combinations of `theta=ceil(mu H)` and `nu=ceil(4 epsilon H/Lambda)`. -/
theorem wooley_theta_nu_linear_eventually
    {alpha beta target mu epsilon Lambda : ℝ}
    (halpha : 0 ≤ alpha) (hbeta : 0 ≤ beta) (htarget : 0 ≤ target)
    (hmu : 0 ≤ mu) (hepsilon : 0 ≤ epsilon) (hLambda : 0 < Lambda)
    (hslope : alpha * mu + beta * (4 * epsilon / Lambda) < target * mu) :
    ∃ H0 : ℕ, ∀ H : ℕ, H0 ≤ H →
      alpha * (wooleyIterationTheta mu H : ℝ) +
          beta * (wooleyInitialNu epsilon Lambda H : ℝ) ≤
        target * (wooleyIterationTheta mu H : ℝ) := by
  have hslopeLeft : 0 ≤ alpha * mu + beta * (4 * epsilon / Lambda) := by
    positivity
  have hadd : 0 ≤ alpha + beta := add_nonneg halpha hbeta
  obtain ⟨H0, hH0⟩ := wooley_eventually_linear_gap
    (c := alpha + beta) hslope
  refine ⟨H0, ?_⟩
  intro H hH
  have hthetaUpper := (wooley_iterationTheta_lt_add_one
    (H := H) hmu).le
  have hnuUpper := (wooley_initialNu_lt_add_one
    (H := H) hepsilon hLambda).le
  have hthetaLower := wooley_iterationTheta_lower (mu := mu) (H := H)
  have hleft :
      alpha * (wooleyIterationTheta mu H : ℝ) +
          beta * (wooleyInitialNu epsilon Lambda H : ℝ) ≤
        (alpha * mu + beta * (4 * epsilon / Lambda)) * (H : ℝ) +
          (alpha + beta) := by
    calc
      alpha * (wooleyIterationTheta mu H : ℝ) +
          beta * (wooleyInitialNu epsilon Lambda H : ℝ) ≤
        alpha * (mu * (H : ℝ) + 1) +
          beta * (4 * epsilon * (H : ℝ) / Lambda + 1) := by gcongr
      _ = (alpha * mu + beta * (4 * epsilon / Lambda)) * (H : ℝ) +
          (alpha + beta) := by
        field_simp
        ring
  calc
    alpha * (wooleyIterationTheta mu H : ℝ) +
        beta * (wooleyInitialNu epsilon Lambda H : ℝ) ≤
      (alpha * mu + beta * (4 * epsilon / Lambda)) * (H : ℝ) +
        (alpha + beta) := hleft
    _ ≤ target * mu * (H : ℝ) := hH0 H hH
    _ ≤ target * (wooleyIterationTheta mu H : ℝ) := by
      have := mul_le_mul_of_nonneg_left hthetaLower htarget
      convert this using 1
      · ring

/-- The strict quadratic-loss inequality in the Section-9 admissibility
ledger. -/
theorem wooley_theta_epsilon_sq_lt_nu_eventually
    {alpha mu epsilon Lambda : ℝ}
    (halpha : 0 ≤ alpha) (hmu : 0 ≤ mu)
    (hepsilon : 0 < epsilon) (hLambda : 0 < Lambda)
    (hslope : alpha * mu * epsilon ^ 2 < 4 * epsilon / Lambda) :
    ∃ H0 : ℕ, ∀ H : ℕ, H0 ≤ H →
      alpha * (wooleyIterationTheta mu H : ℝ) * epsilon ^ 2 <
        (wooleyInitialNu epsilon Lambda H : ℝ) := by
  have hcoef : 0 ≤ alpha * epsilon ^ 2 := mul_nonneg halpha (sq_nonneg epsilon)
  have hslope' : alpha * epsilon ^ 2 * mu < 4 * epsilon / Lambda := by
    nlinarith
  obtain ⟨H0, hH0⟩ := wooley_eventually_linear_gap_strict
    (c := alpha * epsilon ^ 2) hslope'
  refine ⟨H0, ?_⟩
  intro H hH
  have htheta := (wooley_iterationTheta_lt_add_one
    (H := H) hmu).le
  have hleft := mul_le_mul_of_nonneg_left htheta hcoef
  have hlinear := hH0 H hH
  have hnuLower := wooley_initialNu_lower
    (epsilon := epsilon) (Lambda := Lambda) (H := H)
  calc
    alpha * (wooleyIterationTheta mu H : ℝ) * epsilon ^ 2 =
        (alpha * epsilon ^ 2) * (wooleyIterationTheta mu H : ℝ) := by ring
    _ ≤ (alpha * epsilon ^ 2) * (mu * (H : ℝ) + 1) := hleft
    _ = (alpha * epsilon ^ 2 * mu) * (H : ℝ) +
        alpha * epsilon ^ 2 := by ring
    _ < (4 * epsilon / Lambda) * (H : ℝ) := hlinear
    _ = 4 * epsilon * (H : ℝ) / Lambda := by
      field_simp
    _ ≤ (wooleyInitialNu epsilon Lambda H : ℝ) := hnuLower

/-- The exact global arithmetic data needed to validate every bounded node
of the Section-10 recursion.  All quantities here occur literally in
`wooleySection10NodeHierarchy_of_global`. -/
def WooleySection10GlobalHierarchy
    (k N H thetaNat nu : ℕ) (Lambda delta tau epsilon : ℝ) : Prop :=
  1 ≤ thetaNat ∧
  1 ≤ nu ∧
  nu ≤ thetaNat ∧
  2 * (k ^ (2 * N + 1) * thetaNat) + 1 ≤ H ∧
  ((4 * k ^ 3 * nu : ℕ) : ℝ) ≤
    (k : ℝ) ^ 2 * (delta * (thetaNat : ℝ)) ∧
  tau * ((k * (k ^ (2 * N) * thetaNat) : ℕ) : ℝ) +
      ((k * nu : ℕ) : ℝ) ≤ delta * (thetaNat : ℝ) ∧
  tau * ((k ^ 2 * (k ^ (2 * N) * thetaNat) : ℕ) : ℝ) +
      ((k * nu : ℕ) : ℝ) ≤
    (k : ℝ) ^ 2 * (delta * (thetaNat : ℝ)) ∧
  ((k ^ 2 * (k ^ (2 * N) * thetaNat) : ℕ) : ℝ) * epsilon ^ 2 <
    (nu : ℝ) ∧
  2 * ((k ^ 5 * nu : ℕ) : ℝ) ≤
    ((k : ℝ) ^ 2 * (delta * (thetaNat : ℝ))) * Lambda

/-- Explicit eventual realization of the global hierarchy.  Its hypotheses
are precisely the strict inequalities between the limiting slopes; the
proof absorbs every `Nat.ceil` endpoint by a finite lower threshold for
`H`. -/
theorem wooley_section10_globalHierarchy_eventually
    {k N : ℕ} {Lambda mu delta tau epsilon : ℝ}
    (hk : 2 ≤ k) (hLambda : 0 < Lambda)
    (hmu : 0 < mu) (hdelta : 0 ≤ delta) (htau : 0 ≤ tau)
    (hepsilon : 0 < epsilon)
    (hscaleSlope : 2 * (k : ℝ) ^ (2 * N + 1) * mu < 1)
    (hnuThetaSlope : 4 * epsilon / Lambda < mu)
    (hnuScaleSlope :
      (4 * (k : ℝ) ^ 3) * (4 * epsilon / Lambda) <
        ((k : ℝ) ^ 2 * delta) * mu)
    (hcurrentSlope :
      (tau * (k : ℝ) ^ (2 * N + 1)) * mu +
          (k : ℝ) * (4 * epsilon / Lambda) < delta * mu)
    (hsecondSlope :
      (tau * (k : ℝ) ^ (2 * N + 2)) * mu +
          (k : ℝ) * (4 * epsilon / Lambda) <
        ((k : ℝ) ^ 2 * delta) * mu)
    (hepsilonSlope :
      (k : ℝ) ^ (2 * N + 2) * mu * epsilon ^ 2 <
        4 * epsilon / Lambda)
    (hhierarchySlope :
      (2 * (k : ℝ) ^ 5) * (4 * epsilon / Lambda) <
        ((k : ℝ) ^ 2 * delta * Lambda) * mu) :
    ∃ H0 : ℕ, ∀ H : ℕ, H0 ≤ H →
      WooleySection10GlobalHierarchy k N H
        (wooleyIterationTheta mu H)
        (wooleyInitialNu epsilon Lambda H) Lambda delta tau epsilon := by
  obtain ⟨Hscale, hHscale⟩ :=
    wooley_iterationTheta_double_scale_succ_eventually hmu.le hscaleSlope
  obtain ⟨HnuTheta, hHnuTheta⟩ :=
    wooley_initialNu_le_iterationTheta_eventually hepsilon.le hLambda
      hnuThetaSlope
  obtain ⟨HnuScale, hHnuScale⟩ :=
    wooley_theta_nu_linear_eventually
      (alpha := 0) (beta := 4 * (k : ℝ) ^ 3)
      (target := (k : ℝ) ^ 2 * delta)
      (by norm_num) (by positivity) (by positivity) hmu.le hepsilon.le
      hLambda (by simpa only [zero_mul, zero_add] using hnuScaleSlope)
  obtain ⟨Hcurrent, hHcurrent⟩ :=
    wooley_theta_nu_linear_eventually
      (alpha := tau * (k : ℝ) ^ (2 * N + 1)) (beta := k)
      (target := delta) (by positivity) (by positivity) hdelta hmu.le
      hepsilon.le hLambda hcurrentSlope
  obtain ⟨Hsecond, hHsecond⟩ :=
    wooley_theta_nu_linear_eventually
      (alpha := tau * (k : ℝ) ^ (2 * N + 2)) (beta := k)
      (target := (k : ℝ) ^ 2 * delta)
      (by positivity) (by positivity) (by positivity) hmu.le hepsilon.le
      hLambda hsecondSlope
  obtain ⟨Hepsilon, hHepsilon⟩ :=
    wooley_theta_epsilon_sq_lt_nu_eventually
      (alpha := (k : ℝ) ^ (2 * N + 2))
      (by positivity) hmu.le hepsilon hLambda hepsilonSlope
  obtain ⟨Hhierarchy, hHhierarchy⟩ :=
    wooley_theta_nu_linear_eventually
      (alpha := 0) (beta := 2 * (k : ℝ) ^ 5)
      (target := (k : ℝ) ^ 2 * delta * Lambda)
      (by norm_num) (by positivity) (by positivity) hmu.le hepsilon.le
      hLambda (by simpa only [zero_mul, zero_add] using hhierarchySlope)
  let H0 := max 1 (max Hscale (max HnuTheta
    (max HnuScale (max Hcurrent (max Hsecond (max Hepsilon Hhierarchy))))))
  refine ⟨H0, ?_⟩
  intro H hH
  have hHone : 1 ≤ H := (le_max_left 1 _).trans hH
  have hscale : Hscale ≤ H := by
    exact (le_max_left Hscale _).trans
      ((le_max_right 1 _).trans hH)
  have hnuTheta : HnuTheta ≤ H := by
    exact (le_max_left HnuTheta _).trans
      ((le_max_right Hscale _).trans ((le_max_right 1 _).trans hH))
  have hnuScale : HnuScale ≤ H := by
    exact (le_max_left HnuScale _).trans
      ((le_max_right HnuTheta _).trans
        ((le_max_right Hscale _).trans ((le_max_right 1 _).trans hH)))
  have hcurrent : Hcurrent ≤ H := by
    exact (le_max_left Hcurrent _).trans
      ((le_max_right HnuScale _).trans
        ((le_max_right HnuTheta _).trans
          ((le_max_right Hscale _).trans ((le_max_right 1 _).trans hH))))
  have hsecond : Hsecond ≤ H := by
    exact (le_max_left Hsecond _).trans
      ((le_max_right Hcurrent _).trans
        ((le_max_right HnuScale _).trans
          ((le_max_right HnuTheta _).trans
            ((le_max_right Hscale _).trans ((le_max_right 1 _).trans hH)))))
  have hepsH : Hepsilon ≤ H := by
    exact (le_max_left Hepsilon _).trans
      ((le_max_right Hsecond _).trans
        ((le_max_right Hcurrent _).trans
          ((le_max_right HnuScale _).trans
            ((le_max_right HnuTheta _).trans
              ((le_max_right Hscale _).trans ((le_max_right 1 _).trans hH))))))
  have hhierH : Hhierarchy ≤ H := by
    exact (le_max_right Hepsilon Hhierarchy).trans
      ((le_max_right Hsecond _).trans
        ((le_max_right Hcurrent _).trans
          ((le_max_right HnuScale _).trans
            ((le_max_right HnuTheta _).trans
              ((le_max_right Hscale _).trans ((le_max_right 1 _).trans hH))))))
  have hthetaPosR : 0 < (wooleyIterationTheta mu H : ℝ) := by
    have hlow := wooley_iterationTheta_lower (mu := mu) (H := H)
    have hHR : (0 : ℝ) < H := by exact_mod_cast (show 0 < H by omega)
    exact lt_of_lt_of_le (mul_pos hmu hHR) hlow
  have hnuPosR : 0 < (wooleyInitialNu epsilon Lambda H : ℝ) := by
    have hlow := wooley_initialNu_lower
      (epsilon := epsilon) (Lambda := Lambda) (H := H)
    have hHR : (0 : ℝ) < H := by exact_mod_cast (show 0 < H by omega)
    have hraw : 0 < 4 * epsilon * (H : ℝ) / Lambda := by positivity
    exact lt_of_lt_of_le hraw hlow
  refine ⟨by exact_mod_cast hthetaPosR, by exact_mod_cast hnuPosR,
    hHnuTheta H hnuTheta, hHscale H hscale, ?_, ?_, ?_, ?_, ?_⟩
  · have h := hHnuScale H hnuScale
    push_cast at h ⊢
    simpa only [zero_mul, zero_add, mul_assoc] using h
  · have h := hHcurrent H hcurrent
    push_cast at h ⊢
    convert h using 1
    all_goals ring
  · have h := hHsecond H hsecond
    push_cast at h ⊢
    convert h using 1
    all_goals ring
  · have h := hHepsilon H hepsH
    push_cast at h ⊢
    convert h using 1
    all_goals ring
  · have h := hHhierarchy H hhierH
    push_cast at h ⊢
    convert h using 1
    all_goals ring

set_option maxHeartbeats 1000000 in
/-- Source hierarchy (6.2), with explicit quantitative reserves sufficient
for every slope hypothesis of `wooley_section10_globalHierarchy_eventually`.
The witnesses depend only on `k`, the finite iteration length `N`, and the
positive normalization exponent `Lambda`. -/
theorem wooley_section10_slopeHierarchy_exists
    {k N : ℕ} {Lambda : ℝ} (hk : 2 ≤ k) (hLambda : 0 < Lambda) :
    ∃ mu delta tau epsilon : ℝ,
      0 < epsilon ∧ epsilon < tau ∧ tau < delta ∧ delta < mu ∧ mu < 1 ∧
      (k : ℝ) ^ 2 * delta ≤ 1 ∧
      4 * tau * (k : ℝ) ^ 2 ≤ 1 ∧
      epsilon ≤ mu ∧
      2 * (k : ℝ) ^ (2 * N + 1) * mu < 1 ∧
      4 * epsilon / Lambda < mu ∧
      (4 * (k : ℝ) ^ 3) * (4 * epsilon / Lambda) <
        ((k : ℝ) ^ 2 * delta) * mu ∧
      (tau * (k : ℝ) ^ (2 * N + 1)) * mu +
          (k : ℝ) * (4 * epsilon / Lambda) < delta * mu ∧
      (tau * (k : ℝ) ^ (2 * N + 2)) * mu +
          (k : ℝ) * (4 * epsilon / Lambda) <
        ((k : ℝ) ^ 2 * delta) * mu ∧
      (k : ℝ) ^ (2 * N + 2) * mu * epsilon ^ 2 <
        4 * epsilon / Lambda ∧
      (2 * (k : ℝ) ^ 5) * (4 * epsilon / Lambda) <
        ((k : ℝ) ^ 2 * delta * Lambda) * mu := by
  let K1 : ℝ := (k : ℝ) ^ (2 * N + 1)
  let K2 : ℝ := (k : ℝ) ^ (2 * N + 2)
  let mu : ℝ := 1 / (4 * K1)
  let delta : ℝ := mu / (4 * (k : ℝ) ^ 2)
  let tau : ℝ := delta / (8 * K2)
  let E3 : ℝ := delta * mu * Lambda / (64 * (k : ℝ) ^ 3)
  let E4 : ℝ := delta * Lambda ^ 2 * mu / (16 * (k : ℝ) ^ 3)
  let E5 : ℝ := 2 / (K2 * mu * Lambda)
  let cap : ℝ := min tau (min mu
    (min (Lambda * mu / 8) (min E3 (min E4 E5))))
  let epsilon : ℝ := cap / 2
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hK1 : 0 < K1 := by dsimp [K1]; positivity
  have hK2 : 0 < K2 := by dsimp [K2]; positivity
  have hmu : 0 < mu := by dsimp [mu]; positivity
  have hmuOne : mu < 1 := by
    dsimp [mu, K1]
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < 4 * (k : ℝ) ^ (2 * N + 1))]
    have hpowOne : (1 : ℝ) ≤ (k : ℝ) ^ (2 * N + 1) :=
      one_le_pow₀ (by linarith)
    nlinarith
  have hdelta : 0 < delta := by dsimp [delta]; positivity
  have hdeltaMu : delta < mu := by
    dsimp [delta]
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < 4 * (k : ℝ) ^ 2)]
    have hden : (1 : ℝ) < 4 * (k : ℝ) ^ 2 := by
      nlinarith [sq_nonneg (k : ℝ)]
    simpa only [one_mul, mul_one] using mul_lt_mul_of_pos_left hden hmu
  have htau : 0 < tau := by dsimp [tau]; positivity
  have htauDelta : tau < delta := by
    dsimp [tau]
    rw [div_lt_iff₀ (by positivity : 0 < 8 * K2)]
    have hden : (1 : ℝ) < 8 * K2 := by
      have hK2one : (1 : ℝ) ≤ K2 := by
        dsimp [K2]
        exact one_le_pow₀ (by linarith : (1 : ℝ) ≤ k)
      nlinarith
    simpa only [one_mul, mul_one] using mul_lt_mul_of_pos_left hden hdelta
  have hE3 : 0 < E3 := by dsimp [E3]; positivity
  have hE4 : 0 < E4 := by dsimp [E4]; positivity
  have hE5 : 0 < E5 := by dsimp [E5]; positivity
  have hcap : 0 < cap := by dsimp [cap]; positivity
  have hepsilon : 0 < epsilon := by dsimp [epsilon]; linarith
  have hepsilonCap : epsilon < cap := by dsimp [epsilon]; linarith
  have hcapTau : cap ≤ tau := by dsimp [cap]; exact min_le_left _ _
  have hcapMu : cap ≤ mu := by
    dsimp [cap]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hcapLMu : cap ≤ Lambda * mu / 8 := by
    dsimp [cap]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hcapE3 : cap ≤ E3 := by
    dsimp [cap]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))
  have hcapE4 : cap ≤ E4 := by
    dsimp [cap]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hcapE5 : cap ≤ E5 := by
    dsimp [cap]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  have hepsTau : epsilon < tau := hepsilonCap.trans_le hcapTau
  have hepsMu : epsilon ≤ mu := hepsilonCap.le.trans hcapMu
  have hepsLMu : epsilon < Lambda * mu / 8 := hepsilonCap.trans_le hcapLMu
  have hepsE3 : epsilon < E3 := hepsilonCap.trans_le hcapE3
  have hepsE4 : epsilon < E4 := hepsilonCap.trans_le hcapE4
  have hepsE5 : epsilon < E5 := hepsilonCap.trans_le hcapE5
  have hE3Raw : epsilon * (64 * (k : ℝ) ^ 3) <
      delta * mu * Lambda := by
    dsimp [E3] at hepsE3
    exact (lt_div_iff₀ (by positivity : (0 : ℝ) < 64 * (k : ℝ) ^ 3)).mp
      hepsE3
  have hE4Raw : epsilon * (16 * (k : ℝ) ^ 3) <
      delta * Lambda ^ 2 * mu := by
    dsimp [E4] at hepsE4
    exact (lt_div_iff₀ (by positivity : (0 : ℝ) < 16 * (k : ℝ) ^ 3)).mp
      hepsE4
  have hE5Raw : epsilon * (K2 * mu * Lambda) < 2 := by
    dsimp [E5] at hepsE5
    exact (lt_div_iff₀ (by positivity : 0 < K2 * mu * Lambda)).mp hepsE5
  have hkCubic : (16 : ℝ) * k ≤ 64 * (k : ℝ) ^ 3 := by
    have hk0 : (0 : ℝ) ≤ k := by linarith
    have hfactor : 0 ≤ (k : ℝ) * (4 * (k : ℝ) ^ 2 - 1) :=
      mul_nonneg hk0 (by nlinarith [sq_nonneg (k : ℝ)])
    nlinarith
  have hVsmall : (k : ℝ) * (4 * epsilon / Lambda) <
      delta * mu / 4 := by
    rw [show (k : ℝ) * (4 * epsilon / Lambda) =
      (4 * (k : ℝ) * epsilon) / Lambda by ring]
    rw [div_lt_iff₀ hLambda]
    have hscaled := mul_le_mul_of_nonneg_right hkCubic hepsilon.le
    nlinarith [hE3Raw]
  refine ⟨mu, delta, tau, epsilon, hepsilon, hepsTau, htauDelta,
    hdeltaMu, hmuOne, ?_, ?_, hepsMu, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [delta]
    field_simp
    nlinarith
  · dsimp [tau, delta]
    have hK2one : 1 ≤ K2 := by
      dsimp [K2]
      exact one_le_pow₀ (by linarith : (1 : ℝ) ≤ k)
    field_simp
    nlinarith
  · dsimp [mu, K1]
    field_simp
    norm_num
  · have h := hepsLMu
    field_simp at h ⊢
    nlinarith
  · rw [show (4 * (k : ℝ) ^ 3) * (4 * epsilon / Lambda) =
      (16 * (k : ℝ) ^ 3 * epsilon) / Lambda by ring]
    rw [div_lt_iff₀ hLambda]
    have hkSqOne : (1 : ℝ) ≤ (k : ℝ) ^ 2 := by
      nlinarith [sq_nonneg (k : ℝ)]
    have hright : delta * mu * Lambda ≤
        (k : ℝ) ^ 2 * delta * mu * Lambda := by
      have := mul_le_mul_of_nonneg_right hkSqOne
        (mul_nonneg (mul_nonneg hdelta.le hmu.le) hLambda.le)
      nlinarith
    nlinarith [hE3Raw]
  · have hTauK1 : tau * K1 = delta / (8 * (k : ℝ)) := by
      dsimp [tau, K2, K1]
      field_simp
      ring
    rw [show (k : ℝ) ^ (2 * N + 1) = K1 by rfl]
    rw [hTauK1]
    have hfirst : delta / (8 * (k : ℝ)) * mu ≤ delta * mu / 16 := by
      rw [div_mul_eq_mul_div]
      apply div_le_div_of_nonneg_left (mul_nonneg hdelta.le hmu.le)
        (by norm_num)
      nlinarith
    have hsum : delta / (8 * (k : ℝ)) * mu +
        (k : ℝ) * (4 * epsilon / Lambda) < delta * mu := by
      nlinarith [hfirst, hVsmall, mul_pos hdelta hmu]
    exact hsum
  · have hTauK2 : tau * K2 = delta / 8 := by
      dsimp [tau]
      field_simp
    rw [show (k : ℝ) ^ (2 * N + 2) = K2 by rfl]
    rw [hTauK2]
    have hfirst : delta / 8 * mu = delta * mu / 8 := by ring
    rw [hfirst]
    have hkSq : (4 : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith [sq_nonneg (k : ℝ)]
    have htarget : delta * mu ≤ (k : ℝ) ^ 2 * delta * mu := by
      have := mul_le_mul_of_nonneg_right hkSq (mul_nonneg hdelta.le hmu.le)
      nlinarith
    have hsum : delta * mu / 8 +
        (k : ℝ) * (4 * epsilon / Lambda) < delta * mu := by
      nlinarith [hVsmall, mul_pos hdelta hmu]
    exact hsum.trans_le htarget
  ·
    rw [show (k : ℝ) ^ (2 * N + 2) = K2 by rfl]
    apply (lt_div_iff₀ hLambda).2
    have hmul := mul_lt_mul_of_pos_left hE5Raw hepsilon
    nlinarith [hmul]
  · rw [show (2 * (k : ℝ) ^ 5) * (4 * epsilon / Lambda) =
      (8 * (k : ℝ) ^ 5 * epsilon) / Lambda by ring]
    rw [div_lt_iff₀ hLambda]
    have hmul := mul_lt_mul_of_pos_left hE4Raw
      (show 0 < (k : ℝ) ^ 2 / 2 by positivity)
    have hconverted : 8 * (k : ℝ) ^ 5 * epsilon <
        ((k : ℝ) ^ 2 / 2) * (delta * Lambda ^ 2 * mu) := by
      convert hmul using 1
      · ring
    have hright : ((k : ℝ) ^ 2 / 2) * (delta * Lambda ^ 2 * mu) <
        (k : ℝ) ^ 2 * delta * Lambda * mu * Lambda := by
      nlinarith [mul_pos (mul_pos (mul_pos (sq_pos_of_pos (by linarith : (0 : ℝ) < k))
        hdelta) (sq_pos_of_pos hLambda)) hmu]
    exact hconverted.trans hright

/-- Fully quantified replacement for the informal hierarchy declaration
(6.2): the four positive parameters are selected first, and one finite
height threshold then validates the entire global recursion ledger. -/
theorem wooley_section10_hierarchy_exists
    {k N : ℕ} {Lambda : ℝ} (hk : 2 ≤ k) (hLambda : 0 < Lambda) :
    ∃ mu delta tau epsilon : ℝ, ∃ H0 : ℕ,
      0 < epsilon ∧ epsilon < tau ∧ tau < delta ∧ delta < mu ∧ mu < 1 ∧
      (k : ℝ) ^ 2 * delta ≤ 1 ∧
      4 * tau * (k : ℝ) ^ 2 ≤ 1 ∧ epsilon ≤ mu ∧
      ∀ H : ℕ, H0 ≤ H →
        WooleySection10GlobalHierarchy k N H
          (wooleyIterationTheta mu H)
          (wooleyInitialNu epsilon Lambda H) Lambda delta tau epsilon := by
  obtain ⟨mu, delta, tau, epsilon, hepsilon, hepsilonTau,
    htauDelta, hdeltaMu, hmuOne, hdeltaScale, htauScale,
    hepsilonMu, hscaleSlope, hnuThetaSlope, hnuScaleSlope,
    hcurrentSlope, hsecondSlope, hepsilonSlope, hhierarchySlope⟩ :=
      wooley_section10_slopeHierarchy_exists hk hLambda
  obtain ⟨H0, hH0⟩ := wooley_section10_globalHierarchy_eventually
    hk hLambda
    (lt_trans (lt_trans (lt_trans hepsilon hepsilonTau) htauDelta) hdeltaMu)
    (lt_trans (lt_trans hepsilon hepsilonTau) htauDelta).le
    (lt_trans hepsilon hepsilonTau).le hepsilon
    hscaleSlope hnuThetaSlope hnuScaleSlope hcurrentSlope hsecondSlope
    hepsilonSlope hhierarchySlope
  exact ⟨mu, delta, tau, epsilon, H0, hepsilon, hepsilonTau,
    htauDelta, hdeltaMu, hmuOne, hdeltaScale, htauScale, hepsilonMu, hH0⟩

/-- The one-unit reserve in the height ledger gives both physical scale
bounds when `H=ceil(B/k)`. -/
theorem WooleySection10GlobalHierarchy.physical_scales
    {k N B H thetaNat nu : ℕ} {Lambda delta tau epsilon : ℝ}
    (hk : 1 ≤ k) (hH : H = B ⌈/⌉ k)
    (h : WooleySection10GlobalHierarchy k N H thetaNat nu
      Lambda delta tau epsilon) :
    k ^ (2 * N + 2) * thetaNat ≤ B ∧
      k ^ (2 * N + 1) * thetaNat ≤ H := by
  rcases h with ⟨htheta, hnu, hnuTheta, hscaleSucc, hrest⟩
  have hceil : k * H < B + k := by
    simpa only [hH] using wooley_mul_ceilDiv_lt_add (B := B) hk
  have hscaleH : k ^ (2 * N + 1) * thetaNat ≤ H := by omega
  have hmul : k * (k ^ (2 * N + 1) * thetaNat) ≤ B := by
    have hscaleSuccSingle :
        k ^ (2 * N + 1) * thetaNat + 1 ≤ H := by omega
    have hscaled := Nat.mul_le_mul_left k hscaleSuccSingle
    have hstrict : k * (k ^ (2 * N + 1) * thetaNat) + k < B + k := by
      apply lt_of_le_of_lt _ hceil
      simpa only [Nat.mul_add, Nat.mul_one] using hscaled
    omega
  have heq : k ^ (2 * N + 2) * thetaNat =
      k * (k ^ (2 * N + 1) * thetaNat) := by
    rw [show 2 * N + 2 = (2 * N + 1) + 1 by omega, pow_succ]
    ring
  exact ⟨by simpa only [heq] using hmul, hscaleH⟩

/-- The global hierarchy is a complete consumer for the per-node arithmetic
obligations; no scale hypothesis remains to be supplied during recursion. -/
theorem wooley_section10_nodes_of_globalHierarchy
    {k N B H thetaNat nu : ℕ} {Lambda delta tau epsilon : ℝ}
    (hk : 2 ≤ k) (hLambda : 0 < Lambda) (htau : 0 ≤ tau)
    (hH : H = B ⌈/⌉ k)
    (hglobal : WooleySection10GlobalHierarchy k N H thetaNat nu
      Lambda delta tau epsilon) :
    ∀ m b : ℕ, m < N → b ≤ k ^ (2 * m) * thetaNat →
      (k : ℝ) ^ 2 * (delta * (thetaNat : ℝ)) ≤ (b : ℝ) →
      WooleySection10NodeHierarchy k B H nu thetaNat m b
        Lambda delta tau epsilon := by
  rcases hglobal with ⟨htheta, hnu, hnuTheta, hscaleSucc,
    hnuScale, hcurrent, hsecond, heps, hhierarchy⟩
  have hphysical := WooleySection10GlobalHierarchy.physical_scales
    (show 1 ≤ k by omega) hH
      ⟨htheta, hnu, hnuTheta, hscaleSucc, hnuScale,
        hcurrent, hsecond, heps, hhierarchy⟩
  intro m b hm hb hstate
  exact wooleySection10NodeHierarchy_of_global hk hLambda htau hm hb hstate
    hnuScale hphysical.1 hphysical.2 hcurrent hsecond heps hhierarchy

/-- Once the conditioning depth has been selected, decreasing the iteration
loss preserves the complete global hierarchy. -/
theorem WooleySection10GlobalHierarchy.mono_epsilon
    {k N H thetaNat nu : ℕ} {Lambda delta tau epsilon epsilon' : ℝ}
    (hepsilon' : 0 ≤ epsilon') (hepsilon : epsilon' ≤ epsilon)
    (h : WooleySection10GlobalHierarchy k N H thetaNat nu
      Lambda delta tau epsilon) :
    WooleySection10GlobalHierarchy k N H thetaNat nu
      Lambda delta tau epsilon' := by
  rcases h with ⟨htheta, hnu, hnuTheta, hscale, hnuScale,
    hcurrent, hsecond, hepsilonSmall, hhierarchy⟩
  have hepsilon0 : 0 ≤ epsilon := le_trans hepsilon' hepsilon
  have hsquare : epsilon' ^ 2 ≤ epsilon ^ 2 := by nlinarith
  have hfactor : (0 : ℝ) ≤
      ((k ^ 2 * (k ^ (2 * N) * thetaNat) : ℕ) : ℝ) := by positivity
  refine ⟨htheta, hnu, hnuTheta, hscale, hnuScale,
    hcurrent, hsecond, ?_, hhierarchy⟩
  exact (mul_le_mul_of_nonneg_left hsquare hfactor).trans_lt hepsilonSmall

/-- Decreasing the source spacing parameter enlarges `Phi_tau` and also
preserves every numerical inequality in the global hierarchy. -/
theorem WooleySection10GlobalHierarchy.mono_tau
    {k N H thetaNat nu : ℕ} {Lambda delta tau tau' epsilon : ℝ}
    (htau : tau' ≤ tau)
    (h : WooleySection10GlobalHierarchy k N H thetaNat nu
      Lambda delta tau epsilon) :
    WooleySection10GlobalHierarchy k N H thetaNat nu
      Lambda delta tau' epsilon := by
  rcases h with ⟨htheta, hnu, hnuTheta, hscale, hnuScale,
    hcurrent, hsecond, hepsilonSmall, hhierarchy⟩
  refine ⟨htheta, hnu, hnuTheta, hscale, hnuScale, ?_, ?_,
    hepsilonSmall, hhierarchy⟩
  · calc
      tau' * ((k * (k ^ (2 * N) * thetaNat) : ℕ) : ℝ) +
          ((k * nu : ℕ) : ℝ) ≤
        tau * ((k * (k ^ (2 * N) * thetaNat) : ℕ) : ℝ) +
          ((k * nu : ℕ) : ℝ) := by gcongr
      _ ≤ delta * (thetaNat : ℝ) := hcurrent
  · calc
      tau' * ((k ^ 2 * (k ^ (2 * N) * thetaNat) : ℕ) : ℝ) +
          ((k * nu : ℕ) : ℝ) ≤
        tau * ((k ^ 2 * (k ^ (2 * N) * thetaNat) : ℕ) : ℝ) +
          ((k * nu : ℕ) : ℝ) := by gcongr
      _ ≤ (k : ℝ) ^ 2 * (delta * (thetaNat : ℝ)) := hsecond

#print axioms wooleyIterationTheta
#print axioms wooley_iterationTheta_lower
#print axioms wooley_iterationTheta_lt_add_one
#print axioms wooley_initialNu_lt_add_one
#print axioms wooley_eventually_linear_gap
#print axioms wooley_eventually_linear_gap_strict
#print axioms wooley_initialNu_le_iterationTheta_eventually
#print axioms wooley_H_mul_epsilon_le_iterationTheta
#print axioms wooley_iterationTheta_scale_eventually
#print axioms wooley_iterationTheta_scale_succ_eventually
#print axioms wooley_iterationTheta_double_scale_succ_eventually
#print axioms wooley_theta_nu_linear_eventually
#print axioms wooley_theta_epsilon_sq_lt_nu_eventually
#print axioms WooleySection10GlobalHierarchy
#print axioms wooley_section10_globalHierarchy_eventually
#print axioms wooley_section10_slopeHierarchy_exists
#print axioms wooley_section10_hierarchy_exists
#print axioms WooleySection10GlobalHierarchy.physical_scales
#print axioms wooley_section10_nodes_of_globalHierarchy
#print axioms WooleySection10GlobalHierarchy.mono_epsilon
#print axioms WooleySection10GlobalHierarchy.mono_tau

end

end GafniTao
