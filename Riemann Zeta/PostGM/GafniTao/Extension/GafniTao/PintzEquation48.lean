import GafniTao.PintzEquation46Lower

/-!
# Pintz equations (4.8)--(4.10)

This module estimates the literal factor `f_j` occurring after the contour
shift.  The first bound deliberately keeps a supplied zeta-window majorant
visible; later modules discharge that majorant from the proved Ford growth
theorem.  The resulting selection theorem acts on the actual finite Mobius
polynomial and not on an abstract large-value certificate.
-/

open Complex MeasureTheory Set

namespace GafniTao

open RiemannZeta.GuthMaynard

noncomputable section

/-- A convenient explicit majorant for the integral in Pintz (4.8).  It is
slightly coarser than the source logarithmic factor, but retains the decisive
`exp (-lambda * Delta)` saving and every parameter is visible. -/
noncomputable def pintzEquation48Majorant
    (Delta lambda Z : ℝ) : ℝ :=
  4 * lambda * (Z / Delta) * Real.exp (1 / 4 - lambda * Delta)

/-- Pointwise estimate for the literal equation-(4.7) factor. -/
theorem norm_pintzF_le
    {Delta eta etaJ gamma lambda t Z : ℝ}
    (hDelta : 0 < Delta) (hdeltaJ : 0 <= pintzDeltaJ eta etaJ)
    (hetaJ : 0 <= etaJ) (hxi : pintzXi Delta eta <= 1 / 2)
    (hlambda : 1 <= lambda) (hZ : 0 <= Z)
    (hZeta : ‖riemannZeta
      ((1 - pintzXi Delta eta : ℝ) + I * (gamma + t))‖ <= Z) :
    ‖pintzF Delta eta etaJ gamma lambda t‖ <=
      (Z / Delta) * Real.exp (1 / 4 - lambda * Delta) := by
  let a : ℝ := Delta + pintzDeltaJ eta etaJ
  let s : ℂ := (pintzLeftEdge Delta eta etaJ : ℝ) + I * t
  have haDelta : Delta <= a := by
    dsimp [a]
    linarith
  have haPos : 0 < a := hDelta.trans_le haDelta
  have haXi : a <= pintzXi Delta eta := by
    dsimp [a]
    unfold pintzDeltaJ pintzXi
    linarith
  have haHalf : a <= 1 / 2 := haXi.trans hxi
  have hleft : pintzLeftEdge Delta eta etaJ = -a := by
    unfold pintzLeftEdge
    dsimp [a]
    ring
  have hden : Delta <= ‖s‖ := by
    calc
      Delta <= |pintzLeftEdge Delta eta etaJ| := by
        rw [hleft, abs_neg, abs_of_pos haPos]
        exact haDelta
      _ <= ‖s‖ := by
        simpa [s] using Complex.abs_re_le_norm s
  have hdenPos : 0 < ‖s‖ := hDelta.trans_le hden
  have haSq : a ^ 2 <= 1 / 4 := by nlinarith
  have hdiv : a ^ 2 / lambda <= 1 / 4 := by
    have hlambdaPos : 0 < lambda := zero_lt_one.trans_le hlambda
    calc
      a ^ 2 / lambda <= (1 / 4) / lambda :=
        div_le_div_of_nonneg_right haSq hlambdaPos.le
      _ <= 1 / 4 := by
        rw [div_le_iff₀ hlambdaPos]
        nlinarith
  have hgauss : ‖pintzGaussianNumerator lambda s‖ <=
      Real.exp (1 / 4 - lambda * Delta) := by
    dsimp [s]
    rw [hleft, norm_pintzGaussianNumerator_vertical lambda (-a) t
      (zero_lt_one.trans_le hlambda)]
    apply Real.exp_le_exp.mpr
    have htSq : 0 <= t ^ 2 := sq_nonneg t
    have hlambdaPos : 0 < lambda := zero_lt_one.trans_le hlambda
    have hneg : (-a) ^ 2 - t ^ 2 <= a ^ 2 := by nlinarith
    have hquot : ((-a) ^ 2 - t ^ 2) / lambda <= a ^ 2 / lambda :=
      div_le_div_of_nonneg_right hneg hlambdaPos.le
    have hlinear : lambda * (-a) <= -lambda * Delta := by
      have := mul_le_mul_of_nonneg_left haDelta hlambdaPos.le
      linarith
    linarith
  unfold pintzF
  dsimp only
  rw [norm_mul, norm_div]
  have hquot :
      ‖riemannZeta ((1 - pintzXi Delta eta : ℝ) + I * (gamma + t))‖ /
          ‖s‖ <= Z / Delta := by
    calc
      _ <= Z / ‖s‖ :=
        div_le_div_of_nonneg_right hZeta (norm_nonneg _)
      _ <= Z / Delta :=
        div_le_div_of_nonneg_left hZ hDelta hden
  exact mul_le_mul hquot hgauss (norm_nonneg _)
    (div_nonneg hZ hDelta.le)

/-- Integrated equation-(4.8) estimate on the exact interval
`[-2 lambda, 2 lambda]`. -/
theorem integral_norm_pintzF_le_equation48Majorant
    {Delta eta etaJ gamma lambda Z : ℝ}
    (hDelta : 0 < Delta) (hdeltaJ : 0 <= pintzDeltaJ eta etaJ)
    (hetaJ : 0 <= etaJ) (hxi : pintzXi Delta eta <= 1 / 2)
    (hlambda : 1 <= lambda) (hZ : 0 <= Z)
    (hZeta : ∀ t ∈ Set.Icc (-2 * lambda) (2 * lambda),
      ‖riemannZeta
        ((1 - pintzXi Delta eta : ℝ) + I * (gamma + t))‖ <= Z) :
    ∫ t in (-2 * lambda)..(2 * lambda),
        ‖pintzF Delta eta etaJ gamma lambda t‖ <=
      pintzEquation48Majorant Delta lambda Z := by
  have hlambdaNonneg : 0 <= lambda := zero_le_one.trans hlambda
  let C : ℝ := (Z / Delta) * Real.exp (1 / 4 - lambda * Delta)
  have hCnonneg : 0 <= C := by dsimp [C]; positivity
  have hnormIntegral :
      |∫ t in (-2 * lambda)..(2 * lambda),
          ‖pintzF Delta eta etaJ gamma lambda t‖| <=
        C * |2 * lambda - (-2 * lambda)| := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using
      (intervalIntegral.norm_integral_le_of_norm_le_const
        (f := fun t : ℝ => ‖pintzF Delta eta etaJ gamma lambda t‖)
        (C := C) (fun t ht => by
          have htIcc : t ∈ Set.Icc (-2 * lambda) (2 * lambda) := by
            have ht' := Set.uIoc_subset_uIcc ht
            have hab : -2 * lambda <= 2 * lambda := by linarith
            rw [Set.uIcc_of_le hab] at ht'
            exact ht'
          simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using
            (norm_pintzF_le hDelta hdeltaJ hetaJ hxi hlambda hZ
              (hZeta t htIcc))))
  calc
    ∫ t in (-2 * lambda)..(2 * lambda),
        ‖pintzF Delta eta etaJ gamma lambda t‖ <=
      |∫ t in (-2 * lambda)..(2 * lambda),
        ‖pintzF Delta eta etaJ gamma lambda t‖| := le_abs_self _
    _ <= C * |2 * lambda - (-2 * lambda)| := hnormIntegral
    _ = 4 * lambda *
        ((Z / Delta) * Real.exp (1 / 4 - lambda * Delta)) := by
      rw [abs_of_nonneg (by linarith : 0 <= 2 * lambda - (-2 * lambda))]
      dsimp [C]
      ring
    _ = pintzEquation48Majorant Delta lambda Z := by
      unfold pintzEquation48Majorant
      ring

/-- Equation (4.9): the contour lower bound and the actual `f_j` mass force
a large value of the exact finite Mobius polynomial at a physical ordinate
inside Pintz's window. -/
theorem exists_large_pintzFiniteMobiusPolynomial
    {Delta eta etaJ gamma lambda F : ℝ}
    (hrhoZero : riemannZeta (pintzRho etaJ gamma) = 0)
    (hDelta : 0 < Delta) (hdeltaJ : 0 <= pintzDeltaJ eta etaJ)
    (hlambda : 0 < lambda) (hF : 0 < F)
    (hlower : 1 / 4 <=
      ‖pintzEquation46Integral Delta eta etaJ gamma lambda‖)
    (hFpoint : ∀ t ∈ Set.Icc (-2 * lambda) (2 * lambda),
        ‖pintzF Delta eta etaJ gamma lambda t‖ <= F) :
    ∃ t ∈ Set.Icc (-2 * lambda) (2 * lambda),
      1 / (32 * lambda * F) <=
        ‖pintzFiniteMobiusPolynomial (pintzRho etaJ gamma) lambda
          ((pintzLeftEdge Delta eta etaJ : ℝ) + I * t)‖ := by
  by_contra hnot
  push Not at hnot
  have hsource := pintzEquation46Integral_eq_source
    (lambda := lambda) hrhoZero hDelta hdeltaJ
  have hpiPos : 0 < Real.pi := Real.pi_pos
  let raw : ℂ := ∫ t in (-2 * lambda)..(2 * lambda),
    pintzFiniteMobiusPolynomial (pintzRho etaJ gamma) lambda
        ((pintzLeftEdge Delta eta etaJ : ℝ) + I * t) *
      pintzF Delta eta etaJ gamma lambda t
  have hnormSource :
      ‖pintzEquation46Integral Delta eta etaJ gamma lambda‖ =
        (1 / (2 * Real.pi)) * ‖raw‖ := by
    rw [hsource]
    dsimp [raw]
    simp only [norm_mul, norm_div, norm_one, norm_I,
      norm_real, Real.norm_eq_abs]
    rw [show ‖(2 : ℂ)‖ = 2 by norm_num, abs_of_pos hpiPos]
    ring
  have hrawLower : Real.pi / 2 <=
      ‖∫ t in (-2 * lambda)..(2 * lambda),
        pintzFiniteMobiusPolynomial (pintzRho etaJ gamma) lambda
            ((pintzLeftEdge Delta eta etaJ : ℝ) + I * t) *
          pintzF Delta eta etaJ gamma lambda t‖ := by
    rw [hnormSource] at hlower
    dsimp [raw] at hlower
    have htwoPi : 0 < 2 * Real.pi := by positivity
    have hdiv : 1 / 4 <=
        ‖∫ t in (-2 * lambda)..(2 * lambda),
          pintzFiniteMobiusPolynomial (pintzRho etaJ gamma) lambda
              ((pintzLeftEdge Delta eta etaJ : ℝ) + I * t) *
            pintzF Delta eta etaJ gamma lambda t‖ /
          (2 * Real.pi) := by
      simpa [div_eq_mul_inv, mul_comm] using hlower
    have hmul := (le_div_iff₀ htwoPi).mp hdiv
    convert hmul using 1
    ring
  have hpoint : ∀ t ∈ Set.uIoc (-2 * lambda) (2 * lambda),
      ‖pintzFiniteMobiusPolynomial (pintzRho etaJ gamma) lambda
          ((pintzLeftEdge Delta eta etaJ : ℝ) + I * t) *
        pintzF Delta eta etaJ gamma lambda t‖ <=
      (1 / (32 * lambda * F)) * F := by
    intro t ht
    have htIcc : t ∈ Set.Icc (-2 * lambda) (2 * lambda) := by
      have ht' := Set.uIoc_subset_uIcc ht
      have hab : -2 * lambda <= 2 * lambda := by linarith
      rw [Set.uIcc_of_le hab] at ht'
      exact ht'
    rw [norm_mul]
    exact mul_le_mul (hnot t htIcc).le
      (hFpoint t htIcc) (norm_nonneg _)
      (by positivity)
  have hrawUpper :
      ‖∫ t in (-2 * lambda)..(2 * lambda),
        pintzFiniteMobiusPolynomial (pintzRho etaJ gamma) lambda
            ((pintzLeftEdge Delta eta etaJ : ℝ) + I * t) *
          pintzF Delta eta etaJ gamma lambda t‖ <= 1 / 8 := by
    have hraw := intervalIntegral.norm_integral_le_of_norm_le_const hpoint
    calc
      _ <= (1 / (32 * lambda * F)) * F *
          |2 * lambda - (-2 * lambda)| := hraw
      _ = 1 / 8 := by
        rw [abs_of_nonneg (by linarith :
          0 <= 2 * lambda - (-2 * lambda))]
        field_simp
        ring
  have hpiHalf : 1 / 8 < Real.pi / 2 := by
    nlinarith [Real.pi_gt_three]
  linarith

#print axioms norm_pintzF_le
#print axioms integral_norm_pintzF_le_equation48Majorant
#print axioms exists_large_pintzFiniteMobiusPolynomial

end

end GafniTao
