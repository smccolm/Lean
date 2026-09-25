import TaoTrudgianYang2025.RobertSargosSymmetricQuadratic
import TaoTrudgianYang2025.RobertSargosSymmetricThirdDerivative

/-! The zero-q column: genuine leading phase and differentiated remainder. -/

noncomputable section
open Set GafniTao
open scoped ContDiff
namespace TaoTrudgianYang2025

def robertSargosZeroQLeading (f : ℝ → ℝ) (r x : ℝ) : ℝ :=
  -2*r*iteratedDeriv 1 f x

def robertSargosZeroQRemainder (f : ℝ → ℝ) (h r x : ℝ) : ℝ :=
  robertSargosSymmetricDifference f x h -
    robertSargosSymmetricDifference f x (h+r) + 2*r*iteratedDeriv 1 f x

theorem robertSargos_zero_q_phase_identity (f : ℝ → ℝ) (h r x : ℝ) :
    robertSargosSymmetricDifference f x h -
      robertSargosSymmetricDifference f x (h+r) =
        robertSargosZeroQLeading f r x+robertSargosZeroQRemainder f h r x := by
  unfold robertSargosZeroQLeading robertSargosZeroQRemainder
  ring

theorem hasDerivAt_robertSargos_zero_q_remainder
    {f : ℝ → ℝ} {h r x : ℝ}
    (hx : ContDiffAt ℝ 4 f x)
    (hp : ContDiffAt ℝ 4 f (x+h)) (hm : ContDiffAt ℝ 4 f (x-h))
    (hrp : ContDiffAt ℝ 4 f (x+(h+r))) (hrm : ContDiffAt ℝ 4 f (x-(h+r))) :
    HasDerivAt (robertSargosZeroQRemainder f h r)
      (robertSargosSymmetricDifference (iteratedDeriv 1 f) x h -
        robertSargosSymmetricDifference (iteratedDeriv 1 f) x (h+r) +
          2*r*iteratedDeriv 2 f x) x := by
  have hdp := hasDerivAt_robertSargos_symmetric_jet (by norm_num : 0 < 4) hp hm
  have hdr := hasDerivAt_robertSargos_symmetric_jet (by norm_num : 0 < 4) hrp hrm
  have hd1 := (hasDerivAt_iteratedDeriv_finite (by norm_num : 1 < 4) hx).const_mul (2*r)
  simpa only [robertSargosZeroQRemainder,iteratedDeriv_zero] using (hdp.sub hdr).add hd1

theorem abs_robertSargos_zero_q_remainder_derivative_le
    {f : ℝ → ℝ} {a b x h r B : ℝ} (hh : 0 ≤ h) (hhr : 0 ≤ h+r)
    (ha : a ≤ x-h) (hb : x+h ≤ b)
    (har : a ≤ x-(h+r)) (hbr : x+(h+r) ≤ b)
    (hf : ∀ y ∈ Icc a b, ContDiffAt ℝ 4 f y)
    (hd : ∀ y ∈ Icc a b, |iteratedDeriv 4 f y| ≤ B) :
    |deriv (robertSargosZeroQRemainder f h r) x| ≤ B*(h^3+(h+r)^3)/3 := by
  have hx : x ∈ Icc a b := ⟨by linarith,by linarith⟩
  have hp : x+h ∈ Icc a b := ⟨by linarith,hb⟩
  have hm : x-h ∈ Icc a b := ⟨ha,by linarith⟩
  have hrp : x+(h+r) ∈ Icc a b := ⟨by linarith,hbr⟩
  have hrm : x-(h+r) ∈ Icc a b := ⟨har,by linarith⟩
  rw [(hasDerivAt_robertSargos_zero_q_remainder
    (hf x hx) (hf _ hp) (hf _ hm) (hf _ hrp) (hf _ hrm)).deriv]
  have h₁ := abs_symmetric_first_jet_remainder_le hh ha hb hf hd
  have h₂ := abs_symmetric_first_jet_remainder_le hhr har hbr hf hd
  have he :
      robertSargosSymmetricDifference (iteratedDeriv 1 f) x h -
        robertSargosSymmetricDifference (iteratedDeriv 1 f) x (h+r) +
          2*r*iteratedDeriv 2 f x =
      (robertSargosSymmetricDifference (iteratedDeriv 1 f) x h-2*h*iteratedDeriv 2 f x) -
        (robertSargosSymmetricDifference (iteratedDeriv 1 f) x (h+r)-
          2*(h+r)*iteratedDeriv 2 f x) := by ring
  rw [he]
  have ht := abs_sub_le
    (robertSargosSymmetricDifference (iteratedDeriv 1 f) x h-2*h*iteratedDeriv 2 f x) 0
    (robertSargosSymmetricDifference (iteratedDeriv 1 f) x (h+r)-
      2*(h+r)*iteratedDeriv 2 f x)
  simp only [sub_zero,zero_sub,abs_neg] at ht
  nlinarith

theorem hasDerivAt_robertSargos_zero_q_leading_jet
    {f : ℝ → ℝ} {x r : ℝ} {j : ℕ} (hj : j < 3) (hf : ContDiffAt ℝ 4 f x) :
    HasDerivAt (fun y => -2*r*iteratedDeriv (j+1) f y)
      (-2*r*iteratedDeriv (j+2) f x) x := by
  exact (hasDerivAt_iteratedDeriv_finite (show j+1 < 4 by omega) hf).const_mul (-2*r)

end TaoTrudgianYang2025
