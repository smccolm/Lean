import TaoTrudgianYang2025.RobertSargosZeroQLeading
import TaoTrudgianYang2025.ContinuousPhaseAbel

/-! Abel summation consumes the actual differentiated zero-q remainder. -/

noncomputable section
open Set GafniTao
open scoped ContDiff
namespace TaoTrudgianYang2025

theorem robertSargos_zero_q_perturbed_prefix
    (f : ℝ → ℝ) (A : ℝ) (N : ℕ) {a b h r C lam : ℝ}
    (hh : 0 ≤ h) (hhr : 0 ≤ h+r) (hr : r ≠ 0)
    (hC : 1 ≤ C) (hlam : 0 < lam) (hscale : 2*|r| *lam ≤ 1)
    (ha : a ≤ A-h) (hb : A+N+h ≤ b)
    (har : a ≤ A-(h+r)) (hbr : A+N+(h+r) ≤ b)
    (hf : ∀ x ∈ Icc a b, ContDiffAt ℝ 4 f x)
    (hlo : ∀ x ∈ Icc a b, lam ≤ iteratedDeriv 4 f x)
    (hhi : ∀ x ∈ Icc a b, iteratedDeriv 4 f x ≤ C*lam) :
    ‖∑ n ∈ Finset.range N, fordAdditiveCharacter
      (robertSargosSymmetricDifference f (A+n) h -
        robertSargosSymmetricDifference f (A+n) (h+r))‖ ≤
      (1+2*Real.pi*(C*lam*(h^3+(h+r)^3)/3)*N)*
        (20*C*((N:ℝ)*(2*|r| *lam)^((1:ℝ)/6)+
          Real.sqrt N*(2*|r| *lam)^(-(1:ℝ)/6))) := by
  let μ := 2*|r| *lam
  let B := 20*C*((N:ℝ)*μ^((1:ℝ)/6)+Real.sqrt N*μ^(-(1:ℝ)/6))
  let K := C*lam*(h^3+(h+r)^3)/3
  have hCp : 0 ≤ C := zero_le_one.trans hC
  have hin (x : ℝ) (hx : x ∈ Icc A (A+N)) :
      x ∈ Icc a b ∧ x+h ∈ Icc a b ∧ x-h ∈ Icc a b ∧
        x+(h+r) ∈ Icc a b ∧ x-(h+r) ∈ Icc a b := by
    constructor
    · constructor <;> linarith [hx.1,hx.2]
    constructor
    · constructor <;> linarith [hx.1,hx.2]
    constructor
    · constructor <;> linarith [hx.1,hx.2]
    constructor <;> constructor <;> linarith [hx.1,hx.2]
  have hp (n : ℕ) (hn : n ≤ N) :
      ‖∑ j ∈ Finset.range n, fordAdditiveCharacter (robertSargosZeroQLeading f r (A+j))‖ ≤ B := by
    have hnc : (n:ℝ) ≤ N := by exact_mod_cast hn
    have hsub : Icc A (A+n) ⊆ Icc A (A+N) := fun x hx => ⟨hx.1,by linarith [hx.2]⟩
    have he := robertSargos_zero_q_leading_prefix f A n hr hC hlam hscale
      (fun x hx => hf x (hin x (hsub hx)).1)
      (fun x hx => hlo x (hin x (hsub hx)).1)
      (fun x hx => hhi x (hin x (hsub hx)).1)
    apply he.trans
    exact mul_le_mul_of_nonneg_left
      (add_le_add
        (mul_le_mul_of_nonneg_right hnc (Real.rpow_nonneg (by positivity) _))
        (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hnc)
          (Real.rpow_nonneg (by positivity) _))) (by positivity)
  have hu (x : ℝ) (hx : x ∈ Icc A (A+N)) :
      HasDerivAt (robertSargosZeroQRemainder f h r)
        (deriv (robertSargosZeroQRemainder f h r) x) x := by
    obtain ⟨hx0,hxp,hxm,hxrp,hxrm⟩ := hin x hx
    exact (hasDerivAt_robertSargos_zero_q_remainder
      (hf x hx0) (hf _ hxp) (hf _ hxm) (hf _ hxrp) (hf _ hxrm)).differentiableAt.hasDerivAt
  have hd (x : ℝ) (hx : x ∈ Icc A (A+N)) :
      |deriv (robertSargosZeroQRemainder f h r) x| ≤ K := by
    obtain ⟨_,hxp,hxm,hxrp,hxrm⟩ := hin x hx
    exact abs_robertSargos_zero_q_remainder_derivative_le hh hhr
      hxm.1 hxp.2 hxrm.1 hxrp.2 hf
      (fun y hy => by rw [abs_of_nonneg (hlam.le.trans (hlo y hy))]; exact hhi y hy)
  have ht := norm_continuous_perturbed_phase_prefix
    (robertSargosZeroQLeading f r) (robertSargosZeroQRemainder f h r)
    (deriv (robertSargosZeroQRemainder f h r)) A N
    (show 0 ≤ B by dsimp [B,μ]; positivity)
    (show 0 ≤ K by dsimp [K]; positivity) hp hu hd
  simpa only [← robertSargos_zero_q_phase_identity] using ht

end TaoTrudgianYang2025
