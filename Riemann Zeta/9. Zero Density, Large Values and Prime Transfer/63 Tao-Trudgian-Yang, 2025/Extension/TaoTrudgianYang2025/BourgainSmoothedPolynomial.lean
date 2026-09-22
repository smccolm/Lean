import TaoTrudgianYang2025.BourgainMellinLocalization
import TaoTrudgianYang2025.JutilaReflectionIntegrals
import TaoTrudgianYang2025.BourgainZetaDifferenceMoments

/-!
# An actual smoothed critical polynomial and its retained zeta-square bound

The fixed profile is one on [1,2] and zero outside [1/2,5/2].
This is a genuine coefficient majorant, with finite support after dilation.
The pole, window-length loss, and tail remain explicit in the square bound.
-/

open Complex Filter MeasureTheory Set
open RiemannZeta.GuthMaynard
open scoped Interval

noncomputable section

namespace TaoTrudgianYang2025

/-- Fixed, scale-independent profile for a dyadic critical block. -/
def bourgainDyadicProfile (x : ℝ) : ℂ := zetaIntervalCutoff 1 2 x

def bourgainDyadicProfileTest : DFIVoronoiTestFunction bourgainDyadicProfile :=
  zetaIntervalCutoffTest 1 2 (by norm_num)

/-- The actual finite-support critical-line Dirichlet polynomial. -/
def bourgainSmoothedCriticalPolynomial (L t : ℝ) : ℂ :=
  ∑' n : ℕ, bourgainCriticalWeight bourgainDyadicProfile L n * dirichletPhase n t

/-- Exact coefficient on the complete closed dyadic block. -/
theorem bourgainDyadicProfile_weight_eq {L x : ℝ}
    (hL : 0 < L) (hl : L ≤ x) (hu : x ≤ 2*L) :
    bourgainCriticalWeight bourgainDyadicProfile L x = ((x^(-1/2 : ℝ) : ℝ) : ℂ) := by
  have h := zetaIntervalCutoff_eq_one (a := 1) (b := 2)
    ((le_div_iff₀ hL).2 (by simpa using hl)) ((div_le_iff₀ hL).2 hu)
  simp only [bourgainCriticalWeight, bourgainRealPowerWeight, bourgainDyadicProfile,
    h, ofReal_one, mul_one]

/-- Literal support bound, including vanishing at both outer endpoints. -/
theorem bourgainDyadicProfile_weight_eq_zero {L x : ℝ}
    (hL : 0 < L) (hx : x ≤ L/2 ∨ 5*L/2 ≤ x) :
    bourgainCriticalWeight bourgainDyadicProfile L x = 0 := by
  have hz : zetaIntervalCutoff 1 2 (x/L) = 0 := by
    rcases hx with hl | hu
    · apply zetaIntervalCutoff_eq_zero_left
      apply (div_le_iff₀ hL).2
      norm_num
      linarith
    · apply zetaIntervalCutoff_eq_zero_right
      apply (le_div_iff₀ hL).2
      norm_num
      linarith
  simp only [bourgainCriticalWeight, bourgainRealPowerWeight, bourgainDyadicProfile,
    hz, ofReal_zero, mul_zero]

/-- The infinite-sum notation is exactly a finite sum with a proved,
physical-scale cutoff. -/
theorem bourgainSmoothedCriticalPolynomial_eq_sum {L : ℝ}
    (hL : 0 < L) (t : ℝ) :
    bourgainSmoothedCriticalPolynomial L t =
      ∑ n ∈ Finset.range (Nat.ceil (5*L/2)+1),
        bourgainCriticalWeight bourgainDyadicProfile L n * dirichletPhase n t := by
  apply tsum_eq_sum
  intro n hn
  have hn' : Nat.ceil (5*L/2)+1 ≤ n := Nat.le_of_not_gt (fun hh => hn (Finset.mem_range.mpr hh))
  have hn'' : (Nat.ceil (5*L/2) : ℝ) < n := by exact_mod_cast hn'
  have hcut : 5*L/2 ≤ (n : ℝ) := (Nat.le_ceil (5*L/2)).trans hn''.le
  rw [bourgainDyadicProfile_weight_eq_zero hL (Or.inr hcut), zero_mul]

/-- Squaring the actual localized Mellin estimate retains the local
zeta-square integral, rather than replacing it by a global moment. -/
theorem bourgainCriticalWeight_localized_sq {g : ℝ → ℂ}
    (hg : DFIVoronoiTestFunction g) (q : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ L : ℝ, 0 < L → ∀ t H : ℝ, 0 ≤ H →
      ‖∑' n : ℕ, bourgainCriticalWeight g L n * dirichletPhase n t‖^2 ≤
        C * (L/(1+|t|)^(2*q) +
          2*H*(∫ u in -H..H, zetaMomentCriticalNorm (u+t)^2) +
          (1+|t|)^2/(1+H)^(2*q)) := by
  obtain ⟨A,hA,hbound⟩ := bourgainCriticalWeight_localized hg q
  refine ⟨3*A^2, by positivity, ?_⟩
  intro L hL t H hH
  let a : ℝ := Real.sqrt L/(1+|t|)^q
  let b : ℝ := ∫ u in -H..H, zetaMomentCriticalNorm (u+t)
  let c : ℝ := (1+|t|)/(1+H)^q
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := intervalIntegral.integral_nonneg (by linarith)
    (fun _ _ => norm_nonneg _)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hp := pow_le_pow_left₀ (norm_nonneg _) (hbound L hL t H hH) 2
  have hj : b^2 ≤ 2*H*∫ u in -H..H, zetaMomentCriticalNorm (u+t)^2 := by
    simpa only [Nat.reduceSub, pow_one] using
      jutila_intervalIntegral_pow_le (fun u => zetaMomentCriticalNorm (u+t))
        H hH (by norm_num : 0 < (2 : ℕ))
        (continuous_zetaMomentCriticalNorm.comp (continuous_id.add continuous_const))
        (fun _ => norm_nonneg _)
  have hasq : a^2 = L/(1+|t|)^(2*q) := by
    dsimp [a]
    rw [div_pow, Real.sq_sqrt hL.le, ← pow_mul, Nat.mul_comm q 2]
  have hcsq : c^2 = (1+|t|)^2/(1+H)^(2*q) := by
    dsimp [c]
    rw [div_pow, ← pow_mul, Nat.mul_comm q 2]
  have hsum : (a+b+c)^2 ≤ 3*(a^2+b^2+c^2) := by
    nlinarith [sq_nonneg (a-b), sq_nonneg (a-c), sq_nonneg (b-c)]
  calc
    _ ≤ (A*(a+b+c))^2 := hp
    _ = A^2*(a+b+c)^2 := mul_pow _ _ _
    _ ≤ A^2*(3*(a^2+b^2+c^2)) :=
      mul_le_mul_of_nonneg_left hsum (sq_nonneg A)
    _ ≤ A^2*(3*(a^2+(2*H*∫ u in -H..H, zetaMomentCriticalNorm (u+t)^2)+c^2)) := by
      gcongr
    _ = _ := by rw [hasq,hcsq]; ring

/-- The smooth test is constructed from the fixed profile, not supplied
as an analytic hypothesis. -/
theorem bourgainSmoothedCriticalPolynomial_localized_sq (q : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ L : ℝ, 0 < L → ∀ t H : ℝ, 0 ≤ H →
      ‖bourgainSmoothedCriticalPolynomial L t‖^2 ≤
        C * (L/(1+|t|)^(2*q) +
          2*H*(∫ u in -H..H, zetaMomentCriticalNorm (u+t)^2) +
          (1+|t|)^2/(1+H)^(2*q)) :=
  bourgainCriticalWeight_localized_sq bourgainDyadicProfileTest q

/-- Actual pair differences enter the proved integer difference moment.
The diagonal/pole term is retained as its own finite sum. -/
theorem bourgainSmoothedCriticalPolynomial_pair_moment (q : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ L : ℝ, 0 < L →
      ∀ (W : Finset ℝ) (T H : ℝ), 0 ≤ T → 0 ≤ H → InBaseInterval T W →
      (∑ t ∈ W, ∑ v ∈ W, ‖bourgainSmoothedCriticalPolynomial L (t-v)‖^2) ≤
        C * (L*(∑ t ∈ W, ∑ v ∈ W, 1/(1+|t-v|)^(2*q)) +
          2*H*bourgainZetaDifferenceMoment W (H+1) +
          (W.card : ℝ)^2*(1+T)^2/(1+H)^(2*q)) := by
  obtain ⟨C,hC,hbound⟩ := bourgainSmoothedCriticalPolynomial_localized_sq q
  refine ⟨C,hC,?_⟩
  intro L hL W T H hT hH hbase
  have hpoint (t : ℝ) (ht : t ∈ W) (v : ℝ) (hv : v ∈ W) :
      ‖bourgainSmoothedCriticalPolynomial L (t-v)‖^2 ≤
        C*(L/(1+|t-v|)^(2*q) +
          2*H*(∫ u in -H..H, zetaMomentCriticalNorm (t-v+u)^2) +
          (1+T)^2/(1+H)^(2*q)) := by
    apply (hbound L hL (t-v) H hH).trans
    have htb := hbase t ht
    have hvb := hbase v hv
    have habs : |t-v| ≤ T := abs_le.mpr
      ⟨by linarith [htb.1, hvb.2], by linarith [hvb.1, htb.2]⟩
    have ht0 : 0 ≤ 1+|t-v| := by positivity
    have hpow : (1+|t-v|)^2 ≤ (1+T)^2 :=
      pow_le_pow_left₀ ht0 (by linarith) 2
    apply mul_le_mul_of_nonneg_left _ hC.le
    apply add_le_add
    · simp only [add_comm, le_refl]
    · exact div_le_div_of_nonneg_right hpow (by positivity)
  have hsum := Finset.sum_le_sum (s := W) (fun t ht =>
    Finset.sum_le_sum (s := W) (fun v hv => hpoint t ht v hv))
  have hz := bourgain_pair_zeta_square_integral_le W hH
  calc
    _ ≤ _ := hsum
    _ = C*(L*(∑ t ∈ W, ∑ v ∈ W, 1/(1+|t-v|)^(2*q)) +
        2*H*(∑ t ∈ W, ∑ v ∈ W,
          ∫ u in -H..H, zetaMomentCriticalNorm (t-v+u)^2) +
        (W.card : ℝ)^2*(1+T)^2/(1+H)^(2*q)) := by
      simp only [div_eq_mul_inv, one_mul, Finset.sum_add_distrib,
        ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≤ _ := by gcongr

end TaoTrudgianYang2025
