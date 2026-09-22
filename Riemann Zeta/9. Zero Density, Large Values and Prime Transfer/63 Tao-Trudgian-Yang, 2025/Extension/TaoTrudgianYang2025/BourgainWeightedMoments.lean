import TaoTrudgianYang2025.BourgainCriticalMajorant
import TaoTrudgianYang2025.JutilaPolynomialMoments

/-!
# Retained zeta moments in the native weighted-moment convention

The source uses positive phases and 1/sqrt(n); the Mellin consumer uses
negative phases and n^(-1/2). Both bridges are proved before composition.
The literal n=1 term is also treated by the actual Mellin majorant.
-/

open Complex Finset MeasureTheory Set
open RiemannZeta.GuthMaynard

noncomputable section

namespace TaoTrudgianYang2025

/-- Complete physical budget, with zeta differences and the explicit tail. -/
def bourgainMomentBudget (q : ℕ) (U T H : ℝ) (W : Finset ℝ) : ℝ :=
  U*(W.card : ℝ) + H*bourgainZetaDifferenceMoment W (H+1) +
    (W.card : ℝ)^2*(1+T)^2/(1+H)^(2*q)

theorem bourgainMomentBudget_nonneg (q : ℕ) {U T H : ℝ} (W : Finset ℝ)
    (hU : 0 ≤ U) (hH : 0 ≤ H) : 0 ≤ bourgainMomentBudget q U T H W := by
  have hm : 0 ≤ bourgainZetaDifferenceMoment W (H+1) := by
    unfold bourgainZetaDifferenceMoment
    exact Finset.sum_nonneg (fun ℓ _ =>
      mul_nonneg (Nat.cast_nonneg _) (bourgainLocalZetaSquare_nonneg (by linarith) ℓ))
  unfold bourgainMomentBudget
  positivity

theorem bourgainMomentBudget_mono_scale (q : ℕ) {U V : ℝ}
    (hUV : U ≤ V) (T H : ℝ) (W : Finset ℝ) :
    bourgainMomentBudget q U T H W ≤ bourgainMomentBudget q V T H W := by
  unfold bourgainMomentBudget
  gcongr

/-- The native half weight agrees exactly with the Mellin normalization. -/
theorem bourgain_heathBrownHalfWeight_eq_rpow (n : ℕ) :
    heathBrownHalfWeight n = (n : ℝ)^(-1/2 : ℝ) := by
  unfold heathBrownHalfWeight
  rw [Real.sqrt_eq_rpow, show (-1/2 : ℝ) = -(1/2) by ring,
    Real.rpow_neg (Nat.cast_nonneg n), one_div]

/-- Reverse the ordered pair to match the negative-phase Mellin entry. -/
theorem bourgain_sourceDirichletPoly_eq_negative_sum (N : ℕ)
    (a : ℕ → ℂ) (t v : ℝ) :
    sourceDirichletPoly N a (t-v) =
      ∑ n ∈ dyadicInterval N, a n * dirichletPhase n (v-t) := by
  rw [← dirichletPoly_neg_eq_sourceDirichletPoly, neg_sub,
    ← heathBrownDifferencePolynomial_dyadic_eq_dirichletPoly,
    heathBrownDifferencePolynomial_eq_dirichletPhase]
  intro n hn
  exact lt_of_le_of_lt (Nat.zero_le N) (Finset.mem_Ioc.mp hn).1

/-- Actual native weighted moment with its zeta moment still retained. -/
theorem bourgain_heathBrownWeightedMoment_retained {q : ℕ} (hq : 0 < q) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (T H : ℝ) (W : Finset ℝ),
      0 < N → 0 ≤ T → 0 ≤ H → IsSeparated 1 W → InBaseInterval T W →
      heathBrownWeightedMoment N W ≤ C*bourgainMomentBudget q N T H W := by
  obtain ⟨C,hC,hbound⟩ := bourgain_critical_block_retained_zeta_moment hq
  refine ⟨C,hC,?_⟩
  intro N T H W hN hT hH hsep hbase
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hI : ∀ n ∈ dyadicInterval N, (N : ℝ) ≤ n ∧ (n : ℝ) ≤ 2*N := by
    intro n hn
    have h := Finset.mem_Ioc.mp hn
    exact ⟨by exact_mod_cast h.1.le, by exact_mod_cast h.2⟩
  have ha : ∀ n ∈ dyadicInterval N,
      ‖(heathBrownHalfWeight n : ℂ)‖ ≤ 1*(n : ℝ)^(-1/2 : ℝ) := by
    intro n hn
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (heathBrownHalfWeight_nonneg n),
      bourgain_heathBrownHalfWeight_eq_rpow, one_mul]
  have h := hbound N hNr (dyadicInterval N) W (fun n => (heathBrownHalfWeight n : ℂ))
    1 T H (by norm_num) hT hH hsep hbase hI ha
  unfold heathBrownWeightedMoment
  simp_rw [bourgain_sourceDirichletPoly_eq_negative_sum]
  rw [Finset.sum_comm]
  simpa only [one_pow,mul_one,bourgainMomentBudget] using h

/-- The n=1 term is not replaced by an uncontrolled R-squared error.
It too is an actual finite critical block consumed by the Mellin bound. -/
theorem bourgain_literal_one_moment_retained {q : ℕ} (hq : 0 < q) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T H : ℝ) (W : Finset ℝ),
      0 ≤ T → 0 ≤ H → IsSeparated 1 W → InBaseInterval T W →
      (W.card : ℝ)^2 ≤ C*bourgainMomentBudget q 1 T H W := by
  obtain ⟨C,hC,hbound⟩ := bourgain_critical_block_retained_zeta_moment hq
  refine ⟨C,hC,?_⟩
  intro T H W hT hH hsep hbase
  have hI : ∀ n ∈ ({1} : Finset ℕ), (1 : ℝ) ≤ n ∧ (n : ℝ) ≤ 2*1 := by
    intro n hn
    have := Finset.mem_singleton.mp hn
    subst n
    norm_num
  have ha : ∀ n ∈ ({1} : Finset ℕ), ‖(1 : ℂ)‖ ≤ 1*(n : ℝ)^(-1/2 : ℝ) := by
    intro n hn
    have := Finset.mem_singleton.mp hn
    subst n
    norm_num
  have h := hbound 1 (by norm_num) {1} W (fun _ => (1 : ℂ))
    1 T H (by norm_num) hT hH hsep hbase hI ha
  simpa [dirichletPhase,bourgainMomentBudget,pow_two] using h

end TaoTrudgianYang2025
