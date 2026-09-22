import TaoTrudgianYang2025.BourgainPolynomialMoments
import TaoTrudgianYang2025.JutilaPrefixMoments

/-!
# Retained zeta moments of the actual reflected prefix

The prefix is the native unweighted polynomial, including n=1. Its
translation parameter remains in unit-bounded coefficients, so the
bound is uniform in the translation. The conversion factor U
is retained for the subsequent physical reflection normalization.
-/

open Complex Finset
open RiemannZeta.GuthMaynard

noncomputable section

namespace TaoTrudgianYang2025

/-- Actual native reflected-prefix moments, with every dyadic piece,
the literal first term, and the retained zeta-square budget consumed. -/
theorem bourgain_reflected_prefix_moment_retained (k : ℕ) (hk : 0 < k)
    {q : ℕ} (hq : 0 < q) {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : ℕ) (T H : ℝ) (W : Finset ℝ) (u : ℝ),
        0 < M → 0 ≤ T → 0 ≤ H → IsSeparated 1 W → InBaseInterval T W →
        (∑ t ∈ W, ∑ v ∈ W, ‖gmReflectionDirichletPoly (t-v) M u‖^(2*k)) ≤
          C*((Nat.clog 2 M : ℝ)+1)^(2*k)*(2^k*M^k : ℕ)*
            (((2^k*M^k : ℕ) : ℝ)^η)^2 *
              bourgainMomentBudget q (2^k*M^k : ℕ) T H W := by
  obtain ⟨A,hA,hmoment⟩ := bourgain_source_power_moment_retained k hk hq hη
  obtain ⟨D,hD,hone⟩ := bourgain_literal_one_moment_retained hq
  refine ⟨A+D, by positivity, ?_⟩
  intro M T H W u hM hT hH hsep hbase
  let U : ℕ := 2^k*M^k
  let B : ℝ := bourgainMomentBudget q U T H W
  let F : ℝ := (U : ℝ)*((U : ℝ)^η)^2*B
  let L : ℝ := Nat.clog 2 M
  have hUpos : 0 < U := by dsimp [U]; positivity
  have hU1 : (1 : ℝ) ≤ U := by exact_mod_cast hUpos
  have hB : 0 ≤ B := bourgainMomentBudget_nonneg q W (Nat.cast_nonneg U) hH
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hBF : B ≤ F := by
    have hη1 : 1 ≤ (U : ℝ)^η := Real.one_le_rpow hU1 hη.le
    dsimp [F]
    calc
      B = 1*1^2*B := by ring
      _ ≤ _ := by gcongr
  have hRF : (W.card : ℝ)^2 ≤ D*F :=
    (hone T H W hT hH hsep hbase).trans (mul_le_mul_of_nonneg_left
      ((bourgainMomentBudget_mono_scale q hU1 T H W).trans hBF) hD.le)
  have hblock (r : ℕ) (hr : r ∈ Finset.range (Nat.clog 2 M)) :
      (∑ t ∈ W, ∑ v ∈ W,
        ‖dirichletPoly (2^r) (heathBrownReflectedPrefixCoeff M u) (t-v)‖^(2*k)) ≤
        A*F := by
    have hNM : 2^r ≤ M := (Nat.pow_lt_of_lt_clog (Finset.mem_range.mp hr)).le
    have hQU : 2^k*(2^r)^k ≤ U := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hNM k)
    have hQUr : ((2^k*(2^r)^k : ℕ) : ℝ) ≤ U := by exact_mod_cast hQU
    have hm := hmoment (2^r) T H W (heathBrownReflectedPrefixCoeff M u)
      (by positivity) hT hH hsep hbase
      (fun n _ => norm_heathBrownReflectedPrefixCoeff_le_one M u n)
    have heq :
        (∑ t ∈ W, ∑ v ∈ W,
          ‖dirichletPoly (2^r) (heathBrownReflectedPrefixCoeff M u) (t-v)‖^(2*k)) =
        ∑ t ∈ W, ∑ v ∈ W,
          ‖sourceDirichletPoly (2^r) (heathBrownReflectedPrefixCoeff M u) (t-v)‖^(2*k) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro t ht
      apply Finset.sum_congr rfl
      intro v hv
      rw [← dirichletPoly_neg_eq_sourceDirichletPoly,neg_sub]
    rw [heq]
    apply hm.trans
    have hbudget := bourgainMomentBudget_mono_scale q hQUr T H W
    have hbudget0 := bourgainMomentBudget_nonneg q
      (T := T) W (Nat.cast_nonneg (2^k*(2^r)^k)) hH
    calc
      _ ≤ A*(U : ℝ)*((U : ℝ)^η)^2*B := by
        dsimp [B]
        gcongr
      _ = _ := by dsimp [F]; ring
  have hsum := Finset.sum_le_sum hblock
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul] at hsum
  have hbound := jutila_reflected_prefix_moment_le_blocks W u hM hk
  have hcore : (W.card : ℝ)^2 +
      (∑ r ∈ Finset.range (Nat.clog 2 M), ∑ t ∈ W, ∑ v ∈ W,
        ‖dirichletPoly (2^r) (heathBrownReflectedPrefixCoeff M u) (t-v)‖^(2*k)) ≤
        (A+D)*(L+1)*F := by
    calc
      _ ≤ D*F + L*(A*F) := add_le_add hRF hsum
      _ ≤ _ := by nlinarith [mul_nonneg hA.le hF, mul_nonneg hL hF]
  have hfinal := hbound.trans (mul_le_mul_of_nonneg_left hcore (by positivity))
  have hp : 2*k-1+1 = 2*k := by omega
  have hid : (L+1)^(2*k-1)*((A+D)*(L+1)*F) = (A+D)*(L+1)^(2*k)*F := by
    calc
      _ = (A+D)*((L+1)^(2*k-1)*(L+1))*F := by ring
      _ = _ := by rw [← pow_succ,hp]
  change _ ≤ (L+1)^(2*k-1)*((A+D)*(L+1)*F) at hfinal
  rw [hid] at hfinal
  convert hfinal using 1
  dsimp [L,F,B,U]
  ring

end TaoTrudgianYang2025
