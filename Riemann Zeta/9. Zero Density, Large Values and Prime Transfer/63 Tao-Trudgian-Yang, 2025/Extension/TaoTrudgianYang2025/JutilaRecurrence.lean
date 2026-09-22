import TaoTrudgianYang2025.JutilaSmoothedPatterns

/-!
# Solving the actual Jutila cardinality recurrence

The physical value threshold absorbs the cardinality-square term.
The remaining mixed term is solved by the square-root inequality.
-/

open Finset RiemannZeta.GuthMaynard

noncomputable section

namespace TaoTrudgianYang2025

/-- For an actual integer cardinality, the stronger five-quarter moment
term is bounded by the classical three-halves term. -/
theorem jutila_card_five_quarters_le (r : ℕ) :
    (r : ℝ)^(5/4 : ℝ) ≤ (r : ℝ)*Real.sqrt (r : ℝ) := by
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst r
    norm_num
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hrp : (0 : ℝ) < r := by exact_mod_cast hr
  calc
    (r : ℝ)^(5/4 : ℝ) ≤ (r : ℝ)^(3/2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hr1 (by norm_num)
    _ = (r : ℝ)*Real.sqrt (r : ℝ) := by
      rw [Real.sqrt_eq_rpow, show (3/2 : ℝ) = 1+1/2 by norm_num,
        Real.rpow_add hrp, Real.rpow_one]

/-- The elementary square-root inequality used after absorption. -/
theorem jutila_sqrt_recurrence {R b c : ℝ} (hR : 0 ≤ R)
    (h : R ≤ b+c*Real.sqrt R) : R ≤ 2*b+c^2 := by
  have hs := Real.sq_sqrt hR
  nlinarith [sq_nonneg (Real.sqrt R-c)]

/-- The powered Gram recurrence gives the two off-diagonal cardinality
terms once its explicit source-scale value threshold holds. -/
theorem jutila_powered_recurrence_card_le (k Q : ℕ) (T D V : ℝ) (W : Finset ℝ)
    (hT : 0 ≤ T) (hD : 0 ≤ D) (hV : 0 < V)
    (habs : 2*D*(Q : ℝ)^k ≤ V^(4*k))
    (hrec : (W.card : ℝ)^2*V^(4*k) ≤ D*jutilaMomentCore k Q T W) :
    (W.card : ℝ) ≤ 4*D*T^k/V^(4*k) +
      4*D^2*T*(Q : ℝ)^(2*k)/V^(8*k) := by
  let R : ℝ := W.card
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hden : 0 < V^(4*k) := pow_pos hV _
  by_cases hzero : R = 0
  · rw [show (W.card : ℝ) = 0 from hzero]
    positivity
  have hRp : 0 < R := lt_of_le_of_ne hR (Ne.symm hzero)
  have hmixed := jutila_card_five_quarters_le W.card
  have hrootT : T^(1/2 : ℝ) = Real.sqrt T := (Real.sqrt_eq_rpow T).symm
  have hcore : jutilaMomentCore k Q T W ≤
      R^2*(Q : ℝ)^k+R*T^k+R*Real.sqrt R*Real.sqrt T*(Q : ℝ)^k := by
    unfold jutilaMomentCore
    rw [hrootT]
    gcongr
  have hb : R^2*V^(4*k) ≤
      D*(R^2*(Q : ℝ)^k+R*T^k+R*Real.sqrt R*Real.sqrt T*(Q : ℝ)^k) :=
    hrec.trans (mul_le_mul_of_nonneg_left hcore hD)
  have habsR := mul_le_mul_of_nonneg_left habs (sq_nonneg R)
  have hlinear : R*V^(4*k) ≤
      2*D*T^k+2*D*Real.sqrt R*Real.sqrt T*(Q : ℝ)^k := by
    have hprod : R*(R*V^(4*k)) ≤
        R*(2*D*T^k+2*D*Real.sqrt R*Real.sqrt T*(Q : ℝ)^k) := by nlinarith
    exact le_of_mul_le_mul_left hprod hRp
  have hsqrt : R ≤ 2*D*T^k/V^(4*k)+
      (2*D*Real.sqrt T*(Q : ℝ)^k/V^(4*k))*Real.sqrt R := by
    apply (le_div_iff₀ hden).mpr at hlinear
    convert hlinear using 1
    ring
  have hsol := jutila_sqrt_recurrence hR hsqrt
  change R ≤ _
  convert hsol using 1
  rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt hT, ← pow_mul, ← pow_mul]
  ring

end TaoTrudgianYang2025
