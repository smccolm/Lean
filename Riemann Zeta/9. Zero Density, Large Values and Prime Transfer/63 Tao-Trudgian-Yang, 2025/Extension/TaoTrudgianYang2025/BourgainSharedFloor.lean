import TaoTrudgianYang2025.BourgainMassDichotomy
import TaoTrudgianYang2025.BourgainBandSelection

/-!
# A shared physical amplitude floor

The floor depends on N, alpha, tau and epsilon, not on the local mass,
the difference-level index, or its cardinality. The actual heavy-level
bounds make the discarded low-amplitude contribution absorbable.
-/

open RiemannZeta.GuthMaynard

noncomputable section

namespace TaoTrudgianYang2025

/-- A common exponent for the amplitude floor, independent of local sets. -/
def bourgainSharedFloorExponent (α τ ε : ℝ) : ℝ :=
  |α|+4*|τ|+ε+20

theorem bourgainSharedFloorExponent_pos (α τ : ℝ) {ε : ℝ} (hε : 0 ≤ ε) :
    0 < bourgainSharedFloorExponent α τ ε := by
  dsimp only [bourgainSharedFloorExponent]
  positivity

/-- The fixed numerical margin absorbs the crude finite cardinality and
difference-level costs, without making the threshold depend on alpha. -/
theorem bourgain_shared_floor_exponent {α τ ε : ℝ} (hε : 0 ≤ ε) :
    ε/8-2*bourgainSharedFloorExponent α τ ε+3*(|τ|+1)+7 ≤ -α+τ/2 := by
  dsimp only [bourgainSharedFloorExponent]
  nlinarith [le_abs_self α, abs_nonneg α, neg_le_abs τ, abs_nonneg τ]

theorem bourgain_shared_floor_power_bound {N α τ ε : ℝ}
    (hN : 2 ≤ N) (hε : 0 ≤ ε) :
    128*N^(ε/8)*(N^(-bourgainSharedFloorExponent α τ ε))^2*
      (N^(|τ|+1))^3 ≤ N^(-α+τ/2) := by
  have hNp : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have h128 : (128 : ℝ) ≤ N^(7 : ℝ) := by
    calc
      (128 : ℝ) ≤ N^(7 : ℕ) := by
        have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hN 7
        norm_num at hh
        exact hh
      _ = N^(7 : ℝ) := (Real.rpow_natCast N 7).symm
  have heq : N^(7 : ℝ)*N^(ε/8)*(N^(-bourgainSharedFloorExponent α τ ε))^2*
      (N^(|τ|+1))^3 =
      N^(ε/8-2*bourgainSharedFloorExponent α τ ε+3*(|τ|+1)+7) := by
    rw [← Real.rpow_mul_natCast hNp.le, ← Real.rpow_mul_natCast hNp.le]
    rw [← Real.rpow_add hNp, ← Real.rpow_add hNp, ← Real.rpow_add hNp]
    congr 1
    norm_num
    ring
  calc
    _ ≤ N^(7 : ℝ)*N^(ε/8)*(N^(-bourgainSharedFloorExponent α τ ε))^2*
        (N^(|τ|+1))^3 := by gcongr
    _ = _ := heq
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN1 (bourgain_shared_floor_exponent hε)

/-- The cost of the low floor in the selected difference level is bounded
using its actual cardinality and the finite logarithmic index count. -/
theorem bourgain_difference_level_low_mass (W : Finset ℝ) (j : ℕ)
    {H a : ℝ} (hH : 0 ≤ H) (hW : 0 < W.card) :
    2*(Nat.log 2 W.card+1 : ℕ)*(2 : ℝ)^(j+1)*
      (2*H*a^2*((bourgainDifferenceLevel W j).card : ℝ)) ≤
        16*H*a^2*(W.card : ℝ)^3 := by
  have hlog : (Nat.log 2 W.card+1 : ℕ) ≤ W.card :=
    Nat.succ_le_iff.mpr (Nat.log_lt_self 2 hW.ne')
  have hlogR : ((Nat.log 2 W.card+1 : ℕ) : ℝ) ≤ (W.card : ℝ) := by exact_mod_cast hlog
  have hsize : (2 : ℝ)^j*((bourgainDifferenceLevel W j).card : ℝ) ≤
      2*(W.card : ℝ)^2 := by exact_mod_cast bourgainDifferenceLevel_card_le W j
  calc
    _ = 8*H*a^2*((Nat.log 2 W.card+1 : ℕ) : ℝ)*
        ((2 : ℝ)^j*((bourgainDifferenceLevel W j).card : ℝ)) := by rw [pow_succ]; ring
    _ ≤ 8*H*a^2*(W.card : ℝ)*(2*(W.card : ℝ)^2) := by gcongr
    _ = _ := by ring

/-- The physical power window bounds every actual retained subfamily. -/
theorem bourgain_retained_card_le_shared_power (P : LargeValuePattern)
    {W : Finset ℝ} (hsub : W ⊆ P.reflectedOrdinates) {τ δ : ℝ}
    (hδ : δ ≤ 1) (hT : P.T ≤ P.N^(τ+δ)) :
    (W.card : ℝ) ≤ 2*P.N^(|τ|+1) := by
  have hN1 := P.one_lt_N.le
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hc : (W.card : ℝ) ≤ (P.ordinates.card : ℝ) := by
    exact_mod_cast (Finset.card_le_card hsub).trans_eq P.reflectedOrdinates_card
  have hp : P.N^(τ+δ) ≤ P.N^(|τ|+1) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith [le_abs_self τ])
  have hone : 1 ≤ P.N^(|τ|+1) := Real.one_le_rpow hN1 (by positivity)
  linarith [P.ordinate_card_cast_le]

/-- The same floor works for every retained heavy level of the actual
pattern. Its doubled low contribution is below the source mass scale. -/
theorem bourgain_shared_floor_low_bound (P : LargeValuePattern)
    {W : Finset ℝ} (hsub : W ⊆ P.reflectedOrdinates) (j : ℕ)
    (hW : 0 < W.card) {α τ ε δ : ℝ}
    (hN : 2 ≤ P.N) (hε : 0 ≤ ε) (hδ : δ ≤ 1) (hT : P.T ≤ P.N^(τ+δ)) :
    2*(Nat.log 2 W.card+1 : ℕ)*(2 : ℝ)^(j+1)*
      (2*P.N^(ε/8)*(P.N^(-bourgainSharedFloorExponent α τ ε))^2*
        ((bourgainDifferenceLevel W j).card : ℝ)) ≤
      P.N^(-α)*(W.card : ℝ)^(3/2 : ℝ)*P.N^(τ/2) := by
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hcard := bourgain_retained_card_le_shared_power P hsub hδ hT
  have hR1 : (1 : ℝ) ≤ W.card := by exact_mod_cast hW
  have hpower : (1 : ℝ) ≤ (W.card : ℝ)^(3/2 : ℝ) :=
    Real.one_le_rpow hR1 (by norm_num)
  calc
    _ ≤ 16*P.N^(ε/8)*(P.N^(-bourgainSharedFloorExponent α τ ε))^2*(W.card : ℝ)^3 :=
      bourgain_difference_level_low_mass W j (by positivity) hW
    _ ≤ 16*P.N^(ε/8)*(P.N^(-bourgainSharedFloorExponent α τ ε))^2*
        (2*P.N^(|τ|+1))^3 := by gcongr
    _ = 128*P.N^(ε/8)*(P.N^(-bourgainSharedFloorExponent α τ ε))^2*
        (P.N^(|τ|+1))^3 := by ring
    _ ≤ P.N^(-α+τ/2) := bourgain_shared_floor_power_bound hN hε
    _ = P.N^(-α)*P.N^(τ/2) := Real.rpow_add hNp _ _
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left hpower
        (show 0 ≤ P.N^(-α)*P.N^(τ/2) by positivity)
      nlinarith

end TaoTrudgianYang2025
