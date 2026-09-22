import TaoTrudgianYang2025.BourgainCommonCorrelation
import TaoTrudgianYang2025.BourgainSliceSelection

/-!
# Weighted actual component masses before the common-shift argument

The two lower estimates use the already constructed component band, its
actual fourth moment, and the common relative and correlation levels.
The remaining dyadic difference-level loss is bounded logarithmically,
uniformly over localized components.
-/

open MeasureTheory RiemannZeta.GuthMaynard
open scoped Interval Classical

set_option maxHeartbeats 800000

noncomputable section

namespace TaoTrudgianYang2025

def bourgainDifferenceLogLoss (N τ : ℝ) : ℝ :=
  3+(|τ|+1)*Real.log N/Real.log 2

theorem bourgainDifferenceLogLoss_pos {N : ℝ} (hN : 1 ≤ N) (τ : ℝ) :
    0 < bourgainDifferenceLogLoss N τ := by
  have hl := Real.log_nonneg hN
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  dsimp only [bourgainDifferenceLogLoss]
  positivity

theorem bourgain_difference_level_count_log_bound {N τ : ℝ} {R : ℕ}
    (hN : 1 ≤ N) (hR : 0 < R) (hsize : (R : ℝ) ≤ 2*N^(|τ|+1)) :
    (Nat.log 2 R+1 : ℕ) ≤ bourgainDifferenceLogLoss N τ := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hRp : (0 : ℝ) < R := by exact_mod_cast hR
  have hlog : Real.log (R : ℝ) ≤ Real.log 2+(|τ|+1)*Real.log N := by
    calc
      _ ≤ Real.log (2*N^(|τ|+1)) := Real.log_le_log hRp hsize
      _ = _ := by rw [Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hNp _).ne',
        Real.log_rpow hNp]
  have hc := heathBrown_natCast_clog_two_le_one_add_log R hR
  have hn : (Nat.log 2 R : ℝ) ≤ (Nat.clog 2 R : ℝ) := by
    exact_mod_cast Nat.log_le_clog 2 R
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hd := div_le_div_of_nonneg_right hlog htwo.le
  rw [add_div, div_self htwo.ne'] at hd
  simp only [Nat.cast_add, Nat.cast_one, bourgainDifferenceLogLoss]
  linarith

/-- Actual cardinality and physical height discharge the uniform logarithmic
difference-level count needed by the selected family. -/
theorem bourgain_retained_difference_level_count (P : LargeValuePattern)
    {W : Finset ℝ} (hsub : W ⊆ P.reflectedOrdinates) (hW : 0 < W.card)
    {τ δ : ℝ} (hδ : δ ≤ 1) (hT : P.T ≤ P.N^(τ+δ)) :
    (Nat.log 2 W.card+1 : ℕ) ≤ bourgainDifferenceLogLoss P.N τ := by
  exact bourgain_difference_level_count_log_bound P.one_lt_N.le hW
    (bourgain_retained_card_le_shared_power P hsub hδ hT)

/-- Two genuine lower bounds for the weighted component occupancy.
The second uses the actual fourth-moment measure bound to remove the
amplitude from its coefficient. -/
theorem BourgainComponentBand.weighted_mass_lower
    {N T B C τ α ε : ℝ} {W : Finset ℝ} {j q : ℕ}
    (hband : BourgainComponentBand N T B C τ α ε W j q) (hN : 0 < N)
    {s d Z : ℝ} (hs : 0 < s) (hd : 0 < d)
    (hZ : (Nat.log 2 W.card+1 : ℕ) ≤ Z)
    (hrel : (2 : ℝ)^j ≤ 2*d*(W.card : ℝ))
    (hcorr : s ≤ bourgainZetaBandCorrelation (bourgainDifferenceLevel W j)
      (N^(ε/8)) (T+N^(ε/8)+1)
      (N^(-bourgainSharedFloorExponent α τ ε)*(2 : ℝ)^q)) :
    let H := N^(ε/8)
    let U := T+H+1
    let J := bourgainZetaBandCount B U (N^(-bourgainSharedFloorExponent α τ ε))
    let V := N^(-bourgainSharedFloorExponent α τ ε)*(2 : ℝ)^q
    let μ := volume.real (bourgainZetaBand U V)
    let M := bourgainZetaBandMass (bourgainDifferenceLevel W j) H U V
    let R := (W.card : ℝ)
    s^2*μ*R/(2*H) ≤ R*M ∧
      (N^(-α)*N^(τ/2)/(32*Z*(J : ℝ)*d*Real.sqrt (C*U^(1+ε))))*
        Real.sqrt μ*R^(3/2 : ℝ) < R*M := by
  rcases hband with ⟨_, hD, hpow, _, _, _, _, hV, hM, hμ, hm, h4,
    hcard, _, hr, heq, _⟩
  let D := bourgainDifferenceLevel W j
  let H := N^(ε/8)
  let U := T+H+1
  let J := bourgainZetaBandCount B U (N^(-bourgainSharedFloorExponent α τ ε))
  let V := N^(-bourgainSharedFloorExponent α τ ε)*(2 : ℝ)^q
  let μ := volume.real (bourgainZetaBand U V)
  let M := bourgainZetaBandMass D H U V
  let R := (W.card : ℝ)
  let r := bourgainZetaBandCorrelation D H U V
  let Y := C*U^(1+ε)
  have hH : 0 < H := Real.rpow_pos_of_pos hN _
  have hR : 0 < R := by
    dsimp only [R]
    exact_mod_cast (Nat.pow_pos (by norm_num : 0 < (2 : ℕ))).trans_le hpow
  have hDp : (0 : ℝ) < D.card := by exact_mod_cast hD.card_pos
  have hY : 0 < Y := (mul_pos (pow_pos hV 4) hμ).trans_le h4
  have hZp : 0 < Z := lt_of_lt_of_le (by positivity) hZ
  have hJp : (0 : ℝ) < J := by exact_mod_cast bourgainZetaBandCount_pos _ _ _
  have hsm : 0 < Real.sqrt μ := Real.sqrt_pos.mpr hμ
  have hMY : V^2*Real.sqrt μ ≤ Real.sqrt Y := by
    apply Real.le_sqrt_of_sq_le
    calc
      (V^2*Real.sqrt μ)^2 = V^4*μ := by rw [mul_pow, Real.sq_sqrt hμ.le]; ring
      _ ≤ Y := h4
  have hden : 0 < 32*Z*(J : ℝ)*d*Real.sqrt Y := by positivity
  constructor
  · have hsq : M^2 = r^2*μ*(D.card : ℝ) := by
      change M = r*Real.sqrt μ*Real.sqrt (D.card : ℝ) at heq
      rw [heq, mul_pow, mul_pow, Real.sq_sqrt hμ.le, Real.sq_sqrt hDp.le]
    have hprod := mul_le_mul_of_nonneg_left hcard hM.le
    have hc : r^2*μ ≤ 2*H*M := by
      apply (mul_le_mul_iff_of_pos_right hDp).mp
      nlinarith [hprod]
    have hsr : s^2 ≤ r^2 := pow_le_pow_left₀ hs.le hcorr 2
    have hbound : s^2*μ ≤ 2*H*M :=
      (mul_le_mul_of_nonneg_right hsr hμ.le).trans hc
    apply (div_le_iff₀ (by positivity : 0 < 2*H)).mpr
    nlinarith [mul_le_mul_of_nonneg_right hbound hR.le]
  · have hmass : N^(-α)*R^(3/2 : ℝ)*N^(τ/2) <
        32*Z*(J : ℝ)*d*V^2*(R*M) := by
      apply lt_of_lt_of_le hm
      calc
        _ = 16*(Nat.log 2 W.card+1 : ℕ)*(2 : ℝ)^j*(J : ℝ)*V^2*M := by
          rw [pow_succ]
          ring
        _ ≤ 16*(Nat.log 2 W.card+1 : ℕ)*(2*d*R)*(J : ℝ)*V^2*M := by
          gcongr
        _ ≤ 16*Z*(2*d*R)*(J : ℝ)*V^2*M := by gcongr
        _ = _ := by ring
    have hweighted := mul_lt_mul_of_pos_right hmass hsm
    have hright :
        (32*Z*(J : ℝ)*d*V^2*(R*M))*Real.sqrt μ ≤
          (32*Z*(J : ℝ)*d*Real.sqrt Y)*(R*M) := by
      calc
        _ = (32*Z*(J : ℝ)*d*(R*M))*(V^2*Real.sqrt μ) := by ring
        _ ≤ (32*Z*(J : ℝ)*d*(R*M))*Real.sqrt Y :=
          mul_le_mul_of_nonneg_left hMY (by positivity)
        _ = _ := by ring
    have hfinal : (N^(-α)*N^(τ/2)*Real.sqrt μ*R^(3/2 : ℝ)) /
        (32*Z*(J : ℝ)*d*Real.sqrt Y) < R*M := by
      apply (div_lt_iff₀ hden).mpr
      nlinarith [hweighted.trans_le hright]
    convert hfinal using 1
    ring

end TaoTrudgianYang2025
