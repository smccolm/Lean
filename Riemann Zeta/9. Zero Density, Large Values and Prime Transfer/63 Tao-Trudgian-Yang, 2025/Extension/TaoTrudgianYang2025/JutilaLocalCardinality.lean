import TaoTrudgianYang2025.JutilaRecurrence

/-!
# Cardinality bounds on the actual Jutila source pattern

The spaced witnesses are eliminated, while the explicit value threshold
needed for absorption is kept visible at the physical source scale.
-/

open Finset RiemannZeta.GuthMaynard

noncomputable section

namespace TaoTrudgianYang2025

/-- The three-term local bound, with the source endpoint loss and the
uniform smoothing factor visible. This is only a numerical expression. -/
def jutilaLocalCardinalityBound (k : ℕ) (N T V Z : ℝ) : ℝ :=
  Z*(2*(2*N)^2/((V-1)/3)^2 +
    4*(Z*(4*N)^(2*k))*T^k/((V-1)/3)^(4*k) +
    4*(Z*(4*N)^(2*k))^2*T*(2*N)^(2*k)/((V-1)/3)^(8*k))

/-- Actual source cardinality after solving both alternatives. Constants
precede the pattern; the high-value absorption condition is numerical
and is not an assumed cardinality bound. -/
theorem jutila_local_pattern_cardinality (cutoff : GMSmoothCutoff)
    (k : ℕ) (hk : 0 < k) {ν : ℝ} (hν : 0 < ν) :
    ∃ B T₀ : ℝ, 0 < B ∧ 2 ≤ T₀ ∧
      ∀ P : LargeValuePattern,
        30 ≤ P.scale → 1 < P.V → T₀ ≤ P.T → P.N ≤ P.T →
        2*(B*P.T^ν*(4*P.N)^(2*k))*(2*P.N)^k ≤ ((P.V-1)/3)^(4*k) →
        (P.ordinates.card : ℝ) ≤
          jutilaLocalCardinalityBound k P.N P.T P.V (B*P.T^ν) := by
  obtain ⟨B, T₀, hB, hT₀, hp⟩ := jutila_smoothed_pattern_bound cutoff k hk hν
  refine ⟨B, T₀, hB, hT₀, ?_⟩
  intro P hN hV hT hNT habs
  have hTp : 0 < P.T := lt_of_lt_of_le (by linarith : (0 : ℝ) < T₀) hT
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hv : 0 < (P.V-1)/3 := by linarith
  let Z := B*P.T^ν
  let D := Z*(4*P.N)^(2*k)
  have hZ : 0 ≤ Z := by dsimp [Z]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  obtain ⟨W, Q, hsub, hcard, hQ, hlow, hhigh, hsep, hbase, hg⟩ := hp P hN hV hT hNT
  have hq : (0 : ℝ) ≤ Q := by positivity
  have hmain : 0 ≤ jutilaMomentCore k Q P.T W := by unfold jutilaMomentCore; positivity
  have hr :
      (W.card : ℝ) ≤ 2*(2*P.N)^2/((P.V-1)/3)^2 +
        4*D*P.T^k/((P.V-1)/3)^(4*k) +
        4*D^2*P.T*(2*P.N)^(2*k)/((P.V-1)/3)^(8*k) := by
    rcases hg with hsmall | hlarge
    · have hc : (W.card : ℝ) ≤ 2*(2*P.N)^2/((P.V-1)/3)^2 := by
        apply (le_div_iff₀ (sq_pos_of_pos hv)).mpr
        exact hsmall.trans (by gcongr)
      have h1 : 0 ≤ 4*D*P.T^k/((P.V-1)/3)^(4*k) := by positivity
      have h2 : 0 ≤ 4*D^2*P.T*(2*P.N)^(2*k)/((P.V-1)/3)^(8*k) := by positivity
      linarith
    · have hd : Z*(2*(Q : ℝ))^(2*k) ≤ D := by
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by positivity) (by linarith : 2*(Q : ℝ) ≤ 4*P.N) (2*k)) hZ
      have ha : 2*D*(Q : ℝ)^k ≤ ((P.V-1)/3)^(4*k) :=
        (show 2*D*(Q : ℝ)^k ≤ 2*D*(2*P.N)^k by gcongr).trans habs
      have hrec : (W.card : ℝ)^2*((P.V-1)/3)^(4*k) ≤ D*jutilaMomentCore k Q P.T W :=
        hlarge.trans (mul_le_mul_of_nonneg_right hd hmain)
      have hs := jutila_powered_recurrence_card_le k Q P.T D ((P.V-1)/3) W hTp.le hD hv ha hrec
      have hc :
          (W.card : ℝ) ≤ 4*D*P.T^k/((P.V-1)/3)^(4*k) +
            4*D^2*P.T*(2*P.N)^(2*k)/((P.V-1)/3)^(8*k) :=
        hs.trans (by gcongr)
      have h0 : 0 ≤ 2*(2*P.N)^2/((P.V-1)/3)^2 := by positivity
      linarith
  exact hcard.trans (mul_le_mul_of_nonneg_left hr hZ)

end TaoTrudgianYang2025
