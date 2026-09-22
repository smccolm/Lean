import TaoTrudgianYang2025.BourgainSmoothedPatterns

/-!
# Solving the retained-zeta cardinality recurrence

The value threshold below is an explicit numerical absorption condition.
It is not part of the unrestricted printed Lemma 4.1, whose full range
is not claimed by this high-value consumer.
-/

open Finset RiemannZeta.GuthMaynard

noncomputable section

namespace TaoTrudgianYang2025

/-- The elementary quadratic inequality with a retained nonnegative term. -/
theorem bourgain_quadratic_recurrence {R a b : ℝ}
    (hb : 0 ≤ b) (h : R^2 ≤ a*R+b) :
    R ≤ max a 0 + Real.sqrt b := by
  by_contra hn
  have hg : max a 0 + Real.sqrt b < R := lt_of_not_ge hn
  have hroot := Real.sqrt_nonneg b
  have hRp : 0 < R := by have := le_max_right a 0; linarith
  have ha := le_max_left a 0
  have hdiff : Real.sqrt b < R-a := by linarith
  have hm := mul_lt_mul_of_pos_left hdiff hRp
  have hrootR : Real.sqrt b ≤ R := by have := le_max_right a 0; linarith
  have hs := mul_le_mul_of_nonneg_right hrootR hroot
  nlinarith [Real.sq_sqrt hb]

/-- The actual fourth-powered Gram recurrence, with the zeta moment retained.
Only its cardinality-square term is absorbed by the displayed threshold. -/
theorem bourgain_retained_recurrence_card_le (Q : ℕ) (T H D V : ℝ) (W : Finset ℝ)
    (hH : 0 ≤ H) (hD : 0 ≤ D) (hV : 0 < V)
    (habs : 2*D*(Q : ℝ)^2 ≤ V^8)
    (hrec : (W.card : ℝ)^2*V^8 ≤ D*bourgainRetainedMomentCore 2 Q T H W) :
    (W.card : ℝ) ≤ 2*D*T^2/V^8 +
      Real.sqrt (2*D)*(Q : ℝ)*Real.sqrt (bourgainZetaDifferenceMoment W (H+1))/V^4 := by
  let R : ℝ := W.card
  let M := bourgainZetaDifferenceMoment W (H+1)
  have hM : 0 ≤ M := bourgainZetaDifferenceMoment_nonneg W (by linarith)
  have hv8 : 0 < V^8 := pow_pos hV _
  have hnorm : R^2 ≤ (2*D*T^2/V^8)*R + (2*D*(Q : ℝ)^2*M/V^8) := by
    have habsR := mul_le_mul_of_nonneg_left habs (sq_nonneg R)
    have hs : R^2*V^8 ≤ 2*D*T^2*R+2*D*(Q : ℝ)^2*M := by
      dsimp [bourgainRetainedMomentCore] at hrec
      change R^2*V^8 ≤ D*(R^2*(Q : ℝ)^2+R*T^2+M*(Q : ℝ)^2) at hrec
      nlinarith
    have hh := (le_div_iff₀ hv8).mpr hs
    convert hh using 1; ring
  have ha : 0 ≤ 2*D*T^2/V^8 := by positivity
  have hb : 0 ≤ 2*D*(Q : ℝ)^2*M/V^8 := by positivity
  have hs := bourgain_quadratic_recurrence hb hnorm
  rw [max_eq_left ha] at hs
  have he :
      Real.sqrt (2*D*(Q : ℝ)^2*M/V^8) =
        Real.sqrt (2*D)*(Q : ℝ)*Real.sqrt M/V^4 := by
    rw [Real.sqrt_div (by positivity), Real.sqrt_mul (by positivity),
      Real.sqrt_mul (by positivity), Real.sqrt_sq (Nat.cast_nonneg Q),
      show V^8 = (V^4)^2 by ring, Real.sqrt_sq (by positivity)]
  simpa only [he, R, M] using hs

/-- The source-scale three-term bound before endpoint constants are absorbed. -/
def bourgainRetainedCardinalityBound (N T V Z M : ℝ) : ℝ :=
  Z*(2*(2*N)^2/((V-1)/3)^2 +
    2*(Z*(4*N)^4)*T^2/((V-1)/3)^8 +
    Real.sqrt (2*(Z*(4*N)^4))*(2*N)*Real.sqrt M/((V-1)/3)^4)

/-- The solved expression has the three source powers, with every numerical
factor and the endpoint loss V-1 explicit. -/
theorem bourgainRetainedCardinalityBound_expand (N T V Z M : ℝ)
    (hZ : 0 ≤ Z) (hV : 1 < V) :
    bourgainRetainedCardinalityBound N T V Z M =
      (72*Z)*N^2/(V-1)^2 +
      (2*Z^2*(4 : ℝ)^4*(3 : ℝ)^8)*T^2*N^4/(V-1)^8 +
      (2*Z*Real.sqrt (2*Z)*(4 : ℝ)^2*(3 : ℝ)^4)*
        N^3*Real.sqrt M/(V-1)^4 := by
  have hv : V-1 ≠ 0 := by linarith
  have hs : Real.sqrt (2*(Z*(4*N)^4)) = Real.sqrt (2*Z)*(4*N)^2 := by
    rw [show 2*(Z*(4*N)^4) = (2*Z)*((4*N)^2)^2 by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (sq_nonneg _)]
  unfold bourgainRetainedCardinalityBound
  rw [hs]
  field_simp
  ring

/-- Exact value-threshold normalization; its N^6 cost is not suppressed. -/
theorem bourgain_retained_absorption_identity (N Z : ℝ) :
    (2*(Z*(4*N)^4)*(2*N)^2)*(3 : ℝ)^8 =
      (2*(4 : ℝ)^4*(2 : ℝ)^2*(3 : ℝ)^8)*Z*N^6 := by ring

/-- An actual two-separated source subfamily carries the retained zeta moment.
The original pattern's cardinality satisfies the solved bound in the
explicit high-value absorption range. No zeta estimate is a premise. -/
theorem bourgain_high_value_pattern_retained (cutoff : GMSmoothCutoff)
    {ν : ℝ} (hν : 0 < ν) :
    ∃ θ B T₀ : ℝ, 0 < θ ∧ θ ≤ 1 ∧ θ ≤ ν ∧ 0 < B ∧ 2 ≤ T₀ ∧
      ∀ P : LargeValuePattern,
        30 ≤ P.scale → 1 < P.V → T₀ ≤ P.T → P.N ≤ P.T →
        2*(B*P.T^ν*(4*P.N)^4)*(2*P.N)^2 ≤ ((P.V-1)/3)^8 →
        ∃ W : Finset ℝ,
          W ⊆ P.reflectedOrdinates ∧ IsSeparated 2 W ∧ InBaseInterval P.T W ∧
          (P.ordinates.card : ℝ) ≤ B*P.T^ν*(W.card : ℝ) ∧
          (P.ordinates.card : ℝ) ≤
            bourgainRetainedCardinalityBound P.N P.T P.V (B*P.T^ν)
              (bourgainZetaDifferenceMoment W
                ((heathBrownSmoothingHeight P.T θ : ℝ)+1)) := by
  obtain ⟨θ,B,T₀,hθ,hθ1,hθν,hB,hT₀,hp⟩ :=
    bourgain_smoothed_pattern_retained cutoff 2 (by norm_num) hν
  refine ⟨θ,B,T₀,hθ,hθ1,hθν,hB,hT₀,?_⟩
  intro P hN hV hT hNT habs
  have hTp : 0 < P.T := lt_of_lt_of_le (by linarith : (0 : ℝ) < T₀) hT
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hv : 0 < (P.V-1)/3 := by linarith
  let H := heathBrownSmoothingHeight P.T θ
  let Z := B*P.T^ν
  let D := Z*(4*P.N)^4
  have hZ : 0 ≤ Z := by dsimp [Z]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  obtain ⟨W,Q,hsub,hcard,hQ,hlow,hhigh,hsep,hbase,hg⟩ := hp P hN hV hT hNT
  refine ⟨W,hsub,hsep,hbase,hcard,?_⟩
  let M := bourgainZetaDifferenceMoment W ((H : ℝ)+1)
  have hM : 0 ≤ M := bourgainZetaDifferenceMoment_nonneg W (by positivity)
  have hmain := bourgainRetainedMomentCore_nonneg 2 Q hTp.le (Nat.cast_nonneg H) W
  have hr : (W.card : ℝ) ≤
      2*(2*P.N)^2/((P.V-1)/3)^2 + 2*D*P.T^2/((P.V-1)/3)^8 +
        Real.sqrt (2*D)*(2*P.N)*Real.sqrt M/((P.V-1)/3)^4 := by
    rcases hg with hsmall | hlarge
    · have hc : (W.card : ℝ) ≤ 2*(2*P.N)^2/((P.V-1)/3)^2 := by
        apply (le_div_iff₀ (sq_pos_of_pos hv)).mpr
        exact hsmall.trans (by gcongr)
      have h1 : 0 ≤ 2*D*P.T^2/((P.V-1)/3)^8 := by positivity
      have h2 : 0 ≤ Real.sqrt (2*D)*(2*P.N)*Real.sqrt M/((P.V-1)/3)^4 := by positivity
      linarith
    · have hd : Z*(2*(Q : ℝ))^4 ≤ D := by
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by positivity) (by linarith : 2*(Q : ℝ) ≤ 4*P.N) 4) hZ
      have ha : 2*D*(Q : ℝ)^2 ≤ ((P.V-1)/3)^8 :=
        (show 2*D*(Q : ℝ)^2 ≤ 2*D*(2*P.N)^2 by gcongr).trans habs
      have hrec : (W.card : ℝ)^2*((P.V-1)/3)^8 ≤ D*bourgainRetainedMomentCore 2 Q P.T H W :=
        hlarge.trans (mul_le_mul_of_nonneg_right hd hmain)
      have hs := bourgain_retained_recurrence_card_le Q P.T H D ((P.V-1)/3) W
        (Nat.cast_nonneg H) hD hv ha hrec
      have hc : (W.card : ℝ) ≤ 2*D*P.T^2/((P.V-1)/3)^8 +
          Real.sqrt (2*D)*(2*P.N)*Real.sqrt M/((P.V-1)/3)^4 :=
        hs.trans (by gcongr)
      have h0 : 0 ≤ 2*(2*P.N)^2/((P.V-1)/3)^2 := by positivity
      linarith
  exact hcard.trans (mul_le_mul_of_nonneg_left hr hZ)

end TaoTrudgianYang2025
