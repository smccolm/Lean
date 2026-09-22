import TaoTrudgianYang2025.BourgainPhysicalPatterns
import TaoTrudgianYang2025.JutilaSmoothingLosses

/-!
# Smoothing the retained-zeta physical Gram estimate

The actual native height and derivative order discharge the reflection
errors and the Mellin tail. The zeta difference moment is retained,
with its enlarged integration radius explicit.
-/

open Finset RiemannZeta.GuthMaynard

noncomputable section

namespace TaoTrudgianYang2025

/-- The native derivative budget bounds the complete retained Mellin tail. -/
theorem bourgain_mellin_tail_smoothing_le {θ T : ℝ}
    (hθ : 0 < θ) (hT : 1 ≤ T) :
    (1+T)^2 /
      (1+(heathBrownSmoothingHeight T θ : ℝ))^
        (2*heathBrownReflectionDerivativeOrder 0 θ) ≤ 4 := by
  let H := heathBrownSmoothingHeight T θ
  let q := heathBrownReflectionDerivativeOrder 0 θ
  have hTp : 0 < T := by linarith
  have hHp : (0 : ℝ) < H := by exact_mod_cast heathBrownSmoothingHeight_pos T θ
  have hi : 1/(H : ℝ)^q ≤ 1/T := by
    calc
      _ ≤ T^(-(0+4 : ℝ)) :=
        one_div_heathBrownSmoothingHeight_pow_order_le (A := 0) hθ hT
      _ ≤ T^(-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hT (by norm_num)
      _ = 1/T := by rw [Real.rpow_neg_one, one_div]
  have htH : T ≤ (H : ℝ)^q := by
    have hh := (div_le_div_iff₀ (pow_pos hHp q) hTp).mp hi
    simpa using hh
  have hh : (H : ℝ)^q ≤ (1+(H : ℝ))^q := by gcongr; linarith
  have hp : (1+T)^2 ≤ (2*(1+(H : ℝ))^q)^2 :=
    pow_le_pow_left₀ (by linarith) (by linarith : 1+T ≤ 2*(1+(H : ℝ))^q) 2
  have hpow : (1+(H : ℝ))^(2*q) = ((1+(H : ℝ))^q)^2 := by
    rw [← pow_mul, Nat.mul_comm]
  change (1+T)^2/(1+(H : ℝ))^(2*q) ≤ 4
  apply (div_le_iff₀ (by positivity)).mpr
  rw [hpow]
  nlinarith

/-- Nonnegativity of the actual weighted integer-window zeta moment. -/
theorem bourgainZetaDifferenceMoment_nonneg (W : Finset ℝ) {H : ℝ}
    (hH : 0 ≤ H) : 0 ≤ bourgainZetaDifferenceMoment W H := by
  unfold bourgainZetaDifferenceMoment
  exact Finset.sum_nonneg (fun ℓ _ =>
    mul_nonneg (Nat.cast_nonneg _) (bourgainLocalZetaSquare_nonneg hH ℓ))

/-- The three terms kept before the source scalar absorption step. -/
def bourgainRetainedMomentCore (k Q : ℕ) (T H : ℝ) (W : Finset ℝ) : ℝ :=
  (W.card : ℝ)^2*(Q : ℝ)^k + (W.card : ℝ)*T^k +
    bourgainZetaDifferenceMoment W (H+1)*(Q : ℝ)^k

theorem bourgainRetainedMomentCore_nonneg (k Q : ℕ) {T H : ℝ}
    (hT : 0 ≤ T) (hH : 0 ≤ H) (W : Finset ℝ) :
    0 ≤ bourgainRetainedMomentCore k Q T H W := by
  have hm := bourgainZetaDifferenceMoment_nonneg W (by linarith : 0 ≤ H+1)
  unfold bourgainRetainedMomentCore
  positivity

/-- All physical errors are absorbed into an explicit smoothing coefficient;
no estimate of the retained zeta moment is a hypothesis. -/
theorem bourgain_physical_envelope_smoothing_le
    (k Q : ℕ) (T : ℝ) (W : Finset ℝ) {θ E F A C K L D : ℝ}
    (hθ : 0 < θ) (hθOne : θ ≤ 1) (hT : 1 ≤ T) (hQ : 0 < Q)
    (hQT : (Q : ℝ) ≤ 2*T) (hF : 0 ≤ F) (hA : 0 ≤ A)
    (hK : 0 ≤ K) (hL : 0 ≤ L) (hD : 0 ≤ D) :
    bourgainPhysicalEnvelope (heathBrownReflectionDerivativeOrder 0 θ) k Q
        (heathBrownSmoothingHeight T θ) T W E F A C K L D θ ≤
      (4*((heathBrownSmoothingHeight T θ : ℝ)+1)) *
        jutilaSmoothingCoefficient k T θ E F A C K L D θ θ *
        bourgainRetainedMomentCore k Q T (heathBrownSmoothingHeight T θ) W := by
  have hTp : 0 < T := by linarith
  let H := heathBrownSmoothingHeight T θ
  let q := heathBrownReflectionDerivativeOrder 0 θ
  let B : ℝ := 16*K+L*(3 : ℝ)^(q+2)+2*D
  let X := bourgainRetainedMomentCore k Q T H W
  let J : ℝ := 4*((H : ℝ)+1)
  have hH1 : (1 : ℝ) ≤ H := by exact_mod_cast heathBrownSmoothingHeight_pos T θ
  have hJ : 1 ≤ J := by dsimp [J]; linarith
  have hM := bourgainZetaDifferenceMoment_nonneg W
    (by positivity : 0 ≤ (H : ℝ)+1)
  have hx : 0 ≤ X := bourgainRetainedMomentCore_nonneg k Q hTp.le (Nat.cast_nonneg H) W
  have hrq : (W.card : ℝ)^2*(Q : ℝ)^k ≤ X := by
    dsimp [X, bourgainRetainedMomentCore]
    have h1 : 0 ≤ (W.card : ℝ)*T^k := by positivity
    have h2 : 0 ≤ bourgainZetaDifferenceMoment W ((H : ℝ)+1)*(Q : ℝ)^k := by positivity
    linarith
  have hrt : (W.card : ℝ)*T^k ≤ X := by
    dsimp [X, bourgainRetainedMomentCore]
    have h1 : 0 ≤ (W.card : ℝ)^2*(Q : ℝ)^k := by positivity
    have h2 : 0 ≤ bourgainZetaDifferenceMoment W ((H : ℝ)+1)*(Q : ℝ)^k := by positivity
    linarith
  have hmq : bourgainZetaDifferenceMoment W ((H : ℝ)+1)*(Q : ℝ)^k ≤ X := by
    dsimp [X, bourgainRetainedMomentCore]
    have h1 : 0 ≤ (W.card : ℝ)^2*(Q : ℝ)^k := by positivity
    have h2 : 0 ≤ (W.card : ℝ)*T^k := by positivity
    linarith
  have hqone : (1 : ℝ) ≤ (Q : ℝ)^k := one_le_pow₀ (by exact_mod_cast hQ)
  have hr : (W.card : ℝ)^2 ≤ X :=
    (le_mul_of_one_le_right (by positivity) hqone).trans hrq
  have hz : (Q : ℝ)*F/(H : ℝ)^q ≤ 2*F := by
    simpa only [H, q, neg_zero, Real.rpow_zero, mul_one] using
      (jutila_zero_mode_smoothing_le (a := 0) hθ hT hQT hF)
  have he : heathBrownSharpUniformReflectionError K L D q Q H T ≤ B := by
    simpa only [B, H, q, neg_zero, Real.rpow_zero, mul_one] using
      (heathBrownSharpUniformReflectionError_smoothing_le (A := 0)
        hθ hθOne hT hQ hQT hK hL hD)
  have hzn : 0 ≤ (Q : ℝ)*F/(H : ℝ)^q := by positivity
  have hen : 0 ≤ heathBrownSharpUniformReflectionError K L D q Q H T := by
    unfold heathBrownSharpUniformReflectionError
    positivity
  have hnear : (W.card : ℝ)^2 *
      (E^(2*k)*(Q : ℝ)^k + ((Q : ℝ)*F/(H : ℝ)^q)^(2*k)) ≤
      (E^(2*k)+(2*F)^(2*k))*X := by
    have hEpow : 0 ≤ E^(2*k) := by rw [pow_mul]; exact pow_nonneg (sq_nonneg E) k
    have h1 := mul_le_mul_of_nonneg_left hrq hEpow
    have h2 := mul_le_mul hr (pow_le_pow_left₀ hzn hz (2*k)) (by positivity) hx
    nlinarith
  have herr : (W.card : ℝ)^2 *
      (heathBrownSharpUniformReflectionError K L D q Q H T)^(2*k) ≤ B^(2*k)*X := by
    have hh := mul_le_mul hr (pow_le_pow_left₀ hen he (2*k)) (by positivity) hx
    nlinarith
  have htail := bourgain_mellin_tail_smoothing_le hθ hT
  have hmaincore :
      (W.card : ℝ)*T^k + bourgainMomentRemainder q T H W*(Q : ℝ)^k ≤ J*X := by
    have ht := mul_le_mul_of_nonneg_left htail
      (by positivity : 0 ≤ (W.card : ℝ)^2*(Q : ℝ)^k)
    have hm := mul_le_mul_of_nonneg_left hmq (Nat.cast_nonneg H)
    have hr4 := mul_le_mul_of_nonneg_left hrq (by norm_num : (0 : ℝ) ≤ 4)
    dsimp [bourgainMomentRemainder, q, H, J] at *
    simp only [div_eq_mul_inv] at ht ⊢
    nlinarith [mul_nonneg (sub_nonneg.mpr hH1) hx]
  have hloss : jutilaMomentLoss k H T A 0 θ ≤ jutilaMomentLoss k H T A θ θ := by
    unfold jutilaMomentLoss
    rw [Real.rpow_zero]
    have ht := Real.one_le_rpow hT hθ.le
    gcongr
  have hloss0 : 0 ≤ jutilaMomentLoss k H T A 0 θ := by unfold jutilaMomentLoss; positivity
  have hloss1 : 0 ≤ jutilaMomentLoss k H T A θ θ := by unfold jutilaMomentLoss; positivity
  have hmain :
      jutilaMomentLoss k H T A 0 θ * bourgainPhysicalMain q k Q H T W C ≤
        J*(jutilaMomentLoss k H T A θ θ*(16*C^2*((H : ℝ)+2)^4)^k)*X := by
    unfold bourgainPhysicalMain
    calc
      _ ≤ jutilaMomentLoss k H T A 0 θ *
          ((16*C^2*((H : ℝ)+2)^4)^k*(J*X)) := by gcongr
      _ ≤ jutilaMomentLoss k H T A θ θ *
          ((16*C^2*((H : ℝ)+2)^4)^k*(J*X)) := by gcongr
      _ = _ := by ring
  have hnear0 : 0 ≤ (E^(2*k)+(2*F)^(2*k))*X := by
    have heven : 0 ≤ E^(2*k) := by rw [pow_mul]; exact pow_nonneg (sq_nonneg E) k
    positivity
  have herr0 : 0 ≤ B^(2*k)*X := by dsimp [B]; positivity
  have hnearJ := hnear.trans (le_mul_of_one_le_left hnear0 hJ)
  have herrJ := herr.trans (le_mul_of_one_le_left herr0 hJ)
  unfold bourgainPhysicalEnvelope jutilaSmoothingCoefficient
  change (2 : ℝ)^(2*k-1)*(_+_+_) ≤ J*((2 : ℝ)^(2*k-1)*(_+_+_+_))*X
  calc
    _ ≤ (2 : ℝ)^(2*k-1) *
        (J*((E^(2*k)+(2*F)^(2*k))*X) +
          J*(jutilaMomentLoss k H T A θ θ*(16*C^2*((H : ℝ)+2)^4)^k)*X +
          J*(B^(2*k)*X)) :=
      mul_le_mul_of_nonneg_left (add_le_add (add_le_add hnearJ hmain) herrJ) (by positivity)
    _ = _ := by dsimp [B, H, q]; ring

end TaoTrudgianYang2025
