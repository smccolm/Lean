import TaoTrudgianYang2025.JutilaPhysicalPatterns

/-!
# Physical smoothing of Jutila's actual reflection errors

The smoothing height and derivative order are the native analytic choices.
The scale restriction Q ≤ 2T is explicit; no claim about the complementary
short-height range is made here.
-/

open Finset
open scoped BigOperators
open RiemannZeta.GuthMaynard

noncomputable section

namespace TaoTrudgianYang2025

/-- The zero-frequency error decays with the same derivative budget as
the three nonzero-frequency reflection errors. -/
theorem jutila_zero_mode_smoothing_le {a θ T F : ℝ} {Q : ℕ}
    (hθ : 0 < θ) (hT : 1 ≤ T) (hQT : (Q : ℝ) ≤ 2*T) (hF : 0 ≤ F) :
    (Q : ℝ)*F/(heathBrownSmoothingHeight T θ : ℝ)^
        heathBrownReflectionDerivativeOrder a θ ≤ 2*F*T^(-a) := by
  have hTp : 0 < T := by linarith
  have hi := one_div_heathBrownSmoothingHeight_pow_order_le (A := a) hθ hT
  have hpow : T * T^(-(a+4)) ≤ T^(-a) := by
    calc
      T * T^(-(a+4)) = T^(1-(a+4)) := by
        conv_lhs => lhs; rw [← Real.rpow_one T]
        rw [← Real.rpow_add hTp]
        congr 1
      _ ≤ T^(-a) := Real.rpow_le_rpow_of_exponent_le hT (by linarith)
  calc
    (Q : ℝ)*F/(heathBrownSmoothingHeight T θ : ℝ)^
        heathBrownReflectionDerivativeOrder a θ ≤
        (2*T)*F*T^(-(a+4)) := by
          rw [div_eq_mul_one_div]
          gcongr
    _ = 2*F*(T*T^(-(a+4))) := by ring
    _ ≤ 2*F*T^(-a) := mul_le_mul_of_nonneg_left hpow (by positivity)

/-- The three physical terms that remain after reflection and smoothing. -/
def jutilaMomentCore (k Q : ℕ) (T : ℝ) (W : Finset ℝ) : ℝ :=
  (W.card : ℝ)^2*(Q : ℝ)^k + (W.card : ℝ)*T^k +
    (W.card : ℝ)^(5/4 : ℝ)*T^(1/2 : ℝ)*(Q : ℝ)^k

/-- The complete coefficient after the native smoothing substitution.
It includes all near, reflected, logarithmic and divisor costs. -/
def jutilaSmoothingCoefficient (k : ℕ) (T θ E F A C K L D ε η : ℝ) : ℝ :=
  (2 : ℝ)^(2*k-1) *
    (E^(2*k) + (2*F)^(2*k) +
      (16*K + L*(3 : ℝ)^(heathBrownReflectionDerivativeOrder 0 θ+2) + 2*D)^(2*k) +
      jutilaMomentLoss k (heathBrownSmoothingHeight T θ) T A ε η *
        (16*C^2*((heathBrownSmoothingHeight T θ : ℝ)+2)^4)^k)

/-- The actual physical envelope is bounded by the three source-scale
terms with a single explicit coefficient. All reflection errors have
been discharged by the native analytic smoothing theorem. -/
theorem jutila_physical_envelope_smoothing_le
    (k Q : ℕ) (T : ℝ) (W : Finset ℝ) {θ E F A C K L D ε η : ℝ}
    (hθ : 0 < θ) (hθOne : θ ≤ 1) (hT : 1 ≤ T) (hQ : 0 < Q)
    (hQT : (Q : ℝ) ≤ 2*T) (hF : 0 ≤ F)
    (hK : 0 ≤ K) (hL : 0 ≤ L) (hD : 0 ≤ D) :
    jutilaPhysicalEnvelope (heathBrownReflectionDerivativeOrder 0 θ) k Q
        (heathBrownSmoothingHeight T θ) T W E F A C K L D ε η ≤
      jutilaSmoothingCoefficient k T θ E F A C K L D ε η *
        jutilaMomentCore k Q T W := by
  have hTp : 0 < T := by linarith
  let H := heathBrownSmoothingHeight T θ
  let q := heathBrownReflectionDerivativeOrder 0 θ
  let B : ℝ := 16*K+L*(3 : ℝ)^(q+2)+2*D
  let X := jutilaMomentCore k Q T W
  have hx : 0 ≤ X := by dsimp [X, jutilaMomentCore]; positivity
  have hrq : (W.card : ℝ)^2*(Q : ℝ)^k ≤ X := by
    dsimp [X, jutilaMomentCore]
    have h1 : 0 ≤ (W.card : ℝ)*T^k := by positivity
    have h2 : 0 ≤ (W.card : ℝ)^(5/4 : ℝ)*T^(1/2 : ℝ)*(Q : ℝ)^k := by positivity
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
  have hm : jutilaPhysicalMain k Q H T W C =
      (16*C^2*((H : ℝ)+2)^4)^k*X := rfl
  unfold jutilaPhysicalEnvelope jutilaSmoothingCoefficient
  change (2 : ℝ)^(2*k-1) * (_ + _ + _) ≤ (2 : ℝ)^(2*k-1) * (_ + _ + _ + _) * X
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  change _ + jutilaMomentLoss k H T A ε η * jutilaPhysicalMain k Q H T W C + _ ≤ _
  rw [hm]
  nlinarith

end TaoTrudgianYang2025
