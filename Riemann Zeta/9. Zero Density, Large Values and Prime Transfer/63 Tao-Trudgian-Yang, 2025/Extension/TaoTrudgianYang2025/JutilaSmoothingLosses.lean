import TaoTrudgianYang2025.JutilaSmoothingProfile

/-!
# Absorption of the complete powered Jutila loss

The bounds here consume the explicit coefficient of the actual
near/far reflection theorem. No loss bound is assumed.
-/

open Filter RiemannZeta.GuthMaynard

noncomputable section

namespace TaoTrudgianYang2025

/-- Divisor powering commutes with the real epsilon exponent. -/
theorem jutila_powered_divisor_loss (k M : ℕ) (θ : ℝ) :
    ((((2^k*M^k : ℕ) : ℝ)^θ)^2) = ((2*(M : ℝ))^θ)^(2*k) := by
  push_cast
  rw [← mul_pow, ← Real.rpow_natCast_mul (by positivity),
    mul_comm (k : ℝ) θ, Real.rpow_mul_natCast (by positivity), ← pow_mul]
  congr 1
  omega

/-- The prefix moment and smoothing cost use at most eight profile
factors per power, in addition to the original height epsilon. -/
theorem jutila_moment_loss_le_profile (k : ℕ) (θ T C : ℝ) {A : ℝ}
    (hA : 0 ≤ A) (hT : 0 ≤ T) :
    jutilaMomentLoss k (heathBrownSmoothingHeight T θ) T A θ θ *
        (16*C^2*((heathBrownSmoothingHeight T θ : ℝ)+2)^4)^k ≤
      (A*(16*C^2*(3 : ℝ)^4)^k) * jutilaSmoothingProfile θ T^(8*k)*T^θ := by
  let B := jutilaSmoothingProfile θ T
  have hc := jutila_smoothing_profile_components θ T
  have hB : 0 ≤ B := le_trans zero_le_one hc.1
  have hH : (heathBrownSmoothingHeight T θ : ℝ)+2 ≤ 3*B := by linarith [hc.2.2.1]
  have hl := hc.2.2.2.1
  have hd := hc.2.2.2.2
  unfold jutilaMomentLoss
  rw [jutila_powered_divisor_loss]
  calc
    _ ≤ (A*B^(2*k)*B^(2*k)*T^θ)*(16*C^2*(3*B)^4)^k := by gcongr
    _ = _ := by dsimp [B]; simp only [mul_pow, pow_mul]; ring

/-- After multiplication by the actual bin count, the entire smoothing
coefficient has a uniform arbitrarily small power cost. -/
theorem jutila_smoothing_coefficient_uniform
    (k : ℕ) {θ E F A C K L D : ℝ}
    (hθ : 0 < θ) (hθOne : θ ≤ 1)
    (hE : 0 ≤ E) (hF : 0 ≤ F) (hA : 0 ≤ A)
    (hK : 0 ≤ K) (hL : 0 ≤ L) (hD : 0 ≤ D) :
    ∃ B T₀ : ℝ, 0 < B ∧ 2 ≤ T₀ ∧
      ∀ T : ℝ, T₀ ≤ T →
        ((Nat.log 2 (Nat.floor T)+1 : ℕ) : ℝ) *
          jutilaSmoothingCoefficient k T θ E F A C K L D θ θ ≤
            B*T^(((16*k : ℕ) : ℝ)*θ+3*θ) := by
  obtain ⟨P₀, T₀, hP₀, hT₀, hp⟩ := jutila_smoothing_profile_uniform hθ hθOne
  let U : ℝ := E^(2*k)+(2*F)^(2*k)+
    (16*K+L*(3 : ℝ)^(heathBrownReflectionDerivativeOrder 0 θ+2)+2*D)^(2*k)
  let V : ℝ := A*(16*C^2*(3 : ℝ)^4)^k
  let B : ℝ := (2 : ℝ)^(2*k-1)*(U+V+1)*P₀^(8*k+1)
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨B, T₀, hB, hT₀, ?_⟩
  intro T hT
  let P := jutilaSmoothingProfile θ T
  have hT1 : 1 ≤ T := by linarith [hT₀.trans hT]
  have hTp : 0 < T := by linarith
  have hc := jutila_smoothing_profile_components θ T
  have hP1 : 1 ≤ P := hc.1
  have hPn : 0 ≤ P := by linarith
  have hpp : 1 ≤ P^(8*k)*T^θ :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hP1) (Real.one_le_rpow hT1 hθ.le)
  have hmoment := jutila_moment_loss_le_profile k θ T C hA hTp.le
  have hcoef : jutilaSmoothingCoefficient k T θ E F A C K L D θ θ ≤
      (2 : ℝ)^(2*k-1)*(U+V+1)*P^(8*k)*T^θ := by
    have hUle := mul_le_mul_of_nonneg_left hpp hU
    have hn : 0 ≤ P^(8*k)*T^θ := by positivity
    unfold jutilaSmoothingCoefficient
    change (2 : ℝ)^(2*k-1)*(U+_) ≤ _
    calc
      _ ≤ (2 : ℝ)^(2*k-1)*((U+V+1)*(P^(8*k)*T^θ)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        change _ ≤ _
        dsimp [V, P] at hUle hn ⊢
        nlinarith
      _ = _ := by ring
  have hcn : 0 ≤ jutilaSmoothingCoefficient k T θ E F A C K L D θ θ := by
    unfold jutilaSmoothingCoefficient jutilaMomentLoss
    positivity
  calc
    _ ≤ P*((2 : ℝ)^(2*k-1)*(U+V+1)*P^(8*k)*T^θ) :=
      mul_le_mul hc.2.1 hcoef hcn hPn
    _ = (2 : ℝ)^(2*k-1)*(U+V+1)*P^(8*k+1)*T^θ := by rw [pow_succ]; ring
    _ ≤ (2 : ℝ)^(2*k-1)*(U+V+1)*(P₀*T^(2*θ))^(8*k+1)*T^θ := by
      gcongr
      exact hp T hT
    _ = B*T^(((16*k : ℕ) : ℝ)*θ+3*θ) := by
      rw [mul_pow, ← Real.rpow_mul_natCast hTp.le]
      have he : 2*(θ*((8*k+1 : ℕ) : ℝ))+θ = ((16*k : ℕ) : ℝ)*θ+3*θ := by
        push_cast
        ring
      simp only [B, mul_assoc, ← Real.rpow_add hTp, he]

end TaoTrudgianYang2025
