import TaoTrudgianYang2025.BourgainComparisonLogarithm

/-!
# Fixed-parameter limit algebra for the finite logarithmic comparison

These are supporting limit deductions. The source family's branch selection
and the final removal of positive accuracy parameters remain separate work.
-/

open Filter Topology

set_option maxHeartbeats 800000

noncomputable section

namespace TaoTrudgianYang2025

theorem bourgain_tendsto_logb_const (N : ℕ → ℝ)
    (hN : Tendsto N atTop atTop) (C : ℝ) :
    Tendsto (fun n => Real.logb (N n) C) atTop (nhds 0) := by
  exact tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.comp hN)

/-- All fixed multiplicative factors disappear in the limit. The stated
finite comparison is a genuine narrower premise, not the limiting conclusion. -/
theorem bourgain_fixed_logarithmic_limit {σ τ α χ δ E a r x G K : ℝ}
    (N R X : ℕ → ℝ) (hN : Tendsto N atTop atTop)
    (hr : Tendsto (fun n => Real.logb (N n) (R n)) atTop (nhds r))
    (hx : Tendsto (fun n => Real.logb (N n) (X n)) atTop (nhds x))
    (hcomp : ∀ᶠ n in atTop,
      max (-2*α+2*σ+Real.logb (N n) (X n)+Real.logb (N n) (R n)-E-2*δ-Real.logb (N n) G)
        (-α-χ/2+2*σ+Real.logb (N n) (X n)/2+3*Real.logb (N n) (R n)/2-
          E/2-2*δ-Real.logb (N n) (2*G)/2) ≤
      Real.logb (N n) (3*K)+a+
        heathBrownDoubleZetaExponent τ (Real.logb (N n) (R n))/2+
        heathBrownDoubleZetaExponent τ (Real.logb (N n) (X n))/2) :
    max (-2*α+2*σ+x+r-E-2*δ) (-α-χ/2+2*σ+x/2+3*r/2-E/2-2*δ) ≤
      a+heathBrownDoubleZetaExponent τ r/2+heathBrownDoubleZetaExponent τ x/2 := by
  have hG := bourgain_tendsto_logb_const N hN G
  have hG₂ := bourgain_tendsto_logb_const N hN (2*G)
  have hK := bourgain_tendsto_logb_const N hN (3*K)
  have hleft₁ : Tendsto
      (fun n => -2*α+2*σ+Real.logb (N n) (X n)+Real.logb (N n) (R n)-
        E-2*δ-Real.logb (N n) G) atTop (nhds (-2*α+2*σ+x+r-E-2*δ)) := by
    simpa only [sub_zero] using
      (((((hx.const_add (-2*α+2*σ)).add hr).sub_const E).sub_const (2*δ)).sub hG)
  have hleft₂ : Tendsto
      (fun n => -α-χ/2+2*σ+Real.logb (N n) (X n)/2+3*Real.logb (N n) (R n)/2-
        E/2-2*δ-Real.logb (N n) (2*G)/2)
      atTop (nhds (-α-χ/2+2*σ+x/2+3*r/2-E/2-2*δ)) := by
    simpa only [zero_div, sub_zero] using
      ((((((hx.div_const 2).const_add (-α-χ/2+2*σ)).add
        ((hr.const_mul 3).div_const 2)).sub_const (E/2)).sub_const (2*δ)).sub (hG₂.div_const 2))
  have hpairR : Tendsto (fun n => (τ, Real.logb (N n) (R n))) atTop (nhds (τ, r)) :=
    tendsto_const_nhds.prodMk_nhds hr
  have hpairX : Tendsto (fun n => (τ, Real.logb (N n) (X n))) atTop (nhds (τ, x)) :=
    tendsto_const_nhds.prodMk_nhds hx
  have hBR : Tendsto (fun n => heathBrownDoubleZetaExponent τ (Real.logb (N n) (R n)))
      atTop (nhds (heathBrownDoubleZetaExponent τ r)) :=
    (bourgain_doubleZeta_exponent_continuous.tendsto (τ, r)).comp
      hpairR
  have hBX : Tendsto (fun n => heathBrownDoubleZetaExponent τ (Real.logb (N n) (X n)))
      atTop (nhds (heathBrownDoubleZetaExponent τ x)) :=
    (bourgain_doubleZeta_exponent_continuous.tendsto (τ, x)).comp
      hpairX
  have hright : Tendsto
      (fun n => Real.logb (N n) (3*K)+a+
        heathBrownDoubleZetaExponent τ (Real.logb (N n) (R n))/2+
        heathBrownDoubleZetaExponent τ (Real.logb (N n) (X n))/2)
      atTop (nhds (a+heathBrownDoubleZetaExponent τ r/2+heathBrownDoubleZetaExponent τ x/2)) := by
    simpa only [zero_add] using ((hK.add_const a).add (hBR.div_const 2)).add (hBX.div_const 2)
  exact le_of_tendsto_of_tendsto (hleft₁.max hleft₂) hright hcomp

end TaoTrudgianYang2025
