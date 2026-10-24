import Dubon2026.SourceEllipticVeluAffineEvaluation
import Mathlib.Analysis.Analytic.Constructions

/-! Analyticity of the literal finite Velu coordinate formulas away from the
actual kernel denominator. These are the same formulas already proved for
the actual odd point norm. They supply the single affine germ needed for
complex scalar compatibility and the DUB-17/18 odd-prime product identity. -/

namespace Dubon2026.SourceEllipticFunctionField
open WeierstrassCurve
open SourceEllipticVelu SourceEllipticVelu.OddDiscriminant.Algebra

theorem analyticAt_veluAffineX (W : WeierstrassCurve ℂ) (S : Finset (ℂ × ℂ))
    {f : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z)
    (hd : (hP S Prod.fst).eval (f z) ≠ 0) :
    AnalyticAt ℂ (fun u => veluAffineX W S (f u)) z := by
  have hn : ∀ P ∈ S, f z - P.1 ≠ 0 := by
    rw [hP_eval, Finset.prod_ne_zero_iff] at hd
    exact hd
  unfold veluAffineX Xv
  apply hf.add
  apply Finset.analyticAt_fun_sum
  intro P hP
  exact (analyticAt_const.div (hf.sub analyticAt_const) (hn P hP)).add
    (analyticAt_const.div ((hf.sub analyticAt_const).pow 2) (pow_ne_zero 2 (hn P hP)))

theorem analyticAt_veluAffineY (W : WeierstrassCurve ℂ) (S : Finset (ℂ × ℂ))
    {f g : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z) (hg : AnalyticAt ℂ g z)
    (hd : (hP S Prod.fst).eval (f z) ≠ 0) :
    AnalyticAt ℂ (fun u => veluAffineY W S (f u) (g u)) z := by
  have hn : ∀ P ∈ S, f z - P.1 ≠ 0 := by
    rw [hP_eval, Finset.prod_ne_zero_iff] at hd
    exact hd
  unfold veluAffineY
  apply hg.sub
  apply Finset.analyticAt_fun_sum
  intro P hP
  have hden := hf.sub (analyticAt_const (v := P.1))
  have hnum1 : AnalyticAt ℂ (fun u =>
      veluU W P.1 P.2 * (2 * g u + W.a₁ * f u + W.a₃)) z := by fun_prop
  have hnum2 : AnalyticAt ℂ (fun u =>
      veluT W P.1 P.2 * (W.a₁ * (f u - P.1) + g u - P.2)) z := by fun_prop
  exact ((hnum1.div (hden.pow 3) (pow_ne_zero 3 (hn P hP))).add
    (hnum2.div (hden.pow 2) (pow_ne_zero 2 (hn P hP)))).add
    (analyticAt_const.div (hden.pow 2) (pow_ne_zero 2 (hn P hP)))

end Dubon2026.SourceEllipticFunctionField
