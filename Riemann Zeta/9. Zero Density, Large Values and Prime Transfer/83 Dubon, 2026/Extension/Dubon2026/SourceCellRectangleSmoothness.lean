import Dubon2026.SourceCellRectangleBranches
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! DUB-17/18 -> original Abel-Jacobi -> paired analytic cell dissection.
The literal rectangle radius, its side formulas and piecewise smoothness
supply the required six-arc rectangle. Adapted from anthropics/fermats-last-theorem,
Apache-2.0, commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.RectRadial
open Real
variable {a b c d : ℝ}

theorem contDiffOn_r4_arc1 (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    ContDiffOn ℝ 2 (rectRadial4 a b c d) (Set.Icc 0 (cornerAngle a c)) := by
  have hψ2 := cornerAngle_lt_pi_div_two a c
  refine ContDiffOn.congr (f := fun ψ => (Real.cos ψ / a)⁻¹) ?_
    (fun ψ hψ => collapse_arc1 ha hb hc hd hψ.1 hψ.2)
  exact ((Real.contDiff_cos.contDiffOn.div_const a).inv
    (fun ψ hψ => (div_pos (Real.cos_pos_of_mem_Ioo
      ⟨by linarith [hψ.1, Real.pi_pos], by linarith [hψ.2]⟩) ha).ne'))

theorem contDiffOn_r4_arc2 (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    ContDiffOn ℝ 2 (rectRadial4 a b c d)
      (Set.Icc (cornerAngle a c) (π - cornerAngle b c)) := by
  have hac0 := cornerAngle_pos ha hc
  have hbc0 := cornerAngle_pos hb hc
  refine ContDiffOn.congr (f := fun ψ => (Real.sin ψ / c)⁻¹) ?_
    (fun ψ hψ => collapse_arc2 ha hb hc hd hψ.1 hψ.2)
  exact ((Real.contDiff_sin.contDiffOn.div_const c).inv
    (fun ψ hψ => (div_pos (Real.sin_pos_of_pos_of_lt_pi
      (by linarith [hψ.1]) (by linarith [hψ.2])) hc).ne'))

theorem contDiffOn_r4_arc3 (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    ContDiffOn ℝ 2 (rectRadial4 a b c d)
      (Set.Icc (π - cornerAngle b c) (π + cornerAngle b d)) := by
  have hbc2 := cornerAngle_lt_pi_div_two b c
  have hbd2 := cornerAngle_lt_pi_div_two b d
  refine ContDiffOn.congr (f := fun ψ => (-Real.cos ψ / b)⁻¹) ?_
    (fun ψ hψ => collapse_arc3 ha hb hc hd hψ.1 hψ.2)
  refine ((Real.contDiff_cos.neg.contDiffOn.div_const b).inv (fun ψ hψ => ?_))
  have hneg : Real.cos ψ < 0 :=
    Real.cos_neg_of_pi_div_two_lt_of_lt (by linarith [hψ.1]) (by linarith [hψ.2])
  exact (div_pos (by linarith) hb).ne'

theorem contDiffOn_r4_arc4 (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    ContDiffOn ℝ 2 (rectRadial4 a b c d)
      (Set.Icc (π + cornerAngle b d) (2 * π - cornerAngle a d)) := by
  have hbd0 := cornerAngle_pos hb hd
  have had0 := cornerAngle_pos ha hd
  refine ContDiffOn.congr (f := fun ψ => (-Real.sin ψ / d)⁻¹) ?_
    (fun ψ hψ => collapse_arc4 ha hb hc hd hψ.1 hψ.2)
  refine ((Real.contDiff_sin.neg.contDiffOn.div_const d).inv (fun ψ hψ => ?_))
  have hneg : Real.sin ψ < 0 := by
    have h1 : Real.sin (ψ - π) > 0 :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hψ.1]) (by linarith [hψ.2])
    have h2 : Real.sin ψ = -Real.sin (ψ - π) := by
      rw [show ψ = (ψ - π) + π by ring, Real.sin_add_pi]
      ring_nf
    rw [h2]
    linarith
  exact (div_pos (by linarith) hd).ne'

theorem contDiffOn_r4_arc5 (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    ContDiffOn ℝ 2 (rectRadial4 a b c d)
      (Set.Icc (2 * π - cornerAngle a d) (2 * π)) := by
  have had2 := cornerAngle_lt_pi_div_two a d
  refine ContDiffOn.congr (f := fun ψ => (Real.cos ψ / a)⁻¹) ?_
    (fun ψ hψ => collapse_arc5 ha hb hc hd hψ.1 hψ.2)
  refine ((Real.contDiff_cos.contDiffOn.div_const a).inv (fun ψ hψ => ?_))
  have hpos : 0 < Real.cos ψ := by
    have h1 : Real.cos ψ = Real.cos (ψ - 2 * π) := by
      rw [show ψ = (ψ - 2 * π) + 2 * π by ring, Real.cos_add_two_pi]
      ring_nf
    rw [h1]
    exact Real.cos_pos_of_mem_Ioo
      ⟨by linarith [hψ.1], by linarith [hψ.2, Real.pi_pos]⟩
  exact (div_pos hpos ha).ne'


end Dubon2026.SourceFunctionField.CellGeometry.RectRadial
