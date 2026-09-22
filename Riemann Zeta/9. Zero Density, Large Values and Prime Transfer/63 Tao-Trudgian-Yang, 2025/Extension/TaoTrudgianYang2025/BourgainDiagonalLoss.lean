import TaoTrudgianYang2025.BourgainLinkedLogarithm
import TaoTrudgianYang2025.BourgainRegionRealization

/-!
# Removing the finite comparison losses along a diagonal sequence

The analytic comparison remains an explicit premise of the scalar lemma.
The source-family construction applies it to the actual selected objects.
-/

noncomputable section

namespace TaoTrudgianYang2025

/-- A finite collection of varying factors can be absorbed at one scale. -/
theorem bourgain_abs_logb_le_of_sum_threshold {m : ℕ}
    (A : Fin m → ℝ) {N ε : ℝ} (hN : 1 < N) (hε : 0 < ε)
    (hscale : (∑ i, Real.exp (|Real.log (A i)|/ε+1)) ≤ N) (i : Fin m) :
    |Real.logb N (A i)| ≤ ε := by
  apply bourgain_abs_logb_le_of_threshold hN hε
  exact (Finset.single_le_sum (fun j _ => (Real.exp_pos (|Real.log (A j)|/ε+1)).le)
    (Finset.mem_univ i)).trans hscale

/-- With every accuracy at most epsilon, both comparison losses are bounded
by one explicit vanishing power loss. All three double-zeta terms survive. -/
theorem bourgain_diagonal_comparison {σ τ α χ ε δ r x g g₂ k : ℝ}
    (hlocal : 0 ≤ τ-χ) (hε : 0 < ε) (hε₁ : ε ≤ 1)
    (hδ : 0 ≤ δ) (hδε : δ ≤ ε)
    (hg : g ≤ ε) (hg₂ : g₂ ≤ ε) (hk : k ≤ ε)
    (hcomp :
      max (-2*α+2*σ+x+r-bourgainComparisonLoss (τ-χ) ε δ ε-2*δ-g)
        (-α-χ/2+2*σ+x/2+3*r/2-bourgainComparisonLoss (τ-χ) ε δ ε/2-2*δ-g₂/2) ≤
      k+(2*ε+(τ+δ)*ε)+heathBrownDoubleZetaExponent (τ+δ) r/2+
        heathBrownDoubleZetaExponent (τ+δ) x/2) :
    max (-2*α+2*σ+x+r) (-α-χ/2+2*σ+x/2+3*r/2) ≤
      (2*τ-χ+12)*ε+heathBrownDoubleZetaExponent τ r/2+
        heathBrownDoubleZetaExponent τ x/2 := by
  have hδ₁ : δ ≤ 1 := hδε.trans hε₁
  have hprod : δ*ε ≤ ε := by nlinarith
  have hEpos : 0 ≤ bourgainComparisonLoss (τ-χ) ε δ ε := by
    unfold bourgainComparisonLoss
    positivity
  have hE : bourgainComparisonLoss (τ-χ) ε δ ε ≤ (τ-χ+4)*ε := by
    unfold bourgainComparisonLoss
    nlinarith
  have hr := bourgain_doubleZeta_height_slack (τ := τ) (r := r) hδ
  have hx := bourgain_doubleZeta_height_slack (τ := τ) (r := x) hδ
  have h₁ := (le_max_left _ _).trans hcomp
  have h₂ := (le_max_right _ _).trans hcomp
  apply max_le <;> nlinarith

end TaoTrudgianYang2025
