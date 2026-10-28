import Dubon2026.SourceModularSidePairingAction
/-! DUB-17/18 -> original all-weight arithmetic association -> Gamma1 Picard/H1
-> Abel-Jacobi converse -> reciprocity -> winding-period identity.
Boundary reindexing at the literal coset representatives, using native slash
actions. Adapted from pinned Apache-2.0 anthropics source. These equalities do
not supply the later Green identity or edge integrability. -/
namespace Dubon2026.SourceModularSidePairing
noncomputable section
open UpperHalfPlane Complex MeasureTheory
open scoped MatrixGroups ModularForm
variable {Γ : Subgroup SL(2, ℤ)}

theorem sum_integral_rightRay [Fintype (SL(2, ℤ) ⧸ Γ)] (φ : ℍ → ℂ) {s : Set ℝ}
    (hs : MeasurableSet s) (hs0 : s ⊆ Set.Ioi 0) :
    ∑ q : SL(2, ℤ) ⧸ Γ, ∫ y in s, tilePull φ (Quotient.out q)⁻¹ (1 / 2 + y * Complex.I) =
      ∑ q : SL(2, ℤ) ⧸ Γ, ∫ y in s,
        tilePull ((φ ∣[(2 : ℤ)] pairElt Γ ModularGroup.T q)) (Quotient.out q)⁻¹ (-(1 / 2) + y * Complex.I) := by
  rw [← sum_comp_smul ModularGroup.T]
  refine Finset.sum_congr rfl fun q _ => setIntegral_congr_fun hs fun y hy => ?_
  exact tilePull_T_pt φ q (hs0 hy)

theorem sum_integral_arc [Fintype (SL(2, ℤ) ⧸ Γ)] (φ : ℍ → ℂ) :
    ∑ q : SL(2, ℤ) ⧸ Γ, ∫ θ in (Real.pi / 3)..(2 * Real.pi / 3),
        tilePull φ (Quotient.out q)⁻¹ (Complex.exp (θ * Complex.I)) *
          (Complex.I * Complex.exp (θ * Complex.I)) =
      -∑ q : SL(2, ℤ) ⧸ Γ, ∫ θ in (Real.pi / 3)..(2 * Real.pi / 3),
        tilePull ((φ ∣[(2 : ℤ)] pairElt Γ ModularGroup.S q)) (Quotient.out q)⁻¹ (Complex.exp (θ * Complex.I)) *
          (Complex.I * Complex.exp (θ * Complex.I)) := by
  rw [← sum_comp_smul ModularGroup.S, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun q _ => ?_

  have hrefl := intervalIntegral.integral_comp_sub_left
    (fun θ : ℝ => tilePull φ (Quotient.out (ModularGroup.S • q))⁻¹ (Complex.exp (θ * Complex.I)) *
      (Complex.I * Complex.exp (θ * Complex.I)))
    (a := Real.pi / 3) (b := 2 * Real.pi / 3) Real.pi
  have e1 : Real.pi - 2 * Real.pi / 3 = Real.pi / 3 := by ring
  have e2 : Real.pi - Real.pi / 3 = 2 * Real.pi / 3 := by ring
  rw [e1, e2] at hrefl
  rw [← hrefl, ← intervalIntegral.integral_neg]
  refine intervalIntegral.integral_congr fun θ hθ => ?_
  have hpi := Real.pi_pos
  rw [Set.uIcc_of_le (by linarith)] at hθ
  have h1 : 0 < θ := by linarith [hθ.1]
  have h2 : θ < Real.pi := by linarith [hθ.2]
  rw [tilePull_S_pt φ q h1 h2]
  push_cast
  rw [sub_mul, Complex.exp_sub, Complex.exp_pi_mul_I]
  have hne : Complex.exp (θ * Complex.I) ≠ 0 := Complex.exp_ne_zero _
  field_simp

end
end Dubon2026.SourceModularSidePairing
