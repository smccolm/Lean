import Dubon2026.SourceInverseJLimits
import Dubon2026.SourceMonicRelationRootBound

/-! DUB-17/18 -> regular-differential cusp decay -> bounded analytic
inverse-j integral expression. Finitely many actual polynomial coefficients
are uniformly bounded because inverse j tends to zero.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open UpperHalfPlane Filter Polynomial
open scoped Topology BigOperators

theorem exists_inverse_j_polynomial_bound (n : ℕ) (c : ℕ → ℂ[X]) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ τ : ℍ in atImInfty,
      ∀ i ∈ Finset.range n, ‖(c i).eval ((JMultiplicity.jf τ)⁻¹)‖ ≤ B := by
  let B : ℝ := ∑ i ∈ Finset.range n, (‖(c i).eval 0‖ + 1)
  have hB : 0 ≤ B := Finset.sum_nonneg fun i _ => by positivity
  refine ⟨B, hB, (Finset.eventually_all _).mpr ?_⟩
  intro i hi
  have ht := (((c i).continuous.tendsto 0).comp
    JMultiplicity.tendsto_inverse_j_atImInfty).norm
  filter_upwards [ht.eventually_lt_const (lt_add_one ‖(c i).eval 0‖)] with τ hτ
  apply hτ.le.trans
  dsimp only [B]
  exact Finset.single_le_sum (f := fun j : ℕ => ‖(c j).eval (0 : ℂ)‖ + (1 : ℝ))
    (s := Finset.range n) (fun j _ => by positivity) hi

end
end Dubon2026.SourceFunctionField
