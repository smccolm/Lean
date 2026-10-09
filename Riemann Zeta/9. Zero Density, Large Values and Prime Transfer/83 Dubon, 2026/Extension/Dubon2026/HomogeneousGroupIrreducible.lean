import Dubon2026.HomogeneousIrreducible
import Dubon2026.HomogeneousTwistDerivative
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! # Irreducibility of the original determinant-twisted GL₂ representation -/

namespace Dubon2026

noncomputable section
open MvPolynomial Filter

/-- Actual group invariance in the original finite-dimensional space implies invariance under its genuine norm-derived traceless action. -/
theorem homogeneousDeterminantTwist_invariant_lie (m : ℕ)
    (p : Submodule ℂ (homogeneousSubmodule (Fin 2) ℂ (2 * m)))
    (hi : ∀ g v, v ∈ p → homogeneousDeterminantTwist (2 * m) (-(m : ℤ)) g v ∈ p)
    (a : ComplexSl2) (v : homogeneousSubmodule (Fin 2) ℂ (2 * m)) (hv : v ∈ p) :
    homogeneousSl2Action (2 * m) a v ∈ p := by
  have hd := homogeneousNormalizedTwist_hasDerivAt m a.val v
  rw [complexTracelessProjection_sl] at hd
  apply p.closed_of_finiteDimensional.mem_of_tendsto hd.tendsto_slope_zero
  exact Eventually.of_forall (fun t => p.smul_mem t⁻¹ (p.sub_mem (hi _ v hv) (hi _ v hv)))

/-- The genuine original determinant-twisted GL₂ representation has no proper nonzero invariant complex subspace. -/
theorem homogeneousDeterminantTwist_irreducible (m : ℕ)
    (p : Submodule ℂ (homogeneousSubmodule (Fin 2) ℂ (2 * m)))
    (hi : ∀ g v, v ∈ p → homogeneousDeterminantTwist (2 * m) (-(m : ℤ)) g v ∈ p) :
    p = ⊥ ∨ p = ⊤ := by
  by_cases hp : p = ⊥
  · exact Or.inl hp
  · exact Or.inr (homogeneousSl2_submodule_eq_top (2 * m) p hp
      (homogeneousDeterminantTwist_invariant_lie m p hi compactSl2H)
      (homogeneousDeterminantTwist_invariant_lie m p hi compactSl2E)
      (homogeneousDeterminantTwist_invariant_lie m p hi compactSl2F))

end
end Dubon2026
