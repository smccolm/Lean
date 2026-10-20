import Dubon2026.IntegralInducedDenominatorBound

/-! Finite freeness of the literal source integral induced coefficient module.
Uniform determinant denominators and actual numerator homogeneity place
the entire original induced module inside one finite polynomial stage.
Noetherian finiteness and the already proved original torsion freeness
then give finite freeness over the source characteristic-zero local PID.
No finite-generation, dimension, lattice, or basis hypothesis is supplied.
-/

namespace Dubon2026
noncomputable section

universe u
variable (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [IsLocalRing R] [CharZero R]

/-- The entire exact source induced module lies in one original polynomial stage whose denominator and degree bounds depend only on the original weight. -/
theorem integralLocalInduced_le_fixed_polynomial_stage {n : ℕ}
    (lam : Fin (n + 1) → ℤ) :
    generalLinearIntegralInducedSubmodule R (n + 1) lam ≤
      generalLinearRegularPolynomialStage R (n + 1)
        (-lam (0 : Fin (n + 1)).rev).toNat
        ((∑ i, lam i) + ((n + 1 : ℕ) : ℤ) *
          (-lam (0 : Fin (n + 1)).rev).toNat).toNat := by
  intro p hp
  obtain ⟨P, hP⟩ := integralInduced_exists_fixed_denominator R lam ⟨p, hp⟩
  apply Submodule.mem_map.mpr
  refine ⟨P, (MvPolynomial.mem_restrictTotalDegree _ _ _).mpr ?_, hP⟩
  apply integralLocal_induced_numerator_degree_le R lam
  rw [hP]
  exact hp

/-- The actual source integral Borel-induced module is finite over its original characteristic-zero local PID; finite generation is derived from the fixed original polynomial stage. -/
instance integralLocalInducedFinite {n : ℕ} (lam : Fin (n + 1) → ℤ) :
    Module.Finite R (generalLinearIntegralInducedSubmodule R (n + 1) lam) := by
  exact Module.Finite.of_injective
    (Submodule.inclusion (integralLocalInduced_le_fixed_polynomial_stage R lam))
    (Submodule.inclusion_injective _)

/-- The exact source induced module is free over the original local PID, using its proved finite generation and proved original torsion freeness. -/
instance integralLocalInducedFree {n : ℕ} (lam : Fin (n + 1) → ℤ) :
    Module.Free R (generalLinearIntegralInducedSubmodule R (n + 1) lam) := inferInstance

/-- Geraghty's literal integral induced coefficient module in every positive rank is finite free under the actual coefficient-ring assumptions, with no supplied finite-free representation or lattice certificate. -/
theorem integralLocalInduced_finite_free {n : ℕ} (lam : Fin (n + 1) → ℤ) :
    Module.Finite R (generalLinearIntegralInducedSubmodule R (n + 1) lam) ∧
      Module.Free R (generalLinearIntegralInducedSubmodule R (n + 1) lam) :=
  ⟨inferInstance, inferInstance⟩

end
end Dubon2026
