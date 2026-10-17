import Dubon2026.OriginalRelationExtensionObstruction

/-! # Original prime-annihilated coefficients give prime-annihilated H1

The quotient-functional extension in DUB-17's relation dévissage uses
the actual first cohomology of the induced quotient. Its prime
annihilation follows from the literal cochains and cocycle projection.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory

/-- The same prime annihilating every original coefficient annihilates
its actual first cohomology. No torsion certificate on H1 is supplied. -/
theorem originalPrimeCoefficient_first_annihilated
    {G : Type} [Group G] (B : Rep.{0} ℤ G) (p : ℕ)
    (hB : ∀ b : B, p • b = 0) (x : groupCohomology B 1) : p • x = 0 := by
  refine groupCohomology_induction_on x (fun c => ?_)
  rw [← map_nsmul]
  have hc : p • c = 0 := by
    apply (ModuleCat.mono_iff_injective (groupCohomology.iCocycles B 1)).mp inferInstance
    rw [map_nsmul, map_zero]
    funext g
    exact hB _
  rw [hc, map_zero]

end
end Dubon2026
