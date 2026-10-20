import Dubon2026.IntegralInducedOrbitContinuity

/-! Joint continuity of the literal source integral induced action.
The proved finite basis expands a variable vector into finitely many
original orbit maps. This discharges the coefficient-action continuity
input on the automorphy route to Dubon's Theorem 2.6 (DUB-17--19).
-/

namespace Dubon2026
noncomputable section
open Matrix Topology

universe u

/-- A linear family on an actual finite basis acts jointly continuously once its original basis orbits are continuous. -/
theorem finiteBasis_linearFamily_continuous
    {R M X J : Type u} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsModuleTopology R M]
    [TopologicalSpace X] [Fintype J] (b : Module.Basis J R M)
    (rho : X → M →ₗ[R] M) (h : ∀ i, Continuous (fun x => rho x (b i))) :
    Continuous (fun p : X × M => rho p.1 p.2) := by
  letI : ContinuousAdd M := IsModuleTopology.toContinuousAdd R M
  have he (p : X × M) : rho p.1 p.2 = ∑ i, b.coord i p.2 • rho p.1 (b i) := by
    conv_lhs => rw [← b.sum_repr p.2]
    simp only [map_sum, map_smul, Module.Basis.coord_apply]
  simp_rw [he]
  apply continuous_finsetSum
  intro i _
  exact ((IsModuleTopology.continuous_of_linearMap (b.coord i)).comp continuous_snd).smul
    ((h i).comp continuous_fst)

/-- The actual original integral induced representation acts jointly continuously in its canonical finite-module topology. -/
theorem integralLocalInducedRepresentation_continuous
    (R E : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [IsLocalRing R] [CharZero R]
    [TopologicalSpace R] [CompactSpace R] [IsTopologicalRing R]
    [Field E] [Infinite E] [Algebra R E] [TopologicalSpace E] [IsTopologicalDivisionRing E]
    [ContinuousSMul R E] [T2Space E]
    {n : ℕ} (lam : Fin (n + 1) → ℤ)
    [TopologicalSpace (generalLinearIntegralInducedSubmodule R (n + 1) lam)]
    [IsModuleTopology R (generalLinearIntegralInducedSubmodule R (n + 1) lam)]
    (hRE : Function.Injective (algebraMap R E)) (hcont : Continuous (algebraMap R E)) :
    Continuous (fun p : GeneralLinearGroup (Fin (n + 1)) R ×
        generalLinearIntegralInducedSubmodule R (n + 1) lam =>
      generalLinearIntegralInducedRepresentation R (n + 1) lam p.1 p.2) := by
  apply finiteBasis_linearFamily_continuous
    (Module.Free.chooseBasis R (generalLinearIntegralInducedSubmodule R (n + 1) lam))
  intro i
  exact integralLocalInducedRepresentation_orbit_continuous R E lam hRE hcont _

end
end Dubon2026
