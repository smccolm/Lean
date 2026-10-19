import Dubon2026.FinitePrimaryGroupAlgebraLocal
import Dubon2026.CompactSeparatedLocalAdicTopology
import Dubon2026.Reuse.Imperial.Patching.Utils.AdicTopology
import Mathlib.Topology.Algebra.Module.ModuleTopology

/-! The literal finite auxiliary group algebra is a complete compact
local coefficient ring in its finite-module topology. This allows the
common power-series action needed for the arithmetic annihilator ideals,
without replacing the group algebra by a separate completion. -/

namespace Dubon2026
noncomputable section
open IsLocalRing

/-- Derive the full local coefficient topology and completeness of
the actual finite primary group algebra from the compact coefficient
ring. Finite-module topology is transported by its original group basis. -/
theorem finitePrimaryGroupAlgebra_completeData
    (O D : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O] [T2Space O]
    [CommGroup D] [Finite D] (q : ℕ) (hq : q.Prime)
    [CharP (ResidueField O) q] (hD : IsPGroup q D) :
    letI : TopologicalSpace (MonoidAlgebra O D) := moduleTopology O (MonoidAlgebra O D)
    letI : Module.Finite O (MonoidAlgebra O D) := Module.Finite.of_basis (MonoidAlgebra.basis D O)
    letI := IsModuleTopology.isTopologicalRing O (MonoidAlgebra O D)
    letI := finitePrimaryGroupAlgebra_isLocal O D q hq hD
    IsNoetherianRing (MonoidAlgebra O D) ∧ IsTopologicalRing (MonoidAlgebra O D) ∧
      CompactSpace (MonoidAlgebra O D) ∧ T2Space (MonoidAlgebra O D) ∧
      IsAdicTopology (MonoidAlgebra O D) ∧
      IsAdicComplete (maximalIdeal (MonoidAlgebra O D)) (MonoidAlgebra O D) := by
  letI : TopologicalSpace (MonoidAlgebra O D) := moduleTopology O (MonoidAlgebra O D)
  letI := finitePrimaryGroupAlgebra_isLocal O D q hq hD
  letI : Module.Finite O (MonoidAlgebra O D) := Module.Finite.of_basis (MonoidAlgebra.basis D O)
  letI : IsNoetherianRing (MonoidAlgebra O D) := IsNoetherianRing.of_finite O _
  letI := IsModuleTopology.isTopologicalRing O (MonoidAlgebra O D)
  let e := (MonoidAlgebra.basis D O).equivFun
  let h : MonoidAlgebra O D ≃ₜ (D → O) :=
    { toEquiv := e.toEquiv
      continuous_toFun := IsModuleTopology.continuous_of_linearMap e.toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap }
  letI := h.symm.compactSpace
  letI := h.symm.t2Space
  letI : IsAdicTopology (MonoidAlgebra O D) := ⟨compactSeparatedLocalRing_isAdic⟩
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, {}⟩

end
end Dubon2026
