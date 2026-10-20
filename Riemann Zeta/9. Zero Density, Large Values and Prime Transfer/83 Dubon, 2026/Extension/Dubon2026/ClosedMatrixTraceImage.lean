import Dubon2026.ClosedMatrixTraceAlgebra
import Mathlib.RingTheory.Noetherian.Basic

/-! Images of the actual closed trace algebra under continuous coefficient
maps from compact rings. This identifies the CM trace algebra as a quotient
of the proved universal trace ring on DUB-17's polarized deformation route. -/

namespace Dubon2026
open Matrix
noncomputable section

variable {G ι O R A : Type*} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [CommRing R] [CommRing A] [Algebra O R] [Algebra O A]
  [TopologicalSpace R] [IsTopologicalRing R] [CompactSpace R]
  [TopologicalSpace A] [IsTopologicalRing A] [T2Space A]

/-- Continuous coefficient change from a compact ring maps its whole closed
trace algebra onto the whole closed trace algebra of the changed matrices. -/
theorem closedMatrixTraceAlgebra_map
    (ρ : G →* GeneralLinearGroup ι R) (f : R →ₐ[O] A) (hf : Continuous f) :
    (closedMatrixTraceAlgebra (O := O) ρ).map f =
      closedMatrixTraceAlgebra (O := O) ((GeneralLinearGroup.map f.toRingHom).comp ρ) := by
  unfold closedMatrixTraceAlgebra
  rw [← Subalgebra.topologicalClosure_map ⟨f, hf⟩ hf.isClosedMap]
  congr 1
  rw [AlgHom.map_adjoin]
  congr 1
  rw [← Set.range_comp]
  congr 1
  funext g
  exact AddMonoidHom.map_trace f.toAddMonoidHom (ρ g).val

/-- The actual specialized closed trace algebra is Noetherian when the
original compact trace algebra is Noetherian, by the proved surjective map. -/
theorem closedMatrixTraceAlgebra_isNoetherian_of_map
    (ρ : G →* GeneralLinearGroup ι R) (f : R →ₐ[O] A) (hf : Continuous f)
    [IsNoetherianRing (closedMatrixTraceAlgebra (O := O) ρ)] :
    IsNoetherianRing
      (closedMatrixTraceAlgebra (O := O) ((GeneralLinearGroup.map f.toRingHom).comp ρ)) := by
  let T := closedMatrixTraceAlgebra (O := O) ρ
  let U := closedMatrixTraceAlgebra (O := O) ((GeneralLinearGroup.map f.toRingHom).comp ρ)
  have he : T.map f = U := closedMatrixTraceAlgebra_map ρ f hf
  let g : T →ₐ[O] U := (f.comp T.val).codRestrict U (fun x => by
    change f x.val ∈ U
    rw [← he]
    exact ⟨x.val, x.property, rfl⟩)
  apply isNoetherianRing_of_surjective _ _ g.toRingHom
  intro y
  have hy : y.val ∈ T.map f := he.symm ▸ y.property
  obtain ⟨x, hx, hxy⟩ := hy
  exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩

end
end Dubon2026
