import Dubon2026.CompletedResidualCompactness
import Mathlib.Topology.Algebra.Nonarchimedean.TotallyDisconnected
import Mathlib.Topology.Instances.Matrix

/-! # Genuine profinite topology on matrices over the original residual completion -/

namespace Dubon2026

noncomputable section
open Matrix

variable {R ι : Type*} [CommRing R] [WithIdeal R] [T2Space R]
  [Fintype ι] [DecidableEq ι]

/-- The actual matrix unit group of a Hausdorff adic ring is totally disconnected. -/
theorem adicMatrixGroup_totallyDisconnected : TotallyDisconnectedSpace (GeneralLinearGroup ι R) := by
  letI : TotallyDisconnectedSpace R := inferInstance
  letI : TotallyDisconnectedSpace (Matrix ι ι R) :=
    inferInstanceAs (TotallyDisconnectedSpace (ι → ι → R))
  refine ⟨isTotallyDisconnected_of_image
    (Units.continuous_val (M := Matrix ι ι R)).continuousOn Units.val_injective ?_⟩
  exact isTotallyDisconnected_of_totallyDisconnectedSpace _

variable {G O : Type*} [Group G] [CommRing O] [IsLocalRing O]
  [Group.FG G] [IsNoetherianRing O] [Finite (IsLocalRing.ResidueField O)]

/-- Matrices over the genuine original residual completion form an actual compact unit group. -/
instance residualRepresentationMatrixCompact
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) :
    CompactSpace (GeneralLinearGroup ι (ResidualRepresentationCompletion ρ)) := by
  letI := residualRepresentationCompletion_compactSpace ρ
  letI : CompactSpace (Matrix ι ι (ResidualRepresentationCompletion ρ)) :=
    inferInstanceAs (CompactSpace (ι → ι → ResidualRepresentationCompletion ρ))
  infer_instance

/-- The actual matrix group over the original residual completion is totally disconnected in its inherited topology. -/
instance residualRepresentationMatrixTotallyDisconnected
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) :
    TotallyDisconnectedSpace (GeneralLinearGroup ι (ResidualRepresentationCompletion ρ)) :=
  adicMatrixGroup_totallyDisconnected (R := ResidualRepresentationCompletion ρ) (ι := ι)

end
end Dubon2026
