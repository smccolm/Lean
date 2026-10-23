import Dubon2026.SourceLatticeFractionCoordinates
import Dubon2026.SourceStableLatticeGaloisCoordinates

/-! DUB-17/18 -> original residual association -> preserve the rational
representation under integral coordinates. The basis of the actual
lattice extends to a basis of the original field space. Its integral
matrices have exactly the original action after coefficient inclusion. -/
namespace Dubon2026
noncomputable section
open Matrix
variable {S E G : Type*} [CommRing S] [Field E] [Algebra S E] [IsFractionRing S E]
variable [Group G] (ρ : G →* GeneralLinearGroup (Fin 2) E)
variable (L : Submodule S (Fin 2 → E)) [Submodule.IsLattice E L]
variable (hL : ∀ g x, x ∈ L → (ρ g).val *ᵥ x ∈ L) (b : Module.Basis (Fin 2) S L)

theorem stableLatticeGeneralLinearRep_field_entry (g : G) (i j : Fin 2) :
    algebraMap S E ((stableLatticeGeneralLinearRep ρ L hL b g).val i j) =
      (b.extendOfIsLattice E).repr ((ρ g).val *ᵥ (b.extendOfIsLattice E j)) i := by
  rw [stableLatticeGeneralLinearRep_entry, ← latticeBasis_fraction_repr,
    stableLatticeGaloisRep_coe, Module.Basis.extendOfIsLattice_apply]

theorem stableLatticeGeneralLinearRep_field_matrix (g : G) :
    (stableLatticeGeneralLinearRep ρ L hL b g).val.map (algebraMap S E) =
      LinearMap.toMatrix (b.extendOfIsLattice E) (b.extendOfIsLattice E)
        (Matrix.mulVecLin (ρ g).val) := by
  ext i j
  exact (stableLatticeGeneralLinearRep_field_entry ρ L hL b g i j).trans
    (LinearMap.toMatrix_apply (b.extendOfIsLattice E) (b.extendOfIsLattice E)
      (Matrix.mulVecLin (ρ g).val) i j).symm

theorem stableLatticeGeneralLinearRep_field_action (g : G) (v : Fin 2 → E) :
    (stableLatticeGeneralLinearRep ρ L hL b g).val.map (algebraMap S E) *ᵥ
        (b.extendOfIsLattice E).repr v =
      (b.extendOfIsLattice E).repr ((ρ g).val *ᵥ v) := by
  rw [stableLatticeGeneralLinearRep_field_matrix]
  exact LinearMap.toMatrix_mulVec_repr _ _ _ v

end
end Dubon2026
