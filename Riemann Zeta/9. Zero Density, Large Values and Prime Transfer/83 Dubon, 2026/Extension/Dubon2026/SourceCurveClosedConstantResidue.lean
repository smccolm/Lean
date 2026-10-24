import Dubon2026.SourceCurveFiniteCoordinateResidues
import Dubon2026.SourceCurveCoordinateValues
import Mathlib.RingTheory.Valuation.RamificationGroup

/-! Identify the actual residue field with the algebraically closed base
field and prove that a place's decomposition group is inertia.
Native valuation-ring inertia and the existing finite-coordinate residue
rationality discharge the constant-field assumptions for DUB-17/18
finite Galois specialization and its exceptional-fiber census. -/
namespace Dubon2026.SourceCurve.Place
open IsLocalRing IntermediateField
noncomputable section
variable {K M : Type*} [Field K] [IsAlgClosed K] [Field M] [Algebra K M]
variable (t : M) [FiniteDimensional K⟮t⟯ M] (v : Place K M)

/-- The inverse of the actual constant-field embedding into the residue field. -/
def residueConstantEquiv : v.ResidueField ≃ₐ[K] K :=
  (AlgEquiv.ofBijective (Algebra.ofId K v.ResidueField)
    (place_residue_bijective_of_finite_coordinate t v)).symm

theorem residueConstantEquiv_algebraMap (c : K) :
    residueConstantEquiv t v (algebraMap K v.ResidueField c) = c := by
  exact (residueConstantEquiv t v).commutes c

/-- Evaluation in the constant field through the actual valuation-ring residue map. -/
def residueConstantMap : v.toValuationSubring →+* K :=
  (residueConstantEquiv t v).toRingHom.comp (residue v.toValuationSubring)

theorem residueConstantMap_algebraMap (c : K) :
    residueConstantMap t v (algebraMap K v.toValuationSubring c) = c := by
  change residueConstantEquiv t v
    (residue v.toValuationSubring (algebraMap K v.toValuationSubring c)) = c
  rw [show residue v.toValuationSubring (algebraMap K v.toValuationSubring c) =
    algebraMap K v.ResidueField c from
      (IsScalarTower.algebraMap_apply K v.toValuationSubring v.ResidueField c).symm]
  exact residueConstantEquiv_algebraMap t v c

theorem residueConstantMap_coordinate (ht : Transcendental K t)
    (htv : t ∈ v.toValuationSubring) (a : K)
    (ha : 0 < v.ord (t - algebraMap K M a)) :
    residueConstantMap t v ⟨t, htv⟩ = a := by
  change residueConstantEquiv t v (residue v.toValuationSubring ⟨t, htv⟩) = a
  rw [(v.ord_sub_algebraMap_pos_iff_residue_eq ht htv a).mp ha]
  exact residueConstantEquiv_algebraMap t v a

include t in
theorem mem_inertia_of_decomposition_of_finite_coordinate
    {F : Type*} [Field F] [Algebra K F] [Algebra F M] [IsScalarTower K F M]
    {σ : M ≃ₐ[F] M} (hσ : σ ∈ v.toValuationSubring.decompositionSubgroup F) :
    (⟨σ, hσ⟩ : v.toValuationSubring.decompositionSubgroup F) ∈
      v.toValuationSubring.inertiaSubgroup F := by
  rw [ValuationSubring.inertiaSubgroup, MonoidHom.mem_ker]
  apply RingEquiv.ext
  intro r
  show (⟨σ, hσ⟩ : v.toValuationSubring.decompositionSubgroup F) • r = r
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective r
  obtain ⟨c, hc⟩ := (place_residue_bijective_of_finite_coordinate t v).2 (residue _ a)
  have hc' : residue _ a = residue _ (algebraMap K v.toValuationSubring c) := hc.symm
  rw [hc', ← IsLocalRing.ResidueField.residue_smul]
  congr 1
  apply Subtype.ext
  show σ (algebraMap K M c) = algebraMap K M c
  rw [IsScalarTower.algebraMap_apply K F M, σ.commutes]

end
end Dubon2026.SourceCurve.Place
