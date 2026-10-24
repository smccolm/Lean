import Dubon2026.SourceCurveDecompositionFixedField
import Dubon2026.SourceCurveDecompositionCardinality
import Dubon2026.SourceCurveResidueRestrictionConstants

/-! The actual decomposition fixed field has orders divisible by the
decomposition group cardinality. The full Galois group fixes the place,
so the existing cardinality theorem computes the ramification index;
the existing restriction-order formula gives divisibility. Rational lower
residues are derived from the upper place, avoiding new coordinate towers.
This removes the fixed-field order-gap input of the DUB-17/18 wild estimate. -/
namespace Dubon2026.SourceCurve.Place
noncomputable section
open IntermediateField
variable {K F M : Type*} [Field K] [IsAlgClosed K] [Field F] [Field M]
variable [Algebra K F] [Algebra K M] [Algebra F M] [IsScalarTower K F M]
variable [FiniteDimensional F M] (v : Place K M)

theorem decomposition_fixedField_order_dvd
    (htop : Function.Bijective (algebraMap K v.ResidueField))
    {z : M} (hz : z ∈ fixedField (v.decompositionConstantAction (F := F)).range) :
    (Nat.card (v.toValuationSubring.decompositionSubgroup F) : ℤ) ∣ v.ord z := by
  let I := v.toValuationSubring.decompositionSubgroup F
  let Z := fixedField I
  letI : IsScalarTower K Z M := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsGalois Z M := inferInstanceAs (IsGalois (FixedPoints.subfield I M) M)
  have hbase : Function.Bijective (algebraMap K (v.restrict Z).ResidueField) :=
    ⟨(algebraMap K (v.restrict Z).ResidueField).injective,
      v.residue_algebraMap_surjective_restrict (F := Z) htop.surjective⟩
  have hc := decomposition_card_eq_uniformizer_order (F := Z) v hbase htop
  have hcard : Nat.card (v.toValuationSubring.decompositionSubgroup Z) = Nat.card I := by
    rw [v.decomposition_over_fixedField_eq_top,
      Nat.card_congr (Subgroup.topEquiv : (⊤ : Subgroup (M ≃ₐ[Z] M)) ≃* (M ≃ₐ[Z] M)).toEquiv,
      IsGalois.card_aut_eq_finrank]
    exact finrank_fixedField_eq_card I
  have hord : v.ord (algebraMap Z M (v.restrict Z).uniformizer) = (Nat.card I : ℤ) := by
    have h := congrArg (fun n : ℕ => (n : ℤ)) (hcard.symm.trans hc)
    dsimp only at h
    rw [Int.toNat_of_nonneg (v.ord_restricted_uniformizer_pos (F := Z)).le] at h
    exact h.symm
  have hzZ : z ∈ Z := by
    rw [← v.decomposition_fixedField_restrictScalars] at hz
    exact hz
  have ho := v.ord_algebraMap_restrict (F := Z) (⟨z, hzZ⟩ : Z)
  rw [hord] at ho
  refine ⟨(v.restrict Z).ord (⟨z, hzZ⟩ : Z), ?_⟩
  exact ho.trans (mul_comm _ _)

end
end Dubon2026.SourceCurve.Place
