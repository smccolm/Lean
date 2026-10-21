import Dubon2026.SourceCurveResidueAlgebraic
import Dubon2026.SourceCurvePlaceCenters

/-! DUB-17/18 -> matching cusp-form dimension -> numerical modular genus
and analytic regularity. To compute the canonical j-divisor, every nonpole
place must lie over one unique finite coordinate value. Actual residue-field
rationality supplies that value; transcendence excludes equality with any
base-field scalar. This is the needed finite-value step, selected from the exists_value
argument in S_ModularCurve_isIntegral_and_isIntegral_of_smul_D_mem_regularDifferentialsBar,
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2.
-/
namespace Dubon2026.SourceCurve.Place
noncomputable section
open IsLocalRing
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem transcendental_sub_algebraMap_ne_zero {f : F} (ht : Transcendental K f) (c : K) :
    f - algebraMap K F c ≠ 0 := by
  intro h
  apply ht
  rw [sub_eq_zero.mp h]
  exact isAlgebraic_algebraMap (R := K) (A := F) c

theorem ord_sub_algebraMap_pos_iff_residue_eq (v : Place K F)
    {f : F} (ht : Transcendental K f) (hf : f ∈ v.toValuationSubring) (c : K) :
    0 < v.ord (f - algebraMap K F c) ↔
      residue v.toValuationSubring ⟨f, hf⟩ = algebraMap K v.ResidueField c := by
  let g : v.toValuationSubring := ⟨f, hf⟩ - algebraMap K v.toValuationSubring c
  have hg : (g : F) = f - algebraMap K F c := by
    change f - ((algebraMap K v.toValuationSubring c) : F) = _
    rw [v.coe_algebraMap]
  have hg0 : (g : F) ≠ 0 := hg ▸ transcendental_sub_algebraMap_ne_zero ht c
  calc
    _ ↔ g ∈ maximalIdeal v.toValuationSubring := by
      rw [v.mem_maximalIdeal_iff_ord_pos hg0 g.2, hg]
    _ ↔ residue v.toValuationSubring g = 0 := (residue_eq_zero_iff g).symm
    _ ↔ _ := by
      change residue v.toValuationSubring
        (⟨f, hf⟩ - algebraMap K v.toValuationSubring c) = 0 ↔ _
      rw [map_sub, show residue v.toValuationSubring (algebraMap K v.toValuationSubring c) =
        algebraMap K v.ResidueField c from
          (IsScalarTower.algebraMap_apply K v.toValuationSubring v.ResidueField c).symm,
        sub_eq_zero]

theorem exists_unique_coordinate_value (v : Place K F)
    (hres : Function.Surjective (algebraMap K v.ResidueField))
    {f : F} (ht : Transcendental K f) (hf : f ∈ v.toValuationSubring) :
    ∃! c : K, 0 < v.ord (f - algebraMap K F c) := by
  obtain ⟨c, hc⟩ := hres (residue v.toValuationSubring ⟨f, hf⟩)
  refine ⟨c, (v.ord_sub_algebraMap_pos_iff_residue_eq ht hf c).mpr hc.symm, ?_⟩
  intro d hd
  apply (algebraMap K v.ResidueField).injective
  exact ((v.ord_sub_algebraMap_pos_iff_residue_eq ht hf d).mp hd).symm.trans hc.symm

end
end Dubon2026.SourceCurve.Place
