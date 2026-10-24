import Dubon2026.SourceCurveOrderFiltration

/-! The residue constant needed in the fixed-field derivative estimate.
This uses the actual valuation-ring residue map and its existing
maximal-ideal/order characterization. It is the constant-subtraction step
in the FLT wild different argument (Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2), on the DUB-17/18 wild genus chain. -/
namespace Dubon2026.SourceCurve.Place
noncomputable section
variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

theorem exists_constant_of_ordGe_zero
    (hres : Function.Surjective (algebraMap K v.ResidueField))
    {z : F} (hz : v.OrdGe 0 z) :
    ∃ c : K, v.OrdGe 1 (z - algebraMap K F c) := by
  let z' : v.toValuationSubring := ⟨z, hz.mem_of_zero⟩
  obtain ⟨c, hc⟩ := hres (IsLocalRing.residue _ z')
  refine ⟨c, ?_⟩
  have he : IsLocalRing.residue _ (z' - algebraMap K v.toValuationSubring c) = 0 := by
    rw [map_sub]
    change IsLocalRing.residue _ z' - algebraMap K v.ResidueField c = 0
    exact sub_eq_zero.mpr hc.symm
  have hmem := (IsLocalRing.residue_eq_zero_iff _).mp he
  have hval : ((z' - algebraMap K v.toValuationSubring c : v.toValuationSubring) : F) =
      z - algebraMap K F c := by
    change z - ((algebraMap K v.toValuationSubring c : v.toValuationSubring) : F) = _
    rw [coe_algebraMap]
  have h := (v.mk_mem_maximalIdeal_iff
    (z' - algebraMap K v.toValuationSubring c).2).mp hmem
  rw [hval] at h
  exact h.imp_right (by omega)

end
end Dubon2026.SourceCurve.Place
