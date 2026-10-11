import Dubon2026.LocalFieldResidueExtensionPolynomial
import Dubon2026.MonicResidueIrreducibleDVR
import Dubon2026.FiniteBasisAdicCompleteness
import Dubon2026.LocalFieldOriginalNorm
import Dubon2026.SpectralValuationExtension
import Dubon2026.FiniteResidueCompleteAlgebraSplitting
import Dubon2026.OriginalFractionScalarAlgebra
import Dubon2026.MonicRootFractionDegree
import Dubon2026.AdjoinRootFractionGeneration
import Dubon2026.LocalFieldMonicRootIntegerEquiv

/-! # Actual unramified Galois extensions of each positive local-field degree -/

namespace Dubon2026
noncomputable section

open Polynomial IsLocalRing
open scoped ValuativeRel

/-- Construct an actual unramified Galois extension of the original local
field of each positive degree. The field is the genuine fraction field of
the original integral root algebra. Its topology is the spectral topology;
its valuation restriction, original integer ring and Galois property are proved. -/
theorem localField_exists_unramified_galois_extension
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : ℕ) [NeZero n] :
    ∃ (L : Type) (_ : Field L) (_ : Algebra K L)
      (_ : ValuativeRel L) (_ : TopologicalSpace L)
      (_ : IsNonarchimedeanLocalField L)
      (_ : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)),
      FiniteDimensional K L ∧ IsGalois K L ∧
        Algebra.FormallyUnramified 𝒪[K] 𝒪[L] ∧ Module.finrank K L = n := by
  letI := IsTopologicalAddGroup.rightUniformSpace K
  haveI := isUniformAddGroup_of_addCommGroup (G := K)
  obtain ⟨f, hf, hfn, _, hfi, hfs, _⟩ :=
    localField_exists_integral_residue_extension_polynomial K n
  have hpos : 0 < f.natDegree := hfn.symm ▸ Nat.pos_of_ne_zero (NeZero.ne n)
  have hprime : Prime f := (Polynomial.Monic.irreducible_of_irreducible_map
    (residue 𝒪[K]) f hf hfi).prime
  let B := AdjoinRoot f
  haveI : IsDomain B := AdjoinRoot.isDomain_of_prime hprime
  haveI : IsLocalRing B := monic_residue_irreducible_adjoinRoot_local f hf hfi
  haveI : IsDiscreteValuationRing B := monic_residue_irreducible_adjoinRoot_dvr f hf hfi
  haveI : Module.Finite 𝒪[K] B := hf.finite_adjoinRoot
  have hinj : Function.Injective (algebraMap 𝒪[K] B) := by
    apply AdjoinRoot.of.injective_of_degree_ne_zero
    intro h
    exact (Nat.ne_of_gt hpos) (Polynomial.natDegree_eq_of_degree_eq_some h)
  haveI : FaithfulSMul 𝒪[K] B :=
    (faithfulSMul_iff_algebraMap_injective 𝒪[K] B).mpr hinj
  haveI : IsAdicComplete (maximalIdeal B) B := by
    have hcomplete := monic_adjoinRoot_isAdicComplete (maximalIdeal 𝒪[K]) f hf
    have hmax : (maximalIdeal 𝒪[K]).map (algebraMap 𝒪[K] B) = maximalIdeal B :=
      IsLocalRing.eq_maximalIdeal (monic_residue_irreducible_adjoinRoot_maximal f hfi)
    exact hmax ▸ hcomplete
  have hsplitB : (f.map (algebraMap 𝒪[K] B)).Splits :=
    finiteResidue_complete_algebra_polynomial_splits f hf hfi hfs (AdjoinRoot.root f)
      (by rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self])
  let L := FractionRing B
  letI : Algebra 𝒪[K] L := inferInstance
  haveI : IsScalarTower 𝒪[K] B L := inferInstance
  haveI : FaithfulSMul 𝒪[K] L := by
    apply (faithfulSMul_iff_algebraMap_injective 𝒪[K] L).mpr
    rw [IsScalarTower.algebraMap_eq 𝒪[K] B L]
    exact (IsFractionRing.injective B L).comp hinj
  letI : Algebra K L := originalFractionScalarAlgebra 𝒪[K] K L
  haveI : IsScalarTower 𝒪[K] K L := originalFractionScalarAlgebra_tower 𝒪[K] K L
  have hbase (x : 𝒪[K]) : algebraMap K L (x : K) =
      algebraMap B L (algebraMap 𝒪[K] B x) := by
    change algebraMap K L (algebraMap 𝒪[K] K x) = _
    rw [← IsScalarTower.algebraMap_apply 𝒪[K] K L,
      IsScalarTower.algebraMap_apply 𝒪[K] B L]
  obtain ⟨hdegree, hfinite⟩ := monicRootFraction_finrank_and_finite 𝒪[K] K L f hf hpos
  haveI : FiniteDimensional K L := hfinite
  have hsplitL : ((f.map (algebraMap 𝒪[K] K)).map (algebraMap K L)).Splits := by
    have h := hsplitB.map (algebraMap B L)
    rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq 𝒪[K] B L] at h
    rwa [Polynomial.map_map, ← IsScalarTower.algebraMap_eq 𝒪[K] K L]
  haveI : (f.map (algebraMap 𝒪[K] K)).IsSplittingField K L :=
    adjoinRootFraction_isSplittingField 𝒪[K] K L f hf hsplitL
  haveI : IsGalois K L := IsGalois.of_separable_splitting_field
    ((local_monic_separable_of_residue f hf hfs).map (f := algebraMap 𝒪[K] K))
  letI : NontriviallyNormedField K := localFieldOriginalNorm K
  haveI : IsUltrametricDist K := localFieldOriginalNorm_isUltrametric K
  haveI : CompleteSpace K := localFieldOriginalNorm_complete K
  haveI : (NormedField.valuation (K := K)).Compatible := localFieldOriginalNorm_compatible K
  letI : NontriviallyNormedField L := spectralNorm.nontriviallyNormedField K L
  letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
  letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel L := ValuativeRel.ofValuation (NormedField.valuation (K := L))
  haveI : IsNonarchimedeanLocalField L := spectralFiniteExtension_isNonarchimedeanLocalField K L
  haveI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L) :=
    spectralValuation_hasExtension K L
  haveI : Algebra.Etale 𝒪[K] 𝒪[L] := by
    letI : Algebra 𝒪[K] L := Algebra.ofSubring (ValuativeRel.valuation K).integer
    letI : SMul 𝒪[K] L := (inferInstance : Algebra 𝒪[K] L).toSMul
    haveI : IsScalarTower 𝒪[K] B L := IsScalarTower.of_algebraMap_eq hbase
    exact localFieldMonicRootInteger_etale K L f hf hfs
  exact ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, hdegree.trans hfn⟩

end
end Dubon2026
