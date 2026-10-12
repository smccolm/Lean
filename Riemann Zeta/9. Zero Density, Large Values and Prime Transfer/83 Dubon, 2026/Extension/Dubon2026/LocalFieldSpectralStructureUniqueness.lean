import Dubon2026.LocalFieldValuativeExtensionUniqueness
import Dubon2026.SpectralValuationExtension

/-! # The canonical spectral structures equal the original local structures -/

namespace Dubon2026
noncomputable section

/-- A valuative relation determines its actual valuative topology. -/
theorem valuativeTopology_unique {L : Type*} [Field L] [ValuativeRel L]
    (t u : TopologicalSpace L)
    (ht : letI := t; IsValuativeTopology L) (hu : letI := u; IsValuativeTopology L) : t = u := by
  have heqt : t = (ValuativeRel.valuation L).subgroups_basis.topology := by
    letI := t
    haveI := ht
    exact Valuation.toTopologicalSpace_eq (ValuativeRel.valuation L)
  have hequ : u = (ValuativeRel.valuation L).subgroups_basis.topology := by
    letI := u
    haveI := hu
    exact Valuation.toTopologicalSpace_eq (ValuativeRel.valuation L)
  exact heqt.trans hequ.symm

/-- Separately constructed actual local structures extending the
same original base have equal valuations and equal topologies. -/
theorem localField_local_structures_unique
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (v w : ValuativeRel L) (t u : TopologicalSpace L)
    (hv : letI := v; letI := t; IsNonarchimedeanLocalField L)
    (hw : letI := w; letI := u; IsNonarchimedeanLocalField L)
    (hvext : letI := v;
      (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L))
    (hwext : letI := w;
      (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)) :
    v = w ∧ t = u := by
  have heq := localField_valuative_extension_unique K L v w t u hv hw hvext hwext
  subst w
  refine ⟨rfl, ?_⟩
  letI := v
  exact valuativeTopology_unique t u hv.toIsValuativeTopology hw.toIsValuativeTopology

/-- The spectral valuation and topology on the same original finite
local extension equal its supplied extending local structures. -/
theorem localField_local_structures_eq_spectral
    (K L : Type) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [ValuativeRel K] [(NormedField.valuation (K := K)).Compatible]
    [IsNonarchimedeanLocalField K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [v : ValuativeRel L] [t : TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)] :
    letI : NontriviallyNormedField L := spectralNorm.nontriviallyNormedField K L
    letI : TopologicalSpace L := (spectralNorm.uniformSpace K L).toTopologicalSpace
    letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
    letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
    v = ValuativeRel.ofValuation (NormedField.valuation (K := L)) ∧
      t = (spectralNorm.uniformSpace K L).toTopologicalSpace := by
  have hlocal : @IsNonarchimedeanLocalField L _ v t := inferInstance
  have hext := (inferInstance : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L))
  letI : NontriviallyNormedField L := spectralNorm.nontriviallyNormedField K L
  letI : TopologicalSpace L := (spectralNorm.uniformSpace K L).toTopologicalSpace
  letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
  letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel L := ValuativeRel.ofValuation (NormedField.valuation (K := L))
  haveI : IsNonarchimedeanLocalField L := spectralFiniteExtension_isNonarchimedeanLocalField K L
  haveI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L) :=
    spectralValuation_hasExtension K L
  exact localField_local_structures_unique K L v inferInstance t inferInstance
    hlocal inferInstance hext inferInstance

end
end Dubon2026
