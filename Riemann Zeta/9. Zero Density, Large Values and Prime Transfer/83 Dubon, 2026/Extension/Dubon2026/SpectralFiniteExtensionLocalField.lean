import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.NumberTheory.LocalField.Basic

/-! # Actual local fields from the canonical spectral norm on finite extensions -/

namespace Dubon2026
noncomputable section

open scoped Topology

/-- The actual norm valuation of a locally compact nontrivially normed
ultrametric field gives the existing valuative local-field structure, with
the original norm topology preserved. -/
theorem normValuation_isNonarchimedeanLocalField
    (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F]
    [LocallyCompactSpace F] :
    letI : ValuativeRel F := ValuativeRel.ofValuation (NormedField.valuation (K := F))
    IsNonarchimedeanLocalField F := by
  letI : ValuativeRel F := ValuativeRel.ofValuation (NormedField.valuation (K := F))
  haveI : (NormedField.valuation (K := F)).Compatible :=
    Valuation.Compatible.ofValuation _
  haveI : IsValuativeTopology F := by
    apply IsValuativeTopology.of_zero
    intro s
    have h := (NormedField.toValued (K := F)).is_topological_valuation s
    exact h.trans (by simpa only [sub_zero] using
      (NormedField.valuation (K := F)).exists_setOf_restrict_le_iff 0 s)
  haveI : ValuativeRel.IsNontrivial F :=
    (ValuativeRel.isNontrivial_iff_isNontrivial (NormedField.valuation (K := F))).mpr
      inferInstance
  exact {}

/-- A genuine finite extension of the original complete local normed field
is a local field for its canonical spectral norm and actual norm valuation.
Local compactness follows from the finite-dimensional topology theorem. -/
theorem spectralFiniteExtension_isNonarchimedeanLocalField
    (K L : Type) [NontriviallyNormedField K] [IsUltrametricDist K]
    [CompleteSpace K] [LocallyCompactSpace K] [Field L] [Algebra K L]
    [FiniteDimensional K L] :
    letI : NontriviallyNormedField L := spectralNorm.nontriviallyNormedField K L
    letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
    letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
    letI : ValuativeRel L := ValuativeRel.ofValuation (NormedField.valuation (K := L))
    IsNonarchimedeanLocalField L := by
  letI : NontriviallyNormedField L := spectralNorm.nontriviallyNormedField K L
  letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
  letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
  haveI : ProperSpace L := FiniteDimensional.proper K L
  exact normValuation_isNonarchimedeanLocalField L

end
end Dubon2026
