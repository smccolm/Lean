import Dubon2026.CompactDVRLocalAlgebraFinite
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.RingTheory.Valuation.Extension
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.Algebraic.Integral

/-! # Finite generation of the original local-field integer-ring extension -/

namespace Dubon2026
noncomputable section

open scoped ValuativeRel nonZeroDivisors

variable {K L : Type} [Field K] [Field L] [Algebra K L]
  [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]

/-- The actual integer-ring extension of valuation-compatible original
local fields is a finite module. Compactness, separatedness and the original
faithful local algebra map discharge the complete compact-DVR argument. -/
theorem localField_integer_module_finite : Module.Finite 𝒪[K] 𝒪[L] := by
  letI := IsTopologicalAddGroup.rightUniformSpace K
  haveI := isUniformAddGroup_of_addCommGroup (G := K)
  letI := IsTopologicalAddGroup.rightUniformSpace L
  haveI := isUniformAddGroup_of_addCommGroup (G := L)
  exact compactDVRLocalAlgebra_module_finite

/-- The original fraction-field extension is finite-dimensional as a
consequence of the proved actual integer-ring finite generation. -/
theorem localField_field_module_finite : FiniteDimensional K L := by
  haveI : Module.Finite 𝒪[K] 𝒪[L] := localField_integer_module_finite
  exact Module.Finite.of_isLocalization 𝒪[K] 𝒪[L] 𝒪[K]⁰

end
end Dubon2026
