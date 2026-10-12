import Dubon2026.LocalFieldSpectralStructureUniqueness
import Dubon2026.SpectralUnramifiedStageInvariant

/-! # Spectral stage invariants equal the periods of the original local structures -/

namespace Dubon2026
noncomputable section

open scoped ValuativeRel

variable (K Ω : Type) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [ValuativeRel K] [(NormedField.valuation (K := K)).Compatible]
  [IsNonarchimedeanLocalField K] [Field Ω] [Algebra K Ω]

/-- The spectral invariant agrees with the actual arithmetic period
computed from any original extending local structures on the same unramified
field. Both its valuation and topology are proved equal to the spectral ones. -/
theorem spectralUnramifiedStageInvariant_eq_original_period
    (F : FiniteGaloisIntermediateField K Ω) (hF : SpectralStageUnramified K Ω F)
    [v : ValuativeRel F] [t : TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation F)]
    [Algebra.FormallyUnramified 𝒪[K] 𝒪[F]] (x : GaloisUnitH2FiniteStage K Ω F) :
    letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K F) := ⊥
    letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K F) := ⟨rfl⟩
    spectralUnramifiedStageInvariant K Ω F hF x = localFieldPeriodRationalInvariant K F x := by
  obtain ⟨hv, ht⟩ := localField_local_structures_eq_spectral K F
  cases hv
  cases ht
  rfl

end
end Dubon2026
