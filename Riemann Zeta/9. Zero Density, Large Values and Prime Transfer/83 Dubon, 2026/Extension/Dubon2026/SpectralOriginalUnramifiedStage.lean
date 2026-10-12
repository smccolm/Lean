import Dubon2026.SpectralUnramifiedIntegerExtension
import Dubon2026.LocalFieldOriginalUnramifiedStageExistence

/-! # Original unramified stages with their genuine compatible spectral structures -/

namespace Dubon2026
noncomputable section

open scoped ValuativeRel

/-- Every positive degree occurs inside the original separably closed
field with the actual spectral norm over K. The original finite field and
its unramified integer extension are constructed, not postulated. -/
theorem localField_exists_spectral_original_unramified_stage
    (K Ω : Type) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [ValuativeRel K] [(NormedField.valuation (K := K)).Compatible]
    [IsNonarchimedeanLocalField K] [Field Ω] [Algebra K Ω] [IsSepClosed Ω]
    (n : ℕ) [NeZero n] :
    ∃ F : FiniteGaloisIntermediateField K Ω, Module.finrank K F = n ∧
      letI : NontriviallyNormedField F := spectralNorm.nontriviallyNormedField K F
      letI : NormedAlgebra K F := spectralNorm.normedAlgebra K F
      letI : IsUltrametricDist F := IsUltrametricDist.of_normedAlgebra K
      letI : ValuativeRel F := ValuativeRel.ofValuation (NormedField.valuation (K := F))
      letI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation F) :=
        spectralValuation_hasExtension K F
      Algebra.FormallyUnramified 𝒪[K] 𝒪[F] := by
  obtain ⟨F, hval, htop, hlocal, hext, hunram, hdegree⟩ :=
    localField_exists_original_unramified_stage K Ω n
  letI : ValuativeRel F := hval
  letI : TopologicalSpace F := htop
  haveI : IsNonarchimedeanLocalField F := hlocal
  haveI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation F) := hext
  haveI : Algebra.FormallyUnramified 𝒪[K] 𝒪[F] := hunram
  exact ⟨F, hdegree, spectralIntegerExtension_formallyUnramified K F⟩

end
end Dubon2026
