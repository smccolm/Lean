import Dubon2026.LocalFieldIntegerGaloisRestriction
import Dubon2026.UnramifiedLocalResidueAutEquiv

/-! # The original unramified local-field Galois group equals the actual residue Galois group -/

namespace Dubon2026
noncomputable section

open scoped ValuativeRel

variable (K L : Type) [Field K] [Field L] [Algebra K L] [IsGalois K L]
  [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
  [Algebra.FormallyUnramified 𝒪[K] 𝒪[L]]

/-- Actual integer restriction and actual unramified residue reduction give
the original field-to-residue Galois equivalence. Compact local-field theory
supplies integer finiteness, integral closure and separatedness; actual Galois
fixed-field descent supplies residue surjectivity. -/
def unramifiedLocalFieldResidueGaloisEquiv : Gal(L/K) ≃* Gal(𝓀[L]/𝓀[K]) := by
  haveI : FiniteDimensional K L := localField_field_module_finite
  haveI : IsIntegralClosure 𝒪[L] 𝒪[K] L := localField_integer_isIntegralClosure
  haveI : Finite (𝒪[L] ≃ₐ[𝒪[K]] 𝒪[L]) :=
    Finite.of_equiv Gal(L/K) (localFieldIntegerGaloisEquiv K L).toEquiv
  letI := IsTopologicalAddGroup.rightUniformSpace L
  haveI := isUniformAddGroup_of_addCommGroup (G := L)
  haveI : Algebra.IsInvariant 𝒪[K] 𝒪[L] (𝒪[L] ≃ₐ[𝒪[K]] 𝒪[L]) :=
    Algebra.isInvariant_of_isGalois' 𝒪[K] K L 𝒪[L]
  exact (localFieldIntegerGaloisEquiv K L).trans unramifiedLocalResidueAutEquiv

/-- The genuine field-to-residue Galois equivalence retains actual integer
restriction and literal reduction of the same original element. -/
theorem unramifiedLocalFieldResidueGaloisEquiv_apply (g : Gal(L/K)) (x : 𝒪[L]) :
    unramifiedLocalFieldResidueGaloisEquiv K L g (IsLocalRing.residue 𝒪[L] x) =
      IsLocalRing.residue 𝒪[L] (localFieldIntegerGaloisEquiv K L g x) := by
  rfl

end
end Dubon2026
