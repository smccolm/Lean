import Dubon2026.IntegralNormalBasisLattice
import Dubon2026.FullBasisLatticeBounds
import Dubon2026.LocalFieldIntegerIntegralClosure
import Mathlib.RingTheory.Finiteness.Basic

/-! # An actual integral normal lattice between original local-field ideal powers -/

namespace Dubon2026
noncomputable section

open scoped ValuativeRel

/-- The original local Galois field admits an integral normal-basis lattice
which contains a power of the original uniformizer times the actual integer
ring. Both containments concern the original coefficients inside the field. -/
theorem localField_exists_integral_normal_lattice
    (K L : Type) [Field K] [Field L] [Algebra K L] [IsGalois K L]
    [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
    [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
    [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
    (π : 𝒪[K]) (hπ : Irreducible π) :
    ∃ (b : Module.Basis Gal(L/K) K L) (n : ℕ),
      (∀ σ, b σ = σ (b 1)) ∧
      (∀ x ∈ Submodule.span 𝒪[K] (Set.range b),
        x ∈ (ValuativeRel.valuation L).integer) ∧
      ∀ x : 𝒪[L], π ^ n • (x : L) ∈ Submodule.span 𝒪[K] (Set.range b) := by
  haveI : FiniteDimensional K L := localField_field_module_finite
  haveI : Module.Finite 𝒪[K] 𝒪[L] := localField_integer_module_finite
  haveI : IsIntegralClosure 𝒪[L] 𝒪[K] L := localField_integer_isIntegralClosure
  obtain ⟨b, hb, hint⟩ := exists_integral_normal_basis 𝒪[K] K L
  let j : 𝒪[L] →ₗ[𝒪[K]] L := (IsScalarTower.toAlgHom 𝒪[K] 𝒪[L] L).toLinearMap
  obtain ⟨n, hn⟩ := fullBasis_span_absorbs_uniformizer_power b j.range
    (Submodule.fg_range j) π hπ
  refine ⟨b, n, hb, ?_, fun x => hn (x : L) ⟨x, rfl⟩⟩
  have hA : Submodule.span 𝒪[K] (Set.range b) ≤
      (integralClosure 𝒪[K] L).toSubmodule := by
    apply Submodule.span_le.mpr
    rintro _ ⟨σ, rfl⟩
    exact hint σ
  intro x hx
  obtain ⟨y, rfl⟩ := (IsIntegralClosure.isIntegral_iff (A := 𝒪[L])).mp (hA hx)
  exact y.property

end
end Dubon2026
