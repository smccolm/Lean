import Dubon2026.SourceOriginalRegularCuspEquiv

/-! DUB-17/18 -> original Picard-period Hecke comparison -> the actual
regular/cusp period identification. The constructed equivalence agrees
with the original differential germ at every upper-half-plane point.
The existing global modular ratio supplies this consistency, while the
proved cusp germ injection fixes the normalization uniquely.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open UpperHalfPlane SourceCurve KaehlerDifferential Filter
open scoped Topology
variable (N : ℕ) [NeZero N]

theorem exists_original_regular_cusp_all_germs
    (ω : regularDifferentials ℂ (modularFunctionFieldOver N ℂ)) :
    ∃ f : CuspForm (CongruenceSubgroup.Gamma0 N) 2, ∀ τ : ℍ,
      originalCuspFormGerm N τ f = originalRegularDifferentialGerm N τ ω := by
  let x := (originalDifferentialCoordinateEquiv N).symm ω.val
  have hxω : x • D ℂ (modularFunctionFieldOver N ℂ) (jOver N ℂ) = ω.val :=
    (originalDifferentialCoordinateEquiv N).apply_symm_apply ω.val
  by_cases hx : x = 0
  · have hω : ω = 0 := by
      apply Subtype.ext
      simpa only [hx, zero_smul] using hxω.symm
    refine ⟨0, fun τ => ?_⟩
    rw [hω, map_zero, map_zero]
  · have hreg : x • D ℂ (modularFunctionFieldOver N ℂ) (jOver N ℂ) ∈
        regularDifferentials ℂ (modularFunctionFieldOver N ℂ) := hxω ▸ ω.property
    obtain ⟨k, g, h, f, hh, hr, he⟩ :=
      original_regular_differential_cusp_form_realization N x hx hreg
    refine ⟨f, fun τ => ?_⟩
    exact (original_regular_cusp_germ N τ x g h hh hr f he).symm

theorem originalRegularCuspEquiv_germ (τ : ℍ)
    (ω : regularDifferentials ℂ (modularFunctionFieldOver N ℂ)) :
    originalCuspFormGerm N τ (originalRegularCuspEquiv N ω) =
      originalRegularDifferentialGerm N τ ω := by
  obtain ⟨f, hf⟩ := exists_original_regular_cusp_all_germs N ω
  have he : originalRegularCuspEquiv N ω = f :=
    originalCuspFormGerm_injective N I
      ((originalRegularCuspEquiv_germ_at_I N ω).trans (hf I).symm)
  rw [he]
  exact hf τ

theorem originalRegularCuspEquiv_eventuallyEq (τ : ℍ)
    (ω : regularDifferentials ℂ (modularFunctionFieldOver N ℂ)) :
    (fun z : ℂ => originalRegularCuspEquiv N ω (ofComplex z)) =ᶠ[𝓝[≠] (τ : ℂ)]
      fun z => realize N
        (((originalDifferentialCoordinateEquiv N).symm ω.val) : LaurentSeries ℂ) (ofComplex z) *
          deriv (JMultiplicity.jf ∘ ofComplex) z :=
  Germ.coe_eq.mp (originalRegularCuspEquiv_germ N τ ω)

end
end Dubon2026.SourceFunctionField
