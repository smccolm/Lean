import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! # Original coefficient exactness under internal Hom from a lattice

The pinned linear projective lifting property and actual range/kernel
identity prove exactness of the literal internal-Hom sequence. This
supplies the coefficient sequence used for DUB-17's lattice acyclicity.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory

/-- Postcomposition with the zero coefficient map is the zero internal-Hom map. -/
instance originalInternalHomPreservesZeroMorphisms
    {k G : Type} [CommRing k] [Group G] (M : Rep.{0} k G) :
    (Rep.ihom M).PreservesZeroMorphisms where
  map_zero _ _ := rfl

/-- A projective original linear source preserves the actual short exact coefficient sequence under internal Hom. -/
theorem originalInternalHom_shortExact
    {k G : Type} [CommRing k] [Group G] (M : Rep.{0} k G)
    [Module.Projective k M] {X : ShortComplex (Rep k G)} (hX : X.ShortExact) :
    (X.map (Rep.ihom M)).ShortExact := by
  have hf := (Rep.mono_iff_injective X.f).mp hX.mono_f
  have hg := (Rep.epi_iff_surjective X.g).mp hX.epi_g
  have hr : LinearMap.range X.f.hom.toLinearMap = LinearMap.ker X.g.hom.toLinearMap :=
    (hX.exact.map (forget₂ (Rep k G) (ModuleCat k))).moduleCat_range_eq_ker
  refine {
    exact := ?_
    mono_f := (Rep.mono_iff_injective _).mpr (fun φ ψ h => by
      apply LinearMap.ext
      intro m
      exact hf (LinearMap.congr_fun h m))
    epi_g := (Rep.epi_iff_surjective _).mpr (fun χ => by
      obtain ⟨φ, hφ⟩ := Module.projective_lifting_property X.g.hom.toLinearMap χ hg
      exact ⟨φ, hφ⟩) }
  apply ((X.map (Rep.ihom M)).exact_map_iff_of_faithful
    (forget₂ (Rep k G) (ModuleCat k))).mp
  rw [ShortComplex.moduleCat_exact_iff]
  intro φ hφ
  change M →ₗ[k] X.X₂ at φ
  change X.g.hom.toLinearMap ∘ₗ φ = 0 at hφ
  have hm : ∀ m, φ m ∈ LinearMap.range X.f.hom.toLinearMap := by
    intro m
    rw [hr, LinearMap.mem_ker]
    exact LinearMap.congr_fun hφ m
  let ψ : M →ₗ[k] X.X₁ := (LinearEquiv.ofInjective X.f.hom.toLinearMap hf).symm.toLinearMap ∘ₗ
    LinearMap.codRestrict (LinearMap.range X.f.hom.toLinearMap) φ hm
  refine ⟨ψ, LinearMap.ext fun m => ?_⟩
  exact congrArg Subtype.val
    ((LinearEquiv.ofInjective X.f.hom.toLinearMap hf).apply_symm_apply ⟨φ m, hm m⟩)

end
end Dubon2026
