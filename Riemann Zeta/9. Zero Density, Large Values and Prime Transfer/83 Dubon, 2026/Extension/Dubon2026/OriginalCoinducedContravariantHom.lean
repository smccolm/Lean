import Dubon2026.OriginalCoinducedLatticeShift
import Dubon2026.OriginalInternalHomPrecomposition

/-! # The actual contravariant Hom sequence of the original shift

Identity evaluation extends every integral linear map across the
original coinduced inclusion. Literal quotient descent proves the
remaining exactness, preparing the equivariant extension used twice
in DUB-17's converse norm criterion.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2 Submodule.module Submodule.Quotient.module
variable {G : Type} [Group G] (M C : Rep.{0} ℤ G)

/-- Literal precomposition reverses the original coinduced coefficient sequence. -/
def originalCoinducedContravariantHomSequence : ShortComplex (Rep ℤ G) where
  X₁ := (Rep.ihom (originalCoinducedQuotient M)).obj C
  X₂ := (Rep.ihom (originalCoinducedFunctionRep M)).obj C
  X₃ := (Rep.ihom M).obj C
  f := originalInternalHomPrecomposition C (originalCoinducedShortComplex M).g
  g := originalInternalHomPrecomposition C (originalCoinducedUnit M)
  zero := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro η
    change originalCoinducedQuotient M →ₗ[ℤ] C at η
    apply LinearMap.ext
    intro x
    change η ((originalCoinducedShortComplex M).g.hom ((originalCoinducedUnit M).hom x)) = 0
    have hz := congrArg (fun f : M ⟶ originalCoinducedQuotient M => f.hom x)
      (originalCoinducedShortComplex M).zero
    change (originalCoinducedShortComplex M).g.hom ((originalCoinducedUnit M).hom x) = 0 at hz
    rw [hz]
    exact η.map_zero

/-- The actual reversed Hom sequence is short exact, using identity evaluation and literal quotient descent. -/
theorem originalCoinducedContravariantHom_shortExact :
    (originalCoinducedContravariantHomSequence M C).ShortExact := by
  have hg := (Rep.epi_iff_surjective _).mp (originalCoinducedShortComplex_shortExact M).epi_g
  refine {
    exact := ?_
    mono_f := (Rep.mono_iff_injective _).mpr (fun η θ h => by
      apply LinearMap.ext
      intro q
      obtain ⟨v, rfl⟩ := hg q
      exact LinearMap.congr_fun h v)
    epi_g := (Rep.epi_iff_surjective _).mpr (fun η => by
      change M →ₗ[ℤ] C at η
      refine ⟨η.comp (originalCoinducedEvaluation M 1), LinearMap.ext fun x => ?_⟩
      exact congrArg η (originalCoinducedEvaluation_unit M x)) }
  apply ((originalCoinducedContravariantHomSequence M C).exact_map_iff_of_faithful
    (forget₂ (Rep ℤ G) (ModuleCat ℤ))).mp
  rw [ShortComplex.moduleCat_exact_iff]
  intro η hη
  change originalCoinducedFunctionRep M →ₗ[ℤ] C at η
  change η.comp (originalCoinducedUnit M).hom.toLinearMap = 0 at hη
  have hk : (originalCoinducedUnit M).hom.toLinearMap.range ≤ η.ker := by
    rintro _ ⟨x, rfl⟩
    exact LinearMap.congr_fun hη x
  exact ⟨(originalCoinducedUnit M).hom.toLinearMap.range.liftQ η hk, rfl⟩

end
end Dubon2026
