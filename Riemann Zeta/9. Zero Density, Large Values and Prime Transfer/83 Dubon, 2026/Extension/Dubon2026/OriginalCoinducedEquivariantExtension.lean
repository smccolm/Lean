import Dubon2026.OriginalCoinducedContravariantHom
import Dubon2026.OriginalInvariantConnectingKernel
import Dubon2026.OriginalInternalHomNormQuotient

/-! # Equivariant extension across the actual coinduced embedding

Vanishing of the original internal-Hom H1 removes the obstruction to
extending an actual coefficient morphism. The genuine invariant
connecting kernel supplies the extension; its defining equality is
retained for the two commuting diagrams in DUB-17's norm criterion.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2
variable {G : Type} [Group G] (M C : Rep.{0} ℤ G)

/-- Actual internal-Hom H1 vanishing constructs an equivariant extension of every original coefficient morphism. -/
theorem originalCoinduced_equivariant_extension
    (h : Limits.IsZero (groupCohomology ((Rep.ihom (originalCoinducedQuotient M)).obj C) 1))
    (f : M ⟶ C) :
    ∃ a : originalCoinducedFunctionRep M ⟶ C, originalCoinducedUnit M ≫ a = f := by
  let z : ((Rep.ihom M).obj C).ρ.invariants :=
    ⟨f.hom.toLinearMap, originalMorphism_internalHom_invariant M C f⟩
  have hz : (groupCohomology.δ (originalCoinducedContravariantHom_shortExact M C)
      0 1 rfl).hom ((groupCohomology.H0Iso ((Rep.ihom M).obj C)).inv z) = 0 := by
    exact congrArg (fun t : groupCohomology ((Rep.ihom (originalCoinducedQuotient M)).obj C) 1 ⟶
      groupCohomology ((Rep.ihom (originalCoinducedQuotient M)).obj C) 1 =>
        t ((groupCohomology.δ (originalCoinducedContravariantHom_shortExact M C)
          0 1 rfl).hom ((groupCohomology.H0Iso ((Rep.ihom M).obj C)).inv z)))
      (h.eq_of_src (𝟙 _) 0)
  obtain ⟨a, ha, he⟩ := originalInvariantConnecting_lift
    (originalCoinducedContravariantHom_shortExact M C) z hz
  refine ⟨Representation.linHom.invariantsEquivRepHom
    (originalCoinducedFunctionRep M) C ⟨a, ha⟩, ?_⟩
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  exact he

end
end Dubon2026
