import Dubon2026.OriginalInternalHomCoinducedTarget
import Dubon2026.OriginalArbitraryFreeCoinduced
import Dubon2026.OriginalRelationModuleSequence

/-! # Positive internal-Hom vanishing into actual projective coefficients

The actual free cover and pinned projective lifting construct a retract.
Its internal Hom is a retract of the explicitly coinduced model. This
is the vanishing input for DUB-17's actual fundamental presentation.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2

/-- Internal Hom into the actual arbitrary free representation has zero positive cohomology. -/
theorem originalInternalHomFreeTarget_positive_zero
    {k G : Type} [CommRing k] [Group G] [Fintype G]
    (M : Rep.{0} k G) (α : Type) (n : ℕ) :
    Limits.IsZero (groupCohomology ((Rep.ihom M).obj (Rep.free k G α)) (n + 1)) :=
  (originalInternalHomCoinducedTarget_positive_zero M (Rep.trivial k G (α →₀ k)) n).of_iso
    ((groupCohomology.functor k G (n + 1)).mapIso
      ((Rep.ihom M).mapIso (originalArbitraryFreeCoinducedIso α)))

/-- Actual projectivity gives internal-Hom vanishing into that same original integral coefficient by a constructed free-cover retract. -/
theorem originalInternalHomProjectiveTarget_positive_zero
    {G : Type} [Group G] [Fintype G] (M P : Rep.{0} ℤ G)
    [Projective P] (n : ℕ) :
    Limits.IsZero (groupCohomology ((Rep.ihom M).obj P) (n + 1)) := by
  letI : Epi (originalRelationFreeCover P) :=
    (Rep.epi_iff_surjective _).mpr (originalRelationFreeCover_surjective P)
  let r : Retract P (Rep.free ℤ G P) :=
    ⟨Projective.factorThru (𝟙 P) (originalRelationFreeCover P),
      originalRelationFreeCover P, Projective.factorThru_comp _ _⟩
  let rh := (r.map (Rep.ihom M)).map (groupCohomology.functor ℤ G (n + 1))
  have hz := originalInternalHomFreeTarget_positive_zero M P n
  exact Limits.IsZero.of_mono_eq_zero rh.i (hz.eq_of_tgt _ _)

end
end Dubon2026
