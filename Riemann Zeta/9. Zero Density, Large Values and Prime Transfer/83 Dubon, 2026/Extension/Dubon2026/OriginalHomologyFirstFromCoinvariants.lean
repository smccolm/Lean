import Dubon2026.OriginalCoinvariantNormMap
import Mathlib.RepresentationTheory.Homological.GroupHomology.LongExactSequence

/-! # First homology vanishing from the actual coinvariant sequence

Pinned H0 naturality and the genuine homology long exact sequence reduce
first homology vanishing to the injective original coinvariant map.
This is the precise negative-two input on DUB-17's projectivity route.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory CategoryTheory.Limits

variable {k G : Type} [CommRing k] [Group G]

/-- Injectivity of the actual coinvariant map transfers to the pinned zeroth homology map. -/
theorem originalHomologyH0Map_injective_of_coinvariants
    {A B : Rep.{0} k G} (f : A ⟶ B)
    (hf : Function.Injective (Representation.Coinvariants.map A.ρ B.ρ f.hom)) :
    Function.Injective ((groupHomology.functor k G 0).map f) := by
  have hn (x : groupHomology A 0) :
      (groupHomology.H0Iso B).hom ((groupHomology.functor k G 0).map f x) =
        Representation.Coinvariants.map A.ρ B.ρ f.hom ((groupHomology.H0Iso A).hom x) :=
    congrArg (fun j => j.hom x) (groupHomology.map_id_comp_H0Iso_hom f)
  intro a b hab
  apply (ModuleCat.mono_iff_injective (groupHomology.H0Iso A).hom).mp inferInstance
  apply hf
  rw [← hn, ← hn, hab]

/-- Middle first homology vanishing and an injective original coinvariant inclusion imply first homology vanishing of the actual quotient. -/
theorem originalQuotient_first_homology_zero_of_coinvariant_inclusion
    {X : ShortComplex (Rep.{0} k G)} (hX : X.ShortExact)
    (hmid : Limits.IsZero (groupHomology X.X₂ 1))
    (hcoin : Function.Injective (Representation.Coinvariants.map X.X₁.ρ X.X₂.ρ X.f.hom)) :
    Limits.IsZero (groupHomology X.X₃ 1) := by
  haveI := groupHomology.mono_δ_of_isZero hX 0 hmid
  haveI : Mono ((groupHomology.functor k G 0).map X.f) :=
    (ModuleCat.mono_iff_injective _).mpr
      (originalHomologyH0Map_injective_of_coinvariants X.f hcoin)
  have hz : groupHomology.δ hX 1 0 rfl = 0 := by
    exact (groupHomology.mapShortComplex₁_exact hX (i := 1) (j := 0) rfl).mono_g_iff.mp
      (inferInstance : Mono ((groupHomology.functor k G 0).map X.f))
  rw [Limits.IsZero.iff_id_eq_zero, ← cancel_mono (groupHomology.δ hX 1 0 rfl),
    hz, comp_zero, comp_zero]

end
end Dubon2026
