import Dubon2026.OriginalCanonicalClassSystem
import Dubon2026.OriginalClassInvariantCorestriction

/-! # Original corestriction for the canonically normalized class system

Consume the full canonical system and an existing original full-order
class. The native restriction-surjectivity and trace-index results supply
corestriction compatibility for those same normalized invariants. This is
the next input to DUB-17's subgroup local-fundamental-class comparison.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2

/-- The full original canonical invariant system together with compatibility with every genuine subgroup cohomology trace; this proposition alone asserts no existence. -/
def OriginalCanonicalClassInvariantTraceSystem
    (K E : Type) [Field K] [Field E] [NumberField E]
    [Algebra K E] [FiniteDimensional K E]
    (total : groupCohomology (originalFullIdeleRep K E) 2 →+ AddCircle (1 : ℚ)) : Prop :=
    ∃ invG : groupCohomology (originalIdeleClassRep K E) 2 →+ AddCircle (1 : ℚ),
      Function.Injective invG ∧
      (∀ z : AddCircle (1 : ℚ), z ∈ invG.range ↔ Module.finrank K E • z = 0) ∧
      (∀ x : groupCohomology (originalFullIdeleRep K E) 2,
        invG ((groupCohomology.functor ℤ Gal(E/K) 2).map (originalFullClassRepHom K E) x) = total x) ∧
      ∀ S : Subgroup Gal(E/K),
        ∃ invS : groupCohomology (Rep.res S.subtype (originalIdeleClassRep K E)) 2 →+ AddCircle (1 : ℚ),
          Function.Injective invS ∧
          (∀ z : AddCircle (1 : ℚ), z ∈ invS.range ↔ Nat.card S • z = 0) ∧
          (∀ x : groupCohomology (originalIdeleClassRep K E) 2,
            invS ((groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype (originalIdeleClassRep K E))) 2).hom x) =
              S.index • invG x) ∧
          (letI : Fintype (Gal(E/K) ⧸ S) := Fintype.ofFinite _
           ∀ y : groupCohomology (Rep.res S.subtype (originalIdeleClassRep K E)) 2,
             invG ((subgroupCohomologyTrace (originalIdeleClassRep K E) S 2).hom y) = invS y)

/-- The actual canonical class system retains all its normalization clauses and is compatible with the genuine original cohomology trace on every subgroup. -/
theorem originalIdeleClass_canonical_system_with_trace
    (K E : Type) [Field K] [NumberField K] [Field E] [NumberField E]
    [Algebra K E] [FiniteDimensional K E] [IsGalois K E]
    (total : groupCohomology (originalFullIdeleRep K E) 2 →+ AddCircle (1 : ℚ))
    (hfull : ∃ u : groupCohomology (originalIdeleClassRep K E) 2,
      addOrderOf u = Module.finrank K E)
    (h : OriginalCanonicalClassInvariantSystem K E total) :
    OriginalCanonicalClassInvariantTraceSystem K E total := by
  obtain ⟨u, hu⟩ := hfull
  obtain ⟨invG, hi, hr, ht, hs⟩ := h
  refine ⟨invG, hi, hr, ht, fun S => ?_⟩
  obtain ⟨invS, hiS, hrS, hres⟩ := hs S
  exact ⟨invS, hiS, hrS, hres,
    originalIdeleClass_invariant_original_trace_of_full_order K E u hu S invG invS hres⟩


/-- Injectivity of each genuine original subgroup class trace, with its finite coset enumeration fixed by the original finite extension. -/
def OriginalClassTraceInjective
    (K E : Type) [Field K] [Field E] [NumberField E]
    [Algebra K E] [FiniteDimensional K E] : Prop :=
    ∀ S : Subgroup Gal(E/K),
      letI : Fintype (Gal(E/K) ⧸ S) := Fintype.ofFinite _
      Function.Injective (subgroupCohomologyTrace (originalIdeleClassRep K E) S 2).hom

/-- The actual subgroup class trace is injective when the canonical global and subgroup invariants satisfy their proved trace comparison. -/
theorem originalIdeleClass_canonical_trace_injective
    (K E : Type) [Field K] [Field E] [NumberField E]
    [Algebra K E] [FiniteDimensional K E]
    (total : groupCohomology (originalFullIdeleRep K E) 2 →+ AddCircle (1 : ℚ))
    (h : OriginalCanonicalClassInvariantTraceSystem K E total) :
    OriginalClassTraceInjective K E := by
  obtain ⟨invG, _, _, _, hs⟩ := h
  intro S
  letI : Fintype (Gal(E/K) ⧸ S) := Fintype.ofFinite _
  obtain ⟨invS, hiS, _, _, ht⟩ := hs S
  intro x y hxy
  apply hiS
  exact (ht x).symm.trans ((congrArg invG hxy).trans (ht y))

end
end Dubon2026
