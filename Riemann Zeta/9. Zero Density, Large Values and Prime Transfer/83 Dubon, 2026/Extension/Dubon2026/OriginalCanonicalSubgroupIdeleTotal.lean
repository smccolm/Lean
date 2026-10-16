import Dubon2026.OriginalCanonicalClassSystemTrace
import Dubon2026.OriginalCohomologyTraceNaturality

/-! # The canonical total detects every actual subgroup idele-class kernel

Apply coefficient naturality to the original idele-to-class projection.
The previously constructed normalized invariants therefore evaluate a
subgroup idele class by the canonical total of its genuine trace. This
removes the class/projection comparison needed before the local
fundamental-class normalization on the DUB-17 dependency chain.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2

variable (K E : Type) [Field K] [Field E] [NumberField E] [Algebra K E]

/-- Global canonical-total and class-trace compatibility determine the invariant of the actual subgroup idele projection. -/
theorem originalIdeleClass_invariant_subgroup_projection_trace
    (S : Subgroup Gal(E/K)) [Fintype (Gal(E/K) ⧸ S)]
    (total : groupCohomology (originalFullIdeleRep K E) 2 →+ AddCircle (1 : ℚ))
    (invG : groupCohomology (originalIdeleClassRep K E) 2 →+ AddCircle (1 : ℚ))
    (invS : groupCohomology (Rep.res S.subtype (originalIdeleClassRep K E)) 2 →+ AddCircle (1 : ℚ))
    (htotal : ∀ x : groupCohomology (originalFullIdeleRep K E) 2,
      invG ((groupCohomology.functor ℤ Gal(E/K) 2).map (originalFullClassRepHom K E) x) = total x)
    (htrace : ∀ y : groupCohomology (Rep.res S.subtype (originalIdeleClassRep K E)) 2,
      invG ((subgroupCohomologyTrace (originalIdeleClassRep K E) S 2).hom y) = invS y)
    (x : groupCohomology (Rep.res S.subtype (originalFullIdeleRep K E)) 2) :
    invS ((groupCohomology.functor ℤ S 2).map
      ((Rep.resFunctor S.subtype).map (originalFullClassRepHom K E)) x) =
      total ((subgroupCohomologyTrace (originalFullIdeleRep K E) S 2).hom x) := by
  have hn := congrArg (fun f => f.hom x)
    (originalCohomologyTrace_coefficient_naturality S (originalFullClassRepHom K E) 2)
  exact (htrace _).symm.trans ((congrArg invG hn).trans (htotal _))

variable [FiniteDimensional K E]

/-- For every original subgroup, an idele projects to zero class exactly when its genuine trace has zero canonical total. -/
theorem originalIdeleClass_canonical_subgroup_projection_zero_iff
    (total : groupCohomology (originalFullIdeleRep K E) 2 →+ AddCircle (1 : ℚ))
    (h : OriginalCanonicalClassInvariantTraceSystem K E total)
    (S : Subgroup Gal(E/K)) :
    letI : Fintype (Gal(E/K) ⧸ S) := Fintype.ofFinite _
    ∀ x : groupCohomology (Rep.res S.subtype (originalFullIdeleRep K E)) 2,
      (groupCohomology.functor ℤ S 2).map
        ((Rep.resFunctor S.subtype).map (originalFullClassRepHom K E)) x = 0 ↔
      total ((subgroupCohomologyTrace (originalFullIdeleRep K E) S 2).hom x) = 0 := by
  letI : Fintype (Gal(E/K) ⧸ S) := Fintype.ofFinite _
  obtain ⟨invG, _, _, ht, hs⟩ := h
  obtain ⟨invS, hiS, _, _, htr⟩ := hs S
  intro x
  have hv := originalIdeleClass_invariant_subgroup_projection_trace K E S total invG invS ht htr x
  constructor
  · intro hx
    rw [← hv, hx]
    exact map_zero invS
  · intro hx
    apply hiS
    exact hv.trans (hx.trans (map_zero invS).symm)

end
end Dubon2026
