import Dubon2026.SupportedOutsideUnramifiedVanishing
import Dubon2026.OriginalUnramifiedIdeleSupport
import Dubon2026.IdeleClassHerbrandFromOutside

/-! # The original cyclic idele-class Herbrand formula with local hypotheses discharged

One actual finite stable support supplies class surjectivity and excludes
every absolutely ramified place. The proved original integer-unit
vanishing outside it completes the local calculation. Together with the
actual S-unit formula, exact coefficient sequence and unrestricted local
calculations, this proves the original global ratio needed for DUB-17's
norm-index lower bound. Global reciprocity and duality remain separate.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField Classical
variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsCyclic Gal(L/K)]

/-- Original cyclic idele-class H1 and H2 are finite, with the exact degree ratio; every local and support-choice hypothesis is proved. -/
theorem original_ideleClass_herbrand :
    Finite (groupCohomology (originalIdeleClassRep K L) 1) ∧
      Finite (groupCohomology (originalIdeleClassRep K L) 2) ∧
      Nat.card (groupCohomology (originalIdeleClassRep K L) 2) =
        Nat.card (groupCohomology (originalIdeleClassRep K L) 1) * Nat.card Gal(L/K) := by
  obtain ⟨S, _, hS, hsurj, hunram⟩ := original_exists_unramified_galoisStable_idele_support K L ∅
  apply original_ideleClass_herbrand_of_outside K L S hS hsurj
  letI := IsCyclic.commGroup (α := Gal(L/K))
  letI := supportedOutsidePlaceAction K L S hS
  intro ω
  exact supportedOutsideOrbitPoint_first_second_zero_of_unramified K L S hS ω
    (hunram ω.out.val ω.out.property)

end
end Dubon2026
