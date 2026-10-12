import Dubon2026.ContinuousH1Corestriction
import Dubon2026.CosetTraceOneRestriction
import Dubon2026.ContinuousCohomologyRestriction
import Mathlib.Data.Int.GCD

/-! # Actual continuous H1 restriction/corestriction and coprime detection

The original finite-index identity removes the restriction-kernel obstacle in
cyclotomic descent of the local Kummer perfect pairing.
-/

namespace Dubon2026
noncomputable section

open scoped BigOperators

variable {R G : Type} [CommRing R] [Group G]
  [TopologicalSpace R] [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Rep R G) [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  (S : Subgroup G) [Fintype (G ⧸ S)] (hS : IsOpen (S : Set G))

/-- The actual continuous H1 restriction followed by original finite-coset
corestriction is multiplication by the original subgroup index. -/
theorem continuousRepresentationH1Corestriction_restriction
    (x : ContinuousRepresentationH1 A hA) :
    continuousRepresentationH1Corestriction A hA S hS
      (continuousRepresentationH1Restriction A hA S.subtype continuous_subtype_val x) =
        Fintype.card (G ⧸ S) • x := by
  induction x using Submodule.Quotient.induction_on with
  | _ c =>
    let a := ∑ q : G ⧸ S, c.val q.out
    have he : continuousCosetTraceOneCocycle A hA S hS
        (continuousRepresentationCocycleOneRestriction A S.subtype continuous_subtype_val c) =
          Fintype.card (G ⧸ S) • c + continuousRepresentationCoboundaryOne A hA a := by
      apply Subtype.ext
      apply Subtype.ext
      exact cosetTraceOne_restriction A S c.val
    have hz : (Submodule.Quotient.mk (continuousRepresentationCoboundaryOne A hA a) :
        ContinuousRepresentationH1 A hA) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr ⟨a, rfl⟩
    rw [continuousRepresentationH1Restriction_mk, continuousRepresentationH1Corestriction_mk,
      he, Submodule.Quotient.mk_add, Submodule.Quotient.mk_smul, hz, add_zero]
    rfl

include hS in
/-- Actual continuous H1 restriction detects classes killed by an integer
coprime to the actual subgroup index. Both annihilations are proved on the
same original continuous cohomology class. -/
theorem continuousRepresentationH1Restriction_coprime_zero
    (m : ℕ) (hm : m.Coprime (Fintype.card (G ⧸ S)))
    (x : ContinuousRepresentationH1 A hA) (hx : m • x = 0)
    (hres : continuousRepresentationH1Restriction A hA S.subtype continuous_subtype_val x = 0) :
    x = 0 := by
  have hi := continuousRepresentationH1Corestriction_restriction A hA S hS x
  rw [hres, map_zero] at hi
  have h := gcd_nsmul_eq_zero.mpr ⟨hx, hi.symm⟩
  simpa only [hm.gcd_eq_one, one_nsmul] using h

end
end Dubon2026
