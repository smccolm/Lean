import Dubon2026.CosetTraceCochains
import Mathlib.Tactic.Abel

/-! # An explicit original-cochain homotopy for restriction followed by coset trace -/

namespace Dubon2026
noncomputable section

open scoped BigOperators

variable {R G : Type} [CommRing R] [Group G] (A : Rep R G) (S : Subgroup G)

/-- The literal one-cochain correction relating an original cocycle to
its restriction and finite coset trace. -/
def cosetRestrictionHomotopyTerm (c : G × G → A) (g : G) (q : G ⧸ S) : A :=
  c (g, q.out) - c ((g • q).out, cosetTransition S g q)

/-- The original cocycle identity gives the exact termwise homotopy.
It holds for unnormalized cocycles as well. -/
theorem cosetRestrictionHomotopyTerm_identity (c : groupCohomology.cocycles₂ A)
    (g h : G) (q : G ⧸ S) :
    c (g, h) - cosetTraceTwoTerm A S (fun z => c (z.1, z.2)) g h q =
      A.ρ g (cosetRestrictionHomotopyTerm A S c h q) -
        cosetRestrictionHomotopyTerm A S c (g * h) q +
        cosetRestrictionHomotopyTerm A S c g (h • q) := by
  have h₁ := (groupCohomology.mem_cocycles₂_iff _).mp c.property g h q.out
  have h₂ := (groupCohomology.mem_cocycles₂_iff _).mp c.property
    g (h • q).out (cosetTransition S h q)
  have h₃ := (groupCohomology.mem_cocycles₂_iff _).mp c.property
    (g • h • q).out (cosetTransition S g (h • q)) (cosetTransition S h q)
  rw [cosetTransition_factor] at h₂
  rw [cosetTransition_factor] at h₃
  have hcoord : (cosetTransition S (g * h) q : G) =
      (cosetTransition S g (h • q) : G) * (cosetTransition S h q : G) :=
    congrArg Subtype.val (cosetTransition_mul S g h q)
  dsimp only [cosetRestrictionHomotopyTerm, cosetTraceTwoTerm]
  rw [map_sub, mul_smul, hcoord]
  have hsum := congrArg₂ (fun a b : A => a + b) h₁ h₃
  have hsum' := congrArg₂ (fun a b : A => a - b) hsum h₂
  apply sub_eq_zero.mp
  calc
    _ = (c (g * h, q.out) + c (g, h) +
          (c (g * (h • q).out, cosetTransition S h q) +
            c ((g • h • q).out, cosetTransition S g (h • q)))) -
        (c (g * (h • q).out, cosetTransition S h q) + c (g, (h • q).out)) -
      ((A.ρ g (c (h, q.out)) + c (g, h * q.out) +
          (A.ρ (g • h • q).out (c (cosetTransition S g (h • q), cosetTransition S h q)) +
            c ((g • h • q).out, (cosetTransition S g (h • q) : G) * cosetTransition S h q))) -
        (A.ρ g (c ((h • q).out, cosetTransition S h q)) + c (g, h * q.out))) := by abel
    _ = 0 := sub_eq_zero.mpr hsum'

/-- The finite sum of the original one-cochain corrections. -/
def cosetRestrictionHomotopy [Fintype (G ⧸ S)] (c : G × G → A) : G → A :=
  fun g => ∑ q : G ⧸ S, cosetRestrictionHomotopyTerm A S c g q

/-- The original differential of the explicit correction is exactly
the index multiple of the cocycle minus its actual restriction trace. -/
theorem cosetRestrictionHomotopy_differential [Fintype (G ⧸ S)]
    (c : groupCohomology.cocycles₂ A) :
    groupCohomology.d₁₂ A (cosetRestrictionHomotopy A S c) =
      Fintype.card (G ⧸ S) • c.val - cosetTraceTwo A S (fun z => c (z.1, z.2)) := by
  funext z
  obtain ⟨g, h⟩ := z
  have hs := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun q _ => cosetRestrictionHomotopyTerm_identity A S c g h q)
  have hr : (∑ q : G ⧸ S, cosetRestrictionHomotopyTerm A S c g (h • q)) =
      ∑ q : G ⧸ S, cosetRestrictionHomotopyTerm A S c g q :=
    Equiv.sum_comp (MulAction.toPerm h) _
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, ← map_sum, hr] at hs
  exact hs.symm

end
end Dubon2026
