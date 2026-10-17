import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import Mathlib.GroupTheory.OrderOfElement

/-! # First cohomology of the actual trivial integer coefficient

Pinned H1 classification identifies it with homomorphisms from the finite
group to the additive integers. Finite-group torsion forces those maps
to vanish. This calculates the quotient term needed for H2 vanishing of
the original augmentation ideal in DUB-17's finite duality argument.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory

/-- Finite-group torsion forces first cohomology with trivial integral coefficients to vanish. -/
theorem originalTrivialInteger_first_zero (G : Type) [Group G] [Finite G] :
    Limits.IsZero (groupCohomology (Rep.trivial ℤ G ℤ) 1) := by
  letI := Fintype.ofFinite G
  have hz : ∀ f : Additive G →+ ℤ, f = 0 := by
    intro f
    apply AddMonoidHom.ext
    intro g
    have he := congrArg f (card_nsmul_eq_zero (x := g))
    rw [map_nsmul, map_zero] at he
    have hn : (Fintype.card (Additive G) : ℤ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    exact (mul_eq_zero.mp (show (Fintype.card (Additive G) : ℤ) * f g = 0 by
      simpa only [nsmul_eq_mul] using he)).resolve_left hn
  letI : Subsingleton (Additive G →+ ℤ) := ⟨fun f h => (hz f).trans (hz h).symm⟩
  exact (ModuleCat.isZero_of_subsingleton (ModuleCat.of ℤ (Additive G →+ ℤ))).of_iso
    (groupCohomology.H1IsoOfIsTrivial (Rep.trivial ℤ G ℤ))

end
end Dubon2026
