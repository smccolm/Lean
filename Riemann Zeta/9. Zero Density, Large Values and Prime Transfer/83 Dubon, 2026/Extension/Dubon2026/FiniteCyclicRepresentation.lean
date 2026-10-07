import Dubon2026.FiniteGroupProjection
import Mathlib.Data.ZMod.Basic

/-! # Finite cyclic actions and their literal operator averages -/

namespace Dubon2026

noncomputable section

/-- A group element with d-th power one induces an actual cyclic-group homomorphism. -/
def finiteCyclicHom {G : Type*} [Group G] (d : ℕ) (g : G) (hg : g ^ d = 1) :
    Multiplicative (ZMod d) →* G :=
  (ZMod.lift d ⟨(zpowersHom G g).toAdditiveRight, by
    change g ^ (d : ℤ) = 1
    simpa only [zpow_natCast] using hg⟩).toMultiplicativeLeft

/-- On an integer representative, the cyclic homomorphism is exactly the corresponding power. -/
theorem finiteCyclicHom_intCast {G : Type*} [Group G] (d : ℕ) (g : G) (hg : g ^ d = 1)
    (j : ℤ) : finiteCyclicHom d g hg (Multiplicative.ofAdd (j : ZMod d)) = g ^ j := by
  change Additive.toMul (ZMod.lift (A := Additive G) d _ (j : ZMod d)) = _
  rw [ZMod.lift_coe]
  rfl

/-- Cyclic restriction of a genuine group representation. -/
def finiteCyclicRepresentation {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (d : ℕ) (g : G) (hg : g ^ d = 1) :
    Representation ℂ (Multiplicative (ZMod d)) V :=
  ρ.comp (finiteCyclicHom d g hg)

/-- The finite-group projection of a cyclic action is the exact sum over the first d powers. -/
theorem finiteCyclicProjection_eq {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (d : ℕ) [NeZero d] (g : G) (hg : g ^ d = 1) :
    finiteGroupProjection (finiteCyclicRepresentation ρ d g hg) =
      (d : ℂ)⁻¹ • ∑ j ∈ Finset.range d, ρ (g ^ j) := by
  rw [finiteGroupProjection_eq]
  have hsum : (∑ a : Multiplicative (ZMod d), finiteCyclicRepresentation ρ d g hg a) =
      ∑ j ∈ Finset.range d, ρ (g ^ j) := by
    rw [← (Multiplicative.ofAdd : ZMod d ≃ Multiplicative (ZMod d)).sum_comp]
    rw [← (ZMod.finEquiv d).toEquiv.sum_comp]
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro j _
    have hval : ((ZMod.finEquiv d) j).val = j.val := by
      cases d with
      | zero => exact (NeZero.ne 0 rfl).elim
      | succ d => rfl
    have hcast : (ZMod.finEquiv d) j = (j.val : ZMod d) := by
      rw [← hval, ZMod.natCast_zmod_val]
    change ρ (finiteCyclicHom d g hg (Multiplicative.ofAdd ((ZMod.finEquiv d) j))) = _
    rw [hcast]
    have h := finiteCyclicHom_intCast d g hg (j.val : ℤ)
    simpa only [Int.cast_natCast, zpow_natCast] using congrArg ρ h
  rw [hsum]
  simp

section Inner
variable {G V : Type*} [Group G] [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- Cyclic averaging is an orthogonal projection for every invariant inner product. -/
theorem finiteCyclicProjection_symmetric (ρ : Representation ℂ G V)
    (hρ : ∀ g x y, inner ℂ (ρ g x) (ρ g y) = inner ℂ x y)
    (d : ℕ) [NeZero d] (g : G) (hg : g ^ d = 1) :
    (finiteGroupProjection (finiteCyclicRepresentation ρ d g hg)).IsSymmetricProjection :=
  finiteGroupProjection_symmetric _ (fun a x y => hρ (finiteCyclicHom d g hg a) x y)

end Inner
end
end Dubon2026
