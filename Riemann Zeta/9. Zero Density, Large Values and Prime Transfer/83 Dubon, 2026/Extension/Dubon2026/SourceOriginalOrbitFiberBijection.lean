import Dubon2026.SourceOriginalCosetOrbitOrder
import Dubon2026.SourceLevelIndexFormula
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! DUB-17/18 -> numerical modular genus -> exact original finite fibers.
Positive multiplicities and the exact total degree rule out identifications
between distinct full-stabilizer orbits of level cosets. This uses the
already proved orbit size/place-order equality and replaces a separate
analytic modular-form point-separation construction.
-/
namespace Dubon2026.SourceFunctionField.FiberOrbits
noncomputable section
open UpperHalfPlane
open scoped MatrixGroups BigOperators StabilizerCharacter

private theorem injective_of_positive_weight_sum {A B : Type*} [Fintype A] [Fintype B]
    (f : A → B) (hf : Function.Surjective f) (w : B → ℤ) (hw : ∀ b, 0 < w b)
    (hsum : ∑ a, w (f a) = ∑ b, w b) : Function.Injective f := by
  classical
  obtain ⟨g, hg⟩ := hf.hasRightInverse
  have hi : Function.Injective g := hg.injective
  have himage : ∑ a ∈ Finset.univ.image g, w (f a) = ∑ b, w b := by
    rw [Finset.sum_image (fun a _ b _ h => hi h)]
    exact Finset.sum_congr rfl (fun b _ => congrArg w (hg b))
  have hgs : Function.Surjective g := by
    intro a
    by_contra ha
    have hnot : a ∉ Finset.univ.image g := by simpa using ha
    have hlt := Finset.sum_lt_sum_of_subset (Finset.subset_univ (Finset.univ.image g))
      (Finset.mem_univ a) hnot (hw (f a)) (fun b _ _ => (hw (f b)).le)
    rw [himage, hsum] at hlt
    exact (lt_irrefl _ hlt)
  intro a b hab
  obtain ⟨a', rfl⟩ := hgs a
  obtain ⟨b', rfl⟩ := hgs b
  apply congrArg g
  simpa only [hg a', hg b'] using hab

/-- Full point-stabilizer orbits of the actual level cosets. -/
abbrev Orb (N : ℕ) (τ : ℍ) :=
  MulAction.orbitRel.Quotient (MulAction.stabilizer SL(2, ℤ) τ) (X N)

/-- The genuine positive discrete place order in this finite j-fiber. -/
def weight (N : ℕ) (τ : ℍ) (P : Fiber N τ) : ℤ :=
  P.1.ord (jOver N ℂ - algebraMap ℂ (modularFunctionFieldOver N ℂ) (JMultiplicity.jf τ))

/-- The original finite place attached to a full-stabilizer orbit of level cosets. -/
def orbitToFiber (N : ℕ) [NeZero N] (τ : ℍ) : Orb N τ → Fiber N τ :=
  Quotient.lift (toFiber N τ) (by
    intro a b hab
    change a ∈ MulAction.orbit (MulAction.stabilizer SL(2, ℤ) τ) b at hab
    obtain ⟨k, hk⟩ := hab
    rw [← hk]
    exact toFiber_stabilizer_smul N τ k b)

theorem orbitToFiber_surjective (N : ℕ) [NeZero N] (τ : ℍ) :
    Function.Surjective (orbitToFiber N τ) := by
  intro P
  obtain ⟨x, hx⟩ := toFiber_surjective N τ P
  exact ⟨Quotient.mk _ x, hx⟩

theorem toFiber_out (N : ℕ) [NeZero N] (τ : ℍ) (q : Orb N τ) :
    toFiber N τ q.out = orbitToFiber N τ q :=
  congrArg (orbitToFiber N τ) q.out_eq'

theorem card_coset_orbit_eq_weight (N : ℕ) [NeZero N] (τ : ℍ) (x : X N) :
    (Nat.card (MulAction.orbit (MulAction.stabilizer SL(2, ℤ) τ) x) : ℤ) =
      weight N τ (toFiber N τ x) := by
  induction x using QuotientGroup.induction_on with
  | H g => exact card_coset_orbit_eq_place_order N τ g

theorem sum_orbit_weights (N : ℕ) [NeZero N] (τ : ℍ) [Fintype (Orb N τ)] :
    ∑ q, weight N τ (orbitToFiber N τ q) = (SourceLevelProjective.dedekindPsi N : ℤ) := by
  classical
  letI : Fintype (X N) := Fintype.ofFinite _
  letI : ∀ q : Orb N τ,
      Fintype (MulAction.orbit (MulAction.stabilizer SL(2, ℤ) τ) q.out) :=
    fun _ => Fintype.ofFinite _
  have hcard : Fintype.card (X N) =
      ∑ q : Orb N τ, Fintype.card (MulAction.orbit (MulAction.stabilizer SL(2, ℤ) τ) q.out) := by
    rw [Fintype.card_congr (MulAction.selfEquivSigmaOrbits
      (MulAction.stabilizer SL(2, ℤ) τ) (X N)), Fintype.card_sigma]
  have hindex : Nat.card (X N) = SourceLevelProjective.dedekindPsi N :=
    SourceLevelProjective.gamma0_index N
  rw [Nat.card_eq_fintype_card] at hindex
  have hn : (∑ q : Orb N τ,
      Nat.card (MulAction.orbit (MulAction.stabilizer SL(2, ℤ) τ) q.out)) =
        SourceLevelProjective.dedekindPsi N := by
    simpa only [Nat.card_eq_fintype_card] using hcard.symm.trans hindex
  calc
    ∑ q, weight N τ (orbitToFiber N τ q) =
        ∑ q : Orb N τ, (Nat.card (MulAction.orbit (MulAction.stabilizer SL(2, ℤ) τ) q.out) : ℤ) := by
      apply Finset.sum_congr rfl
      intro q _
      rw [← toFiber_out]
      exact (card_coset_orbit_eq_weight N τ q.out).symm
    _ = (SourceLevelProjective.dedekindPsi N : ℤ) := by exact_mod_cast hn

theorem orbitToFiber_bijective (N : ℕ) [NeZero N] (τ : ℍ) :
    Function.Bijective (orbitToFiber N τ) := by
  classical
  letI : Fintype (Orb N τ) := Fintype.ofFinite _
  letI : Fintype (Fiber N τ) := Fintype.ofFinite _
  refine ⟨injective_of_positive_weight_sum (orbitToFiber N τ)
    (orbitToFiber_surjective N τ) (weight N τ) (fun P => P.2) ?_,
    orbitToFiber_surjective N τ⟩
  have h := sum_original_j_fiber_orders_eq_psi N ℂ (JMultiplicity.jf τ)
  have hf : (∑ P : Fiber N τ, weight N τ P) = (SourceLevelProjective.dedekindPsi N : ℤ) := by
    simpa only [finsum_eq_sum_of_fintype] using h
  exact (sum_orbit_weights N τ).trans hf.symm

end
end Dubon2026.SourceFunctionField.FiberOrbits
