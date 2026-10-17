import Dubon2026.OriginalCoinducedInvariantNorms
import Mathlib.RepresentationTheory.Coinvariants

/-! # The actual coinduced norm has no kernel on coinvariants

An identity-supported function represents each coinduced coinvariant.
Its coefficient is the sum of all original function values, which is
also evaluation of the actual norm at the identity. This supplies the
negative-degree-one input needed for DUB-17's integral duality route
without introducing an integer-graded Tate complex.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory

variable {k G : Type} [CommRing k] [Group G] [Fintype G] (A : Rep k G)

/-- The original coefficient embedded as an identity-supported coinduced function. -/
def originalCoinducedPoint : A →ₗ[k] originalCoinducedFunctionRep A := by
  classical
  exact {
    toFun := fun a => originalCoinducedFunction A (fun g => if g = 1 then a else 0)
    map_add' := fun a b => by
      apply Subtype.ext
      funext g
      change (if g = 1 then a + b else 0) =
        (if g = 1 then a else 0) + (if g = 1 then b else 0)
      split_ifs <;> simp
    map_smul' := fun r a => by
      apply Subtype.ext
      funext g
      change (if g = 1 then r • a else 0) = r • (if g = 1 then a else 0)
      split_ifs <;> simp }

/-- Every original coinduced function is the sum of the translates of its literal point values. -/
theorem originalCoinduced_point_sum (x : originalCoinducedFunctionRep A) :
    x = ∑ g : G, (originalCoinducedFunctionRep A).ρ g⁻¹ (originalCoinducedPoint A (x.val g)) := by
  classical
  apply Subtype.ext
  funext h
  simp only [Submodule.coe_sum, Finset.sum_apply]
  change x.val h = ∑ g : G, if h * g⁻¹ = 1 then x.val g else 0
  simp only [mul_inv_eq_one, Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- In the actual coinduced coinvariants, the original function equals the identity-supported sum of its values. -/
theorem originalCoinduced_coinvariant_point_sum (x : originalCoinducedFunctionRep A) :
    Representation.Coinvariants.mk (originalCoinducedFunctionRep A).ρ x =
      Representation.Coinvariants.mk (originalCoinducedFunctionRep A).ρ
        (originalCoinducedPoint A (∑ g : G, x.val g)) := by
  conv_lhs => rw [originalCoinduced_point_sum A x]
  simp only [map_sum, Representation.Coinvariants.mk_self_apply]

/-- A zero actual coinduced norm implies zero in the literal original coinvariant quotient. -/
theorem originalCoinduced_coinvariant_zero_of_norm_zero
    (x : originalCoinducedFunctionRep A)
    (hx : (originalCoinducedFunctionRep A).ρ.norm x = 0) :
    Representation.Coinvariants.mk (originalCoinducedFunctionRep A).ρ x = 0 := by
  have hs : ∑ g : G, x.val g = 0 := by
    have h := congrArg (fun y : originalCoinducedFunctionRep A => y.val 1) hx
    simp only [Representation.norm, LinearMap.sum_apply, Submodule.coe_sum,
      Finset.sum_apply] at h
    change (∑ g : G, x.val (1 * g)) = 0 at h
    simpa only [one_mul] using h
  rw [originalCoinduced_coinvariant_point_sum A x, hs, map_zero, map_zero]

end
end Dubon2026
