import Dubon2026.FiniteSecondCohomologyFromSylows
import Mathlib.Data.Nat.Factorization.Basic

/-! # Actual second cohomology order divisibility from genuine Sylow cohomology -/

namespace Dubon2026
noncomputable section

/-- A Sylow subgroup of the original multiplicative tag of cohomology
injects under the genuine comparison with a Sylow subgroup of the acting
group. This is the proved primary-component injection, with original values. -/
theorem sylowSecondCohomologyComparison_injective
    {k G : Type} [CommRing k] [Group G] [Finite G] (A : Rep.{0} k G)
    (p : ℕ) [Fact p.Prime] (P : Sylow p G)
    (Q : Sylow p (Multiplicative (groupCohomology A 2))) :
    Function.Injective (fun x : Q =>
      subgroupCohomologyComparison A (P : Subgroup G) 2 (Multiplicative.toAdd x.val)) := by
  let j : Q → AddCommGroup.primaryComponent (groupCohomology A 2) p := fun x =>
    ⟨Multiplicative.toAdd x.val, by
      obtain ⟨m, hm⟩ := Q.isPGroup' x
      refine AddCommGroup.mem_primaryComponent.mpr ⟨m, ?_⟩
      have h := congrArg (fun y : Q => Multiplicative.toAdd y.val) hm
      exact h⟩
  intro x y hxy
  have he : j x = j y := sylowCohomologyComparison_primary_injective A 2 p P hxy
  apply Subtype.ext
  exact congrArg (fun z : AddCommGroup.primaryComponent (groupCohomology A 2) p =>
    Multiplicative.ofAdd z.val) he

/-- If the actual second cohomology of every actual Sylow restriction is
finite with order dividing that Sylow group order, then the original H2
is finite and its order divides the original whole group order. -/
theorem secondCohomology_card_dvd_of_sylows
    {k G : Type} [CommRing k] [Group G] [Fintype G] (A : Rep.{0} k G)
    (hSylow : ∀ p : ℕ, p.Prime → ∀ P : Sylow p G,
      Finite (groupCohomology (Rep.res (P : Subgroup G).subtype A) 2) ∧
        Nat.card (groupCohomology (Rep.res (P : Subgroup G).subtype A) 2) ∣ Nat.card P) :
    Finite (groupCohomology A 2) ∧ Nat.card (groupCohomology A 2) ∣ Nat.card G := by
  haveI : Finite (groupCohomology A 2) := finite_second_cohomology_of_sylows A
    (fun p hp _ P => (hSylow p hp P).1)
  refine ⟨inferInstance, (Nat.dvd_iff_prime_pow_dvd_dvd _ _).mpr ?_⟩
  intro p m hp hpm
  letI : Fact p.Prime := ⟨hp⟩
  let P : Sylow p G := Classical.choice inferInstance
  let Q : Sylow p (Multiplicative (groupCohomology A 2)) := Classical.choice inferInstance
  let f : Q →* Multiplicative (groupCohomology (Rep.res (P : Subgroup G).subtype A) 2) :=
    ((subgroupCohomologyComparison A (P : Subgroup G) 2).hom.toAddMonoidHom.toMultiplicative).comp
      (Q : Subgroup (Multiplicative (groupCohomology A 2))).subtype
  have hf : Function.Injective f := sylowSecondCohomologyComparison_injective A p P Q
  have hQ := Q.pow_dvd_card_of_pow_dvd_card hpm
  have hQP := Subgroup.card_dvd_of_injective f hf
  exact hQ.trans (hQP.trans ((hSylow p hp P).2.trans (P : Subgroup G).card_subgroup_dvd_card))

end
end Dubon2026
