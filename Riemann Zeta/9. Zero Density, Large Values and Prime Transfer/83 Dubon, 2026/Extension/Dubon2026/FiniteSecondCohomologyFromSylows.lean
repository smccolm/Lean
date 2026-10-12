import Dubon2026.FiniteSecondCohomologySylowDetection
import Mathlib.Data.Nat.PrimeFin

/-! # Original second cohomology finiteness from genuine Sylow comparisons -/

namespace Dubon2026
noncomputable section

/-- The original full second cohomology injects into finitely many genuine
Sylow cohomology groups. Their finiteness therefore implies its finiteness;
no finite cardinality premise is imposed on the original full group. -/
theorem finite_second_cohomology_of_sylows
    {k G : Type} [CommRing k] [Group G] [Fintype G] (A : Rep k G)
    (hfinite : ∀ p : ℕ, p.Prime → p ∣ Fintype.card G → ∀ P : Sylow p G,
      Finite (groupCohomology (Rep.res (P : Subgroup G).subtype A) 2)) :
    Finite (groupCohomology A 2) := by
  let I := (Fintype.card G).primeFactors
  have hprime (p : I) : p.val.Prime := (Nat.mem_primeFactors.mp p.property).1
  have hdvd (p : I) : p.val ∣ Fintype.card G := (Nat.mem_primeFactors.mp p.property).2.1
  let P (p : I) : Sylow p.val G := Classical.choice inferInstance
  let C (p : I) := groupCohomology (Rep.res (P p : Subgroup G).subtype A) 2
  haveI (p : I) : Finite (C p) := hfinite p.val (hprime p) (hdvd p) (P p)
  let f : groupCohomology A 2 → ∀ p : I, C p :=
    fun x p => subgroupCohomologyComparison A (P p : Subgroup G) 2 x
  apply Finite.of_injective f
  intro x y hxy
  apply sub_eq_zero.mp
  apply finiteSecondCohomology_sylow_zero A (x - y)
  intro p hp hpd
  let q : I := ⟨p, Nat.mem_primeFactors.mpr ⟨hp, hpd, Fintype.card_ne_zero⟩⟩
  refine ⟨P q, ?_⟩
  rw [map_sub]
  exact sub_eq_zero.mpr (congrFun hxy q)

end
end Dubon2026
