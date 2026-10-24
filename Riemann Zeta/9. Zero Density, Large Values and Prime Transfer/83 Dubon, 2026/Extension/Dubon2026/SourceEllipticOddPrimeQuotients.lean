import Dubon2026.SourceEllipticCyclicGenerators
import Dubon2026.SourceEllipticOddPointFibers

/-! The complete family of actual odd-prime cyclic quotient maps, indexed
by p+1 generators of distinct cyclic subgroups. The subgroup count and every
map, kernel and fiber size are proved. These supply the geometric factors in
the integral modular-polynomial product needed by the DUB-17/18 cyclic-root
correspondence and inertia census. SourceIntegralComplexOddQuotientProduct
proves the complex product; integral reduction remains required. -/

namespace Dubon2026.SourceEllipticFunctionField
open WeierstrassCurve Dubon2026.SourceEllipticVelu
open Dubon2026.SourceEllipticCyclicCount
noncomputable section

variable {F K : Type*} [Field F] [Field K] [Algebra F K]
variable [IsAlgClosed K] [DecidableEq K] (W : WeierstrassCurve F) [W.IsElliptic]

/-- The actual p+1 cyclic quotients, with no assumed quotient maps or kernel certificates. -/
theorem exists_odd_prime_cyclic_quotients (p : ℕ) [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hpK : (p : K) ≠ 0) :
    letI : (W.baseChange K).IsElliptic :=
      ⟨by rw [baseChange, map_Δ]; exact W.isUnit_Δ.map (algebraMap F K)⟩
    ∃ Q : Fin (p + 1) → (W.baseChange K).toAffine.Point,
      ∃ hQ : ∀ i, addOrderOf (Q i) = 2 * (p / 2) + 1,
        Function.Injective (fun i => AddSubgroup.zmultiples (Q i)) ∧
        (∀ H : AddSubgroup (W.baseChange K).toAffine.Point,
          IsAddCyclic H → Nat.card H = p → ∃ i, AddSubgroup.zmultiples (Q i) = H) ∧
        ∀ i, (oddPointNorm (W.baseChange K) (hQ i)).ker = AddSubgroup.zmultiples (Q i) ∧
          Function.Surjective (oddPointNorm (W.baseChange K) (hQ i)) ∧
          ∀ R, Nat.card {P // oddPointNorm (W.baseChange K) (hQ i) P = R} = p := by
  have hodd : 2 * (p / 2) + 1 = p := by
    rcases hp.out.eq_two_or_odd' with h | h
    · exact (hp2 h).elim
    · exact Nat.two_mul_div_two_add_one_of_odd h
  obtain ⟨Q, ho, hi, hall⟩ := exists_prime_cyclic_generators W p hpK
  let hQ : ∀ i, addOrderOf (Q i) = 2 * (p / 2) + 1 := fun i => (ho i).trans hodd.symm
  refine ⟨Q, hQ, hi, hall, fun i => ⟨ker_oddPointNorm _ _, oddPointNorm_surjective _ _, ?_⟩⟩
  intro R
  exact (card_fiber_oddPointNorm _ _ R).trans hodd

end
end Dubon2026.SourceEllipticFunctionField
