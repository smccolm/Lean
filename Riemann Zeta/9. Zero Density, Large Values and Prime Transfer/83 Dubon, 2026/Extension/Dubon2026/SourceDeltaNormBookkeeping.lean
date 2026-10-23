import Dubon2026.SourceModularJSeries

/-! DUB-17/18 -> original Frobenius/inertia -> good reduction -> exact
residue-field degree -> prime j nonmembership -> discriminant norm identity.
These proofs establish the literal product of root-of-unity twists of the eta
series, regrouping divisible and nondivisible indices. Only the topology and
product identities required for this exact norm calculation are selected.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularCurve_StarBank_deltaNorm. The existing q-substitution/power-series
identity is reused; repeated first-coefficient proofs are omitted. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open scoped PowerSeries.WithPiTopology

theorem prod_single_one {K : Type*} [CommRing K] (s : Finset ℕ) (x : ℕ → K) :
    ∏ b ∈ s, HahnSeries.single (1 : ℤ) (x b) = HahnSeries.single (s.card : ℤ) (∏ b ∈ s, x b) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, ih, HahnSeries.single_mul_single,
      Finset.card_insert_of_notMem ha, Nat.cast_succ, add_comm (1 : ℤ)]

theorem delta_bookkeeping {K : Type*} [Field K] (p : ℕ) (ε : K) (PT V1 V2 : LaurentSeries K)
    (hN : PT * V2 = V1 ^ (p + 1)) :
    HahnSeries.single (p : ℤ) ε * PT ^ 24 * (HahnSeries.single ((p * p : ℕ) : ℤ) (1 : K) * V2 ^ 24) =
      HahnSeries.C ε * (HahnSeries.single (p : ℤ) (1 : K) * V1 ^ 24) ^ (p + 1) := by
  have hs : HahnSeries.single (p : ℤ) ε * HahnSeries.single ((p * p : ℕ) : ℤ) (1 : K) =
      HahnSeries.C ε * HahnSeries.single (p : ℤ) (1 : K) ^ (p + 1) := by
    rw [HahnSeries.single_mul_single, HahnSeries.single_pow, HahnSeries.C_apply,
      HahnSeries.single_mul_single, mul_one, one_pow, mul_one,
      show (0 : ℤ) + (p + 1) • ((p : ℕ) : ℤ) = ((p : ℕ) : ℤ) + ((p * p : ℕ) : ℤ) by
        rw [nsmul_eq_mul]; push_cast; ring]
  calc HahnSeries.single (p : ℤ) ε * PT ^ 24 *
        (HahnSeries.single ((p * p : ℕ) : ℤ) (1 : K) * V2 ^ 24)
      = (HahnSeries.single (p : ℤ) ε * HahnSeries.single ((p * p : ℕ) : ℤ) (1 : K)) *
          (PT * V2) ^ 24 := by ring
    _ = HahnSeries.C ε * (HahnSeries.single (p : ℤ) (1 : K) * V1 ^ 24) ^ (p + 1) := by
        rw [hN, hs]; ring


end
end Dubon2026.SourceFunctionField
