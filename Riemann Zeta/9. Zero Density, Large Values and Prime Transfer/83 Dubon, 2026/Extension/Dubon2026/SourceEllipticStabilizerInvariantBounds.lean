import Dubon2026.SourceEllipticStabilizerScaling
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-! Root counting bounds the actual coordinate-change stabilizer directly
from its scaling invariant. This avoids short-normal-form infrastructure
and supplies exactly the bounds needed for the DUB-17/18 inertia image. -/
namespace Dubon2026.SourceEllipticStabilizer
open WeierstrassCurve Polynomial
noncomputable section
variable {K : Type*} [Field K] (W : WeierstrassCurve K)

theorem finite_and_card_le_of_scaling_power (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    (n : ℕ) (hn : 0 < n)
    (hpow : ∀ C : VariableChange K, C • W = W → (C.u : K) ^ n = 1) :
    Finite (MulAction.stabilizer (VariableChange K) W) ∧
      Nat.card (MulAction.stabilizer (VariableChange K) W) ≤ n := by
  classical
  let T := (nthRoots n (1 : K)).toFinset
  let f : MulAction.stabilizer (VariableChange K) W → T := fun C =>
    ⟨C.val.u, by
      change (C.val.u : K) ∈ (nthRoots n (1 : K)).toFinset
      rw [Multiset.mem_toFinset, mem_nthRoots hn]
      exact hpow C.val (MulAction.mem_stabilizer_iff.mp C.property)⟩
  have hf : Function.Injective f := fun _ _ h =>
    scaling_injective W h2 h3 (congrArg Subtype.val h)
  letI : Finite (MulAction.stabilizer (VariableChange K) W) := Finite.of_injective f hf
  refine ⟨inferInstance, (Nat.card_le_card_of_injective f hf).trans ?_⟩
  change Nat.card T ≤ n
  rw [Nat.card_eq_finsetCard]
  exact (Multiset.toFinset_card_le _).trans (card_nthRoots n 1)

variable [W.IsElliptic]

theorem j_eq_1728_of_c6_eq_zero (hc : W.c₆ = 0) : W.j = 1728 := by
  have h := W.c_relation
  rw [hc, zero_pow (by norm_num : (2 : ℕ) ≠ 0), sub_zero] at h
  rw [WeierstrassCurve.j, ← h, mul_left_comm, ← coe_Δ', Units.inv_mul, mul_one]

theorem c6_ne_zero_of_j_ne_1728 (hj : W.j ≠ 1728) : W.c₆ ≠ 0 :=
  fun hc => hj (j_eq_1728_of_c6_eq_zero W hc)

theorem stabilizer_card_le_four (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) (hj : W.j ≠ 0) :
    Finite (MulAction.stabilizer (VariableChange K) W) ∧
      Nat.card (MulAction.stabilizer (VariableChange K) W) ≤ 4 :=
  finite_and_card_le_of_scaling_power W h2 h3 4 (by norm_num)
    (fun _ hC => scaling_pow_four W (fun hc => hj (W.j_eq_zero hc)) hC)

theorem stabilizer_card_le_six (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) (hj : W.j ≠ 1728) :
    Finite (MulAction.stabilizer (VariableChange K) W) ∧
      Nat.card (MulAction.stabilizer (VariableChange K) W) ≤ 6 :=
  finite_and_card_le_of_scaling_power W h2 h3 6 (by norm_num)
    (fun _ hC => scaling_pow_six W (c6_ne_zero_of_j_ne_1728 W hj) hC)

theorem stabilizer_card_le_two (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    (hj0 : W.j ≠ 0) (hj1728 : W.j ≠ 1728) :
    Finite (MulAction.stabilizer (VariableChange K) W) ∧
      Nat.card (MulAction.stabilizer (VariableChange K) W) ≤ 2 :=
  finite_and_card_le_of_scaling_power W h2 h3 2 (by norm_num)
    (fun _ hC => scaling_pow_two W (fun hc => hj0 (W.j_eq_zero hc))
      (c6_ne_zero_of_j_ne_1728 W hj1728) hC)

end
end Dubon2026.SourceEllipticStabilizer
