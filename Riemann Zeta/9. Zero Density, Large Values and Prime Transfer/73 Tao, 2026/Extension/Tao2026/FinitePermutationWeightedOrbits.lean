import Tao2026.BurgessWeilPrimeKummerFrobeniusSubfields
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.Dynamics.PeriodicPts.Lemmas

/-!
# Weighted fixed-point sums of finite permutations

The quotient includes every cycle, including singleton cycles. An orbit-invariant
weight compatible with repeated periods gives a
fixed-point sum equal to a divisor sum over the cycles. This is the finite
combinatorial input to the Kummer Euler-product integrality argument.
-/

namespace Tao2026
open Finset Function
open scoped BigOperators
noncomputable section

abbrev finitePermutationOrbits {α : Type*} (σ : Equiv.Perm α) :=
  Quotient (Equiv.Perm.SameCycle.setoid σ)

def finitePermutationOrbitLength {α : Type*} (σ : Equiv.Perm α)
    (o : finitePermutationOrbits σ) : ℕ := minimalPeriod σ o.out

theorem finitePermutationOrbitLength_pos {α : Type*} [Finite α]
    (σ : Equiv.Perm α) (o : finitePermutationOrbits σ) :
    0 < finitePermutationOrbitLength σ o :=
  minimalPeriod_pos_of_mem_periodicPts (σ.injective.mem_periodicPts o.out)

theorem finitePermutation_sameCycle_out {α : Type*}
    (σ : Equiv.Perm α) (o : finitePermutationOrbits σ) (x : α)
    (hx : Quotient.mk (Equiv.Perm.SameCycle.setoid σ) x = o) :
    σ.SameCycle o.out x :=
  Quotient.exact (o.out_eq.trans hx.symm)

theorem finitePermutationOrbitLength_eq {α : Type*} [Finite α]
    (σ : Equiv.Perm α) (o : finitePermutationOrbits σ) (x : α)
    (hx : Quotient.mk (Equiv.Perm.SameCycle.setoid σ) x = o) :
    minimalPeriod σ x = finitePermutationOrbitLength σ o := by
  obtain ⟨i, rfl⟩ := (finitePermutation_sameCycle_out σ o x hx).exists_nat_pow_eq
  exact minimalPeriod_apply_iterate (σ.injective.mem_periodicPts o.out) i

theorem finitePermutationOrbit_card {α : Type*} [Fintype α]
    (σ : Equiv.Perm α) (o : finitePermutationOrbits σ) :
    letI : DecidableEq (finitePermutationOrbits σ) := Classical.decEq _
    (univ.filter (fun x => Quotient.mk (Equiv.Perm.SameCycle.setoid σ) x = o)).card =
      finitePermutationOrbitLength σ o := by
  classical
  letI : DecidableEq (finitePermutationOrbits σ) := Classical.decEq _
  symm
  rw [← card_range (finitePermutationOrbitLength σ o)]
  refine card_bij (fun i _ => (σ ^ i) o.out) ?_ ?_ ?_
  · intro i _
    simp only [mem_filter, mem_univ, true_and]
    exact (Quotient.sound (Equiv.Perm.SameCycle.rfl.pow_right (n := i))).symm.trans
      o.out_eq
  · intro i hi j hj hij
    exact iterate_injOn_Iio_minimalPeriod (mem_range.mp hi) (mem_range.mp hj) hij
  · intro x hx
    obtain ⟨i, hi⟩ := (finitePermutation_sameCycle_out σ o x
      (mem_filter.mp hx).2).exists_nat_pow_eq
    refine ⟨i % finitePermutationOrbitLength σ o,
      mem_range.mpr (Nat.mod_lt _ (finitePermutationOrbitLength_pos σ o)), ?_⟩
    exact (iterate_mod_minimalPeriod_eq (n := i)).trans hi

theorem finitePermutationWeight_sameCycle {α : Type*} [Finite α]
    (σ : Equiv.Perm α) (w : ℕ → α → ℂ)
    (hinv : ∀ d x, (σ ^ d) x = x → w d (σ x) = w d x)
    (d : ℕ) {x y : α} (hxy : σ.SameCycle x y) (hx : (σ ^ d) x = x) :
    w d y = w d x := by
  obtain ⟨i, rfl⟩ := hxy.exists_nat_pow_eq
  clear hxy
  have hfixed (j : ℕ) : (σ ^ d) ((σ ^ j) x) = (σ ^ j) x := by
    change (σ ^ d * σ ^ j) x = (σ ^ j) x
    rw [← pow_add, Nat.add_comm, pow_add]
    change (σ ^ j) ((σ ^ d) x) = (σ ^ j) x
    rw [hx]
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [pow_succ']
      change w d (σ ((σ ^ i) x)) = w d x
      rw [hinv d _ (hfixed i), ih]

theorem finitePermutationWeight_fixed_sum {α : Type*} [Fintype α]
    (σ : Equiv.Perm α) (w : ℕ → α → ℂ)
    (hinv : ∀ d x, (σ ^ d) x = x → w d (σ x) = w d x)
    (hmul : ∀ d k x, (σ ^ d) x = x → w (d * k) x = w d x ^ k)
    (d : ℕ) :
    letI : DecidableEq α := Classical.decEq _
    letI : Fintype (finitePermutationOrbits σ) := Fintype.ofFinite _
    letI : DecidableEq (finitePermutationOrbits σ) := Classical.decEq _
    (∑ x ∈ univ.filter (fun x => (σ ^ d) x = x), w d x) =
      ∑ o : finitePermutationOrbits σ,
        if finitePermutationOrbitLength σ o ∣ d then
          (finitePermutationOrbitLength σ o : ℂ) *
            w (finitePermutationOrbitLength σ o) o.out ^
              (d / finitePermutationOrbitLength σ o)
        else 0 := by
  classical
  letI : Fintype (finitePermutationOrbits σ) := Fintype.ofFinite _
  letI : DecidableEq α := Classical.decEq _
  letI : DecidableEq (finitePermutationOrbits σ) := Classical.decEq _
  rw [sum_filter]
  rw [← Finset.sum_fiberwise univ
    (fun x => Quotient.mk (Equiv.Perm.SameCycle.setoid σ) x)
    (fun x => if (σ ^ d) x = x then w d x else 0)]
  apply sum_congr rfl
  intro o _
  have hfix (x : α) (hx : Quotient.mk (Equiv.Perm.SameCycle.setoid σ) x = o) :
      (σ ^ d) x = x ↔ finitePermutationOrbitLength σ o ∣ d := by
    change IsPeriodicPt σ d x ↔ _
    rw [isPeriodicPt_iff_minimalPeriod_dvd, finitePermutationOrbitLength_eq σ o x hx]
  by_cases hd : finitePermutationOrbitLength σ o ∣ d
  · rw [if_pos hd]
    have hrep : (σ ^ finitePermutationOrbitLength σ o) o.out = o.out :=
      iterate_minimalPeriod
    have hw : w d o.out = w (finitePermutationOrbitLength σ o) o.out ^
        (d / finitePermutationOrbitLength σ o) := by
      conv_lhs => rw [← Nat.mul_div_cancel' hd]
      exact hmul _ _ _ hrep
    calc
      _ = ∑ _x ∈ univ.filter
          (fun x => Quotient.mk (Equiv.Perm.SameCycle.setoid σ) x = o),
          w (finitePermutationOrbitLength σ o) o.out ^
            (d / finitePermutationOrbitLength σ o) := by
        apply sum_congr rfl
        intro x hx
        have hx' := (mem_filter.mp hx).2
        rw [if_pos ((hfix x hx').2 hd)]
        exact (finitePermutationWeight_sameCycle σ w hinv d
          (finitePermutation_sameCycle_out σ o x hx')
          ((hfix o.out o.out_eq).2 hd)).trans hw
      _ = _ := by rw [sum_const, nsmul_eq_mul, finitePermutationOrbit_card]
  · rw [if_neg hd]
    apply sum_eq_zero
    intro x hx
    rw [if_neg (fun h => hd ((hfix x (mem_filter.mp hx).2).1 h))]

end
end Tao2026
