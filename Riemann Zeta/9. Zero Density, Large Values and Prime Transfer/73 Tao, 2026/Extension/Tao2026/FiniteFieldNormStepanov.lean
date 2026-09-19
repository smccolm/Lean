import Tao2026.PolynomialStepanovSqrtParameters
import Tao2026.FiniteCharacterFiberCancellation

/-!
# Explicit Stepanov bounds for finite-field norm character sums

The norm exponent identifies the relevant fibers with the polynomial power
fibers counted by the auxiliary construction. Character cancellation and
translation give a square-root bound at any simple root, uniformly in the
extension size above an explicit threshold.
-/

namespace Tao2026
open Finset Polynomial
open scoped BigOperators
noncomputable section

theorem nat_stepanov_norm_exponent_bounds
    (e d Q : ℕ) (he : 0 < e) (hlarge : 16 * e ^ 2 * (e * d + 1) ^ 2 ≤ Q) :
    2 ≤ (Q - 1) / e ∧ e * ((Q - 1) / e) ≤ Q ∧ Q ≤ e * ((Q - 1) / e + 1) := by
  have heSq : e ≤ e ^ 2 := by nlinarith
  have hAe : 0 < (e * d + 1) ^ 2 := by positivity
  have h16 : 16 * e ≤ Q := (Nat.mul_le_mul_left 16 heSq).trans
    ((Nat.le_mul_of_pos_right _ hAe).trans hlarge)
  have hh : 2 ≤ (Q - 1) / e := (Nat.le_div_iff_mul_le he).2 (by omega)
  have hdiv := Nat.mod_add_div (Q - 1) e
  have hmod := Nat.mod_lt (Q - 1) he
  refine ⟨hh, ?_, ?_⟩
  · omega
  · nlinarith [Nat.sub_add_cancel (show 1 ≤ Q by omega)]

theorem finiteField_norm_polynomial_fiber_card_le_sqrt_of_simple_root
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (K : Type*) [Field K] [Fintype K] [Algebra (ZMod p) K] [ExpChar K p]
    (n : ℕ) (hcardK : Fintype.card K = p ^ n)
    (g : K[X]) (hg : g ≠ 0) (hroot : g.rootMultiplicity 0 = 1)
    (hlarge : 16 * (p - 1) ^ 2 * ((p - 1) * g.natDegree + 1) ^ 2 ≤ p ^ n)
    (b : ZMod p) (hb : b ≠ 0) :
    ((univ.filter fun x : K => Algebra.norm (ZMod p) (g.eval x) = b).card : ℝ) ≤
      (p : ℝ) ^ n / (p - 1 : ℕ) +
        4 * ((p - 1 : ℕ) * (g.natDegree : ℝ) + 1) ^ 2 * Real.sqrt ((p : ℝ) ^ n) := by
  classical
  have he : 0 < p - 1 := Nat.sub_pos_of_lt (Fact.out : p.Prime).one_lt
  obtain ⟨hh, hQ, hround⟩ := nat_stepanov_norm_exponent_bounds (p - 1) g.natDegree (p ^ n) he hlarge
  let T := univ.filter fun x : K => Algebra.norm (ZMod p) (g.eval x) = b
  have hT : ∀ x ∈ T, x ^ p ^ n = x ∧ g.eval x ≠ 0 ∧
      g.eval x ^ ((p ^ n - 1) / (p - 1)) = algebraMap (ZMod p) K b := by
    intro x hx
    have hnorm : Algebra.norm (ZMod p) (g.eval x) = b := (mem_filter.mp hx).2
    refine ⟨by rw [← hcardK]; exact FiniteField.pow_card x, ?_, ?_⟩
    · exact Algebra.norm_ne_zero_iff.1 (hnorm ▸ hb)
    · have heq := FiniteField.algebraMap_norm_eq_pow (K := ZMod p) (x := g.eval x)
      rw [hnorm] at heq
      simpa only [Nat.card_eq_fintype_card, hcardK, ZMod.card] using heq.symm
  have hbound := polynomialStepanov_card_le_sqrt_of_simple_root p g hg hroot (p - 1)
    ((p ^ n - 1) / (p - 1)) n (algebraMap (ZMod p) K b) he hh hQ hround hlarge T hT
  have heR : (0 : ℝ) < (p - 1 : ℕ) := by exact_mod_cast he
  apply (mul_le_mul_iff_left₀ heR).1
  convert hbound using 1
  field_simp

theorem finiteField_norm_polynomial_sum_le_sqrt_of_simple_root
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (K : Type*) [Field K] [Fintype K] [Algebra (ZMod p) K] [ExpChar K p]
    (n : ℕ) (hcardK : Fintype.card K = p ^ n)
    (g : K[X]) (hg : g ≠ 0) (hroot : g.rootMultiplicity 0 = 1)
    (χ : MulChar (ZMod p) ℂ) (hχ : χ ≠ 1)
    (hlarge : 16 * (p - 1) ^ 2 * ((p - 1) * g.natDegree + 1) ^ 2 ≤ p ^ n) :
    ‖∑ x : K, χ (Algebra.norm (ZMod p) (g.eval x))‖ ≤
      (4 * (p - 1 : ℕ) * ((p - 1 : ℕ) * (g.natDegree : ℝ) + 1) ^ 2 + g.natDegree) *
        Real.sqrt ((p : ℝ) ^ n) := by
  classical
  let U : ℝ := (p : ℝ) ^ n / (p - 1 : ℕ) +
    4 * ((p - 1 : ℕ) * (g.natDegree : ℝ) + 1) ^ 2 * Real.sqrt ((p : ℝ) ^ n)
  have hbound := prime_mulChar_sum_norm_le_of_fiber_card_upper p
    (fun x : K => Algebra.norm (ZMod p) (g.eval x)) χ hχ U
    (finiteField_norm_polynomial_fiber_card_le_sqrt_of_simple_root p K n hcardK g hg hroot hlarge)
  have hzeros : (univ.filter fun x : K => Algebra.norm (ZMod p) (g.eval x) = 0).card ≤ g.natDegree := by
    apply Polynomial.card_le_degree_of_subset_roots
    intro x hx
    exact (Polynomial.mem_roots hg).2 (Algebra.norm_eq_zero_iff.1 (mem_filter.mp hx).2)
  have hzerosR : ((univ.filter fun x : K => Algebra.norm (ZMod p) (g.eval x) = 0).card : ℝ) ≤ g.natDegree :=
    by exact_mod_cast hzeros
  have heR : (0 : ℝ) < (p - 1 : ℕ) := by exact_mod_cast Nat.sub_pos_of_lt (Fact.out : p.Prime).one_lt
  have hcancel : (p - 1 : ℕ) * U - (p : ℝ) ^ n =
      4 * (p - 1 : ℕ) * ((p - 1 : ℕ) * (g.natDegree : ℝ) + 1) ^ 2 * Real.sqrt ((p : ℝ) ^ n) := by
    dsimp [U]
    field_simp
    ring
  rw [hcardK, Nat.cast_pow, hcancel] at hbound
  have hsqrt : 1 ≤ Real.sqrt ((p : ℝ) ^ n) := by
    apply Real.one_le_sqrt.2
    exact one_le_pow₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt.le)
  nlinarith [(Nat.cast_nonneg g.natDegree : (0 : ℝ) ≤ g.natDegree)]

theorem finiteField_polynomial_weight_sum_taylor_eq
    {K : Type*} [Field K] [Fintype K] (w : K → ℂ) (g : K[X]) (a : K) :
    (∑ x : K, w ((taylor a g).eval x)) = ∑ x : K, w (g.eval x) := by
  simp only [taylor_apply, eval_comp, eval_add, eval_X, eval_C]
  exact Equiv.sum_comp (Equiv.addRight a) (fun x => w (g.eval x))

theorem finiteField_norm_polynomial_sum_le_sqrt_of_rootMultiplicity_one
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (K : Type*) [Field K] [Fintype K] [Algebra (ZMod p) K] [ExpChar K p]
    (n : ℕ) (hcardK : Fintype.card K = p ^ n)
    (g : K[X]) (hg : g ≠ 0) (a : K) (hroot : g.rootMultiplicity a = 1)
    (χ : MulChar (ZMod p) ℂ) (hχ : χ ≠ 1)
    (hlarge : 16 * (p - 1) ^ 2 * ((p - 1) * g.natDegree + 1) ^ 2 ≤ p ^ n) :
    ‖∑ x : K, χ (Algebra.norm (ZMod p) (g.eval x))‖ ≤
      (4 * (p - 1 : ℕ) * ((p - 1 : ℕ) * (g.natDegree : ℝ) + 1) ^ 2 + g.natDegree) *
        Real.sqrt ((p : ℝ) ^ n) := by
  have ht : taylor a g ≠ 0 := by
    intro ht0
    apply hg
    exact (taylorEquiv a).injective (by simpa using ht0)
  have hroot' : (taylor a g).rootMultiplicity 0 = 1 := by
    rw [taylor_apply, ← rootMultiplicity_eq_rootMultiplicity]
    exact hroot
  have h := finiteField_norm_polynomial_sum_le_sqrt_of_simple_root p K n hcardK
    (taylor a g) ht hroot' χ hχ (by simpa only [natDegree_taylor] using hlarge)
  rw [finiteField_polynomial_weight_sum_taylor_eq (fun z => χ (Algebra.norm (ZMod p) z)) g a] at h
  simpa only [natDegree_taylor] using h

end
end Tao2026
