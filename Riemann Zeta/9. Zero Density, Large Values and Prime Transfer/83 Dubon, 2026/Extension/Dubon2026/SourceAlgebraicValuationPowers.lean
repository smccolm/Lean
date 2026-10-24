import Mathlib.RingTheory.Valuation.Basic
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.Tactic

/-! DUB-17/18 -> Picard torsion injectivity -> Kummer power lifting ->
extending regular reductions. Algebraicity forces a positive power of an
extension value to lie in the base value group. Together with algebraically
closed constants and the original regular normalization, this discharges
normalization for the extending valuation. The native unique-maximum
valuation lemma supplies the polynomial argument. -/
namespace Dubon2026.SourceCurve
noncomputable section
open Polynomial
variable {F E Γ : Type*} [Field F] [Field E] [Algebra F E]
  [LinearOrderedCommGroupWithZero Γ]

theorem exists_equal_valued_terms_of_aeval_zero (v : Valuation E Γ)
    {x : E} (hx : x ≠ 0) {p : F[X]} (hp : p ≠ 0) (hpx : aeval x p = 0) :
    ∃ i j : ℕ, i < j ∧ p.coeff i ≠ 0 ∧ p.coeff j ≠ 0 ∧
      v (algebraMap F E (p.coeff i) * x ^ i) =
        v (algebraMap F E (p.coeff j) * x ^ j) := by
  classical
  let term := fun i => algebraMap F E (p.coeff i) * x ^ i
  have hsum : ∑ i ∈ p.support, term i = 0 := by
    simpa only [aeval_def, eval₂_eq_sum, Polynomial.sum_def] using hpx
  obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image p.support (fun i => v (term i))
    (support_nonempty.mpr hp)
  have hcoeff (i : ℕ) (hi : i ∈ p.support) : p.coeff i ≠ 0 := mem_support_iff.mp hi
  have hnonzero : v (term j) ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr (mul_ne_zero ((map_ne_zero_iff _ (algebraMap F E).injective).mpr
      (hcoeff j hj)) (pow_ne_zero _ hx))
  have hex : ∃ i ∈ p.support, i ≠ j ∧ v (term i) = v (term j) := by
    by_contra! h
    have he := v.map_sum_eq_of_lt hj (fun i hi =>
      lt_of_le_of_ne (hmax i (Finset.mem_sdiff.mp hi).1)
        (h i (Finset.mem_sdiff.mp hi).1 (by simpa using (Finset.mem_sdiff.mp hi).2)))
    rw [hsum, map_zero] at he
    exact hnonzero he.symm
  obtain ⟨i, hi, hij, heq⟩ := hex
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact ⟨i, j, hij, hcoeff i hi, hcoeff j hj, heq⟩
  · exact ⟨j, i, hji, hcoeff j hj, hcoeff i hi, heq.symm⟩

theorem exists_valuation_pow_eq_of_isIntegral (v : Valuation E Γ)
    {x : E} (hx : x ≠ 0) (hint : IsIntegral F x) :
    ∃ (n : ℕ) (a : F), 0 < n ∧ a ≠ 0 ∧ v x ^ n = v (algebraMap F E a) := by
  obtain ⟨i, j, hij, hi, hj, heq⟩ := exists_equal_valued_terms_of_aeval_zero v hx
    (minpoly.ne_zero hint) (minpoly.aeval F x)
  refine ⟨j - i, (minpoly F x).coeff i / (minpoly F x).coeff j,
    Nat.sub_pos_of_lt hij, div_ne_zero hi hj, ?_⟩
  have hvx : v x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
  have hvj : v (algebraMap F E ((minpoly F x).coeff j)) ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr ((map_ne_zero_iff _ (algebraMap F E).injective).mpr hj)
  rw [map_mul, map_mul, map_pow, map_pow] at heq
  have hp : v x ^ j = v x ^ (j - i) * v x ^ i := by
    rw [← pow_add, Nat.sub_add_cancel hij.le]
  rw [hp, ← mul_assoc] at heq
  have hcancel := mul_right_cancel₀ (pow_ne_zero i hvx) heq
  rw [map_div₀, map_div₀]
  apply (eq_div_iff hvj).mpr
  exact (mul_comm _ _).trans hcancel.symm

end
end Dubon2026.SourceCurve
