import Dubon2026.RootMultiplicityMapGcd
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # Removing repeated roots by division by the derivative GCD -/

namespace Dubon2026

open Polynomial

noncomputable section

/-- The actual squarefree quotient of a real polynomial. -/
def derivativeRootQuotient (P : ℝ[X]) : ℝ[X] := P / gcd P P.derivative

theorem derivativeRootQuotient_ne_zero {P : ℝ[X]} (hP : P ≠ 0) :
    derivativeRootQuotient P ≠ 0 := left_div_gcd_ne_zero hP

theorem derivativeRootQuotient_rootMultiplicity {P : ℝ[X]} (hP : P ≠ 0) (t : ℝ) :
    (derivativeRootQuotient P).rootMultiplicity t = if P.IsRoot t then 1 else 0 := by
  simpa only [Polynomial.map_id, derivativeRootQuotient] using
    rootMultiplicity_map_derivativeQuotient (RingHom.id ℝ) hP t

/-- All complex roots of the quotient are simple, hence it is separable over the reals. -/
theorem derivativeRootQuotient_separable {P : ℝ[X]} (hP : P ≠ 0) :
    (derivativeRootQuotient P).Separable := by
  apply (Polynomial.nodup_aroots_iff_of_splits
    (K := ℂ) (derivativeRootQuotient_ne_zero hP) (IsAlgClosed.splits _)).mp
  rw [Polynomial.aroots_def, Multiset.nodup_iff_count_le_one]
  intro t
  rw [Polynomial.count_roots]
  change ((P / gcd P P.derivative).map (algebraMap ℝ ℂ)).rootMultiplicity t ≤ 1
  rw [rootMultiplicity_map_derivativeQuotient (algebraMap ℝ ℂ) hP]
  split_ifs <;> omega

theorem derivativeRootQuotient_roots_toFinset {P : ℝ[X]} (hP : P ≠ 0) :
    (derivativeRootQuotient P).roots.toFinset = P.roots.toFinset := by
  classical
  ext t
  simp only [Multiset.mem_toFinset, ← Multiset.count_pos, Polynomial.count_roots,
    derivativeRootQuotient_rootMultiplicity hP]
  rw [Polynomial.rootMultiplicity_pos hP]
  by_cases hr : P.IsRoot t <;>
    simp only [hr, ↓reduceIte, Nat.zero_lt_one, lt_self_iff_false]

theorem distinct_count_eq_derivativeRootQuotient_count {P : ℝ[X]} (hP : P ≠ 0) (l u : ℝ) :
    realPolynomialDistinctRootCount P l u =
      realPolynomialRootCount (derivativeRootQuotient P) l u := by
  classical
  unfold realPolynomialDistinctRootCount realPolynomialRootCount
  rw [← derivativeRootQuotient_roots_toFinset hP, ← Multiset.toFinset_filter,
    Multiset.toFinset_card_of_nodup
      ((Polynomial.nodup_roots (derivativeRootQuotient_separable hP)).filter _)]

end

end Dubon2026
