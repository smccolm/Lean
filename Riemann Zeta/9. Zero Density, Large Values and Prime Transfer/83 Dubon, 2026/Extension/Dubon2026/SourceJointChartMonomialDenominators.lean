import Dubon2026.SourceJointChartGoodPolynomials

/-! DUB-17/18 -> Kummer genus inequality -> constants in the common residue
chart. The chart overlap permits denominators whose reduction is a single
nonzero monomial. Products and reflection preserve that exact condition.
The degree-zero condition is the previously proved `IsGood` predicate.
Adapted from Apache-2.0 FLT commit 6e837e75355538c7f80bab5b956861e86c4eacc2. -/
namespace Dubon2026.SourceCurve.RegularProlongation.JointChartConstants
noncomputable section
open Polynomial

variable {L : Type*} [Field L] (A : ValuationSubring L)

/-- A polynomial whose reduction is a nonzero monomial of degree `d`. -/
def IsGoodAt (d : ℕ) (t : L[X]) : Prop :=
  A.valuation (t.coeff d) = 1 ∧ ∀ j, j ≠ d → A.valuation (t.coeff j) < 1

namespace IsGoodAt

variable {A}

theorem valuation_le {d : ℕ} {t : L[X]} (ht : IsGoodAt A d t) (j : ℕ) :
    A.valuation (t.coeff j) ≤ 1 := by
  by_cases hj : j = d
  · rw [hj, ht.1]
  · exact (ht.2 j hj).le

theorem coeff_mem {d : ℕ} {t : L[X]} (ht : IsGoodAt A d t) (j : ℕ) : t.coeff j ∈ A :=
  (A.valuation_le_one_iff _).mp (ht.valuation_le j)

theorem mul {d d' : ℕ} {t s : L[X]} (ht : IsGoodAt A d t) (hs : IsGoodAt A d' s) :
    IsGoodAt A (d + d') (t * s) := by
  classical
  have hlt : ∀ x : ℕ × ℕ, x ≠ (d, d') → A.valuation (t.coeff x.1 * s.coeff x.2) < 1 := by
    rintro ⟨i, j⟩ hx
    rw [map_mul]
    by_cases hi : i = d
    · have hj : j ≠ d' := fun hj => hx (by rw [hi, hj])
      calc A.valuation (t.coeff i) * A.valuation (s.coeff j)
          ≤ 1 * A.valuation (s.coeff j) := by gcongr; exact ht.valuation_le _
        _ < 1 := by rw [one_mul]; exact hs.2 _ hj
    · calc A.valuation (t.coeff i) * A.valuation (s.coeff j)
          ≤ A.valuation (t.coeff i) * 1 := by gcongr; exact hs.valuation_le _
        _ < 1 := by rw [mul_one]; exact ht.2 _ hi
  refine ⟨?_, fun n hn => ?_⟩
  · have hmem : (d, d') ∈ Finset.HasAntidiagonal.antidiagonal (d + d') := Finset.HasAntidiagonal.mem_antidiagonal.mpr rfl
    rw [coeff_mul, ← Finset.add_sum_erase _ _ hmem]
    have hmain : A.valuation (t.coeff d * s.coeff d') = 1 := by
      rw [map_mul, ht.1, hs.1, one_mul]
    have hrest : A.valuation (∑ x ∈ (Finset.HasAntidiagonal.antidiagonal (d + d')).erase (d, d'),
        t.coeff x.1 * s.coeff x.2) < 1 :=
      Valuation.map_sum_lt _ one_ne_zero fun x hx => hlt x (Finset.mem_erase.mp hx).1
    rw [Valuation.map_add_eq_of_lt_left _ (by rw [hmain]; exact hrest), hmain]
  · rw [coeff_mul]
    refine Valuation.map_sum_lt _ one_ne_zero fun x hx => hlt x ?_
    rintro rfl
    exact hn (Finset.HasAntidiagonal.mem_antidiagonal.mp hx).symm

theorem X_pow (m : ℕ) : IsGoodAt A m ((X : L[X]) ^ m) := by
  refine ⟨by rw [coeff_X_pow, if_pos rfl, map_one], fun j hj => ?_⟩
  rw [coeff_X_pow, if_neg hj, map_zero]
  exact zero_lt_one

theorem one : IsGoodAt A 0 (1 : L[X]) := by
  simpa using X_pow (A := A) 0

theorem reflect {t : L[X]} (ht : IsGoodAt A 0 t) (N : ℕ) : IsGoodAt A N (reflect N t) := by
  refine ⟨?_, fun j hj => ?_⟩
  · rw [coeff_reflect, revAt_le le_rfl, Nat.sub_self, ht.1]
  · rw [coeff_reflect]
    apply ht.2
    intro h0
    apply hj
    have := congrArg (revAt N) h0
    rwa [revAt_invol, revAt_zero] at this

end IsGoodAt

variable {A}
variable {F : Type*} [Field F] [Algebra L F]

theorem aeval_reflect_eq {g : F} (hg : g ≠ 0) (t : L[X]) {N : ℕ} (hN : t.natDegree ≤ N) :
    aeval g (Polynomial.reflect N t) = aeval g⁻¹ t * g ^ N := by
  haveI : Invertible g⁻¹ := invertibleOfNonzero (inv_ne_zero hg)
  have h := eval₂_reflect_mul_pow (algebraMap L F) g⁻¹ N t hN
  rw [invOf_eq_inv, inv_inv] at h
  rw [aeval_def, aeval_def, ← h, mul_assoc, ← mul_pow, inv_mul_cancel₀ hg, one_pow, mul_one]


end
end Dubon2026.SourceCurve.RegularProlongation.JointChartConstants
