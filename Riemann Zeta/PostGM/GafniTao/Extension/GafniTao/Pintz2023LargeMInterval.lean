import GafniTao.Pintz2023LargeMFactor
import GafniTao.Pintz2023WeightedBlockComplex
import GafniTao.Pintz2023VariableLocalization

/-!
# Exact interval carried by the large-`m` factor

For a source interval `(A,B]`, the three literal restrictions in the
factorized inner sum are exactly one half-open natural interval.  This file
records the floor and division endpoints before any dyadic estimate is used.
-/

open Complex Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

def pintz2023LargeMLeftEndpoint (A d : ℕ) (R : ℝ) : ℕ :=
  max (A / d) (Nat.floor R)

def pintz2023LargeMRightEndpoint (B d : ℕ) : ℕ :=
  B / d

/-- The apparently filtered interval returned by the first localization is
literally one half-open interval; the minimum retains its right truncation. -/
theorem pintz2023LocalizedInterval_eq_Ioc (X Y r : ℕ) :
    pintz2023LocalizedInterval X Y r =
      Finset.Ioc (2 ^ r * X) (min (2 * (2 ^ r * X)) Y) := by
  have hpow : 1 ≤ 2 ^ r := one_le_pow₀ (by omega : (1 : ℕ) ≤ 2)
  have hXU : X ≤ 2 ^ r * X := by
    calc
      X = 1 * X := by omega
      _ ≤ 2 ^ r * X := Nat.mul_le_mul_right X hpow
  ext n
  simp only [pintz2023LocalizedInterval, Finset.mem_filter,
    Finset.mem_Ioc, le_min_iff]
  omega

theorem pintz2023_largeM_inner_index_set
    {A B d : ℕ} {R : ℝ} (hd : 0 < d) (hR : 0 ≤ R) :
    (Finset.Icc 1 (B + 1)).filter
        (fun m => d * m ∈ Finset.Ioc A B ∧ R < (m : ℝ)) =
      Finset.Ioc (pintz2023LargeMLeftEndpoint A d R)
        (pintz2023LargeMRightEndpoint B d) := by
  ext m
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc,
    pintz2023LargeMLeftEndpoint, pintz2023LargeMRightEndpoint,
    max_lt_iff]
  constructor
  · rintro ⟨⟨hmOne, hmB⟩, ⟨hA, hB⟩, hRm⟩
    have hAdiv : A / d < m := by
      rw [Nat.div_lt_iff_lt_mul hd]
      simpa [Nat.mul_comm] using hA
    have hRfloor : Nat.floor R < m :=
      (Nat.floor_lt hR).2 hRm
    have hmDiv : m ≤ B / d := by
      rw [Nat.le_div_iff_mul_le hd]
      simpa [Nat.mul_comm] using hB
    exact ⟨⟨hAdiv, hRfloor⟩, hmDiv⟩
  · rintro ⟨⟨hAdiv, hRfloor⟩, hmDiv⟩
    have hA : A < d * m := by
      rw [Nat.div_lt_iff_lt_mul hd] at hAdiv
      simpa [Nat.mul_comm] using hAdiv
    have hB : d * m ≤ B := by
      rw [Nat.le_div_iff_mul_le hd] at hmDiv
      simpa [Nat.mul_comm] using hmDiv
    have hRm : R < (m : ℝ) := (Nat.floor_lt hR).1 hRfloor
    have hmPos : 0 < m := by
      have : 0 ≤ Nat.floor R := Nat.zero_le _
      omega
    have hmLeB : m ≤ B := by
      calc
        m = 1 * m := by omega
        _ ≤ d * m := Nat.mul_le_mul_right m hd
        _ ≤ B := hB
    exact ⟨⟨hmPos, hmLeB.trans (Nat.le_succ B)⟩, ⟨hA, hB⟩, hRm⟩

theorem pintz2023LargeMInnerBlock_source_interval
    {A B d : ℕ} {R : ℝ} {s : ℂ}
    (hd : 0 < d) (hR : 0 ≤ R) :
    pintz2023LargeMInnerBlock B d (Finset.Ioc A B) R s =
      ∑ m ∈ Finset.Ioc (pintz2023LargeMLeftEndpoint A d R)
          (pintz2023LargeMRightEndpoint B d),
        (m : ℂ) ^ (-s) := by
  classical
  unfold pintz2023LargeMInnerBlock
  rw [← Finset.sum_filter]
  rw [pintz2023_largeM_inner_index_set hd hR]

theorem pintz2023LargeMInnerBlock_source_interval_eq_weighted
    {A B d : ℕ} {R xi t : ℝ}
    (hd : 0 < d) (hR : 0 ≤ R) :
    pintz2023LargeMInnerBlock B d (Finset.Ioc A B) R
        (((1 - xi : ℝ) : ℂ) + I * (t : ℂ)) =
      pintz2023ComplexWeightedBlock xi
        (pintz2023LargeMLeftEndpoint A d R)
        (pintz2023LargeMRightEndpoint B d) t := by
  rw [pintz2023LargeMInnerBlock_source_interval hd hR]
  rfl

theorem pintz2023LargeMInnerBlock_localized_eq_weighted
    {X Y r d : ℕ} {R xi t : ℝ}
    (hd : 0 < d) (hR : 0 ≤ R) :
    pintz2023LargeMInnerBlock (min (2 * (2 ^ r * X)) Y) d
        (pintz2023LocalizedInterval X Y r) R
        (((1 - xi : ℝ) : ℂ) + I * (t : ℂ)) =
      pintz2023ComplexWeightedBlock xi
        (pintz2023LargeMLeftEndpoint (2 ^ r * X) d R)
        (pintz2023LargeMRightEndpoint
          (min (2 * (2 ^ r * X)) Y) d) t := by
  rw [pintz2023LocalizedInterval_eq_Ioc]
  exact pintz2023LargeMInnerBlock_source_interval_eq_weighted hd hR

#print axioms pintz2023_largeM_inner_index_set
#print axioms pintz2023LocalizedInterval_eq_Ioc
#print axioms pintz2023LargeMInnerBlock_source_interval
#print axioms pintz2023LargeMInnerBlock_source_interval_eq_weighted
#print axioms pintz2023LargeMInnerBlock_localized_eq_weighted

end

end GafniTao
