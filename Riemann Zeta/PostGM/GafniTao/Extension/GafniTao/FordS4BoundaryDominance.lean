import GafniTao.FordOddHolder

/-!
# Ford Lemma 3.2: exclusion of a boundary-dominant `S₄`

If the shifted boundary count strictly exceeds the interior count, the exact
boundary cover and powered Hölder inequality give Ford's strict upper bound
for `S₄`.  Strictness is retained because it is what handles the possible
floor equality `Q / p = 16 s²` in the final arithmetic contradiction.
-/

namespace GafniTao

noncomputable section

theorem fordS4_strict_upper_of_interior_lt_boundary
    {k d T P p s Q q : ℕ} [NeZero p]
    (Ψ : FordIntegerPolynomialSystem k d T) (hdk : d ≤ k)
    (c : ZMod p) (hs : 1 ≤ s)
    (hdom : Nat.card (FordS4ShiftedInterior (P := P) Ψ hdk s Q q c) <
      Nat.card (FordS4ShiftedBoundary (P := P) Ψ hdk s Q q c)) :
    (fordS4Count (P := P) Ψ hdk s Q q c : ℝ) <
      (4 * s : ℝ) ^ (2 * s) *
        (fordPolynomialCollisionCount (P := P) (p := p) Ψ hdk : ℝ) := by
  let S : ℝ := fordS4Count (P := P) Ψ hdk s Q q c
  let I : ℝ := fordPolynomialCollisionCount (P := P) (p := p) Ψ hdk
  let O : ℝ := fordS4OddIntegral (P := P) Ψ hdk s Q q c
  have hdecompNat : fordS4Count (P := P) Ψ hdk s Q q c =
      Nat.card (FordS4ShiftedInterior (P := P) Ψ hdk s Q q c) +
        Nat.card (FordS4ShiftedBoundary (P := P) Ψ hdk s Q q c) := by
    rw [fordS4Count_eq_shiftedCount,
      fordS4Shifted_card_eq_interior_add_boundary]
  have hdecomp : S =
      (Nat.card (FordS4ShiftedInterior (P := P) Ψ hdk s Q q c) : ℝ) +
        (Nat.card (FordS4ShiftedBoundary (P := P) Ψ hdk s Q q c) : ℝ) := by
    dsimp [S]
    rw [hdecompNat]
    push_cast
    rfl
  have hboundary := ford_shifted_boundary_card_le_two_s_odd
    (P := P) (Q := Q) (q := q) Ψ hdk c hs
  have hSodd : S < (4 * s : ℝ) * O := by
    have hstrict : S < 2 *
        (Nat.card (FordS4ShiftedBoundary (P := P) Ψ hdk s Q q c) : ℝ) := by
      rw [hdecomp]
      exact_mod_cast (by omega :
        Nat.card (FordS4ShiftedInterior (P := P) Ψ hdk s Q q c) +
          Nat.card (FordS4ShiftedBoundary (P := P) Ψ hdk s Q q c) <
            2 * Nat.card (FordS4ShiftedBoundary (P := P) Ψ hdk s Q q c))
    calc
      S < 2 * (Nat.card (FordS4ShiftedBoundary (P := P)
          Ψ hdk s Q q c) : ℝ) := hstrict
      _ ≤ 2 * ((2 : ℝ) * s * O) :=
        mul_le_mul_of_nonneg_left hboundary (by norm_num)
      _ = (4 * s : ℝ) * O := by ring
  have hSpos : 0 < S := by
    have hboundaryPos : 0 <
        Nat.card (FordS4ShiftedBoundary (P := P) Ψ hdk s Q q c) :=
      lt_of_le_of_lt (Nat.zero_le _) hdom
    rw [hdecomp]
    exact add_pos_of_nonneg_of_pos (by positivity) (by exact_mod_cast hboundaryPos)
  have hholder : O ^ (2 * s) ≤ S ^ (2 * s - 1) * I := by
    exact ford_odd_integral_pow_le Ψ hdk c hs
  have hpowStrict : S ^ (2 * s) < ((4 * s : ℝ) * O) ^ (2 * s) :=
    pow_lt_pow_left₀ hSodd hSpos.le (by omega)
  have hmain : S ^ (2 * s) <
      (4 * s : ℝ) ^ (2 * s) * (S ^ (2 * s - 1) * I) := by
    calc
      S ^ (2 * s) < ((4 * s : ℝ) * O) ^ (2 * s) := hpowStrict
      _ = (4 * s : ℝ) ^ (2 * s) * O ^ (2 * s) := by rw [mul_pow]
      _ ≤ (4 * s : ℝ) ^ (2 * s) * (S ^ (2 * s - 1) * I) :=
        mul_le_mul_of_nonneg_left hholder (by positivity)
  have hpowSplit : S ^ (2 * s) = S ^ (2 * s - 1) * S := by
    calc
      S ^ (2 * s) = S ^ ((2 * s - 1) + 1) := by congr 1; omega
      _ = S ^ (2 * s - 1) * S := by rw [pow_succ]
  rw [hpowSplit] at hmain
  have hfactor : (4 * s : ℝ) ^ (2 * s) *
      (S ^ (2 * s - 1) * I) =
      S ^ (2 * s - 1) * ((4 * s : ℝ) ^ (2 * s) * I) := by ring
  rw [hfactor] at hmain
  exact lt_of_mul_lt_mul_left hmain (pow_pos hSpos (2 * s - 1)).le

#print axioms fordS4_strict_upper_of_interior_lt_boundary

end

end GafniTao
