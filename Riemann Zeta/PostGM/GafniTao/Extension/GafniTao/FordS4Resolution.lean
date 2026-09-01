import GafniTao.FordS4BoundaryDominance
import GafniTao.FordS4ToS6

/-!
# Ford Lemma 3.2: resolution of the `S₄` boundary alternative

The source hypothesis `32 s² M < Q`, together with `p ≤ 2M`, rules out a
boundary-dominant shifted residue box.  Consequently the complete `S₄`
collision count is at most twice its interior part, and hence at most twice
the exact equation-(3.6) collision count.
-/

namespace GafniTao

noncomputable section

theorem ford_sixteen_s_sq_le_div
    {s M Q p : ℕ} [NeZero p]
    (hpM : p ≤ 2 * M) (hQ : 32 * s ^ 2 * M < Q) :
    16 * s ^ 2 ≤ Q / p := by
  rw [Nat.le_div_iff_mul_le (NeZero.pos p)]
  calc
    (16 * s ^ 2) * p ≤ (16 * s ^ 2) * (2 * M) :=
      Nat.mul_le_mul_left (16 * s ^ 2) hpM
    _ = 32 * s ^ 2 * M := by ring
    _ ≤ Q := Nat.le_of_lt hQ

theorem ford_four_s_pow_le_div_pow
    {s M Q p : ℕ} [NeZero p]
    (hpM : p ≤ 2 * M) (hQ : 32 * s ^ 2 * M < Q) :
    (4 * s : ℝ) ^ (2 * s) ≤ ((Q / p : ℕ) : ℝ) ^ s := by
  have hbaseNat := ford_sixteen_s_sq_le_div hpM hQ
  have hbaseReal : (4 * s : ℝ) ^ 2 ≤ ((Q / p : ℕ) : ℝ) := by
    have heq : (4 * s : ℝ) ^ 2 = ((16 * s ^ 2 : ℕ) : ℝ) := by
      push_cast
      ring
    rw [heq]
    exact_mod_cast hbaseNat
  have hpow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (4 * s : ℝ) ^ 2)
    hbaseReal s
  calc
    (4 * s : ℝ) ^ (2 * s) = ((4 * s : ℝ) ^ 2) ^ s := by
      rw [pow_mul]
    _ ≤ ((Q / p : ℕ) : ℝ) ^ s := hpow

theorem fordS4Count_le_two_interior
    {k d T P p s Q q M : ℕ} [NeZero p]
    (Ψ : FordIntegerPolynomialSystem k d T) (hdk : d ≤ k)
    (c : ZMod p) (hs : 1 ≤ s)
    (hpM : p ≤ 2 * M) (hQ : 32 * s ^ 2 * M < Q) :
    fordS4Count (P := P) Ψ hdk s Q q c ≤
      2 * fordS4InteriorCount (P := P) Ψ hdk s Q q c := by
  let B := Nat.card (FordS4ShiftedBoundary (P := P) Ψ hdk s Q q c)
  let H := Nat.card (FordS4ShiftedInterior (P := P) Ψ hdk s Q q c)
  have hdecomp : fordS4Count (P := P) Ψ hdk s Q q c = H + B := by
    dsimp [H, B]
    rw [fordS4Count_eq_shiftedCount,
      fordS4Shifted_card_eq_interior_add_boundary]
  by_cases hBH : B ≤ H
  · rw [hdecomp, fordS4InteriorCount_eq_shiftedInterior]
    dsimp [H] at hBH ⊢
    omega
  · have hHB : H < B := Nat.lt_of_not_ge hBH
    have hstrict := fordS4_strict_upper_of_interior_lt_boundary
      (P := P) (p := p) Ψ hdk c hs (by simpa [H, B] using hHB)
    let I := fordPolynomialCollisionCount (P := P) (p := p) Ψ hdk
    let S := fordS4Count (P := P) Ψ hdk s Q q c
    have hIposNat : 0 < I := by
      by_contra hI
      have hIzero : I = 0 := Nat.eq_zero_of_not_pos hI
      have hSnonneg : (0 : ℝ) ≤ (S : ℝ) := by positivity
      have hstrict' : (S : ℝ) <
          (4 * s : ℝ) ^ (2 * s) * (I : ℝ) := by
        simpa [S, I] using hstrict
      rw [hIzero, Nat.cast_zero, mul_zero] at hstrict'
      linarith
    have hdiagNat := fordS4_diagonal_lower
      (P := P) (s := s) (Q := Q) (q := q) Ψ hdk c
    have hdiag : (I : ℝ) * ((Q / p : ℕ) : ℝ) ^ s ≤ (S : ℝ) := by
      exact_mod_cast hdiagNat
    have hstrict' : (S : ℝ) <
        (4 * s : ℝ) ^ (2 * s) * (I : ℝ) := by
      simpa [S, I] using hstrict
    have hproduct : (I : ℝ) * ((Q / p : ℕ) : ℝ) ^ s <
        (I : ℝ) * (4 * s : ℝ) ^ (2 * s) := by
      calc
        (I : ℝ) * ((Q / p : ℕ) : ℝ) ^ s ≤ (S : ℝ) := hdiag
        _ < (4 * s : ℝ) ^ (2 * s) * (I : ℝ) := hstrict'
        _ = (I : ℝ) * (4 * s : ℝ) ^ (2 * s) := by ring
    have hbaseStrict : ((Q / p : ℕ) : ℝ) ^ s <
        (4 * s : ℝ) ^ (2 * s) :=
      lt_of_mul_lt_mul_left hproduct (by positivity)
    have hbaseLower := ford_four_s_pow_le_div_pow hpM hQ
    exact False.elim ((not_lt_of_ge hbaseLower) hbaseStrict)

theorem fordS4Count_le_two_S6
    {k d T P p s Q q r M : ℕ} [NeZero p]
    (Ψ : FordIntegerPolynomialSystem k d T) (hdk : d ≤ k)
    (c : ZMod p) (hs : 1 ≤ s) (hr : 0 < r)
    (hpM : p ≤ 2 * M) (hQ : 32 * s ^ 2 * M < Q) :
    fordS4Count (P := P) Ψ hdk s Q q c ≤
      2 * fordS6Count Ψ (fordS4TranslationScale q c)
        s P (Q / p) p q r hdk := by
  calc
    fordS4Count (P := P) Ψ hdk s Q q c ≤
        2 * fordS4InteriorCount (P := P) Ψ hdk s Q q c :=
      fordS4Count_le_two_interior Ψ hdk c hs hpM hQ
    _ ≤ 2 * fordS6Count Ψ (fordS4TranslationScale q c)
        s P (Q / p) p q r hdk :=
      Nat.mul_le_mul_left 2 (fordS4InteriorCount_le_S6 Ψ hdk hr c)

#print axioms ford_sixteen_s_sq_le_div
#print axioms ford_four_s_pow_le_div_pow
#print axioms fordS4Count_le_two_interior
#print axioms fordS4Count_le_two_S6

end

end GafniTao
