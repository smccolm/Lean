import RiemannZeta.GuthMaynard.HughesYoungProductTruncation

open Complex Filter MeasureTheory Set Topology
open scoped BigOperators Interval Topology

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# Square truncation of the high Hughes--Young opening

The DFI consumer is rectangular.  This file therefore converts the
arbitrary-high-line product truncation into the exact square used by the
finite four-index expansion.  The complement of the square is contained in
the already controlled product tail.
-/

/-- The `hughesYoungHighPairSquare` definition used by the source-facing construction in `HughesYoungSquareTruncation`. -/
noncomputable def hughesYoungHighPairSquare
    (q : ℕ) (t u : ℝ) (M : ℕ) : ℂ :=
  ∑ p ∈ Finset.Icc (1, 1) (M, M),
    hughesYoungRightPairTerm t (2 * q) u p

/-- The `hughesYoungHighPairSquareTail` definition used by the source-facing construction in `HughesYoungSquareTruncation`. -/
noncomputable def hughesYoungHighPairSquareTail
    (q : ℕ) (t u : ℝ) (M : ℕ) : ℂ :=
  ∑' p : ℕ × ℕ,
    if M < p.1 ∨ M < p.2 then
      hughesYoungRightPairTerm t (2 * q) u p
    else 0

theorem hughesYoungRightPairTerm_eq_zero_of_fst_eq_zero
    (t c u : ℝ) {p : ℕ × ℕ} (hp : p.1 = 0) :
    hughesYoungRightPairTerm t c u p = 0 := by
  simp [hughesYoungRightPairTerm, hp, divisorDirichletTerm]

theorem hughesYoungRightPairTerm_eq_zero_of_snd_eq_zero
    (t c u : ℝ) {p : ℕ × ℕ} (hp : p.2 = 0) :
    hughesYoungRightPairTerm t c u p = 0 := by
  simp [hughesYoungRightPairTerm, hp, divisorDirichletTerm]

theorem summable_hughesYoungHighPairSquareTail
    {q : ℕ} (hq : 0 < q) (t u : ℝ) (M : ℕ) :
    Summable (fun p : ℕ × ℕ =>
      if M < p.1 ∨ M < p.2 then
        hughesYoungRightPairTerm t (2 * q) u p
      else 0) := by
  have hfull : Summable (hughesYoungRightPairTerm t (2 * q) u) :=
    summable_hughesYoungRightPairTerm t u (by
      have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
      linarith)
  refine (Summable.indicator hfull
    {p : ℕ × ℕ | M < p.1 ∨ M < p.2}).congr ?_
  intro p
  simp only [Set.indicator_apply, Set.mem_setOf_eq]

theorem tsum_hughesYoungRightPairTerm_eq_square_add_tail
    {q M : ℕ} (hq : 0 < q) (t u : ℝ) :
    (∑' p : ℕ × ℕ, hughesYoungRightPairTerm t (2 * q) u p) =
      hughesYoungHighPairSquare q t u M +
        hughesYoungHighPairSquareTail q t u M := by
  classical
  have htail := summable_hughesYoungHighPairSquareTail hq t u M
  rw [show hughesYoungHighPairSquare q t u M =
      ∑' p : ℕ × ℕ,
        if p ∈ Finset.Icc (1, 1) (M, M) then
          hughesYoungRightPairTerm t (2 * q) u p else 0 by
    unfold hughesYoungHighPairSquare
    symm
    calc
      (∑' p : ℕ × ℕ,
          if p ∈ Finset.Icc (1, 1) (M, M) then
            hughesYoungRightPairTerm t (2 * q) u p else 0) =
          ∑ p ∈ Finset.Icc (1, 1) (M, M),
            (if p ∈ Finset.Icc (1, 1) (M, M) then
              hughesYoungRightPairTerm t (2 * q) u p else 0) := by
        apply tsum_eq_sum
        intro p hp
        simp [hp]
      _ = ∑ p ∈ Finset.Icc (1, 1) (M, M),
          hughesYoungRightPairTerm t (2 * q) u p := by
        apply Finset.sum_congr rfl
        intro p hp
        simp [hp]
    ]
  have hlow : Summable (fun p : ℕ × ℕ =>
      if p ∈ Finset.Icc (1, 1) (M, M) then
        hughesYoungRightPairTerm t (2 * q) u p else 0) := by
    apply summable_of_ne_finset_zero (s := Finset.Icc (1, 1) (M, M))
    intro p hp
    simp [hp]
  unfold hughesYoungHighPairSquareTail
  rw [← hlow.tsum_add htail]
  apply tsum_congr
  intro p
  rcases p with ⟨m, n⟩
  by_cases hm0 : m = 0
  · simp [hm0, hughesYoungRightPairTerm_eq_zero_of_fst_eq_zero]
  by_cases hn0 : n = 0
  · simp [hn0, hughesYoungRightPairTerm_eq_zero_of_snd_eq_zero]
  have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm0
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
  by_cases hm : m ≤ M
  · by_cases hn : n ≤ M
    · simp [hm1, hn1, hm, hn]
    · have hn' : M < n := Nat.lt_of_not_ge hn
      simp [hm1, hn1, hm, hn, hn']
  · have hm' : M < m := Nat.lt_of_not_ge hm
    simp [hm1, hn1, hm, hm']

theorem norm_hughesYoungHighPairSquareTail_le_productTail
    {q M : ℕ} (hq : 0 < q) (hM : 0 < M) (t u : ℝ) :
    ‖hughesYoungHighPairSquareTail q t u M‖ ≤
      ∑' p : ℕ × ℕ,
        ‖if (M : ℝ) < (p.1 : ℝ) * p.2 then
            hughesYoungRightPairTerm t (2 * q) u p else 0‖ := by
  have hfullNorm : Summable (fun p : ℕ × ℕ =>
      ‖hughesYoungRightPairTerm t (2 * q) u p‖) :=
    (summable_hughesYoungRightPairTerm t u (by
      have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
      linarith)).norm
  have hleftNorm : Summable (fun p : ℕ × ℕ =>
      ‖if M < p.1 ∨ M < p.2 then
          hughesYoungRightPairTerm t (2 * q) u p else 0‖) := by
    refine (Summable.indicator hfullNorm
      {p : ℕ × ℕ | M < p.1 ∨ M < p.2}).congr ?_
    intro p
    by_cases hp : M < p.1 ∨ M < p.2 <;>
      simp [hp]
  have hη : (1 / 4 : ℝ) < 2 * (q : ℝ) - 1 / 2 := by
    have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  have hrightNorm : Summable (fun p : ℕ × ℕ =>
      ‖if (M : ℝ) < (p.1 : ℝ) * p.2 then
          hughesYoungRightPairTerm t (2 * q) u p else 0‖) :=
    summable_norm_hughesYoungRightPairTerm_high_tail
      (show 0 < (M : ℝ) by exact_mod_cast hM)
      (by positivity : (0 : ℝ) < 1 / 4) hη
  unfold hughesYoungHighPairSquareTail
  calc
    ‖∑' p : ℕ × ℕ,
        if M < p.1 ∨ M < p.2 then
          hughesYoungRightPairTerm t (2 * q) u p else 0‖ ≤
        ∑' p : ℕ × ℕ,
          ‖if M < p.1 ∨ M < p.2 then
              hughesYoungRightPairTerm t (2 * q) u p else 0‖ :=
      norm_tsum_le_tsum_norm
        hleftNorm
    _ ≤ ∑' p : ℕ × ℕ,
        ‖if (M : ℝ) < (p.1 : ℝ) * p.2 then
            hughesYoungRightPairTerm t (2 * q) u p else 0‖ := by
      apply Summable.tsum_le_tsum
      · intro p
        rcases p with ⟨m, n⟩
        by_cases hm0 : m = 0
        · simp [hm0, hughesYoungRightPairTerm_eq_zero_of_fst_eq_zero]
        by_cases hn0 : n = 0
        · simp [hn0, hughesYoungRightPairTerm_eq_zero_of_snd_eq_zero]
        have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm0
        have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
        by_cases hout : M < m ∨ M < n
        · have hprodNat : M < m * n := by
            rcases hout with hm | hn
            · exact lt_of_lt_of_le hm
                (Nat.le_mul_of_pos_right m (Nat.zero_lt_of_lt hn1))
            · exact lt_of_lt_of_le hn
                (Nat.le_mul_of_pos_left n (Nat.zero_lt_of_lt hm1))
          have hprod : (M : ℝ) < (m : ℝ) * n := by exact_mod_cast hprodNat
          simp [hout, hprod]
        · simp [hout]
      · exact hleftNorm
      · exact hrightNorm

theorem norm_hughesYoungHighPairSquareTail_le
    {q M : ℕ} (hq : 0 < q) (hM : 0 < M) (t u : ℝ)
    {η : ℝ} (hη0 : 0 < η)
    (hη : η < 2 * (q : ℝ) - 1 / 2) :
    ‖hughesYoungHighPairSquareTail q t u M‖ ≤
      ‖hughesYoungRightContourWeight t (2 * q) u‖ *
        (M : ℝ) ^ (-(2 * (q : ℝ) - 1 / 2 - η)) *
        hughesYoungReferenceDivisorPairMass η := by
  calc
    ‖hughesYoungHighPairSquareTail q t u M‖ ≤
        ∑' p : ℕ × ℕ,
          ‖if (M : ℝ) < (p.1 : ℝ) * p.2 then
              hughesYoungRightPairTerm t (2 * q) u p else 0‖ :=
      norm_hughesYoungHighPairSquareTail_le_productTail hq hM t u
    _ ≤ ∑' p : ℕ × ℕ,
        (‖hughesYoungRightContourWeight t (2 * q) u‖ *
          (M : ℝ) ^ (-(2 * (q : ℝ) - 1 / 2 - η))) *
          (‖divisorDirichletTerm ((1 + η : ℝ) : ℂ) p.1‖ *
            ‖divisorDirichletTerm ((1 + η : ℝ) : ℂ) p.2‖) := by
      exact
        (summable_norm_hughesYoungRightPairTerm_high_tail
            (show 0 < (M : ℝ) by exact_mod_cast hM) hη0 hη).tsum_le_tsum
          (fun p => by
            simpa only [mul_assoc] using
              norm_hughesYoungRightPairTerm_high_tail_le
                (show 0 < (M : ℝ) by exact_mod_cast hM) hη p)
          ((summable_norm_divisorPair_one_add hη0).mul_left
            (‖hughesYoungRightContourWeight t (2 * q) u‖ *
              (M : ℝ) ^ (-(2 * (q : ℝ) - 1 / 2 - η))))
    _ = _ := by
      rw [tsum_mul_left]
      rfl

end RiemannZeta.GuthMaynard
