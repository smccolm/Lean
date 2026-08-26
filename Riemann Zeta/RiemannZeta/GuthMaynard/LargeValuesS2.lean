import RiemannZeta.GuthMaynard.HeathBrownReflection
import RiemannZeta.GuthMaynard.QuantitativeSmoothReflection

open Complex Finset Filter MeasureTheory Real Set
open scoped BigOperators

namespace RiemannZeta.GuthMaynard

/-!
# Guth--Maynard Proposition 6.1

This module starts from the literal three cyclic summands in `gmCubicS2`.
It records the exact conjugation and cyclic identities before applying the
quantitative reflection theorem and the native Heath--Brown estimate.
-/

/-- Reversing an ordinate difference conjugates the complete scaled
nonzero-frequency series.  The proof reindexes the complete integer sum by
`m ↦ -m`; no truncation or triangle inequality is involved. -/
theorem gmTraceNonzeroTailAt_neg_eq_star
    (cutoff : GMSmoothCutoff) (N : ℕ) (t : ℝ) :
    gmTraceNonzeroTailAt cutoff N (-t) =
      star (gmTraceNonzeroTailAt cutoff N t) := by
  unfold gmTraceNonzeroTailAt
  rw [← Equiv.tsum_eq (Equiv.neg ℤ), tsum_star]
  apply tsum_congr
  intro m
  by_cases hm : m = 0
  · subst m
    simp
  · have hNeg : -m ≠ 0 := neg_ne_zero.mpr hm
    change (if -m = 0 then 0 else
        (N : ℂ) * gmTraceFourier cutoff (-t) ((N : ℝ) * ((-m : ℤ) : ℝ))) =
      star (if m = 0 then 0 else
        (N : ℂ) * gmTraceFourier cutoff t ((N : ℝ) * (m : ℝ)))
    rw [if_neg hNeg, if_neg hm]
    have hFreq : (N : ℝ) * ((-m : ℤ) : ℝ) =
        -((N : ℝ) * (m : ℝ)) := by push_cast; ring
    rw [hFreq, gmTraceFourier_neg_eq_conj cutoff (-t), neg_neg]
    simp

/-- Norm form of the exact reversal identity. -/
theorem norm_gmTraceNonzeroTailAt_neg
    (cutoff : GMSmoothCutoff) (N : ℕ) (t : ℝ) :
    ‖gmTraceNonzeroTailAt cutoff N (-t)‖ =
      ‖gmTraceNonzeroTailAt cutoff N t‖ := by
  rw [gmTraceNonzeroTailAt_neg_eq_star cutoff N, norm_star]

/-- The second `S₂` summand is the first one after the cyclic permutation
`(t,u,v) ↦ (v,t,u)`. -/
theorem gmCubicS2SecondSummand_eq_first_cyclic
    (cutoff : GMSmoothCutoff) (N : ℕ) {W : Finset ℝ}
    (t u v : GMRow W) :
    gmCubicS2SecondSummand cutoff N t u v =
      gmCubicS2FirstSummand cutoff N v t u := by
  unfold gmCubicS2SecondSummand gmCubicS2FirstSummand
  ring

/-- The third `S₂` summand is the first one after the cyclic permutation
`(t,u,v) ↦ (u,v,t)`. -/
theorem gmCubicS2ThirdSummand_eq_first_cyclic
    (cutoff : GMSmoothCutoff) (N : ℕ) {W : Finset ℝ}
    (t u v : GMRow W) :
    gmCubicS2ThirdSummand cutoff N t u v =
      gmCubicS2FirstSummand cutoff N u v t := by
  unfold gmCubicS2ThirdSummand gmCubicS2FirstSummand
  ring

/-- On the diagonal selected by the zero mode, the first cyclic product has
exactly the squared norm of one complete nonzero tail. -/
theorem norm_gmCubicS2FirstSummand_diagonal
    (cutoff : GMSmoothCutoff) (N : ℕ)
    {W : Finset ℝ} (t u : GMRow W) :
    ‖gmCubicS2FirstSummand cutoff N t u t‖ =
      ‖gmTraceZeroMode cutoff N 0‖ *
        ‖gmTraceNonzeroTailAt cutoff N ((t : ℝ) - (u : ℝ))‖ ^ 2 := by
  unfold gmCubicS2FirstSummand
  simp only [sub_self, norm_mul]
  have hReverse : (u : ℝ) - (t : ℝ) = -((t : ℝ) - (u : ℝ)) := by ring
  rw [hReverse, norm_gmTraceNonzeroTailAt_neg cutoff N]
  ring

/-- The complete first cyclic contribution to `S₂`. -/
noncomputable def gmCubicS2First (cutoff : GMSmoothCutoff) (N : ℕ)
    (W : Finset ℝ) : ℂ :=
  ∑ t : GMRow W, ∑ u : GMRow W, ∑ v : GMRow W,
    gmCubicS2FirstSummand cutoff N t u v

/-- The complete second cyclic sum equals the first one by a literal cyclic
reindexing of the three finite row variables. -/
theorem gmCubicS2Second_sum_eq_first
    (cutoff : GMSmoothCutoff) (N : ℕ) (W : Finset ℝ) :
    (∑ t : GMRow W, ∑ u : GMRow W, ∑ v : GMRow W,
        gmCubicS2SecondSummand cutoff N t u v) =
      gmCubicS2First cutoff N W := by
  simp_rw [gmCubicS2SecondSummand_eq_first_cyclic]
  unfold gmCubicS2First
  calc
    (∑ t : GMRow W, ∑ u : GMRow W, ∑ v : GMRow W,
        gmCubicS2FirstSummand cutoff N v t u) =
        ∑ t : GMRow W, ∑ v : GMRow W, ∑ u : GMRow W,
          gmCubicS2FirstSummand cutoff N v t u := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [Finset.sum_comm]
    _ = ∑ v : GMRow W, ∑ t : GMRow W, ∑ u : GMRow W,
          gmCubicS2FirstSummand cutoff N v t u := by
      rw [Finset.sum_comm]
    _ = _ := by rfl

/-- The complete third cyclic sum equals the first one. -/
theorem gmCubicS2Third_sum_eq_first
    (cutoff : GMSmoothCutoff) (N : ℕ) (W : Finset ℝ) :
    (∑ t : GMRow W, ∑ u : GMRow W, ∑ v : GMRow W,
        gmCubicS2ThirdSummand cutoff N t u v) =
      gmCubicS2First cutoff N W := by
  simp_rw [gmCubicS2ThirdSummand_eq_first_cyclic]
  unfold gmCubicS2First
  calc
    (∑ t : GMRow W, ∑ u : GMRow W, ∑ v : GMRow W,
        gmCubicS2FirstSummand cutoff N u v t) =
        ∑ u : GMRow W, ∑ t : GMRow W, ∑ v : GMRow W,
          gmCubicS2FirstSummand cutoff N u v t := by
      rw [Finset.sum_comm]
    _ = ∑ u : GMRow W, ∑ v : GMRow W, ∑ t : GMRow W,
          gmCubicS2FirstSummand cutoff N u v t := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [Finset.sum_comm]
    _ = _ := by rfl

/-- Exact cyclic symmetry identity used at the start of the proof of
Guth--Maynard Proposition 6.1. -/
theorem gmCubicS2_eq_three_mul_first
    (cutoff : GMSmoothCutoff) (N : ℕ) (W : Finset ℝ) :
    gmCubicS2 cutoff N W = 3 * gmCubicS2First cutoff N W := by
  unfold gmCubicS2 gmCubicS2Summand
  simp_rw [Finset.sum_add_distrib]
  rw [gmCubicS2Second_sum_eq_first, gmCubicS2Third_sum_eq_first]
  unfold gmCubicS2First
  ring

/-- Diagonal part of the first cyclic contribution (`v=t`). -/
noncomputable def gmCubicS2FirstDiagonal
    (cutoff : GMSmoothCutoff) (N : ℕ) (W : Finset ℝ) : ℂ :=
  ∑ t : GMRow W, ∑ u : GMRow W,
    gmCubicS2FirstSummand cutoff N t u t

/-- Complement of the `v=t` diagonal in the first cyclic contribution. -/
noncomputable def gmCubicS2FirstOffDiagonal
    (cutoff : GMSmoothCutoff) (N : ℕ) (W : Finset ℝ) : ℂ :=
  ∑ t : GMRow W, ∑ u : GMRow W,
    ∑ v ∈ (Finset.univ.erase t : Finset (GMRow W)),
      gmCubicS2FirstSummand cutoff N t u v

/-- Exact diagonal/off-diagonal split of the first cyclic contribution. -/
theorem gmCubicS2First_eq_diagonal_add_offDiagonal
    (cutoff : GMSmoothCutoff) (N : ℕ) (W : Finset ℝ) :
    gmCubicS2First cutoff N W =
      gmCubicS2FirstDiagonal cutoff N W +
        gmCubicS2FirstOffDiagonal cutoff N W := by
  unfold gmCubicS2First gmCubicS2FirstDiagonal gmCubicS2FirstOffDiagonal
  calc
    (∑ t : GMRow W, ∑ u : GMRow W, ∑ v : GMRow W,
        gmCubicS2FirstSummand cutoff N t u v) =
      ∑ t : GMRow W, ∑ u : GMRow W,
        (gmCubicS2FirstSummand cutoff N t u t +
          ∑ v ∈ (Finset.univ.erase t : Finset (GMRow W)),
            gmCubicS2FirstSummand cutoff N t u v) := by
      apply Finset.sum_congr rfl
      intro t ht
      apply Finset.sum_congr rfl
      intro u hu
      exact (Finset.add_sum_erase Finset.univ
        (fun v : GMRow W => gmCubicS2FirstSummand cutoff N t u v)
        (Finset.mem_univ t)).symm
    _ = _ := by
      simp_rw [Finset.sum_add_distrib]

/-- Ordered difference moment of the literal complete nonzero Poisson tail
which remains on the `v = t` diagonal of the first cyclic contribution. -/
noncomputable def gmTraceNonzeroDifferenceMoment
    (cutoff : GMSmoothCutoff) (N : ℕ) (W : Finset ℝ) : ℝ :=
  ∑ t : GMRow W, ∑ u : GMRow W,
    ‖gmTraceNonzeroTailAt cutoff N ((t : ℝ) - (u : ℝ))‖ ^ 2

/-- Source-finset presentation of the same ordered moment. -/
theorem gmTraceNonzeroDifferenceMoment_eq_source
    (cutoff : GMSmoothCutoff) (N : ℕ) (W : Finset ℝ) :
    gmTraceNonzeroDifferenceMoment cutoff N W =
      ∑ t ∈ W, ∑ u ∈ W,
        ‖gmTraceNonzeroTailAt cutoff N (t - u)‖ ^ 2 := by
  unfold gmTraceNonzeroDifferenceMoment
  have hInner (t : GMRow W) :
      (∑ u : GMRow W,
          ‖gmTraceNonzeroTailAt cutoff N ((t : ℝ) - (u : ℝ))‖ ^ 2) =
        ∑ u ∈ W,
          ‖gmTraceNonzeroTailAt cutoff N ((t : ℝ) - u)‖ ^ 2 := by
    conv_rhs => rw [← Finset.sum_attach]
    rw [Finset.univ_eq_attach W]
  calc
    (∑ t : GMRow W, ∑ u : GMRow W,
        ‖gmTraceNonzeroTailAt cutoff N ((t : ℝ) - (u : ℝ))‖ ^ 2) =
      ∑ t : GMRow W, ∑ u ∈ W,
        ‖gmTraceNonzeroTailAt cutoff N ((t : ℝ) - u)‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro t ht
          exact hInner t
    _ = _ := by
      conv_rhs => rw [← Finset.sum_attach]
      rw [Finset.univ_eq_attach W]

/-- The first cyclic diagonal is exactly controlled by the zero mode at the
origin times the ordered nonzero-tail moment.  This is the finite triangle
inequality step at the start of Guth--Maynard Proposition 6.1. -/
theorem norm_gmCubicS2FirstDiagonal_le
    (cutoff : GMSmoothCutoff) (N : ℕ) (W : Finset ℝ) :
    ‖gmCubicS2FirstDiagonal cutoff N W‖ ≤
      ‖gmTraceZeroMode cutoff N 0‖ *
        gmTraceNonzeroDifferenceMoment cutoff N W := by
  unfold gmCubicS2FirstDiagonal gmTraceNonzeroDifferenceMoment
  calc
    ‖∑ t : GMRow W, ∑ u : GMRow W,
        gmCubicS2FirstSummand cutoff N t u t‖ ≤
        ∑ t : GMRow W, ‖∑ u : GMRow W,
          gmCubicS2FirstSummand cutoff N t u t‖ := norm_sum_le _ _
    _ ≤ ∑ t : GMRow W, ∑ u : GMRow W,
        ‖gmCubicS2FirstSummand cutoff N t u t‖ := by
      apply Finset.sum_le_sum
      intro t ht
      exact norm_sum_le _ _
    _ = ∑ t : GMRow W, ∑ u : GMRow W,
        ‖gmTraceZeroMode cutoff N 0‖ *
          ‖gmTraceNonzeroTailAt cutoff N
            ((t : ℝ) - (u : ℝ))‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro t ht
      apply Finset.sum_congr rfl
      intro u hu
      exact norm_gmCubicS2FirstSummand_diagonal cutoff N t u
    _ = ‖gmTraceZeroMode cutoff N 0‖ *
        (∑ t : GMRow W, ∑ u : GMRow W,
          ‖gmTraceNonzeroTailAt cutoff N
            ((t : ℝ) - (u : ℝ))‖ ^ 2) := by
      simp_rw [Finset.mul_sum]

/-- Quantitative zero-mode insertion in the cyclic diagonal. -/
theorem gmCubicS2FirstDiagonal_le_zeroModeConstant
    (cutoff : GMSmoothCutoff) :
    ∃ B : ℝ, 0 < B ∧ ∀ (N : ℕ) (W : Finset ℝ),
      ‖gmCubicS2FirstDiagonal cutoff N W‖ ≤
        B * (N : ℝ) * gmTraceNonzeroDifferenceMoment cutoff N W := by
  obtain ⟨B, hB, hZero⟩ := gmTraceZeroMode_bound cutoff
  refine ⟨B, hB, ?_⟩
  intro N W
  calc
    ‖gmCubicS2FirstDiagonal cutoff N W‖ ≤
        ‖gmTraceZeroMode cutoff N 0‖ *
          gmTraceNonzeroDifferenceMoment cutoff N W :=
      norm_gmCubicS2FirstDiagonal_le cutoff N W
    _ ≤ (B * (N : ℝ)) * gmTraceNonzeroDifferenceMoment cutoff N W := by
      apply mul_le_mul_of_nonneg_right
      · simpa [mul_comm] using hZero N 0
      · unfold gmTraceNonzeroDifferenceMoment
        positivity
    _ = B * (N : ℝ) * gmTraceNonzeroDifferenceMoment cutoff N W := by ring

/-! ## Literal nonzero-tail reflection on dyadic difference bins -/

/-- The squared literal nonzero Poisson tail on one dyadic displacement
fiber.  Unlike the Heath--Brown trace moment, this quantity contains no zero
mode. -/
noncomputable def gmNonzeroTailBinMoment
    (cutoff : GMSmoothCutoff) (N : ℕ) (W : Finset ℝ) (j : ℕ) : ℝ :=
  ∑ p ∈ heathBrownDifferenceBin W j,
    ‖gmTraceNonzeroTailAt cutoff N (p.1 - p.2)‖ ^ 2

/-- The literal diagonal part of the complete nonzero-tail difference
moment.  It is kept separate because Lemma 6.2 is used only at nonzero
displacements. -/
noncomputable def gmTraceNonzeroDiagonalMoment
    (cutoff : GMSmoothCutoff) (N : ℕ) (W : Finset ℝ) : ℝ :=
  ∑ t ∈ W, ‖gmTraceNonzeroTailAt cutoff N (t - t)‖ ^ 2

/-- The literal off-diagonal part of the complete nonzero-tail difference
moment, represented as the filtered ordered product used by the common
dyadic displacement partition. -/
noncomputable def gmTraceNonzeroOffDiagonalMoment
    (cutoff : GMSmoothCutoff) (N : ℕ) (W : Finset ℝ) : ℝ :=
  ∑ p ∈ heathBrownOffDiagonalPairs W,
    ‖gmTraceNonzeroTailAt cutoff N (p.1 - p.2)‖ ^ 2

theorem gmTraceNonzeroOffDiagonalMoment_eq_nested
    (cutoff : GMSmoothCutoff) (N : ℕ) (W : Finset ℝ) :
    gmTraceNonzeroOffDiagonalMoment cutoff N W =
      ∑ t ∈ W, ∑ u ∈ W.erase t,
        ‖gmTraceNonzeroTailAt cutoff N (t - u)‖ ^ 2 := by
  classical
  unfold gmTraceNonzeroOffDiagonalMoment heathBrownOffDiagonalPairs
  rw [Finset.sum_filter, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro t ht
  calc
    (∑ u ∈ W, if t ≠ u then
        ‖gmTraceNonzeroTailAt cutoff N (t - u)‖ ^ 2 else 0) =
      ∑ u ∈ W.erase t, if t ≠ u then
        ‖gmTraceNonzeroTailAt cutoff N (t - u)‖ ^ 2 else 0 := by
          rw [← Finset.sum_erase_add W _ ht]
          simp
    _ = ∑ u ∈ W.erase t,
        ‖gmTraceNonzeroTailAt cutoff N (t - u)‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro u hu
      simp [(Finset.ne_of_mem_erase hu).symm]

/-- Exact diagonal/off-diagonal decomposition of the complete literal tail
moment used by the cyclic `S₂` diagonal. -/
theorem gmTraceNonzeroDifferenceMoment_eq_diagonal_add_offDiagonal
    (cutoff : GMSmoothCutoff) (N : ℕ) (W : Finset ℝ) :
    gmTraceNonzeroDifferenceMoment cutoff N W =
      gmTraceNonzeroDiagonalMoment cutoff N W +
        gmTraceNonzeroOffDiagonalMoment cutoff N W := by
  rw [gmTraceNonzeroDifferenceMoment_eq_source,
    orderedPairSum_eq_diagonal_add_offDiagonal,
    gmTraceNonzeroOffDiagonalMoment_eq_nested]
  rfl

/-- Exact finite dyadic expansion of the literal nonzero-tail off-diagonal
moment. -/
theorem gmTraceNonzeroOffDiagonalMoment_eq_sum_bins
    {T : ℝ} {W : Finset ℝ} (hSep : IsSeparated 1 W)
    (hInterval : InBaseInterval T W) (cutoff : GMSmoothCutoff) (N : ℕ) :
    gmTraceNonzeroOffDiagonalMoment cutoff N W =
      ∑ j ∈ Finset.range (Nat.log 2 (Nat.floor T) + 1),
        gmNonzeroTailBinMoment cutoff N W j := by
  unfold gmTraceNonzeroOffDiagonalMoment gmNonzeroTailBinMoment
  exact sum_heathBrownOffDiagonalPairs_eq_sum_differenceBins hSep hInterval _

/-- Exact source identity combining the diagonal and every finite dyadic
displacement fiber. -/
theorem gmTraceNonzeroDifferenceMoment_eq_diagonal_add_bins
    {T : ℝ} {W : Finset ℝ} (hSep : IsSeparated 1 W)
    (hInterval : InBaseInterval T W) (cutoff : GMSmoothCutoff) (N : ℕ) :
    gmTraceNonzeroDifferenceMoment cutoff N W =
      gmTraceNonzeroDiagonalMoment cutoff N W +
        ∑ j ∈ Finset.range (Nat.log 2 (Nat.floor T) + 1),
          gmNonzeroTailBinMoment cutoff N W j := by
  rw [gmTraceNonzeroDifferenceMoment_eq_diagonal_add_offDiagonal,
    gmTraceNonzeroOffDiagonalMoment_eq_sum_bins hSep hInterval]

/-- Uniform sum of the Mellin-tail and omitted-frequency errors on a dyadic
displacement fiber. -/
noncomputable def gmNonzeroTailBinError
    (q N M : ℕ) (H U K L : ℝ) : ℝ :=
  (N : ℝ) * K * (M : ℝ) ^ 2 * H ^ (1 - (q : ℝ)) +
    (N : ℝ) * L * (1 + U) ^ (q + 2) /
      ((N : ℝ) ^ (q + 2) * (M : ℝ) ^ q)

/-- Exact fixed-length reflection estimate for the literal nonzero tail on
one dyadic displacement fiber.  The common cutoff `M` is essential: after
Cauchy--Schwarz the translated prefix coefficients are independent of the
pair, so the native Heath--Brown difference-set theorem applies. -/
theorem gmNonzeroTailBinMoment_le_reflection
    (cutoff : GMSmoothCutoff) (q : ℕ) (hq : 2 ≤ q) :
    ∃ C K L : ℝ, 0 < C ∧ 0 < K ∧ 0 < L ∧
      ∀ {W : Finset ℝ} {j N M : ℕ} {H : ℝ},
        IsSeparated 1 W → 2 ≤ j → 1 ≤ H →
        H ≤ ((2 ^ j : ℕ) : ℝ) / 2 → 0 < N → 0 < M →
        gmNonzeroTailBinMoment cutoff N W j ≤
          2 * (((N : ℝ) * C / Real.sqrt ((2 ^ j : ℕ) : ℝ)) ^ 2) *
              ((2 * H) ^ 2 * heathBrownReflectionDyadicMoment W M) +
            2 * ((heathBrownDifferenceBin W j).card : ℝ) *
              (gmNonzeroTailBinError q N M H
                (((2 ^ (j + 1) : ℕ) : ℝ)) K L) ^ 2 := by
  obtain ⟨C, K, L, hC, hK, hL, hReflect⟩ :=
    gmCompleteSmoothReflection_bound_order cutoff q hq
  refine ⟨C, K, L, hC, hK, hL, ?_⟩
  intro W j N M H hSep hj hH hHupper hN hM
  let T₀ : ℝ := ((2 ^ j : ℕ) : ℝ)
  let U : ℝ := ((2 ^ (j + 1) : ℕ) : ℝ)
  let A : ℝ := (N : ℝ) * C / Real.sqrt T₀
  let E : ℝ := gmNonzeroTailBinError q N M H U K L
  have hT₀ : 4 ≤ T₀ := by
    have hNat : 4 ≤ 2 ^ j := by
      change 2 ^ 2 ≤ 2 ^ j
      exact Nat.pow_le_pow_right (by omega) hj
    dsimp only [T₀]
    exact_mod_cast hNat
  have hPoint : ∀ p ∈ heathBrownDifferenceBin W j,
      ‖gmTraceNonzeroTailAt cutoff N (p.1 - p.2)‖ ≤
        A * (∫ u in -H..H,
          ‖gmReflectionDirichletPoly (p.1 - p.2) M u‖) + E := by
    intro p hp
    have hBin := heathBrownDifferenceBin_bounds hSep hp
    have hRaw := hReflect hT₀ hBin.1 hH
      (by simpa only [T₀] using hHupper) hN hM
    have hBase : 1 + |p.1 - p.2| ≤ 1 + U := by
      dsimp only [U]
      linarith
    have hPow : (1 + |p.1 - p.2|) ^ (q + 2) ≤
        (1 + U) ^ (q + 2) :=
      pow_le_pow_left₀ (by positivity) hBase (q + 2)
    have hDenom : 0 < (N : ℝ) ^ (q + 2) * (M : ℝ) ^ q := by
      positivity
    have hFrequency :
        (N : ℝ) * L * (1 + |p.1 - p.2|) ^ (q + 2) /
            ((N : ℝ) ^ (q + 2) * (M : ℝ) ^ q) ≤
          (N : ℝ) * L * (1 + U) ^ (q + 2) /
            ((N : ℝ) ^ (q + 2) * (M : ℝ) ^ q) := by
      apply div_le_div_of_nonneg_right _ hDenom.le
      exact mul_le_mul_of_nonneg_left hPow (by positivity)
    rw [norm_gmTraceNonzeroTailAt_eq]
    have hScaled := mul_le_mul_of_nonneg_left hRaw (Nat.cast_nonneg N)
    dsimp only [A, E, gmNonzeroTailBinError, T₀, U]
    calc
      (N : ℝ) * ‖gmTraceNonzeroFourierSum cutoff N (p.1 - p.2)‖ ≤
          (N : ℝ) *
            (C / Real.sqrt (((2 ^ j : ℕ) : ℝ)) *
                (∫ u in -H..H,
                  ‖gmReflectionDirichletPoly (p.1 - p.2) M u‖) +
              K * (M : ℝ) ^ 2 * H ^ (1 - (q : ℝ)) +
              L * (1 + |p.1 - p.2|) ^ (q + 2) /
                ((N : ℝ) ^ (q + 2) * (M : ℝ) ^ q)) := hScaled
      _ = (N : ℝ) * C / Real.sqrt (((2 ^ j : ℕ) : ℝ)) *
              (∫ u in -H..H,
                ‖gmReflectionDirichletPoly (p.1 - p.2) M u‖) +
            (N : ℝ) * K * (M : ℝ) ^ 2 * H ^ (1 - (q : ℝ)) +
            (N : ℝ) * L * (1 + |p.1 - p.2|) ^ (q + 2) /
              ((N : ℝ) ^ (q + 2) * (M : ℝ) ^ q) := by ring
      _ ≤ (N : ℝ) * C / Real.sqrt (((2 ^ j : ℕ) : ℝ)) *
              (∫ u in -H..H,
                ‖gmReflectionDirichletPoly (p.1 - p.2) M u‖) +
            (N : ℝ) * K * (M : ℝ) ^ 2 * H ^ (1 - (q : ℝ)) +
            (N : ℝ) * L * (1 + U) ^ (q + 2) /
              ((N : ℝ) ^ (q + 2) * (M : ℝ) ^ q) := by
        exact add_le_add le_rfl hFrequency
      _ = _ := by ring
  have hPointSq : ∀ p ∈ heathBrownDifferenceBin W j,
      ‖gmTraceNonzeroTailAt cutoff N (p.1 - p.2)‖ ^ 2 ≤
        2 * A ^ 2 *
            (∫ u in -H..H,
              ‖gmReflectionDirichletPoly (p.1 - p.2) M u‖) ^ 2 +
          2 * E ^ 2 := by
    intro p hp
    have hpBound := hPoint p hp
    have hRhsNonneg : 0 ≤ A *
        (∫ u in -H..H,
          ‖gmReflectionDirichletPoly (p.1 - p.2) M u‖) + E :=
      (norm_nonneg _).trans hpBound
    have hSq := pow_le_pow_left₀ (norm_nonneg _) hpBound 2
    calc
      ‖gmTraceNonzeroTailAt cutoff N (p.1 - p.2)‖ ^ 2 ≤
          (A * (∫ u in -H..H,
            ‖gmReflectionDirichletPoly (p.1 - p.2) M u‖) + E) ^ 2 := hSq
      _ ≤ 2 * A ^ 2 *
            (∫ u in -H..H,
              ‖gmReflectionDirichletPoly (p.1 - p.2) M u‖) ^ 2 +
          2 * E ^ 2 := by
        nlinarith [sq_nonneg
          (A * (∫ u in -H..H,
            ‖gmReflectionDirichletPoly (p.1 - p.2) M u‖) - E)]
  have hIntegral := sum_bin_sq_integral_norm_gmReflectionDirichletPoly_le
    W j hM H ((by norm_num : (0 : ℝ) ≤ 1).trans hH)
  unfold gmNonzeroTailBinMoment
  calc
    (∑ p ∈ heathBrownDifferenceBin W j,
        ‖gmTraceNonzeroTailAt cutoff N (p.1 - p.2)‖ ^ 2) ≤
      ∑ p ∈ heathBrownDifferenceBin W j,
        (2 * A ^ 2 *
            (∫ u in -H..H,
              ‖gmReflectionDirichletPoly (p.1 - p.2) M u‖) ^ 2 +
          2 * E ^ 2) := by
      apply Finset.sum_le_sum
      intro p hp
      exact hPointSq p hp
    _ = 2 * A ^ 2 *
          (∑ p ∈ heathBrownDifferenceBin W j,
            (∫ u in -H..H,
              ‖gmReflectionDirichletPoly (p.1 - p.2) M u‖) ^ 2) +
        2 * ((heathBrownDifferenceBin W j).card : ℝ) * E ^ 2 := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp
      ring
    _ ≤ 2 * A ^ 2 *
          ((2 * H) ^ 2 * heathBrownReflectionDyadicMoment W M) +
        2 * ((heathBrownDifferenceBin W j).card : ℝ) * E ^ 2 := by
      apply add_le_add
      · apply mul_le_mul_of_nonneg_left
        · simpa only [heathBrownReflectionDyadicMoment] using hIntegral
        · positivity
      · exact le_rfl
    _ = _ := by rfl

/-- The native Heath--Brown theorem inserted into the complete dyadic
prefix majorant.  All logarithmic factors remain explicit at this stage;
they are absorbed only in the later epsilon-budget theorem. -/
theorem heathBrownReflectionDyadicMoment_le_native
    (η : ℝ) (hη : 0 < η) :
    ∃ C T_min : ℝ, 0 < C ∧ 1 ≤ T_min ∧
      ∀ {M : ℕ} {T : ℝ} (W : Finset ℝ),
        0 < M → T_min ≤ T → IsSeparated 1 W → InBaseInterval T W →
        heathBrownReflectionDyadicMoment W M ≤
          2 * ((Nat.clog 2 M : ℝ) + 1) *
            ((W.card : ℝ) ^ 2 +
              (Nat.clog 2 M : ℝ) * C * T ^ η *
                ((W.card : ℝ) ^ 2 * M +
                  (W.card : ℝ) * M ^ 2 +
                  (W.card : ℝ) ^ (5 / 4 : ℝ) *
                    T ^ (1 / 2 : ℝ) * M)) := by
  obtain ⟨C, T_min, hC, hT_min, hHB⟩ :=
    heathBrownCoefficientOneMeanSquare_native η hη
  refine ⟨C, T_min, hC, hT_min, ?_⟩
  intro M T W hM hT hSep hBase
  have hTOne : 1 ≤ T := hT_min.trans hT
  have hTNonneg : 0 ≤ T := zero_le_one.trans hTOne
  let k : ℕ := Nat.clog 2 M
  let R : ℝ := W.card
  let B : ℝ := C * T ^ η *
    (R ^ 2 * M + R * M ^ 2 +
      R ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ) * M)
  have hBNonneg : 0 ≤ B := by
    dsimp only [B, R]
    positivity
  have hCTNonneg : 0 ≤ C * T ^ η :=
    mul_nonneg hC.le (Real.rpow_nonneg hTNonneg η)
  have hRTailNonneg : 0 ≤
      R ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ) := by
    exact mul_nonneg (Real.rpow_nonneg (by dsimp only [R]; positivity) _)
      (Real.rpow_nonneg hTNonneg _)
  have hEach : ∀ r ∈ Finset.range k,
      heathBrownCoefficientOneMoment (2 ^ r) W ≤ B := by
    intro r hr
    have hrk : r < k := Finset.mem_range.mp hr
    have hScaleNat : 2 ^ r ≤ M :=
      (Nat.pow_lt_of_lt_clog hrk).le
    have hScale : ((2 ^ r : ℕ) : ℝ) ≤ M := by exact_mod_cast hScaleNat
    have hScaleSq : (((2 ^ r : ℕ) : ℝ)) ^ 2 ≤ (M : ℝ) ^ 2 := by
      exact pow_le_pow_left₀ (by positivity) hScale 2
    have hAt := hHB (2 ^ r) T W (by positivity) hT hSep hBase
    calc
      heathBrownCoefficientOneMoment (2 ^ r) W ≤
          C * T ^ η *
            ((R ^ 2 * ((2 ^ r : ℕ) : ℝ)) +
              (R * (((2 ^ r : ℕ) : ℝ)) ^ 2) +
              (R ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ) *
                ((2 ^ r : ℕ) : ℝ))) := by
        simpa only [heathBrownCoefficientOneMoment, R] using hAt
      _ ≤ C * T ^ η *
            (R ^ 2 * M + R * M ^ 2 +
              R ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ) * M) := by
        gcongr
      _ = B := by rfl
  have hSum :
      (∑ r ∈ Finset.range k,
          heathBrownCoefficientOneMoment (2 ^ r) W) ≤ (k : ℝ) * B := by
    calc
      _ ≤ ∑ _r ∈ Finset.range k, B := Finset.sum_le_sum hEach
      _ = (k : ℝ) * B := by simp
  rw [heathBrownReflectionDyadicMoment_eq]
  dsimp only [k] at hSum ⊢
  calc
    2 * ((Nat.clog 2 M : ℝ) + 1) *
        ((W.card : ℝ) ^ 2 +
          ∑ r ∈ Finset.range (Nat.clog 2 M),
            heathBrownCoefficientOneMoment (2 ^ r) W) ≤
      2 * ((Nat.clog 2 M : ℝ) + 1) *
        ((W.card : ℝ) ^ 2 + (Nat.clog 2 M : ℝ) * B) := by
          gcongr
    _ = _ := by
      dsimp only [B, R]
      ring

/-! ## The arbitrary-coefficient powering step, equations (6.2)--(6.3) -/

/-- Ordered difference moment of an arbitrary dyadic Dirichlet polynomial.
This is the quantity on the right of the reflected estimate (6.1). -/
noncomputable def gmDifferenceMoment
    (M : ℕ) (W : Finset ℝ) (a : ℕ → ℂ) : ℝ :=
  ∑ t ∈ W, ∑ u ∈ W,
    ‖sourceDirichletPoly M a (t - u)‖ ^ 2

/-- The `2k`-th ordered difference moment used in (6.2). -/
noncomputable def gmDifferencePowerMoment
    (M k : ℕ) (W : Finset ℝ) (a : ℕ → ℂ) : ℝ :=
  ∑ t ∈ W, ∑ u ∈ W,
    ‖sourceDirichletPoly M a (t - u)‖ ^ (2 * k)

theorem gmDifferenceMoment_nonneg
    (M : ℕ) (W : Finset ℝ) (a : ℕ → ℂ) :
    0 ≤ gmDifferenceMoment M W a := by
  unfold gmDifferenceMoment
  positivity

/-- Literal finite Hölder inequality in Guth--Maynard (6.2). -/
theorem gmDifferenceMoment_pow_le
    (M k : ℕ) (W : Finset ℝ) (a : ℕ → ℂ) (hk : 0 < k) :
    gmDifferenceMoment M W a ^ k ≤
      ((W.card : ℝ) ^ 2) ^ (k - 1) *
        gmDifferencePowerMoment M k W a := by
  let f : ℝ × ℝ → ℝ := fun p =>
    ‖sourceDirichletPoly M a (p.1 - p.2)‖ ^ 2
  have h := pow_sum_le_card_mul_sum_pow
    (s := W.product W) (f := f)
    (by intro p hp; exact sq_nonneg _) (k - 1)
  have hkSub : k - 1 + 1 = k := Nat.sub_add_cancel hk
  rw [hkSub] at h
  rw [Finset.product_eq_sprod] at h
  simp_rw [Finset.sum_product] at h
  rw [Finset.card_product] at h
  simp only [f, Nat.cast_mul] at h
  have hPower :
      (∑ t ∈ W, ∑ u ∈ W,
          (‖sourceDirichletPoly M a (t - u)‖ ^ 2) ^ k) =
        gmDifferencePowerMoment M k W a := by
    unfold gmDifferencePowerMoment
    apply Finset.sum_congr rfl
    intro t ht
    apply Finset.sum_congr rfl
    intro u hu
    rw [← pow_mul]
  rw [hPower] at h
  have hCard :
      (W.card : ℝ) * (W.card : ℝ) = (W.card : ℝ) ^ 2 := by ring
  rw [hCard] at h
  simpa only [gmDifferenceMoment] using h

/-- The source positive-phase polynomial raised to the `k`-th power is
the generic finite-powered polynomial at the matching imaginary point. -/
theorem sourceDirichletPoly_pow_eq_finitePowPoly
    (M k : ℕ) (a : ℕ → ℂ) (y : ℝ) :
    (sourceDirichletPoly M a y) ^ k =
      finitePowPoly M k a (-((y : ℂ) * I)) := by
  unfold sourceDirichletPoly finitePowPoly
  congr 2
  funext n
  simp

/-- Exact wide-support form of the powered arbitrary-coefficient block. -/
theorem gmPoweredWide_eq
    (M k : ℕ) (a : ℕ → ℂ) (y : ℝ)
    (hM : 0 < M) (hk : 0 < k) :
    wideDirichletPoly (M ^ k) k (finitePowCoeff M k a) (-y) =
      (sourceDirichletPoly M a y) ^ k := by
  rw [sourceDirichletPoly_pow_eq_finitePowPoly]
  rw [finite_polynomial_power_identity_Ioc M k a
    (-((y : ℂ) * I)) hM hk]
  unfold wideDirichletPoly
  have hUpper : 2 ^ k * M ^ k = (2 * M) ^ k := by rw [mul_pow]
  rw [hUpper]
  apply Finset.sum_congr rfl
  intro m hm
  congr 2
  push_cast
  ring

/-- Moment form of the exact powered expansion. -/
theorem sum_norm_gmPoweredWide_sq
    (M k : ℕ) (W : Finset ℝ) (a : ℕ → ℂ)
    (hM : 0 < M) (hk : 0 < k) :
    (∑ t ∈ W, ∑ u ∈ W,
      ‖wideDirichletPoly (M ^ k) k (finitePowCoeff M k a)
        (-(t - u))‖ ^ 2) =
      gmDifferencePowerMoment M k W a := by
  unfold gmDifferencePowerMoment
  apply Finset.sum_congr rfl
  intro t ht
  apply Finset.sum_congr rfl
  intro u hu
  rw [gmPoweredWide_eq M k a (t - u) hM hk, norm_pow, ← pow_mul]
  congr 1
  omega

/-- Cauchy--Schwarz after decomposing the powered support into its exact
`k` ordinary dyadic blocks. -/
theorem sum_norm_gmPoweredWide_sq_le_blocks
    (M k : ℕ) (W : Finset ℝ) (a : ℕ → ℂ) :
    (∑ t ∈ W, ∑ u ∈ W,
      ‖wideDirichletPoly (M ^ k) k (finitePowCoeff M k a)
        (-(t - u))‖ ^ 2) ≤
      (k : ℝ) * ∑ r ∈ Finset.range k,
        gmDifferenceMoment (2 ^ r * M ^ k) W (finitePowCoeff M k a) := by
  calc
    _ ≤ ∑ t ∈ W, ∑ u ∈ W, (k : ℝ) *
        ∑ r ∈ Finset.range k,
          ‖sourceDirichletPoly (2 ^ r * M ^ k)
            (finitePowCoeff M k a) (t - u)‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro t ht
      apply Finset.sum_le_sum
      intro u hu
      rw [wideDirichletPoly_eq_sum_blocks]
      have hCS := complex_sum_sq_le_card_mul_sum_sq (Finset.range k)
        (fun r => dirichletPoly (2 ^ r * M ^ k)
          (finitePowCoeff M k a) (-(t - u)))
      simpa only [dirichletPoly_neg_eq_sourceDirichletPoly,
        Finset.card_range, Nat.cast_id] using hCS
    _ = _ := by
      unfold gmDifferenceMoment
      simp_rw [Finset.mul_sum]
      calc
        (∑ t ∈ W, ∑ u ∈ W, ∑ r ∈ Finset.range k,
            (k : ℝ) *
              ‖sourceDirichletPoly (2 ^ r * M ^ k)
                (finitePowCoeff M k a) (t - u)‖ ^ 2) =
            ∑ t ∈ W, ∑ r ∈ Finset.range k, ∑ u ∈ W,
              (k : ℝ) *
                ‖sourceDirichletPoly (2 ^ r * M ^ k)
                  (finitePowCoeff M k a) (t - u)‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro t ht
          rw [Finset.sum_comm]
        _ = ∑ r ∈ Finset.range k, ∑ t ∈ W, ∑ u ∈ W,
              (k : ℝ) *
                ‖sourceDirichletPoly (2 ^ r * M ^ k)
                  (finitePowCoeff M k a) (t - u)‖ ^ 2 := by
          rw [Finset.sum_comm]

/-- Unit normalization of the literal powered coefficients used in the
Section 6 application of Heath--Brown's theorem. -/
noncomputable def gmNormalizedPoweredCoeffs
    (M k : ℕ) (a : ℕ → ℂ) (C η : ℝ) (m : ℕ) : ℂ :=
  finitePowCoeff M k a m /
    ((C * ((2 ^ k * M ^ k : ℕ) : ℝ) ^ η : ℝ) : ℂ)

theorem norm_gmNormalizedPoweredCoeffs_le_one
    (M k m : ℕ) (a : ℕ → ℂ) (C η : ℝ)
    (hM : 0 < M) (hC : 0 < C) (hη : 0 < η)
    (hm : m ∈ Finset.Ioc (M ^ k) (2 ^ k * M ^ k))
    (hCoeff : ‖finitePowCoeff M k a m‖ ≤ C * (m : ℝ) ^ η) :
    ‖gmNormalizedPoweredCoeffs M k a C η m‖ ≤ 1 := by
  have hmUpper : m ≤ 2 ^ k * M ^ k := (Finset.mem_Ioc.mp hm).2
  have hUpperPos : 0 < 2 ^ k * M ^ k :=
    mul_pos (pow_pos (by omega) k) (pow_pos hM k)
  have hRpow : (m : ℝ) ^ η ≤
      ((2 ^ k * M ^ k : ℕ) : ℝ) ^ η :=
    Real.rpow_le_rpow (Nat.cast_nonneg m)
      (by exact_mod_cast hmUpper) hη.le
  have hDenomPos : 0 < C * ((2 ^ k * M ^ k : ℕ) : ℝ) ^ η := by
    exact mul_pos hC (Real.rpow_pos_of_pos (by exact_mod_cast hUpperPos) _)
  have hDenomNorm :
      ‖((C * ((2 ^ k * M ^ k : ℕ) : ℝ) ^ η : ℝ) : ℂ)‖ =
        C * ((2 ^ k * M ^ k : ℕ) : ℝ) ^ η := by
    simpa only [Complex.norm_real] using abs_of_pos hDenomPos
  rw [gmNormalizedPoweredCoeffs, norm_div, hDenomNorm,
    div_le_one hDenomPos]
  exact hCoeff.trans (mul_le_mul_of_nonneg_left hRpow hC.le)

/-- Scaling the normalized coefficients back recovers the powered block
exactly, including the complex phase. -/
theorem sourceDirichletPoly_gmNormalizedPoweredCoeffs
    (Q M k : ℕ) (a : ℕ → ℂ) (C η y : ℝ)
    (hDenom : 0 < C * ((2 ^ k * M ^ k : ℕ) : ℝ) ^ η) :
    sourceDirichletPoly Q (finitePowCoeff M k a) y =
      ((C * ((2 ^ k * M ^ k : ℕ) : ℝ) ^ η : ℝ) : ℂ) *
        sourceDirichletPoly Q
          (gmNormalizedPoweredCoeffs M k a C η) y := by
  unfold sourceDirichletPoly gmNormalizedPoweredCoeffs
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [div_mul_eq_mul_div]
  have hDenomC :
      ((C * ((2 ^ k * M ^ k : ℕ) : ℝ) ^ η : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hDenom.ne'
  field_simp [hDenomC]

/-- Moment scaling identity for one normalized powered dyadic block. -/
theorem gmDifferenceMoment_normalizedPowered
    (Q M k : ℕ) (W : Finset ℝ) (a : ℕ → ℂ) (C η : ℝ)
    (hDenom : 0 < C * ((2 ^ k * M ^ k : ℕ) : ℝ) ^ η) :
    gmDifferenceMoment Q W (finitePowCoeff M k a) =
      (C * ((2 ^ k * M ^ k : ℕ) : ℝ) ^ η) ^ 2 *
        gmDifferenceMoment Q W
          (gmNormalizedPoweredCoeffs M k a C η) := by
  unfold gmDifferenceMoment
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  rw [sourceDirichletPoly_gmNormalizedPoweredCoeffs
    Q M k a C η (t - u) hDenom, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hDenom, mul_pow]

/-- Guth--Maynard (6.2)--(6.3), before taking the `k`-th root.  The
factorization constant is uniform in `M` and the base coefficients, and
the actual native arbitrary-coefficient Heath--Brown theorem is applied to
every powered dyadic block. -/
theorem gmDifferenceMoment_pow_le_heathBrown
    (k : ℕ) (η : ℝ) (hk : 0 < k) (hη : 0 < η) :
    ∃ C T_min : ℝ, 0 < C ∧ 1 ≤ T_min ∧
      ∀ {M : ℕ} {T : ℝ} (W : Finset ℝ) (a : ℕ → ℂ),
        0 < M → T_min ≤ T → IsSeparated 1 W → InBaseInterval T W →
        (∀ n ∈ dyadicInterval M, ‖a n‖ ≤ 1) →
        gmDifferenceMoment M W a ^ k ≤
          ((W.card : ℝ) ^ 2) ^ (k - 1) * (k : ℝ) ^ 2 *
            C * T ^ η *
              (C * ((2 ^ k * M ^ k : ℕ) : ℝ) ^ η) ^ 2 *
              ((W.card : ℝ) ^ 2 * (2 ^ k * M ^ k : ℕ) +
                (W.card : ℝ) * (2 ^ k * M ^ k : ℕ) ^ 2 +
                (W.card : ℝ) ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ) *
                  (2 ^ k * M ^ k : ℕ)) := by
  obtain ⟨A, hA, hCoeff⟩ := finitePowCoeff_bound_uniform k η hη
  obtain ⟨B, T_min, hB, hT_min, hHB⟩ :=
    heathBrownDifferenceSetMeanSquare_native η hη
  let C : ℝ := max A B
  refine ⟨C, T_min, lt_of_lt_of_le hA (le_max_left _ _), hT_min, ?_⟩
  intro M T W a hM hT hSep hBase ha
  have hC_A : A ≤ C := le_max_left _ _
  have hC_B : B ≤ C := le_max_right _ _
  have hCoeffC : ∀ m : ℕ, 0 < m →
      ‖finitePowCoeff M k a m‖ ≤ C * (m : ℝ) ^ η := by
    intro m hm
    exact (hCoeff M a ha m hm).trans
      (mul_le_mul_of_nonneg_right hC_A (Real.rpow_nonneg (by positivity) _))
  let U : ℕ := 2 ^ k * M ^ k
  let D : ℝ := C * (U : ℝ) ^ η
  have hU : 0 < U := by dsimp only [U]; positivity
  have hD : 0 < D := by
    dsimp only [D, U]
    positivity
  have hTOne : 1 ≤ T := hT_min.trans hT
  have hTNonneg : 0 ≤ T := zero_le_one.trans hTOne
  have hEach : ∀ r ∈ Finset.range k,
      gmDifferenceMoment (2 ^ r * M ^ k) W (finitePowCoeff M k a) ≤
        D ^ 2 * (C * T ^ η *
          ((W.card : ℝ) ^ 2 * U +
            (W.card : ℝ) * U ^ 2 +
            (W.card : ℝ) ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ) * U)) := by
    intro r hr
    have hrk : r < k := Finset.mem_range.mp hr
    let Q : ℕ := 2 ^ r * M ^ k
    have hQ : 0 < Q := by dsimp only [Q]; positivity
    have hQU : Q ≤ U := by
      dsimp only [Q, U]
      exact Nat.mul_le_mul_right _
        (pow_le_pow_right₀ (by omega : (1 : ℕ) ≤ 2) hrk.le)
    have hUnit : ∀ m ∈ dyadicInterval Q,
        ‖gmNormalizedPoweredCoeffs M k a C η m‖ ≤ 1 := by
      intro m hm
      have hmWide : m ∈ Finset.Ioc (M ^ k) U := by
        simpa only [Q, U] using
          heathBrown_poweredBlock_subset M k r m hrk hm
      exact norm_gmNormalizedPoweredCoeffs_le_one M k m a C η
        hM (lt_of_lt_of_le hA hC_A) hη hmWide (hCoeffC m (by
          rw [Finset.mem_Ioc] at hmWide
          omega))
    have hRaw := hHB Q T W
      (gmNormalizedPoweredCoeffs M k a C η)
      hQ hT hSep hBase hUnit
    have hRawC : gmDifferenceMoment Q W
        (gmNormalizedPoweredCoeffs M k a C η) ≤
        C * T ^ η *
          ((W.card : ℝ) ^ 2 * U +
            (W.card : ℝ) * U ^ 2 +
            (W.card : ℝ) ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ) * U) := by
      have hCoreQNonneg : 0 ≤
          (W.card : ℝ) ^ 2 * Q +
            (W.card : ℝ) * Q ^ 2 +
            (W.card : ℝ) ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ) * Q := by
        positivity
      have hCTNonneg : 0 ≤ C * T ^ η := by positivity
      have hTailNonneg : 0 ≤
          (W.card : ℝ) ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ) := by
        positivity
      calc
        _ ≤ B * T ^ η *
            ((W.card : ℝ) ^ 2 * Q +
              (W.card : ℝ) * Q ^ 2 +
              (W.card : ℝ) ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ) * Q) := by
          simpa only [gmDifferenceMoment, dyadicInterval] using hRaw
        _ ≤ C * T ^ η *
            ((W.card : ℝ) ^ 2 * U +
              (W.card : ℝ) * U ^ 2 +
              (W.card : ℝ) ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ) * U) := by
          gcongr
    rw [gmDifferenceMoment_normalizedPowered Q M k W a C η hD]
    exact mul_le_mul_of_nonneg_left hRawC (sq_nonneg D)
  have hBlocks := sum_norm_gmPoweredWide_sq_le_blocks M k W a
  have hIdentity := sum_norm_gmPoweredWide_sq M k W a hM hk
  have hSum :
      (∑ r ∈ Finset.range k,
        gmDifferenceMoment (2 ^ r * M ^ k) W (finitePowCoeff M k a)) ≤
      (k : ℝ) * (D ^ 2 * (C * T ^ η *
        ((W.card : ℝ) ^ 2 * U +
          (W.card : ℝ) * U ^ 2 +
          (W.card : ℝ) ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ) * U))) := by
    calc
      _ ≤ ∑ _r ∈ Finset.range k,
          D ^ 2 * (C * T ^ η *
            ((W.card : ℝ) ^ 2 * U +
              (W.card : ℝ) * U ^ 2 +
              (W.card : ℝ) ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ) * U)) :=
        Finset.sum_le_sum hEach
      _ = _ := by simp
  have hPower : gmDifferencePowerMoment M k W a ≤
      (k : ℝ) ^ 2 * D ^ 2 * (C * T ^ η *
        ((W.card : ℝ) ^ 2 * U +
          (W.card : ℝ) * U ^ 2 +
          (W.card : ℝ) ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ) * U)) := by
    rw [← hIdentity]
    calc
      _ ≤ (k : ℝ) * ∑ r ∈ Finset.range k,
          gmDifferenceMoment (2 ^ r * M ^ k) W
            (finitePowCoeff M k a) := hBlocks
      _ ≤ (k : ℝ) * ((k : ℝ) * (D ^ 2 * (C * T ^ η *
          ((W.card : ℝ) ^ 2 * U +
            (W.card : ℝ) * U ^ 2 +
            (W.card : ℝ) ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ) * U)))) := by
        gcongr
      _ = _ := by ring
  calc
    gmDifferenceMoment M W a ^ k ≤
        ((W.card : ℝ) ^ 2) ^ (k - 1) *
          gmDifferencePowerMoment M k W a :=
      gmDifferenceMoment_pow_le M k W a hk
    _ ≤ ((W.card : ℝ) ^ 2) ^ (k - 1) *
        ((k : ℝ) ^ 2 * D ^ 2 * (C * T ^ η *
          ((W.card : ℝ) ^ 2 * U +
            (W.card : ℝ) * U ^ 2 +
            (W.card : ℝ) ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ) * U))) := by
      gcongr
    _ = _ := by
      dsimp only [D, U]
      ring

/-! ## Taking the fixed `k`-th root -/

theorem le_rpow_inv_nat_of_pow_le
    {x y : ℝ} {k : ℕ} (hx : 0 ≤ x)
    (hk : 0 < k) (hxy : x ^ k ≤ y) :
    x ≤ y ^ (1 / (k : ℝ)) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hRoot := Real.rpow_le_rpow (pow_nonneg hx k) hxy
    (by positivity : 0 ≤ (1 / (k : ℝ)))
  calc
    x = (x ^ k) ^ (1 / (k : ℝ)) := by
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul hx]
      have hkNe : (k : ℝ) ≠ 0 := ne_of_gt hkR
      have hExp : (k : ℝ) * (1 / (k : ℝ)) = 1 := by
        field_simp
      rw [hExp, Real.rpow_one]
    _ ≤ y ^ (1 / (k : ℝ)) := hRoot

theorem pow_rpow_inv_nat
    {x : ℝ} {k : ℕ} (hx : 0 ≤ x) (hk : 0 < k) :
    (x ^ k) ^ (1 / (k : ℝ)) = x := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hkNe : (k : ℝ) ≠ 0 := ne_of_gt hkR
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul hx]
  have hExp : (k : ℝ) * (1 / (k : ℝ)) = 1 := by field_simp
  rw [hExp, Real.rpow_one]

theorem gm_first_root_identity
    {P R U : ℝ} {k : ℕ}
    (hP : 0 ≤ P) (hU : 0 ≤ U) (hk : 0 < k) :
    (((R ^ 2) ^ (k - 1) * P) * (R ^ 2 * U)) ^
        (1 / (k : ℝ)) =
      P ^ (1 / (k : ℝ)) * R ^ 2 * U ^ (1 / (k : ℝ)) := by
  have hkSub : k - 1 + 1 = k := Nat.sub_add_cancel hk
  have hRsq : 0 ≤ R ^ 2 := sq_nonneg R
  have hRpow : (R ^ 2) ^ (k - 1) * R ^ 2 = (R ^ 2) ^ k := by
    conv_lhs => rhs; rw [← pow_one (R ^ 2)]
    rw [← pow_add, hkSub]
  rw [show ((R ^ 2) ^ (k - 1) * P) * (R ^ 2 * U) =
      P * ((R ^ 2) ^ k * U) by rw [← hRpow]; ring]
  rw [Real.mul_rpow hP (mul_nonneg (pow_nonneg hRsq k) hU),
    Real.mul_rpow (pow_nonneg hRsq k) hU,
    pow_rpow_inv_nat hRsq hk]
  ring

theorem gm_r_exponent_second_identity
    {R : ℝ} {k : ℕ} (hR : 0 < R) (hk : 0 < k) :
    ((R ^ 2) ^ (k - 1) * R) ^ (1 / (k : ℝ)) =
      R ^ (2 - 1 / (k : ℝ)) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hkSub : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    have hNat := congrArg (fun n : ℕ => (n : ℝ))
      (Nat.sub_add_cancel hk)
    push_cast at hNat
    linarith
  have hbase : (R ^ 2) ^ (k - 1) * R =
      R ^ (2 * (k - 1) + 1) := by
    rw [← pow_mul]
    conv_lhs => rhs; rw [← pow_one R]
    rw [← pow_add]
  rw [hbase, ← Real.rpow_natCast R (2 * (k - 1) + 1)]
  rw [← Real.rpow_mul hR.le]
  congr 1
  push_cast
  rw [hkSub]
  field_simp
  ring

theorem gm_r_exponent_third_identity
    {R : ℝ} {k : ℕ} (hR : 0 < R) (hk : 0 < k) :
    ((R ^ 2) ^ (k - 1) * R ^ (5 / 4 : ℝ)) ^
        (1 / (k : ℝ)) =
      R ^ (2 - 3 / (4 * (k : ℝ))) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hkSub : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    have hNat := congrArg (fun n : ℕ => (n : ℝ))
      (Nat.sub_add_cancel hk)
    push_cast at hNat
    linarith
  rw [← Real.rpow_natCast (R ^ 2) (k - 1),
    ← Real.rpow_natCast R 2]
  rw [← Real.rpow_mul hR.le]
  rw [← Real.rpow_add hR]
  rw [← Real.rpow_mul hR.le]
  congr 1
  rw [hkSub]
  field_simp
  ring

/-- The second Heath--Brown contribution after taking the fixed `k`-th
root.  This is the exact source exponent `2 - 1/k` in (6.4). -/
theorem gm_second_root_identity
    {P R U : ℝ} {k : ℕ}
    (hP : 0 ≤ P) (hR : 0 < R) (hU : 0 ≤ U) (hk : 0 < k) :
    (((R ^ 2) ^ (k - 1) * P) * (R * U ^ 2)) ^
        (1 / (k : ℝ)) =
      P ^ (1 / (k : ℝ)) * R ^ (2 - 1 / (k : ℝ)) *
        U ^ (2 / (k : ℝ)) := by
  have hRfactor : 0 ≤ (R ^ 2) ^ (k - 1) * R := by positivity
  have hUsq : 0 ≤ U ^ 2 := sq_nonneg U
  rw [show ((R ^ 2) ^ (k - 1) * P) * (R * U ^ 2) =
      P * (((R ^ 2) ^ (k - 1) * R) * U ^ 2) by ring]
  rw [Real.mul_rpow hP (mul_nonneg hRfactor hUsq),
    Real.mul_rpow hRfactor hUsq,
    gm_r_exponent_second_identity hR hk]
  rw [← Real.rpow_natCast U 2, ← Real.rpow_mul hU]
  have hUExp : U ^ (((2 : ℕ) : ℝ) * (1 / (k : ℝ))) =
      U ^ (2 / (k : ℝ)) := by
    congr 1
    norm_num
    ring
  rw [hUExp]
  ring

/-- The third Heath--Brown contribution after taking the fixed `k`-th
root.  Both the `R^(2-3/(4k))` and `T^(1/(2k))` factors are retained
literally. -/
theorem gm_third_root_identity
    {P R T U : ℝ} {k : ℕ}
    (hP : 0 ≤ P) (hR : 0 < R) (hT : 0 ≤ T)
    (hU : 0 ≤ U) (hk : 0 < k) :
    (((R ^ 2) ^ (k - 1) * P) *
        (R ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ) * U)) ^
          (1 / (k : ℝ)) =
      P ^ (1 / (k : ℝ)) * R ^ (2 - 3 / (4 * (k : ℝ))) *
        T ^ (1 / (2 * (k : ℝ))) * U ^ (1 / (k : ℝ)) := by
  have hRfactor : 0 ≤ (R ^ 2) ^ (k - 1) * R ^ (5 / 4 : ℝ) := by
    positivity
  have hTfactor : 0 ≤ T ^ (1 / 2 : ℝ) := Real.rpow_nonneg hT _
  rw [show ((R ^ 2) ^ (k - 1) * P) *
      (R ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ) * U) =
        P * (((R ^ 2) ^ (k - 1) * R ^ (5 / 4 : ℝ)) *
          (T ^ (1 / 2 : ℝ) * U)) by ring]
  rw [Real.mul_rpow hP (mul_nonneg hRfactor (mul_nonneg hTfactor hU)),
    Real.mul_rpow hRfactor (mul_nonneg hTfactor hU),
    gm_r_exponent_third_identity hR hk,
    Real.mul_rpow hTfactor hU]
  rw [← Real.rpow_mul hT]
  have hExp : (1 / 2 : ℝ) * (1 / (k : ℝ)) =
      1 / (2 * (k : ℝ)) := by ring
  rw [hExp]
  ring

theorem rpow_inv_nat_add_three_le
    {A B C : ℝ} {k : ℕ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hk : 0 < k) :
    (A + B + C) ^ (1 / (k : ℝ)) ≤
      A ^ (1 / (k : ℝ)) + B ^ (1 / (k : ℝ)) +
        C ^ (1 / (k : ℝ)) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hExp0 : 0 ≤ (1 / (k : ℝ)) := by positivity
  have hExp1 : 1 / (k : ℝ) ≤ 1 := by
    rw [div_le_one hkR]
    exact_mod_cast hk
  calc
    (A + B + C) ^ (1 / (k : ℝ)) ≤
        (A + B) ^ (1 / (k : ℝ)) + C ^ (1 / (k : ℝ)) :=
      Real.rpow_add_le_add_rpow (add_nonneg hA hB) hC hExp0 hExp1
    _ ≤ (A ^ (1 / (k : ℝ)) + B ^ (1 / (k : ℝ))) +
        C ^ (1 / (k : ℝ)) := by
      gcongr
      exact Real.rpow_add_le_add_rpow hA hB hExp0 hExp1
    _ = _ := by ring

/-- Root form of (6.2)--(6.3), with the three Heath--Brown contributions
kept separate for the subsequent exponent calculation. -/
theorem gmDifferenceMoment_le_heathBrown_roots
    (k : ℕ) (η : ℝ) (hk : 0 < k) (hη : 0 < η) :
    ∃ C T_min : ℝ, 0 < C ∧ 1 ≤ T_min ∧
      ∀ {M : ℕ} {T : ℝ} (W : Finset ℝ) (a : ℕ → ℂ),
        0 < M → T_min ≤ T → IsSeparated 1 W → InBaseInterval T W →
        (∀ n ∈ dyadicInterval M, ‖a n‖ ≤ 1) →
        let R : ℝ := W.card
        let U : ℝ := (2 ^ k * M ^ k : ℕ)
        let F : ℝ := (R ^ 2) ^ (k - 1) * (k : ℝ) ^ 2 *
          C * T ^ η * (C * U ^ η) ^ 2
        gmDifferenceMoment M W a ≤
          (F * (R ^ 2 * U)) ^ (1 / (k : ℝ)) +
            (F * (R * U ^ 2)) ^ (1 / (k : ℝ)) +
            (F * (R ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ) * U)) ^
              (1 / (k : ℝ)) := by
  obtain ⟨C, T_min, hC, hT_min, hPow⟩ :=
    gmDifferenceMoment_pow_le_heathBrown k η hk hη
  refine ⟨C, T_min, hC, hT_min, ?_⟩
  intro M T W a hM hT hSep hBase ha
  let R : ℝ := W.card
  let U : ℝ := (2 ^ k * M ^ k : ℕ)
  let F : ℝ := (R ^ 2) ^ (k - 1) * (k : ℝ) ^ 2 *
    C * T ^ η * (C * U ^ η) ^ 2
  have hTOne : 1 ≤ T := hT_min.trans hT
  have hTNonneg : 0 ≤ T := zero_le_one.trans hTOne
  have hF : 0 ≤ F := by dsimp only [F, R, U]; positivity
  have hA : 0 ≤ F * (R ^ 2 * U) := by positivity
  have hB : 0 ≤ F * (R * U ^ 2) := by positivity
  have hD : 0 ≤ F *
      (R ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ) * U) := by positivity
  have hPow' : gmDifferenceMoment M W a ^ k ≤
      F * (R ^ 2 * U) + F * (R * U ^ 2) +
        F * (R ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ) * U) := by
    have hRaw := hPow W a hM hT hSep hBase ha
    dsimp only [F, R, U]
    convert hRaw using 1
    all_goals ring
  calc
    gmDifferenceMoment M W a ≤
        (F * (R ^ 2 * U) + F * (R * U ^ 2) +
          F * (R ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ) * U)) ^
            (1 / (k : ℝ)) :=
      le_rpow_inv_nat_of_pow_le (gmDifferenceMoment_nonneg M W a)
        hk hPow'
    _ ≤ (F * (R ^ 2 * U)) ^ (1 / (k : ℝ)) +
          (F * (R * U ^ 2)) ^ (1 / (k : ℝ)) +
          (F * (R ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ) * U)) ^
            (1 / (k : ℝ)) :=
      rpow_inv_nat_add_three_le hA hB hD hk

/-- Source-exponent form of equations (6.2)--(6.3).  The sole common
factor `P^(1/k)` contains the fixed-power divisor loss and is isolated for
the subsequent epsilon budget. -/
theorem gmDifferenceMoment_le_heathBrown_source_exponents
    (k : ℕ) (η : ℝ) (hk : 0 < k) (hη : 0 < η) :
    ∃ C T_min : ℝ, 0 < C ∧ 1 ≤ T_min ∧
      ∀ {M : ℕ} {T : ℝ} (W : Finset ℝ) (a : ℕ → ℂ),
        0 < M → T_min ≤ T → IsSeparated 1 W → InBaseInterval T W →
        W.Nonempty →
        (∀ n ∈ dyadicInterval M, ‖a n‖ ≤ 1) →
        let R : ℝ := W.card
        let U : ℝ := (2 ^ k * M ^ k : ℕ)
        let P : ℝ := (k : ℝ) ^ 2 * C * T ^ η * (C * U ^ η) ^ 2
        gmDifferenceMoment M W a ≤
          P ^ (1 / (k : ℝ)) *
            (R ^ 2 * U ^ (1 / (k : ℝ)) +
              R ^ (2 - 1 / (k : ℝ)) * U ^ (2 / (k : ℝ)) +
              R ^ (2 - 3 / (4 * (k : ℝ))) *
                T ^ (1 / (2 * (k : ℝ))) * U ^ (1 / (k : ℝ))) := by
  obtain ⟨C, T_min, hC, hT_min, hRoot⟩ :=
    gmDifferenceMoment_le_heathBrown_roots k η hk hη
  refine ⟨C, T_min, hC, hT_min, ?_⟩
  intro M T W a hM hT hSep hBase hW ha
  let R : ℝ := W.card
  let U : ℝ := (2 ^ k * M ^ k : ℕ)
  let P : ℝ := (k : ℝ) ^ 2 * C * T ^ η * (C * U ^ η) ^ 2
  have hTOne : 1 ≤ T := hT_min.trans hT
  have hTNonneg : 0 ≤ T := zero_le_one.trans hTOne
  have hP : 0 ≤ P := by dsimp only [P, U]; positivity
  have hU : 0 ≤ U := by dsimp only [U]; positivity
  have hR : 0 < R := by
    dsimp only [R]
    exact_mod_cast hW.card_pos
  have hRaw := hRoot W a hM hT hSep hBase ha
  have hRaw' : gmDifferenceMoment M W a ≤
        (((R ^ 2) ^ (k - 1) * P) * (R ^ 2 * U)) ^ (1 / (k : ℝ)) +
          (((R ^ 2) ^ (k - 1) * P) * (R * U ^ 2)) ^ (1 / (k : ℝ)) +
          (((R ^ 2) ^ (k - 1) * P) *
            (R ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ) * U)) ^
              (1 / (k : ℝ)) := by
    simpa only [R, U, P, mul_assoc, mul_left_comm, mul_comm] using hRaw
  calc
    gmDifferenceMoment M W a ≤
        (((R ^ 2) ^ (k - 1) * P) * (R ^ 2 * U)) ^ (1 / (k : ℝ)) +
          (((R ^ 2) ^ (k - 1) * P) * (R * U ^ 2)) ^ (1 / (k : ℝ)) +
          (((R ^ 2) ^ (k - 1) * P) *
            (R ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ) * U)) ^
              (1 / (k : ℝ)) := hRaw'
    _ = P ^ (1 / (k : ℝ)) *
        (R ^ 2 * U ^ (1 / (k : ℝ)) +
          R ^ (2 - 1 / (k : ℝ)) * U ^ (2 / (k : ℝ)) +
          R ^ (2 - 3 / (4 * (k : ℝ))) *
            T ^ (1 / (2 * (k : ℝ))) * U ^ (1 / (k : ℝ))) := by
      rw [gm_first_root_identity hP hU hk,
        gm_second_root_identity hP hR hU hk,
        gm_third_root_identity hP hR hTNonneg hU hk]
      ring

/-- Common source-exponent majorant for an arbitrary coefficient block.
The scale argument is monotone and will be replaced by the terminal prefix
length after the exact dyadic decomposition. -/
noncomputable def gmPoweredDifferenceSourceBound
    (C : ℝ) (k : ℕ) (η T : ℝ) (W : Finset ℝ) (M : ℕ) : ℝ :=
  let R : ℝ := W.card
  let U : ℝ := (2 ^ k * M ^ k : ℕ)
  let P : ℝ := (k : ℝ) ^ 2 * C * T ^ η * (C * U ^ η) ^ 2
  P ^ (1 / (k : ℝ)) *
    (R ^ 2 * U ^ (1 / (k : ℝ)) +
      R ^ (2 - 1 / (k : ℝ)) * U ^ (2 / (k : ℝ)) +
      R ^ (2 - 3 / (4 * (k : ℝ))) *
        T ^ (1 / (2 * (k : ℝ))) * U ^ (1 / (k : ℝ)))

theorem gmPoweredDifferenceSourceBound_nonneg
    {C : ℝ} {k : ℕ} {η T : ℝ} {W : Finset ℝ} {M : ℕ}
    (hC : 0 ≤ C) (hk : 0 < k) (hT : 0 ≤ T) :
    0 ≤ gmPoweredDifferenceSourceBound C k η T W M := by
  unfold gmPoweredDifferenceSourceBound
  positivity

theorem gmPoweredDifferenceSourceBound_mono_scale
    {C : ℝ} {k M M' : ℕ} {η T : ℝ} {W : Finset ℝ}
    (hC : 0 ≤ C) (hk : 0 < k) (hη : 0 ≤ η)
    (hT : 0 ≤ T) (hMM' : M ≤ M') :
    gmPoweredDifferenceSourceBound C k η T W M ≤
      gmPoweredDifferenceSourceBound C k η T W M' := by
  have hUNat : 2 ^ k * M ^ k ≤ 2 ^ k * M' ^ k := by gcongr
  have hU : ((2 ^ k * M ^ k : ℕ) : ℝ) ≤
      ((2 ^ k * M' ^ k : ℕ) : ℝ) := by exact_mod_cast hUNat
  have hExpOne : 0 ≤ (1 / (k : ℝ)) := by positivity
  have hExpTwo : 0 ≤ (2 / (k : ℝ)) := by positivity
  unfold gmPoweredDifferenceSourceBound
  dsimp only
  gcongr

/-- Uniform terminal-scale form of equations (6.2)--(6.3). -/
theorem gmDifferenceMoment_le_heathBrown_terminal_scale
    (k : ℕ) (η : ℝ) (hk : 0 < k) (hη : 0 < η) :
    ∃ C T_min : ℝ, 0 < C ∧ 1 ≤ T_min ∧
      ∀ {M M' : ℕ} {T : ℝ} (W : Finset ℝ) (a : ℕ → ℂ),
        0 < M → M ≤ M' → T_min ≤ T →
        IsSeparated 1 W → InBaseInterval T W → W.Nonempty →
        (∀ n ∈ dyadicInterval M, ‖a n‖ ≤ 1) →
        gmDifferenceMoment M W a ≤
          gmPoweredDifferenceSourceBound C k η T W M' := by
  obtain ⟨C, T_min, hC, hT_min, hSource⟩ :=
    gmDifferenceMoment_le_heathBrown_source_exponents k η hk hη
  refine ⟨C, T_min, hC, hT_min, ?_⟩
  intro M M' T W a hM hMM' hT hSep hBase hW ha
  have hTNonneg : 0 ≤ T := zero_le_one.trans (hT_min.trans hT)
  exact (hSource W a hM hT hSep hBase hW ha).trans
    (gmPoweredDifferenceSourceBound_mono_scale hC.le hk hη.le
      hTNonneg hMM')

/-- The reflected-prefix moment after the genuine arbitrary-coefficient
powering argument.  Every dyadic prefix block is bounded at the common
terminal scale `M`; the two displayed logarithmic factors are the exact
finite dyadic losses preceding epsilon absorption. -/
theorem heathBrownReflectionDyadicMoment_le_powered
    (k : ℕ) (η : ℝ) (hk : 0 < k) (hη : 0 < η) :
    ∃ C T_min : ℝ, 0 < C ∧ 1 ≤ T_min ∧
      ∀ {M : ℕ} {T : ℝ} (W : Finset ℝ),
        0 < M → T_min ≤ T → IsSeparated 1 W →
        InBaseInterval T W → W.Nonempty →
        heathBrownReflectionDyadicMoment W M ≤
          2 * ((Nat.clog 2 M : ℝ) + 1) *
            ((W.card : ℝ) ^ 2 +
              (Nat.clog 2 M : ℝ) *
                gmPoweredDifferenceSourceBound C k η T W M) := by
  obtain ⟨C, T_min, hC, hT_min, hTerminal⟩ :=
    gmDifferenceMoment_le_heathBrown_terminal_scale k η hk hη
  refine ⟨C, T_min, hC, hT_min, ?_⟩
  intro M T W hM hT hSep hBase hW
  let L : ℕ := Nat.clog 2 M
  let B : ℝ := gmPoweredDifferenceSourceBound C k η T W M
  have hB : 0 ≤ B := by
    exact gmPoweredDifferenceSourceBound_nonneg hC.le hk
      (zero_le_one.trans (hT_min.trans hT))
  have hEach : ∀ r ∈ Finset.range L,
      heathBrownCoefficientOneMoment (2 ^ r) W ≤ B := by
    intro r hr
    have hrL : r < Nat.clog 2 M := by
      simpa only [L] using Finset.mem_range.mp hr
    have hScale : 2 ^ r ≤ M := (Nat.pow_lt_of_lt_clog hrL).le
    have hAt := hTerminal W (fun _ => (1 : ℂ)) (by positivity) hScale
      hT hSep hBase hW (by intro n hn; simp)
    simpa only [heathBrownCoefficientOneMoment, gmDifferenceMoment, B] using hAt
  have hSum :
      (∑ r ∈ Finset.range L,
          heathBrownCoefficientOneMoment (2 ^ r) W) ≤ (L : ℝ) * B := by
    calc
      _ ≤ ∑ _r ∈ Finset.range L, B := Finset.sum_le_sum hEach
      _ = (L : ℝ) * B := by simp
  rw [heathBrownReflectionDyadicMoment_eq]
  dsimp only [L, B] at hSum ⊢
  gcongr

/-- Fixed-bin form of Guth--Maynard (6.1) with the powered
Heath--Brown estimate inserted.  This theorem consumes the literal complete
nonzero Fourier tail and retains the two quantitative reflection errors. -/
theorem gmNonzeroTailBinMoment_le_powered_reflection
    (cutoff : GMSmoothCutoff) (q k : ℕ) (hq : 2 ≤ q)
    (η : ℝ) (hk : 0 < k) (hη : 0 < η) :
    ∃ A K L C T_min : ℝ,
      0 < A ∧ 0 < K ∧ 0 < L ∧ 0 < C ∧ 1 ≤ T_min ∧
      ∀ {T : ℝ} {W : Finset ℝ} {j N M : ℕ} {H : ℝ},
        T_min ≤ T → IsSeparated 1 W → InBaseInterval T W →
        W.Nonempty → 2 ≤ j → 1 ≤ H →
        H ≤ ((2 ^ j : ℕ) : ℝ) / 2 → 0 < N → 0 < M →
        gmNonzeroTailBinMoment cutoff N W j ≤
          2 * (((N : ℝ) * A / Real.sqrt ((2 ^ j : ℕ) : ℝ)) ^ 2) *
              ((2 * H) ^ 2 *
                (2 * ((Nat.clog 2 M : ℝ) + 1) *
                  ((W.card : ℝ) ^ 2 +
                    (Nat.clog 2 M : ℝ) *
                      gmPoweredDifferenceSourceBound C k η T W M))) +
            2 * ((heathBrownDifferenceBin W j).card : ℝ) *
              (gmNonzeroTailBinError q N M H
                (((2 ^ (j + 1) : ℕ) : ℝ)) K L) ^ 2 := by
  obtain ⟨A, K, L, hA, hK, hL, hReflect⟩ :=
    gmNonzeroTailBinMoment_le_reflection cutoff q hq
  obtain ⟨C, T_min, hC, hT_min, hPowered⟩ :=
    heathBrownReflectionDyadicMoment_le_powered k η hk hη
  refine ⟨A, K, L, C, T_min, hA, hK, hL, hC, hT_min, ?_⟩
  intro T W j N M H hT hSep hBase hW hj hH hHupper hN hM
  have hRaw := hReflect hSep hj hH hHupper hN hM
  have hMoment := hPowered W hM hT hSep hBase hW
  calc
    gmNonzeroTailBinMoment cutoff N W j ≤
        2 * (((N : ℝ) * A / Real.sqrt ((2 ^ j : ℕ) : ℝ)) ^ 2) *
            ((2 * H) ^ 2 * heathBrownReflectionDyadicMoment W M) +
          2 * ((heathBrownDifferenceBin W j).card : ℝ) *
            (gmNonzeroTailBinError q N M H
              (((2 ^ (j + 1) : ℕ) : ℝ)) K L) ^ 2 := hRaw
    _ ≤ 2 * (((N : ℝ) * A /
            Real.sqrt ((2 ^ j : ℕ) : ℝ)) ^ 2) *
              ((2 * H) ^ 2 *
                (2 * ((Nat.clog 2 M : ℝ) + 1) *
                  ((W.card : ℝ) ^ 2 +
                    (Nat.clog 2 M : ℝ) *
                      gmPoweredDifferenceSourceBound C k η T W M))) +
            2 * ((heathBrownDifferenceBin W j).card : ℝ) *
              (gmNonzeroTailBinError q N M H
                (((2 ^ (j + 1) : ℕ) : ℝ)) K L) ^ 2 := by
      gcongr

/-- Elementary contribution of coincident ordinates to the complete
nonzero-tail difference moment. -/
theorem gmTraceNonzeroDiagonalMoment_le
    (cutoff : GMSmoothCutoff) (q : ℕ) (hq : 2 ≤ q) :
    ∃ B : ℝ, 0 < B ∧ ∀ {N : ℕ} (W : Finset ℝ), 0 < N →
      gmTraceNonzeroDiagonalMoment cutoff N W ≤
        (W.card : ℝ) * (B / (N : ℝ) ^ (q - 1)) ^ 2 := by
  obtain ⟨B, hB, hTail⟩ := gmTraceNonzeroTailAt_bound cutoff q hq
  refine ⟨B, hB, ?_⟩
  intro N W hN
  unfold gmTraceNonzeroDiagonalMoment
  calc
    (∑ t ∈ W, ‖gmTraceNonzeroTailAt cutoff N (t - t)‖ ^ 2) ≤
        ∑ _t ∈ W, (B / (N : ℝ) ^ (q - 1)) ^ 2 := by
      apply Finset.sum_le_sum
      intro t ht
      have hAt := hTail N hN (t - t)
      simp only [sub_self, abs_zero, add_zero, one_pow, mul_one] at hAt
      simpa only [sub_self] using
        (pow_le_pow_left₀ (norm_nonneg _) hAt 2)
    _ = (W.card : ℝ) * (B / (N : ℝ) ^ (q - 1)) ^ 2 := by simp

/-- The explicit powered-reflection majorant attached to one physical
difference bin. -/
noncomputable def gmS2PoweredBinBound
    (A K L C : ℝ) (q k : ℕ) (η : ℝ)
    (N : ℕ) (T : ℝ) (W : Finset ℝ) (H j : ℕ) : ℝ :=
  let M := heathBrownFixedReflectionLength N H j
  2 * (((N : ℝ) * A / Real.sqrt ((2 ^ j : ℕ) : ℝ)) ^ 2) *
      ((2 * (H : ℝ)) ^ 2 *
        (2 * ((Nat.clog 2 M : ℝ) + 1) *
          ((W.card : ℝ) ^ 2 +
            (Nat.clog 2 M : ℝ) *
              gmPoweredDifferenceSourceBound C k η T W M))) +
    2 * ((heathBrownDifferenceBin W j).card : ℝ) *
      (gmNonzeroTailBinError q N M H
        (((2 ^ (j + 1) : ℕ) : ℝ)) K L) ^ 2

theorem gmS2PoweredBinBound_nonneg
    {A K L C : ℝ} {q k N H j : ℕ} {η T : ℝ} {W : Finset ℝ}
    (hC : 0 ≤ C) (hk : 0 < k) (hT : 0 ≤ T) :
    0 ≤ gmS2PoweredBinBound A K L C q k η N T W H j := by
  unfold gmS2PoweredBinBound
  dsimp only
  have hSource := gmPoweredDifferenceSourceBound_nonneg
    (C := C) (k := k) (η := η) (T := T) (W := W)
    (M := heathBrownFixedReflectionLength N H j) hC hk hT
  positivity

/-- Exact finite scheduling theorem for the complete literal nonzero-tail
moment.  Source separation makes every occupied dyadic bin stationary;
the physical reflected length is chosen separately on each bin. -/
theorem gmTraceNonzeroDifferenceMoment_le_powered_schedule
    (cutoff : GMSmoothCutoff) (q k : ℕ) (hq : 2 ≤ q)
    (η : ℝ) (hk : 0 < k) (hη : 0 < η) :
    ∃ A K L C B T_min : ℝ,
      0 < A ∧ 0 < K ∧ 0 < L ∧ 0 < C ∧ 0 < B ∧
      1 ≤ T_min ∧
      ∀ {N H : ℕ} {T δ : ℝ} (W : Finset ℝ),
        T_min ≤ T → 0 < N → 0 < H → 4 * (H : ℝ) ≤ δ →
        IsSeparated δ W → InBaseInterval T W → W.Nonempty →
        gmTraceNonzeroDifferenceMoment cutoff N W ≤
          (W.card : ℝ) * (B / (N : ℝ) ^ (q - 1)) ^ 2 +
            ∑ j ∈ Finset.range (Nat.log 2 (Nat.floor T) + 1),
              gmS2PoweredBinBound A K L C q k η N T W H j := by
  obtain ⟨A, K, L, C, T_ref, hA, hK, hL, hC, hT_ref, hBin⟩ :=
    gmNonzeroTailBinMoment_le_powered_reflection cutoff q k hq η hk hη
  obtain ⟨B, hB, hDiag⟩ := gmTraceNonzeroDiagonalMoment_le cutoff q
    hq
  refine ⟨A, K, L, C, B, T_ref, hA, hK, hL, hC, hB, hT_ref, ?_⟩
  intro N H T δ W hT hN hH hHsep hSep hBase hW
  have hδOne : 1 ≤ δ := by
    have hHOne : (1 : ℝ) ≤ H := by exact_mod_cast hH
    linarith
  have hSepOne : IsSeparated 1 W := by
    intro x hx y hy hxy
    exact hδOne.trans (hSep x hx y hy hxy)
  have hTNonneg : 0 ≤ T := zero_le_one.trans (hT_ref.trans hT)
  have hEach : ∀ j ∈ Finset.range (Nat.log 2 (Nat.floor T) + 1),
      gmNonzeroTailBinMoment cutoff N W j ≤
        gmS2PoweredBinBound A K L C q k η N T W H j := by
    intro j hj
    by_cases hEmpty : (heathBrownDifferenceBin W j).Nonempty
    · obtain ⟨p, hp⟩ := hEmpty
      have hpFilter := Finset.mem_filter.mp hp
      have hpOff := Finset.mem_filter.mp hpFilter.1
      have hpW := Finset.mem_product.mp hpOff.1
      have hDelta : δ ≤ |p.1 - p.2| := by
        simpa only [Real.dist_eq] using
          hSep p.1 hpW.1 p.2 hpW.2 hpOff.2
      have hBounds := heathBrownDifferenceBin_bounds hSepOne hp
      have hjTwo : 2 ≤ j := by
        have hFour : (4 : ℝ) ≤ δ := by
          have hHOne : (1 : ℝ) ≤ H := by exact_mod_cast hH
          linarith
        by_contra hnot
        have hjSmall : j ≤ 1 := by omega
        interval_cases j <;> norm_num at hBounds ⊢ <;>
          linarith [hBounds.2, hDelta, hFour]
      have hHeightLower : (1 : ℝ) ≤ H := by exact_mod_cast hH
      have hHeightUpper : (H : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) / 2 := by
        have hPowSucc : (((2 ^ (j + 1) : ℕ) : ℝ)) =
            2 * (((2 ^ j : ℕ) : ℝ)) := by
          rw [pow_succ]
          norm_num
          ring
        rw [hPowSucc] at hBounds
        linarith
      have hAt := hBin hT hSepOne hBase hW hjTwo hHeightLower
        hHeightUpper hN (heathBrownFixedReflectionLength_pos N H j)
      simpa only [gmS2PoweredBinBound] using hAt
    · have hEq : heathBrownDifferenceBin W j = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp hEmpty
      have hBound := gmS2PoweredBinBound_nonneg
        (A := A) (K := K) (L := L) (C := C) (q := q) (k := k)
        (N := N) (H := H) (j := j) (η := η) (T := T) (W := W)
        hC.le hk hTNonneg
      simpa only [gmNonzeroTailBinMoment, hEq, Finset.sum_empty] using hBound
  rw [gmTraceNonzeroDifferenceMoment_eq_diagonal_add_bins hSepOne hBase]
  exact add_le_add (hDiag W hN) (Finset.sum_le_sum hEach)

set_option maxHeartbeats 400000 in
/-- Quantitative off-diagonal bound for the first cyclic `S₂` term.  The
two complete nonzero tails use Lemma 4.3 with order two, while the zero
mode on `v ≠ t` uses arbitrary-order separation decay. -/
theorem gmCubicS2FirstOffDiagonal_quantitative
    (cutoff : GMSmoothCutoff) (q : ℕ) :
    ∃ K : ℝ, 0 < K ∧
      ∀ {N : ℕ} {T δ : ℝ} (W : Finset ℝ),
        0 < N → 1 ≤ T → (N : ℝ) ≤ T → 0 < δ →
        IsSeparated δ W → InBaseInterval T W →
        ‖gmCubicS2FirstOffDiagonal cutoff N W‖ ≤
          K * (W.card : ℝ) ^ 3 * T ^ 5 / δ ^ q := by
  obtain ⟨B, hB, hTail⟩ := gmTraceNonzeroTailAt_bound cutoff 2 (by norm_num)
  obtain ⟨C, hC, hZero⟩ := gmTraceZeroMode_separated_bound cutoff q
  let K : ℝ := 16 * B ^ 2 * C
  refine ⟨K, by dsimp only [K]; positivity, ?_⟩
  intro N T δ W hN hT hNT hδ hSep hBase
  have hTPos : 0 < T := zero_lt_one.trans_le hT
  have hNOne : (1 : ℝ) ≤ N := by exact_mod_cast hN
  let major : ℝ := K * T ^ 5 / δ ^ q
  have hMajorNonneg : 0 ≤ major := by dsimp only [major, K]; positivity
  have hTerm : ∀ (t u v : GMRow W), v ≠ t →
      ‖gmCubicS2FirstSummand cutoff N t u v‖ ≤ major := by
    intro t u v hvt
    have htu := abs_sub_le_height_of_mem_baseInterval hBase
      t.property u.property
    have huv := abs_sub_le_height_of_mem_baseInterval hBase
      u.property v.property
    have hOneTu : 1 + |(t : ℝ) - (u : ℝ)| ≤ 2 * T := by linarith
    have hOneUv : 1 + |(u : ℝ) - (v : ℝ)| ≤ 2 * T := by linarith
    have hTuSq : (1 + |(t : ℝ) - (u : ℝ)|) ^ 2 ≤ 4 * T ^ 2 := by
      calc
        _ ≤ (2 * T) ^ 2 := pow_le_pow_left₀ (by positivity) hOneTu 2
        _ = 4 * T ^ 2 := by ring
    have hUvSq : (1 + |(u : ℝ) - (v : ℝ)|) ^ 2 ≤ 4 * T ^ 2 := by
      calc
        _ ≤ (2 * T) ^ 2 := pow_le_pow_left₀ (by positivity) hOneUv 2
        _ = 4 * T ^ 2 := by ring
    have hTailTuRaw := hTail N hN ((t : ℝ) - (u : ℝ))
    have hTailUvRaw := hTail N hN ((u : ℝ) - (v : ℝ))
    have hTailTu : ‖gmTraceNonzeroTailAt cutoff N ((t : ℝ) - (u : ℝ))‖ ≤
        4 * B * T ^ 2 := by
      calc
        _ ≤ B * (1 + |(t : ℝ) - (u : ℝ)|) ^ 2 /
            (N : ℝ) ^ (2 - 1) := hTailTuRaw
        _ = B * (1 + |(t : ℝ) - (u : ℝ)|) ^ 2 / (N : ℝ) := by norm_num
        _ ≤ B * (4 * T ^ 2) / (N : ℝ) := by gcongr
        _ ≤ B * (4 * T ^ 2) / 1 := by
          exact div_le_div_of_nonneg_left (by positivity) (by norm_num) hNOne
        _ = 4 * B * T ^ 2 := by ring
    have hTailUv : ‖gmTraceNonzeroTailAt cutoff N ((u : ℝ) - (v : ℝ))‖ ≤
        4 * B * T ^ 2 := by
      calc
        _ ≤ B * (1 + |(u : ℝ) - (v : ℝ)|) ^ 2 /
            (N : ℝ) ^ (2 - 1) := hTailUvRaw
        _ = B * (1 + |(u : ℝ) - (v : ℝ)|) ^ 2 / (N : ℝ) := by norm_num
        _ ≤ B * (4 * T ^ 2) / (N : ℝ) := by gcongr
        _ ≤ B * (4 * T ^ 2) / 1 := by
          exact div_le_div_of_nonneg_left (by positivity) (by norm_num) hNOne
        _ = 4 * B * T ^ 2 := by ring
    have htvSep : δ ≤ |(v : ℝ) - (t : ℝ)| := by
      have hvtReal : (v : ℝ) ≠ (t : ℝ) := by
        intro h
        exact hvt (Subtype.ext h)
      simpa only [Real.dist_eq] using hSep v v.property t t.property hvtReal
    have hZeroVt := hZero N hδ htvSep
    have hZeroVt' : ‖gmTraceZeroMode cutoff N ((v : ℝ) - (t : ℝ))‖ ≤
        T * C / δ ^ q := by
      calc
        _ ≤ (N : ℝ) * C / δ ^ q := hZeroVt
        _ ≤ T * C / δ ^ q := by gcongr
    unfold gmCubicS2FirstSummand
    simp only [norm_mul]
    calc
      _ ≤ (4 * B * T ^ 2) * (4 * B * T ^ 2) *
          (T * C / δ ^ q) := by gcongr
      _ = major := by
        dsimp only [major, K]
        ring
  unfold gmCubicS2FirstOffDiagonal
  calc
    ‖∑ t : GMRow W, ∑ u : GMRow W,
        ∑ v ∈ (Finset.univ.erase t : Finset (GMRow W)),
          gmCubicS2FirstSummand cutoff N t u v‖ ≤
        ∑ t : GMRow W, ‖∑ u : GMRow W,
          ∑ v ∈ (Finset.univ.erase t : Finset (GMRow W)),
            gmCubicS2FirstSummand cutoff N t u v‖ := norm_sum_le _ _
    _ ≤ ∑ t : GMRow W, ∑ u : GMRow W,
        ‖∑ v ∈ (Finset.univ.erase t : Finset (GMRow W)),
          gmCubicS2FirstSummand cutoff N t u v‖ := by
      apply Finset.sum_le_sum
      intro t ht
      exact norm_sum_le _ _
    _ ≤ ∑ t : GMRow W, ∑ u : GMRow W,
        ∑ v ∈ (Finset.univ.erase t : Finset (GMRow W)),
          ‖gmCubicS2FirstSummand cutoff N t u v‖ := by
      apply Finset.sum_le_sum
      intro t ht
      apply Finset.sum_le_sum
      intro u hu
      exact norm_sum_le _ _
    _ ≤ ∑ _t : GMRow W, ∑ _u : GMRow W,
        ∑ _v : GMRow W, major := by
      apply Finset.sum_le_sum
      intro t ht
      apply Finset.sum_le_sum
      intro u hu
      calc
        (∑ v ∈ (Finset.univ.erase t : Finset (GMRow W)),
            ‖gmCubicS2FirstSummand cutoff N t u v‖) ≤
            ∑ _v ∈ (Finset.univ.erase t : Finset (GMRow W)), major := by
          apply Finset.sum_le_sum
          intro v hv
          exact hTerm t u v (Finset.ne_of_mem_erase hv)
        _ ≤ ∑ _v : GMRow W, major := by
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
            (fun _ _ _ => hMajorNonneg)
    _ = (W.card : ℝ) ^ 3 * major := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe,
        nsmul_eq_mul]
      ring
    _ = K * (W.card : ℝ) ^ 3 * T ^ 5 / δ ^ q := by
      dsimp only [major]
      ring

/-- With the source `T^ε` separation, the off-diagonal zero-mode terms are
`O(T⁻¹⁰)`. -/
theorem gmCubicS2FirstOffDiagonal_power_decay
    (cutoff : GMSmoothCutoff) (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧
      ∀ {N : ℕ} {T : ℝ} (W : Finset ℝ),
        0 < N → 1 ≤ T → (N : ℝ) ≤ T →
        IsSeparated (T ^ ε) W → InBaseInterval T W →
        ‖gmCubicS2FirstOffDiagonal cutoff N W‖ ≤ K / T ^ 10 := by
  obtain ⟨q, hq⟩ := exists_nat_gt (18 / ε)
  have hqPos : 0 < q := by
    have : 0 < (q : ℝ) := (div_pos (by norm_num) hε).trans hq
    exact_mod_cast this
  obtain ⟨K₀, hK₀, hRaw⟩ :=
    gmCubicS2FirstOffDiagonal_quantitative cutoff q
  refine ⟨8 * K₀, by positivity, ?_⟩
  intro N T W hN hT hNT hSep hBase
  have hTPos : 0 < T := zero_lt_one.trans_le hT
  have hScalePos : 0 < T ^ ε := Real.rpow_pos_of_pos hTPos ε
  have hScaleOne : 1 ≤ T ^ ε := Real.one_le_rpow hT hε.le
  have hOneSep : IsSeparated 1 W := by
    intro x hx y hy hxy
    exact hScaleOne.trans (hSep x hx y hy hxy)
  have hCard := gmSeparated_card_le_two_height hT hOneSep hBase
  have hCardCube : (W.card : ℝ) ^ 3 ≤ 8 * T ^ 3 := by
    calc
      (W.card : ℝ) ^ 3 ≤ (2 * T) ^ 3 :=
        pow_le_pow_left₀ (by positivity) hCard 3
      _ = 8 * T ^ 3 := by ring
  have hExponent : 18 < ε * (q : ℝ) := by
    rw [div_lt_iff₀ hε] at hq
    nlinarith
  have hDeltaPow : (T ^ ε) ^ q = T ^ (ε * (q : ℝ)) := by
    rw [← Real.rpow_natCast, Real.rpow_mul hTPos.le]
  have hPowCompare : T ^ 8 * T ^ 10 ≤ T ^ (ε * (q : ℝ)) := by
    calc
      T ^ 8 * T ^ 10 = T ^ 18 := by ring
      _ = T ^ (18 : ℝ) := by norm_num
      _ ≤ T ^ (ε * (q : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le hT hExponent.le
  have hApplied := hRaw W hN hT hNT hScalePos hSep hBase
  calc
    _ ≤ K₀ * (W.card : ℝ) ^ 3 * T ^ 5 / (T ^ ε) ^ q := hApplied
    _ ≤ K₀ * (8 * T ^ 3) * T ^ 5 / (T ^ ε) ^ q := by gcongr
    _ ≤ 8 * K₀ / T ^ 10 := by
      rw [hDeltaPow]
      have hDenPos : 0 < T ^ (ε * (q : ℝ)) :=
        Real.rpow_pos_of_pos hTPos _
      rw [div_le_iff₀ hDenPos]
      have hT10Pos : 0 < T ^ 10 := pow_pos hTPos 10
      rw [div_mul_eq_mul_div, le_div_iff₀ hT10Pos]
      calc
        K₀ * (8 * T ^ 3) * T ^ 5 * T ^ 10 =
            8 * K₀ * (T ^ 8 * T ^ 10) := by ring
        _ ≤ 8 * K₀ * T ^ (ε * (q : ℝ)) := by gcongr
    _ = _ := by rfl

/-- The powered dyadic scale in equations (6.2)--(6.3) has the exact
`k`-th root `2M`.  Keeping this identity explicit prevents the later
epsilon budget from obscuring the physical reflected length. -/
theorem gm_powered_scale_rpow_inv
    (k M : ℕ) (hk : 0 < k) :
    (((2 ^ k * M ^ k : ℕ) : ℝ)) ^ (1 / (k : ℝ)) = 2 * M := by
  have hM : (0 : ℝ) ≤ M := by positivity
  norm_num only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  have hmul :
      (((2 : ℝ) ^ k * (M : ℝ) ^ k) ^ (1 / (k : ℝ))) =
        ((2 : ℝ) ^ k) ^ (1 / (k : ℝ)) *
          ((M : ℝ) ^ k) ^ (1 / (k : ℝ)) :=
    Real.mul_rpow (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) k)
      (pow_nonneg hM k)
  rw [hmul]
  rw [pow_rpow_inv_nat (by norm_num : (0 : ℝ) ≤ 2) hk,
    pow_rpow_inv_nat hM hk]

/-- The corresponding squared scale is `4M²`. -/
theorem gm_powered_scale_rpow_two_inv
    (k M : ℕ) (hk : 0 < k) :
    (((2 ^ k * M ^ k : ℕ) : ℝ)) ^ (2 / (k : ℝ)) = 4 * (M : ℝ) ^ 2 := by
  have hU : (0 : ℝ) ≤ ((2 ^ k * M ^ k : ℕ) : ℝ) := by positivity
  calc
    (((2 ^ k * M ^ k : ℕ) : ℝ)) ^ (2 / (k : ℝ)) =
        ((((2 ^ k * M ^ k : ℕ) : ℝ)) ^ (1 / (k : ℝ))) ^ 2 := by
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul hU]
      congr 1
      norm_num
      ring
    _ = (2 * (M : ℝ)) ^ 2 := by rw [gm_powered_scale_rpow_inv k M hk]
    _ = 4 * (M : ℝ) ^ 2 := by ring

/-- Equation (6.3) with the artificial powered scale eliminated.  The
remaining common factor is exactly the fixed-power divisor/epsilon loss. -/
theorem gmPoweredDifferenceSourceBound_eq_physical
    (C : ℝ) (k : ℕ) (η T : ℝ) (W : Finset ℝ) (M : ℕ) (hk : 0 < k) :
    gmPoweredDifferenceSourceBound C k η T W M =
      (((k : ℝ) ^ 2 * C * T ^ η *
          (C * (((2 ^ k * M ^ k : ℕ) : ℝ)) ^ η) ^ 2) ^
            (1 / (k : ℝ))) *
        ((W.card : ℝ) ^ 2 * (2 * M) +
          (W.card : ℝ) ^ (2 - 1 / (k : ℝ)) * (4 * (M : ℝ) ^ 2) +
          (W.card : ℝ) ^ (2 - 3 / (4 * (k : ℝ))) *
            T ^ (1 / (2 * (k : ℝ))) * (2 * M)) := by
  unfold gmPoweredDifferenceSourceBound
  dsimp only
  rw [gm_powered_scale_rpow_inv k M hk,
    gm_powered_scale_rpow_two_inv k M hk]

/-- Exact factorization of the common loss in (6.3). -/
theorem gm_powered_common_factor_eq
    {C η T : ℝ} {k M : ℕ} (hC : 0 ≤ C) (hT : 0 ≤ T)
    (hk : 0 < k) :
    (((k : ℝ) ^ 2 * C * T ^ η *
        (C * (((2 ^ k * M ^ k : ℕ) : ℝ)) ^ η) ^ 2) ^
          (1 / (k : ℝ))) =
      (((k : ℝ) ^ 2 * C ^ 3) ^ (1 / (k : ℝ))) *
        T ^ (η / (k : ℝ)) * (2 * (M : ℝ)) ^ (2 * η) := by
  let U : ℝ := ((2 ^ k * M ^ k : ℕ) : ℝ)
  have hU : 0 ≤ U := by dsimp only [U]; positivity
  have hconst : 0 ≤ (k : ℝ) ^ 2 * C ^ 3 := by positivity
  have hTpow : 0 ≤ T ^ η := Real.rpow_nonneg hT _
  have hUpow : 0 ≤ U ^ η := Real.rpow_nonneg hU _
  have hRewrite :
      (k : ℝ) ^ 2 * C * T ^ η * (C * U ^ η) ^ 2 =
        ((k : ℝ) ^ 2 * C ^ 3) * T ^ η * (U ^ η) ^ 2 := by ring
  rw [show (((2 ^ k * M ^ k : ℕ) : ℝ)) = U by rfl, hRewrite]
  rw [Real.mul_rpow (mul_nonneg hconst hTpow) (pow_nonneg hUpow 2),
    Real.mul_rpow hconst hTpow]
  have hTroot : (T ^ η) ^ (1 / (k : ℝ)) = T ^ (η / (k : ℝ)) := by
    rw [← Real.rpow_mul hT]
    congr 1
    ring
  rw [hTroot]
  have hUroot : ((U ^ η) ^ 2) ^ (1 / (k : ℝ)) =
      (2 * (M : ℝ)) ^ (2 * η) := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul hUpow, ← Real.rpow_mul hU]
    have hExp : η * ((2 : ℝ) * (1 / (k : ℝ))) =
        (1 / (k : ℝ)) * (2 * η) := by ring
    norm_num only [Nat.cast_ofNat]
    rw [hExp, Real.rpow_mul hU]
    rw [show U ^ (1 / (k : ℝ)) = 2 * (M : ℝ) by
      simpa only [U] using gm_powered_scale_rpow_inv k M hk]
  rw [hUroot]

/-! ## Physical-scale bounds for the dyadic Proposition 6.1 sum -/

/-- The stationary coefficient which precedes the powered difference-set
moment on one physical displacement bin. -/
noncomputable def gmS2ReflectionCoefficient
    (A : ℝ) (N H j : ℕ) : ℝ :=
  2 * (((N : ℝ) * A / Real.sqrt ((2 ^ j : ℕ) : ℝ)) ^ 2) *
    (2 * (H : ℝ)) ^ 2

theorem gmS2ReflectionCoefficient_eq
    (A : ℝ) (N H j : ℕ) :
    gmS2ReflectionCoefficient A N H j =
      8 * (N : ℝ) ^ 2 * A ^ 2 * H ^ 2 /
        ((2 ^ j : ℕ) : ℝ) := by
  let X : ℝ := ((2 ^ j : ℕ) : ℝ)
  have hX : 0 < X := by dsimp only [X]; positivity
  unfold gmS2ReflectionCoefficient
  change 2 * (((N : ℝ) * A / Real.sqrt X) ^ 2) *
      (2 * (H : ℝ)) ^ 2 = _
  rw [div_pow, Real.sq_sqrt hX.le]
  field_simp
  ring

/-- A single reflected length cancels one power of the source polynomial
scale.  This is the first and third physical terms of (6.4), before the
dyadic geometric sum and epsilon absorption. -/
theorem gmS2ReflectionCoefficient_mul_length_le
    {A X n h m : ℝ} (hX : 0 < X) (hn : 0 < n)
    (hh : 0 ≤ h) (hM : m ≤ X * h / n + 1) :
    (8 * n ^ 2 * A ^ 2 * h ^ 2 / X) * m ≤
      8 * A ^ 2 * (n * h ^ 3 + n ^ 2 * h ^ 2 / X) := by
  have hCoeff : 0 ≤ 8 * n ^ 2 * A ^ 2 * h ^ 2 / X := by positivity
  calc
    (8 * n ^ 2 * A ^ 2 * h ^ 2 / X) * m ≤
        (8 * n ^ 2 * A ^ 2 * h ^ 2 / X) * (X * h / n + 1) := by
      exact mul_le_mul_of_nonneg_left hM hCoeff
    _ = 8 * A ^ 2 * (n * h ^ 3 + n ^ 2 * h ^ 2 / X) := by
      field_simp

/-- The squared reflected length leaves one growing dyadic scale and one
inverse dyadic scale.  Their sums are respectively bounded by the physical
height and a geometric constant. -/
theorem gmS2ReflectionCoefficient_mul_length_sq_le
    {A X n h m : ℝ} (hX : 0 < X) (hn : 0 < n)
    (hh : 0 ≤ h) (hm : 0 ≤ m) (hM : m ≤ X * h / n + 1) :
    (8 * n ^ 2 * A ^ 2 * h ^ 2 / X) * m ^ 2 ≤
      16 * A ^ 2 * (X * h ^ 4 + n ^ 2 * h ^ 2 / X) := by
  let y : ℝ := X * h / n
  have hy : 0 ≤ y := by dsimp only [y]; positivity
  have hmSq : m ^ 2 ≤ 2 * y ^ 2 + 2 := by
    calc
      m ^ 2 ≤ (y + 1) ^ 2 :=
        pow_le_pow_left₀ hm hM 2
      _ ≤ 2 * y ^ 2 + 2 := by nlinarith [sq_nonneg (y - 1)]
  have hCoeff : 0 ≤ 8 * n ^ 2 * A ^ 2 * h ^ 2 / X := by positivity
  calc
    (8 * n ^ 2 * A ^ 2 * h ^ 2 / X) * m ^ 2 ≤
        (8 * n ^ 2 * A ^ 2 * h ^ 2 / X) * (2 * y ^ 2 + 2) := by
      exact mul_le_mul_of_nonneg_left hmSq hCoeff
    _ = 16 * A ^ 2 * (X * h ^ 4 + n ^ 2 * h ^ 2 / X) := by
      dsimp only [y]
      field_simp
      ring

/-- Coarse but source-shaped bound for the powered moment after multiplication
by the stationary coefficient on one bin.  The first and third terms retain
the inverse dyadic gain; the middle term retains the growing dyadic scale. -/
noncomputable def gmS2PhysicalBinSourceBound
    (A C : ℝ) (k : ℕ) (η T : ℝ) (W : Finset ℝ)
    (N H j : ℕ) : ℝ :=
  let R : ℝ := W.card
  let X : ℝ := (2 ^ j : ℕ)
  let F : ℝ := (((k : ℝ) ^ 2 * C ^ 3) ^ (1 / (k : ℝ))) *
    T ^ (η / (k : ℝ)) * (2 * (heathBrownFixedReflectionLength N H j : ℝ)) ^ (2 * η)
  F *
    (16 * R ^ 2 * A ^ 2 *
        ((N : ℝ) * H ^ 3 + (N : ℝ) ^ 2 * H ^ 2 / X) +
      64 * R ^ (2 - 1 / (k : ℝ)) * A ^ 2 *
        (X * H ^ 4 + (N : ℝ) ^ 2 * H ^ 2 / X) +
      16 * R ^ (2 - 3 / (4 * (k : ℝ))) *
        T ^ (1 / (2 * (k : ℝ))) * A ^ 2 *
        ((N : ℝ) * H ^ 3 + (N : ℝ) ^ 2 * H ^ 2 / X))

theorem gmS2ReflectionCoefficient_mul_source_le_physical
    {A C η T : ℝ} {k N H j : ℕ} {W : Finset ℝ}
    (hC : 0 ≤ C) (hT : 0 ≤ T) (hk : 0 < k)
    (hN : 0 < N) (hH : 0 < H) :
    gmS2ReflectionCoefficient A N H j *
        gmPoweredDifferenceSourceBound C k η T W
          (heathBrownFixedReflectionLength N H j) ≤
      gmS2PhysicalBinSourceBound A C k η T W N H j := by
  let X : ℝ := ((2 ^ j : ℕ) : ℝ)
  let n : ℝ := N
  let h : ℝ := H
  let m : ℝ := heathBrownFixedReflectionLength N H j
  let R : ℝ := W.card
  let F : ℝ := (((k : ℝ) ^ 2 * C ^ 3) ^ (1 / (k : ℝ))) *
    T ^ (η / (k : ℝ)) * (2 * m) ^ (2 * η)
  have hX : 0 < X := by dsimp only [X]; positivity
  have hn : 0 < n := by
    simpa only [n] using (Nat.cast_pos.mpr hN : (0 : ℝ) < (N : ℝ))
  have hh : 0 ≤ h := by positivity
  have hm : 0 ≤ m := by positivity
  have hmUpper : m ≤ X * h / n + 1 := by
    dsimp only [m, X, h, n]
    exact heathBrownFixedReflectionLength_cast_le N H j hN hH
  have hOne := gmS2ReflectionCoefficient_mul_length_le
    (A := A) hX hn hh hmUpper
  have hTwo := gmS2ReflectionCoefficient_mul_length_sq_le
    (A := A) hX hn hh hm hmUpper
  have hF : 0 ≤ F := by dsimp only [F]; positivity
  have hR : 0 ≤ R := by dsimp only [R]; positivity
  rw [gmPoweredDifferenceSourceBound_eq_physical C k η T W
    (heathBrownFixedReflectionLength N H j) hk]
  rw [gm_powered_common_factor_eq hC hT hk]
  rw [gmS2ReflectionCoefficient_eq]
  change (8 * n ^ 2 * A ^ 2 * h ^ 2 / X) *
      (F * (R ^ 2 * (2 * m) +
        R ^ (2 - 1 / (k : ℝ)) * (4 * m ^ 2) +
        R ^ (2 - 3 / (4 * (k : ℝ))) *
          T ^ (1 / (2 * (k : ℝ))) * (2 * m))) ≤ _
  unfold gmS2PhysicalBinSourceBound
  dsimp only [R, X, F, n, h, m]
  rw [show (8 * n ^ 2 * A ^ 2 * h ^ 2 / X) *
      (F * (R ^ 2 * (2 * m) +
        R ^ (2 - 1 / (k : ℝ)) * (4 * m ^ 2) +
        R ^ (2 - 3 / (4 * (k : ℝ))) *
          T ^ (1 / (2 * (k : ℝ))) * (2 * m))) =
      F * (2 * R ^ 2 * ((8 * n ^ 2 * A ^ 2 * h ^ 2 / X) * m) +
        4 * R ^ (2 - 1 / (k : ℝ)) *
          ((8 * n ^ 2 * A ^ 2 * h ^ 2 / X) * m ^ 2) +
        2 * R ^ (2 - 3 / (4 * (k : ℝ))) *
          T ^ (1 / (2 * (k : ℝ))) *
          ((8 * n ^ 2 * A ^ 2 * h ^ 2 / X) * m)) by ring]
  apply mul_le_mul_of_nonneg_left _ hF
  change
    2 * R ^ 2 * ((8 * n ^ 2 * A ^ 2 * h ^ 2 / X) * m) +
        4 * R ^ (2 - 1 / (k : ℝ)) *
          ((8 * n ^ 2 * A ^ 2 * h ^ 2 / X) * m ^ 2) +
        2 * R ^ (2 - 3 / (4 * (k : ℝ))) *
          T ^ (1 / (2 * (k : ℝ))) *
          ((8 * n ^ 2 * A ^ 2 * h ^ 2 / X) * m) ≤
      16 * R ^ 2 * A ^ 2 *
          (n * h ^ 3 + n ^ 2 * h ^ 2 / X) +
        64 * R ^ (2 - 1 / (k : ℝ)) * A ^ 2 *
          (X * h ^ 4 + n ^ 2 * h ^ 2 / X) +
        16 * R ^ (2 - 3 / (4 * (k : ℝ))) *
          T ^ (1 / (2 * (k : ℝ))) * A ^ 2 *
          (n * h ^ 3 + n ^ 2 * h ^ 2 / X)
  calc
    _ ≤ 2 * R ^ 2 *
          (8 * A ^ 2 * (n * h ^ 3 + n ^ 2 * h ^ 2 / X)) +
        4 * R ^ (2 - 1 / (k : ℝ)) *
          (16 * A ^ 2 * (X * h ^ 4 + n ^ 2 * h ^ 2 / X)) +
        2 * R ^ (2 - 3 / (4 * (k : ℝ))) *
          T ^ (1 / (2 * (k : ℝ))) *
          (8 * A ^ 2 * (n * h ^ 3 + n ^ 2 * h ^ 2 / X)) := by
      gcongr
    _ = _ := by ring

/-- One-bin majorant after eliminating the powered scale.  The reflection
errors are retained verbatim; no asymptotic notation has yet been used. -/
noncomputable def gmS2PhysicalBinBound
    (A K L C : ℝ) (q k : ℕ) (η : ℝ)
    (N : ℕ) (T : ℝ) (W : Finset ℝ) (H j : ℕ) : ℝ :=
  let M := heathBrownFixedReflectionLength N H j
  2 * ((Nat.clog 2 M : ℝ) + 1) *
      (gmS2ReflectionCoefficient A N H j * (W.card : ℝ) ^ 2 +
        (Nat.clog 2 M : ℝ) *
          gmS2PhysicalBinSourceBound A C k η T W N H j) +
    2 * ((heathBrownDifferenceBin W j).card : ℝ) *
      (gmNonzeroTailBinError q N M H
        (((2 ^ (j + 1) : ℕ) : ℝ)) K L) ^ 2

theorem gmS2PoweredBinBound_le_physical
    {A K L C η T : ℝ} {q k N H j : ℕ} {W : Finset ℝ}
    (hC : 0 ≤ C) (hT : 0 ≤ T) (hk : 0 < k)
    (hN : 0 < N) (hH : 0 < H) :
    gmS2PoweredBinBound A K L C q k η N T W H j ≤
      gmS2PhysicalBinBound A K L C q k η N T W H j := by
  let M := heathBrownFixedReflectionLength N H j
  let D := gmS2ReflectionCoefficient A N H j
  let R : ℝ := W.card
  have hD : 0 ≤ D := by dsimp only [D]; unfold gmS2ReflectionCoefficient; positivity
  have hR : 0 ≤ R := by dsimp only [R]; positivity
  have hSource : 0 ≤ gmPoweredDifferenceSourceBound C k η T W M :=
    gmPoweredDifferenceSourceBound_nonneg hC hk hT
  have hPhysical : 0 ≤ gmS2PhysicalBinSourceBound A C k η T W N H j := by
    unfold gmS2PhysicalBinSourceBound
    positivity
  have hMain := gmS2ReflectionCoefficient_mul_source_le_physical
    (A := A) (C := C) (η := η) (T := T) (k := k)
    (N := N) (H := H) (j := j) (W := W) hC hT hk hN hH
  unfold gmS2PoweredBinBound gmS2PhysicalBinBound
  dsimp only [M, D, R]
  rw [show
      2 * (((N : ℝ) * A / Real.sqrt ((2 ^ j : ℕ) : ℝ)) ^ 2) *
          ((2 * (H : ℝ)) ^ 2 *
            (2 * ((Nat.clog 2 M : ℝ) + 1) *
              (R ^ 2 + (Nat.clog 2 M : ℝ) *
                gmPoweredDifferenceSourceBound C k η T W M))) =
        2 * ((Nat.clog 2 M : ℝ) + 1) *
          (D * R ^ 2 + (Nat.clog 2 M : ℝ) *
            (D * gmPoweredDifferenceSourceBound C k η T W M)) by
      dsimp only [D]
      unfold gmS2ReflectionCoefficient
      ring]
  gcongr

/-- Complete literal tail schedule with every powered block replaced by its
physical-scale bound. -/
theorem gmTraceNonzeroDifferenceMoment_le_physical_schedule
    (cutoff : GMSmoothCutoff) (q k : ℕ) (hq : 2 ≤ q)
    (η : ℝ) (hk : 0 < k) (hη : 0 < η) :
    ∃ A K L C B T_min : ℝ,
      0 < A ∧ 0 < K ∧ 0 < L ∧ 0 < C ∧ 0 < B ∧
      1 ≤ T_min ∧
      ∀ {N H : ℕ} {T δ : ℝ} (W : Finset ℝ),
        T_min ≤ T → 0 < N → 0 < H → 4 * (H : ℝ) ≤ δ →
        IsSeparated δ W → InBaseInterval T W → W.Nonempty →
        gmTraceNonzeroDifferenceMoment cutoff N W ≤
          (W.card : ℝ) * (B / (N : ℝ) ^ (q - 1)) ^ 2 +
            ∑ j ∈ Finset.range (Nat.log 2 (Nat.floor T) + 1),
              gmS2PhysicalBinBound A K L C q k η N T W H j := by
  obtain ⟨A, K, L, C, B, T_min, hA, hK, hL, hC, hB, hT_min, hRaw⟩ :=
    gmTraceNonzeroDifferenceMoment_le_powered_schedule
      cutoff q k hq η hk hη
  refine ⟨A, K, L, C, B, T_min, hA, hK, hL, hC, hB, hT_min, ?_⟩
  intro N H T δ W hT hN hH hHδ hSep hBase hW
  have hTNonneg : 0 ≤ T := zero_le_one.trans (hT_min.trans hT)
  exact (hRaw W hT hN hH hHδ hSep hBase hW).trans <| by
    gcongr
    exact gmS2PoweredBinBound_le_physical hC.le hTNonneg hk hN hH

/-- The source-faithful schedule vanishes on empty displacement fibers.  This
keeps the stationary hypotheses available in every nonzero summand and avoids
introducing artificial low-frequency terms. -/
noncomputable def gmS2ScheduledPhysicalBinBound
    (A K L C : ℝ) (q k : ℕ) (η : ℝ)
    (N : ℕ) (T : ℝ) (W : Finset ℝ) (H j : ℕ) : ℝ :=
  if (heathBrownDifferenceBin W j).Nonempty then
    gmS2PhysicalBinBound A K L C q k η N T W H j
  else 0

theorem gmTraceNonzeroDifferenceMoment_le_scheduled_physical
    (cutoff : GMSmoothCutoff) (q k : ℕ) (hq : 2 ≤ q)
    (η : ℝ) (hk : 0 < k) (hη : 0 < η) :
    ∃ A K L C B T_min : ℝ,
      0 < A ∧ 0 < K ∧ 0 < L ∧ 0 < C ∧ 0 < B ∧
      1 ≤ T_min ∧
      ∀ {N H : ℕ} {T δ : ℝ} (W : Finset ℝ),
        T_min ≤ T → 0 < N → 0 < H → 4 * (H : ℝ) ≤ δ →
        IsSeparated δ W → InBaseInterval T W → W.Nonempty →
        gmTraceNonzeroDifferenceMoment cutoff N W ≤
          (W.card : ℝ) * (B / (N : ℝ) ^ (q - 1)) ^ 2 +
            ∑ j ∈ Finset.range (Nat.log 2 (Nat.floor T) + 1),
              gmS2ScheduledPhysicalBinBound
                A K L C q k η N T W H j := by
  obtain ⟨A, K, L, C, T_ref, hA, hK, hL, hC, hT_ref, hBin⟩ :=
    gmNonzeroTailBinMoment_le_powered_reflection
      cutoff q k hq η hk hη
  obtain ⟨B, hB, hDiag⟩ := gmTraceNonzeroDiagonalMoment_le cutoff q hq
  refine ⟨A, K, L, C, B, T_ref, hA, hK, hL, hC, hB, hT_ref, ?_⟩
  intro N H T δ W hT hN hH hHδ hSep hBase hW
  have hδOne : 1 ≤ δ := by
    have hHOne : (1 : ℝ) ≤ H := by exact_mod_cast hH
    linarith
  have hSepOne : IsSeparated 1 W := by
    intro x hx y hy hxy
    exact hδOne.trans (hSep x hx y hy hxy)
  have hTNonneg : 0 ≤ T := zero_le_one.trans (hT_ref.trans hT)
  have hEach : ∀ j ∈ Finset.range (Nat.log 2 (Nat.floor T) + 1),
      gmNonzeroTailBinMoment cutoff N W j ≤
        gmS2ScheduledPhysicalBinBound A K L C q k η N T W H j := by
    intro j hj
    by_cases hOccupied : (heathBrownDifferenceBin W j).Nonempty
    · have hOcc : (heathBrownDifferenceBin W j).Nonempty := hOccupied
      obtain ⟨p, hp⟩ := hOccupied
      have hpFilter := Finset.mem_filter.mp hp
      have hpOff := Finset.mem_filter.mp hpFilter.1
      have hpW := Finset.mem_product.mp hpOff.1
      have hDelta : δ ≤ |p.1 - p.2| := by
        simpa only [Real.dist_eq] using
          hSep p.1 hpW.1 p.2 hpW.2 hpOff.2
      have hBounds := heathBrownDifferenceBin_bounds hSepOne hp
      have hjTwo : 2 ≤ j := by
        have hFour : (4 : ℝ) ≤ δ := by
          have hHOne : (1 : ℝ) ≤ H := by exact_mod_cast hH
          linarith
        by_contra hnot
        have hjSmall : j ≤ 1 := by omega
        interval_cases j <;> norm_num at hBounds ⊢ <;>
          linarith [hBounds.2, hDelta, hFour]
      have hHeightLower : (1 : ℝ) ≤ H := by exact_mod_cast hH
      have hHeightUpper : (H : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) / 2 := by
        have hPowSucc : (((2 ^ (j + 1) : ℕ) : ℝ)) =
            2 * (((2 ^ j : ℕ) : ℝ)) := by
          rw [pow_succ]
          norm_num
          ring
        rw [hPowSucc] at hBounds
        linarith
      have hPowered := hBin hT hSepOne hBase hW hjTwo hHeightLower
        hHeightUpper hN (heathBrownFixedReflectionLength_pos N H j)
      have hPhysical := gmS2PoweredBinBound_le_physical
        (A := A) (K := K) (L := L) (C := C) (q := q) (k := k)
        (N := N) (H := H) (j := j) (η := η) (T := T) (W := W)
        hC.le hTNonneg hk hN hH
      rw [gmS2ScheduledPhysicalBinBound, if_pos hOcc]
      exact hPowered.trans (by
        simpa only [gmS2PoweredBinBound] using hPhysical)
    · have hEq : heathBrownDifferenceBin W j = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp hOccupied
      rw [gmS2ScheduledPhysicalBinBound, if_neg hOccupied]
      simp [gmNonzeroTailBinMoment, hEq]
  rw [gmTraceNonzeroDifferenceMoment_eq_diagonal_add_bins hSepOne hBase]
  exact add_le_add (hDiag W hN) (Finset.sum_le_sum hEach)

/-- Every occupied reflected length is bounded by the common dyadic target. -/
theorem gmS2FixedReflectionLength_le_target
    {T : ℝ} {N H j : ℕ}
    (hj : j ∈ Finset.range (Nat.log 2 (Nat.floor T) + 1))
    (hjTwo : 2 ≤ j) :
    heathBrownFixedReflectionLength N H j ≤
      heathBrownReflectionTargetScale N H T := by
  exact (heathBrownFixedReflectionLength_le_common (Q := N) (H := H) hj hjTwo).trans
    (heathBrownCommonReflectionLength_le_target N H T)

/-- The local dyadic-prefix logarithm is at most the common corrected
exponent used by the source epsilon profile. -/
theorem gmS2FixedClog_add_one_le_commonExponent
    {T : ℝ} {N H j : ℕ}
    (hj : j ∈ Finset.range (Nat.log 2 (Nat.floor T) + 1))
    (hjTwo : 2 ≤ j) :
    Nat.clog 2 (heathBrownFixedReflectionLength N H j) + 1 ≤
      heathBrownCorrectedCommonExponent N H T := by
  have hM := heathBrownFixedReflectionLength_le_common (Q := N) (H := H) hj hjTwo
  have hClog := Nat.clog_mono_right 2 hM
  unfold heathBrownCorrectedCommonExponent
  omega

/-- The complete fixed-length factor occurring in the powered common loss is
absorbed by two powers of the explicit local recurrence profile. -/
theorem gmS2FixedLengthEpsilonLoss_le_profile_sq
    {η T : ℝ} {N H j : ℕ}
    (hη : 0 ≤ η)
    (hj : j ∈ Finset.range (Nat.log 2 (Nat.floor T) + 1))
    (hjTwo : 2 ≤ j) :
    (2 * (heathBrownFixedReflectionLength N H j : ℝ)) ^ (2 * η) ≤
      heathBrownLocalRecurrenceProfile η T N H ^ 2 := by
  let M : ℕ := heathBrownFixedReflectionLength N H j
  let P : ℕ := heathBrownCorrectedCommonScale N H T
  let G : ℝ := heathBrownLocalRecurrenceProfile η T N H
  have hMTarget := gmS2FixedReflectionLength_le_target (N := N) (H := H) hj hjTwo
  have hTwoM : (2 * M : ℝ) ≤ P := by
    have hNat : 2 * M ≤ P := by
      dsimp only [P]
      rw [heathBrownCorrectedCommonScale_eq_two_mul_target]
      exact Nat.mul_le_mul_left 2 hMTarget
    exact_mod_cast hNat
  have hP4 : (P : ℝ) ≤ (4 * P : ℕ) := by
    exact_mod_cast (show P ≤ 4 * P by omega)
  have hBase : (2 * (M : ℝ)) ≤ (4 * P : ℕ) := by
    exact hTwoM.trans hP4
  have hPow : (2 * (M : ℝ)) ^ η ≤ ((4 * P : ℕ) : ℝ) ^ η :=
    Real.rpow_le_rpow (by positivity) hBase hη
  have hComponent : ((4 * P : ℕ) : ℝ) ^ η ≤ G := by
    dsimp only [P, G]
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      (heathBrownLocalRecurrenceProfile_components
        (η := η) (T := T) (Q := N) (H := H)).2.2.2.2
  have hPowG : (2 * (M : ℝ)) ^ η ≤ G := hPow.trans hComponent
  have hLeft : (2 * (M : ℝ)) ^ (2 * η) =
      ((2 * (M : ℝ)) ^ η) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    congr 1
    ring
  rw [hLeft]
  exact pow_le_pow_left₀ (Real.rpow_nonneg (by positivity) _) hPowG 2

/-! ## Nonstationary part of the literal Section 6 schedule -/

/-- On the Mellin core `|r| \le N`, every retained signed Fourier mode is
uniformly to the right of its stationary point when `|t| \le N`.  Keeping
the finite Dirichlet polynomial inside the aggregate integral and using the
fixed Mellin `L^1` mass gives a factor `M / N`; the complementary Mellin
range is controlled at order five. -/
theorem gmRetainedSignedReflection_near_bound
    (cutoff : GMSmoothCutoff) :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
      ∀ {N M : ℕ} {t : ℝ}, 0 < N → 0 < M → |t| ≤ (N : ℝ) →
        ‖∑ m ∈ Finset.Icc 1 M,
            (gmTraceFourier cutoff t ((N : ℝ) * m) +
              gmTraceFourier cutoff t (-((N : ℝ) * m)))‖ ≤
          C * (M : ℝ) / (N : ℝ) +
            K * (M : ℝ) ^ 2 * (N : ℝ) ^ (-4 : ℝ) := by
  obtain ⟨K₀, hK₀, hTail⟩ :=
    gmPositiveMellinTail_bound_order cutoff 5 (by norm_num)
  have hMellin : Integrable (gmCutoffMellin cutoff) := by
    simpa only [gmCutoffMellin, VerticalIntegrable] using
      verticalIntegrable_mellin_gmCutoffSq_one cutoff
  let L₁ : ℝ := ∫ r : ℝ, ‖gmCutoffMellin cutoff r‖
  let C : ℝ := 2 * (L₁ / (2 * Real.pi)) + 1
  have hL₁ : 0 ≤ L₁ := by
    dsimp only [L₁]
    exact integral_nonneg fun _ => norm_nonneg _
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, 2 * K₀, hC, by positivity, ?_⟩
  intro N M t hN hM htN
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  let fpos : ℝ → ℝ := fun r =>
    (1 / (2 * Real.pi) : ℝ) * ‖gmCutoffMellin cutoff r‖ *
      ‖gmReflectionIntegral (t - r) N (2 * N * M)‖ *
        ‖gmPositiveDualDirichletPoly t N M r‖
  let fneg : ℝ → ℝ := fun r =>
    (1 / (2 * Real.pi) : ℝ) * ‖gmCutoffMellin cutoff r‖ *
      ‖gmReflectionIntegral (-t - r) N (2 * N * M)‖ *
        ‖gmPositiveDualDirichletPoly (-t) N M r‖
  have hPosInt : Integrable fpos := by
    simpa only [fpos] using
      integrable_norm_gmPositiveDualAggregate cutoff t (M := M) hN
  have hNegInt : Integrable fneg := by
    simpa only [fneg] using
      integrable_norm_gmPositiveDualAggregate cutoff (-t) (M := M) hN
  have hAB : (N : ℝ) ≤ 2 * N * M := by
    have hMOne : (1 : ℝ) ≤ M := by exact_mod_cast hM
    nlinarith
  have hCorePos : ∫ r : ℝ in Set.Icc (-(N : ℝ)) N, fpos r ≤
      (L₁ / (2 * Real.pi)) * (M : ℝ) / (N : ℝ) := by
    have hDom : IntegrableOn (fun r : ℝ =>
        (1 / (2 * Real.pi)) * ‖gmCutoffMellin cutoff r‖ *
          ((M : ℝ) / (2 * N))) (Set.Icc (-(N : ℝ)) N) :=
      ((hMellin.norm.const_mul
        (1 / (2 * Real.pi))).mul_const ((M : ℝ) / (2 * N))).integrableOn
    calc
      ∫ r : ℝ in Set.Icc (-(N : ℝ)) N, fpos r ≤
          ∫ r : ℝ in Set.Icc (-(N : ℝ)) N,
            (1 / (2 * Real.pi)) * ‖gmCutoffMellin cutoff r‖ *
              ((M : ℝ) / (2 * N)) := by
        apply integral_mono_ae hPosInt.integrableOn hDom
        filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
        have hrLower : -(N : ℝ) ≤ r := hr.1
        have htUpper : t ≤ (N : ℝ) := (le_abs_self t).trans htN
        have hPhase : t - r < 2 * Real.pi * (N : ℝ) := by
          nlinarith [Real.pi_gt_three]
        have hReflect := norm_gmReflectionIntegral_le_right
          hAB hNr hPhase
        have hDen : 4 * (N : ℝ) ≤
            2 * Real.pi * (N : ℝ) - (t - r) := by
          nlinarith [Real.pi_gt_three]
        have hDenPos : 0 < 2 * Real.pi * (N : ℝ) - (t - r) := by
          linarith
        have hReflect' : ‖gmReflectionIntegral (t - r) N (2 * N * M)‖ ≤
            1 / (2 * (N : ℝ)) := by
          calc
            ‖gmReflectionIntegral (t - r) N (2 * N * M)‖ ≤
                2 / (2 * Real.pi * (N : ℝ) - (t - r)) := hReflect
            _ ≤ 2 / (4 * (N : ℝ)) :=
              div_le_div_of_nonneg_left (by norm_num) (by positivity) hDen
            _ = 1 / (2 * (N : ℝ)) := by ring
        have hPoly := norm_gmPositiveDualDirichletPoly_le t (M := M) hN r
        dsimp only [fpos]
        calc
          (1 / (2 * Real.pi)) * ‖gmCutoffMellin cutoff r‖ *
                ‖gmReflectionIntegral (t - r) N (2 * N * M)‖ *
                  ‖gmPositiveDualDirichletPoly t N M r‖ ≤
              (1 / (2 * Real.pi)) * ‖gmCutoffMellin cutoff r‖ *
                (1 / (2 * (N : ℝ))) * (M : ℝ) := by gcongr
          _ = (1 / (2 * Real.pi)) * ‖gmCutoffMellin cutoff r‖ *
                ((M : ℝ) / (2 * N)) := by ring
      _ ≤ (1 / (2 * Real.pi)) * L₁ * ((M : ℝ) / (2 * N)) := by
        rw [← MeasureTheory.integral_const_mul,
          ← MeasureTheory.integral_mul_const]
        apply MeasureTheory.integral_mono_measure Measure.restrict_le_self
        · filter_upwards with r
          positivity
        · exact (hMellin.norm.const_mul
            (1 / (2 * Real.pi))).mul_const ((M : ℝ) / (2 * N))
      _ ≤ (L₁ / (2 * Real.pi)) * (M : ℝ) / (N : ℝ) := by
        have hPi : 0 < Real.pi := Real.pi_pos
        field_simp [hPi.ne', hNr.ne']
        nlinarith [mul_nonneg hL₁ hMr.le]
  have hCoreNeg : ∫ r : ℝ in Set.Icc (-(N : ℝ)) N, fneg r ≤
      (L₁ / (2 * Real.pi)) * (M : ℝ) / (N : ℝ) := by
    have htNeg : |-t| ≤ (N : ℝ) := by simpa using htN
    have hEq : fneg = fun r =>
        (1 / (2 * Real.pi) : ℝ) * ‖gmCutoffMellin cutoff r‖ *
          ‖gmReflectionIntegral ((-t) - r) N (2 * N * M)‖ *
            ‖gmPositiveDualDirichletPoly (-t) N M r‖ := by
      funext r
      simp only [fneg]
    rw [hEq]
    -- The positive-core argument is ordinate-uniform, so repeat it at `-t`.
    have hDom : IntegrableOn (fun r : ℝ =>
        (1 / (2 * Real.pi)) * ‖gmCutoffMellin cutoff r‖ *
          ((M : ℝ) / (2 * N))) (Set.Icc (-(N : ℝ)) N) :=
      ((hMellin.norm.const_mul
        (1 / (2 * Real.pi))).mul_const ((M : ℝ) / (2 * N))).integrableOn
    calc
      ∫ r : ℝ in Set.Icc (-(N : ℝ)) N,
          (1 / (2 * Real.pi)) * ‖gmCutoffMellin cutoff r‖ *
            ‖gmReflectionIntegral ((-t) - r) N (2 * N * M)‖ *
              ‖gmPositiveDualDirichletPoly (-t) N M r‖ ≤
          ∫ r : ℝ in Set.Icc (-(N : ℝ)) N,
            (1 / (2 * Real.pi)) * ‖gmCutoffMellin cutoff r‖ *
              ((M : ℝ) / (2 * N)) := by
        apply integral_mono_ae hNegInt.integrableOn hDom
        filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
        have hrLower : -(N : ℝ) ≤ r := hr.1
        have htUpper : -t ≤ (N : ℝ) := (le_abs_self (-t)).trans htNeg
        have hPhase : (-t) - r < 2 * Real.pi * (N : ℝ) := by
          nlinarith [Real.pi_gt_three]
        have hReflect := norm_gmReflectionIntegral_le_right hAB hNr hPhase
        have hDen : 4 * (N : ℝ) ≤
            2 * Real.pi * (N : ℝ) - ((-t) - r) := by
          nlinarith [Real.pi_gt_three]
        have hDenPos : 0 < 2 * Real.pi * (N : ℝ) - ((-t) - r) := by
          linarith
        have hReflect' : ‖gmReflectionIntegral ((-t) - r) N (2 * N * M)‖ ≤
            1 / (2 * (N : ℝ)) := by
          calc
            ‖gmReflectionIntegral ((-t) - r) N (2 * N * M)‖ ≤
                2 / (2 * Real.pi * (N : ℝ) - ((-t) - r)) := hReflect
            _ ≤ 2 / (4 * (N : ℝ)) :=
              div_le_div_of_nonneg_left (by norm_num) (by positivity) hDen
            _ = 1 / (2 * (N : ℝ)) := by ring
        have hPoly := norm_gmPositiveDualDirichletPoly_le (-t) (M := M) hN r
        calc
          (1 / (2 * Real.pi)) * ‖gmCutoffMellin cutoff r‖ *
                ‖gmReflectionIntegral ((-t) - r) N (2 * N * M)‖ *
                  ‖gmPositiveDualDirichletPoly (-t) N M r‖ ≤
              (1 / (2 * Real.pi)) * ‖gmCutoffMellin cutoff r‖ *
                (1 / (2 * (N : ℝ))) * (M : ℝ) := by gcongr
          _ = (1 / (2 * Real.pi)) * ‖gmCutoffMellin cutoff r‖ *
                ((M : ℝ) / (2 * N)) := by ring
      _ ≤ (1 / (2 * Real.pi)) * L₁ * ((M : ℝ) / (2 * N)) := by
        rw [← MeasureTheory.integral_const_mul,
          ← MeasureTheory.integral_mul_const]
        apply MeasureTheory.integral_mono_measure Measure.restrict_le_self
        · filter_upwards with r
          positivity
        · exact (hMellin.norm.const_mul
            (1 / (2 * Real.pi))).mul_const ((M : ℝ) / (2 * N))
      _ ≤ (L₁ / (2 * Real.pi)) * (M : ℝ) / (N : ℝ) := by
        have hPi : 0 < Real.pi := Real.pi_pos
        field_simp [hPi.ne', hNr.ne']
        nlinarith [mul_nonneg hL₁ hMr.le]
  have hTailPos := hTail t (N : ℝ) N M (by exact_mod_cast hN) hN hM
  have hTailNeg := hTail (-t) (N : ℝ) N M (by exact_mod_cast hN) hN hM
  calc
    ‖∑ m ∈ Finset.Icc 1 M,
        (gmTraceFourier cutoff t ((N : ℝ) * m) +
          gmTraceFourier cutoff t (-((N : ℝ) * m)))‖ ≤
        (∫ r : ℝ, fpos r) + ∫ r : ℝ, fneg r := by
      simpa only [fpos, fneg] using
        norm_gmTraceFourier_signed_sum_le_dualPoly cutoff t hN
    _ = ((∫ r : ℝ in Set.Icc (-(N : ℝ)) N, fpos r) +
          ∫ r : ℝ in (Set.Icc (-(N : ℝ)) N)ᶜ, fpos r) +
        ((∫ r : ℝ in Set.Icc (-(N : ℝ)) N, fneg r) +
          ∫ r : ℝ in (Set.Icc (-(N : ℝ)) N)ᶜ, fneg r) := by
      rw [integral_add_compl measurableSet_Icc hPosInt,
        integral_add_compl measurableSet_Icc hNegInt]
    _ ≤ 2 * (L₁ / (2 * Real.pi)) * (M : ℝ) / (N : ℝ) +
        (2 * K₀) * (M : ℝ) ^ 2 * (N : ℝ) ^ (-4 : ℝ) := by
      have hPieces := add_le_add
        (add_le_add hCorePos hTailPos) (add_le_add hCoreNeg hTailNeg)
      simpa only [fpos, fneg, Nat.cast_ofNat] using hPieces.trans_eq (by ring)
    _ ≤ C * (M : ℝ) / (N : ℝ) +
        (2 * K₀) * (M : ℝ) ^ 2 * (N : ℝ) ^ (-4 : ℝ) := by
      have hCoeff : 2 * (L₁ / (2 * Real.pi)) ≤ C := by
        dsimp only [C]
        linarith
      gcongr

/-- The complete *scaled* nonzero Poisson tail is of square-root size below
the first stationary scale.  The truncation `Nat.sqrt N + 1` balances the
retained nonstationary reflection integral against the omitted Fourier
frequencies.  This is the source-sharp `M = 1` input in Proposition 6.1. -/
theorem exists_norm_gmTraceNonzeroTailAt_le_sqrt_near
    (cutoff : GMSmoothCutoff) :
    ∃ D : ℝ, 0 < D ∧ ∀ (N : ℕ) (t : ℝ), 0 < N →
      |t| ≤ (N : ℝ) →
      ‖gmTraceNonzeroTailAt cutoff N t‖ ≤ D * Real.sqrt N := by
  obtain ⟨C, K, hC, hK, hRetained⟩ :=
    gmRetainedSignedReflection_near_bound cutoff
  obtain ⟨L, hL, hFar⟩ := gmTraceFourierFarTail_bound_order cutoff 2
  let D : ℝ := 2 * C + 4 * K + 16 * L + 1
  have hD : 0 < D := by dsimp only [D]; positivity
  refine ⟨D, hD, ?_⟩
  intro N t hN htN
  let M : ℕ := Nat.sqrt N + 1
  let S : ℝ := Real.sqrt N
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hNOne : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hS : 0 < S := by
    dsimp only [S]
    exact Real.sqrt_pos.2 hNr
  have hSOne : 1 ≤ S := by
    dsimp only [S]
    simpa only [Real.sqrt_one] using
      Real.sqrt_le_sqrt hNOne
  have hSsq : S ^ 2 = (N : ℝ) := by
    dsimp only [S]
    exact Real.sq_sqrt hNr.le
  have hM : 0 < M := by dsimp only [M]; omega
  have hMlower : S ≤ (M : ℝ) := by
    dsimp only [S, M]
    simpa only [Nat.cast_add, Nat.cast_one] using
      (Real.real_sqrt_le_nat_sqrt_succ (a := N))
  have hMupper : (M : ℝ) ≤ 2 * S := by
    have hNatSqrt : ((Nat.sqrt N : ℕ) : ℝ) ≤ S := by
      dsimp only [S]
      exact Real.nat_sqrt_le_real_sqrt
    dsimp only [M]
    push_cast
    linarith
  have hMnonneg : (0 : ℝ) ≤ M := by positivity
  have hMtwo : (M : ℝ) ^ 2 ≤ 4 * (N : ℝ) := by
    have hSq := pow_le_pow_left₀ hMnonneg hMupper 2
    rw [mul_pow, hSsq] at hSq
    norm_num at hSq ⊢
    linarith
  have hNm2 : (N : ℝ) ≤ (M : ℝ) ^ 2 := by
    rw [← hSsq]
    exact pow_le_pow_left₀ hS.le hMlower 2
  have hRet := hRetained hN hM htN
  have hRetScaled :
      (N : ℝ) *
          ‖∑ m ∈ Finset.Icc 1 M,
              (gmTraceFourier cutoff t ((N : ℝ) * m) +
                gmTraceFourier cutoff t (-((N : ℝ) * m)))‖ ≤
        (2 * C + 4 * K) * S := by
    have hFirst :
        (N : ℝ) * (C * (M : ℝ) / (N : ℝ)) ≤ 2 * C * S := by
      calc
        (N : ℝ) * (C * (M : ℝ) / (N : ℝ)) = C * (M : ℝ) := by
          field_simp [hNr.ne']
        _ ≤ C * (2 * S) := mul_le_mul_of_nonneg_left hMupper hC.le
        _ = 2 * C * S := by ring
    have hInv : (N : ℝ) ^ (-4 : ℝ) = ((N : ℝ) ^ 4)⁻¹ := by
      rw [Real.rpow_neg hNr.le]
      exact congrArg Inv.inv (Real.rpow_natCast (N : ℝ) 4)
    have hSecond :
        (N : ℝ) * (K * (M : ℝ) ^ 2 * (N : ℝ) ^ (-4 : ℝ)) ≤
          4 * K * S := by
      rw [hInv]
      have hKN : K * (M : ℝ) ^ 2 ≤ K * (4 * (N : ℝ)) :=
        mul_le_mul_of_nonneg_left hMtwo hK.le
      have hScale : (1 : ℝ) ≤ S * (N : ℝ) ^ 2 := by
        have hN2 : (1 : ℝ) ≤ (N : ℝ) ^ 2 := one_le_pow₀ hNOne
        nlinarith
      calc
        (N : ℝ) * (K * (M : ℝ) ^ 2 * ((N : ℝ) ^ 4)⁻¹) =
            K * (M : ℝ) ^ 2 / (N : ℝ) ^ 3 := by
              field_simp [hNr.ne']
        _ ≤ (K * (4 * (N : ℝ))) / (N : ℝ) ^ 3 := by
              exact div_le_div_of_nonneg_right hKN (by positivity)
        _ ≤ 4 * K * S := by
              apply (div_le_iff₀ (pow_pos hNr 3)).2
              have hK4N : 0 ≤ 4 * K * (N : ℝ) := by positivity
              calc
                K * (4 * (N : ℝ)) = 4 * K * (N : ℝ) := by ring
                _ ≤ (4 * K * (N : ℝ)) * (S * (N : ℝ) ^ 2) :=
                  le_mul_of_one_le_right hK4N hScale
                _ = 4 * K * S * (N : ℝ) ^ 3 := by ring
    have hScaled := mul_le_mul_of_nonneg_left hRet hNr.le
    calc
      (N : ℝ) *
          ‖∑ m ∈ Finset.Icc 1 M,
              (gmTraceFourier cutoff t ((N : ℝ) * m) +
                gmTraceFourier cutoff t (-((N : ℝ) * m)))‖ ≤
          (N : ℝ) *
            (C * (M : ℝ) / (N : ℝ) +
              K * (M : ℝ) ^ 2 * (N : ℝ) ^ (-4 : ℝ)) := hScaled
      _ = (N : ℝ) * (C * (M : ℝ) / (N : ℝ)) +
          (N : ℝ) *
            (K * (M : ℝ) ^ 2 * (N : ℝ) ^ (-4 : ℝ)) := by ring
      _ ≤ 2 * C * S + 4 * K * S := add_le_add hFirst hSecond
      _ = (2 * C + 4 * K) * S := by ring
  have hOneAbs : 1 + |t| ≤ 2 * (N : ℝ) := by linarith
  have hFourth : (1 + |t|) ^ 4 ≤ 16 * (N : ℝ) ^ 4 := by
    have hPow := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + |t|) hOneAbs 4
    nlinarith
  have hFarRaw := hFar N M hN hM t
  have hFarScaled :
      (N : ℝ) * ‖gmTraceFourierFarTail cutoff N M t‖ ≤ 16 * L * S := by
    have hDenPos : 0 < (N : ℝ) ^ 4 * (M : ℝ) ^ 2 := by positivity
    have hNumer : L * (1 + |t|) ^ 4 ≤ L * (16 * (N : ℝ) ^ 4) :=
      mul_le_mul_of_nonneg_left hFourth hL.le
    have hQuot :
        L * (1 + |t|) ^ 4 /
            ((N : ℝ) ^ 4 * (M : ℝ) ^ 2) ≤
          L * (16 * (N : ℝ) ^ 4) /
            ((N : ℝ) ^ 4 * (M : ℝ) ^ 2) :=
      div_le_div_of_nonneg_right hNumer hDenPos.le
    have hScaled := mul_le_mul_of_nonneg_left (hFarRaw.trans hQuot) hNr.le
    calc
      (N : ℝ) * ‖gmTraceFourierFarTail cutoff N M t‖ ≤
          (N : ℝ) *
            (L * (16 * (N : ℝ) ^ 4) /
              ((N : ℝ) ^ 4 * (M : ℝ) ^ 2)) := hScaled
      _ = 16 * L * ((N : ℝ) / (M : ℝ) ^ 2) := by
            field_simp [hNr.ne']
      _ ≤ 16 * L := by
            have hRatio : (N : ℝ) / (M : ℝ) ^ 2 ≤ 1 :=
              (div_le_one (by positivity)).2 hNm2
            nlinarith [mul_nonneg hL.le (sub_nonneg.mpr hRatio)]
      _ ≤ 16 * L * S := by
            exact le_mul_of_one_le_right (by positivity) hSOne
  rw [norm_gmTraceNonzeroTailAt_eq,
    gmTraceNonzeroFourierSum_eq_signed_add_far cutoff N M hN]
  calc
    (N : ℝ) *
        ‖(∑ m ∈ Finset.Icc 1 M,
            (gmTraceFourier cutoff t ((N : ℝ) * m) +
              gmTraceFourier cutoff t (-((N : ℝ) * m)))) +
            gmTraceFourierFarTail cutoff N M t‖ ≤
        (N : ℝ) *
          (‖∑ m ∈ Finset.Icc 1 M,
              (gmTraceFourier cutoff t ((N : ℝ) * m) +
                gmTraceFourier cutoff t (-((N : ℝ) * m)))‖ +
            ‖gmTraceFourierFarTail cutoff N M t‖) := by
              gcongr
              exact norm_add_le _ _
    _ = (N : ℝ) *
          ‖∑ m ∈ Finset.Icc 1 M,
              (gmTraceFourier cutoff t ((N : ℝ) * m) +
                gmTraceFourier cutoff t (-((N : ℝ) * m)))‖ +
        (N : ℝ) * ‖gmTraceFourierFarTail cutoff N M t‖ := by ring
    _ ≤ (2 * C + 4 * K) * S + 16 * L * S :=
      add_le_add hRetScaled hFarScaled
    _ ≤ D * S := by
      dsimp only [D]
      nlinarith

/-- All dyadic fibers whose *upper* endpoint lies below `N` are bounded
together, not one at a time.  The exact fiber partition prevents a spurious
logarithmic or local-density loss and produces the paper's `N * R^2`
difference moment. -/
theorem gmNearScaleBinSum_le_sqrt
    (cutoff : GMSmoothCutoff) {D : ℝ}
    (hTail : ∀ (N : ℕ) (t : ℝ), 0 < N → |t| ≤ (N : ℝ) →
      ‖gmTraceNonzeroTailAt cutoff N t‖ ≤ D * Real.sqrt N)
    {T : ℝ} {W : Finset ℝ} (hSep : IsSeparated 1 W)
    (hInterval : InBaseInterval T W) {N : ℕ} (hN : 0 < N) :
    (∑ j ∈ Finset.range (Nat.log 2 (Nat.floor T) + 1),
        if 2 ^ (j + 1) ≤ N then gmNonzeroTailBinMoment cutoff N W j else 0) ≤
      D ^ 2 * (N : ℝ) * (W.card : ℝ) ^ 2 := by
  let F : (ℝ × ℝ) → ℝ := fun p =>
    if 2 ^ (heathBrownDifferenceScale p.1 p.2 + 1) ≤ N then
      ‖gmTraceNonzeroTailAt cutoff N (p.1 - p.2)‖ ^ 2
    else 0
  have hBin (j : ℕ) :
      (∑ p ∈ heathBrownDifferenceBin W j, F p) =
        if 2 ^ (j + 1) ≤ N then gmNonzeroTailBinMoment cutoff N W j else 0 := by
    by_cases hj : 2 ^ (j + 1) ≤ N
    · rw [if_pos hj]
      unfold gmNonzeroTailBinMoment
      apply Finset.sum_congr rfl
      intro p hp
      have hScale : heathBrownDifferenceScale p.1 p.2 = j :=
        (Finset.mem_filter.mp hp).2
      simp only [F, hScale, if_pos hj]
    · rw [if_neg hj]
      apply Finset.sum_eq_zero
      intro p hp
      have hScale : heathBrownDifferenceScale p.1 p.2 = j :=
        (Finset.mem_filter.mp hp).2
      simp only [F, hScale, if_neg hj]
  have hPartition :=
    sum_heathBrownOffDiagonalPairs_eq_sum_differenceBins hSep hInterval F
  have hRewrite :
      (∑ j ∈ Finset.range (Nat.log 2 (Nat.floor T) + 1),
          if 2 ^ (j + 1) ≤ N then gmNonzeroTailBinMoment cutoff N W j else 0) =
        ∑ p ∈ heathBrownOffDiagonalPairs W, F p := by
    rw [hPartition]
    apply Finset.sum_congr rfl
    intro j hj
    exact (hBin j).symm
  rw [hRewrite]
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hCardNat : (heathBrownOffDiagonalPairs W).card ≤ W.card ^ 2 := by
    calc
      (heathBrownOffDiagonalPairs W).card ≤ (W ×ˢ W).card := by
        apply Finset.card_le_card
        intro p hp
        exact (Finset.mem_filter.mp hp).1
      _ = W.card ^ 2 := by simp [pow_two]
  have hCard : ((heathBrownOffDiagonalPairs W).card : ℝ) ≤
      (W.card : ℝ) ^ 2 := by exact_mod_cast hCardNat
  calc
    (∑ p ∈ heathBrownOffDiagonalPairs W, F p) ≤
        ∑ _p ∈ heathBrownOffDiagonalPairs W, D ^ 2 * (N : ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      by_cases hScale :
          2 ^ (heathBrownDifferenceScale p.1 p.2 + 1) ≤ N
      · have hpData := Finset.mem_filter.mp hp
        have hpW := Finset.mem_product.mp hpData.1
        have hLower : 1 ≤ |p.1 - p.2| := by
          simpa [Real.dist_eq] using
            hSep p.1 hpW.1 p.2 hpW.2 hpData.2
        have hBounds := heathBrownDifferenceScale_bounds hLower
        have hScaleR :
            (((2 ^ (heathBrownDifferenceScale p.1 p.2 + 1) : ℕ) : ℝ)) ≤
              (N : ℝ) := by exact_mod_cast hScale
        have hAbs : |p.1 - p.2| ≤ (N : ℝ) := hBounds.2.le.trans hScaleR
        have hPoint := hTail N (p.1 - p.2) hN hAbs
        have hSq := pow_le_pow_left₀ (norm_nonneg _) hPoint 2
        have hSqrtSq : (Real.sqrt (N : ℝ)) ^ 2 = (N : ℝ) :=
          Real.sq_sqrt hNr.le
        dsimp only [F]
        rw [if_pos hScale]
        calc
          ‖gmTraceNonzeroTailAt cutoff N (p.1 - p.2)‖ ^ 2 ≤
              (D * Real.sqrt N) ^ 2 := hSq
          _ = D ^ 2 * (N : ℝ) := by rw [mul_pow, hSqrtSq]
      · dsimp only [F]
        rw [if_neg hScale]
        positivity
    _ = ((heathBrownOffDiagonalPairs W).card : ℝ) *
        (D ^ 2 * (N : ℝ)) := by simp
    _ ≤ (W.card : ℝ) ^ 2 * (D ^ 2 * (N : ℝ)) :=
      mul_le_mul_of_nonneg_right hCard (by positivity)
    _ = D ^ 2 * (N : ℝ) * (W.card : ℝ) ^ 2 := by ring

/-- The exact Poisson identity also gives the reverse triangle inequality
needed to estimate the nonzero tail from the physical trace polynomial and
the zero Fourier mode. -/
theorem norm_gmTraceNonzeroTailAt_le_trace_add_zero
    (cutoff : GMSmoothCutoff) (N : ℕ) (hN : 0 < N) (t : ℝ) :
    ‖gmTraceNonzeroTailAt cutoff N t‖ ≤
      ‖heathBrownTracePolynomial cutoff N t‖ +
        ‖gmTraceZeroMode cutoff N t‖ := by
  have hPhase : ‖(N : ℂ) ^ ((t : ℂ) * I)‖ = 1 := by
    rw [Complex.norm_natCast_cpow_of_pos hN]
    simp
  have hNormSum :
      ‖gmTraceZeroMode cutoff N t + gmTraceNonzeroTailAt cutoff N t‖ =
        ‖heathBrownTracePolynomial cutoff N t‖ := by
    rw [heathBrownTracePolynomial_eq_phase_mul_zero_add_tail cutoff N hN t,
      norm_mul, hPhase, one_mul]
  calc
    ‖gmTraceNonzeroTailAt cutoff N t‖ =
        ‖(gmTraceZeroMode cutoff N t + gmTraceNonzeroTailAt cutoff N t) -
          gmTraceZeroMode cutoff N t‖ := by congr 1; ring
    _ ≤ ‖gmTraceZeroMode cutoff N t + gmTraceNonzeroTailAt cutoff N t‖ +
          ‖gmTraceZeroMode cutoff N t‖ := norm_sub_le _ _
    _ = _ := by rw [hNormSum]

/-- Below the physical polynomial scale the complete nonzero Poisson tail
has the same `N / |t|` nonstationary decay as the source trace polynomial.
This is the literal low-frequency input omitted by an all-bin reflection
schedule. -/
theorem exists_norm_gmTraceNonzeroTailAt_le_div
    (cutoff : GMSmoothCutoff) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (t : ℝ), 0 < N →
      1 ≤ |t| → |t| ≤ (N : ℝ) →
      ‖gmTraceNonzeroTailAt cutoff N t‖ ≤ C * (N : ℝ) / |t| := by
  obtain ⟨C₁, hC₁, hTrace⟩ :=
    exists_norm_heathBrownTracePolynomial_le_div cutoff
  obtain ⟨C₀, hC₀, hZero⟩ :=
    gmTraceZeroMode_separated_bound cutoff 1
  refine ⟨C₁ + C₀, by positivity, ?_⟩
  intro N t hN htOne htN
  have htPos : 0 < |t| := zero_lt_one.trans_le htOne
  have hTail := norm_gmTraceNonzeroTailAt_le_trace_add_zero cutoff N hN t
  have hTraceAt := hTrace N t hN htOne htN
  have hZeroAt := hZero N (show 0 < |t| from htPos) (le_rfl)
  calc
    ‖gmTraceNonzeroTailAt cutoff N t‖ ≤
        ‖heathBrownTracePolynomial cutoff N t‖ +
          ‖gmTraceZeroMode cutoff N t‖ := hTail
    _ ≤ C₁ * (N : ℝ) / |t| + (N : ℝ) * C₀ / |t| ^ 1 :=
      add_le_add hTraceAt hZeroAt
    _ = (C₁ + C₀) * (N : ℝ) / |t| := by ring

/-- Source-sharp nonstationary estimate for one dyadic displacement fiber
of the literal nonzero tail. -/
theorem exists_gmNonzeroTailBinMoment_near_bound
    (cutoff : GMSmoothCutoff) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N : ℕ) (W : Finset ℝ) (j : ℕ),
        0 < N → IsSeparated 1 W → 2 ^ (j + 1) ≤ N →
        gmNonzeroTailBinMoment cutoff N W j ≤
          4 * (W.card : ℝ) * C ^ 2 * (N : ℝ) ^ 2 /
            ((2 ^ j : ℕ) : ℝ) := by
  obtain ⟨C, hC, hTail⟩ := exists_norm_gmTraceNonzeroTailAt_le_div cutoff
  refine ⟨C, hC, ?_⟩
  intro N W j hN hSep hjN
  have hCardNat := heathBrownDifferenceBin_card_le W j hSep
  have hCard : ((heathBrownDifferenceBin W j).card : ℝ) ≤
      (W.card : ℝ) * (2 * 2 ^ (j + 1) : ℕ) := by
    exact_mod_cast hCardNat
  have hPowPos : (0 : ℝ) < ((2 ^ j : ℕ) : ℝ) := by positivity
  unfold gmNonzeroTailBinMoment
  calc
    (∑ p ∈ heathBrownDifferenceBin W j,
        ‖gmTraceNonzeroTailAt cutoff N (p.1 - p.2)‖ ^ 2) ≤
      ∑ _p ∈ heathBrownDifferenceBin W j,
        (C * (N : ℝ) / (2 ^ j : ℕ)) ^ 2 := by
          apply Finset.sum_le_sum
          intro p hp
          have hBounds := heathBrownDifferenceBin_bounds hSep hp
          have hUpper : |p.1 - p.2| ≤ (N : ℝ) := by
            have hCast : ((2 ^ (j + 1) : ℕ) : ℝ) ≤ N := by
              exact_mod_cast hjN
            exact hBounds.2.le.trans hCast
          have hOnePow : (1 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) := by
            exact_mod_cast (Nat.one_le_pow j 2 (by omega))
          have hPoint := hTail N (p.1 - p.2) hN
            (hOnePow.trans hBounds.1) hUpper
          have hDenom : C * (N : ℝ) / |p.1 - p.2| ≤
              C * (N : ℝ) / (2 ^ j : ℕ) := by
            exact div_le_div_of_nonneg_left (by positivity) hPowPos hBounds.1
          exact pow_le_pow_left₀ (norm_nonneg _) (hPoint.trans hDenom) 2
    _ = ((heathBrownDifferenceBin W j).card : ℝ) *
        (C * (N : ℝ) / (2 ^ j : ℕ)) ^ 2 := by simp
    _ ≤ ((W.card : ℝ) * (2 * 2 ^ (j + 1) : ℕ)) *
        (C * (N : ℝ) / (2 ^ j : ℕ)) ^ 2 :=
      mul_le_mul_of_nonneg_right hCard (sq_nonneg _)
    _ = 4 * (W.card : ℝ) * C ^ 2 * (N : ℝ) ^ 2 /
        ((2 ^ j : ℕ) : ℝ) := by
      rw [pow_succ]
      push_cast
      field_simp
      ring

/-- The stationary part of the exact Section 6 bin schedule.  Empty fibers
and fibers lying wholly below the physical polynomial scale contribute zero;
the latter are estimated *together* by `gmNearScaleBinSum_le_sqrt`. -/
noncomputable def gmS2SourceScheduledBinBound
    (A K L C : ℝ) (q k : ℕ) (η : ℝ)
    (N : ℕ) (T : ℝ) (W : Finset ℝ) (H j : ℕ) : ℝ :=
  if (heathBrownDifferenceBin W j).Nonempty then
    if 2 ^ (j + 1) ≤ N then
      0
    else gmS2PhysicalBinBound A K L C q k η N T W H j
  else 0

/-- Exact diagonal/nonstationary/stationary reduction of the literal
nonzero Poisson-tail moment in Proposition 6.1.  The nonstationary fibers
are aggregated through the exact dyadic partition, yielding `N * R^2`
rather than the false local-density majorant from the provisional schedule. -/
theorem gmTraceNonzeroDifferenceMoment_le_source_schedule
    (cutoff : GMSmoothCutoff) (q k : ℕ) (hq : 2 ≤ q)
    (η : ℝ) (hk : 0 < k) (hη : 0 < η) :
    ∃ D A K L C B T_min : ℝ,
      0 < D ∧ 0 < A ∧ 0 < K ∧ 0 < L ∧ 0 < C ∧
      0 < B ∧ 1 ≤ T_min ∧
      ∀ {N H : ℕ} {T δ : ℝ} (W : Finset ℝ),
        T_min ≤ T → 0 < N → 0 < H → 4 * (H : ℝ) ≤ δ →
        IsSeparated δ W → InBaseInterval T W → W.Nonempty →
        gmTraceNonzeroDifferenceMoment cutoff N W ≤
          D ^ 2 * (N : ℝ) * (W.card : ℝ) ^ 2 +
            (W.card : ℝ) * (B / (N : ℝ) ^ (q - 1)) ^ 2 +
            ∑ j ∈ Finset.range (Nat.log 2 (Nat.floor T) + 1),
              gmS2SourceScheduledBinBound
                A K L C q k η N T W H j := by
  obtain ⟨D, hD, hNearPoint⟩ :=
    exists_norm_gmTraceNonzeroTailAt_le_sqrt_near cutoff
  obtain ⟨A, K, L, C, T_ref, hA, hK, hL, hC, hT_ref, hBin⟩ :=
    gmNonzeroTailBinMoment_le_powered_reflection
      cutoff q k hq η hk hη
  obtain ⟨B, hB, hDiag⟩ := gmTraceNonzeroDiagonalMoment_le cutoff q hq
  refine ⟨D, A, K, L, C, B, T_ref, hD, hA, hK, hL, hC,
    hB, hT_ref, ?_⟩
  intro N H T δ W hT hN hH hHδ hSep hBase hW
  have hδOne : 1 ≤ δ := by
    have hHOne : (1 : ℝ) ≤ H := by exact_mod_cast hH
    linarith
  have hSepOne : IsSeparated 1 W := by
    intro x hx y hy hxy
    exact hδOne.trans (hSep x hx y hy hxy)
  have hTNonneg : 0 ≤ T := zero_le_one.trans (hT_ref.trans hT)
  have hNear := gmNearScaleBinSum_le_sqrt cutoff hNearPoint hSepOne hBase hN
  have hEach : ∀ j ∈ Finset.range (Nat.log 2 (Nat.floor T) + 1),
      gmNonzeroTailBinMoment cutoff N W j ≤
        (if 2 ^ (j + 1) ≤ N then
          gmNonzeroTailBinMoment cutoff N W j else 0) +
        gmS2SourceScheduledBinBound A K L C q k η N T W H j := by
    intro j hj
    by_cases hOccupied : (heathBrownDifferenceBin W j).Nonempty
    · by_cases hNearScale : 2 ^ (j + 1) ≤ N
      · rw [if_pos hNearScale, gmS2SourceScheduledBinBound,
          if_pos hOccupied, if_pos hNearScale, add_zero]
      · have hOcc := hOccupied
        obtain ⟨p, hp⟩ := hOcc
        have hpFilter := Finset.mem_filter.mp hp
        have hpOff := Finset.mem_filter.mp hpFilter.1
        have hpW := Finset.mem_product.mp hpOff.1
        have hDelta : δ ≤ |p.1 - p.2| := by
          simpa only [Real.dist_eq] using
            hSep p.1 hpW.1 p.2 hpW.2 hpOff.2
        have hBounds := heathBrownDifferenceBin_bounds hSepOne hp
        have hjTwo : 2 ≤ j := by
          have hFour : (4 : ℝ) ≤ δ := by
            have hHOne : (1 : ℝ) ≤ H := by exact_mod_cast hH
            linarith
          by_contra hnot
          have hjSmall : j ≤ 1 := by omega
          interval_cases j <;> norm_num at hBounds ⊢ <;>
            linarith [hBounds.2, hDelta, hFour]
        have hHeightLower : (1 : ℝ) ≤ H := by exact_mod_cast hH
        have hHeightUpper : (H : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) / 2 := by
          have hPowSucc : (((2 ^ (j + 1) : ℕ) : ℝ)) =
              2 * (((2 ^ j : ℕ) : ℝ)) := by
            rw [pow_succ]
            norm_num
            ring
          rw [hPowSucc] at hBounds
          linarith
        have hPowered := hBin hT hSepOne hBase hW hjTwo hHeightLower
          hHeightUpper hN (heathBrownFixedReflectionLength_pos N H j)
        have hPhysical := gmS2PoweredBinBound_le_physical
          (A := A) (K := K) (L := L) (C := C) (q := q) (k := k)
          (N := N) (H := H) (j := j) (η := η) (T := T) (W := W)
          hC.le hTNonneg hk hN hH
        rw [if_neg hNearScale, zero_add, gmS2SourceScheduledBinBound,
          if_pos hOccupied, if_neg hNearScale]
        exact hPowered.trans (by
          simpa only [gmS2PoweredBinBound] using hPhysical)
    · have hEq : heathBrownDifferenceBin W j = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp hOccupied
      rw [gmS2SourceScheduledBinBound, if_neg hOccupied]
      simp [gmNonzeroTailBinMoment, hEq]
  rw [gmTraceNonzeroDifferenceMoment_eq_diagonal_add_bins hSepOne hBase]
  have hBins := Finset.sum_le_sum hEach
  rw [Finset.sum_add_distrib] at hBins
  calc
    gmTraceNonzeroDiagonalMoment cutoff N W +
        ∑ j ∈ Finset.range (Nat.log 2 (Nat.floor T) + 1),
          gmNonzeroTailBinMoment cutoff N W j ≤
      (W.card : ℝ) * (B / (N : ℝ) ^ (q - 1)) ^ 2 +
        ((∑ j ∈ Finset.range (Nat.log 2 (Nat.floor T) + 1),
            if 2 ^ (j + 1) ≤ N then
              gmNonzeroTailBinMoment cutoff N W j else 0) +
          ∑ j ∈ Finset.range (Nat.log 2 (Nat.floor T) + 1),
            gmS2SourceScheduledBinBound A K L C q k η N T W H j) :=
      add_le_add (hDiag W hN) hBins
    _ ≤ (W.card : ℝ) * (B / (N : ℝ) ^ (q - 1)) ^ 2 +
        (D ^ 2 * (N : ℝ) * (W.card : ℝ) ^ 2 +
          ∑ j ∈ Finset.range (Nat.log 2 (Nat.floor T) + 1),
            gmS2SourceScheduledBinBound A K L C q k η N T W H j) := by
      gcongr
    _ = D ^ 2 * (N : ℝ) * (W.card : ℝ) ^ 2 +
        (W.card : ℝ) * (B / (N : ℝ) ^ (q - 1)) ^ 2 +
          ∑ j ∈ Finset.range (Nat.log 2 (Nat.floor T) + 1),
            gmS2SourceScheduledBinBound A K L C q k η N T W H j := by ring

/-! ## Source-shaped aggregation of the stationary main terms -/

theorem gmS2_dyadic_scale_le_height
    {T : ℝ} {j : ℕ}
    (hj : j ∈ Finset.range (Nat.log 2 (Nat.floor T) + 1))
    (hjTwo : 2 ≤ j) :
    (((2 ^ j : ℕ) : ℝ)) ≤ T := by
  have hPow := two_pow_le_floor_of_mem_difference_range hj hjTwo
  calc
    (((2 ^ j : ℕ) : ℝ)) ≤ (Nat.floor T : ℝ) := by exact_mod_cast hPow
    _ ≤ T := Nat.floor_le (by
      have : 0 < Nat.floor T := lt_of_lt_of_le (by positivity) hPow
      exact zero_le_one.trans (Nat.floor_pos.mp this))

theorem gmS2_not_near_inverse_scale
    {N j : ℕ} (hN : 0 < N) (hNotNear : ¬ 2 ^ (j + 1) ≤ N) :
    (N : ℝ) ^ 2 / ((2 ^ j : ℕ) : ℝ) ≤ 2 * (N : ℝ) := by
  have hNlt : N < 2 ^ (j + 1) := by omega
  have hNle : (N : ℝ) ≤ 2 * (((2 ^ j : ℕ) : ℝ)) := by
    have hCast : (N : ℝ) ≤ ((2 ^ (j + 1) : ℕ) : ℝ) := by
      exact_mod_cast hNlt.le
    rw [pow_succ] at hCast
    push_cast at hCast
    simpa [mul_comm] using hCast
  have hXPos : (0 : ℝ) < ((2 ^ j : ℕ) : ℝ) := by positivity
  rw [div_le_iff₀ hXPos]
  have hNReal : 0 ≤ (N : ℝ) := by positivity
  nlinarith

theorem gmS2_card_rpow_sub_inv_le_sq
    {W : Finset ℝ} {k : ℕ} (hW : W.Nonempty) (hk : 0 < k) :
    (W.card : ℝ) ^ (2 - 1 / (k : ℝ)) ≤ (W.card : ℝ) ^ 2 := by
  have hR : (1 : ℝ) ≤ W.card := by exact_mod_cast hW.card_pos
  have hkReal : (0 : ℝ) < k := by exact_mod_cast hk
  calc
    (W.card : ℝ) ^ (2 - 1 / (k : ℝ)) ≤
        (W.card : ℝ) ^ (2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hR (by
        have hInv : 0 ≤ 1 / (k : ℝ) := by positivity
        linarith)
    _ = (W.card : ℝ) ^ 2 := by norm_num

theorem gmS2_card_rpow_sub_three_quarter_inv_le_sq
    {W : Finset ℝ} {k : ℕ} (hW : W.Nonempty) (hk : 0 < k) :
    (W.card : ℝ) ^ (2 - 3 / (4 * (k : ℝ))) ≤ (W.card : ℝ) ^ 2 := by
  have hR : (1 : ℝ) ≤ W.card := by exact_mod_cast hW.card_pos
  have hkReal : (0 : ℝ) < k := by exact_mod_cast hk
  calc
    (W.card : ℝ) ^ (2 - 3 / (4 * (k : ℝ))) ≤
        (W.card : ℝ) ^ (2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hR (by
        have hInv : 0 ≤ 3 / (4 * (k : ℝ)) := by positivity
        linarith)
    _ = (W.card : ℝ) ^ 2 := by norm_num

/-- The three source terms in Proposition 6.1 before reinserting the outer
zero mode. -/
noncomputable def gmS2TracePaperShape
    (k N : ℕ) (T : ℝ) (W : Finset ℝ) : ℝ :=
  (N : ℝ) * (W.card : ℝ) ^ 2 +
    T * (W.card : ℝ) ^ (2 - 1 / (k : ℝ)) +
    (N : ℝ) * (W.card : ℝ) ^ (2 - 3 / (4 * (k : ℝ))) *
      T ^ (1 / (2 * (k : ℝ)))

theorem gmS2TracePaperShape_nonneg
    {k N : ℕ} {T : ℝ} {W : Finset ℝ} (hT : 0 ≤ T) :
    0 ≤ gmS2TracePaperShape k N T W := by
  unfold gmS2TracePaperShape
  positivity

/-- An occupied source-schedule bin above the nonstationary cutoff satisfies
the two stationary hypotheses required by the reflection theorem.  The
factor `4H` is exactly the spacing reserved in the Section 6 extraction. -/
theorem gmS2_occupied_far_stationary
    {N H j : ℕ} {δ : ℝ} {W : Finset ℝ}
    (hH : 0 < H) (hHδ : 4 * (H : ℝ) ≤ δ)
    (hSep : IsSeparated δ W) (hSepOne : IsSeparated 1 W)
    (hOccupied : (heathBrownDifferenceBin W j).Nonempty)
    (hNotNear : ¬ 2 ^ (j + 1) ≤ N) :
    2 ≤ j ∧ 2 * H ≤ 2 ^ j := by
  obtain ⟨p, hp⟩ := hOccupied
  have hpFilter := Finset.mem_filter.mp hp
  have hpOff := Finset.mem_filter.mp hpFilter.1
  have hpW := Finset.mem_product.mp hpOff.1
  have hDelta : δ ≤ |p.1 - p.2| := by
    simpa only [Real.dist_eq] using
      hSep p.1 hpW.1 p.2 hpW.2 hpOff.2
  have hBounds := heathBrownDifferenceBin_bounds hSepOne hp
  have hHOne : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hFour : (4 : ℝ) ≤ δ := by linarith
  have hjTwo : 2 ≤ j := by
    by_contra hnot
    have hjSmall : j ≤ 1 := by omega
    interval_cases j <;> norm_num at hBounds ⊢ <;>
      linarith [hBounds.2, hDelta, hFour]
  have hHeightUpper : (H : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) / 2 := by
    have hPowSucc : (((2 ^ (j + 1) : ℕ) : ℝ)) =
        2 * (((2 ^ j : ℕ) : ℝ)) := by
      rw [pow_succ]
      norm_num
      ring
    rw [hPowSucc] at hBounds
    linarith
  constructor
  · exact hjTwo
  · exact_mod_cast (show (2 : ℝ) * H ≤ (2 ^ j : ℕ) by linarith)

/-- After excluding the nonstationary range, one reflected physical bin has
exactly the three scale shapes appearing in equation (6.4), up to the
explicit fixed-power and epsilon profile. -/
theorem gmS2PhysicalBinSourceBound_le_paperShape
    {A C η T : ℝ} {k N H j : ℕ} {W : Finset ℝ}
    (hC : 0 ≤ C) (hT : 1 ≤ T) (hk : 0 < k)
    (hη : 0 ≤ η)
    (hN : 0 < N)
    (hW : W.Nonempty)
    (hj : j ∈ Finset.range (Nat.log 2 (Nat.floor T) + 1))
    (hjTwo : 2 ≤ j) (hNotNear : ¬ 2 ^ (j + 1) ≤ N) :
    gmS2PhysicalBinSourceBound A C k η T W N H j ≤
      192 * (((k : ℝ) ^ 2 * C ^ 3) ^ (1 / (k : ℝ))) * A ^ 2 *
        T ^ (η / (k : ℝ)) *
        heathBrownLocalRecurrenceProfile η T N H ^ 6 *
        gmS2TracePaperShape k N T W := by
  let X : ℝ := ((2 ^ j : ℕ) : ℝ)
  let n : ℝ := N
  let h : ℝ := H
  let R : ℝ := W.card
  let G : ℝ := heathBrownLocalRecurrenceProfile η T N H
  let D : ℝ := (((k : ℝ) ^ 2 * C ^ 3) ^ (1 / (k : ℝ)))
  let F : ℝ := D * T ^ (η / (k : ℝ)) *
    (2 * (heathBrownFixedReflectionLength N H j : ℝ)) ^ (2 * η)
  have hX : 0 < X := by dsimp only [X]; positivity
  have hn : 0 < n := by dsimp only [n]; exact_mod_cast hN
  have hT0 : 0 ≤ T := zero_le_one.trans hT
  have hGOne : 1 ≤ G := by
    dsimp only [G]
    exact heathBrownLocalRecurrenceProfile_components.1
  have hHle : h ≤ G := by
    dsimp only [h, G]
    exact heathBrownLocalRecurrenceProfile_components.2.2.1
  have hH2 : h ^ 2 ≤ G ^ 2 := pow_le_pow_left₀ (by positivity) hHle 2
  have hH3 : h ^ 3 ≤ G ^ 3 := pow_le_pow_left₀ (by positivity) hHle 3
  have hH4 : h ^ 4 ≤ G ^ 4 := pow_le_pow_left₀ (by positivity) hHle 4
  have hG2le4 : G ^ 2 ≤ G ^ 4 := by
    calc
      G ^ 2 = 1 * G ^ 2 := by ring
      _ ≤ G ^ 2 * G ^ 2 := by
        gcongr
        exact one_le_pow₀ hGOne
      _ = G ^ 4 := by ring
  have hG3le4 : G ^ 3 ≤ G ^ 4 := by
    have hG0 : 0 ≤ G := zero_le_one.trans hGOne
    calc
      G ^ 3 = 1 * G ^ 3 := by ring
      _ ≤ G * G ^ 3 := mul_le_mul_of_nonneg_right hGOne (pow_nonneg hG0 3)
      _ = G ^ 4 := by ring
  have hInv : n ^ 2 / X ≤ 2 * n := by
    simpa only [n, X] using gmS2_not_near_inverse_scale hN hNotNear
  have hXle : X ≤ T := by
    simpa only [X] using gmS2_dyadic_scale_le_height hj hjTwo
  have hRmid : R ^ (2 - 1 / (k : ℝ)) ≤ R ^ 2 := by
    simpa only [R] using gmS2_card_rpow_sub_inv_le_sq hW hk
  have hRthird : R ^ (2 - 3 / (4 * (k : ℝ))) ≤ R ^ 2 := by
    simpa only [R] using
      gmS2_card_rpow_sub_three_quarter_inv_le_sq hW hk
  have hLoss := gmS2FixedLengthEpsilonLoss_le_profile_sq
    (η := η) (N := N) (H := H) (j := j) (T := T) hη hj hjTwo
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hTpow : 0 ≤ T ^ (η / (k : ℝ)) := Real.rpow_nonneg hT0 _
  have hF : F ≤ D * T ^ (η / (k : ℝ)) * G ^ 2 := by
    dsimp only [F]
    exact mul_le_mul_of_nonneg_left hLoss (mul_nonneg hD hTpow)
  have hInnerOne : n * h ^ 3 + n ^ 2 * h ^ 2 / X ≤
      3 * n * G ^ 4 := by
    have hFirst : n * h ^ 3 ≤ n * G ^ 4 :=
      mul_le_mul_of_nonneg_left (hH3.trans hG3le4) hn.le
    have hSecond : n ^ 2 * h ^ 2 / X ≤ 2 * n * G ^ 4 := by
      calc
        n ^ 2 * h ^ 2 / X = (n ^ 2 / X) * h ^ 2 := by ring
        _ ≤ (2 * n) * G ^ 2 := by gcongr
        _ ≤ 2 * n * G ^ 4 := by gcongr
    linarith
  have hInnerTwo : X * h ^ 4 + n ^ 2 * h ^ 2 / X ≤
      T * G ^ 4 + 2 * n * G ^ 4 := by
    have hFirst : X * h ^ 4 ≤ T * G ^ 4 := by gcongr
    have hSecond : n ^ 2 * h ^ 2 / X ≤ 2 * n * G ^ 4 := by
      calc
        n ^ 2 * h ^ 2 / X = (n ^ 2 / X) * h ^ 2 := by ring
        _ ≤ (2 * n) * G ^ 2 := by gcongr
        _ ≤ 2 * n * G ^ 4 := by gcongr
    linarith
  have hShapeEq : gmS2TracePaperShape k N T W =
      n * R ^ 2 + T * R ^ (2 - 1 / (k : ℝ)) +
        n * R ^ (2 - 3 / (4 * (k : ℝ))) *
          T ^ (1 / (2 * (k : ℝ))) := by rfl
  have hBracket :
      16 * R ^ 2 * A ^ 2 * (n * h ^ 3 + n ^ 2 * h ^ 2 / X) +
        64 * R ^ (2 - 1 / (k : ℝ)) * A ^ 2 *
          (X * h ^ 4 + n ^ 2 * h ^ 2 / X) +
        16 * R ^ (2 - 3 / (4 * (k : ℝ))) *
          T ^ (1 / (2 * (k : ℝ))) * A ^ 2 *
          (n * h ^ 3 + n ^ 2 * h ^ 2 / X) ≤
      192 * A ^ 2 * G ^ 4 * gmS2TracePaperShape k N T W := by
    rw [hShapeEq]
    have hTermOne :
        16 * R ^ 2 * A ^ 2 * (n * h ^ 3 + n ^ 2 * h ^ 2 / X) ≤
          48 * A ^ 2 * G ^ 4 * (n * R ^ 2) := by
      calc
        _ ≤ 16 * R ^ 2 * A ^ 2 * (3 * n * G ^ 4) := by gcongr
        _ = _ := by ring
    have hTermTwo :
        64 * R ^ (2 - 1 / (k : ℝ)) * A ^ 2 *
            (X * h ^ 4 + n ^ 2 * h ^ 2 / X) ≤
          64 * A ^ 2 * G ^ 4 *
            (T * R ^ (2 - 1 / (k : ℝ)) + 2 * n * R ^ 2) := by
      calc
        _ ≤ 64 * R ^ (2 - 1 / (k : ℝ)) * A ^ 2 *
            (T * G ^ 4 + 2 * n * G ^ 4) := by gcongr
        _ = 64 * A ^ 2 * G ^ 4 *
            (T * R ^ (2 - 1 / (k : ℝ)) +
              2 * n * R ^ (2 - 1 / (k : ℝ))) := by ring
        _ ≤ 64 * A ^ 2 * G ^ 4 *
            (T * R ^ (2 - 1 / (k : ℝ)) + 2 * n * R ^ 2) := by
          gcongr
    have hTermThree :
        16 * R ^ (2 - 3 / (4 * (k : ℝ))) *
            T ^ (1 / (2 * (k : ℝ))) * A ^ 2 *
            (n * h ^ 3 + n ^ 2 * h ^ 2 / X) ≤
          48 * A ^ 2 * G ^ 4 *
            (n * R ^ (2 - 3 / (4 * (k : ℝ))) *
              T ^ (1 / (2 * (k : ℝ)))) := by
      calc
        _ ≤ 16 * R ^ (2 - 3 / (4 * (k : ℝ))) *
            T ^ (1 / (2 * (k : ℝ))) * A ^ 2 *
            (3 * n * G ^ 4) := by gcongr
        _ = _ := by ring
    have hK0 : 0 ≤ A ^ 2 * G ^ 4 := by positivity
    have hx : 0 ≤ n * R ^ 2 := by positivity
    have hy : 0 ≤ T * R ^ (2 - 1 / (k : ℝ)) := by positivity
    have hz : 0 ≤ n * R ^ (2 - 3 / (4 * (k : ℝ))) *
        T ^ (1 / (2 * (k : ℝ))) := by positivity
    nlinarith
  unfold gmS2PhysicalBinSourceBound
  dsimp only [X, n, h, R, F, D]
  calc
    F * (16 * R ^ 2 * A ^ 2 * (n * h ^ 3 + n ^ 2 * h ^ 2 / X) +
        64 * R ^ (2 - 1 / (k : ℝ)) * A ^ 2 *
          (X * h ^ 4 + n ^ 2 * h ^ 2 / X) +
        16 * R ^ (2 - 3 / (4 * (k : ℝ))) *
          T ^ (1 / (2 * (k : ℝ))) * A ^ 2 *
          (n * h ^ 3 + n ^ 2 * h ^ 2 / X)) ≤
      (D * T ^ (η / (k : ℝ)) * G ^ 2) *
        (192 * A ^ 2 * G ^ 4 * gmS2TracePaperShape k N T W) :=
      mul_le_mul hF hBracket (by positivity) (by positivity)
    _ = _ := by ring

/-- The stationary main term inside one physical scheduled bin, separated
from the two complete reflection-error terms. -/
noncomputable def gmS2PhysicalBinMain
    (A C : ℝ) (k : ℕ) (η T : ℝ) (W : Finset ℝ)
    (N H j : ℕ) : ℝ :=
  let M := heathBrownFixedReflectionLength N H j
  2 * ((Nat.clog 2 M : ℝ) + 1) *
    (gmS2ReflectionCoefficient A N H j * (W.card : ℝ) ^ 2 +
      (Nat.clog 2 M : ℝ) *
        gmS2PhysicalBinSourceBound A C k η T W N H j)

theorem gmS2PhysicalBinBound_eq_main_add_error
    (A K L C : ℝ) (q k : ℕ) (η : ℝ)
    (N : ℕ) (T : ℝ) (W : Finset ℝ) (H j : ℕ) :
    gmS2PhysicalBinBound A K L C q k η N T W H j =
      gmS2PhysicalBinMain A C k η T W N H j +
        2 * ((heathBrownDifferenceBin W j).card : ℝ) *
          (gmNonzeroTailBinError q N
            (heathBrownFixedReflectionLength N H j) H
            (((2 ^ (j + 1) : ℕ) : ℝ)) K L) ^ 2 := by
  rfl

/-- Uniform source-shaped estimate for one stationary main bin.  Every
dyadic logarithm, smoothing height and finite-power coefficient is kept in
the common recurrence profile so that it can later be absorbed by `T^ε`. -/
theorem gmS2PhysicalBinMain_le_paperShape
    {A C η T : ℝ} {k N H j : ℕ} {W : Finset ℝ}
    (hC : 0 ≤ C) (hT : 1 ≤ T) (hk : 0 < k)
    (hη : 0 ≤ η) (hN : 0 < N) (hW : W.Nonempty)
    (hj : j ∈ Finset.range (Nat.log 2 (Nat.floor T) + 1))
    (hjTwo : 2 ≤ j) (hNotNear : ¬ 2 ^ (j + 1) ≤ N) :
    gmS2PhysicalBinMain A C k η T W N H j ≤
      400 * (1 + A ^ 2 +
          (((k : ℝ) ^ 2 * C ^ 3) ^ (1 / (k : ℝ))) * A ^ 2 *
            T ^ (η / (k : ℝ))) *
        heathBrownLocalRecurrenceProfile η T N H ^ 8 *
          gmS2TracePaperShape k N T W := by
  let M : ℕ := heathBrownFixedReflectionLength N H j
  let ell : ℝ := Nat.clog 2 M
  let G : ℝ := heathBrownLocalRecurrenceProfile η T N H
  let P : ℝ := gmS2TracePaperShape k N T W
  let J : ℝ := (((k : ℝ) ^ 2 * C ^ 3) ^ (1 / (k : ℝ))) *
    A ^ 2 * T ^ (η / (k : ℝ))
  have hGOne : 1 ≤ G := by
    dsimp only [G]
    exact heathBrownLocalRecurrenceProfile_components.1
  have hG0 : 0 ≤ G := zero_le_one.trans hGOne
  have hP0 : 0 ≤ P := by
    dsimp only [P]
    exact gmS2TracePaperShape_nonneg (zero_le_one.trans hT)
  have hJ0 : 0 ≤ J := by dsimp only [J]; positivity
  have hEllOne : ell + 1 ≤ G := by
    have hNat := gmS2FixedClog_add_one_le_commonExponent
      (N := N) (H := H) hj hjTwo
    have hCast : ((Nat.clog 2 M + 1 : ℕ) : ℝ) ≤
        (heathBrownCorrectedCommonExponent N H T : ℝ) := by
      exact_mod_cast hNat
    have hComponent :=
      (heathBrownLocalRecurrenceProfile_components
        (η := η) (T := T) (Q := N) (H := H)).2.2.2.1
    dsimp only [ell, M, G]
    push_cast at hCast
    exact hCast.trans hComponent
  have hEll : ell ≤ G := by linarith
  have hEll0 : 0 ≤ ell := by dsimp only [ell]; positivity
  have hHle : (H : ℝ) ≤ G := by
    dsimp only [G]
    exact heathBrownLocalRecurrenceProfile_components.2.2.1
  have hHsq : (H : ℝ) ^ 2 ≤ G ^ 2 :=
    pow_le_pow_left₀ (by positivity) hHle 2
  have hInv := gmS2_not_near_inverse_scale hN hNotNear
  have hFirstShape : (N : ℝ) * (W.card : ℝ) ^ 2 ≤ P := by
    dsimp only [P, gmS2TracePaperShape]
    have hSecond : 0 ≤ T * (W.card : ℝ) ^ (2 - 1 / (k : ℝ)) := by
      positivity
    have hThird : 0 ≤ (N : ℝ) *
        (W.card : ℝ) ^ (2 - 3 / (4 * (k : ℝ))) *
          T ^ (1 / (2 * (k : ℝ))) := by positivity
    linarith
  have hCoeff : gmS2ReflectionCoefficient A N H j * (W.card : ℝ) ^ 2 ≤
      16 * A ^ 2 * G ^ 2 * P := by
    rw [gmS2ReflectionCoefficient_eq]
    calc
      (8 * (N : ℝ) ^ 2 * A ^ 2 * H ^ 2 /
          ((2 ^ j : ℕ) : ℝ)) * (W.card : ℝ) ^ 2 =
          8 * A ^ 2 * (H : ℝ) ^ 2 * (W.card : ℝ) ^ 2 *
            ((N : ℝ) ^ 2 / ((2 ^ j : ℕ) : ℝ)) := by ring
      _ ≤ 8 * A ^ 2 * G ^ 2 * (W.card : ℝ) ^ 2 *
            (2 * (N : ℝ)) := by gcongr
      _ = 16 * A ^ 2 * G ^ 2 *
            ((N : ℝ) * (W.card : ℝ) ^ 2) := by ring
      _ ≤ 16 * A ^ 2 * G ^ 2 * P := by gcongr
  have hSource := gmS2PhysicalBinSourceBound_le_paperShape
    (A := A) (C := C) (η := η) (T := T) (k := k) (N := N)
    (H := H) (j := j) (W := W) hC hT hk hη hN hW hj hjTwo hNotNear
  have hSource' : gmS2PhysicalBinSourceBound A C k η T W N H j ≤
      192 * J * G ^ 6 * P := by
    simpa only [J, G, P, mul_assoc] using hSource
  have hG2le8 : G ^ 2 ≤ G ^ 8 :=
    pow_le_pow_right₀ hGOne (by omega)
  have hG3le8 : G ^ 3 ≤ G ^ 8 :=
    pow_le_pow_right₀ hGOne (by omega)
  have hCoeff0 : 0 ≤ gmS2ReflectionCoefficient A N H j := by
    unfold gmS2ReflectionCoefficient
    positivity
  have hSource0 : 0 ≤ gmS2PhysicalBinSourceBound A C k η T W N H j := by
    unfold gmS2PhysicalBinSourceBound
    positivity
  unfold gmS2PhysicalBinMain
  dsimp only [M, ell]
  calc
    2 * (ell + 1) *
        (gmS2ReflectionCoefficient A N H j * (W.card : ℝ) ^ 2 +
          ell * gmS2PhysicalBinSourceBound A C k η T W N H j) ≤
      2 * G * (16 * A ^ 2 * G ^ 2 * P +
        G * (192 * J * G ^ 6 * P)) := by gcongr
    _ = 32 * A ^ 2 * G ^ 3 * P + 384 * J * G ^ 8 * P := by ring
    _ ≤ 32 * A ^ 2 * G ^ 8 * P + 384 * J * G ^ 8 * P := by
      gcongr
    _ ≤ 400 * (1 + A ^ 2 + J) * G ^ 8 * P := by
      have hA0 : 0 ≤ A ^ 2 := sq_nonneg A
      nlinarith [mul_nonneg (mul_nonneg hG0 (pow_nonneg hG0 7)) hP0,
        mul_nonneg hJ0 (mul_nonneg (pow_nonneg hG0 8) hP0)]

noncomputable def gmS2ScheduledMain
    (A C : ℝ) (k : ℕ) (η : ℝ)
    (N : ℕ) (T : ℝ) (W : Finset ℝ) (H j : ℕ) : ℝ :=
  if (heathBrownDifferenceBin W j).Nonempty then
    if 2 ^ (j + 1) ≤ N then 0
    else gmS2PhysicalBinMain A C k η T W N H j
  else 0

noncomputable def gmS2ScheduledError
    (K L : ℝ) (q : ℕ)
    (N : ℕ) (W : Finset ℝ) (H j : ℕ) : ℝ :=
  if (heathBrownDifferenceBin W j).Nonempty then
    if 2 ^ (j + 1) ≤ N then 0
    else 2 * ((heathBrownDifferenceBin W j).card : ℝ) *
      (gmNonzeroTailBinError q N
        (heathBrownFixedReflectionLength N H j) H
        (((2 ^ (j + 1) : ℕ) : ℝ)) K L) ^ 2
  else 0

theorem gmS2SourceScheduledBinBound_eq_main_add_error
    (A K L C : ℝ) (q k : ℕ) (η : ℝ)
    (N : ℕ) (T : ℝ) (W : Finset ℝ) (H j : ℕ) :
    gmS2SourceScheduledBinBound A K L C q k η N T W H j =
      gmS2ScheduledMain A C k η N T W H j +
        gmS2ScheduledError K L q N W H j := by
  by_cases hOcc : (heathBrownDifferenceBin W j).Nonempty
  · by_cases hNear : 2 ^ (j + 1) ≤ N
    · simp [gmS2SourceScheduledBinBound, gmS2ScheduledMain,
        gmS2ScheduledError, hOcc, hNear]
    · simp only [gmS2SourceScheduledBinBound, gmS2ScheduledMain,
        gmS2ScheduledError, hOcc, hNear, if_pos]
      exact gmS2PhysicalBinBound_eq_main_add_error
        A K L C q k η N T W H j
  · simp [gmS2SourceScheduledBinBound, gmS2ScheduledMain,
      gmS2ScheduledError, hOcc]

/-- Summation of all stationary main bins.  The number of dyadic fibers is
itself one component of the local recurrence profile. -/
theorem sum_gmS2ScheduledMain_le_paperShape
    {A C η T δ : ℝ} {k N H : ℕ} {W : Finset ℝ}
    (hC : 0 ≤ C) (hT : 1 ≤ T) (hk : 0 < k)
    (hη : 0 ≤ η) (hN : 0 < N) (hH : 0 < H)
    (hW : W.Nonempty) (hHδ : 4 * (H : ℝ) ≤ δ)
    (hSep : IsSeparated δ W) (hSepOne : IsSeparated 1 W) :
    (∑ j ∈ Finset.range (Nat.log 2 (Nat.floor T) + 1),
        gmS2ScheduledMain A C k η N T W H j) ≤
      400 * (1 + A ^ 2 +
          (((k : ℝ) ^ 2 * C ^ 3) ^ (1 / (k : ℝ))) * A ^ 2 *
            T ^ (η / (k : ℝ))) *
        heathBrownLocalRecurrenceProfile η T N H ^ 9 *
          gmS2TracePaperShape k N T W := by
  let G : ℝ := heathBrownLocalRecurrenceProfile η T N H
  let B : ℝ := 400 * (1 + A ^ 2 +
      (((k : ℝ) ^ 2 * C ^ 3) ^ (1 / (k : ℝ))) * A ^ 2 *
        T ^ (η / (k : ℝ))) * G ^ 8 * gmS2TracePaperShape k N T W
  have hG0 : 0 ≤ G := by
    exact zero_le_one.trans heathBrownLocalRecurrenceProfile_components.1
  have hP0 : 0 ≤ gmS2TracePaperShape k N T W :=
    gmS2TracePaperShape_nonneg (zero_le_one.trans hT)
  have hB0 : 0 ≤ B := by
    dsimp only [B]
    exact mul_nonneg (by positivity) hP0
  have hEach : ∀ j ∈ Finset.range (Nat.log 2 (Nat.floor T) + 1),
      gmS2ScheduledMain A C k η N T W H j ≤ B := by
    intro j hj
    by_cases hOcc : (heathBrownDifferenceBin W j).Nonempty
    · by_cases hNear : 2 ^ (j + 1) ≤ N
      · simp [gmS2ScheduledMain, hOcc, hNear, hB0]
      · have hStationary := gmS2_occupied_far_stationary hH hHδ
          hSep hSepOne hOcc hNear
        rw [gmS2ScheduledMain, if_pos hOcc, if_neg hNear]
        dsimp only [B, G]
        exact gmS2PhysicalBinMain_le_paperShape hC hT hk hη hN hW hj
          hStationary.1 hNear
    · simp [gmS2ScheduledMain, hOcc, hB0]
  calc
    (∑ j ∈ Finset.range (Nat.log 2 (Nat.floor T) + 1),
        gmS2ScheduledMain A C k η N T W H j) ≤
      ∑ _j ∈ Finset.range (Nat.log 2 (Nat.floor T) + 1), B :=
        Finset.sum_le_sum hEach
    _ = ((Nat.log 2 (Nat.floor T) + 1 : ℕ) : ℝ) * B := by simp
    _ ≤ G * B := by
      gcongr
      dsimp only [G]
      exact heathBrownLocalRecurrenceProfile_components.2.1
    _ = 400 * (1 + A ^ 2 +
          (((k : ℝ) ^ 2 * C ^ 3) ^ (1 / (k : ℝ))) * A ^ 2 *
            T ^ (η / (k : ℝ))) * G ^ 9 *
          gmS2TracePaperShape k N T W := by dsimp only [B]; ring

theorem gmNonzeroTailBinError_eq_reflectionBinError_zero
    (q N M H : ℕ) (U X K L : ℝ) :
    gmNonzeroTailBinError q N M H U K L =
      heathBrownReflectionBinError q N M H U X K L 0 := by
  unfold gmNonzeroTailBinError heathBrownReflectionBinError
  ring

/-- Complete summation of the Mellin and omitted-frequency errors in the
stationary schedule.  Arbitrary-order decay is specialized to the source
smoothing height with two spare powers of `T`. -/
theorem sum_gmS2ScheduledError_le_decay
    {K L η T δ : ℝ} {N H : ℕ} {W : Finset ℝ}
    (hη : 0 < η) (hηOne : η ≤ 1) (hT : 2 ≤ T)
    (hN : 0 < N) (hNT : (N : ℝ) ≤ 2 * T)
    (hH : 0 < H) (hHeight : H = heathBrownSmoothingHeight T η)
    (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hHδ : 4 * (H : ℝ) ≤ δ)
    (hSep : IsSeparated δ W) (hSepOne : IsSeparated 1 W) :
    (∑ j ∈ Finset.range (Nat.log 2 (Nat.floor T) + 1),
        gmS2ScheduledError K L
          (heathBrownReflectionDerivativeOrder 2 η) N W H j) ≤
      ((Nat.log 2 (Nat.floor T) + 1 : ℕ) : ℝ) *
        (8 * (W.card : ℝ) * T *
          ((16 * K + L * (3 : ℝ) ^
              (heathBrownReflectionDerivativeOrder 2 η + 2)) *
            T ^ (-(2 : ℝ))) ^ 2) := by
  let q : ℕ := heathBrownReflectionDerivativeOrder 2 η
  let E : ℝ := 16 * K + L * (3 : ℝ) ^ (q + 2)
  let B : ℝ := 8 * (W.card : ℝ) * T *
    (E * T ^ (-(2 : ℝ))) ^ 2
  have hTOne : 1 ≤ T := by linarith
  have hT0 : 0 ≤ T := zero_le_one.trans hTOne
  have hE0 : 0 ≤ E := by dsimp only [E]; positivity
  have hB0 : 0 ≤ B := by dsimp only [B]; positivity
  have hEach : ∀ j ∈ Finset.range (Nat.log 2 (Nat.floor T) + 1),
      gmS2ScheduledError K L q N W H j ≤ B := by
    intro j hj
    by_cases hOcc : (heathBrownDifferenceBin W j).Nonempty
    · by_cases hNear : 2 ^ (j + 1) ≤ N
      · simp [gmS2ScheduledError, hOcc, hNear, hB0]
      · have hStationary := gmS2_occupied_far_stationary hH hHδ
          hSep hSepOne hOcc hNear
        have hErrHB := heathBrownReflectionBinError_fixed_le_sharp_uniform
          K L 0 q N H j T hK hL (by norm_num) hN hH hj hStationary hNear
        have hErrEq := gmNonzeroTailBinError_eq_reflectionBinError_zero
          q N (heathBrownFixedReflectionLength N H j) H
          (((2 ^ (j + 1) : ℕ) : ℝ)) (((2 ^ j : ℕ) : ℝ)) K L
        have hSmooth := heathBrownSharpUniformReflectionError_smoothing_le
          (A := (2 : ℝ)) (η := η) (T := T) (K := K) (L := L) (D := 0)
          (Q := N) hη hηOne hTOne hN hNT hK hL (by norm_num)
        rw [← hHeight] at hSmooth
        have hErr : gmNonzeroTailBinError q N
            (heathBrownFixedReflectionLength N H j) H
            (((2 ^ (j + 1) : ℕ) : ℝ)) K L ≤ E * T ^ (-(2 : ℝ)) := by
          rw [hErrEq]
          exact hErrHB.trans (by
            simpa [q, E] using hSmooth)
        have hErr0 : 0 ≤ gmNonzeroTailBinError q N
            (heathBrownFixedReflectionLength N H j) H
            (((2 ^ (j + 1) : ℕ) : ℝ)) K L := by
          unfold gmNonzeroTailBinError
          positivity
        have hErrSq := pow_le_pow_left₀ hErr0 hErr 2
        have hCardNat := heathBrownDifferenceBin_card_le W j hSepOne
        have hPowFloor := two_pow_le_floor_of_mem_difference_range hj hStationary.1
        have hPowT : (((2 ^ j : ℕ) : ℝ)) ≤ T := by
          calc
            (((2 ^ j : ℕ) : ℝ)) ≤ (Nat.floor T : ℝ) := by
              exact_mod_cast hPowFloor
            _ ≤ T := Nat.floor_le hT0
        have hCard : ((heathBrownDifferenceBin W j).card : ℝ) ≤
            (W.card : ℝ) * (4 * T) := by
          calc
            ((heathBrownDifferenceBin W j).card : ℝ) ≤
                (W.card : ℝ) *
                  (2 * (((2 ^ (j + 1) : ℕ) : ℝ))) := by
              exact_mod_cast hCardNat
            _ = (W.card : ℝ) * (4 * (((2 ^ j : ℕ) : ℝ))) := by
              rw [pow_succ]
              push_cast
              ring
            _ ≤ (W.card : ℝ) * (4 * T) := by gcongr
        rw [gmS2ScheduledError, if_pos hOcc, if_neg hNear]
        dsimp only [B]
        calc
          2 * ((heathBrownDifferenceBin W j).card : ℝ) *
              (gmNonzeroTailBinError q N
                (heathBrownFixedReflectionLength N H j) H
                (((2 ^ (j + 1) : ℕ) : ℝ)) K L) ^ 2 ≤
            2 * ((W.card : ℝ) * (4 * T)) *
              (E * T ^ (-(2 : ℝ))) ^ 2 := by gcongr
          _ = 8 * (W.card : ℝ) * T *
              (E * T ^ (-(2 : ℝ))) ^ 2 := by ring
    · simp [gmS2ScheduledError, hOcc, hB0]
  calc
    (∑ j ∈ Finset.range (Nat.log 2 (Nat.floor T) + 1),
        gmS2ScheduledError K L q N W H j) ≤
      ∑ _j ∈ Finset.range (Nat.log 2 (Nat.floor T) + 1), B :=
        Finset.sum_le_sum hEach
    _ = ((Nat.log 2 (Nat.floor T) + 1 : ℕ) : ℝ) * B := by simp
    _ = _ := by rfl

set_option maxHeartbeats 1000000 in
/-- Proposition 6.1 at the trace-difference level, with every finite loss
displayed in one tenth-power recurrence profile. -/
theorem gmTraceNonzeroDifferenceMoment_le_profile_paperShape
    (cutoff : GMSmoothCutoff) {k : ℕ} (hk : 0 < k)
    {η : ℝ} (hη : 0 < η) (hηOne : η ≤ 1) :
    ∃ Q₀ T_min : ℝ, 0 < Q₀ ∧ 2 ≤ T_min ∧
      ∀ {N : ℕ} {T δ : ℝ} (W : Finset ℝ),
        T_min ≤ T → 0 < N → (N : ℝ) ≤ 2 * T →
        W.Nonempty →
        let H := heathBrownSmoothingHeight T η
        4 * (H : ℝ) ≤ δ → IsSeparated δ W →
        InBaseInterval T W →
        gmTraceNonzeroDifferenceMoment cutoff N W ≤
          Q₀ * (1 + T ^ (η / (k : ℝ))) *
            heathBrownLocalRecurrenceProfile η T N H ^ 10 *
              gmS2TracePaperShape k N T W := by
  let q : ℕ := heathBrownReflectionDerivativeOrder 2 η
  have hq : 2 ≤ q := heathBrownReflectionDerivativeOrder_two_le 2 η
  obtain ⟨D, A, K, L, C, B, T_ref, hD, hA, hK, hL, hC, hB,
      hT_ref, hSource⟩ :=
    gmTraceNonzeroDifferenceMoment_le_source_schedule
      cutoff q k hq η hk hη
  let J₀ : ℝ := (((k : ℝ) ^ 2 * C ^ 3) ^ (1 / (k : ℝ))) * A ^ 2
  let E : ℝ := 16 * K + L * (3 : ℝ) ^ (q + 2)
  let Q₀ : ℝ := 2 + D ^ 2 + B ^ 2 + 400 * (1 + A ^ 2 + J₀) + 8 * E ^ 2
  let T_min : ℝ := max 2 T_ref
  have hQ₀ : 0 < Q₀ := by dsimp only [Q₀]; positivity
  have hTmin : 2 ≤ T_min := le_max_left _ _
  refine ⟨Q₀, T_min, hQ₀, hTmin, ?_⟩
  intro N T δ W hT hN hNT hW
  dsimp only
  intro hHδ hSep hBase
  let H : ℕ := heathBrownSmoothingHeight T η
  let G : ℝ := heathBrownLocalRecurrenceProfile η T N H
  let P : ℝ := gmS2TracePaperShape k N T W
  have hTTwo : 2 ≤ T := hTmin.trans hT
  have hTOne : 1 ≤ T := by linarith
  have hTref : T_ref ≤ T := (le_max_right _ _).trans hT
  have hH : 0 < H := by
    dsimp only [H]
    exact heathBrownSmoothingHeight_pos T η
  have hHeight : H = heathBrownSmoothingHeight T η := rfl
  have hδOne : 1 ≤ δ := by
    have hHOne : (1 : ℝ) ≤ H := by exact_mod_cast hH
    linarith
  have hSepOne : IsSeparated 1 W := by
    intro x hx y hy hxy
    exact hδOne.trans (hSep x hx y hy hxy)
  have hRaw := hSource W hTref hN hH hHδ hSep hBase hW
  have hMain := sum_gmS2ScheduledMain_le_paperShape
    (A := A) (C := C) (η := η) (T := T) (δ := δ)
    (k := k) (N := N) (H := H) (W := W) hC.le hTOne hk hη.le
    hN hH hW hHδ hSep hSepOne
  have hError := sum_gmS2ScheduledError_le_decay
    (K := K) (L := L) (η := η) (T := T) (δ := δ)
    (N := N) (H := H) (W := W) hη hηOne hTTwo hN hNT hH hHeight
    hK.le hL.le hHδ hSep hSepOne
  have hScheduleEq :
      (∑ j ∈ Finset.range (Nat.log 2 (Nat.floor T) + 1),
          gmS2SourceScheduledBinBound A K L C q k η N T W H j) =
        (∑ j ∈ Finset.range (Nat.log 2 (Nat.floor T) + 1),
          gmS2ScheduledMain A C k η N T W H j) +
        ∑ j ∈ Finset.range (Nat.log 2 (Nat.floor T) + 1),
          gmS2ScheduledError K L q N W H j := by
    simp_rw [gmS2SourceScheduledBinBound_eq_main_add_error]
    exact Finset.sum_add_distrib
  rw [hScheduleEq] at hRaw
  have hGOne : 1 ≤ G := by
    dsimp only [G]
    exact heathBrownLocalRecurrenceProfile_components.1
  have hG0 : 0 ≤ G := zero_le_one.trans hGOne
  have hP0 : 0 ≤ P := by
    dsimp only [P]
    exact gmS2TracePaperShape_nonneg (zero_le_one.trans hTOne)
  have hRone : (1 : ℝ) ≤ W.card := by exact_mod_cast hW.card_pos
  have hNone : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hRleFirst : (W.card : ℝ) ≤ (N : ℝ) * (W.card : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((W.card : ℝ) - 1)]
  have hFirstP : (N : ℝ) * (W.card : ℝ) ^ 2 ≤ P := by
    dsimp only [P, gmS2TracePaperShape]
    have hTwo : 0 ≤ T * (W.card : ℝ) ^ (2 - 1 / (k : ℝ)) := by positivity
    have hThree : 0 ≤ (N : ℝ) *
        (W.card : ℝ) ^ (2 - 3 / (4 * (k : ℝ))) *
          T ^ (1 / (2 * (k : ℝ))) := by positivity
    linarith
  have hRleP : (W.card : ℝ) ≤ P := hRleFirst.trans hFirstP
  have hDiagTerm : (W.card : ℝ) *
      (B / (N : ℝ) ^ (q - 1)) ^ 2 ≤ B ^ 2 * P := by
    have hDenOne : (1 : ℝ) ≤ (N : ℝ) ^ (q - 1) :=
      one_le_pow₀ hNone
    have hDiv : B / (N : ℝ) ^ (q - 1) ≤ B :=
      div_le_self hB.le hDenOne
    have hDiv0 : 0 ≤ B / (N : ℝ) ^ (q - 1) := by positivity
    calc
      (W.card : ℝ) * (B / (N : ℝ) ^ (q - 1)) ^ 2 ≤
          (W.card : ℝ) * B ^ 2 := by gcongr
      _ ≤ P * B ^ 2 := mul_le_mul_of_nonneg_right hRleP (sq_nonneg B)
      _ = B ^ 2 * P := by ring
  have hNearTerm : D ^ 2 * (N : ℝ) * (W.card : ℝ) ^ 2 ≤ D ^ 2 * P := by
    calc
      D ^ 2 * (N : ℝ) * (W.card : ℝ) ^ 2 =
          D ^ 2 * ((N : ℝ) * (W.card : ℝ) ^ 2) := by ring
      _ ≤ D ^ 2 * P := mul_le_mul_of_nonneg_left hFirstP (sq_nonneg D)
  have hCountG : ((Nat.log 2 (Nat.floor T) + 1 : ℕ) : ℝ) ≤ G := by
    dsimp only [G]
    exact heathBrownLocalRecurrenceProfile_components.2.1
  have hTPos : 0 < T := by linarith
  have hDecay : T * (T ^ (-(2 : ℝ))) ^ 2 ≤ 1 := by
    have heq : T * (T ^ (-(2 : ℝ))) ^ 2 = (T ^ 3)⁻¹ := by
      rw [Real.rpow_neg hTPos.le, Real.rpow_two]
      field_simp [hTPos.ne']
    rw [heq]
    exact (inv_le_one₀ (pow_pos hTPos 3)).2 (one_le_pow₀ hTOne)
  have hError' :
      (∑ j ∈ Finset.range (Nat.log 2 (Nat.floor T) + 1),
          gmS2ScheduledError K L q N W H j) ≤ 8 * E ^ 2 * G * P := by
    have hCore :
        8 * (W.card : ℝ) * E ^ 2 *
            (T * (T ^ (-(2 : ℝ))) ^ 2) ≤ 8 * P * E ^ 2 := by
      have hEightE : 0 ≤ 8 * E ^ 2 := by positivity
      calc
        8 * (W.card : ℝ) * E ^ 2 *
              (T * (T ^ (-(2 : ℝ))) ^ 2) ≤
            8 * (W.card : ℝ) * E ^ 2 :=
              mul_le_of_le_one_right (by positivity) hDecay
        _ ≤ 8 * P * E ^ 2 := by
          have hEightR : 8 * (W.card : ℝ) ≤ 8 * P :=
            mul_le_mul_of_nonneg_left hRleP (by norm_num)
          exact mul_le_mul_of_nonneg_right hEightR (sq_nonneg E)
    calc
      _ ≤ ((Nat.log 2 (Nat.floor T) + 1 : ℕ) : ℝ) *
          (8 * (W.card : ℝ) * T *
            (E * T ^ (-(2 : ℝ))) ^ 2) := by
              simpa only [q, E] using hError
      _ = ((Nat.log 2 (Nat.floor T) + 1 : ℕ) : ℝ) *
          (8 * (W.card : ℝ) * E ^ 2 *
            (T * (T ^ (-(2 : ℝ))) ^ 2)) := by ring
      _ ≤ G * (8 * P * E ^ 2) := by
        exact mul_le_mul hCountG hCore (by positivity) (by positivity)
      _ = 8 * E ^ 2 * G * P := by ring
  have hG9le10 : G ^ 9 ≤ G ^ 10 := pow_le_pow_right₀ hGOne (by omega)
  have hMain' :
      (∑ j ∈ Finset.range (Nat.log 2 (Nat.floor T) + 1),
          gmS2ScheduledMain A C k η N T W H j) ≤
        400 * (1 + A ^ 2 + J₀ * T ^ (η / (k : ℝ))) * G ^ 10 * P := by
    calc
      _ ≤ 400 * (1 + A ^ 2 + J₀ * T ^ (η / (k : ℝ))) *
          G ^ 9 * P := by simpa only [J₀, G, P, mul_assoc] using hMain
      _ ≤ 400 * (1 + A ^ 2 + J₀ * T ^ (η / (k : ℝ))) *
          G ^ 10 * P := by gcongr
  have hTpow0 : 0 ≤ T ^ (η / (k : ℝ)) := by positivity
  have hG10One : 1 ≤ G ^ 10 := one_le_pow₀ hGOne
  have hJ₀0 : 0 ≤ J₀ := by
    dsimp only [J₀]
    positivity
  have hOneTpow : 1 ≤ 1 + T ^ (η / (k : ℝ)) := by linarith
  have hGle10 : G ≤ G ^ 10 := by
    calc
      G = G ^ 1 := by simp
      _ ≤ G ^ 10 := pow_le_pow_right₀ hGOne (by omega)
  have hScaleOne : 1 ≤ (1 + T ^ (η / (k : ℝ))) * G ^ 10 := by
    simpa only [one_mul] using
      mul_le_mul hOneTpow hG10One (by norm_num) (by linarith)
  have hPScale : P ≤ (1 + T ^ (η / (k : ℝ))) * G ^ 10 * P := by
    calc
      P = 1 * P := by ring
      _ ≤ ((1 + T ^ (η / (k : ℝ))) * G ^ 10) * P :=
        mul_le_mul_of_nonneg_right hScaleOne hP0
  have hGPScale : G * P ≤ (1 + T ^ (η / (k : ℝ))) * G ^ 10 * P := by
    have hGScale : G ≤ (1 + T ^ (η / (k : ℝ))) * G ^ 10 := by
      calc
        G ≤ G ^ 10 := hGle10
        _ ≤ (1 + T ^ (η / (k : ℝ))) * G ^ 10 := by
          nlinarith [mul_nonneg hTpow0 (pow_nonneg hG0 10)]
    exact mul_le_mul_of_nonneg_right hGScale hP0
  have hCoeff :
      1 + A ^ 2 + J₀ * T ^ (η / (k : ℝ)) ≤
        (1 + A ^ 2 + J₀) * (1 + T ^ (η / (k : ℝ))) := by
    rw [← sub_nonneg]
    have hEq :
        (1 + A ^ 2 + J₀) * (1 + T ^ (η / (k : ℝ))) -
            (1 + A ^ 2 + J₀ * T ^ (η / (k : ℝ))) =
          J₀ + (1 + A ^ 2) * T ^ (η / (k : ℝ)) := by ring
    rw [hEq]
    exact add_nonneg hJ₀0 (mul_nonneg (by positivity) hTpow0)
  have hCommon0 :
      0 ≤ (1 + T ^ (η / (k : ℝ))) * G ^ 10 * P := by positivity
  have hDTerm :
      D ^ 2 * P ≤ D ^ 2 *
        ((1 + T ^ (η / (k : ℝ))) * G ^ 10 * P) :=
    mul_le_mul_of_nonneg_left hPScale (sq_nonneg D)
  have hBTerm :
      B ^ 2 * P ≤ B ^ 2 *
        ((1 + T ^ (η / (k : ℝ))) * G ^ 10 * P) :=
    mul_le_mul_of_nonneg_left hPScale (sq_nonneg B)
  have hMainTerm :
      400 * (1 + A ^ 2 + J₀ * T ^ (η / (k : ℝ))) * G ^ 10 * P ≤
        (400 * (1 + A ^ 2 + J₀)) *
          ((1 + T ^ (η / (k : ℝ))) * G ^ 10 * P) := by
    have h400Coeff :
        400 * (1 + A ^ 2 + J₀ * T ^ (η / (k : ℝ))) ≤
          400 * ((1 + A ^ 2 + J₀) * (1 + T ^ (η / (k : ℝ)))) :=
      mul_le_mul_of_nonneg_left hCoeff (by norm_num)
    calc
      400 * (1 + A ^ 2 + J₀ * T ^ (η / (k : ℝ))) * G ^ 10 * P ≤
          400 * ((1 + A ^ 2 + J₀) * (1 + T ^ (η / (k : ℝ)))) *
            G ^ 10 * P := by gcongr
      _ = (400 * (1 + A ^ 2 + J₀)) *
          ((1 + T ^ (η / (k : ℝ))) * G ^ 10 * P) := by ring
  have hErrorTerm :
      8 * E ^ 2 * G * P ≤ (8 * E ^ 2) *
        ((1 + T ^ (η / (k : ℝ))) * G ^ 10 * P) := by
    calc
      8 * E ^ 2 * G * P = (8 * E ^ 2) * (G * P) := by ring
      _ ≤ (8 * E ^ 2) *
          ((1 + T ^ (η / (k : ℝ))) * G ^ 10 * P) :=
        mul_le_mul_of_nonneg_left hGPScale (by positivity)
  calc
    gmTraceNonzeroDifferenceMoment cutoff N W ≤
        D ^ 2 * P + B ^ 2 * P +
          (400 * (1 + A ^ 2 + J₀ * T ^ (η / (k : ℝ))) * G ^ 10 * P +
            8 * E ^ 2 * G * P) := by
      exact hRaw.trans (add_le_add (add_le_add hNearTerm hDiagTerm)
        (add_le_add hMain' hError'))
    _ ≤ Q₀ * (1 + T ^ (η / (k : ℝ))) * G ^ 10 * P := by
      dsimp only [Q₀]
      calc
        D ^ 2 * P + B ^ 2 * P +
              (400 * (1 + A ^ 2 + J₀ * T ^ (η / (k : ℝ))) * G ^ 10 * P +
                8 * E ^ 2 * G * P) ≤
            D ^ 2 * ((1 + T ^ (η / (k : ℝ))) * G ^ 10 * P) +
              B ^ 2 * ((1 + T ^ (η / (k : ℝ))) * G ^ 10 * P) +
              ((400 * (1 + A ^ 2 + J₀)) *
                  ((1 + T ^ (η / (k : ℝ))) * G ^ 10 * P) +
                (8 * E ^ 2) *
                  ((1 + T ^ (η / (k : ℝ))) * G ^ 10 * P)) :=
          add_le_add (add_le_add hDTerm hBTerm) (add_le_add hMainTerm hErrorTerm)
        _ = (D ^ 2 + B ^ 2 + 400 * (1 + A ^ 2 + J₀) + 8 * E ^ 2) *
              ((1 + T ^ (η / (k : ℝ))) * G ^ 10 * P) := by ring
        _ ≤ (2 + D ^ 2 + B ^ 2 + 400 * (1 + A ^ 2 + J₀) + 8 * E ^ 2) *
              ((1 + T ^ (η / (k : ℝ))) * G ^ 10 * P) := by
          exact mul_le_mul_of_nonneg_right (by linarith) hCommon0
        _ = (2 + D ^ 2 + B ^ 2 + 400 * (1 + A ^ 2 + J₀) + 8 * E ^ 2) *
              (1 + T ^ (η / (k : ℝ))) * G ^ 10 * P := by ring

/-- A source `T^ε`-separated set has enough room for the integral
`T^η` smoothing height as soon as `η < ε`.  This is the exact spacing
bridge used when Proposition 6.1 consumes the trace estimate above. -/
theorem exists_gmS2SmoothingThreshold
    {ε η : ℝ} (hη : 0 ≤ η) (hηε : η < ε) :
    ∃ T₀ : ℝ, 2 ≤ T₀ ∧ ∀ {T : ℝ}, T₀ ≤ T →
      4 * (heathBrownSmoothingHeight T η : ℝ) ≤ T ^ ε := by
  have hGap : 0 < ε - η := sub_pos.mpr hηε
  have hTend := tendsto_rpow_atTop hGap
  have hEventually : ∀ᶠ T : ℝ in atTop, 8 ≤ T ^ (ε - η) :=
    hTend.eventually (eventually_ge_atTop 8)
  rw [eventually_atTop] at hEventually
  obtain ⟨Tgap, hTgap⟩ := hEventually
  let T₀ : ℝ := max 2 Tgap
  refine ⟨T₀, le_max_left _ _, ?_⟩
  intro T hT
  have hTTwo : 2 ≤ T := (le_max_left _ _).trans hT
  have hTOne : 1 ≤ T := by linarith
  have hTPos : 0 < T := by linarith
  have hGapAt : 8 ≤ T ^ (ε - η) := hTgap T ((le_max_right _ _).trans hT)
  have hHeight := heathBrownSmoothingHeight_le_two_rpow hTOne hη
  have hFactor : 8 * T ^ η ≤ T ^ ε := by
    calc
      8 * T ^ η ≤ T ^ (ε - η) * T ^ η :=
        mul_le_mul_of_nonneg_right hGapAt (Real.rpow_nonneg hTPos.le _)
      _ = T ^ ε := by
        rw [← Real.rpow_add hTPos]
        congr 1
        ring
  calc
    4 * (heathBrownSmoothingHeight T η : ℝ) ≤ 4 * (2 * T ^ η) := by gcongr
    _ = 8 * T ^ η := by ring
    _ ≤ T ^ ε := hFactor

set_option maxHeartbeats 1000000 in
/-- Epsilon-absorbed trace form of Guth--Maynard Proposition 6.1.  The
separation exponent is the caller's `ε`; internally a strictly smaller
`η = min(ε/44,1/2)` pays for smoothing, dyadic recurrence, Mellin tails,
and the finite powering loss. -/
theorem gmTraceNonzeroDifferenceMoment_estimate
    (cutoff : GMSmoothCutoff) {k : ℕ} (hk : 0 < k)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C T₀ : ℝ, 0 < C ∧ 2 ≤ T₀ ∧
      ∀ {N : ℕ} {T : ℝ} (W : Finset ℝ),
        0 < N → T₀ ≤ T → (N : ℝ) ≤ T → W.Nonempty →
        IsSeparated (T ^ ε) W → InBaseInterval T W →
        gmTraceNonzeroDifferenceMoment cutoff N W ≤
          C * T ^ ε * gmS2TracePaperShape k N T W := by
  let η : ℝ := min (ε / 44) (1 / 2)
  have hη : 0 < η := by
    dsimp only [η]
    exact lt_min (div_pos hε (by norm_num)) (by norm_num)
  have hηOne : η ≤ 1 := by
    exact (min_le_right (ε / 44) (1 / 2)).trans (by norm_num)
  have hηLe : η ≤ ε / 44 := min_le_left _ _
  have hηε : η < ε := by
    have hDivLt : ε / 44 < ε := by nlinarith
    exact hηLe.trans_lt hDivLt
  have hBudget : 21 * η ≤ ε := by nlinarith
  obtain ⟨Q, Ttrace, hQ, hTtrace, hTrace⟩ :=
    gmTraceNonzeroDifferenceMoment_le_profile_paperShape
      cutoff hk hη hηOne
  obtain ⟨Cp, hCp, Tprofile, hTprofile, hProfile⟩ :=
    eventually_heathBrownLocalRecurrenceProfile_pow_ten_le_rpow
      η hη hηOne
  obtain ⟨Tsmooth, hTsmooth, hSmooth⟩ :=
    exists_gmS2SmoothingThreshold hη.le hηε
  let C : ℝ := 2 * Q * Cp
  let T₀ : ℝ := max Ttrace (max Tprofile Tsmooth)
  have hC : 0 < C := by dsimp only [C]; positivity
  have hT₀ : 2 ≤ T₀ := by
    exact hTtrace.trans (le_max_left _ _)
  refine ⟨C, T₀, hC, hT₀, ?_⟩
  intro N T W hN hT hNT hW hSep hBase
  have hTraceT : Ttrace ≤ T := (le_max_left _ _).trans hT
  have hProfileT : Tprofile ≤ T :=
    (le_max_left Tprofile Tsmooth).trans ((le_max_right _ _).trans hT)
  have hSmoothT : Tsmooth ≤ T :=
    (le_max_right Tprofile Tsmooth).trans ((le_max_right _ _).trans hT)
  have hTTwo : 2 ≤ T := hT₀.trans hT
  have hTOne : 1 ≤ T := by linarith
  have hTPos : 0 < T := by linarith
  let H : ℕ := heathBrownSmoothingHeight T η
  have hH : 0 < H := heathBrownSmoothingHeight_pos T η
  have hNTTwo : (N : ℝ) ≤ 2 * T := by linarith
  have hSpacing : 4 * (H : ℝ) ≤ T ^ ε := by
    dsimp only [H]
    exact hSmooth hSmoothT
  have hRaw := hTrace W hTraceT hN hNTTwo hW hSpacing hSep hBase
  have hProf : heathBrownLocalRecurrenceProfile η T N H ^ 10 ≤
      Cp * T ^ (20 * η) := by
    exact hProfile T N H hProfileT hN rfl
  have hkOneNat : 1 ≤ k := hk
  have hkOne : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hkOneNat
  have hExp : η / (k : ℝ) ≤ η := div_le_self hη.le hkOne
  have hPowK : T ^ (η / (k : ℝ)) ≤ T ^ η :=
    Real.rpow_le_rpow_of_exponent_le hTOne hExp
  have hPowOne : 1 ≤ T ^ η := Real.one_le_rpow hTOne hη.le
  have hOneAdd : 1 + T ^ (η / (k : ℝ)) ≤ 2 * T ^ η := by linarith
  have hPowBudget : T ^ (21 * η) ≤ T ^ ε :=
    Real.rpow_le_rpow_of_exponent_le hTOne hBudget
  have hPowMul : T ^ η * T ^ (20 * η) = T ^ (21 * η) := by
    rw [← Real.rpow_add hTPos]
    congr 1
    ring
  have hP0 : 0 ≤ gmS2TracePaperShape k N T W :=
    gmS2TracePaperShape_nonneg hTPos.le
  calc
    gmTraceNonzeroDifferenceMoment cutoff N W ≤
        Q * (1 + T ^ (η / (k : ℝ))) *
          heathBrownLocalRecurrenceProfile η T N H ^ 10 *
            gmS2TracePaperShape k N T W := by
      simpa only [H] using hRaw
    _ ≤ Q * (2 * T ^ η) * (Cp * T ^ (20 * η)) *
          gmS2TracePaperShape k N T W := by gcongr
    _ = C * T ^ (21 * η) * gmS2TracePaperShape k N T W := by
      dsimp only [C]
      rw [← hPowMul]
      ring
    _ ≤ C * T ^ ε * gmS2TracePaperShape k N T W := by gcongr

/-- The exact three-term right-hand side of Guth--Maynard Proposition 6.1,
after reinserting the outer zero mode. -/
noncomputable def gmS2PaperShape
    (k N : ℕ) (T : ℝ) (W : Finset ℝ) : ℝ :=
  (N : ℝ) * gmS2TracePaperShape k N T W

theorem gmS2PaperShape_eq
    (k N : ℕ) (T : ℝ) (W : Finset ℝ) :
    gmS2PaperShape k N T W =
      (N : ℝ) ^ 2 * (W.card : ℝ) ^ 2 +
        T * (N : ℝ) * (W.card : ℝ) ^ (2 - 1 / (k : ℝ)) +
        (N : ℝ) ^ 2 * (W.card : ℝ) ^ (2 - 3 / (4 * (k : ℝ))) *
          T ^ (1 / (2 * (k : ℝ))) := by
  unfold gmS2PaperShape gmS2TracePaperShape
  ring

theorem gmS2PaperShape_nonneg
    {k N : ℕ} {T : ℝ} {W : Finset ℝ} (hT : 0 ≤ T) :
    0 ≤ gmS2PaperShape k N T W := by
  unfold gmS2PaperShape
  exact mul_nonneg (Nat.cast_nonneg N) (gmS2TracePaperShape_nonneg hT)

set_option maxHeartbeats 1000000 in
/-- Guth--Maynard Proposition 6.1 in its source epsilon-separated form.
This theorem consumes the literal cubic `S₂`, all three cyclic summands,
the zero-mode factor, the complete nonzero integer-frequency moment, and
the off-diagonal `v ≠ t` decay. -/
theorem gmCubicS2_estimate
    (cutoff : GMSmoothCutoff) {k : ℕ} (hk : 0 < k)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C T₀ : ℝ, 0 < C ∧ 2 ≤ T₀ ∧
      ∀ {N : ℕ} {T : ℝ} (W : Finset ℝ),
        0 < N → T₀ ≤ T → (N : ℝ) ≤ T →
        IsSeparated (T ^ ε) W → InBaseInterval T W →
        ‖gmCubicS2 cutoff N W‖ ≤
          C * T ^ ε * gmS2PaperShape k N T W := by
  obtain ⟨Ct, Tt, hCt, hTt, hTrace⟩ :=
    gmTraceNonzeroDifferenceMoment_estimate cutoff hk ε hε
  obtain ⟨B, hB, hDiag⟩ := gmCubicS2FirstDiagonal_le_zeroModeConstant cutoff
  obtain ⟨K, hK, hOff⟩ := gmCubicS2FirstOffDiagonal_power_decay cutoff ε hε
  let C : ℝ := 3 * (B * Ct + K + 1)
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, Tt, hC, hTt, ?_⟩
  intro N T W hN hT hNT hSep hBase
  have hTTwo : 2 ≤ T := hTt.trans hT
  have hTOne : 1 ≤ T := by linarith
  have hTPos : 0 < T := by linarith
  by_cases hW : W.Nonempty
  · have hTraceAt := hTrace W hN hT hNT hW hSep hBase
    have hTrace0 : 0 ≤ gmTraceNonzeroDifferenceMoment cutoff N W := by
      unfold gmTraceNonzeroDifferenceMoment
      positivity
    have hShape0 : 0 ≤ gmS2PaperShape k N T W :=
      gmS2PaperShape_nonneg hTPos.le
    have hTpowOne : 1 ≤ T ^ ε := Real.one_le_rpow hTOne hε.le
    have hNone : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hRone : (1 : ℝ) ≤ W.card := by exact_mod_cast hW.card_pos
    have hRsq : (1 : ℝ) ≤ (W.card : ℝ) ^ 2 := by
      rw [pow_two]
      simpa only [one_mul] using
        mul_le_mul hRone hRone (by norm_num) (by linarith)
    have hTraceShapeOne : 1 ≤ gmS2TracePaperShape k N T W := by
      have hFirst : 1 ≤ (N : ℝ) * (W.card : ℝ) ^ 2 := by
        simpa only [one_mul] using
          mul_le_mul hNone hRsq (by norm_num) (by linarith)
      unfold gmS2TracePaperShape
      have hSecond : 0 ≤ T * (W.card : ℝ) ^ (2 - 1 / (k : ℝ)) := by positivity
      have hThird : 0 ≤ (N : ℝ) *
          (W.card : ℝ) ^ (2 - 3 / (4 * (k : ℝ))) *
            T ^ (1 / (2 * (k : ℝ))) := by positivity
      linarith
    have hShapeOne : 1 ≤ gmS2PaperShape k N T W := by
      unfold gmS2PaperShape
      simpa only [one_mul] using
        mul_le_mul hNone hTraceShapeOne (by norm_num) (by linarith)
    have hScaleOne : 1 ≤ T ^ ε * gmS2PaperShape k N T W := by
      simpa only [one_mul] using
        mul_le_mul hTpowOne hShapeOne (by norm_num) (by linarith)
    have hDiagAt : ‖gmCubicS2FirstDiagonal cutoff N W‖ ≤
        (B * Ct) * (T ^ ε * gmS2PaperShape k N T W) := by
      calc
        ‖gmCubicS2FirstDiagonal cutoff N W‖ ≤
            B * (N : ℝ) * gmTraceNonzeroDifferenceMoment cutoff N W :=
          hDiag N W
        _ ≤ B * (N : ℝ) *
            (Ct * T ^ ε * gmS2TracePaperShape k N T W) := by gcongr
        _ = (B * Ct) * (T ^ ε * gmS2PaperShape k N T W) := by
          unfold gmS2PaperShape
          ring
    have hOffRaw := hOff W hN hTOne hNT hSep hBase
    have hOffAt : ‖gmCubicS2FirstOffDiagonal cutoff N W‖ ≤
        K * (T ^ ε * gmS2PaperShape k N T W) := by
      calc
        ‖gmCubicS2FirstOffDiagonal cutoff N W‖ ≤ K / T ^ 10 := hOffRaw
        _ ≤ K := div_le_self hK.le (one_le_pow₀ hTOne)
        _ ≤ K * (T ^ ε * gmS2PaperShape k N T W) := by
          simpa only [mul_one] using
            mul_le_mul_of_nonneg_left hScaleOne hK.le
    have hFirst : ‖gmCubicS2First cutoff N W‖ ≤
        (B * Ct + K) * (T ^ ε * gmS2PaperShape k N T W) := by
      rw [gmCubicS2First_eq_diagonal_add_offDiagonal]
      calc
        ‖gmCubicS2FirstDiagonal cutoff N W +
            gmCubicS2FirstOffDiagonal cutoff N W‖ ≤
          ‖gmCubicS2FirstDiagonal cutoff N W‖ +
            ‖gmCubicS2FirstOffDiagonal cutoff N W‖ := norm_add_le _ _
        _ ≤ (B * Ct) * (T ^ ε * gmS2PaperShape k N T W) +
            K * (T ^ ε * gmS2PaperShape k N T W) :=
          add_le_add hDiagAt hOffAt
        _ = (B * Ct + K) *
            (T ^ ε * gmS2PaperShape k N T W) := by ring
    rw [gmCubicS2_eq_three_mul_first]
    calc
      ‖(3 : ℂ) * gmCubicS2First cutoff N W‖ =
          3 * ‖gmCubicS2First cutoff N W‖ := by norm_num [norm_mul]
      _ ≤ 3 * ((B * Ct + K) *
          (T ^ ε * gmS2PaperShape k N T W)) := by gcongr
      _ ≤ C * T ^ ε * gmS2PaperShape k N T W := by
        dsimp only [C]
        have hScale0 : 0 ≤ T ^ ε * gmS2PaperShape k N T W := by positivity
        nlinarith [mul_nonneg (by positivity : 0 ≤ (3 : ℝ)) hScale0]
  · have hEmpty : W = ∅ := Finset.not_nonempty_iff_eq_empty.mp hW
    subst W
    have hShape0 : 0 ≤ gmS2PaperShape k N T ∅ :=
      gmS2PaperShape_nonneg hTPos.le
    have hRhs0 : 0 ≤ C * T ^ ε * gmS2PaperShape k N T ∅ := by
      positivity
    simpa [gmCubicS2] using hRhs0

end RiemannZeta.GuthMaynard
