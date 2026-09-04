import GafniTao.WooleyPolynomialRefinement

/-!
# Initial conditioning for Wooley polynomial systems

This is the phase-independent Section 6 argument instantiated with the exact
polynomial sums.  It supplies the form needed by the degree induction in
Section 7, while the monomial specialization remains available as a regression
theorem.
-/

open Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

def wooleyPolynomialInitialDiagonal {Q k : ℕ}
    (phi : WooleyPolynomialSystem k) (p B nu : ℕ)
    [NeZero p] [NeZero (p ^ B)]
    (gamma : Fin Q → ℂ) (alpha : Fin k → ZMod (p ^ B)) : ℝ :=
  (wooleyWeightedMassSq gamma)⁻¹ *
    ∑ xi : ZMod (p ^ nu),
      wooleyWeightedResidueMassSq gamma xi *
        ‖wooleyPolynomialNormalizedResidueGridSum
          phi (p ^ B) gamma alpha xi‖ ^ 2

def wooleyPolynomialInitialOffDiagonal {Q k : ℕ}
    (phi : WooleyPolynomialSystem k) (p B nu : ℕ)
    [NeZero p] [NeZero (p ^ B)]
    (gamma : Fin Q → ℂ) (alpha : Fin k → ZMod (p ^ B)) : ℝ :=
  (wooleyWeightedMassSq gamma)⁻¹ *
    ∑ xi : ZMod (p ^ nu),
      ∑ eta : ZMod (p ^ nu) with wooleyResiduesSeparated nu xi eta,
        Real.sqrt (wooleyWeightedResidueMassSq gamma xi) *
          Real.sqrt (wooleyWeightedResidueMassSq gamma eta) *
          ‖wooleyPolynomialNormalizedResidueGridSum
            phi (p ^ B) gamma alpha xi‖ *
          ‖wooleyPolynomialNormalizedResidueGridSum
            phi (p ^ B) gamma alpha eta‖

def wooleyPolynomialInitialMixedForward {Q k : ℕ}
    (phi : WooleyPolynomialSystem k) (p B nu s : ℕ)
    [NeZero p] [NeZero (p ^ B)]
    (gamma : Fin Q → ℂ) (alpha : Fin k → ZMod (p ^ B)) : ℝ :=
  ∑ xi : ZMod (p ^ nu),
    ∑ eta : ZMod (p ^ nu) with wooleyResiduesSeparated nu xi eta,
      wooleyWeightedResidueMassSq gamma xi *
        wooleyWeightedResidueMassSq gamma eta *
        ‖wooleyPolynomialNormalizedResidueGridSum
          phi (p ^ B) gamma alpha xi‖ ^ 2 *
        ‖wooleyPolynomialNormalizedResidueGridSum
          phi (p ^ B) gamma alpha eta‖ ^ (2 * (s - 1))

theorem wooleyPolynomialInitialDiagonal_nonneg {Q k : ℕ}
    (phi : WooleyPolynomialSystem k) (p B nu : ℕ)
    [NeZero p] [NeZero (p ^ B)]
    (gamma : Fin Q → ℂ) (alpha : Fin k → ZMod (p ^ B)) :
    0 ≤ wooleyPolynomialInitialDiagonal phi p B nu gamma alpha := by
  unfold wooleyPolynomialInitialDiagonal
  exact mul_nonneg
    (inv_nonneg.mpr (wooleyWeightedMassSq_nonneg gamma))
    (Finset.sum_nonneg fun xi hxi =>
      mul_nonneg (wooleyWeightedResidueMassSq_nonneg gamma xi)
        (sq_nonneg _))

theorem wooleyPolynomialInitialOffDiagonal_nonneg {Q k : ℕ}
    (phi : WooleyPolynomialSystem k) (p B nu : ℕ)
    [NeZero p] [NeZero (p ^ B)]
    (gamma : Fin Q → ℂ) (alpha : Fin k → ZMod (p ^ B)) :
    0 ≤ wooleyPolynomialInitialOffDiagonal phi p B nu gamma alpha := by
  unfold wooleyPolynomialInitialOffDiagonal
  exact mul_nonneg
    (inv_nonneg.mpr (wooleyWeightedMassSq_nonneg gamma))
    (Finset.sum_nonneg fun xi hxi =>
      Finset.sum_nonneg fun eta heta => by positivity)

theorem wooleyPolynomialInitialMixedForward_nonneg {Q k : ℕ}
    (phi : WooleyPolynomialSystem k) (p B nu s : ℕ)
    [NeZero p] [NeZero (p ^ B)]
    (gamma : Fin Q → ℂ) (alpha : Fin k → ZMod (p ^ B)) :
    0 ≤ wooleyPolynomialInitialMixedForward
      phi p B nu s gamma alpha := by
  unfold wooleyPolynomialInitialMixedForward
  exact Finset.sum_nonneg fun xi hxi =>
    Finset.sum_nonneg fun eta heta =>
      mul_nonneg
        (mul_nonneg
          (mul_nonneg (wooleyWeightedResidueMassSq_nonneg gamma xi)
            (wooleyWeightedResidueMassSq_nonneg gamma eta))
          (sq_nonneg _))
        (pow_nonneg (norm_nonneg _) _)

theorem wooleyPolynomialInitialMixedReverse_eq_forward {Q k : ℕ}
    (phi : WooleyPolynomialSystem k) (p B nu s : ℕ)
    [NeZero p] [NeZero (p ^ B)]
    (gamma : Fin Q → ℂ) (alpha : Fin k → ZMod (p ^ B)) :
    (∑ xi : ZMod (p ^ nu),
      ∑ eta : ZMod (p ^ nu) with wooleyResiduesSeparated nu xi eta,
        wooleyWeightedResidueMassSq gamma xi *
          wooleyWeightedResidueMassSq gamma eta *
          ‖wooleyPolynomialNormalizedResidueGridSum
            phi (p ^ B) gamma alpha eta‖ ^ 2 *
          ‖wooleyPolynomialNormalizedResidueGridSum
            phi (p ^ B) gamma alpha xi‖ ^ (2 * (s - 1))) =
      wooleyPolynomialInitialMixedForward phi p B nu s gamma alpha := by
  unfold wooleyPolynomialInitialMixedForward
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro xi hxi
  apply Finset.sum_congr rfl
  intro eta heta
  have hsep : wooleyResiduesSeparated nu eta xi ↔
      wooleyResiduesSeparated nu xi eta := by
    rw [wooleyResiduesSeparated_same_iff_ne,
      wooleyResiduesSeparated_same_iff_ne]
    exact ne_comm
  by_cases h : wooleyResiduesSeparated nu eta xi
  · have h' := hsep.mp h
    rw [if_pos h, if_pos h']
    ring
  · have h' : ¬ wooleyResiduesSeparated nu xi eta :=
      fun hxiEta => h (hsep.mpr hxiEta)
    rw [if_neg h, if_neg h']

/-- Polynomial-system equation (6.6). -/
theorem wooleyPolynomial_equation_6_6 {Q k : ℕ}
    (phi : WooleyPolynomialSystem k) (p B nu : ℕ)
    [NeZero p] [NeZero (p ^ B)]
    (gamma : Fin Q → ℂ) (alpha : Fin k → ZMod (p ^ B)) :
    ‖wooleyPolynomialNormalizedGridSum phi (p ^ B) gamma alpha‖ ^ 2 ≤
      wooleyPolynomialInitialDiagonal phi p B nu gamma alpha +
        wooleyPolynomialInitialOffDiagonal phi p B nu gamma alpha := by
  by_cases hmass : wooleyWeightedMassSq gamma = 0
  · simp [wooleyPolynomialNormalizedGridSum, hmass,
      wooleyPolynomialInitialDiagonal,
      wooleyPolynomialInitialOffDiagonal]
  · let M : ℝ := wooleyWeightedMassSq gamma
    let a : ZMod (p ^ nu) → ℂ := fun xi =>
      (Real.sqrt (wooleyWeightedResidueMassSq gamma xi) : ℂ) *
        wooleyPolynomialNormalizedResidueGridSum
          phi (p ^ B) gamma alpha xi
    have hM : 0 < M := lt_of_le_of_ne
      (wooleyWeightedMassSq_nonneg gamma) (Ne.symm hmass)
    have hdecomp := wooleyPolynomial_normalizedGridSum_decomposition
      (qH := p ^ nu) phi gamma alpha hmass
    have hraw := wooley_norm_sum_sq_le_diagonal_add_offDiagonal
      (Finset.univ : Finset (ZMod (p ^ nu))) a
    have hscale :
        ‖((Real.sqrt M : ℝ) : ℂ)⁻¹‖ ^ 2 = M⁻¹ := by
      rw [norm_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _), inv_pow,
        Real.sq_sqrt hM.le]
    rw [hdecomp, norm_mul, mul_pow, hscale]
    calc
      M⁻¹ * ‖∑ xi : ZMod (p ^ nu), a xi‖ ^ 2 ≤
          M⁻¹ * ((∑ xi : ZMod (p ^ nu), ‖a xi‖ ^ 2) +
            ∑ xi : ZMod (p ^ nu),
              ∑ eta : ZMod (p ^ nu) with eta ≠ xi,
                ‖a xi‖ * ‖a eta‖) := by gcongr
      _ = wooleyPolynomialInitialDiagonal phi p B nu gamma alpha +
          wooleyPolynomialInitialOffDiagonal phi p B nu gamma alpha := by
        have hnormA (xi : ZMod (p ^ nu)) :
            ‖a xi‖ =
              Real.sqrt (wooleyWeightedResidueMassSq gamma xi) *
                ‖wooleyPolynomialNormalizedResidueGridSum
                  phi (p ^ B) gamma alpha xi‖ := by
          simp [a, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (Real.sqrt_nonneg _)]
        simp_rw [hnormA]
        unfold wooleyPolynomialInitialDiagonal
          wooleyPolynomialInitialOffDiagonal
        rw [mul_add]
        congr 1
        · apply congrArg (M⁻¹ * ·)
          apply Finset.sum_congr rfl
          intro xi hxi
          rw [mul_pow, Real.sq_sqrt
            (wooleyWeightedResidueMassSq_nonneg gamma xi)]
        · apply congrArg (M⁻¹ * ·)
          apply Finset.sum_congr rfl
          intro xi hxi
          apply Finset.sum_congr
          · ext eta
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            rw [wooleyResiduesSeparated_same_iff_ne]
            exact ne_comm
          · intro eta heta
            ring

/-- Polynomial-system equation (6.7). -/
theorem wooleyPolynomial_equation_6_7 {Q k : ℕ}
    (phi : WooleyPolynomialSystem k) (p B nu s : ℕ)
    [NeZero p] [NeZero (p ^ B)]
    (gamma : Fin Q → ℂ) (alpha : Fin k → ZMod (p ^ B))
    (hs : 1 ≤ s) :
    wooleyPolynomialInitialDiagonal phi p B nu gamma alpha ^ s ≤
      (wooleyWeightedMassSq gamma)⁻¹ *
        ∑ xi : ZMod (p ^ nu),
          wooleyWeightedResidueMassSq gamma xi *
            ‖wooleyPolynomialNormalizedResidueGridSum
              phi (p ^ B) gamma alpha xi‖ ^ (2 * s) := by
  by_cases hmass : wooleyWeightedMassSq gamma = 0
  · have hs0 : s ≠ 0 := by omega
    simp [wooleyPolynomialInitialDiagonal, hmass, hs0]
  · let M : ℝ := wooleyWeightedMassSq gamma
    let w : ZMod (p ^ nu) → ℝ := fun xi =>
      wooleyWeightedResidueMassSq gamma xi
    let f : ZMod (p ^ nu) → ℝ := fun xi =>
      ‖wooleyPolynomialNormalizedResidueGridSum
        phi (p ^ B) gamma alpha xi‖ ^ 2
    let R : ℝ := ∑ xi : ZMod (p ^ nu),
      w xi * ‖wooleyPolynomialNormalizedResidueGridSum
        phi (p ^ B) gamma alpha xi‖ ^ (2 * s)
    have hM : 0 < M := lt_of_le_of_ne
      (wooleyWeightedMassSq_nonneg gamma) (Ne.symm hmass)
    have hholder := wooley_weighted_rpow_sum_le
      (Finset.univ : Finset (ZMod (p ^ nu))) w f
      (p := (s : ℝ)) (by exact_mod_cast hs)
      (fun xi => wooleyWeightedResidueMassSq_nonneg gamma xi)
      (fun xi => sq_nonneg _)
    have hsub : (s : ℝ) - 1 = ((s - 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub hs]
      norm_num
    have hholderNat :
        (∑ xi : ZMod (p ^ nu), w xi * f xi) ^ s ≤
          M ^ (s - 1) * R := by
      rw [← Real.rpow_natCast] at ⊢
      calc
        (∑ xi : ZMod (p ^ nu), w xi * f xi) ^ (s : ℝ) ≤
            (∑ xi : ZMod (p ^ nu), w xi) ^ ((s : ℝ) - 1) *
              ∑ xi : ZMod (p ^ nu), w xi * f xi ^ (s : ℝ) := hholder
        _ = M ^ (s - 1) * R := by
          dsimp [w, f, M, R]
          rw [wooley_sum_weightedResidueMassSq, hsub,
            Real.rpow_natCast]
          apply congrArg (wooleyWeightedMassSq gamma ^ (s - 1) * ·)
          apply Finset.sum_congr rfl
          intro xi hxi
          rw [Real.rpow_natCast, ← pow_mul]
    unfold wooleyPolynomialInitialDiagonal
    change (M⁻¹ * ∑ xi : ZMod (p ^ nu), w xi * f xi) ^ s ≤ M⁻¹ * R
    calc
      (M⁻¹ * ∑ xi : ZMod (p ^ nu), w xi * f xi) ^ s =
          M⁻¹ ^ s * (∑ xi : ZMod (p ^ nu), w xi * f xi) ^ s := by
        rw [mul_pow]
      _ ≤ M⁻¹ ^ s * (M ^ (s - 1) * R) := by gcongr
      _ = M⁻¹ * R := by
        rw [← mul_assoc, wooley_inv_pow_mul_pow_pred hM hs]

/-- Polynomial-system equation (6.8). -/
theorem wooleyPolynomial_equation_6_8 {Q k : ℕ}
    (phi : WooleyPolynomialSystem k) (p B nu s : ℕ)
    [NeZero p] [NeZero (p ^ B)]
    (gamma : Fin Q → ℂ) (alpha : Fin k → ZMod (p ^ B))
    (hs : 2 ≤ s) :
    wooleyPolynomialInitialOffDiagonal phi p B nu gamma alpha ^ s ≤
      (wooleyWeightedMassSq gamma)⁻¹ ^ 2 *
        (p ^ nu : ℝ) ^ s *
          wooleyPolynomialInitialMixedForward
            phi p B nu s gamma alpha := by
  by_cases hmass : wooleyWeightedMassSq gamma = 0
  · have hs0 : s ≠ 0 := by omega
    simp [wooleyPolynomialInitialOffDiagonal, hmass, hs0]
  · let M : ℝ := wooleyWeightedMassSq gamma
    let q : ℝ := (p ^ nu : ℕ)
    let t : Finset (ZMod (p ^ nu) × ZMod (p ^ nu)) :=
      wooleySeparatedResiduePairs p nu
    let w : (ZMod (p ^ nu) × ZMod (p ^ nu)) → ℝ := fun xy =>
      wooleyWeightedResidueMassSq gamma xy.1 *
        wooleyWeightedResidueMassSq gamma xy.2
    let u : (ZMod (p ^ nu) × ZMod (p ^ nu)) → ℝ := fun xy =>
      ‖wooleyPolynomialNormalizedResidueGridSum
        phi (p ^ B) gamma alpha xy.1‖
    let v : (ZMod (p ^ nu) × ZMod (p ^ nu)) → ℝ := fun xy =>
      ‖wooleyPolynomialNormalizedResidueGridSum
        phi (p ^ B) gamma alpha xy.2‖
    let S : ℝ := ∑ xy ∈ t, Real.sqrt (w xy) * u xy * v xy
    let F : ℝ := ∑ xy ∈ t,
      w xy * u xy ^ 2 * v xy ^ (2 * (s - 1))
    have hMpos : 0 < M := lt_of_le_of_ne
      (wooleyWeightedMassSq_nonneg gamma) (Ne.symm hmass)
    have hq : 0 ≤ q := by positivity
    have hw : ∀ xy ∈ t, 0 ≤ w xy := by
      intro xy hxy
      exact mul_nonneg
        (wooleyWeightedResidueMassSq_nonneg gamma xy.1)
        (wooleyWeightedResidueMassSq_nonneg gamma xy.2)
    have hu : ∀ xy ∈ t, 0 ≤ u xy := fun _ _ => norm_nonneg _
    have hv : ∀ xy ∈ t, 0 ≤ v xy := fun _ _ => norm_nonneg _
    have hcard : (#t : ℝ) ≤ q ^ 2 := by
      dsimp [t, q]
      exact_mod_cast wooleySeparatedResiduePairs_card_le p nu
    have hpairMass : (∑ xy ∈ t, w xy) ≤ M ^ 2 := by
      dsimp [t, w, M]
      rw [wooley_sum_separatedResiduePairs_apply]
      exact wooley_separated_pair_mass_le_square p nu gamma
    have hF : F = wooleyPolynomialInitialMixedForward
        phi p B nu s gamma alpha := by
      dsimp [F, t, w, u, v]
      rw [wooley_sum_separatedResiduePairs_apply]
      rfl
    have hsym :
        (∑ xy ∈ t,
          w xy * v xy ^ 2 * u xy ^ (2 * (s - 1))) = F := by
      dsimp [t, w, u, v]
      rw [wooley_sum_separatedResiduePairs_apply]
      calc
        (∑ xi : ZMod (p ^ nu),
          ∑ eta : ZMod (p ^ nu) with
            wooleyResiduesSeparated nu xi eta,
              wooleyWeightedResidueMassSq gamma xi *
                wooleyWeightedResidueMassSq gamma eta *
                ‖wooleyPolynomialNormalizedResidueGridSum
                  phi (p ^ B) gamma alpha eta‖ ^ 2 *
                ‖wooleyPolynomialNormalizedResidueGridSum
                  phi (p ^ B) gamma alpha xi‖ ^ (2 * (s - 1))) =
            wooleyPolynomialInitialMixedForward
              phi p B nu s gamma alpha :=
          wooleyPolynomialInitialMixedReverse_eq_forward
            phi p B nu s gamma alpha
        _ = F := hF.symm
    have hcore : S ^ s ≤ q ^ s * M ^ (s - 2) * F :=
      wooley_cauchy_three_factor_symmetric
        t w u v q M hq hMpos.le hw hu hv hs hcard hpairMass
          (by simpa [F] using hsym)
    have hS : S =
        ∑ xi : ZMod (p ^ nu),
          ∑ eta : ZMod (p ^ nu) with wooleyResiduesSeparated nu xi eta,
            Real.sqrt (wooleyWeightedResidueMassSq gamma xi) *
              Real.sqrt (wooleyWeightedResidueMassSq gamma eta) *
              ‖wooleyPolynomialNormalizedResidueGridSum
                phi (p ^ B) gamma alpha xi‖ *
              ‖wooleyPolynomialNormalizedResidueGridSum
                phi (p ^ B) gamma alpha eta‖ := by
      dsimp [S, t, w, u, v]
      rw [wooley_sum_separatedResiduePairs_apply]
      apply Finset.sum_congr rfl
      intro xi hxi
      apply Finset.sum_congr rfl
      intro eta heta
      rw [Real.sqrt_mul
        (wooleyWeightedResidueMassSq_nonneg gamma xi)]
    have hT2 : wooleyPolynomialInitialOffDiagonal
        phi p B nu gamma alpha = M⁻¹ * S := by
      unfold wooleyPolynomialInitialOffDiagonal
      dsimp [M]
      rw [hS]
    have hqEq : q = (p : ℝ) ^ nu := by
      dsimp [q]
      norm_cast
    rw [hT2, ← hqEq]
    calc
      (M⁻¹ * S) ^ s = M⁻¹ ^ s * S ^ s := by rw [mul_pow]
      _ ≤ M⁻¹ ^ s * (q ^ s * M ^ (s - 2) * F) := by gcongr
      _ = M⁻¹ ^ 2 * q ^ s *
          wooleyPolynomialInitialMixedForward
            phi p B nu s gamma alpha := by
        rw [hF]
        calc
          M⁻¹ ^ s *
              (q ^ s * M ^ (s - 2) *
                wooleyPolynomialInitialMixedForward
                  phi p B nu s gamma alpha) =
              (M⁻¹ ^ s * M ^ (s - 2)) * q ^ s *
                wooleyPolynomialInitialMixedForward
                  phi p B nu s gamma alpha := by ring
          _ = M⁻¹ ^ 2 * q ^ s *
                wooleyPolynomialInitialMixedForward
                  phi p B nu s gamma alpha := by
            rw [wooley_inv_pow_mul_pow_sub_two hMpos hs]

/-- The polynomial-system pointwise form of equation (6.9). -/
theorem wooleyPolynomial_equation_6_9_pointwise {Q k : ℕ}
    (phi : WooleyPolynomialSystem k) (p B nu s : ℕ)
    [NeZero p] [NeZero (p ^ B)]
    (gamma : Fin Q → ℂ) (alpha : Fin k → ZMod (p ^ B))
    (hs : 2 ≤ s) :
    ‖wooleyPolynomialNormalizedGridSum phi (p ^ B) gamma alpha‖ ^
        (2 * s) ≤
      2 ^ (s - 1) *
        ((wooleyWeightedMassSq gamma)⁻¹ *
            ∑ xi : ZMod (p ^ nu),
              wooleyWeightedResidueMassSq gamma xi *
                ‖wooleyPolynomialNormalizedResidueGridSum
                  phi (p ^ B) gamma alpha xi‖ ^ (2 * s) +
          (wooleyWeightedMassSq gamma)⁻¹ ^ 2 *
            (p ^ nu : ℝ) ^ s *
              wooleyPolynomialInitialMixedForward
                phi p B nu s gamma alpha) := by
  let D := wooleyPolynomialInitialDiagonal phi p B nu gamma alpha
  let O := wooleyPolynomialInitialOffDiagonal phi p B nu gamma alpha
  have hsplit := wooleyPolynomial_equation_6_6
    phi p B nu gamma alpha
  have hpow :
      (‖wooleyPolynomialNormalizedGridSum
        phi (p ^ B) gamma alpha‖ ^ 2) ^ s ≤ (D + O) ^ s :=
    pow_le_pow_left₀ (sq_nonneg _) hsplit s
  have hconv : (D + O) ^ s ≤
      2 ^ (s - 1) * (D ^ s + O ^ s) :=
    wooley_add_pow_le_two_pow_pred_mul
      (wooleyPolynomialInitialDiagonal_nonneg phi p B nu gamma alpha)
      (wooleyPolynomialInitialOffDiagonal_nonneg phi p B nu gamma alpha)
      (by omega)
  have hdiag := wooleyPolynomial_equation_6_7
    phi p B nu s gamma alpha (by omega)
  have hoff := wooleyPolynomial_equation_6_8
    phi p B nu s gamma alpha hs
  calc
    ‖wooleyPolynomialNormalizedGridSum phi (p ^ B) gamma alpha‖ ^
        (2 * s) =
        (‖wooleyPolynomialNormalizedGridSum
          phi (p ^ B) gamma alpha‖ ^ 2) ^ s := by rw [pow_mul]
    _ ≤ (D + O) ^ s := hpow
    _ ≤ 2 ^ (s - 1) * (D ^ s + O ^ s) := hconv
    _ ≤ _ := by gcongr

theorem wooleyPolynomial_initial_diagonal_average {Q k : ℕ}
    (phi : WooleyPolynomialSystem k) (p B nu s : ℕ)
    [NeZero p] [NeZero (p ^ B)] [NeZero (p ^ nu)]
    (gamma : Fin Q → ℂ) :
    ((((p ^ B) ^ k : ℕ) : ℝ))⁻¹ *
        ∑ alpha : Fin k → ZMod (p ^ B),
          (wooleyWeightedMassSq gamma)⁻¹ *
            ∑ xi : ZMod (p ^ nu),
              wooleyWeightedResidueMassSq gamma xi *
                ‖wooleyPolynomialNormalizedResidueGridSum
                  phi (p ^ B) gamma alpha xi‖ ^ (2 * s) =
      wooleyPolynomialConditionedGridMean
        phi s (p ^ B) (p ^ nu) gamma := by
  unfold wooleyPolynomialConditionedGridMean
  split_ifs with hmass
  · simp [hmass]
  · simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro xi hxi
    apply Finset.sum_congr rfl
    intro alpha halpha
    ac_rfl

theorem wooleyPolynomial_initial_mixed_average {Q k : ℕ}
    (phi : WooleyPolynomialSystem k) (p B nu s : ℕ)
    [NeZero p] [NeZero (p ^ B)]
    (gamma : Fin Q → ℂ) :
    ((((p ^ B) ^ k : ℕ) : ℝ))⁻¹ *
        ∑ alpha : Fin k → ZMod (p ^ B),
          (wooleyWeightedMassSq gamma)⁻¹ ^ 2 *
            wooleyPolynomialInitialMixedForward
              phi p B nu s gamma alpha =
      wooleyPolynomialMixedGridMean
        phi s 1 p B nu nu nu gamma := by
  unfold wooleyPolynomialMixedGridMean
  split_ifs with hmass
  · simp [hmass]
  · simp only [wooleyPolynomialMixedResidueGridMoment,
      wooleyTriangular_one, Nat.mul_one]
    unfold wooleyPolynomialInitialMixedForward
    simp_rw [Finset.mul_sum]
    rw [show
      (∑ alpha : Fin k → ZMod (p ^ B),
        ∑ xi : ZMod (p ^ nu),
          ∑ eta : ZMod (p ^ nu) with wooleyResiduesSeparated nu xi eta,
            ((((p ^ B) ^ k : ℕ) : ℝ))⁻¹ *
              ((wooleyWeightedMassSq gamma)⁻¹ ^ 2 *
                (wooleyWeightedResidueMassSq gamma xi *
                  wooleyWeightedResidueMassSq gamma eta *
                  ‖wooleyPolynomialNormalizedResidueGridSum
                    phi (p ^ B) gamma alpha xi‖ ^ 2 *
                  ‖wooleyPolynomialNormalizedResidueGridSum
                    phi (p ^ B) gamma alpha eta‖ ^ (2 * (s - 1))))) =
        ∑ xi : ZMod (p ^ nu),
          ∑ eta : ZMod (p ^ nu) with wooleyResiduesSeparated nu xi eta,
            ∑ alpha : Fin k → ZMod (p ^ B),
              ((((p ^ B) ^ k : ℕ) : ℝ))⁻¹ *
                ((wooleyWeightedMassSq gamma)⁻¹ ^ 2 *
                  (wooleyWeightedResidueMassSq gamma xi *
                    wooleyWeightedResidueMassSq gamma eta *
                    ‖wooleyPolynomialNormalizedResidueGridSum
                      phi (p ^ B) gamma alpha xi‖ ^ 2 *
                    ‖wooleyPolynomialNormalizedResidueGridSum
                      phi (p ^ B) gamma alpha eta‖ ^ (2 * (s - 1)))) by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro xi hxi
        rw [Finset.sum_comm]]
    apply Finset.sum_congr rfl
    intro xi hxi
    apply Finset.sum_congr rfl
    intro eta heta
    apply Finset.sum_congr rfl
    intro alpha halpha
    ac_rfl

/-- Polynomial-system equation (6.9), on the exact finite grid. -/
theorem wooleyPolynomial_equation_6_9 {Q k : ℕ}
    (phi : WooleyPolynomialSystem k) (p B nu s : ℕ)
    [NeZero p] [NeZero (p ^ B)] [NeZero (p ^ nu)]
    (gamma : Fin Q → ℂ) (hs : 2 ≤ s) :
    wooleyPolynomialWeightedGridMean phi s (p ^ B) gamma ≤
      2 ^ (s - 1) *
        (wooleyPolynomialConditionedGridMean
            phi s (p ^ B) (p ^ nu) gamma +
          (p ^ nu : ℝ) ^ s *
            wooleyPolynomialMixedGridMean
              phi s 1 p B nu nu nu gamma) := by
  let c : ℝ := 2 ^ (s - 1)
  let scale : ℝ := ((((p ^ B) ^ k : ℕ) : ℝ))⁻¹
  have hscale : 0 ≤ scale := by positivity
  have hsum :
      scale *
          ∑ alpha : Fin k → ZMod (p ^ B),
            ‖wooleyPolynomialNormalizedGridSum
              phi (p ^ B) gamma alpha‖ ^ (2 * s) ≤
        scale *
          ∑ alpha : Fin k → ZMod (p ^ B),
            c *
              ((wooleyWeightedMassSq gamma)⁻¹ *
                  ∑ xi : ZMod (p ^ nu),
                    wooleyWeightedResidueMassSq gamma xi *
                      ‖wooleyPolynomialNormalizedResidueGridSum
                        phi (p ^ B) gamma alpha xi‖ ^ (2 * s) +
                (wooleyWeightedMassSq gamma)⁻¹ ^ 2 *
                  (p ^ nu : ℝ) ^ s *
                    wooleyPolynomialInitialMixedForward
                      phi p B nu s gamma alpha) := by
    apply mul_le_mul_of_nonneg_left _ hscale
    apply Finset.sum_le_sum
    intro alpha halpha
    exact wooleyPolynomial_equation_6_9_pointwise
      phi p B nu s gamma alpha hs
  unfold wooleyPolynomialWeightedGridMean
  change scale *
      ∑ alpha : Fin k → ZMod (p ^ B),
        ‖wooleyPolynomialNormalizedGridSum
          phi (p ^ B) gamma alpha‖ ^ (2 * s) ≤ _
  calc
    scale * ∑ alpha : Fin k → ZMod (p ^ B),
        ‖wooleyPolynomialNormalizedGridSum
          phi (p ^ B) gamma alpha‖ ^ (2 * s) ≤
      scale * ∑ alpha : Fin k → ZMod (p ^ B),
        c *
          ((wooleyWeightedMassSq gamma)⁻¹ *
              ∑ xi : ZMod (p ^ nu),
                wooleyWeightedResidueMassSq gamma xi *
                  ‖wooleyPolynomialNormalizedResidueGridSum
                    phi (p ^ B) gamma alpha xi‖ ^ (2 * s) +
            (wooleyWeightedMassSq gamma)⁻¹ ^ 2 *
              (p ^ nu : ℝ) ^ s *
                wooleyPolynomialInitialMixedForward
                  phi p B nu s gamma alpha) := hsum
    _ = c *
        (wooleyPolynomialConditionedGridMean
            phi s (p ^ B) (p ^ nu) gamma +
          (p ^ nu : ℝ) ^ s *
            wooleyPolynomialMixedGridMean
              phi s 1 p B nu nu nu gamma) := by
      let A : (Fin k → ZMod (p ^ B)) → ℝ := fun alpha =>
        (wooleyWeightedMassSq gamma)⁻¹ *
          ∑ xi : ZMod (p ^ nu),
            wooleyWeightedResidueMassSq gamma xi *
              ‖wooleyPolynomialNormalizedResidueGridSum
                phi (p ^ B) gamma alpha xi‖ ^ (2 * s)
      let F : (Fin k → ZMod (p ^ B)) → ℝ := fun alpha =>
        (wooleyWeightedMassSq gamma)⁻¹ ^ 2 *
          wooleyPolynomialInitialMixedForward
            phi p B nu s gamma alpha
      have hA : scale * ∑ alpha, A alpha =
          wooleyPolynomialConditionedGridMean
            phi s (p ^ B) (p ^ nu) gamma :=
        wooleyPolynomial_initial_diagonal_average phi p B nu s gamma
      have hF : scale * ∑ alpha, F alpha =
          wooleyPolynomialMixedGridMean
            phi s 1 p B nu nu nu gamma :=
        wooleyPolynomial_initial_mixed_average phi p B nu s gamma
      have hsumF :
          (∑ alpha, (p ^ nu : ℝ) ^ s * F alpha) =
            (p ^ nu : ℝ) ^ s * ∑ alpha, F alpha := by
        rw [Finset.mul_sum]
      have hbody (alpha : Fin k → ZMod (p ^ B)) :
          (wooleyWeightedMassSq gamma)⁻¹ *
                ∑ xi : ZMod (p ^ nu),
                  wooleyWeightedResidueMassSq gamma xi *
                    ‖wooleyPolynomialNormalizedResidueGridSum
                      phi (p ^ B) gamma alpha xi‖ ^ (2 * s) +
              (wooleyWeightedMassSq gamma)⁻¹ ^ 2 *
                (p ^ nu : ℝ) ^ s *
                  wooleyPolynomialInitialMixedForward
                    phi p B nu s gamma alpha =
            A alpha + (p ^ nu : ℝ) ^ s * F alpha := by
        dsimp [A, F]
        ring
      simp_rw [hbody]
      change scale * ∑ alpha, c *
          (A alpha + (p ^ nu : ℝ) ^ s * F alpha) = _
      rw [← Finset.mul_sum, Finset.sum_add_distrib, hsumF]
      rw [mul_add]
      calc
        scale * (c * (∑ x, A x) +
            c * ((p ^ nu : ℝ) ^ s * ∑ x, F x)) =
            c * (scale * ∑ x, A x) +
              c * ((p ^ nu : ℝ) ^ s * (scale * ∑ x, F x)) := by ring
        _ = _ := by rw [hA, hF]; ring
    _ = _ := by rfl

#print axioms wooleyPolynomial_equation_6_6
#print axioms wooleyPolynomial_equation_6_7
#print axioms wooleyPolynomial_equation_6_8
#print axioms wooleyPolynomial_equation_6_9_pointwise
#print axioms wooleyPolynomial_equation_6_9

end


end GafniTao
