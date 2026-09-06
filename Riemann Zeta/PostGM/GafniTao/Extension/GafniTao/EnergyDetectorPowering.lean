import GafniTao.EnergyDetectorTranslation
import RiemannZeta.GuthMaynard.ClassicalPowering

/-!
# Exact powering of positive-sign detector blocks

Guth--Maynard's finite powering API is written for the negative-sign
Dirichlet-polynomial convention.  The zero-energy detector naturally emits
the positive-sign source convention.  This file supplies the exact bridge:
conjugate the base coefficient, apply the frozen finite convolution and
normalization, and conjugate the powered coefficient back.  No ordinate is
reflected and the separated set therefore stays inside its translated base
interval.
-/

open scoped BigOperators

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- The unit-normalized positive-sign coefficient obtained from the exact
`k`-fold convolution of a positive-sign source block. -/
noncomputable def sourceNormalizedFinitePoweredCoeffs
    (N k : Nat) (a : Nat → Complex) (C eta : Real) (m : Nat) : Complex :=
  conjugateCoeffs
    (normalizedFinitePoweredCoeffs N k (conjugateCoeffs a) 0 C eta) m

/-- The selected ordinary dyadic block lies in the full wide powered
support. -/
theorem sourcePoweredDyadicBlock_subset
    {N k r n : Nat} (hr : r < k)
    (hn : n ∈ dyadicInterval (2 ^ r * N ^ k)) :
    n ∈ Finset.Ioc (N ^ k) (2 ^ k * N ^ k) := by
  rw [dyadicInterval] at hn
  rw [Finset.mem_Ioc] at hn ⊢
  constructor
  · exact lt_of_le_of_lt
      (Nat.le_mul_of_pos_left _ (pow_pos (by omega) r)) hn.1
  · have hrSucc : r + 1 ≤ k := by omega
    have hPow : 2 ^ (r + 1) ≤ (2 : Nat) ^ k :=
      pow_le_pow_right₀ (by omega : (1 : Nat) ≤ 2) hrSucc
    calc
      n ≤ 2 * (2 ^ r * N ^ k) := hn.2
      _ = 2 ^ (r + 1) * N ^ k := by rw [pow_succ]; ring
      _ ≤ 2 ^ k * N ^ k := Nat.mul_le_mul_right _ hPow

/-- Unit coefficient control survives the two exact conjugations and
restriction to any ordinary dyadic subblock of the powered support. -/
theorem norm_sourceNormalizedFinitePoweredCoeffs_le_one
    {N k r n : Nat} {a : Nat → Complex} {C eta : Real}
    (hN : 0 < N) (hC : 0 < C) (heta : 0 < eta) (hr : r < k)
    (hn : n ∈ dyadicInterval (2 ^ r * N ^ k))
    (hPow : ∀ m : Nat, 0 < m →
      ‖finitePowCoeff N k (conjugateCoeffs a) m‖ ≤
        C * (m : Real) ^ eta) :
    ‖sourceNormalizedFinitePoweredCoeffs N k a C eta n‖ ≤ 1 := by
  rw [sourceNormalizedFinitePoweredCoeffs, norm_conjugateCoeffs]
  apply norm_normalizedFinitePoweredCoeffs_le_one
      N k n (conjugateCoeffs a) 0 C eta hN (by norm_num) hC heta
      (sourcePoweredDyadicBlock_subset hr hn)
  exact hPow n (by
    have hnWide := sourcePoweredDyadicBlock_subset hr hn
    exact lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_Ioc.mp hnWide).1)

/-- Pointwise form of exact source-sign powering with a fixed coefficient
majorant.  This is the choice function used when additive quadruples are
colored by their selected powered dyadic blocks. -/
theorem exists_source_powered_dyadic_index
    (N k : Nat) (a : Nat → Complex) (C eta L t : Real)
    (hN : 0 < N) (hk : 0 < k) (hC : 0 < C)
    (hL : 0 ≤ L)
    (hLarge : L ≤ ‖sourceDirichletPoly N a t‖) :
    ∃ r ∈ Finset.range k,
      (L ^ k / (C * ((2 ^ k * N ^ k : Nat) : Real) ^ eta)) / k ≤
        ‖sourceDirichletPoly (2 ^ r * N ^ k)
          (sourceNormalizedFinitePoweredCoeffs N k a C eta) t‖ := by
  have hDenom : 0 < C * ((2 ^ k * N ^ k : Nat) : Real) ^ eta := by
    have hUpper : 0 < 2 ^ k * N ^ k :=
      Nat.mul_pos (pow_pos (by omega) k) (pow_pos hN k)
    exact mul_pos hC (Real.rpow_pos_of_pos (by exact_mod_cast hUpper) _)
  have hDouble : conjugateCoeffs (conjugateCoeffs a) = a := by
    funext n
    simp [conjugateCoeffs]
  have hConvention : ‖dirichletPoly N (conjugateCoeffs a) t‖ =
      ‖sourceDirichletPoly N a t‖ := by
    calc
      ‖dirichletPoly N (conjugateCoeffs a) t‖ =
          ‖sourceDirichletPoly N
            (conjugateCoeffs (conjugateCoeffs a)) t‖ :=
        (norm_sourceDirichletPoly_conjugateCoeffs
          N (conjugateCoeffs a) t).symm
      _ = ‖sourceDirichletPoly N a t‖ := by rw [hDouble]
  have hBase : L ≤ ‖∑ n ∈ Finset.Ioc N (2 * N),
      conjugateCoeffs a n * (n : Complex) ^ (-(0 + Complex.I * t))‖ := by
    have hPoly :
        (∑ n ∈ Finset.Ioc N (2 * N), conjugateCoeffs a n *
          (n : Complex) ^ (-(0 + Complex.I * t))) =
          dirichletPoly N (conjugateCoeffs a) t := by
      unfold dirichletPoly dyadicInterval
      apply Finset.sum_congr rfl
      intro n hn
      congr 2
      ring
    rw [hPoly, hConvention]
    exact hLarge
  have hWide0 := normalized_finite_powered_wide_lower
    N k (conjugateCoeffs a) 0 C eta t L hN hk hL hDenom hBase
  have hWide : L ^ k / (C * ((2 ^ k * N ^ k : Nat) : Real) ^ eta) ≤
      ‖wideDirichletPoly (N ^ k) k
        (normalizedFinitePoweredCoeffs N k (conjugateCoeffs a) 0 C eta) t‖ := by
    simpa using hWide0
  obtain ⟨r, hr, hrLarge⟩ := exists_large_dyadic_block
    (N ^ k) k
    (normalizedFinitePoweredCoeffs N k (conjugateCoeffs a) 0 C eta) t
    (L ^ k / (C * ((2 ^ k * N ^ k : Nat) : Real) ^ eta)) hk hWide
  refine ⟨r, hr, ?_⟩
  change _ ≤ ‖sourceDirichletPoly (2 ^ r * N ^ k)
    (conjugateCoeffs
      (normalizedFinitePoweredCoeffs N k (conjugateCoeffs a) 0 C eta)) t‖
  rw [norm_sourceDirichletPoly_conjugateCoeffs]
  exact hrLarge

/-- Exact source-sign powered extraction.  A common large positive-sign
block on `W` yields one common powered dyadic block on a subfamily `W'`, with
the factorization constant, dyadic loss, support, and unit normalization all
visible in the conclusion. -/
theorem exists_source_normalized_powered_block
    (N k : Nat) (a : Nat → Complex) (eta L : Real) (W : Finset Real)
    (hN : 0 < N) (hk : 0 < k) (heta : 0 < eta) (hL : 0 ≤ L)
    (hCoeff : ∀ n ∈ dyadicInterval N, ‖a n‖ ≤ 1)
    (hLarge : ∀ t ∈ W, L ≤ ‖sourceDirichletPoly N a t‖) :
    ∃ C : Real, 0 < C ∧
      ∃ r ∈ Finset.range k, ∃ W' ⊆ W,
        (W.card : Real) ≤ k * (W'.card : Real) ∧
        (∀ n ∈ dyadicInterval (2 ^ r * N ^ k),
          ‖sourceNormalizedFinitePoweredCoeffs N k a C eta n‖ ≤ 1) ∧
        ∀ t ∈ W',
          (L ^ k /
              (C * ((2 ^ k * N ^ k : Nat) : Real) ^ eta)) / k ≤
            ‖sourceDirichletPoly (2 ^ r * N ^ k)
              (sourceNormalizedFinitePoweredCoeffs N k a C eta) t‖ := by
  obtain ⟨C, hC, hPow⟩ := finitePowCoeff_bound_uniform k eta heta
  have hConjCoeff : ∀ n ∈ dyadicInterval N, ‖conjugateCoeffs a n‖ ≤ 1 := by
    intro n hn
    rw [norm_conjugateCoeffs]
    exact hCoeff n hn
  have hBase : ∀ t ∈ W, L ≤
      ‖∑ n ∈ Finset.Ioc N (2 * N),
        conjugateCoeffs a n * (n : Complex) ^ (-(0 + Complex.I * t))‖ := by
    intro t ht
    have hDouble : conjugateCoeffs (conjugateCoeffs a) = a := by
      funext n
      simp [conjugateCoeffs]
    have hConvention :
        ‖dirichletPoly N (conjugateCoeffs a) t‖ =
          ‖sourceDirichletPoly N a t‖ := by
      calc
        ‖dirichletPoly N (conjugateCoeffs a) t‖ =
            ‖sourceDirichletPoly N
              (conjugateCoeffs (conjugateCoeffs a)) t‖ :=
          (norm_sourceDirichletPoly_conjugateCoeffs
            N (conjugateCoeffs a) t).symm
        _ = ‖sourceDirichletPoly N a t‖ := by rw [hDouble]
    have hPoly :
        (∑ n ∈ Finset.Ioc N (2 * N),
          conjugateCoeffs a n *
            (n : Complex) ^ (-(0 + Complex.I * t))) =
          dirichletPoly N (conjugateCoeffs a) t := by
      unfold dirichletPoly dyadicInterval
      apply Finset.sum_congr rfl
      intro n hn
      congr 2
      ring
    rw [hPoly, hConvention]
    exact hLarge t ht
  have hDenom : 0 < C * ((2 ^ k * N ^ k : Nat) : Real) ^ eta := by
    have hUpper : 0 < 2 ^ k * N ^ k :=
      Nat.mul_pos (pow_pos (by omega) k) (pow_pos hN k)
    exact mul_pos hC (Real.rpow_pos_of_pos (by exact_mod_cast hUpper) _)
  obtain ⟨r, hr, W', hW', hCard, hPowered⟩ :=
    extract_normalized_finite_powered_block N k (conjugateCoeffs a)
      0 C eta L W hN hk hL hDenom hBase
  refine ⟨C, hC, r, hr, W', hW', hCard, ?_, ?_⟩
  · intro n hn
    exact norm_sourceNormalizedFinitePoweredCoeffs_le_one
      hN hC heta (Finset.mem_range.mp hr) hn
        (hPow N (conjugateCoeffs a) hConjCoeff)
  · intro t ht
    have hSource := norm_sourceDirichletPoly_conjugateCoeffs
      (2 ^ r * N ^ k)
      (normalizedFinitePoweredCoeffs N k (conjugateCoeffs a) 0 C eta) t
    change (L ^ k /
        (C * ((2 ^ k * N ^ k : Nat) : Real) ^ eta)) / k ≤
      ‖sourceDirichletPoly (2 ^ r * N ^ k)
        (conjugateCoeffs
          (normalizedFinitePoweredCoeffs N k (conjugateCoeffs a) 0 C eta)) t‖
    rw [hSource]
    simpa using hPowered t ht

#print axioms sourcePoweredDyadicBlock_subset
#print axioms norm_sourceNormalizedFinitePoweredCoeffs_le_one
#print axioms exists_source_powered_dyadic_index
#print axioms exists_source_normalized_powered_block

end

end GafniTao
