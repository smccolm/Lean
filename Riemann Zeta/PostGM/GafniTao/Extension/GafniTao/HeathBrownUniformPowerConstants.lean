import GafniTao.HeathBrownSourceThreshold
import GafniTao.HeathBrownPoweredCardinality

/-!
# Uniform constants for the bounded source powers

The source power is bounded solely in terms of the fixed cutoff exponent.
Consequently the factorization constants must be selected uniformly over a
finite range of powers before the physical height and detector coefficients
are introduced.  This module proves that quantifier-correct selection and a
fixed-constant version of the positive-sign powered extraction.
-/

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- One factorization constant works for every power at most `P`. -/
theorem finitePowCoeff_bound_uniform_up_to
    (P : Nat) (eta : Real) (heta : 0 < eta) :
    ∃ Cp : Real, 1 ≤ Cp ∧
      ∀ (p : Nat), p ≤ P → ∀ (N : Nat) (a : Nat → Complex),
        (∀ n ∈ dyadicInterval N, ‖a n‖ ≤ 1) →
        ∀ m : Nat, 0 < m →
          ‖finitePowCoeff N p a m‖ ≤ Cp * (m : Real) ^ eta := by
  have hEach : ∀ p : Nat, ∃ c : Real, 0 < c ∧
      ∀ (N : Nat) (a : Nat → Complex),
        (∀ n ∈ dyadicInterval N, ‖a n‖ ≤ 1) →
        ∀ m : Nat, 0 < m →
          ‖finitePowCoeff N p a m‖ ≤ c * (m : Real) ^ eta :=
    fun p => finitePowCoeff_bound_uniform p eta heta
  choose c hc hBound using hEach
  let Cp : Real := 1 + ∑ p ∈ Finset.range (P + 1), c p
  have hSumNonneg : 0 ≤ ∑ p ∈ Finset.range (P + 1), c p :=
    Finset.sum_nonneg fun p _ => (hc p).le
  have hCp : 1 ≤ Cp := by
    dsimp only [Cp]
    linarith
  refine ⟨Cp, hCp, ?_⟩
  intro p hpP N a ha m hm
  have hpMem : p ∈ Finset.range (P + 1) :=
    Finset.mem_range.mpr (by omega)
  have hcp : c p ≤ Cp := by
    have hSingle : c p ≤ ∑ j ∈ Finset.range (P + 1), c j :=
      Finset.single_le_sum (fun j _ => (hc j).le) hpMem
    dsimp only [Cp]
    linarith
  exact (hBound p N a ha m hm).trans
    (mul_le_mul_of_nonneg_right hcp
      (Real.rpow_nonneg (by positivity) eta))

/-- Positive-sign powered extraction with a coefficient constant supplied
by the caller.  This is the quantifier-correct counterpart of the convenient
existential wrapper `exists_source_normalized_powered_block`. -/
theorem exists_source_normalized_powered_block_of_bound
    (N p : Nat) (a : Nat → Complex) (Cp eta L : Real)
    (W : Finset Real)
    (hN : 0 < N) (hp : 0 < p) (hCp : 0 < Cp)
    (heta : 0 < eta) (hL : 0 ≤ L)
    (hCoeff : ∀ n ∈ dyadicInterval N, ‖a n‖ ≤ 1)
    (hPow : ∀ m : Nat, 0 < m →
      ‖finitePowCoeff N p (conjugateCoeffs a) m‖ ≤
        Cp * (m : Real) ^ eta)
    (hLarge : ∀ t ∈ W, L ≤ ‖sourceDirichletPoly N a t‖) :
    ∃ r ∈ Finset.range p, ∃ W' ⊆ W,
      (W.card : Real) ≤ p * (W'.card : Real) ∧
      (∀ n ∈ dyadicInterval (2 ^ r * N ^ p),
        ‖sourceNormalizedFinitePoweredCoeffs N p a Cp eta n‖ ≤ 1) ∧
      ∀ t ∈ W',
        heathBrownPoweredThreshold N p L Cp eta ≤
          ‖sourceDirichletPoly (2 ^ r * N ^ p)
            (sourceNormalizedFinitePoweredCoeffs N p a Cp eta) t‖ := by
  have hConjCoeff : ∀ n ∈ dyadicInterval N,
      ‖conjugateCoeffs a n‖ ≤ 1 := by
    intro n hn
    rw [norm_conjugateCoeffs]
    exact hCoeff n hn
  have hBase : ∀ t ∈ W, L ≤
      ‖∑ n ∈ Finset.Ioc N (2 * N),
        conjugateCoeffs a n *
          (n : Complex) ^ (-(0 + Complex.I * t))‖ := by
    intro t ht
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
  have hDenom : 0 <
      Cp * ((2 ^ p * N ^ p : Nat) : Real) ^ eta := by
    have hSupport : 0 < 2 ^ p * N ^ p :=
      Nat.mul_pos (pow_pos (by omega) p) (pow_pos hN p)
    exact mul_pos hCp
      (Real.rpow_pos_of_pos (by exact_mod_cast hSupport) eta)
  obtain ⟨r, hr, W', hW', hCard, hPowered⟩ :=
    extract_normalized_finite_powered_block N p (conjugateCoeffs a)
      0 Cp eta L W hN hp hL hDenom hBase
  refine ⟨r, hr, W', hW', hCard, ?_, ?_⟩
  · intro n hn
    exact norm_sourceNormalizedFinitePoweredCoeffs_le_one
      hN hCp heta (Finset.mem_range.mp hr) hn hPow
  · intro t ht
    have hSource := norm_sourceDirichletPoly_conjugateCoeffs
      (2 ^ r * N ^ p)
      (normalizedFinitePoweredCoeffs N p
        (conjugateCoeffs a) 0 Cp eta) t
    change heathBrownPoweredThreshold N p L Cp eta ≤
      ‖sourceDirichletPoly (2 ^ r * N ^ p)
        (conjugateCoeffs
          (normalizedFinitePoweredCoeffs N p
            (conjugateCoeffs a) 0 Cp eta)) t‖
    rw [hSource]
    simpa only [heathBrownPoweredThreshold, Real.rpow_zero, one_mul] using
      hPowered t ht

#print axioms finitePowCoeff_bound_uniform_up_to
#print axioms exists_source_normalized_powered_block_of_bound

end

end GafniTao
