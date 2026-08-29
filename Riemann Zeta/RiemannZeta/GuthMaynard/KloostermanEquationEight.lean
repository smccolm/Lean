import RiemannZeta.GuthMaynard.KloostermanClosedPoints
import RiemannZeta.GuthMaynard.KloostermanCurveTrace

/-!
# Harcos equation (8)

This file assembles the closed-point formula of Harcos equation (10) into
the extension-field Kloosterman trace formula (8).  The first stage records
the exact tower degree and the trace of a root and its inverse.
-/

open Polynomial Classical
open scoped BigOperators

namespace RiemannZeta.GuthMaynard

noncomputable section

/-- The `galoisFieldFintype` definition used by the source-facing construction in `KloostermanEquationEight`. -/
noncomputable local instance galoisFieldFintype
    (p n : ℕ) [Fact p.Prime] : Fintype (GaloisField p n) :=
  Fintype.ofFinite (GaloisField p n)

theorem minpoly_eq_closedPointPolynomial
    (p n : ℕ) [Fact p.Prime]
    (z : HarcosClosedPointRoot p n) :
    minpoly (ZMod p) z.2.1 = z.1.1.1.1 := by
  symm
  exact minpoly.eq_of_irreducible_of_monic z.1.1.1.2.1
    (z.1.1.1.2.2.mem_rootSet.mp z.2.2) z.1.1.1.2.2

theorem finrank_adjoin_closedPointRoot_eq_div
    (p n : ℕ) [Fact p.Prime] (hn : n ≠ 0)
    (z : HarcosClosedPointRoot p n) :
    Module.finrank (IntermediateField.adjoin (ZMod p) {z.2.1})
        (GaloisField p n) =
      n / z.1.1.1.1.natDegree := by
  have hmul := Module.finrank_mul_finrank (ZMod p)
    (IntermediateField.adjoin (ZMod p) {z.2.1}) (GaloisField p n)
  rw [IntermediateField.adjoin.finrank
      (Algebra.IsIntegral.isIntegral z.2.1),
    minpoly_eq_closedPointPolynomial p n z,
    GaloisField.finrank p hn] at hmul
  exact Nat.eq_div_of_mul_eq_right
    (harcosPrimeUpTo_degree_pos p n z.1.1).ne' hmul

theorem trace_closedPointRoot
    (p n : ℕ) [Fact p.Prime] (hn : n ≠ 0)
    (z : HarcosClosedPointRoot p n) :
    Algebra.trace (ZMod p) (GaloisField p n) z.2.1 =
      (n / z.1.1.1.1.natDegree) •
        (-z.1.1.1.1.nextCoeff) := by
  rw [trace_eq_finrank_mul_minpoly_nextCoeff,
    minpoly_eq_closedPointPolynomial p n z,
    finrank_adjoin_closedPointRoot_eq_div p n hn z]
  simp [nsmul_eq_mul]

theorem trace_closedPointRoot_inv
    (p n : ℕ) [Fact p.Prime] (hn : n ≠ 0)
    (z : HarcosClosedPointRoot p n) (hz : z.2.1 ≠ 0) :
    Algebra.trace (ZMod p) (GaloisField p n) z.2.1⁻¹ =
      (n / z.1.1.1.1.natDegree) •
        (-(z.1.1.1.1.coeff 1 / z.1.1.1.1.coeff 0)) := by
  rw [trace_inv_eq_finrank_mul_coeff_one_div_coeff_zero z.2.1 hz,
    minpoly_eq_closedPointPolynomial p n z,
    finrank_adjoin_closedPointRoot_eq_div p n hn z]
  simp [nsmul_eq_mul]

theorem trace_closedPointPhase
    (p n : ℕ) [Fact p.Prime] (hn : n ≠ 0)
    (a b : ZMod p) (z : HarcosClosedPointRoot p n)
    (hz : z.2.1 ≠ 0) :
    Algebra.trace (ZMod p) (GaloisField p n)
        (algebraMap (ZMod p) (GaloisField p n) a * z.2.1 +
          algebraMap (ZMod p) (GaloisField p n) b * z.2.1⁻¹) =
      (n / z.1.1.1.1.natDegree) •
        (-a * z.1.1.1.1.nextCoeff -
          b * (z.1.1.1.1.coeff 1 / z.1.1.1.1.coeff 0)) := by
  rw [← Algebra.smul_def a z.2.1, ← Algebra.smul_def b z.2.1⁻¹]
  rw [map_add, map_smul, map_smul,
    trace_closedPointRoot p n hn z,
    trace_closedPointRoot_inv p n hn z hz]
  simp [Algebra.smul_def]
  ring

theorem harcosEta_closedPoint_pow_eq_character_of_ne_zero
    (p n : ℕ) [NeZero p] [Fact p.Prime] (hn : n ≠ 0)
    (a b : ZMod p) (z : HarcosClosedPointRoot p n)
    (hz : z.2.1 ≠ 0) :
    harcosEtaPolynomial p a b z.1.1.1.1 ^
        (n / z.1.1.1.1.natDegree) =
      ZMod.stdAddChar
        (Algebra.trace (ZMod p) (GaloisField p n)
          (algebraMap (ZMod p) (GaloisField p n) a * z.2.1 +
            algebraMap (ZMod p) (GaloisField p n) b * z.2.1⁻¹)) := by
  have hdeg : z.1.1.1.1.natDegree ≠ 0 :=
    (harcosPrimeUpTo_degree_pos p n z.1.1).ne'
  have hcoeff : z.1.1.1.1.coeff 0 ≠ 0 := by
    rw [← minpoly_eq_closedPointPolynomial p n z]
    exact minpoly.coeff_zero_ne_zero
      (Algebra.IsIntegral.isIntegral z.2.1) hz
  rw [harcosEtaPolynomial_eq_of_monic_pos p a b z.1.1.1.1
    z.1.1.1.2.2 hdeg hcoeff]
  rw [trace_closedPointPhase p n hn a b z hz]
  exact (AddChar.map_nsmul_eq_pow ZMod.stdAddChar
    (n / z.1.1.1.1.natDegree)
    (-a * z.1.1.1.1.nextCoeff -
      b * (z.1.1.1.1.coeff 1 / z.1.1.1.1.coeff 0))).symm

theorem harcosEta_closedPoint_pow_eq_zero_of_eq_zero
    (p n : ℕ) [NeZero p] [Fact p.Prime]
    (a b : ZMod p) (z : HarcosClosedPointRoot p n)
    (hz : z.2.1 = 0) :
    harcosEtaPolynomial p a b z.1.1.1.1 ^
        (n / z.1.1.1.1.natDegree) = 0 := by
  have hdegpos : 0 < z.1.1.1.1.natDegree :=
    harcosPrimeUpTo_degree_pos p n z.1.1
  have hdegle : z.1.1.1.1.natDegree ≤ n := z.1.1.2
  have hpowpos : 0 < n / z.1.1.1.1.natDegree :=
    Nat.div_pos hdegle hdegpos
  have hcoeff : z.1.1.1.1.coeff 0 = 0 := by
    have hroot := z.1.1.1.2.2.mem_rootSet.mp z.2.2
    rw [hz] at hroot
    apply (algebraMap (ZMod p) (GaloisField p n)).injective
    simpa [Polynomial.coeff_zero_eq_aeval_zero'] using hroot
  rw [harcosEtaPolynomial, if_neg hdegpos.ne', if_pos hcoeff,
    zero_pow hpowpos.ne']

/-- The `extensionKloostermanZeroExtendedSummand` definition used by the source-facing construction in `KloostermanEquationEight`. -/
noncomputable def extensionKloostermanZeroExtendedSummand
    (p n : ℕ) [Fact p.Prime] (a b : ZMod p)
    (x : GaloisField p n) : ℂ :=
  if x = 0 then 0
  else ZMod.stdAddChar
    (Algebra.trace (ZMod p) (GaloisField p n)
      (algebraMap (ZMod p) (GaloisField p n) a * x +
        algebraMap (ZMod p) (GaloisField p n) b * x⁻¹))

theorem harcosEta_closedPoint_pow_eq_zeroExtended
    (p n : ℕ) [NeZero p] [Fact p.Prime] (hn : n ≠ 0)
    (a b : ZMod p) (z : HarcosClosedPointRoot p n) :
    harcosEtaPolynomial p a b z.1.1.1.1 ^
        (n / z.1.1.1.1.natDegree) =
      extensionKloostermanZeroExtendedSummand p n a b z.2.1 := by
  by_cases hz : z.2.1 = 0
  · rw [extensionKloostermanZeroExtendedSummand, if_pos hz]
    exact harcosEta_closedPoint_pow_eq_zero_of_eq_zero p n a b z hz
  · rw [extensionKloostermanZeroExtendedSummand, if_neg hz]
    exact harcosEta_closedPoint_pow_eq_character_of_ne_zero
      p n hn a b z hz

theorem sum_zeroExtended_eq_extensionKloostermanSum
    (p n : ℕ) [Fact p.Prime] (a b : ZMod p) :
    (∑ x : GaloisField p n,
        extensionKloostermanZeroExtendedSummand p n a b x) =
      extensionKloostermanSum p n
        (algebraMap (ZMod p) (GaloisField p n) a)
        (algebraMap (ZMod p) (GaloisField p n) b) := by
  rw [Fintype.sum_eq_add_sum_subtype_ne _ (0 : GaloisField p n)]
  rw [show extensionKloostermanZeroExtendedSummand p n a b 0 = 0 by
    simp [extensionKloostermanZeroExtendedSummand]]
  simp only [zero_add]
  unfold extensionKloostermanSum
  apply Fintype.sum_equiv unitsEquivNeZero.symm
  intro x
  rw [extensionKloostermanZeroExtendedSummand, if_neg x.2]
  rfl

theorem harcosEquationTenDivisorSum_eq_closedPointSum
    (p n : ℕ) [NeZero p] [Fact p.Prime] (hn : 0 < n)
    (a b : ZMod p) :
    harcosEquationTenDivisorSum p n a b =
      ∑ z : HarcosClosedPointRoot p n,
        harcosEtaPolynomial p a b z.1.1.1.1 ^
          (n / z.1.1.1.1.natDegree) := by
  rw [harcosEquationTenDivisorSum_eq_sigma]
  calc
    (∑ z : HarcosEquationTenIndex p n,
        (z.1.1 : ℂ) * harcosEtaPolynomial p a b z.2.1.1 ^
          (n / z.1.1)) =
        ∑ q : HarcosPrimeDividingDegree p n,
          (q.1.1.1.natDegree : ℂ) *
            harcosEtaPolynomial p a b q.1.1.1 ^
              (n / q.1.1.1.natDegree) := by
      apply Fintype.sum_equiv (harcosEquationTenIndexEquiv p n hn)
      intro z
      rcases z with ⟨⟨d, hd⟩, ⟨q, hq⟩⟩
      dsimp [harcosEquationTenIndexEquiv]
      change q.1.natDegree = d at hq
      subst d
      rfl
    _ = ∑ q : HarcosPrimeDividingDegree p n,
          ∑ x : q.1.1.1.rootSet (GaloisField p n),
            harcosEtaPolynomial p a b q.1.1.1 ^
              (n / q.1.1.1.natDegree) := by
      apply Finset.sum_congr rfl
      intro q _hq
      rw [Finset.sum_const]
      change (q.1.1.1.natDegree : ℂ) *
          harcosEtaPolynomial p a b q.1.1.1 ^
            (n / q.1.1.1.natDegree) =
        Fintype.card (q.1.1.1.rootSet (GaloisField p n)) •
          harcosEtaPolynomial p a b q.1.1.1 ^
            (n / q.1.1.1.natDegree)
      rw [card_rootSet_harcosIrreducibleMonicDegree p n
        q.1.1.1.natDegree hn.ne' ⟨q.1.1, rfl⟩ q.2]
      simp [nsmul_eq_mul]
    _ = ∑ z : HarcosClosedPointRoot p n,
        harcosEtaPolynomial p a b z.1.1.1.1 ^
          (n / z.1.1.1.1.natDegree) := by
      exact (Fintype.sum_sigma'
        (fun (q : HarcosPrimeDividingDegree p n)
          (x : q.1.1.1.rootSet (GaloisField p n)) ↦
            harcosEtaPolynomial p a b q.1.1.1 ^
              (n / q.1.1.1.natDegree))).symm

/-- Harcos equation (8): the Frobenius-root power sum is the exact
extension-field Kloosterman sum. -/
theorem harcosEquationEight
    (p n : ℕ) [NeZero p] [Fact p.Prime]
    (a b : ZMod p) (ha : a ≠ 0) (hb : b ≠ 0) (hn : 0 < n) :
    -(kloostermanAlpha p a b ^ n + kloostermanBeta p a b ^ n) =
      extensionKloostermanSum p n
        (algebraMap (ZMod p) (GaloisField p n) a)
        (algebraMap (ZMod p) (GaloisField p n) b) := by
  rw [harcosEquationTen p n a b ha hb hn]
  change harcosEquationTenDivisorSum p n a b = _
  rw [harcosEquationTenDivisorSum_eq_closedPointSum p n hn a b]
  calc
    (∑ z : HarcosClosedPointRoot p n,
        harcosEtaPolynomial p a b z.1.1.1.1 ^
          (n / z.1.1.1.1.natDegree)) =
        ∑ x : GaloisField p n,
          extensionKloostermanZeroExtendedSummand p n a b x := by
      apply Fintype.sum_equiv (harcosClosedPointEquiv p n hn.ne').symm
      intro z
      exact harcosEta_closedPoint_pow_eq_zeroExtended p n hn.ne' a b z
    _ = extensionKloostermanSum p n
        (algebraMap (ZMod p) (GaloisField p n) a)
        (algebraMap (ZMod p) (GaloisField p n) b) :=
      sum_zeroExtended_eq_extensionKloostermanSum p n a b

theorem extensionKloostermanScalarSum_zero
    (p n : ℕ) [NeZero p] [Fact p.Prime] (hn : n ≠ 0)
    (c : GaloisField p n) :
    extensionKloostermanScalarSum p n c 0 = ((p ^ n - 1 : ℕ) : ℂ) := by
  unfold extensionKloostermanScalarSum
  simp only [zero_mul, AddChar.map_zero_eq_one, Finset.sum_const,
    nsmul_eq_mul, mul_one]
  have hcard : Fintype.card (GaloisField p n) = p ^ n := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card p n hn
  norm_cast
  change Fintype.card (GaloisField p n)ˣ = p ^ n - 1
  rw [Fintype.card_units, hcard]

theorem extensionKloostermanScalarSum_eq_rootPower
    (p n : ℕ) [NeZero p] [Fact p.Prime] (hn : 0 < n)
    (c : ZMod p) (hc : c ≠ 0) (m : {m : ZMod p // m ≠ 0}) :
    extensionKloostermanScalarSum p n
        (algebraMap (ZMod p) (GaloisField p n) c) m.1 =
      -(kloostermanAlpha p m.1 (m.1 * c) ^ n +
        kloostermanBeta p m.1 (m.1 * c) ^ n) := by
  rw [extensionKloostermanScalarSum_eq]
  rw [← map_mul]
  exact (harcosEquationEight p n m.1 (m.1 * c) m.2
    (mul_ne_zero m.2 hc) hn).symm

/-- Harcos equation (3), in the normalized family `S(m,mc;p)` equivalent
to the source family `S(ma,mb;p)` when `c = ab`. -/
theorem harcosEquationThree_normalized
    (p n : ℕ) [NeZero p] [Fact p.Prime] (hpodd : Odd p)
    (c : ZMod p) (hc : c ≠ 0) (hn : 0 < n) :
    ((p ^ n : ℕ) : ℂ) - 1 -
        ∑ m : {m : ZMod p // m ≠ 0},
          (kloostermanAlpha p m.1 (m.1 * c) ^ n +
            kloostermanBeta p m.1 (m.1 * c) ^ n) =
      (Nat.card (QuadraticArtinCurvePoints p
        (algebraMap (ZMod p) (GaloisField p n) c)) : ℂ) := by
  rw [card_quadraticArtinCurve_eq_scalarSums p n hpodd hn.ne'
    (algebraMap (ZMod p) (GaloisField p n) c)
    (by
      simpa only [map_zero] using
        (FaithfulSMul.algebraMap_injective (ZMod p)
          (GaloisField p n)).ne hc)]
  rw [Fintype.sum_eq_add_sum_subtype_ne _ (0 : ZMod p)]
  rw [extensionKloostermanScalarSum_zero p n hn.ne'
    (algebraMap (ZMod p) (GaloisField p n) c)]
  simp_rw [extensionKloostermanScalarSum_eq_rootPower p n hn c hc]
  have hpow : 1 ≤ p ^ n := by
    have : 0 < p ^ n := pow_pos (show 0 < p from
      (show p.Prime from Fact.out).pos) n
    omega
  rw [Nat.cast_sub hpow]
  push_cast
  rw [Finset.sum_neg_distrib]
  ring

end

end RiemannZeta.GuthMaynard
