import GafniTao.WooleyNormalFormChange

/-!
# Analytic form of Wooley equation (7.17)

The congruence work proves (7.17) after ordered-tuple expansion.  This file
identifies both sides with the literal finite Fourier averages of the source
polynomial sums.  In particular, it retains the coefficient twist
`c_y(alpha)` and the auxiliary lower-degree sum rather than replacing the
inner mean by an unrelated variable.
-/

open Finset
open scoped BigOperators ComplexConjugate

namespace GafniTao

noncomputable section

/-- Complex raw form of the product of the two even moments. -/
def wooleySourceRawMixedComplexAverage {k : ℕ}
    (leftPhi rightPhi : WooleyPolynomialSystem k)
    (q R S : ℕ) [NeZero q]
    (left right : WooleySourceSequence) : ℂ :=
  ((((q ^ k : ℕ) : ℂ))⁻¹) *
    ∑ alpha : Fin k → ZMod q,
      (wooleySourcePolynomialSum leftPhi left alpha ^ R *
        conj (wooleySourcePolynomialSum leftPhi left alpha) ^ R) *
      (wooleySourcePolynomialSum rightPhi right alpha ^ S *
        conj (wooleySourcePolynomialSum rightPhi right alpha) ^ S)

/-- The tuple phase of a pointwise product factors into the two tuple
phases. -/
theorem wooleyTuplePhase_mul {I : Type*} (s : ℕ) (f g : I → ℂ)
    (xy : WooleyFiniteTuple s I × WooleyFiniteTuple s I) :
    wooleyTuplePhase s (fun x => f x * g x) xy =
      wooleyTuplePhase s f xy * wooleyTuplePhase s g xy := by
  simp only [wooleyTuplePhase, Finset.prod_mul_distrib, map_mul]
  ring

/-- Source polynomial phases restricted to the support subtype have the
character displacement used in the equation-(7.17) tuple identity. -/
theorem wooleySource_support_tuple_pair_character
    {k q : ℕ} [NeZero q] (phi : WooleyPolynomialSystem k)
    (gamma : WooleySourceSequence) (s : ℕ)
    (alpha : Fin k → ZMod q)
    (xy : WooleySourceTuplePair s gamma) :
    wooleyTuplePhase s
        (fun n : ↑gamma.support =>
          wooleySourcePolynomialPhase phi alpha (n : ℤ)) xy =
      ∏ j, ZMod.stdAddChar
        (alpha j *
          wooleySourceTuplePolynomialDisplacement phi q s gamma xy j) := by
  simp_rw [wooleySourcePolynomialPhase_eq_pointCharacter]
  exact wooley_tuple_pair_character q k s
    (fun n : ↑gamma.support => wooleyPolynomialValue phi q (n : ℤ))
      alpha xy

/-- Exact ordered-tuple expansion of the raw mixed Fourier average. -/
theorem wooleySourceRawMixedComplexAverage_eq_tuple
    {k : ℕ} (leftPhi rightPhi : WooleyPolynomialSystem k)
    (q R S : ℕ) [NeZero q]
    (left right : WooleySourceSequence) :
    wooleySourceRawMixedComplexAverage leftPhi rightPhi q R S left right =
      ((((q ^ k : ℕ) : ℂ))⁻¹) *
        ∑ alpha : Fin k → ZMod q,
          ∑ omega : WooleySourceMixedTuple R S left right,
            wooleySourceMixedTupleCoefficient R S left right omega *
              ∏ j, ZMod.stdAddChar
                (alpha j * wooleyEquation717OriginalDisplacement
                  leftPhi rightPhi q R S left right omega j) := by
  unfold wooleySourceRawMixedComplexAverage
  apply congrArg (((((q ^ k : ℕ) : ℂ))⁻¹) * ·)
  apply Finset.sum_congr rfl
  intro alpha halpha
  unfold wooleySourcePolynomialSum
  rw [wooleySource_sum_eq_support_subtype left
      (fun n => wooleySourcePolynomialPhase leftPhi alpha n),
    wooleySource_sum_eq_support_subtype right
      (fun n => wooleySourcePolynomialPhase rightPhi alpha n),
    wooley_weighted_sum_abs_pow_expand,
    wooley_weighted_sum_abs_pow_expand,
    Finset.sum_mul_sum]
  conv_rhs => rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro leftXY hleftXY
  apply Finset.sum_congr rfl
  intro rightXY hrightXY
  rw [wooleySource_support_tuple_pair_character,
    wooleySource_support_tuple_pair_character]
  simp only [wooleySourceMixedTupleCoefficient,
    wooleyEquation717OriginalDisplacement]
  have hphase :
      (∏ j, ZMod.stdAddChar
          (alpha j * wooleySourceTuplePolynomialDisplacement
            leftPhi q R left leftXY j)) *
        (∏ j, ZMod.stdAddChar
          (alpha j * wooleySourceTuplePolynomialDisplacement
            rightPhi q S right rightXY j)) =
      ∏ j, ZMod.stdAddChar
        (alpha j *
          (wooleySourceTuplePolynomialDisplacement
              leftPhi q R left leftXY j +
            wooleySourceTuplePolynomialDisplacement
              rightPhi q S right rightXY j)) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro j hj
    rw [← AddChar.map_add_eq_mul]
    congr 1
    ring
  rw [← hphase]
  ring

/-- The raw auxiliary sum in (7.16), with the `alpha`-dependent coefficient
twist and the lower system both explicit. -/
def wooleySection7AuxiliaryRawSum {k r : ℕ}
    (leftPhi : WooleyPolynomialSystem k)
    (Psi : WooleyPolynomialSystem r)
    (left : WooleySourceSequence)
    {q qPrime : ℕ} [NeZero q] [NeZero qPrime]
    (alpha : Fin k → ZMod q) (beta : Fin r → ZMod qPrime) : ℂ :=
  ∑ n ∈ left.support,
    left n * (wooleySourcePolynomialPhase leftPhi alpha n *
      wooleySourcePolynomialPhase Psi beta n)

/-- The raw auxiliary sum is the ordinary polynomial sum of the exact
twisted coefficient sequence from (7.14)--(7.16). -/
theorem wooleySection7AuxiliaryRawSum_eq_twistedPolynomialSum
    {k r : ℕ} (leftPhi : WooleyPolynomialSystem k)
    (Psi : WooleyPolynomialSystem r) (left : WooleySourceSequence)
    {q qPrime : ℕ} [NeZero q] [NeZero qPrime]
    (alpha : Fin k → ZMod q) (beta : Fin r → ZMod qPrime) :
    wooleySection7AuxiliaryRawSum leftPhi Psi left alpha beta =
      wooleySourcePolynomialSum Psi
        (wooleySourceTwist left
          (fun n => wooleySourcePolynomialPhase leftPhi alpha n)) beta := by
  unfold wooleySection7AuxiliaryRawSum wooleySourcePolynomialSum
  rw [wooleySourceTwist_support left _
    (fun n => wooleySourcePolynomialPhase_ne_zero leftPhi alpha n)]
  apply Finset.sum_congr rfl
  intro n hn
  rw [wooleySourceTwist_apply]
  ring

/-- Raw complex double average on the right side of (7.17). -/
def wooleySourceInsertedComplexAverage {k r : ℕ}
    (leftPhi rightPhi : WooleyPolynomialSystem k)
    (Psi : WooleyPolynomialSystem r)
    (q qPrime R S : ℕ) [NeZero q] [NeZero qPrime]
    (left right : WooleySourceSequence) : ℂ :=
  ((((q ^ k : ℕ) : ℂ))⁻¹) *
    ((((qPrime ^ r : ℕ) : ℂ))⁻¹) *
      ∑ alpha : Fin k → ZMod q,
        ∑ beta : Fin r → ZMod qPrime,
          (wooleySection7AuxiliaryRawSum leftPhi Psi left alpha beta ^ R *
            conj (wooleySection7AuxiliaryRawSum
              leftPhi Psi left alpha beta) ^ R) *
          (wooleySourcePolynomialSum rightPhi right alpha ^ S *
            conj (wooleySourcePolynomialSum rightPhi right alpha) ^ S)

/-- Exact ordered-tuple expansion of the inserted double average. -/
theorem wooleySourceInsertedComplexAverage_eq_tuple
    {k r : ℕ} (leftPhi rightPhi : WooleyPolynomialSystem k)
    (Psi : WooleyPolynomialSystem r)
    (q qPrime R S : ℕ) [NeZero q] [NeZero qPrime]
    (left right : WooleySourceSequence) :
    wooleySourceInsertedComplexAverage
        leftPhi rightPhi Psi q qPrime R S left right =
      ((((q ^ k : ℕ) : ℂ))⁻¹) *
        ((((qPrime ^ r : ℕ) : ℂ))⁻¹) *
          ∑ alpha : Fin k → ZMod q,
            ∑ beta : Fin r → ZMod qPrime,
              ∑ omega : WooleySourceMixedTuple R S left right,
                wooleySourceMixedTupleCoefficient R S left right omega *
                  (∏ j, ZMod.stdAddChar
                    (alpha j * wooleyEquation717OriginalDisplacement
                      leftPhi rightPhi q R S left right omega j)) *
                  ∏ l, ZMod.stdAddChar
                    (beta l * wooleyEquation717InsertedDisplacement
                      Psi qPrime R S left right omega l) := by
  unfold wooleySourceInsertedComplexAverage
  apply congrArg
    ((((((q ^ k : ℕ) : ℂ))⁻¹) * ((((qPrime ^ r : ℕ) : ℂ))⁻¹)) * ·)
  apply Finset.sum_congr rfl
  intro alpha halpha
  apply Finset.sum_congr rfl
  intro beta hbeta
  unfold wooleySection7AuxiliaryRawSum
  unfold wooleySourcePolynomialSum
  rw [wooleySource_sum_eq_support_subtype left
      (fun n => wooleySourcePolynomialPhase leftPhi alpha n *
        wooleySourcePolynomialPhase Psi beta n),
    wooley_weighted_sum_abs_pow_expand,
    wooleySource_sum_eq_support_subtype right
      (fun n => wooleySourcePolynomialPhase rightPhi alpha n),
    wooley_weighted_sum_abs_pow_expand,
    Finset.sum_mul_sum]
  conv_rhs => rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro leftXY hleftXY
  apply Finset.sum_congr rfl
  intro rightXY hrightXY
  rw [wooleyTuplePhase_mul,
    wooleySource_support_tuple_pair_character,
    wooleySource_support_tuple_pair_character,
    wooleySource_support_tuple_pair_character]
  simp only [wooleySourceMixedTupleCoefficient,
    wooleyEquation717OriginalDisplacement,
    wooleyEquation717InsertedDisplacement]
  have hphase :
      (∏ j, ZMod.stdAddChar
          (alpha j * wooleySourceTuplePolynomialDisplacement
            leftPhi q R left leftXY j)) *
        (∏ j, ZMod.stdAddChar
          (alpha j * wooleySourceTuplePolynomialDisplacement
            rightPhi q S right rightXY j)) =
      ∏ j, ZMod.stdAddChar
        (alpha j *
          (wooleySourceTuplePolynomialDisplacement
              leftPhi q R left leftXY j +
            wooleySourceTuplePolynomialDisplacement
              rightPhi q S right rightXY j)) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro j hj
    rw [← AddChar.map_add_eq_mul]
    congr 1
    ring
  rw [← hphase]
  ring

/-- Real raw mixed average represented by the complex tuple expansion. -/
def wooleySourceRawMixedRealAverage {k : ℕ}
    (leftPhi rightPhi : WooleyPolynomialSystem k)
    (q R S : ℕ) [NeZero q]
    (left right : WooleySourceSequence) : ℝ :=
  ((((q ^ k : ℕ) : ℝ))⁻¹) *
    ∑ alpha : Fin k → ZMod q,
      ‖wooleySourcePolynomialSum leftPhi left alpha‖ ^ (2 * R) *
        ‖wooleySourcePolynomialSum rightPhi right alpha‖ ^ (2 * S)

/-- Real raw double average after insertion of the lower Fourier grid. -/
def wooleySourceInsertedRealAverage {k r : ℕ}
    (leftPhi rightPhi : WooleyPolynomialSystem k)
    (Psi : WooleyPolynomialSystem r)
    (q qPrime R S : ℕ) [NeZero q] [NeZero qPrime]
    (left right : WooleySourceSequence) : ℝ :=
  ((((q ^ k : ℕ) : ℝ))⁻¹) *
    ((((qPrime ^ r : ℕ) : ℝ))⁻¹) *
      ∑ alpha : Fin k → ZMod q,
        ∑ beta : Fin r → ZMod qPrime,
          ‖wooleySection7AuxiliaryRawSum leftPhi Psi left alpha beta‖ ^
              (2 * R) *
            ‖wooleySourcePolynomialSum rightPhi right alpha‖ ^ (2 * S)

/-- The normalized mixed average on the left side of (7.17). -/
def wooleySourceNormalizedMixedRealAverage {k : ℕ}
    (leftPhi rightPhi : WooleyPolynomialSystem k)
    (q R S : ℕ) [NeZero q]
    (left right : WooleySourceSequence) : ℝ :=
  ((((q ^ k : ℕ) : ℝ))⁻¹) *
    ∑ alpha : Fin k → ZMod q,
      ‖wooleySourceNormalizedPolynomialSum leftPhi left alpha‖ ^ (2 * R) *
        ‖wooleySourceNormalizedPolynomialSum rightPhi right alpha‖ ^ (2 * S)

/-- The normalized inserted average on the right side of (7.17).  Its inner
average is literally the lower-degree source mean `J(alpha)` from (7.18). -/
def wooleySourceInsertedNormalizedRealAverage {k r : ℕ}
    (leftPhi rightPhi : WooleyPolynomialSystem k)
    (Psi : WooleyPolynomialSystem r)
    (q qPrime R S : ℕ) [NeZero q] [NeZero qPrime]
    (left right : WooleySourceSequence) : ℝ :=
  ((((q ^ k : ℕ) : ℝ))⁻¹) *
    ∑ alpha : Fin k → ZMod q,
      wooleySourcePolynomialMean R qPrime Psi
          (wooleySourceTwist left
            (fun n => wooleySourcePolynomialPhase leftPhi alpha n)) *
        ‖wooleySourceNormalizedPolynomialSum rightPhi right alpha‖ ^ (2 * S)

theorem wooleySourceRawMixedComplexAverage_eq_ofReal
    {k : ℕ} (leftPhi rightPhi : WooleyPolynomialSystem k)
    (q R S : ℕ) [NeZero q]
    (left right : WooleySourceSequence) :
    wooleySourceRawMixedComplexAverage leftPhi rightPhi q R S left right =
      (wooleySourceRawMixedRealAverage
        leftPhi rightPhi q R S left right : ℂ) := by
  unfold wooleySourceRawMixedComplexAverage
    wooleySourceRawMixedRealAverage
  simp_rw [ford_pow_mul_conj_pow]
  simp

theorem wooleySourceInsertedComplexAverage_eq_ofReal
    {k r : ℕ} (leftPhi rightPhi : WooleyPolynomialSystem k)
    (Psi : WooleyPolynomialSystem r)
    (q qPrime R S : ℕ) [NeZero q] [NeZero qPrime]
    (left right : WooleySourceSequence) :
    wooleySourceInsertedComplexAverage
        leftPhi rightPhi Psi q qPrime R S left right =
      (wooleySourceInsertedRealAverage
        leftPhi rightPhi Psi q qPrime R S left right : ℂ) := by
  unfold wooleySourceInsertedComplexAverage
    wooleySourceInsertedRealAverage
  simp_rw [ford_pow_mul_conj_pow]
  simp

/-- Removing the source normalization from an even moment contributes the
exact `R`-th inverse power of the coefficient mass.  The zero-mass case is
kept separate, as it is in the source definitions. -/
theorem norm_wooleySourceNormalizedPolynomialSum_pow_even
    {k q : ℕ} [NeZero q]
    (phi : WooleyPolynomialSystem k) (gamma : WooleySourceSequence)
    (alpha : Fin k → ZMod q) (R : ℕ)
    (hmass : wooleySourceMassSq gamma ≠ 0) :
    ‖wooleySourceNormalizedPolynomialSum phi gamma alpha‖ ^ (2 * R) =
      (wooleySourceMassSq gamma)⁻¹ ^ R *
        ‖wooleySourcePolynomialSum phi gamma alpha‖ ^ (2 * R) := by
  unfold wooleySourceNormalizedPolynomialSum
  rw [if_neg hmass, norm_mul, norm_inv]
  have hnonneg : 0 ≤ wooleySourceMassSq gamma :=
    wooleySourceMassSq_nonneg gamma
  rw [Complex.norm_real]
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [mul_pow, pow_mul, inv_pow, Real.sq_sqrt hnonneg]

theorem wooleySourceNormalizedMixedRealAverage_eq_mass_mul_raw
    {k : ℕ} (leftPhi rightPhi : WooleyPolynomialSystem k)
    (q R S : ℕ) [NeZero q]
    (left right : WooleySourceSequence)
    (hleft : wooleySourceMassSq left ≠ 0)
    (hright : wooleySourceMassSq right ≠ 0) :
    wooleySourceNormalizedMixedRealAverage
        leftPhi rightPhi q R S left right =
      (wooleySourceMassSq left)⁻¹ ^ R *
        (wooleySourceMassSq right)⁻¹ ^ S *
          wooleySourceRawMixedRealAverage
            leftPhi rightPhi q R S left right := by
  unfold wooleySourceNormalizedMixedRealAverage
    wooleySourceRawMixedRealAverage
  simp_rw [norm_wooleySourceNormalizedPolynomialSum_pow_even
    leftPhi left _ R hleft]
  simp_rw [norm_wooleySourceNormalizedPolynomialSum_pow_even
    rightPhi right _ S hright]
  have hsum :
      (∑ alpha : Fin k → ZMod q,
          ((wooleySourceMassSq left)⁻¹ ^ R *
              ‖wooleySourcePolynomialSum leftPhi left alpha‖ ^ (2 * R)) *
            ((wooleySourceMassSq right)⁻¹ ^ S *
              ‖wooleySourcePolynomialSum rightPhi right alpha‖ ^ (2 * S))) =
        (wooleySourceMassSq left)⁻¹ ^ R *
          (wooleySourceMassSq right)⁻¹ ^ S *
            ∑ alpha : Fin k → ZMod q,
              ‖wooleySourcePolynomialSum leftPhi left alpha‖ ^ (2 * R) *
                ‖wooleySourcePolynomialSum rightPhi right alpha‖ ^ (2 * S) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro alpha halpha
    ring
  rw [hsum]
  ring

theorem wooleySourceInsertedNormalizedRealAverage_eq_mass_mul_raw
    {k r : ℕ} (leftPhi rightPhi : WooleyPolynomialSystem k)
    (Psi : WooleyPolynomialSystem r)
    (q qPrime R S : ℕ) [NeZero q] [NeZero qPrime]
    (left right : WooleySourceSequence)
    (hleft : wooleySourceMassSq left ≠ 0)
    (hright : wooleySourceMassSq right ≠ 0) :
    wooleySourceInsertedNormalizedRealAverage
        leftPhi rightPhi Psi q qPrime R S left right =
      (wooleySourceMassSq left)⁻¹ ^ R *
        (wooleySourceMassSq right)⁻¹ ^ S *
          wooleySourceInsertedRealAverage
            leftPhi rightPhi Psi q qPrime R S left right := by
  have htwist (alpha : Fin k → ZMod q) :
      wooleySourceMassSq
          (wooleySourceTwist left
            (fun n => wooleySourcePolynomialPhase leftPhi alpha n)) =
        wooleySourceMassSq left :=
    wooleySourceMassSq_twist left _
      (fun n => wooleySourcePolynomialPhase_norm leftPhi alpha n)
  have hleftNorm (alpha : Fin k → ZMod q)
      (beta : Fin r → ZMod qPrime) :
      ‖wooleySourceNormalizedPolynomialSum Psi
          (wooleySourceTwist left
            (fun n => wooleySourcePolynomialPhase leftPhi alpha n)) beta‖ ^
          (2 * R) =
        (wooleySourceMassSq left)⁻¹ ^ R *
          ‖wooleySection7AuxiliaryRawSum
            leftPhi Psi left alpha beta‖ ^ (2 * R) := by
    rw [norm_wooleySourceNormalizedPolynomialSum_pow_even]
    · rw [htwist]
      rw [← wooleySection7AuxiliaryRawSum_eq_twistedPolynomialSum]
    · rw [htwist]
      exact hleft
  unfold wooleySourceInsertedNormalizedRealAverage
    wooleySourcePolynomialMean wooleySourceInsertedRealAverage
  simp_rw [hleftNorm]
  simp_rw [norm_wooleySourceNormalizedPolynomialSum_pow_even
    rightPhi right _ S hright]
  have hsum :
      (∑ alpha : Fin k → ZMod q,
          ((↑(qPrime ^ r))⁻¹ *
            ∑ beta : Fin r → ZMod qPrime,
              (wooleySourceMassSq left)⁻¹ ^ R *
                ‖wooleySection7AuxiliaryRawSum
                  leftPhi Psi left alpha beta‖ ^ (2 * R)) *
            ((wooleySourceMassSq right)⁻¹ ^ S *
              ‖wooleySourcePolynomialSum rightPhi right alpha‖ ^ (2 * S))) =
        (wooleySourceMassSq left)⁻¹ ^ R *
          (wooleySourceMassSq right)⁻¹ ^ S *
            ((↑(qPrime ^ r))⁻¹ *
              ∑ alpha : Fin k → ZMod q,
                ∑ beta : Fin r → ZMod qPrime,
                  ‖wooleySection7AuxiliaryRawSum
                    leftPhi Psi left alpha beta‖ ^ (2 * R) *
                    ‖wooleySourcePolynomialSum rightPhi right alpha‖ ^
                      (2 * S)) := by
    calc
      _ = ∑ alpha : Fin k → ZMod q,
          (wooleySourceMassSq left)⁻¹ ^ R *
            (wooleySourceMassSq right)⁻¹ ^ S *
              ((↑(qPrime ^ r))⁻¹ *
                ∑ beta : Fin r → ZMod qPrime,
                  ‖wooleySection7AuxiliaryRawSum
                    leftPhi Psi left alpha beta‖ ^ (2 * R) *
                    ‖wooleySourcePolynomialSum rightPhi right alpha‖ ^
                      (2 * S)) := by
            apply Finset.sum_congr rfl
            intro alpha halpha
            rw [← Finset.mul_sum]
            rw [← Finset.sum_mul]
            ring
      _ = _ := by
        calc
          _ = (wooleySourceMassSq left)⁻¹ ^ R *
              (wooleySourceMassSq right)⁻¹ ^ S *
                ∑ alpha : Fin k → ZMod q,
                  ((↑(qPrime ^ r))⁻¹ : ℝ) *
                    ∑ beta : Fin r → ZMod qPrime,
                      ‖wooleySection7AuxiliaryRawSum
                        leftPhi Psi left alpha beta‖ ^ (2 * R) *
                        ‖wooleySourcePolynomialSum
                          rightPhi right alpha‖ ^ (2 * S) :=
            (Finset.mul_sum
              (Finset.univ : Finset (Fin k → ZMod q))
              (fun alpha =>
                ((↑(qPrime ^ r))⁻¹ : ℝ) *
                  ∑ beta : Fin r → ZMod qPrime,
                    ‖wooleySection7AuxiliaryRawSum
                      leftPhi Psi left alpha beta‖ ^ (2 * R) *
                      ‖wooleySourcePolynomialSum rightPhi right alpha‖ ^
                        (2 * S))
              ((wooleySourceMassSq left)⁻¹ ^ R *
                (wooleySourceMassSq right)⁻¹ ^ S)).symm
          _ = _ := by
            congr 1
            exact (Finset.mul_sum
              (Finset.univ : Finset (Fin k → ZMod q))
              (fun alpha =>
                ∑ beta : Fin r → ZMod qPrime,
                  ‖wooleySection7AuxiliaryRawSum
                    leftPhi Psi left alpha beta‖ ^ (2 * R) *
                    ‖wooleySourcePolynomialSum rightPhi right alpha‖ ^
                      (2 * S))
              ((↑(qPrime ^ r))⁻¹ : ℝ)).symm
  rw [hsum]
  ring

/-- Analytic equality (7.17) obtained from the source-spaced congruence
argument, before normalization by the two residue masses. -/
theorem wooley_equation_7_17_raw_native
    {k r p c a b B nu R S gamma : ℕ}
    [NeZero (p ^ B)]
    [NeZero (p ^ wooleySection7BPrimeNat k r a b gamma)]
    (hpPrime : p.Prime) (hc : 1 ≤ c) (hr : 1 ≤ r)
    (hrk : r < k) (hkp : k < p)
    (hMB : (k - r + 1) * b ≤ B)
    (hgammaK : gamma * k ≤ a)
    (hBPrime : (nu : ℤ) < wooleySection7BPrimeInt k r a b gamma)
    (omegaVal h : ℤ) (homega : omegaVal ≠ 0)
    (hcop : Nat.Coprime p omegaVal.natAbs)
    (hsep : h = omegaVal * (p : ℤ) ^ gamma) (hh : h ≠ 0)
    (phi : WooleyPolynomialSystem k) (hphi : phi.Spaced p c)
    (left right : WooleySourceSequence) :
    ∃ Psi : WooleyPolynomialSystem r,
      Psi.Spaced p (a - (k - r) * gamma) ∧
      wooleySourceRawMixedComplexAverage
          (wooleySection7LeftFourierSystemOf phi p a h)
          (wooleySection7RightPositiveFourierSystemOf phi p b)
          (p ^ B) R S left right =
        wooleySourceInsertedComplexAverage
          (wooleySection7LeftFourierSystemOf phi p a h)
          (wooleySection7RightPositiveFourierSystemOf phi p b)
          Psi (p ^ B)
          (p ^ wooleySection7BPrimeNat k r a b gamma)
          R S left right := by
  obtain ⟨Psi, hPsi, h717⟩ :=
    wooley_equation_7_17_spaced_positive_native
      hpPrime hc hr hrk hkp hMB hgammaK hBPrime
        omegaVal h homega hcop hsep hh phi hphi left right
  refine ⟨Psi, hPsi, ?_⟩
  rw [wooleySourceRawMixedComplexAverage_eq_tuple,
    wooleySourceInsertedComplexAverage_eq_tuple]
  exact h717

/-- Real form of equation (7.17), still before residue-mass normalization. -/
theorem wooley_equation_7_17_raw_real_native
    {k r p c a b B nu R S gamma : ℕ}
    [NeZero (p ^ B)]
    [NeZero (p ^ wooleySection7BPrimeNat k r a b gamma)]
    (hpPrime : p.Prime) (hc : 1 ≤ c) (hr : 1 ≤ r)
    (hrk : r < k) (hkp : k < p)
    (hMB : (k - r + 1) * b ≤ B)
    (hgammaK : gamma * k ≤ a)
    (hBPrime : (nu : ℤ) < wooleySection7BPrimeInt k r a b gamma)
    (omegaVal h : ℤ) (homega : omegaVal ≠ 0)
    (hcop : Nat.Coprime p omegaVal.natAbs)
    (hsep : h = omegaVal * (p : ℤ) ^ gamma) (hh : h ≠ 0)
    (phi : WooleyPolynomialSystem k) (hphi : phi.Spaced p c)
    (left right : WooleySourceSequence) :
    ∃ Psi : WooleyPolynomialSystem r,
      Psi.Spaced p (a - (k - r) * gamma) ∧
      wooleySourceRawMixedRealAverage
          (wooleySection7LeftFourierSystemOf phi p a h)
          (wooleySection7RightPositiveFourierSystemOf phi p b)
          (p ^ B) R S left right =
        wooleySourceInsertedRealAverage
          (wooleySection7LeftFourierSystemOf phi p a h)
          (wooleySection7RightPositiveFourierSystemOf phi p b)
          Psi (p ^ B)
          (p ^ wooleySection7BPrimeNat k r a b gamma)
          R S left right := by
  obtain ⟨Psi, hPsi, hraw⟩ := wooley_equation_7_17_raw_native
    hpPrime hc hr hrk hkp hMB hgammaK hBPrime
      omegaVal h homega hcop hsep hh phi hphi left right
  refine ⟨Psi, hPsi, ?_⟩
  apply Complex.ofReal_injective
  rw [← wooleySourceRawMixedComplexAverage_eq_ofReal,
    ← wooleySourceInsertedComplexAverage_eq_ofReal]
  exact hraw

/-- Normalized source form of equation (7.17), equivalently (7.18), for the
nonzero residue-mass branch.  Zero residue masses are eliminated by the
outer mass weights when this local identity is assembled into `K_{a,b}`. -/
theorem wooley_equation_7_17_normalized_nonzero_native
    {k r p c a b B nu R S gamma : ℕ}
    [NeZero (p ^ B)]
    [NeZero (p ^ wooleySection7BPrimeNat k r a b gamma)]
    (hpPrime : p.Prime) (hc : 1 ≤ c) (hr : 1 ≤ r)
    (hrk : r < k) (hkp : k < p)
    (hMB : (k - r + 1) * b ≤ B)
    (hgammaK : gamma * k ≤ a)
    (hBPrime : (nu : ℤ) < wooleySection7BPrimeInt k r a b gamma)
    (omegaVal h : ℤ) (homega : omegaVal ≠ 0)
    (hcop : Nat.Coprime p omegaVal.natAbs)
    (hsep : h = omegaVal * (p : ℤ) ^ gamma) (hh : h ≠ 0)
    (phi : WooleyPolynomialSystem k) (hphi : phi.Spaced p c)
    (left right : WooleySourceSequence)
    (hleft : wooleySourceMassSq left ≠ 0)
    (hright : wooleySourceMassSq right ≠ 0) :
    ∃ Psi : WooleyPolynomialSystem r,
      Psi.Spaced p (a - (k - r) * gamma) ∧
      wooleySourceNormalizedMixedRealAverage
          (wooleySection7LeftFourierSystemOf phi p a h)
          (wooleySection7RightPositiveFourierSystemOf phi p b)
          (p ^ B) R S left right =
        wooleySourceInsertedNormalizedRealAverage
          (wooleySection7LeftFourierSystemOf phi p a h)
          (wooleySection7RightPositiveFourierSystemOf phi p b)
          Psi (p ^ B)
          (p ^ wooleySection7BPrimeNat k r a b gamma)
          R S left right := by
  obtain ⟨Psi, hPsi, hraw⟩ := wooley_equation_7_17_raw_real_native
    hpPrime hc hr hrk hkp hMB hgammaK hBPrime
      omegaVal h homega hcop hsep hh phi hphi left right
  refine ⟨Psi, hPsi, ?_⟩
  rw [wooleySourceNormalizedMixedRealAverage_eq_mass_mul_raw
    _ _ _ _ _ left right hleft hright]
  rw [wooleySourceInsertedNormalizedRealAverage_eq_mass_mul_raw
    _ _ Psi _ _ _ _ left right hleft hright]
  rw [hraw]

#print axioms wooleyTuplePhase_mul
#print axioms wooleySource_support_tuple_pair_character
#print axioms wooleySourceRawMixedComplexAverage_eq_tuple
#print axioms wooleySection7AuxiliaryRawSum_eq_twistedPolynomialSum
#print axioms wooleySourceInsertedComplexAverage_eq_tuple
#print axioms wooley_equation_7_17_raw_native
#print axioms wooleySourceRawMixedComplexAverage_eq_ofReal
#print axioms wooleySourceInsertedComplexAverage_eq_ofReal
#print axioms wooley_equation_7_17_raw_real_native
#print axioms norm_wooleySourceNormalizedPolynomialSum_pow_even
#print axioms wooleySourceNormalizedMixedRealAverage_eq_mass_mul_raw
#print axioms wooleySourceInsertedNormalizedRealAverage_eq_mass_mul_raw
#print axioms wooley_equation_7_17_normalized_nonzero_native

end

end GafniTao
