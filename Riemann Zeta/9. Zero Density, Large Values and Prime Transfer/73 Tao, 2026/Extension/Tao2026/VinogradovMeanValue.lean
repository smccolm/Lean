import Tao2026.VinogradovSharp
import Tao2026.WeylDifferencing
import RiemannZeta.GuthMaynard.ClassicalLargeValues
import GafniTao.WooleySourceCriticalBase
import GafniTao.WooleySourceToPadic
import GafniTao.WooleyPadicToCritical
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Vinogradov polynomial moments

This module begins the polynomial mean-value argument after the coefficient
selection in `Tao2026.Vinogradov`. It formalizes the first Hölder step and the
finite power-sum representation functions used to define Vinogradov's mean
value count.
-/

namespace Tao2026

open scoped BigOperators NNReal

open RiemannZeta.GuthMaynard

/-- Finite power-mean inequality in the exact form used for the first Hölder
step of Vinogradov's bilinear argument. -/
theorem norm_sum_pow_le_card_pow_mul_sum_norm_pow
    {ι : Type*} (s : Finset ι) (f : ι → ℂ) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    ‖∑ i ∈ s, f i‖ ^ ℓ ≤
      (s.card : ℝ) ^ (ℓ - 1) * ∑ i ∈ s, ‖f i‖ ^ ℓ := by
  have hnorm : ‖∑ i ∈ s, f i‖ ≤ ∑ i ∈ s, ‖f i‖ := norm_sum_le _ _
  calc
    ‖∑ i ∈ s, f i‖ ^ ℓ ≤ (∑ i ∈ s, ‖f i‖) ^ ℓ :=
      pow_le_pow_left₀ (norm_nonneg _) hnorm ℓ
    _ ≤ (s.card : ℝ) ^ (ℓ - 1) * ∑ i ∈ s, ‖f i‖ ^ ℓ := by
      have h := pow_sum_le_card_mul_sum_pow
        (s := s) (f := fun i => ‖f i‖) (fun _ _ => norm_nonneg _) (ℓ - 1)
      simpa only [Nat.sub_add_cancel hℓ] using h

/-- The inner `y`-sum of the generic diagonal bilinear polynomial sum. -/
noncomputable def vinogradovBilinearPolynomialInnerSum
    (c : ℕ → ℝ) (R V x : ℕ) : ℂ :=
  ∑ y ∈ Finset.Icc 1 V, standardAdditiveCharacter
    (∑ r ∈ Finset.range R, c (r + 1) * x ^ (r + 1) * y ^ (r + 1))

/-- The generic bilinear sum is the outer sum of its polynomial inner sums. -/
theorem vinogradovBilinearPolynomialSum_eq_sum_inner
    (c : ℕ → ℝ) (R V : ℕ) :
    vinogradovBilinearPolynomialSum c R V =
      ∑ x ∈ Finset.Icc 1 V, vinogradovBilinearPolynomialInnerSum c R V x := by
  rfl

/-- First Hölder step for the unnormalized bilinear polynomial sum. -/
theorem norm_vinogradovBilinearPolynomialSum_pow_le_firstMoment
    (c : ℕ → ℝ) (R V ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    ‖vinogradovBilinearPolynomialSum c R V‖ ^ ℓ ≤
      (V : ℝ) ^ (ℓ - 1) *
        ∑ x ∈ Finset.Icc 1 V,
          ‖vinogradovBilinearPolynomialInnerSum c R V x‖ ^ ℓ := by
  rw [vinogradovBilinearPolynomialSum_eq_sum_inner]
  have h := norm_sum_pow_le_card_pow_mul_sum_norm_pow
    (Finset.Icc 1 V) (vinogradovBilinearPolynomialInnerSum c R V) hℓ
  simpa using h

/-- The vector `(x,x²,…,xᴿ)` on the integer polynomial moment curve. -/
def vinogradovPolynomialCurve (R : ℕ) (x : ℕ) : Fin R → ℤ :=
  fun j => (x : ℤ) ^ (j.1 + 1)

/-- Sum of `ℓ` polynomial-curve vectors associated to an `ℓ`-tuple from
`{1,…,V}` (represented internally by `Fin V`). -/
def vinogradovTuplePowerSum {ℓ V : ℕ} (R : ℕ)
    (x : Fin ℓ → Fin V) : Fin R → ℤ :=
  fun j => ∑ i, (((x i).1 + 1 : ℕ) : ℤ) ^ (j.1 + 1)

/-- Finite set of power-sum vectors represented by `ℓ`-tuples. -/
def vinogradovPowerSumSupport (ℓ R V : ℕ) : Finset (Fin R → ℤ) :=
  Finset.univ.image (vinogradovTuplePowerSum (ℓ := ℓ) (V := V) R)

/-- Multiplicity of a power-sum vector among `ℓ`-tuples. -/
def vinogradovRepresentationCount (ℓ R V : ℕ) (u : Fin R → ℤ) : ℕ :=
  (Finset.univ.filter fun x : Fin ℓ → Fin V =>
    vinogradovTuplePowerSum R x = u).card

/-- Vinogradov's mean-value count, expressed directly as the number of pairs
of `ℓ`-tuples having the same first `R` power sums. -/
def vinogradovMeanValueCount (ℓ R V : ℕ) : ℕ :=
  ∑ u ∈ vinogradovPowerSumSupport ℓ R V,
    (vinogradovRepresentationCount ℓ R V u) ^ 2

@[simp]
theorem mem_vinogradovPowerSumSupport {ℓ R V : ℕ} {u : Fin R → ℤ} :
    u ∈ vinogradovPowerSumSupport ℓ R V ↔
      ∃ x : Fin ℓ → Fin V, vinogradovTuplePowerSum R x = u := by
  classical
  simp [vinogradovPowerSumSupport]

/-- Summing all representation multiplicities recovers the number `V^ℓ` of
source tuples. This is equation (14) of the moment argument. -/
theorem sum_vinogradovRepresentationCount (ℓ R V : ℕ) :
    ∑ u ∈ vinogradovPowerSumSupport ℓ R V,
      vinogradovRepresentationCount ℓ R V u = V ^ ℓ := by
  classical
  unfold vinogradovPowerSumSupport vinogradovRepresentationCount
  rw [← Finset.card_eq_sum_card_image]
  simp

/-- Equation (15): the second moment of the representation function is the
Vinogradov mean-value count. -/
theorem sum_sq_vinogradovRepresentationCount (ℓ R V : ℕ) :
    ∑ u ∈ vinogradovPowerSumSupport ℓ R V,
      (vinogradovRepresentationCount ℓ R V u) ^ 2 =
        vinogradovMeanValueCount ℓ R V := by
  rfl

/-- Finite solution set for the Vinogradov system of equal power sums. -/
def vinogradovMeanValueSolutions (ℓ R V : ℕ) :
    Finset ((Fin ℓ → Fin V) × (Fin ℓ → Fin V)) :=
  (Finset.univ ×ˢ Finset.univ).filter fun p =>
    vinogradovTuplePowerSum R p.1 = vinogradovTuplePowerSum R p.2

/-- The representation-function second moment equals the number of solutions
to the system of equal power sums. This is equation (17). -/
theorem card_vinogradovMeanValueSolutions_eq_meanValueCount (ℓ R V : ℕ) :
    (vinogradovMeanValueSolutions ℓ R V).card =
      vinogradovMeanValueCount ℓ R V := by
  classical
  unfold vinogradovMeanValueSolutions
  rw [Finset.card_filter, Finset.sum_product]
  have hinner : ∀ x : Fin ℓ → Fin V,
      (∑ y : Fin ℓ → Fin V,
        if vinogradovTuplePowerSum R x = vinogradovTuplePowerSum R y
        then 1 else 0) =
      vinogradovRepresentationCount ℓ R V (vinogradovTuplePowerSum R x) := by
    intro x
    unfold vinogradovRepresentationCount
    rw [Finset.card_filter]
    apply Finset.sum_congr rfl
    intro y _
    by_cases h : vinogradovTuplePowerSum R y = vinogradovTuplePowerSum R x
    · rw [if_pos h.symm, if_pos h]
    · have h' : ¬vinogradovTuplePowerSum R x = vinogradovTuplePowerSum R y :=
        fun h' => h h'.symm
      rw [if_neg h', if_neg h]
  simp_rw [hinner]
  unfold vinogradovMeanValueCount vinogradovPowerSumSupport
  rw [← Finset.sum_fiberwise_of_maps_to
    (s := (Finset.univ : Finset (Fin ℓ → Fin V)))
    (t := Finset.univ.image (vinogradovTuplePowerSum R))
    (g := vinogradovTuplePowerSum R)
    (fun x hx => Finset.mem_image_of_mem _ hx)
    (fun x => vinogradovRepresentationCount ℓ R V
      (vinogradovTuplePowerSum R x))]
  apply Finset.sum_congr rfl
  intro u hu
  have hconst : ∀ x ∈ (Finset.univ.filter fun x : Fin ℓ → Fin V =>
      vinogradovTuplePowerSum R x = u),
      vinogradovRepresentationCount ℓ R V (vinogradovTuplePowerSum R x) =
        vinogradovRepresentationCount ℓ R V u := by
    intro x hx
    rw [Finset.mem_filter] at hx
    rw [hx.2]
  rw [Finset.sum_const_nat hconst]
  change vinogradovRepresentationCount ℓ R V u *
      vinogradovRepresentationCount ℓ R V u =
    vinogradovRepresentationCount ℓ R V u ^ 2
  rw [pow_two]

/-- At side length one there is exactly one tuple pair, in every degree and
at every moment. -/
theorem vinogradovMeanValueCount_one (ℓ R : ℕ) :
    vinogradovMeanValueCount ℓ R 1 = 1 := by
  classical
  rw [← card_vinogradovMeanValueSolutions_eq_meanValueCount]
  unfold vinogradovMeanValueSolutions
  rw [show (Finset.univ ×ˢ Finset.univ).filter (fun p :
      (Fin ℓ → Fin 1) × (Fin ℓ → Fin 1) =>
        vinogradovTuplePowerSum R p.1 = vinogradovTuplePowerSum R p.2) =
      {default} by
    ext p
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
      true_and, Finset.mem_singleton]
    constructor
    · intro _
      exact Subsingleton.elim _ _
    · intro hp
      subst p
      rfl]
  simp

/-- The native Wooley development in the frozen dependency proves the full
Vinogradov main conjecture, without adding a project axiom. -/
theorem nativeHeathBrownVMVTMainConjecture :
    GafniTao.HeathBrownVMVTMainConjecture :=
  GafniTao.heathBrownVMVTMainConjecture_of_wooleyPadic
    (GafniTao.wooleyMonomialPadicConcentration_of_polynomialCorollary32
      GafniTao.wooleyPolynomialCorollary32_native)

/-- The local equation-(17) count is definitionally the same finite
Vinogradov moment used by the frozen Gafni--Tao development. -/
theorem vinogradovMeanValueCount_eq_fordVinogradovMomentNat
    (ℓ R V : ℕ) :
    vinogradovMeanValueCount ℓ R V =
      GafniTao.fordVinogradovMomentNat ℓ R V := by
  rw [← card_vinogradovMeanValueSolutions_eq_meanValueCount]
  unfold vinogradovMeanValueSolutions GafniTao.fordVinogradovMomentNat
    GafniTao.fordVinogradovShiftedCountNat GafniTao.fordRepresentationCount
  congr 1
  ext xy
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and,
    sub_eq_zero]
  rfl

/-- Any frozen Ford-form moment estimate transfers verbatim to the local
mean-value count. -/
theorem vinogradovMeanValueCount_le_of_fordVinogradovMomentBound
    {ℓ R : ℕ} {C δ : ℝ}
    (hmoment : GafniTao.FordVinogradovMomentBound ℓ R C δ)
    (V : ℕ) (hV : 1 ≤ V) :
    (vinogradovMeanValueCount ℓ R V : ℝ) ≤
      C * (V : ℝ) ^ GafniTao.fordLambda34 ℓ R δ := by
  rw [vinogradovMeanValueCount_eq_fordVinogradovMomentNat]
  exact hmoment V hV

/-- Native critical VMVT in the exact local count notation and with its
critical exponent simplified. -/
theorem native_critical_vinogradovMeanValueCount_bound
    {R : ℕ} (hR : 1 ≤ R) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ V : ℕ, 1 ≤ V →
      (vinogradovMeanValueCount (GafniTao.fordVinogradovKappa R) R V : ℝ) ≤
        C * (V : ℝ) ^ ((GafniTao.fordVinogradovKappa R : ℕ) + ε) := by
  obtain ⟨C, hC, hmoment⟩ := nativeHeathBrownVMVTMainConjecture R
    (GafniTao.fordVinogradovKappa R) ε hR (by rfl) hε
  refine ⟨C, hC, fun V hV => ?_⟩
  have hbound := vinogradovMeanValueCount_le_of_fordVinogradovMomentBound
    hmoment V hV
  simpa only [GafniTao.fordLambda34_critical] using hbound

/-- The critical Vinogradov moment is exactly half the sum of the first `R`
degrees. This division-free form is convenient for exponent cancellation. -/
theorem two_mul_fordVinogradovKappa (R : ℕ) :
    2 * GafniTao.fordVinogradovKappa R = R * (R + 1) := by
  unfold GafniTao.fordVinogradovKappa
  exact Nat.two_mul_div_two_of_even (Nat.even_mul_succ_self R)

/-- At the critical moment, the four positive `V`-power contributions in
equation (18) sum to `4*ell^2`: the first Hölder factor, the representation
factor, the two critical VMVT bounds, and the coordinate-box volume. -/
theorem critical_vinogradov_power_exponent_identity
    (R : ℕ) (hR : 1 ≤ R) :
    let ell := GafniTao.fordVinogradovKappa R
    (ell - 1) * (2 * ell) + ell * (2 * ell - 2) + 2 * ell + R * (R + 1) =
      4 * ell ^ 2 := by
  dsimp only
  have hk := two_mul_fordVinogradovKappa R
  have hell : 1 ≤ GafniTao.fordVinogradovKappa R := by
    have hproduct : 2 ≤ R * (R + 1) := by
      calc
        2 ≤ R * 2 := by omega
        _ ≤ R * (R + 1) := Nat.mul_le_mul_left R (by omega)
    rw [← hk] at hproduct
    omega
  rw [← hk]
  let K := GafniTao.fordVinogradovKappa R
  change (K - 1) * (2 * K) + K * (2 * K - 2) + 2 * K + 2 * K = 4 * K ^ 2
  have hKsub : K - 1 + 1 = K := by omega
  have h2Ksub : 2 * K - 2 + 2 = 2 * K := by omega
  have hfirst : (K - 1) * (2 * K) + 2 * K = K * (2 * K) := by
    calc
      (K - 1) * (2 * K) + 2 * K = (K - 1 + 1) * (2 * K) := by ring
      _ = K * (2 * K) := by rw [hKsub]
  have hsecond : K * (2 * K - 2) + 2 * K = K * (2 * K) := by
    calc
      K * (2 * K - 2) + 2 * K = K * (2 * K - 2 + 2) := by ring
      _ = K * (2 * K) := by rw [h2Ksub]
  calc
    (K - 1) * (2 * K) + K * (2 * K - 2) + 2 * K + 2 * K =
        ((K - 1) * (2 * K) + 2 * K) +
          (K * (2 * K - 2) + 2 * K) := by ring
    _ = K * (2 * K) + K * (2 * K) := by rw [hfirst, hsecond]
    _ = 4 * K ^ 2 := by ring

/-- Real-power normalization of the critical exponent ledger. The two
critical mean-value factors contribute `C^2`; all powers of `V` combine into
the normalized exponent `4*ell^2 + 2*ε - δ`. -/
theorem critical_vinogradov_power_rpow_identity
    (R V : ℕ) (hV : 1 ≤ V) (C A ε δ : ℝ) (K : ℕ)
    (hid : (K - 1) * (2 * K) + K * (2 * K - 2) + 2 * K + R * (R + 1) =
      4 * K ^ 2) :
    (V : ℝ) ^ ((K - 1) * (2 * K)) *
        ((((V ^ K : ℕ) : ℝ) ^ (2 * K - 2) *
          (C * (V : ℝ) ^ ((K : ℕ) + ε)) *
            ((C * (V : ℝ) ^ ((K : ℕ) + ε)) *
              ((V : ℝ) ^ (-δ) * (A * (V : ℝ) ^ (R * (R + 1))))))) =
      C ^ 2 * A * (V : ℝ) ^ ((4 * K ^ 2 : ℕ) + 2 * ε - δ) := by
  have hVpos : (0 : ℝ) < V := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hV)
  rw [show (((V ^ K : ℕ) : ℝ)) = (V : ℝ) ^ K by norm_cast]
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul hVpos.le]
  have hmoment :
      ((V : ℝ) ^ ((K : ℕ) + ε)) ^ 2 =
        (V : ℝ) ^ (2 * ((K : ℕ) + ε)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hVpos.le]
    congr 1
    ring
  ring_nf
  rw [hmoment]
  have hpowers :
      (V : ℝ) ^ (((K - 1) * (2 * K) : ℕ) : ℝ) *
          (V : ℝ) ^ ((K : ℝ) * ((2 * K - 2 : ℕ) : ℝ)) *
          (V : ℝ) ^ (2 * ((K : ℝ) + ε)) *
          (V : ℝ) ^ (-δ) *
          (V : ℝ) ^ ((R * (R + 1) : ℕ) : ℝ) =
        (V : ℝ) ^ (((4 * K ^ 2 : ℕ) : ℝ) + 2 * ε - δ) := by
    repeat' rw [← Real.rpow_add hVpos]
    congr 1
    have hidReal :
        (((K - 1) * (2 * K) : ℕ) : ℝ) +
          ((K * (2 * K - 2) : ℕ) : ℝ) + (2 * K : ℕ) +
            ((R * (R + 1) : ℕ) : ℝ) = ((4 * K ^ 2 : ℕ) : ℝ) := by
      exact_mod_cast hid
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
      at hidReal ⊢
    linarith
  ring_nf at hpowers
  convert congrArg (fun z : ℝ => C ^ 2 * A * z) hpowers using 1
  all_goals ring_nf

/-- Difference of the power-sum vectors associated to two `ℓ`-tuples. -/
def vinogradovTuplePowerDifference {ℓ V : ℕ} (R : ℕ)
    (p : (Fin ℓ → Fin V) × (Fin ℓ → Fin V)) : Fin R → ℤ :=
  fun j => vinogradovTuplePowerSum R p.1 j - vinogradovTuplePowerSum R p.2 j

/-- Finite support of the difference representation function appearing when
the linearized `2ℓ`-moment is expanded. -/
def vinogradovPowerDifferenceSupport (ℓ R V : ℕ) : Finset (Fin R → ℤ) :=
  ((Finset.univ : Finset (Fin ℓ → Fin V)) ×ˢ
    (Finset.univ : Finset (Fin ℓ → Fin V))).image
      (vinogradovTuplePowerDifference R)

/-- Number of pairs of `ℓ`-tuples representing a given power-sum
difference. -/
def vinogradovDifferenceRepresentationCount
    (ℓ R V : ℕ) (d : Fin R → ℤ) : ℕ :=
  (((Finset.univ : Finset (Fin ℓ → Fin V)) ×ˢ
      (Finset.univ : Finset (Fin ℓ → Fin V))).filter fun p :
      (Fin ℓ → Fin V) × (Fin ℓ → Fin V) =>
    vinogradovTuplePowerDifference R p = d).card

@[simp]
theorem mem_vinogradovPowerDifferenceSupport {ℓ R V : ℕ} {d : Fin R → ℤ} :
    d ∈ vinogradovPowerDifferenceSupport ℓ R V ↔
      ∃ p : (Fin ℓ → Fin V) × (Fin ℓ → Fin V),
        vinogradovTuplePowerDifference R p = d := by
  classical
  simp [vinogradovPowerDifferenceSupport]

/-- The total multiplicity of all power-sum differences is the number of
ordered pairs of source tuples. -/
theorem sum_vinogradovDifferenceRepresentationCount (ℓ R V : ℕ) :
    ∑ d ∈ vinogradovPowerDifferenceSupport ℓ R V,
      vinogradovDifferenceRepresentationCount ℓ R V d = (V ^ ℓ) ^ 2 := by
  classical
  unfold vinogradovPowerDifferenceSupport vinogradovDifferenceRepresentationCount
  rw [← Finset.card_eq_sum_card_image]
  simp [pow_two]

theorem vinogradovTuplePowerSum_nonneg {ℓ R V : ℕ}
    (x : Fin ℓ → Fin V) (j : Fin R) :
    0 ≤ vinogradovTuplePowerSum R x j := by
  unfold vinogradovTuplePowerSum
  exact Finset.sum_nonneg fun _ _ => by positivity

/-- Each coordinate of an `ℓ`-fold curve sum lies below its natural box
side length. -/
theorem vinogradovTuplePowerSum_le {ℓ R V : ℕ}
    (x : Fin ℓ → Fin V) (j : Fin R) :
    vinogradovTuplePowerSum R x j ≤ (ℓ * V ^ (j.1 + 1) : ℕ) := by
  unfold vinogradovTuplePowerSum
  calc
    (∑ i, (((x i).1 + 1 : ℕ) : ℤ) ^ (j.1 + 1)) ≤
        ∑ _i : Fin ℓ, (V : ℤ) ^ (j.1 + 1) := by
      apply Finset.sum_le_sum
      intro i hi
      exact_mod_cast Nat.pow_le_pow_left (show (x i).1 + 1 ≤ V by omega) _
    _ = (ℓ * V ^ (j.1 + 1) : ℕ) := by simp

/-- The difference support is contained in Tao's symmetric box
`|d_j| ≤ ℓ V^(j+1)`. -/
theorem abs_vinogradovTuplePowerDifference_le {ℓ R V : ℕ}
    (p : (Fin ℓ → Fin V) × (Fin ℓ → Fin V)) (j : Fin R) :
    |vinogradovTuplePowerDifference R p j| ≤
      (ℓ * V ^ (j.1 + 1) : ℕ) := by
  have h₁ := vinogradovTuplePowerSum_nonneg p.1 j
  have h₂ := vinogradovTuplePowerSum_nonneg p.2 j
  have h₁' := vinogradovTuplePowerSum_le p.1 j
  have h₂' := vinogradovTuplePowerSum_le p.2 j
  unfold vinogradovTuplePowerDifference
  rw [abs_le]
  constructor <;> omega

theorem abs_le_of_mem_vinogradovPowerDifferenceSupport {ℓ R V : ℕ}
    {d : Fin R → ℤ} (hd : d ∈ vinogradovPowerDifferenceSupport ℓ R V)
    (j : Fin R) :
    |d j| ≤ (ℓ * V ^ (j.1 + 1) : ℕ) := by
  rw [mem_vinogradovPowerDifferenceSupport] at hd
  obtain ⟨p, rfl⟩ := hd
  exact abs_vinogradovTuplePowerDifference_le p j

/-- A sum of coordinatewise products over a finite product box factors as the
product of the corresponding coordinate sums. -/
theorem sum_piFinset_prod_eq_prod_sum {ι α A : Type*} [Fintype ι]
    [DecidableEq ι] [DecidableEq α] [CommSemiring A]
    (t : ι → Finset α) (f : ι → α → A) :
    (∑ x ∈ Fintype.piFinset t, ∏ i, f i (x i)) =
      ∏ i, ∑ y ∈ t i, f i y := by
  rw [Finset.prod_sum]
  unfold Fintype.piFinset
  rw [Finset.sum_map]
  apply Finset.sum_congr rfl
  intro p hp
  simp

/-- One coordinate interval of Tao's symmetric power-sum box. -/
noncomputable def vinogradovPowerBoxSide
    (ℓ V degree : ℕ) : Finset ℤ :=
  Finset.Icc (-((ℓ * V ^ degree : ℕ) : ℤ))
    ((ℓ * V ^ degree : ℕ) : ℤ)

/-- Tao's symmetric power-sum box
`|u_j| ≤ ℓ V^(j+1)` for `j = 0,…,R-1`. -/
noncomputable def vinogradovPowerBox (ℓ R V : ℕ) : Finset (Fin R → ℤ) :=
  Fintype.piFinset fun j : Fin R =>
    vinogradovPowerBoxSide ℓ V (j.1 + 1)

@[simp]
theorem mem_vinogradovPowerBox {ℓ R V : ℕ} {u : Fin R → ℤ} :
    u ∈ vinogradovPowerBox ℓ R V ↔
      ∀ j, |u j| ≤ (ℓ * V ^ (j.1 + 1) : ℕ) := by
  simp only [vinogradovPowerBox, vinogradovPowerBoxSide,
    Fintype.mem_piFinset, Finset.mem_Icc]
  constructor
  · intro h j
    rw [abs_le]
    exact h j
  · intro h j
    rw [← abs_le]
    exact h j

/-- The positive tuple power-sum support is contained in the symmetric box. -/
theorem vinogradovPowerSumSupport_subset_powerBox (ℓ R V : ℕ) :
    vinogradovPowerSumSupport ℓ R V ⊆ vinogradovPowerBox ℓ R V := by
  intro u hu
  rw [mem_vinogradovPowerSumSupport] at hu
  obtain ⟨x, rfl⟩ := hu
  rw [mem_vinogradovPowerBox]
  intro j
  rw [abs_of_nonneg (vinogradovTuplePowerSum_nonneg x j)]
  exact vinogradovTuplePowerSum_le x j

/-- The signed tuple-difference support is contained in the same symmetric
box. -/
theorem vinogradovPowerDifferenceSupport_subset_powerBox (ℓ R V : ℕ) :
    vinogradovPowerDifferenceSupport ℓ R V ⊆ vinogradovPowerBox ℓ R V := by
  intro d hd
  rw [mem_vinogradovPowerBox]
  exact abs_le_of_mem_vinogradovPowerDifferenceSupport hd

theorem vinogradovRepresentationCount_eq_zero_of_not_mem
    {ℓ R V : ℕ} {u : Fin R → ℤ}
    (hu : u ∉ vinogradovPowerSumSupport ℓ R V) :
    vinogradovRepresentationCount ℓ R V u = 0 := by
  unfold vinogradovRepresentationCount
  rw [Finset.card_eq_zero]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  rw [Finset.mem_filter] at hx
  apply hu
  rw [mem_vinogradovPowerSumSupport]
  exact ⟨x, hx.2⟩

/-- Translation cannot increase the squared mass of the representation
function, because it is zero off its finite support. -/
theorem sum_sq_shift_vinogradovRepresentationCount_le
    (ℓ R V : ℕ) (d : Fin R → ℤ) :
    ∑ u ∈ vinogradovPowerSumSupport ℓ R V,
        vinogradovRepresentationCount ℓ R V (u + d) ^ 2 ≤
      vinogradovMeanValueCount ℓ R V := by
  classical
  let S := vinogradovPowerSumSupport ℓ R V
  let T := S.filter fun u => u + d ∈ S
  have hrestrict :
      (∑ u ∈ S, vinogradovRepresentationCount ℓ R V (u + d) ^ 2) =
        ∑ u ∈ T, vinogradovRepresentationCount ℓ R V (u + d) ^ 2 := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro u huS huT
    rw [Finset.mem_filter] at huT
    have hout : u + d ∉ S := by
      intro hin
      exact huT ⟨huS, hin⟩
    rw [vinogradovRepresentationCount_eq_zero_of_not_mem hout]
    simp
  rw [hrestrict]
  have hinj : Set.InjOn (fun u : Fin R → ℤ => u + d) T := by
    intro u hu v hv huv
    exact add_right_cancel huv
  rw [← Finset.sum_image (f := fun v =>
    vinogradovRepresentationCount ℓ R V v ^ 2) hinj]
  unfold vinogradovMeanValueCount
  change ∑ v ∈ T.image (fun u => u + d),
      vinogradovRepresentationCount ℓ R V v ^ 2 ≤
    ∑ v ∈ S, vinogradovRepresentationCount ℓ R V v ^ 2
  apply Finset.sum_le_sum_of_subset
  intro v hv
  rw [Finset.mem_image] at hv
  obtain ⟨u, huT, rfl⟩ := hv
  rw [Finset.mem_filter] at huT
  exact huT.2

/-- A difference multiplicity is the additive autocorrelation of the original
representation function. -/
theorem vinogradovDifferenceRepresentationCount_eq_sum
    (ℓ R V : ℕ) (d : Fin R → ℤ) :
    vinogradovDifferenceRepresentationCount ℓ R V d =
      ∑ u ∈ vinogradovPowerSumSupport ℓ R V,
        vinogradovRepresentationCount ℓ R V u *
          vinogradovRepresentationCount ℓ R V (u + d) := by
  classical
  unfold vinogradovDifferenceRepresentationCount
  rw [Finset.card_filter, Finset.sum_product]
  rw [Finset.sum_comm]
  have hinner : ∀ b : Fin ℓ → Fin V,
      (∑ a : Fin ℓ → Fin V,
        if vinogradovTuplePowerDifference R (a, b) = d then 1 else 0) =
      vinogradovRepresentationCount ℓ R V
        (vinogradovTuplePowerSum R b + d) := by
    intro b
    unfold vinogradovRepresentationCount
    rw [Finset.card_filter]
    apply Finset.sum_congr rfl
    intro a ha
    unfold vinogradovTuplePowerDifference
    change (if vinogradovTuplePowerSum R a - vinogradovTuplePowerSum R b = d
      then 1 else 0) = _
    by_cases h : vinogradovTuplePowerSum R a - vinogradovTuplePowerSum R b = d
    · rw [if_pos h]
      rw [if_pos]
      funext j
      have hj := congr_fun h j
      simp only [Pi.sub_apply, Pi.add_apply] at hj ⊢
      omega
    · rw [if_neg h]
      rw [if_neg]
      intro h'
      apply h
      funext j
      have hj := congr_fun h' j
      simp only [Pi.add_apply, Pi.sub_apply] at hj ⊢
      omega
  simp_rw [hinner]
  rw [← Finset.sum_fiberwise_of_maps_to
    (s := (Finset.univ : Finset (Fin ℓ → Fin V)))
    (t := vinogradovPowerSumSupport ℓ R V)
    (g := vinogradovTuplePowerSum R)
    (fun b hb => by
      rw [mem_vinogradovPowerSumSupport]
      exact ⟨b, rfl⟩)
    (fun b => vinogradovRepresentationCount ℓ R V
      (vinogradovTuplePowerSum R b + d))]
  apply Finset.sum_congr rfl
  intro u hu
  rw [Finset.sum_const_nat]
  · rfl
  · intro b hb
    rw [Finset.mem_filter] at hb
    rw [hb.2]

/-- Cauchy--Schwarz bounds every signed-difference multiplicity by the
Vinogradov mean value `J`. This is the multiplicity estimate used in the
passage from equation (16) to equation (18). -/
theorem vinogradovDifferenceRepresentationCount_le_meanValueCount
    (ℓ R V : ℕ) (d : Fin R → ℤ) :
    vinogradovDifferenceRepresentationCount ℓ R V d ≤
      vinogradovMeanValueCount ℓ R V := by
  classical
  let S := vinogradovPowerSumSupport ℓ R V
  have hcauchy := Finset.sum_mul_sq_le_sq_mul_sq S
    (vinogradovRepresentationCount ℓ R V)
    (fun u => vinogradovRepresentationCount ℓ R V (u + d))
  have hsquare :
      vinogradovDifferenceRepresentationCount ℓ R V d ^ 2 ≤
        vinogradovMeanValueCount ℓ R V ^ 2 := by
    rw [vinogradovDifferenceRepresentationCount_eq_sum]
    calc
      (∑ u ∈ S, vinogradovRepresentationCount ℓ R V u *
          vinogradovRepresentationCount ℓ R V (u + d)) ^ 2 ≤
        (∑ u ∈ S, vinogradovRepresentationCount ℓ R V u ^ 2) *
          ∑ u ∈ S, vinogradovRepresentationCount ℓ R V (u + d) ^ 2 := hcauchy
      _ ≤ vinogradovMeanValueCount ℓ R V *
          vinogradovMeanValueCount ℓ R V := by
        apply Nat.mul_le_mul
        · exact le_of_eq (sum_sq_vinogradovRepresentationCount ℓ R V)
        · exact sum_sq_shift_vinogradovRepresentationCount_le ℓ R V d
      _ = vinogradovMeanValueCount ℓ R V ^ 2 := by rw [pow_two]
  exact (Nat.pow_le_pow_iff_left (by norm_num : 2 ≠ 0)).mp hsquare

/-- An even power of a complex norm is a product of a power and its
conjugate. -/
theorem complex_norm_even_pow_eq_pow_mul_star_pow (z : ℂ) (ℓ : ℕ) :
    ((‖z‖ ^ (2 * ℓ) : ℝ) : ℂ) = z ^ ℓ * star z ^ ℓ := by
  push_cast
  rw [pow_mul]
  have hsq : ((‖z‖ : ℂ) ^ 2) = ((‖z‖ ^ 2 : ℝ) : ℂ) := by norm_num
  rw [hsq]
  rw [← Complex.normSq_eq_norm_sq]
  rw [← Complex.mul_conj, mul_pow]
  rfl

/-- Expanding the even norm moment of a finite complex sum produces one term
for each ordered pair of `ℓ`-tuples. -/
theorem complex_norm_sum_even_pow_eq_sum_pair {α : Type*} [Fintype α]
    (f : α → ℂ) (ℓ : ℕ) :
    ((‖∑ x, f x‖ ^ (2 * ℓ) : ℝ) : ℂ) =
      ∑ p : (Fin ℓ → α) × (Fin ℓ → α),
        (∏ i, f (p.1 i)) * star (∏ i, f (p.2 i)) := by
  rw [complex_norm_even_pow_eq_pow_mul_star_pow]
  rw [Fintype.sum_pow]
  have hstar : star (∑ x, f x) ^ ℓ = star ((∑ x, f x) ^ ℓ) := by
    exact (map_pow (starRingEnd ℂ) _ _).symm
  rw [hstar]
  rw [Fintype.sum_pow]
  change
    (∑ p : Fin ℓ → α, ∏ i, f (p i)) *
        (starRingEnd ℂ) (∑ p : Fin ℓ → α, ∏ i, f (p i)) = _
  rw [map_sum]
  rw [Finset.sum_mul_sum]
  rw [Fintype.sum_prod_type]
  rfl

/-- Re-index a sum over `{1,…,V}` by the finite type `Fin V`. -/
theorem sum_Icc_one_eq_sum_fin {E : Type*} [AddCommMonoid E]
    (V : ℕ) (f : ℕ → E) :
    ∑ x ∈ Finset.Icc 1 V, f x = ∑ x : Fin V, f (x.1 + 1) := by
  rw [Fin.sum_univ_eq_sum_range (fun x => f (x + 1))]
  have hset : Finset.Icc 1 V =
      (Finset.range V).image (fun x => x + 1) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
    constructor
    · intro hx
      refine ⟨x - 1, by omega, by omega⟩
    · rintro ⟨y, hy, rfl⟩
      omega
  rw [hset, Finset.sum_image]
  intro x _ y _ hxy
  exact Nat.add_right_cancel hxy

/-- Diagonal bilinear form associated to the coefficient vector `c`. -/
def vinogradovCoefficientBilinearForm
    (c : ℕ → ℝ) (R : ℕ) (u v : Fin R → ℤ) : ℝ :=
  ∑ j, c (j.1 + 1) * (u j : ℝ) * (v j : ℝ)

/-- The original polynomial phase is the coefficient bilinear form evaluated
on two points of the polynomial moment curve. -/
theorem vinogradovCoefficientBilinearForm_curve_curve
    (c : ℕ → ℝ) (R x y : ℕ) :
    vinogradovCoefficientBilinearForm c R
        (vinogradovPolynomialCurve R x) (vinogradovPolynomialCurve R y) =
      ∑ r ∈ Finset.range R,
        c (r + 1) * x ^ (r + 1) * y ^ (r + 1) := by
  unfold vinogradovCoefficientBilinearForm vinogradovPolynomialCurve
  rw [Fin.sum_univ_eq_sum_range (fun r =>
    c (r + 1) * (((x : ℤ) ^ (r + 1) : ℤ) : ℝ) *
      (((y : ℤ) ^ (r + 1) : ℤ) : ℝ))]
  apply Finset.sum_congr rfl
  intro r hr
  norm_num

/-- The inner polynomial sum, re-indexed by points of the finite moment
curve. -/
theorem vinogradovBilinearPolynomialInnerSum_eq_sum_curve
    (c : ℕ → ℝ) (R V x : ℕ) :
    vinogradovBilinearPolynomialInnerSum c R V x =
      ∑ y : Fin V, standardAdditiveCharacter
        (vinogradovCoefficientBilinearForm c R
          (vinogradovPolynomialCurve R x)
          (vinogradovPolynomialCurve R (y.1 + 1))) := by
  unfold vinogradovBilinearPolynomialInnerSum
  rw [sum_Icc_one_eq_sum_fin]
  apply Finset.sum_congr rfl
  intro y hy
  rw [vinogradovCoefficientBilinearForm_curve_curve]

/-- Bilinearity in the tuple power-sum variable. -/
theorem vinogradovCoefficientBilinearForm_curve_tuplePowerSum
    (c : ℕ → ℝ) (R x : ℕ) {ℓ V : ℕ} (y : Fin ℓ → Fin V) :
    vinogradovCoefficientBilinearForm c R
        (vinogradovPolynomialCurve R x) (vinogradovTuplePowerSum R y) =
      ∑ i, vinogradovCoefficientBilinearForm c R
        (vinogradovPolynomialCurve R x)
        (vinogradovPolynomialCurve R ((y i).1 + 1)) := by
  unfold vinogradovCoefficientBilinearForm vinogradovPolynomialCurve
    vinogradovTuplePowerSum
  simp_rw [Int.cast_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mul_sum]

/-- Bilinearity in the first tuple power-sum variable. -/
theorem vinogradovCoefficientBilinearForm_tuplePowerSum_left
    (c : ℕ → ℝ) (R : ℕ) {ℓ V : ℕ} (x : Fin ℓ → Fin V)
    (u : Fin R → ℤ) :
    vinogradovCoefficientBilinearForm c R
        (vinogradovTuplePowerSum R x) u =
      ∑ i, vinogradovCoefficientBilinearForm c R
        (vinogradovPolynomialCurve R ((x i).1 + 1)) u := by
  unfold vinogradovCoefficientBilinearForm vinogradovPolynomialCurve
    vinogradovTuplePowerSum
  simp_rw [Int.cast_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mul_sum]
  rw [Finset.sum_mul]

/-- The coefficient bilinear form carries subtraction in its first variable
to subtraction of real phases. -/
theorem vinogradovCoefficientBilinearForm_sub_left
    (c : ℕ → ℝ) (R : ℕ) (a b u : Fin R → ℤ) :
    vinogradovCoefficientBilinearForm c R (a - b) u =
      vinogradovCoefficientBilinearForm c R a u -
        vinogradovCoefficientBilinearForm c R b u := by
  unfold vinogradovCoefficientBilinearForm
  simp_rw [Pi.sub_apply, Int.cast_sub]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- An additive character maps a finite real sum to the corresponding complex
product. -/
theorem standardAdditiveCharacter_sum {ι : Type*}
    (s : Finset ι) (f : ι → ℝ) :
    standardAdditiveCharacter (∑ i ∈ s, f i) =
      ∏ i ∈ s, standardAdditiveCharacter (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [standardAdditiveCharacter]
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha,
        standardAdditiveCharacter_add, ih]

/-- The additive character of the diagonal bilinear form is the product of
its coordinate characters. -/
theorem standardAdditiveCharacter_bilinearForm_eq_prod
    (c : ℕ → ℝ) (R : ℕ) (d u : Fin R → ℤ) :
    standardAdditiveCharacter (vinogradovCoefficientBilinearForm c R d u) =
      ∏ j, standardAdditiveCharacter
        (c (j.1 + 1) * (d j : ℝ) * (u j : ℝ)) := by
  unfold vinogradovCoefficientBilinearForm
  exact standardAdditiveCharacter_sum Finset.univ _

/-- The inner character sum over the full power-sum box factors by
coordinates. -/
theorem sum_powerBox_standardAdditiveCharacter_eq_prod
    (c : ℕ → ℝ) (R V ℓ : ℕ) (d : Fin R → ℤ) :
    (∑ u ∈ vinogradovPowerBox ℓ R V,
      standardAdditiveCharacter (vinogradovCoefficientBilinearForm c R d u)) =
      ∏ j : Fin R, ∑ y ∈ vinogradovPowerBoxSide ℓ V (j.1 + 1),
        standardAdditiveCharacter
          (c (j.1 + 1) * (d j : ℝ) * (y : ℝ)) := by
  simp_rw [standardAdditiveCharacter_bilinearForm_eq_prod]
  unfold vinogradovPowerBox
  exact sum_piFinset_prod_eq_prod_sum
    (fun j : Fin R => vinogradovPowerBoxSide ℓ V (j.1 + 1))
    (fun j y => standardAdditiveCharacter
      (c (j.1 + 1) * (d j : ℝ) * (y : ℝ)))

/-- The norm of an inner full-box character sum is the product of the norms
of its coordinate sums. -/
theorem norm_sum_powerBox_standardAdditiveCharacter_eq_prod
    (c : ℕ → ℝ) (R V ℓ : ℕ) (d : Fin R → ℤ) :
    ‖∑ u ∈ vinogradovPowerBox ℓ R V,
      standardAdditiveCharacter (vinogradovCoefficientBilinearForm c R d u)‖ =
      ∏ j : Fin R, ‖∑ y ∈ vinogradovPowerBoxSide ℓ V (j.1 + 1),
        standardAdditiveCharacter
          (c (j.1 + 1) * (d j : ℝ) * (y : ℝ))‖ := by
  rw [sum_powerBox_standardAdditiveCharacter_eq_prod, norm_prod]

/-- Exact factorization of the double full-box phase expression into the
one-dimensional factors used in Tao's Lemma 12. -/
theorem sum_norm_powerBox_phase_eq_prod_coordinateSums
    (c : ℕ → ℝ) (R V ℓ : ℕ) :
    (∑ d ∈ vinogradovPowerBox ℓ R V,
      ‖∑ u ∈ vinogradovPowerBox ℓ R V,
        standardAdditiveCharacter
          (vinogradovCoefficientBilinearForm c R d u)‖) =
      ∏ j : Fin R, ∑ x ∈ vinogradovPowerBoxSide ℓ V (j.1 + 1),
        ‖∑ y ∈ vinogradovPowerBoxSide ℓ V (j.1 + 1),
          standardAdditiveCharacter
            (c (j.1 + 1) * (x : ℝ) * (y : ℝ))‖ := by
  simp_rw [norm_sum_powerBox_standardAdditiveCharacter_eq_prod]
  unfold vinogradovPowerBox
  exact sum_piFinset_prod_eq_prod_sum
    (fun j : Fin R => vinogradovPowerBoxSide ℓ V (j.1 + 1))
    (fun j x => ‖∑ y ∈ vinogradovPowerBoxSide ℓ V (j.1 + 1),
      standardAdditiveCharacter
        (c (j.1 + 1) * (x : ℝ) * (y : ℝ))‖)

/-- A symmetric integer character sum is exactly an affine exponential sum
on an initial natural-number interval. -/
theorem sum_symmetric_standardAdditiveCharacter_eq_phaseExponentialSum
    (alpha : ℝ) (L : ℕ) :
    (∑ y ∈ Finset.Icc (-(L : ℤ)) (L : ℤ),
      standardAdditiveCharacter (alpha * (y : ℝ))) =
      phaseExponentialSum
        (fun n => (n : ℝ) * alpha - (L : ℝ) * alpha) (2 * L + 1) := by
  unfold phaseExponentialSum phaseExponentialSequence
  apply Finset.sum_bij (fun y _hy => (y + (L : ℤ)).toNat)
  · intro y hy
    rw [Finset.mem_Icc] at hy
    rw [Finset.mem_range]
    have hnonneg : 0 ≤ y + (L : ℤ) := by omega
    have hle : y + (L : ℤ) ≤ (2 * L : ℕ) := by omega
    omega
  · intro y₁ hy₁ y₂ hy₂ h
    rw [Finset.mem_Icc] at hy₁ hy₂
    have h₁ : 0 ≤ y₁ + (L : ℤ) := by omega
    have h₂ : 0 ≤ y₂ + (L : ℤ) := by omega
    have hc₁ : (((y₁ + (L : ℤ)).toNat : ℕ) : ℤ) = y₁ + (L : ℤ) :=
      Int.toNat_of_nonneg h₁
    have hc₂ : (((y₂ + (L : ℤ)).toNat : ℕ) : ℤ) = y₂ + (L : ℤ) :=
      Int.toNat_of_nonneg h₂
    omega
  · intro n hn
    rw [Finset.mem_range] at hn
    refine ⟨(n : ℤ) - (L : ℤ), ?_, ?_⟩
    · rw [Finset.mem_Icc]
      constructor <;> omega
    · simp
  · intro y hy
    rw [Finset.mem_Icc] at hy
    have hnonneg : 0 ≤ y + (L : ℤ) := by omega
    have hcast : (((y + (L : ℤ)).toNat : ℕ) : ℤ) = y + (L : ℤ) :=
      Int.toNat_of_nonneg hnonneg
    apply congrArg standardAdditiveCharacter
    have hreal : (((y + (L : ℤ)).toNat : ℕ) : ℝ) =
        (y : ℝ) + (L : ℝ) := by
      exact_mod_cast hcast
    change alpha * (y : ℝ) =
      (((y + (L : ℤ)).toNat : ℕ) : ℝ) * alpha - (L : ℝ) * alpha
    rw [hreal]
    ring

/-- Uniform geometric-series majorant, retaining the exact length in the
resonant case and the minimum of length and reciprocal distance otherwise. -/
noncomputable def vinogradovGeometricSumBound (N : ℕ) (alpha : ℝ) : ℝ :=
  if nearestIntegerDistance alpha = 0 then (N : ℝ)
  else min (N : ℝ) (1 / (2 * nearestIntegerDistance alpha))

/-- Symmetric geometric-sum bound in nearest-integer-distance form. -/
theorem norm_sum_symmetric_standardAdditiveCharacter_le_geometricBound
    (alpha : ℝ) (L : ℕ) :
    ‖∑ y ∈ Finset.Icc (-(L : ℤ)) (L : ℤ),
      standardAdditiveCharacter (alpha * (y : ℝ))‖ ≤
      vinogradovGeometricSumBound (2 * L + 1) alpha := by
  rw [sum_symmetric_standardAdditiveCharacter_eq_phaseExponentialSum]
  by_cases hdist : nearestIntegerDistance alpha = 0
  · rw [vinogradovGeometricSumBound, if_pos hdist]
    exact norm_phaseExponentialSum_le _ _
  · rw [vinogradovGeometricSumBound, if_neg hdist]
    simpa only [sub_eq_add_neg] using
      norm_phaseExponentialSum_affine_le_min_nearestIntegerDistance
        alpha (-((L : ℝ) * alpha)) (2 * L + 1)
          (lt_of_le_of_ne (nearestIntegerDistance_nonneg alpha) (Ne.symm hdist))

/-- The geometric bound specialized to one inner coordinate sum in the
Vinogradov power box. -/
theorem norm_sum_powerBoxSide_standardAdditiveCharacter_le_geometricBound
    (c : ℕ → ℝ) (V ℓ degree : ℕ) (x : ℤ) :
    ‖∑ y ∈ vinogradovPowerBoxSide ℓ V degree,
      standardAdditiveCharacter (c degree * (x : ℝ) * (y : ℝ))‖ ≤
      vinogradovGeometricSumBound (2 * (ℓ * V ^ degree) + 1)
        (c degree * (x : ℝ)) := by
  unfold vinogradovPowerBoxSide
  simpa only [mul_assoc] using
    norm_sum_symmetric_standardAdditiveCharacter_le_geometricBound
      (c degree * (x : ℝ)) (ℓ * V ^ degree)

/-- The one-dimensional Lemma 12 factor is reduced to summing the uniform
geometric-series majorant over its outer coordinate. -/
theorem sum_norm_powerBoxSide_phase_le_sum_geometricBound
    (c : ℕ → ℝ) (V ℓ degree : ℕ) :
    (∑ x ∈ vinogradovPowerBoxSide ℓ V degree,
      ‖∑ y ∈ vinogradovPowerBoxSide ℓ V degree,
        standardAdditiveCharacter
          (c degree * (x : ℝ) * (y : ℝ))‖) ≤
      ∑ x ∈ vinogradovPowerBoxSide ℓ V degree,
        vinogradovGeometricSumBound (2 * (ℓ * V ^ degree) + 1)
          (c degree * (x : ℝ)) := by
  apply Finset.sum_le_sum
  intro x hx
  exact norm_sum_powerBoxSide_standardAdditiveCharacter_le_geometricBound
    c V ℓ degree x

/-- Exact cardinality of one symmetric power-box coordinate interval. -/
theorem card_vinogradovPowerBoxSide (V ℓ degree : ℕ) :
    (vinogradovPowerBoxSide ℓ V degree).card =
      2 * (ℓ * V ^ degree) + 1 := by
  unfold vinogradovPowerBoxSide
  rw [Int.card_Icc]
  omega

theorem vinogradovGeometricSumBound_nonneg (N : ℕ) (alpha : ℝ) :
    0 ≤ vinogradovGeometricSumBound N alpha := by
  unfold vinogradovGeometricSumBound
  by_cases h : nearestIntegerDistance alpha = 0
  · rw [if_pos h]
    positivity
  · rw [if_neg h]
    rw [le_min_iff]
    constructor
    · positivity
    · exact div_nonneg (by norm_num)
        (mul_nonneg (by norm_num) (nearestIntegerDistance_nonneg alpha))

theorem vinogradovGeometricSumBound_le_length (N : ℕ) (alpha : ℝ) :
    vinogradovGeometricSumBound N alpha ≤ (N : ℝ) := by
  unfold vinogradovGeometricSumBound
  by_cases h : nearestIntegerDistance alpha = 0
  · rw [if_pos h]
  · rw [if_neg h]
    exact min_le_left _ _

/-- The trivial square-cardinality estimate for every one-dimensional factor
in the box factorization. -/
theorem sum_norm_powerBoxSide_phase_le_card_sq
    (c : ℕ → ℝ) (V ℓ degree : ℕ) :
    (∑ x ∈ vinogradovPowerBoxSide ℓ V degree,
      ‖∑ y ∈ vinogradovPowerBoxSide ℓ V degree,
        standardAdditiveCharacter
          (c degree * (x : ℝ) * (y : ℝ))‖) ≤
      (2 * (ℓ * V ^ degree) + 1 : ℝ) ^ 2 := by
  let N := 2 * (ℓ * V ^ degree) + 1
  calc
    (∑ x ∈ vinogradovPowerBoxSide ℓ V degree,
      ‖∑ y ∈ vinogradovPowerBoxSide ℓ V degree,
        standardAdditiveCharacter
          (c degree * (x : ℝ) * (y : ℝ))‖) ≤
      ∑ x ∈ vinogradovPowerBoxSide ℓ V degree,
        vinogradovGeometricSumBound N (c degree * (x : ℝ)) := by
          simpa only [N] using
            sum_norm_powerBoxSide_phase_le_sum_geometricBound c V ℓ degree
    _ ≤ ∑ _x ∈ vinogradovPowerBoxSide ℓ V degree, (N : ℝ) := by
      apply Finset.sum_le_sum
      intro x hx
      exact vinogradovGeometricSumBound_le_length N _
    _ = (N : ℝ) ^ 2 := by
      rw [Finset.sum_const, nsmul_eq_mul, card_vinogradovPowerBoxSide]
      dsimp [N]
      norm_num [pow_two]
    _ = (2 * (ℓ * V ^ degree) + 1 : ℝ) ^ 2 := by
      dsimp [N]
      push_cast
      rfl

/-- A capped reciprocal-distance kernel on a real line. Its exceptional value
at zero records the trivial length bound for a resonant character sum. -/
noncomputable def cappedInverseDistanceMajorant
    (N : ℕ) (A u : ℝ) : ℝ :=
  if u = 0 then (N : ℝ) else min (N : ℝ) (A / |u|)

/-- Quantitative integral-test bound for a capped reciprocal kernel on a
finite `1`-separated set. The central interval contributes at most two trivial
terms, while the remaining annuli have harmonic total mass. -/
theorem sum_cappedInverseDistanceMajorant_le
    (N K : ℕ) (A : ℝ) (W : Finset ℝ)
    (hA : 0 ≤ A) (hSep : IsSeparated 1 W)
    (hW : ∀ u ∈ W, |u| ≤ (K : ℝ)) :
    (∑ u ∈ W, cappedInverseDistanceMajorant N A u) ≤
      2 * (N : ℝ) + 4 * A * (((harmonic K : ℚ) : ℝ)) := by
  let C := W.filter fun u => |u| < 1
  let F := W.filter fun u => ¬ |u| < 1
  have hcardC : C.card ≤ 2 := by
    by_cases hzero : (0 : ℝ) ∈ C
    · have hcardOne : C.card ≤ 1 := by
        rw [Finset.card_le_one]
        intro x hx y hy
        have hxW : x ∈ W := (Finset.mem_filter.mp hx).1
        have hyW : y ∈ W := (Finset.mem_filter.mp hy).1
        have h0W : (0 : ℝ) ∈ W := (Finset.mem_filter.mp hzero).1
        have hx0 : x = 0 := by
          by_contra hxne
          have hs := hSep 0 h0W x hxW (Ne.symm hxne)
          rw [Real.dist_eq, zero_sub, abs_neg] at hs
          have hxlt := (Finset.mem_filter.mp hx).2
          linarith
        have hy0 : y = 0 := by
          by_contra hyne
          have hs := hSep 0 h0W y hyW (Ne.symm hyne)
          rw [Real.dist_eq, zero_sub, abs_neg] at hs
          have hylt := (Finset.mem_filter.mp hy).2
          linarith
        rw [hx0, hy0]
      omega
    · calc
        C.card ≤
            ({u ∈ W | u ≠ 0 ∧ (0 : ℝ) ≤ |u - 0| ∧
              |u - 0| < (0 : ℝ) + 1}).card := by
          apply Finset.card_le_card
          intro u hu
          have huW := (Finset.mem_filter.mp hu).1
          have hult := (Finset.mem_filter.mp hu).2
          rw [Finset.mem_filter]
          refine ⟨huW, ?_, by positivity, ?_⟩
          · intro hu0
            exact hzero (by simpa [hu0] using hu)
          · simpa using hult
        _ ≤ 2 := by
          simpa only [Nat.cast_zero, zero_add] using
            separated_annulus_card_le_two W 0 0 hSep
  have hcentral :
      (∑ u ∈ C, cappedInverseDistanceMajorant N A u) ≤
        2 * (N : ℝ) := by
    calc
      (∑ u ∈ C, cappedInverseDistanceMajorant N A u) ≤
          ∑ _u ∈ C, (N : ℝ) := by
        apply Finset.sum_le_sum
        intro u hu
        unfold cappedInverseDistanceMajorant
        by_cases hu0 : u = 0
        · rw [if_pos hu0]
        · rw [if_neg hu0]
          exact min_le_left _ _
      _ = (C.card : ℝ) * N := by simp
      _ ≤ 2 * (N : ℝ) := by
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcardC) (by positivity)
  have hFsubset : F ⊆ W := Finset.filter_subset _ _
  have hFaway : ∀ u ∈ F, (1 : ℝ) ≤ |u| := by
    intro u hu
    have hnot := (Finset.mem_filter.mp hu).2
    exact le_of_not_gt hnot
  let W₀ := insert (0 : ℝ) F
  have hsepW₀ : IsSeparated 1 W₀ := by
    intro x hx y hy hxy
    rw [Finset.mem_insert] at hx hy
    rcases hx with rfl | hxF
    · rcases hy with rfl | hyF
      · exact (hxy rfl).elim
      · simpa only [Real.dist_eq, zero_sub, abs_neg] using hFaway y hyF
    · rcases hy with rfl | hyF
      · simpa only [Real.dist_eq, sub_zero] using hFaway x hxF
      · exact hSep x (hFsubset hxF) y (hFsubset hyF) hxy
  have hzeroW₀ : (0 : ℝ) ∈ W₀ := Finset.mem_insert_self _ _
  have hset :
      {u ∈ W₀ | u ≠ 0 ∧ |u - 0| ≤ (K : ℝ)} = F := by
    dsimp [W₀]
    ext u
    simp only [Finset.mem_filter, Finset.mem_insert, sub_zero]
    constructor
    · rintro ⟨hu0 | huF, hne, hbound⟩
      · exact (hne hu0).elim
      · exact huF
    · intro huF
      refine ⟨Or.inr huF, ?_, ?_⟩
      · intro hu0
        have := hFaway u huF
        rw [hu0, abs_zero] at this
        linarith
      · exact hW u (hFsubset huF)
  have hinv : (∑ u ∈ F, 1 / |u|) ≤
      2 * (((harmonic K : ℚ) : ℝ)) := by
    have h := sum_inv_distance_near_le_harmonic K W₀ 0 hsepW₀ hzeroW₀
    rw [hset] at h
    simpa only [sub_zero] using h
  have hfar : (∑ u ∈ F, cappedInverseDistanceMajorant N A u) ≤
      2 * A * (((harmonic K : ℚ) : ℝ)) := by
    calc
      (∑ u ∈ F, cappedInverseDistanceMajorant N A u) ≤
          ∑ u ∈ F, A * (1 / |u|) := by
        apply Finset.sum_le_sum
        intro u hu
        have hu0 : u ≠ 0 := by
          intro hu0
          have := hFaway u hu
          rw [hu0, abs_zero] at this
          linarith
        unfold cappedInverseDistanceMajorant
        rw [if_neg hu0]
        calc
          min (N : ℝ) (A / |u|) ≤ A / |u| := min_le_right _ _
          _ = A * (1 / |u|) := by simp [div_eq_mul_inv]
      _ = A * (∑ u ∈ F, 1 / |u|) := by simp_rw [Finset.mul_sum]
      _ ≤ A * (2 * (((harmonic K : ℚ) : ℝ))) :=
        mul_le_mul_of_nonneg_left hinv hA
      _ = 2 * A * (((harmonic K : ℚ) : ℝ)) := by ring
  have hsplit :
      (∑ u ∈ W, cappedInverseDistanceMajorant N A u) =
        (∑ u ∈ C, cappedInverseDistanceMajorant N A u) +
          ∑ u ∈ F, cappedInverseDistanceMajorant N A u := by
    dsimp [C, F]
    rw [Finset.sum_filter_add_sum_filter_not]
  rw [hsplit]
  calc
    (∑ u ∈ C, cappedInverseDistanceMajorant N A u) +
        ∑ u ∈ F, cappedInverseDistanceMajorant N A u ≤
      2 * (N : ℝ) + 2 * A * (((harmonic K : ℚ) : ℝ)) :=
        add_le_add hcentral hfar
    _ ≤ 2 * (N : ℝ) + 4 * A * (((harmonic K : ℚ) : ℝ)) := by
      have hh : 0 ≤ (((harmonic K : ℚ) : ℝ)) := by
        cases K with
        | zero => simp
        | succ K => exact_mod_cast (harmonic_pos (Nat.succ_ne_zero K)).le
      nlinarith

/-- Integers in the symmetric interval whose nearest integer after scaling by
`alpha` is `m`. These are the fibers used in the integral-test proof of
Tao's Lemma 12. -/
noncomputable def vinogradovNearestIntegerFiber
    (alpha : ℝ) (L : ℕ) (m : ℤ) : Finset ℤ :=
  (Finset.Icc (-(L : ℤ)) (L : ℤ)).filter fun x =>
    round (alpha * (x : ℝ)) = m

/-- A nearest-integer fiber, translated by its nearest integer and rescaled
by `|alpha|`. -/
noncomputable def vinogradovScaledNearestIntegerFiber
    (alpha : ℝ) (L : ℕ) (m : ℤ) : Finset ℝ :=
  (vinogradovNearestIntegerFiber alpha L m).image fun x : ℤ =>
    (alpha * (x : ℝ) - (m : ℝ)) / |alpha|

/-- After rescaling, distinct members of one nearest-integer fiber are at
least one unit apart. -/
theorem vinogradovScaledNearestIntegerFiber_separated
    (alpha : ℝ) (L : ℕ) (m : ℤ) (halpha : alpha ≠ 0) :
    IsSeparated 1 (vinogradovScaledNearestIntegerFiber alpha L m) := by
  intro u hu v hv huv
  rw [vinogradovScaledNearestIntegerFiber, Finset.mem_image] at hu hv
  obtain ⟨x, hx, rfl⟩ := hu
  obtain ⟨y, hy, rfl⟩ := hv
  have hxy : x ≠ y := by
    intro h
    apply huv
    rw [h]
  have hInt : (1 : ℤ) ≤ |x - y| :=
    Int.one_le_abs (sub_ne_zero.mpr hxy)
  have hReal : (1 : ℝ) ≤ |(x : ℝ) - (y : ℝ)| := by
    exact_mod_cast hInt
  have habs : 0 < |alpha| := abs_pos.mpr halpha
  rw [Real.dist_eq]
  calc
    |((alpha * (x : ℝ) - (m : ℝ)) / |alpha| -
        (alpha * (y : ℝ) - (m : ℝ)) / |alpha|)| =
      |(alpha * ((x : ℝ) - (y : ℝ)) / |alpha|)| := by
        congr 1
        field_simp
        ring
    _ = |alpha| * |(x : ℝ) - (y : ℝ)| / |alpha| := by
      rw [abs_div, abs_mul, abs_abs]
    _ = |(x : ℝ) - (y : ℝ)| := by field_simp
    _ ≥ 1 := hReal

/-- Every rescaled nearest-integer fiber lies in the interval dictated by
the universal distance-to-nearest-integer bound. -/
theorem abs_le_ceil_inv_two_mul_abs_of_mem_scaledNearestIntegerFiber
    (alpha : ℝ) (L : ℕ) (m : ℤ) (halpha : alpha ≠ 0)
    (u : ℝ) (hu : u ∈ vinogradovScaledNearestIntegerFiber alpha L m) :
    |u| ≤ (Nat.ceil (1 / (2 * |alpha|)) : ℝ) := by
  rw [vinogradovScaledNearestIntegerFiber, Finset.mem_image] at hu
  obtain ⟨x, hx, rfl⟩ := hu
  have habs : 0 < |alpha| := abs_pos.mpr halpha
  have hround : round (alpha * (x : ℝ)) = m :=
    (Finset.mem_filter.mp hx).2
  have hdist : nearestIntegerDistance (alpha * (x : ℝ)) =
      |alpha * (x : ℝ) - (m : ℝ)| := by
    unfold nearestIntegerDistance
    rw [hround]
  calc
    |((alpha * (x : ℝ) - (m : ℝ)) / |alpha|)| =
        |alpha * (x : ℝ) - (m : ℝ)| / |alpha| := by
      rw [abs_div, abs_abs]
    _ = nearestIntegerDistance (alpha * (x : ℝ)) / |alpha| := by
      rw [hdist]
    _ ≤ (1 / 2) / |alpha| := by
      exact div_le_div_of_nonneg_right
        (nearestIntegerDistance_le_half _) habs.le
    _ = 1 / (2 * |alpha|) := by field_simp
    _ ≤ (Nat.ceil (1 / (2 * |alpha|)) : ℝ) := Nat.le_ceil _

/-- On a nearest-integer fiber, the geometric-sum bound is exactly the
capped reciprocal-distance kernel after rescaling. -/
theorem vinogradovGeometricSumBound_eq_cappedInverseDistanceMajorant_on_fiber
    (N : ℕ) (alpha : ℝ) (x m : ℤ) (halpha : alpha ≠ 0)
    (hround : round (alpha * (x : ℝ)) = m) :
    vinogradovGeometricSumBound N (alpha * (x : ℝ)) =
      cappedInverseDistanceMajorant N (1 / (2 * |alpha|))
        ((alpha * (x : ℝ) - (m : ℝ)) / |alpha|) := by
  have habs : 0 < |alpha| := abs_pos.mpr halpha
  have hdist : nearestIntegerDistance (alpha * (x : ℝ)) =
      |alpha * (x : ℝ) - (m : ℝ)| := by
    unfold nearestIntegerDistance
    rw [hround]
  by_cases hzero : nearestIntegerDistance (alpha * (x : ℝ)) = 0
  · have hnum : alpha * (x : ℝ) - (m : ℝ) = 0 := by
      rw [hdist, abs_eq_zero] at hzero
      exact hzero
    rw [vinogradovGeometricSumBound, if_pos hzero,
      cappedInverseDistanceMajorant, hnum, zero_div, if_pos rfl]
  · have hnum : alpha * (x : ℝ) - (m : ℝ) ≠ 0 := by
      intro h
      apply hzero
      rw [hdist, h, abs_zero]
    have hu : (alpha * (x : ℝ) - (m : ℝ)) / |alpha| ≠ 0 :=
      div_ne_zero hnum (ne_of_gt habs)
    rw [vinogradovGeometricSumBound, if_neg hzero,
      cappedInverseDistanceMajorant, if_neg hu]
    congr 1
    rw [abs_div, abs_abs, hdist]
    field_simp

/-- The rescaling map is injective on every nondegenerate nearest-integer
fiber. -/
theorem vinogradovScaledNearestIntegerFiberMap_injOn
    (alpha : ℝ) (L : ℕ) (m : ℤ) (halpha : alpha ≠ 0) :
    Set.InjOn (fun x : ℤ =>
      (alpha * (x : ℝ) - (m : ℝ)) / |alpha|)
      (vinogradovNearestIntegerFiber alpha L m) := by
  intro x hx y hy hxy
  have habs : |alpha| ≠ 0 := abs_ne_zero.mpr halpha
  have hmul : alpha * (x : ℝ) = alpha * (y : ℝ) := by
    have hsub := (div_left_inj' habs).mp hxy
    linarith
  have hcast : (x : ℝ) = (y : ℝ) := by
    exact mul_left_cancel₀ halpha hmul
  exact_mod_cast hcast

/-- The sum of geometric bounds on one nearest-integer fiber satisfies the
harmonic integral-test estimate. -/
theorem sum_vinogradovGeometricSumBound_on_fiber_le
    (N L : ℕ) (alpha : ℝ) (m : ℤ) (halpha : alpha ≠ 0) :
    (∑ x ∈ vinogradovNearestIntegerFiber alpha L m,
        vinogradovGeometricSumBound N (alpha * (x : ℝ))) ≤
      2 * (N : ℝ) +
        2 / |alpha| *
          (((harmonic (Nat.ceil (1 / (2 * |alpha|))) : ℚ) : ℝ)) := by
  have hsum :
      (∑ x ∈ vinogradovNearestIntegerFiber alpha L m,
          vinogradovGeometricSumBound N (alpha * (x : ℝ))) =
        ∑ u ∈ vinogradovScaledNearestIntegerFiber alpha L m,
          cappedInverseDistanceMajorant N (1 / (2 * |alpha|)) u := by
    rw [vinogradovScaledNearestIntegerFiber, Finset.sum_image
      (vinogradovScaledNearestIntegerFiberMap_injOn alpha L m halpha)]
    apply Finset.sum_congr rfl
    intro x hx
    exact
      vinogradovGeometricSumBound_eq_cappedInverseDistanceMajorant_on_fiber
        N alpha x m halpha (Finset.mem_filter.mp hx).2
  rw [hsum]
  have hA : 0 ≤ 1 / (2 * |alpha|) := by positivity
  have hkernel := sum_cappedInverseDistanceMajorant_le N
    (Nat.ceil (1 / (2 * |alpha|))) (1 / (2 * |alpha|))
    (vinogradovScaledNearestIntegerFiber alpha L m) hA
    (vinogradovScaledNearestIntegerFiber_separated alpha L m halpha)
    (abs_le_ceil_inv_two_mul_abs_of_mem_scaledNearestIntegerFiber
      alpha L m halpha)
  calc
    (∑ u ∈ vinogradovScaledNearestIntegerFiber alpha L m,
        cappedInverseDistanceMajorant N (1 / (2 * |alpha|)) u) ≤
      2 * (N : ℝ) + 4 * (1 / (2 * |alpha|)) *
        (((harmonic (Nat.ceil (1 / (2 * |alpha|))) : ℚ) : ℝ)) := hkernel
    _ = 2 * (N : ℝ) + 2 / |alpha| *
        (((harmonic (Nat.ceil (1 / (2 * |alpha|))) : ℚ) : ℝ)) := by
      ring

/-- Nearest integers attained by `alpha * x` on the symmetric interval. -/
noncomputable def vinogradovNearestIntegerImage
    (alpha : ℝ) (L : ℕ) : Finset ℤ :=
  (Finset.Icc (-(L : ℤ)) (L : ℤ)).image fun x : ℤ =>
    round (alpha * (x : ℝ))

/-- The nearest-integer image lies in the interval of radius
`ceil (|alpha| L + 1/2)`. -/
theorem vinogradovNearestIntegerImage_subset
    (alpha : ℝ) (L : ℕ) :
    vinogradovNearestIntegerImage alpha L ⊆
      Finset.Icc
        (-(Nat.ceil (|alpha| * (L : ℝ) + 1 / 2) : ℤ))
        (Nat.ceil (|alpha| * (L : ℝ) + 1 / 2) : ℤ) := by
  intro m hm
  rw [vinogradovNearestIntegerImage, Finset.mem_image] at hm
  obtain ⟨x, hx, rfl⟩ := hm
  rw [Finset.mem_Icc] at hx ⊢
  have hxreal : |(x : ℝ)| ≤ (L : ℝ) := by
    rw [abs_le]
    constructor
    · exact_mod_cast hx.1
    · exact_mod_cast hx.2
  have hround := abs_sub_round (alpha * (x : ℝ))
  have hrabs : |((round (alpha * (x : ℝ)) : ℤ) : ℝ)| ≤
      |alpha * (x : ℝ)| + 1 / 2 := by
    calc
      |((round (alpha * (x : ℝ)) : ℤ) : ℝ)| =
          |alpha * (x : ℝ) -
            (alpha * (x : ℝ) - (round (alpha * (x : ℝ)) : ℤ))| := by
              congr 1
              ring
      _ ≤ |alpha * (x : ℝ)| +
          |alpha * (x : ℝ) - (round (alpha * (x : ℝ)) : ℤ)| :=
            abs_sub _ _
      _ ≤ |alpha * (x : ℝ)| + 1 / 2 := by gcongr
  have hmreal : |((round (alpha * (x : ℝ)) : ℤ) : ℝ)| ≤
      |alpha| * (L : ℝ) + 1 / 2 := by
    calc
      |((round (alpha * (x : ℝ)) : ℤ) : ℝ)| ≤
          |alpha * (x : ℝ)| + 1 / 2 := hrabs
      _ = |alpha| * |(x : ℝ)| + 1 / 2 := by rw [abs_mul]
      _ ≤ |alpha| * (L : ℝ) + 1 / 2 := by gcongr
  have hmceil : |((round (alpha * (x : ℝ)) : ℤ) : ℝ)| ≤
      (Nat.ceil (|alpha| * (L : ℝ) + 1 / 2) : ℝ) :=
    hmreal.trans (Nat.le_ceil _)
  rw [abs_le] at hmceil
  constructor
  · exact_mod_cast hmceil.1
  · exact_mod_cast hmceil.2

/-- Consequently the nearest-integer image has at most
`2 ceil (|alpha| L + 1/2) + 1` elements. -/
theorem vinogradovNearestIntegerImage_card_le
    (alpha : ℝ) (L : ℕ) :
    (vinogradovNearestIntegerImage alpha L).card ≤
      2 * Nat.ceil (|alpha| * (L : ℝ) + 1 / 2) + 1 := by
  calc
    (vinogradovNearestIntegerImage alpha L).card ≤
        (Finset.Icc
          (-(Nat.ceil (|alpha| * (L : ℝ) + 1 / 2) : ℤ))
          (Nat.ceil (|alpha| * (L : ℝ) + 1 / 2) : ℤ)).card :=
      Finset.card_le_card (vinogradovNearestIntegerImage_subset alpha L)
    _ = 2 * Nat.ceil (|alpha| * (L : ℝ) + 1 / 2) + 1 := by
      rw [Int.card_Icc]
      omega

/-- Quantitative one-dimensional integral-test estimate for the geometric
majorants arising in Tao's Lemma 12. -/
theorem sum_vinogradovGeometricSumBound_le
    (N L : ℕ) (alpha : ℝ) (halpha : alpha ≠ 0) :
    (∑ x ∈ Finset.Icc (-(L : ℤ)) (L : ℤ),
        vinogradovGeometricSumBound N (alpha * (x : ℝ))) ≤
      (2 * Nat.ceil (|alpha| * (L : ℝ) + 1 / 2) + 1 : ℝ) *
        (2 * (N : ℝ) + 2 / |alpha| *
          (((harmonic (Nat.ceil (1 / (2 * |alpha|))) : ℚ) : ℝ))) := by
  let X := Finset.Icc (-(L : ℤ)) (L : ℤ)
  let M := vinogradovNearestIntegerImage alpha L
  let B : ℝ := 2 * (N : ℝ) + 2 / |alpha| *
    (((harmonic (Nat.ceil (1 / (2 * |alpha|))) : ℚ) : ℝ))
  have hgroup :
      (∑ x ∈ X, vinogradovGeometricSumBound N (alpha * (x : ℝ))) =
        ∑ m ∈ M, ∑ x ∈ vinogradovNearestIntegerFiber alpha L m,
          vinogradovGeometricSumBound N (alpha * (x : ℝ)) := by
    rw [← Finset.sum_fiberwise_of_maps_to
      (s := X) (t := M)
      (g := fun x : ℤ => round (alpha * (x : ℝ)))
      (fun x hx => by
        dsimp [M, vinogradovNearestIntegerImage]
        rw [Finset.mem_image]
        exact ⟨x, hx, rfl⟩)
      (fun x => vinogradovGeometricSumBound N (alpha * (x : ℝ)))]
    rfl
  have hB : 0 ≤ B := by
    dsimp [B]
    have hh : 0 ≤
        (((harmonic (Nat.ceil (1 / (2 * |alpha|))) : ℚ) : ℝ)) := by
      cases Nat.ceil (1 / (2 * |alpha|)) with
      | zero => simp
      | succ K => exact_mod_cast (harmonic_pos (Nat.succ_ne_zero K)).le
    positivity
  rw [hgroup]
  calc
    (∑ m ∈ M, ∑ x ∈ vinogradovNearestIntegerFiber alpha L m,
        vinogradovGeometricSumBound N (alpha * (x : ℝ))) ≤
      ∑ _m ∈ M, B := by
        apply Finset.sum_le_sum
        intro m hm
        simpa only [B] using
          sum_vinogradovGeometricSumBound_on_fiber_le N L alpha m halpha
    _ = ((M.card : ℕ) : ℝ) * B := by simp
    _ ≤ (2 * Nat.ceil (|alpha| * (L : ℝ) + 1 / 2) + 1 : ℝ) * B := by
      apply mul_le_mul_of_nonneg_right _ hB
      exact_mod_cast vinogradovNearestIntegerImage_card_le alpha L
    _ = (2 * Nat.ceil (|alpha| * (L : ℝ) + 1 / 2) + 1 : ℝ) *
        (2 * (N : ℝ) + 2 / |alpha| *
          (((harmonic (Nat.ceil (1 / (2 * |alpha|))) : ℚ) : ℝ))) := by
      rfl

/-- The quantitative one-dimensional estimate in the precise coordinate-box
form needed by equation (18). -/
theorem sum_norm_powerBoxSide_phase_le_integralTest
    (c : ℕ → ℝ) (V ell degree : ℕ) (hc : c degree ≠ 0) :
    (∑ x ∈ vinogradovPowerBoxSide ell V degree,
      ‖∑ y ∈ vinogradovPowerBoxSide ell V degree,
        standardAdditiveCharacter
          (c degree * (x : ℝ) * (y : ℝ))‖) ≤
      (2 * Nat.ceil
          (|c degree| * (ell * V ^ degree : ℕ) + 1 / 2) + 1 : ℝ) *
        (2 * (((2 * (ell * V ^ degree) + 1 : ℕ) : ℝ)) +
          2 / |c degree| *
            (((harmonic (Nat.ceil (1 / (2 * |c degree|))) : ℚ) : ℝ))) := by
  calc
    (∑ x ∈ vinogradovPowerBoxSide ell V degree,
      ‖∑ y ∈ vinogradovPowerBoxSide ell V degree,
        standardAdditiveCharacter
          (c degree * (x : ℝ) * (y : ℝ))‖) ≤
      ∑ x ∈ vinogradovPowerBoxSide ell V degree,
        vinogradovGeometricSumBound (2 * (ell * V ^ degree) + 1)
          (c degree * (x : ℝ)) :=
      sum_norm_powerBoxSide_phase_le_sum_geometricBound c V ell degree
    _ ≤ (2 * Nat.ceil
          (|c degree| * (ell * V ^ degree : ℕ) + 1 / 2) + 1 : ℝ) *
        (2 * (((2 * (ell * V ^ degree) + 1 : ℕ) : ℝ)) +
          2 / |c degree| *
            (((harmonic (Nat.ceil (1 / (2 * |c degree|))) : ℚ) : ℝ))) := by
      simpa only [vinogradovPowerBoxSide] using
        sum_vinogradovGeometricSumBound_le
          (2 * (ell * V ^ degree) + 1) (ell * V ^ degree) (c degree) hc

/-- A medium coefficient over a positive base is nonzero, so the explicit
integral-test coordinate estimate applies to every selected medium degree. -/
theorem coefficient_ne_zero_of_isVinogradovMediumCoefficient
    {M c₀ : ℝ} {c : ℕ → ℝ} {degree : ℕ} (hM : 0 < M)
    (hmedium : IsVinogradovMediumCoefficient M c₀ c degree) :
    c degree ≠ 0 := by
  have hpow : 0 < M ^ (-(2 - c₀) * (degree : ℝ)) :=
    Real.rpow_pos_of_pos hM _
  have habs : 0 < |c degree| := hpow.trans_le hmedium.1
  exact abs_pos.mp habs

/-- The lower endpoint of a medium window bounds the reciprocal absolute
coefficient by the corresponding positive power. -/
theorem one_div_abs_coefficient_le_of_isVinogradovMediumCoefficient
    {M c₀ : ℝ} {c : ℕ → ℝ} {degree : ℕ} (hM : 0 < M)
    (hmedium : IsVinogradovMediumCoefficient M c₀ c degree) :
    1 / |c degree| ≤ M ^ ((2 - c₀) * (degree : ℝ)) := by
  have hpow : 0 < M ^ (-(2 - c₀) * (degree : ℝ)) :=
    Real.rpow_pos_of_pos hM _
  have hrecip := one_div_le_one_div_of_le hpow hmedium.1
  have hexp : -(2 - c₀) * (degree : ℝ) =
      -((2 - c₀) * (degree : ℝ)) := by ring
  rw [hexp, Real.rpow_neg hM.le] at hrecip
  simpa only [one_div, inv_inv] using hrecip

/-- Elementary ceiling simplification for the number of nearest-integer
fibers. -/
theorem two_mul_ceil_abs_mul_add_half_add_one_le
    (alpha : ℝ) (L : ℕ) :
    (2 * Nat.ceil (|alpha| * (L : ℝ) + 1 / 2) + 1 : ℝ) ≤
      2 * |alpha| * (L : ℝ) + 4 := by
  have hz : 0 ≤ |alpha| * (L : ℝ) + 1 / 2 := by positivity
  have hceil := (Nat.ceil_lt_add_one hz).le
  linarith

/-- Coarse coordinate form of the integral-test bound, with the
nearest-integer-image ceiling eliminated. -/
theorem sum_norm_powerBoxSide_phase_le_coarseIntegralTest
    (c : ℕ → ℝ) (V ell degree : ℕ) (hc : c degree ≠ 0) :
    (∑ x ∈ vinogradovPowerBoxSide ell V degree,
      ‖∑ y ∈ vinogradovPowerBoxSide ell V degree,
        standardAdditiveCharacter
          (c degree * (x : ℝ) * (y : ℝ))‖) ≤
      (2 * |c degree| * ((ell * V ^ degree : ℕ) : ℝ) + 4) *
        (2 * (((2 * (ell * V ^ degree) + 1 : ℕ) : ℝ)) +
          2 / |c degree| *
            (((harmonic (Nat.ceil (1 / (2 * |c degree|))) : ℚ) : ℝ))) := by
  have hB : 0 ≤
      2 * (((2 * (ell * V ^ degree) + 1 : ℕ) : ℝ)) +
        2 / |c degree| *
          (((harmonic (Nat.ceil (1 / (2 * |c degree|))) : ℚ) : ℝ)) := by
    have hcabs : 0 < |c degree| := abs_pos.mpr hc
    have hh : 0 ≤
        (((harmonic (Nat.ceil (1 / (2 * |c degree|))) : ℚ) : ℝ)) := by
      cases Nat.ceil (1 / (2 * |c degree|)) with
      | zero => simp
      | succ K => exact_mod_cast (harmonic_pos (Nat.succ_ne_zero K)).le
    positivity
  exact (sum_norm_powerBoxSide_phase_le_integralTest c V ell degree hc).trans
    (mul_le_mul_of_nonneg_right
      (two_mul_ceil_abs_mul_add_half_add_one_le
        (c degree) (ell * V ^ degree)) hB)

/-- Harmonic numbers are monotone in their natural index. -/
theorem harmonic_mono_nat {m n : ℕ} (h : m ≤ n) :
    harmonic m ≤ harmonic n := by
  unfold harmonic
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono h)
  intro i hi hnot
  positivity

/-- A harmonic number at a real ceiling is controlled by the logarithm of
twice that real scale. -/
theorem harmonic_ceil_le_one_add_log_two_mul
    {x : ℝ} (hx : 1 ≤ x) :
    (((harmonic (Nat.ceil x) : ℚ) : ℝ)) ≤ 1 + Real.log (2 * x) := by
  have hx0 : 0 ≤ x := zero_le_one.trans hx
  have hceilLt : (Nat.ceil x : ℝ) < x + 1 := Nat.ceil_lt_add_one hx0
  have hceil : (Nat.ceil x : ℝ) ≤ 2 * x := by linarith
  have hceilOne : 1 ≤ Nat.ceil x := by
    exact_mod_cast hx.trans (Nat.le_ceil x)
  have hceilPos : 0 < (Nat.ceil x : ℝ) := by exact_mod_cast hceilOne
  calc
    (((harmonic (Nat.ceil x) : ℚ) : ℝ)) ≤
        1 + Real.log (Nat.ceil x) := harmonic_le_one_add_log _
    _ ≤ 1 + Real.log (2 * x) := by gcongr

/-- Specialization of the ceiling-harmonic estimate to a nonnegative real
power. -/
theorem harmonic_ceil_rpow_le
    {V A : ℝ} (hV : 1 ≤ V) (hA : 0 ≤ A) :
    (((harmonic (Nat.ceil (V ^ A)) : ℚ) : ℝ)) ≤
      1 + Real.log 2 + A * Real.log V := by
  have hVpos : 0 < V := zero_lt_one.trans_le hV
  have hpowOne : 1 ≤ V ^ A := Real.one_le_rpow hV hA
  calc
    (((harmonic (Nat.ceil (V ^ A)) : ℚ) : ℝ)) ≤
        1 + Real.log (2 * V ^ A) :=
      harmonic_ceil_le_one_add_log_two_mul hpowOne
    _ = 1 + Real.log 2 + A * Real.log V := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_rpow hVpos]
      ring

/-- The coarse coordinate estimate after applying both endpoints of the
medium-coefficient window. -/
theorem sum_norm_powerBoxSide_phase_le_mediumEnvelope
    (c : ℕ → ℝ) (V ell degree : ℕ) (c₀ : ℝ) (hV : 0 < (V : ℝ))
    (hmedium : IsVinogradovMediumCoefficient (V : ℝ) c₀ c degree) :
    (∑ x ∈ vinogradovPowerBoxSide ell V degree,
      ‖∑ y ∈ vinogradovPowerBoxSide ell V degree,
        standardAdditiveCharacter
          (c degree * (x : ℝ) * (y : ℝ))‖) ≤
      (2 * (V : ℝ) ^ (-c₀ * (degree : ℝ)) *
          ((ell * V ^ degree : ℕ) : ℝ) + 4) *
        (2 * (((2 * (ell * V ^ degree) + 1 : ℕ) : ℝ)) +
          2 * (V : ℝ) ^ ((2 - c₀) * (degree : ℝ)) *
            (((harmonic (Nat.ceil (1 / (2 * |c degree|))) : ℚ) : ℝ))) := by
  have hc : c degree ≠ 0 :=
    coefficient_ne_zero_of_isVinogradovMediumCoefficient hV hmedium
  have hcabs : 0 < |c degree| := abs_pos.mpr hc
  have hh : 0 ≤
      (((harmonic (Nat.ceil (1 / (2 * |c degree|))) : ℚ) : ℝ)) := by
    cases Nat.ceil (1 / (2 * |c degree|)) with
    | zero => simp
    | succ K => exact_mod_cast (harmonic_pos (Nat.succ_ne_zero K)).le
  have hleft :
      2 * |c degree| * ((ell * V ^ degree : ℕ) : ℝ) + 4 ≤
        2 * (V : ℝ) ^ (-c₀ * (degree : ℝ)) *
          ((ell * V ^ degree : ℕ) : ℝ) + 4 := by
    gcongr
    exact hmedium.2
  have hinv : 1 / |c degree| ≤
      (V : ℝ) ^ ((2 - c₀) * (degree : ℝ)) :=
    one_div_abs_coefficient_le_of_isVinogradovMediumCoefficient hV hmedium
  have hinv' : |c degree|⁻¹ ≤
      (V : ℝ) ^ ((2 - c₀) * (degree : ℝ)) := by
    simpa only [one_div] using hinv
  have hright :
      2 * (((2 * (ell * V ^ degree) + 1 : ℕ) : ℝ)) +
          2 / |c degree| *
            (((harmonic (Nat.ceil (1 / (2 * |c degree|))) : ℚ) : ℝ)) ≤
        2 * (((2 * (ell * V ^ degree) + 1 : ℕ) : ℝ)) +
          2 * (V : ℝ) ^ ((2 - c₀) * (degree : ℝ)) *
            (((harmonic (Nat.ceil (1 / (2 * |c degree|))) : ℚ) : ℝ)) := by
    rw [div_eq_mul_inv]
    gcongr
  have hrightNonneg : 0 ≤
      2 * (((2 * (ell * V ^ degree) + 1 : ℕ) : ℝ)) +
        2 / |c degree| *
          (((harmonic (Nat.ceil (1 / (2 * |c degree|))) : ℚ) : ℝ)) := by
    positivity
  have hleftTargetNonneg : 0 ≤
      2 * (V : ℝ) ^ (-c₀ * (degree : ℝ)) *
        ((ell * V ^ degree : ℕ) : ℝ) + 4 := by
    positivity
  calc
    (∑ x ∈ vinogradovPowerBoxSide ell V degree,
      ‖∑ y ∈ vinogradovPowerBoxSide ell V degree,
        standardAdditiveCharacter
          (c degree * (x : ℝ) * (y : ℝ))‖) ≤
      (2 * |c degree| * ((ell * V ^ degree : ℕ) : ℝ) + 4) *
        (2 * (((2 * (ell * V ^ degree) + 1 : ℕ) : ℝ)) +
          2 / |c degree| *
            (((harmonic (Nat.ceil (1 / (2 * |c degree|))) : ℚ) : ℝ))) :=
      sum_norm_powerBoxSide_phase_le_coarseIntegralTest c V ell degree hc
    _ ≤ (2 * (V : ℝ) ^ (-c₀ * (degree : ℝ)) *
          ((ell * V ^ degree : ℕ) : ℝ) + 4) *
        (2 * (((2 * (ell * V ^ degree) + 1 : ℕ) : ℝ)) +
          2 / |c degree| *
            (((harmonic (Nat.ceil (1 / (2 * |c degree|))) : ℚ) : ℝ))) :=
      mul_le_mul_of_nonneg_right hleft hrightNonneg
    _ ≤ (2 * (V : ℝ) ^ (-c₀ * (degree : ℝ)) *
          ((ell * V ^ degree : ℕ) : ℝ) + 4) *
        (2 * (((2 * (ell * V ^ degree) + 1 : ℕ) : ℝ)) +
          2 * (V : ℝ) ^ ((2 - c₀) * (degree : ℝ)) *
            (((harmonic (Nat.ceil (1 / (2 * |c degree|))) : ℚ) : ℝ))) :=
      mul_le_mul_of_nonneg_left hright hleftTargetNonneg

/-- The medium-coordinate estimate with its harmonic cutoff made independent
of the actual coefficient. -/
theorem sum_norm_powerBoxSide_phase_le_mediumHarmonicEnvelope
    (c : ℕ → ℝ) (V ell degree : ℕ) (c₀ : ℝ) (hV : 0 < (V : ℝ))
    (hmedium : IsVinogradovMediumCoefficient (V : ℝ) c₀ c degree) :
    (∑ x ∈ vinogradovPowerBoxSide ell V degree,
      ‖∑ y ∈ vinogradovPowerBoxSide ell V degree,
        standardAdditiveCharacter
          (c degree * (x : ℝ) * (y : ℝ))‖) ≤
      (2 * (V : ℝ) ^ (-c₀ * (degree : ℝ)) *
          ((ell * V ^ degree : ℕ) : ℝ) + 4) *
        (2 * (((2 * (ell * V ^ degree) + 1 : ℕ) : ℝ)) +
          2 * (V : ℝ) ^ ((2 - c₀) * (degree : ℝ)) *
            (((harmonic
              (Nat.ceil ((V : ℝ) ^ ((2 - c₀) * (degree : ℝ)))) : ℚ) : ℝ))) := by
  have hc : c degree ≠ 0 :=
    coefficient_ne_zero_of_isVinogradovMediumCoefficient hV hmedium
  have hcabs : 0 < |c degree| := abs_pos.mpr hc
  have hinv : 1 / |c degree| ≤
      (V : ℝ) ^ ((2 - c₀) * (degree : ℝ)) :=
    one_div_abs_coefficient_le_of_isVinogradovMediumCoefficient hV hmedium
  have hhalf : 1 / (2 * |c degree|) ≤ 1 / |c degree| := by
    calc
      1 / (2 * |c degree|) = (1 / 2) * (1 / |c degree|) := by field_simp
      _ ≤ 1 * (1 / |c degree|) := by
        gcongr
        norm_num
      _ = 1 / |c degree| := one_mul _
  have hceil : Nat.ceil (1 / (2 * |c degree|)) ≤
      Nat.ceil ((V : ℝ) ^ ((2 - c₀) * (degree : ℝ))) :=
    Nat.ceil_mono (hhalf.trans hinv)
  have hh :
      (((harmonic (Nat.ceil (1 / (2 * |c degree|))) : ℚ) : ℝ)) ≤
        (((harmonic
          (Nat.ceil ((V : ℝ) ^ ((2 - c₀) * (degree : ℝ)))) : ℚ) : ℝ)) := by
    exact_mod_cast harmonic_mono_nat hceil
  have hfactor : 0 ≤
      2 * (V : ℝ) ^ ((2 - c₀) * (degree : ℝ)) := by positivity
  have hinner :
      2 * (((2 * (ell * V ^ degree) + 1 : ℕ) : ℝ)) +
          2 * (V : ℝ) ^ ((2 - c₀) * (degree : ℝ)) *
            (((harmonic (Nat.ceil (1 / (2 * |c degree|))) : ℚ) : ℝ)) ≤
        2 * (((2 * (ell * V ^ degree) + 1 : ℕ) : ℝ)) +
          2 * (V : ℝ) ^ ((2 - c₀) * (degree : ℝ)) *
            (((harmonic
              (Nat.ceil ((V : ℝ) ^ ((2 - c₀) * (degree : ℝ)))) : ℚ) : ℝ)) := by
    simpa only [add_comm] using
      add_le_add_left (mul_le_mul_of_nonneg_left hh hfactor)
        (2 * (((2 * (ell * V ^ degree) + 1 : ℕ) : ℝ)))
  exact
    (sum_norm_powerBoxSide_phase_le_mediumEnvelope
      c V ell degree c₀ hV hmedium).trans
      (mul_le_mul_of_nonneg_left hinner (by positivity))

/-- Fully coefficient-free logarithmic envelope for every medium coordinate
in Lemma 12. -/
theorem sum_norm_powerBoxSide_phase_le_mediumLogEnvelope
    (c : ℕ → ℝ) (V ell degree : ℕ) (c₀ : ℝ) (hV : 1 ≤ V)
    (hc₀ : c₀ ≤ 2)
    (hmedium : IsVinogradovMediumCoefficient (V : ℝ) c₀ c degree) :
    (∑ x ∈ vinogradovPowerBoxSide ell V degree,
      ‖∑ y ∈ vinogradovPowerBoxSide ell V degree,
        standardAdditiveCharacter
          (c degree * (x : ℝ) * (y : ℝ))‖) ≤
      (2 * (V : ℝ) ^ (-c₀ * (degree : ℝ)) *
          ((ell * V ^ degree : ℕ) : ℝ) + 4) *
        (2 * (((2 * (ell * V ^ degree) + 1 : ℕ) : ℝ)) +
          2 * (V : ℝ) ^ ((2 - c₀) * (degree : ℝ)) *
            (1 + Real.log 2 +
              ((2 - c₀) * (degree : ℝ)) * Real.log V)) := by
  have hVreal : (1 : ℝ) ≤ (V : ℝ) := by exact_mod_cast hV
  have hVpos : 0 < (V : ℝ) := zero_lt_one.trans_le hVreal
  have hA : 0 ≤ (2 - c₀) * (degree : ℝ) :=
    mul_nonneg (sub_nonneg.mpr hc₀) (Nat.cast_nonneg _)
  have hh := harmonic_ceil_rpow_le hVreal hA
  have hfactor : 0 ≤
      2 * (V : ℝ) ^ ((2 - c₀) * (degree : ℝ)) := by positivity
  have hinner :
      2 * (((2 * (ell * V ^ degree) + 1 : ℕ) : ℝ)) +
          2 * (V : ℝ) ^ ((2 - c₀) * (degree : ℝ)) *
            (((harmonic
              (Nat.ceil ((V : ℝ) ^ ((2 - c₀) * (degree : ℝ)))) : ℚ) : ℝ)) ≤
        2 * (((2 * (ell * V ^ degree) + 1 : ℕ) : ℝ)) +
          2 * (V : ℝ) ^ ((2 - c₀) * (degree : ℝ)) *
            (1 + Real.log 2 +
              ((2 - c₀) * (degree : ℝ)) * Real.log V) := by
    simpa only [add_comm] using
      add_le_add_left (mul_le_mul_of_nonneg_left hh hfactor)
        (2 * (((2 * (ell * V ^ degree) + 1 : ℕ) : ℝ)))
  exact
    (sum_norm_powerBoxSide_phase_le_mediumHarmonicEnvelope
      c V ell degree c₀ hVpos hmedium).trans
      (mul_le_mul_of_nonneg_left hinner (by positivity))

/-- Source-style expanded medium-coordinate estimate. Expanding before
applying the two coefficient endpoints preserves the cancellation between
`|c degree|` and its reciprocal and gives precisely the four terms used in
Tao's proof of Lemma 12. -/
theorem sum_norm_powerBoxSide_phase_le_mediumExpandedLogEnvelope
    (c : ℕ → ℝ) (V ell degree : ℕ) (c₀ : ℝ) (hV : 1 ≤ V)
    (hc₀ : c₀ ≤ 2)
    (hmedium : IsVinogradovMediumCoefficient (V : ℝ) c₀ c degree) :
    (∑ x ∈ vinogradovPowerBoxSide ell V degree,
      ‖∑ y ∈ vinogradovPowerBoxSide ell V degree,
        standardAdditiveCharacter
          (c degree * (x : ℝ) * (y : ℝ))‖) ≤
      4 * (V : ℝ) ^ (-c₀ * (degree : ℝ)) *
          ((ell * V ^ degree : ℕ) : ℝ) *
          (((2 * (ell * V ^ degree) + 1 : ℕ) : ℝ)) +
        4 * ((ell * V ^ degree : ℕ) : ℝ) *
          (1 + Real.log 2 +
            ((2 - c₀) * (degree : ℝ)) * Real.log V) +
        8 * (((2 * (ell * V ^ degree) + 1 : ℕ) : ℝ)) +
        8 * (V : ℝ) ^ ((2 - c₀) * (degree : ℝ)) *
          (1 + Real.log 2 +
            ((2 - c₀) * (degree : ℝ)) * Real.log V) := by
  let L : ℝ := ((ell * V ^ degree : ℕ) : ℝ)
  let N : ℝ := (((2 * (ell * V ^ degree) + 1 : ℕ) : ℝ))
  let H : ℝ :=
    (((harmonic (Nat.ceil (1 / (2 * |c degree|))) : ℚ) : ℝ))
  let G : ℝ := 1 + Real.log 2 +
    ((2 - c₀) * (degree : ℝ)) * Real.log V
  let U : ℝ := (V : ℝ) ^ (-c₀ * (degree : ℝ))
  let Q : ℝ := (V : ℝ) ^ ((2 - c₀) * (degree : ℝ))
  have hVreal : (1 : ℝ) ≤ (V : ℝ) := by exact_mod_cast hV
  have hVpos : 0 < (V : ℝ) := zero_lt_one.trans_le hVreal
  have hc : c degree ≠ 0 :=
    coefficient_ne_zero_of_isVinogradovMediumCoefficient hVpos hmedium
  have hcabs : 0 < |c degree| := abs_pos.mpr hc
  have hinv : 1 / |c degree| ≤ Q := by
    simpa only [Q] using
      one_div_abs_coefficient_le_of_isVinogradovMediumCoefficient hVpos hmedium
  have hhalf : 1 / (2 * |c degree|) ≤ 1 / |c degree| := by
    calc
      1 / (2 * |c degree|) = (1 / 2) * (1 / |c degree|) := by field_simp
      _ ≤ 1 * (1 / |c degree|) := by
        gcongr
        norm_num
      _ = 1 / |c degree| := one_mul _
  have hceil : Nat.ceil (1 / (2 * |c degree|)) ≤ Nat.ceil Q :=
    Nat.ceil_mono (hhalf.trans hinv)
  have hHharm : H ≤ (((harmonic (Nat.ceil Q) : ℚ) : ℝ)) := by
    dsimp only [H]
    exact_mod_cast harmonic_mono_nat hceil
  have hA : 0 ≤ (2 - c₀) * (degree : ℝ) :=
    mul_nonneg (sub_nonneg.mpr hc₀) (Nat.cast_nonneg _)
  have hharmG : (((harmonic (Nat.ceil Q) : ℚ) : ℝ)) ≤ G := by
    dsimp only [Q, G]
    exact harmonic_ceil_rpow_le hVreal hA
  have hHG : H ≤ G := hHharm.trans hharmG
  have hH : 0 ≤ H := by
    dsimp only [H]
    cases Nat.ceil (1 / (2 * |c degree|)) with
    | zero => simp
    | succ K => exact_mod_cast (harmonic_pos (Nat.succ_ne_zero K)).le
  have hG : 0 ≤ G := hH.trans hHG
  have hU : |c degree| ≤ U := by simpa only [U] using hmedium.2
  have hL : 0 ≤ L := by positivity
  have hN : 0 ≤ N := by positivity
  have hQ : 0 ≤ Q := by positivity
  calc
    (∑ x ∈ vinogradovPowerBoxSide ell V degree,
      ‖∑ y ∈ vinogradovPowerBoxSide ell V degree,
        standardAdditiveCharacter
          (c degree * (x : ℝ) * (y : ℝ))‖) ≤
      (2 * |c degree| * L + 4) * (2 * N + 2 / |c degree| * H) := by
        simpa only [L, N, H] using
          sum_norm_powerBoxSide_phase_le_coarseIntegralTest c V ell degree hc
    _ = 4 * |c degree| * L * N + 4 * L * H + 8 * N +
        8 * (1 / |c degree|) * H := by
      field_simp
      ring
    _ ≤ 4 * U * L * N + 4 * L * G + 8 * N + 8 * Q * G := by
      gcongr
    _ = 4 * (V : ℝ) ^ (-c₀ * (degree : ℝ)) *
          ((ell * V ^ degree : ℕ) : ℝ) *
          (((2 * (ell * V ^ degree) + 1 : ℕ) : ℝ)) +
        4 * ((ell * V ^ degree : ℕ) : ℝ) *
          (1 + Real.log 2 +
            ((2 - c₀) * (degree : ℝ)) * Real.log V) +
        8 * (((2 * (ell * V ^ degree) + 1 : ℕ) : ℝ)) +
        8 * (V : ℝ) ^ ((2 - c₀) * (degree : ℝ)) *
          (1 + Real.log 2 +
            ((2 - c₀) * (degree : ℝ)) * Real.log V) := by
      rfl

/-- Algebraic normalization of the four source terms by the square of the
coordinate side length. -/
theorem expanded_mediumCoordinateEnvelope_le_normalized
    {U Q L N G : ℝ} (hU : 0 ≤ U) (hQ : 0 ≤ Q) (hL : 0 < L)
    (hLN : L ≤ N) (hG : 1 ≤ G) :
    4 * U * L * N + 4 * L * G + 8 * N + 8 * Q * G ≤
      24 * G * (U + 1 / L + Q / L ^ 2) * N ^ 2 := by
  have hN : 0 < N := hL.trans_le hLN
  have h1 : 4 * U * L * N ≤ 4 * G * U * N ^ 2 := by
    calc
      4 * U * L * N ≤ 4 * U * N * N := by
        have h := mul_le_mul_of_nonneg_left hLN
          (by positivity : 0 ≤ 4 * U * N)
        nlinarith
      _ ≤ 4 * G * U * N ^ 2 := by
        have h := mul_le_mul_of_nonneg_right hG
          (by positivity : 0 ≤ 4 * U * N ^ 2)
        nlinarith [sq_nonneg N]
  have hsq : L ^ 2 ≤ N ^ 2 := by gcongr
  have h2 : 4 * L * G ≤ 4 * G * (1 / L) * N ^ 2 := by
    calc
      4 * L * G = 4 * G * (1 / L) * L ^ 2 := by field_simp
      _ ≤ 4 * G * (1 / L) * N ^ 2 := by
        exact mul_le_mul_of_nonneg_left hsq (by positivity)
  have h3 : 8 * N ≤ 8 * G * (1 / L) * N ^ 2 := by
    calc
      8 * N = 8 * (1 / L) * L * N := by field_simp
      _ ≤ 8 * (1 / L) * N * N := by
        have h := mul_le_mul_of_nonneg_left hLN
          (by positivity : 0 ≤ 8 * (1 / L) * N)
        nlinarith
      _ ≤ 8 * G * (1 / L) * N ^ 2 := by
        have h := mul_le_mul_of_nonneg_right hG
          (by positivity : 0 ≤ 8 * (1 / L) * N ^ 2)
        nlinarith [sq_nonneg N]
  have h4 : 8 * Q * G ≤ 8 * G * (Q / L ^ 2) * N ^ 2 := by
    calc
      8 * Q * G = 8 * G * (Q / L ^ 2) * L ^ 2 := by field_simp
      _ ≤ 8 * G * (Q / L ^ 2) * N ^ 2 := by
        exact mul_le_mul_of_nonneg_left hsq (by positivity)
  calc
    4 * U * L * N + 4 * L * G + 8 * N + 8 * Q * G ≤
        4 * G * U * N ^ 2 + 4 * G * (1 / L) * N ^ 2 +
          8 * G * (1 / L) * N ^ 2 + 8 * G * (Q / L ^ 2) * N ^ 2 := by
      linarith
    _ ≤ 24 * G * (U + 1 / L + Q / L ^ 2) * N ^ 2 := by
      rw [show 24 * G * (U + 1 / L + Q / L ^ 2) * N ^ 2 =
          (4 * G * U * N ^ 2 + 4 * G * (1 / L) * N ^ 2 +
            8 * G * (1 / L) * N ^ 2 + 8 * G * (Q / L ^ 2) * N ^ 2) +
          (20 * G * U + 12 * G * (1 / L) + 16 * G * (Q / L ^ 2)) * N ^ 2 by
        ring]
      exact le_add_of_nonneg_right (by positivity)

/-- Normalized medium-coordinate saving. This is the direct coefficient-free
input for multiplying the good coordinates in Lemma 12. -/
theorem sum_norm_powerBoxSide_phase_le_mediumNormalized
    (c : ℕ → ℝ) (V ell degree : ℕ) (c₀ : ℝ) (hV : 1 ≤ V)
    (hell : 1 ≤ ell) (hc₀ : c₀ ≤ 2)
    (hmedium : IsVinogradovMediumCoefficient (V : ℝ) c₀ c degree) :
    (∑ x ∈ vinogradovPowerBoxSide ell V degree,
      ‖∑ y ∈ vinogradovPowerBoxSide ell V degree,
        standardAdditiveCharacter
          (c degree * (x : ℝ) * (y : ℝ))‖) ≤
      24 * (1 + Real.log 2 +
          ((2 - c₀) * (degree : ℝ)) * Real.log V) *
        ((V : ℝ) ^ (-c₀ * (degree : ℝ)) +
          1 / ((ell * V ^ degree : ℕ) : ℝ) +
          (V : ℝ) ^ ((2 - c₀) * (degree : ℝ)) /
            ((ell * V ^ degree : ℕ) : ℝ) ^ 2) *
        (((2 * (ell * V ^ degree) + 1 : ℕ) : ℝ)) ^ 2 := by
  let U : ℝ := (V : ℝ) ^ (-c₀ * (degree : ℝ))
  let Q : ℝ := (V : ℝ) ^ ((2 - c₀) * (degree : ℝ))
  let L : ℝ := ((ell * V ^ degree : ℕ) : ℝ)
  let N : ℝ := (((2 * (ell * V ^ degree) + 1 : ℕ) : ℝ))
  let G : ℝ := 1 + Real.log 2 +
    ((2 - c₀) * (degree : ℝ)) * Real.log V
  have hLnat : 1 ≤ ell * V ^ degree := by
    have hellPos : 0 < ell := zero_lt_one.trans_le hell
    have hVPos : 0 < V := zero_lt_one.trans_le hV
    exact Nat.one_le_iff_ne_zero.mpr
      (mul_ne_zero hellPos.ne' (pow_ne_zero degree hVPos.ne'))
  have hL : 0 < L := by
    dsimp only [L]
    exact_mod_cast (zero_lt_one.trans_le hLnat)
  have hLN : L ≤ N := by
    dsimp only [L, N]
    exact_mod_cast (show ell * V ^ degree ≤ 2 * (ell * V ^ degree) + 1 by omega)
  have hA : 0 ≤ (2 - c₀) * (degree : ℝ) :=
    mul_nonneg (sub_nonneg.mpr hc₀) (Nat.cast_nonneg _)
  have hlogV : 0 ≤ Real.log V := Real.log_nonneg (by exact_mod_cast hV)
  have hG : 1 ≤ G := by
    dsimp only [G]
    have hlogTwo : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    nlinarith [mul_nonneg hA hlogV]
  have hU : 0 ≤ U := by positivity
  have hQ : 0 ≤ Q := by positivity
  calc
    (∑ x ∈ vinogradovPowerBoxSide ell V degree,
      ‖∑ y ∈ vinogradovPowerBoxSide ell V degree,
        standardAdditiveCharacter
          (c degree * (x : ℝ) * (y : ℝ))‖) ≤
      4 * U * L * N + 4 * L * G + 8 * N + 8 * Q * G := by
        simpa only [U, Q, L, N, G] using
          sum_norm_powerBoxSide_phase_le_mediumExpandedLogEnvelope
            c V ell degree c₀ hV hc₀ hmedium
    _ ≤ 24 * G * (U + 1 / L + Q / L ^ 2) * N ^ 2 :=
      expanded_mediumCoordinateEnvelope_le_normalized hU hQ hL hLN hG
    _ = 24 * (1 + Real.log 2 +
          ((2 - c₀) * (degree : ℝ)) * Real.log V) *
        ((V : ℝ) ^ (-c₀ * (degree : ℝ)) +
          1 / ((ell * V ^ degree : ℕ) : ℝ) +
          (V : ℝ) ^ ((2 - c₀) * (degree : ℝ)) /
            ((ell * V ^ degree : ℕ) : ℝ) ^ 2) *
        (((2 * (ell * V ^ degree) + 1 : ℕ) : ℝ)) ^ 2 := by
      rfl

/-- The reciprocal box length is at most the medium-coordinate decay scale
when the medium exponent is at most one. -/
theorem one_div_vinogradovBoxLength_le_mediumPower
    (V ell degree : ℕ) (c₀ : ℝ) (hV : 1 ≤ V) (hell : 1 ≤ ell)
    (hc₀ : c₀ ≤ 1) :
    1 / ((ell * V ^ degree : ℕ) : ℝ) ≤
      (V : ℝ) ^ (-c₀ * (degree : ℝ)) := by
  have hVreal : (1 : ℝ) ≤ (V : ℝ) := by exact_mod_cast hV
  have hVpos : 0 < (V : ℝ) := zero_lt_one.trans_le hVreal
  have hpowpos : 0 < (((V ^ degree : ℕ) : ℝ)) := by positivity
  have hden : (((V ^ degree : ℕ) : ℝ)) ≤
      ((ell * V ^ degree : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_mul_of_pos_left (V ^ degree) (zero_lt_one.trans_le hell)
  calc
    1 / ((ell * V ^ degree : ℕ) : ℝ) ≤
        1 / (((V ^ degree : ℕ) : ℝ)) :=
      one_div_le_one_div_of_le hpowpos hden
    _ = (V : ℝ) ^ (-(degree : ℝ)) := by
      rw [Nat.cast_pow, ← Real.rpow_natCast, Real.rpow_neg hVpos.le]
      simp only [one_div]
    _ ≤ (V : ℝ) ^ (-c₀ * (degree : ℝ)) := by
      apply Real.rpow_le_rpow_of_exponent_le hVreal
      have hd : 0 ≤ (degree : ℝ) := Nat.cast_nonneg _
      nlinarith

/-- The upper medium-window power divided by the square box length has the
same decay scale as the lower medium-window power. -/
theorem mediumPower_div_vinogradovBoxLength_sq_le
    (V ell degree : ℕ) (c₀ : ℝ) (hV : 1 ≤ V) (hell : 1 ≤ ell) :
    (V : ℝ) ^ ((2 - c₀) * (degree : ℝ)) /
        ((ell * V ^ degree : ℕ) : ℝ) ^ 2 ≤
      (V : ℝ) ^ (-c₀ * (degree : ℝ)) := by
  have hVreal : (1 : ℝ) ≤ (V : ℝ) := by exact_mod_cast hV
  have hVpos : 0 < (V : ℝ) := zero_lt_one.trans_le hVreal
  have hinv : 1 / ((ell * V ^ degree : ℕ) : ℝ) ≤
      (V : ℝ) ^ (-(degree : ℝ)) := by
    simpa using
      one_div_vinogradovBoxLength_le_mediumPower
        V ell degree 1 hV hell le_rfl
  have hinv_nonneg : 0 ≤ 1 / ((ell * V ^ degree : ℕ) : ℝ) := by positivity
  have hsq : (1 / ((ell * V ^ degree : ℕ) : ℝ)) ^ 2 ≤
      ((V : ℝ) ^ (-(degree : ℝ))) ^ 2 :=
    pow_le_pow_left₀ hinv_nonneg hinv 2
  calc
    (V : ℝ) ^ ((2 - c₀) * (degree : ℝ)) /
        ((ell * V ^ degree : ℕ) : ℝ) ^ 2 =
      (V : ℝ) ^ ((2 - c₀) * (degree : ℝ)) *
        (1 / ((ell * V ^ degree : ℕ) : ℝ)) ^ 2 := by ring
    _ ≤ (V : ℝ) ^ ((2 - c₀) * (degree : ℝ)) *
        ((V : ℝ) ^ (-(degree : ℝ))) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = (V : ℝ) ^ (-c₀ * (degree : ℝ)) := by
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul hVpos.le]
      rw [← Real.rpow_add hVpos]
      congr 1
      ring

/-- The normalized scalar saving supplied by one medium coordinate. -/
noncomputable def vinogradovMediumCoordinateSaving
    (V ell degree : ℕ) (c₀ : ℝ) : ℝ :=
  24 * (1 + Real.log 2 +
      ((2 - c₀) * (degree : ℝ)) * Real.log V) *
    ((V : ℝ) ^ (-c₀ * (degree : ℝ)) +
      1 / ((ell * V ^ degree : ℕ) : ℝ) +
      (V : ℝ) ^ ((2 - c₀) * (degree : ℝ)) /
        ((ell * V ^ degree : ℕ) : ℝ) ^ 2)

theorem vinogradovMediumCoordinateSaving_nonneg
    (V ell degree : ℕ) (c₀ : ℝ) (hV : 1 ≤ V) (hc₀ : c₀ ≤ 2) :
    0 ≤ vinogradovMediumCoordinateSaving V ell degree c₀ := by
  have hVreal : (1 : ℝ) ≤ (V : ℝ) := by exact_mod_cast hV
  have hA : 0 ≤ (2 - c₀) * (degree : ℝ) :=
    mul_nonneg (sub_nonneg.mpr hc₀) (Nat.cast_nonneg _)
  have hlogV : 0 ≤ Real.log V := Real.log_nonneg hVreal
  have hlogTwo : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  unfold vinogradovMediumCoordinateSaving
  positivity

/-- All three terms in the normalized medium saving lie on the common
`V ^ (-c₀ * degree)` scale. -/
theorem vinogradovMediumCoordinateSaving_le_seventyTwo_mul
    (V ell degree : ℕ) (c₀ : ℝ) (hV : 1 ≤ V) (hell : 1 ≤ ell)
    (hc₀ : c₀ ≤ 1) :
    vinogradovMediumCoordinateSaving V ell degree c₀ ≤
      72 * (1 + Real.log 2 +
        ((2 - c₀) * (degree : ℝ)) * Real.log V) *
        (V : ℝ) ^ (-c₀ * (degree : ℝ)) := by
  let G : ℝ := 1 + Real.log 2 +
    ((2 - c₀) * (degree : ℝ)) * Real.log V
  let U : ℝ := (V : ℝ) ^ (-c₀ * (degree : ℝ))
  have hVreal : (1 : ℝ) ≤ (V : ℝ) := by exact_mod_cast hV
  have hlogV : 0 ≤ Real.log V := Real.log_nonneg hVreal
  have hG : 0 ≤ G := by
    dsimp only [G]
    have hlogTwo : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hA : 0 ≤ (2 - c₀) * (degree : ℝ) :=
      mul_nonneg (by linarith) (Nat.cast_nonneg _)
    positivity
  have hinv : 1 / ((ell * V ^ degree : ℕ) : ℝ) ≤ U := by
    simpa only [U] using
      one_div_vinogradovBoxLength_le_mediumPower V ell degree c₀ hV hell hc₀
  have hquot : (V : ℝ) ^ ((2 - c₀) * (degree : ℝ)) /
      ((ell * V ^ degree : ℕ) : ℝ) ^ 2 ≤ U := by
    simpa only [U] using
      mediumPower_div_vinogradovBoxLength_sq_le V ell degree c₀ hV hell
  have hsum : U + 1 / ((ell * V ^ degree : ℕ) : ℝ) +
      (V : ℝ) ^ ((2 - c₀) * (degree : ℝ)) /
        ((ell * V ^ degree : ℕ) : ℝ) ^ 2 ≤ 3 * U := by
    linarith
  calc
    vinogradovMediumCoordinateSaving V ell degree c₀ =
        24 * G * (U + 1 / ((ell * V ^ degree : ℕ) : ℝ) +
          (V : ℝ) ^ ((2 - c₀) * (degree : ℝ)) /
            ((ell * V ^ degree : ℕ) : ℝ) ^ 2) := by rfl
    _ ≤ 24 * G * (3 * U) :=
      mul_le_mul_of_nonneg_left hsum (mul_nonneg (by norm_num) hG)
    _ = 72 * G * U := by ring
    _ = 72 * (1 + Real.log 2 +
        ((2 - c₀) * (degree : ℝ)) * Real.log V) *
        (V : ℝ) ^ (-c₀ * (degree : ℝ)) := by rfl

/-- Once the explicit logarithmic prefactor is absorbed by half of the
medium exponent, a medium coordinate supplies a fixed negative power. -/
theorem vinogradovMediumCoordinateSaving_le_rpow_half
    (V ell degree : ℕ) (c₀ : ℝ) (hV : 1 ≤ V) (hell : 1 ≤ ell)
    (hc₀ : c₀ ≤ 1)
    (hgrowth :
      72 * (1 + Real.log 2 +
        ((2 - c₀) * (degree : ℝ)) * Real.log V) ≤
        (V : ℝ) ^ ((c₀ / 2) * (degree : ℝ))) :
    vinogradovMediumCoordinateSaving V ell degree c₀ ≤
      (V : ℝ) ^ (-(c₀ / 2) * (degree : ℝ)) := by
  have hVreal : (1 : ℝ) ≤ (V : ℝ) := by exact_mod_cast hV
  have hVpos : 0 < (V : ℝ) := zero_lt_one.trans_le hVreal
  calc
    vinogradovMediumCoordinateSaving V ell degree c₀ ≤
        72 * (1 + Real.log 2 +
          ((2 - c₀) * (degree : ℝ)) * Real.log V) *
          (V : ℝ) ^ (-c₀ * (degree : ℝ)) :=
      vinogradovMediumCoordinateSaving_le_seventyTwo_mul
        V ell degree c₀ hV hell hc₀
    _ ≤ (V : ℝ) ^ ((c₀ / 2) * (degree : ℝ)) *
        (V : ℝ) ^ (-c₀ * (degree : ℝ)) :=
      mul_le_mul_of_nonneg_right hgrowth (by positivity)
    _ = (V : ℝ) ^ (-(c₀ / 2) * (degree : ℝ)) := by
      rw [← Real.rpow_add hVpos]
      congr 1
      ring

/-- A parameterized version of the scalar absorption step. If the logarithmic
prefactor costs only `η*degree`, a medium coordinate retains the full exponent
`(c₀-η)*degree`; no artificial loss of half of `c₀` is imposed. -/
theorem vinogradovMediumCoordinateSaving_le_rpow_of_absorption
    (V ell degree : ℕ) (c₀ η : ℝ) (hV : 1 ≤ V) (hell : 1 ≤ ell)
    (hc₀ : c₀ ≤ 1)
    (hgrowth :
      72 * (1 + Real.log 2 +
        ((2 - c₀) * (degree : ℝ)) * Real.log V) ≤
        (V : ℝ) ^ (η * (degree : ℝ))) :
    vinogradovMediumCoordinateSaving V ell degree c₀ ≤
      (V : ℝ) ^ (-(c₀ - η) * (degree : ℝ)) := by
  have hVreal : (1 : ℝ) ≤ (V : ℝ) := by exact_mod_cast hV
  have hVpos : 0 < (V : ℝ) := zero_lt_one.trans_le hVreal
  calc
    vinogradovMediumCoordinateSaving V ell degree c₀ ≤
        72 * (1 + Real.log 2 +
          ((2 - c₀) * (degree : ℝ)) * Real.log V) *
          (V : ℝ) ^ (-c₀ * (degree : ℝ)) :=
      vinogradovMediumCoordinateSaving_le_seventyTwo_mul
        V ell degree c₀ hV hell hc₀
    _ ≤ (V : ℝ) ^ (η * (degree : ℝ)) *
        (V : ℝ) ^ (-c₀ * (degree : ℝ)) :=
      mul_le_mul_of_nonneg_right hgrowth (by positivity)
    _ = (V : ℝ) ^ (-(c₀ - η) * (degree : ℝ)) := by
      rw [← Real.rpow_add hVpos]
      congr 1
      ring

/-- A coordinate contributes its normalized saving precisely when it lies in
the medium window, and contributes one otherwise. -/
noncomputable def vinogradovMediumCoordinateSavingFactor
    (c : ℕ → ℝ) (V ell degree : ℕ) (c₀ : ℝ) : ℝ := by
  classical
  exact if IsVinogradovMediumCoefficient (V : ℝ) c₀ c degree
    then vinogradovMediumCoordinateSaving V ell degree c₀ else 1

theorem vinogradovMediumCoordinateSavingFactor_nonneg
    (c : ℕ → ℝ) (V ell degree : ℕ) (c₀ : ℝ)
    (hV : 1 ≤ V) (hc₀ : c₀ ≤ 2) :
    0 ≤ vinogradovMediumCoordinateSavingFactor c V ell degree c₀ := by
  rw [vinogradovMediumCoordinateSavingFactor]
  split_ifs
  · exact vinogradovMediumCoordinateSaving_nonneg V ell degree c₀ hV hc₀
  · norm_num

/-- Under the explicit scalar growth condition, the coordinate factor is a
fixed negative power on the medium window and one off that window. -/
theorem vinogradovMediumCoordinateSavingFactor_le_rpow_half
    (c : ℕ → ℝ) (V ell degree : ℕ) (c₀ : ℝ)
    (hV : 1 ≤ V) (hell : 1 ≤ ell) (hc₀ : c₀ ≤ 1)
    (hgrowth :
      72 * (1 + Real.log 2 +
        ((2 - c₀) * (degree : ℝ)) * Real.log V) ≤
        (V : ℝ) ^ ((c₀ / 2) * (degree : ℝ))) :
    vinogradovMediumCoordinateSavingFactor c V ell degree c₀ ≤
      (by classical exact
        if IsVinogradovMediumCoefficient (V : ℝ) c₀ c degree
        then (V : ℝ) ^ (-(c₀ / 2) * (degree : ℝ)) else 1) := by
  rw [vinogradovMediumCoordinateSavingFactor]
  split_ifs
  · exact vinogradovMediumCoordinateSaving_le_rpow_half
      V ell degree c₀ hV hell hc₀ hgrowth
  · exact le_rfl

/-- Multiplying the coordinatewise estimate converts the medium-coordinate
product into a product of explicit negative powers. -/
theorem prod_mediumSavingFactor_le_prod_rpow_half
    (c : ℕ → ℝ) (V ell R : ℕ) (c₀ : ℝ)
    (hV : 1 ≤ V) (hell : 1 ≤ ell) (hc₀ : c₀ ≤ 1)
    (hgrowth : ∀ j : Fin R,
      72 * (1 + Real.log 2 +
        ((2 - c₀) * ((j.1 + 1 : ℕ) : ℝ)) * Real.log V) ≤
        (V : ℝ) ^ ((c₀ / 2) * ((j.1 + 1 : ℕ) : ℝ))) :
    (∏ j : Fin R,
      vinogradovMediumCoordinateSavingFactor c V ell (j.1 + 1) c₀) ≤
      ∏ j : Fin R,
        (by classical exact
          if IsVinogradovMediumCoefficient (V : ℝ) c₀ c (j.1 + 1)
          then (V : ℝ) ^ (-(c₀ / 2) * ((j.1 + 1 : ℕ) : ℝ)) else 1) := by
  apply Finset.prod_le_prod
  · intro j hj
    exact vinogradovMediumCoordinateSavingFactor_nonneg
      c V ell (j.1 + 1) c₀ hV (hc₀.trans (by norm_num))
  · intro j hj
    exact vinogradovMediumCoordinateSavingFactor_le_rpow_half
      c V ell (j.1 + 1) c₀ hV hell hc₀ (hgrowth j)

/-- A finite product of real powers with a common positive base is the power
whose exponent is the corresponding finite sum. -/
theorem finset_prod_rpow_eq_rpow_sum
    {ι : Type*} (s : Finset ι) (V : ℝ) (a : ι → ℝ) (hV : 0 < V) :
    (∏ i ∈ s, V ^ a i) = V ^ (∑ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, Real.rpow_add hV]

/-- Reindex a product over `Fin R` by its positive degree `j + 1`. -/
theorem prod_fin_succ_eq_prod_Icc
    {M : Type*} [CommMonoid M] (R : ℕ) (f : ℕ → M) :
    (∏ j : Fin R, f (j.1 + 1)) = ∏ r ∈ Finset.Icc 1 R, f r := by
  classical
  refine Finset.prod_bij (fun j _ => j.1 + 1) ?_ ?_ ?_ ?_
  · intro j hj
    simp only [Finset.mem_Icc]
    omega
  · intro j₁ hj₁ j₂ hj₂ heq
    change j₁.val + 1 = j₂.val + 1 at heq
    apply Fin.ext
    exact Nat.add_right_cancel heq
  · intro r hr
    simp only [Finset.mem_Icc] at hr
    refine ⟨⟨r - 1, by omega⟩, Finset.mem_univ _, ?_⟩
    change (r - 1) + 1 = r
    omega
  · intro j hj
    rfl

/-- The product of the conditional medium-coordinate powers is exactly one
power with exponent the negative weighted sum of all medium degrees. -/
theorem prod_mediumDecay_eq_rpow_sum_mediumIndices
    (c : ℕ → ℝ) (V R : ℕ) (c₀ : ℝ) (hV : 1 ≤ V) :
    (∏ j : Fin R,
      (by classical exact
        if IsVinogradovMediumCoefficient (V : ℝ) c₀ c (j.1 + 1)
        then (V : ℝ) ^ (-(c₀ / 2) * ((j.1 + 1 : ℕ) : ℝ)) else 1)) =
      (V : ℝ) ^
        (∑ r ∈ vinogradovMediumCoefficientIndices (V : ℝ) c₀ c R,
          -(c₀ / 2) * (r : ℝ)) := by
  classical
  calc
    (∏ j : Fin R,
      if IsVinogradovMediumCoefficient (V : ℝ) c₀ c (j.1 + 1)
      then (V : ℝ) ^ (-(c₀ / 2) * ((j.1 + 1 : ℕ) : ℝ)) else 1) =
        ∏ r ∈ Finset.Icc 1 R,
          if IsVinogradovMediumCoefficient (V : ℝ) c₀ c r
          then (V : ℝ) ^ (-(c₀ / 2) * (r : ℝ)) else 1 := by
      exact prod_fin_succ_eq_prod_Icc R (fun r =>
        if IsVinogradovMediumCoefficient (V : ℝ) c₀ c r
        then (V : ℝ) ^ (-(c₀ / 2) * (r : ℝ)) else 1)
    _ = ∏ r ∈ vinogradovMediumCoefficientIndices (V : ℝ) c₀ c R,
          (V : ℝ) ^ (-(c₀ / 2) * (r : ℝ)) := by
      rw [vinogradovMediumCoefficientIndices, Finset.prod_filter]
    _ = (V : ℝ) ^
        (∑ r ∈ vinogradovMediumCoefficientIndices (V : ℝ) c₀ c R,
          -(c₀ / 2) * (r : ℝ)) :=
      finset_prod_rpow_eq_rpow_sum _ _ _
        (zero_lt_one.trans_le (by exact_mod_cast hV))

/-- The full product of normalized coordinate savings is controlled by the
single power attached to the weighted sum of the medium degrees. -/
theorem prod_mediumSavingFactor_le_rpow_sum_mediumIndices
    (c : ℕ → ℝ) (V ell R : ℕ) (c₀ : ℝ)
    (hV : 1 ≤ V) (hell : 1 ≤ ell) (hc₀ : c₀ ≤ 1)
    (hgrowth : ∀ j : Fin R,
      72 * (1 + Real.log 2 +
        ((2 - c₀) * ((j.1 + 1 : ℕ) : ℝ)) * Real.log V) ≤
        (V : ℝ) ^ ((c₀ / 2) * ((j.1 + 1 : ℕ) : ℝ))) :
    (∏ j : Fin R,
      vinogradovMediumCoordinateSavingFactor c V ell (j.1 + 1) c₀) ≤
      (V : ℝ) ^
        (∑ r ∈ vinogradovMediumCoefficientIndices (V : ℝ) c₀ c R,
          -(c₀ / 2) * (r : ℝ)) := by
  calc
    (∏ j : Fin R,
      vinogradovMediumCoordinateSavingFactor c V ell (j.1 + 1) c₀) ≤
        ∏ j : Fin R,
          (by classical exact
            if IsVinogradovMediumCoefficient (V : ℝ) c₀ c (j.1 + 1)
            then (V : ℝ) ^ (-(c₀ / 2) * ((j.1 + 1 : ℕ) : ℝ)) else 1) :=
      prod_mediumSavingFactor_le_prod_rpow_half
        c V ell R c₀ hV hell hc₀ hgrowth
    _ = (V : ℝ) ^
        (∑ r ∈ vinogradovMediumCoefficientIndices (V : ℝ) c₀ c R,
          -(c₀ / 2) * (r : ℝ)) :=
      prod_mediumDecay_eq_rpow_sum_mediumIndices c V R c₀ hV

/-- A lower bound for the sum of medium degrees turns the exact weighted
exponent into a corresponding fixed negative power. -/
theorem prod_mediumSavingFactor_le_rpow_of_sum_lower
    (c : ℕ → ℝ) (V ell R : ℕ) (c₀ K : ℝ)
    (hV : 1 ≤ V) (hell : 1 ≤ ell) (hc₀nonneg : 0 ≤ c₀) (hc₀ : c₀ ≤ 1)
    (hgrowth : ∀ j : Fin R,
      72 * (1 + Real.log 2 +
        ((2 - c₀) * ((j.1 + 1 : ℕ) : ℝ)) * Real.log V) ≤
        (V : ℝ) ^ ((c₀ / 2) * ((j.1 + 1 : ℕ) : ℝ)))
    (hsum : K ≤
      ∑ r ∈ vinogradovMediumCoefficientIndices (V : ℝ) c₀ c R,
        (r : ℝ)) :
    (∏ j : Fin R,
      vinogradovMediumCoordinateSavingFactor c V ell (j.1 + 1) c₀) ≤
      (V : ℝ) ^ (-(c₀ / 2) * K) := by
  have hVreal : (1 : ℝ) ≤ (V : ℝ) := by exact_mod_cast hV
  have ha : 0 ≤ c₀ / 2 := div_nonneg hc₀nonneg (by norm_num)
  calc
    (∏ j : Fin R,
      vinogradovMediumCoordinateSavingFactor c V ell (j.1 + 1) c₀) ≤
        (V : ℝ) ^
          (∑ r ∈ vinogradovMediumCoefficientIndices (V : ℝ) c₀ c R,
            -(c₀ / 2) * (r : ℝ)) :=
      prod_mediumSavingFactor_le_rpow_sum_mediumIndices
        c V ell R c₀ hV hell hc₀ hgrowth
    _ = (V : ℝ) ^ (-(c₀ / 2) *
          (∑ r ∈ vinogradovMediumCoefficientIndices (V : ℝ) c₀ c R,
            (r : ℝ))) := by
      congr 1
      rw [Finset.mul_sum]
    _ ≤ (V : ℝ) ^ (-(c₀ / 2) * K) := by
      apply Real.rpow_le_rpow_of_exponent_le hVreal
      exact mul_le_mul_of_nonpos_left hsum (neg_nonpos.mpr ha)

/-- Product form of the parameterized absorption step. A lower bound for the
weighted set of medium degrees retains `c₀-η` of every degree in that set. -/
theorem prod_mediumSavingFactor_le_rpow_of_sum_lower_of_absorption
    (c : ℕ → ℝ) (V ell R : ℕ) (c₀ η K : ℝ)
    (hV : 1 ≤ V) (hell : 1 ≤ ell) (hc₀ : c₀ ≤ 1) (hη : 0 ≤ c₀ - η)
    (hgrowth : ∀ j : Fin R,
      72 * (1 + Real.log 2 +
        ((2 - c₀) * ((j.1 + 1 : ℕ) : ℝ)) * Real.log V) ≤
        (V : ℝ) ^ (η * ((j.1 + 1 : ℕ) : ℝ)))
    (hsum : K ≤
      ∑ r ∈ vinogradovMediumCoefficientIndices (V : ℝ) c₀ c R,
        (r : ℝ)) :
    (∏ j : Fin R,
      vinogradovMediumCoordinateSavingFactor c V ell (j.1 + 1) c₀) ≤
      (V : ℝ) ^ (-(c₀ - η) * K) := by
  classical
  have hVreal : (1 : ℝ) ≤ (V : ℝ) := by exact_mod_cast hV
  have hVpos : 0 < (V : ℝ) := zero_lt_one.trans_le hVreal
  calc
    (∏ j : Fin R,
      vinogradovMediumCoordinateSavingFactor c V ell (j.1 + 1) c₀) ≤
        ∏ j : Fin R,
          if IsVinogradovMediumCoefficient (V : ℝ) c₀ c (j.1 + 1)
          then (V : ℝ) ^ (-(c₀ - η) * ((j.1 + 1 : ℕ) : ℝ)) else 1 := by
      apply Finset.prod_le_prod
      · intro j hj
        exact vinogradovMediumCoordinateSavingFactor_nonneg
          c V ell (j.1 + 1) c₀ hV (hc₀.trans (by norm_num))
      · intro j hj
        rw [vinogradovMediumCoordinateSavingFactor]
        split_ifs with hmedium
        · exact vinogradovMediumCoordinateSaving_le_rpow_of_absorption
            V ell (j.1 + 1) c₀ η hV hell hc₀ (hgrowth j)
        · exact le_rfl
    _ = ∏ r ∈ Finset.Icc 1 R,
          if IsVinogradovMediumCoefficient (V : ℝ) c₀ c r
          then (V : ℝ) ^ (-(c₀ - η) * (r : ℝ)) else 1 := by
      exact prod_fin_succ_eq_prod_Icc R (fun r =>
        if IsVinogradovMediumCoefficient (V : ℝ) c₀ c r
        then (V : ℝ) ^ (-(c₀ - η) * (r : ℝ)) else 1)
    _ = ∏ r ∈ vinogradovMediumCoefficientIndices (V : ℝ) c₀ c R,
          (V : ℝ) ^ (-(c₀ - η) * (r : ℝ)) := by
      rw [vinogradovMediumCoefficientIndices, Finset.prod_filter]
    _ = (V : ℝ) ^
        (∑ r ∈ vinogradovMediumCoefficientIndices (V : ℝ) c₀ c R,
          -(c₀ - η) * (r : ℝ)) :=
      finset_prod_rpow_eq_rpow_sum _ _ _ hVpos
    _ = (V : ℝ) ^ (-(c₀ - η) *
          (∑ r ∈ vinogradovMediumCoefficientIndices (V : ℝ) c₀ c R,
            (r : ℝ))) := by
      congr 1
      rw [Finset.mul_sum]
    _ ≤ (V : ℝ) ^ (-(c₀ - η) * K) := by
      apply Real.rpow_le_rpow_of_exponent_le hVreal
      exact mul_le_mul_of_nonpos_left hsum (neg_nonpos.mpr hη)

/-- The explicit source block gives a quadratic lower bound for the sum,
not merely the count, of the actual medium Taylor degrees. -/
theorem vinogradovTaylorDegree_sq_div_1200_le_sum_mediumDegrees
    {X F α : ℝ} {n : ℕ} {c : ℕ → ℝ}
    (hX : 2 ≤ X) (hFhigh : X ^ 4 ≤ F) (hα : 1 ≤ α)
    (hn : (n : ℝ) ∈ Set.Icc X (2 * X))
    (hcoeff : ∀ r : ℕ, 1 ≤ r → r ≤ vinogradovTaylorDegree X F →
      F / α ^ (r ^ 3) ≤ (n : ℝ) ^ r * |c r| ∧
        (n : ℝ) ^ r * |c r| ≤ α ^ (r ^ 3) * F)
    (hsmall : 2 * α * Real.exp
      (-((2 : ℝ) ^ (-18 : ℝ)) * (Real.log X) ^ 3 /
        (Real.log F) ^ 2) < 1) :
    (vinogradovTaylorDegree X F : ℝ) ^ 2 / 1200 ≤
      ∑ r ∈ vinogradovMediumCoefficientIndices
        (vinogradovAveragingRange X : ℝ) (1 / 128) c
        (vinogradovTaylorDegree X F), (r : ℝ) := by
  have hXpos : 0 < X := by linarith
  have hlogX : 0 < Real.log X := Real.log_pos (by linarith)
  have hFpos : 0 < F := (pow_pos hXpos 4).trans_le hFhigh
  let s : ℝ := Real.log F / Real.log X
  have hs : 4 ≤ s := by
    dsimp only [s]
    rw [le_div_iff₀ hlogX]
    calc
      4 * Real.log X = Real.log (X ^ 4) := by
        rw [Real.log_pow]
        norm_num
      _ ≤ Real.log F := Real.strictMonoOn_log.monotoneOn
        (Set.mem_Ioi.mpr (pow_pos hXpos 4)) (Set.mem_Ioi.mpr hFpos) hFhigh
  have hratio : 0 ≤ Real.log F / Real.log X := by
    dsimp only [s] at hs
    linarith
  have hsubset : vinogradovMediumDegreeBlock X F ⊆
      vinogradovMediumCoefficientIndices
        (vinogradovAveragingRange X : ℝ) (1 / 128) c
        (vinogradovTaylorDegree X F) := by
    intro r hr
    obtain ⟨hrlow, hrupp⟩ :=
      mem_vinogradovMediumDegreeBlock_bounds hratio hr
    obtain ⟨hrone, hrR⟩ :=
      mem_vinogradovMediumDegreeBlock_degree hX hFhigh hr
    rw [mem_vinogradovMediumCoefficientIndices]
    exact ⟨hrone, hrR,
      isVinogradovMediumCoefficient_one_div_128_of_sourceBlock
        hX hFhigh hα hn hrone hrlow hrupp (hcoeff r hrone hrR) hsmall⟩
  have hcard :=
    vinogradovTaylorDegree_div_128_le_card_mediumDegreeBlock hX hFhigh
  have hblockSum :
      ((vinogradovMediumDegreeBlock X F).card : ℝ) * ((4 / 3 : ℝ) * s) ≤
        ∑ r ∈ vinogradovMediumDegreeBlock X F, (r : ℝ) := by
    calc
      ((vinogradovMediumDegreeBlock X F).card : ℝ) * ((4 / 3 : ℝ) * s) =
          ∑ r ∈ vinogradovMediumDegreeBlock X F, ((4 / 3 : ℝ) * s) := by
        simp
      _ ≤ ∑ r ∈ vinogradovMediumDegreeBlock X F, (r : ℝ) := by
        apply Finset.sum_le_sum
        intro r hr
        exact (mem_vinogradovMediumDegreeBlock_bounds hratio hr).1
  have hsumSubset :
      (∑ r ∈ vinogradovMediumDegreeBlock X F, (r : ℝ)) ≤
        ∑ r ∈ vinogradovMediumCoefficientIndices
          (vinogradovAveragingRange X : ℝ) (1 / 128) c
          (vinogradovTaylorDegree X F), (r : ℝ) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun r hr hnot => Nat.cast_nonneg r)
  have hceil : (⌈s⌉₊ : ℝ) < s + 1 :=
    Nat.ceil_lt_add_one (by linarith)
  have hRupper : (vinogradovTaylorDegree X F : ℝ) < 10 * (s + 1) := by
    rw [vinogradovTaylorDegree]
    push_cast
    dsimp only [s] at hceil ⊢
    linarith
  have hsR : (2 / 25 : ℝ) * (vinogradovTaylorDegree X F : ℝ) ≤ s := by
    nlinarith
  have hRnonneg : 0 ≤ (vinogradovTaylorDegree X F : ℝ) := by positivity
  have hscaleNonneg : 0 ≤ (4 / 3 : ℝ) * s := by positivity
  have hcardScale :
      (vinogradovTaylorDegree X F : ℝ) / 128 * ((4 / 3 : ℝ) * s) ≤
        ((vinogradovMediumDegreeBlock X F).card : ℝ) * ((4 / 3 : ℝ) * s) :=
    mul_le_mul_of_nonneg_right hcard hscaleNonneg
  have hquad :
      (vinogradovTaylorDegree X F : ℝ) ^ 2 / 1200 ≤
        (vinogradovTaylorDegree X F : ℝ) / 128 * ((4 / 3 : ℝ) * s) := by
    nlinarith [mul_nonneg hRnonneg (sub_nonneg.mpr hsR)]
  exact hquad.trans (hcardScale.trans (hblockSum.trans hsumSubset))

/-- The explicit source degree block itself has quadratic total weight. This
coefficient-independent form allows the same arithmetic block to be used at
the native medium-window separation `c₀=1/8`. -/
theorem vinogradovTaylorDegree_sq_div_1200_le_sum_mediumDegreeBlock
    {X F : ℝ} (hX : 2 ≤ X) (hFhigh : X ^ 4 ≤ F) :
    (vinogradovTaylorDegree X F : ℝ) ^ 2 / 1200 ≤
      ∑ r ∈ vinogradovMediumDegreeBlock X F, (r : ℝ) := by
  have hXpos : 0 < X := by linarith
  have hlogX : 0 < Real.log X := Real.log_pos (by linarith)
  have hFpos : 0 < F := (pow_pos hXpos 4).trans_le hFhigh
  let s : ℝ := Real.log F / Real.log X
  have hs : 4 ≤ s := by
    dsimp only [s]
    rw [le_div_iff₀ hlogX]
    calc
      4 * Real.log X = Real.log (X ^ 4) := by
        rw [Real.log_pow]
        norm_num
      _ ≤ Real.log F := Real.strictMonoOn_log.monotoneOn
        (Set.mem_Ioi.mpr (pow_pos hXpos 4)) (Set.mem_Ioi.mpr hFpos) hFhigh
  have hratio : 0 ≤ Real.log F / Real.log X := by
    dsimp only [s] at hs
    linarith
  have hcard :=
    vinogradovTaylorDegree_div_128_le_card_mediumDegreeBlock hX hFhigh
  have hblockSum :
      ((vinogradovMediumDegreeBlock X F).card : ℝ) * ((4 / 3 : ℝ) * s) ≤
        ∑ r ∈ vinogradovMediumDegreeBlock X F, (r : ℝ) := by
    calc
      ((vinogradovMediumDegreeBlock X F).card : ℝ) * ((4 / 3 : ℝ) * s) =
          ∑ r ∈ vinogradovMediumDegreeBlock X F, ((4 / 3 : ℝ) * s) := by
        simp
      _ ≤ ∑ r ∈ vinogradovMediumDegreeBlock X F, (r : ℝ) := by
        apply Finset.sum_le_sum
        intro r hr
        exact (mem_vinogradovMediumDegreeBlock_bounds hratio hr).1
  have hceil : (⌈s⌉₊ : ℝ) < s + 1 :=
    Nat.ceil_lt_add_one (by linarith)
  have hRupper : (vinogradovTaylorDegree X F : ℝ) < 10 * (s + 1) := by
    rw [vinogradovTaylorDegree]
    push_cast
    dsimp only [s] at hceil ⊢
    linarith
  have hsR : (2 / 25 : ℝ) * (vinogradovTaylorDegree X F : ℝ) ≤ s := by
    nlinarith
  have hRnonneg : 0 ≤ (vinogradovTaylorDegree X F : ℝ) := by positivity
  have hscaleNonneg : 0 ≤ (4 / 3 : ℝ) * s := by positivity
  have hcardScale :
      (vinogradovTaylorDegree X F : ℝ) / 128 * ((4 / 3 : ℝ) * s) ≤
        ((vinogradovMediumDegreeBlock X F).card : ℝ) * ((4 / 3 : ℝ) * s) :=
    mul_le_mul_of_nonneg_right hcard hscaleNonneg
  have hquad :
      (vinogradovTaylorDegree X F : ℝ) ^ 2 / 1200 ≤
        (vinogradovTaylorDegree X F : ℝ) / 128 * ((4 / 3 : ℝ) * s) := by
    nlinarith [mul_nonneg hRnonneg (sub_nonneg.mpr hsR)]
  exact hquad.trans (hcardScale.trans hblockSum)

/-- The source Taylor degree is nontrivial throughout the high-scale branch;
in fact the assumption `X^4 ≤ F` forces at least forty degrees. -/
theorem forty_le_vinogradovTaylorDegree
    {X F : ℝ} (hX : 2 ≤ X) (hFhigh : X ^ 4 ≤ F) :
    40 ≤ vinogradovTaylorDegree X F := by
  have hXpos : 0 < X := by linarith
  have hlogX : 0 < Real.log X := Real.log_pos (by linarith)
  have hFpos : 0 < F := (pow_pos hXpos 4).trans_le hFhigh
  have hs : 4 ≤ Real.log F / Real.log X := by
    rw [le_div_iff₀ hlogX]
    calc
      4 * Real.log X = Real.log (X ^ 4) := by
        rw [Real.log_pow]
        norm_num
      _ ≤ Real.log F := Real.strictMonoOn_log.monotoneOn
        (Set.mem_Ioi.mpr (pow_pos hXpos 4)) (Set.mem_Ioi.mpr hFpos) hFhigh
  have hceil : 4 ≤ ⌈Real.log F / Real.log X⌉₊ := by
    exact_mod_cast hs.trans (Nat.le_ceil _)
  rw [vinogradovTaylorDegree]
  omega

/-- The same quadratic block weight lies inside the genuinely stronger
`c₀=1/8` medium set; no weakening to `1/128` is needed. -/
theorem vinogradovTaylorDegree_sq_div_1200_le_sum_mediumDegrees_eighth
    {X F α : ℝ} {n : ℕ} {c : ℕ → ℝ}
    (hX : 2 ≤ X) (hFhigh : X ^ 4 ≤ F) (hα : 1 ≤ α)
    (hn : (n : ℝ) ∈ Set.Icc X (2 * X))
    (hcoeff : ∀ r : ℕ, 1 ≤ r → r ≤ vinogradovTaylorDegree X F →
      F / α ^ (r ^ 3) ≤ (n : ℝ) ^ r * |c r| ∧
        (n : ℝ) ^ r * |c r| ≤ α ^ (r ^ 3) * F)
    (hsmall : 2 * α * Real.exp
      (-((2 : ℝ) ^ (-18 : ℝ)) * (Real.log X) ^ 3 /
        (Real.log F) ^ 2) < 1) :
    (vinogradovTaylorDegree X F : ℝ) ^ 2 / 1200 ≤
      ∑ r ∈ vinogradovMediumCoefficientIndices
        (vinogradovAveragingRange X : ℝ) (1 / 8) c
        (vinogradovTaylorDegree X F), (r : ℝ) := by
  have hratio : 0 ≤ Real.log F / Real.log X := by
    have hXpos : 0 < X := by linarith
    have hlogX : 0 < Real.log X := Real.log_pos (by linarith)
    have hFone : 1 ≤ F := by
      calc
        1 ≤ X ^ 4 := by nlinarith [sq_nonneg (X ^ 2 - 1)]
        _ ≤ F := hFhigh
    exact div_nonneg (Real.log_nonneg hFone) hlogX.le
  have hsubset : vinogradovMediumDegreeBlock X F ⊆
      vinogradovMediumCoefficientIndices
        (vinogradovAveragingRange X : ℝ) (1 / 8) c
        (vinogradovTaylorDegree X F) := by
    intro r hr
    obtain ⟨hrlow, hrupp⟩ :=
      mem_vinogradovMediumDegreeBlock_bounds hratio hr
    obtain ⟨hrone, hrR⟩ :=
      mem_vinogradovMediumDegreeBlock_degree hX hFhigh hr
    rw [mem_vinogradovMediumCoefficientIndices]
    exact ⟨hrone, hrR,
      isVinogradovMediumCoefficient_eighth_of_sourceBlock
        hX hFhigh hα hn hrone hrlow hrupp (hcoeff r hrone hrR) hsmall⟩
  exact (vinogradovTaylorDegree_sq_div_1200_le_sum_mediumDegreeBlock
      hX hFhigh).trans
    (Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun r hr hnot => Nat.cast_nonneg r))

/-- The widened sharp block supplies the stronger weighted lower bound
`R²/160` inside the genuine `c₀=1/8` medium-coordinate set. -/
theorem vinogradovTaylorDegree_sq_div_160_le_sum_mediumDegrees_sharp
    {X F α : ℝ} {n : ℕ} {c : ℕ → ℝ}
    (hX : 2 ≤ X) (hFhigh : X ^ 4 ≤ F) (hα : 1 ≤ α)
    (hn : (n : ℝ) ∈ Set.Icc X (2 * X))
    (hcoeff : ∀ r : ℕ, 1 ≤ r → r ≤ vinogradovTaylorDegree X F →
      F / α ^ (r ^ 3) ≤ (n : ℝ) ^ r * |c r| ∧
        (n : ℝ) ^ r * |c r| ≤ α ^ (r ^ 3) * F)
    (hsmall : 2 * α * Real.exp
      (-((2 : ℝ) ^ (-18 : ℝ)) * (Real.log X) ^ 3 /
        (Real.log F) ^ 2) < 1) :
    (vinogradovTaylorDegree X F : ℝ) ^ 2 / 160 ≤
      ∑ r ∈ vinogradovMediumCoefficientIndices
        (vinogradovAveragingRange X : ℝ) (1 / 8) c
        (vinogradovTaylorDegree X F), (r : ℝ) := by
  have hratio : 0 ≤ Real.log F / Real.log X := by
    have hXpos : 0 < X := by linarith
    have hlogX : 0 < Real.log X := Real.log_pos (by linarith)
    have hFone : 1 ≤ F := by
      calc
        1 ≤ X ^ 4 := by nlinarith [sq_nonneg (X ^ 2 - 1)]
        _ ≤ F := hFhigh
    exact div_nonneg (Real.log_nonneg hFone) hlogX.le
  have hsubset : vinogradovSharpMediumDegreeBlock X F ⊆
      vinogradovMediumCoefficientIndices
        (vinogradovAveragingRange X : ℝ) (1 / 8) c
        (vinogradovTaylorDegree X F) := by
    intro r hr
    obtain ⟨hrlow, hrupp⟩ :=
      mem_vinogradovSharpMediumDegreeBlock_bounds hratio hr
    obtain ⟨hrone, hrR⟩ :=
      mem_vinogradovSharpMediumDegreeBlock_degree hX hFhigh hr
    rw [mem_vinogradovMediumCoefficientIndices]
    exact ⟨hrone, hrR,
      isVinogradovMediumCoefficient_eighth_of_sharpBlock
        hX hFhigh hα hn hrone hrlow hrupp (hcoeff r hrone hrR) hsmall⟩
  exact (vinogradovTaylorDegree_sq_div_160_le_sum_sharpMediumDegreeBlock
      hX hFhigh).trans
    (Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun r hr hnot => Nat.cast_nonneg r))

/-- The quarter-window block supplies weighted mass `R²/193` inside the
genuine `c₀=1/4` medium-coordinate set. -/
theorem vinogradovTaylorDegree_sq_div_193_le_sum_mediumDegrees_quarter
    {X F α : ℝ} {n : ℕ} {c : ℕ → ℝ}
    (hX : 2 ≤ X) (hFhigh : X ^ 4 ≤ F) (hα : 1 ≤ α)
    (hn : (n : ℝ) ∈ Set.Icc X (2 * X))
    (hcoeff : ∀ r : ℕ, 1 ≤ r → r ≤ vinogradovTaylorDegree X F →
      F / α ^ (r ^ 3) ≤ (n : ℝ) ^ r * |c r| ∧
        (n : ℝ) ^ r * |c r| ≤ α ^ (r ^ 3) * F)
    (hsmall : 2 * α * Real.exp
      (-((2 : ℝ) ^ (-18 : ℝ)) * (Real.log X) ^ 3 /
        (Real.log F) ^ 2) < 1) :
    (vinogradovTaylorDegree X F : ℝ) ^ 2 / 193 ≤
      ∑ r ∈ vinogradovMediumCoefficientIndices
        (vinogradovAveragingRange X : ℝ) (1 / 4) c
        (vinogradovTaylorDegree X F), (r : ℝ) := by
  have hratio : 0 ≤ Real.log F / Real.log X := by
    have hXpos : 0 < X := by linarith
    have hlogX : 0 < Real.log X := Real.log_pos (by linarith)
    have hFone : 1 ≤ F := by
      calc
        1 ≤ X ^ 4 := by nlinarith [sq_nonneg (X ^ 2 - 1)]
        _ ≤ F := hFhigh
    exact div_nonneg (Real.log_nonneg hFone) hlogX.le
  have hsubset : vinogradovQuarterMediumDegreeBlock X F ⊆
      vinogradovMediumCoefficientIndices
        (vinogradovAveragingRange X : ℝ) (1 / 4) c
        (vinogradovTaylorDegree X F) := by
    intro r hr
    obtain ⟨hrlow, hrupp⟩ :=
      mem_vinogradovQuarterMediumDegreeBlock_bounds hratio hr
    obtain ⟨hrone, hrR⟩ :=
      mem_vinogradovQuarterMediumDegreeBlock_degree hX hFhigh hr
    rw [mem_vinogradovMediumCoefficientIndices]
    exact ⟨hrone, hrR,
      isVinogradovMediumCoefficient_quarter_of_sharpBlock
        hX hFhigh hα hn hrone hrlow hrupp (hcoeff r hrone hrR) hsmall⟩
  exact (vinogradovTaylorDegree_sq_div_193_le_sum_quarterMediumDegreeBlock
      hX hFhigh).trans
    (Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun r hr hnot => Nat.cast_nonneg r))

/-- A single envelope at degree one implies every scalar growth inequality
needed for the source choice `c₀ = 1/128`. -/
theorem vinogradovScalarGrowth_one_div_128_of_uniformEnvelope
    (V R : ℕ) (hV : 1 ≤ V)
    (henvelope :
      72 * (1 + Real.log 2 + 2 * (R : ℝ) * Real.log V) ≤
        (V : ℝ) ^ (1 / 256 : ℝ)) :
    ∀ j : Fin R,
      72 * (1 + Real.log 2 +
        ((2 - (1 / 128 : ℝ)) * ((j.1 + 1 : ℕ) : ℝ)) * Real.log V) ≤
        (V : ℝ) ^
          (((1 / 128 : ℝ) / 2) * ((j.1 + 1 : ℕ) : ℝ)) := by
  intro j
  have hVreal : (1 : ℝ) ≤ (V : ℝ) := by exact_mod_cast hV
  have hlogV : 0 ≤ Real.log V := Real.log_nonneg hVreal
  have hdOne : (1 : ℝ) ≤ ((j.1 + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le j.1)
  have hdR : ((j.1 + 1 : ℕ) : ℝ) ≤ (R : ℝ) := by
    exact_mod_cast j.isLt
  have hdegree :
      (2 - (1 / 128 : ℝ)) * ((j.1 + 1 : ℕ) : ℝ) ≤ 2 * (R : ℝ) := by
    apply mul_le_mul (by norm_num) hdR
    · positivity
    · positivity
  have hleft :
      72 * (1 + Real.log 2 +
        ((2 - (1 / 128 : ℝ)) * ((j.1 + 1 : ℕ) : ℝ)) * Real.log V) ≤
        72 * (1 + Real.log 2 + 2 * (R : ℝ) * Real.log V) := by
    gcongr
  have hexponent :
      (1 / 256 : ℝ) ≤
        ((1 / 128 : ℝ) / 2) * ((j.1 + 1 : ℕ) : ℝ) := by
    nlinarith
  exact hleft.trans (henvelope.trans
    (Real.rpow_le_rpow_of_exponent_le hVreal hexponent))

/-- The same uniform envelope absorbs only `1/256` of each degree while the
actual medium window keeps `c₀=1/8`. Thus `31/256` of every medium degree
survives in the product estimate. -/
theorem vinogradovScalarGrowth_eighth_of_uniformEnvelope
    (V R : ℕ) (hV : 1 ≤ V)
    (henvelope :
      72 * (1 + Real.log 2 + 2 * (R : ℝ) * Real.log V) ≤
        (V : ℝ) ^ (1 / 256 : ℝ)) :
    ∀ j : Fin R,
      72 * (1 + Real.log 2 +
        ((2 - (1 / 8 : ℝ)) * ((j.1 + 1 : ℕ) : ℝ)) * Real.log V) ≤
        (V : ℝ) ^
          ((1 / 256 : ℝ) * ((j.1 + 1 : ℕ) : ℝ)) := by
  intro j
  have hVreal : (1 : ℝ) ≤ (V : ℝ) := by exact_mod_cast hV
  have hlogV : 0 ≤ Real.log V := Real.log_nonneg hVreal
  have hdOne : (1 : ℝ) ≤ ((j.1 + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le j.1)
  have hdR : ((j.1 + 1 : ℕ) : ℝ) ≤ (R : ℝ) := by
    exact_mod_cast j.isLt
  have hdegree :
      (2 - (1 / 8 : ℝ)) * ((j.1 + 1 : ℕ) : ℝ) ≤ 2 * (R : ℝ) := by
    apply mul_le_mul (by norm_num) hdR
    · positivity
    · positivity
  have hleft :
      72 * (1 + Real.log 2 +
        ((2 - (1 / 8 : ℝ)) * ((j.1 + 1 : ℕ) : ℝ)) * Real.log V) ≤
        72 * (1 + Real.log 2 + 2 * (R : ℝ) * Real.log V) := by
    gcongr
  have hexponent :
      (1 / 256 : ℝ) ≤
        (1 / 256 : ℝ) * ((j.1 + 1 : ℕ) : ℝ) := by
    nlinarith
  exact hleft.trans (henvelope.trans
    (Real.rpow_le_rpow_of_exponent_le hVreal hexponent))

/-- A `V^(1/1024)` uniform envelope absorbs only `1/1024` of each degree in
the genuine `c₀=1/4` medium window. -/
theorem vinogradovScalarGrowth_quarter_of_uniformEnvelope
    (V R : ℕ) (hV : 1 ≤ V)
    (henvelope :
      72 * (1 + Real.log 2 + 2 * (R : ℝ) * Real.log V) ≤
        (V : ℝ) ^ (1 / 1024 : ℝ)) :
    ∀ j : Fin R,
      72 * (1 + Real.log 2 +
        ((2 - (1 / 4 : ℝ)) * ((j.1 + 1 : ℕ) : ℝ)) * Real.log V) ≤
        (V : ℝ) ^
          ((1 / 1024 : ℝ) * ((j.1 + 1 : ℕ) : ℝ)) := by
  intro j
  have hVreal : (1 : ℝ) ≤ (V : ℝ) := by exact_mod_cast hV
  have hlogV : 0 ≤ Real.log V := Real.log_nonneg hVreal
  have hdOne : (1 : ℝ) ≤ ((j.1 + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le j.1)
  have hdR : ((j.1 + 1 : ℕ) : ℝ) ≤ (R : ℝ) := by
    exact_mod_cast j.isLt
  have hdegree :
      (2 - (1 / 4 : ℝ)) * ((j.1 + 1 : ℕ) : ℝ) ≤ 2 * (R : ℝ) := by
    apply mul_le_mul (by norm_num) hdR
    · positivity
    · positivity
  have hleft :
      72 * (1 + Real.log 2 +
        ((2 - (1 / 4 : ℝ)) * ((j.1 + 1 : ℕ) : ℝ)) * Real.log V) ≤
        72 * (1 + Real.log 2 + 2 * (R : ℝ) * Real.log V) := by
    gcongr
  have hexponent :
      (1 / 1024 : ℝ) ≤
        (1 / 1024 : ℝ) * ((j.1 + 1 : ℕ) : ℝ) := by
    nlinarith
  exact hleft.trans (henvelope.trans
    (Real.rpow_le_rpow_of_exponent_le hVreal hexponent))

/-- The nontrivial source scale forces the Taylor degree below `log X`. -/
theorem vinogradovTaylorDegree_cast_le_log_of_nontrivialScale
    {X F α : ℝ} (hX : 2 ≤ X) (hFhigh : X ^ 4 ≤ F) (hα : 1 ≤ α)
    (hsmall : 2 * α * Real.exp
      (-((2 : ℝ) ^ (-18 : ℝ)) * (Real.log X) ^ 3 /
        (Real.log F) ^ 2) < 1) :
    (vinogradovTaylorDegree X F : ℝ) ≤ Real.log X := by
  have hXpos : 0 < X := by linarith
  have hlogX : 0 < Real.log X := Real.log_pos (by linarith)
  have hFpos : 0 < F := (pow_pos hXpos 4).trans_le hFhigh
  have hlogF : 0 < Real.log F := by
    apply Real.log_pos
    exact (show 1 < X ^ 4 by nlinarith [sq_nonneg (X ^ 2 - 4)]).trans_le hFhigh
  have hlogTwoHalf : (1 / 2 : ℝ) < Real.log 2 := by
    exact (by norm_num : (1 / 2 : ℝ) < 0.6931471803).trans Real.log_two_gt_d9
  have hdecay : Real.log 2 <
      (2 : ℝ) ^ (-18 : ℝ) * (Real.log X) ^ 3 / (Real.log F) ^ 2 := by
    apply log_lt_of_nontrivial_exponential_scale hα (by norm_num)
    rw [show -((2 : ℝ) ^ (-18 : ℝ) * (Real.log X) ^ 3 /
        (Real.log F) ^ 2) =
      -((2 : ℝ) ^ (-18 : ℝ)) * (Real.log X) ^ 3 /
        (Real.log F) ^ 2 by ring]
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hsmall
  have hscaled : (2 : ℝ) ^ 17 * (Real.log F) ^ 2 <
      (Real.log X) ^ 3 := by
    have hmul := mul_lt_mul_of_pos_right hdecay (sq_pos_of_pos hlogF)
    have hhalfMul :=
      mul_lt_mul_of_pos_right hlogTwoHalf (sq_pos_of_pos hlogF)
    rw [div_mul_cancel₀ _ (ne_of_gt (sq_pos_of_pos hlogF))] at hmul
    norm_num at hmul ⊢
    nlinarith
  let s : ℝ := Real.log F / Real.log X
  have hsnonneg : 0 ≤ s := by dsimp only [s]; positivity
  have hssq : (2 : ℝ) ^ 17 * s ^ 2 < Real.log X := by
    dsimp only [s]
    rw [div_pow, ← mul_div_assoc,
      div_lt_iff₀ (sq_pos_of_pos hlogX)]
    nlinarith
  have hlogLarge :=
    two_pow_22_mul_log_two_lt_log_of_nontrivialScale hX hFhigh hα hsmall
  have htwo21 : (2 : ℝ) ^ 21 < Real.log X := by
    have := mul_lt_mul_of_pos_left hlogTwoHalf
      (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) 22)
    norm_num at this hlogLarge ⊢
    linarith
  have hsLe : s ≤ Real.log X / 20 := by
    by_contra hnot
    have hsGt : Real.log X / 20 < s := lt_of_not_ge hnot
    have hsquare : (Real.log X / 20) ^ 2 < s ^ 2 := by nlinarith
    have hbad : (2 : ℝ) ^ 17 * (Real.log X / 20) ^ 2 < Real.log X :=
      (mul_lt_mul_of_pos_left hsquare (by positivity)).trans hssq
    norm_num at hbad htwo21
    nlinarith [sq_pos_of_pos hlogX]
  have hceil : (⌈s⌉₊ : ℝ) < s + 1 := Nat.ceil_lt_add_one hsnonneg
  have hRlt : (vinogradovTaylorDegree X F : ℝ) < 10 * (s + 1) := by
    rw [vinogradovTaylorDegree]
    push_cast
    dsimp only [s] at hceil ⊢
    linarith
  have htwenty : (20 : ℝ) ≤ Real.log X := by
    norm_num at htwo21 ⊢
    linarith
  linarith

/-- The original nontrivial-scale hypothesis absorbs the complete uniform
scalar envelope, including the floor-rounded averaging range. -/
theorem vinogradovScalarUniformEnvelope_of_nontrivialScale
    {X F α : ℝ} (hX : 2 ≤ X) (hFhigh : X ^ 4 ≤ F) (hα : 1 ≤ α)
    (hsmall : 2 * α * Real.exp
      (-((2 : ℝ) ^ (-18 : ℝ)) * (Real.log X) ^ 3 /
        (Real.log F) ^ 2) < 1) :
    72 * (1 + Real.log 2 +
        2 * (vinogradovTaylorDegree X F : ℝ) *
          Real.log (vinogradovAveragingRange X)) ≤
      (vinogradovAveragingRange X : ℝ) ^ (1 / 256 : ℝ) := by
  let L : ℝ := Real.log X
  let W : ℝ := Real.log (vinogradovAveragingRange X : ℝ)
  have hXpos : 0 < X := by linarith
  have hLpos : 0 < L := by dsimp only [L]; exact Real.log_pos (by linarith)
  have hlogTwoUpper : Real.log 2 < 1 :=
    Real.log_two_lt_d9.trans (by norm_num)
  have hlarge :=
    two_pow_22_mul_log_two_lt_log_of_nontrivialScale hX hFhigh hα hsmall
  have hlogTwoHalf : (1 / 2 : ℝ) < Real.log 2 := by
    exact (by norm_num : (1 / 2 : ℝ) < 0.6931471803).trans Real.log_two_gt_d9
  have hLlarge : (2 : ℝ) ^ 21 < L := by
    have hmul := mul_lt_mul_of_pos_left hlogTwoHalf
      (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) 22)
    dsimp only [L]
    norm_num at hmul hlarge ⊢
    linarith
  have hXsixteen : 16 ≤ X :=
    (sixteen_lt_of_nontrivialScale hX hFhigh hα hsmall).le
  obtain ⟨hWlower, hWupper⟩ :=
    log_vinogradovAveragingRange_bounds hXsixteen
  change L / 4 - Real.log 2 < W at hWlower
  change W ≤ L / 4 at hWupper
  have hWlow : L / 8 ≤ W := by
    nlinarith
  have hWnonneg : 0 ≤ W := by
    have : (0 : ℝ) ≤ L / 8 := by positivity
    linarith
  have hR : (vinogradovTaylorDegree X F : ℝ) ≤ L := by
    dsimp only [L]
    exact vinogradovTaylorDegree_cast_le_log_of_nontrivialScale
      hX hFhigh hα hsmall
  have hRW : (vinogradovTaylorDegree X F : ℝ) * W ≤ L ^ 2 := by
    have := mul_le_mul hR hWupper hWnonneg hLpos.le
    nlinarith
  have hLsqTwo : (2 : ℝ) ≤ L ^ 2 := by
    norm_num at hLlarge
    nlinarith [sq_nonneg (L - 2)]
  have hleft :
      72 * (1 + Real.log 2 +
        2 * (vinogradovTaylorDegree X F : ℝ) * W) ≤ 216 * L ^ 2 := by
    nlinarith
  have hcoef :
      (216 : ℝ) * 720 * 2048 ^ 6 ≤ ((2 : ℝ) ^ 21) ^ 4 := by
    norm_num
  have hLfour : (216 : ℝ) * 720 * 2048 ^ 6 ≤ L ^ 4 := by
    exact hcoef.trans (pow_le_pow_left₀ (by positivity) hLlarge.le 4)
  have hmul := mul_le_mul_of_nonneg_right hLfour (sq_nonneg L)
  have hpoly : 216 * L ^ 2 ≤ (L / 2048) ^ 6 / 720 := by
    norm_num at hmul ⊢
    nlinarith
  have hexpPoly : (L / 2048) ^ 6 / 720 ≤ Real.exp (L / 2048) := by
    have h := Real.pow_div_factorial_le_exp
      (L / 2048) (show 0 ≤ L / 2048 by positivity) 6
    norm_num [Nat.factorial] at h
    exact h
  have hexpMono : Real.exp (L / 2048) ≤ Real.exp (W / 256) := by
    apply Real.exp_le_exp.mpr
    linarith
  calc
    72 * (1 + Real.log 2 +
        2 * (vinogradovTaylorDegree X F : ℝ) *
          Real.log (vinogradovAveragingRange X)) =
        72 * (1 + Real.log 2 +
          2 * (vinogradovTaylorDegree X F : ℝ) * W) := by rfl
    _ ≤ 216 * L ^ 2 := hleft
    _ ≤ (L / 2048) ^ 6 / 720 := hpoly
    _ ≤ Real.exp (L / 2048) := hexpPoly
    _ ≤ Real.exp (W / 256) := hexpMono
    _ = (vinogradovAveragingRange X : ℝ) ^ (1 / 256 : ℝ) := by
      rw [Real.rpow_def_of_pos]
      · congr 1
        dsimp only [W]
        ring
      · exact_mod_cast vinogradovAveragingRange_pos (show 1 ≤ X by linarith)

/-- A sharper absorption of the same scalar envelope. Using the ninth Taylor
term in `exp` replaces the earlier exponent `1/256` by `1/1024`. -/
theorem vinogradovScalarUniformEnvelope_one_div_1024_of_nontrivialScale
    {X F α : ℝ} (hX : 2 ≤ X) (hFhigh : X ^ 4 ≤ F) (hα : 1 ≤ α)
    (hsmall : 2 * α * Real.exp
      (-((2 : ℝ) ^ (-18 : ℝ)) * (Real.log X) ^ 3 /
        (Real.log F) ^ 2) < 1) :
    72 * (1 + Real.log 2 +
        2 * (vinogradovTaylorDegree X F : ℝ) *
          Real.log (vinogradovAveragingRange X)) ≤
      (vinogradovAveragingRange X : ℝ) ^ (1 / 1024 : ℝ) := by
  let L : ℝ := Real.log X
  let W : ℝ := Real.log (vinogradovAveragingRange X : ℝ)
  have hLpos : 0 < L := by dsimp only [L]; exact Real.log_pos (by linarith)
  have hlogTwoUpper : Real.log 2 < 1 :=
    Real.log_two_lt_d9.trans (by norm_num)
  have hlarge :=
    two_pow_22_mul_log_two_lt_log_of_nontrivialScale hX hFhigh hα hsmall
  have hlogTwoHalf : (1 / 2 : ℝ) < Real.log 2 := by
    exact (by norm_num : (1 / 2 : ℝ) < 0.6931471803).trans Real.log_two_gt_d9
  have hLlarge : (2 : ℝ) ^ 21 < L := by
    have hmul := mul_lt_mul_of_pos_left hlogTwoHalf
      (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) 22)
    dsimp only [L]
    norm_num at hmul hlarge ⊢
    linarith
  have hXsixteen : 16 ≤ X :=
    (sixteen_lt_of_nontrivialScale hX hFhigh hα hsmall).le
  obtain ⟨hWlower, hWupper⟩ :=
    log_vinogradovAveragingRange_bounds hXsixteen
  change L / 4 - Real.log 2 < W at hWlower
  change W ≤ L / 4 at hWupper
  have hWlow : L / 8 ≤ W := by
    nlinarith
  have hWnonneg : 0 ≤ W := by
    have : (0 : ℝ) ≤ L / 8 := by positivity
    linarith
  have hR : (vinogradovTaylorDegree X F : ℝ) ≤ L := by
    dsimp only [L]
    exact vinogradovTaylorDegree_cast_le_log_of_nontrivialScale
      hX hFhigh hα hsmall
  have hRW : (vinogradovTaylorDegree X F : ℝ) * W ≤ L ^ 2 := by
    have := mul_le_mul hR hWupper hWnonneg hLpos.le
    nlinarith
  have hLsqTwo : (2 : ℝ) ≤ L ^ 2 := by
    norm_num at hLlarge
    nlinarith [sq_nonneg (L - 2)]
  have hleft :
      72 * (1 + Real.log 2 +
        2 * (vinogradovTaylorDegree X F : ℝ) * W) ≤ 216 * L ^ 2 := by
    nlinarith
  have hcoef :
      (216 : ℝ) * 362880 * 8192 ^ 9 ≤ ((2 : ℝ) ^ 21) ^ 7 := by
    norm_num
  have hLseven : (216 : ℝ) * 362880 * 8192 ^ 9 ≤ L ^ 7 := by
    exact hcoef.trans (pow_le_pow_left₀ (by positivity) hLlarge.le 7)
  have hmul := mul_le_mul_of_nonneg_right hLseven (sq_nonneg L)
  have hpoly : 216 * L ^ 2 ≤ (L / 8192) ^ 9 / 362880 := by
    norm_num at hmul ⊢
    nlinarith
  have hexpPoly : (L / 8192) ^ 9 / 362880 ≤ Real.exp (L / 8192) := by
    have h := Real.pow_div_factorial_le_exp
      (L / 8192) (show 0 ≤ L / 8192 by positivity) 9
    norm_num [Nat.factorial] at h
    exact h
  have hexpMono : Real.exp (L / 8192) ≤ Real.exp (W / 1024) := by
    apply Real.exp_le_exp.mpr
    linarith
  calc
    72 * (1 + Real.log 2 +
        2 * (vinogradovTaylorDegree X F : ℝ) *
          Real.log (vinogradovAveragingRange X)) =
        72 * (1 + Real.log 2 +
          2 * (vinogradovTaylorDegree X F : ℝ) * W) := by rfl
    _ ≤ 216 * L ^ 2 := hleft
    _ ≤ (L / 8192) ^ 9 / 362880 := hpoly
    _ ≤ Real.exp (L / 8192) := hexpPoly
    _ ≤ Real.exp (W / 1024) := hexpMono
    _ = (vinogradovAveragingRange X : ℝ) ^ (1 / 1024 : ℝ) := by
      rw [Real.rpow_def_of_pos]
      · congr 1
        dsimp only [W]
        ring
      · exact_mod_cast vinogradovAveragingRange_pos (show 1 ≤ X by linarith)

/-- The source nontrivial-scale assumption supplies every coordinatewise
scalar growth inequality used by the quadratic product estimate. -/
theorem sourceVinogradovScalarGrowth_of_nontrivialScale
    {X F α : ℝ} (hX : 2 ≤ X) (hFhigh : X ^ 4 ≤ F) (hα : 1 ≤ α)
    (hsmall : 2 * α * Real.exp
      (-((2 : ℝ) ^ (-18 : ℝ)) * (Real.log X) ^ 3 /
        (Real.log F) ^ 2) < 1) :
    ∀ j : Fin (vinogradovTaylorDegree X F),
      72 * (1 + Real.log 2 +
        ((2 - (1 / 128 : ℝ)) * ((j.1 + 1 : ℕ) : ℝ)) *
          Real.log (vinogradovAveragingRange X)) ≤
        (vinogradovAveragingRange X : ℝ) ^
          (((1 / 128 : ℝ) / 2) * ((j.1 + 1 : ℕ) : ℝ)) := by
  apply vinogradovScalarGrowth_one_div_128_of_uniformEnvelope
  · exact vinogradovAveragingRange_pos (show 1 ≤ X by linarith)
  · exact vinogradovScalarUniformEnvelope_of_nontrivialScale
      hX hFhigh hα hsmall

/-- Source-scale scalar growth at the genuine `c₀=1/8` medium window, with
only the fixed absorption cost `η=1/256`. -/
theorem sourceVinogradovScalarGrowth_eighth_of_nontrivialScale
    {X F α : ℝ} (hX : 2 ≤ X) (hFhigh : X ^ 4 ≤ F) (hα : 1 ≤ α)
    (hsmall : 2 * α * Real.exp
      (-((2 : ℝ) ^ (-18 : ℝ)) * (Real.log X) ^ 3 /
        (Real.log F) ^ 2) < 1) :
    ∀ j : Fin (vinogradovTaylorDegree X F),
      72 * (1 + Real.log 2 +
        ((2 - (1 / 8 : ℝ)) * ((j.1 + 1 : ℕ) : ℝ)) *
          Real.log (vinogradovAveragingRange X)) ≤
        (vinogradovAveragingRange X : ℝ) ^
          ((1 / 256 : ℝ) * ((j.1 + 1 : ℕ) : ℝ)) := by
  apply vinogradovScalarGrowth_eighth_of_uniformEnvelope
  · exact vinogradovAveragingRange_pos (show 1 ≤ X by linarith)
  · exact vinogradovScalarUniformEnvelope_of_nontrivialScale
      hX hFhigh hα hsmall

/-- Source-scale scalar growth for `c₀=1/4`, retaining all but `1/1024` of
each medium degree. -/
theorem sourceVinogradovScalarGrowth_quarter_of_nontrivialScale
    {X F α : ℝ} (hX : 2 ≤ X) (hFhigh : X ^ 4 ≤ F) (hα : 1 ≤ α)
    (hsmall : 2 * α * Real.exp
      (-((2 : ℝ) ^ (-18 : ℝ)) * (Real.log X) ^ 3 /
        (Real.log F) ^ 2) < 1) :
    ∀ j : Fin (vinogradovTaylorDegree X F),
      72 * (1 + Real.log 2 +
        ((2 - (1 / 4 : ℝ)) * ((j.1 + 1 : ℕ) : ℝ)) *
          Real.log (vinogradovAveragingRange X)) ≤
        (vinogradovAveragingRange X : ℝ) ^
          ((1 / 1024 : ℝ) * ((j.1 + 1 : ℕ) : ℝ)) := by
  apply vinogradovScalarGrowth_quarter_of_uniformEnvelope
  · exact vinogradovAveragingRange_pos (show 1 ≤ X by linarith)
  · exact vinogradovScalarUniformEnvelope_one_div_1024_of_nontrivialScale
      hX hFhigh hα hsmall

/-- Source-form quadratic saving for the complete product of normalized
coordinate factors, conditional only on the explicit scalar growth bound. -/
theorem source_prod_mediumSavingFactor_le_quadratic_rpow
    {X F α : ℝ} {n ell : ℕ} {c : ℕ → ℝ}
    (hX : 2 ≤ X) (hFhigh : X ^ 4 ≤ F) (hα : 1 ≤ α)
    (hn : (n : ℝ) ∈ Set.Icc X (2 * X)) (hell : 1 ≤ ell)
    (hcoeff : ∀ r : ℕ, 1 ≤ r → r ≤ vinogradovTaylorDegree X F →
      F / α ^ (r ^ 3) ≤ (n : ℝ) ^ r * |c r| ∧
        (n : ℝ) ^ r * |c r| ≤ α ^ (r ^ 3) * F)
    (hsmall : 2 * α * Real.exp
      (-((2 : ℝ) ^ (-18 : ℝ)) * (Real.log X) ^ 3 /
        (Real.log F) ^ 2) < 1)
    (hgrowth : ∀ j : Fin (vinogradovTaylorDegree X F),
      72 * (1 + Real.log 2 +
        ((2 - (1 / 128 : ℝ)) * ((j.1 + 1 : ℕ) : ℝ)) *
          Real.log (vinogradovAveragingRange X)) ≤
        (vinogradovAveragingRange X : ℝ) ^
          (((1 / 128 : ℝ) / 2) * ((j.1 + 1 : ℕ) : ℝ))) :
    (∏ j : Fin (vinogradovTaylorDegree X F),
      vinogradovMediumCoordinateSavingFactor c
        (vinogradovAveragingRange X) ell (j.1 + 1) (1 / 128)) ≤
      (vinogradovAveragingRange X : ℝ) ^
        (-(vinogradovTaylorDegree X F : ℝ) ^ 2 / 307200) := by
  have hV : 1 ≤ vinogradovAveragingRange X :=
    vinogradovAveragingRange_pos (show 1 ≤ X by linarith)
  calc
    (∏ j : Fin (vinogradovTaylorDegree X F),
      vinogradovMediumCoordinateSavingFactor c
        (vinogradovAveragingRange X) ell (j.1 + 1) (1 / 128)) ≤
        (vinogradovAveragingRange X : ℝ) ^
          (-((1 / 128 : ℝ) / 2) *
            ((vinogradovTaylorDegree X F : ℝ) ^ 2 / 1200)) := by
      exact prod_mediumSavingFactor_le_rpow_of_sum_lower
        c (vinogradovAveragingRange X) ell (vinogradovTaylorDegree X F)
        (1 / 128) ((vinogradovTaylorDegree X F : ℝ) ^ 2 / 1200)
        hV hell (by norm_num) (by norm_num) hgrowth
        (vinogradovTaylorDegree_sq_div_1200_le_sum_mediumDegrees
          hX hFhigh hα hn hcoeff hsmall)
    _ = (vinogradovAveragingRange X : ℝ) ^
        (-(vinogradovTaylorDegree X F : ℝ) ^ 2 / 307200) := by
      congr 1
      ring

/-- Sharp source-window version of the normalized coordinate product. Using
`c₀=1/8` and absorbing only `η=1/256` retains `31/256` of the weighted medium
degrees, improving the previous exponent by the exact factor `31`. -/
theorem source_prod_mediumSavingFactor_le_quadratic_rpow_eighth
    {X F α : ℝ} {n ell : ℕ} {c : ℕ → ℝ}
    (hX : 2 ≤ X) (hFhigh : X ^ 4 ≤ F) (hα : 1 ≤ α)
    (hn : (n : ℝ) ∈ Set.Icc X (2 * X)) (hell : 1 ≤ ell)
    (hcoeff : ∀ r : ℕ, 1 ≤ r → r ≤ vinogradovTaylorDegree X F →
      F / α ^ (r ^ 3) ≤ (n : ℝ) ^ r * |c r| ∧
        (n : ℝ) ^ r * |c r| ≤ α ^ (r ^ 3) * F)
    (hsmall : 2 * α * Real.exp
      (-((2 : ℝ) ^ (-18 : ℝ)) * (Real.log X) ^ 3 /
        (Real.log F) ^ 2) < 1)
    (hgrowth : ∀ j : Fin (vinogradovTaylorDegree X F),
      72 * (1 + Real.log 2 +
        ((2 - (1 / 8 : ℝ)) * ((j.1 + 1 : ℕ) : ℝ)) *
          Real.log (vinogradovAveragingRange X)) ≤
        (vinogradovAveragingRange X : ℝ) ^
          ((1 / 256 : ℝ) * ((j.1 + 1 : ℕ) : ℝ))) :
    (∏ j : Fin (vinogradovTaylorDegree X F),
      vinogradovMediumCoordinateSavingFactor c
        (vinogradovAveragingRange X) ell (j.1 + 1) (1 / 8)) ≤
      (vinogradovAveragingRange X : ℝ) ^
        (-(31 * (vinogradovTaylorDegree X F : ℝ) ^ 2) / 307200) := by
  have hV : 1 ≤ vinogradovAveragingRange X :=
    vinogradovAveragingRange_pos (show 1 ≤ X by linarith)
  calc
    (∏ j : Fin (vinogradovTaylorDegree X F),
      vinogradovMediumCoordinateSavingFactor c
        (vinogradovAveragingRange X) ell (j.1 + 1) (1 / 8)) ≤
        (vinogradovAveragingRange X : ℝ) ^
          (-((1 / 8 : ℝ) - 1 / 256) *
            ((vinogradovTaylorDegree X F : ℝ) ^ 2 / 1200)) := by
      exact prod_mediumSavingFactor_le_rpow_of_sum_lower_of_absorption
        c (vinogradovAveragingRange X) ell (vinogradovTaylorDegree X F)
        (1 / 8) (1 / 256) ((vinogradovTaylorDegree X F : ℝ) ^ 2 / 1200)
        hV hell (by norm_num) (by norm_num) hgrowth
        (vinogradovTaylorDegree_sq_div_1200_le_sum_mediumDegrees_eighth
          hX hFhigh hα hn hcoeff hsmall)
    _ = (vinogradovAveragingRange X : ℝ) ^
        (-(31 * (vinogradovTaylorDegree X F : ℝ) ^ 2) / 307200) := by
      congr 1
      ring

/-- The stronger `1/8` coordinate product with its scalar-growth premise
discharged directly from the source nontrivial-scale hypothesis. -/
theorem source_prod_mediumSavingFactor_le_quadratic_rpow_eighth_of_nontrivialScale
    {X F α : ℝ} {n ell : ℕ} {c : ℕ → ℝ}
    (hX : 2 ≤ X) (hFhigh : X ^ 4 ≤ F) (hα : 1 ≤ α)
    (hn : (n : ℝ) ∈ Set.Icc X (2 * X)) (hell : 1 ≤ ell)
    (hcoeff : ∀ r : ℕ, 1 ≤ r → r ≤ vinogradovTaylorDegree X F →
      F / α ^ (r ^ 3) ≤ (n : ℝ) ^ r * |c r| ∧
        (n : ℝ) ^ r * |c r| ≤ α ^ (r ^ 3) * F)
    (hsmall : 2 * α * Real.exp
      (-((2 : ℝ) ^ (-18 : ℝ)) * (Real.log X) ^ 3 /
        (Real.log F) ^ 2) < 1) :
    (∏ j : Fin (vinogradovTaylorDegree X F),
      vinogradovMediumCoordinateSavingFactor c
        (vinogradovAveragingRange X) ell (j.1 + 1) (1 / 8)) ≤
      (vinogradovAveragingRange X : ℝ) ^
        (-(31 * (vinogradovTaylorDegree X F : ℝ) ^ 2) / 307200) := by
  exact source_prod_mediumSavingFactor_le_quadratic_rpow_eighth
    hX hFhigh hα hn hell hcoeff hsmall
      (sourceVinogradovScalarGrowth_eighth_of_nontrivialScale
        hX hFhigh hα hsmall)

/-- Sharp quarter-window normalized coordinate product.  The weighted mass
`R²/193` and absorption cost `1/1024` leave exponent `-255 R²/197632`. -/
theorem source_prod_mediumSavingFactor_le_quadratic_rpow_quarter
    {X F α : ℝ} {n ell : ℕ} {c : ℕ → ℝ}
    (hX : 2 ≤ X) (hFhigh : X ^ 4 ≤ F) (hα : 1 ≤ α)
    (hn : (n : ℝ) ∈ Set.Icc X (2 * X)) (hell : 1 ≤ ell)
    (hcoeff : ∀ r : ℕ, 1 ≤ r → r ≤ vinogradovTaylorDegree X F →
      F / α ^ (r ^ 3) ≤ (n : ℝ) ^ r * |c r| ∧
        (n : ℝ) ^ r * |c r| ≤ α ^ (r ^ 3) * F)
    (hsmall : 2 * α * Real.exp
      (-((2 : ℝ) ^ (-18 : ℝ)) * (Real.log X) ^ 3 /
        (Real.log F) ^ 2) < 1)
    (hgrowth : ∀ j : Fin (vinogradovTaylorDegree X F),
      72 * (1 + Real.log 2 +
        ((2 - (1 / 4 : ℝ)) * ((j.1 + 1 : ℕ) : ℝ)) *
          Real.log (vinogradovAveragingRange X)) ≤
        (vinogradovAveragingRange X : ℝ) ^
          ((1 / 1024 : ℝ) * ((j.1 + 1 : ℕ) : ℝ))) :
    (∏ j : Fin (vinogradovTaylorDegree X F),
      vinogradovMediumCoordinateSavingFactor c
        (vinogradovAveragingRange X) ell (j.1 + 1) (1 / 4)) ≤
      (vinogradovAveragingRange X : ℝ) ^
        (-(255 * (vinogradovTaylorDegree X F : ℝ) ^ 2) / 197632) := by
  have hV : 1 ≤ vinogradovAveragingRange X :=
    vinogradovAveragingRange_pos (show 1 ≤ X by linarith)
  calc
    (∏ j : Fin (vinogradovTaylorDegree X F),
      vinogradovMediumCoordinateSavingFactor c
        (vinogradovAveragingRange X) ell (j.1 + 1) (1 / 4)) ≤
        (vinogradovAveragingRange X : ℝ) ^
          (-((1 / 4 : ℝ) - 1 / 1024) *
            ((vinogradovTaylorDegree X F : ℝ) ^ 2 / 193)) := by
      exact prod_mediumSavingFactor_le_rpow_of_sum_lower_of_absorption
        c (vinogradovAveragingRange X) ell (vinogradovTaylorDegree X F)
        (1 / 4) (1 / 1024) ((vinogradovTaylorDegree X F : ℝ) ^ 2 / 193)
        hV hell (by norm_num) (by norm_num) hgrowth
        (vinogradovTaylorDegree_sq_div_193_le_sum_mediumDegrees_quarter
          hX hFhigh hα hn hcoeff hsmall)
    _ = (vinogradovAveragingRange X : ℝ) ^
        (-(255 * (vinogradovTaylorDegree X F : ℝ) ^ 2) / 197632) := by
      congr 1
      ring

/-- The sharp quarter-window coordinate product with scalar growth discharged
from source nontriviality. -/
theorem source_prod_mediumSavingFactor_le_quadratic_rpow_quarter_of_nontrivialScale
    {X F α : ℝ} {n ell : ℕ} {c : ℕ → ℝ}
    (hX : 2 ≤ X) (hFhigh : X ^ 4 ≤ F) (hα : 1 ≤ α)
    (hn : (n : ℝ) ∈ Set.Icc X (2 * X)) (hell : 1 ≤ ell)
    (hcoeff : ∀ r : ℕ, 1 ≤ r → r ≤ vinogradovTaylorDegree X F →
      F / α ^ (r ^ 3) ≤ (n : ℝ) ^ r * |c r| ∧
        (n : ℝ) ^ r * |c r| ≤ α ^ (r ^ 3) * F)
    (hsmall : 2 * α * Real.exp
      (-((2 : ℝ) ^ (-18 : ℝ)) * (Real.log X) ^ 3 /
        (Real.log F) ^ 2) < 1) :
    (∏ j : Fin (vinogradovTaylorDegree X F),
      vinogradovMediumCoordinateSavingFactor c
        (vinogradovAveragingRange X) ell (j.1 + 1) (1 / 4)) ≤
      (vinogradovAveragingRange X : ℝ) ^
        (-(255 * (vinogradovTaylorDegree X F : ℝ) ^ 2) / 197632) := by
  exact source_prod_mediumSavingFactor_le_quadratic_rpow_quarter
    hX hFhigh hα hn hell hcoeff hsmall
      (sourceVinogradovScalarGrowth_quarter_of_nontrivialScale
        hX hFhigh hα hsmall)

/-- Lemma 12 product assembly before the final scalar exponent estimate:
medium coordinates contribute their normalized saving, while all remaining
coordinates use the sharp cardinality-square bound. -/
theorem prod_coordinateSums_le_prod_mediumSaving_mul_prod_side_sq
    (c : ℕ → ℝ) (V ell R : ℕ) (c₀ : ℝ) (hV : 1 ≤ V)
    (hell : 1 ≤ ell) (hc₀ : c₀ ≤ 2) :
    (∏ j : Fin R, ∑ x ∈ vinogradovPowerBoxSide ell V (j.1 + 1),
      ‖∑ y ∈ vinogradovPowerBoxSide ell V (j.1 + 1),
        standardAdditiveCharacter
          (c (j.1 + 1) * (x : ℝ) * (y : ℝ))‖) ≤
      (∏ j : Fin R,
        vinogradovMediumCoordinateSavingFactor c V ell (j.1 + 1) c₀) *
      ∏ j : Fin R,
        (((2 * (ell * V ^ (j.1 + 1)) + 1 : ℕ) : ℝ)) ^ 2 := by
  classical
  calc
    (∏ j : Fin R, ∑ x ∈ vinogradovPowerBoxSide ell V (j.1 + 1),
      ‖∑ y ∈ vinogradovPowerBoxSide ell V (j.1 + 1),
        standardAdditiveCharacter
          (c (j.1 + 1) * (x : ℝ) * (y : ℝ))‖) ≤
      ∏ j : Fin R,
        vinogradovMediumCoordinateSavingFactor c V ell (j.1 + 1) c₀ *
        (((2 * (ell * V ^ (j.1 + 1)) + 1 : ℕ) : ℝ)) ^ 2 := by
      apply Finset.prod_le_prod
      · intro j hj
        positivity
      · intro j hj
        by_cases hmedium :
            IsVinogradovMediumCoefficient (V : ℝ) c₀ c (j.1 + 1)
        · rw [vinogradovMediumCoordinateSavingFactor, if_pos hmedium]
          simpa only [vinogradovMediumCoordinateSaving] using
            sum_norm_powerBoxSide_phase_le_mediumNormalized
              c V ell (j.1 + 1) c₀ hV hell hc₀ hmedium
        · rw [vinogradovMediumCoordinateSavingFactor, if_neg hmedium, one_mul]
          simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat,
            Nat.cast_pow] using
            sum_norm_powerBoxSide_phase_le_card_sq c V ell (j.1 + 1)
    _ = (∏ j : Fin R,
        vinogradovMediumCoordinateSavingFactor c V ell (j.1 + 1) c₀) *
      ∏ j : Fin R,
        (((2 * (ell * V ^ (j.1 + 1)) + 1 : ℕ) : ℝ)) ^ 2 := by
      rw [Finset.prod_mul_distrib]

/-- Twice the sum of the coordinate degrees `1, ..., R`. Keeping the factor
`2` outside the sum avoids parity bookkeeping and gives the exact exponent
contributed by the squared power-box side lengths. -/
theorem two_mul_sum_fin_val_add_one (R : ℕ) :
    2 * ∑ j : Fin R, (j.1 + 1) = R * (R + 1) := by
  induction R with
  | zero => simp
  | succ R ih =>
      rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero, zero_add, Fin.val_succ]
      have hrewrite : (∑ x : Fin R, (x.1 + 1 + 1)) =
          (∑ x : Fin R, (x.1 + 1)) + R := by
        calc
          (∑ x : Fin R, (x.1 + 1 + 1)) =
              (∑ x : Fin R, (x.1 + 1)) + ∑ _x : Fin R, 1 := by
            rw [Finset.sum_add_distrib]
          _ = (∑ x : Fin R, (x.1 + 1)) + R := by simp
      rw [hrewrite]
      calc
        2 * (1 + ((∑ x : Fin R, (x.1 + 1)) + R)) =
            2 * (∑ x : Fin R, (x.1 + 1)) + 2 * (R + 1) := by ring
        _ = R * (R + 1) + 2 * (R + 1) := by rw [ih]
        _ = (R + 1) * (R + 1 + 1) := by ring

/-- Exact polynomial-size bound for the product of the squared coordinate
box cardinalities. The `V` exponent is `R(R+1)`, the critical Vinogradov
degree, while every additive endpoint loss is isolated in `(3*ell)^(2R)`. -/
theorem prod_powerBoxSide_card_sq_le
    (V ell R : ℕ) (hV : 1 ≤ V) (hell : 1 ≤ ell) :
    (∏ j : Fin R,
      (((2 * (ell * V ^ (j.1 + 1)) + 1 : ℕ) : ℝ)) ^ 2) ≤
      (((3 * ell : ℕ) : ℝ)) ^ (2 * R) *
        (V : ℝ) ^ (R * (R + 1)) := by
  classical
  calc
    (∏ j : Fin R,
      (((2 * (ell * V ^ (j.1 + 1)) + 1 : ℕ) : ℝ)) ^ 2) ≤
        ∏ j : Fin R,
          (((3 * ell : ℕ) : ℝ)) ^ 2 *
            (V : ℝ) ^ (2 * (j.1 + 1)) := by
      apply Finset.prod_le_prod
      · intro j hj
        positivity
      · intro j hj
        have hV0 : V ≠ 0 := by omega
        have hpow0 : V ^ (j.1 + 1) ≠ 0 := pow_ne_zero _ hV0
        have hlength : 1 ≤ ell * V ^ (j.1 + 1) := by
          have hell0 : ell ≠ 0 := by omega
          exact Nat.one_le_iff_ne_zero.mpr (mul_ne_zero hell0 hpow0)
        have hbase :
            2 * (ell * V ^ (j.1 + 1)) + 1 ≤
              (3 * ell) * V ^ (j.1 + 1) := by
          calc
            2 * (ell * V ^ (j.1 + 1)) + 1 ≤
                3 * (ell * V ^ (j.1 + 1)) := by omega
            _ = (3 * ell) * V ^ (j.1 + 1) := by ring
        have hbaseReal :
            ((2 * (ell * V ^ (j.1 + 1)) + 1 : ℕ) : ℝ) ≤
              (((3 * ell) * V ^ (j.1 + 1) : ℕ) : ℝ) := by
          exact_mod_cast hbase
        calc
          (((2 * (ell * V ^ (j.1 + 1)) + 1 : ℕ) : ℝ)) ^ 2 ≤
              ((((3 * ell) * V ^ (j.1 + 1) : ℕ) : ℝ)) ^ 2 :=
            pow_le_pow_left₀ (by positivity) hbaseReal 2
          _ = (((3 * ell : ℕ) : ℝ)) ^ 2 *
                (V : ℝ) ^ (2 * (j.1 + 1)) := by
            norm_cast
            ring
    _ = (((3 * ell : ℕ) : ℝ)) ^ (2 * R) *
        (V : ℝ) ^ (2 * ∑ j : Fin R, (j.1 + 1)) := by
      rw [Finset.prod_mul_distrib]
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      rw [Finset.prod_pow_eq_pow_sum]
      congr 1
      · rw [← pow_mul]
      · congr 1
        rw [Finset.mul_sum]
    _ = (((3 * ell : ℕ) : ℝ)) ^ (2 * R) *
        (V : ℝ) ^ (R * (R + 1)) := by
      rw [two_mul_sum_fin_val_add_one]

/-- Source-form Lemma 12 coordinate product: the medium-degree block supplies
a quadratic negative power after the scalar growth condition is imposed. -/
theorem source_prod_coordinateSums_le_quadraticSaving_mul_prod_side_sq
    {X F α : ℝ} {n ell : ℕ} {c : ℕ → ℝ}
    (hX : 2 ≤ X) (hFhigh : X ^ 4 ≤ F) (hα : 1 ≤ α)
    (hn : (n : ℝ) ∈ Set.Icc X (2 * X)) (hell : 1 ≤ ell)
    (hcoeff : ∀ r : ℕ, 1 ≤ r → r ≤ vinogradovTaylorDegree X F →
      F / α ^ (r ^ 3) ≤ (n : ℝ) ^ r * |c r| ∧
        (n : ℝ) ^ r * |c r| ≤ α ^ (r ^ 3) * F)
    (hsmall : 2 * α * Real.exp
      (-((2 : ℝ) ^ (-18 : ℝ)) * (Real.log X) ^ 3 /
        (Real.log F) ^ 2) < 1)
    (hgrowth : ∀ j : Fin (vinogradovTaylorDegree X F),
      72 * (1 + Real.log 2 +
        ((2 - (1 / 128 : ℝ)) * ((j.1 + 1 : ℕ) : ℝ)) *
          Real.log (vinogradovAveragingRange X)) ≤
        (vinogradovAveragingRange X : ℝ) ^
          (((1 / 128 : ℝ) / 2) * ((j.1 + 1 : ℕ) : ℝ))) :
    (∏ j : Fin (vinogradovTaylorDegree X F),
      ∑ x ∈ vinogradovPowerBoxSide ell (vinogradovAveragingRange X) (j.1 + 1),
        ‖∑ y ∈ vinogradovPowerBoxSide ell (vinogradovAveragingRange X) (j.1 + 1),
          standardAdditiveCharacter
            (c (j.1 + 1) * (x : ℝ) * (y : ℝ))‖) ≤
      (vinogradovAveragingRange X : ℝ) ^
          (-(vinogradovTaylorDegree X F : ℝ) ^ 2 / 307200) *
        ∏ j : Fin (vinogradovTaylorDegree X F),
          (((2 * (ell * vinogradovAveragingRange X ^ (j.1 + 1)) + 1 : ℕ) : ℝ)) ^ 2 := by
  have hV : 1 ≤ vinogradovAveragingRange X :=
    vinogradovAveragingRange_pos (show 1 ≤ X by linarith)
  calc
    (∏ j : Fin (vinogradovTaylorDegree X F),
      ∑ x ∈ vinogradovPowerBoxSide ell (vinogradovAveragingRange X) (j.1 + 1),
        ‖∑ y ∈ vinogradovPowerBoxSide ell (vinogradovAveragingRange X) (j.1 + 1),
          standardAdditiveCharacter
            (c (j.1 + 1) * (x : ℝ) * (y : ℝ))‖) ≤
        (∏ j : Fin (vinogradovTaylorDegree X F),
          vinogradovMediumCoordinateSavingFactor c
            (vinogradovAveragingRange X) ell (j.1 + 1) (1 / 128)) *
        ∏ j : Fin (vinogradovTaylorDegree X F),
          (((2 * (ell * vinogradovAveragingRange X ^ (j.1 + 1)) + 1 : ℕ) : ℝ)) ^ 2 := by
      exact prod_coordinateSums_le_prod_mediumSaving_mul_prod_side_sq
        c (vinogradovAveragingRange X) ell (vinogradovTaylorDegree X F)
        (1 / 128) hV hell (by norm_num)
    _ ≤ (vinogradovAveragingRange X : ℝ) ^
          (-(vinogradovTaylorDegree X F : ℝ) ^ 2 / 307200) *
        ∏ j : Fin (vinogradovTaylorDegree X F),
          (((2 * (ell * vinogradovAveragingRange X ^ (j.1 + 1)) + 1 : ℕ) : ℝ)) ^ 2 := by
      apply mul_le_mul_of_nonneg_right
      · exact source_prod_mediumSavingFactor_le_quadratic_rpow
          hX hFhigh hα hn hell hcoeff hsmall hgrowth
      · positivity

/-- The complete source coordinate-product estimate with its scalar growth
condition discharged from the original nontrivial-scale hypothesis. -/
theorem source_prod_coordinateSums_le_quadraticSaving_of_nontrivialScale
    {X F α : ℝ} {n ell : ℕ} {c : ℕ → ℝ}
    (hX : 2 ≤ X) (hFhigh : X ^ 4 ≤ F) (hα : 1 ≤ α)
    (hn : (n : ℝ) ∈ Set.Icc X (2 * X)) (hell : 1 ≤ ell)
    (hcoeff : ∀ r : ℕ, 1 ≤ r → r ≤ vinogradovTaylorDegree X F →
      F / α ^ (r ^ 3) ≤ (n : ℝ) ^ r * |c r| ∧
        (n : ℝ) ^ r * |c r| ≤ α ^ (r ^ 3) * F)
    (hsmall : 2 * α * Real.exp
      (-((2 : ℝ) ^ (-18 : ℝ)) * (Real.log X) ^ 3 /
        (Real.log F) ^ 2) < 1) :
    (∏ j : Fin (vinogradovTaylorDegree X F),
      ∑ x ∈ vinogradovPowerBoxSide ell (vinogradovAveragingRange X) (j.1 + 1),
        ‖∑ y ∈ vinogradovPowerBoxSide ell (vinogradovAveragingRange X) (j.1 + 1),
          standardAdditiveCharacter
            (c (j.1 + 1) * (x : ℝ) * (y : ℝ))‖) ≤
      (vinogradovAveragingRange X : ℝ) ^
          (-(vinogradovTaylorDegree X F : ℝ) ^ 2 / 307200) *
        ∏ j : Fin (vinogradovTaylorDegree X F),
          (((2 * (ell * vinogradovAveragingRange X ^ (j.1 + 1)) + 1 : ℕ) : ℝ)) ^ 2 := by
  exact source_prod_coordinateSums_le_quadraticSaving_mul_prod_side_sq
    hX hFhigh hα hn hell hcoeff hsmall
      (sourceVinogradovScalarGrowth_of_nontrivialScale
        hX hFhigh hα hsmall)

/-- Lemma 12 with the native `1/8` medium window and the exact critical box
power. The retained saving is thirty-one times the earlier weakened exponent. -/
theorem source_prod_coordinateSums_le_eighthSaving_mul_criticalPower
    {X F α : ℝ} {n ell : ℕ} {c : ℕ → ℝ}
    (hX : 2 ≤ X) (hFhigh : X ^ 4 ≤ F) (hα : 1 ≤ α)
    (hn : (n : ℝ) ∈ Set.Icc X (2 * X)) (hell : 1 ≤ ell)
    (hcoeff : ∀ r : ℕ, 1 ≤ r → r ≤ vinogradovTaylorDegree X F →
      F / α ^ (r ^ 3) ≤ (n : ℝ) ^ r * |c r| ∧
        (n : ℝ) ^ r * |c r| ≤ α ^ (r ^ 3) * F)
    (hsmall : 2 * α * Real.exp
      (-((2 : ℝ) ^ (-18 : ℝ)) * (Real.log X) ^ 3 /
        (Real.log F) ^ 2) < 1) :
    (∏ j : Fin (vinogradovTaylorDegree X F),
      ∑ x ∈ vinogradovPowerBoxSide ell (vinogradovAveragingRange X) (j.1 + 1),
        ‖∑ y ∈ vinogradovPowerBoxSide ell (vinogradovAveragingRange X) (j.1 + 1),
          standardAdditiveCharacter
            (c (j.1 + 1) * (x : ℝ) * (y : ℝ))‖) ≤
      (vinogradovAveragingRange X : ℝ) ^
          (-(31 * (vinogradovTaylorDegree X F : ℝ) ^ 2) / 307200) *
        ((((3 * ell : ℕ) : ℝ)) ^
            (2 * vinogradovTaylorDegree X F) *
          (vinogradovAveragingRange X : ℝ) ^
            (vinogradovTaylorDegree X F *
              (vinogradovTaylorDegree X F + 1))) := by
  have hV : 1 ≤ vinogradovAveragingRange X :=
    vinogradovAveragingRange_pos (show 1 ≤ X by linarith)
  calc
    (∏ j : Fin (vinogradovTaylorDegree X F),
      ∑ x ∈ vinogradovPowerBoxSide ell (vinogradovAveragingRange X) (j.1 + 1),
        ‖∑ y ∈ vinogradovPowerBoxSide ell (vinogradovAveragingRange X) (j.1 + 1),
          standardAdditiveCharacter
            (c (j.1 + 1) * (x : ℝ) * (y : ℝ))‖) ≤
        (∏ j : Fin (vinogradovTaylorDegree X F),
          vinogradovMediumCoordinateSavingFactor c
            (vinogradovAveragingRange X) ell (j.1 + 1) (1 / 8)) *
          ∏ j : Fin (vinogradovTaylorDegree X F),
            (((2 * (ell * vinogradovAveragingRange X ^ (j.1 + 1)) + 1 : ℕ) : ℝ)) ^ 2 := by
      exact prod_coordinateSums_le_prod_mediumSaving_mul_prod_side_sq
        c (vinogradovAveragingRange X) ell (vinogradovTaylorDegree X F)
        (1 / 8) hV hell (by norm_num)
    _ ≤ (vinogradovAveragingRange X : ℝ) ^
          (-(31 * (vinogradovTaylorDegree X F : ℝ) ^ 2) / 307200) *
        ∏ j : Fin (vinogradovTaylorDegree X F),
          (((2 * (ell * vinogradovAveragingRange X ^ (j.1 + 1)) + 1 : ℕ) : ℝ)) ^ 2 := by
      apply mul_le_mul_of_nonneg_right
      · exact source_prod_mediumSavingFactor_le_quadratic_rpow_eighth_of_nontrivialScale
          hX hFhigh hα hn hell hcoeff hsmall
      · positivity
    _ ≤ (vinogradovAveragingRange X : ℝ) ^
          (-(31 * (vinogradovTaylorDegree X F : ℝ) ^ 2) / 307200) *
        ((((3 * ell : ℕ) : ℝ)) ^
            (2 * vinogradovTaylorDegree X F) *
          (vinogradovAveragingRange X : ℝ) ^
            (vinogradovTaylorDegree X F *
              (vinogradovTaylorDegree X F + 1))) := by
      apply mul_le_mul_of_nonneg_left
      · exact prod_powerBoxSide_card_sq_le
          (vinogradovAveragingRange X) ell (vinogradovTaylorDegree X F)
          hV hell
      · positivity

/-- Lemma 12 with the sharp `c₀=1/4` medium window and exact critical box
power. -/
theorem source_prod_coordinateSums_le_quarterSaving_mul_criticalPower
    {X F α : ℝ} {n ell : ℕ} {c : ℕ → ℝ}
    (hX : 2 ≤ X) (hFhigh : X ^ 4 ≤ F) (hα : 1 ≤ α)
    (hn : (n : ℝ) ∈ Set.Icc X (2 * X)) (hell : 1 ≤ ell)
    (hcoeff : ∀ r : ℕ, 1 ≤ r → r ≤ vinogradovTaylorDegree X F →
      F / α ^ (r ^ 3) ≤ (n : ℝ) ^ r * |c r| ∧
        (n : ℝ) ^ r * |c r| ≤ α ^ (r ^ 3) * F)
    (hsmall : 2 * α * Real.exp
      (-((2 : ℝ) ^ (-18 : ℝ)) * (Real.log X) ^ 3 /
        (Real.log F) ^ 2) < 1) :
    (∏ j : Fin (vinogradovTaylorDegree X F),
      ∑ x ∈ vinogradovPowerBoxSide ell (vinogradovAveragingRange X) (j.1 + 1),
        ‖∑ y ∈ vinogradovPowerBoxSide ell (vinogradovAveragingRange X) (j.1 + 1),
          standardAdditiveCharacter
            (c (j.1 + 1) * (x : ℝ) * (y : ℝ))‖) ≤
      (vinogradovAveragingRange X : ℝ) ^
          (-(255 * (vinogradovTaylorDegree X F : ℝ) ^ 2) / 197632) *
        ((((3 * ell : ℕ) : ℝ)) ^
            (2 * vinogradovTaylorDegree X F) *
          (vinogradovAveragingRange X : ℝ) ^
            (vinogradovTaylorDegree X F *
              (vinogradovTaylorDegree X F + 1))) := by
  have hV : 1 ≤ vinogradovAveragingRange X :=
    vinogradovAveragingRange_pos (show 1 ≤ X by linarith)
  calc
    (∏ j : Fin (vinogradovTaylorDegree X F),
      ∑ x ∈ vinogradovPowerBoxSide ell (vinogradovAveragingRange X) (j.1 + 1),
        ‖∑ y ∈ vinogradovPowerBoxSide ell (vinogradovAveragingRange X) (j.1 + 1),
          standardAdditiveCharacter
            (c (j.1 + 1) * (x : ℝ) * (y : ℝ))‖) ≤
        (∏ j : Fin (vinogradovTaylorDegree X F),
          vinogradovMediumCoordinateSavingFactor c
            (vinogradovAveragingRange X) ell (j.1 + 1) (1 / 4)) *
          ∏ j : Fin (vinogradovTaylorDegree X F),
            (((2 * (ell * vinogradovAveragingRange X ^ (j.1 + 1)) + 1 : ℕ) : ℝ)) ^ 2 := by
      exact prod_coordinateSums_le_prod_mediumSaving_mul_prod_side_sq
        c (vinogradovAveragingRange X) ell (vinogradovTaylorDegree X F)
        (1 / 4) hV hell (by norm_num)
    _ ≤ (vinogradovAveragingRange X : ℝ) ^
          (-(255 * (vinogradovTaylorDegree X F : ℝ) ^ 2) / 197632) *
        ∏ j : Fin (vinogradovTaylorDegree X F),
          (((2 * (ell * vinogradovAveragingRange X ^ (j.1 + 1)) + 1 : ℕ) : ℝ)) ^ 2 := by
      apply mul_le_mul_of_nonneg_right
      · exact source_prod_mediumSavingFactor_le_quadratic_rpow_quarter_of_nontrivialScale
          hX hFhigh hα hn hell hcoeff hsmall
      · positivity
    _ ≤ (vinogradovAveragingRange X : ℝ) ^
          (-(255 * (vinogradovTaylorDegree X F : ℝ) ^ 2) / 197632) *
        ((((3 * ell : ℕ) : ℝ)) ^
            (2 * vinogradovTaylorDegree X F) *
          (vinogradovAveragingRange X : ℝ) ^
            (vinogradovTaylorDegree X F *
              (vinogradovTaylorDegree X F + 1))) := by
      apply mul_le_mul_of_nonneg_left
      · exact prod_powerBoxSide_card_sq_le
          (vinogradovAveragingRange X) ell (vinogradovTaylorDegree X F)
          hV hell
      · positivity

/-- The source coordinate-product estimate with the power-box cardinalities
collected into their exact critical-degree power of `V`. This is the form
needed for cancellation against the two critical Vinogradov moments. -/
theorem source_prod_coordinateSums_le_quadraticSaving_mul_criticalPower
    {X F α : ℝ} {n ell : ℕ} {c : ℕ → ℝ}
    (hX : 2 ≤ X) (hFhigh : X ^ 4 ≤ F) (hα : 1 ≤ α)
    (hn : (n : ℝ) ∈ Set.Icc X (2 * X)) (hell : 1 ≤ ell)
    (hcoeff : ∀ r : ℕ, 1 ≤ r → r ≤ vinogradovTaylorDegree X F →
      F / α ^ (r ^ 3) ≤ (n : ℝ) ^ r * |c r| ∧
        (n : ℝ) ^ r * |c r| ≤ α ^ (r ^ 3) * F)
    (hsmall : 2 * α * Real.exp
      (-((2 : ℝ) ^ (-18 : ℝ)) * (Real.log X) ^ 3 /
        (Real.log F) ^ 2) < 1) :
    (∏ j : Fin (vinogradovTaylorDegree X F),
      ∑ x ∈ vinogradovPowerBoxSide ell (vinogradovAveragingRange X) (j.1 + 1),
        ‖∑ y ∈ vinogradovPowerBoxSide ell (vinogradovAveragingRange X) (j.1 + 1),
          standardAdditiveCharacter
            (c (j.1 + 1) * (x : ℝ) * (y : ℝ))‖) ≤
      (vinogradovAveragingRange X : ℝ) ^
          (-(vinogradovTaylorDegree X F : ℝ) ^ 2 / 307200) *
        ((((3 * ell : ℕ) : ℝ)) ^
            (2 * vinogradovTaylorDegree X F) *
          (vinogradovAveragingRange X : ℝ) ^
            (vinogradovTaylorDegree X F *
              (vinogradovTaylorDegree X F + 1))) := by
  have hV : 1 ≤ vinogradovAveragingRange X :=
    vinogradovAveragingRange_pos (show 1 ≤ X by linarith)
  calc
    (∏ j : Fin (vinogradovTaylorDegree X F),
      ∑ x ∈ vinogradovPowerBoxSide ell (vinogradovAveragingRange X) (j.1 + 1),
        ‖∑ y ∈ vinogradovPowerBoxSide ell (vinogradovAveragingRange X) (j.1 + 1),
          standardAdditiveCharacter
            (c (j.1 + 1) * (x : ℝ) * (y : ℝ))‖) ≤
        (vinogradovAveragingRange X : ℝ) ^
            (-(vinogradovTaylorDegree X F : ℝ) ^ 2 / 307200) *
          ∏ j : Fin (vinogradovTaylorDegree X F),
            (((2 * (ell * vinogradovAveragingRange X ^ (j.1 + 1)) + 1 : ℕ) : ℝ)) ^ 2 :=
      source_prod_coordinateSums_le_quadraticSaving_of_nontrivialScale
        hX hFhigh hα hn hell hcoeff hsmall
    _ ≤ (vinogradovAveragingRange X : ℝ) ^
          (-(vinogradovTaylorDegree X F : ℝ) ^ 2 / 307200) *
        ((((3 * ell : ℕ) : ℝ)) ^
            (2 * vinogradovTaylorDegree X F) *
          (vinogradovAveragingRange X : ℝ) ^
            (vinogradovTaylorDegree X F *
              (vinogradovTaylorDegree X F + 1))) := by
      apply mul_le_mul_of_nonneg_left
      · exact prod_powerBoxSide_card_sq_le
          (vinogradovAveragingRange X) ell (vinogradovTaylorDegree X F)
          hV hell
      · positivity

/-- Product of the phases associated with an `ℓ`-tuple depends only on its
power-sum vector. -/
theorem prod_standardAdditiveCharacter_bilinear_curve_eq_tuplePowerSum
    (c : ℕ → ℝ) (R x : ℕ) {ℓ V : ℕ} (y : Fin ℓ → Fin V) :
    (∏ i, standardAdditiveCharacter
      (vinogradovCoefficientBilinearForm c R
        (vinogradovPolynomialCurve R x)
        (vinogradovPolynomialCurve R ((y i).1 + 1)))) =
      standardAdditiveCharacter
        (vinogradovCoefficientBilinearForm c R
          (vinogradovPolynomialCurve R x)
          (vinogradovTuplePowerSum R y)) := by
  rw [vinogradovCoefficientBilinearForm_curve_tuplePowerSum]
  exact (standardAdditiveCharacter_sum Finset.univ _).symm

/-- Product of phases along a tuple in the first variable depends only on
that tuple's power-sum vector. -/
theorem prod_standardAdditiveCharacter_tuplePowerSum_left
    (c : ℕ → ℝ) (R : ℕ) {ℓ V : ℕ} (x : Fin ℓ → Fin V)
    (u : Fin R → ℤ) :
    (∏ i, standardAdditiveCharacter
      (vinogradovCoefficientBilinearForm c R
        (vinogradovPolynomialCurve R ((x i).1 + 1)) u)) =
      standardAdditiveCharacter
        (vinogradovCoefficientBilinearForm c R
          (vinogradovTuplePowerSum R x) u) := by
  rw [vinogradovCoefficientBilinearForm_tuplePowerSum_left]
  exact (standardAdditiveCharacter_sum Finset.univ _).symm

/-- Expanding the `ℓ`-th power of an inner polynomial sum produces one phase
for each tuple, indexed only by its power-sum vector. -/
theorem vinogradovBilinearPolynomialInnerSum_pow_eq_sum_tuplePowerSum
    (c : ℕ → ℝ) (R V x ℓ : ℕ) :
    (vinogradovBilinearPolynomialInnerSum c R V x) ^ ℓ =
      ∑ y : Fin ℓ → Fin V, standardAdditiveCharacter
        (vinogradovCoefficientBilinearForm c R
          (vinogradovPolynomialCurve R x)
          (vinogradovTuplePowerSum R y)) := by
  rw [vinogradovBilinearPolynomialInnerSum_eq_sum_curve, Fintype.sum_pow]
  apply Finset.sum_congr rfl
  intro y hy
  exact prod_standardAdditiveCharacter_bilinear_curve_eq_tuplePowerSum c R x y

/-- Group the tuple expansion by power-sum vector, with the exact
representation multiplicity `ν`. -/
theorem vinogradovBilinearPolynomialInnerSum_pow_eq_sum_representationCount
    (c : ℕ → ℝ) (R V x ℓ : ℕ) :
    (vinogradovBilinearPolynomialInnerSum c R V x) ^ ℓ =
      ∑ u ∈ vinogradovPowerSumSupport ℓ R V,
        (vinogradovRepresentationCount ℓ R V u) •
          standardAdditiveCharacter
            (vinogradovCoefficientBilinearForm c R
              (vinogradovPolynomialCurve R x) u) := by
  rw [vinogradovBilinearPolynomialInnerSum_pow_eq_sum_tuplePowerSum]
  classical
  rw [← Finset.sum_fiberwise_of_maps_to
    (s := (Finset.univ : Finset (Fin ℓ → Fin V)))
    (t := vinogradovPowerSumSupport ℓ R V)
    (g := vinogradovTuplePowerSum R)
    (fun y hy => by
      rw [mem_vinogradovPowerSumSupport]
      exact ⟨y, rfl⟩)
    (fun y => standardAdditiveCharacter
      (vinogradovCoefficientBilinearForm c R
        (vinogradovPolynomialCurve R x)
        (vinogradovTuplePowerSum R y)))]
  apply Finset.sum_congr rfl
  intro u hu
  rw [Finset.sum_eq_card_nsmul]
  · rfl
  · intro y hy
    rw [Finset.mem_filter] at hy
    rw [hy.2]

/-- Unit-norm multiplier rotating a complex number to its nonnegative real
norm. -/
noncomputable def complexNormPhase (z : ℂ) : ℂ :=
  if z = 0 then 1 else (‖z‖ : ℂ) / z

theorem complexNormPhase_mul (z : ℂ) :
    complexNormPhase z * z = (‖z‖ : ℂ) := by
  by_cases hz : z = 0
  · simp [complexNormPhase, hz]
  · simp [complexNormPhase, hz]

@[simp]
theorem norm_complexNormPhase (z : ℂ) :
    ‖complexNormPhase z‖ = 1 := by
  by_cases hz : z = 0
  · simp [complexNormPhase, hz]
  · have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
    simp [complexNormPhase, hz, hn.ne']

/-- Raising the rotation identity to a natural power. -/
theorem complex_norm_pow_eq_phase_mul_pow (z : ℂ) (ℓ : ℕ) :
    ((‖z‖ ^ ℓ : ℝ) : ℂ) = (complexNormPhase z) ^ ℓ * z ^ ℓ := by
  rw [← mul_pow, complexNormPhase_mul]
  norm_num

/-- Unit coefficient used to remove the absolute value from the first Hölder
moment. -/
noncomputable def vinogradovOuterPhaseCoefficient
    (c : ℕ → ℝ) (R V ℓ x : ℕ) : ℂ :=
  (complexNormPhase (vinogradovBilinearPolynomialInnerSum c R V x)) ^ ℓ

@[simp]
theorem norm_vinogradovOuterPhaseCoefficient
    (c : ℕ → ℝ) (R V ℓ x : ℕ) :
    ‖vinogradovOuterPhaseCoefficient c R V ℓ x‖ = 1 := by
  simp [vinogradovOuterPhaseCoefficient, norm_pow]

/-- One summand in the linearized outer sum, indexed by `Fin V`. -/
noncomputable def vinogradovLinearizedTerm
    (c : ℕ → ℝ) (R V ℓ : ℕ) (u : Fin R → ℤ) (x : Fin V) : ℂ :=
  vinogradovOuterPhaseCoefficient c R V ℓ (x.1 + 1) *
    standardAdditiveCharacter
      (vinogradovCoefficientBilinearForm c R
        (vinogradovPolynomialCurve R (x.1 + 1)) u)

/-- Product of the unit outer coefficients along an `ℓ`-tuple. -/
noncomputable def vinogradovLinearizedTupleCoefficient
    (c : ℕ → ℝ) (R V ℓ : ℕ) (x : Fin ℓ → Fin V) : ℂ :=
  ∏ i, vinogradovOuterPhaseCoefficient c R V ℓ ((x i).1 + 1)

@[simp]
theorem norm_vinogradovLinearizedTupleCoefficient
    (c : ℕ → ℝ) (R V ℓ : ℕ) (x : Fin ℓ → Fin V) :
    ‖vinogradovLinearizedTupleCoefficient c R V ℓ x‖ = 1 := by
  simp [vinogradovLinearizedTupleCoefficient, norm_prod]

/-- Re-index the linearized outer sum by `Fin V`. -/
theorem vinogradovLinearizedSum_eq_sum_fin
    (c : ℕ → ℝ) (R V ℓ : ℕ) (u : Fin R → ℤ) :
    (∑ x ∈ Finset.Icc 1 V,
        vinogradovOuterPhaseCoefficient c R V ℓ x *
          standardAdditiveCharacter
            (vinogradovCoefficientBilinearForm c R
              (vinogradovPolynomialCurve R x) u)) =
      ∑ x : Fin V, vinogradovLinearizedTerm c R V ℓ u x := by
  rw [sum_Icc_one_eq_sum_fin]
  rfl

/-- The product of the linearized terms along a tuple is a unit coefficient
times the phase at the tuple power sum. -/
theorem prod_vinogradovLinearizedTerm
    (c : ℕ → ℝ) (R V ℓ : ℕ) (u : Fin R → ℤ)
    (x : Fin ℓ → Fin V) :
    (∏ i, vinogradovLinearizedTerm c R V ℓ u (x i)) =
      vinogradovLinearizedTupleCoefficient c R V ℓ x *
        standardAdditiveCharacter
          (vinogradovCoefficientBilinearForm c R
            (vinogradovTuplePowerSum R x) u) := by
  unfold vinogradovLinearizedTerm vinogradovLinearizedTupleCoefficient
  rw [Finset.prod_mul_distrib]
  rw [prod_standardAdditiveCharacter_tuplePowerSum_left]

/-- Unit coefficient left by a pair of tuple expansions. -/
noncomputable def vinogradovLinearizedPairCoefficient
    (c : ℕ → ℝ) (R V ℓ : ℕ)
    (p : (Fin ℓ → Fin V) × (Fin ℓ → Fin V)) : ℂ :=
  vinogradovLinearizedTupleCoefficient c R V ℓ p.1 *
    star (vinogradovLinearizedTupleCoefficient c R V ℓ p.2)

@[simp]
theorem norm_vinogradovLinearizedPairCoefficient
    (c : ℕ → ℝ) (R V ℓ : ℕ)
    (p : (Fin ℓ → Fin V) × (Fin ℓ → Fin V)) :
    ‖vinogradovLinearizedPairCoefficient c R V ℓ p‖ = 1 := by
  simp [vinogradovLinearizedPairCoefficient]

/-- A tuple phase times the conjugate of a second tuple phase is the phase at
their signed power-sum difference. -/
theorem prod_pair_vinogradovLinearizedTerm_eq_difference
    (c : ℕ → ℝ) (R V ℓ : ℕ) (u : Fin R → ℤ)
    (p : (Fin ℓ → Fin V) × (Fin ℓ → Fin V)) :
    (∏ i, vinogradovLinearizedTerm c R V ℓ u (p.1 i)) *
        star (∏ i, vinogradovLinearizedTerm c R V ℓ u (p.2 i)) =
      vinogradovLinearizedPairCoefficient c R V ℓ p *
        standardAdditiveCharacter
          (vinogradovCoefficientBilinearForm c R
            (vinogradovTuplePowerDifference R p) u) := by
  rw [prod_vinogradovLinearizedTerm, prod_vinogradovLinearizedTerm]
  have hstar (a b : ℂ) : star (a * b) = star a * star b := by
    change (starRingEnd ℂ) (a * b) = _
    exact map_mul (starRingEnd ℂ) a b
  rw [hstar]
  change
    (vinogradovLinearizedTupleCoefficient c R V ℓ p.1 *
        standardAdditiveCharacter
          (vinogradovCoefficientBilinearForm c R
            (vinogradovTuplePowerSum R p.1) u)) *
      (star (vinogradovLinearizedTupleCoefficient c R V ℓ p.2) *
        (starRingEnd ℂ) (standardAdditiveCharacter
          (vinogradovCoefficientBilinearForm c R
            (vinogradovTuplePowerSum R p.2) u))) = _
  rw [mul_mul_mul_comm]
  rw [standardAdditiveCharacter_mul_conj]
  unfold vinogradovLinearizedPairCoefficient
  rw [← vinogradovCoefficientBilinearForm_sub_left]
  rfl

/-- Exact `2ℓ`-moment expansion of one linearized sum, indexed by signed
power-sum differences. -/
theorem coe_norm_linearized_sum_pow_eq_sum_powerDifference
    (c : ℕ → ℝ) (R V ℓ : ℕ) (u : Fin R → ℤ) :
    ((‖∑ x ∈ Finset.Icc 1 V,
        vinogradovOuterPhaseCoefficient c R V ℓ x *
          standardAdditiveCharacter
            (vinogradovCoefficientBilinearForm c R
              (vinogradovPolynomialCurve R x) u)‖ ^ (2 * ℓ) : ℝ) : ℂ) =
      ∑ p : (Fin ℓ → Fin V) × (Fin ℓ → Fin V),
        vinogradovLinearizedPairCoefficient c R V ℓ p *
          standardAdditiveCharacter
            (vinogradovCoefficientBilinearForm c R
              (vinogradovTuplePowerDifference R p) u) := by
  rw [vinogradovLinearizedSum_eq_sum_fin,
    complex_norm_sum_even_pow_eq_sum_pair]
  apply Finset.sum_congr rfl
  intro p hp
  exact prod_pair_vinogradovLinearizedTerm_eq_difference c R V ℓ u p

/-- Pointwise removal of the absolute value followed by grouping the tuple
expansion according to its representation count. -/
theorem coe_norm_inner_pow_eq_phase_mul_representationCount
    (c : ℕ → ℝ) (R V x ℓ : ℕ) :
    ((‖vinogradovBilinearPolynomialInnerSum c R V x‖ ^ ℓ : ℝ) : ℂ) =
      vinogradovOuterPhaseCoefficient c R V ℓ x *
        ∑ u ∈ vinogradovPowerSumSupport ℓ R V,
          (vinogradovRepresentationCount ℓ R V u) •
            standardAdditiveCharacter
              (vinogradovCoefficientBilinearForm c R
                (vinogradovPolynomialCurve R x) u) := by
  rw [complex_norm_pow_eq_phase_mul_pow]
  unfold vinogradovOuterPhaseCoefficient
  rw [vinogradovBilinearPolynomialInnerSum_pow_eq_sum_representationCount]

/-- Equation (13)--(14) after the first Hölder step: the sum of absolute
moments is an exact representation-weighted linearized bilinear sum. -/
theorem coe_sum_norm_inner_pow_eq_sum_representationCount_mul_linearized
    (c : ℕ → ℝ) (R V ℓ : ℕ) :
    (∑ x ∈ Finset.Icc 1 V,
        ((‖vinogradovBilinearPolynomialInnerSum c R V x‖ ^ ℓ : ℝ) : ℂ)) =
      ∑ u ∈ vinogradovPowerSumSupport ℓ R V,
        (vinogradovRepresentationCount ℓ R V u) •
          (∑ x ∈ Finset.Icc 1 V,
            vinogradovOuterPhaseCoefficient c R V ℓ x *
              standardAdditiveCharacter
                (vinogradovCoefficientBilinearForm c R
                  (vinogradovPolynomialCurve R x) u)) := by
  simp_rw [coe_norm_inner_pow_eq_phase_mul_representationCount]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u hu
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  simp only [nsmul_eq_mul]
  ring

/-- The norm of a complex sum of nonnegative real numbers is the original
real sum. -/
theorem norm_sum_coe_eq_sum_of_nonneg {ι : Type*}
    (s : Finset ι) (f : ι → ℝ) (hf : ∀ i ∈ s, 0 ≤ f i) :
    ‖∑ i ∈ s, (f i : ℂ)‖ = ∑ i ∈ s, f i := by
  rw [← Complex.ofReal_sum, Complex.norm_real]
  exact Real.norm_of_nonneg (Finset.sum_nonneg hf)

/-- Triangle inequality after the exact representation-weighted
linearization of the first Hölder moment. -/
theorem sum_norm_inner_pow_le_representationCount_mul_norm_linearized
    (c : ℕ → ℝ) (R V ℓ : ℕ) :
    (∑ x ∈ Finset.Icc 1 V,
        ‖vinogradovBilinearPolynomialInnerSum c R V x‖ ^ ℓ : ℝ) ≤
      ∑ u ∈ vinogradovPowerSumSupport ℓ R V,
        (vinogradovRepresentationCount ℓ R V u : ℝ) *
          ‖∑ x ∈ Finset.Icc 1 V,
            vinogradovOuterPhaseCoefficient c R V ℓ x *
              standardAdditiveCharacter
                (vinogradovCoefficientBilinearForm c R
                  (vinogradovPolynomialCurve R x) u)‖ := by
  let lhs : ℝ := ∑ x ∈ Finset.Icc 1 V,
    ‖vinogradovBilinearPolynomialInnerSum c R V x‖ ^ ℓ
  let rhs : ℂ := ∑ u ∈ vinogradovPowerSumSupport ℓ R V,
    (vinogradovRepresentationCount ℓ R V u) •
      (∑ x ∈ Finset.Icc 1 V,
        vinogradovOuterPhaseCoefficient c R V ℓ x *
          standardAdditiveCharacter
            (vinogradovCoefficientBilinearForm c R
              (vinogradovPolynomialCurve R x) u))
  have heq : (∑ x ∈ Finset.Icc 1 V,
      ((‖vinogradovBilinearPolynomialInnerSum c R V x‖ ^ ℓ : ℝ) : ℂ)) = rhs :=
    coe_sum_norm_inner_pow_eq_sum_representationCount_mul_linearized c R V ℓ
  have hlhs : ‖∑ x ∈ Finset.Icc 1 V,
      ((‖vinogradovBilinearPolynomialInnerSum c R V x‖ ^ ℓ : ℝ) : ℂ)‖ = lhs := by
    apply norm_sum_coe_eq_sum_of_nonneg
    intro x hx
    positivity
  calc
    (∑ x ∈ Finset.Icc 1 V,
        ‖vinogradovBilinearPolynomialInnerSum c R V x‖ ^ ℓ : ℝ) = lhs := rfl
    _ = ‖rhs‖ := by rw [← hlhs, heq]
    _ ≤ ∑ u ∈ vinogradovPowerSumSupport ℓ R V,
        ‖(vinogradovRepresentationCount ℓ R V u) •
          (∑ x ∈ Finset.Icc 1 V,
            vinogradovOuterPhaseCoefficient c R V ℓ x *
              standardAdditiveCharacter
                (vinogradovCoefficientBilinearForm c R
                  (vinogradovPolynomialCurve R x) u))‖ := norm_sum_le _ _
    _ = ∑ u ∈ vinogradovPowerSumSupport ℓ R V,
        (vinogradovRepresentationCount ℓ R V u : ℝ) *
          ‖∑ x ∈ Finset.Icc 1 V,
            vinogradovOuterPhaseCoefficient c R V ℓ x *
              standardAdditiveCharacter
                (vinogradovCoefficientBilinearForm c R
                  (vinogradovPolynomialCurve R x) u)‖ := by
      apply Finset.sum_congr rfl
      intro u hu
      simp [nsmul_eq_mul]

/-- The three-factor Hölder interpolation used in the second moment step.
The exponent `L` is kept real here so that the two nested Hölder inequalities
can use their natural conjugate exponents. -/
theorem nnreal_sum_mul_rpow_le_interpolation
    {ι : Type*} (s : Finset ι) (ν A : ι → ℝ≥0) (L : ℝ) (hL : 2 < L) :
    (∑ i ∈ s, ν i * A i) ^ L ≤
      (∑ i ∈ s, ν i) ^ (L - 2) *
        (∑ i ∈ s, ν i ^ (2 : ℝ)) *
          (∑ i ∈ s, A i ^ L) := by
  let p : ℝ := L / (L - 1)
  let q₁ : ℝ := (L - 1) / (L - 2)
  let q₂ : ℝ := L - 1
  have hpL : p.HolderConjugate L := by
    rw [Real.holderConjugate_iff]
    constructor
    · dsimp [p]
      rw [one_lt_div₀ (by linarith)]
      linarith
    · dsimp [p]
      field_simp [ne_of_gt (show 0 < L - 1 by linarith)]
      ring
  have hq : q₁.HolderConjugate q₂ := by
    rw [Real.holderConjugate_iff]
    constructor
    · dsimp [q₁]
      rw [one_lt_div₀ (by linarith)]
      linarith
    · dsimp [q₁, q₂]
      field_simp [ne_of_gt (show 0 < L - 2 by linarith),
        ne_of_gt (show 0 < L - 1 by linarith)]
      ring
  have houter := NNReal.inner_le_Lp_mul_Lq s ν A hpL
  have hinter := NNReal.inner_le_Lp_mul_Lq s
    (fun i => ν i ^ ((L - 2) / (L - 1)))
    (fun i => ν i ^ (2 / (L - 1))) hq
  dsimp [p] at houter
  dsimp [q₁, q₂] at hinter
  have hinter' :
      (∑ i ∈ s, ν i ^ (L / (L - 1))) ≤
        (∑ i ∈ s, ν i) ^ ((L - 2) / (L - 1)) *
          (∑ i ∈ s, ν i ^ (2 : ℝ)) ^ (1 / (L - 1)) := by
    convert hinter using 1
    · apply Finset.sum_congr rfl
      intro i hi
      by_cases hν : ν i = 0
      · have h₀ : 0 < L / (L - 1) := div_pos (by linarith) (by linarith)
        have h₁ : 0 < (L - 2) / (L - 1) := div_pos (by linarith) (by linarith)
        have h₂ : 0 < 2 / (L - 1) := div_pos (by norm_num) (by linarith)
        simp [hν, NNReal.zero_rpow, h₀.ne', h₁.ne', h₂.ne']
      · rw [← NNReal.rpow_add hν]
        congr 1
        field_simp [ne_of_gt (show 0 < L - 1 by linarith)]
        ring
    · congr 1
      · congr 1
        · apply Finset.sum_congr rfl
          intro i hi
          rw [← NNReal.rpow_mul]
          field_simp [ne_of_gt (show 0 < L - 2 by linarith),
            ne_of_gt (show 0 < L - 1 by linarith)]
          simp
        · field_simp [ne_of_gt (show 0 < L - 2 by linarith),
            ne_of_gt (show 0 < L - 1 by linarith)]
      · congr 1
        apply Finset.sum_congr rfl
        intro i hi
        rw [← NNReal.rpow_mul]
        congr 1
        field_simp [ne_of_gt (show 0 < L - 1 by linarith)]
  have hraw :
      (∑ i ∈ s, ν i * A i) ≤
        ((∑ i ∈ s, ν i) ^ ((L - 2) / (L - 1)) *
          (∑ i ∈ s, ν i ^ (2 : ℝ)) ^ (1 / (L - 1))) ^
            (1 / (L / (L - 1))) *
          (∑ i ∈ s, A i ^ L) ^ (1 / L) :=
    houter.trans (mul_le_mul_left
      (NNReal.rpow_le_rpow hinter'
        (show 0 ≤ 1 / (L / (L - 1)) by
          exact le_of_lt (one_div_pos.mpr (div_pos (by linarith) (by linarith))))) _)
  have hmain :
      (∑ i ∈ s, ν i * A i) ≤
        (∑ i ∈ s, ν i) ^ ((L - 2) / L) *
          (∑ i ∈ s, ν i ^ (2 : ℝ)) ^ (1 / L) *
            (∑ i ∈ s, A i ^ L) ^ (1 / L) := by
    convert hraw using 1
    rw [NNReal.mul_rpow, ← NNReal.rpow_mul, ← NNReal.rpow_mul]
    congr 2
    · field_simp [ne_of_gt (show 0 < L - 1 by linarith),
        ne_of_gt (show 0 < L by linarith)]
    · field_simp [ne_of_gt (show 0 < L - 1 by linarith),
        ne_of_gt (show 0 < L by linarith)]
  have hpow := NNReal.rpow_le_rpow hmain (show 0 ≤ L by linarith)
  convert hpow using 1
  rw [NNReal.mul_rpow, NNReal.mul_rpow, ← NNReal.rpow_mul,
    ← NNReal.rpow_mul, ← NNReal.rpow_mul]
  have hinv : 1 / L * L = 1 := by
    field_simp [ne_of_gt (show 0 < L by linarith)]
  rw [hinv]
  simp only [NNReal.rpow_one]
  congr 2
  field_simp [ne_of_gt (show 0 < L by linarith)]

/-- Integer-power form of the second Hölder interpolation. The endpoint
`ℓ = 1` is exactly Cauchy--Schwarz; larger exponents follow from the real
interpolation lemma. -/
theorem nnreal_sum_mul_pow_le_interpolation
    {ι : Type*} (s : Finset ι) (ν A : ι → ℝ≥0) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    (∑ i ∈ s, ν i * A i) ^ (2 * ℓ) ≤
      (∑ i ∈ s, ν i) ^ (2 * ℓ - 2) *
        (∑ i ∈ s, ν i ^ 2) *
          (∑ i ∈ s, A i ^ (2 * ℓ)) := by
  rcases hℓ.eq_or_lt with rfl | hℓ
  · simpa using Finset.sum_mul_sq_le_sq_mul_sq s ν A
  · have h := nnreal_sum_mul_rpow_le_interpolation s ν A (2 * ℓ : ℝ)
      (by exact_mod_cast (show 2 < 2 * ℓ by omega))
    have hmul : (2 : ℝ) * ℓ = ((2 * ℓ : ℕ) : ℝ) := by norm_num
    have hsub : ((2 * ℓ - 2 : ℕ) : ℝ) = ((2 * ℓ : ℕ) : ℝ) - 2 := by
      rw [Nat.cast_sub (by omega)]
      norm_num
    rw [hmul, ← hsub] at h
    have htwo (x : ℝ≥0) : x ^ (2 : ℝ) = x ^ (2 : ℕ) := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, NNReal.rpow_natCast]
    simp_rw [htwo] at h
    simpa only [NNReal.rpow_natCast] using h

/-- Real-valued nonnegative form of the second Hölder interpolation. -/
theorem sum_mul_pow_le_interpolation_of_nonneg
    {ι : Type*} (s : Finset ι) (ν A : ι → ℝ) (ℓ : ℕ) (hℓ : 1 ≤ ℓ)
    (hν : ∀ i, 0 ≤ ν i) (hA : ∀ i, 0 ≤ A i) :
    (∑ i ∈ s, ν i * A i) ^ (2 * ℓ) ≤
      (∑ i ∈ s, ν i) ^ (2 * ℓ - 2) *
        (∑ i ∈ s, ν i ^ 2) *
          (∑ i ∈ s, A i ^ (2 * ℓ)) := by
  lift ν to ι → ℝ≥0 using hν
  lift A to ι → ℝ≥0 using hA
  beta_reduce at *
  norm_cast at *
  exact nnreal_sum_mul_pow_le_interpolation s ν A ℓ hℓ

/-- Norm of the linearized outer sum attached to a power-sum vector. -/
noncomputable def vinogradovLinearizedSumNorm
    (c : ℕ → ℝ) (R V ℓ : ℕ) (u : Fin R → ℤ) : ℝ :=
  ‖∑ x ∈ Finset.Icc 1 V,
      vinogradovOuterPhaseCoefficient c R V ℓ x *
        standardAdditiveCharacter
          (vinogradovCoefficientBilinearForm c R
            (vinogradovPolynomialCurve R x) u)‖

theorem vinogradovLinearizedSumNorm_nonneg
    (c : ℕ → ℝ) (R V ℓ : ℕ) (u : Fin R → ℤ) :
    0 ≤ vinogradovLinearizedSumNorm c R V ℓ u := by
  exact norm_nonneg _

/-- Even-moment expansion and triangle inequality over an arbitrary finite set
of power-sum vectors. -/
theorem sum_linearizedMoment_on_le_sum_pair_phase
    (c : ℕ → ℝ) (R V ℓ : ℕ) (Y : Finset (Fin R → ℤ)) :
    (∑ u ∈ Y, vinogradovLinearizedSumNorm c R V ℓ u ^ (2 * ℓ)) ≤
      ∑ p : (Fin ℓ → Fin V) × (Fin ℓ → Fin V),
        ‖∑ u ∈ Y, standardAdditiveCharacter
          (vinogradovCoefficientBilinearForm c R
            (vinogradovTuplePowerDifference R p) u)‖ := by
  have hexact :
      (∑ u ∈ Y,
        ((vinogradovLinearizedSumNorm c R V ℓ u ^ (2 * ℓ) : ℝ) : ℂ)) =
        ∑ p : (Fin ℓ → Fin V) × (Fin ℓ → Fin V),
          vinogradovLinearizedPairCoefficient c R V ℓ p *
            (∑ u ∈ Y, standardAdditiveCharacter
              (vinogradovCoefficientBilinearForm c R
                (vinogradovTuplePowerDifference R p) u)) := by
    simp_rw [vinogradovLinearizedSumNorm,
      coe_norm_linearized_sum_pow_eq_sum_powerDifference]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p hp
    simp_rw [Finset.mul_sum]
  have hlhs :
      ‖∑ u ∈ Y,
        ((vinogradovLinearizedSumNorm c R V ℓ u ^ (2 * ℓ) : ℝ) : ℂ)‖ =
        ∑ u ∈ Y, vinogradovLinearizedSumNorm c R V ℓ u ^ (2 * ℓ) := by
    apply norm_sum_coe_eq_sum_of_nonneg
    intro u hu
    exact pow_nonneg (vinogradovLinearizedSumNorm_nonneg c R V ℓ u) _
  calc
    (∑ u ∈ Y, vinogradovLinearizedSumNorm c R V ℓ u ^ (2 * ℓ)) =
      ‖∑ u ∈ Y,
        ((vinogradovLinearizedSumNorm c R V ℓ u ^ (2 * ℓ) : ℝ) : ℂ)‖ :=
          hlhs.symm
    _ = ‖∑ p : (Fin ℓ → Fin V) × (Fin ℓ → Fin V),
          vinogradovLinearizedPairCoefficient c R V ℓ p *
            (∑ u ∈ Y, standardAdditiveCharacter
              (vinogradovCoefficientBilinearForm c R
                (vinogradovTuplePowerDifference R p) u))‖ := by rw [hexact]
    _ ≤ ∑ p : (Fin ℓ → Fin V) × (Fin ℓ → Fin V),
        ‖vinogradovLinearizedPairCoefficient c R V ℓ p *
          (∑ u ∈ Y, standardAdditiveCharacter
            (vinogradovCoefficientBilinearForm c R
              (vinogradovTuplePowerDifference R p) u))‖ := norm_sum_le _ _
    _ = ∑ p : (Fin ℓ → Fin V) × (Fin ℓ → Fin V),
        ‖∑ u ∈ Y, standardAdditiveCharacter
          (vinogradovCoefficientBilinearForm c R
            (vinogradovTuplePowerDifference R p) u)‖ := by
        apply Finset.sum_congr rfl
        intro p hp
        rw [norm_mul, norm_vinogradovLinearizedPairCoefficient, one_mul]

/-- Regroup the tuple-pair phase sum over an arbitrary finite inner set by
signed power-sum difference. -/
theorem sum_pair_phase_on_eq_differenceRepresentationCount
    (c : ℕ → ℝ) (R V ℓ : ℕ) (Y : Finset (Fin R → ℤ)) :
    (∑ p : (Fin ℓ → Fin V) × (Fin ℓ → Fin V),
        ‖∑ u ∈ Y, standardAdditiveCharacter
          (vinogradovCoefficientBilinearForm c R
            (vinogradovTuplePowerDifference R p) u)‖) =
      ∑ d ∈ vinogradovPowerDifferenceSupport ℓ R V,
        (vinogradovDifferenceRepresentationCount ℓ R V d : ℝ) *
          ‖∑ u ∈ Y, standardAdditiveCharacter
            (vinogradovCoefficientBilinearForm c R d u)‖ := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to
    (s := (Finset.univ : Finset
      ((Fin ℓ → Fin V) × (Fin ℓ → Fin V))))
    (t := vinogradovPowerDifferenceSupport ℓ R V)
    (g := vinogradovTuplePowerDifference R)
    (fun p hp => by
      rw [mem_vinogradovPowerDifferenceSupport]
      exact ⟨p, rfl⟩)
    (fun p => ‖∑ u ∈ Y, standardAdditiveCharacter
      (vinogradovCoefficientBilinearForm c R
        (vinogradovTuplePowerDifference R p) u)‖)]
  apply Finset.sum_congr rfl
  intro d hd
  let Fd : ℝ := ‖∑ u ∈ Y, standardAdditiveCharacter
    (vinogradovCoefficientBilinearForm c R d u)‖
  rw [Finset.sum_eq_card_nsmul (b := Fd)]
  · have huniv :
        (Finset.univ : Finset
          ((Fin ℓ → Fin V) × (Fin ℓ → Fin V))) =
          (Finset.univ : Finset (Fin ℓ → Fin V)) ×ˢ
            (Finset.univ : Finset (Fin ℓ → Fin V)) := by
        ext p
        simp
    unfold vinogradovDifferenceRepresentationCount
    rw [huniv]
    simp only [nsmul_eq_mul]
    rfl
  · intro p hp
    rw [Finset.mem_filter] at hp
    dsimp [Fd]
    rw [hp.2]

/-- The difference-multiplicity estimate with an arbitrary finite inner set. -/
theorem sum_linearizedMoment_on_le_meanValue_mul_differencePhase
    (c : ℕ → ℝ) (R V ℓ : ℕ) (Y : Finset (Fin R → ℤ)) :
    (∑ u ∈ Y, vinogradovLinearizedSumNorm c R V ℓ u ^ (2 * ℓ)) ≤
      (vinogradovMeanValueCount ℓ R V : ℝ) *
        ∑ d ∈ vinogradovPowerDifferenceSupport ℓ R V,
          ‖∑ u ∈ Y, standardAdditiveCharacter
            (vinogradovCoefficientBilinearForm c R d u)‖ := by
  calc
    (∑ u ∈ Y, vinogradovLinearizedSumNorm c R V ℓ u ^ (2 * ℓ)) ≤
      ∑ p : (Fin ℓ → Fin V) × (Fin ℓ → Fin V),
        ‖∑ u ∈ Y, standardAdditiveCharacter
          (vinogradovCoefficientBilinearForm c R
            (vinogradovTuplePowerDifference R p) u)‖ :=
        sum_linearizedMoment_on_le_sum_pair_phase c R V ℓ Y
    _ = ∑ d ∈ vinogradovPowerDifferenceSupport ℓ R V,
        (vinogradovDifferenceRepresentationCount ℓ R V d : ℝ) *
          ‖∑ u ∈ Y, standardAdditiveCharacter
            (vinogradovCoefficientBilinearForm c R d u)‖ :=
        sum_pair_phase_on_eq_differenceRepresentationCount c R V ℓ Y
    _ ≤ ∑ d ∈ vinogradovPowerDifferenceSupport ℓ R V,
        (vinogradovMeanValueCount ℓ R V : ℝ) *
          ‖∑ u ∈ Y, standardAdditiveCharacter
            (vinogradovCoefficientBilinearForm c R d u)‖ := by
        apply Finset.sum_le_sum
        intro d hd
        apply mul_le_mul_of_nonneg_right
        · exact_mod_cast
            vinogradovDifferenceRepresentationCount_le_meanValueCount ℓ R V d
        · exact norm_nonneg _
    _ = (vinogradovMeanValueCount ℓ R V : ℝ) *
        ∑ d ∈ vinogradovPowerDifferenceSupport ℓ R V,
          ‖∑ u ∈ Y, standardAdditiveCharacter
            (vinogradovCoefficientBilinearForm c R d u)‖ := by
        rw [Finset.mul_sum]

/-- Tao's equation (18) with both variables enlarged to the full symmetric
power-sum box. -/
theorem sum_linearizedMoment_le_meanValue_mul_powerBoxPhase
    (c : ℕ → ℝ) (R V ℓ : ℕ) :
    (∑ u ∈ vinogradovPowerSumSupport ℓ R V,
        vinogradovLinearizedSumNorm c R V ℓ u ^ (2 * ℓ)) ≤
      (vinogradovMeanValueCount ℓ R V : ℝ) *
        ∑ d ∈ vinogradovPowerBox ℓ R V,
          ‖∑ u ∈ vinogradovPowerBox ℓ R V,
            standardAdditiveCharacter
              (vinogradovCoefficientBilinearForm c R d u)‖ := by
  calc
    (∑ u ∈ vinogradovPowerSumSupport ℓ R V,
        vinogradovLinearizedSumNorm c R V ℓ u ^ (2 * ℓ)) ≤
      ∑ u ∈ vinogradovPowerBox ℓ R V,
        vinogradovLinearizedSumNorm c R V ℓ u ^ (2 * ℓ) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
            (vinogradovPowerSumSupport_subset_powerBox ℓ R V)
          intro u hu hnot
          exact pow_nonneg (vinogradovLinearizedSumNorm_nonneg c R V ℓ u) _
    _ ≤ (vinogradovMeanValueCount ℓ R V : ℝ) *
        ∑ d ∈ vinogradovPowerDifferenceSupport ℓ R V,
          ‖∑ u ∈ vinogradovPowerBox ℓ R V,
            standardAdditiveCharacter
              (vinogradovCoefficientBilinearForm c R d u)‖ :=
        sum_linearizedMoment_on_le_meanValue_mul_differencePhase
          c R V ℓ (vinogradovPowerBox ℓ R V)
    _ ≤ (vinogradovMeanValueCount ℓ R V : ℝ) *
        ∑ d ∈ vinogradovPowerBox ℓ R V,
          ‖∑ u ∈ vinogradovPowerBox ℓ R V,
            standardAdditiveCharacter
              (vinogradovCoefficientBilinearForm c R d u)‖ := by
          apply mul_le_mul_of_nonneg_left
          · apply Finset.sum_le_sum_of_subset_of_nonneg
              (vinogradovPowerDifferenceSupport_subset_powerBox ℓ R V)
            intro d hd hnot
            exact norm_nonneg _
          · positivity

/-- Equation (18) with the full box phase expression replaced by its exact
product of one-dimensional coordinate sums. -/
theorem sum_linearizedMoment_le_meanValue_mul_prod_coordinateSums
    (c : ℕ → ℝ) (R V ℓ : ℕ) :
    (∑ u ∈ vinogradovPowerSumSupport ℓ R V,
        vinogradovLinearizedSumNorm c R V ℓ u ^ (2 * ℓ)) ≤
      (vinogradovMeanValueCount ℓ R V : ℝ) *
        ∏ j : Fin R, ∑ x ∈ vinogradovPowerBoxSide ℓ V (j.1 + 1),
          ‖∑ y ∈ vinogradovPowerBoxSide ℓ V (j.1 + 1),
            standardAdditiveCharacter
              (c (j.1 + 1) * (x : ℝ) * (y : ℝ))‖ := by
  rw [← sum_norm_powerBox_phase_eq_prod_coordinateSums]
  exact sum_linearizedMoment_le_meanValue_mul_powerBoxPhase c R V ℓ

/-- After the exact even-moment expansion and the triangle inequality, the
linearized moment is bounded by one phase sum for every ordered tuple pair. -/
theorem sum_linearizedMoment_le_sum_pair_phase
    (c : ℕ → ℝ) (R V ℓ : ℕ) :
    (∑ u ∈ vinogradovPowerSumSupport ℓ R V,
        vinogradovLinearizedSumNorm c R V ℓ u ^ (2 * ℓ)) ≤
      ∑ p : (Fin ℓ → Fin V) × (Fin ℓ → Fin V),
        ‖∑ u ∈ vinogradovPowerSumSupport ℓ R V,
          standardAdditiveCharacter
            (vinogradovCoefficientBilinearForm c R
              (vinogradovTuplePowerDifference R p) u)‖ := by
  let S := vinogradovPowerSumSupport ℓ R V
  have hexact :
      (∑ u ∈ S,
        ((vinogradovLinearizedSumNorm c R V ℓ u ^ (2 * ℓ) : ℝ) : ℂ)) =
        ∑ p : (Fin ℓ → Fin V) × (Fin ℓ → Fin V),
          vinogradovLinearizedPairCoefficient c R V ℓ p *
            (∑ u ∈ S, standardAdditiveCharacter
              (vinogradovCoefficientBilinearForm c R
                (vinogradovTuplePowerDifference R p) u)) := by
    dsimp [S]
    simp_rw [vinogradovLinearizedSumNorm,
      coe_norm_linearized_sum_pow_eq_sum_powerDifference]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p hp
    simp_rw [Finset.mul_sum]
  have hlhs :
      ‖∑ u ∈ S,
        ((vinogradovLinearizedSumNorm c R V ℓ u ^ (2 * ℓ) : ℝ) : ℂ)‖ =
        ∑ u ∈ S, vinogradovLinearizedSumNorm c R V ℓ u ^ (2 * ℓ) := by
    apply norm_sum_coe_eq_sum_of_nonneg
    intro u hu
    exact pow_nonneg (vinogradovLinearizedSumNorm_nonneg c R V ℓ u) _
  calc
    (∑ u ∈ vinogradovPowerSumSupport ℓ R V,
        vinogradovLinearizedSumNorm c R V ℓ u ^ (2 * ℓ)) =
      ‖∑ u ∈ S,
        ((vinogradovLinearizedSumNorm c R V ℓ u ^ (2 * ℓ) : ℝ) : ℂ)‖ := by
          rw [hlhs]
    _ = ‖∑ p : (Fin ℓ → Fin V) × (Fin ℓ → Fin V),
          vinogradovLinearizedPairCoefficient c R V ℓ p *
            (∑ u ∈ S, standardAdditiveCharacter
              (vinogradovCoefficientBilinearForm c R
                (vinogradovTuplePowerDifference R p) u))‖ := by rw [hexact]
    _ ≤ ∑ p : (Fin ℓ → Fin V) × (Fin ℓ → Fin V),
        ‖vinogradovLinearizedPairCoefficient c R V ℓ p *
          (∑ u ∈ S, standardAdditiveCharacter
            (vinogradovCoefficientBilinearForm c R
              (vinogradovTuplePowerDifference R p) u))‖ := norm_sum_le _ _
    _ = ∑ p : (Fin ℓ → Fin V) × (Fin ℓ → Fin V),
        ‖∑ u ∈ vinogradovPowerSumSupport ℓ R V,
          standardAdditiveCharacter
            (vinogradovCoefficientBilinearForm c R
              (vinogradovTuplePowerDifference R p) u)‖ := by
        dsimp [S]
        apply Finset.sum_congr rfl
        intro p hp
        rw [norm_mul, norm_vinogradovLinearizedPairCoefficient, one_mul]

/-- Regroup the tuple-pair phase sum by signed power-sum difference, with its
exact representation multiplicity. -/
theorem sum_pair_phase_eq_differenceRepresentationCount
    (c : ℕ → ℝ) (R V ℓ : ℕ) :
    (∑ p : (Fin ℓ → Fin V) × (Fin ℓ → Fin V),
        ‖∑ u ∈ vinogradovPowerSumSupport ℓ R V,
          standardAdditiveCharacter
            (vinogradovCoefficientBilinearForm c R
              (vinogradovTuplePowerDifference R p) u)‖) =
      ∑ d ∈ vinogradovPowerDifferenceSupport ℓ R V,
        (vinogradovDifferenceRepresentationCount ℓ R V d : ℝ) *
          ‖∑ u ∈ vinogradovPowerSumSupport ℓ R V,
            standardAdditiveCharacter
              (vinogradovCoefficientBilinearForm c R d u)‖ := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to
    (s := (Finset.univ : Finset
      ((Fin ℓ → Fin V) × (Fin ℓ → Fin V))))
    (t := vinogradovPowerDifferenceSupport ℓ R V)
    (g := vinogradovTuplePowerDifference R)
    (fun p hp => by
      rw [mem_vinogradovPowerDifferenceSupport]
      exact ⟨p, rfl⟩)
    (fun p => ‖∑ u ∈ vinogradovPowerSumSupport ℓ R V,
      standardAdditiveCharacter
        (vinogradovCoefficientBilinearForm c R
          (vinogradovTuplePowerDifference R p) u)‖)]
  apply Finset.sum_congr rfl
  intro d hd
  let Fd : ℝ := ‖∑ u ∈ vinogradovPowerSumSupport ℓ R V,
    standardAdditiveCharacter (vinogradovCoefficientBilinearForm c R d u)‖
  rw [Finset.sum_eq_card_nsmul (b := Fd)]
  · have huniv :
        (Finset.univ : Finset
          ((Fin ℓ → Fin V) × (Fin ℓ → Fin V))) =
          (Finset.univ : Finset (Fin ℓ → Fin V)) ×ˢ
            (Finset.univ : Finset (Fin ℓ → Fin V)) := by
        ext p
        simp
    unfold vinogradovDifferenceRepresentationCount
    rw [huniv]
    simp only [nsmul_eq_mul]
    rfl
  · intro p hp
    rw [Finset.mem_filter] at hp
    dsimp [Fd]
    rw [hp.2]

/-- Equation (18): the linearized `2ℓ`-moment is controlled by the
Vinogradov mean value times a sum of additive-character norms over the signed
power-sum difference support. -/
theorem sum_linearizedMoment_le_meanValue_mul_differencePhase
    (c : ℕ → ℝ) (R V ℓ : ℕ) :
    (∑ u ∈ vinogradovPowerSumSupport ℓ R V,
        vinogradovLinearizedSumNorm c R V ℓ u ^ (2 * ℓ)) ≤
      (vinogradovMeanValueCount ℓ R V : ℝ) *
        ∑ d ∈ vinogradovPowerDifferenceSupport ℓ R V,
          ‖∑ u ∈ vinogradovPowerSumSupport ℓ R V,
            standardAdditiveCharacter
              (vinogradovCoefficientBilinearForm c R d u)‖ := by
  calc
    (∑ u ∈ vinogradovPowerSumSupport ℓ R V,
        vinogradovLinearizedSumNorm c R V ℓ u ^ (2 * ℓ)) ≤
      ∑ p : (Fin ℓ → Fin V) × (Fin ℓ → Fin V),
        ‖∑ u ∈ vinogradovPowerSumSupport ℓ R V,
          standardAdditiveCharacter
            (vinogradovCoefficientBilinearForm c R
              (vinogradovTuplePowerDifference R p) u)‖ :=
        sum_linearizedMoment_le_sum_pair_phase c R V ℓ
    _ = ∑ d ∈ vinogradovPowerDifferenceSupport ℓ R V,
        (vinogradovDifferenceRepresentationCount ℓ R V d : ℝ) *
          ‖∑ u ∈ vinogradovPowerSumSupport ℓ R V,
            standardAdditiveCharacter
              (vinogradovCoefficientBilinearForm c R d u)‖ :=
        sum_pair_phase_eq_differenceRepresentationCount c R V ℓ
    _ ≤ ∑ d ∈ vinogradovPowerDifferenceSupport ℓ R V,
        (vinogradovMeanValueCount ℓ R V : ℝ) *
          ‖∑ u ∈ vinogradovPowerSumSupport ℓ R V,
            standardAdditiveCharacter
              (vinogradovCoefficientBilinearForm c R d u)‖ := by
        apply Finset.sum_le_sum
        intro d hd
        apply mul_le_mul_of_nonneg_right
        · exact_mod_cast
            vinogradovDifferenceRepresentationCount_le_meanValueCount ℓ R V d
        · exact norm_nonneg _
    _ = (vinogradovMeanValueCount ℓ R V : ℝ) *
        ∑ d ∈ vinogradovPowerDifferenceSupport ℓ R V,
          ‖∑ u ∈ vinogradovPowerSumSupport ℓ R V,
            standardAdditiveCharacter
              (vinogradovCoefficientBilinearForm c R d u)‖ := by
        rw [Finset.mul_sum]

/-- The exact second Hölder estimate for the representation-weighted
linearized sum. This is the finite combinatorial inequality underlying
equation (16) in the Vinogradov argument. -/
theorem representationCount_linearized_pow_le_meanValue
    (c : ℕ → ℝ) (R V ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    (∑ u ∈ vinogradovPowerSumSupport ℓ R V,
        (vinogradovRepresentationCount ℓ R V u : ℝ) *
          vinogradovLinearizedSumNorm c R V ℓ u) ^ (2 * ℓ) ≤
      ((V ^ ℓ : ℕ) : ℝ) ^ (2 * ℓ - 2) *
        (vinogradovMeanValueCount ℓ R V : ℝ) *
          ∑ u ∈ vinogradovPowerSumSupport ℓ R V,
            vinogradovLinearizedSumNorm c R V ℓ u ^ (2 * ℓ) := by
  have h := sum_mul_pow_le_interpolation_of_nonneg
    (vinogradovPowerSumSupport ℓ R V)
    (fun u => (vinogradovRepresentationCount ℓ R V u : ℝ))
    (vinogradovLinearizedSumNorm c R V ℓ) ℓ hℓ
    (fun _ => Nat.cast_nonneg _) (vinogradovLinearizedSumNorm_nonneg c R V ℓ)
  have hsum :
      (∑ u ∈ vinogradovPowerSumSupport ℓ R V,
        (vinogradovRepresentationCount ℓ R V u : ℝ)) =
          ((V ^ ℓ : ℕ) : ℝ) := by
    exact_mod_cast sum_vinogradovRepresentationCount ℓ R V
  have hsq :
      (∑ u ∈ vinogradovPowerSumSupport ℓ R V,
        (vinogradovRepresentationCount ℓ R V u : ℝ) ^ 2) =
          (vinogradovMeanValueCount ℓ R V : ℝ) := by
    exact_mod_cast sum_sq_vinogradovRepresentationCount ℓ R V
  rw [hsum, hsq] at h
  exact h

/-- Equation (16) after both Hölder steps: the first inner-sum moment is
controlled by the representation count, its quadratic mean value, and the
`2ℓ`-moment of the linearized outer sums. -/
theorem sum_norm_inner_pow_pow_le_meanValue
    (c : ℕ → ℝ) (R V ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    (∑ x ∈ Finset.Icc 1 V,
        ‖vinogradovBilinearPolynomialInnerSum c R V x‖ ^ ℓ) ^ (2 * ℓ) ≤
      ((V ^ ℓ : ℕ) : ℝ) ^ (2 * ℓ - 2) *
        (vinogradovMeanValueCount ℓ R V : ℝ) *
          ∑ u ∈ vinogradovPowerSumSupport ℓ R V,
            vinogradovLinearizedSumNorm c R V ℓ u ^ (2 * ℓ) := by
  have hfirst :=
    sum_norm_inner_pow_le_representationCount_mul_norm_linearized c R V ℓ
  have hfirst' :
      (∑ x ∈ Finset.Icc 1 V,
          ‖vinogradovBilinearPolynomialInnerSum c R V x‖ ^ ℓ : ℝ) ≤
        ∑ u ∈ vinogradovPowerSumSupport ℓ R V,
          (vinogradovRepresentationCount ℓ R V u : ℝ) *
            vinogradovLinearizedSumNorm c R V ℓ u := by
    simpa only [vinogradovLinearizedSumNorm] using hfirst
  calc
    (∑ x ∈ Finset.Icc 1 V,
        ‖vinogradovBilinearPolynomialInnerSum c R V x‖ ^ ℓ) ^ (2 * ℓ) ≤
      (∑ u ∈ vinogradovPowerSumSupport ℓ R V,
        (vinogradovRepresentationCount ℓ R V u : ℝ) *
          vinogradovLinearizedSumNorm c R V ℓ u) ^ (2 * ℓ) :=
        pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => by positivity) hfirst' _
    _ ≤ ((V ^ ℓ : ℕ) : ℝ) ^ (2 * ℓ - 2) *
        (vinogradovMeanValueCount ℓ R V : ℝ) *
          ∑ u ∈ vinogradovPowerSumSupport ℓ R V,
            vinogradovLinearizedSumNorm c R V ℓ u ^ (2 * ℓ) :=
      representationCount_linearized_pow_le_meanValue c R V ℓ hℓ

/-- Both Hölder steps combined with the original bilinear polynomial sum.
The remaining analytic input is now isolated in the mean-value count and the
linearized outer `2ℓ`-moment. -/
theorem norm_bilinearPolynomialSum_pow_le_meanValue
    (c : ℕ → ℝ) (R V ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    ‖vinogradovBilinearPolynomialSum c R V‖ ^ (ℓ * (2 * ℓ)) ≤
      (V : ℝ) ^ ((ℓ - 1) * (2 * ℓ)) *
        (((V ^ ℓ : ℕ) : ℝ) ^ (2 * ℓ - 2) *
          (vinogradovMeanValueCount ℓ R V : ℝ) *
            ∑ u ∈ vinogradovPowerSumSupport ℓ R V,
              vinogradovLinearizedSumNorm c R V ℓ u ^ (2 * ℓ)) := by
  have hfirst :=
    norm_vinogradovBilinearPolynomialSum_pow_le_firstMoment c R V ℓ hℓ
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤
      ‖vinogradovBilinearPolynomialSum c R V‖ ^ ℓ) hfirst (2 * ℓ)
  have hpow' :
      ‖vinogradovBilinearPolynomialSum c R V‖ ^ (ℓ * (2 * ℓ)) ≤
        (V : ℝ) ^ ((ℓ - 1) * (2 * ℓ)) *
          (∑ x ∈ Finset.Icc 1 V,
            ‖vinogradovBilinearPolynomialInnerSum c R V x‖ ^ ℓ) ^
              (2 * ℓ) := by
    simpa only [pow_mul, mul_pow] using hpow
  calc
    ‖vinogradovBilinearPolynomialSum c R V‖ ^ (ℓ * (2 * ℓ)) ≤
        (V : ℝ) ^ ((ℓ - 1) * (2 * ℓ)) *
          (∑ x ∈ Finset.Icc 1 V,
            ‖vinogradovBilinearPolynomialInnerSum c R V x‖ ^ ℓ) ^
              (2 * ℓ) := hpow'
    _ ≤ (V : ℝ) ^ ((ℓ - 1) * (2 * ℓ)) *
        (((V ^ ℓ : ℕ) : ℝ) ^ (2 * ℓ - 2) *
          (vinogradovMeanValueCount ℓ R V : ℝ) *
            ∑ u ∈ vinogradovPowerSumSupport ℓ R V,
              vinogradovLinearizedSumNorm c R V ℓ u ^ (2 * ℓ)) := by
      exact mul_le_mul_of_nonneg_left
        (sum_norm_inner_pow_pow_le_meanValue c R V ℓ hℓ) (by positivity)

/-- Both Hölder steps followed by the full equation-(18) box expansion and
coordinate factorization. In particular, the Vinogradov mean value occurs
twice, exactly as in Tao's source argument. -/
theorem norm_bilinearPolynomialSum_pow_le_meanValue_sq_mul_coordinateSums
    (c : ℕ → ℝ) (R V ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    ‖vinogradovBilinearPolynomialSum c R V‖ ^ (ℓ * (2 * ℓ)) ≤
      (V : ℝ) ^ ((ℓ - 1) * (2 * ℓ)) *
        (((V ^ ℓ : ℕ) : ℝ) ^ (2 * ℓ - 2) *
          (vinogradovMeanValueCount ℓ R V : ℝ) *
            ((vinogradovMeanValueCount ℓ R V : ℝ) *
              ∏ j : Fin R,
                ∑ x ∈ vinogradovPowerBoxSide ℓ V (j.1 + 1),
                  ‖∑ y ∈ vinogradovPowerBoxSide ℓ V (j.1 + 1),
                    standardAdditiveCharacter
                      (c (j.1 + 1) * (x : ℝ) * (y : ℝ))‖)) := by
  calc
    ‖vinogradovBilinearPolynomialSum c R V‖ ^ (ℓ * (2 * ℓ)) ≤
        (V : ℝ) ^ ((ℓ - 1) * (2 * ℓ)) *
          (((V ^ ℓ : ℕ) : ℝ) ^ (2 * ℓ - 2) *
            (vinogradovMeanValueCount ℓ R V : ℝ) *
              ∑ u ∈ vinogradovPowerSumSupport ℓ R V,
                vinogradovLinearizedSumNorm c R V ℓ u ^ (2 * ℓ)) :=
      norm_bilinearPolynomialSum_pow_le_meanValue c R V ℓ hℓ
    _ ≤ (V : ℝ) ^ ((ℓ - 1) * (2 * ℓ)) *
        (((V ^ ℓ : ℕ) : ℝ) ^ (2 * ℓ - 2) *
          (vinogradovMeanValueCount ℓ R V : ℝ) *
            ((vinogradovMeanValueCount ℓ R V : ℝ) *
              ∏ j : Fin R,
                ∑ x ∈ vinogradovPowerBoxSide ℓ V (j.1 + 1),
                  ‖∑ y ∈ vinogradovPowerBoxSide ℓ V (j.1 + 1),
                    standardAdditiveCharacter
                      (c (j.1 + 1) * (x : ℝ) * (y : ℝ))‖)) := by
      apply mul_le_mul_of_nonneg_left
      · apply mul_le_mul_of_nonneg_left
        · exact
            sum_linearizedMoment_le_meanValue_mul_prod_coordinateSums c R V ℓ
        · positivity
      · positivity

/-- The exact monotone composition point for the two remaining analytic
inputs: a bound for the Vinogradov mean value and a bound for the factored
coordinate product. This keeps the final exponent and root bookkeeping
separate from both deep estimates. -/
theorem powered_bilinear_bound_of_meanValue_and_coordinate_bounds
    (c : ℕ → ℝ) (R V ℓ : ℕ) (hℓ : 1 ≤ ℓ) {J P : ℝ}
    (hJ : (vinogradovMeanValueCount ℓ R V : ℝ) ≤ J)
    (hP : (∏ j : Fin R,
      ∑ x ∈ vinogradovPowerBoxSide ℓ V (j.1 + 1),
        ‖∑ y ∈ vinogradovPowerBoxSide ℓ V (j.1 + 1),
          standardAdditiveCharacter
            (c (j.1 + 1) * (x : ℝ) * (y : ℝ))‖) ≤ P)
    (hJ0 : 0 ≤ J) :
    ‖vinogradovBilinearPolynomialSum c R V‖ ^ (ℓ * (2 * ℓ)) ≤
      (V : ℝ) ^ ((ℓ - 1) * (2 * ℓ)) *
        (((V ^ ℓ : ℕ) : ℝ) ^ (2 * ℓ - 2) * J * (J * P)) := by
  calc
    ‖vinogradovBilinearPolynomialSum c R V‖ ^ (ℓ * (2 * ℓ)) ≤
        (V : ℝ) ^ ((ℓ - 1) * (2 * ℓ)) *
          (((V ^ ℓ : ℕ) : ℝ) ^ (2 * ℓ - 2) *
            (vinogradovMeanValueCount ℓ R V : ℝ) *
              ((vinogradovMeanValueCount ℓ R V : ℝ) *
                ∏ j : Fin R,
                  ∑ x ∈ vinogradovPowerBoxSide ℓ V (j.1 + 1),
                    ‖∑ y ∈ vinogradovPowerBoxSide ℓ V (j.1 + 1),
                      standardAdditiveCharacter
                        (c (j.1 + 1) * (x : ℝ) * (y : ℝ))‖)) :=
      norm_bilinearPolynomialSum_pow_le_meanValue_sq_mul_coordinateSums
        c R V ℓ hℓ
    _ ≤ (V : ℝ) ^ ((ℓ - 1) * (2 * ℓ)) *
        (((V ^ ℓ : ℕ) : ℝ) ^ (2 * ℓ - 2) * J * (J * P)) := by
      gcongr

/-- Critical-moment assembly of equation (18). Given a VMVT loss `ε` and a
coordinate saving `δ`, all scale powers cancel except `2*ε-δ`; the two VMVT
constants and the endpoint factor remain as `C^2*A`. -/
theorem powered_bilinear_critical_bound_of_meanValue_and_coordinate_bounds
    (c : ℕ → ℝ) (R V : ℕ) (hR : 1 ≤ R) (hV : 1 ≤ V)
    {C ε δ A : ℝ} (hC0 : 0 ≤ C)
    (hJ : (vinogradovMeanValueCount (GafniTao.fordVinogradovKappa R) R V : ℝ) ≤
      C * (V : ℝ) ^ ((GafniTao.fordVinogradovKappa R : ℕ) + ε))
    (hP : (∏ j : Fin R,
      ∑ x ∈ vinogradovPowerBoxSide (GafniTao.fordVinogradovKappa R) V (j.1 + 1),
        ‖∑ y ∈ vinogradovPowerBoxSide (GafniTao.fordVinogradovKappa R) V (j.1 + 1),
          standardAdditiveCharacter
            (c (j.1 + 1) * (x : ℝ) * (y : ℝ))‖) ≤
      (V : ℝ) ^ (-δ) *
        (A * (V : ℝ) ^ (R * (R + 1)))) :
    ‖vinogradovBilinearPolynomialSum c R V‖ ^
        (GafniTao.fordVinogradovKappa R *
          (2 * GafniTao.fordVinogradovKappa R)) ≤
      C ^ 2 * A *
        (V : ℝ) ^
          ((4 * (GafniTao.fordVinogradovKappa R) ^ 2 : ℕ) + 2 * ε - δ) := by
  have hell : 1 ≤ GafniTao.fordVinogradovKappa R := by
    have hk := two_mul_fordVinogradovKappa R
    have hproduct : 2 ≤ R * (R + 1) := by
      calc
        2 ≤ R * 2 := by omega
        _ ≤ R * (R + 1) := Nat.mul_le_mul_left R (by omega)
    rw [← hk] at hproduct
    omega
  calc
    ‖vinogradovBilinearPolynomialSum c R V‖ ^
        (GafniTao.fordVinogradovKappa R *
          (2 * GafniTao.fordVinogradovKappa R)) ≤
      (V : ℝ) ^ ((GafniTao.fordVinogradovKappa R - 1) *
          (2 * GafniTao.fordVinogradovKappa R)) *
        ((((V ^ GafniTao.fordVinogradovKappa R : ℕ) : ℝ) ^
            (2 * GafniTao.fordVinogradovKappa R - 2) *
          (C * (V : ℝ) ^ ((GafniTao.fordVinogradovKappa R : ℕ) + ε)) *
            ((C * (V : ℝ) ^ ((GafniTao.fordVinogradovKappa R : ℕ) + ε)) *
              ((V : ℝ) ^ (-δ) * (A * (V : ℝ) ^ (R * (R + 1))))))) := by
        exact powered_bilinear_bound_of_meanValue_and_coordinate_bounds
          c R V (GafniTao.fordVinogradovKappa R) hell hJ hP
            (mul_nonneg hC0 (Real.rpow_nonneg (by positivity) _))
    _ = C ^ 2 * A *
        (V : ℝ) ^
          ((4 * (GafniTao.fordVinogradovKappa R) ^ 2 : ℕ) + 2 * ε - δ) := by
      exact critical_vinogradov_power_rpow_identity R V hV C A ε δ
        (GafniTao.fordVinogradovKappa R)
        (critical_vinogradov_power_exponent_identity R hR)

/-- Extract an exact real `m`-th root from a powered scale estimate. The
dominant exponent `2*m` becomes `V^2`, while the saving `d` becomes `d/m`. -/
theorem le_root_mul_sq_mul_saving_of_pow_le
    {x D V d : ℝ} {m : ℕ} (hm : 1 ≤ m) (hx : 0 ≤ x)
    (hD : 0 ≤ D) (hV : 0 < V)
    (hpow : x ^ m ≤ D * V ^ (((2 * m : ℕ) : ℝ) - d)) :
    x ≤ D ^ (1 / (m : ℝ)) * V ^ (2 : ℕ) * V ^ (-d / (m : ℝ)) := by
  have hmreal : (0 : ℝ) < m := by exact_mod_cast (Nat.zero_lt_of_lt hm)
  have hroot := Real.rpow_le_rpow (pow_nonneg hx m) hpow
    (show 0 ≤ 1 / (m : ℝ) by positivity)
  have hleft : (x ^ m) ^ (1 / (m : ℝ)) = x := by
    rw [show 1 / (m : ℝ) = ((m : ℝ))⁻¹ by ring]
    exact Real.pow_rpow_inv_natCast hx (by omega)
  rw [hleft, Real.mul_rpow hD (Real.rpow_nonneg hV.le _)] at hroot
  calc
    x ≤ D ^ (1 / (m : ℝ)) *
        (V ^ (((2 * m : ℕ) : ℝ) - d)) ^ (1 / (m : ℝ)) := hroot
    _ = D ^ (1 / (m : ℝ)) * V ^ (2 : ℕ) * V ^ (-d / (m : ℝ)) := by
      rw [← Real.rpow_mul hV.le]
      rw [mul_assoc]
      congr 1
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_add hV]
      congr 1
      norm_num only [Nat.cast_mul, Nat.cast_ofNat]
      field_simp
      ring_nf

/-- Native critical VMVT composed with the sharp `1/8` source coordinate
estimate. Choosing `ε=δ/4` leaves half of the coordinate exponent after the
two critical moments, before the final `2*ell^2` root is extracted. -/
theorem source_powered_bilinear_critical_bound_eighth
    {X F α : ℝ} {n : ℕ} {c : ℕ → ℝ}
    (hX : 2 ≤ X) (hFhigh : X ^ 4 ≤ F) (hα : 1 ≤ α)
    (hn : (n : ℝ) ∈ Set.Icc X (2 * X))
    (hcoeff : ∀ r : ℕ, 1 ≤ r → r ≤ vinogradovTaylorDegree X F →
      F / α ^ (r ^ 3) ≤ (n : ℝ) ^ r * |c r| ∧
        (n : ℝ) ^ r * |c r| ≤ α ^ (r ^ 3) * F)
    (hsmall : 2 * α * Real.exp
      (-((2 : ℝ) ^ (-18 : ℝ)) * (Real.log X) ^ 3 /
        (Real.log F) ^ 2) < 1) :
    ∃ C : ℝ, 0 < C ∧
      ‖vinogradovBilinearPolynomialSum c (vinogradovTaylorDegree X F)
        (vinogradovAveragingRange X)‖ ^
          (GafniTao.fordVinogradovKappa (vinogradovTaylorDegree X F) *
            (2 * GafniTao.fordVinogradovKappa (vinogradovTaylorDegree X F))) ≤
        C ^ 2 *
          (((3 * GafniTao.fordVinogradovKappa
            (vinogradovTaylorDegree X F) : ℕ) : ℝ) ^
              (2 * vinogradovTaylorDegree X F)) *
          (vinogradovAveragingRange X : ℝ) ^
            ((4 * (GafniTao.fordVinogradovKappa
              (vinogradovTaylorDegree X F)) ^ 2 : ℕ) -
                (31 * (vinogradovTaylorDegree X F : ℝ) ^ 2) / 614400) := by
  let R := vinogradovTaylorDegree X F
  let V := vinogradovAveragingRange X
  let K := GafniTao.fordVinogradovKappa R
  let δ : ℝ := 31 * (R : ℝ) ^ 2 / 307200
  have hR : 1 ≤ R := by
    have hforty := forty_le_vinogradovTaylorDegree hX hFhigh
    dsimp only [R]
    omega
  have hV : 1 ≤ V := by
    dsimp only [V]
    exact vinogradovAveragingRange_pos (show 1 ≤ X by linarith)
  have hδ : 0 < δ := by
    dsimp only [δ]
    positivity
  obtain ⟨C, hC, hJ⟩ :=
    native_critical_vinogradovMeanValueCount_bound hR
      (show 0 < δ / 4 by positivity)
  refine ⟨C, hC, ?_⟩
  have hP := source_prod_coordinateSums_le_eighthSaving_mul_criticalPower
    (ell := K) hX hFhigh hα hn (by
      have hk := two_mul_fordVinogradovKappa R
      have : 2 ≤ R * (R + 1) := by nlinarith
      rw [← hk] at this
      omega) hcoeff hsmall
  dsimp only [R, V, K, δ] at hJ hP
  rw [show (-(31 * (vinogradovTaylorDegree X F : ℝ) ^ 2)) / 307200 =
      -(31 * (vinogradovTaylorDegree X F : ℝ) ^ 2 / 307200) by ring] at hP
  have hassembled :=
    powered_bilinear_critical_bound_of_meanValue_and_coordinate_bounds
      c (vinogradovTaylorDegree X F) (vinogradovAveragingRange X)
        (by simpa only [R] using hR) (by simpa only [V] using hV) hC.le
        (ε := (31 * (vinogradovTaylorDegree X F : ℝ) ^ 2 / 307200) / 4)
        (δ := 31 * (vinogradovTaylorDegree X F : ℝ) ^ 2 / 307200)
        (A := (((3 * GafniTao.fordVinogradovKappa
          (vinogradovTaylorDegree X F) : ℕ) : ℝ)) ^
            (2 * vinogradovTaylorDegree X F))
        (hJ (vinogradovAveragingRange X) (by simpa only [V] using hV)) hP
  convert hassembled using 1
  ring_nf

/-- Exact source-facing root extraction from the native critical moment. The
remaining coefficient is isolated from the scale saving, which is now an
explicit negative power divided by the critical root degree. -/
theorem source_bilinear_critical_root_bound_eighth
    {X F α : ℝ} {n : ℕ} {c : ℕ → ℝ}
    (hX : 2 ≤ X) (hFhigh : X ^ 4 ≤ F) (hα : 1 ≤ α)
    (hn : (n : ℝ) ∈ Set.Icc X (2 * X))
    (hcoeff : ∀ r : ℕ, 1 ≤ r → r ≤ vinogradovTaylorDegree X F →
      F / α ^ (r ^ 3) ≤ (n : ℝ) ^ r * |c r| ∧
        (n : ℝ) ^ r * |c r| ≤ α ^ (r ^ 3) * F)
    (hsmall : 2 * α * Real.exp
      (-((2 : ℝ) ^ (-18 : ℝ)) * (Real.log X) ^ 3 /
        (Real.log F) ^ 2) < 1) :
    ∃ C : ℝ, 0 < C ∧
      ‖vinogradovBilinearPolynomialSum c (vinogradovTaylorDegree X F)
        (vinogradovAveragingRange X)‖ ≤
        (C ^ 2 *
          (((3 * GafniTao.fordVinogradovKappa
            (vinogradovTaylorDegree X F) : ℕ) : ℝ) ^
              (2 * vinogradovTaylorDegree X F))) ^
            (1 / ((GafniTao.fordVinogradovKappa (vinogradovTaylorDegree X F) *
              (2 * GafniTao.fordVinogradovKappa
                (vinogradovTaylorDegree X F)) : ℕ) : ℝ)) *
          (vinogradovAveragingRange X : ℝ) ^ (2 : ℕ) *
          (vinogradovAveragingRange X : ℝ) ^
            (-(31 * (vinogradovTaylorDegree X F : ℝ) ^ 2 / 614400) /
              ((GafniTao.fordVinogradovKappa (vinogradovTaylorDegree X F) *
                (2 * GafniTao.fordVinogradovKappa
                  (vinogradovTaylorDegree X F)) : ℕ) : ℝ)) := by
  obtain ⟨C, hC, hpow⟩ := source_powered_bilinear_critical_bound_eighth
    hX hFhigh hα hn hcoeff hsmall
  refine ⟨C, hC, ?_⟩
  let R := vinogradovTaylorDegree X F
  let V := vinogradovAveragingRange X
  let K := GafniTao.fordVinogradovKappa R
  let m := K * (2 * K)
  let d : ℝ := 31 * (R : ℝ) ^ 2 / 614400
  let D : ℝ := C ^ 2 * (((3 * K : ℕ) : ℝ)) ^ (2 * R)
  have hK : 1 ≤ K := by
    have hR : 1 ≤ R := by
      have hforty := forty_le_vinogradovTaylorDegree hX hFhigh
      dsimp only [R]
      omega
    have hk := two_mul_fordVinogradovKappa R
    have : 2 ≤ R * (R + 1) := by nlinarith
    rw [← hk] at this
    omega
  have hm : 1 ≤ m := by
    dsimp only [m]
    exact Nat.one_le_iff_ne_zero.mpr
      (mul_ne_zero (by omega) (mul_ne_zero (by omega) (by omega)))
  have hV : 0 < (V : ℝ) := by
    exact_mod_cast vinogradovAveragingRange_pos (show 1 ≤ X by linarith)
  have hD : 0 ≤ D := by
    dsimp only [D]
    positivity
  have hpow' :
      ‖vinogradovBilinearPolynomialSum c R V‖ ^ m ≤
        D * (V : ℝ) ^ (((2 * m : ℕ) : ℝ) - d) := by
    dsimp only [R, V, K, m, d, D] at hpow ⊢
    convert hpow using 1
    congr 2
    norm_num only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    ring
  have hroot := le_root_mul_sq_mul_saving_of_pow_le hm
    (norm_nonneg _) hD hV hpow'
  dsimp only [R, V, K, m, d, D] at hroot ⊢
  exact hroot

/-- Native critical VMVT composed with the sharp quarter-window coordinate
estimate. Choosing `ε=δ/128` retains `63/64` of the coordinate saving. -/
theorem source_powered_bilinear_critical_bound_quarter
    {X F α : ℝ} {n : ℕ} {c : ℕ → ℝ}
    (hX : 2 ≤ X) (hFhigh : X ^ 4 ≤ F) (hα : 1 ≤ α)
    (hn : (n : ℝ) ∈ Set.Icc X (2 * X))
    (hcoeff : ∀ r : ℕ, 1 ≤ r → r ≤ vinogradovTaylorDegree X F →
      F / α ^ (r ^ 3) ≤ (n : ℝ) ^ r * |c r| ∧
        (n : ℝ) ^ r * |c r| ≤ α ^ (r ^ 3) * F)
    (hsmall : 2 * α * Real.exp
      (-((2 : ℝ) ^ (-18 : ℝ)) * (Real.log X) ^ 3 /
        (Real.log F) ^ 2) < 1) :
    ∃ C : ℝ, 0 < C ∧
      ‖vinogradovBilinearPolynomialSum c (vinogradovTaylorDegree X F)
        (vinogradovAveragingRange X)‖ ^
          (GafniTao.fordVinogradovKappa (vinogradovTaylorDegree X F) *
            (2 * GafniTao.fordVinogradovKappa (vinogradovTaylorDegree X F))) ≤
        C ^ 2 *
          (((3 * GafniTao.fordVinogradovKappa
            (vinogradovTaylorDegree X F) : ℕ) : ℝ) ^
              (2 * vinogradovTaylorDegree X F)) *
          (vinogradovAveragingRange X : ℝ) ^
            ((4 * (GafniTao.fordVinogradovKappa
              (vinogradovTaylorDegree X F)) ^ 2 : ℕ) -
                (16065 * (vinogradovTaylorDegree X F : ℝ) ^ 2) / 12648448) := by
  let R := vinogradovTaylorDegree X F
  let V := vinogradovAveragingRange X
  let K := GafniTao.fordVinogradovKappa R
  let δ : ℝ := 255 * (R : ℝ) ^ 2 / 197632
  have hR : 1 ≤ R := by
    have hforty := forty_le_vinogradovTaylorDegree hX hFhigh
    dsimp only [R]
    omega
  have hV : 1 ≤ V := by
    dsimp only [V]
    exact vinogradovAveragingRange_pos (show 1 ≤ X by linarith)
  have hδ : 0 < δ := by
    dsimp only [δ]
    positivity
  obtain ⟨C, hC, hJ⟩ :=
    native_critical_vinogradovMeanValueCount_bound hR
      (show 0 < δ / 128 by positivity)
  refine ⟨C, hC, ?_⟩
  have hP := source_prod_coordinateSums_le_quarterSaving_mul_criticalPower
    (ell := K) hX hFhigh hα hn (by
      have hk := two_mul_fordVinogradovKappa R
      have : 2 ≤ R * (R + 1) := by nlinarith
      rw [← hk] at this
      omega) hcoeff hsmall
  dsimp only [R, V, K, δ] at hJ hP
  rw [show (-(255 * (vinogradovTaylorDegree X F : ℝ) ^ 2)) / 197632 =
      -(255 * (vinogradovTaylorDegree X F : ℝ) ^ 2 / 197632) by ring] at hP
  have hassembled :=
    powered_bilinear_critical_bound_of_meanValue_and_coordinate_bounds
      c (vinogradovTaylorDegree X F) (vinogradovAveragingRange X)
        (by simpa only [R] using hR) (by simpa only [V] using hV) hC.le
        (ε := (255 * (vinogradovTaylorDegree X F : ℝ) ^ 2 / 197632) / 128)
        (δ := 255 * (vinogradovTaylorDegree X F : ℝ) ^ 2 / 197632)
        (A := (((3 * GafniTao.fordVinogradovKappa
          (vinogradovTaylorDegree X F) : ℕ) : ℝ)) ^
            (2 * vinogradovTaylorDegree X F))
        (hJ (vinogradovAveragingRange X) (by simpa only [V] using hV)) hP
  convert hassembled using 1
  ring_nf

/-- Root extraction for the sharp quarter-window critical estimate. -/
theorem source_bilinear_critical_root_bound_quarter
    {X F α : ℝ} {n : ℕ} {c : ℕ → ℝ}
    (hX : 2 ≤ X) (hFhigh : X ^ 4 ≤ F) (hα : 1 ≤ α)
    (hn : (n : ℝ) ∈ Set.Icc X (2 * X))
    (hcoeff : ∀ r : ℕ, 1 ≤ r → r ≤ vinogradovTaylorDegree X F →
      F / α ^ (r ^ 3) ≤ (n : ℝ) ^ r * |c r| ∧
        (n : ℝ) ^ r * |c r| ≤ α ^ (r ^ 3) * F)
    (hsmall : 2 * α * Real.exp
      (-((2 : ℝ) ^ (-18 : ℝ)) * (Real.log X) ^ 3 /
        (Real.log F) ^ 2) < 1) :
    ∃ C : ℝ, 0 < C ∧
      ‖vinogradovBilinearPolynomialSum c (vinogradovTaylorDegree X F)
        (vinogradovAveragingRange X)‖ ≤
        (C ^ 2 *
          (((3 * GafniTao.fordVinogradovKappa
            (vinogradovTaylorDegree X F) : ℕ) : ℝ) ^
              (2 * vinogradovTaylorDegree X F))) ^
            (1 / ((GafniTao.fordVinogradovKappa (vinogradovTaylorDegree X F) *
              (2 * GafniTao.fordVinogradovKappa
                (vinogradovTaylorDegree X F)) : ℕ) : ℝ)) *
          (vinogradovAveragingRange X : ℝ) ^ (2 : ℕ) *
          (vinogradovAveragingRange X : ℝ) ^
            (-(16065 * (vinogradovTaylorDegree X F : ℝ) ^ 2 / 12648448) /
              ((GafniTao.fordVinogradovKappa (vinogradovTaylorDegree X F) *
                (2 * GafniTao.fordVinogradovKappa
                  (vinogradovTaylorDegree X F)) : ℕ) : ℝ)) := by
  obtain ⟨C, hC, hpow⟩ := source_powered_bilinear_critical_bound_quarter
    hX hFhigh hα hn hcoeff hsmall
  refine ⟨C, hC, ?_⟩
  let R := vinogradovTaylorDegree X F
  let V := vinogradovAveragingRange X
  let K := GafniTao.fordVinogradovKappa R
  let m := K * (2 * K)
  let d : ℝ := 16065 * (R : ℝ) ^ 2 / 12648448
  let D : ℝ := C ^ 2 * (((3 * K : ℕ) : ℝ)) ^ (2 * R)
  have hK : 1 ≤ K := by
    have hR : 1 ≤ R := by
      have hforty := forty_le_vinogradovTaylorDegree hX hFhigh
      dsimp only [R]
      omega
    have hk := two_mul_fordVinogradovKappa R
    have : 2 ≤ R * (R + 1) := by nlinarith
    rw [← hk] at this
    omega
  have hm : 1 ≤ m := by
    dsimp only [m]
    exact Nat.one_le_iff_ne_zero.mpr
      (mul_ne_zero (by omega) (mul_ne_zero (by omega) (by omega)))
  have hV : 0 < (V : ℝ) := by
    exact_mod_cast vinogradovAveragingRange_pos (show 1 ≤ X by linarith)
  have hD : 0 ≤ D := by
    dsimp only [D]
    positivity
  have hpow' :
      ‖vinogradovBilinearPolynomialSum c R V‖ ^ m ≤
        D * (V : ℝ) ^ (((2 * m : ℕ) : ℝ) - d) := by
    dsimp only [R, V, K, m, d, D] at hpow ⊢
    convert hpow using 1
    congr 2
    norm_num only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    ring
  have hroot := le_root_mul_sq_mul_saving_of_pow_le hm
    (norm_nonneg _) hD hV hpow'
  dsimp only [R, V, K, m, d, D] at hroot ⊢
  exact hroot

/-- The rooted quarter-window saving dominates the exact source target
`4·2⁻¹⁸/s²`.  The proof includes the ceiling loss in
`R = 10⌈s⌉` and the exact critical moment `K=R(R+1)/2`. -/
theorem critical_quarter_root_saving_ge
    {s : ℝ} {R : ℕ} (hs : 4 ≤ s) (hR : R = 10 * ⌈s⌉₊) :
    4 * (2 : ℝ) ^ (-18 : ℝ) / s ^ 2 ≤
      (16065 * (R : ℝ) ^ 2 / 12648448) /
        ((GafniTao.fordVinogradovKappa R *
          (2 * GafniTao.fordVinogradovKappa R) : ℕ) : ℝ) := by
  let K := GafniTao.fordVinogradovKappa R
  have hspos : 0 < s := by linarith
  have hceil : (⌈s⌉₊ : ℝ) < s + 1 := Nat.ceil_lt_add_one (by linarith)
  have hRcast : (R : ℝ) = 10 * (⌈s⌉₊ : ℝ) := by
    norm_num [hR]
  have hRplus : (R : ℝ) + 1 ≤ (51 / 4 : ℝ) * s := by
    rw [hRcast]
    nlinarith
  have hRpos : 0 < (R : ℝ) := by
    rw [hRcast]
    have : (4 : ℝ) ≤ (⌈s⌉₊ : ℝ) := hs.trans (Nat.le_ceil s)
    positivity
  have hk : (2 : ℝ) * (K : ℝ) = (R : ℝ) * ((R : ℝ) + 1) := by
    dsimp only [K]
    exact_mod_cast two_mul_fordVinogradovKappa R
  have hKpos : 0 < (K : ℝ) := by nlinarith
  have hm : ((K * (2 * K) : ℕ) : ℝ) =
      (R : ℝ) ^ 2 * ((R : ℝ) + 1) ^ 2 / 2 := by
    push_cast
    nlinarith [sq_nonneg ((R : ℝ) * ((R : ℝ) + 1))]
  change 4 * (2 : ℝ) ^ (-18 : ℝ) / s ^ 2 ≤
      (16065 * (R : ℝ) ^ 2 / 12648448) / ((K * (2 * K) : ℕ) : ℝ)
  rw [hm]
  norm_num
  field_simp
  nlinarith [sq_nonneg ((51 / 4 : ℝ) * s - ((R : ℝ) + 1))]

/-- After accounting for the floor in `V=⌊X^(1/4)⌋`, the sharp rooted
quarter-window power is at most two copies of the exact source decay. -/
theorem quarter_root_scale_saving_le_sourceDecay
    {X F : ℝ} (hX : 16 ≤ X) (hFhigh : X ^ 4 ≤ F) :
    (vinogradovAveragingRange X : ℝ) ^
        (-(16065 * (vinogradovTaylorDegree X F : ℝ) ^ 2 / 12648448) /
          ((GafniTao.fordVinogradovKappa (vinogradovTaylorDegree X F) *
            (2 * GafniTao.fordVinogradovKappa
              (vinogradovTaylorDegree X F)) : ℕ) : ℝ)) ≤
      2 * Real.exp
        (-((2 : ℝ) ^ (-18 : ℝ)) * (Real.log X) ^ 3 /
          (Real.log F) ^ 2) := by
  let s : ℝ := Real.log F / Real.log X
  let R : ℕ := vinogradovTaylorDegree X F
  let K : ℕ := GafniTao.fordVinogradovKappa R
  let e : ℝ := (16065 * (R : ℝ) ^ 2 / 12648448) / ((K * (2 * K) : ℕ) : ℝ)
  let e₀ : ℝ := 4 * (2 : ℝ) ^ (-18 : ℝ) / s ^ 2
  let D : ℝ := (2 : ℝ) ^ (-18 : ℝ) * (Real.log X) ^ 3 / (Real.log F) ^ 2
  have hXpos : 0 < X := by linarith
  have hlogX : 0 < Real.log X := Real.log_pos (by linarith)
  have hFpos : 0 < F := (pow_pos hXpos 4).trans_le hFhigh
  have hlogF : 0 < Real.log F := Real.log_pos
    ((show 1 < X ^ 4 by nlinarith [sq_nonneg (X ^ 2 - 4)]).trans_le hFhigh)
  have hs : 4 ≤ s := by
    dsimp only [s]
    rw [le_div_iff₀ hlogX]
    calc
      4 * Real.log X = Real.log (X ^ 4) := by rw [Real.log_pow]; norm_num
      _ ≤ Real.log F := Real.strictMonoOn_log.monotoneOn
        (Set.mem_Ioi.mpr (pow_pos hXpos 4)) (Set.mem_Ioi.mpr hFpos) hFhigh
  have he₀ : e₀ ≤ e := by
    dsimp only [e₀, e, K, R]
    apply critical_quarter_root_saving_ge hs
    rfl
  have he₀nonneg : 0 ≤ e₀ := by
    dsimp only [e₀]
    positivity
  have he₀one : e₀ ≤ 1 := by
    dsimp only [e₀]
    norm_num
    have hspos : 0 < s := by linarith
    have hsquare : 16 ≤ s ^ 2 := by nlinarith
    rw [div_le_iff₀ (sq_pos_of_pos hspos)]
    nlinarith
  obtain ⟨hlogVLow, hlogVUpp⟩ := log_vinogradovAveragingRange_bounds hX
  have hVpos : 0 < (vinogradovAveragingRange X : ℝ) := by
    exact_mod_cast vinogradovAveragingRange_pos (show 1 ≤ X by linarith)
  have hlogV : 0 ≤ Real.log (vinogradovAveragingRange X) :=
    Real.log_nonneg (by exact_mod_cast
      vinogradovAveragingRange_pos (show 1 ≤ X by linarith))
  have hlogTwo : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hD : D = (2 : ℝ) ^ (-18 : ℝ) * Real.log X / s ^ 2 := by
    dsimp only [D, s]
    field_simp
  have hexponent :
      -e * Real.log (vinogradovAveragingRange X) ≤ Real.log 2 - D := by
    have hfirst : -e * Real.log (vinogradovAveragingRange X) ≤
        -e₀ * Real.log (vinogradovAveragingRange X) := by
      nlinarith
    have hsecond : -e₀ * Real.log (vinogradovAveragingRange X) ≤
        -e₀ * (Real.log X / 4 - Real.log 2) :=
      mul_le_mul_of_nonpos_left hlogVLow.le (by linarith)
    have hlogPart : e₀ * Real.log 2 ≤ Real.log 2 :=
      mul_le_of_le_one_left hlogTwo he₀one
    rw [hD]
    calc
      -e * Real.log (vinogradovAveragingRange X) ≤
          -e₀ * Real.log (vinogradovAveragingRange X) := hfirst
      _ ≤ -e₀ * (Real.log X / 4 - Real.log 2) := hsecond
      _ = -(2 : ℝ) ^ (-18 : ℝ) * Real.log X / s ^ 2 +
          e₀ * Real.log 2 := by
        dsimp only [e₀]
        norm_num
        ring
      _ ≤ -(2 : ℝ) ^ (-18 : ℝ) * Real.log X / s ^ 2 +
          Real.log 2 := by
        simpa only [add_comm] using
          add_le_add_left hlogPart (-(2 : ℝ) ^ (-18 : ℝ) * Real.log X / s ^ 2)
      _ = Real.log 2 - (2 : ℝ) ^ (-18 : ℝ) * Real.log X / s ^ 2 := by ring
  have hneg : (-(16065 * (vinogradovTaylorDegree X F : ℝ) ^ 2 / 12648448) /
      ((GafniTao.fordVinogradovKappa (vinogradovTaylorDegree X F) *
        (2 * GafniTao.fordVinogradovKappa
          (vinogradovTaylorDegree X F)) : ℕ) : ℝ)) = -e := by
    dsimp only [e, K, R]
    ring
  rw [hneg]
  rw [Real.rpow_def_of_pos hVpos]
  have hdecayNeg :
      -((2 : ℝ) ^ (-18 : ℝ)) * (Real.log X) ^ 3 / (Real.log F) ^ 2 = -D := by
    dsimp only [D]
    ring
  rw [hdecayNeg]
  change Real.exp (Real.log (vinogradovAveragingRange X) * -e) ≤
    2 * Real.exp (-D)
  calc
    Real.exp (Real.log (vinogradovAveragingRange X) * -e) ≤
        Real.exp (Real.log 2 - D) := Real.exp_le_exp.mpr (by
          simpa only [mul_comm] using hexponent)
    _ = 2 * Real.exp (-D) := by
      rw [sub_eq_add_neg, Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]

end Tao2026
