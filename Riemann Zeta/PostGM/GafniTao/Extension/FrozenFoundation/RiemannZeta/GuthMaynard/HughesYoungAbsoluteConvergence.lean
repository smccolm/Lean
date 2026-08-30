import Mathlib.Data.PNat.Basic
import RiemannZeta.GuthMaynard.HughesYoungArithmetic

open Complex Finset
open scoped BigOperators

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# Absolute convergence in Hughes--Young Lemma 6.1

The change of order between equations (105) and (106) is justified by an
explicit positive triple series.  Its three coordinates are the common
divisor `d` and the quotients `l / d`, `r / d`; using positive naturals
removes all artificial zero terms.
-/

/-- A positive-natural p-series. -/
theorem summable_pnat_rpow_neg {u : ℝ} (hu : 1 < u) :
    Summable (fun n : ℕ+ => ((n : ℕ) : ℝ) ^ (-u)) := by
  have hnat : Summable (fun n : ℕ => (n : ℝ) ^ (-u)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hshift : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (-u)) :=
    (summable_nat_add_iff 1).mpr hnat
  have hreindex : Summable
      ((fun n : ℕ+ => ((n : ℕ) : ℝ) ^ (-u)) ∘
        Equiv.pnatEquivNat.symm) := by
    simpa [Function.comp_def, Equiv.pnatEquivNat] using hshift
  exact ((Equiv.pnatEquivNat.symm).summable_iff).mp hreindex

/-- The common-divisor parameterization of a pair `(l,r)`: the source
coordinates are `(d,m,n)` and the target is `(dm,dn)`. -/
def hughesYoungPositiveTripleMap :
    ((ℕ+ × ℕ+) × ℕ+) → (ℕ+ × ℕ+) :=
  fun x =>
    (⟨(x.1.1 : ℕ) * (x.1.2 : ℕ),
        Nat.mul_pos x.1.1.2 x.1.2.2⟩,
      ⟨(x.1.1 : ℕ) * (x.2 : ℕ),
        Nat.mul_pos x.1.1.2 x.2.2⟩)

/-- The factorized positive majorant attached to `(d,m,n)`. -/
noncomputable def hughesYoungPositiveTripleWeight
    (A C : ℝ) (x : (ℕ+ × ℕ+) × ℕ+) : ℝ :=
  (((x.1.1 : ℕ) : ℝ) ^ (-(A + C))) *
    (((x.1.2 : ℕ) : ℝ) ^ (-A)) *
    (((x.2 : ℕ) : ℝ) ^ (-(1 + C)))

theorem hughesYoungPositiveTripleWeight_nonneg
    (A C : ℝ) (x : (ℕ+ × ℕ+) × ℕ+) :
    0 ≤ hughesYoungPositiveTripleWeight A C x := by
  unfold hughesYoungPositiveTripleWeight
  positivity

/-- Absolute summability of the factorized triple majorant under the exact
half-plane assumptions of Hughes--Young Lemma 6.1. -/
theorem summable_hughesYoungPositiveTripleWeight
    {A C : ℝ} (hA : 1 < A) (hC : 0 < C) :
    Summable (hughesYoungPositiveTripleWeight A C) := by
  have hAC : 1 < A + C := lt_trans hA (lt_add_of_pos_right A hC)
  have hOneC : 1 < 1 + C := by linarith
  have hd := summable_pnat_rpow_neg hAC
  have hm := summable_pnat_rpow_neg hA
  have hn := summable_pnat_rpow_neg hOneC
  have hdm : Summable (fun x : ℕ+ × ℕ+ =>
      (((x.1 : ℕ) : ℝ) ^ (-(A + C))) *
        (((x.2 : ℕ) : ℝ) ^ (-A))) :=
    hd.mul_of_nonneg hm (fun _ => by positivity) (fun _ => by positivity)
  exact hdm.mul_of_nonneg hn
    (fun _ => by positivity) (fun _ => by positivity)

/-- The triple series grouped over all factorizations of a fixed positive
pair. -/
noncomputable def hughesYoungPositivePairMajorant
    (A C : ℝ) (y : ℕ+ × ℕ+) : ℝ :=
  ∑' x : {x : (ℕ+ × ℕ+) × ℕ+ //
      hughesYoungPositiveTripleMap x = y},
    hughesYoungPositiveTripleWeight A C x.1

theorem summable_hughesYoungPositivePairMajorant
    {A C : ℝ} (hA : 1 < A) (hC : 0 < C) :
    Summable (hughesYoungPositivePairMajorant A C) := by
  have htriple := summable_hughesYoungPositiveTripleWeight hA hC
  let e := Equiv.sigmaFiberEquiv hughesYoungPositiveTripleMap
  have hsigma : Summable (fun z :
      (y : ℕ+ × ℕ+) × {x : (ℕ+ × ℕ+) × ℕ+ //
        hughesYoungPositiveTripleMap x = y} =>
      hughesYoungPositiveTripleWeight A C z.2.1) := by
    have hreindex := (e.summable_iff).mpr htriple
    simpa [e, Function.comp_def] using hreindex
  exact hsigma.sigma

/-- The triple `(d,l/d,r/d)` attached to a positive common divisor. -/
def hughesYoungCommonDivisorTriple (y : ℕ+ × ℕ+)
    (d : ↥(Nat.gcd (y.1 : ℕ) (y.2 : ℕ)).divisors) :
    {x : (ℕ+ × ℕ+) × ℕ+ //
      hughesYoungPositiveTripleMap x = y} := by
  have hgcd0 : Nat.gcd (y.1 : ℕ) (y.2 : ℕ) ≠ 0 := by
    exact (Nat.gcd_pos_of_pos_left _ y.1.2).ne'
  have hdpos : 0 < (d : ℕ) := Nat.pos_of_mem_divisors d.2
  have hdgcd : (d : ℕ) ∣ Nat.gcd (y.1 : ℕ) (y.2 : ℕ) :=
    Nat.dvd_of_mem_divisors d.2
  have hdl : (d : ℕ) ∣ (y.1 : ℕ) :=
    dvd_trans hdgcd (Nat.gcd_dvd_left _ _)
  have hdr : (d : ℕ) ∣ (y.2 : ℕ) :=
    dvd_trans hdgcd (Nat.gcd_dvd_right _ _)
  have hml : 0 < (y.1 : ℕ) / (d : ℕ) :=
    Nat.div_pos (Nat.le_of_dvd y.1.2 hdl) hdpos
  have hnr : 0 < (y.2 : ℕ) / (d : ℕ) :=
    Nat.div_pos (Nat.le_of_dvd y.2.2 hdr) hdpos
  let dp : ℕ+ := ⟨d, hdpos⟩
  let m : ℕ+ := ⟨(y.1 : ℕ) / (d : ℕ), hml⟩
  let n : ℕ+ := ⟨(y.2 : ℕ) / (d : ℕ), hnr⟩
  refine ⟨((dp, m), n), ?_⟩
  apply Prod.ext <;> apply Subtype.ext
  · exact Nat.mul_div_cancel' hdl
  · exact Nat.mul_div_cancel' hdr

theorem hughesYoungCommonDivisorTriple_injective (y : ℕ+ × ℕ+) :
    Function.Injective (hughesYoungCommonDivisorTriple y) := by
  intro d e hde
  apply Subtype.ext
  have hfirst := congrArg (fun x => (((x.1.1.1 : ℕ+)) : ℕ)) hde
  exact hfirst

/-- The factorized triple weight is exactly the common-divisor summand after
the substitutions `l = dm`, `r = dn`. -/
theorem hughesYoungPositiveTripleWeight_commonDivisor
    (A C : ℝ) (y : ℕ+ × ℕ+)
    (d : ↥(Nat.gcd (y.1 : ℕ) (y.2 : ℕ)).divisors) :
    hughesYoungPositiveTripleWeight A C
        (hughesYoungCommonDivisorTriple y d).1 =
      ((d : ℕ) : ℝ) /
        (((y.1 : ℕ) : ℝ) ^ A) /
        (((y.2 : ℕ) : ℝ) ^ (1 + C)) := by
  have hdpos : 0 < (d : ℕ) := Nat.pos_of_mem_divisors d.2
  have hdgcd : (d : ℕ) ∣ Nat.gcd (y.1 : ℕ) (y.2 : ℕ) :=
    Nat.dvd_of_mem_divisors d.2
  have hdl : (d : ℕ) ∣ (y.1 : ℕ) :=
    dvd_trans hdgcd (Nat.gcd_dvd_left _ _)
  have hdr : (d : ℕ) ∣ (y.2 : ℕ) :=
    dvd_trans hdgcd (Nat.gcd_dvd_right _ _)
  have hdR : 0 < (((d : ℕ) : ℝ)) := by exact_mod_cast hdpos
  have hmR : 0 < ((((y.1 : ℕ) / (d : ℕ) : ℕ) : ℝ)) := by
    exact_mod_cast Nat.div_pos (Nat.le_of_dvd y.1.2 hdl) hdpos
  have hnR : 0 < ((((y.2 : ℕ) / (d : ℕ) : ℕ) : ℝ)) := by
    exact_mod_cast Nat.div_pos (Nat.le_of_dvd y.2.2 hdr) hdpos
  have hlEq : (((y.1 : ℕ) : ℝ)) =
      ((d : ℕ) : ℝ) * (((y.1 : ℕ) / (d : ℕ) : ℕ) : ℝ) := by
    exact_mod_cast (Nat.mul_div_cancel' hdl).symm
  have hrEq : (((y.2 : ℕ) : ℝ)) =
      ((d : ℕ) : ℝ) * (((y.2 : ℕ) / (d : ℕ) : ℕ) : ℝ) := by
    exact_mod_cast (Nat.mul_div_cancel' hdr).symm
  unfold hughesYoungPositiveTripleWeight
  simp only [hughesYoungCommonDivisorTriple]
  change
    (((d : ℕ) : ℝ) ^ (-(A + C))) *
        ((((y.1 : ℕ) / (d : ℕ) : ℕ) : ℝ) ^ (-A)) *
        ((((y.2 : ℕ) / (d : ℕ) : ℕ) : ℝ) ^ (-(1 + C))) =
      ((d : ℕ) : ℝ) / (((y.1 : ℕ) : ℝ) ^ A) /
        (((y.2 : ℕ) : ℝ) ^ (1 + C))
  rw [hlEq, hrEq, Real.mul_rpow hdR.le hmR.le,
    Real.mul_rpow hdR.le hnR.le]
  rw [div_eq_mul_inv, Real.rpow_neg hdR.le,
    Real.rpow_neg hmR.le, Real.rpow_neg hnR.le]
  have hdAC0 : (((d : ℕ) : ℝ) ^ (A + C)) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hdR _)
  have hdA0 : (((d : ℕ) : ℝ) ^ A) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hdR _)
  have hdOneC0 : (((d : ℕ) : ℝ) ^ (1 + C)) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hdR _)
  have hmA0 : ((((y.1 : ℕ) / (d : ℕ) : ℕ) : ℝ) ^ A) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hmR _)
  have hnOneC0 : ((((y.2 : ℕ) / (d : ℕ) : ℕ) : ℝ) ^ (1 + C)) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hnR _)
  field_simp [hdAC0, hdA0, hdOneC0, hmA0, hnOneC0]
  rw [← Real.rpow_add hdR A (1 + C)]
  rw [show A + (1 + C) = 1 + (A + C) by ring,
    Real.rpow_add hdR 1 (A + C), Real.rpow_one]
  ring

/-- The common-divisor majorant for a positive pair `(l,r)`. -/
noncomputable def hughesYoungCommonDivisorMajorant
    (A C : ℝ) (y : ℕ+ × ℕ+) : ℝ :=
  ∑ d ∈ (Nat.gcd (y.1 : ℕ) (y.2 : ℕ)).divisors,
    (d : ℝ) / (((y.1 : ℕ) : ℝ) ^ A) /
      (((y.2 : ℕ) : ℝ) ^ (1 + C))

/-- Every common-divisor summand occurs in the corresponding fiber of the
positive triple map. -/
theorem hughesYoungCommonDivisorMajorant_le_pairMajorant
    {A C : ℝ} (hA : 1 < A) (hC : 0 < C) (y : ℕ+ × ℕ+) :
    hughesYoungCommonDivisorMajorant A C y ≤
      hughesYoungPositivePairMajorant A C y := by
  let g : {x : (ℕ+ × ℕ+) × ℕ+ //
      hughesYoungPositiveTripleMap x = y} → ℝ :=
    fun x => hughesYoungPositiveTripleWeight A C x.1
  let f : ↥(Nat.gcd (y.1 : ℕ) (y.2 : ℕ)).divisors → ℝ :=
    fun d => ((d : ℕ) : ℝ) / (((y.1 : ℕ) : ℝ) ^ A) /
      (((y.2 : ℕ) : ℝ) ^ (1 + C))
  have hg0 : Summable
      (hughesYoungPositiveTripleWeight A C ∘
        (Subtype.val : {x : (ℕ+ × ℕ+) × ℕ+ //
          hughesYoungPositiveTripleMap x = y} → (ℕ+ × ℕ+) × ℕ+)) :=
    (summable_hughesYoungPositiveTripleWeight hA hC).comp_injective
      Subtype.coe_injective
  have hg : Summable g := by
    simpa only [g, Function.comp_apply] using hg0
  have hf : Summable f :=
    summable_of_hasFiniteSupport (Set.toFinite (Function.support f))
  have hle : (∑' d, f d) ≤ ∑' x, g x :=
    Summable.tsum_le_tsum_of_inj (hughesYoungCommonDivisorTriple y)
      (hughesYoungCommonDivisorTriple_injective y)
      (fun x _hx => hughesYoungPositiveTripleWeight_nonneg A C x.1)
      (fun d => (hughesYoungPositiveTripleWeight_commonDivisor A C y d).ge)
      hf hg
  simpa only [hughesYoungCommonDivisorMajorant,
    hughesYoungPositivePairMajorant, f, g, tsum_fintype,
    Finset.sum_subtype (Nat.gcd (y.1 : ℕ) (y.2 : ℕ)).divisors
      (fun _ => Iff.rfl)] using hle

/-- A finite bound for the fixed gcd-power factor occurring in equation
(96). -/
noncomputable def hughesYoungGCDCPowBound (h : ℕ) (a : ℂ) : ℝ :=
  ∑ d ∈ h.divisors, ‖((d : ℕ) : ℂ) ^ a‖

theorem norm_gcd_cpow_le_hughesYoungGCDCPowBound
    {h n : ℕ} (hh : 0 < h) (a : ℂ) :
    ‖(((Nat.gcd h n : ℕ) : ℂ) ^ a)‖ ≤
      hughesYoungGCDCPowBound h a := by
  have hgpos : 0 < Nat.gcd h n := Nat.gcd_pos_of_pos_left _ hh
  have hgmem : Nat.gcd h n ∈ h.divisors :=
    Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left h n, hh.ne'⟩
  unfold hughesYoungGCDCPowBound
  exact Finset.single_le_sum
    (fun (d : ℕ) _hd => norm_nonneg (((d : ℕ) : ℂ) ^ a)) hgmem

/-- The equation-(104) absolute majorant, retaining every common divisor
instead of replacing it by a coarser divisor-count estimate. -/
theorem norm_ramanujanSum_le_sum_gcd_divisors
    (l r : ℕ) [NeZero l] :
    ‖ramanujanSum l r‖ ≤
      ∑ d ∈ (Nat.gcd l r).divisors, (d : ℝ) := by
  rw [hughesYoungEquation104 l r]
  calc
    ‖∑ d ∈ (Nat.gcd r l).divisors,
        (d : ℂ) * ArithmeticFunction.moebius (l / d)‖ ≤
        ∑ d ∈ (Nat.gcd r l).divisors,
          ‖(d : ℂ) * ArithmeticFunction.moebius (l / d)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ d ∈ (Nat.gcd r l).divisors, (d : ℝ) := by
      apply Finset.sum_le_sum
      intro d _hd
      rw [norm_mul, Complex.norm_natCast, Complex.norm_intCast]
      have hμ : (|ArithmeticFunction.moebius (l / d)| : ℝ) ≤ 1 := by
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one
      nlinarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
    _ = ∑ d ∈ (Nat.gcd l r).divisors, (d : ℝ) := by
      rw [Nat.gcd_comm]

/-- Equation (96), on positive indices and in `(l,r)` order. -/
noncomputable def hughesYoungEquation96PositiveTerm
    (h k : ℕ) (a b c : ℂ) (y : ℕ+ × ℕ+) : ℂ :=
  ramanujanSum (y.1 : ℕ) (y.2 : ℕ) *
      ((Nat.gcd h (y.1 : ℕ) : ℕ) : ℂ) ^ a *
      ((Nat.gcd k (y.1 : ℕ) : ℕ) : ℂ) ^ b /
      ((((y.1 : ℕ) : ℂ) ^ (a + b)) *
        (((y.2 : ℕ) : ℂ) ^ c))

/-- Pointwise domination of equation (96) by the positive common-divisor
majorant. -/
theorem norm_hughesYoungEquation96PositiveTerm_le
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    (a b c : ℂ) (y : ℕ+ × ℕ+) :
    ‖hughesYoungEquation96PositiveTerm h k a b (1 + c) y‖ ≤
      (hughesYoungGCDCPowBound h a *
        hughesYoungGCDCPowBound k b) *
      hughesYoungCommonDivisorMajorant (a + b).re c.re y := by
  letI : NeZero (y.1 : ℕ) := ⟨y.1.2.ne'⟩
  have hram := norm_ramanujanSum_le_sum_gcd_divisors
    (y.1 : ℕ) (y.2 : ℕ)
  have hhg := norm_gcd_cpow_le_hughesYoungGCDCPowBound
    (n := (y.1 : ℕ)) hh a
  have hkg := norm_gcd_cpow_le_hughesYoungGCDCPowBound
    (n := (y.1 : ℕ)) hk b
  have hlpos : 0 < (((y.1 : ℕ) : ℝ)) := by exact_mod_cast y.1.2
  have hrpos : 0 < (((y.2 : ℕ) : ℝ)) := by exact_mod_cast y.2.2
  have hgcdh : 0 < Nat.gcd h (y.1 : ℕ) :=
    Nat.gcd_pos_of_pos_left _ hh
  have hgcdk : 0 < Nat.gcd k (y.1 : ℕ) :=
    Nat.gcd_pos_of_pos_left _ hk
  have hhgR : ((Nat.gcd h (y.1 : ℕ) : ℝ) ^ a.re) ≤
      hughesYoungGCDCPowBound h a := by
    simpa only [Complex.norm_natCast_cpow_of_pos hgcdh a] using hhg
  have hkgR : ((Nat.gcd k (y.1 : ℕ) : ℝ) ^ b.re) ≤
      hughesYoungGCDCPowBound k b := by
    simpa only [Complex.norm_natCast_cpow_of_pos hgcdk b] using hkg
  have hden1 : 0 < (((y.1 : ℕ) : ℝ) ^ (a + b).re) :=
    Real.rpow_pos_of_pos hlpos _
  have hden2 : 0 < (((y.2 : ℕ) : ℝ) ^ (1 + c.re)) :=
    Real.rpow_pos_of_pos hrpos _
  have hlnorm : ‖(((y.1 : ℕ) : ℂ) ^ (a + b))‖ =
      (((y.1 : ℕ) : ℝ) ^ (a + b).re) := by
    simpa only using
      (Complex.norm_natCast_cpow_of_pos
        (n := (y.1 : ℕ)) y.1.2 (a + b))
  have hrnorm : ‖(((y.2 : ℕ) : ℂ) ^ (1 + c))‖ =
      (((y.2 : ℕ) : ℝ) ^ (1 + c).re) := by
    simpa only using
      (Complex.norm_natCast_cpow_of_pos
        (n := (y.2 : ℕ)) y.2.2 (1 + c))
  have hdenNorm :
      ‖(((y.1 : ℕ) : ℂ) ^ (a + b)) *
          (((y.2 : ℕ) : ℂ) ^ (1 + c))‖ =
        (((y.1 : ℕ) : ℝ) ^ (a + b).re) *
          (((y.2 : ℕ) : ℝ) ^ (1 + c).re) := by
    rw [norm_mul, hlnorm, hrnorm]
  unfold hughesYoungEquation96PositiveTerm
  rw [norm_div, hdenNorm]
  simp only [norm_mul]
  rw [Complex.norm_natCast_cpow_of_pos hgcdh a,
    Complex.norm_natCast_cpow_of_pos hgcdk b]
  simp only [add_re, one_re]
  unfold hughesYoungCommonDivisorMajorant
  rw [← Finset.sum_div, ← Finset.sum_div]
  calc
    ‖ramanujanSum (y.1 : ℕ) (y.2 : ℕ)‖ *
          ((Nat.gcd h (y.1 : ℕ) : ℝ) ^ a.re) *
          ((Nat.gcd k (y.1 : ℕ) : ℝ) ^ b.re) /
        ((((y.1 : ℕ) : ℝ) ^ (a.re + b.re)) *
          (((y.2 : ℕ) : ℝ) ^ (1 + c.re))) ≤
      ((∑ d ∈ (Nat.gcd (y.1 : ℕ) (y.2 : ℕ)).divisors, (d : ℝ)) *
          hughesYoungGCDCPowBound h a *
          hughesYoungGCDCPowBound k b) /
        ((((y.1 : ℕ) : ℝ) ^ (a.re + b.re)) *
          (((y.2 : ℕ) : ℝ) ^ (1 + c.re))) := by
      gcongr
      exact mul_nonneg (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _)
        (Finset.sum_nonneg fun _ _ => norm_nonneg _)
    _ = (hughesYoungGCDCPowBound h a *
          hughesYoungGCDCPowBound k b) *
        ((∑ d ∈ (Nat.gcd (y.1 : ℕ) (y.2 : ℕ)).divisors, (d : ℝ)) /
          (((y.1 : ℕ) : ℝ) ^ (a.re + b.re)) /
          (((y.2 : ℕ) : ℝ) ^ (1 + c.re))) := by
      field_simp [hden1.ne', hden2.ne']

/-- Absolute convergence of equation (96) on positive `(l,r)` indices,
under exactly the half-plane hypotheses in Hughes--Young Lemma 6.1. -/
theorem summable_hughesYoungEquation96PositiveTerm
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    {a b c : ℂ} (hA : 1 < (a + b).re) (hC : 0 < c.re) :
    Summable (hughesYoungEquation96PositiveTerm h k a b (1 + c)) := by
  let K := hughesYoungGCDCPowBound h a *
    hughesYoungGCDCPowBound k b
  have hK : 0 ≤ K := by
    exact mul_nonneg
      (Finset.sum_nonneg fun _ _ => norm_nonneg _)
      (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  have hmajor : Summable (fun y : ℕ+ × ℕ+ =>
      K * hughesYoungPositivePairMajorant (a + b).re c.re y) :=
    (summable_hughesYoungPositivePairMajorant hA hC).mul_left K
  refine hmajor.of_norm_bounded fun y => ?_
  exact (norm_hughesYoungEquation96PositiveTerm_le hh hk a b c y).trans
    (mul_le_mul_of_nonneg_left
      (hughesYoungCommonDivisorMajorant_le_pairMajorant hA hC y) hK)

/-- Absolute convergence of equation (96) in the shifted natural-number
coordinates used by the paper and by `hughesYoungEquation96`. -/
theorem summable_hughesYoungEquation96Term
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    {a b c : ℂ} (hA : 1 < (a + b).re) (hC : 0 < c.re) :
    Summable (fun p : ℕ × ℕ =>
      hughesYoungEquation96Term h k a b (1 + c) p.1 p.2) := by
  let e : (ℕ × ℕ) ≃ (ℕ+ × ℕ+) :=
    (Equiv.prodCongr Equiv.pnatEquivNat.symm
      Equiv.pnatEquivNat.symm).trans (Equiv.prodComm _ _)
  have hpos := summable_hughesYoungEquation96PositiveTerm hh hk hA hC
  have hreindex := (e.summable_iff).mpr hpos
  simpa only [e, Function.comp_def, Equiv.trans_apply,
    Equiv.prodCongr_apply, Equiv.prodComm_apply,
    Equiv.pnatEquivNat, hughesYoungEquation96PositiveTerm,
    hughesYoungEquation96Term] using hreindex

/-- Hughes--Young equations (105)--(106), with the Fubini interchange now
proved from the published half-plane hypotheses rather than assumed. -/
theorem hughesYoungEquation105_106
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    (a b c : ℂ) (hA : 1 < (a + b).re) (hC : 0 < c.re) :
    hughesYoungEquation96 h k a b (1 + c) =
      hughesYoungEquation106 h k a b c :=
  hughesYoungEquation105_106_of_summable h k a b c hC
    (summable_hughesYoungEquation96Term hh hk hA hC)

/-! ## Source-strength gcd interpolation on the shifted contour -/

/-- Interpolate the two elementary bounds `gcd h l ≤ h` and
`gcd h l ≤ l`.  The exponent is kept explicit because Hughes--Young use it
just to the right of `1/2`. -/
theorem natCast_gcd_le_rpow_interpolation
    {h l : ℕ} (hh : 0 < h) (hl : 0 < l)
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    (Nat.gcd h l : ℝ) ≤ (h : ℝ) ^ θ * (l : ℝ) ^ (1 - θ) := by
  have hg : 0 < (Nat.gcd h l : ℝ) := by
    exact_mod_cast Nat.gcd_pos_of_pos_left l hh
  have hgh : (Nat.gcd h l : ℝ) ≤ (h : ℝ) := by
    exact_mod_cast Nat.gcd_le_left l hh
  have hgl : (Nat.gcd h l : ℝ) ≤ (l : ℝ) := by
    exact_mod_cast Nat.gcd_le_right h hl
  have hθc : 0 ≤ 1 - θ := sub_nonneg.mpr hθ1
  calc
    (Nat.gcd h l : ℝ) =
        (Nat.gcd h l : ℝ) ^ θ *
          (Nat.gcd h l : ℝ) ^ (1 - θ) := by
      rw [← Real.rpow_add hg]
      norm_num
    _ ≤ (h : ℝ) ^ θ * (l : ℝ) ^ (1 - θ) := by
      exact mul_le_mul
        (Real.rpow_le_rpow hg.le hgh hθ0)
        (Real.rpow_le_rpow hg.le hgl hθc)
        (Real.rpow_nonneg hg.le _)
        (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ h) _)

/-- Source-strength pointwise bound for the unshifted Hughes--Young
arithmetic series.  Choosing `θ > 1/2` makes the resulting triple series
absolutely summable and costs only `(hk)^θ`. -/
theorem norm_hughesYoungEquation96PositiveTerm_one_one_le
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (c : ℂ) (y : ℕ+ × ℕ+) :
    ‖hughesYoungEquation96PositiveTerm h k 1 1 (1 + c) y‖ ≤
      ((h : ℝ) ^ θ * (k : ℝ) ^ θ) *
        hughesYoungCommonDivisorMajorant (2 * θ) c.re y := by
  letI : NeZero (y.1 : ℕ) := ⟨y.1.2.ne'⟩
  have hram := norm_ramanujanSum_le_sum_gcd_divisors
    (y.1 : ℕ) (y.2 : ℕ)
  have hlpos : 0 < (((y.1 : ℕ) : ℝ)) := by exact_mod_cast y.1.2
  have hrpos : 0 < (((y.2 : ℕ) : ℝ)) := by exact_mod_cast y.2.2
  have hgcdh : 0 < Nat.gcd h (y.1 : ℕ) :=
    Nat.gcd_pos_of_pos_left _ hh
  have hgcdk : 0 < Nat.gcd k (y.1 : ℕ) :=
    Nat.gcd_pos_of_pos_left _ hk
  have hhg := natCast_gcd_le_rpow_interpolation hh y.1.2 hθ0 hθ1
  have hkg := natCast_gcd_le_rpow_interpolation hk y.1.2 hθ0 hθ1
  have hden1 : 0 < (((y.1 : ℕ) : ℝ) ^ (2 : ℝ)) :=
    Real.rpow_pos_of_pos hlpos _
  have hden2 : 0 < (((y.2 : ℕ) : ℝ) ^ (1 + c.re)) :=
    Real.rpow_pos_of_pos hrpos _
  have hlnorm : ‖(((y.1 : ℕ) : ℂ) ^ ((1 : ℂ) + 1))‖ =
      (((y.1 : ℕ) : ℝ) ^ (2 : ℝ)) := by
    have h := Complex.norm_natCast_cpow_of_pos
      (n := (y.1 : ℕ)) y.1.2 ((1 : ℂ) + 1)
    norm_num at h ⊢
  have hrnorm : ‖(((y.2 : ℕ) : ℂ) ^ (1 + c))‖ =
      (((y.2 : ℕ) : ℝ) ^ (1 + c.re)) := by
    simpa only [add_re, one_re] using
      (Complex.norm_natCast_cpow_of_pos
        (n := (y.2 : ℕ)) y.2.2 (1 + c))
  have hhNorm : ‖(((Nat.gcd h (y.1 : ℕ) : ℕ) : ℂ) ^ (1 : ℂ))‖ =
      (Nat.gcd h (y.1 : ℕ) : ℝ) := by
    rw [Complex.norm_natCast_cpow_of_pos hgcdh]
    norm_num
  have hkNorm : ‖(((Nat.gcd k (y.1 : ℕ) : ℕ) : ℂ) ^ (1 : ℂ))‖ =
      (Nat.gcd k (y.1 : ℕ) : ℝ) := by
    rw [Complex.norm_natCast_cpow_of_pos hgcdk]
    norm_num
  have hdenNorm :
      ‖(((y.1 : ℕ) : ℂ) ^ ((1 : ℂ) + 1)) *
          (((y.2 : ℕ) : ℂ) ^ (1 + c))‖ =
        (((y.1 : ℕ) : ℝ) ^ (2 : ℝ)) *
          (((y.2 : ℕ) : ℝ) ^ (1 + c.re)) := by
    rw [norm_mul, hlnorm, hrnorm]
  unfold hughesYoungEquation96PositiveTerm
  rw [norm_div, hdenNorm]
  simp only [norm_mul, hhNorm, hkNorm]
  unfold hughesYoungCommonDivisorMajorant
  rw [← Finset.sum_div, ← Finset.sum_div]
  have hlθ : 0 ≤ (((y.1 : ℕ) : ℝ) ^ (1 - θ)) :=
    Real.rpow_nonneg hlpos.le _
  have hhθ : 0 ≤ ((h : ℝ) ^ θ) := Real.rpow_nonneg (by positivity) _
  have hkθ : 0 ≤ ((k : ℝ) ^ θ) := Real.rpow_nonneg (by positivity) _
  calc
    ‖ramanujanSum (y.1 : ℕ) (y.2 : ℕ)‖ *
          (Nat.gcd h (y.1 : ℕ) : ℝ) *
          (Nat.gcd k (y.1 : ℕ) : ℝ) /
        ((((y.1 : ℕ) : ℝ) ^ (2 : ℝ)) *
          (((y.2 : ℕ) : ℝ) ^ (1 + c.re))) ≤
      ((∑ d ∈ (Nat.gcd (y.1 : ℕ) (y.2 : ℕ)).divisors, (d : ℝ)) *
          ((h : ℝ) ^ θ * (((y.1 : ℕ) : ℝ) ^ (1 - θ))) *
          ((k : ℝ) ^ θ * (((y.1 : ℕ) : ℝ) ^ (1 - θ)))) /
        ((((y.1 : ℕ) : ℝ) ^ (2 : ℝ)) *
          (((y.2 : ℕ) : ℝ) ^ (1 + c.re))) := by
      gcongr
      · exact hhg
      · exact hkg
    _ = ((h : ℝ) ^ θ * (k : ℝ) ^ θ) *
        ((∑ d ∈ (Nat.gcd (y.1 : ℕ) (y.2 : ℕ)).divisors, (d : ℝ)) /
          (((y.1 : ℕ) : ℝ) ^ (2 * θ)) /
          (((y.2 : ℕ) : ℝ) ^ (1 + c.re))) := by
      rw [show ((y.1 : ℕ) : ℝ) ^ (2 : ℝ) =
          ((y.1 : ℕ) : ℝ) ^ (2 * θ) *
            (((y.1 : ℕ) : ℝ) ^ (1 - θ) *
              ((y.1 : ℕ) : ℝ) ^ (1 - θ)) by
        rw [← Real.rpow_add hlpos, ← Real.rpow_add hlpos]
        congr 1
        ring]
      field_simp [hden1.ne', hden2.ne',
        (Real.rpow_pos_of_pos hlpos (2 * θ)).ne',
        (Real.rpow_pos_of_pos hlpos (1 - θ)).ne']

/-- Absolute convergence of the Hughes--Young arithmetic series at
`a = b = 1`, with the source-strength interpolated dependence on the two
twisting integers. -/
theorem summable_hughesYoungEquation96PositiveTerm_one_one
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    {θ : ℝ} (hθ : 1 / 2 < θ) (hθ1 : θ ≤ 1)
    {c : ℂ} (hc : 0 < c.re) :
    Summable (hughesYoungEquation96PositiveTerm h k 1 1 (1 + c)) := by
  have hθ0 : 0 ≤ θ := le_trans (by norm_num) hθ.le
  have hA : 1 < 2 * θ := by linarith
  let K : ℝ := (h : ℝ) ^ θ * (k : ℝ) ^ θ
  have hK : 0 ≤ K := by
    dsimp only [K]
    positivity
  have hMajor : Summable (fun y : ℕ+ × ℕ+ =>
      K * hughesYoungPositivePairMajorant (2 * θ) c.re y) :=
    (summable_hughesYoungPositivePairMajorant hA hc).mul_left K
  refine hMajor.of_norm_bounded fun y => ?_
  exact (norm_hughesYoungEquation96PositiveTerm_one_one_le
      hh hk hθ0 hθ1 c y).trans
    (mul_le_mul_of_nonneg_left
      (hughesYoungCommonDivisorMajorant_le_pairMajorant hA hc y) hK)

/-- The total equation-(96) series is bounded by the convergent positive
triple majorant.  This is the quantitative form needed after the
Hughes--Young contour is moved just to the right of `Re s = 1/2`. -/
theorem norm_tsum_hughesYoungEquation96PositiveTerm_one_one_le
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    {θ : ℝ} (hθ : 1 / 2 < θ) (hθ1 : θ ≤ 1)
    {c : ℂ} (hc : 0 < c.re) :
    ‖∑' y : ℕ+ × ℕ+,
        hughesYoungEquation96PositiveTerm h k 1 1 (1 + c) y‖ ≤
      ((h : ℝ) ^ θ * (k : ℝ) ^ θ) *
        ∑' y : ℕ+ × ℕ+,
          hughesYoungPositivePairMajorant (2 * θ) c.re y := by
  have hθ0 : 0 ≤ θ := le_trans (by norm_num) hθ.le
  have hA : 1 < 2 * θ := by linarith
  let K : ℝ := (h : ℝ) ^ θ * (k : ℝ) ^ θ
  have hK : 0 ≤ K := by
    dsimp only [K]
    positivity
  have hTerm :=
    summable_hughesYoungEquation96PositiveTerm_one_one hh hk hθ hθ1 hc
  have hMajor : Summable (fun y : ℕ+ × ℕ+ =>
      K * hughesYoungPositivePairMajorant (2 * θ) c.re y) :=
    (summable_hughesYoungPositivePairMajorant hA hc).mul_left K
  calc
    ‖∑' y : ℕ+ × ℕ+,
        hughesYoungEquation96PositiveTerm h k 1 1 (1 + c) y‖ ≤
        ∑' y : ℕ+ × ℕ+,
          ‖hughesYoungEquation96PositiveTerm h k 1 1 (1 + c) y‖ :=
      norm_tsum_le_tsum_norm hTerm.norm
    _ ≤ ∑' y : ℕ+ × ℕ+,
        K * hughesYoungPositivePairMajorant (2 * θ) c.re y :=
      hTerm.norm.tsum_le_tsum
        (fun y => (norm_hughesYoungEquation96PositiveTerm_one_one_le
          hh hk hθ0 hθ1 c y).trans
            (mul_le_mul_of_nonneg_left
              (hughesYoungCommonDivisorMajorant_le_pairMajorant hA hc y) hK))
        hMajor
    _ = ((h : ℝ) ^ θ * (k : ℝ) ^ θ) *
        ∑' y : ℕ+ × ℕ+,
          hughesYoungPositivePairMajorant (2 * θ) c.re y := by
      rw [tsum_mul_left]

/-- Equation (96) is exactly the positive-index product series used by the
interpolated majorant. -/
theorem hughesYoungEquation96_eq_positiveTsum_one_one
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    {c : ℂ} (hc : 0 < c.re) :
    hughesYoungEquation96 h k 1 1 (1 + c) =
      ∑' y : ℕ+ × ℕ+,
        hughesYoungEquation96PositiveTerm h k 1 1 (1 + c) y := by
  let e : (ℕ × ℕ) ≃ (ℕ+ × ℕ+) :=
    (Equiv.prodCongr Equiv.pnatEquivNat.symm
      Equiv.pnatEquivNat.symm).trans (Equiv.prodComm _ _)
  rw [hughesYoungEquation96_eq_tsum_term]
  have hTerm : Summable (fun p : ℕ × ℕ =>
      hughesYoungEquation96Term h k 1 1 (1 + c) p.1 p.2) :=
    summable_hughesYoungEquation96Term hh hk (by norm_num) hc
  rw [← hTerm.tsum_prod]
  rw [← (e.tsum_eq
    (hughesYoungEquation96PositiveTerm h k 1 1 (1 + c)))]
  apply tsum_congr
  intro p
  simp [e, Equiv.pnatEquivNat, Nat.succPNat_coe,
    Nat.succ_eq_add_one,
    hughesYoungEquation96PositiveTerm,
    hughesYoungEquation96Term]

/-- Source-strength upper bound for equation (96) itself. -/
theorem norm_hughesYoungEquation96_one_one_le
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    {θ : ℝ} (hθ : 1 / 2 < θ) (hθ1 : θ ≤ 1)
    {c : ℂ} (hc : 0 < c.re) :
    ‖hughesYoungEquation96 h k 1 1 (1 + c)‖ ≤
      ((h : ℝ) ^ θ * (k : ℝ) ^ θ) *
        ∑' y : ℕ+ × ℕ+,
          hughesYoungPositivePairMajorant (2 * θ) c.re y := by
  rw [hughesYoungEquation96_eq_positiveTsum_one_one hh hk hc]
  exact norm_tsum_hughesYoungEquation96PositiveTerm_one_one_le
    hh hk hθ hθ1 hc

end RiemannZeta.GuthMaynard
