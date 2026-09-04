import GafniTao.WooleySection7Congruence

/-!
# Extraction of Wooley's top congruences in Section 7

This file formalizes the passage from (7.6), after the source's first
integral change of equations, to (7.10).  The variables on the right lie on
the progression `p^b * t`; hence equation `j` on that side is divisible by
`p^(j*b)`.  For the top `r` equations this kills the right side modulo
`p^((k-r+1)*b)`.  The remaining left displacement is then exactly the
translated-and-dilated displacement used by the equation-(7.12) theorem.
-/

open Finset Polynomial
open scoped BigOperators

namespace GafniTao

noncomputable section

/-- The special first-phase normal form (7.7), with zero-based indices. -/
def wooleySection7NormalSystem
    (k p c : ℕ) (psi : WooleyPolynomialSystem k) :
    WooleyPolynomialSystem k := fun j =>
  X ^ ((j : ℕ) + 1) +
    C ((p : ℤ) ^ c) * X ^ (k + 1) * psi j

/-- The top `r` members of (7.7) are literally the system used in (7.10). -/
theorem wooleySection7NormalSystem_top
    {k r p c : ℕ} (hrk : r ≤ k) (psi : WooleyPolynomialSystem k)
    (l : Fin r) :
    wooleySection7NormalSystem k p c psi
        ⟨wooleySection7Node k r l,
          wooleySection7Node_succ_le hrk l⟩ =
      wooleySection7TopSystem k r p c
        (fun u => psi
          ⟨wooleySection7Node k r u,
            wooleySection7Node_succ_le hrk u⟩) l := by
  rfl

/-- Evaluation of equation `j` in the normal system on the progression
`p^b*t` is divisible by `p^(b*(j+1))`. -/
theorem wooleySection7NormalSystem_eval_progression_dvd
    {k p c b : ℕ} (psi : WooleyPolynomialSystem k)
    (j : Fin k) (t : ℤ) :
    (p : ℤ) ^ (b * ((j : ℕ) + 1)) ∣
      (wooleySection7NormalSystem k p c psi j).eval
        ((p : ℤ) ^ b * t) := by
  let d := (j : ℕ) + 1
  have hjk : d ≤ k := j.isLt
  have hfirst : (p : ℤ) ^ (b * d) ∣
      ((p : ℤ) ^ b * t) ^ d := by
    rw [mul_pow, pow_mul]
    exact dvd_mul_right _ _
  have htailPow : (p : ℤ) ^ (b * d) ∣
      ((p : ℤ) ^ b * t) ^ (k + 1) := by
    have hle : b * d ≤ b * (k + 1) :=
      Nat.mul_le_mul_left b (hjk.trans (Nat.le_succ k))
    have hpowers : (p : ℤ) ^ (b * d) ∣
        (p : ℤ) ^ (b * (k + 1)) := pow_dvd_pow (p : ℤ) hle
    have hproduct : (p : ℤ) ^ (b * d) ∣
        (p : ℤ) ^ (b * (k + 1)) * t ^ (k + 1) :=
      dvd_mul_of_dvd_left hpowers _
    simpa only [mul_pow, pow_mul] using hproduct
  have htail : (p : ℤ) ^ (b * d) ∣
      (p : ℤ) ^ c * (((p : ℤ) ^ b * t) ^ (k + 1) *
        (psi j).eval ((p : ℤ) ^ b * t)) := by
    obtain ⟨z, hz⟩ := htailPow
    refine ⟨(p : ℤ) ^ c * z *
      (psi j).eval ((p : ℤ) ^ b * t), ?_⟩
    rw [hz]
    ring
  unfold wooleySection7NormalSystem
  simp only [eval_add, eval_pow, eval_X, eval_mul, eval_C]
  dsimp only [d] at hfirst htail ⊢
  exact dvd_add hfirst (by simpa only [mul_assoc] using htail)

/-- Every equal-length tuple displacement on the right progression has the
same divisibility. -/
theorem wooleySection7NormalSystem_right_displacement_dvd
    {I : Type*} {k p c b S : ℕ}
    (psi : WooleyPolynomialSystem k) (j : Fin k) (point : I → ℤ)
    (xy : WooleyFiniteTuple S I × WooleyFiniteTuple S I) :
    (p : ℤ) ^ (b * ((j : ℕ) + 1)) ∣
      wooleyIntegerTupleDisplacement S
        (fun x => (wooleySection7NormalSystem k p c psi j).eval
          ((p : ℤ) ^ b * point x)) xy := by
  unfold wooleyIntegerTupleDisplacement
  apply dvd_sub
  · exact dvd_sum fun i _ =>
      wooleySection7NormalSystem_eval_progression_dvd psi j (point (xy.1 i))
  · exact dvd_sum fun i _ =>
      wooleySection7NormalSystem_eval_progression_dvd psi j (point (xy.2 i))

/-- Integer negation of a polynomial negates its tuple displacement. -/
theorem wooleyIntegerTupleDisplacement_polynomial_neg
    {I : Type*} (S : ℕ) (f : Polynomial ℤ) (point : I → ℤ)
    (xy : WooleyFiniteTuple S I × WooleyFiniteTuple S I) :
    wooleyIntegerTupleDisplacement S
        (fun x => (-f).eval (point x)) xy =
      -wooleyIntegerTupleDisplacement S
        (fun x => f.eval (point x)) xy := by
  simp only [wooleyIntegerTupleDisplacement, eval_neg, Finset.sum_neg_distrib]
  ring

/-- Exact (7.6)-to-(7.10) implication for a system already in the source
normal form (7.7).  The input uses the genuine combined left-minus-right
Fourier displacement modulo `p^B`; the output is integral divisibility by
the precise retained modulus. -/
theorem wooleySection7_original_implies_top_congruences
    {I J : Type*} {k r p c a b B R S : ℕ}
    (hrk : r ≤ k) (hMB : (k - r + 1) * b ≤ B)
    (psi : WooleyPolynomialSystem k) (h : ℤ)
    (leftPoint : I → ℤ) (rightPoint : J → ℤ)
    (leftXY : WooleyFiniteTuple R I × WooleyFiniteTuple R I)
    (rightXY : WooleyFiniteTuple S J × WooleyFiniteTuple S J)
    (horiginal : ∀ j : Fin k,
      (p : ℤ) ^ B ∣
        wooleyIntegerTupleDisplacement R
          (fun x => (wooleySection7NormalSystem k p c psi j).eval
            ((p : ℤ) ^ a * leftPoint x + h)) leftXY -
        wooleyIntegerTupleDisplacement S
          (fun x => (wooleySection7NormalSystem k p c psi j).eval
            ((p : ℤ) ^ b * rightPoint x)) rightXY) :
    ∀ l : Fin r, (p : ℤ) ^ ((k - r + 1) * b) ∣
      wooleyIntegerTupleDisplacement R
        (fun x =>
          (wooleySection7TranslatedDilatedPolynomial p a h
            (wooleySection7TopSystem k r p c
              (fun u => psi
                ⟨wooleySection7Node k r u,
                  wooleySection7Node_succ_le hrk u⟩) l)).eval
              (leftPoint x)) leftXY := by
  intro l
  let j : Fin k :=
    ⟨wooleySection7Node k r l, wooleySection7Node_succ_le hrk l⟩
  let M := (k - r + 1) * b
  let leftDisp : ℤ := wooleyIntegerTupleDisplacement R
    (fun x => (wooleySection7NormalSystem k p c psi j).eval
      ((p : ℤ) ^ a * leftPoint x + h)) leftXY
  let rightDisp : ℤ := wooleyIntegerTupleDisplacement S
    (fun x => (wooleySection7NormalSystem k p c psi j).eval
      ((p : ℤ) ^ b * rightPoint x)) rightXY
  have hcombined : (p : ℤ) ^ M ∣ leftDisp - rightDisp :=
    dvd_trans (pow_dvd_pow (p : ℤ) hMB) (horiginal j)
  have hnode : k - r + 1 ≤ (j : ℕ) + 1 := by
    dsimp only [j, wooleySection7Node]
    omega
  have hrightStrong : (p : ℤ) ^ (b * ((j : ℕ) + 1)) ∣ rightDisp := by
    exact wooleySection7NormalSystem_right_displacement_dvd
      psi j rightPoint rightXY
  have hright : (p : ℤ) ^ M ∣ rightDisp := by
    apply dvd_trans (pow_dvd_pow (p : ℤ) ?_) hrightStrong
    dsimp only [M]
    nlinarith
  have hleft : (p : ℤ) ^ M ∣ leftDisp := by
    rw [show leftDisp = (leftDisp - rightDisp) + rightDisp by ring]
    exact dvd_add hcombined hright
  have htranslate :=
    wooleySection7TranslatedDilatedPolynomial_tupleDisplacement
      p a R h (wooleySection7NormalSystem k p c psi j)
        leftPoint leftXY
  have hnormal : wooleySection7NormalSystem k p c psi j =
      wooleySection7TopSystem k r p c
        (fun u => psi
          ⟨wooleySection7Node k r u,
            wooleySection7Node_succ_le hrk u⟩) l := by
    dsimp only [j]
    exact wooleySection7NormalSystem_top hrk psi l
  dsimp only [leftDisp] at hleft
  rw [hnormal] at hleft htranslate
  dsimp only [M] at hleft ⊢
  rw [htranslate] at hleft
  exact hleft

/-- The actual left polynomial system in (7.6), after `x = p^a u + ξ`
and translation by `η`, so that `h = ξ-η`. -/
def wooleySection7LeftFourierSystem
    (k p c a : ℕ) (psi : WooleyPolynomialSystem k) (h : ℤ) :
    WooleyPolynomialSystem k :=
  wooleyAffinePolynomialSystem
    (wooleySection7NormalSystem k p c psi) (p ^ a) h

/-- The negated right system makes the single Fourier displacement encode
the left-minus-right congruence in (7.6). -/
def wooleySection7RightFourierSystem
    (k p c b : ℕ) (psi : WooleyPolynomialSystem k) :
    WooleyPolynomialSystem k := fun j =>
  -(wooleyAffinePolynomialSystem
      (wooleySection7NormalSystem k p c psi) (p ^ b) 0 j)

/-- The finite-Fourier displacement for the two source tuple families is
exactly reduction of the integral left-minus-right displacement. -/
theorem wooleySection7OriginalDisplacement_eq_intCast
    {k p c a b B R S : ℕ} (psi : WooleyPolynomialSystem k) (h : ℤ)
    (left right : WooleySourceSequence)
    (omega : WooleySourceMixedTuple R S left right) (j : Fin k) :
    wooleyEquation717OriginalDisplacement
        (wooleySection7LeftFourierSystem k p c a psi h)
        (wooleySection7RightFourierSystem k p c b psi)
        (p ^ B) R S left right omega j =
      ((wooleyIntegerTupleDisplacement R
          (fun x : ↑left.support =>
            (wooleySection7NormalSystem k p c psi j).eval
              ((p : ℤ) ^ a * (x : ℤ) + h)) omega.1 -
        wooleyIntegerTupleDisplacement S
          (fun x : ↑right.support =>
            (wooleySection7NormalSystem k p c psi j).eval
              ((p : ℤ) ^ b * (x : ℤ))) omega.2 : ℤ) : ZMod (p ^ B)) := by
  simp [wooleyEquation717OriginalDisplacement,
    wooleySourceTuplePolynomialDisplacement, wooleyTupleDisplacement,
    wooleyIntegerTupleDisplacement, wooleyPolynomialValue,
    wooleySection7LeftFourierSystem,
    wooleySection7RightFourierSystem, wooleyAffinePolynomialSystem_eval]
  ring

/-- Complete normal-form version of the hard source implication:
the genuine (7.6) displacement forces an exact spaced system (7.12). -/
theorem wooleySection7_original_implies_equation_7_12
    {I J : Type*} {k r p c a b B nu R S gamma : ℕ}
    (hpPrime : p.Prime) (hc : 1 ≤ c) (hr : 1 ≤ r)
    (hrk : r < k) (hkp : k < p)
    (hMB : (k - r + 1) * b ≤ B)
    (hgammaK : gamma * k ≤ a)
    (hBPrime : (nu : ℤ) < wooleySection7BPrimeInt k r a b gamma)
    (omegaVal h : ℤ) (homega : omegaVal ≠ 0)
    (hcop : Nat.Coprime p omegaVal.natAbs)
    (hsep : h = omegaVal * (p : ℤ) ^ gamma) (hh : h ≠ 0)
    (psi : WooleyPolynomialSystem k)
    (leftPoint : I → ℤ) (rightPoint : J → ℤ)
    (leftXY : WooleyFiniteTuple R I × WooleyFiniteTuple R I)
    (rightXY : WooleyFiniteTuple S J × WooleyFiniteTuple S J)
    (horiginal : ∀ j : Fin k,
      (p : ℤ) ^ B ∣
        wooleyIntegerTupleDisplacement R
          (fun x => (wooleySection7NormalSystem k p c psi j).eval
            ((p : ℤ) ^ a * leftPoint x + h)) leftXY -
        wooleyIntegerTupleDisplacement S
          (fun x => (wooleySection7NormalSystem k p c psi j).eval
            ((p : ℤ) ^ b * rightPoint x)) rightXY) :
    ∃ Psi : WooleyPolynomialSystem r,
      Psi.Spaced p (a - (k - r) * gamma) ∧
      ∀ i : Fin r,
        wooleyTupleDisplacement
          (p ^ wooleySection7BPrimeNat k r a b gamma) r R
          (fun x j => (((Psi j).eval (leftPoint x) : ℤ) :
            ZMod (p ^ wooleySection7BPrimeNat k r a b gamma))) leftXY i = 0 := by
  apply wooleySection7_top_congruences_imply_equation_7_12
    hpPrime hc hr hrk hkp hgammaK hBPrime omegaVal h homega hcop hsep hh
      (fun u => psi
        ⟨wooleySection7Node k r u,
          wooleySection7Node_succ_le hrk.le u⟩) leftPoint leftXY
  exact wooleySection7_original_implies_top_congruences
    hrk.le hMB psi h leftPoint rightPoint leftXY rightXY horiginal

/-- The pointwise forcing theorem required by the exact equation-(7.17)
Fourier insertion.  Unlike the earlier abstract interface, no (7.12)
hypothesis remains: it is derived from the original displacement. -/
theorem wooleySection7_equation_7_12_forced
    {k r p c a b B nu R S gamma : ℕ}
    (hpPrime : p.Prime) (hc : 1 ≤ c) (hr : 1 ≤ r)
    (hrk : r < k) (hkp : k < p)
    (hMB : (k - r + 1) * b ≤ B)
    (hgammaK : gamma * k ≤ a)
    (hBPrime : (nu : ℤ) < wooleySection7BPrimeInt k r a b gamma)
    (omegaVal h : ℤ) (homega : omegaVal ≠ 0)
    (hcop : Nat.Coprime p omegaVal.natAbs)
    (hsep : h = omegaVal * (p : ℤ) ^ gamma) (hh : h ≠ 0)
    (psi : WooleyPolynomialSystem k)
    (left right : WooleySourceSequence)
    (omega : WooleySourceMixedTuple R S left right)
    (horiginal : wooleyEquation717OriginalDisplacement
      (wooleySection7LeftFourierSystem k p c a psi h)
      (wooleySection7RightFourierSystem k p c b psi)
      (p ^ B) R S left right omega = 0) :
    ∃ Psi : WooleyPolynomialSystem r,
      Psi.Spaced p (a - (k - r) * gamma) ∧
      wooleyEquation717InsertedDisplacement Psi
        (p ^ wooleySection7BPrimeNat k r a b gamma)
        R S left right omega = 0 := by
  have hdiv : ∀ j : Fin k,
      (p : ℤ) ^ B ∣
        wooleyIntegerTupleDisplacement R
          (fun x : ↑left.support =>
            (wooleySection7NormalSystem k p c psi j).eval
              ((p : ℤ) ^ a * (x : ℤ) + h)) omega.1 -
        wooleyIntegerTupleDisplacement S
          (fun x : ↑right.support =>
            (wooleySection7NormalSystem k p c psi j).eval
              ((p : ℤ) ^ b * (x : ℤ))) omega.2 := by
    intro j
    have hj := congrFun horiginal j
    rw [wooleySection7OriginalDisplacement_eq_intCast
      psi h left right omega j] at hj
    simp only [Pi.zero_apply] at hj
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hj
    norm_num only [Nat.cast_pow, Nat.cast_ofNat] at hj
    exact hj
  obtain ⟨Psi, hPsi, hlow⟩ :=
    wooleySection7_original_implies_equation_7_12
      hpPrime hc hr hrk hkp hMB hgammaK hBPrime
        omegaVal h homega hcop hsep hh psi
        (fun x : ↑left.support => (x : ℤ))
        (fun x : ↑right.support => (x : ℤ)) omega.1 omega.2 hdiv
  refine ⟨Psi, hPsi, ?_⟩
  funext i
  exact hlow i

/-- Uniform source form: one lower system `Psi`, determined before any
tuple is chosen, is forced by the original Fourier displacement for every
term in the expansion.  This is the quantifier order required by (7.17). -/
theorem wooleySection7_exists_uniform_equation_7_12
    {k r p c a b B nu R S gamma : ℕ}
    (hpPrime : p.Prime) (hc : 1 ≤ c) (hr : 1 ≤ r)
    (hrk : r < k) (hkp : k < p)
    (hMB : (k - r + 1) * b ≤ B)
    (hgammaK : gamma * k ≤ a)
    (hBPrime : (nu : ℤ) < wooleySection7BPrimeInt k r a b gamma)
    (omegaVal h : ℤ) (homega : omegaVal ≠ 0)
    (hcop : Nat.Coprime p omegaVal.natAbs)
    (hsep : h = omegaVal * (p : ℤ) ^ gamma) (hh : h ≠ 0)
    (psi : WooleyPolynomialSystem k)
    (left right : WooleySourceSequence) :
    ∃ Psi : WooleyPolynomialSystem r,
      Psi.Spaced p (a - (k - r) * gamma) ∧
      ∀ omega : WooleySourceMixedTuple R S left right,
        wooleyEquation717OriginalDisplacement
          (wooleySection7LeftFourierSystem k p c a psi h)
          (wooleySection7RightFourierSystem k p c b psi)
          (p ^ B) R S left right omega = 0 →
        wooleyEquation717InsertedDisplacement Psi
          (p ^ wooleySection7BPrimeNat k r a b gamma)
          R S left right omega = 0 := by
  have hkpos : 1 ≤ k := hr.trans hrk.le
  have hgamma : gamma ≤ a := by
    have hle : gamma ≤ gamma * k := by
      simpa only [Nat.mul_one] using Nat.mul_le_mul_left gamma hkpos
    exact hle.trans hgammaK
  let M := (k - r + 1) * b
  let bp := wooleySection7BPrimeNat k r a b gamma
  have hsum := wooley_section7_BPrimeNat_add hBPrime
  have hdecomp : M = gamma * k + r * (a - gamma) + bp := by
    dsimp only [M, bp]
    have hgammaR : gamma * r + (a - gamma) * r = a * r := by
      rw [← Nat.add_mul, Nat.add_sub_of_le hgamma]
    have hsplit : gamma * k = gamma * (k - r) + gamma * r := by
      have hkr : (k - r) + r = k := Nat.sub_add_cancel hrk.le
      calc
        gamma * k = gamma * ((k - r) + r) := by rw [hkr]
        _ = _ := Nat.mul_add _ _ _
    rw [hsplit]
    calc
      (k - r + 1) * b =
          bp + r * a + (k - r) * gamma := by
        simpa only [bp] using hsum.symm
      _ = gamma * (k - r) + gamma * r +
          r * (a - gamma) + bp := by
        rw [Nat.mul_comm (k - r) gamma]
        have hgammaR' : gamma * r + r * (a - gamma) = r * a := by
          simpa [Nat.mul_comm] using hgammaR
        omega
  have hgammaM : gamma * k ≤ M := by omega
  have hcommon : r * (a - gamma) ≤ M - gamma * k := by omega
  obtain ⟨Psi, hPsi, huniform⟩ :=
    wooleySection7_top_congruences_exist_lower_system
      hpPrime hc hrk.le hkp hgamma hgammaK hgammaM hcommon
        omegaVal h homega hcop hsep hh
        (fun u => psi
          ⟨wooleySection7Node k r u,
            wooleySection7Node_succ_le hrk.le u⟩)
  refine ⟨Psi, hPsi, ?_⟩
  intro tuple horiginal
  have hdiv : ∀ j : Fin k,
      (p : ℤ) ^ B ∣
        wooleyIntegerTupleDisplacement R
          (fun x : ↑left.support =>
            (wooleySection7NormalSystem k p c psi j).eval
              ((p : ℤ) ^ a * (x : ℤ) + h)) tuple.1 -
        wooleyIntegerTupleDisplacement S
          (fun x : ↑right.support =>
            (wooleySection7NormalSystem k p c psi j).eval
              ((p : ℤ) ^ b * (x : ℤ))) tuple.2 := by
    intro j
    have hj := congrFun horiginal j
    rw [wooleySection7OriginalDisplacement_eq_intCast
      psi h left right tuple j] at hj
    simp only [Pi.zero_apply] at hj
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hj
    norm_num only [Nat.cast_pow, Nat.cast_ofNat] at hj
    exact hj
  have htop := wooleySection7_original_implies_top_congruences
    hrk.le hMB psi h
      (fun x : ↑left.support => (x : ℤ))
      (fun x : ↑right.support => (x : ℤ)) tuple.1 tuple.2 hdiv
  have hraw := huniform (fun x : ↑left.support => (x : ℤ)) tuple.1 htop
  funext i
  have hdepth := wooley_section7_common_depth_eq_BPrimeNat
    hrk hgamma hBPrime
  have hdivLow : (p : ℤ) ^ bp ∣
      wooleyIntegerTupleDisplacement R
        (fun x : ↑left.support => (Psi i).eval (x : ℤ)) tuple.1 := by
    have hi := hraw i
    dsimp only [M, bp] at hi hdepth ⊢
    rw [hdepth] at hi
    exact hi
  have hz :
      (wooleyIntegerTupleDisplacement R
        (fun x : ↑left.support => (Psi i).eval (x : ℤ)) tuple.1 :
          ZMod (p ^ bp)) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    norm_num only [Nat.cast_pow, Nat.cast_ofNat]
    exact hdivLow
  rw [wooleyIntegerTupleDisplacement_cast
    (p ^ bp) r R
      (fun x : ↑left.support => fun j => (Psi j).eval (x : ℤ))
      tuple.1 i] at hz
  simpa only [wooleyEquation717InsertedDisplacement,
    wooleySourceTuplePolynomialDisplacement, wooleyPolynomialValue, bp]
    using hz

/-- The exact finite normalized identity displayed in (7.17), packaged only
to keep its two occurrences in the native theorem synchronized. -/
def WooleyEquation717FiniteIdentity
    {k r : ℕ} (leftPhi rightPhi : WooleyPolynomialSystem k)
    (Psi : WooleyPolynomialSystem r)
    (q qPrime R S : ℕ) [NeZero q] [NeZero qPrime]
    (left right : WooleySourceSequence) : Prop :=
  ((((q ^ k : ℕ) : ℂ))⁻¹) *
      ∑ alpha : Fin k → ZMod q,
        ∑ tuple : WooleySourceMixedTuple R S left right,
          wooleySourceMixedTupleCoefficient R S left right tuple *
            ∏ j, ZMod.stdAddChar
              (alpha j * wooleyEquation717OriginalDisplacement
                leftPhi rightPhi q R S left right tuple j) =
    ((((q ^ k : ℕ) : ℂ))⁻¹) *
      ((((qPrime ^ r : ℕ) : ℂ))⁻¹) *
        ∑ alpha : Fin k → ZMod q,
          ∑ beta : Fin r → ZMod qPrime,
            ∑ tuple : WooleySourceMixedTuple R S left right,
              wooleySourceMixedTupleCoefficient R S left right tuple *
                (∏ j, ZMod.stdAddChar
                  (alpha j * wooleyEquation717OriginalDisplacement
                    leftPhi rightPhi q R S left right tuple j)) *
                ∏ l, ZMod.stdAddChar
                  (beta l * wooleyEquation717InsertedDisplacement
                    Psi qPrime R S left right tuple l)

/-- Equation (7.17) for the genuine Section 7 normal-form systems, with the
uniform lower system constructed by the source's determinant and valuation
argument. -/
theorem wooley_equation_7_17_normal_native
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
    (psi : WooleyPolynomialSystem k)
    (left right : WooleySourceSequence) :
    ∃ Psi : WooleyPolynomialSystem r,
      Psi.Spaced p (a - (k - r) * gamma) ∧
      WooleyEquation717FiniteIdentity
        (wooleySection7LeftFourierSystem k p c a psi h)
        (wooleySection7RightFourierSystem k p c b psi)
        Psi (p ^ B)
        (p ^ wooleySection7BPrimeNat k r a b gamma)
        R S left right := by
  obtain ⟨Psi, hPsi, hforced⟩ :=
    wooleySection7_exists_uniform_equation_7_12
      hpPrime hc hr hrk hkp hMB hgammaK hBPrime
        omegaVal h homega hcop hsep hh psi left right
  refine ⟨Psi, hPsi, ?_⟩
  unfold WooleyEquation717FiniteIdentity
  exact wooley_equation_7_17_tuple
    (wooleySection7LeftFourierSystem k p c a psi h)
    (wooleySection7RightFourierSystem k p c b psi)
    Psi (p ^ B) (p ^ wooleySection7BPrimeNat k r a b gamma)
    R S left right hforced

#print axioms wooleySection7NormalSystem_top
#print axioms wooleySection7NormalSystem_eval_progression_dvd
#print axioms wooleySection7NormalSystem_right_displacement_dvd
#print axioms wooleyIntegerTupleDisplacement_polynomial_neg
#print axioms wooleySection7_original_implies_top_congruences
#print axioms wooleySection7OriginalDisplacement_eq_intCast
#print axioms wooleySection7_original_implies_equation_7_12
#print axioms wooleySection7_equation_7_12_forced
#print axioms wooleySection7_exists_uniform_equation_7_12
#print axioms WooleyEquation717FiniteIdentity
#print axioms wooley_equation_7_17_normal_native

end

end GafniTao
