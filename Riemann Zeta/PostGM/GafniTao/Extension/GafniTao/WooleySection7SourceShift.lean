import GafniTao.WooleyTranslatedNormalChange

/-!
# Source-residue entry to Wooley equation (7.17)

This file restores the two literal residue representatives `xi` and `eta`.
The earlier congruence kernel is phrased after subtracting `eta`; here the
translated polynomial system is normalized by the integral row change from
the preceding file, and the resulting forcing theorem is applied to the
original positive Fourier phases.
-/

open Finset Polynomial Matrix
open scoped BigOperators

namespace GafniTao

noncomputable section

theorem wooleySection7PositiveDisplacementShifted_eq_intCast
    {k p a b B R S : ℕ} (phi : WooleyPolynomialSystem k)
    (xi eta : ℤ) (left right : WooleySourceSequence)
    (omega : WooleySourceMixedTuple R S left right) (j : Fin k) :
    wooleyEquation717OriginalDisplacement
        (wooleyAffinePolynomialSystem phi (p ^ a) xi)
        (wooleyAffinePolynomialSystem phi (p ^ b) eta)
        (p ^ B) R S left right omega j =
      ((wooleyIntegerTupleDisplacement R
          (fun x : ↑left.support =>
            (phi j).eval ((p : ℤ) ^ a * (x : ℤ) + xi)) omega.1 +
        wooleyIntegerTupleDisplacement S
          (fun x : ↑right.support =>
            (phi j).eval ((p : ℤ) ^ b * (x : ℤ) + eta)) omega.2 : ℤ) :
        ZMod (p ^ B)) := by
  simp [wooleyEquation717OriginalDisplacement,
    wooleySourceTuplePolynomialDisplacement, wooleyTupleDisplacement,
    wooleyIntegerTupleDisplacement, wooleyPolynomialValue,
    wooleyAffinePolynomialSystem_eval]

/-- The lower system used in the shifted equation (7.17) is uniform in the
coefficient sequences and in the two moment exponents.  This strengthening
is essential when equation (7.19) subsequently subdivides `c(alpha)` into
all residue classes modulo `p^H'`: one and the same `Psi` must serve every
summand. -/
theorem wooleySection7_exists_uniform_shifted_forcing
    {k r p c a b B nu gamma : ℕ}
    (hpPrime : p.Prime) (hc : 1 ≤ c) (hr : 1 ≤ r)
    (hrk : r < k) (hkp : k < p)
    (hMB : (k - r + 1) * b ≤ B)
    (hgammaK : gamma * k ≤ a)
    (hBPrime : (nu : ℤ) < wooleySection7BPrimeInt k r a b gamma)
    (omegaVal xi eta : ℤ) (homega : omegaVal ≠ 0)
    (hcop : Nat.Coprime p omegaVal.natAbs)
    (hsep : xi - eta = omegaVal * (p : ℤ) ^ gamma)
    (hdiff : xi - eta ≠ 0)
    (phi : WooleyPolynomialSystem k) (hphi : phi.Spaced p c) :
    ∃ Psi : WooleyPolynomialSystem r,
      Psi.Spaced p (a - (k - r) * gamma) ∧
      ∀ {R S : ℕ} (left right : WooleySourceSequence)
        (tuple : WooleySourceMixedTuple R S left right),
        wooleyEquation717OriginalDisplacement
            (wooleyAffinePolynomialSystem phi (p ^ a) xi)
            (wooleyAffinePolynomialSystem phi (p ^ b) eta)
            (p ^ B) R S left right tuple = 0 →
          wooleyEquation717InsertedDisplacement Psi
            (p ^ wooleySection7BPrimeNat k r a b gamma)
            R S left right tuple = 0 := by
  obtain ⟨G, psi, Error, hchange⟩ :=
    hphi.exists_translated_tail_normal_change hc hpPrime.ne_zero eta
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
      (k - r + 1) * b = bp + r * a + (k - r) * gamma := by
        simpa only [bp] using hsum.symm
      _ = gamma * (k - r) + gamma * r + r * (a - gamma) + bp := by
        rw [Nat.mul_comm (k - r) gamma]
        have hgammaR' : gamma * r + r * (a - gamma) = r * a := by
          simpa [Nat.mul_comm] using hgammaR
        omega
  have hgammaM : gamma * k ≤ M := by omega
  have hcommon : r * (a - gamma) ≤ M - gamma * k := by omega
  obtain ⟨Psi, hPsi, huniform⟩ :=
    wooleySection7_top_congruences_exist_lower_system
      hpPrime hc hrk.le hkp hgamma hgammaK hgammaM hcommon
        omegaVal (xi - eta) homega hcop hsep hdiff
        (fun u => psi
          ⟨wooleySection7Node k r u,
            wooleySection7Node_succ_le hrk.le u⟩)
  refine ⟨Psi, hPsi, ?_⟩
  intro R S left right tuple horiginal
  let swapped : WooleySourceMixedTuple R S left right :=
    (tuple.1, (tuple.2.2, tuple.2.1))
  have hdiv : ∀ j : Fin k, (p : ℤ) ^ B ∣
      wooleyIntegerMixedPolynomialDisplacement R S
        (fun x : ↑left.support => (p : ℤ) ^ a * (x : ℤ) + xi)
        (fun x : ↑right.support => (p : ℤ) ^ b * (x : ℤ) + eta)
        swapped.1 swapped.2 (phi j) := by
    intro j
    have hj := congrFun horiginal j
    rw [wooleySection7PositiveDisplacementShifted_eq_intCast
      phi xi eta left right tuple j] at hj
    simp only [Pi.zero_apply] at hj
    have hsumDiv : (p : ℤ) ^ B ∣
        wooleyIntegerTupleDisplacement R
            (fun x : ↑left.support =>
              (phi j).eval ((p : ℤ) ^ a * (x : ℤ) + xi)) tuple.1 +
          wooleyIntegerTupleDisplacement S
            (fun x : ↑right.support =>
              (phi j).eval ((p : ℤ) ^ b * (x : ℤ) + eta)) tuple.2 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hj
      norm_num only [Nat.cast_pow, Nat.cast_ofNat] at hj
      exact hj
    unfold wooleyIntegerMixedPolynomialDisplacement
    dsimp only [swapped]
    rw [wooleyIntegerTupleDisplacement_swap, sub_neg_eq_add]
    exact hsumDiv
  have hdivTranslated : ∀ j : Fin k, (p : ℤ) ^ B ∣
      wooleyIntegerMixedPolynomialDisplacement R S
        (fun x : ↑left.support =>
          (p : ℤ) ^ a * (x : ℤ) + (xi - eta))
        (fun x : ↑right.support => (p : ℤ) ^ b * (x : ℤ))
        swapped.1 swapped.2
        (wooleyAffinePolynomialSystem phi 1 eta j) := by
    intro j
    have hleft :
        (fun x : ↑left.support =>
            (wooleyAffinePolynomialSystem phi 1 eta j).eval
              ((p : ℤ) ^ a * (x : ℤ) + (xi - eta))) =
          (fun x : ↑left.support =>
            (phi j).eval ((p : ℤ) ^ a * (x : ℤ) + xi)) := by
      funext x
      rw [wooleyAffinePolynomialSystem_eval]
      congr 1
      ring
    have hright :
        (fun x : ↑right.support =>
            (wooleyAffinePolynomialSystem phi 1 eta j).eval
              ((p : ℤ) ^ b * (x : ℤ))) =
          (fun x : ↑right.support =>
            (phi j).eval ((p : ℤ) ^ b * (x : ℤ) + eta)) := by
      funext x
      rw [wooleyAffinePolynomialSystem_eval]
      congr 1
      ring
    unfold wooleyIntegerMixedPolynomialDisplacement
    rw [hleft, hright]
    exact hdiv j
  have hnormalDiv : ∀ j : Fin k, (p : ℤ) ^ B ∣
      wooleyIntegerMixedPolynomialDisplacement R S
        (fun x : ↑left.support =>
          (p : ℤ) ^ a * (x : ℤ) + (xi - eta))
        (fun x : ↑right.support => (p : ℤ) ^ b * (x : ℤ))
        swapped.1 swapped.2
        (wooleySection7NormalSystem k p c psi j) := by
    intro j
    exact wooleyTailNormalChange_mixed_displacement_dvd
      (wooleyAffinePolynomialSystem phi 1 eta) G psi Error hchange
      (fun x : ↑left.support =>
        (p : ℤ) ^ a * (x : ℤ) + (xi - eta))
      (fun x : ↑right.support => (p : ℤ) ^ b * (x : ℤ))
      swapped.1 swapped.2 hdivTranslated j
  have htop := wooleySection7_original_implies_top_congruences
    hrk.le hMB psi (xi - eta)
      (fun x : ↑left.support => (x : ℤ))
      (fun x : ↑right.support => (x : ℤ)) swapped.1 swapped.2 hnormalDiv
  have hraw := huniform (fun x : ↑left.support => (x : ℤ)) swapped.1 htop
  funext i
  have hdepth := wooley_section7_common_depth_eq_BPrimeNat
    hrk hgamma hBPrime
  have hdivLow : (p : ℤ) ^ bp ∣
      wooleyIntegerTupleDisplacement R
        (fun x : ↑left.support => (Psi i).eval (x : ℤ)) swapped.1 := by
    have hi := hraw i
    dsimp only [M, bp] at hi hdepth ⊢
    rw [hdepth] at hi
    exact hi
  have hz :
      (wooleyIntegerTupleDisplacement R
        (fun x : ↑left.support => (Psi i).eval (x : ℤ)) swapped.1 :
          ZMod (p ^ bp)) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    norm_num only [Nat.cast_pow, Nat.cast_ofNat]
    exact hdivLow
  rw [wooleyIntegerTupleDisplacement_cast
    (p ^ bp) r R
      (fun x : ↑left.support => fun j => (Psi j).eval (x : ℤ))
      swapped.1 i] at hz
  simpa only [swapped, wooleyEquation717InsertedDisplacement,
    wooleySourceTuplePolynomialDisplacement, wooleyPolynomialValue, bp]
    using hz

/-- Literal source-residue version of equation (7.17), before analytic
normalization.  Both residue representatives occur in the displayed Fourier
systems; `h = xi-eta` is used only inside the congruence extraction. -/
theorem wooley_equation_7_17_shifted_spaced_positive_native
    {k r p c a b B nu R S gamma : ℕ}
    [NeZero (p ^ B)]
    [NeZero (p ^ wooleySection7BPrimeNat k r a b gamma)]
    (hpPrime : p.Prime) (hc : 1 ≤ c) (hr : 1 ≤ r)
    (hrk : r < k) (hkp : k < p)
    (hMB : (k - r + 1) * b ≤ B)
    (hgammaK : gamma * k ≤ a)
    (hBPrime : (nu : ℤ) < wooleySection7BPrimeInt k r a b gamma)
    (omegaVal xi eta : ℤ) (homega : omegaVal ≠ 0)
    (hcop : Nat.Coprime p omegaVal.natAbs)
    (hsep : xi - eta = omegaVal * (p : ℤ) ^ gamma)
    (hdiff : xi - eta ≠ 0)
    (phi : WooleyPolynomialSystem k) (hphi : phi.Spaced p c)
    (left right : WooleySourceSequence) :
    ∃ Psi : WooleyPolynomialSystem r,
      Psi.Spaced p (a - (k - r) * gamma) ∧
      WooleyEquation717FiniteIdentity
        (wooleyAffinePolynomialSystem phi (p ^ a) xi)
        (wooleyAffinePolynomialSystem phi (p ^ b) eta)
        Psi (p ^ B)
        (p ^ wooleySection7BPrimeNat k r a b gamma)
        R S left right := by
  obtain ⟨G, psi, Error, hchange⟩ :=
    hphi.exists_translated_tail_normal_change hc hpPrime.ne_zero eta
  obtain ⟨Psi, hPsi, hnormalForced⟩ :=
    wooleySection7_exists_uniform_equation_7_12
      hpPrime hc hr hrk hkp hMB hgammaK hBPrime
        omegaVal (xi - eta) homega hcop hsep hdiff psi left right
  refine ⟨Psi, hPsi, ?_⟩
  unfold WooleyEquation717FiniteIdentity
  apply wooley_equation_7_17_tuple
  intro tuple horiginal
  let swapped : WooleySourceMixedTuple R S left right :=
    (tuple.1, (tuple.2.2, tuple.2.1))
  have hdiv : ∀ j : Fin k, (p : ℤ) ^ B ∣
      wooleyIntegerMixedPolynomialDisplacement R S
        (fun x : ↑left.support => (p : ℤ) ^ a * (x : ℤ) + xi)
        (fun x : ↑right.support => (p : ℤ) ^ b * (x : ℤ) + eta)
        swapped.1 swapped.2 (phi j) := by
    intro j
    have hj := congrFun horiginal j
    rw [wooleySection7PositiveDisplacementShifted_eq_intCast
      phi xi eta left right tuple j] at hj
    simp only [Pi.zero_apply] at hj
    have hsum : (p : ℤ) ^ B ∣
        wooleyIntegerTupleDisplacement R
            (fun x : ↑left.support =>
              (phi j).eval ((p : ℤ) ^ a * (x : ℤ) + xi)) tuple.1 +
          wooleyIntegerTupleDisplacement S
            (fun x : ↑right.support =>
              (phi j).eval ((p : ℤ) ^ b * (x : ℤ) + eta)) tuple.2 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hj
      norm_num only [Nat.cast_pow, Nat.cast_ofNat] at hj
      exact hj
    unfold wooleyIntegerMixedPolynomialDisplacement
    dsimp only [swapped]
    rw [wooleyIntegerTupleDisplacement_swap, sub_neg_eq_add]
    exact hsum
  have hdivTranslated : ∀ j : Fin k, (p : ℤ) ^ B ∣
      wooleyIntegerMixedPolynomialDisplacement R S
        (fun x : ↑left.support =>
          (p : ℤ) ^ a * (x : ℤ) + (xi - eta))
        (fun x : ↑right.support => (p : ℤ) ^ b * (x : ℤ))
        swapped.1 swapped.2
        (wooleyAffinePolynomialSystem phi 1 eta j) := by
    intro j
    have hleft :
        (fun x : ↑left.support =>
            (wooleyAffinePolynomialSystem phi 1 eta j).eval
              ((p : ℤ) ^ a * (x : ℤ) + (xi - eta))) =
          (fun x : ↑left.support =>
            (phi j).eval ((p : ℤ) ^ a * (x : ℤ) + xi)) := by
      funext x
      rw [wooleyAffinePolynomialSystem_eval]
      congr 1
      ring
    have hright :
        (fun x : ↑right.support =>
            (wooleyAffinePolynomialSystem phi 1 eta j).eval
              ((p : ℤ) ^ b * (x : ℤ))) =
          (fun x : ↑right.support =>
            (phi j).eval ((p : ℤ) ^ b * (x : ℤ) + eta)) := by
      funext x
      rw [wooleyAffinePolynomialSystem_eval]
      congr 1
      ring
    unfold wooleyIntegerMixedPolynomialDisplacement
    rw [hleft, hright]
    exact hdiv j
  have hnormalDiv : ∀ j : Fin k, (p : ℤ) ^ B ∣
      wooleyIntegerMixedPolynomialDisplacement R S
        (fun x : ↑left.support =>
          (p : ℤ) ^ a * (x : ℤ) + (xi - eta))
        (fun x : ↑right.support => (p : ℤ) ^ b * (x : ℤ))
        swapped.1 swapped.2
        (wooleySection7NormalSystem k p c psi j) := by
    intro j
    exact wooleyTailNormalChange_mixed_displacement_dvd
      (wooleyAffinePolynomialSystem phi 1 eta) G psi Error hchange
      (fun x : ↑left.support =>
        (p : ℤ) ^ a * (x : ℤ) + (xi - eta))
      (fun x : ↑right.support => (p : ℤ) ^ b * (x : ℤ))
      swapped.1 swapped.2 hdivTranslated j
  have hnormal : wooleyEquation717OriginalDisplacement
      (wooleySection7LeftFourierSystem k p c a psi (xi - eta))
      (wooleySection7RightFourierSystem k p c b psi)
      (p ^ B) R S left right swapped = 0 := by
    funext j
    rw [wooleySection7OriginalDisplacement_eq_intCast
      psi (xi - eta) left right swapped j]
    simp only [Pi.zero_apply]
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    norm_num only [Nat.cast_pow, Nat.cast_ofNat]
    exact hnormalDiv j
  have hins := hnormalForced swapped hnormal
  simpa only [swapped, wooleyEquation717InsertedDisplacement] using hins

#print axioms wooleySection7PositiveDisplacementShifted_eq_intCast
#print axioms wooleySection7_exists_uniform_shifted_forcing
#print axioms wooley_equation_7_17_shifted_spaced_positive_native

end

end GafniTao
