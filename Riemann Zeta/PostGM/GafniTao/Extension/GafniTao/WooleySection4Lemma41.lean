import GafniTao.WooleySection4Arithmetic
import GafniTao.WooleyExponent

/-!
# Wooley Lemma 4.1

This file assembles equations (4.2), (4.12), (4.13), and (4.14) into the
source conditioning estimate.  The public theorem is eventual in `B`, as in
the paper, and its proof uses the operational critical exponent rather than
an externally supplied estimate.
-/

open Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

/-- The local progression estimate underlying Lemma 4.1.  This theorem keeps
the uniform critical-exponent estimate explicit so that its finite sum
assembly can be audited independently. -/
theorem wooleySourcePolynomial_lemma_4_1_local
    {k p c B h H : ℕ} [NeZero p]
    (hpPrime : p.Prime) (hk : 1 ≤ k) (hc : 1 ≤ c)
    (hkhB : k * h ≤ B) (hH : H = B ⌈/⌉ k)
    {tau Lambda C : ℝ} {Bcrit : ℕ}
    (htau : 0 < tau)
    (huniform : ∀ (B' : ℕ) (Psi : WooleyPolynomialSystem k)
        (gamma' : WooleySourceSequence),
      Bcrit ≤ B' → Psi.InPhiTau p B' tau → gamma'.Admissible →
        wooleySourcePolynomialMean (wooleyTriangular k) (p ^ B')
            Psi gamma' ≤
          C * (((p ^ (B' ⌈/⌉ k) : ℕ) : ℝ) ^ Lambda) *
            wooleySourcePolynomialConditionedMean
              (wooleyTriangular k) (p ^ B')
                (p ^ (B' ⌈/⌉ k)) Psi gamma')
    (hBcrit : Bcrit ≤ B - k * h)
    (phi : WooleyPolynomialSystem k) (hphi : phi.Spaced p c)
    (hphiScale : tau * B ≤ c)
    (gamma : WooleySourceSequence) (hgamma : gamma.Admissible)
    (xi : ZMod (p ^ h)) :
    wooleySourcePolynomialMean (wooleyTriangular k) (p ^ B)
        (wooleyAffinePolynomialSystem phi (p ^ h) xi.val)
        (wooleyAffinePullback gamma (p ^ h) (pow_pos hpPrime.pos h) xi.val) ≤
      C * (((p ^ (H - h) : ℕ) : ℝ) ^ Lambda) *
        wooleySourcePolynomialConditionedMean (wooleyTriangular k) (p ^ B)
          (p ^ (H - h))
          (wooleyAffinePolynomialSystem phi (p ^ h) xi.val)
          (wooleyAffinePullback gamma (p ^ h) (pow_pos hpPrime.pos h)
            xi.val) := by
  let theta := wooleyAffinePolynomialSystem phi (p ^ h) xi.val
  let gammaXi := wooleyAffinePullback gamma (p ^ h) (pow_pos hpPrime.pos h)
    xi.val
  let B' := B - k * h
  have hs : 1 ≤ wooleyTriangular k := by
    unfold wooleyTriangular
    have hkpos : 0 < k := by omega
    have htwo : 2 ≤ k * (k + 1) := by nlinarith
    omega
  obtain ⟨Psi, hPsi, h412⟩ := wooleySourcePolynomial_equation_4_12
    hpPrime hc hkhB hs phi hphi xi.val
  have hPsiPhi : Psi.InPhiTau p B' tau := by
    refine ⟨c + h, hPsi, ?_⟩
    dsimp [B']
    rw [Nat.cast_sub hkhB]
    have hkhNonneg : (0 : ℝ) ≤ k * h := by positivity
    have hhNonneg : (0 : ℝ) ≤ h := by positivity
    push_cast at hphiScale ⊢
    nlinarith
  have hgammaXi : gammaXi.Admissible := by
    exact hgamma.affinePullback (p ^ h) (pow_pos hpPrime.pos h) xi.val
  have hterm (alpha : Fin k → ZMod (p ^ B)) :
      wooleySourcePolynomialMean (wooleyTriangular k) (p ^ B') Psi
          (wooleySourceTwist gammaXi
            (fun n => wooleySourcePolynomialPhase theta alpha n)) ≤
        C * (((p ^ (B' ⌈/⌉ k) : ℕ) : ℝ) ^ Lambda) *
          wooleySourcePolynomialConditionedMean (wooleyTriangular k)
            (p ^ B') (p ^ (B' ⌈/⌉ k)) Psi
            (wooleySourceTwist gammaXi
              (fun n => wooleySourcePolynomialPhase theta alpha n)) := by
    apply huniform B' Psi _ hBcrit hPsiPhi
    exact hgammaXi.twist _ (fun n => by
      rw [wooleySourcePolynomialPhase_norm])
  have hsum := Finset.sum_le_sum (fun alpha (_ : alpha ∈
      (Finset.univ : Finset (Fin k → ZMod (p ^ B)))) => hterm alpha)
  have hceil : B' ⌈/⌉ k = H - h := by
    dsimp [B']
    rw [wooley_ceilDiv_sub_mul hk hkhB, ← hH]
  have hconditioned :=
    wooleySection4_conditionedInsertedAverage_eq_of_equation_4_12
      (B := B) (h := h) (H := H) (s := wooleyTriangular k)
      theta Psi (by simpa only [theta, B', gammaXi] using h412)
      gammaXi
  calc
    wooleySourcePolynomialMean (wooleyTriangular k) (p ^ B) theta gammaXi =
        ((((p ^ B) ^ k : ℕ) : ℝ)⁻¹) *
          ∑ alpha : Fin k → ZMod (p ^ B),
            wooleySourcePolynomialMean (wooleyTriangular k) (p ^ B') Psi
              (wooleySourceTwist gammaXi
                (fun n => wooleySourcePolynomialPhase theta alpha n)) := by
      simpa only [theta, gammaXi, B'] using h412 gammaXi
    _ ≤ ((((p ^ B) ^ k : ℕ) : ℝ)⁻¹) *
          ∑ alpha : Fin k → ZMod (p ^ B),
            C * (((p ^ (B' ⌈/⌉ k) : ℕ) : ℝ) ^ Lambda) *
              wooleySourcePolynomialConditionedMean (wooleyTriangular k)
                (p ^ B') (p ^ (B' ⌈/⌉ k)) Psi
                (wooleySourceTwist gammaXi
                  (fun n => wooleySourcePolynomialPhase theta alpha n)) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = C * (((p ^ (H - h) : ℕ) : ℝ) ^ Lambda) *
        wooleySection4ConditionedInsertedAverage theta Psi
          (p ^ B) (p ^ B') (p ^ (H - h)) (wooleyTriangular k) gammaXi := by
      rw [hceil]
      unfold wooleySection4ConditionedInsertedAverage
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro alpha halpha
      ring
    _ = C * (((p ^ (H - h) : ℕ) : ℝ) ^ Lambda) *
        wooleySourcePolynomialConditionedMean (wooleyTriangular k) (p ^ B)
          (p ^ (H - h)) theta gammaXi := by rw [hconditioned]

/-- Source Lemma 4.1 at the critical value `s=k(k+1)/2`. -/
theorem wooleySourcePolynomial_lemma_4_1
    {k p : ℕ} [NeZero p]
    (hpPrime : p.Prime) (hk : 1 ≤ k) (hkp : k < p)
    {tau epsilon delta : ℝ}
    (hepsilon : 0 < epsilon)
    (hepsilonTau : epsilon < tau) (htauDelta : tau < delta)
    (hdeltaOne : delta < 1) :
    ∃ C : ℝ, 0 < C ∧ ∃ B0 : ℕ,
      ∀ (B : ℕ) (phi : WooleyPolynomialSystem k)
        (gamma : WooleySourceSequence) (h : ℕ),
        B0 ≤ B → phi.InPhiTau p B tau → gamma.Admissible →
        (h : ℝ) ≤ (1 - delta) * (B ⌈/⌉ k : ℕ) →
          wooleySourcePolynomialConditionedMean (wooleyTriangular k)
              (p ^ B) (p ^ h) phi gamma ≤
            C * (((p ^ (B ⌈/⌉ k - h) : ℕ) : ℝ) ^
                (wooleyCriticalExponent k p + epsilon)) *
              wooleySourcePolynomialConditionedMean (wooleyTriangular k)
                (p ^ B) (p ^ (B ⌈/⌉ k)) phi gamma := by
  have htau : 0 < tau := lt_trans hepsilon hepsilonTau
  have hpPositive : 0 < p := by omega
  have hcritical := wooley_uniformExponentBound_above_critical
    (k := k) (p := p) hk
    (Lambda := wooleyCriticalExponent k p + epsilon)
    (show wooleyCriticalExponent k p <
        wooleyCriticalExponent k p + epsilon by linarith)
  obtain ⟨C, hC, Bcrit, huniform⟩ := hcritical tau htau
  obtain ⟨N₁ : ℕ, hN₁⟩ := exists_nat_ge (1 / tau)
  obtain ⟨N₂ : ℕ, hN₂⟩ :=
    exists_nat_ge (((Bcrit + k : ℕ) : ℝ) / delta)
  refine ⟨C, hC, max N₁ N₂, ?_⟩
  intro B phi gamma h hB hphi hgamma hh
  have hBN₁ : N₁ ≤ B := le_trans (le_max_left _ _) hB
  have hBN₂ : N₂ ≤ B := le_trans (le_max_right _ _) hB
  have htauB : (1 : ℝ) ≤ tau * B := by
    have hN₁B : (N₁ : ℝ) ≤ B := by exact_mod_cast hBN₁
    have htauNonzero : tau ≠ 0 := ne_of_gt htau
    have : 1 / tau ≤ (B : ℝ) := hN₁.trans hN₁B
    rw [div_le_iff₀ htau] at this
    simpa only [one_mul, mul_comm] using this
  have hdeltaB : ((Bcrit + k : ℕ) : ℝ) ≤ delta * B := by
    have hN₂B : (N₂ : ℝ) ≤ B := by exact_mod_cast hBN₂
    have : ((Bcrit + k : ℕ) : ℝ) / delta ≤ (B : ℝ) :=
      hN₂.trans hN₂B
    rw [div_le_iff₀ (lt_trans htau htauDelta)] at this
    simpa only [mul_comm] using this
  have hlarge : (k : ℝ) ≤ delta * B := by
    have : (k : ℝ) ≤ (Bcrit + k : ℕ) := by
      exact_mod_cast (Nat.le_add_left k Bcrit)
    exact this.trans hdeltaB
  obtain ⟨hkhB, hmargin⟩ := wooley_section4_depth_margin
    hk (lt_trans htau htauDelta) hdeltaOne hh hlarge
  have hBcrit : Bcrit ≤ B - k * h := by
    have hBcritReal : (Bcrit : ℝ) ≤ delta * B - k := by
      push_cast at hdeltaB ⊢
      nlinarith
    exact_mod_cast hBcritReal.trans hmargin
  obtain ⟨c, hphiSpaced, hphiScale⟩ := hphi
  have hc : 1 ≤ c := by
    have : (1 : ℝ) ≤ c := htauB.trans hphiScale
    exact_mod_cast this
  by_cases hmass : wooleySourceMassSq gamma = 0
  · simp [wooleySourcePolynomialConditionedMean, hmass]
  · have hH : h ≤ B ⌈/⌉ k := by
      have hH0 : (0 : ℝ) ≤ (B ⌈/⌉ k : ℕ) := by positivity
      have hdeltaPos : 0 < delta := lt_trans htau htauDelta
      have : (h : ℝ) ≤ (B ⌈/⌉ k : ℕ) := by nlinarith
      exact_mod_cast this
    have hlocal (xi : ZMod (p ^ h)) :=
      wooleySourcePolynomial_lemma_4_1_local hpPrime hk hc hkhB rfl
        htau huniform hBcrit phi hphiSpaced hphiScale gamma hgamma xi
    have hsum := Finset.sum_le_sum (fun xi (_ : xi ∈
        (Finset.univ : Finset (ZMod (p ^ h)))) =>
      mul_le_mul_of_nonneg_left (hlocal xi)
        (wooleySourceResidueMassSq_nonneg gamma (p ^ h) xi))
    have hleft := wooleySourceMassSq_mul_conditionedMean_eq_affineSum
      (s := wooleyTriangular k) (q := p ^ B) (q₁ := p ^ h) phi gamma
    have hright := wooleySourcePolynomialConditionedMean_power_tower
      (s := wooleyTriangular k) (q := p ^ B) (p := p) hH phi gamma
    have hmul : wooleySourceMassSq gamma *
        wooleySourcePolynomialConditionedMean (wooleyTriangular k)
          (p ^ B) (p ^ h) phi gamma ≤
      wooleySourceMassSq gamma *
        (C * (((p ^ (B ⌈/⌉ k - h) : ℕ) : ℝ) ^
            (wooleyCriticalExponent k p + epsilon)) *
          wooleySourcePolynomialConditionedMean (wooleyTriangular k)
            (p ^ B) (p ^ (B ⌈/⌉ k)) phi gamma) := by
      rw [hleft]
      calc
        ∑ xi : ZMod (p ^ h),
            wooleySourceResidueMassSq gamma (p ^ h) xi *
              wooleySourcePolynomialMean (wooleyTriangular k) (p ^ B)
                (wooleyAffinePolynomialSystem phi (p ^ h) xi.val)
                (wooleyAffinePullback gamma (p ^ h)
                  (pow_pos hpPositive h) xi.val) ≤
          ∑ xi : ZMod (p ^ h),
            wooleySourceResidueMassSq gamma (p ^ h) xi *
              (C * (((p ^ (B ⌈/⌉ k - h) : ℕ) : ℝ) ^
                  (wooleyCriticalExponent k p + epsilon)) *
                wooleySourcePolynomialConditionedMean (wooleyTriangular k)
                  (p ^ B) (p ^ (B ⌈/⌉ k - h))
                  (wooleyAffinePolynomialSystem phi (p ^ h) xi.val)
                  (wooleyAffinePullback gamma (p ^ h)
                    (pow_pos hpPositive h) xi.val)) := hsum
        _ = C * (((p ^ (B ⌈/⌉ k - h) : ℕ) : ℝ) ^
              (wooleyCriticalExponent k p + epsilon)) *
            (∑ xi : ZMod (p ^ h),
              wooleySourceResidueMassSq gamma (p ^ h) xi *
                wooleySourcePolynomialConditionedMean (wooleyTriangular k)
                  (p ^ B) (p ^ (B ⌈/⌉ k - h))
                  (wooleyAffinePolynomialSystem phi (p ^ h) xi.val)
                  (wooleyAffinePullback gamma (p ^ h)
                    (pow_pos hpPositive h) xi.val)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro xi hxi
          ring
        _ = C * (((p ^ (B ⌈/⌉ k - h) : ℕ) : ℝ) ^
              (wooleyCriticalExponent k p + epsilon)) *
            (wooleySourceMassSq gamma *
              wooleySourcePolynomialConditionedMean (wooleyTriangular k)
                (p ^ B) (p ^ (B ⌈/⌉ k)) phi gamma) := by
          rw [hright]
        _ = wooleySourceMassSq gamma *
            (C * (((p ^ (B ⌈/⌉ k - h) : ℕ) : ℝ) ^
                (wooleyCriticalExponent k p + epsilon)) *
              wooleySourcePolynomialConditionedMean (wooleyTriangular k)
                (p ^ B) (p ^ (B ⌈/⌉ k)) phi gamma) := by ring
    exact le_of_mul_le_mul_left hmul
      (lt_of_le_of_ne (wooleySourceMassSq_nonneg gamma) (Ne.symm hmass))

#print axioms wooleySourcePolynomial_lemma_4_1_local
#print axioms wooleySourcePolynomial_lemma_4_1

end

end GafniTao
