import Tao2026.VinogradovUniform
import GafniTao.WooleyPadicToCritical
import GafniTao.WooleySourceCriticalBase
import GafniTao.WooleySourceToPadic

/-!
# Exact Wooley coefficient interface

The qualitative native VMVT proof chooses a concentration constant and a
starting p-adic depth.  This file retains those two quantities literally and
computes the exact coefficient they produce at the critical real moment.
-/

namespace Tao2026

noncomputable section

open scoped BigOperators NNReal

/-- A supplied p-adic concentration estimate gives the critical Ford moment
with the exact coefficient `C * (p^(B0+1) * κ)^ε` used in Section 12. -/
theorem critical_fordMomentBound_of_wooleyConcentrationData
    {k p : ℕ} (hk : 1 ≤ k) (hp : p.Prime)
    {ε C : ℝ} (hε : 0 < ε) (hC : 0 < C) (B0 : ℕ)
    (hconcentration : ∀ (Q h : ℕ), 1 ≤ Q → B0 ≤ k * h → Q < p ^ h →
      (GafniTao.wooleyPadicCount
        (GafniTao.fordVinogradovKappa k) k Q p (k * h) : ℝ) ≤
          C * (p ^ (k * h) : ℝ) ^ (ε / (k : ℝ)) *
            (Q : ℝ) ^ GafniTao.fordVinogradovKappa k) :
    GafniTao.FordVinogradovMomentBound
      (GafniTao.fordVinogradovKappa k) k
      (C * ((p ^ (B0 + 1) * GafniTao.fordVinogradovKappa k : ℕ) : ℝ) ^ ε) ε := by
  let s := GafniTao.fordVinogradovKappa k
  let δ := ε / (k : ℝ)
  let D : ℕ := p ^ (B0 + 1) * s
  have hkPos : 0 < k := by omega
  have hkReal : (0 : ℝ) < k := by exact_mod_cast hkPos
  have hδ : 0 < δ := div_pos hε hkReal
  have hsPos : 0 < s := GafniTao.fordVinogradovKappa_pos hk
  have hDPos : 0 < D := by
    dsimp [D]
    exact Nat.mul_pos (pow_pos hp.pos (B0 + 1)) hsPos
  intro Q hQ
  obtain ⟨h, hB, hQph, hnowrap, hphUpper⟩ :=
    GafniTao.exists_wooleyPadicScale hk hp.two_le hQ
  have hmodular := hconcentration Q h hQ hB hQph
  rw [GafniTao.wooleyPadicCount_eq_fordVinogradovMomentNat hQ hnowrap] at hmodular
  have hQPosNat : 0 < Q := by omega
  have hQPos : (0 : ℝ) < Q := by exact_mod_cast hQPosNat
  have hDPosReal : (0 : ℝ) < D := by exact_mod_cast hDPos
  have hphUpperNat : p ^ h ≤ D * Q := by
    simpa [D, s, Nat.mul_assoc] using hphUpper
  have hpowUpperNat : p ^ (k * h) ≤ (D * Q) ^ k := by
    rw [show p ^ (k * h) = (p ^ h) ^ k by rw [← pow_mul, Nat.mul_comm]]
    exact Nat.pow_le_pow_left hphUpperNat k
  have hpowUpperReal :
      ((p ^ (k * h) : ℕ) : ℝ) ≤ ((D * Q : ℕ) : ℝ) ^ k := by
    exact_mod_cast hpowUpperNat
  have hδScale : (k : ℝ) * δ = ε := by
    dsimp [δ]
    field_simp
  have hloss :
      ((p ^ (k * h) : ℕ) : ℝ) ^ δ ≤
        (D : ℝ) ^ ε * (Q : ℝ) ^ ε := by
    calc
      ((p ^ (k * h) : ℕ) : ℝ) ^ δ ≤
          (((D * Q : ℕ) : ℝ) ^ k) ^ δ :=
        Real.rpow_le_rpow (by positivity) hpowUpperReal hδ.le
      _ = (((D : ℝ) * (Q : ℝ)) ^ (k : ℝ)) ^ δ := by
        norm_num [Real.rpow_natCast]
      _ = ((D : ℝ) * (Q : ℝ)) ^ ((k : ℝ) * δ) := by
        rw [Real.rpow_mul (mul_pos hDPosReal hQPos).le]
      _ = ((D : ℝ) * (Q : ℝ)) ^ ε := by rw [hδScale]
      _ = (D : ℝ) ^ ε * (Q : ℝ) ^ ε := by
        rw [Real.mul_rpow hDPosReal.le hQPos.le]
  have hcriticalExponent :
      GafniTao.fordLambda34 (GafniTao.fordVinogradovKappa k) k ε =
        (s : ℝ) + ε := by
    simpa [s] using GafniTao.fordLambda34_critical k ε
  have hmodular' :
      (GafniTao.fordVinogradovMomentNat
        (GafniTao.fordVinogradovKappa k) k Q : ℝ) ≤
        C * ((p ^ (k * h) : ℕ) : ℝ) ^ δ *
          (Q : ℝ) ^ GafniTao.fordVinogradovKappa k := by
    simpa only [δ, Nat.cast_pow] using hmodular
  change (GafniTao.fordVinogradovMomentNat
      (GafniTao.fordVinogradovKappa k) k Q : ℝ) ≤
    (C * (D : ℝ) ^ ε) *
      (Q : ℝ) ^ GafniTao.fordLambda34
        (GafniTao.fordVinogradovKappa k) k ε
  calc
    (GafniTao.fordVinogradovMomentNat
        (GafniTao.fordVinogradovKappa k) k Q : ℝ) ≤
        C * ((p ^ (k * h) : ℕ) : ℝ) ^ δ *
          (Q : ℝ) ^ GafniTao.fordVinogradovKappa k := hmodular'
    _ ≤ C * ((D : ℝ) ^ ε * (Q : ℝ) ^ ε) *
          (Q : ℝ) ^ GafniTao.fordVinogradovKappa k := by
      gcongr
    _ = (C * (D : ℝ) ^ ε) * (Q : ℝ) ^ ((s : ℝ) + ε) := by
      rw [Real.rpow_add hQPos, Real.rpow_natCast]
      dsimp [s]
      ring
    _ = (C * (D : ℝ) ^ ε) *
        (Q : ℝ) ^ GafniTao.fordLambda34
          (GafniTao.fordVinogradovKappa k) k ε := by
      rw [hcriticalExponent]

/-- Exact source-level residual: uniform rooted control of the constant and
starting depth selected by Wooley's p-adic concentration theorem. -/
def WooleyCriticalDataRootCoefficientBoundAt (A : ℝ) : Prop :=
  1 ≤ A ∧ ∀ R : ℕ, 40 ≤ R →
    ∃ (p : ℕ) (C : ℝ) (B0 : ℕ), p.Prime ∧ R < p ∧ 0 < C ∧
      (∀ (Q h : ℕ), 1 ≤ Q → B0 ≤ R * h → Q < p ^ h →
        (GafniTao.wooleyPadicCount
          (GafniTao.fordVinogradovKappa R) R Q p (R * h) : ℝ) ≤
            C * (p ^ (R * h) : ℝ) ^
                ((255 * (R : ℝ) ^ 2 / 197632) / 128 / (R : ℝ)) *
              (Q : ℝ) ^ GafniTao.fordVinogradovKappa R) ∧
      ((C * ((p ^ (B0 + 1) * GafniTao.fordVinogradovKappa R : ℕ) : ℝ) ^
          ((255 * (R : ℝ) ^ 2 / 197632) / 128)) ^ 2 *
        (((3 * GafniTao.fordVinogradovKappa R : ℕ) : ℝ) ^ (2 * R))) ^
          (1 / ((GafniTao.fordVinogradovKappa R *
            (2 * GafniTao.fordVinogradovKappa R) : ℕ) : ℝ)) ≤ A

/-- Rooted control at the p-adic data level is exactly sufficient for the
critical coefficient contract consumed by the bilinear estimate. -/
theorem vinogradovCriticalRootCoefficientBoundAt_of_wooleyData
    {A : ℝ} (hA : WooleyCriticalDataRootCoefficientBoundAt A) :
    VinogradovCriticalRootCoefficientBoundAt A := by
  refine ⟨hA.1, ?_⟩
  intro R hR
  obtain ⟨p, C, B0, hp, hRp, hC, hconcentration, hroot⟩ := hA.2 R hR
  let ε : ℝ := (255 * (R : ℝ) ^ 2 / 197632) / 128
  have hRone : 1 ≤ R := by omega
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  let Ccritical : ℝ :=
    C * ((p ^ (B0 + 1) * GafniTao.fordVinogradovKappa R : ℕ) : ℝ) ^ ε
  have hmoment : GafniTao.FordVinogradovMomentBound
      (GafniTao.fordVinogradovKappa R) R Ccritical ε := by
    dsimp only [Ccritical]
    exact critical_fordMomentBound_of_wooleyConcentrationData
      hRone hp hε hC B0 (by
        intro Q h hQ hB hQph
        simpa only [ε] using hconcentration Q h hQ hB hQph)
  have hCcritical : 0 < Ccritical := by
    dsimp [Ccritical]
    apply mul_pos hC
      (Real.rpow_pos_of_pos (by
        exact_mod_cast Nat.mul_pos (pow_pos hp.pos (B0 + 1))
          (GafniTao.fordVinogradovKappa_pos hRone)) _)
  refine ⟨Ccritical, hCcritical, ?_, ?_⟩
  · intro V hV
    have hlocal := vinogradovMeanValueCount_le_of_fordVinogradovMomentBound
      hmoment V hV
    simpa only [ε, GafniTao.fordLambda34_critical] using hlocal
  · simpa only [Ccritical, ε] using hroot

/-- The native Wooley proof supplies all p-adic data in the preceding
contract; only its uniform rooted inequality is additional. -/
theorem native_wooleyCriticalData_exists
    {R : ℕ} (hR : 40 ≤ R) :
    ∃ (p : ℕ) (C : ℝ) (B0 : ℕ), p.Prime ∧ R < p ∧ 0 < C ∧
      ∀ (Q h : ℕ), 1 ≤ Q → B0 ≤ R * h → Q < p ^ h →
        (GafniTao.wooleyPadicCount
          (GafniTao.fordVinogradovKappa R) R Q p (R * h) : ℝ) ≤
            C * (p ^ (R * h) : ℝ) ^
                ((255 * (R : ℝ) ^ 2 / 197632) / 128 / (R : ℝ)) *
              (Q : ℝ) ^ GafniTao.fordVinogradovKappa R := by
  obtain ⟨p, hp, hRp⟩ := GafniTao.exists_prime_strictly_above R
  let hnative : GafniTao.WooleyMonomialPadicConcentration :=
    GafniTao.wooleyMonomialPadicConcentration_of_polynomialCorollary32
      GafniTao.wooleyPolynomialCorollary32_native
  have hδ : 0 < (255 * (R : ℝ) ^ 2 / 197632) / 128 / (R : ℝ) := by
    positivity
  obtain ⟨C, hC, B0, hbound⟩ := hnative.specialize hp hRp hδ
  exact ⟨p, C, B0, hp, hRp, hC, hbound⟩

end

end Tao2026
