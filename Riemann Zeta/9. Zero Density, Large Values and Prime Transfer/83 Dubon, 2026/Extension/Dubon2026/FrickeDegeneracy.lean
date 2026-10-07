import Dubon2026.FrickeCusp
import Dubon2026.CuspPrimeDepletion

/-! # Fricke transport of the actual lower-level degeneracy maps -/

namespace Dubon2026

open Matrix.SpecialLinearGroup CongruenceSubgroup UpperHalfPlane
open scoped MatrixGroups ModularForm

noncomputable section

/-- Exact upper-half-plane identity exchanging the complementary degeneracy factors. -/
theorem fricke_degeneracy_point {M N : ℕ} [NeZero M] [NeZero N]
    (d e : ℕ) [NeZero d] [NeZero e] (hN : N = d * e * M) (τ : ℍ) :
    levelRaiseMatrix d • (frickeMatrix N • τ) =
      frickeMatrix M • (levelRaiseMatrix e • τ) := by
  apply UpperHalfPlane.ext
  simp only [coe_levelRaiseMatrix_smul, frickeMatrix_smul, hN, Nat.cast_mul]
  field_simp [Nat.cast_ne_zero.mpr (NeZero.ne d), Nat.cast_ne_zero.mpr (NeZero.ne e),
    Nat.cast_ne_zero.mpr (NeZero.ne M), τ.ne_zero]

/-- Fricke exchanges the genuine complementary degeneracy maps, with their exact scalar. -/
theorem cuspFricke_degeneracy {M N : ℕ} [NeZero M] [NeZero N]
    (d e : ℕ) [NeZero d] [NeZero e] (hN : N = d * e * M) (k : ℤ)
    (f : CuspForm ((Gamma0 M).map (mapGL ℝ)) k) :
    cuspFricke N k (cuspDegeneracyMap d (by rw [hN]; exact ⟨e, by ring⟩) k f) =
      ((e : ℂ) ^ (k - 1) * (d : ℂ)⁻¹) •
        cuspDegeneracyMap e (by rw [hN]; exact ⟨d, by ring⟩) k (cuspFricke M k f) := by
  ext τ
  simp only [cuspFricke_apply, fricke_slash_apply, cuspDegeneracyMap_apply,
    CuspForm.IsGLPos.smul_apply, smul_eq_mul, coe_levelRaiseMatrix_smul,
    fricke_degeneracy_point d e hN, mul_zpow]
  have he : (e : ℂ) ^ (k - 1) * (e : ℂ) ^ (-k) = (e : ℂ)⁻¹ := by
    rw [← zpow_add₀ (Nat.cast_ne_zero.mpr (NeZero.ne e)),
      show k - 1 + -k = (-1 : ℤ) by omega, zpow_neg_one]
  calc
    _ = ((e : ℂ)⁻¹ * (d : ℂ)⁻¹ * (M : ℂ)⁻¹) * (τ : ℂ) ^ (-k) *
        f (frickeMatrix M • (levelRaiseMatrix e • τ)) := by
      rw [hN, Nat.cast_mul, Nat.cast_mul, mul_inv_rev, mul_inv_rev]
      ring
    _ = _ := by rw [← he]; ring

/-- The first Fricke coefficient of a degeneracy term is supported only on complementary factor one. -/
theorem cuspFricke_degeneracy_coeff_one {M N : ℕ} [NeZero M] [NeZero N]
    (d e : ℕ) [NeZero d] [NeZero e] (hN : N = d * e * M) (k : ℤ)
    (f : CuspForm ((Gamma0 M).map (mapGL ℝ)) k) :
    cuspCoefficients
        (cuspFricke N k (cuspDegeneracyMap d (by rw [hN]; exact ⟨e, by ring⟩) k f)) 1 =
      if e = 1 then (d : ℂ)⁻¹ * cuspCoefficients (cuspFricke M k f) 1 else 0 := by
  rw [cuspFricke_degeneracy d e hN]
  change cuspCoefficientLinear N k 1 (_ • _) = _
  rw [map_smul]
  change _ * cuspCoefficients (cuspDegeneracyMap e _ k _) 1 = _
  rw [cuspDegeneracyMap_coeff]
  by_cases he : e = 1
  · simp [he]
  · simp [he, Nat.dvd_one]

/-- Prime depletion multiplies the first Fricke coefficient by exactly p^(k-3). -/
theorem cuspFricke_primeDepletion_coeff_one {M p : ℕ} [NeZero M] [NeZero p]
    (hp : Nat.Prime p) (k : ℤ) (eigenvalue : ℂ)
    (f : CuspForm ((Gamma0 M).map (mapGL ℝ)) k) :
    cuspCoefficients (cuspFricke (p * (p * M)) k (cuspPrimeDepletion (p := p) k eigenvalue f)) 1 =
      (p : ℂ) ^ (k - 3) * cuspCoefficients (cuspFricke M k f) 1 := by
  change cuspCoefficientLinear (p * (p * M)) k 1
    (cuspFricke (p * (p * M)) k (cuspPrimeDepletion (p := p) k eigenvalue f)) = _
  simp only [cuspPrimeDepletion, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, map_add, map_sub, map_smul]
  change cuspCoefficients (cuspFricke _ k (cuspDegeneracyMap 1 _ k f)) 1 -
    eigenvalue * cuspCoefficients (cuspFricke _ k (cuspDegeneracyMap p _ k f)) 1 +
    (p : ℂ) ^ (k - 1) *
      cuspCoefficients (cuspFricke _ k (cuspDegeneracyMap (p * p) _ k f)) 1 = _
  rw [cuspFricke_degeneracy_coeff_one 1 (p * p) (by ring),
    cuspFricke_degeneracy_coeff_one p p (by ring),
    cuspFricke_degeneracy_coeff_one (p * p) 1 (by ring)]
  have hpp : p * p ≠ 1 := by nlinarith [hp.two_le]
  simp only [if_neg hpp, if_neg hp.ne_one, if_true, mul_zero, sub_zero, zero_add]
  rw [Nat.cast_mul, mul_inv_rev, ← mul_assoc, ← mul_assoc, ← zpow_neg_one,
    ← zpow_add₀ (Nat.cast_ne_zero.mpr hp.ne_zero),
    ← zpow_add₀ (Nat.cast_ne_zero.mpr hp.ne_zero)]
  congr 2
  omega

end
end Dubon2026
