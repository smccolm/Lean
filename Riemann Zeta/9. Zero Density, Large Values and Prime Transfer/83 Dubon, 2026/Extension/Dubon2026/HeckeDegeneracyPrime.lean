import Dubon2026.HeckeAllIndices

/-! # Good-prime Hecke operators commute with the genuine degeneracy maps -/

namespace Dubon2026

open Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

noncomputable section

/-- The actual two-term prime coefficient transform commutes with a coprime sparse dilation. -/
theorem primeCoefficient_dilation {p d : ℕ} (hp : 0 < p) (hd : 0 < d) (hpd : Nat.Coprime p d)
    (a : ℕ → ℂ) (w : ℂ) (m : ℕ) :
    (if d ∣ p * m then a (p * m / d) else 0) +
        (if p ∣ m then w * (if d ∣ m / p then a (m / p / d) else 0) else 0) =
      if d ∣ m then a (p * (m / d)) +
        (if p ∣ m / d then w * a (m / d / p) else 0) else 0 := by
  by_cases hdm : d ∣ m
  · obtain ⟨t, rfl⟩ := hdm
    have hfirst : p * (d * t) / d = p * t := by
      rw [mul_left_comm, Nat.mul_div_cancel_left _ hd]
    rw [if_pos (dvd_mul_of_dvd_right (dvd_mul_right d t) p), hfirst,
      if_pos (dvd_mul_right d t), Nat.mul_div_cancel_left _ hd]
    by_cases hpt : p ∣ t
    · obtain ⟨u, rfl⟩ := hpt
      have hdiv : d * (p * u) / p = d * u := by
        rw [← mul_assoc, mul_comm d p, mul_assoc, Nat.mul_div_cancel_left _ hp]
      rw [if_pos (dvd_mul_of_dvd_right (dvd_mul_right p u) d), hdiv,
        if_pos (dvd_mul_right d u), Nat.mul_div_cancel_left _ hd,
        if_pos (dvd_mul_right p u)]
      congr 2
      exact congrArg a (Nat.mul_div_cancel_left u hp).symm
    · have hpdt : ¬p ∣ d * t := fun h => hpt (hpd.dvd_mul_left.mp h)
      rw [if_neg hpdt, if_neg hpt]
  · have hdpm : ¬d ∣ p * m := fun h => hdm (hpd.symm.dvd_mul_left.mp h)
    rw [if_neg hdm, if_neg hdpm, zero_add]
    by_cases hpm : p ∣ m
    · rw [if_pos hpm]
      have hnd : ¬d ∣ m / p := fun h => hdm (h.trans (Nat.div_dvd_of_dvd hpm))
      rw [if_neg hnd, mul_zero]
    · rw [if_neg hpm]

/-- A good-prime classical operator commutes with every genuine lower-level degeneracy map. -/
theorem cuspHeckeLinear_prime_degeneracy {M N p : ℕ} [NeZero M] [NeZero N] [NeZero p]
    (d : ℕ) [NeZero d] (h : d * M ∣ N) (k : ℤ) (hp : Nat.Prime p)
    (hpN : Nat.Coprime p N) (f : CuspForm ((Gamma0 M).map (mapGL ℝ)) k) :
    cuspHeckeLinear N k p (cuspDegeneracyMap d h k f) =
      cuspDegeneracyMap d h k (cuspHeckeLinear M k p f) := by
  have hpd : Nat.Coprime p d := hpN.of_dvd_right ((dvd_mul_right d M).trans h)
  have hpM : Nat.Coprime p M := hpN.of_dvd_right ((dvd_mul_left M d).trans h)
  apply cuspCoefficients_injective N k
  funext m
  change cuspCoefficients (cuspHecke p (cuspDegeneracyMap d h k f)) m =
    cuspCoefficients (cuspDegeneracyMap d h k (cuspHecke p f)) m
  simp only [cuspHecke_coeff, classicalHeckeCoefficient_prime _ _ hp,
    cuspDegeneracyMap_coeff]
  simp only [and_iff_right hpN, and_iff_right hpM]
  exact primeCoefficient_dilation hp.pos (Nat.pos_of_neZero d) hpd (cuspCoefficients f) ((p : ℂ) ^ (k - 1)) m

end
end Dubon2026
