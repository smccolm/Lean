import Dubon2026.BadPrimeDilationArithmetic

/-! # Genuine bad-prime Hecke action on every oldspace degeneracy generator -/

namespace Dubon2026

open Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

noncomputable section

/-- When the bad prime divides the dilation, the actual Hecke operator removes one copy of it. -/
theorem cuspHeckeLinear_prime_degeneracy_dividing {M N p d : ℕ}
    [NeZero M] [NeZero N] [NeZero p] [NeZero d] [NeZero (d / p)]
    (h : d * M ∣ N) (h' : (d / p) * M ∣ N) (k : ℤ) (hp : Nat.Prime p) (hpd : p ∣ d)
    (f : CuspForm ((Gamma0 M).map (mapGL ℝ)) k) :
    cuspHeckeLinear N k p (cuspDegeneracyMap d h k f) = cuspDegeneracyMap (d / p) h' k f := by
  have hpN : ¬ Nat.Coprime p N := by
    rw [hp.coprime_iff_not_dvd, not_not]
    exact (hpd.trans (dvd_mul_right d M)).trans h
  apply cuspCoefficients_injective N k
  funext m
  change cuspCoefficients (cuspHecke p (cuspDegeneracyMap d h k f)) m = _
  simp only [cuspHecke_coeff, classicalHeckeCoefficient_prime _ _ hp,
    cuspDegeneracyMap_coeff, hpN, false_and, if_false, add_zero]
  exact primeCoefficient_dilation_divide hp.pos hpd (cuspCoefficients f) m

/-- A bad prime coprime to the dilation and already dividing the lower level commutes with dilation. -/
theorem cuspHeckeLinear_prime_degeneracy_bad_lower {M N p d : ℕ}
    [NeZero M] [NeZero N] [NeZero p] [NeZero d]
    (h : d * M ∣ N) (k : ℤ) (hp : Nat.Prime p) (hpd : p.Coprime d) (hpM : p ∣ M)
    (f : CuspForm ((Gamma0 M).map (mapGL ℝ)) k) :
    cuspHeckeLinear N k p (cuspDegeneracyMap d h k f) =
      cuspDegeneracyMap d h k (cuspHeckeLinear M k p f) := by
  have hnM : ¬ Nat.Coprime p M := fun hc => hp.coprime_iff_not_dvd.mp hc hpM
  have hnN : ¬ Nat.Coprime p N := fun hc =>
    hp.coprime_iff_not_dvd.mp hc ((hpM.trans (dvd_mul_left M d)).trans h)
  apply cuspCoefficients_injective N k
  funext m
  change cuspCoefficients (cuspHecke p (cuspDegeneracyMap d h k f)) m =
    cuspCoefficients (cuspDegeneracyMap d h k (cuspHecke p f)) m
  simp only [cuspHecke_coeff, classicalHeckeCoefficient_prime _ _ hp,
    cuspDegeneracyMap_coeff, hnN, hnM, false_and, if_false, add_zero]
  simpa only [zero_mul, ite_self, add_zero] using
    primeCoefficient_dilation hp.pos (Nat.pos_of_neZero d) hpd (cuspCoefficients f) 0 m

/-- When a prime becomes bad only at the upper level, the exact degeneracy commutation defect
is the classical extra dilation with coefficient p^(k-1). -/
theorem cuspHeckeLinear_prime_degeneracy_bad_defect {M N p d : ℕ}
    [NeZero M] [NeZero N] [NeZero p] [NeZero d]
    (h : d * M ∣ N) (h' : (p * d) * M ∣ N) (k : ℤ) (hp : Nat.Prime p)
    (hpd : p.Coprime d) (hpM : p.Coprime M) (hpN : p ∣ N)
    (f : CuspForm ((Gamma0 M).map (mapGL ℝ)) k) :
    cuspHeckeLinear N k p (cuspDegeneracyMap d h k f) =
      cuspDegeneracyMap d h k (cuspHeckeLinear M k p f) -
        (p : ℂ) ^ (k - 1) • cuspDegeneracyMap (p * d) h' k f := by
  have hnN : ¬ Nat.Coprime p N := fun hc => hp.coprime_iff_not_dvd.mp hc hpN
  apply cuspCoefficients_injective N k
  funext m
  change cuspCoefficients (cuspHecke p (cuspDegeneracyMap d h k f)) m =
    cuspCoefficientLinear N k m (cuspDegeneracyMap d h k (cuspHecke p f) -
      (p : ℂ) ^ (k - 1) • cuspDegeneracyMap (p * d) h' k f)
  rw [map_sub, map_smul]
  change cuspCoefficients (cuspHecke p (cuspDegeneracyMap d h k f)) m =
    cuspCoefficients (cuspDegeneracyMap d h k (cuspHecke p f)) m -
      (p : ℂ) ^ (k - 1) * cuspCoefficients (cuspDegeneracyMap (p * d) h' k f) m
  simp only [cuspHecke_coeff, classicalHeckeCoefficient_prime _ _ hp,
    cuspDegeneracyMap_coeff, hnN, false_and, if_false, add_zero, and_iff_right hpM]
  simpa only [zero_mul, ite_self, add_zero, zero_sub, neg_mul, ← sub_eq_add_neg] using
    primeCoefficient_dilation_defect hp.pos (Nat.pos_of_neZero d) hpd
      (cuspCoefficients f) 0 ((p : ℂ) ^ (k - 1)) m

end
end Dubon2026
