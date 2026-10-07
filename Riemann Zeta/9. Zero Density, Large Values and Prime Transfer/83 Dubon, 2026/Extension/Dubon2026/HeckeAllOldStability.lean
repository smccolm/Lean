import Dubon2026.HeckeBadDegeneracy
import Dubon2026.HeckeOldNewStability

/-! # Every actual Hecke operator preserves the full classical oldspace -/

namespace Dubon2026

open Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

noncomputable section

/-- Every prime Hecke operator, including bad primes, preserves the entire degeneracy oldspace. -/
theorem cuspOldspace_hecke_prime_all {N p : ℕ} [NeZero N] [NeZero p] {k : ℤ}
    (hp : Nat.Prime p) (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)
    (hf : f ∈ cuspOldspace N k) : cuspHeckeLinear N k p f ∈ cuspOldspace N k := by
  by_cases hgood : p.Coprime N
  · exact cuspOldspace_hecke_prime hp hgood f hf
  have hpN : p ∣ N := not_not.mp (fun hn => hgood (hp.coprime_iff_not_dvd.mpr hn))
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hf
  · rintro g ⟨M, hM, d, hd, u, rfl⟩
    by_cases hpd : p ∣ d.val
    · have hdpos : 0 < d.val / p := Nat.div_pos (Nat.le_of_dvd d.pos hpd) hp.pos
      letI : NeZero (d.val / p) := ⟨hdpos.ne'⟩
      have h' : (d.val / p) * M.val ∣ N :=
        (Nat.mul_dvd_mul_right (Nat.div_dvd_of_dvd hpd) M.val).trans hd
      rw [cuspHeckeLinear_prime_degeneracy_dividing hd h' k hp hpd]
      exact cuspDegeneracyMap_mem_oldspace M.pos hM _ h' u
    · have hcpd := hp.coprime_iff_not_dvd.mpr hpd
      by_cases hpM : p ∣ M.val
      · rw [cuspHeckeLinear_prime_degeneracy_bad_lower hd k hp hcpd hpM]
        exact cuspDegeneracyMap_mem_oldspace M.pos hM _ hd _
      · have hcpM := hp.coprime_iff_not_dvd.mpr hpM
        have h' : (p * d.val) * M.val ∣ N := by
          simpa only [mul_assoc] using
            (hcpd.mul_right hcpM).mul_dvd_of_dvd_of_dvd hpN hd
        rw [cuspHeckeLinear_prime_degeneracy_bad_defect hd h' k hp hcpd hcpM hpN]
        exact (cuspOldspace N k).sub_mem (cuspDegeneracyMap_mem_oldspace M.pos hM _ hd _)
          ((cuspOldspace N k).smul_mem _ (cuspDegeneracyMap_mem_oldspace M.pos hM _ h' u))
  · rw [map_zero]
    exact (cuspOldspace N k).zero_mem
  · intro g h _ _ hg hh
    rw [map_add]
    exact (cuspOldspace N k).add_mem hg hh
  · intro c g _ hg
    rw [map_smul]
    exact (cuspOldspace N k).smul_mem c hg

/-- Every prime-power classical operator preserves the actual full oldspace. -/
theorem cuspOldspace_hecke_primePower_all {N p : ℕ} [NeZero N] [NeZero p] {k : ℤ}
    (hp : Nat.Prime p) (r : ℕ) :
    ∀ f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k, f ∈ cuspOldspace N k →
      cuspHeckeLinear N k (p ^ r) f ∈ cuspOldspace N k := by
  induction r using Nat.twoStepInduction with
  | zero => simpa only [pow_zero, cuspHeckeLinear_one] using (fun f hf => hf)
  | one => simpa only [pow_one] using cuspOldspace_hecke_prime_all hp
  | more r ih0 ih1 =>
    intro f hf
    rw [cuspHeckeLinear_primePower_recurrence N k hp]
    change cuspHeckeLinear N k p (cuspHeckeLinear N k (p ^ (r + 1)) f) -
      heckeDivisorWeight N k p • cuspHeckeLinear N k (p ^ r) f ∈ cuspOldspace N k
    exact (cuspOldspace N k).sub_mem (cuspOldspace_hecke_prime_all hp _ (ih1 f hf))
      ((cuspOldspace N k).smul_mem _ (ih0 f hf))

/-- Every actual classical Hecke endomorphism preserves the full oldspace, without a coprimality restriction. -/
theorem cuspOldspace_hecke_all (N : ℕ) [NeZero N] (k : ℤ) (n : ℕ) :
    ∀ f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k, f ∈ cuspOldspace N k →
      cuspHeckeLinear N k n f ∈ cuspOldspace N k := by
  induction n using Nat.recOnPrimeCoprime with
  | zero =>
    intro f _
    rw [cuspHeckeLinear_zero]
    exact (cuspOldspace N k).zero_mem
  | prime_pow p r hp =>
    haveI : NeZero p := ⟨hp.ne_zero⟩
    exact cuspOldspace_hecke_primePower_all hp r
  | coprime a b ha hb hab iha ihb =>
    intro f hf
    rw [← cuspHeckeLinear_coprime_mul N k (by omega) (by omega) hab]
    exact iha _ (ihb f hf)

end
end Dubon2026
