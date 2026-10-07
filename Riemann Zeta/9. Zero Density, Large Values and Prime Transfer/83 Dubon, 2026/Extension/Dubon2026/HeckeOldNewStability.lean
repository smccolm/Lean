import Dubon2026.HeckeDegeneracyPrime
import Dubon2026.HeckeGoodAdjoint

/-! # Good-index Hecke stability of the full actual oldspace and newspace -/

namespace Dubon2026

open Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

noncomputable section

/-- A good-prime actual Hecke operator preserves the full oldspace, including d=1 generators. -/
theorem cuspOldspace_hecke_prime {N p : ℕ} [NeZero N] [NeZero p] {k : ℤ}
    (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (hf : f ∈ cuspOldspace N k) :
    cuspHeckeLinear N k p f ∈ cuspOldspace N k := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hf
  · rintro g ⟨M, hM, d, hd, u, rfl⟩
    rw [cuspHeckeLinear_prime_degeneracy d hd k hp hpN]
    exact cuspDegeneracyMap_mem_oldspace M.pos hM d hd _
  · rw [map_zero]
    exact (cuspOldspace N k).zero_mem
  · intro g h _ _ hg hh
    rw [map_add]
    exact (cuspOldspace N k).add_mem hg hh
  · intro c g _ hg
    rw [map_smul]
    exact (cuspOldspace N k).smul_mem c hg

/-- Every good prime-power operator preserves the genuine full oldspace. -/
theorem cuspOldspace_hecke_primePower {N p : ℕ} [NeZero N] [NeZero p] {k : ℤ}
    (hp : Nat.Prime p) (hpN : Nat.Coprime p N) (r : ℕ) :
    ∀ f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k, f ∈ cuspOldspace N k →
      cuspHeckeLinear N k (p ^ r) f ∈ cuspOldspace N k := by
  induction r using Nat.twoStepInduction with
  | zero => simpa only [pow_zero, cuspHeckeLinear_one] using (fun f hf => hf)
  | one => simpa only [pow_one] using cuspOldspace_hecke_prime hp hpN
  | more r ih0 ih1 =>
    intro f hf
    rw [cuspHeckeLinear_primePower_recurrence N k hp]
    change cuspHeckeLinear N k p (cuspHeckeLinear N k (p ^ (r + 1)) f) -
      heckeDivisorWeight N k p • cuspHeckeLinear N k (p ^ r) f ∈ cuspOldspace N k
    exact (cuspOldspace N k).sub_mem (cuspOldspace_hecke_prime hp hpN _ (ih1 f hf))
      ((cuspOldspace N k).smul_mem _ (ih0 f hf))

/-- Every actual good-index Hecke operator preserves the full oldspace. -/
theorem cuspOldspace_hecke_coprime (N : ℕ) [NeZero N] (k : ℤ) (n : ℕ)
    (hnN : Nat.Coprime n N) :
    ∀ f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k, f ∈ cuspOldspace N k →
      cuspHeckeLinear N k n f ∈ cuspOldspace N k := by
  induction n using Nat.recOnPrimeCoprime with
  | zero =>
    intro f _
    rw [cuspHeckeLinear_zero]
    exact (cuspOldspace N k).zero_mem
  | prime_pow p r hp =>
    haveI : NeZero p := ⟨hp.ne_zero⟩
    cases r with
    | zero => simpa only [pow_zero, cuspHeckeLinear_one] using (fun f hf => hf)
    | succ r =>
      exact cuspOldspace_hecke_primePower hp (hnN.of_dvd_left (dvd_pow_self p (Nat.succ_ne_zero r))) _
  | coprime a b ha hb hab iha ihb =>
    intro f hf
    rw [← cuspHeckeLinear_coprime_mul N k (by omega) (by omega) hab]
    exact iha (Nat.coprime_mul_iff_left.mp hnN).1 _
      (ihb (Nat.coprime_mul_iff_left.mp hnN).2 f hf)

/-- Actual self-adjointness and full-oldspace stability imply genuine newspace stability. -/
theorem cuspNewspace_hecke_coprime {N : ℕ} [NeZero N] {k : ℤ} (n : ℕ)
    (hnN : Nat.Coprime n N)
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (hf : f ∈ cuspNewspace N k) :
    cuspHeckeLinear N k n f ∈ cuspNewspace N k := by
  intro g hg
  rw [cuspHeckeLinear_coprime_selfAdjoint N k n hnN]
  exact hf _ (cuspOldspace_hecke_coprime N k n hnN g hg)

end
end Dubon2026
