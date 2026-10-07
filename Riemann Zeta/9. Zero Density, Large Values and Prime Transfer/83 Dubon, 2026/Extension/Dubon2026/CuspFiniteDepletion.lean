import Dubon2026.FrickeDegeneracy

/-! # Genuine depletion at the square of a finite product of distinct primes -/

namespace Dubon2026

open Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

noncomputable section

/-- Iterating the actual prime depletion constructs the coprime-supported cusp form and computes its first Fricke coefficient. -/
theorem exists_cuspFiniteDepletion (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p)
    {R : ℕ} [NeZero R] (hR : R = ∏ p ∈ S, p)
    {L : ℕ} [NeZero L] (hL : L = R * R) {k : ℤ} (f : PrimitiveCuspForm 1 k) :
    ∃ g : CuspForm ((Gamma0 L).map (mapGL ℝ)) k,
      (∀ n, cuspCoefficients g n = if n.Coprime R then cuspCoefficients f.toCuspForm n else 0) ∧
      (∀ q [NeZero q], Nat.Prime q → q.Coprime R →
        cuspHeckeLinear L k q g = cuspCoefficients f.toCuspForm q • g) ∧
      cuspCoefficients (cuspFricke L k g) 1 = (R : ℂ) ^ (k - 3) := by
  induction S using Finset.induction_on generalizing R L with
  | empty =>
    simp only [Finset.prod_empty] at hR
    subst R
    have hL' : L = 1 := by simpa only [one_mul] using hL
    subst L
    refine ⟨f.toCuspForm, ?_, ?_, ?_⟩
    · intro n
      exact (if_pos (Nat.coprime_one_right n)).symm
    · intro q _ hq _
      exact primitiveCuspForm_eigenvector_all f hq.pos
    · simp only [Nat.cast_one, one_zpow]
      change cuspCoefficients (cuspFricke 1 k f.toCuspForm) 1 = 1
      rw [cuspFricke_one, Module.End.one_apply]
      exact f.normalized
  | @insert p S hpS ih =>
    have hp : Nat.Prime p := hS p (Finset.mem_insert_self p S)
    have hS' : ∀ q ∈ S, Nat.Prime q := fun q hq => hS q (Finset.mem_insert_of_mem hq)
    let r : ℕ := ∏ q ∈ S, q
    have hrpos : 0 < r := Finset.prod_pos fun q hq => (hS' q hq).pos
    letI : NeZero r := ⟨hrpos.ne'⟩
    letI : NeZero p := ⟨hp.ne_zero⟩
    have hpr : p.Coprime r := by
      apply Nat.coprime_prod_right_iff.mpr
      intro q hq
      exact (Nat.coprime_primes hp (hS' q hq)).mpr (fun h => hpS (h ▸ hq))
    have hR' : R = p * r := by simpa only [Finset.prod_insert hpS] using hR
    clear hR
    subst R
    obtain ⟨g, hg, he, hw⟩ := ih hS' (R := r) rfl (L := r * r) rfl
    have hlevel : (p * r) * (p * r) = p * (p * (r * r)) := by ring
    have hL' : L = p * (p * (r * r)) := hL.trans hlevel
    clear hL
    subst L
    refine ⟨cuspPrimeDepletion (p := p) k (cuspCoefficients f.toCuspForm p) g, ?_, ?_, ?_⟩
    · intro n
      rw [cuspPrimeDepletion_coeff hp (hpr.mul_right hpr) _ g (he p hp hpr), hg]
      have hn : n.Coprime p ↔ ¬p ∣ n := by rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
      simp only [Nat.coprime_mul_iff_right, hn]
      split_ifs <;> simp_all
    · intro q _ hq hqr
      have hqpr := Nat.coprime_mul_iff_right.mp hqr
      have hqN : q.Coprime (p * (p * (r * r))) :=
        hqpr.1.mul_right (hqpr.1.mul_right (hqpr.2.mul_right hqpr.2))
      rw [cuspPrimeDepletion_hecke_commute k _ hq hqN, he q hq hqpr.2, map_smul]
    · rw [cuspFricke_primeDepletion_coeff_one hp, hw, Nat.cast_mul, mul_zpow]

end
end Dubon2026
