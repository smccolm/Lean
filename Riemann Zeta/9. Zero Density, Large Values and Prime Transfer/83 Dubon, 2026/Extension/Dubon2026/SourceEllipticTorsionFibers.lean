import Dubon2026.SourceEllipticTorsionZeroCriterion
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.Data.Set.Card

/-! DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> modular good reduction
-> reverse genus -> finite exceptional fibers -> elliptic cyclic-subgroup
inertia -> actual n-torsion cardinality. The native division-polynomial
degrees and the proved point multiplication formula control actual point
fibers. Native perfect-field separability replaces the archive's generic
squarefree helpers, and one general surjectivity proof replaces its two
duplicated odd/general proofs. The torsion group is the native multiplication
homomorphism kernel. Adapted from anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_WeierstrassCurve_card_torsion_of_isAlgClosed.lean. -/
namespace Dubon2026.SourceEllipticTorsion
open WeierstrassCurve WeierstrassCurve.Affine Polynomial
open Dubon2026.SourceEllipticPointFormula
noncomputable section
variable {F K : Type*} [Field F] [Field K] [Algebra F K] [DecidableEq K]
variable (W : WeierstrassCurve F)
/-- The native multiplication-by-n homomorphism kernel on the actual point group. -/
abbrev nTorsion (n : ℕ) : AddSubgroup (W.baseChange K).toAffine.Point :=
  (nsmulAddMonoidHom n : (W.baseChange K).toAffine.Point →+
    (W.baseChange K).toAffine.Point).ker

omit [DecidableEq K] in

theorem wronskian_Φ_ΨSq_ne_zero [W.IsElliptic] {n : ℕ} (hn : (n : K) ≠ 0) :
    derivative ((W.baseChange K).Φ n) * (W.baseChange K).ΨSq n -
      (W.baseChange K).Φ n * derivative ((W.baseChange K).ΨSq n) ≠ 0 := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  obtain rfl | h2 : n = 1 ∨ 2 ≤ n := by omega
  · simp [Φ_one, ΨSq_one]
  · set E := W.baseChange K with hE
    have hnQ : ((n : ℕ) : K) ≠ 0 := hn
    have hm4 : 4 ≤ n ^ 2 := by nlinarith

    have hFlc : (E.Φ n).coeff (n ^ 2) = 1 := by
      simpa using WeierstrassCurve.coeff_Φ E (n : ℤ)
    have hGlc : (E.ΨSq n).coeff (n ^ 2 - 1) = (n : K) ^ 2 := by
      simpa using WeierstrassCurve.coeff_ΨSq E (n : ℤ)
    have hF'c : (derivative (E.Φ n)).coeff (n ^ 2 - 1) =
        ((n ^ 2 - 1 : ℕ) : K) + 1 := by
      rw [coeff_derivative, Nat.sub_add_cancel (by omega : 1 ≤ n ^ 2), hFlc, one_mul]
    have hG'c : (derivative (E.ΨSq n)).coeff (n ^ 2 - 2) =
        (n : K) ^ 2 * (((n ^ 2 - 2 : ℕ) : K) + 1) := by
      rw [coeff_derivative, (by omega : n ^ 2 - 2 + 1 = n ^ 2 - 1), hGlc]

    have hFdegle : (E.Φ n).natDegree ≤ n ^ 2 := by
      have h := WeierstrassCurve.natDegree_Φ_le E (n : ℤ)
      rwa [Int.natAbs_natCast] at h
    have hGdegle : (E.ΨSq n).natDegree ≤ n ^ 2 - 1 := by
      have h := WeierstrassCurve.natDegree_ΨSq_le E (n : ℤ)
      rwa [Int.natAbs_natCast] at h
    have hF'le : (derivative (E.Φ n)).natDegree ≤ n ^ 2 - 1 := by
      have h := natDegree_derivative_le (E.Φ (n : ℤ))
      omega
    have hG'le : (derivative (E.ΨSq n)).natDegree ≤ n ^ 2 - 2 := by
      have h := natDegree_derivative_le (E.ΨSq (n : ℤ))
      omega
    intro hzero
    have hco : (derivative (E.Φ n) * E.ΨSq n - E.Φ n * derivative (E.ΨSq n)).coeff
        (2 * n ^ 2 - 2) = 0 := by rw [hzero, coeff_zero]
    have e1 : (derivative (E.Φ n) * E.ΨSq n).coeff (2 * n ^ 2 - 2) =
        (((n ^ 2 - 1 : ℕ) : K) + 1) * (n : K) ^ 2 := by
      rw [(by omega : 2 * n ^ 2 - 2 = (n ^ 2 - 1) + (n ^ 2 - 1)),
        coeff_mul_add_eq_of_natDegree_le hF'le hGdegle, hF'c, hGlc]
    have e2 : (E.Φ n * derivative (E.ΨSq n)).coeff (2 * n ^ 2 - 2) =
        1 * ((n : K) ^ 2 * (((n ^ 2 - 2 : ℕ) : K) + 1)) := by
      rw [(by omega : 2 * n ^ 2 - 2 = n ^ 2 + (n ^ 2 - 2)),
        coeff_mul_add_eq_of_natDegree_le hFdegle hG'le, hFlc, hG'c]
    rw [coeff_sub, e1, e2] at hco
    have c1 : ((n ^ 2 - 1 : ℕ) : K) = (n : K) ^ 2 - 1 := by
      push_cast [Nat.cast_sub (by omega : 1 ≤ n ^ 2)]
      ring
    have c2 : ((n ^ 2 - 2 : ℕ) : K) = (n : K) ^ 2 - 2 := by
      push_cast [Nat.cast_sub (by omega : 2 ≤ n ^ 2)]
      ring
    rw [c1, c2] at hco
    exact pow_ne_zero 2 hnQ (by linear_combination hco)

theorem finite_not_squarefree_fiber [IsAlgClosed K] [W.IsElliptic] {n : ℕ}
    (hn : (n : K) ≠ 0) :
    {c : K | ¬ Squarefree
      ((W.baseChange K).Φ n - C c * (W.baseChange K).ΨSq n)}.Finite := by
  have hpos : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
  set F' := (W.baseChange K).Φ n with hFdef
  set G := (W.baseChange K).ΨSq n with hGdef
  have hWr : derivative F' * G - F' * derivative G ≠ 0 := wronskian_Φ_ΨSq_ne_zero W hn
  have hroots : {x : K | (derivative F' * G - F' * derivative G).IsRoot x}.Finite :=
    finite_setOf_isRoot hWr
  refine Set.Finite.subset (hroots.image (fun x => F'.eval x / G.eval x)) ?_
  intro c hc
  rw [Set.mem_setOf_eq] at hc
  unfold Squarefree at hc
  push Not at hc
  obtain ⟨q, hq2, hqu⟩ := hc
  have hqdeg : q.degree ≠ 0 := fun h => hqu (isUnit_iff_degree_eq_zero.mpr h)
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root q hqdeg
  have hdvd : (X - C x) * (X - C x) ∣ F' - C c * G :=
    dvd_trans (mul_dvd_mul (dvd_iff_isRoot.mpr hx) (dvd_iff_isRoot.mpr hx)) hq2
  obtain ⟨r, hr⟩ := hdvd
  have hpx : (F' - C c * G).eval x = 0 := by rw [hr]; simp
  have hp'x : (derivative (F' - C c * G)).eval x = 0 := by
    rw [hr]
    simp [derivative_mul, derivative_sub, derivative_X, derivative_C]
  have hFx : F'.eval x = c * G.eval x := by
    have h := hpx
    simp only [eval_sub, eval_mul, eval_C] at h
    exact sub_eq_zero.mp h
  have hF'x : (derivative F').eval x = c * (derivative G).eval x := by
    have h := hp'x
    rw [derivative_sub, derivative_C_mul] at h
    simp only [eval_sub, eval_mul, eval_C] at h
    exact sub_eq_zero.mp h
  have hGx : G.eval x ≠ 0 := by
    intro hG0
    have hF0 : F'.eval x = 0 := by rw [hFx, hG0, mul_zero]
    obtain ⟨a, b, hab⟩ := isCoprime_Φ_ΨSq W (K := K) hpos
    rw [← hFdef, ← hGdef] at hab
    have h1 := congrArg (Polynomial.eval x) hab
    rw [eval_add, eval_mul, eval_mul, eval_one, hF0, hG0, mul_zero, mul_zero,
      add_zero] at h1
    exact zero_ne_one h1
  refine ⟨x, ?_, ?_⟩
  · show (derivative F' * G - F' * derivative G).IsRoot x
    simp only [IsRoot, eval_sub, eval_mul]
    rw [hFx, hF'x]
    ring
  · show F'.eval x / G.eval x = c
    rw [hFx, mul_div_assoc, div_self hGx, mul_one]


end
end Dubon2026.SourceEllipticTorsion
