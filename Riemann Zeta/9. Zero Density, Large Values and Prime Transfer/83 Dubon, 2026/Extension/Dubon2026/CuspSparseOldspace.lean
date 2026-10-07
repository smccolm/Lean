import Dubon2026.CuspSparseLowering
import Dubon2026.ModularNewspace

/-! # Sparse cusp forms are genuine oldforms from the divided level -/

namespace Dubon2026

open Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

noncomputable section

/-- The constructed lower cusp form maps back to f under the actual degeneracy map. -/
theorem cuspSparseLower_degeneracy {N d : ℕ} [NeZero N] [NeZero d] (hd : d ∣ N) (k : ℤ)
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)
    (hf : ∀ n, ¬d ∣ n → cuspCoefficients f n = 0) :
    cuspDegeneracyMap d (by rw [Nat.mul_div_cancel' hd]) k (cuspSparseLower hd k f hf) = f := by
  ext τ
  rw [cuspDegeneracyMap_apply]
  rw [← levelRaiseFun_apply d k (cuspSparseLower hd k f hf) τ]
  exact congr_fun (cuspSparseLower_levelRaise hd k f hf) τ

/-- The lowered source form has precisely the subsequence a_f(dn) as its q-expansion. -/
theorem cuspSparseLower_coeff {N d : ℕ} [NeZero N] [NeZero d] (hd : d ∣ N) (k : ℤ)
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)
    (hf : ∀ n, ¬d ∣ n → cuspCoefficients f n = 0) (n : ℕ) :
    cuspCoefficients (cuspSparseLower hd k f hf) n = cuspCoefficients f (d * n) := by
  have he := congrArg (fun g => cuspCoefficients g (d * n)) (cuspSparseLower_degeneracy hd k f hf)
  dsimp only at he
  rw [cuspDegeneracyMap_coeff, if_pos (dvd_mul_right d n),
    Nat.mul_div_cancel_left n (Nat.pos_of_neZero d)] at he
  exact he

/-- Sparse support at a proper divisor dilation places the actual form in the full classical oldspace. -/
theorem cusp_sparse_mem_oldspace {N d : ℕ} [NeZero N] [NeZero d]
    (hd : d ∣ N) (hd1 : 1 < d) (k : ℤ)
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)
    (hf : ∀ n, ¬d ∣ n → cuspCoefficients f n = 0) : f ∈ cuspOldspace N k := by
  rw [← cuspSparseLower_degeneracy hd k f hf]
  exact cuspDegeneracyMap_mem_oldspace
    (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_neZero N) hd) (Nat.pos_of_neZero d))
    (Nat.div_lt_self (Nat.pos_of_neZero N) hd1) d _ _

/-- No nonzero actual newform-space vector can be supported on multiples of a proper dilation. -/
theorem cusp_new_sparse_eq_zero {N d : ℕ} [NeZero N] [NeZero d]
    (hd : d ∣ N) (hd1 : 1 < d) (k : ℤ)
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (hnew : f ∈ cuspNewspace N k)
    (hf : ∀ n, ¬d ∣ n → cuspCoefficients f n = 0) : f = 0 :=
  Submodule.disjoint_def.mp (cuspOldspace_disjoint_newspace N k) f
    (cusp_sparse_mem_oldspace hd hd1 k f hf) hnew

/-- At every positive prime-power level the full coprime-support implication already follows. -/
theorem cusp_primePower_coprime_support_old {p r : ℕ} [NeZero p] (hp : Nat.Prime p)
    (hr : 0 < r) (k : ℤ) (f : CuspForm ((Gamma0 (p ^ r)).map (mapGL ℝ)) k)
    (hf : ∀ n, (p ^ r).Coprime n → cuspCoefficients f n = 0) :
    f ∈ cuspOldspace (p ^ r) k := by
  apply cusp_sparse_mem_oldspace (dvd_pow_self p hr.ne') hp.one_lt k f
  intro n hn
  exact hf n ((hp.coprime_iff_not_dvd.mpr hn).pow_left r)

/-- At prime-power level a genuine newspace vector is determined by its coprime coefficients. -/
theorem cusp_primePower_new_coprime_eq_zero {p r : ℕ} [NeZero p] (hp : Nat.Prime p)
    (hr : 0 < r) (k : ℤ) (f : CuspForm ((Gamma0 (p ^ r)).map (mapGL ℝ)) k)
    (hnew : f ∈ cuspNewspace (p ^ r) k)
    (hf : ∀ n, (p ^ r).Coprime n → cuspCoefficients f n = 0) : f = 0 :=
  Submodule.disjoint_def.mp (cuspOldspace_disjoint_newspace (p ^ r) k) f
    (cusp_primePower_coprime_support_old hp hr k f hf) hnew

end
end Dubon2026
