import FiniteDirichletPolynomial
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Data.Finset.Lattice.Fold

/-! # Actual finite Dirichlet polynomials and their supported length

The source sum uses the positive natural indices `1 ≤ n ≤ N`. Its complex
powers are Mathlib's principal powers. The positive-natural index adapter
identifies it with the existing foundation's `RiemannZeta.dirichletPoly`.
-/

namespace Dubon2026

open scoped BigOperators

noncomputable section

/-- The paper's actual finite Dirichlet truncation, including its `n = 1` term. -/
def dirichletSum (a : ℕ → ℂ) (N : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, a n * (n : ℂ) ^ (-s)

/-- Nonzero coefficients among the positive indices of the truncation. -/
def coefficientSupport (a : ℕ → ℂ) (N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter fun n => a n ≠ 0

/-- The source's largest supported index; zero for an empty supported set. -/
def lastIndex (a : ℕ → ℂ) (N : ℕ) : ℕ :=
  (coefficientSupport a N).sup id

/-- The same finite index set on the positive naturals used by the foundation. -/
def positiveIndices (N : ℕ) : Finset ℕ+ :=
  (Finset.Icc 1 N).attach.image fun n =>
    ⟨n.val, lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp n.property).1⟩

@[simp]
theorem dirichletSum_zero (a : ℕ → ℂ) (s : ℂ) : dirichletSum a 0 s = 0 := by
  simp [dirichletSum]

@[simp]
theorem dirichletSum_one (a : ℕ → ℂ) (s : ℂ) : dirichletSum a 1 s = a 1 := by
  simp [dirichletSum]

theorem mem_coefficientSupport {a : ℕ → ℂ} {N n : ℕ} :
    n ∈ coefficientSupport a N ↔ 1 ≤ n ∧ n ≤ N ∧ a n ≠ 0 := by
  simp only [coefficientSupport, Finset.mem_filter, Finset.mem_Icc]
  tauto

theorem lastIndex_le (a : ℕ → ℂ) (N : ℕ) : lastIndex a N ≤ N := by
  apply Finset.sup_le
  intro n hn
  exact (mem_coefficientSupport.mp hn).2.1

theorem le_lastIndex {a : ℕ → ℂ} {N n : ℕ} (hn : n ∈ coefficientSupport a N) :
    n ≤ lastIndex a N :=
  Finset.le_sup (f := id) hn

theorem one_mem_coefficientSupport {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) : 1 ∈ coefficientSupport a N := by
  exact mem_coefficientSupport.mpr ⟨le_rfl, hN, ha⟩

theorem one_le_lastIndex {a : ℕ → ℂ} {N : ℕ} (hN : 1 ≤ N) (ha : a 1 ≠ 0) :
    1 ≤ lastIndex a N :=
  le_lastIndex (one_mem_coefficientSupport hN ha)

theorem lastIndex_mem {a : ℕ → ℂ} {N : ℕ}
    (h : (coefficientSupport a N).Nonempty) : lastIndex a N ∈ coefficientSupport a N := by
  have hm := Finset.sup_mem_of_nonempty (f := id) h
  simpa only [Set.image_id, Finset.mem_coe] using hm

theorem coefficient_lastIndex_ne_zero {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) : a (lastIndex a N) ≠ 0 :=
  (mem_coefficientSupport.mp (lastIndex_mem ⟨1, one_mem_coefficientSupport hN ha⟩)).2.2

theorem coefficient_eq_zero_of_lastIndex_lt {a : ℕ → ℂ} {N n : ℕ}
    (hn : n ≤ N) (h : lastIndex a N < n) : a n = 0 := by
  by_contra hne
  have hpos : 1 ≤ n := by omega
  have := le_lastIndex (mem_coefficientSupport.mpr ⟨hpos, hn, hne⟩)
  omega

theorem lastIndex_eq_of_last_coefficient {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a N ≠ 0) : lastIndex a N = N := by
  apply le_antisymm (lastIndex_le a N)
  exact le_lastIndex (mem_coefficientSupport.mpr ⟨hN, le_rfl, ha⟩)

theorem dirichletSum_eq_foundation (a : ℕ → ℂ) (N : ℕ) (s : ℂ) :
    dirichletSum a N s =
      RiemannZeta.dirichletPoly (fun n => a n.val) (positiveIndices N) s := by
  unfold RiemannZeta.dirichletPoly positiveIndices
  rw [Finset.sum_image]
  · simpa only [dirichletSum] using
      (Finset.sum_attach (Finset.Icc 1 N) (fun n => a n * (n : ℂ) ^ (-s))).symm
  · intro n hn m hm h
    apply Subtype.ext
    exact congrArg (fun p : ℕ+ => (p : ℕ)) h

theorem nat_cpow_neg_eq_exp {n : ℕ} (hn : 1 ≤ n) (s : ℂ) :
    (n : ℂ) ^ (-s) = Complex.exp (-s * (Real.log n : ℂ)) := by
  have hpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (show n ≠ 0 by omega))]
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_log hpos.le]
  congr 1
  ring

theorem dirichletSum_eq_sum_exp (a : ℕ → ℂ) (N : ℕ) (s : ℂ) :
    dirichletSum a N s =
      ∑ n ∈ Finset.Icc 1 N, a n * Complex.exp (-s * (Real.log n : ℂ)) := by
  apply Finset.sum_congr rfl
  intro n hn
  rw [nat_cpow_neg_eq_exp (Finset.mem_Icc.mp hn).1]

theorem analyticAt_dirichletSum (a : ℕ → ℂ) (N : ℕ) (s : ℂ) :
    AnalyticAt ℂ (dirichletSum a N) s := by
  simp_rw [show dirichletSum a N =
      (fun z => ∑ n ∈ Finset.Icc 1 N, a n * Complex.exp (-z * (Real.log n : ℂ))) by
    funext z
    exact dirichletSum_eq_sum_exp a N z]
  fun_prop

theorem analyticOnNhd_dirichletSum (a : ℕ → ℂ) (N : ℕ) :
    AnalyticOnNhd ℂ (dirichletSum a N) Set.univ :=
  fun s _ => analyticAt_dirichletSum a N s

end

end Dubon2026
