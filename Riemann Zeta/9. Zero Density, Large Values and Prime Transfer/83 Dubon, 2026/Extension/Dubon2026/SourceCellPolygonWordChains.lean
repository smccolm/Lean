import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

/-! DUB-17/18 -> original Abel-Jacobi -> jump-to-period formula.
The exact strict polygon subword defines an integer edge chain. Reindex its
signed edge integrals by that chain and prove its coefficients vanish on the
dual tree. These are the finite-sum steps needed to use the already proved
closed-cycle decomposition; no analytic generation is assumed.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.DissectionPeriods
noncomputable section
variable {E : Type*} [DecidableEq E] {𝒯s : Finset E} {m : ℕ} [NeZero m]

/-- Signed integer coefficient of an edge in the source strict cyclic subword. -/
def wordChain (wd : ZMod m ≃ {q : E × Bool // q.1 ∉ 𝒯s}) (e : E) (he : e ∉ 𝒯s) (f : E) : ℤ :=
  ∑ i ∈ Finset.univ.filter (fun i : ZMod m => i ≠ wd.symm ⟨(e, true), he⟩ ∧
      (i - wd.symm ⟨(e, true), he⟩).val <
        (wd.symm ⟨(e, false), he⟩ - wd.symm ⟨(e, true), he⟩).val),
    (if (wd i).1.2 then (1 : ℤ) else -1) * (if (wd i).1.1 = f then 1 else 0)

theorem wordChain_of_mem (wd : ZMod m ≃ {q : E × Bool // q.1 ∉ 𝒯s}) (e : E) (he : e ∉ 𝒯s)
    {f : E} (hf : f ∈ 𝒯s) : wordChain wd e he f = 0 := by
  refine Finset.sum_eq_zero fun i _ => ?_
  have h : ¬ (wd i).1.1 = f := fun h => (wd i).2 (h ▸ hf)
  rw [if_neg h, mul_zero]

theorem sum_word_eq_sum_wordChain [Fintype E] {κ : Type*} {𝒯s : Finset E} {m : ℕ} [NeZero m]
    (wd : ZMod m ≃ {q : E × Bool // q.1 ∉ 𝒯s}) (j : E) (hj : j ∉ 𝒯s)
    (I : E → κ → ℂ) :
    ∑ i ∈ Finset.univ.filter (fun i : ZMod m => i ≠ wd.symm ⟨(j, true), hj⟩ ∧
        (i - wd.symm ⟨(j, true), hj⟩).val <
          (wd.symm ⟨(j, false), hj⟩ - wd.symm ⟨(j, true), hj⟩).val),
      (if (wd i).1.2 then (1 : ℂ) else -1) • I (wd i).1.1 =
    ∑ f, (wordChain wd j hj f : ℂ) • I f := by
  classical
  simp only [wordChain]
  push_cast
  simp only [Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [mul_ite, mul_one, mul_zero, ite_smul, zero_smul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]

end
end Dubon2026.SourceFunctionField.CellGeometry.DissectionPeriods
