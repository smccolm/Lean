import Dubon2026.SourceCellPolygonWordChains
import Dubon2026.SourceCyclicChordAntisymmetry

/-! DUB-17/18 -> original Abel-Jacobi -> raw period reciprocity.
The exact strict cyclic-word matrix must be skew-symmetric and unimodular.
Adapted from anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
Only the required cyclic interval and lattice arguments are retained;
the existing actual dissection, loop generation and full real span supply
their inputs in the original-curve consumer.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.DissectionPeriods
noncomputable section
variable {E : Type*} [DecidableEq E] {𝒯s : Finset E} {m : ℕ} [NeZero m]

theorem wordChain_eq (wd : ZMod m ≃ {q : E × Bool // q.1 ∉ 𝒯s}) (e : E) (he : e ∉ 𝒯s)
    (f : E) (hf : f ∉ 𝒯s) :
    wordChain wd e he f =
      (if wd.symm ⟨(f, true), hf⟩ ≠ wd.symm ⟨(e, true), he⟩ ∧
          (wd.symm ⟨(f, true), hf⟩ - wd.symm ⟨(e, true), he⟩).val <
            (wd.symm ⟨(e, false), he⟩ - wd.symm ⟨(e, true), he⟩).val then (1 : ℤ) else 0) -
      (if wd.symm ⟨(f, false), hf⟩ ≠ wd.symm ⟨(e, true), he⟩ ∧
          (wd.symm ⟨(f, false), hf⟩ - wd.symm ⟨(e, true), he⟩).val <
            (wd.symm ⟨(e, false), he⟩ - wd.symm ⟨(e, true), he⟩).val then (1 : ℤ) else 0) := by
  classical
  unfold wordChain
  set α := wd.symm ⟨(e, true), he⟩
  set β := wd.symm ⟨(e, false), he⟩
  set af := wd.symm ⟨(f, true), hf⟩
  set bf := wd.symm ⟨(f, false), hf⟩

  have hsplit : ∀ i : ZMod m,
      (if (wd i).1.2 then (1 : ℤ) else -1) * (if (wd i).1.1 = f then 1 else 0) =
        (if i = af then 1 else 0) - (if i = bf then 1 else 0) := by
    intro i
    have haf : i = af ↔ (wd i).1 = (f, true) := by
      constructor
      · rintro rfl; simp [af]
      · intro h
        apply wd.injective
        rw [Equiv.apply_symm_apply]
        exact Subtype.ext h
    have hbf : i = bf ↔ (wd i).1 = (f, false) := by
      constructor
      · rintro rfl; simp [bf]
      · intro h
        apply wd.injective
        rw [Equiv.apply_symm_apply]
        exact Subtype.ext h
    by_cases h1 : (wd i).1.1 = f
    · cases h2 : (wd i).1.2
      · have : (wd i).1 = (f, false) := Prod.ext h1 h2
        have hia : ¬ i = af := fun h => by rw [haf.1 h] at this; simp at this
        have hib : i = bf := hbf.2 this
        rw [if_neg hia, if_pos hib, if_pos h1]
        simp
      · have : (wd i).1 = (f, true) := Prod.ext h1 h2
        have hia : i = af := haf.2 this
        have hib : ¬ i = bf := fun h => by rw [hbf.1 h] at this; simp at this
        rw [if_pos hia, if_neg hib, if_pos h1]
        simp
    · have hia : ¬ i = af := fun h => h1 (by rw [haf.1 h])
      have hib : ¬ i = bf := fun h => h1 (by rw [hbf.1 h])
      rw [if_neg h1, mul_zero, if_neg hia, if_neg hib]
      simp
  simp_rw [hsplit]
  rw [Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]


theorem wordChain_antisymm (wd : ZMod m ≃ {q : E × Bool // q.1 ∉ 𝒯s})
    (e f : E) (he : e ∉ 𝒯s) (hf : f ∉ 𝒯s) :
    wordChain wd f hf e = -wordChain wd e he f := by
  rw [wordChain_eq wd f hf e he, wordChain_eq wd e he f hf]
  by_cases hef : e = f
  · subst f
    simp
  · have h := four_point_cyclic_interval_identity
      (x := wd.symm ⟨(e, true), he⟩) (y := wd.symm ⟨(e, false), he⟩)
      (z := wd.symm ⟨(f, true), hf⟩) (w := wd.symm ⟨(f, false), hf⟩)
      (wd.symm.injective.ne (by simp))
      (wd.symm.injective.ne (by simp [hef]))
      (wd.symm.injective.ne (by simp))
      (wd.symm.injective.ne (by simp))
      (wd.symm.injective.ne (by simp [hef]))
      (wd.symm.injective.ne (by simp))
    linear_combination h

end
end Dubon2026.SourceFunctionField.CellGeometry.DissectionPeriods
