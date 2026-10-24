import Mathlib.FieldTheory.Normal.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Separable

/-! DUB-17/18 -> exceptional fibers -> finite Galois modular roots.
A separable root fixed by all automorphisms of an algebraic closure descends
to the original field. Native normal-extension root conjugacy replaces the
external proof's explicit construction and extension of embeddings.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2, the mem_range_of_fixed lemma in
S_WeierstrassCurve_exists_equiv_addSubgroup_isAddCyclic_isRoot_modularPolynomial_of_transcendental_j. -/
namespace Dubon2026.SourceEllipticVelu
open Polynomial
noncomputable section

theorem separable_root_mem_range_of_fixed
    {F L : Type*} [Field F] [Field L] [Algebra F L] [IsAlgClosure F L]
    (α : L) (p : Polynomial F) (hsep : p.Separable)
    (hroot : (p.map (algebraMap F L)).IsRoot α)
    (hfix : ∀ σ : L ≃ₐ[F] L, σ α = α) : α ∈ Set.range (algebraMap F L) := by
  classical
  letI : IsAlgClosed L := IsAlgClosure.isAlgClosed F
  letI : Algebra.IsAlgebraic F L := IsAlgClosure.isAlgebraic
  letI : Normal F L := ⟨fun _ => IsAlgClosed.splits _⟩
  have hint : IsIntegral F α := Algebra.IsIntegral.isIntegral α
  have hmin : (minpoly F α).Separable := hsep.of_dvd (minpoly.dvd F α (by
    rwa [IsRoot.def, eval_map, ← aeval_def] at hroot))
  let q := (minpoly F α).map (algebraMap F L)
  have hall : ∀ β ∈ q.roots, β = α := by
    intro β hβ
    have hr := (mem_roots (Polynomial.map_ne_zero (minpoly.ne_zero hint))).mp hβ
    have hev : aeval β (minpoly F α) = 0 := by
      simpa only [IsRoot.def, eval_map, aeval_def] using hr
    obtain ⟨σ, hσ⟩ := minpoly.exists_algEquiv_of_root' hint.isAlgebraic hev
    exact hσ.symm.trans (hfix σ)
  have hnodup : q.roots.Nodup := Polynomial.nodup_roots hmin.map
  have hrep := Multiset.eq_replicate_card.mpr hall
  have hle : q.roots.card ≤ 1 := by
    have hc := (Multiset.nodup_iff_count_le_one.mp hnodup) α
    rwa [hrep, Multiset.count_replicate_self] at hc
  have hcard : q.roots.card = (minpoly F α).natDegree := by
    rw [← Polynomial.natDegree_map (algebraMap F L)]
    exact Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits q)
  have hdeg : (minpoly F α).natDegree = 1 := by
    have hp := minpoly.natDegree_pos hint
    omega
  apply minpoly.mem_range_of_degree_eq_one F α
  rw [Polynomial.degree_eq_natDegree (minpoly.ne_zero hint), hdeg]
  rfl

end
end Dubon2026.SourceEllipticVelu
