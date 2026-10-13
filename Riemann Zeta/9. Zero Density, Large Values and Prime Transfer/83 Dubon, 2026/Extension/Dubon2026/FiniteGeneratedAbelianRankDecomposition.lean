import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.LinearAlgebra.Dimension.Torsion.Finite
import Mathlib.LinearAlgebra.Dimension.RankNullity

/-! # Finite torsion and the exact free rank

The pinned structure theorem supplies a finite factor and a free factor
whose rank is computed here. This is used only to count the original
S-unit power quotient in the global norm-index dependency of DUB-17.
-/

namespace Dubon2026
noncomputable section

/-- A finitely generated abelian group has an actual finite factor and a free factor
of precisely its integer rank. No logarithmic lattice or splitting hypothesis is needed. -/
theorem finiteGeneratedAbelian_exists_rank_decomposition
    (G : Type*) [AddCommGroup G] [AddGroup.FG G] :
    ∃ (d : ℕ) (T : Type) (_ : AddCommGroup T) (_ : Finite T),
      Nonempty (G ≃+ (Fin d → ℤ) × T) ∧ Module.finrank ℤ G = d := by
  classical
  obtain ⟨d, ι, hι, p, hp, k, ⟨e⟩⟩ := AddCommGroup.equiv_free_prod_directSum_zmod G
  letI := hι
  letI : ∀ i, NeZero (p i ^ k i) := fun i => ⟨pow_ne_zero _ (hp i).ne_zero⟩
  let T := (i : ι) → ZMod (p i ^ k i)
  let e' : G ≃+ (Fin d → ℤ) × T := e.trans
    (Finsupp.addEquivFunOnFinite.prodCongr (DirectSum.addEquivProd _))
  have ht : Module.rank ℤ T = 0 := rank_eq_zero_iff_isTorsion.mpr
    (AddMonoid.isTorsion_iff_isTorsion_int.mp is_add_torsion_of_finite)
  refine ⟨d, T, inferInstance, inferInstance, ⟨e'⟩, ?_⟩
  have h := LinearMap.rank_eq_of_surjective
    (f := LinearMap.fst ℤ (Fin d → ℤ) T) Prod.fst_surjective
  rw [LinearMap.ker_fst,
    ← (LinearEquiv.ofInjective (LinearMap.inr ℤ (Fin d → ℤ) T)
      LinearMap.inr_injective).rank_eq,
    ht, add_zero] at h
  rw [e'.toIntLinearEquiv.finrank_eq]
  exact (congrArg Cardinal.toNat h).trans (by
    change Module.finrank ℤ (Fin d → ℤ) = d
    simp)

end
end Dubon2026
