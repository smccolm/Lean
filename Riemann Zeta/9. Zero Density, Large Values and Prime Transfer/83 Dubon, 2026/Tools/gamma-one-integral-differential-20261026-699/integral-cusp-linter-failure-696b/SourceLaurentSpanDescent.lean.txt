import Dubon2026.SourceLaurentIntegralDescent

/-! DUB-17/18 -> actual Gamma1 differential realization -> original
integral-ratio field -> bounded rational Fourier denominators. Descend
membership in the finite scalar span of the original Fricke Laurent field
using the same coefficient retraction as the existing monic-relation
descent. This provides the original cyclotomic function-field entry for a
rational-coefficient cusp image; no additional fixed-field infrastructure
or algebraicity hypothesis is required. -/
namespace Dubon2026.SourceFunctionField
noncomputable section

theorem mem_span_of_coeffMap_mem_span {k L : Type*} [Field k] [Field L]
    (σ : k →+* L) (S : Set (LaurentSeries k)) (x : LaurentSeries k)
    (hx : coeffMap σ x ∈ Submodule.span L (coeffMap σ '' S)) :
    x ∈ Submodule.span k S := by
  classical
  letI : Algebra k L := σ.toAlgebra
  obtain ⟨π, hπ⟩ := (Algebra.linearMap k L).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr (algebraMap k L).injective)
  have hπσ (a : k) : π (σ a) = a := by
    have he := LinearMap.congr_fun hπ a
    simpa using he
  let Pr : LaurentSeries L →+ LaurentSeries k :=
    { toFun := fun Z => Z.map π
      map_zero' := by ext n; simp
      map_add' := fun Z Z' => by ext n; simp }
  have hPr_coeff (Z : LaurentSeries L) (n : ℤ) : (Pr Z).coeff n = π (Z.coeff n) := rfl
  have hPr_map (z : LaurentSeries k) : Pr (coeffMap σ z) = z := by
    ext n
    rw [hPr_coeff, coeffMap_coeff, hπσ]
  have hPr_smul (c : L) (z : LaurentSeries k) :
      Pr (c • coeffMap σ z) = π c • z := by
    ext n
    rw [hPr_coeff, HahnSeries.coeff_smul, HahnSeries.coeff_smul, coeffMap_coeff]
    change π (c * σ (z.coeff n)) = π c * z.coeff n
    rw [mul_comm c,
      show σ (z.coeff n) * c = (z.coeff n) • c from (Algebra.smul_def _ _).symm,
      map_smul, smul_eq_mul, mul_comm]
  obtain ⟨n, c, g, hg⟩ := Submodule.mem_span_set'.mp hx
  choose z hz hze using fun i => (g i).property
  have hs : (∑ i, π (c i) • z i) = x := by
    calc (∑ i, π (c i) • z i) = ∑ i, Pr (c i • coeffMap σ (z i)) :=
        Finset.sum_congr rfl fun i _ => (hPr_smul _ _).symm
      _ = Pr (∑ i, c i • (g i : LaurentSeries L)) := by
        rw [map_sum]
        simp_rw [hze]
      _ = Pr (coeffMap σ x) := congrArg Pr hg
      _ = x := hPr_map x
  rw [← hs]
  exact Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span (hz i))

end
end Dubon2026.SourceFunctionField
