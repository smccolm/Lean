import Dubon2026.SourceCurveLaurentPlaces
import Dubon2026.SourceCurveResidueRestriction

/-! DUB-17/18 -> analytic torsion-cover places -> exact normalized orders.
The existing Laurent-place theorem permits a positive scaling. A mapped
base uniformizer of Laurent order one forces that scaling to be one. -/
namespace Dubon2026.SourceCurve.Place
noncomputable section
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem exists_place_of_laurent_order_one (ι : F →ₐ[K] LaurentSeries K)
    (u : F) (hu : (ι u).order = 1) :
    ∃ w : Place K F, ∀ f : F, w.ord f = (ι f).order := by
  obtain ⟨w, γ, hγ, hord⟩ := exists_place_of_laurent_embedding ι ⟨u, by rw [hu]; decide⟩
  have he := hord u
  rw [hu] at he
  have hg : (0 : ℤ) < γ := by exact_mod_cast hγ
  have hw : 0 < w.ord u := (mul_pos_iff_of_pos_right hg).mp (he.symm ▸ Int.zero_lt_one)
  have hγ1 : (γ : ℤ) = 1 := by nlinarith
  exact ⟨w, fun f => by simpa only [hγ1, mul_one] using hord f⟩

theorem exists_place_of_laurent_extension
    {E : Type*} [Field E] [Algebra K E] [Algebra F E] [IsScalarTower K F E]
    [Algebra.IsIntegral F E] (ι : F →ₐ[K] LaurentSeries K)
    (e : E →ₐ[K] LaurentSeries K) (v : Place K F)
    (he : ∀ g : F, e (algebraMap F E g) = ι g)
    (hv : ∀ g : F, g ≠ 0 → (ι g).order = v.ord g) :
    ∃ w : Place K E, w.restrict F = v ∧ ∀ a : E, w.ord a = (e a).order := by
  have hπ : (e (algebraMap F E v.uniformizer)).order = 1 := by
    rw [he, hv _ v.uniformizer_ne_zero, v.ord_uniformizer]
  obtain ⟨w, hw⟩ := exists_place_of_laurent_order_one e _ hπ
  have hbase (g : F) : w.ord (algebraMap F E g) = v.ord g := by
    rcases eq_or_ne g 0 with rfl | hg
    · rw [map_zero, w.ord_zero, v.ord_zero]
    rw [hw, he, hv g hg]
  refine ⟨w, ?_, hw⟩
  apply Place.ext
  ext g
  change algebraMap F E g ∈ w.toValuationSubring ↔ g ∈ v.toValuationSubring
  constructor
  · intro hg
    apply v.mem_of_ord_nonneg
    rw [← hbase]
    exact w.ord_nonneg_of_mem hg
  · intro hg
    apply w.mem_of_ord_nonneg
    rw [hbase]
    exact v.ord_nonneg_of_mem hg

end
end Dubon2026.SourceCurve.Place
