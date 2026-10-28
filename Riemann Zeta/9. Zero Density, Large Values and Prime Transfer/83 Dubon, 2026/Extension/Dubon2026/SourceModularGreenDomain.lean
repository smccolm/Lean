import Mathlib
/-! DUB-17/18 -> original all-weight arithmetic association -> Gamma1 Picard/H1
-> Abel-Jacobi converse -> analytic reciprocity -> winding-period identity
-> Green's formula on the actual modular fundamental domain.
Adapted from pinned Apache-2.0 anthropics/fermats-last-theorem source.
Native Fubini, one-dimensional FTC and real change-of-variable theorems provide
the shorter rigorous route for the curved boundary; no boundary identity is
assumed. No incidental open-neighborhood assumption is retained. -/
namespace Dubon2026.SourceModularGreen
noncomputable section
open Complex MeasureTheory Set Filter Topology

/-- The actual closed planar modular domain. -/
def D : Set ℂ := {z : ℂ | |z.re| ≤ 1 / 2 ∧ 1 ≤ ‖z‖ ∧ 0 < z.im}

/-- Height of the unit semicircle above a horizontal coordinate. -/
def h (x : ℝ) : ℝ := Real.sqrt (1 - x ^ 2)

/-- Real-coordinate epigraph representing the modular domain. -/
def T : Set (ℝ × ℝ) := {p | |p.1| ≤ 1 / 2 ∧ h p.1 ≤ p.2}

lemma three_quarters_le {x : ℝ} (hx : |x| ≤ 1 / 2) : 3 / 4 ≤ 1 - x ^ 2 := by
  have h1 : x ^ 2 ≤ (1 / 2) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg x) hx 2
  linarith

lemma sqrt3_sq : (Real.sqrt 3 / 2) ^ 2 = 3 / 4 := by
  rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num

lemma sqrt3_pos : 0 < Real.sqrt 3 / 2 := by positivity

lemma sqrt3_lt_one : Real.sqrt 3 / 2 < 1 := by
  rw [div_lt_one two_pos, Real.sqrt_lt' two_pos]; norm_num

lemma sqrt3_le_h {x : ℝ} (hx : |x| ≤ 1 / 2) : Real.sqrt 3 / 2 ≤ h x := by
  unfold h
  rw [Real.le_sqrt' sqrt3_pos, sqrt3_sq]
  exact three_quarters_le hx

lemma h_pos {x : ℝ} (hx : |x| ≤ 1 / 2) : 0 < h x := lt_of_lt_of_le sqrt3_pos (sqrt3_le_h hx)

lemma h_le_one (x : ℝ) : h x ≤ 1 := by
  unfold h
  rw [Real.sqrt_le_left zero_le_one]
  nlinarith [sq_nonneg x]

lemma mem_D_iff {x y : ℝ} : (⟨x, y⟩ : ℂ) ∈ D ↔ |x| ≤ 1 / 2 ∧ h x ≤ y := by
  simp only [D, mem_setOf_eq, Complex.norm_def, Complex.normSq_mk, Real.one_le_sqrt]
  constructor
  · rintro ⟨hx, hn, hy⟩
    refine ⟨hx, ?_⟩
    unfold h
    rw [Real.sqrt_le_iff]
    exact ⟨hy.le, by nlinarith⟩
  · rintro ⟨hx, hy⟩
    have hpos := h_pos hx
    have hy' := hy
    unfold h at hy'
    rw [Real.sqrt_le_iff] at hy'
    exact ⟨hx, by nlinarith [hy'.2], lt_of_lt_of_le hpos hy⟩

lemma mk_mem_D {x y : ℝ} (hx : |x| ≤ 1 / 2) (hy : h x ≤ y) : (⟨x, y⟩ : ℂ) ∈ D :=
  mem_D_iff.mpr ⟨hx, hy⟩

lemma preimage_D : (measurableEquivRealProd.symm : ℝ × ℝ → ℂ) ⁻¹' D = T := by
  ext ⟨x, y⟩
  simp only [mem_preimage, measurableEquivRealProd_symm_apply, T, mem_setOf_eq]
  exact mem_D_iff

lemma isClosed_T : IsClosed T := by
  have h1 : IsClosed {p : ℝ × ℝ | |p.1| ≤ 1 / 2} :=
    isClosed_le (continuous_abs.comp continuous_fst) continuous_const
  have h2 : IsClosed {p : ℝ × ℝ | h p.1 ≤ p.2} := by
    refine isClosed_le ?_ continuous_snd
    exact (Real.continuous_sqrt.comp (continuous_const.sub (continuous_fst.pow 2)))
  simpa [T, setOf_and] using h1.inter h2

lemma measurableSet_T : MeasurableSet T := isClosed_T.measurableSet

lemma T_subset_prod : T ⊆ Icc (-(1 / 2 : ℝ)) (1 / 2) ×ˢ Ioi (0 : ℝ) := by
  rintro ⟨x, y⟩ ⟨hx, hy⟩
  exact ⟨abs_le.mp hx, lt_of_lt_of_le (h_pos hx) hy⟩

lemma setIntegral_D (G : ℂ → ℂ) : ∫ z in D, G z = ∫ p in T, G ⟨p.1, p.2⟩ := by
  rw [← preimage_D]
  exact ((Complex.volume_preserving_equiv_real_prod.symm _).setIntegral_preimage_emb
    measurableEquivRealProd.symm.measurableEmbedding G D).symm

lemma integrableOn_T_of_bound {G : ℝ × ℝ → ℂ} {C δ : ℝ} (hδ : 0 < δ)
    (hG : ContinuousOn G T) (hb : ∀ p ∈ T, ‖G p‖ ≤ C * Real.exp (-δ * p.2)) :
    IntegrableOn G T := by
  have hdom : IntegrableOn (fun p : ℝ × ℝ => (C : ℝ) * Real.exp (-δ * p.2))
      (Icc (-(1 / 2 : ℝ)) (1 / 2) ×ˢ Ioi (0 : ℝ)) := by
    rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict]
    have h1 : Integrable (fun _ : ℝ => (C : ℝ)) (volume.restrict (Icc (-(1 / 2 : ℝ)) (1 / 2))) :=
      integrable_const _
    have h2 : Integrable (fun y : ℝ => Real.exp (-δ * y)) (volume.restrict (Ioi (0 : ℝ))) :=
      exp_neg_integrableOn_Ioi 0 hδ
    exact h1.mul_prod h2
  refine Integrable.mono' (hdom.mono_set T_subset_prod)
    (hG.aestronglyMeasurable measurableSet_T) ?_
  exact (ae_restrict_iff' measurableSet_T).mpr (Eventually.of_forall hb)

lemma setIntegral_T_eq_x_y {G : ℝ × ℝ → ℂ} (hG : IntegrableOn G T) :
    ∫ p in T, G p = ∫ x in Icc (-(1 / 2 : ℝ)) (1 / 2), ∫ y in Ici (h x), G (x, y) := by
  have hi : Integrable (T.indicator G) (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]; exact hG.integrable_indicator measurableSet_T
  rw [← integral_indicator measurableSet_T, Measure.volume_eq_prod, integral_prod _ hi]
  have hS : {x : ℝ | |x| ≤ 1 / 2} = Icc (-(1 / 2 : ℝ)) (1 / 2) := by
    ext x; simp [abs_le]
  rw [← hS, ← integral_indicator (measurableSet_le continuous_abs.measurable measurable_const)]
  congr 1 with x
  by_cases hx : |x| ≤ 1 / 2
  · rw [indicator_of_mem (by exact hx), ← integral_indicator measurableSet_Ici]
    congr 1 with y
    by_cases hy : h x ≤ y
    · rw [indicator_of_mem (show (x, y) ∈ T from ⟨hx, hy⟩), indicator_of_mem (by exact hy)]
    · rw [indicator_of_notMem (show (x, y) ∉ T from fun hm => hy hm.2),
        indicator_of_notMem (by exact hy)]
  · rw [indicator_of_notMem (by exact hx)]
    have : ∀ y, T.indicator G (x, y) = 0 := fun y =>
      indicator_of_notMem (show (x, y) ∉ T from fun hm => hx hm.1) _
    simp [this]

lemma setIntegral_T_eq_y_x {G : ℝ × ℝ → ℂ} (hG : IntegrableOn G T) :
    ∫ p in T, G p = ∫ y, ∫ x in {x | |x| ≤ 1 / 2 ∧ h x ≤ y}, G (x, y) := by
  have hi : Integrable (T.indicator G) (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]; exact hG.integrable_indicator measurableSet_T
  rw [← integral_indicator measurableSet_T, Measure.volume_eq_prod, integral_prod_symm _ hi]
  congr 1 with y
  have hm : MeasurableSet {x : ℝ | |x| ≤ 1 / 2 ∧ h x ≤ y} := by
    have : IsClosed {x : ℝ | |x| ≤ 1 / 2 ∧ h x ≤ y} := by
      rw [setOf_and]
      exact (isClosed_le continuous_abs continuous_const).inter
        (isClosed_le (Real.continuous_sqrt.comp (continuous_const.sub (continuous_id.pow 2)))
          continuous_const)
    exact this.measurableSet
  rw [← integral_indicator hm]
  congr 1 with x


end
end Dubon2026.SourceModularGreen
