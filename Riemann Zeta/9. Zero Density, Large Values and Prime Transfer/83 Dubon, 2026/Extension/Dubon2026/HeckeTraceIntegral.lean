import Dubon2026.HeckeProjectiveCosets
import Dubon2026.HeckeSlashIntegrability

/-! # Integrating actual finite slash traces over the corresponding genuine domains -/

namespace Dubon2026

open Matrix.SpecialLinearGroup CongruenceSubgroup UpperHalfPlane MeasureTheory
open scoped MatrixGroups ModularForm Pointwise

noncomputable section

/-- The literal union of matrix-translated Gamma0 domains. -/
def heckeTransversalDomain {ι : Type*} {Q : ℕ} (r : ι → Gamma0 Q) : Set ℍ :=
  ⋃ i, mapGL ℝ (r i).val • gamma0FundamentalDomain Q

/-- Every finite union of these genuine translates has finite hyperbolic volume. -/
theorem heckeTransversalDomain_volume_lt_top {ι : Type*} [Fintype ι] {Q : ℕ} [NeZero Q]
    (r : ι → Gamma0 Q) : (volume : Measure ℍ) (heckeTransversalDomain r) < ⊤ := by
  unfold heckeTransversalDomain
  refine lt_of_le_of_lt (measure_iUnion_le _) ?_
  rw [tsum_fintype]
  refine ENNReal.sum_lt_top.mpr fun i _ => ?_
  rw [measure_smul]
  exact gamma0FundamentalDomain_volume_lt_top Q

/-- Distinct actual projective representatives give tiles with null intersection. -/
theorem heckeTransversalDomain_tiles_aedisjoint {ι : Type*} {Q : ℕ} [NeZero Q]
    (r : ι → Gamma0 Q) (hr : Function.Injective (fun i => gamma0ToRealProjective Q (r i))) :
    Pairwise (fun i j => AEDisjoint (volume : Measure ℍ)
      (mapGL ℝ (r i).val • gamma0FundamentalDomain Q)
      (mapGL ℝ (r j).val • gamma0FundamentalDomain Q)) := by
  intro i j hij
  have hne : gamma0ToRealProjective Q (r i) ≠ gamma0ToRealProjective Q (r j) :=
    fun h => hij (hr h)
  have hd := (isFundamentalDomain_realGamma0 Q).aedisjoint hne
  exact hd

/-- Every matrix tile is hyperbolically null-measurable. -/
theorem heckeTransversalDomain_tile_nullMeasurable {ι : Type*} {Q : ℕ} [NeZero Q]
    (r : ι → Gamma0 Q) (i : ι) :
    NullMeasurableSet (mapGL ℝ (r i).val • gamma0FundamentalDomain Q) (volume : Measure ℍ) :=
  (isFundamentalDomain_realGamma0 Q).nullMeasurableSet_smul (gamma0ToRealProjective Q (r i))

/-- Integrating a genuine left slash trace unfolds to the integral over its exact tile union. -/
theorem peterssonInner_trace_left {ι : Type*} [Fintype ι] {Q : ℕ} [NeZero Q] {k : ℤ}
    (f g : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (A : GL (Fin 2) ℝ)
    (r : ι → Gamma0 Q) (hr : Function.Injective (fun i => gamma0ToRealProjective Q (r i))) :
    peterssonInner k (gamma0FundamentalDomain Q)
        (∑ i, (⇑f ∣[k] A) ∣[k] mapGL ℝ (r i).val) g =
      peterssonInner k (heckeTransversalDomain r) (⇑f ∣[k] A) g := by
  have hU : IntegrableOn (petersson k (⇑f ∣[k] A) g) (heckeTransversalDomain r)
      (volume : Measure ℍ) := by
    simpa only [SlashAction.slash_one] using integrableOn_cusp_mixed_slash f g A 1
      (heckeTransversalDomain r) (heckeTransversalDomain_volume_lt_top r)
  have hD (i : ι) : IntegrableOn (petersson k ((⇑f ∣[k] A) ∣[k] mapGL ℝ (r i).val) g)
      (gamma0FundamentalDomain Q) (volume : Measure ℍ) := by
    simpa only [SlashAction.slash_one, SlashAction.slash_mul] using
      integrableOn_cusp_mixed_slash f g (A * mapGL ℝ (r i).val) 1
        (gamma0FundamentalDomain Q) (gamma0FundamentalDomain_volume_lt_top Q)
  have hs : petersson k (∑ i, (⇑f ∣[k] A) ∣[k] mapGL ℝ (r i).val) g =
      ∑ i, petersson k ((⇑f ∣[k] A) ∣[k] mapGL ℝ (r i).val) g := by
    funext τ
    simp [petersson, Finset.sum_apply, map_sum, Finset.sum_mul]
  unfold peterssonInner
  rw [hs]
  simp only [Finset.sum_apply]
  rw [integral_finsetSum _ (fun i _ => hD i)]
  rw [heckeTransversalDomain, integral_iUnion_ae (heckeTransversalDomain_tile_nullMeasurable r)
    (heckeTransversalDomain_tiles_aedisjoint r hr) hU, tsum_fintype]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_matrix_translate]
  apply integral_congr_ae
  exact ae_of_all _ fun τ => by
    have h := petersson_slash_SL k (⇑f ∣[k] A) g (r i).val τ
    rw [slash_Gamma0_eq g (r i).val (r i).property] at h
    exact h

/-- The corresponding right trace unfolds over exactly the same genuine tile union. -/
theorem peterssonInner_trace_right {ι : Type*} [Fintype ι] {Q : ℕ} [NeZero Q] {k : ℤ}
    (f g : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (A : GL (Fin 2) ℝ)
    (r : ι → Gamma0 Q) (hr : Function.Injective (fun i => gamma0ToRealProjective Q (r i))) :
    peterssonInner k (gamma0FundamentalDomain Q) f
        (∑ i, (⇑g ∣[k] A) ∣[k] mapGL ℝ (r i).val) =
      peterssonInner k (heckeTransversalDomain r) f (⇑g ∣[k] A) := by
  have h := congrArg (starRingEnd ℂ) (peterssonInner_trace_left g f A r hr)
  simpa only [peterssonInner_conj_symm] using h

end
end Dubon2026
