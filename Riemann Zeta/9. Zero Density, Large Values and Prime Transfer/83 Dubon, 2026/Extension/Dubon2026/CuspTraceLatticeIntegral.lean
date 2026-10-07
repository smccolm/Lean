import Dubon2026.CongruenceTraceDomain
import Dubon2026.CuspCosetTrace
import Dubon2026.LatticeCuspMajorant
import Dubon2026.PeterssonSlashTransport

/-! # Actual finite trace of the completed lattice-Petersson integral -/

namespace Dubon2026

open UpperHalfPlane ModularGroup Matrix.SpecialLinearGroup CongruenceSubgroup MeasureTheory
open scoped MatrixGroups Pointwise ModularForm

noncomputable section

/-- A finite integral-coset tiling has genuinely finite hyperbolic volume. -/
theorem integralSubgroupDomain_volume_lt_top (H : Subgroup SL(2, ℤ)) [Fintype (SL(2, ℤ) ⧸ H)] :
    (volume : Measure ℍ) (integralSubgroupDomain H) < ⊤ := by
  unfold integralSubgroupDomain
  refine lt_of_le_of_lt (measure_iUnion_le _) ?_
  rw [tsum_fintype]
  refine ENNReal.sum_lt_top.mpr fun q _ => ?_
  rw [measure_smul]
  exact lt_of_le_of_lt (measure_mono fdo_subset_fd) hyperbolicMeasure_fd_lt_top

/-- Genuine cusp decay bounds the literal lattice-Petersson integrand on the entire finite coset tiling. -/
theorem exists_lattice_petersson_bound_integralSubgroup {H : Subgroup SL(2, ℤ)} [H.FiniteIndex]
    [Fintype (SL(2, ℤ) ⧸ H)] {k : ℤ} (f : CuspForm (H.map (mapGL ℝ)) k)
    {s : ℂ} (hs : 1 < s.re) :
    ∃ C : ℝ, ∀ z ∈ integralSubgroupDomain H,
      ‖latticeCompletedMellin z s * petersson k f f z‖ ≤ C := by
  choose C hC hb using (fun q : SL(2, ℤ) ⧸ H => exists_lattice_petersson_slash_bound_fd f q.out⁻¹ hs)
  refine ⟨∑ q, C q, ?_⟩
  intro z hz
  obtain ⟨q, hq⟩ := Set.mem_iUnion.mp hz
  obtain ⟨w, hw, rfl⟩ := Set.mem_smul_set.mp hq
  rw [latticeCompletedMellin_SL2 hs, ← petersson_slash_SL]
  exact (hb q w (fdo_subset_fd hw)).trans
    (Finset.single_le_sum (fun q _ => (hC q).le) (Finset.mem_univ q))

/-- The genuine weighted lattice-cusp integral is absolutely integrable over its actual finite-index subgroup domain. -/
theorem integrableOn_lattice_petersson_integralSubgroup {H : Subgroup SL(2, ℤ)} [H.FiniteIndex]
    [Fintype (SL(2, ℤ) ⧸ H)] (hH : Subgroup.center SL(2, ℤ) ≤ H) {k : ℤ}
    (f : CuspForm (H.map (mapGL ℝ)) k) {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun z : ℍ => latticeCompletedMellin z s * petersson k f f z) (integralSubgroupDomain H) := by
  obtain ⟨C, hC⟩ := exists_lattice_petersson_bound_integralSubgroup f hs
  have hm := (measurable_latticeCompletedMellin s).mul
    (petersson_continuous k (ModularFormClass.continuous f) (ModularFormClass.continuous f)).measurable
  apply IntegrableOn.of_bound (integralSubgroupDomain_volume_lt_top H) hm.aestronglyMeasurable.restrict C
  filter_upwards [ae_restrict_mem₀ (isFundamentalDomain_integralSubgroup H hH).nullMeasurableSet] with z hz
  exact hC z hz

/-- Every actual summand of the completed lattice trace is absolutely integrable on the full-level domain. -/
theorem integrableOn_lattice_cuspCosetFamily {N : ℕ} [NeZero N] {H : Subgroup SL(2, ℤ)}
    (hH : Gamma N ≤ H) {k : ℤ} (f : CuspForm (H.map (mapGL ℝ)) k) (q : SL(2, ℤ) ⧸ H)
    {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun z : ℍ => latticeCompletedMellin z s *
      petersson k (cuspCosetFamily hH f q) (cuspCosetFamily hH f q) z) fdo := by
  letI : H.FiniteIndex := Subgroup.finiteIndex_of_le hH
  obtain ⟨C, _, hb⟩ := exists_lattice_petersson_slash_bound_fd f q.out⁻¹ hs
  have hm := (measurable_latticeCompletedMellin s).mul
    (petersson_continuous k (ModularFormClass.continuous (cuspCosetFamily hH f q))
      (ModularFormClass.continuous (cuspCosetFamily hH f q))).measurable
  apply IntegrableOn.of_bound (lt_of_le_of_lt (measure_mono fdo_subset_fd) hyperbolicMeasure_fd_lt_top)
    hm.aestronglyMeasurable.restrict C
  filter_upwards [ae_restrict_mem isOpen_fdo.measurableSet] with z hz
  exact hb z (fdo_subset_fd hz)

/-- The original subgroup integral equals the literal finite cusp trace on the full-level domain. -/
theorem lattice_cusp_integral_eq_trace {N : ℕ} [NeZero N] {H : Subgroup SL(2, ℤ)}
    [Fintype (SL(2, ℤ) ⧸ H)] (hH : Gamma N ≤ H) (hCenter : Subgroup.center SL(2, ℤ) ≤ H)
    {k : ℤ} (f : CuspForm (H.map (mapGL ℝ)) k) {s : ℂ} (hs : 1 < s.re) :
    (∫ z : ℍ in integralSubgroupDomain H, latticeCompletedMellin z s * petersson k f f z) =
      ∫ z : ℍ in fdo, latticeCompletedMellin z s *
        ∑ q : SL(2, ℤ) ⧸ H, petersson k (cuspCosetFamily hH f q) (cuspCosetFamily hH f q) z := by
  letI : H.FiniteIndex := Subgroup.finiteIndex_of_le hH
  have hi := integrableOn_lattice_petersson_integralSubgroup hCenter f hs
  rw [integralSubgroupDomain] at hi ⊢
  rw [integral_iUnion_ae (fun q : SL(2, ℤ) ⧸ H =>
    isOpen_fdo.measurableSet.nullMeasurableSet.smul q.out⁻¹)
    (integralSubgroupDomain_tiles_aedisjoint H hCenter) hi, tsum_fintype]
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ (fun q _ => integrableOn_lattice_cuspCosetFamily hH f q hs)]
  apply Finset.sum_congr rfl
  intro q _
  change (∫ z : ℍ in (fun w : ℍ => q.out⁻¹ • w) '' ModularGroup.fdo, _) = _
  rw [(measurePreserving_smul q.out⁻¹ (volume : Measure ℍ)).setIntegral_image_emb
    (measurableEmbedding_const_smul _) _ _]
  apply integral_congr_ae
  filter_upwards with z
  rw [latticeCompletedMellin_SL2 hs, petersson_cuspCosetFamily]

end
end Dubon2026
