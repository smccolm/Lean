import Dubon2026.CuspPolynomialDecay
import Dubon2026.LatticeFundamentalBound
import Dubon2026.LatticeSpatialMeasurable

/-! # Actual integrable lattice majorants against cusp Petersson densities -/

namespace Dubon2026

open UpperHalfPlane ModularGroup MeasureTheory CongruenceSubgroup
open Matrix.SpecialLinearGroup
open scoped MatrixGroups ModularForm Pointwise

noncomputable section

/-- The genuine convergent lattice value times any slashed cusp density is bounded on the standard domain. -/
theorem exists_lattice_petersson_slash_bound_fd {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic]
    {k : ℤ} (f : CuspForm Γ k) (g : SL(2, ℤ)) {s : ℂ} (hs : 1 < s.re) :
    ∃ C : ℝ, 0 < C ∧ ∀ z ∈ fd,
      ‖latticeCompletedMellin z s * petersson k (⇑f ∣[k] g) (⇑f ∣[k] g) z‖ ≤ C := by
  obtain ⟨C, hC, hCb⟩ := exists_latticeCompletedMellin_bound_fd hs
  obtain ⟨D, hD, hDb⟩ := exists_petersson_slash_rpow_bound_fd f g s.re
  refine ⟨C * D, mul_pos hC hD, ?_⟩
  intro z hz
  rw [norm_mul]
  calc
    _ ≤ (C * z.im ^ s.re) * ‖petersson k (⇑f ∣[k] g) (⇑f ∣[k] g) z‖ :=
      mul_le_mul_of_nonneg_right (hCb z hz) (norm_nonneg _)
    _ = C * (z.im ^ s.re * ‖petersson k (⇑f ∣[k] g) (⇑f ∣[k] g) z‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hDb z hz) hC.le

/-- The actual completed lattice value times a cusp density is uniformly bounded over the whole higher-level domain. -/
theorem exists_lattice_petersson_bound_gamma0 {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) {s : ℂ} (hs : 1 < s.re) :
    ∃ C : ℝ, ∀ z ∈ gamma0FundamentalDomain Q,
      ‖latticeCompletedMellin z s * petersson k f f z‖ ≤ C := by
  letI : Fintype (SL(2, ℤ) ⧸ Gamma0 Q) := Subgroup.fintypeQuotientOfFiniteIndex
  choose C hC hb using (fun q : SL(2, ℤ) ⧸ Gamma0 Q =>
    exists_lattice_petersson_slash_bound_fd f (q.out)⁻¹ hs)
  refine ⟨∑ q, C q, ?_⟩
  intro z hz
  obtain ⟨q, hq⟩ := Set.mem_iUnion.mp hz
  obtain ⟨w, hw, rfl⟩ := Set.mem_smul_set.mp hq
  rw [latticeCompletedMellin_SL2 hs, ← petersson_slash_SL]
  exact (hb q w (fdo_subset_fd hw)).trans
    (Finset.single_le_sum (fun q _ => (hC q).le) (Finset.mem_univ q))

/-- The real lattice majorant needed for continuation under the actual cusp integral is integrable. -/
theorem integrableOn_lattice_petersson_gamma0 {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun z : ℍ => latticeCompletedMellin z s * petersson k f f z)
      (gamma0FundamentalDomain Q) := by
  obtain ⟨C, hC⟩ := exists_lattice_petersson_bound_gamma0 f hs
  have hm := (measurable_latticeCompletedMellin s).mul
    (petersson_continuous k (ModularFormClass.continuous f) (ModularFormClass.continuous f)).measurable
  apply IntegrableOn.of_bound (gamma0FundamentalDomain_volume_lt_top Q)
    hm.aestronglyMeasurable.restrict C
  filter_upwards [ae_restrict_mem₀ (isFundamentalDomain_gamma0 Q).nullMeasurableSet] with z hz
  exact hC z hz

/-- The literal product of the two norms is an integrable positive majorant over the actual level domain. -/
theorem integrableOn_norm_lattice_petersson_gamma0 {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun z : ℍ => ‖latticeCompletedMellin z s‖ * ‖petersson k f f z‖)
      (gamma0FundamentalDomain Q) := by
  simpa only [norm_mul] using (integrableOn_lattice_petersson_gamma0 f hs).norm

end
end Dubon2026
