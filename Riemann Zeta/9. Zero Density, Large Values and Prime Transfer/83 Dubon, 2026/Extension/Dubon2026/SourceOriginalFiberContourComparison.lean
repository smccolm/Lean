import Dubon2026.SourceOriginalFiberContourSums

/-! DUB-17/18 -> original torsion cardinality -> Abel-Jacobi -> principal
divisor kernel -> constancy of the exact weighted fiber contour. These
functions are the literal contour sums on the actual original chart disks.
Their comparison, derivative and vanishing are proved separately under
the existing limits, retaining the exact coefficients and multiplicities.
Adapted from S_AlgebraicCurve_eventually_abelJacobiDiv_fibre_sub_mem_pathPeriodLattice,
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve Filter Set Metric KaehlerDifferential ComplexFiberContour
open scoped Topology
variable (N : ℕ) [NeZero N]
local notation "F" => modularFunctionFieldOver N ℂ
attribute [local instance] placeTopology

theorem original_fiber_sub_contour_mem {n : ℕ} (bb : Fin n → Ω[F⁄ℂ])
    (P₀ : Place ℂ F) (f : F) (h : Fin n → F) (t₀ : ℂ) (Z₀ : Finset (Place ℂ F))
    (Z : ℂ → Divisor ℂ F) (j : OriginalFiberIndexing N bb P₀ f h t₀ Z₀ Z)
    {t : ℂ} (ht : t ∈ ball t₀ j.ε) :
    abelJacobiDiv N bb P₀ (Z t) - originalFiberContourSum N bb P₀ f h t₀ Z₀ Z j t ∈
      pathPeriodLattice N bb := by
  classical
  let Λ := pathPeriodLattice N bb
  obtain ⟨⟨⟨O, ρ, Φ, hρ, hOdisj, htar, hOf, hΦd, hAJloc, hRan, hRc, hpunct⟩,
    r, ε, Zf, hε, hzeros, hr, hcb, hbb', hsph, hΦan, hΨan, hcirc', hZf, hI0, hIΦ⟩,
    hfibA, hfibB, hsurj, hmem, hinj, hmult⟩ := j

  set A : Place ℂ F → (Fin n → ℂ) := fun v => abelJacobiVec N bb P₀ v with hAdef
  set Φc : Place ℂ F → (Fin n → ℂ) := fun v i => Φ v i ((0 : ℂ)) with hΦcdef
  set m : Place ℂ F → ℂ → ℂ → ℕ := fun v t a =>
    analyticOrderNatAt (fun z => chartRead N v f z - t) a with hmdef
  set sy : Place ℂ F → ℂ → Place ℂ F := fun v a => (placeChart N v).symm a with hsydef

  have h2pi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  set k : ℂ := (2 * Real.pi * Complex.I : ℂ)⁻¹ with hkdef
  set L : ℂ → (Fin n → ℂ) := fun t => ∑ v ∈ Z₀,
      ((k * ∮ z in C((0 : ℂ), r v),
          (fun _ => (1 : ℂ)) z * deriv (chartRead N v f) z / (chartRead N v f z - t)) • (A v - Φc v) +
        k • fun i => ∮ z in C((0 : ℂ), r v),
          Φ v i z * deriv (chartRead N v f) z / (chartRead N v f z - t)) with hLdef
  set L' : ℂ → (Fin n → ℂ) := fun t => ∑ v ∈ Z₀,
      ((k * ∮ z in C((0 : ℂ), r v),
          deriv (fun _ => (1 : ℂ)) z / (chartRead N v f z - t)) • (A v - Φc v) +
        k • fun i => ∮ z in C((0 : ℂ), r v),
          deriv (Φ v i) z / (chartRead N v f z - t)) with hL'def

  change abelJacobiDiv N bb P₀ (Z t) - L t ∈ Λ
  have hAJ : abelJacobiDiv N bb P₀ (Z t) =
      ∑ v ∈ Z₀, ∑ a ∈ Zf v t, (m v t a : ℂ) • A (sy v a) := by
    rw [abelJacobiDiv_apply, Finsupp.sum,
      sum_eq_sum_sum (Z t).support Z₀ (fun v => Zf v t) sy (hsurj t ht) (hmem t ht) (hinj t ht)]
    refine Finset.sum_congr rfl fun v hv => Finset.sum_congr rfl fun a ha => ?_
    have hmu : (Z t) (sy v a) = (m v t a : ℤ) := hmult t ht v hv a ha
    rw [hmu, natCast_zsmul, Nat.cast_smul_eq_nsmul]
  have hL : L t = ∑ v ∈ Z₀, ((∑ a ∈ Zf v t, (m v t a : ℂ)) • (A v - Φc v) +
      fun i => ∑ a ∈ Zf v t, (m v t a : ℂ) * Φ v i a) := by
    simp only [hLdef]
    refine Finset.sum_congr rfl fun v hv => ?_
    rw [hI0 v hv t ht]
    congr 1
    · congr 1
      rw [← mul_assoc, hkdef, inv_mul_cancel₀ h2pi, one_mul]
      simp only [mul_one]
      rfl
    · funext i
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [hIΦ v hv t ht i, ← mul_assoc, hkdef, inv_mul_cancel₀ h2pi, one_mul]
  rw [hAJ, hL, ← Finset.sum_sub_distrib]
  refine Λ.sum_mem fun v hv => ?_
  have hterm : ∑ a ∈ Zf v t, (m v t a : ℂ) • A (sy v a) -
      ((∑ a ∈ Zf v t, (m v t a : ℂ)) • (A v - Φc v) +
        fun i => ∑ a ∈ Zf v t, (m v t a : ℂ) * Φ v i a) =
      ∑ a ∈ Zf v t, (m v t a : ℂ) • (A (sy v a) - A v - ((fun i => Φ v i a) - Φc v)) := by
    have hfun : (fun i => ∑ a ∈ Zf v t, (m v t a : ℂ) * Φ v i a) =
        ∑ a ∈ Zf v t, (m v t a : ℂ) • (fun i => Φ v i a) := by
      funext i
      simp [Finset.sum_apply, smul_eq_mul]
    rw [hfun, Finset.sum_smul]
    simp only [smul_sub, Finset.sum_sub_distrib]
    abel
  rw [hterm]
  refine Λ.sum_mem fun a ha => ?_
  obtain ⟨-, -, haball, -⟩ := hfibB t ht v hv a ha
  rw [Nat.cast_smul_eq_nsmul ℂ, ← natCast_zsmul]
  exact Λ.smul_mem _ (hAJloc v hv a (hbb' v haball))


end
end Dubon2026.SourceFunctionField.OriginalChart
