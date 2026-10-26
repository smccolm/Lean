import Dubon2026.SourceGammaOneComplexRatio
import Dubon2026.SourceGammaOneJCoordinate
import Dubon2026.SourceLaurentScalarIndependence

/-! DUB-17/18 -> arithmetic Gamma1 realization -> rational finite function
field. The existing Laurent coefficient-map independence theorem descends the
actual bounded complex norm relation to rational coefficients. It supplies a
nonzero relation for the literal original j and integral modular-form ratio.
The external independent-Laurent-series proof and alternate coordinate are
not duplicated. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open UpperHalfPlane Polynomial
open scoped MatrixGroups

private theorem aeval_fin_sum {p : Polynomial ℂ} {m : ℕ}
    (hp : p.natDegree ≤ m) (j : LaurentSeries ℂ) :
    Polynomial.aeval j p = ∑ b : Fin (m + 1), p.coeff (b : ℕ) • j ^ (b : ℕ) := by
  rw [Polynomial.aeval_eq_sum_range' (Nat.lt_succ_of_le hp)]
  simp only [Algebra.smul_def, LaurentSeries.algebraMap_apply, HahnSeries.C_mul_eq_smul]
  exact (Fin.sum_univ_eq_sum_range
    (fun b => p.coeff b • j ^ b) (m + 1)).symm

theorem exists_rational_j_relation
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)} [Γ.FiniteIndex]
    (hT : ModularGroup.T ∈ Γ) {k : ℤ}
    (f g : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k)
    {pf pg : PowerSeries ℤ} (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg)
    (hg0 : intSeriesC ℚ pg ≠ 0) :
    ∃ (m : ℕ)
      (d : Fin (Nat.card (𝒮ℒ ⧸
        (Γ : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) + 1) × Fin (m + 1) → ℚ),
      (∃ ib, d ib ≠ 0) ∧
      ∑ ib, d ib • (jq ^ (ib.2 : ℕ) *
        (intSeriesC ℚ pf / intSeriesC ℚ pg) ^ (ib.1 : ℕ)) = 0 := by
  classical
  have hgne : g ≠ 0 := by
    intro hz
    apply hg0
    have hpg : pg = 0 := by
      apply PowerSeries.map_injective (Int.castRingHom ℂ) Int.cast_injective
      rw [hg, hz, ModularForm.coe_zero, qExpansion_zero, map_zero]
    rw [hpg, intSeriesC_zero]
  obtain ⟨m, P, hdeg, ⟨i₀, hi₀⟩, hsum⟩ :=
    exists_complex_j_relation_of_ratio hT f g hgne
  let c := Nat.card (𝒮ℒ ⧸ (Γ : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ)
  let v : Fin (c + 1) × Fin (m + 1) → LaurentSeries ℚ :=
    fun ib => jq ^ (ib.2 : ℕ) *
      (intSeriesC ℚ pf / intSeriesC ℚ pg) ^ (ib.1 : ℕ)
  have hv : ∀ ib, coeffEmb ℂ (v ib) =
      jqModC ℂ ^ (ib.2 : ℕ) *
        ((qExpansion 1 (f : ℍ → ℂ) : LaurentSeries ℂ) /
          (qExpansion 1 (g : ℍ → ℂ) : LaurentSeries ℂ)) ^ (ib.1 : ℕ) := by
    intro ib
    simp only [v, map_mul, map_pow, map_div₀, coeffEmb_jq, coeffEmb_intSeries]
    change _ * (((HahnSeries.ofPowerSeries ℤ ℂ) (pf.map (Int.castRingHom ℂ))) /
      ((HahnSeries.ofPowerSeries ℤ ℂ) (pg.map (Int.castRingHom ℂ)))) ^ _ = _
    rw [hf, hg]
  have hc : ∑ ib : Fin (c + 1) × Fin (m + 1),
      (P ib.1).coeff (ib.2 : ℕ) • coeffEmb ℂ (v ib) = 0 := by
    simp_rw [hv]
    rw [Fintype.sum_prod_type, ← hsum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [aeval_fin_sum (hdeg i), Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← HahnSeries.C_mul_eq_smul, ← HahnSeries.C_mul_eq_smul, mul_assoc]
  let b := (P i₀).natDegree
  have hb : (P i₀).coeff b ≠ 0 := by
    rw [Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hi₀
  have hbmem : b < m + 1 := Nat.lt_succ_of_le
    ((Polynomial.le_natDegree_of_ne_zero hb).trans (hdeg i₀))
  have hdep : ¬ LinearIndependent ℂ (fun ib => coeffEmb ℂ (v ib)) := by
    rw [Fintype.not_linearIndependent_iff]
    exact ⟨fun ib => (P ib.1).coeff (ib.2 : ℕ), hc, ⟨(i₀, ⟨b, hbmem⟩), hb⟩⟩
  have hdepQ : ¬ LinearIndependent ℚ v := fun h =>
    hdep (linearIndependent_coeffMap_algebraMap ℂ h)
  rw [Fintype.not_linearIndependent_iff] at hdepQ
  obtain ⟨d, hd, ib, hib⟩ := hdepQ
  exact ⟨m, d, ⟨ib, hib⟩, hd⟩

end
end Dubon2026.SourceFunctionField.GammaOne
