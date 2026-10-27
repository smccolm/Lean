import Dubon2026.SourceCyclotomicCuspFourierTransport
import Dubon2026.SourceGammaOneCyclotomicCuspSpan

/-! DUB-17/18 -> actual Gamma1 differential realization -> rational Fourier
structure -> coefficientwise Galois conjugation. The analytic conjugate is
an actual same-level, same-weight cusp form, and its width-one coefficients
are exactly the original cyclotomic automorphism applied to those of the
given form. The source weight balance and Fricke-image premise are explicit;
the already proved spanning theorem supplies forms satisfying that premise. -/
namespace Dubon2026.SourceFricke
noncomputable section
open UpperHalfPlane SourceFunctionField CongruenceSubgroup
open scoped Manifold ModularForm MatrixGroups

theorem CyclotomicConjugates.qExpansion_coeff {N : ℕ}
    {σ : kN N ≃ₐ[ℚ] kN N} {F G : ℍ → ℂ} (hFG : CyclotomicConjugates σ F G)
    (hF : CuspTaylor.Represents (qExpansion N F : LaurentSeries ℂ) (cuspFunction N F))
    (hG : CuspTaylor.Represents (qExpansion N G : LaurentSeries ℂ) (cuspFunction N G))
    (n : ℕ) : ∃ c : kN N,
      (qExpansion N F).coeff n = (c : ℂ) ∧ (qExpansion N G).coeff n = (σ c : ℂ) := by
  obtain ⟨A, hA, hAG⟩ := hFG
  refine ⟨A.coeff (n : ℤ), ?_, ?_⟩
  · have he := congrArg (fun X : LaurentSeries ℂ => X.coeff (n : ℤ)) (hA.eq_series hF)
    simpa only [coeffMap_coeff, HahnSeries.ofPowerSeries_apply_coeff] using he.symm
  · have he := congrArg (fun X : LaurentSeries ℂ => X.coeff (n : ℤ)) (hAG.eq_series hG)
    simpa only [coeffMap_coeff, HahnSeries.ofPowerSeries_apply_coeff] using he.symm

theorem CyclotomicConjugates.gammaOne_qExpansion_coeff {N : ℕ} [NeZero N]
    {σ : kN N ≃ₐ[ℚ] kN N} {k : ℤ} {f g : CuspForm (Gamma1 N) k}
    (hfg : CyclotomicConjugates σ f g) (c : ℕ → kN N)
    (hc : ∀ n : ℕ, (qExpansion 1 f).coeff n = (c n : ℂ)) :
    ∀ n : ℕ, (qExpansion 1 g).coeff n = (σ (c n) : ℂ) := by
  have hp : (1 : ℝ) ∈ ((Gamma1 N) : Subgroup (GL (Fin 2) ℝ)).strictPeriods :=
    GammaOne.hper (by simp [Gamma1_mem, ModularGroup.T])
  letI : Fact (IsCusp OnePoint.infty ((Gamma1 N) : Subgroup (GL (Fin 2) ℝ))) :=
    ⟨Subgroup.isCusp_of_mem_strictPeriods zero_lt_one hp⟩
  have hpf := SlashInvariantFormClass.periodic_comp_ofComplex f hp
  have hpg := SlashInvariantFormClass.periodic_comp_ofComplex g hp
  have hbf := ModularFormClass.bdd_at_infty f
  have hbg := ModularFormClass.bdd_at_infty g
  have hN : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  intro n
  obtain ⟨d, hfd, hgd⟩ := hfg.qExpansion_coeff
    (CuspTaylor.represents_qExpansion hN (by simpa using hpf.nat_mul N) f.holo' hbf)
    (CuspTaylor.represents_qExpansion hN (by simpa using hpg.nat_mul N) g.holo' hbg) (n * N)
  rw [qExpansion_coeff_width _ (NeZero.ne N) hpf f.holo' hbf] at hfd
  rw [qExpansion_coeff_width _ (NeZero.ne N) hpg g.holo' hbg] at hgd
  simp only [if_pos (dvd_mul_left N n), Nat.mul_div_cancel n (NeZero.pos N)] at hfd hgd
  have hd : d = c n := Subtype.ext (hfd.symm.trans (hc n))
  simpa only [hd] using hgd

theorem exists_gammaOne_cuspForm_cyclotomic_conjugate (N : ℕ) [NeZero N]
    (σ : kN N ≃ₐ[ℚ] kN N) (k : ℤ) (a b m : ℕ)
    (hk : k + 4 * a + 6 * b = 12 * m) (f : CuspForm (Gamma1 N) k)
    (hf : cuspWeightImage (Gamma1 N) k a b m f ∈ holomorphicCyclotomicFrickeFractions N)
    (c : ℕ → kN N) (hc : ∀ n : ℕ, (qExpansion 1 f).coeff n = (c n : ℂ)) :
    ∃ g : CuspForm (Gamma1 N) k,
      cuspWeightImage (Gamma1 N) k a b m g ∈ holomorphicCyclotomicFrickeFractions N ∧
      ∀ n : ℕ, (qExpansion 1 g).coeff n = (σ (c n) : ℂ) := by
  obtain ⟨g, hg, hfg⟩ :=
    exists_gammaOne_cuspWeightImage_cyclotomic_conjugate N σ k a b m hk f hf
  exact ⟨g, hg, (hfg.cusp_forms (Gamma1 N) k a b m f g).gammaOne_qExpansion_coeff c hc⟩

end
end Dubon2026.SourceFricke
