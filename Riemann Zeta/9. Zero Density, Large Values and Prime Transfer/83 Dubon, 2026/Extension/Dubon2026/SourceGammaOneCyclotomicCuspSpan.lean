import Dubon2026.SourceCuspWeightImageFourier
import Dubon2026.SourceCuspFrickeRationalSpan
import Dubon2026.SourceGammaOneRatioClosure

/-! DUB-17/18 -> actual Gamma1 differential realization -> rational cusp
spanning. The original Gamma1 cusp-form space is spanned by forms whose
width-one Fourier coefficients lie in the original cyclotomic field.
The source weight balance is explicit; the geometric weight-two case is
unconditional in N. This is not the arithmetic Galois association theorem. -/
namespace Dubon2026.SourceFricke
noncomputable section
open UpperHalfPlane SourceFunctionField CongruenceSubgroup
open scoped Manifold ModularForm MatrixGroups

theorem gammaOne_cuspWeightImage_qExpansion_coeff_mem (N : ℕ) [NeZero N]
    (k : ℤ) (a b m : ℕ) (f : CuspForm (Gamma1 N) k)
    (hf : cuspWeightImage (Gamma1 N) k a b m f ∈ holomorphicCyclotomicFrickeFractions N)
    (n : ℕ) : (qExpansion 1 f).coeff n ∈ kN N := by
  have hp : (1 : ℝ) ∈ ((Gamma1 N) : Subgroup (GL (Fin 2) ℝ)).strictPeriods :=
    GammaOne.hper (by simp [Gamma1_mem, ModularGroup.T])
  letI : Fact (IsCusp OnePoint.infty ((Gamma1 N) : Subgroup (GL (Fin 2) ℝ))) :=
    ⟨Subgroup.isCusp_of_mem_strictPeriods zero_lt_one hp⟩
  have hper := SlashInvariantFormClass.periodic_comp_ofComplex f hp
  have hbd := ModularFormClass.bdd_at_infty f
  have hc := cuspWeightImage_qExpansion_coeff_mem (Gamma1 N) k a b m f hf
    (by simpa using hper.nat_mul N) hbd (n * N)
  rw [qExpansion_coeff_width _ (NeZero.ne N) hper f.holo' hbd] at hc
  simpa only [if_pos (dvd_mul_left N n), Nat.mul_div_cancel n (NeZero.pos N)] using hc

theorem span_gammaOne_cyclotomic_cuspForms_eq_top (N : ℕ) [NeZero N]
    (k : ℤ) (a b m : ℕ) (hk : k + 4 * a + 6 * b = 12 * m) :
    Submodule.span ℂ {f : CuspForm (Gamma1 N) k |
      ∀ n : ℕ, (qExpansion 1 f).coeff n ∈ kN N} = ⊤ := by
  have hΓ : Gamma N ≤ Gamma1 N := by
    intro A hA
    simp_all [Gamma1_mem, Gamma_mem]
  apply top_unique
  rw [← span_cuspWeightImage_cyclotomic_fractions_eq_top N (Gamma1 N) hΓ k a b m hk]
  exact Submodule.span_mono (fun f hf n =>
    gammaOne_cuspWeightImage_qExpansion_coeff_mem N k a b m f hf n)

theorem span_gammaOne_weightTwo_cyclotomic_cuspForms_eq_top (N : ℕ) [NeZero N] :
    Submodule.span ℂ {f : CuspForm (Gamma1 N) 2 |
      ∀ n : ℕ, (qExpansion 1 f).coeff n ∈ kN N} = ⊤ :=
  span_gammaOne_cyclotomic_cuspForms_eq_top N 2 1 1 1 (by norm_num)

end
end Dubon2026.SourceFricke
