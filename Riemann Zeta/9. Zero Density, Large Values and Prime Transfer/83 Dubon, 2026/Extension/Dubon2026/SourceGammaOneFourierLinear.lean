import Dubon2026.SourceGammaOneCyclotomicFourierConjugation

/-! DUB-17/18 -> actual Gamma1 differential realization -> rational Fourier
structure -> trace reconstruction. The original width-one Fourier coefficient
is a complex linear functional on actual Gamma1 cusp forms, and those
coefficients determine the form. These facts identify the finite trace sum. -/
namespace Dubon2026.SourceFricke
noncomputable section
open UpperHalfPlane SourceFunctionField CongruenceSubgroup
open scoped Manifold ModularForm MatrixGroups

theorem gammaOne_one_mem_strictPeriods (N : ℕ) :
    (1 : ℝ) ∈ ((Gamma1 N) : Subgroup (GL (Fin 2) ℝ)).strictPeriods :=
  GammaOne.hper (by simp [Gamma1_mem, ModularGroup.T])

/-- The actual width-one Fourier coefficient functional on Gamma1 cusp forms. -/
def gammaOneQCoeffLinear (N : ℕ) (k : ℤ) (n : ℕ) : CuspForm (Gamma1 N) k →ₗ[ℂ] ℂ where
  toFun f := (qExpansion 1 f).coeff n
  map_add' f g := by
    rw [CuspForm.coe_add,
      ModularForm.qExpansion_add zero_lt_one (gammaOne_one_mem_strictPeriods N) f g, map_add]
  map_smul' c f := by
    rw [CuspForm.IsGLPos.coe_smul,
      ModularForm.qExpansion_smul zero_lt_one (gammaOne_one_mem_strictPeriods N) c f,
      map_smul, RingHom.id_apply]

theorem gammaOne_eq_of_qExpansion_coeff_eq (N : ℕ) (k : ℤ)
    (f g : CuspForm (Gamma1 N) k)
    (he : ∀ n : ℕ, (qExpansion 1 f).coeff n = (qExpansion 1 g).coeff n) : f = g := by
  have hp := gammaOne_one_mem_strictPeriods N
  letI : Fact (IsCusp OnePoint.infty ((Gamma1 N) : Subgroup (GL (Fin 2) ℝ))) :=
    ⟨Subgroup.isCusp_of_mem_strictPeriods zero_lt_one hp⟩
  have hpf := SlashInvariantFormClass.periodic_comp_ofComplex f hp
  have hpg := SlashInvariantFormClass.periodic_comp_ofComplex g hp
  have hf := CuspTaylor.represents_qExpansion zero_lt_one hpf f.holo'
    (ModularFormClass.bdd_at_infty f)
  have hg := CuspTaylor.represents_qExpansion zero_lt_one hpg g.holo'
    (ModularFormClass.bdd_at_infty g)
  have heq : qExpansion 1 f = qExpansion 1 g := PowerSeries.ext he
  rw [heq] at hf
  exact DFunLike.ext _ _ (congrFun (hf.eq_upperHalfPlane hg zero_lt_one f.holo' g.holo' hpf hpg))

end
end Dubon2026.SourceFricke
