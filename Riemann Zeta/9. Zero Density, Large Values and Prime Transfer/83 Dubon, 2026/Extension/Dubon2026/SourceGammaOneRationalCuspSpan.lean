import Dubon2026.SourceGammaOneRationalTraceSpan

/-! DUB-17/18 -> actual Gamma1 differential realization -> rational Fourier
structure. Consume the proved original Fricke-image spanning set and its
actual cyclotomic conjugates, then trace-descent each generator to rational
Fourier forms. This proves rational spanning for the explicit source weight
balance and in particular for the geometric weight two at every nonzero level.
Bounded denominators and actual differential realization remain separate. -/
namespace Dubon2026.SourceFricke
noncomputable section
open UpperHalfPlane SourceFunctionField CongruenceSubgroup
open scoped Manifold ModularForm MatrixGroups

theorem span_gammaOne_rational_cuspForms_eq_top (N : ℕ) [NeZero N]
    (k : ℤ) (a b m : ℕ) (hk : k + 4 * a + 6 * b = 12 * m) :
    Submodule.span ℂ {f : CuspForm (Gamma1 N) k |
      ∀ n : ℕ, (qExpansion 1 f).coeff n ∈ Set.range ((↑) : ℚ → ℂ)} = ⊤ := by
  have hΓ : Gamma N ≤ Gamma1 N := by
    intro A hA
    simp_all [Gamma1_mem, Gamma_mem]
  apply top_unique
  rw [← span_cuspWeightImage_cyclotomic_fractions_eq_top N (Gamma1 N) hΓ k a b m hk]
  apply Submodule.span_le.mpr
  intro f hf
  let c : ℕ → kN N := fun n => ⟨(qExpansion 1 f).coeff n,
    gammaOne_cuspWeightImage_qExpansion_coeff_mem N k a b m f hf n⟩
  have hc : ∀ n : ℕ, (qExpansion 1 f).coeff n = (c n : ℂ) := fun _ => rfl
  apply gammaOne_mem_span_rational_of_conjugates N k f c hc
  intro σ
  obtain ⟨g, _, hg⟩ := exists_gammaOne_cuspForm_cyclotomic_conjugate N σ k a b m hk f hf c hc
  exact ⟨g, hg⟩

theorem span_gammaOne_weightTwo_rational_cuspForms_eq_top (N : ℕ) [NeZero N] :
    Submodule.span ℂ {f : CuspForm (Gamma1 N) 2 |
      ∀ n : ℕ, (qExpansion 1 f).coeff n ∈ Set.range ((↑) : ℚ → ℂ)} = ⊤ :=
  span_gammaOne_rational_cuspForms_eq_top N 2 1 1 1 (by norm_num)

end
end Dubon2026.SourceFricke
