import Dubon2026.SourceFrickeLaurentIntegralDescent
import Dubon2026.SourceFrickeFractionPeriodicity

/-! DUB-17/18 -> actual Gamma1 differential/cusp comparison -> rational
Fourier structure -> integral base change. An actual holomorphic Fricke
fraction with a complex monic j-relation has a cyclotomic monic j-relation.
The proof descends its literal Laurent series by the already proved
coefficient retraction, then uses analytic identity to recover equality
of the original functions. No cyclotomic relation or Fourier injectivity
is assumed. -/
namespace Dubon2026.SourceFricke
noncomputable section
open UpperHalfPlane SourceFunctionField
open scoped Manifold ModularForm MatrixGroups

theorem mdifferentiable_polynomial_jf (P : Polynomial ℂ) :
    MDiff (fun τ : ℍ => P.eval (JMultiplicity.jf τ)) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simpa only [Polynomial.eval_add] using hP.add hQ
  | monomial n c =>
    simpa only [Polynomial.eval_monomial] using
      mdifferentiable_const.mul (JMultiplicity.mdifferentiable_jf.pow n)

theorem exists_cyclotomic_monic_relation {N : ℕ} [NeZero N]
    {a b f : ℍ → ℂ} (ha : a ∈ cyclotomicLevelRing N) (hb : b ∈ cyclotomicLevelRing N)
    (hb0 : b ≠ 0) (hf : MDiff f) (hfrac : f * b = a)
    (d : ℕ) (p : Fin d → Polynomial ℂ)
    (hrel : ∀ τ : ℍ, f τ ^ d +
      ∑ i : Fin d, (p i).eval (JMultiplicity.jf τ) * f τ ^ (i : ℕ) = 0) :
    ∃ (e : ℕ) (q : Fin e → Polynomial (kN N)), ∀ τ : ℍ, f τ ^ e +
      ∑ i : Fin e, ((q i).map (algebraMap (kN N) ℂ)).eval (JMultiplicity.jf τ) *
        f τ ^ (i : ℕ) = 0 := by
  classical
  obtain ⟨X, hX, hXI⟩ := exists_integral_cyclotomic_laurent_of_monic ha hb hb0 hfrac d p hrel
  obtain ⟨e, q, hq⟩ := exists_polynomial_monic_relation_of_isIntegral hXI
  have hC := congrArg (coeffMap (algebraMap (kN N) ℂ)) hq
  simp only [map_add, map_pow, map_sum, map_mul, map_zero, coeffMap_aeval_jqNModC_kN] at hC
  let T : ℍ → ℂ := fun τ => f τ ^ e + ∑ i : Fin e,
    ((q i).map (algebraMap (kN N) ℂ)).eval (JMultiplicity.jf τ) * f τ ^ (i : ℕ)
  have hr := (hX.cusp_pow e).cusp_add (CuspTaylor.Represents.cusp_sum Finset.univ fun i _ =>
    ((represents_jqNModC N).cusp_aeval ((q i).map (algebraMap (kN N) ℂ))).cusp_mul
      (hX.cusp_pow i.val))
  change CuspTaylor.Represents _ (cuspFunction N T) at hr
  rw [hC] at hr
  have hsum : MDiff (fun τ : ℍ => ∑ i : Fin e,
      ((q i).map (algebraMap (kN N) ℂ)).eval (JMultiplicity.jf τ) * f τ ^ (i : ℕ)) := by
    have hs := MDifferentiable.sum (t := Finset.univ)
      (fun i _ => (mdifferentiable_polynomial_jf ((q i).map (algebraMap (kN N) ℂ))).mul
        (hf.pow i.val))
    convert hs using 1
    funext τ
    simp only [Finset.sum_apply, Pi.mul_apply, Pi.pow_apply]
  have hT : MDiff T := (hf.pow e).add hsum
  have hfp := periodic_cyclotomic_fraction ha hb hb0 hf hfrac
  have hTp : Function.Periodic (T ∘ ofComplex) N := by
    intro z
    have h1 := hfp z
    have h2 := periodic_jf_width N z
    simp only [Function.comp_apply] at h1 h2
    simp only [Function.comp_apply, T, h1, h2]
  have hz : CuspTaylor.Represents 0 (cuspFunction N (0 : ℍ → ℂ)) := by
    simpa only [map_zero] using CuspTaylor.represents_cusp_const N 0
  have he := hr.eq_upperHalfPlane hz (by exact_mod_cast NeZero.pos N)
    hT mdifferentiable_const hTp (by intro z; rfl)
  exact ⟨e, q, fun τ => congrFun he τ⟩

end
end Dubon2026.SourceFricke