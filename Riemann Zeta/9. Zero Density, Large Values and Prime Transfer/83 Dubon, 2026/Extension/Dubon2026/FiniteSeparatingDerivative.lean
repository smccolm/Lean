import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Analysis.Complex.Basic

/-! # Norm derivatives from a genuine separating family in finite dimension -/

namespace Dubon2026

noncomputable section

/-- In a genuine finite-dimensional normed space, derivatives through an actual separating family of linear forms determine the original norm derivative. -/
theorem finiteSeparatingFamily_hasDerivAt {ι V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    (L : ι → V →ₗ[ℂ] ℂ) (hsep : ∀ v, (∀ i, L i v = 0) → v = 0)
    (f : ℂ → V) (v : V) (z : ℂ)
    (h : ∀ i, HasDerivAt (fun t => L i (f t)) (L i v) z) : HasDerivAt f v z := by
  have hdual (K : V →ₗ[ℂ] ℂ) : HasDerivAt (fun t => K (f t)) (K v) z := by
    have hm : K ∈ Submodule.span ℂ (Set.range L) := by
      apply FiniteDimensional.mem_span_of_iInf_ker_le_ker
      intro w hw
      have hz : w = 0 := hsep w (fun i => (Submodule.mem_iInf _).mp hw i)
      rw [hz]
      exact LinearMap.mem_ker.mpr (map_zero K)
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hm
    · rintro _ ⟨i, rfl⟩
      exact h i
    · simpa only [LinearMap.zero_apply] using hasDerivAt_const z (0 : ℂ)
    · intro K S _ _ hK hS
      simpa only [LinearMap.add_apply] using hK.add hS
    · intro c K _ hK
      simpa only [LinearMap.smul_apply, smul_eq_mul] using hK.const_mul c
  let b := Module.finBasis ℂ V
  have hd : HasDerivAt (fun t => ∑ i, (b.repr (f t) i) • b i)
      (∑ i, (b.repr v i) • b i) z :=
    HasDerivAt.fun_sum (fun i _ => (hdual (b.coord i)).smul_const (b i))
  simpa only [b.sum_repr] using hd

end
end Dubon2026
