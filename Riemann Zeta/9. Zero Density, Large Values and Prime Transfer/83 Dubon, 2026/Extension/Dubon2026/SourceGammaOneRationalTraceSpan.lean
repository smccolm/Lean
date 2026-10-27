import Dubon2026.SourceCyclotomicTraceStructure
import Dubon2026.SourceGammaOneFourierLinear

/-! DUB-17/18 -> actual Gamma1 differential realization -> rational Fourier
structure -> trace descent. Actual same-level conjugate cusp forms yield
rational-coefficient trace sums. Native trace-dual basis reconstruction
expresses the original form in their complex span, avoiding a second
Dedekind-independence and matrix-invertibility development. -/
namespace Dubon2026.SourceFricke
noncomputable section
open UpperHalfPlane SourceFunctionField CongruenceSubgroup
open scoped Manifold ModularForm MatrixGroups

theorem gammaOne_mem_span_rational_of_conjugates (N : ℕ) [NeZero N] (k : ℤ)
    (f : CuspForm (Gamma1 N) k) (c : ℕ → kN N)
    (hc : ∀ n : ℕ, (qExpansion 1 f).coeff n = (c n : ℂ))
    (hconj : ∀ σ : kN N ≃ₐ[ℚ] kN N, ∃ g : CuspForm (Gamma1 N) k,
      ∀ n : ℕ, (qExpansion 1 g).coeff n = (σ (c n) : ℂ)) :
    f ∈ Submodule.span ℂ {g : CuspForm (Gamma1 N) k |
      ∀ n : ℕ, (qExpansion 1 g).coeff n ∈ Set.range ((↑) : ℚ → ℂ)} := by
  classical
  letI := finiteDimensional_kN N
  letI := isGalois_kN N
  choose fσ hfσ using hconj
  let T : kN N → CuspForm (Gamma1 N) k :=
    fun x => ∑ σ : kN N ≃ₐ[ℚ] kN N, (σ x : ℂ) • fσ σ
  have hTcoeff (x : kN N) (n : ℕ) :
      gammaOneQCoeffLinear N k n (T x) = (Algebra.trace ℚ (kN N) (x * c n) : ℂ) := by
    calc gammaOneQCoeffLinear N k n (T x)
        = ∑ σ : kN N ≃ₐ[ℚ] kN N, (σ x : ℂ) * (σ (c n) : ℂ) := by
            simp only [T, map_sum, map_smul, smul_eq_mul]
            exact Finset.sum_congr rfl (fun σ _ =>
              congrArg ((σ x : ℂ) * ·) (hfσ σ n))
      _ = algebraMap (kN N) ℂ (∑ σ : kN N ≃ₐ[ℚ] kN N, σ (x * c n)) := by
        rw [map_sum]
        exact Finset.sum_congr rfl (fun σ _ => by simp only [map_mul]; rfl)
      _ = (Algebra.trace ℚ (kN N) (x * c n) : ℂ) := by
        rw [← trace_eq_sum_automorphisms]
        simp only [eq_ratCast, map_ratCast]
  have hT (x : kN N) : ∀ n : ℕ,
      (qExpansion 1 (T x)).coeff n ∈ Set.range ((↑) : ℚ → ℂ) :=
    fun n => ⟨Algebra.trace ℚ (kN N) (x * c n), (hTcoeff x n).symm⟩
  let b := Module.finBasis ℚ (kN N)
  have hcomb : (∑ i, (b.traceDual i : ℂ) • T (b i)) = f := by
    apply gammaOne_eq_of_qExpansion_coeff_eq N k
    intro n
    calc (qExpansion 1 ((∑ i, (b.traceDual i : ℂ) • T (b i)) : CuspForm (Gamma1 N) k)).coeff n
        = ∑ i, (b.traceDual i : ℂ) * (Algebra.trace ℚ (kN N) (b i * c n) : ℂ) := by
            change gammaOneQCoeffLinear N k n (∑ i, (b.traceDual i : ℂ) • T (b i)) = _
            rw [map_sum]
            simp only [map_smul, smul_eq_mul]
            exact Finset.sum_congr rfl (fun i _ =>
              congrArg ((b.traceDual i : ℂ) * ·) (hTcoeff (b i) n))
      _ = (c n : ℂ) := by
        have hrepr := b.traceDual.sum_repr (c n)
        have ht (i) : b.traceDual.repr (c n) i = Algebra.trace ℚ (kN N) (b i * c n) := by
          rw [Module.Basis.traceDual_repr_apply]
          change Algebra.trace ℚ (kN N) (c n * b i) = _
          rw [mul_comm]
        simp only [ht, Algebra.smul_def] at hrepr
        have hcast := congrArg (algebraMap (kN N) ℂ) hrepr
        rw [map_sum] at hcast
        simpa only [map_mul, eq_ratCast, map_ratCast, mul_comm] using hcast
      _ = (qExpansion 1 f).coeff n := (hc n).symm
  rw [← hcomb]
  exact Submodule.sum_mem _ (fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span (hT (b i))))

end
end Dubon2026.SourceFricke
