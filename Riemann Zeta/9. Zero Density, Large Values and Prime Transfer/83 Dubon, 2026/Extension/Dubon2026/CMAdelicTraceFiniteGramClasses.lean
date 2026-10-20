import Dubon2026.CMAdelicTraceGramDetBound
import Dubon2026.IntegralBilinearFiniteClasses

/-! # Finite Gram classes for the actual attached CM unitary lattices

The original source positivity, fixed matrix denominator, proved full
rank and uniform determinant bound now satisfy the integral reduction
theorem. Thus the actual attached trace lattices have finitely many
Gram representatives. For DUB-17's arithmetic double-coset finiteness,
finite compatible CM action structures and recovery of the unitary
double coset remain separate obligations.
-/

namespace Dubon2026

noncomputable section

open NumberField Matrix Module LinearMap.BilinForm
open scoped ComplexOrder

variable (K : Type) [Field K] [NumberField K] [IsCMField K]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The actual attached integral trace lattices have a fixed finite set of Gram representatives. -/
theorem cmAdelicTrace_finite_gram_classes (H : Matrix ι ι K)
    (hH : ∀ φ : K →+* ℂ, (φ.mapMatrix H).PosDef) :
    ∃ (d : ℤ) (_ : 0 < d) (hIntegral : ∀ i j, IsIntegral ℤ (d • H i j))
      (S : Finset (Matrix (Fin (Fintype.card ι * Module.finrank ℚ K))
        (Fin (Fintype.card ι * Module.finrank ℚ K)) ℤ)),
      ∀ g : cmFiniteAdelicUnitaryGroup K H,
        ∃ b : Basis (Fin (Fintype.card ι * Module.finrank ℚ K)) ℤ
          (numberFieldAdelicLattice K ι g.val),
          toMatrix b (cmAdelicLatticeIntegralTraceForm K H d hIntegral g) ∈ S := by
  obtain ⟨d, hd, hdi⟩ := numberField_exists_positive_integral_multiple
    (fun ij : ι × ι => H ij.1 ij.2)
  let hIntegral := fun i j => hdi (i, j)
  obtain ⟨m, _, hdet⟩ := cmAdelicTraceGramDet_uniform_bound K H hH d hd hIntegral
  let n := Fintype.card ι * Module.finrank ℚ K
  obtain ⟨S, hS⟩ := integralBilinForm_finite_gram_classes n (m ^ n)
  refine ⟨d, hd, hIntegral, S, ?_⟩
  intro g
  letI := numberFieldAdelicLattice_finite K ι g.val
  letI := numberFieldAdelicLattice_free K ι g.val
  let b := (Module.finBasis ℤ (numberFieldAdelicLattice K ι g.val)).reindex
    (finCongr (numberFieldAdelicLattice_finrank K ι g.val))
  apply hS (cmAdelicLatticeIntegralTraceForm K H d hIntegral g)
    (cmAdelicLatticeIntegralTraceForm_isSymm K H
      (cmHermitianPositiveMatrix_isHermitian K H hH) d hIntegral g)
    (cmAdelicLatticeIntegralTraceForm_posDef K H hH d hd hIntegral g) b
  simpa only [Fintype.card_fin] using hdet g b

end
end Dubon2026
