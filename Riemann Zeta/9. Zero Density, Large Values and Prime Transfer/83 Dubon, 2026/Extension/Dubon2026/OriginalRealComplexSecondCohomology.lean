import Dubon2026.OriginalRealComplexNormQuotient
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # The original real/complex unit H2 has order two

The existing original norm-quotient/continuous-H2 equivalence and the proved
continuous/algebraic comparison consume the actual sign quotient. This is
the archimedean local coefficient calculation needed by DUB-17's idele formula.
-/

namespace Dubon2026
noncomputable section

/-- The original real/complex Galois unit coefficient has finite H2 of order two. -/
theorem originalRealComplex_second_cohomology_order :
    Finite (groupCohomology (Rep.ofAlgebraAutOnUnits ℝ ℂ) 2) ∧
      Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits ℝ ℂ) 2) = 2 := by
  haveI : Algebra.IsQuadraticExtension ℝ ℂ := ⟨Complex.finrank_real_complex⟩
  letI := IsCyclic.commGroup (α := Gal(ℂ/ℝ))
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits ℝ ℂ) := ⊥
  haveI : DiscreteTopology (Rep.ofAlgebraAutOnUnits ℝ ℂ) := ⟨rfl⟩
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Gal(ℂ/ℝ))
  let e : (Additive ℝˣ ⧸ LinearMap.range (galoisUnitFieldNormLinear (K := ℝ) (L := ℂ))) ≃ₗ[ℤ]
      groupCohomology (Rep.ofAlgebraAutOnUnits ℝ ℂ) 2 :=
    (continuousCyclicGaloisNormQuotientEquiv g hg).trans
      (continuousDiscreteH2Equiv (Rep.ofAlgebraAutOnUnits ℝ ℂ)
        (discreteGaloisUnitAction_continuous (K := ℝ) (Ω := ℂ)))
  obtain ⟨hfin, hcard⟩ := originalRealComplexNormQuotient_card
  haveI := hfin
  exact ⟨Finite.of_equiv _ e.toEquiv, (Nat.card_congr e.symm.toEquiv).trans hcard⟩

end
end Dubon2026
