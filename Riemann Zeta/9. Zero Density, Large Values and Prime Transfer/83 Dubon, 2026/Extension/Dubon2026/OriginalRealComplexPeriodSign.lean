import Dubon2026.OriginalRealComplexNormQuotient
import Dubon2026.CyclicGaloisH2PeriodSurjective
import Dubon2026.GaloisUnitCharacterCarryPeriod
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # The actual real carry class under the original period-sign equivalence

The original cyclic cocycle period and the existing complex norm quotient
give an equivalence from actual real-place unit H2 to the two-element sign
group. The formula retains the literal character carry and original real
unit. This is the real cohomology input needed to turn DUB-17's proved
principal automorphism product into the all-primary invariant comparison.
-/
namespace Dubon2026
noncomputable section
open scoped BigOperators

/-- The actual real/complex extension has the original degree two. -/
local instance originalRealPeriodQuadratic : Algebra.IsQuadraticExtension ℝ ℂ :=
  ⟨Complex.finrank_real_complex⟩

/-- Actual complex conjugation generates the actual real absolute Galois group. -/
theorem originalRealComplexConjugation_generates :
    ∀ σ : Gal(ℂ/ℝ), σ ∈ Subgroup.zpowers Complex.conjAe := by
  intro σ
  rcases Complex.real_algHom_eq_id_or_conj σ.toAlgHom with h | h
  · have hσ : σ = 1 := by
      ext z
      exact congrArg (fun f : ℂ →ₐ[ℝ] ℂ => f z) h
    rw [hσ]
    exact (Subgroup.zpowers Complex.conjAe).one_mem
  · have hσ : σ = Complex.conjAe := by
      ext z
      exact congrArg (fun f : ℂ →ₐ[ℝ] ℂ => f z) h
    rw [hσ]
    exact Subgroup.mem_zpowers _

/-- The period of the original real generator is exactly two. -/
theorem originalRealComplexConjugation_order : orderOf Complex.conjAe = 2 := by
  rw [orderOf_eq_card_of_forall_mem_zpowers originalRealComplexConjugation_generates,
    IsGalois.card_aut_eq_finrank, Complex.finrank_real_complex]

variable [TopologicalSpace (Rep.ofAlgebraAutOnUnits ℝ ℂ)]
    [DiscreteTopology (Rep.ofAlgebraAutOnUnits ℝ ℂ)]

attribute [local instance] IsCyclic.commGroup

/-- The original period map, with actual complex conjugation as generator,
is an equivalence onto the quotient by actual complex norms. -/
def originalRealComplexPeriodNormEquiv :
    GaloisUnitContinuousH2 (K := ℝ) (Ω := ℂ) ≃ₗ[ℤ]
      (Additive ℝˣ ⧸ LinearMap.range (galoisUnitFieldNormLinear (K := ℝ) (L := ℂ))) := by
  haveI := originalRealComplexNormQuotient_card.1
  exact LinearEquiv.ofBijective
    (cyclicGaloisH2PeriodNormMap Complex.conjAe originalRealComplexConjugation_generates)
    (cyclicGaloisH2PeriodNormMap_bijective Complex.conjAe originalRealComplexConjugation_generates)

/-- The exact original real unit H2 is identified with its actual period sign. -/
def originalRealComplexH2SignEquiv :
    GaloisUnitContinuousH2 (K := ℝ) (Ω := ℂ) ≃ₗ[ℤ] Additive ℤˣ :=
  originalRealComplexPeriodNormEquiv.trans originalRealComplexNormQuotientEquiv

omit [TopologicalSpace (Rep.ofAlgebraAutOnUnits ℝ ℂ)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits ℝ ℂ)] in
/-- The existing norm-quotient sign equivalence retains the original real unit. -/
theorem originalRealComplexNormQuotientEquiv_mk (u : Additive ℝˣ) :
    originalRealComplexNormQuotientEquiv (Submodule.Quotient.mk u) =
      Additive.ofMul (originalRealUnitsSign u.toMul) := by
  rfl

/-- The actual H2 sign is the sign of its literal descended cyclic period. -/
theorem originalRealComplexH2SignEquiv_mk
    (c : continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits ℝ ℂ)) :
    originalRealComplexH2SignEquiv (Submodule.Quotient.mk c) =
      Additive.ofMul (originalRealUnitsSign
        (galoisUnitCyclicPeriodBase Complex.conjAe originalRealComplexConjugation_generates c).toMul) := by
  change originalRealComplexNormQuotientEquiv
    (cyclicGaloisH2PeriodNormMap Complex.conjAe originalRealComplexConjugation_generates
      (Submodule.Quotient.mk c)) = _
  rw [cyclicGaloisH2PeriodNormMap_mk, originalRealComplexNormQuotientEquiv_mk]

/-- An actual finite-character carry at the real place has its genuine
two-step carry sum times the sign of the original real unit. -/
theorem originalRealComplexH2SignEquiv_characterCarry
    {n : ℕ} [NeZero n] (χ : Gal(ℂ/ℝ) →* Multiplicative (ZMod n)) (u : ℝˣ) :
    originalRealComplexH2SignEquiv
      (Submodule.Quotient.mk (galoisUnitCharacterCarryCocycle χ u)) =
      (∑ i ∈ Finset.range 2,
        zmodAdditionCarry (i • (χ Complex.conjAe).toAdd) (χ Complex.conjAe).toAdd) •
        Additive.ofMul (originalRealUnitsSign u) := by
  rw [originalRealComplexH2SignEquiv_mk, galoisUnitCharacterCarryCocycle_period,
    originalRealComplexConjugation_order]
  exact map_nsmul originalRealUnitsSign.toAdditive _ _

end
end Dubon2026
