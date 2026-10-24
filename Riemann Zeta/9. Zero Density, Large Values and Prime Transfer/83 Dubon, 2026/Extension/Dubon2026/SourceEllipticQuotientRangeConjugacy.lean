import Dubon2026.SourceEllipticCompositeQuotientJ
import Dubon2026.SourceIntegralCoordinateRootConjugacy
import Mathlib.AlgebraicGeometry.EllipticCurve.IsomOfJ

/-! The actual composite quotient range is invariant under automorphisms
fixing the original j-invariant. Native equality-of-j model classification
and the proved field/model compatibilities derive the needed range statement.
With native modular-root conjugacy this supplies only the transitive-support
input used by the finite-fiber counting argument; multiplicity invariance
is unnecessary. The DUB-17/18 all-level bijection remains to be assembled. -/

namespace Dubon2026.SourceEllipticVelu
open WeierstrassCurve SourceFunctionField SourceFunctionField.IntegralJCoordinate
open scoped IntermediateField
noncomputable section
variable {F : Type*} [Field F] [DecidableEq F] [IsAlgClosed F]

/-- Every actual quotient value transports under an automorphism fixing the original j-invariant. -/
theorem cyclicQuotientJ_mem_range_map
    (W : WeierstrassCurve F) [W.IsElliptic] (N : ℕ) (hN : (N : F) ≠ 0)
    (σ : F ≃+* F) (hσ : σ W.j = W.j)
    {y : F} (hy : y ∈ Set.range (cyclicQuotientJ W N hN)) :
    σ y ∈ Set.range (cyclicQuotientJ W N hN) := by
  obtain ⟨H, rfl⟩ := hy
  let V := W.map σ.toRingHom
  let H' := primeCyclicKernelMap σ.toRingHom W N H
  obtain ⟨C, hC⟩ := exists_variableChange_of_j_eq V W (by
    dsimp only [V]
    rw [map_j]
    exact hσ)
  let J := cyclicKernelVariableChange C V N H'
  have hv : ∀ (U : WeierstrassCurve F) (hU : C • V = U) (he : U.IsElliptic),
      @cyclicQuotientJ F _ _ _ U he N hN (hU ▸ J) = σ (cyclicQuotientJ W N hN H) := by
    rintro U rfl he
    rw [cyclicQuotientJ_variableChange]
    exact cyclicQuotientJ_map σ.toRingHom W N hN H
  exact ⟨hC ▸ J, hv W hC inferInstance⟩

/-- Membership in the actual quotient range is constant on the original modular-root orbit. -/
theorem modular_roots_quotient_range_iff
    {K : Type*} [Field K] [IsAlgClosed K] [Algebra K F]
    (W : WeierstrassCurve F) [W.IsElliptic] (N : ℕ) [NeZero N]
    (hNK : (N : K) ≠ 0) (hNF : (N : F) ≠ 0)
    (hj : Transcendental K W.j) [Algebra.IsAlgebraic K⟮W.j⟯ F]
    {r s : F} (hr : (relationAtSeed (modularPolynomial N) W.j).IsRoot r)
    (hs : (relationAtSeed (modularPolynomial N) W.j).IsRoot s) :
    r ∈ Set.range (cyclicQuotientJ W N hNF) ↔ s ∈ Set.range (cyclicQuotientJ W N hNF) := by
  obtain ⟨σ, hσ⟩ := modularPolynomial_coordinate_roots_conjugate N hNK W.j hj hr hs
  have hfix : σ W.j = W.j := σ.commutes (IntermediateField.AdjoinSimple.gen K W.j)
  have hfix' : σ.symm W.j = W.j := by
    apply σ.injective
    rw [σ.apply_symm_apply, hfix]
  constructor
  · intro h
    rw [← hσ]
    exact cyclicQuotientJ_mem_range_map W N hNF σ.toRingEquiv hfix h
  · intro h
    have he := cyclicQuotientJ_mem_range_map W N hNF σ.symm.toRingEquiv hfix' h
    change σ.symm s ∈ Set.range (cyclicQuotientJ W N hNF) at he
    rwa [← hσ, σ.symm_apply_apply] at he

end
end Dubon2026.SourceEllipticVelu
