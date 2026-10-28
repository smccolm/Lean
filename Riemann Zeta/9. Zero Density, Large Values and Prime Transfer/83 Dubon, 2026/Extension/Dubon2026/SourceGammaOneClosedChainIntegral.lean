import Dubon2026.SourceWeightTwoSegmentPeriods
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

/-! DUB-17/18 -> original all-weight association -> actual Gamma1 Picard/H1 ->
Abel-Jacobi reciprocity. A closed integer chain on the ORIGINAL Gamma1 quotient
has its literal straight-segment cusp integrals represented by an element
of the actual original modular-period integer lattice, at every nonzero level.
No closed-chain, integral-normalization or lattice-membership premise remains. -/
namespace Dubon2026
noncomputable section
open UpperHalfPlane Matrix.SpecialLinearGroup CongruenceSubgroup Classical
open scoped MatrixGroups

theorem sourceGamma1_closed_chain_integrals_mem
    (N : ℕ) [NeZero N] (Z : (ℍ × ℍ) →₀ ℤ)
    (hZ : ∀ τ : ℍ, Z.sum (fun e m =>
      (if ∃ γ : Gamma1 N, γ.val • e.2 = τ then m else 0) -
        (if ∃ γ : Gamma1 N, γ.val • e.1 = τ then m else 0)) = 0) :
    ∃ L : Module.Dual ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) 2),
      L ∈ sourceWeightTwoIntegralLattice (Gamma1 N) ∧
      ∀ f, L f = Z.sum (fun e m => m •
        (∫ t in (0 : ℝ)..1,
          f (ofComplex ((e.1 : ℂ) + (t : ℂ) * ((e.2 : ℂ) - e.1))) *
            ((e.2 : ℂ) - e.1))) := by
  refine ⟨Z.sum (fun e m => m • sourceWeightTwoAlong (Gamma1 N) e.1 e.2),
    sourceWeightTwo_chain_period_mem_of_orbit_boundary (Gamma1 N) Z hZ, ?_⟩
  intro f
  simp only [Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply,
    sourceWeightTwoAlong_eq_segment_integral]

end
end Dubon2026
