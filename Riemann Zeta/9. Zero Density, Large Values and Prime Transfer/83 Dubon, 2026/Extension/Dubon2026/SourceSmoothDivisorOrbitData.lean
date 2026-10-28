import Dubon2026.SourceSmoothModularGeometry
import Dubon2026.SourceModularSmoothProjectiveRepresentatives
import Dubon2026.SourceModularStabilizerCharacter

/-! DUB-17/18 -> original all-weight arithmetic association -> Gamma1 Picard/H1
-> Abel-Jacobi converse -> analytic reciprocity -> invariant comparison V.
A base point outside the finite union of original modular orbits is chosen.
Actual stabilizer finiteness is inherited from the existing full integral
stabilizer theorem; actual orbit fibers are counted by stabilizers.
These are exactly the multiplicity and cancellation inputs of the dipole
orbit product. No divisor realization or period identity is assumed.
Adapted from the pinned Apache-2.0 scope-889 construction. -/
namespace Dubon2026.SourceSmoothDivisor
noncomputable section
open UpperHalfPlane hiding I
open MeasureTheory Filter Complex Set
open scoped MatrixGroups Topology Real

/-- The stabilizer of any integral subgroup is contained in the proved finite full stabilizer. -/
scoped instance finiteStabilizer (Γ : Subgroup SL(2, ℤ)) (τ : ℍ) :
    Finite (MulAction.stabilizer Γ τ) := by
  letI := SourceFunctionField.StabilizerCharacter.finite_stabilizer τ
  refine Finite.of_injective
    (fun a => (⟨a.val.val, a.property⟩ : MulAction.stabilizer SL(2, ℤ) τ)) ?_
  intro a b h
  have hh := congrArg (fun x : MulAction.stabilizer SL(2, ℤ) τ => x.val) h
  exact Subtype.ext (Subtype.ext hh)

theorem exists_basePoint (S : Finset ℍ) :
    ∃ b : ℍ, ∀ s ∈ S, ∀ γ : SL(2, ℤ), γ • s ≠ b := by
  set B : Set ℝ := ⋃ s ∈ S, Set.range fun γ : SL(2, ℤ) => (γ • s).im with hB
  have hBc : B.Countable := Set.Countable.biUnion S.countable_toSet fun s _ => Set.countable_range _
  have hne : (Set.Ioi (1 : ℝ) \ B).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty, Set.diff_eq_empty] at h
    have h1 : volume (Set.Ioi (1 : ℝ)) ≤ volume B := measure_mono h
    rw [hBc.measure_zero, Real.volume_Ioi] at h1
    exact absurd h1 (by simp)
  obtain ⟨y, hy1, hyB⟩ := hne
  have hy1' : 1 < y := hy1
  let b : ℍ := ⟨(y : ℂ) * Complex.I, by simpa using (show 0 < y by linarith)⟩
  refine ⟨b, fun s hs γ h => hyB ?_⟩
  refine Set.mem_iUnion₂.2 ⟨s, hs, γ, ?_⟩
  show (γ • s).im = y
  rw [h]
  simp [b]

variable {Γ : Subgroup SL(2, ℤ)}

theorem card_fibre_eq_card_stabilizer (τ s : ℍ) (δ₀ : Γ) (h₀ : (δ₀ : SL(2, ℤ)) • τ = s) :
    Nat.card {δ : Γ // (δ : SL(2, ℤ)) • τ = s} = Nat.card (MulAction.stabilizer Γ s) := by
  refine Nat.card_congr ⟨fun δ => ⟨δ.1 * δ₀⁻¹, ?_⟩, fun σ => ⟨σ.1 * δ₀, ?_⟩, ?_, ?_⟩
  · rw [MulAction.mem_stabilizer_iff]
    have hδ := δ.2
    have key : ((δ.1 * δ₀⁻¹ : Γ) : SL(2, ℤ)) • ((δ₀ : SL(2, ℤ)) • τ) = s := by
      rw [Subgroup.coe_mul, mul_smul, Subgroup.coe_inv, inv_smul_smul, hδ]
    rwa [h₀] at key
  · show ((σ.1 * δ₀ : Γ) : SL(2, ℤ)) • τ = s
    rw [Subgroup.coe_mul, mul_smul, h₀]; exact σ.2
  · intro δ; simp
  · intro σ; simp

theorem card_fibre_eq_zero (τ s : ℍ) (h : ∀ δ : Γ, (δ : SL(2, ℤ)) • τ ≠ s) :
    Nat.card {δ : Γ // (δ : SL(2, ℤ)) • τ = s} = 0 := by
  haveI : IsEmpty {δ : Γ // (δ : SL(2, ℤ)) • τ = s} := ⟨fun δ => h δ.1 δ.2⟩
  exact Nat.card_of_isEmpty

end
end Dubon2026.SourceSmoothDivisor
