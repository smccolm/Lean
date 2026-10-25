import Dubon2026.SourceOriginalWeilCoverSimplePoleSpaceFinite

/-! DUB-17/18 -> auxiliary point division -> actual cover Abel converse ->
meromorphic loop generation for every permitted simple-pole differential.
Reuse the existing simple-pole subspace and finite residue-kernel argument
with the actual cover linear coefficients, residues and finite regular space.
A finite basis will allow one simultaneous integer loop formula to extend
by linearity to all allowed differentials; generation itself remains open. -/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve KaehlerDifferential
variable (N : ℕ) [NeZero N] (n : ℕ) (radicand : modularFunctionFieldOver N ℂ)
local notation "FF" => modularFunctionFieldOver N ℂ
local notation "EE" => Polynomial.SplittingField (Polynomial.X ^ n - Polynomial.C radicand : Polynomial FF)

theorem exists_cover_simple_pole_basis (S : Finset (Place ℂ EE)) :
    ∃ (d : ℕ) (b : Module.Basis (Fin d) ℂ (coverSimplePoleSpace N n radicand S)),
      ∀ θ : coverSimplePoleSpace N n radicand S, ∃ a : Fin d → ℂ,
        (θ : Ω[EE⁄ℂ]) = ∑ i, a i • (b i : Ω[EE⁄ℂ]) := by
  letI := finite_cover_simplePoleSpace N n radicand S
  let b := Module.finBasis ℂ (coverSimplePoleSpace N n radicand S)
  refine ⟨_, b, fun θ => ⟨fun i => b.repr θ i, ?_⟩⟩
  have h := congrArg Subtype.val (b.sum_repr θ)
  simpa only [Submodule.coe_sum, Submodule.coe_smul] using h.symm

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
