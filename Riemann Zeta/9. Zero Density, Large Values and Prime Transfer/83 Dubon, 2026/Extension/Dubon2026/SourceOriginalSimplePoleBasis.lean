import Dubon2026.SourceOriginalSimplePoleSpaceFinite

/-! DUB-17/18 -> original Abel-Jacobi -> meromorphic loop-period generation.
Construct a finite basis spanning every actual differential with the required
simple poles. The following path argument can therefore prove simultaneous
integer loop coefficients for this finite family and extend by linearity.
No period-generation conclusion is asserted at this stage.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve KaehlerDifferential
variable (N : ℕ) [NeZero N]
local notation "F" => modularFunctionFieldOver N ℂ

theorem exists_original_simple_pole_basis (S : Finset (Place ℂ F)) :
    ∃ (d : ℕ) (b : Module.Basis (Fin d) ℂ (originalSimplePoleSpace N S)),
      ∀ θ : originalSimplePoleSpace N S, ∃ a : Fin d → ℂ,
        (θ : Ω[F⁄ℂ]) = ∑ i, a i • (b i : Ω[F⁄ℂ]) := by
  letI := finite_original_simplePoleSpace N S
  let b := Module.finBasis ℂ (originalSimplePoleSpace N S)
  refine ⟨_, b, fun θ => ⟨fun i => b.repr θ i, ?_⟩⟩
  have h := congrArg Subtype.val (b.sum_repr θ)
  simpa only [Submodule.coe_sum, Submodule.coe_smul] using h.symm

end
end Dubon2026.SourceFunctionField
