import Dubon2026.SourceModularGaussSurjectivity

/-! DUB-17/18 -> original Frobenius/inertia -> good/place reduction ->
actual modular reduction data. The constructed Gauss valuation has a surjective
ring homomorphism onto the actual residue modular field, with its exact maximal
ideal kernel, literal action on constants, and a nonzero residue after scaling
every nonzero function. All residue-image and valuation inputs are proved.
Genus preservation and the place/divisor comparison are still required. -/
namespace Dubon2026.SourceFunctionField.GaussReduction
noncomputable section
open IntermediateField
variable {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L) (N : ℕ) [NeZero N]
variable (hNL : (N : L) ≠ 0) (hNk : (N : IsLocalRing.ResidueField A) ≠ 0)
local notation "FF" => modularFunctionFieldCoeff N L
local notation "kk" => IsLocalRing.ResidueField A
local notation "Fb" => modularFunctionFieldCoeff N kk

/-- Literal modular coefficient reduction from the constructed Gauss valuation ring. -/
def modularResidueHom : gaussRing A N →+* Fb :=
  (resHom A N).codRestrict (modularFunctionFieldCoeff N kk)
    (resHom_mem_coefficient_field A N hNL hNk)

theorem coe_modularResidueHom (f : gaussRing A N) :
    ((modularResidueHom A N hNL hNk f : Fb) : LaurentSeries kk) = resHom A N f := rfl

theorem modularResidueHom_ne_zero_iff (f : gaussRing A N) :
    modularResidueHom A N hNL hNk f ≠ 0 ↔ resHom A N f ≠ 0 := by
  rw [Ne, Ne, ← coe_modularResidueHom A N hNL hNk f, ZeroMemClass.coe_eq_zero]

theorem modularResidueHom_surjective : Function.Surjective (modularResidueHom A N hNL hNk) := by
  intro z
  obtain ⟨f, hf⟩ := exists_resHom_eq A N z.2
  exact ⟨f, Subtype.ext hf⟩

theorem ker_modularResidueHom : RingHom.ker (modularResidueHom A N hNL hNk) =
    IsLocalRing.maximalIdeal (gaussRing A N) := by
  ext f
  rw [RingHom.mem_ker, ← resHom_eq_zero_iff, ← coe_modularResidueHom A N hNL hNk f,
    ZeroMemClass.coe_eq_zero]

theorem modularResidueHom_algebraMap (a : A) (h : algebraMap L FF a ∈ gaussRing A N) :
    modularResidueHom A N hNL hNk ⟨algebraMap L FF a, h⟩ =
      algebraMap kk Fb (IsLocalRing.residue A a) :=
  Subtype.ext (resHom_algebraMap A N a h)

theorem exists_smul_mem_modularResidueHom (f : FF) (hf : f ≠ 0) :
    ∃ c : L, ∃ h : c • f ∈ gaussRing A N, modularResidueHom A N hNL hNk ⟨c • f, h⟩ ≠ 0 := by
  obtain ⟨c, h, hne⟩ := exists_smul_mem_gaussRing A N f hf
  exact ⟨c, h, (modularResidueHom_ne_zero_iff A N hNL hNk _).mpr hne⟩

end
end Dubon2026.SourceFunctionField.GaussReduction
