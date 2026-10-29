import Dubon2026.SourceGammaOneResidueHecke
import Dubon2026.SourceGammaOneResidueCoordinateFinite
import Dubon2026.SourceFiniteCoordinateHom
import Dubon2026.SourceCurveFiniteCoordinateResidues

/-! DUB-17/18 -> original Gamma1 Frobenius correspondence -> finite
residue maps. The actual residue j is transcendental and finite upstairs;
the existing coordinate-exchange and finite-hom theorem apply directly to
both original residue Hecke maps. No residue map degree is assumed.
-/
namespace Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction
noncomputable section
open CongruenceSubgroup
variable {L : Type*} [Field L] [Algebra ℚ L] (A : ValuationSubring L)
  (M d : ℕ) [NeZero M] [NeZero d]
local notation "kk" => IsLocalRing.ResidueField A
local notation "Γ" => Gamma1 M
local notation "Δ" => Gamma1 M ⊓ Gamma0 (d * M)

theorem residue_hecke_hom_finite (φ : residueImage A Γ →ₐ[kk] residueImage A Δ) :
    φ.toRingHom.Finite := by
  let x := residueJCoordinate A Γ
  let t := residueJCoordinate A Δ
  have hT : ModularGroup.T ∈ Δ := by
    simp [Subgroup.mem_inf, Gamma1_mem, Gamma0_mem, ModularGroup.T]
  haveI : FiniteDimensional (IntermediateField.adjoin kk ({t} : Set (residueImage A Δ)))
      (residueImage A Δ) := (finite_residueCoordinate_and_degree_le A Δ hT).1
  have hφx : Transcendental kk (φ x) := by
    intro h
    exact transcendental_residueJCoordinate A Γ ((isAlgebraic_algHom_iff φ φ.injective).mp h)
  haveI := SourceCurve.finite_over_transcendental_of_finite_coordinate t hφx
  exact SourceCurve.finite_hom_of_finite_image_coordinate φ x

theorem residueHeckeAlpha_finite : (residueHeckeAlpha A M d).toRingHom.Finite :=
  residue_hecke_hom_finite A M d (residueHeckeAlpha A M d)

theorem residueHeckeBeta_finite : (residueHeckeBeta A M d).toRingHom.Finite :=
  residue_hecke_hom_finite A M d (residueHeckeBeta A M d)

end
end Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction
