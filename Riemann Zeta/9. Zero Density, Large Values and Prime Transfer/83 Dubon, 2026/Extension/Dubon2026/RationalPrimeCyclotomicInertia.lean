import Dubon2026.AlgebraicLocalInertiaRestriction
import Dubon2026.LocalFieldNormUniformizerResidue
import Dubon2026.NormLocalTotalInertia
import Dubon2026.RationalPrimeOriginalCyclotomicNorm
import Dubon2026.RationalPrimeCyclotomicCharacter
import Dubon2026.RationalPrimeOriginalNormPrime
import Dubon2026.SpectralFiniteExtensionLocalField
import Mathlib.Analysis.Normed.Algebra.Basic

/-! The original local cyclotomic character is surjective on original
inertia. Native cyclotomic irreducibility and the norm of zeta minus one
give residue degree one; native inertia lifting then realizes every power
action in the original algebraic closure. This constructs the fixed tame
quotient required by Dubon Theorem 2.6's auxiliary local deformation rings. -/

namespace Dubon2026
noncomputable section
open scoped ValuativeRel NNReal

attribute [local instance] rationalPrimeLocalField_charZero
  rationalPrimeOriginalNorm rationalPrimeOriginalNorm_ultrametric
  rationalPrimeOriginalClosureNorm rationalPrimeOriginalClosureNormedAlgebra
  rationalPrimeOriginalClosureNorm_ultrametric algebraicLocalIntegerAction
attribute [local instance 1100] rationalPrimeOriginalNormedField

/-- Every power automorphism of prime-order roots of unity occurs in the
original norm inertia at that same odd rational prime. -/
theorem rationalPrimeCyclotomicCharacter_inertia_surjective
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) [NeZero p] (u : (ZMod p)ˣ) :
    ∃ g, g ∈ rationalPrimeNormInertia p hp ∧
      rationalPrimeCyclotomicCharacter p hp p g = u := by
  letI : Fact p.Prime := ⟨hp⟩
  let K := rationalPrimeLocalField p hp
  let Ω := rationalPrimeLocalClosure p hp
  letI : Field K := (inferInstance : NontriviallyNormedField K).toField
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω p
  let F := originalPrimitiveRootStage K Ω hζ
  let E := F.toIntermediateField
  letI : NormedField E := (inferInstance : NontriviallyNormedField E).toNormedField
  letI : Field E := (inferInstance : NormedField E).toField
  letI : NormedAlgebra K E := inferInstance
  letI : Algebra K E := (inferInstance : NormedAlgebra K E).toAlgebra
  letI : @IsGalois K (inferInstance : NontriviallyNormedField K).toField E
      (inferInstance : NormedField E).toField (inferInstance : NormedAlgebra K E).toAlgebra := by
    exact F.isGalois
  letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra K
  haveI : ProperSpace E := FiniteDimensional.proper K E
  haveI : CompleteSpace E := inferInstance
  letI : NormedAlgebra E Ω := ⟨fun x y => by
    change ‖(x : Ω) * y‖ ≤ ‖(x : Ω)‖ * ‖y‖
    exact (norm_mul _ _).le⟩
  letI : ValuativeRel E := ValuativeRel.ofValuation (NormedField.valuation (K := E))
  letI : (NormedField.valuation (K := E)).Compatible := Valuation.Compatible.ofValuation _
  letI : (NormedField.valuation (K := K)).Compatible := localFieldOriginalNorm_compatible K
  letI : IsNonarchimedeanLocalField E := normValuation_isNonarchimedeanLocalField E
  letI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation E) := ⟨by
    intro x y
    rw [← (ValuativeRel.valuation K).vle_iff_le,
      (NormedField.valuation (K := K)).vle_iff_le]
    change _ ↔ ValuativeRel.valuation E (algebraMap K E x) ≤
      ValuativeRel.valuation E (algebraMap K E y)
    rw [← (ValuativeRel.valuation E).vle_iff_le,
      (NormedField.valuation (K := E)).vle_iff_le]
    change ‖x‖₊ ≤ ‖y‖₊ ↔ ‖algebraMap K E x‖₊ ≤ ‖algebraMap K E y‖₊
    exact Iff.of_eq ((congrArg₂ (fun a b : ℝ≥0 => a ≤ b)
      (nnnorm_algebraMap' E x) (nnnorm_algebraMap' E y)).symm)⟩
  let ζE : E := originalPrimitiveRootStageRoot K Ω hζ
  have hζE : IsPrimitiveRoot ζE p := originalPrimitiveRootStageRoot_isPrimitive K Ω hζ
  letI : IsCyclotomicExtension {p} K E := originalPrimitiveRootStage_isCyclotomic K Ω hζ
  have hirr : Irreducible (Polynomial.cyclotomic p K) := by
    simpa using rationalPrimePowerCyclotomic_irreducible p hp 0
  have hn : Algebra.norm K (ζE - 1) = (p : K) :=
    hζE.norm_sub_one_of_prime_ne_two' hirr hp2
  have hz : ζE - 1 ≠ 0 := by
    intro hz
    rw [hz, Algebra.norm_zero] at hn
    exact (Nat.cast_ne_zero.mpr hp.ne_zero : (p : K) ≠ 0) hn.symm
  let v := Units.mk0 (ζE - 1) hz
  have hnv : Units.map (Algebra.norm K (S := E)) v = rationalPrimePrimeUnit p hp :=
    Units.ext hn
  have ho : localFieldUnitOrder K
      (Additive.ofMul (Units.map (Algebra.norm K (S := E)) v)) = 1 := by
    rw [hnv]
    exact rationalPrimeLocalField_prime_order p hp
  have hI : algebraicLocalInertia K E = ⊤ :=
    algebraicLocal_inertia_eq_top_of_residue_surjective K E
      (localField_residue_surjective_of_norm_order_one K E v ho)
  let e := IsCyclotomicExtension.autEquivPow E hirr
  let σ := e.symm u
  obtain ⟨g, hg, hr⟩ := algebraicLocal_inertia_exists_restriction_lift K E Ω σ (by rw [hI]; trivial)
  refine ⟨g, hg, ?_⟩
  have hpower : g ζ = ζ ^ (u : ZMod p).val := by
    have he : hζE.autToPow K σ = u := by
      rw [hζE.autToPow_eq_modularCyclotomicCharacter p K,
        ← (IsCyclotomicExtension.zeta_spec p K E).autToPow_eq_modularCyclotomicCharacter p K]
      exact e.apply_symm_apply u
    have hσ := hζE.autToPow_spec K σ
    rw [he] at hσ
    have h := congrArg (algebraMap E Ω) hσ
    rw [map_pow] at h
    exact ((g.restrictNormal_commutes E ζE).symm.trans
      (congrArg (algebraMap E Ω) (DFunLike.congr_fun hr ζE))).trans h.symm
  have hc := rationalPrimeCyclotomicCharacter_apply_root p hp p g hζ
  apply Units.ext
  apply ZMod.val_injective
  exact hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) (hc.symm.trans hpower)

end
end Dubon2026
