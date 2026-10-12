import Dubon2026.LocalScalarCharacterDualRight
import Dubon2026.ContinuousTrivialDualityRightReduction

/-! # Original split finite coefficient cups have zero right annihilator

The local scalar premise is discharged by the proved Kummer theorem. A basis
of the actual finite coefficient space then detects every original continuous
H1 class. This is the split-module right side of DUB-17's local duality route;
arbitrary nontrivial actions and full perfectness remain separate obligations.
-/

namespace Dubon2026
noncomputable section

attribute [local instance] characterDualSequenceContinuousSMul

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsAlgClosed Ω]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (q : ℕ) [Fact q.Prime] (χ : Gal(Ω/K) →* ZMod q) (hχ : Continuous χ)
  (e : coefficientCharacterRep χ ≃+ galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)
  (heρ : ∀ g a, e ((coefficientCharacterRep χ).ρ g a) =
    (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q).ρ g (e a))
  [TopologicalSpace (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)]
  [DiscreteTopology (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]
  [TopologicalSpace (characterDualCoefficientRep (coefficientCharacterRep (1 : Gal(Ω/K) →* ZMod q)) χ)]
  [DiscreteTopology (characterDualCoefficientRep (coefficientCharacterRep (1 : Gal(Ω/K) →* ZMod q)) χ)]
  (A : Rep.{0} (ZMod q) Gal(Ω/K)) [Finite A] [TopologicalSpace A] [DiscreteTopology A]
  [TopologicalSpace (characterDualCoefficientRep A χ)] [DiscreteTopology (characterDualCoefficientRep A χ)]
  (htrivial : ∀ g a, A.ρ g a = a)
  (hA : Continuous (fun z : Gal(Ω/K) × A => A.ρ z.1 z.2))

include e heρ htrivial in
/-- The actual split finite-module cup has zero right annihilator. The original
local Kummer theorem supplies scalar nondegeneracy, and original basis
coordinates reconstruct the continuous coefficient coboundary. -/
theorem localTrivialCharacterDualH1Cup_right_zero (hq : (q : K) ≠ 0)
    (y : ContinuousRepresentationH1 (characterDualCoefficientRep A χ)
      (finiteCharacterDualAction_continuous A χ hA hχ))
    (hy : ∀ x, continuousCharacterDualH1Cup A χ hχ hA x y = 0) : y = 0 :=
  continuousTrivialCharacterDualH1Cup_right_zero A χ hχ (Module.finBasis (ZMod q) A)
    htrivial hA (localScalarCharacterDualH1Cup_right_injective K Ω q χ hχ e heρ hq) y hy

include e heρ htrivial in
/-- The original local character-dual cup is injective in its split finite
coefficient dual H1 argument. Scalar nondegeneracy is supplied by Kummer
and no primitive root in the base field is assumed. -/
theorem localTrivialCharacterDualH1Cup_right_injective (hq : (q : K) ≠ 0) :
    Function.Injective (continuousCharacterDualH1Cup A χ hχ hA).flip := by
  intro x y h
  apply sub_eq_zero.mp
  apply localTrivialCharacterDualH1Cup_right_zero K Ω q χ hχ e heρ A htrivial hA hq
  intro v
  rw [map_sub]
  exact sub_eq_zero.mpr (DFunLike.congr_fun h v)

end
end Dubon2026
