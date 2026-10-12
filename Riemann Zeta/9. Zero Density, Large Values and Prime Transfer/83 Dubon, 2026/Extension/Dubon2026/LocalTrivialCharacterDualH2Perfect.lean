import Dubon2026.ContinuousTrivialCharacterDualH2Right
import Dubon2026.LocalCharacterDualScalarCup
import Mathlib.LinearAlgebra.PerfectPairing.Basic

/-! # The original split local H2/H0 endpoint is perfect

The proved local H2 invariant supplies a nonzero scalar class and normalizes
the original invariant-evaluation pairing. Both annihilators and the finite
invariant space give perfectness, supplying the split endpoint required in
DUB-17's remaining finite-module local-duality exact-sequence argument.
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

variable (A : Rep.{0} (ZMod q) Gal(Ω/K)) [Finite A] [TopologicalSpace A] [DiscreteTopology A]
  [TopologicalSpace (characterDualCoefficientRep A χ)] [DiscreteTopology (characterDualCoefficientRep A χ)]
  (hA : Continuous (fun z : Gal(Ω/K) × A => A.ρ z.1 z.2))

/-- The original local H2/invariant evaluation normalized by its actual
character-line H2 invariant, with the original invariant and cohomology domains. -/
def localCharacterDualH2InvariantScalarPairing :
    ContinuousRepresentationH2 (characterDualCoefficientRep A χ)
      (finiteCharacterDualAction_continuous A χ hA hχ) →ₗ[ZMod q]
      A.ρ.invariants →ₗ[ZMod q] ZMod q :=
  (continuousCharacterDualH2InvariantPairing A χ hχ hA).compr₂
    (localCharacterLineH2ScalarEquiv K Ω q χ hχ e heρ).toLinearMap

variable (htrivial : ∀ g a, A.ρ g a = a)

include htrivial in
/-- The normalized original endpoint pairing detects every split dual H2 class. -/
theorem localTrivialCharacterDualH2InvariantScalarPairing_left_injective :
    Function.Injective (localCharacterDualH2InvariantScalarPairing K Ω q χ hχ e heρ A hA) := by
  intro x y h
  apply continuousTrivialCharacterDualH2InvariantPairing_left_injective A χ hχ hA
    (Module.finBasis (ZMod q) A) htrivial
  apply LinearMap.ext
  intro w
  apply (localCharacterLineH2ScalarEquiv K Ω q χ hχ e heρ).injective
  exact DFunLike.congr_fun h w

include htrivial in
/-- The actual local invariant supplies a nonzero scalar H2 class, so the
normalized original pairing detects every invariant in the split module. -/
theorem localTrivialCharacterDualH2InvariantScalarPairing_right_injective :
    Function.Injective (localCharacterDualH2InvariantScalarPairing K Ω q χ hχ e heρ A hA).flip := by
  let e₂ := localCharacterLineH2ScalarEquiv K Ω q χ hχ e heρ
  have hc : e₂.symm 1 ≠ 0 := by
    intro hz
    have hzero : (1 : ZMod q) = 0 := (e₂.apply_symm_apply 1).symm.trans
      ((congrArg e₂ hz).trans (map_zero e₂))
    exact one_ne_zero hzero
  intro x y h
  apply continuousTrivialCharacterDualH2InvariantPairing_right_injective A χ hχ hA
    (Module.finBasis (ZMod q) A) htrivial (e₂.symm 1) hc
  apply LinearMap.ext
  intro z
  apply e₂.injective
  exact DFunLike.congr_fun h z

include htrivial in
/-- The original invariant-valued local H2/H0 pairing is perfect for split
finite prime-field coefficients. Finite dimensionality is needed only for the
original invariant space; no independent H2 finiteness assumption is introduced. -/
theorem localTrivialCharacterDualH2InvariantScalarPairing_isPerfPair :
    (localCharacterDualH2InvariantScalarPairing K Ω q χ hχ e heρ A hA).IsPerfPair := by
  haveI : Module.Finite (ZMod q) A.ρ.invariants := Module.Finite.of_finite
  exact LinearMap.IsPerfPair.of_injective'
    (localTrivialCharacterDualH2InvariantScalarPairing_left_injective K Ω q χ hχ e heρ A hA htrivial)
    (localTrivialCharacterDualH2InvariantScalarPairing_right_injective K Ω q χ hχ e heρ A hA htrivial)

end
end Dubon2026
