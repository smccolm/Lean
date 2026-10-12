import Dubon2026.LocalTrivialCharacterDualLeft
import Dubon2026.LocalTrivialCharacterDualRight
import Dubon2026.LocalCharacterDualScalarCup
import Dubon2026.LocalFieldFiniteScalarCoefficientH1
import Mathlib.LinearAlgebra.PerfectPairing.Basic

/-! # Perfectness of the original split local character-dual cup

The original Kummer pairing supplies both annihilators, and the proved finite
coefficient H1 theorem supplies finite dimensionality. This closes the split
prime-field coefficient case in the DUB-17 local duality dependency.
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


include htrivial in
/-- The original invariant-valued cup is injective in the split coefficient
H1 argument, by the proved local Kummer annihilator theorem. -/
theorem localTrivialCharacterDualH1ScalarCup_left_injective :
    Function.Injective (localCharacterDualH1ScalarCup K Ω q χ hχ e heρ A hA) := by
  intro x y h
  apply sub_eq_zero.mp
  apply localTrivialCharacterDualH1Cup_left_zero K Ω q χ hχ e heρ A htrivial hA
  intro v
  apply (localCharacterDualH1ScalarCup_eq_zero_iff K Ω q χ hχ e heρ A hA (x - y) v).mp
  rw [map_sub, LinearMap.sub_apply]
  exact sub_eq_zero.mpr (DFunLike.congr_fun h v)

include htrivial in
/-- The opposite map of the original invariant-valued cup is injective,
using descended Kummer nondegeneracy without base primitive roots. -/
theorem localTrivialCharacterDualH1ScalarCup_right_injective (hq : (q : K) ≠ 0) :
    Function.Injective (localCharacterDualH1ScalarCup K Ω q χ hχ e heρ A hA).flip := by
  intro x y h
  apply sub_eq_zero.mp
  apply localTrivialCharacterDualH1Cup_right_zero K Ω q χ hχ e heρ A htrivial hA hq
  intro v
  apply (localCharacterDualH1ScalarCup_eq_zero_iff K Ω q χ hχ e heρ A hA v (x - y)).mp
  rw [map_sub]
  exact sub_eq_zero.mpr (DFunLike.congr_fun h v)

include htrivial in
/-- The actual invariant-valued local character-dual pairing is perfect for
split finite prime-field coefficients. Both maps onto the actual linear duals
are bijective; H1 finiteness and both annihilators are proved, not assumed. -/
theorem localTrivialCharacterDualH1ScalarCup_isPerfPair (hq : (q : K) ≠ 0) :
    (localCharacterDualH1ScalarCup K Ω q χ hχ e heρ A hA).IsPerfPair := by
  haveI : Finite (characterDualCoefficientRep A χ) :=
    Finite.of_injective (fun ℓ : characterDualCoefficientRep A χ => (ℓ : A → ZMod q))
      DFunLike.coe_injective
  haveI := localField_finiteScalarCoefficientH1 q K Ω A hA hq
  haveI := localField_finiteScalarCoefficientH1 q K Ω (characterDualCoefficientRep A χ)
    (finiteCharacterDualAction_continuous A χ hA hχ) hq
  exact LinearMap.IsPerfPair.of_injective
    (localTrivialCharacterDualH1ScalarCup_left_injective K Ω q χ hχ e heρ A htrivial hA)
    (localTrivialCharacterDualH1ScalarCup_right_injective K Ω q χ hχ e heρ A htrivial hA hq)

end
end Dubon2026
