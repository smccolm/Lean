import Dubon2026.LocalCharacterDualH1Perfect
import Dubon2026.FiniteScalarTraceCup

/-! # Original extension-field local H1 annihilators from actual field trace

The proved prime-field perfectness detects the traced original cup. Genuine
coefficient H1 equivalences then detect both original extension-field H1
arguments. This removes the arbitrary-action annihilator premises for the
finite extension-field step of DUB-17's actual trace-zero local pairing.
-/

namespace Dubon2026
noncomputable section

attribute [local instance] characterDualSequenceContinuousSMul finiteScalarPrimeModule

variable {k : Type} [Field k] [Finite k]
  [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsAlgClosed Ω]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (q : ℕ) [Fact q.Prime] [CharP k q] [Algebra (ZMod q) k] (χ : Gal(Ω/K) →* ZMod q) (hχ : Continuous χ)
  (e : coefficientCharacterRep χ ≃+ galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)
  (heρ : ∀ g a, e ((coefficientCharacterRep χ).ρ g a) =
    (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q).ρ g (e a))
  [TopologicalSpace (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)]
  [DiscreteTopology (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

variable (A : Rep.{0} k Gal(Ω/K)) [Finite A] [TopologicalSpace A] [DiscreteTopology A]
  [TopologicalSpace (characterDualCoefficientRep A ((algebraMap (ZMod q) k).toMonoidHom.comp χ))]
  [DiscreteTopology (characterDualCoefficientRep A ((algebraMap (ZMod q) k).toMonoidHom.comp χ))]
  (hA : Continuous (fun z : Gal(Ω/K) × A => A.ρ z.1 z.2))

include e heρ in
/-- The actual extension-field cup detects its left original H1 argument,
using proved prime-field perfectness and the original field-trace comparison. -/
theorem localFiniteScalarCharacterDualH1Cup_left_injective (hq : (q : K) ≠ 0) :
    Function.Injective (continuousCharacterDualH1Cup A ((algebraMap (ZMod q) k).toMonoidHom.comp χ)
      (finiteScalarCharacter_continuous q χ hχ) hA) := by
  letI : TopologicalSpace (characterDualCoefficientRep (finiteScalarPrimeRep q A) χ) := ⊥
  letI : DiscreteTopology (characterDualCoefficientRep (finiteScalarPrimeRep q A) χ) := ⟨rfl⟩
  let e₂ := localCharacterLineH2ScalarEquiv K Ω q χ hχ e heρ
  intro x y h
  apply (finiteScalarPrimeH1Equiv q A hA).injective
  apply localCharacterDualH1ScalarCup_left_injective K Ω q χ hχ e heρ (finiteScalarPrimeRep q A) hA hq
  apply LinearMap.ext
  intro z
  obtain ⟨z, rfl⟩ := (finiteScalarTraceDualH1Equiv q A hA χ hχ).surjective z
  exact (congrArg e₂ (finiteScalarTraceCharacterH2Map_cup q A hA χ hχ x z).symm).trans
    ((congrArg (fun v => e₂ (finiteScalarTraceCharacterH2Map q χ hχ v)) (DFunLike.congr_fun h z)).trans
      (congrArg e₂ (finiteScalarTraceCharacterH2Map_cup q A hA χ hχ y z)))

include e heρ in
/-- The actual extension-field cup detects its right original H1 argument,
using proved prime-field perfectness and the original field-trace comparison. -/
theorem localFiniteScalarCharacterDualH1Cup_right_injective (hq : (q : K) ≠ 0) :
    Function.Injective (continuousCharacterDualH1Cup A ((algebraMap (ZMod q) k).toMonoidHom.comp χ)
      (finiteScalarCharacter_continuous q χ hχ) hA).flip := by
  letI : TopologicalSpace (characterDualCoefficientRep (finiteScalarPrimeRep q A) χ) := ⊥
  letI : DiscreteTopology (characterDualCoefficientRep (finiteScalarPrimeRep q A) χ) := ⟨rfl⟩
  let e₂ := localCharacterLineH2ScalarEquiv K Ω q χ hχ e heρ
  intro x y h
  apply (finiteScalarTraceDualH1Equiv q A hA χ hχ).injective
  apply localCharacterDualH1ScalarCup_right_injective K Ω q χ hχ e heρ (finiteScalarPrimeRep q A) hA hq
  apply LinearMap.ext
  intro z
  obtain ⟨z, rfl⟩ := (finiteScalarPrimeH1Equiv q A hA).surjective z
  exact (congrArg e₂ (finiteScalarTraceCharacterH2Map_cup q A hA χ hχ z x).symm).trans
    ((congrArg (fun v => e₂ (finiteScalarTraceCharacterH2Map q χ hχ v)) (DFunLike.congr_fun h z)).trans
      (congrArg e₂ (finiteScalarTraceCharacterH2Map_cup q A hA χ hχ z y)))

end
end Dubon2026
