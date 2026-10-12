import Dubon2026.ScalarCharacterDualKummerCohomology
import Dubon2026.LocalFieldKummerCharacterNondegeneracy
import Dubon2026.ContinuousFiniteCharacterH1
import Dubon2026.ContinuousCupSkewSymmetry

/-! # The actual local scalar character-dual cup has zero left annihilator

The proved local Kummer character nondegeneracy and the exact original cup
comparison discharge the scalar premise of the split-module left-annihilator
argument for DUB-17. The root identification is actual equivariant coefficient
data, already constructed for the original rational-prime cyclotomic line.
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

include e heρ in
/-- The original local scalar cup has zero left annihilator, by the proved
actual Kummer theorem and the sign-correct original continuous cup comparison. -/
theorem localScalarCharacterDualH1Cup_left_zero
    (x : ContinuousRepresentationH1 (coefficientCharacterRep (1 : Gal(Ω/K) →* ZMod q))
      (coefficientCharacterAction_continuous (1 : Gal(Ω/K) →* ZMod q) continuous_const))
    (hx : ∀ y, continuousCharacterDualH1Cup (coefficientCharacterRep (1 : Gal(Ω/K) →* ZMod q)) χ hχ
      (coefficientCharacterAction_continuous (1 : Gal(Ω/K) →* ZMod q) continuous_const) x y = 0) : x = 0 := by
  let T := Rep.of (1 : Representation ℤ Gal(Ω/K) (ZMod q))
  let R := galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q
  let hr := discreteGaloisRootAction_continuous (K := K) (Ω := Ω) q
  let e0 := scalarTrivialLineH1IntegerEquiv K Ω q
  let eD := scalarCharacterDualH1RootEquiv K Ω q χ hχ e heρ
  let e2 := scalarCharacterLineH2RootEquiv K Ω q χ hχ e heρ
  obtain ⟨ψ, hψ⟩ := continuousGaloisFiniteCharacterH1_surjective q (e0 x)
  have hψone : ψ = 1 := by
    apply localFieldKummer_character_eq_one_of_cup_zero K Ω q ψ
    intro z
    obtain ⟨y, rfl⟩ := eD.surjective z
    have hz : continuousH1Cup T R R (galoisRootExponentPairing q).flip
        (fun g a b => galoisRootExponentPairing_equivariant q g b a)
        continuous_of_discreteTopology continuous_snd hr hr (e0 x) (eD y) = 0 :=
      (scalarCharacterDualH1Cup_kummer K Ω q χ hχ e heρ x y).symm.trans
        ((congrArg e2 (hx y)).trans (map_zero e2))
    have hs := continuousH1Cup_skew R T R (galoisRootExponentPairing q)
      (galoisRootExponentPairing_equivariant q) continuous_of_discreteTopology
      hr continuous_snd hr (eD y) (Submodule.Quotient.mk (continuousGaloisFiniteCharacterOneCocycle q ψ))
    let flipCup := continuousH1Cup T R R (galoisRootExponentPairing q).flip
      (fun g a b => galoisRootExponentPairing_equivariant q g b a)
      continuous_of_discreteTopology continuous_snd hr hr
    have hz' : flipCup (Submodule.Quotient.mk (continuousGaloisFiniteCharacterOneCocycle q ψ))
        (eD y) = 0 :=
      (congrArg (fun t => flipCup t (eD y)) hψ).trans hz
    exact hs.trans ((congrArg (fun t : GaloisRootContinuousH2 (K := K) (Ω := Ω) q => -t) hz').trans
      neg_zero)
  have hc : continuousGaloisFiniteCharacterOneCocycle (K := K) (Ω := Ω) q 1 = 0 := by
    apply Subtype.ext
    apply Subtype.ext
    funext g
    rfl
  have hz : (Submodule.Quotient.mk (continuousGaloisFiniteCharacterOneCocycle q ψ) :
      ContinuousRepresentationH1 T continuous_snd) = 0 := by
    rw [hψone, hc]
    rfl
  exact e0.injective (hψ.symm.trans (hz.trans (map_zero e0).symm))

include e heρ in
/-- The actual local scalar character-dual cup map is injective, with its
local Kummer premise proved rather than assumed. -/
theorem localScalarCharacterDualH1Cup_left_injective :
    Function.Injective (continuousCharacterDualH1Cup
      (coefficientCharacterRep (1 : Gal(Ω/K) →* ZMod q)) χ hχ
      (coefficientCharacterAction_continuous (1 : Gal(Ω/K) →* ZMod q) continuous_const)) := by
  intro x y h
  apply sub_eq_zero.mp
  apply localScalarCharacterDualH1Cup_left_zero K Ω q χ hχ e heρ
  intro v
  rw [map_sub, LinearMap.sub_apply]
  exact sub_eq_zero.mpr (DFunLike.congr_fun h v)

end
end Dubon2026
