import Dubon2026.LocalScalarCharacterDualNondegeneracy
import Dubon2026.LocalFieldPrimeKummerPerfectDescent

/-! # The original local scalar cup has zero right annihilator

The existing descended Kummer theorem and the same actual cup comparison
prove the opposite scalar annihilator statement needed for DUB-17 local duality.
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
/-- The original scalar character-dual cup has zero right annihilator when
the prime is nonzero in the original local field. The descended Kummer root
theorem discharges this conclusion without a base primitive-root hypothesis. -/
theorem localScalarCharacterDualH1Cup_right_zero (hq : (q : K) ≠ 0)
    (y : ContinuousRepresentationH1
      (characterDualCoefficientRep (coefficientCharacterRep (1 : Gal(Ω/K) →* ZMod q)) χ)
      (finiteCharacterDualAction_continuous (coefficientCharacterRep (1 : Gal(Ω/K) →* ZMod q)) χ
        (coefficientCharacterAction_continuous (1 : Gal(Ω/K) →* ZMod q) continuous_const) hχ))
    (hy : ∀ x, continuousCharacterDualH1Cup (coefficientCharacterRep (1 : Gal(Ω/K) →* ZMod q)) χ hχ
      (coefficientCharacterAction_continuous (1 : Gal(Ω/K) →* ZMod q) continuous_const) x y = 0) : y = 0 := by
  let T := Rep.of (1 : Representation ℤ Gal(Ω/K) (ZMod q))
  let R := galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q
  let hr := discreteGaloisRootAction_continuous (K := K) (Ω := Ω) q
  let e0 := scalarTrivialLineH1IntegerEquiv K Ω q
  let eD := scalarCharacterDualH1RootEquiv K Ω q χ hχ e heρ
  let e2 := scalarCharacterLineH2RootEquiv K Ω q χ hχ e heρ
  have hz : eD y = 0 := by
    apply localFieldPrimeKummer_root_eq_zero_of_cup_zero K Ω q hq
    intro ψ
    obtain ⟨x, hx⟩ := e0.surjective
      (Submodule.Quotient.mk (continuousGaloisFiniteCharacterOneCocycle q ψ))
    let flipCup := continuousH1Cup T R R (galoisRootExponentPairing q).flip
      (fun g a b => galoisRootExponentPairing_equivariant q g b a)
      continuous_of_discreteTopology continuous_snd hr hr
    have hp : flipCup (e0 x) (eD y) = 0 :=
      (scalarCharacterDualH1Cup_kummer K Ω q χ hχ e heρ x y).symm.trans
        ((congrArg e2 (hy x)).trans (map_zero e2))
    have hp' : flipCup (Submodule.Quotient.mk (continuousGaloisFiniteCharacterOneCocycle q ψ))
        (eD y) = 0 := (congrArg (fun t => flipCup t (eD y)) hx).symm.trans hp
    have hs := continuousH1Cup_skew R T R (galoisRootExponentPairing q)
      (galoisRootExponentPairing_equivariant q) continuous_of_discreteTopology
      hr continuous_snd hr (eD y) (Submodule.Quotient.mk (continuousGaloisFiniteCharacterOneCocycle q ψ))
    exact hs.trans ((congrArg (fun t : GaloisRootContinuousH2 (K := K) (Ω := Ω) q => -t) hp').trans
      neg_zero)
  exact eD.injective (hz.trans (map_zero eD).symm)

include e heρ in
/-- The actual local scalar character-dual cup map is injective in its
original dual H1 argument, using the proved descended Kummer nondegeneracy. -/
theorem localScalarCharacterDualH1Cup_right_injective (hq : (q : K) ≠ 0) :
    Function.Injective (continuousCharacterDualH1Cup
      (coefficientCharacterRep (1 : Gal(Ω/K) →* ZMod q)) χ hχ
      (coefficientCharacterAction_continuous (1 : Gal(Ω/K) →* ZMod q) continuous_const)).flip := by
  intro x y h
  apply sub_eq_zero.mp
  apply localScalarCharacterDualH1Cup_right_zero K Ω q χ hχ e heρ hq
  intro v
  rw [map_sub]
  exact sub_eq_zero.mpr (DFunLike.congr_fun h v)

end
end Dubon2026
