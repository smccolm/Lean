import Dubon2026.ContinuousH1AdditiveCoefficientEquiv
import Dubon2026.ContinuousH2AdditiveCoefficientEquiv
import Dubon2026.ContinuousCohomologyCup

/-! # Original cups under additive equivariant coefficient identifications

The integer-linear Kummer cup and the prime-field character-dual cup have
different scalar rings but actual additively identified coefficients. This
identity preserves their original cocycle values, closing the coefficient-ring
comparison needed to use the local Kummer theorem in DUB-17's split-module step.
-/

namespace Dubon2026
noncomputable section

variable {R S G : Type} [CommRing R] [CommRing S] [Group G]
  [TopologicalSpace R] [TopologicalSpace S] [TopologicalSpace G] [IsTopologicalGroup G]
  (A B C : Rep.{0} R G) (A' B' C' : Rep.{0} S G)
  [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
  [TopologicalSpace B] [IsTopologicalAddGroup B] [ContinuousSMul R B]
  [TopologicalSpace C] [IsTopologicalAddGroup C] [ContinuousSMul R C]
  [TopologicalSpace A'] [IsTopologicalAddGroup A'] [ContinuousSMul S A']
  [TopologicalSpace B'] [IsTopologicalAddGroup B'] [ContinuousSMul S B']
  [TopologicalSpace C'] [IsTopologicalAddGroup C'] [ContinuousSMul S C']
  (eA : A ≃+ A') (heA : Continuous eA) (heAi : Continuous eA.symm)
  (heAρ : ∀ g a, eA (A.ρ g a) = A'.ρ g (eA a))
  (eB : B ≃+ B') (heB : Continuous eB) (heBi : Continuous eB.symm)
  (heBρ : ∀ g b, eB (B.ρ g b) = B'.ρ g (eB b))
  (eC : C ≃+ C') (heC : Continuous eC) (heCi : Continuous eC.symm)
  (heCρ : ∀ g c, eC (C.ρ g c) = C'.ρ g (eC c))
  (β : A →ₗ[R] B →ₗ[R] C) (β' : A' →ₗ[S] B' →ₗ[S] C')
  (hβ : ∀ g a b, β (A.ρ g a) (B.ρ g b) = C.ρ g (β a b))
  (hβ' : ∀ g a b, β' (A'.ρ g a) (B'.ρ g b) = C'.ρ g (β' a b))
  (hcβ : Continuous (fun z : A × B => β z.1 z.2))
  (hcβ' : Continuous (fun z : A' × B' => β' z.1 z.2))
  (hpair : ∀ a b, eC (β a b) = β' (eA a) (eB b))
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  (hB : Continuous (fun z : G × B => B.ρ z.1 z.2))
  (hC : Continuous (fun z : G × C => C.ρ z.1 z.2))
  (hA' : Continuous (fun z : G × A' => A'.ρ z.1 z.2))
  (hB' : Continuous (fun z : G × B' => B'.ρ z.1 z.2))
  (hC' : Continuous (fun z : G × C' => C'.ρ z.1 z.2))

include hpair in
/-- The actual continuous cup commutes with the actual additive coefficient
identifications, preserving both original coefficient rings and all cocycle values. -/
theorem continuousH1Cup_additiveCoefficientEquiv
    (x : ContinuousRepresentationH1 A hA) (y : ContinuousRepresentationH1 B hB) :
    continuousH2AdditiveCoefficientEquiv C C' eC heC heCi heCρ hC hC'
      (continuousH1Cup A B C β hβ hcβ hA hB hC x y) =
      continuousH1Cup A' B' C' β' hβ' hcβ' hA' hB' hC'
        (continuousH1AdditiveCoefficientEquiv A A' eA heA heAi heAρ hA hA' x)
        (continuousH1AdditiveCoefficientEquiv B B' eB heB heBi heBρ hB hB' y) := by
  induction x using Submodule.Quotient.induction_on with
  | _ c =>
    induction y using Submodule.Quotient.induction_on with
    | _ u =>
      rw [continuousH1Cup_mk, continuousH2AdditiveCoefficientEquiv_mk,
        continuousH1AdditiveCoefficientEquiv_mk, continuousH1AdditiveCoefficientEquiv_mk,
        continuousH1Cup_mk]
      congr 1
      apply Subtype.ext
      apply Subtype.ext
      funext z
      change eC (β (c.val z.1) (B.ρ z.1 (u.val z.2))) =
        β' (eA (c.val z.1)) (B'.ρ z.1 (eB (u.val z.2)))
      rw [hpair, heBρ]

end
end Dubon2026
