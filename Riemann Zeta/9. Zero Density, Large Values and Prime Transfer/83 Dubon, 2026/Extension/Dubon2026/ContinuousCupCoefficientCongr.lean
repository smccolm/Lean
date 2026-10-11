import Dubon2026.ContinuousCohomologyCup
import Dubon2026.ContinuousCohomologyCoefficientCongr

/-! # Exact continuous cup compatibility under proved equality of coefficient actions -/

namespace Dubon2026
noncomputable section

variable {R G A B C : Type} [CommRing R] [Group G]
  [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
  [TopologicalSpace R] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
  [TopologicalSpace B] [IsTopologicalAddGroup B] [ContinuousSMul R B]
  [TopologicalSpace C] [IsTopologicalAddGroup C] [ContinuousSMul R C]
  {ρA σA : Representation R G A} {ρB σB : Representation R G B}
  {ρC σC : Representation R G C}

/-- Proved equalities of the three original coefficient actions transport the
same continuous cup product. The original pairing, topologies and cocycle
quotients are unchanged; only equal action expressions are identified. -/
theorem continuousH1Cup_coefficientCongr
    (eA : ρA = σA) (eB : ρB = σB) (eC : ρC = σC)
    (β : A →ₗ[R] B →ₗ[R] C)
    (hβρ : ∀ g x y, β (ρA g x) (ρB g y) = ρC g (β x y))
    (hβσ : ∀ g x y, β (σA g x) (σB g y) = σC g (β x y))
    (hcβ : Continuous (fun z : A × B => β z.1 z.2))
    (hρA : Continuous (fun z : G × A => ρA z.1 z.2))
    (hρB : Continuous (fun z : G × B => ρB z.1 z.2))
    (hρC : Continuous (fun z : G × C => ρC z.1 z.2))
    (hσA : Continuous (fun z : G × A => σA z.1 z.2))
    (hσB : Continuous (fun z : G × B => σB z.1 z.2))
    (hσC : Continuous (fun z : G × C => σC z.1 z.2))
    (x : ContinuousRepresentationH1 (Rep.of ρA) hρA)
    (y : ContinuousRepresentationH1 (Rep.of ρB) hρB) :
    continuousH2CoefficientCongr eC hρC hσC
        (continuousH1Cup (Rep.of ρA) (Rep.of ρB) (Rep.of ρC)
          β hβρ hcβ hρA hρB hρC x y) =
      continuousH1Cup (Rep.of σA) (Rep.of σB) (Rep.of σC)
        β hβσ hcβ hσA hσB hσC
        (continuousH1CoefficientCongr eA hρA hσA x)
        (continuousH1CoefficientCongr eB hρB hσB y) := by
  subst σA
  subst σB
  subst σC
  rfl

end
end Dubon2026
