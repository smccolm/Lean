import Dubon2026.FiniteScalarTraceCohomology
import Dubon2026.ContinuousScalarH2Coordinates

/-! # Original scalar-extension H2 classes are detected by prime-field coordinates

Extend an original prime-field class by the actual characteristic map.
Every coordinate of a scalar multiple is the corresponding coefficient
coordinate times that same original class. Together with proved continuous
coordinate detection, this supplies the scalar invariant normalization over
the finite extension field in DUB-17's local trace pairing.
-/

namespace Dubon2026
noncomputable section

attribute [local instance] finiteScalarPrimeModule characterDualSequenceContinuousSMul
attribute [local instance 1100] Rep.hV2

variable {k G : Type} [Field k] [Group G]
  (q : ℕ) [Fact q.Prime] [CharP k q] [Algebra (ZMod q) k]
  [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
  [TopologicalSpace G] [IsTopologicalGroup G]
  (χ : G →* ZMod q) (hχ : Continuous χ)

/-- The existing prime restriction of the genuine extended character,
retained as a representation so its own scalar instance is selected. -/
abbrev finiteScalarCharacterPrimeRep : Rep (ZMod q) G :=
  finiteScalarPrimeRep q (coefficientCharacterRep ((algebraMap (ZMod q) k).toMonoidHom.comp χ)) 

/-- The scalar line uses the module stored by its actual prime restriction. -/
local instance finiteScalarLinePrimeModule : Module (ZMod q) k :=
  AddCommGroup.zmodModule (fun a => by
    rw [← Nat.cast_smul_eq_nsmul k, CharP.cast_eq_zero k q, zero_smul])

attribute [local instance 1100] finiteScalarLinePrimeModule

omit [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
  [TopologicalSpace G] [IsTopologicalGroup G] in
/-- The original prime-field scalar action agrees with the actual algebra
map, even for the existing additive prime-field restriction instance. -/
theorem finiteScalarCharacterPrime_smul (r : ZMod q) (a : k) :
    @SMul.smul (ZMod q) k
      (finiteScalarCharacterPrimeRep q χ (k := k)).hV2.toDistribMulAction.toDistribSMul.toSMul r a =
      algebraMap (ZMod q) k r * a := by
  rw [← ZMod.intCast_zmod_cast r, map_intCast]
  exact (@Int.cast_smul_eq_zsmul (ZMod q) k _ _
    (finiteScalarCharacterPrimeRep q χ (k := k)).hV2 r.cast a).trans (zsmul_eq_mul _ _)

omit [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
  [TopologicalSpace G] [IsTopologicalGroup G] in
/-- The original extended character acts as the same prime-field scalar
on its actual restricted coefficient module. -/
theorem finiteScalarCharacterPrime_action (g : G) (a : k) :
    (finiteScalarCharacterPrimeRep q χ (k := k)).ρ g a =
      @SMul.smul (ZMod q) k
        (finiteScalarCharacterPrimeRep q χ (k := k)).hV2.toDistribMulAction.toDistribSMul.toSMul (χ g) a :=
  (finiteScalarCharacterPrime_smul q χ (χ g) a).symm

omit [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
  [TopologicalSpace G] [IsTopologicalGroup G] in
/-- The genuine characteristic inclusion intertwines the original scalar characters. -/
theorem finiteScalarCharacterInclusion_equivariant (g : G) (r : ZMod q) :
    algebraMap (ZMod q) k ((coefficientCharacterRep χ).ρ g r) =
      (finiteScalarCharacterPrimeRep q χ (k := k)).ρ g
        (algebraMap (ZMod q) k r) := map_mul (algebraMap (ZMod q) k) (χ g) r

/-- The actual characteristic inclusion as a linear map between the two
original prime-field coefficient modules, with their own scalar instances. -/
def finiteScalarCharacterInclusion :
    @LinearMap (ZMod q) (ZMod q) _ _ (RingHom.id (ZMod q))
      (coefficientCharacterRep χ) (finiteScalarCharacterPrimeRep q χ (k := k)) _ _
      (coefficientCharacterRep χ).hV2 (finiteScalarCharacterPrimeRep q χ (k := k)).hV2 :=
  @AddMonoidHom.toZModLinearMap q (ZMod q) k _ _ (coefficientCharacterRep χ).hV2
    (finiteScalarCharacterPrimeRep q χ (k := k)).hV2 (algebraMap (ZMod q) k).toAddMonoidHom

/-- Original H2 retains all values and continuous boundaries under the
existing prime-field restriction of its scalar coefficient line. -/
def finiteScalarCharacterPrimeH2Equiv :
    ContinuousRepresentationH2 (coefficientCharacterRep ((algebraMap (ZMod q) k).toMonoidHom.comp χ))
      (coefficientCharacterAction_continuous
        ((algebraMap (ZMod q) k).toMonoidHom.comp χ) (finiteScalarCharacter_continuous q χ hχ)) ≃+
    ContinuousRepresentationH2
      (finiteScalarCharacterPrimeRep q χ (k := k))
      (coefficientCharacterAction_continuous
        ((algebraMap (ZMod q) k).toMonoidHom.comp χ) (finiteScalarCharacter_continuous q χ hχ)) :=
  continuousH2AdditiveCoefficientEquiv
    (coefficientCharacterRep ((algebraMap (ZMod q) k).toMonoidHom.comp χ))
    (finiteScalarCharacterPrimeRep q χ (k := k))
    (AddEquiv.refl k) continuous_id continuous_id (fun _ _ => rfl) _ _

/-- Extend an actual prime-field continuous H2 class along the original
characteristic map, and retain the original extension-field H2 quotient. -/
def finiteScalarCharacterH2Extend :
    ContinuousRepresentationH2 (coefficientCharacterRep χ) (coefficientCharacterAction_continuous χ hχ) →+
    ContinuousRepresentationH2 (coefficientCharacterRep ((algebraMap (ZMod q) k).toMonoidHom.comp χ))
      (coefficientCharacterAction_continuous
        ((algebraMap (ZMod q) k).toMonoidHom.comp χ) (finiteScalarCharacter_continuous q χ hχ)) :=
  (finiteScalarCharacterPrimeH2Equiv q χ hχ).symm.toAddMonoidHom.comp
    (continuousCoefficientH2Map (coefficientCharacterRep χ)
      (finiteScalarCharacterPrimeRep q χ (k := k))
      (finiteScalarCharacterInclusion q χ)
      continuous_of_discreteTopology (finiteScalarCharacterInclusion_equivariant q χ (k := k))
      (coefficientCharacterAction_continuous χ hχ)
      (coefficientCharacterAction_continuous
        ((algebraMap (ZMod q) k).toMonoidHom.comp χ) (finiteScalarCharacter_continuous q χ hχ))).toAddMonoidHom

variable {ι : Type}
  (b : @Module.Basis ι (ZMod q) k _ _ (finiteScalarCharacterPrimeRep q χ (k := k)).hV2)

/-- Each original H2 coordinate of an extended scalar multiple is its
actual coefficient coordinate times the original prime-field class. -/
theorem finiteScalarCharacterH2Extend_coordinate (i : ι) (a : k)
    (u : ContinuousRepresentationH2 (coefficientCharacterRep χ) (coefficientCharacterAction_continuous χ hχ)) :
    continuousCoefficientH2Map
      (finiteScalarCharacterPrimeRep q χ (k := k))
      (coefficientCharacterRep χ) (b.coord i) continuous_of_discreteTopology
      (scalarCoefficientCoordinate_equivariant
        (finiteScalarCharacterPrimeRep q χ (k := k)) χ b (finiteScalarCharacterPrime_action q χ) i)
      (coefficientCharacterAction_continuous
        ((algebraMap (ZMod q) k).toMonoidHom.comp χ) (finiteScalarCharacter_continuous q χ hχ))
      (coefficientCharacterAction_continuous χ hχ)
      (finiteScalarCharacterPrimeH2Equiv q χ hχ (a • finiteScalarCharacterH2Extend q χ hχ u)) =
      b.coord i a • u := by
  induction u using Submodule.Quotient.induction_on with
  | _ c =>
    letI : Module (ZMod q) (ZMod q) := (coefficientCharacterRep χ).hV2
    letI : Module (ZMod q) (continuousRepresentationCocyclesTwo (coefficientCharacterRep χ)) :=
      (continuousRepresentationCocyclesTwo (coefficientCharacterRep χ)).module
    apply congrArg (continuousRepresentationCoboundariesTwo (coefficientCharacterRep χ)
      (coefficientCharacterAction_continuous χ hχ)).mkQ
    apply Subtype.ext
    apply Subtype.ext
    funext z
    change b.coord i (a * algebraMap (ZMod q) k (c.val z)) = b.coord i a * c.val z
    rw [mul_comm a, ← finiteScalarCharacterPrime_smul q χ]
    exact ((b.coord i).map_smul (c.val z) a).trans (mul_comm _ _)

end
end Dubon2026
