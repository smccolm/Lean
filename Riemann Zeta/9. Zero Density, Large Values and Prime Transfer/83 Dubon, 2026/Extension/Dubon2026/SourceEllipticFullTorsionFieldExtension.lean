import Dubon2026.SourceEllipticFiniteTorsionField

/-! A containing field retains all prime-to-characteristic torsion once
the actual division field has all n^2 points. The two actual point-map
injections and the proved algebraically closed torsion count give the
equality, without any new torsion structure assumption. This is required
by DUB-17/18 finite Galois specialization and exceptional-fiber counting. -/
namespace Dubon2026.SourceEllipticDivisionField
open WeierstrassCurve WeierstrassCurve.Affine
noncomputable section

theorem card_torsion_of_containing_full_field
    {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] [IsAlgClosed Ω] [DecidableEq Ω]
    (E : WeierstrassCurve F) [E.IsElliptic] {n : ℕ} (hn : (n : F) ≠ 0)
    (L M : IntermediateField F Ω) (hL : L ≤ M)
    (hcard : Nat.card {P : (E.baseChange L).toAffine.Point // n • P = 0} = n ^ 2) :
    Nat.card {P : (E.baseChange M).toAffine.Point // n • P = 0} = n ^ 2 := by
  have hnΩ : (n : Ω) ≠ 0 := natCast_ne_zero_of_ne_zero hn
  let f : (E.baseChange L).toAffine.Point →+ (E.baseChange M).toAffine.Point :=
    Point.map (IntermediateField.inclusion hL)
  let g : (E.baseChange M).toAffine.Point →+ (E.baseChange Ω).toAffine.Point :=
    Point.map (IntermediateField.val M)
  let fT : {P : (E.baseChange L).toAffine.Point // n • P = 0} →
      {P : (E.baseChange M).toAffine.Point // n • P = 0} :=
    fun P => ⟨f P.1, by rw [← map_nsmul, P.2, map_zero]⟩
  let gT : {P : (E.baseChange M).toAffine.Point // n • P = 0} →
      {P : (E.baseChange Ω).toAffine.Point // n • P = 0} :=
    fun P => ⟨g P.1, by rw [← map_nsmul, P.2, map_zero]⟩
  have hfT : Function.Injective fT := fun P Q h =>
    Subtype.ext (Point.map_injective _ (congrArg Subtype.val h))
  have hgT : Function.Injective gT := fun P Q h =>
    Subtype.ext (Point.map_injective _ (congrArg Subtype.val h))
  have hΩ : Nat.card {P : (E.baseChange Ω).toAffine.Point // n • P = 0} = n ^ 2 := by
    change Nat.card ({P : (E.baseChange Ω).toAffine.Point | n • P = 0} : Set _) = n ^ 2
    rw [Nat.card_coe_set_eq]
    exact (finite_and_ncard_torsion E hnΩ).2
  have hn0 : n ≠ 0 := by rintro rfl; exact hn (Nat.cast_zero)
  haveI : Finite {P : (E.baseChange Ω).toAffine.Point // n • P = 0} :=
    Nat.finite_of_card_ne_zero (by rw [hΩ]; exact pow_ne_zero _ hn0)
  haveI : Finite {P : (E.baseChange M).toAffine.Point // n • P = 0} :=
    Finite.of_injective gT hgT
  apply le_antisymm
  · calc _ ≤ Nat.card {P : (E.baseChange Ω).toAffine.Point // n • P = 0} :=
      Nat.card_le_card_of_injective gT hgT
    _ = n ^ 2 := hΩ
  · calc _ = Nat.card {P : (E.baseChange L).toAffine.Point // n • P = 0} := hcard.symm
    _ ≤ _ := Nat.card_le_card_of_injective fT hfT

end
end Dubon2026.SourceEllipticDivisionField
