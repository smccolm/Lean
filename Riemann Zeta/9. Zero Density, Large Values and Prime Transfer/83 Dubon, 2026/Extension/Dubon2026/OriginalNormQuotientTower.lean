import Dubon2026.OriginalIdeleNormTower
import Dubon2026.OriginalIdeleClassNativeNormQuotient

/-! # The original norm quotient in a tower

Norm transitivity puts the composite norm range inside the lower norm
range. The original upper norm quotient surjects onto their quotient.
The pinned third-isomorphism cardinal formula then bounds the original
composite norm index by the two original indices. This is the exact
induction step from the proved prime case to DUB-17's cyclic norm index.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2
variable (K E L : Type) [Field K] [NumberField K] [Field E] [NumberField E]
  [Field L] [NumberField L] [Algebra K E] [Algebra E L] [Algebra K L]
  [IsScalarTower K E L] [FiniteDimensional K E] [FiniteDimensional E L]
  [FiniteDimensional K L] [IsGalois K E] [IsGalois E L] [IsGalois K L]

/-- The literal original class norm quotient in a Galois tower has cardinal
at most the product of the two literal original norm-quotient cardinals. -/
theorem originalIdeleClassNormQuotient_card_le_tower
    [Finite (OriginalIdeleClassNormQuotient E L)] :
    Nat.card (OriginalIdeleClassNormQuotient K L) ≤
      Nat.card (OriginalIdeleClassNormQuotient E L) *
        Nat.card (OriginalIdeleClassNormQuotient K E) := by
  let f := originalIdeleClassNormLinear K E
  let g := originalIdeleClassNormLinear E L
  let h := originalIdeleClassNormLinear K L
  have hComp (x : Additive (OriginalNumberFieldIdeleClassGroup L)) : f (g x) = h x :=
    congrArg Additive.ofMul (originalIdeleClassNorm_tower K E L x.toMul)
  let U := f.range
  let V := g.range
  let W := h.range
  have hWU : W ≤ U := by
    rintro _ ⟨x, rfl⟩
    exact ⟨g x, hComp x⟩
  let φ : Additive (OriginalNumberFieldIdeleClassGroup E) →ₗ[ℤ] U.map W.mkQ :=
    (W.mkQ.comp f).codRestrict _ (fun x => ⟨f x, ⟨x, rfl⟩, rfl⟩)
  have hKer : V ≤ φ.ker := by
    rintro _ ⟨x, rfl⟩
    apply Subtype.ext
    change W.mkQ (f (g x)) = 0
    apply (Submodule.Quotient.mk_eq_zero W).mpr
    exact ⟨x, (hComp x).symm⟩
  let ψ : OriginalIdeleClassNormQuotient E L →ₗ[ℤ] U.map W.mkQ := V.liftQ φ hKer
  have hSurj : Function.Surjective ψ := by
    intro y
    obtain ⟨a, ha, hay⟩ := y.property
    obtain ⟨b, hb⟩ := ha
    refine ⟨V.mkQ b, ?_⟩
    apply Subtype.ext
    change W.mkQ (f b) = y.val
    rw [hb]
    exact hay
  have hCard := Nat.card_le_card_of_surjective ψ hSurj
  change Nat.card (Additive (OriginalNumberFieldIdeleClassGroup K) ⧸ W) ≤ _
  rw [← Submodule.card_quotient_mul_card_quotient U W hWU]
  exact Nat.mul_le_mul_right _ hCard

end
end Dubon2026
