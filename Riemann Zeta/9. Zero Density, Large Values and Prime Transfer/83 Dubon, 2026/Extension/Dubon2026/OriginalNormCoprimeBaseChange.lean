import Dubon2026.OriginalIdeleNormTower
import Dubon2026.OriginalNormQuotientCoprime

/-! # Coprime comparison of the actual original class norm quotients

Tower transitivity reflects norm membership after a coprime Galois base
extension. Choosing actual original class representatives then gives an
injection of the literal norm quotients. Only that cardinal comparison is
needed for cyclotomic descent in DUB-17's prime norm-index chain; no general
pushout norm-map compatibility or transported class space is required.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2
variable (K L M N : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Field M] [NumberField M] [Field N] [NumberField N]
  [Algebra K L] [Algebra K M] [Algebra K N] [Algebra L N] [Algebra M N]
  [IsScalarTower K L N] [IsScalarTower K M N]
  [FiniteDimensional K L] [FiniteDimensional K M] [FiniteDimensional K N]
  [FiniteDimensional L N] [FiniteDimensional M N]
  [IsGalois K L] [IsGalois K M] [IsGalois K N] [IsGalois L N] [IsGalois M N]
  [IsCyclic Gal(L/K)]

/-- Coprime base extension reflects actual original class-norm membership. -/
theorem originalIdeleClassNorm_reflects_coprime_baseChange
    (hd : (Module.finrank K M).Coprime (Module.finrank K L))
    (c : OriginalNumberFieldIdeleClassGroup K)
    (hc : originalIdeleClassBaseChangeMap K M c ∈ (originalIdeleClassNorm M N).range) :
    c ∈ (originalIdeleClassNorm K L).range := by
  apply originalIdeleClassNorm_mem_of_coprime_pow K L (Module.finrank K M) hd
  obtain ⟨b, hb⟩ := hc
  refine ⟨originalIdeleClassNorm L N b, ?_⟩
  rw [originalIdeleClassNorm_tower K L N, ← originalIdeleClassNorm_tower K M N,
    hb, originalIdeleClassNorm_baseChange]

/-- The literal original norm quotient injects into the original quotient
after coprime Galois base extension, by actual class representatives. -/
theorem originalIdeleClassNormQuotient_coprime_embedding
    (hd : (Module.finrank K M).Coprime (Module.finrank K L)) :
    Nonempty (OriginalIdeleClassNormQuotient K L ↪ OriginalIdeleClassNormQuotient M N) := by
  let U := (originalIdeleClassNormLinear K L).range
  let V := (originalIdeleClassNormLinear M N).range
  let β : Additive (OriginalNumberFieldIdeleClassGroup K) →ₗ[ℤ]
      Additive (OriginalNumberFieldIdeleClassGroup M) :=
    (originalIdeleClassBaseChangeMap K M).toAdditive.toIntLinearMap
  let r (x : OriginalIdeleClassNormQuotient K L) := (U.mkQ_surjective x).choose
  have hr (x : OriginalIdeleClassNormQuotient K L) : U.mkQ (r x) = x :=
    (U.mkQ_surjective x).choose_spec
  have hReflect (x : Additive (OriginalNumberFieldIdeleClassGroup K)) (hx : β x ∈ V) :
      x ∈ U := by
    obtain ⟨b, hb⟩ := hx
    have hx' : originalIdeleClassBaseChangeMap K M x.toMul ∈ (originalIdeleClassNorm M N).range :=
      ⟨b.toMul, congrArg Additive.toMul hb⟩
    obtain ⟨y, hy⟩ := originalIdeleClassNorm_reflects_coprime_baseChange K L M N hd x.toMul hx'
    exact ⟨Additive.ofMul y, congrArg Additive.ofMul hy⟩
  refine ⟨⟨fun x => V.mkQ (β (r x)), ?_⟩⟩
  intro x y h
  have hDiff : β (r x - r y) ∈ V := by
    apply (Submodule.Quotient.mk_eq_zero V).mp
    change V.mkQ (β (r x - r y)) = 0
    rw [β.map_sub, V.mkQ.map_sub]
    exact sub_eq_zero.mpr h
  have hZero : U.mkQ (r x - r y) = 0 :=
    (Submodule.Quotient.mk_eq_zero U).mpr (hReflect _ hDiff)
  rw [U.mkQ.map_sub, hr, hr] at hZero
  exact sub_eq_zero.mp hZero

/-- The actual coprime comparison gives the required original norm-index bound. -/
theorem originalIdeleClassNormQuotient_card_le_coprime_baseChange
    [Finite (OriginalIdeleClassNormQuotient M N)]
    (hd : (Module.finrank K M).Coprime (Module.finrank K L)) :
    Nat.card (OriginalIdeleClassNormQuotient K L) ≤ Nat.card (OriginalIdeleClassNormQuotient M N) := by
  obtain ⟨e⟩ := originalIdeleClassNormQuotient_coprime_embedding K L M N hd
  exact Nat.card_le_card_of_injective e e.injective

end
end Dubon2026
