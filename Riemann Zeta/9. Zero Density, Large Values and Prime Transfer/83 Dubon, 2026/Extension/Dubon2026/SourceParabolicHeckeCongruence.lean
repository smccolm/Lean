import Dubon2026.SourceParabolicHeckeSpan
import Dubon2026.SourceFiniteIntegralSaturation
import Dubon2026.SourceSupportedCharacterDivisibility
import Dubon2026.SourceBinaryH1PrimePowerKernel
import Dubon2026.SourcePrimitiveLocalH1Character

/-! DUB17/18 -> original all-weight association -> finite parabolic
character descent -> original operator congruence. The actual Hecke span
of integral parabolic H1 is finite and supports the original Fourier
character. Away from its fixed saturation obstruction, an operator zero
after reduction on parabolic H1 has the matching integral quotient of
its original character. No parabolic stability, finite Gamma1 transfer
or exceptional-prime conclusion is inferred. -/
namespace Dubon2026
noncomputable section
open CongruenceSubgroup groupCohomology

open scoped IsMulCommutative in
theorem sourcePrimitiveParabolicHecke_congruence_integral_away
    {Q : ℕ} [NeZero Q] {k : ℤ} (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) :
    ∃ d : ℤ, d ≠ 0 ∧ ∀ {E : Type} [Field E] [CharZero E]
      (τ : sourcePrimitiveCoefficientField f →ₐ[ℚ] E)
      (N : ℕ), N ≠ 0 → IsCoprime (N : ℤ) d →
      ∀ T : sourceBinaryH1HeckeAlgebra Q (k - 2).toNat,
        (∀ x : H1 (sourceBinaryCoefficientRep ℤ Q (k - 2).toNat),
          x ∈ sourceParabolicH1 (Gamma0 Q) (sourceBinaryCoefficientRep ℤ Q (k - 2).toNat) →
          sourceBinaryH1Change (Int.castRingHom (ZMod N)) Q (k - 2).toNat (T.val x) = 0) →
        IsIntegral ℤ (τ (sourcePrimitiveFieldH1HeckeCharacter f hk T) / (N : E)) := by
  let w := (k - 2).toNat
  let A := sourceBinaryH1HeckeAlgebra Q w
  letI : IsMulCommutative A := Algebra.isMulCommutative_adjoin ℤ (by
    rintro _ ⟨p, rfl⟩ _ ⟨q, rfl⟩
    exact (sourceBinaryH1PrimeOperators_commute ℤ Q w p q).eq)
  letI : CommRing A := inferInstance
  let S := sourceParabolicHeckeSpan Q w
  letI := sourceIntegralBinaryH1Finite Q w
  letI := sourceParabolicHeckeSpan_finite Q w
  let P : Submodule ℤ (H1 (sourceBinaryCoefficientRep ℤ Q w)) :=
    { S.toAddSubmonoid with
      smul_mem' := by
        intro n x hx
        simpa only [← Int.cast_smul_eq_zsmul ℤ, Int.cast_id] using S.toAddSubgroup.zsmul_mem hx n }
  obtain ⟨d, hd, hsat⟩ := sourceFiniteIntegralSubmodule_saturation P
  refine ⟨d, hd, ?_⟩
  intro E _ _ τ N hN hcop T hT
  let χ : A →+* E := τ.toRingHom.comp (sourcePrimitiveFieldH1HeckeCharacter f hk).toRingHom
  have hann : Module.annihilator A S ≤ RingHom.ker χ := by
    intro a ha
    change τ (sourcePrimitiveFieldH1HeckeCharacter f hk a) = 0
    have h := sourcePrimitiveParabolicHeckeSpan_annihilator f hk ha
    change sourcePrimitiveFieldH1HeckeCharacter f hk a = 0 at h
    rw [h, map_zero]
  have hn : ((N : ℤ) : E) ≠ 0 := by exact_mod_cast hN
  have hi := sourceSupportedCharacter_div_isIntegral (M := S) χ hann T (N : ℤ) hn (by
    intro x
    have hz := sourceParabolicHeckeSpan_operator_congruence Q w N T hT x
    obtain ⟨y, hy⟩ := (sourceBinaryH1Change_zmod_nonzero_eq_zero_iff Q w N hN (T.val x.val)).mp hz
    have hyS : y ∈ S := hsat N (by exact_mod_cast hN) hcop y (by
      change (N : ℤ) • y ∈ S
      rw [← hy]
      exact S.smul_mem T x.property)
    refine ⟨⟨y, hyS⟩, ?_⟩
    apply Subtype.ext
    exact hy)
  simpa only [χ, RingHom.comp_apply, Int.cast_natCast] using hi

end
end Dubon2026
