import Dubon2026.SourcePrimitiveParabolicHeckeRelations
import Dubon2026.SourcePrimitiveH1CoefficientField

/-! DUB17/18 -> original all-weight association -> finite parabolic
character descent. Consume the original, already constructed integral
H1 character itself: an operator annihilating integral parabolic H1 has
zero value in the original Fourier coefficient field. This is the
characteristic-zero kernel statement; finite congruence remains. -/
namespace Dubon2026
noncomputable section
open CongruenceSubgroup groupCohomology

theorem sourcePrimitiveH1HeckeCharacter_zero_of_parabolic
    {Q : ℕ} [NeZero Q] {k : ℤ} (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k)
    (T : sourceBinaryH1HeckeAlgebra Q (k - 2).toNat)
    (hT : ∀ x : H1 (sourceBinaryCoefficientRep ℤ Q (k - 2).toNat),
      x ∈ sourceParabolicH1 (Gamma0 Q) (sourceBinaryCoefficientRep ℤ Q (k - 2).toNat) →
        T.val x = 0) :
    sourcePrimitiveH1HeckeCharacter f hk T = 0 := by
  let w := (k - 2).toNat
  let t := sourceBinaryH1PrimeOperators ℤ Q w
  let g : FreeAlgebra ℤ (sourceBinaryHeckePrime Q) →ₐ[ℤ] sourceBinaryH1HeckeAlgebra Q w :=
    FreeAlgebra.lift ℤ (fun p => ⟨t p, Algebra.subset_adjoin ⟨p, rfl⟩⟩)
  have hg : (sourceBinaryH1HeckeAlgebra Q w).val.comp g = FreeAlgebra.lift ℤ t := by
    apply FreeAlgebra.hom_ext
    funext p
    simp only [Function.comp_apply, AlgHom.comp_apply, g, FreeAlgebra.lift_ι_apply]
    rfl
  have hc : (sourcePrimitiveH1HeckeCharacter f hk).comp g =
      FreeAlgebra.lift ℤ (fun p : sourceBinaryHeckePrime Q => cuspCoefficients f.toCuspForm p.val) := by
    apply FreeAlgebra.hom_ext
    funext p
    simp only [Function.comp_apply, AlgHom.comp_apply, g, FreeAlgebra.lift_ι_apply]
    exact sourcePrimitiveH1HeckeCharacter_hecke f hk p
  have hm : T.val ∈ (FreeAlgebra.lift ℤ t).range := by
    rw [← Algebra.adjoin_range_eq_range_freeAlgebra_lift]
    exact T.property
  obtain ⟨a, ha⟩ := hm
  change FreeAlgebra.lift ℤ t a = T.val at ha
  have hag : g a = T := Subtype.ext ((AlgHom.congr_fun hg a).trans ha)
  rw [← hag, ← AlgHom.comp_apply, hc]
  apply sourcePrimitiveIntegralParabolicHecke_relation f hk a
  intro x hx
  change FreeAlgebra.lift ℤ t a x = 0
  rw [ha]
  exact hT x hx

theorem sourcePrimitiveFieldH1HeckeCharacter_zero_of_parabolic
    {Q : ℕ} [NeZero Q] {k : ℤ} (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k)
    (T : sourceBinaryH1HeckeAlgebra Q (k - 2).toNat)
    (hT : ∀ x : H1 (sourceBinaryCoefficientRep ℤ Q (k - 2).toNat),
      x ∈ sourceParabolicH1 (Gamma0 Q) (sourceBinaryCoefficientRep ℤ Q (k - 2).toNat) →
        T.val x = 0) :
    sourcePrimitiveFieldH1HeckeCharacter f hk T = 0 := by
  apply Subtype.ext
  exact sourcePrimitiveH1HeckeCharacter_zero_of_parabolic f hk T hT

end
end Dubon2026
