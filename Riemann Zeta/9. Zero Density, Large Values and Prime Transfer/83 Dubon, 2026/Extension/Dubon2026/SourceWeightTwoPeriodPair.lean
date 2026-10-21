import Dubon2026.SourceWeightTwoPeriods
import Dubon2026.SourceWeightTwoMixedInjectivity

/-! DUB-17/18 -> residual Galois association -> parabolic Hecke realization
-> injectivity of the actual weight-two period pair. Reflection is the literal
integral J conjugation. A relation between original periods supplies the mixed
primitive invariance, whose analytic vanishing theorem constructs all
derivative and cusp-limit inputs from the original forms.
-/
namespace Dubon2026
noncomputable section
open CongruenceSubgroup Matrix.SpecialLinearGroup UpperHalfPlane
open scoped MatrixGroups

variable (N : ℕ) [NeZero N]

/-- An original period relation with the reflected second form forces the first
form to vanish. All primitive invariance assumptions are discharged here. -/
theorem sourceWeightTwo_period_relation_zero
    (f g : CuspForm ((Gamma0 N).map (mapGL ℝ)) 2)
    (h : ∀ γ : Gamma0 N, sourceWeightTwoPeriodValue (Gamma0 N) f γ =
      sourceWeightTwoPeriodValue (Gamma0 N) g (sourceJConjugateGamma0 N γ)) : f = 0 := by
  apply sourceWeightTwo_mixedPrimitive_injective N f g
  intro γ z
  rw [sourceJ_smul_SL]
  change sourceWeightTwoPrimitive _ f (γ.val • z) -
      sourceWeightTwoPrimitive _ g ((sourceJConjugateGamma0 N γ).val • (J • z)) = _
  rw [sourceWeightTwoPrimitive_period, sourceWeightTwoPrimitive_period, h γ]
  ring

/-- Precomposition by the actual integral reflection on additive characters. -/
def sourceWeightTwoPeriodReflection :
    (Additive (Gamma0 N) →+ ℂ) →ₗ[ℂ] (Additive (Gamma0 N) →+ ℂ) where
  toFun φ :=
    { toFun := fun γ => φ (Additive.ofMul (sourceJConjugateGamma0 N γ.toMul))
      map_zero' := by
        change φ (Additive.ofMul (sourceJConjugateGamma0Hom N 1)) = 0
        rw [map_one]
        exact φ.map_zero
      map_add' γ δ := by
        change φ (Additive.ofMul (sourceJConjugateGamma0Hom N (γ.toMul * δ.toMul))) = _
        rw [map_mul, ofMul_mul, map_add]
        rfl }
  map_add' φ ψ := by ext γ; rfl
  map_smul' c φ := by ext γ; rfl

omit [NeZero N] in
/-- Reflecting the actual period character twice is the identity. -/
theorem sourceWeightTwoPeriodReflection_involutive :
    Function.Involutive (sourceWeightTwoPeriodReflection N) := by
  intro φ
  ext γ
  change φ (Additive.ofMul (sourceJConjugateGamma0 N
    (sourceJConjugateGamma0 N γ))) = φ (Additive.ofMul γ)
  rw [sourceJConjugateGamma0_involutive N γ]

/-- The genuine even/odd period pair, valued in native additive characters. -/
def sourceWeightTwoPeriodPair :
    (CuspForm ((Gamma0 N).map (mapGL ℝ)) 2 ×
      CuspForm ((Gamma0 N).map (mapGL ℝ)) 2) →ₗ[ℂ]
      (Additive (Gamma0 N) →+ ℂ) where
  toFun fg := sourceWeightTwoPeriodHom (Gamma0 N) fg.1 +
    sourceWeightTwoPeriodReflection N (sourceWeightTwoPeriodHom (Gamma0 N) fg.1) +
    sourceWeightTwoPeriodHom (Gamma0 N) fg.2 -
    sourceWeightTwoPeriodReflection N (sourceWeightTwoPeriodHom (Gamma0 N) fg.2)
  map_add' fg uv := by
    simp only [Prod.fst_add, Prod.snd_add, map_add]
    abel
  map_smul' c fg := by
    simp only [Prod.smul_fst, Prod.smul_snd, map_smul, RingHom.id_apply, smul_add, smul_sub]

/-- The original two-form period map is injective. Its kernel supplies the
mixed invariance relation, so no injectivity or analytic limit is assumed. -/
theorem sourceWeightTwoPeriodPair_injective :
    Function.Injective (sourceWeightTwoPeriodPair N) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  rintro ⟨f, g⟩ h
  have hp (γ : Gamma0 N) :
      sourceWeightTwoPeriodValue (Gamma0 N) (f + g) γ =
        sourceWeightTwoPeriodValue (Gamma0 N) (g - f) (sourceJConjugateGamma0 N γ) := by
    have he := congrArg (fun φ : Additive (Gamma0 N) →+ ℂ => φ (Additive.ofMul γ)) h
    change sourceWeightTwoPeriodValue (Gamma0 N) f γ +
      sourceWeightTwoPeriodValue (Gamma0 N) f (sourceJConjugateGamma0 N γ) +
      sourceWeightTwoPeriodValue (Gamma0 N) g γ -
      sourceWeightTwoPeriodValue (Gamma0 N) g (sourceJConjugateGamma0 N γ) = 0 at he
    simp only [map_add, map_sub, Pi.add_apply, Pi.sub_apply]
    linear_combination he
  have hsum := sourceWeightTwo_period_relation_zero N (f + g) (g - f) hp
  have hsub : g - f = 0 := sourceWeightTwo_period_relation_zero N (g - f) (f + g) (by
    intro γ
    simpa only [sourceJConjugateGamma0_involutive N γ] using
      (hp (sourceJConjugateGamma0 N γ)).symm)
  have hgf : g = f := sub_eq_zero.mp hsub
  have hf : f = 0 := by
    apply DFunLike.ext
    intro z
    have hz := congrArg (fun u : CuspForm ((Gamma0 N).map (mapGL ℝ)) 2 => u z) hsum
    rw [hgf] at hz
    change f z + f z = 0 at hz
    change f z = 0
    linear_combination (1 / 2 : ℂ) * hz
  exact Prod.ext hf (hgf.trans hf)

end
end Dubon2026
