import Dubon2026.RationalArithmeticGaloisGroup
import Dubon2026.EmbeddedNormalGaloisRestrictionContinuity

/-! Enlarging the exceptional integer gives the actual continuous
surjective restriction of arithmetic Galois groups. This is the group
map required to compare the auxiliary deformation ring with the original
support in the Dubon Theorem 2.6 patching chain. -/

namespace Dubon2026
noncomputable section
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
open IsDedekindDomain
open scoped NumberField

private theorem arithmetic_support_normal (a : 𝓞 ℚ)
    (α : Algebra ℚ (rationalUnramifiedExtension a)) :
    @Normal ℚ (rationalUnramifiedExtension a) _ _ α := by
  have h := (originalUnramifiedGaloisUnion_isGalois (Ω := AlgebraicClosure ℚ) a).to_normal
  have he : (rationalUnramifiedExtension a).algebra' = α := Subsingleton.elim _ _
  exact Eq.mp (congrArg (fun α : Algebra ℚ (rationalUnramifiedExtension a) =>
    @Normal ℚ (rationalUnramifiedExtension a) _ _ α) he) h

attribute [local instance] arithmetic_support_normal

/-- The original unramified unions are nested when their exceptional
integers divide, directly from the defining finite-stage ramification. -/
theorem originalUnramifiedGaloisUnion_mono_dvd
    {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] [NumberField K]
    {a b : 𝓞 K} (hab : a ∣ b) :
    originalUnramifiedGaloisUnion (Ω := Ω) a ≤ originalUnramifiedGaloisUnion b := by
  apply iSup_le
  intro F
  have hF : ∀ w : HeightOneSpectrum (𝓞 F.val),
      algebraMap (𝓞 K) (𝓞 F.val) b ∉ w.asIdeal →
      (w.asIdeal.under (𝓞 K)).ramificationIdx w.asIdeal = 1 := by
    intro w hw
    apply F.property w
    intro ha
    apply hw
    obtain ⟨c, rfl⟩ := hab
    rw [map_mul]
    exact w.asIdeal.mul_mem_right _ ha
  exact originalUnramifiedGaloisStage_le_union b ⟨F.val, hF⟩

/-- The genuine inclusion of the original arithmetic extensions. -/
def rationalArithmeticSupportInclusion (a b : 𝓞 ℚ) (hab : a ∣ b) :
    rationalUnramifiedExtension a →ₐ[ℚ] rationalUnramifiedExtension b :=
  IntermediateField.inclusion (originalUnramifiedGaloisUnion_mono_dvd hab)

/-- Continuous restriction along the actual inclusion of arithmetic
extensions, retaining the original Krull topologies. -/
def rationalArithmeticSupportRestriction (a b : 𝓞 ℚ) (hab : a ∣ b) :
    rationalArithmeticGaloisGroup b →ₜ* rationalArithmeticGaloisGroup a where
  toMonoidHom := embeddedNormalGaloisRestriction (F := ℚ) (rationalArithmeticSupportInclusion a b hab)
  continuous_toFun := embeddedNormalGaloisRestriction_continuous (F := ℚ)
    (rationalArithmeticSupportInclusion a b hab)

/-- The actual inclusion characterizes this restriction on every element. -/
theorem rationalArithmeticSupportRestriction_commutes (a b : 𝓞 ℚ) (hab : a ∣ b)
    (g : rationalArithmeticGaloisGroup b) (x : rationalUnramifiedExtension a) :
    rationalArithmeticSupportInclusion a b hab
      ((show Gal(rationalUnramifiedExtension a/ℚ) from rationalArithmeticSupportRestriction a b hab g) x) =
    (show Gal(rationalUnramifiedExtension b/ℚ) from g) (rationalArithmeticSupportInclusion a b hab x) :=
  embeddedNormalGaloisRestriction_commutes (rationalArithmeticSupportInclusion a b hab) g x

/-- Every original-support automorphism extends to the larger original
normal arithmetic extension. -/
theorem rationalArithmeticSupportRestriction_surjective (a b : 𝓞 ℚ) (hab : a ∣ b) :
    Function.Surjective (rationalArithmeticSupportRestriction a b hab) := by
  let E := rationalUnramifiedExtension a
  let K := rationalUnramifiedExtension b
  let e := rationalArithmeticSupportInclusion a b hab
  letI : Algebra E K := e.toRingHom.toAlgebra
  letI : IsScalarTower ℚ E K := IsScalarTower.of_algHom e
  intro σ
  obtain ⟨τ, hτ⟩ := AlgEquiv.restrictNormalHom_surjective (F := ℚ) (K₁ := E) (E := K) σ
  exact ⟨τ, hτ⟩

end
end Dubon2026
