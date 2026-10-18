import Dubon2026.ArithmeticSourceClassSaturationColimit
import Dubon2026.OriginalRelationGroupChange

/-! Bring the actual full-class extension back to S-place classes. The
prime-annihilated coefficient makes each free-cover value prime-divisible
into the source image; the proved arithmetic saturation supplies its
unique source value and preserves the original relation. This removes
the class-image lifting premise on DUB-17's reverse-localization chain. -/
namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2

variable (K Ω : Type) [Field K] [Field Ω] [NumberField K] [Algebra K Ω]
  [IsAlgClosure K Ω] (a : 𝓞 K) (ha : a ≠ 0)
  [DecidableEq (FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))]
  (q : ℕ) [Fact q.Prime] (hqa : (q : 𝓞 K) ∣ a)
  (P : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
  (B : Rep.{0} ℤ Gal(P/K)) (hB : ∀ b : B, q • b = 0)

include hqa hB in
/-- An actual full-class extension of a source relation lifts
to the original S-place classes, with both the extension and comparison
equalities preserved. -/
theorem arithmeticSourceClassRelation_extension_lifts :
    let π : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K) →* Gal(P/K) :=
      AlgEquiv.restrictNormalHom P
    let X := (originalRelationShortComplex B).map (Rep.resFunctor π)
    let S := arithmeticSPlaceClassColimitRep K Ω a ha
    let C := arithmeticClassesModOutsideColimitRep K Ω a ha
    let j := arithmeticSourceClassColimitComparison K Ω a ha
    ∀ (φ : X.X₁ ⟶ S) (f : X.X₂ ⟶ C), X.f ≫ f = φ ≫ j →
      ∃ fS : X.X₂ ⟶ S, fS ≫ j = f ∧ X.f ≫ fS = φ := by
  intro π X S C j φ f hf
  have hj : Function.Injective j.hom := arithmeticSourceClassColimitComparison_injective K Ω a ha
  have hX := originalRelationGroupChange_shortExact π B
  have hm := hX.map_of_exact
    (forget₂ (Rep ℤ Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K)) (ModuleCat ℤ))
  have hex : LinearMap.range X.f.hom.toLinearMap = LinearMap.ker X.g.hom.toLinearMap :=
    hm.exact.moduleCat_range_eq_ker
  have hvalues (x : X.X₂) : f.hom x ∈ LinearMap.range j.hom.toLinearMap := by
    have hmem : q • x ∈ LinearMap.range X.f.hom.toLinearMap := by
      rw [hex]
      change X.g.hom (q • x) = 0
      rw [map_nsmul]
      exact hB (X.g.hom x)
    obtain ⟨r, hr⟩ := hmem
    have he : q • f.hom x = j.hom (φ.hom r) := by
      rw [← map_nsmul]
      change f.hom (q • x) = _
      rw [← hr]
      exact congrArg (fun m : X.X₁ ⟶ C => m.hom r) hf
    exact arithmeticSourceClassColimit_prime_saturated K Ω a ha q hqa
      (f.hom x) (φ.hom r) he
  let e := LinearEquiv.ofInjective j.hom.toLinearMap hj
  let l := e.symm.toLinearMap.comp (f.hom.toLinearMap.codRestrict _ hvalues)
  have hl (x : X.X₂) : j.hom (l x) = f.hom x :=
    congrArg Subtype.val (e.apply_symm_apply (f.hom.toLinearMap.codRestrict _ hvalues x))
  let fS : X.X₂ ⟶ S := Rep.ofHom ⟨l, by
    intro g
    apply LinearMap.ext
    intro x
    apply hj
    change j.hom (l (X.X₂.ρ g x)) = j.hom (S.ρ g (l x))
    rw [hl, Rep.hom_comm_apply j, hl]
    exact Rep.hom_comm_apply f g x⟩
  have hfs : fS ≫ j = f := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    exact hl
  refine ⟨fS, hfs, ?_⟩
  letI : Mono j := (Rep.mono_iff_injective j).mpr hj
  apply (cancel_mono j).mp
  rw [Category.assoc, hfs]
  exact hf

end
end Dubon2026
