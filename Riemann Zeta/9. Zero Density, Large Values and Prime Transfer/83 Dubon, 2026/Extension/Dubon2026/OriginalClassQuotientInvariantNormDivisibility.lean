import Dubon2026.OriginalClassQuotientNormComparison
import Dubon2026.OriginalIdeleClassBaseInvariants

/-! # Invariant norm roots from the actual norm-field containment

The arithmetic norm-field theorem supplies containment of the actual
class-norm image in powers plus the original outside-unit image. This
deduction constructs an invariant root in the actual upper quotient.
The norm-field containment remains explicit; it is not proved here.
This is the missing arithmetic input to DUB-17's relation-extension step.
-/
namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (S : Finset (HeightOneSpectrum (𝓞 K))) (T : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(K/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K K σ v ∈ S)
  (hT : ∀ (σ : Gal(L/K)) v, v ∈ T ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ T)
  (hST : ∀ w, w ∈ T ↔ originalFinitePrimeBelow K L w ∈ S)

include hST in
/-- An actual norm-field containment constructs invariant roots of all literal quotient norms. -/
theorem originalClassesModOutside_invariant_norm_divisibility (n : ℕ)
    (hnorm : LinearMap.range (originalIdeleClassNormLinear K L) ≤
      LinearMap.range ((n : ℤ) • (LinearMap.id :
        originalIdeleClassRep K K →ₗ[ℤ] originalIdeleClassRep K K)) ⊔
        LinearMap.range (originalOutsideIdeleClassRepHom K K S hS).hom.toLinearMap)
    (x : originalIdeleClassesModOutsideRep K L T hT) :
    ∃ d : originalIdeleClassesModOutsideRep K L T hT,
      (∀ g, (originalIdeleClassesModOutsideRep K L T hT).ρ g d = d) ∧
      (∑ g : Gal(L/K), (originalIdeleClassesModOutsideRep K L T hT).ρ g x) = n • d := by
  letI : Module ℤ (Additive (OriginalNumberFieldIdeleClassGroup K)) :=
    (originalIdeleClassRep K K).hV2
  induction x using Submodule.Quotient.induction_on with
  | H c =>
    have hc := hnorm (show (originalIdeleClassNormLinear K L) c ∈
      LinearMap.range (originalIdeleClassNormLinear K L) from ⟨c, rfl⟩)
    obtain ⟨y, ⟨b, hb⟩, z, ⟨u, hu⟩, he⟩ :=
      (Submodule.mem_sup (M := originalIdeleClassRep K K)).mp hc
    let q := originalIdeleClassesModOutsideRepHom K K S hS
    let β := originalClassesModOutsideBaseChangeRepHom K K L S T hS hT hST
    let d := originalClassesModOutsideBaseInvariant K L S T hS hT hST (q.hom b)
    refine ⟨d.val, d.property, ?_⟩
    have hu0 : q.hom ((originalOutsideIdeleClassRepHom K K S hS).hom u) = 0 := by
      exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨u, rfl⟩
    have hq : q.hom ((originalIdeleClassNormLinear K L) c) = n • q.hom b := by
      have h := congrArg q.hom (hb ▸ hu ▸ he)
      change q.hom ((n : ℤ) • b +
        (originalOutsideIdeleClassRepHom K K S hS).hom u) =
          q.hom ((originalIdeleClassNormLinear K L) c) at h
      rw [map_add, hu0, add_zero, map_smul] at h
      exact h.symm
    have hβ := congrArg β.hom hq
    rw [map_nsmul] at hβ
    have hn := originalClassesModOutside_norm_comparison K L T hT c.toMul
    simpa only [Representation.norm, LinearMap.sum_apply] using hn.symm.trans hβ

end
end Dubon2026
