import Dubon2026.ArithmeticFiniteOriginalSupportEmbedding
import Dubon2026.ArithmeticSupportRestriction

/-! The auxiliary inertia relations force the kernel of the actual
restriction to original support to act trivially. This discharges the
group-theoretic descent assumption in the base-support deformation
comparison for Dubon Theorem 2.6. -/

namespace Dubon2026
noncomputable section
open scoped NumberField BigOperators
attribute [local instance] rationalArithmeticOriginalFiniteGalois

private theorem embedded_finite_factor_kernel_le
    {K E F Ω G T : Type} [Field K] [Field E] [Field F] [Group G] [Group T]
    [Algebra K E] [Algebra K F]
    (j : E → Ω) (z : F → Ω) (hz : Function.Injective z) (act : G → Ω → Ω)
    (π : G →* Gal(E/K)) (r : G →* Gal(F/K))
    (hπ : ∀ g x, j (π g x) = act g (j x))
    (hr : ∀ g x, z (r g x) = act g (z x))
    (i : F → E) (hi : ∀ x, j (i x) = z x)
    (χ : G →* T) (ψ : Gal(F/K) →* T) (hf : ∀ g, ψ (r g) = χ g) :
    π.ker ≤ χ.ker := by
  intro g hg
  have hg' : π g = 1 := hg
  have he : r g = 1 := by
    apply AlgEquiv.ext
    intro x
    apply hz
    have hc := hπ g (i x)
    rw [hg'] at hc
    change j (i x) = act g (j (i x)) at hc
    rw [hi x] at hc
    exact (hr g x).trans hc.symm
  change χ g = 1
  exact (hf g).symm.trans ((congrArg ψ he).trans ψ.map_one)

private theorem arithmetic_support_embedding_commutes
    (a b : 𝓞 ℚ) (hab : a ∣ b)
    (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension b))
    (i : F →ₐ[ℚ] rationalUnramifiedExtension a)
    (hi : ∀ x : F, (i x : AlgebraicClosure ℚ) = (x.val : AlgebraicClosure ℚ))
    (x : F) : rationalArithmeticSupportInclusion a b hab (i x) = x.val := by
  apply Subtype.ext
  exact (IntermediateField.coe_inclusion (originalUnramifiedGaloisUnion_mono_dvd hab) (i x)).trans (hi x)

private theorem arithmetic_finite_restriction_commutes
    (b : 𝓞 ℚ) (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension b))
    (g : rationalArithmeticGaloisGroup b) (x : F) :
    ((AlgEquiv.restrictNormalHom F (show Gal(rationalUnramifiedExtension b/ℚ) from g)) x).val =
      (show Gal(rationalUnramifiedExtension b/ℚ) from g) x.val :=
  (show Gal(rationalUnramifiedExtension b/ℚ) from g).restrictNormal_commutes F x

private theorem arithmetic_embedded_finite_factor_kernel_le
    {T : Type} [Group T] (a b : 𝓞 ℚ) (hab : a ∣ b)
    (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension b))
    (i : F →ₐ[ℚ] rationalUnramifiedExtension a)
    (hi : ∀ x : F, (i x : AlgebraicClosure ℚ) = (x.val : AlgebraicClosure ℚ))
    (χ : rationalArithmeticGaloisGroup b →* T) (ψ : Gal(F/ℚ) →* T)
    (hf : ∀ g, ψ (AlgEquiv.restrictNormalHom F g) = χ g) :
    (rationalArithmeticSupportRestriction a b hab).toMonoidHom.ker ≤ χ.ker := by
  exact embedded_finite_factor_kernel_le (rationalArithmeticSupportInclusion a b hab)
    (fun x : F => x.val) Subtype.val_injective
    (fun g x => (show Gal(rationalUnramifiedExtension b/ℚ) from g) x)
    (rationalArithmeticSupportRestriction a b hab).toMonoidHom
    (AlgEquiv.restrictNormalHom F)
    (rationalArithmeticSupportRestriction_commutes a b hab)
    (arithmetic_finite_restriction_commutes b F)
    i (arithmetic_support_embedding_commutes a b hab F i hi) χ ψ hf

/-- A discrete continuous arithmetic representation killing the actual
auxiliary inertia groups kills the full kernel of restriction to the
original support. The faithful finite field and its original-support
embedding are constructed from the representation. -/
theorem continuousArithmetic_original_support_kernel
    {T : Type} [Group T] [TopologicalSpace T] [DiscreteTopology T]
    (a b : 𝓞 ℚ) (hb : b ≠ 0) (Q : Finset Nat.Primes)
    (hba : b = a * ∏ p ∈ Q, (p.val : 𝓞 ℚ)) (hab : a ∣ b)
    (χ : rationalArithmeticGaloisGroup b →ₜ* T)
    (hI : ∀ (p : Q) g, g ∈ rationalPrimeNormInertia p.val.val p.val.property →
      χ (rationalPrimeArithmeticRestriction b p.val.val p.val.property g) = 1) :
    (rationalArithmeticSupportRestriction a b hab).toMonoidHom.ker ≤ χ.toMonoidHom.ker := by
  obtain ⟨F, ψ, _, hf, hQ⟩ := continuousArithmetic_faithful_unramified_factor b χ Q hI
  obtain ⟨i, hi⟩ := rationalArithmetic_finite_original_support_embedding a b hb Q hba F hQ
  exact arithmetic_embedded_finite_factor_kernel_le a b hab F i hi χ.toMonoidHom ψ hf

end
end Dubon2026
