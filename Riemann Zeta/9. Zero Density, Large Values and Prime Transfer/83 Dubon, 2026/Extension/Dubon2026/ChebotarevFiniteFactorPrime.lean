import Dubon2026.Reuse.Chebotarev.Main
import Dubon2026.ContinuousGaloisFiniteFactors

/-! Prescribed Frobenius primes for the actual finite field constructed by the
native continuous Galois factorization theorem. This is the prime-existence
input to DUB-17's arithmetic patching chain. Image conditions, dual Selmer
detection, and a full Taylor-Wiles system are not asserted. -/

namespace Dubon2026
noncomputable section
open scoped NumberField

variable {K Ω T : Type*} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
  [IsGalois K Ω] [Group T] [TopologicalSpace T] [DiscreteTopology T]

/-- Outside every specified finite set, a prime realizes the conjugacy class
of the image of any original Galois element in the actual constructed finite
factor. The finite field and representation factor are produced by the native
continuous factorization theorem; continuity discharges the open-kernel
condition, and no independent finite-field witness is assumed. -/
theorem continuous_galois_exists_frobenius_prime
    (χ : Gal(Ω/K) →ₜ* T) :
    ∃ F : FiniteGaloisIntermediateField K Ω,
      ∃ ψ : Gal(F/K) →* T,
        (∀ g : Gal(Ω/K), ψ (AlgEquiv.restrictNormalHom F g) = χ g) ∧
        (letI : NumberField F := NumberField.of_module_finite K F
         ∀ (g : Gal(Ω/K)) (S : Finset (Ideal (𝓞 K))),
           ∃ v : Ideal (𝓞 K), v ∉ S ∧ v.IsPrime ∧ Chebotarev.UnramifiedIn K F v ∧
             Chebotarev.frobeniusClass K F v =
               ConjClasses.mk (AlgEquiv.restrictNormalHom F g) ∧
             IsConj (ψ (Chebotarev.frobeniusClass K F v).out) (χ g)) := by
  obtain ⟨F, ψ, hψ⟩ := continuous_galois_finite_factor χ
  refine ⟨F, ψ, hψ, ?_⟩
  letI : NumberField F := NumberField.of_module_finite K F
  intro g S
  obtain ⟨v, hv, hvS⟩ :=
    ((Chebotarev.infinite_setOf_frobenius_class
      (ConjClasses.mk (AlgEquiv.restrictNormalHom F g))).diff S.finite_toSet).nonempty
  refine ⟨v, hvS, hv.1, hv.2.1, hv.2.2, ?_⟩
  have hc : IsConj (Chebotarev.frobeniusClass K F v).out
      (AlgEquiv.restrictNormalHom F g) := by
    apply ConjClasses.mk_eq_mk_iff_isConj.mp
    exact (Quotient.out_eq _).trans hv.2.2
  simpa only [hψ] using ψ.map_isConj hc

end
end Dubon2026
