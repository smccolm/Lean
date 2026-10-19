import Dubon2026.OriginalLocalCompletionEquivContinuity
import Dubon2026.NumberFieldGaloisLocalTransport

/-! An automorphism fixing the actual induced original prime extends
to its generated local field. The existing completed transport constructs
the map; continuity and rational density show that it fixes the entire
rational prime completion. This supplies the local lift required for
Dubon Theorem 2.6's original-support quotient comparison. -/

namespace Dubon2026
noncomputable section
open IsDedekindDomain
open scoped NumberField ValuativeRel

variable (F L : Type) [Field F] [NumberField F] [NormedField L] [Algebra F L]
  (p : ℕ) (hp : p.Prime) [Algebra (rationalPrimeLocalField p hp) L]
  [ValuativeRel L] [IsNonarchimedeanLocalField L]
  [(ValuativeRel.valuation (rationalPrimeLocalField p hp)).HasExtension (ValuativeRel.valuation L)]

omit [Algebra F L] [Field F] [NumberField F] in
private theorem continuous_ringAut_fixes_primeBase (g : L ≃+* L) (hg : Continuous g) :
    ∀ x : rationalPrimeLocalField p hp, g (algebraMap (rationalPrimeLocalField p hp) L x) =
      algebraMap (rationalPrimeLocalField p hp) L x := by
  have hc := originalLocalScalar_continuous (rationalPrimeLocalField p hp) L
  have h : (fun x : rationalPrimeLocalField p hp => g (algebraMap (rationalPrimeLocalField p hp) L x)) =
      algebraMap (rationalPrimeLocalField p hp) L := by
    apply funext
    apply UniformSpace.Completion.ext' (hg.comp hc) hc
    intro x
    change g (algebraMap (rationalPrimeLocalField p hp) L
      (algebraMap ℚ (rationalPrimeLocalField p hp) x.ofVal)) =
        algebraMap (rationalPrimeLocalField p hp) L
          (algebraMap ℚ (rationalPrimeLocalField p hp) x.ofVal)
    simp only [eq_ratCast, map_ratCast]
  exact congrFun h

/-- The actual prime-stabilizing original field automorphism extends
to an automorphism over the full original rational completion. -/
theorem originalGeneratedLocalField_exists_automorphism
    (hgen : (algebraMap (rationalPrimeLocalField p hp) L).fieldRange ⊔
      (algebraMap F L).fieldRange = ⊤)
    (σ : Gal(F/ℚ))
    (hσ : numberFieldGaloisPlaceEquiv ℚ F σ (originalLocalEmbeddingPrime F L p hp) =
      originalLocalEmbeddingPrime F L p hp) :
    ∃ g : Gal(L/rationalPrimeLocalField p hp),
      ∀ x : F, g (algebraMap F L x) = algebraMap F L (σ x) := by
  let w := originalLocalEmbeddingPrime F L p hp
  let e := originalLocalCompletionEquiv F L p hp hgen
  let t := numberFieldGaloisLocalTransport ℚ F σ w w hσ
  let u := (e.symm.trans t).trans e
  have hu : Continuous u := (originalLocalCompletionEquiv_continuous F L p hp hgen).comp
    ((numberFieldGaloisLocalTransport_continuous ℚ F σ w w hσ).comp
      (originalLocalCompletionEquiv_symm_continuous F L p hp hgen))
  let g : Gal(L/rationalPrimeLocalField p hp) := {
    u with commutes' := continuous_ringAut_fixes_primeBase L p hp u hu }
  refine ⟨g, ?_⟩
  intro x
  have he := originalLocalCompletionEquiv_algebraMap F L p hp hgen x
  change e (t (e.symm (algebraMap F L x))) = algebraMap F L (σ x)
  rw [← he, e.symm_apply_apply]
  exact (congrArg e (numberFieldGaloisLocalTransport_algebraMap ℚ F σ w w hσ x)).trans
    (originalLocalCompletionEquiv_algebraMap F L p hp hgen (σ x))

end
end Dubon2026
