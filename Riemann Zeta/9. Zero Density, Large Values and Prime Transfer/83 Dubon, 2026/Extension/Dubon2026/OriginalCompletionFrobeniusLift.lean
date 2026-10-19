import Dubon2026.Reuse.Chebotarev.Frobenius
import Dubon2026.OriginalGlobalCompletionH2
import Dubon2026.OriginalAdicDecompositionDegree

/-! The Chebotarev Frobenius conjugacy class is represented by an actual
automorphism of the original completion. This connects prescribed primes to
the existing local restriction maps used in DUB-17 dual Selmer detection. -/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField
attribute [-instance] UniformSpace.Completion.instSMul

/-- The original completion Galois group supplies a representative of the
actual Frobenius class, via the proved original decomposition-group equivalence. -/
theorem originalCompletion_exists_frobenius
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
    [w.asIdeal.LiesOver v.asIdeal] (hunr : Chebotarev.UnramifiedIn K L v.asIdeal) :
    letI : Algebra (v.adicCompletion K) (w.adicCompletion L) :=
      (originalAdicBaseChangeMap K L v w).toAlgebra
    ∃ σ : Gal(w.adicCompletion L/v.adicCompletion K),
      Chebotarev.frobeniusClass K L v.asIdeal =
        ConjClasses.mk (originalCompletionGaloisRestriction K L v w σ) := by
  letI : Algebra (v.adicCompletion K) (w.adicCompletion L) :=
    (originalAdicBaseChangeMap K L v w).toAlgebra
  letI : Finite (𝓞 L ⧸ w.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient w.ne_bot
  let τ := arithFrobAt (𝓞 K) Gal(L/K) w.asIdeal
  obtain ⟨d, hd⟩ := originalFiniteDecompositionIdealMap_surjective K L w
    ⟨τ, IsArithFrobAt.arithFrobAt_mem_stabilizer (𝓞 K) Gal(L/K) w.asIdeal⟩
  have hdval : d.val = τ := congrArg Subtype.val hd
  let e := originalAdicDecompositionGaloisEquiv K L v w
  refine ⟨e d, ?_⟩
  change Chebotarev.frobeniusClass K L v.asIdeal = ConjClasses.mk (e.symm (e d)).val
  rw [e.symm_apply_apply, hdval]
  exact Chebotarev.frobeniusClass_eq_mk_of_isArithFrobAt K L v.asIdeal hunr τ w.asIdeal
    (IsArithFrobAt.arithFrobAt (𝓞 K) Gal(L/K) w.asIdeal) inferInstance

end
end Dubon2026
