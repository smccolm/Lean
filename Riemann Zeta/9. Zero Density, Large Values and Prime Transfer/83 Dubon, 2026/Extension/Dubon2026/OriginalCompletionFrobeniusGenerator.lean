import Dubon2026.OriginalUnramifiedFrobeniusGenerator
import Dubon2026.OriginalCompletionFrobeniusLift

/-! The actual original completion has a generating arithmetic Frobenius
with the same global Chebotarev class. This supplies the finite local-image
generator needed to connect DUB-17's selected primes to fixed dimensions. -/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField Pointwise
attribute [-instance] UniformSpace.Completion.instSMul

/-- The original unramified completion Frobenius both represents the exact
global class and generates the entire original finite completion Galois group. -/
theorem originalCompletion_exists_frobenius_generator
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
    [w.asIdeal.LiesOver v.asIdeal] (hunr : Chebotarev.UnramifiedIn K L v.asIdeal) :
    letI : Algebra (v.adicCompletion K) (w.adicCompletion L) :=
      (originalAdicBaseChangeMap K L v w).toAlgebra
    ∃ σ : Gal(w.adicCompletion L/v.adicCompletion K),
      Chebotarev.frobeniusClass K L v.asIdeal =
        ConjClasses.mk (originalCompletionGaloisRestriction K L v w σ) ∧
      ∀ g : Gal(w.adicCompletion L/v.adicCompletion K), g ∈ Subgroup.zpowers σ := by
  letI : Algebra (v.adicCompletion K) (w.adicCompletion L) :=
    (originalAdicBaseChangeMap K L v w).toAlgebra
  letI : Finite (𝓞 L ⧸ w.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient w.ne_bot
  let τ := arithFrobAt (𝓞 K) Gal(L/K) w.asIdeal
  have hτ : IsArithFrobAt (𝓞 K) τ w.asIdeal := IsArithFrobAt.arithFrobAt _ _ _
  obtain ⟨d, hd⟩ := originalFiniteDecompositionIdealMap_surjective K L w ⟨τ, hτ.mem_stabilizer⟩
  have hdval : d.val = τ := congrArg Subtype.val hd
  let e := originalAdicDecompositionGaloisEquiv K L v w
  refine ⟨e d, ?_, fun g => ?_⟩
  · change Chebotarev.frobeniusClass K L v.asIdeal = ConjClasses.mk (e.symm (e d)).val
    rw [e.symm_apply_apply, hdval]
    exact Chebotarev.frobeniusClass_eq_mk_of_isArithFrobAt K L v.asIdeal hunr τ w.asIdeal hτ inferInstance
  · have hidx : v.asIdeal.ramificationIdx w.asIdeal = 1 := by
      rw [Ideal.over_def w.asIdeal v.asIdeal]
      exact Chebotarev.UnramifiedIn.ramificationIdx_eq_one K L hunr w.asIdeal inferInstance
    have hz := originalUnramified_frobenius_generates_stabilizer K L v w hidx τ hτ
      (originalFiniteDecompositionIdealMap K L w (e.symm g))
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hz
    have he : d ^ n = e.symm g := by
      apply Subtype.ext
      change d.val ^ n = (e.symm g).val
      rw [hdval]
      exact hn
    apply Subgroup.mem_zpowers_iff.mpr
    refine ⟨n, ?_⟩
    rw [← map_zpow, he, e.apply_symm_apply]

/-- Any original completion element with the prescribed global Frobenius
class is a generator. This applies directly to already-selected local
representatives, without changing the arithmetic prime or its embedding. -/
theorem originalCompletion_frobenius_class_generates
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
    [w.asIdeal.LiesOver v.asIdeal] (hunr : Chebotarev.UnramifiedIn K L v.asIdeal) :
    letI : Algebra (v.adicCompletion K) (w.adicCompletion L) :=
      (originalAdicBaseChangeMap K L v w).toAlgebra
    ∀ σ : Gal(w.adicCompletion L/v.adicCompletion K),
      Chebotarev.frobeniusClass K L v.asIdeal =
        ConjClasses.mk (originalCompletionGaloisRestriction K L v w σ) →
      ∀ g : Gal(w.adicCompletion L/v.adicCompletion K), g ∈ Subgroup.zpowers σ := by
  letI : Algebra (v.adicCompletion K) (w.adicCompletion L) :=
    (originalAdicBaseChangeMap K L v w).toAlgebra
  intro σ hσ g
  let e := originalAdicDecompositionGaloisEquiv K L v w
  letI : Finite Gal(w.adicCompletion L/v.adicCompletion K) :=
    Finite.of_equiv (OriginalFiniteDecompositionGroup K L w) e.toEquiv
  let f := originalCompletionGaloisRestriction K L v w
  have hf : Function.Injective f := Subtype.val_injective.comp e.symm.injective
  obtain ⟨τ, hτ, hgen⟩ := originalCompletion_exists_frobenius_generator K L v w hunr
  have hord : orderOf σ = orderOf τ := by
    rw [← orderOf_injective f hf σ, ← orderOf_injective f hf τ]
    have hc : IsConj (f σ) (f τ) := ConjClasses.mk_eq_mk_iff_isConj.mp (hσ.symm.trans hτ)
    obtain ⟨c, hc⟩ := hc
    exact hc.orderOf_eq
  have htop : Subgroup.zpowers σ = ⊤ :=
    Subgroup.eq_top_of_card_eq _ (by
      rw [Nat.card_zpowers, hord, orderOf_eq_card_of_forall_mem_zpowers hgen])
  rw [htop]
  exact Subgroup.mem_top _

end
end Dubon2026
