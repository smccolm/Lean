import Dubon2026.OriginalIdeleSingleFiniteEquivariance
import Dubon2026.CoinducedCohomologyTrace

/-! # The original single-prime coinduced trace

For the actual decomposition subgroup, the finite coset trace of the
single-prime coefficient insertion evaluates at that prime by identity
evaluation. This is the local section required for DUB-17's normalization,
without a general Mackey formula for arbitrary coefficients.
-/
namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField Classical BigOperators
attribute [local instance 1100] Rep.hV2
variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]

/-- A translated single-prime idele has identity coordinate away from the translated prime. -/
theorem originalIdeleSingleFinite_galois_other (w v : HeightOneSpectrum (𝓞 L))
    (σ : Gal(L/K)) (hv : numberFieldGaloisPlaceEquiv K L σ w ≠ v)
    (u : (w.adicCompletion L)ˣ) :
    numberFieldIdeleFiniteComponent L v
      (numberFieldIdeleGaloisMap K L σ (originalIdeleSingleFinite L w u)) = 1 := by
  apply Units.ext
  let e := numberFieldGaloisPlaceEquiv K L σ
  have he : e.symm v ≠ w := by
    intro h
    exact hv ((congrArg e h).symm.trans (e.apply_symm_apply v))
  change numberFieldFiniteAdeleGaloisMap K L σ (originalIdeleSingleFinite L w u).val.2 v = 1
  rw [numberFieldFiniteAdeleGaloisMap_apply K L σ _ (e.symm v) v (e.apply_symm_apply v)]
  have hc := congrArg Units.val (originalIdeleSingleFinite_ne L w (e.symm v) he u)
  change (originalIdeleSingleFinite L w u).val.2 (e.symm v) = 1 at hc
  rw [hc, map_one]

variable (w : HeightOneSpectrum (𝓞 L))
  [Fintype (Gal(L/K) ⧸ OriginalFiniteDecompositionGroup K L w)]

/-- Trace the genuine coinduced single-prime insertion into the original full ideles. -/
def originalSinglePrimeCoinducedTrace :
    Rep.coind (OriginalFiniteDecompositionGroup K L w).subtype (originalAdicUnitRep K L w) ⟶
      originalFullIdeleRep K L :=
    (Rep.coindFunctor ℤ (OriginalFiniteDecompositionGroup K L w).subtype).map
      (originalIdeleSingleFiniteRepHom K L w) ≫
        coinducedCosetTrace (originalFullIdeleRep K L) (OriginalFiniteDecompositionGroup K L w)

omit [Fintype (Gal(L/K) ⧸ OriginalFiniteDecompositionGroup K L w)] in
/-- Every nonidentity decomposition coset contributes zero at the original chosen prime. -/
theorem originalSinglePrimeCoinducedTrace_other_coset
    (x : Rep.coind (OriginalFiniteDecompositionGroup K L w).subtype (originalAdicUnitRep K L w))
    (q : Gal(L/K) ⧸ OriginalFiniteDecompositionGroup K L w)
    (hq : q ≠ QuotientGroup.mk (1 : Gal(L/K))) :
    (originalFullIdeleAdicRepHom K L w).hom
      (coinducedCosetValues (originalFullIdeleRep K L) (OriginalFiniteDecompositionGroup K L w)
        (((Rep.coindFunctor ℤ (OriginalFiniteDecompositionGroup K L w).subtype).map
          (originalIdeleSingleFiniteRepHom K L w)).hom x) q) = 0 := by
  induction q using QuotientGroup.induction_on with
  | H g =>
    have hg : g ∉ OriginalFiniteDecompositionGroup K L w := by
      intro h
      apply hq
      apply QuotientGroup.eq.mpr
      simpa only [mul_one] using (OriginalFiniteDecompositionGroup K L w).inv_mem h
    exact congrArg Additive.ofMul
      (originalIdeleSingleFinite_galois_other K L w w g hg (x.val g⁻¹).toMul)

/-- Evaluation of the actual single-prime coset trace is precisely evaluation of the coinduced function at the identity. -/
theorem originalSinglePrimeCoinducedTrace_evaluation
    (x : Rep.coind (OriginalFiniteDecompositionGroup K L w).subtype (originalAdicUnitRep K L w)) :
    (originalFullIdeleAdicRepHom K L w).hom ((originalSinglePrimeCoinducedTrace K L w).hom x) =
      x.val 1 := by
  change (originalFullIdeleAdicRepHom K L w).hom
    (∑ q : Gal(L/K) ⧸ OriginalFiniteDecompositionGroup K L w,
      coinducedCosetValues (originalFullIdeleRep K L) (OriginalFiniteDecompositionGroup K L w)
        (((Rep.coindFunctor ℤ (OriginalFiniteDecompositionGroup K L w).subtype).map
          (originalIdeleSingleFiniteRepHom K L w)).hom x) q) = _
  rw [map_sum, Finset.sum_eq_single (QuotientGroup.mk (1 : Gal(L/K)))]
  · rw [coinducedCosetValues_mk, map_one, Module.End.one_apply]
    exact congrArg Additive.ofMul (originalIdeleSingleFinite_same L w (x.val 1).toMul)
  · intro q _ hq
    exact originalSinglePrimeCoinducedTrace_other_coset K L w x q hq
  · intro h
    exact (h (Finset.mem_univ _)).elim

/-- The single-prime trace has zero coefficient at every original prime outside its Galois orbit. -/
theorem originalSinglePrimeCoinducedTrace_outside_orbit
    (v : HeightOneSpectrum (𝓞 L))
    (hv : ∀ σ : Gal(L/K), numberFieldGaloisPlaceEquiv K L σ w ≠ v)
    (x : Rep.coind (OriginalFiniteDecompositionGroup K L w).subtype (originalAdicUnitRep K L w)) :
    (originalFullIdeleAdicRepHom K L v).hom ((originalSinglePrimeCoinducedTrace K L w).hom x) = 0 := by
  change (originalFullIdeleAdicRepHom K L v).hom
    (∑ q : Gal(L/K) ⧸ OriginalFiniteDecompositionGroup K L w,
      coinducedCosetValues (originalFullIdeleRep K L) (OriginalFiniteDecompositionGroup K L w)
        (((Rep.coindFunctor ℤ (OriginalFiniteDecompositionGroup K L w).subtype).map
          (originalIdeleSingleFiniteRepHom K L w)).hom x) q) = 0
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro q _
  induction q using QuotientGroup.induction_on with
  | H g =>
    exact congrArg Additive.ofMul
      (originalIdeleSingleFinite_galois_other K L w v g (hv g) (x.val g⁻¹).toMul)

end
end Dubon2026
