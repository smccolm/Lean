import Dubon2026.OriginalCyclicPrimePowerSubgroup
import Dubon2026.OriginalAuxiliaryCyclicExtension
import Dubon2026.OriginalDecompositionRestriction
import Dubon2026.OriginalPrimeTowerSelection

/-! # Full-decomposition primes for original cyclic prime-power extensions

The proved prime-degree avoidance theorem is applied to an actual degree-prime
subfield. Surjective restriction of the original prime stabilizers and the
cyclic subgroup lemma force full decomposition upstairs. This supplies the
full local degree required to construct a full-order idele-class H2 element
on DUB-17's normalized-invariant and reverse-localization dependency chain.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField

/-- Every original cyclic prime-power extension has a full-decomposition prime
above a base prime outside any prescribed finite set. -/
theorem original_cyclicPrimePower_exists_fullDecomposition_outside
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    (p n : ℕ) (hp : p.Prime) (hn : 0 < n)
    (hdegree : Module.finrank K L = p ^ n)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ w : HeightOneSpectrum (𝓞 L), originalFinitePrimeBelow K L w ∉ S ∧
      OriginalFiniteDecompositionGroup K L w = ⊤ := by
  obtain ⟨E, hGalois, _, hEdegree⟩ := originalCyclic_exists_intermediate_degree K L p hp.pos
    (hdegree ▸ dvd_pow_self p hn.ne')
  letI := hGalois
  letI : NumberField E := NumberField.of_module_finite K E
  obtain ⟨v, hv, hFull⟩ := original_primeDegree_exists_fullDecomposition_outside K E
    (hEdegree ▸ hp) S
  obtain ⟨w, hw⟩ := originalFinitePrimeBelow_surjective E L v
  refine ⟨w, ?_, ?_⟩
  · rw [← originalFinitePrimeBelow_tower K E L, hw]
    exact hv
  · by_contra hProper
    have hindex : (AlgEquiv.restrictNormalHom (F := K) (K₁ := L) E).ker.index = p := by
      rw [Subgroup.index_ker,
        MonoidHom.range_eq_top.mpr (AlgEquiv.restrictNormalHom_surjective (K₁ := E) L)]
      simpa only [Nat.card_congr (Subgroup.topEquiv).toEquiv] using
        (IsGalois.card_aut_eq_finrank K E).trans hEdegree
    have hle := originalCyclicPrimePower_subgroup_le_index_prime hp
      ((IsGalois.card_aut_eq_finrank K L).trans hdegree)
      (AlgEquiv.restrictNormalHom E).ker (OriginalFiniteDecompositionGroup K L w)
      hindex hProper
    have hbot := originalFiniteDecomposition_below_eq_bot_of_le_ker K L E w hle
    rw [hw, hFull] at hbot
    have hcardE := (IsGalois.card_aut_eq_finrank K E).trans hEdegree
    have h := congrArg Subgroup.index hbot
    simp only [Subgroup.index_top, Subgroup.index_bot, hcardE] at h
    exact hp.ne_one h.symm

end
end Dubon2026
