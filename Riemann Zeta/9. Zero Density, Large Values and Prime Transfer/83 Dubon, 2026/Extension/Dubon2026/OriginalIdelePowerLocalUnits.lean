import Dubon2026.OriginalIdeleLocalUnitAssembly
import Dubon2026.NumberFieldSupportedIdeleExact

/-! # The power/local-unit subgroup of the original idele group

These are the actual source local conditions: n-th powers at every
infinite place and at S, no finite restriction at T outside S, and
original integer units outside S union T. Its original class image is
the quotient input to DUB-17's prime-degree norm-index upper bound.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField Classical
variable (K : Type) [Field K] [NumberField K]

/-- The original finite local condition: powers at S, arbitrary units at T outside S, integer units elsewhere. -/
def originalFinitePowerLocalUnitCondition (n : ℕ)
    (S T : Finset (HeightOneSpectrum (𝓞 K))) (v : HeightOneSpectrum (𝓞 K)) :
    Subgroup (v.adicCompletion K)ˣ :=
  if v ∈ S then (powMonoidHom n).range else if v ∈ T then ⊤ else (v.adicCompletionIntegers K).units

/-- The actual original idele power/local-unit subgroup with its full finite and infinite local conditions. -/
def originalIdelePowerLocalUnitSubgroup (n : ℕ) (S T : Finset (HeightOneSpectrum (𝓞 K))) :
    Subgroup (AdeleRing (𝓞 K) K)ˣ :=
  (⨅ w : InfinitePlace K, ((powMonoidHom n).range).comap (numberFieldIdeleInfiniteComponent K w)) ⊓
    ⨅ v : HeightOneSpectrum (𝓞 K),
      (originalFinitePowerLocalUnitCondition K n S T v).comap (numberFieldIdeleFiniteComponent K v)

/-- Membership retains exactly the specified powers and original integer units at the actual places. -/
theorem originalIdelePowerLocalUnitSubgroup_mem_iff (n : ℕ)
    (S T : Finset (HeightOneSpectrum (𝓞 K))) (a : (AdeleRing (𝓞 K) K)ˣ) :
    a ∈ originalIdelePowerLocalUnitSubgroup K n S T ↔
      (∀ w : InfinitePlace K, numberFieldIdeleInfiniteComponent K w a ∈ (powMonoidHom n).range) ∧
      (∀ v : HeightOneSpectrum (𝓞 K), v ∈ S →
        numberFieldIdeleFiniteComponent K v a ∈ (powMonoidHom n).range) ∧
      (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S ∪ T →
        numberFieldIdeleFiniteComponent K v a ∈ (v.adicCompletionIntegers K).units) := by
  simp only [originalIdelePowerLocalUnitSubgroup, Subgroup.mem_inf, Subgroup.mem_iInf,
    Subgroup.mem_comap]
  constructor
  · rintro ⟨hInf, hFin⟩
    refine ⟨hInf, ?_, ?_⟩
    · intro v hv
      simpa only [originalFinitePowerLocalUnitCondition, if_pos hv] using hFin v
    · intro v hv
      have hs : v ∉ S := fun h => hv (Finset.mem_union_left T h)
      have ht : v ∉ T := fun h => hv (Finset.mem_union_right S h)
      simpa only [originalFinitePowerLocalUnitCondition, if_neg hs, if_neg ht] using hFin v
  · rintro ⟨hInf, hS, hAway⟩
    refine ⟨hInf, ?_⟩
    intro v
    by_cases hs : v ∈ S
    · simpa only [originalFinitePowerLocalUnitCondition, if_pos hs] using hS v hs
    · by_cases ht : v ∈ T
      · simp only [originalFinitePowerLocalUnitCondition, if_neg hs, if_pos ht, Subgroup.mem_top]
      · simpa only [originalFinitePowerLocalUnitCondition, if_neg hs, if_neg ht] using
          hAway v (by simpa only [Finset.mem_union, not_or] using And.intro hs ht)

/-- The corresponding subgroup in the actual original idele class group is the image of the actual idele subgroup. -/
def originalIdeleClassPowerLocalUnitSubgroup (n : ℕ) (S T : Finset (HeightOneSpectrum (𝓞 K))) :
    Subgroup (OriginalNumberFieldIdeleClassGroup K) :=
  (originalIdelePowerLocalUnitSubgroup K n S T).map (QuotientGroup.mk' (numberFieldPrincipalIdele K).range)

end
end Dubon2026
