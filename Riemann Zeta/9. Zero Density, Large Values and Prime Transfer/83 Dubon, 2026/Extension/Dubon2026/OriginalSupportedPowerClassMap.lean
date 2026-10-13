import Dubon2026.OriginalIdelePowerLocalUnits

/-! # The actual supported-idele quotient maps onto its original local power classes

Reduction of actual components modulo powers retains all infinite places
and the finite places in S. Its kernel is exactly the source power/local-unit
subgroup inside the original S-union-T-supported ideles. Actual coordinate
assembly proves surjectivity. This is the local-product quotient needed for
DUB-17's selected-prime norm-index upper-bound calculation.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField Classical IsMulCommutative
variable (K : Type) [Field K] [NumberField K]

/-- The product of actual original local power-class groups at all infinite places and the specified finite places. -/
abbrev OriginalSupportedLocalPowerClasses (n : ℕ) (S : Finset (HeightOneSpectrum (𝓞 K))) :=
  ((w : InfinitePlace K) → w.Completionˣ ⧸ (powMonoidHom n : w.Completionˣ →* w.Completionˣ).range) ×
    ((v : S) → (v.val.adicCompletion K)ˣ ⧸
      (powMonoidHom n : (v.val.adicCompletion K)ˣ →* (v.val.adicCompletion K)ˣ).range)

/-- The local power-class product carries the canonical coordinatewise commutative group structure. -/
instance originalSupportedLocalPowerClassesCommGroup (n : ℕ) (S : Finset (HeightOneSpectrum (𝓞 K))) :
    CommGroup (OriginalSupportedLocalPowerClasses K n S) := by
  letI (w : InfinitePlace K) : CommGroup
      (w.Completionˣ ⧸ (powMonoidHom n : w.Completionˣ →* w.Completionˣ).range) := inferInstance
  letI (v : S) : CommGroup ((v.val.adicCompletion K)ˣ ⧸
      (powMonoidHom n : (v.val.adicCompletion K)ˣ →* (v.val.adicCompletion K)ˣ).range) := inferInstance
  exact inferInstanceAs (CommGroup
    (((w : InfinitePlace K) → w.Completionˣ ⧸ (powMonoidHom n : w.Completionˣ →* w.Completionˣ).range) ×
      ((v : S) → (v.val.adicCompletion K)ˣ ⧸
        (powMonoidHom n : (v.val.adicCompletion K)ˣ →* (v.val.adicCompletion K)ˣ).range)))

/-- The source local-condition subgroup inside the original supported ideles. -/
def originalSupportedPowerLocalUnitSubgroup (n : ℕ) (S T : Finset (HeightOneSpectrum (𝓞 K))) :
    Subgroup (numberFieldSupportedIdeles K (↑(S ∪ T) : Set (HeightOneSpectrum (𝓞 K)))) :=
  (originalIdelePowerLocalUnitSubgroup K n S T).comap (numberFieldSupportedIdeles K (↑(S ∪ T) : Set (HeightOneSpectrum (𝓞 K)))).subtype

/-- Membership in the actual power/local-unit subgroup implies the original supported-idele condition. -/
theorem originalIdelePowerLocalUnitSubgroup_le_supported (n : ℕ)
    (S T : Finset (HeightOneSpectrum (𝓞 K))) :
    originalIdelePowerLocalUnitSubgroup K n S T ≤ numberFieldSupportedIdeles K (↑(S ∪ T) : Set (HeightOneSpectrum (𝓞 K))) := by
  intro a ha
  have h := ((originalIdelePowerLocalUnitSubgroup_mem_iff K n S T a).mp ha).2.2
  simpa only [numberFieldSupportedIdeles, Subgroup.mem_iInf, Subgroup.mem_comap, Finset.mem_union, Set.mem_union, Finset.mem_coe] using h

/-- The map taking actual supported-idele components to their original local power classes. -/
def originalSupportedPowerClassMap (n : ℕ) (S T : Finset (HeightOneSpectrum (𝓞 K))) :
    numberFieldSupportedIdeles K (↑(S ∪ T) : Set (HeightOneSpectrum (𝓞 K))) →* OriginalSupportedLocalPowerClasses K n S where
  toFun a := (fun w => QuotientGroup.mk'
    (powMonoidHom n : w.Completionˣ →* w.Completionˣ).range (numberFieldIdeleInfiniteComponent K w a.val),
    fun v => QuotientGroup.mk' (powMonoidHom n : (v.val.adicCompletion K)ˣ →* (v.val.adicCompletion K)ˣ).range
      (numberFieldIdeleFiniteComponent K v.val a.val))
  map_one' := by
    apply Prod.ext
    · funext w
      change QuotientGroup.mk' (powMonoidHom n : w.Completionˣ →* w.Completionˣ).range
        (numberFieldIdeleInfiniteComponent K w 1) = 1
      rw [map_one, map_one]
    · funext v
      change QuotientGroup.mk' (powMonoidHom n : (v.val.adicCompletion K)ˣ →* (v.val.adicCompletion K)ˣ).range
        (numberFieldIdeleFiniteComponent K v.val 1) = 1
      rw [map_one, map_one]
  map_mul' a b := by
    apply Prod.ext
    · funext w
      change QuotientGroup.mk' (powMonoidHom n : w.Completionˣ →* w.Completionˣ).range
        (numberFieldIdeleInfiniteComponent K w (a.val * b.val)) = _
      rw [map_mul, map_mul]
      rfl
    · funext v
      change QuotientGroup.mk' (powMonoidHom n : (v.val.adicCompletion K)ˣ →* (v.val.adicCompletion K)ˣ).range
        (numberFieldIdeleFiniteComponent K v.val (a.val * b.val)) = _
      rw [map_mul, map_mul]
      rfl

/-- The actual component map has precisely the original power/local-unit subgroup as kernel. -/
theorem originalSupportedPowerClassMap_ker (n : ℕ) (S T : Finset (HeightOneSpectrum (𝓞 K))) :
    (originalSupportedPowerClassMap K n S T).ker = originalSupportedPowerLocalUnitSubgroup K n S T := by
  ext a
  change originalSupportedPowerClassMap K n S T a = 1 ↔ a.val ∈ originalIdelePowerLocalUnitSubgroup K n S T
  rw [originalIdelePowerLocalUnitSubgroup_mem_iff]
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro w
      exact (QuotientGroup.eq_one_iff _).mp (congrArg (fun z => z.1 w) h)
    · intro v hv
      exact (QuotientGroup.eq_one_iff _).mp (congrArg (fun z => z.2 ⟨v, hv⟩) h)
    · simpa only [numberFieldSupportedIdeles, Subgroup.mem_iInf, Subgroup.mem_comap, Finset.mem_union, Set.mem_union, Finset.mem_coe] using a.property
  · rintro ⟨hInf, hS, _⟩
    apply Prod.ext
    · funext w
      exact (QuotientGroup.eq_one_iff _).mpr (hInf w)
    · funext v
      exact (QuotientGroup.eq_one_iff _).mpr (hS v.val v.property)

/-- Every family of actual local power classes is represented by an original supported idele. -/
theorem originalSupportedPowerClassMap_surjective (n : ℕ) (S T : Finset (HeightOneSpectrum (𝓞 K))) :
    Function.Surjective (originalSupportedPowerClassMap K n S T) := by
  intro q
  choose yInf hyInf using (fun w : InfinitePlace K =>
    QuotientGroup.mk'_surjective (powMonoidHom n : w.Completionˣ →* w.Completionˣ).range (q.1 w))
  choose yFin hyFin using (fun v : S =>
    QuotientGroup.mk'_surjective (powMonoidHom n : (v.val.adicCompletion K)ˣ →* (v.val.adicCompletion K)ˣ).range (q.2 v))
  let y (v : HeightOneSpectrum (𝓞 K)) : (v.adicCompletion K)ˣ := if hv : v ∈ S then yFin ⟨v, hv⟩ else 1
  have hy : y ∈ numberFieldSupportedFiniteCoordinates K (↑(S ∪ T) : Set (HeightOneSpectrum (𝓞 K))) := by
    simp only [numberFieldSupportedFiniteCoordinates, Subgroup.mem_iInf, Subgroup.mem_comap, Pi.evalMonoidHom_apply]
    intro v hv
    have hs : v ∉ S := fun h => hv (Finset.mem_union_left T h)
    simpa only [y, dif_neg hs] using (v.adicCompletionIntegers K).units.one_mem
  let a := (numberFieldSupportedIdeleCoordinateEquiv K (S ∪ T)).symm (yInf, ⟨y, hy⟩)
  have ha := (numberFieldSupportedIdeleCoordinateEquiv K (S ∪ T)).apply_symm_apply (yInf, ⟨y, hy⟩)
  refine ⟨a, ?_⟩
  apply Prod.ext
  · funext w
    change QuotientGroup.mk' (powMonoidHom n).range (numberFieldIdeleInfiniteComponent K w a.val) = q.1 w
    rw [← numberFieldSupportedIdeleCoordinateEquiv_infinite K (S ∪ T) a w]
    rw [show numberFieldSupportedIdeleCoordinateEquiv K (S ∪ T) a = (yInf, ⟨y, hy⟩) from ha]
    exact hyInf w
  · funext v
    change QuotientGroup.mk' (powMonoidHom n).range (numberFieldIdeleFiniteComponent K v.val a.val) = q.2 v
    rw [← numberFieldSupportedIdeleCoordinateEquiv_finite K (S ∪ T) a v.val]
    rw [show numberFieldSupportedIdeleCoordinateEquiv K (S ∪ T) a = (yInf, ⟨y, hy⟩) from ha]
    change QuotientGroup.mk' (powMonoidHom n).range (y v.val) = q.2 v
    rw [show y v.val = yFin v from dif_pos v.property]
    exact hyFin v

end
end Dubon2026
