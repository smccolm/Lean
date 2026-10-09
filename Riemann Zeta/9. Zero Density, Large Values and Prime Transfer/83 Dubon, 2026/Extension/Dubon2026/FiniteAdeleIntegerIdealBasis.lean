import Dubon2026.CompactRingIntegerIdeals
import Dubon2026.FiniteAdelicCompactLevel
import Dubon2026.FiniteAdeleClassicalIntersection

/-! # Genuine ordinary integer ideals are cofinal in the original finite-adelic neighborhoods -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Filter Set Topology

/-- Distinct original ordinary integers remain distinct in the genuine integral finite adele ring. -/
theorem finiteAdeleIntegerSubring_int_injective :
    Function.Injective (Int.cast : ℤ → finiteAdeleIntegerSubring) := by
  intro n m h
  let v : HeightOneSpectrum ℤ := Rat.HeightOneSpectrum.primesEquiv.symm ⟨2, by decide⟩
  have he := congrArg (fun x : finiteAdeleIntegerSubring => x.val v) h
  change (n : v.adicCompletion ℚ) = (m : v.adicCompletion ℚ) at he
  have hq : (n : ℚ) = (m : ℚ) :=
    (algebraMap ℚ (v.adicCompletion ℚ)).injective (by simpa only [map_intCast] using he)
  exact Int.cast_injective hq

/-- The actual integral finite adele ring is infinite, witnessed by its original integer embedding. -/
instance finiteAdeleIntegerSubringInfinite : Infinite finiteAdeleIntegerSubring :=
  Infinite.of_injective (Int.cast : ℤ → finiteAdeleIntegerSubring) finiteAdeleIntegerSubring_int_injective

/-- Ordinary integers are dense in the original everywhere-integral finite adele ring. -/
theorem finiteAdeleIntegerSubring_int_dense : DenseRange (Int.cast : ℤ → finiteAdeleIntegerSubring) := by
  apply dense_iff_inter_open.mpr
  intro U hU hne
  have hopen : IsOpen (Subtype.val '' U : Set (FiniteAdeleRing ℤ ℚ)) :=
    finiteAdeleIntegerSubring_isOpen.isOpenMap_subtype_val U hU
  obtain ⟨q, y, hyU, hyq⟩ := rational_dense_finiteAdeles.exists_mem_open hopen (hne.image Subtype.val)
  have hqi : algebraMap ℚ (FiniteAdeleRing ℤ ℚ) q ∈ finiteAdeleIntegerSubring := hyq ▸ y.property
  obtain ⟨n, hn⟩ := (finiteAdele_rational_integral_iff q).mp hqi
  have he : (n : finiteAdeleIntegerSubring) = y := by
    apply Subtype.ext
    rw [hyq, ← hn, map_intCast]
    rfl
  exact ⟨y, hyU, n, he⟩

/-- Every original finite-adelic zero neighborhood contains a genuine positive ordinary integer ideal of the entire integral subring. -/
theorem finiteAdeleLevelMultiple_cofinal (U : Set (FiniteAdeleRing ℤ ℚ)) (hU : U ∈ 𝓝 0) :
    ∃ D : ℕ, 0 < D ∧ ∀ x, finiteAdeleLevelMultiple D x → x ∈ U := by
  letI : CompactSpace finiteAdeleIntegerSubring :=
    isCompact_iff_compactSpace.mp finiteAdeleIntegerSubring_isCompact
  have hV : {x : finiteAdeleIntegerSubring | x.val ∈ U} ∈ 𝓝 0 :=
    continuous_subtype_val.continuousAt hU
  obtain ⟨D, hD, hsmall⟩ := compactRing_positive_integer_ideal_small
    finiteAdeleIntegerSubring_int_dense _ hV
  refine ⟨D, hD, ?_⟩
  rintro x ⟨y, hy, hxy⟩
  have h := hsmall ⟨y, hy⟩
  change (D : FiniteAdeleRing ℤ ℚ) * y ∈ U at h
  rwa [← hxy] at h

end
end Dubon2026
