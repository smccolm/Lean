import Dubon2026.FiniteAdelicLevelLocalization
import Dubon2026.FiniteAdelicLocalTopology
import Dubon2026.FiniteAdelicCompactLevel

/-! # Compactness and openness of the original finite-place level group -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix

/-- Genuine finite-place evaluation is continuous in the original restricted-product topology. -/
theorem finiteAdelePlace_continuous (v : HeightOneSpectrum ℤ) : Continuous (finiteAdelePlace v) :=
  RestrictedProduct.continuous_eval v

/-- The actual local level group is exactly the preimage under the genuine one-place insertion. -/
theorem finitePlaceGL2Gamma0_eq_local_preimage (N : ℕ) [NeZero N] (v : HeightOneSpectrum ℤ) :
    (finitePlaceGL2Gamma0 N v : Set (GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ))) =
      finiteAdelicLocalGL2Hom v ⁻¹' (finiteAdeleGL2Gamma0 N :
        Set (GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ))) := by
  ext g
  constructor
  · intro hg
    exact finiteAdelicLocal_level_mem N v ⟨g, hg⟩
  · intro hg
    have he := (finiteAdeleGL2Gamma0_iff_places N _).mp hg v
    change GeneralLinearGroup.map (finiteAdelePlace v) (finiteAdelicLocalGL2 v g) ∈
      finitePlaceGL2Gamma0 N v at he
    simpa only [finiteAdelicLocalGL2_same] using he

/-- The genuine local level group is open in the original local GL2 topology. -/
theorem finitePlaceGL2Gamma0_isOpen (N : ℕ) [NeZero N] (v : HeightOneSpectrum ℤ) :
    IsOpen (finitePlaceGL2Gamma0 N v : Set (GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ))) := by
  rw [finitePlaceGL2Gamma0_eq_local_preimage]
  exact (finiteAdeleGL2Gamma0_isOpen N).preimage (finiteAdelicLocalGL2_continuous v)

/-- The actual local level group is precisely the image of the original full finite level group. -/
theorem finitePlaceGL2Gamma0_eq_place_image (N : ℕ) [NeZero N] (v : HeightOneSpectrum ℤ) :
    (finitePlaceGL2Gamma0 N v : Set (GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ))) =
      GeneralLinearGroup.map (finiteAdelePlace v) '' (finiteAdeleGL2Gamma0 N :
        Set (GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ))) := by
  ext g
  constructor
  · intro hg
    obtain ⟨h, he⟩ := finiteAdelicLevelAt_surjective N v ⟨g, hg⟩
    exact ⟨h.val, h.property, congrArg Subtype.val he⟩
  · rintro ⟨h, hh, rfl⟩
    exact (finiteAdeleGL2Gamma0_iff_places N h).mp hh v

/-- The actual local level group is compact, as the genuine continuous image of the original finite adelic compact level group. -/
theorem finitePlaceGL2Gamma0_isCompact (N : ℕ) [NeZero N] (v : HeightOneSpectrum ℤ) :
    IsCompact (finitePlaceGL2Gamma0 N v : Set (GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ))) := by
  rw [finitePlaceGL2Gamma0_eq_place_image]
  exact (finiteAdeleGL2Gamma0_isCompact N).image (finiteAdelePlace_continuous v).generalLinearGroup_map

end
end Dubon2026
