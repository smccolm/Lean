import Dubon2026.FinitePlaceLevelTopology
import Dubon2026.IntegralGamma0FiniteResidue
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.GroupTheory.Index

/-! # Genuine finite-index sublevels and their actual integral classical subgroups -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

/-- A prescribed genuine local subgroup pulls back to the actual original full finite level group. -/
def finiteAdelicPlaceSublevel (N : ℕ) (v : HeightOneSpectrum ℤ)
    (J : Subgroup (GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ))) :
    Subgroup (finiteAdeleGL2Gamma0 N) :=
  J.comap ((GeneralLinearGroup.map (finiteAdelePlace v)).comp (finiteAdeleGL2Gamma0 N).subtype)

/-- A genuine open local subgroup defines an actual open subgroup of the original compact finite level group. -/
theorem finiteAdelicPlaceSublevel_isOpen (N : ℕ) (v : HeightOneSpectrum ℤ)
    (J : Subgroup (GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ)))
    (hJ : IsOpen (J : Set (GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ)))) :
    IsOpen (finiteAdelicPlaceSublevel N v J : Set (finiteAdeleGL2Gamma0 N)) :=
  hJ.preimage ((finiteAdelePlace_continuous v).generalLinearGroup_map.comp continuous_subtype_val)

/-- Compactness of the original global level group proves finite index of every genuine local-open pullback. -/
theorem finiteAdelicPlaceSublevel_finiteIndex (N : ℕ) (v : HeightOneSpectrum ℤ)
    (J : Subgroup (GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ)))
    (hJ : IsOpen (J : Set (GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ)))) :
    (finiteAdelicPlaceSublevel N v J).FiniteIndex := by
  letI : CompactSpace (finiteAdeleGL2Gamma0 N) :=
    isCompact_iff_compactSpace.mp (finiteAdeleGL2Gamma0_isCompact N)
  letI : Finite ((finiteAdeleGL2Gamma0 N) ⧸ finiteAdelicPlaceSublevel N v J) :=
    (finiteAdelicPlaceSublevel N v J).quotient_finite_of_isOpen (finiteAdelicPlaceSublevel_isOpen N v J hJ)
  exact Subgroup.finiteIndex_of_finite_quotient

/-- The actual classical integral subgroup cut out by an original finite adelic sublevel. -/
def finiteAdelicSublevelIntegerGroup (N : ℕ) [NeZero N]
    (L : Subgroup (finiteAdeleGL2Gamma0 N)) : Subgroup SL(2, ℤ) :=
  (L.comap (integralGamma0FiniteGL2Hom N)).map (Gamma0 N).subtype

/-- An original Gamma0 matrix belongs to the actual sublevel integer group exactly when its genuine finite embedding belongs to the given sublevel. -/
theorem mem_finiteAdelicSublevelIntegerGroup (N : ℕ) [NeZero N]
    (L : Subgroup (finiteAdeleGL2Gamma0 N)) (γ : Gamma0 N) :
    γ.val ∈ finiteAdelicSublevelIntegerGroup N L ↔ integralGamma0FiniteGL2Hom N γ ∈ L := by
  constructor
  · rintro ⟨δ, hδ, he⟩
    have hd : δ = γ := Subtype.ext he
    exact hd ▸ hδ
  · intro hγ
    exact ⟨γ, hγ, rfl⟩

/-- The actual integral subgroup at a sublevel lies in the original Gamma0 subgroup. -/
theorem finiteAdelicSublevelIntegerGroup_le (N : ℕ) [NeZero N]
    (L : Subgroup (finiteAdeleGL2Gamma0 N)) :
    finiteAdelicSublevelIntegerGroup N L ≤ Gamma0 N := by
  rintro _ ⟨γ, hγ, rfl⟩
  exact γ.property

/-- The actual integral finite-level homomorphism is the finite component of the original rational matrix. -/
theorem integralGamma0FiniteGL2Hom_val (N : ℕ) [NeZero N] (γ : Gamma0 N) :
    (integralGamma0FiniteGL2Hom N γ).val =
      rationalGL2ToFinite (GeneralLinearGroup.map (Int.castRingHom ℚ) (toGL γ.val)) := by
  apply Units.ext
  funext i j
  exact (map_intCast (algebraMap ℚ (FiniteAdeleRing ℤ ℚ)) (γ.val i j)).symm

/-- Every genuine finite-index adelic sublevel yields a finite-index actual integral subgroup, so the existing general cusp-space finiteness theorem applies. -/
theorem finiteAdelicSublevelIntegerGroup_finiteIndex (N : ℕ) [NeZero N]
    (L : Subgroup (finiteAdeleGL2Gamma0 N)) [L.FiniteIndex] :
    (finiteAdelicSublevelIntegerGroup N L).FiniteIndex := by
  have hc : (L.comap (integralGamma0FiniteGL2Hom N)).index ≠ 0 := by
    rw [Subgroup.index_comap]
    exact (Subgroup.instFiniteIndex_subgroupOf L (integralGamma0FiniteGL2Hom N).range).index_ne_zero
  constructor
  rw [finiteAdelicSublevelIntegerGroup, Subgroup.index_map_subtype]
  exact mul_ne_zero hc (Subgroup.FiniteIndex.index_ne_zero (H := Gamma0 N))

end
end Dubon2026
