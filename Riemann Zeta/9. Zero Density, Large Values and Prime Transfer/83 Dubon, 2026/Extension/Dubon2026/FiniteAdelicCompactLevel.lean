import Dubon2026.RationalAdelicAdditiveHaar
import Dubon2026.FiniteAdelicGL2Level
import Mathlib.Topology.Algebra.Group.Pointwise

/-! # Genuine compact open finite adelic level groups and local compactness -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Set Topology

/-- The actual canonical finite adele ring is Hausdorff. -/
instance rationalFiniteAdeleT2Space : T2Space (FiniteAdeleRing ℤ ℚ) := by
  letI (v : HeightOneSpectrum ℤ) : T2Space (v.adicCompletion ℚ) := by
    unfold HeightOneSpectrum.adicCompletion
    infer_instance
  exact T2Space.of_injective_continuous
    (show Function.Injective (fun x : FiniteAdeleRing ℤ ℚ => fun v : HeightOneSpectrum ℤ => x v)
      from DFunLike.coe_injective) RestrictedProduct.continuous_coe

/-- The genuine compact open integral subring makes the actual finite adele ring locally compact. -/
instance rationalFiniteAdeleLocallyCompactSpace : LocallyCompactSpace (FiniteAdeleRing ℤ ℚ) :=
  finiteAdeleIntegerSubring_isCompact.locallyCompactSpace_of_mem_nhds_of_addGroup
    (finiteAdeleIntegerSubring_isOpen.mem_nhds finiteAdeleIntegerSubring.zero_mem)

/-- Each actual principal level ideal is compact in the canonical finite adele ring, including zero level. -/
theorem finiteAdeleLevelMultiple_isCompact (N : ℕ) :
    IsCompact {x : FiniteAdeleRing ℤ ℚ | finiteAdeleLevelMultiple N x} := by
  have he : {x : FiniteAdeleRing ℤ ℚ | finiteAdeleLevelMultiple N x} =
      (fun y : FiniteAdeleRing ℤ ℚ => (N : FiniteAdeleRing ℤ ℚ) * y) '' finiteAdeleIntegerSubring := by
    ext x
    simp only [finiteAdeleLevelMultiple, mem_setOf_eq, mem_image]
    constructor
    · rintro ⟨y, hy, h⟩
      exact ⟨y, hy, h.symm⟩
    · rintro ⟨y, hy, h⟩
      exact ⟨y, hy, h.symm⟩
  rw [he]
  exact finiteAdeleIntegerSubring_isCompact.image (continuous_const.mul continuous_id)

/-- The actual original integral level matrix order is a genuine multiplicative submonoid. -/
def finiteAdeleLevelMatrixSubmonoid (N : ℕ) :
    Submonoid (Matrix (Fin 2) (Fin 2) (FiniteAdeleRing ℤ ℚ)) where
  carrier := {g | finiteAdeleLevelMatrix N g}
  one_mem' := finiteAdeleLevelMatrix_one N
  mul_mem' := finiteAdeleLevelMatrix_mul N

/-- All original integral level matrices form a compact set in the actual finite adelic matrix space. -/
theorem finiteAdeleLevelMatrix_isCompact (N : ℕ) :
    IsCompact {g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing ℤ ℚ) | finiteAdeleLevelMatrix N g} := by
  have hi : IsCompact {g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing ℤ ℚ) |
      ∀ i j, g i j ∈ finiteAdeleIntegerSubring} := by
    convert isCompact_univ_pi (fun _ : Fin 2 =>
      isCompact_univ_pi (fun _ : Fin 2 => finiteAdeleIntegerSubring_isCompact)) using 1
    ext g
    change (∀ i j : Fin 2, g i j ∈ finiteAdeleIntegerSubring) ↔
      ∀ i ∈ (univ : Set (Fin 2)), ∀ j ∈ (univ : Set (Fin 2)), g i j ∈ finiteAdeleIntegerSubring
    simp only [mem_univ, forall_const]
  have hc : Continuous (fun g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing ℤ ℚ) => g 1 0) :=
    (_root_.continuous_apply 0).comp (_root_.continuous_apply 1)
  exact hi.inter_right ((finiteAdeleLevelMultiple_isCompact N).isClosed.preimage hc)

/-- The original finite adelic general-linear level subgroup is genuinely compact. -/
theorem finiteAdeleGL2Gamma0_isCompact (N : ℕ) :
    IsCompact (finiteAdeleGL2Gamma0 N : Set (GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ))) := by
  exact Submonoid.units_isCompact (S := finiteAdeleLevelMatrixSubmonoid N)
    (finiteAdeleLevelMatrix_isCompact N)

/-- The original finite adelic general-linear group has its actual locally compact topology. -/
instance rationalFiniteAdelicGL2LocallyCompactSpace :
    LocallyCompactSpace (GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) :=
  (finiteAdeleGL2Gamma0_isCompact 1).locallyCompactSpace_of_mem_nhds_of_group
    ((finiteAdeleGL2Gamma0_isOpen 1).mem_nhds (finiteAdeleGL2Gamma0 1).one_mem)

/-- The genuine nonzero finite adelic level group is both compact and open. -/
theorem finiteAdeleGL2Gamma0_compact_open (N : ℕ) [NeZero N] :
    IsCompact (finiteAdeleGL2Gamma0 N : Set (GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ))) ∧
      IsOpen (finiteAdeleGL2Gamma0 N : Set (GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ))) :=
  ⟨finiteAdeleGL2Gamma0_isCompact N, finiteAdeleGL2Gamma0_isOpen N⟩

end
end Dubon2026
