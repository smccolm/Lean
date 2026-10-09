import Dubon2026.AdelicSublevelLowestFiniteDimension

/-! # Genuine finite-open fixed vectors in the original global lowest-weight Hilbert space -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- Restrict the actual full adelic action to a genuine subgroup of the entire original finite adelic group. -/
def adelicFiniteSubgroupRepresentation (J : Subgroup (GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ))) :
    Representation ℂ J (AdelicCyclicHilbert f) :=
  (adelicCyclicHilbertRepresentation f).comp (rationalAdelicFiniteGL2Embedding.comp J.subtype)

/-- Actual Hilbert vectors fixed by the given genuine finite adelic subgroup. -/
def adelicFiniteSubgroupFixedSpace (J : Subgroup (GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ))) :
    Submodule ℂ (AdelicCyclicHilbert f) := Representation.invariants (adelicFiniteSubgroupRepresentation f J)

/-- The actual finite-subgroup fixed space consists exactly of the literal original fixed vectors. -/
theorem mem_adelicFiniteSubgroupFixedSpace (J : Subgroup (GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)))
    (x : AdelicCyclicHilbert f) : x ∈ adelicFiniteSubgroupFixedSpace f J ↔
      ∀ a : J, adelicCyclicHilbertRepresentation f (rationalAdelicFiniteGL2Embedding a.val) x = x := Iff.rfl

/-- The genuine fixed equations define a closed subspace in the original global Hilbert topology. -/
theorem adelicFiniteSubgroupFixedSpace_isClosed (J : Subgroup (GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ))) :
    IsClosed (adelicFiniteSubgroupFixedSpace f J : Set (AdelicCyclicHilbert f)) :=
  @representation_invariants_isClosed J (AdelicCyclicHilbert f)
    inferInstance inferInstance inferInstance (adelicFiniteSubgroupRepresentation f J)
    (fun a => adelicCyclicHilbertOperator f (rationalAdelicFiniteGL2Embedding a.val)) (fun _ _ => rfl)

/-- Original vectors fixed by any finite adelic subgroup remain fixed by its actual intersection with the original level. -/
theorem adelicFiniteSubgroupFixedSpace_le_sublevel
    (J : Subgroup (GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ))) :
    adelicFiniteSubgroupFixedSpace f J ≤ adelicSublevelFixedSpace f (J.comap (finiteAdeleGL2Gamma0 N).subtype) := by
  intro x hx
  apply (mem_adelicSublevelFixedSpace f _ x).mpr
  intro a
  exact (mem_adelicFiniteSubgroupFixedSpace f J x).mp hx ⟨a.val.val, a.property⟩

/-- Every genuine open finite adelic subgroup has a finite-dimensional fixed part in the entire original lowest-weight Hilbert space. -/
theorem adelicFiniteOpenLowest_finiteDimensional (hf : f ≠ 0) (hk : 0 < k)
    (J : Subgroup (GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)))
    (hJ : IsOpen (J : Set (GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)))) :
    FiniteDimensional ℂ ↥(adelicRotationWeightSpace f ⊓ adelicFiniteSubgroupFixedSpace f J :
      Submodule ℂ (AdelicCyclicHilbert f)) := by
  let L := J.comap (finiteAdeleGL2Gamma0 N).subtype
  have hL : IsOpen (L : Set (finiteAdeleGL2Gamma0 N)) := hJ.preimage continuous_subtype_val
  letI := adelicSublevelFixedLowest_finiteDimensional f hf hk L hL
  have h : adelicRotationWeightSpace f ⊓ adelicFiniteSubgroupFixedSpace f J ≤
      adelicRotationWeightSpace f ⊓ adelicSublevelFixedSpace f L :=
    inf_le_inf_left _ (adelicFiniteSubgroupFixedSpace_le_sublevel f J)
  exact FiniteDimensional.of_injective (Submodule.inclusion h) (Submodule.inclusion_injective h)

end
end Dubon2026
