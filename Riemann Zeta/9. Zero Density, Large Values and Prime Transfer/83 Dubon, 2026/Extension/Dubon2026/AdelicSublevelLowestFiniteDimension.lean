import Dubon2026.AdelicSublevelFiniteDimension
import Dubon2026.AdelicSublevelProjection
import Dubon2026.ProjectionCoreDensity

/-! # Actual sublevel fixed vectors in the original lowest-weight Hilbert space are finite dimensional -/

namespace Dubon2026

noncomputable section
open Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- Actual compact projection of the original finite-adelic core proves density at every genuine open sublevel. -/
theorem adelicSublevelFixedLowest_algebraic_density (hf : f ≠ 0) (hk : 0 < k)
    (L : Subgroup (finiteAdeleGL2Gamma0 N)) (hL : IsOpen (L : Set (finiteAdeleGL2Gamma0 N))) :
    (adelicFiniteCyclicSpan f ⊓ adelicSublevelFixedSpace f L).topologicalClosure =
      adelicRotationWeightSpace f ⊓ adelicSublevelFixedSpace f L := by
  have he := @projection_stable_core_closure (AdelicCyclicHilbert f) inferInstance inferInstance
    (adelicFiniteCyclicSpan f) (adelicSublevelFixedSpace f L) inferInstance
    (adelicSublevelFixedSpace_isClosed f L) (adelicSublevelProjection_finiteSpan f L hL)
  rw [adelicFiniteCyclicSpan_closure, ← adelicRotationWeightSpace_eq_finiteClosure f hf hk] at he
  exact he

/-- Every original lowest-weight Hilbert vector fixed by a genuine open sublevel belongs to the original algebraic finite-adelic core. -/
theorem adelicSublevelFixedLowest_eq_algebraic (hf : f ≠ 0) (hk : 0 < k)
    (L : Subgroup (finiteAdeleGL2Gamma0 N)) (hL : IsOpen (L : Set (finiteAdeleGL2Gamma0 N))) :
    adelicRotationWeightSpace f ⊓ adelicSublevelFixedSpace f L =
      adelicFiniteCyclicSpan f ⊓ adelicSublevelFixedSpace f L := by
  letI : CompactSpace (finiteAdeleGL2Gamma0 N) :=
    isCompact_iff_compactSpace.mp (finiteAdeleGL2Gamma0_isCompact N)
  letI : Finite ((finiteAdeleGL2Gamma0 N) ⧸ L) := L.quotient_finite_of_isOpen hL
  letI : L.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  rw [← adelicSublevelFixedLowest_algebraic_density f hf hk L hL]
  exact (Submodule.closed_of_finiteDimensional _).submodule_topologicalClosure_eq

/-- Genuine classical cusp-space finiteness, faithful finite-coset reconstruction and original Hilbert density prove finite dimensionality of the entire actual lowest-weight sublevel fixed space. -/
theorem adelicSublevelFixedLowest_finiteDimensional (hf : f ≠ 0) (hk : 0 < k)
    (L : Subgroup (finiteAdeleGL2Gamma0 N)) (hL : IsOpen (L : Set (finiteAdeleGL2Gamma0 N))) :
    FiniteDimensional ℂ ↥(adelicRotationWeightSpace f ⊓ adelicSublevelFixedSpace f L :
      Submodule ℂ (AdelicCyclicHilbert f)) := by
  letI : CompactSpace (finiteAdeleGL2Gamma0 N) :=
    isCompact_iff_compactSpace.mp (finiteAdeleGL2Gamma0_isCompact N)
  letI : Finite ((finiteAdeleGL2Gamma0 N) ⧸ L) := L.quotient_finite_of_isOpen hL
  letI : L.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  rw [adelicSublevelFixedLowest_eq_algebraic f hf hk L hL]
  infer_instance

end
end Dubon2026
