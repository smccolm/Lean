import Dubon2026.AdelicSignedFiniteIsometry

/-! # Equivariance of the original finite cyclic isometries at all signed real weights -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- The actual finite action multiplies the genuine finite orbit coordinates of a signed raising vector. -/
theorem adelicSignedFiniteOrbit_action (i : ℕ ⊕ ℕ)
    (a b : GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) :
    adelicCyclicHilbertRepresentation f (rationalAdelicFiniteGL2Embedding a) (adelicSignedFiniteOrbit f i b) =
      adelicSignedFiniteOrbit f i (a * b) :=
  (@representation_hom_mul_apply
    (GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) RationalAdelicGL2 (AdelicCyclicHilbert f)
    inferInstance inferInstance inferInstance inferInstance (adelicCyclicHilbertRepresentation f)
    rationalAdelicFiniteGL2Embedding a b (adelicNormalizedSignedRaisingJet f i)).symm

/-- The genuine signed finite-core isometry intertwines the actual original finite representations. -/
theorem adelicSignedFiniteCoreIsometry_intertwines (hf : f ≠ 0) (hk : 0 < k) (i : ℕ ⊕ ℕ)
    (a : GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) (x : adelicFullFiniteUnitCore f) :
    adelicSignedFiniteCoreIsometry f hf hk i (adelicFullFiniteUnitCoreRepresentation f a x) =
      adelicCyclicHilbertRepresentation f (rationalAdelicFiniteGL2Embedding a)
        (adelicSignedFiniteCoreIsometry f hf hk i x) :=
  @linearMap_intertwines_of_spanning_family
    (GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) (adelicFullFiniteUnitCore f) (AdelicCyclicHilbert f)
    inferInstance inferInstance inferInstance inferInstance inferInstance
    (adelicFullFiniteUnitCoreRepresentation f)
    ((adelicCyclicHilbertRepresentation f).comp rationalAdelicFiniteGL2Embedding)
    (adelicSignedFiniteCoreIsometry f hf hk i).toLinearMap
    (adelicFullFiniteUnitOrbit f) (adelicSignedFiniteOrbit f i) (adelicFullFiniteUnitOrbit_span f)
    (adelicSignedFiniteCoreIsometry_family f hf hk i) (adelicFullFiniteUnitOrbit_action f)
    (adelicSignedFiniteOrbit_action f i) a x

end
end Dubon2026
