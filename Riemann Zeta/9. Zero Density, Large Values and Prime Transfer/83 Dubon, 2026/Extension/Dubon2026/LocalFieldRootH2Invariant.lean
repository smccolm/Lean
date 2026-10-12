import Dubon2026.ContinuousKummerH2Torsion
import Dubon2026.LocalFieldContinuousH2Invariant
import Dubon2026.RationalCyclicInvariant

/-! # The original local invariant on actual root-of-unity cohomology

This supplies the finite scalar target required for the local arithmetic cup.
It reuses the original Kummer inclusion and the proved full local invariant.
Perfectness of the degree-one pairing is a separate obligation.
-/

namespace Dubon2026
noncomputable section

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]
  [IsGalois K Ω] [IsAlgClosed Ω]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (n : ℕ) [NeZero n]
  [TopologicalSpace (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)]
  [DiscreteTopology (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

/-- The invariant of an actual root-of-unity class is the full local invariant
of its original coefficient inclusion into unit cohomology. -/
def localFieldRootH2Invariant :
    GaloisRootContinuousH2 (K := K) (Ω := Ω) n →ₗ[ℤ] AddCircle (1 : ℚ) :=
  (localFieldContinuousH2InvariantEquiv K Ω).toLinearMap.comp
    (galoisKummerH2Inclusion (K := K) (Ω := Ω) n)

/-- Hilbert 90, through the original Kummer exact sequence, makes the actual
root-of-unity invariant injective. -/
theorem localFieldRootH2Invariant_injective :
    Function.Injective (localFieldRootH2Invariant K Ω n) :=
  (localFieldContinuousH2InvariantEquiv K Ω).injective.comp
    (galoisKummerH2Inclusion_injective (K := K) (Ω := Ω) n (NeZero.pos n))

/-- The actual finite-coefficient invariant has exactly the n-torsion image
in the rational circle; neither direction assumes a cardinality formula. -/
theorem localFieldRootH2Invariant_mem_range_iff (q : AddCircle (1 : ℚ)) :
    q ∈ (localFieldRootH2Invariant K Ω n).range ↔ n • q = 0 := by
  let e := localFieldContinuousH2InvariantEquiv K Ω
  constructor
  · rintro ⟨x, rfl⟩
    have hx := (galoisKummerH2_mem_range_iff_nsmul_zero
      (K := K) (Ω := Ω) n (NeZero.pos n)
      (galoisKummerH2Inclusion (K := K) (Ω := Ω) n x)).mp ⟨x, rfl⟩
    change n • e (galoisKummerH2Inclusion (K := K) (Ω := Ω) n x) = 0
    rw [← map_nsmul, hx, e.map_zero]
  · intro hq
    have hx : n • e.symm q = 0 := by
      apply e.injective
      rw [map_nsmul, e.apply_symm_apply, hq, e.map_zero]
    obtain ⟨x, hx⟩ := (galoisKummerH2_mem_range_iff_nsmul_zero
      (K := K) (Ω := Ω) n (NeZero.pos n) (e.symm q)).mpr hx
    refine ⟨x, ?_⟩
    change e (galoisKummerH2Inclusion (K := K) (Ω := Ω) n x) = q
    rw [hx, e.apply_symm_apply]

/-- The original root invariant and the literal rational cyclic invariant
have the same image. -/
theorem localFieldRootH2Invariant_range :
    (localFieldRootH2Invariant K Ω n).range =
      (rationalCyclicInvariant n).toIntLinearMap.range := by
  ext q
  exact (localFieldRootH2Invariant_mem_range_iff K Ω n q).trans
    (rationalCyclicInvariant_mem_range_iff n q).symm

/-- The actual original continuous H2 with root-of-unity coefficients is
canonically cyclic of order n, normalized by the full local invariant. -/
def localFieldRootH2CyclicEquiv :
    GaloisRootContinuousH2 (K := K) (Ω := Ω) n ≃ₗ[ℤ] ZMod n :=
  ((LinearEquiv.ofInjective (localFieldRootH2Invariant K Ω n)
    (localFieldRootH2Invariant_injective K Ω n)).trans
      (LinearEquiv.ofEq _ _ (localFieldRootH2Invariant_range K Ω n))).trans
        (LinearEquiv.ofInjective (rationalCyclicInvariant n).toIntLinearMap
          (rationalCyclicInvariant_injective n)).symm

/-- The cyclic coordinate retains the actual Kummer inclusion and full
local invariant, rather than merely choosing an abstract finite-group isomorphism. -/
theorem localFieldRootH2CyclicEquiv_invariant
    (x : GaloisRootContinuousH2 (K := K) (Ω := Ω) n) :
    rationalCyclicInvariant n (localFieldRootH2CyclicEquiv K Ω n x) =
      localFieldContinuousH2InvariantEquiv K Ω
        (galoisKummerH2Inclusion (K := K) (Ω := Ω) n x) := by
  exact LinearEquiv.ofInjective_symm_apply
    (rationalCyclicInvariant n).toIntLinearMap
    (h := rationalCyclicInvariant_injective n) _

/-- The exact order of the actual original root-of-unity H2 follows from
the invariant equivalence and the proved Kummer image. -/
theorem localFieldRootH2_card :
    Nat.card (GaloisRootContinuousH2 (K := K) (Ω := Ω) n) = n := by
  rw [Nat.card_congr (localFieldRootH2CyclicEquiv K Ω n).toEquiv,
    Nat.card_eq_fintype_card, ZMod.card]

end
end Dubon2026
