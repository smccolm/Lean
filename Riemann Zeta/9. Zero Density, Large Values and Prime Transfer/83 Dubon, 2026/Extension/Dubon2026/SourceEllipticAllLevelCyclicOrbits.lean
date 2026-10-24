import Dubon2026.SourceEllipticAllLevelCyclicRootBijection
import Dubon2026.SourceEllipticAllLevelCyclicEquivariance

/-! At every invertible level and transcendental j, the orbit relation on
the original cyclic subgroups equals the orbit relation on their exact
modular roots. The actual all-level bijection and quotient equivariance
discharge injectivity and compatibility. This applies to every subgroup of
base-field automorphisms, including inertia. Specialization to the residue
curve and the numerical ramification census remain DUB-17/18 obligations. -/

namespace Dubon2026.SourceEllipticVelu
open WeierstrassCurve SourceFunctionField.IntegralJCoordinate
noncomputable section

/-- The actual all-level cyclic-subgroup and modular-root orbit relations agree for every subgroup of base-field automorphisms. -/
theorem cyclicQuotientJ_galois_orbit_iff
    {K F L : Type*} [Field K] [IsAlgClosed K] [Field F] [Field L]
    [DecidableEq L] [IsAlgClosed L] [Algebra K L] [Algebra F L]
    (W : WeierstrassCurve F) [W.IsElliptic]
    (hj : Transcendental K (W.baseChange L).j)
    (N : ℕ) [NeZero N] (hNK : (N : K) ≠ 0)
    (G : Subgroup (L ≃ₐ[F] L))
    (H₁ H₂ : {H : AddSubgroup (W.baseChange L).toAffine.Point //
      IsAddCyclic H ∧ Nat.card H = N}) :
    let hNL : (N : L) ≠ 0 := by simpa only [map_natCast] using (_root_.map_ne_zero (algebraMap K L)).mpr hNK
    (∃ σ ∈ G, fixedCurveCyclicKernelMap σ.toRingHom (W.baseChange L)
      (W.map_baseChange σ.toAlgHom) N H₂ = H₁) ↔
    (∃ σ ∈ G, σ (cyclicQuotientJ (W.baseChange L) N hNL H₂) =
      cyclicQuotientJ (W.baseChange L) N hNL H₁) := by
  intro hNL
  have hi := (cyclicQuotientJ_bijOn_transcendental (K := K) N hNK (W.baseChange L) hj).injOn
  constructor
  · rintro ⟨σ, hσ, h⟩
    refine ⟨σ, hσ, ?_⟩
    rw [← cyclicQuotientJ_galois W σ N hNL H₂, h]
  · rintro ⟨σ, hσ, h⟩
    refine ⟨σ, hσ, hi (Set.mem_univ _) (Set.mem_univ _) ?_⟩
    exact (cyclicQuotientJ_galois W σ N hNL H₂).trans h

end
end Dubon2026.SourceEllipticVelu
