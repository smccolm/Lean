import Dubon2026.SourcePrimeHeckeNaturality

/-! Exact native coboundary primitives for the original full Hecke correspondence.
DUB-17/18 -> residual modular Galois association -> character-to-weight-two
reduction -> the Eisenstein eigenvalue of a class killed by coefficient
inclusion -> this exact original degree-zero trace. The existing native
coset-trace coboundary identity supplies the proof.
-/

namespace Dubon2026
noncomputable section

variable {R G : Type} [CommRing R] [Group G] (A : Rep R G)
    (S : Subgroup G) [Fintype (G ⧸ S)] (θ : S →* G) (b : Module.End R A)
    (hb : ∀ u : S, b.comp (A.ρ (θ u)) = (A.ρ u.val).comp b)

include hb in
/-- The full original correspondence sends a native coboundary to the
coboundary of its literal degree-zero trace, with its primitive retained. -/
theorem sourceCorrespondenceOne_d01 (v : A) :
    sourceCorrespondenceOne A S θ b (groupCohomology.d₀₁ A v) =
      groupCohomology.d₀₁ A (cosetTraceZero A S (b v)) := by
  have he : sourceCorrespondencePull A S θ b (groupCohomology.d₀₁ A v) =
      groupCohomology.d₀₁ (restrictedCoefficientRep A S.subtype) (b v) := by
    funext u
    change b (A.ρ (θ u) v - v) = A.ρ u.val (b v) - b v
    rw [map_sub, show b (A.ρ (θ u) v) = A.ρ u.val (b v) from
      LinearMap.congr_fun (hb u) v]
  change cosetTraceOne A S (sourceCorrespondencePull A S θ b _) = _
  rw [he, cosetTraceOne_coboundary]

end
end Dubon2026
