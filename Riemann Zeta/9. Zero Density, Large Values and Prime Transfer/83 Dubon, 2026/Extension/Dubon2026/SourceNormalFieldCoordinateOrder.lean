import Dubon2026.SourceNormalCoordinateEmbeddingRange
import Dubon2026.SourceKernelOrbitDivisibility
import Dubon2026.SourceRationalEmbeddingFiberOrder
import Dubon2026.SourceRationalCoordinateFiberSurjectivity

/-! The actual normalized order in the normal intermediate field divides
the finite inertia quotient order. Existing place-fiber and inertia-orbit
identities supply the geometric comparison. This is the exact bridge to
the DUB-17/18 characteristic-three order-dividing-six auxiliary field. -/
namespace Dubon2026.SourceCurve.Place
noncomputable section
variable {K M : Type*} [Field K] [IsAlgClosed K] [Field M]
variable [Algebra K M] [Algebra (RatFunc K) M] [IsScalarTower K (RatFunc K) M]
variable [FiniteDimensional (RatFunc K) M] [IsGalois (RatFunc K) M]

theorem normal_coordinate_order_dvd_of_inertia_kernel
    (L : IntermediateField (RatFunc K) M) [Normal (RatFunc K) L]
    (w : Place K M) (hw : 0 < w.ord (algebraMap (RatFunc K) M RatFunc.X))
    {P : Type*} [Group P]
    (π : w.toValuationSubring.inertiaSubgroup (RatFunc K) →* P)
    (hfix : ∀ σ, π σ = 1 → ∀ a : L, σ.val.val (a : M) = a)
    (v : Place K L) (hv : 0 < v.ord (algebraMap (RatFunc K) L RatFunc.X)) :
    v.ord (algebraMap (RatFunc K) L RatFunc.X) ∣ (Nat.card P : ℤ) := by
  let x := algebraMap (RatFunc K) L RatFunc.X
  have hx : Transcendental K x := rationalCoordinate_transcendental K
  let ι : L →ₐ[K] M := L.val.restrictScalars K
  have hι : ι x = algebraMap (RatFunc K) M RatFunc.X := rfl
  have hw' : 0 < w.ord (algebraMap (RatFunc K) M RatFunc.X - algebraMap K M 0) := by
    simpa only [map_zero, sub_zero] using hw
  have hv' : 0 < v.ord (x - algebraMap K L 0) := by
    simpa only [map_zero, sub_zero] using hv
  obtain ⟨ψ, hψ, hres⟩ := exists_coordinate_embedding_restrict_eq x hx ι hι w 0 hw' v hv'
  let Ψ : {ψ : L →ₐ[K] M // ψ x = algebraMap (RatFunc K) M RatFunc.X} := ⟨ψ, hψ⟩
  letI := coordinateEmbeddingAction (K := K) (M := M) x
  have hker (σ : w.toValuationSubring.inertiaSubgroup (RatFunc K))
      (hσ : π σ = 1) : σ • Ψ = Ψ := by
    apply Subtype.ext
    apply AlgHom.ext
    intro a
    change σ.val.val (ψ a) = ψ a
    exact hfix σ hσ ⟨ψ a, normal_coordinate_embedding_mem L ψ hψ a⟩
  have hd := orbit_card_dvd_of_kernel_fixes π Ψ hker
  have ho := restricted_coordinate_order_eq_embedding_fiber_card x hx w 0 hw' Ψ
  simp only [map_zero, sub_zero] at ho
  change v.ord x ∣ (Nat.card P : ℤ)
  rw [← hres, ho]
  rw [← coordinateEmbedding_restriction_fiber_eq_orbit x hx w Ψ] at hd
  exact_mod_cast hd

end
end Dubon2026.SourceCurve.Place
