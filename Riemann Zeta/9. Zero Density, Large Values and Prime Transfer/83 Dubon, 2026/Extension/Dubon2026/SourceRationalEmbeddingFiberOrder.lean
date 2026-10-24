import Dubon2026.SourceRationalEmbeddingStabilizerCardinality

/-! DUB-17/18 -> reverse genus -> normalized exceptional-fiber counts.
The order at the restricted place equals the number of embeddings giving
that place. Orbit-stabilizer uses the actual inertia group and the proved
upper decomposition group; normalized restriction orders cancel their
common positive ramification factor. -/
namespace Dubon2026.SourceCurve.Place
noncomputable section
variable {K F M : Type*} [Field K] [IsAlgClosed K] [Field F] [Field M]
variable [Algebra K F] [Algebra K M]
variable [Algebra (RatFunc K) M] [IsScalarTower K (RatFunc K) M]
variable [FiniteDimensional (RatFunc K) M] [IsGalois (RatFunc K) M]

theorem restricted_coordinate_order_eq_embedding_fiber_card
    (x : F) (hx : Transcendental K x) (w : Place K M) (a : K)
    (hw : 0 < w.ord (algebraMap (RatFunc K) M RatFunc.X - algebraMap K M a))
    (ψ : {ψ : F →ₐ[K] M // ψ x = algebraMap (RatFunc K) M RatFunc.X}) :
    (restrictAlongFinite ψ.val (finite_galois_along_coordinate x hx ψ.val ψ.property).1 w).ord
      (x - algebraMap K F a) =
      Nat.card {ψ' : {ψ : F →ₐ[K] M // ψ x = algebraMap (RatFunc K) M RatFunc.X} //
        restrictAlongFinite ψ'.val (finite_galois_along_coordinate x hx ψ'.val ψ'.property).1 w =
          restrictAlongFinite ψ.val (finite_galois_along_coordinate x hx ψ.val ψ.property).1 w} := by
  letI := coordinateEmbeddingAction (K := K) (M := M) x
  let I := w.toValuationSubring.inertiaSubgroup (RatFunc K)
  let hfin := (finite_galois_along_coordinate x hx ψ.val ψ.property).1
  let v := restrictAlongFinite ψ.val hfin w
  let r := w.ord (ψ.val v.uniformizer)
  let Fiber := {ψ' : {ψ : F →ₐ[K] M // ψ x = algebraMap (RatFunc K) M RatFunc.X} //
    restrictAlongFinite ψ'.val (finite_galois_along_coordinate x hx ψ'.val ψ'.property).1 w = v}
  have hprod := (MulAction.stabilizer I ψ).card_mul_index
  have horbit : (MulAction.orbit I ψ).ncard = Nat.card Fiber := by
    rw [← coordinateEmbedding_restriction_fiber_eq_orbit x hx w ψ,
      ← Nat.card_coe_set_eq]
    rfl
  rw [MulAction.index_stabilizer, horbit,
    coordinateEmbedding_stabilizer_card x hx w ψ,
    inertia_card_eq_rational_specialization_order K w a hw] at hprod
  have hr : 0 < r := ord_restrictAlongFinite_uniformizer_pos ψ.val hfin w
  have hcast : r * (Nat.card Fiber : ℤ) =
      w.ord (algebraMap (RatFunc K) M RatFunc.X - algebraMap K M a) := by
    change r.toNat * Nat.card Fiber =
      (w.ord (algebraMap (RatFunc K) M RatFunc.X - algebraMap K M a)).toNat at hprod
    have h := congrArg (fun n : ℕ => (n : ℤ)) hprod
    simpa only [Nat.cast_mul, Int.toNat_of_nonneg hr.le, Int.toNat_of_nonneg hw.le] using h
  have ho := ord_restrictAlongFinite ψ.val hfin w (x - algebraMap K F a)
  rw [map_sub, ψ.property, ψ.val.commutes] at ho
  change _ = v.ord (x - algebraMap K F a) * r at ho
  change v.ord (x - algebraMap K F a) = (Nat.card Fiber : ℤ)
  apply mul_left_cancel₀ hr.ne'
  rw [mul_comm r, ← ho, hcast]

end
end Dubon2026.SourceCurve.Place
