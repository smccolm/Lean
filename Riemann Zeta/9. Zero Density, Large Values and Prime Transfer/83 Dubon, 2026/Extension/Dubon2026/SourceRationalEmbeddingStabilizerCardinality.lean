import Dubon2026.SourceRationalEmbeddingStabilizer
import Dubon2026.SourceRatFuncInertiaCardinality

/-! DUB-17/18 -> reverse genus -> normalized embedding-fiber counts.
The actual embedding stabilizer has cardinality equal to the normalized
order of the mapped lower uniformizer. Rational residues and the finite
Galois extension over the embedded field are derived from the original
rational-coordinate extension. -/
namespace Dubon2026.SourceCurve.Place
noncomputable section
variable {K F M : Type*} [Field K] [IsAlgClosed K] [Field F] [Field M]
variable [Algebra K F] [Algebra K M]
variable [Algebra (RatFunc K) M] [IsScalarTower K (RatFunc K) M]
variable [FiniteDimensional (RatFunc K) M] [IsGalois (RatFunc K) M]

theorem coordinateEmbedding_stabilizer_card (x : F) (hx : Transcendental K x)
    (w : Place K M)
    (ψ : {ψ : F →ₐ[K] M // ψ x = algebraMap (RatFunc K) M RatFunc.X}) :
    letI := coordinateEmbeddingAction (K := K) (M := M) x
    Nat.card (MulAction.stabilizer (w.toValuationSubring.inertiaSubgroup (RatFunc K)) ψ) =
      (w.ord (ψ.val (restrictAlongFinite ψ.val
        (finite_galois_along_coordinate x hx ψ.val ψ.property).1 w).uniformizer)).toNat := by
  letI := coordinateEmbeddingAction (K := K) (M := M) x
  letI := algebraAlong ψ.val
  haveI := scalarTower_along ψ.val
  haveI := (finite_galois_along_coordinate x hx ψ.val ψ.property).1
  haveI := (finite_galois_along_coordinate x hx ψ.val ψ.property).2
  haveI := (finite_galois_coordinateField K (M := M)).1
  have hr (u : Place K M) : Function.Bijective (algebraMap K u.ResidueField) :=
    place_residue_bijective_of_finite_coordinate (algebraMap (RatFunc K) M RatFunc.X) u
  rw [Nat.card_congr (coordinateEmbeddingStabilizerEquiv x hx w ψ)]
  exact decomposition_card_eq_uniformizer_order w
    ((w.restrict F).residue_bijective_of_all_upper hr) (hr w)

theorem coordinateEmbedding_restriction_fiber_eq_orbit
    (x : F) (hx : Transcendental K x) (w : Place K M)
    (ψ : {ψ : F →ₐ[K] M // ψ x = algebraMap (RatFunc K) M RatFunc.X}) :
    letI := coordinateEmbeddingAction (K := K) (M := M) x
    {ψ' : {ψ : F →ₐ[K] M // ψ x = algebraMap (RatFunc K) M RatFunc.X} |
      restrictAlongFinite ψ'.val (finite_galois_along_coordinate x hx ψ'.val ψ'.property).1 w =
        restrictAlongFinite ψ.val (finite_galois_along_coordinate x hx ψ.val ψ.property).1 w} =
      MulAction.orbit (w.toValuationSubring.inertiaSubgroup (RatFunc K)) ψ := by
  letI := coordinateEmbeddingAction (K := K) (M := M) x
  ext ψ'
  rw [Set.mem_setOf_eq,
    restrictAlongFinite_eq_iff_inertia x hx ψ.val ψ'.val ψ.property ψ'.property w,
    MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨σ, hσ⟩
    exact ⟨σ, Subtype.ext hσ.symm⟩
  · rintro ⟨σ, hσ⟩
    exact ⟨σ, (congrArg Subtype.val hσ).symm⟩

end
end Dubon2026.SourceCurve.Place
