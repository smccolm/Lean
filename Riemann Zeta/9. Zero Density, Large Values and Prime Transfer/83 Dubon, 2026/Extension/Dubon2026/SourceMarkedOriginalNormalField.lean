import Dubon2026.SourceMarkedOriginalOfJChart
import Dubon2026.SourceMarkedFullTorsionNonempty
import Dubon2026.SourceMarkedEmbeddingSignKernel
import Dubon2026.SourceCoordinateEmbeddingFixedFieldMap

/-! DUB-17/18 -> reverse original genus -> wild differential bounds.
The actual original Gamma1 coordinate-embedding kernel defines a finite
Galois field containing the original field. A native inertia sign kernel
fixes this entire auxiliary field. Thus the existing characteristic-two
and characteristic-three quotient actions can bound its local j orders;
no new normal-closure or Galois-descent infrastructure is required. -/
namespace Dubon2026.SourceFunctionField.MarkedChart
noncomputable section
open WeierstrassCurve CongruenceSubgroup SourceCurve SourceEllipticReduction
open GammaOne GammaOne.ToricCoordinates IntegralDiamond
local notation "Qbar" => AlgebraicClosure ℚ
variable (A : ValuationSubring Qbar) (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime]
    [CharP (IsLocalRing.ResidueField A) ℓ]
local notation "kk" => IsLocalRing.ResidueField A
local notation "F" => qExpFunctionFieldC kk (Gamma1 N)
private local instance : Algebra kk F := (F).toSubalgebra.algebra

theorem exists_original_normal_field_of_torsion_sign_kernel
    (hℓN : ¬ ℓ ∣ N) (hN : 2 ≤ N) [DecidableEq (RatFunc kk)]
    (x : F) (hx : (x : LaurentSeries kk) = jqModC kk)
    (M : Type*) [Field M] [DecidableEq M] [Algebra kk M] [Algebra (RatFunc kk) M]
    [IsScalarTower kk (RatFunc kk) M] [FiniteDimensional (RatFunc kk) M] [IsGalois (RatFunc kk) M]
    (hfull : Nat.card {P : ((ofJ (RatFunc.X : RatFunc kk)).baseChange M).toAffine.Point //
      N • P = 0} = N ^ 2)
    (w : ValuationSubring M) {G : Type*} [Group G] (π : w.inertiaSubgroup (RatFunc kk) →* G)
    (hker : ∀ σ, π σ = 1 →
      (∀ P, galoisTorsionMap (ofJ (RatFunc.X : RatFunc kk)) N σ.val.val P = P) ∨
      (∀ P, galoisTorsionMap (ofJ (RatFunc.X : RatFunc kk)) N σ.val.val P = -P)) :
    ∃ L : IntermediateField (RatFunc kk) M,
      letI : Algebra kk L := IntermediateField.algebra' L
      FiniteDimensional (RatFunc kk) L ∧ IsGalois (RatFunc kk) L ∧
      ∃ ι : F →ₐ[kk] L, ι x = algebraMap (RatFunc kk) L RatFunc.X ∧
        ∀ σ, π σ = 1 → ∀ a : L, σ.val.val (a : M) = a := by
  classical
  let E := ofJ (RatFunc.X : RatFunc kk)
  obtain ⟨Φ, hnat, _, hneg, _, hsurj⟩ :=
    exists_original_ofJ_full_torsion_chart A N ℓ hℓN hN x hx M hfull
  have hNK : (N : kk) ≠ 0 := fun h => hℓN ((CharP.cast_eq_zero_iff kk ℓ N).mp h)
  have hNM : (N : M) ≠ 0 := by
    simpa only [map_natCast] using (map_ne_zero (algebraMap kk M)).mpr hNK
  obtain ⟨P, hP⟩ := exists_exactOrder_point_of_full_torsion (E.baseChange M) N hNM hfull
  let ψ := Φ ⟨P, hP⟩
  let L := coordinateEmbeddingFixingField (K := kk) (M := M) x
  letI : Algebra kk L := IntermediateField.algebra' L
  let ι := coordinateEmbeddingIntoFixingField x ψ.val ψ.property
  refine ⟨L, inferInstance, coordinateEmbedding_fixingField_isGalois x, ι,
    coordinateEmbeddingIntoFixingField_coordinate x ψ.val ψ.property, ?_⟩
  intro σ hσ a
  apply coordinateEmbedding_fixingField_fixed x σ.val.val _ a
  intro φ hφ
  exact normalized_embeddings_fixed_of_torsion_sign E N x
    (algebraMap (RatFunc kk) M RatFunc.X) Φ hsurj hnat hneg σ.val.val (hker σ hσ) φ hφ

end
end Dubon2026.SourceFunctionField.MarkedChart
