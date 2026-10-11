import Dubon2026.FiniteFreeHopfPoints
import Mathlib.Algebra.Algebra.Tower
import Mathlib.FieldTheory.KrullTopology

/-! # The actual continuous Galois action on finite free Hopf-algebra points -/

namespace Dubon2026
noncomputable section
open Filter Topology

variable {R A F K : Type*} [CommRing R] [CommRing A] [HopfAlgebra R A]
  [Field F] [Field K] [Algebra R F] [Algebra F K] [Algebra R K]
  [IsScalarTower R F K]

/-- The original field automorphisms act on genuine points through restriction of scalars and their actual coordinate values. -/
def hopfPointsGaloisAction :
    (K ≃ₐ[F] K) →* MulAut (WithConv (A →ₐ[R] K)) where
  toFun g := commutativeHopfPointsAutomorphism (g.restrictScalars R)
  map_one' := by
    ext p a
    rfl
  map_mul' g h := by
    ext p a
    rfl

/-- The actual Galois point action applies the original field automorphism to each original coordinate value. -/
theorem hopfPointsGaloisAction_apply (g : K ≃ₐ[F] K)
    (p : WithConv (A →ₐ[R] K)) (a : A) :
    hopfPointsGaloisAction (R := R) (A := A) g p a = g (p a) := by
  rfl

/-- A finite free coordinate algebra and an algebraic point-value field force the actual point-action kernel to be open in the original Krull topology. -/
theorem hopfPointsGaloisAction_isOpen_ker [Module.Free R A] [Module.Finite R A]
    [Algebra.IsIntegral F K] :
    IsOpen ((hopfPointsGaloisAction (R := R) (A := A) (F := F) (K := K)).ker :
      Set (K ≃ₐ[F] K)) := by
  classical
  letI : Finite (WithConv (A →ₐ[R] K)) := finiteFreeHopfPoints_finite
  let b := Module.Free.chooseBasis R A
  have hker : ((hopfPointsGaloisAction (R := R) (A := A) (F := F) (K := K)).ker :
      Set (K ≃ₐ[F] K)) =
      ⋂ (p : WithConv (A →ₐ[R] K)) (i : Module.Free.ChooseBasisIndex R A),
        (MulAction.stabilizer (K ≃ₐ[F] K) (p (b i)) : Set (K ≃ₐ[F] K)) := by
    ext g
    simp only [Set.mem_iInter, SetLike.mem_coe, MonoidHom.mem_ker,
      MulAction.mem_stabilizer_iff]
    constructor
    · intro h p i
      exact congrArg (fun e : MulAut (WithConv (A →ₐ[R] K)) => e p (b i)) h
    · intro h
      apply MulEquiv.ext
      intro p
      apply WithConv.ext
      apply AlgHom.toLinearMap_injective
      exact b.ext (fun i => h p i)
  rw [hker]
  exact isOpen_iInter_of_finite fun p => isOpen_iInter_of_finite fun i =>
    stabilizer_isOpen_of_isIntegral (K := F) (p (b i))

/-- The constructed action on the genuine finite point group is continuous for its discrete automorphism group, derived from finite coordinate stabilizers in the original Krull topology. -/
theorem hopfPointsGaloisAction_continuous [Module.Free R A] [Module.Finite R A]
    [Algebra.IsIntegral F K]
    [TopologicalSpace (MulAut (WithConv (A →ₐ[R] K)))]
    [DiscreteTopology (MulAut (WithConv (A →ₐ[R] K)))] :
    Continuous (hopfPointsGaloisAction (R := R) (A := A) (F := F) (K := K)) := by
  apply continuous_of_tendsto_nhds_one
  apply tendsto_const_nhds.congr'
  filter_upwards [(hopfPointsGaloisAction_isOpen_ker (R := R) (A := A) (F := F)
    (K := K)).mem_nhds (Subgroup.one_mem _)] with g hg
  exact (MonoidHom.mem_ker.mp hg).symm

end
end Dubon2026
