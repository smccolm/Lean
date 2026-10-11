import Dubon2026.HopfCoinvariantPointBaseChange
import Dubon2026.HopfPointBaseChangeNaturality
import Dubon2026.HopfCoinvariantPointFibers

/-! # Genuine point fibers of the original integral invariant coordinates -/

namespace Dubon2026
noncomputable section
open WithConv
open scoped TensorProduct

variable {R K A B : Type*} [CommRing R] [Field K] [IsAlgClosed K]
  [Algebra R K] [Module.Flat R K]
  [CommRing A] [HopfAlgebra R A] [Module.Finite R A]
  [CommRing B] [HopfAlgebra R B] [Module.Finite R B] [IsReduced (K ⊗[R] B)]

/-- Equality on the original integral invariants is exactly multiplication by an original subgroup point. The actual flat invariant base change and original point-map naturality transport the proved geometric fiber theorem without changing either original point. -/
theorem integralHopfCoinvariantPoints_fiber_orbit (q : A →ₐc[R] B)
    (p r : WithConv (A →ₐ[R] K)) :
    p.ofConv.comp (hopfSubgroupCoinvariants q).val =
      r.ofConv.comp (hopfSubgroupCoinvariants q).val ↔
    ∃ s : WithConv (B →ₐ[R] K), p * hopfPointsRestriction q s = r := by
  let ea := hopfBaseChangePointsEquiv (R := R) (F := K) (A := A) (K := K)
  let eb := hopfBaseChangePointsEquiv (R := R) (F := K) (A := B) (K := K)
  constructor
  · intro h
    have hg := (hopfCoinvariantPointBaseChange_restriction_iff q p.ofConv r.ofConv).mp h
    obtain ⟨s, hs⟩ := (hopfCoinvariantPoints_fiber_orbit
      (hopfBaseChangeCoordinateMap (S := K) q) (ea p) (ea r)).mp hg
    refine ⟨eb.symm s, ?_⟩
    apply ea.injective
    rw [map_mul]
    change ea p * hopfBaseChangePointsEquiv (F := K) (hopfPointsRestriction q (eb.symm s)) = ea r
    rw [hopfBaseChangePointsEquiv_restriction]
    simpa only [show hopfBaseChangePointsEquiv (F := K) (eb.symm s) = s from eb.apply_symm_apply s]
      using hs
  · rintro ⟨s, hs⟩
    apply (hopfCoinvariantPointBaseChange_restriction_iff q p.ofConv r.ofConv).mpr
    apply (hopfCoinvariantPoints_fiber_orbit
      (hopfBaseChangeCoordinateMap (S := K) q) (ea p) (ea r)).mpr
    refine ⟨eb s, ?_⟩
    calc
      _ = ea (p * hopfPointsRestriction q s) := by
        rw [map_mul]
        exact congrArg (fun x => ea p * x) (hopfBaseChangePointsEquiv_restriction q s).symm
      _ = ea r := congrArg ea hs

omit [Module.Finite R B] [IsReduced (K ⊗[R] B)] in
/-- Every genuine point of the original integral invariant coordinates extends to an original point of the finite algebra. Actual flat invariant base change reduces extension to the proved geometric lying-over theorem, and original tensor evaluation returns precisely the requested integral point. -/
theorem integralHopfCoinvariantPoints_restriction_surjective (q : A →ₐc[R] B) :
    Function.Surjective (fun p : WithConv (A →ₐ[R] K) =>
      toConv (p.ofConv.comp (hopfSubgroupCoinvariants q).val)) := by
  intro r
  let e := hopfCoinvariantBaseChangeAlgEquiv (S := K) q
  let rk := (AlgHom.liftEquiv R K (hopfSubgroupCoinvariants q) K r.ofConv).comp e.symm.toAlgHom
  obtain ⟨pk, hpk⟩ := finiteAlgebraPointRestriction_surjective
    (hopfSubgroupCoinvariants (hopfBaseChangeCoordinateMap (S := K) q)) rk
  change pk.comp (hopfSubgroupCoinvariants (hopfBaseChangeCoordinateMap (S := K) q)).val = rk at hpk
  let p := (AlgHom.liftEquiv R K A K).symm pk
  refine ⟨toConv p, WithConv.ext ?_⟩
  apply (AlgHom.liftEquiv R K (hopfSubgroupCoinvariants q) K).injective
  rw [← hopfCoinvariantPointBaseChange_restriction q p,
    show AlgHom.liftEquiv R K A K p = pk from (AlgHom.liftEquiv R K A K).apply_symm_apply pk,
    hpk]
  apply AlgHom.ext
  intro z
  change (AlgHom.liftEquiv R K (hopfSubgroupCoinvariants q) K r.ofConv) (e.symm (e z)) = _
  rw [AlgEquiv.symm_apply_apply]

end
end Dubon2026
