import Dubon2026.HopfSubgroupFixedCoordinates
import Dubon2026.FiniteGroupInvariantPointOrbit
import Dubon2026.FiniteAlgebraPointRestriction

/-! # Actual invariant-coordinate point fibers are original subgroup orbits -/

namespace Dubon2026
noncomputable section
open WithConv
open scoped TensorProduct

variable {K A B : Type*} [Field K] [IsAlgClosed K]
  [CommRing A] [HopfAlgebra K A] [Module.Finite K A]
  [CommRing B] [HopfAlgebra K B] [Module.Finite K B] [IsReduced B]

/-- The original subgroup-coordinate point group in the exact fiber comparison. -/
local instance hopfCoinvariantFiberPointGroup : Group (WithConv (B →ₐ[K] K)) :=
  commutativeHopfPointsGroup

/-- Equal restrictions of two original points to the actual coaction coinvariants are related by multiplication by an actual original subgroup point. The literal fixed-coordinate identification and original invariant-prime orbit theorem derive the subgroup witness. -/
theorem hopfCoinvariantPoints_fiber_orbit (q : A →ₐc[K] B)
    (p r : WithConv (A →ₐ[K] K)) :
    p.ofConv.comp (hopfSubgroupCoinvariants q).val =
      r.ofConv.comp (hopfSubgroupCoinvariants q).val ↔
    ∃ s : WithConv (B →ₐ[K] K), p * hopfPointsRestriction q s = r := by
  constructor
  · intro h
    letI := hopfSubgroupTranslationMulSemiringAction q
    letI := hopfSubgroupTranslationScalarComm q
    letI : Finite (WithConv (B →ₐ[K] K)) := finiteFreeHopfPoints_finite
    have hS := hopfSubgroupCoinvariants_eq_fixed q
    rw [hS] at h
    obtain ⟨s, hs⟩ := finiteGroupInvariantPoint_sameRestriction_orbit
      (G := WithConv (B →ₐ[K] K)) p.ofConv r.ofConv h
    refine ⟨s, ?_⟩
    apply WithConv.ext
    apply AlgHom.ext
    intro a
    have he := AlgHom.congr_fun hs a
    change p (hopfPointTranslation (toConv (s.ofConv.comp q.toAlgHom)) a) = r a at he
    rw [hopfPointTranslation_evaluation] at he
    exact he
  · rintro ⟨s, hs⟩
    apply AlgHom.ext
    intro a
    have hc : hopfSubgroupRightCoaction q a.val = a.val ⊗ₜ[K] (1 : B) := a.property
    have ht : hopfPointTranslation (toConv (s.ofConv.comp q.toAlgHom)) a.val = a.val := by
      rw [← hopfCoinvariant_point_translation q s.ofConv a.val, hc]
      simp
    calc
      p.ofConv a.val = p (hopfPointTranslation (toConv (s.ofConv.comp q.toAlgHom)) a.val) :=
        congrArg (fun x => p x) ht.symm
      _ = (p * hopfPointsRestriction q s) a.val :=
        hopfPointTranslation_evaluation p (toConv (s.ofConv.comp q.toAlgHom)) a.val
      _ = r.ofConv a.val := by rw [hs]

omit [Module.Finite K B] [IsReduced B] in
/-- Every genuine point of the literal invariant-coordinate subalgebra extends to an original point of the finite coordinate algebra, using actual finite-algebra point extension. -/
theorem hopfCoinvariantPoints_restriction_surjective (q : A →ₐc[K] B) :
    Function.Surjective (fun p : WithConv (A →ₐ[K] K) =>
      toConv (p.ofConv.comp (hopfSubgroupCoinvariants q).val)) := by
  intro r
  obtain ⟨p, hp⟩ := finiteAlgebraPointRestriction_surjective (hopfSubgroupCoinvariants q) r.ofConv
  exact ⟨toConv p, WithConv.ext hp⟩

end
end Dubon2026
