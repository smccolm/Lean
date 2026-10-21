import Dubon2026.SourceSL2PermutationLift
import Dubon2026.SourceCupThreePrimitive

/-! DUB-17/18 -> residual Galois association -> integral weight-two lifting.
The original Gamma0 homomorphism induces a native cocycle by the already
proved coset-transition formula. Vanishing on finite-order elements makes
the stabilizer conditions automatic. Evaluation at the original identity
coset recovers a lift of the original homomorphism.
-/

namespace Dubon2026
noncomputable section
open scoped MatrixGroups
open Matrix.SpecialLinearGroup CongruenceSubgroup groupCohomology

variable (M : ℕ) (κ : Type) [CommRing κ]

private theorem transition_finiteOrder (g : SL(2, ℤ)) (hg : IsOfFinOrder g)
    (q : SL(2, ℤ) ⧸ Gamma0 M) (hq : g • q = q) :
    IsOfFinOrder (SourceCupThree.jj M g q) := by
  apply Submonoid.isOfFinOrder_coe.mp
  have hqi : g⁻¹ • q = q := by
    calc
      g⁻¹ • q = g⁻¹ • (g • q) := congrArg (fun y => g⁻¹ • y) hq.symm
      _ = q := inv_smul_smul g q
  rw [SourceCupThree.coe_jj, hqi]
  obtain ⟨n, hn, hgn⟩ := (isOfFinOrder_inv_iff.mpr hg).exists_pow_eq_one
  apply isOfFinOrder_iff_pow_eq_one.mpr
  refine ⟨n, hn, ?_⟩
  have he : (q.out⁻¹ * g⁻¹ * q.out) ^ n = q.out⁻¹ * (g⁻¹ ^ n) * q.out := by
    simpa only [inv_inv] using
      (conj_pow (a := q.out⁻¹) (b := g⁻¹) (i := n))
  rw [← mul_assoc, he, hgn]
  simp

/-- An original congruence homomorphism vanishing on finite-order elements
lifts through a surjective additive coefficient map. No lifted homomorphism
or cohomological lifting assumption is supplied. -/
theorem sourceGamma0Hom_lift_of_torsion_vanishing
    {A : Type} [AddCommGroup A] (π : A →+ κ) (hπ : Function.Surjective π)
    (x : Additive (Gamma0 M) →+ κ)
    (hx : ∀ g : Gamma0 M, IsOfFinOrder g → x (Additive.ofMul g) = 0) :
    ∃ y : Additive (Gamma0 M) →+ A, π.comp y = x := by
  let cfun := SourceCupThree.zY M κ x
  have hcfun : cfun ∈ cocycles₁ (Rep.of
      (sourceAdditivePermutationRep SL(2, ℤ) (SL(2, ℤ) ⧸ Gamma0 M) κ)) := by
    apply (mem_cocycles₁_iff _).mpr
    intro g h
    funext q
    exact congrFun ((mem_cocycles₁_iff _).mp (SourceCupThree.zY_mem M κ x) g h) q
  let c : cocycles₁ (Rep.of
      (sourceAdditivePermutationRep SL(2, ℤ) (SL(2, ℤ) ⧸ Gamma0 M) κ)) :=
    ⟨cfun, hcfun⟩
  have hc : ∀ g : SL(2, ℤ), IsOfFinOrder g → ∀ q : SL(2, ℤ) ⧸ Gamma0 M,
      g • q = q → c g q = 0 := by
    intro g hg q hq
    change x (Additive.ofMul (SourceCupThree.jj M g q)) = 0
    exact hx _ (transition_finiteOrder M g hg q hq)
  obtain ⟨z, hz⟩ := sourceSL2PermutationCocycle_lift M π hπ c hc
  let yfun : Additive (Gamma0 M) → A :=
    fun a => -z (Additive.toMul a).val (SourceCupThree.y0 M)
  have hyfun (a b : Additive (Gamma0 M)) : yfun (a + b) = yfun a + yfun b := by
    have h := congrFun ((mem_cocycles₁_iff z).mp z.property
      (Additive.toMul a).val (Additive.toMul b).val) (SourceCupThree.y0 M)
    change z ((Additive.toMul a).val * (Additive.toMul b).val) (SourceCupThree.y0 M) =
      z (Additive.toMul b).val ((Additive.toMul a).val⁻¹ • SourceCupThree.y0 M) +
      z (Additive.toMul a).val (SourceCupThree.y0 M) at h
    rw [SourceCupThree.inv_smul_y0] at h
    change -z ((Additive.toMul a).val * (Additive.toMul b).val) (SourceCupThree.y0 M) = _
    rw [h]
    change -(z (Additive.toMul b).val (SourceCupThree.y0 M) +
      z (Additive.toMul a).val (SourceCupThree.y0 M)) =
      -z (Additive.toMul a).val (SourceCupThree.y0 M) +
      -z (Additive.toMul b).val (SourceCupThree.y0 M)
    abel
  refine ⟨AddMonoidHom.mk' yfun hyfun, ?_⟩
  ext a
  change π (-z (Additive.toMul a).val (SourceCupThree.y0 M)) = x a
  rw [map_neg, hz]
  change -SourceCupThree.zY M κ x (Additive.toMul a).val (SourceCupThree.y0 M) = x a
  rw [SourceCupThree.zY_y0, neg_neg]
  rfl

end
end Dubon2026
