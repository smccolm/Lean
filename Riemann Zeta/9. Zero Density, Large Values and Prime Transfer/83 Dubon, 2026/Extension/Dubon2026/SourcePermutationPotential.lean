import Dubon2026.SourceCupThreeNativeCocycles
import Mathlib.GroupTheory.GroupAction.Quotient

/-! DUB-17/18 -> residual Galois association -> integral weight-two lifting.
For the actual induced cocycle, vanishing on finite-order subgroup elements
makes its restrictions to the modular-generator orbits coboundaries. Lifting
these potentials permits the existing SL2 cocycle-existence theorem to apply.
Adapted to native Mathlib cocycles from anthropics/fermats-last-theorem,
revision 6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_CohCarrier_mem_span_int_of_forall_isOfFinOrder_apply_eq_zero.lean.txt,
exists_potential (Apache-2.0; retained LICENSE and NOTICE).
-/

namespace Dubon2026
noncomputable section
open groupCohomology

variable (G Ω A : Type) [Group G] [MulAction G Ω] [AddCommGroup A]

/-- The original inverse-coordinate action with arbitrary additive coefficients,
needed for the integral free module mapping onto the residue field. -/
def sourceAdditivePermutationRep : Representation ℤ G (Ω → A) where
  toFun g := LinearMap.funLeft ℤ A (fun i : Ω => g⁻¹ • i)
  map_one' := by ext x i; simp
  map_mul' g h := by ext x i; simp [mul_smul]

/-- The additive coefficient action is the actual inverse-coordinate action. -/
theorem sourceAdditivePermutationRep_apply (g : G) (f : Ω → A) (i : Ω) :
    sourceAdditivePermutationRep G Ω A g f i = f (g⁻¹ • i) := rfl

variable {G Ω A}

/-- A native permutation cocycle which vanishes on stabilizers of a subgroup
is a coboundary on that subgroup, with no division by its order. -/
theorem sourcePermutationCocycle_exists_potential
    (c : cocycles₁ (Rep.of (sourceAdditivePermutationRep G Ω A)))
    (K : Subgroup G)
    (hK : ∀ k ∈ K, ∀ y : Ω, k • y = y → c k y = 0) :
    ∃ f : Ω → A, ∀ k ∈ K, ∀ y, c k y = f y - f (k⁻¹ • y) := by
  classical
  have hmul (g h : G) (y : Ω) :
      c (g * h) y = c g y + c h (g⁻¹ • y) := by
    exact congrFun (SourceCupThree.cocycle_mul c.property g h) y
  have hinv (g : G) (y : Ω) : c g⁻¹ y = -c g (g • y) := by
    simpa only [Pi.neg_apply, sourceAdditivePermutationRep_apply, inv_inv]
      using congrFun (SourceCupThree.cocycle_inv c.property g) y
  let base : Ω → Ω := fun x => (Quotient.mk (MulAction.orbitRel K Ω) x).out
  have hbase : ∀ x : Ω, ∃ s : G, s ∈ K ∧ s • base x = x := by
    intro x
    have hrel : (MulAction.orbitRel K Ω) (base x) x := Quotient.mk_out x
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hrel
    obtain ⟨u, hu⟩ := hrel
    refine ⟨((u⁻¹ : K) : G), (u⁻¹).2, ?_⟩
    rw [← hu, ← Subgroup.smul_def, inv_smul_smul]
  choose s hsK hs using hbase
  have hbase_smul : ∀ k ∈ K, ∀ x : Ω, base (k • x) = base x := by
    intro k hk x
    show (Quotient.mk (MulAction.orbitRel K Ω) (k • x)).out =
      (Quotient.mk (MulAction.orbitRel K Ω) x).out
    congr 1
    exact Quotient.sound ⟨⟨k, hk⟩, rfl⟩
  refine ⟨fun x => c (s x) x, ?_⟩
  intro k hk x
  have hb : base (k⁻¹ • x) = base x := hbase_smul k⁻¹ (inv_mem hk) x
  have hs' : s (k⁻¹ • x) • base x = k⁻¹ • x := by rw [← hb]; exact hs _
  have hsx : (s x)⁻¹ • x = base x := by rw [inv_smul_eq_iff, hs x]
  have hκK : (s x)⁻¹ * k * s (k⁻¹ • x) ∈ K :=
    mul_mem (mul_mem (inv_mem (hsK x)) hk) (hsK _)
  have hκy : ((s x)⁻¹ * k * s (k⁻¹ • x)) • base x = base x := by
    rw [mul_smul, mul_smul, hs', smul_inv_smul, hsx]
  have hκ0 := hK _ hκK _ hκy
  have hdecomp : s (k⁻¹ • x) =
      k⁻¹ * (s x * ((s x)⁻¹ * k * s (k⁻¹ • x))) := by group
  have key : c (s (k⁻¹ • x)) (k⁻¹ • x) = -c k x + c (s x) x := by
    rw [hdecomp, hmul, hmul, hinv]
    simp only [inv_inv, smul_inv_smul, hsx, hκ0, add_zero]
  change c k x = c (s x) x - c (s (k⁻¹ • x)) (k⁻¹ • x)
  rw [key]
  abel

end
end Dubon2026
