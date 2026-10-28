import Dubon2026.SourceIntegralCharacterCrossed

/-! DUB-17/18 -> original Gamma1 Picard/H1 -> Abel-Jacobi -> unitary
multiplier logarithms -> integral parabolic-character lifting -> actual
permutation cocycles and factorwise potentials. Adapted from
anthropics/fermats-last-theorem, Apache-2.0, revision
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularCurve_Period_exists_parabolicHoms_int_castAddHom_comp_eq_of_forall_isOfFinOrder.
These explicit upstream identities support the integer lift; no lift is assumed. -/
namespace Dubon2026.SourceIntegralCharacterLift
noncomputable section
open Subgroup
section Crossed
variable {G : Type*} [Group G] {Ω : Type*} [MulAction G Ω] {A B : Type*} [AddCommGroup A] [AddCommGroup B]
theorem exists_potential {c : G → Ω → A} (hc : IsCrossed c) (K : Subgroup G)
    (hK : ∀ k ∈ K, ∀ y : Ω, k • y = y → c k y = 0) :
    ∃ f : Ω → A, ∀ k ∈ K, c k = cob f k := by
  classical

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
    show (Quotient.mk (MulAction.orbitRel K Ω) (k • x)).out = (Quotient.mk (MulAction.orbitRel K Ω) x).out
    congr 1
    exact Quotient.sound ⟨⟨k, hk⟩, rfl⟩
  refine ⟨fun x => c (s x) x, ?_⟩
  intro k hk
  funext x
  rw [cob_apply]
  have hb : base (k⁻¹ • x) = base x := hbase_smul k⁻¹ (inv_mem hk) x
  have hs' : s (k⁻¹ • x) • base x = k⁻¹ • x := by rw [← hb]; exact hs _
  have hsx : (s x)⁻¹ • x = base x := by rw [inv_smul_eq_iff, hs x]

  have hκK : (s x)⁻¹ * k * s (k⁻¹ • x) ∈ K := mul_mem (mul_mem (inv_mem (hsK x)) hk) (hsK _)
  have hκy : ((s x)⁻¹ * k * s (k⁻¹ • x)) • base x = base x := by
    rw [mul_smul, mul_smul, hs', smul_inv_smul, hsx]
  have hκ0 : c ((s x)⁻¹ * k * s (k⁻¹ • x)) (base x) = 0 := hK _ hκK _ hκy

  have hdecomp : s (k⁻¹ • x) = k⁻¹ * (s x * ((s x)⁻¹ * k * s (k⁻¹ • x))) := by group
  have key : c (s (k⁻¹ • x)) (k⁻¹ • x) = -c k x + c (s x) x := by
    rw [hdecomp, hc, hc]
    simp only [Pi.add_apply, tr_apply, inv_inv]
    rw [hc.map_inv_apply, smul_inv_smul, hsx, hκ0, add_zero]
  rw [key]; abel

/-- The translation automorphism of the multiplicative form of the coefficient group. -/
def trAut (g : G) : Multiplicative (Ω → A) ≃* Multiplicative (Ω → A) :=
  AddEquiv.toMultiplicative
    { toFun := tr g
      invFun := tr g⁻¹
      left_inv := fun F => by simp [← tr_mul, tr_one (G := G)]
      right_inv := fun F => by simp [← tr_mul, tr_one (G := G)]
      map_add' := tr_add g }

@[scoped simp] theorem trAut_apply (g : G) (F : Multiplicative (Ω → A)) :
    trAut g F = Multiplicative.ofAdd (tr g (Multiplicative.toAdd F)) := rfl

variable (G Ω A) in

/-- The group homomorphism defining the translation action. -/
def trHom : G →* MulAut (Multiplicative (Ω → A)) where
  toFun := trAut
  map_one' := by
    ext F
    simp [tr_one (G := G)]
  map_mul' g h := by
    ext F
    simp [tr_mul]

theorem trHom_apply (g : G) (F : Multiplicative (Ω → A)) :
    trHom G Ω A g F = Multiplicative.ofAdd (tr g (Multiplicative.toAdd F)) := rfl

end Crossed
end
end Dubon2026.SourceIntegralCharacterLift
