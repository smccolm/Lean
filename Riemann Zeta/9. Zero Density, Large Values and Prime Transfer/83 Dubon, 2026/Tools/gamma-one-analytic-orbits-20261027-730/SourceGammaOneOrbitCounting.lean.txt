import Dubon2026.SourceOriginalCosetOrbitOrder

/-! DUB-17/18 -> actual Gamma1 global charts -> exact elliptic ramification.
The weighted subgroup-orbit count supplies the comparison with actual
finite j-fiber orders. Adapt only the required finite coset-fiber proof
from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularCurve_ComplexPlaceDictionaryOf_two_mul_ramification_eq_card_stabilizer.
No exact field degree or ramification identity is assumed. -/
namespace Dubon2026.SourceFunctionField.GammaOne.OrbitCounting
noncomputable section
open MulAction

variable {G : Type*} [Group G] {α : Type*} [MulAction G α]

theorem card_stabilizer_subgroup (L : Subgroup G) (a : α) :
    Nat.card (stabilizer L a) = Nat.card (L ⊓ stabilizer G a : Subgroup G) := by
  refine Nat.card_congr
    { toFun := fun g => ⟨(g.1 : G), g.1.2, by
        have h := g.2
        rw [mem_stabilizer_iff, Subgroup.smul_def] at h
        exact h⟩
      invFun := fun g => ⟨⟨g.1, g.2.1⟩, by
        rw [mem_stabilizer_iff, Subgroup.smul_def]
        exact g.2.2⟩
      left_inv := fun g => rfl
      right_inv := fun g => rfl }

theorem relIndex_stabilizer_smul_of_mem (H : Subgroup G) {g : G} (hg : g ∈ H) (x : α) :
    H.relIndex (stabilizer G (g • x)) = H.relIndex (stabilizer G x) := by
  have hH : H.map (MulAut.conj g).toMonoidHom = H := by
    ext y
    rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
    constructor
    · intro h
      have := H.mul_mem (H.mul_mem hg h) (H.inv_mem hg)
      simpa [mul_assoc] using this
    · intro h
      exact H.mul_mem (H.mul_mem (H.inv_mem hg) h) hg
  rw [stabilizer_smul_eq_stabilizer_map_conj]
  conv_lhs => rw [← hH]
  exact Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective

theorem relIndex_stabilizer_mul_card_stabilizer (H : Subgroup G) (x : α) :
    H.relIndex (stabilizer G x) * Nat.card (stabilizer H x) = Nat.card (stabilizer G x) := by
  rw [card_stabilizer_subgroup, ← Subgroup.subgroupOf_map_subtype,
    Nat.card_congr (Subgroup.equivMapOfInjective _ _ (Subgroup.subtype_injective _)).toEquiv.symm,
    Subgroup.relIndex, mul_comm]
  exact Subgroup.card_mul_index _

variable (H : Subgroup G) (a : α)

private def fib : Quotient (QuotientGroup.rightRel H) → orbitRel.Quotient H (orbit G a) :=
  Quotient.lift (fun g : G => Quotient.mk (orbitRel H (orbit G a)) ⟨g • a, mem_orbit a g⟩) (by
    intro g g' hgg'
    have hgg'' : g' * g⁻¹ ∈ H := QuotientGroup.rightRel_apply.mp hgg'
    refine Quotient.sound (mem_orbit_iff.mpr ?_)
    refine ⟨⟨g * g'⁻¹, by simpa using H.inv_mem hgg''⟩, Subtype.ext ?_⟩
    show (g * g'⁻¹) • g' • a = g • a
    rw [smul_smul, inv_mul_cancel_right])

private theorem fib_mk (g : G) :
    fib H a (Quotient.mk _ g) = Quotient.mk (orbitRel H (orbit G a)) ⟨g • a, mem_orbit a g⟩ := rfl

private theorem fib_surjective : Function.Surjective (fib H a) := by
  intro q
  induction q using Quotient.inductionOn with
  | h x =>
    obtain ⟨g, hg⟩ := mem_orbit_iff.mp x.2
    exact ⟨Quotient.mk _ g, by rw [fib_mk]; congr 1; exact Subtype.ext hg⟩

theorem finite_orbitRelQuotient_orbit [H.FiniteIndex] : Finite (orbitRel.Quotient H (orbit G a)) := by
  haveI : Finite (Quotient (QuotientGroup.rightRel H)) :=
    Finite.of_equiv (G ⧸ H) (QuotientGroup.quotientRightRelEquivQuotientLeftRel H).symm
  exact Finite.of_surjective _ (fib_surjective H a)

private theorem card_fiber (q : orbitRel.Quotient H (orbit G a)) :
    Nat.card {c // fib H a c = q} = H.relIndex (stabilizer G ((q.out : orbit G a) : α)) := by
  classical
  set x : orbit G a := q.out with hx
  obtain ⟨g₀, hg₀⟩ := mem_orbit_iff.mp x.2
  have hq : Quotient.mk (orbitRel H (orbit G a)) x = q := Quotient.out_eq q
  let K : Subgroup G := stabilizer G (x : α)

  let φ : K → {c // fib H a c = q} := fun k => ⟨Quotient.mk _ ((k : G) * g₀), by
    rw [fib_mk, ← hq]
    congr 1
    apply Subtype.ext
    show ((k : G) * g₀) • a = (x : α)
    rw [mul_smul, hg₀]
    exact k.2⟩
  have hφ : ∀ k k' : K, φ k = φ k' ↔ QuotientGroup.rightRel (H.subgroupOf K) k k' := by
    intro k k'
    rw [QuotientGroup.rightRel_apply, Subgroup.mem_subgroupOf, Subtype.ext_iff]
    show Quotient.mk (QuotientGroup.rightRel H) ((k : G) * g₀) = Quotient.mk _ ((k' : G) * g₀) ↔ _
    rw [Quotient.eq, QuotientGroup.rightRel_apply]
    simp [mul_assoc]
  let ψ : Quotient (QuotientGroup.rightRel (H.subgroupOf K)) → {c // fib H a c = q} :=
    Quotient.lift φ (fun k k' h => (hφ k k').mpr h)
  have hψ : Function.Bijective ψ := by
    constructor
    · intro c c'
      induction c using Quotient.inductionOn with
      | h k =>
        induction c' using Quotient.inductionOn with
        | h k' =>
          intro h
          exact Quotient.sound ((hφ k k').mp h)
    · rintro ⟨c, hc⟩
      induction c using Quotient.inductionOn with
      | h g =>
        rw [fib_mk, ← hq] at hc
        have hc' : (⟨g • a, mem_orbit a g⟩ : orbit G a) ∈ orbit H x := Quotient.exact hc
        obtain ⟨h, hh⟩ := mem_orbit_iff.mp hc'
        have hh' : (h : G) • (x : α) = g • a := congrArg Subtype.val hh
        refine ⟨Quotient.mk _ ⟨(h : G)⁻¹ * g * g₀⁻¹, ?_⟩, ?_⟩
        · rw [mem_stabilizer_iff, mul_smul, mul_smul, ← hg₀, inv_smul_smul, hg₀, ← hh', inv_smul_smul]
        · apply Subtype.ext
          show Quotient.mk (QuotientGroup.rightRel H) (((h : G)⁻¹ * g * g₀⁻¹) * g₀) = Quotient.mk _ g
          refine Quotient.sound (QuotientGroup.rightRel_apply.mpr ?_)
          simp [mul_assoc]
  rw [← Nat.card_eq_of_bijective ψ hψ, Subgroup.relIndex, Subgroup.index,
    Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel (H.subgroupOf K))]

theorem exists_smul_out_eq (b : orbit G a) :
    ∃ h ∈ H, h • (((Quotient.mk (orbitRel H (orbit G a)) b).out : orbit G a) : α) = b := by
  have hrel : ((Quotient.mk (orbitRel H (orbit G a)) b).out : orbit G a) ∈ orbit H b :=
    Quotient.mk_out (s := orbitRel H (orbit G a)) b
  obtain ⟨h, hh⟩ := mem_orbit_iff.mp hrel
  refine ⟨((h⁻¹ : H) : G), (h⁻¹).2, ?_⟩
  rw [← hh, Subgroup.coe_inv]
  show (h : G)⁻¹ • (h : G) • (b : α) = b
  rw [inv_smul_smul]

theorem finsum_relIndex_stabilizer_eq_index [H.FiniteIndex] :
    ∑ᶠ q : orbitRel.Quotient H (orbit G a),
        H.relIndex (stabilizer G ((q.out : orbit G a) : α)) = H.index := by
  classical
  haveI := finite_orbitRelQuotient_orbit H a
  haveI : Fintype (orbitRel.Quotient H (orbit G a)) := Fintype.ofFinite _
  haveI : Finite (Quotient (QuotientGroup.rightRel H)) :=
    Finite.of_equiv (G ⧸ H) (QuotientGroup.quotientRightRelEquivQuotientLeftRel H).symm
  rw [finsum_eq_sum_of_fintype, Subgroup.index,
    ← Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel H),
    ← Nat.card_congr (Equiv.sigmaFiberEquiv (fib H a)), Nat.card_sigma]
  exact Finset.sum_congr rfl fun q _ => (card_fiber H a q).symm

end
end Dubon2026.SourceFunctionField.GammaOne.OrbitCounting
