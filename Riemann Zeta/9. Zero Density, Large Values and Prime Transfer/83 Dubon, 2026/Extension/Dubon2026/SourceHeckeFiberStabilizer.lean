import Dubon2026.SourceOriginalCosetOrbitOrder

/-! DUB-17/18 -> original Picard-period Hecke comparison -> analytic
divisor multiplicities. A transversal fiber has precisely the stabilizer
ratio that the actual normalized beta ramification supplies. The consumer
uses the genuine upper congruence subgroup and original analytic places.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularCurve_ComplexPlaceDictionary_heckeDivBar_single_pt, Counting.
-/
namespace Dubon2026.HeckeFiber
noncomputable section
section Counting

variable {G X : Type*} [Group G] [MulAction G X]

open MulAction in

theorem card_stabilizer_eq_card_filter_mul (H : Subgroup G) {ι : Type*} (R : ι → G)
    (s : Finset ι) (hcover : ∀ g : G, ∃ i ∈ s, g * (R i)⁻¹ ∈ H)
    (hdisj : ∀ i ∈ s, ∀ j ∈ s, R i * (R j)⁻¹ ∈ H → i = j) (y x : X) (g₀ : G)
    (hg₀ : g₀ • y = x) [DecidablePred fun i => R i • y ∈ orbit H x] :
    Nat.card (stabilizer G x) =
      (s.filter fun i => R i • y ∈ orbit H x).card * Nat.card (stabilizer H x) := by
  classical
  set T := s.filter fun i => R i • y ∈ orbit H x with hT
  have hidx : ∀ σ : stabilizer G x, ∃ i ∈ s, (σ : G) * g₀ * (R i)⁻¹ ∈ H := fun σ =>
    hcover ((σ : G) * g₀)
  choose idx hidx_mem hidx_H using hidx
  have hidx_unique : ∀ (σ : stabilizer G x) (i : ι), i ∈ s → (σ : G) * g₀ * (R i)⁻¹ ∈ H →
      i = idx σ := by
    intro σ i hi hH
    refine hdisj i hi (idx σ) (hidx_mem σ) ?_
    have : R i * (R (idx σ))⁻¹ = ((σ : G) * g₀ * (R i)⁻¹)⁻¹ * ((σ : G) * g₀ * (R (idx σ))⁻¹) := by
      group
    rw [this]
    exact H.mul_mem (H.inv_mem hH) (hidx_H σ)
  have hidx_T : ∀ σ : stabilizer G x, idx σ ∈ T := by
    intro σ
    rw [hT, Finset.mem_filter]
    refine ⟨hidx_mem σ, mem_orbit_iff.mpr ⟨⟨_, H.inv_mem (hidx_H σ)⟩, ?_⟩⟩
    rw [Subgroup.mk_smul, mul_inv_rev, mul_inv_rev, inv_inv, mul_smul, mul_smul,
      show (σ : G)⁻¹ • x = x from mem_stabilizer_iff.mp (inv_mem σ.2), ← hg₀, inv_smul_smul]
  have hbase : ∀ i ∈ T, ∃ σ : stabilizer G x, (σ : G) * g₀ * (R i)⁻¹ ∈ H := by
    intro i hi
    rw [hT, Finset.mem_filter] at hi
    obtain ⟨h, hh⟩ := mem_orbit_iff.mp hi.2
    refine ⟨⟨(h : G)⁻¹ * R i * g₀⁻¹, ?_⟩, ?_⟩
    · rw [mem_stabilizer_iff, mul_smul, mul_smul, ← hg₀, inv_smul_smul, hg₀, ← hh,
        Subgroup.smul_def, inv_smul_smul]
    · rw [show (h : G)⁻¹ * R i * g₀⁻¹ * g₀ * (R i)⁻¹ = (h : G)⁻¹ by group]
      exact H.inv_mem h.2
  choose! base hbase_H using hbase
  have hquot : ∀ σ : stabilizer G x, (σ : G) * ((base (idx σ) : stabilizer G x) : G)⁻¹ ∈ H := by
    intro σ
    have h1 := hidx_H σ
    have h2 := hbase_H (idx σ) (hidx_T σ)
    have : (σ : G) * ((base (idx σ) : stabilizer G x) : G)⁻¹ =
        ((σ : G) * g₀ * (R (idx σ))⁻¹) * (((base (idx σ) : stabilizer G x) : G) * g₀ *
          (R (idx σ))⁻¹)⁻¹ := by group
    rw [this]
    exact H.mul_mem h1 (H.inv_mem h2)
  have hquot_stab : ∀ σ : stabilizer G x,
      (⟨_, hquot σ⟩ : H) ∈ stabilizer H x := by
    intro σ
    rw [mem_stabilizer_iff, Subgroup.mk_smul, mul_smul,
      show ((base (idx σ) : stabilizer G x) : G)⁻¹ • x = x from
        mem_stabilizer_iff.mp (inv_mem (base (idx σ)).2)]
    exact mem_stabilizer_iff.mp σ.2
  let F : stabilizer G x → T × stabilizer H x := fun σ =>
    ⟨⟨idx σ, hidx_T σ⟩, ⟨_, hquot_stab σ⟩⟩
  have hinv_stab : ∀ p : T × stabilizer H x,
      ((p.2 : H) : G) * ((base p.1 : stabilizer G x) : G) ∈ stabilizer G x := by
    intro p
    rw [mem_stabilizer_iff, mul_smul, mem_stabilizer_iff.mp (base (p.1 : ι)).2]
    have := mem_stabilizer_iff.mp p.2.2
    rwa [Subgroup.smul_def] at this
  let Finv : T × stabilizer H x → stabilizer G x := fun p => ⟨_, hinv_stab p⟩
  have hidx_Finv : ∀ p : T × stabilizer H x, idx (Finv p) = (p.1 : ι) := by
    rintro ⟨⟨i, hi⟩, η⟩
    symm
    apply hidx_unique _ i (Finset.mem_filter.mp hi).1
    show ((η : H) : G) * ((base i : stabilizer G x) : G) * g₀ * (R i)⁻¹ ∈ H
    have : ((η : H) : G) * ((base i : stabilizer G x) : G) * g₀ * (R i)⁻¹ =
        ((η : H) : G) * (((base i : stabilizer G x) : G) * g₀ * (R i)⁻¹) := by group
    rw [this]
    exact H.mul_mem (η : H).2 (hbase_H i hi)
  let e : stabilizer G x ≃ T × stabilizer H x :=
    { toFun := F
      invFun := Finv
      left_inv := by
        intro σ
        apply Subtype.ext
        show ((σ : G) * ((base (idx σ) : stabilizer G x) : G)⁻¹) *
          ((base (idx σ) : stabilizer G x) : G) = σ
        group
      right_inv := by
        intro p
        have hi := hidx_Finv p
        apply Prod.ext
        · exact Subtype.ext hi
        · apply Subtype.ext; apply Subtype.ext
          show ((Finv p : stabilizer G x) : G) * ((base (idx (Finv p)) : stabilizer G x) : G)⁻¹
            = ((p.2 : H) : G)
          rw [hi]
          show ((p.2 : H) : G) * ((base p.1 : stabilizer G x) : G) *
            ((base (p.1 : ι) : stabilizer G x) : G)⁻¹ = ((p.2 : H) : G)
          group }
  rw [Nat.card_congr e, Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_coe]

end Counting

end
end Dubon2026.HeckeFiber
