import Dubon2026.SourceCellIntegerSpanningTree
import Mathlib.LinearAlgebra.InvariantBasisNumber

/-! DUB-17/18 -> original Abel-Jacobi -> 2g generating loops -> tree/cotree.
Integer chains retain the actual edge labels needed by period sums. The source
minimal connected subset argument avoids translating a multigraph into a simple
graph and back. These foundations will be consumed by the original dissection
tree/cotree theorem; no loop generation is claimed at this intermediate stage.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.IntegerEdgeChains
noncomputable section
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (hd tl : E → V)

theorem spanningTree_card [Nonempty V] (T : Finset E) (hT : IsTree hd tl T) :
    T.card + 1 = Fintype.card V := by
  classical
  obtain ⟨v₀⟩ := ‹Nonempty V›

  set ext : (↥T → ℤ) → (E → ℤ) := fun d e => if he : e ∈ T then d ⟨e, he⟩ else 0
  have hext_T : ∀ d e (he : e ∈ T), ext d e = d ⟨e, he⟩ := fun d e he => dif_pos he
  have hext_nT : ∀ d, ∀ e ∉ T, ext d e = 0 := fun d e he => dif_neg he
  set c : V → E → ℤ := fun v => Classical.choose (hT v₀ v).exists
  have hcspec : ∀ v, (∀ e ∉ T, c v e = 0) ∧
      ∀ w, bd hd tl (c v) w = (if w = v then (1:ℤ) else 0) - (if w = v₀ then 1 else 0) :=
    fun v => Classical.choose_spec (hT v₀ v).exists

  have hsum0 : ∀ d : E → ℤ, ∑ w, bd hd tl d w = 0 := by
    intro d
    have := sum_bd_eq hd tl d Finset.univ
    simp only [Finset.mem_univ, if_true, sub_self, Finset.sum_const_zero] at this
    exact this

  let L : (↥T → ℤ) →ₗ[ℤ] ({v : V // v ≠ v₀} → ℤ) :=
    { toFun := fun d v => bd hd tl (ext d) v.1
      map_add' := fun d₁ d₂ => funext fun v => by
        rw [show ext (d₁ + d₂) = ext d₁ + ext d₂ from funext (fun e => by
          simp only [ext, Pi.add_apply]; split_ifs <;> simp), bd_add]; rfl
      map_smul' := fun n d => funext fun v => by
        rw [show ext (n • d) = n • ext d from funext (fun e => by
          simp only [ext, Pi.smul_apply]; split_ifs <;> simp), bd_smul]; rfl }
  have hLinj : Function.Injective L := by
    intro d₁ d₂ heq

    have hbd0 : ∀ w, bd hd tl (ext d₁ - ext d₂) w = 0 := by
      intro w
      by_cases hw : w = v₀
      · subst hw
        have h := hsum0 (ext d₁ - ext d₂)
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ w),
          ← Finset.sdiff_singleton_eq_erase] at h
        have hrest : ∑ w' ∈ Finset.univ \ {w}, bd hd tl (ext d₁ - ext d₂) w' = 0 := by
          refine Finset.sum_eq_zero (fun w' hw' => ?_)
          simp only [Finset.mem_sdiff, Finset.mem_singleton] at hw'
          have := congrFun heq ⟨w', hw'.2⟩
          simp only [L, LinearMap.coe_mk, AddHom.coe_mk] at this
          rw [bd_sub]; linarith
        linarith
      · have := congrFun heq ⟨w, hw⟩
        simp only [L, LinearMap.coe_mk, AddHom.coe_mk] at this
        rw [bd_sub]; linarith

    have hdiff : (ext d₁ - ext d₂) = (0 : E → ℤ) :=
      (hT v₀ v₀).unique
        ⟨fun e he => by
            show ext d₁ e - ext d₂ e = 0
            rw [hext_nT d₁ e he, hext_nT d₂ e he]; ring,
         fun w => by simp only [hbd0 w]; split_ifs <;> ring⟩
        ⟨fun _ _ => rfl, fun w => by unfold bd; simp⟩
    funext e
    have := congrFun hdiff e.1
    simp only [Pi.sub_apply, hext_T d₁ e.1 e.2, hext_T d₂ e.1 e.2, Pi.zero_apply] at this
    linarith
  have hLsurj : Function.Surjective L := by
    intro a
    refine ⟨fun e => ∑ v : {v : V // v ≠ v₀}, a v * c v.1 e.1, ?_⟩
    funext ⟨w, hw⟩
    simp only [L, LinearMap.coe_mk, AddHom.coe_mk]

    have hext_eq : ext (fun e => ∑ v : {v : V // v ≠ v₀}, a v * c v.1 e.1) =
        fun e => ∑ v : {v : V // v ≠ v₀}, a v * c v.1 e := by
      funext e
      by_cases he : e ∈ T
      · simp only [ext, dif_pos he]
      · simp only [ext, dif_neg he]
        exact (Finset.sum_eq_zero (fun v _ => by rw [(hcspec v.1).1 e he, mul_zero])).symm
    rw [hext_eq, show (fun e => ∑ v : {v : V // v ≠ v₀}, a v * c v.1 e) =
          (fun e => ∑ v : {v : V // v ≠ v₀}, ((a v) • (c v.1)) e) from
        funext (fun e => Finset.sum_congr rfl (fun v _ => by
          simp only [Pi.smul_apply, smul_eq_mul])),
      bd_finsum]
    rw [show (∑ v : {v : V // v ≠ v₀}, bd hd tl ((a v) • (c v.1)) w) =
          ∑ v : {v : V // v ≠ v₀}, a v * ((if w = v.1 then (1:ℤ) else 0) - if w = v₀ then 1 else 0)
        from Finset.sum_congr rfl (fun v _ => by rw [bd_smul, (hcspec v.1).2 w])]
    rw [if_neg hw]
    simp only [sub_zero]
    rw [Finset.sum_eq_single ⟨w, hw⟩]
    · rw [if_pos rfl, mul_one]
    · intro v _ hne
      rw [if_neg (fun h => hne (Subtype.ext h.symm)), mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hequiv := LinearEquiv.ofBijective L ⟨hLinj, hLsurj⟩
  have hc := card_eq_of_linearEquiv ℤ hequiv
  simp only [Fintype.card_coe, Fintype.card_subtype_compl, Fintype.card_subtype_eq] at hc
  have hVpos : 1 ≤ Fintype.card V := Fintype.card_pos
  omega

end
end Dubon2026.SourceFunctionField.CellGeometry.IntegerEdgeChains
