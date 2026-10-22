import Dubon2026.SourceOriginalEdgePathIntegral

/-! DUB-17/18 -> original Abel-Jacobi -> actual fundamental-cycle loops.
A walk on the actual dissection edges gives a path on its skeleton, an integer
edge chain with the exact endpoint boundary, and its integral for every
original differential regular on that skeleton. Adapted from the verified
Apache-2.0 source anthropics/fermats-last-theorem, commit
6e837e75355538c7f80bab5b956861e86c4eacc2; existing original integral laws are reused.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.OriginalEdgePaths
noncomputable section
open SourceCurve Set KaehlerDifferential OriginalChart CellDissection
attribute [local instance] placeTopology placeChartedSpace
variable {N : ℕ} [NeZero N]
local notation "F" => modularFunctionFieldOver N ℂ

theorem exists_path_of_walk (𝒟 : CellDissection N) (𝒯 : Finset 𝒟.ιE) {u v : 𝒟.ιV}
    (hu : 𝒟.vert u ∈ 𝒟.skeleton)
    (h : Relation.ReflTransGen
      (fun a b : 𝒟.ιV => ∃ e ∈ 𝒯, 𝒟.ends e = (a, b) ∨ 𝒟.ends e = (b, a)) u v) :
    ∃ (p : Path (𝒟.vert u) (𝒟.vert v)) (c : 𝒟.ιE → ℤ),
      (∀ t, p t ∈ 𝒟.skeleton) ∧ (∀ e ∉ 𝒯, c e = 0) ∧
      (∀ w : 𝒟.ιV, (∑ e with (𝒟.ends e).2 = w, c e) - (∑ e with (𝒟.ends e).1 = w, c e) =
        (if w = v then 1 else 0) - (if w = u then 1 else 0)) ∧
      ∀ θ : Ω[F⁄ℂ], RegOnSkeleton 𝒟 θ →
        (∃ g, IsPrimitiveAlong N θ p g) ∧
          pathIntegral N θ p = ∑ e, (c e : ℂ) * 𝒟.edgeInt θ e := by
  classical
  induction h with
  | refl =>
    refine ⟨Path.refl _, 0, fun t => hu, fun e _ => rfl, fun w => by simp, fun θ hθ => ?_⟩
    have hr : ∀ t, ((Path.refl (𝒟.vert u)) t).differentialCoeff θ ∈
        ((Path.refl (𝒟.vert u)) t).toValuationSubring :=
      fun _ => (𝒟.vert u).mem_of_ord_nonneg (hθ _ hu)
    have he := pathIntegral_symm_of_coeff_mem N (Path.refl (𝒟.vert u)) hr
    change pathIntegral N θ (Path.refl (𝒟.vert u)) =
      -pathIntegral N θ (Path.refl (𝒟.vert u)) at he
    refine ⟨primitive_on_skeleton 𝒟 hθ (fun _ => hu), ?_⟩
    simp only [Pi.zero_apply, Int.cast_zero, zero_mul, Finset.sum_const_zero]
    linear_combination (1 / 2 : ℂ) * he
  | @tail b w _ hbw ih =>
    obtain ⟨p, c, hps, hcT, hbd, hint⟩ := ih
    obtain ⟨e, he𝒯, he⟩ := hbw

    have hedge : ∀ θ : Ω[F⁄ℂ], RegOnSkeleton 𝒟 θ →
        (∃ g, IsPrimitiveAlong N θ (edgePath 𝒟 e) g) ∧
          pathIntegral N θ (edgePath 𝒟 e) = 𝒟.edgeInt θ e := fun θ hθ =>
      pathIntegral_edgePath 𝒟 e fun s hs => hθ _
        (mem_iUnion.2 ⟨arcOf 𝒟 (e, true), _, ⟨s, hs, rfl⟩, rfl⟩)
    rcases he with he | he
    ·
      have h1 : 𝒟.vert b = 𝒟.vert (𝒟.ends e).1 := by rw [he]
      have h2 : 𝒟.vert w = 𝒟.vert (𝒟.ends e).2 := by rw [he]
      set q : Path (𝒟.vert b) (𝒟.vert w) := (edgePath 𝒟 e).cast h1 h2 with hq
      have hqs : ∀ t, q t ∈ 𝒟.skeleton :=
        fun t => edgePath_mem_skeleton 𝒟 e t
      refine ⟨p.trans q, fun f => c f + (if f = e then 1 else 0), ?_, ?_, ?_, ?_⟩
      · exact mem_skeleton_trans 𝒟 hps hqs
      · intro f hf
        show c f + (if f = e then 1 else 0) = 0
        rw [hcT f hf, if_neg (fun h => hf (by rw [h]; exact he𝒯)), add_zero]
      · intro x
        have hb := hbd x
        have hhd : (𝒟.ends e).2 = w := by rw [he]
        have htl : (𝒟.ends e).1 = b := by rw [he]
        have h1 : (∑ f with (𝒟.ends f).2 = x, (c f + if f = e then (1 : ℤ) else 0)) =
            (∑ f with (𝒟.ends f).2 = x, c f) + if w = x then 1 else 0 := by
          rw [Finset.sum_add_distrib, Finset.sum_ite_eq']
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, hhd]
        have h2 : (∑ f with (𝒟.ends f).1 = x, (c f + if f = e then (1 : ℤ) else 0)) =
            (∑ f with (𝒟.ends f).1 = x, c f) + if b = x then 1 else 0 := by
          rw [Finset.sum_add_distrib, Finset.sum_ite_eq']
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, htl]
        show (∑ f with (𝒟.ends f).2 = x, (c f + if f = e then (1 : ℤ) else 0)) -
          (∑ f with (𝒟.ends f).1 = x, (c f + if f = e then (1 : ℤ) else 0)) = _
        simp only [@eq_comm _ w x] at h1
        simp only [@eq_comm _ b x] at h2
        rw [h1, h2]
        split_ifs at hb ⊢ <;> linarith
      · intro θ hθ
        obtain ⟨_, hp2⟩ := hint θ hθ
        obtain ⟨_, hq2⟩ := hedge θ hθ
        refine ⟨primitive_on_skeleton 𝒟 hθ (mem_skeleton_trans 𝒟 hps hqs), ?_⟩
        rw [pathIntegral_trans_on_skeleton 𝒟 p q hθ hps hqs, hp2, hq, pathIntegral_cast, hq2]
        have : ∀ f, (((c f + if f = e then (1 : ℤ) else 0 : ℤ) : ℂ)) * 𝒟.edgeInt θ f =
            (c f : ℂ) * 𝒟.edgeInt θ f + if f = e then 𝒟.edgeInt θ f else 0 := by
          intro f; split_ifs <;> push_cast <;> ring
        simp only [this, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ·
      have h1 : 𝒟.vert w = 𝒟.vert (𝒟.ends e).1 := by rw [he]
      have h2 : 𝒟.vert b = 𝒟.vert (𝒟.ends e).2 := by rw [he]
      set q : Path (𝒟.vert b) (𝒟.vert w) := ((edgePath 𝒟 e).cast h1 h2).symm with hq
      have hqs : ∀ t, q t ∈ 𝒟.skeleton :=
        fun t => edgePath_mem_skeleton 𝒟 e (unitInterval.symm t)
      refine ⟨p.trans q, fun f => c f - (if f = e then 1 else 0), ?_, ?_, ?_, ?_⟩
      · exact mem_skeleton_trans 𝒟 hps hqs
      · intro f hf
        show c f - (if f = e then 1 else 0) = 0
        rw [hcT f hf, if_neg (fun h => hf (by rw [h]; exact he𝒯)), sub_zero]
      · intro x
        have hb := hbd x
        have hhd : (𝒟.ends e).2 = b := by rw [he]
        have htl : (𝒟.ends e).1 = w := by rw [he]
        have h1 : (∑ f with (𝒟.ends f).2 = x, (c f - if f = e then (1 : ℤ) else 0)) =
            (∑ f with (𝒟.ends f).2 = x, c f) - if b = x then 1 else 0 := by
          rw [Finset.sum_sub_distrib, Finset.sum_ite_eq']
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, hhd]
        have h2 : (∑ f with (𝒟.ends f).1 = x, (c f - if f = e then (1 : ℤ) else 0)) =
            (∑ f with (𝒟.ends f).1 = x, c f) - if w = x then 1 else 0 := by
          rw [Finset.sum_sub_distrib, Finset.sum_ite_eq']
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, htl]
        show (∑ f with (𝒟.ends f).2 = x, (c f - if f = e then (1 : ℤ) else 0)) -
          (∑ f with (𝒟.ends f).1 = x, (c f - if f = e then (1 : ℤ) else 0)) = _
        simp only [@eq_comm _ b x] at h1
        simp only [@eq_comm _ w x] at h2
        rw [h1, h2]
        split_ifs at hb ⊢ <;> linarith
      · intro θ hθ
        obtain ⟨_, hp2⟩ := hint θ hθ
        obtain ⟨_, hq2⟩ := hedge θ hθ
        refine ⟨primitive_on_skeleton 𝒟 hθ (mem_skeleton_trans 𝒟 hps hqs), ?_⟩
        have hsym : pathIntegral N θ q = -pathIntegral N θ (edgePath 𝒟 e) := by
          rw [hq, pathIntegral_symm_of_coeff_mem N _
            (fun t => (((edgePath 𝒟 e).cast h1 h2) t).mem_of_ord_nonneg
              (hθ _ (edgePath_mem_skeleton 𝒟 e t))), pathIntegral_cast]
        rw [pathIntegral_trans_on_skeleton 𝒟 p q hθ hps hqs, hp2, hsym, hq2]
        have : ∀ f, (((c f - if f = e then (1 : ℤ) else 0 : ℤ) : ℂ)) * 𝒟.edgeInt θ f =
            (c f : ℂ) * 𝒟.edgeInt θ f - if f = e then 𝒟.edgeInt θ f else 0 := by
          intro f; split_ifs <;> push_cast <;> ring
        simp only [this, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
        ring

end
end Dubon2026.SourceFunctionField.CellGeometry.OriginalEdgePaths
