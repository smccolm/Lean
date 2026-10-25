import Dubon2026.SourceRadialMeromorphicBoundaryValues
import Dubon2026.SourceRadialArcIndexInverse

/-! DUB-17/18 -> cover Abel converse -> meromorphic loop generation.
Boundary primitives with the same reversed differential integrand have a
constant jump on each paired arc, including its endpoints by continuity.
Adapted from the existing original-curve proof, originating in
anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2. -/
namespace Dubon2026.SourceFunctionField.CellGeometry.RadialMeromorphicPeriods
noncomputable section
open Set
variable {X R : Type*} [TopologicalSpace X]

/-- Exact reversed-arc constant jumps of the logarithmic boundary primitive. -/
def IsJumpH {A : Type*} [AddGroup A] (𝒟 : RadialCellDissection X) (H : 𝒟.ιC → ℝ → A)
    (J : 𝒟.ιE → A) : Prop :=
  ∀ e : 𝒟.ιE, ∃ ψ : ℝ → ℝ,
    StrictAntiOn ψ ((𝒟.cell (𝒟.arcOf (e, false)).1).R.arcIcc (𝒟.arcOf (e, false)).2) ∧
    ψ ((𝒟.cell (𝒟.arcOf (e, false)).1).R.φs (𝒟.arcOf (e, false)).2.castSucc) =
      (𝒟.cell (𝒟.arcOf (e, true)).1).R.φs (𝒟.arcOf (e, true)).2.succ ∧
    ψ ((𝒟.cell (𝒟.arcOf (e, false)).1).R.φs (𝒟.arcOf (e, false)).2.succ) =
      (𝒟.cell (𝒟.arcOf (e, true)).1).R.φs (𝒟.arcOf (e, true)).2.castSucc ∧
    (∀ t ∈ (𝒟.cell (𝒟.arcOf (e, false)).1).R.arcIcc (𝒟.arcOf (e, false)).2,
      (𝒟.cell (𝒟.arcOf (e, false)).1).bdry t = (𝒟.cell (𝒟.arcOf (e, true)).1).bdry (ψ t)) ∧
    ∀ t ∈ (𝒟.cell (𝒟.arcOf (e, false)).1).R.arcIcc (𝒟.arcOf (e, false)).2,
      H (𝒟.arcOf (e, true)).1 (ψ t) - H (𝒟.arcOf (e, false)).1 t = J e


theorem edge_pair_boundary {D : RadialCellDissection X}
    (H : D.ιC → ℝ → R → ℂ) (B : R → D.ιC → ℝ → ℂ)
    (hHc : ∀ r C, Continuous (fun s => H C s r))
    (hHd : ∀ r C (k : Fin (D.cell C).R.N) {s : ℝ},
      s ∈ Ioo ((D.cell C).R.φs k.castSucc) ((D.cell C).R.φs k.succ) →
      HasDerivAt (fun s => H C s r) (B r C s) s)
    (C C' : D.ιC) (k : Fin (D.cell C).R.N)
    (k' : Fin (D.cell C').R.N) (ψ : ℝ → ℝ)
    (hψanti : StrictAntiOn ψ ((D.cell C').R.arcIcc k'))
    (hψC1 : ContDiffOn ℝ 1 ψ ((D.cell C').R.arcIcc k'))
    (hψa : ψ ((D.cell C').R.φs k'.castSucc) = (D.cell C).R.φs k.succ)
    (hψb : ψ ((D.cell C').R.φs k'.succ) = (D.cell C).R.φs k.castSucc)
    (hrev : ∀ r {t d : ℝ},
      t ∈ Ioo ((D.cell C').R.φs k'.castSucc) ((D.cell C').R.φs k'.succ) →
      HasDerivAt ψ d t → B r C' t = B r C (ψ t) * d) :
    ∃ J : R → ℂ, ∀ t ∈ (D.cell C').R.arcIcc k', H C (ψ t) - H C' t = J := by
  set a' := (D.cell C').R.φs k'.castSucc with ha'
  set b' := (D.cell C').R.φs k'.succ with hb'
  have hab' : a' < b' := (D.cell C').R.hmono Fin.castSucc_lt_succ
  have harc' : (D.cell C').R.arcIcc k' = Icc a' b' := rfl

  have key : ∀ r, ∃ Jr : ℂ, ∀ t ∈ Icc a' b', H C (ψ t) r - H C' t r = Jr := by
    intro r
    set diff : ℝ → ℂ := fun t => H C (ψ t) r - H C' t r with hD
    have hDd : ∀ t ∈ Ioo a' b', HasDerivAt diff 0 t := by
      intro t ht
      have hψd : HasDerivAt ψ (deriv ψ t) t :=
        ((hψC1.differentiableOn one_ne_zero).differentiableAt
          (Icc_mem_nhds ht.1 ht.2)).hasDerivAt
      have htI : t ∈ (D.cell C').R.arcIcc k' := ⟨ht.1.le, ht.2.le⟩
      have hψt : ψ t ∈ Ioo ((D.cell C).R.φs k.castSucc) ((D.cell C).R.φs k.succ) := by
        constructor
        · rw [← hψb]
          exact hψanti htI (right_mem_Icc.mpr hab'.le) ht.2
        · rw [← hψa]
          exact hψanti (left_mem_Icc.mpr hab'.le) htI ht.1
      have hg := hrev r ht hψd
      have h1 : HasDerivAt (fun s => H C s r) (B r C (ψ t)) (ψ t) :=
        hHd r C k hψt
      have h1' : HasDerivAt (fun t => H C (ψ t) r)
          (((deriv ψ t : ℝ) : ℂ) * B r C (ψ t)) t := by
        have := h1.scomp t hψd
        rwa [Complex.real_smul] at this
      have h2 : HasDerivAt (fun t => H C' t r) (B r C' t) t :=
        hHd r C' k' ht
      have := h1'.sub h2
      rw [hg, mul_comm ((deriv ψ t : ℝ) : ℂ), sub_self] at this
      exact this
    have hDconst : ∀ t ∈ Ioo a' b', ∀ t₀ ∈ Ioo a' b', diff t = diff t₀ := by
      intro t ht t₀ ht₀
      exact (isOpen_Ioo (a := a') (b := b')).is_const_of_deriv_eq_zero isPreconnected_Ioo
        (fun u hu => (hDd u hu).differentiableAt.differentiableWithinAt)
        (fun u hu => (hDd u hu).deriv) ht ht₀
    set t₀ : ℝ := (a' + b') / 2 with ht₀
    have ht₀I : t₀ ∈ Ioo a' b' := ⟨by rw [ht₀]; linarith, by rw [ht₀]; linarith⟩
    have hDc : ContinuousOn diff (Icc a' b') := by
      refine ((hHc r C).comp_continuousOn
        (hψC1.continuousOn)).sub (hHc r C').continuousOn
    refine ⟨diff t₀, fun t ht => ?_⟩
    have heq : EqOn diff (fun _ => diff t₀) (Ioo a' b') := fun s hs => hDconst s hs t₀ ht₀I
    exact heq.of_subset_closure hDc continuousOn_const Ioo_subset_Icc_self
      (by rw [closure_Ioo hab'.ne]) ht
  choose Jr hJr using key
  exact ⟨Jr, fun t ht => funext fun r => hJr r t ht⟩

end
end Dubon2026.SourceFunctionField.CellGeometry.RadialMeromorphicPeriods
