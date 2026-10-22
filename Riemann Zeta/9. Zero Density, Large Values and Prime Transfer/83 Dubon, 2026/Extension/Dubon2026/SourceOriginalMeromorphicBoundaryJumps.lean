import Dubon2026.SourceOriginalMeromorphicBoundaryFTC
import Dubon2026.SourceOriginalReversedArcIntegrand

/-! DUB-17/18 -> original Abel-Jacobi -> meromorphic loop-period generation.
The logarithmic boundary primitives have constant jumps on each actual paired
arc. Reuse the proved reversed-arc integrand identity instead of rebuilding
the source coordinate derivative transport. Extend equality to the endpoints
by continuity, retaining the actual reversed parameterization.
Adapted from S_AlgebraicCurve_CellDissection_exists_int_pathIntegral_eq_sum_periods_add_sum_residues,
anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.MeromorphicPeriods
noncomputable section
open SourceCurve Set KaehlerDifferential
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable {N : ℕ} [NeZero N] {R : Type*}
local notation "F" => modularFunctionFieldOver N ℂ

/-- Exact reversed-arc constant jumps of the logarithmic boundary primitive. -/
def IsJumpH {A : Type*} [AddGroup A] (𝒟 : CellDissection N) (H : 𝒟.ιC → ℝ → A)
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


theorem edge_pair_hfun {𝒟 : CellDissection N} (S : Finset (Place ℂ F))
    (θ : R → Ω[F⁄ℂ]) {V : 𝒟.ιC → Set ℂ} {Ψ : R → 𝒟.ιC → ℂ → ℂ}
    (hP : RegPrimData S θ V Ψ) (C C' : 𝒟.ιC) (k : Fin (𝒟.cell C).R.N)
    (k' : Fin (𝒟.cell C').R.N) (ψ : ℝ → ℝ)
    (hψanti : StrictAntiOn ψ ((𝒟.cell C').R.arcIcc k'))
    (hψC1 : ContDiffOn ℝ 1 ψ ((𝒟.cell C').R.arcIcc k'))
    (hψa : ψ ((𝒟.cell C').R.φs k'.castSucc) = (𝒟.cell C).R.φs k.succ)
    (hψb : ψ ((𝒟.cell C').R.φs k'.succ) = (𝒟.cell C).R.φs k.castSucc)
    (hbd : ∀ t ∈ (𝒟.cell C').R.arcIcc k', (𝒟.cell C').bdry t = (𝒟.cell C).bdry (ψ t)) :
    ∃ J : R → ℂ, ∀ t ∈ (𝒟.cell C').R.arcIcc k', hfun S θ Ψ C (ψ t) - hfun S θ Ψ C' t = J := by
  set a' := (𝒟.cell C').R.φs k'.castSucc with ha'
  set b' := (𝒟.cell C').R.φs k'.succ with hb'
  have hab' : a' < b' := (𝒟.cell C').R.hmono Fin.castSucc_lt_succ
  have harc' : (𝒟.cell C').R.arcIcc k' = Icc a' b' := rfl

  have key : ∀ r, ∃ Jr : ℂ, ∀ t ∈ Icc a' b', hfun S θ Ψ C (ψ t) r - hfun S θ Ψ C' t r = Jr := by
    intro r
    set D : ℝ → ℂ := fun t => hfun S θ Ψ C (ψ t) r - hfun S θ Ψ C' t r with hD
    have hDd : ∀ t ∈ Ioo a' b', HasDerivAt D 0 t := by
      intro t ht
      have hψd : HasDerivAt ψ (deriv ψ t) t :=
        ((hψC1.differentiableOn one_ne_zero).differentiableAt
          (Icc_mem_nhds ht.1 ht.2)).hasDerivAt
      have htI : t ∈ (𝒟.cell C').R.arcIcc k' := ⟨ht.1.le, ht.2.le⟩
      have hψt : ψ t ∈ Ioo ((𝒟.cell C).R.φs k.castSucc) ((𝒟.cell C).R.φs k.succ) := by
        constructor
        · rw [← hψb]
          exact hψanti htI (right_mem_Icc.mpr hab'.le) ht.2
        · rw [← hψa]
          exact hψanti (left_mem_Icc.mpr hab'.le) htI ht.1
      have hg := (𝒟.cell C).reversed_arc_integrand (𝒟.cell C') k k' ψ
        hψanti hψa hψb hbd (θ r) ht hψd
      have h1 : HasDerivAt (fun s => hfun S θ Ψ C s r) ((𝒟.cell C).bdryIntegrand (θ r) (ψ t)) (ψ t) :=
        hasDerivAt_hfun S θ hP r C k hψt
      have h1' : HasDerivAt (fun t => hfun S θ Ψ C (ψ t) r)
          (((deriv ψ t : ℝ) : ℂ) * (𝒟.cell C).bdryIntegrand (θ r) (ψ t)) t := by
        have := h1.scomp t hψd
        rwa [Complex.real_smul] at this
      have h2 : HasDerivAt (fun t => hfun S θ Ψ C' t r) ((𝒟.cell C').bdryIntegrand (θ r) t) t :=
        hasDerivAt_hfun S θ hP r C' k' ht
      have := h1'.sub h2
      rw [hg, mul_comm ((deriv ψ t : ℝ) : ℂ), sub_self] at this
      exact this
    have hDconst : ∀ t ∈ Ioo a' b', ∀ t₀ ∈ Ioo a' b', D t = D t₀ := by
      intro t ht t₀ ht₀
      exact (isOpen_Ioo (a := a') (b := b')).is_const_of_deriv_eq_zero isPreconnected_Ioo
        (fun u hu => (hDd u hu).differentiableAt.differentiableWithinAt)
        (fun u hu => (hDd u hu).deriv) ht ht₀
    set t₀ : ℝ := (a' + b') / 2 with ht₀
    have ht₀I : t₀ ∈ Ioo a' b' := ⟨by rw [ht₀]; linarith, by rw [ht₀]; linarith⟩
    have hDc : ContinuousOn D (Icc a' b') := by
      refine ((continuous_hfun S θ hP r C).comp_continuousOn
        (hψC1.continuousOn)).sub (continuous_hfun S θ hP r C').continuousOn
    refine ⟨D t₀, fun t ht => ?_⟩
    have heq : EqOn D (fun _ => D t₀) (Ioo a' b') := fun s hs => hDconst s hs t₀ ht₀I
    exact heq.of_subset_closure hDc continuousOn_const Ioo_subset_Icc_self
      (by rw [closure_Ioo hab'.ne]) ht
  choose Jr hJr using key
  exact ⟨Jr, fun t ht => funext fun r => hJr r t ht⟩


theorem exists_isJumpH {𝒟 : CellDissection N} (S : Finset (Place ℂ F))
    (θ : R → Ω[F⁄ℂ]) {V : 𝒟.ιC → Set ℂ} {Ψ : R → 𝒟.ιC → ℂ → ℂ}
    (hP : RegPrimData S θ V Ψ) : ∃ J : 𝒟.ιE → R → ℂ, IsJumpH 𝒟 (hfun S θ Ψ) J := by
  have key : ∀ e : 𝒟.ιE, ∃ (Je : R → ℂ) (ψ : ℝ → ℝ),
      StrictAntiOn ψ ((𝒟.cell (𝒟.arcOf (e, false)).1).R.arcIcc (𝒟.arcOf (e, false)).2) ∧
      ψ ((𝒟.cell (𝒟.arcOf (e, false)).1).R.φs (𝒟.arcOf (e, false)).2.castSucc) =
        (𝒟.cell (𝒟.arcOf (e, true)).1).R.φs (𝒟.arcOf (e, true)).2.succ ∧
      ψ ((𝒟.cell (𝒟.arcOf (e, false)).1).R.φs (𝒟.arcOf (e, false)).2.succ) =
        (𝒟.cell (𝒟.arcOf (e, true)).1).R.φs (𝒟.arcOf (e, true)).2.castSucc ∧
      (∀ t ∈ (𝒟.cell (𝒟.arcOf (e, false)).1).R.arcIcc (𝒟.arcOf (e, false)).2,
        (𝒟.cell (𝒟.arcOf (e, false)).1).bdry t = (𝒟.cell (𝒟.arcOf (e, true)).1).bdry (ψ t)) ∧
      ∀ t ∈ (𝒟.cell (𝒟.arcOf (e, false)).1).R.arcIcc (𝒟.arcOf (e, false)).2,
        hfun S θ Ψ (𝒟.arcOf (e, true)).1 (ψ t) - hfun S θ Ψ (𝒟.arcOf (e, false)).1 t = Je := by
    intro e
    obtain ⟨ψ, hanti, hC1, ha, hb, hbd⟩ := 𝒟.arc_rev (𝒟.arcOf (e, true)).1 (𝒟.arcOf (e, true)).2
      (𝒟.arcOf (e, false)).1 (𝒟.arcOf (e, false)).2
      (by rw [CellDissection.side_arcOf, CellDissection.side_arcOf]) (by rw [CellDissection.side_arcOf]) (by rw [CellDissection.side_arcOf])
    obtain ⟨Je, hJe⟩ := edge_pair_hfun S θ hP _ _ _ _ ψ hanti hC1 ha hb hbd
    exact ⟨Je, ψ, hanti, ha, hb, hbd, hJe⟩
  choose J ψ h1 h2 h3 h4 h5 using key
  exact ⟨J, fun e => ⟨ψ e, h1 e, h2 e, h3 e, h4 e, h5 e⟩⟩

end
end Dubon2026.SourceFunctionField.CellGeometry.MeromorphicPeriods
