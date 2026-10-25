import Dubon2026.SourcePathAtlasJumpClosure
import Dubon2026.SourceOriginalWeilCoverCellPrimitiveLocalDifference
import Dubon2026.SourceOriginalWeilCoverPathIntegral
import Dubon2026.SourceRadialPrimitiveAtlas
import Dubon2026.SourceRadialCellJumpDifferences

/-! DUB-17/18 -> cover Abel converse -> regular loop generation. Adapt the
proved original-curve path-atlas comparison to the actual Kummer cover.
The unchanged generic atlas theorem, proved local primitive uniqueness and
actual cell intersection chains supply the result for arbitrary paths. -/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve Set Filter KaehlerDifferential
open scoped Topology
variable (N : ℕ) [NeZero N] (n : ℕ) [NeZero n]
variable (radicand : modularFunctionFieldOver N ℂ)
local notation "FF" => modularFunctionFieldOver N ℂ
local notation "EE" => Polynomial.SplittingField (Polynomial.X ^ n - Polynomial.C radicand : Polynomial FF)
variable (baseDivisor : Divisor ℂ (modularFunctionFieldOver N ℂ)) (hRadicand : radicand ≠ 0)
variable (hOrders : ∀ v : Place ℂ (modularFunctionFieldOver N ℂ), v.ord radicand = (n : ℤ) * baseDivisor v)
include baseDivisor hRadicand hOrders
local notation "PC" => placeChart N n radicand baseDivisor hRadicand hOrders
local notation "PF" => placeFamily N n radicand baseDivisor hRadicand hOrders
local notation "RD" => readDifferential N n radicand baseDivisor hRadicand hOrders
local notation "CF" => coverCoeffIn N n radicand baseDivisor hRadicand hOrders



open CellGeometry RadialDissectionPeriods

theorem cover_path_sub_mem_closure_jumps {κ : Type*} [Finite κ] :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    ∀ (𝒟 : RadialCellDissection (Place ℂ EE)) (η : κ → Ω[EE⁄ℂ])
      (V : 𝒟.ιC → Set ℂ) (Ψ : κ → 𝒟.ιC → ℂ → ℂ) (J : 𝒟.ιE → κ → ℂ),
      CoverPrimData N n radicand baseDivisor hRadicand hOrders 𝒟 η V Ψ → IsJump 𝒟 Ψ J →
      ∀ {P P' : Place ℂ EE} (δ : Path P P') (g : κ → unitInterval → ℂ),
      (∀ i, IsPrimitiveAlong N n radicand baseDivisor hRadicand hOrders (η i) δ (g i)) →
      (fun i => g i 1 - g i 0) - (gvec 𝒟 Ψ P' (cellOf 𝒟 P') - gvec 𝒟 Ψ P (cellOf 𝒟 P)) ∈
        AddSubgroup.closure (Set.range J) := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  letI := place_t2Space N n radicand baseDivisor hRadicand hOrders
  intro 𝒟 η V Ψ J hP hJ P P' δ g hg
  set Λ := AddSubgroup.closure (Set.range J) with hΛ
  have key := CellGeometry.DissectionPeriods.sub_sub_mem_of_atlas Λ (fun x : Place ℂ EE => (badCarrierSet 𝒟 x)ᶜ) (Gchart 𝒟 Ψ)
    ?_ δ.continuous (fun t i => g i t) ?_ (j₀ := P) (j₁ := P')
    (by rw [δ.source]; exact not_mem_badCarrierSet_self 𝒟 P)
    (by rw [δ.target]; exact not_mem_badCarrierSet_self 𝒟 P')
  · have h0 : Gchart 𝒟 Ψ P (δ 0) = gvec 𝒟 Ψ P (cellOf 𝒟 P) := by
      rw [δ.source]; simp only [Gchart]; abel
    have h1 : Gchart 𝒟 Ψ P' (δ 1) = gvec 𝒟 Ψ P' (cellOf 𝒟 P') := by
      rw [δ.target]; simp only [Gchart]; abel
    rw [h0, h1] at key
    exact key
  ·
    rintro x x' y ⟨hy, hy'⟩
    have hcy : x ∈ (𝒟.cell (cellOf 𝒟 y)).carrier :=
      mem_carrier_of_not_mem_badCarrierSet 𝒟 hy (mem_cellOf 𝒟 y)
    have hcy' : x' ∈ (𝒟.cell (cellOf 𝒟 y)).carrier :=
      mem_carrier_of_not_mem_badCarrierSet 𝒟 hy' (mem_cellOf 𝒟 y)
    have h1 := gvec_sub_mem hJ (mem_cellOf 𝒟 x) hcy
    have h2 := gvec_sub_mem hJ hcy' (mem_cellOf 𝒟 x')
    have : Gchart 𝒟 Ψ x y - Gchart 𝒟 Ψ x' y =
        (gvec 𝒟 Ψ x (cellOf 𝒟 x) - gvec 𝒟 Ψ x (cellOf 𝒟 y)) +
          (gvec 𝒟 Ψ x' (cellOf 𝒟 y) - gvec 𝒟 Ψ x' (cellOf 𝒟 x')) := by
      simp only [Gchart]; abel
    rw [this]
    exact add_mem h1 h2
  ·
    intro t₀
    refine ⟨δ t₀, (isClosed_badCarrierSet 𝒟 (δ t₀)).isOpen_compl, not_mem_badCarrierSet_self 𝒟 (δ t₀), ?_⟩

    have hev1 : ∀ᶠ t in 𝓝 t₀, δ t ∈ (badCarrierSet 𝒟 (δ t₀))ᶜ :=
      δ.continuous.continuousAt.preimage_mem_nhds
        ((isClosed_badCarrierSet 𝒟 (δ t₀)).isOpen_compl.mem_nhds (not_mem_badCarrierSet_self 𝒟 (δ t₀)))
    have hev2 : ∀ᶠ t in 𝓝 t₀, ∀ E : 𝒟.ιC, (δ t₀) ∈ (𝒟.cell E).carrier →
        gvec 𝒟 Ψ (δ t) E - gvec 𝒟 Ψ (δ t) (cellOf 𝒟 (δ t₀)) = gvec 𝒟 Ψ (δ t₀) E - gvec 𝒟 Ψ (δ t₀) (cellOf 𝒟 (δ t₀)) := by
      haveI : Fintype 𝒟.ιC := 𝒟.fintypeC
      refine Filter.eventually_all.2 fun E => ?_
      by_cases hE : (δ t₀) ∈ (𝒟.cell E).carrier
      · have := cover_eventually_gvec_sub N n radicand baseDivisor hRadicand hOrders 𝒟 η V Ψ hP hE (mem_cellOf 𝒟 (δ t₀))
        have h' := δ.continuous.continuousAt (x := t₀) |>.eventually this
        filter_upwards [h'] with t ht _
        exact ht
      · exact Filter.Eventually.of_forall fun t h => absurd h hE
    have hG : ∀ᶠ t in 𝓝 t₀, Gchart 𝒟 Ψ (δ t₀) (δ t) = gvec 𝒟 Ψ (δ t) (cellOf 𝒟 (δ t₀)) := by
      filter_upwards [hev1, hev2] with t ht1 ht2
      have hE : (δ t₀) ∈ (𝒟.cell (cellOf 𝒟 (δ t))).carrier :=
        mem_carrier_of_not_mem_badCarrierSet 𝒟 ht1 (mem_cellOf 𝒟 (δ t))
      have := ht2 _ hE
      simp only [Gchart]
      linear_combination this

    have hsrc : (δ t₀) ∈ (𝒟.cell (cellOf 𝒟 (δ t₀))).ζ.source ∧
        (𝒟.cell (cellOf 𝒟 (δ t₀))).ζ (δ t₀) ∈ V (cellOf 𝒟 (δ t₀)) := by
      have hgen : ∀ (E : 𝒟.ιC) (y : Place ℂ EE), y ∈ (𝒟.cell E).carrier →
          y ∈ (𝒟.cell E).ζ.source ∧ (𝒟.cell E).ζ y ∈ V E := by
        rintro E y ⟨z, hz, rfl⟩
        have ht := (𝒟.cell E).hKt hz
        exact ⟨(𝒟.cell E).ζ.map_target ht, by rw [(𝒟.cell E).ζ.right_inv ht]; exact hP.2.2.1 E hz⟩
      exact hgen _ _ (mem_cellOf 𝒟 (δ t₀))
    have hcomp : ∀ i, ∃ c : ℂ, ∀ᶠ t in 𝓝 t₀, g i t = Ψ i (cellOf 𝒟 (δ t₀)) ((𝒟.cell (cellOf 𝒟 (δ t₀))).ζ (δ t)) + c := by
      intro i
      obtain ⟨Φ₁, hΦ₁, hgΦ⟩ := hg i t₀
      rw [placeChart_self] at hΦ₁
      have hcoord := hP.1 (cellOf 𝒟 (δ t₀)) (δ t₀) hsrc.1
      have hη := (mem_cover_regularDifferentials_iff N n radicand (η i)).mp (hP.2.2.2.2 i) (δ t₀)
      have hΦ := cover_hasDerivAt_coordPrimitive N n radicand baseDivisor hRadicand hOrders
        (𝒟.cell (cellOf 𝒟 (δ t₀))).ζ hsrc.1 hcoord.1 hcoord.2
        (hP.2.1 (cellOf 𝒟 (δ t₀))) hsrc.2 (hP.2.2.2.1 i (cellOf 𝒟 (δ t₀))) hη
      have hdiff := cover_eventually_coordPrimitive_sub_eq N n radicand baseDivisor hRadicand hOrders hΦ₁ hΦ
      refine ⟨Φ₁ 0 - Ψ i (cellOf 𝒟 (δ t₀)) ((𝒟.cell (cellOf 𝒟 (δ t₀))).ζ (δ t₀)), ?_⟩
      have h1 := δ.continuous.continuousAt (x := t₀) |>.eventually hdiff
      have h2 : ∀ᶠ t in 𝓝 t₀, δ t ∈ (PC (δ t₀)).source :=
        δ.continuous.continuousAt.preimage_mem_nhds
          (placeChart_source_mem_nhds N n radicand baseDivisor hRadicand hOrders (δ t₀))
      filter_upwards [h1, h2, hgΦ] with t ht hts hgt
      rw [hgt]
      change Φ₁ (PC (δ t₀) (δ t)) = _
      have hback : PF (δ t₀) (PC (δ t₀) (δ t)) = δ t := (PC (δ t₀)).left_inv hts
      simp only [Function.comp_apply, hback,
        (place_spec N n radicand baseDivisor hRadicand hOrders (δ t₀)).2.1] at ht
      linear_combination ht
    choose c hc using hcomp
    refine ⟨c, ?_⟩
    filter_upwards [hG, Filter.eventually_all.2 hc] with t htG htc
    rw [htG]
    funext i
    exact htc i
end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
