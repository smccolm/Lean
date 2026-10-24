import Mathlib

/-! DUB-17/18 -> Picard torsion injectivity -> Kummer power lifting ->
sum-of-genera inequality -> dimensions of simultaneous residue chart spaces.
This finite-window linear algebra supplies the eventual comparison needed
for pole spaces on the coordinate and inverse-coordinate charts. Chart
generation, monic torsion and constant intersection remain separate inputs
to discharge in the actual curve argument. Adapted from Apache-2.0 FLT,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2. Native eventual Fitting
disjointness replaces the external auxiliary stabilization proof. -/
namespace Dubon2026.SourceCurve.RegularProlongation.JointChartLinearAlgebra
noncomputable section
open Submodule LinearMap Module
variable {k : Type*} [Field k] {W : Type*} [AddCommGroup W] [Module k W]

theorem map_pow_le {ψ : W →ₗ[k] W} {S : Submodule k W} (hS : S.map ψ ≤ S) :
    ∀ M : ℕ, S.map (ψ^M) ≤ S := by
  intro M; induction M with
  | zero => rw [pow_zero, show (1:W→ₗ[k]W) = LinearMap.id from rfl, Submodule.map_id]
  | succ n ih =>
    rw [pow_succ, show (ψ^n * ψ : W→ₗ[k]W) = (ψ^n).comp ψ from rfl, Submodule.map_comp]
    exact (Submodule.map_mono hS).trans ih

theorem mem_of_pow_map {ψ : W →ₗ[k] W} {S : Submodule k W} (hS : S.map ψ ≤ S)
    (M : ℕ) {x : W} (hx : x ∈ S) : (ψ^M) x ∈ S :=
  map_pow_le hS M ⟨x, hx, rfl⟩

/-- Endomorphism induced on a stable chart quotient. -/
def barEnd (φ : W →ₗ[k] W) (P B : Submodule k W)
    (hP : P.map φ ≤ P) (hB : B.map φ ≤ B) :
    (B ⧸ P.comap B.subtype) →ₗ[k] (B ⧸ P.comap B.subtype) :=
  (P.comap B.subtype).mapQ (P.comap B.subtype) (φ.restrict (fun x hx => hB ⟨x, hx, rfl⟩))
    (fun x hx => by simp only [mem_comap, coe_subtype] at hx ⊢; exact hP ⟨(x : W), hx, rfl⟩)

theorem finiteDimensional_quot_of_monicTorsion
    (φ : W →ₗ[k] W) (P B : Submodule k W)
    (hP : P.map φ ≤ P) (hB : B.map φ ≤ B)
    (S : Submodule k W) (hSB : S ≤ B) [FiniteDimensional k S]
    (hgen : B ≤ ⨆ j : ℕ, S.map (φ ^ j))
    (htor : ∀ y ∈ B, ∃ c : Polynomial k, c.Monic ∧ Polynomial.aeval φ c y ∈ P) :
    FiniteDimensional k (B ⧸ P.comap B.subtype) := by
  classical
  have key : ∀ (s : W) (c : Polynomial k), c.Monic → Polynomial.aeval φ c s ∈ P →
      ∀ m, (φ^m) s ∈
        P ⊔ Submodule.span k ((Finset.range c.natDegree).image (fun j => (φ^j) s)) := by
    intro s c hc hcs
    set d := c.natDegree with hd
    have happ : (φ^d) s + ∑ j ∈ Finset.range d, c.coeff j • (φ^j) s
        = (Polynomial.aeval φ c) s := by
      conv_rhs => rw [hc.as_sum]
      simp only [map_add, map_pow, Polynomial.aeval_X, map_sum, map_mul, Polynomial.aeval_C,
        LinearMap.add_apply, LinearMap.sum_apply, Module.End.mul_apply,
        Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, Module.End.one_apply]
      simp only [← hd]
    have hd_expr : (φ^d) s =
        (Polynomial.aeval φ c) s - ∑ j ∈ Finset.range d, c.coeff j • (φ^j) s :=
      eq_sub_of_add_eq happ
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      rcases lt_or_ge m d with hm | hm
      · exact Submodule.mem_sup_right
          (Submodule.subset_span (Finset.mem_image.mpr ⟨m, Finset.mem_range.mpr hm, rfl⟩))
      · have hsplit : (φ^m) s = (φ^(m-d)) ((φ^d) s) := by
          have h : (φ^((m-d)+d)) s = (φ^(m-d)) ((φ^d) s) := by rw [pow_add]; rfl
          rwa [Nat.sub_add_cancel hm] at h
        rw [hsplit, hd_expr, map_sub, map_sum]
        refine sub_mem ?_ (Submodule.sum_mem _ fun j hj => ?_)
        · exact Submodule.mem_sup_left (mem_of_pow_map hP (m-d) hcs)
        · rw [map_smul]
          refine Submodule.smul_mem _ _ ?_
          have hlt : (m - d) + j < m := by
            have := Finset.mem_range.mp hj; omega
          have heq : (φ^(m-d)) ((φ^j) s) = (φ^((m-d)+j)) s := by rw [pow_add]; rfl
          rw [heq]; exact ih _ hlt
  have hSfg : S.FG := by
    have h1 : (⊤ : Submodule k ↥S).FG := Module.finite_def.mp inferInstance
    have h2 : S = (⊤ : Submodule k ↥S).map S.subtype := by
      rw [Submodule.map_top, Submodule.range_subtype]
    rw [h2]; exact h1.map _
  obtain ⟨σ, hσ⟩ := hSfg
  have hσB : ∀ s ∈ σ, s ∈ B := fun s hs => hSB (hσ ▸ Submodule.subset_span hs)
  choose! c hcMon hcP using fun s (hs : s ∈ σ) => htor s (hσB s hs)
  let Tof : W → Submodule k W := fun s =>
    Submodule.span k ((Finset.range (c s).natDegree).image (fun j => (φ^j) s))
  let T : Submodule k W := σ.sup Tof
  haveI hTfd : FiniteDimensional k ↥T :=
    Module.Finite.iff_fg.mpr (Submodule.fg_finset_sup σ Tof fun s _ =>
      Submodule.fg_span (Finset.image _ _).finite_toSet)
  have hTB : T ≤ B := Finset.sup_le fun s hs => Submodule.span_le.mpr fun x hx => by
    simp only [Finset.coe_image, Set.mem_image] at hx
    obtain ⟨j, _, rfl⟩ := hx
    exact mem_of_pow_map hB j (hσB s hs)
  have hBPT : B ≤ P ⊔ T := by
    refine hgen.trans (iSup_le fun j => ?_)
    rw [← hσ, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨s, hs, rfl⟩
    exact (sup_le_sup_left (Finset.le_sup hs : Tof s ≤ T) P)
      (key s (c s) (hcMon s hs) (hcP s hs) j)
  haveI : FiniteDimensional k ↥(T.comap B.subtype) :=
    LinearEquiv.finiteDimensional (Submodule.comapSubtypeEquivOfLe hTB).symm
  refine Module.Finite.of_surjective
    ((P.comap B.subtype).mkQ ∘ₗ (T.comap B.subtype).subtype) ?_
  intro q
  obtain ⟨⟨b, hbB⟩, rfl⟩ := (P.comap B.subtype).mkQ_surjective q
  obtain ⟨p, hpP, t, htT, hbpt⟩ := Submodule.mem_sup.mp (hBPT hbB)
  have htB : t ∈ B := hTB htT
  refine ⟨⟨⟨t, htB⟩, Submodule.mem_comap.mpr htT⟩, ?_⟩
  simp only [LinearMap.comp_apply, Submodule.subtype_apply, Submodule.mkQ_apply]
  refine (Submodule.Quotient.eq _).mpr ?_
  refine Submodule.mem_comap.mpr ?_
  show (t : W) - b ∈ P
  have hneg : (t : W) - b = -p := by rw [← hbpt]; abel
  rw [hneg]; exact P.neg_mem hpP


end
end Dubon2026.SourceCurve.RegularProlongation.JointChartLinearAlgebra
