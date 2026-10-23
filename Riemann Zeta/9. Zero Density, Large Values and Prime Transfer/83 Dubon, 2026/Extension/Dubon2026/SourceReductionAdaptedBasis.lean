import Dubon2026.SourceReductionIndependent
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Analytic.Order
import Mathlib.Tactic

/-! DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> higher symmetric-power
continuation -> arithmetic automorphy and residual association -> original
weight-two Frobenius/inertia -> actual good reduction -> genus comparison ->
preservation of dimensions under coefficient reduction. These lemmas serve
that finite-space dimension theorem; no genus or good-reduction claim is made.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2. Native polynomial monomial independence
replaces the external custom coefficient linear-combination equivalence. -/
namespace Dubon2026.SourceCurve.RegularProlongation
noncomputable section
open IsLocalRing
variable {L : Type*} [Field L] {A : ValuationSubring L}
variable {F : Type*} [Field F] [Algebra L F]
variable {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]

section adapted

variable (A)

theorem exists_adapted {V : Type*} [AddCommGroup V] [Module L V] {J : Type*} [Fintype J]
    (ℓ : J → V →ₗ[L] L) :
    ∀ (d : ℕ) (W : Submodule L V), (∀ v ∈ W, (∀ j, ℓ j v = 0) → v = 0) →
      Module.finrank L W = d →
      ∃ (b : Fin d → V) (c : Fin d → J), Function.Injective c ∧ (∀ a, b a ∈ W) ∧
        (∀ a j, ℓ j (b a) ∈ A) ∧ (∀ a a', ℓ (c a) (b a') = if a = a' then 1 else 0) := by
  classical
  intro d
  induction d with
  | zero =>
    intro W _ _
    exact ⟨Fin.elim0, Fin.elim0, fun a => Fin.elim0 a, fun a => Fin.elim0 a,
      fun a => Fin.elim0 a, fun a => Fin.elim0 a⟩
  | succ d ih =>
    intro W hinj hW
    haveI : Module.Finite L W := Module.finite_of_finrank_eq_succ hW

    have hWne : W ≠ ⊥ := by
      intro hbot
      rw [hbot, finrank_bot] at hW
      exact Nat.succ_ne_zero d hW.symm
    obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hWne
    have hex : ∃ j, ℓ j w ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hw0 (hinj w hwW hall)
    obtain ⟨j₁, hj₁⟩ := hex
    obtain ⟨j₀, -, hj₀, hcA, -⟩ :=
      exists_normalizer (A := A) Finset.univ (fun j => ℓ j w) (Finset.mem_univ j₁) hj₁

    set w' : V := (ℓ j₀ w)⁻¹ • w with hw'
    have hw'W : w' ∈ W := W.smul_mem _ hwW
    have hw'A : ∀ j, ℓ j w' ∈ A := fun j => by
      rw [hw', map_smul, smul_eq_mul]
      exact hcA j (Finset.mem_univ j)
    have hw'1 : ℓ j₀ w' = 1 := by
      rw [hw', map_smul, smul_eq_mul, inv_mul_cancel₀ hj₀]

    let φ : W →ₗ[L] L := (ℓ j₀).domRestrict W
    have hφsurj : Function.Surjective φ := by
      intro c
      refine ⟨⟨c • w', W.smul_mem _ hw'W⟩, ?_⟩
      simp [φ, hw'1]
    have hrange : Module.finrank L (LinearMap.range φ) = 1 := by
      rw [LinearMap.range_eq_top.mpr hφsurj, finrank_top, Module.finrank_self]
    have hsum := LinearMap.finrank_range_add_finrank_ker φ
    have hker : Module.finrank L (LinearMap.ker φ) = d := by
      rw [hrange, hW] at hsum
      omega
    set W' : Submodule L V := (LinearMap.ker φ).map W.subtype with hW'def
    have hW' : Module.finrank L W' = d := by
      rw [hW'def, Submodule.finrank_map_subtype_eq, hker]
    have hmemW' : ∀ v, v ∈ W' ↔ v ∈ W ∧ ℓ j₀ v = 0 := by
      intro v
      rw [hW'def, Submodule.mem_map]
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y.2, hy⟩
      · rintro ⟨hvW, hv0⟩
        exact ⟨⟨v, hvW⟩, hv0, rfl⟩
    have hinj' : ∀ v ∈ W', (∀ j, ℓ j v = 0) → v = 0 := fun v hv hall =>
      hinj v ((hmemW' v).mp hv).1 hall
    obtain ⟨b', c', hc'inj, hb'W', hb'A, hδ'⟩ := ih W' hinj' hW'
    have hb'W : ∀ a, b' a ∈ W := fun a => ((hmemW' _).mp (hb'W' a)).1
    have hb'0 : ∀ a, ℓ j₀ (b' a) = 0 := fun a => ((hmemW' _).mp (hb'W' a)).2
    have hc'ne : ∀ a, c' a ≠ j₀ := by
      intro a h
      have h1 := hδ' a a
      rw [if_pos rfl, h, hb'0] at h1
      exact zero_ne_one h1

    set b₀ : V := w' - ∑ a, ℓ (c' a) w' • b' a with hb₀
    have hb₀W : b₀ ∈ W :=
      W.sub_mem hw'W (W.sum_mem fun a _ => W.smul_mem _ (hb'W a))
    have hℓb₀ : ∀ j, ℓ j b₀ = ℓ j w' - ∑ a, ℓ (c' a) w' * ℓ j (b' a) := by
      intro j
      rw [hb₀, map_sub, map_sum]
      simp_rw [map_smul, smul_eq_mul]
    refine ⟨Fin.cons b₀ b', Fin.cons j₀ c', ?_, ?_, ?_, ?_⟩
    · rw [Fin.cons_injective_iff]
      refine ⟨?_, hc'inj⟩
      rintro ⟨a, ha⟩
      exact hc'ne a ha
    · intro a
      refine Fin.cases ?_ (fun a => ?_) a
      · simpa using hb₀W
      · simpa using hb'W a
    · intro a j
      refine Fin.cases ?_ (fun a => ?_) a
      · simp only [Fin.cons_zero]
        rw [hℓb₀]
        exact A.sub_mem (hw'A j)
          (A.toSubring.sum_mem fun a _ => A.toSubring.mul_mem (hw'A (c' a)) (hb'A a j))
      · simp only [Fin.cons_succ]
        exact hb'A a j
    · intro a a'
      refine Fin.cases ?_ (fun a => ?_) a <;> refine Fin.cases ?_ (fun a' => ?_) a'
      · simp only [Fin.cons_zero]
        rw [hℓb₀, hw'1]
        simp [hb'0]
      · simp only [Fin.cons_zero, Fin.cons_succ]
        rw [hb'0, if_neg (Fin.succ_ne_zero a').symm]
      · simp only [Fin.cons_zero, Fin.cons_succ]
        rw [hℓb₀, if_neg (Fin.succ_ne_zero a)]
        simp_rw [hδ' a, mul_ite, mul_one, mul_zero]
        rw [Finset.sum_ite_eq Finset.univ a, if_pos (Finset.mem_univ a), sub_self]
      · simp only [Fin.cons_succ]
        rw [hδ' a a']
        by_cases h : a = a'
        · subst h; simp
        · rw [if_neg h, if_neg (fun h' => h (Fin.succ_inj.mp h'))]

end adapted


end
end Dubon2026.SourceCurve.RegularProlongation
