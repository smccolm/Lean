import Dubon2026.SourceJointChartQuotientFinite

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

variable (φ : W ≃ₗ[k] W) (P B P' B' : Submodule k W)

theorem aux_symm_mul : (φ.symm : W →ₗ[k] W) * (φ : W →ₗ[k] W) = 1 :=
  LinearMap.ext fun x => φ.symm_apply_apply x

theorem aux_mul_symm : (φ : W →ₗ[k] W) * (φ.symm : W →ₗ[k] W) = 1 :=
  LinearMap.ext fun x => φ.apply_symm_apply x

theorem pow_symm_pow (M : ℕ) (x : W) :
    ((φ.symm : W →ₗ[k] W) ^ M) (((φ : W →ₗ[k] W) ^ M) x) = x := by
  have hcomm : Commute (φ.symm : W →ₗ[k] W) (φ : W →ₗ[k] W) :=
    (aux_symm_mul φ).trans (aux_mul_symm φ).symm
  have h1 : ((φ.symm : W →ₗ[k] W) ^ M) * ((φ : W →ₗ[k] W) ^ M) = 1 := by
    rw [← hcomm.mul_pow, aux_symm_mul, one_pow]
  calc ((φ.symm:W→ₗ[k]W)^M) (((φ:W→ₗ[k]W)^M) x)
      = (((φ.symm:W→ₗ[k]W)^M) * ((φ:W→ₗ[k]W)^M)) x := rfl
    _ = (1 : W →ₗ[k] W) x := by rw [h1]
    _ = x := rfl

theorem pow_pow_symm (M : ℕ) (x : W) :
    ((φ : W →ₗ[k] W) ^ M) (((φ.symm : W →ₗ[k] W) ^ M) x) = x := by
  have := pow_symm_pow φ.symm M x; simpa using this

theorem barEnd_mkQ (ψ : W →ₗ[k] W) (P B : Submodule k W)
    (hP : P.map ψ ≤ P) (hB : B.map ψ ≤ B) (x : W) (hx : x ∈ B) :
    barEnd ψ P B hP hB ((P.comap B.subtype).mkQ ⟨x, hx⟩) =
      (P.comap B.subtype).mkQ ⟨ψ x, hB ⟨x, hx, rfl⟩⟩ := by
  simp only [barEnd, Submodule.mapQ_apply, Submodule.mkQ_apply]
  rfl

theorem barEnd_pow_mkQ (ψ : W →ₗ[k] W) (P B : Submodule k W)
    (hP : P.map ψ ≤ P) (hB : B.map ψ ≤ B) (M : ℕ) (x : W) (hx : x ∈ B) :
    ((barEnd ψ P B hP hB) ^ M) ((P.comap B.subtype).mkQ ⟨x, hx⟩) =
      (P.comap B.subtype).mkQ ⟨(ψ^M) x, mem_of_pow_map hB M hx⟩ := by
  induction M with
  | zero => simp only [pow_zero]; rfl
  | succ n ih =>
    have hstep : ((barEnd ψ P B hP hB) ^ (n+1)) ((P.comap B.subtype).mkQ ⟨x, hx⟩)
        = (barEnd ψ P B hP hB) (((barEnd ψ P B hP hB) ^ n) ((P.comap B.subtype).mkQ ⟨x, hx⟩)) := by
      rw [pow_succ']; rfl
    have hval : ψ ((ψ^n) x) = (ψ^(n+1)) x := by rw [pow_succ']; rfl
    rw [hstep, ih, barEnd_mkQ]
    exact congrArg _ (Subtype.ext hval)

theorem symm_pow_mem_of_mem_map (M : ℕ) (x : W) (hx : x ∈ B'.map ((φ : W →ₗ[k] W) ^ M)) :
    ((φ.symm : W →ₗ[k] W) ^ M) x ∈ B' := by
  obtain ⟨y, hyB', hy⟩ := hx; rw [← hy, pow_symm_pow]; exact hyB'

/-- Maps a finite chart intersection to the product of the chart quotients. -/
def Psi (M : ℕ) :
    ↥(B ⊓ B'.map ((φ : W →ₗ[k] W) ^ M)) →ₗ[k]
      (B ⧸ P.comap B.subtype) × (B' ⧸ P'.comap B'.subtype) :=
  LinearMap.prod
    ((P.comap B.subtype).mkQ ∘ₗ Submodule.inclusion inf_le_left)
    ((P'.comap B'.subtype).mkQ ∘ₗ
      { toFun := fun x => ⟨((φ.symm : W →ₗ[k] W) ^ M) x.1, symm_pow_mem_of_mem_map φ B' M x.1 x.2.2⟩
        map_add' := fun x y => by ext; simp
        map_smul' := fun c x => by ext; simp })

theorem ker_Psi_eq (M : ℕ) :
    LinearMap.ker (Psi φ P B P' B' M) =
      (P ⊓ P'.map ((φ : W →ₗ[k] W) ^ M)).comap
        (B ⊓ B'.map ((φ : W →ₗ[k] W) ^ M)).subtype := by
  ext ⟨x, hx⟩
  have hxB : x ∈ B := hx.1
  have hxB' : x ∈ B'.map ((φ : W →ₗ[k] W) ^ M) := hx.2
  constructor
  · intro hker
    have h1 : (P.comap B.subtype).mkQ ⟨x, hxB⟩ = 0 := congrArg Prod.fst hker
    have h2 : (P'.comap B'.subtype).mkQ
        ⟨((φ.symm:W→ₗ[k]W)^M) x, symm_pow_mem_of_mem_map φ B' M x hxB'⟩ = 0 :=
      congrArg Prod.snd hker
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h1 h2
    simp only [mem_comap, coe_subtype] at h1 h2 ⊢
    exact ⟨h1, ((φ.symm:W→ₗ[k]W)^M) x, h2, pow_pow_symm φ M x⟩
  · intro hmem
    simp only [mem_comap, coe_subtype, mem_inf] at hmem
    obtain ⟨h1, y, hyP', hy⟩ := hmem
    have hy' : ((φ.symm:W→ₗ[k]W)^M) x = y := by rw [← hy, pow_symm_pow]
    show Psi φ P B P' B' M ⟨x, hx⟩ = 0
    ext
    · show (P.comap B.subtype).mkQ ⟨x, hxB⟩ = 0
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]; exact h1
    · show (P'.comap B'.subtype).mkQ ⟨_, _⟩ = 0
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      simp only [mem_comap, coe_subtype, hy']; exact hyP'

theorem Psi_fst (M : ℕ) (z : ↥(B ⊓ B'.map ((φ:W→ₗ[k]W)^M))) :
    (Psi φ P B P' B' M z).1 = (P.comap B.subtype).mkQ ⟨z.1, z.2.1⟩ := rfl

theorem Psi_snd (M : ℕ) (z : ↥(B ⊓ B'.map ((φ:W→ₗ[k]W)^M))) :
    (Psi φ P B P' B' M z).2 =
      (P'.comap B'.subtype).mkQ ⟨((φ.symm:W→ₗ[k]W)^M) z.1,
        symm_pow_mem_of_mem_map φ B' M z.1 z.2.2⟩ := rfl

theorem range_Psi_superset
    (hP : P.map (φ : W →ₗ[k] W) ≤ P) (hB : B.map (φ : W →ₗ[k] W) ≤ B)
    (hP' : P'.map (φ.symm : W →ₗ[k] W) ≤ P') (hB' : B'.map (φ.symm : W →ₗ[k] W) ≤ B')
    (M : ℕ) :
    (LinearMap.range (Psi φ P B P' B' 0)).map
        (LinearMap.prodMap ((barEnd (φ : W →ₗ[k] W) P B hP hB) ^ M) LinearMap.id) ⊔
      (LinearMap.range (Psi φ P B P' B' 0)).map
        (LinearMap.prodMap LinearMap.id ((barEnd (φ.symm : W →ₗ[k] W) P' B' hP' hB') ^ M))
      ≤ LinearMap.range (Psi φ P B P' B' M) := by
  have hmap0 : B'.map ((φ:W→ₗ[k]W)^(0:ℕ)) = B' := by
    rw [pow_zero, show (1:W→ₗ[k]W) = LinearMap.id from rfl, Submodule.map_id]
  apply sup_le
  · rintro _ ⟨_, ⟨⟨x, hx⟩, rfl⟩, rfl⟩
    have hx0 : x ∈ B := hx.1
    have hx0' : x ∈ B' := hmap0 ▸ hx.2
    have hφMx : ((φ:W→ₗ[k]W)^M) x ∈ B := mem_of_pow_map hB M hx0
    refine ⟨⟨((φ:W→ₗ[k]W)^M) x, hφMx, x, hx0', rfl⟩, Prod.ext ?_ ?_⟩
    · rw [Psi_fst, LinearMap.prodMap_apply, Psi_fst]
      exact (barEnd_pow_mkQ (φ:W→ₗ[k]W) P B hP hB M x hx.1).symm
    · rw [Psi_snd, LinearMap.prodMap_apply, Psi_snd, LinearMap.id_apply]
      refine congrArg _ (Subtype.ext ?_)
      show ((φ.symm:W→ₗ[k]W)^M) (((φ:W→ₗ[k]W)^M) x) = ((φ.symm:W→ₗ[k]W)^0) x
      rw [pow_symm_pow, pow_zero]; rfl
  · rintro _ ⟨_, ⟨⟨x, hx⟩, rfl⟩, rfl⟩
    have hx0 : x ∈ B := hx.1
    have hx0' : x ∈ B' := hmap0 ▸ hx.2
    have hφMx' : ((φ.symm:W→ₗ[k]W)^M) x ∈ B' := mem_of_pow_map hB' M hx0'
    have hxM : x ∈ B'.map ((φ:W→ₗ[k]W)^M) :=
      ⟨((φ.symm:W→ₗ[k]W)^M) x, hφMx', pow_pow_symm φ M x⟩
    refine ⟨⟨x, hx0, hxM⟩, Prod.ext ?_ ?_⟩
    · rw [Psi_fst, LinearMap.prodMap_apply, Psi_fst, LinearMap.id_apply]
    · rw [Psi_snd, LinearMap.prodMap_apply, Psi_snd]
      have hval0 : ((φ.symm:W→ₗ[k]W)^0) x = x := by rw [pow_zero]; rfl
      have hxval : (⟨((φ.symm:W→ₗ[k]W)^0) x,
          symm_pow_mem_of_mem_map φ B' 0 x hx.2⟩ : ↥B') = ⟨x, hx0'⟩ :=
        Subtype.ext hval0
      rw [congrArg (P'.comap B'.subtype).mkQ hxval]
      exact (barEnd_pow_mkQ (φ.symm:W→ₗ[k]W) P' B' hP' hB' M x hx0').symm


end
end Dubon2026.SourceCurve.RegularProlongation.JointChartLinearAlgebra
