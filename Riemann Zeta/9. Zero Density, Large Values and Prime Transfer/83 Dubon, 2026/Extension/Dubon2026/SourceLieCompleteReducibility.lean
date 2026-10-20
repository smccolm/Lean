/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Algebra.Lie.Semisimple.Defs

import Mathlib.Algebra.Lie.CartanCriterion
import Mathlib.Algebra.Lie.Quotient
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-!
# Source-chain Lie complete reducibility

Adapted from facebookresearch/atlas-lean at b619e3f1a69ea6a0e900bc348f803e4c5d53bba4,
MathlibExt/Algebra/Lie/LeviDecomposition.lean, original lines 1-822.
Modified for this project: retain only the complete-reducibility dependency closure,
use the local namespace and pinned imports, and defer the unrelated Levi decomposition.
Original copyright and full license are retained in the adjacent external-source archive.

Exact dependency: DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> higher symmetric-power
automorphy -> BLGG/Geraghty original coefficient modules -> characteristic-zero
irreducibility. This proves invariant complements for finite-dimensional semisimple
Lie-algebra modules. Differentiation of the original induced action, recovery of
group-stability, and the actual irreducibility consumer remain to be constructed.
-/


namespace Dubon2026

open LieAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

private theorem levi_sum_repr
    {K V ι : Type*} [Semiring K] [AddCommMonoid V] [Module K V]
    [Fintype ι] (b : Module.Basis ι K V) (x : V) :
    ∑ i, b.repr x i • b i = x := by
  apply b.repr.injective
  ext j
  simp

private theorem levi_repr_eq_dual
    {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Finite ι] [DecidableEq ι] {B : LinearMap.BilinForm K V}
    (hB : B.Nondegenerate) (b : Module.Basis ι K V) (x : V) (i : ι) :
    b.repr x i = B (B.dualBasis hB b i) x := by
  let _ := Fintype.ofFinite ι
  conv_rhs => rw [← levi_sum_repr b x]
  rw [map_sum]
  simp_rw [map_smul]
  simp_rw [LinearMap.BilinForm.apply_dualBasis_left hB b]
  simp

private noncomputable def leviTraceKernel
    {K L M : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
    [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
    [Module.Finite K M] : LieIdeal K L where
  __ := LinearMap.ker (LieModule.traceForm K L M)
  lie_mem := by
    intro x y hy
    change LieModule.traceForm K L M ⁅x, y⁆ = 0
    ext z
    rw [LieModule.traceForm_apply_lie_apply']
    have h := LinearMap.congr_fun (LinearMap.mem_ker.mp hy) (⁅x, z⁆ : L)
    simpa using h

private theorem leviTraceKernel_isSolvable
    {K L M : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
    [Module.Finite K L] [AddCommGroup M] [Module K M] [LieRingModule L M]
    [LieModule K L M] [Module.Finite K M] [LieModule.IsFaithful K L M] :
    LieAlgebra.IsSolvable (leviTraceKernel (K := K) (L := L) (M := M)) := by
  let I := leviTraceKernel (K := K) (L := L) (M := M)
  change LieAlgebra.IsSolvable I
  have htf : LieModule.traceForm K I M = 0 := by
    ext x y
    change LieModule.traceForm K L M x.1 y.1 = 0
    exact LinearMap.congr_fun (LinearMap.mem_ker.mp x.2) y
  let D' := LieAlgebra.derivedSeries K I 1
  have hnil : LieModule.IsNilpotent D' M :=
    LieModule.isNilpotent_derivedSeries_of_traceForm_eq_zero htf
  let D : LieIdeal K L := ⁅I, I⁆
  have hnil' (x : D) : IsNilpotent (LieModule.toEnd K D M x) := by
    have hxI : x.1 ∈ I := LieSubmodule.lie_le_left I I x.2
    have hxD' : (⟨x.1, hxI⟩ : I) ∈ LieAlgebra.derivedSeries K I 1 := by
      rw [LieIdeal.derivedSeries_eq_derivedSeriesOfIdeal_comap]
      exact x.2
    let x' : D' := ⟨⟨x.1, hxI⟩, hxD'⟩
    have hx := (LieModule.isNilpotent_iff_forall' (R := K)).mp hnil x'
    change IsNilpotent (LieModule.toEnd K L M x.1)
    change IsNilpotent (LieModule.toEnd K L M x'.1.1) at hx
    simpa [x'] using hx
  let φ := LieModule.toEnd K D M
  have hrange : LieRing.IsNilpotent φ.range := by
    rw [LieAlgebra.isNilpotent_iff_forall (R := K) (L := φ.range)]
    rintro ⟨_, ⟨x, rfl⟩⟩
    apply LieAlgebra.isNilpotent_ad_of_isNilpotent
    exact hnil' x
  let _ : LieRing.IsNilpotent φ.range := hrange
  have hφ : Function.Injective φ.rangeRestrict := by
    intro x y hxy
    apply Subtype.ext
    apply LieModule.IsFaithful.injective_toEnd (R := K) (L := L) (M := M)
    exact congr_arg Subtype.val hxy
  have hD : LieRing.IsNilpotent D := hφ.lieAlgebra_isNilpotent
  let _ : LieRing.IsNilpotent D := hD
  let _ : LieAlgebra.IsSolvable D := inferInstance
  obtain ⟨k, hk⟩ := LieAlgebra.IsSolvable.solvable K D
  rw [LieIdeal.derivedSeries_eq_bot_iff (R := K) (L := L) D] at hk
  change LieAlgebra.derivedSeriesOfIdeal K L k ⁅I, I⁆ = ⊥ at hk
  refine LieAlgebra.IsSolvable.mk (R := K) (L := I) (k := k + 1) ?_
  rw [LieIdeal.derivedSeries_eq_bot_iff (R := K) (L := L) I]
  rwa [LieAlgebra.derivedSeriesOfIdeal_add, LieAlgebra.derivedSeriesOfIdeal_succ,
    LieAlgebra.derivedSeriesOfIdeal_zero]

private theorem levi_traceForm_nondegenerate
    {K L M : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
    [Module.Finite K L] [LieAlgebra.IsSemisimple K L]
    [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
    [Module.Finite K M] [LieModule.IsFaithful K L M] :
    (LieModule.traceForm K L M).Nondegenerate := by
  let I := leviTraceKernel (K := K) (L := L) (M := M)
  have hsolv : LieAlgebra.IsSolvable I := leviTraceKernel_isSolvable
  let _ : LieAlgebra.IsSolvable I := hsolv
  have hI : I = ⊥ := LieAlgebra.HasTrivialRadical.eq_bot_of_isSolvable I
  rw [LinearMap.BilinForm.nondegenerate_iff_ker_eq_bot]
  change (I : Submodule K L) = ⊥
  exact congr_arg LieSubmodule.toSubmodule hI

private noncomputable def leviCasimir
    {K L M : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    [Module.Finite K L] [AddCommGroup M] [Module K M] [LieRingModule L M]
    [LieModule K L M] [Module.Free K M] [Module.Finite K M]
    (hβ : (LieModule.traceForm K L M).Nondegenerate) : Module.End K M := by
  classical
  let b := Module.Free.chooseBasis K L
  exact ∑ i, LieModule.toEnd K L M (b i) *
    LieModule.toEnd K L M ((LieModule.traceForm K L M).dualBasis hβ b i)

private theorem levi_trace_casimir
    {K L M : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    [Module.Finite K L] [AddCommGroup M] [Module K M] [LieRingModule L M]
    [LieModule K L M] [Module.Free K M] [Module.Finite K M]
    (hβ : (LieModule.traceForm K L M).Nondegenerate) :
    LinearMap.trace K M (leviCasimir hβ) = (Module.finrank K L : K) := by
  classical
  let b := Module.Free.chooseBasis K L
  change LinearMap.trace K M (∑ i, LieModule.toEnd K L M (b i) *
    LieModule.toEnd K L M ((LieModule.traceForm K L M).dualBasis hβ b i)) = _
  rw [map_sum]
  simp_rw [Module.End.mul_eq_comp]
  simp_rw [← LieModule.traceForm_apply_apply]
  simp_rw [LinearMap.BilinForm.apply_dualBasis_right hβ
    (LinearMap.BilinForm.isSymm_iff.mpr (LieModule.traceForm_isSymm K L M)) b]
  simp [Module.finrank_eq_card_basis b]

private theorem levi_lie_dualBasis
    {K L M ι : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
    [Fintype ι] [DecidableEq ι]
    (hβ : (LieModule.traceForm K L M).Nondegenerate)
    (b : Module.Basis ι K L) (x : L) (i : ι) :
    ⁅x, (LieModule.traceForm K L M).dualBasis hβ b i⁆ =
      -∑ j, b.repr ⁅x, b j⁆ i •
        (LieModule.traceForm K L M).dualBasis hβ b j := by
  let d := (LieModule.traceForm K L M).dualBasis hβ b
  apply d.repr.injective
  ext j
  rw [LinearMap.BilinForm.dualBasis_repr_apply]
  rw [LieModule.traceForm_apply_lie_apply']
  rw [← levi_repr_eq_dual hβ b ⁅x, b j⁆ i]
  simp [d, Finsupp.single_apply]

private theorem levi_casimir_commute
    {K L M : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    [Module.Finite K L] [AddCommGroup M] [Module K M] [LieRingModule L M]
    [LieModule K L M] [Module.Free K M] [Module.Finite K M]
    (hβ : (LieModule.traceForm K L M).Nondegenerate) (x : L) :
    Commute (leviCasimir hβ) (LieModule.toEnd K L M x) := by
  classical
  let b := Module.Free.chooseBasis K L
  let d := (LieModule.traceForm K L M).dualBasis hβ b
  let ρ := LieModule.toEnd K L M
  change Commute (∑ i, ρ (b i) * ρ (d i)) (ρ x)
  rw [commute_iff_eq]
  rw [← sub_eq_zero]
  calc
    (∑ i, ρ (b i) * ρ (d i)) * ρ x - ρ x * (∑ i, ρ (b i) * ρ (d i)) =
        -(∑ i, (ρ ⁅x, b i⁆ * ρ (d i) + ρ (b i) * ρ ⁅x, d i⁆)) := by
          rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib,
            ← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl
          intro i _
          rw [LieHom.map_lie ρ, LieHom.map_lie ρ, Ring.lie_def, Ring.lie_def]
          noncomm_ring
    _ = 0 := by
      have hxb (i) : ρ ⁅x, b i⁆ =
          ∑ j, b.repr ⁅x, b i⁆ j • ρ (b j) := by
        conv_lhs => rw [← levi_sum_repr b ⁅x, b i⁆]
        rw [map_sum]
        simp_rw [map_smul]
      have hxd (i) : ρ ⁅x, d i⁆ =
          -∑ j, b.repr ⁅x, b j⁆ i • ρ (d j) := by
        rw [levi_lie_dualBasis hβ b x i]
        rw [map_neg, map_sum]
        simp_rw [map_smul]
        rfl
      rw [Finset.sum_add_distrib]
      simp_rw [hxb, hxd]
      simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm,
        mul_neg, Finset.sum_neg_distrib]
      rw [Finset.sum_comm]
      simp

private theorem levi_casimir_range_le
    {K L M : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    [Module.Finite K L] [AddCommGroup M] [Module K M] [LieRingModule L M]
    [LieModule K L M] [Module.Free K M] [Module.Finite K M]
    (hβ : (LieModule.traceForm K L M).Nondegenerate) (W : Submodule K M)
    (hW : ∀ (x : L) (m : M), LieModule.toEnd K L M x m ∈ W) :
    LinearMap.range (leviCasimir hβ) ≤ W := by
  classical
  rintro _ ⟨m, rfl⟩
  let b := Module.Free.chooseBasis K L
  let d := (LieModule.traceForm K L M).dualBasis hβ b
  change (∑ i, LieModule.toEnd K L M (b i) * LieModule.toEnd K L M (d i)) m ∈ W
  rw [LinearMap.sum_apply]
  apply Submodule.sum_mem
  intro i _
  rw [Module.End.mul_apply]
  exact hW (b i) _

private theorem levi_isKilling_killingCompl
    {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
    [Module.Finite K L] [LieAlgebra.IsSemisimple K L] (I : LieIdeal K L) :
    LieAlgebra.IsKilling K I.killingCompl := by
  let _ : LieAlgebra.IsKilling K L := inferInstance
  let H := I.killingCompl
  have hcompl : IsCompl I H := I.isCompl_killingCompl
  have hB := LieAlgebra.IsKilling.killingForm_nondegenerate K L
  have hrefl := (LieModule.traceForm_isSymm K L L).isRefl
  have horth : (killingForm K L).orthogonal H.toSubmodule = I.toSubmodule := by
    change (killingForm K L).orthogonal
      ((killingForm K L).orthogonal I.toSubmodule) = I.toSubmodule
    exact LinearMap.BilinForm.orthogonal_orthogonal hB hrefl I.toSubmodule
  have hdisj : Disjoint H.toSubmodule
      ((killingForm K L).orthogonal H.toSubmodule) := by
    rw [horth]
    exact LieSubmodule.disjoint_toSubmodule.mpr hcompl.disjoint.symm
  have hres : ((killingForm K L).restrict H.toSubmodule).Nondegenerate :=
    LinearMap.BilinForm.nondegenerate_restrict_of_disjoint_orthogonal
      (killingForm K L) hrefl hdisj
  have hk : (killingForm K H).Nondegenerate := by
    rw [LieIdeal.killingForm_eq]
    exact hres
  refine LieAlgebra.IsKilling.mk ?_
  rw [eq_bot_iff]
  intro x hx
  rw [LieSubmodule.mem_bot]
  apply hk.2 x
  intro y
  exact (LieIdeal.mem_killingCompl K H ⊤).mp hx y (LieSubmodule.mem_top y)

private theorem levi_isFaithful_killingCompl_ker
    {K L M : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
    [Module.Finite K L] [LieAlgebra.IsSemisimple K L]
    [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M] :
    LieModule.IsFaithful K (LieModule.ker K L M).killingCompl M := by
  let I := LieModule.ker K L M
  let H := I.killingCompl
  let _ : LieAlgebra.IsKilling K L := inferInstance
  have hcompl : IsCompl I H := I.isCompl_killingCompl
  refine ⟨?_⟩
  intro x y hxy
  apply Subtype.ext
  change LieModule.toEnd K L M x.1 = LieModule.toEnd K L M y.1 at hxy
  have hker : x.1 - y.1 ∈ I := by
    change LieModule.toEnd K L M (x.1 - y.1) = 0
    rw [map_sub, sub_eq_zero]
    exact hxy
  have hH : x.1 - y.1 ∈ H := H.sub_mem x.2 y.2
  have hz : x.1 - y.1 ∈ I ⊓ H := ⟨hker, hH⟩
  rw [hcompl.inf_eq_bot] at hz
  change x.1 - y.1 = 0 at hz
  exact sub_eq_zero.mp hz

private theorem levi_lie_top_eq_top
    {K L : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]
    [LieAlgebra.IsSemisimple K L] :
    ⁅(⊤ : LieIdeal K L), (⊤ : LieIdeal K L)⁆ = ⊤ := by
  apply top_unique
  calc
    (⊤ : LieIdeal K L) = sSup {I : LieIdeal K L | IsAtom I} :=
      LieAlgebra.IsSemisimple.sSup_atoms_eq_top.symm
    _ ≤ ⁅(⊤ : LieIdeal K L), (⊤ : LieIdeal K L)⁆ := by
      apply sSup_le
      intro I hI
      rw [← lie_eq_self_of_isAtom_of_nonabelian I hI
        (LieAlgebra.IsSemisimple.non_abelian_of_isAtom I hI)]
      exact LieSubmodule.mono_lie le_top le_top

private theorem levi_codim_one_action_mem
    {K L M : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    [LieAlgebra.IsSemisimple K L] [AddCommGroup M] [Module K M]
    [LieRingModule L M] [LieModule K L M] [Module.Finite K M]
    (W : LieSubmodule K L M) (hW : Module.finrank K (M ⧸ W) = 1) :
    ∀ (x : L) (m : M), ⁅x, m⁆ ∈ W := by
  let Q := M ⧸ W
  have hendcomm (f g : Module.End K Q) : Commute f g := by
    obtain ⟨a, ha, -⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hW f
    obtain ⟨b, hb, -⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hW g
    rw [ha, hb]
    ext q
    simp only [Module.End.mul_apply, LinearMap.smul_apply, LinearMap.id_apply, smul_smul]
    rw [mul_comm]
  have hbracket (x y : L) : LieModule.toEnd K L Q ⁅x, y⁆ = 0 := by
    rw [LieHom.map_lie, Ring.lie_def, (hendcomm _ _).eq, sub_self]
  have hle : ⁅(⊤ : LieIdeal K L), (⊤ : LieIdeal K L)⁆ ≤ LieModule.ker K L Q := by
    rw [LieSubmodule.lie_le_iff]
    intro x _ y _
    change LieModule.toEnd K L Q ⁅x, y⁆ = 0
    exact hbracket x y
  have hker : LieModule.ker K L Q = ⊤ := by
    apply top_unique
    rw [← levi_lie_top_eq_top]
    exact hle
  intro x m
  apply (LieSubmodule.Quotient.mk_eq_zero W).mp
  rw [LieModuleHom.map_lie]
  have hx : x ∈ LieModule.ker K L Q := by
    rw [hker]
    exact LieSubmodule.mem_top x
  change LieModule.toEnd K L Q x ((LieSubmodule.Quotient.mk' W) m) = 0
  change LieModule.toEnd K L Q x = 0 at hx
  rw [hx]
  rfl

private theorem levi_exists_isCompl_of_trivial_action
    {K L M : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
    (htriv : ∀ (x : L) (m : M), ⁅x, m⁆ = 0) (W : LieSubmodule K L M) :
    ∃ U : LieSubmodule K L M, IsCompl W U := by
  obtain ⟨U, hU⟩ := W.toSubmodule.exists_isCompl
  let U' : LieSubmodule K L M :=
    { __ := U
      lie_mem := by
        intro x m _
        rw [htriv]
        exact zero_mem U }
  exact ⟨U', LieSubmodule.isCompl_toSubmodule.mp hU⟩

private def leviZeroFitting
    {K L M : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]
    [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
    (c : Module.End K M)
    (hc : ∀ x : L, Commute c (LieModule.toEnd K L M x)) : LieSubmodule K L M where
  __ := c.maxGenEigenspace 0
  lie_mem := by
    intro x m hm
    exact Module.End.mapsTo_maxGenEigenspace_of_comm (hc x) 0 hm

private theorem levi_finrank_quotient_comap
    {K L M : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
    [Module.Finite K M] (V W : LieSubmodule K L M) (hVW : V ⊔ W = ⊤) :
    Module.finrank K (V ⧸ W.comap V.incl) = Module.finrank K (M ⧸ W) := by
  change Module.finrank K (V ⧸ (W.comap V.incl).toSubmodule) =
    Module.finrank K (M ⧸ W.toSubmodule)
  let f : V →ₗ[K] M ⧸ W := W.toSubmodule.mkQ.comp V.toSubmodule.subtype
  have hker : LinearMap.ker f = (W.comap V.incl).toSubmodule := by
    ext v
    simp [f]
  have hsurj : Function.Surjective f := by
    intro q
    induction q using Submodule.Quotient.induction_on with
    | _ m =>
      have hm : m ∈ V ⊔ W := by
        rw [hVW]
        exact LieSubmodule.mem_top m
      rw [LieSubmodule.mem_sup] at hm
      obtain ⟨v, hv, w, hw, rfl⟩ := hm
      refine ⟨⟨v, hv⟩, ?_⟩
      change LieSubmodule.Quotient.mk (N := W) v =
        LieSubmodule.Quotient.mk (N := W) (v + w)
      apply (Submodule.Quotient.eq W.toSubmodule).2
      have hw' : w ∈ W.toSubmodule := hw
      simpa only [sub_add_cancel_left, neg_mem_iff] using hw'
  calc
    Module.finrank K (V ⧸ (W.comap V.incl).toSubmodule) =
        Module.finrank K (V ⧸ LinearMap.ker f) := by rw [hker]
    _ = Module.finrank K (LinearMap.range f) := f.quotKerEquivRange.finrank_eq
    _ = Module.finrank K (M ⧸ W) := by
      exact (LinearEquiv.ofTop (LinearMap.range f)
        (LinearMap.range_eq_top.mpr hsurj)).finrank_eq

private theorem levi_isCompl_map_of_isCompl_comap
    {K L M : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]
    [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
    (V W : LieSubmodule K L M) (hVW : V ⊔ W = ⊤)
    (U : LieSubmodule K L V) (hU : IsCompl (W.comap V.incl) U) :
    IsCompl W (U.map V.incl) := by
  constructor
  · rw [disjoint_iff]
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxW, hxU⟩ := hx
    change x ∈ U.toSubmodule.map V.toSubmodule.subtype at hxU
    rw [Submodule.mem_map] at hxU
    obtain ⟨u, hu, rfl⟩ := hxU
    have huW : u ∈ W.comap V.incl := hxW
    have hu0 : u ∈ (W.comap V.incl) ⊓ U := ⟨huW, hu⟩
    rw [hU.inf_eq_bot] at hu0
    change u = 0 at hu0
    change (u.1 : M) = 0
    exact congr_arg Subtype.val hu0
  · rw [codisjoint_iff]
    apply top_unique
    intro x _
    have hx : x ∈ V ⊔ W := by
      rw [hVW]
      exact LieSubmodule.mem_top x
    rw [LieSubmodule.mem_sup] at hx
    obtain ⟨v, hv, w, hw, rfl⟩ := hx
    let v' : V := ⟨v, hv⟩
    have hv' : v' ∈ (W.comap V.incl) ⊔ U := by
      rw [hU.sup_eq_top]
      exact LieSubmodule.mem_top v'
    rw [LieSubmodule.mem_sup] at hv'
    obtain ⟨a, ha, b, hb, hab⟩ := hv'
    rw [LieSubmodule.mem_sup]
    refine ⟨a.1 + w, W.add_mem ha hw, b.1, ?_, ?_⟩
    · exact LieSubmodule.mem_map_of_mem hb
    · apply_fun Subtype.val at hab
      dsimp [v'] at hab
      rw [← hab]
      abel

private theorem levi_codim_one_complement_aux
    (n : ℕ) {K L M : Type*} [Field K] [CharZero K] [LieRing L]
    [LieAlgebra K L] [Module.Finite K L] [LieAlgebra.IsSemisimple K L]
    [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
    [Module.Finite K M] (W : LieSubmodule K L M)
    (hquot : Module.finrank K (M ⧸ W) = 1) (_hlt : Module.finrank K W < n) :
    ∃ U : LieSubmodule K L M, IsCompl W U := by
  classical
  let I := LieModule.ker K L M
  let H := I.killingCompl
  let _ : LieAlgebra.IsKilling K L := inferInstance
  have hcompl : IsCompl I H := I.isCompl_killingCompl
  have hHkilling : LieAlgebra.IsKilling K H := levi_isKilling_killingCompl I
  let _ : LieAlgebra.IsKilling K H := hHkilling
  let _ : LieAlgebra.IsSemisimple K H := inferInstance
  by_cases hH0 : Module.finrank K H = 0
  · have hHbot : H = ⊥ := by
      rw [← LieSubmodule.toSubmodule_inj]
      exact Submodule.finrank_eq_zero.mp hH0
    have hItop : I = ⊤ := by
      have hs := hcompl.sup_eq_top
      rwa [hHbot, sup_bot_eq] at hs
    apply levi_exists_isCompl_of_trivial_action (W := W)
    intro x m
    have hx : x ∈ I := by
      rw [hItop]
      exact LieSubmodule.mem_top x
    change LieModule.toEnd K L M x = 0 at hx
    change LieModule.toEnd K L M x m = 0
    rw [hx]
    rfl
  · have hfaithful : LieModule.IsFaithful K H M :=
      levi_isFaithful_killingCompl_ker
    let _ : LieModule.IsFaithful K H M := hfaithful
    have hβ : (LieModule.traceForm K H M).Nondegenerate :=
      levi_traceForm_nondegenerate
    let c := leviCasimir hβ
    have hcL (x : L) : Commute c (LieModule.toEnd K L M x) := by
      have hx : x ∈ I ⊔ H := by
        rw [hcompl.sup_eq_top]
        exact LieSubmodule.mem_top x
      rw [LieSubmodule.mem_sup] at hx
      obtain ⟨i, hi, h, hh, rfl⟩ := hx
      have hi0 : LieModule.toEnd K L M i = 0 := by
        exact hi
      have hch := levi_casimir_commute hβ (⟨h, hh⟩ : H)
      change Commute c (LieModule.toEnd K L M h) at hch
      rw [map_add, hi0, zero_add]
      exact hch
    let V := leviZeroFitting c hcL
    let P := ⨅ k : ℕ, LinearMap.range (c ^ k)
    have hV : V.toSubmodule = ⨆ k : ℕ, LinearMap.ker (c ^ k) := by
      change c.maxGenEigenspace 0 = _
      rw [← Module.End.iSup_genEigenspace_eq]
      simp_rw [Module.End.genEigenspace_zero_nat]
    have hVP : IsCompl V.toSubmodule P := by
      rw [hV]
      exact LinearMap.isCompl_iSup_ker_pow_iInf_range_pow c
    have haction := levi_codim_one_action_mem W hquot
    have hcW : LinearMap.range c ≤ W.toSubmodule := by
      apply levi_casimir_range_le hβ W.toSubmodule
      intro x m
      exact haction x.1 m
    have hPW : P ≤ W.toSubmodule := by
      calc
        P ≤ LinearMap.range (c ^ 1) := iInf_le _ 1
        _ = LinearMap.range c := by rw [pow_one]
        _ ≤ W.toSubmodule := hcW
    have hPne : P ≠ ⊥ := by
      intro hP
      have hVtop : V.toSubmodule = ⊤ := by
        have hs := hVP.sup_eq_top
        rwa [hP, sup_bot_eq] at hs
      have hpoint : ∀ m : M, ∃ k : ℕ, (c ^ k) m = 0 := by
        intro m
        have hm : m ∈ c.maxGenEigenspace 0 := by
          change m ∈ V.toSubmodule
          rw [hVtop]
          exact Submodule.mem_top
        simpa using (Module.End.mem_maxGenEigenspace c 0 m).mp hm
      have hnil : IsNilpotent c :=
        ((LinearMap.charpoly_nilpotent_tfae c).out 2 0).mp hpoint
      have htrace0 : LinearMap.trace K M c = 0 :=
        (LinearMap.isNilpotent_trace_of_isNilpotent hnil).eq_zero
      rw [levi_trace_casimir hβ] at htrace0
      exact (Nat.cast_ne_zero.mpr hH0) htrace0
    have hVWsub : V.toSubmodule ⊔ W.toSubmodule = ⊤ := by
      apply top_unique
      rw [← hVP.sup_eq_top]
      exact sup_le_sup le_rfl hPW
    have hVW : V ⊔ W = ⊤ := by
      rw [← LieSubmodule.toSubmodule_inj]
      exact hVWsub
    have hInfLt : V.toSubmodule ⊓ W.toSubmodule < W.toSubmodule := by
      refine lt_of_le_of_ne inf_le_right ?_
      intro heq
      have hWV : W.toSubmodule ≤ V.toSubmodule := by
        rw [← heq]
        exact inf_le_left
      have hPV : P ≤ V.toSubmodule := hPW.trans hWV
      apply hPne
      rw [← le_bot_iff, ← hVP.inf_eq_bot]
      exact le_inf hPV le_rfl
    let W' := W.comap V.incl
    have hmapW' : W'.map V.incl = V ⊓ W := by
      ext x
      constructor
      · intro hx
        rw [LieSubmodule.mem_map] at hx
        obtain ⟨w, hw, rfl⟩ := hx
        exact ⟨w.2, hw⟩
      · rintro ⟨hxV, hxW⟩
        exact LieSubmodule.mem_map_of_mem (m := (⟨x, hxV⟩ : V)) hxW
    have hfinW' : Module.finrank K W' = Module.finrank K ↑(V ⊓ W) := by
      rw [← hmapW']
      exact (LieSubmodule.equivMapOfInjective W' V.injective_incl).toLinearEquiv.finrank_eq
    have hlt' : Module.finrank K W' < Module.finrank K W := by
      rw [hfinW']
      exact Submodule.finrank_lt_finrank_of_lt hInfLt
    have hquot' : Module.finrank K (V ⧸ W') = 1 := by
      rw [levi_finrank_quotient_comap V W hVW]
      exact hquot
    obtain ⟨U, hU⟩ := levi_codim_one_complement_aux (Module.finrank K W) W' hquot' hlt'
    exact ⟨U.map V.incl, levi_isCompl_map_of_isCompl_comap V W hVW U hU⟩
termination_by n
decreasing_by exact _hlt

private theorem levi_codim_one_complement
    {K L M : Type*} [Field K] [CharZero K] [LieRing L]
    [LieAlgebra K L] [Module.Finite K L] [LieAlgebra.IsSemisimple K L]
    [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
    [Module.Finite K M] (W : LieSubmodule K L M)
    (hquot : Module.finrank K (M ⧸ W) = 1) :
    ∃ U : LieSubmodule K L M, IsCompl W U :=
  levi_codim_one_complement_aux (Module.finrank K W + 1) W hquot (Nat.lt_succ_self _)

private def leviHomVanishing
    {K L M : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]
    [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
    (W : LieSubmodule K L M) : LieSubmodule K L (M →ₗ[K] W) where
  carrier := {f | ∀ w : W, f w = 0}
  zero_mem' w := rfl
  add_mem' {f g} hf hg w := by rw [LinearMap.add_apply, hf, hg, add_zero]
  smul_mem' a f hf w := by rw [LinearMap.smul_apply, hf, smul_zero]
  lie_mem := by
    intro x f hf w
    rw [LieHom.lie_apply]
    rw [hf, lie_zero]
    have hfw := hf (⟨⁅x, w.1⁆, W.lie_mem w.2⟩ : W)
    simpa using hfw

private def leviHomScalarMaps
    {K L M : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]
    [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
    (W : LieSubmodule K L M) : LieSubmodule K L (M →ₗ[K] W) where
  carrier := {f | ∃ a : K, ∀ w : W, f w = a • w}
  zero_mem' := ⟨0, fun w ↦ by simp⟩
  add_mem' {f g} := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    refine ⟨a + b, fun w ↦ ?_⟩
    rw [LinearMap.add_apply, ha, hb, add_smul]
  smul_mem' c f := by
    rintro ⟨a, ha⟩
    refine ⟨c * a, fun w ↦ ?_⟩
    rw [LinearMap.smul_apply, ha, mul_smul]
  lie_mem := by
    intro x f hf
    obtain ⟨a, ha⟩ := hf
    refine ⟨0, fun w ↦ ?_⟩
    rw [LieHom.lie_apply, ha, lie_smul]
    have haw := ha (⟨⁅x, w.1⁆, W.lie_mem w.2⟩ : W)
    rw [haw]
    have hxw : ⁅x, w⁆ = (⟨⁅x, w.1⁆, W.lie_mem w.2⟩ : W) := rfl
    rw [hxw, sub_self, zero_smul]

private theorem levi_scalar_unique
    {K L M : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
    (W : LieSubmodule K L M) (hW : W ≠ ⊥) {a b : K}
    (h : ∀ w : W, a • w = b • w) : a = b := by
  have hWsub : W.toSubmodule ≠ ⊥ := by
    intro h
    apply hW
    rw [← LieSubmodule.toSubmodule_inj]
    exact h
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hWsub
  have hab : a • w = b • w := congrArg Subtype.val (h ⟨w, hw⟩)
  have hz : (a - b) • w = 0 := by rw [sub_smul, hab, sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_right hw0)

private noncomputable def leviHomScalar
    {K L M : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
    (W : LieSubmodule K L M) (hW : W ≠ ⊥) :
    leviHomScalarMaps W →ₗ[K] K where
  toFun f := Classical.choose f.2
  map_add' f g := by
    apply levi_scalar_unique W hW
    intro w
    calc
      Classical.choose (f + g).property • w = (f + g : M →ₗ[K] W) w :=
        (Classical.choose_spec (f + g).property w).symm
      _ = f.1 w + g.1 w := rfl
      _ = Classical.choose f.property • w + Classical.choose g.property • w := by
        rw [Classical.choose_spec f.property w, Classical.choose_spec g.property w]
      _ = (Classical.choose f.property + Classical.choose g.property) • w :=
        (add_smul _ _ _).symm
  map_smul' c f := by
    apply levi_scalar_unique W hW
    intro w
    calc
      Classical.choose (c • f).property • w = (c • f : M →ₗ[K] W) w :=
        (Classical.choose_spec (c • f).property w).symm
      _ = c • f.1 w := rfl
      _ = c • (Classical.choose f.property • w) := by
        rw [Classical.choose_spec f.property w]
      _ = (c * Classical.choose f.property) • w := (mul_smul _ _ _).symm

private theorem leviHomScalar_apply
    {K L M : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
    (W : LieSubmodule K L M) (hW : W ≠ ⊥)
    (f : leviHomScalarMaps W) (w : W) :
    f.1 w = leviHomScalar W hW f • w :=
  Classical.choose_spec f.2 w

private theorem leviHomScalar_ker
    {K L M : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
    (W : LieSubmodule K L M) (hW : W ≠ ⊥) :
    LinearMap.ker (leviHomScalar W hW) =
      (leviHomVanishing W).toSubmodule.comap
        (leviHomScalarMaps W).toSubmodule.subtype := by
  ext f
  constructor
  · intro hf
    change leviHomScalar W hW f = 0 at hf
    change ∀ w : W, f.1 w = 0
    intro w
    rw [leviHomScalar_apply W hW f w, hf, zero_smul]
  · intro hf
    change leviHomScalar W hW f = 0
    apply levi_scalar_unique W hW
    intro w
    rw [zero_smul]
    exact (leviHomScalar_apply W hW f w).symm.trans (hf w)

private theorem leviHomScalar_surjective
    {K L M : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
    (W : LieSubmodule K L M) (hW : W ≠ ⊥) :
    Function.Surjective (leviHomScalar W hW) := by
  obtain ⟨Q, hQ⟩ := W.toSubmodule.exists_isCompl
  let p : M →ₗ[K] W := W.toSubmodule.projectionOnto Q hQ
  have hp (w : W) : p w = w := by
    exact Submodule.projectionOnto_apply_left hQ w
  let pv : leviHomScalarMaps W :=
    ⟨p, 1, fun w ↦ by rw [hp, one_smul]⟩
  have hpv : leviHomScalar W hW pv = 1 := by
    apply levi_scalar_unique W hW
    intro w
    rw [one_smul]
    exact (leviHomScalar_apply W hW pv w).symm.trans (hp w)
  intro a
  refine ⟨a • pv, ?_⟩
  rw [LinearMap.map_smul, hpv, smul_eq_mul, mul_one]

private theorem leviHomScalarMaps_quotient_finrank
    {K L M : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
    [Module.Finite K M] (W : LieSubmodule K L M) (hW : W ≠ ⊥) :
    Module.finrank K
        (leviHomScalarMaps W ⧸
          (leviHomVanishing W).comap (leviHomScalarMaps W).incl) = 1 := by
  let s := leviHomScalar W hW
  have hsKer : LinearMap.ker s =
      ((leviHomVanishing W).comap (leviHomScalarMaps W).incl).toSubmodule := by
    exact leviHomScalar_ker W hW
  have hsRange : LinearMap.range s = ⊤ :=
    LinearMap.range_eq_top.mpr (leviHomScalar_surjective W hW)
  change Module.finrank K
      (leviHomScalarMaps W ⧸
        ((leviHomVanishing W).comap (leviHomScalarMaps W).incl).toSubmodule) = 1
  rw [← hsKer, s.quotKerEquivRange.finrank_eq, hsRange]
  rw [finrank_top]
  exact Module.finrank_self K

private theorem levi_lie_mem_HomVanishing_of_mem_scalarMaps
    {K L M : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]
    [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
    (W : LieSubmodule K L M) (f : leviHomScalarMaps W) (x : L) :
    ⁅x, (f.1 : M →ₗ[K] W)⁆ ∈ leviHomVanishing W := by
  obtain ⟨a, ha⟩ := f.2
  intro w
  rw [LieHom.lie_apply, ha, lie_smul]
  have haw := ha (⟨⁅x, w.1⁆, W.lie_mem w.2⟩ : W)
  rw [haw]
  have hxw : ⁅x, w⁆ = (⟨⁅x, w.1⁆, W.lie_mem w.2⟩ : W) := rfl
  rw [hxw, sub_self]

/-- Weyl's complete reducibility theorem for finite-dimensional modules over a
semisimple Lie algebra in characteristic zero. -/
theorem sourceLieModule_exists_complement
    {K L M : Type*} [Field K] [CharZero K] [LieRing L]
    [LieAlgebra K L] [Module.Finite K L] [LieAlgebra.IsSemisimple K L]
    [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
    [Module.Finite K M] (W : LieSubmodule K L M) :
    ∃ U : LieSubmodule K L M, IsCompl W U := by
  by_cases hW : W = ⊥
  · subst W
    exact ⟨⊤, isCompl_bot_top⟩
  let V := leviHomScalarMaps W
  let Z := (leviHomVanishing W).comap V.incl
  have hfin : Module.finrank K (V ⧸ Z) = 1 :=
    leviHomScalarMaps_quotient_finrank W hW
  obtain ⟨T, hT⟩ := levi_codim_one_complement Z hfin
  obtain ⟨Q, hQ⟩ := W.toSubmodule.exists_isCompl
  let p : M →ₗ[K] W := W.toSubmodule.projectionOnto Q hQ
  have hp (w : W) : p w = w := Submodule.projectionOnto_apply_left hQ w
  let pv : V := ⟨p, 1, fun w ↦ by rw [hp, one_smul]⟩
  have hpvScalar : leviHomScalar W hW pv = 1 := by
    apply levi_scalar_unique W hW
    intro w
    rw [one_smul]
    exact (leviHomScalar_apply W hW pv w).symm.trans (hp w)
  have hpvMem : pv ∈ Z ⊔ T := by
    rw [hT.sup_eq_top]
    trivial
  rw [LieSubmodule.mem_sup] at hpvMem
  obtain ⟨z, hz, t, ht, hzt⟩ := hpvMem
  have hzScalar : leviHomScalar W hW z = 0 := by
    have hzKer : z ∈ LinearMap.ker (leviHomScalar W hW) := by
      rw [leviHomScalar_ker W hW]
      exact hz
    exact hzKer
  have htScalar : leviHomScalar W hW t = 1 := by
    have h := congrArg (fun f : V ↦ leviHomScalar W hW f) hzt
    change leviHomScalar W hW (z + t) = leviHomScalar W hW pv at h
    rw [LinearMap.map_add, hzScalar, zero_add, hpvScalar] at h
    exact h
  have htApply (w : W) : t.1 w = w := by
    rw [leviHomScalar_apply W hW t w, htScalar, one_smul]
  have htInvariant (x : L) : ⁅x, (t.1 : M →ₗ[K] W)⁆ = 0 := by
    have hxZ : ⁅x, t⁆ ∈ Z := by
      exact levi_lie_mem_HomVanishing_of_mem_scalarMaps W t x
    have hxT : ⁅x, t⁆ ∈ T := T.lie_mem ht
    have hxBot : ⁅x, t⁆ ∈ (⊥ : LieSubmodule K L V) := by
      rw [← hT.inf_eq_bot]
      exact ⟨hxZ, hxT⟩
    have hxZero : ⁅x, t⁆ = 0 := by simpa using hxBot
    exact congrArg Subtype.val hxZero
  let U : LieSubmodule K L M :=
    { carrier := {m | t.1 m = 0}
      zero_mem' := LinearMap.map_zero t.1
      add_mem' := by
        intro a b ha hb
        change t.1 (a + b) = 0
        rw [LinearMap.map_add, ha, hb, add_zero]
      smul_mem' := by
        intro a m hm
        change t.1 (a • m) = 0
        rw [LinearMap.map_smul, hm, smul_zero]
      lie_mem := by
        intro x m hm
        have h := congrArg (fun f : M →ₗ[K] W ↦ f m) (htInvariant x)
        change (⁅x, (t.1 : M →ₗ[K] W)⁆) m = 0 at h
        rw [LieHom.lie_apply, hm, lie_zero, zero_sub] at h
        exact neg_eq_zero.mp h }
  refine ⟨U, ?_⟩
  constructor
  · rw [disjoint_iff, eq_bot_iff]
    intro m hm
    have htm : t.1 m = 0 := hm.2
    have hrest := htApply (⟨m, hm.1⟩ : W)
    have hm0 : m = 0 := by
      have h := congrArg Subtype.val hrest
      rw [htm] at h
      exact h.symm
    change m = 0
    exact hm0
  · rw [codisjoint_iff, eq_top_iff]
    intro m _
    rw [LieSubmodule.mem_sup]
    refine ⟨(t.1 m).1, (t.1 m).2, m - (t.1 m).1, ?_, ?_⟩
    · change t.1 (m - (t.1 m).1) = 0
      rw [LinearMap.map_sub, htApply (t.1 m), sub_self]
    · abel

end Dubon2026
