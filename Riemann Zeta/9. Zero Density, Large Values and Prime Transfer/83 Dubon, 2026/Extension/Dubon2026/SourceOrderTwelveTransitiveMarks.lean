import Dubon2026.SourceOrderTwelveCubicCentralizer

/-! DUB-17/18 -> characteristic-two genus/Picard -> weighted exceptional
census -> exact orbit sizes and involution/cubic fixed-point marks for the
actual order-twelve sign quotient. Adapted from
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_MulAction_natCard_fixedBy_of_isPretransitive_of_card_eq_twelve.
Only the source dependency chain to these exact marks is retained. The
actual elliptic quotient must discharge the order/exponent hypotheses. -/
namespace Dubon2026.SourceOrderTwelve
open MulAction Subgroup
noncomputable section
variable {G : Type*} [Group G] [Finite G]
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

variable (X : Type*) [MulAction G X]

omit [Finite G] in
theorem card_fixedBy_mul_card_stabilizer [IsPretransitive G X] (x₀ : X) (g : G) :
    Nat.card (fixedBy X g) * Nat.card (stabilizer G x₀) =
      Nat.card {x : G // x⁻¹ * g * x ∈ stabilizer G x₀} := by
  classical
  set H := stabilizer G x₀ with hH
  let ψ : G ⧸ H → X := fun q => ((orbitEquivQuotientStabilizer G x₀).symm q : orbit G x₀)
  have hψ : ∀ a : G, ψ (a : G ⧸ H) = a • x₀ := fun a => orbitEquivQuotientStabilizer_symm_apply G x₀ a
  have hψinj : Function.Injective ψ := Subtype.val_injective.comp (Equiv.injective _)
  have hψsurj : Function.Surjective ψ := by
    intro x
    obtain ⟨a, ha⟩ := exists_smul_eq G x₀ x
    exact ⟨a, by rw [hψ, ha]⟩
  have e1 : fixedBy X g ≃ fixedBy (G ⧸ H) g := by
    refine ((Equiv.ofBijective ψ ⟨hψinj, hψsurj⟩).subtypeEquiv ?_).symm
    intro q
    induction q using QuotientGroup.induction_on with
    | H a =>
      show g • (a : G ⧸ H) = (a : G ⧸ H) ↔ g • ψ (a : G ⧸ H) = ψ (a : G ⧸ H)
      rw [MulAction.Quotient.smul_coe, smul_eq_mul, hψ, ← mul_smul, ← hψ, ← hψ, hψinj.eq_iff]
  have e2 : (QuotientGroup.mk ⁻¹' fixedBy (G ⧸ H) g : Set G) = {x : G | x⁻¹ * g * x ∈ H} := by
    ext a
    simp only [Set.mem_preimage, mem_fixedBy, Set.mem_setOf_eq, MulAction.Quotient.smul_coe,
      QuotientGroup.eq]
    rw [smul_eq_mul, show (g * a)⁻¹ * a = (a⁻¹ * g * a)⁻¹ by group, H.inv_mem_iff]
  calc Nat.card (fixedBy X g) * Nat.card H = Nat.card H * Nat.card (fixedBy (G ⧸ H) g) := by
        rw [Nat.card_congr e1, mul_comm]
    _ = Nat.card (QuotientGroup.mk ⁻¹' fixedBy (G ⧸ H) g : Set G) :=
        (QuotientGroup.card_preimage_mk H _).symm
    _ = Nat.card {x : G // x⁻¹ * g * x ∈ H} := by rw [e2]; rfl

omit [Finite G] in
theorem mem_smul_sylow_iff (g : G) (P : Sylow 3 G) (x : G) :
    x ∈ ((g • P : Sylow 3 G) : Subgroup G) ↔ g⁻¹ * x * g ∈ (P : Subgroup G) := by
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp [MulAut.smul_def, mul_assoc]

variable (hG : Nat.card G = 12) (hexp : ∀ g : G, g ^ 2 = 1 ∨ g ^ 3 = 1)
variable [Nonempty X] [IsPretransitive G X]
include hG hexp

theorem marks :
    (Nat.card X = 1 ∨ Nat.card X = 3 ∨ Nat.card X = 4 ∨ Nat.card X = 6 ∨ Nat.card X = 12) ∧
    (∀ a : G, a ≠ 1 → a ^ 2 = 1 →
      (Nat.card X = 1 → Nat.card (fixedBy X a) = 1) ∧
      (Nat.card X = 3 → Nat.card (fixedBy X a) = 3) ∧
      (Nat.card X = 4 → Nat.card (fixedBy X a) = 0) ∧
      (Nat.card X = 6 → Nat.card (fixedBy X a) = 2) ∧
      (Nat.card X = 12 → Nat.card (fixedBy X a) = 0)) ∧
    (∀ b : G, b ≠ 1 → b ^ 3 = 1 →
      (Nat.card X = 1 → Nat.card (fixedBy X b) = 1) ∧
      (Nat.card X = 3 → Nat.card (fixedBy X b) = 0) ∧
      (Nat.card X = 4 → Nat.card (fixedBy X b) = 1) ∧
      (Nat.card X = 6 → Nat.card (fixedBy X b) = 0) ∧
      (Nat.card X = 12 → Nat.card (fixedBy X b) = 0)) := by
  classical
  obtain ⟨x₀⟩ := (inferInstance : Nonempty X)
  set H := stabilizer G x₀ with hH
  have hidx : H.index = Nat.card X := index_stabilizer_of_transitive G x₀
  have hHX : Nat.card X * Nat.card H = 12 := by rw [← hidx, H.index_mul_card, hG]
  have hHpos : 0 < Nat.card H := Nat.card_pos
  have hHdvd : Nat.card H ∣ 12 := hG ▸ Subgroup.card_subgroup_dvd_card H

  have key : ∀ g : G, Nat.card (fixedBy X g) * Nat.card H = Nat.card {x : G // x⁻¹ * g * x ∈ H} :=
    card_fixedBy_mul_card_stabilizer X x₀

  have hH6 : Nat.card H ≠ 6 := by
    intro h6
    have hidx2 : H.index = 2 := by
      have := H.index_mul_card; rw [hG, h6] at this; omega
    haveI hn : H.Normal := Subgroup.normal_of_index_eq_two hidx2
    have hsub : {g : G | orderOf g = 3} ⊆ (H : Set G) := by
      intro g hg
      have hg3 : g ^ 3 = 1 := by rw [← hg]; exact pow_orderOf_eq_one g
      have hq2 : Nat.card (G ⧸ H) = 2 := by rw [← Subgroup.index_eq_card, hidx2]
      have h2 : ((g : G ⧸ H)) ^ 2 = 1 := by
        have := pow_card_eq_one' (G := G ⧸ H) (x := (g : G ⧸ H))
        rwa [hq2] at this
      have h3 : ((g : G ⧸ H)) ^ 3 = 1 := by rw [← QuotientGroup.mk_pow, hg3, QuotientGroup.mk_one]
      have h1 : (g : G ⧸ H) = 1 := by
        have e : (g : G ⧸ H) = (g : G ⧸ H) ^ 3 * ((g : G ⧸ H) ^ 2)⁻¹ := by
          simp only [pow_succ, pow_zero, one_mul]; group
        rw [e, h3, h2]; group
      exact (QuotientGroup.eq_one_iff g).mp h1
    have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [ncard_orderOf_eq_three hG hexp, ← Nat.card_coe_set_eq] at hle
    change 8 ≤ Nat.card H at hle
    omega
  have hHcases : Nat.card H = 1 ∨ Nat.card H = 2 ∨ Nat.card H = 3 ∨ Nat.card H = 4 ∨
      Nat.card H = 12 := by
    have hle := Nat.le_of_dvd (by norm_num) hHdvd
    interval_cases h : (Nat.card H) <;> omega

  have fix_zero : ∀ g : G, (∀ x : G, x⁻¹ * g * x ∉ H) → Nat.card (fixedBy X g) = 0 := by
    intro g hg
    have h0 : Nat.card {x : G // x⁻¹ * g * x ∈ H} = 0 := by
      rw [Nat.card_eq_zero]; left; exact ⟨fun x => hg x.1 x.2⟩
    have := key g
    rw [h0] at this
    exact (mul_eq_zero.mp this).resolve_right hHpos.ne'
  have fix_of_count : ∀ (g : G) (m : ℕ), Nat.card {x : G // x⁻¹ * g * x ∈ H} = m * Nat.card H →
      Nat.card (fixedBy X g) = m := by
    intro g m hn
    have := key g
    rw [hn] at this
    exact Nat.eq_of_mul_eq_mul_right hHpos this

  have fix_one : ∀ g : G, Nat.card X = 1 → Nat.card (fixedBy X g) = 1 := by
    intro g h1
    haveI : Subsingleton X := (Nat.card_eq_one_iff_unique.mp h1).1
    have : fixedBy X g = Set.univ := Set.eq_univ_of_forall fun x => Subsingleton.elim _ _
    rw [this, Nat.card_coe_set_eq, Set.ncard_univ, h1]

  have ord_dvd : ∀ {y : G}, y ∈ H → orderOf y ∣ Nat.card H := fun hy => Subgroup.orderOf_dvd_natCard H hy

  have exists_ne_one : 1 < Nat.card H → ∃ y : G, y ∈ H ∧ y ≠ 1 := by
    intro hlt
    haveI := (Finite.one_lt_card_iff_nontrivial.mp hlt)
    obtain ⟨⟨y, hy⟩, hy1⟩ := exists_ne (1 : H)
    exact ⟨y, hy, fun h => hy1 (Subtype.ext h)⟩

  have ncard_image : ∀ (S : Set G) (x : G), ((fun y => y * x) '' S).ncard = S.ncard := fun S x =>
    Set.ncard_image_of_injective S (mul_left_injective x)
  refine ⟨by rcases hHcases with h | h | h | h | h <;> · rw [h] at hHX; omega, ?_, ?_⟩
  ·
    intro a ha1 ha2
    have hoa : orderOf a = 2 := orderOf_eq_two_of_sq ha2 ha1
    have haa : a * a = 1 := by rw [← sq]; exact ha2
    have hcsq : ∀ x : G, (x⁻¹ * a * x) ^ 2 = 1 := fun x => by
      calc (x⁻¹ * a * x) ^ 2 = x⁻¹ * (a * a) * x := by simp only [sq]; group
        _ = 1 := by rw [haa]; group
    have hcne : ∀ x : G, x⁻¹ * a * x ≠ 1 := fun x h => ha1 (by
      calc a = x * (x⁻¹ * a * x) * x⁻¹ := by group
        _ = 1 := by rw [h]; group)
    have hoc : ∀ x : G, orderOf (x⁻¹ * a * x) = 2 := fun x => orderOf_eq_two_of_sq (hcsq x) (hcne x)

    have result : ∃ n v : ℕ, Nat.card X = n ∧ Nat.card (fixedBy X a) = v ∧
        ((n = 1 ∧ v = 1) ∨ (n = 3 ∧ v = 3) ∨ (n = 4 ∧ v = 0) ∨ (n = 6 ∧ v = 2) ∨ (n = 12 ∧ v = 0)) := by
      rcases hHcases with h | h | h | h | h
      ·
        refine ⟨12, 0, by rw [h] at hHX; omega, fix_zero a fun x hx => ?_, by simp⟩
        rw [Subgroup.eq_bot_of_card_eq H h, Subgroup.mem_bot] at hx
        exact hcne x hx
      ·
        obtain ⟨τ, hτH, hτ1⟩ := exists_ne_one (by omega)
        have hτ2 : τ ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp (h ▸ ord_dvd hτH)
        have hoτ : orderOf τ = 2 := orderOf_eq_two_of_sq hτ2 hτ1
        have hHset : (H : Set G) = {1, τ} := by
          symm
          apply Set.eq_of_subset_of_ncard_le
          · intro y hy
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
            rcases hy with rfl | rfl
            · exact H.one_mem
            · exact hτH
          · rw [Set.ncard_pair (Ne.symm hτ1), ← Nat.card_coe_set_eq]
            exact h.le
          · exact Set.toFinite _
        have hmemH : ∀ y : G, y ∈ H ↔ y = 1 ∨ y = τ := by
          intro y
          rw [← SetLike.mem_coe, hHset]
          simp
        obtain ⟨x₀, hx₀⟩ := exists_conj_eq hG hexp hoa hoτ
        have hset : {x : G | x⁻¹ * a * x ∈ H} = (fun y => y * x₀) '' {y : G | y ^ 2 = 1} := by
          ext x
          simp only [Set.mem_setOf_eq, Set.mem_image]
          constructor
          · intro hx
            rw [hmemH] at hx
            rcases hx with hx | hx
            · exact absurd hx (hcne x)
            · refine ⟨x * x₀⁻¹, ?_, by group⟩
              rw [← mul_eq_mul_iff_sq_eq_one hG hexp hoa]

              have e : x⁻¹ * a * x = x₀⁻¹ * a * x₀ := by rw [hx, hx₀]
              calc x * x₀⁻¹ * a = x * (x₀⁻¹ * a * x₀) * x₀⁻¹ := by group
                _ = x * (x⁻¹ * a * x) * x₀⁻¹ := by rw [e]
                _ = a * (x * x₀⁻¹) := by group
          · rintro ⟨y, hy, rfl⟩
            rw [← mul_eq_mul_iff_sq_eq_one hG hexp hoa] at hy
            rw [hmemH]; right
            calc (y * x₀)⁻¹ * a * (y * x₀) = x₀⁻¹ * (y⁻¹ * (a * y)) * x₀ := by group
              _ = x₀⁻¹ * (y⁻¹ * (y * a)) * x₀ := by rw [hy]
              _ = x₀⁻¹ * a * x₀ := by group
              _ = τ := hx₀
        refine ⟨6, 2, by rw [h] at hHX; omega, fix_of_count a 2 ?_, by simp⟩
        change Nat.card ({x : G | x⁻¹ * a * x ∈ H} : Set G) = 2 * Nat.card H
        rw [h, Nat.card_coe_set_eq, hset, ncard_image, ncard_sq_eq_one hG hexp]
      ·
        refine ⟨4, 0, by rw [h] at hHX; omega, fix_zero a fun x hx => ?_, by simp⟩
        have := ord_dvd hx
        rw [hoc x, h] at this
        norm_num at this
      ·
        refine ⟨3, 3, by rw [h] at hHX; omega, fix_of_count a 3 ?_, by simp⟩
        have : ∀ x : G, x⁻¹ * a * x ∈ H := fun x =>
          (mem_iff_sq_eq_one_of_card_eq_four hG hexp h _).mpr (hcsq x)
        rw [h, Nat.card_congr (Equiv.subtypeUnivEquiv this), hG]
      ·
        refine ⟨1, 1, by rw [h] at hHX; omega, fix_one a (by rw [h] at hHX; omega), by simp⟩
    obtain ⟨n, v, hn, hv, hcases⟩ := result
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩ <;>
      rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega
  ·
    intro b hb1 hb3
    have hob : orderOf b = 3 := orderOf_eq_three_of_cube hb3 hb1
    have hcpow : ∀ x : G, (x⁻¹ * b * x) ^ 3 = 1 := fun x => by
      calc (x⁻¹ * b * x) ^ 3 = x⁻¹ * b ^ 3 * x := by
            simp only [pow_succ, pow_zero, one_mul]; group
        _ = 1 := by rw [hb3]; group
    have hcne : ∀ x : G, x⁻¹ * b * x ≠ 1 := fun x h => hb1 (by
      calc b = x * (x⁻¹ * b * x) * x⁻¹ := by group
        _ = 1 := by rw [h]; group)
    have hoc : ∀ x : G, orderOf (x⁻¹ * b * x) = 3 := fun x => orderOf_eq_three_of_cube (hcpow x) (hcne x)
    have hcsq : ∀ x : G, (x⁻¹ * b * x) ^ 2 ≠ 1 := fun x h2 => by
      have := orderOf_dvd_of_pow_eq_one h2
      rw [hoc x] at this; norm_num at this
    have result : ∃ n v : ℕ, Nat.card X = n ∧ Nat.card (fixedBy X b) = v ∧
        ((n = 1 ∧ v = 1) ∨ (n = 3 ∧ v = 0) ∨ (n = 4 ∧ v = 1) ∨ (n = 6 ∧ v = 0) ∨ (n = 12 ∧ v = 0)) := by
      rcases hHcases with h | h | h | h | h
      · refine ⟨12, 0, by rw [h] at hHX; omega, fix_zero b fun x hx => ?_, by simp⟩
        rw [Subgroup.eq_bot_of_card_eq H h, Subgroup.mem_bot] at hx
        exact hcne x hx
      ·
        refine ⟨6, 0, by rw [h] at hHX; omega, fix_zero b fun x hx => ?_, by simp⟩
        have := ord_dvd hx
        rw [hoc x, h] at this
        norm_num at this
      ·
        obtain ⟨c, hcH, hc1⟩ := exists_ne_one (by omega)
        have hocc : orderOf c = 3 := orderOf_eq_three_of_mem h hcH hc1
        have hc3 : c ^ 3 = 1 := by rw [← hocc]; exact pow_orderOf_eq_one c

        obtain ⟨x₀, hx₀⟩ : ∃ x₀ : G, x₀⁻¹ * b * x₀ ∈ H := by
          let PH : Sylow 3 G := Sylow.ofCard H (by rw [hG, factorization_twelve_three, pow_one]; exact h)
          obtain ⟨Pb, hbPb⟩ := exists_sylow_mem_of_orderOf hob
          obtain ⟨g, hg⟩ := exists_smul_eq G Pb PH
          refine ⟨g⁻¹, ?_⟩
          have : g * b * g⁻¹ ∈ ((g • Pb : Sylow 3 G) : Subgroup G) := by
            rw [mem_smul_sylow_iff]
            have e : g⁻¹ * (g * b * g⁻¹) * g = b := by group
            rw [e]; exact hbPb
          rw [hg] at this
          simpa [PH, Sylow.coe_ofCard] using this
        have hset : {x : G | x⁻¹ * b * x ∈ H} = (fun y => y * x₀) '' (Subgroup.zpowers b : Set G) := by
          ext x
          simp only [Set.mem_setOf_eq, Set.mem_image, SetLike.mem_coe]
          constructor
          · intro hx

            have hd := mem_of_card_three h hcH hc1 hx
            have hd₀ := mem_of_card_three h hcH hc1 hx₀
            refine ⟨x * x₀⁻¹, ?_, by group⟩

            suffices heq : x⁻¹ * b * x = x₀⁻¹ * b * x₀ by
              apply mem_zpowers_of_mul_eq_mul hG hexp hob
              calc x * x₀⁻¹ * b = x * (x₀⁻¹ * b * x₀) * x₀⁻¹ := by group
                _ = x * (x⁻¹ * b * x) * x₀⁻¹ := by rw [heq]
                _ = b * (x * x₀⁻¹) := by group

            have hz : (x₀⁻¹ * x)⁻¹ * (x₀⁻¹ * b * x₀) * (x₀⁻¹ * x) = x⁻¹ * b * x := by group
            rcases hd with hd | hd | hd
            · exact absurd hd (hcne x)
            rcases hd₀ with hd₀ | hd₀ | hd₀
            · exact absurd hd₀ (hcne x₀)
            · rw [hd, hd₀]
            · exfalso
              rw [hd, hd₀] at hz

              have hocc2 : orderOf (c ^ 2) = 3 := by
                apply orderOf_eq_three_of_cube
                · rw [← pow_mul, show 2 * 3 = 3 * 2 by norm_num, pow_mul, hc3, one_pow]
                · intro h2
                  apply hc1
                  calc c = c ^ 3 * (c ^ 2)⁻¹ := by simp only [pow_succ, pow_zero, one_mul]; group
                    _ = 1 := by rw [hc3, h2]; group
              apply conj_ne_sq hG hexp hocc2 (z := x₀⁻¹ * x)
              rw [hz]
              calc c = c ^ 3 * c := by rw [hc3, one_mul]
                _ = (c ^ 2) ^ 2 := by simp only [pow_succ, pow_zero, one_mul]; group
            rcases hd₀ with hd₀ | hd₀ | hd₀
            · exact absurd hd₀ (hcne x₀)
            · exfalso
              rw [hd, hd₀] at hz
              exact conj_ne_sq hG hexp hocc hz
            · rw [hd, hd₀]
          · rintro ⟨y, hy, rfl⟩
            rw [Subgroup.mem_zpowers_iff] at hy
            obtain ⟨k, rfl⟩ := hy
            have hc : Commute (b ^ k) b := (Commute.refl b).zpow_left k
            have hcomm : (b ^ k)⁻¹ * b * b ^ k = b := by
              rw [mul_assoc, ← hc.eq, ← mul_assoc, inv_mul_cancel, one_mul]
            have e : (b ^ k * x₀)⁻¹ * b * (b ^ k * x₀) = x₀⁻¹ * b * x₀ := by
              calc (b ^ k * x₀)⁻¹ * b * (b ^ k * x₀) = x₀⁻¹ * ((b ^ k)⁻¹ * b * b ^ k) * x₀ := by group
                _ = x₀⁻¹ * b * x₀ := by rw [hcomm]
            rw [e]
            exact hx₀
        refine ⟨4, 1, by rw [h] at hHX; omega, fix_of_count b 1 ?_, by simp⟩
        change Nat.card ({x : G | x⁻¹ * b * x ∈ H} : Set G) = 1 * Nat.card H
        rw [h, Nat.card_coe_set_eq, hset, ncard_image, ← Nat.card_coe_set_eq]
        change Nat.card (Subgroup.zpowers b) = 1 * 3
        rw [Nat.card_zpowers, hob]
      ·
        refine ⟨3, 0, by rw [h] at hHX; omega, fix_zero b fun x hx => ?_, by simp⟩
        exact hcsq x ((mem_iff_sq_eq_one_of_card_eq_four hG hexp h _).mp hx)
      · refine ⟨1, 1, by rw [h] at hHX; omega, fix_one b (by rw [h] at hHX; omega), by simp⟩
    obtain ⟨n, v, hn, hv, hcases⟩ := result
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩ <;>
      rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega

end
end Dubon2026.SourceOrderTwelve
