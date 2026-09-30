import TaoTrudgianYang2025.HuxleyLinearForms

open Set Polynomial TaoTrudgianYang2025 TaoTrudgianYang2025.HuxleyRationalPhase
open scoped ContDiff BigOperators FourierTransform Classical
namespace HuxleyDenseAnchorScratch

private theorem positive_difference_dyadic_anchor_source_partition_cutoffs
    {σ c J : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J) :
    ∃ C ≥ (1:ℝ), ∀ (ι : Type*) (S : Finset ι) (F : ℝ → ℝ)
      (y : ι → ℝ) (L : ι → ℤ) (H : ι → ℕ) (anchor : ι → ℚ) (za : ι → ℝ)
      (N Q : ℕ) (η T M R : ℝ),
      1 ≤ N → (∀ i∈S, H i ≤ N) →
      0 < η → η ≤ 1/8 → 0 < T → 0 < M → 0 < R →
      (∀ i∈S, y i∈Icc (1:ℝ) 2) →
      (∀ i∈S, (L i:ℝ)-2*(N:ℝ)∈Icc M (2*M)) →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ J) →
      (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c) →
      T*(N:ℝ)*R^2=M^3 →
      7*(N:ℝ)+2 ≤ M/4 →
      (3*J/σ)*(6*(N:ℝ)+1)^4 ≤ M*(N:ℝ)*R^2 →
      (3*J/(4*σ))*(6*(N:ℝ)+1)^2 ≤ (N:ℝ)*R^2 →
      Q ≤ N →
      let f := fun i w => T*(F (w/M)-F (w/M+η*y i))/(σ*η)
      (∀ i∈S, za i∈Ioo ((L i:ℝ)-2*(N:ℝ)-(N:ℝ)/8)
        ((L i:ℝ)-2*(N:ℝ)+(N:ℝ)/8) ∧
        iteratedDeriv 2 (f i) (za i)/2=(anchor i:ℝ)) →
      ∀ (Acut : ℕ) (Bmajor : ℝ), 2 ≤ Acut → 128*σ ≤ Bmajor →
      let Good := fun i => Acut*(anchor i).den ≤ Q ∧
        Bmajor*R^2 ≤ c*(Q:ℝ)*(anchor i).den
      let G := S.filter Good
      ∃ (r : ι → ℚ) (z : ι → ℝ),
      (∀ i∈G, (r i).den ≤ Q ∧ Q ≤ 2*(r i).den ∧
        (anchor i:ℝ) < r i ∧ |(r i:ℝ)-(anchor i:ℝ)| ≤ c/(64*σ*R^2) ∧
        z i∈Icc (za i) (za i+(N:ℝ)/16) ∧
        iteratedDeriv 2 (f i) (z i)/2=(r i:ℝ)) ∧
      let m := fun i => round (z i)
      let A := fun i => (L i-m i).toNat
      let q := fun i => (r i).den
      let μ := fun i => iteratedDeriv 3 (f i) (m i)/6
      let ℓ := fun i => deriv (f i) (m i)
      let U₃ := J/(2*σ*(N:ℝ)*R^2)
      (∀ i∈G, |z i-(m i:ℝ)| ≤ 1/2 ∧
        N ≤ A i ∧ A i ≤ 3*N ∧ m i+(A i:ℤ)=L i) ∧
      ∀ (K₀ : ℕ) [NeZero K₀], 63*U₃*(Q:ℝ)*(N:ℝ)^2 ≤ K₀ →
      ∃ v : ι → ℤ, (∀ i∈G, (q i:ℤ) ∣ (r i).num*v i-1) ∧
      let b := fun i (p : Fin 2) => (⌊(q i:ℝ)*ℓ i⌋+(p:ℕ) : ℤ)
      let τ := fun i p => ((b i p:ℝ)-(q i:ℝ)*ℓ i)/2
      let s := fun i => Real.sqrt (2/(3*μ i*(q i:ℝ)))
      let K := fun i => -2*μ i*(s i)^3
      let x := fun i p =>
        (![-(v i:ℝ)*b i p/q i,-(v i:ℝ)/q i,K i,3*K i*τ i p/2] : Fin 4 → ℝ)
      ∃ k : ZMod K₀,
        (∑ i∈S, ‖∑ n∈Finset.Ioc (L i) (L i+H i),(𝐞 (f i n):ℂ)‖) ≤
          C*((∑ i∈S.filter (fun i => ¬ Good i),(H i:ℝ))+
            (1+Real.log K₀)*
            (∑ i∈G, ∑ p : Fin 2,
              (Real.sqrt (2*(q i:ℝ))/((q i:ℝ)*Real.sqrt (μ i*A i)))*
              ‖∑ j : ZMod K₀,ZMod.stdAddChar (-(j*k))*
                GafniTao.fordAdditiveCharacter (∑ d,x i p d*
                  (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
                    Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖)+
            ∑ i∈G, (Real.sqrt (A i)*Real.log (2*(A i:ℝ))+1/(μ i*(A i:ℝ)^2))) := by
  classical
  obtain ⟨C,hC,hentry⟩ := positive_difference_dyadic_anchor_source_fourier hσ hc hJ
  refine ⟨C,hC,?_⟩
  intro ι S F y L H anchor za N Q η T M R hN hH hη hηmax hT hM hR
    hy hbase hf hbound hnegative hphase hbuffer hfourBudget hquadBudget
    hQN f hanchors Acut Bmajor hAcut hBmajor Good G
  have hGS : G ⊆ S := fun i hi => (Finset.mem_filter.mp hi).1
  obtain ⟨r,z,hr,hconsumer⟩ := hentry ι G F y L H anchor za N Q η T M R hN
    (fun i hi => hH i (hGS hi)) hη hηmax hT hM hR
    (fun i hi => hy i (hGS hi)) (fun i hi => hbase i (hGS hi)) hf hbound hnegative
    hphase hbuffer hfourBudget hquadBudget hQN
    (fun i hi => (Nat.mul_le_mul_right _ hAcut).trans (Finset.mem_filter.mp hi).2.1)
    (fun i hi => (mul_le_mul_of_nonneg_right hBmajor (sq_nonneg R)).trans
      (Finset.mem_filter.mp hi).2.2)
    (fun i hi => hanchors i (hGS hi))
  refine ⟨r,z,hr,?_⟩
  intro m A q μ ℓ U₃
  obtain ⟨hgeo,hcomplete⟩ := hconsumer
  refine ⟨hgeo,?_⟩
  intro K₀ inst hK₀
  obtain ⟨v,hv,hfourier⟩ := hcomplete K₀ hK₀
  refine ⟨v,hv,?_⟩
  intro b τ s K x
  obtain ⟨k,hk⟩ := hfourier
  refine ⟨k,?_⟩
  let Src := fun i => ‖∑ n∈Finset.Ioc (L i) (L i+H i),(𝐞 (f i n):ℂ)‖
  let Bad := S.filter (fun i => ¬ Good i)
  have hbad : (∑ i∈Bad,Src i) ≤ ∑ i∈Bad,(H i:ℝ) := by
    apply Finset.sum_le_sum
    intro i _hi
    dsimp only [Src]
    apply (norm_sum_le _ _).trans_eq
    simp
  have hbad0 : 0 ≤ ∑ i∈Bad,(H i:ℝ) :=
    Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  have hbadC := mul_le_mul_of_nonneg_right hC hbad0
  simp only [one_mul] at hbadC
  have hsplit : (∑ i∈S,Src i)=(∑ i∈G,Src i)+(∑ i∈Bad,Src i) :=
    (Finset.sum_filter_add_sum_filter_not S Good Src).symm
  change (∑ i∈S,Src i) ≤ _
  rw [hsplit]
  have hh := add_le_add hk (hbad.trans hbadC)
  convert hh using 1
  dsimp only [Bad]
  ring

theorem positive_difference_dyadic_anchor_source_partition
    {σ c J : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J) :
    ∃ C ≥ (1:ℝ), ∀ (ι : Type*) (S : Finset ι) (F : ℝ → ℝ)
      (y : ι → ℝ) (L : ι → ℤ) (H : ι → ℕ) (anchor : ι → ℚ) (za : ι → ℝ)
      (N Q : ℕ) (η T M R : ℝ),
      1 ≤ N → (∀ i∈S, H i ≤ N) →
      0 < η → η ≤ 1/8 → 0 < T → 0 < M → 0 < R →
      (∀ i∈S, y i∈Icc (1:ℝ) 2) →
      (∀ i∈S, (L i:ℝ)-2*(N:ℝ)∈Icc M (2*M)) →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ J) →
      (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c) →
      T*(N:ℝ)*R^2=M^3 →
      7*(N:ℝ)+2 ≤ M/4 →
      (3*J/σ)*(6*(N:ℝ)+1)^4 ≤ M*(N:ℝ)*R^2 →
      (3*J/(4*σ))*(6*(N:ℝ)+1)^2 ≤ (N:ℝ)*R^2 →
      Q ≤ N →
      let f := fun i w => T*(F (w/M)-F (w/M+η*y i))/(σ*η)
      (∀ i∈S, za i∈Ioo ((L i:ℝ)-2*(N:ℝ)-(N:ℝ)/8)
        ((L i:ℝ)-2*(N:ℝ)+(N:ℝ)/8) ∧
        iteratedDeriv 2 (f i) (za i)/2=(anchor i:ℝ)) →
      let Good := fun i => 2*(anchor i).den ≤ Q ∧
        128*σ*R^2 ≤ c*(Q:ℝ)*(anchor i).den
      let G := S.filter Good
      ∃ (r : ι → ℚ) (z : ι → ℝ),
      (∀ i∈G, (r i).den ≤ Q ∧ Q ≤ 2*(r i).den ∧
        (anchor i:ℝ) < r i ∧ |(r i:ℝ)-(anchor i:ℝ)| ≤ c/(64*σ*R^2) ∧
        z i∈Icc (za i) (za i+(N:ℝ)/16) ∧
        iteratedDeriv 2 (f i) (z i)/2=(r i:ℝ)) ∧
      let m := fun i => round (z i)
      let A := fun i => (L i-m i).toNat
      let q := fun i => (r i).den
      let μ := fun i => iteratedDeriv 3 (f i) (m i)/6
      let ℓ := fun i => deriv (f i) (m i)
      let U₃ := J/(2*σ*(N:ℝ)*R^2)
      (∀ i∈G, |z i-(m i:ℝ)| ≤ 1/2 ∧
        N ≤ A i ∧ A i ≤ 3*N ∧ m i+(A i:ℤ)=L i) ∧
      ∀ (K₀ : ℕ) [NeZero K₀], 63*U₃*(Q:ℝ)*(N:ℝ)^2 ≤ K₀ →
      ∃ v : ι → ℤ, (∀ i∈G, (q i:ℤ) ∣ (r i).num*v i-1) ∧
      let b := fun i (p : Fin 2) => (⌊(q i:ℝ)*ℓ i⌋+(p:ℕ) : ℤ)
      let τ := fun i p => ((b i p:ℝ)-(q i:ℝ)*ℓ i)/2
      let s := fun i => Real.sqrt (2/(3*μ i*(q i:ℝ)))
      let K := fun i => -2*μ i*(s i)^3
      let x := fun i p =>
        (![-(v i:ℝ)*b i p/q i,-(v i:ℝ)/q i,K i,3*K i*τ i p/2] : Fin 4 → ℝ)
      ∃ k : ZMod K₀,
        (∑ i∈S, ‖∑ n∈Finset.Ioc (L i) (L i+H i),(𝐞 (f i n):ℂ)‖) ≤
          C*((∑ i∈S.filter (fun i => ¬ Good i),(H i:ℝ))+
            (1+Real.log K₀)*
            (∑ i∈G, ∑ p : Fin 2,
              (Real.sqrt (2*(q i:ℝ))/((q i:ℝ)*Real.sqrt (μ i*A i)))*
              ‖∑ j : ZMod K₀,ZMod.stdAddChar (-(j*k))*
                GafniTao.fordAdditiveCharacter (∑ d,x i p d*
                  (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
                    Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖)+
            ∑ i∈G, (Real.sqrt (A i)*Real.log (2*(A i:ℝ))+1/(μ i*(A i:ℝ)^2))) := by
  obtain ⟨C,hC,hentry⟩ := positive_difference_dyadic_anchor_source_partition_cutoffs hσ hc hJ
  refine ⟨C,hC,?_⟩
  intro ι S F y L H anchor za N Q η T M R hN hH hη hηmax hT hM hR
    hy hbase hf hbound hnegative hphase hbuffer hfourBudget hquadBudget hQN f hanchors
  exact hentry ι S F y L H anchor za N Q η T M R hN hH hη hηmax hT hM hR
    hy hbase hf hbound hnegative hphase hbuffer hfourBudget hquadBudget hQN hanchors
    2 (128*σ) (by norm_num) le_rfl

private theorem positive_difference_tagged_gap_dyadic_source_fourier_cutoffs
    {σ c J : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J) :
    ∃ C ≥ (1:ℝ), ∀ (ι : Type*) (Y : Finset ι) (F : ℝ → ℝ)
      (N : ℕ) (s : ℤ) (H : ι → ℤ → ℕ)
      (η T M R U : ℝ) (y x₁ x₂ : ι → ℝ),
      1 ≤ N → (∀ i∈Y, ∀ k, H i k ≤ N) →
      0 < η → η ≤ 1/8 → (∀ i∈Y, y i∈Icc (1:ℝ) 2) →
      0 < T → 0 < M → 0 < R → 0 < U →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ J) →
      (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c) →
      T*(N:ℝ)*R^2=M^3 → 7*(N:ℝ)+2 ≤ M/4 →
      (3*J/σ)*(6*(N:ℝ)+1)^4 ≤ M*(N:ℝ)*R^2 →
      (3*J/(4*σ))*(6*(N:ℝ)+1)^2 ≤ (N:ℝ)*R^2 →
      3*J ≤ σ*U →
      (∀ i∈Y, x₁ i∈Icc M (2*M)) → (∀ i∈Y, x₂ i∈Icc M (2*M)) →
      let f := fun i w => T*(F (w/M)-F (w/M+η*y i))/(σ*η)
      let h := fun i w => iteratedDeriv 2 (f i) w/2
      let t := fun k : ℤ => (s:ℝ)+(N:ℝ)*k
      let L := fun k : ℤ => s+(N:ℤ)*k+2*(N:ℤ)
      let delta := c/(64*σ*R^2)
      let Vbound := 3*J*M/(2*σ*(N:ℝ)*R^2)
      (∀ i∈Y, U/(4*R^2) ≤ h i (x₂ i)-h i (x₁ i) ∧
        h i (x₂ i)-h i (x₁ i) ≤ 7*U/(2*R^2)) →
      ∃ (S : ι → Finset ℤ) (anchor : ι → ℤ → ℚ) (za : ι → ℤ → ℝ),
        (∀ i∈Y,
          (∀ k : ℤ, k∈(S i) ↔ (x₁ i)+(N:ℝ)/4 ≤ t k ∧ t k ≤ (x₂ i)-(N:ℝ)/4) ∧
        (∀ k∈(S i), (za i) k∈Ioo (x₁ i) (x₂ i) ∧ (h i) ((za i) k)=((anchor i) k:ℝ) ∧
          ((anchor i) k:ℝ)∈Ioo ((h i) (x₁ i)) ((h i) (x₂ i)) ∧
          ((anchor i) k:ℝ)∈Ioo ((h i) (t k)-delta) ((h i) (t k)+delta) ∧
          ∀ a : ℚ, (a:ℝ)∈Ioo ((h i) (t k)-delta) ((h i) (t k)+delta) → ((anchor i) k).den ≤ a.den) ∧
        (∀ k∈(S i), |(za i) k-t k| ≤ (N:ℝ)/16) ∧
        (σ/(6*J))*U-3/2 ≤ ((S i).card:ℝ) ∧ ((S i).card:ℝ) ≤ (56*σ/c)*U+1/2 ∧
        (∀ Q : ℕ, 2 ≤ Q →
          let D := 64*σ*R^2/(c*(Q:ℝ))
          (((S i).filter (fun k => Q ≤ ((anchor i) k).den)).card:ℝ) ≤
            4*(Vbound+1)*D^2+D*(2+Real.log (D+1)))) ∧
      ∀ Q : ℕ, Q ≤ N →
      ∀ (Acut : ℕ) (Bmajor : ℝ), 2 ≤ Acut → 128*σ ≤ Bmajor →
      let Sall := Y.biUnion (fun i => (S i).image (fun k => (i,k)))
      let Good := fun i => Acut*(anchor i.1 i.2).den ≤ Q ∧
        Bmajor*R^2 ≤ c*(Q:ℝ)*(anchor i.1 i.2).den
      let G := Sall.filter Good
      ∃ (r : ι × ℤ → ℚ) (z : ι × ℤ → ℝ),
      (∀ i∈G, (r i).den ≤ Q ∧ Q ≤ 2*(r i).den ∧
        (anchor i.1 i.2:ℝ) < r i ∧ |(r i:ℝ)-(anchor i.1 i.2:ℝ)| ≤ c/(64*σ*R^2) ∧
        z i∈Icc (za i.1 i.2) (za i.1 i.2+(N:ℝ)/16) ∧
        iteratedDeriv 2 (f i.1) (z i)/2=(r i:ℝ)) ∧
      (∀ i∈G, z i∈Ioo (x₁ i.1) (x₂ i.1)) ∧
      let m := fun i => round (z i)
      let A := fun i => (L i.2-m i).toNat
      let q := fun i => (r i).den
      let μ := fun i => iteratedDeriv 3 (f i.1) (m i)/6
      let ℓ := fun i => deriv (f i.1) (m i)
      let U₃ := J/(2*σ*(N:ℝ)*R^2)
      (∀ i∈G, |z i-(m i:ℝ)| ≤ 1/2 ∧
        N ≤ A i ∧ A i ≤ 3*N ∧ m i+(A i:ℤ)=L i.2) ∧
      ∀ (K₀ : ℕ) [NeZero K₀], 63*U₃*(Q:ℝ)*(N:ℝ)^2 ≤ K₀ →
      ∃ v : ι × ℤ → ℤ, (∀ i∈G, (q i:ℤ) ∣ (r i).num*v i-1) ∧
      let b := fun i (p : Fin 2) => (⌊(q i:ℝ)*ℓ i⌋+(p:ℕ) : ℤ)
      let τ := fun i p => ((b i p:ℝ)-(q i:ℝ)*ℓ i)/2
      let s := fun i => Real.sqrt (2/(3*μ i*(q i:ℝ)))
      let K := fun i => -2*μ i*(s i)^3
      let x := fun i p =>
        (![-(v i:ℝ)*b i p/q i,-(v i:ℝ)/q i,K i,3*K i*τ i p/2] : Fin 4 → ℝ)
      ∃ k : ZMod K₀,
        (∑ i∈Sall, ‖∑ n∈Finset.Ioc (L i.2) (L i.2+H i.1 i.2),(𝐞 (f i.1 n):ℂ)‖) ≤
          C*((∑ i∈Sall.filter (fun i => ¬ Good i),(H i.1 i.2:ℝ))+
            (1+Real.log K₀)*
            (∑ i∈G, ∑ p : Fin 2,
              (Real.sqrt (2*(q i:ℝ))/((q i:ℝ)*Real.sqrt (μ i*A i)))*
              ‖∑ j : ZMod K₀,ZMod.stdAddChar (-(j*k))*
                GafniTao.fordAdditiveCharacter (∑ d,x i p d*
                  (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
                    Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖)+
            ∑ i∈G, (Real.sqrt (A i)*Real.log (2*(A i:ℝ))+1/(μ i*(A i:ℝ)^2))) := by
  classical
  obtain ⟨C,hC,hentry⟩ := positive_difference_dyadic_anchor_source_partition_cutoffs hσ hc hJ
  obtain ⟨_Cgap,_hCgap,hgapEntry⟩ := positive_difference_interior_gap_dyadic_source_fourier hσ hc hJ
  refine ⟨C,hC,?_⟩
  intro ι Y F N s H η T M R U y x₁ x₂ hN hH hη hηmax hy hT hM hR hU
    hf hbound hnegative hphase hbuffer hfourBudget hquadBudget hUlarge hx₁ hx₂
    f h t L delta Vbound hgap
  let Data (i : ι) (Si : Finset ℤ) (ai : ℤ → ℚ) (zi : ℤ → ℝ) : Prop :=
    (∀ k : ℤ, k∈Si ↔ (x₁ i)+(N:ℝ)/4 ≤ t k ∧ t k ≤ (x₂ i)-(N:ℝ)/4) ∧
        (∀ k∈Si, zi k∈Ioo (x₁ i) (x₂ i) ∧ (h i) (zi k)=(ai k:ℝ) ∧
          (ai k:ℝ)∈Ioo ((h i) (x₁ i)) ((h i) (x₂ i)) ∧
          (ai k:ℝ)∈Ioo ((h i) (t k)-delta) ((h i) (t k)+delta) ∧
          ∀ a : ℚ, (a:ℝ)∈Ioo ((h i) (t k)-delta) ((h i) (t k)+delta) → (ai k).den ≤ a.den) ∧
        (∀ k∈Si, |zi k-t k| ≤ (N:ℝ)/16) ∧
        (σ/(6*J))*U-3/2 ≤ (Si.card:ℝ) ∧ (Si.card:ℝ) ≤ (56*σ/c)*U+1/2 ∧
        (∀ Q : ℕ, 2 ≤ Q →
          let D := 64*σ*R^2/(c*(Q:ℝ))
          ((Si.filter (fun k => Q ≤ (ai k).den)).card:ℝ) ≤
            4*(Vbound+1)*D^2+D*(2+Real.log (D+1)))
  have hex : ∀ i∈Y, ∃ Si ai zi, Data i Si ai zi := by
    intro i hi
    obtain ⟨Si,ai,zi,hmem,hdata,hdist,hcardlow,hcardup,htail,_hfourier⟩ :=
      hgapEntry F N s (H i) η (y i) T M R U (x₁ i) (x₂ i)
        hN (hH i hi) hη hηmax (hy i hi) hT hM hR hU hf hbound hnegative
        hphase hbuffer hfourBudget hquadBudget hUlarge (hx₁ i hi) (hx₂ i hi)
        (hgap i hi).1 (hgap i hi).2
    exact ⟨Si,ai,zi,hmem,hdata,hdist,hcardlow,hcardup,htail⟩
  choose! S anchor za hinfo using hex
  refine ⟨S,anchor,za,hinfo,?_⟩
  intro Q hQN Acut Bmajor hAcut hBmajor Sall Good G
  have hNp : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hmem (j : ι × ℤ) : j∈Sall ↔ j.1∈Y ∧ j.2∈S j.1 := by
    constructor
    · intro hj
      obtain ⟨i,hi,hj⟩ := Finset.mem_biUnion.mp hj
      obtain ⟨k,hk,he⟩ := Finset.mem_image.mp hj
      subst j
      exact ⟨hi,hk⟩
    · rintro ⟨hi,hj⟩
      exact Finset.mem_biUnion.mpr ⟨j.1,hi,Finset.mem_image.mpr ⟨j.2,hj,rfl⟩⟩
  have hL k : (L k:ℝ)-2*(N:ℝ)=t k := by
    dsimp only [L,t]
    push_cast
    ring
  have hbase j (hj : j∈Sall) : (L j.2:ℝ)-2*(N:ℝ)∈Icc M (2*M) := by
    rw [hL]
    obtain ⟨hi,hk⟩ := (hmem j).mp hj
    have hg := ((hinfo j.1 hi).1 j.2).mp hk
    constructor <;> linarith only [hg.1,hg.2,(hx₁ j.1 hi).1,(hx₂ j.1 hi).2,hNp]
  have hanchors j (hj : j∈Sall) :
      za j.1 j.2∈Ioo ((L j.2:ℝ)-2*(N:ℝ)-(N:ℝ)/8)
        ((L j.2:ℝ)-2*(N:ℝ)+(N:ℝ)/8) ∧
      iteratedDeriv 2 (f j.1) (za j.1 j.2)/2=(anchor j.1 j.2:ℝ) := by
    obtain ⟨hi,hk⟩ := (hmem j).mp hj
    refine ⟨?_,((hinfo j.1 hi).2.1 j.2 hk).2.1⟩
    rw [hL]
    have hh := abs_le.mp ((hinfo j.1 hi).2.2.1 j.2 hk)
    constructor <;> linarith only [hh.1,hh.2,hNp]
  obtain ⟨r,z,hr,hfourier⟩ := hentry (ι × ℤ) Sall F (fun j => y j.1)
    (fun j => L j.2) (fun j => H j.1 j.2) (fun j => anchor j.1 j.2) (fun j => za j.1 j.2)
    N Q η T M R hN (fun j hj => hH j.1 ((hmem j).mp hj).1 j.2)
    hη hηmax hT hM hR (fun j hj => hy j.1 ((hmem j).mp hj).1) hbase hf hbound hnegative
    hphase hbuffer hfourBudget hquadBudget hQN hanchors Acut Bmajor hAcut hBmajor
  refine ⟨r,z,hr,?_,hfourier⟩
  intro j hj
  obtain ⟨hi,hk⟩ := (hmem j).mp (Finset.mem_filter.mp hj).1
  have hh := abs_le.mp ((hinfo j.1 hi).2.2.1 j.2 hk)
  have hg := ((hinfo j.1 hi).1 j.2).mp hk
  have hz := (hr j hj).2.2.2.2.1
  constructor <;> linarith only [hh.1,hh.2,hg.1,hg.2,hz.1,hz.2,hNp]

theorem positive_difference_tagged_gap_dyadic_source_fourier
    {σ c J : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J) :
    ∃ C ≥ (1:ℝ), ∀ (ι : Type*) (Y : Finset ι) (F : ℝ → ℝ)
      (N : ℕ) (s : ℤ) (H : ι → ℤ → ℕ)
      (η T M R U : ℝ) (y x₁ x₂ : ι → ℝ),
      1 ≤ N → (∀ i∈Y, ∀ k, H i k ≤ N) →
      0 < η → η ≤ 1/8 → (∀ i∈Y, y i∈Icc (1:ℝ) 2) →
      0 < T → 0 < M → 0 < R → 0 < U →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ J) →
      (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c) →
      T*(N:ℝ)*R^2=M^3 → 7*(N:ℝ)+2 ≤ M/4 →
      (3*J/σ)*(6*(N:ℝ)+1)^4 ≤ M*(N:ℝ)*R^2 →
      (3*J/(4*σ))*(6*(N:ℝ)+1)^2 ≤ (N:ℝ)*R^2 →
      3*J ≤ σ*U →
      (∀ i∈Y, x₁ i∈Icc M (2*M)) → (∀ i∈Y, x₂ i∈Icc M (2*M)) →
      let f := fun i w => T*(F (w/M)-F (w/M+η*y i))/(σ*η)
      let h := fun i w => iteratedDeriv 2 (f i) w/2
      let t := fun k : ℤ => (s:ℝ)+(N:ℝ)*k
      let L := fun k : ℤ => s+(N:ℤ)*k+2*(N:ℤ)
      let delta := c/(64*σ*R^2)
      let Vbound := 3*J*M/(2*σ*(N:ℝ)*R^2)
      (∀ i∈Y, U/(4*R^2) ≤ h i (x₂ i)-h i (x₁ i) ∧
        h i (x₂ i)-h i (x₁ i) ≤ 7*U/(2*R^2)) →
      ∃ (S : ι → Finset ℤ) (anchor : ι → ℤ → ℚ) (za : ι → ℤ → ℝ),
        (∀ i∈Y,
          (∀ k : ℤ, k∈(S i) ↔ (x₁ i)+(N:ℝ)/4 ≤ t k ∧ t k ≤ (x₂ i)-(N:ℝ)/4) ∧
        (∀ k∈(S i), (za i) k∈Ioo (x₁ i) (x₂ i) ∧ (h i) ((za i) k)=((anchor i) k:ℝ) ∧
          ((anchor i) k:ℝ)∈Ioo ((h i) (x₁ i)) ((h i) (x₂ i)) ∧
          ((anchor i) k:ℝ)∈Ioo ((h i) (t k)-delta) ((h i) (t k)+delta) ∧
          ∀ a : ℚ, (a:ℝ)∈Ioo ((h i) (t k)-delta) ((h i) (t k)+delta) → ((anchor i) k).den ≤ a.den) ∧
        (∀ k∈(S i), |(za i) k-t k| ≤ (N:ℝ)/16) ∧
        (σ/(6*J))*U-3/2 ≤ ((S i).card:ℝ) ∧ ((S i).card:ℝ) ≤ (56*σ/c)*U+1/2 ∧
        (∀ Q : ℕ, 2 ≤ Q →
          let D := 64*σ*R^2/(c*(Q:ℝ))
          (((S i).filter (fun k => Q ≤ ((anchor i) k).den)).card:ℝ) ≤
            4*(Vbound+1)*D^2+D*(2+Real.log (D+1)))) ∧
      ∀ Q : ℕ, Q ≤ N →
      let Sall := Y.biUnion (fun i => (S i).image (fun k => (i,k)))
      let Good := fun i => 2*(anchor i.1 i.2).den ≤ Q ∧
        128*σ*R^2 ≤ c*(Q:ℝ)*(anchor i.1 i.2).den
      let G := Sall.filter Good
      ∃ (r : ι × ℤ → ℚ) (z : ι × ℤ → ℝ),
      (∀ i∈G, (r i).den ≤ Q ∧ Q ≤ 2*(r i).den ∧
        (anchor i.1 i.2:ℝ) < r i ∧ |(r i:ℝ)-(anchor i.1 i.2:ℝ)| ≤ c/(64*σ*R^2) ∧
        z i∈Icc (za i.1 i.2) (za i.1 i.2+(N:ℝ)/16) ∧
        iteratedDeriv 2 (f i.1) (z i)/2=(r i:ℝ)) ∧
      (∀ i∈G, z i∈Ioo (x₁ i.1) (x₂ i.1)) ∧
      let m := fun i => round (z i)
      let A := fun i => (L i.2-m i).toNat
      let q := fun i => (r i).den
      let μ := fun i => iteratedDeriv 3 (f i.1) (m i)/6
      let ℓ := fun i => deriv (f i.1) (m i)
      let U₃ := J/(2*σ*(N:ℝ)*R^2)
      (∀ i∈G, |z i-(m i:ℝ)| ≤ 1/2 ∧
        N ≤ A i ∧ A i ≤ 3*N ∧ m i+(A i:ℤ)=L i.2) ∧
      ∀ (K₀ : ℕ) [NeZero K₀], 63*U₃*(Q:ℝ)*(N:ℝ)^2 ≤ K₀ →
      ∃ v : ι × ℤ → ℤ, (∀ i∈G, (q i:ℤ) ∣ (r i).num*v i-1) ∧
      let b := fun i (p : Fin 2) => (⌊(q i:ℝ)*ℓ i⌋+(p:ℕ) : ℤ)
      let τ := fun i p => ((b i p:ℝ)-(q i:ℝ)*ℓ i)/2
      let s := fun i => Real.sqrt (2/(3*μ i*(q i:ℝ)))
      let K := fun i => -2*μ i*(s i)^3
      let x := fun i p =>
        (![-(v i:ℝ)*b i p/q i,-(v i:ℝ)/q i,K i,3*K i*τ i p/2] : Fin 4 → ℝ)
      ∃ k : ZMod K₀,
        (∑ i∈Sall, ‖∑ n∈Finset.Ioc (L i.2) (L i.2+H i.1 i.2),(𝐞 (f i.1 n):ℂ)‖) ≤
          C*((∑ i∈Sall.filter (fun i => ¬ Good i),(H i.1 i.2:ℝ))+
            (1+Real.log K₀)*
            (∑ i∈G, ∑ p : Fin 2,
              (Real.sqrt (2*(q i:ℝ))/((q i:ℝ)*Real.sqrt (μ i*A i)))*
              ‖∑ j : ZMod K₀,ZMod.stdAddChar (-(j*k))*
                GafniTao.fordAdditiveCharacter (∑ d,x i p d*
                  (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
                    Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖)+
            ∑ i∈G, (Real.sqrt (A i)*Real.log (2*(A i:ℝ))+1/(μ i*(A i:ℝ)^2))) := by
  obtain ⟨C,hC,hentry⟩ := positive_difference_tagged_gap_dyadic_source_fourier_cutoffs hσ hc hJ
  refine ⟨C,hC,?_⟩
  intro ι Y F N s H η T M R U y x₁ x₂ hN hH hη hηmax hy hT hM hR hU
    hf hbound hnegative hphase hbuffer hfourBudget hquadBudget hUlarge hx₁ hx₂
    f h t L delta Vbound hgap
  obtain ⟨S,anchor,za,hinfo,hfourier⟩ :=
    hentry ι Y F N s H η T M R U y x₁ x₂ hN hH hη hηmax hy hT hM hR hU
      hf hbound hnegative hphase hbuffer hfourBudget hquadBudget hUlarge hx₁ hx₂ hgap
  refine ⟨S,anchor,za,hinfo,?_⟩
  intro Q hQN
  exact hfourier Q hQN 2 (128*σ) (by norm_num) le_rfl

private theorem tagged_cost_source_scale
    {a N C D Q L cost : ℝ}
    (ha : 0 ≤ a) (hN : 0 < N) (hQ : 0 < Q)
    (hcost : cost ≤ C*(D/(N*Q))*L) :
    a*N*cost ≤ a*C*(D/Q)*L := by
  calc
    _ ≤ a*N*(C*(D/(N*Q))*L) :=
      mul_le_mul_of_nonneg_left hcost (mul_nonneg ha hN.le)
    _ = _ := by field_simp

private theorem tagged_anchor_complement_grouped_count
    {ι : Type*} [DecidableEq ι] (Y : Finset ι) (S : ι → Finset ℤ)
    (F : ℝ → ℝ) (y : ι → ℝ) (anchor : ι → ℤ → ℚ)
    (N : ℕ) (s : ℝ) {σ c J η T M R : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J)
    (hη : 0 < η) (hηmax : η ≤ 1/8) (hy : ∀ i∈Y, y i∈Icc (1:ℝ) 2)
    (hf : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hbound : ∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ J)
    (htests : ∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
        (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|)
    (hnegative : ∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hphase : T*(N:ℝ)*R^2=M^3)
    (hpoints : ∀ i∈Y, ∀ k∈S i, s+(N:ℝ)*k∈Icc M (2*M))
    (hdisjoint : ∀ i∈Y, ∀ j∈Y, i≠j → y i=y j → Disjoint (S i) (S j)) :
    let f := fun u w => T*(F (w/M)-F (w/M+η*u))/(σ*η)
    let h := fun u w => iteratedDeriv 2 (f u) w/2
    let t := fun k : ℤ => s+(N:ℝ)*k
    let delta := c/(64*σ*R^2)
    let Vbound := 3*J*M/(2*σ*(N:ℝ)*R^2)
    (∀ i∈Y, ∀ k∈S i,
      (anchor i k:ℝ)∈Ioo (h (y i) (t k)-delta) (h (y i) (t k)+delta) ∧
      ∀ a : ℚ, (a:ℝ)∈Ioo (h (y i) (t k)-delta) (h (y i) (t k)+delta) →
        (anchor i k).den ≤ a.den) →
    ∀ (Q Acut : ℕ) (Bmajor : ℝ), 2 ≤ Acut → Acut ≤ Q → 0 ≤ Bmajor →
      let Sall := Y.biUnion (fun i => (S i).image (fun k => (i,k)))
      let Good : ι × ℤ → Prop := fun p => Acut*(anchor p.1 p.2).den ≤ Q ∧
        Bmajor*R^2 ≤ c*(Q:ℝ)*(anchor p.1 p.2).den
      let Dlow := Bmajor*R^2/(c*(Q:ℝ))
      let Dhigh := 64*σ*R^2/(c*((Q/Acut+1:ℕ):ℝ))
      let Cost := 4*Vbound*Dhigh^2+3*Dhigh*(2+Real.log (Dhigh+1))+
        Dlow*(2*(Vbound+delta)*Dlow+1)
      ((Sall.filter (fun p => ¬ Good p)).card:ℝ) ≤ ((Y.image y).card:ℝ)*Cost ∧
      ∀ H : ι → ℤ → ℕ, (∀ i∈Y, ∀ k∈S i, H i k ≤ N) →
        (∑ p∈Sall.filter (fun p => ¬ Good p),(H p.1 p.2:ℝ)) ≤
          ((Y.image y).card:ℝ)*(N:ℝ)*Cost := by
  classical
  intro f h t delta Vbound hanchors Q Acut Bmajor hA hAQ hB Sall Good Dlow Dhigh Cost
  let Phases := Y.image y
  let P := Sall.filter (fun p => ¬ Good p)
  let Grid := fun u => (Y.filter (fun i => y i=u)).biUnion S
  have hgrid u k : k∈Grid u ↔ ∃ i∈Y, y i=u ∧ k∈S i := by
    constructor
    · intro hk
      obtain ⟨i,hi,hk⟩ := Finset.mem_biUnion.mp hk
      exact ⟨i,(Finset.mem_filter.mp hi).1,(Finset.mem_filter.mp hi).2,hk⟩
    · rintro ⟨i,hi,hu,hk⟩
      exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_filter.mpr ⟨hi,hu⟩,hk⟩
  let ag := fun u k => if hh : ∃ i∈Y, y i=u ∧ k∈S i then
    anchor (Classical.choose hh) k else (0:ℚ)
  have hag i (hi : i∈Y) k (hk : k∈S i) : ag (y i) k=anchor i k := by
    have hex : ∃ j∈Y, y j=y i ∧ k∈S j := ⟨i,hi,rfl,hk⟩
    dsimp only [ag]
    rw [dif_pos hex]
    have hh := Classical.choose_spec hex
    have he : Classical.choose hex=i := by
      by_contra hne
      exact Finset.disjoint_left.mp
        (hdisjoint _ hh.1 i hi hne hh.2.1) hh.2.2 hk
    rw [he]
  have hmem p : p∈Sall ↔ p.1∈Y ∧ p.2∈S p.1 := by
    constructor
    · intro hp
      obtain ⟨i,hi,hp⟩ := Finset.mem_biUnion.mp hp
      obtain ⟨k,hk,he⟩ := Finset.mem_image.mp hp
      subst p
      exact ⟨hi,hk⟩
    · rintro ⟨hi,hk⟩
      exact Finset.mem_biUnion.mpr ⟨p.1,hi,Finset.mem_image.mpr ⟨p.2,hk,rfl⟩⟩
  have hGcount u (hu : u∈Phases) :
      ((Grid u).filter (fun k => ¬ (Acut*(ag u k).den ≤ Q ∧
        Bmajor*R^2 ≤ c*(Q:ℝ)*(ag u k).den))).card ≤ (Cost:ℝ) := by
    have hyp : u∈Icc (1:ℝ) 2 := by
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hu
      exact hy i hi
    have hpts k (hk : k∈Grid u) : t k∈Icc M (2*M) := by
      obtain ⟨i,hi,_hui,hk⟩ := (hgrid u k).mp hk
      exact hpoints i hi k hk
    have hanc k (hk : k∈Grid u) :
        (ag u k:ℝ)∈Ioo (h u (t k)-delta) (h u (t k)+delta) ∧
        ∀ a : ℚ, (a:ℝ)∈Ioo (h u (t k)-delta) (h u (t k)+delta) →
          (ag u k).den ≤ a.den := by
      obtain ⟨i,hi,hui,hk⟩ := (hgrid u k).mp hk
      rw [←hui,hag i hi k hk]
      exact hanchors i hi k hk
    exact (positive_difference_minimal_anchor_complement_count (Grid u) F (ag u) N s
      hσ hc hJ hη hηmax hyp hf hbound htests hnegative hT hM hN hR hphase
      hpts hanc Q Acut Bmajor hA hAQ hB).1
  have hfiber u (hu : u∈Phases) :
      ((P.filter (fun p => y p.1=u)).card:ℝ) ≤ Cost := by
    let V := P.filter (fun p => y p.1=u)
    have hdata p (hp : p∈V) : p.1∈Y ∧ p.2∈S p.1 ∧ ¬ Good p ∧ y p.1=u := by
      have hh := Finset.mem_filter.mp hp
      have hpP := Finset.mem_filter.mp hh.1
      have hm := (hmem p).mp hpP.1
      exact ⟨hm.1,hm.2,hpP.2,hh.2⟩
    have hinj : Set.InjOn Prod.snd (V:Set (ι × ℤ)) := by
      intro p hp q hq he
      have hpS := hdata p hp
      have hqS := hdata q hq
      have hij : p.1=q.1 := by
        by_contra hne
        exact Finset.disjoint_left.mp
          (hdisjoint p.1 hpS.1 q.1 hqS.1 hne (hpS.2.2.2.trans hqS.2.2.2.symm))
          hpS.2.1 (by rw [he]; exact hqS.2.1)
      exact Prod.ext hij he
    have hsub : V.image Prod.snd ⊆ (Grid u).filter (fun k =>
        ¬ (Acut*(ag u k).den ≤ Q ∧ Bmajor*R^2 ≤ c*(Q:ℝ)*(ag u k).den)) := by
      intro k hk
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hk
      have hh := hdata p hp
      refine Finset.mem_filter.mpr ⟨(hgrid u p.2).mpr ⟨p.1,hh.1,hh.2.2.2,hh.2.1⟩,?_⟩
      rw [←hh.2.2.2,hag p.1 hh.1 p.2 hh.2.1]
      exact hh.2.2.1
    have hh := (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (hGcount u hu)
    rwa [Finset.card_image_of_injOn hinj] at hh
  have hcard : (P.card:ℝ) ≤ (Phases.card:ℝ)*Cost := by
    have he : (P.card:ℝ)=∑ u∈Phases,((P.filter (fun p => y p.1=u)).card:ℝ) := by
      exact_mod_cast Finset.card_eq_sum_card_fiberwise
        (fun p hp => Finset.mem_image_of_mem y ((hmem p).mp (Finset.mem_filter.mp hp).1).1)
    calc
      _ = _ := he
      _ ≤ ∑ _u∈Phases,Cost := Finset.sum_le_sum hfiber
      _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]
  refine ⟨hcard,?_⟩
  intro H hH
  have hNp : (0:ℝ) ≤ N := Nat.cast_nonneg _
  calc
    (∑ p∈P,(H p.1 p.2:ℝ)) ≤ ∑ _p∈P,(N:ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      have hh := (hmem p).mp (Finset.mem_filter.mp hp).1
      exact Nat.cast_le.mpr (hH p.1 hh.1 p.2 hh.2)
    _ = (N:ℝ)*(P.card:ℝ) := by simp only [Finset.sum_const,nsmul_eq_mul,mul_comm]
    _ ≤ (N:ℝ)*((Phases.card:ℝ)*Cost) := mul_le_mul_of_nonneg_left hcard hNp
    _ = _ := by ring

private theorem strong_anchor_cutoff_dense
    (Acut Q d : ℕ) {σ c R Bmajor : ℝ}
    (hσ : 0 < σ) (hR : 0 < R)
    (hA : 768 ≤ Acut) (hB : 24576*σ ≤ Bmajor)
    (hcut : Acut*d ≤ Q) (hlow : Bmajor*R^2 ≤ c*(Q:ℝ)*d) :
    256*(d:ℝ) ≤ (Q:ℝ)/3 ∧
      ∀ eps : ℝ, c/(64*σ*R^2) ≤ eps →
        256 ≤ 2*eps*((Q:ℝ)/3)*d := by
  have hcut' : (768:ℝ)*d ≤ Q := by
    exact_mod_cast (Nat.mul_le_mul_right d hA).trans hcut
  have hraw := (mul_le_mul_of_nonneg_right hB (sq_nonneg R)).trans hlow
  have hdelta : 256 ≤ 2*(c/(64*σ*R^2))*((Q:ℝ)/3)*d := by
    have hh : (256:ℝ) ≤ c*(Q:ℝ)*d/(96*σ*R^2) := by
      apply (le_div_iff₀ (by positivity : 0 < 96*σ*R^2)).mpr
      nlinarith only [hraw]
    convert hh using 1
    ring
  refine ⟨by linarith only [hcut'],?_⟩
  intro eps heps
  apply hdelta.trans
  gcongr


theorem positive_difference_tagged_gap_controlled_complement_fourier
    {σ c J : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J) :
    ∃ C ≥ (1:ℝ), ∀ (ι : Type*) (Y : Finset ι) (F : ℝ → ℝ)
      (N : ℕ) (s : ℤ) (H : ι → ℤ → ℕ)
      (η T M R U : ℝ) (y x₁ x₂ : ι → ℝ),
      1 ≤ N → (∀ i∈Y, ∀ k, H i k ≤ N) →
      0 < η → η ≤ 1/8 → (∀ i∈Y, y i∈Icc (1:ℝ) 2) →
      0 < T → 0 < M → 0 < R → 0 < U →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ J) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
        c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
          (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|) →
      (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c) →
      T*(N:ℝ)*R^2=M^3 → 7*(N:ℝ)+2 ≤ M/4 →
      (3*J/σ)*(6*(N:ℝ)+1)^4 ≤ M*(N:ℝ)*R^2 →
      (3*J/(4*σ))*(6*(N:ℝ)+1)^2 ≤ (N:ℝ)*R^2 →
      3*J ≤ σ*U →
      (∀ i∈Y, x₁ i∈Icc M (2*M)) → (∀ i∈Y, x₂ i∈Icc M (2*M)) →
      (∀ i∈Y, ∀ j∈Y, i≠j → y i=y j → x₂ i ≤ x₁ j ∨ x₂ j ≤ x₁ i) →
      let f := fun i w => T*(F (w/M)-F (w/M+η*y i))/(σ*η)
      let h := fun i w => iteratedDeriv 2 (f i) w/2
      let t := fun k : ℤ => (s:ℝ)+(N:ℝ)*k
      let L := fun k : ℤ => s+(N:ℤ)*k+2*(N:ℤ)
      let delta := c/(64*σ*R^2)
      let Vbound := 3*J*M/(2*σ*(N:ℝ)*R^2)
      (∀ i∈Y, U/(4*R^2) ≤ h i (x₂ i)-h i (x₁ i) ∧
        h i (x₂ i)-h i (x₁ i) ≤ 7*U/(2*R^2)) →
      ∃ (S : ι → Finset ℤ) (anchor : ι → ℤ → ℚ) (za : ι → ℤ → ℝ),
        (∀ i∈Y,
          (∀ k : ℤ, k∈(S i) ↔ (x₁ i)+(N:ℝ)/4 ≤ t k ∧ t k ≤ (x₂ i)-(N:ℝ)/4) ∧
        (∀ k∈(S i), (za i) k∈Ioo (x₁ i) (x₂ i) ∧ (h i) ((za i) k)=((anchor i) k:ℝ) ∧
          ((anchor i) k:ℝ)∈Ioo ((h i) (x₁ i)) ((h i) (x₂ i)) ∧
          ((anchor i) k:ℝ)∈Ioo ((h i) (t k)-delta) ((h i) (t k)+delta) ∧
          ∀ a : ℚ, (a:ℝ)∈Ioo ((h i) (t k)-delta) ((h i) (t k)+delta) → ((anchor i) k).den ≤ a.den) ∧
        (∀ k∈(S i), |(za i) k-t k| ≤ (N:ℝ)/16) ∧
        (σ/(6*J))*U-3/2 ≤ ((S i).card:ℝ) ∧ ((S i).card:ℝ) ≤ (56*σ/c)*U+1/2 ∧
        (∀ Q : ℕ, 2 ≤ Q →
          let D := 64*σ*R^2/(c*(Q:ℝ))
          (((S i).filter (fun k => Q ≤ ((anchor i) k).den)).card:ℝ) ≤
            4*(Vbound+1)*D^2+D*(2+Real.log (D+1)))) ∧
      ∀ Q : ℕ, 2 ≤ Q → Q ≤ N →
      ∀ (Acut : ℕ) (Bmajor : ℝ), 2 ≤ Acut → Acut ≤ Q → 128*σ ≤ Bmajor →
      let Sall := Y.biUnion (fun i => (S i).image (fun k => (i,k)))
      let Good := fun i => Acut*(anchor i.1 i.2).den ≤ Q ∧
        Bmajor*R^2 ≤ c*(Q:ℝ)*(anchor i.1 i.2).den
      let G := Sall.filter Good
      let Dlow := Bmajor*R^2/(c*(Q:ℝ))
      let Khigh := Q/Acut+1
      let Dhigh := 64*σ*R^2/(c*(Khigh:ℝ))
      let Dlog := 64*σ*R^2/(c*((Q:ℝ)/Acut))
      let Cost := 4*Vbound*Dhigh^2+3*Dhigh*(2+Real.log (Dhigh+1))+
        Dlow*(2*(Vbound+delta)*Dlow+1)
      ∃ (r : ι × ℤ → ℚ) (z : ι × ℤ → ℝ),
      (∀ i∈G, (r i).den ≤ Q ∧ Q ≤ 2*(r i).den ∧
        (anchor i.1 i.2:ℝ) < r i ∧ |(r i:ℝ)-(anchor i.1 i.2:ℝ)| ≤ c/(64*σ*R^2) ∧
        z i∈Icc (za i.1 i.2) (za i.1 i.2+(N:ℝ)/16) ∧
        iteratedDeriv 2 (f i.1) (z i)/2=(r i:ℝ)) ∧
      (∀ i∈G, z i∈Ioo (x₁ i.1) (x₂ i.1)) ∧
      (768 ≤ Acut → 24576*σ ≤ Bmajor →
        ∀ i∈G, 256*((anchor i.1 i.2).den:ℝ) ≤ (Q:ℝ)/3 ∧
          ∀ eps : ℝ, delta ≤ eps → 256 ≤ 2*eps*((Q:ℝ)/3)*(anchor i.1 i.2).den) ∧
      let m := fun i => round (z i)
      let A := fun i => (L i.2-m i).toNat
      let q := fun i => (r i).den
      let μ := fun i => iteratedDeriv 3 (f i.1) (m i)/6
      let ℓ := fun i => deriv (f i.1) (m i)
      let U₃ := J/(2*σ*(N:ℝ)*R^2)
      (∀ i∈G, |z i-(m i:ℝ)| ≤ 1/2 ∧
        N ≤ A i ∧ A i ≤ 3*N ∧ m i+(A i:ℤ)=L i.2) ∧
      ∀ (K₀ : ℕ) [NeZero K₀], 63*U₃*(Q:ℝ)*(N:ℝ)^2 ≤ K₀ →
      ∃ v : ι × ℤ → ℤ, (∀ i∈G, (q i:ℤ) ∣ (r i).num*v i-1) ∧
      let b := fun i (p : Fin 2) => (⌊(q i:ℝ)*ℓ i⌋+(p:ℕ) : ℤ)
      let τ := fun i p => ((b i p:ℝ)-(q i:ℝ)*ℓ i)/2
      let s := fun i => Real.sqrt (2/(3*μ i*(q i:ℝ)))
      let K := fun i => -2*μ i*(s i)^3
      let x := fun i p =>
        (![-(v i:ℝ)*b i p/q i,-(v i:ℝ)/q i,K i,3*K i*τ i p/2] : Fin 4 → ℝ)
      ∃ k : ZMod K₀,
      let FourierCost :=
            (1+Real.log K₀)*
            (∑ i∈G, ∑ p : Fin 2,
              (Real.sqrt (2*(q i:ℝ))/((q i:ℝ)*Real.sqrt (μ i*A i)))*
              ‖∑ j : ZMod K₀,ZMod.stdAddChar (-(j*k))*
                GafniTao.fordAdditiveCharacter (∑ d,x i p d*
                  (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
                    Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖)+
            ∑ i∈G, (Real.sqrt (A i)*Real.log (2*(A i:ℝ))+1/(μ i*(A i:ℝ)^2))
      let Cerror := (Acut:ℝ)*((6*J/σ)*(64*σ/c)^2+192*σ/c)+
        ((3*J/σ+c/(32*σ))*(Bmajor/c)^2+Bmajor/c)
      (∑ i∈Sall, ‖∑ n∈Finset.Ioc (L i.2) (L i.2+H i.1 i.2),(𝐞 (f i.1 n):ℂ)‖) ≤ C*(((Y.image y).card:ℝ)*(N:ℝ)*Cost+FourierCost) ∧
      ((Acut:ℝ)*R ≤ (Q:ℝ) → (N:ℝ)*R ≤ M →
        (∑ i∈Sall, ‖∑ n∈Finset.Ioc (L i.2) (L i.2+H i.1 i.2),(𝐞 (f i.1 n):ℂ)‖) ≤
          C*(((Y.image y).card:ℝ)*Cerror*(M*R/Q)*(2+Real.log (Dlog+1))+FourierCost)) := by
  classical
  obtain ⟨C,hC,hentry⟩ := positive_difference_tagged_gap_dyadic_source_fourier_cutoffs hσ hc hJ
  refine ⟨C,hC,?_⟩
  intro ι Y F N s H η T M R U y x₁ x₂ hN hH hη hηmax hy hT hM hR hU
    hf hbound htests hnegative hphase hbuffer hfourBudget hquadBudget hUlarge hx₁ hx₂
    hGapSep f h t L delta Vbound hgap
  obtain ⟨S,anchor,za,hinfo,hfourier⟩ :=
    hentry ι Y F N s H η T M R U y x₁ x₂ hN hH hη hηmax hy hT hM hR hU
      hf hbound hnegative hphase hbuffer hfourBudget hquadBudget hUlarge hx₁ hx₂ hgap
  refine ⟨S,anchor,za,hinfo,?_⟩
  intro Q hQ hQN Acut Bmajor hAcut hAQ hBmajor Sall Good G Dlow Khigh Dhigh Dlog Cost
  have hB0 : 0 ≤ Bmajor := (show 0 ≤ 128*σ by positivity).trans hBmajor
  have hNp : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hpoints i (hi : i∈Y) k (hk : k∈S i) : t k∈Icc M (2*M) := by
    have hh := ((hinfo i hi).1 k).mp hk
    constructor <;> linarith only [hh.1,hh.2,(hx₁ i hi).1,(hx₂ i hi).2,hNp]
  have hanchors i (hi : i∈Y) k (hk : k∈S i) := ((hinfo i hi).2.1 k hk).2.2.2
  have hdisjoint i (hi : i∈Y) j (hj : j∈Y) (hne : i≠j) (hye : y i=y j) :
      Disjoint (S i) (S j) := by
    apply Finset.disjoint_left.mpr
    intro k hki hkj
    have hai := ((hinfo i hi).1 k).mp hki
    have haj := ((hinfo j hj).1 k).mp hkj
    rcases hGapSep i hi j hj hne hye with hij | hji
    · linarith only [hai.1,hai.2,haj.1,haj.2,hij,hNp]
    · linarith only [hai.1,hai.2,haj.1,haj.2,hji,hNp]
  have hgroup := tagged_anchor_complement_grouped_count Y S F y anchor N (s:ℝ)
    hσ hc hJ hη hηmax hy hf hbound htests hnegative hT hM
    (show 0 < N by omega) hR hphase hpoints hdisjoint hanchors
    Q Acut Bmajor hAcut hAQ hB0
  have hweight : (∑ i∈Sall.filter (fun i => ¬ Good i),(H i.1 i.2:ℝ)) ≤
      ((Y.image y).card:ℝ)*(N:ℝ)*Cost :=
    hgroup.2 H (fun i hi k _ => hH i hi k)
  obtain ⟨r,z,hr,hzg,hcenter,hcompletion⟩ := hfourier Q hQN Acut Bmajor hAcut hBmajor
  have hdense : 768 ≤ Acut → 24576*σ ≤ Bmajor →
      ∀ i∈G, 256*((anchor i.1 i.2).den:ℝ) ≤ (Q:ℝ)/3 ∧
        ∀ eps : ℝ, delta ≤ eps → 256 ≤ 2*eps*((Q:ℝ)/3)*(anchor i.1 i.2).den := by
    intro hAstrong hBstrong i hi
    exact strong_anchor_cutoff_dense Acut Q (anchor i.1 i.2).den hσ hR
      hAstrong hBstrong (Finset.mem_filter.mp hi).2.1 (Finset.mem_filter.mp hi).2.2
  refine ⟨r,z,hr,hzg,hdense,hcenter,?_⟩
  dsimp only
  intro K₀ _ hK₀
  obtain ⟨v,hv,k,hfour⟩ := hcompletion K₀ hK₀
  refine ⟨v,hv,k,?_⟩
  let m := fun i => round (z i)
  let A := fun i => (L i.2-m i).toNat
  let q := fun i => (r i).den
  let μ := fun i => iteratedDeriv 3 (f i.1) (m i)/6
  let ℓ := fun i => deriv (f i.1) (m i)
  let b := fun i (p : Fin 2) => (⌊(q i:ℝ)*ℓ i⌋+(p:ℕ) : ℤ)
  let τ := fun i p => ((b i p:ℝ)-(q i:ℝ)*ℓ i)/2
  let stretch := fun i => Real.sqrt (2/(3*μ i*(q i:ℝ)))
  let K := fun i => -2*μ i*(stretch i)^3
  let x := fun i p =>
    (![-(v i:ℝ)*b i p/q i,-(v i:ℝ)/q i,K i,3*K i*τ i p/2] : Fin 4 → ℝ)
  let FourierCost :=
            (1+Real.log K₀)*
            (∑ i∈G, ∑ p : Fin 2,
              (Real.sqrt (2*(q i:ℝ))/((q i:ℝ)*Real.sqrt (μ i*A i)))*
              ‖∑ j : ZMod K₀,ZMod.stdAddChar (-(j*k))*
                GafniTao.fordAdditiveCharacter (∑ d,x i p d*
                  (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
                    Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖)+
            ∑ i∈G, (Real.sqrt (A i)*Real.log (2*(A i:ℝ))+1/(μ i*(A i:ℝ)^2))
  let Cerror := (Acut:ℝ)*((6*J/σ)*(64*σ/c)^2+192*σ/c)+
        ((3*J/σ+c/(32*σ))*(Bmajor/c)^2+Bmajor/c)
  have hbase : (∑ i∈Sall, ‖∑ n∈Finset.Ioc (L i.2) (L i.2+H i.1 i.2),(𝐞 (f i.1 n):ℂ)‖) ≤ C*(((Y.image y).card:ℝ)*(N:ℝ)*Cost+FourierCost) := by
    apply hfour.trans
    dsimp only [FourierCost]
    rw [←add_assoc (((Y.image y).card:ℝ)*(N:ℝ)*Cost)]
    gcongr
  refine ⟨hbase,?_⟩
  intro hRQ hNR
  have hcost : Cost ≤ Cerror*(M*R/((N:ℝ)*Q))*(2+Real.log (Dlog+1)) :=
    huxley_anchor_complement_source_scale Q Acut
      hσ hc hJ hM hNp hR hAcut hAQ hB0 hRQ hNR
  have hscaled : ((Y.image y).card:ℝ)*(N:ℝ)*Cost ≤
      ((Y.image y).card:ℝ)*Cerror*(M*R/Q)*(2+Real.log (Dlog+1)) :=
    tagged_cost_source_scale (Nat.cast_nonneg _) hNp
      (by exact_mod_cast (show 0 < Q by omega)) hcost
  apply hbase.trans
  apply mul_le_mul_of_nonneg_left _ (by linarith only [hC])
  exact add_le_add hscaled (le_refl FourierCost)

example
    {σ c J : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J) :
    ∃ C ≥ (1:ℝ), ∀ (ι : Type*) (S : Finset ι) (F : ℝ → ℝ)
      (y : ι → ℝ) (L : ι → ℤ) (H : ι → ℕ) (anchor : ι → ℚ) (za : ι → ℝ)
      (N Q : ℕ) (η T M R : ℝ),
      1 ≤ N → (∀ i∈S, H i ≤ N) →
      0 < η → η ≤ 1/8 → 0 < T → 0 < M → 0 < R →
      (∀ i∈S, y i∈Icc (1:ℝ) 2) →
      (∀ i∈S, (L i:ℝ)-2*(N:ℝ)∈Icc M (2*M)) →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ J) →
      (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c) →
      T*(N:ℝ)*R^2=M^3 →
      7*(N:ℝ)+2 ≤ M/4 →
      (3*J/σ)*(6*(N:ℝ)+1)^4 ≤ M*(N:ℝ)*R^2 →
      (3*J/(4*σ))*(6*(N:ℝ)+1)^2 ≤ (N:ℝ)*R^2 →
      Q ≤ N →
      let f := fun i w => T*(F (w/M)-F (w/M+η*y i))/(σ*η)
      (∀ i∈S, za i∈Ioo ((L i:ℝ)-2*(N:ℝ)-(N:ℝ)/8)
        ((L i:ℝ)-2*(N:ℝ)+(N:ℝ)/8) ∧
        iteratedDeriv 2 (f i) (za i)/2=(anchor i:ℝ)) →
      let Good := fun i => 2*(anchor i).den ≤ Q ∧
        128*σ*R^2 ≤ c*(Q:ℝ)*(anchor i).den
      let G := S.filter Good
      ∃ (r : ι → ℚ) (z : ι → ℝ),
      (∀ i∈G, (r i).den ≤ Q ∧ Q ≤ 2*(r i).den ∧
        (anchor i:ℝ) < r i ∧ |(r i:ℝ)-(anchor i:ℝ)| ≤ c/(64*σ*R^2) ∧
        z i∈Icc (za i) (za i+(N:ℝ)/16) ∧
        iteratedDeriv 2 (f i) (z i)/2=(r i:ℝ)) ∧
      let m := fun i => round (z i)
      let A := fun i => (L i-m i).toNat
      let q := fun i => (r i).den
      let μ := fun i => iteratedDeriv 3 (f i) (m i)/6
      let ℓ := fun i => deriv (f i) (m i)
      let U₃ := J/(2*σ*(N:ℝ)*R^2)
      (∀ i∈G, |z i-(m i:ℝ)| ≤ 1/2 ∧
        N ≤ A i ∧ A i ≤ 3*N ∧ m i+(A i:ℤ)=L i) ∧
      ∀ (K₀ : ℕ) [NeZero K₀], 63*U₃*(Q:ℝ)*(N:ℝ)^2 ≤ K₀ →
      ∃ v : ι → ℤ, (∀ i∈G, (q i:ℤ) ∣ (r i).num*v i-1) ∧
      let b := fun i (p : Fin 2) => (⌊(q i:ℝ)*ℓ i⌋+(p:ℕ) : ℤ)
      let τ := fun i p => ((b i p:ℝ)-(q i:ℝ)*ℓ i)/2
      let s := fun i => Real.sqrt (2/(3*μ i*(q i:ℝ)))
      let K := fun i => -2*μ i*(s i)^3
      let x := fun i p =>
        (![-(v i:ℝ)*b i p/q i,-(v i:ℝ)/q i,K i,3*K i*τ i p/2] : Fin 4 → ℝ)
      ∃ k : ZMod K₀,
        (∑ i∈S, ‖∑ n∈Finset.Ioc (L i) (L i+H i),(𝐞 (f i n):ℂ)‖) ≤
          C*((∑ i∈S.filter (fun i => ¬ Good i),(H i:ℝ))+
            (1+Real.log K₀)*
            (∑ i∈G, ∑ p : Fin 2,
              (Real.sqrt (2*(q i:ℝ))/((q i:ℝ)*Real.sqrt (μ i*A i)))*
              ‖∑ j : ZMod K₀,ZMod.stdAddChar (-(j*k))*
                GafniTao.fordAdditiveCharacter (∑ d,x i p d*
                  (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
                    Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖)+
            ∑ i∈G, (Real.sqrt (A i)*Real.log (2*(A i:ℝ))+1/(μ i*(A i:ℝ)^2))) :=
  HuxleyDenseAnchorScratch.positive_difference_dyadic_anchor_source_partition (σ:=σ) (c:=c) (J:=J) hσ hc hJ

example
    {σ c J : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J) :
    ∃ C ≥ (1:ℝ), ∀ (ι : Type*) (Y : Finset ι) (F : ℝ → ℝ)
      (N : ℕ) (s : ℤ) (H : ι → ℤ → ℕ)
      (η T M R U : ℝ) (y x₁ x₂ : ι → ℝ),
      1 ≤ N → (∀ i∈Y, ∀ k, H i k ≤ N) →
      0 < η → η ≤ 1/8 → (∀ i∈Y, y i∈Icc (1:ℝ) 2) →
      0 < T → 0 < M → 0 < R → 0 < U →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ J) →
      (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c) →
      T*(N:ℝ)*R^2=M^3 → 7*(N:ℝ)+2 ≤ M/4 →
      (3*J/σ)*(6*(N:ℝ)+1)^4 ≤ M*(N:ℝ)*R^2 →
      (3*J/(4*σ))*(6*(N:ℝ)+1)^2 ≤ (N:ℝ)*R^2 →
      3*J ≤ σ*U →
      (∀ i∈Y, x₁ i∈Icc M (2*M)) → (∀ i∈Y, x₂ i∈Icc M (2*M)) →
      let f := fun i w => T*(F (w/M)-F (w/M+η*y i))/(σ*η)
      let h := fun i w => iteratedDeriv 2 (f i) w/2
      let t := fun k : ℤ => (s:ℝ)+(N:ℝ)*k
      let L := fun k : ℤ => s+(N:ℤ)*k+2*(N:ℤ)
      let delta := c/(64*σ*R^2)
      let Vbound := 3*J*M/(2*σ*(N:ℝ)*R^2)
      (∀ i∈Y, U/(4*R^2) ≤ h i (x₂ i)-h i (x₁ i) ∧
        h i (x₂ i)-h i (x₁ i) ≤ 7*U/(2*R^2)) →
      ∃ (S : ι → Finset ℤ) (anchor : ι → ℤ → ℚ) (za : ι → ℤ → ℝ),
        (∀ i∈Y,
          (∀ k : ℤ, k∈(S i) ↔ (x₁ i)+(N:ℝ)/4 ≤ t k ∧ t k ≤ (x₂ i)-(N:ℝ)/4) ∧
        (∀ k∈(S i), (za i) k∈Ioo (x₁ i) (x₂ i) ∧ (h i) ((za i) k)=((anchor i) k:ℝ) ∧
          ((anchor i) k:ℝ)∈Ioo ((h i) (x₁ i)) ((h i) (x₂ i)) ∧
          ((anchor i) k:ℝ)∈Ioo ((h i) (t k)-delta) ((h i) (t k)+delta) ∧
          ∀ a : ℚ, (a:ℝ)∈Ioo ((h i) (t k)-delta) ((h i) (t k)+delta) → ((anchor i) k).den ≤ a.den) ∧
        (∀ k∈(S i), |(za i) k-t k| ≤ (N:ℝ)/16) ∧
        (σ/(6*J))*U-3/2 ≤ ((S i).card:ℝ) ∧ ((S i).card:ℝ) ≤ (56*σ/c)*U+1/2 ∧
        (∀ Q : ℕ, 2 ≤ Q →
          let D := 64*σ*R^2/(c*(Q:ℝ))
          (((S i).filter (fun k => Q ≤ ((anchor i) k).den)).card:ℝ) ≤
            4*(Vbound+1)*D^2+D*(2+Real.log (D+1)))) ∧
      ∀ Q : ℕ, Q ≤ N →
      let Sall := Y.biUnion (fun i => (S i).image (fun k => (i,k)))
      let Good := fun i => 2*(anchor i.1 i.2).den ≤ Q ∧
        128*σ*R^2 ≤ c*(Q:ℝ)*(anchor i.1 i.2).den
      let G := Sall.filter Good
      ∃ (r : ι × ℤ → ℚ) (z : ι × ℤ → ℝ),
      (∀ i∈G, (r i).den ≤ Q ∧ Q ≤ 2*(r i).den ∧
        (anchor i.1 i.2:ℝ) < r i ∧ |(r i:ℝ)-(anchor i.1 i.2:ℝ)| ≤ c/(64*σ*R^2) ∧
        z i∈Icc (za i.1 i.2) (za i.1 i.2+(N:ℝ)/16) ∧
        iteratedDeriv 2 (f i.1) (z i)/2=(r i:ℝ)) ∧
      (∀ i∈G, z i∈Ioo (x₁ i.1) (x₂ i.1)) ∧
      let m := fun i => round (z i)
      let A := fun i => (L i.2-m i).toNat
      let q := fun i => (r i).den
      let μ := fun i => iteratedDeriv 3 (f i.1) (m i)/6
      let ℓ := fun i => deriv (f i.1) (m i)
      let U₃ := J/(2*σ*(N:ℝ)*R^2)
      (∀ i∈G, |z i-(m i:ℝ)| ≤ 1/2 ∧
        N ≤ A i ∧ A i ≤ 3*N ∧ m i+(A i:ℤ)=L i.2) ∧
      ∀ (K₀ : ℕ) [NeZero K₀], 63*U₃*(Q:ℝ)*(N:ℝ)^2 ≤ K₀ →
      ∃ v : ι × ℤ → ℤ, (∀ i∈G, (q i:ℤ) ∣ (r i).num*v i-1) ∧
      let b := fun i (p : Fin 2) => (⌊(q i:ℝ)*ℓ i⌋+(p:ℕ) : ℤ)
      let τ := fun i p => ((b i p:ℝ)-(q i:ℝ)*ℓ i)/2
      let s := fun i => Real.sqrt (2/(3*μ i*(q i:ℝ)))
      let K := fun i => -2*μ i*(s i)^3
      let x := fun i p =>
        (![-(v i:ℝ)*b i p/q i,-(v i:ℝ)/q i,K i,3*K i*τ i p/2] : Fin 4 → ℝ)
      ∃ k : ZMod K₀,
        (∑ i∈Sall, ‖∑ n∈Finset.Ioc (L i.2) (L i.2+H i.1 i.2),(𝐞 (f i.1 n):ℂ)‖) ≤
          C*((∑ i∈Sall.filter (fun i => ¬ Good i),(H i.1 i.2:ℝ))+
            (1+Real.log K₀)*
            (∑ i∈G, ∑ p : Fin 2,
              (Real.sqrt (2*(q i:ℝ))/((q i:ℝ)*Real.sqrt (μ i*A i)))*
              ‖∑ j : ZMod K₀,ZMod.stdAddChar (-(j*k))*
                GafniTao.fordAdditiveCharacter (∑ d,x i p d*
                  (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
                    Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖)+
            ∑ i∈G, (Real.sqrt (A i)*Real.log (2*(A i:ℝ))+1/(μ i*(A i:ℝ)^2))) :=
  HuxleyDenseAnchorScratch.positive_difference_tagged_gap_dyadic_source_fourier (σ:=σ) (c:=c) (J:=J) hσ hc hJ

example
    {σ c J : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J) :
    ∃ C ≥ (1:ℝ), ∀ (ι : Type*) (Y : Finset ι) (F : ℝ → ℝ)
      (N : ℕ) (s : ℤ) (H : ι → ℤ → ℕ)
      (η T M R U : ℝ) (y x₁ x₂ : ι → ℝ),
      1 ≤ N → (∀ i∈Y, ∀ k, H i k ≤ N) →
      0 < η → η ≤ 1/8 → (∀ i∈Y, y i∈Icc (1:ℝ) 2) →
      0 < T → 0 < M → 0 < R → 0 < U →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ J) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
        c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
          (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|) →
      (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c) →
      T*(N:ℝ)*R^2=M^3 → 7*(N:ℝ)+2 ≤ M/4 →
      (3*J/σ)*(6*(N:ℝ)+1)^4 ≤ M*(N:ℝ)*R^2 →
      (3*J/(4*σ))*(6*(N:ℝ)+1)^2 ≤ (N:ℝ)*R^2 →
      3*J ≤ σ*U →
      (∀ i∈Y, x₁ i∈Icc M (2*M)) → (∀ i∈Y, x₂ i∈Icc M (2*M)) →
      (∀ i∈Y, ∀ j∈Y, i≠j → y i=y j → x₂ i ≤ x₁ j ∨ x₂ j ≤ x₁ i) →
      let f := fun i w => T*(F (w/M)-F (w/M+η*y i))/(σ*η)
      let h := fun i w => iteratedDeriv 2 (f i) w/2
      let t := fun k : ℤ => (s:ℝ)+(N:ℝ)*k
      let L := fun k : ℤ => s+(N:ℤ)*k+2*(N:ℤ)
      let delta := c/(64*σ*R^2)
      let Vbound := 3*J*M/(2*σ*(N:ℝ)*R^2)
      (∀ i∈Y, U/(4*R^2) ≤ h i (x₂ i)-h i (x₁ i) ∧
        h i (x₂ i)-h i (x₁ i) ≤ 7*U/(2*R^2)) →
      ∃ (S : ι → Finset ℤ) (anchor : ι → ℤ → ℚ) (za : ι → ℤ → ℝ),
        (∀ i∈Y,
          (∀ k : ℤ, k∈(S i) ↔ (x₁ i)+(N:ℝ)/4 ≤ t k ∧ t k ≤ (x₂ i)-(N:ℝ)/4) ∧
        (∀ k∈(S i), (za i) k∈Ioo (x₁ i) (x₂ i) ∧ (h i) ((za i) k)=((anchor i) k:ℝ) ∧
          ((anchor i) k:ℝ)∈Ioo ((h i) (x₁ i)) ((h i) (x₂ i)) ∧
          ((anchor i) k:ℝ)∈Ioo ((h i) (t k)-delta) ((h i) (t k)+delta) ∧
          ∀ a : ℚ, (a:ℝ)∈Ioo ((h i) (t k)-delta) ((h i) (t k)+delta) → ((anchor i) k).den ≤ a.den) ∧
        (∀ k∈(S i), |(za i) k-t k| ≤ (N:ℝ)/16) ∧
        (σ/(6*J))*U-3/2 ≤ ((S i).card:ℝ) ∧ ((S i).card:ℝ) ≤ (56*σ/c)*U+1/2 ∧
        (∀ Q : ℕ, 2 ≤ Q →
          let D := 64*σ*R^2/(c*(Q:ℝ))
          (((S i).filter (fun k => Q ≤ ((anchor i) k).den)).card:ℝ) ≤
            4*(Vbound+1)*D^2+D*(2+Real.log (D+1)))) ∧
      ∀ Q : ℕ, 2 ≤ Q → Q ≤ N →
      ∀ (Acut : ℕ) (Bmajor : ℝ), 2 ≤ Acut → Acut ≤ Q → 128*σ ≤ Bmajor →
      let Sall := Y.biUnion (fun i => (S i).image (fun k => (i,k)))
      let Good := fun i => Acut*(anchor i.1 i.2).den ≤ Q ∧
        Bmajor*R^2 ≤ c*(Q:ℝ)*(anchor i.1 i.2).den
      let G := Sall.filter Good
      let Dlow := Bmajor*R^2/(c*(Q:ℝ))
      let Khigh := Q/Acut+1
      let Dhigh := 64*σ*R^2/(c*(Khigh:ℝ))
      let Dlog := 64*σ*R^2/(c*((Q:ℝ)/Acut))
      let Cost := 4*Vbound*Dhigh^2+3*Dhigh*(2+Real.log (Dhigh+1))+
        Dlow*(2*(Vbound+delta)*Dlow+1)
      ∃ (r : ι × ℤ → ℚ) (z : ι × ℤ → ℝ),
      (∀ i∈G, (r i).den ≤ Q ∧ Q ≤ 2*(r i).den ∧
        (anchor i.1 i.2:ℝ) < r i ∧ |(r i:ℝ)-(anchor i.1 i.2:ℝ)| ≤ c/(64*σ*R^2) ∧
        z i∈Icc (za i.1 i.2) (za i.1 i.2+(N:ℝ)/16) ∧
        iteratedDeriv 2 (f i.1) (z i)/2=(r i:ℝ)) ∧
      (∀ i∈G, z i∈Ioo (x₁ i.1) (x₂ i.1)) ∧
      (768 ≤ Acut → 24576*σ ≤ Bmajor →
        ∀ i∈G, 256*((anchor i.1 i.2).den:ℝ) ≤ (Q:ℝ)/3 ∧
          ∀ eps : ℝ, delta ≤ eps → 256 ≤ 2*eps*((Q:ℝ)/3)*(anchor i.1 i.2).den) ∧
      let m := fun i => round (z i)
      let A := fun i => (L i.2-m i).toNat
      let q := fun i => (r i).den
      let μ := fun i => iteratedDeriv 3 (f i.1) (m i)/6
      let ℓ := fun i => deriv (f i.1) (m i)
      let U₃ := J/(2*σ*(N:ℝ)*R^2)
      (∀ i∈G, |z i-(m i:ℝ)| ≤ 1/2 ∧
        N ≤ A i ∧ A i ≤ 3*N ∧ m i+(A i:ℤ)=L i.2) ∧
      ∀ (K₀ : ℕ) [NeZero K₀], 63*U₃*(Q:ℝ)*(N:ℝ)^2 ≤ K₀ →
      ∃ v : ι × ℤ → ℤ, (∀ i∈G, (q i:ℤ) ∣ (r i).num*v i-1) ∧
      let b := fun i (p : Fin 2) => (⌊(q i:ℝ)*ℓ i⌋+(p:ℕ) : ℤ)
      let τ := fun i p => ((b i p:ℝ)-(q i:ℝ)*ℓ i)/2
      let s := fun i => Real.sqrt (2/(3*μ i*(q i:ℝ)))
      let K := fun i => -2*μ i*(s i)^3
      let x := fun i p =>
        (![-(v i:ℝ)*b i p/q i,-(v i:ℝ)/q i,K i,3*K i*τ i p/2] : Fin 4 → ℝ)
      ∃ k : ZMod K₀,
      let FourierCost :=
            (1+Real.log K₀)*
            (∑ i∈G, ∑ p : Fin 2,
              (Real.sqrt (2*(q i:ℝ))/((q i:ℝ)*Real.sqrt (μ i*A i)))*
              ‖∑ j : ZMod K₀,ZMod.stdAddChar (-(j*k))*
                GafniTao.fordAdditiveCharacter (∑ d,x i p d*
                  (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
                    Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖)+
            ∑ i∈G, (Real.sqrt (A i)*Real.log (2*(A i:ℝ))+1/(μ i*(A i:ℝ)^2))
      let Cerror := (Acut:ℝ)*((6*J/σ)*(64*σ/c)^2+192*σ/c)+
        ((3*J/σ+c/(32*σ))*(Bmajor/c)^2+Bmajor/c)
      (∑ i∈Sall, ‖∑ n∈Finset.Ioc (L i.2) (L i.2+H i.1 i.2),(𝐞 (f i.1 n):ℂ)‖) ≤ C*(((Y.image y).card:ℝ)*(N:ℝ)*Cost+FourierCost) ∧
      ((Acut:ℝ)*R ≤ (Q:ℝ) → (N:ℝ)*R ≤ M →
        (∑ i∈Sall, ‖∑ n∈Finset.Ioc (L i.2) (L i.2+H i.1 i.2),(𝐞 (f i.1 n):ℂ)‖) ≤
          C*(((Y.image y).card:ℝ)*Cerror*(M*R/Q)*(2+Real.log (Dlog+1))+FourierCost)) :=
  HuxleyDenseAnchorScratch.positive_difference_tagged_gap_controlled_complement_fourier (σ:=σ) (c:=c) (J:=J) hσ hc hJ

example
    {σ c J : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J) :
    ∃ C ≥ (1:ℝ), ∀ (ι : Type*) (Y : Finset ι) (F : ℝ → ℝ)
      (N : ℕ) (s : ℤ) (H : ι → ℤ → ℕ)
      (η T M R U : ℝ) (y x₁ x₂ : ι → ℝ),
      1 ≤ N → (∀ i∈Y, ∀ k, H i k ≤ N) →
      0 < η → η ≤ 1/8 → (∀ i∈Y, y i∈Icc (1:ℝ) 2) →
      0 < T → 0 < M → 0 < R → 0 < U →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ J) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
        c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
          (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|) →
      (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c) →
      T*(N:ℝ)*R^2=M^3 → 7*(N:ℝ)+2 ≤ M/4 →
      (3*J/σ)*(6*(N:ℝ)+1)^4 ≤ M*(N:ℝ)*R^2 →
      (3*J/(4*σ))*(6*(N:ℝ)+1)^2 ≤ (N:ℝ)*R^2 →
      3*J ≤ σ*U →
      (∀ i∈Y, x₁ i∈Icc M (2*M)) → (∀ i∈Y, x₂ i∈Icc M (2*M)) →
      (∀ i∈Y, ∀ j∈Y, i≠j → y i=y j → x₂ i ≤ x₁ j ∨ x₂ j ≤ x₁ i) →
      let f := fun i w => T*(F (w/M)-F (w/M+η*y i))/(σ*η)
      let h := fun i w => iteratedDeriv 2 (f i) w/2
      let t := fun k : ℤ => (s:ℝ)+(N:ℝ)*k
      let L := fun k : ℤ => s+(N:ℤ)*k+2*(N:ℤ)
      let delta := c/(64*σ*R^2)
      let Vbound := 3*J*M/(2*σ*(N:ℝ)*R^2)
      (∀ i∈Y, U/(4*R^2) ≤ h i (x₂ i)-h i (x₁ i) ∧
        h i (x₂ i)-h i (x₁ i) ≤ 7*U/(2*R^2)) →
      ∃ (S : ι → Finset ℤ) (anchor : ι → ℤ → ℚ) (za : ι → ℤ → ℝ),
        (∀ i∈Y,
          (∀ k : ℤ, k∈(S i) ↔ (x₁ i)+(N:ℝ)/4 ≤ t k ∧ t k ≤ (x₂ i)-(N:ℝ)/4) ∧
        (∀ k∈(S i), (za i) k∈Ioo (x₁ i) (x₂ i) ∧ (h i) ((za i) k)=((anchor i) k:ℝ) ∧
          ((anchor i) k:ℝ)∈Ioo ((h i) (x₁ i)) ((h i) (x₂ i)) ∧
          ((anchor i) k:ℝ)∈Ioo ((h i) (t k)-delta) ((h i) (t k)+delta) ∧
          ∀ a : ℚ, (a:ℝ)∈Ioo ((h i) (t k)-delta) ((h i) (t k)+delta) → ((anchor i) k).den ≤ a.den) ∧
        (∀ k∈(S i), |(za i) k-t k| ≤ (N:ℝ)/16) ∧
        (σ/(6*J))*U-3/2 ≤ ((S i).card:ℝ) ∧ ((S i).card:ℝ) ≤ (56*σ/c)*U+1/2 ∧
        (∀ Q : ℕ, 2 ≤ Q →
          let D := 64*σ*R^2/(c*(Q:ℝ))
          (((S i).filter (fun k => Q ≤ ((anchor i) k).den)).card:ℝ) ≤
            4*(Vbound+1)*D^2+D*(2+Real.log (D+1)))) ∧
      ∀ Q : ℕ, 2 ≤ Q → Q ≤ N →
      let Sall := Y.biUnion (fun i => (S i).image (fun k => (i,k)))
      let Good := fun i => 2*(anchor i.1 i.2).den ≤ Q ∧
        128*σ*R^2 ≤ c*(Q:ℝ)*(anchor i.1 i.2).den
      let G := Sall.filter Good
      let Dlow := 128*σ*R^2/(c*(Q:ℝ))
      let Khigh := Q/2+1
      let Dhigh := 64*σ*R^2/(c*(Khigh:ℝ))
      let Cost := 4*Vbound*Dhigh^2+3*Dhigh*(2+Real.log (Dhigh+1))+
        Dlow*(2*(Vbound+delta)*Dlow+1)
      ∃ (r : ι × ℤ → ℚ) (z : ι × ℤ → ℝ),
      (∀ i∈G, (r i).den ≤ Q ∧ Q ≤ 2*(r i).den ∧
        (anchor i.1 i.2:ℝ) < r i ∧ |(r i:ℝ)-(anchor i.1 i.2:ℝ)| ≤ c/(64*σ*R^2) ∧
        z i∈Icc (za i.1 i.2) (za i.1 i.2+(N:ℝ)/16) ∧
        iteratedDeriv 2 (f i.1) (z i)/2=(r i:ℝ)) ∧
      (∀ i∈G, z i∈Ioo (x₁ i.1) (x₂ i.1)) ∧
      let m := fun i => round (z i)
      let A := fun i => (L i.2-m i).toNat
      let q := fun i => (r i).den
      let μ := fun i => iteratedDeriv 3 (f i.1) (m i)/6
      let ℓ := fun i => deriv (f i.1) (m i)
      let U₃ := J/(2*σ*(N:ℝ)*R^2)
      (∀ i∈G, |z i-(m i:ℝ)| ≤ 1/2 ∧
        N ≤ A i ∧ A i ≤ 3*N ∧ m i+(A i:ℤ)=L i.2) ∧
      ∀ (K₀ : ℕ) [NeZero K₀], 63*U₃*(Q:ℝ)*(N:ℝ)^2 ≤ K₀ →
      ∃ v : ι × ℤ → ℤ, (∀ i∈G, (q i:ℤ) ∣ (r i).num*v i-1) ∧
      let b := fun i (p : Fin 2) => (⌊(q i:ℝ)*ℓ i⌋+(p:ℕ) : ℤ)
      let τ := fun i p => ((b i p:ℝ)-(q i:ℝ)*ℓ i)/2
      let s := fun i => Real.sqrt (2/(3*μ i*(q i:ℝ)))
      let K := fun i => -2*μ i*(s i)^3
      let x := fun i p =>
        (![-(v i:ℝ)*b i p/q i,-(v i:ℝ)/q i,K i,3*K i*τ i p/2] : Fin 4 → ℝ)
      ∃ k : ZMod K₀,
      let FourierCost :=
            (1+Real.log K₀)*
            (∑ i∈G, ∑ p : Fin 2,
              (Real.sqrt (2*(q i:ℝ))/((q i:ℝ)*Real.sqrt (μ i*A i)))*
              ‖∑ j : ZMod K₀,ZMod.stdAddChar (-(j*k))*
                GafniTao.fordAdditiveCharacter (∑ d,x i p d*
                  (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
                    Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖)+
            ∑ i∈G, (Real.sqrt (A i)*Real.log (2*(A i:ℝ))+1/(μ i*(A i:ℝ)^2))
      let Cerror := 2*((6*J/σ)*(64*σ/c)^2+192*σ/c)+
        ((3*J/σ+c/(32*σ))*(128*σ/c)^2+128*σ/c)
      (∑ i∈Sall, ‖∑ n∈Finset.Ioc (L i.2) (L i.2+H i.1 i.2),(𝐞 (f i.1 n):ℂ)‖) ≤ C*(((Y.image y).card:ℝ)*(N:ℝ)*Cost+FourierCost) ∧
      (2*R ≤ (Q:ℝ) → (N:ℝ)*R ≤ M →
        (∑ i∈Sall, ‖∑ n∈Finset.Ioc (L i.2) (L i.2+H i.1 i.2),(𝐞 (f i.1 n):ℂ)‖) ≤
          C*(((Y.image y).card:ℝ)*Cerror*(M*R/Q)*(2+Real.log (Dlow+1))+FourierCost)) := by
  obtain ⟨C,hC,hentry⟩ :=
    HuxleyDenseAnchorScratch.positive_difference_tagged_gap_controlled_complement_fourier hσ hc hJ
  refine ⟨C,hC,?_⟩
  intro ι Y F N s H η T M R U y x₁ x₂ hN hH hη hηmax hy hT hM hR hU
    hf hbound htests hnegative hphase hbuffer hfourBudget hquadBudget hUlarge hx₁ hx₂
    hGapSep f h t L delta Vbound hgap
  obtain ⟨S,anchor,za,hinfo,hconsumer⟩ :=
    hentry ι Y F N s H η T M R U y x₁ x₂ hN hH hη hηmax hy hT hM hR hU
      hf hbound htests hnegative hphase hbuffer hfourBudget hquadBudget hUlarge hx₁ hx₂ hGapSep hgap
  refine ⟨S,anchor,za,hinfo,?_⟩
  intro Q hQ hQN Sall Good G Dlow Khigh Dhigh Cost
  obtain ⟨r,z,hr,hzg,_hdense,hrest⟩ :=
    hconsumer Q hQ hQN 2 (128*σ) (by norm_num) hQ le_rfl
  refine ⟨r,z,hr,hzg,?_⟩
  have he : 64*σ*R^2/(c*((Q:ℝ)/2))=Dlow := by dsimp only [Dlow]; ring
  simpa only [Nat.cast_ofNat,he] using hrest

#print axioms positive_difference_tagged_gap_controlled_complement_fourier
#print axioms positive_difference_dyadic_anchor_source_partition_cutoffs
#print axioms positive_difference_tagged_gap_dyadic_source_fourier_cutoffs
#print axioms tagged_anchor_complement_grouped_count
#print axioms strong_anchor_cutoff_dense
#print axioms positive_difference_dyadic_anchor_source_partition
#print axioms positive_difference_tagged_gap_dyadic_source_fourier
end HuxleyDenseAnchorScratch
