import UV.ContinueCompressedModesFockCycles
import UV.ContinueSourceReviewClassicalPacket
import Mathlib.GroupTheory.Perm.Cycle.Basic

/-! Independent carrier momenta of the cycles extracted from a normal-
ordered Fock coefficient. Every declared transverse rim is oriented
by the signed energy transfer on its own sector plane. -/

noncomputable section
open UV.SectorPlane MeasureTheory Filter
open scoped Topology ENNReal SchwartzMap

namespace UV.FermionWick

variable {ν : Type*} [Fintype ν]

abbrev Cycle (σ : Equiv.Perm ν) := Quotient (Equiv.Perm.SameCycle.setoid σ)

def cycleClass (σ : Equiv.Perm ν) (i : ν) : Cycle σ := Quotient.mk _ i

abbrev CycleVertex (σ : Equiv.Perm ν) (C : Cycle σ) := {i : ν // cycleClass σ i=C}

noncomputable instance (σ : Equiv.Perm ν) : Fintype (Cycle σ) := Fintype.ofFinite _
noncomputable instance (σ : Equiv.Perm ν) (C : Cycle σ) : Fintype (CycleVertex σ C) := Fintype.ofFinite _

instance (σ : Equiv.Perm ν) (C : Cycle σ) : Nonempty (CycleVertex σ C) :=
  ⟨⟨C.out,Quotient.out_eq _⟩⟩

def cycleStep (σ : Equiv.Perm ν) (C : Cycle σ) : Equiv.Perm (CycleVertex σ C) :=
  σ.subtypePerm (fun i => by
    have h : cycleClass σ (σ i)=cycleClass σ i := Quotient.sound ((Equiv.Perm.sameCycle_apply_left).mpr (Equiv.Perm.SameCycle.refl σ i))
    simp [h])

def signedRim {V : Type*} [NormedAddCommGroup V] (diamond : Plane V) (positive : Bool) : Evolution :=
  match diamond.s,positive with
  | .N,true | .A,false => .ascending
  | .A,true | .N,false => .descending

theorem signed_rim_eta {V : Type*} [NormedAddCommGroup V] (diamond : Plane V) (b : Bool) :
    diamond.eta (signedRim diamond b) = (if b then 1 else -1) := by
  cases diamond with
  | mk s x u => cases s <;> cases b <;> norm_num [signedRim,Plane.eta,sectorSign,evolutionSign]

def rimOnCycle {V : Type*} [NormedAddCommGroup V] (diamond : Plane V) (σ : Equiv.Perm ν)
    (band : ν→Bool) (C : Cycle σ) (offset : ν→Spatial) (m ℓ : ℝ) (N : ℕ) (k : Spatial) :=
  seaComplexLoopReadout diamond (fun i : CycleVertex σ C => signedRim diamond (band i.val)) (cycleStep σ C)
    (fun i => band i.val) (fun i => offset i.val) m ℓ N k

theorem measurable_rim {V : Type*} [NormedAddCommGroup V] (diamond : Plane V) (ε : Evolution)
    (changeBand : Bool) (m ℓ : ℝ) (N : ℕ) :
    Measurable (fun p : Spatial × Spatial => seaRimMark diamond ε changeBand m ℓ N p.1 p.2) := by
  cases changeBand <;> simp only [seaRimMark,if_true,Bool.false_eq_true,if_false,seaMarkDen,
    seaTransferSq,FurtherOptical.energy] <;> fun_prop

private theorem measurable_rim_pair {V Z : Type*} [NormedAddCommGroup V] [MeasurableSpace Z]
    (diamond : Plane V) (ε : Evolution) (chg : Bool) (m ℓ : ℝ) (N : ℕ)
    (k l : Z→Spatial) (hk : Measurable k) (hl : Measurable l) :
    Measurable (fun z => seaRimMark diamond ε chg m ℓ N (k z) (l z)) := by
  cases chg <;> simp only [seaRimMark,if_true,Bool.false_eq_true,if_false,seaMarkDen,seaTransferSq,FurtherOptical.energy] <;> fun_prop

set_option maxHeartbeats 400000 in
theorem contribution_integrable {V : Type*} [NormedAddCommGroup V] (diamond : Plane V)
    (σ : Equiv.Perm ν) (bands : ν→Bool) {d : ℕ} {T : Type*} [MeasurableSpace T]
    (μ : Measure T) [IsFiniteMeasure μ] (χ : 𝓢(EuclideanSpace ℝ (Fin d),ℂ))
    (t : ν→ℝ) (ord : ∀ i, if bands i then t i<t (σ i) else t (σ i)<t i)
    (offset : ν→Spatial) (L : ν→EuclideanSpace ℝ (Fin d)→L[ℝ] Spatial)
    {m ℓ : ℝ} (hm : 0<m) (hℓ : 0<ℓ) {N : ℕ} (hN : 2≤N)
    (spin : T × (EuclideanSpace ℝ (Fin d) × (Cycle σ→Spatial)) → ℂ)
    (hs : AEStronglyMeasurable spin (μ.prod (volume.prod volume))) (hsq : ∀z,‖spin z‖≤1) :
    Integrable (fun z : T × (EuclideanSpace ℝ (Fin d) × (Cycle σ→Spatial)) =>
      spin z*χ z.2.1*∏ c : Cycle σ, rimOnCycle diamond σ bands c (fun i => offset i+L i z.2.1) m ℓ N (z.2.2 c))
      (μ.prod (volume.prod volume)) := by
  classical
  let h := Fintype.card (Cycle σ)
  let B := fun c : Cycle σ => (5+ℓ⁻¹)*(1+m+2*∑ i:CycleVertex σ c, (‖offset i.val‖+‖L i.val‖))
  let A := ∏ c : Cycle σ, ((1+ℓ*(2*m))^(Fintype.card (CycleVertex σ c))*(B c)^2)^N
  let W := fun k:Spatial => (1+‖k‖)^(-((2*N:ℕ):ℝ))
  have hord (c : Cycle σ) (i : CycleVertex σ c) :
      if bands i.val then t i.val < t ((cycleStep σ c i).val) else t ((cycleStep σ c i).val)<t i.val := ord i.val
  have hsingle (c : Cycle σ) (q : EuclideanSpace ℝ (Fin d)) (k:Spatial) :
      ‖rimOnCycle diamond σ bands c (fun i => offset i+L i q) m ℓ N k‖ ≤
        ((1+ℓ*(2*m))^(Fintype.card (CycleVertex σ c))*(B c)^2)^N*(1+‖q‖)^(2*N)*W k := by
    rw [rimOnCycle,sea_complex_loop_readout_norm _ _ _ _ _ hm hℓ]
    apply (sea_classical_loop_budget _ _ _ (hord c) _ hm hℓ N k).trans
    let o := fun i : CycleVertex σ c => offset i.val
    let l := fun i : CycleVertex σ c => L i.val
    have hcost := sea_affine_loop_cost o l hm hℓ q
    have hpos : 0≤seaLoopRoutingCost m ℓ (fun i:CycleVertex σ c => offset i.val+L i.val q) := by
      unfold seaLoopRoutingCost; positivity
    calc _ ≤ ((1+ℓ*(2*m))^Fintype.card (CycleVertex σ c)*(B c*(1+‖q‖))^2)^N/(1+‖k‖)^(2*N) := by
          gcongr
      _ = _ := by dsimp [W]; rw [Real.rpow_neg (by positivity),Real.rpow_natCast,mul_pow (B c),←mul_assoc,mul_pow,←pow_mul,div_eq_mul_inv]
  have hiW : Integrable W volume := integrable_one_add_norm (by simpa using (show (3:ℝ)<(2*N:ℕ) by exact_mod_cast (show 3<2*N by omega)))
  have hiP := Integrable.fintype_prod (ι:=Cycle σ) (fun _ => hiW)
  let n := 2*N*h
  have hiχ := sea_packet_integrable χ n
  have hall := (integrable_const (μ:=μ) (1:ℝ)).mul_prod ((hiχ.const_mul A).mul_prod hiP)
  refine hall.mono' ?_ (ae_of_all _ fun z => ?_)
  · apply (hs.mul ((χ.continuous.measurable.comp (measurable_fst.comp measurable_snd)).aestronglyMeasurable)).mul
    apply Measurable.aestronglyMeasurable
    unfold rimOnCycle seaComplexLoopReadout
    apply Finset.measurable_prod
    intro c _
    apply Finset.measurable_prod
    intro i _
    have K : Measurable (fun z:T × (EuclideanSpace ℝ (Fin d) × (Cycle σ→Spatial)) => z.2.2 c) := (measurable_pi_apply c).comp (measurable_snd.comp measurable_snd)
    have H (j : CycleVertex σ c) : Measurable (fun z : T × (EuclideanSpace ℝ (Fin d) × (Cycle σ→Spatial)) => z.2.2 c+(offset j.val+L j.val z.2.1)) :=
      K.add (measurable_const.add ((L j.val).continuous.measurable.comp (measurable_fst.comp measurable_snd)))
    exact measurable_rim_pair diamond _ _ m ℓ N _ _ (H ((cycleStep σ c).symm i)) (H i)
  · simp only [norm_mul,norm_prod,one_mul]
    have hprod := Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun c (_ : c∈Finset.univ) => hsingle c z.2.1 (z.2.2 c))
    rw [Finset.prod_mul_distrib,Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,←pow_mul] at hprod
    have h₁ := mul_le_mul_of_nonneg_right (hsq z) (norm_nonneg (χ z.2.1))
    rw [one_mul] at h₁
    have hh := mul_le_mul h₁ hprod (Finset.prod_nonneg (fun _ _ => norm_nonneg _)) (norm_nonneg _)
    exact hh.trans_eq (by change ‖χ z.2.1‖*(A*(1+‖z.2.1‖)^n*(∏j:Cycle σ,W (z.2.2 j)))=A*((1+‖z.2.1‖)^n*‖χ z.2.1‖)*(∏j:Cycle σ,W (z.2.2 j)); ring)

end UV.FermionWick
