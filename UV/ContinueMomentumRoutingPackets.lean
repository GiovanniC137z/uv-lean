import UV.ContinueMomentumRoutingGraph

/-! Retain the endpoint difference in the joint estimate. The incoming
and outgoing packets together supply integrable decay in the unrestricted
external transfer in addition to the base carrier momentum. -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Set Filter UV.SectorPlane
open scoped SchwartzMap Matrix.Norms.L2Operator

namespace UV

theorem momentum_packet_weight_pos (p : OSFourSpace) : 0 < normalPacketWeight p := by unfold normalPacketWeight; positivity

theorem momentum_schwartz_overlap (φ ψ : 𝓢(OSFourSpace,WilsonPacketSpinor)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k Δ : OSFourSpace, ‖φ (k+Δ)‖*‖ψ k‖ ≤ C*normalPacketWeight Δ*normalPacketWeight k := by
  let K (n : ℕ) (f : 𝓢(OSFourSpace,WilsonPacketSpinor)) := (2:ℝ)^n*(Finset.Iic (n,0)).sup (fun m : ℕ × ℕ => SchwartzMap.seminorm ℝ m.1 m.2) f
  have h (n : ℕ) (f : 𝓢(OSFourSpace,WilsonPacketSpinor)) (p : OSFourSpace) : (1+‖p‖)^n*‖f p‖ ≤ K n f := by
    simpa only [K,norm_iteratedFDeriv_zero] using SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (n,0)) (le_refl n) (le_refl 0) f p
  have hK (n) (f) : 0 ≤ K n f := (by positivity : 0 ≤ (1+‖(0:OSFourSpace)‖)^n*‖f 0‖).trans (h n f 0)
  refine ⟨K 6 φ*K 12 ψ,mul_nonneg (hK _ _) (hK _ _),fun k Δ => ?_⟩
  have hΔ : 1+‖Δ‖ ≤ (1+‖k+Δ‖)*(1+‖k‖) := by
    have hx := norm_sub_le (k+Δ) k
    rw [add_sub_cancel_left] at hx
    nlinarith [mul_nonneg (norm_nonneg (k+Δ)) (norm_nonneg k)]
  unfold normalPacketWeight
  rw [←div_eq_mul_inv,le_div_iff₀ (by positivity),←div_eq_mul_inv,le_div_iff₀ (by positivity)]
  calc _ ≤ (‖φ (k+Δ)‖*‖ψ k‖*(1+‖k‖)^6)*((1+‖k+Δ‖)*(1+‖k‖))^6 := by
         exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hΔ 6) (by positivity)
       _ = ((1+‖k+Δ‖)^6*‖φ (k+Δ)‖)*((1+‖k‖)^12*‖ψ k‖) := by ring
       _ ≤ _ := mul_le_mul (h _ φ _) (h _ ψ _) (by positivity) (hK _ _)

theorem momentum_overlap_integral (σ : Measure OSFourSpace) (hi : Integrable normalPacketWeight σ)
    (φ ψ : 𝓢(OSFourSpace,WilsonPacketSpinor)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Δ : OSFourSpace,
      let Y := fun k => ‖φ (k+Δ)‖*‖ψ k‖
      Integrable Y σ ∧ (∫ k, Y k ∂σ) ≤ C * normalPacketWeight Δ := by
  obtain ⟨C,hC,h⟩ := momentum_schwartz_overlap φ ψ
  have hI : 0 ≤ ∫ k, normalPacketWeight k ∂σ := integral_nonneg fun k => (momentum_packet_weight_pos k).le
  refine ⟨C*(∫ k, normalPacketWeight k ∂σ),mul_nonneg hC hI,fun Δ => ?_⟩
  let Y := fun k => ‖φ (k+Δ)‖*‖ψ k‖
  have hc : Continuous Y := ((φ.continuous.comp (continuous_id.add continuous_const)).norm).mul ψ.continuous.norm
  have hb (k) := h k Δ
  have hm := hi.const_mul (C*normalPacketWeight Δ)
  have hy : Integrable Y σ := hm.mono' hc.aestronglyMeasurable (Eventually.of_forall fun k => by
    rw [Real.norm_of_nonneg (show 0 ≤ Y k by dsimp [Y]; positivity)]; exact hb k)
  refine ⟨hy,(integral_mono hy hm hb).trans_eq ?_⟩
  rw [integral_const_mul]; ring

theorem momentum_lattice_weight (b : NormalReciprocalBasis) : Integrable normalPacketWeight (normalLatticeMeasure b) := by
  obtain ⟨_,_,hb⟩ := normal_lattice_packet_weight_shifts b
  simpa using (hb 0).1

/-- The dependent external transfer is fixed by overall conservation.
One bounded packet is evaluated there and every other packet is
integrated over its full independent carrier space. -/
theorem momentum_external_tests_integrable {A : Type*} [AddCommGroup A] [MeasurableSpace A] [MeasurableAdd₂ A] [MeasurableSub₂ A]
    (σ : Measure A) [SigmaFinite σ] {n : ℕ} (q : A) (f : Fin (n+1) → A → ℝ) (B : ℝ)
    (hB : ∀ a, ‖f 0 a‖ ≤ B) (hm : ∀ i, Measurable (f i)) (hi : ∀ i : Fin n, Integrable (f i.succ) σ) :
    Integrable (fun x : Fin n → A => ∏ i, f i (Fin.cons (α := fun _ => A) (q-∑ j, x j) x i)) (Measure.pi fun _ => σ) := by
  simp only [Fin.prod_univ_succ,Fin.cons_zero,Fin.cons_succ]
  have h := Integrable.fintype_prod hi
  have hM : Measurable (fun x : Fin n → A => f 0 (q-∑ j, x j)) := (hm 0).comp (measurable_const.sub (Finset.measurable_sum _ (fun j _ => measurable_pi_apply j)))
  refine (h.norm.const_mul B).mono' (hM.aestronglyMeasurable.mul h.aestronglyMeasurable) (Eventually.of_forall fun x => ?_)
  rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hB _) (norm_nonneg _)

theorem momentum_packet_pair_product (φ ψ : WilsonPacket) (k Δ : OSFourSpace) (A : DiracMatrix) :
    ‖wilsonPacketPair φ ψ k Δ A‖ ≤ ‖A‖*(‖φ.value (k+Δ)‖*‖ψ.value k‖) := by
  apply (norm_inner_le_norm (𝕜 := ℂ) _ _).trans
  exact (mul_le_mul_of_nonneg_left (Matrix.l2_opNorm_mulVec A (ψ.value k)) (norm_nonneg _)).trans_eq (by ring)

theorem momentum_open_word_decay {m : ℝ} (hm : 0 < m) {r : ℕ} (u : Fin r → UnitVector OSFourSpace)
    (σ : Measure OSFourSpace) [SFinite σ] (hσ : Integrable normalPacketWeight σ) (φ ψ : 𝓢(OSFourSpace,WilsonPacketSpinor)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ D Δ (p : NormalOpenVariables r → Fin (r+1) → OSFourSpace),
      (∀ j, Measurable (p · j)) →
      let F := normalPacketWord m D u (normalSchwartzPacket φ) (normalSchwartzPacket ψ) Δ p
      Integrable F (volume.prod σ) ∧ (∫ t, ‖F t‖ ∂volume.prod σ) ≤ C*Real.exp (-(m/2)*|D|)*normalPacketWeight Δ := by
  obtain ⟨C,hC,hy⟩ := momentum_overlap_integral σ hσ φ ψ
  let K := (2:ℝ)^(r+1)*(4/m)^r*C
  refine ⟨K,by dsimp [K]; positivity,fun D Δ p hp => ?_⟩
  let M := (2:ℝ)^(r+1)*Real.exp (-(m/2)*|D|)
  let g := fun t : ℝ => Real.exp (-(m/2)*|t|)
  let X := fun x : Fin r → ℝ => M*∏ j,g (x j)
  let Y := fun k => ‖φ (k+Δ)‖*‖ψ k‖
  obtain ⟨hy',hY⟩ := hy Δ
  have hg := normal_open_laplace_mass hm
  have hX : Integrable X := (Integrable.fintype_prod (fun _ : Fin r => hg.1)).const_mul M
  have hXY : Integrable (fun t : NormalOpenVariables r => X t.1*Y t.2) (volume.prod σ) := hX.mul_prod hy'
  have hF := wilson_packet_pair_measurable (normalSchwartzPacket φ) (normalSchwartzPacket ψ) measurable_snd (measurable_const (a := Δ))
    (normal_open_word_args_measurable normalCoverGamma5 m D u hp (fun i => (measurable_pi_apply i).comp measurable_fst))
  have hb (t : NormalOpenVariables r) : ‖normalPacketWord m D u (normalSchwartzPacket φ) (normalSchwartzPacket ψ) Δ p t‖ ≤ X t.1*Y t.2 :=
    (momentum_packet_pair_product _ _ _ _ _).trans (mul_le_mul_of_nonneg_right
      (normal_open_dirac_majorant normalCoverGamma5 normal_cover_gamma_norm hm D u (p t) t.1) (by positivity))
  have hi := hXY.mono' hF.aestronglyMeasurable (Eventually.of_forall hb)
  refine ⟨hi,(integral_mono hi.norm hXY hb).trans ?_⟩
  rw [integral_prod_mul X Y]
  dsimp only [X]
  rw [integral_const_mul,integral_fintype_prod_volume_eq_pow g]
  simp only [Fintype.card_fin,g,hg.2,M]
  calc _ ≤ _ := mul_le_mul_of_nonneg_left hY (by positivity)
       _ = _ := by dsimp only [K]; ring

end UV
