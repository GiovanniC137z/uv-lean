import UV.ExtendCurvaturePotential
import Mathlib.Analysis.MeanInequalitiesPow

/-! Integrable Gaussian bounds for the literal torus bracket potential at
one positive normal depth, on the existing common source preparation. -/

noncomputable section

open MeasureTheory Filter Real
open scoped BigOperators Topology ENNReal NNReal

namespace UV.AdvanceCurvatureEnvelope

open UV.ExtendCurvaturePotential UV.NextCurvatureLaw UV.NextCurvatureFourierSummability

private def slotWeight {n : ℕ} (ℓ : ℝ) (i : ModeSlot n) : ℝ :=
  derivativeWeight 0 ℓ i.1

private theorem slotWeight_nonneg {n : ℕ} (ℓ : ℝ) (i : ModeSlot n) :
    0 ≤ slotWeight ℓ i := derivativeWeight_nonneg 0 ℓ i.1

private theorem slotWeight_summable {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) :
    Summable (slotWeight (n := n) ℓ) := by
  apply (summable_prod_of_nonneg (slotWeight_nonneg ℓ)).2
  refine ⟨fun _ => summable_of_finite_support (Set.toFinite _), ?_⟩
  simp only [slotWeight, tsum_fintype, Finset.sum_const, nsmul_eq_mul]
  exact (derivativeWeight_summable 0 hℓ).mul_left _

private theorem base_abs_pow_integrable (r : ℕ) :
    Integrable (fun x : ℝ => |x| ^ r) UV.sourceGaussianBase := by
  have h := UV.sourceGaussian_power_integrable (1/2 : ℝ) r
  have he : UV.sourceGaussian (1/2 : ℝ) =
      UV.sourceGaussianBase := by
    unfold UV.sourceGaussian
    norm_num
  simpa only [he, Real.norm_eq_abs, abs_pow] using h.norm

private def weightMoment {n : ℕ} (ℓ : ℝ) (r : ℕ) (X : ModeSlot n → ℝ) : ℝ :=
  ∑' i, slotWeight ℓ i * |X i| ^ r

private theorem weightMoment_integrable_and_ae_summable {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (r : ℕ) :
    Integrable (weightMoment (n := n) ℓ r) (commonGaussian n) ∧
      ∀ᵐ X ∂commonGaussian n, Summable (fun i => slotWeight ℓ i * |X i| ^ r) := by
  let m := ∫ x : ℝ, |x| ^ r ∂UV.sourceGaussianBase
  have hm : 0 ≤ m := integral_nonneg (fun _ => pow_nonneg (abs_nonneg _) _)
  let f (i : ModeSlot n) (X : ModeSlot n → ℝ) : ℝ≥0 :=
    ⟨slotWeight ℓ i * |X i| ^ r, mul_nonneg (slotWeight_nonneg ℓ i) (pow_nonneg (abs_nonneg _) _)⟩
  let G (X : ModeSlot n → ℝ) := ∑' i, (f i X : ℝ≥0∞)
  have hf (i : ModeSlot n) : Integrable (fun X => (f i X : ℝ)) (commonGaussian n) := by
    have he := measurePreserving_eval_infinitePi
      (μ := fun _ : ModeSlot n => UV.sourceGaussianBase) i
    exact ((he.integrable_comp_of_integrable (base_abs_pow_integrable r)).const_mul (slotWeight ℓ i))
  have hfm (i : ModeSlot n) : AEMeasurable (fun X => (f i X : ℝ≥0∞)) (commonGaussian n) := by
    have h : Measurable (fun X : ModeSlot n → ℝ => slotWeight ℓ i * |X i| ^ r) := by fun_prop
    convert h.ennreal_ofReal.aemeasurable using 1
    funext X
    rw [ENNReal.ofReal_eq_coe_nnreal (mul_nonneg (slotWeight_nonneg ℓ i)
      (pow_nonneg (abs_nonneg _) r))]
  have hGm : AEMeasurable G (commonGaussian n) := AEMeasurable.ennreal_tsum hfm
  have hintegral (i : ModeSlot n) : (∫ X, (f i X : ℝ) ∂commonGaussian n) = slotWeight ℓ i * m := by
    change (∫ X, slotWeight ℓ i * |X i| ^ r ∂commonGaussian n) = _
    rw [integral_const_mul]
    have he := measurePreserving_eval_infinitePi
      (μ := fun _ : ModeSlot n => UV.sourceGaussianBase) i
    congr 1
    calc
      _ = ∫ x : ℝ, |x| ^ r ∂(commonGaussian n).map (Function.eval i) :=
        (integral_map he.measurable.aemeasurable
          (by fun_prop : Measurable (fun x : ℝ => |x| ^ r)).aestronglyMeasurable).symm
      _ = m := congrArg (fun ν : Measure ℝ => ∫ x : ℝ, |x| ^ r ∂ν) he.map_eq
  have hG : (∫⁻ X, G X ∂commonGaussian n) ≠ ∞ := by
    unfold G
    rw [lintegral_tsum hfm]
    have he (i : ModeSlot n) : (∫⁻ X, (f i X : ℝ≥0∞) ∂commonGaussian n) =
        ENNReal.ofReal (slotWeight ℓ i * m) := by
      rw [lintegral_coe_eq_integral _ (hf i), hintegral i]
    simp_rw [he]
    let g (i : ModeSlot n) : ℝ≥0 := ⟨slotWeight ℓ i * m, mul_nonneg (slotWeight_nonneg ℓ i) hm⟩
    have hee (i : ModeSlot n) : ENNReal.ofReal (slotWeight ℓ i * m) = (g i : ℝ≥0∞) :=
      ENNReal.ofReal_eq_coe_nnreal _
    simp_rw [hee]
    exact ENNReal.tsum_coe_ne_top_iff_summable_coe.2 ((slotWeight_summable hℓ).mul_right m)
  have hae : ∀ᵐ X ∂commonGaussian n, Summable (fun i => (f i X : ℝ)) :=
    (ae_lt_top' hGm hG).mono fun X hX => ENNReal.tsum_coe_ne_top_iff_summable_coe.1 hX.ne
  refine ⟨(integrable_toReal_of_lintegral_ne_top hGm hG).congr ?_, hae⟩
  filter_upwards [hae] with X hX
  change (∑' i, (f i X : ℝ≥0∞)).toReal = ∑' i, (f i X : ℝ)
  rw [← ENNReal.coe_tsum (NNReal.summable_coe.mp hX), ENNReal.coe_toReal, NNReal.coe_tsum]

private theorem finite_pow_weighted_sum_bound {ι : Type*} (s : Finset ι) (w a : ι → ℝ)
    {W : ℝ} (hW : 1 ≤ W) (hw : ∀ i, 0 ≤ w i) (ha : ∀ i, 0 ≤ a i)
    (hs : ∑ i ∈ s, w i ≤ W) (r : ℕ) (hr : 0 < r) :
    (∑ i ∈ s, w i * a i) ^ r ≤ W ^ r * ∑ i ∈ s, w i * a i ^ r := by
  have hWp : 0 < W := zero_lt_one.trans_le hW
  let q (i : ι) := w i / W
  let v := 1 - ∑ i ∈ s, q i
  have hv : 0 ≤ v := sub_nonneg.mpr (by
    unfold q
    rw [← Finset.sum_div]
    exact (div_le_one hWp).mpr hs)
  have he : v + ∑ i ∈ s, q i = 1 := sub_add_cancel 1 _
  have hj := (convexOn_pow r).map_add_sum_le (t := s) (w := q) (p := a) (v := v) (q := 0)
    (fun i _ => div_nonneg (hw i) hWp.le) he (fun i _ => ha i) hv (le_refl (0 : ℝ))
  simp only [smul_eq_mul, mul_zero, zero_add, zero_pow hr.ne'] at hj
  have hh (g : ι → ℝ) : ∑ i ∈ s, q i * g i = (∑ i ∈ s, w i * g i) / W := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => by unfold q; ring
  rw [hh a, hh (fun x => a x ^ r), div_pow] at hj
  calc
    _ ≤ (∑ i ∈ s, w i * a i ^ r) / W * W^r := (div_le_iff₀ (pow_pos hWp _)).mp hj
    _ ≤ _ := by
      rw [mul_comm (W^r)]
      exact mul_le_mul_of_nonneg_right (div_le_self (Finset.sum_nonneg fun i _ =>
        mul_nonneg (hw i) (pow_nonneg (ha i) _)) hW) (pow_nonneg hWp.le _)

private theorem weightMoment_pow_integrable {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (r : ℕ) :
    Integrable (fun X => weightMoment (n := n) ℓ 1 X ^ r) (commonGaussian n) := by
  by_cases hr : r = 0
  · simp [hr]
  let W : ℝ := 1 + ∑' i : ModeSlot n, slotWeight ℓ i
  have hW : 1 ≤ W := le_add_of_nonneg_right (tsum_nonneg (slotWeight_nonneg ℓ))
  have hi := weightMoment_integrable_and_ae_summable (n := n) hℓ 1
  have hp := weightMoment_integrable_and_ae_summable (n := n) hℓ r
  apply (hp.1.const_mul (W^r)).mono' (hi.1.aestronglyMeasurable.pow r)
  filter_upwards [hi.2, hp.2] with X hX hY
  have hc : ∀ s : Finset (ModeSlot n), (∑ i ∈ s, slotWeight ℓ i * |X i|) ^ r ≤
      W^r * ∑ i ∈ s, slotWeight ℓ i * |X i| ^ r := fun s =>
    finite_pow_weighted_sum_bound s (slotWeight ℓ) (fun i => |X i|) hW
      (slotWeight_nonneg ℓ) (fun _ => abs_nonneg _)
      (((slotWeight_summable hℓ).sum_le_tsum s (fun i _ => slotWeight_nonneg ℓ i)).trans
        (le_add_of_nonneg_left zero_le_one)) _ (Nat.pos_of_ne_zero hr)
  have hX' : Summable (fun i => slotWeight ℓ i * |X i|) := by simpa using hX
  change ‖weightMoment ℓ 1 X ^ r‖ ≤ W ^ r * weightMoment ℓ r X
  have hnonneg : 0 ≤ weightMoment ℓ 1 X :=
    tsum_nonneg (fun i => mul_nonneg (slotWeight_nonneg ℓ i) (pow_nonneg (abs_nonneg _) _))
  rw [Real.norm_of_nonneg (pow_nonneg hnonneg _)]
  unfold weightMoment
  simp only [pow_one]
  have hx : Tendsto (fun s : Finset (ModeSlot n) => ∑ i ∈ s, slotWeight ℓ i * |X i|)
      atTop (𝓝 (∑' i, slotWeight ℓ i * |X i|)) := hX'.hasSum
  have hy : Tendsto (fun s : Finset (ModeSlot n) => ∑ i ∈ s, slotWeight ℓ i * |X i| ^ r)
      atTop (𝓝 (∑' i, slotWeight ℓ i * |X i| ^ r)) := hY.hasSum
  exact le_of_tendsto_of_tendsto (hx.pow r) (hy.const_mul (W^r)) (Eventually.of_forall hc)

private theorem cutoff_field_norm_le {n : ℕ} (Λ ℓ : ℝ) (X : ModeSlot n → ℝ)
    (hX : Summable (fun i => slotWeight ℓ i * |X i| ^ 1)) (a : Fin 2) (c : Fin n) :
    ‖cutoffTransferredField Λ ℓ X a c‖ ≤ sqrt 2 * weightMoment ℓ 1 X := by
  have hnorm (k : MeanZeroMode) : ‖transferredTerm ℓ X a c k‖ ≤
      sqrt 2 * (slotWeight ℓ (k, (a,c)) * |X (k,(a,c))|) := by
    unfold transferredTerm slotWeight
    rw [norm_smul, norm_mul, Real.norm_of_nonneg (derivativeWeight_nonneg 0 ℓ k),
      Real.norm_eq_abs, mul_comm (sqrt 2)]
    exact mul_le_mul_of_nonneg_left (realTorusMode_norm_bound k)
      (mul_nonneg (derivativeWeight_nonneg 0 ℓ k) (abs_nonneg _))
  unfold cutoffTransferredField
  calc
    _ ≤ ∑ k ∈ retainedModes Λ, sqrt 2 * (slotWeight ℓ (k,(a,c)) * |X (k,(a,c))|) :=
      norm_sum_le_of_le _ (fun k _ => hnorm k)
    _ ≤ _ := by
      rw [← Finset.mul_sum]
      apply mul_le_mul_of_nonneg_left _ (sqrt_nonneg _)
      let e : MeanZeroMode ↪ ModeSlot n := ⟨fun k => (k,(a,c)), fun _ _ h => congrArg Prod.fst h⟩
      have hb := hX.sum_le_tsum ((retainedModes Λ).map e) (fun j _ =>
        mul_nonneg (slotWeight_nonneg ℓ j) (pow_nonneg (abs_nonneg _) _))
      rw [Finset.sum_map] at hb
      simpa only [e, Function.Embedding.coeFn_mk, pow_one, weightMoment] using hb

private def colorL1 {n : ℕ} (B : Fin n → Fin n → Fin n → ℝ) (c : Fin n) : ℝ :=
  ∑ a, ∑ b, |B c a b|

private def bracketBoundConstant {n : ℕ} (B : Fin n → Fin n → Fin n → ℝ) : ℝ :=
  (1/2) * ∑ c, colorL1 B c ^ 2

private theorem cutoff_potential_norm_le {n : ℕ} (B : Fin n → Fin n → Fin n → ℝ)
    (Λ ℓ : ℝ) (X : ModeSlot n → ℝ) (hX : Summable (fun i => slotWeight ℓ i * |X i| ^ 1)) :
    ‖cutoffBracketPotential B Λ ℓ X‖ ≤ bracketBoundConstant B * (sqrt 2 * weightMoment ℓ 1 X)^4 := by
  let A := sqrt 2 * weightMoment ℓ 1 X
  have hA : 0 ≤ A := mul_nonneg (sqrt_nonneg _)
    (tsum_nonneg (fun i => mul_nonneg (slotWeight_nonneg ℓ i) (pow_nonneg (abs_nonneg _) _)))
  let U := cutoffTransferredField Λ ℓ X 0
  let W := cutoffTransferredField Λ ℓ X 1
  have hU (a : Fin n) : ‖U a‖ ≤ A := cutoff_field_norm_le Λ ℓ X hX 0 a
  have hW (b : Fin n) : ‖W b‖ ≤ A := cutoff_field_norm_le Λ ℓ X hX 1 b
  have hb (c : Fin n) : ‖bracketCoordinate B U W c‖ ≤ colorL1 B c * A ^ 2 := by
    unfold bracketCoordinate colorL1
    simp_rw [Finset.sum_mul]
    apply norm_sum_le_of_le _
    intro a _
    apply norm_sum_le_of_le _
    intro b _
    rw [norm_smul, Real.norm_eq_abs, pow_two]
    exact mul_le_mul_of_nonneg_left ((norm_mul_le _ _).trans
      (mul_le_mul (hU a) (hW b) (norm_nonneg _) hA)) (abs_nonneg _)
  have hd : ‖bracketDensity B U W‖ ≤ bracketBoundConstant B * A^4 := by
    unfold bracketDensity bracketBoundConstant
    rw [norm_smul, Real.norm_of_nonneg (by positivity : (0:ℝ) ≤ 1/2), mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [Finset.sum_mul]
    apply norm_sum_le_of_le _
    intro c _
    exact (norm_pow_le _ _).trans ((pow_le_pow_left₀ (norm_nonneg _) (hb c) 2).trans_eq (by ring))
  change ‖normalizedIntegral (bracketDensity B U W)‖ ≤ _
  exact (BoundedContinuousFunction.norm_integral_le_norm normalizedTorusVolume
    (BoundedContinuousFunction.mkOfCompact (bracketDensity B U W))).trans (by simpa using hd)

/-- A uniform-in-cutoff integrable envelope for every nonnegative integer
power of the original quartic potential at a strictly positive depth. -/
theorem bracketPotential_power_envelope {n : ℕ} (B : Fin n → Fin n → Fin n → ℝ)
    {ℓ : ℝ} (hℓ : 0 < ℓ) (q : ℕ) :
    ∃ E : (ModeSlot n → ℝ) → ℝ, Integrable E (commonGaussian n) ∧
      ∀ᵐ X ∂commonGaussian n, ∀ Λ : ℝ, ‖cutoffBracketPotential B Λ ℓ X ^ q‖ ≤ E X := by
  let K := bracketBoundConstant B * (sqrt 2)^4
  refine ⟨fun X => K^q * weightMoment ℓ 1 X ^ (4*q),
    (weightMoment_pow_integrable hℓ (4*q)).const_mul _, ?_⟩
  filter_upwards [(weightMoment_integrable_and_ae_summable (n := n) hℓ 1).2] with X hX
  intro Λ
  calc
    _ ≤ ‖cutoffBracketPotential B Λ ℓ X‖^q := norm_pow_le _ _
    _ ≤ (bracketBoundConstant B * (sqrt 2 * weightMoment ℓ 1 X)^4)^q :=
      pow_le_pow_left₀ (norm_nonneg _) (cutoff_potential_norm_le B Λ ℓ X hX) _
    _ = _ := by unfold K; rw [mul_pow (sqrt 2), ← mul_assoc, mul_pow, ← pow_mul]

private theorem cutoff_potential_measurable {n : ℕ} (B : Fin n → Fin n → Fin n → ℝ)
    (Λ ℓ : ℝ) : Measurable (fun X : ModeSlot n → ℝ => cutoffBracketPotential B Λ ℓ X) := by
  change Measurable ((fun p : ℝ × (ModeSlot n → ℝ) => cutoffBracketPotential B Λ p.1 p.2) ∘
    (fun X : ModeSlot n → ℝ => (ℓ, X)))
  apply Measurable.comp (cutoffBracketPotential_measurable B Λ)
  exact measurable_const.prodMk measurable_id

/-- For the fixed positive depth and the original Gaussian product law,
cutoff bracket powers are integrable and their expectations converge to
the actual continuum powers. This uses the spherical transfer limit. -/
theorem bracketPotential_power_integral_limit {n : ℕ} (B : Fin n → Fin n → Fin n → ℝ)
    {ℓ : ℝ} (hℓ : 0 < ℓ) (q : ℕ) :
    (∀ Λ : ℝ, Integrable (fun X => cutoffBracketPotential B Λ ℓ X ^ q) (commonGaussian n)) ∧
    Integrable (fun X => fullBracketPotential B ℓ X ^ q) (commonGaussian n) ∧
    Tendsto (fun Λ : ℝ => ∫ X, cutoffBracketPotential B Λ ℓ X ^ q ∂commonGaussian n) atTop
      (𝓝 (∫ X, fullBracketPotential B ℓ X ^ q ∂commonGaussian n)) := by
  obtain ⟨E, hE, hbound⟩ := bracketPotential_power_envelope B hℓ q
  have hM (Λ : ℝ) : AEStronglyMeasurable (fun X => cutoffBracketPotential B Λ ℓ X ^ q)
      (commonGaussian n) := ((cutoff_potential_measurable B Λ ℓ).pow_const q).aestronglyMeasurable
  have ht := (ae_bracketPotential_limit B hℓ).mono fun _ h => h.pow q
  have hf : AEStronglyMeasurable (fun X => fullBracketPotential B ℓ X ^ q) (commonGaussian n) :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun j : ℕ => hM j)
      (ht.mono fun _ h => h.comp tendsto_natCast_atTop_atTop)
  refine ⟨fun Λ => hE.mono' (hM Λ) (hbound.mono fun _ h => h Λ), hE.mono' hf ?_, ?_⟩
  · filter_upwards [ht, hbound] with X hX hB
    exact le_of_tendsto hX.norm (Eventually.of_forall hB)
  · exact tendsto_integral_filter_of_dominated_convergence E (Eventually.of_forall hM)
      (Eventually.of_forall fun Λ => hbound.mono fun _ h => h Λ) hE ht

end UV.AdvanceCurvatureEnvelope
