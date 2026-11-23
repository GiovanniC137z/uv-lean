import UV.ContinueHeatMaxwellTaylor
import UV.ContinueHeatMaxwellLoopInputs

/-! Constant, linear and quadratic coefficients for the original native
shifted heat symbols and both integrated marks, in their normalized
three-vector coordinate basis. -/

noncomputable section
namespace UV.HeatMaxwell
open UV.SectorPlane UV.RelativeSoft MeasureTheory Filter Set
open scoped RealInnerProductSpace Topology

private abbrev K := EuclideanPlaneMomentum

theorem heat_carrier_scale (k : K) (c : ℝ) (v : ℝ×ℝ×ℝ) :
    heatCarrierVector k (vectorScale c v) = c • heatCarrierVector k v := by
  simp only [vectorScale,heatCarrierVector,smul_add,smul_smul]
theorem heat_carrier_zero (k : K) : heatCarrierVector k vectorZero=0 := by simp [heatCarrierVector,vectorZero]
theorem heat_carrier_k (k : K) : heatCarrierVector k heatK=k := by simp [heatCarrierVector,heatK]

private theorem heat_centered_mass : heatCenteredLaw.real univ=1 := by
  simp [heatCenteredLaw,Measure.real,Real.volume_Ioc]
  norm_num

private theorem heat_contact_mass : heatContactLaw.real univ=1 := by
  change ((heatUnitLaw.prod heatUnitLaw) univ).toReal=1
  rw [←univ_prod_univ,Measure.prod_prod]
  simp [heatUnitLaw,Real.volume_Ioc]

private theorem heat_centered_mean : (∫ x : ℝ, id x ∂heatCenteredLaw)=0 := by
  rw [show (∫ x : ℝ, id x ∂heatCenteredLaw) = ∫ x in (-1/2:ℝ)..(1/2:ℝ), x from
    (intervalIntegral.integral_of_le (by norm_num : (-1/2:ℝ)≤1/2)).symm,integral_id]
  norm_num

private theorem heat_contact_mean : (∫ p : ℝ×ℝ, p.1-p.2 ∂heatContactLaw)=0 := by
  have h := Measure.measurePreserving_swap (μ:=heatUnitLaw) (ν:=heatUnitLaw)
  have he := h.integral_comp MeasurableEquiv.prodComm.measurableEmbedding (fun p : ℝ×ℝ => p.1-p.2)
  change (∫ p : ℝ×ℝ, p.2-p.1 ∂heatContactLaw)=_ at he
  have hn : (∫ p : ℝ×ℝ, p.2-p.1 ∂heatContactLaw)= -(∫ p : ℝ×ℝ, p.1-p.2 ∂heatContactLaw) := by
    rw [←integral_neg]
    simp
  linarith

private theorem heat_averaged_germ {ι : Type*} [MeasurableSpace ι] {μ : Measure ι} [IsFiniteMeasure μ]
    {a : ι→ℝ} (ha : Measurable a) (hb : ∀ᵐ z ∂μ, |a z|≤1)
    (hμ : μ.real univ=1) (h0 : (∫ z, a z ∂μ)=0)
    {f : ℝ→K} (hf : ContDiff ℝ 2 f) {v w : K} (hv : f 0=v)
    (hw : deriv (deriv (heatChordMoment μ a 0 f)) 0=(2:ℝ) • w) :
    HeatJetGerm (heatChordMoment μ a 0 f) v 0 w := by
  have h1 (t) := (hf.differentiable (by norm_num) t).hasDerivAt
  have hf' : ContDiff ℝ 1 (deriv f) := hf.deriv'
  have h2 (t) := (hf'.differentiable (by norm_num) t).hasDerivAt
  have hd (t) := heat_chord_moment_hasDerivAt ha hb hf'.continuous h1 0 t
  have he : deriv (heatChordMoment μ a 0 f) = heatChordMoment μ a 1 (deriv f) := funext fun t => (hd t).deriv
  apply HeatJetGerm.of_derivatives (fun t => (hd t).differentiableAt) _ _ _ hw
  · rw [he]
    exact (heat_chord_moment_hasDerivAt ha hb (hf'.continuous_deriv (by norm_num)) h2 1 0).differentiableAt
  · simp [heatChordMoment,hμ,hv]
  · rw [he]
    simp [heatChordMoment,integral_smul_const,h0]

def heatNormalizedMotion (k : K) (f : ℝ→K) : ℝ→K := fun t => (Real.exp (-‖k‖^2))⁻¹ • f t

theorem heat_shifted_germ (k : K) (a : ℝ) :
    VectorGerm k (heatNormalizedMotion k (fun t => heatSymbol (k+(a*t) • softLongitudinal.val)))
      ⟨heatK,vectorScale a (heatH₁ ⟪k,softLongitudinal.val⟫),
       vectorScale (a^2/2) (heatH₁₁ ⟪k,softLongitudinal.val⟫)⟩ := by
  let f := fun s : ℝ => heatSymbol (k+s • softLongitudinal.val)
  let c := Real.exp (-‖k‖^2)
  have hf : ContDiff ℝ 2 f := by
    have he (t) := heatSymbol_two_unit_shifts k t 0
    have H : f = fun t => (c*heatShiftFactor ⟪k,softLongitudinal.val⟫ t) • (k+t • softLongitudinal.val) := by
      funext t
      simpa only [f,c,zero_smul,add_zero,heatShiftFactor_at_zero,mul_one] using he t
    rw [H]
    unfold heatShiftFactor
    fun_prop
  have h := heatSymbol_longitudinal_derivatives k
  have hG : HeatJetGerm f (c • k) (c • heatCarrierVector k (heatH₁ ⟪k,softLongitudinal.val⟫))
      ((1/2:ℝ) • (c • heatCarrierVector k (heatH₁₁ ⟪k,softLongitudinal.val⟫))) := by
    apply HeatJetGerm.of_derivatives (hf.differentiable (by norm_num)) (hf.differentiable_deriv_two _)
    · simp [f,heatSymbol,c]
    · exact h.1
    · rw [smul_smul,show (2:ℝ)*(1/2)=1 by norm_num,one_smul]
      exact h.2
  have he := (hG.scale c⁻¹).reparam a
  have hc : c≠0 := Real.exp_ne_zero _
  unfold VectorGerm
  rw [heat_carrier_k,heat_carrier_scale,heat_carrier_scale]
  convert he using 1
  · rw [smul_smul,inv_mul_cancel₀ hc,one_smul]
  · rw [smul_smul c⁻¹ c,inv_mul_cancel₀ hc,one_smul]
  · simp only [smul_smul];congr 1;field_simp

def heatContactBase (j : ℝ) : ℝ×ℝ×ℝ := (4*j^2-2,0,-4*j)

theorem heat_first_germ (k : K) :
    VectorGerm k (heatNormalizedMotion k (heatFirstChord k))
      ⟨heatH₂ ⟪k,softTransverse.val⟫,vectorZero,
        vectorScale (1/24) (heatH₁₁₂ ⟪k,softLongitudinal.val⟫ ⟪k,softTransverse.val⟫)⟩ := by
  let c := Real.exp (-‖k‖^2)
  have hv : heatFirstLocal k 0=c • heatCarrierVector k (heatH₂ ⟪k,softTransverse.val⟫) := by
    rw [heatFirstLocal,(heatSymbol_transverse_derivatives k 0).1]
    simp [heatCarrierVector,heatH₂,heatShiftFactor_at_zero,c]
  have h := heat_averaged_germ measurable_id heat_centered_bound heat_centered_mass heat_centered_mean
    (heat_first_local_contDiff k) hv (w:=(1/24:ℝ) • (c • heatCarrierVector k (heatH₁₁₂ ⟪k,softLongitudinal.val⟫ ⟪k,softTransverse.val⟫))) (by
      change deriv (deriv (heatFirstChord k)) 0=_
      rw [heat_first_chord_second];change (1/12:ℝ) • (c • _)=(2:ℝ) • ((1/24:ℝ) • (c • _));rw [smul_smul (2:ℝ) (1/24)];norm_num)
  have hc : c≠0 := Real.exp_ne_zero _
  convert h.scale c⁻¹ using 1
  · rw [smul_smul,inv_mul_cancel₀ hc,one_smul]
  · rw [heat_carrier_zero,smul_zero]
  · rw [heat_carrier_scale,smul_comm c⁻¹ (1/24:ℝ),smul_smul c⁻¹ c,inv_mul_cancel₀ hc,one_smul]

theorem heat_contact_germ (k : K) :
    VectorGerm k (heatNormalizedMotion k (heatContactChord k))
      ⟨heatContactBase ⟪k,softTransverse.val⟫,vectorZero,
        vectorScale (1/12) (heatH₁₁₂₂ ⟪k,softLongitudinal.val⟫ ⟪k,softTransverse.val⟫)⟩ := by
  let c := Real.exp (-‖k‖^2)
  have hv : heatContactLocal k 0=c • heatCarrierVector k (heatContactBase ⟪k,softTransverse.val⟫) := by
    rw [heatContactLocal,(heatSymbol_transverse_derivatives k 0).2]
    simp [heatCarrierVector,heatContactBase,heatShiftFactor_at_zero,c]
  have h := heat_averaged_germ (measurable_fst.sub measurable_snd) heat_contact_bound heat_contact_mass heat_contact_mean
    (heat_contact_local_contDiff k) hv (w:=(1/12:ℝ) • (c • heatCarrierVector k (heatH₁₁₂₂ ⟪k,softLongitudinal.val⟫ ⟪k,softTransverse.val⟫))) (by
      change deriv (deriv (heatContactChord k)) 0=_
      rw [heat_contact_chord_second];change (1/6:ℝ) • (c • _)=(2:ℝ) • ((1/12:ℝ) • (c • _));rw [smul_smul (2:ℝ) (1/12)];norm_num)
  have hc : c≠0 := Real.exp_ne_zero _
  convert h.scale c⁻¹ using 1
  · rw [smul_smul,inv_mul_cancel₀ hc,one_smul]
  · rw [heat_carrier_zero,smul_zero]
  · rw [heat_carrier_scale,smul_comm c⁻¹ (1/12:ℝ),smul_smul c⁻¹ c,inv_mul_cancel₀ hc,one_smul]

end UV.HeatMaxwell
