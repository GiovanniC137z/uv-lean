import UV.ExtendOpticalProjectorObstruction
import UV.NextOpticalOverlap

/-! The finite-slot sea can change occupied rank on a set of finite
measure. The rank defect relative to the onsite projector is integrable,
so translating it contributes zero to the integrated identity-shift
density. All limits use one fixed oriented sector plane. -/

noncomputable section

open Filter Set MeasureTheory Matrix
open scoped Topology ComplexConjugate Matrix ENNReal

namespace UV.ContinuationBoostSpectrum

variable {d : ℕ}

private theorem inclusive_nonneg (A : Matrix (Fin d) (Fin d) ℂ) : 0 ≤ chargeInclusiveSquare A :=
  Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => Complex.normSq_nonneg _))

private theorem projected_overlap_nonneg {A B : Matrix (Fin d) (Fin d) ℂ}
    (hA : Aᴴ=A) (hB : Bᴴ=B) (hAA : A*A=A) (hBB : B*B=B) :
    0 ≤ (((1-A)*B).trace).re := by
  let C := 1-A
  have hadj : Cᴴ=C := by dsimp [C]; rw [conjTranspose_sub,conjTranspose_one,hA]
  have hsq : C*C=C := by dsimp [C]; noncomm_ring [hAA]
  have ht := inclusive_nonneg (C*B)
  rw [chargeInclusiveSquare_eq_trace,conjTranspose_mul,hB,hadj,
    show (B*C)*(C*B) = (B*(C*C))*B by noncomm_ring,hsq,
    Matrix.trace_mul_comm (B*C) B,←mul_assoc,hBB,Matrix.trace_mul_comm B C] at ht
  exact ht

theorem projection_overlap_with_trace_defect {A B : Matrix (Fin d) (Fin d) ℂ}
    (hA : Aᴴ=A) (hB : Bᴴ=B) (hAA : A*A=A) (hBB : B*B=B) :
    (((1-A)*B).trace).re =
      (chargeInclusiveSquare (A-B) + B.trace.re - A.trace.re)/2 := by
  rw [chargeInclusiveSquare_eq_trace,conjTranspose_sub,hA,hB,sub_mul,one_mul,
    mul_sub,sub_mul,sub_mul,hAA,hBB]
  simp only [Matrix.trace_sub,Complex.sub_re]
  rw [Matrix.trace_mul_comm B A]
  ring

theorem projector_trace_defect_bound {A B : Matrix (Fin d) (Fin d) ℂ}
    (hA : Aᴴ=A) (hB : Bᴴ=B) (hAA : A*A=A) (hBB : B*B=B) :
    |A.trace.re-B.trace.re| ≤ chargeInclusiveSquare (A-B) := by
  have h₁ := projected_overlap_nonneg hA hB hAA hBB
  have h₂ := projected_overlap_nonneg hB hA hBB hAA
  rw [projection_overlap_with_trace_defect hA hB hAA hBB] at h₁
  rw [projection_overlap_with_trace_defect hB hA hBB hAA] at h₂
  have he : chargeInclusiveSquare (B-A) = chargeInclusiveSquare (A-B) := by
    simp only [chargeInclusiveSquare_sub_eq,matrixOverlap_symm B A]; ring
  rw [he] at h₂
  exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem canonicalDensity_variable_rank_identity {E : Type*} [Norm E] (diamond : SectorPlane.Plane E)
    (P : SectorPlane.Plane E → ChargeSpatialMomentum → Matrix (Fin d) (Fin d) ℂ) (P₀ : Matrix (Fin d) (Fin d) ℂ)
    (h₀ : P₀ᴴ=P₀) (h₀₀ : P₀*P₀=P₀) (hm : ∀ i j, Measurable (fun k => P diamond k i j))
    (ha : ∀ k, (P diamond k)ᴴ = P diamond k) (hi : ∀ k, P diamond k*P diamond k=P diamond k)
    (hL : Integrable (fun k => chargeInclusiveSquare (P diamond k-P₀))) (p : ChargeSpatialMomentum) :
    canonicalDensity (P diamond) p = spatialMeasureFactor *
      ((∫ k, chargeInclusiveSquare (P diamond k-P₀)) - ∫ k, matrixOverlap (P diamond (k+p)-P₀) (P diamond k-P₀)) := by
  let F := fun k => P diamond k-P₀
  let q := fun k => chargeInclusiveSquare (F k)
  let t := fun k => (P diamond k).trace.re - P₀.trace.re
  let b := fun k => matrixOverlap (F (k+p)) (F k)
  have hF (i j) : Measurable (fun k => F k i j) := (hm i j).sub measurable_const
  have hp := measurePreserving_add_right (volume : Measure ChargeSpatialMomentum) p
  have hq : Integrable q := hL
  have hq' : Integrable (fun k => q (k+p)) := hp.integrable_comp_of_integrable hq
  have ht : Integrable t := by
    apply hq.mono'
    · apply Measurable.aestronglyMeasurable
      exact ((Complex.continuous_re.measurable.comp (Finset.measurable_sum _ (fun i _ => hm i i))).sub measurable_const)
    · exact Eventually.of_forall fun k => projector_trace_defect_bound (ha k) h₀ (hi k) h₀₀
  have ht' := hp.integrable_comp_of_integrable ht
  have hb : Integrable b := by
    apply (hq'.add hq).mono'
    · apply Measurable.aestronglyMeasurable
      exact Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ =>
        Complex.continuous_re.measurable.comp (((hF i j).comp (measurable_id.add measurable_const)).mul
          (Complex.continuous_conj.measurable.comp (hF i j)))
    · apply Eventually.of_forall
      intro k
      simpa only [Real.norm_eq_abs,inv_one,one_mul] using (matrixOverlap_abs_bound (F (k+p)) (F k) zero_lt_one)
  have shift (f : ChargeSpatialMomentum → ℝ) : (∫ k, f (k+p)) = ∫ k, f k :=
    hp.integral_comp (Homeomorph.addRight p).measurableEmbedding f
  have hpt (k) : (((1-P diamond (k+p))*P diamond k).trace).re =
      ((q (k+p)+q k-2*b k)+(t k-t (k+p)))/2 := by
    rw [projection_overlap_with_trace_defect (ha _) (ha _) (hi _) (hi _),
      show P diamond (k+p)-P diamond k = F (k+p)-F k by dsimp [F]; abel,chargeInclusiveSquare_sub_eq]
    dsimp only [q,t,b]; ring
  unfold canonicalDensity
  congr 1
  simp_rw [hpt]
  have hsub : Integrable (fun k => q (k+p)+q k-2*b k) := (hq'.add hq).sub (hb.const_mul _)
  have htShift : Integrable (fun k => t (k+p)) := ht'
  have htDiff : Integrable (fun k => t k - t (k+p)) := ht.sub htShift
  have hqSum : Integrable (fun k => q (k+p) + q k) := hq'.add hq
  have hbDbl : Integrable (fun k => 2*b k) := hb.const_mul _
  rw [integral_div,integral_add hsub htDiff,integral_sub ht htShift,shift t,
    integral_sub hqSum hbDbl,integral_add hq' hq,integral_const_mul,shift q]
  change ((∫ k, q k)+(∫ k, q k)-2*(∫ k, b k)+((∫ k, t k)-(∫ k, t k)))/2 = _
  dsimp only [q,b,F]; ring

theorem canonicalDensity_variable_rank_limit {E : Type*} [Norm E] (diamond : SectorPlane.Plane E)
    (P : SectorPlane.Plane E → ChargeSpatialMomentum → Matrix (Fin d) (Fin d) ℂ) (P₀ : Matrix (Fin d) (Fin d) ℂ)
    (h₀ : P₀ᴴ=P₀) (h₀₀ : P₀*P₀=P₀) (hm : ∀ i j, Measurable (fun k => P diamond k i j))
    (ha : ∀ k, (P diamond k)ᴴ = P diamond k) (hi : ∀ k, P diamond k*P diamond k=P diamond k)
    (hL : Integrable (fun k => chargeInclusiveSquare (P diamond k-P₀))) {α : Type*} {l : Filter α}
    (p : α → ChargeSpatialMomentum) (hp : Tendsto (fun x => ‖p x‖) l atTop) :
    Tendsto (fun x => canonicalDensity (P diamond) (p x)) l
      (𝓝 (spatialMeasureFactor*∫ k, chargeInclusiveSquare (P diamond k-P₀))) := by
  have h := matrixOverlap_tendsto_zero hL p hp
  have hc : Tendsto (fun _ : α => ∫ k, chargeInclusiveSquare (P diamond k-P₀)) l _ := tendsto_const_nhds
  simpa only [canonicalDensity_variable_rank_identity diamond P P₀ h₀ h₀₀ hm ha hi hL,sub_zero] using
    (hc.sub h).const_mul spatialMeasureFactor

/-- Without any constant-rank hypothesis, a finite-slot canonical sea
cannot dominate the time-component measure of a nonzero timelike band. -/
theorem variable_rank_cannot_dominate_timelike_band {E : Type*} [Norm E] (diamond : SectorPlane.Plane E)
    (P : SectorPlane.Plane E → ChargeSpatialMomentum → Matrix (Fin d) (Fin d) ℂ) (P₀ : Matrix (Fin d) (Fin d) ℂ)
    (h₀ : P₀ᴴ=P₀) (h₀₀ : P₀*P₀=P₀) (hm : ∀ i j, Measurable (fun k => P diamond k i j))
    (ha : ∀ k, (P diamond k)ᴴ = P diamond k) (hi : ∀ k, P diamond k*P diamond k=P diamond k)
    (hL : Integrable (fun k => chargeInclusiveSquare (P diamond k-P₀)))
    (ρ : Measure ℝ) {s₁ s₂ S₀ : ℝ} (h₁ : 0 < s₁) (h₁₂ : s₁ ≤ s₂)
    (hFin : ρ (Icc s₁ s₂) ≠ ∞) (hPos : ρ (Icc s₁ s₂) ≠ 0) :
    ¬ (∀ S > S₀, 0 < S → (NextOpticalRadial.timelikeTimeSpectrum ρ S).real (Icc s₁ s₂) ≤
      canonicalDensity (P diamond) (S • (NextOpticalRadial.spatialAxis : ChargeSpatialMomentum))) := by
  intro h
  let p := fun S : ℝ => S • (NextOpticalRadial.spatialAxis : ChargeSpatialMomentum)
  have hp : Tendsto (fun S => ‖p S‖) atTop atTop := by
    apply tendsto_id.congr'
    filter_upwards [eventually_ge_atTop (0:ℝ)] with S hS
    simp only [p,norm_smul,NextOpticalRadial.spatialAxis.property,mul_one,Real.norm_of_nonneg hS,id_eq]
  let C := spatialMeasureFactor * ∫ k, chargeInclusiveSquare (P diamond k-P₀)
  have hlim := canonicalDensity_variable_rank_limit diamond P P₀ h₀ h₀₀ hm ha hi hL p hp
  have hUp : ∀ᶠ S in atTop, canonicalDensity (P diamond) (p S) < C+1 :=
    hlim.eventually (Iio_mem_nhds (lt_add_one C))
  let c := ρ.real (Icc s₁ s₂)/4
  have hc : 0 < c := div_pos (ENNReal.toReal_pos hPos hFin) (by norm_num)
  obtain ⟨S,hU,hS₀,hR,hC⟩ := (hUp.and ((eventually_gt_atTop S₀).and
    ((eventually_gt_atTop (Real.sqrt s₂)).and (eventually_gt_atTop ((C+1)/c))))).exists
  have hS := (Real.sqrt_nonneg s₂).trans_lt hR
  have hS₂ : s₂ ≤ S^2 := by
    rw [← Real.sq_sqrt (h₁.le.trans h₁₂)]
    exact (sq_le_sq₀ (Real.sqrt_nonneg _) hS.le).mpr hR.le
  have hLow := NextOpticalRadial.compactTimelikeDensity_linear_lower ρ h₁ h₁₂ hS hS₂ hFin
  rw [← NextOpticalRadial.timelikeTimeSpectrum_real_band ρ h₁ hS hFin] at hLow
  have hLarge : C+1 < S*c := (div_lt_iff₀ hc).mp hC
  exact (not_lt_of_ge (hLow.trans (h S hS₀ hS))) (hU.trans hLarge)

end UV.ContinuationBoostSpectrum
