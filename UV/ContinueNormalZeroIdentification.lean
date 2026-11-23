import UV.ContinueNormalConstrainedTransform

/-! Identify the zero-winding displacement trace with its unrestricted
continuous-frequency integral. The convolution is continuous at zero even
though each first-order cover propagator has a sign jump there. -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Filter Set UV.SectorPlane
open scoped Matrix.Norms.L2Operator Topology FourierTransform

namespace UV

local instance normalInverseMatrixMeasurable : MeasurableSpace DiracMatrix := borel _
local instance normalInverseMatrixBorel : BorelSpace DiracMatrix := ⟨rfl⟩

theorem normal_mark_continuous_off_zero (m : ℝ) (p : OSFourSpace) (u : UnitVector OSFourSpace) {d : ℝ} (hd : d ≠ 0) :
    ContinuousAt (normalCoverMark m p u) d := by
  have hs : ContinuousAt Real.sign d := by
    rcases lt_or_gt_of_ne hd with h | h
    · have e : Real.sign =ᶠ[𝓝 d] fun _ => (-1:ℝ) := (gt_mem_nhds h).mono fun _ h' => Real.sign_of_neg h'
      exact (continuousAt_congr e).mpr continuousAt_const
    · have e : Real.sign =ᶠ[𝓝 d] fun _ => (1:ℝ) := (lt_mem_nhds h).mono fun _ h' => Real.sign_of_pos h'
      exact (continuousAt_congr e).mpr continuousAt_const
  unfold normalCoverMark normalDiracCover
  fun_prop

theorem normal_constrained_slice_integrable {n : ℕ} {m : ℝ} (hm : 0 < m)
    (u : Fin (n+1) → UnitVector OSFourSpace) (p : Fin (n+1) → OSFourSpace) (D : ℝ) :
    Integrable (normalConstrainedWord m u p D) :=
  ((Integrable.fintype_prod (fun _ : Fin n => (normal_open_laplace_mass hm).1)).const_mul _).mono'
    ((normal_constrained_measurable m u p).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    (Eventually.of_forall fun x => normal_constrained_bound hm u p D x)

theorem normal_cover_convolution_continuous {n : ℕ} {m : ℝ} (hm : 0 < m)
    (u : Fin (n+1+1) → UnitVector OSFourSpace) (p : Fin (n+1+1) → OSFourSpace) :
    Continuous (normalCoverConvolution m u p) := by
  apply continuous_iff_continuousAt.mpr
  intro D
  let b := fun x : Fin (n+1) → ℝ => (2:ℝ)^(n+1+1)*∏ j, Real.exp (-(m/2)*|x j|)
  have hi : Integrable b := (Integrable.fintype_prod (fun _ : Fin (n+1) => (normal_open_laplace_mass hm).1)).const_mul _
  apply tendsto_integral_filter_of_dominated_convergence b
    (Eventually.of_forall fun S => (normal_constrained_slice_integrable hm u p S).aestronglyMeasurable) _ hi
  · filter_upwards [normal_sum_ne_ae n D] with x hx
    have h0 : D-∑ i, x i ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
    have hu : ContinuousAt (fun S : ℝ => S - ∑ i, x i) D := continuousAt_id.sub continuousAt_const
    have hc : ContinuousAt (fun S : ℝ => normalCoverMark m (p 0) (u 0) (S - ∑ i, x i)) D :=
      (normal_mark_continuous_off_zero m (p 0) (u 0) h0).tendsto.comp hu.tendsto
    let tail := normalOrderedWord (fun i => normalCoverMark m (p i.succ) (u i.succ) (x i))
    change Tendsto (fun S => normalConstrainedWord m u p S x) (𝓝 D) (𝓝 (normalConstrainedWord m u p D x))
    have he (S : ℝ) : normalConstrainedWord m u p S x = normalCoverMark m (p 0) (u 0) (S-∑ i, x i)*tail := by
      simp only [normalConstrainedWord,normalOrderedWord,List.ofFn_succ,List.prod_cons,normalOpenIncrements,Fin.cons_zero,Fin.cons_succ,tail]
    simp_rw [he]
    exact hc.tendsto.mul_const tail
  · refine Eventually.of_forall fun S => Eventually.of_forall fun x => (normal_constrained_bound hm u p S x).trans ?_
    have h : Real.exp (-(m/2)*|S|) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg hm.le (abs_nonneg S)])
    apply mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (by positivity) h) (Finset.prod_nonneg fun _ _ => (Real.exp_pos _).le)

theorem normal_convolution_trace_fourier {n : ℕ} {m : ℝ} (hm : 0 < m)
    (u : Fin (n+1+1) → UnitVector OSFourSpace) (p : Fin (n+1+1) → OSFourSpace) (η : ℝ) :
    𝓕 (fun D => (normalCoverConvolution m u p D).trace) η = normalFrequencyTrace m u p (2*Real.pi*η) := by
  let tr := (Matrix.traceLinearMap (Fin 4) ℂ ℂ).toContinuousLinearMap
  let G := normalCoverConvolution m u p
  let a := 2*Real.pi*η
  have hi : Integrable G := (normal_constrained_integrable hm u p).integral_prod_left
  have hc := normal_cover_convolution_continuous hm u p
  have hwa : Integrable (fun D => normalAngularPhase a D • G D) := hi.norm.mono'
    (((show Continuous (normalAngularPhase a) by unfold normalAngularPhase; fun_prop).smul hc).aestronglyMeasurable)
    (Eventually.of_forall fun D => by rw [norm_smul,normal_angular_phase_norm,one_mul])
  have hw (D : ℝ) : Complex.exp ((↑(-2*Real.pi*inner ℝ D η):ℂ)*Complex.I) = normalAngularPhase a D := by
    unfold normalAngularPhase
    dsimp only [a]
    simp only [RCLike.inner_apply, conj_trivial]
    push_cast
    congr 1; ring
  rw [Real.fourierIntegral_eq']
  simp_rw [hw]
  change (∫ D, normalAngularPhase a D • tr (G D)) = _
  simp_rw [←map_smul tr]
  rw [tr.integral_comp_comm hwa,normal_cover_convolution_transform hm u p a]
  rfl

/-- This representation identity holds at fixed carrier transfers already
for two insertions. Integrating the independent four-momentum absolutely
at zero winding uses the separate six-insertion estimate. -/
theorem normal_winding_zero_frequency_identity {n : ℕ} {m L : ℝ} (hm : 0 < m) (θ : ℝ)
    (u : Fin (n+1+1) → UnitVector OSFourSpace) (p : Fin (n+1+1) → OSFourSpace) :
    (∫ x, normalWindingTrace m L θ 0 u p x) = ∫ ξ, normalZeroTrace m L u p ξ := by
  let tr := (Matrix.traceLinearMap (Fin 4) ℂ ℂ).toContinuousLinearMap
  let g := fun D => tr (normalCoverConvolution m u p D)
  have hg : Integrable g := tr.integrable_comp (normal_constrained_integrable hm u p).integral_prod_left
  have hc : Continuous g := tr.continuous.comp (normal_cover_convolution_continuous hm u p)
  have ha : 0 < 2*Real.pi := by positivity
  have hhat : 𝓕 g = fun η : ℝ => normalFrequencyTrace m u p (2*Real.pi*η) := funext (normal_convolution_trace_fourier hm u p)
  have hi : Integrable (𝓕 g) := hhat ▸ (normal_frequency_trace_integrable hm (by omega) u p).comp_mul_left' ha.ne'
  have h := hg.fourier_inversion hi (hc.continuousAt (x := 0))
  rw [Real.fourierIntegralInv_eq',hhat] at h
  simp only [inner_zero_right,mul_zero,Complex.ofReal_zero,zero_mul,Complex.exp_zero,one_smul] at h
  rw [Measure.integral_comp_mul_left,abs_of_pos (inv_pos.mpr ha)] at h
  have hcoord (x) : normalWindingTrace m L θ 0 u p x = (L:ℂ)*tr (normalConstrainedWord m u p 0 x) := by
    simp only [normalWindingTrace,normalLoopPhase,Int.cast_zero,zero_mul,Complex.ofReal_zero,mul_zero,Complex.exp_zero,mul_one,
      tr,LinearMap.coe_toContinuousLinearMap',Matrix.traceLinearMap_apply,normalConstrainedWord,normalOrderedWord,normalCoverMark]
  simp_rw [hcoord]
  rw [integral_const_mul,tr.integral_comp_comm (normal_constrained_slice_integrable hm u p 0)]
  change (L:ℂ)*g 0 = ∫ ξ, ((L/(2*Real.pi):ℝ):ℂ)*normalFrequencyTrace m u p ξ
  rw [←h,integral_const_mul,Complex.real_smul]
  push_cast; ring

/-- The integrated compact zero-winding coefficient of the periodic word. -/
theorem normal_periodic_zero_frequency {n : ℕ} {m L : ℝ} (hm : 0 < m) (hL : 0 < L) (θ : ℝ)
    (u : Fin (n+1+1) → UnitVector OSFourSpace) (p : Fin (n+1+1) → OSFourSpace) :
    L^(n+1) • (∫ t in normalUnitCell (n+1), ∑' h : Fin (n+1) → ℤ,
      normalWindingTrace m L (-θ) 0 u p (fun j => L*(t j+(h j:ℝ)))) = ∫ ξ, normalZeroTrace m L u p ξ :=
  (normal_periodic_winding_integral hm hL θ 0 u p).trans (normal_winding_zero_frequency_identity hm (-θ) u p)

/-- The compact coefficient after its normal integration is absolutely
integrable in carrier momentum under the joint frequency estimate. This
works for both Euclidean volume and a full reciprocal-lattice measure. -/
theorem normal_periodic_zero_carrier_integrable {n : ℕ} {m L : ℝ} (hm : 0 < m) (hL : 0 < L) (θ : ℝ)
    (u : Fin (n+1+1) → UnitVector OSFourSpace) (s : Fin (n+1+1) → OSFourSpace) (σ : Measure OSFourSpace) [SFinite σ]
    (h : Integrable (fun x : NormalLoopFrequency => normalZeroTrace m L u (fun j => x.1+s j) x.2) (σ.prod volume)) :
    Integrable (fun k => L^(n+1) • (∫ t in normalUnitCell (n+1), ∑' h : Fin (n+1) → ℤ,
      normalWindingTrace m L (-θ) 0 u (fun j => k+s j) (fun j => L*(t j+(h j:ℝ))))) σ := by
  simpa only [normal_periodic_zero_frequency hm hL] using h.integral_prod_left

end UV
