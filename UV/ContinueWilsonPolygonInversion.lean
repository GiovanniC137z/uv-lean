import UV.ContinueWilsonHopInversion
import UV.ContinueWilsonJointTraces
import UV.ContinueWilsonMomentumWard

/-! Closing the carrier circulation by Fourier inversion. One arbitrarily
marked hop is inverted at minus the sum of the remaining displacements.
The other hops are integrated against the actual two-mark probability
measure. The identity holds entrywise for every spin contraction. -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Filter Set Real Metric
open scoped RealInnerProductSpace

namespace UV

structure WilsonSpinEntry where
  marks : WilsonDirections
  row : Fin 4
  col : Fin 4

def WilsonSpinEntry.amplitude (e : WilsonSpinEntry) (L : ℝ) (x : OSFourSpace) : ℂ :=
  wilsonDirectionWeight e.marks x * wilsonSpinWeight L x e.row e.col

theorem WilsonSpinEntry.amplitude_continuous (e : WilsonSpinEntry) (L : ℝ) : Continuous (e.amplitude L) := by
  apply (wilson_direction_weight_continuous e.marks).mul
  simp only [wilsonSpinWeight,diracSlash,Matrix.sub_apply,Matrix.smul_apply,Matrix.sum_apply,smul_eq_mul]
  fun_prop

variable {ι : Type*} [Fintype ι]

def WilsonSpinEntry.hop (e : WilsonSpinEntry) (L : ℝ) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι) :=
  wilsonMarkedSpinHop L T e.marks e.row e.col

def WilsonSpinEntry.density (e : WilsonSpinEntry) (L : ℝ) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι) :=
  wilsonMarkedEntryDensity L T e.marks e.row e.col

theorem WilsonSpinEntry.hop_measurable (e : WilsonSpinEntry) (L : ℝ) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι) :
    Measurable (e.hop L T) := by
  have hc : Continuous (fun t : OSFourSpace × OSFourSpace => thinPlaneWave t.1 t.2 * e.amplitude L t.2) := by
    apply Continuous.mul _ ((e.amplitude_continuous L).comp continuous_snd)
    unfold thinPlaneWave; fun_prop
  change Measurable (fun p => e.hop L T p)
  simpa only [hop,wilsonMarkedSpinHop,amplitude,mul_assoc] using
    (hc.stronglyMeasurable.integral_prod_right' (ν := wilsonDisplacementMeasure L T)).measurable

private theorem wilson_wave_add_position (p x y : OSFourSpace) :
    thinPlaneWave p (x+y) = thinPlaneWave p x * thinPlaneWave p y := by
  simp [thinPlaneWave,inner_add_right,mul_add,Complex.exp_add]

theorem wilson_shifted_hop_closure {L : ℝ} (hL : 0 < L) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι)
    (e : WilsonSpinEntry) (q S : OSFourSpace) :
    (((2*π)^4)⁻¹ : ℝ) • (∫ p, e.hop L T (p+q) * thinPlaneWave p S) =
      thinPlaneWave q (-S) * e.density L T (-S) := by
  have he (p : OSFourSpace) : e.hop L T (p+q) * thinPlaneWave p S =
      thinPlaneWave q (-S) * (thinPlaneWave (p+q) S * e.hop L T (p+q)) := by
    have h := wilson_wave_add q p S
    rw [←h]
    have hp : thinPlaneWave q (-S)*thinPlaneWave q S = 1 := by
      rw [←wilson_wave_add_position,neg_add_cancel]
      simp [thinPlaneWave]
    linear_combination -(thinPlaneWave p S * e.hop L T (p+q))*hp
  simp_rw [he]
  rw [integral_const_mul,(measurePreserving_add_right (volume : Measure OSFourSpace) q).integral_comp
    (Homeomorph.addRight q).measurableEmbedding (fun p => thinPlaneWave p S*e.hop L T p),←mul_smul_comm]
  have h := wilson_marked_hop_inversion hL T e.marks e.row e.col (-S)
  exact congrArg (thinPlaneWave q (-S) * ·) (by simpa only [neg_neg] using h)

variable {J : Type*} [Fintype J]

def wilsonTailEntryWeight (L : ℝ) (tail : J → WilsonSpinEntry) (q d : J → OSFourSpace) : ℂ :=
  ∏ j, thinPlaneWave (q j) (d j) * (tail j).amplitude L (d j)

theorem wilson_tail_weight_continuous (L : ℝ) (tail : J → WilsonSpinEntry) (q : J → OSFourSpace) :
    Continuous (wilsonTailEntryWeight L tail q) := by
  apply continuous_finset_prod
  intro j _
  apply Continuous.mul _ (((tail j).amplitude_continuous L).comp (continuous_apply j))
  unfold thinPlaneWave; fun_prop

theorem wilson_tail_weight_integrable {L : ℝ} (hL : 0 < L) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι)
    (tail : J → WilsonSpinEntry) (q : J → OSFourSpace) :
    Integrable (wilsonTailEntryWeight L tail q) (Measure.pi (fun _ => wilsonDisplacementMeasure L T)) := by
  unfold wilsonTailEntryWeight
  apply Integrable.fintype_prod (f := fun j x => thinPlaneWave (q j) x * (tail j).amplitude L x)
  intro j
  have hc : Continuous (fun x => thinPlaneWave (q j) x * (tail j).amplitude L x) := by
    apply Continuous.mul _ ((tail j).amplitude_continuous L)
    unfold thinPlaneWave; fun_prop
  have hmem : ∀ᵐ x ∂wilsonDisplacementMeasure L T, x ∈ closedBall 0 (2*L) := by
    simpa only [mem_closedBall,dist_zero_right] using wilson_displacement_band hL.le T
  have h := hc.continuousOn.integrableOn_compact (μ := wilsonDisplacementMeasure L T) (isCompact_closedBall 0 (2*L))
  rwa [IntegrableOn,Measure.restrict_eq_self_of_ae_mem hmem] at h

private theorem wilson_wave_sum (p : OSFourSpace) (d : J → OSFourSpace) :
    thinPlaneWave p (∑ j, d j) = ∏ j, thinPlaneWave p (d j) := by
  classical
  generalize (Finset.univ : Finset J) = s
  induction s using Finset.induction_on with
  | empty => simp [thinPlaneWave]
  | insert j s hj ih => simp only [Finset.sum_insert hj,Finset.prod_insert hj,wilson_wave_add_position,ih]

theorem wilson_tail_transform (L : ℝ) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι) (tail : J → WilsonSpinEntry)
    (q : J → OSFourSpace) (p : OSFourSpace) :
    (∏ j, (tail j).hop L T (p+q j)) =
      ∫ d, thinPlaneWave p (∑ j, d j) * wilsonTailEntryWeight L tail q d
        ∂Measure.pi (fun _ => wilsonDisplacementMeasure L T) := by
  simp only [wilson_wave_sum,wilsonTailEntryWeight,←Finset.prod_mul_distrib]
  rw [integral_fintype_prod_eq_prod (fun j x => thinPlaneWave p x * (thinPlaneWave (q j) x * (tail j).amplitude L x))]
  apply Finset.prod_congr rfl
  intro j _
  unfold WilsonSpinEntry.hop wilsonMarkedSpinHop
  congr 1
  funext x
  rw [←wilson_wave_add]
  unfold WilsonSpinEntry.amplitude
  ring

/-- Four-dimensional return formula for any nonempty word of marked spin
entries. The closing displacement is fixed by conservation. -/
theorem wilson_spin_entry_polygon_closure {L : ℝ} (hL : 0 < L) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι)
    (head : WilsonSpinEntry) (tail : J → WilsonSpinEntry) (b : OSFourSpace) (q : J → OSFourSpace) :
    (((2*π)^4)⁻¹ : ℝ) • (∫ p, head.hop L T (p+b) * ∏ j, (tail j).hop L T (p+q j)) =
      ∫ d, (thinPlaneWave b (-(∑ j, d j)) * head.density L T (-(∑ j, d j))) * wilsonTailEntryWeight L tail q d
        ∂Measure.pi (fun _ => wilsonDisplacementMeasure L T) := by
  let ν := Measure.pi (fun _ : J => wilsonDisplacementMeasure L T)
  let H := fun p => head.hop L T (p+b)
  let G := wilsonTailEntryWeight L tail q
  let W := fun (p : OSFourSpace) (d : J → OSFourSpace) => thinPlaneWave p (∑ j, d j)
  have hH : Integrable H := ((measurePreserving_add_right (volume : Measure OSFourSpace) b).integrable_comp_emb
    (Homeomorph.addRight b).measurableEmbedding).mpr (wilson_marked_spin_hop_integrable hL T _ _ _)
  have hG := wilson_tail_weight_integrable hL T tail q
  have hW : Continuous (Function.uncurry W) := by unfold W Function.uncurry thinPlaneWave; fun_prop
  have hm : Measurable (fun z : OSFourSpace × (J → OSFourSpace) => H z.1 * W z.1 z.2 * G z.2) :=
    (((head.hop_measurable L T).comp (measurable_fst.add measurable_const)).mul hW.measurable).mul
      ((wilson_tail_weight_continuous L tail q).measurable.comp measurable_snd)
  have hi : Integrable (fun z : OSFourSpace × (J → OSFourSpace) => H z.1 * W z.1 z.2 * G z.2) (volume.prod ν) := by
    apply (hH.norm.mul_prod hG.norm).mono' hm.aestronglyMeasurable (Eventually.of_forall fun z => ?_)
    simp only [W,norm_mul,wilson_wave_norm,mul_one,G,le_refl]
  simp_rw [wilson_tail_transform L T tail q,←integral_const_mul]
  change _ • (∫ p, ∫ d, H p*(W p d*G d) ∂ν) = _
  simp_rw [←mul_assoc]
  rw [integral_integral_swap hi,←integral_smul]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro d
  dsimp only
  rw [integral_mul_const,←smul_mul_assoc]
  exact congrArg (· * G d) (wilson_shifted_hop_closure hL T head b (∑ j, d j))

end UV
