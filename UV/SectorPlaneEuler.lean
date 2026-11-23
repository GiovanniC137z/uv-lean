import UV.AdvanceStableCartesian
import UV.ContinueStableMassivePV

/-! Integration by parts for dilations of the four intrinsic momentum
coordinates. The Euler derivative is basis independent. -/

noncomputable section

namespace UV.SectorPlane

open MeasureTheory Set
open scoped Topology

def momentumEuler (f : MassiveMomentum → ℂ) (q : MassiveMomentum) : ℂ :=
  fderiv ℝ f q q

theorem momentum_euler_compact {f : MassiveMomentum → ℂ} (hs : HasCompactSupport f) :
    HasCompactSupport (momentumEuler f) := by
  apply HasCompactSupport.intro (hs.fderiv ℝ)
  intro q hq
  simp [momentumEuler,image_eq_zero_of_notMem_tsupport hq]

theorem momentum_euler_continuous {f : MassiveMomentum → ℂ} (hf : ContDiff ℝ 1 f) :
    Continuous (momentumEuler f) :=
  (hf.continuous_fderiv_apply le_rfl).comp (continuous_id.prodMk continuous_id)

theorem momentum_euler_c1 {f : MassiveMomentum → ℂ} (hf : ContDiff ℝ 2 f) :
    ContDiff ℝ 1 (momentumEuler f) :=
  (hf.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).clm_apply contDiff_id

/-- The four-dimensional divergence of the radial vector field is four.
The proof integrates each component against its dual coordinate. -/
theorem integral_momentum_euler {f : MassiveMomentum → ℂ} (hf : ContDiff ℝ 1 f) (hs : HasCompactSupport f) :
    ∫ q, momentumEuler f q = -4 * ∫ q, f q := by
  classical
  let b := Module.finBasis ℝ MassiveMomentum
  let x (i : Fin (Module.finrank ℝ MassiveMomentum)) : MassiveMomentum →L[ℝ] ℂ :=
    Complex.ofRealCLM.comp ((b.coord i).toContinuousLinearMap)
  let g (i : Fin (Module.finrank ℝ MassiveMomentum)) (q : MassiveMomentum) :=
    x i q * fderiv ℝ f q (b i)
  have hcoord (i) (q) : x i q = (b.repr q i : ℂ) := rfl
  have hd (i) : Continuous (fun q => fderiv ℝ f q (b i)) :=
    (hf.continuous_fderiv_apply le_rfl).comp (continuous_id.prodMk continuous_const)
  have hi (i) : Integrable (g i) := ((x i).continuous.mul (hd i)).integrable_of_hasCompactSupport
    (hs.fderiv_apply ℝ (b i)).mul_left
  haveI : (volume : Measure MassiveMomentum).IsAddHaarMeasure := by
    change ((volume : Measure ℝ).prod (volume : Measure Spatial)).IsAddHaarMeasure
    infer_instance
  have hpart (i) : ∫ q, g i q = -(∫ q, f q) := by
    have he (q : MassiveMomentum) : fderiv ℝ (x i) q (b i) = 1 := by
      rw [ContinuousLinearMap.fderiv,hcoord,b.repr_self]; simp
    have hI : Integrable (fun q => fderiv ℝ (x i) q (b i) * f q) := by
      simp only [he,one_mul]; exact hf.continuous.integrable_of_hasCompactSupport hs
    have H := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume) hI (hi i)
      (((x i).continuous.mul hf.continuous).integrable_of_hasCompactSupport hs.mul_left)
      (x i).differentiable (hf.differentiable le_rfl)
    simpa only [g,he,one_mul] using H
  have he (q : MassiveMomentum) : (∑ i, g i q) = momentumEuler f q := by
    calc
      _ = fderiv ℝ f q (∑ i, b.repr q i • b i) := by
        rw [map_sum]; apply Finset.sum_congr rfl
        intro i _
        simp only [g,hcoord,map_smul,Complex.real_smul]
      _ = _ := by rw [b.sum_repr]; rfl
  simp_rw [← he,integral_finset_sum _ (fun i _ => hi i),hpart]
  simp [MassiveMomentum,Spatial,Module.finrank_prod]

end UV.SectorPlane
