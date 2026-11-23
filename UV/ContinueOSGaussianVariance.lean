import UV.ContinueOSGaussianProcess
import Mathlib.Probability.Distributions.Gaussian.Real

/-! Probability law and second moment of actual field increments. -/

noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped Matrix NNReal ENNReal

namespace UV

theorem osQuarticFiniteLaw_scalar {ι : Type*} [Fintype ι] [DecidableEq ι]
    {m r : ℝ} (hm : 0 < m) (hr : 0 < r) (s : ι → OSQuarticSlot) (v : ι → ℝ) :
    let D : Matrix ι ι ℝ := fun i j => osQuarticCovariance m r (s i) (s j)
    ∃ w : ℝ≥0, (w : ℝ) = v ⬝ᵥ (D *ᵥ v) ∧
      (osQuarticFiniteLaw hm hr s).map (fun x => v ⬝ᵥ x) = gaussianReal 0 w := by
  intro D
  have h0 := (osQuarticCovariance_posSemidef hm hr s).2 v
  have hw : 0 ≤ v ⬝ᵥ (D *ᵥ v) := by simpa only [star_trivial] using h0
  let w : ℝ≥0 := ⟨_,hw⟩
  refine ⟨w,rfl,Measure.ext_of_charFun ?_⟩
  funext t
  rw [charFun_gaussianReal,charFun_apply_real,integral_map (by fun_prop : AEMeasurable (fun x : ι → ℝ => v ⬝ᵥ x)
    (osQuarticFiniteLaw hm hr s)) (by fun_prop)]
  have he (x : ι → ℝ) : ((t • v) ⬝ᵥ x : ℝ) = t * (v ⬝ᵥ x) := smul_dotProduct t v x
  change (∫ x, Complex.exp ((t : ℂ) * (v ⬝ᵥ x : ℝ) * Complex.I) ∂osQuarticFiniteLaw hm hr s) = _
  rw [show (∫ x, Complex.exp ((t : ℂ) * (v ⬝ᵥ x : ℝ) * Complex.I) ∂osQuarticFiniteLaw hm hr s) =
      MarkedPhoton.photonCharacteristic (osQuarticFiniteLaw hm hr s) (t • v) by
    unfold MarkedPhoton.photonCharacteristic
    simp only [he,Complex.ofReal_mul], osQuarticFiniteLaw_characteristic]
  congr 1
  change -(((t • v) ⬝ᵥ (D *ᵥ (t • v)) : ℝ) : ℂ)/2 = _
  rw [D.mulVec_smul,smul_dotProduct,dotProduct_smul]
  simp only [w, NNReal.coe_mk, Complex.ofReal_zero, smul_eq_mul, Complex.ofReal_mul]
  ring

theorem osQuarticProcess_difference {m r : ℝ} (hm : 0 < m) (hr : 0 < r)
    (μ : Measure (OSQuarticSlot → ℝ)) (hμ : IsProjectiveLimit (α := fun _ => ℝ) μ (osGaussianFamily hm hr))
    (a b : OSQuarticSlot) :
    Integrable (fun z => (z a-z b)^2) μ ∧
      (∫ z, (z a-z b)^2 ∂μ) = osQuarticCovariance m r a a - osQuarticCovariance m r a b -
        osQuarticCovariance m r b a + osQuarticCovariance m r b b := by
  let s : Fin 2 → OSQuarticSlot := ![a,b]
  let v : Fin 2 → ℝ := ![1,-1]
  obtain ⟨w,hw,hlaw⟩ := osQuarticFiniteLaw_scalar hm hr s v
  have hproj := osQuarticGaussianProcess_projection hm hr μ hμ s
  have hcoord : Measurable (fun (z : OSQuarticSlot → ℝ) => z ∘ s) := measurable_pi_lambda _ (fun i => measurable_pi_apply _)
  have hdiff : μ.map (fun z => z a - z b) = gaussianReal 0 w := by
    rw [←hlaw,←hproj,Measure.map_map (by fun_prop : Measurable (fun x : Fin 2 → ℝ => v ⬝ᵥ x)) hcoord]
    congr 1
    ext z
    simp [s,v,dotProduct,Fin.sum_univ_two,Function.comp_def,sub_eq_add_neg]
  have hmeas : Measurable (fun z : OSQuarticSlot → ℝ => z a - z b) := (measurable_pi_apply _).sub (measurable_pi_apply _)
  have hI : Integrable (fun x : ℝ => x^2) (gaussianReal 0 w) := by
    simpa only [id_eq] using (memLp_id_gaussianReal (μ := 0) (v := w) 2).integrable_sq
  have hV := variance_fun_id_gaussianReal (μ := 0) (v := w)
  rw [variance_eq_integral measurable_id'.aemeasurable] at hV
  simp only [integral_id_gaussianReal,sub_zero] at hV
  rw [←hdiff] at hI hV
  refine ⟨hI.comp_aemeasurable hmeas.aemeasurable,?_⟩
  rw [integral_map hmeas.aemeasurable (by fun_prop)] at hV
  rw [hV,hw]
  simp [s,v,dotProduct,mulVec,Fin.sum_univ_two]
  ring

end UV
