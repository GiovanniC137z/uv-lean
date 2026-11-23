import UV.ContinueOSGaussianProcess
import Mathlib.Analysis.InnerProductSpace.GramMatrix

/-! The entire massive boundary covariance-form domain, in its Fourier
representation. The vector in L² is the Fourier smearing multiplied by
the positive square root of 1/(m²+4π²|k|²). All transferred point
observables and the four physical boundary probes use this same map. -/

noncomputable section
open MeasureTheory Matrix
open scoped InnerProductSpace ComplexConjugate Topology FourierTransform SchwartzMap

namespace UV

abbrev OSMassiveFormSpace := Lp ℂ 2 (volume : Measure OSFourSpace)

def osMassiveFormMultiplier (m : ℝ) (f : OSFourSpace → ℂ) (k : OSFourSpace) : ℂ :=
  (Real.sqrt (osCovWeight m 0 k) : ℂ) * f k

/-- A Fourier smearing belongs to the free covariance-form domain iff
its weighted square norm is integrable. -/
theorem osMassiveForm_mem_iff {m : ℝ} (hm : 0 < m) {f : OSFourSpace → ℂ} (hf : AEStronglyMeasurable f) :
    MemLp (osMassiveFormMultiplier m f) 2 volume ↔ Integrable (fun k => osCovWeight m 0 k * ‖f k‖^2) := by
  have hc : Continuous (fun k => (Real.sqrt (osCovWeight m 0 k) : ℂ)) := by
    unfold osCovWeight osTransferSymbol osMassiveSymbol
    fun_prop (disch := intro k; positivity)
  have hme : AEStronglyMeasurable (osMassiveFormMultiplier m f) := hc.aestronglyMeasurable.mul hf
  rw [memLp_two_iff_integrable_sq_norm hme]
  simp only [osMassiveFormMultiplier,norm_mul,Complex.norm_real,Real.norm_of_nonneg (Real.sqrt_nonneg _),
    mul_pow,Real.sq_sqrt (osCovWeight_bound hm le_rfl _).1]

/-- The L² vector for any Fourier smearing with finite free covariance. -/
def osMassiveFormVector {m : ℝ} (hm : 0 < m) (f : OSFourSpace → ℂ) (hf : AEStronglyMeasurable f)
    (hi : Integrable (fun k => osCovWeight m 0 k * ‖f k‖^2)) : OSMassiveFormSpace :=
  ((osMassiveForm_mem_iff hm hf).mpr hi).toLp _

private theorem osQuarticFeatureContinuous (m r : ℝ) (i : OSQuarticSlot) : Continuous (osQuarticFourierFeature m r i) := by
  cases i with
  | inl i => exact (SchwartzMap.fourierTransformCLM ℂ (osBoundaryTestProbe m i)).continuous
  | inr x =>
    change Continuous (fun k : OSFourSpace => (osTransferSymbol r k : ℂ) * conj (osPointWave x k))
    have hp : Continuous (osTransferSymbol r) := by unfold osTransferSymbol; fun_prop
    exact (Complex.continuous_ofReal.comp hp).mul (Complex.continuous_conj.comp (osPointWave_continuous x))

theorem osQuarticFourierFeature_mem {m r : ℝ} (hm : 0 < m) (hr : 0 < r) (i : OSQuarticSlot) :
    MemLp (osMassiveFormMultiplier m (osQuarticFourierFeature m r i)) 2 volume := by
  apply (osMassiveForm_mem_iff hm (osQuarticFeatureContinuous m r i).aestronglyMeasurable).mpr
  apply (osQuarticGramEntry_integrable hm hr i i).re.congr
  filter_upwards with k
  let z := osQuarticFourierFeature m r i k
  let c := osCovWeight m 0 k
  change (conj z * (c:ℂ) * z).re = c * ‖z‖^2
  rw [Complex.sq_norm,Complex.normSq_apply]
  simp [Complex.mul_re,Complex.mul_im]
  ring

def osQuarticFormSlot {m r : ℝ} (hm : 0 < m) (hr : 0 < r) (i : OSQuarticSlot) : OSMassiveFormSpace :=
  (osQuarticFourierFeature_mem hm hr i).toLp _

/-- The four probe types and continuum point slots have exactly their
manuscript covariance in the real Hilbert form on massive Fourier tests. -/
theorem osQuarticFormSlot_inner {m r : ℝ} (hm : 0 < m) (hr : 0 < r) (i j : OSQuarticSlot) :
    ⟪osQuarticFormSlot hm hr i,osQuarticFormSlot hm hr j⟫_ℝ = osQuarticCovariance m r i j := by
  rw [L2.inner_def,osQuarticCovariance_gram hm hr]
  refine Eq.trans ?_ (integral_re (osQuarticGramEntry_integrable hm hr i j))
  apply integral_congr_ae
  filter_upwards [(osQuarticFourierFeature_mem hm hr i).coeFn_toLp,
    (osQuarticFourierFeature_mem hm hr j).coeFn_toLp] with k hi hj
  change ⟪((osQuarticFourierFeature_mem hm hr i).toLp _) k,((osQuarticFourierFeature_mem hm hr j).toLp _) k⟫_ℝ = _
  rw [hi,hj]
  let z := osQuarticFourierFeature m r i k
  let w := osQuarticFourierFeature m r j k
  let c := osCovWeight m 0 k
  have hc : 0 ≤ c := (osCovWeight_bound hm le_rfl _).1
  change ⟪((Real.sqrt c : ℂ)*z),((Real.sqrt c : ℂ)*w)⟫_ℝ = (conj z*(c:ℂ)*w).re
  rw [real_inner_eq_re_inner ℂ,RCLike.inner_apply']
  simp only [map_mul,Complex.conj_ofReal]
  have hs : (Real.sqrt c : ℂ)*(Real.sqrt c : ℂ) = (c:ℂ) := by exact_mod_cast Real.mul_self_sqrt hc
  change (((Real.sqrt c : ℂ)*conj z)*((Real.sqrt c : ℂ)*w)).re = (conj z*(c:ℂ)*w).re
  apply congrArg Complex.re
  calc
    _ = ((Real.sqrt c : ℂ)*(Real.sqrt c : ℂ))*conj z*w := by ring
    _ = _ := by rw [hs]; ring

def osMassiveHilbertCovariance : OSPositiveCovariance OSMassiveFormSpace where
  entry f g := ⟪f,g⟫_ℝ
  pos s := Matrix.posSemidef_gram ℝ s

end UV
