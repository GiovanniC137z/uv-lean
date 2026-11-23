import UV.ContinueOSJointWitness

/-! Transport of the entire reflected quadratic form between oriented
sector charts, and its relation to the ordinary positive joint covariance. -/

noncomputable section

open MeasureTheory Set
open scoped SchwartzMap FourierTransform ComplexConjugate Topology

namespace UV

/-- The ordinary two-source covariance density, with a single underlying
field and a real Poisson transfer in the second slot. -/
def osJointDensity (m r : ℝ) (k : OSFourSpace) (z w : ℂ) : ℝ :=
  Complex.normSq (z + (osTransferSymbol r k : ℂ) * w) / osMassiveSymbol m k

theorem osJointDensity_blocks {m : ℝ} (hm : 0 < m) (r : ℝ)
    (k : OSFourSpace) (z w : ℂ) :
    osJointDensity m r k z w =
      osCovWeight m 0 k * Complex.normSq z + 2 * osCovWeight m r k * (conj z * w).re +
        osCovWeight m (r + r) k * Complex.normSq w := by
  have hS := (osMassiveSymbol_pos hm k).ne'
  simp only [osJointDensity, osCovWeight, osTransferSymbol_zero, osTransferSymbol_add,
    Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im]
  field_simp
  ring

theorem osJointDensity_nonneg {m : ℝ} (hm : 0 < m) (r : ℝ)
    (k : OSFourSpace) (z w : ℂ) : 0 ≤ osJointDensity m r k z w :=
  div_nonneg (Complex.normSq_nonneg _) (osMassiveSymbol_pos hm _).le

theorem osOrdinaryBlock_integrable {m a : ℝ} (hm : 0 < m) (ha : 0 ≤ a) (f g : OSProbe) :
    Integrable (fun k => conj (𝓕 f k) * (osCovWeight m a k : ℂ) * 𝓕 g k) := by
  have h := osReflectedBlock_integrable hm ha (osReflectProbe f) g
  simpa only [osReflectProbe_fourier, osTimeReflect_involutive _] using h

theorem osJointDensity_integrable {m r : ℝ} (hm : 0 < m) (hr : 0 ≤ r) (f g : OSProbe) :
    Integrable (fun k => osJointDensity m r k (𝓕 f k) (𝓕 g k)) := by
  have h0 := (osOrdinaryBlock_integrable hm (le_rfl : (0 : ℝ) ≤ 0) f f).re
  have h1 := ((osOrdinaryBlock_integrable hm hr f g).re).const_mul 2
  have h2 := (osOrdinaryBlock_integrable hm (add_nonneg hr hr) g g).re
  apply ((h0.add h1).add h2).congr
  filter_upwards with k
  change (conj (𝓕 f k) * (osCovWeight m 0 k : ℂ) * 𝓕 f k).re +
    2 * (conj (𝓕 f k) * (osCovWeight m r k : ℂ) * 𝓕 g k).re +
    (conj (𝓕 g k) * (osCovWeight m (r + r) k : ℂ) * 𝓕 g k).re = _
  rw [osJointDensity_blocks hm]
  simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.normSq_apply]
  ring

theorem osJointCovariance_positive {m : ℝ} (hm : 0 < m) (r : ℝ) (f g : OSProbe) :
    0 ≤ ∫ k, osJointDensity m r k (𝓕 f k) (𝓕 g k) :=
  integral_nonneg (fun _ => osJointDensity_nonneg hm _ _ _ _)

open SectorPlane

variable {E : Type*} [NormedAddCommGroup E]

def SectorPlane.Plane.osChartProbe (diamond : Plane E) (f : OSProbe) : OSProbe :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ diamond.osOrientedChart.toContinuousLinearEquiv f

theorem SectorPlane.Plane.osChartProbe_fourier (diamond : Plane E) (f : OSProbe) (k : OSFourSpace) :
    𝓕 (diamond.osChartProbe f) k = 𝓕 f (diamond.osOrientedChart k) :=
  Real.fourierIntegral_comp_linearIsometry diamond.osOrientedChart _ _

theorem SectorPlane.Plane.osReflectedBlock_chart (diamond : Plane E) (m a : ℝ) (f g : OSProbe) :
    osReflectedBlock m a (diamond.osChartProbe f) (diamond.osChartProbe g) =
      osReflectedBlock m a f g := by
  unfold osReflectedBlock
  calc
    _ = ∫ k, (fun x => conj (𝓕 f (osTimeReflect x)) * (osCovWeight m a x : ℂ) * 𝓕 g x)
        (diamond.osOrientedChart k) := by
      congr 1
      funext k
      simp [Plane.osChartProbe_fourier, Plane.osOrientedChart_commutes, osCovWeight,
        osTransferSymbol, osMassiveSymbol]
    _ = _ := diamond.osOrientedChart.measurePreserving.integral_comp
      diamond.osOrientedChart.toHomeomorph.measurableEmbedding
        (fun k => conj (𝓕 f (osTimeReflect k)) * (osCovWeight m a k : ℂ) * 𝓕 g k)

theorem SectorPlane.Plane.osJointReflectedQuadratic_chart (diamond : Plane E) (m r t : ℝ) (f g : OSProbe) :
    osJointReflectedQuadratic m r t (diamond.osChartProbe f) (diamond.osChartProbe g) =
      osJointReflectedQuadratic m r t f g := by
  simp only [osJointReflectedQuadratic, Plane.osReflectedBlock_chart]

variable [InnerProductSpace ℝ E]

theorem SectorPlane.Plane.osChartProbe_support (diamond : Plane E) (f : OSProbe)
    (hf : tsupport f ⊆ {x | 1 ≤ x 0}) :
    tsupport (diamond.osChartProbe f) ⊆ {x | 1 ≤ diamond.orientedGT (x 0)} := by
  have hc : Continuous (fun x : OSFourSpace => diamond.orientedGT (x 0)) :=
    continuous_const.mul (PiLp.continuous_apply 2 _ 0)
  apply closure_minimal _ (isClosed_le continuous_const hc)
  intro x hx
  have h1 : diamond.osOrientedChart x ∈ Function.support f := hx
  have h2 := hf (subset_closure h1)
  change 1 ≤ (diamond.osOrientedChart x) 0 at h2
  rwa [diamond.osOrientedChart_time] at h2

/-- A negative joint quadratic form exists for each locked copy with its
own assigned unit carrier and positive oriented-GT support. -/
theorem SectorPlane.Plane.os_joint_negative (diamond : Plane E) {m r : ℝ} (hm : 0 < m) (hr : 0 < r) :
    ∃ f g : OSProbe, tsupport f ⊆ {x | 1 ≤ diamond.orientedGT (x 0)} ∧
      tsupport g ⊆ {x | 1 ≤ diamond.orientedGT (x 0)} ∧
      HasCompactSupport f ∧ HasCompactSupport g ∧
      ∃ t : ℝ, osJointReflectedQuadratic m r t f g < 0 := by
  obtain ⟨f,g,hf,hg,hfc,hgc,t,ht⟩ := os_joint_massive_obstruction hm hr
  exact ⟨diamond.osChartProbe f, diamond.osChartProbe g, diamond.osChartProbe_support f hf,
    diamond.osChartProbe_support g hg, hfc.comp_homeomorph diamond.osOrientedChart.toHomeomorph,
    hgc.comp_homeomorph diamond.osOrientedChart.toHomeomorph, t,
    diamond.osJointReflectedQuadratic_chart m r t f g ▸ ht⟩

end UV
