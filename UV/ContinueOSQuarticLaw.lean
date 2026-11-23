import UV.ContinueOSPointSource
import UV.ContinueOSQuarticMoments

/-! Exact boundary weak-coupling tests for a jointly measurable fixed-depth
Gaussian realization of the four physical probes and the point field. -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology SchwartzMap FourierTransform

namespace UV

inductive OSBoundaryTest where
  | localProbe | reflectedLocal | bump | reflectedBump
  deriving DecidableEq

abbrev OSQuarticSlot := OSBoundaryTest ⊕ OSFourSpace

def osBoundaryTestProbe (m : ℝ) : OSBoundaryTest → OSProbe
  | .localProbe => osMassiveLocal m osBumpProbe
  | .reflectedLocal => osReflectProbe (osMassiveLocal m osBumpProbe)
  | .bump => osBumpProbe
  | .reflectedBump => osReflectProbe osBumpProbe

/-- The specified ordinary massive covariance, with a factor of the depth
transfer at each point insertion. The real boundary tests use the four
Schwartz smearings above. -/
def osQuarticCovariance (m r : ℝ) : OSQuarticSlot → OSQuarticSlot → ℝ
  | .inl i, .inl j => (osReflectedBlock m 0 (osReflectProbe (osBoundaryTestProbe m i))
      (osBoundaryTestProbe m j)).re
  | .inl i, .inr x => (osPointSource m r (osBoundaryTestProbe m i) x).re
  | .inr x, .inl i => (osPointSource m r (osBoundaryTestProbe m i) x).re
  | .inr x, .inr y => stableCoordinateCovariance (2*r) m (x-y)

@[simp] theorem osReflectProbe_twice (f : OSProbe) : osReflectProbe (osReflectProbe f) = f := by
  ext x
  simp only [osReflectProbe_apply, osTimeReflect_involutive x]

theorem osQuarticCovariance_raw_null {m : ℝ} (hm : 0 < m) (r : ℝ) :
    osQuarticCovariance m r (.inl .reflectedLocal) (.inl .localProbe) = 0 := by
  simp only [osQuarticCovariance, osBoundaryTestProbe, osReflectProbe_twice,
    osReflectedBlock_null hm, Complex.zero_re]

theorem osQuarticCovariance_cross_null {m : ℝ} (hm : 0 < m) (r : ℝ) :
    osQuarticCovariance m r (.inl .reflectedLocal) (.inl .bump) = 0 := by
  simp only [osQuarticCovariance, osBoundaryTestProbe, osReflectProbe_twice,
    osReflectedBlock_local_zero hm _ osBumpProbe_support, Complex.zero_re]

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- All stochastic assumptions refer to the actual covariance on these
slots. Spatial Fubini, strictness of the slope and normalization at weak
coupling are consequences. -/
theorem osRawQuartic_realization {m r : ℝ} (hm : 0 < m) (hr : 0 < r)
    {ζ : OSFourSpace → ℝ} (hc : Continuous ζ) (hk : HasCompactSupport ζ)
    (hn : 0 ≤ ζ) (hz : ∃ x, 0 < ζ x)
    (F : OSQuarticSlot → Ω → ℝ) (hW : OSWickMoments μ F (osQuarticCovariance m r))
    (hZ : Measurable (fun p : OSFourSpace × Ω => F (.inr p.1) p.2)) :
    let A := fun ω => F (.inl .reflectedLocal) ω * F (.inl .localProbe) ω
    let V := osSpatialPotential volume (fun x ω => ζ x * F (.inr x) ω ^ 4 / 24)
    HasDerivWithinAt (osGibbsExpectation μ V A) (osRawQuarticSlope m r ζ) (Ioi 0) 0 ∧
      ∀ᶠ g : ℝ in 𝓝[Ioi 0] 0, osGibbsExpectation μ V A g < 0 := by
  let a : OSQuarticSlot := .inl .reflectedLocal
  let b : OSQuarticSlot := .inl .localProbe
  let K := osQuarticCovariance m r
  let A := fun ω => F a ω * F b ω
  let D := fun x ω => ζ x * F (.inr x) ω^4 / 24
  let S := fun x => (osCoincidence m r / 2) *
    (ζ x * (osPoissonTransfer r osReflectedBump x * osPoissonTransfer r osPositiveBump x))
  have hζ : Integrable ζ := hc.integrable_of_hasCompactSupport hk
  have hv (x : OSFourSpace) : K (.inr x) (.inr x) = osCoincidence m r := by
    simp [K, osQuarticCovariance, osCoincidence]
  have hD : Integrable (Function.uncurry D) (volume.prod μ) := by
    have h := osQuartic_product_integrable (A := fun _ : Ω => 1) (Z := fun x ω => F (.inr x) ω)
      (C := 105 * osCoincidence m r ^ 4) hZ aestronglyMeasurable_const
      (by simp) hζ
      (fun x => (osWick_eighth_point hW _).1) (fun x => by
        rw [(osWick_eighth_point hW _).2, show osQuarticCovariance m r (.inr x) (.inr x) = _ from hv x])
    simpa only [one_mul] using h
  have hA : Integrable A μ := (hW.integrable [a,b]).congr
    (Eventually.of_forall fun ω => by simp [osMonomial, A])
  have hDA := osWick_raw_product_integrable hW a b Sum.inr hζ hZ hv
  have hnull : K a b = 0 := osQuarticCovariance_raw_null hm r
  have hnullA : (∫ ω, A ω ∂μ) = 0 := by
    have h := hW.moment 1 [a,b] (by simp)
    simpa [A, osMonomial, osWickMoment, List.zipIdx, List.eraseIdx, K, hnull] using h
  have hiS : (∫ x, S x) = -(osRawQuarticSlope m r ζ) := by
    simp only [S, integral_const_mul, osRawQuarticSlope, neg_mul, neg_neg]
  have hS (x : OSFourSpace) : (∫ ω, A ω * D x ω ∂μ) = S x := by
    obtain ⟨hb,ha,_,_⟩ := osPointSource_four_pairings hm hr x
    calc
      _ = ζ x * ∫ ω, F a ω * F b ω * F (.inr x) ω^4 / 24 ∂μ := by
        rw [← integral_const_mul]
        congr 1
        funext ω
        dsimp [A,D]
        ring
      _ = _ := by
        rw [osWickRawQuartic_pair_mean hW a b _ hnull]
        change ζ x * (K (.inr x) (.inr x) * ((osPointSource m r
          (osReflectProbe (osMassiveLocal m osBumpProbe)) x).re *
          (osPointSource m r (osMassiveLocal m osBumpProbe) x).re) / 2) = _
        rw [hv, ha, hb]
        dsimp [S]
        ring
  have hpos : 0 < ∫ x, S x := hiS ▸ neg_pos.mpr (osRawQuarticSlope_neg hm hr hc hk hn hz)
  have h := osSpatialPotential_negative_reflection (D := D) (A := A) (L := 0) hD hA hDA
    (Eventually.of_forall fun ω => by
      apply le_trans (by norm_num : -(0 : ℝ) ≤ 0)
      exact integral_nonneg fun x => div_nonneg (mul_nonneg (hn x) (by positivity)) (by norm_num))
    le_rfl hnullA (Eventually.of_forall hS) hpos
  simpa only [hiS, neg_neg] using h

end UV
