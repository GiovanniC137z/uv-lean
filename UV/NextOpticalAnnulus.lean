import UV.NextOpticalTail

/-! An integrable radial mixing tail has sublinear mass on each bounded
boosted radial band. This is the exact final contradiction once the
restricted pair-space upper and covariant lower estimates share a band. -/

noncomputable section

open Filter Set MeasureTheory
open scoped Topology

namespace UV.NextOpticalRadial

/-- An absolutely integrable mixing budget makes the harmonic mass of
every traveling interval with a positive lower scaling vanish. -/
theorem mixingHarmonicBand_tendsto_zero (v : ℝ → ℝ) {R a b : ℝ} (ha : 0 < a)
    (hInt : IntegrableOn (fun r => (v r)^2/r) (Ioi R)) :
    Tendsto (fun S => ∫ r in Icc (a*S) (b*S), (v r)^2/r) atTop (𝓝 0) := by
  let f (r : ℝ) : ℝ := (v r)^2/r
  let g := (Ioi R).indicator f
  have hg : Integrable g := hInt.integrable_indicator measurableSet_Ioi
  have h := tendsto_integral_filter_of_dominated_convergence (l := atTop)
    (F := fun S r => (Icc (a*S) (b*S)).indicator g r)
    (f := fun _ => (0:ℝ)) (fun r => ‖g r‖)
    (Eventually.of_forall fun _ => (hg.indicator measurableSet_Icc).aestronglyMeasurable)
    (Eventually.of_forall fun S => Eventually.of_forall fun r => by
      by_cases hm : r ∈ Icc (a*S) (b*S) <;> simp [hm])
    hg.norm (Eventually.of_forall fun r => by
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_gt_atTop (r/a)] with S hS
      have hSr : r < a*S := by
        rw [mul_comm]
        exact (div_lt_iff₀ ha).mp hS
      exact (indicator_of_notMem (fun h => not_le_of_gt hSr h.1) _).symm)
  simp only [integral_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (R/a)] with S hS
  have hSR : R < a*S := by
    rw [mul_comm]
    exact (div_lt_iff₀ ha).mp hS
  rw [integral_indicator measurableSet_Icc]
  apply setIntegral_congr_fun measurableSet_Icc
  intro r hr
  exact indicator_of_mem (hSR.trans_le hr.1) f

/-- A compact timelike band with linear lower density and the radial
pair-space upper estimate is incompatible with the harmonic budget.
The band density and both comparison constants refer to the same plane. -/
theorem mixingBand_contradiction {E : Type*} [Norm E] (diamond : SectorPlane.Plane E)
    (v : SectorPlane.Plane E → ℝ → ℝ) (Dband : SectorPlane.Plane E → ℝ → ℝ)
    {R S₀ a b C c : ℝ} (ha : 0 < a) (hC : 0 < C) (hc : 0 < c)
    (hInt : IntegrableOn (fun r => (v diamond r)^2/r) (Ioi R))
    (hSq : ∀ S > S₀, IntegrableOn (fun r => (v diamond r)^2) (Icc (a*S) (b*S)))
    (hUpper : ∀ S > S₀, Dband diamond S ≤ C * ∫ r in Icc (a*S) (b*S), (v diamond r)^2)
    (hLower : ∀ S > S₀, c*S ≤ Dband diamond S) :
    False := by
  have hLimit := (mixingHarmonicBand_tendsto_zero (v diamond) (b := b) ha hInt).const_mul (C*b)
  simp only [mul_zero] at hLimit
  have hn : ∀ᶠ S in atTop, (C*b) * (∫ r in Icc (a*S) (b*S), (v diamond r)^2/r) < c :=
    hLimit.eventually_lt_const hc
  obtain ⟨S,hS,hS0,hSR,hSm⟩ : ∃ S : ℝ, 0 < S ∧ S₀ < S ∧ R/a < S ∧
      (C*b) * (∫ r in Icc (a*S) (b*S), (v diamond r)^2/r) < c := by
    exact (hn.and ((eventually_gt_atTop (0:ℝ)).and
      ((eventually_gt_atTop S₀).and (eventually_gt_atTop (R/a))))).exists.imp
      (fun S h => ⟨h.2.1,h.2.2.1,h.2.2.2,h.1⟩)
  let s := Icc (a*S) (b*S)
  have hs : s ⊆ Ioi R := by
    intro r hr
    have hrS : R < a*S := by
      rw [mul_comm]
      exact (div_lt_iff₀ ha).mp hSR
    exact hrS.trans_le hr.1
  have hi := hInt.mono_set hs
  have hz : (∫ r in s, (v diamond r)^2) ≤ (b*S)*(∫ r in s, (v diamond r)^2/r) := by
    rw [← integral_const_mul]
    refine setIntegral_mono_on (hSq S hS0) (hi.const_mul _) measurableSet_Icc fun r hr => ?_
    have hrs : 0 < r := (mul_pos ha hS).trans_le hr.1
    calc
      _ = r * ((v diamond r)^2/r) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hr.2 (div_nonneg (sq_nonneg _) hrs.le)
  have hbud : c*S ≤ S * ((C*b) * ∫ r in s, (v diamond r)^2/r) := by
    calc
      _ ≤ Dband diamond S := hLower S hS0
      _ ≤ C * ∫ r in s, (v diamond r)^2 := hUpper S hS0
      _ ≤ C * ((b*S)*(∫ r in s, (v diamond r)^2/r)) :=
        mul_le_mul_of_nonneg_left hz hC.le
      _ = _ := by ring
  have ht := mul_lt_mul_of_pos_left hSm hS
  linarith

/-- The exact Euclidean canonical coefficient is not integrable if the
same-plane band has both the radial upper estimate and a linear lower
bound. This uses the literal spinors at the tested spatial transfer. -/
theorem radialEuclideanDensity_not_integrable_of_band {E : Type*} [Norm E]
    (diamond : SectorPlane.Plane E) (u v : SectorPlane.Plane E → ℝ → ℝ)
    (Dband : SectorPlane.Plane E → ℝ → ℝ)
    (hu : Measurable (u diamond)) (hv : Measurable (v diamond))
    (hUnit : ∀ r, u diamond r ^ 2 + v diamond r ^ 2 = 1)
    {m ω R : ℝ} (hm : 0 ≤ m) (hR : 0 < R) (hRm : m ≤ R)
    (p : ChargeSpatialMomentum) (hp : p ≠ 0) (hRp : ‖p‖ ≤ R) (hRω : |ω| ≤ R)
    {S₀ a b C c : ℝ} (ha : 0 < a) (hC : 0 < C) (hc : 0 < c)
    (hUpper : ∀ S > S₀, Dband diamond S ≤ C * ∫ r in Icc (a*S) (b*S), (v diamond r)^2)
    (hLower : ∀ S > S₀, c*S ≤ Dband diamond S) :
    ¬ Integrable (radialEuclideanDensity (u diamond) (v diamond) m ω p) := by
  intro hD
  have hInt := radialEuclideanDensity_requires_mixing_tail diamond u v hu hv hUnit
    hm hR hRm p hp hRp hRω hD
  apply mixingBand_contradiction diamond v Dband ha hC hc hInt _ hUpper hLower
  intro S _
  exact (integrableOn_const (C := (1:ℝ)) (measure_Icc_lt_top.ne)).mono'
    (hv.pow_const 2).aestronglyMeasurable (Eventually.of_forall fun r => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      linarith [hUnit r, sq_nonneg (u diamond r)])

end UV.NextOpticalRadial
