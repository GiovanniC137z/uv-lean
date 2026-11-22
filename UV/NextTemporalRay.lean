import UV.FurtherTemporalAnalytic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Actual frequency-band lower estimate for a ray approaching one fixed
orthonormal energy chart. The contact sequence is only assumed bounded,
and subsequence compactness is used in its finite matrix space. -/

noncomputable section
open Complex Filter Matrix MeasureTheory Set
open scoped Topology Matrix Matrix.Norms.Elementwise

namespace UV

variable {d : ℕ} {Sector : Type*}

abbrev TemporalHermitian (d : ℕ) := {H : TemporalMatrix d // H.IsHermitian}

def furtherTemporalBand (b : Bool) (A B : TemporalHermitian d) (C Q : TemporalMatrix d) : ℝ :=
  ∫ u in Icc (1 : ℝ) 2, ‖furtherTemporalCoefficient A.1 B.1 C Q (furtherTemporalFrequency b u)‖

def furtherTemporalBandParam (b : Bool)
    (p : (TemporalHermitian d × TemporalHermitian d × TemporalMatrix d) × TemporalMatrix d) : ℝ :=
  furtherTemporalBand b p.1.1 p.1.2.1 p.2 p.1.2.2

/-- The band absolute integral varies continuously with both actual inverse
pencils, the contact, and the first derivative, all on the common domain. -/
theorem continuous_furtherTemporalBandParam (b : Bool) :
    Continuous (furtherTemporalBandParam (d := d) b) := by
  let T := (TemporalHermitian d × TemporalHermitian d × TemporalMatrix d) × TemporalMatrix d
  let Z := fun p : T × ℝ => furtherTemporalFrequency b (max p.2 1)
  have hz : Continuous Z := (furtherTemporalFrequency_continuous b).comp (continuous_snd.max continuous_const)
  have hP : Continuous (fun p : T × ℝ => p.1.1) := continuous_fst.comp continuous_fst
  have hA : Continuous (fun p : T × ℝ => p.1.1.1.1) :=
    continuous_subtype_val.comp (continuous_fst.comp hP)
  have hBQ : Continuous (fun p : T × ℝ => p.1.1.2) := continuous_snd.comp hP
  have hB : Continuous (fun p : T × ℝ => p.1.1.2.1.1) :=
    continuous_subtype_val.comp (continuous_fst.comp hBQ)
  have hC : Continuous (fun p : T × ℝ => p.1.2) := continuous_snd.comp continuous_fst
  have hQ : Continuous (fun p : T × ℝ => p.1.1.2.2) := continuous_snd.comp hBQ
  have hunit (p : T × ℝ) : (Z p).im ≠ 0 :=
    furtherTemporalFrequency_im_ne_zero b (zero_lt_one.trans_le (le_max_right _ _))
  have hR : Continuous (fun p : T × ℝ => furtherTemporalResolvent p.1.1.1.1 (Z p)) := by
    apply continuous_iff_continuousAt.mpr
    intro p
    apply (continuousAt_matrix_inv _ ?_).comp
      ((hz.smul continuous_const).add hA).continuousAt
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ (isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp
      (furtherTemporalPencil_isUnit_of_im_ne_zero p.1.1.1.2 (hunit p))))
  have hS : Continuous (fun p : T × ℝ => furtherTemporalResolvent p.1.1.2.1.1 (Z p)) := by
    apply continuous_iff_continuousAt.mpr
    intro p
    apply (continuousAt_matrix_inv _ ?_).comp
      ((hz.smul continuous_const).add hB).continuousAt
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ (isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp
      (furtherTemporalPencil_isUnit_of_im_ne_zero p.1.1.2.1.2 (hunit p))))
  have ht : Continuous (Matrix.trace : TemporalMatrix d → ℂ) :=
    continuous_finset_sum _ fun i _ => (continuous_apply i).comp (continuous_apply i)
  let f := fun (p : T) (u : ℝ) =>
    ‖furtherTemporalCoefficient p.1.1.1 p.1.2.1.1 p.2 p.1.2.2
      (furtherTemporalFrequency b (max u 1))‖
  have hf : Continuous f.uncurry :=
    ((ht.comp (hR.mul hC)).sub (ht.comp (((hR.mul hQ.matrix_conjTranspose).mul hS).mul hQ))).norm
  have hInt := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (μ := (volume : Measure ℝ)) hf 1 2
  have hEq : (fun p : T => ∫ u in (1 : ℝ)..2, f p u) = furtherTemporalBandParam b := by
    funext p
    rw [intervalIntegral.integral_of_le (by norm_num : (1 : ℝ) ≤ 2), ← integral_Icc_eq_integral_Ioc]
    apply setIntegral_congr_fun measurableSet_Icc
    intro u hu
    change 1 ≤ u ∧ u ≤ 2 at hu
    simp only [f, max_eq_left hu.1]
  rwa [hEq] at hInt

private theorem temporal_eventually_positive_of_compact_contacts
    {X Y : Type*} [TopologicalSpace X] [MetricSpace Y]
    (f : X × Y → ℝ) (hf : Continuous f) (hnonneg : ∀ p, 0 ≤ f p)
    (x : ℝ → X) (x₀ : X) (hx : Tendsto x atTop (𝓝 x₀))
    (y : ℝ → Y) (S : Set Y) (hS : IsCompact S)
    (hy : ∀ᶠ t in atTop, y t ∈ S)
    (hpos : ∀ c ∈ S, 0 < f (x₀, c)) :
    ∃ c > (0 : ℝ), ∀ᶠ t in atTop, c ≤ f (x t, y t) := by
  by_contra! hb
  have hseq (n : ℕ) : ∃ t : ℝ, (n : ℝ) ≤ t ∧ y t ∈ S ∧ f (x t, y t) < ((n : ℝ) + 1)⁻¹ := by
    have hfq : ∃ᶠ t in atTop, f (x t, y t) < ((n : ℝ) + 1)⁻¹ := by
      simp only [Filter.Frequently, not_lt]
      exact hb (((n : ℝ) + 1)⁻¹) (by positivity)
    obtain ⟨t, ht, hn, hs⟩ := (hfq.and_eventually ((eventually_ge_atTop (n : ℝ)).and hy)).exists
    exact ⟨t, hn, hs, ht⟩
  choose t ht hbound hsmall using hseq
  have htt : Tendsto t atTop atTop := tendsto_atTop_mono (fun n => ht n) tendsto_natCast_atTop_atTop
  obtain ⟨c, hc, φ, hφ, hlim⟩ := hS.tendsto_subseq hbound
  have hEsc := htt.comp hφ.tendsto_atTop
  have hpair : Tendsto (fun n => (x (t (φ n)), y (t (φ n)))) atTop (𝓝 (x₀, c)) :=
    (hx.comp hEsc).prodMk_nhds hlim
  have hfun : Tendsto (fun n => f (x (t (φ n)), y (t (φ n)))) atTop (𝓝 (f (x₀, c))) :=
    hf.continuousAt.tendsto.comp hpair
  have hinv : Tendsto (fun n : ℕ => (((n : ℝ) + 1)⁻¹)) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  have hzero : Tendsto (fun n => f (x (t (φ n)), y (t (φ n)))) atTop (𝓝 0) :=
    squeeze_zero (fun _ => hnonneg _) (fun n => (hsmall (φ n)).le) (hinv.comp hφ.tendsto_atTop)
  exact (hpos c hc).ne' (tendsto_nhds_unique hfun hzero)

private theorem furtherTemporalDiagonal_hermitian (ε : Fin d → ℝ) :
    (Matrix.diagonal fun i => (ε i : ℂ)).IsHermitian := by
  unfold Matrix.IsHermitian
  simp [Matrix.diagonal_conjTranspose]

/-- Each fixed contact has strictly positive limiting band weight. -/
theorem temporal_diagonal_band_positive (b : Bool)
    (ε : ChargePlane Sector → Fin d → ℝ) (plane : ChargePlane Sector)
    (C₀ : TemporalMatrix d) (Q₀ : ChargePlane Sector → TemporalMatrix d)
    (E : ℝ) (hcharge : temporalEnergyProjection (ε plane) E * Q₀ plane *
      temporalEnergyProjection (ε plane) E ≠ 0) :
    0 < furtherTemporalBand b
      ⟨diagonal (fun i => (ε plane i : ℂ)), furtherTemporalDiagonal_hermitian (ε plane)⟩
      ⟨diagonal (fun i => (ε plane i : ℂ)), furtherTemporalDiagonal_hermitian (ε plane)⟩
      C₀ (Q₀ plane) := by
  let H : TemporalHermitian d := ⟨diagonal (fun i => (ε plane i : ℂ)),
    furtherTemporalDiagonal_hermitian (ε plane)⟩
  change 0 < furtherTemporalBand b H H C₀ (Q₀ plane)
  have he : furtherTemporalBand b H H C₀ (Q₀ plane) =
      ∫ u in Icc (1 : ℝ) 2, ‖temporalContactCoefficient ε (fun _ => C₀) Q₀ plane
        (furtherTemporalFrequency b u)‖ := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro u hu
    change ‖furtherTemporalCoefficient (Matrix.diagonal fun i => (ε plane i : ℂ))
      (Matrix.diagonal fun i => (ε plane i : ℂ)) C₀ (Q₀ plane) (furtherTemporalFrequency b u)‖ =
      ‖temporalContactCoefficient ε (fun _ => C₀) Q₀ plane (furtherTemporalFrequency b u)‖
    rw [furtherTemporalCoefficient_eq_diagonal ε (fun _ => C₀) Q₀ plane]
    intro i hz
    apply furtherTemporalFrequency_im_ne_zero b (zero_lt_one.trans_le hu.1)
    simpa only [add_im, ofReal_im, add_zero, zero_im] using congrArg Complex.im hz
  rw [he]
  exact temporal_contact_positive_frequency_integral ε (fun _ => C₀) Q₀ plane b E hcharge

set_option maxHeartbeats 500000 in
/-- The rescaled ray estimate on one fixed orthonormal energy chart.
The momentum-dependent Hamiltonians need not be diagonal or commuting. -/
theorem temporal_contact_rescaled_ray_bound (b : Bool) (ε : ChargePlane Sector → Fin d → ℝ)
    (plane : ChargePlane Sector) (A B : ℝ → TemporalHermitian d) (C Q : ℝ → TemporalMatrix d)
    (hA : Tendsto (fun t => (A t).1) atTop (𝓝 (Matrix.diagonal fun i => (ε plane i : ℂ))))
    (hB : Tendsto (fun t => (B t).1) atTop (𝓝 (Matrix.diagonal fun i => (ε plane i : ℂ))))
    (Q₀ : ChargePlane Sector → TemporalMatrix d) (hQ : Tendsto Q atTop (𝓝 (Q₀ plane)))
    (hC : ∃ K : ℝ, ∀ᶠ t in (atTop : Filter ℝ), ‖C t‖ ≤ K)
    (E : ℝ) (hcharge : temporalEnergyProjection (ε plane) E * Q₀ plane *
      temporalEnergyProjection (ε plane) E ≠ 0) :
    ∃ c > (0 : ℝ), ∀ᶠ t in (atTop : Filter ℝ),
      c ≤ furtherTemporalBand b (A t) (B t) (C t) (Q t) := by
  let H : TemporalHermitian d := ⟨Matrix.diagonal fun i => (ε plane i : ℂ),
    furtherTemporalDiagonal_hermitian (ε plane)⟩
  have hpos (C₀ : TemporalMatrix d) : 0 < furtherTemporalBand b H H C₀ (Q₀ plane) :=
    temporal_diagonal_band_positive b ε plane C₀ Q₀ E hcharge
  let X := TemporalHermitian d × TemporalHermitian d × TemporalMatrix d
  let f := furtherTemporalBandParam (d := d) b
  let x : ℝ → X := fun t => (A t, B t, Q t)
  let x₀ : X := (H, H, Q₀ plane)
  have hCA : Tendsto A atTop (𝓝 H) := tendsto_subtype_rng.mpr hA
  have hCB : Tendsto B atTop (𝓝 H) := tendsto_subtype_rng.mpr hB
  have hx : Tendsto x atTop (𝓝 x₀) := hCA.prodMk_nhds (hCB.prodMk_nhds hQ)
  have hf : Continuous f := continuous_furtherTemporalBandParam (d := d) b
  obtain ⟨K, hK⟩ := hC
  have hClosed : ∀ᶠ t in atTop, C t ∈ Metric.closedBall (0 : TemporalMatrix d) K := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hK
  have hn : ∀ p, 0 ≤ f p := by
    intro p
    unfold f furtherTemporalBandParam furtherTemporalBand
    exact integral_nonneg fun _ => norm_nonneg _
  have hp : ∀ C₀ ∈ Metric.closedBall (0 : TemporalMatrix d) K, 0 < f (x₀, C₀) := by
    intro C₀ _
    change 0 < furtherTemporalBand b H H C₀ (Q₀ plane)
    exact hpos C₀
  have hres := temporal_eventually_positive_of_compact_contacts f hf hn x x₀ hx C _
    (isCompact_closedBall _ _) hClosed hp
  change ∃ c > (0 : ℝ), ∀ᶠ t in atTop, c ≤ furtherTemporalBand b (A t) (B t) (C t) (Q t) at hres
  exact hres

end UV
