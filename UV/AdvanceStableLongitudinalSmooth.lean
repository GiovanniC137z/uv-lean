import UV.AdvanceStableLongitudinal
import UV.AdvanceConeAngularSmooth

/-! Compact Cartesian C² tests supply the angular estimates for the
assembled longitudinal boundary, including tests that meet the tip. -/

noncomputable section

namespace UV.SectorPlane

open Filter Set UV.Carrier
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E]

theorem Plane.massless_stable_longitudinal_C2_limit (diamond : Plane E) (ε : Evolution)
    {a : ℝ} (ha : 0 ≤ a) (u v : ConeUnitDirection) {g : ℝ × Spatial → ℂ}
    (hg : ContDiff ℝ 2 g) (hs : HasCompactSupport g) :
    ∃ L : ℂ,
      Tendsto (fun h : Height => diamond.masslessStableLongitudinalPair ε h a u v g)
        ((𝓝[>] (0 : ℝ)).comap (fun h : Height => (h : ℝ))) (𝓝 L) ∧
      Tendsto (fun h : Height => directed (diamond.masslessStableLongitudinalPair ε h a u v g))
        ((𝓝[>] (0 : ℝ)).comap (fun h : Height => (h : ℝ))) (𝓝 (directed L)) := by
  let U := coneCovector (WithLp.ofLp u.val)
  let V := coneCovector (WithLp.ofLp v.val)
  have hTest : coneTensorTest u v g = fun q => (U q * V q) • g q := by
    funext q
    simp only [coneTensorTest, coneLinearTest, U, V, Complex.real_smul, Complex.ofReal_mul]
    ring
  have hf : ContDiff ℝ 2 (coneTensorTest u v g) := by
    rw [hTest]
    exact (U.contDiff.mul V.contDiff).smul hg
  have hfs := cone_tensor_test_compact u v hs
  obtain ⟨R, hR, hOff⟩ := cone_radial_cutoff_of_compact hfs
  obtain ⟨d, C₂, hC₂, hQuad⟩ := cone_smooth_quadratic_normal_jet hg U V R
  rw [← hTest] at hQuad
  obtain ⟨C₁, hC₁, hSimple⟩ := cone_smooth_single_normal_jet hf R
  let C := max C₁ C₂
  have hC : 0 ≤ C := hC₁.trans (le_max_left _ _)
  have hSin (r : ℝ) (hr : r ∈ Ioc (0 : ℝ) R) :
      ‖coneAngularAmplitude (coneTensorTest u v g) r 0‖ ≤ C ∧
      ∀ y ∈ Icc (-1 : ℝ) 1,
        ‖coneAngularAmplitude (coneTensorTest u v g) r y -
          coneAngularAmplitude (coneTensorTest u v g) r 0‖ ≤ C * |y| := by
    exact ⟨(hSimple r hr).1.trans (le_max_left _ _), fun y hy =>
      ((hSimple r hr).2 y hy).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))⟩
  have hDou (r : ℝ) (hr : r ∈ Ioc (0 : ℝ) R) :
      ‖coneQuadraticAngularAmplitude (coneTensorTest u v g) r 0‖ ≤ C ∧ ‖d r‖ ≤ C ∧
      ∀ y ∈ Icc (-1 : ℝ) 1, ‖coneQuadraticAngularAmplitude (coneTensorTest u v g) r y -
        coneQuadraticAngularAmplitude (coneTensorTest u v g) r 0 - (y : ℂ) * d r‖ ≤ C * |y| ^ 2 := by
    refine ⟨(hQuad r hr).1.trans (le_max_right _ _), (hQuad r hr).2.1.trans (le_max_right _ _), ?_⟩
    intro y hy
    exact ((hQuad r hr).2.2 y hy).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _))
  have hLim := diamond.massless_stable_longitudinal_limit ε ha hR hC u v
    (hg.of_le (by norm_num)) hs hOff d hSin hDou
  exact ⟨_, hLim, directed_shell_readout_continuous.continuousAt.tendsto.comp hLim⟩

end UV.SectorPlane
