import UV.ContinueWilsonSoftPhoton
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! One transverse Maxwell sewing between actual closed Wilson currents
and products on independent photon transfers, under the stated shell bound. -/

noncomputable section

open MeasureTheory Set Filter Finset
open scoped Topology InnerProductSpace ComplexConjugate

namespace UV

theorem wilson_edge_wave_continuous_momentum (x d : ThinCurrentPlane) :
    Continuous (fun p => wilsonEdgeWave p x d) := by
  apply intervalIntegral.continuous_of_dominated_interval (bound := fun _ => 1)
  · intro p
    exact (show Continuous (fun t : ℝ => thinPlaneWave p (x+t • d)) by unfold thinPlaneWave; fun_prop).aestronglyMeasurable
  · intro p
    exact Eventually.of_forall (fun t _ => by simp [thinPlaneWave,Complex.norm_exp,Complex.mul_re])
  · exact (continuous_const (y := (1:ℝ))).intervalIntegrable (μ := volume) 0 1
  · exact Eventually.of_forall (fun _ _ => by unfold thinPlaneWave; fun_prop)

theorem wilson_polygon_continuous (d : ℕ → ThinCurrentPlane) (N : ℕ) :
    Continuous (wilsonPolygonCurrent d N) :=
  continuous_finset_sum _ (fun k _ => (wilson_edge_wave_continuous_momentum (wilsonPolygonStart d k) (d k)).smul continuous_const)

theorem wilson_edge_conjugate (p x d : ThinCurrentPlane) :
    wilsonEdgeWave (-p) x d = conj (wilsonEdgeWave p x d) := by
  unfold wilsonEdgeWave
  rw [intervalIntegral.integral_of_le zero_le_one,intervalIntegral.integral_of_le zero_le_one,←integral_conj]
  congr 1
  funext t
  simp [thinPlaneWave,←Complex.exp_conj,inner_neg_left]

theorem wilson_polygon_conjugate (d : ℕ → ThinCurrentPlane) (N : ℕ) (p : ThinCurrentPlane) (i : Fin 4) :
    wilsonPolygonCurrent d N (-p) i = conj (wilsonPolygonCurrent d N p i) := by
  simp [wilson_polygon_coordinate,wilson_edge_conjugate]

def wilsonTransverseSpace (p : ThinCurrentPlane) : Submodule ℂ (EuclideanSpace ℂ (Fin 4)) :=
  (ℂ ∙ wilsonCarrierInclusion p)ᗮ

theorem wilson_transverse_projection (d : ℕ → ThinCurrentPlane) (N : ℕ)
    (hc : wilsonPolygonStart d N = 0) (p : ThinCurrentPlane) :
    (wilsonTransverseSpace p).starProjection (wilsonPolygonCurrent d N p) = wilsonPolygonCurrent d N p := by
  apply Submodule.starProjection_eq_self_iff.mpr
  apply Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
  rw [PiLp.inner_apply]
  simpa only [RCLike.inner_apply,wilsonCarrierInclusion,LinearMap.coe_mk,AddHom.coe_mk,complexifyMomentum,
    PiLp.toLp_apply,Complex.conj_ofReal,mul_comm] using wilson_polygon_transverse d N p hc

/-- The identical external shell at the two ends gives its squared modulus.
The Hermitian numerator below equals the bilinear pairing with momenta p and −p. -/
def wilsonSewnPhoton (χ : ThinCurrentPlane → ℂ) (d e : ℕ → ThinCurrentPlane) (N M : ℕ) (p : ThinCurrentPlane) : ℂ :=
  ((‖χ p‖^2:ℝ):ℂ) * inner ℂ (wilsonPolygonCurrent e M p)
    ((wilsonTransverseSpace p).starProjection (wilsonPolygonCurrent d N p)) / ((‖p‖^2:ℝ):ℂ)

theorem wilson_sewn_photon_coordinates (χ : ThinCurrentPlane → ℂ) (d e : ℕ → ThinCurrentPlane) (N M : ℕ)
    (hc : wilsonPolygonStart d N = 0) (p : ThinCurrentPlane) :
    wilsonSewnPhoton χ d e N M p = ((‖χ p‖^2:ℝ):ℂ) *
      (∑ i : Fin 4, wilsonPolygonCurrent d N p i * wilsonPolygonCurrent e M (-p) i) / ((‖p‖^2:ℝ):ℂ) := by
  simp only [wilsonSewnPhoton,wilson_transverse_projection d N hc,PiLp.inner_apply,RCLike.inner_apply,
    wilson_polygon_conjugate]

theorem wilson_sewn_photon_bound (χ : ThinCurrentPlane → ℂ) (d e : ℕ → ThinCurrentPlane) (N M : ℕ)
    (hc : wilsonPolygonStart d N = 0) (hc' : wilsonPolygonStart e M = 0) (p : ThinCurrentPlane) :
    ‖wilsonSewnPhoton χ d e N M p‖ ≤ ‖χ p‖^2 * (wilsonPerimeter d N^2 * wilsonPerimeter e M^2) := by
  rw [wilsonSewnPhoton,wilson_transverse_projection d N hc,norm_div,norm_mul,Complex.norm_real,Complex.norm_real,
    Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _),abs_of_nonneg (sq_nonneg _),mul_div_assoc]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  by_cases hp : p = 0
  · subst p
    simp
    positivity
  · apply (div_le_iff₀ (sq_pos_of_pos (norm_pos_iff.mpr hp))).mpr
    calc
      _ ≤ ‖wilsonPolygonCurrent e M p‖*‖wilsonPolygonCurrent d N p‖ := norm_inner_le_norm _ _
      _ ≤ (‖p‖*wilsonPerimeter e M^2)*(‖p‖*wilsonPerimeter d N^2) := mul_le_mul
        (wilson_polygon_soft_bound e M p hc') (wilson_polygon_soft_bound d N p hc)
        (norm_nonneg _) (mul_nonneg (norm_nonneg _) (sq_nonneg _))
      _ = _ := by ring

theorem wilson_sewn_photon_integrable {χ : ThinCurrentPlane → ℂ} (hχ : Integrable (fun p => ‖χ p‖^2))
    (d e : ℕ → ThinCurrentPlane) (N M : ℕ) (hc : wilsonPolygonStart d N = 0)
    (hc' : wilsonPolygonStart e M = 0) : Integrable (wilsonSewnPhoton χ d e N M) := by
  apply (hχ.mul_const (wilsonPerimeter d N^2 * wilsonPerimeter e M^2)).mono' _ (Eventually.of_forall (wilson_sewn_photon_bound _ _ _ _ _ hc hc'))
  change AEStronglyMeasurable (fun p => wilsonSewnPhoton χ d e N M p) volume
  simp only [wilsonSewnPhoton,wilson_transverse_projection d N hc]
  apply AEMeasurable.aestronglyMeasurable
  exact ((Complex.continuous_ofReal.measurable.comp_aemeasurable hχ.aemeasurable).mul
    ((wilson_polygon_continuous e M).inner (𝕜 := ℂ) (wilson_polygon_continuous d N)).measurable.aemeasurable).div
      ((Complex.continuous_ofReal.comp (continuous_norm.pow 2)).measurable.aemeasurable)

theorem wilson_sewn_photon_of_power_envelope {χ : ThinCurrentPlane → ℂ} (hχ : Measurable χ)
    {K C : ℝ} (hK : 4 < K) (hbound : ∀ p, ‖χ p‖^2 ≤ C*(1+‖p‖)^(-K))
    (d e : ℕ → ThinCurrentPlane) (N M : ℕ) (hc : wilsonPolygonStart d N = 0)
    (hc' : wilsonPolygonStart e M = 0) : Integrable (wilsonSewnPhoton χ d e N M) := by
  apply wilson_sewn_photon_integrable _ d e N M hc hc'
  have h := integrable_one_add_norm (μ := (volume : Measure ThinCurrentPlane)) (r := K)
    (by simpa [finrank_euclideanSpace] using hK)
  apply (h.const_mul C).mono' (hχ.norm.pow_const 2).aestronglyMeasurable
  exact Eventually.of_forall (fun p => by simpa only [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg ‖χ p‖)] using hbound p)

/-- Independent photon momenta may go soft or hard simultaneously. Each
independent edge is sewn with the transverse current and its own shell. -/
theorem wilson_independent_sewn_photons {ι : Type*} [Fintype ι] {χ : ι → ThinCurrentPlane → ℂ}
    (hχ : ∀ i, Integrable (fun p => ‖χ i p‖^2)) (d e : ι → ℕ → ThinCurrentPlane) (N M : ι → ℕ)
    (hc : ∀ i, wilsonPolygonStart (d i) (N i) = 0) (hc' : ∀ i, wilsonPolygonStart (e i) (M i) = 0) :
    Integrable (fun q : ι → ThinCurrentPlane => ∏ i, wilsonSewnPhoton (χ i) (d i) (e i) (N i) (M i) (q i))
      (Measure.pi (fun _ => volume)) :=
  Integrable.fintype_prod (fun i => wilson_sewn_photon_integrable (hχ i) (d i) (e i) (N i) (M i) (hc i) (hc' i))

end UV
