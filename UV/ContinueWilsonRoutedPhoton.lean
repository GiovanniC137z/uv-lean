import UV.ContinueWilsonActualShell

/-! The transverse Maxwell product on closed charged polygons. Chord
momenta are independent integration variables. All remaining edges may
depend on all chords, and different edges may use the same polygon. -/

noncomputable section

open MeasureTheory Filter
open scoped Topology InnerProductSpace

namespace UV

variable {ι : Type*} [Fintype ι]

theorem wilson_shell_form_le_one (L : ℝ) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι) (p : OSFourSpace) :
    ‖wilsonShellPhotonForm L T p‖ ≤ 1 := by
  rw [wilson_shell_photon_transform]
  exact wilson_marked_transform_bound _ (Eventually.of_forall (fun _ => (norm_one (α := ℂ)).le)) p

theorem wilson_shell_form_zero (L : ℝ) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι) :
    wilsonShellPhotonForm L T 0 = 1 := by simp [wilsonShellPhotonForm]

theorem wilson_shell_form_continuous (L : ℝ) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι) :
    Continuous (wilsonShellPhotonForm L T) := by
  rw [wilson_shell_photon_transform]
  apply continuous_iff_continuousAt.mpr
  intro p
  unfold ContinuousAt wilsonMarkedTransform
  apply tendsto_integral_filter_of_dominated_convergence (fun _ => 1)
    (Eventually.of_forall fun q => (show Continuous (fun d : OSFourSpace => thinPlaneWave q d * 1) by unfold thinPlaneWave; fun_prop).aestronglyMeasurable)
    (Eventually.of_forall fun q => Eventually.of_forall fun d => by simp [wilson_wave_norm])
    (integrable_const 1)
  exact Eventually.of_forall (fun d => (show Continuous (fun q : OSFourSpace => thinPlaneWave q d * 1) by unfold thinPlaneWave; fun_prop).tendsto p)

structure WilsonClosedPolygon where
  displacement : ℕ → OSFourSpace
  hops : ℕ
  closed : wilsonPolygonStart displacement hops = 0

def WilsonClosedPolygon.perimeter (P : WilsonClosedPolygon) : ℝ :=
  wilsonPerimeter P.displacement P.hops

structure WilsonPolygonEdge where
  src : WilsonClosedPolygon
  dst : WilsonClosedPolygon

def WilsonPolygonEdge.sewing (e : WilsonPolygonEdge) (χ : OSFourSpace → ℂ) : OSFourSpace → ℂ :=
  wilsonSewnPhoton χ e.src.displacement e.dst.displacement e.src.hops e.dst.hops

def WilsonPolygonEdge.cost (e : WilsonPolygonEdge) : ℝ := e.src.perimeter^2 * e.dst.perimeter^2

theorem WilsonPolygonEdge.cost_nonneg (e : WilsonPolygonEdge) : 0 ≤ e.cost := mul_nonneg (sq_nonneg _) (sq_nonneg _)

theorem WilsonPolygonEdge.bound (e : WilsonPolygonEdge) (χ : OSFourSpace → ℂ) (p : OSFourSpace) :
    ‖e.sewing χ p‖ ≤ ‖χ p‖^2 * e.cost :=
  wilson_sewn_photon_bound _ _ _ _ _ e.src.closed e.dst.closed p

theorem WilsonPolygonEdge.uniform_bound (e : WilsonPolygonEdge) (L : ℝ)
    (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι) (p : OSFourSpace) :
    ‖e.sewing (wilsonShellPhotonForm L T) p‖ ≤ e.cost := by
  apply (e.bound _ p).trans
  exact mul_le_of_le_one_left e.cost_nonneg (by simpa using pow_le_pow_left₀ (norm_nonneg _) (wilson_shell_form_le_one L T p) 2)

theorem WilsonPolygonEdge.formula (e : WilsonPolygonEdge) (χ : OSFourSpace → ℂ) (p : OSFourSpace) :
    e.sewing χ p = ((‖χ p‖^2 : ℝ) : ℂ) * inner ℂ (wilsonPolygonCurrent e.dst.displacement e.dst.hops p)
      (wilsonPolygonCurrent e.src.displacement e.src.hops p) / ((‖p‖^2 : ℝ) : ℂ) := by
  unfold sewing wilsonSewnPhoton
  rw [wilson_transverse_projection _ _ e.src.closed]

theorem WilsonPolygonEdge.sewing_measurable (e : WilsonPolygonEdge) {χ : OSFourSpace → ℂ} (hχ : Continuous χ) :
    Measurable (e.sewing χ) := by
  change Measurable (fun p => e.sewing χ p)
  simp only [e.formula]
  exact ((Complex.continuous_ofReal.comp (hχ.norm.pow 2)).mul
    ((wilson_polygon_continuous _ _).inner (𝕜 := ℂ) (wilson_polygon_continuous _ _))).measurable.div
      (Complex.continuous_ofReal.comp (continuous_norm.pow 2)).measurable

theorem WilsonPolygonEdge.sewing_continuousAt (e : WilsonPolygonEdge) {χ : OSFourSpace → ℂ} (hχ : Continuous χ)
    {p : OSFourSpace} (hp : p ≠ 0) : ContinuousAt (e.sewing χ) p := by
  change ContinuousAt (fun q => e.sewing χ q) p
  simp only [e.formula]
  apply (((Complex.continuous_ofReal.comp (hχ.norm.pow 2)).mul
    ((wilson_polygon_continuous _ _).inner (𝕜 := ℂ) (wilson_polygon_continuous _ _))).continuousAt).div
    (Complex.continuous_ofReal.comp (continuous_norm.pow 2)).continuousAt
  exact Complex.ofReal_ne_zero.mpr (pow_ne_zero 2 (norm_ne_zero_iff.mpr hp))

variable {C D : Type*} [Fintype C] [Fintype D]

def wilsonRoutedPhotonProduct (χ : OSFourSpace → ℂ) (chord : C → WilsonPolygonEdge) (tree : D → WilsonPolygonEdge)
    (route : (C → OSFourSpace) → D → OSFourSpace) (q : C → OSFourSpace) : ℂ :=
  (∏ i, (chord i).sewing χ (q i)) * ∏ e, (tree e).sewing χ (route q e)

def wilsonRoutedPhotonCost (chord : C → WilsonPolygonEdge) (tree : D → WilsonPolygonEdge) : ℝ :=
  (∏ i, (chord i).cost) * ∏ e, (tree e).cost

theorem wilson_routed_product_measurable {χ : OSFourSpace → ℂ} (hχ : Continuous χ)
    (chord : C → WilsonPolygonEdge) (tree : D → WilsonPolygonEdge) {route : (C → OSFourSpace) → D → OSFourSpace}
    (hroute : ∀ e, Measurable (route · e)) : Measurable (wilsonRoutedPhotonProduct χ chord tree route) :=
  (Finset.measurable_prod _ (fun i _ => ((chord i).sewing_measurable hχ).comp (measurable_pi_apply i))).mul
    (Finset.measurable_prod _ (fun e _ => ((tree e).sewing_measurable hχ).comp (hroute e)))

theorem wilson_routed_product_bound (L : ℝ) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι)
    (chord : C → WilsonPolygonEdge) (tree : D → WilsonPolygonEdge) (route : (C → OSFourSpace) → D → OSFourSpace)
    (q : C → OSFourSpace) :
    ‖wilsonRoutedPhotonProduct (wilsonShellPhotonForm L T) chord tree route q‖ ≤
      (∏ i, ‖wilsonShellPhotonForm L T (q i)‖^2) * wilsonRoutedPhotonCost chord tree := by
  rw [wilsonRoutedPhotonProduct,norm_mul,norm_prod,norm_prod,wilsonRoutedPhotonCost,←mul_assoc,←Finset.prod_mul_distrib]
  exact mul_le_mul (Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun i _ => (chord i).bound _ _))
    (Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun e _ => (tree e).uniform_bound L T _))
    (Finset.prod_nonneg (fun _ _ => norm_nonneg _))
    (Finset.prod_nonneg (fun i _ => mul_nonneg (sq_nonneg _) (chord i).cost_nonneg))

/-- The same chord majorant works uniformly for every measurable routing
of the remaining photon edges, including simultaneous soft and hard regions. -/
theorem wilson_routed_photons_integrable {L : ℝ} (hL : 0 < L) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι)
    (chord : C → WilsonPolygonEdge) (tree : D → WilsonPolygonEdge) {route : (C → OSFourSpace) → D → OSFourSpace}
    (hroute : ∀ e, Measurable (route · e)) :
    Integrable (wilsonRoutedPhotonProduct (wilsonShellPhotonForm L T) chord tree route)
      (Measure.pi (fun _ => volume)) :=
  ((Integrable.fintype_prod (fun _ : C => wilson_actual_shell_square_integrable hL T)).mul_const
    (wilsonRoutedPhotonCost chord tree)).mono' (wilson_routed_product_measurable (wilson_shell_form_continuous L T)
      chord tree hroute).aestronglyMeasurable (Eventually.of_forall (wilson_routed_product_bound L T chord tree route))

end UV
