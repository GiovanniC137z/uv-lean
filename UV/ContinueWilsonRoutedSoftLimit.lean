import UV.ContinueWilsonAffineRoute

/-! The amputated two-point coefficient for fixed closed Wilson polygons.
All photon momenta live in the Euclidean chart of the selected plane.
The derivative is taken along a unit direction and both external test
polarizations have norm one. -/

noncomputable section

open MeasureTheory Filter Set UV.SectorPlane
open scoped Topology RealInnerProductSpace

namespace UV

def wilsonOppositeDirection (u : UnitVector OSFourSpace) : UnitVector OSFourSpace :=
  ⟨-u.val, (norm_neg _).trans u.property⟩

def WilsonClosedPolygon.polarized (P : WilsonClosedPolygon) (v : UnitVector OSFourSpace) (p : OSFourSpace) : ℂ :=
  inner ℂ (wilsonCarrierInclusion v.val) (wilsonPolygonCurrent P.displacement P.hops p)

theorem WilsonClosedPolygon.polarized_coordinates (P : WilsonClosedPolygon) (v : UnitVector OSFourSpace) (p : OSFourSpace) :
    P.polarized v p = ∑ i : Fin 4, wilsonPolygonCurrent P.displacement P.hops p i * (v.val i:ℂ) := by
  simp [polarized,PiLp.inner_apply,RCLike.inner_apply,wilsonCarrierInclusion,complexifyMomentum]

def WilsonClosedPolygon.softMark (P : WilsonClosedPolygon) (χ : OSFourSpace → ℂ)
    (u v : UnitVector OSFourSpace) (r : ℝ) : ℂ := χ (r • u.val)*(P.polarized v (r • u.val)/(r:ℂ))

def WilsonClosedPolygon.softCoefficient (P : WilsonClosedPolygon) (u v : UnitVector OSFourSpace) : ℂ :=
  ∑ i : Fin 4, (∑ k ∈ Finset.range P.hops,
    (Complex.I*(⟪u.val,wilsonPolygonStart P.displacement k+(1/2:ℝ) • P.displacement k⟫:ℂ))*
      (P.displacement k i:ℂ))*(v.val i:ℂ)

theorem WilsonClosedPolygon.softMark_limit (P : WilsonClosedPolygon) {χ : OSFourSpace → ℂ}
    (hχ : Continuous χ) (h0 : χ 0 = 1) (u v : UnitVector OSFourSpace) :
    Tendsto (P.softMark χ u v) (𝓝[≠] 0) (𝓝 (P.softCoefficient u v)) := by
  have hs : Tendsto (fun r : ℝ => χ (r • u.val)) (𝓝[≠] 0) (𝓝 1) := by
    have h := (hχ.comp (continuous_id.smul (continuous_const (y := u.val)))).continuousAt (x := (0:ℝ))
    simpa only [Function.comp_apply,id_eq,zero_smul,h0] using h.tendsto.mono_left nhdsWithin_le_nhds
  have hvec := tendsto_finset_sum (Finset.univ : Finset (Fin 4)) (fun i _ =>
    (wilson_polygon_soft_directional u P.displacement P.hops P.closed i).mul_const (v.val i:ℂ))
  have he (r : ℝ) : P.polarized v (r • u.val)/(r:ℂ) =
      ∑ i : Fin 4, wilsonPolygonCurrent P.displacement P.hops (r • u.val) i/(r:ℂ)*(v.val i:ℂ) := by
    rw [P.polarized_coordinates,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    ring
  change Tendsto (fun r => P.softMark χ u v r) _ _
  simpa only [softMark,softCoefficient,he,one_mul] using hs.mul hvec

theorem WilsonClosedPolygon.softMark_bound (P : WilsonClosedPolygon) {χ : OSFourSpace → ℂ}
    (hχ : ∀ p, ‖χ p‖ ≤ 1) (u v : UnitVector OSFourSpace) (r : ℝ) :
    ‖P.softMark χ u v r‖ ≤ P.perimeter^2 := by
  unfold softMark
  rw [norm_mul,norm_div,Complex.norm_real]
  apply (mul_le_of_le_one_left (div_nonneg (norm_nonneg _) (norm_nonneg _)) (hχ _)).trans
  by_cases hr : r = 0
  · simpa only [hr,norm_zero,div_zero] using sq_nonneg P.perimeter
  · apply (div_le_iff₀ (norm_pos_iff.mpr hr)).mpr
    have h := (norm_inner_le_norm (𝕜 := ℂ) (wilsonCarrierInclusion v.val) (wilsonPolygonCurrent P.displacement P.hops (r • u.val)))
    rw [wilson_carrier_inclusion_norm,v.property,one_mul] at h
    apply h.trans
    simpa only [perimeter,norm_smul,u.property,mul_one,mul_comm] using
      wilson_polygon_soft_bound P.displacement P.hops (r • u.val) P.closed

variable {C D : Type*} [Fintype C] [Fintype D]

theorem wilson_routed_product_soft_limit {χ : OSFourSpace → ℂ} (hχ : Continuous χ)
    (chord : C → WilsonPolygonEdge) (tree : D → WilsonPolygonEdge)
    (b : OSFourSpace → D → OSFourSpace) (hb : ∀ e, ContinuousAt (b · e) 0)
    (a : D → C → ℝ) (ha : ∀ e, ∃ j, a e j ≠ 0) (u : UnitVector OSFourSpace) :
    ∀ᵐ q ∂Measure.pi (fun _ : C => (volume : Measure OSFourSpace)),
      Tendsto (fun r : ℝ => wilsonRoutedPhotonProduct χ chord tree
        (fun k e => wilsonAffineTransfer (b (r • u.val) e) (a e) k) q) (𝓝[≠] 0)
        (𝓝 (wilsonRoutedPhotonProduct χ chord tree (fun k e => wilsonAffineTransfer (b 0 e) (a e) k) q)) := by
  have hall := ae_all_iff.mpr (fun e => wilson_affine_transfer_null (b 0 e) (ha e))
  filter_upwards [hall] with q hq
  have hru : Tendsto (fun r : ℝ => r • u.val) (𝓝[≠] 0) (𝓝 0) := by
    simpa using ((continuous_id.smul (continuous_const (y := u.val))).continuousAt (x := (0:ℝ))).tendsto.mono_left nhdsWithin_le_nhds
  apply Tendsto.const_mul
  apply tendsto_finset_prod
  intro e _
  exact ((tree e).sewing_continuousAt hχ (hq e)).tendsto.comp (((hb e).tendsto.comp hru).add_const _)

variable {ι : Type*} [Fintype ι]

/-- The two external currents are each divided by the same real radial
parameter. The limiting coefficient integrates their actual first
moments and the internally routed transverse photon product. -/
theorem wilson_fixed_polygon_two_point_limit {L : ℝ} (hL : 0 < L) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι)
    (chord : C → WilsonPolygonEdge) (tree : D → WilsonPolygonEdge)
    (b : OSFourSpace → D → OSFourSpace) (hb : ∀ e, ContinuousAt (b · e) 0)
    (a : D → C → ℝ) (ha : ∀ e, ∃ j, a e j ≠ 0)
    (P Q : WilsonClosedPolygon) (u v w : UnitVector OSFourSpace) :
    let χ := wilsonShellPhotonForm L T
    let F := fun z k => wilsonRoutedPhotonProduct χ chord tree (fun p e => wilsonAffineTransfer (b z e) (a e) p) k
    Tendsto (fun r : ℝ => ∫ k, P.softMark χ u v r * Q.softMark χ (wilsonOppositeDirection u) w r * F (r • u.val) k
      ∂Measure.pi (fun _ : C => volume)) (𝓝[≠] 0)
      (𝓝 (∫ k, P.softCoefficient u v * Q.softCoefficient (wilsonOppositeDirection u) w * F 0 k
        ∂Measure.pi (fun _ : C => volume))) := by
  dsimp only
  let χ := wilsonShellPhotonForm L T
  let F := fun z k => wilsonRoutedPhotonProduct χ chord tree (fun p e => wilsonAffineTransfer (b z e) (a e) p) k
  have hInt (z) : Integrable (F z) (Measure.pi (fun _ : C => volume)) :=
    wilson_routed_photons_integrable hL T chord tree (fun e => (wilson_affine_transfer_continuous _ _).measurable)
  have hχ := wilson_shell_form_continuous L T
  have hI := ((Integrable.fintype_prod (fun _ : C => wilson_actual_shell_square_integrable hL T)).mul_const
    (wilsonRoutedPhotonCost chord tree)).const_mul (P.perimeter^2 * Q.perimeter^2)
  refine tendsto_integral_filter_of_dominated_convergence _ (Eventually.of_forall fun r => ((hInt _).const_mul _).aestronglyMeasurable)
    ?_ hI ?_
  · apply Eventually.of_forall
    intro r
    apply Eventually.of_forall
    intro k
    rw [norm_mul,norm_mul]
    exact mul_le_mul (mul_le_mul (P.softMark_bound (wilson_shell_form_le_one L T) _ _ _)
      (Q.softMark_bound (wilson_shell_form_le_one L T) _ _ _) (norm_nonneg _) (sq_nonneg _))
      (wilson_routed_product_bound L T chord tree _ _) (norm_nonneg _) (mul_nonneg (sq_nonneg _) (sq_nonneg _))
  · filter_upwards [wilson_routed_product_soft_limit hχ chord tree b hb a ha u] with k hk
    exact ((P.softMark_limit hχ (wilson_shell_form_zero L T) u v).mul
      (Q.softMark_limit hχ (wilson_shell_form_zero L T) _ w)).mul hk

end UV
