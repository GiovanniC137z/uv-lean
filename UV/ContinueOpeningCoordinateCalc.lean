import UV.UnboundedSourceBorel
import UV.UnboundedSourceProjection

/-! Measurable real coordinates acting on complex L², with strong
convergence proved in the Hilbert norm by dominated convergence. -/

noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace Topology

namespace UV

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

theorem opening_l2_norm_square (x : Lp ℂ 2 μ) : ‖x‖^2 = ∫ u, ‖x u‖^2 ∂μ := by
  rw [←inner_self_eq_norm_sq (𝕜 := ℂ),L2.inner_def,←integral_re (L2.integrable_inner _ _)]
  simp only [inner_self_eq_norm_sq]

/-- A dominated sequence (or countably generated net) of concrete
representatives converges in complex L². Each representative can use
a distinct null exceptional set. -/
theorem opening_l2_dominated {ι : Type*} (l : Filter ι) [l.IsCountablyGenerated]
    (v : ι → Lp ℂ 2 μ) (x : Lp ℂ 2 μ) (a : ι → X → ℂ) (b : X → ℂ)
    (ha : ∀ i, (v i : X → ℂ) =ᵐ[μ] a i) (hb : (x : X → ℂ) =ᵐ[μ] b)
    (G : X → ℝ) (hG : Integrable G μ) (hbound : ∀ i, ∀ᵐ u ∂μ, ‖a i u-b u‖^2 ≤ G u)
    (hlim : ∀ᵐ u ∂μ, Tendsto (fun i => a i u) l (𝓝 (b u))) :
    Tendsto v l (𝓝 x) := by
  have hm i : AEStronglyMeasurable (fun u => ‖a i u-b u‖^2) μ :=
    ((((Lp.aestronglyMeasurable (v i)).congr (ha i)).sub ((Lp.aestronglyMeasurable x).congr hb)).norm.pow 2)
  have h := tendsto_integral_filter_of_dominated_convergence (l := l) (μ := μ)
    (F := fun i u => ‖a i u-b u‖^2) (f := fun _ => 0) G (Eventually.of_forall hm)
    (Eventually.of_forall (fun i => (hbound i).mono fun u h => by simpa using h))
    hG (hlim.mono (fun u hu => by simpa using (hu.sub_const (b u)).norm.pow 2))
  have he i : (∫ u, ‖a i u-b u‖^2 ∂μ) = ‖v i-x‖^2 := by
    rw [opening_l2_norm_square]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (v i) x,ha i,hb] with u hu hv hw
    rw [hu]
    simp [hv,hw]
  simp_rw [he] at h
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have ht := Real.continuous_sqrt.continuousAt.tendsto.comp h
  change Tendsto (fun i => Real.sqrt (‖v i-x‖^2)) l (𝓝 (Real.sqrt (∫ _ : X, (0:ℝ) ∂μ))) at ht
  simpa using ht

private def openingBoundedLinear (w : X → ℝ) (hw : Measurable w) (C : ℝ)
    (hC : ∀ u, |w u| ≤ C) : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ :=
  let T := sourceL2Multiplier μ (fun u => (w u : ℂ))
  T.toFun.comp (LinearMap.id.codRestrict T.domain (fun x => by
    apply (Lp.memLp x).of_le_mul (c := C) ((Complex.measurable_ofReal.comp hw).aestronglyMeasurable.mul (Lp.aestronglyMeasurable x))
    exact ae_of_all _ (fun u => by
      change ‖(w u:ℂ)*x u‖ ≤ C*‖x u‖
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hC u) (norm_nonneg _))))

private theorem opening_bounded_linear_ae (w : X → ℝ) (hw : Measurable w) (C : ℝ) (hC : ∀ u, |w u| ≤ C)
    (x : Lp ℂ 2 μ) : (openingBoundedLinear μ w hw C hC x : X → ℂ) =ᵐ[μ] fun u => (w u : ℂ)*x u :=
  sourceL2Multiplier_coe μ _ _

private theorem opening_bounded_linear_le (w : X → ℝ) (hw : Measurable w) (C : ℝ) (h0 : 0 ≤ C)
    (hC : ∀ u, |w u| ≤ C) (x : Lp ℂ 2 μ) : ‖openingBoundedLinear μ w hw C hC x‖ ≤ C*‖x‖ := by
  have he : C*‖x‖ = ‖(C:ℂ) • x‖ := by rw [norm_smul,Complex.norm_real,Real.norm_of_nonneg h0]
  rw [he]
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [opening_bounded_linear_ae μ w hw C hC x,Lp.coeFn_smul (C:ℂ) x] with u h k
  rw [h,k]
  simp only [Pi.smul_apply,smul_eq_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg h0]
  exact mul_le_mul_of_nonneg_right (hC u) (norm_nonneg _)

/-- The calculus only uses the indicated value at bounded Borel symbols. -/
def openingCoordinateAction (w : X → ℝ) (hw : Measurable w) (f : ℝ → ℝ) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ := by
  classical
  exact if h : sourceBoundedBorel f then
    let C := h.2.choose
    let hc := h.2.choose_spec
    (openingBoundedLinear μ (f ∘ w) (h.1.comp hw) C (fun u => hc.2 (w u))).mkContinuous C
      (opening_bounded_linear_le μ _ _ C hc.1 _)
  else 0

theorem opening_coordinate_action_ae (w : X → ℝ) (hw : Measurable w) {f : ℝ → ℝ}
    (hf : sourceBoundedBorel f) (x : Lp ℂ 2 μ) :
    (openingCoordinateAction μ w hw f x : X → ℂ) =ᵐ[μ] fun u => (f (w u):ℂ)*x u := by
  classical
  unfold openingCoordinateAction
  rw [dif_pos hf]
  exact opening_bounded_linear_ae μ (f ∘ w) (hf.1.comp hw) hf.2.choose (fun u => hf.2.choose_spec.2 (w u)) x

theorem opening_coordinate_action_strong (w : X → ℝ) (hw : Measurable w)
    {ι : Type*} (l : Filter ι) [l.IsCountablyGenerated] [l.NeBot]
    (f : ι → ℝ → ℝ) (g : ℝ → ℝ) (C : ℝ) (hf : ∀ i, Measurable (f i))
    (hg : Measurable g) (hC : 0 ≤ C) (hB : ∀ i u, |f i u| ≤ C)
    (hlim : ∀ u, Tendsto (fun i => f i u) l (𝓝 (g u))) (x : Lp ℂ 2 μ) :
    Tendsto (fun i => openingCoordinateAction μ w hw (f i) x) l (𝓝 (openingCoordinateAction μ w hw g x)) := by
  have hb u : |g u| ≤ C := le_of_tendsto (hlim u).abs (Eventually.of_forall fun i => hB i u)
  have hfx i := opening_coordinate_action_ae μ w hw (show sourceBoundedBorel (f i) from ⟨hf i,C,hC,hB i⟩) x
  have hgx := opening_coordinate_action_ae μ w hw (show sourceBoundedBorel g from ⟨hg,C,hC,hb⟩) x
  have hi := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable x)).mp (Lp.memLp x)
  apply opening_l2_dominated μ l _ _ _ _ hfx hgx (fun u => (2*C)^2*‖x u‖^2) (hi.const_mul _)
  · intro i
    apply ae_of_all
    intro u
    rw [←sub_mul,norm_mul,mul_pow]
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    apply pow_le_pow_left₀ (norm_nonneg _)
    refine (norm_sub_le _ _).trans ?_
    simpa only [Complex.norm_real,Real.norm_eq_abs,two_mul] using add_le_add (hB i (w u)) (hb (w u))
  · exact ae_of_all _ fun u => (Complex.continuous_ofReal.continuousAt.tendsto.comp (hlim (w u))).mul_const (x u)

end UV
