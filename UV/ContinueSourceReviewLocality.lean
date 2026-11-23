import UV.ContinuationSectorPlane
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Topology.Compactness.Lindelof

/-! Instantaneous charged hopping and localized occupation phases, expanded
manuscript proposition `prop:omega-locality-uv`. Real carrier time acts by
the Hamiltonian's strongly continuous unitary evolution. A vacuum-to-pair
kernel is tested on separated spatial neighborhoods of the same plane. -/

noncomputable section
open Filter Set Metric MeasureTheory UV.SectorPlane
open scoped Topology ContDiff

namespace UV

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Vacuum-to-pair consequence of commutation on a time neighborhood. Only the
initial test vector must be in the domain of the infinitesimal generator.
Strong continuity suffices on the second vector. -/
theorem sea_locality_forces_zero (V : ℝ → E ≃ₗᵢ[ℂ] E)
    (vzero : ∀ w, V 0 w = w) (vinv : ∀ t w, V t (V (-t) w) = w)
    (vcont : ∀ w, ContinuousAt (fun t => V t w) 0)
    (Ω K : E) (hK : HasDerivAt (fun t => V (-t) Ω) ((-Complex.I) • K) 0)
    (F H : E →L[ℂ] E) (hF : F Ω = Ω) (hH : H Ω = Ω)
    (hloc : ∀ᶠ t in 𝓝 0, V t (F (V (-t) (H Ω))) = H (V t (F (V (-t) Ω)))) :
    ((1-H) : E →L[ℂ] E) (((F-1) : E →L[ℂ] E) K) = 0 := by
  let A : E →L[ℂ] E := F-1
  let B : E →L[ℂ] E := 1-H
  let D := (-Complex.I) • K
  let q (t : ℝ) := t⁻¹ • (V (-t) Ω - Ω)
  have hq : Tendsto q (𝓝[≠] 0) (𝓝 D) := by simpa [q,D,vzero] using hK.tendsto_slope_zero
  have hA := A.continuous.continuousAt.tendsto.comp hq
  have hT : Tendsto (fun t => V t (A (q t))) (𝓝[≠] 0) (𝓝 (A D)) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    have hv : Tendsto (fun t => V t (A D)) (𝓝[≠] 0) (𝓝 (A D)) := by
      simpa only [vzero] using ((vcont (A D)).continuousWithinAt (s := {0}ᶜ)).tendsto
    have hv' := tendsto_iff_dist_tendsto_zero.mp hv
    have ha' := tendsto_iff_dist_tendsto_zero.mp hA
    apply squeeze_zero (fun _ => dist_nonneg)
    · intro t
      calc dist (V t (A (q t))) (A D) ≤ dist (V t (A (q t))) (V t (A D)) + dist (V t (A D)) (A D) := dist_triangle _ _ _
           _ = _ := by rw [(V t).isometry.dist_eq]
    · simpa using ha'.add hv'
  have hB := B.continuous.continuousAt.tendsto.comp hT
  have heq : (fun t => B (V t (A (q t)))) =ᶠ[𝓝[≠] 0] fun _ => 0 := by
    filter_upwards [hloc.filter_mono nhdsWithin_le_nhds] with t ht
    rw [hH] at ht
    have hs : A (q t) = ((t⁻¹:ℝ):ℂ) • (F (V (-t) Ω)-V (-t) Ω) := by
      change A (((t⁻¹:ℝ):ℂ) • (V (-t) Ω-Ω)) = _
      rw [map_smul,map_sub]; congr 1
      simp only [A,ContinuousLinearMap.sub_apply,ContinuousLinearMap.one_apply,hF,sub_self,sub_zero]
    simp only [B,ContinuousLinearMap.sub_apply,ContinuousLinearMap.one_apply,hs,map_smul,
      map_sub,vinv,hH,←ht,sub_self,smul_zero]
  have hz := tendsto_nhds_unique hB ((tendsto_const_nhds (x := (0:E))).congr' heq.symm)
  change B (A ((-Complex.I) • K)) = 0 at hz
  rw [map_smul,map_smul,smul_eq_zero] at hz
  exact hz.resolve_left (neg_ne_zero.mpr Complex.I_ne_zero)

def seaOccupationPhase (f : Spatial → ℝ) (x y : Spatial) : ℂ :=
  Complex.exp (((f x - f y : ℝ):ℂ)*Complex.I)

private def seaLocationBump (x : Spatial) (r : ℝ) (hr : 0 < r) : ContDiffBump x :=
  ⟨r,2*r,hr,by linarith⟩

private theorem sea_pair_phase_product {Config : Type*} [MeasurableSpace Config] {μ : Measure Config}
    (x y : Config → Spatial) (P : E →L[ℂ] Lp ℂ 2 μ) (T : (Spatial → ℝ) → E →L[ℂ] E)
    (hT : ∀ f w, ∀ᵐ a ∂μ, P (T f w) a = seaOccupationPhase f (x a) (y a) * P w a)
    (f h : Spatial → ℝ) (K : E)
    (hz : ((1-T h) : E →L[ℂ] E) (((T f-1) : E →L[ℂ] E) K) = 0) :
    ∀ᵐ a ∂μ, (1-seaOccupationPhase h (x a) (y a)) *
      (seaOccupationPhase f (x a) (y a)-1) * P K a = 0 := by
  let w := T f K - K
  change w - T h w = 0 at hz
  have eqw : P w = P (T h w) := congrArg P (sub_eq_zero.mp hz)
  have hw : P w = P (T f K)-P K := map_sub P _ _
  have hw' : ⇑(P w) =ᵐ[μ] fun a => P (T f K) a - P K a := by
    rw [hw]; exact Lp.coeFn_sub _ _
  filter_upwards [hw',hT f K,hT h w] with a ha hb hc
  rw [←eqw] at hc
  rw [ha,hb] at hc
  linear_combination hc

private theorem sea_separated_hop_patch {Config : Type*} [MeasurableSpace Config] (μ : Measure Config)
    (x y : Config → Spatial) (K : Config → ℂ) (hnz : ¬∀ᵐ a ∂μ, x a ≠ y a → K a = 0) :
    ∃ (x₀ y₀ : Spatial) (r : ℝ), 0 < r ∧ 4*r < dist x₀ y₀ ∧
      ¬∀ᵐ a ∂μ, x a ∈ closedBall x₀ r → y a ∈ closedBall y₀ r → K a = 0 := by
  let S : Set (Spatial × Spatial) := {z | z.1 ≠ z.2}
  let r (z : S) := dist z.val.1 z.val.2/5
  let W (z : S) := ball z.val.1 (r z) ×ˢ ball z.val.2 (r z)
  have hpos (z : S) : 0 < r z := div_pos (dist_pos.mpr z.property) (by norm_num)
  have hc : S ⊆ ⋃ z, W z := by
    intro a ha
    apply mem_iUnion.mpr
    exact ⟨⟨a,ha⟩,mem_ball_self (hpos _),mem_ball_self (hpos _)⟩
  obtain ⟨D,hD,hcover⟩ := (HereditarilyLindelof_LindelofSets S).elim_countable_subcover W
    (fun _ => isOpen_ball.prod isOpen_ball) hc
  by_contra! hall
  apply hnz
  have he (z : S) : ∀ᵐ a ∂μ, x a ∈ closedBall z.val.1 (r z) →
      y a ∈ closedBall z.val.2 (r z) → K a = 0 := by
    apply hall _ _ _ (hpos z)
    dsimp only [r]; linarith [dist_pos.mpr z.property]
  filter_upwards [(ae_ball_iff hD).2 (fun z _ => he z)] with a ha
  intro hxy
  have hw := hcover (show (x a,y a) ∈ S from hxy)
  obtain ⟨z,hz,hmem⟩ := mem_iUnion₂.mp hw
  exact ha z hz (ball_subset_closedBall hmem.1) (ball_subset_closedBall hmem.2)

/-- A nonzero occupied-to-empty Hamiltonian kernel between separated spatial
balls forces a violation of local commutation. The maps `x` and `y` retain the
particle and hole positions even when the pair sector also has spin or normal
coordinates. The localized tests are smooth and compactly supported and the
theorem gives their positive separation explicitly. -/
theorem sea_hopping_violates_locality {Config : Type*} [MeasurableSpace Config] (μ : Measure Config)
    (x y : Config → Spatial) (P : E →L[ℂ] Lp ℂ 2 μ) (T : (Spatial → ℝ) → E →L[ℂ] E)
    (V : ℝ → E ≃ₗᵢ[ℂ] E) (vzero : ∀ w, V 0 w = w) (vinv : ∀ t w, V t (V (-t) w) = w)
    (vcont : ∀ w, ContinuousAt (fun t => V t w) 0)
    (Ω K : E) (hK : HasDerivAt (fun t => V (-t) Ω) ((-Complex.I) • K) 0)
    (hΩ : ∀ f, T f Ω = Ω)
    (hT : ∀ f w, ∀ᵐ a ∂μ, P (T f w) a = seaOccupationPhase f (x a) (y a) * P w a)
    (hoff : ¬ ∀ᵐ a ∂μ, x a ≠ y a → P K a = 0) :
    ∃ (f h : Spatial → ℝ) (d : ℝ), 0 < d ∧ ContDiff ℝ ∞ f ∧ ContDiff ℝ ∞ h ∧
      HasCompactSupport f ∧ HasCompactSupport h ∧
      (∀ X ∈ tsupport f, ∀ Y ∈ tsupport h, d ≤ dist X Y) ∧
      ¬ ∀ᶠ t in 𝓝 0, V t (T f (V (-t) (T h Ω))) = T h (V t (T f (V (-t) Ω))) := by
  obtain ⟨x₀,y₀,r,hr,hsep,hnz⟩ := sea_separated_hop_patch μ x y (P K) hoff
  let f (z : Spatial) := Real.pi * seaLocationBump x₀ r hr z
  let h (z : Spatial) := Real.pi * seaLocationBump y₀ r hr z
  have hsup (z₀ : Spatial) : tsupport (fun z => Real.pi * seaLocationBump z₀ r hr z) ⊆ closedBall z₀ (2*r) := by
    have hs : tsupport ((fun _ : Spatial => Real.pi) * ⇑(seaLocationBump z₀ r hr)) ⊆ _ := tsupport_mul_subset_right
    exact hs.trans (seaLocationBump z₀ r hr).tsupport_eq.subset
  refine ⟨f,h,dist x₀ y₀-4*r,sub_pos.mpr hsep,contDiff_const.mul (seaLocationBump _ _ _).contDiff,
    contDiff_const.mul (seaLocationBump _ _ _).contDiff,
    HasCompactSupport.mul_left (seaLocationBump x₀ r hr).hasCompactSupport,
    HasCompactSupport.mul_left (seaLocationBump y₀ r hr).hasCompactSupport,?_,?_⟩
  · intro X hX Y hY
    have hx := (hsup x₀ hX : dist X x₀ ≤ 2*r)
    have hy := (hsup y₀ hY : dist Y y₀ ≤ 2*r)
    change dist X x₀ ≤ 2*r at hx
    change dist Y y₀ ≤ 2*r at hy
    linarith [dist_triangle x₀ X y₀,dist_triangle X Y y₀,dist_comm x₀ X]
  · intro hloc
    have hz := sea_locality_forces_zero V vzero vinv vcont Ω K hK (T f) (T h) (hΩ f) (hΩ h) hloc
    apply hnz
    filter_upwards [sea_pair_phase_product x y P T hT f h K hz] with a ha
    intro hx hy
    have hxx := (seaLocationBump x₀ r hr).one_of_mem_closedBall hx
    have hyy := (seaLocationBump y₀ r hr).one_of_mem_closedBall hy
    have hxy : 2*r ≤ dist (y a) x₀ := by
      have h' : dist (y a) y₀ ≤ r := hy
      linarith [dist_triangle x₀ (y a) y₀,dist_comm x₀ (y a)]
    have hyx : 2*r ≤ dist (x a) y₀ := by
      have h' : dist (x a) x₀ ≤ r := hx
      linarith [dist_triangle x₀ (x a) y₀,dist_comm x₀ (x a)]
    simp [seaOccupationPhase,f,h,hxx,hyy,(seaLocationBump x₀ r hr).zero_of_le_dist hxy,
      (seaLocationBump y₀ r hr).zero_of_le_dist hyx,Complex.exp_pi_mul_I,Complex.exp_neg] at ha
    exact ha.resolve_left (by norm_num)

end UV
