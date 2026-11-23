import UV.ContinueThinCurrent
import UV.ScalarTube
import Mathlib.Analysis.SpecificLimits.Normed

/-! The full four-dimensional current on a closed polygon of ordered
Wilson hops, including the uniform perimeter and soft-momentum bounds. -/

noncomputable section

open MeasureTheory Set Filter Finset
open scoped Topology RealInnerProductSpace

namespace UV

def wilsonCarrierInclusion : ThinCurrentPlane →ₗ[ℝ] EuclideanSpace ℂ (Fin 4) where
  toFun := fun x => WithLp.toLp 2 (complexifyMomentum x)
  map_add' x y := by ext k; simp [complexifyMomentum]
  map_smul' a x := by ext k; simp [complexifyMomentum]

theorem wilson_carrier_inclusion_norm (x : ThinCurrentPlane) : ‖wilsonCarrierInclusion x‖ = ‖x‖ := by
  have he : ‖wilsonCarrierInclusion x‖^2 = ‖x‖^2 := by
    rw [EuclideanSpace.norm_sq_eq,EuclideanSpace.norm_sq_eq]
    simp only [wilsonCarrierInclusion,LinearMap.coe_mk,AddHom.coe_mk,complexifyMomentum,
      PiLp.toLp_apply,Complex.norm_real]
  nlinarith [norm_nonneg (wilsonCarrierInclusion x),norm_nonneg x]

theorem wilson_plane_wave_soft (p x : ThinCurrentPlane) :
    ‖thinPlaneWave p x-1‖ ≤ ‖p‖*‖x‖ := by
  let a := (Complex.I*(⟪p,x⟫:ℂ))
  have hd (t : ℝ) : HasDerivAt (fun s : ℝ => Complex.exp (a*(s:ℂ))) (Complex.exp (a*(t:ℂ))*a) t := by
    simpa only [mul_one] using (((hasDerivAt_id (t:ℂ)).const_mul a).cexp).comp_ofReal
  have hb (t : ℝ) : ‖Complex.exp (a*(t:ℂ))*a‖ ≤ ‖p‖*‖x‖ := by
    have he : ‖Complex.exp (a*(t:ℂ))‖ = 1 := by simp [a,Complex.norm_exp,Complex.mul_re]
    rw [norm_mul,he,one_mul]
    simpa [a] using (abs_real_inner_le_norm p x)
  have hh := norm_image_sub_le_of_norm_deriv_le_segment_01' (fun t _ => (hd t).hasDerivWithinAt) (fun t _ => hb t)
  simpa only [Complex.ofReal_one,mul_one,Complex.ofReal_zero,mul_zero,Complex.exp_zero] using hh

def wilsonEdgeWave (p x d : ThinCurrentPlane) : ℂ :=
  ∫ t in (0:ℝ)..1, thinPlaneWave p (x+t • d)

private theorem wilson_edge_wave_continuous (p x d : ThinCurrentPlane) :
    Continuous (fun t : ℝ => thinPlaneWave p (x+t • d)) := by unfold thinPlaneWave; fun_prop

theorem wilson_edge_contraction (p x d : ThinCurrentPlane) :
    Complex.I*(⟪p,d⟫:ℂ)*wilsonEdgeWave p x d = thinPlaneWave p (x+d)-thinPlaneWave p x := by
  let a := Complex.I*(⟪p,d⟫:ℂ)
  have hphase : (fun t : ℝ => thinPlaneWave p (x+t • d)) =
      fun t : ℝ => Complex.exp (Complex.I*(⟪p,x⟫:ℂ)+(t:ℂ)*a) := by
    funext t
    unfold thinPlaneWave
    rw [inner_add_right,real_inner_smul_right]
    push_cast
    dsimp [a]
    ring_nf
  have hd (t : ℝ) : HasDerivAt (fun s : ℝ => thinPlaneWave p (x+s • d)) (a*thinPlaneWave p (x+t • d)) t := by
    rw [hphase,congrFun hphase t]
    simpa only [one_mul,mul_comm] using ((((hasDerivAt_id (t:ℂ)).mul_const a).const_add _).cexp).comp_ofReal
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
    ((continuous_const.mul (wilson_edge_wave_continuous p x d)).intervalIntegrable (μ := volume) 0 1)
  rw [intervalIntegral.integral_const_mul] at he
  simpa only [one_smul,zero_smul,add_zero] using he

def wilsonPolygonStart (d : ℕ → ThinCurrentPlane) (k : ℕ) := ∑ j ∈ range k, d j

def wilsonPerimeter (d : ℕ → ThinCurrentPlane) (N : ℕ) : ℝ := ∑ k ∈ range N, ‖d k‖

def wilsonPolygonCurrent (d : ℕ → ThinCurrentPlane) (N : ℕ) (p : ThinCurrentPlane) : EuclideanSpace ℂ (Fin 4) :=
  ∑ k ∈ range N, wilsonEdgeWave p (wilsonPolygonStart d k) (d k) • wilsonCarrierInclusion (d k)

theorem wilson_polygon_coordinate (d : ℕ → ThinCurrentPlane) (N : ℕ) (p : ThinCurrentPlane) (i : Fin 4) :
    wilsonPolygonCurrent d N p i = ∑ k ∈ range N, wilsonEdgeWave p (wilsonPolygonStart d k) (d k)*(d k i:ℂ) := by
  change (PiLp.projₗ (𝕜 := ℂ) 2 (fun _ : Fin 4 => ℂ) i) (∑ k ∈ range N, _) = _
  rw [map_sum]
  rfl

theorem wilson_polygon_transverse (d : ℕ → ThinCurrentPlane) (N : ℕ) (p : ThinCurrentPlane)
    (closed : wilsonPolygonStart d N = 0) :
    ∑ i : Fin 4, (p i:ℂ)*wilsonPolygonCurrent d N p i = 0 := by
  have he (k : ℕ) := wilson_edge_contraction p (wilsonPolygonStart d k) (d k)
  have hz : (∑ k ∈ range N, Complex.I*(⟪p,d k⟫:ℂ)*wilsonEdgeWave p (wilsonPolygonStart d k) (d k)) = 0 := by
    simp_rw [he]
    have hnext (k : ℕ) : wilsonPolygonStart d k+d k = wilsonPolygonStart d (k+1) := (sum_range_succ _ _).symm
    simp_rw [hnext]
    rw [sum_range_sub (fun k => thinPlaneWave p (wilsonPolygonStart d k)),closed]
    simp [wilsonPolygonStart]
  suffices h : Complex.I*(∑ i : Fin 4, (p i:ℂ)*wilsonPolygonCurrent d N p i) = 0 from
    (mul_eq_zero.mp h).resolve_left Complex.I_ne_zero
  rw [← hz]
  simp only [wilson_polygon_coordinate,Finset.mul_sum]
  rw [sum_comm]
  simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial,Complex.ofReal_sum,Complex.ofReal_mul,
    Finset.mul_sum,Finset.sum_mul]
  apply sum_congr rfl
  intro k _
  apply sum_congr rfl
  intro i _
  change _ = Complex.I * ((d k i:ℂ)*(p i:ℂ)) * _
  ring

theorem wilson_polygon_zero (d : ℕ → ThinCurrentPlane) (N : ℕ) (closed : wilsonPolygonStart d N = 0) :
    wilsonPolygonCurrent d N 0 = 0 := by
  have h (x y : ThinCurrentPlane) : wilsonEdgeWave 0 x y = 1 := by simp [wilsonEdgeWave,thinPlaneWave]
  simp only [wilsonPolygonCurrent,h,one_smul,←map_sum,show ∑ k ∈ range N, d k = 0 from closed,map_zero]

theorem wilson_polygon_perimeter_bound (d : ℕ → ThinCurrentPlane) (N : ℕ) (p : ThinCurrentPlane) :
    ‖wilsonPolygonCurrent d N p‖ ≤ wilsonPerimeter d N := by
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro k _
  have hm : ‖wilsonEdgeWave p (wilsonPolygonStart d k) (d k)‖ ≤ 1 := by
    apply (intervalIntegral.norm_integral_le_of_norm_le_const (C := 1) (fun t _ => ?_)).trans (by norm_num)
    simp [thinPlaneWave,Complex.norm_exp,Complex.mul_re]
  rw [norm_smul,wilson_carrier_inclusion_norm]
  exact mul_le_of_le_one_left (norm_nonneg _) hm

theorem wilson_polygon_soft_bound (d : ℕ → ThinCurrentPlane) (N : ℕ) (p : ThinCurrentPlane)
    (closed : wilsonPolygonStart d N = 0) :
    ‖wilsonPolygonCurrent d N p‖ ≤ ‖p‖*(wilsonPerimeter d N)^2 := by
  let P := wilsonPerimeter d N
  have hprefix {k : ℕ} (hk : k < N) :
      (∑ j ∈ range k, ‖d j‖) + ‖d k‖ ≤ P := by
    rw [←sum_range_succ]
    exact sum_le_sum_of_subset_of_nonneg (range_mono hk) (fun i _ _ => norm_nonneg (d i))
  have hpos (k : ℕ) (hk : k < N) (t : ℝ) (ht : t ∈ Ioc (0:ℝ) 1) :
      ‖wilsonPolygonStart d k+t • d k‖ ≤ P := by
    apply (norm_add_le _ _).trans
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg ht.1.le]
    exact (add_le_add (norm_sum_le _ _) (mul_le_of_le_one_left (norm_nonneg _) ht.2)).trans (hprefix hk)
  have hEdge (k : ℕ) (hk : k < N) : ‖wilsonEdgeWave p (wilsonPolygonStart d k) (d k)-1‖ ≤ ‖p‖*P := by
    let W := fun t : ℝ => thinPlaneWave p (wilsonPolygonStart d k+t • d k)
    have hW := (wilson_edge_wave_continuous p (wilsonPolygonStart d k) (d k)).intervalIntegrable (μ := volume) 0 1
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (f := fun t => W t-1) (a := 0) (b := 1)
      (C := ‖p‖*P) (fun t ht => (wilson_plane_wave_soft _ _).trans (mul_le_mul_of_nonneg_left
        (hpos k hk t (by simpa only [uIoc_of_le zero_le_one] using ht)) (norm_nonneg _)))
    have hconst := (continuous_const (y := (1:ℂ))).intervalIntegrable (μ := volume) (0:ℝ) 1
    rw [intervalIntegral.integral_sub (f := W) (g := fun _ : ℝ => (1:ℂ)) hW hconst] at h
    simpa [W,wilsonEdgeWave] using h
  have hc : ∑ k ∈ range N, wilsonCarrierInclusion (d k) = 0 := by rw [←map_sum,show ∑ k ∈ range N, d k = 0 from closed,map_zero]
  have he : wilsonPolygonCurrent d N p = ∑ k ∈ range N,
      (wilsonEdgeWave p (wilsonPolygonStart d k) (d k)-1) • wilsonCarrierInclusion (d k) := by
    simp only [sub_smul,one_smul,Finset.sum_sub_distrib,hc,sub_zero,wilsonPolygonCurrent]
  rw [he]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ k ∈ range N, (‖p‖*P)*‖d k‖ := by
      apply sum_le_sum
      intro k hk
      rw [norm_smul,wilson_carrier_inclusion_norm]
      exact mul_le_mul_of_nonneg_right (hEdge k (mem_range.mp hk)) (norm_nonneg _)
    _ = _ := by rw [←mul_sum]; change (‖p‖*P)*P = ‖p‖*P^2; ring

theorem wilson_polygon_shell_bound {L : ℝ} (d : ℕ → ThinCurrentPlane) (N : ℕ)
    (hd : ∀ k < N, ‖d k‖ ≤ 2*L) (closed : wilsonPolygonStart d N = 0) (p : ThinCurrentPlane) :
    ‖wilsonPolygonCurrent d N p‖ ≤ min (2*L*N) (‖p‖*(2*L*N)^2) := by
  have hP : wilsonPerimeter d N ≤ 2*L*N := by
    calc
      _ ≤ ∑ _k ∈ range N, 2*L := sum_le_sum (fun k hk => hd k (mem_range.mp hk))
      _ = _ := by simp [mul_comm]
  have hpos : 0 ≤ wilsonPerimeter d N := sum_nonneg (fun _ _ => norm_nonneg _)
  refine le_min ((wilson_polygon_perimeter_bound _ _ _).trans hP) ((wilson_polygon_soft_bound _ _ _ closed).trans ?_)
  gcongr

/-- Any fixed number of marked factors costs at most polynomial growth in
the number of hops. The specified hopping weight gives a summable bound. -/
theorem wilson_marked_hop_summable (a : ℕ) {lam : ℝ} (hlam : 0 ≤ lam) (hl : 2*lam < 1) :
    Summable (fun N : ℕ => (2*lam)^N*(1+(N:ℝ))^a) := by
  have h := summable_pow_mul_geometric_of_norm_lt_one a (r := 2*lam)
    (show ‖2*lam‖ < 1 by rwa [Real.norm_eq_abs,abs_of_nonneg (by positivity)])
  by_cases h0 : lam = 0
  · subst lam
    apply summable_of_ne_finset_zero (s := {0})
    intro n hn
    simp only [Finset.mem_singleton] at hn
    simp [zero_pow hn]
  · have hd : 2*lam ≠ 0 := mul_ne_zero (by norm_num) h0
    have hh := (summable_nat_add_iff 1).mpr h
    apply (hh.mul_left (2*lam)⁻¹).congr
    intro n
    simp only [Nat.cast_add,Nat.cast_one,pow_succ]
    field_simp
    ring

end UV
