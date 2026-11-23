import UV.ResumeCollarSpectral
import UV.ContinueTemporalMaximum

/-! Pointwise decay of quartic-collar eigenmodes, derived from their
one-dimensional differential equation and their Dirichlet endpoint trace.
The comparison function has an exact second derivative. -/

noncomputable section

open Real Set Filter MeasureTheory
open scoped Topology

namespace UV.CollarEigenmode

def potential (j r : ℝ) := 2/r^2+j^2/r^8

/-- An unnormalized recessive solution for the auxiliary barrier with
squared angular coefficient 9 c². The r² prefactor gives its tip value. -/
def barrier (c r : ℝ) := r^2 * exp (-c/r^3)

theorem barrier_pos {c r : ℝ} (hr : 0 < r) : 0 < barrier c r := mul_pos (sq_pos_of_pos hr) (exp_pos _)

theorem barrier_gradient (c : ℝ) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (barrier c) ((2*r+3*c/r^2)*exp (-c/r^3)) r := by
  have hp := ((hasDerivAt_const r (-c)).div ((hasDerivAt_id r).pow 3) (pow_ne_zero 3 hr.ne')).exp
  convert ((hasDerivAt_id r).pow 2).mul hp using 1
  simp only [Pi.pow_apply, Pi.div_apply,id_eq]
  field_simp; ring

theorem barrier_laplacian (c : ℝ) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun x => (2*x+3*c/x^2)*exp (-c/x^3)) (potential (3*c) r * barrier c r) r := by
  have hp := ((hasDerivAt_const r (-c)).div ((hasDerivAt_id r).pow 3) (pow_ne_zero 3 hr.ne')).exp
  have hg := ((hasDerivAt_id r).const_mul 2).add ((hasDerivAt_const r (3*c)).div ((hasDerivAt_id r).pow 2) (pow_ne_zero 2 hr.ne'))
  convert hg.mul hp using 1
  simp only [id_eq,Pi.pow_apply,Pi.div_apply,Pi.add_apply,potential,barrier]
  field_simp; ring

theorem barrier_continuous {c h : ℝ} (hc : 0 < c) : ContinuousOn (barrier c) (Icc 0 h) := by
  intro r hr
  rcases lt_or_eq_of_le hr.1 with h | h
  · exact (barrier_gradient c h).continuousAt.continuousWithinAt
  · subst r
    have hz : barrier c 0 = 0 := by simp [barrier]
    rw [ContinuousWithinAt,hz]
    apply squeeze_zero' (Eventually.of_forall fun t => mul_nonneg (sq_nonneg t) (exp_pos _).le)
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact mul_le_of_le_one_right (sq_nonneg t) (exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc.le) (pow_nonneg ht.1 3)))
    · simpa using ((continuous_id.pow 2).continuousAt (x := (0:ℝ))).continuousWithinAt (s := Icc 0 h) |>.tendsto

private theorem scalar_barrier_principle {h : ℝ} (f g : ℝ → ℝ)
    (hc : ContinuousOn f (Icc 0 h)) (h₀ : 0 ≤ f 0) (h₁ : 0 ≤ f h)
    (hd : ∀ x ∈ Ioo 0 h,HasDerivAt f (g x) x) (hg : ∀ x ∈ Ioo 0 h, f x < 0 → ∃ z, z < 0 ∧ HasDerivAt g z x) :
    ∀ r ∈ Icc 0 h,0 ≤ f r := by
  intro r hr
  by_contra! hneg
  obtain ⟨x,hx,hmin⟩ := isCompact_Icc.exists_isMinOn ⟨r,hr⟩ hc
  have hn : f x < 0 := (hmin hr).trans_lt hneg
  have hxl : 0 < x := lt_of_le_of_ne hx.1 fun he => by rw [←he] at hn; linarith
  have hxr : x < h := lt_of_le_of_ne hx.2 fun he => by rw [he] at hn; linarith
  have hxx := Icc_mem_nhds hxl hxr
  have hz := (hmin.isLocalMin hxx).hasDerivAt_eq_zero (hd x ⟨hxl,hxr⟩)
  have he := (hd x ⟨hxl,hxr⟩).continuousAt (Iio_mem_nhds hn)
  obtain ⟨ε,hε,hε'⟩ := Metric.mem_nhds_iff.mp he
  let b := min (x+ε/2) ((x+h)/2)
  have hxb : x < b := lt_min (by linarith) (by linarith)
  have hbh : b < h := (min_le_right ..).trans_lt (by linarith)
  have hwin {t : ℝ} (ht : t ∈ Icc x b) : t ∈ Ioo 0 h := ⟨hxl.trans_le ht.1,ht.2.trans_lt hbh⟩
  have hfn {t : ℝ} (ht : t ∈ Icc x b) : f t < 0 := by
    apply hε'
    rw [Metric.mem_ball,Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr ht.1)]
    linarith [ht.2.trans (min_le_left (x+ε/2) ((x+h)/2))]
  have hga : StrictAntiOn g (Icc x b) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc x b)
    · intro t ht
      obtain ⟨_,_,H⟩ := hg t (hwin ht) (hfn ht)
      exact H.continuousAt.continuousWithinAt
    · intro t ht
      have h := interior_subset ht
      obtain ⟨_,hb,H⟩ := hg t (hwin h) (hfn h)
      rwa [H.deriv]
  have hfa : StrictAntiOn f (Icc x b) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc x b) (hc.mono fun _ h => ⟨(hwin h).1.le,(hwin h).2.le⟩)
    intro t ht
    have ht' := interior_subset ht
    rw [(hd t (hwin ht')).deriv,←hz]
    exact hga ⟨le_rfl,hxb.le⟩ ht' (by rw [interior_Icc] at ht; exact ht.1)
  exact (hfa ⟨le_rfl,hxb.le⟩ ⟨hxb.le,le_rfl⟩ hxb).not_ge (hmin ⟨hxl.le.trans hxb.le,hbh.le⟩)

/-- Pointwise version of the collar Agmon bound. It is derived directly
from the radial ODE by comparison with r² exp(−c/r³). -/
theorem dirichlet_mode_bound {u g : ℝ → ℝ} {j E c h : ℝ} (hc : 0 < c) (hh : 0 < h) (hEn : 0 ≤ E)
    (hU : ContinuousOn u (Icc 0 h)) (hz : u 0 = 0)
    (hu : ∀ x ∈ Ioo 0 h,HasDerivAt u (g x) x)
    (hg : ∀ x ∈ Ioo 0 h,HasDerivAt g ((potential j x-E)*u x) x)
    (hE : E*h^8 ≤ j^2-(3*c)^2) :
    ∀ r ∈ Icc 0 h, |u r| ≤ (|u h|/barrier c h)*barrier c r := by
  let A := |u h|/barrier c h
  have hA : 0 ≤ A := div_nonneg (abs_nonneg _) (barrier_pos hh).le
  have bv := barrier_pos (c := c) hh
  have hb (r : ℝ) (hr : r ∈ Ioo 0 h) : potential (3*c) r ≤ potential j r - E := by
    have hpow := pow_le_pow_left₀ hr.1.le hr.2.le 8
    have hr' := pow_pos hr.1 8
    unfold potential
    have h' := (mul_le_mul_of_nonneg_left hpow hEn).trans hE
    linarith only [(le_div_iff₀ hr').mpr (show E*r^8 ≤ j^2-(3*c)^2 from h'),sub_div (j^2) ((3*c)^2) (r^8)]
  have hpos (r) (hr : r ∈ Ioo 0 h) : 0 < potential j r - E := by
    apply lt_of_lt_of_le _ (hb r hr)
    have hz := hr.1
    dsimp [potential]; positivity
  have hs (v v' : ℝ → ℝ) (hC : ContinuousOn v (Icc 0 h)) (h0 : v 0 = 0) (hhs : v h ≤ |u h|)
      (hv : ∀ x ∈ Ioo 0 h,HasDerivAt v (v' x) x) (hv' : ∀ x ∈ Ioo 0 h, HasDerivAt v' ((potential j x-E)*v x) x) :
      ∀ r ∈ Icc 0 h,v r ≤ A*barrier c r := by
    let f := fun r => A*barrier c r-v r
    let d := fun r => A*((2*r+3*c/r^2)*exp (-c/r^3))-v' r
    apply fun r hr => sub_nonneg.mp (scalar_barrier_principle f d
      ((continuousOn_const.mul (barrier_continuous hc)).sub hC)
      (by simp [f,barrier,h0]) (by simpa [f,A,div_mul_cancel₀ _ bv.ne'] using sub_nonneg.mpr hhs)
      (fun x hx => ((barrier_gradient c hx.1).const_mul A).sub (hv x hx)) ?_ r hr)
    intro x hx hn
    refine ⟨_,?_,((barrier_laplacian c hx.1).const_mul A).sub (hv' x hx)⟩
    have h' := mul_nonpos_of_nonneg_of_nonpos hA (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (hb x hx)) (barrier_pos (c := c) hx.1).le)
    have h'' := mul_neg_of_pos_of_neg (hpos x hx) hn
    dsimp [f] at h''
    linarith only [h',h'']
  intro r hr
  apply abs_le.mpr
  refine ⟨neg_le.mp (hs (fun x => -u x) (fun x => -g x) hU.neg (by simp [hz]) (neg_le_abs _) (fun x hx => (hu x hx).neg)
    (fun x hx => by simpa only [mul_neg] using (hg x hx).neg) r hr),hs u g hU hz (le_abs_self _) hu hg r hr⟩

end UV.CollarEigenmode
