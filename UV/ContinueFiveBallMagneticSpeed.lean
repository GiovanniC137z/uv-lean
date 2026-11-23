import UV.ContinueNormalMaxwellModes
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! The positive magnetic square in the neutral count-two fibre.
Only the spatial norm of the selected carrier momentum enters the
speed estimate. The unit photon polarization and its orthogonal
complement are kept in the physical fibre throughout. -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology NNReal

namespace UV

/-- Expected magnetic smearing for a probability law of nonnegative
normal widths. No strictly positive lower bound on the width is needed. -/
def magneticWidthLaplace (μ : Measure ℝ≥0) (p : ℝ) : ℝ :=
  ∫ a, Real.exp (-(a:ℝ)*p) ∂μ

theorem magnetic_width_soft_limit (μ : Measure ℝ≥0) [IsProbabilityMeasure μ] :
    Tendsto (magneticWidthLaplace μ) (𝓝[>] 0) (𝓝 1) := by
  have h := tendsto_integral_filter_of_dominated_convergence (l := 𝓝[>] (0:ℝ))
    (F := fun p (a:ℝ≥0) => Real.exp (-(a:ℝ)*p)) (f := fun _ => (1:ℝ)) (μ := μ) (fun _ => (1:ℝ))
    (Eventually.of_forall fun _ => by fun_prop) ?_ (integrable_const _)
    (Eventually.of_forall fun a => ?_)
  · unfold magneticWidthLaplace
    simpa only [integral_const,measureReal_univ_eq_one,one_smul] using h
  · filter_upwards [self_mem_nhdsWithin] with p hp
    exact Eventually.of_forall fun a => by
      rw [Real.norm_of_nonneg (Real.exp_pos _).le,Real.exp_le_one_iff]
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr a.property) (le_of_lt hp)
  · have h' : Continuous (fun p:ℝ => Real.exp (-(a:ℝ)*p)) := by fun_prop
    simpa only [mul_zero,Real.exp_zero] using h'.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0) (a := (0:ℝ)))

def magneticSingularValue (μ : Measure ℝ≥0) (L p : ℝ) :=
  Real.sqrt p / (Real.sqrt 2*L) * magneticWidthLaplace μ p

theorem magnetic_singular_square (μ : Measure ℝ≥0) (L p : ℝ) (hp : 0 < p) :
    magneticSingularValue μ L p ^ 2 / p = magneticWidthLaplace μ p ^ 2 / (2*L^2) := by
  rw [magneticSingularValue,mul_pow,div_pow,mul_pow,Real.sq_sqrt hp.le,Real.sq_sqrt (by norm_num : 0 ≤ (2:ℝ))]
  field_simp [hp.ne']

/-- Completing the square on the gapped orthogonal component, retaining
the positive part from the triangle inequality for the magnetic row. -/
theorem magnetic_minimize_row {a κ K t s : ℝ} (ha : 0 < a) (hκ : 0 < κ)
    (ht : 0 ≤ t) :
    κ*a/(a+κ*K^2)*t^2 ≤ a*s^2+κ*(max (t-K*s) 0)^2 := by
  have hden : 0 < a+κ*K^2 := by positivity
  rw [div_mul_eq_mul_div,div_le_iff₀ hden]
  by_cases h : K*s ≤ t
  · rw [max_eq_left (by linarith)]
    nlinarith [sq_nonneg ((a+κ*K^2)*s-κ*K*t)]
  · rw [max_eq_right (by linarith)]
    have hsq := pow_le_pow_left₀ ht (le_of_not_ge h) 2
    nlinarith [mul_nonneg ha.le (sq_nonneg s),mul_le_mul_of_nonneg_left hsq (mul_nonneg hκ.le ha.le),sq_nonneg (a*s)]

/-- Fibre form estimate from the actual bounded annihilation row on a
normalized vector v=u+w. The transverse singular value is specified on
the bare component u and the gap acts on its orthogonal complement w. -/
theorem magnetic_fibre_speed {H F : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (B : H →L[ℂ] F) (u w : H) {E p d κ K b : ℝ} (hp : p < d) (hκ : 0 < κ)
    (hK : ‖B‖ ≤ K) (hb : 0 ≤ b) (hsing : ‖B u‖ = b*‖u‖)
    (hunit : ‖u‖^2+‖w‖^2 = 1)
    (hform : p*‖u‖^2+d*‖w‖^2+κ*‖B (u+w)‖^2 ≤ E) :
    κ*(d-p)/(d-p+κ*K^2)*b^2*‖u‖^2 ≤ E-p := by
  have hBw := (B.le_opNorm w).trans (mul_le_mul_of_nonneg_right hK (norm_nonneg w))
  have hBu : ‖B u‖ ≤ ‖B (u+w)‖+‖B w‖ := by
    simpa only [map_add,add_sub_cancel_right] using norm_sub_le (B (u+w)) (B w)
  have hrow : max (b*‖u‖-K*‖w‖) 0 ≤ ‖B (u+w)‖ := max_le (by linarith) (norm_nonneg _)
  have hm := magnetic_minimize_row (K := K) (s := ‖w‖) (sub_pos.mpr hp) hκ (mul_nonneg hb (norm_nonneg u))
  rw [mul_pow] at hm
  calc _ = κ*(d-p)/(d-p+κ*K^2)*(b^2*‖u‖^2) := by ring
       _ ≤ (d-p)*‖w‖^2+κ*(max (b*‖u‖-K*‖w‖) 0)^2 := hm
       _ ≤ (d-p)*‖w‖^2+κ*‖B (u+w)‖^2 := by gcongr
       _ ≤ E-p := by linarith [congrArg (p*·) hunit]

/-- On every (possibly essential) soft-momentum filter the two low
branches obey the manuscript's quantitative strictly positive speed
shift. Neither eigenvector continuity nor differentiation of a branch
is required. The data are the projected annihilation row, its bare
singular value, the form domination by the positive square, and the
bare-photon variational upper bound. -/
theorem magnetic_low_pole_speed {X H F : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    [NormedAddCommGroup F] [NormedSpace ℂ F] (l : Filter X) [NeBot l]
    (μ : Measure ℝ≥0) [IsProbabilityMeasure μ] {κ d L K : ℝ} (hκ : 0 < κ) (hd : 0 < d) (hL : 0 < L)
    (p E : X → ℝ) (B : X → H →L[ℂ] F) (u w : X → H) (hp : Tendsto p l (𝓝[>] 0))
    (hrow : ∀ᶠ x in l, ‖B x‖ ≤ K ∧ ‖B x (u x)‖ = magneticSingularValue μ L (p x)*‖u x‖)
    (hunit : ∀ᶠ x in l, ‖u x‖^2+‖w x‖^2=1)
    (hform : ∀ᶠ x in l, p x*‖u x‖^2+d*‖w x‖^2+κ*‖B x (u x+w x)‖^2 ≤ E x)
    (htrial : ∀ᶠ x in l, E x ≤ (1+κ/(2*L^2))*p x) :
    0 < κ*d/(2*L^2*(d+κ*K^2)) ∧
    κ*d/(2*L^2*(d+κ*K^2)) ≤ liminf (fun x => E x/p x-1) l := by
  have hdK : 0 < d+κ*K^2 := by positivity
  let A := 1+κ/(2*L^2)
  have hpos : ∀ᶠ x in l, 0 < p x := hp.eventually self_mem_nhdsWithin
  have hp0 := tendsto_nhdsWithin_iff.mp hp |>.1
  have hpd : ∀ᶠ x in l, p x < d := hp0.eventually (gt_mem_nhds hd)
  have hU0 : Tendsto (fun x => ‖w x‖^2) l (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun _ => sq_nonneg _) ?_ (by simpa only [mul_zero,zero_div] using (hp0.const_mul A).div_const d)
    filter_upwards [hpos,hform,htrial] with x hx hf ht
    rw [le_div_iff₀ hd]
    linarith [mul_nonneg hx.le (sq_nonneg ‖u x‖),mul_nonneg hκ.le (sq_nonneg ‖B x (u x+w x)‖)]
  have hU : Tendsto (fun x => ‖u x‖^2) l (𝓝 1) := by
    have hlim : Tendsto (fun x => 1-‖w x‖^2) l (𝓝 1) := by simpa using hU0.const_sub 1
    apply hlim.congr'
    filter_upwards [hunit] with x hx using by linarith
  let S := fun x => κ*(d-p x)/(d-p x+κ*K^2)
  let M := fun x => magneticWidthLaplace μ (p x)^2/(2*L^2)
  have hS : Tendsto S l (𝓝 (κ*d/(d+κ*K^2))) := by
    simpa only [S,sub_zero] using ((hp0.const_sub d).const_mul κ).div ((hp0.const_sub d).add_const (κ*K^2)) (by simpa using hdK.ne')
  have hM : Tendsto M l (𝓝 (1/(2*L^2))) := by
    simpa only [M,one_pow] using ((((magnetic_width_soft_limit μ).comp hp).pow 2).div_const (2*L^2))
  have hlim : Tendsto (fun x => S x * M x * ‖u x‖^2) l (𝓝 (κ*d/(2*L^2*(d+κ*K^2)))) := by
    convert (hS.mul hM).mul hU using 2
    rw [mul_one]
    field_simp
  have hlev : ∀ᶠ x in l, S x * M x * ‖u x‖^2 ≤ E x/p x-1 := by
    filter_upwards [hpos,hpd,hrow,hform,hunit] with x hx hpd' hr hf hu
    have hbn : 0 ≤ magneticSingularValue μ L (p x) := by
      unfold magneticSingularValue magneticWidthLaplace
      exact mul_nonneg (div_nonneg (Real.sqrt_nonneg _) (by positivity)) (integral_nonneg fun _ => (Real.exp_pos _).le)
    have h := magnetic_fibre_speed (B x) (u x) (w x) hpd' hκ hr.1 hbn hr.2 hu hf
    change S x * magneticSingularValue μ L (p x)^2 * ‖u x‖^2 ≤ E x-p x at h
    dsimp only [M]
    rw [←magnetic_singular_square μ L (p x) hx]
    rw [show E x/p x-1 = (E x-p x)/p x by field_simp]
    apply (div_le_div_of_nonneg_right h hx.le).trans_eq' (by ring)
  have hcb : l.IsCoboundedUnder (· ≥ ·) (fun x => E x/p x-1) := by
    apply isCoboundedUnder_ge_of_eventually_le l (x := A-1)
    filter_upwards [hpos,htrial] with x hx ht
    exact sub_le_sub_right ((div_le_iff₀ hx).mpr ht) _
  have hLB : 0 < κ*d/(2*L^2*(d+κ*K^2)) := by positivity
  have hfloor : ∀ᶠ x in l, (0:ℝ) ≤ E x/p x-1 := ((hlim.eventually (lt_mem_nhds hLB)).and hlev).mono fun _ h => h.1.le.trans h.2
  refine ⟨hLB,(le_liminf_iff hcb ⟨0,hfloor⟩).mpr fun y hy => ?_⟩
  exact ((hlim.eventually (lt_mem_nhds hy)).and hlev).mono fun _ h => h.1.trans_le h.2

end UV
