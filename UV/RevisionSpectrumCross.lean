import UV.StableMomentThreshold

/-! Boundary calculations for the shifted square-root cross covariance.
The upper-half-plane square root is written in real coordinates to retain
the correct boundary at the negative-real cut. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology

namespace UV.RevisionSpectrum

def spectralRootUpper (p e : ℝ) : ℂ :=
  (Real.sqrt ((Real.sqrt (p^2+e^2)+p)/2) : ℂ) +
    (Real.sqrt ((Real.sqrt (p^2+e^2)-p)/2) : ℂ)*Complex.I

theorem spectralRootUpper_sq (p : ℝ) {e : ℝ} (he : 0 ≤ e) :
    spectralRootUpper p e ^ 2 = (p : ℂ) + (e : ℂ) * Complex.I := by
  let R := Real.sqrt (p^2+e^2)
  have hR₀ : 0 ≤ R := Real.sqrt_nonneg _
  have hR : R^2 = p^2+e^2 := Real.sq_sqrt (by positivity)
  have habs : |p| ≤ R := by apply (sq_le_sq₀ (abs_nonneg p) hR₀).mp; rw [sq_abs, hR]; linarith [sq_nonneg e]
  have hp₁ : 0 ≤ (R+p)/2 := by linarith [neg_abs_le p]
  have hp₂ : 0 ≤ (R-p)/2 := by linarith [le_abs_self p]
  let u := Real.sqrt ((R+p)/2)
  let v := Real.sqrt ((R-p)/2)
  have hu : u^2 = (R+p)/2 := Real.sq_sqrt hp₁
  have hv : v^2 = (R-p)/2 := Real.sq_sqrt hp₂
  have huv : 2*u*v = e := by
    have hsq : (2*u*v)^2 = e^2 := by
      calc
        _ = 4*u^2*v^2 := by ring
        _ = R^2-p^2 := by rw [hu, hv]; ring
        _ = _ := by rw [hR]; ring
    have hnonneg : 0 ≤ 2*u*v := by dsimp [u, v]; positivity
    exact le_antisymm ((sq_le_sq₀ hnonneg he).mp hsq.le)
      ((sq_le_sq₀ he hnonneg).mp hsq.ge)
  have hdiff : u*u-v*v = p := by nlinarith

  apply Complex.ext
  · change (((u:ℂ)+(v:ℂ)*Complex.I)^2).re = ((p:ℂ)+(e:ℂ)*Complex.I).re
    simp [pow_two, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, hdiff]
  · change (((u:ℂ)+(v:ℂ)*Complex.I)^2).im = ((p:ℂ)+(e:ℂ)*Complex.I).im
    simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero,
      mul_one, add_zero, zero_add, sub_zero]
    linarith

theorem spectralRootUpper_at_cut {p : ℝ} (hp : p ≤ 0) :
    spectralRootUpper p 0 = (Real.sqrt (-p) : ℂ) * Complex.I := by
  unfold spectralRootUpper
  rw [show p^2+(0:ℝ)^2 = p^2 by ring, Real.sqrt_sq_eq_abs, abs_of_nonpos hp]
  simp [show (-p-p)/2 = -p by ring]

theorem spectralRootUpper_at_nonneg {p : ℝ} (hp : 0 ≤ p) :
    spectralRootUpper p 0 = (Real.sqrt p : ℂ) := by
  unfold spectralRootUpper
  rw [show p^2+(0:ℝ)^2 = p^2 by ring, Real.sqrt_sq hp]
  simp [show (p+p)/2 = p by ring]

theorem spectralRootUpper_continuous (p : ℝ) :
    Continuous (spectralRootUpper p) := by unfold spectralRootUpper; fun_prop

def crossUpper (a M m₂ s e : ℝ) : ℂ :=
  Complex.exp ((a : ℂ) * ((M : ℂ) - spectralRootUpper (M^2-s) e)) /
    ((m₂-s : ℝ) + (e : ℂ)*Complex.I)

def crossDensity (a M m₂ s : ℝ) : ℝ :=
  if M^2 < s then Real.exp (a*M) * Real.sin (a*Real.sqrt (s-M^2)) /
    (Real.pi*(m₂-s)) else 0

theorem crossUpper_at_cut {a M m₂ s : ℝ} (hs : M^2 < s) :
    crossUpper a M m₂ s 0 =
      (Real.exp (a*M) : ℂ) * Complex.exp ((↑(-(a*Real.sqrt (s-M^2))) : ℂ) * Complex.I) /
        (↑(m₂-s) : ℂ) := by
  unfold crossUpper
  rw [spectralRootUpper_at_cut (sub_nonpos.mpr hs.le), show -(M^2-s) = s-M^2 by ring]
  have heq : (a:ℂ) * ((M:ℂ) -(↑(Real.sqrt (s-M^2)):ℂ)*Complex.I) =
      (↑(a*M):ℂ) + (↑(-(a*Real.sqrt (s-M^2))):ℂ)*Complex.I := by push_cast; ring
  rw [heq, Complex.exp_add, Complex.ofReal_exp]
  simp

theorem crossUpper_jump {a M m₂ s : ℝ} (hs : M^2 < s) :
    -(crossUpper a M m₂ s 0).im / Real.pi = crossDensity a M m₂ s := by
  rw [crossUpper_at_cut hs, crossDensity, if_pos hs]
  simp only [Complex.div_ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, add_zero, Complex.exp_ofReal_mul_I_im, Real.sin_neg, mul_neg, neg_div,
    neg_neg, div_div]
  ring

theorem crossUpper_tendsto {a M m₂ s : ℝ} (hm : m₂ ≠ s) :
    Tendsto (crossUpper a M m₂ s) (𝓝 0) (𝓝 (crossUpper a M m₂ s 0)) := by
  unfold crossUpper
  apply ContinuousAt.tendsto
  have hnum : Continuous (fun e => Complex.exp ((a:ℂ)*((M:ℂ)-spectralRootUpper (M^2-s) e))) :=
    Complex.continuous_exp.comp (continuous_const.mul
      (continuous_const.sub (spectralRootUpper_continuous _)))
  apply hnum.continuousAt.div (by fun_prop)
  simp [sub_eq_zero, hm]

/-- Candidate cut density has a removable embedded-pole value precisely in
the sine-zero case. This gives its actual one-sided and two-sided
punctured limits, including the sign and scale of the limiting density. -/
theorem crossDensity_embedded_limit {a M m₂ : ℝ} (hm : M^2 < m₂)
    (hzero : Real.sin (a*Real.sqrt (m₂-M^2)) = 0) :
    Tendsto (crossDensity a M m₂) (𝓝[≠] m₂)
      (𝓝 (-(Real.exp (a*M) * (a/(2*Real.sqrt (m₂-M^2))) *
        Real.cos (a*Real.sqrt (m₂-M^2))) / Real.pi)) := by
  let k := Real.sqrt (m₂-M^2)
  have hk : 0 < k := Real.sqrt_pos.mpr (sub_pos.mpr hm)
  have hd := ((Real.hasDerivAt_sqrt (sub_pos.mpr hm).ne').comp m₂
    ((hasDerivAt_id m₂).sub_const (M^2))).const_mul a
  have hsin := hasDerivAt_iff_tendsto_slope.mp hd.sin
  simp only [Function.comp_apply, id_eq, mul_one] at hsin
  have hconst : Tendsto (fun _ : ℝ => -Real.exp (a*M)/Real.pi) (𝓝[≠] m₂)
      (𝓝 (-Real.exp (a*M)/Real.pi)) := tendsto_const_nhds
  have hmul := hconst.mul hsin
  have hlim : -(Real.exp (a*M))/Real.pi *
      (Real.cos (a*Real.sqrt (m₂-M^2))*(a*(1/(2*Real.sqrt (m₂-M^2))))) =
        -(Real.exp (a*M) * (a/(2*Real.sqrt (m₂-M^2))) *
        Real.cos (a*Real.sqrt (m₂-M^2))) / Real.pi := by ring
  rw [hlim] at hmul
  apply hmul.congr'
  have ha : ∀ᶠ x in 𝓝[≠] m₂, M^2 < x :=
    mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hm)
  have hne : ∀ᶠ x in 𝓝[≠] m₂, x ≠ m₂ := self_mem_nhdsWithin
  filter_upwards [ha, hne] with x hx hneq
  have hd : m₂-x ≠ 0 := sub_ne_zero.mpr hneq.symm
  have hd' : x-m₂ ≠ 0 := sub_ne_zero.mpr hneq
  change -Real.exp (a*M)/Real.pi * slope (fun y => Real.sin (a*Real.sqrt (y-M^2))) m₂ x =
    crossDensity a M m₂ x
  rw [crossDensity, if_pos hx, slope, vsub_eq_sub, hzero, sub_zero, smul_eq_mul]
  field_simp [Real.pi_ne_zero, hd, hd']
  ring

/-- At threshold the continuum has the integrable inverse-square-root
strength and the displayed leading coefficient. -/
theorem crossDensity_threshold_limit (a M : ℝ) :
    Tendsto (fun s => Real.sqrt (s-M^2) * crossDensity a M (M^2) s)
      (𝓝[>] (M^2)) (𝓝 (-(a*Real.exp (a*M))/Real.pi)) := by
  have hsin : HasDerivAt (fun k : ℝ => Real.sin (a*k)) a 0 := by
    simpa using (((hasDerivAt_id (0:ℝ)).const_mul a).sin)
  have hratio := hasDerivAt_iff_tendsto_slope.mp hsin
  have hscont : Tendsto (fun s : ℝ => Real.sqrt (s-M^2))
      (𝓝[>] (M^2)) (𝓝 0) := by
    have h : Continuous (fun s : ℝ => Real.sqrt (s-M^2)) := by fun_prop
    have h' := h.continuousAt (x := M^2)
    simpa [ContinuousWithinAt] using h'.continuousWithinAt (s := Ioi (M^2))
  have hnonzero : ∀ᶠ s : ℝ in 𝓝[>] (M^2), Real.sqrt (s-M^2) ∈ ({0}:Set ℝ)ᶜ := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (Real.sqrt_pos.mpr (sub_pos.mpr hs)).ne'
  have hscont' := tendsto_nhdsWithin_iff.mpr ⟨hscont, hnonzero⟩
  have hl := hratio.comp hscont'
  have hconst : Tendsto (fun _ : ℝ => -Real.exp (a*M)/Real.pi) (𝓝[>] (M^2))
      (𝓝 (-Real.exp (a*M)/Real.pi)) := tendsto_const_nhds
  have hm := hconst.mul hl
  rw [show -Real.exp (a*M)/Real.pi*a = -(a*Real.exp (a*M))/Real.pi by ring] at hm
  apply hm.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  change M^2 < s at hs
  have hk : 0 < Real.sqrt (s-M^2) := Real.sqrt_pos.mpr (sub_pos.mpr hs)
  have hsq := Real.sq_sqrt (sub_nonneg.mpr hs.le)
  have hne : M^2-s ≠ 0 := sub_ne_zero.mpr hs.ne
  change -Real.exp (a*M)/Real.pi * slope (fun k : ℝ => Real.sin (a*k)) 0
      (Real.sqrt (s-M^2)) = Real.sqrt (s-M^2)*crossDensity a M (M^2) s
  rw [crossDensity, if_pos hs]
  simp only [slope, smul_eq_mul, vsub_eq_sub, mul_zero, Real.sin_zero, sub_zero]
  field_simp [Real.pi_ne_zero, hk.ne', hne]
  rw [show M^2-s = -(Real.sqrt (s-M^2))^2 by linarith]
  ring

/-- At a generic embedded pole the ordinary cut density cannot be locally
integrable. This certifies the failure of its candidate measure directly,
without treating the principal-value distribution as an ordinary function. -/
theorem crossDensity_embedded_nonintegrable {a M m₂ δ : ℝ}
    (hm : M^2 < m₂) (hδ : 0 < δ)
    (hzero : Real.sin (a*Real.sqrt (m₂-M^2)) ≠ 0) :
    ¬ IntegrableOn (crossDensity a M m₂) (Ioo m₂ (m₂+δ)) := by
  let f := fun s => |Real.sin (a*Real.sqrt (s-M^2))|
  let b := f m₂ / 2
  have hb : 0 < b := div_pos (abs_pos.mpr hzero) (by norm_num)
  have hfc : Continuous f := by unfold f; fun_prop
  have hball := Metric.tendsto_nhds_nhds.mp (hfc.continuousAt (x := m₂)).tendsto b hb
  obtain ⟨ε, hε, hlocal⟩ := hball
  let η := min δ ε
  have hη : 0 < η := lt_min hδ hε
  let c := Real.exp (a*M)*b/Real.pi
  have hc : 0 < c := by dsimp [c]; positivity
  intro hInt
  have hder : ∀ y ∈ Ioo (0:ℝ) η,
      HasDerivWithinAt (fun y => m₂+y) 1 (Ioo 0 η) y :=
    fun y _ => ((hasDerivAt_id y).const_add m₂).hasDerivWithinAt
  have hinj : InjOn (fun y : ℝ => m₂+y) (Ioo 0 η) :=
    fun _ _ _ _ h => add_left_cancel h
  have hImage : (fun y : ℝ => m₂+y) '' Ioo 0 η = Ioo m₂ (m₂+η) := by
    ext s
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
    · intro hs
      exact ⟨s-m₂, ⟨by linarith [hs.1], by linarith [hs.2]⟩, by ring⟩
  have hi := integrableOn_image_iff_integrableOn_abs_deriv_smul
    measurableSet_Ioo hder hinj (crossDensity a M m₂)
  rw [hImage] at hi
  have hle : Ioo m₂ (m₂+η) ⊆ Ioo m₂ (m₂+δ) :=
    Ioo_subset_Ioo le_rfl (add_le_add_left (min_le_left _ _) _)
  have hi' : IntegrableOn (fun y => crossDensity a M m₂ (m₂+y)) (Ioo 0 η) := by
    simpa using hi.mp (hInt.mono_set hle)
  have hir : IntegrableOn (fun y : ℝ => y^(-(1:ℝ))) (Ioo 0 η) := by
    have hdom : IntegrableOn (fun y => c⁻¹ * ‖crossDensity a M m₂ (m₂+y)‖) (Ioo 0 η) :=
      hi'.norm.const_mul _
    apply hdom.mono' (by exact (measurable_id.pow_const _).aestronglyMeasurable)
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
    have hya := hy.1
    have hyb : y < ε := hy.2.trans_le (min_le_right _ _)
    have hmf : M^2 < m₂+y := by linarith
    have hdist : dist (m₂+y) m₂ < ε := by
      rw [Real.dist_eq, show m₂+y-m₂ = y by ring, abs_of_pos hya]
      exact hyb
    have ht := hlocal hdist
    rw [Real.dist_eq, abs_lt] at ht
    have hfb : b ≤ f (m₂+y) := by dsimp [b] at ht ⊢; linarith [ht.1]
    rw [Real.rpow_neg_one, Real.norm_of_nonneg (inv_nonneg.mpr hya.le), crossDensity,
      if_pos hmf, Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos (Real.exp_pos _),
      abs_mul, abs_of_pos Real.pi_pos, show m₂-(m₂+y) = -y by ring, abs_neg, abs_of_pos hya,
      ← div_eq_inv_mul, le_div_iff₀ hc]
    change y⁻¹*c ≤ Real.exp (a*M)*f (m₂+y)/(Real.pi*y)
    rw [inv_mul_eq_div]
    dsimp [c]
    rw [div_div, div_le_div_iff_of_pos_right (mul_pos Real.pi_pos hya)]
    exact mul_le_mul_of_nonneg_left hfb (Real.exp_pos _).le
  have h := (intervalIntegral.integrableOn_Ioo_rpow_iff hη).mp hir
  norm_num at h

/-- The pole coefficient obtained by multiplying the upper covariance by
its pole denominator and then approaching the real axis from above. -/
theorem crossUpper_pole_limit (a M m₂ : ℝ) :
    Tendsto (fun e : ℝ => ((e : ℂ) * Complex.I) * crossUpper a M m₂ m₂ e)
      (𝓝[>] (0:ℝ))
      (𝓝 (Complex.exp ((a:ℂ)*((M:ℂ) - spectralRootUpper (M^2-m₂) 0)))) := by
  have hnum : Continuous (fun e => Complex.exp ((a:ℂ) *
      ((M:ℂ)-spectralRootUpper (M^2-m₂) e))) :=
    Complex.continuous_exp.comp
      (continuous_const.mul (continuous_const.sub (spectralRootUpper_continuous _)))
  apply ((hnum.continuousAt (x := 0)).continuousWithinAt (s := Ioi 0)).tendsto.congr'
  filter_upwards [self_mem_nhdsWithin] with e he
  have he0 : (e:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (mem_Ioi.mp he).ne'
  have hi0 : (e:ℂ)*Complex.I ≠ 0 := mul_ne_zero he0 Complex.I_ne_zero
  unfold crossUpper
  simp only [sub_self, Complex.ofReal_zero, zero_add]
  field_simp

theorem crossPoleCoeff_below {a M m₂ : ℝ} (hm : m₂ ≤ M^2) :
    Complex.exp ((a:ℂ)*((M:ℂ) - spectralRootUpper (M^2-m₂) 0)) =
      (Real.exp (a*(M-Real.sqrt (M^2-m₂))) : ℂ) := by
  rw [spectralRootUpper_at_nonneg (sub_nonneg.mpr hm), Complex.ofReal_exp]
  push_cast
  rfl

theorem crossPoleCoeff_above {a M m₂ : ℝ} (hm : M^2 < m₂) :
    let w := Complex.exp ((a:ℂ)*((M:ℂ) - spectralRootUpper (M^2-m₂) 0))
    w.re = Real.exp (a*M)*Real.cos (a*Real.sqrt (m₂-M^2)) ∧
    w.im = -(Real.exp (a*M)*Real.sin (a*Real.sqrt (m₂-M^2))) := by
  rw [spectralRootUpper_at_cut (sub_nonpos.mpr hm.le), show -(M^2-m₂) = m₂-M^2 by ring]
  have heq : (a:ℂ) * ((M:ℂ) -(↑(Real.sqrt (m₂-M^2)):ℂ)*Complex.I) =
      (↑(a*M):ℂ) + (↑(-(a*Real.sqrt (m₂-M^2))):ℂ)*Complex.I := by push_cast; ring
  rw [heq, Complex.exp_add, ← Complex.ofReal_exp]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.exp_ofReal_mul_I_im, Complex.exp_ofReal_mul_I_re, Real.cos_neg, Real.sin_neg,
    zero_mul, mul_neg, neg_zero, sub_zero, add_zero, and_self]

/-- The ordinary density has a uniform inverse-mass bound on the far tail,
which yields absolute Stieltjes integrability there. -/
theorem crossDensity_large_bound (a M m₂ s : ℝ) (hs : 0 < s)
    (hM : M^2 < s) (hm : 2*m₂ ≤ s) :
    |crossDensity a M m₂ s| ≤ (2*Real.exp (a*M)/Real.pi)/s := by
  unfold crossDensity
  rw [if_pos hM, abs_div, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _),
    abs_of_pos Real.pi_pos, abs_of_nonpos (show m₂-s ≤ 0 by linarith)]
  have hpos : 0 < Real.pi * -(m₂-s) := mul_pos Real.pi_pos (by linarith)
  have hs₁ : 0 < Real.pi*s := by positivity
  rw [div_div, div_le_div_iff₀ hpos hs₁]
  have hsin := Real.abs_sin_le_one (a*Real.sqrt (s-M^2))
  have hmain : |Real.sin (a*Real.sqrt (s-M^2))| * s ≤ 2 * -(m₂-s) := by
    calc
      _ ≤ s := by simpa using mul_le_mul_of_nonneg_right hsin hs.le
      _ ≤ _ := by linarith
  calc
    _ = (Real.exp (a*M)*Real.pi) * (|Real.sin (a*Real.sqrt (s-M^2))| * s) := by ring
    _ ≤ (Real.exp (a*M)*Real.pi) * (2 * -(m₂-s)) :=
      mul_le_mul_of_nonneg_left hmain (by positivity)
    _ = _ := by ring

end UV.RevisionSpectrum
