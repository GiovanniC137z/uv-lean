import UV.StableMomentThreshold

/-! Positive spectral sewing and the integrability obstruction for finite
dilation combinations. -/

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace UV.RevisionSpectrum

/-- A positive compact spectral band gives a strictly positive constant
lower bound on the unsubtracted transverse response at high momentum. -/
theorem positive_band_unsubtracted_lower (ρ : Measure ℝ)
    (hs : ∀ᵐ s ∂ρ, 0 ≤ s) {s₀ s₁ X : ℝ}
    (hX : 0 < X) (hb : s₁ ≤ X)
    (hmass : ρ (Icc s₀ s₁) ≠ ⊤)
    (hInt : Integrable (fun s => X/(s+X)) ρ) :
    ρ.real (Icc s₀ s₁) / 2 ≤ ∫ s, X/(s+X) ∂ρ := by
  let B := Icc s₀ s₁
  have hi : Integrable (B.indicator fun _ => (1:ℝ)/2) ρ :=
    (integrable_indicator_iff measurableSet_Icc).mpr (integrableOn_const hmass)
  have hm := integral_mono_ae hi hInt (by
    filter_upwards [hs] with s hsp
    have hd := add_pos_of_nonneg_of_pos hsp hX
    by_cases h : s ∈ B
    · rw [indicator_of_mem h]
      rw [le_div_iff₀ hd]
      linarith [h.2.trans hb]
    · rw [indicator_of_notMem h]
      positivity)
  rw [integral_indicator measurableSet_Icc, setIntegral_const, smul_eq_mul] at hm
  simpa [B, div_eq_mul_inv] using hm

/-- An unsubtracted positive band makes this complete radial contraction
nonintegrable on every sufficiently large half-line. -/
theorem positive_band_unsubtracted_sewing_diverges (ρ : Measure ℝ) (D : ℝ → ℝ)
    (hs : ∀ᵐ s ∂ρ, 0 ≤ s) {s₀ s₁ c R : ℝ}
    (hc : 0 < c) (hR : 0 < R) (hb : s₁ ≤ R)
    (hmass : ρ (Icc s₀ s₁) ≠ ⊤) (hpos : ρ (Icc s₀ s₁) ≠ 0)
    (hD : ∀ X ≥ R, c/X ≤ D X)
    (hInt : ∀ X ≥ R, Integrable (fun s => X/(s+X)) ρ) :
    ¬ IntegrableOn (fun X => X * D X * ∫ s, X/(s+X) ∂ρ) (Ioi R) := by
  let m := ρ.real (Icc s₀ s₁) / 2
  have hm : 0 < m := div_pos (ENNReal.toReal_pos hpos hmass) (by norm_num)
  intro hi
  have ci : IntegrableOn (fun _ : ℝ => c*m) (Ioi R) := by
    apply hi.mono' aestronglyMeasurable_const
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with X hX
    change R < X at hX
    have hX₀ := hR.trans hX
    have hK := positive_band_unsubtracted_lower ρ hs hX₀ (hb.trans hX.le) hmass (hInt X hX.le)
    have hxd : c ≤ X*D X := by
      have hd := (div_le_iff₀ hX₀).mp (hD X hX.le)
      linarith
    have hK₀ : 0 ≤ ∫ s, X/(s+X) ∂ρ := hm.le.trans hK
    rw [Real.norm_of_nonneg (mul_nonneg hc.le hm.le)]
    change c*m ≤ X*D X * ∫ s, X/(s+X) ∂ρ
    exact (mul_le_mul_of_nonneg_left hK hc.le).trans
      (mul_le_mul_of_nonneg_right hxd hK₀)
  have hp : (c*m) ≠ 0 := (mul_pos hc hm).ne'
  have hvol := (integrableOn_const_iff (μ := volume) (s := Ioi R) (C := c*m)).mp ci
  rcases hvol with hzero | hvol
  · exact hp (by simpa using hzero)
  · simp at hvol

/-- Positive massless-pole weight supplies the needed photon lower bound
for the positive spectral covariance, regardless of its other weights. -/
theorem atom_photon_lower (ρ : Measure ℝ) {z X : ℝ} (hX : 0 < X)
    (hs : ∀ᵐ s ∂ρ, 0 ≤ s) :
    z/X ≤ z/X + ∫ s, (X+s)⁻¹ ∂ρ := by
  apply le_add_of_nonneg_right
  apply integral_nonneg_of_ae
  filter_upwards [hs] with s hsp
  exact inv_nonneg.mpr (add_nonneg hX.le hsp)

/-- A lower bound by the inverse momentum variable on any finite dilation
combination is incompatible with integrability of the original response.
This is the implication used after killing polynomial contacts. -/
theorem finite_dilation_inverse_obstruction {ι : Type*} [Fintype ι]
    (K : ℝ → ℝ) (w scale : ι → ℝ) {R c : ℝ} (hR : 0 < R) (hc : 0 < c)
    (hs : ∀ j, 1 ≤ scale j)
    (hlower : ∀ X > R, c/X ≤ |∑ j, w j * K (scale j * X)|) :
    ¬ IntegrableOn K (Ioi R) := by
  intro hi
  have hsum : IntegrableOn (fun X => ∑ j, w j * K (scale j * X)) (Ioi R) := by
    apply integrable_finset_sum
    intro j _
    have hsj : 0 < scale j := zero_lt_one.trans_le (hs j)
    have hrle : R ≤ scale j * R := by nlinarith [mul_nonneg (sub_nonneg.mpr (hs j)) hR.le]
    have hm := hi.mono_set (Ioi_subset_Ioi hrle)
    exact ((integrableOn_Ioi_comp_mul_left_iff K R hsj).mpr hm).const_mul _
  have hinv : IntegrableOn (fun X : ℝ => X ^ (-(1:ℝ))) (Ioi R) := by
    have hdom : IntegrableOn (fun X => c⁻¹ * ‖∑ j, w j * K (scale j * X)‖) (Ioi R) :=
      hsum.norm.const_mul _
    apply hdom.mono' (by exact (measurable_id.pow_const _).aestronglyMeasurable)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with X hX
    change R < X at hX
    rw [Real.rpow_neg_one, Real.norm_of_nonneg (inv_nonneg.mpr (hR.trans hX).le),
      Real.norm_eq_abs, ← div_eq_inv_mul, le_div_iff₀ hc, inv_mul_eq_div]
    exact hlower X hX
  have h := (integrableOn_Ioi_rpow_iff hR).mp hinv
  norm_num at h

theorem radial_sewing_diverges {K D : ℝ → ℝ} {c R : ℝ} (hc : 0 < c) (hR : 0 < R)
    (hK : AEStronglyMeasurable K (volume.restrict (Ioi R)))
    (hD : ∀ X > R, c/X ≤ D X) (h : ¬ IntegrableOn K (Ioi R)) :
    ¬ IntegrableOn (fun X => X * D X * K X) (Ioi R) := by
  intro hi
  apply h
  apply (hi.norm.const_mul c⁻¹).mono' hK
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with X hX
  change R < X at hX
  have hp := hR.trans hX
  have hxd : c ≤ X*D X := by
    have h := (div_le_iff₀ hp).mp (hD X hX)
    linarith
  have ha : 0 ≤ X*D X := hc.le.trans hxd
  change ‖K X‖ ≤ c⁻¹ * ‖X*D X*K X‖
  rw [norm_mul, Real.norm_of_nonneg ha, ← div_eq_inv_mul, le_div_iff₀ hc]
  simpa only [mul_comm c] using mul_le_mul_of_nonneg_right hxd (norm_nonneg (K X))

/-- The alternating finite difference, oriented to make the reciprocal
kernel positive at every order. -/
def reciprocalDiff (h : ℝ) : ℕ → (ℝ → ℝ) → ℝ → ℝ
  | 0, f, x => f x
  | n+1, f, x => reciprocalDiff h n f x - reciprocalDiff h n f (x+h)

theorem reciprocalDiff_inv (s x h : ℝ) (hx : 0 < s+x) (hh : 0 ≤ h) (n : ℕ) :
    reciprocalDiff h n (fun y => (s+y)⁻¹) x =
      ((n.factorial : ℝ)*h^n) / ∏ j ∈ Finset.range (n+1), (s+x+(j:ℝ)*h) := by
  induction n generalizing x with
  | zero => simp [reciprocalDiff]
  | succ n ih =>
    have hx' : 0 < s+(x+h) := by linarith

    let P := ∏ j ∈ Finset.range n, (s+x+((j+1:ℕ):ℝ)*h)
    let L := s+x+((n+1:ℕ):ℝ)*h
    have eqShift (j : ℕ) : s+(x+h)+(j:ℝ)*h = s+x+((j+1:ℕ):ℝ)*h := by
      push_cast
      ring
    have first : (∏ j ∈ Finset.range (n+1), (s+x+(j:ℝ)*h)) = P*(s+x) := by
      rw [Finset.prod_range_succ']
      simp [P]
    have second : (∏ j ∈ Finset.range (n+1), (s+(x+h)+(j:ℝ)*h)) = P*L := by
      simp_rw [eqShift]
      rw [Finset.prod_range_succ]
    have third : (∏ j ∈ Finset.range (n+1+1), (s+x+(j:ℝ)*h)) = (P*(s+x))*L := by
      rw [Finset.prod_range_succ, first]
    rw [reciprocalDiff, ih x hx, ih (x+h) hx', first, second, third]
    have hL : 0 < L := by dsimp [L]; positivity
    have hP : P ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun j _ => by positivity)
    rw [Nat.factorial_succ, Nat.cast_mul, pow_succ]
    field_simp [hL.ne', hP, hx.ne']
    dsimp [L]
    push_cast
    ring

private theorem reciprocalDiff_affine (h c d : ℝ) (f : ℝ → ℝ) (n : ℕ) (x : ℝ) :
    reciprocalDiff h (n+1) (fun y => c+d*f y) x = d * reciprocalDiff h (n+1) f x := by
  induction n generalizing x with
  | zero => simp only [reciprocalDiff]; ring
  | succ n ih =>
    change reciprocalDiff h (n+1) (fun y => c+d*f y) x -
      reciprocalDiff h (n+1) (fun y => c+d*f y) (x+h) =
      d * (reciprocalDiff h (n+1) f x - reciprocalDiff h (n+1) f (x+h))
    rw [ih x, ih (x+h)]
    ring

/-- Exact same-sign spectral kernel after a positive order finite difference. -/
theorem reciprocalDiff_transverse (s x h : ℝ) (hs : 0 ≤ s) (hx : 0 < x)
    (hh : 0 ≤ h) (n : ℕ) :
    |reciprocalDiff h (n+1) (fun y => y/(s+y)) x| =
      ((n+1).factorial * s * h^(n+1)) / ∏ j ∈ Finset.range (n+1+1), (s+x+(j:ℝ)*h) := by
  have hcongr (k : ℕ) (z : ℝ) (hz : 0 < z) :
      reciprocalDiff h k (fun y => y/(s+y)) z =
      reciprocalDiff h k (fun y => 1 + (-s)*(s+y)⁻¹) z := by
    induction k generalizing z with
    | zero =>
      simp only [reciprocalDiff]
      have hz' : 0 < s+z := by positivity
      field_simp [hz'.ne']
      ring
    | succ k ih =>
      simp only [reciprocalDiff]
      rw [ih z hz, ih (z+h) (by linarith)]
  rw [hcongr (n+1) x hx, reciprocalDiff_affine,
    reciprocalDiff_inv s x h (by positivity) hh, abs_mul, abs_neg, abs_of_nonneg hs,
    abs_of_nonneg (by positivity)]
  ring

theorem reciprocalDiff_dilations_integrable {K : ℝ → ℝ} {R : ℝ}
    (hR : 0 < R) (hK : IntegrableOn K (Ioi R)) (n : ℕ) (k : ℝ) (hk : 1 ≤ k) :
    IntegrableOn (fun X => reciprocalDiff X n K (k*X)) (Ioi R) := by
  induction n generalizing k with
  | zero =>
    have hk₀ := zero_lt_one.trans_le hk
    have hle : R ≤ k*R := by nlinarith [mul_nonneg (sub_nonneg.mpr hk) hR.le]
    exact (integrableOn_Ioi_comp_mul_left_iff K R hk₀).mpr (hK.mono_set (Ioi_subset_Ioi hle))
  | succ n ih =>
    have hl : 1 ≤ k+1 := by linarith
    have hi := (ih k hk).sub (ih (k+1) hl)
    simpa only [reciprocalDiff, add_mul, one_mul, Pi.sub_apply] using hi

theorem finite_difference_sewing_diverges {K D : ℝ → ℝ} {c d R : ℝ}
    (hc : 0 < c) (hd : 0 < d) (hR : 0 < R)
    (hK : AEStronglyMeasurable K (volume.restrict (Ioi R)))
    (hD : ∀ X > R, c/X ≤ D X) (n : ℕ)
    (hlower : ∀ X > R, d/X ≤ |reciprocalDiff X n K X|) :
    ¬ IntegrableOn (fun X => X * D X * K X) (Ioi R) := by
  apply radial_sewing_diverges hc hR hK hD
  intro hi
  have hsum := reciprocalDiff_dilations_integrable hR hi n 1 le_rfl
  have hdom : IntegrableOn (fun X => d⁻¹ * ‖reciprocalDiff X n K X‖) (Ioi R) := by
    simpa only [one_mul] using hsum.norm.const_mul d⁻¹
  have hinv : IntegrableOn (fun X : ℝ => X ^ (-(1:ℝ))) (Ioi R) := by
    apply hdom.mono' ((measurable_id.pow_const _).aestronglyMeasurable)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with X hX
    change R < X at hX
    change ‖X ^ (-(1:ℝ))‖ ≤ d⁻¹ * ‖reciprocalDiff X n K X‖
    rw [Real.rpow_neg_one, Real.norm_of_nonneg (inv_nonneg.mpr (hR.trans hX).le),
      Real.norm_eq_abs, ← div_eq_inv_mul, le_div_iff₀ hd, inv_mul_eq_div]
    exact hlower X hX
  have h := (integrableOn_Ioi_rpow_iff hR).mp hinv
  norm_num at h

end UV.RevisionSpectrum
