import UV.ContinueTemporalStrip

/-! Exponential decay across a positive optical strip survives every
fixed finite order of the retained-endpoint time derivative. -/

noncomputable section

namespace UV.TemporalRay

open Set Real
open scoped Nat

/-- The physical length enters the attenuation rate through the
channel's actual optical length. -/
def NormalChannel.opticalStripRate (D : NormalChannel) (d r₁ r₂ : ℝ) : ℝ :=
  Real.sqrt d * (D.opticalCoordinate r₂ - D.opticalCoordinate r₁)

theorem NormalChannel.optical_strip_rate_pos (D : NormalChannel) {d r₁ r₂ : ℝ}
    (hd : 0 < d) (hr₁ : 0 ≤ r₁) (h₁₂ : r₁ < r₂) :
    0 < D.opticalStripRate d r₁ r₂ := by
  have hmax : 0 < D.aMax := D.aMin_pos.trans_le ((D.a_bound 0 le_rfl).1.trans (D.a_bound 0 le_rfl).2)
  exact mul_pos (Real.sqrt_pos.2 hd)
    ((div_pos (sub_pos.2 h₁₂) hmax).trans_le (D.optical_length_lower hr₁ h₁₂.le))

private theorem reciprocal_cosh_le_exp (x : ℝ) :
    1 / Real.cosh x ≤ 2 * Real.exp (-x) := by
  have h : Real.exp x / 2 ≤ Real.cosh x := by
    rw [Real.cosh_eq]
    linarith only [Real.exp_nonneg (-x)]
  exact (one_div_le_one_div_of_le (by positivity) h).trans_eq (by
    rw [Real.exp_neg]
    ring)

theorem normal_transfer_optical_strip_exponential (D : NormalChannel) (ω : ℝ)
    (u : NormalTransfer D.a (D.potential (ω ^ 2))) {r₁ r₂ r d : ℝ}
    (hr₁ : 0 ≤ r₁) (h₁₂ : r₁ ≤ r₂) (h₂r : r₂ ≤ r) (hd : 0 < d)
    (hstrip : ∀ s ∈ Icc r₁ r₂, d ≤ D.a s * D.temporal s) :
    u.amplitude r ≤ 2 * Real.exp (-(D.opticalStripRate d r₁ r₂ * |ω|)) := by
  refine (normal_transfer_optical_strip D ω u hr₁ h₁₂ h₂r hd hstrip).trans ?_
  rw [show D.opticalStripRate d r₁ r₂ * |ω| =
      Real.sqrt d * |ω| * (D.opticalCoordinate r₂ - D.opticalCoordinate r₁) by
    unfold NormalChannel.opticalStripRate
    ring]
  exact reciprocal_cosh_le_exp _

/-- The explicit high-frequency bound for a finite time-derivative
factor, at any desired inverse-power order. -/
theorem normal_transfer_optical_strip_power_decay (D : NormalChannel) {ω : ℝ} (hω : ω ≠ 0)
    (u : NormalTransfer D.a (D.potential (ω ^ 2))) {r₁ r₂ r d : ℝ}
    (hr₁ : 0 ≤ r₁) (h₁₂ : r₁ < r₂) (h₂r : r₂ ≤ r) (hd : 0 < d)
    (hstrip : ∀ s ∈ Icc r₁ r₂, d ≤ D.a s * D.temporal s) (j N : ℕ) :
    |ω| ^ j * u.amplitude r ≤
      (2 * ((j + N)! : ℝ) / (D.opticalStripRate d r₁ r₂) ^ (j + N)) / |ω| ^ N := by
  let c := D.opticalStripRate d r₁ r₂
  have hc : 0 < c := D.optical_strip_rate_pos hd hr₁ h₁₂
  let X := c * |ω|
  have hX : 0 ≤ X := mul_nonneg hc.le (abs_nonneg ω)
  have hf : 0 < ((j + N)! : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hE := (div_le_iff₀ hf).mp (Real.pow_div_factorial_le_exp X hX (j + N))
  have ht := mul_le_mul_of_nonneg_right hE (Real.exp_nonneg (-X))
  have hR : Real.exp X * ((j + N)! : ℝ) * Real.exp (-X) = ((j + N)! : ℝ) := by
    calc
      _ = ((j + N)! : ℝ) * (Real.exp X * Real.exp (-X)) := by ring
      _ = _ := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
  rw [hR] at ht
  have hu := normal_transfer_optical_strip_exponential D ω u hr₁ h₁₂.le h₂r hd hstrip
  have hU := mul_le_mul_of_nonneg_left hu (show 0 ≤ |ω| ^ (j + N) by positivity)
  have hbound : |ω| ^ (j + N) * u.amplitude r ≤ 2 * ((j + N)! : ℝ) / c ^ (j + N) := by
    apply (le_div_iff₀ (pow_pos hc _)).mpr
    calc
      _ ≤ (|ω| ^ (j + N) * (2 * Real.exp (-X))) * c ^ (j + N) :=
        mul_le_mul_of_nonneg_right hU (pow_nonneg hc.le _)
      _ = 2 * (X ^ (j + N) * Real.exp (-X)) := by
        dsimp only [X]
        rw [mul_pow]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left ht (by norm_num)
  apply (le_div_iff₀ (pow_pos (abs_pos.2 hω) _)).mpr
  calc
    _ = |ω| ^ (j + N) * u.amplitude r := by rw [pow_add]; ring
    _ ≤ _ := hbound

/-- On the frequency side the actual (j)-th time-derivative symbol is
((mathrm iomega)^j), whose norm is covered by the estimate. -/
theorem normal_transfer_optical_strip_time_symbol_decay (D : NormalChannel) {ω : ℝ} (hω : ω ≠ 0)
    (u : NormalTransfer D.a (D.potential (ω ^ 2))) {r₁ r₂ r d : ℝ}
    (hr₁ : 0 ≤ r₁) (h₁₂ : r₁ < r₂) (h₂r : r₂ ≤ r) (hd : 0 < d)
    (hstrip : ∀ s ∈ Icc r₁ r₂, d ≤ D.a s * D.temporal s) (j N : ℕ) :
    ‖(Complex.I * (ω : ℂ)) ^ j * (u.amplitude r : ℂ)‖ ≤
      (2 * ((j + N)! : ℝ) / (D.opticalStripRate d r₁ r₂) ^ (j + N)) / |ω| ^ N := by
  have hr : 0 ≤ r := hr₁.trans (h₁₂.le.trans h₂r)
  rw [norm_mul, norm_pow, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_of_nonneg (normal_transfer_positive D (sq_nonneg ω) u hr).le]
  exact normal_transfer_optical_strip_power_decay D hω u hr₁ h₁₂ h₂r hd hstrip j N

end UV.TemporalRay
