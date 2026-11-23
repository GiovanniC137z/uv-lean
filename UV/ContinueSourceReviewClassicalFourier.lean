import UV.ContinueSourceReviewClassicalPacket

/-! Time transform of the invariant-current two-point coefficient at fixed
spatial momentum on the locked sector plane. -/

noncomputable section
open MeasureTheory Filter Set UV.SectorPlane

namespace UV

def seaTimeWave (κ ω t : ℝ) : ℂ :=
  Complex.exp (Complex.I * (ω:ℂ)*(t:ℂ)-(κ:ℂ)*(|t|:ℝ))

/-- Direct evaluation on the two ordered half-lines, allowing either
signed real frequency; the measure is Lebesgue in the carrier time. -/
theorem sea_time_wave_fourier {κ : ℝ} (hκ : 0 < κ) (ω : ℝ) :
    Integrable (seaTimeWave κ ω) ∧
    (∫ t : ℝ, seaTimeWave κ ω t) = ((2*κ/(κ^2+ω^2):ℝ):ℂ) := by
  let p : ℂ := κ+Complex.I*ω
  let n : ℂ := -κ+Complex.I*ω
  have hp : 0 < p.re := by simpa [p] using hκ
  have hn : n.re < 0 := by simpa [n] using neg_lt_zero.mpr hκ
  have ep : EqOn (seaTimeWave κ ω) (fun x : ℝ => Complex.exp (p*x)) (Iic 0) := by
    intro x hx
    unfold seaTimeWave
    rw [abs_of_nonpos hx,Complex.ofReal_neg]
    congr 1; dsimp only [p]; ring
  have en : EqOn (seaTimeWave κ ω) (fun x : ℝ => Complex.exp (n*x)) (Ioi 0) := by
    intro x hx
    unfold seaTimeWave
    rw [abs_of_nonneg (le_of_lt hx)]
    congr 1; dsimp only [n]; ring
  have ip := (integrableOn_congr_fun ep measurableSet_Iic).mpr (integrableOn_exp_mul_complex_Iic hp 0)
  have ineg := (integrableOn_congr_fun en measurableSet_Ioi).mpr (integrableOn_exp_mul_complex_Ioi hn 0)
  have hi := ip.union ineg
  rw [Iic_union_Ioi,integrableOn_univ] at hi
  refine ⟨hi,?_⟩
  rw [← intervalIntegral.integral_Iic_add_Ioi ip ineg,
    setIntegral_congr_fun measurableSet_Iic ep,setIntegral_congr_fun measurableSet_Ioi en,
    integral_exp_mul_complex_Iic hp,integral_exp_mul_complex_Ioi hn]
  simp only [Complex.ofReal_zero,mul_zero,Complex.exp_zero]
  have hp0 : p ≠ 0 := by intro h; simp [h] at hp
  have hn0 : n ≠ 0 := by intro h; simp [h] at hn
  have hd : (κ:ℂ)^2+(ω:ℂ)^2 ≠ 0 := by exact_mod_cast (by positivity : 0 < κ^2+ω^2).ne'
  push_cast
  field_simp [hp0,hn0,hd]
  dsimp only [p,n]
  linear_combination (norm := ring_nf) (-2*(κ:ℂ)*(ω:ℂ)^2) * Complex.I_sq

theorem sea_time_wave_norm (κ ω t : ℝ) :
    ‖seaTimeWave κ ω t‖ = Real.exp (-κ*|t|) := by
  rw [seaTimeWave,Complex.norm_exp]
  congr 1
  simp [Complex.mul_re,Complex.mul_im]

/-- The energy kernel has L¹-time mass 2/κ at all real frequencies. -/
theorem sea_time_wave_mass {κ : ℝ} (hκ : 0 < κ) (ω : ℝ) :
    (∫ t : ℝ, ‖seaTimeWave κ ω t‖) = 2/κ := by
  have h : ∀ t, (‖seaTimeWave κ ω t‖ : ℂ) = seaTimeWave κ 0 t := by
    intro t
    rw [sea_time_wave_norm]
    simp only [seaTimeWave,Complex.ofReal_zero,mul_zero,zero_mul,zero_sub,Complex.ofReal_exp,
      Complex.ofReal_mul, Complex.ofReal_neg, neg_mul]
  have hf := (sea_time_wave_fourier hκ 0).2
  simp only [zero_pow (by decide : 2 ≠ 0),add_zero] at hf
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  simp_rw [h]
  rw [hf]
  norm_cast
  field_simp

/-- Fourier transform of the complete separated-time pair kernel with an
arbitrary fixed spatial component numerator a*s+b. All exchanges use
absolute product integrability on the actual timelike spectral band. -/
theorem sea_invariant_time_fourier {e m ℓ : ℝ} (hm : 0 < m) (hℓ : 0 < ℓ)
    {N : ℕ} (hN : 2 ≤ N) (q : Spatial) (ω a b : ℝ) :
    let ρ := seaInvariantPairDensity e m ℓ N
    let κ (s : ℝ) := Real.sqrt (s+‖q‖^2)
    let F (s t : ℝ) := (((a*s+b)*ρ s/(2*κ s):ℝ):ℂ) * seaTimeWave (κ s) ω t
    let μ := volume.restrict (Ici ((2*m)^2))
    Integrable (fun p : ℝ × ℝ => F p.1 p.2) (μ.prod volume) ∧
      (∫ t : ℝ, ∫ s, F s t ∂μ) =
        ((∫ s, (a*s+b)*ρ s/(s+(‖q‖^2+ω^2)) ∂μ : ℝ):ℂ) := by
  let ρ := seaInvariantPairDensity e m ℓ N
  let κ (s : ℝ) := Real.sqrt (s+‖q‖^2)
  let A (s : ℝ) := (a*s+b)*ρ s/(2*κ s)
  let F (s t : ℝ) := (A s : ℂ)*seaTimeWave (κ s) ω t
  let μ : Measure ℝ := volume.restrict (Ici ((2*m)^2))
  change Integrable (fun p : ℝ × ℝ => F p.1 p.2) (μ.prod volume) ∧ _
  have hs0 {s : ℝ} (hs : s∈Ici ((2*m)^2)) : 0 < s+‖q‖^2 := by
    have h := (sq_pos_of_pos (by positivity : 0 < 2*m)).trans_le hs
    positivity
  have hk {s : ℝ} (hs : s∈Ici ((2*m)^2)) : 0 < κ s := Real.sqrt_pos.mpr (hs0 hs)
  have hf : IntegrableOn (fun s => (a*s+b)*ρ s/(s+‖q‖^2)) (Ici ((2*m)^2)) := by
    simpa [ρ] using sea_fixed_spatial_tensor_integrable (e:=e) hm hℓ hN q 0 a b
  have hi : Integrable (fun p : ℝ × ℝ => F p.1 p.2) (μ.prod volume) := by
    have hmeas : Measurable (fun p : ℝ × ℝ => F p.1 p.2) := by
      dsimp only [F,A,ρ,κ,seaInvariantPairDensity,seaTimeWave]
      fun_prop
    apply (integrable_prod_iff hmeas.aestronglyMeasurable).mpr
    constructor
    · filter_upwards [ae_restrict_mem (μ:=volume) (measurableSet_Ici (a:=(2*m)^2))] with s hs
      exact (sea_time_wave_fourier (hk hs) ω).1.const_mul (A s:ℂ)
    · apply hf.norm.congr
      filter_upwards [ae_restrict_mem (μ:=volume) (measurableSet_Ici (a:=(2*m)^2))] with s hs
      simp only [F,norm_mul,integral_const_mul,Complex.norm_real,sea_time_wave_mass (hk hs) ω]
      have h₂ := Real.sq_sqrt (hs0 hs).le
      change κ s^2 = _ at h₂
      rw [← Real.norm_of_nonneg (show 0 ≤ 2/κ s by positivity : 0 ≤ 2/κ s), ← norm_mul]
      congr 1
      dsimp only [A]
      rw [← h₂]
      field_simp
  refine ⟨hi,?_⟩
  change (∫ t : ℝ, ∫ s, F s t ∂μ) = _
  rw [← integral_integral_swap (f:=F) hi,← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (μ:=volume) (measurableSet_Ici (a:=(2*m)^2))] with s hs
  simp only [F, integral_const_mul,(sea_time_wave_fourier (hk hs) ω).2]
  rw [← Complex.ofReal_mul]
  congr 1
  have h₂ := Real.sq_sqrt (hs0 hs).le
  change κ s^2 = _ at h₂
  dsimp only [A,ρ]
  rw [show s+(‖q‖^2+ω^2) = κ s^2+ω^2 by linarith]
  field_simp [(hk hs).ne']

end UV
