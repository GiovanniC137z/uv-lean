import UV.ContinueTwoBandSpectralExpansion
import UV.ContinueOpeningGaussianCarrier
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Fourier origin of all the normalized hopping differences. Duration is
oriented along the real unit carrier of the selected sector plane, and every
temporal mark on a link is integrated over that same signed interval. -/

noncomputable section
open MeasureTheory Filter Complex Set
open scoped Topology

namespace UV.SectorPlane

def hoppingPulse (ν u : ℝ) : ℂ := ∫ t in 0..u, openingFourierWave ν t

theorem hopping_pulse_zero (u : ℝ) : hoppingPulse 0 u = u := by
  simp [hoppingPulse,openingFourierWave]

theorem hopping_pulse_formula {ν : ℝ} (hν : ν ≠ 0) (u : ℝ) :
    hoppingPulse ν u = (openingFourierWave ν u-1)/(I*ν) := by
  have h (t : ℝ) : openingFourierWave ν t = Complex.exp ((I*ν)*(t:ℂ)) := by
    unfold openingFourierWave
    congr 1
    ring
  simp only [hoppingPulse,h,integral_exp_mul_complex (mul_ne_zero I_ne_zero (Complex.ofReal_ne_zero.mpr hν))]
  simp

theorem hopping_pulse_norm (ν u : ℝ) : ‖hoppingPulse ν u‖ ≤ |u| := by
  simpa only [hoppingPulse,sub_zero,mul_one,one_mul] using intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := u) (C := 1) (fun t _ => (opening_fourier_wave_norm ν t).le)

private theorem pulse_continuous (ν : ℝ) : Continuous (hoppingPulse ν) := by
  by_cases h : ν=0
  · subst ν
    simpa only [show hoppingPulse 0 = fun t : ℝ => (t:ℂ) by funext; apply hopping_pulse_zero] using Complex.continuous_ofReal
  · simp_rw [show hoppingPulse ν = _ from funext (hopping_pulse_formula h)]
    exact ((opening_fourier_wave_continuous ν).sub continuous_const).div_const _

private def markDensity (V : List ℝ) (g : ℝ → ℂ) (u : ℝ) :=
  g u * (V.map (fun ν => hoppingPulse ν u)).prod

private def pulseFourier (μ : Measure ℝ) (g : ℝ → ℂ) (s : ℝ) := ∫ u, g u * openingFourierWave s u ∂μ

private def AllMoments (μ : Measure ℝ) (g : ℝ → ℂ) :=
  AEStronglyMeasurable g μ ∧ ∀ n : ℕ, Integrable (fun u : ℝ => |u|^n * ‖g u‖) μ

private theorem pulse_density_integrable {μ : Measure ℝ} {g : ℝ → ℂ} (hg : AllMoments μ g) :
    Integrable g μ := by
  exact ((hg.2 0).mono' hg.1 (ae_of_all _ (by simp)))

private theorem pulse_moments {μ : Measure ℝ} {g : ℝ → ℂ} (hg : AllMoments μ g) (ν : ℝ) :
    AllMoments μ (fun u => g u*hoppingPulse ν u) := by
  have hme := hg.1.mul (pulse_continuous ν).aestronglyMeasurable
  refine ⟨hme,fun n => (hg.2 (n+1)).mono' ((by fun_prop : Measurable (fun u : ℝ => |u|^n)).aestronglyMeasurable.mul hme.norm) ?_⟩
  filter_upwards with u
  rw [Real.norm_of_nonneg (by positivity),norm_mul,pow_succ]
  grw [hopping_pulse_norm]
  ring_nf
  exact le_refl _

private theorem pulse_step {μ : Measure ℝ} {g : ℝ → ℂ} (hg : AllMoments μ g) (ν : ℝ) :
    hoppingDifference ν (pulseFourier μ g) = pulseFourier μ (fun u => g u*hoppingPulse ν u) := by
  have hi := pulse_density_integrable hg
  funext s
  by_cases hν : ν=0
  · subst ν
    have hx : Integrable (fun u : ℝ => (u:ℂ)*g u) μ := by
      apply (hg.2 1).mono' (Complex.continuous_ofReal.aestronglyMeasurable.mul hg.1)
      filter_upwards with u
      simp
    have h := opening_fourier_test_hasDerivAt hi hx (-s)
    have hd := h.scomp (𝕜 := ℝ) s (hasDerivAt_id s).neg
    have hf : (fun s : ℝ => (∫ u, g u*openingFourierWave (-s) u ∂μ)) ∘ (Neg.neg : ℝ → ℝ) =
        pulseFourier μ g := by funext; simp [pulseFourier]
    rw [hf] at hd
    rw [hoppingDifference,if_pos rfl,hd.deriv]
    simp only [neg_neg,one_smul,neg_smul,pulseFourier,hopping_pulse_zero,←integral_neg,←integral_div]
    apply integral_congr_ae
    filter_upwards with u
    simp [div_eq_mul_inv]
    ring_nf
    simp [I_sq]
  · rw [hoppingDifference,if_neg hν,pulseFourier,pulseFourier,pulseFourier]
    rw [←integral_sub (opening_wave_mul_integrable hi _) (opening_wave_mul_integrable hi _),←integral_div]
    apply integral_congr_ae
    filter_upwards with u
    rw [hopping_pulse_formula hν,opening_fourier_wave_add]
    ring

private theorem pulse_marks {μ : Measure ℝ} {g : ℝ → ℂ} (hg : AllMoments μ g) (V : List ℝ) :
    hoppingMarks V (pulseFourier μ g) = pulseFourier μ (markDensity V g) := by
  induction V generalizing g with
  | nil => simp only [hoppingMarks,show markDensity [] g = g by funext; simp [markDensity]]
  | cons ν V ih =>
    rw [hoppingMarks,pulse_step hg,ih (pulse_moments hg ν)]
    congr 1
    funext u
    simp [markDensity,mul_assoc]

private theorem moment_pos {m : ℝ} (hm : 0<m) (b : ℝ) :
    AllMoments (volume.restrict (Ioi 0)) (fun u : ℝ => (Real.exp (-m*u):ℂ)*openingFourierWave b u) := by
  refine ⟨((by fun_prop: Continuous (fun u : ℝ => (Real.exp (-m*u):ℂ))).mul
    (opening_fourier_wave_continuous b)).aestronglyMeasurable,?_⟩
  intro n
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := (n:ℝ)) (p := 1) (b := m)
    (by linarith [Nat.cast_nonneg (α := ℝ) n]) (by norm_num) hm
  apply h.congr
  filter_upwards [ae_restrict_mem (μ := volume) (s := Ioi (0:ℝ)) measurableSet_Ioi] with u hu
  change 0 < u at hu
  simp only [Real.rpow_natCast,Real.rpow_one,abs_of_pos hu,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _),opening_fourier_wave_norm,mul_one]

private theorem moment_neg {m : ℝ} (hm : 0<m) (b : ℝ) :
    AllMoments (volume.restrict (Iic 0)) (fun u : ℝ => -(Real.exp (m*u):ℂ)*openingFourierWave b u) := by
  refine ⟨((by fun_prop: Continuous (fun u : ℝ => -(Real.exp (m*u):ℂ))).mul
    (opening_fourier_wave_continuous b)).aestronglyMeasurable,?_⟩
  intro n
  have h : IntegrableOn (fun u : ℝ => |u|^n * Real.exp (-m*u)) (Ioi 0) := by
    simpa only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),
      opening_fourier_wave_norm,mul_one] using (moment_pos hm 0).2 n
  have hneg := IntegrableOn.comp_neg_Iio (μ := (volume : Measure ℝ)) (c := (0:ℝ)) (f := fun u : ℝ => |u|^n * Real.exp (-m*u)) (by simpa only [neg_zero] using h)
  apply (integrableOn_Iic_iff_integrableOn_Iio (f := fun u : ℝ => |u|^n * ‖-(Real.exp (m*u):ℂ)*openingFourierWave b u‖) (μ := (volume : Measure ℝ)) (b := (0:ℝ))).mpr
  simpa only [Function.comp_apply,neg_zero,abs_neg,neg_mul_neg,norm_mul,norm_neg,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),opening_fourier_wave_norm,mul_one] using hneg

/-- The forward and backward onsite factors with arbitrary shift are exactly
the Fourier integrals of their oriented decaying time densities. -/
private theorem pulse_onsite {m : ℝ} (hm : 0<m) (b : ℝ) :
    (fun s => hoppingInterval m (s+b)) =
      pulseFourier (volume.restrict (Ioi 0)) (fun u : ℝ => (Real.exp (-m*u):ℂ)*openingFourierWave b u) ∧
    (fun s => hoppingInterval (-m) (s+b)) =
      pulseFourier (volume.restrict (Iic 0)) (fun u : ℝ => -(Real.exp (m*u):ℂ)*openingFourierWave b u) := by
  constructor <;> funext s
  · let c : ℂ := -m+I*(s+b)
    have he (u : ℝ) : (Real.exp (-m*u):ℂ)*openingFourierWave b u*openingFourierWave s u =
        Complex.exp (c*u) := by
      simp only [openingFourierWave,Complex.ofReal_exp,←Complex.exp_add]
      congr 1
      dsimp [c]
      push_cast
      ring
    simp only [pulseFourier,he,integral_exp_mul_complex_Ioi (show c.re < 0 by simpa [c,Complex.mul_re] using hm) 0]
    simp only [hoppingInterval,c,Complex.ofReal_zero,mul_zero,Complex.exp_zero,Complex.ofReal_add,
      show -(m:ℂ)+I*(s+b) = -((m:ℂ)-I*(s+b)) by ring,div_neg,neg_div,neg_neg,one_div]
  · let c : ℂ := m+I*(s+b)
    have he (u : ℝ) : -(Real.exp (m*u):ℂ)*openingFourierWave b u*openingFourierWave s u =
        -Complex.exp (c*u) := by
      simp only [openingFourierWave,Complex.ofReal_exp,neg_mul,←Complex.exp_add]
      congr 2
      dsimp [c]
      push_cast
      ring
    simp only [pulseFourier,he,integral_neg,
      integral_exp_mul_complex_Iic (show 0 < c.re by simpa [c,Complex.mul_re] using hm) 0]
    simp only [hoppingInterval,c,Complex.ofReal_zero,mul_zero,Complex.exp_zero,Complex.ofReal_neg,Complex.ofReal_add,
      show -(m:ℂ)-I*(s+b) = -((m:ℂ)+I*(s+b)) by ring,inv_neg,one_div]

/-- Exact temporal multiplier for every ordered list of marks on either
oriented onsite slot, with the carrier shift and positive Fourier phase intact. -/
theorem hopping_marks_oriented_fourier {m : ℝ} (hm : 0<m) (b : ℝ) (V : List ℝ) (s : ℝ) :
    hoppingMarks V (fun x => hoppingInterval m (x+b)) s =
      ∫ u in Ioi (0:ℝ), (Real.exp (-m*u):ℂ)*openingFourierWave (s+b) u*
        (V.map (fun ν => hoppingPulse ν u)).prod ∧
    hoppingMarks V (fun x => hoppingInterval (-m) (x+b)) s =
      ∫ u in Iic (0:ℝ), -(Real.exp (m*u):ℂ)*openingFourierWave (s+b) u*
        (V.map (fun ν => hoppingPulse ν u)).prod := by
  obtain ⟨hp,hn⟩ := pulse_onsite hm b
  rw [hp,hn,pulse_marks (moment_pos hm b),pulse_marks (moment_neg hm b)]
  constructor <;> apply integral_congr_ae <;> filter_upwards with u <;>
    simp only [markDensity,opening_fourier_wave_add] <;> ring

/-- Complete marks commute for either oriented slot even if some transfer,
or a nontrivial sum of transfers, vanishes. The equality uses the common
product of actual pulses on the original signed duration interval. -/
theorem hopping_marks_permutation {a : ℝ} (ha : a ≠ 0) (b : ℝ) {V W : List ℝ} (h : V.Perm W) :
    hoppingMarks V (fun x => hoppingInterval a (x+b)) = hoppingMarks W (fun x => hoppingInterval a (x+b)) := by
  funext s
  have he (u : ℝ) : (V.map (fun ν => hoppingPulse ν u)).prod = (W.map (fun ν => hoppingPulse ν u)).prod :=
    (h.map _).prod_eq
  rcases lt_or_gt_of_ne ha with hn|hp
  · have hv := (hopping_marks_oriented_fourier (neg_pos.mpr hn) b V s).2
    have hw := (hopping_marks_oriented_fourier (neg_pos.mpr hn) b W s).2
    simpa only [neg_neg] using hv.trans ((integral_congr_ae (ae_of_all _ (fun u =>
      congrArg (fun z : ℂ => -(Real.exp (-a*u):ℂ)*openingFourierWave (s+b) u*z) (he u)))).trans hw.symm)
  · rw [(hopping_marks_oriented_fourier hp b V s).1,(hopping_marks_oriented_fourier hp b W s).1]
    simp_rw [he]

end UV.SectorPlane
