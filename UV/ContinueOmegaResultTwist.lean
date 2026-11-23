import UV.ContinueOmegaResultHolonomy

/-! The static flat-Maxwell twist on the physical spatial torus. Its
equivariant Wilson factor uses the actual lift of the chord, so the
integer winding is accounted for before any electric-order expansion. -/

noncomputable section
open MeasureTheory Set UV.SectorPlane
open scoped InnerProductSpace

namespace UV

def omegaTorusInteger (m : Fin 3 → ℤ) : Spatial := WithLp.toLp 2 (fun j => (m j : ℝ))

private theorem omega_torus_integer_inner (n m : Fin 3 → ℤ) :
    ⟪omegaTorusInteger n,omegaTorusInteger m⟫_ℝ = ((∑ j, n j * m j : ℤ) : ℝ) := by
  simp [omegaTorusInteger,PiLp.inner_apply,RCLike.inner_apply,mul_comm]

def omegaPhase (u : ℝ) : ℂ := Complex.exp ((u:ℂ)*Complex.I)

theorem omega_phase_norm (u : ℝ) : ‖omegaPhase u‖ = 1 := by simp [omegaPhase,Complex.norm_exp]

private theorem omega_phase_add (u w : ℝ) : omegaPhase (u+w) = omegaPhase u * omegaPhase w := by
  simp [omegaPhase,add_mul,Complex.exp_add]

private theorem omega_phase_winding (n : ℤ) : omegaPhase (2*Real.pi*(n:ℝ)) = 1 := by
  unfold omegaPhase
  push_cast
  convert Complex.exp_int_mul_two_pi_mul_I n using 2
  ring

def omegaWilsonTwist (b z : Spatial) (L : ℝ) := omegaPhase (⟪b,z⟫_ℝ/L)

def omegaGaugeEndpoint (n : Fin 3 → ℤ) (x : Spatial) (L : ℝ) :=
  omegaPhase (2*Real.pi*⟪omegaTorusInteger n,x⟫_ℝ/L)

/-- A large gauge transformation produces exactly the two charged endpoint
phases, including when the chosen chord crosses a periodic boundary. -/
theorem omega_wilson_large_gauge (b x y : Spatial) (m n : Fin 3 → ℤ) {L : ℝ} (hL : 0 < L) :
    let z := (y-x)+L • omegaTorusInteger m
    omegaWilsonTwist (b+(2*Real.pi) • omegaTorusInteger n) z L * omegaGaugeEndpoint n x L =
      omegaWilsonTwist b z L * omegaGaugeEndpoint n y L := by
  dsimp only [omegaWilsonTwist,omegaGaugeEndpoint]
  rw [←omega_phase_add,←omega_phase_add]
  have h : ⟪b+(2*Real.pi) • omegaTorusInteger n,y-x+L • omegaTorusInteger m⟫_ℝ/L +
      2*Real.pi*⟪omegaTorusInteger n,x⟫_ℝ/L =
      (⟪b,y-x+L • omegaTorusInteger m⟫_ℝ/L+2*Real.pi*⟪omegaTorusInteger n,y⟫_ℝ/L) +
        2*Real.pi*((∑ j, n j*m j:ℤ):ℝ) := by
    simp only [inner_add_left,real_inner_smul_left,inner_add_right,inner_sub_right,
      real_inner_smul_right,omega_torus_integer_inner]
    field_simp
    ring
  rw [h,omega_phase_add,omega_phase_winding,mul_one]

private theorem omega_twist_character_mean (w : ℤ) :
    (∫ u in Ioc (0:ℝ) 1, omegaPhase (2*Real.pi*(w:ℝ)*u)) = if w=0 then 1 else 0 := by
  split_ifs with h
  · simp [h,omegaPhase]
  · let c : ℂ := (2*Real.pi*(w:ℂ))*Complex.I
    have hc : c ≠ 0 := by
      dsimp [c]
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) (Int.cast_ne_zero.mpr h)) Complex.I_ne_zero
    have he (u : ℝ) : omegaPhase (2*Real.pi*(w:ℝ)*u) = Complex.exp (c*(u:ℂ)) := by
      unfold omegaPhase
      dsimp [c]
      push_cast
      ring_nf
    simp_rw [he]
    rw [←intervalIntegral.integral_of_le zero_le_one,integral_exp_mul_complex hc]
    have hce : Complex.exp c = 1 := by
      convert Complex.exp_int_mul_two_pi_mul_I w using 2
      dsimp [c]
      ring
    simp [hce]

/-- The normalized cell average for b₀/(2π) projects exactly onto the
trivial total winding character before averaging the Brownian marks. -/
theorem omega_uniform_twist_projection (w : Fin 3 → ℤ) :
    (∫ u : Fin 3 → ℝ, ∏ j, omegaPhase (2*Real.pi*(w j:ℝ)*(u j))
      ∂Measure.pi (fun _ => volume.restrict (Ioc (0:ℝ) 1))) =
      if w = 0 then 1 else 0 := by
  rw [integral_fintype_prod_eq_prod (fun j u => omegaPhase (2*Real.pi*(w j:ℝ)*u))]
  simp_rw [omega_twist_character_mean]
  split_ifs with h
  · simp [h]
  · obtain ⟨j,hj⟩ : ∃ j, w j ≠ 0 := by
      by_contra! hh
      exact h (funext hh)
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    simp [hj]

end UV
