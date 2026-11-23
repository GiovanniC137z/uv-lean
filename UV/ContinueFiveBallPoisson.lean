import UV.ContinueFiveBallSharp

/-! Poisson's integral representation for the Bessel J function evaluated
on the actual normalized A4 ball. The formula applies at positive radius;
at the origin the probability characteristic is exactly one. -/

noncomputable section

open MeasureTheory Metric
open scoped ENNReal

namespace UV

/-- Poisson's integral for the real Bessel function of the first kind,
for order ν > −1/2 and positive argument x. -/
def normalBesselJPoisson (ν x : ℝ) : ℝ :=
  (x/2)^ν / (Real.sqrt Real.pi * Real.Gamma (ν+1/2)) * normalBallCosine (ν-1/2) x

private theorem normal_unit_ball_volume (d : ℕ) :
    volume.real (ball (0:NormalBall (d+1)) 1) =
      Real.sqrt Real.pi ^ (d+1) / Real.Gamma (((d+1:ℕ):ℝ)/2+1) := by
  rw [measureReal_def,EuclideanSpace.volume_ball]
  simp only [Fintype.card_fin,ENNReal.ofReal_one,one_pow,one_mul]
  exact ENNReal.toReal_ofReal (div_nonneg (pow_nonneg (Real.sqrt_nonneg _) _) (Real.Gamma_pos_of_pos (by positivity)).le)

private theorem normal_axis_bessel (d : ℕ) {x : ℝ} (hx : 0 < x) :
    let ν := (((d+1+1:ℕ):ℝ)/2)
    (normalShellCharacteristic (EuclideanSpace.single (0:Fin (d+1+1)) x)).re =
      Real.Gamma (1+ν) * (2/x)^ν * normalBesselJPoisson ν x := by
  dsimp only
  let ν := (((d+1+1:ℕ):ℝ)/2)
  have hα : ((d+1:ℕ):ℝ)/2 = ν-1/2 := by dsimp [ν]; push_cast; ring
  have hΓ : ((d+1:ℕ):ℝ)/2+1 = ν+1/2 := by linarith
  have hν : 0 < ν := by dsimp [ν]; positivity
  have hπ := Real.sqrt_pos_of_pos Real.pi_pos
  have h1 : Real.Gamma (1+ν) ≠ 0 := (Real.Gamma_pos_of_pos (by positivity : 0 < 1+ν)).ne'
  have h2 : Real.Gamma (ν+1/2) ≠ 0 := (Real.Gamma_pos_of_pos (by positivity : 0 < ν+1/2)).ne'
  have hcancel : (2/x)^ν * (x/2)^ν = 1 := by
    rw [←Real.mul_rpow (by positivity) (by positivity),show (2/x)*(x/2)=1 by field_simp,Real.one_rpow]
  change _ = Real.Gamma (1+ν) * (2/x)^ν * normalBesselJPoisson ν x
  rw [normal_ball_axis_characteristic]
  change (volume.real (ball (0:NormalBall (d+1+1)) 1))⁻¹ * _ * _ = _
  rw [normal_unit_ball_volume (d+1),normal_unit_ball_volume d]
  change (_ / Real.Gamma (ν+1))⁻¹ * (_ / Real.Gamma (((d+1:ℕ):ℝ)/2+1)) * _ = _
  rw [hΓ,hα,add_comm ν 1,normalBesselJPoisson,pow_succ _ (d+1)]
  calc _ = Real.Gamma (1+ν)/(Real.sqrt Real.pi*Real.Gamma (ν+1/2))*normalBallCosine (ν-1/2) x := by
             field_simp [hπ.ne',h1,h2]
       _ = _ := by
             symm
             calc _ = ((2/x)^ν * (x/2)^ν)*(Real.Gamma (1+ν)/(Real.sqrt Real.pi*Real.Gamma (ν+1/2))*normalBallCosine (ν-1/2) x) := by ring
                  _ = _ := by rw [hcancel,one_mul]

/-- The manuscript's full radial Bessel expression for an arbitrary
orthonormal chart, with the gamma and radius factors fixed by Haar
volume. The value at zero follows from probability normalization. -/
theorem normal_shell_poisson_formula (ι : Type*) [Fintype ι] (hn : 2 ≤ Fintype.card ι) :
    normalShellCharacteristic (0:WilsonBallSpace ι) = 1 ∧
    ∀ p : WilsonBallSpace ι, p ≠ 0 →
      let ν := ((Fintype.card ι:ℝ)/2)
      normalShellCharacteristic p = ((Real.Gamma (1+ν) * (2/‖p‖)^ν * normalBesselJPoisson ν ‖p‖ : ℝ):ℂ) := by
  refine ⟨by simp [normalShellCharacteristic],fun p hp => ?_⟩
  let d := Fintype.card ι-2
  have hdim : Fintype.card ι = d+1+1 := by dsimp [d]; omega
  let e : WilsonBallSpace ι ≃ₗᵢ[ℝ] NormalBall (d+1+1) :=
    LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Fintype.equivOfCardEq (by simpa only [Fintype.card_fin] using hdim))
  let q := EuclideanSpace.single (0:Fin (d+1+1)) ‖p‖
  have he : ‖e p‖ = ‖q‖ := by simp [q,EuclideanSpace.norm_single]
  dsimp only
  rw [hdim,←normal_shell_characteristic_isometry e p,normal_shell_characteristic_radial he,←normal_shell_characteristic_real q]
  exact_mod_cast normal_axis_bessel d (norm_pos_iff.mpr hp)

end UV
