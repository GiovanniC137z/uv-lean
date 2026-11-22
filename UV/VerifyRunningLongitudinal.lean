import UV.VerifyRunningFractional
import UV.VerifyRunningSingle
import UV.AdvanceStableLongitudinal

/-! One-height decomposition and compact-test boundary value of the complete
running stable-half longitudinal coefficient on a fixed sector plane. -/

noncomputable section

namespace UV.SectorPlane

open Filter MeasureTheory Set UV.Carrier
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E]

def Plane.masslessRunningStableLongitudinalPair (diamond : Plane E) (ε : Evolution) (h : Height)
    (a : ℝ) (u v : ConeUnitDirection) (g : ℝ × Spatial → ℂ) : ℂ :=
  ∫ q : ℝ × Spatial, runningAxialTest (coneTensorTest u v g) q *
    (diamond.stableHalfCoefficient ε a (shellSquare q.1 q.2) h *
      (diamond.poleCoefficient ε h (shellSquare q.1 q.2)) ^ 2)


theorem Plane.massless_running_longitudinal_integrand_directed (diamond : Plane E) (ε : Evolution)
    (h : Height) (a : ℝ) (u v : ConeUnitDirection) (g : ℝ × Spatial → ℂ) (q : ℝ × Spatial) :
    let w := shellSquare q.1 q.2
    directed (runningAxialTest (coneTensorTest u v g) q * (diamond.stableHalfCoefficient ε a w h *
      (diamond.poleCoefficient ε h w) ^ 2)) =
      directed (runningAxialTest (coneTensorTest u v g) q) *
        (diamond.stableHalfNumerator ε h a w * (diamond.poleInverse ε h w) ^ 2) := by
  dsimp only
  rw [directed_mul, diamond.stable_square_coefficient_directed]

theorem Plane.massless_running_stable_longitudinal_pair_split (diamond : Plane E) (ε : Evolution)
    (h : Height) (a : ℝ) (u v : ConeUnitDirection) {g : ℝ × Spatial → ℂ}
    (hg : Continuous g) (hs : HasCompactSupport g) :
    diamond.masslessRunningStableLongitudinalPair ε h a u v g =
      (∫ q : ℝ × Spatial, runningAxialTest (coneTensorTest u v g) q *
        (diamond.poleCoefficient ε h (shellSquare q.1 q.2)) ^ 2) +
      diamond.runningTensorFractionalPair ε h a u v g -
      ((a : ℂ) ^ 2 / 2) * (∫ q : ℝ × Spatial, runningAxialTest (coneTensorTest u v g) q *
        diamond.poleCoefficient ε h (shellSquare q.1 q.2)) +
      ∫ q : ℝ × Spatial, runningAxialTest (coneTensorTest u v g) q *
        stableSquareResidual a (diamond.shiftedShellCoefficient ε h (shellSquare q.1 q.2)) := by
  let T := coneTensorTest u v g
  let f := runningAxialTest T
  let w (q : ℝ × Spatial) := shellSquare q.1 q.2
  let Z (q : ℝ × Spatial) := diamond.shiftedShellCoefficient ε h (w q)
  let P (q : ℝ × Spatial) := diamond.poleCoefficient ε h (w q)
  let S (q : ℝ × Spatial) := diamond.stableShellRoot ε h (w q)
  let C := (a : ℂ) ^ 2 / 2
  let B (q : ℝ × Spatial) := -(a : ℂ) / (S q) ^ 3
  let D (q : ℝ × Spatial) := stableSquareResidual a (Z q)
  have hPc : Continuous P := (diamond.pole_coefficient_continuous ε h).comp shellSquare_continuous
  have hZc : Continuous Z := (Complex.continuous_ofReal.add continuous_const).comp shellSquare_continuous
  have hS₀ (q : ℝ × Spatial) : S q ≠ 0 := diamond.stable_shell_root_ne_zero ε h (w q)
  have hSc : Continuous S := by
    have hInv (x : ℝ) : HasDerivAt (fun y => (diamond.stableShellRoot ε h y)⁻¹)
        ((2 : ℂ)⁻¹ * ((diamond.stableShellRoot ε h x) ^ 3)⁻¹) x :=
      diamond.stable_shell_inverse_root_hasDerivAt ε h x
    have hC := ((continuous_iff_continuousAt.mpr fun x => (hInv x).continuousAt).comp
      shellSquare_continuous).inv₀ (fun q => inv_ne_zero (hS₀ q))
    simpa only [Function.comp_def, inv_inv] using hC
  have hB : Continuous B := continuous_const.div (hSc.pow 3) (fun q => pow_ne_zero _ (hS₀ q))
  have hD : Continuous D := by
    let X (q : ℝ × Spatial) := -(a : ℂ) * S q
    have hX : Continuous X := continuous_const.mul hSc
    change Continuous (fun q => (Complex.exp (X q) - 1 - X q - X q ^ 2 / 2) / Z q ^ 2)
    exact (((Complex.continuous_exp.comp hX).sub continuous_const).sub hX |>.sub
      ((hX.pow 2).div_const 2)).div (hZc.pow 2)
      (fun q => pow_ne_zero _ (diamond.massless_shifted_coefficient_nonzero ε h (w q)))
  have hf : Continuous T := cone_tensor_test_continuous u v hg
  have hfs : HasCompactSupport T := cone_tensor_test_compact u v hs
  have hi {K : ℝ × Spatial → ℂ} (hK : Continuous K) :
      Integrable (fun q => f q * K q) volume := by
    simpa only [f, runningAxialTest, mul_assoc] using integrable_runningAxialSign_mul measurable_fst
      ((hf.mul hK).integrable_of_hasCompactSupport hfs.mul_right)
  have h₂ := hi (hPc.pow 2)
  have hB' := hi hB
  have h₁ := (hi hPc).const_mul C
  have hD' := hi hD
  have hSum : Integrable (fun q => f q * (P q) ^ 2 + f q * B q) volume := h₂.add hB'
  have hSub : Integrable (fun q => f q * (P q) ^ 2 + f q * B q - C * (f q * P q)) volume :=
    hSum.sub h₁
  have hFrac : diamond.runningTensorFractionalPair ε h a u v g = ∫ q, f q * B q := by
    apply integral_congr_ae
    refine Eventually.of_forall fun q => ?_
    simp only [runningAxialTest, coneTensorTest, f, T, B, S, w, mul_assoc]
  rw [hFrac]
  change diamond.masslessRunningStableLongitudinalPair ε h a u v g =
    (∫ q, f q * (P q) ^ 2) + (∫ q, f q * B q) -
      C * (∫ q, f q * P q) + ∫ q, f q * D q
  rw [← integral_const_mul, ← integral_add h₂ hB', ← integral_sub hSum h₁,
    ← integral_add hSub hD']
  unfold Plane.masslessRunningStableLongitudinalPair
  apply integral_congr_ae
  refine Eventually.of_forall fun q => ?_
  change f q * (diamond.stableHalfCoefficient ε a (w q) h * (P q) ^ 2) =
    f q * (P q) ^ 2 + f q * B q - C * (f q * P q) + f q * D q
  rw [diamond.stable_square_coefficient_split ε h a (w q)]
  dsimp only [P, B, C, D, Z, S]
  ring

/-- The flow keeps the same positive height in the stable numerator and
both pole powers. No exclusion of tests through the light-cone tip is needed. -/
theorem Plane.massless_running_stable_longitudinal_limit (diamond : Plane E) (ε : Evolution)
    {a : ℝ} (ha : 0 ≤ a) (u v : ConeUnitDirection) {g : ℝ × Spatial → ℂ}
    (hg : ContDiff ℝ 2 g) (hs : HasCompactSupport g) :
    ∃ L : ℂ,
      Tendsto (fun h : Height => diamond.masslessRunningStableLongitudinalPair ε h a u v g)
        ((𝓝[>] (0 : ℝ)).comap (fun h : Height => (h : ℝ))) (𝓝 L) ∧
      Tendsto (fun h : Height => directed (diamond.masslessRunningStableLongitudinalPair ε h a u v g))
        ((𝓝[>] (0 : ℝ)).comap (fun h : Height => (h : ℝ))) (𝓝 (directed L)) := by
  let U := coneCovector (WithLp.ofLp u.val)
  let V := coneCovector (WithLp.ofLp v.val)
  let F := coneTensorTest u v g
  have hF : F = fun q => (U q * V q) • g q := by
    funext q
    simp only [F, coneTensorTest, coneLinearTest, U, V, Complex.real_smul, Complex.ofReal_mul]
    ring
  have hf : ContDiff ℝ 2 F := hF.symm ▸ (U.contDiff.mul V.contDiff).smul hg
  have hfs : HasCompactSupport F := cone_tensor_test_compact u v hs
  obtain ⟨_, _, h₁⟩ := diamond.cone_running_smooth_single_limit ε hf hfs
  obtain ⟨_, _, _, h₂⟩ := diamond.cone_running_smooth_longitudinal_limit ε hg hs U V
  rw [← hF] at h₂
  have hB := diamond.running_tensor_fractional_pair_limit ε a u v (hg.of_le (by norm_num)) hs
  have hD := diamond.running_square_residual_full_momentum ε ha hf.continuous hfs
  have hL := (((h₂.add hB).sub (h₁.const_mul ((a : ℂ) ^ 2 / 2))).add hD).congr
    (f₂ := fun h => diamond.masslessRunningStableLongitudinalPair ε h a u v g) (fun h => by
      dsimp only
      rw [diamond.massless_running_stable_longitudinal_pair_split ε h a u v hg.continuous hs]
      simp only [F, Complex.real_smul, runningAxialTest, mul_assoc])
  exact ⟨_, hL, directed_shell_readout_continuous.continuousAt.tendsto.comp hL⟩

end UV.SectorPlane
