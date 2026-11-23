import UV.SectorPlaneFractionalRadial
import UV.SectorPlaneStableProduct
import UV.AdvanceStableLongitudinal

/-! The same-side, equal-massless-shell stable-half product. A radial
smooth compact test through the cone tip detects the logarithm of the
bare square at all nonnegative depths. -/

noncomputable section

namespace UV.SectorPlane

open Filter MeasureTheory UV.Carrier
open scoped Topology ContDiff

variable {E : Type*} [NormedAddCommGroup E]

theorem Plane.stable_same_pair_weight_add (diamond : Plane E) (ε : Evolution) (a b : ℝ)
    (h : Height) (w : ℝ) :
    diamond.stablePairWeight ε ε a b h w = diamond.stableHalfCoefficient ε (a+b) w h := by
  simp only [Plane.stablePairWeight,diamond.stable_half_analytic_form,← Complex.exp_add]
  push_cast
  congr 1
  ring

theorem Plane.same_stable_pairing_readout (diamond : Plane E) (ε : Evolution) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (m : ℝ) (h : Height) {f : MassiveMomentum → ℂ}
    (hf : Continuous f) (hs : HasCompactSupport f) :
    let φ := fun z => Complex.exp (-principalSqrt z)
    diamond.twoLinePairing ε ε h φ φ a b m m f = directed (-(∫ q,
      f q * (diamond.stableHalfCoefficient ε (a+b) (shellSquare q.1 q.2) h * (diamond.poleCoefficient ε h (massiveD m q))^2))) := by
  intro φ
  have hn := stable_pair_numerator diamond ε ε ha hb h
  have hsign : -(diamond.eta ε : ℂ) * (diamond.eta ε : ℂ) = -1 := by
    rw [neg_mul,← sq]; congr 1; exact_mod_cast diamond.eta_sq ε
  have hN : Continuous (diamond.twoLineNumerator ε ε φ φ a b h) := by
    rw [hn]; exact continuous_const.mul ((diamond.stable_pair_weight_continuous ε ε a b h).comp shellSquare_continuous)
  rw [diamond.two_line_pairing_readout ε ε h φ φ a b m m hf hs hN,← integral_neg]
  apply congrArg directed
  apply integral_congr_ae
  refine Eventually.of_forall fun q => ?_
  rw [hn]
  simp only [hsign,diamond.stable_same_pair_weight_add]
  ring

/-- The depth-dependent correction to the bare squared-pole coefficient
is bounded on the smooth radial probe. The normalized running-unit
product contributes a minus sign in the extracted character. -/
theorem Plane.massless_stable_square_log_witness (diamond : Plane E) (ε : Evolution) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    let φ := fun z => Complex.exp (-principalSqrt z)
    ∃ f : MassiveMomentum → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
      (∀ q, coneEuclideanRadius q ≤ 1 → f q = 1) ∧
      (∃ C ≥ (0:ℝ), ∀ᶠ h in poleBoundaryHeights,
        ‖(quotientCharacterEquiv (diamond.twoLinePairing ε ε h φ φ a b 0 0 (fun q => (f q : ℂ)))).1 +
          ∫ q, (f q : ℂ) * (diamond.poleCoefficient ε h (shellSquare q.1 q.2))^2‖ ≤ C) ∧
      (∃ B : ℝ, ∀ᶠ h in poleBoundaryHeights,
        ‖(quotientCharacterEquiv (diamond.twoLinePairing ε ε h φ φ a b 0 0 (fun q => (f q : ℂ)))).1.im +
          diamond.eta ε * Real.pi^2 * Real.log (1 / (h:ℝ))‖ ≤ B) ∧
      Tendsto (fun h => -(diamond.eta ε) * (quotientCharacterEquiv
        (diamond.twoLinePairing ε ε h φ φ a b 0 0 (fun q => (f q : ℂ)))).1.im) poleBoundaryHeights atTop := by
  intro φ
  obtain ⟨ψ,hψ,hunit,hR,hf,hs,hone,hbare⟩ := diamond.cone_square_smooth_radial_probe ε
  let f (q : MassiveMomentum) := ψ (coneEuclideanRadius q)
  let g (q : MassiveMomentum) := (f q : ℂ)
  let d := a+b
  have hg : ContDiff ℝ 2 g := Complex.ofRealCLM.contDiff.comp (contDiff_infty.mp hf 2)
  have hgs : HasCompactSupport g := hs.comp_left Complex.ofReal_zero
  let w := fun q : MassiveMomentum => shellSquare q.1 q.2
  let A (h : Height) := (quotientCharacterEquiv (diamond.twoLinePairing ε ε h φ φ a b 0 0 g)).1
  let Q (h : Height) := ∫ q, g q * (diamond.poleCoefficient ε h (w q))^2
  let J (h : Height) := ∫ q, f q • ((diamond.stableShellRoot ε h (w q))⁻¹)^3
  let U (h : Height) := -((d:ℂ)^2/2) * (∫ q, g q * diamond.poleCoefficient ε h (w q)) +
    ∫ q, g q * stableSquareResidual d (diamond.shiftedShellCoefficient ε h (w q))
  have har (h : Height) : A h + Q h = (d:ℂ)*J h - U h := by
    dsimp only [A]
    rw [diamond.same_stable_pairing_readout ε ha hb 0 h hg.continuous hgs]
    simp only [directed,AlgEquiv.apply_symm_apply,massiveD,zero_pow (by decide : (2:ℕ) ≠ 0),sub_zero]
    rw [diamond.stable_square_test_split ε h (a+b) hg.continuous hgs]
    have hh : (∫ q, g q * (-(d:ℂ)/(diamond.stableShellRoot ε h (w q))^3)) = -(d:ℂ)*J h := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      refine Eventually.of_forall fun q => ?_
      dsimp only [g,J]; rw [Complex.real_smul,div_eq_mul_inv,inv_pow]; ring
    dsimp only [U,Q]
    change -(_ + (∫ q, g q * (-(d:ℂ)/(diamond.stableShellRoot ε h (w q))^3)) - _ + _) + _ = _
    rw [hh]
    dsimp only [w,d]; ring
  obtain ⟨L,hL,hJ⟩ := diamond.radial_fractional_uniform ε hψ hR
  have hup := ((diamond.bare_complex_shell_boundary ε (m := 0) le_rfl hg hgs).const_mul (-((d:ℂ)^2/2))).add
    (diamond.stable_square_residual_full_momentum ε (add_nonneg ha hb) hg.continuous hgs).2
  have hU : ∃ z, Tendsto U poleBoundaryHeights (𝓝 z) := by
    refine ⟨-((d:ℂ)^2/2) * bareComplexShellBoundary (diamond.eta ε) 0 g +
      ∫ q, g q * stableSquareBoundaryResidual (diamond.eta ε) (a+b) (w q),?_⟩
    simpa only [U,w,massiveD,zero_pow (by decide : (2:ℕ) ≠ 0),sub_zero] using hup
  obtain ⟨z,hz⟩ := hU
  let C := ‖(d:ℂ)‖*L + (‖z‖+1)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hbnd : ∀ᶠ h in poleBoundaryHeights, ‖A h+Q h‖ ≤ C := by
    filter_upwards [hz.norm.eventually (gt_mem_nhds (by linarith : ‖z‖ < ‖z‖+1))] with h hu
    rw [har]
    apply (norm_sub_le _ _).trans
    rw [norm_mul]
    exact add_le_add (mul_le_mul_of_nonneg_left (hJ h) (norm_nonneg _)) hu.le
  obtain ⟨D,hD⟩ := diamond.cone_square_pairing_log_budget ε zero_lt_one (by norm_num : (1:ℝ) ≤ 2)
    zero_lt_one hψ hunit hR
  refine ⟨f,hf,hs,hone,⟨C,hC,hbnd⟩,⟨C+D,?_⟩,?_⟩
  · filter_upwards [hbnd,pole_height_tendsto_zero.eventually (gt_mem_nhds zero_lt_one)] with h hh ht
    change (h:ℝ) < 1 at ht
    have hbareBound := hD h (by simpa only [one_pow] using ht.le)
    have hq : Q h = diamond.coneSquarePairing ε h ψ := by
      simp only [Q,g,f,w,Plane.coneSquarePairing,Complex.real_smul]
    change ‖(A h).im + diamond.eta ε * Real.pi^2 * Real.log (1 / (h:ℝ))‖ ≤ C+D
    rw [← hq] at hbareBound
    calc
      _ = ‖(A h+Q h).im - ((Q h).im-diamond.eta ε*Real.pi^2*Real.log (1/(h:ℝ)))‖ := by rw [Complex.add_im]; congr 1; ring
      _ ≤ _ := (norm_sub_le _ _).trans (add_le_add ((Complex.abs_im_le_norm _).trans hh) hbareBound)
  have hQ : Tendsto (fun h => diamond.eta ε*(Q h).im) poleBoundaryHeights atTop := by
    simpa only [Plane.coneSquarePairing,Q,g,f,w,Complex.real_smul] using hbare
  have hη : |diamond.eta ε| = 1 := by
    rw [← Real.sqrt_sq_eq_abs,diamond.eta_sq,Real.sqrt_one]
  apply tendsto_atTop.2
  intro B
  filter_upwards [hQ.eventually_ge_atTop (B+C),hbnd] with h hlarge hsmall
  have hu : diamond.eta ε*(A h+Q h).im ≤ C := by
    calc
      _ ≤ |diamond.eta ε*(A h+Q h).im| := le_abs_self _
      _ = |(A h+Q h).im| := by rw [abs_mul,hη,one_mul]
      _ ≤ _ := (Complex.abs_im_le_norm _).trans hsmall
  rw [Complex.add_im,mul_add] at hu
  change B ≤ -(diamond.eta ε)*(A h).im
  linarith

theorem Plane.massless_same_side_stable_no_boundary (diamond : Plane E) (ε : Evolution) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    let φ := fun z => Complex.exp (-principalSqrt z)
    ∃ f : MassiveMomentum → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
      ¬∃ z, Tendsto (fun h => diamond.twoLinePairing ε ε h φ φ a b 0 0 (fun q => (f q : ℂ)))
        poleBoundaryHeights (𝓝 z) := by
  intro φ
  obtain ⟨f,hf,hs,_,_,_,H⟩ := diamond.massless_stable_square_log_witness ε ha hb
  refine ⟨f,hf,hs,?_⟩
  rintro ⟨z,hz⟩
  letI : poleBoundaryHeights.NeBot := pole_boundary_heights_neBot
  have hr : Continuous (fun x : QuotientCarrier => (quotientCharacterEquiv x).1.im) :=
    Complex.continuous_im.comp (continuous_fst.comp quotientCharacterIsometry.continuous)
  exact not_tendsto_atTop_of_tendsto_nhds ((hr.continuousAt.tendsto.comp hz).const_mul (-(diamond.eta ε))) H

end UV.SectorPlane
