import UV.SectorPlaneScalarProduct
import UV.SectorPlaneShellConcentration

/-! The leading opposite-side pinch for two co-routed scalar lines on a
fixed sector plane, including the common massless shell. A nonzero shell
residue obstructs a finite boundary on that test. -/

noncomputable section

namespace UV.SectorPlane

open Filter MeasureTheory Set UV.Carrier
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E]

theorem Plane.opposite_pole_poisson (diamond : Plane E) (ε₁ ε₂ : Evolution)
    (hη : diamond.eta ε₂ = -diamond.eta ε₁) (h : Height) (D : ℝ) :
    (h : ℂ) * (diamond.poleCoefficient ε₁ h D * diamond.poleCoefficient ε₂ h D) =
      (polePoisson h D : ℂ) := by
  have hs : (diamond.eta ε₁ : ℂ)^2 = 1 := by exact_mod_cast diamond.eta_sq ε₁
  have hz : diamond.shiftedShellCoefficient ε₁ h D * diamond.shiftedShellCoefficient ε₂ h D =
      ((D^2+(h:ℝ)^2 : ℝ) : ℂ) := by
    simp only [Plane.shiftedShellCoefficient,hη,Complex.ofReal_mul,Complex.ofReal_neg,Complex.ofReal_add,Complex.ofReal_pow]
    ring_nf
    rw [hs, Complex.I_sq]
    ring
  rw [diamond.pole_coefficient_eq_inv, diamond.pole_coefficient_eq_inv, ← mul_inv, hz]
  simp [polePoisson, div_eq_mul_inv]

/-- An admissible continuous extension is required only on the chosen side
of each branch. The height in the numerator is the one in both poles. -/
theorem Plane.opposite_product_residue (diamond : Plane E) (ε₁ ε₂ : Evolution)
    (hη : diamond.eta ε₂ = -diamond.eta ε₁) (m a₁ a₂ : ℝ) (φ₁ φ₂ : ℂ → ℂ)
    (U : ℝ → MassiveMomentum → ℂ) (hc : Continuous (Function.uncurry U))
    (he : ∀ h : Height, diamond.twoLineNumerator ε₁ ε₂ φ₁ φ₂ a₁ a₂ h = U h)
    {c : ℂ} (hshell : ∀ q, massiveD m q = 0 → U 0 q = c)
    {f : MassiveMomentum → ℂ} (hf : Continuous f) (hs : HasCompactSupport f) :
    Tendsto (fun h : Height => directed (h : ℂ) * diamond.twoLinePairing ε₁ ε₂ h φ₁ φ₂ a₁ a₂ m m f)
      poleBoundaryHeights (𝓝 (directed ((Real.pi : ℂ) * (c * complexShellTest m f)))) := by
  have H := moving_poisson_shell_limit m U hc hf hs
  have eq : complexShellTest m (fun q => U 0 q*f q) = c * complexShellTest m f := by
    rw [← complex_shell_test_const_mul m hf hs c]
    exact complex_shell_test_congr (fun q hq => by rw [hshell q hq])
  rw [eq] at H
  apply (directed_shell_readout_continuous.continuousAt.tendsto.comp H).congr
  intro h
  have hU : Continuous (diamond.twoLineNumerator ε₁ ε₂ φ₁ φ₂ a₁ a₂ h) := by
    rw [he]; exact hc.comp ((continuous_const (y := (h:ℝ))).prodMk continuous_id)
  rw [diamond.two_line_pairing_readout ε₁ ε₂ h φ₁ φ₂ a₁ a₂ m m hf hs hU, ← directed_mul, ← integral_const_mul]
  apply congrArg directed
  apply integral_congr_ae
  refine Eventually.of_forall fun q => ?_
  dsimp only
  rw [he, ← diamond.opposite_pole_poisson ε₁ ε₂ hη h (massiveD m q)]
  ring

theorem Plane.continuous_profile_pinch (diamond : Plane E) (ε₁ ε₂ : Evolution)
    (hη : diamond.eta ε₂ = -diamond.eta ε₁) (m a₁ a₂ : ℝ) {φ₁ φ₂ : ℂ → ℂ}
    (h₁ : Continuous φ₁) (h₂ : Continuous φ₂) {f : MassiveMomentum → ℂ} (hf : Continuous f) (hs : HasCompactSupport f) :
    let c := φ₁ (-(a₁:ℂ)^2*(m:ℂ)^2) * φ₂ (-(a₂:ℂ)^2*(m:ℂ)^2)
    Tendsto (fun h : Height => directed (h : ℂ) * diamond.twoLinePairing ε₁ ε₂ h φ₁ φ₂ a₁ a₂ m m f)
      poleBoundaryHeights (𝓝 (directed ((Real.pi : ℂ) * (c * complexShellTest m f)))) := by
  intro c
  apply diamond.opposite_product_residue ε₁ ε₂ hη m a₁ a₂ φ₁ φ₂
    (diamond.twoLineNumerator ε₁ ε₂ φ₁ φ₂ a₁ a₂) ?_ (fun _ => rfl) ?_ hf hs
  · have hz (ε : Evolution) (a : ℝ) : Continuous (fun y : ℝ × MassiveMomentum => -(a:ℂ)^2 *
        ((shellSquare y.2.1 y.2.2 : ℂ) + Complex.I * ((diamond.eta ε*y.1 : ℝ) : ℂ))) :=
      continuous_const.mul ((Complex.continuous_ofReal.comp (shellSquare_continuous.comp continuous_snd)).add
        (continuous_const.mul (Complex.continuous_ofReal.comp (continuous_const.mul continuous_fst))))
    exact continuous_const.mul ((h₁.comp (hz ε₁ a₁)).mul (h₂.comp (hz ε₂ a₂)))
  · intro q hq
    have he : shellSquare q.1 q.2 = m^2 := sub_eq_zero.mp hq
    have hsign : -(diamond.eta ε₁ : ℂ)*(diamond.eta ε₂ : ℂ) = 1 := by
      rw [hη, Complex.ofReal_neg, neg_mul_neg, ← sq]
      exact_mod_cast diamond.eta_sq ε₁
    simp [Plane.twoLineNumerator, he, hsign, c]

/-- A nonzero residue gives failure of the unscaled boundary integral
in the original two-character algebra. -/
theorem nonzero_pinch_excludes_boundary {F : Height → QuotientCarrier} {c : ℂ} (hc : c ≠ 0)
    (H : Tendsto (fun h : Height => directed (h : ℂ) * F h) poleBoundaryHeights (𝓝 (directed c))) :
    ¬∃ z, Tendsto F poleBoundaryHeights (𝓝 z) := by
  letI : poleBoundaryHeights.NeBot := pole_boundary_heights_neBot
  rintro ⟨z,hz⟩
  have ht : Tendsto (fun h : Height => directed (h : ℂ)) poleBoundaryHeights (𝓝 (directed (0 : ℂ))) :=
    directed_shell_readout_continuous.continuousAt.tendsto.comp
      (Complex.continuous_ofReal.continuousAt.tendsto.comp pole_height_tendsto_zero)
  have he := tendsto_nhds_unique H (ht.mul hz)
  have h' := congrArg (fun x : QuotientCarrier => (quotientCharacterEquiv x).1) he
  exact hc (by simpa [directed] using h')

end UV.SectorPlane
