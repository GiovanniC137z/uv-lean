import UV.SectorPlanePinch

/-! Opposite-side stable-half lines in the original directed algebra. The
root has a continuous extension from each prescribed side, including the
branch edge. On coincident shells the two on-shell phases subtract. -/

noncomputable section

namespace UV.SectorPlane

open Filter MeasureTheory Set UV.Carrier UV.RevisionSpectrum
open scoped Topology

set_option maxHeartbeats 800000

variable {E : Type*} [NormedAddCommGroup E]

/-- An extension off the positive-height domain used only to take the
one-sided limit. On the physical domain it is the prescribed principal root. -/
def sideRootExtension (η h w : ℝ) : ℂ :=
  if η = 1 then star (spectralRootUpper (-w) h) else spectralRootUpper (-w) h

theorem side_root_extension_continuous (η : ℝ) :
    Continuous (Function.uncurry (sideRootExtension η)) := by
  unfold sideRootExtension
  split_ifs <;> unfold Function.uncurry spectralRootUpper <;> fun_prop

theorem Plane.side_root_extension_positive (diamond : Plane E) (ε : Evolution) (h : Height) (w : ℝ) :
    sideRootExtension (diamond.eta ε) h w = diamond.stableShellRoot ε h w := by
  have hη : diamond.eta ε = 1 ∨ diamond.eta ε = -1 :=
    eq_or_eq_neg_of_sq_eq_sq _ 1 (by simp)
  rcases hη with he | he
  · have hz : -(diamond.shiftedShellCoefficient ε h w) = ((-w:ℝ):ℂ) - (h:ℂ)*Complex.I := by
      simp [Plane.shiftedShellCoefficient,he]; ring
    rw [Plane.stableShellRoot,hz,principalSqrt_lower_eq _ h.property]
    simp [sideRootExtension,he]
  · have hz : -(diamond.shiftedShellCoefficient ε h w) = ((-w:ℝ):ℂ) + (h:ℂ)*Complex.I := by
      simp [Plane.shiftedShellCoefficient,he]; ring
    rw [Plane.stableShellRoot,hz,principalSqrt_upper_eq _ h.property]
    norm_num [sideRootExtension,he]

private theorem root_slice_continuous (η w : ℝ) : Continuous (fun h : ℝ => sideRootExtension η h w) := by
  change Continuous (Function.uncurry (sideRootExtension η) ∘ (fun h : ℝ => (h,w)))
  exact (side_root_extension_continuous _).comp (continuous_id.prodMk continuous_const)

theorem Plane.side_root_extension_boundary (diamond : Plane E) (ε : Evolution) (w : ℝ) :
    sideRootExtension (diamond.eta ε) 0 w = stableShellBoundaryRoot (diamond.eta ε) w := by
  letI : poleBoundaryHeights.NeBot := pole_boundary_heights_neBot
  have H : Continuous (fun h : ℝ => sideRootExtension (diamond.eta ε) h w) :=
    root_slice_continuous _ _
  apply tendsto_nhds_unique (f := fun h : Height => sideRootExtension (diamond.eta ε) h w)
    (H.continuousAt.tendsto.comp pole_height_tendsto_zero)
  exact (diamond.stable_shell_root_tendsto ε w).congr fun h => (diamond.side_root_extension_positive ε h w).symm

/-- Unequal nonnegative depths retain a pure phase in the leading residue.
Equal depths give exactly the bare shell weight at every nonnegative mass. -/
theorem Plane.stable_half_pinch_residue (diamond : Plane E) (ε₁ ε₂ : Evolution)
    (hη : diamond.eta ε₂ = -diamond.eta ε₁) {a₁ a₂ m : ℝ} (h₁ : 0 ≤ a₁) (h₂ : 0 ≤ a₂) (hm : 0 ≤ m)
    {f : MassiveMomentum → ℂ} (hf : Continuous f) (hs : HasCompactSupport f) :
    let φ := fun z => Complex.exp (-principalSqrt z)
    let phase := Complex.exp (Complex.I * (diamond.eta ε₁ : ℂ) * ((a₁-a₂:ℝ):ℂ) * (m:ℂ))
    Tendsto (fun h : Height => directed (h : ℂ) * diamond.twoLinePairing ε₁ ε₂ h φ φ a₁ a₂ m m f)
      poleBoundaryHeights (𝓝 (directed ((Real.pi : ℂ) * (phase * complexShellTest m f)))) := by
  intro φ phase
  let V (ε : Evolution) (a t : ℝ) (q : MassiveMomentum) :=
    Complex.exp (-(a:ℂ) * sideRootExtension (diamond.eta ε) t (shellSquare q.1 q.2))
  have cont (ε : Evolution) (a : ℝ) : Continuous (Function.uncurry (V ε a)) := by
    have hw : Continuous (fun y : ℝ × MassiveMomentum => (y.1, shellSquare y.2.1 y.2.2)) :=
      continuous_fst.prodMk (shellSquare_continuous.comp continuous_snd)
    have hr := (side_root_extension_continuous (diamond.eta ε)).comp hw
    exact Complex.continuous_exp.comp ((continuous_const (y := -(a:ℂ))).mul hr)
  have eqV (ε : Evolution) {a : ℝ} (ha : 0 ≤ a) (h : Height) (q : MassiveMomentum) :
      diamond.scalarKernelReadout ε a φ h (shellSquare q.1 q.2) = V ε a h q := by
    rw [diamond.stable_scalar_kernel_readout ε ha h, Plane.stableHalfCoefficient, dif_pos h.property,
      diamond.stable_half_numerator_characters]
    dsimp only [V]
    rw [diamond.side_root_extension_positive]
    rfl
  have hsign : -(diamond.eta ε₁ : ℂ)*(diamond.eta ε₂ : ℂ) = 1 := by
    rw [hη,Complex.ofReal_neg,neg_mul_neg,← sq]
    exact_mod_cast diamond.eta_sq ε₁
  apply diamond.opposite_product_residue ε₁ ε₂ hη m a₁ a₂ φ φ
    (fun t q => V ε₁ a₁ t q * V ε₂ a₂ t q) ((cont _ _).mul (cont _ _)) ?_ ?_ hf hs
  · intro h
    funext q
    change -(diamond.eta ε₁ : ℂ)*(diamond.eta ε₂ : ℂ) *
      (diamond.scalarKernelReadout ε₁ a₁ φ h (shellSquare q.1 q.2) *
       diamond.scalarKernelReadout ε₂ a₂ φ h (shellSquare q.1 q.2)) = _
    rw [hsign,one_mul,eqV _ h₁,eqV _ h₂]
  · intro q hq
    have hmass : shellSquare q.1 q.2 = m^2 := sub_eq_zero.mp hq
    dsimp only [V]
    rw [hmass,diamond.side_root_extension_boundary,diamond.side_root_extension_boundary]
    change stableSideValue _ _ (m^2) * stableSideValue _ _ (m^2) = _
    rw [stable_side_value_at_mass _ _ hm,stable_side_value_at_mass _ _ hm,← Complex.exp_add]
    unfold phase; rw [hη]; push_cast; congr 1; ring

theorem Plane.stable_half_pinch_no_boundary (diamond : Plane E) (ε₁ ε₂ : Evolution)
    (hη : diamond.eta ε₂ = -diamond.eta ε₁) {a₁ a₂ m : ℝ} (h₁ : 0 ≤ a₁) (h₂ : 0 ≤ a₂) (hm : 0 ≤ m)
    {f : MassiveMomentum → ℂ} (hf : Continuous f) (hs : HasCompactSupport f) (hw : complexShellTest m f ≠ 0) :
    let φ := fun z => Complex.exp (-principalSqrt z)
    ¬∃ z, Tendsto (fun h => diamond.twoLinePairing ε₁ ε₂ h φ φ a₁ a₂ m m f) poleBoundaryHeights (𝓝 z) := by
  intro φ
  exact nonzero_pinch_excludes_boundary (mul_ne_zero (by exact_mod_cast Real.pi_ne_zero)
    (mul_ne_zero (Complex.exp_ne_zero _) hw)) (diamond.stable_half_pinch_residue ε₁ ε₂ hη h₁ h₂ hm hf hs)

end UV.SectorPlane
