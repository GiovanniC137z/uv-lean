import UV.SectorPlaneResolventProduct
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! Separated translated mass shells on the same locked sector plane.
The algebraic decomposition is applied at the common positive pole height,
with a smooth extension of its coefficients off the compact test support. -/

noncomputable section

namespace UV.SectorPlane

open Filter MeasureTheory Set
open scoped Topology ContDiff UV.SectorPlane

variable {E : Type*} [NormedAddCommGroup E]

def shiftedD (m : ℝ) (c q : MassiveMomentum) : ℝ :=
  massiveD m (q + c)

theorem shiftedD_contDiff {n : WithTop ℕ∞} (m : ℝ) (c : MassiveMomentum) :
    ContDiff ℝ n (shiftedD m c) := by
  have h : ContDiff ℝ n (fun q : MassiveMomentum => shellSquare q.1 q.2) :=
    (contDiff_fst.pow 2).sub (contDiff_snd.norm_sq ℝ)
  exact (h.comp (contDiff_id.add contDiff_const)).sub contDiff_const

theorem massive_momentum_translation_preserves_volume (c : MassiveMomentum) :
    MeasurePreserving (fun q : MassiveMomentum => q + c) volume volume := by
  letI : (volume : Measure MassiveMomentum).IsAddRightInvariant := by
    change ((volume : Measure ℝ).prod (volume : Measure Spatial)).IsAddRightInvariant
    infer_instance
  exact measurePreserving_add_right volume c

theorem Plane.shifted_bare_shell_boundary (diamond : Plane E) (ε : Evolution) {m : ℝ}
    (hm : 0 ≤ m) (c : MassiveMomentum) {f : MassiveMomentum → ℂ}
    (hf : ContDiff ℝ 2 f) (hs : HasCompactSupport f) :
    Tendsto (fun h : Height => ∫ q, f q * diamond.poleCoefficient ε h (shiftedD m c q))
      poleBoundaryHeights (𝓝 (bareComplexShellBoundary (diamond.eta ε) m (fun p => f (p - c)))) := by
  have hfs : HasCompactSupport (fun p => f (p - c)) := hs.comp_homeomorph (Homeomorph.subRight c)
  apply (diamond.bare_complex_shell_boundary ε hm (hf.comp (contDiff_id.sub contDiff_const)) hfs).congr
  intro h
  let F (p : MassiveMomentum) := f (p - c) * diamond.poleCoefficient ε h (massiveD m p)
  calc
    (∫ p, F p) = ∫ q, F (q + c) :=
      ((massive_momentum_translation_preserves_volume c).integral_comp
        (Homeomorph.addRight c).measurableEmbedding F).symm
    _ = _ := by simp only [F, add_sub_cancel_right, shiftedD]

/-- A smooth positive extension of the identity above the given margin. -/
def smoothPositiveFloor (δ x : ℝ) : ℝ :=
  δ + (x - δ) * Real.smoothTransition ((x - δ) / δ)

theorem smooth_positive_floor_contDiff (δ : ℝ) :
    ContDiff ℝ 2 (smoothPositiveFloor δ) :=
  contDiff_const.add ((contDiff_id.sub contDiff_const).mul
    (Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const δ)))

theorem smooth_positive_floor_pos {δ : ℝ} (hδ : 0 < δ) (x : ℝ) : 0 < smoothPositiveFloor δ x := by
  by_cases hx : x ≤ δ
  · simp only [smoothPositiveFloor, Real.smoothTransition.zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx) hδ.le), mul_zero, add_zero]
    exact hδ
  · exact add_pos_of_pos_of_nonneg hδ (mul_nonneg (sub_nonneg.mpr (le_of_lt (lt_of_not_ge hx))) (Real.smoothTransition.nonneg _))

theorem smooth_positive_floor_eq {δ x : ℝ} (hδ : 0 < δ) (hx : 2 * δ ≤ x) : smoothPositiveFloor δ x = x := by
  have he := Real.smoothTransition.one_of_one_le (show 1 ≤ (x - δ) / δ from (le_div_iff₀ hδ).mpr (by linarith))
  simp only [smoothPositiveFloor, he, mul_one]
  ring

theorem compact_positive_margin (K : TopologicalSpace.Compacts MassiveMomentum)
    {F : MassiveMomentum → ℝ} (hF : Continuous F) (h : ∀ q ∈ K, 0 < F q) :
    ∃ δ > 0, ∀ q ∈ K, 2 * δ ≤ F q := by
  by_cases hh : (K : Set MassiveMomentum).Nonempty
  · obtain ⟨q, hq, hmin⟩ := K.isCompact.exists_isMinOn hh hF.continuousOn
    refine ⟨F q / 2, by linarith [h q hq], fun p hp => ?_⟩
    have he : F q ≤ F p := hmin hp
    linarith
  · exact ⟨1, zero_lt_one, fun p hp => (hh ⟨p, hp⟩).elim⟩

private theorem shifted_shell_split (diamond : Plane E) (ε₁ ε₂ : Evolution) (h : Height)
    (D₁ D₂ : ℝ) :
    let A : ℂ := (D₁ ^ 2 + D₂ ^ 2 + 2 * (h : ℝ) ^ 2 : ℝ)
    (diamond.poleCoefficient ε₁ h D₁ * diamond.poleCoefficient ε₂ h D₂) * A =
      ((D₂ : ℂ) - Complex.I * ((diamond.eta ε₂ * (h : ℝ) : ℝ) : ℂ)) * diamond.poleCoefficient ε₁ h D₁ +
      ((D₁ : ℂ) - Complex.I * ((diamond.eta ε₁ * (h : ℝ) : ℝ) : ℂ)) * diamond.poleCoefficient ε₂ h D₂ := by
  intro A
  let Z₁ := diamond.shiftedShellCoefficient ε₁ h D₁
  let Z₂ := diamond.shiftedShellCoefficient ε₂ h D₂
  have h₁ : Z₁ ≠ 0 := diamond.shifted_denominator_ne_zero ε₁ h D₁
  have h₂ : Z₂ ≠ 0 := diamond.shifted_denominator_ne_zero ε₂ h D₂
  let C₁ := (D₁ : ℂ) - Complex.I * ((diamond.eta ε₁ * (h : ℝ) : ℝ) : ℂ)
  let C₂ := (D₂ : ℂ) - Complex.I * ((diamond.eta ε₂ * (h : ℝ) : ℝ) : ℂ)
  have hZ (ε : Evolution) (D : ℝ) :
      diamond.shiftedShellCoefficient ε h D *
        ((D : ℂ) - Complex.I * ((diamond.eta ε * (h : ℝ) : ℝ) : ℂ)) = ((D ^ 2 + (h : ℝ) ^ 2 : ℝ) : ℂ) := by
    have hs : (diamond.eta ε : ℂ) ^ 2 = 1 := by exact_mod_cast diamond.eta_sq ε
    unfold Plane.shiftedShellCoefficient
    push_cast
    calc
      _ = (D : ℂ)^2 - Complex.I^2 * (diamond.eta ε : ℂ)^2 * ((h:ℝ):ℂ)^2 := by ring
      _ = _ := by rw [Complex.I_sq, hs]; ring
  have he : A = Z₁ * C₁ + Z₂ * C₂ := by
    dsimp only [Z₁, Z₂, C₁, C₂]
    rw [hZ, hZ]
    dsimp only [A]
    push_cast
    ring
  simp only [diamond.pole_coefficient_eq_inv]
  change (Z₁⁻¹ * Z₂⁻¹) * A = C₂ * Z₁⁻¹ + C₁ * Z₂⁻¹
  rw [he]
  field_simp
  ring

/-- On a compact test domain without a common zero of the two actual routed
shells, every jointly C² numerator gives a boundary of order at most two.
The result holds at every pair of nonnegative masses and prescribed sides. -/
theorem Plane.shifted_separated_product_distribution (diamond : Plane E) (ε₁ ε₂ : Evolution)
    (K : TopologicalSpace.Compacts MassiveMomentum) (c₁ c₂ : MassiveMomentum) {m₁ m₂ : ℝ}
    (hm₁ : 0 ≤ m₁) (hm₂ : 0 ≤ m₂) (hsep : ∀ q ∈ K, shiftedD m₁ c₁ q ≠ 0 ∨ shiftedD m₂ c₂ q ≠ 0)
    (U : ℝ → MassiveMomentum → ℂ) (hU : ContDiff ℝ 2 (Function.uncurry U)) :
    ∃ T : CompactMomentumTest K →L[ℂ] ℂ, ∀ f : CompactMomentumTest K,
      Tendsto (fun h : Height => ∫ q, f.value q * (U h q *
        (diamond.poleCoefficient ε₁ h (shiftedD m₁ c₁ q) * diamond.poleCoefficient ε₂ h (shiftedD m₂ c₂ q))))
        poleBoundaryHeights (𝓝 (T f)) := by
  let D₁ := shiftedD m₁ c₁
  let D₂ := shiftedD m₂ c₂
  have hd₁ : ContDiff ℝ 2 D₁ := shiftedD_contDiff ..
  have hd₂ : ContDiff ℝ 2 D₂ := shiftedD_contDiff ..
  let S (q : MassiveMomentum) := D₁ q ^ 2 + D₂ q ^ 2
  have hS : ContDiff ℝ 2 S := (hd₁.pow 2).add (hd₂.pow 2)
  obtain ⟨δ,hδ,hmin⟩ := compact_positive_margin K hS.continuous (fun q hq => by
    rcases hsep q hq with h | h
    · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero h) (sq_nonneg _)
    · exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero h))
  let A (x : ℝ × MassiveMomentum) := smoothPositiveFloor δ (S x.2 + 2 * x.1 ^ 2)
  have hA : ContDiff ℝ 2 A := (smooth_positive_floor_contDiff δ).comp
    ((hS.comp contDiff_snd).add (contDiff_const.mul (contDiff_fst.pow 2)))
  have hn (x : ℝ × MassiveMomentum) : (A x : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (smooth_positive_floor_pos hδ _).ne'
  let C (ε : Evolution) (D : MassiveMomentum → ℝ) (x : ℝ × MassiveMomentum) :=
    (D x.2 : ℂ) - Complex.I * ((diamond.eta ε * x.1 : ℝ) : ℂ)
  have hC (ε : Evolution) {D : MassiveMomentum → ℝ} (hd : ContDiff ℝ 2 D) : ContDiff ℝ 2 (C ε D) :=
    (Complex.ofRealCLM.contDiff.comp (hd.comp contDiff_snd)).sub (contDiff_const.mul
      (Complex.ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_fst)))
  let V (ε : Evolution) (D : MassiveMomentum → ℝ) (t : ℝ) (q : MassiveMomentum) :=
    U t q * C ε D (t,q) / (A (t,q) : ℂ)
  have hV (ε : Evolution) {D : MassiveMomentum → ℝ} (hd : ContDiff ℝ 2 D) :
      ContDiff ℝ 2 (Function.uncurry (V ε D)) :=
    by
      simp only [V, div_eq_mul_inv]
      exact (hU.mul (hC ε hd)).mul ((Complex.ofRealCLM.contDiff.comp hA).inv hn)
  let P (ε : Evolution) (m : ℝ) (c : MassiveMomentum) (h : Height) (q : MassiveMomentum) :=
    diamond.poleCoefficient ε h (shiftedD m c q)
  have hp (ε : Evolution) (m : ℝ) (c : MassiveMomentum) (h : Height) : Continuous (P ε m c h) :=
    (diamond.pole_coefficient_continuous ε h).comp (shiftedD_contDiff (n := 1) m c).continuous
  have hlim (ε : Evolution) {m : ℝ} (hm : 0 ≤ m) (c : MassiveMomentum) (V₀ : ℝ → MassiveMomentum → ℂ)
      (hv : ContDiff ℝ 2 (Function.uncurry V₀)) :=
    compact_momentum_multiplier_distribution K (P ε m c)
      (fun h => (hp ε m c h).continuousOn.integrableOn_compact K.isCompact)
      (fun f => ⟨_, diamond.shifted_bare_shell_boundary ε hm c f.contDiff f.compact_support⟩) V₀ hv
  obtain ⟨T₁,H₁⟩ := hlim ε₁ hm₁ c₁ (V ε₂ D₂) (hV ε₂ hd₂)
  obtain ⟨T₂,H₂⟩ := hlim ε₂ hm₂ c₂ (V ε₁ D₁) (hV ε₁ hd₁)
  refine ⟨T₁+T₂, fun f => ((H₁ f).add (H₂ f)).congr fun h => ?_⟩
  have hi (ε κ : Evolution) (m : ℝ) (c : MassiveMomentum) {D : MassiveMomentum → ℝ} (hd : ContDiff ℝ 2 D) :
      Integrable (fun q => f.value q * (V κ D h q * P ε m c h q)) :=
    (f.contDiff.continuous.mul (((hV κ hd).continuous.comp (continuous_const.prodMk continuous_id)).mul
      (hp ε m c h))).integrable_of_hasCompactSupport f.compact_support.mul_right
  rw [← integral_add (hi ε₁ ε₂ m₁ c₁ hd₂) (hi ε₂ ε₁ m₂ c₂ hd₁)]
  apply integral_congr_ae
  refine Eventually.of_forall fun q => ?_
  by_cases hq : q ∈ K
  · have he : A (h,q) = S q + 2 * (h : ℝ)^2 := smooth_positive_floor_eq hδ
      ((hmin q hq).trans (le_add_of_nonneg_right (by positivity)))
    have hsplit := shifted_shell_split diamond ε₁ ε₂ h (D₁ q) (D₂ q)
    change f.value q * (U h q * C ε₂ D₂ (h,q) / (A (h,q) : ℂ) * P ε₁ m₁ c₁ h q) +
      f.value q * (U h q * C ε₁ D₁ (h,q) / (A (h,q) : ℂ) * P ε₂ m₂ c₂ h q) =
      f.value q * (U h q * (P ε₁ m₁ c₁ h q * P ε₂ m₂ c₂ h q))
    apply (mul_right_cancel₀ (hn (h,q)))
    rw [add_mul]
    have ec (x y z : ℂ) : x * (y / (A (h,q):ℂ) * z) * (A (h,q):ℂ) = x*y*z := by
      rw [div_eq_mul_inv]
      calc
        _ = x*y*z * ((A (h,q):ℂ)⁻¹ * (A (h,q):ℂ)) := by ring
        _ = _ := by rw [inv_mul_cancel₀ (hn (h,q)),mul_one]
    rw [ec,ec,he]
    dsimp only [C,P,S] at hsplit ⊢
    linear_combination -(f.value q * U h q) * hsplit
  · have hz : f.value q = 0 := f.property.1 q hq
    simp only [hz, zero_mul, add_zero]

end UV.SectorPlane
