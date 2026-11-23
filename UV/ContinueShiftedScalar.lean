import UV.ContinueShiftedShellGeometry
import UV.SectorPlaneStableProduct

/-! The literal pair of translated scalar lines. The two running units
are evaluated at their own routed momenta. A smooth representative of
their product is used only on compact supports where it is exact. -/

noncomputable section

namespace UV.SectorPlane

open Filter MeasureTheory Set UV.Carrier
open scoped Topology ContDiff UV.SectorPlane

variable {E : Type*} [NormedAddCommGroup E]

def Plane.shiftedScalarPairing (diamond : Plane E) (ε₁ ε₂ : Evolution) (h : Height)
    (φ₁ φ₂ : ℂ → ℂ) (a₁ a₂ m₁ m₂ : ℝ) (c₁ c₂ : MassiveMomentum) (f : MassiveMomentum → ℂ) : QuotientCarrier :=
  ∫ q : MassiveMomentum, directed (f q) *
    (if h₁ : (q+c₁).1 ≠ 0 then
      if h₂ : (q+c₂).1 ≠ 0 then
        diamond.scalarLine ε₁ h φ₁ a₁ m₁ (q+c₁).1 (q+c₁).2 h₁ *
          diamond.scalarLine ε₂ h φ₂ a₂ m₂ (q+c₂).1 (q+c₂).2 h₂
      else 0
    else 0)

theorem Plane.shifted_scalar_pairing_zero (diamond : Plane E) (ε₁ ε₂ : Evolution) (h : Height)
    (φ₁ φ₂ : ℂ → ℂ) (a₁ a₂ m₁ m₂ : ℝ) (f : MassiveMomentum → ℂ) :
    diamond.shiftedScalarPairing ε₁ ε₂ h φ₁ φ₂ a₁ a₂ m₁ m₂ 0 0 f =
      diamond.twoLinePairing ε₁ ε₂ h φ₁ φ₂ a₁ a₂ m₁ m₂ f := by
  unfold Plane.shiftedScalarPairing Plane.twoLinePairing
  apply integral_congr_ae
  refine Eventually.of_forall fun q => ?_
  by_cases hq : q.1 ≠ 0 <;> simp [hq]

def Plane.shiftedScalarNumerator (diamond : Plane E) (ε₁ ε₂ : Evolution) (h : Height)
    (φ₁ φ₂ : ℂ → ℂ) (a₁ a₂ : ℝ) (c₁ c₂ q : MassiveMomentum) : ℂ :=
  -(diamond.eta ε₁ : ℂ) * (diamond.eta ε₂ : ℂ) *
    (axialSign (q+c₁).1 : ℂ) * (axialSign (q+c₂).1 : ℂ) *
    (diamond.scalarKernelReadout ε₁ a₁ φ₁ h (shellSquare (q+c₁).1 (q+c₁).2) *
      diamond.scalarKernelReadout ε₂ a₂ φ₂ h (shellSquare (q+c₂).1 (q+c₂).2))

private theorem shifted_real_axial_nonzero_ae (c : MassiveMomentum) : ∀ᵐ q : MassiveMomentum ∂volume, (q+c).1 ≠ 0 := by
  exact (massive_momentum_translation_preserves_volume c).quasiMeasurePreserving.ae real_axial_nonzero_ae

theorem Plane.shifted_scalar_lines_readout (diamond : Plane E) (ε₁ ε₂ : Evolution) (h : Height)
    (φ₁ φ₂ : ℂ → ℂ) (a₁ a₂ m₁ m₂ : ℝ) (c₁ c₂ q : MassiveMomentum)
    (hq₁ : (q+c₁).1 ≠ 0) (hq₂ : (q+c₂).1 ≠ 0) :
    diamond.scalarLine ε₁ h φ₁ a₁ m₁ (q+c₁).1 (q+c₁).2 hq₁ *
      diamond.scalarLine ε₂ h φ₂ a₂ m₂ (q+c₂).1 (q+c₂).2 hq₂ =
      directed (diamond.shiftedScalarNumerator ε₁ ε₂ h φ₁ φ₂ a₁ a₂ c₁ c₂ q *
        (diamond.poleCoefficient ε₁ h (shiftedD m₁ c₁ q) * diamond.poleCoefficient ε₂ h (shiftedD m₂ c₂ q))) := by
  simp only [Plane.scalarLine, diamond.pole_inverse_complex, diamond.pole_coefficient_eq_inv, shiftedD, massiveD,
    ← directed_mul, Plane.shiftedScalarNumerator, Plane.scalarKernelReadout, Plane.shiftedShellCoefficient, Complex.ofReal_mul]
  congr 1
  ring_nf
  rw [Complex.I_sq]
  ring

/-- Read both original directed lines after integration. The comparison
numerator need only agree where the test is nonzero and the running units
are defined. -/
theorem Plane.shifted_scalar_pairing_eq_of_numerator (diamond : Plane E) (ε₁ ε₂ : Evolution)
    (h : Height) (φ₁ φ₂ : ℂ → ℂ) (a₁ a₂ m₁ m₂ : ℝ) (c₁ c₂ : MassiveMomentum)
    {f U : MassiveMomentum → ℂ}
    (hi : Integrable (fun q => f q * (U q *
      (diamond.poleCoefficient ε₁ h (shiftedD m₁ c₁ q) * diamond.poleCoefficient ε₂ h (shiftedD m₂ c₂ q)))))
    (hU : ∀ q, f q ≠ 0 → (q+c₁).1 ≠ 0 → (q+c₂).1 ≠ 0 →
      U q = diamond.shiftedScalarNumerator ε₁ ε₂ h φ₁ φ₂ a₁ a₂ c₁ c₂ q) :
    diamond.shiftedScalarPairing ε₁ ε₂ h φ₁ φ₂ a₁ a₂ m₁ m₂ c₁ c₂ f =
      directed (∫ q, f q * (U q *
        (diamond.poleCoefficient ε₁ h (shiftedD m₁ c₁ q) * diamond.poleCoefficient ε₂ h (shiftedD m₂ c₂ q)))) := by
  unfold Plane.shiftedScalarPairing
  rw [← directed_integral hi]
  apply integral_congr_ae
  filter_upwards [shifted_real_axial_nonzero_ae c₁,shifted_real_axial_nonzero_ae c₂] with q h₁ h₂
  simp only [dif_pos h₁,dif_pos h₂,diamond.shifted_scalar_lines_readout, ← directed_mul]
  by_cases hq : f q = 0
  · simp only [hq,zero_mul]
  · rw [hU q hq h₁ h₂]

private theorem shifted_scalar_boundary_of_comparison (diamond : Plane E) (ε₁ ε₂ : Evolution)
    (K : TopologicalSpace.Compacts MassiveMomentum) (c₁ c₂ : MassiveMomentum) {m₁ m₂ : ℝ}
    (hm₁ : 0 ≤ m₁) (hm₂ : 0 ≤ m₂) (hsep : ∀ q ∈ K, shiftedD m₁ c₁ q ≠ 0 ∨ shiftedD m₂ c₂ q ≠ 0)
    (φ₁ φ₂ : ℂ → ℂ) (a₁ a₂ : ℝ)
    (U : ℝ → MassiveMomentum → ℂ) (hU : ContDiff ℝ 2 (Function.uncurry U))
    (he : ∀ (h : Height) q, q ∈ K → (q+c₁).1 ≠ 0 → (q+c₂).1 ≠ 0 →
      U h q = diamond.shiftedScalarNumerator ε₁ ε₂ h φ₁ φ₂ a₁ a₂ c₁ c₂ q) :
    ∃ T : CompactMomentumTest K →L[ℂ] ℂ, ∀ f : CompactMomentumTest K,
      Tendsto (fun h => diamond.shiftedScalarPairing ε₁ ε₂ h φ₁ φ₂ a₁ a₂ m₁ m₂ c₁ c₂ f.value)
        poleBoundaryHeights (𝓝 (directed (T f))) := by
  obtain ⟨T,hT⟩ := diamond.shifted_separated_product_distribution ε₁ ε₂ K c₁ c₂ hm₁ hm₂ hsep U hU
  refine ⟨T, fun f => (directed_shell_readout_continuous.continuousAt.tendsto.comp (hT f)).congr fun h => ?_⟩
  let P (ε : Evolution) (m : ℝ) (c : MassiveMomentum) :=
    diamond.poleCoefficient ε h ∘ shiftedD m c
  have hp (ε : Evolution) (m : ℝ) (c : MassiveMomentum) : Continuous (P ε m c) :=
    (diamond.pole_coefficient_continuous ε h).comp (shiftedD_contDiff (n := 1) m c).continuous
  have hi : Integrable (fun q => f.value q * (U h q * (P ε₁ m₁ c₁ q * P ε₂ m₂ c₂ q))) :=
    (f.contDiff.continuous.mul ((hU.continuous.comp (continuous_const.prodMk continuous_id)).mul
      ((hp ε₁ m₁ c₁).mul (hp ε₂ m₂ c₂)))).integrable_of_hasCompactSupport f.compact_support.mul_right
  symm
  exact diamond.shifted_scalar_pairing_eq_of_numerator ε₁ ε₂ h φ₁ φ₂ a₁ a₂ m₁ m₂ c₁ c₂ hi
    (fun q hn h₁ h₂ => he h q (by by_contra hq; exact hn (f.property.1 q hq)) h₁ h₂)

/-- On a support separated from both axial-zero sets the two normalized
running signs have jointly smooth representatives. With equal axial
routing their product is exactly one almost everywhere. -/
private theorem shifted_running_signs_comparison (K : TopologicalSpace.Compacts MassiveMomentum)
    (c₁ c₂ : MassiveMomentum)
    (ha : c₁.1 = c₂.1 ∨ ∀ q ∈ K, (q+c₁).1 ≠ 0 ∧ (q+c₂).1 ≠ 0) :
    ∃ G : MassiveMomentum → ℂ, ContDiff ℝ 2 G ∧
      ∀ q ∈ K, (q+c₁).1 ≠ 0 → (q+c₂).1 ≠ 0 →
        G q = (axialSign (q+c₁).1 : ℂ) * (axialSign (q+c₂).1 : ℂ) := by
  rcases ha with he | hn
  · refine ⟨fun _ => 1, contDiff_const, fun q _ hq _ => ?_⟩
    have h : (q+c₂).1 = (q+c₁).1 := by simp only [Prod.fst_add,he]
    have hs : (axialSign (q+c₁).1 : ℂ)^2 = 1 := by
      exact_mod_cast (show (axialSign (q+c₁).1)^2 = 1 by rw [← sq_abs,axialSign_abs hq,one_pow])
    rw [h,← sq,hs]
  · let A (c q : MassiveMomentum) := (q+c).1
    have hA (c : MassiveMomentum) : ContDiff ℝ 2 (A c) := contDiff_fst.comp (contDiff_id.add contDiff_const)
    have hmargin (c : MassiveMomentum) (hc : ∀ q ∈ K, A c q ≠ 0) :=
      compact_positive_margin K (hA c).continuous.abs (fun q hq => abs_pos.mpr (hc q hq))
    obtain ⟨δ₁,hδ₁,hbound₁⟩ := hmargin c₁ (fun q hq => (hn q hq).1)
    obtain ⟨δ₂,hδ₂,hbound₂⟩ := hmargin c₂ (fun q hq => (hn q hq).2)
    let S (δ x : ℝ) := 2 * Real.smoothTransition ((x+δ) / (2*δ)) - 1
    have hS (δ : ℝ) : ContDiff ℝ 2 (S δ) :=
      (contDiff_const.mul (Real.smoothTransition.contDiff.comp ((contDiff_id.add contDiff_const).div_const _))).sub contDiff_const
    have heq {x δ : ℝ} (hδ : 0 < δ) (hx : 2 * δ ≤ |x|) : S δ x = axialSign x := by
      rcases le_total x 0 with hx₀ | hx₀
      · rw [abs_of_nonpos hx₀] at hx
        have hneg : x < 0 := by linarith
        simp [S,Real.smoothTransition.zero_of_nonpos
          (div_nonpos_of_nonpos_of_nonneg (by linarith : x+δ ≤ 0) (by positivity : 0 ≤ 2*δ)), axialSign, hneg,hneg.not_gt]
      · rw [abs_of_nonneg hx₀] at hx
        have hpos : 0 < x := by linarith
        simp [S,Real.smoothTransition.one_of_one_le
          ((le_div_iff₀ (by positivity : 0 < 2*δ)).mpr (by linarith : 1*(2*δ) ≤ x+δ)),axialSign,hpos]
        norm_num
    refine ⟨fun q => (S δ₁ (A c₁ q) : ℂ) * (S δ₂ (A c₂ q) : ℂ),
      (Complex.ofRealCLM.contDiff.comp ((hS δ₁).comp (hA c₁))).mul
        (Complex.ofRealCLM.contDiff.comp ((hS δ₂).comp (hA c₂))), fun q hq _ _ => ?_⟩
    change (S δ₁ (A c₁ q) : ℂ) * (S δ₂ (A c₂ q) : ℂ) = _
    rw [heq hδ₁ (hbound₁ q hq),heq hδ₂ (hbound₂ q hq)]

private theorem shifted_invariant_contDiff (c : MassiveMomentum) :
    ContDiff ℝ 2 (fun q : MassiveMomentum => shellSquare (q+c).1 (q+c).2) :=
  ((contDiff_fst.pow 2).sub (contDiff_snd.norm_sq ℝ)).comp (contDiff_id.add contDiff_const)

/-- Full translated pair for real-C² scalar profiles and separated poles.
This includes arbitrary spatial shifts across the axial-zero slice and
arbitrary shifts on supports separated from both axial-zero slices. -/
theorem Plane.shifted_smooth_scalar_distribution (diamond : Plane E) (ε₁ ε₂ : Evolution)
    (K : TopologicalSpace.Compacts MassiveMomentum) (c₁ c₂ : MassiveMomentum) {m₁ m₂ : ℝ}
    (hm₁ : 0 ≤ m₁) (hm₂ : 0 ≤ m₂) (hsep : ∀ q ∈ K, shiftedD m₁ c₁ q ≠ 0 ∨ shiftedD m₂ c₂ q ≠ 0)
    (hax : c₁.1 = c₂.1 ∨ ∀ q ∈ K, (q+c₁).1 ≠ 0 ∧ (q+c₂).1 ≠ 0)
    {φ₁ φ₂ : ℂ → ℂ} (hφ₁ : ContDiff ℝ 2 φ₁) (hφ₂ : ContDiff ℝ 2 φ₂) (a₁ a₂ : ℝ) :
    ∃ T : CompactMomentumTest K →L[ℂ] ℂ, ∀ f : CompactMomentumTest K,
      Tendsto (fun h => diamond.shiftedScalarPairing ε₁ ε₂ h φ₁ φ₂ a₁ a₂ m₁ m₂ c₁ c₂ f.value)
        poleBoundaryHeights (𝓝 (directed (T f))) := by
  obtain ⟨G,hG,hmatch⟩ := shifted_running_signs_comparison K c₁ c₂ hax
  let V (ε : Evolution) (φ : ℂ → ℂ) (a : ℝ) (c : MassiveMomentum) (x : ℝ × MassiveMomentum) :=
    φ (-(a : ℂ)^2 * ((shellSquare (x.2+c).1 (x.2+c).2 : ℂ) +
      Complex.I * ((diamond.eta ε*x.1 : ℝ) : ℂ)))
  have hc (ε : Evolution) {φ : ℂ → ℂ} (hφ : ContDiff ℝ 2 φ) (a : ℝ) (c : MassiveMomentum) :
      ContDiff ℝ 2 (V ε φ a c) :=
    hφ.comp (contDiff_const.mul
      ((Complex.ofRealCLM.contDiff.comp ((shifted_invariant_contDiff c).comp contDiff_snd)).add
        (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_fst)))))
  let d := -(diamond.eta ε₁ : ℂ) * (diamond.eta ε₂ : ℂ)
  let U (t : ℝ) (q : MassiveMomentum) := d * G q * (V ε₁ φ₁ a₁ c₁ (t,q) * V ε₂ φ₂ a₂ c₂ (t,q))
  have hU : ContDiff ℝ 2 (Function.uncurry U) :=
    (contDiff_const.mul (hG.comp contDiff_snd)).mul ((hc ε₁ hφ₁ a₁ c₁).mul (hc ε₂ hφ₂ a₂ c₂))
  apply shifted_scalar_boundary_of_comparison diamond ε₁ ε₂ K c₁ c₂ hm₁ hm₂ hsep φ₁ φ₂ a₁ a₂ U hU
  intro h q hq h₁ h₂
  dsimp only [U, V, d]
  rw [hmatch q hq h₁ h₂]
  unfold Plane.shiftedScalarNumerator Plane.scalarKernelReadout Plane.shiftedShellCoefficient
  ring

private theorem shifted_stable_weight_comparison (diamond : Plane E) (ε : Evolution)
    (K : TopologicalSpace.Compacts MassiveMomentum) (a : ℝ) (c : MassiveMomentum)
    (hbranch : ∀ q ∈ K, shellSquare (q+c).1 (q+c).2 ≠ 0) :
    ∃ F : ℝ × MassiveMomentum → ℂ, ContDiff ℝ 2 F ∧
      ∀ (h : Height) q, q ∈ K →
        F (h,q) = diamond.stableHalfCoefficient ε a (shellSquare (q+c).1 (q+c).2) h := by
  let w (q : MassiveMomentum) := shellSquare (q+c).1 (q+c).2
  have hw : ContDiff ℝ 2 w := shifted_invariant_contDiff c
  obtain ⟨δ,hδ,hbound⟩ := compact_positive_margin K hw.continuous.abs (fun q hq => abs_pos.mpr (hbranch q hq))
  let Z (sign : ℝ) (x : ℝ × MassiveMomentum) :=
    (smoothPositiveFloor δ (sign * w x.2) : ℂ) + Complex.I * ((sign * (diamond.eta ε*x.1) : ℝ) : ℂ)
  have hc (sign : ℝ) : ContDiff ℝ 2 (Z sign) :=
    (Complex.ofRealCLM.contDiff.comp ((smooth_positive_floor_contDiff δ).comp
      (contDiff_const.mul (hw.comp contDiff_snd)))).add
      (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (contDiff_const.mul (contDiff_const.mul contDiff_fst))))
  have hr (sign : ℝ) : ContDiff ℝ 2 (fun x => principalSqrt (Z sign x)) := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    have hp : 0 < (Z sign x).re := by simpa [Z] using smooth_positive_floor_pos hδ (sign * w x.2)
    exact ((principalSqrt_analyticOnNhd_rightHalfPlane (Z sign x) hp).contDiffAt.restrict_scalars ℝ).comp x (hc sign).contDiffAt
  let L (q : MassiveMomentum) := Real.smoothTransition ((w q+δ)/(2*δ))
  let Fpos (x : ℝ × MassiveMomentum) := Complex.exp ((Complex.I * ((diamond.eta ε*a:ℝ):ℂ)) * principalSqrt (Z 1 x))
  let Fneg (x : ℝ × MassiveMomentum) := Complex.exp (-(a:ℂ) * principalSqrt (Z (-1) x))
  have hL : ContDiff ℝ 2 (fun x : ℝ × MassiveMomentum => (L x.2 : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (Real.smoothTransition.contDiff.comp
      (((hw.comp contDiff_snd).add contDiff_const).div_const _))
  have hposF : ContDiff ℝ 2 Fpos := (Complex.contDiff_exp : ContDiff ℝ 2 Complex.exp).comp (contDiff_const.mul (hr 1))
  have hnegF : ContDiff ℝ 2 Fneg := (Complex.contDiff_exp : ContDiff ℝ 2 Complex.exp).comp (contDiff_const.mul (hr (-1)))
  refine ⟨fun x => (L x.2 : ℂ)*Fpos x + (1-(L x.2 : ℂ))*Fneg x,
    (hL.mul hposF).add ((contDiff_const.sub hL).mul hnegF),?_⟩
  intro h q hq
  change (L q : ℂ) * Fpos (h,q) + (1 - (L q : ℂ)) * Fneg (h,q) = _
  have hb := hbound q hq
  rcases le_total (w q) 0 with hn | hp
  · rw [abs_of_nonpos hn] at hb
    have hl : L q = 0 := Real.smoothTransition.zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity))
    have hz : Z (-1) (h,q) = -diamond.shiftedShellCoefficient ε h (w q) := by
      dsimp only [Z,Plane.shiftedShellCoefficient]
      rw [neg_one_mul,neg_one_mul,smooth_positive_floor_eq hδ hb]
      push_cast
      ring
    rw [hl]
    simp only [Complex.ofReal_zero,zero_mul,sub_zero,one_mul,zero_add,Fneg,hz,
      Plane.stableHalfCoefficient,dif_pos h.property,diamond.stable_half_numerator_characters]
    rfl
  · rw [abs_of_nonneg hp] at hb
    have hl : L q = 1 := Real.smoothTransition.one_of_one_le ((le_div_iff₀ (by positivity)).mpr (by linarith))
    have hz : Z 1 (h,q) = diamond.shiftedShellCoefficient ε h (w q) := by
      simp only [Z,one_mul,smooth_positive_floor_eq hδ hb,Plane.shiftedShellCoefficient]
    rw [hl,diamond.stable_half_analytic_form]
    simp only [Complex.ofReal_one,one_mul,sub_self,zero_mul,add_zero,Fpos,hz]
    rfl

/-- Stable-half profiles on compact separated charts away from the branch
edges of the two routed invariants. Either side of each branch edge is
permitted, with the actual prescribed square-root branch. -/
theorem Plane.shifted_stable_scalar_distribution (diamond : Plane E) (ε₁ ε₂ : Evolution)
    (K : TopologicalSpace.Compacts MassiveMomentum) (c₁ c₂ : MassiveMomentum) {m₁ m₂ a₁ a₂ : ℝ}
    (hm₁ : 0 ≤ m₁) (hm₂ : 0 ≤ m₂) (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂)
    (hsep : ∀ q ∈ K, shiftedD m₁ c₁ q ≠ 0 ∨ shiftedD m₂ c₂ q ≠ 0)
    (hax : c₁.1 = c₂.1 ∨ ∀ q ∈ K, (q+c₁).1 ≠ 0 ∧ (q+c₂).1 ≠ 0)
    (hb : ∀ q ∈ K, shellSquare (q+c₁).1 (q+c₁).2 ≠ 0 ∧ shellSquare (q+c₂).1 (q+c₂).2 ≠ 0) :
    let φ := fun z => Complex.exp (-principalSqrt z)
    ∃ T : CompactMomentumTest K →L[ℂ] ℂ, ∀ f : CompactMomentumTest K,
      Tendsto (fun h => diamond.shiftedScalarPairing ε₁ ε₂ h φ φ a₁ a₂ m₁ m₂ c₁ c₂ f.value)
        poleBoundaryHeights (𝓝 (directed (T f))) := by
  intro φ
  obtain ⟨G,hG,hmatch⟩ := shifted_running_signs_comparison K c₁ c₂ hax
  obtain ⟨F₁,hF₁,e₁⟩ := shifted_stable_weight_comparison diamond ε₁ K a₁ c₁ (fun q hq => (hb q hq).1)
  obtain ⟨F₂,hF₂,e₂⟩ := shifted_stable_weight_comparison diamond ε₂ K a₂ c₂ (fun q hq => (hb q hq).2)
  let U (t : ℝ) (q : MassiveMomentum) :=
    -(diamond.eta ε₁ : ℂ) * (diamond.eta ε₂ : ℂ) * G q * (F₁ (t,q) * F₂ (t,q))
  have hU : ContDiff ℝ 2 (Function.uncurry U) :=
    (contDiff_const.mul (hG.comp contDiff_snd)).mul (hF₁.mul hF₂)
  apply shifted_scalar_boundary_of_comparison diamond ε₁ ε₂ K c₁ c₂ hm₁ hm₂ hsep φ φ a₁ a₂ U hU
  intro h q hq h₁ h₂
  dsimp only [U, Plane.shiftedScalarNumerator]
  rw [hmatch q hq h₁ h₂, e₁ h q hq, e₂ h q hq,
    diamond.stable_scalar_kernel_readout ε₁ ha₁ h, diamond.stable_scalar_kernel_readout ε₂ ha₂ h]
  ring

end UV.SectorPlane
