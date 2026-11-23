import UV.ContinueTransverseRestMeasure
import UV.ContinueShiftedScalar

/-! Actual stable-half lines in the simultaneous rest-shell chart. Both
running units are evaluated before coefficient extraction. The compact
normal support stays on the positive-radius and positive-invariant chart. -/

noncomputable section

namespace UV.SectorPlane

open Filter MeasureTheory Real Set UV.Carrier
open scoped Topology UV.SectorPlane

variable {E : Type*} [NormedAddCommGroup E]

/-- The region of independent real normals where, for positive transfer,
the first running sign is +1 and the second is −1. Both stable square roots
are evaluated on their prescribed timelike rims. -/
def stableRestNormalRegion (m t : ℝ) : Set (ℝ × ℝ) :=
  {Y | 0 < restNormalRadiusSq m t Y ∧ |restNormalAxial t Y| < t/2 ∧
    0 < Y.1 + m^2 ∧ 0 < Y.2 + m^2}

theorem stable_rest_normal_region_open (m t : ℝ) : IsOpen (stableRestNormalRegion m t) := by
  have hA : Continuous (restNormalAxial t) := by unfold restNormalAxial; fun_prop
  have hR : Continuous (restNormalRadiusSq m t) := by unfold restNormalRadiusSq; fun_prop
  exact (isOpen_lt continuous_const hR).inter
    ((isOpen_lt hA.abs continuous_const).inter
      ((isOpen_lt continuous_const (continuous_fst.add continuous_const)).inter
        (isOpen_lt continuous_const (continuous_snd.add continuous_const))))

theorem zero_mem_stable_rest_normal_region {m t : ℝ} (hm : 0 < m) (ht : 2*m < t) :
    (0 : ℝ × ℝ) ∈ stableRestNormalRegion m t := by
  have ht' : 0 < t := by linarith
  obtain ⟨b,hb,hB⟩ := rest_normal_strip hm (by rwa [abs_of_pos ht'])
  have hR := (hB 0 (by simpa using hb.le) (by simpa using hb.le)).1
  refine ⟨hR,?_,?_,?_⟩
  · simp only [restNormalAxial,Prod.fst_zero,Prod.snd_zero,sub_self,zero_div,abs_zero]
    positivity
  · simpa only [Prod.fst_zero,zero_add] using sq_pos_of_pos hm
  · simpa only [Prod.snd_zero,zero_add] using sq_pos_of_pos hm

private def stableRestRim (η a w h : ℝ) : ℂ :=
  Complex.exp ((Complex.I * ((η * a : ℝ) : ℂ)) *
    principalSqrt ((w : ℂ) + Complex.I * ((η * h : ℝ) : ℂ)))

private theorem stable_rest_rim_contDiffAt {w : ℝ × (ℝ × ℝ) → ℝ}
    (hw : ContDiff ℝ 2 w) (η a : ℝ) (p : ℝ × (ℝ × ℝ)) (hp : 0 < w p) :
    ContDiffAt ℝ 2 (fun z => stableRestRim η a (w z) z.1) p := by
  let Z (z : ℝ × (ℝ × ℝ)) := (w z : ℂ) + Complex.I * ((η*z.1 : ℝ) : ℂ)
  have hZ : ContDiff ℝ 2 Z := (Complex.ofRealCLM.contDiff.comp hw).add
    (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_fst)))
  have hZp : 0 < (Z p).re := by simpa [Z] using hp
  have hs : ContDiffAt ℝ 2 (fun z => principalSqrt (Z z)) p :=
    ((principalSqrt_analyticOnNhd_rightHalfPlane (Z p) hZp).contDiffAt.restrict_scalars ℝ).comp p hZ.contDiffAt
  exact (Complex.contDiff_exp : ContDiff ℝ 2 Complex.exp).contDiffAt.comp p
    ((contDiffAt_const (c := Complex.I * ((η*a:ℝ):ℂ))).mul hs)

/-- With the two evaluated running units, the prefactor is η₁η₂
in the positive rest-transfer strip. The scalar weight has an analytic
formula in each normal coordinate before the height is removed. -/
def Plane.restStableNormalNumerator (diamond : Plane E) (ε₁ ε₂ : Evolution)
    (m a b h : ℝ) (Y : ℝ × ℝ) : ℂ :=
  (diamond.eta ε₁ : ℂ) * (diamond.eta ε₂ : ℂ) *
    (stableRestRim (diamond.eta ε₁) a (Y.1+m^2) h *
      stableRestRim (diamond.eta ε₂) b (Y.2+m^2) h)

theorem Plane.rest_stable_normal_numerator_contDiffAt (diamond : Plane E) (ε₁ ε₂ : Evolution)
    (m a b : ℝ) (z : ℝ × (ℝ × ℝ)) (h₁ : 0 < z.2.1 + m^2) (h₂ : 0 < z.2.2 + m^2) :
    ContDiffAt ℝ 2 (Function.uncurry (diamond.restStableNormalNumerator ε₁ ε₂ m a b)) z := by
  exact contDiffAt_const.mul
    ((stable_rest_rim_contDiffAt ((contDiff_fst.comp contDiff_snd).add contDiff_const) _ _ z h₁).mul
      (stable_rest_rim_contDiffAt ((contDiff_snd.comp contDiff_snd).add contDiff_const) _ _ z h₂))

private theorem stable_rest_rim_positive_height (diamond : Plane E) (ε : Evolution)
    (a w : ℝ) (h : Height) :
    stableRestRim (diamond.eta ε) a w h = diamond.stableHalfCoefficient ε a w h := by
  rw [diamond.stable_half_analytic_form]
  rfl

theorem Plane.rest_stable_normal_numerator_continuous (diamond : Plane E) (ε₁ ε₂ : Evolution)
    (m a b : ℝ) (h : Height) :
    Continuous (diamond.restStableNormalNumerator ε₁ ε₂ m a b h) := by
  change Continuous (fun Y : ℝ × ℝ => (diamond.eta ε₁ : ℂ) * (diamond.eta ε₂ : ℂ) *
    (stableRestRim (diamond.eta ε₁) a (Y.1+m^2) h *
      stableRestRim (diamond.eta ε₂) b (Y.2+m^2) h))
  simp_rw [stable_rest_rim_positive_height]
  exact continuous_const.mul
    (((diamond.stable_half_coefficient_continuous ε₁ a h).comp (continuous_fst.add continuous_const)).mul
      ((diamond.stable_half_coefficient_continuous ε₂ b h).comp (continuous_snd.add continuous_const)))

/-- On the normal support, the finite-height stable rim is exactly the
character readout of the original two running numerators. -/
theorem Plane.rest_stable_normal_numerator_eq (diamond : Plane E) (ε₁ ε₂ : Evolution)
    {m t a b : ℝ} (ht : 0 < t) (ha : 0 ≤ a) (hb : 0 ≤ b) (h : Height) (q : MassiveMomentum)
    (hq : symmetricRestNormals m t q ∈ stableRestNormalRegion m t) :
    let φ := fun z => Complex.exp (-principalSqrt z)
    diamond.restStableNormalNumerator ε₁ ε₂ m a b h (symmetricRestNormals m t q) =
      diamond.shiftedScalarNumerator ε₁ ε₂ h φ φ a b (axialTransfer (t/2))
        (axialTransfer (-(t/2))) q := by
  intro φ
  let Y := symmetricRestNormals m t q
  have hY : Y = restAxialRadialNormals m t (q.1,‖q.2‖) :=
    symmetric_rest_normals_eval m t q
  have hA : restNormalAxial t Y = q.1 := by
    rw [hY,rest_normal_axial_forward m ht.ne']
  have habs : |q.1| < t/2 := by
    have hh : |restNormalAxial t Y| < t/2 := hq.2.1
    rwa [hA] at hh
  have hpos : 0 < (q + axialTransfer (t/2)).1 := by
    rw [axial_transfer_coordinates,Prod.fst_add]
    linarith [neg_le_abs q.1]
  have hneg : (q + axialTransfer (-(t/2))).1 < 0 := by
    rw [axial_transfer_coordinates,Prod.fst_add]
    linarith [le_abs_self q.1]
  unfold Plane.restStableNormalNumerator Plane.shiftedScalarNumerator
  rw [stable_rest_rim_positive_height,stable_rest_rim_positive_height,
    diamond.stable_scalar_kernel_readout ε₁ ha h,diamond.stable_scalar_kernel_readout ε₂ hb h]
  have hW₁ : (symmetricRestNormals m t q).1 + m^2 =
      shellSquare (q + axialTransfer (t/2)).1 (q + axialTransfer (t/2)).2 := by
    simp only [symmetricRestNormals,shiftedD,massiveD,sub_add_cancel]
  have hW₂ : (symmetricRestNormals m t q).2 + m^2 =
      shellSquare (q + axialTransfer (-(t/2))).1 (q + axialTransfer (-(t/2))).2 := by
    simp only [symmetricRestNormals,shiftedD,massiveD,sub_add_cancel]
  rw [hW₁,hW₂]
  have hsign₁ : axialSign (q + axialTransfer (t/2)).1 = 1 := if_pos hpos
  have hsign₂ : axialSign (q + axialTransfer (-(t/2))).1 = -1 := by
    unfold axialSign
    rw [if_neg hneg.not_gt,if_pos hneg]
  rw [hsign₁,hsign₂]
  push_cast
  ring

/-- The full compact test on the symmetric rest pair is represented by a
compact C² normal test at every real parameter. Its zero-height value
contains the exact spatial angular average, radial Jacobian and phase. -/
def Plane.restStableNormalTest (diamond : Plane E) (ε₁ ε₂ : Evolution)
    (m t a b : ℝ) (f : MassiveMomentum → ℂ) (g : ℝ × ℝ → ℂ)
    (h : ℝ) (Y : ℝ × ℝ) : ℂ :=
  restNormalMeasureFactor m t Y •
    (coneSpatialMean f (restNormalInverse m t Y) *
      (g Y * diamond.restStableNormalNumerator ε₁ ε₂ m a b h Y))

theorem Plane.rest_stable_normal_test_contDiff (diamond : Plane E) (ε₁ ε₂ : Evolution)
    (m t a b : ℝ) {f : MassiveMomentum → ℂ} {g : ℝ × ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (K : TopologicalSpace.Compacts (ℝ × ℝ)) (hK : (K : Set (ℝ × ℝ)) ⊆ stableRestNormalRegion m t)
    (hgK : ∀ Y ∉ K, g Y = 0) :
    ContDiff ℝ 2 (Function.uncurry (diamond.restStableNormalTest ε₁ ε₂ m t a b f g)) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  by_cases hz : z.2 ∈ K
  · have h := hK hz
    have hInv : ContDiffAt ℝ 2 (restNormalInverse m t) z.2 :=
      rest_normal_inverse_contDiffAt m t z.2 h.1
    have hJ : ContDiffAt ℝ 2 (restNormalMeasureFactor m t) z.2 :=
      (contDiff_snd.contDiffAt.comp _ hInv).div_const _
    exact (hJ.comp z contDiffAt_snd).smul
      ((((cone_spatial_mean_contDiff hf).contDiffAt.comp _ hInv).comp z contDiffAt_snd).mul
        ((hg.contDiffAt.comp z contDiffAt_snd).mul
          (diamond.rest_stable_normal_numerator_contDiffAt ε₁ ε₂ m a b z h.2.2.1 h.2.2.2)))
  · apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
    have hOpen : IsOpen {z : ℝ × (ℝ × ℝ) | z.2 ∉ K} :=
      K.isCompact.isClosed.isOpen_compl.preimage continuous_snd
    filter_upwards [hOpen.mem_nhds hz] with z' hz'
    simp [Function.uncurry,Plane.restStableNormalTest,hgK z'.2 hz']

/-- Exact finite-height integral identity for the original two scalar lines,
with the Cartesian test localized by the simultaneous real normals. -/
theorem Plane.rest_stable_pairing_normal_integral (diamond : Plane E) (ε₁ ε₂ : Evolution)
    {m t a b : ℝ} (ht : 0 < t) (ha : 0 ≤ a) (hb : 0 ≤ b) (h : Height)
    {f : MassiveMomentum → ℂ} (hf : Continuous f) (hs : HasCompactSupport f)
    {g : ℝ × ℝ → ℂ} (hg : Continuous g) (hgs : ∀ Y, g Y ≠ 0 → Y ∈ stableRestNormalRegion m t) :
    let φ := fun z => Complex.exp (-principalSqrt z)
    diamond.shiftedScalarPairing ε₁ ε₂ h φ φ a b m m (axialTransfer (t/2)) (axialTransfer (-(t/2)))
      (fun q => f q * g (symmetricRestNormals m t q)) =
      directed ((4 * π) • ∫ Y, diamond.restStableNormalTest ε₁ ε₂ m t a b f g h Y *
        (diamond.poleCoefficient ε₁ h Y.1 * diamond.poleCoefficient ε₂ h Y.2)) := by
  intro φ
  let N := symmetricRestNormals m t
  let W := diamond.restStableNormalNumerator ε₁ ε₂ m a b h
  let P (Y : ℝ × ℝ) := diamond.poleCoefficient ε₁ h Y.1 * diamond.poleCoefficient ε₂ h Y.2
  let G (Y : ℝ × ℝ) := g Y * W Y * P Y
  have hN : Continuous N :=
    (shiftedD_contDiff (n := 1) _ _).continuous.prodMk (shiftedD_contDiff (n := 1) _ _).continuous
  have hW : Continuous W := diamond.rest_stable_normal_numerator_continuous ε₁ ε₂ m a b h
  have hP : Continuous P := ((diamond.pole_coefficient_continuous ε₁ h).comp continuous_fst).mul
    ((diamond.pole_coefficient_continuous ε₂ h).comp continuous_snd)
  have hi : Integrable (fun q => (f q * g (N q)) * (W (N q) * P (N q))) :=
    ((hf.mul (hg.comp hN)).mul ((hW.comp hN).mul (hP.comp hN))).integrable_of_hasCompactSupport
      hs.mul_right.mul_right
  rw [diamond.shifted_scalar_pairing_eq_of_numerator ε₁ ε₂ h φ φ a b m m _ _ hi
    (fun q hq _ _ => diamond.rest_stable_normal_numerator_eq ε₁ ε₂ ht ha hb h q
      (hgs _ (fun hz => hq (by rw [hz,mul_zero]))))]
  congr 1
  calc
    _ = ∫ q, f q * G (N q) := by
      apply integral_congr_ae
      exact Eventually.of_forall fun q => by
        change (f q * g (N q)) * (W (N q) * P (N q)) = f q * (g (N q) * W (N q) * P (N q))
        ring
    _ = (4 * π) • ∫ Y, restNormalMeasureFactor m t Y •
          (coneSpatialMean f (restNormalInverse m t Y) * G Y) :=
      symmetric_rest_normal_integral m t ht.ne' hf hs ((hg.mul hW).mul hP) (fun Y hY => by
        have hz : g Y = 0 := by
          by_contra hne
          exact (not_lt_of_ge hY) (hgs Y hne).1
        simp [G,hz])
    _ = _ := by
      congr 1
      apply integral_congr_ae
      exact Eventually.of_forall fun Y => by
        simp only [Plane.restStableNormalTest,G,W,P,Complex.real_smul]
        ring

/-- At the intersection of the two mass shells the test carries the
normalized spatial sphere average, its geometric weight and the
on-shell phase of both original numerators. -/
theorem Plane.rest_stable_normal_test_at_intersection (diamond : Plane E) (ε₁ ε₂ : Evolution)
    {m : ℝ} (hm : 0 ≤ m) (t a b : ℝ) (f : MassiveMomentum → ℂ) (g : ℝ × ℝ → ℂ) :
    let r := Real.sqrt ((t/2)^2 - m^2)
    diamond.restStableNormalTest ε₁ ε₂ m t a b f g 0 0 =
      (r/(4*|t|)) • (coneSpatialMean f (0,r) * (g 0 *
        ((diamond.eta ε₁ : ℂ) * (diamond.eta ε₂ : ℂ) *
          Complex.exp (Complex.I * (((diamond.eta ε₁ * a + diamond.eta ε₂ * b) * m : ℝ) : ℂ))))) := by
  intro r
  have hphase : diamond.restStableNormalNumerator ε₁ ε₂ m a b 0 0 =
      (diamond.eta ε₁ : ℂ) * (diamond.eta ε₂ : ℂ) *
        Complex.exp (Complex.I * (((diamond.eta ε₁ * a + diamond.eta ε₂ * b) * m : ℝ) : ℂ)) := by
    unfold Plane.restStableNormalNumerator stableRestRim
    simp only [Prod.fst_zero,Prod.snd_zero,zero_add,mul_zero,Complex.ofReal_zero,add_zero,
      principalSqrt_ofReal (sq_nonneg m),Real.sqrt_sq hm,← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp only [Plane.restStableNormalTest,restNormalMeasureFactor,rest_normal_inverse_origin,hphase]
  rfl

end UV.SectorPlane
