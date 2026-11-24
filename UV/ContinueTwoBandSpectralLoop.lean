import UV.ContinueTwoBandSpectralDerivatives
import UV.ContinueTwoBandSpectralPulse

/-! Charged-frequency cost of an arbitrary complete hopping loop with two
retained L² intervals. The fixed-order constant is independent of the number
of unmarked intervals and every affine frequency shift. -/

noncomputable section
open MeasureTheory Complex

namespace UV.SectorPlane

/-- Oriented slot and its complete scalar insertions on one loop interval.
The derivative count records further powers of the oriented duration. -/
structure HoppingCarrierSlot where
  signedMass : ℝ
  shift : ℝ
  marks : List ℝ
  derivatives : ℕ

def HoppingCarrierSlot.degree (t : HoppingCarrierSlot) := t.marks.length+t.derivatives
def HoppingCarrierSlot.value (t : HoppingCarrierSlot) : ℝ → ℂ :=
  iteratedDeriv t.derivatives (hoppingMarks t.marks (fun x => hoppingInterval t.signedMass (x+t.shift)))

def HoppingCarrierSlot.weight (t : HoppingCarrierSlot) := hoppingWeight t.marks

theorem HoppingCarrierSlot.continuous (t : HoppingCarrierSlot) (ht : t.signedMass ≠ 0) : Continuous t.value :=
  hopping_marked_derivative_continuous ht _ _ _


def hoppingOrderConstant (m : ℝ) : ℕ → ℝ
  | 0 => max 1 (hoppingIntervalConstant m 0)
  | n+1 => max (hoppingOrderConstant m n) (hoppingIntervalConstant m (n+1))

theorem hopping_order_constant_one (m : ℝ) (n : ℕ) : 1 ≤ hoppingOrderConstant m n := by
  induction n with
  | zero => exact le_max_left _ _
  | succ n ih => exact ih.trans (le_max_left _ _)

private theorem order_dominates (m : ℝ) {j n : ℕ} (hj : j ≤ n) :
    hoppingIntervalConstant m j ≤ hoppingOrderConstant m n := by
  induction n with
  | zero => simp only [Nat.le_zero.mp hj,hoppingOrderConstant,le_max_right]
  | succ n ih =>
    rcases Nat.eq_or_lt_of_le hj with rfl|h
    · exact le_max_right _ _
    · exact (ih (by omega)).trans (le_max_left _ _)

private theorem slot_bound {m : ℝ} (hm : 0<m) (t : HoppingCarrierSlot) (ht : |t.signedMass|=m)
    {M : ℕ} (hD : t.degree ≤ M) (s : ℝ) :
    ‖t.value s‖ ≤ m⁻¹*(hoppingOrderConstant m M)^t.degree*t.weight := by
  by_cases hz : t.degree=0
  · have hnil : t.marks=[] := List.length_eq_zero_iff.mp (by simpa [HoppingCarrierSlot.degree] using (Nat.eq_zero_of_add_eq_zero_right hz))
    have hn : t.derivatives=0 := Nat.eq_zero_of_add_eq_zero_left hz
    simpa [HoppingCarrierSlot.value,HoppingCarrierSlot.weight,hoppingWeight,hnil,hn,hz,
      hoppingMarks,hopping_interval_norm,ht] using (twoBand_resolvent_bound hm 0 (s+t.shift)).2
  · have h := hopping_marked_derivative_sup hm ht t.shift t.marks t.derivatives s
    have hK : hoppingIntervalConstant m t.degree ≤ (hoppingOrderConstant m M)^t.degree := by
      apply (order_dominates m hD).trans
      simpa using (pow_le_pow_right₀ (hopping_order_constant_one m M) (Nat.one_le_iff_ne_zero.mpr hz) :
        (hoppingOrderConstant m M)^1 ≤ _)
    exact h.trans (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hK
      (hopping_weight_nonneg _)) (inv_nonneg.mpr hm.le))

def hoppingLoopValue (T : List HoppingCarrierSlot) (s : ℝ) := (T.map (fun t => t.value s)).prod
def hoppingLoopDegree (T : List HoppingCarrierSlot) := (T.map HoppingCarrierSlot.degree).sum
def hoppingLoopWeight (T : List HoppingCarrierSlot) := (T.map HoppingCarrierSlot.weight).prod

private theorem loop_weight_nonneg (T : List HoppingCarrierSlot) : 0 ≤ hoppingLoopWeight T := by
  induction T with
  | nil => exact zero_le_one
  | cons t _ ih => exact mul_nonneg (hopping_weight_nonneg t.marks) ih

private theorem loop_bound {m : ℝ} (hm : 0<m) {M : ℕ} (T : List HoppingCarrierSlot)
    (hT : ∀ t ∈ T, |t.signedMass|=m) (hD : hoppingLoopDegree T ≤ M) (s : ℝ) :
    ‖hoppingLoopValue T s‖ ≤ m⁻¹^T.length * hoppingOrderConstant m M ^ hoppingLoopDegree T * hoppingLoopWeight T := by
  induction T with
  | nil => simp [hoppingLoopValue,hoppingLoopWeight,hoppingLoopDegree]
  | cons t T ih =>
    change t.degree+hoppingLoopDegree T ≤ M at hD
    have h₁ := slot_bound hm t (hT t List.mem_cons_self) (by omega : t.degree ≤ M) s
    have h₂ := ih (fun u hu => hT u (List.mem_cons_of_mem t hu)) (by omega)
    change ‖t.value s * hoppingLoopValue T s‖ ≤ _
    rw [norm_mul]
    apply (mul_le_mul h₁ h₂ (norm_nonneg _) (by
      have hp := (hopping_order_constant_one m M).trans' zero_le_one
      have hw := hopping_weight_nonneg t.marks
      unfold HoppingCarrierSlot.weight
      positivity)).trans_eq
    change _ = m⁻¹^(T.length+1)*hoppingOrderConstant m M^(t.degree+hoppingLoopDegree T)*(t.weight*hoppingLoopWeight T)
    rw [pow_succ,pow_add]
    ring

private theorem loop_continuous {m : ℝ} (hm : 0<m) (T : List HoppingCarrierSlot)
    (hT : ∀ t ∈ T, |t.signedMass|=m) : Continuous (hoppingLoopValue T) := by
  induction T with
  | nil => exact continuous_const
  | cons t T ih =>
    exact (t.continuous (abs_pos.mp ((hT t List.mem_cons_self).symm ▸ hm))).mul
      (ih (fun u hu => hT u (List.mem_cons_of_mem _ hu)))

/-- Open lines retain the external carrier frequency. The uniform bound
uses all `n+1` interval suprema, including the one interval at zero hops. -/
theorem hopping_open_frequency_bound {m : ℝ} (hm : 0<m) {M : ℕ} (T : List HoppingCarrierSlot)
    (hT : ∀ t ∈ T, |t.signedMass|=m) (hD : hoppingLoopDegree T ≤ M) (s : ℝ) :
    ‖hoppingLoopValue T s‖ ≤ m⁻¹^T.length * hoppingOrderConstant m M ^ M * hoppingLoopWeight T :=
  (loop_bound hm T hT hD s).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (hopping_order_constant_one m M) hD)
      (pow_nonneg (inv_nonneg.mpr hm.le) _)) (loop_weight_nonneg _))

/-- Uniform original charged-frequency integral with two onsite intervals
in L² and all others in L∞. For a total mark and derivative budget `M`
the power of the mass is `1 − (2 + T.length)`. -/
theorem hopping_charged_loop_frequency {m : ℝ} (hm : 0<m) (u v : HoppingCarrierSlot)
    (T : List HoppingCarrierSlot) (hu : |u.signedMass|=m) (hv : |v.signedMass|=m)
    (hT : ∀ t ∈ T, |t.signedMass|=m) {M : ℕ}
    (hD : u.degree + v.degree + hoppingLoopDegree T ≤ M) :
    Integrable (hoppingLoopValue (u::v::T)) ∧
    (∫ s : ℝ, ‖hoppingLoopValue (u::v::T) s‖) ≤
      (Real.pi/m)*m⁻¹^T.length*hoppingOrderConstant m M^(M+2)*hoppingLoopWeight (u::v::T) := by
  let C := hoppingOrderConstant m M
  have hC : 1 ≤ C := hopping_order_constant_one _ _
  have hp := hopping_marked_derivative_pair hm hu hv u.shift v.shift u.marks v.marks u.derivatives v.derivatives
  let H := m⁻¹^T.length * C^(hoppingLoopDegree T)*hoppingLoopWeight T
  have hH : 0 ≤ H := mul_nonneg (mul_nonneg (pow_nonneg (inv_nonneg.mpr hm.le) _) (pow_nonneg (zero_le_one.trans hC) _))
    (loop_weight_nonneg _)
  have hle (s : ℝ) : ‖hoppingLoopValue (u::v::T) s‖ ≤ ‖u.value s*v.value s‖*H := by
    change ‖u.value s*(v.value s*hoppingLoopValue T s)‖ ≤ _
    rw [←mul_assoc,norm_mul]
    exact mul_le_mul_of_nonneg_left (loop_bound hm T hT (by omega : hoppingLoopDegree T ≤ M) s) (norm_nonneg _)
  have hB : Integrable (fun s => ‖u.value s*v.value s‖*H) := hp.1.norm.mul_const _
  have hi : Integrable (hoppingLoopValue (u::v::T)) := by
    apply hB.mono' (loop_continuous hm _ (by simpa using And.intro hu (And.intro hv hT))).aestronglyMeasurable (ae_of_all _ hle)
  refine ⟨hi,(integral_mono hi.norm hB hle).trans ?_⟩
  rw [integral_mul_const]
  have hbound := mul_le_mul_of_nonneg_right hp.2 hH
  apply hbound.trans
  have hcmp : hoppingIntervalConstant m u.degree * hoppingIntervalConstant m v.degree * C^(hoppingLoopDegree T) ≤ C^(M+2) := by
    calc
      _ ≤ (C*C)*C^(hoppingLoopDegree T) := mul_le_mul_of_nonneg_right
        (mul_le_mul (order_dominates m (show u.degree≤M by omega)) (order_dominates m (show v.degree≤M by omega))
          (hopping_interval_constant_nonneg _ _) (zero_le_one.trans hC)) (pow_nonneg (zero_le_one.trans hC) _)
      _ = C^(hoppingLoopDegree T+2) := by rw [pow_add,pow_two]; ring
      _ ≤ _ := pow_le_pow_right₀ hC (by omega)
  let A := (Real.pi/m)*m⁻¹^T.length*(u.weight*v.weight*hoppingLoopWeight T)
  have hA : 0 ≤ A := mul_nonneg (mul_nonneg (by positivity) (by positivity))
    (mul_nonneg (mul_nonneg (hopping_weight_nonneg _) (hopping_weight_nonneg _)) (loop_weight_nonneg _))
  calc
    _ = (hoppingIntervalConstant m u.degree*hoppingIntervalConstant m v.degree*C^(hoppingLoopDegree T))*A := by
      unfold A H HoppingCarrierSlot.degree HoppingCarrierSlot.weight
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hcmp hA
    _ = _ := by
      change _ = (Real.pi/m)*m⁻¹^T.length*C^(M+2)*(u.weight*(v.weight*hoppingLoopWeight T))
      unfold A
      ring

end UV.SectorPlane
