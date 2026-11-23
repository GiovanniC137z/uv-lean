import UV.SectorPlaneMassiveSquare

/-! Arbitrary powers of a same-side positive-height pole on the full
intrinsic four-momentum space. A Cartesian Euler integration by parts
lowers the power by one and retains the complex mass shift. -/

noncomputable section

namespace UV.SectorPlane

open Filter MeasureTheory UV.Carrier
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E]

/-- Lowers pole order k+2 to k+1 in four momentum dimensions. -/
def poleOrderEulerStep (k : ℕ) (f : MassiveMomentum → ℂ) (q : MassiveMomentum) : ℂ :=
  ((4 - 2 * ((k : ℂ) + 1)) * f q + momentumEuler f q) / (2 * ((k : ℂ) + 1))

theorem pole_order_euler_step_compact (k : ℕ) {f : MassiveMomentum → ℂ}
    (hs : HasCompactSupport f) : HasCompactSupport (poleOrderEulerStep k f) := by
  unfold poleOrderEulerStep
  simp only [div_eq_mul_inv]
  exact (((hs.mul_left (f := fun _ => 4 - 2 * ((k : ℂ) + 1))).add
    (momentum_euler_compact hs)).mul_right (f' := fun _ => (2 * ((k : ℂ) + 1))⁻¹))

theorem pole_order_euler_step_contDiff (k : ℕ) {r : WithTop ℕ∞} {f : MassiveMomentum → ℂ}
    (hf : ContDiff ℝ (r + 1) f) : ContDiff ℝ r (poleOrderEulerStep k f) := by
  have hE : ContDiff ℝ r (momentumEuler f) :=
    (hf.fderiv_right (rfl.le : r + 1 ≤ r + 1)).clm_apply contDiff_id
  exact ((contDiff_const.mul (hf.of_le (by exact le_self_add))).add hE).div_const _

def poleOrderEulerTest : ℕ → (MassiveMomentum → ℂ) → MassiveMomentum → ℂ
  | 0, f => f
  | n + 1, f => poleOrderEulerTest n (poleOrderEulerStep n f)

theorem pole_order_euler_test_compact (n : ℕ) {f : MassiveMomentum → ℂ}
    (hs : HasCompactSupport f) : HasCompactSupport (poleOrderEulerTest n f) := by
  induction n generalizing f with
  | zero => exact hs
  | succ n ih => exact ih (pole_order_euler_step_compact n hs)

theorem pole_order_euler_test_contDiff (n : ℕ) (r : WithTop ℕ∞) {f : MassiveMomentum → ℂ}
    (hf : ContDiff ℝ ((n : WithTop ℕ∞) + r) f) : ContDiff ℝ r (poleOrderEulerTest n f) := by
  induction n generalizing f with
  | zero => simpa only [poleOrderEulerTest, Nat.cast_zero, zero_add] using hf
  | succ n ih =>
    apply ih
    apply pole_order_euler_step_contDiff
    simpa only [Nat.cast_succ, add_right_comm] using hf

theorem Plane.massive_pole_order_parts (diamond : Plane E) (ε : Evolution) (h : Height)
    (m : ℝ) (k : ℕ) {f : MassiveMomentum → ℂ} (hf : ContDiff ℝ 1 f) (hs : HasCompactSupport f) :
    diamond.squareMassShift ε m h * (∫ q, f q * (diamond.poleCoefficient ε h (massiveD m q))^(k+2)) =
      ∫ q, poleOrderEulerStep k f q * (diamond.poleCoefficient ε h (massiveD m q))^(k+1) := by
  let Z (q : MassiveMomentum) := diamond.shiftedShellCoefficient ε h (massiveD m q)
  let P (q : MassiveMomentum) := (Z q)⁻¹
  let C : ℂ := (k : ℂ) + 1
  let μ := diamond.squareMassShift ε m h
  have hC : C ≠ 0 := by
    have hc : 0 < (k : ℝ) + 1 := by positivity
    change (k : ℂ) + 1 ≠ 0
    exact_mod_cast hc.ne'
  have hCZ : 2 * C ≠ 0 := mul_ne_zero (by norm_num) hC
  have hNZ (q) : Z q ≠ 0 := diamond.shifted_denominator_ne_zero ε h _
  have hw : ContDiff ℝ 1 (fun q : MassiveMomentum => shellSquare q.1 q.2) :=
    (contDiff_fst.pow 2).sub (contDiff_snd.norm_sq ℝ)
  have hZ : ContDiff ℝ 1 Z := (Complex.ofRealCLM.contDiff.comp (hw.sub contDiff_const)).add contDiff_const
  have hP : ContDiff ℝ 1 P := hZ.inv hNZ
  let F (q : MassiveMomentum) := f q * P q ^ (k+1)
  have hF : ContDiff ℝ 1 F := hf.mul (hP.pow (k+1))
  have hsF : HasCompactSupport F := hs.mul_right
  have dP (q) : momentumEuler P q = -2 * (shellSquare q.1 q.2 : ℂ) * P q ^ 2 := by
    have hz := ((Complex.ofRealCLM.hasFDerivAt.comp q ((shell_square_hasFDerivAt q).sub_const (m^2))).add_const
      (Complex.I * ((diamond.eta ε*(h:ℝ):ℝ):ℂ)))
    have hd := ((hasFDerivAt_inv (hNZ q)).restrictScalars ℝ).comp q hz
    change fderiv ℝ ((fun z : ℂ => z⁻¹) ∘ Z) q q = _
    rw [hd.fderiv]
    simp [P,coneCovector_apply,real_inner_self_eq_norm_sq,shellSquare,inv_pow]
    ring
  have dPk (q) : momentumEuler (fun p => P p ^ (k+1)) q =
      -2 * C * (shellSquare q.1 q.2 : ℂ) * P q ^ (k+2) := by
    have hp := ((hP.differentiable le_rfl q).hasFDerivAt.pow (k+1)).fderiv
    unfold momentumEuler
    rw [hp]
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, Nat.add_sub_cancel]
    change _ * momentumEuler P q = _
    rw [dP, pow_add]
    dsimp only [C]
    ring
  have dF (q) : momentumEuler F q = momentumEuler f q * P q ^ (k+1) -
      2 * C * (shellSquare q.1 q.2 : ℂ) * f q * P q ^ (k+2) := by
    have hp := (((hP.pow (k+1)).differentiable le_rfl q).hasFDerivAt)
    have hprod := ((hf.differentiable le_rfl q).hasFDerivAt.mul hp).fderiv
    unfold momentumEuler
    rw [show fderiv ℝ F q = _ from hprod]
    simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_eq_mul]
    change _ * momentumEuler (fun p => P p ^ (k+1)) q + _ * momentumEuler f q = _
    rw [dPk]; unfold momentumEuler; ring
  have he (q) :
      μ * (f q * P q ^ (k+2)) - poleOrderEulerStep k f q * P q ^ (k+1) =
      (-4 * F q - momentumEuler F q) / (2 * C) := by
    have hz : (shellSquare q.1 q.2 : ℂ) - μ = Z q := by
      simp only [μ,Plane.squareMassShift,Z,Plane.shiftedShellCoefficient,massiveD,Complex.ofReal_sub]; ring
    have hrel : ((shellSquare q.1 q.2 : ℂ) - μ) * P q = 1 := by
      rw [hz]
      exact mul_inv_cancel₀ (hNZ q)
    rw [dF]
    change μ * (f q * P q ^ (k+2)) -
      (((4 - 2 * C) * f q + momentumEuler f q) / (2 * C)) * P q ^ (k+1) =
      (-4 * (f q * P q ^ (k+1)) -
        (momentumEuler f q * P q ^ (k+1) -
          2 * C * (shellSquare q.1 q.2 : ℂ) * f q * P q ^ (k+2))) / (2 * C)
    field_simp [hCZ]
    rw [pow_succ (P q) (k+1)]
    linear_combination -(2 * C * f q * P q ^ (k+1)) * hrel
  have htc : Continuous (poleOrderEulerStep k f) :=
    ((continuous_const.mul hf.continuous).add (momentum_euler_continuous hf)).div_const _
  have hi := (hf.continuous.mul (hP.continuous.pow (k+2))).integrable_of_hasCompactSupport (μ := volume) hs.mul_right
  have hj := (htc.mul (hP.continuous.pow (k+1))).integrable_of_hasCompactSupport (μ := volume)
    (pole_order_euler_step_compact k hs).mul_right
  have hiF := hF.continuous.integrable_of_hasCompactSupport (μ := volume) hsF
  have hiE := (momentum_euler_continuous hF).integrable_of_hasCompactSupport (μ := volume) (momentum_euler_compact hsF)
  simp only [diamond.pole_coefficient_eq_inv]
  change μ * (∫ q, f q * P q^(k+2)) = ∫ q, poleOrderEulerStep k f q * P q^(k+1)
  rw [← sub_eq_zero, ← integral_const_mul, ← integral_sub (hi.const_mul _) hj]
  simp_rw [he]
  rw [integral_div, integral_sub (hiF.const_mul _) hiE, integral_const_mul, integral_momentum_euler hF hsF, sub_self, zero_div]

/-- Exact finite-height reduction to the simple pole on its iterated
Euler test. The height and evolution argument never change. -/
theorem Plane.massive_pole_order_euler_reduction (diamond : Plane E) (ε : Evolution) (h : Height)
    (m : ℝ) (n : ℕ) {f : MassiveMomentum → ℂ}
    (hf : ContDiff ℝ (n : WithTop ℕ∞) f) (hs : HasCompactSupport f) :
    (diamond.squareMassShift ε m h)^n *
      (∫ q, f q * (diamond.poleCoefficient ε h (massiveD m q))^(n+1)) =
      ∫ q, poleOrderEulerTest n f q * diamond.poleCoefficient ε h (massiveD m q) := by
  induction n generalizing f with
  | zero => simp [poleOrderEulerTest]
  | succ n ih =>
    have h₁ : ContDiff ℝ 1 f := hf.of_le (by exact_mod_cast (Nat.succ_le_succ (Nat.zero_le n)))
    have hf' : ContDiff ℝ (n : WithTop ℕ∞) (poleOrderEulerStep n f) :=
      pole_order_euler_step_contDiff n (by rwa [← Nat.cast_succ])
    rw [pow_succ, mul_assoc, diamond.massive_pole_order_parts ε h m n h₁ hs]
    exact ih hf' (pole_order_euler_step_compact n hs)

theorem Plane.square_mass_shift_tendsto (diamond : Plane E) (ε : Evolution) (m : ℝ) :
    Tendsto (fun h : Height => diamond.squareMassShift ε m h) poleBoundaryHeights (𝓝 ((m^2:ℝ):ℂ)) := by
  have hc : Continuous (diamond.squareMassShift ε m) := by unfold Plane.squareMassShift; fun_prop
  have he : diamond.squareMassShift ε m 0 = ((m^2:ℝ):ℂ) := by simp [Plane.squareMassShift]
  rw [← he]
  exact (hc.continuousAt (x := 0)).tendsto.comp pole_height_tendsto_zero

theorem Plane.square_mass_shift_ne_zero (diamond : Plane E) (ε : Evolution) {m : ℝ}
    (hm : 0 < m) (t : ℝ) : diamond.squareMassShift ε m t ≠ 0 := by
  intro hx
  have H := congrArg Complex.re hx
  simp only [Plane.squareMassShift,Complex.sub_re,Complex.ofReal_re,Complex.I_mul_re,Complex.ofReal_im,
    neg_zero,sub_zero,Complex.zero_re] at H
  exact (sq_pos_of_pos hm).ne' H

/-- For every n, the order n+1 same-side pole acts on compact Cartesian
C^(n+1) complex tests via the iterated Euler test of the massive simple
pole, with the exact factor (m²)^(-n). -/
theorem Plane.massive_same_side_pole_order_boundary (diamond : Plane E) (ε : Evolution)
    {m : ℝ} (hm : 0 < m) (n : ℕ) {f : MassiveMomentum → ℂ}
    (hf : ContDiff ℝ ((n : WithTop ℕ∞) + 1) f) (hs : HasCompactSupport f) :
    Tendsto (fun h : Height => ∫ q, f q * (diamond.poleCoefficient ε h (massiveD m q))^(n+1))
      poleBoundaryHeights (𝓝 (bareComplexShellBoundary (diamond.eta ε) m (poleOrderEulerTest n f) /
        ((m ^ 2 : ℝ) : ℂ) ^ n)) := by
  have ht := pole_order_euler_test_contDiff n 1 hf
  have hts := pole_order_euler_test_compact n hs
  have hc := (diamond.square_mass_shift_tendsto ε m).pow n
  have hn : ((m^2:ℝ):ℂ) ≠ 0 := by exact_mod_cast (sq_pos_of_pos hm).ne'
  refine ((diamond.bare_massive_complex_c1 ε hm ht hts).div hc (pow_ne_zero _ hn)).congr fun h => ?_
  apply (div_eq_iff (pow_ne_zero _ (diamond.square_mass_shift_ne_zero ε hm h))).mpr
  dsimp only
  rw [← diamond.massive_pole_order_euler_reduction ε h m n (hf.of_le (by exact le_self_add)) hs, mul_comm]

end UV.SectorPlane
