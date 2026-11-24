import UV.ContinueTwoBandDensityTrace

/-! The two-band Hamiltonian and its occupied-to-empty transition on a
locked plane. The unit Bloch vector lives in the real space of Pauli
coefficients, independently of the chosen geometric carrier unit. -/

noncomputable section
open Matrix
open scoped Matrix RealInnerProductSpace

namespace UV.SectorPlane

def twoBandGap (m v : ℝ) : ℝ := Real.sqrt (m^2 + v^2)

@[fun_prop] theorem continuous_twoBandGap (m : ℝ) : Continuous (twoBandGap m) := by
  unfold twoBandGap
  fun_prop

theorem twoBand_gap_pos {m : ℝ} (hm : 0 < m) (v : ℝ) : 0 < twoBandGap m v := by
  unfold twoBandGap
  positivity

theorem twoBand_gap_sq (m v : ℝ) : (twoBandGap m v)^2 = m^2 + v^2 :=
  Real.sq_sqrt (by positivity)

theorem twoBand_mass_le_gap {m : ℝ} (hm : 0 < m) (v : ℝ) : m ≤ twoBandGap m v := by
  nlinarith [twoBand_gap_sq m v, twoBand_gap_pos hm v, sq_nonneg v]

/-- Real coordinates in the Pauli coefficient space. -/
def twoBandBloch (m v : ℝ) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![v / twoBandGap m v, 0, m / twoBandGap m v]

theorem twoBand_bloch_unit {m : ℝ} (hm : 0 < m) (v : ℝ) : ‖twoBandBloch m v‖ = 1 := by
  have he := twoBand_gap_sq m v
  have hn : ‖twoBandBloch m v‖^2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
    simp [twoBandBloch, Real.norm_eq_abs, sq_abs, div_pow, he]
    field_simp
    ring
  nlinarith [norm_nonneg (twoBandBloch m v)]

def twoBandBlochUnit {m : ℝ} (hm : 0 < m) (v : ℝ) : UnitVector (EuclideanSpace ℝ (Fin 3)) :=
  ⟨twoBandBloch m v, twoBand_bloch_unit hm v⟩

def twoBandTransitionWeight (m v w : ℝ) : ℝ :=
  (1 - (m^2+v*w)/(twoBandGap m v*twoBandGap m w))/2

/-- The positive transition weight is the squared difference of the
two actual normalized Hamiltonian directions divided by four. -/
theorem twoBand_transition_distance {m : ℝ} (hm : 0 < m) (v w : ℝ) :
    twoBandTransitionWeight m v w =
      ‖(twoBandBlochUnit hm w).val - (twoBandBlochUnit hm v).val‖^2 / 4 := by
  change _ = ‖twoBandBloch m w - twoBandBloch m v‖^2/4
  rw [norm_sub_sq_real, twoBand_bloch_unit hm w, twoBand_bloch_unit hm v,
    PiLp.inner_apply, Fin.sum_univ_three]
  simp [twoBandBloch, twoBandTransitionWeight]
  ring

theorem twoBand_transition_nonneg {m : ℝ} (hm : 0 < m) (v w : ℝ) :
    0 ≤ twoBandTransitionWeight m v w := by
  rw [twoBand_transition_distance hm]
  positivity

theorem twoBand_transition_pos {m : ℝ} (hm : 0 < m) {v w : ℝ} (hvw : v ≠ w) :
    0 < twoBandTransitionWeight m v w := by
  rw [twoBand_transition_distance hm]
  have hne : twoBandBloch m w ≠ twoBandBloch m v := by
    intro eq
    have he := congrArg (fun (x : EuclideanSpace ℝ (Fin 3)) => x 2) eq
    have hv := congrArg (fun (x : EuclideanSpace ℝ (Fin 3)) => x 0) eq
    change m / twoBandGap m w = m / twoBandGap m v at he
    change w / twoBandGap m w = v / twoBandGap m v at hv
    have hG : twoBandGap m w = twoBandGap m v := by
      field_simp [(twoBand_gap_pos hm w).ne', (twoBand_gap_pos hm v).ne'] at he
      nlinarith
    rw [hG] at hv
    exact hvw ((div_left_inj' (twoBand_gap_pos hm v).ne').mp hv).symm
  exact div_pos (sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hne))) (by norm_num)

theorem twoBand_transition_upper {m : ℝ} (hm : 0 < m) (v w : ℝ) :
    twoBandTransitionWeight m v w ≤ (v-w)^2/(4*m^2) := by
  let A := twoBandGap m v
  let B := twoBandGap m w
  have hA : 0 < A := twoBand_gap_pos hm v
  have hB : 0 < B := twoBand_gap_pos hm w
  have hprod : m*m ≤ A*B := mul_le_mul (twoBand_mass_le_gap hm v)
    (twoBand_mass_le_gap hm w) hm.le hA.le
  have he : 2 * (A*B-(m^2+v*w)) ≤ (v-w)^2 := by
    nlinarith only [sq_nonneg (A-B), (twoBand_gap_sq m v : A^2 = _),
      (twoBand_gap_sq m w : B^2 = _)]
  change (1-(m^2+v*w)/(A*B))/2 ≤ _
  calc
    _ = (2*(A*B-(m^2+v*w))) / (4*(A*B)) := by field_simp; ring
    _ ≤ (v-w)^2/(4*(A*B)) := div_le_div_of_nonneg_right he (by positivity)
    _ ≤ _ := div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by nlinarith only [hprod])

def twoBandProjector (upper : Bool) (m v : ℝ) : TwoBandMatrix :=
  let e : ℂ := if upper then 1 else -1
  let E : ℂ := twoBandGap m v
  !![(1+e*m/E)/2, e*v/E/2; e*v/E/2, (1-e*m/E)/2]

/-- Spectral projectors of the actual zero-frequency Hamiltonian
square to themselves and have the signed band energy on their range. -/
theorem twoBand_projector_spectral {m : ℝ} (hm : 0 < m) (v : ℝ) (upper : Bool) :
    let P := twoBandProjector upper m v
    Pᴴ = P ∧ P*P = P ∧ twoBandSymbol m v 0 * P =
      ((if upper then (twoBandGap m v : ℂ) else -(twoBandGap m v : ℂ))) • P := by
  have hE : (twoBandGap m v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (twoBand_gap_pos hm v).ne'
  have hSq : (twoBandGap m v : ℂ)^2 = (m:ℂ)^2+(v:ℂ)^2 := by exact_mod_cast twoBand_gap_sq m v
  dsimp only
  constructor
  · ext i j
    cases upper <;> fin_cases i <;> fin_cases j <;> simp [twoBandProjector, Matrix.conjTranspose_apply]
  constructor
  all_goals
    ext i j
    cases upper <;> fin_cases i <;> fin_cases j <;>
      simp [twoBandProjector, twoBandSymbol, Matrix.mul_apply, Fin.sum_univ_two] <;>
      field_simp [hE] <;> ring_nf <;> rw [hSq] <;> ring

theorem twoBand_transition_projector_trace {m : ℝ} (hm : 0 < m) (v w : ℝ) :
    (twoBandProjector false m v * twoBandProjector true m w).trace =
      (twoBandTransitionWeight m v w : ℂ) := by
  have ha := Complex.ofReal_ne_zero.mpr (twoBand_gap_pos hm v).ne'
  have hb := Complex.ofReal_ne_zero.mpr (twoBand_gap_pos hm w).ne'
  rw [Matrix.trace, Fin.sum_univ_two]
  simp [twoBandProjector, twoBandTransitionWeight]
  field_simp [ha,hb]
  ring

end UV.SectorPlane
