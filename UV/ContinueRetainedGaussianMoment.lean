import UV.ContinueRetainedGaussianMass

/-! Uniform positive Gaussian moment comparison after scaling the independent
Euclidean coordinates by their positive covariance lengths. -/

noncomputable section

open Matrix MeasureTheory Set
open scoped Matrix BigOperators InnerProductSpace ENNReal

namespace UV

variable {D : Type*} [Fintype D]

/-- The squared Euclidean norm in independent real coordinates. -/
def retainedCoordinateNormSq (x : D → ℝ) : ℝ :=
  ∑ i, x i ^ 2

/-- Real-power moment with a diagonal nonnegative covariance scale. -/
def retainedScaledMoment (h : ℝ) (a : D → ℝ) : ℝ≥0∞ :=
  ∫⁻ x : D → ℝ, ENNReal.ofReal ((1 + ∑ i, a i * x i ^ 2) ^ h *
    Real.exp (-(retainedCoordinateNormSq x / 2)))

private theorem retained_rpow_exp_bound {h q : ℝ} (hh : 0 ≤ h) (hq : 0 ≤ q) :
    (1 + q) ^ h * Real.exp (-(q / 2)) ≤
      (1 + 4 * h) ^ h * Real.exp (-(q / 4)) := by
  let B := 1 + 4 * h
  have hB : 0 < B := by dsimp [B]; positivity
  have hB1 : 1 ≤ B := by dsimp [B]; linarith
  have hsmall : h / B ≤ 1 / 4 := (div_le_iff₀ hB).mpr (by dsimp [B]; linarith)
  have hq' : 0 ≤ q / B := div_nonneg hq hB.le
  have hlog := Real.log_le_sub_one_of_pos (show 0 < 1 + q / B by positivity)
  have haux : (1 + q / B) ^ h ≤ Real.exp (q / 4) := by
    rw [Real.rpow_def_of_pos (show 0 < 1 + q / B by positivity), Real.exp_le_exp]
    calc
      Real.log (1 + q / B) * h ≤ (q / B) * h :=
        mul_le_mul_of_nonneg_right (by linarith) hh
      _ = h / B * q := by ring
      _ ≤ q / 4 := by linarith [mul_le_mul_of_nonneg_right hsmall hq]
  have hsum : 1 + q ≤ B * (1 + q / B) := by
    calc
      _ ≤ B + q := by linarith
      _ = _ := by rw [mul_add, mul_one, mul_div_cancel₀ _ hB.ne']
  have hpow := Real.rpow_le_rpow (show 0 ≤ 1 + q by positivity) hsum hh
  rw [Real.mul_rpow hB.le (by positivity)] at hpow
  calc
    _ ≤ (B ^ h * Real.exp (q / 4)) * Real.exp (-(q / 2)) :=
      mul_le_mul_of_nonneg_right (hpow.trans
        (mul_le_mul_of_nonneg_left haux (Real.rpow_nonneg hB.le _))) (Real.exp_pos _).le
    _ = _ := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring

private theorem retained_standard_integrable (D : Type*) [Fintype D]
    (b : ℝ) (hb : 0 < b) :
    Integrable (fun x : D → ℝ => Real.exp (-(retainedCoordinateNormSq x / b))) := by
  have he (x : D → ℝ) : Real.exp (-(retainedCoordinateNormSq x / b)) =
      ∏ i, Real.exp (-(1 / b) * x i ^ 2) := by
    rw [retainedCoordinateNormSq, Finset.sum_div, ← Finset.sum_neg_distrib, Real.exp_sum]
    apply Finset.prod_congr rfl
    intro i _
    congr 1
    ring
  simp_rw [he]
  exact Integrable.fintype_prod (fun _ => integrable_exp_neg_mul_sq (one_div_pos.mpr hb))

/-- Constants for the standard-coordinate comparison depend only on dimension
and the real moment exponent. -/
theorem retainedScaledMoment_comparison (h : ℝ) (hh : 0 ≤ h) :
    ∃ c C : ℝ≥0∞, 0 < c ∧ C < ∞ ∧
      ∀ a : D → ℝ, (∀ i, 0 ≤ a i) →
        c * ENNReal.ofReal ((1 + ∑ i, a i) ^ h) ≤ retainedScaledMoment h a ∧
          retainedScaledMoment h a ≤ C * ENNReal.ofReal ((1 + ∑ i, a i) ^ h) := by
  let c := ENNReal.ofReal (Real.exp (-(2 * Fintype.card D)))
  let U := ∫⁻ x : D → ℝ, ENNReal.ofReal (Real.exp (-(retainedCoordinateNormSq x / 4)))
  let C := ENNReal.ofReal ((1 + 4 * h) ^ h) * U
  have hC : C < ∞ := by
    have hi := ofReal_integral_eq_lintegral_ofReal (retained_standard_integrable D 4 (by norm_num))
      (ae_of_all _ fun _ => (Real.exp_pos _).le)
    change ENNReal.ofReal ((1 + 4 * h) ^ h) * U < ⊤
    rw [show U = _ from hi.symm]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  refine ⟨c, C, ENNReal.ofReal_pos.mpr (Real.exp_pos _), hC, ?_⟩
  intro a ha
  let A := 1 + ∑ i, a i
  have hA : 0 ≤ A := add_nonneg zero_le_one (Finset.sum_nonneg (fun i _ => ha i))
  have ha0 : 0 ≤ A ^ h := Real.rpow_nonneg hA h
  constructor
  · let box : Set (D → ℝ) := Set.univ.pi (fun _ => Set.Icc (1 : ℝ) 2)
    have hbox : MeasurableSet box := MeasurableSet.univ_pi (fun _ => measurableSet_Icc)
    have hvolume : volume box = 1 := by
      change Measure.pi (fun _ : D => volume) (univ.pi (fun _ => Icc (1 : ℝ) 2)) = 1
      rw [Measure.pi_pi]
      norm_num [Real.volume_Icc]
    calc
      c * ENNReal.ofReal (A ^ h) =
          ∫⁻ x in box, c * ENNReal.ofReal (A ^ h) := by rw [setLIntegral_const, hvolume, mul_one]
      _ ≤ retainedScaledMoment h a := by
        rw [← lintegral_indicator hbox]
        apply lintegral_mono
        intro x
        by_cases hx : x ∈ box
        · rw [indicator_of_mem hx]
          have hxi (i : D) : x i ∈ Icc (1 : ℝ) 2 := hx i (Set.mem_univ i)
          have h1 : A ≤ 1 + ∑ i, a i * x i ^ 2 := by
            apply add_le_add_left
            apply Finset.sum_le_sum
            intro i _
            calc
              a i = a i * 1 := (mul_one _).symm
              _ ≤ _ := mul_le_mul_of_nonneg_left (by nlinarith [(hxi i).1]) (ha i)
          have h4 : retainedCoordinateNormSq x ≤ 4 * Fintype.card D := by
            calc
              _ ≤ ∑ _i : D, (4 : ℝ) := by
                apply Finset.sum_le_sum
                intro i _
                nlinarith [(hxi i).1, (hxi i).2]
              _ = _ := by simp [mul_comm]
          rw [show c = _ from rfl, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
          apply ENNReal.ofReal_le_ofReal
          rw [mul_comm (Real.exp _)]
          exact mul_le_mul (Real.rpow_le_rpow hA h1 hh)
            (Real.exp_le_exp.mpr (by linarith)) (Real.exp_pos _).le
            (Real.rpow_nonneg (hA.trans h1) h)
        · simp [indicator_of_notMem hx]
  · have hpoint (x : D → ℝ) :
        (1 + ∑ i, a i * x i ^ 2) ^ h * Real.exp (-(retainedCoordinateNormSq x / 2)) ≤
          (A ^ h * (1 + 4 * h) ^ h) * Real.exp (-(retainedCoordinateNormSq x / 4)) := by
      let q := retainedCoordinateNormSq x
      have hq : 0 ≤ q := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
      have hs : 0 ≤ ∑ i, a i * x i ^ 2 :=
        Finset.sum_nonneg (fun i _ => mul_nonneg (ha i) (sq_nonneg _))
      have hsum : 1 + ∑ i, a i * x i ^ 2 ≤ A * (1 + q) := by
        have hb : ∑ i, a i * x i ^ 2 ≤ A * q := by
          change ∑ i, a i * x i ^ 2 ≤ A * (∑ i, x i ^ 2)
          rw [Finset.mul_sum]
          apply Finset.sum_le_sum
          intro i _
          apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
          have hi := Finset.single_le_sum (f := a) (fun j _ => ha j) (Finset.mem_univ i)
          dsimp [A]
          linarith
        dsimp [A] at *
        rw [mul_add, mul_one]
        linarith [Finset.sum_nonneg (s := Finset.univ) (fun i _ => ha i)]
      have hp := Real.rpow_le_rpow (show 0 ≤ 1 + ∑ i, a i * x i ^ 2 by positivity) hsum hh
      rw [Real.mul_rpow hA (by positivity)] at hp
      calc
        _ ≤ (A ^ h * (1 + q) ^ h) * Real.exp (-(q / 2)) :=
          mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
        _ ≤ _ := by
          rw [mul_assoc, mul_assoc]
          exact mul_le_mul_of_nonneg_left (retained_rpow_exp_bound hh hq) ha0
    calc
      retainedScaledMoment h a ≤ ∫⁻ x : D → ℝ, ENNReal.ofReal ((A ^ h * (1 + 4 * h) ^ h) *
          Real.exp (-(retainedCoordinateNormSq x / 4))) :=
        lintegral_mono (fun x => ENNReal.ofReal_le_ofReal (hpoint x))
      _ = C * ENNReal.ofReal (A ^ h) := by
        have he (x : D → ℝ) :
            ENNReal.ofReal ((A ^ h * (1 + 4 * h) ^ h) *
                Real.exp (-(retainedCoordinateNormSq x / 4))) =
              ENNReal.ofReal (A ^ h * (1 + 4 * h) ^ h) *
                ENNReal.ofReal (Real.exp (-(retainedCoordinateNormSq x / 4))) :=
          ENNReal.ofReal_mul (mul_nonneg ha0 (Real.rpow_nonneg (by positivity) _))
        simp_rw [he]
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ENNReal.ofReal_mul ha0]
        unfold C U
        ac_rfl

end UV
