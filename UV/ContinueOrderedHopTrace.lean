import UV.ContinueOrderedHopPaths

/-! Ordered two-band position-space traces. Each hop flips the charged slot,
and the two onsite intervals have opposite supports and signs. The
1/N logarithm coefficient and any real link phases are included. -/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace UV.SectorPlane

def orderedHopFlipMatrix (A : Bool → ℂ) : Matrix Bool Bool ℂ :=
  fun i j => if j = !i then A i else 0

def orderedHopFlipWord {ι : Type*} (A : ι → Bool → ℂ) (L : List ι) : Matrix Bool Bool ℂ :=
  (L.map (fun j => orderedHopFlipMatrix (A j))).prod

private theorem orderedHop_flip_cons {ι : Type*} (A : ι → Bool → ℂ) (j : ι) (L : List ι) (s t : Bool) :
    orderedHopFlipWord A (j::L) s t = A j s * orderedHopFlipWord A L (!s) t := by
  cases s <;> simp [orderedHopFlipWord,orderedHopFlipMatrix,Matrix.mul_apply]

theorem orderedHop_flip_support {ι : Type*} (A : ι → Bool → ℂ) (L : List ι) (s t : Bool)
    (h : t ≠ (if L.length % 2 = 0 then s else !s)) : orderedHopFlipWord A L s t = 0 := by
  induction L generalizing s with
  | nil =>
    simp only [List.length_nil, Nat.zero_mod, ↓reduceIte] at h
    simp [orderedHopFlipWord,h.symm]
  | cons j L ih =>
    rw [orderedHop_flip_cons]
    apply mul_eq_zero_of_right
    apply ih
    by_cases he : L.length % 2 = 0
    · have ho : (j::L).length % 2 ≠ 0 := by simp only [List.length_cons]; omega
      rw [if_neg ho] at h
      rw [if_pos he]
      exact h
    · have hz : (j::L).length % 2 = 0 := by simp only [List.length_cons]; omega
      rw [if_pos hz] at h
      simpa only [if_neg he,Bool.not_not] using h

theorem orderedHop_odd_trace_zero {ι : Type*} (A : ι → Bool → ℂ) (L : List ι) (h : L.length % 2 = 1) :
    (orderedHopFlipWord A L).trace = 0 := by
  rw [Matrix.trace,Fintype.sum_bool]
  change orderedHopFlipWord A L true true + orderedHopFlipWord A L false false = 0
  rw [orderedHop_flip_support A L true true (by simp [h]),orderedHop_flip_support A L false false (by simp [h]),zero_add]

private theorem orderedHop_flip_entry_bound {ι : Type*} {A : ι → Bool → ℂ} {B : ι → ℝ}
    (hA : ∀ j s, ‖A j s‖ ≤ B j) (L : List ι) (s t : Bool) :
    ‖orderedHopFlipWord A L s t‖ ≤ (L.map B).prod := by
  induction L generalizing s with
  | nil => cases s <;> cases t <;> norm_num [orderedHopFlipWord,Matrix.one_apply]
  | cons j L ih =>
    rw [orderedHop_flip_cons,norm_mul,List.map_cons,List.prod_cons]
    exact mul_le_mul (hA j s) (ih (!s)) (norm_nonneg _) ((norm_nonneg _).trans (hA j s))

theorem orderedHop_flip_trace_bound {ι : Type*} {A : ι → Bool → ℂ} {B : ι → ℝ}
    (hA : ∀ j s, ‖A j s‖ ≤ B j) (L : List ι) : ‖(orderedHopFlipWord A L).trace‖ ≤ 2*(L.map B).prod := by
  rw [Matrix.trace,Fintype.sum_bool]
  exact (norm_add_le _ _).trans ((add_le_add (orderedHop_flip_entry_bound hA L true true)
    (orderedHop_flip_entry_bound hA L false false)).trans_eq (two_mul _).symm)

def orderedHopStepAt {n : ℕ} (d : Fin n → OrderedHopStep) : Fin (n+1) → OrderedHopStep :=
  Fin.cons (orderedHopClosingStep d) d

theorem orderedHop_stepAt_continuous {n : ℕ} (j : Fin (n+1)) :
    Continuous (fun d => orderedHopStepAt (n := n) d j) := Fin.cases continuous_orderedHopClosingStep
      (fun i => continuous_apply i) j

theorem orderedHop_return_eq_prod {n : ℕ} (m σ : ℝ) (d : Fin n → OrderedHopStep) :
    (∏ j, orderedHopDensity m σ (orderedHopStepAt d j)) = orderedHopReturnDensity m σ d := by
  rw [Fin.prod_univ_succ]; rfl

/-- A representative of the onsite inverse times one heat hop. True is
the +m slot with u>0, false the -m slot with u<0. The value at the jump
is chosen zero. -/
def orderedHopOrientedWeight (m σ : ℝ) (s : Bool) (x : OrderedHopStep) : ℝ :=
  if s then (if 0 < x.1 then orderedHopDensity m σ x else 0)
  else (if x.1 < 0 then -orderedHopDensity m σ x else 0)

theorem orderedHop_oriented_bound {σ : ℝ} (hσ : 0 < σ) (m : ℝ) (s : Bool) (x : OrderedHopStep) :
    |orderedHopOrientedWeight m σ s x| ≤ orderedHopDensity m σ x := by
  have h := orderedHop_density_nonneg hσ m x
  cases s <;> unfold orderedHopOrientedWeight <;> simp only [Bool.false_eq_true,↓reduceIte] <;>
    split <;> simp [abs_of_nonneg h,h]

theorem orderedHop_oriented_measurable (m σ : ℝ) (s : Bool) : Measurable (orderedHopOrientedWeight m σ s) := by
  cases s <;> unfold orderedHopOrientedWeight <;> simp only [Bool.false_eq_true,↓reduceIte]
  · exact Measurable.ite (measurableSet_lt measurable_fst measurable_const)
      (continuous_orderedHopDensity m σ).measurable.neg measurable_const
  · exact Measurable.ite (measurableSet_lt measurable_const measurable_fst)
      (continuous_orderedHopDensity m σ).measurable measurable_const

abbrev OrderedHopPhases (n : ℕ) := Fin (n+1) → Bool → (Fin n → OrderedHopStep) → ℝ

def orderedHopPhasedWeight {n : ℕ} (m σ : ℝ) (φ : OrderedHopPhases n) (d : Fin n → OrderedHopStep)
    (j : Fin (n+1)) (s : Bool) : ℂ :=
  Complex.exp ((φ j s d : ℂ)*Complex.I) * (orderedHopOrientedWeight m σ s (orderedHopStepAt d j) : ℝ)

theorem orderedHop_phase_bound {n : ℕ} {σ : ℝ} (hσ : 0 < σ) (m : ℝ) (φ : OrderedHopPhases n)
    (d : Fin n → OrderedHopStep) (j : Fin (n+1)) (s : Bool) :
    ‖orderedHopPhasedWeight m σ φ d j s‖ ≤ orderedHopDensity m σ (orderedHopStepAt d j) := by
  simpa [orderedHopPhasedWeight,norm_mul,Complex.norm_exp,Real.norm_eq_abs] using orderedHop_oriented_bound hσ m s (orderedHopStepAt d j)

/-- Length N=n+1 in the logarithm expansion of I+X, with both initial
slots summed by the matrix trace and the signed real hopping g. -/
def orderedHopLogWord {n : ℕ} (m σ g : ℝ) (φ : OrderedHopPhases n) (d : Fin n → OrderedHopStep) : ℂ :=
  (((-1:ℝ)^n * g^(n+1) / (n+1:ℝ)) : ℝ) *
    (orderedHopFlipWord (orderedHopPhasedWeight m σ φ d) (List.ofFn id)).trace

theorem orderedHop_log_word_odd {n : ℕ} (hn : (n+1)%2 = 1) (m σ g : ℝ) (φ : OrderedHopPhases n)
    (d : Fin n → OrderedHopStep) : orderedHopLogWord m σ g φ d = 0 := by
  rw [orderedHopLogWord,orderedHop_odd_trace_zero _ _ (by simpa using hn),mul_zero]

theorem orderedHop_log_word_bound {n : ℕ} {σ : ℝ} (hσ : 0 < σ) (m g : ℝ) (φ : OrderedHopPhases n)
    (d : Fin n → OrderedHopStep) : ‖orderedHopLogWord m σ g φ d‖ ≤ 2/(n+1:ℝ)*|g|^(n+1)*orderedHopReturnDensity m σ d := by
  have hT := orderedHop_flip_trace_bound (orderedHop_phase_bound hσ m φ d) (List.ofFn id)
  simp only [List.map_ofFn,Function.comp_id,Fin.prod_ofFn,orderedHop_return_eq_prod] at hT
  rw [orderedHopLogWord,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_div,abs_mul,abs_pow,abs_pow,
    abs_neg,abs_one,one_pow,one_mul,abs_of_pos (show 0 < (n+1:ℝ) by positivity)]
  apply (mul_le_mul_of_nonneg_left hT (by positivity)).trans_eq
  ring

theorem orderedHop_log_word_measurable {n : ℕ} (m σ g : ℝ) {φ : OrderedHopPhases n}
    (hφ : ∀ j s, Measurable (φ j s)) : Measurable (orderedHopLogWord m σ g φ) := by
  have hStep (j : Fin (n+1)) (s : Bool) : Measurable (fun d => orderedHopPhasedWeight m σ φ d j s) := by
    unfold orderedHopPhasedWeight
    apply Measurable.mul
    · exact Complex.continuous_exp.measurable.comp (((Complex.continuous_ofReal.measurable.comp (hφ j s))).mul measurable_const)
    · exact Complex.continuous_ofReal.measurable.comp ((orderedHop_oriented_measurable m σ s).comp
        (orderedHop_stepAt_continuous j).measurable)
  have hWord (L : List (Fin (n+1))) (s t : Bool) :
      Measurable (fun d => orderedHopFlipWord (orderedHopPhasedWeight m σ φ d) L s t) := by
    induction L generalizing s with
    | nil => exact measurable_const
    | cons j L ih => simpa only [orderedHop_flip_cons] using (hStep j s).mul (ih (!s))
  unfold orderedHopLogWord
  simp only [Matrix.trace,Fintype.sum_bool,Matrix.diag_apply]
  exact measurable_const.mul ((hWord _ true true).add (hWord _ false false))

/-- The actual alternating signed traces (including 1/N) can be multiplied
by any measurable mark with a uniform polynomial count/perimeter bound. -/
theorem orderedHop_marked_log_words_summable {m σ g C : ℝ} (hσ : 0 < σ) (hg : 2*|g| < m)
    (hC : 0 ≤ C) (a b : ℕ) (φ : (n : ℕ) → OrderedHopPhases n)
    (hφ : ∀ n j s, Measurable (φ n j s)) (M : (n : ℕ) → (Fin n → OrderedHopStep) → ℂ)
    (hM : ∀ n, Measurable (M n))
    (hBound : ∀ n d, ‖M n d‖ ≤ C*(1+(n:ℝ))^a*(1+orderedHopPathLength d)^b) :
    (∀ n, Integrable (fun d => M n d * orderedHopLogWord m σ g (φ n) d)) ∧
      Summable (fun n => ∫ d, ‖M n d * orderedHopLogWord m σ g (φ n) d‖) := by
  obtain ⟨hE,hS⟩ := orderedHop_path_moments_summable hσ hg a b
  have hB (n : ℕ) (d : Fin n → OrderedHopStep) :
      ‖M n d * orderedHopLogWord m σ g (φ n) d‖ ≤ (2*C)*orderedHopPathEnvelope m σ g a b d := by
    have hOn : 2/(n+1:ℝ) ≤ 2 := (div_le_iff₀ (by positivity)).mpr (by nlinarith [Nat.cast_nonneg (α := ℝ) n])
    have hLen := orderedHop_path_length_nonneg d
    have hDen := orderedHop_return_density_nonneg hσ m d
    have hw := (orderedHop_log_word_bound hσ m g (φ n) d).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hOn (pow_nonneg (abs_nonneg _) _)) hDen)
    rw [norm_mul]
    apply (mul_le_mul (hBound n d) hw (norm_nonneg _) (by positivity)).trans_eq
    unfold orderedHopPathEnvelope
    ring
  have hI (n : ℕ) := ((hE n).const_mul (2*C)).mono' ((hM n).mul
    (orderedHop_log_word_measurable m σ g (hφ n))).aestronglyMeasurable (Filter.Eventually.of_forall (hB n))
  refine ⟨hI,Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _) (fun n => ?_) (hS.mul_left (2*C))⟩
  simpa only [integral_const_mul] using integral_mono (hI n).norm ((hE n).const_mul (2*C)) (hB n)

end UV.SectorPlane
