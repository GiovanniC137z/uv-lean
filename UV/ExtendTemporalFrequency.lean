import UV.ContinuationGraphMoments
import UV.ContinuationSectorPlane
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! Absolute carrier-frequency estimates for the common finite graph routing.
The real integration variable is the intrinsic component on the chosen
norm-one sector-plane carrier. -/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology BigOperators

namespace UV.SectorPlane

/-- The fixed-units one-dimensional temporal envelope, with power (a). -/
def frequencyEnvelope (a u : ℝ) : ℝ := (1 + u ^ 2) ^ (-a / 2)

theorem frequencyEnvelope_pos (a u : ℝ) : 0 < frequencyEnvelope a u :=
  Real.rpow_pos_of_pos (by positivity) _

theorem frequencyEnvelope_le_one {a : ℝ} (ha : 0 ≤ a) (u : ℝ) : frequencyEnvelope a u ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [sq_nonneg u]) (by linarith)

theorem frequencyEnvelope_measurable (a : ℝ) : Measurable (frequencyEnvelope a) := by
  unfold frequencyEnvelope
  fun_prop

theorem frequencyEnvelope_integrable {a : ℝ} (ha : 1 < a) : Integrable (frequencyEnvelope a) volume := by
  have hc : (Module.finrank ℝ ℝ : ℝ) < a := by simpa using ha
  simpa only [frequencyEnvelope, Real.norm_eq_abs, sq_abs] using
    (integrable_rpow_neg_one_add_norm_sq (μ := (volume : Measure ℝ)) hc)

/-- All retained trees have one weight, including a single tree with no
chords. Parallel edges remain distinct elements of the edge index. -/
def frequencyTreeWeight (T : Type*) [Fintype T] : ℝ := (Fintype.card T : ℝ)⁻¹

theorem frequencyTreeWeight_pos (T : Type*) [Fintype T] [Nonempty T] :
    0 < frequencyTreeWeight T := inv_pos.mpr (by exact_mod_cast Fintype.card_pos)

theorem sum_frequencyTreeWeight (T : Type*) [Fintype T] [Nonempty T] :
    ∑ _ : T, frequencyTreeWeight T = 1 := by
  have h : (Fintype.card T : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [frequencyTreeWeight, nsmul_eq_mul, h]

variable {T E : Type*} [Fintype T] [DecidableEq E] {L : ℕ}

/-- The edge set of the chord coordinates for a particular tree. -/
def frequencyChords (r : T → Fin L → E) (t : T) : Finset E := Finset.univ.image (r t)

/-- Chord probability for the uniform tree distribution. -/
def frequencyChordShare (r : T → Fin L → E) (e : E) : ℝ :=
  ∑ t, if e ∈ frequencyChords r t then frequencyTreeWeight T else 0

theorem frequencyChordShare_nonneg (r : T → Fin L → E) (e : E) : 0 ≤ frequencyChordShare r e := by
  apply Finset.sum_nonneg
  intro t _
  split_ifs <;> simp [frequencyTreeWeight]

theorem frequencyChordShare_le_one [Nonempty T] (r : T → Fin L → E) (e : E) :
    frequencyChordShare r e ≤ 1 := by
  rw [← sum_frequencyTreeWeight T]
  apply Finset.sum_le_sum
  intro t _
  split_ifs <;> simp [frequencyTreeWeight]

theorem frequencyChordShare_pos_of_mem [Nonempty T] (r : T → Fin L → E) (e : E)
    (t : T) (ht : e ∈ frequencyChords r t) : 0 < frequencyChordShare r e := by
  unfold frequencyChordShare
  refine lt_of_lt_of_le (frequencyTreeWeight_pos T) ?_
  convert Finset.single_le_sum (f := fun t => if e ∈ frequencyChords r t then frequencyTreeWeight T else 0)
    (fun t _ => ?_) (Finset.mem_univ t) using 1
  · simp [ht]
  · exact ite_nonneg (by simp [frequencyTreeWeight]) le_rfl

theorem frequencyChordShare_lt_one_of_omitted [Nonempty T] (r : T → Fin L → E) (e : E)
    (t : T) (ht : e ∉ frequencyChords r t) : frequencyChordShare r e < 1 := by
  rw [← sum_frequencyTreeWeight T]
  refine Finset.sum_lt_sum (fun t _ => ?_) ⟨t, Finset.mem_univ t, ?_⟩
  · split_ifs <;> simp [frequencyTreeWeight]
  · simpa [ht] using frequencyTreeWeight_pos T

/-- The actual auxiliary tree product on the same routed frequencies. -/
def frequencyTreeMajorant (r : T → Fin L → E) (a : E → ℝ) (u : E → ℝ) (t : T) : ℝ :=
  ∏ j, frequencyEnvelope (a (r t j) / frequencyChordShare r (r t j)) (u (r t j))

variable [Fintype E]

private theorem frequencyTreeMajorant_prod_edges (r : T → Fin L → E) (a : E → ℝ) (u : E → ℝ)
    (t : T) (hinj : Function.Injective (r t)) :
    frequencyTreeMajorant r a u t =
      ∏ e, if e ∈ frequencyChords r t then
        frequencyEnvelope (a e / frequencyChordShare r e) (u e) else 1 := by
  unfold frequencyTreeMajorant frequencyChords
  rw [← Finset.prod_filter]
  have h : Finset.univ.filter (fun e => e ∈ Finset.univ.image (r t)) = Finset.univ.image (r t) := by
    ext e
    simp
  rw [h, Finset.prod_image (fun _ _ _ _ h => hinj h)]

/-- The exact geometric product of tree majorants recovers every
nonbridge edge envelope, with the bridges omitted. -/
theorem frequencyTreeMajorant_geometric_product (r : T → Fin L → E)
    (a : E → ℝ) (u : E → ℝ) (hinj : ∀ t, Function.Injective (r t)) :
    (∏ t, frequencyTreeMajorant r a u t ^ frequencyTreeWeight T) =
      ∏ e, if 0 < frequencyChordShare r e then frequencyEnvelope (a e) (u e) else 1 := by
  classical
  have hp (t : T) : frequencyTreeMajorant r a u t ^ frequencyTreeWeight T =
      ∏ e, (1 + u e ^ 2) ^ (if e ∈ frequencyChords r t then
        (- (a e / frequencyChordShare r e) / 2) * frequencyTreeWeight T else 0) := by
    rw [frequencyTreeMajorant_prod_edges r a u t (hinj t), ← Real.finset_prod_rpow]
    · apply Finset.prod_congr rfl
      intro e _
      by_cases h : e ∈ frequencyChords r t
      · simp only [h, if_true, frequencyEnvelope]
        rw [Real.rpow_mul (by positivity)]
      · simp [h]
    · intro e _
      split_ifs
      · exact (frequencyEnvelope_pos _ _).le
      · positivity
  simp_rw [hp]
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro e _
  rw [← Real.rpow_sum_of_pos (by positivity : 0 < (1 : ℝ) + u e ^ 2)]
  have hsum : (∑ t, if e ∈ frequencyChords r t then
      (- (a e / frequencyChordShare r e) / 2) * frequencyTreeWeight T else 0) =
        (- (a e / frequencyChordShare r e) / 2) * frequencyChordShare r e := by
    rw [frequencyChordShare, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    split_ifs <;> simp
  rw [hsum]
  by_cases hb : 0 < frequencyChordShare r e
  · rw [if_pos hb, frequencyEnvelope]
    congr 1
    field_simp [hb.ne']
  · rw [if_neg hb, le_antisymm (le_of_not_gt hb) (frequencyChordShare_nonneg r e),
      mul_zero, Real.rpow_zero]

/-- The actual full frequency-envelope product is bounded by the weighted
geometric tree product. Bridges contribute factors bounded by one. -/
theorem frequencyEnvelope_le_treeMajorants (r : T → Fin L → E)
    (a : E → ℝ) (ha : ∀ e, 0 ≤ a e) (u : E → ℝ) (hinj : ∀ t, Function.Injective (r t)) :
    (∏ e, frequencyEnvelope (a e) (u e)) ≤
      ∏ t, frequencyTreeMajorant r a u t ^ frequencyTreeWeight T := by
  rw [frequencyTreeMajorant_geometric_product r a u hinj]
  refine Finset.prod_le_prod (fun e _ => (frequencyEnvelope_pos _ _).le) (fun e _ => ?_)
  split_ifs
  · rfl
  · exact frequencyEnvelope_le_one (ha e) (u e)

end UV.SectorPlane
