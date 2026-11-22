import UV.ExtendTemporalFrequency
import Mathlib.MeasureTheory.Integral.Pi

/-! Uniform absolute bounds on the carrier-frequency integral, retaining the
chord coordinate change and its determinant on each tree chart. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal Topology BigOperators

namespace UV.SectorPlane

abbrev FrequencyCoordinates (L : ℕ) := Fin L → ℝ

/-- Affine external-frequency shifts leave the exact linear volume factor
unchanged. This works for the empty chart and for an arbitrary invertible chart. -/
theorem frequency_affine_map_volume {L : ℕ} (M : Matrix (Fin L) (Fin L) ℝ)
    (hM : M.det ≠ 0) (s : FrequencyCoordinates L) :
    Measure.map (fun q : FrequencyCoordinates L => M.mulVec q + s) volume =
      ENNReal.ofReal |M.det⁻¹| • (volume : Measure (FrequencyCoordinates L)) := by
  have hf : Measurable (Matrix.toLin' M) :=
    (Matrix.toLin' M).continuous_of_finiteDimensional.measurable
  have ht := measurePreserving_add_right (volume : Measure (FrequencyCoordinates L)) s
  rw [show (fun q : FrequencyCoordinates L => M.mulVec q + s) =
    (fun x : FrequencyCoordinates L => x + s) ∘ Matrix.toLin' M by rfl,
    ← Measure.map_map ht.measurable hf, Real.map_matrix_volume_pi_eq_smul_volume_pi hM,
    Measure.map_smul, ht.map_eq]

theorem frequency_affine_map_volume_unimodular {L : ℕ}
    (M : Matrix (Fin L) (Fin L) ℝ) (hM : |M.det| = 1) (s : FrequencyCoordinates L) :
    Measure.map (fun q : FrequencyCoordinates L => M.mulVec q + s) volume = volume := by
  have hn : M.det ≠ 0 := by
    intro hz
    simp [hz] at hM
  rw [frequency_affine_map_volume M hn s, abs_inv, hM, inv_one, ENNReal.ofReal_one, one_smul]

/-- The independent chord integral on one fixed tree chart factors with
the actual affine shift and absolute Jacobian. -/
theorem frequency_tree_factorization {L : ℕ} (M : Matrix (Fin L) (Fin L) ℝ)
    (hM : M.det ≠ 0) (s : FrequencyCoordinates L) (p : Fin L → ℝ)
    (hp : ∀ j, 1 < p j) :
    (∫⁻ q : FrequencyCoordinates L, ENNReal.ofReal
      (∏ j, frequencyEnvelope (p j) ((M.mulVec q + s) j))) =
      ENNReal.ofReal |M.det⁻¹| *
        ENNReal.ofReal (∏ j, ∫ z : ℝ, frequencyEnvelope (p j) z) := by
  have hbase : Measurable (fun q : FrequencyCoordinates L => ∏ j, frequencyEnvelope (p j) (q j)) :=
    Finset.measurable_prod _ fun j _ => (frequencyEnvelope_measurable _).comp (measurable_pi_apply j)
  have hf : Measurable (fun q : FrequencyCoordinates L => M.mulVec q + s) := by
    change Measurable (fun q : FrequencyCoordinates L => (Matrix.toLin' M) q + s)
    exact (Matrix.toLin' M).continuous_of_finiteDimensional.measurable.add_const s
  rw [← lintegral_map hbase.ennreal_ofReal hf, frequency_affine_map_volume M hM s,
    lintegral_smul_measure, smul_eq_mul]
  congr 1
  have hi : Integrable (fun q : FrequencyCoordinates L => ∏ j, frequencyEnvelope (p j) (q j)) volume :=
    Integrable.fintype_prod (fun j => frequencyEnvelope_integrable (hp j))
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun _ =>
    Finset.prod_nonneg fun _ _ => (frequencyEnvelope_pos _ _).le),
    integral_fintype_prod_volume_eq_prod (fun j : Fin L => frequencyEnvelope (p j))]

variable {G T E X : Type*} [Norm G] [Fintype T] [Nonempty T]
  [DecidableEq E] {L : ℕ}

/-- The exponent hypothesis is only strict for an edge that is a chord of
every chart. When the family comprises all spanning trees these are the
self-loops. -/
theorem frequency_tree_exponent_gt_one (r : T → Fin L → E) (a : E → ℝ)
    (ha : ∀ e, 1 ≤ a e)
    (hAlways : ∀ e, (∀ t, e ∈ frequencyChords r t) → 1 < a e)
    (t : T) (j : Fin L) :
    1 < a (r t j) / frequencyChordShare r (r t j) := by
  have hmem : r t j ∈ frequencyChords r t := Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩
  have hpos := frequencyChordShare_pos_of_mem r _ t hmem
  rw [lt_div_iff₀ hpos, one_mul]
  by_cases hall : ∀ t', r t j ∈ frequencyChords r t'
  · exact (frequencyChordShare_le_one r _).trans_lt (hAlways _ hall)
  · obtain ⟨t', h⟩ := not_forall.mp hall
    exact (frequencyChordShare_lt_one_of_omitted r _ t' h).trans_le (ha _)

/-- The exact graph constant built from the tree exponents and determinant
factors. It is independent of the external frequency shifts. -/
def frequency_tree_budget (r : T → Fin L → E) (M : T → Matrix (Fin L) (Fin L) ℝ)
    (a : E → ℝ) : ℝ≥0∞ :=
  ∏ t, (ENNReal.ofReal |(M t).det⁻¹| *
    ENNReal.ofReal (∏ j, ∫ z : ℝ, frequencyEnvelope (a (r t j) / frequencyChordShare r (r t j)) z))
      ^ frequencyTreeWeight T

theorem frequency_tree_budget_lt_top (r : T → Fin L → E)
    (M : T → Matrix (Fin L) (Fin L) ℝ) (a : E → ℝ) :
    frequency_tree_budget r M a < ∞ := by
  apply ENNReal.prod_lt_top
  intro t _
  exact ENNReal.rpow_lt_top_of_nonneg (frequencyTreeWeight_pos T).le
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)

variable [Fintype E]

/-- Weighted Hölder on the common carrier-frequency routing. The chord
charts may have distinct Jacobians. The uniform bound depends on their
linear parts and the line exponents, including for zero-dimensional routing. -/
theorem frequency_tree_integral_bound (diamond : Plane G)
    (u : Plane G → X → FrequencyCoordinates L → E → ℝ)
    (hu : ∀ x e, Measurable (fun q => u diamond x q e))
    (r : T → Fin L → E) (hinj : ∀ t, Function.Injective (r t))
    (M : T → Matrix (Fin L) (Fin L) ℝ) (hM : ∀ t, (M t).det ≠ 0)
    (shift : T → X → FrequencyCoordinates L)
    (hchart : ∀ t x q, (fun j => u diamond x q (r t j)) = (M t).mulVec q + shift t x)
    (a : E → ℝ) (ha : ∀ e, 1 ≤ a e)
    (hAlways : ∀ e, (∀ t, e ∈ frequencyChords r t) → 1 < a e) (x : X) :
    (∫⁻ q : FrequencyCoordinates L, ENNReal.ofReal (∏ e, frequencyEnvelope (a e) (u diamond x q e))) ≤
      frequency_tree_budget r M a := by
  let H (t : T) (q : FrequencyCoordinates L) := frequencyTreeMajorant r a (u diamond x q) t
  have hH (t : T) : Measurable (H t) := by
    unfold H frequencyTreeMajorant
    exact Finset.measurable_prod _ fun j _ => (frequencyEnvelope_measurable _).comp (hu x (r t j))
  have hpos (t : T) (q : FrequencyCoordinates L) : 0 < H t q :=
    Finset.prod_pos fun _ _ => frequencyEnvelope_pos _ _
  have hHolder := ENNReal.lintegral_prod_norm_pow_le (μ := (volume : Measure (FrequencyCoordinates L)))
    Finset.univ (f := fun t q => ENNReal.ofReal (H t q))
    (fun t _ => (hH t).ennreal_ofReal.aemeasurable)
    (sum_frequencyTreeWeight T) (fun _ _ => (frequencyTreeWeight_pos T).le)
  calc
    _ ≤ ∫⁻ q : FrequencyCoordinates L, ∏ t, ENNReal.ofReal (H t q) ^ frequencyTreeWeight T := by
      apply lintegral_mono
      intro q
      change ENNReal.ofReal (∏ e, frequencyEnvelope (a e) (u diamond x q e)) ≤
        ∏ t, ENNReal.ofReal (H t q) ^ frequencyTreeWeight T
      simp_rw [ENNReal.ofReal_rpow_of_pos (hpos _ q)]
      rw [← ENNReal.ofReal_prod_of_nonneg (fun t _ =>
        Real.rpow_nonneg (hpos t q).le (frequencyTreeWeight T))]
      exact ENNReal.ofReal_le_ofReal
        (frequencyEnvelope_le_treeMajorants r a (fun e => zero_le_one.trans (ha e)) (u diamond x q) hinj)
    _ ≤ _ := hHolder
    _ = _ := by
      unfold frequency_tree_budget
      apply Finset.prod_congr rfl
      intro t _
      congr 1
      have he : (fun q : FrequencyCoordinates L => ENNReal.ofReal (H t q)) =
          fun q => ENNReal.ofReal (∏ j, frequencyEnvelope
            (a (r t j) / frequencyChordShare r (r t j)) (((M t).mulVec q + shift t x) j)) := by
        funext q
        unfold H frequencyTreeMajorant
        simp_rw [congrFun (hchart t x q)]
      rw [he]
      exact frequency_tree_factorization (M t) (hM t) (shift t x) _
        (fun j => frequency_tree_exponent_gt_one r a ha hAlways t j)

/-- The complete amplitude is absolutely integrable on the shared chart
and obeys the uniform bound with the given vertex and line constants. -/
theorem frequency_tree_graph_integrable (diamond : Plane G)
    (u : Plane G → X → FrequencyCoordinates L → E → ℝ)
    (hu : ∀ x e, Measurable (fun q => u diamond x q e))
    (r : T → Fin L → E) (hinj : ∀ t, Function.Injective (r t))
    (M : T → Matrix (Fin L) (Fin L) ℝ) (hM : ∀ t, (M t).det ≠ 0)
    (shift : T → X → FrequencyCoordinates L)
    (hchart : ∀ t x q, (fun j => u diamond x q (r t j)) = (M t).mulVec q + shift t x)
    (a D : E → ℝ) (ha : ∀ e, 1 ≤ a e) (hD : ∀ e, 0 ≤ D e)
    (hAlways : ∀ e, (∀ t, e ∈ frequencyChords r t) → 1 < a e)
    (V : ℝ) (hV : 0 ≤ V)
    (K : Plane G → X → FrequencyCoordinates L → ℂ)
    (hK : ∀ x, AEStronglyMeasurable (K diamond x) volume)
    (hbound : ∀ x q, ‖K diamond x q‖ ≤ V * ∏ e, D e * frequencyEnvelope (a e) (u diamond x q e)) :
    ∀ x, Integrable (K diamond x) volume ∧
      (∫ q, ‖K diamond x q‖) ≤ V * (∏ e, D e) * (frequency_tree_budget r M a).toReal := by
  intro x
  let B := V * ∏ e, D e
  have hB : 0 ≤ B := mul_nonneg hV (Finset.prod_nonneg fun e _ => hD e)
  let F (q : FrequencyCoordinates L) := ENNReal.ofReal
    (∏ e, frequencyEnvelope (a e) (u diamond x q e))
  have hF : Measurable F := (Finset.measurable_prod _ (fun e _ =>
    (frequencyEnvelope_measurable (a e)).comp (hu x e))).ennreal_ofReal
  have hI := frequency_tree_integral_bound diamond u hu r hinj M hM shift hchart a ha hAlways x
  have hpoint (q : FrequencyCoordinates L) : ‖K diamond x q‖ₑ ≤ ENNReal.ofReal B * F q := by
    rw [← ofReal_norm, show F q = ENNReal.ofReal _ from rfl, ← ENNReal.ofReal_mul hB]
    exact ENNReal.ofReal_le_ofReal (by
      simpa only [Finset.prod_mul_distrib, mul_assoc, B] using hbound x q)
  have hlim : (∫⁻ q, ‖K diamond x q‖ₑ) ≤ ENNReal.ofReal B * frequency_tree_budget r M a := by
    calc
      _ ≤ ∫⁻ q, ENNReal.ofReal B * F q := lintegral_mono hpoint
      _ = ENNReal.ofReal B * ∫⁻ q, F q := lintegral_const_mul _ hF
      _ ≤ _ := mul_le_mul_left' hI _
  have hfin : ENNReal.ofReal B * frequency_tree_budget r M a < ∞ :=
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top (frequency_tree_budget_lt_top r M a)
  have hi : Integrable (K diamond x) volume :=
    ⟨hK x, hasFiniteIntegral_iff_enorm.mpr (hlim.trans_lt hfin)⟩
  refine ⟨hi, ?_⟩
  have hreal := ENNReal.toReal_mono hfin.ne hlim
  simpa only [← ofReal_integral_norm_eq_lintegral_enorm hi,
    ENNReal.toReal_ofReal (integral_nonneg fun _ => norm_nonneg _),
    ENNReal.toReal_mul, ENNReal.toReal_ofReal hB, B] using hreal

end UV.SectorPlane
