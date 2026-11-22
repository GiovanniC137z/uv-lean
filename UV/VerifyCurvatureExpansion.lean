import UV.VerifyCurvaturePairings
import UV.AdvanceCurvatureVertexRouted
import UV.AdvanceCurvatureLines
import UV.AdvanceCurvatureEnvelope

/-! Literal all-order finite spherical Wick expansion. An occurrence
records whether it is in the transferred quartic or an elementary probe;
both use the same field, color, and signed Fourier coordinate space. -/

noncomputable section

open MeasureTheory Real Filter
open scoped BigOperators Topology

namespace UV.VerifyCurvatureExpansion

open UV.NextCurvatureLaw UV.NextCurvatureFourierSummability UV.FurtherCurvatureShell
open UV.FurtherCurvatureLine UV.AdvanceCurvatureLines UV.AdvanceCurvatureWick
open UV.AdvanceCurvatureVertex UV.ExtendCurvaturePotential UV.VerifyCurvaturePairings
open UV.AdvanceCurvatureEnvelope
open UV.RevisionCurvatureDeterminant (latticeFrequency)

abbrev Occurrence (n : ℕ) := Bool × ModeSlot n

def occurrenceAmplitude {n : ℕ} (ℓ : ℝ) (i : Occurrence n) : ℝ :=
  if i.1 then derivativeWeight 0 ℓ i.2.1 else sqrt (2 * curvatureCovariance ℓ i.2.1)

def occurrenceValue {n : ℕ} (ℓ : ℝ) (X : ModeSlot n → ℝ) (i : Occurrence n) : ℝ :=
  occurrenceAmplitude ℓ i * X i.2

def occurrenceCovariance {n : ℕ} (ℓ : ℝ) (i j : Occurrence n) : ℝ :=
  occurrenceAmplitude ℓ i * occurrenceAmplitude ℓ j *
    diagonalCovariance (fun (_ : ModeSlot n) => (1/2 : ℝ)) i.2 j.2

/-- The exact contracted line, with zero, one, or two transferred ends. -/
def occurrenceLine (ℓ : ℝ) (k : MeanZeroMode) : Bool → Bool → ℝ
  | true, true => curvatureLine ℓ k
  | true, false => exp (-ℓ * latticeFrequency k) * curvatureCovariance ℓ k
  | false, true => exp (-ℓ * latticeFrequency k) * curvatureCovariance ℓ k
  | false, false => curvatureCovariance ℓ k

/-- Mode, field and color equality is required on an edge. Equal slots
have precisely the two-endpoint, one-endpoint or raw physical variance. -/
theorem occurrence_covariance_eq {n : ℕ} (ℓ : ℝ) (i j : Occurrence n) :
    occurrenceCovariance ℓ i j = if i.2 = j.2 then occurrenceLine ℓ i.2.1 i.1 j.1 else 0 := by
  classical
  rcases i with ⟨b,i⟩
  rcases j with ⟨c,j⟩
  by_cases h : i = j
  · subst j
    have hC : 0 ≤ 2 * curvatureCovariance ℓ i.1 := by unfold curvatureCovariance; positivity
    have hS := Real.mul_self_sqrt hC
    cases b <;> cases c <;>
      simp only [occurrenceCovariance, occurrenceAmplitude, occurrenceLine, diagonalCovariance,
        Bool.false_eq_true, if_false, if_true]
    · rw [hS]
      ring
    · simp only [derivativeWeight, pow_zero, one_mul]
      linear_combination (exp (-ℓ * latticeFrequency i.1)/2) * hS
    · simp only [derivativeWeight, pow_zero, one_mul]
      linear_combination (exp (-ℓ * latticeFrequency i.1)/2) * hS
    · simpa only [← pow_two, div_eq_mul_inv, one_div, one_mul] using transferWeight_sq_half ℓ i.1
  · simp [occurrenceCovariance, diagonalCovariance, h]

/-- The spherical raw-probe and mixed contractions are uniformly bounded
on every nonnegative depth, at the same fixed Euclidean momentum. -/
theorem noninternal_line_norm_le (ℓ : ℝ) (hℓ : 0 ≤ ℓ) (k : MeanZeroMode) (b c : Bool)
    (hnot : (b && c) = false) : ‖occurrenceLine ℓ k b c‖ ≤ 1 := by
  have hf : 1 ≤ latticeFrequency k :=
    (show (1 : ℝ) ≤ latticeHeight k from Nat.one_le_cast.mpr
      (Nat.pos_of_ne_zero (latticeHeight_ne_zero k.2))).trans (latticeHeight_le_latticeFrequency _)
  have hC : 0 ≤ curvatureCovariance ℓ k := by unfold curvatureCovariance; positivity
  have hc := (mode_covariance_le_boundary ℓ k).trans (inv_le_one_of_one_le₀ (one_le_pow₀ hf))
  have hE : exp (-ℓ * latticeFrequency k) ≤ 1 := Real.exp_le_one_iff.mpr
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hℓ) (zero_le_one.trans hf))
  have hM : ‖exp (-ℓ * latticeFrequency k) * curvatureCovariance ℓ k‖ ≤ 1 := by
    rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_nonneg _) hC)]
    exact (mul_le_of_le_one_left hC hE).trans hc
  cases b <;> cases c
  · simpa only [occurrenceLine, Real.norm_of_nonneg hC] using hc
  · exact hM
  · exact hM
  · simp at hnot

abbrev VertexChoice (n : ℕ) := Fin n × (Leg n × Leg n)

def sphericalVertexChoices (n : ℕ) (Λ : ℝ) : Finset (VertexChoice n) :=
  Finset.univ ×ˢ (vertexLegs n Λ ×ˢ vertexLegs n Λ)

def vertexOccurrences {n : ℕ} (v : VertexChoice n) : List (Occurrence n) :=
  [(true, leftSlot v.2.1), (true, leftSlot v.2.2),
    (true, rightSlot v.2.1), (true, rightSlot v.2.2)]

def vertexCoefficient {n : ℕ} (B : Fin n → Fin n → Fin n → ℝ) (v : VertexChoice n) : ℝ :=
  (1/2 : ℝ) * curvatureVertexFactor B v.1 v.2.1 v.2.2

def vertexTerm {n : ℕ} (B : Fin n → Fin n → Fin n → ℝ) (ℓ : ℝ)
    (X : ModeSlot n → ℝ) (v : VertexChoice n) : ℝ :=
  vertexCoefficient B v * ((vertexOccurrences v).map (occurrenceValue ℓ X)).prod

theorem cutoff_potential_vertex_sum {n : ℕ} (B : Fin n → Fin n → Fin n → ℝ) (Λ ℓ : ℝ)
    (X : ModeSlot n → ℝ) : cutoffBracketPotential B Λ ℓ X =
      ∑ v ∈ sphericalVertexChoices n Λ, vertexTerm B ℓ X v := by
  rw [cutoffBracketPotential_haar_expansion]
  simp only [sphericalVertexChoices, Finset.sum_product, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun f _ => ?_
  simp only [vertexTerm, vertexCoefficient, vertexOccurrences, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, occurrenceValue, occurrenceAmplitude, if_true, leftSlot, rightSlot,
    quarticMonomial]
  ring

def sourceOccurrences {n r : ℕ} (v : Fin r → VertexChoice n) (probes : List (ModeSlot n)) :
    List (Occurrence n) := (List.ofFn v).flatMap vertexOccurrences ++ probes.map (fun i => (false,i))

def rawProbeMonomial {n : ℕ} (ℓ : ℝ) (X : ModeSlot n → ℝ) (probes : List (ModeSlot n)) : ℝ :=
  (probes.map (depthRescale ℓ X)).prod

private theorem prod_flatMap_images {α β M : Type*} [CommMonoid M] (f : α → List β)
    (g : β → M) (l : List α) : ((l.flatMap f).map g).prod =
      (l.map fun a => ((f a).map g).prod).prod := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.flatMap_cons, List.map_append, List.prod_append, List.map_cons,
      List.prod_cons, ih]

private theorem sourceOccurrences_product {n r : ℕ} (v : Fin r → VertexChoice n) (ℓ : ℝ)
    (X : ModeSlot n → ℝ) (probes : List (ModeSlot n)) :
    ((sourceOccurrences v probes).map (occurrenceValue ℓ X)).prod =
      (∏ z, ((vertexOccurrences (v z)).map (occurrenceValue ℓ X)).prod) * rawProbeMonomial ℓ X probes := by
  simp only [sourceOccurrences, List.map_append, List.prod_append, prod_flatMap_images,
    List.map_ofFn, List.prod_ofFn, List.map_map]
  rfl

/-- The actual polynomial at every order, with an arbitrary list of fixed
raw elementary Fourier insertions, expands into these literal vertices. -/
theorem cutoff_power_probe_expansion {n : ℕ} (B : Fin n → Fin n → Fin n → ℝ) (Λ ℓ : ℝ)
    (X : ModeSlot n → ℝ) (r : ℕ) (probes : List (ModeSlot n)) :
    cutoffBracketPotential B Λ ℓ X ^ r * rawProbeMonomial ℓ X probes =
      ∑ v ∈ Fintype.piFinset (fun _ : Fin r => sphericalVertexChoices n Λ),
        (∏ z, vertexCoefficient B (v z)) *
          ((sourceOccurrences v probes).map (occurrenceValue ℓ X)).prod := by
  rw [cutoff_potential_vertex_sum]
  have hsum := Finset.sum_prod_piFinset (sphericalVertexChoices n Λ)
    (fun (_ : Fin r) v => vertexTerm B ℓ X v)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hsum
  rw [← hsum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp only [vertexTerm, Finset.prod_mul_distrib, sourceOccurrences_product]
  ring

/-- Exact pairing sum before integrating the depth. The identity covers
any fixed perturbative order and any elementary monomial, with no
Gaussian factorization or covariance hypothesis supplied by the caller. -/
theorem cutoff_power_probe_wick {n : ℕ} (B : Fin n → Fin n → Fin n → ℝ) (Λ ℓ : ℝ)
    (r : ℕ) (probes : List (ModeSlot n)) :
    Integrable (fun X => cutoffBracketPotential B Λ ℓ X ^ r * rawProbeMonomial ℓ X probes)
      (commonGaussian n) ∧
    (∫ X, cutoffBracketPotential B Λ ℓ X ^ r * rawProbeMonomial ℓ X probes ∂commonGaussian n) =
      ∑ v ∈ Fintype.piFinset (fun _ : Fin r => sphericalVertexChoices n Λ),
        (∏ z, vertexCoefficient B (v z)) * osWickMoment (occurrenceCovariance ℓ)
          (sourceOccurrences v probes).length (sourceOccurrences v probes) := by
  simp_rw [cutoff_power_probe_expansion]
  have hW (v : Fin r → VertexChoice n) :
      Integrable (fun X => ((sourceOccurrences v probes).map (occurrenceValue ℓ X)).prod)
        (commonGaussian n) ∧
      (∫ X, ((sourceOccurrences v probes).map (occurrenceValue ℓ X)).prod ∂commonGaussian n) =
        osWickMoment (occurrenceCovariance ℓ) (sourceOccurrences v probes).length
          (sourceOccurrences v probes) := weighted_coordinate_list_wick
    (Prod.snd : Occurrence n → ModeSlot n) (occurrenceAmplitude ℓ) (sourceOccurrences v probes)
    (sourceOccurrences v probes).length (by omega)
  refine ⟨integrable_finset_sum _ (fun v _ => (hW v).1.const_mul _), ?_⟩
  rw [integral_finset_sum _ (fun v _ => (hW v).1.const_mul _)]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [integral_const_mul]
  exact congrArg ((∏ z, vertexCoefficient B (v z)) * ·) (hW v).2

private theorem rawProbeMonomial_sq_integrable {n : ℕ} (ℓ : ℝ) (probes : List (ModeSlot n)) :
    Integrable (fun X => rawProbeMonomial ℓ X probes ^ 2) (commonGaussian n) := by
  let w (i : ModeSlot n) := sqrt (2 * curvatureCovariance ℓ i.1)
  have hi := (weighted_coordinate_list_wick id w (probes ++ probes) (probes ++ probes).length (by omega)).1
  apply hi.congr
  refine Eventually.of_forall fun X => ?_
  simp only [List.map_append, List.prod_append, id, rawProbeMonomial, w, pow_two]
  rfl

/-- For every fixed perturbative order and every fixed elementary mode
monomial, the actual continuum integrand is integrable at positive depth.
Its expectation is the limit of the spherical Wick-expanded expectations. -/
theorem full_power_probe_integral_limit {n : ℕ} (B : Fin n → Fin n → Fin n → ℝ)
    {ℓ : ℝ} (hℓ : 0 < ℓ) (r : ℕ) (probes : List (ModeSlot n)) :
    Integrable (fun X => fullBracketPotential B ℓ X ^ r * rawProbeMonomial ℓ X probes)
      (commonGaussian n) ∧
    Tendsto (fun Λ : ℝ =>
      ∫ X, cutoffBracketPotential B Λ ℓ X ^ r * rawProbeMonomial ℓ X probes ∂commonGaussian n)
      atTop (𝓝 (∫ X, fullBracketPotential B ℓ X ^ r * rawProbeMonomial ℓ X probes
        ∂commonGaussian n)) := by
  obtain ⟨E,hE,hbound⟩ := bracketPotential_power_envelope B hℓ (2*r)
  let D (X : ModeSlot n → ℝ) := (E X + rawProbeMonomial ℓ X probes ^ 2)/2
  have hD : Integrable D (commonGaussian n) := (hE.add (rawProbeMonomial_sq_integrable ℓ probes)).div_const _
  have hb : ∀ᵐ X ∂commonGaussian n, ∀ Λ : ℝ,
      ‖cutoffBracketPotential B Λ ℓ X ^ r * rawProbeMonomial ℓ X probes‖ ≤ D X := by
    filter_upwards [hbound] with X hX
    intro Λ
    let a := cutoffBracketPotential B Λ ℓ X ^ r
    let b := rawProbeMonomial ℓ X probes
    have ha : ‖a‖ ^ 2 ≤ E X := by
      rw [← norm_pow, ← pow_mul, Nat.mul_comm]
      exact hX Λ
    have hbb : ‖b‖ ^ 2 = b^2 := by rw [Real.norm_eq_abs, sq_abs]
    change ‖a * b‖ ≤ (E X + b^2)/2
    rw [norm_mul, ← hbb]
    nlinarith [sq_nonneg (‖a‖ - ‖b‖)]
  have hm (Λ : ℝ) : AEStronglyMeasurable
      (fun X => cutoffBracketPotential B Λ ℓ X ^ r * rawProbeMonomial ℓ X probes) (commonGaussian n) :=
    (cutoff_power_probe_wick B Λ ℓ r probes).1.aestronglyMeasurable
  have ht := (ae_bracketPotential_limit B hℓ).mono fun X hX =>
    (hX.pow r).const_mul (rawProbeMonomial ℓ X probes)
  have ht' : ∀ᵐ X ∂commonGaussian n, Tendsto
      (fun Λ : ℝ => cutoffBracketPotential B Λ ℓ X ^ r * rawProbeMonomial ℓ X probes)
      atTop (𝓝 (fullBracketPotential B ℓ X ^ r * rawProbeMonomial ℓ X probes)) := by
    filter_upwards [ht] with X hX
    simpa only [mul_comm] using hX
  have hfull := aestronglyMeasurable_of_tendsto_ae atTop (fun j : ℕ => hm j)
    (ht'.mono fun _ h => h.comp tendsto_natCast_atTop_atTop)
  refine ⟨hD.mono' hfull ?_, tendsto_integral_filter_of_dominated_convergence D
    (Eventually.of_forall hm) (Eventually.of_forall fun Λ => hb.mono fun _ h => h Λ) hD ht'⟩
  filter_upwards [ht', hb] with X hX hB
  exact le_of_tendsto hX.norm (Eventually.of_forall hB)

end UV.VerifyCurvatureExpansion
