import UV.NextCurvatureFourierSummability
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction

/-! The transferred real fields and quartic bracket density on the
dimensionless four-torus of period 2π, on one fixed sector plane.
The Haar normalization and orthonormal adjoint coordinates are retained. -/

noncomputable section

open MeasureTheory Real Filter
open scoped BigOperators Topology

namespace UV.ExtendCurvaturePotential

open UV.NextCurvatureLaw UV.NextCurvatureFourierSummability
open UV.FurtherCurvatureLine UV.FurtherCurvatureShell
open UV.RevisionCurvatureDeterminant (latticeFrequency)

abbrev Torus := Fin 4 → AddCircle (2 * π)
abbrev ContinuousField := C(Torus, ℝ)

private instance positivePeriod : Fact (0 < (2 : ℝ) * π) := ⟨by positivity⟩

def normalizedTorusVolume : Measure Torus :=
  Measure.pi (fun _ => AddCircle.haarAddCircle)

instance : IsProbabilityMeasure normalizedTorusVolume := by
  unfold normalizedTorusVolume
  infer_instance

def torusCharacter (k : TorusMode) : C(Torus, ℂ) :=
  ∏ j : Fin 4, (fourier (T := (2 : ℝ) * π) (k j)).comp
    ⟨Function.eval j, continuous_apply j⟩

theorem torusCharacter_point_norm (k : TorusMode) (x : Torus) :
    ‖torusCharacter k x‖ = 1 := by
  unfold torusCharacter
  simp only [ContinuousMap.prod_apply, ContinuousMap.comp_apply,
    norm_prod, fourier_apply, Circle.norm_coe, Finset.prod_const_one]

private theorem active_nonempty (k : MeanZeroMode) :
    (Finset.univ.filter (fun j : Fin 4 => k.1 j ≠ 0)).Nonempty := by
  by_contra! hn
  apply k.2
  funext j
  by_contra hj
  exact hn ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩

def firstActive (k : MeanZeroMode) : Fin 4 :=
  (Finset.univ.filter (fun j : Fin 4 => k.1 j ≠ 0)).min' (active_nonempty k)

def realTorusMode (k : MeanZeroMode) : ContinuousField :=
  if 0 < k.1 (firstActive k) then
    sqrt 2 • ((⟨Complex.re, Complex.continuous_re⟩ : C(ℂ, ℝ)).comp (torusCharacter k))
  else
    sqrt 2 • ((⟨Complex.im, Complex.continuous_im⟩ : C(ℂ, ℝ)).comp (torusCharacter (-k.1)))

/-- Signed lattice modes are indexed as real sine and cosine directions.
Their pointwise supremum norm is at most sqrt(2) at normalized Haar volume. -/
theorem realTorusMode_norm_bound (k : MeanZeroMode) : ‖realTorusMode k‖ ≤ sqrt 2 := by
  apply (ContinuousMap.norm_le _ (sqrt_nonneg _)).2
  intro x
  unfold realTorusMode
  split
  · simp only [ContinuousMap.smul_apply, ContinuousMap.comp_apply, ContinuousMap.coe_mk]
    rw [norm_smul, Real.norm_of_nonneg (sqrt_nonneg _)]
    apply mul_le_of_le_one_right (sqrt_nonneg _)
    simpa only [Real.norm_eq_abs, torusCharacter_point_norm] using
      Complex.abs_re_le_norm (torusCharacter k x)
  · simp only [ContinuousMap.smul_apply, ContinuousMap.comp_apply, ContinuousMap.coe_mk]
    rw [norm_smul, Real.norm_of_nonneg (sqrt_nonneg _)]
    apply mul_le_of_le_one_right (sqrt_nonneg _)
    simpa only [Real.norm_eq_abs, torusCharacter_point_norm] using
      Complex.abs_im_le_norm (torusCharacter (-k.1) x)

def retainedModes (Λ : ℝ) : Finset MeanZeroMode :=
  (sphericalModes Λ).subtype (· ≠ 0)

theorem mem_retainedModes (Λ : ℝ) (k : MeanZeroMode) :
    k ∈ retainedModes Λ ↔ latticeFrequency k ≤ Λ := by
  simp only [retainedModes, Finset.mem_subtype, mem_sphericalModes]
  exact ⟨And.right, fun h => ⟨k.2,h⟩⟩

private theorem retainedModes_cofinal :
    Tendsto retainedModes atTop atTop := by
  refine tendsto_atTop.mpr fun s => eventually_atTop.mpr ⟨∑ k ∈ s, latticeFrequency k, ?_⟩
  intro Λ hΛ k hk
  apply (mem_retainedModes Λ k).mpr
  exact (Finset.single_le_sum (f := fun k => latticeFrequency (k : MeanZeroMode))
    (fun _ _ => sqrt_nonneg _) hk).trans hΛ

def transferredTerm {n : ℕ} (ℓ : ℝ) (X : ModeSlot n → ℝ)
    (a : Fin 2) (c : Fin n) (k : MeanZeroMode) : ContinuousField :=
  (derivativeWeight 0 ℓ k * X (k, (a, c))) • realTorusMode k

def cutoffTransferredField {n : ℕ} (Λ ℓ : ℝ) (X : ModeSlot n → ℝ)
    (a : Fin 2) (c : Fin n) : ContinuousField :=
  ∑ k ∈ retainedModes Λ, transferredTerm ℓ X a c k

def fullTransferredField {n : ℕ} (ℓ : ℝ) (X : ModeSlot n → ℝ)
    (a : Fin 2) (c : Fin n) : ContinuousField :=
  ∑' k, transferredTerm ℓ X a c k

private theorem transferredTerm_norm_bound {n : ℕ} (ℓ : ℝ) (X : ModeSlot n → ℝ)
    (a : Fin 2) (c : Fin n) (k : MeanZeroMode) :
    ‖transferredTerm ℓ X a c k‖ ≤ sqrt 2 * (derivativeWeight 0 ℓ k * |X (k, (a, c))|) := by
  unfold transferredTerm
  rw [norm_smul, norm_mul, Real.norm_of_nonneg (derivativeWeight_nonneg 0 ℓ k),
    Real.norm_eq_abs, mul_comm (sqrt 2)]
  exact mul_le_mul_of_nonneg_left (realTorusMode_norm_bound k)
    (mul_nonneg (derivativeWeight_nonneg 0 ℓ k) (abs_nonneg _))

theorem transferred_field_uniform_limit {n : ℕ} {ℓ : ℝ} {X : ModeSlot n → ℝ}
    (h : Summable fun i : ModeSlot n => derivativeWeight 0 ℓ i.1 * |X i|)
    (a : Fin 2) (c : Fin n) :
    Tendsto (fun Λ : ℝ => cutoffTransferredField Λ ℓ X a c) atTop
      (𝓝 (fullTransferredField ℓ X a c)) := by
  let i : MeanZeroMode → ModeSlot n := fun k => (k, (a,c))
  have hi : Function.Injective i := fun _ _ hh => congrArg (fun j : ModeSlot n => j.1) hh
  have hs : Summable (fun k : MeanZeroMode => derivativeWeight 0 ℓ k * |X (k, (a, c))|) := by
    simpa only [Function.comp_def, i] using h.comp_injective hi
  have hnorm : Summable fun k => ‖transferredTerm ℓ X a c k‖ :=
    (hs.mul_left (sqrt 2)).of_nonneg_of_le (fun _ => norm_nonneg _)
      (transferredTerm_norm_bound ℓ X a c)
  exact hnorm.of_norm.hasSum.comp retainedModes_cofinal

/-- The source structure constants are expressed in the orthonormal
coefficient basis. The bracket on two fields is evaluated at each torus point. -/
def bracketCoordinate {n : ℕ} (B : Fin n → Fin n → Fin n → ℝ)
    (U W : Fin n → ContinuousField) (c : Fin n) : ContinuousField :=
  ∑ a, ∑ b, B c a b • (U a * W b)

def bracketDensity {n : ℕ} (B : Fin n → Fin n → Fin n → ℝ)
    (U W : Fin n → ContinuousField) : ContinuousField :=
  (1/2 : ℝ) • ∑ c, bracketCoordinate B U W c ^ 2

private theorem field_integrable (f : ContinuousField) : Integrable f normalizedTorusVolume :=
  (BoundedContinuousFunction.mkOfCompact f).integrable _

def normalizedIntegral : ContinuousField →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ x, f x ∂normalizedTorusVolume
      map_add' := fun f g => integral_add (field_integrable f) (field_integrable g)
      map_smul' := fun r f => integral_const_mul r _ }
    1 (fun f => by
      change ‖∫ x, f x ∂normalizedTorusVolume‖ ≤ 1 * ‖f‖
      simpa only [one_mul, BoundedContinuousFunction.norm_mkOfCompact] using
        (BoundedContinuousFunction.norm_integral_le_norm normalizedTorusVolume
          (BoundedContinuousFunction.mkOfCompact f)))

def cutoffBracketPotential {n : ℕ} (B : Fin n → Fin n → Fin n → ℝ) (Λ ℓ : ℝ)
    (X : ModeSlot n → ℝ) : ℝ :=
  normalizedIntegral (bracketDensity B (cutoffTransferredField Λ ℓ X 0)
    (cutoffTransferredField Λ ℓ X 1))

def fullBracketPotential {n : ℕ} (B : Fin n → Fin n → Fin n → ℝ) (ℓ : ℝ)
    (X : ModeSlot n → ℝ) : ℝ :=
  normalizedIntegral (bracketDensity B (fullTransferredField ℓ X 0) (fullTransferredField ℓ X 1))

theorem bracketDensity_nonneg {n : ℕ} (B : Fin n → Fin n → Fin n → ℝ)
    (U W : Fin n → ContinuousField) (x : Torus) : 0 ≤ bracketDensity B U W x := by
  unfold bracketDensity
  simp only [ContinuousMap.smul_apply, smul_eq_mul, ContinuousMap.sum_apply, ContinuousMap.pow_apply]
  positivity

theorem fullBracketPotential_nonneg {n : ℕ} (B : Fin n → Fin n → Fin n → ℝ) (ℓ : ℝ)
    (X : ModeSlot n → ℝ) : 0 ≤ fullBracketPotential B ℓ X := by
  apply integral_nonneg
  intro x
  apply bracketDensity_nonneg

theorem cutoffBracketPotential_nonneg {n : ℕ} (B : Fin n → Fin n → Fin n → ℝ) (Λ ℓ : ℝ)
    (X : ModeSlot n → ℝ) : 0 ≤ cutoffBracketPotential B Λ ℓ X := by
  apply integral_nonneg
  intro x
  apply bracketDensity_nonneg

theorem bracketPotential_limit {n : ℕ} (B : Fin n → Fin n → Fin n → ℝ)
    {ℓ : ℝ} {X : ModeSlot n → ℝ}
    (hs : Summable (fun i : ModeSlot n => derivativeWeight 0 ℓ i.1 * |X i|)) :
    Tendsto (fun Λ : ℝ => cutoffBracketPotential B Λ ℓ X) atTop
      (𝓝 (fullBracketPotential B ℓ X)) := by
  have h (a : Fin 2) (c : Fin n) := transferred_field_uniform_limit hs a c
  have hb (c : Fin n) : Tendsto
      (fun Λ : ℝ => bracketCoordinate B (cutoffTransferredField Λ ℓ X 0)
        (cutoffTransferredField Λ ℓ X 1) c) atTop
      (𝓝 (bracketCoordinate B (fullTransferredField ℓ X 0) (fullTransferredField ℓ X 1) c)) := by
    unfold bracketCoordinate
    apply tendsto_finset_sum
    intro a _
    apply tendsto_finset_sum
    intro b _
    exact tendsto_const_nhds.smul ((h 0 a).mul (h 1 b))
  have hv : Tendsto
      (fun Λ : ℝ => bracketDensity B (cutoffTransferredField Λ ℓ X 0)
        (cutoffTransferredField Λ ℓ X 1)) atTop
      (𝓝 (bracketDensity B (fullTransferredField ℓ X 0) (fullTransferredField ℓ X 1))) := by
    unfold bracketDensity
    apply tendsto_const_nhds.smul
    exact tendsto_finset_sum _ (fun c _ => (hb c).pow 2)
  exact normalizedIntegral.continuous.continuousAt.tendsto.comp hv

/-- On the common preparation, the actual quartic norm-square potential
converges almost surely at every fixed positive normal separation. -/
theorem ae_bracketPotential_limit {n : ℕ} (B : Fin n → Fin n → Fin n → ℝ) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ∀ᵐ X ∂commonGaussian n,
      Tendsto (fun Λ : ℝ => cutoffBracketPotential B Λ ℓ X) atTop
        (𝓝 (fullBracketPotential B ℓ X)) :=
  (ae_weighted_transfer_summable n hℓ).mono fun _ h => bracketPotential_limit B (h 0)

theorem cutoffBracketPotential_measurable {n : ℕ} (B : Fin n → Fin n → Fin n → ℝ) (Λ : ℝ) :
    Measurable (fun p : ℝ × (ModeSlot n → ℝ) => cutoffBracketPotential B Λ p.1 p.2) := by
  let f (z : (ℝ × (ModeSlot n → ℝ)) × Torus) : ℝ :=
    bracketDensity B (cutoffTransferredField Λ z.1.1 z.1.2 0)
      (cutoffTransferredField Λ z.1.1 z.1.2 1) z.2
  have hf : Measurable f := by
    unfold f bracketDensity bracketCoordinate cutoffTransferredField transferredTerm
    simp only [ContinuousMap.smul_apply, ContinuousMap.sum_apply, ContinuousMap.mul_apply,
      ContinuousMap.pow_apply, smul_eq_mul]
    unfold derivativeWeight curvatureCovariance
    fun_prop (disch := exact ContinuousMap.continuous _)
  change Measurable (fun p : ℝ × (ModeSlot n → ℝ) => ∫ x, f (p,x) ∂normalizedTorusVolume)
  exact (hf.stronglyMeasurable.integral_prod_right' (ν := normalizedTorusVolume)).measurable

end UV.ExtendCurvaturePotential
