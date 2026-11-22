import UV.ContinueCurvatureModes
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Independence.Integration

/-! Wick contractions of the actual independent signed-mode coordinates
for the two distinct real adjoint fields. The standard common law has
variance 1/2 in each real coordinate. -/

noncomputable section

open MeasureTheory ProbabilityTheory Real Filter
open scoped BigOperators NNReal Topology

namespace UV.AdvanceCurvatureWick

open UV.NextCurvatureLaw UV.ContinueCurvatureGaussian UV.ExtendCurvaturePotential
open UV.NextCurvatureFourierSummability UV.FurtherCurvatureLine

private theorem scalar_half_variance_law : sourceGaussian (1/2 : ℝ) = sourceGaussianBase := by
  unfold sourceGaussian
  norm_num

private theorem base_power_integrable (q : ℕ) :
    Integrable (fun x : ℝ => x ^ q) sourceGaussianBase := by
  rw [← scalar_half_variance_law]
  exact sourceGaussian_power_integrable _ _

private theorem coord_integral {n : ℕ} (i : ModeSlot n) (f : ℝ → ℝ) (hf : Measurable f) :
    (∫ X, f (X i) ∂commonGaussian n) = ∫ x, f x ∂sourceGaussianBase := by
  letI : IsProbabilityMeasure sourceGaussianBase := by rw [sourceGaussianBase_eq_gaussianReal]; infer_instance
  have h := measurePreserving_eval_infinitePi (μ := fun _ : ModeSlot n => sourceGaussianBase) i
  have hi := integral_map (μ := commonGaussian n) h.measurable.aemeasurable hf.aestronglyMeasurable
  have hm : (commonGaussian n).map (Function.eval i) = sourceGaussianBase := h.map_eq
  rw [hm] at hi
  exact hi.symm

private theorem coord_power_integrable {n : ℕ} (i : ModeSlot n) (q : ℕ) :
    Integrable (fun X : ModeSlot n → ℝ => X i ^ q) (commonGaussian n) := by
  letI : IsProbabilityMeasure sourceGaussianBase := by rw [sourceGaussianBase_eq_gaussianReal]; infer_instance
  exact (measurePreserving_eval_infinitePi (μ := fun _ : ModeSlot n => sourceGaussianBase) i).integrable_comp_of_integrable
    (base_power_integrable q)

private theorem coords_independent (n : ℕ) :
    iIndepFun (fun i (X : ModeSlot n → ℝ) => X i) (commonGaussian n) := by
  letI : IsProbabilityMeasure sourceGaussianBase := by rw [sourceGaussianBase_eq_gaussianReal]; infer_instance
  unfold commonGaussian
  exact iIndepFun_infinitePi (X := fun _ : ModeSlot n => id) fun _ => measurable_id

/-- Pairing two coordinates gives the exact diagonal covariance of the
standard product, including a repeated coordinate at a tadpole. -/
theorem baseCoord_pair_integral {n : ℕ} (i j : ModeSlot n) :
    (∫ X, X i * X j ∂commonGaussian n) = if i = j then 1/2 else 0 := by
  classical
  by_cases h : i = j
  · subst j
    rw [if_pos rfl]
    simp_rw [← sq, coord_integral i (fun x => x^2) (by fun_prop), ← scalar_half_variance_law]
    exact (sourceGaussian_even_moments (by norm_num : 0 ≤ (1/2 : ℝ))).1
  · rw [if_neg h]
    have hi := (coords_independent n).indepFun h
    rw [hi.integral_fun_mul_eq_mul_integral (measurable_pi_apply i).aestronglyMeasurable
      (measurable_pi_apply j).aestronglyMeasurable,
      coord_integral i (fun x => x) measurable_id, sourceGaussianBase_eq_gaussianReal,
      integral_id_gaussianReal, zero_mul]

private theorem baseCoord_pair_integrable {n : ℕ} (i j : ModeSlot n) :
    Integrable (fun X => X i * X j) (commonGaussian n) := by
  by_cases h : i = j
  · subst j
    simpa only [pow_two] using coord_power_integrable i 2
  · exact ((coords_independent n).indepFun h).integrable_mul
      (by simpa only [pow_one] using coord_power_integrable i 1)
      (by simpa only [pow_one] using coord_power_integrable j 1)

private theorem cross_pair_independent {n : ℕ} (i j k l : ModeSlot n)
    (hi : i.2.1 = 0) (hj : j.2.1 = 0) (hk : k.2.1 = 1) (hl : l.2.1 = 1) :
    IndepFun (fun X => X i * X j) (fun X => X k * X l) (commonGaussian n) := by
  apply (coords_independent n).indepFun_mul_mul (fun slot => measurable_pi_apply slot)
  all_goals
    intro h
    have he := congrArg (fun a : ModeSlot n => a.2.1) h
    simp [hi, hj, hk, hl] at he

/-- The first quartic vacuum contraction has only the two same-field
pairings. Cross-field contractions vanish identically. -/
theorem independentField_four_integral {n : ℕ} (i j k l : ModeSlot n)
    (hi : i.2.1 = 0) (hj : j.2.1 = 0) (hk : k.2.1 = 1) (hl : l.2.1 = 1) :
    (∫ X, (X i * X j) * (X k * X l) ∂commonGaussian n) =
      (if i = j then 1/2 else 0) * (if k = l then 1/2 else 0) := by
  classical
  rw [(cross_pair_independent i j k l hi hj hk hl).integral_fun_mul_eq_mul_integral,
    baseCoord_pair_integral, baseCoord_pair_integral]
  · exact (baseCoord_pair_integrable i j).aestronglyMeasurable
  · exact (baseCoord_pair_integrable k l).aestronglyMeasurable

private theorem independentField_four_integrable {n : ℕ} (i j k l : ModeSlot n)
    (hi : i.2.1 = 0) (hj : j.2.1 = 0) (hk : k.2.1 = 1) (hl : l.2.1 = 1) :
    Integrable (fun X => (X i * X j) * (X k * X l)) (commonGaussian n) :=
  (cross_pair_independent i j k l hi hj hk hl).integrable_mul
    (baseCoord_pair_integrable i j) (baseCoord_pair_integrable k l)

abbrev Leg (n : ℕ) := (Fin n × MeanZeroMode) × (Fin n × MeanZeroMode)

def leftSlot {n : ℕ} (e : Leg n) : ModeSlot n := (e.1.2, (0, e.1.1))
def rightSlot {n : ℕ} (e : Leg n) : ModeSlot n := (e.2.2, (1, e.2.1))

def vertexLegs (n : ℕ) (Λ : ℝ) : Finset (Leg n) :=
  let s := (Finset.univ : Finset (Fin n)) ×ˢ retainedModes Λ
  s ×ˢ s

def legShape {n : ℕ} (B : Fin n → Fin n → Fin n → ℝ) (ℓ : ℝ)
    (c : Fin n) (e : Leg n) : ContinuousField :=
  (B c e.1.1 e.2.1 * derivativeWeight 0 ℓ e.1.2 * derivativeWeight 0 ℓ e.2.2) •
    (realTorusMode e.1.2 * realTorusMode e.2.2)

/-- The actual bracket is the sum of the product of its two elementary
Fourier coefficients times the corresponding literal torus mode shape. -/
theorem cutoff_bracket_leg_expansion {n : ℕ} (B : Fin n → Fin n → Fin n → ℝ)
    (Λ ℓ : ℝ) (X : ModeSlot n → ℝ) (c : Fin n) :
    bracketCoordinate B (cutoffTransferredField Λ ℓ X 0) (cutoffTransferredField Λ ℓ X 1) c =
      ∑ e ∈ vertexLegs n Λ, (X (leftSlot e) * X (rightSlot e)) • legShape B ℓ c e := by
  ext x
  simp only [bracketCoordinate, cutoffTransferredField, transferredTerm, vertexLegs, legShape,
    leftSlot, rightSlot, ContinuousMap.sum_apply, ContinuousMap.smul_apply, ContinuousMap.mul_apply,
    smul_eq_mul, Finset.sum_product, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  let G (b : Fin n) (k l : MeanZeroMode) := B c a b *
    ((derivativeWeight 0 ℓ k * X (k, 0, a) * realTorusMode k x) *
      (derivativeWeight 0 ℓ l * X (l, 1, b) * realTorusMode l x))
  change (∑ b, ∑ l ∈ retainedModes Λ, ∑ k ∈ retainedModes Λ, G b k l) = _
  calc
    _ = ∑ b, ∑ k ∈ retainedModes Λ, ∑ l ∈ retainedModes Λ, G b k l :=
      Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ k ∈ retainedModes Λ, ∑ b, ∑ l ∈ retainedModes Λ, G b k l := Finset.sum_comm
    _ = _ := by
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun b _ => ?_
      refine Finset.sum_congr rfl fun l _ => ?_
      unfold G
      ring

def quarticMonomial {n : ℕ} (e f : Leg n) (X : ModeSlot n → ℝ) : ℝ :=
  (X (leftSlot e) * X (leftSlot f)) * (X (rightSlot e) * X (rightSlot f))

private theorem quarticMonomial_integrable {n : ℕ} (e f : Leg n) :
    Integrable (quarticMonomial e f) (commonGaussian n) :=
  independentField_four_integrable _ _ _ _ rfl rfl rfl rfl

private theorem quarticMonomial_integral {n : ℕ} (e f : Leg n) :
    (∫ X, quarticMonomial e f X ∂commonGaussian n) = if e = f then 1/4 else 0 := by
  classical
  change (∫ X, (X (leftSlot e) * X (leftSlot f)) * (X (rightSlot e) * X (rightSlot f))
    ∂commonGaussian n) = _
  rw [independentField_four_integral _ _ _ _ rfl rfl rfl rfl]
  by_cases he : e = f
  · subst f
    norm_num
  · rw [if_neg he]
    by_cases hleft : leftSlot e = leftSlot f
    · have hright : rightSlot e ≠ rightSlot f := by
        intro hr
        apply he
        exact Prod.ext (Prod.ext (congrArg (fun i : ModeSlot n => i.2.2) hleft)
          (congrArg Prod.fst hleft)) (Prod.ext (congrArg (fun i : ModeSlot n => i.2.2) hr)
          (congrArg Prod.fst hr))
      rw [if_neg hright, mul_zero]
    · rw [if_neg hleft, zero_mul]

/-- Exact finite polynomial expansion of the integrated squared bracket.
The vertex factor is a normalized Haar integral of four real signed modes. -/
theorem cutoffBracketPotential_quartic_expansion {n : ℕ} (B : Fin n → Fin n → Fin n → ℝ)
    (Λ ℓ : ℝ) (X : ModeSlot n → ℝ) : cutoffBracketPotential B Λ ℓ X =
      (1/2 : ℝ) * ∑ c, ∑ e ∈ vertexLegs n Λ, ∑ f ∈ vertexLegs n Λ,
        normalizedIntegral (legShape B ℓ c e * legShape B ℓ c f) * quarticMonomial e f X := by
  unfold cutoffBracketPotential bracketDensity
  simp only [cutoff_bracket_leg_expansion, pow_two, Finset.sum_mul_sum, map_smul, map_sum, smul_eq_mul]
  congr 1
  refine Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun e _ => ?_))
  refine Finset.sum_congr rfl (fun f _ => ?_)
  rw [smul_mul_assoc, mul_smul_comm, map_smul, map_smul]
  unfold quarticMonomial
  simp only [smul_eq_mul]
  ring

/-- The Gaussian expectation of the actual finite-action bracket reduces
to one diagonal sum over both signed modes and both color slots. -/
theorem cutoffBracketPotential_diagonal_wick {n : ℕ} (B : Fin n → Fin n → Fin n → ℝ)
    (Λ ℓ : ℝ) : (∫ X, cutoffBracketPotential B Λ ℓ X ∂commonGaussian n) =
      (1/8 : ℝ) * ∑ c, ∑ e ∈ vertexLegs n Λ, normalizedIntegral (legShape B ℓ c e ^ 2) := by
  classical
  simp_rw [cutoffBracketPotential_quartic_expansion, integral_const_mul]
  let A (c : Fin n) (e f : Leg n) := normalizedIntegral (legShape B ℓ c e * legShape B ℓ c f)
  let m := vertexLegs n Λ
  have hInt (c : Fin n) (e f : Leg n) : Integrable
      (fun X => A c e f * quarticMonomial e f X) (commonGaussian n) :=
    (quarticMonomial_integrable e f).const_mul _
  have hInt₁ (c : Fin n) (e : Leg n) : Integrable
      (fun X => ∑ f ∈ m, A c e f * quarticMonomial e f X) (commonGaussian n) :=
    integrable_finset_sum _ (fun f _ => hInt c e f)
  have hInt₂ (c : Fin n) : Integrable
      (fun X => ∑ e ∈ m, ∑ f ∈ m, A c e f * quarticMonomial e f X) (commonGaussian n) :=
    integrable_finset_sum _ (fun e _ => hInt₁ c e)
  have houter : (∫ X, ∑ c, ∑ e ∈ m, ∑ f ∈ m, A c e f * quarticMonomial e f X
      ∂commonGaussian n) = ∑ c, ∑ e ∈ m, ∫ X, ∑ f ∈ m, A c e f * quarticMonomial e f X
      ∂commonGaussian n := by
    rw [integral_finset_sum _ (fun c _ => hInt₂ c)]
    exact Finset.sum_congr rfl fun c _ => integral_finset_sum _ (fun e _ => hInt₁ c e)
  have hinner (c : Fin n) (e : Leg n) (he : e ∈ m) :
      (∫ X, ∑ f ∈ m, A c e f * quarticMonomial e f X ∂commonGaussian n) =
        A c e e * (1/4) := by
    rw [integral_finset_sum _ (fun f _ => hInt c e f)]
    simp_rw [integral_const_mul, quarticMonomial_integral]
    rw [Finset.sum_eq_single_of_mem e he]
    · rw [if_pos rfl]
    · intro f hf hne
      rw [if_neg (Ne.symm hne), mul_zero]
  have hf : (∑ c, ∑ e ∈ m, ∫ X, ∑ f ∈ m, A c e f * quarticMonomial e f X
      ∂commonGaussian n) = ∑ c, ∑ e ∈ m, A c e e * (1/4) :=
    Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun e he => hinner c e he
  change (1/2 : ℝ) * (∫ X, ∑ c, ∑ e ∈ m, ∑ f ∈ m, A c e f * quarticMonomial e f X
    ∂commonGaussian n) = _
  rw [houter, hf]
  simp only [← Finset.sum_mul, A, pow_two]
  ring

end UV.AdvanceCurvatureWick
