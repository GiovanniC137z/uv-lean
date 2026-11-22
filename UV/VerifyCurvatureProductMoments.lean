import UV.AdvanceCurvatureWick

/-! Exact moments for every finite list of elementary preparation
coordinates, with repeated signed modes and field or color labels. -/

noncomputable section

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators NNReal

namespace UV.VerifyCurvatureProductMoments

open UV.NextCurvatureLaw UV.ContinueCurvatureGaussian

/-- The scalar pairing recurrence for the source preparation variance 1/2. -/
def scalarPairMoment : ℕ → ℝ
  | 0 => 1
  | 1 => 0
  | q + 2 => ((q : ℝ) + 1)/2 * scalarPairMoment q

private theorem gaussianBase_probability : IsProbabilityMeasure sourceGaussianBase := by
  rw [sourceGaussianBase_eq_gaussianReal]
  infer_instance

private theorem scalar_odd (q : ℕ) :
    (∫ x : ℝ, x ^ (2*q+1) ∂sourceGaussianBase) = 0 := by
  let m := (1/2 : ℝ≥0)
  have hmap : (gaussianReal 0 m).map (fun x : ℝ => -x) = gaussianReal 0 m := by simp [gaussianReal_map_neg]
  have hpow (x : ℝ) : (-x) ^ (2*q+1) = -(x ^ (2*q+1)) := by
    rw [pow_succ (-x), pow_mul (-x), neg_sq, mul_neg, ← pow_mul, ← pow_succ]
  rw [sourceGaussianBase_eq_gaussianReal]
  have hh : (∫ x : ℝ, x ^ (2*q+1) ∂gaussianReal 0 m) =
      ∫ x : ℝ, (-x) ^ (2*q+1) ∂gaussianReal 0 m := by
    rw [← integral_map (by fun_prop : AEMeasurable (fun x : ℝ => -x) (gaussianReal 0 m))
      (by fun_prop : AEStronglyMeasurable (fun x : ℝ => x ^ (2*q+1)) _), hmap]
  simp_rw [hpow, integral_neg] at hh
  exact eq_zero_of_neg_eq (Eq.symm hh)

private theorem scalar_moment_step (q : ℕ) :
    (∫ x : ℝ, x ^ (q+2) ∂sourceGaussianBase) =
      ((q : ℝ) + 1)/2 * ∫ x : ℝ, x ^ q ∂sourceGaussianBase := by
  rcases Nat.even_or_odd q with h | h
  · obtain ⟨k,hk⟩ := h
    rw [show q = 2*k by omega, show 2*k+2 = 2*(k+1) by omega,
      sourceGaussianBase_even_moment, sourceGaussianBase_even_moment, centered_gaussian_half_recurrence]
    push_cast
    ring
  · obtain ⟨k,hk⟩ := h
    rw [show q = 2*k+1 by omega, show 2*k+1+2 = 2*(k+1)+1 by omega, scalar_odd, scalar_odd, mul_zero]

/-- The exact scalar Gaussian moment equals its pairing recurrence at every
integer exponent, including the vanishing odd moments. -/
theorem scalarPairMoment_eq_integral (q : ℕ) :
    (∫ x : ℝ, x ^ q ∂sourceGaussianBase) = scalarPairMoment q := by
  letI := gaussianBase_probability
  induction q using Nat.twoStepInduction with
  | zero => simp [scalarPairMoment]
  | one => exact scalar_odd 0
  | more q hq _ => rw [scalar_moment_step, scalarPairMoment, hq]

private theorem base_power_integrable (q : ℕ) :
    Integrable (fun x : ℝ => x ^ q) sourceGaussianBase := by
  have he : sourceGaussian (1/2 : ℝ) = sourceGaussianBase := by unfold sourceGaussian; norm_num
  rw [← he]
  exact sourceGaussian_power_integrable _ _

/-- Mixed monomials in any finite list of actual signed elementary
coordinates factor into exact copies of the scalar pairing recurrence. -/
theorem coordinate_list_moment {n : ℕ} (l : List (ModeSlot n)) :
    Integrable (fun X => (l.map fun i => X i).prod) (commonGaussian n) ∧
    (∫ X, (l.map fun i => X i).prod ∂commonGaussian n) =
      ∏ i ∈ l.toFinset, scalarPairMoment (l.count i) := by
  classical
  letI := gaussianBase_probability
  let s := l.toFinset
  let F (Y : s → ℝ) : ℝ := ∏ i : s, Y i ^ l.count i.1
  let ν : Measure (s → ℝ) := Measure.pi (fun _ : s => sourceGaussianBase)
  have hp : MeasurePreserving s.restrict (commonGaussian n) ν :=
    ⟨Finset.measurable_restrict _, Measure.infinitePi_map_restrict _⟩
  have hF : Integrable F ν := Integrable.fintype_prod fun i : s => base_power_integrable (l.count i.1)
  have hprod (X : ModeSlot n → ℝ) : (l.map fun i => X i).prod = F (s.restrict X) := by
    rw [Finset.prod_list_map_count]
    change _ = ∏ i : s, X i.1 ^ l.count i.1
    rw [Finset.prod_coe_sort s (fun i => X i ^ l.count i)]
    apply Finset.prod_congr rfl
    intro i hi
    congr 1
    simp only [List.count_eq_countP]
    exact List.countP_congr fun j _ => by simp only [beq_iff_eq]
  constructor
  · exact (hp.integrable_comp_of_integrable hF).congr (Filter.Eventually.of_forall fun X => (hprod X).symm)
  · simp_rw [hprod]
    change (∫ X, F (s.restrict X) ∂Measure.infinitePi (fun _ : ModeSlot n => sourceGaussianBase)) = _
    rw [integral_restrict_infinitePi (fun _ : ModeSlot n => sourceGaussianBase) hF.aestronglyMeasurable]
    calc
      _ = ∏ i : s, ∫ x : ℝ, x ^ l.count i.1 ∂sourceGaussianBase :=
        integral_fintype_prod_eq_prod (fun i : s => fun x : ℝ => x ^ l.count i.1)
      _ = _ := by
        simp_rw [scalarPairMoment_eq_integral]
        exact Finset.prod_coe_sort s (fun i => scalarPairMoment (l.count i))

end UV.VerifyCurvatureProductMoments
