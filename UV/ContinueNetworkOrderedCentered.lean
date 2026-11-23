import UV.ContinueNetworkOrderedMonomial
import UV.ContinueNetworkOrderedSectors
import UV.ContinueNetworkPrecisionChart
import UV.ContinueNetworkPolynomialNormIntegration
import UV.ContinueNetworkPolynomialNormPullback

/-! End-to-end ordered-sector criterion for the literal centered
Schwinger cost, in the selected physical momentum coordinates. -/

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators ENNReal

namespace UV

open ContinueNetworkPrecision

variable {d a m : ℕ} {b : Fin m → ℕ}

def directionalCenteredSectorCost
    (A : DirectionalMomentum d →ₗ[ℝ] DirectionalMomentum a)
    (C : ∀ e, DirectionalMomentum d →ₗ[ℝ] DirectionalMomentum (b e))
    (ν : Fin m → ℝ) (P : MvPolynomial (Fin d) ℂ) : ℝ≥0∞ :=
  ∫⁻ t in directionalOrderedSet m, directionalOrderedDensity ν t *
    (∫⁻ k : DirectionalMomentum d,
      ENNReal.ofReal (‖directionalNumerator P k‖ * Real.exp (-sourcePrecision A C t k)))

private theorem directionalGaussianSchwingerMonomial_eq_orderedDensity
    (label : Fin d → Option (Fin m)) (ν : Fin m → ℝ)
    (β : Fin d →₀ ℕ) (t : Fin m → ℝ) :
    directionalGaussianSchwingerMonomial label ν β t =
      directionalOrderedDensity (directionalMonomialExponent ν label β) t := by
  unfold directionalGaussianSchwingerMonomial directionalOrderedDensity
  apply Finset.prod_congr rfl
  intro j _
  have he :
      (directionalGaussianEdgeCost label β j : ℝ) / 2 =
        ∑ i ∈ Finset.univ.filter (fun i => label i = some j), directionalMonomialLoss β i := by
    unfold directionalGaussianEdgeCost
    push_cast
    rw [Finset.sum_div]
    exact (Finset.sum_subtype _ (by simp) (fun i : Fin d => (1 + (β i : ℝ)) / 2)).symm.trans
      (Finset.sum_congr rfl (fun i _ => by unfold directionalMonomialLoss; ring))
  rw [he]
  rfl

/-- For each strictly ordered sector, the literal centered Gaussian
with its routed precision has finite cost exactly when every surviving
monomial in the selected chart satisfies every strict prefix inequality.
The same chart identifies each physical kernel flag with its weak
coordinate subspace. -/
theorem directionalCenteredSectorCost_finite_iff
    (A : DirectionalMomentum d →ₗ[ℝ] DirectionalMomentum a)
    (C : ∀ e, DirectionalMomentum d →ₗ[ℝ] DirectionalMomentum (b e))
    (ν : Fin m → ℝ) (P : MvPolynomial (Fin d) ℂ)
    (hinj : Function.Injective (fun k : DirectionalMomentum d => (A k, fun e => C e k))) :
    ∃ (chart : DirectionalMomentum d ≃L[ℝ] DirectionalMomentum d)
      (label : Fin d → Option (Fin m)),
      (∀ j : ℕ, j ≤ m →
        Module.finrank ℝ (sourceNullFlag A C j) =
          Nat.card {i : Fin d // (label i).elim False (fun e => e.val < j)} ∧
        ∀ k : DirectionalMomentum d, k ∈ sourceNullFlag A C j ↔
          ∀ i : Fin d, (label i).elim True (fun e => j ≤ e.val) → chart k i = 0) ∧
      (directionalCenteredSectorCost A C ν P < ⊤ ↔
        ∀ β ∈ (directionalPolynomialComposeLinear chart.symm.toContinuousLinearMap P).support,
          ∀ j, 0 < directionalOrderedPrefix (directionalMonomialExponent ν label β) j) := by
  obtain ⟨chart, label, D, hD, hprec, hflags⟩ := source_greedy_euclidean_chart A C hinj
  refine ⟨chart, label, hflags, ?_⟩
  let T := directionalPolynomialComposeLinear chart.symm.toContinuousLinearMap P
  let μ : Measure (Fin m → ℝ) := volume.restrict (directionalOrderedSet m)
  let B (c : ℝ) : ℝ≥0∞ := ∫⁻ t, directionalOrderedDensity ν t *
    ENNReal.ofReal (c * directionalGaussianCoefficientBudget (directionalGaussianRowWeights label t) T) ∂μ
  have hD0 : 0 < D := zero_lt_one.trans_le hD
  obtain ⟨c₁, c₂, hc₁, hc₂, hnorm⟩ :=
    directionalGaussianLIntegral_physical_norm_equivalent zero_lt_one hD0 chart P
  have ha : ∀ᵐ t ∂μ, t ∈ directionalOrderedSet m :=
    ae_restrict_mem (directionalOrderedSet_open m).measurableSet
  have hpos : ∀ᵐ t ∂μ, ∀ e, 0 < t e := ha.mono fun t ht e =>
    (((directionalOrderedSet_mem_iff t).1 ht).2 e).1
  have hmin (t : Fin m → ℝ) :
      Measurable (fun k : DirectionalMomentum d => sourcePrecision A C t k) := by
    apply Continuous.measurable
    unfold sourcePrecision
    have hA := (A.continuous_of_finiteDimensional.norm).pow 2
    apply hA.add
    exact continuous_finset_sum _ fun e _ =>
      continuous_const.mul (((C e).continuous_of_finiteDimensional.norm).pow 2)
  have hint (t : Fin m → ℝ) (ht : t ∈ directionalOrderedSet m) :
      ENNReal.ofReal (c₁ * directionalGaussianCoefficientBudget (directionalGaussianRowWeights label t) T) ≤
        (∫⁻ k : DirectionalMomentum d,
          ENNReal.ofReal (‖directionalNumerator P k‖ * Real.exp (-sourcePrecision A C t k))) ∧
      (∫⁻ k : DirectionalMomentum d,
          ENNReal.ofReal (‖directionalNumerator P k‖ * Real.exp (-sourcePrecision A C t k))) ≤
        ENNReal.ofReal (c₂ * directionalGaussianCoefficientBudget (directionalGaussianRowWeights label t) T) := by
    rcases (directionalOrderedSet_mem_iff t).1 ht with ⟨hmono, ht⟩
    have ht0 (e : Fin m) : 0 < t e := (ht e).1
    have ht1 (e : Fin m) : t e ≤ 1 := (ht e).2.le
    exact hnorm (directionalGaussianRowWeights label t)
      (directionalGaussianRowWeights_pos label ht0) (sourcePrecision A C t) (hmin t)
      (fun k => by simpa only [one_mul] using (hprec t k hmono.monotone
        (fun e => (ht0 e).le) ht1).1)
      (fun k => (hprec t k hmono.monotone (fun e => (ht0 e).le) ht1).2)
  have hlo : B c₁ ≤ directionalCenteredSectorCost A C ν P := by
    apply lintegral_mono_ae
    filter_upwards [ha] with t ht
    exact mul_le_mul_left' (hint t ht).1 _
  have hhi : directionalCenteredSectorCost A C ν P ≤ B c₂ := by
    apply lintegral_mono_ae
    filter_upwards [ha] with t ht
    exact mul_le_mul_left' (hint t ht).2 _
  have hbudget (c : ℝ) (hc : 0 < c) :
      B c < ⊤ ↔ ∀ β ∈ T.support, ∀ j,
        0 < directionalOrderedPrefix (directionalMonomialExponent ν label β) j := by
    unfold B directionalOrderedDensity
    rw [directionalGaussianCoefficientBudget_schwinger_finite_iff μ label ν T hc
      (fun e => measurable_pi_apply e) hpos]
    simp_rw [directionalGaussianSchwingerMonomial_eq_orderedDensity]
    change (∀ β ∈ T.support, directionalOrderedCost (directionalMonomialExponent ν label β) < ⊤) ↔ _
    simp_rw [directionalOrderedCost_finite_iff]
  exact ⟨fun h => (hbudget c₁ hc₁).1 (hlo.trans_lt h),
    fun h => hhi.trans_lt ((hbudget c₂ hc₂).2 h)⟩

/-- The complete positive Schwinger cost of the centered quadratic
model before partitioning its common times into ordered sectors. -/
def directionalCenteredSchwingerCost
    (A : DirectionalMomentum d →ₗ[ℝ] DirectionalMomentum a)
    (C : ∀ e, DirectionalMomentum d →ₗ[ℝ] DirectionalMomentum (b e))
    (ν : Fin m → ℝ) (P : MvPolynomial (Fin d) ℂ) : ℝ≥0∞ :=
  ∫⁻ t, directionalOrderedDensity ν t *
    (∫⁻ k : DirectionalMomentum d,
      ENNReal.ofReal (‖directionalNumerator P k‖ * Real.exp (-sourcePrecision A C t k)))
    ∂directionalSchwingerMeasure (Fin m)

/-- Sector relabelling permutes only the actual routes and their powers,
with the same momentum integral and without a Jacobian. -/
theorem directionalCenteredSchwingerCost_finite_iff_sectors
    (A : DirectionalMomentum d →ₗ[ℝ] DirectionalMomentum a)
    (C : ∀ e, DirectionalMomentum d →ₗ[ℝ] DirectionalMomentum (b e))
    (ν : Fin m → ℝ) (P : MvPolynomial (Fin d) ℂ) :
    directionalCenteredSchwingerCost A C ν P < ⊤ ↔
      ∀ σ : Equiv.Perm (Fin m),
        directionalCenteredSectorCost A (fun j => C (σ j)) (ν ∘ σ) P < ⊤ := by
  unfold directionalCenteredSchwingerCost
  rw [directionalSchwinger_finite_iff_ordered_sectors]
  apply forall_congr'
  intro σ
  rw [directionalPermutedSector_lintegral_eq]
  have hprec (t : Fin m → ℝ) (k : DirectionalMomentum d) :
      sourcePrecision A C (t ∘ σ.symm) k =
        sourcePrecision A (fun j => C (σ j)) t k := by
    unfold sourcePrecision
    congr 1
    rw [← Equiv.sum_comp σ (fun e => (t ∘ σ.symm) e * ‖C e k‖ ^ 2)]
    simp only [Function.comp_apply, Equiv.symm_apply_apply]
  have hdensity (t : Fin m → ℝ) :
      directionalOrderedDensity ν (t ∘ σ.symm) = directionalOrderedDensity (ν ∘ σ) t := by
    unfold directionalOrderedDensity
    rw [← Equiv.prod_comp σ (fun e => ENNReal.ofReal ((t ∘ σ.symm) e ^ (ν e - 1)))]
    simp only [Function.comp_apply, Equiv.symm_apply_apply]
  simp only [directionalCenteredSectorCost, hdensity, hprec]

end UV
