import UV.ContinuePoleOrderStable

/-! Products of arbitrarily many literal scalar lines with the same
positive-mass shell, evolution and height. Every factor carries the
normalized running axial unit before its character is taken. -/

noncomputable section

namespace UV.SectorPlane

open Filter MeasureTheory UV.Carrier
open scoped Topology BigOperators

set_option maxHeartbeats 1200000

variable {E : Type*} [NormedAddCommGroup E]

private theorem directed_order_product {ι : Type*} (s : Finset ι) (u : ι → ℂ) :
    directed (∏ i ∈ s, u i) = ∏ i ∈ s, directed (u i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty] using directed_one
  | insert i s hs ih => simp only [Finset.prod_insert hs, directed_mul, ih]

def Plane.stablePoleOrderLinePairing (diamond : Plane E) (ε : Evolution) (h : Height)
    (m : ℝ) (n : ℕ) (a : Fin (n+1) → ℝ) (f : MassiveMomentum → ℂ) : QuotientCarrier :=
  ∫ q : MassiveMomentum, directed (f q) *
    (if hq : q.1 ≠ 0 then ∏ i, diamond.scalarLine ε h
      (fun z => Complex.exp (-principalSqrt z)) (a i) m q.1 q.2 hq else 0)

theorem Plane.stable_pole_order_lines_readout (diamond : Plane E) (ε : Evolution) (h : Height)
    (m : ℝ) (n : ℕ) (a : Fin (n+1) → ℝ) (ha : ∀ i, 0 ≤ a i)
    (q : MassiveMomentum) (hq : q.1 ≠ 0) :
    (∏ i, diamond.scalarLine ε h (fun z => Complex.exp (-principalSqrt z)) (a i) m q.1 q.2 hq) =
      directed ((Complex.I * (diamond.eta ε : ℂ))^(n+1) *
        (diamond.stablePoleOrderWeight ε (∑ i, a i) (n+1) h q *
          (diamond.poleCoefficient ε h (massiveD m q))^(n+1))) := by
  have hline (i : Fin (n+1)) := (diamond.massive_stable_running_integrand_scalarLine ε h (ha i) m q hq).symm
  simp_rw [hline, ← directed_order_product]
  let w := shellSquare q.1 q.2
  let Z := principalSqrt (-(diamond.shiftedShellCoefficient ε h w))
  let P := diamond.poleCoefficient ε h (massiveD m q)
  let A := Complex.I * (diamond.eta ε : ℂ) * (axialSign q.1 : ℂ)
  have hφ (b : ℝ) : diamond.stableHalfCoefficient ε b w h = Complex.exp (-(b : ℂ) * Z) := by
    rw [Plane.stableHalfCoefficient, dif_pos h.property, diamond.stable_half_numerator_characters]
  change directed (∏ i, diamond.massiveStableRunningIntegrand ε (a i) m q h) = _
  congr 1
  have hper (i : Fin (n+1)) : diamond.massiveStableRunningIntegrand ε (a i) m q h =
      A * (Complex.exp (-(a i : ℂ) * Z) * P) := by
    rw [Plane.massiveStableRunningIntegrand, Plane.massiveStableFactor, dif_pos h.property]
    simp only [A, Complex.ofReal_mul, mul_assoc, ← hφ, P, massiveD, w]
  have hs : (∏ i, Complex.exp (-(a i : ℂ) * Z)) = diamond.stableHalfCoefficient ε (∑ i, a i) w h := by
    rw [← Complex.exp_sum, hφ]
    congr 1
    rw [← Finset.sum_mul, Finset.sum_neg_distrib, Complex.ofReal_sum]
  simp_rw [hper, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, hs,
    Plane.stablePoleOrderWeight]
  change A^(n+1) * (diamond.stableHalfCoefficient ε (∑ i, a i) w h * P^(n+1)) = _
  rw [show A^(n+1) =
      (Complex.I * (diamond.eta ε : ℂ))^(n+1) * (axialSign q.1 : ℂ)^(n+1) by simp only [A, mul_pow]]
  ring

/-- The full product with arbitrary finite many prescribed stable-half
depths has a common-height directed boundary on compact C^(n+2) tests.
Its total depth is the sum of the original depths, and its axial weight
is exactly the original running sign raised to the number of lines. -/
theorem Plane.massive_same_side_stable_lines_boundary (diamond : Plane E) (ε : Evolution)
    {m : ℝ} (hm : 0 < m) (n : ℕ) (a : Fin (n+1) → ℝ) (ha : ∀ i, 0 ≤ a i)
    {f : MassiveMomentum → ℂ} (hf : ContDiff ℝ ((n : WithTop ℕ∞)+2) f) (hs : HasCompactSupport f) :
    let A := ∑ i, a i
    Tendsto (fun h : Height => diamond.stablePoleOrderLinePairing ε h m n a f)
      poleBoundaryHeights (𝓝 (directed ((Complex.I * (diamond.eta ε : ℂ))^(n+1) *
        diamond.stablePoleOrderLimit ε hm A n (n+1) f))) := by
  intro A
  let c := (Complex.I * (diamond.eta ε : ℂ))^(n+1)
  let W := diamond.stablePoleOrderWeight ε A (n+1)
  let P (h : Height) (q : MassiveMomentum) := diamond.poleCoefficient ε h (massiveD m q)
  have hA : 0 ≤ A := Finset.sum_nonneg (fun i _ => ha i)
  have H := directed_shell_readout_continuous.continuousAt.tendsto.comp
    ((diamond.massive_stable_pole_order_boundary ε hm hA n (n+1) (f := f) hf hs).const_mul c)
  refine H.congr fun h => ?_
  have hfP : Integrable (fun q : MassiveMomentum =>
      f q * (diamond.stableHalfCoefficient ε A (shellSquare q.1 q.2) h * P h q^(n+1))) :=
    (hf.continuous.mul (((diamond.stable_half_coefficient_continuous ε A h).comp shellSquare_continuous).mul
      (((diamond.pole_coefficient_continuous ε h).comp (massiveD_continuous m)).pow _))).integrable_of_hasCompactSupport
      (μ := volume) hs.mul_right
  have hsg : Measurable (fun q : MassiveMomentum => (axialSign q.1 : ℂ)^(n+1)) :=
    (Complex.continuous_ofReal.measurable.comp (massive_axial_sign_measurable.comp measurable_fst)).pow_const _
  have hsgb : ∀ q : MassiveMomentum, ‖(axialSign q.1 : ℂ)^(n+1)‖ ≤ 1 := by
    intro q
    rw [norm_pow, Complex.norm_real]
    exact pow_le_one₀ (norm_nonneg _) (massive_running_axial_sign_norm_le_one q.1)
  have hi : Integrable (fun q : MassiveMomentum => c * (f q * (W h q * P h q^(n+1)))) := by
    apply ((hfP.bdd_mul hsg.aestronglyMeasurable ⟨1,hsgb⟩).const_mul c).congr
    refine Eventually.of_forall fun q => ?_
    dsimp only [W, Plane.stablePoleOrderWeight]
    ring
  change directed (c * ∫ q, f q * (W h q * P h q^(n+1))) = _
  rw [← integral_const_mul, ← directed_integral hi]
  apply integral_congr_ae
  filter_upwards [real_axial_nonzero_ae] with q hq
  rw [dif_pos hq, diamond.stable_pole_order_lines_readout ε h m n a ha q hq, ← directed_mul]
  congr 1
  ring

end UV.SectorPlane
