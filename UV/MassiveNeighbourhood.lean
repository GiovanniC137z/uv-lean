import UV.GlobalAssembly
import UV.Holomorphy
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

noncomputable section
open MeasureTheory Set Real Filter Metric
open scoped ENNReal BigOperators Topology

namespace UV

/-- The unnormalized positive exponential tilt used for local complex graph
estimates. Its normalization is not changed. -/
def massiveTilt (ρ : Measure ℝ) (lam : ℝ) : Measure ℝ :=
  ρ.withDensity (fun τ => ENNReal.ofReal (Real.exp (lam * τ)))

theorem massiveTilt_no_negative (ρ : Measure ℝ) (lam : ℝ) (hneg : ρ (Iio 0) = 0) :
    massiveTilt ρ lam (Iio 0) = 0 :=
  withDensity_absolutelyContinuous ρ _ hneg

theorem massiveTilt_no_atom (ρ : Measure ℝ) (lam : ℝ) (hzero : ρ {0} = 0) :
    massiveTilt ρ lam {0} = 0 :=
  withDensity_absolutelyContinuous ρ _ hzero

theorem massiveTilt_finite (ρ : Measure ℝ) (lam ε : ℝ)
    (hneg : ρ (Iio 0) = 0) (hzero : ρ {0} = 0) (hlamε : lam ≤ ε)
    (hexp : (∫⁻ τ : ℝ, ENNReal.ofReal (Real.exp (ε * τ)) ∂ρ) < ⊤) :
    IsFiniteMeasure (massiveTilt ρ lam) := by
  apply isFiniteMeasure_withDensity
  apply ne_of_lt
  apply lt_of_le_of_lt _ hexp
  apply lintegral_mono_ae
  filter_upwards [ae_positive_of_support_no_atom ρ hneg hzero] with τ hτ
  exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_right hlamε hτ.le))

theorem massiveTilt_integrable_iff (ρ : Measure ℝ) (lam : ℝ) (f : ℝ → ℝ) :
    Integrable f (massiveTilt ρ lam) ↔
      Integrable (fun τ => Real.exp (lam * τ) * f τ) ρ := by
  unfold massiveTilt
  have hm : Measurable (fun τ : ℝ => ENNReal.ofReal (Real.exp (lam * τ))) := by fun_prop
  rw [integrable_withDensity_iff_integrable_smul' hm
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (Real.exp_nonneg _), smul_eq_mul]

theorem massiveTilt_inverseMoment_bound (ρ : Measure ℝ) {lam ε r : ℝ}
    (hlam : 0 ≤ lam) (hlamε : lam ≤ ε) (hr : 0 ≤ r) :
    inverseMoment (massiveTilt ρ lam) r ≤
      ENNReal.ofReal (Real.exp lam) * inverseMoment ρ r +
        ∫⁻ τ : ℝ, ENNReal.ofReal (Real.exp (ε * τ)) ∂ρ := by
  have hm : Measurable (fun τ : ℝ => ENNReal.ofReal (Real.exp (lam * τ))) := by fun_prop
  have hp : Measurable (fun τ : ℝ => ENNReal.ofReal (τ ^ (-r))) := by fun_prop
  unfold inverseMoment massiveTilt
  rw [restrict_withDensity measurableSet_Ioi,
    lintegral_withDensity_eq_lintegral_mul _ hm hp]
  calc
    _ ≤ ∫⁻ τ : ℝ in Ioi 0, ENNReal.ofReal (Real.exp lam) *
        ENNReal.ofReal (τ ^ (-r)) + ENNReal.ofReal (Real.exp (ε * τ)) ∂ρ := by
      apply setLIntegral_mono' measurableSet_Ioi
      intro τ hτ
      dsimp only [Pi.mul_apply]
      rw [← ENNReal.ofReal_mul (Real.exp_nonneg _),
        ← ENNReal.ofReal_mul (Real.exp_nonneg lam),
        ← ENNReal.ofReal_add (mul_nonneg (Real.exp_nonneg lam) (Real.rpow_nonneg hτ.le _))
          (Real.exp_nonneg _)]
      apply ENNReal.ofReal_le_ofReal
      by_cases ht : τ ≤ 1
      · have he : Real.exp (lam * τ) ≤ Real.exp lam :=
          Real.exp_le_exp.mpr (by nlinarith)
        have hh := mul_le_mul_of_nonneg_right he (Real.rpow_nonneg hτ.le (-r))
        have hn := Real.exp_nonneg (ε * τ)
        nlinarith
      · have hp1 : τ ^ (-r) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos
          (le_of_lt (lt_of_not_ge ht)) (neg_nonpos.mpr hr)
        have he : Real.exp (lam * τ) ≤ Real.exp (ε * τ) :=
          Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hlamε hτ.le)
        have hn := mul_nonneg (Real.exp_nonneg lam) (Real.rpow_nonneg hτ.le (-r))
        nlinarith [mul_le_mul_of_nonneg_left hp1 (Real.exp_nonneg (lam * τ))]
    _ = ENNReal.ofReal (Real.exp lam) * (∫⁻ τ : ℝ in Ioi 0, ENNReal.ofReal (τ ^ (-r)) ∂ρ) +
        ∫⁻ τ : ℝ in Ioi 0, ENNReal.ofReal (Real.exp (ε * τ)) ∂ρ := by
      rw [lintegral_add_left (measurable_const.mul hp), lintegral_const_mul _ hp]
    _ ≤ _ := add_le_add_left (setLIntegral_le_lintegral _ _) _

theorem massiveTilt_inverseMoment_finite (ρ : Measure ℝ) {lam ε r : ℝ}
    (hlam : 0 ≤ lam) (hlamε : lam ≤ ε) (hr : 0 ≤ r)
    (hM : inverseMoment ρ r < ⊤)
    (hexp : (∫⁻ τ : ℝ, ENNReal.ofReal (Real.exp (ε * τ)) ∂ρ) < ⊤) :
    inverseMoment (massiveTilt ρ lam) r < ⊤ :=
  lt_of_le_of_lt (massiveTilt_inverseMoment_bound ρ hlam hlamε hr)
    (ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top hM, hexp⟩)

theorem massiveTilt_control (ρ : Measure ℝ) [IsFiniteMeasure ρ] {lam ε D : ℝ}
    (hlam : 0 ≤ lam) (hlamε : lam ≤ ε) (hD : 0 ≤ D)
    (hcontrol : GapOrEndpoint ρ D)
    (hexp : (∫⁻ τ : ℝ, ENNReal.ofReal (Real.exp (ε * τ)) ∂ρ) < ⊤) :
    GapOrEndpoint (massiveTilt ρ lam) D := by
  right
  refine ⟨massiveTilt_no_atom ρ lam hcontrol.no_atom, ?_⟩
  exact massiveTilt_inverseMoment_finite ρ hlam hlamε (by linarith)
    (hcontrol.endpoint hD) hexp

/-- Complex bilinear momentum square; this is not the Hermitian norm square. -/
def massiveBilinearSquare (q : Fin 4 → ℂ) : ℂ := ∑ ν, q ν ^ 2

theorem massive_coordinate_square_lower (x : ℝ) (h : ℂ) :
    (1 / 2 : ℝ) * x ^ 2 - ‖h‖ ^ 2 ≤ (((x : ℂ) + h) ^ 2).re := by
  have hh := Complex.sq_norm h
  simp only [Complex.normSq_apply] at hh
  simp only [pow_two, Complex.mul_re, Complex.add_re, Complex.ofReal_re,
    Complex.add_im, Complex.ofReal_im, zero_add]
  nlinarith [sq_nonneg (x / 2 + h.re)]

/-- The exact real-centre Gaussian comparison, retaining the full imaginary
and real routing displacement in the error term. -/
theorem massive_square_lower (q : LoopMomentum) (h : Fin 4 → ℂ) :
    (1 / 2 : ℝ) * ‖q‖ ^ 2 - ∑ ν, ‖h ν‖ ^ 2 ≤
      (massiveBilinearSquare (fun ν => (q ν : ℂ) + h ν)).re := by
  have hh := Finset.sum_le_sum (s := Finset.univ)
    (fun ν _ => massive_coordinate_square_lower (q ν) (h ν))
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at hh
  unfold massiveBilinearSquare
  change (1 / 2 : ℝ) * ‖q‖ ^ 2 - ∑ ν, ‖h ν‖ ^ 2 ≤
    Complex.reCLM (∑ ν, ((q ν : ℂ) + h ν) ^ 2)
  rw [map_sum]
  rw [EuclideanSpace.norm_sq_eq]
  simpa only [Real.norm_eq_abs, sq_abs] using hh

/-- Source monomials in actual real loop coordinates. -/
def massiveMonomial {L : ℕ} (γ : (Fin L × Fin 4) → ℕ)
    (k : Fin L → LoopMomentum) : ℂ :=
  ∏ v, (k v.1 v.2 : ℂ) ^ γ v

theorem massiveMonomial_norm_bound {L D : ℕ} (γ : (Fin L × Fin 4) → ℕ)
    (hγ : ∑ v, γ v ≤ D) (k : Fin L → LoopMomentum) :
    ‖massiveMonomial γ k‖ ≤ 1 + ‖k‖ ^ D := by
  have hcoord (v : Fin L × Fin 4) : ‖(k v.1 v.2 : ℂ)‖ ≤ ‖k‖ := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact (PiLp.norm_apply_le (k v.1) v.2).trans (norm_le_pi_norm k v.1)
  have hp : ‖massiveMonomial γ k‖ ≤ ‖k‖ ^ (∑ v, γ v) := by
    unfold massiveMonomial
    rw [norm_prod, ← Finset.prod_pow_eq_pow_sum]
    apply Finset.prod_le_prod
    · intro v _; exact norm_nonneg _
    · intro v _
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (hcoord v) _
  by_cases hk : ‖k‖ ≤ 1
  · have hpow := pow_le_one₀ (n := ∑ v, γ v) (norm_nonneg k) hk
    have hn := pow_nonneg (norm_nonneg k) D
    linarith
  · have hpow := pow_le_pow_right₀ (le_of_lt (lt_of_not_ge hk)) hγ
    linarith

def massivePolynomial {Γ : Type*} [Fintype Γ] {H : Type*} {L : ℕ}
    (γ : Γ → (Fin L × Fin 4) → ℕ) (c : Γ → H → ℂ)
    (k : Fin L → LoopMomentum) (z : H) : ℂ :=
  ∑ g, c g z * massiveMonomial (γ g) k

theorem massivePolynomial_norm_bound {Γ H : Type*} [Fintype Γ] {L D : ℕ}
    (γ : Γ → (Fin L × Fin 4) → ℕ) (c : Γ → H → ℂ)
    (hγ : ∀ g, ∑ v, γ g v ≤ D) {W : Set H} {B : ℝ} (hB : 0 ≤ B)
    (hc : ∀ g z, z ∈ W → ‖c g z‖ ≤ B) {z : H} (hz : z ∈ W)
    (k : Fin L → LoopMomentum) :
    ‖massivePolynomial γ c k z‖ ≤ (Fintype.card Γ * B) * (1 + ‖k‖ ^ D) := by
  unfold massivePolynomial
  calc
    _ ≤ ∑ g, ‖c g z * massiveMonomial (γ g) k‖ := norm_sum_le _ _
    _ ≤ ∑ _ : Γ, B * (1 + ‖k‖ ^ D) := by
      apply Finset.sum_le_sum
      intro g _
      rw [norm_mul]
      exact mul_le_mul (hc g z hz) (massiveMonomial_norm_bound (γ g) (hγ g) k)
        (norm_nonneg _) hB
    _ = _ := by simp [mul_assoc]

theorem massiveTilt_laplace (ρ : Measure ℝ) (lam z : ℝ) :
    laplace (massiveTilt ρ lam) z =
      ∫ τ : ℝ, Real.exp (lam * τ) * Real.exp (-τ * z) ∂ρ := by
  unfold laplace massiveTilt
  have hm : Measurable (fun τ : ℝ => ENNReal.ofReal (Real.exp (lam * τ))) := by fun_prop
  rw [integral_withDensity_eq_integral_toReal_smul hm
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (Real.exp_nonneg _), smul_eq_mul]

/-- Positive reduced massive envelope, with the one-half Gaussian widths
retained before either line parameter is integrated. -/
def massiveLineEnvelope (a m e x : ℝ) (t : ℝ × ℝ) : ℝ :=
  (Real.exp (a ^ 2 * e * t.1) *
    Real.exp (-t.1 * ((a / Real.sqrt 2) ^ 2 * x))) *
      Real.exp (-t.2 * ((m ^ 2 - e) + x / 2))

theorem massive_half_covariance (b x : ℝ) :
    (∫ α : ℝ in Ioi 0, Real.exp (-α * (b + x / 2))) =
      2 * schwingerCovariance (fun α => Real.exp (-2 * b * α)) x := by
  calc
    _ = 2 * ∫ α : ℝ in Ioi 0, Real.exp (-(2 * α) * (b + x / 2)) := by
      rw [integral_comp_mul_left_Ioi
        (fun α : ℝ => Real.exp (-α * (b + x / 2))) 0 (by norm_num : (0 : ℝ) < 2)]
      norm_num only [mul_zero, smul_eq_mul]
      ring
    _ = _ := by
      unfold schwingerCovariance
      congr 1
      apply setIntegral_congr_fun measurableSet_Ioi
      intro α _
      dsimp only
      rw [← Real.exp_add]
      congr 1
      ring

theorem massiveLineEnvelope_integrable (ρ : Measure ℝ) [IsFiniteMeasure ρ]
    (a m e : ℝ) [IsFiniteMeasure (massiveTilt ρ (a ^ 2 * e))]
    (hneg : ρ (Iio 0) = 0) (hzero : ρ {0} = 0) (hm : e < m ^ 2)
    {x : ℝ} (hx : 0 ≤ x) :
    Integrable (massiveLineEnvelope a m e x) (ρ.prod (volume.restrict (Ioi 0))) := by
  have ht : Integrable (fun τ : ℝ => Real.exp (-τ * ((a / Real.sqrt 2) ^ 2 * x)))
      (massiveTilt ρ (a ^ 2 * e)) := by
    refine (integrable_const (1 : ℝ)).mono' (by fun_prop) ?_
    filter_upwards [ae_positive_of_support_no_atom _
      (massiveTilt_no_negative ρ _ hneg) (massiveTilt_no_atom ρ _ hzero)] with τ hτ
    rw [Real.norm_of_nonneg (Real.exp_nonneg _)]
    exact Real.exp_le_one_iff.mpr (by
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hτ.le) (by positivity))
  have hto := (massiveTilt_integrable_iff ρ (a ^ 2 * e) _).mp ht
  have ha : IntegrableOn (fun α : ℝ => Real.exp (-α * ((m ^ 2 - e) + x / 2))) (Ioi 0) := by
    have h := integrableOn_exp_mul_Ioi (a := -((m ^ 2 - e) + x / 2)) (by linarith) 0
    simpa only [neg_mul, mul_neg, mul_comm] using h
  exact hto.mul_prod ha

theorem massiveLineEnvelope_norm_integral (ρ : Measure ℝ) [SigmaFinite ρ] (a m e x : ℝ) :
    (∫ t : ℝ × ℝ, ‖massiveLineEnvelope a m e x t‖
      ∂ρ.prod (volume.restrict (Ioi 0))) =
      2 * (laplace (massiveTilt ρ (a ^ 2 * e)) ((a / Real.sqrt 2) ^ 2 * x) *
        schwingerCovariance (fun α => Real.exp (-2 * (m ^ 2 - e) * α)) x) := by
  unfold massiveLineEnvelope
  simp_rw [Real.norm_of_nonneg (mul_nonneg
    (mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _)) (Real.exp_nonneg _))]
  rw [integral_prod_mul
    (fun τ : ℝ => Real.exp (a ^ 2 * e * τ) * Real.exp (-τ * ((a / Real.sqrt 2) ^ 2 * x)))
    (fun α : ℝ => Real.exp (-α * ((m ^ 2 - e) + x / 2))),
    ← massiveTilt_laplace, massive_half_covariance]
  ring

def massiveCentreMajorant {I : Type*} [Fintype I] {L : ℕ}
    (Croute : Matrix I (Fin L) ℝ) (R0 : I → LoopMomentum)
    (m e : I → ℝ) (a C : ℝ) (D : ℕ)
    (w : (Fin L → LoopMomentum) × (I → ℝ × ℝ)) : ℝ :=
  C * (1 + ‖w.1‖ ^ D) * ∏ i,
    massiveLineEnvelope a (m i) (e i)
      (‖rectangularMomentum Croute (fun _ : Unit => R0) i () w.1‖ ^ 2) (w.2 i)

theorem massiveCentreMajorant_nonneg {I : Type*} [Fintype I] {L : ℕ}
    (Croute : Matrix I (Fin L) ℝ) (R0 : I → LoopMomentum)
    (m e : I → ℝ) (a C : ℝ) (D : ℕ) (hC : 0 ≤ C)
    (w : (Fin L → LoopMomentum) × (I → ℝ × ℝ)) :
    0 ≤ massiveCentreMajorant Croute R0 m e a C D w := by
  unfold massiveCentreMajorant massiveLineEnvelope
  positivity

/-- Integrability of the actual fixed-centre pre-Gaussian complex envelope,
under the original (untilted) line-parameter measure. -/
theorem massiveCentreMajorant_integrable {I : Type*} [Fintype I] {L D : ℕ}
    (Croute : Matrix I (Fin L) ℝ) (hrank : Croute.rank = L)
    (R0 : I → LoopMomentum) (m e : I → ℝ) {a C ε : ℝ}
    (ha : 0 < a) (hC : 0 ≤ C) (he : ∀ i, 0 ≤ e i) (hm : ∀ i, e i < m i ^ 2)
    (hε : ∀ i, a ^ 2 * e i ≤ ε)
    (ρ : Measure ℝ) [IsFiniteMeasure ρ] (hneg : ρ (Iio 0) = 0)
    (hcontrol : GapOrEndpoint ρ (D : ℝ))
    (hexp : (∫⁻ τ : ℝ, ENNReal.ofReal (Real.exp (ε * τ)) ∂ρ) < ⊤) :
    Integrable (massiveCentreMajorant Croute R0 m e a C D)
      ((Measure.pi fun _ : Fin L => volume).prod
        (Measure.pi fun _ : I => ρ.prod (volume.restrict (Ioi 0)))) := by
  let rt : I → Measure ℝ := fun i => massiveTilt ρ (a ^ 2 * e i)
  haveI : ∀ i, IsFiniteMeasure (rt i) := fun i =>
    massiveTilt_finite ρ _ ε hneg hcontrol.no_atom (hε i) hexp
  let Er : I → ℝ → ℝ := fun i α => Real.exp (-2 * (m i ^ 2 - e i) * α)
  have hEr : ∀ i, IntegrableOn (Er i) (Ioi 0) := by
    intro i
    exact integrableOn_exp_mul_Ioi (a := -2 * (m i ^ 2 - e i)) (by linarith [hm i]) 0
  have hEr0 : ∀ i α, 0 < α → 0 ≤ Er i α := by intros; exact Real.exp_nonneg _
  have hEr1 : ∀ i, ∀ α ∈ Ioc (0 : ℝ) 1, Er i α ≤ 1 := by
    intro i α hα
    apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith [hm i]) hα.1.le
  let N : Unit → (Fin L → LoopMomentum) → ℝ := fun _ k => C * (1 + ‖k‖ ^ D)
  have hN : ∀ p k, ‖N p k‖ ≤ C * (1 + ‖k‖ ^ (D : ℝ)) := by
    intro p k
    dsimp only [N]
    rw [Real.norm_of_nonneg (by positivity), Real.rpow_natCast]
  obtain ⟨A, hA, hg⟩ := global_uv_rectangular Croute hrank (fun _ : Unit => R0)
    (norm_nonneg R0) hC (Nat.cast_nonneg D) (fun _ => le_rfl)
    rt (fun i => massiveTilt_no_negative ρ _ hneg)
    (fun i => massiveTilt_control ρ (mul_nonneg (sq_nonneg a) (he i)) (hε i)
      (Nat.cast_nonneg D) hcontrol hexp)
    Er (fun _ => a / Real.sqrt 2) (fun _ => 1) (fun _ => 1)
    (fun _ => by dsimp only [Er]; fun_prop) hEr hEr0 (fun _ => zero_lt_one) hEr1
    (fun _ => by positivity) N (fun _ => by dsimp only [N]; fun_prop) hN
  let Fline : I → (Fin L → LoopMomentum) → (ℝ × ℝ) → ℝ := fun i k =>
    massiveLineEnvelope a (m i) (e i)
      (‖rectangularMomentum Croute (fun _ : Unit => R0) i () k‖ ^ 2)
  have hline : ∀ k i, Integrable (Fline i k) (ρ.prod (volume.restrict (Ioi 0))) := by
    intro k i
    exact massiveLineEnvelope_integrable ρ a (m i) (e i) hneg hcontrol.no_atom
      (hm i) (sq_nonneg _)
  have hmeas : AEStronglyMeasurable
      (fun w : (Fin L → LoopMomentum) × (I → ℝ × ℝ) => N () w.1 * ∏ i, Fline i w.1 (w.2 i))
      ((Measure.pi fun _ : Fin L => volume).prod
        (Measure.pi fun _ : I => ρ.prod (volume.restrict (Ioi 0)))) := by
    apply Measurable.aestronglyMeasurable
    dsimp only [N, Fline, massiveLineEnvelope, rectangularMomentum]
    fun_prop
  have hloop : Integrable (fun k : Fin L → LoopMomentum => ‖N () k‖ *
      ∏ i, ∫ t : ℝ × ℝ, ‖Fline i k t‖ ∂ρ.prod (volume.restrict (Ioi 0)))
      (Measure.pi fun _ : Fin L => volume) := by
    apply ((hg ()).1.norm.const_mul ((2 : ℝ) ^ Fintype.card I)).congr
    apply Eventually.of_forall
    intro k
    dsimp only [Fline]
    simp_rw [massiveLineEnvelope_norm_integral]
    have hp : 0 ≤ ∏ i, schwingerLine (rt i) (Er i) (a / Real.sqrt 2)
        (rectangularMomentum Croute (fun _ : Unit => R0) i () k) :=
      Finset.prod_nonneg fun i _ => schwingerLine_nonneg _ (hEr0 i) _ _
    rw [norm_smul, Real.norm_of_nonneg hp]
    simp only [schwingerLine, rt, Er, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ]
    ring
  exact (joint_parameter_integrable_iff (fun _ : I => ρ.prod (volume.restrict (Ioi 0)))
    (Measure.pi fun _ : Fin L => volume) Fline (N ()) hline hmeas).mpr hloop

def massiveComplexMomentum {I H : Type*} {L : ℕ}
    (Croute : Matrix I (Fin L) ℝ) (R : I → H → Fin 4 → ℂ)
    (i : I) (z : H) (k : Fin L → LoopMomentum) (ν : Fin 4) : ℂ :=
  ((∑ j, Croute i j * k j ν : ℝ) : ℂ) + R i z ν

def massiveRealShift {I H : Type*} (R : I → H → Fin 4 → ℂ) (p : H) (i : I) : LoopMomentum :=
  WithLp.toLp 2 (fun ν => (R i p ν).re)

theorem massiveComplexMomentum_eq_shift {I H : Type*} {L : ℕ}
    (Croute : Matrix I (Fin L) ℝ) (R : I → H → Fin 4 → ℂ) (i : I) (p z : H)
    (hreal : ∀ ν, (R i p ν).im = 0) (k : Fin L → LoopMomentum) :
    massiveComplexMomentum Croute R i z k = fun ν =>
      ((rectangularMomentum Croute (fun _ : Unit => massiveRealShift R p) i () k ν : ℝ) : ℂ) +
        (R i z ν - R i p ν) := by
  funext ν
  rw [rectangularMomentum_apply]
  dsimp only [massiveComplexMomentum, massiveRealShift]
  have hp : ((R i p ν).re : ℂ) = R i p ν := by
    apply Complex.ext <;> simp [hreal ν]
  simp only [Complex.ofReal_add, PiLp.toLp_apply]
  rw [hp]
  ring

def massivePreGaussian {I H : Type*} [Fintype I] {L : ℕ}
    (Croute : Matrix I (Fin L) ℝ) (R : I → H → Fin 4 → ℂ)
    (N : (Fin L → LoopMomentum) → H → ℂ) (a : ℝ) (m : I → ℝ)
    (z : H) (w : (Fin L → LoopMomentum) × (I → ℝ × ℝ)) : ℂ :=
  N w.1 z * ∏ i, Complex.exp
    (-(((w.2 i).2 + a ^ 2 * (w.2 i).1 : ℝ) : ℂ) *
      massiveBilinearSquare (massiveComplexMomentum Croute R i z w.1) -
      (((w.2 i).2 * m i ^ 2 : ℝ) : ℂ))

theorem massive_half_scale (a : ℝ) : (a / Real.sqrt 2) ^ 2 = a ^ 2 / 2 := by
  rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

theorem massive_complex_line_bound {a m e τ α x : ℝ} {Q : ℂ}
    (hτ : 0 ≤ τ) (hα : 0 ≤ α) (hQ : (1 / 2 : ℝ) * x - e ≤ Q.re) :
    ‖Complex.exp (-(((α + a ^ 2 * τ : ℝ) : ℂ)) * Q - ((α * m ^ 2 : ℝ) : ℂ))‖ ≤
      massiveLineEnvelope a m e x (τ, α) := by
  rw [Complex.norm_exp]
  simp only [Complex.sub_re, Complex.mul_re, Complex.neg_re, Complex.ofReal_re,
    Complex.neg_im, Complex.ofReal_im, neg_zero, zero_mul, sub_zero]
  unfold massiveLineEnvelope
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  rw [massive_half_scale]
  have hw : 0 ≤ α + a ^ 2 * τ := by positivity
  have hh := mul_le_mul_of_nonneg_left hQ hw
  nlinarith

/-- Every nearby complex graph coefficient is bounded pointwise by a fixed
real-centre envelope. No integrability is a hypothesis of this estimate. -/
theorem massivePreGaussian_centre_bound {I H : Type*} [Fintype I] {L D : ℕ}
    (Croute : Matrix I (Fin L) ℝ) (R : I → H → Fin 4 → ℂ)
    (N : (Fin L → LoopMomentum) → H → ℂ) (a C : ℝ) (m e : I → ℝ)
    (p z : H) (hC : 0 ≤ C) (hreal : ∀ i ν, (R i p ν).im = 0)
    (hshift : ∀ i, ∑ ν, ‖R i z ν - R i p ν‖ ^ 2 ≤ e i)
    (hN : ∀ k, ‖N k z‖ ≤ C * (1 + ‖k‖ ^ D))
    (w : (Fin L → LoopMomentum) × (I → ℝ × ℝ))
    (ht : ∀ i, 0 ≤ (w.2 i).1 ∧ 0 ≤ (w.2 i).2) :
    ‖massivePreGaussian Croute R N a m z w‖ ≤
      massiveCentreMajorant Croute (massiveRealShift R p) m e a C D w := by
  unfold massivePreGaussian massiveCentreMajorant
  rw [norm_mul, norm_prod]
  apply mul_le_mul (hN w.1) _ (by positivity) (by positivity)
  apply Finset.prod_le_prod
  · intro i _; exact norm_nonneg _
  · intro i _
    apply massive_complex_line_bound (ht i).1 (ht i).2
    rw [massiveComplexMomentum_eq_shift Croute R i p z (hreal i)]
    have hh := massive_square_lower
      (rectangularMomentum Croute (fun _ : Unit => massiveRealShift R p) i () w.1)
      (fun ν => R i z ν - R i p ν)
    linarith [hshift i]

/-- Compact real-centre data admit finitely many genuine complex balls with
uniformly small routing displacements and closures inside the original domain. -/
theorem massive_compact_routing_cover
    {I H : Type*} [Fintype I] [NormedAddCommGroup H]
    {K Ω0 : Set H} (hK : IsCompact K) (hΩ0 : IsOpen Ω0) (hKΩ0 : K ⊆ Ω0)
    (R : I → H → Fin 4 → ℂ) (hR : ∀ i, Continuous (R i))
    (e : I → ℝ) (he : ∀ i, 0 < e i) :
    ∃ (r : K → ℝ) (s : Finset K),
      (∀ p : K, 0 < r p) ∧ K ⊆ ⋃ p ∈ s, ball (p : H) (r p) ∧
      (∀ p : K, closedBall (p : H) (r p) ⊆ Ω0) ∧
      (∀ (p : K) (z : H), z ∈ closedBall (p : H) (r p) →
        ∀ i, ∑ ν, ‖R i z ν - R i p ν‖ ^ 2 ≤ e i) := by
  classical
  have hlocal : ∀ p : K, ∃ r > 0, closedBall (p : H) r ⊆ Ω0 ∧
      ∀ z ∈ closedBall (p : H) r, ∀ i, ∑ ν, ‖R i z ν - R i p ν‖ ^ 2 ≤ e i := by
    intro p
    let V : Set H := Ω0 ∩ ⋂ i, {z | (∑ ν, ‖R i z ν - R i p ν‖ ^ 2) < e i}
    have herror (i : I) : Continuous (fun z : H => ∑ ν, ‖R i z ν - R i p ν‖ ^ 2) := by
      fun_prop
    have hV : IsOpen V := hΩ0.inter
      (isOpen_iInter_of_finite fun i => isOpen_lt (herror i) continuous_const)
    have hpV : (p : H) ∈ V := by
      refine ⟨hKΩ0 p.property, ?_⟩
      simp only [mem_iInter, mem_setOf_eq, sub_self, norm_zero, ne_eq,
        OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero]
      exact he
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hV p hpV
    have hclosed : closedBall (p : H) (r / 2) ⊆ V :=
      (closedBall_subset_ball (by linarith)).trans hball
    refine ⟨r / 2, by linarith, fun z hz => (hclosed hz).1, ?_⟩
    intro z hz i
    exact (mem_iInter.mp (hclosed hz).2 i).le
  choose r hr hsub hshift using hlocal
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover (fun p : K => ball (p : H) (r p))
    (fun _ => isOpen_ball) (by
      intro p hp
      exact mem_iUnion.mpr ⟨⟨p, hp⟩, mem_ball_self (hr ⟨p, hp⟩)⟩)
  exact ⟨r, s, hr, hs, hsub, hshift⟩

/-- The finite union of the covering closed balls is a compact coefficient
control set; its subset relation also controls the closure of the open union. -/
theorem massive_cover_compact {H : Type*} [NormedAddCommGroup H] [ProperSpace H]
    {K Ω0 : Set H} (r : K → ℝ) (s : Finset K)
    (hsub : ∀ p : K, closedBall (p : H) (r p) ⊆ Ω0) :
    IsCompact (⋃ p ∈ s, closedBall (p : H) (r p)) ∧
      closure (⋃ p ∈ s, ball (p : H) (r p)) ⊆ Ω0 := by
  have hc : IsCompact (⋃ p ∈ s, closedBall (p : H) (r p)) :=
    s.isCompact_biUnion fun p _ => isCompact_closedBall _ _
  refine ⟨hc, ?_⟩
  apply (closure_minimal ?_ hc.isClosed).trans ?_
  · intro z hz
    rcases mem_iUnion₂.mp hz with ⟨p, hp, hz⟩
    exact mem_iUnion₂.mpr ⟨p, hp, ball_subset_closedBall hz⟩
  · intro z hz
    rcases mem_iUnion₂.mp hz with ⟨p, _, hz⟩
    exact hsub p hz

/-- A finite holomorphic coefficient family has one compact-domain coefficient
bound; analyticity will be supplied by the source hypothesis later. -/
theorem massive_compact_coefficient_bound {Γ H : Type*} [Fintype Γ]
    [TopologicalSpace H] {W : Set H} (hW : IsCompact W)
    (c : Γ → H → ℂ) (hc : ∀ g, ContinuousOn (c g) W) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ g z, z ∈ W → ‖c g z‖ ≤ B := by
  classical
  have hvec : ContinuousOn (fun z : H => fun g : Γ => c g z) W :=
    continuousOn_pi.mpr hc
  obtain ⟨B, hB⟩ := hW.exists_bound_of_continuousOn hvec
  refine ⟨max 0 B, le_max_left _ _, ?_⟩
  intro g z hz
  exact (norm_le_pi_norm (fun g : Γ => c g z) g).trans ((hB z hz).trans (le_max_right _ _))

theorem massivePreGaussian_polynomial_measurable
    {I Γ H : Type*} [Fintype I] [Fintype Γ] {L : ℕ}
    (Croute : Matrix I (Fin L) ℝ) (R : I → H → Fin 4 → ℂ)
    (γ : Γ → (Fin L × Fin 4) → ℕ) (c : Γ → H → ℂ)
    (a : ℝ) (m : I → ℝ) (z : H) :
    Measurable (massivePreGaussian Croute R (massivePolynomial γ c) a m z) := by
  unfold massivePreGaussian massivePolynomial massiveMonomial massiveBilinearSquare massiveComplexMomentum
  fun_prop

theorem massive_differentiableWithinAt_prod {I H : Type*} [Fintype I]
    [NormedAddCommGroup H] [NormedSpace ℂ H] {f : I → H → ℂ} {s : Set H} {z : H}
    (hf : ∀ i, DifferentiableWithinAt ℂ (f i) s z) :
    DifferentiableWithinAt ℂ (fun z => ∏ i, f i z) s z := by
  classical
  exact (HasFDerivWithinAt.finset_prod
    (g' := fun i => fderivWithin ℂ (f i) s z)
    (fun i _ => (hf i).hasFDerivWithinAt)).differentiableWithinAt

theorem massivePreGaussian_polynomial_differentiableOn
    {I Γ H : Type*} [Fintype I] [Fintype Γ] {L : ℕ}
    [NormedAddCommGroup H] [NormedSpace ℂ H]
    (Croute : Matrix I (Fin L) ℝ) (R : I → H → Fin 4 → ℂ)
    (hR : ∀ i, Differentiable ℂ (R i))
    (γ : Γ → (Fin L × Fin 4) → ℕ) (c : Γ → H → ℂ)
    {Ω0 : Set H} (hc : ∀ g, DifferentiableOn ℂ (c g) Ω0)
    (a : ℝ) (m : I → ℝ)
    (w : (Fin L → LoopMomentum) × (I → ℝ × ℝ)) :
    DifferentiableOn ℂ (fun z => massivePreGaussian Croute R (massivePolynomial γ c) a m z w) Ω0 := by
  unfold massivePreGaussian massivePolynomial massiveMonomial massiveBilinearSquare massiveComplexMomentum
  intro z hz
  have hcp (g : Γ) : DifferentiableWithinAt ℂ (c g) Ω0 z := hc g z hz
  have hrp (i : I) (ν : Fin 4) : DifferentiableAt ℂ (fun w => R i w ν) z :=
    (ContinuousLinearMap.proj ν : (Fin 4 → ℂ) →L[ℂ] ℂ).differentiableAt.comp z (hR i z)
  apply DifferentiableWithinAt.mul
  · exact DifferentiableWithinAt.fun_sum fun g _ => (hcp g).mul_const _
  · apply massive_differentiableWithinAt_prod
    intro i
    apply DifferentiableWithinAt.cexp
    apply DifferentiableWithinAt.sub_const
    apply DifferentiableWithinAt.const_mul
    apply DifferentiableWithinAt.fun_sum
    intro ν _
    exact (DifferentiableWithinAt.const_add _ (hrp i ν).differentiableWithinAt).pow 2

theorem massive_parameters_nonneg {I X : Type*} [Fintype I] [MeasurableSpace X]
    (μ : Measure X) [SigmaFinite μ] (ρ : Measure ℝ) [IsFiniteMeasure ρ]
    (hneg : ρ (Iio 0) = 0) (hzero : ρ {0} = 0) :
    ∀ᵐ w : X × (I → ℝ × ℝ) ∂μ.prod
      (Measure.pi fun _ : I => ρ.prod (volume.restrict (Ioi 0))),
      ∀ i, 0 ≤ (w.2 i).1 ∧ 0 ≤ (w.2 i).2 := by
  have ht : ∀ᵐ t : ℝ × ℝ ∂ρ.prod (volume.restrict (Ioi 0)),
      0 ≤ t.1 ∧ 0 ≤ t.2 := by
    have hτ := (Measure.quasiMeasurePreserving_fst
      (μ := ρ) (ν := volume.restrict (Ioi (0 : ℝ)))).ae
      (ae_positive_of_support_no_atom ρ hneg hzero)
    have hα := (Measure.quasiMeasurePreserving_snd
      (μ := ρ) (ν := volume.restrict (Ioi (0 : ℝ)))).ae
      (ae_restrict_mem measurableSet_Ioi)
    filter_upwards [hτ, hα] with t hτ hα
    exact ⟨hτ.le, hα.le⟩
  have hp : ∀ᵐ t : I → ℝ × ℝ ∂Measure.pi
      (fun _ : I => ρ.prod (volume.restrict (Ioi 0))),
      ∀ i, 0 ≤ (t i).1 ∧ 0 ≤ (t i).2 :=
    eventually_all.mpr fun i => (Measure.tendsto_eval_ae_ae
      (μ := fun _ : I => ρ.prod (volume.restrict (Ioi 0))) (i := i)).eventually ht
  exact (Measure.quasiMeasurePreserving_snd (μ := μ)).ae hp

def massiveGraphMeasure {I : Type*} [Fintype I] {L : ℕ} (ρ : Measure ℝ) :
    Measure ((Fin L → LoopMomentum) × (I → ℝ × ℝ)) :=
  (Measure.pi fun _ : Fin L => volume).prod
    (Measure.pi fun _ : I => ρ.prod (volume.restrict (Ioi 0)))

/-- A sufficient massive complex neighbourhood, with the actual common
pre-Gaussian graph majorant derived from the source data. The numerator's
finite polynomial expansion and fixed degree are explicit. -/
theorem massive_neighbourhood
    {I Γ H : Type*} [Fintype I] [Fintype Γ] {L D : ℕ}
    [NormedAddCommGroup H] [NormedSpace ℂ H] [FiniteDimensional ℂ H] [ProperSpace H]
    (Croute : Matrix I (Fin L) ℝ) (hrank : Croute.rank = L)
    (R : I → H → Fin 4 → ℂ) (hR : ∀ i, Differentiable ℂ (R i))
    {K Ω0 : Set H} (hK : IsCompact K) (hΩ0 : IsOpen Ω0) (hKΩ0 : K ⊆ Ω0)
    (hreal : ∀ p ∈ K, ∀ i ν, (R i p ν).im = 0)
    (γ : Γ → (Fin L × Fin 4) → ℕ) (c : Γ → H → ℂ)
    (hγ : ∀ g, ∑ v, γ g v ≤ D) (hc : ∀ g, AnalyticOnNhd ℂ (c g) Ω0)
    (m : I → ℝ) (hm : ∀ i, 0 < m i) {a ε : ℝ} (ha : 0 < a) (hε : 0 < ε)
    (ρ : Measure ℝ) [IsFiniteMeasure ρ] (hneg : ρ (Iio 0) = 0)
    (hcontrol : GapOrEndpoint ρ (D : ℝ))
    (hexp : (∫⁻ τ : ℝ, ENNReal.ofReal (Real.exp (ε * τ)) ∂ρ) < ⊤) :
    ∃ Ω : Set H, IsOpen Ω ∧ K ⊆ Ω ∧ IsCompact (closure Ω) ∧ closure Ω ⊆ Ω0 ∧
      ∃ M : ((Fin L → LoopMomentum) × (I → ℝ × ℝ)) → ℝ,
        Integrable M (massiveGraphMeasure ρ) ∧
        (∀ᵐ w ∂massiveGraphMeasure ρ, ∀ z ∈ Ω,
          ‖massivePreGaussian Croute R (massivePolynomial γ c) a m z w‖ ≤ M w) ∧
        DifferentiableOn ℂ (fun z => ∫ w,
          massivePreGaussian Croute R (massivePolynomial γ c) a m z w
          ∂massiveGraphMeasure ρ) Ω := by
  classical
  let e : I → ℝ := fun i => min (m i ^ 2 / 4) (ε / (2 * a ^ 2))
  have he : ∀ i, 0 < e i := by
    intro i
    have hmi := hm i
    exact lt_min (by positivity) (by positivity)
  have hmass : ∀ i, e i < m i ^ 2 := by
    intro i
    exact (min_le_left _ _).trans_lt (by nlinarith [sq_pos_of_pos (hm i)])
  have htilt : ∀ i, a ^ 2 * e i ≤ ε := by
    intro i
    have h := (le_div_iff₀ (by positivity : 0 < 2 * a ^ 2)).mp
      (min_le_right (m i ^ 2 / 4) (ε / (2 * a ^ 2)))
    change e i * (2 * a ^ 2) ≤ ε at h
    nlinarith
  obtain ⟨r, s, hr, hcover, hsub, hshift⟩ := massive_compact_routing_cover
    hK hΩ0 hKΩ0 R (fun i => (hR i).continuous) e he
  let Ω : Set H := ⋃ p ∈ s, ball (p : H) (r p)
  let W : Set H := ⋃ p ∈ s, closedBall (p : H) (r p)
  have hΩ : IsOpen Ω := isOpen_iUnion fun _ => isOpen_iUnion fun _ => isOpen_ball
  have hΩW : Ω ⊆ W := by
    intro z hz
    rcases mem_iUnion₂.mp hz with ⟨p, hp, hz⟩
    exact mem_iUnion₂.mpr ⟨p, hp, ball_subset_closedBall hz⟩
  have hW : IsCompact W := (massive_cover_compact r s hsub).1
  have hcl : closure Ω ⊆ Ω0 := (massive_cover_compact r s hsub).2
  have hWsub : W ⊆ Ω0 := by
    intro z hz
    rcases mem_iUnion₂.mp hz with ⟨p, _, hz⟩
    exact hsub p hz
  have hΩsub : Ω ⊆ Ω0 := subset_closure.trans hcl
  have hcompact : IsCompact (closure Ω) :=
    hW.of_isClosed_subset isClosed_closure (closure_minimal hΩW hW.isClosed)
  obtain ⟨B, hB, hcoeff⟩ := massive_compact_coefficient_bound hW c
    (fun g => (hc g).continuousOn.mono hWsub)
  let C : ℝ := (Fintype.card Γ : ℝ) * B
  have hC : 0 ≤ C := mul_nonneg (Nat.cast_nonneg _) hB
  let M : ((Fin L → LoopMomentum) × (I → ℝ × ℝ)) → ℝ := fun w =>
    ∑ p ∈ s, massiveCentreMajorant Croute (massiveRealShift R p) m e a C D w
  have hM : Integrable M (massiveGraphMeasure ρ) := by
    apply integrable_finset_sum s
    intro p _
    exact massiveCentreMajorant_integrable Croute hrank (massiveRealShift R p) m e ha hC
      (fun i => (he i).le) hmass htilt ρ hneg hcontrol hexp
  have hb : ∀ᵐ w ∂massiveGraphMeasure ρ, ∀ z ∈ Ω,
      ‖massivePreGaussian Croute R (massivePolynomial γ c) a m z w‖ ≤ M w := by
    filter_upwards [massive_parameters_nonneg (I := I)
      (Measure.pi fun _ : Fin L => volume) ρ hneg hcontrol.no_atom] with w hw
    intro z hz
    rcases mem_iUnion₂.mp hz with ⟨p, hp, hz⟩
    have hzW : z ∈ W := mem_iUnion₂.mpr ⟨p, hp, ball_subset_closedBall hz⟩
    have hbound := massivePreGaussian_centre_bound Croute R (massivePolynomial γ c)
      a C m e p z hC (hreal p p.property)
      (hshift p z (ball_subset_closedBall hz))
      (fun k => massivePolynomial_norm_bound γ c hγ hB hcoeff hzW k) w hw
    apply hbound.trans
    change massiveCentreMajorant Croute (massiveRealShift R p) m e a C D w ≤
      ∑ q ∈ s, massiveCentreMajorant Croute (massiveRealShift R q) m e a C D w
    exact Finset.single_le_sum
      (fun (q : K) _ => massiveCentreMajorant_nonneg Croute (massiveRealShift R q) m e a C D hC w) hp
  refine ⟨Ω, hΩ, hcover, hcompact, hcl, M, hM, hb, ?_⟩
  apply holomorphy_from_local_graph_majorants hΩ
  · intro z _
    exact (massivePreGaussian_polynomial_measurable Croute R γ c a m z).aestronglyMeasurable
  · apply Eventually.of_forall
    intro w
    exact (massivePreGaussian_polynomial_differentiableOn Croute R hR γ c
      (fun g => (hc g).differentiableOn) a m w).mono hΩsub
  · intro z hz
    obtain ⟨r0, hr0, hball⟩ := Metric.isOpen_iff.mp hΩ z hz
    refine ⟨r0, hr0, hball, M, hM, ?_⟩
    filter_upwards [hb] with w hw
    exact fun q hq => hw q (hball hq)

/-- The source's affine external routing is an actual entire complex map;
its analyticity is derived from the continuous linear routing coefficients. -/
theorem massive_neighbourhood_affine
    {I Γ H : Type*} [Fintype I] [Fintype Γ] {L D : ℕ}
    [NormedAddCommGroup H] [NormedSpace ℂ H] [FiniteDimensional ℂ H] [ProperSpace H]
    (Croute : Matrix I (Fin L) ℝ) (hrank : Croute.rank = L)
    (A : I → H →L[ℂ] (Fin 4 → ℂ)) (b : I → Fin 4 → ℂ)
    {K Ω0 : Set H} (hK : IsCompact K) (hΩ0 : IsOpen Ω0) (hKΩ0 : K ⊆ Ω0)
    (hreal : ∀ p ∈ K, ∀ i ν, (A i p ν + b i ν).im = 0)
    (γ : Γ → (Fin L × Fin 4) → ℕ) (c : Γ → H → ℂ)
    (hγ : ∀ g, ∑ v, γ g v ≤ D) (hc : ∀ g, AnalyticOnNhd ℂ (c g) Ω0)
    (m : I → ℝ) (hm : ∀ i, 0 < m i) {a ε : ℝ} (ha : 0 < a) (hε : 0 < ε)
    (ρ : Measure ℝ) [IsFiniteMeasure ρ] (hneg : ρ (Iio 0) = 0)
    (hcontrol : GapOrEndpoint ρ (D : ℝ))
    (hexp : (∫⁻ τ : ℝ, ENNReal.ofReal (Real.exp (ε * τ)) ∂ρ) < ⊤) :
    ∃ Ω : Set H, IsOpen Ω ∧ K ⊆ Ω ∧ IsCompact (closure Ω) ∧ closure Ω ⊆ Ω0 ∧
      ∃ M : ((Fin L → LoopMomentum) × (I → ℝ × ℝ)) → ℝ,
        Integrable M (massiveGraphMeasure ρ) ∧
        (∀ᵐ w ∂massiveGraphMeasure ρ, ∀ z ∈ Ω,
          ‖massivePreGaussian Croute (fun i z => A i z + b i)
            (massivePolynomial γ c) a m z w‖ ≤ M w) ∧
        DifferentiableOn ℂ (fun z => ∫ w,
          massivePreGaussian Croute (fun i z => A i z + b i)
            (massivePolynomial γ c) a m z w ∂massiveGraphMeasure ρ) Ω := by
  exact massive_neighbourhood Croute hrank (fun i z => A i z + b i)
    (fun i => (A i).differentiable.add_const (b i)) hK hΩ0 hKΩ0 hreal
    γ c hγ hc m hm ha hε ρ hneg hcontrol hexp

end UV
