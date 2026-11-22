import UV.ResumeConvergenceNetwork
import UV.ResidualCoercivity
import UV.HeatFourier
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Real.StarOrdered

/-! The grounded shared-vertex Gaussian of the marked normal network.
One vertex is rooted at zero; every remaining visit carries one common
four-vector, including when several edges meet at that visit. The oriented
incidence matrix is constructed from the actual edge endpoints. -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology BigOperators Matrix InnerProductSpace

namespace UV

def networkRootLift {n : ℕ} (x : Fin n → ℝ) : Option (Fin n) → ℝ
  | none => 0
  | some v => x v

def groundedNetworkIncidence {E : Type*} {n : ℕ}
    (src dst : E → Option (Fin n)) : Matrix E (Fin n) ℝ := by
  classical
  exact fun e v => (if dst e = some v then 1 else 0) - (if src e = some v then 1 else 0)

theorem groundedNetworkIncidence_mulVec {E : Type*} {n : ℕ}
    (src dst : E → Option (Fin n)) (x : Fin n → ℝ) (e : E) :
    (groundedNetworkIncidence src dst *ᵥ x) e =
      networkRootLift x (dst e) - networkRootLift x (src e) := by
  classical
  have hsum (v : Option (Fin n)) : (∑ j : Fin n, if v = some j then x j else 0) = networkRootLift x v := by
    cases v <;> simp [networkRootLift]
  simp only [Matrix.mulVec, dotProduct, groundedNetworkIncidence, sub_mul, ite_mul,
    one_mul, zero_mul, Finset.sum_sub_distrib, hsum]

/-- Every graph edge is represented with one of its two possible orientations.
Repeated edges and further endpoints may be retained in the physical list. -/
def NetworkOrientationCovers {E : Type*} {n : ℕ}
    (G : SimpleGraph (Option (Fin n))) (src dst : E → Option (Fin n)) : Prop :=
  ∀ u v, G.Adj u v → ∃ e, (src e = u ∧ dst e = v) ∨ (src e = v ∧ dst e = u)

theorem groundedNetworkIncidence_kernel {E : Type*} {n : ℕ}
    (G : SimpleGraph (Option (Fin n))) (src dst : E → Option (Fin n))
    (hG : G.Connected) (hcover : NetworkOrientationCovers G src dst)
    (x : Fin n → ℝ) (hx : groundedNetworkIncidence src dst *ᵥ x = 0) : x = 0 := by
  have he (e : E) : networkRootLift x (dst e) = networkRootLift x (src e) := by
    have h := congrFun hx e
    rw [groundedNetworkIncidence_mulVec] at h
    exact sub_eq_zero.mp h
  have hadj {u v : Option (Fin n)} (h : G.Adj u v) : networkRootLift x u = networkRootLift x v := by
    obtain ⟨e, h | h⟩ := hcover u v h
    · simpa only [h.1, h.2] using (he e).symm
    · simpa only [h.1, h.2] using he e
  have hwalk {u v : Option (Fin n)} (w : G.Walk u v) : networkRootLift x u = networkRootLift x v := by
    induction w with
    | nil => rfl
    | cons h w ih => exact (hadj h).trans ih
  have hall (v : Fin n) : networkRootLift x (some v) = 0 := by
    obtain ⟨w⟩ := hG none (some v)
    simpa only [networkRootLift] using (hwalk w).symm
  funext v
  exact hall v

theorem groundedNetworkIncidence_injective {E : Type*} {n : ℕ}
    (G : SimpleGraph (Option (Fin n))) (src dst : E → Option (Fin n))
    (hG : G.Connected) (hcover : NetworkOrientationCovers G src dst) :
    Function.Injective (groundedNetworkIncidence src dst).mulVec := by
  intro x y hxy
  have hzero : groundedNetworkIncidence src dst *ᵥ (x - y) = 0 := by
    rw [Matrix.mulVec_sub, hxy, sub_self]
  have h := groundedNetworkIncidence_kernel G src dst hG hcover (x - y) hzero
  exact sub_eq_zero.mp h

def networkPrecision {E : Type*} [Fintype E] {n : ℕ}
    (src dst : E → Option (Fin n)) (s : E → ℝ) : Matrix (Fin n) (Fin n) ℝ := by
  classical
  exact (groundedNetworkIncidence src dst).transpose * Matrix.diagonal (fun e => (s e)⁻¹) *
    groundedNetworkIncidence src dst

theorem networkPrecision_posDef {E : Type*} [Fintype E] {n : ℕ}
    (G : SimpleGraph (Option (Fin n))) (src dst : E → Option (Fin n)) (s : E → ℝ)
    (hG : G.Connected) (hcover : NetworkOrientationCovers G src dst) (hs : ∀ e, 0 < s e) :
    (networkPrecision src dst s).PosDef := by
  classical
  have hdiag := Matrix.PosDef.diagonal (fun e => inv_pos.mpr (hs e))
  simpa only [networkPrecision, Matrix.conjTranspose_eq_transpose_of_trivial] using
    hdiag.conjTranspose_mul_mul_same (groundedNetworkIncidence_injective G src dst hG hcover)

theorem networkPrecision_det_pos {E : Type*} [Fintype E] {n : ℕ}
    (G : SimpleGraph (Option (Fin n))) (src dst : E → Option (Fin n)) (s : E → ℝ)
    (hG : G.Connected) (hcover : NetworkOrientationCovers G src dst) (hs : ∀ e, 0 < s e) :
    0 < (networkPrecision src dst s).det :=
  (networkPrecision_posDef G src dst s hG hcover hs).det_pos

abbrev NetworkVisitSpace (n : ℕ) := EuclideanSpace ℝ (Fin n × Fin 4)

def networkVisit {n : ℕ} (x : NetworkVisitSpace n) : Option (Fin n) → ScalarMomentum
  | none => 0
  | some v => WithLp.toLp 2 (fun ν => x (v, ν))

def networkEdgeDifference {E : Type*} {n : ℕ} (src dst : E → Option (Fin n))
    (x : NetworkVisitSpace n) (e : E) : ScalarMomentum := networkVisit x (dst e) - networkVisit x (src e)

theorem networkVisit_coordinate {n : ℕ} (x : NetworkVisitSpace n) (v : Option (Fin n)) (ν : Fin 4) :
    networkVisit x v ν = networkRootLift (fun j => x (j, ν)) v := by cases v <;> rfl

theorem networkEdgeDifference_eq_routing {E : Type*} {n : ℕ} (src dst : E → Option (Fin n))
    (x : NetworkVisitSpace n) (e : E) :
    networkEdgeDifference src dst x e = residualRouting (groundedNetworkIncidence src dst) e x := by
  ext ν
  rw [residualRouting_component]
  change networkVisit x (dst e) ν - networkVisit x (src e) ν =
    (groundedNetworkIncidence src dst *ᵥ (fun j => x (j, ν))) e
  rw [groundedNetworkIncidence_mulVec, networkVisit_coordinate, networkVisit_coordinate]

def networkSharedEnergy {E : Type*} [Fintype E] {n : ℕ}
    (src dst : E → Option (Fin n)) (s : E → ℝ) (x : NetworkVisitSpace n) : ℝ :=
  ∑ e, (s e)⁻¹ * ‖networkEdgeDifference src dst x e‖ ^ 2

/-- The actual shared-vertex edge energy is exactly the four-coordinate
realization of H=Dᵀ diag(s⁻¹) D, with no independent copy per edge. -/
theorem networkSharedEnergy_matrix {E : Type*} [Fintype E] {n : ℕ}
    (src dst : E → Option (Fin n)) (s : E → ℝ) (x : NetworkVisitSpace n) :
    networkSharedEnergy src dst s x =
      ∑ ν : Fin 4, (fun j => x (j, ν)) ⬝ᵥ
        (networkPrecision src dst s *ᵥ (fun j => x (j, ν))) := by
  unfold networkSharedEnergy
  simp_rw [networkEdgeDifference_eq_routing]
  exact residualGram_four_coordinate_identity (groundedNetworkIncidence src dst) (fun e => (s e)⁻¹) x

theorem networkSharedEnergy_positive {E : Type*} [Fintype E] {n : ℕ}
    (G : SimpleGraph (Option (Fin n))) (src dst : E → Option (Fin n)) (s : E → ℝ)
    (hG : G.Connected) (hcover : NetworkOrientationCovers G src dst) (hs : ∀ e, 0 < s e)
    {x : NetworkVisitSpace n} (hx : x ≠ 0) : 0 < networkSharedEnergy src dst s x := by
  unfold networkSharedEnergy
  simp_rw [networkEdgeDifference_eq_routing]
  have hH : (residualGram (groundedNetworkIncidence src dst) (fun e => (s e)⁻¹)).PosDef :=
    networkPrecision_posDef G src dst s hG hcover hs
  exact residualGram_positive (groundedNetworkIncidence src dst) (fun e => (s e)⁻¹) hH hx

theorem networkSharedEnergy_continuous {E : Type*} [Fintype E] {n : ℕ}
    (src dst : E → Option (Fin n)) (s : E → ℝ) : Continuous (networkSharedEnergy src dst s) := by
  unfold networkSharedEnergy
  simp_rw [networkEdgeDifference_eq_routing]
  fun_prop

theorem networkSharedEnergy_coercive {E : Type*} [Fintype E] {n : ℕ}
    (G : SimpleGraph (Option (Fin n))) (src dst : E → Option (Fin n)) (s : E → ℝ)
    (hG : G.Connected) (hcover : NetworkOrientationCovers G src dst) (hs : ∀ e, 0 < s e) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ x : NetworkVisitSpace n, γ * ‖x‖ ^ 2 ≤ networkSharedEnergy src dst s x := by
  apply positive_homogeneous_coercivity (networkSharedEnergy src dst s)
    (networkSharedEnergy_continuous src dst s) (n := 2) (by norm_num)
  · intro t _ x
    unfold networkSharedEnergy
    simp_rw [networkEdgeDifference_eq_routing, map_smul, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    ring
  · intro x hx
    apply networkSharedEnergy_positive G src dst s hG hcover hs
    intro hz
    rw [hz, norm_zero] at hx
    norm_num at hx

def networkIncidenceBound {E : Type*} [Fintype E] {n : ℕ}
    (src dst : E → Option (Fin n)) : ℝ :=
  ∑ e, ‖residualRouting (groundedNetworkIncidence src dst) e‖ ^ 2

theorem networkSharedEnergy_unweighted_upper {E : Type*} [Fintype E] {n : ℕ}
    (src dst : E → Option (Fin n)) (x : NetworkVisitSpace n) :
    networkSharedEnergy src dst (fun _ => 1) x ≤ networkIncidenceBound src dst * ‖x‖ ^ 2 := by
  unfold networkSharedEnergy networkIncidenceBound
  simp only [inv_one, one_mul]
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro e _
  rw [networkEdgeDifference_eq_routing]
  simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _)
    ((residualRouting (groundedNetworkIncidence src dst) e).le_opNorm x) 2

/-- Uniform precision bounds on every box of positive durations. The
constants depend on the connected incidence graph, while the duration
dependence is exactly s_max⁻¹ and s_min⁻¹. -/
theorem networkSharedEnergy_duration_bounds {E : Type*} [Fintype E] {n : ℕ}
    (G : SimpleGraph (Option (Fin n))) (src dst : E → Option (Fin n))
    (hG : G.Connected) (hcover : NetworkOrientationCovers G src dst) :
    ∃ γ C : ℝ, 0 < γ ∧ 0 ≤ C ∧ ∀ (s : E → ℝ) (smin smax : ℝ),
      0 < smin → 0 < smax → (∀ e, smin ≤ s e ∧ s e ≤ smax) →
      ∀ x : NetworkVisitSpace n,
        γ / smax * ‖x‖ ^ 2 ≤ networkSharedEnergy src dst s x ∧
          networkSharedEnergy src dst s x ≤ C / smin * ‖x‖ ^ 2 := by
  obtain ⟨γ, hγ, hlo⟩ := networkSharedEnergy_coercive G src dst (fun _ => 1) hG hcover (fun _ => zero_lt_one)
  refine ⟨γ, networkIncidenceBound src dst, hγ, Finset.sum_nonneg (fun _ _ => sq_nonneg _), ?_⟩
  intro s smin smax hmin hmax hs x
  have hse (e : E) : 0 < s e := hmin.trans_le (hs e).1
  have hLower : smax⁻¹ * networkSharedEnergy src dst (fun _ => 1) x ≤ networkSharedEnergy src dst s x := by
    unfold networkSharedEnergy
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro e _
    simp only [inv_one, one_mul]
    exact mul_le_mul_of_nonneg_right (inv_anti₀ (hse e) (hs e).2) (sq_nonneg _)
  have hUpper : networkSharedEnergy src dst s x ≤ smin⁻¹ * networkSharedEnergy src dst (fun _ => 1) x := by
    unfold networkSharedEnergy
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro e _
    simp only [inv_one, one_mul]
    exact mul_le_mul_of_nonneg_right (inv_anti₀ hmin (hs e).1) (sq_nonneg _)
  constructor
  · calc
      _ = smax⁻¹ * (γ * ‖x‖ ^ 2) := by ring
      _ ≤ smax⁻¹ * networkSharedEnergy src dst (fun _ => 1) x :=
        mul_le_mul_of_nonneg_left (hlo x) (inv_pos.mpr hmax).le
      _ ≤ _ := hLower
  · calc
      _ ≤ smin⁻¹ * networkSharedEnergy src dst (fun _ => 1) x := hUpper
      _ ≤ smin⁻¹ * (networkIncidenceBound src dst * ‖x‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (networkSharedEnergy_unweighted_upper src dst x) (inv_pos.mpr hmin).le
      _ = _ := by ring

def networkSharedPrefactor {E : Type*} [Fintype E] (m z s : E → ℝ) : ℝ :=
  ∏ e, networkHeatFive (m e) (z e) (s e)

def networkSharedKernel {E : Type*} [Fintype E] {n : ℕ}
    (src dst : E → Option (Fin n)) (m z s : E → ℝ) (x : NetworkVisitSpace n) : ℝ :=
  ∏ e, networkHeatFive (m e) (z e) (s e) *
    Real.exp (-‖networkEdgeDifference src dst x e‖ ^ 2 / (4 * s e))

/-- Literal multiplication of the original five-dimensional edge kernels.
The same x_v is used at every occurrence of vertex v. -/
theorem networkSharedKernel_literal {E : Type*} [Fintype E] {n : ℕ}
    (src dst : E → Option (Fin n)) (m z s : E → ℝ) (hs : ∀ e, 0 < s e) (x : NetworkVisitSpace n) :
    networkSharedKernel src dst m z s x = ∏ e,
      (4 * Real.pi * s e) ^ (-(5 : ℝ) / 2) *
        Real.exp (-((m e) ^ 2 * s e) -
          (‖networkEdgeDifference src dst x e‖ ^ 2 + (z e) ^ 2) / (4 * s e)) := by
  unfold networkSharedKernel
  apply Finset.prod_congr rfl
  intro e _
  rw [networkHeatFive_standard (hs e), mul_assoc, ← Real.exp_add]
  congr 2
  ring

theorem networkSharedKernel_gaussian {E : Type*} [Fintype E] {n : ℕ}
    (src dst : E → Option (Fin n)) (m z s : E → ℝ) (x : NetworkVisitSpace n) :
    networkSharedKernel src dst m z s x = networkSharedPrefactor m z s *
      Real.exp (-(networkSharedEnergy src dst s x) / 4) := by
  unfold networkSharedKernel networkSharedPrefactor
  rw [Finset.prod_mul_distrib, ← Real.exp_sum]
  congr 2
  unfold networkSharedEnergy
  rw [← Finset.sum_neg_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro e _
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem networkSharedPrefactor_nonneg {E : Type*} [Fintype E]
    (m z s : E → ℝ) (hs : ∀ e, 0 < s e) : 0 ≤ networkSharedPrefactor m z s :=
  Finset.prod_nonneg (fun e _ => networkHeatFive_nonneg (hs e).le _ _)

theorem networkSharedPrefactor_pos {E : Type*} [Fintype E]
    (m z s : E → ℝ) (hs : ∀ e, 0 < s e) : 0 < networkSharedPrefactor m z s := by
  apply Finset.prod_pos
  intro e _
  have hse := hs e
  unfold networkHeatFive
  positivity

theorem networkSharedKernel_nonneg {E : Type*} [Fintype E] {n : ℕ}
    (src dst : E → Option (Fin n)) (m z s : E → ℝ) (hs : ∀ e, 0 < s e) (x : NetworkVisitSpace n) :
    0 ≤ networkSharedKernel src dst m z s x := by
  rw [networkSharedKernel_gaussian]
  exact mul_nonneg (networkSharedPrefactor_nonneg m z s hs) (Real.exp_pos _).le

theorem networkSharedKernel_pos {E : Type*} [Fintype E] {n : ℕ}
    (src dst : E → Option (Fin n)) (m z s : E → ℝ) (hs : ∀ e, 0 < s e) (x : NetworkVisitSpace n) :
    0 < networkSharedKernel src dst m z s x := by
  rw [networkSharedKernel_gaussian]
  exact mul_pos (networkSharedPrefactor_pos m z s hs) (Real.exp_pos _)

theorem networkSharedKernel_continuous {E : Type*} [Fintype E] {n : ℕ}
    (src dst : E → Option (Fin n)) (m z s : E → ℝ) : Continuous (networkSharedKernel src dst m z s) := by
  have he : networkSharedKernel src dst m z s = fun x : NetworkVisitSpace n =>
      networkSharedPrefactor m z s * Real.exp (-(networkSharedEnergy src dst s x) / 4) :=
    funext (networkSharedKernel_gaussian src dst m z s)
  rw [he]
  exact continuous_const.mul (Real.continuous_exp.comp ((networkSharedEnergy_continuous src dst s).neg.div_const 4))

theorem networkSharedKernel_integrable {E : Type*} [Fintype E] {n : ℕ}
    (G : SimpleGraph (Option (Fin n))) (src dst : E → Option (Fin n)) (m z s : E → ℝ)
    (hG : G.Connected) (hcover : NetworkOrientationCovers G src dst) (hs : ∀ e, 0 < s e) :
    Integrable (networkSharedKernel src dst m z s) := by
  obtain ⟨γ, hγ, hbound⟩ := networkSharedEnergy_coercive G src dst s hG hcover hs
  have hi : Integrable (fun x : NetworkVisitSpace n => Real.exp (-((γ / 4) * ‖x‖ ^ 2))) := by
    apply (integrable_real_degree_gaussian (a := γ / 4) (D := 0) (by positivity) le_rfl).mono'
      (by fun_prop)
    filter_upwards with x
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    simp only [Real.rpow_zero]
    nlinarith [Real.exp_pos (-((γ / 4) * ‖x‖ ^ 2))]
  apply (hi.const_mul (networkSharedPrefactor m z s)).mono'
    (networkSharedKernel_continuous src dst m z s).aestronglyMeasurable
  filter_upwards with x
  rw [Real.norm_of_nonneg (networkSharedKernel_nonneg src dst m z s hs x), networkSharedKernel_gaussian]
  apply mul_le_mul_of_nonneg_left _ (networkSharedPrefactor_nonneg m z s hs)
  apply Real.exp_le_exp.mpr
  nlinarith [hbound x]

def networkSharedFourier {E : Type*} [Fintype E] {n : ℕ}
    (src dst : E → Option (Fin n)) (m z s : E → ℝ) (q : NetworkVisitSpace n) : ℂ :=
  ∫ x : NetworkVisitSpace n, Complex.exp (Complex.I * (inner ℝ q x : ℂ)) *
    (networkSharedKernel src dst m z s x : ℂ)

def networkRoutedFourier {E : Type*} [Fintype E] {n L : ℕ}
    (src dst : E → Option (Fin n)) (m z s : E → ℝ)
    (B : NetworkVisitSpace L →L[ℝ] NetworkVisitSpace n) (b : NetworkVisitSpace n)
    (k : NetworkVisitSpace L) : ℂ := networkSharedFourier src dst m z s (B k + b)

theorem networkSharedFourier_zero {E : Type*} [Fintype E] {n : ℕ}
    (src dst : E → Option (Fin n)) (m z s : E → ℝ) :
    networkSharedFourier src dst m z s 0 = ((∫ x, networkSharedKernel src dst m z s x : ℝ) : ℂ) := by
  unfold networkSharedFourier
  simp only [inner_zero_left, Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul]
  exact integral_complex_ofReal

theorem networkSharedFourier_zero_re_pos {E : Type*} [Fintype E] {n : ℕ}
    (G : SimpleGraph (Option (Fin n))) (src dst : E → Option (Fin n)) (m z s : E → ℝ)
    (hG : G.Connected) (hcover : NetworkOrientationCovers G src dst) (hs : ∀ e, 0 < s e) :
    0 < (networkSharedFourier src dst m z s 0).re := by
  rw [networkSharedFourier_zero, Complex.ofReal_re]
  exact integral_pos_of_integrable_nonneg_nonzero
    (networkSharedKernel_continuous src dst m z s)
    (networkSharedKernel_integrable G src dst m z s hG hcover hs)
    (networkSharedKernel_nonneg src dst m z s hs)
    (networkSharedKernel_pos src dst m z s hs 0).ne'

theorem networkSharedFourier_integrable {E : Type*} [Fintype E] {n : ℕ}
    (G : SimpleGraph (Option (Fin n))) (src dst : E → Option (Fin n)) (m z s : E → ℝ)
    (hG : G.Connected) (hcover : NetworkOrientationCovers G src dst) (hs : ∀ e, 0 < s e)
    (q : NetworkVisitSpace n) :
    Integrable (fun x : NetworkVisitSpace n => Complex.exp (Complex.I * (inner ℝ q x : ℂ)) *
      (networkSharedKernel src dst m z s x : ℂ)) := by
  have hi : Integrable (fun x : NetworkVisitSpace n => (networkSharedKernel src dst m z s x : ℂ)) :=
    (networkSharedKernel_integrable G src dst m z s hG hcover hs).ofReal
  have hp : Continuous (fun x : NetworkVisitSpace n => Complex.exp (Complex.I * (inner ℝ q x : ℂ))) := by
    fun_prop
  apply hi.bdd_mul hp.aestronglyMeasurable
  refine ⟨1, fun x => ?_⟩
  simp [Complex.norm_exp, Complex.mul_re]

theorem networkSharedFourier_norm_le {E : Type*} [Fintype E] {n : ℕ}
    (src dst : E → Option (Fin n)) (m z s : E → ℝ) (hs : ∀ e, 0 < s e) (q : NetworkVisitSpace n) :
    ‖networkSharedFourier src dst m z s q‖ ≤ ∫ x, networkSharedKernel src dst m z s x := by
  unfold networkSharedFourier
  have he : (fun x : NetworkVisitSpace n => ‖Complex.exp (Complex.I * (inner ℝ q x : ℂ)) *
      (networkSharedKernel src dst m z s x : ℂ)‖) = networkSharedKernel src dst m z s := by
    funext x
    rw [norm_mul, Complex.norm_exp]
    simp only [Complex.mul_re, Complex.I_re, Complex.ofReal_re, Complex.I_im, Complex.ofReal_im,
      mul_zero, zero_mul, sub_self, Real.exp_zero, one_mul, Complex.norm_real,
      Real.norm_of_nonneg (networkSharedKernel_nonneg src dst m z s hs x)]
  simpa only [he] using norm_integral_le_integral_norm
    (fun x : NetworkVisitSpace n => Complex.exp (Complex.I * (inner ℝ q x : ℂ)) *
      (networkSharedKernel src dst m z s x : ℂ))

end UV
