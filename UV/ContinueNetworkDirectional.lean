import UV.RealDegree
import UV.ResidualCoercivity
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Funext

/-! The literal polynomial, affine massive factors, and Gaussian
exponent in the directional absolute-integrability model. -/

noncomputable section

open MeasureTheory Filter
open scoped BigOperators InnerProductSpace

namespace UV

abbrev DirectionalMomentum (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The original polynomial evaluated on real momentum, allowing complex coefficients. -/
def directionalNumerator {d : ℕ} (P : MvPolynomial (Fin d) ℂ)
    (k : DirectionalMomentum d) : ℂ :=
  MvPolynomial.eval (fun i => (k i : ℂ)) P

theorem directionalNumerator_exists_ne_zero {d : ℕ} {P : MvPolynomial (Fin d) ℂ}
    (hP : P ≠ 0) : ∃ k, directionalNumerator P k ≠ 0 := by
  contrapose! hP
  apply MvPolynomial.funext_set (fun _ => Set.range (Complex.ofReal : ℝ → ℂ))
    (fun _ => Set.infinite_range_of_injective Complex.ofReal_injective)
  intro z hz
  choose x hx using fun i => hz i (Set.mem_univ i)
  let k : DirectionalMomentum d := WithLp.toLp 2 x
  have hcoords : (fun i => (k i : ℂ)) = z := funext hx
  simpa [directionalNumerator, hcoords] using hP k

theorem directionalNumerator_continuous {d : ℕ} (P : MvPolynomial (Fin d) ℂ) :
    Continuous (directionalNumerator P) := by
  induction P using MvPolynomial.induction_on with
  | C a =>
      convert (continuous_const : Continuous (fun _ : DirectionalMomentum d => a)) using 1
      ext k
      simp [directionalNumerator]
  | add p q hp hq =>
      convert hp.add hq using 1
      ext k
      simp [directionalNumerator]
  | mul_X p i hp =>
      convert hp.mul (Complex.continuous_ofReal.comp
        (PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) i)) using 1
      ext k
      simp [directionalNumerator]

theorem directionalNumerator_polynomial_bound {d : ℕ} (P : MvPolynomial (Fin d) ℂ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ N : ℕ, ∀ k, ‖directionalNumerator P k‖ ≤ K * (1 + ‖k‖) ^ N := by
  induction P using MvPolynomial.induction_on with
  | C a =>
      exact ⟨‖a‖, norm_nonneg _, 0, fun k => by simp [directionalNumerator]⟩
  | add p q hp hq =>
      obtain ⟨Cp, hCp, Np, hp⟩ := hp
      obtain ⟨Cq, hCq, Nq, hq⟩ := hq
      refine ⟨Cp + Cq, add_nonneg hCp hCq, max Np Nq, fun k => ?_⟩
      have hk : 1 ≤ 1 + ‖k‖ := le_add_of_nonneg_right (norm_nonneg _)
      rw [directionalNumerator, map_add]
      apply (norm_add_le _ _).trans
      rw [add_mul]
      refine add_le_add ((hp k).trans ?_) ((hq k).trans ?_)
      · exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hk (le_max_left _ _)) hCp
      · exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hk (le_max_right _ _)) hCq
  | mul_X p i hp =>
      obtain ⟨C, hC, N, hp⟩ := hp
      refine ⟨C, hC, N + 1, fun k => ?_⟩
      rw [directionalNumerator, map_mul, MvPolynomial.eval_X, norm_mul, Complex.norm_real,
        pow_succ, ← mul_assoc]
      exact mul_le_mul (hp k) ((PiLp.norm_apply_le (p := 2) k i).trans
        (le_add_of_nonneg_left zero_le_one)) (norm_nonneg _) (by positivity)

theorem directionalNumerator_real_degree_bound {d : ℕ} (P : MvPolynomial (Fin d) ℂ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ N : ℕ, ∀ k, ‖directionalNumerator P k‖ ≤ K * (1 + ‖k‖ ^ (N : ℝ)) := by
  obtain ⟨K, hK, N, hN⟩ := directionalNumerator_polynomial_bound P
  refine ⟨K * 2 ^ N, by positivity, N, fun k => (hN k).trans ?_⟩
  rw [Real.rpow_natCast, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ hK
  by_cases h : ‖k‖ ≤ 1
  · exact (pow_le_pow_left₀ (by positivity) (by linarith : 1 + ‖k‖ ≤ 2) _).trans
      (le_mul_of_one_le_right (by positivity) (le_add_of_nonneg_right (by positivity)))
  · calc
      _ ≤ (2 * ‖k‖) ^ N := pow_le_pow_left₀ (by positivity) (by linarith) _
      _ = 2 ^ N * ‖k‖ ^ N := mul_pow _ _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one) (by positivity)

/-- The reference massive denominator uses the actual routed line momentum. -/
def directionalMassiveFactor {V : Type*} [NormedAddCommGroup V] (ν : ℝ) (x : V) : ℝ :=
  (1 + ‖x‖ ^ 2) ^ (-ν)

theorem directionalMassiveFactor_pos {V : Type*} [NormedAddCommGroup V] (ν : ℝ) (x : V) :
    0 < directionalMassiveFactor ν x := by
  unfold directionalMassiveFactor
  positivity

theorem directionalMassiveFactor_le_one {V : Type*} [NormedAddCommGroup V] {ν : ℝ}
    (hν : 0 ≤ ν) (x : V) : directionalMassiveFactor ν x ≤ 1 := by
  exact Real.rpow_le_one_of_one_le_of_nonpos
    (le_add_of_nonneg_right (sq_nonneg ‖x‖)) (neg_nonpos.mpr hν)

theorem directionalMassiveFactor_continuous {V : Type*} [NormedAddCommGroup V] (ν : ℝ) :
    Continuous (directionalMassiveFactor (V := V) ν) := by
  apply Continuous.rpow_const (by fun_prop)
  intro x
  exact Or.inl (by positivity)

private theorem directionalShift_normSq {V : Type*} [NormedAddCommGroup V] (x p : V) :
    1 + ‖x + p‖ ^ 2 ≤ (2 * (1 + ‖p‖ ^ 2)) * (1 + ‖x‖ ^ 2) := by
  have h := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le x p) 2
  have hprod := mul_nonneg (sq_nonneg ‖p‖) (sq_nonneg ‖x‖)
  nlinarith only [h, hprod, sq_nonneg (‖x‖ - ‖p‖)]

/-- Removing a fixed affine shift changes the massive factor only by
positive comparison constants depending on that shift and the exponent. -/
theorem directionalMassiveFactor_shift_compare {V : Type*} [NormedAddCommGroup V]
    {ν : ℝ} (hν : 0 ≤ ν) (x p : V) :
    (2 * (1 + ‖p‖ ^ 2)) ^ (-ν) * directionalMassiveFactor ν x ≤
      directionalMassiveFactor ν (x + p) ∧
    directionalMassiveFactor ν (x + p) ≤
      (2 * (1 + ‖p‖ ^ 2)) ^ ν * directionalMassiveFactor ν x := by
  have lower (u v : V) :
      (2 * (1 + ‖v‖ ^ 2)) ^ (-ν) * directionalMassiveFactor ν u ≤
        directionalMassiveFactor ν (u + v) := by
    unfold directionalMassiveFactor
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    exact Real.rpow_le_rpow_of_nonpos (by positivity) (directionalShift_normSq u v)
      (neg_nonpos.mpr hν)
  refine ⟨lower x p, ?_⟩
  have hup := lower (x + p) (-p)
  simp only [norm_neg, add_neg_cancel_right] at hup
  have hconst : 0 < (2 * (1 + ‖p‖ ^ 2)) ^ ν := by positivity
  have hh := mul_le_mul_of_nonneg_left hup hconst.le
  rwa [← mul_assoc, ← Real.rpow_add (by positivity), add_neg_cancel, Real.rpow_zero,
    one_mul] at hh

variable {E : Type*} [Fintype E] {d : ℕ}
variable {V : E → Type*} [∀ e, NormedAddCommGroup (V e)] [∀ e, NormedSpace ℝ (V e)]

def directionalAbsoluteModel (Q : DirectionalMomentum d →L[ℝ] DirectionalMomentum d)
    (h : DirectionalMomentum d) (C : ∀ e, DirectionalMomentum d →L[ℝ] V e)
    (p : ∀ e, V e) (ν : E → ℝ) (P : MvPolynomial (Fin d) ℂ)
    (k : DirectionalMomentum d) : ℝ :=
  ‖directionalNumerator P k‖ * Real.exp (-inner ℝ k (Q k) + inner ℝ h k) *
    ∏ e, directionalMassiveFactor (ν e) (C e k + p e)

theorem directionalAbsoluteModel_continuous
    (Q : DirectionalMomentum d →L[ℝ] DirectionalMomentum d) (h : DirectionalMomentum d)
    (C : ∀ e, DirectionalMomentum d →L[ℝ] V e) (p : ∀ e, V e) (ν : E → ℝ)
    (P : MvPolynomial (Fin d) ℂ) :
    Continuous (directionalAbsoluteModel Q h C p ν P) := by
  unfold directionalAbsoluteModel
  apply ((directionalNumerator_continuous P).norm.mul (by fun_prop)).mul
  exact continuous_finset_prod _ fun e _ =>
    (directionalMassiveFactor_continuous (ν e)).comp ((C e).continuous.add continuous_const)

/-- The strictly positive part of the directional criterion. Positive
definiteness gives a Gaussian bound after absorbing the exact drift;
each shifted denominator stays bounded by one. -/
theorem directionalAbsoluteModel_integrable_of_posDef
    (Q : DirectionalMomentum d →L[ℝ] DirectionalMomentum d) (h : DirectionalMomentum d)
    (C : ∀ e, DirectionalMomentum d →L[ℝ] V e) (p : ∀ e, V e)
    (ν : E → ℝ) (hν : ∀ e, 0 ≤ ν e) (P : MvPolynomial (Fin d) ℂ)
    (hQ : ∀ k, k ≠ 0 → 0 < inner ℝ k (Q k)) :
    Integrable (directionalAbsoluteModel Q h C p ν P) := by
  have hhom (t : ℝ) (ht : 0 ≤ t) (k : DirectionalMomentum d) :
      inner ℝ (t • k) (Q (t • k)) = t ^ (2 : ℕ) * inner ℝ k (Q k) := by
    rw [map_smul, real_inner_smul_left, real_inner_smul_right]
    ring
  have hcont : Continuous (fun k => inner ℝ k (Q k)) :=
    continuous_id.inner Q.continuous
  obtain ⟨a, ha, haq⟩ := positive_homogeneous_coercivity (fun k => inner ℝ k (Q k)) hcont
    (by norm_num : 0 < (2 : ℕ)) hhom (fun k hk => hQ k (by
      intro hz
      simp [hz] at hk))
  obtain ⟨K, hK, N, hN⟩ := directionalNumerator_real_degree_bound P
  refine residual_quadratic_real_degree_convergence (P := Unit)
    (f := fun _ => directionalAbsoluteModel Q h C p ν P)
    (ψ := fun _ k => inner ℝ k (Q k) - inner ℝ h k)
    (a := a / 2) (B := ‖h‖ ^ 2 / (2 * a)) (C := K) (D := (N : ℝ))
    (by positivity) hK (by positivity)
    (fun _ => (directionalAbsoluteModel_continuous Q h C p ν P).aestronglyMeasurable) ?_ ?_ ()
  · intro _ k
    unfold directionalAbsoluteModel
    rw [Real.norm_of_nonneg (by
      exact mul_nonneg (mul_nonneg (norm_nonneg _) (Real.exp_nonneg _))
        (Finset.prod_nonneg fun e _ => (directionalMassiveFactor_pos _ _).le))]
    rw [neg_sub, sub_eq_add_neg, add_comm (inner ℝ h k)]
    have hprod : (∏ e, directionalMassiveFactor (ν e) (C e k + p e)) ≤ 1 :=
      Finset.prod_le_one (fun e _ => (directionalMassiveFactor_pos _ _).le)
        fun e _ => directionalMassiveFactor_le_one (hν e) _
    exact (mul_le_of_le_one_right (by positivity) hprod).trans
      (mul_le_mul_of_nonneg_right (hN k) (Real.exp_nonneg _))
  · intro _ k
    have hq := haq k
    have hh := real_inner_le_norm h k
    have hy : ‖h‖ * ‖k‖ ≤ a / 2 * ‖k‖ ^ 2 + ‖h‖ ^ 2 / (2 * a) := by
      have hy' : ‖h‖ * ‖k‖ - a / 2 * ‖k‖ ^ 2 ≤ ‖h‖ ^ 2 / (2 * a) := by
        apply (le_div_iff₀ (show 0 < 2 * a by positivity)).mpr
        nlinarith only [sq_nonneg (a * ‖k‖ - ‖h‖)]
      linarith
    linarith

end UV
