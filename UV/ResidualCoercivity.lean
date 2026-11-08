import UV.RealDegree
import UV.Routing
import UV.RankMinor
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Normed.Module.FiniteDimension

noncomputable section
open MeasureTheory Set Real
open scoped BigOperators Matrix

namespace UV

/-- Compactness of the unit sphere turns a strictly positive homogeneous
function into a uniform positive coercivity margin. -/
theorem positive_homogeneous_coercivity
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (f : E → ℝ) (hf : Continuous f) {n : ℕ} (hn : 0 < n)
    (hhom : ∀ t : ℝ, 0 ≤ t → ∀ x, f (t • x) = t ^ n * f x)
    (hpos : ∀ x, ‖x‖ = 1 → 0 < f x) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ x, γ * ‖x‖ ^ n ≤ f x := by
  have hzero : f 0 = 0 := by
    have h := hhom 0 le_rfl 0
    simpa only [zero_smul, zero_pow (Nat.ne_of_gt hn), zero_mul] using h
  cases subsingleton_or_nontrivial E with
  | inl hs =>
    letI := hs
    refine ⟨1, zero_lt_one, ?_⟩
    intro x
    have hx : x = 0 := Subsingleton.elim _ _
    simp [hx, hzero, Nat.ne_of_gt hn]
  | inr hs =>
    letI := hs
    obtain ⟨ω, hω, hmin⟩ := (isCompact_sphere (0 : E) 1).exists_isMinOn
      (NormedSpace.sphere_nonempty.mpr zero_le_one) hf.continuousOn
    have hωnorm : ‖ω‖ = 1 := by simpa using hω
    refine ⟨f ω, hpos ω hωnorm, ?_⟩
    intro x
    by_cases hx : x = 0
    · simp [hx, hzero, Nat.ne_of_gt hn]
    have hnx : 0 < ‖x‖ := norm_pos_iff.mpr hx
    let u : E := ‖x‖⁻¹ • x
    have hu : ‖u‖ = 1 := by
      simp [u, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hnx.le), hnx.ne']
    have humem : u ∈ Metric.sphere (0 : E) 1 := by simpa using hu
    have hfx : f x = ‖x‖ ^ n * f u := by
      have h := hhom ‖x‖ hnx.le u
      simpa only [u, smul_smul, mul_inv_cancel₀ hnx.ne', one_smul] using h
    rw [hfx]
    simpa only [mul_comm] using
      mul_le_mul_of_nonneg_left (hmin humem) (pow_nonneg hnx.le n)

/-- Signed quadratic residuals retain the absolute value on the affine error,
so negative individual line residuals are allowed. -/
theorem signed_norm_sq_add_lower {V : Type*} [NormedAddCommGroup V]
    (h : ℝ) (x r : V) :
    h * ‖x‖ ^ 2 - |h| * (2 * ‖x‖ * ‖r‖ + ‖r‖ ^ 2) ≤ h * ‖x + r‖ ^ 2 := by
  have ha : |‖x + r‖ - ‖x‖| ≤ ‖r‖ := by
    simpa only [add_sub_cancel_left] using abs_norm_sub_norm_le (x + r) x
  have hs : 0 ≤ ‖x + r‖ + ‖x‖ := by positivity
  have hab : |‖x + r‖ ^ 2 - ‖x‖ ^ 2| ≤ 2 * ‖x‖ * ‖r‖ + ‖r‖ ^ 2 := by
    calc
      _ = |‖x + r‖ - ‖x‖| * (‖x + r‖ + ‖x‖) := by
        rw [← abs_of_nonneg hs, ← abs_mul]
        congr 1
        ring
      _ ≤ ‖r‖ * (‖x + r‖ + ‖x‖) := mul_le_mul_of_nonneg_right ha hs
      _ ≤ ‖r‖ * ((‖x‖ + ‖r‖) + ‖x‖) :=
        mul_le_mul_of_nonneg_left (add_le_add_right (norm_add_le x r) _) (norm_nonneg _)
      _ = _ := by ring
  have hh : |h * (‖x + r‖ ^ 2 - ‖x‖ ^ 2)| ≤
      |h| * (2 * ‖x‖ * ‖r‖ + ‖r‖ ^ 2) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hab (abs_nonneg h)
  have hl := (abs_le.mp hh).1
  nlinarith

/-- The explicit four-coordinate realization of a routing row. -/
def residualLineMatrix {I : Type*} {L : ℕ}
    (C : Matrix I (Fin L) ℝ) (i : I) : Matrix (Fin 4) (Fin L × Fin 4) ℝ :=
  fun ν j => C i j.1 * if ν = j.2 then 1 else 0

def residualRouting {I : Type*} {L : ℕ}
    (C : Matrix I (Fin L) ℝ) (i : I) :
    EuclideanSpace ℝ (Fin L × Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4) :=
  (Matrix.toEuclideanLin (residualLineMatrix C i)).toContinuousLinearMap

theorem residualRouting_component {I : Type*} {L : ℕ}
    (C : Matrix I (Fin L) ℝ) (i : I)
    (k : EuclideanSpace ℝ (Fin L × Fin 4)) (ν : Fin 4) :
    residualRouting C i k ν = ∑ j, C i j * k (j, ν) := by
  change (Matrix.mulVec (residualLineMatrix C i) (WithLp.ofLp k)) ν = _
  simp [Matrix.mulVec, dotProduct, residualLineMatrix, Fintype.sum_prod_type]

def residualGram {I : Type*} [Fintype I] {L : ℕ}
    (C : Matrix I (Fin L) ℝ) (h : I → ℝ) : Matrix (Fin L) (Fin L) ℝ := by
  classical
  exact C.transpose * Matrix.diagonal h * C

theorem residualGram_scalar_identity {I : Type*} [Fintype I] {L : ℕ}
    (C : Matrix I (Fin L) ℝ) (h : I → ℝ) (x : Fin L → ℝ) :
    x ⬝ᵥ (residualGram C h *ᵥ x) = ∑ i, h i * (C *ᵥ x) i ^ 2 := by
  classical
  unfold residualGram
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose]
  simp only [dotProduct, Matrix.mulVec_diagonal]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The signed routed quadratic residual is exactly the residual Gram form
in each of the four Euclidean components. -/
theorem residualGram_four_coordinate_identity {I : Type*} [Fintype I] {L : ℕ}
    (C : Matrix I (Fin L) ℝ) (h : I → ℝ)
    (k : EuclideanSpace ℝ (Fin L × Fin 4)) :
    (∑ i, h i * ‖residualRouting C i k‖ ^ 2) =
      ∑ ν : Fin 4, (fun j => k (j, ν)) ⬝ᵥ
        (residualGram C h *ᵥ (fun j => k (j, ν))) := by
  simp_rw [EuclideanSpace.norm_sq_eq, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ν _
  rw [residualGram_scalar_identity]
  apply Finset.sum_congr rfl
  intro i _
  rw [residualRouting_component]
  simp only [Real.norm_eq_abs, sq_abs, Matrix.mulVec, dotProduct]

/-- Positive definiteness is imposed on the actual signed Gram matrix;
individual residual coefficients need not be positive. -/
theorem residualGram_positive {I : Type*} [Fintype I] {L : ℕ}
    (C : Matrix I (Fin L) ℝ) (h : I → ℝ) (hH : (residualGram C h).PosDef)
    {k : EuclideanSpace ℝ (Fin L × Fin 4)} (hk : k ≠ 0) :
    0 < ∑ i, h i * ‖residualRouting C i k‖ ^ 2 := by
  rw [residualGram_four_coordinate_identity]
  have hp (x : Fin L → ℝ) (hx : x ≠ 0) : 0 < x ⬝ᵥ (residualGram C h *ᵥ x) := by
    simpa using hH.2 x hx
  have hn (x : Fin L → ℝ) : 0 ≤ x ⬝ᵥ (residualGram C h *ᵥ x) := by
    by_cases hx : x = 0
    · simp [hx]
    · exact (hp x hx).le
  have hex : ∃ ν : Fin 4, (fun j => k (j, ν)) ≠ 0 := by
    by_contra! hzero
    apply hk
    ext j
    exact congrFun (hzero j.2) j.1
  obtain ⟨ν, hν⟩ := hex
  exact (hp _ hν).trans_le
    (Finset.single_le_sum (fun ν _ => hn (fun j => k (j, ν))) (Finset.mem_univ ν))

/-- Homogeneous signed linear damping has a positive margin precisely when
its continuous unit-sphere residual is strictly positive. -/
theorem signed_linear_sphere_coercivity
    {I E V : Type*} [Fintype I] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (T : I → E →L[ℝ] V) (h : I → ℝ)
    (hsphere : ∀ k, ‖k‖ = 1 → 0 < ∑ i, h i * ‖T i k‖) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ k, γ * ‖k‖ ≤ ∑ i, h i * ‖T i k‖ := by
  have hm : Continuous (fun k => ∑ i, h i * ‖T i k‖) := by fun_prop
  have hhom : ∀ t : ℝ, 0 ≤ t → ∀ k : E,
      (∑ i, h i * ‖T i (t • k)‖) = t ^ 1 * ∑ i, h i * ‖T i k‖ := by
    intro t ht k
    simp only [map_smul, norm_smul, Real.norm_of_nonneg ht, pow_one, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simpa only [pow_one] using positive_homogeneous_coercivity _ hm (by norm_num : 0 < 1)
    hhom hsphere

theorem signed_linear_affine_from_sphere
    {I P E V : Type*} [Fintype I] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (T : I → E →L[ℝ] V) (h : I → ℝ) (R : I → P → V) (b : I → ℝ)
    (hb : ∀ i, 0 ≤ b i) (hR : ∀ i p, ‖R i p‖ ≤ b i)
    (hsphere : ∀ k, ‖k‖ = 1 → 0 < ∑ i, h i * ‖T i k‖) :
    ∃ γ B : ℝ, 0 < γ ∧ 0 ≤ B ∧ ∀ p k,
      γ * ‖k‖ - B ≤ ∑ i, h i * ‖T i k + R i p‖ := by
  obtain ⟨γ, hγ, hc⟩ := signed_linear_sphere_coercivity T h hsphere
  refine ⟨γ, ∑ i, |h i| * b i, hγ,
    Finset.sum_nonneg (fun i _ => mul_nonneg (abs_nonneg _) (hb i)), ?_⟩
  intro p k
  exact signed_affine_coercivity h (fun i k => T i k) R b γ hc hR k p

/-- Young's inequality bounds every signed affine quadratic error uniformly.
The positive homogeneous quadratic residual is used only on the unit sphere. -/
theorem signed_quadratic_affine_coercivity
    {I P E V : Type*} [Fintype I] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (T : I → E →L[ℝ] V) (h : I → ℝ) (R : I → P → V) (b : I → ℝ)
    (hb : ∀ i, 0 ≤ b i) (hR : ∀ i p, ‖R i p‖ ≤ b i)
    (hsphere : ∀ k, ‖k‖ = 1 → 0 < ∑ i, h i * ‖T i k‖ ^ 2) :
    ∃ lam B : ℝ, 0 < lam ∧ 0 ≤ B ∧ ∀ p k,
      (lam / 2) * ‖k‖ ^ 2 - B ≤ ∑ i, h i * ‖T i k + R i p‖ ^ 2 := by
  have hm : Continuous (fun k => ∑ i, h i * ‖T i k‖ ^ 2) := by fun_prop
  have hhom : ∀ t : ℝ, 0 ≤ t → ∀ k : E,
      (∑ i, h i * ‖T i (t • k)‖ ^ 2) = t ^ 2 * ∑ i, h i * ‖T i k‖ ^ 2 := by
    intro t ht k
    simp only [map_smul, norm_smul, Real.norm_of_nonneg ht, mul_pow, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  obtain ⟨lam, hlam, hc⟩ := positive_homogeneous_coercivity _ hm (by norm_num : 0 < 2)
    hhom hsphere
  let A := ∑ i, 2 * |h i| * ‖T i‖ * b i
  let B0 := ∑ i, |h i| * (b i) ^ 2
  have hB0 : 0 ≤ B0 := Finset.sum_nonneg fun i _ => mul_nonneg (abs_nonneg _) (sq_nonneg _)
  refine ⟨lam, A ^ 2 / (2 * lam) + B0, hlam, add_nonneg (by positivity) hB0, ?_⟩
  intro p k
  have herror i :
      |h i| * (2 * ‖T i k‖ * ‖R i p‖ + ‖R i p‖ ^ 2) ≤
        |h i| * (2 * ‖T i‖ * ‖k‖ * b i + (b i) ^ 2) := by
    have hc := mul_le_mul ((T i).le_opNorm k) (hR i p)
      (norm_nonneg (R i p)) (mul_nonneg (norm_nonneg (T i)) (norm_nonneg k))
    have hsq := (sq_le_sq₀ (norm_nonneg (R i p)) (hb i)).mpr (hR i p)
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    nlinarith
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    (sub_le_sub_left (herror i) (h i * ‖T i k‖ ^ 2)).trans
      (signed_norm_sq_add_lower (h i) (T i k) (R i p)))
  rw [Finset.sum_sub_distrib] at hs
  have he : (∑ i, |h i| * (2 * ‖T i‖ * ‖k‖ * b i + (b i) ^ 2)) = A * ‖k‖ + B0 := by
    calc
      _ = ∑ i, ((2 * |h i| * ‖T i‖ * b i) * ‖k‖ + |h i| * (b i) ^ 2) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by rw [Finset.sum_add_distrib, ← Finset.sum_mul]
  rw [he] at hs
  have hyoung : A * ‖k‖ ≤ (lam / 2) * ‖k‖ ^ 2 + A ^ 2 / (2 * lam) := by
    have heq : (lam / 2) * ‖k‖ ^ 2 + A ^ 2 / (2 * lam) =
        ((lam * ‖k‖) ^ 2 + A ^ 2) / (2 * lam) := by field_simp
    rw [heq]
    apply (le_div_iff₀ (by positivity : 0 < 2 * lam)).mpr
    nlinarith [sq_nonneg (lam * ‖k‖ - A)]
  linarith [hc k]

/-- Positive definiteness of the actual matrix `Cᵀdiag(h)C` supplies the
quadratic affine estimate, including signed individual residuals. -/
theorem matrix_residual_affine_coercivity
    {I P : Type*} [Fintype I] {L : ℕ}
    (C : Matrix I (Fin L) ℝ) (h : I → ℝ)
    (hH : (residualGram C h).PosDef)
    (R : I → P → EuclideanSpace ℝ (Fin 4)) (b : I → ℝ)
    (hb : ∀ i, 0 ≤ b i) (hR : ∀ i p, ‖R i p‖ ≤ b i) :
    ∃ lam B : ℝ, 0 < lam ∧ 0 ≤ B ∧ ∀ p k,
      (lam / 2) * ‖k‖ ^ 2 - B ≤
        ∑ i, h i * ‖residualRouting C i k + R i p‖ ^ 2 := by
  apply signed_quadratic_affine_coercivity (residualRouting C) h R b hb hR
  intro k hk
  apply residualGram_positive C h hH
  intro hzero
  simp [hzero] at hk

/-- Linear or quadratic damping size, used for the two source alternatives. -/
def residualSize {V : Type*} [NormedAddCommGroup V] (quadratic : Bool) (q : V) : ℝ :=
  if quadratic then ‖q‖ ^ 2 else ‖q‖

/-- The complete graph retains every covariance, every multiplier, and the
complete numerator whose possible exponential growth must be budgeted. -/
def residualGraph {I P E V F : Type*} [Fintype I]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (q : I → P → E → V) (cov Φ : I → V → ℝ) (N : P → E → F)
    (p : P) (k : E) : F :=
  (∏ i, cov i (q i p k) * Φ i (q i p k)) • N p k

/-- Complete vertex growth combines with the actual line damping into the
signed residual exponent. No line residual is replaced by its positive part. -/
theorem residual_complete_graph_bound
    {I P E V F : Type*} [Fintype I] [NormedAddCommGroup E]
    [NormedAddCommGroup V] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (quadratic : Bool) (q : I → P → E → V) (cov Φ : I → V → ℝ)
    (Ienv Benv d v : I → ℝ) (N : P → E → F) {C D : ℝ}
    (hBenv : ∀ i, 0 ≤ Benv i)
    (hcov : ∀ i x, 0 ≤ cov i x ∧ cov i x ≤ Ienv i)
    (hΦ : ∀ i x, 0 ≤ Φ i x ∧ Φ i x ≤ Benv i * exp (-d i * residualSize quadratic x))
    (hN : ∀ p k, ‖N p k‖ ≤ C * (1 + ‖k‖ ^ D) *
      exp (∑ i, v i * residualSize quadratic (q i p k))) (p : P) (k : E) :
    ‖residualGraph q cov Φ N p k‖ ≤
      (C * ∏ i, Ienv i * Benv i) * (1 + ‖k‖ ^ D) *
        exp (-(∑ i, (d i - v i) * residualSize quadratic (q i p k))) := by
  have hIenv i : 0 ≤ Ienv i := (hcov i 0).1.trans (hcov i 0).2
  have hp0 : 0 ≤ ∏ i, cov i (q i p k) * Φ i (q i p k) :=
    Finset.prod_nonneg fun i _ => mul_nonneg (hcov i _).1 (hΦ i _).1
  have hprod : (∏ i, cov i (q i p k) * Φ i (q i p k)) ≤
      (∏ i, Ienv i * Benv i) * exp (∑ i, -d i * residualSize quadratic (q i p k)) := by
    calc
      _ ≤ ∏ i, (Ienv i * Benv i) * exp (-d i * residualSize quadratic (q i p k)) := by
        apply Finset.prod_le_prod
        · intro i _; exact mul_nonneg (hcov i _).1 (hΦ i _).1
        · intro i _
          calc
            _ ≤ Ienv i * (Benv i * exp (-d i * residualSize quadratic (q i p k))) :=
              mul_le_mul (hcov i _).2 (hΦ i _).2 (hΦ i _).1 (hIenv i)
            _ = _ := by ring
      _ = _ := by rw [Finset.prod_mul_distrib, ← Real.exp_sum]
  have hprod0 : 0 ≤ (∏ i, Ienv i * Benv i) *
      exp (∑ i, -d i * residualSize quadratic (q i p k)) :=
    mul_nonneg (Finset.prod_nonneg fun i _ => mul_nonneg (hIenv i) (hBenv i)) (exp_nonneg _)
  have he : exp (∑ i, -d i * residualSize quadratic (q i p k)) *
      exp (∑ i, v i * residualSize quadratic (q i p k)) =
        exp (-(∑ i, (d i - v i) * residualSize quadratic (q i p k))) := by
    rw [← exp_add, ← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  unfold residualGraph
  rw [norm_smul, Real.norm_of_nonneg hp0]
  calc
    _ ≤ ((∏ i, Ienv i * Benv i) * exp (∑ i, -d i * residualSize quadratic (q i p k))) *
        (C * (1 + ‖k‖ ^ D) * exp (∑ i, v i * residualSize quadratic (q i p k))) :=
      mul_le_mul hprod (hN p k) (norm_nonneg _) hprod0
    _ = (C * ∏ i, Ienv i * Benv i) * (1 + ‖k‖ ^ D) *
        (exp (∑ i, -d i * residualSize quadratic (q i p k)) *
          exp (∑ i, v i * residualSize quadratic (q i p k))) := by ring
    _ = _ := by rw [he]

/-- The complete residual-coercivity proposition. The quadratic branch assumes
positive definiteness of the actual signed Gram matrix; the linear branch
assumes positive signed residual on the unit sphere. Uniform affine coercivity,
a common integrable majorant, and actual graph convergence are all derived. -/
theorem residual_coercivity_graph
    {I P F : Type*} [Fintype I] {L : ℕ}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (quadratic : Bool) (Croute : Matrix I (Fin L) ℝ)
    (R : I → P → EuclideanSpace ℝ (Fin 4)) (b : I → ℝ)
    (hb : ∀ i, 0 ≤ b i) (hR : ∀ i p, ‖R i p‖ ≤ b i)
    (cov Φ : I → EuclideanSpace ℝ (Fin 4) → ℝ) (Ienv Benv d v : I → ℝ)
    (hmcov : ∀ i, Measurable (cov i)) (hmΦ : ∀ i, Measurable (Φ i))
    (hBenv : ∀ i, 0 ≤ Benv i)
    (hcov : ∀ i x, 0 ≤ cov i x ∧ cov i x ≤ Ienv i)
    (hΦ : ∀ i x, 0 ≤ Φ i x ∧ Φ i x ≤ Benv i * exp (-d i * residualSize quadratic x))
    (N : P → EuclideanSpace ℝ (Fin L × Fin 4) → F)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hmN : ∀ p, StronglyMeasurable (N p))
    (hN : ∀ p k, ‖N p k‖ ≤ C * (1 + ‖k‖ ^ D) * exp
      (∑ i, v i * residualSize quadratic (residualRouting Croute i k + R i p)))
    (hcontrol : if quadratic then (residualGram Croute (fun i => d i - v i)).PosDef
      else ∀ k, ‖k‖ = 1 → 0 < ∑ i, (d i - v i) * ‖residualRouting Croute i k‖) :
    ∃ M : EuclideanSpace ℝ (Fin L × Fin 4) → ℝ, Integrable M volume ∧
      (∀ p k, ‖residualGraph (fun i p k => residualRouting Croute i k + R i p)
        cov Φ N p k‖ ≤ M k) ∧
      ∀ p, Integrable (residualGraph (fun i p k => residualRouting Croute i k + R i p)
        cov Φ N p) volume ∧
        (∫ k, ‖residualGraph (fun i p k => residualRouting Croute i k + R i p)
          cov Φ N p k‖) ≤ ∫ k, M k := by
  let q := fun i p k => residualRouting Croute i k + R i p
  let ψ := fun p k => ∑ i, (d i - v i) * residualSize quadratic (q i p k)
  have hc : ∃ c B : ℝ, 0 < c ∧ 0 ≤ B ∧ ∀ p k,
      c * residualSize quadratic k - B ≤ ψ p k := by
    cases hq : quadratic with
    | false =>
      have hs : ∀ k, ‖k‖ = 1 → 0 < ∑ i, (d i - v i) * ‖residualRouting Croute i k‖ := by
        simpa only [hq, Bool.false_eq_true, ite_false] using hcontrol
      simpa only [residualSize, hq, Bool.false_eq_true, ite_false, ψ, q] using
        signed_linear_affine_from_sphere (residualRouting Croute) (fun i => d i - v i) R b hb hR hs
    | true =>
      have hs : (residualGram Croute (fun i => d i - v i)).PosDef := by
        simpa only [hq, ite_true] using hcontrol
      obtain ⟨lam, B, hlam, hB, hc⟩ := matrix_residual_affine_coercivity
        Croute (fun i => d i - v i) hs R b hb hR
      refine ⟨lam / 2, B, by positivity, hB, ?_⟩
      simpa only [residualSize, hq, ite_true, ψ, q] using hc
  obtain ⟨c, B, hc, hB, hcoercive⟩ := hc
  let Ctotal := C * ∏ i, Ienv i * Benv i
  have hCt : 0 ≤ Ctotal := by
    apply mul_nonneg hC
    apply Finset.prod_nonneg
    intro i _
    exact mul_nonneg ((hcov i 0).1.trans (hcov i 0).2) (hBenv i)
  let W := fun k : EuclideanSpace ℝ (Fin L × Fin 4) =>
    (1 + ‖k‖ ^ D) * exp (-(c * residualSize quadratic k))
  have hiW : Integrable W volume := by
    cases hq : quadratic with
    | false => simpa only [W, residualSize, hq, Bool.false_eq_true, ite_false] using
        (integrable_real_degree_exp (E := EuclideanSpace ℝ (Fin L × Fin 4))) hc hD
    | true => simpa only [W, residualSize, hq, ite_true] using
        (integrable_real_degree_gaussian (E := EuclideanSpace ℝ (Fin L × Fin 4))) hc hD
  let M := fun k => (Ctotal * exp B) * W k
  have hiM : Integrable M volume := hiW.const_mul _
  have hbound p k : ‖residualGraph q cov Φ N p k‖ ≤ M k := by
    have hgraph := residual_complete_graph_bound quadratic q cov Φ Ienv Benv d v N hBenv hcov hΦ hN p k
    calc
      _ ≤ Ctotal * (1 + ‖k‖ ^ D) * exp (-ψ p k) := hgraph
      _ ≤ Ctotal * (1 + ‖k‖ ^ D) * exp (B - c * residualSize quadratic k) := by
        apply mul_le_mul_of_nonneg_left (exp_le_exp.mpr (by linarith [hcoercive p k]))
        exact mul_nonneg hCt (by positivity)
      _ = M k := by dsimp [M, W]; rw [exp_sub, exp_neg]; ring
  have hm p : StronglyMeasurable (residualGraph q cov Φ N p) := by
    apply StronglyMeasurable.smul _ (hmN p)
    apply Measurable.stronglyMeasurable
    apply Finset.measurable_prod
    intro i _
    have hq : Measurable (q i p) := by dsimp [q]; fun_prop
    exact ((hmcov i).comp hq).mul ((hmΦ i).comp hq)
  refine ⟨M, hiM, hbound, ?_⟩
  intro p
  have hi := hiM.mono' (hm p).aestronglyMeasurable (Filter.Eventually.of_forall (hbound p))
  exact ⟨hi, integral_mono_ae hi.norm hiM (Filter.Eventually.of_forall (hbound p))⟩

/-- Positive selected rows of full rank detect every nonzero loop vector. -/
theorem nonnegative_residual_positive_of_minor
    {I : Type*} [Fintype I] {L : ℕ}
    (C : Matrix I (Fin L) ℝ) (h : I → ℝ) (hnonnegative : ∀ i, 0 ≤ h i)
    (s : Fin L ↪ I) (hminor : Matrix.det (C.submatrix s id) ≠ 0)
    (hselected : ∀ j, 0 < h (s j))
    {k : EuclideanSpace ℝ (Fin L × Fin 4)} (hk : k ≠ 0) :
    0 < ∑ i, h i * ‖residualRouting C i k‖ := by
  classical
  have hinj : Function.Injective (C.submatrix s id).mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det _).mpr
      (isUnit_iff_ne_zero.mpr hminor))
  have hex : ∃ j, residualRouting C (s j) k ≠ 0 := by
    by_contra! hzero
    apply hk
    ext jν
    have hx : (fun j => k (j, jν.2)) = (0 : Fin L → ℝ) := by
      apply hinj
      rw [Matrix.mulVec_zero]
      ext j
      have hc := congrArg (fun x : EuclideanSpace ℝ (Fin 4) => x jν.2) (hzero j)
      simpa only [residualRouting_component, PiLp.zero_apply, Matrix.mulVec,
        Matrix.submatrix_apply, id_eq, dotProduct] using hc
    exact congrFun hx jν.1
  obtain ⟨j, hj⟩ := hex
  exact (mul_pos (hselected j) (norm_pos_iff.mpr hj)).trans_le
    (Finset.single_le_sum (fun i _ => mul_nonneg (hnonnegative i) (norm_nonneg (residualRouting C i k)))
      (Finset.mem_univ (s j)))

/-- The positive-row full-rank subcase in the source linear proposition. The
invertible positive row block is extracted from the rectangular rank premise. -/
theorem nonnegative_positive_row_rank_control
    {I : Type*} [Fintype I] {L : ℕ}
    (C : Matrix I (Fin L) ℝ) (h : I → ℝ) [Fintype {i : I // 0 < h i}]
    (hnonnegative : ∀ i, 0 ≤ h i)
    (hpositive_rank : (C.submatrix (fun i : {i : I // 0 < h i} => i.val) id).rank = L) :
    ∀ k : EuclideanSpace ℝ (Fin L × Fin 4), ‖k‖ = 1 →
      0 < ∑ i, h i * ‖residualRouting C i k‖ := by
  classical
  obtain ⟨s, hs⟩ := exists_invertible_row_minor _ hpositive_rank
  let sI : Fin L ↪ I := s.trans (Function.Embedding.subtype (fun i => 0 < h i))
  have hminor : Matrix.det (C.submatrix sI id) ≠ 0 := hs
  intro k hk
  apply nonnegative_residual_positive_of_minor C h hnonnegative sI hminor
    (fun j => (s j).property)
  intro hzero
  simp [hzero] at hk

end UV
