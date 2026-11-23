import UV.ContinueRetainedGaussianMoment
import UV.ContinueRetainedGaussianSewing
import UV.ContinueRetainedGaussianCofactor
import UV.ContinueRetainedGaussianDegenerate

/-! Transport of the Gaussian moments between four Euclidean Cartesian
components and their independent standardized coordinates. -/

noncomputable section

open Matrix MeasureTheory Set
open scoped Matrix BigOperators InnerProductSpace ENNReal

namespace UV

variable {R : Type*} [Fintype R] [DecidableEq R]

omit [DecidableEq R] in
private theorem retained_uncurry_preserving :
    MeasurePreserving (MeasurableEquiv.curry (Fin 4) R ℝ).symm volume volume := by
  let e := (MeasurableEquiv.curry (Fin 4) R ℝ).symm
  refine ⟨e.measurable, Eq.symm (Measure.pi_eq (fun s hs => ?_))⟩
  have hpre : e ⁻¹' univ.pi s = univ.pi (fun j => univ.pi (fun i => s (j, i))) := by
    ext x
    simp [e, Set.mem_pi]
  rw [Measure.map_apply e.measurable (MeasurableSet.univ_pi hs), hpre]
  change Measure.pi (fun _ : Fin 4 => Measure.pi (fun _ : R => volume))
    (univ.pi (fun j => univ.pi (fun i => s (j, i)))) = _
  rw [Measure.pi_pi]
  simp_rw [Measure.pi_pi]
  exact (Fintype.prod_prod_type (fun i : Fin 4 × R => (volume : Measure ℝ) (s i))).symm

private def retained_flat (b : OrthonormalBasis R ℝ (EuclideanSpace ℝ R)) :
    (Fin 4 → EuclideanSpace ℝ R) ≃ᵐ (Fin 4 × R → ℝ) :=
  (MeasurableEquiv.arrowCongr' (Equiv.refl (Fin 4))
    (b.measurableEquiv.trans (EuclideanSpace.measurableEquiv R))).trans
      (MeasurableEquiv.curry (Fin 4) R ℝ).symm

omit [DecidableEq R] in
private theorem retained_flat_apply (b : OrthonormalBasis R ℝ (EuclideanSpace ℝ R))
    (x : Fin 4 → EuclideanSpace ℝ R) (i : Fin 4 × R) :
    retained_flat b x i = b.repr (x i.1) i.2 := rfl

omit [DecidableEq R] in
private theorem retained_flat_preserving (b : OrthonormalBasis R ℝ (EuclideanSpace ℝ R)) :
    MeasurePreserving (retained_flat b) volume volume := by
  unfold retained_flat
  let e := b.measurableEquiv.trans (EuclideanSpace.measurableEquiv R)
  have he : MeasurePreserving e volume volume :=
    (EuclideanSpace.volume_preserving_measurableEquiv R).comp b.measurePreserving_measurableEquiv
  exact (retained_uncurry_preserving (R := R)).comp
    (measurePreserving_arrowCongr'
      (fun _ : Fin 4 => (volume : Measure (EuclideanSpace ℝ R)))
      (fun _ : Fin 4 => (volume : Measure (R → ℝ)))
      (Equiv.refl _) e (fun _ => he))

omit [DecidableEq R] in
private theorem retained_norm_sq_repr (b : OrthonormalBasis R ℝ (EuclideanSpace ℝ R))
    (x : EuclideanSpace ℝ R) : ‖x‖ ^ 2 = ∑ i, (b.repr x i) ^ 2 := by
  rw [← b.repr.norm_map x, EuclideanSpace.norm_sq_eq]
  simp

/-- Gaussian moment in four Euclidean Cartesian components with weight
((1+sum_mu|k_mu|^2)^h). -/
def retainedFourMoment (A : Matrix R R ℝ) (h : ℝ) : ℝ≥0∞ :=
  ∫⁻ x : Fin 4 → EuclideanSpace ℝ R, ENNReal.ofReal
    ((1 + ∑ μ, ‖x μ‖ ^ 2) ^ h * retainedFourGaussian A x)

private def retained_diagonal_integrand (a : Fin 4 × R → ℝ) (h : ℝ)
    (x : Fin 4 × R → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((1 + retainedCoordinateNormSq x) ^ h *
    Real.exp (-((∑ i, a i * x i ^ 2) / 2)))

private theorem retainedFourMoment_diagonal (A : Matrix R R ℝ) (hA : A.PosDef) (h : ℝ) :
    retainedFourMoment A h =
      ∫⁻ x, retained_diagonal_integrand (fun i : Fin 4 × R => hA.1.eigenvalues i.2) h x := by
  let b := hA.1.eigenvectorBasis
  let e := retained_flat b
  let a := fun i : Fin 4 × R => hA.1.eigenvalues i.2
  have he := retained_flat_preserving b
  rw [← he.lintegral_comp_emb e.measurableEmbedding]
  have hnorm (x : Fin 4 → EuclideanSpace ℝ R) :
      (∑ μ, ‖x μ‖ ^ 2) = retainedCoordinateNormSq (e x) := by
    simp only [retained_norm_sq_repr b, retainedCoordinateNormSq, Fintype.sum_prod_type, e,
      retained_flat_apply]
  have hexp (x : Fin 4 → EuclideanSpace ℝ R) :
      retainedFourGaussian A x = Real.exp (-((∑ i, a i * (e x i) ^ 2) / 2)) := by
    unfold retainedFourGaussian retainedGaussian
    rw [← Real.exp_sum, Fintype.sum_prod_type, Finset.sum_div, ← Finset.sum_neg_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro μ _
    rw [networkBasis_quadratic A b hA.1.eigenvalues (networkSPD_eigenbasis_action A hA.1)]
    rfl
  unfold retainedFourMoment
  apply lintegral_congr
  intro x
  change _ = retained_diagonal_integrand a h (e x)
  unfold retained_diagonal_integrand
  rw [← hnorm, ← hexp]

private theorem retainedFourMoment_scale (A : Matrix R R ℝ) (hA : A.PosDef) :
    ∃ d : ℝ≥0∞, d ≠ 0 ∧ d ≠ ∞ ∧ ∀ h : ℝ,
      d * retainedFourMoment A h = retainedScaledMoment h
        (fun i : Fin 4 × R => (hA.1.eigenvalues i.2)⁻¹) := by
  let a := fun i : Fin 4 × R => hA.1.eigenvalues i.2
  let s (i : Fin 4 × R) := (Real.sqrt (a i))⁻¹
  have ha (i : Fin 4 × R) : 0 < a i := hA.eigenvalues_pos i.2
  have hs (i : Fin 4 × R) : 0 < s i := inv_pos.mpr (Real.sqrt_pos.mpr (ha i))
  have hd : 0 < (diagonal s).det := by rw [det_diagonal]; exact Finset.prod_pos fun i _ => hs i
  let d := ENNReal.ofReal (diagonal s).det⁻¹
  refine ⟨d, (ENNReal.ofReal_pos.mpr (inv_pos.mpr hd)).ne', ENNReal.ofReal_ne_top, ?_⟩
  intro h
  let e := toLin' (diagonal s)
  have he : Measurable e := (LinearMap.continuous_on_pi e).measurable
  have hemap : Measure.map e volume = d • volume := by
    rw [Real.map_matrix_volume_pi_eq_smul_volume_pi hd.ne', abs_of_pos (inv_pos.mpr hd)]
  have hf : Measurable (retained_diagonal_integrand a h) := by
    unfold retained_diagonal_integrand retainedCoordinateNormSq
    fun_prop
  have hel (x : Fin 4 × R → ℝ) (i : Fin 4 × R) :
      e x i ^ 2 = (a i)⁻¹ * x i ^ 2 := by
    change ((diagonal s) *ᵥ x) i ^ 2 = _
    rw [mulVec_diagonal, mul_pow, show (s i) ^ 2 = (a i)⁻¹ by
      rw [show s i = (Real.sqrt (a i))⁻¹ from rfl, inv_pow, Real.sq_sqrt (ha i).le]]
  have hel' (x : Fin 4 × R → ℝ) (i : Fin 4 × R) :
      a i * (e x i) ^ 2 = x i ^ 2 := by
    rw [hel, ← mul_assoc, mul_inv_cancel₀ (ha i).ne', one_mul]
  rw [retainedFourMoment_diagonal A hA h, ← smul_eq_mul, ← lintegral_smul_measure, ← hemap,
    lintegral_map hf he]
  change (∫⁻ x, retained_diagonal_integrand a h (e x)) =
    retainedScaledMoment h (fun i => (a i)⁻¹)
  unfold retainedScaledMoment
  apply lintegral_congr
  intro x
  unfold retained_diagonal_integrand retainedCoordinateNormSq
  simp only [hel']
  simp only [hel]

theorem retainedInverse_trace (A : Matrix R R ℝ) (hA : A.PosDef) :
    A⁻¹.trace = ∑ i, (hA.1.eigenvalues i)⁻¹ := by
  let U : Matrix R R ℝ := hA.1.eigenvectorUnitary
  let a := hA.1.eigenvalues
  have hU : star U * U = 1 := unitary.coe_star_mul_self _
  have hU' : U * star U = 1 := unitary.coe_mul_star_self _
  have hspec : A = U * diagonal a * star U := hA.1.spectral_theorem
  have hinv : A⁻¹ = U * diagonal (fun i => (a i)⁻¹) * star U := by
    apply inv_eq_right_inv
    rw [hspec]
    calc
      _ = U * diagonal a * (star U * U) * diagonal (fun i => (a i)⁻¹) * star U := by
        simp only [Matrix.mul_assoc]
      _ = _ := by
        rw [hU, mul_one, Matrix.mul_assoc U, diagonal_mul_diagonal]
        have ha : (fun i => a i * (a i)⁻¹) = fun _ => 1 := by
          funext i
          exact mul_inv_cancel₀ (hA.eigenvalues_pos i).ne'
        rw [ha, diagonal_one, mul_one, hU']
  rw [hinv, Matrix.trace_mul_cycle, hU, Matrix.one_mul, Matrix.trace_diagonal]

theorem retainedFourMoment_comparison (h : ℝ) (hh : 0 ≤ h) :
    ∃ c C : ℝ≥0∞, 0 < c ∧ C < ∞ ∧
      ∀ A : Matrix R R ℝ, A.PosDef →
        c * (retainedFourMoment A 0 * ENNReal.ofReal ((1 + A⁻¹.trace) ^ h)) ≤
          retainedFourMoment A h ∧
        retainedFourMoment A h ≤
          C * (retainedFourMoment A 0 * ENNReal.ofReal ((1 + A⁻¹.trace) ^ h)) := by
  let Z := retainedScaledMoment 0 (0 : Fin 4 × R → ℝ)
  obtain ⟨zlo, zhi, zlo_pos, zhi_fin, hz⟩ :=
    retainedScaledMoment_comparison (D := Fin 4 × R) 0 (by norm_num)
  obtain ⟨hzlo, hzhi⟩ := hz 0 (fun _ => by norm_num)
  have hZ0 : 0 < Z := zlo_pos.trans_le (by simpa [Z] using hzlo)
  have hZtop : Z < ∞ := (show Z ≤ zhi by simpa [Z] using hzhi).trans_lt zhi_fin
  obtain ⟨c, C, hc, hC, hcmp⟩ := retainedScaledMoment_comparison (D := Fin 4 × R) h hh
  let B := ENNReal.ofReal ((4 : ℝ) ^ h)
  refine ⟨c * Z⁻¹, C * B * Z⁻¹, ENNReal.mul_pos hc.ne' (by simp [hZtop.ne]),
    ENNReal.mul_lt_top (ENNReal.mul_lt_top hC ENNReal.ofReal_lt_top)
      (ENNReal.inv_lt_top.mpr hZ0), ?_⟩
  intro A hA
  let a := fun i : Fin 4 × R => (hA.1.eigenvalues i.2)⁻¹
  have ha (i : Fin 4 × R) : 0 ≤ a i := (inv_pos.mpr (hA.eigenvalues_pos i.2)).le
  obtain ⟨hlo, hhi⟩ := hcmp a ha
  obtain ⟨d, hd0, hdt, hd⟩ := retainedFourMoment_scale A hA
  have hZ : d * retainedFourMoment A 0 = Z := by
    rw [hd]
    simp [Z, retainedScaledMoment]
  have hsum : (∑ i, a i) = 4 * A⁻¹.trace := by
    rw [Fintype.sum_prod_type, retainedInverse_trace A hA]
    simp [a, Finset.sum_const, nsmul_eq_mul]
  have hT : 0 ≤ A⁻¹.trace := by
    rw [retainedInverse_trace A hA]
    exact Finset.sum_nonneg (fun i _ => (inv_pos.mpr (hA.eigenvalues_pos i)).le)
  let W := ENNReal.ofReal ((1 + A⁻¹.trace) ^ h)
  have hWlo : W ≤ ENNReal.ofReal ((1 + ∑ i, a i) ^ h) := by
    apply ENNReal.ofReal_le_ofReal
    apply Real.rpow_le_rpow (by positivity) _ hh
    rw [hsum]
    linarith
  have hWhi : ENNReal.ofReal ((1 + ∑ i, a i) ^ h) ≤ B * W := by
    dsimp [B, W]
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _),
      ← Real.mul_rpow (by norm_num) (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    apply Real.rpow_le_rpow (add_nonneg zero_le_one (Finset.sum_nonneg fun i _ => ha i)) _ hh
    rw [hsum]
    linarith
  constructor
  · apply (ENNReal.mul_le_mul_left hd0 hdt).mp
    rw [hd]
    calc
      _ = c * (Z⁻¹ * (d * retainedFourMoment A 0)) * W := by ac_rfl
      _ = c * W := by rw [hZ, ENNReal.inv_mul_cancel hZ0.ne' hZtop.ne, mul_one]
      _ ≤ _ := (mul_le_mul_left' hWlo _).trans hlo
  · apply (ENNReal.mul_le_mul_left hd0 hdt).mp
    rw [hd]
    calc
      _ ≤ C * (B * W) := hhi.trans (mul_le_mul_left' hWhi _)
      _ = C * B * (Z⁻¹ * (d * retainedFourMoment A 0)) * W := by
        rw [hZ, ENNReal.inv_mul_cancel hZ0.ne' hZtop.ne, mul_one, mul_assoc]
      _ = _ := by ac_rfl

variable {E S L : Type*} [Fintype E] [Fintype S] [Fintype L]
variable [DecidableEq E] [DecidableEq S] [DecidableEq L]

/-- The unnormalized weighted mass in the physical four Cartesian loop slots. -/
def retainedK (h : ℝ) (t : E → ℝ) (C : Matrix S E ℝ) (J : Matrix L E ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (retainedSeamDensityAtZero (retainedGram t C) /
    (2 * Real.pi) ^ (4 * Fintype.card L)) * retainedFourMoment (retainedSchur t C J) h

omit [DecidableEq L] in
theorem retainedK_zero (t : E → ℝ) (C : Matrix S E ℝ) (J : Matrix L E ℝ) :
    retainedK 0 t C J = retainedK0 t C J := by
  simp [retainedK, retainedFourMoment, retainedK0]

/-- Weighted Gaussian mass compared with the exact unweighted sewn mass
times the real power of one plus the sum of score deletion cofactors. -/
theorem retainedK_comparison (h : ℝ) (hh : 0 ≤ h) :
    ∃ c C' : ℝ≥0∞, 0 < c ∧ C' < ∞ ∧
      ∀ (t : E → ℝ), (∀ e, 0 < t e) →
        ∀ (C : Matrix S E ℝ) (J : Matrix L E ℝ), C.rank = Fintype.card S →
          (fromRows C J).rank = Fintype.card S + Fintype.card L →
          c * (retainedK0 t C J * ENNReal.ofReal ((1 +
            ∑ j : L, (retainedGram t (retainedDeleteScore C J j)).det /
              (retainedGram t (fromRows C J)).det) ^ h)) ≤ retainedK h t C J ∧
          retainedK h t C J ≤ C' * (retainedK0 t C J * ENNReal.ofReal ((1 +
            ∑ j : L, (retainedGram t (retainedDeleteScore C J j)).det /
              (retainedGram t (fromRows C J)).det) ^ h)) := by
  obtain ⟨c, C', hc, hC', hcomp⟩ := retainedFourMoment_comparison (R := L) h hh
  refine ⟨c, C', hc, hC', ?_⟩
  intro t ht C J hC hM
  have hQ := (retainedSchur_posDef_iff_rank t ht C J hC).mpr hM
  obtain ⟨hlo, hhi⟩ := hcomp (retainedSchur t C J) hQ
  rw [retainedSchur_trace_inv_cofactor t ht C J hC hM] at hlo hhi
  rw [← retainedK_zero]
  unfold retainedK
  let p := ENNReal.ofReal (retainedSeamDensityAtZero (retainedGram t C) /
    (2 * Real.pi) ^ (4 * Fintype.card L))
  exact ⟨by simpa only [p, mul_assoc, mul_comm, mul_left_comm] using mul_le_mul_left' hlo p,
    by simpa only [p, mul_assoc, mul_comm, mul_left_comm] using mul_le_mul_left' hhi p⟩

omit [DecidableEq L] in
theorem retainedK_integral_sewn (h : ℝ) (t : E → ℝ) (ht : ∀ e, 0 < t e)
    (C : Matrix S E ℝ) (J : Matrix L E ℝ) (hC : C.rank = Fintype.card S) :
    retainedK h t C J = ∫⁻ v : Fin 4 → EuclideanSpace ℝ L, ENNReal.ofReal
      ((1 + ∑ μ, ‖v μ‖ ^ 2) ^ h * ‖retainedSewnFourier t C J v‖ /
        (2 * Real.pi) ^ (4 * Fintype.card L)) := by
  have hA := (retainedGram_posDef_iff_rank t ht C).mpr hC
  have hs : 0 ≤ retainedSeamDensityAtZero (retainedGram t C) := by
    rw [retainedSeamDensityAtZero_formula _ hA]
    positivity
  rw [retainedK, retainedFourMoment, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_congr
  intro v
  rw [retainedSewnFourier_eq t ht C J hC, Complex.norm_real,
    Real.norm_of_nonneg (mul_nonneg hs (retainedFourGaussian_pos _ _).le),
    ← ENNReal.ofReal_mul (div_nonneg hs (by positivity))]
  congr 1
  ring

omit [DecidableEq L] in
theorem retainedK0_le_retainedK (h : ℝ) (hh : 0 ≤ h) (t : E → ℝ)
    (C : Matrix S E ℝ) (J : Matrix L E ℝ) :
    retainedK0 t C J ≤ retainedK h t C J := by
  unfold retainedK retainedK0 retainedFourMoment
  apply mul_le_mul_left'
  apply lintegral_mono
  intro v
  have hbase : 1 ≤ 1 + ∑ μ, ‖v μ‖ ^ 2 := by
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hw : 1 ≤ (1 + ∑ μ, ‖v μ‖ ^ 2) ^ h :=
    Real.one_le_rpow hbase hh
  exact ENNReal.ofReal_le_ofReal
    (le_mul_of_one_le_left (retainedFourGaussian_pos _ _).le hw)

theorem retainedK_eq_top_of_rank_defect (h : ℝ) (hh : 0 ≤ h) (t : E → ℝ) (ht : ∀ e, 0 < t e)
    (C : Matrix S E ℝ) (J : Matrix L E ℝ) (hC : C.rank = Fintype.card S)
    (hM : (fromRows C J).rank ≠ Fintype.card S + Fintype.card L) :
    retainedK h t C J = ∞ := by
  apply top_unique
  rw [← retainedK0_eq_top t ht C J hC hM]
  exact retainedK0_le_retainedK h hh t C J

end UV
