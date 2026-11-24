import UV.AdvanceNetworkRouted
import UV.ContinueSewnFlagOrdered

/-! Fourier integration of a shifted Gaussian with the literal
independent loop coordinates and original four-dimensional routes. -/

noncomputable section
open Real MeasureTheory Matrix
open scoped BigOperators Matrix Kronecker RealInnerProductSpace
namespace UV.SewnFlags

def routedPhase {L : ℕ} (d k : EuclideanSpace ℝ (Fin L × Fin 4)) : ℂ :=
  Complex.exp (Complex.I * (inner ℝ d k : ℂ))

theorem routedPhase_norm {L : ℕ} (d k : EuclideanSpace ℝ (Fin L × Fin 4)) :
    ‖routedPhase d k‖ = 1 := by
  rw [routedPhase,Complex.norm_exp]
  simp [Complex.mul_re]

theorem routedPhase_continuous {L : ℕ} :
    Continuous (fun p : (EuclideanSpace ℝ (Fin L × Fin 4)) × (EuclideanSpace ℝ (Fin L × Fin 4)) =>
      routedPhase p.1 p.2) := by
  unfold routedPhase
  exact Complex.continuous_exp.comp
    (continuous_const.mul (Complex.continuous_ofReal.comp (continuous_fst.inner continuous_snd)))

def routedAffineEnergy {N L : ℕ} (C : Matrix (Fin N) (Fin L) ℝ) (t : Fin N → ℝ)
    (p : Fin N → ScalarMomentum) (k : EuclideanSpace ℝ (Fin L × Fin 4)) :=
  ∑ i, t i * ‖residualRouting C i k+p i‖^2

def routedAffineWave {N L : ℕ} (C : Matrix (Fin N) (Fin L) ℝ) (t : Fin N → ℝ)
    (p : Fin N → ScalarMomentum) (d k : EuclideanSpace ℝ (Fin L × Fin 4)) : ℂ :=
  routedPhase d k * (exp (-(routedAffineEnergy C t p k)):ℂ)

private theorem four_block_mulVec {E F : Type*} [Fintype F]
    (C : Matrix E F ℝ) (k : F × Fin 4 → ℝ) (i : E) (j : Fin 4) :
    ((C ⊗ₖ (1 : Matrix (Fin 4) (Fin 4) ℝ)) *ᵥ k) (i,j) =
      (C *ᵥ fun k' => k (k',j)) i := by
  classical
  simp [Matrix.mulVec,dotProduct,Fintype.sum_prod_type,Matrix.one_apply]

/-- The complex Fourier integral exists for every real affine shift.
The shift contributes a unit phase and a nonnegative residual energy.
The remaining factor is the exact determinant and inverse Gram form. -/
theorem routed_affine_wave_bound {N L : ℕ} (C : Matrix (Fin N) (Fin L) ℝ)
    (hC : Function.Injective C.mulVec) (t : Fin N → ℝ) (ht : ∀ i, 0 < t i)
    (p : Fin N → ScalarMomentum) (d : EuclideanSpace ℝ (Fin L × Fin 4)) :
    Integrable (routedAffineWave C t p d) ∧
      ‖∫ k, routedAffineWave C t p d k‖ ≤
        π^(L*2) * ((residualGram C t).det^2)⁻¹ * exp (-(routedInverseWeight C t d)/4) := by
  let I₄ : Matrix (Fin 4) (Fin 4) ℝ := 1
  let Q := diagonal (fun i : Fin N => 4*t i) ⊗ₖ I₄
  let B := C ⊗ₖ I₄
  let M := residualGram C t
  let P := networkRoutedPrecision Q B
  let b := fun z : Fin N × Fin 4 => p z.1 z.2
  have hQeq : Q = diagonal (fun z : Fin N × Fin 4 => 4*t z.1) := by
    ext ⟨i,j⟩ ⟨l,r⟩
    by_cases h₁ : i=l <;> by_cases h₂ : j=r <;>
      simp [Q,I₄,h₁,h₂]
  have hQ : Q.PosDef := by
    rw [hQeq]
    exact Matrix.PosDef.diagonal (fun z => mul_pos (by norm_num) (ht z.1))
  have hB : Function.Injective B.mulVec := by
    intro x y h
    have hc (r : Fin 4) : (fun i => x (i,r)) = (fun i => y (i,r)) := by
      apply hC
      funext i
      simpa only [B,I₄,four_block_mulVec] using congrFun h (i,r)
    funext z
    exact congrFun (hc z.2) z.1
  have hP : P.PosDef := networkRoutedPrecision_posDef hQ hB
  have hM : M.PosDef := by
    have h : M = Cᴴ * diagonal t * C := by unfold M residualGram; rw [conjTranspose_eq_transpose_of_trivial]; congr!
    rw [h]
    exact (Matrix.PosDef.diagonal ht).conjTranspose_mul_mul_same hC
  have hPt : P = (4:ℝ) • (M ⊗ₖ I₄) := by
    unfold P networkRoutedPrecision
    have hBt : B.transpose = C.transpose ⊗ₖ I₄ := by
      ext ⟨i,r⟩ ⟨j,s⟩
      simp [B,I₄,Matrix.one_apply,eq_comm]
    have hdt : diagonal (fun i : Fin N => 4*t i) = (4:ℝ) • diagonal t := by
      ext i j
      by_cases h : i=j <;> simp [h]
    dsimp only [Q]
    rw [hBt,← mul_kronecker_mul,← mul_kronecker_mul,
      show I₄*I₄ = I₄ from one_mul _,hdt,Matrix.mul_smul,Matrix.smul_mul,Matrix.smul_kronecker]
    simp only [I₄, one_mul]
    unfold M residualGram
    congr!
  have hInv : P⁻¹ = (1/4:ℝ) • (M⁻¹ ⊗ₖ I₄) := by
    apply Matrix.inv_eq_right_inv
    rw [hPt,smul_mul_assoc,mul_smul_comm,← mul_kronecker_mul,
      Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hM.det_pos.ne'),
      show I₄*I₄ = I₄ from one_mul _,show I₄ = 1 from rfl,one_kronecker_one,smul_smul]
    norm_num
  have hInverse : d.ofLp ⬝ᵥ (P⁻¹ *ᵥ d.ofLp) = routedInverseWeight C t d/4 := by
    have he : d.ofLp ⬝ᵥ ((M⁻¹ ⊗ₖ I₄) *ᵥ d.ofLp) = routedInverseWeight C t d := by
      unfold routedInverseWeight
      simp only [dotProduct,Fintype.sum_prod_type,I₄,four_block_mulVec]
      rw [Finset.sum_comm]
      rfl
    rw [hInv,Matrix.smul_mulVec,dotProduct_smul,smul_eq_mul,he]
    ring
  have hNormalizer : sqrt ((4*π)^Fintype.card (Fin L × Fin 4)/P.det) =
      π^(L*2)*(M.det^2)⁻¹ := by
    rw [hPt,Matrix.det_smul,show (M ⊗ₖ I₄).det = M.det^4 from four_dimensional_routing_det _,
      mul_pow,mul_div_mul_left _ _ (by positivity)]
    have hd : Fintype.card (Fin L × Fin 4) = (L*2)*2 := by
      simp only [Fintype.card_prod,Fintype.card_fin]
      omega
    rw [hd,pow_mul,show M.det^4 = (M.det^2)^2 by rw [← pow_mul],
      ← div_pow,sqrt_sq (by positivity),div_eq_mul_inv]
  have hEnergy (k : EuclideanSpace ℝ (Fin L × Fin 4)) :
      ((B *ᵥ k.ofLp+b) ⬝ᵥ (Q *ᵥ (B *ᵥ k.ofLp+b)))/4 = routedAffineEnergy C t p k := by
    rw [hQeq,div_eq_iff (by norm_num : (4:ℝ) ≠ 0)]
    simp only [dotProduct,Matrix.mulVec_diagonal,Fintype.sum_prod_type,Pi.add_apply,
      B,I₄,b,four_block_mulVec,routedAffineEnergy,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    simp only [EuclideanSpace.norm_sq_eq,Finset.mul_sum,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    simp only [PiLp.add_apply,residualRouting_component,Real.norm_eq_abs,sq_abs]
    change (((C *ᵥ fun k' => k (k',j)) i+p i j) *
      (4*t i*((C *ᵥ fun k' => k (k',j)) i+p i j))) =
      t i * (((C *ᵥ fun k' => k (k',j)) i+p i j)^2)*4
    ring
  let c : EuclideanSpace ℝ (Fin L × Fin 4) := WithLp.toLp 2 (networkRoutedCenter Q B b)
  let r := networkRoutedResidual Q B b
  let Z := routedPhase d (-c) * (exp (-(r ⬝ᵥ (Q *ᵥ r))/4):ℂ)
  have hZ : ‖Z‖ ≤ 1 := by
    unfold Z
    rw [norm_mul,routedPhase_norm,one_mul,Complex.norm_real,Real.norm_of_nonneg (exp_pos _).le]
    exact exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (networkRoutedResidual_nonneg (B := B) hQ b)) (by norm_num))
  have hFactor (k : EuclideanSpace ℝ (Fin L × Fin 4)) :
      routedAffineWave C t p d k = Z*networkSPDWave P d (k+c) := by
    have hE : routedAffineEnergy C t p k =
        ((k+c).ofLp ⬝ᵥ (P *ᵥ (k+c).ofLp))/4 + (r ⬝ᵥ (Q *ᵥ r))/4 := by
      rw [← hEnergy k,networkRoutedQuadratic_complete_square hQ hB,add_div]
      rfl
    have hp : routedPhase d k = routedPhase d (-c)*routedPhase d (k+c) := by
      unfold routedPhase
      rw [← Complex.exp_add]
      congr 1
      rw [inner_neg_right,inner_add_right]
      push_cast
      ring
    unfold routedAffineWave Z networkSPDWave
    rw [hE,neg_add,exp_add,Complex.ofReal_mul,hp]
    unfold routedPhase
    ring_nf
  have hI : Integrable (routedAffineWave C t p d) := by
    rw [funext hFactor]
    have hAdd : MeasurePreserving (fun k : EuclideanSpace ℝ (Fin L × Fin 4) => k+c) volume volume :=
      measurePreserving_add_right volume c
    have hE : MeasurableEmbedding (fun k : EuclideanSpace ℝ (Fin L × Fin 4) => k+c) :=
      (Homeomorph.addRight c).measurableEmbedding
    exact ((hAdd.integrable_comp_emb hE).2 (networkSPDWave_integrable P hP d)).const_mul Z
  refine ⟨hI,?_⟩
  simp_rw [hFactor]
  rw [integral_const_mul,integral_add_right_eq_self,networkSPDWave_integral P hP d,hNormalizer,hInverse,
    norm_mul,Complex.norm_real,Real.norm_of_nonneg (mul_nonneg
      (mul_nonneg (pow_nonneg pi_pos.le _) (inv_nonneg.mpr (sq_nonneg _))) (exp_pos _).le)]
  simp only [neg_div, M]
  exact mul_le_of_le_one_left (mul_nonneg
    (mul_nonneg (pow_nonneg pi_pos.le _) (inv_nonneg.mpr (sq_nonneg _))) (exp_pos _).le) hZ

end UV.SewnFlags
