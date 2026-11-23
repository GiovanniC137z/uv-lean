import UV.ContinuationSectorPlane
import Mathlib.Analysis.Matrix.Order
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! The six independent components of the Abelian curvature on the
four-torus. Matrices represent the complex Fourier covariance of a real
field. The mode p=0 is excluded from the photon sum. -/

noncomputable section
open scoped Matrix ComplexConjugate ComplexOrder MatrixOrder
open MeasureTheory

namespace UV

abbrev CurvatureMode := {p : Fin 4 → ℤ // p ≠ 0}

def contactPhotonVector (p : CurvatureMode) (j : Fin 4) : ℂ := p.val j

def contactModeSquare (p : CurvatureMode) : ℝ := ∑ i, (p.val i:ℝ)^2

/-- Matrix of the six exterior components (01),(02),(03),(12),(13),(23).
The two Fourier derivatives in a covariance cancel the factors i and −i. -/
def contactExterior (p : CurvatureMode) : Matrix (Fin 6) (Fin 4) ℂ :=
  let k := contactPhotonVector p
  !![-k 1,k 0,0,0; -k 2,0,k 0,0; -k 3,0,0,k 0;
     0,-k 2,k 1,0; 0,-k 3,0,k 1; 0,0,-k 3,k 2]

def contactLongitudinal (p : CurvatureMode) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => contactPhotonVector p i * contactPhotonVector p j

set_option maxHeartbeats 1500000 in
theorem contact_exterior_gram (p : CurvatureMode) :
    (contactExterior p)ᴴ * contactExterior p =
      (contactModeSquare p:ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) - contactLongitudinal p := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply,contactModeSquare,contactLongitudinal,contactExterior,contactPhotonVector,
      Matrix.conjTranspose_apply,Fin.sum_univ_succ] <;> ring

def contactCurvatureCov (p : CurvatureMode) (D : Matrix (Fin 4) (Fin 4) ℂ) :=
  contactExterior p * D * (contactExterior p)ᴴ

theorem contact_curvature_trace (p : CurvatureMode) (D : Matrix (Fin 4) (Fin 4) ℂ)
    (hT : D *ᵥ contactPhotonVector p = 0) :
    (contactCurvatureCov p D).trace = (contactModeSquare p:ℂ) * D.trace := by
  have h0 : D*contactLongitudinal p = 0 := by
    ext i j
    have hi := congrFun hT i
    change (∑ k, D i k * contactPhotonVector p k) = 0 at hi
    simp only [Matrix.mul_apply,contactLongitudinal,← mul_assoc,← Finset.sum_mul,hi,zero_mul,Matrix.zero_apply]
  unfold contactCurvatureCov
  rw [Matrix.trace_mul_cycle, Matrix.trace_mul_comm,contact_exterior_gram,Matrix.mul_sub,h0,sub_zero,
    Matrix.mul_smul,Matrix.mul_one,Matrix.trace_smul,smul_eq_mul]

private theorem contact_gram_entry_le_trace {n : ℕ} {C : Matrix (Fin n) (Fin n) ℂ} (hC : C.PosSemidef)
    (i j : Fin n) : ‖C i j‖ ≤ C.trace.re := by
  obtain ⟨B,rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hC.nonneg
  let q := fun i : Fin n => ∑ k, ‖B k i‖^2
  have hd (k : Fin n) : ((Bᴴ*B) k k).re = q k := by
    simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,Complex.re_sum,q,Complex.sq_norm]
    apply Finset.sum_congr rfl
    intro t _
    change ((conj (B t k)) * B t k).re = _
    rw [←Complex.normSq_eq_conj_mul_self,Complex.ofReal_re]
  have htot : (Bᴴ*B).trace.re = ∑ k, q k := by
    simp only [Matrix.trace,Matrix.diag_apply,Complex.re_sum,hd]
  have hq (i : Fin n) : q i ≤ ∑ k, q k :=
    Finset.single_le_sum (f := q) (fun k _ => Finset.sum_nonneg (fun t _ => sq_nonneg ‖B t k‖)) (Finset.mem_univ i)
  change ‖(Bᴴ*B) i j‖ ≤ (Bᴴ*B).trace.re
  rw [htot,Matrix.mul_apply]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ k, ((‖B k i‖^2+‖B k j‖^2)/2) := by
      apply Finset.sum_le_sum
      intro k _
      rw [Matrix.conjTranspose_apply,norm_mul,norm_star]
      nlinarith [sq_nonneg (‖B k i‖-‖B k j‖)]
    _ = (q i + q j)/2 := by rw [←Finset.sum_div,Finset.sum_add_distrib]
    _ ≤ _ := by linarith [hq i,hq j]

theorem contact_curvature_line_bound (p : CurvatureMode) {D : Matrix (Fin 4) (Fin 4) ℂ}
    (hD : D.PosSemidef) (hT : D *ᵥ contactPhotonVector p = 0) (i j : Fin 6) :
    ‖contactCurvatureCov p D i j‖ ≤ contactModeSquare p * D.trace.re := by
  have hc := contact_gram_entry_le_trace (hD.mul_mul_conjTranspose_same (contactExterior p)) i j
  change _ ≤ (contactCurvatureCov p D).trace.re at hc
  simpa [contact_curvature_trace p D hT] using hc

/-- The powers and fixed Fourier probes of a local polynomial yield finite
sums of assignments of tensor components. The bounded factor enforces
all vertex conservation conditions and carries the external coefficients. -/
theorem contact_finite_graph {I : ℕ} (D : CurvatureMode → Matrix (Fin 4) (Fin 4) ℂ)
    (hD : ∀ p, (D p).PosSemidef) (hT : ∀ p, D p *ᵥ contactPhotonVector p = 0)
    (hb : Summable (fun p => contactModeSquare p * (D p).trace.re))
    (i j : Fin I → Fin 6) (c : (Fin I → CurvatureMode) → ℂ) (C : ℝ)
    (hc : ∀ q, ‖c q‖ ≤ C) :
    let μ := Measure.pi (fun _ : Fin I => (Measure.count : Measure CurvatureMode))
    let F := fun q : Fin I → CurvatureMode => c q * ∏ e,
      contactCurvatureCov (q e) (D (q e)) (i e) (j e)
    Integrable F μ ∧ (∫ q, ‖F q‖ ∂μ) ≤ C * (∑' p, contactModeSquare p * (D p).trace.re)^I := by
  let b := fun p => contactModeSquare p*(D p).trace.re
  let μ := Measure.pi (fun _ : Fin I => (Measure.count : Measure CurvatureMode))
  have hb0 (p) : 0 ≤ b p := by
    apply mul_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) (Complex.nonneg_iff.mp (hD p).trace_nonneg).1
  have hi : Integrable b Measure.count := integrable_count_iff.mpr (by simpa only [Real.norm_eq_abs,abs_of_nonneg (hb0 _)] using hb)
  have hP : Integrable (fun q : Fin I → CurvatureMode => C * ∏ e, b (q e)) μ :=
    (Integrable.fintype_prod (fun _ => hi)).const_mul C
  have hbd (q : Fin I → CurvatureMode) : ‖c q * ∏ e, contactCurvatureCov (q e) (D (q e)) (i e) (j e)‖ ≤
      C * ∏ e, b (q e) := by
    rw [norm_mul,norm_prod]
    apply mul_le_mul (hc q) _ (Finset.prod_nonneg fun _ _ => norm_nonneg _) ((norm_nonneg _).trans (hc q))
    exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun e _ => contact_curvature_line_bound (q e) (hD _) (hT _) _ _)
  have hF := hP.mono' (f := fun q : Fin I → CurvatureMode => c q *
      ∏ e, contactCurvatureCov (q e) (D (q e)) (i e) (j e)) (measurable_of_countable _).aestronglyMeasurable (ae_of_all _ hbd)
  refine ⟨hF,(integral_mono hF.norm hP hbd).trans_eq ?_⟩
  rw [integral_const_mul,integral_fintype_prod_eq_prod (fun _ : Fin I => b),integral_countable' hi]
  simp [b]

/-- The homogeneous two-field part of the local polynomial
|f+uG|^(2N), for |f|=1, a=(f,G) and b=|G|². -/
theorem contact_polynomial_two_internal (a b : ℝ) (N : ℕ) :
    let P : Polynomial ℝ := 1 + Polynomial.C (2*a)*Polynomial.X + Polynomial.C b*Polynomial.X^2
    (P^N).coeff 2 = N*b + 2*(N:ℝ)*(N-1:ℝ)*a^2 := by
  let P : Polynomial ℝ := 1 + Polynomial.C (2*a)*Polynomial.X + Polynomial.C b*Polynomial.X^2
  suffices (P^N).coeff 0 = 1 ∧ (P^N).coeff 1 = 2*N*a ∧
      (P^N).coeff 2 = N*b+2*(N:ℝ)*(N-1:ℝ)*a^2 from this.2.2
  induction N with
  | zero => simp [Polynomial.coeff_one]
  | succ n ih =>
    obtain ⟨h0,h1,h2⟩ := ih
    rw [pow_succ]
    have eqP : P^n*P = P^n + (P^n*Polynomial.C (2*a))*Polynomial.X +
        (P^n*Polynomial.C b)*Polynomial.X^2 := by simp [P,mul_add,mul_assoc]
    rw [eqP]
    simp [Polynomial.coeff_mul_X_pow',Polynomial.coeff_mul_C,h0,h1,h2,← mul_assoc]
    constructor <;> ring

/-- A two-Fourier-mode real transverse probe. This is dA for spatial
potential components sin(x₀) and −cos(x₀), and has constant unit norm. -/
def contactRotatingProbe (u : ℝ) : Fin 6 → ℂ :=
  ![(Real.cos (2*Real.pi*u):ℂ),(Real.sin (2*Real.pi*u):ℂ),0,0,0,0]

theorem contact_rotating_probe_unit (u : ℝ) : ∑ i, ‖contactRotatingProbe u i‖^2 = 1 := by
  simp only [contactRotatingProbe,Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,
    Complex.norm_real,Real.norm_eq_abs,sq_abs,norm_zero,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,
    zero_pow,Finset.univ_eq_empty,Finset.sum_empty,add_zero]
  exact Real.cos_sq_add_sin_sq _

/-- The whole Wick contact in one internal line, with the physical
transverse-mode curvature tensor C. The polynomial coefficient above
gives N tr C + 2N(N−1)f*Cf. -/
def contactProbeMode (N : ℕ) (p : CurvatureMode) (D : Matrix (Fin 4) (Fin 4) ℂ) : ℝ :=
  let C := contactCurvatureCov p D
  ∫ u in (0:ℝ)..1, (N:ℝ)*C.trace.re + 2*(N:ℝ)*(N-1:ℝ)*
    (star (contactRotatingProbe u) ⬝ᵥ (C *ᵥ contactRotatingProbe u)).re

private theorem contact_probe_cont (i : Fin 6) : Continuous (fun u => contactRotatingProbe u i) := by
  fin_cases i <;> simp [contactRotatingProbe] <;> fun_prop

private theorem contact_probe_quad_cont (C : Matrix (Fin 6) (Fin 6) ℂ) :
    Continuous (fun u => (star (contactRotatingProbe u) ⬝ᵥ (C *ᵥ contactRotatingProbe u)).re) := by
  unfold Matrix.mulVec dotProduct
  apply Complex.continuous_re.comp
  apply continuous_finset_sum
  intro i _
  exact (contact_probe_cont i).star.mul (continuous_finset_sum _ (fun j _ => continuous_const.mul (contact_probe_cont j)))

theorem contact_probe_mode_lower (N : ℕ) (hN : 2 ≤ N) (p : CurvatureMode)
    {D : Matrix (Fin 4) (Fin 4) ℂ} (hD : D.PosSemidef) (hT : D *ᵥ contactPhotonVector p = 0) :
    (N:ℝ)*(contactModeSquare p*D.trace.re) ≤ contactProbeMode N p D := by
  let C := contactCurvatureCov p D
  have hC : C.PosSemidef := hD.mul_mul_conjTranspose_same _
  have ht : C.trace.re = contactModeSquare p * D.trace.re := by
    simp [C, contact_curvature_trace p D hT]
  have hnr : (1:ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hpos : 0 ≤ 2*(N:ℝ)*(N-1:ℝ) := mul_nonneg (by positivity) (sub_nonneg.mpr hnr)
  have hcont := (continuous_const (y := (N:ℝ)*C.trace.re)).add
    (continuous_const (y := 2*(N:ℝ)*(N-1:ℝ)) |>.mul (contact_probe_quad_cont C))
  calc
    _ = ∫ _ in (0:ℝ)..1, (N:ℝ)*C.trace.re := by simp [ht]
    _ ≤ _ := intervalIntegral.integral_mono_on zero_le_one (continuous_const.intervalIntegrable _ _)
      (hcont.intervalIntegrable _ _) (fun u _ => le_add_of_nonneg_right (mul_nonneg hpos (hC.re_dotProduct_nonneg _)))

private theorem contact_probe_coord_le (u : ℝ) (i : Fin 6) : ‖contactRotatingProbe u i‖ ≤ 1 := by
  have h := Finset.single_le_sum (s := Finset.univ) (f := fun j : Fin 6 => ‖contactRotatingProbe u j‖^2)
    (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  rw [contact_rotating_probe_unit] at h
  nlinarith [norm_nonneg (contactRotatingProbe u i)]

private theorem contact_quad_upper {C : Matrix (Fin 6) (Fin 6) ℂ} (hC : C.PosSemidef) (u : ℝ) :
    (star (contactRotatingProbe u) ⬝ᵥ (C *ᵥ contactRotatingProbe u)).re ≤ 36*C.trace.re := by
  let f := contactRotatingProbe u
  apply (Complex.re_le_norm _).trans
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _i : Fin 6, 6*C.trace.re := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul]
      change ‖star (f i)‖ * ‖∑ j, C i j*f j‖ ≤ _
      rw [norm_star]
      apply (mul_le_mul_of_nonneg_right (contact_probe_coord_le _ _) (norm_nonneg _)).trans
      rw [one_mul]
      apply (norm_sum_le _ _).trans
      calc
        _ ≤ ∑ _j : Fin 6, C.trace.re := by
          apply Finset.sum_le_sum
          intro j _
          rw [norm_mul]
          exact (mul_le_mul_of_nonneg_left (contact_probe_coord_le _ _) (norm_nonneg _)).trans
            (by simpa only [mul_one] using contact_gram_entry_le_trace hC i j)
        _ = _ := by simp
    _ = _ := by simp; ring

theorem contact_probe_summable_iff (N : ℕ) (hN : 2 ≤ N)
    (D : CurvatureMode → Matrix (Fin 4) (Fin 4) ℂ)
    (hD : ∀ p, (D p).PosSemidef) (hT : ∀ p, D p *ᵥ contactPhotonVector p = 0) :
    Summable (fun p => contactProbeMode N p (D p)) ↔
      Summable (fun p => contactModeSquare p * (D p).trace.re) := by
  let b := fun p => contactModeSquare p*(D p).trace.re
  have hb (p) : 0 ≤ b p := mul_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    (Complex.nonneg_iff.mp (hD p).trace_nonneg).1
  have hn : (1:ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hlo p := contact_probe_mode_lower N hN p (hD p) (hT p)
  constructor
  · intro hc
    apply Summable.of_nonneg_of_le hb (fun p => ?_) hc
    exact (show b p ≤ (N:ℝ)*b p by simpa only [one_mul] using mul_le_mul_of_nonneg_right hn (hb p)).trans (hlo p)
  · intro h
    let K := 2*(N:ℝ)*(N-1:ℝ)
    have hK : 0 ≤ K := mul_nonneg (by positivity) (sub_nonneg.mpr hn)
    apply Summable.of_nonneg_of_le (fun p => (mul_nonneg (by positivity) (hb p)).trans (hlo p))
      (fun p => ?_) (h.mul_left ((N:ℝ)+36*K))
    let C := contactCurvatureCov p (D p)
    have hc : C.PosSemidef := (hD p).mul_mul_conjTranspose_same _
    have he : C.trace.re = b p := by simp [b,C,contact_curvature_trace _ _ (hT p)]
    have hcont := (continuous_const (y := (N:ℝ)*C.trace.re)).add
      ((continuous_const (y := K)).mul (contact_probe_quad_cont C))
    calc
      _ ≤ ∫ _ in (0:ℝ)..1, (N:ℝ)*C.trace.re+ K*(36*C.trace.re) :=
        intervalIntegral.integral_mono_on zero_le_one (hcont.intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _)
          (fun u _ => add_le_add_left (mul_le_mul_of_nonneg_left (contact_quad_upper hc u) hK) _)
      _ = _ := by simp [he,b]; ring

/-- The two nonzero independent components of the test are actual exterior
derivatives of real periodic potentials. The other curvature components
vanish. The two potentials contain only the opposite fundamental modes. -/
theorem contact_probe_is_curvature (u : ℝ) :
    HasDerivAt (fun z : ℝ => Real.sin (2*Real.pi*z)/(2*Real.pi)) (Real.cos (2*Real.pi*u)) u ∧
    HasDerivAt (fun z : ℝ => -Real.cos (2*Real.pi*z)/(2*Real.pi)) (Real.sin (2*Real.pi*u)) u := by
  have hx := (hasDerivAt_id u).const_mul (2*Real.pi)
  have hπ : (2*Real.pi) ≠ 0 := by positivity
  constructor
  · convert hx.sin.div_const (2*Real.pi) using 1
    dsimp
    field_simp
  · convert hx.cos.neg.div_const (2*Real.pi) using 1
    dsimp
    field_simp

/-- Computing the expectation of the degree-two contraction only needs
the second moments. This applies in particular to every real Gaussian
curvature at a finite symmetric Fourier cutoff. -/
theorem contact_probe_wick {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (G : Fin 6 → Ω → ℝ)
    (hG : ∀ i j, Integrable (fun x => G i x * G j x) μ) (f : Fin 6 → ℝ) (N : ℕ) :
    let M := fun i j => ∫ x, G i x * G j x ∂μ
    (∫ x, ((1 + Polynomial.C (2*(∑ i, f i*G i x))*Polynomial.X +
      Polynomial.C (∑ i, (G i x)^2)*Polynomial.X^2 : Polynomial ℝ)^N).coeff 2 ∂μ) =
    (N:ℝ)*(∑ i, M i i) + 2*(N:ℝ)*(N-1:ℝ)*(∑ i, ∑ j, f i*f j*M i j) := by
  let M := fun i j => ∫ x, G i x * G j x ∂μ
  let W := fun i j x => (f i*f j)*(G i x*G j x)
  have hi i j : Integrable (W i j) μ := (hG i j).const_mul _
  have hg : Integrable (fun x => ∑ i, G i x*G i x) μ := integrable_finset_sum _ (fun i _ => hG i i)
  have hw i : Integrable (fun x => ∑ j, W i j x) μ := integrable_finset_sum _ (fun j _ => hi i j)
  have hh : Integrable (fun x => ∑ i, ∑ j, W i j x) μ := integrable_finset_sum _ (fun i _ => hw i)
  have hsq (x) : (∑ i, f i*G i x)^2 = ∑ i, ∑ j, W i j x := by
    rw [sq,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by dsimp [W]; ring)
  simp_rw [contact_polynomial_two_internal,hsq,pow_two]
  rw [integral_add (hg.const_mul _) (hh.const_mul _),integral_const_mul,integral_const_mul,
    integral_finset_sum _ (fun i _ => hG i i),integral_finset_sum _ (fun i _ => hw i)]
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finset_sum _ (fun j _ => hi i j)]
  exact Finset.sum_congr rfl (fun j _ => integral_const_mul _ _)

end UV
