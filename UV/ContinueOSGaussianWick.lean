import UV.ContinueOSGaussianStein
import UV.RevisionOSMoments

/-! Isserlis moments for jointly linear observations of a possibly
singular finite Gaussian. The contraction recursion derives from the
Stein identity of the joint coordinate law. -/

noncomputable section
open MeasureTheory MvPolynomial

namespace UV.MarkedPhoton

variable {ι α : Type*} [Fintype ι] [DecidableEq ι]

private def osLinearPoly (a : ι → ℝ) : MvPolynomial ι ℝ := ∑ i, C (a i)*X i
private def osCovPair (v a b : ι → ℝ) : ℝ := ∑ i, a i*v i*b i
private def osWeightedDeriv (v a : ι → ℝ) (p : MvPolynomial ι ℝ) : MvPolynomial ι ℝ :=
  ∑ i, C (a i*v i)*pderiv i p

private theorem osWeightedDeriv_linear (v a b : ι → ℝ) :
    osWeightedDeriv v a (osLinearPoly b) = C (osCovPair v a b) := by
  have h (i : ι) : pderiv i (osLinearPoly b) = C (b i) := by
    simp [osLinearPoly,Pi.single_apply,mul_ite]
  simp only [osWeightedDeriv,h,osCovPair,map_sum,map_mul]

omit [DecidableEq ι] in
private theorem osWeightedDeriv_leibniz (v a : ι → ℝ) (p q : MvPolynomial ι ℝ) :
    osWeightedDeriv v a (p*q) = osWeightedDeriv v a p*q + p*osWeightedDeriv v a q := by
  simp only [osWeightedDeriv,pderiv_mul,Finset.sum_mul,Finset.mul_sum,←Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

private def osPolyMean (v : ι → ℝ) : MvPolynomial ι ℝ →ₗ[ℝ] ℝ where
  toFun p := ∫ z, eval z p ∂coordinateLaw v
  map_add' p q := by simp only [map_add]; exact integral_add (osPolynomial_integrable v p) (osPolynomial_integrable v q)
  map_smul' t p := by simp [MvPolynomial.smul_eq_C_mul,integral_const_mul]

omit [DecidableEq ι] in
private theorem osPolyMean_C_mul (v : ι → ℝ) (a : ℝ) (p : MvPolynomial ι ℝ) :
    osPolyMean v (C a*p) = a * osPolyMean v p := by
  rw [←MvPolynomial.smul_eq_C_mul,map_smul,smul_eq_mul]

private theorem osPolyMean_stein (v : ι → ℝ) (hv : ∀ i, 0 ≤ v i) (a : ι → ℝ) (p : MvPolynomial ι ℝ) :
    osPolyMean v (osLinearPoly a*p) = osPolyMean v (osWeightedDeriv v a p) := by
  simp only [osLinearPoly,osWeightedDeriv,Finset.sum_mul,map_sum,mul_assoc,osPolyMean_C_mul]
  apply Finset.sum_congr rfl
  intro i _
  change a i * (∫ z, eval z (X i * p) ∂coordinateLaw v) = _
  rw [osPolynomial_stein v hv]
  rfl

private def osFieldPoly (w : α → ι → ℝ) (l : List α) : MvPolynomial ι ℝ :=
  (l.map (fun b => osLinearPoly (w b))).prod

omit [DecidableEq ι] in
private theorem osFieldPoly_cons (w : α → ι → ℝ) (a : α) (l : List α) :
    osFieldPoly w (a::l) = osLinearPoly (w a) * osFieldPoly w l := rfl

private theorem osWeightedDeriv_list (v a : ι → ℝ) (w : α → ι → ℝ) (l : List α) :
    osWeightedDeriv v a (osFieldPoly w l) =
    ((l.zipIdx 0).map fun (b,k) => C (osCovPair v a (w b))*osFieldPoly w (l.eraseIdx k)).sum := by
  induction l with
  | nil => simp [osFieldPoly,osWeightedDeriv]
  | cons b l ih =>
    rw [osFieldPoly_cons,osWeightedDeriv_leibniz,osWeightedDeriv_linear,ih,
      List.zipIdx_cons',List.map_cons,List.sum_cons,List.map_map]
    congr 1
    rw [←List.sum_map_mul_left]
    congr 1
    apply List.map_congr_left
    rintro ⟨j,k⟩ _
    change osLinearPoly (w b) * (C (osCovPair v a (w j)) * osFieldPoly w (l.eraseIdx k)) =
      C (osCovPair v a (w j))*osFieldPoly w ((b::l).eraseIdx (k+1))
    rw [List.eraseIdx_cons_succ,osFieldPoly_cons]
    ring

private instance osSourceProbability (v : ℝ) : IsProbabilityMeasure (sourceGaussian v) := by
  rw [sourceGaussian,UV.ContinueCurvatureGaussian.sourceGaussianBase_eq_gaussianReal]
  exact Measure.isProbabilityMeasure_map (by fun_prop)

private theorem osPolyMean_wick (v : ι → ℝ) (hv : ∀ i, 0 ≤ v i) (w : α → ι → ℝ)
    (n : ℕ) (l : List α) (hl : l.length ≤ 2*n) :
    osPolyMean v (osFieldPoly w l) = osWickMoment (fun i j => osCovPair v (w i) (w j)) n l := by
  haveI : IsProbabilityMeasure (coordinateLaw v) :=
    inferInstanceAs (IsProbabilityMeasure (Measure.pi fun i => sourceGaussian (v i)))
  induction n generalizing l with
  | zero =>
    have he : l = [] := List.eq_nil_of_length_eq_zero (by simpa using hl)
    subst l; simp [osPolyMean,osFieldPoly,osWickMoment]
  | succ n ih =>
    cases l with
    | nil => simp [osPolyMean,osFieldPoly,osWickMoment]
    | cons a l =>
      rw [osFieldPoly_cons,osPolyMean_stein v hv,osWeightedDeriv_list,
        map_list_sum,List.map_map,osWickMoment]
      apply congrArg List.sum
      apply List.map_congr_left
      rintro ⟨b,k⟩ hk
      obtain ⟨_,hb,_⟩ := List.mem_zipIdx hk
      have hlen : (l.eraseIdx k).length ≤ 2*n := by
        rw [List.length_eraseIdx_of_lt (by simpa using hb)]
        simp only [List.length_cons] at hl
        omega
      exact (osPolyMean_C_mul v _ _).trans (congrArg (_ * ·) (ih _ hlen))

/-- All finite products of linear probes of the same Gaussian obey the
Wick recurrence with their complete, generally nondiagonal covariance. -/
theorem osLinearGaussian_wick (v : ι → ℝ) (hv : ∀ i, 0 ≤ v i) (w : α → ι → ℝ) :
    OSWickMoments (coordinateLaw v) (fun b z => ∑ i, w b i*z i) (fun a b => ∑ i, w a i*v i*w b i) := by
  have he (l : List α) (z : ι → ℝ) :
      osMonomial (fun b z => ∑ i, w b i*z i) l z = eval z (osFieldPoly w l) := by
    simp [osMonomial,osFieldPoly,osLinearPoly,map_list_prod,List.map_map,Function.comp_def]
  constructor
  · intro l
    rw [funext (he l)]
    exact osPolynomial_integrable v _
  · intro n l hl
    simp_rw [he]
    exact osPolyMean_wick v hv w n l hl

end UV.MarkedPhoton
