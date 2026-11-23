import UV.ContinueRelativeSoftConstantField

/-! Tracing the bare constant-field Hessian before integrating its contact term. -/

noncomputable section

namespace UV.RelativeSoft

open UV.SectorPlane
open scoped RealInnerProductSpace BigOperators

def softBasisDirection (b : OrthonormalBasis (Fin 4) ℝ EuclideanPlaneMomentum) (i : Fin 4) :
    ConeUnitDirection :=
  ⟨b i,b.orthonormal.norm_eq_one i⟩

theorem soft_trace_in_basis (b : OrthonormalBasis (Fin 4) ℝ EuclideanPlaneMomentum)
    (A : Module.End ℝ EuclideanPlaneMomentum) :
    LinearMap.trace ℝ EuclideanPlaneMomentum A = ∑ i, inner ℝ (A (b i)) (b i) := by
  rw [LinearMap.trace_eq_matrix_trace ℝ b.toBasis,Matrix.trace]
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.diag_apply,LinearMap.toMatrix_apply,b.coe_toBasis_repr_apply,b.repr_apply_apply,real_inner_comm]
  rfl

theorem soft_chord_differential_symmetric (σ : ℝ) (k v w : EuclideanPlaneMomentum) :
    inner ℝ (softChordDifferential σ k v) w = inner ℝ v (softChordDifferential σ k w) := by
  simp only [softChordDifferential,softOuter,ContinuousLinearMap.sub_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply,ContinuousLinearMap.smulRight_apply,innerSL_apply,
    inner_sub_left,inner_sub_right,real_inner_smul_left,real_inner_smul_right,real_inner_comm v k]
  ring

theorem soft_two_vertex_trace (b : OrthonormalBasis (Fin 4) ℝ EuclideanPlaneMomentum)
    (m σ : ℝ) (k : EuclideanPlaneMomentum) :
    (∑ i, inner ℝ (softLogHessian m k (softChordDifferential σ k (b i)))
      (softChordDifferential σ k (b i))) =
      LinearMap.trace ℝ EuclideanPlaneMomentum
        ((softLogHessian m k).toLinearMap*((softChordDifferential σ k).toLinearMap)^2) := by
  let D := (softChordDifferential σ k).toLinearMap
  let H := (softLogHessian m k).toLinearMap
  change _ = LinearMap.trace ℝ EuclideanPlaneMomentum (H*D^2)
  rw [pow_two,← mul_assoc,LinearMap.trace_mul_comm ℝ (H*D) D,soft_trace_in_basis b]
  apply Finset.sum_congr rfl
  intro i _
  exact (soft_chord_differential_symmetric σ k _ _).symm

/-- The trace of the exact second derivative of the chord, contracted with
the logarithm's gradient, is a scalar density in the original momentum. -/
theorem soft_direct_contact_trace (b : OrthonormalBasis (Fin 4) ℝ EuclideanPlaneMomentum)
    (m σ : ℝ) (k : EuclideanPlaneMomentum) :
    (∑ i, inner ℝ (softLogGradient m k) (softChordSecond σ k (softBasisDirection b i))) =
      (4/(m^2+‖k‖^2))*‖k‖^2*(4*σ^4*‖k‖^2-12*σ^2)*Real.exp (-(σ^2*‖k‖^2)) := by
  let g := Real.exp (-(σ^2*‖k‖^2))
  let l := 4/(m^2+‖k‖^2)
  let A := l * (4*σ^4*g*‖k‖^2-4*σ^2*g)
  let B := -l * (2*σ^2*g*‖k‖^2)
  have he (i : Fin 4) :
      inner ℝ (softLogGradient m k) (softChordSecond σ k (softBasisDirection b i)) =
        A * (inner ℝ k (b i))^2 + B := by
    simp only [softLogGradient,softChordSecond,softBasisDirection,real_inner_smul_left,inner_sub_right,
      real_inner_smul_right,real_inner_self_eq_norm_sq,A,B,l,g]
    ring
  simp_rw [he]
  rw [Finset.sum_add_distrib,← Finset.mul_sum]
  have hParseval : (∑ i, (inner ℝ k (b i))^2) = ‖k‖^2 := by
    rw [← real_inner_self_eq_norm_sq,← b.sum_inner_mul_inner k k]
    apply Finset.sum_congr rfl
    intro i _
    rw [pow_two,real_inner_comm k (b i)]
  rw [hParseval,Finset.sum_const,Finset.card_fin,nsmul_eq_mul]
  dsimp only [A,B,g,l]
  ring

theorem constant_field_full_trace (b : OrthonormalBasis (Fin 4) ℝ EuclideanPlaneMomentum)
    (e σ : ℝ) {m : ℝ} (hm : m ≠ 0) (k : EuclideanPlaneMomentum) :
    (∑ i, deriv (deriv (constantFieldDensity e m σ k (softBasisDirection b i))) 0) =
      e^2 * (LinearMap.trace ℝ EuclideanPlaneMomentum
        ((softLogHessian m k).toLinearMap*((softChordDifferential σ k).toLinearMap)^2) +
        (4/(m^2+‖k‖^2))*‖k‖^2*(4*σ^4*‖k‖^2-12*σ^2)*Real.exp (-(σ^2*‖k‖^2))) := by
  simp_rw [(constant_field_density_second e σ hm k _).deriv,← Finset.mul_sum,Finset.sum_add_distrib]
  change _ * ((∑ i, inner ℝ (softLogHessian m k (softChordDifferential σ k (b i)))
    (softChordDifferential σ k (b i))) + _) = _
  rw [soft_two_vertex_trace,soft_direct_contact_trace]

end UV.RelativeSoft
