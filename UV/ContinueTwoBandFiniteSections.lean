import UV.ContinueTwoBandDeterminantSeries
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Group.Tannery

/-! Orthogonal finite sections of the two composable Hilbert-space
hopping factors. All limits use the directed set of finite subsets. -/

noncomputable section
open Matrix Filter
open scoped Topology Matrix.Norms.L2Operator InnerProductSpace ComplexConjugate

namespace UV.SectorPlane

variable {H I : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (b : HilbertBasis I ℂ H)

def schurRead (s : Finset I) (x : H) : EuclideanSpace ℂ s :=
  WithLp.toLp 2 (fun i => inner ℂ (b i) x)

def schurWrite (s : Finset I) (v : EuclideanSpace ℂ s) : H := ∑ i, v i • b i

def schurProject (s : Finset I) (x : H) : H := schurWrite b s (schurRead b s x)

def schurSection (s : Finset I) (A : H →L[ℂ] H) : Matrix s s ℂ :=
  fun i j => inner ℂ (b i) (A (b j))

theorem schur_read_le (s : Finset I) (x : H) : ‖schurRead b s x‖ ≤ ‖x‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1
  rw [EuclideanSpace.norm_sq_eq]
  rw [show (∑ i : s, ‖schurRead b s x i‖^2) = ∑ i ∈ s, ‖inner ℂ (b i) x‖^2 from
    Finset.sum_coe_sort s (fun i => ‖inner ℂ (b i) x‖^2)]
  exact
    (b.orthonormal.sum_inner_products_le (s := s) x)

theorem schur_write_norm (s : Finset I) (v : EuclideanSpace ℂ s) : ‖schurWrite b s v‖ = ‖v‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  have ho := b.orthonormal.comp (fun i : s => i.val) Subtype.val_injective
  have h := congrArg Complex.re (ho.inner_sum (fun i => v i) (fun i => v i) Finset.univ)
  change Complex.re _ = _ at h
  rw [← RCLike.re_to_complex] at h
  simpa only [schurWrite,← @norm_sq_eq_re_inner ℂ,Function.comp_apply,
    Complex.re_sum, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re,
    Complex.normSq_eq_norm_sq, EuclideanSpace.norm_sq_eq v] using h

theorem schur_project_le (s : Finset I) (x : H) : ‖schurProject b s x‖ ≤ ‖x‖ :=
  (schur_write_norm b s _).le.trans (schur_read_le b s x)

theorem schur_project_tendsto (x : H) : Tendsto (fun s => schurProject b s x) atTop (𝓝 x) := by
  classical
  have he (s : Finset I) : schurProject b s x = ∑ i ∈ s, b.repr x i • b i := by
    simp_rw [b.repr_apply_apply]
    exact Finset.sum_coe_sort s (fun i => inner ℂ (b i) x • b i)
  simp_rw [he]
  exact b.hasSum_repr x

theorem schur_project_tendsto_varying (x : Finset I → H) {y : H} (hx : Tendsto x atTop (𝓝 y)) :
    Tendsto (fun s => schurProject b s (x s)) atTop (𝓝 y) := by
  have hdiff (s : Finset I) : schurProject b s (x s) - schurProject b s y =
      schurProject b s (x s-y) := by simp [schurProject,schurWrite,schurRead,inner_sub_right,sub_smul,Finset.sum_sub_distrib]
  have ht : Tendsto (fun s => schurProject b s (x s)-schurProject b s y) atTop (𝓝 0) := by
    apply squeeze_zero_norm' (Eventually.of_forall fun s => (hdiff s) ▸ schur_project_le b s (x s-y))
    simpa only [sub_self,norm_zero] using (hx.sub (tendsto_const_nhds (x:=y))).norm
  simpa only [sub_add_cancel,zero_add] using ht.add (schur_project_tendsto b y)

variable [DecidableEq I]

theorem schur_section_action (s : Finset I) (A : H →L[ℂ] H) (v : EuclideanSpace ℂ s) :
    Matrix.toEuclideanCLM (n:=s) (𝕜:=ℂ) (schurSection b s A) v = schurRead b s (A (schurWrite b s v)) := by
  ext i
  change (∑ j : s, inner ℂ (b i) (A (b j)) * v j) = inner ℂ (b i) (A (∑ j : s, v j • b j))
  simp only [map_sum,map_smul,inner_sum,inner_smul_right]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

theorem schur_section_opnorm (s : Finset I) (A : H →L[ℂ] H) : ‖schurSection b s A‖ ≤ ‖A‖ := by
  change ‖Matrix.toEuclideanCLM (n:=s) (𝕜:=ℂ) (schurSection b s A)‖ ≤ ‖A‖
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro v
  rw [schur_section_action]
  exact (schur_read_le b s _).trans ((A.le_opNorm _).trans_eq (by rw [schur_write_norm]))

private theorem schur_write_single (s : Finset I) (i : s) :
    schurWrite b s (EuclideanSpace.single i (1:ℂ)) = b i := by
  classical
  simp [schurWrite,EuclideanSpace.single_apply]

/-- The finite intermediate projections of (BA)^n, including both ends. -/
def schurMiddle (s : Finset I) (A B : H →L[ℂ] H) (x : H) : ℕ → H
  | 0 => schurProject b s x
  | n+1 => schurProject b s (B (schurProject b s (A (schurMiddle s A B x n))))

omit [DecidableEq I] in
theorem schur_middle_bound (s : Finset I) (A B : H →L[ℂ] H) (x : H) (n : ℕ) :
    ‖schurMiddle b s A B x n‖ ≤ (‖B‖*‖A‖)^n*‖x‖ := by
  induction n with
  | zero => simpa only [schurMiddle,pow_zero,one_mul] using schur_project_le b s x
  | succ n ih =>
    calc
      _ ≤ ‖B‖*(‖A‖*((‖B‖*‖A‖)^n*‖x‖)) :=
        (schur_project_le b s _).trans ((B.le_opNorm _).trans (mul_le_mul_of_nonneg_left
        ((schur_project_le b s _).trans ((A.le_opNorm _).trans
          (mul_le_mul_of_nonneg_left ih (norm_nonneg _)))) (norm_nonneg _)))
      _ = _ := by rw [pow_succ]; ring

omit [DecidableEq I] in
theorem schur_middle_limit (A B : H →L[ℂ] H) (x : H) (n : ℕ) :
    Tendsto (fun s => schurMiddle b s A B x n) atTop (𝓝 (((B*A)^n) x)) := by
  induction n with
  | zero => simpa [schurMiddle] using schur_project_tendsto b x
  | succ n ih =>
    rw [pow_succ']
    exact schur_project_tendsto_varying b _ (B.continuous.continuousAt.tendsto.comp
      (schur_project_tendsto_varying b _ (A.continuous.continuousAt.tendsto.comp ih)))

private theorem schur_section_run (s : Finset I) (A B : H →L[ℂ] H) (i : s) (n : ℕ) :
    let a := schurSection b s A
    let c := schurSection b s B
    let e := EuclideanSpace.single i (1:ℂ)
    schurWrite b s (Matrix.toEuclideanCLM (n:=s) (𝕜:=ℂ) ((c*a)^n*c) e) =
      schurMiddle b s A B (B (b i)) n := by
  intro a c e
  induction n with
  | zero =>
    rw [pow_zero,one_mul,schurMiddle]
    change schurWrite b s (Matrix.toEuclideanCLM (n:=s) (𝕜:=ℂ) (schurSection b s B) e) = _
    rw [schur_section_action,schur_write_single]
    rfl
  | succ n ih =>
    rw [pow_succ',mul_assoc,map_mul (Matrix.toEuclideanCLM (n:=s) (𝕜:=ℂ)),ContinuousLinearMap.mul_apply,
      map_mul (Matrix.toEuclideanCLM (n:=s) (𝕜:=ℂ)),ContinuousLinearMap.mul_apply,schur_section_action,schur_section_action]
    change schurProject b s (B (schurProject b s (A _))) = _
    rw [ih]
    rfl

theorem schur_section_power_diagonal (s : Finset I) (A B : H →L[ℂ] H) (i : s) (n : ℕ) :
    ((schurSection b s A * schurSection b s B)^(n+1)) i i =
      inner ℂ (b i) (A (schurMiddle b s A B (B (b i)) n)) := by
  let a := schurSection b s A
  let c := schurSection b s B
  let e := EuclideanSpace.single i (1:ℂ)
  have hprod (j : ℕ) : (a*c)^(j+1) = a*((c*a)^j*c) := by
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ _ (j+1),ih,pow_succ]; simp only [mul_assoc]
  let M := (a*c)^(n+1)
  have hdiag : M i i = (Matrix.toEuclideanCLM (n:=s) (𝕜:=ℂ) M e) i := by
    change M i i = (M *ᵥ Pi.single i 1) i
    rw [Matrix.mulVec_single_one]
    rfl
  change M i i = _
  rw [hdiag]
  dsimp only [M]
  rw [hprod,map_mul (Matrix.toEuclideanCLM (n:=s) (𝕜:=ℂ)),ContinuousLinearMap.mul_apply,schur_section_action,
    schur_section_run b s A B i n]
  rfl

end UV.SectorPlane
