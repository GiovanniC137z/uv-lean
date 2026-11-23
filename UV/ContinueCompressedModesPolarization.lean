import UV.ContinueCompressedModesLabels
import Mathlib.Algebra.MvPolynomial.Eval

/-! Extract independently marked electric sources before Wick sewing.
The squarefree multidegree picks precisely the permutations with each
source occurring once. -/

noncomputable section
open Matrix UV.SectorPlane MvPolynomial
open scoped Matrix.Norms.L2Operator
namespace UV

attribute [local instance] Classical.propDecidable

variable {H U : Type*} [Fintype H] [Fintype U]

def compressedColorDegree {r : ℕ} (d : Fin r → H) : H →₀ ℕ := ∑ b, Finsupp.single (d b) 1

def compressedColorPolynomial {r : ℕ} (c : U → (Fin r → H) → ℝ) : MvPolynomial H ℝ :=
  ∑ v, ∑ d, monomial (compressedColorDegree d) (c v d)

theorem compressed_color_polynomial_eval {r : ℕ} (c : U → (Fin r → H) → ℝ) (x : H → ℝ) :
    eval x (compressedColorPolynomial c) = ∑ v, ∑ d, (∏ b, x (d b))*c v d := by
  have hx (h : H) : (monomial (Finsupp.single h 1) 1 : MvPolynomial H ℝ) = X h := rfl
  simp only [compressedColorPolynomial,map_sum,compressedColorDegree,monomial_sum_index,
    hx,map_mul,map_prod,eval_X,eval_C]
  simp only [mul_comm]

theorem compressed_color_degree_bijective {r : ℕ} (d : Fin r → H) :
    compressedColorDegree d = (∑ h : H, Finsupp.single h 1) ↔ Function.Bijective d := by
  classical
  rw [Function.bijective_iff_existsUnique,DFunLike.ext_iff]
  have he (h : H) : compressedColorDegree d h = (Finset.univ.filter fun b => d b = h).card := by
    simp only [compressedColorDegree,Finsupp.finset_sum_apply,Finsupp.single_apply,Finset.card_filter]
  simp only [he,Finsupp.finset_sum_apply,Finsupp.single_apply,Finset.sum_ite_eq',Finset.mem_univ,if_true,
    Finset.card_eq_one,Finset.eq_singleton_iff_unique_mem,Finset.mem_filter,true_and,ExistsUnique]

theorem compressed_color_distinct_source_coefficient {r : ℕ} (c : U → (Fin r → H) → ℝ) :
    (compressedColorPolynomial c).coeff (∑ h : H, Finsupp.single h 1) =
      ∑ v, ∑ d, if Function.Bijective d then c v d else 0 := by
  classical
  simp only [compressedColorPolynomial,coeff_sum,coeff_monomial,compressed_color_degree_bijective]

variable {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι]

omit [Fintype H] [Fintype κ] [DecidableEq κ] in
theorem compressed_label_cycle_scale {n : ℕ} (m L : ℝ) (T : NormalBall 5 →ₗᵢ[ℝ] WilsonBallSpace ι)
    (ξ : ℝ) (p : κ → OSFourSpace) (u : H → κ → κ → UnitVector OSFourSpace) (W : H → κ → κ → ℂ)
    (v : Fin (n+1) → κ) (d : Fin (n+1) → H) (x : H → ℝ) :
    compressedLabelCycle m L T ξ p u (fun c i j => (x c:ℂ)*W c i j) v d =
      (∏ b, (x (d b):ℂ))*compressedLabelCycle m L T ξ p u W v d := by
  simp only [compressedLabelCycle,compressedIncidence,mul_assoc,Finset.prod_mul_distrib]

/-- Evaluation of the real multivariate electric-source polynomial is
the normalized derivative of the actual affine negative logarithmic
determinant for that superposition of sources. -/
theorem compressed_source_polynomial_eval {m : ℝ} (hm : 0 < m) (L : ℝ)
    (T : NormalBall 5 →ₗᵢ[ℝ] WilsonBallSpace ι) (ξ : ℝ) (p : κ → OSFourSpace)
    (u : H → κ → κ → UnitVector OSFourSpace) (W : H → κ → κ → ℂ) (n : ℕ) (x : H → ℝ) :
    iteratedDeriv (n+1) (compressedRelativeLog (compressedBlockSymbol m ξ p)
      (∑ c, compressedBlockVertex L T ξ p (u c) (fun i j => (x c:ℂ)*W c i j))) 0 / (n+1).factorial =
      eval x (compressedColorPolynomial (r := n+1) (fun v d =>
        ((-1:ℝ)^(n+1)/(n+1))*(compressedLabelCycle m L T ξ p u W v d).re)) := by
  rw [compressed_labeled_source_coefficient hm,compressed_color_polynomial_eval]
  simp only [compressed_label_cycle_scale,←Complex.ofReal_prod,Complex.re_sum,Complex.re_ofReal_mul,
    div_eq_mul_inv,Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro d _
  ring

end UV
