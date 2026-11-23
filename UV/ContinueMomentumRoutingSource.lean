import UV.ContinueMomentumRoutingConclusion
import UV.ContinueCompressedModesPencil
import UV.ContinueNormalLegProfile

/-! Fourier-spin coefficients of the protected affine Dirac source.
Only the transverse photon mark is shell-compressed here, with separate
incidences on opposite ends of a contraction. -/

noncomputable section

open Matrix UV.SectorPlane MeasureTheory MeasureTheory.Measure
open scoped ComplexConjugate Matrix.Norms.L2Operator

namespace UV

variable {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι]

def momentumSourceIncidence (L : ℝ) (R : OSFourSpace →L[ℝ] WilsonBallSpace ι)
    (p : κ → OSFourSpace) (W : κ → κ → ℂ) (i j : κ) : ℂ :=
  W i j*normalPhotonForm L R (p i-p j)*Complex.I

def momentumSourceVertex (L : ℝ) (R : OSFourSpace →L[ℝ] WilsonBallSpace ι) (p : κ → OSFourSpace)
    (u : κ → κ → UnitVector OSFourSpace) (W : κ → κ → ℂ) : Matrix κ κ DiracMatrix :=
  fun i j => momentumSourceIncidence L R p W i j • diracSlash (u i j).val

theorem momentum_source_mark (m L : ℝ) (R : OSFourSpace →L[ℝ] WilsonBallSpace ι) (ξ : ℝ)
    (p : κ → OSFourSpace) (u : κ → κ → UnitVector OSFourSpace) (W : κ → κ → ℂ) (i j : κ) :
    (compressedBlockFree m ξ p * momentumSourceVertex L R p u W) i j =
      momentumSourceIncidence L R p W i j • (normalDiracFrequency m (p i) ξ * diracSlash (u i j).val) := by
  simp only [compressedBlockFree,diagonal_mul,momentumSourceVertex,mul_smul_comm]

def momentumSourceCycle {n : ℕ} (m L : ℝ) (R : OSFourSpace →L[ℝ] WilsonBallSpace ι) (ξ : ℝ)
    (p : κ → OSFourSpace) (u : κ → κ → UnitVector OSFourSpace) (W : κ → κ → ℂ) (v : Fin (n+1) → κ) :=
  let next := finRotate (n+1)
  (∏ b, momentumSourceIncidence L R p W (v b) (v (next b))) *
    (normalOrderedWord (fun b => normalDiracFrequency m (p (v b)) ξ*diracSlash (u (v b) (v (next b))).val)).trace

theorem momentum_source_cycle (m L : ℝ) (R : OSFourSpace →L[ℝ] WilsonBallSpace ι) (ξ : ℝ)
    (p : κ → OSFourSpace) (u : κ → κ → UnitVector OSFourSpace) (W : κ → κ → ℂ) {n : ℕ} (i : κ) (z : Fin n → κ) :
    (compressedArc (compressedBlockFree m ξ p*momentumSourceVertex L R p u W) i i z).trace =
      momentumSourceCycle m L R ξ p u W (Fin.cons i z) := by
  simp only [compressedArc,Fin.snoc_eq_cons_rotate,momentum_source_mark,normal_ordered_word_smul,Matrix.trace_smul,smul_eq_mul]
  rfl

theorem momentum_source_closed_coefficient {m : ℝ} (hm : 0 < m) (L : ℝ) (R : OSFourSpace →L[ℝ] WilsonBallSpace ι)
    (ξ : ℝ) (p : κ → OSFourSpace) (u : κ → κ → UnitVector OSFourSpace) (W : κ → κ → ℂ) (n : ℕ) :
    iteratedDeriv (n+1) (compressedRelativeLog (compressedBlockSymbol m ξ p)
      (momentumSourceVertex L R p u W)) 0 / (n+1).factorial =
      (-1:ℝ)^(n+1)*(∑ v : Fin (n+1) → κ, momentumSourceCycle m L R ξ p u W v).re/(n+1) := by
  rw [compressed_block_logdet_paths hm]
  simp_rw [momentum_source_cycle]
  let e := Fin.consEquiv (fun _ : Fin (n+1) => κ)
  rw [←e.sum_comp (momentumSourceCycle m L R ξ p u W),Fintype.sum_prod_type]
  rfl

/-- Open-path coefficient of (S V)^(n+1) S with both Fourier-spin
endpoints fixed and all internal carrier states summed. -/
theorem momentum_source_open_coefficient (m L : ℝ) (R : OSFourSpace →L[ℝ] WilsonBallSpace ι)
    (ξ : ℝ) (p : κ → OSFourSpace) (u : κ → κ → UnitVector OSFourSpace) (W : κ → κ → ℂ) (n : ℕ) (i j : κ) :
    let S := compressedBlockFree m ξ p
    let V := momentumSourceVertex L R p u W
    ((S*V)^(n+1)*S) i j =
      ∑ z : Fin n → κ,
        let l := Fin.cons (α := fun _ => κ) i z
        let r := Fin.snoc (α := fun _ => κ) z j
        (∏ b, momentumSourceIncidence L R p W (l b) (r b)) •
          (normalOrderedWord (fun b => normalDiracFrequency m (p (l b)) ξ * diracSlash (u (l b) (r b)).val) *
            normalDiracFrequency m (p j) ξ) := by
  dsimp only
  rw [show ∀ (A : Matrix κ κ DiracMatrix), (A*compressedBlockFree m ξ p) i j = A i j*normalDiracFrequency m (p j) ξ from
    fun A => by simp only [compressedBlockFree,mul_diagonal]]
  rw [compressed_block_power,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro z _
  simp only [compressedArc,momentum_source_mark,normal_ordered_word_smul,smul_mul_assoc]

theorem momentum_source_opposite (L : ℝ) (R : OSFourSpace →L[ℝ] WilsonBallSpace ι) (q : OSFourSpace) :
    normalPhotonForm L R q*normalPhotonForm L R (-q) = (‖normalPhotonForm L R q‖^2 : ℝ) := by
  let z := normalPhotonForm L R q
  have he : normalPhotonForm L R (-q) = z := by
    unfold normalPhotonForm z
    rw [map_neg,smul_neg]
    exact normal_shell_characteristic_radial (norm_neg _)
  have hz : (z.re:ℂ) = z := normal_shell_characteristic_real _
  change z*normalPhotonForm L R (-q) = _
  rw [he]
  change z*z = ((‖z‖^2 : ℝ):ℂ)
  conv_lhs => rw [←hz]
  rw [←hz,Complex.norm_real,Real.norm_eq_abs,sq_abs,Complex.ofReal_pow,pow_two]
  simp

end UV
