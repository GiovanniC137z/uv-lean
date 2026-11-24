import UV.ContinueTwoBandFredholmLimit
import UV.ContinueTwoBandFourierCycleSource
import UV.ContinueOrderedCurrentVacuum

/-! The ordinary relative determinant of the slab's two-band source.
The two finite slot dimensions and bases may be chosen independently. -/

noncomputable section
open Matrix Filter MeasureTheory
open scoped Topology Matrix.Norms.L2Operator

namespace UV.SectorPlane

variable (T : ℝ) {A : TwoBandPoint → Spatial →L[ℝ] ℝ} (hA : Continuous A)
    {φ : TwoBandPoint → ℝ} (hφ : Continuous φ) {m : ℝ} (hm : 0 ≤ m) (q g : ℝ)
    {σ L₁ L₂ L₃ : ℝ} (hσ : 0 < σ) (h₁ : 0 < L₁) (h₂ : 0 < L₂) (h₃ : 0 < L₃)
    {I J : Type*} [DecidableEq I] [DecidableEq J]
    (b : HilbertBasis I ℂ (Lp ℂ 2 (twoBandSlabMeasure T L₁ L₂ L₃)))
    (d : HilbertBasis J ℂ (Lp ℂ 2 (twoBandSlabMeasure T L₁ L₂ L₃)))

/-- Arbitrary real hopping, charge, and continuous real backgrounds.
The normalized finite block determinant with identity onsite blocks and
the ordinary determinant of the eliminated block have the same limit. -/
theorem twoBand_slab_relative_determinant :
    let U := twoBandSlabOperator true T hA hφ hm q g hσ h₁ h₂ h₃
    let V := twoBandSlabOperator false T hA hφ hm q g hσ h₁ h₂ h₃
    let D := schurNuclearDet (fun i => V.adjoint (b i)) (fun i => U (b i))
    D = schurNuclearDet (fun j => V.adjoint (d j)) (fun j => U (d j)) ∧
      Tendsto (fun s : Finset I × Finset J =>
        (1-schurBetween b d s.1 s.2 V * schurBetween d b s.2 s.1 U).det)
        atTop (𝓝 D) ∧
      Tendsto (fun s : Finset I × Finset J =>
        (Matrix.fromBlocks 1 (schurBetween d b s.2 s.1 U) (schurBetween b d s.1 s.2 V) 1).det)
        atTop (𝓝 D) := by
  intro U V D
  have hUb := twoBand_slab_operator_hilbert_schmidt true T hA hφ hm q g hσ h₁ h₂ h₃ b
  have hVb := twoBand_slab_operator_hilbert_schmidt false T hA hφ hm q g hσ h₁ h₂ h₃ b
  have hUd := twoBand_slab_operator_hilbert_schmidt true T hA hφ hm q g hσ h₁ h₂ h₃ d
  have hVd := twoBand_slab_operator_hilbert_schmidt false T hA hφ hm q g hσ h₁ h₂ h₃ d
  have ht := twoBand_fredholm_independent_sections b d V U hVb hUb
  refine ⟨schur_nuclear_basis_independent b d V U hVb hUb hVd hUd,ht,ht.congr fun s => ?_⟩
  exact (Matrix.det_fromBlocks_one₁₁ _ _ _).symm

/-- The same ordinary determinant is the exponential of the actual closed
position cycles in the convergence disk. In particular its value never
vanishes there, for any real continuous gauge background. -/
theorem twoBand_slab_relative_cycle_value {g : ℝ} (hg : |g| < m) :
    let hm := (abs_nonneg g).trans hg.le
    let U := twoBandSlabOperator true T hA hφ hm q g hσ h₁ h₂ h₃
    let V := twoBandSlabOperator false T hA hφ hm q g hσ h₁ h₂ h₃
    let D := schurNuclearDet (fun i => V.adjoint (b i)) (fun i => U (b i))
    let C := fun n : ℕ => twoBandSlabClosedCycle T hA hφ hm q g hσ h₁ h₂ h₃ n / (n+1)
    Summable (fun n => ‖C n‖) ∧ D = Complex.exp (-(∑' n, C n)) ∧ D ≠ 0 := by
  intro hm U V D C
  obtain ⟨ha, h⟩ := twoBand_slab_determinant_position_cycles T hA hφ hg q hσ h₁ h₂ h₃ b
  obtain ⟨_,ht,_⟩ := twoBand_slab_relative_determinant T hA hφ hm q g hσ h₁ h₂ h₃ b b
  have hv : D = Complex.exp (-(∑' n, C n)) :=
    tendsto_nhds_unique (ht.comp tendsto_atTop_diagonal) h
  exact ⟨ha,hv,hv ▸ Complex.exp_ne_zero _⟩

/-- The zero-hopping relative determinant has value one at every
background, with the same onsite normalization as the smeared vacuum. -/
theorem twoBand_slab_relative_zero (hpos : 0 < m) :
    let U := twoBandSlabOperator true T hA hφ hpos.le q 0 hσ h₁ h₂ h₃
    let V := twoBandSlabOperator false T hA hφ hpos.le q 0 hσ h₁ h₂ h₃
    schurNuclearDet (fun i => V.adjoint (b i)) (fun i => U (b i)) = 1 := by
  intro U V
  obtain ⟨_,ht,_⟩ := twoBand_slab_relative_determinant T hA hφ hpos.le q 0 hσ h₁ h₂ h₃ b b
  have hU : U = 0 := norm_le_zero_iff.mp (by
    simpa only [abs_zero,zero_div] using twoBand_slab_operator_contraction true T hA hφ hpos q 0 hσ h₁ h₂ h₃)
  apply tendsto_nhds_unique (ht.comp tendsto_atTop_diagonal)
  convert (tendsto_const_nhds (α := Finset I) (x := (1:ℂ))) using 1
  funext s
  change (1 - schurBetween b b s s V * schurBetween b b s s U).det = 1
  rw [hU]
  have hz : schurBetween b b s s (0 : _ →L[ℂ] _) = 0 := by ext i j; simp [schurBetween]
  rw [hz,Matrix.mul_zero,sub_zero,Matrix.det_one]

end UV.SectorPlane
