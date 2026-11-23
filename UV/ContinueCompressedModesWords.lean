import UV.ContinueCompressedModesPencil
import UV.ContinueCompressedModesVariation

/-! Each arc and cycle of the affine source is a dressed ordered Dirac
word. The scalar Fourier source and photon incidence factors are
extracted without changing the spin order. -/

noncomputable section
open Matrix UV.SectorPlane
open scoped Matrix.Norms.L2Operator

namespace UV

variable {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι]

def compressedIncidence (L : ℝ) (T : NormalBall 5 →ₗᵢ[ℝ] WilsonBallSpace ι)
    (p : κ → OSFourSpace) (W : κ → κ → ℂ) (i j : κ) :=
  W i j * (normalLegForm L T 0 (p i-p j):ℂ)

omit [Fintype κ] [DecidableEq κ] in
/-- The entry inserted in the determinant is the actual first variation
in the prescribed transverse unit polarization. -/
theorem compressed_block_source_variation (m L : ℝ) (T : NormalBall 5 →ₗᵢ[ℝ] WilsonBallSpace ι) (ξ : ℝ)
    (p : κ → OSFourSpace) (u : κ → κ → UnitVector OSFourSpace) (W : κ → κ → ℂ) (i j : κ)
    (ht : inner ℝ (p i-p j) (u i j).val = 0) :
    HasDerivAt (fun t : ℝ => W i j • compressedToneConjugated m L T ξ (p j) (p i-p j) (u i j).val t 1)
      (compressedBlockVertex L T ξ p u W i j) 0 := by
  have h := (compressed_conjugation_vertex_derivative m L T ξ (p j) (p i-p j) (u i j)).const_smul (W i j)
  convert h using 1
  simp only [compressedPhotonVertex,compressedLongitudinal,ht,zero_div,zero_smul,sub_zero,add_zero,
    diracSlash_real_smul,compressedVertexFactor,show p j+(p i-p j)=p i by abel,
    Complex.ofReal_mul,smul_smul,compressedBlockVertex]
  congr 1
  ring

theorem compressed_block_mark (m L : ℝ) (T : NormalBall 5 →ₗᵢ[ℝ] WilsonBallSpace ι) (ξ : ℝ)
    (p : κ → OSFourSpace) (u : κ → κ → UnitVector OSFourSpace) (W : κ → κ → ℂ) (i j : κ) :
    (compressedBlockFree m ξ p * compressedBlockVertex L T ξ p u W) i j =
      compressedIncidence L T p W i j • compressedOpenFactor m L T ξ (u i j) (p i) (p j) := by
  simp only [compressedBlockFree,diagonal_mul,compressedBlockVertex,compressedOpenFactor,
    compressedIncidence,mul_smul_comm,smul_smul]
  simp only [mul_assoc]

def compressedClosedWord {n : ℕ} (m L : ℝ) (T : NormalBall 5 →ₗᵢ[ℝ] WilsonBallSpace ι) (ξ : ℝ)
    (p : κ → OSFourSpace) (u : κ → κ → UnitVector OSFourSpace) (W : κ → κ → ℂ)
    (v : Fin (n+1) → κ) : ℂ :=
  let next := finRotate (n+1)
  (∏ b, compressedIncidence L T p W (v b) (v (next b))) *
    compressedLoopTrace m L T ξ (fun b => u (v b) (v (next b))) (fun b => p (v b))

theorem compressed_block_cycle (m L : ℝ) (T : NormalBall 5 →ₗᵢ[ℝ] WilsonBallSpace ι) (ξ : ℝ)
    (p : κ → OSFourSpace) (u : κ → κ → UnitVector OSFourSpace) (W : κ → κ → ℂ)
    {n : ℕ} (i : κ) (z : Fin n → κ) :
    (compressedArc (compressedBlockFree m ξ p * compressedBlockVertex L T ξ p u W) i i z).trace =
      compressedClosedWord m L T ξ p u W (Fin.cons i z) := by
  let v := Fin.cons (α := fun _ => κ) i z
  let next := finRotate (n+1)
  let p' := fun b => p (v b)
  let u' := fun b => u (v b) (v (next b))
  have h := compressed_cyclic_vertex_trace m L T ξ u' p' next
  simp only [mul_smul_comm] at h
  simp only [compressedArc,Fin.snoc_eq_cons_rotate,compressed_block_mark,normal_ordered_word_smul,Matrix.trace_smul,smul_eq_mul]
  change _ * (normalOrderedWord (fun b => compressedOpenFactor m L T ξ (u' b) (p' b) (p' (next b)))).trace = _
  rw [show (normalOrderedWord (fun b => compressedOpenFactor m L T ξ (u' b) (p' b) (p' (next b)))).trace =
    compressedLoopTrace m L T ξ u' p' from h]
  rfl

/-- Every positive coefficient of the actual finite Fourier-spin
negative log-modulus determinant, including its cyclic factor. -/
theorem compressed_source_closed_coefficient {m : ℝ} (hm : 0 < m) (L : ℝ)
    (T : NormalBall 5 →ₗᵢ[ℝ] WilsonBallSpace ι) (ξ : ℝ) (p : κ → OSFourSpace)
    (u : κ → κ → UnitVector OSFourSpace) (W : κ → κ → ℂ) (n : ℕ) :
    iteratedDeriv (n+1) (compressedRelativeLog (compressedBlockSymbol m ξ p)
      (compressedBlockVertex L T ξ p u W)) 0 / (n+1).factorial =
      (-1:ℝ)^(n+1)*(∑ v : Fin (n+1) → κ, compressedClosedWord m L T ξ p u W v).re/(n+1) := by
  rw [compressed_block_logdet_paths hm]
  simp_rw [compressed_block_cycle]
  let e := Fin.consEquiv (fun _ : Fin (n+1) => κ)
  rw [←e.sum_comp (compressedClosedWord m L T ξ p u W),Fintype.sum_prod_type]
  rfl

/-- The terminal free propagator gives the open word at order n+1.
The polarization and the transfer are taken on the same marked arc. -/
theorem compressed_block_open_arc (m L : ℝ) (T : NormalBall 5 →ₗᵢ[ℝ] WilsonBallSpace ι) (ξ : ℝ)
    (p : κ → OSFourSpace) (u : κ → κ → UnitVector OSFourSpace) (W : κ → κ → ℂ)
    {n : ℕ} (i j : κ) (z : Fin n → κ) :
    let l := Fin.cons (α := fun _ => κ) i z
    let r := Fin.snoc (α := fun _ => κ) z j
    let v := Fin.snoc (α := fun _ => κ) l j
    compressedArc (compressedBlockFree m ξ p * compressedBlockVertex L T ξ p u W) i j z * normalDiracFrequency m (p j) ξ =
      (∏ b, compressedIncidence L T p W (l b) (r b)) •
        compressedOpenWord m L T ξ (fun b => u (l b) (r b)) (fun b => p (v b)) := by
  simp only [compressedArc,compressed_block_mark,normal_ordered_word_smul,smul_mul_assoc,
    compressedOpenWord,Fin.snoc_last,Fin.snoc_castSucc]
  rw [←Fin.cons_snoc_eq_snoc_cons]
  simp only [Fin.cons_succ]

def compressedOpenSourceWord {n : ℕ} (m L : ℝ) (T : NormalBall 5 →ₗᵢ[ℝ] WilsonBallSpace ι) (ξ : ℝ)
    (p : κ → OSFourSpace) (u : κ → κ → UnitVector OSFourSpace) (W : κ → κ → ℂ)
    (i j : κ) (z : Fin n → κ) : DiracMatrix :=
  let l := Fin.cons (α := fun _ => κ) i z
  let r := Fin.snoc (α := fun _ => κ) z j
  let v := Fin.snoc (α := fun _ => κ) l j
  (∏ b, compressedIncidence L T p W (l b) (r b)) •
    compressedOpenWord m L T ξ (fun b => u (l b) (r b)) (fun b => p (v b))

theorem compressed_source_open_power (m L : ℝ) (T : NormalBall 5 →ₗᵢ[ℝ] WilsonBallSpace ι) (ξ : ℝ)
    (p : κ → OSFourSpace) (u : κ → κ → UnitVector OSFourSpace) (W : κ → κ → ℂ)
    (n : ℕ) (i j : κ) :
    let S := compressedBlockFree m ξ p
    let V := compressedBlockVertex L T ξ p u W
    ((S*V)^(n+1)*S) i j = ∑ z : Fin n → κ, compressedOpenSourceWord m L T ξ p u W i j z := by
  dsimp only
  rw [show compressedBlockFree m ξ p = Matrix.diagonal (fun i => normalDiracFrequency m (p i) ξ) from rfl,
    Matrix.mul_diagonal,compressed_block_power,Finset.sum_mul]
  exact Finset.sum_congr rfl fun z _ => compressed_block_open_arc m L T ξ p u W i j z

/-- The open coefficients come from the actual inverse of the affine
source, with alternating signs and the free endpoint factor. -/
theorem compressed_source_open_series {m : ℝ} (hm : 0 < m) (L : ℝ)
    (T : NormalBall 5 →ₗᵢ[ℝ] WilsonBallSpace ι) (ξ : ℝ) (p : κ → OSFourSpace)
    (u : κ → κ → UnitVector OSFourSpace) (W : κ → κ → ℂ) (t : ℝ) :
    let D := compressedBlockSymbol m ξ p
    let S := compressedBlockFree m ξ p
    let V := compressedBlockVertex L T ξ p u W
    ‖(t:ℂ) • compressedFlatten (S*V)‖ < 1 →
    HasSum (fun r : ℕ => (-(t:ℂ))^r • compressedFlatten ((S*V)^r*S))
      (compressedFlatten (D+(t:ℂ) • V))⁻¹ := by
  dsimp only
  intro ht
  let D := compressedBlockSymbol m ξ p
  let S := compressedBlockFree m ξ p
  let V := compressedBlockVertex L T ξ p u W
  obtain ⟨hDS,hSD⟩ := compressed_block_free_inverse hm ξ p
  have h := compressed_inverse_open_series (compressedFlatten D) (compressedFlatten S) (compressedFlatten V)
    (by rw [←map_mul,hDS,map_one]) (by rw [←map_mul,hSD,map_one]) t (by simpa only [map_mul] using ht)
  simpa only [map_add,map_mul,map_smul,map_pow,D,S,V] using h

end UV
