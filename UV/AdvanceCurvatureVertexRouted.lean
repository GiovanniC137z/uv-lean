import UV.AdvanceCurvatureWick

/-! The literal four-mode vertex on the period-2π torus. Haar and color
factors stay fixed while every depth weight remains attached to a leg. -/

noncomputable section

open MeasureTheory Real
open scoped BigOperators ComplexConjugate

namespace UV.AdvanceCurvatureVertex

open UV.ExtendCurvaturePotential UV.NextCurvatureLaw UV.NextCurvatureFourierSummability
open UV.AdvanceCurvatureWick
open UV.ContinueCurvatureModes UV.FurtherCurvatureShell

/-- The normalized Haar integral of the four real, signed Fourier modes
at a quartic vertex. The grouping follows the two bracket factors. -/
def quarticHaarVertex (k l p q : MeanZeroMode) : ℝ :=
  normalizedIntegral ((realTorusMode k * realTorusMode l) * (realTorusMode p * realTorusMode q))

/-- The normalized measure has mass one, and each signed real basis mode
has supremum norm at most `sqrt 2`. All four slots can repeat. -/
theorem norm_quarticHaarVertex_le (k l p q : MeanZeroMode) :
    ‖quarticHaarVertex k l p q‖ ≤ 4 := by
  let F := (realTorusMode k * realTorusMode l) * (realTorusMode p * realTorusMode q)
  have hpair (i j : MeanZeroMode) : ‖realTorusMode i * realTorusMode j‖ ≤ 2 := by
    calc
      _ ≤ ‖realTorusMode i‖ * ‖realTorusMode j‖ := norm_mul_le _ _
      _ ≤ sqrt 2 * sqrt 2 := mul_le_mul (realTorusMode_norm_bound i) (realTorusMode_norm_bound j)
        (norm_nonneg _) (sqrt_nonneg _)
      _ = _ := Real.mul_self_sqrt (by norm_num)
  have hf : ‖F‖ ≤ 4 := calc
    _ ≤ ‖realTorusMode k * realTorusMode l‖ * ‖realTorusMode p * realTorusMode q‖ := norm_mul_le _ _
    _ ≤ (2 : ℝ) * 2 := mul_le_mul (hpair k l) (hpair p q) (norm_nonneg _) (by norm_num)
    _ = _ := by norm_num
  change ‖∫ x, F x ∂normalizedTorusVolume‖ ≤ 4
  exact (BoundedContinuousFunction.norm_integral_le_norm normalizedTorusVolume
    (BoundedContinuousFunction.mkOfCompact F)).trans (by simpa only
      [BoundedContinuousFunction.norm_mkOfCompact] using hf)

/-- All depth-independent factors of one term of the squared bracket. -/
def curvatureVertexFactor {n : ℕ} (B : Fin n → Fin n → Fin n → ℝ)
    (c : Fin n) (e f : Leg n) : ℝ :=
  B c e.1.1 e.2.1 * B c f.1.1 f.2.1 * quarticHaarVertex e.1.2 e.2.2 f.1.2 f.2.2

/-- Uniform control of each residual vertex coefficient whenever the
finite color array is bounded by `D`. -/
theorem norm_curvatureVertexFactor_le {n : ℕ} (B : Fin n → Fin n → Fin n → ℝ)
    {D : ℝ} (hD : 0 ≤ D) (hB : ∀ a b c, ‖B a b c‖ ≤ D)
    (c : Fin n) (e f : Leg n) : ‖curvatureVertexFactor B c e f‖ ≤ 4 * D^2 := by
  unfold curvatureVertexFactor
  simp only [norm_mul]
  calc
    _ ≤ (D * D) * 4 := mul_le_mul
      (mul_le_mul (hB _ _ _) (hB _ _ _) (norm_nonneg _) hD)
      (norm_quarticHaarVertex_le _ _ _ _) (norm_nonneg _) (mul_nonneg hD hD)
    _ = _ := by ring

/-- The complete finite color array gives a uniform mode-independent
bound for the literal vertex without any additional hypothesis on `B`. -/
theorem curvatureVertexFactor_uniformly_bounded {n : ℕ} (B : Fin n → Fin n → Fin n → ℝ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ c e f, ‖curvatureVertexFactor B c e f‖ ≤ D := by
  let A : ℝ := ∑ c, ∑ a, ∑ b, ‖B c a b‖
  have hA : 0 ≤ A := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => norm_nonneg _
  refine ⟨4 * A^2, by positivity, ?_⟩
  apply norm_curvatureVertexFactor_le B hA
  intro c a b
  have hb : ‖B c a b‖ ≤ ∑ v, ‖B c a v‖ :=
    Finset.single_le_sum (fun v _ => norm_nonneg (B c a v)) (Finset.mem_univ b)
  have ha : (∑ v, ‖B c a v‖) ≤ ∑ u, ∑ v, ‖B c u v‖ :=
    Finset.single_le_sum (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ a)
  have hc : (∑ u, ∑ v, ‖B c u v‖) ≤ A :=
    Finset.single_le_sum
      (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
      (Finset.mem_univ c)
  exact hb.trans (ha.trans hc)

/-- The actual depth-dependent vertex splits into the four harmonic
weights and a single fixed torus and color coefficient. -/
theorem normalizedIntegral_legShape_mul {n : ℕ} (B : Fin n → Fin n → Fin n → ℝ)
    (ℓ : ℝ) (c : Fin n) (e f : Leg n) :
    normalizedIntegral (legShape B ℓ c e * legShape B ℓ c f) =
      curvatureVertexFactor B c e f *
        (derivativeWeight 0 ℓ e.1.2 * derivativeWeight 0 ℓ e.2.2 *
          (derivativeWeight 0 ℓ f.1.2 * derivativeWeight 0 ℓ f.2.2)) := by
  unfold legShape curvatureVertexFactor quarticHaarVertex
  rw [smul_mul_assoc, mul_smul_comm, smul_smul, map_smul]
  simp only [smul_eq_mul]
  ring

/-- Substitutes the literal depth-free vertex in the finite polynomial
expansion of the integrated curvature interaction. -/
theorem cutoffBracketPotential_haar_expansion {n : ℕ} (B : Fin n → Fin n → Fin n → ℝ)
    (Λ ℓ : ℝ) (X : ModeSlot n → ℝ) : cutoffBracketPotential B Λ ℓ X =
      (1/2 : ℝ) * ∑ c, ∑ e ∈ vertexLegs n Λ, ∑ f ∈ vertexLegs n Λ,
        curvatureVertexFactor B c e f *
          (derivativeWeight 0 ℓ e.1.2 * derivativeWeight 0 ℓ e.2.2 *
            (derivativeWeight 0 ℓ f.1.2 * derivativeWeight 0 ℓ f.2.2)) * quarticMonomial e f X := by
  simp only [cutoffBracketPotential_quartic_expansion, normalizedIntegral_legShape_mul]

private def signedIndex (k : MeanZeroMode) (ε : Bool) : TorusMode :=
  if ε then -k.1 else k.1

private def modePhase (k : MeanZeroMode) : ℂ :=
  if 0 < k.1 (firstActive k) then 1 else Complex.I

private def characterCoefficient (k : MeanZeroMode) (ε : Bool) : ℂ :=
  (sqrt (2 : ℝ) : ℂ) / 2 * (if ε then conj (modePhase k) else modePhase k)

private theorem realMode_character_sum (k : MeanZeroMode) (x : Torus) :
    (realTorusMode k x : ℂ) =
      ∑ ε : Bool, characterCoefficient k ε * torusCharacter (signedIndex k ε) x := by
  simp only [Fintype.sum_bool, characterCoefficient, signedIndex, Bool.false_eq_true, ↓reduceIte]
  unfold realTorusMode modePhase
  split
  · simp only [ContinuousMap.smul_apply, smul_eq_mul, ContinuousMap.comp_apply,
      ContinuousMap.coe_mk]
    rw [torusCharacter_neg]
    apply Complex.ext <;> simp [Complex.ofReal_mul, Complex.mul_re, Complex.mul_im]
    all_goals ring
  · simp only [ContinuousMap.smul_apply, smul_eq_mul, ContinuousMap.comp_apply,
      ContinuousMap.coe_mk]
    rw [torusCharacter_neg]
    apply Complex.ext <;> simp [Complex.ofReal_mul, Complex.mul_re, Complex.mul_im, Complex.conj_I]
    all_goals ring

/-- Each sign selects one of the two complex characters in its real
sine or cosine mode. The sum is the torus frequency at the vertex. -/
def signedVertexFrequency (k l p q : MeanZeroMode) (ε : Bool × Bool × Bool × Bool) : TorusMode :=
  (signedIndex k ε.1 + signedIndex l ε.2.1) +
    (signedIndex p ε.2.2.1 + signedIndex q ε.2.2.2)

private def vertexCharacterCoefficient (k l p q : MeanZeroMode) (ε : Bool × Bool × Bool × Bool) : ℂ :=
  (characterCoefficient k ε.1 * characterCoefficient l ε.2.1) *
    (characterCoefficient p ε.2.2.1 * characterCoefficient q ε.2.2.2)

private theorem quartic_character_expansion (k l p q : MeanZeroMode) (x : Torus) :
    ((realTorusMode k x * realTorusMode l x * (realTorusMode p x * realTorusMode q x) : ℝ) : ℂ) =
      ∑ ε : Bool × Bool × Bool × Bool, vertexCharacterCoefficient k l p q ε *
        torusCharacter (signedVertexFrequency k l p q ε) x := by
  simp only [Complex.ofReal_mul, realMode_character_sum, Fintype.sum_prod_type, Fintype.sum_bool,
    vertexCharacterCoefficient, signedVertexFrequency, torusCharacter_add]
  ring

private theorem quarticHaarVertex_character_sum (k l p q : MeanZeroMode) :
    (quarticHaarVertex k l p q : ℂ) = ∑ ε : Bool × Bool × Bool × Bool,
      if signedVertexFrequency k l p q ε = 0 then vertexCharacterCoefficient k l p q ε else 0 := by
  classical
  let h (ε : Bool × Bool × Bool × Bool) (x : Torus) := vertexCharacterCoefficient k l p q ε *
    torusCharacter (signedVertexFrequency k l p q ε) x
  have hi (ε : Bool × Bool × Bool × Bool) : Integrable (h ε) normalizedTorusVolume :=
    ((BoundedContinuousFunction.mkOfCompact
      (torusCharacter (signedVertexFrequency k l p q ε))).integrable _).const_mul _
  change ((∫ x, realTorusMode k x * realTorusMode l x * (realTorusMode p x * realTorusMode q x)
    ∂normalizedTorusVolume : ℝ) : ℂ) = _
  rw [← integral_complex_ofReal]
  simp_rw [quartic_character_expansion]
  change (∫ x, ∑ ε, h ε x ∂normalizedTorusVolume) = _
  rw [integral_finset_sum _ (fun ε _ => hi ε)]
  simp_rw [h, integral_const_mul, torus_character_integral, mul_ite, mul_one, mul_zero]

/-- Haar integration enforces momentum conservation for the sign
choices of the four characters in the actual real basis. -/
theorem quarticHaarVertex_zero_of_no_signed_routing (k l p q : MeanZeroMode)
    (h : ∀ ε, signedVertexFrequency k l p q ε ≠ 0) : quarticHaarVertex k l p q = 0 := by
  apply Complex.ofReal_injective
  rw [quarticHaarVertex_character_sum]
  simp [h]

end UV.AdvanceCurvatureVertex
