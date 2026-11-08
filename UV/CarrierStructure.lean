import UV.Carrier
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! The polynomial quotient carrier, its character equivalence and analytic
character estimates. Source: eq:carrier-algebra and prop:character-majorants. -/
noncomputable section
open Polynomial MeasureTheory
namespace UV.Carrier

/-- The literal defining polynomial of the scalar carrier. -/
def relation : Polynomial ℂ := X ^ 2 - 1
abbrev QuotientCarrier := AdjoinRoot relation

/-- The two polynomial character evaluations. -/
def evaluation : Polynomial ℂ →ₐ[ℂ] Algebra :=
  (Polynomial.aeval (1 : ℂ)).prod (Polynomial.aeval (-1 : ℂ))

@[simp] theorem evaluation_apply (p : Polynomial ℂ) :
    evaluation p = (p.eval 1, p.eval (-1)) := by
  simp [evaluation, Polynomial.aeval_def]

theorem evaluation_surjective : Function.Surjective evaluation := by
  intro z
  refine ⟨C ((z.1 + z.2) / 2) + C ((z.1 - z.2) / 2) * X, ?_⟩
  ext <;> simp [evaluation_apply] <;> ring

theorem evaluation_ker : RingHom.ker evaluation.toRingHom = Ideal.span {relation} := by
  ext p
  change evaluation p = 0 ↔ p ∈ Ideal.span {relation}
  rw [Ideal.mem_span_singleton]
  constructor
  · intro hp
    have h1 : p.eval 1 = 0 := by simpa using congrArg Prod.fst hp
    have h2 : p.eval (-1) = 0 := by simpa using congrArg Prod.snd hp
    have hd1 : X - C (1 : ℂ) ∣ p := (Polynomial.dvd_iff_isRoot).mpr h1
    have hd2 : X - C (-1 : ℂ) ∣ p := (Polynomial.dvd_iff_isRoot).mpr h2
    have hc : IsCoprime (X - C (1 : ℂ)) (X - C (-1 : ℂ)) :=
      Polynomial.isCoprime_X_sub_C_of_isUnit_sub (by norm_num)
    have hd := hc.mul_dvd hd1 hd2
    have hpoly : (X - C (1 : ℂ)) * (X - C (-1 : ℂ)) = relation := by
      simp [relation]
      ring
    rwa [hpoly] at hd
  · rintro ⟨q, rfl⟩
    ext <;> simp [relation]

/-- Complex-algebra identification of C[e]/(e²-1) with its two characters. -/
def quotientCharacterEquiv : QuotientCarrier ≃ₐ[ℂ] Algebra :=
  (Ideal.quotientEquivAlgOfEq ℂ evaluation_ker.symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective evaluation_surjective)

@[simp] theorem quotientCharacterEquiv_mk (p : Polynomial ℂ) :
    quotientCharacterEquiv (AdjoinRoot.mk relation p) = evaluation p := by
  change (Ideal.quotientKerAlgEquivOfSurjective evaluation_surjective)
    ((Ideal.quotientEquivAlgOfEq ℂ evaluation_ker.symm) (Ideal.Quotient.mk _ p)) = evaluation p
  rw [Ideal.quotientEquivAlgOfEq_mk]
  rfl

@[simp] theorem quotientCharacterEquiv_root :
    quotientCharacterEquiv (AdjoinRoot.root relation) = generator := by
  rw [AdjoinRoot.root, quotientCharacterEquiv_mk]
  ext <;> simp [generator]

/-- The declared reality, transported to the literal quotient. -/
def quotientReality (z : QuotientCarrier) : QuotientCarrier :=
  quotientCharacterEquiv.symm (reality (quotientCharacterEquiv z))

@[simp] theorem quotientCharacterEquiv_reality (z : QuotientCarrier) :
    quotientCharacterEquiv (quotientReality z) = reality (quotientCharacterEquiv z) := by
  simp [quotientReality]

theorem quotient_reality_involutive (z : QuotientCarrier) :
    quotientReality (quotientReality z) = z := by
  apply quotientCharacterEquiv.injective
  simp

theorem no_positive_functional_on_quotient :
    ¬ ∃ ω : QuotientCarrier →ₗ[ℂ] ℂ, ω 1 = 1 ∧
      ∀ z, 0 ≤ (ω (quotientReality z * z)).re := by
  rintro ⟨ω, hω, hpos⟩
  apply no_normalized_positive_functional
  refine ⟨ω.comp quotientCharacterEquiv.symm.toLinearMap, ?_, ?_⟩
  · simpa using hω
  · intro z
    simpa [quotientReality] using hpos (quotientCharacterEquiv.symm z)

/-- The transported reality has precisely the declared action on the generator. -/
@[simp] theorem quotientReality_root :
    quotientReality (AdjoinRoot.root relation) = -AdjoinRoot.root relation := by
  apply quotientCharacterEquiv.injective
  simp

/-- The transported reality conjugates the central complex scalars. -/
@[simp] theorem quotientReality_scalar (c : ℂ) :
    quotientReality (algebraMap ℂ QuotientCarrier c) =
      algebraMap ℂ QuotientCarrier (star c) := by
  apply quotientCharacterEquiv.injective
  rw [quotientCharacterEquiv_reality, quotientCharacterEquiv.commutes,
    quotientCharacterEquiv.commutes]
  rfl

/-- Reality respects sums on the literal quotient. -/
theorem quotientReality_add (x y : QuotientCarrier) :
    quotientReality (x + y) = quotientReality x + quotientReality y := by
  apply quotientCharacterEquiv.injective
  simp [reality]

/-- Reality reverses products, as the declared adjoint-type involution does. -/
theorem quotientReality_mul (x y : QuotientCarrier) :
    quotientReality (x * y) = quotientReality y * quotientReality x := by
  apply quotientCharacterEquiv.injective
  simp [reality, mul_comm]

/-- The reality generator gives -1 even in the literal polynomial quotient. -/
theorem quotient_reality_root_mul_root :
    quotientReality (AdjoinRoot.root relation) * AdjoinRoot.root relation = -1 := by
  apply quotientCharacterEquiv.injective
  simp

/-- The obstruction also holds for arbitrary algebraic operators with an everywhere
    defined adjoint pairing; boundedness and Hilbert-space completeness are unnecessary. -/
theorem no_reality_preserving_innerProduct_representation
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [Nontrivial H] :
    ¬ ∃ π : QuotientCarrier →ₐ[ℂ] Module.End ℂ H,
      ∀ z x y, inner ℂ (π (quotientReality z) x) y = inner ℂ x (π z y) := by
  rintro ⟨π, hπ⟩
  let T := π (AdjoinRoot.root relation)
  obtain ⟨v, hv⟩ := exists_ne (0 : H)
  have hprod : π (quotientReality (AdjoinRoot.root relation)) * T = -1 := by
    dsimp [T]
    rw [← map_mul, quotient_reality_root_mul_root, map_neg, map_one]
  have h := hπ (AdjoinRoot.root relation) (T v) v
  change inner ℂ ((π (quotientReality (AdjoinRoot.root relation)) * T) v) v =
    inner ℂ (T v) (T v) at h
  rw [hprod] at h
  have hr := congrArg Complex.re h
  simp only [LinearMap.neg_apply, Module.End.one_apply, inner_neg_left, Complex.neg_re] at hr
  have hvnorm := inner_self_eq_norm_sq (𝕜 := ℂ) v
  have hTnorm := inner_self_eq_norm_sq (𝕜 := ℂ) (T v)
  change (inner ℂ v v).re = ‖v‖ ^ 2 at hvnorm
  change (inner ℂ (T v) (T v)).re = ‖T v‖ ^ 2 at hTnorm
  rw [hvnorm, hTnorm] at hr
  have hp : 0 < ‖v‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hv)
  nlinarith [sq_nonneg ‖T v‖]

/-- No unital representation on a nonzero positive complex Hilbert space can
    identify the declared carrier reality with the physical adjoint. -/
theorem no_reality_preserving_hilbert_representation
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [Nontrivial H] :
    ¬ ∃ π : QuotientCarrier →ₐ[ℂ] (H →L[ℂ] H),
      ∀ z, π (quotientReality z) = (π z).adjoint := by
  rintro ⟨π, hπ⟩
  let T := π (AdjoinRoot.root relation)
  have hT : T.adjoint * T = -1 := by
    dsimp [T]
    rw [← hπ, ← map_mul, quotient_reality_root_mul_root, map_neg, map_one]
  obtain ⟨v, hv⟩ := exists_ne (0 : H)
  have h := ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_left T v
  change ‖T v‖ ^ 2 = (inner ℂ ((T.adjoint * T) v) v).re at h
  rw [hT] at h
  simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.one_apply, inner_neg_left,
    Complex.neg_re] at h
  have hvnorm := inner_self_eq_norm_sq (𝕜 := ℂ) v
  change (inner ℂ v v).re = ‖v‖ ^ 2 at hvnorm
  rw [hvnorm] at h
  have hp : 0 < ‖v‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hv)
  nlinarith [sq_nonneg ‖T v‖]

/-- The character norm is exactly the ordinary product-space norm. -/
theorem character_norm_eq (z : Algebra) : ‖z‖ = max ‖z.1‖ ‖z.2‖ := rfl

theorem character_norm_submultiplicative (x y : Algebra) : ‖x * y‖ ≤ ‖x‖ * ‖y‖ :=
  norm_mul_le x y

/-- Both character majorants control the entire carrier-valued graph. -/
theorem character_majorant_integrable {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {g : X → Algebra} {Mplus Mminus : X → ℝ}
    (hg : AEStronglyMeasurable g μ) (hplus : Integrable Mplus μ) (hminus : Integrable Mminus μ)
    (hb : ∀ᵐ x ∂μ, ‖(g x).1‖ ≤ Mplus x ∧ ‖(g x).2‖ ≤ Mminus x) : Integrable g μ := by
  apply (hplus.add hminus).mono' hg
  filter_upwards [hb] with x hx
  rw [character_norm_eq]
  change max ‖(g x).1‖ ‖(g x).2‖ ≤ Mplus x + Mminus x
  apply max_le
  · linarith [hx.1, hx.2, norm_nonneg (g x).2]
  · linarith [hx.1, hx.2, norm_nonneg (g x).1]

/-- The integral norm estimate in prop:character-majorants. -/
theorem character_integral_norm_bound {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {g : X → Algebra} {Mplus Mminus : X → ℝ}
    (hg : AEStronglyMeasurable g μ) (hplus : Integrable Mplus μ) (hminus : Integrable Mminus μ)
    (hb : ∀ᵐ x ∂μ, ‖(g x).1‖ ≤ Mplus x ∧ ‖(g x).2‖ ≤ Mminus x) :
    (∫ x, ‖g x‖ ∂μ) ≤ (∫ x, Mplus x ∂μ) + ∫ x, Mminus x ∂μ := by
  rw [← integral_add hplus hminus]
  apply integral_mono_ae (character_majorant_integrable hg hplus hminus hb).norm (hplus.add hminus)
  filter_upwards [hb] with x hx
  rw [character_norm_eq]
  change max ‖(g x).1‖ ‖(g x).2‖ ≤ Mplus x + Mminus x
  apply max_le
  · linarith [hx.1, hx.2, norm_nonneg (g x).2]
  · linarith [hx.1, hx.2, norm_nonneg (g x).1]

/-- Integration reconstructs both characters, without equating carrier reality
    with the positive adjoint. -/
theorem character_integral_reconstruction {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {g : X → Algebra} (hg : Integrable g μ) :
    (∫ x, g x ∂μ) = (∫ x, (g x).1 ∂μ, ∫ x, (g x).2 ∂μ) := by
  exact Prod.ext (fst_integral hg) (snd_integral hg)

/-- The paper's character norm equips the literal quotient with a normed-ring structure. -/
instance quotientNormedRing : NormedRing QuotientCarrier :=
  NormedRing.induced QuotientCarrier Algebra quotientCharacterEquiv quotientCharacterEquiv.injective

instance quotientNormedAlgebra : NormedAlgebra ℂ QuotientCarrier :=
  NormedAlgebra.induced ℂ QuotientCarrier Algebra quotientCharacterEquiv

/-- The quotient-to-character identification is an isometry for the declared norm. -/
def quotientCharacterIsometry : QuotientCarrier ≃ₗᵢ[ℂ] Algebra where
  toLinearEquiv := quotientCharacterEquiv.toLinearEquiv
  norm_map' _ := rfl

instance quotientCompleteSpace : CompleteSpace QuotientCarrier :=
  quotientCharacterIsometry.toIsometryEquiv.completeSpace_iff.mpr inferInstance

@[simp] theorem quotient_character_norm (z : QuotientCarrier) :
    ‖z‖ = max ‖(quotientCharacterEquiv z).1‖ ‖(quotientCharacterEquiv z).2‖ := rfl

theorem quotient_character_norm_submultiplicative (x y : QuotientCarrier) :
    ‖x * y‖ ≤ ‖x‖ * ‖y‖ := norm_mul_le x y

/-- The full quotient-valued graph is integrable under its two character bounds. -/
theorem quotient_character_majorant_integrable {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {g : X → QuotientCarrier} {Mplus Mminus : X → ℝ}
    (hg : AEStronglyMeasurable g μ) (hplus : Integrable Mplus μ) (hminus : Integrable Mminus μ)
    (hb : ∀ᵐ x ∂μ, ‖(quotientCharacterEquiv (g x)).1‖ ≤ Mplus x ∧
      ‖(quotientCharacterEquiv (g x)).2‖ ≤ Mminus x) : Integrable g μ := by
  apply (hplus.add hminus).mono' hg
  filter_upwards [hb] with x hx
  rw [quotient_character_norm]
  change max ‖(quotientCharacterEquiv (g x)).1‖ ‖(quotientCharacterEquiv (g x)).2‖ ≤
    Mplus x + Mminus x
  apply max_le
  · linarith [hx.1, hx.2, norm_nonneg (quotientCharacterEquiv (g x)).2]
  · linarith [hx.1, hx.2, norm_nonneg (quotientCharacterEquiv (g x)).1]

/-- Integration of a graph in the literal quotient commutes with both characters. -/
theorem quotient_character_integral_reconstruction {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {g : X → QuotientCarrier} (hg : Integrable g μ) :
    quotientCharacterEquiv (∫ x, g x ∂μ) =
      (∫ x, (quotientCharacterEquiv (g x)).1 ∂μ,
       ∫ x, (quotientCharacterEquiv (g x)).2 ∂μ) := by
  let T := quotientCharacterIsometry.toContinuousLinearEquiv.toContinuousLinearMap
  have hT : Integrable (fun x => T (g x)) μ := T.integrable_comp hg
  have he := T.integral_comp_comm hg
  change (∫ x, T (g x) ∂μ) = quotientCharacterEquiv (∫ x, g x ∂μ) at he
  rw [← he]
  exact character_integral_reconstruction hT

/-- Generic two-character estimate, including matrix coefficient spaces equipped
    with any fixed complete submultiplicative norm. The bounds are uniform in `p`. -/
theorem character_pair_uniform_estimate {X P B : Type*} [MeasurableSpace X]
    [NormedRing B] [NormedSpace ℝ B] [CompleteSpace B]
    {μ : Measure X} {g : P → X → B × B} {Mplus Mminus : X → ℝ}
    (hg : ∀ p, AEStronglyMeasurable (g p) μ)
    (hplus : Integrable Mplus μ) (hminus : Integrable Mminus μ)
    (hb : ∀ p, ∀ᵐ x ∂μ, ‖(g p x).1‖ ≤ Mplus x ∧ ‖(g p x).2‖ ≤ Mminus x) :
    ∀ p, Integrable (g p) μ ∧
      (∫ x, ‖g p x‖ ∂μ) ≤ (∫ x, Mplus x ∂μ) + (∫ x, Mminus x ∂μ) ∧
      (∫ x, g p x ∂μ) = (∫ x, (g p x).1 ∂μ, ∫ x, (g p x).2 ∂μ) := by
  intro p
  have hdom : ∀ᵐ x ∂μ, ‖g p x‖ ≤ (Mplus + Mminus) x := by
    filter_upwards [hb p] with x hx
    rw [Prod.norm_def]
    change max ‖(g p x).1‖ ‖(g p x).2‖ ≤ Mplus x + Mminus x
    apply max_le
    · linarith [hx.1, hx.2, norm_nonneg (g p x).2]
    · linarith [hx.1, hx.2, norm_nonneg (g p x).1]
  have hi := (hplus.add hminus).mono' (hg p) hdom
  refine ⟨hi, ?_, Prod.ext (fst_integral hi) (snd_integral hi)⟩
  rw [← integral_add hplus hminus]
  exact integral_mono_ae hi.norm (hplus.add hminus) hdom

/-- Product norms remain submultiplicative for matrix-valued characters. -/
theorem character_pair_norm_submultiplicative {B : Type*} [NormedRing B]
    (x y : B × B) : ‖x * y‖ ≤ ‖x‖ * ‖y‖ := norm_mul_le x y

/-- The two scalar character idempotents in the literal polynomial quotient. -/
def projectorPlus : QuotientCarrier := quotientCharacterEquiv.symm (1, 0)
def projectorMinus : QuotientCarrier := quotientCharacterEquiv.symm (0, 1)

@[simp] theorem projectors_sum : projectorPlus + projectorMinus = 1 := by
  apply quotientCharacterEquiv.injective
  simp [projectorPlus, projectorMinus]

@[simp] theorem projectorPlus_idempotent : projectorPlus * projectorPlus = projectorPlus := by
  apply quotientCharacterEquiv.injective
  simp [projectorPlus]

@[simp] theorem projectorMinus_idempotent : projectorMinus * projectorMinus = projectorMinus := by
  apply quotientCharacterEquiv.injective
  simp [projectorMinus]

@[simp] theorem projectors_orthogonal : projectorPlus * projectorMinus = 0 := by
  apply quotientCharacterEquiv.injective
  simp [projectorPlus, projectorMinus]

theorem projectorPlus_formula :
    projectorPlus = (1 / 2 : ℂ) • (1 + AdjoinRoot.root relation) := by
  apply quotientCharacterEquiv.injective
  simp [projectorPlus]
  ext <;> norm_num [generator]

theorem projectorMinus_formula :
    projectorMinus = (1 / 2 : ℂ) • (1 - AdjoinRoot.root relation) := by
  apply quotientCharacterEquiv.injective
  simp [projectorMinus]
  ext <;> norm_num [generator]

/-- Exact two-character reconstruction in the quotient presentation. -/
theorem quotient_character_reconstruction (z : QuotientCarrier) :
    z = (quotientCharacterEquiv z).1 • projectorPlus +
      (quotientCharacterEquiv z).2 • projectorMinus := by
  apply quotientCharacterEquiv.injective
  simp [projectorPlus, projectorMinus]

/-- The displayed projector-sum integral identity from prop:character-majorants. -/
theorem quotient_projector_integral_reconstruction {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {g : X → QuotientCarrier} (hg : Integrable g μ) :
    (∫ x, g x ∂μ) = (∫ x, (quotientCharacterEquiv (g x)).1 ∂μ) • projectorPlus +
      (∫ x, (quotientCharacterEquiv (g x)).2 ∂μ) • projectorMinus := by
  apply quotientCharacterEquiv.injective
  rw [quotient_character_integral_reconstruction hg]
  simp [projectorPlus, projectorMinus]

/-- Integral norm bound for the quotient's own declared character norm. -/
theorem quotient_character_integral_norm_bound {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {g : X → QuotientCarrier} {Mplus Mminus : X → ℝ}
    (hg : AEStronglyMeasurable g μ) (hplus : Integrable Mplus μ) (hminus : Integrable Mminus μ)
    (hb : ∀ᵐ x ∂μ, ‖(quotientCharacterEquiv (g x)).1‖ ≤ Mplus x ∧
      ‖(quotientCharacterEquiv (g x)).2‖ ≤ Mminus x) :
    (∫ x, ‖g x‖ ∂μ) ≤ (∫ x, Mplus x ∂μ) + ∫ x, Mminus x ∂μ := by
  have hm := quotientCharacterIsometry.continuous.comp_aestronglyMeasurable hg
  have h := character_integral_norm_bound hm hplus hminus hb
  exact h

/-- Uniform complete-graph estimates in the literal quotient carrier. -/
theorem quotient_character_uniform_estimate {X P : Type*} [MeasurableSpace X]
    {μ : Measure X} {g : P → X → QuotientCarrier} {Mplus Mminus : X → ℝ}
    (hg : ∀ p, AEStronglyMeasurable (g p) μ)
    (hplus : Integrable Mplus μ) (hminus : Integrable Mminus μ)
    (hb : ∀ p, ∀ᵐ x ∂μ, ‖(quotientCharacterEquiv (g p x)).1‖ ≤ Mplus x ∧
      ‖(quotientCharacterEquiv (g p x)).2‖ ≤ Mminus x) :
    ∀ p, Integrable (g p) μ ∧
      (∫ x, ‖g p x‖ ∂μ) ≤ (∫ x, Mplus x ∂μ) + (∫ x, Mminus x ∂μ) ∧
      (∫ x, g p x ∂μ) =
        (∫ x, (quotientCharacterEquiv (g p x)).1 ∂μ) • projectorPlus +
        (∫ x, (quotientCharacterEquiv (g p x)).2 ∂μ) • projectorMinus := by
  intro p
  have hi := quotient_character_majorant_integrable (hg p) hplus hminus (hb p)
  exact ⟨hi, quotient_character_integral_norm_bound (hg p) hplus hminus (hb p),
    quotient_projector_integral_reconstruction hi⟩

end UV.Carrier
