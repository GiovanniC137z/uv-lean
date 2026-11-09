import UV.JordanObservableContourError
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! Actual operator residues in arbitrary compatible operator norms.
The fixed algebra equivalence supplies coordinates only for the determinant
and adjugate construction. All inverse estimates, contour integrals and
residue errors remain in the original continuous-linear-map norm. -/

noncomputable section
open Set Filter Metric Complex
open scoped Topology Matrix.Norms.L2Operator NNReal

namespace UV

variable {H In Out : Type*}
  [NormedAddCommGroup H] [NormedSpace ℂ H]
  [NormedAddCommGroup In] [NormedSpace ℂ In]
  [NormedAddCommGroup Out] [NormedSpace ℂ Out]

def compatibleOperatorObservable (K : ℂ → H →L[ℂ] H)
    (U : ℂ → H →L[ℂ] Out) (V : ℂ → In →L[ℂ] H) (z : ℂ) : In →L[ℂ] Out :=
  (U z).comp ((Ring.inverse (K z)).comp (V z))

section Coordinates

variable {n : Type*} [Fintype n] [DecidableEq n] [FiniteDimensional ℂ H]
  (e : (H →L[ℂ] H) ≃ₐ[ℂ] Matrix n n ℂ)

/-- Every specified finite basis supplies the required algebra coordinates.
The basis need not be orthogonal or normalized. -/
def compatibleOperatorCoordinatesOfBasis (b : Module.Basis n ℂ H) :
    (H →L[ℂ] H) ≃ₐ[ℂ] Matrix n n ℂ :=
  (Module.End.toContinuousLinearMap (𝕜 := ℂ) H).symm.trans (LinearMap.toMatrixAlgEquiv b)

def compatibleOperatorDeterminant (K : ℂ → H →L[ℂ] H) (z : ℂ) : ℂ := (e (K z)).det

def compatibleOperatorAdjugate (K : ℂ → H →L[ℂ] H) (z : ℂ) : H →L[ℂ] H :=
  e.symm ((e (K z)).adjugate)

def compatibleOperatorNumerator (K : ℂ → H →L[ℂ] H)
    (U : ℂ → H →L[ℂ] Out) (V : ℂ → In →L[ℂ] H) (z : ℂ) : In →L[ℂ] Out :=
  (U z).comp ((compatibleOperatorAdjugate e K z).comp (V z))

omit [FiniteDimensional ℂ H] in
/-- Algebra coordinates preserve the genuine everywhere-defined ring inverse,
including its value at nonunits. -/
theorem compatibleOperator_map_inverse (A : H →L[ℂ] H) :
    e (Ring.inverse A) = Ring.inverse (e A) := by
  by_cases hA : IsUnit A
  · have heA : IsUnit (e A) := hA.map e.toMonoidHom
    have hc : e A * e (Ring.inverse A) = 1 := by
      rw [← map_mul, Ring.mul_inverse_cancel A hA, map_one]
    calc
      e (Ring.inverse A) = Ring.inverse (e A) * (e A * e (Ring.inverse A)) := by
        rw [← mul_assoc, Ring.inverse_mul_cancel _ heA, one_mul]
      _ = Ring.inverse (e A) := by rw [hc,mul_one]
  · have heA : ¬ IsUnit (e A) := fun h => hA (by
        have hh : IsUnit (e.symm (e A)) := h.map e.symm.toMonoidHom
        simpa only [AlgEquiv.symm_apply_apply] using hh)
    rw [Ring.inverse_non_unit _ hA, map_zero, Ring.inverse_non_unit _ heA]

omit [FiniteDimensional ℂ H] in
theorem compatibleOperator_isUnit_iff (A : H →L[ℂ] H) :
    IsUnit A ↔ (e A).det ≠ 0 := by
  constructor
  · intro h
    exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp (h.map e.toMonoidHom))
  · intro h
    have hu : IsUnit (e A) := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr h)
    have hh : IsUnit (e.symm (e A)) := hu.map e.symm.toMonoidHom
    simpa only [AlgEquiv.symm_apply_apply] using hh

omit [FiniteDimensional ℂ H] in
/-- The actual inverse is the coordinate adjugate divided by its determinant;
this is derived from the matrix inverse definition rather than assumed. -/
theorem compatibleOperator_inverse_adjugate_quotient (K : ℂ → H →L[ℂ] H) (z : ℂ) :
    Ring.inverse (K z) = (compatibleOperatorDeterminant e K z)⁻¹ •
      compatibleOperatorAdjugate e K z := by
  apply e.injective
  rw [compatibleOperator_map_inverse, ← Matrix.nonsing_inv_eq_ringInverse,
    Matrix.inv_def, Ring.inverse_eq_inv]
  simp only [compatibleOperatorDeterminant,compatibleOperatorAdjugate,
    map_smul,AlgEquiv.apply_symm_apply]

omit [FiniteDimensional ℂ H] in
theorem compatibleOperator_observable_quotient (K : ℂ → H →L[ℂ] H)
    (U : ℂ → H →L[ℂ] Out) (V : ℂ → In →L[ℂ] H) (z : ℂ) :
    compatibleOperatorObservable K U V z =
      (compatibleOperatorDeterminant e K z)⁻¹ • compatibleOperatorNumerator e K U V z := by
  unfold compatibleOperatorObservable compatibleOperatorNumerator
  rw [compatibleOperator_inverse_adjugate_quotient e,
    ContinuousLinearMap.smul_comp,ContinuousLinearMap.comp_smul]

theorem compatibleOperator_coordinates_analyticOnNhd
    {K : ℂ → H →L[ℂ] H} {D : Set ℂ} (hK : AnalyticOnNhd ℂ K D) :
    AnalyticOnNhd ℂ (fun z => e (K z)) D := by
  intro z hz
  exact (e.toLinearEquiv.toContinuousLinearEquiv.toContinuousLinearMap.analyticAt (K z)).comp (hK z hz)

theorem compatibleOperator_determinant_analyticOnNhd
    {K : ℂ → H →L[ℂ] H} {D : Set ℂ} (hK : AnalyticOnNhd ℂ K D) :
    AnalyticOnNhd ℂ (compatibleOperatorDeterminant e K) D :=
  matrixContour_det_analyticOnNhd (compatibleOperator_coordinates_analyticOnNhd e hK)

theorem compatibleOperator_adjugate_analyticOnNhd
    {K : ℂ → H →L[ℂ] H} {D : Set ℂ} (hK : AnalyticOnNhd ℂ K D) :
    AnalyticOnNhd ℂ (compatibleOperatorAdjugate e K) D := by
  have ha := matrixContour_adjugate_analyticOnNhd (compatibleOperator_coordinates_analyticOnNhd e hK)
  intro z hz
  exact (e.symm.toLinearEquiv.toContinuousLinearEquiv.toContinuousLinearMap.analyticAt
    ((e (K z)).adjugate)).comp (f := fun w : ℂ => (e (K w)).adjugate) (ha z hz)

end Coordinates

/-- Composition is analytic for the original normed spaces; no coordinates
or replacement norm are used in this operation. -/
theorem compatibleOperator_comp_analyticOnNhd
    {A : ℂ → H →L[ℂ] Out} {B : ℂ → In →L[ℂ] H} {D : Set ℂ}
    (hA : AnalyticOnNhd ℂ A D) (hB : AnalyticOnNhd ℂ B D) :
    AnalyticOnNhd ℂ (fun z => (A z).comp (B z)) D := by
  intro z hz
  exact ((ContinuousLinearMap.compL ℂ In H Out).analyticAt_bilinear (A z,B z)).comp₂
    (hA z hz) (hB z hz)

/-- Ordered Neumann error in the original compatible operator norms. The
input and output spaces may differ, and no coordinate-map norm enters. -/
theorem compatibleOperator_observable_neumann_error
    [CompleteSpace H]
    (X Y : H →L[ℂ] H) (U : H →L[ℂ] Out) (V : In →L[ℂ] H)
    {B ε Lo Li : ℝ} (hY : IsUnit Y) (hB : ‖Ring.inverse Y‖ ≤ B)
    (hε : ‖X-Y‖ ≤ ε) (hq : B*ε < 1) (hLo : ‖U‖ ≤ Lo) (hLi : ‖V‖ ≤ Li) :
    ‖U.comp ((Ring.inverse X).comp V)-U.comp ((Ring.inverse Y).comp V)‖ ≤
      Lo*Li*B^2*ε/(1-B*ε) := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans hB
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans hε
  have hLo0 : 0 ≤ Lo := (norm_nonneg _).trans hLo
  have hLi0 : 0 ≤ Li := (norm_nonneg _).trans hLi
  have hden : 0 < 1-B*ε := sub_pos.mpr hq
  cases subsingleton_or_nontrivial H with
  | inl h =>
    letI := h
    have hU : U = 0 := Subsingleton.elim _ _
    simp only [hU,ContinuousLinearMap.zero_comp,sub_self,norm_zero]
    positivity
  | inr h =>
    letI := h
    have hdiff : ‖Ring.inverse X-Ring.inverse Y‖ ≤ B^2*ε/(1-B*ε) := by
      have hr := response_resolvent_error hY hB
        (show ‖Y-X‖ ≤ ε by simpa only [norm_sub_rev] using hε) hq
      have he : Y-(Y-X) = X := by abel
      simpa only [he] using hr
    rw [← ContinuousLinearMap.comp_sub,← ContinuousLinearMap.sub_comp]
    calc
      _ ≤ ‖U‖*‖(Ring.inverse X-Ring.inverse Y).comp V‖ := U.opNorm_comp_le _
      _ ≤ ‖U‖*(‖Ring.inverse X-Ring.inverse Y‖*‖V‖) :=
        mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)
      _ ≤ Lo*((B^2*ε/(1-B*ε))*Li) := by gcongr
      _ = _ := by ring

section Residues

variable {n : Type*} [Fintype n] [DecidableEq n]
  [CompleteSpace H] [CompleteSpace Out]
  [FiniteDimensional ℂ H]
  (e : (H →L[ℂ] H) ≃ₐ[ℂ] Matrix n n ℂ)

omit [CompleteSpace H] [CompleteSpace Out] in
theorem compatibleOperator_numerator_analyticOnNhd
    {K : ℂ → H →L[ℂ] H} {U : ℂ → H →L[ℂ] Out} {V : ℂ → In →L[ℂ] H}
    {D : Set ℂ} (hK : AnalyticOnNhd ℂ K D)
    (hU : AnalyticOnNhd ℂ U D) (hV : AnalyticOnNhd ℂ V D) :
    AnalyticOnNhd ℂ (compatibleOperatorNumerator e K U V) D :=
  compatibleOperator_comp_analyticOnNhd hU
    (compatibleOperator_comp_analyticOnNhd (compatibleOperator_adjugate_analyticOnNhd e hK) hV)

omit [CompleteSpace H] in
/-- The residue formula for actual inverse observables in their original
compatible norms on a genuine Jordan contour. -/
theorem jordanContour_compatibleOperator_residue
    {a p : ℂ} {κ : ℝ≥0} {C : Set ℂ}
    {K : ℂ → H →L[ℂ] H} {U : ℂ → H →L[ℂ] Out} {V : ℂ → In →L[ℂ] H}
    (hC : Schoenflies.IsJordanCurve (complexPlaneHomeomorph '' C))
    (γ : Path a a) (hLip : LipschitzWith κ γ.extend)
    (hmap : MapsTo γ.extend (Icc (0 : ℝ) 1) C)
    (havoid : ∀ t ∈ Icc (0 : ℝ) 1, γ.extend t ≠ p)
    (hpos : lipschitzContourWinding γ havoid = 1) (hp : p ∈ jordanFilledRegion C)
    (hK : AnalyticOnNhd ℂ K (jordanFilledRegion C))
    (hU : AnalyticOnNhd ℂ U (jordanFilledRegion C))
    (hV : AnalyticOnNhd ℂ V (jordanFilledRegion C))
    (hzero : compatibleOperatorDeterminant e K p = 0)
    (hderiv : deriv (compatibleOperatorDeterminant e K) p ≠ 0)
    (honly : ∀ z ∈ jordanFilledRegion C, z ≠ p → compatibleOperatorDeterminant e K z ≠ 0) :
    (2*Real.pi*I : ℂ)⁻¹ • parametrizedContourIntegral (compatibleOperatorObservable K U V) γ =
      simplePoleResidue (compatibleOperatorObservable K U V) p := by
  have he : compatibleOperatorObservable K U V = fun z =>
      (compatibleOperatorDeterminant e K z)⁻¹ • compatibleOperatorNumerator e K U V z :=
    funext (compatibleOperator_observable_quotient e K U V)
  rw [he]
  exact jordanContour_simple_denominator_residue hC γ hLip hmap havoid hpos hp
    (compatibleOperator_determinant_analyticOnNhd e hK)
    (compatibleOperator_numerator_analyticOnNhd e hK hU hV) hzero hderiv honly

omit [CompleteSpace H] [CompleteSpace Out] in
theorem compatibleOperator_observable_continuousOn
    {a p : ℂ} {C : Set ℂ}
    {K : ℂ → H →L[ℂ] H} {U : ℂ → H →L[ℂ] Out} {V : ℂ → In →L[ℂ] H}
    (γ : Path a a) (hmap : MapsTo γ.extend (Icc (0 : ℝ) 1) C)
    (havoid : ∀ t ∈ Icc (0 : ℝ) 1, γ.extend t ≠ p)
    (hK : AnalyticOnNhd ℂ K (jordanFilledRegion C))
    (hU : AnalyticOnNhd ℂ U (jordanFilledRegion C))
    (hV : AnalyticOnNhd ℂ V (jordanFilledRegion C))
    (honly : ∀ z ∈ jordanFilledRegion C, z ≠ p → compatibleOperatorDeterminant e K z ≠ 0) :
    ContinuousOn (fun t : ℝ => compatibleOperatorObservable K U V (γ.extend t))
      (Icc (0 : ℝ) 1) := by
  have hmapF : MapsTo γ.extend (Icc (0 : ℝ) 1) (jordanFilledRegion C) :=
    fun _ ht => subset_jordanFilledRegion C (hmap ht)
  have hd : ContinuousOn (compatibleOperatorDeterminant e K) (jordanFilledRegion C) :=
    fun z hz => (compatibleOperator_determinant_analyticOnNhd e hK z hz).continuousAt.continuousWithinAt
  have hn : ContinuousOn (compatibleOperatorNumerator e K U V) (jordanFilledRegion C) :=
    fun z hz => (compatibleOperator_numerator_analyticOnNhd e hK hU hV z hz).continuousAt.continuousWithinAt
  have hc :=
    ((hd.comp γ.continuous_extend.continuousOn hmapF).inv₀
      (fun t ht => honly _ (hmapF ht) (havoid t ht))).smul
      (hn.comp γ.continuous_extend.continuousOn hmapF)
  change ContinuousOn (fun t : ℝ => (compatibleOperatorDeterminant e K (γ.extend t))⁻¹ •
    compatibleOperatorNumerator e K U V (γ.extend t)) (Icc (0 : ℝ) 1) at hc
  simpa only [compatibleOperator_observable_quotient e] using hc

/-- Actual residue error in arbitrary compatible induced operator norms.
Coordinates are used only for the simple determinant poles. -/
theorem jordanContour_compatibleOperator_residue_error
    {a pX pY : ℂ} {κ : ℝ≥0} {C : Set ℂ}
    {KX KY : ℂ → H →L[ℂ] H} {U : ℂ → H →L[ℂ] Out} {V : ℂ → In →L[ℂ] H}
    {B ε Lo Li : ℝ}
    (hC : Schoenflies.IsJordanCurve (complexPlaneHomeomorph '' C))
    (γ : Path a a) (hLip : LipschitzWith κ γ.extend)
    (hmap : MapsTo γ.extend (Icc (0 : ℝ) 1) C)
    (havoidX : ∀ t ∈ Icc (0 : ℝ) 1, γ.extend t ≠ pX)
    (havoidY : ∀ t ∈ Icc (0 : ℝ) 1, γ.extend t ≠ pY)
    (hposX : lipschitzContourWinding γ havoidX = 1)
    (hposY : lipschitzContourWinding γ havoidY = 1)
    (hpX : pX ∈ jordanFilledRegion C) (hpY : pY ∈ jordanFilledRegion C)
    (hKX : AnalyticOnNhd ℂ KX (jordanFilledRegion C))
    (hKY : AnalyticOnNhd ℂ KY (jordanFilledRegion C))
    (hU : AnalyticOnNhd ℂ U (jordanFilledRegion C))
    (hV : AnalyticOnNhd ℂ V (jordanFilledRegion C))
    (hzeroX : compatibleOperatorDeterminant e KX pX = 0)
    (hzeroY : compatibleOperatorDeterminant e KY pY = 0)
    (hderivX : deriv (compatibleOperatorDeterminant e KX) pX ≠ 0)
    (hderivY : deriv (compatibleOperatorDeterminant e KY) pY ≠ 0)
    (honlyX : ∀ z ∈ jordanFilledRegion C, z ≠ pX → compatibleOperatorDeterminant e KX z ≠ 0)
    (honlyY : ∀ z ∈ jordanFilledRegion C, z ≠ pY → compatibleOperatorDeterminant e KY z ≠ 0)
    (hq : B*ε < 1)
    (hB : ∀ t ∈ Icc (0 : ℝ) 1, ‖Ring.inverse (KY (γ.extend t))‖ ≤ B)
    (hε : ∀ t ∈ Icc (0 : ℝ) 1, ‖KX (γ.extend t)-KY (γ.extend t)‖ ≤ ε)
    (hLo : ∀ t ∈ Icc (0 : ℝ) 1, ‖U (γ.extend t)‖ ≤ Lo)
    (hLi : ∀ t ∈ Icc (0 : ℝ) 1, ‖V (γ.extend t)‖ ≤ Li) :
    ‖simplePoleResidue (compatibleOperatorObservable KX U V) pX-
        simplePoleResidue (compatibleOperatorObservable KY U V) pY‖ ≤
      parametrizedContourLength γ/(2*Real.pi)*Lo*Li*B^2*ε/(1-B*ε) := by
  have hcX := compatibleOperator_observable_continuousOn e γ hmap havoidX hKX hU hV honlyX
  have hcY := compatibleOperator_observable_continuousOn e γ hmap havoidY hKY hU hV honlyY
  have hbound : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖compatibleOperatorObservable KX U V (γ.extend t)-
        compatibleOperatorObservable KY U V (γ.extend t)‖ ≤ Lo*Li*B^2*ε/(1-B*ε) := by
    intro t ht
    exact compatibleOperator_observable_neumann_error _ _ _ _
      ((compatibleOperator_isUnit_iff e _).mpr
        (honlyY _ (subset_jordanFilledRegion C (hmap ht)) (havoidY t ht)))
      (hB t ht) (hε t ht) hq (hLo t ht) (hLi t ht)
  rw [← jordanContour_compatibleOperator_residue e hC γ hLip hmap havoidX
      hposX hpX hKX hU hV hzeroX hderivX honlyX,
    ← jordanContour_compatibleOperator_residue e hC γ hLip hmap havoidY
      hposY hpY hKY hU hV hzeroY hderivY honlyY]
  exact (normalizedContour_difference_le γ
    (parametrizedContour_lipschitz_speed_integrable γ hLip)
    (parametrizedContour_lipschitz_integrable γ hLip hcX)
    (parametrizedContour_lipschitz_integrable γ hLip hcY) hbound).trans_eq (by ring)

end Residues

end UV
