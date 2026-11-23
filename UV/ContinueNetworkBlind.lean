import UV.ContinueNetworkDirectional
import UV.ContinueNetworkFourier
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.MeasureTheory.Measure.OpenPos

/-! The directional model on actual parallel momentum fibers. A common
unseen unit direction leaves the Gaussian and all massive factors fixed. -/

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators ENNReal InnerProductSpace Polynomial

namespace UV

theorem directionalNumerator_ray_polynomials {d : ℕ} (P : MvPolynomial (Fin d) ℂ)
    (x w : DirectionalMomentum d) :
    ∃ U V : ℝ[X], ∀ t : ℝ,
      (directionalNumerator P (x + t • w)).re = U.eval t ∧
      (directionalNumerator P (x + t • w)).im = V.eval t := by
  induction P using MvPolynomial.induction_on with
  | C a =>
      exact ⟨Polynomial.C a.re, Polynomial.C a.im, fun t => by simp [directionalNumerator]⟩
  | add p q hp hq =>
      obtain ⟨U, V, h⟩ := hp
      obtain ⟨U', V', h'⟩ := hq
      exact ⟨U + U', V + V', fun t => by
        simp only [directionalNumerator, map_add, Complex.add_re, Complex.add_im,
          Polynomial.eval_add, ← (h t).1, ← (h t).2, ← (h' t).1, ← (h' t).2]
        exact ⟨trivial, trivial⟩⟩
  | mul_X p i hp =>
      obtain ⟨U, V, h⟩ := hp
      let A : ℝ[X] := Polynomial.C (x i) + Polynomial.C (w i) * Polynomial.X
      refine ⟨U * A, V * A, fun t => ?_⟩
      have hA : A.eval t = (x + t • w) i := by
        simp only [A, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul,
          Polynomial.eval_X, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
        ring
      rw [Polynomial.eval_mul, Polynomial.eval_mul, hA, ← (h t).1, ← (h t).2]
      simp [directionalNumerator, Complex.mul_re, Complex.mul_im]

private theorem directionalPolynomial_tail_abs_ge (U : ℝ[X]) {t₀ : ℝ}
    (hU : U.eval t₀ ≠ 0) : ∃ c : ℝ, 0 < c ∧ ∀ᶠ t in atTop, c ≤ |U.eval t| := by
  by_cases hd : 0 < U.degree
  · exact ⟨1, zero_lt_one, (tendsto_atTop.1 ((Polynomial.abs_tendsto_atTop_iff U).2 hd)) 1⟩
  · have hC := Polynomial.eq_C_of_degree_le_zero (not_lt.mp hd)
    refine ⟨|U.eval t₀|, abs_pos.mpr hU, Eventually.of_forall fun t => ?_⟩
    conv_lhs => rw [hC]
    conv_rhs => rw [hC]
    simp

/-- Every nonzero affine-ray restriction is eventually bounded below
in norm on the positive half-line. -/
theorem directionalNumerator_ray_eventually_lower {d : ℕ} (P : MvPolynomial (Fin d) ℂ)
    (x w : DirectionalMomentum d) {t₀ : ℝ}
    (h₀ : directionalNumerator P (x + t₀ • w) ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ t : ℝ in atTop, c ≤ ‖directionalNumerator P (x + t • w)‖ := by
  obtain ⟨U, V, h⟩ := directionalNumerator_ray_polynomials P x w
  by_cases hre : U.eval t₀ = 0
  · have him : V.eval t₀ ≠ 0 := by
      intro hV
      apply h₀
      apply Complex.ext <;> simp [(h t₀).1, (h t₀).2, hre, hV]
    obtain ⟨c, hc, hbound⟩ := directionalPolynomial_tail_abs_ge V him
    exact ⟨c, hc, hbound.mono fun t ht => ht.trans (by rw [← (h t).2]; exact Complex.abs_im_le_norm _)⟩
  · obtain ⟨c, hc, hbound⟩ := directionalPolynomial_tail_abs_ge U hre
    exact ⟨c, hc, hbound.mono fun t ht => ht.trans (by rw [← (h t).1]; exact Complex.abs_re_le_norm _)⟩

theorem directional_not_integrable_of_eventually_pos {f : ℝ → ℝ} {c : ℝ}
    (hc : 0 < c) (hf : ∀ᶠ t in atTop, c ≤ f t) : ¬ Integrable f := by
  intro hI
  obtain ⟨T, hT⟩ := eventually_atTop.1 hf
  have hconst : IntegrableOn (fun _ : ℝ => c) (Ici T) := by
    apply (hI.integrableOn (s := Ici T)).mono' (by fun_prop)
    filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
    rw [Real.norm_of_nonneg hc.le]
    exact hT t ht
  have hvol := ((integrableOn_const_iff (by finiteness)).mp hconst).resolve_left
    (by simpa using hc.ne')
  exact (ne_of_lt hvol) Real.volume_Ici

/-- Extend one actual unit momentum direction to an orthonormal frame. -/
theorem directional_basis_with_unit {d : ℕ} (w : DirectionalMomentum (d + 1))
    (hw : ‖w‖ = 1) :
    ∃ b : OrthonormalBasis (Fin (d + 1)) ℝ (DirectionalMomentum (d + 1)), b 0 = w := by
  let s : Set (Fin (d + 1)) := {0}
  let v : Fin (d + 1) → DirectionalMomentum (d + 1) := fun _ => w
  have hv : Orthonormal ℝ (s.restrict v) := by
    rw [orthonormal_iff_ite]
    intro i j
    have hij : i = j := Subtype.ext (i.property.trans j.property.symm)
    simp [hij, v, Set.restrict, real_inner_self_eq_norm_sq, hw]
  obtain ⟨b, hb⟩ := hv.exists_orthonormalBasis_extension_of_card_eq (by
    simp [DirectionalMomentum, finrank_euclideanSpace])
  exact ⟨b, hb 0 (by simp [s])⟩

def directionalFiber {d : ℕ}
    (b : OrthonormalBasis (Fin (d + 1)) ℝ (DirectionalMomentum (d + 1)))
    (t : ℝ) (y : Fin d → ℝ) : DirectionalMomentum (d + 1) :=
  b.repr.symm (WithLp.toLp 2 (Fin.cons t y))

theorem directionalFiber_affine {d : ℕ}
    (b : OrthonormalBasis (Fin (d + 1)) ℝ (DirectionalMomentum (d + 1)))
    (t : ℝ) (y : Fin d → ℝ) :
    directionalFiber b t y = directionalFiber b 0 y + t • b 0 := by
  apply b.repr.injective
  simp only [directionalFiber, LinearIsometryEquiv.apply_symm_apply, map_add, map_smul,
    b.repr_self]
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [PiLp.add_apply, PiLp.smul_apply, EuclideanSpace.single_apply]
  · simp [PiLp.add_apply, PiLp.smul_apply, EuclideanSpace.single_apply, Fin.succ_ne_zero]

theorem directionalFiber_continuous_transverse {d : ℕ}
    (b : OrthonormalBasis (Fin (d + 1)) ℝ (DirectionalMomentum (d + 1))) (t : ℝ) :
    Continuous (directionalFiber b t) := by
  apply b.repr.symm.continuous.comp
  apply (PiLp.continuous_toLp 2 (fun _ : Fin (d + 1) => ℝ)).comp
  apply continuous_pi fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa only [Fin.cons_zero] using
      (continuous_const : Continuous (fun _ : Fin d → ℝ => t))
  · simpa only [Fin.cons_succ] using (continuous_apply j : Continuous fun y : Fin d → ℝ => y j)

theorem directionalFiber_integrable_ae {d : ℕ}
    (b : OrthonormalBasis (Fin (d + 1)) ℝ (DirectionalMomentum (d + 1)))
    {f : DirectionalMomentum (d + 1) → ℝ} (hf : Integrable f) :
    ∀ᵐ y : Fin d → ℝ, Integrable (fun t : ℝ => f (directionalFiber b t y)) := by
  let e₀ : DirectionalMomentum (d + 1) ≃ᵐ (Fin (d + 1) → ℝ) :=
    b.measurableEquiv.trans (EuclideanSpace.measurableEquiv (Fin (d + 1)))
  let e : DirectionalMomentum (d + 1) ≃ᵐ (ℝ × (Fin d → ℝ)) :=
    e₀.trans (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0)
  have he₀ : MeasurePreserving e₀ volume volume :=
    (EuclideanSpace.volume_preserving_measurableEquiv _).comp b.measurePreserving_measurableEquiv
  have he : MeasurePreserving e volume volume :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0).comp he₀
  have hI : Integrable (fun q => f (e.symm q))
      ((volume : Measure ℝ).prod (volume : Measure (Fin d → ℝ))) :=
    (he.symm e).integrable_comp_of_integrable hf
  apply hI.prod_left_ae.mono
  intro y hy
  convert hy using 1
  ext t
  congr 1
  have hrep : e.symm (t, y) =
      b.repr.symm (WithLp.toLp 2 ((0 : Fin (d + 1)).insertNth t y)) := rfl
  rw [hrep, Fin.insertNth_zero']
  rfl

private theorem directionalFiber_surjective {d : ℕ}
    (b : OrthonormalBasis (Fin (d + 1)) ℝ (DirectionalMomentum (d + 1)))
    (k : DirectionalMomentum (d + 1)) : ∃ t y, directionalFiber b t y = k := by
  refine ⟨b.repr k 0, fun j => b.repr k j.succ, ?_⟩
  apply b.repr.injective
  rw [directionalFiber, LinearIsometryEquiv.apply_symm_apply]
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

/-- If a coefficient is integrable, some fiber parallel to any given unit
direction is integrable and contains a point where a nonzero polynomial is
nonzero. Openness in the transverse directions supplies positive measure. -/
theorem directionalFiber_choose_integrable {d : ℕ}
    {f : DirectionalMomentum (d + 1) → ℝ} (hf : Integrable f)
    {P : MvPolynomial (Fin (d + 1)) ℂ} (hP : P ≠ 0)
    {u : DirectionalMomentum (d + 1)} (hu : ‖u‖ = 1) :
    ∃ (x : DirectionalMomentum (d + 1)) (t₀ : ℝ),
      directionalNumerator P (x + t₀ • u) ≠ 0 ∧
      Integrable (fun t : ℝ => f (x + t • u)) := by
  obtain ⟨b, hb⟩ := directional_basis_with_unit u hu
  have hae := directionalFiber_integrable_ae b hf
  obtain ⟨k₀, h₀⟩ := directionalNumerator_exists_ne_zero hP
  obtain ⟨t₀, y₀, heq⟩ := directionalFiber_surjective b k₀
  let O : Set (Fin d → ℝ) := {y | directionalNumerator P (directionalFiber b t₀ y) ≠ 0}
  have hO : IsOpen O := isOpen_ne_fun
    ((directionalNumerator_continuous P).comp (directionalFiber_continuous_transverse b t₀))
    continuous_const
  have hpos : 0 < volume O := hO.measure_pos volume ⟨y₀, by simpa [O, heq] using h₀⟩
  obtain ⟨y, hy, hiy⟩ := ((frequently_ae_mem_iff.2 hpos.ne').and_eventually hae).exists
  refine ⟨directionalFiber b 0 y, t₀, ?_, ?_⟩
  · simpa only [O, mem_setOf_eq, directionalFiber_affine b t₀ y, hb] using hy
  · have hline (t : ℝ) :
        directionalFiber b t y = directionalFiber b 0 y + t • u := by
      rw [directionalFiber_affine, hb]
    convert hiy using 1
    ext t
    rw [hline t]

variable {E : Type*} [Fintype E] {d : ℕ}
variable {V : E → Type*} [∀ e, NormedAddCommGroup (V e)] [∀ e, NormedSpace ℝ (V e)]

/-- A nonzero momentum direction invisible to the quadratic form,
drift, and every routed massive factor forces the literal absolute
polynomial integral to diverge. -/
theorem directionalAbsoluteModel_not_integrable_of_common_blind
    (Q : DirectionalMomentum (d + 1) →L[ℝ] DirectionalMomentum (d + 1))
    (h : DirectionalMomentum (d + 1))
    (C : ∀ e, DirectionalMomentum (d + 1) →L[ℝ] V e) (p : ∀ e, V e)
    (ν : E → ℝ) (P : MvPolynomial (Fin (d + 1)) ℂ)
    (hSym : ∀ k k', inner ℝ k (Q k') = inner ℝ k' (Q k))
    (hP : P ≠ 0)
    (w : DirectionalMomentum (d + 1)) (hw : w ≠ 0)
    (hQ : Q w = 0) (hh : inner ℝ h w = 0) (hC : ∀ e, C e w = 0) :
    ¬ Integrable (directionalAbsoluteModel Q h C p ν P) := by
  intro hI
  let u := ‖w‖⁻¹ • w
  have hu : ‖u‖ = 1 := by
    have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw
    simp [u, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hn.le), hn.ne']
  have huQ : Q u = 0 := by simp [u, hQ]
  have huh : inner ℝ h u = 0 := by simp [u, real_inner_smul_right, hh]
  have huC (e : E) : C e u = 0 := by simp [u, hC e]
  obtain ⟨x, t₀, hpy, hiy⟩ := directionalFiber_choose_integrable hI hP hu
  obtain ⟨c, hc, htail⟩ := directionalNumerator_ray_eventually_lower P x u hpy
  let Z := Real.exp (-inner ℝ x (Q x) + inner ℝ h x) *
    ∏ e, directionalMassiveFactor (ν e) (C e x + p e)
  have hZ : 0 < Z := mul_pos (Real.exp_pos _)
    (Finset.prod_pos fun e _ => directionalMassiveFactor_pos _ _)
  have hline (t : ℝ) : directionalAbsoluteModel Q h C p ν P (x + t • u) =
      ‖directionalNumerator P (x + t • u)‖ * Z := by
    have hux : inner ℝ u (Q x) = 0 := by rw [hSym, huQ, inner_zero_right]
    simp only [directionalAbsoluteModel, Z, map_add, map_smul, huQ, smul_zero, add_zero,
      inner_add_left, inner_add_right, real_inner_smul_left,
      real_inner_smul_right, hux, huh, huC, mul_zero, mul_assoc]
  apply directional_not_integrable_of_eventually_pos (mul_pos hc hZ) ?_ hiy
  filter_upwards [htail] with t ht
  rw [hline]
  exact mul_le_mul_of_nonneg_right ht hZ.le

end UV
