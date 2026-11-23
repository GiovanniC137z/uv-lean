import UV.ContinueOmegaResultContact

/-! Recover the exact one-point curvature covariance from the Fourier
two-point law at any finite cutoff. The normalization is that each torus
character is unimodular and the Fourier covariance is diagonal in mode. -/

noncomputable section
open MeasureTheory
open scoped Matrix ComplexConjugate ComplexOrder MatrixOrder
namespace UV

private theorem contact_pair_finite {α β Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (s : Finset α) (t : Finset β) (X : α → Ω → ℂ) (Y : β → Ω → ℂ)
    (c : α → ℂ) (d : β → ℂ)
    (hi : ∀ i ∈ s, ∀ j ∈ t, Integrable (fun x => X i x*conj (Y j x)) μ) :
    let F := fun x => (∑ i ∈ s, c i*X i x) * conj (∑ j ∈ t, d j*Y j x)
    Integrable F μ ∧ (∫ x, F x ∂μ) =
        ∑ i ∈ s, ∑ j ∈ t, (c i*conj (d j))*(∫ x, X i x*conj (Y j x) ∂μ) := by
  let Z := fun i j x => (c i*conj (d j))*(X i x*conj (Y j x))
  have hZ i (hh : i ∈ s) j (hj : j ∈ t) : Integrable (Z i j) μ := (hi i hh j hj).const_mul _
  have hs i (hh : i ∈ s) : Integrable (fun x => ∑ j ∈ t, Z i j x) μ :=
    integrable_finset_sum _ (hZ i hh)
  have he x : (∑ i ∈ s, c i*X i x) * conj (∑ j ∈ t, d j*Y j x) =
      ∑ i ∈ s, ∑ j ∈ t, Z i j x := by
    rw [map_sum,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by simp only [Z,map_mul]; ring
  dsimp only
  simp_rw [he]
  refine ⟨integrable_finset_sum _ hs,?_⟩
  rw [integral_finset_sum _ hs]
  apply Finset.sum_congr rfl
  intro i hh
  rw [integral_finset_sum _ (hZ i hh)]
  exact Finset.sum_congr rfl fun j _ => integral_const_mul _ _

def contactFourierPhase (p : CurvatureMode) (z : Fin 4 → ℝ) : ℂ :=
  Complex.I * Complex.exp (Complex.I*((∑ k, (p.val k:ℝ)*z k : ℝ):ℂ))

private theorem contact_phase_conj (p : CurvatureMode) (z : Fin 4 → ℝ) :
    contactFourierPhase p z * conj (contactFourierPhase p z) = 1 := by
  have h : ‖contactFourierPhase p z‖ = 1 := by
    simp [contactFourierPhase,Complex.norm_exp]
  rw [mul_comm,←Complex.normSq_eq_conj_mul_self,←Complex.sq_norm,h]
  norm_num

def contactCutoffCurvature {Ω : Type*} (s : Finset CurvatureMode) (z : Fin 4 → ℝ)
    (A : CurvatureMode → Fin 4 → Ω → ℂ) (i : Fin 6) (x : Ω) : ℂ :=
  ∑ p ∈ s, contactFourierPhase p z * ∑ a, contactExterior p i a * A p a x

/-- The finite-cutoff covariance is derived from the potential modes before
forming the local polynomial. The Fourier phases cancel and the resulting
one-point matrix is translation independent. The real-field reality
condition can be imposed on any symmetric cutoff. -/
theorem contact_cutoff_covariance {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (s : Finset CurvatureMode) (D : CurvatureMode → Matrix (Fin 4) (Fin 4) ℂ)
    (A : CurvatureMode → Fin 4 → Ω → ℂ)
    (hi : ∀ p ∈ s, ∀ q ∈ s, ∀ a b, Integrable (fun x => A p a x * conj (A q b x)) μ)
    (hD : ∀ p ∈ s, ∀ q ∈ s, ∀ a b, (∫ x, A p a x*conj (A q b x) ∂μ) =
      if p = q then D p a b else 0)
    (z : Fin 4 → ℝ) (i j : Fin 6) :
    let F := fun x => contactCutoffCurvature s z A i x * conj (contactCutoffCurvature s z A j x)
    Integrable F μ ∧ (∫ x, F x ∂μ) = ∑ p ∈ s, contactCurvatureCov p (D p) i j := by
  let U := fun (i : Fin 6) p x => ∑ a, contactExterior p i a * A p a x
  have hp p (hp : p ∈ s) q (hq : q ∈ s) :=
    contact_pair_finite μ Finset.univ Finset.univ (A p) (A q) (contactExterior p i) (contactExterior q j)
      (fun a _ b _ => hi p hp q hq a b)
  have hh := contact_pair_finite μ s s (U i) (U j) (fun p => contactFourierPhase p z)
    (fun p => contactFourierPhase p z) (fun p hp' q hq' => (hp p hp' q hq').1)
  refine ⟨hh.1,hh.2.trans ?_⟩
  apply Finset.sum_congr rfl
  intro p hs
  rw [Finset.sum_eq_single_of_mem p hs]
  · rw [contact_phase_conj,one_mul,(hp p hs p hs).2]
    simp_rw [hD p hs p hs,if_true]
    simp only [contactCurvatureCov,Matrix.mul_apply,Matrix.conjTranspose_apply,Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    exact Finset.sum_congr rfl fun b _ => by change _ * conj _ * _ = _ * _ * conj _; ring
  · intro q hq hqp
    rw [(hp p hs q hq).2]
    simp [hD p hs q hq,hqp.symm]

def contactAt (N : ℕ) (C : Matrix (Fin 6) (Fin 6) ℂ) (u : ℝ) :=
  (N:ℝ)*C.trace.re + 2*(N:ℝ)*(N-1:ℝ)*(star (contactRotatingProbe u) ⬝ᵥ C*ᵥ contactRotatingProbe u).re

private theorem contact_at_cont (N : ℕ) (C : Matrix (Fin 6) (Fin 6) ℂ) :
    Continuous (contactAt N C) := by
  have hc (i : Fin 6) : Continuous (fun u => contactRotatingProbe u i) := by
    fin_cases i <;> simp [contactRotatingProbe] <;> fun_prop
  unfold contactAt Matrix.mulVec dotProduct
  apply continuous_const.add
  apply continuous_const.mul
  apply Complex.continuous_re.comp
  exact continuous_finset_sum _ (fun i _ => (hc i).star.mul (continuous_finset_sum _ (fun j _ => continuous_const.mul (hc j))))

private theorem contact_at_add (N : ℕ) (C B : Matrix (Fin 6) (Fin 6) ℂ) (u : ℝ) :
    contactAt N (C+B) u = contactAt N C u + contactAt N B u := by
  simp only [contactAt,Matrix.trace_add,Matrix.add_mulVec,dotProduct_add,Complex.add_re,mul_add]
  ring

/-- Add the full Fourier covariance before taking the source derivative,
as required by a complete one-vertex diagram. The cutoff response
is the finite sum of the one-mode responses used in the necessity proof. -/
theorem contact_cutoff_complete (N : ℕ) (D : CurvatureMode → Matrix (Fin 4) (Fin 4) ℂ)
    (s : Finset CurvatureMode) :
    (∫ u in (0:ℝ)..1, contactAt N (∑ p ∈ s, contactCurvatureCov p (D p)) u) =
      ∑ p ∈ s, contactProbeMode N p (D p) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [contactAt]
  | @insert p s hp ih =>
    rw [Finset.sum_insert hp,Finset.sum_insert hp]
    simp_rw [contact_at_add]
    rw [intervalIntegral.integral_add ((contact_at_cont _ _).intervalIntegrable _ _)
      ((contact_at_cont _ _).intervalIntegrable _ _),ih]
    rfl

/-- Remove all photon-mode cutoffs in the same routed graph. Every finite
set of assigned line momenta is eventually present in any exhausting
cutoff; joint absolute integrability controls the limit. -/
theorem contact_cutoff_limit {I : ℕ} (μ : Measure (Fin I → CurvatureMode)) (F : (Fin I → CurvatureMode) → ℂ)
    (hF : Integrable F μ) (s : ℕ → Finset CurvatureMode)
    (hs : ∀ p, ∀ᶠ k in Filter.atTop, p ∈ s k) :
    Filter.Tendsto (fun k => ∫ q, ({q : Fin I → CurvatureMode | ∀ e, q e ∈ s k}.indicator F) q ∂μ)
      Filter.atTop (nhds (∫ q, F q ∂μ)) := by
  apply tendsto_integral_filter_of_dominated_convergence (fun q => ‖F q‖)
  · exact Filter.Eventually.of_forall fun k => (measurable_of_countable _).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun k => ae_of_all _ fun q => by
      by_cases h : ∀ e, q e ∈ s k <;> simp [h]
  · exact hF.norm
  · apply ae_of_all
    intro q
    have he := (Filter.eventually_all).mpr (fun e => hs (q e))
    apply tendsto_const_nhds.congr'
    filter_upwards [he] with k hk
    simp [hk]

/-- At symmetric cutoffs where the Fourier potential is real, evaluate the
ordinary expectation of the actual local source polynomial. Only second
moments of the potential modes enter this contact. -/
theorem contact_physical_probe_coefficient {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (s : Finset CurvatureMode) (D : CurvatureMode → Matrix (Fin 4) (Fin 4) ℂ)
    (A : CurvatureMode → Fin 4 → Ω → ℂ)
    (hi : ∀ p ∈ s, ∀ q ∈ s, ∀ a b, Integrable (fun x => A p a x * conj (A q b x)) μ)
    (hD : ∀ p ∈ s, ∀ q ∈ s, ∀ a b, (∫ x, A p a x*conj (A q b x) ∂μ) =
      if p = q then D p a b else 0)
    (z : Fin 4 → ℝ) (G : Fin 6 → Ω → ℝ)
    (hreal : ∀ i x, (G i x : ℂ) = contactCutoffCurvature s z A i x) (N : ℕ) (u : ℝ) :
    let f := fun j => (contactRotatingProbe u j).re
    (∫ x, ((1 + Polynomial.C (2*(∑ i, f i*G i x))*Polynomial.X +
      Polynomial.C (∑ i, (G i x)^2)*Polynomial.X^2 : Polynomial ℝ)^N).coeff 2 ∂μ) =
      contactAt N (∑ p ∈ s, contactCurvatureCov p (D p)) u := by
  let C := ∑ p ∈ s, contactCurvatureCov p (D p)
  let f := fun j => (contactRotatingProbe u j).re
  have hf (i : Fin 6) : ((f i : ℝ):ℂ) = contactRotatingProbe u i := by
    fin_cases i <;> rfl
  have hcov (i j) := contact_cutoff_covariance μ s D A hi hD z i j
  have he (i j) : (fun x => (G i x*G j x:ℂ)) =
      fun x => contactCutoffCurvature s z A i x * conj (contactCutoffCurvature s z A j x) := by
    funext x
    rw [←hreal,←hreal,Complex.conj_ofReal]
  have hG (i j) : Integrable (fun x => G i x*G j x) μ := by
    have hh := (hcov i j).1
    rw [←he] at hh
    have hh' : Integrable (fun x => (G i x * G j x : ℂ).re) μ := hh.re
    simpa only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] using hh'
  have hm (i j) : (∫ x, G i x*G j x ∂μ) = (C i j).re := by
    have hh := congrArg Complex.re (hcov i j).2
    dsimp only at hh
    rw [←he] at hh
    simp_rw [←Complex.ofReal_mul] at hh
    rw [integral_complex_ofReal] at hh
    simpa only [C,Matrix.sum_apply,Complex.ofReal_re] using hh
  dsimp only
  rw [contact_probe_wick μ G hG]
  change (N:ℝ)*(∑ i, ∫ x, G i x*G i x ∂μ) + _ = contactAt N C u
  simp_rw [hm]
  unfold contactAt
  simp only [Matrix.trace,Matrix.diag_apply,Complex.re_sum]
  congr 2
  simp only [←hf,dotProduct,Matrix.mulVec,Pi.star_apply,Complex.star_def,Complex.conj_ofReal,
    Finset.mul_sum,Complex.re_sum,Complex.mul_re,Complex.ofReal_im,zero_mul,mul_zero,
    Complex.ofReal_re,sub_zero]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

def contactNegative (p : CurvatureMode) : CurvatureMode := ⟨-p.val,neg_ne_zero.mpr p.property⟩

@[simp] theorem contact_negative_involutive (p : CurvatureMode) : contactNegative (contactNegative p) = p := by
  exact Subtype.ext (neg_neg _)

private theorem contact_exterior_negative (p : CurvatureMode) (i : Fin 6) (a : Fin 4) :
    contactExterior (contactNegative p) i a = -(conj (contactExterior p i a)) := by
  fin_cases i <;> fin_cases a <;> simp [contactNegative,contactExterior,contactPhotonVector]

private theorem contact_phase_negative (p : CurvatureMode) (z : Fin 4 → ℝ) :
    contactFourierPhase (contactNegative p) z = -(conj (contactFourierPhase p z)) := by
  simp [contactFourierPhase,contactNegative,←Complex.exp_conj,Finset.sum_neg_distrib]

/-- On a symmetric Fourier cutoff, conjugate potential modes automatically
give a real curvature field. Its two signs under reflection come from
the factor i and the exterior momentum, respectively. -/
theorem contact_cutoff_real {Ω : Type*} (s : Finset CurvatureMode)
    (hs : ∀ p ∈ s, contactNegative p ∈ s) (z : Fin 4 → ℝ)
    (A : CurvatureMode → Fin 4 → Ω → ℂ)
    (hA : ∀ p ∈ s, ∀ a x, A (contactNegative p) a x = conj (A p a x))
    (i : Fin 6) (x : Ω) :
    ((contactCutoffCurvature s z A i x).re : ℂ) = contactCutoffCurvature s z A i x := by
  apply Complex.conj_eq_iff_re.mp
  unfold contactCutoffCurvature
  rw [map_sum]
  apply Finset.sum_bij' (fun p _ => contactNegative p) (fun p _ => contactNegative p)
  · exact hs
  · exact hs
  · exact fun p _ => contact_negative_involutive p
  · exact fun p _ => contact_negative_involutive p
  · intro p hp
    simp only [map_mul,map_sum,contact_phase_negative,contact_exterior_negative,hA p hp,neg_mul,
      Finset.sum_neg_distrib,mul_neg,neg_neg]

/-- At positive external degree the zero-source partition subtraction
cannot cancel the one-vertex contact used in the converse. -/
theorem contact_vacuum_subtraction (P : Polynomial ℝ) (c : ℝ) {N : ℕ} (hN : 2 ≤ N) :
    (P-Polynomial.C c).coeff (2*N-2) = P.coeff (2*N-2) := by
  have hn : 2*N-2 ≠ 0 := by omega
  simp [Polynomial.coeff_C,hn]

/-- The graphwise criterion consists of two implications: the actual
complete contact tests the budget, and the tested budget controls every
finite component contraction with arbitrary fixed external Fourier data. -/
theorem contact_graphwise_criterion (N : ℕ) (hN : 2 ≤ N)
    (D : CurvatureMode → Matrix (Fin 4) (Fin 4) ℂ)
    (hD : ∀ p, (D p).PosSemidef) (hT : ∀ p, D p *ᵥ contactPhotonVector p = 0) :
    Summable (fun p => contactModeSquare p*(D p).trace.re) ↔
    (Summable (fun p => contactProbeMode N p (D p)) ∧
      ∀ (I : ℕ) (i j : Fin I → Fin 6) (c : (Fin I → CurvatureMode) → ℂ) (C : ℝ),
      (∀ q, ‖c q‖ ≤ C) → Integrable (fun q => c q * ∏ e, contactCurvatureCov (q e) (D (q e)) (i e) (j e))
        (Measure.pi (fun _ : Fin I => (Measure.count : Measure CurvatureMode)))) := by
  constructor
  · intro hb
    exact ⟨(contact_probe_summable_iff N hN D hD hT).mpr hb,
      fun _ i j c C hc => (contact_finite_graph D hD hT hb i j c C hc).1⟩
  · exact fun h => (contact_probe_summable_iff N hN D hD hT).mp h.1

end UV
