import UV.ContinueMomentumRoutingSectors

/-! External legs of a connected comparison graph. A photon test
contributes its own Schwartz weight. A tested charged path contributes
the transfer weight already extracted from its two endpoint packets. -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Filter
open scoped SchwartzMap

namespace UV

inductive MomentumExternalTest
  | photon (f : 𝓢(OSFourSpace,ℂ))
  | charged

def MomentumExternalTest.weight : MomentumExternalTest → OSFourSpace → ℝ
  | .photon f, k => ‖f k‖
  | .charged, k => normalPacketWeight k

theorem MomentumExternalTest.nonneg (p : MomentumExternalTest) (k : OSFourSpace) : 0 ≤ p.weight k := by
  cases p <;> first | exact norm_nonneg _ | exact (momentum_packet_weight_pos k).le

theorem MomentumExternalTest.measurable (p : MomentumExternalTest) : Measurable p.weight := by
  cases p with
  | photon f => exact f.continuous.norm.measurable
  | charged => exact ((measurable_const.add measurable_norm).pow_const 6).inv

theorem MomentumExternalTest.majorant (p : MomentumExternalTest) : ∃ C : ℝ, 0 ≤ C ∧ ∀ k, p.weight k ≤ C*normalPacketWeight k := by
  cases p with
  | charged => exact ⟨1,zero_le_one,fun _ => le_of_eq (one_mul _).symm⟩
  | photon f =>
    let C := (2:ℝ)^6*(Finset.Iic (6,0)).sup (fun m : ℕ × ℕ => SchwartzMap.seminorm ℝ m.1 m.2) f
    have h (p : OSFourSpace) : (1+‖p‖)^6*‖f p‖ ≤ C := by
      simpa only [C,norm_iteratedFDeriv_zero] using SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (6,0)) (le_refl 6) (le_refl 0) f p
    refine ⟨C,(by positivity : 0 ≤ (1+‖(0:OSFourSpace)‖)^6*‖f 0‖).trans (h 0),fun k => ?_⟩
    change ‖f k‖ ≤ C*((1+‖k‖)^6)⁻¹
    rw [←div_eq_mul_inv,le_div_iff₀ (by positivity),mul_comm]
    exact h k

theorem MomentumExternalTest.bounded (p : MomentumExternalTest) : ∃ C : ℝ, ∀ k, ‖p.weight k‖ ≤ C := by
  obtain ⟨C,hC,h⟩ := p.majorant
  refine ⟨C,fun k => ?_⟩
  rw [Real.norm_of_nonneg (p.nonneg k)]
  have h₁ : 1 ≤ (1+‖k‖)^6 := one_le_pow₀ (by linarith [norm_nonneg k])
  exact (h k).trans (mul_le_of_le_one_right hC (inv_le_one_of_one_le₀ h₁))

theorem MomentumExternalTest.integrable {A : Type*} [MeasurableSpace A] (p : MomentumExternalTest)
    (ι : A → OSFourSpace) (hm : Measurable ι) (σ : Measure A) (hσ : Integrable (fun k => normalPacketWeight (ι k)) σ) :
    Integrable (fun k => p.weight (ι k)) σ := by
  obtain ⟨C,_,h⟩ := p.majorant
  exact (hσ.const_mul C).mono' (p.measurable.comp hm).aestronglyMeasurable (Eventually.of_forall fun k => by
    rw [Real.norm_of_nonneg (p.nonneg _)]; exact h _)

def momentumExteriorTransfers {A : Type*} [AddCommGroup A] {n : ℕ} (x : Fin n → A) : Fin (n+1) → A :=
  Fin.cons ((0:A)-∑ j,x j) x

theorem momentum_exterior_conserved {A : Type*} [AddCommGroup A] {n : ℕ} (x : Fin n → A) : ∑ i,momentumExteriorTransfers x i = 0 := by
  simp [momentumExteriorTransfers,Fin.sum_univ_succ]

theorem momentum_exterior_unique {A : Type*} [AddCommGroup A] {n : ℕ} (k : Fin (n+1) → A) (hk : ∑ i,k i = 0) :
    momentumExteriorTransfers (fun j => k j.succ) = k := by
  have h := Fin.sum_univ_succ k
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [momentumExteriorTransfers,Fin.cons_zero]
    rw [hk] at h
    exact (zero_sub _).trans (eq_neg_of_add_eq_zero_left h.symm).symm
  · rfl

theorem momentum_exterior_absolute {A : Type*} [AddCommGroup A] [MeasurableSpace A] [MeasurableAdd₂ A] [MeasurableSub₂ A]
    (ι : A → OSFourSpace) (hm : Measurable ι) (σ : Measure A) [SigmaFinite σ]
    (hσ : Integrable (fun k => normalPacketWeight (ι k)) σ) {n : ℕ} (tests : Fin (n+1) → MomentumExternalTest) :
    Integrable (fun x : Fin n → A => ∏ i,(tests i).weight (ι (momentumExteriorTransfers x i))) (Measure.pi fun _ => σ) := by
  obtain ⟨C,hC⟩ := (tests 0).bounded
  exact momentum_external_tests_integrable σ (0 : A) (fun i k => (tests i).weight (ι k))
    C (fun k => hC _) (fun i => (tests i).measurable.comp hm) (fun i => (tests i.succ).integrable ι hm σ hσ)

theorem momentum_lattice_weight_count (b : NormalReciprocalBasis) :
    Integrable (fun k : NormalReciprocalLattice b => normalPacketWeight (k:OSFourSpace)) Measure.count :=
  (integrable_map_measure ((MomentumExternalTest.charged.measurable).aestronglyMeasurable) measurable_subtype_coe.aemeasurable).mp (momentum_lattice_weight b)

/-- Transfer the outer factor from the charged estimate into the tested
photon bound. The independent-transfer density alone may have infinite integral. -/
theorem momentum_external_photons {Y Q : Type*} [MeasurableSpace Y] [MeasurableSpace Q]
    (μ : Measure Y) (ν : Measure (Y × Q)) (A : Y → ℂ) (hmA : Measurable A) (e : Y → ℝ) (he : Measurable e)
    (hp : ∀ y, 0 < e y) (hi : Integrable (fun y => ‖A y‖*e y) μ) (K : Y × Q → ℂ)
    (hc : ∀ f : Y → ℂ, Measurable f → Integrable f μ →
      Measurable (fun z : Y × Q => f z.1*K z) ∧ Integrable (fun z : Y × Q => f z.1*K z) ν) :
    Measurable (fun z : Y × Q => A z.1*K z) ∧ Integrable (fun z : Y × Q => ‖A z.1*K z‖*e z.1) ν := by
  let f := fun y => A y*(e y:ℂ)
  have hf : Measurable f := hmA.mul (Complex.continuous_ofReal.measurable.comp he)
  have hfn (y) : ‖f y‖ = ‖A y‖*e y := by simp only [f,norm_mul,Complex.norm_real,Real.norm_of_nonneg (hp y).le]
  have hfi := hi.mono' hf.aestronglyMeasurable (Eventually.of_forall fun y => (hfn y).le)
  obtain ⟨hK,hiK⟩ := hc f hf hfi
  have hn (z : Y × Q) : ‖f z.1*K z‖ = ‖A z.1*K z‖*e z.1 := by rw [norm_mul,hfn,norm_mul]; ring
  refine ⟨?_,by simpa only [hn] using hiK.norm⟩
  have hq := hK.div (Complex.continuous_ofReal.measurable.comp (he.comp measurable_fst))
  convert hq using 1
  funext z
  have hne : (e z.1 : ℂ) ≠ 0 := by exact_mod_cast (hp z.1).ne'
  change A z.1*K z = A z.1*(e z.1:ℂ)*K z/(e z.1:ℂ)
  field_simp

end UV
