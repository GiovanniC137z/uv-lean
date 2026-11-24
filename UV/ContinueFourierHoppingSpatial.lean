import UV.ContinueTwoBandFourierLink

/-! Uniform Gaussian costs in a charged circulation with arbitrarily many
unmarked hops and a fixed total number of spatial derivatives. Each spatial
direction is an actual unit polarization of the sector. -/

noncomputable section

open MeasureTheory Filter

namespace UV.SectorPlane

structure HoppingSpatialSlot where
  degree : ℕ
  direction : Fin degree → UnitVector Spatial
  shift : Spatial
  marks : Fin degree → Spatial

def HoppingSpatialSlot.value (t : HoppingSpatialSlot) (σ : ℝ) :=
  twoBandGaussianWilsonMark 1 σ t.direction t.shift t.marks

theorem hopping_unmarked_heat (σ : ℝ) (u : Fin 0 → UnitVector Spatial) (b : Spatial)
    (q : Fin 0 → Spatial) (k : Spatial) :
    twoBandGaussianWilsonMark 1 σ u b q k = Real.exp (-(σ^2*‖k+b‖^2)) := by
  simp [twoBandGaussianWilsonMark,twoBandGaussianMarkAverage,iteratedFDeriv_zero_apply,twoBandSpatialHop]

private theorem spatial_budget_exists {σ : ℝ} (hσ : 0 < σ) (M : ℕ) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ t : HoppingSpatialSlot, t.degree ≤ M →
      Integrable (t.value σ) ∧ (∀ k, ‖t.value σ k‖ ≤ K^t.degree) ∧ (∫ k, ‖t.value σ k‖) ≤ K := by
  obtain ⟨C,D,_,_,h⟩ := twoBand_gaussian_wilson_marks 1 hσ M
  induction M generalizing C D with
  | zero =>
    refine ⟨max 1 D,le_max_left _ _,?_⟩
    rintro ⟨j,u,b,q⟩ hj
    have hz : j=0 := Nat.eq_zero_of_le_zero hj
    subst j
    exact ⟨(h u b q).2.1, fun k => by
        change ‖twoBandGaussianWilsonMark 1 σ u b q k‖ ≤ (max 1 D)^0
        rw [hopping_unmarked_heat,Real.norm_of_nonneg (Real.exp_nonneg _),pow_zero]
        exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity)),
      (h u b q).2.2.2.trans (le_max_right _ _)⟩
  | succ M ih =>
    obtain ⟨C₀,D₀,hC₀,hD₀,h₀⟩ := twoBand_gaussian_wilson_marks 1 hσ M
    obtain ⟨K,hK,hprev⟩ := ih C₀ D₀ hC₀ hD₀ h₀
    let L := max K (max C D)
    have hKL : K ≤ L := le_max_left _ _
    have hL : 1 ≤ L := hK.trans hKL
    refine ⟨L,hL,?_⟩
    rintro ⟨j,u,b,q⟩ hj
    change j ≤ M+1 at hj
    rcases Nat.eq_or_lt_of_le hj with rfl|hj'
    · exact ⟨(h u b q).2.1,fun k => ((h u b q).2.2.1 k).trans
          (((le_max_left C D).trans (le_max_right _ _)).trans (le_self_pow₀ hL (Nat.succ_ne_zero M))),
        (h u b q).2.2.2.trans ((le_max_right C D).trans (le_max_right _ _))⟩
    · obtain ⟨hi,hb,hI⟩ := hprev ⟨j,u,b,q⟩ (by dsimp; omega)
      exact ⟨hi,fun k => (hb k).trans (pow_le_pow_left₀ (zero_le_one.trans hK) hKL _),hI.trans hKL⟩

def hoppingSpatialBudget {σ : ℝ} (hσ : 0 < σ) (M : ℕ) : ℝ :=
  (spatial_budget_exists hσ M).choose

theorem hopping_spatial_budget_one {σ : ℝ} (hσ : 0 < σ) (M : ℕ) :
    1 ≤ hoppingSpatialBudget hσ M := (spatial_budget_exists hσ M).choose_spec.1

def hoppingSpatialProduct (σ : ℝ) (T : List HoppingSpatialSlot) (k : Spatial) : ℝ :=
  (T.map fun t => t.value σ k).prod

def hoppingSpatialDegree (T : List HoppingSpatialSlot) := (T.map HoppingSpatialSlot.degree).sum

theorem hopping_spatial_product_sup {σ : ℝ} (hσ : 0 < σ) {M : ℕ} (T : List HoppingSpatialSlot)
    (hD : hoppingSpatialDegree T ≤ M) (k : Spatial) :
    ‖hoppingSpatialProduct σ T k‖ ≤ (hoppingSpatialBudget hσ M)^(hoppingSpatialDegree T) := by
  induction T with
  | nil => simp [hoppingSpatialProduct,hoppingSpatialDegree]
  | cons t T ih =>
    change t.degree+hoppingSpatialDegree T ≤ M at hD
    change ‖t.value σ k*hoppingSpatialProduct σ T k‖ ≤ _^(t.degree+hoppingSpatialDegree T)
    rw [norm_mul,pow_add]
    exact mul_le_mul (((spatial_budget_exists hσ M).choose_spec.2 t (by omega)).2.1 k)
      (ih (by omega)) (norm_nonneg _) (pow_nonneg (zero_le_one.trans (hopping_spatial_budget_one hσ _)) _)

theorem hopping_spatial_measurable {σ : ℝ} (hσ : 0 < σ) (T : List HoppingSpatialSlot) :
    Measurable (hoppingSpatialProduct σ T) := by
  induction T with
  | nil => exact measurable_const
  | cons t T ih =>
    obtain ⟨C,D,_,_,h⟩ := twoBand_gaussian_wilson_marks 1 hσ t.degree
    exact ((h t.direction t.shift t.marks).1).mul ih

/-- One L¹ Gaussian and all other slots at their uniform suprema. An
unmarked hop has supremum exactly bounded by one, independently of the
number of hops and all external Fourier translations. -/
theorem hopping_charged_loop_spatial {σ : ℝ} (hσ : 0 < σ) (u : HoppingSpatialSlot)
    (T : List HoppingSpatialSlot) {M : ℕ} (hD : u.degree+hoppingSpatialDegree T ≤ M) :
    Integrable (hoppingSpatialProduct σ (u::T)) ∧
      (∫ k, ‖hoppingSpatialProduct σ (u::T) k‖) ≤ (hoppingSpatialBudget hσ M)^(M+1) := by
  let K := hoppingSpatialBudget hσ M
  have hK : 1 ≤ K := hopping_spatial_budget_one hσ M
  obtain ⟨hi,_,hI⟩ := (spatial_budget_exists hσ M).choose_spec.2 u (by omega)
  have hB (k : Spatial) : ‖hoppingSpatialProduct σ (u::T) k‖ ≤ ‖u.value σ k‖*K^M := by
    change ‖u.value σ k * hoppingSpatialProduct σ T k‖ ≤ _
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left ((hopping_spatial_product_sup hσ T (by omega : hoppingSpatialDegree T ≤ M) k).trans
      (pow_le_pow_right₀ hK (by omega))) (norm_nonneg _)
  have hDom := hi.norm.mul_const (K^M)
  have hInt := hDom.mono' (hopping_spatial_measurable hσ (u::T)).aestronglyMeasurable (ae_of_all _ hB)
  refine ⟨hInt,(integral_mono hInt.norm hDom hB).trans ?_⟩
  rw [integral_mul_const,pow_succ,mul_comm (K^M)]
  exact mul_le_mul_of_nonneg_right hI (pow_nonneg (zero_le_one.trans hK) _)

end UV.SectorPlane
