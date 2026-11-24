import UV.ContinuePinnedNormalGaussian

/-! The original multigraph keeps every labelled edge and every held
vertex. Once all held positions equal the same reference point, the
incidence rows only see the interior coordinates. -/

noncomputable section
open MeasureTheory Real Set Matrix
open scoped ENNReal BigOperators Matrix
namespace UV

def pinnedHeldEndpoint {L : ℕ} {B : Type*} : Fin L ⊕ B → Option (Fin L)
  | .inl i => some i
  | .inr _ => none

def pinnedHeldIncidence {L N : ℕ} {B : Type*} (src dst : Fin N → Fin L ⊕ B) :
    Matrix (Fin L) (Fin N) ℝ :=
  (groundedNetworkIncidence (pinnedHeldEndpoint ∘ src) (pinnedHeldEndpoint ∘ dst))ᵀ

theorem pinnedHeldIncidence_mulVec {L N : ℕ} {B : Type*}
    (src dst : Fin N → Fin L ⊕ B) (x : Fin L → ℝ) (e : Fin N) :
    ((pinnedHeldIncidence src dst)ᵀ *ᵥ x) e =
      networkRootLift x (pinnedHeldEndpoint (dst e)) - networkRootLift x (pinnedHeldEndpoint (src e)) := by
  unfold pinnedHeldIncidence
  rw [transpose_transpose,groundedNetworkIncidence_mulVec]
  rfl

theorem pinnedHeldIncidence_selfLoop {L N : ℕ} {B : Type*} (src dst : Fin N → Fin L ⊕ B)
    {e : Fin N} (h : src e = dst e) (i : Fin L) : pinnedHeldIncidence src dst i e = 0 := by
  simp only [pinnedHeldIncidence,transpose_apply,groundedNetworkIncidence,Function.comp_apply,h,sub_self]

theorem pinnedHeldIncidence_injective {L N : ℕ} {B : Type*} (b : B)
    (G : SimpleGraph (Fin L ⊕ B)) (src dst : Fin N → Fin L ⊕ B) (hG : G.Connected)
    (hcover : ∀ u v, G.Adj u v → ∃ e, (src e = u ∧ dst e = v) ∨ (src e = v ∧ dst e = u)) :
    Function.Injective (pinnedHeldIncidence src dst)ᵀ.mulVec := by
  intro x y hxy
  let z := x-y
  let f : Fin L ⊕ B → ℝ := networkRootLift z ∘ pinnedHeldEndpoint
  have hzero : (pinnedHeldIncidence src dst)ᵀ *ᵥ z = 0 := by
    unfold z
    rw [Matrix.mulVec_sub,hxy,sub_self]
  have hE (e : Fin N) : f (dst e) = f (src e) := by
    have h := congrFun hzero e
    rw [pinnedHeldIncidence_mulVec] at h
    exact sub_eq_zero.mp h
  have hAdj {u v : Fin L ⊕ B} (h : G.Adj u v) : f u = f v := by
    obtain ⟨e,he|he⟩ := hcover u v h
    · simpa only [he.1,he.2] using (hE e).symm
    · simpa only [he.1,he.2] using hE e
  have hWalk {u v : Fin L ⊕ B} (w : G.Walk u v) : f u = f v := by
    induction w with
    | nil => rfl
    | cons hv _ ih => exact (hAdj hv).trans ih
  apply sub_eq_zero.mp
  funext i
  obtain ⟨w⟩ := hG (.inr b) (.inl i)
  exact (hWalk w).symm

def pinnedHeldPosition {L d : ℕ} {B : Type*} (y : Fin d → EuclideanSpace ℝ (Fin L)) :
    Fin L ⊕ B → EuclideanSpace ℝ (Fin d)
  | .inl i => WithLp.toLp 2 (fun j => y j i)
  | .inr _ => 0

private theorem pinnedHeldPosition_apply {L d : ℕ} {B : Type*} (y : Fin d → EuclideanSpace ℝ (Fin L))
    (v : Fin L ⊕ B) (j : Fin d) :
    pinnedHeldPosition y v j = networkRootLift (y j).ofLp (pinnedHeldEndpoint v) := by
  cases v <;> rfl

def pinnedHeldHeatProduct {L N d : ℕ} {B : Type*} (src dst : Fin N → Fin L ⊕ B)
    (D : ℝ) (t : Fin N → ℝ) (y : Fin d → EuclideanSpace ℝ (Fin L)) : ℝ :=
  ∏ e, (4*π*D*t e)^(-(d:ℝ)/2) *
    exp (-‖pinnedHeldPosition y (dst e)-pinnedHeldPosition y (src e)‖^2/(4*D*t e))

theorem pinnedHeldHeatProduct_incidence {L N d : ℕ} {B : Type*} (src dst : Fin N → Fin L ⊕ B)
    (D : ℝ) (t : Fin N → ℝ) (y : Fin d → EuclideanSpace ℝ (Fin L)) :
    pinnedHeldHeatProduct src dst D t y = pinnedNormalHeatProduct (pinnedHeldIncidence src dst) D t y := by
  unfold pinnedHeldHeatProduct pinnedNormalHeatProduct
  apply Finset.prod_congr rfl
  intro e _
  rw [EuclideanSpace.norm_sq_eq,← Finset.sum_neg_distrib,Finset.sum_div]
  simp only [PiLp.sub_apply,Real.norm_eq_abs,sq_abs,pinnedHeldPosition_apply,pinnedHeldIncidence_mulVec]

/-- The literal Gaussian on each labelled edge gives the full
short-duration rank test for a pinned connected normal graph. -/
theorem pinnedHeld_heat_duration_finite_iff {L N d : ℕ} {B : Type*} (b : B)
    (G : SimpleGraph (Fin L ⊕ B)) (src dst : Fin N → Fin L ⊕ B) (hG : G.Connected)
    (hcover : ∀ u v, G.Adj u v → ∃ e, (src e = u ∧ dst e = v) ∨ (src e = v ∧ dst e = u))
    {D : ℝ} (hD : 0 < D) (η : Fin N → ℝ) :
    (∫⁻ t, ENNReal.ofReal (retainedWidthDensity η t *
      (∫ y : Fin d → EuclideanSpace ℝ (Fin L), pinnedHeldHeatProduct src dst D t y))
        ∂directionalSchwingerMeasure (Fin N)) < ⊤ ↔
      ∀ S : Finset (Fin N), S.Nonempty →
        (d:ℝ)/2 * pinnedDurationNullity (pinnedHeldIncidence src dst) S < ∑ i ∈ S, η i := by
  simp_rw [pinnedHeldHeatProduct_incidence]
  exact pinned_normal_heat_duration_finite_iff _ (pinnedHeldIncidence_injective b G src dst hG hcover) hD η

theorem pinnedHeld_heat_duration_comparable_finite_iff {L N d : ℕ} {B : Type*} (b : B)
    (G : SimpleGraph (Fin L ⊕ B)) (src dst : Fin N → Fin L ⊕ B) (hG : G.Connected)
    (hcover : ∀ u v, G.Adj u v → ∃ e, (src e = u ∧ dst e = v) ∨ (src e = v ∧ dst e = u))
    {D : ℝ} (hD : 0 < D) (η : Fin N → ℝ) (w : (Fin N → ℝ) → ℝ)
    {lo hi : ℝ} (hlo : 0 < lo) (hhi : 0 ≤ hi)
    (hW : ∀ᵐ t ∂directionalSchwingerMeasure (Fin N),
      lo*retainedWidthDensity η t ≤ w t ∧ w t ≤ hi*retainedWidthDensity η t) :
    (∫⁻ t, ENNReal.ofReal (w t *
      (∫ y : Fin d → EuclideanSpace ℝ (Fin L), pinnedHeldHeatProduct src dst D t y))
        ∂directionalSchwingerMeasure (Fin N)) < ⊤ ↔
      ∀ S : Finset (Fin N), S.Nonempty →
        (d:ℝ)/2 * pinnedDurationNullity (pinnedHeldIncidence src dst) S < ∑ i ∈ S, η i := by
  refine (retainedIntegral_comparable _ _ _ (ENNReal.ofReal lo) (ENNReal.ofReal hi)
    (ENNReal.ofReal_ne_zero_iff.mpr hlo) ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top ?_).trans
    (pinnedHeld_heat_duration_finite_iff b G src dst hG hcover hD η)
  filter_upwards [hW,retainedWidth_ae_positive (n := N)] with t ht ht₀
  let P := ∫ y : Fin d → EuclideanSpace ℝ (Fin L), pinnedHeldHeatProduct src dst D t y
  have hP : 0 ≤ P := by
    apply integral_nonneg
    intro y
    unfold pinnedHeldHeatProduct
    exact Finset.prod_nonneg (fun e _ => mul_nonneg
      (rpow_nonneg (mul_nonneg (mul_nonneg (by positivity) hD.le) (ht₀ e).le) _) (exp_pos _).le)
  change ENNReal.ofReal lo * ENNReal.ofReal (retainedWidthDensity η t*P) ≤ ENNReal.ofReal (w t*P) ∧
    ENNReal.ofReal (w t*P) ≤ ENNReal.ofReal hi * ENNReal.ofReal (retainedWidthDensity η t*P)
  rw [← ENNReal.ofReal_mul hlo.le,← ENNReal.ofReal_mul hhi,← mul_assoc,← mul_assoc]
  exact ⟨ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ht.1 hP),
    ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ht.2 hP)⟩

end UV
