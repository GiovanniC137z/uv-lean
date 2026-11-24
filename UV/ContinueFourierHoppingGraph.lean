import UV.ContinueFourierHoppingPhoton
import UV.ContinueWilsonJointTraces

/-! Simultaneous integration of the soft-routed Fourier representative, with
independent charged four-momenta and free photon four-momenta. -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Filter UV.SectorPlane

namespace UV

variable {E V : Type*} [Fintype E] [DecidableEq E] [Fintype V] {n : ℕ} {A : E → Fin n → ℝ}

def hoppingFourierPhotonWord (kind : E → OrderedPhotonKind) (ij : E → Fin 3 × Fin 3)
    (a : ℝ) (q : E → OSFourSpace) : ℂ :=
  ((∏ e, (kind e).softLine a (q e) * (kind e).projector (ij e).1 (ij e).2 (q e) : ℝ) : ℂ)

omit [DecidableEq E] in
private theorem photon_word_bound (kind : E → OrderedPhotonKind) (ij : E → Fin 3 × Fin 3)
    (a : ℝ) (q : E → OSFourSpace) :
    ‖hoppingFourierPhotonWord kind ij a q‖ ≤ ∏ e, (kind e).softLine a (q e) := by
  simp only [hoppingFourierPhotonWord,Complex.norm_real,norm_prod,Real.norm_eq_abs,abs_mul]
  apply Finset.prod_le_prod (fun e _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
  intro e _
  rw [abs_of_nonneg ((kind e).softLine_nonneg a _)]
  exact mul_le_of_le_one_right ((kind e).softLine_nonneg a _) ((kind e).projector_bound _ _ _)

def hoppingFourierGraph {N : V → ℕ} (B : WilsonIncidenceBasis A)
    (kind : E → OrderedPhotonKind) (ij : E → Fin 3 × Fin 3) (b : Fin n → OSFourSpace)
    (a g σ : ℝ) (L : (v : V) → (B.Chord → OSFourSpace) → HoppingFourierLoop (N v)) :
    (B.Chord → OSFourSpace) × (V → ℝ × Spatial) → ℂ :=
  wilsonJointFactors (fun q => hoppingFourierPhotonWord kind ij a (B.flow b q)) (fun v q => (L v q).word g σ)

/-- Fixed hopping orders and allocations. The momentum slots can share and
depend on every photon variable. Only a measurable choice of slots and the
matching of actual marked ends and line frequencies are required. -/
theorem hopping_fourier_graph_absolute {N : V → ℕ} (B : WilsonIncidenceBasis A)
    (kind : E → OrderedPhotonKind) (ij : E → Fin 3 × Fin 3) (b : Fin n → OSFourSpace)
    {a m σ g : ℝ} (ha : 0<a) (hm : 0<m) (hσ : 0<σ) (M : ℕ)
    (L : (v : V) → (B.Chord → OSFourSpace) → HoppingFourierLoop (N v))
    (hL : ∀ v q, (L v q).valid m M)
    (hMeas : ∀ v, Measurable (fun z : (B.Chord → OSFourSpace) × (ℝ × Spatial) => (L v z.1).word g σ z.2))
    (R : ∀ q, HoppingFourierMark (L · q) ≃ HoppingScalarEnd kind)
    (hr : ∀ q (i : HoppingFourierMark (L · q)), ((L i.1 q).time i.2.1).marks.get i.2.2 =
      hoppingScalarFrequency kind (B.flow b q) (R q i)) :
    let G := hoppingFourierGraph B kind ij b a g σ L
    Integrable G ∧ (∫ z, ‖G z‖) ≤ (∏ c : B.Chord, ∫ p, (kind c).envelope a p) *
      ∏ v, hoppingFourierBudget m g hσ M * (|g|/m)^(N v) := by
  classical
  intro G
  let W := fun q => hoppingFourierPhotonWord kind ij a (B.flow b q)
  let F := fun v q => (L v q).word g σ
  let C := fun v => hoppingFourierBudget m g hσ M * (|g|/m)^(N v)
  let H := fun q : B.Chord → OSFourSpace => ∏ c : B.Chord, (kind c).envelope a (q c)
  have hW : Measurable W := Complex.continuous_ofReal.measurable.comp (Finset.measurable_prod _ fun e _ =>
    (((kind e).measurable_softLine _).mul ((kind e).measurable_projector _ _)).comp (B.measurable_flow b e))
  have hG : Measurable G := wilson_factors_measurable hW hMeas
  have hH : Integrable H := Integrable.fintype_prod (fun c : B.Chord => (kind c).integrable ha)
  have hF (v q) := (L v q).absolute_cost hm hσ g (hL v q)
  have hC v : 0 ≤ C v := mul_nonneg (hopping_fourier_budget_nonneg hm g hσ M)
    (pow_nonneg (div_nonneg (abs_nonneg _) hm.le) _)
  have hi (q) : Integrable (fun x => G (q,x)) :=
    (Integrable.fintype_prod (fun v => (hF v q).1)).const_mul (W q)
  have hbound (q) : (∫ x, ‖G (q,x)‖) ≤ H q * ∏ v, C v := by
    change (∫ x : V → ℝ × Spatial, ‖W q * ∏ v, F v q (x v)‖) ≤ _
    simp only [norm_mul,norm_prod,integral_const_mul]
    rw [integral_fintype_prod_volume_eq_prod (fun v x => ‖F v q x‖)]
    calc
      _ ≤ (∏ e, (kind e).softLine a (B.flow b q e)) * ∏ v, C v * (L v q).weight :=
        mul_le_mul (photon_word_bound kind ij a _) (Finset.prod_le_prod (fun _ _ => integral_nonneg fun _ => norm_nonneg _)
          (fun v _ => (hF v q).2)) (Finset.prod_nonneg fun _ _ => integral_nonneg fun _ => norm_nonneg _)
          (Finset.prod_nonneg fun e _ => (kind e).softLine_nonneg _ _)
      _ = (∏ e, (kind e).envelope a (B.flow b q e)) * ∏ v, C v := by
        rw [Finset.prod_mul_distrib,hopping_fourier_routed_weights (L · q) kind (B.flow b q) (R q) (hr q)]
        calc
          _ = ((∏ e, (kind e).softLine a (B.flow b q e)) * ∏ e, (kind e).carrierWeight (B.flow b q e)) *
            ∏ v, C v := by ring
          _ = _ := by simp only [← Finset.prod_mul_distrib,OrderedPhotonKind.softLine_carrierWeight]
      _ ≤ _ := mul_le_mul_of_nonneg_right (B.ordered_product_bound kind ha.le b q) (Finset.prod_nonneg fun v _ => hC v)
  have hDom := hH.mul_const (∏ v, C v)
  have hInt : Integrable G := by
    apply (integrable_prod_iff hG.aestronglyMeasurable).mpr
    refine ⟨ae_of_all _ hi,?_⟩
    apply hDom.mono' hG.norm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
    exact ae_of_all _ fun q => by rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]; exact hbound q
  refine ⟨hInt,?_⟩
  rw [Measure.volume_eq_prod,integral_prod _ hInt.norm]
  apply (integral_mono hInt.integral_norm_prod_left hDom hbound).trans_eq
  rw [integral_mul_const]
  simp only [H,integral_fintype_prod_volume_eq_prod,C]

end UV
