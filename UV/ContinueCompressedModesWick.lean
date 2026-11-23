import UV.ContinueCompressedModesPolarization
import UV.CurvatureWickMatchings
import UV.RevisionOSMoments

/-! Wick evaluation of arbitrary finite products of the homogeneous
electric coefficients. Positional partners include self-sewings,
parallel photons and repeated source labels with their multiplicities. -/

noncomputable section
open MeasureTheory MvPolynomial UV.SectorPlane
open scoped Matrix.Norms.L2Operator
namespace UV

variable {H V Ω : Type*} [Fintype H] [Fintype V] [MeasurableSpace Ω]

def compressedMarkList (r : V → ℕ) : List ((v : V) × Fin (r v)) :=
  List.ofFn (Fintype.equivFin ((v : V) × Fin (r v))).symm

private theorem compressed_mark_product (r : V → ℕ) (f : (v : V) → Fin (r v) → ℝ) :
    ((compressedMarkList r).map (fun a => f a.1 a.2)).prod = ∏ v, ∏ i, f v i := by
  rw [compressedMarkList,List.map_ofFn,List.prod_ofFn,←Fintype.prod_sigma']
  exact (Fintype.equivFin ((v : V) × Fin (r v))).symm.prod_comp (fun a => f a.1 a.2)

theorem compressed_source_products_wick [DecidableEq V] {μ : Measure Ω} {F : H → Ω → ℝ} {K : H → H → ℝ}
    (hW : OSWickMoments μ F K) (r : V → ℕ) (U : V → Type*) [∀ v, Fintype (U v)]
    (c : (v : V) → U v → (Fin (r v) → H) → ℝ) :
    let P := fun v => compressedColorPolynomial (c v)
    let idx := (v : V) → U v × (Fin (r v) → H)
    let slot := fun (a : idx) (i : (v : V) × Fin (r v)) => (a i.1).2 i.2
    let l := compressedMarkList r
    Integrable (fun ω => ∏ v, eval (fun h => F h ω) (P v)) μ ∧
    (∫ ω, ∏ v, eval (fun h => F h ω) (P v) ∂μ) =
      ∑ a : (v : V) → U v × (Fin (r v) → H), (∏ v, c v (a v).1 (a v).2) *
        ((CurvatureWick.matchings l.length l).map
          (CurvatureWick.matchingWeight (fun i j => K (slot a i) (slot a j)))).sum := by
  classical
  let I := (v : V) → U v × (Fin (r v) → H)
  let slot (a : I) (i : (v : V) × Fin (r v)) := (a i.1).2 i.2
  let l := compressedMarkList r
  let w (a : I) := ∏ v, c v (a v).1 (a v).2
  let g (a : I) (ω : Ω) := w a*osMonomial F (l.map (slot a)) ω
  have h (ω) : (∏ v, eval (fun h => F h ω) (compressedColorPolynomial (c v))) = ∑ a : I, g a ω := by
    simp_rw [compressed_color_polynomial_eval]
    let B (v : V) (z : U v × (Fin (r v) → H)) := (∏ b, F (z.2 b) ω)*c v z.1 z.2
    have hb (v) : (∑ z : U v × (Fin (r v) → H), B v z) =
        ∑ u : U v, ∑ d : Fin (r v) → H, (∏ b, F (d b) ω)*c v u d := Fintype.sum_prod_type _
    simp_rw [←hb]
    rw [Finset.prod_univ_sum]
    apply Finset.sum_congr rfl
    intro a _
    simp only [g,w,osMonomial,List.map_map]
    change (∏ v, B v (a v)) = _ * ((compressedMarkList r).map (fun i => F ((a i.1).2 i.2) ω)).prod
    rw [compressed_mark_product r (fun v i => F ((a v).2 i) ω)]
    simp only [B,Finset.prod_mul_distrib,mul_comm]
  have hi (a : I) : Integrable (g a) μ := (hW.integrable _).const_mul _
  have hm (a : I) : (∫ ω, g a ω ∂μ) = w a *
      ((CurvatureWick.matchings l.length l).map (CurvatureWick.matchingWeight (fun i j => K (slot a i) (slot a j)))).sum := by
    rw [show (∫ ω, g a ω ∂μ) = w a*(∫ ω, osMonomial F (l.map (slot a)) ω ∂μ) from integral_const_mul _ _]
    rw [hW.moment l.length _ (by rw [List.length_map]; omega),CurvatureWick.wick_sum_over_matchings]
  dsimp only
  simp_rw [h]
  exact ⟨integrable_finset_sum _ (fun a _ => hi a), (integral_finset_sum _ (fun a _ => hi a)).trans
    (Finset.sum_congr rfl fun a _ => hm a)⟩

omit [Fintype H] in
/-- A concrete realization on the independent real Gaussian coordinates.
Weights and slot identifications supply the chosen covariance. -/
theorem compressed_real_gaussian_wick {n : ℕ} (slot : H → NextCurvatureLaw.ModeSlot n) (w : H → ℝ) :
    OSWickMoments (NextCurvatureLaw.commonGaussian n) (fun h X => w h*X (slot h))
      (fun h j => w h*w j*VerifyCurvaturePairings.diagonalCovariance (fun _ => (1/2:ℝ)) (slot h) (slot j)) where
  integrable xs := (VerifyCurvaturePairings.weighted_coordinate_list_wick slot w xs xs.length (by omega)).1
  moment k xs hk := (VerifyCurvaturePairings.weighted_coordinate_list_wick slot w xs k hk).2

end UV
