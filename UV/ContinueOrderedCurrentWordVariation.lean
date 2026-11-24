import UV.ContinueOrderedCurrentModes
import UV.ContinueOrderedCurrentGrowth

/-! Complete electromagnetic differentiation of the signed two-slot matter
trace itself, including the oriented onsite inverse, the heat hops and the
logarithmic coefficient 1/N before any marks are distributed. -/

noncomputable section

open MeasureTheory Finset Matrix
open scoped ContinuousMap

namespace UV.SectorPlane.OrderedTwoBandPath

/-- One signed carrier interval and its horizontal Wilson hop. -/
def stepConnection (P : OrderedTwoBandPath) (B : RealConnection) (j : ℕ) : ℝ :=
  (∫ t in P.time j..P.time (j+1), B.1 (t,P.position j)) +
    ∫ r in (0:ℝ)..1, B.2 (P.time (j+1),P.position j+r • P.step j) (P.step j)

def backgroundPhases {n : ℕ} (q : ℝ) (φ : OrderedHopPhases n) (B : RealConnection) : OrderedHopPhases n :=
  fun j s d => φ j s d - q*(returnPath d).stepConnection B j

private theorem weight_step {n : ℕ} (m σ q : ℝ) (φ : OrderedHopPhases n) (B : RealConnection)
    (d : Fin n → OrderedHopStep) (j : Fin (n+1)) (s : Bool) :
    orderedHopPhasedWeight m σ (backgroundPhases q φ B) d j s =
      Complex.exp (-Complex.I*(q:ℂ)*((returnPath d).stepConnection B j:ℂ)) *
        orderedHopPhasedWeight m σ φ d j s := by
  unfold orderedHopPhasedWeight backgroundPhases
  rw [←mul_assoc,←Complex.exp_add]
  congr 2
  push_cast
  ring

private theorem flip_word_scale {ι : Type*} (A : ι → Bool → ℂ) (k : ι → ℂ) (L : List ι) :
    orderedHopFlipWord (fun j s => k j*A j s) L = (L.map k).prod • orderedHopFlipWord A L := by
  induction L with
  | nil => simp [orderedHopFlipWord]
  | cons j L ih =>
    have hstep : orderedHopFlipMatrix (fun s => k j*A j s) = k j • orderedHopFlipMatrix (A j) := by
      ext s t
      simp [orderedHopFlipMatrix,Matrix.smul_apply,mul_ite]
    change orderedHopFlipMatrix _ * orderedHopFlipWord _ L = (k j*(L.map k).prod) •
      (orderedHopFlipMatrix _ * orderedHopFlipWord _ L)
    rw [hstep,ih,smul_mul_assoc,mul_smul_comm,smul_smul]

theorem log_word_phase {n : ℕ} (m σ g q : ℝ) (φ : OrderedHopPhases n) (B : RealConnection)
    (d : Fin n → OrderedHopStep) :
    orderedHopLogWord m σ g (backgroundPhases q φ B) d =
      orderedHopLogWord m σ g φ d * (returnPath d).connectionPhase q B := by
  let P := returnPath d
  let k := fun j : Fin (n+1) => Complex.exp (-Complex.I*(q:ℂ)*(P.stepConnection B j:ℂ))
  have hphase : (∏ j, k j) = P.connectionPhase q B := by
    simp only [k,←Complex.exp_sum,←Finset.mul_sum,←Complex.ofReal_sum,connectionPhase]
    rw [Fin.sum_univ_eq_sum_range]
    rfl
  have he : orderedHopPhasedWeight m σ (backgroundPhases q φ B) d =
      fun j s => k j*orderedHopPhasedWeight m σ φ d j s := funext₂ (weight_step m σ q φ B d)
  rw [orderedHopLogWord,he,flip_word_scale,List.map_ofFn,Fin.prod_ofFn]
  simp only [Function.comp_id,hphase,Matrix.trace_smul,smul_eq_mul,orderedHopLogWord,P]
  ring

theorem mixedVariation_const_mul (L : List (RealConnection × RealConnection)) (k : ℂ)
    (F : RealConnection → ℂ) (B : RealConnection) :
    mixedVariation L (fun C => k*F C) B = k*mixedVariation L F B := by
  induction L generalizing B with
  | nil => rfl
  | cons C L ih =>
    rcases C with ⟨A,D⟩
    simp only [mixedVariation,ih,deriv_const_mul_field]
    ring

/-- This is the actual derivative of the log word, with general time- and
slot-dependent baseline phases. At zero background every order has exactly
the product used to sew the graph. -/
theorem log_word_fourier_coefficient {n : ℕ} (m σ g q a : ℝ) (φ : OrderedHopPhases n)
    (d : Fin n → OrderedHopStep) (marks : List ElectricMark) :
    mixedVariation (marks.map (fun j => j.tests a))
      (fun B => orderedHopLogWord m σ g (backgroundPhases q φ B) d) 0 =
      orderedHopLogWord m σ g φ d * ((-Complex.I*(q:ℂ))^marks.length *
        (marks.map (fun j => (Real.exp (-a*‖j.momentum‖):ℂ)*j.current (returnPath d))).prod) := by
  simp_rw [log_word_phase]
  rw [mixedVariation_const_mul,(returnPath d).actual_fourier_coefficient]

end UV.SectorPlane.OrderedTwoBandPath
