import Mathlib.Tactic
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Convex.Jensen
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.ENNReal.Lemmas


set_option linter.style.multiGoal false
set_option linter.style.whitespace false


open PMF
open MeasureTheory
open Finset
open BigOperators
open Filter
open scoped Topology




noncomputable section RateDistortion

-- finite alphabets
variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

-- blocklength and codebook size are positive
variable (n M : ℕ) (hM : 0 < M) (hn : 0 < n)

-- A finite-alphabet single-letter distortion measure.
-- `NNReal` excludes infinite distortion values; boundedness follows from
-- finiteness of the two alphabets.
def Distortion := X → Y → NNReal
#check Distortion

noncomputable def distortionBound
    (d : Distortion (X := X) (Y := Y)) : NNReal :=
  Finset.univ.sup (fun x => Finset.univ.sup (fun y => d x y))

theorem distortion_le_bound
    (d : Distortion (X := X) (Y := Y)) (x : X) (y : Y) :
    d x y ≤ distortionBound d := by
  exact (Finset.le_sup (Finset.mem_univ y)).trans
    (Finset.le_sup (s := (Finset.univ : Finset X))
      (f := fun x => Finset.univ.sup (fun y => d x y)) (Finset.mem_univ x))

def DistortionBounded
    (d : Distortion (X := X) (Y := Y)) : Prop :=
  ∃ d₀ : NNReal, ∀ x y, d x y ≤ d₀

theorem distortion_bounded
    (d : Distortion (X := X) (Y := Y)) :
    DistortionBounded d := by
  exact ⟨distortionBound d, distortion_le_bound d⟩

-- Blocks are functions on the finite index type `Fin n`. This makes
-- coordinate projections and finite sums available directly.
abbrev Xblock (n : ℕ) (X : Type*) := Fin n → X
abbrev Yblock (n : ℕ) (Y : Type*) := Fin n → Y
abbrev Index (M : ℕ) := Fin M

def finInitLastEquiv (k : ℕ) (A : Type*) :
    (Fin (k + 1) → A) ≃ ((Fin k → A) × A) where
  toFun x := (Fin.init x, x (Fin.last k))
  invFun z := Fin.snoc z.1 z.2
  left_inv x := by
    funext i
    refine Fin.lastCases (by simp) (fun j => ?_) i
    change Fin.snoc (Fin.init x) (x (Fin.last k)) j.castSucc = x j.castSucc
    rw [Fin.snoc_castSucc]
    rfl
  right_inv z := by
    ext <;> simp

@[simp] theorem finInitLastEquiv_symm_apply
    (k : ℕ) (A : Type*) (z : (Fin k → A) × A) :
    (finInitLastEquiv k A).symm z = Fin.snoc z.1 z.2 := rfl

-- Rate distortion code consists of an encoder and an decoder
structure RateDistortionCode
    (X Y : Type*) [Fintype X] [Fintype Y]
    (n M : ℕ) where
  encoder : Xblock n X → Index M
  decoder : Index M → Yblock n Y

-- instantiate a rate distortion code
def MyCode :=
  RateDistortionCode X Y n M

/-- Given a codebook and a predicate on source/reproduction blocks, choose the
first codeword satisfying the predicate; use index `0` when none does. -/
noncomputable def codebookEncoder
    (hM : 0 < M) (codebook : Index M → Yblock n Y)
    (good : Xblock n X → Yblock n Y → Prop) :
    Xblock n X → Index M := by
  classical
  intro x
  exact if h : ∃ j, good x (codebook j) then
    Fin.find (fun j ↦ good x (codebook j)) h else ⟨0, hM⟩

/-- The deterministic code induced by a fixed codebook and a good-pair
predicate. -/
noncomputable def codebookCode
    (hM : 0 < M) (codebook : Index M → Yblock n Y)
    (good : Xblock n X → Yblock n Y → Prop) :
    RateDistortionCode X Y n M where
  encoder := codebookEncoder n M hM codebook good
  decoder := codebook

/-- A constant reconstruction code, used to populate finitely many initial
blocklengths before an asymptotic construction becomes available. -/
noncomputable def constantRateDistortionCode
    (hM : 0 < M) [Nonempty Y] : RateDistortionCode X Y n M :=
  codebookCode n M hM
    (fun _ _ => Classical.choice (inferInstance : Nonempty Y))
    (fun _ _ => True)

/-- A probability mass function has a nonempty underlying alphabet. -/
theorem nonempty_of_pmf (P : PMF X) : Nonempty X := by
  obtain ⟨x, _⟩ := P.support_nonempty
  exact ⟨x⟩

/-- A source distribution and a channel out of that source provide a
nonempty reproduction alphabet. -/
theorem nonempty_reproduction_of_source_channel
    (P : PMF X) (W : X → PMF Y) : Nonempty Y := by
  obtain ⟨x, _⟩ := P.support_nonempty
  obtain ⟨y, _⟩ := (W x).support_nonempty
  exact ⟨y⟩

theorem codebookEncoder_good_of_exists
    (hM : 0 < M) (codebook : Index M → Yblock n Y)
    (good : Xblock n X → Yblock n Y → Prop) (x : Xblock n X)
    (hgood : ∃ j, good x (codebook j)) :
    good x (codebook (codebookEncoder n M hM codebook good x)) := by
  classical
  simp only [codebookEncoder, dif_pos hgood]
  exact Fin.find_spec hgood

@[simp] theorem codebookCode_decoder
    (hM : 0 < M) (codebook : Index M → Yblock n Y)
    (good : Xblock n X → Yblock n Y → Prop) :
    (codebookCode n M hM codebook good).decoder = codebook := rfl

-- Average block distortion. The positivity witness rules out the
-- mathematically meaningless zero-length average.
def blockDistortion (hn : 0 < n) (d : Distortion (X := X) (Y := Y))
    (x : Xblock n X) (y : Yblock n Y) : ENNReal :=
  let sum_dist := ∑ i : Fin n, (d (x i) (y i) : ENNReal)
  sum_dist / n

theorem blockDistortion_le_bound
    (hn : 0 < n) (d : Distortion (X := X) (Y := Y))
    (x : Xblock n X) (y : Yblock n Y) :
    blockDistortion n hn d x y ≤ (distortionBound d : ENNReal) := by
  unfold blockDistortion
  apply ENNReal.div_le_of_le_mul
  calc
    ∑ i : Fin n, (d (x i) (y i) : ENNReal) ≤
        ∑ _i : Fin n, (distortionBound d : ENNReal) := by
      exact Finset.sum_le_sum fun i _ =>
        ENNReal.coe_le_coe.mpr (distortion_le_bound d (x i) (y i))
    _ = (distortionBound d : ENNReal) * n := by simp [mul_comm]

-- Rate of a positive-blocklength code.
def codeRate (hn : 0 < n) : ℝ := (Real.log M) / n

/-- The standard exponential-size codebook, rounded down so that its rate
never exceeds the chosen real rate. -/
noncomputable def exponentialCodebookSize (n : ℕ) (rate : ℝ) : ℕ :=
  ⌊Real.exp ((n : ℝ) * rate)⌋₊

theorem exponentialCodebookSize_pos
    (n : ℕ) (rate : ℝ) (hrate : 0 ≤ rate) :
    0 < exponentialCodebookSize n rate := by
  unfold exponentialCodebookSize
  apply Nat.floor_pos.mpr
  calc
    (1 : ℝ) = Real.exp 0 := Real.exp_zero.symm
    _ ≤ Real.exp ((n : ℝ) * rate) :=
      Real.exp_le_exp.mpr (mul_nonneg (Nat.cast_nonneg _) hrate)

/-- Rounding the exponential codebook size down preserves the pointwise rate
upper bound. -/
theorem codeRate_exponentialCodebookSize_le
    (hn : 0 < n) (rate : ℝ) (hrate : 0 ≤ rate) :
    codeRate n (exponentialCodebookSize n rate) hn ≤ rate := by
  have hMpos : 0 < exponentialCodebookSize n rate :=
    exponentialCodebookSize_pos n rate hrate
  have hMposReal : 0 < (exponentialCodebookSize n rate : ℝ) := by
    exact_mod_cast hMpos
  have hfloor : (exponentialCodebookSize n rate : ℝ) ≤
      Real.exp ((n : ℝ) * rate) := by
    unfold exponentialCodebookSize
    exact Nat.floor_le (Real.exp_nonneg _)
  have hnReal : 0 < (n : ℝ) := by exact_mod_cast hn
  unfold codeRate
  apply (div_le_iff₀ hnReal).mpr
  calc
    Real.log (exponentialCodebookSize n rate : ℝ) ≤
        Real.log (Real.exp ((n : ℝ) * rate)) :=
      Real.log_le_log hMposReal hfloor
    _ = (n : ℝ) * rate := Real.log_exp _
    _ = rate * n := mul_comm _ _

/-- Once the unrounded exponential size is at least two, rounding it down
retains at least half of that size. -/
theorem half_exp_le_exponentialCodebookSize
    (n : ℕ) (rate : ℝ)
    (hlarge : 2 ≤ Real.exp ((n : ℝ) * rate)) :
    Real.exp ((n : ℝ) * rate) / 2 ≤
      (exponentialCodebookSize n rate : ℝ) := by
  have hfloorLt : Real.exp ((n : ℝ) * rate) <
      (exponentialCodebookSize n rate : ℝ) + 1 := by
    unfold exponentialCodebookSize
    exact Nat.lt_floor_add_one _
  linarith

/-- A positive exponential rate eventually makes the unrounded codebook size
at least two. -/
theorem exists_nat_two_le_exp_mul_of_pos
    (rate : ℝ) (hrate : 0 < rate) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (2 : ℝ) ≤ Real.exp ((n : ℝ) * rate) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (Real.log 2 / rate)
  refine ⟨N, ?_⟩
  intro n hn
  have hNn : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hquotient : Real.log 2 / rate < (n : ℝ) := hN.trans_le hNn
  have hargument : Real.log 2 < (n : ℝ) * rate :=
    (div_lt_iff₀ hrate).mp hquotient
  calc
    (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
    _ ≤ Real.exp ((n : ℝ) * rate) := Real.exp_le_exp.mpr hargument.le

/-- With an exponential codebook rate strictly above `threshold`, the
random-covering exponent grows at least exponentially in the rate gap. -/
theorem quarter_exp_rateGap_le_exponentialCodebook_coveringExponent
    (n : ℕ) (rate threshold : ℝ)
    (hlarge : 2 ≤ Real.exp ((n : ℝ) * rate)) :
    (1 / 4 : ℝ) * Real.exp ((n : ℝ) * (rate - threshold)) ≤
      (exponentialCodebookSize n rate : ℝ) * (1 / 2 : ℝ) *
        Real.exp (-((n : ℝ) * threshold)) := by
  have hM : Real.exp ((n : ℝ) * rate) / 2 ≤
      (exponentialCodebookSize n rate : ℝ) :=
    half_exp_le_exponentialCodebookSize n rate hlarge
  have hfactor : 0 ≤ (1 / 2 : ℝ) * Real.exp (-((n : ℝ) * threshold)) :=
    mul_nonneg (by norm_num) (Real.exp_nonneg _)
  calc
    (1 / 4 : ℝ) * Real.exp ((n : ℝ) * (rate - threshold)) =
        (Real.exp ((n : ℝ) * rate) / 2) * ((1 / 2 : ℝ) *
          Real.exp (-((n : ℝ) * threshold))) := by
      rw [show (n : ℝ) * (rate - threshold) =
        (n : ℝ) * rate + -((n : ℝ) * threshold) by ring, Real.exp_add]
      ring
    _ ≤ (exponentialCodebookSize n rate : ℝ) * (1 / 2 : ℝ) *
        Real.exp (-((n : ℝ) * threshold)) := by
      simpa [mul_assoc] using mul_le_mul_of_nonneg_right hM hfactor

/-- A strictly positive rate gap makes the random-covering error bound tend to
zero super-exponentially fast. -/
theorem tendsto_exp_neg_quarter_exp_nat_mul
    (gap : ℝ) (hgap : 0 < gap) :
    Tendsto (fun n : ℕ =>
      Real.exp (-((1 / 4 : ℝ) * Real.exp ((n : ℝ) * gap)))) atTop (𝓝 0) := by
  have hlinear : Tendsto (fun n : ℕ => (n : ℝ) * gap) atTop atTop := by
    simpa using
      (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_mul_const hgap
  have hexp : Tendsto (fun n : ℕ =>
      Real.exp ((n : ℝ) * gap)) atTop atTop :=
    Real.tendsto_exp_comp_atTop.mpr hlinear
  have hscaled : Tendsto (fun n : ℕ =>
      (1 / 4 : ℝ) * Real.exp ((n : ℝ) * gap)) atTop atTop :=
    hexp.const_mul_atTop (by norm_num)
  have hneg : Tendsto (fun n : ℕ =>
      -((1 / 4 : ℝ) * Real.exp ((n : ℝ) * gap))) atTop atBot :=
    tendsto_neg_atTop_atBot.comp hscaled
  exact Real.tendsto_exp_comp_nhds_zero.mpr hneg

/-- For every positive error tolerance, the super-exponential random-covering
bound is below that tolerance at all sufficiently large blocklengths. -/
theorem exists_nat_exp_neg_quarter_exp_nat_mul_lt
    (gap ε : ℝ) (hgap : 0 < gap) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      Real.exp (-((1 / 4 : ℝ) * Real.exp ((n : ℝ) * gap))) < ε := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
    ((tendsto_exp_neg_quarter_exp_nat_mul gap hgap).eventually_lt_const hε)
  exact ⟨N, fun n hn => hN n hn⟩

lemma sum_pmf (P : PMF X) : (∑ x : X, P x) = 1 := by
  classical
  simp only [← tsum_coe P,
    tsum_eq_sum (s := Finset.univ)
      (fun b hb => False.elim (hb (Finset.mem_univ b)))]

lemma sum_pmf_toReal (P : PMF X) : (∑ x : X, (P x).toReal) = 1 := by
  rw [← ENNReal.toReal_sum (fun x _ => P.apply_ne_top x), sum_pmf]
  simp

/-- Expectation of a real-valued function on a finite PMF. -/
noncomputable def pmfRealExpectation
    {A : Type*} [Fintype A] (P : PMF A) (f : A → ℝ) : ℝ :=
  ∑ a : A, (P a).toReal * f a

/-- Variance of a real-valued function on a finite PMF. -/
noncomputable def pmfRealVariance
    {A : Type*} [Fintype A] (P : PMF A) (f : A → ℝ) : ℝ :=
  ∑ a : A, (P a).toReal * (f a - pmfRealExpectation P f) ^ 2

theorem pmfRealVariance_eq_expectation
    {A : Type*} [Fintype A] (P : PMF A) (f : A → ℝ) :
    pmfRealVariance P f =
      pmfRealExpectation P (fun a => (f a - pmfRealExpectation P f) ^ 2) := rfl

theorem pmfRealVariance_nonneg
    {A : Type*} [Fintype A] (P : PMF A) (f : A → ℝ) :
    0 ≤ pmfRealVariance P f := by
  unfold pmfRealVariance
  positivity

@[simp] theorem pmfRealVariance_zero
    {A : Type*} [Fintype A] (P : PMF A) :
    pmfRealVariance P (fun _ => 0) = 0 := by
  unfold pmfRealVariance pmfRealExpectation
  simp

/-- Finite-PMF Chebyshev inequality.  It is stated directly as a finite sum
so it can be used without introducing measurable-space structure. -/
theorem pmf_deviation_probability_le_variance_div_sq
    {A : Type*} [Fintype A] [DecidableEq A]
    (P : PMF A) (f : A → ℝ) (ε : ℝ) (hε : 0 < ε) :
    (∑ a : A, if ε ≤ |f a - pmfRealExpectation P f| then P a else 0) ≤
      ENNReal.ofReal (pmfRealVariance P f / ε ^ 2) := by
  have hvar : 0 ≤ pmfRealVariance P f := pmfRealVariance_nonneg P f
  have hεsq : 0 < ε ^ 2 := sq_pos_of_pos hε
  have hterm_top : ∀ a : A,
      (if ε ≤ |f a - pmfRealExpectation P f| then P a else 0) ≠ ⊤ := by
    intro a
    by_cases ha : ε ≤ |f a - pmfRealExpectation P f|
    · rw [if_pos ha]
      exact P.apply_ne_top a
    · rw [if_neg ha]
      exact ENNReal.zero_ne_top
  apply (ENNReal.toReal_le_toReal
    (ENNReal.sum_ne_top.mpr fun a _ => hterm_top a)
    ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_sum (fun a _ => hterm_top a),
    ENNReal.toReal_ofReal (div_nonneg hvar hεsq.le)]
  calc
      (∑ a : A, (if ε ≤ |f a - pmfRealExpectation P f| then P a else 0).toReal) ≤
          ∑ a : A, (P a).toReal *
            ((f a - pmfRealExpectation P f) ^ 2 / ε ^ 2) := by
        apply Finset.sum_le_sum
        intro a _
        by_cases ha : ε ≤ |f a - pmfRealExpectation P f|
        · rw [if_pos ha]
          have hsq : ε ^ 2 ≤ (f a - pmfRealExpectation P f) ^ 2 := by
            rw [sq_le_sq]
            simpa [abs_of_pos hε] using ha
          have hratio : 1 ≤ (f a - pmfRealExpectation P f) ^ 2 / ε ^ 2 :=
            (le_div_iff₀ hεsq).mpr (by simpa using hsq)
          simpa using mul_le_mul_of_nonneg_left hratio (ENNReal.toReal_nonneg : 0 ≤ (P a).toReal)
        · rw [if_neg ha, ENNReal.toReal_zero]
          exact mul_nonneg ENNReal.toReal_nonneg
            (div_nonneg (sq_nonneg _) hεsq.le)
      _ = pmfRealVariance P f / ε ^ 2 := by
        unfold pmfRealVariance
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro a _
        rw [mul_div_assoc]

-- Shannon entropy in nats. It is kept real-valued so that the usual entropy
-- identities can be stated without truncating intermediate signed terms.
noncomputable def shannonEntropy (P : PMF X) : ℝ :=
  ∑ x : X, Real.negMulLog (P x).toReal

theorem shannonEntropy_nonneg (P : PMF X) : 0 ≤ shannonEntropy P := by
  unfold shannonEntropy
  exact Finset.sum_nonneg fun x _ =>
    Real.negMulLog_nonneg ENNReal.toReal_nonneg
      (by
        rw [← ENNReal.toReal_one]
        exact ENNReal.toReal_mono (by simp) (P.coe_le_one x))

theorem shannonEntropy_le_log_card (P : PMF X) :
    shannonEntropy P ≤ Real.log (Fintype.card X) := by
  letI : Nonempty X := ⟨P.support_nonempty.some⟩
  have hk : 0 < (Fintype.card X : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hw : (∑ _x : X, (Fintype.card X : ℝ)⁻¹) = 1 := by
    simp [hk.ne']
  have hj := Real.concaveOn_negMulLog.le_map_sum
    (t := (Finset.univ : Finset X))
    (w := fun _ : X => (Fintype.card X : ℝ)⁻¹)
    (p := fun x : X => (P x).toReal)
    (fun _ _ => inv_nonneg.mpr hk.le)
    (by simpa using hw)
    (fun _ _ => Set.mem_Ici.mpr ENNReal.toReal_nonneg)
  have hj' :
      (Fintype.card X : ℝ)⁻¹ * shannonEntropy P ≤
        Real.negMulLog (Fintype.card X : ℝ)⁻¹ := by
    simpa only [smul_eq_mul, Function.comp_apply, shannonEntropy,
      ← Finset.mul_sum, sum_pmf_toReal, mul_one] using hj
  have hneg :
      Real.negMulLog (Fintype.card X : ℝ)⁻¹ =
        (Fintype.card X : ℝ)⁻¹ * Real.log (Fintype.card X) := by
    simp only [Real.negMulLog, Real.log_inv]
    ring
  calc
    shannonEntropy P = (Fintype.card X : ℝ) *
        ((Fintype.card X : ℝ)⁻¹ * shannonEntropy P) := by
      field_simp
    _ ≤ (Fintype.card X : ℝ) *
        ((Fintype.card X : ℝ)⁻¹ * Real.log (Fintype.card X)) := by
      exact mul_le_mul_of_nonneg_left (hj'.trans_eq hneg) hk.le
    _ = Real.log (Fintype.card X) := by
      field_simp

theorem negMulLog_add_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.negMulLog (a + b) ≤ Real.negMulLog a + Real.negMulLog b := by
  by_cases ha0 : a = 0
  · simp [ha0]
  by_cases hb0 : b = 0
  · simp [hb0]
  have ha_pos : 0 < a := ha.lt_of_ne' ha0
  have hb_pos : 0 < b := hb.lt_of_ne' hb0
  rw [Real.negMulLog, Real.negMulLog, Real.negMulLog]
  calc
    -(a + b) * Real.log (a + b) =
        (-a) * Real.log (a + b) + (-b) * Real.log (a + b) := by ring
    _ ≤ (-a) * Real.log a + (-b) * Real.log b := by
      exact add_le_add
        (mul_le_mul_of_nonpos_left
          (Real.log_le_log ha_pos (le_add_of_nonneg_right hb)) (neg_nonpos.mpr ha))
        (mul_le_mul_of_nonpos_left
          (Real.log_le_log hb_pos (le_add_of_nonneg_left ha)) (neg_nonpos.mpr hb))
    _ = -a * Real.log a + -b * Real.log b := by ring

theorem negMulLog_sum_le_sum
    {A : Type*} (s : Finset A) (f : A → ℝ)
    (hf : ∀ a ∈ s, 0 ≤ f a) :
    Real.negMulLog (∑ a ∈ s, f a) ≤ ∑ a ∈ s, Real.negMulLog (f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact (negMulLog_add_le (f a) (∑ x ∈ s, f x)
        (hf a (Finset.mem_insert_self a s))
        (Finset.sum_nonneg fun x hx => hf x (Finset.mem_insert_of_mem hx))).trans
        (add_le_add le_rfl (ih fun x hx => hf x (Finset.mem_insert_of_mem hx)))

theorem map_apply_toReal
    {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]
    (Q : PMF A) (f : A → B) (b : B) :
    ((Q.map f) b).toReal =
      ∑ a : A, if b = f a then (Q a).toReal else 0 := by
  classical
  rw [PMF.map_apply, tsum_fintype]
  rw [ENNReal.toReal_sum (fun a _ => by
    by_cases h : b = f a <;> simp [h, Q.apply_ne_top a])]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : b = f a <;> simp [h]

theorem map_apply_equiv
    {A B : Type*} [Fintype A] [Fintype B]
    (P : PMF A) (e : A ≃ B) (b : B) :
    P.map e b = P (e.symm b) := by
  classical
  rw [PMF.map_apply, tsum_fintype]
  calc
    (∑ a : A, if b = e a then P a else 0) =
        ∑ c : B, if b = c then P (e.symm c) else 0 := by
      exact Fintype.sum_equiv e _ _ fun a => by simp
    _ = P (e.symm b) := by simp

theorem shannonEntropy_map_le
    {A B : Type*} [Fintype A] [Fintype B]
    (Q : PMF A) (f : A → B) :
    shannonEntropy (Q.map f) ≤ shannonEntropy Q := by
  classical
  simp only [shannonEntropy, map_apply_toReal]
  calc
    (∑ b : B, Real.negMulLog
        (∑ a : A, if b = f a then (Q a).toReal else 0)) ≤
        ∑ b : B, ∑ a : A,
          Real.negMulLog (if b = f a then (Q a).toReal else 0) := by
      exact Finset.sum_le_sum fun b _ =>
        negMulLog_sum_le_sum Finset.univ
          (fun a : A => if b = f a then (Q a).toReal else 0)
          (fun a _ => by
            change 0 ≤ if b = f a then (Q a).toReal else 0
            by_cases h : b = f a <;> simp [h, ENNReal.toReal_nonneg])
    _ = ∑ a : A, ∑ b : B,
        Real.negMulLog (if b = f a then (Q a).toReal else 0) :=
      Finset.sum_comm
    _ = ∑ a : A, Real.negMulLog (Q a).toReal := by
      apply Finset.sum_congr rfl
      intro a _
      calc
        (∑ b : B, Real.negMulLog
            (if b = f a then (Q a).toReal else 0)) =
            ∑ b : B, if b = f a then Real.negMulLog (Q a).toReal else 0 := by
          apply Finset.sum_congr rfl
          intro b _
          by_cases h : b = f a <;> simp [h]
        _ = Real.negMulLog (Q a).toReal := by
          exact Fintype.sum_ite_eq' (f a) (fun _ => Real.negMulLog (Q a).toReal)

theorem shannonEntropy_map_of_injective
    {A B : Type*} [Fintype A] [Fintype B]
    (Q : PMF A) (f : A → B) (hf : Function.Injective f) :
    shannonEntropy (Q.map f) = shannonEntropy Q := by
  classical
  letI : Nonempty A := ⟨Q.support_nonempty.some⟩
  apply le_antisymm (shannonEntropy_map_le Q f)
  have hleft : (Q.map f).map (Function.invFun f) = Q := by
    rw [PMF.map_comp]
    rw [show Function.invFun f ∘ f = id by
      funext a
      exact Function.leftInverse_invFun hf a]
    exact PMF.map_id Q
  have hrev := shannonEntropy_map_le (Q.map f) (Function.invFun f)
  rw [hleft] at hrev
  exact hrev

theorem pmf_toMeasure_absolutelyContinuous_of_support_subset
    {A : Type*} [MeasurableSpace A] [MeasurableSingletonClass A]
    (P Q : PMF A) (hPQ : P.support ⊆ Q.support) :
    P.toMeasure ≪ Q.toMeasure := by
  apply Measure.AbsolutelyContinuous.mk
  intro s hs hQs
  rw [P.toMeasure_apply_eq_zero_iff hs]
  have hdisj : Disjoint Q.support s :=
    (Q.toMeasure_apply_eq_zero_iff hs).mp hQs
  exact hdisj.mono hPQ le_rfl

def pmfDensityRatio {A : Type*} (P Q : PMF A) (a : A) : ENNReal :=
  P a * (Q a)⁻¹

theorem pmfDensityRatio_mul
    {A : Type*} (P Q : PMF A) (hPQ : P.support ⊆ Q.support) (a : A) :
    pmfDensityRatio P Q a * Q a = P a := by
  by_cases hq : Q a = 0
  · have haQ : a ∉ Q.support := (Q.apply_eq_zero_iff a).mp hq
    have haP : a ∉ P.support := fun ha => haQ (hPQ ha)
    have hp : P a = 0 := (P.apply_eq_zero_iff a).mpr haP
    simp [pmfDensityRatio, hq, hp]
  · rw [pmfDensityRatio, mul_assoc,
      ENNReal.inv_mul_cancel hq (Q.apply_ne_top a), mul_one]

theorem withDensity_pmfDensityRatio
    {A : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    (P Q : PMF A) (hPQ : P.support ⊆ Q.support) :
    Q.toMeasure.withDensity (pmfDensityRatio P Q) = P.toMeasure := by
  apply Measure.ext_of_singleton
  intro a
  rw [withDensity_apply _ (measurableSet_singleton a),
    lintegral_singleton,
    Q.toMeasure_apply_singleton a (measurableSet_singleton a),
    P.toMeasure_apply_singleton a (measurableSet_singleton a)]
  exact pmfDensityRatio_mul P Q hPQ a

theorem rnDeriv_pmf_eq_densityRatio
    {A : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    (P Q : PMF A) (hPQ : P.support ⊆ Q.support) :
    P.toMeasure.rnDeriv Q.toMeasure =ᵐ[Q.toMeasure] pmfDensityRatio P Q := by
  rw [← withDensity_pmfDensityRatio P Q hPQ]
  exact Measure.rnDeriv_withDensity Q.toMeasure
    (measurable_of_finite (pmfDensityRatio P Q))

theorem llr_pmf_ae_eq_log_densityRatio
    {A : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    (P Q : PMF A) (hPQ : P.support ⊆ Q.support) :
    llr P.toMeasure Q.toMeasure =ᵐ[P.toMeasure]
      fun a => Real.log (pmfDensityRatio P Q a).toReal := by
  have hac : P.toMeasure ≪ Q.toMeasure :=
    pmf_toMeasure_absolutelyContinuous_of_support_subset P Q hPQ
  filter_upwards [hac.ae_le (rnDeriv_pmf_eq_densityRatio P Q hPQ)] with a ha
  simp only [llr, ha]

theorem sum_map_mul
    {A B : Type*} [Fintype A] [Fintype B]
    (Q : PMF A) (f : A → B) (g : B → ENNReal) :
    (∑ b : B, (Q.map f) b * g b) = ∑ a : A, Q a * g (f a) := by
  classical
  letI : DecidableEq B := Classical.decEq B
  simp only [PMF.map_apply, tsum_fintype]
  calc
    (∑ b : B, (∑ a : A, if b = f a then Q a else 0) * g b) =
        ∑ b : B, ∑ a : A, if b = f a then Q a * g b else 0 := by
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a _
      by_cases hba : b = f a <;> simp [hba]
    _ = ∑ a : A, ∑ b : B, if b = f a then Q a * g b else 0 :=
      Finset.sum_comm
    _ = ∑ a : A, Q a * g (f a) := by
      apply Finset.sum_congr rfl
      intro a _
      exact Fintype.sum_ite_eq' (f a) (fun b => Q a * g b)

theorem sum_map_mul_toReal
    {A B : Type*} [Fintype A] [Fintype B]
    (Q : PMF A) (f : A → B) (g : B → ℝ) :
    (∑ b : B, ((Q.map f) b).toReal * g b) =
      ∑ a : A, (Q a).toReal * g (f a) := by
  classical
  simp only [map_apply_toReal]
  calc
    (∑ b : B, (∑ a : A, if b = f a then (Q a).toReal else 0) * g b) =
        ∑ b : B, ∑ a : A,
          if b = f a then (Q a).toReal * g b else 0 := by
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a _
      by_cases hba : b = f a <;> simp [hba]
    _ = ∑ a : A, ∑ b : B,
        if b = f a then (Q a).toReal * g b else 0 := Finset.sum_comm
    _ = ∑ a : A, (Q a).toReal * g (f a) := by
      apply Finset.sum_congr rfl
      intro a _
      exact Fintype.sum_ite_eq' (f a) (fun b => (Q a).toReal * g b)

/-- Change of variables for a finite-PMF real expectation. -/
theorem pmfRealExpectation_map
    {A B : Type*} [Fintype A] [Fintype B]
    (Q : PMF A) (f : A → B) (g : B → ℝ) :
    pmfRealExpectation (Q.map f) g = pmfRealExpectation Q (g ∘ f) := by
  unfold pmfRealExpectation
  simpa using sum_map_mul_toReal Q f g

/-- Variance is preserved by changing variables along a finite PMF map. -/
theorem pmfRealVariance_map
    {A B : Type*} [Fintype A] [Fintype B]
    (Q : PMF A) (f : A → B) (g : B → ℝ) :
    pmfRealVariance (Q.map f) g = pmfRealVariance Q (g ∘ f) := by
  unfold pmfRealVariance
  rw [pmfRealExpectation_map]
  simpa [Function.comp_def] using
    (sum_map_mul_toReal Q f
      (fun b => (g b - pmfRealExpectation Q (g ∘ f)) ^ 2))

@[simp] theorem pmfRealExpectation_zero
    {A : Type*} [Fintype A] (P : PMF A) :
    pmfRealExpectation P (fun _ => 0) = 0 := by
  unfold pmfRealExpectation
  simp

theorem pmfRealExpectation_add
    {A : Type*} [Fintype A] (P : PMF A) (f g : A → ℝ) :
    pmfRealExpectation P (fun a => f a + g a) =
      pmfRealExpectation P f + pmfRealExpectation P g := by
  unfold pmfRealExpectation
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]

theorem pmfRealExpectation_const_mul
    {A : Type*} [Fintype A] (P : PMF A) (c : ℝ) (f : A → ℝ) :
    pmfRealExpectation P (fun a => c * f a) = c * pmfRealExpectation P f := by
  unfold pmfRealExpectation
  calc
    (∑ a : A, (P a).toReal * (c * f a)) =
        ∑ a : A, c * ((P a).toReal * f a) := by
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = c * ∑ a : A, (P a).toReal * f a := by rw [Finset.mul_sum]

theorem sum_mul_log_eq_neg_shannonEntropy (P : PMF X) :
    (∑ x : X, (P x).toReal * Real.log (P x).toReal) =
      -shannonEntropy P := by
  simp only [shannonEntropy, Real.negMulLog, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem sum_bind_mul
    {A B : Type*} [Fintype A] [Fintype B]
    (Q : PMF A) (W : A → PMF B) (g : B → ENNReal) :
    (∑ b : B, (Q.bind W) b * g b) =
      ∑ a : A, Q a * ∑ b : B, W a b * g b := by
  classical
  simp only [PMF.bind_apply, tsum_fintype]
  calc
    (∑ b : B, (∑ a : A, Q a * W a b) * g b) =
        ∑ b : B, ∑ a : A, Q a * (W a b * g b) := by
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a _
      rw [mul_assoc]
    _ = ∑ a : A, ∑ b : B, Q a * (W a b * g b) := Finset.sum_comm
    _ = ∑ a : A, Q a * ∑ b : B, W a b * g b := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.mul_sum]


/-- KL divergence of two finite probability mass functions. -/
noncomputable def kl_divergence (P Q : PMF X) : ENNReal :=
  letI : MeasurableSpace X := ⊤
  InformationTheory.klDiv P.toMeasure Q.toMeasure

theorem kl_divergence_eq_ofReal_sum
    (P Q : PMF X) (hPQ : P.support ⊆ Q.support) :
    kl_divergence P Q =
      ENNReal.ofReal (∑ a : X, (P a).toReal *
        Real.log (pmfDensityRatio P Q a).toReal) := by
  letI : MeasurableSpace X := ⊤
  have hac : P.toMeasure ≪ Q.toMeasure :=
    pmf_toMeasure_absolutelyContinuous_of_support_subset P Q hPQ
  have hint : Integrable (llr P.toMeasure Q.toMeasure) P.toMeasure :=
    Integrable.of_finite
  change InformationTheory.klDiv P.toMeasure Q.toMeasure = _
  rw [InformationTheory.klDiv_of_ac_of_integrable hac hint]
  congr 1
  rw [integral_congr_ae (llr_pmf_ae_eq_log_densityRatio P Q hPQ)]
  rw [PMF.integral_eq_sum]
  simp

/-- definition of product distribution Q_XY = P_X ⊗ P_Y -/
def product_pmf (P_X : PMF X) (P_Y : PMF Y) : PMF (X × Y) :=
  P_X.bind (fun x => P_Y.map (fun y => (x, y)))


/-- Mutual information based on KL divergence. -/
noncomputable def mutual_information (P_XY : PMF (X × Y)) : ENNReal :=
  let P_X := P_XY.map Prod.fst -- marginal p x
  let P_Y := P_XY.map Prod.snd -- marginal p y
  --mutual information is given by D(P_XY||Q_XY)
  kl_divergence P_XY (product_pmf P_X P_Y)

-- The entropy expression for finite-alphabet mutual information. A later
-- bridge lemma will identify its nonnegative ENNReal coercion with the KL form.
noncomputable def mutualInformationEntropy (P_XY : PMF (X × Y)) : ℝ :=
  shannonEntropy (P_XY.map Prod.fst) +
    shannonEntropy (P_XY.map Prod.snd) - shannonEntropy P_XY

/-
  definition of Single-letter expected distortion.
  correspond to E[d(X, X_hat)] = ∑ p(x)p(x_hat|x)d(x, x_hat)
  here P is p(x), W is p(\hat{x}|x)
-/

noncomputable def expected_distortion_single
  (P : PMF X)
  (W : X → PMF Y)
  (d : Distortion (X := X) (Y := Y)) : ENNReal :=
  ∑ x, P x * (∑ y, (W x) y * (d x y : ENNReal))

/--
  The joint distribution p(x, y) induced by a source distribution P
  and a conditional distribution (test channel) W.
  Calculated as: p(x, y) = p(x) * p(y | x).
-/
def induced_joint (P : PMF X) (W : X → PMF Y) : PMF (X × Y) :=
  P.bind (fun x => (W x).map (fun y => (x, y)))

@[simp] theorem induced_joint_apply
    (P : PMF X) (W : X → PMF Y) (x : X) (y : Y) :
    induced_joint P W (x, y) = P x * W x y := by
  simp only [induced_joint, PMF.bind_apply, PMF.map_apply, tsum_fintype]
  calc
    _ = ∑ a, if x = a then P a * W a y else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      by_cases hxa : x = a
      · subst a
        simp
      · simp [hxa]
    _ = P x * W x y := by simp

@[simp] theorem induced_joint_fst
    (P : PMF X) (W : X → PMF Y) :
    (induced_joint P W).map Prod.fst = P := by
  ext x
  simp only [PMF.map_apply, tsum_fintype]
  rw [Fintype.sum_prod_type]
  simp only [induced_joint_apply]
  simp
  rw [← Finset.mul_sum, sum_pmf, mul_one]

theorem induced_joint_snd_apply
    (P : PMF X) (W : X → PMF Y) (y : Y) :
    ((induced_joint P W).map Prod.snd) y = ∑ x : X, P x * W x y := by
  simp only [PMF.map_apply, tsum_fintype]
  rw [Fintype.sum_prod_type]
  simp [induced_joint_apply]

@[simp] theorem induced_joint_snd
    (P : PMF X) (W : X → PMF Y) :
    (induced_joint P W).map Prod.snd = P.bind W := by
  ext y
  rw [induced_joint_snd_apply, PMF.bind_apply, tsum_fintype]

theorem bind_apply_toReal
    {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (P : PMF A) (W : A → PMF B) (b : B) :
    ((P.bind W) b).toReal =
      ∑ a : A, (P a).toReal * (W a b).toReal := by
  rw [PMF.bind_apply, tsum_fintype]
  rw [ENNReal.toReal_sum (fun a _ =>
    ENNReal.mul_ne_top (P.apply_ne_top a) ((W a).apply_ne_top b))]
  simp only [ENNReal.toReal_mul]

theorem sum_weighted_entropy_le_entropy_bind
    {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (P : PMF A) (W : A → PMF B) :
    (∑ a : A, (P a).toReal * shannonEntropy (W a)) ≤
      shannonEntropy (P.bind W) := by
  have hjensen : ∀ b : B,
      (∑ a : A, (P a).toReal * Real.negMulLog (W a b).toReal) ≤
        Real.negMulLog ((P.bind W) b).toReal := by
    intro b
    have hj := Real.concaveOn_negMulLog.le_map_sum
      (t := (Finset.univ : Finset A))
      (w := fun a : A => (P a).toReal)
      (p := fun a : A => (W a b).toReal)
      (fun _ _ => ENNReal.toReal_nonneg)
      (by simpa using sum_pmf_toReal P)
      (fun _ _ => Set.mem_Ici.mpr ENNReal.toReal_nonneg)
    simpa only [smul_eq_mul, Function.comp_apply, bind_apply_toReal] using hj
  calc
    (∑ a : A, (P a).toReal * shannonEntropy (W a)) =
        ∑ a : A, ∑ b : B,
          (P a).toReal * Real.negMulLog (W a b).toReal := by
      apply Finset.sum_congr rfl
      intro a _
      rw [shannonEntropy, Finset.mul_sum]
    _ = ∑ b : B, ∑ a : A,
        (P a).toReal * Real.negMulLog (W a b).toReal := Finset.sum_comm
    _ ≤ ∑ b : B, Real.negMulLog ((P.bind W) b).toReal := by
      exact Finset.sum_le_sum fun b _ => hjensen b
    _ = shannonEntropy (P.bind W) := by
      rfl

theorem shannonEntropy_induced_joint
    (P : PMF X) (W : X → PMF Y) :
    shannonEntropy (induced_joint P W) =
      shannonEntropy P +
        ∑ x : X, (P x).toReal * shannonEntropy (W x) := by
  calc
    shannonEntropy (induced_joint P W) =
        ∑ x : X, ∑ y : Y,
          Real.negMulLog (induced_joint P W (x, y)).toReal := by
      rw [shannonEntropy, Fintype.sum_prod_type]
    _ = ∑ x : X, ∑ y : Y,
        ((W x y).toReal * Real.negMulLog (P x).toReal +
          (P x).toReal * Real.negMulLog (W x y).toReal) := by
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      rw [induced_joint_apply, ENNReal.toReal_mul, Real.negMulLog_mul]
    _ = ∑ x : X,
          ((∑ y : Y, (W x y).toReal) * Real.negMulLog (P x).toReal +
            (P x).toReal * ∑ y : Y, Real.negMulLog (W x y).toReal) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
    _ = ∑ x : X,
        (Real.negMulLog (P x).toReal +
          (P x).toReal * ∑ y : Y, Real.negMulLog (W x y).toReal) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [sum_pmf_toReal, one_mul]
    _ = (∑ x : X, Real.negMulLog (P x).toReal) +
        ∑ x : X, (P x).toReal *
          ∑ y : Y, Real.negMulLog (W x y).toReal := by
      rw [Finset.sum_add_distrib]
    _ = shannonEntropy P +
        ∑ x : X, (P x).toReal * shannonEntropy (W x) := by
      rfl

theorem shannonEntropy_product_pmf (P : PMF X) (Q : PMF Y) :
    shannonEntropy (product_pmf P Q) =
      shannonEntropy P + shannonEntropy Q := by
  change shannonEntropy (induced_joint P (fun _ => Q)) = _
  rw [shannonEntropy_induced_joint]
  rw [← Finset.sum_mul, sum_pmf_toReal, one_mul]

theorem induced_joint_map_snd
    {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (P : PMF A) (W : A → PMF B) (f : B → C) :
    (induced_joint P W).map (fun z => (z.1, f z.2)) =
      induced_joint P (fun a => (W a).map f) := by
  unfold induced_joint
  rw [PMF.map_bind]
  congr 1
  funext a
  rw [PMF.map_comp, PMF.map_comp]
  rfl

theorem fstMarginal_apply
    (Q : PMF (X × Y)) (x : X) :
    (Q.map Prod.fst) x = ∑ y : Y, Q (x, y) := by
  simp only [PMF.map_apply, tsum_fintype]
  rw [Fintype.sum_prod_type]
  calc
    _ = ∑ a : X, if x = a then (∑ y : Y, Q (a, y)) else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      by_cases hxa : x = a
      · subst a
        simp
      · simp [hxa]
    _ = ∑ y : Y, Q (x, y) := by simp

theorem sndMarginal_apply
    (Q : PMF (X × Y)) (y : Y) :
    (Q.map Prod.snd) y = ∑ x : X, Q (x, y) := by
  classical
  letI : DecidableEq Y := Classical.decEq Y
  simp only [PMF.map_apply, tsum_fintype]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _
  simp only [Prod.snd]
  exact Fintype.sum_ite_eq y (fun b => Q (x, b))

-- A finite conditional distribution. On a zero-mass input fiber, the output
-- marginal is used as an arbitrary fallback distribution.
noncomputable def conditionalPMF
    (Q : PMF (X × Y)) (x : X) : PMF Y :=
  if hx : (Q.map Prod.fst) x = 0 then
    Q.map Prod.snd
  else
    PMF.normalize (fun y => Q (x, y))
      (by
        rw [tsum_fintype, ← fstMarginal_apply Q x]
        exact hx)
      (by
        rw [tsum_fintype, ← fstMarginal_apply Q x]
        exact (Q.map Prod.fst).apply_ne_top x)

theorem conditionalPMF_eq_snd_of_fst_eq_zero
    (Q : PMF (X × Y)) (x : X) (hx : (Q.map Prod.fst) x = 0) :
    conditionalPMF Q x = Q.map Prod.snd := by
  simp [conditionalPMF, hx]

theorem conditionalPMF_apply_of_fst_ne_zero
    (Q : PMF (X × Y)) (x : X) (y : Y)
    (hx : (Q.map Prod.fst) x ≠ 0) :
    conditionalPMF Q x y = Q (x, y) * ((Q.map Prod.fst) x)⁻¹ := by
  simp only [conditionalPMF, dif_neg hx, PMF.normalize_apply]
  rw [tsum_fintype, ← fstMarginal_apply Q x]

theorem induced_joint_conditionalPMF
    (Q : PMF (X × Y)) :
    induced_joint (Q.map Prod.fst) (conditionalPMF Q) = Q := by
  ext z
  rcases z with ⟨x, y⟩
  rw [induced_joint_apply]
  by_cases hx : (Q.map Prod.fst) x = 0
  · rw [hx, zero_mul]
    have hsum : (∑ b : Y, Q (x, b)) = 0 := by
      rw [← fstMarginal_apply Q x]
      exact hx
    have hzero : ∀ b ∈ (Finset.univ : Finset Y), Q (x, b) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun _ _ => bot_le).mp hsum
    exact (hzero y (Finset.mem_univ y)).symm
  · rw [conditionalPMF_apply_of_fst_ne_zero Q x y hx]
    calc
      (Q.map Prod.fst) x * (Q (x, y) * ((Q.map Prod.fst) x)⁻¹) =
          Q (x, y) * ((Q.map Prod.fst) x * ((Q.map Prod.fst) x)⁻¹) := by
        ac_rfl
      _ = Q (x, y) * 1 := by
        rw [ENNReal.mul_inv_cancel hx ((Q.map Prod.fst).apply_ne_top x)]
      _ = Q (x, y) := mul_one _

-- Conditional entropy H(Y|X), with conditioning on the first coordinate.
noncomputable def conditionalEntropy (Q : PMF (X × Y)) : ℝ :=
  shannonEntropy Q - shannonEntropy (Q.map Prod.fst)

theorem conditionalEntropy_eq_sum (Q : PMF (X × Y)) :
    conditionalEntropy Q =
      ∑ x : X, ((Q.map Prod.fst) x).toReal *
        shannonEntropy (conditionalPMF Q x) := by
  calc
    conditionalEntropy Q =
        shannonEntropy (induced_joint (Q.map Prod.fst) (conditionalPMF Q)) -
          shannonEntropy (Q.map Prod.fst) := by
      rw [conditionalEntropy, induced_joint_conditionalPMF]
    _ = ∑ x : X, ((Q.map Prod.fst) x).toReal *
        shannonEntropy (conditionalPMF Q x) := by
      rw [shannonEntropy_induced_joint]
      ring

theorem conditionalEntropy_nonneg (Q : PMF (X × Y)) :
    0 ≤ conditionalEntropy Q := by
  rw [conditionalEntropy_eq_sum]
  exact Finset.sum_nonneg fun x _ =>
    mul_nonneg ENNReal.toReal_nonneg
      (shannonEntropy_nonneg (conditionalPMF Q x))

theorem bind_conditionalPMF_eq_snd (Q : PMF (X × Y)) :
    (Q.map Prod.fst).bind (conditionalPMF Q) = Q.map Prod.snd := by
  have h := congrArg (PMF.map Prod.snd) (induced_joint_conditionalPMF Q)
  simpa only [induced_joint_snd] using h

theorem conditionalEntropy_le_snd_entropy (Q : PMF (X × Y)) :
    conditionalEntropy Q ≤ shannonEntropy (Q.map Prod.snd) := by
  rw [conditionalEntropy_eq_sum, ← bind_conditionalPMF_eq_snd Q]
  exact sum_weighted_entropy_le_entropy_bind
    (Q.map Prod.fst) (conditionalPMF Q)

theorem shannonEntropy_joint_le_add_marginals (Q : PMF (X × Y)) :
    shannonEntropy Q ≤
      shannonEntropy (Q.map Prod.fst) + shannonEntropy (Q.map Prod.snd) := by
  have h := conditionalEntropy_le_snd_entropy Q
  unfold conditionalEntropy at h
  linarith

theorem mutualInformationEntropy_nonneg (Q : PMF (X × Y)) :
    0 ≤ mutualInformationEntropy Q := by
  have h := shannonEntropy_joint_le_add_marginals Q
  unfold mutualInformationEntropy
  linarith

theorem shannonEntropy_induced_joint_strong_subadditivity
    {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (P : PMF A) (W : A → PMF (B × C)) :
    shannonEntropy (induced_joint P (fun a => (W a).map Prod.fst)) +
        shannonEntropy (induced_joint P (fun a => (W a).map Prod.snd)) ≥
      shannonEntropy P + shannonEntropy (induced_joint P W) := by
  have hsum :
      (∑ a : A, (P a).toReal * shannonEntropy (W a)) ≤
        (∑ a : A, (P a).toReal * shannonEntropy ((W a).map Prod.fst)) +
          ∑ a : A, (P a).toReal * shannonEntropy ((W a).map Prod.snd) := by
    calc
      (∑ a : A, (P a).toReal * shannonEntropy (W a)) ≤
          ∑ a : A, (P a).toReal *
            (shannonEntropy ((W a).map Prod.fst) +
              shannonEntropy ((W a).map Prod.snd)) := by
        exact Finset.sum_le_sum fun a _ =>
          mul_le_mul_of_nonneg_left
            (shannonEntropy_joint_le_add_marginals (W a))
            ENNReal.toReal_nonneg
      _ = (∑ a : A, (P a).toReal *
            shannonEntropy ((W a).map Prod.fst)) +
          ∑ a : A, (P a).toReal *
            shannonEntropy ((W a).map Prod.snd) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro a _
        ring
  rw [shannonEntropy_induced_joint, shannonEntropy_induced_joint,
    shannonEntropy_induced_joint]
  linarith

theorem shannonEntropy_strong_subadditivity
    {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (Q : PMF (A × (B × C))) :
    shannonEntropy (Q.map (fun z => (z.1, z.2.1))) +
        shannonEntropy (Q.map (fun z => (z.1, z.2.2))) ≥
      shannonEntropy (Q.map Prod.fst) + shannonEntropy Q := by
  let P : PMF A := Q.map Prod.fst
  let W : A → PMF (B × C) := conditionalPMF Q
  have hQ : induced_joint P W = Q := by
    exact induced_joint_conditionalPMF Q
  have hAB :
      Q.map (fun z => (z.1, z.2.1)) =
        induced_joint P (fun a => (W a).map Prod.fst) := by
    rw [← hQ, induced_joint_map_snd]
  have hAC :
      Q.map (fun z => (z.1, z.2.2)) =
        induced_joint P (fun a => (W a).map Prod.snd) := by
    rw [← hQ, induced_joint_map_snd]
  calc
    shannonEntropy (Q.map (fun z => (z.1, z.2.1))) +
        shannonEntropy (Q.map (fun z => (z.1, z.2.2))) =
        shannonEntropy (induced_joint P (fun a => (W a).map Prod.fst)) +
          shannonEntropy (induced_joint P (fun a => (W a).map Prod.snd)) := by
      rw [hAB, hAC]
    _ ≥ shannonEntropy P + shannonEntropy (induced_joint P W) :=
      shannonEntropy_induced_joint_strong_subadditivity P W
    _ = shannonEntropy (Q.map Prod.fst) + shannonEntropy Q := by
      rw [hQ]

theorem conditionalEntropy_more_conditioning_le
    {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (Q : PMF (A × (B × C))) :
    conditionalEntropy
        (Q.map (fun z => ((z.1, z.2.1), z.2.2))) ≤
      conditionalEntropy (Q.map (fun z => (z.1, z.2.2))) := by
  have hinj : Function.Injective
      (fun z : A × (B × C) => ((z.1, z.2.1), z.2.2)) := by
    intro z z' h
    have h' := congrArg
      (fun w : (A × B) × C => (w.1.1, (w.1.2, w.2))) h
    simpa using h'
  have hfull :
      shannonEntropy (Q.map (fun z => ((z.1, z.2.1), z.2.2))) =
        shannonEntropy Q :=
    shannonEntropy_map_of_injective Q _ hinj
  have hAB :
      (Q.map (fun z => ((z.1, z.2.1), z.2.2))).map Prod.fst =
        Q.map (fun z => (z.1, z.2.1)) := by
    rw [PMF.map_comp]
    rfl
  have hA :
      (Q.map (fun z => (z.1, z.2.2))).map Prod.fst =
        Q.map Prod.fst := by
    rw [PMF.map_comp]
    rfl
  have hssa := shannonEntropy_strong_subadditivity Q
  unfold conditionalEntropy
  rw [hfull, hAB, hA]
  linarith

theorem conditionalEntropy_pair_le_add
    {A B C D : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]
    (Q : PMF ((C × D) × (A × B))) :
    conditionalEntropy Q ≤
      conditionalEntropy (Q.map (fun z => (z.1.1, z.2.1))) +
        conditionalEntropy (Q.map (fun z => (z.1.2, z.2.2))) := by
  let QA : PMF (C × (D × A)) :=
    Q.map (fun z => (z.1.1, (z.1.2, z.2.1)))
  let QB : PMF (D × (C × B)) :=
    Q.map (fun z => (z.1.2, (z.1.1, z.2.2)))
  have hA := conditionalEntropy_more_conditioning_le QA
  have hB := conditionalEntropy_more_conditioning_le QB
  have hssa := shannonEntropy_strong_subadditivity Q
  unfold conditionalEntropy at hA hB ⊢
  simp only [QA, QB, PMF.map_comp] at hA hB
  simp only [PMF.map_comp]
  change
    shannonEntropy Q - shannonEntropy (Q.map Prod.fst) ≤
      (shannonEntropy (Q.map (fun z => (z.1.1, z.2.1))) -
          shannonEntropy (Q.map (fun z => z.1.1))) +
        (shannonEntropy (Q.map (fun z => (z.1.2, z.2.2))) -
          shannonEntropy (Q.map (fun z => z.1.2)))
  change
    shannonEntropy
        (Q.map (fun z => ((z.1.1, z.1.2), z.2.1))) -
        shannonEntropy (Q.map (fun z => (z.1.1, z.1.2))) ≤
      shannonEntropy (Q.map (fun z => (z.1.1, z.2.1))) -
        shannonEntropy (Q.map (fun z => z.1.1)) at hA
  change
    shannonEntropy
        (Q.map (fun z => ((z.1.2, z.1.1), z.2.2))) -
        shannonEntropy (Q.map (fun z => (z.1.2, z.1.1))) ≤
      shannonEntropy (Q.map (fun z => (z.1.2, z.2.2))) -
        shannonEntropy (Q.map (fun z => z.1.2)) at hB
  have hA' :
      shannonEntropy (Q.map (fun z => (z.1, z.2.1))) -
          shannonEntropy (Q.map Prod.fst) ≤
        shannonEntropy (Q.map (fun z => (z.1.1, z.2.1))) -
          shannonEntropy (Q.map (fun z => z.1.1)) := by
    simpa using hA
  have hB' :
      shannonEntropy (Q.map (fun z => (z.1, z.2.2))) -
          shannonEntropy (Q.map Prod.fst) ≤
        shannonEntropy (Q.map (fun z => (z.1.2, z.2.2))) -
          shannonEntropy (Q.map (fun z => z.1.2)) := by
    have hswapCond :
        shannonEntropy (Q.map (fun z => (z.1.2, z.1.1))) =
          shannonEntropy (Q.map Prod.fst) := by
      calc
        shannonEntropy (Q.map (fun z => (z.1.2, z.1.1))) =
            shannonEntropy ((Q.map Prod.fst).map Prod.swap) := by
          rw [PMF.map_comp]
          rfl
        _ = shannonEntropy (Q.map Prod.fst) :=
          shannonEntropy_map_of_injective _ Prod.swap Prod.swap_injective
    have hswapFull :
        shannonEntropy (Q.map (fun z => ((z.1.2, z.1.1), z.2.2))) =
          shannonEntropy (Q.map (fun z => (z.1, z.2.2))) := by
      let swapCond : ((C × D) × B) → ((D × C) × B) :=
        fun z => ((z.1.2, z.1.1), z.2)
      have hinj : Function.Injective swapCond := by
        intro z z' h
        have h' := congrArg
          (fun w : (D × C) × B => ((w.1.2, w.1.1), w.2)) h
        simpa [swapCond] using h'
      calc
        shannonEntropy (Q.map (fun z => ((z.1.2, z.1.1), z.2.2))) =
            shannonEntropy
              ((Q.map (fun z => (z.1, z.2.2))).map swapCond) := by
          rw [PMF.map_comp]
          rfl
        _ = shannonEntropy (Q.map (fun z => (z.1, z.2.2))) :=
          shannonEntropy_map_of_injective _ swapCond hinj
    rw [hswapFull, hswapCond] at hB
    exact hB
  have hsplit :
      shannonEntropy Q - shannonEntropy (Q.map Prod.fst) ≤
        (shannonEntropy (Q.map (fun z => (z.1, z.2.1))) -
            shannonEntropy (Q.map Prod.fst)) +
          (shannonEntropy (Q.map (fun z => (z.1, z.2.2))) -
            shannonEntropy (Q.map Prod.fst)) := by
    linarith
  linarith

theorem conditionalEntropy_pi_le_sum
    {A C : Type*} [Fintype A] [Fintype C]
    [DecidableEq A] [DecidableEq C]
    (k : ℕ) (Q : PMF ((Fin k → C) × (Fin k → A))) :
    conditionalEntropy Q ≤
      ∑ i : Fin k, conditionalEntropy (Q.map (fun z => (z.1 i, z.2 i))) := by
  induction k with
  | zero =>
      calc
        conditionalEntropy Q ≤ shannonEntropy (Q.map Prod.snd) :=
          conditionalEntropy_le_snd_entropy Q
        _ ≤ Real.log (Fintype.card (Fin 0 → A)) :=
          shannonEntropy_le_log_card (Q.map Prod.snd)
        _ = 0 := by simp
        _ = ∑ i : Fin 0,
            conditionalEntropy (Q.map (fun z => (z.1 i, z.2 i))) := by simp
  | succ k ih =>
      let split :
          ((Fin (k + 1) → C) × (Fin (k + 1) → A)) →
            (((Fin k → C) × C) × ((Fin k → A) × A)) :=
        fun z => ((Fin.init z.1, z.1 (Fin.last k)),
          (Fin.init z.2, z.2 (Fin.last k)))
      have hsplit : Function.Injective split := by
        intro z z' h
        have hinitC : Fin.init z.1 = Fin.init z'.1 :=
          congrArg (fun w => w.1.1) h
        have hlastC : z.1 (Fin.last k) = z'.1 (Fin.last k) :=
          congrArg (fun w => w.1.2) h
        have hinitA : Fin.init z.2 = Fin.init z'.2 :=
          congrArg (fun w => w.2.1) h
        have hlastA : z.2 (Fin.last k) = z'.2 (Fin.last k) :=
          congrArg (fun w => w.2.2) h
        apply Prod.ext
        · funext i
          refine Fin.lastCases hlastC (fun j => ?_) i
          exact congrFun hinitC j
        · funext i
          refine Fin.lastCases hlastA (fun j => ?_) i
          exact congrFun hinitA j
      let R := Q.map split
      have hfull : shannonEntropy R = shannonEntropy Q :=
        shannonEntropy_map_of_injective Q split hsplit
      let splitCond : (Fin (k + 1) → C) → ((Fin k → C) × C) :=
        fun x => (Fin.init x, x (Fin.last k))
      have hsplitCond : Function.Injective splitCond := by
        intro x x' h
        have hinit : Fin.init x = Fin.init x' := congrArg Prod.fst h
        have hlast : x (Fin.last k) = x' (Fin.last k) := congrArg Prod.snd h
        funext i
        refine Fin.lastCases hlast (fun j => ?_) i
        exact congrFun hinit j
      have hcond :
          shannonEntropy (R.map Prod.fst) =
            shannonEntropy (Q.map Prod.fst) := by
        calc
          shannonEntropy (R.map Prod.fst) =
              shannonEntropy ((Q.map Prod.fst).map splitCond) := by
            unfold R
            rw [PMF.map_comp, PMF.map_comp]
            rfl
          _ = shannonEntropy (Q.map Prod.fst) :=
            shannonEntropy_map_of_injective _ splitCond hsplitCond
      have hR : conditionalEntropy R = conditionalEntropy Q := by
        unfold conditionalEntropy
        rw [hfull, hcond]
      have hpair := conditionalEntropy_pair_le_add R
      have hprefix :
          R.map (fun z => (z.1.1, z.2.1)) =
            Q.map (fun z => (Fin.init z.1, Fin.init z.2)) := by
        unfold R
        rw [PMF.map_comp]
        rfl
      have hlast :
          R.map (fun z => (z.1.2, z.2.2)) =
            Q.map (fun z => (z.1 (Fin.last k), z.2 (Fin.last k))) := by
        unfold R
        rw [PMF.map_comp]
        rfl
      rw [hR, hprefix, hlast] at hpair
      have hpre := ih (Q.map (fun z => (Fin.init z.1, Fin.init z.2)))
      have hcoord (i : Fin k) :
          (Q.map (fun z => (Fin.init z.1, Fin.init z.2))).map
              (fun z => (z.1 i, z.2 i)) =
            Q.map (fun z => (z.1 i.castSucc, z.2 i.castSucc)) := by
        rw [PMF.map_comp]
        rfl
      simp_rw [hcoord] at hpre
      calc
        conditionalEntropy Q ≤
            conditionalEntropy
                (Q.map (fun z => (Fin.init z.1, Fin.init z.2))) +
              conditionalEntropy
                (Q.map (fun z =>
                  (z.1 (Fin.last k), z.2 (Fin.last k)))) := hpair
        _ ≤ (∑ i : Fin k,
              conditionalEntropy
                (Q.map (fun z => (z.1 i.castSucc, z.2 i.castSucc)))) +
            conditionalEntropy
              (Q.map (fun z => (z.1 (Fin.last k), z.2 (Fin.last k)))) := by
          exact add_le_add hpre le_rfl
        _ = ∑ i : Fin (k + 1),
            conditionalEntropy (Q.map (fun z => (z.1 i, z.2 i))) := by
          rw [Fin.sum_univ_castSucc]

theorem shannonEntropy_strong_subadditivity_common_snd
    {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (T : PMF (A × (B × C))) :
    shannonEntropy (T.map (fun z => (z.1, z.2.2))) +
        shannonEntropy (T.map Prod.snd) ≥
      shannonEntropy (T.map (fun z => z.2.2)) + shannonEntropy T := by
  let reorder : A × (B × C) → C × (A × B) :=
    fun z => (z.2.2, (z.1, z.2.1))
  have hreorder : Function.Injective reorder := by
    intro z z' h
    have h' := congrArg
      (fun w : C × (A × B) => (w.2.1, (w.2.2, w.1))) h
    simpa [reorder] using h'
  let R : PMF (C × (A × B)) := T.map reorder
  have hR : shannonEntropy R = shannonEntropy T := by
    exact shannonEntropy_map_of_injective T reorder hreorder
  have hRCA :
      R.map (fun z => (z.1, z.2.1)) =
        T.map (fun z => (z.2.2, z.1)) := by
    unfold R
    rw [PMF.map_comp]
    rfl
  have hRCB :
      R.map (fun z => (z.1, z.2.2)) =
        T.map (fun z => (z.2.2, z.2.1)) := by
    unfold R
    rw [PMF.map_comp]
    rfl
  have hRC : R.map Prod.fst = T.map (fun z => z.2.2) := by
    unfold R
    rw [PMF.map_comp]
    rfl
  have hswapA :
      shannonEntropy (T.map (fun z => (z.2.2, z.1))) =
        shannonEntropy (T.map (fun z => (z.1, z.2.2))) := by
    calc
      shannonEntropy (T.map (fun z => (z.2.2, z.1))) =
          shannonEntropy
            ((T.map (fun z => (z.1, z.2.2))).map Prod.swap) := by
        rw [PMF.map_comp]
        rfl
      _ = shannonEntropy (T.map (fun z => (z.1, z.2.2))) :=
        shannonEntropy_map_of_injective _ Prod.swap Prod.swap_injective
  have hswapB :
      shannonEntropy (T.map (fun z => (z.2.2, z.2.1))) =
        shannonEntropy (T.map Prod.snd) := by
    calc
      shannonEntropy (T.map (fun z => (z.2.2, z.2.1))) =
          shannonEntropy ((T.map Prod.snd).map Prod.swap) := by
        rw [PMF.map_comp]
        rfl
      _ = shannonEntropy (T.map Prod.snd) :=
        shannonEntropy_map_of_injective _ Prod.swap Prod.swap_injective
  have hssa := shannonEntropy_strong_subadditivity R
  rw [hRCA, hRCB, hRC, hR, hswapA, hswapB] at hssa
  exact hssa

theorem mutualInformationEntropy_bind_le_average_of_fst_eq
    {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (S : PMF A) (Q : A → PMF (B × C)) (P : PMF B)
    (hfst : ∀ a, (Q a).map Prod.fst = P) :
    mutualInformationEntropy (S.bind Q) ≤
      ∑ a : A, (S a).toReal * mutualInformationEntropy (Q a) := by
  let T : PMF (A × (B × C)) := induced_joint S Q
  have hT_snd : T.map Prod.snd = S.bind Q := by
    exact induced_joint_snd S Q
  have hT_AC :
      T.map (fun z => (z.1, z.2.2)) =
        induced_joint S (fun a => (Q a).map Prod.snd) := by
    exact induced_joint_map_snd S Q Prod.snd
  have hT_C :
      T.map (fun z => z.2.2) = (S.bind Q).map Prod.snd := by
    rw [← hT_snd, PMF.map_comp]
    rfl
  have hbar_fst : (S.bind Q).map Prod.fst = P := by
    rw [PMF.map_bind]
    simp only [hfst]
    simp
  have hssa := shannonEntropy_strong_subadditivity_common_snd T
  rw [hT_AC, hT_snd, hT_C, shannonEntropy_induced_joint,
    shannonEntropy_induced_joint] at hssa
  have haverage :
      (∑ a : A, (S a).toReal * mutualInformationEntropy (Q a)) =
        shannonEntropy P +
          (∑ a : A, (S a).toReal *
            shannonEntropy ((Q a).map Prod.snd)) -
          ∑ a : A, (S a).toReal * shannonEntropy (Q a) := by
    simp only [mutualInformationEntropy, hfst]
    simp_rw [mul_sub, mul_add]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.sum_mul, sum_pmf_toReal, one_mul]
  rw [haverage]
  unfold mutualInformationEntropy
  rw [hbar_fst]
  linarith

theorem mutualInformationEntropy_le_fst (Q : PMF (X × Y)) :
    mutualInformationEntropy Q ≤ shannonEntropy (Q.map Prod.fst) := by
  have h := shannonEntropy_map_le Q Prod.snd
  unfold mutualInformationEntropy
  linarith

theorem mutualInformationEntropy_le_snd (Q : PMF (X × Y)) :
    mutualInformationEntropy Q ≤ shannonEntropy (Q.map Prod.snd) := by
  have h := shannonEntropy_map_le Q Prod.fst
  unfold mutualInformationEntropy
  linarith

@[simp] theorem product_pmf_apply
    (P : PMF X) (Q : PMF Y) (x : X) (y : Y) :
    product_pmf P Q (x, y) = P x * Q y := by
  change induced_joint P (fun _ => Q) (x, y) = _
  rw [induced_joint_apply]

/-- Iterated-sum expression for a real expectation under a product PMF. -/
theorem pmfRealExpectation_product_pmf
    {A B : Type*} [Fintype A] [Fintype B]
    (P : PMF A) (Q : PMF B) (f : A × B → ℝ) :
    pmfRealExpectation (product_pmf P Q) f =
      ∑ a : A, (P a).toReal * ∑ b : B, (Q b).toReal * f (a, b) := by
  classical
  unfold pmfRealExpectation
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  simp_rw [product_pmf_apply, ENNReal.toReal_mul, mul_assoc]
  rw [← Finset.mul_sum]

/-- Expectations add for functions of independent finite-PMF variables. -/
theorem pmfRealExpectation_product_pmf_add
    {A B : Type*} [Fintype A] [Fintype B]
    (P : PMF A) (Q : PMF B) (f : A → ℝ) (g : B → ℝ) :
    pmfRealExpectation (product_pmf P Q) (fun z => f z.1 + g z.2) =
      pmfRealExpectation P f + pmfRealExpectation Q g := by
  classical
  rw [pmfRealExpectation_product_pmf]
  unfold pmfRealExpectation
  calc
    (∑ a : A, (P a).toReal * ∑ b : B, (Q b).toReal * (f a + g b)) =
        ∑ a : A, (P a).toReal *
          ((∑ b : B, (Q b).toReal) * f a +
            ∑ b : B, (Q b).toReal * g b) := by
      apply Finset.sum_congr rfl
      intro a _
      congr 1
      calc
        (∑ b : B, (Q b).toReal * (f a + g b)) =
            ∑ b : B, ((Q b).toReal * f a + (Q b).toReal * g b) := by
          apply Finset.sum_congr rfl
          intro b _
          ring
        _ = (∑ b : B, (Q b).toReal) * f a +
            ∑ b : B, (Q b).toReal * g b := by
          rw [Finset.sum_add_distrib, Finset.sum_mul]
    _ = (∑ a : A, (P a).toReal * f a) +
        (∑ a : A, (P a).toReal) * ∑ b : B, (Q b).toReal * g b := by
      rw [sum_pmf_toReal Q]
      simp only [one_mul, mul_add]
      rw [Finset.sum_add_distrib, Finset.sum_mul]
    _ = pmfRealExpectation P f + pmfRealExpectation Q g := by
      rw [sum_pmf_toReal P, one_mul]
      rfl

/-- A centered real-valued finite-PMF random variable has expectation zero. -/
theorem pmfRealExpectation_sub_self
    {A : Type*} [Fintype A] [DecidableEq A]
    (P : PMF A) (f : A → ℝ) :
    pmfRealExpectation P (fun a => f a - pmfRealExpectation P f) = 0 := by
  unfold pmfRealExpectation
  calc
    (∑ a : A, (P a).toReal * (f a - ∑ a : A, (P a).toReal * f a)) =
        (∑ a : A, (P a).toReal * f a) -
          (∑ a : A, (P a).toReal) * ∑ a : A, (P a).toReal * f a := by
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib, Finset.sum_mul]
    _ = 0 := by rw [sum_pmf_toReal P]; ring

/-- Expectations of products factor for independent finite-PMF variables. -/
theorem pmfRealExpectation_product_pmf_mul
    {A B : Type*} [Fintype A] [Fintype B]
    (P : PMF A) (Q : PMF B) (f : A → ℝ) (g : B → ℝ) :
    pmfRealExpectation (product_pmf P Q) (fun z => f z.1 * g z.2) =
      pmfRealExpectation P f * pmfRealExpectation Q g := by
  classical
  rw [pmfRealExpectation_product_pmf]
  unfold pmfRealExpectation
  calc
    (∑ a : A, (P a).toReal * ∑ b : B, (Q b).toReal * (f a * g b)) =
        ∑ a : A, (P a).toReal *
          (f a * ∑ b : B, (Q b).toReal * g b) := by
      apply Finset.sum_congr rfl
      intro a _
      congr 1
      calc
        (∑ b : B, (Q b).toReal * (f a * g b)) =
            ∑ b : B, f a * ((Q b).toReal * g b) := by
          apply Finset.sum_congr rfl
          intro b _
          ring
        _ = f a * ∑ b : B, (Q b).toReal * g b := by
          rw [Finset.mul_sum]
    _ = (∑ a : A, (P a).toReal * f a) *
        ∑ b : B, (Q b).toReal * g b := by
      calc
        (∑ a : A, (P a).toReal *
            (f a * ∑ b : B, (Q b).toReal * g b)) =
            ∑ a : A, ((P a).toReal * f a) *
              ∑ b : B, (Q b).toReal * g b := by
          apply Finset.sum_congr rfl
          intro a _
          ring
        _ = (∑ a : A, (P a).toReal * f a) *
            ∑ b : B, (Q b).toReal * g b := by
          rw [Finset.sum_mul]
    _ = pmfRealExpectation P f * pmfRealExpectation Q g := rfl

/-- Variances add for sums of independent finite-PMF random variables. -/
theorem pmfRealVariance_product_pmf_add
    {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (P : PMF A) (Q : PMF B) (f : A → ℝ) (g : B → ℝ) :
    pmfRealVariance (product_pmf P Q) (fun z => f z.1 + g z.2) =
      pmfRealVariance P f + pmfRealVariance Q g := by
  classical
  rw [pmfRealVariance_eq_expectation, pmfRealVariance_eq_expectation,
    pmfRealVariance_eq_expectation,
    pmfRealExpectation_product_pmf_add P Q f g]
  let u : A → ℝ := fun a => f a - pmfRealExpectation P f
  let v : B → ℝ := fun b => g b - pmfRealExpectation Q g
  have hcenter :
      pmfRealExpectation (product_pmf P Q)
          (fun z => (f z.1 + g z.2 -
            (pmfRealExpectation P f + pmfRealExpectation Q g)) ^ 2) =
        pmfRealExpectation (product_pmf P Q)
          (fun z => (u z.1 + v z.2) ^ 2) := by
    congr 1
    funext z
    dsimp [u, v]
    ring
  have hu0 : pmfRealExpectation P u = 0 := by
    simpa [u] using pmfRealExpectation_sub_self P f
  have hv0 : pmfRealExpectation Q v = 0 := by
    simpa [v] using pmfRealExpectation_sub_self Q g
  have hfst (h : A → ℝ) :
      pmfRealExpectation (product_pmf P Q) (fun z => h z.1) =
        pmfRealExpectation P h := by
    calc
      pmfRealExpectation (product_pmf P Q) (fun z => h z.1) =
          pmfRealExpectation (product_pmf P Q) (fun z => h z.1 + (0 : ℝ)) := by
        congr 1
        funext z
        ring
      _ = pmfRealExpectation P h + pmfRealExpectation Q (fun _ => 0) := by
        simpa using pmfRealExpectation_product_pmf_add P Q h (fun _ => 0)
      _ = pmfRealExpectation P h := by simp
  have hsnd (h : B → ℝ) :
      pmfRealExpectation (product_pmf P Q) (fun z => h z.2) =
        pmfRealExpectation Q h := by
    calc
      pmfRealExpectation (product_pmf P Q) (fun z => h z.2) =
          pmfRealExpectation (product_pmf P Q) (fun z => (0 : ℝ) + h z.2) := by
        congr 1
        funext z
        ring
      _ = pmfRealExpectation P (fun _ => 0) + pmfRealExpectation Q h := by
        simpa using pmfRealExpectation_product_pmf_add P Q (fun _ => 0) h
      _ = pmfRealExpectation Q h := by simp
  have hcross :
      pmfRealExpectation (product_pmf P Q) (fun z => u z.1 * v z.2) = 0 := by
    rw [pmfRealExpectation_product_pmf_mul, hu0, hv0]
    ring
  calc
    pmfRealExpectation (product_pmf P Q)
        (fun z => (f z.1 + g z.2 -
          (pmfRealExpectation P f + pmfRealExpectation Q g)) ^ 2) =
        pmfRealExpectation (product_pmf P Q) (fun z => (u z.1 + v z.2) ^ 2) := hcenter
    _ =
        pmfRealExpectation (product_pmf P Q)
          (fun z => u z.1 ^ 2 + (2 * (u z.1 * v z.2) + v z.2 ^ 2)) := by
      congr 1
      funext z
      ring
    _ = pmfRealExpectation (product_pmf P Q) (fun z => u z.1 ^ 2) +
        pmfRealExpectation (product_pmf P Q)
          (fun z => 2 * (u z.1 * v z.2) + v z.2 ^ 2) := by
      rw [pmfRealExpectation_add]
    _ = pmfRealExpectation (product_pmf P Q) (fun z => u z.1 ^ 2) +
        (pmfRealExpectation (product_pmf P Q) (fun z => 2 * (u z.1 * v z.2)) +
          pmfRealExpectation (product_pmf P Q) (fun z => v z.2 ^ 2)) := by
      rw [pmfRealExpectation_add]
    _ = pmfRealExpectation P (fun a => u a ^ 2) +
        (2 * pmfRealExpectation (product_pmf P Q) (fun z => u z.1 * v z.2) +
          pmfRealExpectation Q (fun b => v b ^ 2)) := by
      rw [hfst (fun a => u a ^ 2), hsnd (fun b => v b ^ 2)]
      rw [pmfRealExpectation_const_mul]
    _ = pmfRealExpectation P (fun a => u a ^ 2) +
        pmfRealExpectation Q (fun b => v b ^ 2) := by
      rw [hcross]
      ring
    _ = pmfRealExpectation P (fun a => (f a - pmfRealExpectation P f) ^ 2) +
        pmfRealExpectation Q (fun b => (g b - pmfRealExpectation Q g) ^ 2) := by
      rfl

/-- Scaling a real random variable scales its finite-PMF variance quadratically. -/
theorem pmfRealVariance_const_mul
    {A : Type*} [Fintype A] (P : PMF A) (c : ℝ) (f : A → ℝ) :
    pmfRealVariance P (fun a => c * f a) = c ^ 2 * pmfRealVariance P f := by
  unfold pmfRealVariance
  rw [pmfRealExpectation_const_mul]
  calc
    (∑ a : A, (P a).toReal *
        (c * f a - c * pmfRealExpectation P f) ^ 2) =
        ∑ a : A, c ^ 2 * ((P a).toReal *
          (f a - pmfRealExpectation P f) ^ 2) := by
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = c ^ 2 * ∑ a : A, (P a).toReal *
        (f a - pmfRealExpectation P f) ^ 2 := by
      rw [Finset.mul_sum]

theorem support_joint_subset_product_marginals
    (Q : PMF (X × Y)) :
    Q.support ⊆
      (product_pmf (Q.map Prod.fst) (Q.map Prod.snd)).support := by
  intro z hz
  rcases z with ⟨x, y⟩
  have hx : x ∈ (Q.map Prod.fst).support := by
    rw [PMF.mem_support_map_iff]
    exact ⟨(x, y), hz, rfl⟩
  have hy : y ∈ (Q.map Prod.snd).support := by
    rw [PMF.mem_support_map_iff]
    exact ⟨(x, y), hz, rfl⟩
  rw [PMF.mem_support_iff, product_pmf_apply]
  exact (ENNReal.mul_pos ((Q.map Prod.fst).apply_pos_iff x |>.mpr hx |>.ne')
    ((Q.map Prod.snd).apply_pos_iff y |>.mpr hy |>.ne')).ne'

theorem weighted_log_pmfDensityRatio_product_marginals
    (Q : PMF (X × Y)) (z : X × Y) :
    (Q z).toReal * Real.log
        (pmfDensityRatio Q
          (product_pmf (Q.map Prod.fst) (Q.map Prod.snd)) z).toReal =
      (Q z).toReal * Real.log (Q z).toReal -
        (Q z).toReal * Real.log ((Q.map Prod.fst) z.1).toReal -
        (Q z).toReal * Real.log ((Q.map Prod.snd) z.2).toReal := by
  rcases z with ⟨x, y⟩
  by_cases hq : Q (x, y) = 0
  · simp [hq]
  · have hz : (x, y) ∈ Q.support := (PMF.mem_support_iff Q (x, y)).mpr hq
    have hxmem : x ∈ (Q.map Prod.fst).support := by
      rw [PMF.mem_support_map_iff]
      exact ⟨(x, y), hz, rfl⟩
    have hymem : y ∈ (Q.map Prod.snd).support := by
      rw [PMF.mem_support_map_iff]
      exact ⟨(x, y), hz, rfl⟩
    have hx : (Q.map Prod.fst) x ≠ 0 :=
      (PMF.mem_support_iff (Q.map Prod.fst) x).mp hxmem
    have hy : (Q.map Prod.snd) y ≠ 0 :=
      (PMF.mem_support_iff (Q.map Prod.snd) y).mp hymem
    have hqr : (Q (x, y)).toReal ≠ 0 :=
      ENNReal.toReal_ne_zero.mpr ⟨hq, Q.apply_ne_top (x, y)⟩
    have hxr : ((Q.map Prod.fst) x).toReal ≠ 0 :=
      ENNReal.toReal_ne_zero.mpr ⟨hx, (Q.map Prod.fst).apply_ne_top x⟩
    have hyr : ((Q.map Prod.snd) y).toReal ≠ 0 :=
      ENNReal.toReal_ne_zero.mpr ⟨hy, (Q.map Prod.snd).apply_ne_top y⟩
    simp only [pmfDensityRatio, product_pmf_apply, ENNReal.toReal_mul,
      ENNReal.toReal_inv]
    rw [Real.log_mul hqr (inv_ne_zero (mul_ne_zero hxr hyr)),
      Real.log_inv, Real.log_mul hxr hyr]
    ring

theorem sum_weighted_log_densityRatio_product_marginals
    (Q : PMF (X × Y)) :
    (∑ z : X × Y, (Q z).toReal * Real.log
        (pmfDensityRatio Q
          (product_pmf (Q.map Prod.fst) (Q.map Prod.snd)) z).toReal) =
      mutualInformationEntropy Q := by
  have hfst :
      (∑ z : X × Y, (Q z).toReal *
          Real.log ((Q.map Prod.fst) z.1).toReal) =
        ∑ x : X, ((Q.map Prod.fst) x).toReal *
          Real.log ((Q.map Prod.fst) x).toReal := by
    exact (sum_map_mul_toReal Q Prod.fst
      (fun x => Real.log ((Q.map Prod.fst) x).toReal)).symm
  have hsnd :
      (∑ z : X × Y, (Q z).toReal *
          Real.log ((Q.map Prod.snd) z.2).toReal) =
        ∑ y : Y, ((Q.map Prod.snd) y).toReal *
          Real.log ((Q.map Prod.snd) y).toReal := by
    exact (sum_map_mul_toReal Q Prod.snd
      (fun y => Real.log ((Q.map Prod.snd) y).toReal)).symm
  calc
    (∑ z : X × Y, (Q z).toReal * Real.log
        (pmfDensityRatio Q
          (product_pmf (Q.map Prod.fst) (Q.map Prod.snd)) z).toReal) =
        ∑ z : X × Y,
          ((Q z).toReal * Real.log (Q z).toReal -
            (Q z).toReal * Real.log ((Q.map Prod.fst) z.1).toReal -
            (Q z).toReal * Real.log ((Q.map Prod.snd) z.2).toReal) := by
      apply Finset.sum_congr rfl
      intro z _
      exact weighted_log_pmfDensityRatio_product_marginals Q z
    _ = -shannonEntropy Q -
        (-shannonEntropy (Q.map Prod.fst)) -
        (-shannonEntropy (Q.map Prod.snd)) := by
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hfst, hsnd,
        sum_mul_log_eq_neg_shannonEntropy,
        sum_mul_log_eq_neg_shannonEntropy,
        sum_mul_log_eq_neg_shannonEntropy]
    _ = mutualInformationEntropy Q := by
      unfold mutualInformationEntropy
      ring

theorem mutual_information_eq_ofReal_entropy (Q : PMF (X × Y)) :
    mutual_information Q = ENNReal.ofReal (mutualInformationEntropy Q) := by
  unfold mutual_information
  rw [kl_divergence_eq_ofReal_sum _ _
    (support_joint_subset_product_marginals Q)]
  rw [sum_weighted_log_densityRatio_product_marginals]

theorem joint_absolutelyContinuous_product_marginals
    (Q : PMF (X × Y)) :
    letI : MeasurableSpace (X × Y) := ⊤
    Q.toMeasure ≪
      (product_pmf (Q.map Prod.fst) (Q.map Prod.snd)).toMeasure := by
  letI : MeasurableSpace (X × Y) := ⊤
  exact pmf_toMeasure_absolutelyContinuous_of_support_subset Q
    (product_pmf (Q.map Prod.fst) (Q.map Prod.snd))
    (support_joint_subset_product_marginals Q)

noncomputable def jointExpectedDistortion
    (Q : PMF (X × Y)) (d : Distortion (X := X) (Y := Y)) : ENNReal :=
  ∑ x : X, ∑ y : Y, Q (x, y) * (d x y : ENNReal)

/-- The real expectation of finite distortion is the `toReal` of the existing
extended-nonnegative expected-distortion definition. -/
theorem pmfRealExpectation_pairDistortion_eq_toReal_jointExpectedDistortion
    (Q : PMF (X × Y)) (d : Distortion (X := X) (Y := Y)) :
    pmfRealExpectation Q (fun z => (d z.1 z.2 : ℝ)) =
      (jointExpectedDistortion Q d).toReal := by
  unfold pmfRealExpectation jointExpectedDistortion
  rw [Fintype.sum_prod_type]
  symm
  rw [ENNReal.toReal_sum (fun x _ =>
    ENNReal.sum_ne_top.mpr fun y _ =>
      ENNReal.mul_ne_top (Q.apply_ne_top (x, y)) ENNReal.coe_ne_top)]
  apply Finset.sum_congr rfl
  intro x _
  rw [ENNReal.toReal_sum (fun y _ =>
    ENNReal.mul_ne_top (Q.apply_ne_top (x, y)) ENNReal.coe_ne_top)]
  apply Finset.sum_congr rfl
  intro y _
  rw [ENNReal.toReal_mul]
  simp

@[simp] theorem jointExpectedDistortion_induced
    (P : PMF X) (W : X → PMF Y)
    (d : Distortion (X := X) (Y := Y)) :
    jointExpectedDistortion (induced_joint P W) d =
      expected_distortion_single P W d := by
  simp only [jointExpectedDistortion, expected_distortion_single, induced_joint_apply]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.mul_sum]
  simp [mul_assoc]

theorem pmfRealExpectation_inducedJoint_distortion
    (P : PMF X) (W : X → PMF Y) (d : Distortion (X := X) (Y := Y)) :
    pmfRealExpectation (induced_joint P W) (fun z => (d z.1 z.2 : ℝ)) =
      (expected_distortion_single P W d).toReal := by
  rw [pmfRealExpectation_pairDistortion_eq_toReal_jointExpectedDistortion,
    jointExpectedDistortion_induced]


/--
  definition of rate distortion function
-/
noncomputable def RateDistortionFunction
    (P : PMF X) (d : Distortion (X := X) (Y := Y)) (D : ENNReal) : ENNReal :=
--using sInf denote
  sInf { r : ENNReal | ∃ (W : X → PMF Y),
            expected_distortion_single P W d ≤ D ∧
            mutual_information (induced_joint P W)  = r }

theorem RateDistortionFunction_le
    (P : PMF X) (d : Distortion (X := X) (Y := Y)) (D : ENNReal)
    (W : X → PMF Y) (hW : expected_distortion_single P W d ≤ D) :
    RateDistortionFunction P d D ≤ mutual_information (induced_joint P W) := by
  apply sInf_le
  exact ⟨W, hW, rfl⟩

theorem exists_testChannel_of_RateDistortionFunction_lt
    (P : PMF X) (d : Distortion (X := X) (Y := Y))
    (D R : ENNReal)
    (hR : RateDistortionFunction P d D < R) :
    ∃ W : X → PMF Y,
      expected_distortion_single P W d ≤ D ∧
        mutual_information (induced_joint P W) < R := by
  unfold RateDistortionFunction at hR
  rcases sInf_lt_iff.mp hR with ⟨r, ⟨W, hW, hr⟩, hrR⟩
  rw [← hr] at hrR
  exact ⟨W, hW, hrR⟩

theorem exists_testChannel_of_RateDistortionFunction_lt_ofReal
    (P : PMF X) (d : Distortion (X := X) (Y := Y))
    (D : ENNReal) (R : ℝ)
    (hR : RateDistortionFunction P d D < ENNReal.ofReal R) :
    ∃ W : X → PMF Y,
      expected_distortion_single P W d ≤ D ∧
        mutualInformationEntropy (induced_joint P W) < R := by
  obtain ⟨W, hW, hI⟩ :=
    exists_testChannel_of_RateDistortionFunction_lt
      P d D (ENNReal.ofReal R) hR
  rw [mutual_information_eq_ofReal_entropy] at hI
  have hIreal := ENNReal.toReal_lt_of_lt_ofReal hI
  rw [ENNReal.toReal_ofReal
    (mutualInformationEntropy_nonneg (induced_joint P W))] at hIreal
  exact ⟨W, hW, hIreal⟩

theorem RateDistortionFunction_le_of_joint
    (P : PMF X) (d : Distortion (X := X) (Y := Y)) (D : ENNReal)
    (Q : PMF (X × Y)) (hQ : Q.map Prod.fst = P)
    (hD : jointExpectedDistortion Q d ≤ D) :
    RateDistortionFunction P d D ≤ mutual_information Q := by
  subst P
  have hdist :
      expected_distortion_single (Q.map Prod.fst) (conditionalPMF Q) d ≤ D := by
    rw [← jointExpectedDistortion_induced, induced_joint_conditionalPMF]
    exact hD
  simpa only [induced_joint_conditionalPMF] using
    RateDistortionFunction_le (Q.map Prod.fst) d D (conditionalPMF Q) hdist

theorem RateDistortionFunction_antitone
    (P : PMF X) (d : Distortion (X := X) (Y := Y))
    {D₁ D₂ : ENNReal} (hD : D₁ ≤ D₂) :
    RateDistortionFunction P d D₂ ≤ RateDistortionFunction P d D₁ := by
  apply sInf_le_sInf
  rintro r ⟨W, hW, hr⟩
  exact ⟨W, hW.trans hD, hr⟩

def feasibleDistortion
    (P : PMF X)
    (d : Distortion (X := X) (Y := Y))
    (D : ENNReal) : Prop :=
  ∃ W : X → PMF Y, expected_distortion_single P W d ≤ D

theorem feasibleDistortion_mono
    (P : PMF X) (d : Distortion (X := X) (Y := Y))
    {D₁ D₂ : ENNReal} (hD : D₁ ≤ D₂) :
    feasibleDistortion P d D₁ → feasibleDistortion P d D₂ := by
  rintro ⟨W, hW⟩
  exact ⟨W, hW.trans hD⟩

/-
  The two operational distortion thresholds used in the rate-distortion
  theory.  We use `sInf` rather than a finite `min` here; this keeps the
  definitions meaningful without adding a separate `Nonempty Y` assumption.
-/
noncomputable def minimumDistortion
    (P : PMF X) (d : Distortion (X := X) (Y := Y)) : ENNReal :=
  sInf (Set.range (fun W : X → PMF Y =>
    expected_distortion_single P W d))

noncomputable def zeroRateDistortion
    (P : PMF X) (d : Distortion (X := X) (Y := Y)) : ENNReal :=
  sInf (Set.range (fun Q : PMF Y =>
    expected_distortion_single P (fun _ ↦ Q) d))

def interiorDistortion
    (P : PMF X) (d : Distortion (X := X) (Y := Y)) (D : ENNReal) : Prop :=
  minimumDistortion P d < D ∧ D < zeroRateDistortion P d

noncomputable def pmfMix
    (a b : ENNReal) (hab : a + b = 1) (P Q : PMF Y) : PMF Y :=
  PMF.ofFintype (fun y ↦ a * P y + b * Q y) (by
    calc
      ∑ y, (a * P y + b * Q y) =
          a * (∑ y, P y) + b * (∑ y, Q y) := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ = a + b := by rw [sum_pmf P, sum_pmf Q, mul_one, mul_one]
      _ = 1 := hab)

@[simp] theorem pmfMix_apply
    (a b : ENNReal) (hab : a + b = 1) (P Q : PMF Y) (y : Y) :
    pmfMix a b hab P Q y = a * P y + b * Q y := by
  rfl

def channelMix
    (a b : ENNReal) (hab : a + b = 1)
    (W₁ W₂ : X → PMF Y) : X → PMF Y :=
  fun x ↦ pmfMix a b hab (W₁ x) (W₂ x)

@[simp] theorem channelMix_apply
    (a b : ENNReal) (hab : a + b = 1)
    (W₁ W₂ : X → PMF Y) (x : X) :
    channelMix a b hab W₁ W₂ x = pmfMix a b hab (W₁ x) (W₂ x) := rfl

theorem expected_distortion_single_channelMix
    (P : PMF X) (d : Distortion (X := X) (Y := Y))
    (a b : ENNReal) (hab : a + b = 1)
    (W₁ W₂ : X → PMF Y) :
    expected_distortion_single P (channelMix a b hab W₁ W₂) d =
      a * expected_distortion_single P W₁ d +
        b * expected_distortion_single P W₂ d := by
  unfold expected_distortion_single channelMix
  simp only [pmfMix_apply]
  calc
    (∑ x, P x * ∑ y, (a * W₁ x y + b * W₂ x y) * (d x y : ENNReal)) =
        ∑ x, (a * (P x * ∑ y, W₁ x y * (d x y : ENNReal)) +
          b * (P x * ∑ y, W₂ x y * (d x y : ENNReal))) := by
      apply Finset.sum_congr rfl
      intro x _
      calc
        P x * ∑ y, (a * W₁ x y + b * W₂ x y) * (d x y : ENNReal) =
            P x * (a * ∑ y, W₁ x y * (d x y : ENNReal) +
              b * ∑ y, W₂ x y * (d x y : ENNReal)) := by
            congr 1
            calc
              ∑ y, (a * W₁ x y + b * W₂ x y) * (d x y : ENNReal) =
                  ∑ y, (a * (W₁ x y * (d x y : ENNReal)) +
                    b * (W₂ x y * (d x y : ENNReal))) := by
                apply Finset.sum_congr rfl
                intro y _
                ring
              _ = a * ∑ y, W₁ x y * (d x y : ENNReal) +
                    b * ∑ y, W₂ x y * (d x y : ENNReal) := by
                rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        _ = a * (P x * ∑ y, W₁ x y * (d x y : ENNReal)) +
              b * (P x * ∑ y, W₂ x y * (d x y : ENNReal)) := by
                ring
    _ = a * (∑ x, P x * ∑ y, W₁ x y * (d x y : ENNReal)) +
          b * (∑ x, P x * ∑ y, W₂ x y * (d x y : ENNReal)) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

@[simp] theorem induced_joint_channelMix
    (P : PMF X) (a b : ENNReal) (hab : a + b = 1)
    (W₁ W₂ : X → PMF Y) :
    induced_joint P (channelMix a b hab W₁ W₂) =
      pmfMix a b hab (induced_joint P W₁) (induced_joint P W₂) := by
  ext z
  obtain ⟨x, y⟩ := z
  simp only [induced_joint_apply, channelMix_apply, pmfMix_apply]
  ring

@[simp] theorem bind_channelMix
    (P : PMF X) (a b : ENNReal) (hab : a + b = 1)
    (W₁ W₂ : X → PMF Y) :
    P.bind (channelMix a b hab W₁ W₂) =
      pmfMix a b hab (P.bind W₁) (P.bind W₂) := by
  ext y
  simp only [PMF.bind_apply, tsum_fintype, channelMix_apply, pmfMix_apply]
  calc
    (∑ x, P x * (a * W₁ x y + b * W₂ x y)) =
        ∑ x, (a * (P x * W₁ x y) + b * (P x * W₂ x y)) := by
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = a * (∑ x, P x * W₁ x y) + b * (∑ x, P x * W₂ x y) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

noncomputable def binarySelector
    (a b : ENNReal) (hab : a + b = 1) : PMF Bool :=
  PMF.ofFintype (fun i ↦ if i then b else a) (by
    rw [Fintype.sum_bool]
    simpa [add_comm] using hab)

@[simp] theorem binarySelector_false
    (a b : ENNReal) (hab : a + b = 1) :
    binarySelector a b hab false = a := rfl

@[simp] theorem binarySelector_true
    (a b : ENNReal) (hab : a + b = 1) :
    binarySelector a b hab true = b := rfl

theorem binarySelector_bind
    {Z : Type*} [Fintype Z] [DecidableEq Z]
    (a b : ENNReal) (hab : a + b = 1) (Q₀ Q₁ : PMF Z) :
    (binarySelector a b hab).bind (fun i ↦ if i then Q₁ else Q₀) =
      pmfMix a b hab Q₀ Q₁ := by
  ext z
  simp only [PMF.bind_apply, tsum_fintype, pmfMix_apply]
  rw [Fintype.sum_bool]
  simp [add_comm]

theorem mutualInformationEntropy_channelMix_le
    (P : PMF X) (a b : ENNReal) (hab : a + b = 1)
    (W₁ W₂ : X → PMF Y) :
    mutualInformationEntropy (induced_joint P (channelMix a b hab W₁ W₂)) ≤
      a.toReal * mutualInformationEntropy (induced_joint P W₁) +
        b.toReal * mutualInformationEntropy (induced_joint P W₂) := by
  let S : PMF Bool := binarySelector a b hab
  let Q : Bool → PMF (X × Y) := fun i ↦
    if i then induced_joint P W₂ else induced_joint P W₁
  have hfst : ∀ i, (Q i).map Prod.fst = P := by
    intro i
    cases i <;> simp [Q]
  have h := mutualInformationEntropy_bind_le_average_of_fst_eq S Q P hfst
  have hbind : S.bind Q = induced_joint P (channelMix a b hab W₁ W₂) := by
    calc
      S.bind Q = pmfMix a b hab (induced_joint P W₁) (induced_joint P W₂) := by
        simpa [S, Q] using binarySelector_bind a b hab
          (induced_joint P W₁) (induced_joint P W₂)
      _ = induced_joint P (channelMix a b hab W₁ W₂) :=
        (induced_joint_channelMix P a b hab W₁ W₂).symm
  rw [hbind] at h
  simpa [S, Q, Fintype.sum_bool, add_comm] using h

theorem mutual_information_channelMix_le
    (P : PMF X) (a b : ENNReal) (hab : a + b = 1)
    (W₁ W₂ : X → PMF Y) :
    mutual_information (induced_joint P (channelMix a b hab W₁ W₂)) ≤
      a * mutual_information (induced_joint P W₁) +
        b * mutual_information (induced_joint P W₂) := by
  rw [mutual_information_eq_ofReal_entropy,
    mutual_information_eq_ofReal_entropy,
    mutual_information_eq_ofReal_entropy]
  have ha : a ≠ ⊤ := by
    intro h
    simp [h] at hab
  have hb : b ≠ ⊤ := by
    intro h
    simp [h] at hab
  have hI1 := mutualInformationEntropy_nonneg (induced_joint P W₁)
  have hI2 := mutualInformationEntropy_nonneg (induced_joint P W₂)
  calc
    ENNReal.ofReal
        (mutualInformationEntropy (induced_joint P (channelMix a b hab W₁ W₂))) ≤
        ENNReal.ofReal
          (a.toReal * mutualInformationEntropy (induced_joint P W₁) +
            b.toReal * mutualInformationEntropy (induced_joint P W₂)) := by
      exact ENNReal.ofReal_mono
        (mutualInformationEntropy_channelMix_le P a b hab W₁ W₂)
    _ = a * ENNReal.ofReal (mutualInformationEntropy (induced_joint P W₁)) +
          b * ENNReal.ofReal (mutualInformationEntropy (induced_joint P W₂)) := by
      rw [ENNReal.ofReal_add
        (mul_nonneg ENNReal.toReal_nonneg hI1)
        (mul_nonneg ENNReal.toReal_nonneg hI2)]
      rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg,
        ENNReal.ofReal_mul ENNReal.toReal_nonneg,
        ENNReal.ofReal_toReal ha,
        ENNReal.ofReal_toReal hb]

theorem RateDistortionFunction_le_channelMix
    (P : PMF X) (d : Distortion (X := X) (Y := Y))
    (a b : ENNReal) (hab : a + b = 1)
    (D₁ D₂ : ENNReal) (W₁ W₂ : X → PMF Y)
    (hW₁ : expected_distortion_single P W₁ d ≤ D₁)
    (hW₂ : expected_distortion_single P W₂ d ≤ D₂) :
    RateDistortionFunction P d (a * D₁ + b * D₂) ≤
      a * mutual_information (induced_joint P W₁) +
        b * mutual_information (induced_joint P W₂) := by
  apply le_trans
    (RateDistortionFunction_le P d (a * D₁ + b * D₂)
      (channelMix a b hab W₁ W₂) ?_)
    (mutual_information_channelMix_le P a b hab W₁ W₂)
  rw [expected_distortion_single_channelMix]
  exact add_le_add (mul_le_mul_right hW₁ a) (mul_le_mul_right hW₂ b)

theorem RateDistortionFunction_ne_top_of_feasible
    (P : PMF X) (d : Distortion (X := X) (Y := Y)) (D : ENNReal)
    (W : X → PMF Y)
    (hW : expected_distortion_single P W d ≤ D) :
    RateDistortionFunction P d D ≠ ⊤ := by
  have hMI : mutual_information (induced_joint P W) ≠ ⊤ := by
    rw [mutual_information_eq_ofReal_entropy]
    exact ENNReal.ofReal_ne_top
  exact ne_top_of_le_ne_top hMI
    (RateDistortionFunction_le P d D W hW)

theorem RateDistortionFunction_convex_of_feasible
    (P : PMF X) (d : Distortion (X := X) (Y := Y))
    (a b : ENNReal) (hab : a + b = 1)
    (D₁ D₂ : ENNReal)
    (hD₁ : feasibleDistortion P d D₁)
    (hD₂ : feasibleDistortion P d D₂) :
    RateDistortionFunction P d (a * D₁ + b * D₂) ≤
      a * RateDistortionFunction P d D₁ +
        b * RateDistortionFunction P d D₂ := by
  let C₁ := {W : X → PMF Y // expected_distortion_single P W d ≤ D₁}
  let C₂ := {W : X → PMF Y // expected_distortion_single P W d ≤ D₂}
  let I₁ : C₁ → ENNReal := fun W ↦ mutual_information (induced_joint P W.1)
  let I₂ : C₂ → ENNReal := fun W ↦ mutual_information (induced_joint P W.1)
  have hC₁ : Nonempty C₁ := by
    obtain ⟨W, hW⟩ := hD₁
    exact ⟨⟨W, hW⟩⟩
  have hC₂ : Nonempty C₂ := by
    obtain ⟨W, hW⟩ := hD₂
    exact ⟨⟨W, hW⟩⟩
  letI : Nonempty C₁ := hC₁
  letI : Nonempty C₂ := hC₂
  have hset₁ :
      {r : ENNReal | ∃ W : X → PMF Y,
        expected_distortion_single P W d ≤ D₁ ∧
          mutual_information (induced_joint P W) = r} = Set.range I₁ := by
    ext r
    constructor
    · rintro ⟨W, hW, rfl⟩
      exact ⟨⟨W, hW⟩, rfl⟩
    · rintro ⟨W, rfl⟩
      exact ⟨W.1, W.2, rfl⟩
  have hset₂ :
      {r : ENNReal | ∃ W : X → PMF Y,
        expected_distortion_single P W d ≤ D₂ ∧
          mutual_information (induced_joint P W) = r} = Set.range I₂ := by
    ext r
    constructor
    · rintro ⟨W, hW, rfl⟩
      exact ⟨⟨W, hW⟩, rfl⟩
    · rintro ⟨W, rfl⟩
      exact ⟨W.1, W.2, rfl⟩
  have hRDF₁ : RateDistortionFunction P d D₁ = ⨅ W : C₁, I₁ W := by
    unfold RateDistortionFunction
    rw [hset₁, sInf_range]
  have hRDF₂ : RateDistortionFunction P d D₂ = ⨅ W : C₂, I₂ W := by
    unfold RateDistortionFunction
    rw [hset₂, sInf_range]
  have ha : a ≠ ⊤ := by
    intro h
    simp [h] at hab
  have hb : b ≠ ⊤ := by
    intro h
    simp [h] at hab
  have hmul₁ :
      a * (⨅ W : C₁, I₁ W) = ⨅ W : C₁, a * I₁ W := by
    exact ENNReal.mul_iInf (by
      intro ha_top _
      exact (ha ha_top).elim)
  have hmul₂ :
      b * (⨅ W : C₂, I₂ W) = ⨅ W : C₂, b * I₂ W := by
    exact ENNReal.mul_iInf (by
      intro hb_top _
      exact (hb hb_top).elim)
  have hpair : ∀ W₁ : C₁, ∀ W₂ : C₂,
      RateDistortionFunction P d (a * D₁ + b * D₂) ≤
        a * I₁ W₁ + b * I₂ W₂ := by
    intro W₁ W₂
    exact RateDistortionFunction_le_channelMix P d a b hab D₁ D₂
      W₁.1 W₂.1 W₁.2 W₂.2
  calc
    RateDistortionFunction P d (a * D₁ + b * D₂) ≤
        (⨅ W₁ : C₁, a * I₁ W₁) + (⨅ W₂ : C₂, b * I₂ W₂) :=
      ENNReal.le_iInf_add_iInf hpair
    _ = a * RateDistortionFunction P d D₁ +
          b * RateDistortionFunction P d D₂ := by
      rw [← hmul₁, ← hmul₂, ← hRDF₁, ← hRDF₂]

theorem RateDistortionFunction_tsub_le_of_convex
    (P : PMF X) (d : Distortion (X := X) (Y := Y))
    (a b : ENNReal) (hab : a + b = 1)
    (D₁ D₂ : ENNReal)
    (hD₁ : feasibleDistortion P d D₁)
    (hD₂ : feasibleDistortion P d D₂)
    (hb : b ≤ 1) :
    RateDistortionFunction P d (a * D₁ + b * D₂) -
        a * RateDistortionFunction P d D₁ ≤
      RateDistortionFunction P d D₂ := by
  have hconv := RateDistortionFunction_convex_of_feasible P d a b hab D₁ D₂ hD₁ hD₂
  rw [tsub_le_iff_right]
  calc
    RateDistortionFunction P d (a * D₁ + b * D₂) ≤
        a * RateDistortionFunction P d D₁ +
          b * RateDistortionFunction P d D₂ := hconv
    _ = b * RateDistortionFunction P d D₂ +
          a * RateDistortionFunction P d D₁ := by rw [add_comm]
    _ ≤ 1 * RateDistortionFunction P d D₂ +
          a * RateDistortionFunction P d D₁ := by
      gcongr
    _ = RateDistortionFunction P d D₂ +
          a * RateDistortionFunction P d D₁ := by rw [one_mul]

theorem ennreal_barycentric_weights
    (D₀ D ε : ENNReal) (hD₀ : D₀ < D) (hDtop : D ≠ ⊤)
    (hεtop : ε ≠ ⊤) :
    let c := D - D₀
    let a := ε / (c + ε)
    let b := c / (c + ε)
    a + b = 1 ∧ a * D₀ + b * (D + ε) = D ∧ b ≤ 1 := by
  dsimp only
  let c := D - D₀
  have hcpos : 0 < c := tsub_pos_iff_lt.mpr hD₀
  have hc0 : c ≠ 0 := hcpos.ne'
  have hctop : c ≠ ⊤ :=
    ne_top_of_le_ne_top hDtop (tsub_le_self : D - D₀ ≤ D)
  have hd0 : c + ε ≠ 0 := (hcpos.trans_le (le_add_right le_rfl)).ne'
  have hdtop : c + ε ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨hctop, hεtop⟩
  have hcD : c + D₀ = D := tsub_add_cancel_of_le hD₀.le
  have hD₀c : D₀ + c = D := by simpa [add_comm] using hcD
  constructor
  · rw [ENNReal.div_add_div_same, add_comm ε c,
      ENNReal.div_self hd0 hdtop]
  constructor
  · rw [div_eq_mul_inv, div_eq_mul_inv]
    calc
      (ε * (c + ε)⁻¹) * D₀ +
          (c * (c + ε)⁻¹) * (D + ε) =
          (ε * D₀ + c * (D + ε)) * (c + ε)⁻¹ := by ring
      _ = (D * (c + ε)) * (c + ε)⁻¹ := by
        congr 1
        calc
          ε * D₀ + c * (D + ε) = ε * (D₀ + c) + c * D := by ring
          _ = ε * D + c * D := by rw [hD₀c]
          _ = D * (c + ε) := by ring
      _ = D * ((c + ε) * (c + ε)⁻¹) := by rw [mul_assoc]
      _ = D := by rw [ENNReal.mul_inv_cancel hd0 hdtop, mul_one]
  · calc
      c / (c + ε) ≤ (c + ε) / (c + ε) :=
        ENNReal.div_le_div_right (le_add_right le_rfl) (c + ε)
      _ = 1 := ENNReal.div_self hd0 hdtop

theorem ennreal_barycentric_leftWeight_tendsto_zero
    (c : ENNReal) (hc0 : c ≠ 0) (hctop : c ≠ ⊤) :
    Tendsto (fun ε : ENNReal ↦ ε / (c + ε))
      (nhdsWithin (0 : ENNReal) (Set.Ioi 0)) (𝓝 0) := by
  have hnum : Tendsto (fun ε : ENNReal ↦ ε)
      (nhdsWithin (0 : ENNReal) (Set.Ioi 0)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hden : Tendsto (fun ε : ENNReal ↦ c + ε)
      (nhdsWithin (0 : ENNReal) (Set.Ioi 0)) (𝓝 c) :=
    by simpa using (tendsto_const_nhds.add hnum)
  simpa using ENNReal.Tendsto.div hnum (Or.inr hc0) hden (Or.inl hctop)

theorem ennreal_tsub_barycentric_tendsto
    (A B c : ENNReal) (hAtop : A ≠ ⊤) (hBtop : B ≠ ⊤)
    (hc0 : c ≠ 0) (hctop : c ≠ ⊤) :
    Tendsto
      (fun ε : ENNReal ↦ A - (ε / (c + ε)) * B)
      (nhdsWithin (0 : ENNReal) (Set.Ioi 0)) (𝓝 A) := by
  have hweight := ennreal_barycentric_leftWeight_tendsto_zero c hc0 hctop
  have hmul : Tendsto
      (fun ε : ENNReal ↦ (ε / (c + ε)) * B)
      (nhdsWithin (0 : ENNReal) (Set.Ioi 0)) (𝓝 0) := by
    simpa using ENNReal.Tendsto.mul_const hweight (Or.inr hBtop)
  simpa using (ENNReal.continuous_sub_left hAtop).tendsto 0 |>.comp hmul

theorem mutual_information_induced_joint_const
    (P : PMF X) (Q : PMF Y) :
    mutual_information (induced_joint P (fun _ ↦ Q)) = 0 := by
  rw [mutual_information_eq_ofReal_entropy]
  unfold mutualInformationEntropy
  rw [induced_joint_fst, induced_joint_snd]
  have hbind : P.bind (fun _ ↦ Q) = Q := by
    ext y
    rw [PMF.bind_apply, tsum_fintype]
    rw [← Finset.sum_mul, sum_pmf, one_mul]
  have hind : induced_joint P (fun _ ↦ Q) = product_pmf P Q := rfl
  rw [hbind, hind]
  rw [shannonEntropy_product_pmf]
  simp

theorem minimumDistortion_le_of_feasibleDistortion
    (P : PMF X) (d : Distortion (X := X) (Y := Y)) (D : ENNReal)
    (hD : feasibleDistortion P d D) :
    minimumDistortion P d ≤ D := by
  obtain ⟨W, hW⟩ := hD
  unfold minimumDistortion
  apply (sInf_le (show expected_distortion_single P W d ∈
    Set.range (fun W : X → PMF Y => expected_distortion_single P W d) from
      ⟨W, rfl⟩)).trans hW

theorem feasibleDistortion_of_minimumDistortion_lt
    (P : PMF X) (d : Distortion (X := X) (Y := Y)) (D : ENNReal)
    (hD : minimumDistortion P d < D) :
    feasibleDistortion P d D := by
  unfold minimumDistortion at hD
  rcases (sInf_lt_iff.mp hD) with ⟨r, ⟨W, rfl⟩, hr⟩
  exact ⟨W, le_of_lt hr⟩

theorem interiorDistortion_feasible
    (P : PMF X) (d : Distortion (X := X) (Y := Y)) (D : ENNReal)
    (hD : interiorDistortion P d D) :
    feasibleDistortion P d D :=
  feasibleDistortion_of_minimumDistortion_lt P d D hD.1

theorem RateDistortionFunction_ne_top_of_interior
    (P : PMF X) (d : Distortion (X := X) (Y := Y)) (D : ENNReal)
    (hD : interiorDistortion P d D) :
    RateDistortionFunction P d D ≠ ⊤ := by
  obtain ⟨W, hW⟩ := interiorDistortion_feasible P d D hD
  exact RateDistortionFunction_ne_top_of_feasible P d D W hW

theorem RateDistortionFunction_eq_zero_of_zeroRateDistortion_lt
    (P : PMF X) (d : Distortion (X := X) (Y := Y)) (D : ENNReal)
    (hD : zeroRateDistortion P d < D) :
    RateDistortionFunction P d D = 0 := by
  unfold zeroRateDistortion at hD
  rcases (sInf_lt_iff.mp hD) with ⟨r, ⟨Q, rfl⟩, hr⟩
  have hdist : expected_distortion_single P (fun _ ↦ Q) d ≤ D := le_of_lt hr
  apply le_antisymm
  · calc
      RateDistortionFunction P d D ≤
          mutual_information (induced_joint P (fun _ ↦ Q)) :=
        RateDistortionFunction_le P d D (fun _ ↦ Q) hdist
      _ = 0 := mutual_information_induced_joint_const P Q
  · exact bot_le

-- The probability of a block under the i.i.d. source induced by `P`.
noncomputable def probBlock (P : PMF X) (x : Xblock n X) : ENNReal :=
  ∏ i : Fin n, P (x i)

theorem sum_probBlock_fiber
    (P : PMF X) (i : Fin n) (a : X) :
    (∑ x : Xblock n X with x i = a, probBlock n P x) = P a := by
  classical
  let s : Fin n → Finset X := Function.update (fun _ => Finset.univ) i {a}
  calc
    (∑ x : Xblock n X with x i = a, probBlock n P x) =
        ∑ x ∈ Fintype.piFinset s, ∏ j, P (x j) := by
      rw [show Fintype.piFinset s =
          {x ∈ Fintype.piFinset (fun _ : Fin n => (Finset.univ : Finset X)) |
            x i = a} by
        exact Fintype.piFinset_update_singleton_eq_filter_piFinset_eq
          (fun _ : Fin n => (Finset.univ : Finset X)) i (Finset.mem_univ a)]
      simp [probBlock]
    _ = ∏ j, ∑ b ∈ s j, P b := by
      rw [← Finset.prod_univ_sum]
    _ = P a := by
      have hs : (fun j => ∑ b ∈ s j, P b) =
          Function.update (fun _ : Fin n => (1 : ENNReal)) i (P a) := by
        funext j
        by_cases hji : j = i
        · subst j
          simp [s]
        · simp [s, hji, sum_pmf]
      rw [hs]
      change (∏ j ∈ (Finset.univ : Finset (Fin n)),
        Function.update (fun _ : Fin n => (1 : ENNReal)) i (P a) j) = P a
      rw [Finset.prod_update_of_mem (Finset.mem_univ i)]
      simp

-- The finite IID block source. Its point mass is `probBlock`.
noncomputable def iidBlockPMF (P : PMF X) : PMF (Xblock n X) :=
  PMF.ofFintype (probBlock n P) (by
    classical
    simp only [probBlock]
    rw [← Fintype.piFinset_univ]
    rw [Finset.sum_prod_piFinset]
    simp [sum_pmf])

@[simp] theorem iidBlockPMF_apply
    (P : PMF X) (x : Xblock n X) :
    iidBlockPMF n P x = probBlock n P x := rfl

@[simp] theorem iidBlockPMF_coordinate
    (P : PMF X) (i : Fin n) :
    (iidBlockPMF n P).map (fun x => x i) = P := by
  ext a
  simp only [PMF.map_apply, tsum_fintype, iidBlockPMF_apply]
  simpa [Finset.sum_filter, eq_comm] using sum_probBlock_fiber n P i a

/-- Each coordinate of a finite IID block has the single-letter expectation. -/
theorem pmfRealExpectation_iidBlockPMF_coordinate
    (P : PMF X) (i : Fin n) (f : X → ℝ) :
    pmfRealExpectation (iidBlockPMF n P) (fun x => f (x i)) =
      pmfRealExpectation P f := by
  calc
    pmfRealExpectation (iidBlockPMF n P) (fun x => f (x i)) =
        pmfRealExpectation ((iidBlockPMF n P).map (fun x => x i)) f := by
      symm
      simpa [Function.comp_def] using
        (pmfRealExpectation_map (iidBlockPMF n P) (fun x => x i) f)
    _ = pmfRealExpectation P f := by rw [iidBlockPMF_coordinate]

/-- The real-valued sum of a function along a finite source block. -/
def blockRealSum (f : X → ℝ) (x : Xblock n X) : ℝ :=
  ∑ i : Fin n, f (x i)

/-- The average of a real-valued function along a positive-length block. -/
def blockRealAverage (hn : 0 < n) (f : X → ℝ) (x : Xblock n X) : ℝ :=
  blockRealSum n f x / n

@[simp] theorem blockRealSum_zero
    (f : X → ℝ) (x : Xblock 0 X) :
    blockRealSum 0 f x = 0 := by
  simp [blockRealSum]

theorem blockRealSum_succ
    (k : ℕ) (f : X → ℝ) (x : Xblock (k + 1) X) :
    blockRealSum (k + 1) f x =
      blockRealSum k f (Fin.init x) + f (x (Fin.last k)) := by
  unfold blockRealSum
  rw [Fin.sum_univ_castSucc]
  rfl

noncomputable def memorylessChannelBlockPMF
    (W : X → PMF Y) (x : Xblock n X) : PMF (Yblock n Y) :=
  PMF.ofFintype (fun y ↦ ∏ i : Fin n, W (x i) (y i)) (by
    classical
    rw [← Fintype.piFinset_univ]
    rw [Finset.sum_prod_piFinset]
    simp [sum_pmf])

@[simp] theorem memorylessChannelBlockPMF_apply
    (W : X → PMF Y) (x : Xblock n X) (y : Yblock n Y) :
    memorylessChannelBlockPMF n W x y =
      ∏ i : Fin n, W (x i) (y i) := rfl

def blockPairEquiv :
    (Xblock n X × Yblock n Y) ≃ (Fin n → X × Y) where
  toFun z i := (z.1 i, z.2 i)
  invFun z := (fun i ↦ (z i).1, fun i ↦ (z i).2)
  left_inv z := by
    rcases z with ⟨x, y⟩
    rfl
  right_inv z := by
    rfl

/-- The real value of block distortion is the corresponding average of the
single-letter real distortion on the paired block. -/
theorem blockDistortion_toReal_eq_blockRealAverage
    (hn : 0 < n) (d : Distortion (X := X) (Y := Y))
    (x : Xblock n X) (y : Yblock n Y) :
    (blockDistortion n hn d x y).toReal =
      blockRealAverage n hn (fun z : X × Y => (d z.1 z.2 : ℝ))
        (blockPairEquiv n (x, y)) := by
  unfold blockDistortion blockRealAverage blockRealSum
  rw [ENNReal.toReal_div,
    ENNReal.toReal_sum (fun _ _ => ENNReal.coe_ne_top)]
  simp [blockPairEquiv]

def memorylessJointPMF
    (P : PMF X) (W : X → PMF Y) :
    PMF (Xblock n X × Yblock n Y) :=
  induced_joint (iidBlockPMF n P) (memorylessChannelBlockPMF n W)

@[simp] theorem memorylessJointPMF_apply
    (P : PMF X) (W : X → PMF Y)
    (x : Xblock n X) (y : Yblock n Y) :
    memorylessJointPMF n P W (x, y) =
      ∏ i : Fin n, induced_joint P W (x i, y i) := by
  simp only [memorylessJointPMF, induced_joint_apply, iidBlockPMF_apply,
    probBlock, memorylessChannelBlockPMF_apply]
  rw [Finset.prod_mul_distrib]

@[simp] theorem memorylessJointPMF_map_blockPairEquiv
    (P : PMF X) (W : X → PMF Y) :
    (memorylessJointPMF n P W).map (blockPairEquiv n) =
      iidBlockPMF n (induced_joint P W) := by
  ext z
  rw [map_apply_equiv]
  simp [blockPairEquiv, memorylessJointPMF_apply, iidBlockPMF_apply, probBlock]

@[simp] theorem memorylessJointPMF_fst
    (P : PMF X) (W : X → PMF Y) :
    (memorylessJointPMF n P W).map Prod.fst = iidBlockPMF n P := by
  exact induced_joint_fst (iidBlockPMF n P) (memorylessChannelBlockPMF n W)

@[simp] theorem memorylessJointPMF_snd
    (P : PMF X) (W : X → PMF Y) :
    (memorylessJointPMF n P W).map Prod.snd =
      iidBlockPMF n (P.bind W) := by
  rw [memorylessJointPMF, induced_joint_snd]
  ext y
  simp only [PMF.bind_apply, tsum_fintype, iidBlockPMF_apply, probBlock,
    memorylessChannelBlockPMF_apply]
  calc
    (∑ x : Xblock n X,
        (∏ i : Fin n, P (x i)) * ∏ i : Fin n, W (x i) (y i)) =
        ∑ x : Xblock n X,
          ∏ i : Fin n, P (x i) * W (x i) (y i) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.prod_mul_distrib]
    _ = ∏ i : Fin n, ∑ x : X, P x * W x (y i) := by
      rw [← Fintype.piFinset_univ]
      simpa using (Finset.sum_prod_piFinset
        (R := ENNReal) (ι := Fin n) (s := (Finset.univ : Finset X))
        (g := fun i x ↦ P x * W x (y i)))

/-- Every possible output of a positive-probability source block has positive
probability under the output marginal of the memoryless test channel. -/
theorem memorylessChannelBlockPMF_support_subset_output
    (P : PMF X) (W : X → PMF Y) (x : Xblock n X)
    (hx : iidBlockPMF n P x ≠ 0) :
    (memorylessChannelBlockPMF n W x).support ⊆
      (iidBlockPMF n (P.bind W)).support := by
  intro y hy
  rw [← memorylessJointPMF_snd]
  rw [PMF.mem_support_map_iff]
  refine ⟨(x, y), ?_, rfl⟩
  rw [PMF.mem_support_iff, memorylessJointPMF, induced_joint_apply]
  exact mul_ne_zero hx ((PMF.mem_support_iff _ _).mp hy)

@[simp] theorem memorylessJointPMF_coordinate
    (P : PMF X) (W : X → PMF Y) (i : Fin n) :
    (memorylessJointPMF n P W).map
        (fun z ↦ (z.1 i, z.2 i)) = induced_joint P W := by
  calc
    (memorylessJointPMF n P W).map (fun z ↦ (z.1 i, z.2 i)) =
        ((memorylessJointPMF n P W).map (blockPairEquiv n)).map
          (fun z ↦ z i) := by
      rw [PMF.map_comp]
      rfl
    _ = (iidBlockPMF n (induced_joint P W)).map (fun z ↦ z i) := by
      rw [memorylessJointPMF_map_blockPairEquiv]
    _ = induced_joint P W := iidBlockPMF_coordinate n (induced_joint P W) i

theorem memorylessJointPMF_expected_blockDistortion
    (hn : 0 < n) (P : PMF X) (W : X → PMF Y)
    (d : Distortion (X := X) (Y := Y)) :
    (∑ z : Xblock n X × Yblock n Y,
        memorylessJointPMF n P W z *
          blockDistortion n hn d z.1 z.2) =
      expected_distortion_single P W d := by
  simp only [blockDistortion]
  calc
    (∑ z : Xblock n X × Yblock n Y,
        memorylessJointPMF n P W z *
          ((∑ i : Fin n, (d (z.1 i) (z.2 i) : ENNReal)) / n)) =
        (∑ z : Xblock n X × Yblock n Y,
          (memorylessJointPMF n P W z *
            ∑ i : Fin n, (d (z.1 i) (z.2 i) : ENNReal)) / n) := by
      apply Finset.sum_congr rfl
      intro z _
      rw [mul_div_assoc]
    _ = (∑ z : Xblock n X × Yblock n Y,
        memorylessJointPMF n P W z *
          ∑ i : Fin n, (d (z.1 i) (z.2 i) : ENNReal)) / n := by
      simp only [div_eq_mul_inv]
      rw [Finset.sum_mul]
    _ = (∑ z : Xblock n X × Yblock n Y, ∑ i : Fin n,
        memorylessJointPMF n P W z *
          (d (z.1 i) (z.2 i) : ENNReal)) / n := by
      congr 1
      apply Finset.sum_congr rfl
      intro z _
      rw [Finset.mul_sum]
    _ =
        (∑ i : Fin n, ∑ z : Xblock n X × Yblock n Y,
          memorylessJointPMF n P W z *
            (d (z.1 i) (z.2 i) : ENNReal)) / n := by
      rw [Finset.sum_comm]
    _ = (∑ i : Fin n,
        jointExpectedDistortion (induced_joint P W) d) / n := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [← memorylessJointPMF_coordinate n P W i]
      rw [jointExpectedDistortion, ← Fintype.sum_prod_type']
      simpa using (sum_map_mul (memorylessJointPMF n P W)
        (fun z ↦ (z.1 i, z.2 i))
        (fun z ↦ (d z.1 z.2 : ENNReal))).symm
    _ = (∑ _i : Fin n, expected_distortion_single P W d) / n := by
      rw [jointExpectedDistortion_induced]
    _ = expected_distortion_single P W d := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [mul_comm]
      apply ENNReal.mul_div_cancel_right
      · exact_mod_cast hn.ne'
      · exact ENNReal.natCast_ne_top n

/-- A random codebook with `M` independently sampled block codewords. -/
noncomputable def randomCodebookPMF
    (M n : ℕ) (Q : PMF (Yblock n Y)) :
    PMF (Index M → Yblock n Y) :=
  iidBlockPMF M Q

@[simp] theorem randomCodebookPMF_codeword
    (M n : ℕ) (Q : PMF (Yblock n Y)) (j : Index M) :
    (randomCodebookPMF M n Q).map (fun codebook ↦ codebook j) = Q := by
  exact iidBlockPMF_coordinate M Q j

/-- Under an iid random codebook, the probability that no codeword satisfies
`good` is the `M`-th power of the one-codeword failure probability. -/
noncomputable def codebookMissProbability
    {B : Type*} [Fintype B] [DecidableEq B]
    (M : ℕ) (Q : PMF B) (good : B → Prop) [DecidablePred good] : ENNReal := by
  classical
  exact ∑ codebook : Index M → B, iidBlockPMF M Q codebook *
    if ∀ j, ¬ good (codebook j) then 1 else 0

noncomputable def codewordHitProbability
    {B : Type*} [Fintype B] [DecidableEq B]
    (Q : PMF B) (good : B → Prop) [DecidablePred good] : ENNReal :=
  ∑ b : B, if good b then Q b else 0

/-- A codebook-miss probability is an event probability and is therefore at
most one. -/
theorem codebookMissProbability_le_one
    {B : Type*} [Fintype B] [DecidableEq B]
    (M : ℕ) (Q : PMF B) (good : B → Prop) [DecidablePred good] :
    codebookMissProbability M Q good ≤ 1 := by
  classical
  unfold codebookMissProbability
  calc
    (∑ codebook : Index M → B, iidBlockPMF M Q codebook *
        if ∀ j, ¬ good (codebook j) then 1 else 0) ≤
        ∑ codebook : Index M → B, iidBlockPMF M Q codebook := by
      apply Finset.sum_le_sum
      intro codebook _
      by_cases hmiss : ∀ j, ¬ good (codebook j) <;> simp [hmiss]
    _ = 1 := sum_pmf (iidBlockPMF M Q)

/-- If a `[0,1]`-valued error is at most `ε` on a good set, then its average
is bounded by the source mass of the complementary set plus `ε`. -/
theorem weighted_pmf_le_badMass_add_error
    {B : Type*} [Fintype B] [DecidableEq B]
    (Q : PMF B) (q : B → ENNReal) (good : B → Prop) (ε : ENNReal)
    [DecidablePred good]
    (hq : ∀ b, q b ≤ 1) (hgood : ∀ b, good b → Q b ≠ 0 → q b ≤ ε) :
    (∑ b : B, Q b * q b) ≤
      (∑ b : B, if good b then 0 else Q b) + ε := by
  classical
  calc
    (∑ b : B, Q b * q b) ≤
        ∑ b : B, ((if good b then 0 else Q b) + ε * Q b) := by
      apply Finset.sum_le_sum
      intro b _
      by_cases hb : good b
      · rw [if_pos hb, zero_add]
        by_cases hQ : Q b = 0
        · simp [hQ]
        · simpa [mul_comm] using mul_le_mul_left (hgood b hb hQ) (Q b)
      · rw [if_neg hb]
        have hq_le : Q b * q b ≤ Q b := by
          simpa [mul_comm] using mul_le_mul_left (hq b) (Q b)
        exact hq_le.trans (le_add_right le_rfl)
    _ = (∑ b : B, if good b then 0 else Q b) + ε := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, sum_pmf, mul_one]

/-- The source-average probability that a random iid codebook misses the
source-dependent good output set. -/
noncomputable def averageCodebookMissProbability
    {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (M : ℕ) (P : PMF A) (Q : PMF B) (good : A → B → Prop)
    [∀ a, DecidablePred (good a)] : ENNReal :=
  ∑ a : A, P a * codebookMissProbability M Q (good a)

/-- For a fixed codebook, the source-average probability that it contains no
good codeword. -/
noncomputable def codebookSourceMissProbability
    {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (M : ℕ) (P : PMF A) (codebook : Index M → B) (good : A → B → Prop)
    [∀ a, DecidablePred (good a)] : ENNReal :=
  ∑ a : A, P a * if ∀ j, ¬ good a (codebook j) then 1 else 0

/-- A `codebookCode` meets the target distortion whenever its codebook has a
good codeword; on a miss, the finite-alphabet distortion bound controls the
loss. -/
theorem blockDistortion_codebookCode_le_threshold_add_bound_mul_miss
    (hn : 0 < n) (hM : 0 < M) (d : Distortion (X := X) (Y := Y))
    (codebook : Index M → Yblock n Y) (good : Xblock n X → Yblock n Y → Prop)
    [∀ x, DecidablePred (good x)] (distortionThreshold : ENNReal)
    (hgood : ∀ x y, good x y → blockDistortion n hn d x y ≤ distortionThreshold)
    (x : Xblock n X) :
    blockDistortion n hn d x
        ((codebookCode n M hM codebook good).decoder
          ((codebookCode n M hM codebook good).encoder x)) ≤
      distortionThreshold + (distortionBound d : ENNReal) *
        if ∀ j, ¬ good x (codebook j) then 1 else 0 := by
  classical
  by_cases hmiss : ∀ j, ¬ good x (codebook j)
  · rw [if_pos hmiss]
    calc
      blockDistortion n hn d x
          ((codebookCode n M hM codebook good).decoder
            ((codebookCode n M hM codebook good).encoder x)) ≤
          (distortionBound d : ENNReal) :=
        blockDistortion_le_bound n hn d _ _
      _ ≤ distortionThreshold + (distortionBound d : ENNReal) * 1 := by
        simpa using le_add_left (le_refl (distortionBound d : ENNReal))
  · have hnotmiss : ¬ ∀ j, ¬ good x (codebook j) := hmiss
    push_neg at hmiss
    rw [if_neg hnotmiss]
    simp only [mul_zero, add_zero]
    change blockDistortion n hn d x
      (codebook (codebookEncoder n M hM codebook good x)) ≤ distortionThreshold
    exact hgood x _
      (codebookEncoder_good_of_exists n M hM codebook good x hmiss)

/-- A real-valued quantity on a finite probability space is no smaller at
some point than its PMF-weighted average. -/
theorem exists_le_pmf_weighted_sum
    {A : Type*} [Fintype A] [DecidableEq A]
    (P : PMF A) (f : A → ENNReal) :
    ∃ a : A, f a ≤ ∑ b : A, P b * f b := by
  classical
  obtain ⟨a, ha, hmin⟩ := Set.exists_min_image P.support f (Set.toFinite _)
    P.support_nonempty
  refine ⟨a, ?_⟩
  have hsum : (∑ b : A, P b * f a) ≤ ∑ b : A, P b * f b := by
    apply Finset.sum_le_sum
    intro b _
    by_cases hb : b ∈ P.support
    · simpa [mul_comm] using mul_le_mul_left (hmin b hb) (P b)
    · rw [(P.apply_eq_zero_iff b).mpr hb]
      simp
  calc
    f a = ∑ b : A, P b * f a := by rw [← Finset.sum_mul, sum_pmf, one_mul]
    _ ≤ ∑ b : A, P b * f b := hsum

/-- Averaging the fixed-codebook miss probability over iid codebooks recovers
the random-codebook average miss probability. -/
theorem averageCodebookMissProbability_eq_average_codebookSourceMissProbability
    {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (M : ℕ) (P : PMF A) (Q : PMF B) (good : A → B → Prop)
    [∀ a, DecidablePred (good a)] :
    averageCodebookMissProbability M P Q good =
      ∑ codebook : Index M → B, iidBlockPMF M Q codebook *
        codebookSourceMissProbability M P codebook good := by
  unfold averageCodebookMissProbability codebookSourceMissProbability
    codebookMissProbability
  calc
    (∑ a : A, P a * ∑ codebook : Index M → B, iidBlockPMF M Q codebook *
        if ∀ j, ¬ good a (codebook j) then 1 else 0) =
        ∑ a : A, ∑ codebook : Index M → B, P a *
          (iidBlockPMF M Q codebook *
            if ∀ j, ¬ good a (codebook j) then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.mul_sum]
    _ = ∑ codebook : Index M → B, ∑ a : A, P a *
        (iidBlockPMF M Q codebook *
          if ∀ j, ¬ good a (codebook j) then 1 else 0) := Finset.sum_comm
    _ = ∑ codebook : Index M → B, iidBlockPMF M Q codebook *
        ∑ a : A, P a * if ∀ j, ¬ good a (codebook j) then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro codebook _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring

/-- The probabilistic method extracts a deterministic codebook whose source
average miss probability is no larger than the random-codebook average. -/
theorem exists_codebookSourceMissProbability_le_averageCodebookMissProbability
    {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (M : ℕ) (P : PMF A) (Q : PMF B) (good : A → B → Prop)
    [∀ a, DecidablePred (good a)] :
    ∃ codebook : Index M → B,
      codebookSourceMissProbability M P codebook good ≤
        averageCodebookMissProbability M P Q good := by
  obtain ⟨codebook, hcodebook⟩ := exists_le_pmf_weighted_sum (iidBlockPMF M Q)
    (fun codebook => codebookSourceMissProbability M P codebook good)
  refine ⟨codebook, ?_⟩
  calc
    codebookSourceMissProbability M P codebook good ≤
        ∑ codebook : Index M → B, iidBlockPMF M Q codebook *
          codebookSourceMissProbability M P codebook good := hcodebook
    _ = averageCodebookMissProbability M P Q good :=
      (averageCodebookMissProbability_eq_average_codebookSourceMissProbability
        M P Q good).symm

/-- Average random-codebook error is bounded by the bad-source mass plus a
uniform error bound valid on the good-source set. -/
theorem averageCodebookMissProbability_le_badMass_add_error
    {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (M : ℕ) (P : PMF A) (Q : PMF B) (good : A → B → Prop)
    [∀ a, DecidablePred (good a)] (high : A → Prop) (ε : ENNReal)
    [DecidablePred high]
    (hhigh : ∀ a, high a → P a ≠ 0 →
      codebookMissProbability M Q (good a) ≤ ε) :
    averageCodebookMissProbability M P Q good ≤
      (∑ a : A, if high a then 0 else P a) + ε := by
  classical
  unfold averageCodebookMissProbability
  apply weighted_pmf_le_badMass_add_error P
    (fun a => codebookMissProbability M Q (good a)) high ε
  · intro a
    exact codebookMissProbability_le_one M Q (good a)
  · exact hhigh

/-- The value of a finite event probability does not depend on the chosen
decidability instance for that event. -/
theorem codewordHitProbability_eq_of_decidable
    {B : Type*} [Fintype B] [DecidableEq B]
    (Q : PMF B) (good : B → Prop)
    (h₁ h₂ : DecidablePred good) :
    @codewordHitProbability B _ _ Q good h₁ =
      @codewordHitProbability B _ _ Q good h₂ := by
  unfold codewordHitProbability
  apply Finset.sum_congr rfl
  intro b _
  by_cases hb : good b <;> simp [hb]

/-- Event probabilities under a finite PMF are monotone under inclusion. -/
theorem codewordHitProbability_mono
    {B : Type*} [Fintype B] [DecidableEq B]
    (Q : PMF B) (A B : B → Prop) [DecidablePred A] [DecidablePred B]
    (hAB : ∀ b, A b → B b) :
    codewordHitProbability Q A ≤ codewordHitProbability Q B := by
  unfold codewordHitProbability
  apply Finset.sum_le_sum
  intro b _
  by_cases hA : A b
  · simp [hA, hAB b hA]
  · simp [hA]

/-- The probability of an intersection plus the probabilities of the two
failure events is at least one. -/
theorem one_le_codewordHitProbability_and_add_not
    {B : Type*} [Fintype B] [DecidableEq B]
    (Q : PMF B) (A B : B → Prop) [DecidablePred A] [DecidablePred B] :
    1 ≤ codewordHitProbability Q (fun b => A b ∧ B b) +
      codewordHitProbability Q (fun b => ¬ A b) +
      codewordHitProbability Q (fun b => ¬ B b) := by
  classical
  unfold codewordHitProbability
  rw [← sum_pmf Q]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro b _
  by_cases hA : A b <;> by_cases hB : B b <;> simp [hA, hB]

/-- A pointwise likelihood comparison on a good set gives the corresponding
comparison between its total probabilities. -/
theorem codewordHitProbability_le_mul
    {B : Type*} [Fintype B] [DecidableEq B]
    (P Q : PMF B) (good : B → Prop) [DecidablePred good] (c : ENNReal)
    (h : ∀ b, good b → P b ≤ c * Q b) :
    codewordHitProbability P good ≤ c * codewordHitProbability Q good := by
  unfold codewordHitProbability
  calc
    (∑ b : B, if good b then P b else 0) ≤
        ∑ b : B, if good b then c * Q b else 0 := by
      apply Finset.sum_le_sum
      intro b _
      by_cases hgood : good b
      · simpa [hgood] using h b hgood
      · simp [hgood]
    _ = c * ∑ b : B, if good b then Q b else 0 := by
      symm
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      by_cases hgood : good b <;> simp [hgood]

theorem codewordHitProbability_add_miss
    {B : Type*} [Fintype B] [DecidableEq B]
    (Q : PMF B) (good : B → Prop) [DecidablePred good] :
    codewordHitProbability Q good +
      (∑ b : B, if good b then 0 else Q b) = 1 := by
  unfold codewordHitProbability
  rw [← Finset.sum_add_distrib]
  calc
    (∑ b : B, ((if good b then Q b else 0) +
        (if good b then 0 else Q b))) = ∑ b : B, Q b := by
      apply Finset.sum_congr rfl
      intro b _
      by_cases hgood : good b <;> simp [hgood]
    _ = 1 := sum_pmf Q

/-- An event probability under a finite PMF is at most one. -/
theorem codewordHitProbability_le_one
    {B : Type*} [Fintype B] [DecidableEq B]
    (Q : PMF B) (good : B → Prop) [DecidablePred good] :
    codewordHitProbability Q good ≤ 1 := by
  calc
    codewordHitProbability Q good ≤
        codewordHitProbability Q good +
          (∑ b : B, if good b then 0 else Q b) := le_add_right le_rfl
    _ = 1 := codewordHitProbability_add_miss Q good

/-- If a source-good event has probability at least `1 - 2δ`, then the mass
of its complement is at most `2δ`. -/
theorem badMass_le_two_mul_of_one_sub_le_hitProbability
    {B : Type*} [Fintype B] [DecidableEq B]
    (Q : PMF B) (good : B → Prop) [DecidablePred good] (δ : ENNReal)
    (hgood : 1 - 2 * δ ≤ codewordHitProbability Q good) :
    (∑ b : B, if good b then 0 else Q b) ≤ 2 * δ := by
  have hhit_ne_top : codewordHitProbability Q good ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (codewordHitProbability_le_one Q good)
  have hright : 1 ≤ codewordHitProbability Q good + 2 * δ := by
    rwa [tsub_le_iff_right] at hgood
  have hadd : codewordHitProbability Q good +
      (∑ b : B, if good b then 0 else Q b) ≤
      codewordHitProbability Q good + 2 * δ := by
    rw [codewordHitProbability_add_miss]
    exact hright
  exact ENNReal.le_of_add_le_add_left hhit_ne_top hadd

/-- The average of a `[0,1]`-valued function is bounded by the mass of the
set where it exceeds a threshold, plus that threshold. -/
theorem weighted_pmf_le_hitProbability_add_threshold
    {B : Type*} [Fintype B] [DecidableEq B]
    (Q : PMF B) (q : B → ENNReal) (t : ENNReal)
    (hq : ∀ b, q b ≤ 1) :
    (∑ b : B, Q b * q b) ≤
      codewordHitProbability Q (fun b => t ≤ q b) + t := by
  classical
  calc
    (∑ b : B, Q b * q b) ≤
        ∑ b : B, ((if t ≤ q b then Q b else 0) + t * Q b) := by
      apply Finset.sum_le_sum
      intro b _
      by_cases hb : t ≤ q b
      · rw [if_pos hb]
        have hmul : Q b * q b ≤ Q b := by
          simpa [mul_comm] using mul_le_mul_left (hq b) (Q b)
        exact hmul.trans (le_add_right le_rfl)
      · rw [if_neg hb]
        have hqt : q b ≤ t := le_of_lt (lt_of_not_ge hb)
        simpa [mul_comm] using mul_le_mul_left hqt (Q b)
    _ = codewordHitProbability Q (fun b => t ≤ q b) + t := by
      unfold codewordHitProbability
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, sum_pmf, mul_one]

/-- For a `[0,1]`-valued function, its average plus one half of the mass where
it is below one half is at most one. -/
theorem weighted_pmf_add_half_lowMass_le_one
    {B : Type*} [Fintype B] [DecidableEq B]
    (Q : PMF B) (q : B → ENNReal) (hq : ∀ b, q b ≤ 1) :
    (∑ b : B, Q b * q b) +
        (1 / 2 : ENNReal) * (∑ b : B, if 1 / 2 ≤ q b then 0 else Q b) ≤ 1 := by
  classical
  calc
    (∑ b : B, Q b * q b) +
        (1 / 2 : ENNReal) * (∑ b : B, if 1 / 2 ≤ q b then 0 else Q b) =
        ∑ b : B, (Q b * q b +
          (1 / 2 : ENNReal) * (if 1 / 2 ≤ q b then 0 else Q b)) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    _ ≤ ∑ b : B, Q b := by
      apply Finset.sum_le_sum
      intro b _
      by_cases hb : 1 / 2 ≤ q b
      · rw [if_pos hb, mul_zero, add_zero]
        simpa [mul_comm] using mul_le_mul_left (hq b) (Q b)
      · rw [if_neg hb]
        have hqhalf : q b ≤ (1 / 2 : ENNReal) := le_of_lt (lt_of_not_ge hb)
        calc
          Q b * q b + (1 / 2 : ENNReal) * Q b = Q b * (q b + 1 / 2) := by
            ring
          _ ≤ Q b * ((1 / 2 : ENNReal) + 1 / 2) := by
            simpa [mul_comm] using
              mul_le_mul_left (add_le_add_left hqhalf _) (Q b)
          _ = Q b := by simpa using (ENNReal.inv_two_add_inv_two ▸ (mul_one (Q b)))
    _ = 1 := sum_pmf Q

/-- If a `[0,1]`-valued function has average at least `1 - δ`, then the mass
where it is at least one half is at least `1 - 2δ`. -/
theorem one_sub_two_mul_le_hitProbability_half_of_weighted
    {B : Type*} [Fintype B] [DecidableEq B]
    (Q : PMF B) (q : B → ENNReal) (δ : ENNReal)
    (hq : ∀ b, q b ≤ 1) (hδ : δ ≤ 1)
    (hmean : 1 - δ ≤ ∑ b : B, Q b * q b) :
    1 - 2 * δ ≤ codewordHitProbability Q (fun b => 1 / 2 ≤ q b) := by
  classical
  let high : B → Prop := fun b => 1 / 2 ≤ q b
  let miss : ENNReal := ∑ b : B, if high b then 0 else Q b
  have hsum : (1 - δ) + (1 / 2 : ENNReal) * miss ≤ 1 := by
    calc
      (1 - δ) + (1 / 2 : ENNReal) * miss ≤
          (∑ b : B, Q b * q b) + (1 / 2 : ENNReal) * miss :=
        add_le_add_left hmean _
      _ ≤ 1 := weighted_pmf_add_half_lowMass_le_one Q q hq
  have hhalfmiss : (1 / 2 : ENNReal) * miss ≤ δ := by
    have hsub := ENNReal.le_sub_of_add_le_left (ENNReal.sub_ne_top ENNReal.one_ne_top) hsum
    rw [ENNReal.sub_sub_cancel ENNReal.one_ne_top hδ] at hsub
    exact hsub
  have hmiss : miss ≤ 2 * δ := by
    have hhalf_two : (1 / 2 : ENNReal) * 2 = 1 := by
      exact ENNReal.div_mul_cancel (by norm_num) (by norm_num)
    calc
      miss = ((1 / 2 : ENNReal) * miss) * 2 := by
        calc
          miss = 1 * miss := (one_mul _).symm
          _ = ((1 / 2 : ENNReal) * 2) * miss := by rw [hhalf_two]
          _ = ((1 / 2 : ENNReal) * miss) * 2 := by ring
      _ ≤ δ * 2 := mul_le_mul_left hhalfmiss 2
      _ = 2 * δ := mul_comm _ _
  rw [tsub_le_iff_right]
  change 1 ≤ codewordHitProbability Q high + 2 * δ
  calc
    1 = codewordHitProbability Q high + miss := codewordHitProbability_add_miss Q high |>.symm
    _ = miss + codewordHitProbability Q high := add_comm _ _
    _ ≤ 2 * δ + codewordHitProbability Q high := add_le_add_left hmiss _
    _ = codewordHitProbability Q high + 2 * δ := add_comm _ _

theorem codebookMissProbability_eq_pow
    {B : Type*} [Fintype B] [DecidableEq B]
    (M : ℕ) (Q : PMF B) (good : B → Prop) [DecidablePred good] :
    codebookMissProbability M Q good =
      (∑ b : B, if good b then 0 else Q b) ^ M := by
  classical
  unfold codebookMissProbability
  calc
    (∑ codebook : Index M → B, iidBlockPMF M Q codebook *
      if ∀ j, ¬ good (codebook j) then 1 else 0) =
        ∑ codebook : Index M → B,
          ∏ j : Index M, if good (codebook j) then 0 else Q (codebook j) := by
      apply Finset.sum_congr rfl
      intro codebook _
      by_cases hgood : ∀ j, ¬ good (codebook j)
      · rw [if_pos hgood, mul_one, iidBlockPMF_apply]
        unfold probBlock
        apply Finset.prod_congr rfl
        intro j _
        simp [hgood j]
      · rw [if_neg hgood, mul_zero]
        push_neg at hgood
        obtain ⟨j, hj⟩ := hgood
        have hjgood : good (codebook j) := by tauto
        symm
        apply Finset.prod_eq_zero (f := fun j : Index M ↦
          if good (codebook j) then 0 else Q (codebook j))
          (Finset.mem_univ j)
        rw [if_pos hjgood]
    _ = ∏ _j : Index M, ∑ b : B, if good b then 0 else Q b := by
      rw [← Fintype.piFinset_univ]
      simpa using (Finset.sum_prod_piFinset
        (R := ENNReal) (ι := Index M) (s := (Finset.univ : Finset B))
        (g := fun _ b ↦ if good b then 0 else Q b))
    _ = (∑ b : B, if good b then 0 else Q b) ^ M := by
      simp

theorem codebookMissProbability_eq_one_sub_hit
    {B : Type*} [Fintype B] [DecidableEq B]
    (M : ℕ) (Q : PMF B) (good : B → Prop) [DecidablePred good] :
    codebookMissProbability M Q good =
      (1 - codewordHitProbability Q good) ^ M := by
  have hsum := codewordHitProbability_add_miss Q good
  have hhit_le : codewordHitProbability Q good ≤ 1 := by
    calc
      codewordHitProbability Q good ≤
          codewordHitProbability Q good +
            (∑ b : B, if good b then 0 else Q b) := le_add_right le_rfl
      _ = 1 := hsum
  have hhit_ne_top : codewordHitProbability Q good ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top hhit_le
  rw [codebookMissProbability_eq_pow]
  congr 1
  apply ENNReal.eq_sub_of_add_eq hhit_ne_top
  simpa [add_comm] using hsum

/-- A lower bound on the one-codeword hit probability gives an upper bound on
the probability that an iid codebook misses the good set. -/
theorem codebookMissProbability_le_one_sub_pow_of_le_hit
    {B : Type*} [Fintype B] [DecidableEq B]
    (M : ℕ) (Q : PMF B) (good : B → Prop) [DecidablePred good]
    (p : ENNReal) (hp : p ≤ codewordHitProbability Q good) :
    codebookMissProbability M Q good ≤ (1 - p) ^ M := by
  rw [codebookMissProbability_eq_one_sub_hit]
  exact pow_le_pow_left' (tsub_le_tsub_left hp 1) M

/-- The usual exponential upper bound for the probability that `M`
independent trials all miss an event of probability `p`. -/
theorem one_sub_ofReal_pow_le_exp_neg_mul
    (M : ℕ) (p : ℝ) (hp : 0 ≤ p) :
    (1 - ENNReal.ofReal p) ^ M ≤
      ENNReal.ofReal (Real.exp (-((M : ℝ) * p))) := by
  calc
    (1 - ENNReal.ofReal p) ^ M ≤
        (ENNReal.ofReal (Real.exp (-p))) ^ M := by
      apply pow_le_pow_left'
      rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub 1 hp]
      exact ENNReal.ofReal_mono (Real.one_sub_le_exp_neg p)
    _ = ENNReal.ofReal ((Real.exp (-p)) ^ M) :=
      (ENNReal.ofReal_pow (Real.exp_nonneg _) M).symm
    _ = ENNReal.ofReal (Real.exp (-((M : ℝ) * p))) := by
      congr 1
      rw [← Real.exp_nat_mul]
      congr 1
      ring

/-- The random codebook used for a test channel `W`: every codeword has law
`(P.bind W)^n`. -/
noncomputable def memorylessCodebookPMF
    (M n : ℕ) (P : PMF X) (W : X → PMF Y) :
    PMF (Index M → Yblock n Y) :=
  randomCodebookPMF M n (iidBlockPMF n (P.bind W))

@[simp] theorem memorylessCodebookPMF_codeword
    (M n : ℕ) (P : PMF X) (W : X → PMF Y) (j : Index M) :
    (memorylessCodebookPMF M n P W).map (fun codebook ↦ codebook j) =
      iidBlockPMF n (P.bind W) := by
  exact randomCodebookPMF_codeword M n (iidBlockPMF n (P.bind W)) j

theorem iidBlockPMF_succ_map_initLast (k : ℕ) (P : PMF X) :
    (iidBlockPMF (k + 1) P).map (finInitLastEquiv k X) =
      product_pmf (iidBlockPMF k P) P := by
  ext z
  rcases z with ⟨u, a⟩
  rw [map_apply_equiv, product_pmf_apply]
  simp only [iidBlockPMF_apply, probBlock]
  rw [Fin.prod_univ_castSucc]
  simp only [finInitLastEquiv_symm_apply, Fin.snoc_castSucc, Fin.snoc_last]

/-- The expectation of an IID block sum is the blocklength times the
single-letter expectation. -/
theorem pmfRealExpectation_iidBlockPMF_blockRealSum
    (k : ℕ) (P : PMF X) (f : X → ℝ) :
    pmfRealExpectation (iidBlockPMF k P) (blockRealSum k f) =
      (k : ℝ) * pmfRealExpectation P f := by
  induction k with
  | zero =>
      have hzero : blockRealSum 0 f = (fun _ : Xblock 0 X => 0) := by
        funext x
        exact blockRealSum_zero f x
      rw [hzero]
      simp
  | succ k ih =>
      calc
        pmfRealExpectation (iidBlockPMF (k + 1) P) (blockRealSum (k + 1) f) =
            pmfRealExpectation
              ((iidBlockPMF (k + 1) P).map (finInitLastEquiv k X))
              (fun z => blockRealSum k f z.1 + f z.2) := by
          symm
          calc
            pmfRealExpectation
                ((iidBlockPMF (k + 1) P).map (finInitLastEquiv k X))
                (fun z => blockRealSum k f z.1 + f z.2) =
                pmfRealExpectation (iidBlockPMF (k + 1) P)
                  ((fun z => blockRealSum k f z.1 + f z.2) ∘ finInitLastEquiv k X) :=
              pmfRealExpectation_map (iidBlockPMF (k + 1) P) (finInitLastEquiv k X) _
            _ = pmfRealExpectation (iidBlockPMF (k + 1) P)
                (blockRealSum (k + 1) f) := by
              congr 1
              funext x
              change blockRealSum k f (Fin.init x) + f (x (Fin.last k)) =
                blockRealSum (k + 1) f x
              exact (blockRealSum_succ k f x).symm
        _ = pmfRealExpectation (product_pmf (iidBlockPMF k P) P)
            (fun z => blockRealSum k f z.1 + f z.2) := by
          rw [iidBlockPMF_succ_map_initLast]
        _ = pmfRealExpectation (iidBlockPMF k P) (blockRealSum k f) +
            pmfRealExpectation P f :=
          pmfRealExpectation_product_pmf_add (iidBlockPMF k P) P (blockRealSum k f) f
        _ = ((k + 1 : ℕ) : ℝ) * pmfRealExpectation P f := by
          rw [ih]
          rw [Nat.cast_add, Nat.cast_one]
          ring

/-- The variance of an IID block sum is the blocklength times the
single-letter variance. -/
theorem pmfRealVariance_iidBlockPMF_blockRealSum
    (k : ℕ) (P : PMF X) (f : X → ℝ) :
    pmfRealVariance (iidBlockPMF k P) (blockRealSum k f) =
      (k : ℝ) * pmfRealVariance P f := by
  induction k with
  | zero =>
      have hzero : blockRealSum 0 f = (fun _ : Xblock 0 X => 0) := by
        funext x
        exact blockRealSum_zero f x
      rw [hzero]
      simp
  | succ k ih =>
      calc
        pmfRealVariance (iidBlockPMF (k + 1) P) (blockRealSum (k + 1) f) =
            pmfRealVariance
              ((iidBlockPMF (k + 1) P).map (finInitLastEquiv k X))
              (fun z => blockRealSum k f z.1 + f z.2) := by
          symm
          calc
            pmfRealVariance
                ((iidBlockPMF (k + 1) P).map (finInitLastEquiv k X))
                (fun z => blockRealSum k f z.1 + f z.2) =
                pmfRealVariance (iidBlockPMF (k + 1) P)
                  ((fun z => blockRealSum k f z.1 + f z.2) ∘ finInitLastEquiv k X) :=
              pmfRealVariance_map (iidBlockPMF (k + 1) P) (finInitLastEquiv k X) _
            _ = pmfRealVariance (iidBlockPMF (k + 1) P)
                (blockRealSum (k + 1) f) := by
              congr 1
              funext x
              change blockRealSum k f (Fin.init x) + f (x (Fin.last k)) =
                blockRealSum (k + 1) f x
              exact (blockRealSum_succ k f x).symm
        _ = pmfRealVariance (product_pmf (iidBlockPMF k P) P)
            (fun z => blockRealSum k f z.1 + f z.2) := by
          rw [iidBlockPMF_succ_map_initLast]
        _ = pmfRealVariance (iidBlockPMF k P) (blockRealSum k f) +
            pmfRealVariance P f :=
          pmfRealVariance_product_pmf_add (iidBlockPMF k P) P (blockRealSum k f) f
        _ = ((k + 1 : ℕ) : ℝ) * pmfRealVariance P f := by
          rw [ih]
          rw [Nat.cast_add, Nat.cast_one]
          ring

/-- An IID block average has the single-letter expectation. -/
theorem pmfRealExpectation_iidBlockPMF_blockRealAverage
    (hn : 0 < n) (P : PMF X) (f : X → ℝ) :
    pmfRealExpectation (iidBlockPMF n P) (blockRealAverage n hn f) =
      pmfRealExpectation P f := by
  have hn0 : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hn)
  calc
    pmfRealExpectation (iidBlockPMF n P) (blockRealAverage n hn f) =
        pmfRealExpectation (iidBlockPMF n P)
          (fun x => (n : ℝ)⁻¹ * blockRealSum n f x) := by
      congr 1
      funext x
      unfold blockRealAverage
      rw [div_eq_mul_inv]
      ring
    _ = (n : ℝ)⁻¹ *
        pmfRealExpectation (iidBlockPMF n P) (blockRealSum n f) :=
      pmfRealExpectation_const_mul (iidBlockPMF n P) (n : ℝ)⁻¹ (blockRealSum n f)
    _ = (n : ℝ)⁻¹ * ((n : ℝ) * pmfRealExpectation P f) := by
      rw [pmfRealExpectation_iidBlockPMF_blockRealSum]
    _ = pmfRealExpectation P f := by
      rw [← mul_assoc, inv_mul_cancel₀ hn0, one_mul]

/-- The variance of an IID block average is the single-letter variance divided
by the blocklength. -/
theorem pmfRealVariance_iidBlockPMF_blockRealAverage
    (hn : 0 < n) (P : PMF X) (f : X → ℝ) :
    pmfRealVariance (iidBlockPMF n P) (blockRealAverage n hn f) =
      pmfRealVariance P f / n := by
  have hn0 : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hn)
  calc
    pmfRealVariance (iidBlockPMF n P) (blockRealAverage n hn f) =
        pmfRealVariance (iidBlockPMF n P)
          (fun x => (n : ℝ)⁻¹ * blockRealSum n f x) := by
      congr 1
      funext x
      unfold blockRealAverage
      rw [div_eq_mul_inv]
      ring
    _ = (n : ℝ)⁻¹ ^ 2 *
        pmfRealVariance (iidBlockPMF n P) (blockRealSum n f) :=
      pmfRealVariance_const_mul (iidBlockPMF n P) (n : ℝ)⁻¹ (blockRealSum n f)
    _ = (n : ℝ)⁻¹ ^ 2 * ((n : ℝ) * pmfRealVariance P f) := by
      rw [pmfRealVariance_iidBlockPMF_blockRealSum]
    _ = pmfRealVariance P f / n := by
      calc
        (n : ℝ)⁻¹ ^ 2 * ((n : ℝ) * pmfRealVariance P f) =
            ((n : ℝ)⁻¹ * (n : ℝ)) *
              ((n : ℝ)⁻¹ * pmfRealVariance P f) := by ring
        _ = (n : ℝ)⁻¹ * pmfRealVariance P f := by
          rw [inv_mul_cancel₀ hn0, one_mul]
        _ = pmfRealVariance P f / n := by
          rw [div_eq_mul_inv]
          ring

/-- Finite-PMF Chebyshev bound for the average of an IID block. -/
theorem iidBlockPMF_blockRealAverage_deviation_le
    (hn : 0 < n) (P : PMF X) (f : X → ℝ) (ε : ℝ) (hε : 0 < ε) :
    (∑ x : Xblock n X,
      if ε ≤ |blockRealAverage n hn f x - pmfRealExpectation P f| then
        iidBlockPMF n P x else 0) ≤
      ENNReal.ofReal ((pmfRealVariance P f / n) / ε ^ 2) := by
  have h := pmf_deviation_probability_le_variance_div_sq
    (iidBlockPMF n P) (blockRealAverage n hn f) ε hε
  rw [pmfRealExpectation_iidBlockPMF_blockRealAverage,
    pmfRealVariance_iidBlockPMF_blockRealAverage] at h
  exact h

theorem shannonEntropy_iidBlockPMF (k : ℕ) (P : PMF X) :
    shannonEntropy (iidBlockPMF k P) =
      (k : ℝ) * shannonEntropy P := by
  induction k with
  | zero =>
      apply le_antisymm
      · simpa using shannonEntropy_le_log_card (iidBlockPMF 0 P)
      · simpa using shannonEntropy_nonneg (iidBlockPMF 0 P)
  | succ k ih =>
      calc
        shannonEntropy (iidBlockPMF (k + 1) P) =
            shannonEntropy
              ((iidBlockPMF (k + 1) P).map (finInitLastEquiv k X)) := by
          symm
          exact shannonEntropy_map_of_injective _ _
            (finInitLastEquiv k X).injective
        _ = shannonEntropy (product_pmf (iidBlockPMF k P) P) := by
          rw [iidBlockPMF_succ_map_initLast]
        _ = shannonEntropy (iidBlockPMF k P) + shannonEntropy P :=
          shannonEntropy_product_pmf _ _
        _ = ((k + 1 : ℕ) : ℝ) * shannonEntropy P := by
          rw [ih]
          push_cast
          ring

theorem mutualInformationEntropy_memorylessJointPMF
    (P : PMF X) (W : X → PMF Y) :
    mutualInformationEntropy (memorylessJointPMF n P W) =
      (n : ℝ) * mutualInformationEntropy (induced_joint P W) := by
  have hjoint :
      shannonEntropy (memorylessJointPMF n P W) =
        shannonEntropy (iidBlockPMF n (induced_joint P W)) := by
    calc
      shannonEntropy (memorylessJointPMF n P W) =
          shannonEntropy
            ((memorylessJointPMF n P W).map (blockPairEquiv n)) := by
        symm
        exact shannonEntropy_map_of_injective _ _ (blockPairEquiv n).injective
      _ = shannonEntropy (iidBlockPMF n (induced_joint P W)) := by
        rw [memorylessJointPMF_map_blockPairEquiv]
  unfold mutualInformationEntropy
  rw [memorylessJointPMF_fst, memorylessJointPMF_snd, hjoint,
    shannonEntropy_iidBlockPMF, shannonEntropy_iidBlockPMF,
    shannonEntropy_iidBlockPMF]
  rw [induced_joint_fst, induced_joint_snd]
  ring

theorem mutual_information_memorylessJointPMF
    (P : PMF X) (W : X → PMF Y) :
    mutual_information (memorylessJointPMF n P W) =
      (n : ENNReal) * mutual_information (induced_joint P W) := by
  rw [mutual_information_eq_ofReal_entropy,
    mutualInformationEntropy_memorylessJointPMF,
    mutual_information_eq_ofReal_entropy]
  rw [ENNReal.ofReal_mul (Nat.cast_nonneg n)]
  norm_cast

/-- Single-letter information density for the source law and a test channel. -/
noncomputable def singleLetterInformationDensity
    (P : PMF X) (W : X → PMF Y) (z : X × Y) : ℝ :=
  Real.log (pmfDensityRatio (induced_joint P W)
    (product_pmf P (P.bind W)) z).toReal

theorem pmfRealExpectation_singleLetterInformationDensity
    (P : PMF X) (W : X → PMF Y) :
    pmfRealExpectation (induced_joint P W) (singleLetterInformationDensity P W) =
      mutualInformationEntropy (induced_joint P W) := by
  unfold pmfRealExpectation singleLetterInformationDensity
  simpa using sum_weighted_log_densityRatio_product_marginals (induced_joint P W)

/-- Information density of a source/reproduction block under the memoryless
test-channel joint distribution. -/
noncomputable def memorylessInformationDensity
    (P : PMF X) (W : X → PMF Y)
    (z : Xblock n X × Yblock n Y) : ℝ :=
  Real.log (pmfDensityRatio (memorylessJointPMF n P W)
    (product_pmf ((memorylessJointPMF n P W).map Prod.fst)
      ((memorylessJointPMF n P W).map Prod.snd)) z).toReal

theorem memorylessInformationDensity_eq
    (P : PMF X) (W : X → PMF Y)
    (z : Xblock n X × Yblock n Y) :
    memorylessInformationDensity n P W z =
      Real.log (pmfDensityRatio (memorylessJointPMF n P W)
        (product_pmf (iidBlockPMF n P) (iidBlockPMF n (P.bind W))) z).toReal := by
  simp [memorylessInformationDensity]

/-- The real-valued likelihood ratio of a memoryless block factors into its
single-letter likelihood ratios. -/
theorem memorylessPmfDensityRatio_toReal_eq_prod
    (P : PMF X) (W : X → PMF Y)
    (x : Xblock n X) (y : Yblock n Y) :
    (pmfDensityRatio (memorylessJointPMF n P W)
      (product_pmf (iidBlockPMF n P) (iidBlockPMF n (P.bind W))) (x, y)).toReal =
      ∏ i : Fin n, (pmfDensityRatio (induced_joint P W)
        (product_pmf P (P.bind W)) (x i, y i)).toReal := by
  simp only [pmfDensityRatio, memorylessJointPMF_apply, product_pmf_apply,
    iidBlockPMF_apply, probBlock, induced_joint_apply, ENNReal.toReal_mul,
    ENNReal.toReal_inv, ENNReal.toReal_prod]
  have hden :
      (∏ i : Fin n, (P (x i)).toReal * ((P.bind W) (y i)).toReal) =
        (∏ i : Fin n, (P (x i)).toReal) *
          ∏ i : Fin n, ((P.bind W) (y i)).toReal :=
    Finset.prod_mul_distrib
  rw [← hden]
  symm
  rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib]

/-- On the support of the memoryless joint law, block information density is
the sum of its single-letter information densities. -/
theorem memorylessInformationDensity_eq_blockRealSum_of_apply_ne_zero
    (P : PMF X) (W : X → PMF Y)
    (x : Xblock n X) (y : Yblock n Y)
    (hxy : memorylessJointPMF n P W (x, y) ≠ 0) :
    memorylessInformationDensity n P W (x, y) =
      blockRealSum n (singleLetterInformationDensity P W)
        (blockPairEquiv n (x, y)) := by
  have hjoint (i : Fin n) : induced_joint P W (x i, y i) ≠ 0 := by
    intro hi
    apply hxy
    rw [memorylessJointPMF_apply]
    exact Finset.prod_eq_zero (Finset.mem_univ i) hi
  have hproduct (i : Fin n) :
      product_pmf P (P.bind W) (x i, y i) ≠ 0 := by
    apply (PMF.mem_support_iff _ _).mp
    have hmem : (x i, y i) ∈ (induced_joint P W).support :=
      (PMF.mem_support_iff _ _).mpr (hjoint i)
    simpa using
      (support_joint_subset_product_marginals (induced_joint P W) hmem)
  have hratio (i : Fin n) :
      (pmfDensityRatio (induced_joint P W)
        (product_pmf P (P.bind W)) (x i, y i)).toReal ≠ 0 := by
    apply ENNReal.toReal_ne_zero.mpr
    constructor
    · unfold pmfDensityRatio
      exact mul_ne_zero (hjoint i)
        (ENNReal.inv_ne_zero.mpr
          ((product_pmf P (P.bind W)).apply_ne_top (x i, y i)))
    · unfold pmfDensityRatio
      exact ENNReal.mul_ne_top
        ((induced_joint P W).apply_ne_top (x i, y i))
        (ENNReal.inv_ne_top.mpr (hproduct i))
  rw [memorylessInformationDensity_eq,
    memorylessPmfDensityRatio_toReal_eq_prod]
  unfold blockRealSum singleLetterInformationDensity
  rw [Real.log_prod (fun i _ => hratio i)]
  simp [blockPairEquiv]

/-- Chebyshev's weak-law bound for the average information density of a
memoryless source/test-channel block. -/
theorem memorylessInformationDensity_average_deviation_le
    (hn : 0 < n) (P : PMF X) (W : X → PMF Y) (ε : ℝ) (hε : 0 < ε) :
    (∑ z : Xblock n X × Yblock n Y,
      if ε ≤ |memorylessInformationDensity n P W z / n -
          mutualInformationEntropy (induced_joint P W)| then
        memorylessJointPMF n P W z else 0) ≤
      ENNReal.ofReal
        ((pmfRealVariance (induced_joint P W)
          (singleLetterInformationDensity P W) / n) / ε ^ 2) := by
  have hsum :
      (∑ z : Xblock n X × Yblock n Y,
        if ε ≤ |memorylessInformationDensity n P W z / n -
            mutualInformationEntropy (induced_joint P W)| then
          memorylessJointPMF n P W z else 0) =
        ∑ z : Xblock n (X × Y),
          if ε ≤ |blockRealAverage n hn (singleLetterInformationDensity P W) z -
              pmfRealExpectation (induced_joint P W)
                (singleLetterInformationDensity P W)| then
            iidBlockPMF n (induced_joint P W) z else 0 := by
    apply Fintype.sum_equiv (blockPairEquiv n)
    intro z
    have hmap :
        iidBlockPMF n (induced_joint P W) (blockPairEquiv n z) =
          memorylessJointPMF n P W z := by
      rw [← memorylessJointPMF_map_blockPairEquiv, map_apply_equiv]
      simp
    by_cases hz : memorylessJointPMF n P W z = 0
    · simp [hz, hmap]
    · simp only [blockRealAverage]
      rw [memorylessInformationDensity_eq_blockRealSum_of_apply_ne_zero
        (n := n) P W z.1 z.2 hz,
        ← pmfRealExpectation_singleLetterInformationDensity, hmap]
  rw [hsum]
  exact iidBlockPMF_blockRealAverage_deviation_le (n := n) hn (induced_joint P W)
    (singleLetterInformationDensity P W) ε hε

/-- Chebyshev's weak-law bound for the real-valued block distortion under a
memoryless source/test-channel joint law. -/
theorem memorylessBlockDistortion_toReal_deviation_le
    (hn : 0 < n) (P : PMF X) (W : X → PMF Y)
    (d : Distortion (X := X) (Y := Y)) (ε : ℝ) (hε : 0 < ε) :
    (∑ z : Xblock n X × Yblock n Y,
      if ε ≤ |(blockDistortion n hn d z.1 z.2).toReal -
          (expected_distortion_single P W d).toReal| then
        memorylessJointPMF n P W z else 0) ≤
      ENNReal.ofReal
        ((pmfRealVariance (induced_joint P W)
          (fun z => (d z.1 z.2 : ℝ)) / n) / ε ^ 2) := by
  have hsum :
      (∑ z : Xblock n X × Yblock n Y,
        if ε ≤ |(blockDistortion n hn d z.1 z.2).toReal -
            (expected_distortion_single P W d).toReal| then
          memorylessJointPMF n P W z else 0) =
        ∑ z : Xblock n (X × Y),
          if ε ≤ |blockRealAverage n hn (fun z => (d z.1 z.2 : ℝ)) z -
              pmfRealExpectation (induced_joint P W)
                (fun z => (d z.1 z.2 : ℝ))| then
            iidBlockPMF n (induced_joint P W) z else 0 := by
    apply Fintype.sum_equiv (blockPairEquiv n)
    intro z
    have hmap :
        iidBlockPMF n (induced_joint P W) (blockPairEquiv n z) =
          memorylessJointPMF n P W z := by
      rw [← memorylessJointPMF_map_blockPairEquiv, map_apply_equiv]
      simp
    rw [blockDistortion_toReal_eq_blockRealAverage (n := n) hn d z.1 z.2,
      ← pmfRealExpectation_inducedJoint_distortion, hmap]
  exact hsum.trans_le
    (iidBlockPMF_blockRealAverage_deviation_le (n := n) hn (induced_joint P W)
      (fun z => (d z.1 z.2 : ℝ)) ε hε)

/-- Conditional information density of a block.  This is the likelihood ratio
between the memoryless test channel and the random-codeword distribution. -/
noncomputable def memorylessChannelInformationDensity
    (P : PMF X) (W : X → PMF Y)
    (x : Xblock n X) (y : Yblock n Y) : ℝ :=
  Real.log (pmfDensityRatio (memorylessChannelBlockPMF n W x)
    (iidBlockPMF n (P.bind W)) y).toReal

/-- On a source block of positive probability, joint and conditional
information density agree. -/
theorem memorylessInformationDensity_eq_channel
    (P : PMF X) (W : X → PMF Y)
    (x : Xblock n X) (y : Yblock n Y)
    (hx : iidBlockPMF n P x ≠ 0) :
    memorylessInformationDensity n P W (x, y) =
      memorylessChannelInformationDensity n P W x y := by
  rw [memorylessInformationDensity_eq]
  unfold memorylessChannelInformationDensity
  simp only [memorylessJointPMF, induced_joint_apply, product_pmf_apply,
    pmfDensityRatio]
  apply congrArg Real.log
  apply congrArg ENNReal.toReal
  rw [ENNReal.mul_inv (Or.inl hx)
    (Or.inl ((iidBlockPMF n P).apply_ne_top x))]
  calc
    (iidBlockPMF n P x * memorylessChannelBlockPMF n W x y) *
        ((iidBlockPMF n P x)⁻¹ * (iidBlockPMF n (P.bind W) y)⁻¹) =
      (iidBlockPMF n P x * (iidBlockPMF n P x)⁻¹) *
        (memorylessChannelBlockPMF n W x y * (iidBlockPMF n (P.bind W) y)⁻¹) := by
          ring
    _ = memorylessChannelBlockPMF n W x y * (iidBlockPMF n (P.bind W) y)⁻¹ := by
      rw [ENNReal.mul_inv_cancel hx ((iidBlockPMF n P).apply_ne_top x), one_mul]

/-- An upper bound on the log likelihood ratio yields the corresponding
exponential likelihood-ratio bound. -/
theorem pmfDensityRatio_le_exp_of_log_toReal_le
    {A : Type*} (P Q : PMF A) (a : A) (t : ℝ)
    (hP : P a ≠ 0) (hQ : Q a ≠ 0)
    (hlog : Real.log (pmfDensityRatio P Q a).toReal ≤ t) :
    pmfDensityRatio P Q a ≤ ENNReal.ofReal (Real.exp t) := by
  have hratio_top : pmfDensityRatio P Q a ≠ ⊤ := by
    unfold pmfDensityRatio
    exact ENNReal.mul_ne_top (P.apply_ne_top a) (ENNReal.inv_ne_top.mpr hQ)
  have hratio_zero : pmfDensityRatio P Q a ≠ 0 := by
    unfold pmfDensityRatio
    exact mul_ne_zero hP (ENNReal.inv_ne_zero.mpr (Q.apply_ne_top a))
  apply (ENNReal.toReal_le_toReal hratio_top ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_ofReal (Real.exp_nonneg t), ← Real.exp_log
    (ENNReal.toReal_pos hratio_zero hratio_top)]
  exact Real.exp_le_exp.mpr hlog

/-- An information-density upper bound controls the likelihood of every
positive-probability channel output relative to the random-codeword law. -/
theorem memorylessChannelBlockPMF_le_exp_mul_of_informationDensity_le
    (P : PMF X) (W : X → PMF Y)
    (x : Xblock n X) (y : Yblock n Y) (t : ℝ)
    (hx : iidBlockPMF n P x ≠ 0)
    (hinfo : memorylessChannelInformationDensity n P W x y ≤ t) :
    memorylessChannelBlockPMF n W x y ≤
      ENNReal.ofReal (Real.exp t) * iidBlockPMF n (P.bind W) y := by
  by_cases hW : memorylessChannelBlockPMF n W x y = 0
  · simp [hW]
  have hy_mem : y ∈ (iidBlockPMF n (P.bind W)).support :=
    memorylessChannelBlockPMF_support_subset_output (n := n) P W x hx
      ((PMF.mem_support_iff _ _).mpr hW)
  have hQ : iidBlockPMF n (P.bind W) y ≠ 0 :=
    (PMF.mem_support_iff _ _).mp hy_mem
  have hratio :
      pmfDensityRatio (memorylessChannelBlockPMF n W x)
        (iidBlockPMF n (P.bind W)) y ≤ ENNReal.ofReal (Real.exp t) :=
    pmfDensityRatio_le_exp_of_log_toReal_le
      (memorylessChannelBlockPMF n W x) (iidBlockPMF n (P.bind W)) y t hW hQ
        (by simpa [memorylessChannelInformationDensity] using hinfo)
  have hmul := mul_le_mul_left hratio (iidBlockPMF n (P.bind W) y)
  simpa only [pmfDensityRatio,
    ENNReal.inv_mul_cancel_right hQ ((iidBlockPMF n (P.bind W)).apply_ne_top y)]
    using hmul

theorem sum_memorylessInformationDensity
    (P : PMF X) (W : X → PMF Y) :
    (∑ z : Xblock n X × Yblock n Y,
      (memorylessJointPMF n P W z).toReal *
        memorylessInformationDensity n P W z) =
      (n : ℝ) * mutualInformationEntropy (induced_joint P W) := by
  unfold memorylessInformationDensity
  rw [sum_weighted_log_densityRatio_product_marginals]
  exact mutualInformationEntropy_memorylessJointPMF n P W

/-- The good-pair predicate used by random rate-distortion coding.  A pair is
good when it meets both the block-distortion budget and the information-density
budget used for covering. -/
noncomputable def goodBlockPair
    (hn : 0 < n) (P : PMF X) (W : X → PMF Y)
    (d : Distortion (X := X) (Y := Y))
    (distortionThreshold : ENNReal) (informationThreshold : ℝ)
    (x : Xblock n X) (y : Yblock n Y) : Prop :=
  blockDistortion n hn d x y ≤ distortionThreshold ∧
    memorylessInformationDensity n P W (x, y) ≤ informationThreshold

/-- Probability of the good-pair event under the memoryless test-channel joint
law. -/
noncomputable def goodBlockPairProbability
    (hn : 0 < n) (P : PMF X) (W : X → PMF Y)
    (d : Distortion (X := X) (Y := Y))
    (distortionThreshold : ENNReal) (informationThreshold : ℝ) : ENNReal := by
  classical
  exact codewordHitProbability (memorylessJointPMF n P W)
    (fun z => goodBlockPair n hn P W d distortionThreshold informationThreshold z.1 z.2)

/-- Conditional probability of the good output set for a fixed source block
under the memoryless test channel. -/
noncomputable def conditionalGoodBlockPairProbability
    (hn : 0 < n) (P : PMF X) (W : X → PMF Y)
    (d : Distortion (X := X) (Y := Y))
    (distortionThreshold : ENNReal) (informationThreshold : ℝ)
    (x : Xblock n X) : ENNReal := by
  classical
  exact codewordHitProbability (memorylessChannelBlockPMF n W x)
    (goodBlockPair n hn P W d distortionThreshold informationThreshold x)

theorem conditionalGoodBlockPairProbability_le_one
    (hn : 0 < n) (P : PMF X) (W : X → PMF Y)
    (d : Distortion (X := X) (Y := Y))
    (distortionThreshold : ENNReal) (informationThreshold : ℝ)
    (x : Xblock n X) :
    conditionalGoodBlockPairProbability n hn P W d distortionThreshold informationThreshold x ≤ 1 := by
  classical
  unfold conditionalGoodBlockPairProbability
  exact codewordHitProbability_le_one _ _

/-- The good-pair probability is the source average of conditional good-set
probabilities for the test channel. -/
theorem goodBlockPairProbability_eq_sum_conditional
    (hn : 0 < n) (P : PMF X) (W : X → PMF Y)
    (d : Distortion (X := X) (Y := Y))
    (distortionThreshold : ENNReal) (informationThreshold : ℝ) :
    goodBlockPairProbability n hn P W d distortionThreshold informationThreshold =
      ∑ x : Xblock n X, iidBlockPMF n P x *
        conditionalGoodBlockPairProbability n hn P W d distortionThreshold informationThreshold x := by
  classical
  unfold goodBlockPairProbability conditionalGoodBlockPairProbability codewordHitProbability
  rw [Fintype.sum_prod_type]
  simp only [memorylessJointPMF, induced_joint_apply]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  by_cases hgood : goodBlockPair n hn P W d distortionThreshold informationThreshold x y <;>
    simp [hgood]

/-- If the joint good-pair event has probability at least `1 - δ`, then all
but at most `2δ` of source blocks have conditional good-pair probability at
least one half. -/
theorem one_sub_two_mul_le_sourceHalfConditionalGoodProbability
    (hn : 0 < n) (P : PMF X) (W : X → PMF Y)
    (d : Distortion (X := X) (Y := Y))
    (distortionThreshold : ENNReal) (informationThreshold : ℝ)
    (δ : ENNReal) (hδ : δ ≤ 1)
    (hgood : 1 - δ ≤
      goodBlockPairProbability n hn P W d distortionThreshold informationThreshold) :
    1 - 2 * δ ≤
      codewordHitProbability (iidBlockPMF n P)
        (fun x => 1 / 2 ≤
          conditionalGoodBlockPairProbability n hn P W d distortionThreshold informationThreshold x) := by
  apply one_sub_two_mul_le_hitProbability_half_of_weighted
    (iidBlockPMF n P)
    (conditionalGoodBlockPairProbability n hn P W d distortionThreshold informationThreshold)
    δ
    (conditionalGoodBlockPairProbability_le_one (n := n) hn P W d
      distortionThreshold informationThreshold)
    hδ
  rw [← goodBlockPairProbability_eq_sum_conditional]
  exact hgood

/-- If adding one quarter to a quantity reaches one half, that quantity is at
least one quarter. -/
theorem ENNReal.quarter_le_of_half_le_add_quarter
    (p : ENNReal) (h : 1 / 2 ≤ p + 1 / 4) :
    1 / 4 ≤ p := by
  by_contra hp
  have hplt : p < 1 / 4 := lt_of_not_ge hp
  have hquarterTop : (1 / 4 : ENNReal) ≠ ⊤ :=
    ENNReal.div_ne_top ENNReal.one_ne_top (by norm_num)
  have hsumlt : p + 1 / 4 < (1 / 4 : ENNReal) + 1 / 4 :=
    ENNReal.add_lt_add_right hquarterTop hplt
  have hlt : p + 1 / 4 < 1 / 2 := by
    calc
      p + 1 / 4 < (1 / 4 : ENNReal) + 1 / 4 := hsumlt
      _ = 1 / 2 := by
        have hadd : (1 / 4 : ENNReal) + 1 / 4 = (1 + 1) / 4 :=
          ENNReal.div_add_div_same
        rw [hadd]
        have hfrac : (2 : ENNReal) / 4 = 1 / 2 := by
          apply (ENNReal.div_eq_div_iff (by norm_num) (by norm_num)
            (by norm_num) (by norm_num)).mpr
          norm_num
        convert hfrac using 1 <;> norm_num
  exact (not_lt_of_ge h) hlt

/-- A joint good-pair probability of at least one half implies that source
blocks whose conditional good-set probability is at least one quarter have
source probability at least one quarter. -/
theorem quarter_le_sourceHighConditionalGoodProbability
    (hn : 0 < n) (P : PMF X) (W : X → PMF Y)
    (d : Distortion (X := X) (Y := Y))
    (distortionThreshold : ENNReal) (informationThreshold : ℝ)
    (hgood : 1 / 2 ≤
      goodBlockPairProbability n hn P W d distortionThreshold informationThreshold) :
    1 / 4 ≤ codewordHitProbability (iidBlockPMF n P)
      (fun x => 1 / 4 ≤
        conditionalGoodBlockPairProbability n hn P W d distortionThreshold informationThreshold x) := by
  classical
  have hmean := weighted_pmf_le_hitProbability_add_threshold
    (iidBlockPMF n P)
    (conditionalGoodBlockPairProbability n hn P W d distortionThreshold informationThreshold)
    (1 / 4 : ENNReal)
    (conditionalGoodBlockPairProbability_le_one (n := n) hn P W d
      distortionThreshold informationThreshold)
  have hhalfAverage := hgood
  rw [goodBlockPairProbability_eq_sum_conditional] at hhalfAverage
  exact ENNReal.quarter_le_of_half_le_add_quarter _ (hhalfAverage.trans hmean)

theorem goodBlockPair_distortion
    (hn : 0 < n) (P : PMF X) (W : X → PMF Y)
    (d : Distortion (X := X) (Y := Y))
    (distortionThreshold : ENNReal) (informationThreshold : ℝ)
    (x : Xblock n X) (y : Yblock n Y)
    (hgood : goodBlockPair n hn P W d distortionThreshold informationThreshold x y) :
    blockDistortion n hn d x y ≤ distortionThreshold := hgood.1

theorem goodBlockPair_informationDensity
    (hn : 0 < n) (P : PMF X) (W : X → PMF Y)
    (d : Distortion (X := X) (Y := Y))
    (distortionThreshold : ENNReal) (informationThreshold : ℝ)
    (x : Xblock n X) (y : Yblock n Y)
    (hgood : goodBlockPair n hn P W d distortionThreshold informationThreshold x y) :
    memorylessInformationDensity n P W (x, y) ≤ informationThreshold := hgood.2

/-- If the distortion and information thresholds exceed their respective
single-letter means by the stated slacks, the good-pair probability plus the
two corresponding deviation probabilities is at least one. -/
theorem one_le_goodBlockPairProbability_add_deviationProbabilities
    (hn : 0 < n) (P : PMF X) (W : X → PMF Y)
    (d : Distortion (X := X) (Y := Y))
    (distortionThreshold : ENNReal) (informationThreshold εd εi : ℝ)
    (hdistortionThreshold : distortionThreshold ≠ ⊤)
    (hdistortionSlack : (expected_distortion_single P W d).toReal + εd ≤
      distortionThreshold.toReal)
    (hinformationSlack : (n : ℝ) *
        (mutualInformationEntropy (induced_joint P W) + εi) ≤ informationThreshold) :
    1 ≤
      goodBlockPairProbability n hn P W d distortionThreshold informationThreshold +
        codewordHitProbability (memorylessJointPMF n P W)
          (fun z => εd ≤ |(blockDistortion n hn d z.1 z.2).toReal -
            (expected_distortion_single P W d).toReal|) +
        codewordHitProbability (memorylessJointPMF n P W)
          (fun z => εi ≤ |memorylessInformationDensity n P W z / n -
            mutualInformationEntropy (induced_joint P W)|) := by
  classical
  have hbase := one_le_codewordHitProbability_and_add_not
    (memorylessJointPMF n P W)
    (fun z => blockDistortion n hn d z.1 z.2 ≤ distortionThreshold)
    (fun z => memorylessInformationDensity n P W z ≤ informationThreshold)
  have hbase' :
      1 ≤
        goodBlockPairProbability n hn P W d distortionThreshold informationThreshold +
          codewordHitProbability (memorylessJointPMF n P W)
            (fun z => ¬ blockDistortion n hn d z.1 z.2 ≤ distortionThreshold) +
          codewordHitProbability (memorylessJointPMF n P W)
            (fun z => ¬ memorylessInformationDensity n P W z ≤ informationThreshold) := by
    simpa [goodBlockPairProbability, goodBlockPair] using hbase
  have hbadDistortion :
      codewordHitProbability (memorylessJointPMF n P W)
          (fun z => ¬ blockDistortion n hn d z.1 z.2 ≤ distortionThreshold) ≤
        codewordHitProbability (memorylessJointPMF n P W)
          (fun z => εd ≤ |(blockDistortion n hn d z.1 z.2).toReal -
            (expected_distortion_single P W d).toReal|) := by
    apply codewordHitProbability_mono
    intro z hz
    have hblockTop : blockDistortion n hn d z.1 z.2 ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.coe_ne_top
        (blockDistortion_le_bound (n := n) hn d z.1 z.2)
    have hlt : distortionThreshold < blockDistortion n hn d z.1 z.2 :=
      lt_of_not_ge hz
    have hreal : distortionThreshold.toReal <
        (blockDistortion n hn d z.1 z.2).toReal :=
      (ENNReal.toReal_lt_toReal hdistortionThreshold hblockTop).mpr hlt
    have hdiff : εd < (blockDistortion n hn d z.1 z.2).toReal -
        (expected_distortion_single P W d).toReal := by
      linarith
    exact (le_of_lt hdiff).trans (le_abs_self _)
  have hbadInformation :
      codewordHitProbability (memorylessJointPMF n P W)
          (fun z => ¬ memorylessInformationDensity n P W z ≤ informationThreshold) ≤
        codewordHitProbability (memorylessJointPMF n P W)
          (fun z => εi ≤ |memorylessInformationDensity n P W z / n -
            mutualInformationEntropy (induced_joint P W)|) := by
    apply codewordHitProbability_mono
    intro z hz
    have hlt : informationThreshold < memorylessInformationDensity n P W z :=
      lt_of_not_ge hz
    have hnReal : 0 < (n : ℝ) := by exact_mod_cast hn
    have hscaled : (n : ℝ) *
        (mutualInformationEntropy (induced_joint P W) + εi) <
          memorylessInformationDensity n P W z :=
      lt_of_le_of_lt hinformationSlack hlt
    have havg : mutualInformationEntropy (induced_joint P W) + εi <
        memorylessInformationDensity n P W z / n := by
      apply (lt_div_iff₀ hnReal).mpr
      simpa [mul_comm] using hscaled
    have hdiff : εi < memorylessInformationDensity n P W z / n -
        mutualInformationEntropy (induced_joint P W) := by
      linarith
    exact (le_of_lt hdiff).trans (le_abs_self _)
  calc
    1 ≤
        (goodBlockPairProbability n hn P W d distortionThreshold informationThreshold +
          codewordHitProbability (memorylessJointPMF n P W)
            (fun z => ¬ blockDistortion n hn d z.1 z.2 ≤ distortionThreshold)) +
          codewordHitProbability (memorylessJointPMF n P W)
            (fun z => ¬ memorylessInformationDensity n P W z ≤ informationThreshold) := hbase'
    _ =
        goodBlockPairProbability n hn P W d distortionThreshold informationThreshold +
          (codewordHitProbability (memorylessJointPMF n P W)
            (fun z => ¬ blockDistortion n hn d z.1 z.2 ≤ distortionThreshold) +
          codewordHitProbability (memorylessJointPMF n P W)
            (fun z => ¬ memorylessInformationDensity n P W z ≤ informationThreshold)) := by
          ac_rfl
    _ ≤
        goodBlockPairProbability n hn P W d distortionThreshold informationThreshold +
          (codewordHitProbability (memorylessJointPMF n P W)
            (fun z => εd ≤ |(blockDistortion n hn d z.1 z.2).toReal -
              (expected_distortion_single P W d).toReal|) +
          codewordHitProbability (memorylessJointPMF n P W)
            (fun z => εi ≤ |memorylessInformationDensity n P W z / n -
              mutualInformationEntropy (induced_joint P W)|)) :=
          add_le_add_right (add_le_add hbadDistortion hbadInformation) _
    _ =
        (goodBlockPairProbability n hn P W d distortionThreshold informationThreshold +
          codewordHitProbability (memorylessJointPMF n P W)
            (fun z => εd ≤ |(blockDistortion n hn d z.1 z.2).toReal -
              (expected_distortion_single P W d).toReal|)) +
          codewordHitProbability (memorylessJointPMF n P W)
            (fun z => εi ≤ |memorylessInformationDensity n P W z / n -
              mutualInformationEntropy (induced_joint P W)|) := by
          ac_rfl

/-- An explicit finite-block lower bound for the good-pair probability,
obtained by combining the two Chebyshev bounds with the union estimate. -/
theorem one_le_goodBlockPairProbability_add_chebyshevBounds
    (hn : 0 < n) (P : PMF X) (W : X → PMF Y)
    (d : Distortion (X := X) (Y := Y))
    (distortionThreshold : ENNReal) (informationThreshold εd εi : ℝ)
    (hεd : 0 < εd) (hεi : 0 < εi)
    (hdistortionThreshold : distortionThreshold ≠ ⊤)
    (hdistortionSlack : (expected_distortion_single P W d).toReal + εd ≤
      distortionThreshold.toReal)
    (hinformationSlack : (n : ℝ) *
        (mutualInformationEntropy (induced_joint P W) + εi) ≤ informationThreshold) :
    1 ≤
      goodBlockPairProbability n hn P W d distortionThreshold informationThreshold +
        ENNReal.ofReal
          ((pmfRealVariance (induced_joint P W)
            (fun z => (d z.1 z.2 : ℝ)) / n) / εd ^ 2) +
        ENNReal.ofReal
          ((pmfRealVariance (induced_joint P W)
            (singleLetterInformationDensity P W) / n) / εi ^ 2) := by
  have hbase := one_le_goodBlockPairProbability_add_deviationProbabilities
    (n := n) hn P W d distortionThreshold informationThreshold εd εi
    hdistortionThreshold hdistortionSlack hinformationSlack
  have hdistortion := memorylessBlockDistortion_toReal_deviation_le
    (n := n) hn P W d εd hεd
  change codewordHitProbability (memorylessJointPMF n P W)
      (fun z => εd ≤ |(blockDistortion n hn d z.1 z.2).toReal -
        (expected_distortion_single P W d).toReal|) ≤ _ at hdistortion
  have hinformation := memorylessInformationDensity_average_deviation_le
    (n := n) hn P W εi hεi
  change codewordHitProbability (memorylessJointPMF n P W)
      (fun z => εi ≤ |memorylessInformationDensity n P W z / n -
        mutualInformationEntropy (induced_joint P W)|) ≤ _ at hinformation
  exact hbase.trans
    (add_le_add (add_le_add_right hdistortion _) hinformation)

/-- If two nonnegative error terms total at most one half, any quantity whose
sum with them is at least one is itself at least one half. -/
theorem ENNReal.half_le_of_one_le_add_add
    (p a b : ENNReal) (hone : 1 ≤ p + a + b)
    (herrors : a + b ≤ 1 / 2) :
    1 / 2 ≤ p := by
  by_contra hp
  have hplt : p < 1 / 2 := lt_of_not_ge hp
  have hhalfTop : (1 / 2 : ENNReal) ≠ ⊤ :=
    ENNReal.div_ne_top ENNReal.one_ne_top (by norm_num)
  have habTop : a + b ≠ ⊤ :=
    ne_top_of_le_ne_top hhalfTop herrors
  have hsumlt : p + (a + b) < (1 / 2 : ENNReal) + 1 / 2 :=
    (ENNReal.add_lt_add_right habTop hplt).trans_le
      (add_le_add_right herrors (1 / 2 : ENNReal))
  have hlt : p + a + b < 1 := by
    calc
      p + a + b = p + (a + b) := by ac_rfl
      _ < (1 / 2 : ENNReal) + 1 / 2 := hsumlt
      _ = 1 := by simpa using ENNReal.inv_two_add_inv_two
  exact (not_lt_of_ge hone) hlt

/-- If a probability plus an error is at least one and the error is bounded by
`δ`, then the probability is at least `1 - δ`. -/
theorem ENNReal.one_sub_le_of_one_le_add
    (p e δ : ENNReal) (hone : 1 ≤ p + e) (he : e ≤ δ) :
    1 - δ ≤ p := by
  rw [tsub_le_iff_right]
  calc
    1 ≤ p + e := hone
    _ = e + p := add_comm _ _
    _ ≤ δ + p := add_le_add_left he p
    _ = p + δ := add_comm _ _

/-- Every fixed real Chebyshev coefficient is at most one quarter after a
sufficiently large positive natural blocklength. -/
theorem exists_nat_chebyshevError_le_quarter
    (V ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n →
      ENNReal.ofReal ((V / n) / ε ^ 2) ≤ 1 / 4 := by
  obtain ⟨N, hN⟩ := exists_nat_gt (max (1 : ℝ) (4 * V / ε ^ 2))
  refine ⟨N, ?_, ?_⟩
  · have hNone : (1 : ℝ) < N := (lt_of_le_of_lt (le_max_left _ _) hN)
    have hNoneNat : 1 < N := by exact_mod_cast hNone
    exact Nat.zero_lt_one.trans hNoneNat
  intro n hn
  have hNn : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hlarge : 4 * V / ε ^ 2 < (n : ℝ) :=
    (lt_of_le_of_lt (le_max_right _ _) hN).trans_le hNn
  have hnpositive : 0 < (n : ℝ) := by
    have : (1 : ℝ) < n :=
      (lt_of_le_of_lt (le_max_left _ _) hN).trans_le hNn
    linarith
  have hεsq : 0 < ε ^ 2 := sq_pos_of_pos hε
  have hscaled : 4 * V < (n : ℝ) * ε ^ 2 :=
    (div_lt_iff₀ hεsq).mp hlarge
  have hden : 0 < (n : ℝ) * ε ^ 2 := mul_pos hnpositive hεsq
  have hreal : (V / n) / ε ^ 2 ≤ (1 : ℝ) / 4 := by
    rw [div_div]
    apply (div_le_iff₀ hden).mpr
    nlinarith
  calc
    ENNReal.ofReal ((V / n) / ε ^ 2) ≤ ENNReal.ofReal ((1 : ℝ) / 4) :=
      ENNReal.ofReal_mono hreal
    _ = 1 / 4 := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_one]
      norm_num

/-- Every fixed real Chebyshev coefficient eventually lies below any prescribed
positive real tolerance. -/
theorem exists_nat_chebyshevError_le
    (V ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n →
      ENNReal.ofReal ((V / n) / ε ^ 2) ≤ ENNReal.ofReal δ := by
  obtain ⟨N, hN⟩ := exists_nat_gt (max (1 : ℝ) (V / (δ * ε ^ 2)))
  refine ⟨N, ?_, ?_⟩
  · have hNone : (1 : ℝ) < N := (lt_of_le_of_lt (le_max_left _ _) hN)
    have hNoneNat : 1 < N := by exact_mod_cast hNone
    exact Nat.zero_lt_one.trans hNoneNat
  intro n hn
  have hNn : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hlarge : V / (δ * ε ^ 2) < (n : ℝ) :=
    (lt_of_le_of_lt (le_max_right _ _) hN).trans_le hNn
  have hnpositive : 0 < (n : ℝ) := by
    have : (1 : ℝ) < n :=
      (lt_of_le_of_lt (le_max_left _ _) hN).trans_le hNn
    linarith
  have hεsq : 0 < ε ^ 2 := sq_pos_of_pos hε
  have hδεsq : 0 < δ * ε ^ 2 := mul_pos hδ hεsq
  have hscaled : V < (n : ℝ) * (δ * ε ^ 2) :=
    (div_lt_iff₀ hδεsq).mp hlarge
  have hden : 0 < (n : ℝ) * ε ^ 2 := mul_pos hnpositive hεsq
  have hreal : (V / n) / ε ^ 2 ≤ δ := by
    rw [div_div]
    apply (div_le_iff₀ hden).mpr
    nlinarith
  exact ENNReal.ofReal_mono hreal

/-- The sum of two fixed Chebyshev error terms is at most one half after a
sufficiently large positive blocklength. -/
theorem exists_nat_chebyshevErrorSum_le_half
    (V₁ ε₁ V₂ ε₂ : ℝ) (hε₁ : 0 < ε₁) (hε₂ : 0 < ε₂) :
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n →
      ENNReal.ofReal ((V₁ / n) / ε₁ ^ 2) +
        ENNReal.ofReal ((V₂ / n) / ε₂ ^ 2) ≤ 1 / 2 := by
  obtain ⟨N₁, hN₁pos, hN₁⟩ := exists_nat_chebyshevError_le_quarter V₁ ε₁ hε₁
  obtain ⟨N₂, hN₂pos, hN₂⟩ := exists_nat_chebyshevError_le_quarter V₂ ε₂ hε₂
  refine ⟨max N₁ N₂, lt_of_lt_of_le hN₁pos (Nat.le_max_left _ _), ?_⟩
  intro n hn
  have h₁ : ENNReal.ofReal ((V₁ / n) / ε₁ ^ 2) ≤ 1 / 4 :=
    hN₁ n (le_trans (Nat.le_max_left _ _) hn)
  have h₂ : ENNReal.ofReal ((V₂ / n) / ε₂ ^ 2) ≤ 1 / 4 :=
    hN₂ n (le_trans (Nat.le_max_right _ _) hn)
  calc
    ENNReal.ofReal ((V₁ / n) / ε₁ ^ 2) +
        ENNReal.ofReal ((V₂ / n) / ε₂ ^ 2) ≤
          (1 / 4 : ENNReal) + 1 / 4 := add_le_add h₁ h₂
    _ = 1 / 2 := by
      have hadd : (1 / 4 : ENNReal) + 1 / 4 = (1 + 1) / 4 :=
        ENNReal.div_add_div_same
      rw [hadd]
      have hfrac : (2 : ENNReal) / 4 = 1 / 2 := by
        apply (ENNReal.div_eq_div_iff (by norm_num) (by norm_num)
          (by norm_num) (by norm_num)).mpr
        norm_num
      convert hfrac using 1 <;> norm_num

/-- The sum of two fixed Chebyshev coefficients eventually lies below any
prescribed positive real tolerance. -/
theorem exists_nat_chebyshevErrorSum_le
    (V₁ ε₁ V₂ ε₂ δ : ℝ) (hε₁ : 0 < ε₁) (hε₂ : 0 < ε₂) (hδ : 0 < δ) :
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n →
      ENNReal.ofReal ((V₁ / n) / ε₁ ^ 2) +
        ENNReal.ofReal ((V₂ / n) / ε₂ ^ 2) ≤ ENNReal.ofReal δ := by
  have hhalfδ : 0 < δ / 2 := div_pos hδ (by norm_num)
  obtain ⟨N₁, hN₁pos, hN₁⟩ :=
    exists_nat_chebyshevError_le V₁ ε₁ (δ / 2) hε₁ hhalfδ
  obtain ⟨N₂, hN₂pos, hN₂⟩ :=
    exists_nat_chebyshevError_le V₂ ε₂ (δ / 2) hε₂ hhalfδ
  refine ⟨max N₁ N₂, lt_of_lt_of_le hN₁pos (Nat.le_max_left _ _), ?_⟩
  intro n hn
  have h₁ : ENNReal.ofReal ((V₁ / n) / ε₁ ^ 2) ≤ ENNReal.ofReal (δ / 2) :=
    hN₁ n (le_trans (Nat.le_max_left _ _) hn)
  have h₂ : ENNReal.ofReal ((V₂ / n) / ε₂ ^ 2) ≤ ENNReal.ofReal (δ / 2) :=
    hN₂ n (le_trans (Nat.le_max_right _ _) hn)
  calc
    ENNReal.ofReal ((V₁ / n) / ε₁ ^ 2) +
        ENNReal.ofReal ((V₂ / n) / ε₂ ^ 2) ≤
          ENNReal.ofReal (δ / 2) + ENNReal.ofReal (δ / 2) := add_le_add h₁ h₂
    _ = ENNReal.ofReal δ := by
      rw [← ENNReal.ofReal_add hhalfδ.le hhalfδ.le]
      congr 1
      ring

/-- A Chebyshev-error bound of at most one half gives a uniform positive
lower bound on the good-pair probability. -/
theorem half_le_goodBlockPairProbability_of_chebyshevError_le
    (hn : 0 < n) (P : PMF X) (W : X → PMF Y)
    (d : Distortion (X := X) (Y := Y))
    (distortionThreshold : ENNReal) (informationThreshold εd εi : ℝ)
    (hεd : 0 < εd) (hεi : 0 < εi)
    (hdistortionThreshold : distortionThreshold ≠ ⊤)
    (hdistortionSlack : (expected_distortion_single P W d).toReal + εd ≤
      distortionThreshold.toReal)
    (hinformationSlack : (n : ℝ) *
        (mutualInformationEntropy (induced_joint P W) + εi) ≤ informationThreshold)
    (herrors :
      ENNReal.ofReal
          ((pmfRealVariance (induced_joint P W)
            (fun z => (d z.1 z.2 : ℝ)) / n) / εd ^ 2) +
        ENNReal.ofReal
          ((pmfRealVariance (induced_joint P W)
            (singleLetterInformationDensity P W) / n) / εi ^ 2) ≤ 1 / 2) :
    1 / 2 ≤
      goodBlockPairProbability n hn P W d distortionThreshold informationThreshold := by
  exact ENNReal.half_le_of_one_le_add_add _ _ _
    (one_le_goodBlockPairProbability_add_chebyshevBounds
      (n := n) hn P W d distortionThreshold informationThreshold εd εi hεd hεi
      hdistortionThreshold hdistortionSlack hinformationSlack)
    herrors

/-- A Chebyshev-error bound by `δ` makes the good-pair probability at least
`1 - δ`. -/
theorem one_sub_le_goodBlockPairProbability_of_chebyshevError_le
    (hn : 0 < n) (P : PMF X) (W : X → PMF Y)
    (d : Distortion (X := X) (Y := Y))
    (distortionThreshold : ENNReal) (informationThreshold εd εi : ℝ)
    (hεd : 0 < εd) (hεi : 0 < εi)
    (hdistortionThreshold : distortionThreshold ≠ ⊤)
    (hdistortionSlack : (expected_distortion_single P W d).toReal + εd ≤
      distortionThreshold.toReal)
    (hinformationSlack : (n : ℝ) *
        (mutualInformationEntropy (induced_joint P W) + εi) ≤ informationThreshold)
    (δ : ENNReal)
    (herrors :
      ENNReal.ofReal
          ((pmfRealVariance (induced_joint P W)
            (fun z => (d z.1 z.2 : ℝ)) / n) / εd ^ 2) +
        ENNReal.ofReal
          ((pmfRealVariance (induced_joint P W)
            (singleLetterInformationDensity P W) / n) / εi ^ 2) ≤ δ) :
    1 - δ ≤
      goodBlockPairProbability n hn P W d distortionThreshold informationThreshold := by
  apply ENNReal.one_sub_le_of_one_le_add _ (_ + _) δ ?_ herrors
  calc
    1 ≤
        goodBlockPairProbability n hn P W d distortionThreshold informationThreshold +
          ENNReal.ofReal
            ((pmfRealVariance (induced_joint P W)
              (fun z => (d z.1 z.2 : ℝ)) / n) / εd ^ 2) +
          ENNReal.ofReal
            ((pmfRealVariance (induced_joint P W)
              (singleLetterInformationDensity P W) / n) / εi ^ 2) :=
      one_le_goodBlockPairProbability_add_chebyshevBounds
        (n := n) hn P W d distortionThreshold informationThreshold εd εi hεd hεi
        hdistortionThreshold hdistortionSlack hinformationSlack
    _ =
        goodBlockPairProbability n hn P W d distortionThreshold informationThreshold +
          (ENNReal.ofReal
            ((pmfRealVariance (induced_joint P W)
              (fun z => (d z.1 z.2 : ℝ)) / n) / εd ^ 2) +
          ENNReal.ofReal
            ((pmfRealVariance (induced_joint P W)
              (singleLetterInformationDensity P W) / n) / εi ^ 2)) := by
      ac_rfl

/-- For fixed positive slacks, the good-pair probability is at least one half
at every sufficiently large blocklength. -/
theorem exists_nat_half_le_goodBlockPairProbability
    (P : PMF X) (W : X → PMF Y)
    (d : Distortion (X := X) (Y := Y))
    (distortionThreshold : ENNReal) (informationThreshold : ℕ → ℝ)
    (εd εi : ℝ) (hεd : 0 < εd) (hεi : 0 < εi)
    (hdistortionThreshold : distortionThreshold ≠ ⊤)
    (hdistortionSlack : (expected_distortion_single P W d).toReal + εd ≤
      distortionThreshold.toReal)
    (hinformationSlack : ∀ n : ℕ, (n : ℝ) *
        (mutualInformationEntropy (induced_joint P W) + εi) ≤ informationThreshold n) :
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n → ∀ hn : 0 < n,
      1 / 2 ≤
        goodBlockPairProbability n hn P W d distortionThreshold (informationThreshold n) := by
  obtain ⟨N, hNpos, herrors⟩ := exists_nat_chebyshevErrorSum_le_half
    (pmfRealVariance (induced_joint P W) (fun z => (d z.1 z.2 : ℝ))) εd
    (pmfRealVariance (induced_joint P W) (singleLetterInformationDensity P W)) εi
    hεd hεi
  refine ⟨N, hNpos, ?_⟩
  intro n hnN hn
  apply half_le_goodBlockPairProbability_of_chebyshevError_le (n := n)
    hn P W d distortionThreshold (informationThreshold n) εd εi hεd hεi
    hdistortionThreshold hdistortionSlack (hinformationSlack n)
  exact herrors n hnN

/-- For every positive error tolerance, fixed positive slacks make the
good-pair probability at least `1 - δ` at every sufficiently large blocklength. -/
theorem exists_nat_one_sub_le_goodBlockPairProbability
    (P : PMF X) (W : X → PMF Y)
    (d : Distortion (X := X) (Y := Y))
    (distortionThreshold : ENNReal) (informationThreshold : ℕ → ℝ)
    (εd εi δ : ℝ) (hεd : 0 < εd) (hεi : 0 < εi)
    (hδ : 0 < δ)
    (hdistortionThreshold : distortionThreshold ≠ ⊤)
    (hdistortionSlack : (expected_distortion_single P W d).toReal + εd ≤
      distortionThreshold.toReal)
    (hinformationSlack : ∀ n : ℕ, (n : ℝ) *
        (mutualInformationEntropy (induced_joint P W) + εi) ≤ informationThreshold n) :
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n → ∀ hn : 0 < n,
      1 - ENNReal.ofReal δ ≤
        goodBlockPairProbability n hn P W d distortionThreshold (informationThreshold n) := by
  obtain ⟨N, hNpos, herrors⟩ := exists_nat_chebyshevErrorSum_le
    (pmfRealVariance (induced_joint P W) (fun z => (d z.1 z.2 : ℝ))) εd
    (pmfRealVariance (induced_joint P W) (singleLetterInformationDensity P W)) εi δ
    hεd hεi hδ
  refine ⟨N, hNpos, ?_⟩
  intro n hnN hn
  apply one_sub_le_goodBlockPairProbability_of_chebyshevError_le (n := n)
    hn P W d distortionThreshold (informationThreshold n) εd εi hεd hεi
    hdistortionThreshold hdistortionSlack (hinformationSlack n) (ENNReal.ofReal δ)
  exact herrors n hnN

/-- On a positive-probability source block, a good pair also satisfies the
conditional information-density bound needed for random covering. -/
theorem goodBlockPair_channelInformationDensity
    (hn : 0 < n) (P : PMF X) (W : X → PMF Y)
    (d : Distortion (X := X) (Y := Y))
    (distortionThreshold : ENNReal) (informationThreshold : ℝ)
    (x : Xblock n X) (y : Yblock n Y)
    (hx : iidBlockPMF n P x ≠ 0)
    (hgood : goodBlockPair n hn P W d distortionThreshold informationThreshold x y) :
    memorylessChannelInformationDensity n P W x y ≤ informationThreshold := by
  rw [← memorylessInformationDensity_eq_channel (n := n) P W x y hx]
  exact hgood.2

/-- A good pair has channel likelihood at most `exp informationThreshold`
times its random-codeword likelihood. -/
theorem memorylessChannelBlockPMF_le_exp_mul_of_goodBlockPair
    (hn : 0 < n) (P : PMF X) (W : X → PMF Y)
    (d : Distortion (X := X) (Y := Y))
    (distortionThreshold : ENNReal) (informationThreshold : ℝ)
    (x : Xblock n X) (y : Yblock n Y)
    (hx : iidBlockPMF n P x ≠ 0)
    (hgood : goodBlockPair n hn P W d distortionThreshold informationThreshold x y) :
    memorylessChannelBlockPMF n W x y ≤
      ENNReal.ofReal (Real.exp informationThreshold) *
        iidBlockPMF n (P.bind W) y := by
  apply memorylessChannelBlockPMF_le_exp_mul_of_informationDensity_le (n := n) P W x y
    informationThreshold hx
  exact goodBlockPair_channelInformationDensity (n := n) hn P W d distortionThreshold
    informationThreshold x y hx hgood

/-- The test-channel probability of the good output set is controlled by the
random-codeword probability of that set. -/
theorem channelGoodBlockPairHitProbability_le_exp_mul
    (hn : 0 < n) (P : PMF X) (W : X → PMF Y)
    (d : Distortion (X := X) (Y := Y))
    (distortionThreshold : ENNReal) (informationThreshold : ℝ)
    (x : Xblock n X) (hx : iidBlockPMF n P x ≠ 0)
    [DecidablePred
      (goodBlockPair n hn P W d distortionThreshold informationThreshold x)] :
    codewordHitProbability (memorylessChannelBlockPMF n W x)
      (goodBlockPair n hn P W d distortionThreshold informationThreshold x) ≤
      ENNReal.ofReal (Real.exp informationThreshold) *
        codewordHitProbability (iidBlockPMF n (P.bind W))
          (goodBlockPair n hn P W d distortionThreshold informationThreshold x) := by
  apply codewordHitProbability_le_mul
  intro y hgood
  exact memorylessChannelBlockPMF_le_exp_mul_of_goodBlockPair (n := n) hn P W d
    distortionThreshold informationThreshold x y hx hgood

/-- The random-codeword hit probability is at least the test-channel good-set
probability divided by the information-density exponential factor. -/
theorem inv_mul_channelGoodBlockPairHitProbability_le
    (hn : 0 < n) (P : PMF X) (W : X → PMF Y)
    (d : Distortion (X := X) (Y := Y))
    (distortionThreshold : ENNReal) (informationThreshold : ℝ)
    (x : Xblock n X) (hx : iidBlockPMF n P x ≠ 0)
    [DecidablePred
      (goodBlockPair n hn P W d distortionThreshold informationThreshold x)] :
    (ENNReal.ofReal (Real.exp informationThreshold))⁻¹ *
        codewordHitProbability (memorylessChannelBlockPMF n W x)
          (goodBlockPair n hn P W d distortionThreshold informationThreshold x) ≤
      codewordHitProbability (iidBlockPMF n (P.bind W))
        (goodBlockPair n hn P W d distortionThreshold informationThreshold x) := by
  apply (ENNReal.inv_mul_le_iff
    (ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos informationThreshold))
    ENNReal.ofReal_ne_top).mpr
  exact channelGoodBlockPairHitProbability_le_exp_mul (n := n) hn P W d distortionThreshold
    informationThreshold x hx

/-- The preceding random-codeword hit bound in the familiar `exp (-t)` form. -/
theorem exp_neg_mul_channelGoodBlockPairHitProbability_le
    (hn : 0 < n) (P : PMF X) (W : X → PMF Y)
    (d : Distortion (X := X) (Y := Y))
    (distortionThreshold : ENNReal) (informationThreshold : ℝ)
    (x : Xblock n X) (hx : iidBlockPMF n P x ≠ 0)
    [DecidablePred
      (goodBlockPair n hn P W d distortionThreshold informationThreshold x)] :
    ENNReal.ofReal (Real.exp (-informationThreshold)) *
        codewordHitProbability (memorylessChannelBlockPMF n W x)
          (goodBlockPair n hn P W d distortionThreshold informationThreshold x) ≤
      codewordHitProbability (iidBlockPMF n (P.bind W))
        (goodBlockPair n hn P W d distortionThreshold informationThreshold x) := by
  rw [Real.exp_neg, ENNReal.ofReal_inv_of_pos (Real.exp_pos informationThreshold)]
  exact inv_mul_channelGoodBlockPairHitProbability_le (n := n) hn P W d distortionThreshold
    informationThreshold x hx

/-- An iid random codebook misses the good output set with probability bounded
by the standard random-covering expression. -/
theorem codebookMissProbability_le_one_sub_exp_neg_mul_channelGood
    (M : ℕ) (hn : 0 < n) (P : PMF X) (W : X → PMF Y)
    (d : Distortion (X := X) (Y := Y))
    (distortionThreshold : ENNReal) (informationThreshold : ℝ)
    (x : Xblock n X) (hx : iidBlockPMF n P x ≠ 0)
    [DecidablePred
      (goodBlockPair n hn P W d distortionThreshold informationThreshold x)] :
    codebookMissProbability M (iidBlockPMF n (P.bind W))
        (goodBlockPair n hn P W d distortionThreshold informationThreshold x) ≤
      (1 - ENNReal.ofReal (Real.exp (-informationThreshold)) *
        codewordHitProbability (memorylessChannelBlockPMF n W x)
          (goodBlockPair n hn P W d distortionThreshold informationThreshold x)) ^ M := by
  apply codebookMissProbability_le_one_sub_pow_of_le_hit
  exact exp_neg_mul_channelGoodBlockPairHitProbability_le (n := n) hn P W d
    distortionThreshold informationThreshold x hx

/-- A source block whose conditional good-pair probability is at least one
half is missed by an iid random codebook with probability at most
`(1 - exp(-t) / 2)^M`. -/
theorem codebookMissProbability_le_one_sub_half_exp_neg_pow_of_conditionalGood
    (M : ℕ) (hn : 0 < n) (P : PMF X) (W : X → PMF Y)
    (d : Distortion (X := X) (Y := Y))
    (distortionThreshold : ENNReal) (informationThreshold : ℝ)
    (x : Xblock n X) (hx : iidBlockPMF n P x ≠ 0)
    (hhalf : 1 / 2 ≤
      conditionalGoodBlockPairProbability n hn P W d distortionThreshold informationThreshold x)
    [hgoodDec : DecidablePred
      (goodBlockPair n hn P W d distortionThreshold informationThreshold x)] :
    codebookMissProbability M (iidBlockPMF n (P.bind W))
        (goodBlockPair n hn P W d distortionThreshold informationThreshold x) ≤
      (1 - (1 / 2 : ENNReal) *
        ENNReal.ofReal (Real.exp (-informationThreshold))) ^ M := by
  unfold conditionalGoodBlockPairProbability at hhalf
  have hchannel : (1 / 2 : ENNReal) ≤
      codewordHitProbability (memorylessChannelBlockPMF n W x)
        (goodBlockPair n hn P W d distortionThreshold informationThreshold x) := by
    rw [codewordHitProbability_eq_of_decidable
      (memorylessChannelBlockPMF n W x)
      (goodBlockPair n hn P W d distortionThreshold informationThreshold x)
      (Classical.decPred _) hgoodDec] at hhalf
    exact hhalf
  calc
    codebookMissProbability M (iidBlockPMF n (P.bind W))
        (goodBlockPair n hn P W d distortionThreshold informationThreshold x) ≤
        (1 - ENNReal.ofReal (Real.exp (-informationThreshold)) *
          codewordHitProbability (memorylessChannelBlockPMF n W x)
            (goodBlockPair n hn P W d distortionThreshold informationThreshold x)) ^ M :=
      codebookMissProbability_le_one_sub_exp_neg_mul_channelGood (n := n) M hn P W d
        distortionThreshold informationThreshold x hx
    _ ≤ (1 - (1 / 2 : ENNReal) *
        ENNReal.ofReal (Real.exp (-informationThreshold))) ^ M := by
      apply pow_le_pow_left'
      apply tsub_le_tsub_left
      simpa [mul_comm] using
        mul_le_mul_left hchannel (ENNReal.ofReal (Real.exp (-informationThreshold)))

/-- The random-codebook miss probability for a source block with conditional
good probability at least one half has an explicit exponential upper bound. -/
theorem codebookMissProbability_le_exp_neg_mul_half_exp_neg_of_conditionalGood
    (M : ℕ) (hn : 0 < n) (P : PMF X) (W : X → PMF Y)
    (d : Distortion (X := X) (Y := Y))
    (distortionThreshold : ENNReal) (informationThreshold : ℝ)
    (x : Xblock n X) (hx : iidBlockPMF n P x ≠ 0)
    (hhalf : 1 / 2 ≤
      conditionalGoodBlockPairProbability n hn P W d distortionThreshold informationThreshold x)
    [DecidablePred
      (goodBlockPair n hn P W d distortionThreshold informationThreshold x)] :
    codebookMissProbability M (iidBlockPMF n (P.bind W))
        (goodBlockPair n hn P W d distortionThreshold informationThreshold x) ≤
      ENNReal.ofReal (Real.exp (-((M : ℝ) *
        ((1 / 2 : ℝ) * Real.exp (-informationThreshold))))) := by
  have hhalfOfReal : ENNReal.ofReal ((1 / 2 : ℝ)) = (1 / 2 : ENNReal) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_one]
    congr 1
    norm_num [ENNReal.ofReal]
  have hfactor : (1 / 2 : ENNReal) *
      ENNReal.ofReal (Real.exp (-informationThreshold)) =
      ENNReal.ofReal ((1 / 2 : ℝ) * Real.exp (-informationThreshold)) := by
    rw [ENNReal.ofReal_mul (by norm_num), hhalfOfReal]
  calc
    codebookMissProbability M (iidBlockPMF n (P.bind W))
        (goodBlockPair n hn P W d distortionThreshold informationThreshold x) ≤
        (1 - (1 / 2 : ENNReal) *
          ENNReal.ofReal (Real.exp (-informationThreshold))) ^ M :=
      codebookMissProbability_le_one_sub_half_exp_neg_pow_of_conditionalGood
        (n := n) M hn P W d distortionThreshold informationThreshold x hx hhalf
    _ = (1 - ENNReal.ofReal
        ((1 / 2 : ℝ) * Real.exp (-informationThreshold))) ^ M := by rw [hfactor]
    _ ≤ ENNReal.ofReal (Real.exp (-((M : ℝ) *
        ((1 / 2 : ℝ) * Real.exp (-informationThreshold))))) :=
      one_sub_ofReal_pow_le_exp_neg_mul M _
        (mul_nonneg (by norm_num) (Real.exp_nonneg _))

/-- For the rounded exponential codebook, a strict rate gap gives an explicit
super-exponentially small random-covering miss bound. -/
theorem codebookMissProbability_le_exp_neg_quarter_exp_rateGap_of_conditionalGood
    (n : ℕ) (rate threshold : ℝ)
    (hlarge : 2 ≤ Real.exp ((n : ℝ) * rate))
    (hn : 0 < n) (P : PMF X) (W : X → PMF Y)
    (d : Distortion (X := X) (Y := Y))
    (distortionThreshold : ENNReal)
    (x : Xblock n X) (hx : iidBlockPMF n P x ≠ 0)
    (hhalf : 1 / 2 ≤ conditionalGoodBlockPairProbability n hn P W d
      distortionThreshold ((n : ℝ) * threshold) x)
    [DecidablePred
      (goodBlockPair n hn P W d distortionThreshold ((n : ℝ) * threshold) x)] :
    codebookMissProbability (exponentialCodebookSize n rate) (iidBlockPMF n (P.bind W))
        (goodBlockPair n hn P W d distortionThreshold ((n : ℝ) * threshold) x) ≤
      ENNReal.ofReal (Real.exp (-(1 / 4 *
        Real.exp ((n : ℝ) * (rate - threshold))))) := by
  have hcover : (1 / 4 : ℝ) * Real.exp ((n : ℝ) * (rate - threshold)) ≤
      (exponentialCodebookSize n rate : ℝ) * (1 / 2 : ℝ) *
        Real.exp (-((n : ℝ) * threshold)) :=
    quarter_exp_rateGap_le_exponentialCodebook_coveringExponent n rate threshold hlarge
  calc
    codebookMissProbability (exponentialCodebookSize n rate) (iidBlockPMF n (P.bind W))
        (goodBlockPair n hn P W d distortionThreshold ((n : ℝ) * threshold) x) ≤
        ENNReal.ofReal (Real.exp (-((exponentialCodebookSize n rate : ℝ) *
          ((1 / 2 : ℝ) * Real.exp (-((n : ℝ) * threshold)))))) :=
      codebookMissProbability_le_exp_neg_mul_half_exp_neg_of_conditionalGood
        (n := n) (exponentialCodebookSize n rate) hn P W d distortionThreshold
        ((n : ℝ) * threshold) x hx hhalf
    _ ≤ ENNReal.ofReal (Real.exp (-((1 / 4 : ℝ) *
        Real.exp ((n : ℝ) * (rate - threshold))))) := by
      apply ENNReal.ofReal_mono
      apply Real.exp_le_exp.mpr
      exact neg_le_neg (by simpa [mul_assoc] using hcover)

/-- If all but source mass `2δ` has conditional good-pair probability at
least one half, then the average miss probability of the exponential random
codebook is at most `2δ` plus its super-exponential covering term. -/
theorem averageCodebookMissProbability_le_two_mul_add_exp_neg_quarter_exp_rateGap
    (n : ℕ) (rate threshold : ℝ)
    (hlarge : 2 ≤ Real.exp ((n : ℝ) * rate))
    (hn : 0 < n) (P : PMF X) (W : X → PMF Y)
    (d : Distortion (X := X) (Y := Y))
    (distortionThreshold δ : ENNReal)
    [∀ x : Xblock n X, DecidablePred
      (goodBlockPair n hn P W d distortionThreshold ((n : ℝ) * threshold) x)]
    [DecidablePred (fun x : Xblock n X => 1 / 2 ≤
      conditionalGoodBlockPairProbability n hn P W d distortionThreshold
        ((n : ℝ) * threshold) x)]
    (hsource : 1 - 2 * δ ≤ codewordHitProbability (iidBlockPMF n P)
      (fun x => 1 / 2 ≤ conditionalGoodBlockPairProbability n hn P W d
        distortionThreshold ((n : ℝ) * threshold) x)) :
    averageCodebookMissProbability (exponentialCodebookSize n rate)
        (iidBlockPMF n P) (iidBlockPMF n (P.bind W))
        (goodBlockPair n hn P W d distortionThreshold ((n : ℝ) * threshold)) ≤
      2 * δ + ENNReal.ofReal (Real.exp (-(1 / 4 *
        Real.exp ((n : ℝ) * (rate - threshold))))) := by
  let high : Xblock n X → Prop := fun x => 1 / 2 ≤
    conditionalGoodBlockPairProbability n hn P W d distortionThreshold
      ((n : ℝ) * threshold) x
  let ε : ENNReal := ENNReal.ofReal (Real.exp (-(1 / 4 *
    Real.exp ((n : ℝ) * (rate - threshold)))))
  have haverage : averageCodebookMissProbability (exponentialCodebookSize n rate)
      (iidBlockPMF n P) (iidBlockPMF n (P.bind W))
      (goodBlockPair n hn P W d distortionThreshold ((n : ℝ) * threshold)) ≤
      (∑ x : Xblock n X, if high x then 0 else iidBlockPMF n P x) + ε := by
    apply averageCodebookMissProbability_le_badMass_add_error
    intro x hx hPx
    exact codebookMissProbability_le_exp_neg_quarter_exp_rateGap_of_conditionalGood
      n rate threshold hlarge hn P W d distortionThreshold x hPx hx
  have hbad : (∑ x : Xblock n X, if high x then 0 else iidBlockPMF n P x) ≤
      2 * δ := by
    apply badMass_le_two_mul_of_one_sub_le_hitProbability
    simpa [high] using hsource
  calc
    averageCodebookMissProbability (exponentialCodebookSize n rate)
        (iidBlockPMF n P) (iidBlockPMF n (P.bind W))
        (goodBlockPair n hn P W d distortionThreshold ((n : ℝ) * threshold)) ≤
        (∑ x : Xblock n X, if high x then 0 else iidBlockPMF n P x) + ε := haverage
    _ ≤ 2 * δ + ε := by simpa [add_comm] using add_le_add_right hbad ε
    _ = 2 * δ + ENNReal.ofReal (Real.exp (-(1 / 4 *
        Real.exp ((n : ℝ) * (rate - threshold))))) := rfl

theorem sum_coordinate_mutualInformationEntropy_le_block
    (k : ℕ) (Q : PMF ((Fin k → X) × (Fin k → Y))) (P : PMF X)
    (hfst : Q.map Prod.fst = iidBlockPMF k P) :
    (∑ i : Fin k,
        mutualInformationEntropy
          (Q.map (fun z => (z.1 i, z.2 i)))) ≤
      mutualInformationEntropy Q := by
  let S : PMF ((Fin k → Y) × (Fin k → X)) := Q.map Prod.swap
  have hS_entropy : shannonEntropy S = shannonEntropy Q := by
    exact shannonEntropy_map_of_injective Q Prod.swap Prod.swap_injective
  have hS_fst : S.map Prod.fst = Q.map Prod.snd := by
    unfold S
    rw [PMF.map_comp]
    rfl
  have hcoord (i : Fin k) :
      S.map (fun z => (z.1 i, z.2 i)) =
        (Q.map (fun z => (z.1 i, z.2 i))).map Prod.swap := by
    unfold S
    rw [PMF.map_comp, PMF.map_comp]
    rfl
  have hcoord_entropy (i : Fin k) :
      shannonEntropy
          ((Q.map (fun z => (z.1 i, z.2 i))).map Prod.swap) =
        shannonEntropy (Q.map (fun z => (z.1 i, z.2 i))) :=
    shannonEntropy_map_of_injective _ Prod.swap Prod.swap_injective
  have hcoord_fst (i : Fin k) :
      ((Q.map (fun z => (z.1 i, z.2 i))).map Prod.swap).map Prod.fst =
        (Q.map (fun z => (z.1 i, z.2 i))).map Prod.snd := by
    calc
      ((Q.map (fun z => (z.1 i, z.2 i))).map Prod.swap).map Prod.fst =
          (Q.map (fun z => (z.1 i, z.2 i))).map
            (Prod.fst ∘ Prod.swap) := by
        rw [PMF.map_comp]
      _ = (Q.map (fun z => (z.1 i, z.2 i))).map Prod.snd := by
        rfl
  have hcond := conditionalEntropy_pi_le_sum k S
  unfold conditionalEntropy at hcond
  rw [hS_entropy, hS_fst] at hcond
  simp_rw [hcoord, hcoord_entropy, hcoord_fst] at hcond
  have hcoordinate_fst (i : Fin k) :
      (Q.map (fun z => (z.1 i, z.2 i))).map Prod.fst = P := by
    rw [PMF.map_comp]
    change Q.map ((fun x : Fin k → X => x i) ∘ Prod.fst) = P
    rw [← PMF.map_comp, hfst, iidBlockPMF_coordinate]
  have hsum :
      (∑ i : Fin k,
          mutualInformationEntropy (Q.map (fun z => (z.1 i, z.2 i)))) =
        (k : ℝ) * shannonEntropy P -
          ∑ i : Fin k,
            (shannonEntropy (Q.map (fun z => (z.1 i, z.2 i))) -
              shannonEntropy
                ((Q.map (fun z => (z.1 i, z.2 i))).map Prod.snd)) := by
    calc
      (∑ i : Fin k,
          mutualInformationEntropy (Q.map (fun z => (z.1 i, z.2 i)))) =
          ∑ i : Fin k,
            (shannonEntropy P -
              (shannonEntropy (Q.map (fun z => (z.1 i, z.2 i))) -
                shannonEntropy
                  ((Q.map (fun z => (z.1 i, z.2 i))).map Prod.snd))) := by
        apply Finset.sum_congr rfl
        intro i _
        unfold mutualInformationEntropy
        rw [hcoordinate_fst]
        ring
      _ = (k : ℝ) * shannonEntropy P -
          ∑ i : Fin k,
            (shannonEntropy (Q.map (fun z => (z.1 i, z.2 i))) -
              shannonEntropy
                ((Q.map (fun z => (z.1 i, z.2 i))).map Prod.snd)) := by
        rw [Finset.sum_sub_distrib]
        simp
  have hblock :
      mutualInformationEntropy Q =
        (k : ℝ) * shannonEntropy P -
          (shannonEntropy Q - shannonEntropy (Q.map Prod.snd)) := by
    unfold mutualInformationEntropy
    rw [hfst, shannonEntropy_iidBlockPMF]
    ring
  rw [hsum, hblock]
  linarith

def codeReproduction
    (code : RateDistortionCode X Y n M) : Xblock n X → Yblock n Y :=
  fun x => code.decoder (code.encoder x)

-- Distribution of the encoder index under the IID source block.
def codeIndexPMF
    (code : RateDistortionCode X Y n M) (P : PMF X) : PMF (Index M) :=
  (iidBlockPMF n P).map code.encoder

-- Distribution of the reconstructed block under the IID source block.
def codeReproductionPMF
    (code : RateDistortionCode X Y n M) (P : PMF X) : PMF (Yblock n Y) :=
  (iidBlockPMF n P).map (codeReproduction n M code)

theorem codeReproductionPMF_eq_map_codeIndex
    (code : RateDistortionCode X Y n M) (P : PMF X) :
    codeReproductionPMF n M code P =
      (codeIndexPMF n M code P).map code.decoder := by
  rw [codeReproductionPMF, codeIndexPMF, PMF.map_comp]
  rfl

theorem shannonEntropy_codeReproduction_le_codeIndex
    (code : RateDistortionCode X Y n M) (P : PMF X) :
    shannonEntropy (codeReproductionPMF n M code P) ≤
      shannonEntropy (codeIndexPMF n M code P) := by
  rw [codeReproductionPMF_eq_map_codeIndex]
  exact shannonEntropy_map_le (codeIndexPMF n M code P) code.decoder

theorem shannonEntropy_codeIndex_le_log
    (code : RateDistortionCode X Y n M) (P : PMF X) :
    shannonEntropy (codeIndexPMF n M code P) ≤ Real.log M := by
  simpa using shannonEntropy_le_log_card (codeIndexPMF n M code P)

theorem shannonEntropy_codeReproduction_le_log
    (code : RateDistortionCode X Y n M) (P : PMF X) :
    shannonEntropy (codeReproductionPMF n M code P) ≤ Real.log M :=
  (shannonEntropy_codeReproduction_le_codeIndex n M code P).trans
    (shannonEntropy_codeIndex_le_log n M code P)

-- Joint law of a source block and its deterministic reconstruction.
def codeJointPMF
    (code : RateDistortionCode X Y n M) (P : PMF X) :
    PMF (Xblock n X × Yblock n Y) :=
  (iidBlockPMF n P).map fun x => (x, codeReproduction n M code x)

@[simp] theorem codeJointPMF_apply
    (code : RateDistortionCode X Y n M) (P : PMF X)
    (x : Xblock n X) (y : Yblock n Y) :
    codeJointPMF n M code P (x, y) =
      if y = codeReproduction n M code x then iidBlockPMF n P x else 0 := by
  simp only [codeJointPMF, PMF.map_apply, tsum_fintype]
  by_cases hy : y = codeReproduction n M code x
  · subst y
    rw [if_pos rfl]
    calc
      _ = ∑ a, if x = a then iidBlockPMF n P a else 0 := by
        apply Finset.sum_congr rfl
        intro a _
        by_cases hxa : x = a
        · subst a
          simp
        · simp [hxa]
      _ = iidBlockPMF n P x := by simp
  · simp [hy]

@[simp] theorem codeJointPMF_fst
    (code : RateDistortionCode X Y n M) (P : PMF X) :
    (codeJointPMF n M code P).map Prod.fst = iidBlockPMF n P := by
  rw [codeJointPMF, PMF.map_comp]
  convert PMF.map_id (iidBlockPMF n P) using 1

@[simp] theorem codeJointPMF_snd
    (code : RateDistortionCode X Y n M) (P : PMF X) :
    (codeJointPMF n M code P).map Prod.snd =
      codeReproductionPMF n M code P := by
  rw [codeJointPMF, codeReproductionPMF, PMF.map_comp]
  rfl

theorem shannonEntropy_codeJointPMF
    (code : RateDistortionCode X Y n M) (P : PMF X) :
    shannonEntropy (codeJointPMF n M code P) =
      shannonEntropy (iidBlockPMF n P) := by
  apply shannonEntropy_map_of_injective
  intro x x' h
  exact congrArg Prod.fst h

theorem mutualInformationEntropy_codeJointPMF
    (code : RateDistortionCode X Y n M) (P : PMF X) :
    mutualInformationEntropy (codeJointPMF n M code P) =
      shannonEntropy (codeReproductionPMF n M code P) := by
  rw [mutualInformationEntropy, codeJointPMF_fst, codeJointPMF_snd,
    shannonEntropy_codeJointPMF]
  ring

theorem mutualInformationEntropy_codeJointPMF_le_log
    (code : RateDistortionCode X Y n M) (P : PMF X) :
    mutualInformationEntropy (codeJointPMF n M code P) ≤ Real.log M := by
  rw [mutualInformationEntropy_codeJointPMF]
  exact shannonEntropy_codeReproduction_le_log n M code P

theorem mutual_information_codeJointPMF_le_log
    (code : RateDistortionCode X Y n M) (P : PMF X) :
    mutual_information (codeJointPMF n M code P) ≤
      ENNReal.ofReal (Real.log M) := by
  rw [mutual_information_eq_ofReal_entropy]
  exact ENNReal.ofReal_le_ofReal
    (mutualInformationEntropy_codeJointPMF_le_log n M code P)

def codeCoordinateJointPMF
    (code : RateDistortionCode X Y n M) (P : PMF X) (i : Fin n) :
    PMF (X × Y) :=
  (codeJointPMF n M code P).map fun z => (z.1 i, z.2 i)

@[simp] theorem codeCoordinateJointPMF_fst
    (code : RateDistortionCode X Y n M) (P : PMF X) (i : Fin n) :
    (codeCoordinateJointPMF n M code P i).map Prod.fst = P := by
  rw [codeCoordinateJointPMF, PMF.map_comp]
  change (codeJointPMF n M code P).map
    ((fun x : Xblock n X => x i) ∘ Prod.fst) = P
  rw [← PMF.map_comp, codeJointPMF_fst, iidBlockPMF_coordinate]

-- The joint law at a uniformly sampled coordinate. This is the finite
-- time-sharing distribution used to pass from a block code to one letter.
noncomputable def averageCoordinateJointPMF
    (hn : 0 < n) (code : RateDistortionCode X Y n M) (P : PMF X) :
    PMF (X × Y) := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact (PMF.uniformOfFintype (Fin n)).bind
    (codeCoordinateJointPMF n M code P)

@[simp] theorem averageCoordinateJointPMF_fst
    (hn : 0 < n) (code : RateDistortionCode X Y n M) (P : PMF X) :
    (averageCoordinateJointPMF n M hn code P).map Prod.fst = P := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  rw [averageCoordinateJointPMF, PMF.map_bind]
  simp

theorem mutualInformationEntropy_averageCoordinate_le_average
    (hn : 0 < n) (code : RateDistortionCode X Y n M) (P : PMF X) :
    mutualInformationEntropy (averageCoordinateJointPMF n M hn code P) ≤
      (∑ i : Fin n,
        mutualInformationEntropy (codeCoordinateJointPMF n M code P i)) / n := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  rw [averageCoordinateJointPMF]
  calc
    mutualInformationEntropy
        ((PMF.uniformOfFintype (Fin n)).bind
          (codeCoordinateJointPMF n M code P)) ≤
        ∑ i : Fin n, ((PMF.uniformOfFintype (Fin n)) i).toReal *
          mutualInformationEntropy (codeCoordinateJointPMF n M code P i) := by
      exact mutualInformationEntropy_bind_le_average_of_fst_eq
        (PMF.uniformOfFintype (Fin n))
        (codeCoordinateJointPMF n M code P) P
        (codeCoordinateJointPMF_fst n M code P)
    _ = (∑ i : Fin n,
        mutualInformationEntropy (codeCoordinateJointPMF n M code P i)) / n := by
      simp only [PMF.uniformOfFintype_apply, Fintype.card_fin,
        ENNReal.toReal_inv, ENNReal.toReal_natCast]
      rw [← Finset.mul_sum]
      field_simp

theorem sum_codeCoordinate_mutualInformationEntropy_le_block
    (code : RateDistortionCode X Y n M) (P : PMF X) :
    (∑ i : Fin n,
        mutualInformationEntropy (codeCoordinateJointPMF n M code P i)) ≤
      mutualInformationEntropy (codeJointPMF n M code P) := by
  exact sum_coordinate_mutualInformationEntropy_le_block n
    (codeJointPMF n M code P) P (codeJointPMF_fst n M code P)

theorem mutualInformationEntropy_averageCoordinate_le_log_div
    (hn : 0 < n) (code : RateDistortionCode X Y n M) (P : PMF X) :
    mutualInformationEntropy (averageCoordinateJointPMF n M hn code P) ≤
      Real.log M / n := by
  calc
    mutualInformationEntropy (averageCoordinateJointPMF n M hn code P) ≤
        (∑ i : Fin n,
          mutualInformationEntropy (codeCoordinateJointPMF n M code P i)) / n :=
      mutualInformationEntropy_averageCoordinate_le_average n M hn code P
    _ ≤ mutualInformationEntropy (codeJointPMF n M code P) / n := by
      gcongr
      exact sum_codeCoordinate_mutualInformationEntropy_le_block n M code P
    _ ≤ Real.log M / n := by
      gcongr
      exact mutualInformationEntropy_codeJointPMF_le_log n M code P

theorem mutual_information_averageCoordinate_le_codeRate
    (hn : 0 < n) (code : RateDistortionCode X Y n M) (P : PMF X) :
    mutual_information (averageCoordinateJointPMF n M hn code P) ≤
      ENNReal.ofReal (codeRate n M hn) := by
  rw [mutual_information_eq_ofReal_entropy]
  exact ENNReal.ofReal_le_ofReal
    (mutualInformationEntropy_averageCoordinate_le_log_div n M hn code P)

theorem jointExpectedDistortion_codeCoordinate
    (code : RateDistortionCode X Y n M) (P : PMF X)
    (d : Distortion (X := X) (Y := Y)) (i : Fin n) :
    jointExpectedDistortion (codeCoordinateJointPMF n M code P i) d =
      ∑ x : Xblock n X, iidBlockPMF n P x *
        (d (x i) (codeReproduction n M code x i) : ENNReal) := by
  rw [jointExpectedDistortion, ← Fintype.sum_prod_type']
  rw [codeCoordinateJointPMF, sum_map_mul]
  rw [codeJointPMF, sum_map_mul]

theorem jointExpectedDistortion_averageCoordinate
    (hn : 0 < n) (code : RateDistortionCode X Y n M) (P : PMF X)
    (d : Distortion (X := X) (Y := Y)) :
    jointExpectedDistortion (averageCoordinateJointPMF n M hn code P) d =
      (∑ i : Fin n,
        jointExpectedDistortion (codeCoordinateJointPMF n M code P i) d) / n := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  rw [jointExpectedDistortion, ← Fintype.sum_prod_type']
  rw [averageCoordinateJointPMF, sum_bind_mul]
  simp only [PMF.uniformOfFintype_apply, Fintype.card_fin]
  calc
    (∑ i : Fin n, (n : ENNReal)⁻¹ *
        ∑ z : X × Y, codeCoordinateJointPMF n M code P i z *
          (d z.1 z.2 : ENNReal)) =
        ∑ i : Fin n, (∑ z : X × Y,
          codeCoordinateJointPMF n M code P i z *
            (d z.1 z.2 : ENNReal)) * (n : ENNReal)⁻¹ := by
      apply Finset.sum_congr rfl
      intro i _
      ac_rfl
    _ = ∑ i : Fin n,
        jointExpectedDistortion (codeCoordinateJointPMF n M code P i) d *
          (n : ENNReal)⁻¹ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [jointExpectedDistortion, ← Fintype.sum_prod_type']
    _ = (∑ i : Fin n,
        jointExpectedDistortion (codeCoordinateJointPMF n M code P i) d) / n := by
      simp only [div_eq_mul_inv]
      rw [Finset.sum_mul]


-- The expected distortion is the average distortion over all possible source sequences,
-- weighted by their probability.
def expectedDistortion
    (hn : 0 < n)
    (code : RateDistortionCode X Y n M)
    (P : PMF X)
    (d : Distortion (X := X) (Y := Y)) : ENNReal :=
  -- Sum over all possible source blocks x
  ∑' x : (Xblock n X), (iidBlockPMF n P x) *
    (blockDistortion n hn d x (code.decoder (code.encoder x)))

theorem expectedDistortion_eq_averageCoordinate
    (hn : 0 < n) (code : RateDistortionCode X Y n M)
    (P : PMF X) (d : Distortion (X := X) (Y := Y)) :
    expectedDistortion n M hn code P d =
      jointExpectedDistortion (averageCoordinateJointPMF n M hn code P) d := by
  rw [jointExpectedDistortion_averageCoordinate]
  simp only [jointExpectedDistortion_codeCoordinate]
  simp only [expectedDistortion, blockDistortion, codeReproduction, tsum_fintype]
  calc
    (∑ x : Xblock n X, iidBlockPMF n P x *
        ((∑ i : Fin n,
          (d (x i) (code.decoder (code.encoder x) i) : ENNReal)) / n)) =
        ∑ x : Xblock n X,
          (iidBlockPMF n P x *
            ∑ i : Fin n,
              (d (x i) (code.decoder (code.encoder x) i) : ENNReal)) / n := by
      apply Finset.sum_congr rfl
      intro x _
      rw [mul_div_assoc]
    _ = (∑ x : Xblock n X, iidBlockPMF n P x *
          ∑ i : Fin n,
            (d (x i) (code.decoder (code.encoder x) i) : ENNReal)) / n := by
      simp only [div_eq_mul_inv]
      rw [Finset.sum_mul]
    _ = (∑ x : Xblock n X, ∑ i : Fin n,
          iidBlockPMF n P x *
            (d (x i) (code.decoder (code.encoder x) i) : ENNReal)) / n := by
      congr 1
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.mul_sum]
    _ = (∑ i : Fin n, ∑ x : Xblock n X, iidBlockPMF n P x *
          (d (x i) (code.decoder (code.encoder x) i) : ENNReal)) / n := by
      rw [Finset.sum_comm]

theorem RateDistortionFunction_le_codeCoordinateInformation
    (hn : 0 < n) (code : RateDistortionCode X Y n M)
    (P : PMF X) (d : Distortion (X := X) (Y := Y)) :
    RateDistortionFunction P d (expectedDistortion n M hn code P d) ≤
      mutual_information (averageCoordinateJointPMF n M hn code P) := by
  apply RateDistortionFunction_le_of_joint P d
    (expectedDistortion n M hn code P d)
    (averageCoordinateJointPMF n M hn code P)
    (averageCoordinateJointPMF_fst n M hn code P)
  rw [← expectedDistortion_eq_averageCoordinate]

theorem RateDistortionFunction_expectedDistortion_le_codeRate
    (hn : 0 < n) (code : RateDistortionCode X Y n M)
    (P : PMF X) (d : Distortion (X := X) (Y := Y)) :
    RateDistortionFunction P d (expectedDistortion n M hn code P d) ≤
      ENNReal.ofReal (codeRate n M hn) := by
  exact (RateDistortionFunction_le_codeCoordinateInformation
    n M hn code P d).trans
      (mutual_information_averageCoordinate_le_codeRate n M hn code P)

theorem expectedDistortion_le_bound
    (hn : 0 < n) (code : RateDistortionCode X Y n M)
    (P : PMF X) (d : Distortion (X := X) (Y := Y)) :
    expectedDistortion n M hn code P d ≤ (distortionBound d : ENNReal) := by
  unfold expectedDistortion
  calc
    (∑' x : Xblock n X, iidBlockPMF n P x *
      blockDistortion n hn d x (code.decoder (code.encoder x))) ≤
        ∑' x : Xblock n X, iidBlockPMF n P x * distortionBound d := by
      exact ENNReal.tsum_le_tsum fun x => by
        gcongr
        exact blockDistortion_le_bound n hn d x (code.decoder (code.encoder x))
    _ = (distortionBound d : ENNReal) := by
      rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- The expected distortion of a deterministic codebook code is bounded by
its target threshold plus the distortion bound times its source miss
probability. -/
theorem expectedDistortion_codebookCode_le_threshold_add_bound_mul_sourceMiss
    (hn : 0 < n) (hM : 0 < M) (P : PMF X)
    (d : Distortion (X := X) (Y := Y))
    (codebook : Index M → Yblock n Y) (good : Xblock n X → Yblock n Y → Prop)
    [∀ x, DecidablePred (good x)] (distortionThreshold : ENNReal)
    (hgood : ∀ x y, good x y → blockDistortion n hn d x y ≤ distortionThreshold) :
    expectedDistortion n M hn (codebookCode n M hM codebook good) P d ≤
      distortionThreshold + (distortionBound d : ENNReal) *
        codebookSourceMissProbability M (iidBlockPMF n P) codebook good := by
  unfold expectedDistortion codebookSourceMissProbability
  simp only [tsum_fintype]
  calc
    (∑ x : Xblock n X, iidBlockPMF n P x *
        blockDistortion n hn d x
          ((codebookCode n M hM codebook good).decoder
            ((codebookCode n M hM codebook good).encoder x))) ≤
        ∑ x : Xblock n X, iidBlockPMF n P x *
          (distortionThreshold + (distortionBound d : ENNReal) *
            if ∀ j, ¬ good x (codebook j) then 1 else 0) := by
      apply Finset.sum_le_sum
      intro x _
      simpa [mul_comm] using mul_le_mul_left
        (blockDistortion_codebookCode_le_threshold_add_bound_mul_miss
          n M hn hM d codebook good distortionThreshold hgood x)
        (iidBlockPMF n P x)
    _ = ∑ x : Xblock n X, (iidBlockPMF n P x * distortionThreshold +
        (distortionBound d : ENNReal) *
          (iidBlockPMF n P x * if ∀ j, ¬ good x (codebook j) then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = (∑ x : Xblock n X, iidBlockPMF n P x * distortionThreshold) +
        ∑ x : Xblock n X, (distortionBound d : ENNReal) *
          (iidBlockPMF n P x * if ∀ j, ¬ good x (codebook j) then 1 else 0) := by
      rw [Finset.sum_add_distrib]
    _ = distortionThreshold +
        ∑ x : Xblock n X, (distortionBound d : ENNReal) *
          (iidBlockPMF n P x * if ∀ j, ¬ good x (codebook j) then 1 else 0) := by
      congr 1
      rw [← Finset.sum_mul, sum_pmf, one_mul]
    _ = distortionThreshold + (distortionBound d : ENNReal) *
        ∑ x : Xblock n X, iidBlockPMF n P x *
          if ∀ j, ¬ good x (codebook j) then 1 else 0 := by
      rw [← Finset.mul_sum]

/-- Combining random covering, deterministic codebook extraction, and the
bounded-distortion fallback yields a deterministic exponential-size codebook
with the stated expected-distortion bound. -/
theorem exists_codebookCode_expectedDistortion_le_threshold_add_bound_mul_error
    (n : ℕ) (rate threshold : ℝ)
    (hM : 0 < exponentialCodebookSize n rate)
    (hlarge : 2 ≤ Real.exp ((n : ℝ) * rate))
    (hn : 0 < n) (P : PMF X) (W : X → PMF Y)
    (d : Distortion (X := X) (Y := Y))
    (distortionThreshold δ : ENNReal)
    [∀ x : Xblock n X, DecidablePred
      (goodBlockPair n hn P W d distortionThreshold ((n : ℝ) * threshold) x)]
    [DecidablePred (fun x : Xblock n X => 1 / 2 ≤
      conditionalGoodBlockPairProbability n hn P W d distortionThreshold
        ((n : ℝ) * threshold) x)]
    (hsource : 1 - 2 * δ ≤ codewordHitProbability (iidBlockPMF n P)
      (fun x => 1 / 2 ≤ conditionalGoodBlockPairProbability n hn P W d
        distortionThreshold ((n : ℝ) * threshold) x)) :
    ∃ codebook : Index (exponentialCodebookSize n rate) → Yblock n Y,
      expectedDistortion n (exponentialCodebookSize n rate) hn
        (codebookCode n (exponentialCodebookSize n rate) hM codebook
          (goodBlockPair n hn P W d distortionThreshold ((n : ℝ) * threshold))) P d ≤
        distortionThreshold + (distortionBound d : ENNReal) *
          (2 * δ + ENNReal.ofReal (Real.exp (-(1 / 4 *
            Real.exp ((n : ℝ) * (rate - threshold)))))) := by
  obtain ⟨codebook, hcodebook⟩ :=
    exists_codebookSourceMissProbability_le_averageCodebookMissProbability
      (exponentialCodebookSize n rate) (iidBlockPMF n P)
      (iidBlockPMF n (P.bind W))
      (goodBlockPair n hn P W d distortionThreshold ((n : ℝ) * threshold))
  refine ⟨codebook, ?_⟩
  have hmiss : codebookSourceMissProbability (exponentialCodebookSize n rate)
      (iidBlockPMF n P) codebook
      (goodBlockPair n hn P W d distortionThreshold ((n : ℝ) * threshold)) ≤
      2 * δ + ENNReal.ofReal (Real.exp (-(1 / 4 *
        Real.exp ((n : ℝ) * (rate - threshold))))) := by
    calc
      codebookSourceMissProbability (exponentialCodebookSize n rate)
          (iidBlockPMF n P) codebook
          (goodBlockPair n hn P W d distortionThreshold ((n : ℝ) * threshold)) ≤
          averageCodebookMissProbability (exponentialCodebookSize n rate)
            (iidBlockPMF n P) (iidBlockPMF n (P.bind W))
            (goodBlockPair n hn P W d distortionThreshold ((n : ℝ) * threshold)) := hcodebook
      _ ≤ 2 * δ + ENNReal.ofReal (Real.exp (-(1 / 4 *
          Real.exp ((n : ℝ) * (rate - threshold))))) :=
        averageCodebookMissProbability_le_two_mul_add_exp_neg_quarter_exp_rateGap
          n rate threshold hlarge hn P W d distortionThreshold δ hsource
  calc
    expectedDistortion n (exponentialCodebookSize n rate) hn
        (codebookCode n (exponentialCodebookSize n rate) hM codebook
          (goodBlockPair n hn P W d distortionThreshold ((n : ℝ) * threshold))) P d ≤
        distortionThreshold + (distortionBound d : ENNReal) *
          codebookSourceMissProbability (exponentialCodebookSize n rate)
            (iidBlockPMF n P) codebook
            (goodBlockPair n hn P W d distortionThreshold ((n : ℝ) * threshold)) :=
      expectedDistortion_codebookCode_le_threshold_add_bound_mul_sourceMiss
        n (exponentialCodebookSize n rate) hn hM P d codebook
        (goodBlockPair n hn P W d distortionThreshold ((n : ℝ) * threshold))
        distortionThreshold (by
          intro x y hgood
          exact hgood.1)
    _ ≤ distortionThreshold + (distortionBound d : ENNReal) *
        (2 * δ + ENNReal.ofReal (Real.exp (-(1 / 4 *
          Real.exp ((n : ℝ) * (rate - threshold)))))) :=
      by
        simpa [mul_comm] using add_le_add_right
          (mul_le_mul_left hmiss (distortionBound d : ENNReal)) distortionThreshold

/-- With fixed positive distortion and information slacks, every sufficiently
large blocklength admits an exponential-size deterministic code with the
random-coding expected-distortion bound. -/
theorem exists_nat_forall_exists_exponentialCode_rate_and_expectedDistortion
    (rate threshold : ℝ) (hgap : threshold < rate)
    (P : PMF X) (W : X → PMF Y)
    (d : Distortion (X := X) (Y := Y))
    (distortionThreshold : ENNReal) (εd εi δ : ℝ)
    (hεd : 0 < εd) (hεi : 0 < εi) (hδ : 0 < δ) (hδle : δ ≤ 1)
    (hdistortionThreshold : distortionThreshold ≠ ⊤)
    (hdistortionSlack : (expected_distortion_single P W d).toReal + εd ≤
      distortionThreshold.toReal)
    (hinformationSlack : mutualInformationEntropy (induced_joint P W) + εi ≤ threshold) :
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n → ∃ hn : 0 < n,
      ∃ code : RateDistortionCode X Y n (exponentialCodebookSize n rate),
        codeRate n (exponentialCodebookSize n rate) hn ≤ rate ∧
        expectedDistortion n (exponentialCodebookSize n rate) hn code P d ≤
          distortionThreshold + (distortionBound d : ENNReal) *
            (2 * ENNReal.ofReal δ + ENNReal.ofReal (Real.exp (-(1 / 4 *
              Real.exp ((n : ℝ) * (rate - threshold)))))) := by
  have hthresholdPos : 0 < threshold := by
    have hIpos : 0 < mutualInformationEntropy (induced_joint P W) + εi :=
      add_pos_of_nonneg_of_pos
        (mutualInformationEntropy_nonneg (induced_joint P W)) hεi
    exact lt_of_lt_of_le hIpos hinformationSlack
  have hratePos : 0 < rate := hthresholdPos.trans hgap
  obtain ⟨Ngood, hNgoodPos, hgood⟩ :=
    exists_nat_one_sub_le_goodBlockPairProbability P W d distortionThreshold
      (fun n => (n : ℝ) * threshold) εd εi δ hεd hεi hδ
      hdistortionThreshold hdistortionSlack (by
        intro n
        exact mul_le_mul_of_nonneg_left hinformationSlack (Nat.cast_nonneg n))
  obtain ⟨Nlarge, hlarge⟩ := exists_nat_two_le_exp_mul_of_pos rate hratePos
  refine ⟨max Ngood Nlarge,
    lt_of_lt_of_le hNgoodPos (Nat.le_max_left _ _), ?_⟩
  intro n hn
  have hnGood : Ngood ≤ n := (Nat.le_max_left _ _).trans hn
  have hnLarge : Nlarge ≤ n := (Nat.le_max_right _ _).trans hn
  have hnPos : 0 < n := hNgoodPos.trans_le hnGood
  have hM : 0 < exponentialCodebookSize n rate :=
    exponentialCodebookSize_pos n rate hratePos.le
  have hgoodN : 1 - ENNReal.ofReal δ ≤
      goodBlockPairProbability n hnPos P W d distortionThreshold ((n : ℝ) * threshold) :=
    hgood n hnGood hnPos
  have hsource : 1 - 2 * ENNReal.ofReal δ ≤
      codewordHitProbability (iidBlockPMF n P)
        (fun x => 1 / 2 ≤ conditionalGoodBlockPairProbability n hnPos P W d
          distortionThreshold ((n : ℝ) * threshold) x) :=
    one_sub_two_mul_le_sourceHalfConditionalGoodProbability (n := n) hnPos P W d
      distortionThreshold ((n : ℝ) * threshold) (ENNReal.ofReal δ)
      (ENNReal.ofReal_le_one.mpr hδle) hgoodN
  letI : ∀ x : Xblock n X, DecidablePred
      (goodBlockPair n hnPos P W d distortionThreshold ((n : ℝ) * threshold) x) :=
    fun x => Classical.decPred _
  obtain ⟨codebook, hcodebook⟩ :=
    exists_codebookCode_expectedDistortion_le_threshold_add_bound_mul_error
      n rate threshold hM (hlarge n hnLarge) hnPos P W d distortionThreshold
      (ENNReal.ofReal δ) hsource
  refine ⟨hnPos, codebookCode n (exponentialCodebookSize n rate) hM codebook
    (goodBlockPair n hnPos P W d distortionThreshold ((n : ℝ) * threshold)), ?_, ?_⟩
  · exact codeRate_exponentialCodebookSize_le (n := n) hnPos rate hratePos.le
  · exact hcodebook

-- Define a sequence of codes
structure CodeSequence (X Y : Type*) [Fintype X] [Fintype Y] where
  -- At sequence index `n`, the actual blocklength is `n + 1`.
  M : ℕ → ℕ
  -- Every codebook is nonempty.
  hM : ∀ n, 0 < M n
  -- Thus the sequence contains exactly the positive blocklengths 1, 2, 3, ...
  code : ∀ n, RateDistortionCode X Y (n + 1) (M n)

-- The stronger pointwise rate condition used in the PDF's Definition 5.2.
def hasPointwiseRateBound
    (seq : CodeSequence X Y) (R : ℝ) : Prop :=
  ∀ n, codeRate (n + 1) (seq.M n) (Nat.succ_pos n) ≤ R

/-- The sequence of constant-reconstruction codes with exponential codebook
sizes.  It is useful when only a rate bound is required. -/
noncomputable def constantExponentialCodeSequence
    (rate : ℝ) (hrate : 0 ≤ rate) [Nonempty Y] : CodeSequence X Y where
  M := fun n => exponentialCodebookSize (n + 1) rate
  hM := fun n => exponentialCodebookSize_pos (n + 1) rate hrate
  code := fun n => constantRateDistortionCode (n + 1)
    (exponentialCodebookSize (n + 1) rate)
    (exponentialCodebookSize_pos (n + 1) rate hrate)

theorem constantExponentialCodeSequence_hasPointwiseRateBound
    (rate : ℝ) (hrate : 0 ≤ rate) [Nonempty Y] :
    hasPointwiseRateBound (constantExponentialCodeSequence (X := X) (Y := Y)
      rate hrate) rate := by
  intro n
  exact codeRate_exponentialCodebookSize_le (n := n + 1)
    (Nat.succ_pos n) rate hrate

/-- At block index `n`, select the largest positive precision level whose
associated blocklength threshold has already been reached.  Level zero is a
dummy value for the finitely many initial indices. -/
noncomputable def activePrecisionLevel (N : ℕ → ℕ) (n : ℕ) : ℕ := by
  classical
  exact Nat.findGreatest (fun k => k = 0 ∨ N k ≤ n + 1) (n + 1)

theorem activePrecisionLevel_eq_zero_or_threshold_le
    (N : ℕ → ℕ) (n : ℕ) :
    activePrecisionLevel N n = 0 ∨ N (activePrecisionLevel N n) ≤ n + 1 := by
  classical
  unfold activePrecisionLevel
  exact Nat.findGreatest_spec (P := fun k => k = 0 ∨ N k ≤ n + 1) (Nat.zero_le _)
    (Or.inl rfl : 0 = 0 ∨ N 0 ≤ n + 1)

/-- Every fixed precision level is eventually active. -/
theorem eventually_le_activePrecisionLevel
    (N : ℕ → ℕ) (K : ℕ) :
    ∀ᶠ n in atTop, K ≤ activePrecisionLevel N n := by
  classical
  have hevent : ∀ᶠ n in atTop, K ≤ n + 1 ∧ N K ≤ n + 1 := by
    apply eventually_atTop.2
    refine ⟨max K (N K), fun n hn => ?_⟩
    exact ⟨((Nat.le_max_left _ _).trans hn).trans (Nat.le_succ n),
      ((Nat.le_max_right _ _).trans hn).trans (Nat.le_succ n)⟩
  filter_upwards [hevent] with n hn
  unfold activePrecisionLevel
  apply Nat.le_findGreatest
  · exact hn.1
  · exact Or.inr hn.2

/-- The standard positive slack used to diagonalize the fixed-slack direct
coding statements. -/
noncomputable def diagonalSlack (k : ℕ) : ℝ :=
  1 / ((k + 1 : ℕ) : ℝ)

theorem diagonalSlack_pos (k : ℕ) : 0 < diagonalSlack k := by
  unfold diagonalSlack
  positivity

theorem diagonalSlack_le_one (k : ℕ) : diagonalSlack k ≤ 1 := by
  unfold diagonalSlack
  apply (div_le_iff₀ (by positivity)).mpr
  norm_num

theorem ennreal_ofReal_diagonalSlack (k : ℕ) :
    ENNReal.ofReal (diagonalSlack k) = ((k + 1 : ℕ) : ENNReal)⁻¹ := by
  unfold diagonalSlack
  rw [ENNReal.ofReal_div_of_pos (by positivity)]
  simp only [ENNReal.ofReal_one, ENNReal.ofReal_natCast, one_div]

/-- The distortion error remaining at diagonal precision `k`. -/
noncomputable def diagonalDistortionError
    (d : Distortion (X := X) (Y := Y)) (k : ℕ) : ENNReal :=
  ENNReal.ofReal (diagonalSlack k) + (distortionBound d : ENNReal) *
    (3 * ENNReal.ofReal (diagonalSlack k))

theorem diagonalDistortionError_small
    (d : Distortion (X := X) (Y := Y)) :
    ∀ ε : ENNReal, 0 < ε → ∃ K : ℕ,
      ∀ k : ℕ, K ≤ k → diagonalDistortionError d k ≤ ε := by
  intro ε hε
  let c : ENNReal := 1 + (distortionBound d : ENNReal) * 3
  have hcTop : c ≠ ⊤ := by
    dsimp [c]
    finiteness
  obtain ⟨K, hKpos, hK⟩ := ENNReal.exists_nat_pos_inv_mul_lt hcTop hε.ne'
  refine ⟨K, fun k hk => ?_⟩
  have hKle : (K : ENNReal) ≤ ((k + 1 : ℕ) : ENNReal) := by
    exact_mod_cast (Nat.le_succ_of_le hk)
  have hinv : ((k + 1 : ℕ) : ENNReal)⁻¹ ≤ (K : ENNReal)⁻¹ :=
    ENNReal.inv_le_inv' hKle
  have herr : diagonalDistortionError d k =
      c * ((k + 1 : ℕ) : ENNReal)⁻¹ := by
    unfold diagonalDistortionError
    rw [ennreal_ofReal_diagonalSlack]
    dsimp [c]
    ring
  rw [herr]
  calc
    c * ((k + 1 : ℕ) : ENNReal)⁻¹ ≤ c * (K : ENNReal)⁻¹ :=
      mul_le_mul_right hinv c
    _ = (K : ENNReal)⁻¹ * c := mul_comm _ _
    _ ≤ ε := le_of_lt hK

/-- Diagonalize a family of codes that is available after a level-dependent
blocklength threshold.  The selected precision level increases without bound
along the resulting code sequence. -/
theorem exists_diagonalCodeSequence_of_eventually_codes
    (rate : ℝ) (hrate : 0 ≤ rate) [Nonempty Y]
    (P : PMF X) (d : Distortion (X := X) (Y := Y)) (D : ENNReal)
    (N : ℕ → ℕ) (error : ℕ → ENNReal)
    (hcode : ∀ k n : ℕ, N k ≤ n → ∃ hn : 0 < n,
      ∃ code : RateDistortionCode X Y n (exponentialCodebookSize n rate),
        codeRate n (exponentialCodebookSize n rate) hn ≤ rate ∧
        expectedDistortion n (exponentialCodebookSize n rate) hn code P d ≤
          D + error k) :
    ∃ seq : CodeSequence X Y,
      hasPointwiseRateBound seq rate ∧
      ∀ᶠ n in atTop,
        expectedDistortion (n + 1) (seq.M n) (Nat.succ_pos n)
          (seq.code n) P d ≤ D + error (activePrecisionLevel N n) := by
  classical
  let seq : CodeSequence X Y :=
    { M := fun n => exponentialCodebookSize (n + 1) rate
      hM := fun n => exponentialCodebookSize_pos (n + 1) rate hrate
      code := fun n => if h : N (activePrecisionLevel N n) ≤ n + 1 then
        (hcode (activePrecisionLevel N n) (n + 1) h).choose_spec.choose else
        constantRateDistortionCode (n + 1)
          (exponentialCodebookSize (n + 1) rate)
          (exponentialCodebookSize_pos (n + 1) rate hrate) }
  refine ⟨seq, ?_, ?_⟩
  · intro n
    change codeRate (n + 1) (exponentialCodebookSize (n + 1) rate)
      (Nat.succ_pos n) ≤ rate
    exact codeRate_exponentialCodebookSize_le (n := n + 1)
      (Nat.succ_pos n) rate hrate
  · have hactive : ∀ᶠ n in atTop, 1 ≤ activePrecisionLevel N n :=
      eventually_le_activePrecisionLevel N 1
    have hthreshold : ∀ᶠ n in atTop,
        N (activePrecisionLevel N n) ≤ n + 1 := by
      filter_upwards [hactive] with n hn
      rcases activePrecisionLevel_eq_zero_or_threshold_le N n with hzero | hthreshold
      · omega
      · exact hthreshold
    filter_upwards [hthreshold] with n hn
    change expectedDistortion (n + 1) (exponentialCodebookSize (n + 1) rate)
      (Nat.succ_pos n) (if h : N (activePrecisionLevel N n) ≤ n + 1 then
        (hcode (activePrecisionLevel N n) (n + 1) h).choose_spec.choose else
        constantRateDistortionCode (n + 1)
          (exponentialCodebookSize (n + 1) rate)
          (exponentialCodebookSize_pos (n + 1) rate hrate)) P d ≤
        D + error (activePrecisionLevel N n)
    simpa only [dif_pos hn] using
      (hcode (activePrecisionLevel N n) (n + 1) hn).choose_spec.choose_spec.2

/-- Turn codes available at all sufficiently large blocklengths into a full
code sequence.  A constant code supplies the finitely many initial terms. -/
theorem exists_codeSequence_of_eventually_exponentialCode
    (rate : ℝ) (hrate : 0 ≤ rate) [Nonempty Y]
    (P : PMF X) (d : Distortion (X := X) (Y := Y)) (B : ℕ → ENNReal) (N : ℕ)
    (hcode : ∀ k : ℕ, N ≤ k + 1 →
      ∃ code : RateDistortionCode X Y (k + 1)
        (exponentialCodebookSize (k + 1) rate),
        codeRate (k + 1) (exponentialCodebookSize (k + 1) rate)
          (Nat.succ_pos k) ≤ rate ∧
        expectedDistortion (k + 1) (exponentialCodebookSize (k + 1) rate)
          (Nat.succ_pos k) code P d ≤ B k) :
    ∃ seq : CodeSequence X Y,
      hasPointwiseRateBound seq rate ∧
      ∀ᶠ k in atTop,
        expectedDistortion (k + 1) (seq.M k) (Nat.succ_pos k)
          (seq.code k) P d ≤ B k := by
  classical
  let seq : CodeSequence X Y :=
    { M := fun k => exponentialCodebookSize (k + 1) rate
      hM := fun k => exponentialCodebookSize_pos (k + 1) rate hrate
      code := fun k => if hk : N ≤ k + 1 then (hcode k hk).choose else
        constantRateDistortionCode (k + 1)
          (exponentialCodebookSize (k + 1) rate)
          (exponentialCodebookSize_pos (k + 1) rate hrate) }
  refine ⟨seq, ?_, ?_⟩
  · intro k
    change codeRate (k + 1) (exponentialCodebookSize (k + 1) rate)
      (Nat.succ_pos k) ≤ rate
    exact codeRate_exponentialCodebookSize_le (n := k + 1)
      (Nat.succ_pos k) rate hrate
  · filter_upwards [eventually_atTop.2 ⟨N, fun k hk =>
      hk.trans (Nat.le_succ k)⟩] with k hk
    change expectedDistortion (k + 1) (exponentialCodebookSize (k + 1) rate)
      (Nat.succ_pos k) (if h : N ≤ k + 1 then (hcode k h).choose else
        constantRateDistortionCode (k + 1)
          (exponentialCodebookSize (k + 1) rate)
          (exponentialCodebookSize_pos (k + 1) rate hrate)) P d ≤ B k
    simpa only [dif_pos hk] using (hcode k hk).choose_spec.2

/-- Fixed positive slacks give a complete code sequence whose eventual
distortion bound retains the double-exponentially decaying covering error. -/
theorem exists_codeSequence_fixed_slack_bound
    (rate threshold : ℝ) (hgap : threshold < rate) [Nonempty Y]
    (P : PMF X) (W : X → PMF Y)
    (d : Distortion (X := X) (Y := Y))
    (distortionThreshold : ENNReal) (εd εi δ : ℝ)
    (hεd : 0 < εd) (hεi : 0 < εi) (hδ : 0 < δ) (hδle : δ ≤ 1)
    (hdistortionThreshold : distortionThreshold ≠ ⊤)
    (hdistortionSlack : (expected_distortion_single P W d).toReal + εd ≤
      distortionThreshold.toReal)
    (hinformationSlack : mutualInformationEntropy (induced_joint P W) + εi ≤ threshold) :
    ∃ seq : CodeSequence X Y,
      hasPointwiseRateBound seq rate ∧
      ∀ᶠ k in atTop,
        expectedDistortion (k + 1) (seq.M k) (Nat.succ_pos k)
          (seq.code k) P d ≤
          distortionThreshold + (distortionBound d : ENNReal) *
            (2 * ENNReal.ofReal δ + ENNReal.ofReal (Real.exp (-(1 / 4 *
              Real.exp (((k + 1 : ℕ) : ℝ) * (rate - threshold)))))) := by
  have hthresholdPos : 0 < threshold := by
    have hIpos : 0 < mutualInformationEntropy (induced_joint P W) + εi :=
      add_pos_of_nonneg_of_pos
        (mutualInformationEntropy_nonneg (induced_joint P W)) hεi
    exact lt_of_lt_of_le hIpos hinformationSlack
  have hrateNonneg : 0 ≤ rate := (hthresholdPos.trans hgap).le
  obtain ⟨N, _, hcodes⟩ :=
    exists_nat_forall_exists_exponentialCode_rate_and_expectedDistortion
      rate threshold hgap P W d distortionThreshold εd εi δ hεd hεi hδ hδle
      hdistortionThreshold hdistortionSlack hinformationSlack
  refine exists_codeSequence_of_eventually_exponentialCode rate hrateNonneg P d
    (fun k => distortionThreshold + (distortionBound d : ENNReal) *
      (2 * ENNReal.ofReal δ + ENNReal.ofReal (Real.exp (-(1 / 4 *
        Real.exp (((k + 1 : ℕ) : ℝ) * (rate - threshold)))))) ) N ?_
  intro k hk
  obtain ⟨hn, code, hrate, hdist⟩ := hcodes (k + 1) hk
  exact ⟨code, by simpa using hrate, by simpa using hdist⟩

-- asymptotic expected distortion of a sequence of rate-distortion codes
def asymptoticDistortion
    (seq : CodeSequence X Y)
    (P : PMF X)
    (d : Distortion (X := X) (Y := Y)) : ENNReal :=
  Filter.limsup
    (fun n ↦ expectedDistortion (n + 1) (seq.M n) (Nat.succ_pos n)
      (seq.code n) P d)
    atTop

-- The limsup rate used in the asymptotic-rate notion of achievability.
def asymptoticRate
    (seq : CodeSequence X Y) : ENNReal :=
  Filter.limsup
    (fun n ↦ ENNReal.ofReal
      (codeRate (n + 1) (seq.M n) (Nat.succ_pos n)))
    atTop

-- Achievabilty
-- limsup_n E[d(X^n, Y^n)] ≤ D
def achievesDistortion
    (seq : CodeSequence X Y)
    (P : PMF X)
    (d : Distortion (X := X) (Y := Y))
    (D : ENNReal) : Prop :=
  asymptoticDistortion seq P d ≤ D

/-- An eventually valid diagonal error bound yields asymptotic distortion at
most `D` when the error becomes arbitrarily small at high precision levels. -/
theorem asymptoticDistortion_le_of_diagonal_error
    (seq : CodeSequence X Y) (P : PMF X)
    (d : Distortion (X := X) (Y := Y)) (D : ENNReal)
    (N : ℕ → ℕ) (error : ℕ → ENNReal)
    (hbound : ∀ᶠ n in atTop,
      expectedDistortion (n + 1) (seq.M n) (Nat.succ_pos n)
        (seq.code n) P d ≤ D + error (activePrecisionLevel N n))
    (hsmall : ∀ ε : ENNReal, 0 < ε → ∃ K : ℕ,
      ∀ k : ℕ, K ≤ k → error k ≤ ε) :
    asymptoticDistortion seq P d ≤ D := by
  have herror : ∀ ε : ENNReal, 0 < ε →
      ∀ᶠ n in atTop, error (activePrecisionLevel N n) ≤ ε := by
    intro ε hε
    obtain ⟨K, hK⟩ := hsmall ε hε
    filter_upwards [eventually_le_activePrecisionLevel N K] with n hn
    exact hK (activePrecisionLevel N n) hn
  unfold asymptoticDistortion
  apply (limsup_le_iff' (f := atTop)
    (u := fun n => expectedDistortion (n + 1) (seq.M n) (Nat.succ_pos n)
      (seq.code n) P d)
    (by isBoundedDefault) (by isBoundedDefault)).mpr
  intro a ha
  have hsub : 0 < a - D := tsub_pos_iff_lt.mpr ha
  filter_upwards [hbound, herror (a - D) hsub] with n hn herrorn
  calc
    expectedDistortion (n + 1) (seq.M n) (Nat.succ_pos n)
        (seq.code n) P d ≤ D + error (activePrecisionLevel N n) := hn
    _ ≤ D + (a - D) := by simpa [add_comm] using add_le_add_left herrorn D
    _ = a := by
      rw [add_comm, tsub_add_cancel_of_le (le_of_lt ha)]

/-- The double-exponential covering remainder is eventually at most `δ`, so a
fixed-slack construction has the displayed asymptotic distortion bound. -/
theorem exists_codeSequence_fixed_slack_asymptoticBound
    (rate threshold : ℝ) (hgap : threshold < rate) [Nonempty Y]
    (P : PMF X) (W : X → PMF Y)
    (d : Distortion (X := X) (Y := Y))
    (distortionThreshold : ENNReal) (εd εi δ : ℝ)
    (hεd : 0 < εd) (hεi : 0 < εi) (hδ : 0 < δ) (hδle : δ ≤ 1)
    (hdistortionThreshold : distortionThreshold ≠ ⊤)
    (hdistortionSlack : (expected_distortion_single P W d).toReal + εd ≤
      distortionThreshold.toReal)
    (hinformationSlack : mutualInformationEntropy (induced_joint P W) + εi ≤ threshold) :
    ∃ seq : CodeSequence X Y,
      hasPointwiseRateBound seq rate ∧
      asymptoticDistortion seq P d ≤
        distortionThreshold + (distortionBound d : ENNReal) *
          (3 * ENNReal.ofReal δ) := by
  obtain ⟨seq, hrate, hdist⟩ := exists_codeSequence_fixed_slack_bound
    rate threshold hgap P W d distortionThreshold εd εi δ hεd hεi hδ hδle
    hdistortionThreshold hdistortionSlack hinformationSlack
  obtain ⟨N, hN⟩ := exists_nat_exp_neg_quarter_exp_nat_mul_lt
    (rate - threshold) δ (sub_pos.mpr hgap) hδ
  have htail : ∀ᶠ k in atTop,
      ENNReal.ofReal (Real.exp (-(1 / 4 *
        Real.exp (((k + 1 : ℕ) : ℝ) * (rate - threshold))))) ≤
        ENNReal.ofReal δ := by
    filter_upwards [eventually_atTop.2 ⟨N, fun k hk =>
      hk.trans (Nat.le_succ k)⟩] with k hk
    exact ENNReal.ofReal_le_ofReal
      (le_of_lt (hN (k + 1) hk))
  have hbound : ∀ᶠ k in atTop,
      expectedDistortion (k + 1) (seq.M k) (Nat.succ_pos k)
        (seq.code k) P d ≤
        distortionThreshold + (distortionBound d : ENNReal) *
          (3 * ENNReal.ofReal δ) := by
    filter_upwards [hdist, htail] with k hk htailk
    refine hk.trans ?_
    calc
      distortionThreshold + (distortionBound d : ENNReal) *
          (2 * ENNReal.ofReal δ + ENNReal.ofReal (Real.exp (-(1 / 4 *
            Real.exp (((k + 1 : ℕ) : ℝ) * (rate - threshold)))))) ≤
          distortionThreshold + (distortionBound d : ENNReal) *
            (2 * ENNReal.ofReal δ + ENNReal.ofReal δ) := by
              gcongr
      _ = distortionThreshold + (distortionBound d : ENNReal) *
          (3 * ENNReal.ofReal δ) := by ring
  refine ⟨seq, hrate, ?_⟩
  simpa [asymptoticDistortion] using
    (limsup_le_of_le (f := atTop)
      (u := fun k => expectedDistortion (k + 1) (seq.M k) (Nat.succ_pos k)
        (seq.code k) P d)
      (a := distortionThreshold + (distortionBound d : ENNReal) *
        (3 * ENNReal.ofReal δ))
      (by isBoundedDefault) hbound)

/-- For a fixed test channel and fixed positive slacks, every sufficiently
large blocklength admits a code with the stated simplified error bound. -/
theorem exists_nat_forall_exists_testChannelCode_bound
    (P : PMF X) (W : X → PMF Y)
    (d : Distortion (X := X) (Y := Y)) (D : ENNReal) (R : ℝ)
    (hDtop : D ≠ ⊤)
    (hW : expected_distortion_single P W d ≤ D)
    (hI : mutualInformationEntropy (induced_joint P W) < R)
    (η δ : ℝ) (hη : 0 < η) (hδ : 0 < δ) (hδle : δ ≤ 1) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∃ hn : 0 < n,
      ∃ code : RateDistortionCode X Y n (exponentialCodebookSize n R),
        codeRate n (exponentialCodebookSize n R) hn ≤ R ∧
        expectedDistortion n (exponentialCodebookSize n R) hn code P d ≤
          D + ENNReal.ofReal η + (distortionBound d : ENNReal) *
            (3 * ENNReal.ofReal δ) := by
  have hgap : (mutualInformationEntropy (induced_joint P W) + R) / 2 < R := by
    linarith
  have hεd : 0 < η / 2 := by linarith
  have hεi : 0 < (R - mutualInformationEntropy (induced_joint P W)) / 4 := by
    linarith
  have hthresholdTop : D + ENNReal.ofReal η ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨hDtop, ENNReal.ofReal_ne_top⟩
  have hdistortionSlack : (expected_distortion_single P W d).toReal + η / 2 ≤
      (D + ENNReal.ofReal η).toReal := by
    rw [ENNReal.toReal_add hDtop ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hη.le]
    have htoReal := ENNReal.toReal_mono hDtop hW
    linarith
  have hinformationSlack : mutualInformationEntropy (induced_joint P W) +
      (R - mutualInformationEntropy (induced_joint P W)) / 4 ≤
      (mutualInformationEntropy (induced_joint P W) + R) / 2 := by
    linarith
  obtain ⟨Ncode, _, hcodes⟩ :=
    exists_nat_forall_exists_exponentialCode_rate_and_expectedDistortion
      R ((mutualInformationEntropy (induced_joint P W) + R) / 2) hgap
      P W d (D + ENNReal.ofReal η) (η / 2)
      ((R - mutualInformationEntropy (induced_joint P W)) / 4) δ
      hεd hεi hδ hδle hthresholdTop hdistortionSlack hinformationSlack
  obtain ⟨Ntail, htail⟩ := exists_nat_exp_neg_quarter_exp_nat_mul_lt
    (R - (mutualInformationEntropy (induced_joint P W) + R) / 2) δ
    (sub_pos.mpr hgap) hδ
  refine ⟨max Ncode Ntail, ?_⟩
  intro n hn
  obtain ⟨hnpos, code, hrate, hdist⟩ :=
    hcodes n ((Nat.le_max_left _ _).trans hn)
  refine ⟨hnpos, code, hrate, hdist.trans ?_⟩
  have hcover : ENNReal.ofReal (Real.exp (-(1 / 4 *
      Real.exp ((n : ℝ) * (R - (mutualInformationEntropy (induced_joint P W) + R) / 2))))) ≤
      ENNReal.ofReal δ :=
    ENNReal.ofReal_le_ofReal (le_of_lt
      (htail n ((Nat.le_max_right _ _).trans hn)))
  calc
    D + ENNReal.ofReal η + (distortionBound d : ENNReal) *
        (2 * ENNReal.ofReal δ + ENNReal.ofReal (Real.exp (-(1 / 4 *
          Real.exp ((n : ℝ) * (R - (mutualInformationEntropy (induced_joint P W) + R) / 2)))))) ≤
        D + ENNReal.ofReal η + (distortionBound d : ENNReal) *
          (2 * ENNReal.ofReal δ + ENNReal.ofReal δ) := by
            gcongr
    _ = D + ENNReal.ofReal η + (distortionBound d : ENNReal) *
        (3 * ENNReal.ofReal δ) := by ring

/-- Specialization of the fixed-slack construction to a test channel whose
mutual information is strictly below the target rate. -/
theorem exists_codeSequence_testChannel_asymptoticBound
    (P : PMF X) (W : X → PMF Y)
    (d : Distortion (X := X) (Y := Y)) (D : ENNReal) (R : ℝ)
    (hDtop : D ≠ ⊤)
    (hW : expected_distortion_single P W d ≤ D)
    (hI : mutualInformationEntropy (induced_joint P W) < R)
    (η δ : ℝ) (hη : 0 < η) (hδ : 0 < δ) (hδle : δ ≤ 1) :
    ∃ seq : CodeSequence X Y,
      hasPointwiseRateBound seq R ∧
      asymptoticDistortion seq P d ≤
        D + ENNReal.ofReal η + (distortionBound d : ENNReal) *
          (3 * ENNReal.ofReal δ) := by
  letI : Nonempty Y := nonempty_reproduction_of_source_channel P W
  have hgap : (mutualInformationEntropy (induced_joint P W) + R) / 2 < R := by
    linarith
  have hεd : 0 < η / 2 := by linarith
  have hεi : 0 < (R - mutualInformationEntropy (induced_joint P W)) / 4 := by
    linarith
  have hthresholdTop : D + ENNReal.ofReal η ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨hDtop, ENNReal.ofReal_ne_top⟩
  have hdistortionSlack : (expected_distortion_single P W d).toReal + η / 2 ≤
      (D + ENNReal.ofReal η).toReal := by
    rw [ENNReal.toReal_add hDtop ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hη.le]
    have htoReal := ENNReal.toReal_mono hDtop hW
    linarith
  have hinformationSlack : mutualInformationEntropy (induced_joint P W) +
      (R - mutualInformationEntropy (induced_joint P W)) / 4 ≤
      (mutualInformationEntropy (induced_joint P W) + R) / 2 := by
    linarith
  simpa using exists_codeSequence_fixed_slack_asymptoticBound
    R ((mutualInformationEntropy (induced_joint P W) + R) / 2) hgap
    P W d (D + ENNReal.ofReal η) (η / 2)
    ((R - mutualInformationEntropy (induced_joint P W)) / 4) δ
    hεd hεi hδ hδle hthresholdTop hdistortionSlack hinformationSlack






/-- Achievability with an asymptotic rate constraint: both the rate and
the expected distortion are bounded through their limsups. The manuscript's
pointwise rate requirement is recorded separately in `isAchievablePointwise`. -/
def isAchievable (P : PMF X) (d : Distortion (X := X) (Y := Y)) (R : ℝ) (D : ENNReal) : Prop :=
  ∃ seq : CodeSequence X Y,
    asymptoticRate seq ≤ ENNReal.ofReal R ∧ achievesDistortion seq P d D

/-- Achievability with the rate requirement of Definition 5.2 in the manuscript:
every code has rate at most R, and the limsup of expected distortion is at most D.
Rates are measured using natural logarithms throughout this development. -/
def isAchievablePointwise
    (P : PMF X) (d : Distortion (X := X) (Y := Y)) (R : ℝ) (D : ENNReal) : Prop :=
  ∃ seq : CodeSequence X Y,
    hasPointwiseRateBound seq R ∧ achievesDistortion seq P d D

/-- A test channel whose distortion and mutual information satisfy the strict
direct-theorem hypotheses yields one code sequence achieving its distortion
target.  The blocklength thresholds for shrinking slacks are diagonalized. -/
theorem exists_codeSequence_testChannel_achieves
    (P : PMF X) (W : X → PMF Y)
    (d : Distortion (X := X) (Y := Y)) (D : ENNReal) (R : ℝ)
    (hDtop : D ≠ ⊤)
    (hW : expected_distortion_single P W d ≤ D)
    (hI : mutualInformationEntropy (induced_joint P W) < R) :
    ∃ seq : CodeSequence X Y,
      hasPointwiseRateBound seq R ∧ asymptoticDistortion seq P d ≤ D := by
  classical
  letI : Nonempty Y := nonempty_reproduction_of_source_channel P W
  have hRpos : 0 < R :=
    (mutualInformationEntropy_nonneg (induced_joint P W)).trans_lt hI
  choose N hN using fun k =>
    exists_nat_forall_exists_testChannelCode_bound P W d D R hDtop hW hI
      (diagonalSlack k) (diagonalSlack k) (diagonalSlack_pos k)
      (diagonalSlack_pos k) (diagonalSlack_le_one k)
  obtain ⟨seq, hrate, hbound⟩ :=
    exists_diagonalCodeSequence_of_eventually_codes R hRpos.le P d D N
      (diagonalDistortionError d) (by
        intro k n hn
        simpa [diagonalDistortionError, add_assoc] using hN k n hn)
  refine ⟨seq, hrate, ?_⟩
  exact asymptoticDistortion_le_of_diagonal_error seq P d D N
    (diagonalDistortionError d) hbound (diagonalDistortionError_small d)

/-
  Right-continuity at the distortion level is the additional analytic fact
  needed to remove the positive slack from the asymptotic converse.  The
  source filter expresses `ε ↓ 0`, rather than equality at every positive
  increment.
-/
def rateDistortionRightContinuousAt
    (P : PMF X) (d : Distortion (X := X) (Y := Y)) (D : ENNReal) : Prop :=
  Tendsto
    (fun ε : ENNReal ↦ RateDistortionFunction P d (D + ε))
    (nhdsWithin (0 : ENNReal) (Set.Ioi 0))
    (𝓝 (RateDistortionFunction P d D))

/-! Compactness and continuity for finite-alphabet rate-distortion optimization. -/

/-- The topology of pointwise convergence on probability mass functions. -/
instance PMF.instTopologicalSpace {A : Type*} : TopologicalSpace (PMF A) :=
  inferInstanceAs (TopologicalSpace {f : A → ENNReal // HasSum f 1})

theorem PMF.continuous_apply {A : Type*} (a : A) :
    Continuous (fun p : PMF A => p a) :=
  (_root_.continuous_apply a).comp continuous_subtype_val

/-- On a finite alphabet, normalization defines a closed subset of a compact product. -/
instance PMF.instCompactSpace {A : Type*} [Fintype A] : CompactSpace (PMF A) := by
  have heq : {f : A → ENNReal | HasSum f 1} = {f | ∑ a, f a = 1} := by
    ext f
    exact ⟨fun h => (hasSum_fintype f).unique h, fun h => h ▸ hasSum_fintype f⟩
  have hc : IsClosed {f : A → ENNReal | HasSum f 1} := by
    rw [heq]
    exact isClosed_eq (continuous_finset_sum _ (fun a _ => _root_.continuous_apply a)) continuous_const
  exact isCompact_iff_compactSpace.mp hc.isCompact

theorem PMF.continuous_toReal_apply {A : Type*} (a : A) :
    Continuous (fun p : PMF A => (p a).toReal) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  exact ContinuousAt.comp (f := fun q : PMF A => q a)
    (ENNReal.continuousAt_toReal (p.apply_ne_top a))
    (PMF.continuous_apply a).continuousAt

theorem PMF.continuous_map_finite (f : X → Y) :
    Continuous (fun p : PMF X => p.map f) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro y
  change Continuous (fun p : PMF X => p.map f y)
  simp only [PMF.map_apply, tsum_fintype]
  apply continuous_finset_sum
  intro x _
  by_cases h : y = f x
  · simpa [h] using PMF.continuous_apply x
  · simpa [h] using (continuous_const : Continuous (fun _ : PMF X => (0 : ENNReal)))

theorem continuous_shannonEntropy : Continuous (shannonEntropy (X := X)) := by
  unfold shannonEntropy
  apply continuous_finset_sum
  intro x _
  exact Real.continuous_negMulLog.comp (PMF.continuous_toReal_apply x)

theorem continuous_mutualInformationEntropy :
    Continuous (mutualInformationEntropy (X := X) (Y := Y)) := by
  exact ((continuous_shannonEntropy.comp (PMF.continuous_map_finite Prod.fst)).add
    (continuous_shannonEntropy.comp (PMF.continuous_map_finite Prod.snd))).sub
      continuous_shannonEntropy

theorem continuous_mutual_information :
    Continuous (mutual_information (X := X) (Y := Y)) := by
  change Continuous (fun Q : PMF (X × Y) => mutual_information Q)
  simp_rw [mutual_information_eq_ofReal_entropy]
  exact ENNReal.continuous_ofReal.comp continuous_mutualInformationEntropy

theorem continuous_induced_joint (P : PMF X) :
    Continuous (induced_joint (Y := Y) P) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro z
  change Continuous (fun W : X → PMF Y => induced_joint P W (z.1, z.2))
  simp_rw [induced_joint_apply]
  exact (ENNReal.continuous_const_mul (P.apply_ne_top z.1)).comp
    ((PMF.continuous_apply z.2).comp (continuous_apply z.1))

theorem continuous_expected_distortion_single
    (P : PMF X) (d : Distortion (X := X) (Y := Y)) :
    Continuous (fun W : X → PMF Y => expected_distortion_single P W d) := by
  unfold expected_distortion_single
  apply continuous_finset_sum
  intro x _
  apply (ENNReal.continuous_const_mul (P.apply_ne_top x)).comp
  apply continuous_finset_sum
  intro y _
  exact (ENNReal.continuous_mul_const ENNReal.coe_ne_top).comp
    ((PMF.continuous_apply y).comp (continuous_apply x))

/-- A feasible finite-alphabet rate-distortion problem has an optimal test channel. -/
theorem RateDistortionFunction_attained
    (P : PMF X) (d : Distortion (X := X) (Y := Y)) (D : ENNReal)
    (hD : feasibleDistortion P d D) :
    ∃ W : X → PMF Y, expected_distortion_single P W d ≤ D ∧
      mutual_information (induced_joint P W) = RateDistortionFunction P d D := by
  have hc : IsCompact {W : X → PMF Y | expected_distortion_single P W d ≤ D} :=
    (isClosed_le (continuous_expected_distortion_single P d) continuous_const).isCompact
  obtain ⟨W, hW, hmin⟩ := hc.exists_isMinOn hD
    (continuous_mutual_information.comp (continuous_induced_joint P)).continuousOn
  refine ⟨W, hW, le_antisymm ?_ (RateDistortionFunction_le P d D W hW)⟩
  apply le_sInf
  rintro r ⟨V, hV, rfl⟩
  exact hmin hV

/-- Compactness keeps sublevel sets closed, including at the least feasible
distortion. Empty feasible sets are represented by the value infinity. -/
theorem lowerSemicontinuous_RateDistortionFunction
    (P : PMF X) (d : Distortion (X := X) (Y := Y)) :
    LowerSemicontinuous (RateDistortionFunction P d) := by
  apply lowerSemicontinuous_iff_isClosed_preimage.mpr
  intro r
  by_cases hr : r = ⊤
  · subst r
    simp
  have heq : (RateDistortionFunction P d) ⁻¹' Set.Iic r =
      Prod.fst '' {z : ENNReal × (X → PMF Y) |
        expected_distortion_single P z.2 d ≤ z.1 ∧
          mutual_information (induced_joint P z.2) ≤ r} := by
    ext D
    constructor
    · intro hD
      obtain ⟨V, hV, _⟩ := exists_testChannel_of_RateDistortionFunction_lt P d D ⊤
        (lt_of_le_of_lt hD (lt_top_iff_ne_top.mpr hr))
      obtain ⟨W, hW, hI⟩ := RateDistortionFunction_attained P d D ⟨V, hV⟩
      exact ⟨(D, W), ⟨hW, hI.le.trans hD⟩, rfl⟩
    · rintro ⟨⟨D', W⟩, ⟨hW, hI⟩, rfl⟩
      exact (RateDistortionFunction_le P d D' W hW).trans hI
  rw [heq]
  apply IsCompact.isClosed
  apply IsCompact.image _ continuous_fst
  apply IsClosed.isCompact
  exact (isClosed_le ((continuous_expected_distortion_single P d).comp continuous_snd)
    continuous_fst).inter
    (isClosed_le ((continuous_mutual_information.comp
      (continuous_induced_joint P)).comp continuous_snd) continuous_const)

/-- Right continuity holds at every extended nonnegative distortion threshold. -/
theorem rateDistortionRightContinuousAt_all
    (P : PMF X) (d : Distortion (X := X) (Y := Y)) (D : ENNReal) :
    rateDistortionRightContinuousAt P d D := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    have hevent : ∀ᶠ t in 𝓝 D, a < RateDistortionFunction P d t :=
      lowerSemicontinuous_RateDistortionFunction P d D a ha
    have hadd : Tendsto (fun ε : ENNReal => D + ε)
        (nhdsWithin (0 : ENNReal) (Set.Ioi 0)) (𝓝 D) := by
      simpa using ((continuous_const.add continuous_id).continuousAt
        (x := (0 : ENNReal))).tendsto.mono_left nhdsWithin_le_nhds
    exact hadd.eventually hevent
  · intro b hb
    exact Filter.Eventually.of_forall fun ε =>
      (RateDistortionFunction_antitone P d (le_add_right le_rfl)).trans_lt hb


theorem rateDistortionRightContinuousAt_of_interior
    (P : PMF X) (d : Distortion (X := X) (Y := Y)) (D : ENNReal)
    (hDint : interiorDistortion P d D) :
    rateDistortionRightContinuousAt P d D := by
  have hminlt := hDint.1
  unfold minimumDistortion at hminlt
  obtain ⟨r, ⟨W₀, rfl⟩, hW₀lt⟩ := sInf_lt_iff.mp hminlt
  let D₀ := expected_distortion_single P W₀ d
  have hD₀ : D₀ < D := hW₀lt
  have hD₀feas : feasibleDistortion P d D₀ := ⟨W₀, le_rfl⟩
  have hDtop : D ≠ ⊤ :=
    ne_top_of_lt (hDint.2.trans_le le_top)
  have hRDtop : RateDistortionFunction P d D ≠ ⊤ :=
    RateDistortionFunction_ne_top_of_interior P d D hDint
  have hRD₀top : RateDistortionFunction P d D₀ ≠ ⊤ :=
    RateDistortionFunction_ne_top_of_feasible P d D₀ W₀ le_rfl
  have hc0 : D - D₀ ≠ 0 :=
    (tsub_pos_iff_lt.mpr hD₀).ne'
  have hctop : D - D₀ ≠ ⊤ :=
    ne_top_of_le_ne_top hDtop (tsub_le_self : D - D₀ ≤ D)
  have hlower : Tendsto
      (fun ε : ENNReal ↦
        RateDistortionFunction P d D -
          (ε / (D - D₀ + ε)) * RateDistortionFunction P d D₀)
      (nhdsWithin (0 : ENNReal) (Set.Ioi 0))
      (𝓝 (RateDistortionFunction P d D)) :=
    ennreal_tsub_barycentric_tendsto
      (RateDistortionFunction P d D)
      (RateDistortionFunction P d D₀)
      (D - D₀) hRDtop hRD₀top hc0 hctop
  have hupper : Tendsto
      (fun _ : ENNReal ↦ RateDistortionFunction P d D)
      (nhdsWithin (0 : ENNReal) (Set.Ioi 0))
      (𝓝 (RateDistortionFunction P d D)) :=
    tendsto_const_nhds
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper
  · filter_upwards [self_mem_nhdsWithin,
      Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (Iio_mem_nhds (show (0 : ENNReal) < 1 by norm_num))] with ε hε hεsmall
    have hεtop : ε ≠ ⊤ := ne_top_of_lt hεsmall
    obtain ⟨hab, hbar, hb⟩ :=
      ennreal_barycentric_weights D₀ D ε hD₀ hDtop hεtop
    have hDplus : feasibleDistortion P d (D + ε) :=
      feasibleDistortion_mono P d (le_add_right le_rfl)
        (interiorDistortion_feasible P d D hDint)
    have htsub := RateDistortionFunction_tsub_le_of_convex
      P d (ε / (D - D₀ + ε)) ((D - D₀) / (D - D₀ + ε)) hab
      D₀ (D + ε) hD₀feas hDplus hb
    rw [hbar] at htsub
    exact htsub
  · filter_upwards [] with ε
    exact RateDistortionFunction_antitone P d (le_add_right le_rfl)

/-
  The finite-block converse passes to the asymptotic definition with an
  arbitrarily small positive distortion slack.  This is the form that does
  not require a separate right-continuity theorem for the information
  rate-distortion function.
-/
theorem rate_distortion_sequence_converse_add
    (P : PMF X) (d : Distortion (X := X) (Y := Y)) (D ε : ENNReal)
    (seq : CodeSequence X Y)
    (hD : achievesDistortion seq P d D) (hε : 0 < ε) :
    RateDistortionFunction P d (D + ε) ≤ asymptoticRate seq := by
  let u : ℕ → ENNReal := fun n ↦
    expectedDistortion (n + 1) (seq.M n) (Nat.succ_pos n)
      (seq.code n) P d
  have hu_bdd : IsBoundedUnder (· ≤ ·) atTop u := by
    apply isBoundedUnder_of_eventually_le
    filter_upwards [] with n
    exact expectedDistortion_le_bound (n + 1) (seq.M n) (Nat.succ_pos n)
      (seq.code n) P d
  have hu_limsup : Filter.limsup u atTop ≤ D := by
    simpa [u, asymptoticDistortion] using hD
  have hu_event : ∀ᶠ n in atTop, u n < D + ε := by
    by_cases hDtop : D = ⊤
    · subst D
      filter_upwards [] with n
      exact (lt_of_le_of_lt
        (show u n ≤ (distortionBound d : ENNReal) from
          expectedDistortion_le_bound (n + 1) (seq.M n) (Nat.succ_pos n)
            (seq.code n) P d)
        ENNReal.coe_lt_top)
    · exact eventually_lt_of_limsup_lt
        (hu_limsup.trans_lt (ENNReal.lt_add_right hDtop hε.ne')) hu_bdd
  have hrate_event : ∀ᶠ n in atTop,
      RateDistortionFunction P d (D + ε) ≤
        ENNReal.ofReal (codeRate (n + 1) (seq.M n) (Nat.succ_pos n)) := by
    filter_upwards [hu_event] with n hn
    exact (RateDistortionFunction_antitone P d (le_of_lt hn)).trans
      (RateDistortionFunction_expectedDistortion_le_codeRate
        (n + 1) (seq.M n) (Nat.succ_pos n) (seq.code n) P d)
  have hrate_freq : ∃ᶠ n in atTop,
      RateDistortionFunction P d (D + ε) ≤
        ENNReal.ofReal (codeRate (n + 1) (seq.M n) (Nat.succ_pos n)) :=
    hrate_event.frequently
  simpa [asymptoticRate] using
    (le_limsup_of_frequently_le hrate_freq)

theorem rate_distortion_sequence_converse_of_eventually_le
    (P : PMF X) (d : Distortion (X := X) (Y := Y)) (D : ENNReal)
    (seq : CodeSequence X Y)
    (hD : ∀ᶠ n in atTop,
      expectedDistortion (n + 1) (seq.M n) (Nat.succ_pos n)
        (seq.code n) P d ≤ D) :
    RateDistortionFunction P d D ≤ asymptoticRate seq := by
  have hrate_event : ∀ᶠ n in atTop,
      RateDistortionFunction P d D ≤
        ENNReal.ofReal (codeRate (n + 1) (seq.M n) (Nat.succ_pos n)) := by
    filter_upwards [hD] with n hn
    exact (RateDistortionFunction_antitone P d hn).trans
      (RateDistortionFunction_expectedDistortion_le_codeRate
        (n + 1) (seq.M n) (Nat.succ_pos n) (seq.code n) P d)
  simpa [asymptoticRate] using
    (le_limsup_of_frequently_le hrate_event.frequently)

theorem asymptoticRate_le_of_hasPointwiseRateBound
    (seq : CodeSequence X Y) (R : ℝ)
    (hR : hasPointwiseRateBound seq R) :
    asymptoticRate seq ≤ ENNReal.ofReal R := by
  simpa [asymptoticRate] using
    (limsup_le_of_le (f := atTop)
      (u := fun n ↦ ENNReal.ofReal
        (codeRate (n + 1) (seq.M n) (Nat.succ_pos n)))
      (a := ENNReal.ofReal R) (by isBoundedDefault)
      (Filter.Eventually.of_forall fun n ↦ ENNReal.ofReal_mono (hR n)))

/-- A pointwise rate bound implies the asymptotic rate bound for the same codes. -/
theorem isAchievablePointwise_imp_isAchievable
    (P : PMF X) (d : Distortion (X := X) (Y := Y)) (R : ℝ) (D : ENNReal)
    (hA : isAchievablePointwise P d R D) :
    isAchievable P d R D := by
  obtain ⟨seq, hrate, hdist⟩ := hA
  exact ⟨seq, asymptoticRate_le_of_hasPointwiseRateBound seq R hrate, hdist⟩

/-- At infinite distortion a constant-reconstruction sequence satisfies
the pointwise rate requirement at every nonnegative rate. -/
theorem isAchievablePointwise_top_of_nonneg_rate
    (P : PMF X) (d : Distortion (X := X) (Y := Y)) (R : ℝ)
    [Nonempty Y] (hR : 0 ≤ R) :
    isAchievablePointwise P d R ⊤ := by
  let seq := constantExponentialCodeSequence (X := X) (Y := Y) R hR
  exact ⟨seq,
    constantExponentialCodeSequence_hasPointwiseRateBound (X := X) (Y := Y) R hR,
    le_top⟩

/-- At infinite distortion every nonnegative rate is operationally
achievable, since no distortion constraint remains. -/
theorem isAchievable_top_of_nonneg_rate
    (P : PMF X) (d : Distortion (X := X) (Y := Y)) (R : ℝ)
    [Nonempty Y] (hR : 0 ≤ R) :
    isAchievable P d R ⊤ := by
  let seq := constantExponentialCodeSequence (X := X) (Y := Y) R hR
  refine ⟨seq, ?_, ?_⟩
  · exact asymptoticRate_le_of_hasPointwiseRateBound seq R
      (constantExponentialCodeSequence_hasPointwiseRateBound (X := X) (Y := Y)
        R hR)
  · exact le_top

theorem rate_distortion_converse_add
    (P : PMF X) (d : Distortion (X := X) (Y := Y)) (D ε : ENNReal)
    (R : ℝ) (hε : 0 < ε) (hA : isAchievable P d R D) :
    RateDistortionFunction P d (D + ε) ≤ ENNReal.ofReal R := by
  obtain ⟨seq, hrate, hdist⟩ := hA
  exact (rate_distortion_sequence_converse_add P d D ε seq hdist hε).trans hrate

theorem rate_distortion_converse_of_rightContinuousAt
    (P : PMF X) (d : Distortion (X := X) (Y := Y)) (D : ENNReal)
    (R : ℝ) (hcont : rateDistortionRightContinuousAt P d D)
    (hA : isAchievable P d R D) :
    RateDistortionFunction P d D ≤ ENNReal.ofReal R := by
  unfold rateDistortionRightContinuousAt at hcont
  apply le_of_tendsto hcont
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact rate_distortion_converse_add P d D ε R hε hA

/-- Strict slack above RI(D) supplies codes satisfying the manuscript's
pointwise rate requirement. Feasibility follows from the strict inequality. -/
theorem isAchievablePointwise_of_rateDistortionFunction_lt
    (P : PMF X) (d : Distortion (X := X) (Y := Y)) (D : ENNReal) (R : ℝ)
    (hR : RateDistortionFunction P d D < ENNReal.ofReal R) :
    isAchievablePointwise P d R D := by
  obtain ⟨W, hW, hI⟩ :=
    exists_testChannel_of_RateDistortionFunction_lt_ofReal P d D R hR
  by_cases hDtop : D = ⊤
  · subst D
    letI : Nonempty Y := nonempty_reproduction_of_source_channel P W
    exact isAchievablePointwise_top_of_nonneg_rate P d R
      ((mutualInformationEntropy_nonneg (induced_joint P W)).trans_lt hI).le
  · exact exists_codeSequence_testChannel_achieves P W d D R hDtop hW hI

/-- The existing strict-rate asymptotic interface follows from the stronger
pointwise conclusion. Its feasibility argument is retained for compatibility. -/
theorem rate_distortion_achievability_strict
    (P : PMF X) (d : Distortion (X := X) (Y := Y)) (D : ENNReal)
    (R : ℝ)
    (hD : feasibleDistortion P d D)
    (hR : RateDistortionFunction P d D < ENNReal.ofReal R) :
    isAchievable P d R D := by
  clear hD
  exact isAchievablePointwise_imp_isAchievable P d R D
    (isAchievablePointwise_of_rateDistortionFunction_lt P d D R hR)

-- Equality-rate achievability and local continuity interfaces.

theorem ennreal_diagonalSlack_small :
    ∀ ε : ENNReal, 0 < ε → ∃ K : ℕ,
      ∀ k : ℕ, K ≤ k → ENNReal.ofReal (diagonalSlack k) ≤ ε := by
  intro ε hε
  obtain ⟨K, _, hK⟩ := ENNReal.exists_nat_pos_inv_mul_lt
    (show (1 : ENNReal) ≠ ⊤ by simp) hε.ne'
  refine ⟨K, fun k hk => ?_⟩
  rw [ennreal_ofReal_diagonalSlack]
  have hcast : (K : ENNReal) ≤ ((k + 1 : ℕ) : ENNReal) := by
    exact_mod_cast (Nat.le_succ_of_le hk)
  exact (ENNReal.inv_le_inv' hcast).trans (by simpa using hK.le)

/-- A vanishing positive rate slack is sufficient for the limsup rate bound. -/
theorem asymptoticRate_le_of_diagonal_slack
    (seq : CodeSequence X Y) (R : ℝ) (hR : 0 ≤ R) (N : ℕ → ℕ)
    (hbound : ∀ n, codeRate (n + 1) (seq.M n) (Nat.succ_pos n) ≤
      R + diagonalSlack (activePrecisionLevel N n)) :
    asymptoticRate seq ≤ ENNReal.ofReal R := by
  unfold asymptoticRate
  apply (limsup_le_iff' (by isBoundedDefault) (by isBoundedDefault)).mpr
  intro a ha
  obtain ⟨K, hK⟩ := ennreal_diagonalSlack_small (a - ENNReal.ofReal R)
    (tsub_pos_iff_lt.mpr ha)
  filter_upwards [eventually_le_activePrecisionLevel N K] with n hn
  calc
    ENNReal.ofReal (codeRate (n + 1) (seq.M n) (Nat.succ_pos n)) ≤
        ENNReal.ofReal (R + diagonalSlack (activePrecisionLevel N n)) :=
      ENNReal.ofReal_le_ofReal (hbound n)
    _ = ENNReal.ofReal R + ENNReal.ofReal (diagonalSlack (activePrecisionLevel N n)) :=
      ENNReal.ofReal_add hR (diagonalSlack_pos _).le
    _ ≤ ENNReal.ofReal R + (a - ENNReal.ofReal R) :=
      by simpa [add_comm] using add_le_add_left (hK _ hn) (ENNReal.ofReal R)
    _ = a := by rw [add_comm, tsub_add_cancel_of_le ha.le]

/-- Closed-rate achievability for finite distortion. The codebook rate may
exceed R at each finite blocklength, but its limsup is at most R. -/
theorem rate_distortion_achievability_of_finite_distortion
    (P : PMF X) (d : Distortion (X := X) (Y := Y))
    (D : ENNReal) (R : ℝ) (hDtop : D ≠ ⊤) (hR : 0 ≤ R)
    (hRD : RateDistortionFunction P d D ≤ ENNReal.ofReal R) :
    isAchievable P d R D := by
  classical
  have hstrict (k : ℕ) : RateDistortionFunction P d D <
      ENNReal.ofReal (R + diagonalSlack k) :=
    hRD.trans_lt ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg hR).mpr
      (lt_add_of_pos_right R (diagonalSlack_pos k)))
  choose W hW hI using fun k =>
    exists_testChannel_of_RateDistortionFunction_lt_ofReal P d D
      (R + diagonalSlack k) (hstrict k)
  letI : Nonempty Y := nonempty_reproduction_of_source_channel P (W 0)
  choose N hN using fun k => exists_nat_forall_exists_testChannelCode_bound
    P (W k) d D (R + diagonalSlack k) hDtop (hW k) (hI k)
    (diagonalSlack k) (diagonalSlack k) (diagonalSlack_pos k)
    (diagonalSlack_pos k) (diagonalSlack_le_one k)
  let rate := fun n => R + diagonalSlack (activePrecisionLevel N n)
  have hrate (n : ℕ) : 0 ≤ rate n := add_nonneg hR (diagonalSlack_pos _).le
  let seq : CodeSequence X Y :=
    { M := fun n => exponentialCodebookSize (n + 1) (rate n)
      hM := fun n => exponentialCodebookSize_pos (n + 1) (rate n) (hrate n)
      code := fun n => if h : N (activePrecisionLevel N n) ≤ n + 1 then
        (hN (activePrecisionLevel N n) (n + 1) h).choose_spec.choose else
        constantRateDistortionCode (n + 1)
          (exponentialCodebookSize (n + 1) (rate n))
          (exponentialCodebookSize_pos (n + 1) (rate n) (hrate n)) }
  refine ⟨seq, ?_, ?_⟩
  · apply asymptoticRate_le_of_diagonal_slack seq R hR N
    intro n
    exact codeRate_exponentialCodebookSize_le (n := n + 1)
      (Nat.succ_pos n) (rate n) (hrate n)
  · apply asymptoticDistortion_le_of_diagonal_error seq P d D N
      (diagonalDistortionError d) ?_ (diagonalDistortionError_small d)
    have hthreshold : ∀ᶠ n in atTop, N (activePrecisionLevel N n) ≤ n + 1 := by
      filter_upwards [eventually_le_activePrecisionLevel N 1] with n hn
      rcases activePrecisionLevel_eq_zero_or_threshold_le N n with hz | ht
      · omega
      · exact ht
    filter_upwards [hthreshold] with n hn
    change expectedDistortion (n + 1) (exponentialCodebookSize (n + 1) (rate n))
      (Nat.succ_pos n)
      (if h : N (activePrecisionLevel N n) ≤ n + 1 then
        (hN (activePrecisionLevel N n) (n + 1) h).choose_spec.choose else
        constantRateDistortionCode (n + 1)
          (exponentialCodebookSize (n + 1) (rate n))
          (exponentialCodebookSize_pos (n + 1) (rate n) (hrate n))) P d ≤ _
    simpa only [dif_pos hn, diagonalDistortionError, add_assoc] using
      (hN (activePrecisionLevel N n) (n + 1) hn).choose_spec.choose_spec.2

/-- The asymptotic converse also applies to manuscript achievability, using
the implication from a pointwise rate bound to a limsup rate bound. -/
theorem rate_distortion_converse_pointwise_of_rightContinuousAt
    (P : PMF X) (d : Distortion (X := X) (Y := Y)) (D : ENNReal)
    (R : ℝ) (hcont : rateDistortionRightContinuousAt P d D)
    (hA : isAchievablePointwise P d R D) :
    RateDistortionFunction P d D ≤ ENNReal.ofReal R := by
  exact rate_distortion_converse_of_rightContinuousAt P d D R hcont
    (isAchievablePointwise_imp_isAchievable P d R D hA)

/-! Pointwise achievability at the closed rate boundary. -/

/-- Zero finite-PMF mutual information characterizes the product of the marginals. -/
theorem mutual_information_eq_zero_iff_product (Q : PMF (X × Y)) :
    mutual_information Q = 0 ↔ Q = product_pmf (Q.map Prod.fst) (Q.map Prod.snd) := by
  letI : MeasurableSpace (X × Y) := ⊤
  letI : MeasurableSingletonClass (X × Y) := ⟨fun _ => trivial⟩
  change InformationTheory.klDiv Q.toMeasure
    (product_pmf (Q.map Prod.fst) (Q.map Prod.snd)).toMeasure = 0 ↔ _
  rw [InformationTheory.klDiv_eq_zero_iff, PMF.toMeasure_injective.eq_iff]

/-- A zero-information feasible channel admits a constant reproduction symbol. -/
theorem exists_constant_reproduction_of_zero_information
    (P : PMF X) (W : X → PMF Y) (d : Distortion (X := X) (Y := Y))
    (D : ENNReal) (hW : expected_distortion_single P W d ≤ D)
    (hI : mutual_information (induced_joint P W) = 0) :
    ∃ y : Y, (∑ x, P x * (d x y : ENNReal)) ≤ D := by
  have hj := (mutual_information_eq_zero_iff_product (induced_joint P W)).mp hI
  rw [induced_joint_fst, induced_joint_snd] at hj
  have hdist : expected_distortion_single P (fun _ => P.bind W) d =
      expected_distortion_single P W d := by
    rw [← jointExpectedDistortion_induced, ← jointExpectedDistortion_induced]
    congr 1
    exact hj.symm
  obtain ⟨y, hy⟩ := exists_le_pmf_weighted_sum (P.bind W)
    (fun y => ∑ x, P x * (d x y : ENNReal))
  refine ⟨y, hy.trans ?_⟩
  calc
    (∑ y, (P.bind W) y * ∑ x, P x * (d x y : ENNReal)) =
        expected_distortion_single P (fun _ => P.bind W) d := by
      unfold expected_distortion_single
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      ring
    _ ≤ D := hdist ▸ hW

/-- A one-codeword code with a prescribed constant reproduction symbol. -/
def constantSymbolCode (n : ℕ) (y : Y) : RateDistortionCode X Y n 1 where
  encoder := fun _ => ⟨0, Nat.zero_lt_one⟩
  decoder := fun _ _ => y

theorem expectedDistortion_constantSymbolCode
    (n : ℕ) (hn : 0 < n) (P : PMF X) (d : Distortion (X := X) (Y := Y))
    (y : Y) :
    expectedDistortion n 1 hn (constantSymbolCode n y) P d =
      ∑ x, P x * (d x y : ENNReal) := by
  simp only [expectedDistortion, blockDistortion, constantSymbolCode, tsum_fintype,
    div_eq_mul_inv, Finset.mul_sum, ← mul_assoc]
  rw [← Finset.sum_mul, Finset.sum_comm]
  have hcoord (i : Fin n) :
      (∑ x : Xblock n X, iidBlockPMF n P x * (d (x i) y : ENNReal)) =
        ∑ x : X, P x * (d x y : ENNReal) := by
    simpa only [iidBlockPMF_coordinate] using
      (sum_map_mul (iidBlockPMF n P) (fun x => x i)
        (fun x => (d x y : ENNReal))).symm
  simp_rw [hcoord]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hn0 : (n : ENNReal) ≠ 0 := by exact_mod_cast hn.ne'
  calc
    _ = (∑ x, P x * (d x y : ENNReal)) * ((n : ENNReal) * (n : ENNReal)⁻¹) := by
      ring
    _ = _ := by rw [ENNReal.mul_inv_cancel hn0 (ENNReal.natCast_ne_top n), mul_one]

theorem isAchievablePointwise_of_constant_reproduction
    (P : PMF X) (d : Distortion (X := X) (Y := Y)) (D : ENNReal)
    (y : Y) (hy : (∑ x, P x * (d x y : ENNReal)) ≤ D) :
    isAchievablePointwise P d 0 D := by
  let seq : CodeSequence X Y :=
    { M := fun _ => 1
      hM := fun _ => Nat.zero_lt_one
      code := fun n => constantSymbolCode (n + 1) y }
  refine ⟨seq, ?_, ?_⟩
  · intro n
    simp [seq, codeRate]
  · change asymptoticDistortion seq P d ≤ D
    unfold asymptoticDistortion
    have heq : (fun n => expectedDistortion (n + 1) (seq.M n)
        (Nat.succ_pos n) (seq.code n) P d) =
        (fun _ : ℕ => ∑ x, P x * (d x y : ENNReal)) := by
      funext n
      exact expectedDistortion_constantSymbolCode (n + 1) (Nat.succ_pos n) P d y
    rw [heq, limsup_const]
    exact hy

/-- Every test channel has distortion bounded by the finite letterwise bound. -/
theorem expected_distortion_single_le_bound
    (P : PMF X) (W : X → PMF Y) (d : Distortion (X := X) (Y := Y)) :
    expected_distortion_single P W d ≤ (distortionBound d : ENNReal) := by
  unfold expected_distortion_single
  calc
    (∑ x, P x * ∑ y, W x y * (d x y : ENNReal)) ≤
        ∑ x, P x * ∑ y, W x y * (distortionBound d : ENNReal) := by
      apply Finset.sum_le_sum
      intro x _
      apply mul_le_mul_right
      apply Finset.sum_le_sum
      intro y _
      exact mul_le_mul_right (by exact_mod_cast distortion_le_bound d x y) _
    _ = (distortionBound d : ENNReal) := by
      simp_rw [← Finset.sum_mul, sum_pmf, one_mul]
      rw [← Finset.sum_mul, sum_pmf, one_mul]

/-- A finite upper rate bound supplies an optimal feasible test channel. -/
theorem exists_optimal_testChannel_of_rate_bound
    (P : PMF X) (d : Distortion (X := X) (Y := Y)) (D : ENNReal) (R : ℝ)
    (hRD : RateDistortionFunction P d D ≤ ENNReal.ofReal R) :
    ∃ W : X → PMF Y, expected_distortion_single P W d ≤ D ∧
      mutual_information (induced_joint P W) = RateDistortionFunction P d D := by
  obtain ⟨V, hV, _⟩ := exists_testChannel_of_RateDistortionFunction_lt P d D ⊤
    (hRD.trans_lt (lt_top_iff_ne_top.mpr ENNReal.ofReal_ne_top))
  exact RateDistortionFunction_attained P d D ⟨V, hV⟩

/-- At positive rates, move the strict coding slack into distortion by mixing
an optimal channel with an independent reproduction channel. -/
theorem exists_testChannel_strict_rate_with_distortion_slack
    (P : PMF X) (d : Distortion (X := X) (Y := Y)) (D : ENNReal) (R : ℝ)
    (hR : 0 < R) (hRD : RateDistortionFunction P d D ≤ ENNReal.ofReal R)
    (η : ℝ) (hη : 0 < η) :
    ∃ W : X → PMF Y,
      expected_distortion_single P W d ≤ D + ENNReal.ofReal η ∧
      mutualInformationEntropy (induced_joint P W) < R := by
  obtain ⟨W, hW, hIW⟩ := exists_optimal_testChannel_of_rate_bound P d D R hRD
  let Q := P.bind W
  let B : ℝ := (distortionBound d : ℝ)
  have hB : 0 ≤ B := NNReal.coe_nonneg _
  let t : ℝ := min (1 / 2) (η / (B + 1))
  have ht : 0 < t := lt_min (by norm_num) (div_pos hη (by positivity))
  have ht1 : t ≤ 1 / 2 := min_le_left _ _
  have htB : t * B ≤ η := by
    have hmul : t * (B + 1) ≤ η :=
      (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
    nlinarith
  let a := ENNReal.ofReal (1 - t)
  let b := ENNReal.ofReal t
  have hab : a + b = 1 := by
    dsimp [a, b]
    rw [← ENNReal.ofReal_add (by linarith) ht.le]
    norm_num
  have ha1 : a ≤ 1 := by
    dsimp [a]
    exact (ENNReal.ofReal_le_ofReal (by linarith : 1 - t ≤ 1)).trans_eq (by simp)
  have hIz : mutualInformationEntropy (induced_joint P (fun _ => Q)) = 0 := by
    have hz := mutual_information_induced_joint_const P Q
    rw [mutual_information_eq_ofReal_entropy, ENNReal.ofReal_eq_zero] at hz
    exact le_antisymm hz (mutualInformationEntropy_nonneg _)
  have hIR : mutualInformationEntropy (induced_joint P W) ≤ R := by
    have h := hIW.le.trans hRD
    rw [mutual_information_eq_ofReal_entropy] at h
    exact (ENNReal.ofReal_le_ofReal_iff hR.le).mp h
  refine ⟨channelMix a b hab W (fun _ => Q), ?_, ?_⟩
  · rw [expected_distortion_single_channelMix]
    apply add_le_add
    · exact (mul_le_mul_right hW a).trans (by simpa using mul_le_mul_left ha1 D)
    · calc
        b * expected_distortion_single P (fun _ => Q) d ≤
            b * (distortionBound d : ENNReal) :=
          mul_le_mul_right (expected_distortion_single_le_bound P (fun _ => Q) d) b
        _ = ENNReal.ofReal (t * B) := by
          simp [b, B, ENNReal.ofReal_mul ht.le]
        _ ≤ ENNReal.ofReal η := ENNReal.ofReal_le_ofReal htB
  · have hm := mutualInformationEntropy_channelMix_le P a b hab W (fun _ => Q)
    have haReal : a.toReal = 1 - t := ENNReal.toReal_ofReal (by linarith)
    rw [haReal, hIz, mul_zero, add_zero] at hm
    have hmul : (1 - t) * mutualInformationEntropy (induced_joint P W) ≤
        (1 - t) * R := mul_le_mul_of_nonneg_left hIR (by linarith)
    exact hm.trans_lt (hmul.trans_lt (by nlinarith))

/-- Zero information at the optimum gives a zero-rate pointwise-achievable code. -/
theorem rate_distortion_zero_rate_achievable_pointwise
    (P : PMF X) (d : Distortion (X := X) (Y := Y)) (D : ENNReal)
    (hzero : RateDistortionFunction P d D = 0) :
    isAchievablePointwise P d 0 D := by
  obtain ⟨W, hW, hI⟩ := exists_optimal_testChannel_of_rate_bound P d D 0 (by simp [hzero])
  obtain ⟨y, hy⟩ := exists_constant_reproduction_of_zero_information P W d D hW
    (hI.trans hzero)
  exact isAchievablePointwise_of_constant_reproduction P d D y hy

/-- Distortion slack from mixing and random coding vanishes on the same precision schedule. -/
theorem boundaryPointwiseDistortionError_small
    (d : Distortion (X := X) (Y := Y)) :
    ∀ ε : ENNReal, 0 < ε → ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      ENNReal.ofReal (diagonalSlack k) + diagonalDistortionError d k ≤ ε := by
  intro ε hε
  let c : ENNReal := 2 + (distortionBound d : ENNReal) * 3
  have hcTop : c ≠ ⊤ := by dsimp [c]; finiteness
  obtain ⟨K, _, hK⟩ := ENNReal.exists_nat_pos_inv_mul_lt hcTop hε.ne'
  refine ⟨K, fun k hk => ?_⟩
  have hcast : (K : ENNReal) ≤ ((k + 1 : ℕ) : ENNReal) := by
    exact_mod_cast (Nat.le_succ_of_le hk)
  have herr : ENNReal.ofReal (diagonalSlack k) + diagonalDistortionError d k =
      c * ((k + 1 : ℕ) : ENNReal)⁻¹ := by
    unfold diagonalDistortionError
    rw [ennreal_ofReal_diagonalSlack]
    dsimp [c]
    ring
  rw [herr]
  exact (mul_le_mul_right (ENNReal.inv_le_inv' hcast) c).trans
    (by simpa [mul_comm] using hK.le)

/-- Closed-rate achievability with a rate bound on every code, including equality. -/
theorem rate_distortion_achievability_pointwise
    (P : PMF X) (d : Distortion (X := X) (Y := Y)) (D : ENNReal) (R : ℝ)
    (hR : 0 ≤ R) (hRD : RateDistortionFunction P d D ≤ ENNReal.ofReal R) :
    isAchievablePointwise P d R D := by
  classical
  by_cases hRzero : R = 0
  · subst R
    exact rate_distortion_zero_rate_achievable_pointwise P d D
      (le_antisymm (by simpa using hRD) bot_le)
  have hRpos : 0 < R := lt_of_le_of_ne hR (Ne.symm hRzero)
  obtain ⟨V, _, _⟩ := exists_optimal_testChannel_of_rate_bound P d D R hRD
  letI : Nonempty Y := nonempty_reproduction_of_source_channel P V
  by_cases hDtop : D = ⊤
  · subst D
    exact isAchievablePointwise_top_of_nonneg_rate P d R hR
  choose W hW hI using fun k => exists_testChannel_strict_rate_with_distortion_slack
    P d D R hRpos hRD (diagonalSlack k) (diagonalSlack_pos k)
  choose N hN using fun k => exists_nat_forall_exists_testChannelCode_bound
    P (W k) d (D + ENNReal.ofReal (diagonalSlack k)) R
    (ENNReal.add_ne_top.mpr ⟨hDtop, ENNReal.ofReal_ne_top⟩) (hW k) (hI k)
    (diagonalSlack k) (diagonalSlack k) (diagonalSlack_pos k)
    (diagonalSlack_pos k) (diagonalSlack_le_one k)
  obtain ⟨seq, hrate, hbound⟩ := exists_diagonalCodeSequence_of_eventually_codes
    R hR P d D N
    (fun k => ENNReal.ofReal (diagonalSlack k) + diagonalDistortionError d k) (by
      intro k n hn
      simpa only [diagonalDistortionError, add_assoc] using hN k n hn)
  refine ⟨seq, hrate, ?_⟩
  exact asymptoticDistortion_le_of_diagonal_error seq P d D N _ hbound
    (boundaryPointwiseDistortionError_small d)

theorem rate_distortion_achievability_at_boundary_pointwise
    (P : PMF X) (d : Distortion (X := X) (Y := Y)) (D : ENNReal)
    (hfinite : RateDistortionFunction P d D ≠ ⊤) :
    isAchievablePointwise P d (RateDistortionFunction P d D).toReal D := by
  apply rate_distortion_achievability_pointwise P d D _ ENNReal.toReal_nonneg
  rw [ENNReal.ofReal_toReal hfinite]

/-!
===============================================================================
             MAIN THEOREMS WITH THE MANUSCRIPT RATE REQUIREMENT
===============================================================================
Both statements use isAchievablePointwise: every code has rate at most R.
1. Direct theorem: R_I(D) < R implies achievability.
2. Converse: achievability implies R_I(D) <= R at every distortion level.
   Right continuity follows from compactness and continuity of the finite-
   alphabet optimization problem; it is not an additional hypothesis.
Closed-rate pointwise achievability is proved above. The equality-rate public
interface below also uses the pointwise requirement; the asymptotic interface
is retained as a corollary.
===============================================================================
-/

-- ==================== DIRECT THEOREM ====================
/-- Strict-rate achievability with the pointwise rate requirement of the manuscript. -/
theorem rate_distortion_achievability
    (P : PMF X) (d : Distortion (X := X) (Y := Y))
    (D : ENNReal) (R : ℝ)
    (hRD : RateDistortionFunction P d D < ENNReal.ofReal R) :
    isAchievablePointwise P d R D := by
  exact isAchievablePointwise_of_rateDistortionFunction_lt P d D R hRD

-- ==================== CONVERSE ====================
/-- The manuscript rate requirement implies the lower rate bound at every
distortion level. Right continuity is supplied by the finite-alphabet theory. -/
theorem rate_distortion_converse
    (P : PMF X) (d : Distortion (X := X) (Y := Y)) (D : ENNReal)
    (R : ℝ)
    (hA : isAchievablePointwise P d R D) :
    RateDistortionFunction P d D ≤ ENNReal.ofReal R := by
  exact rate_distortion_converse_pointwise_of_rightContinuousAt P d D R
    (rateDistortionRightContinuousAt_all P d D) hA

/-- Rates below RI(D) are not achievable with the manuscript rate requirement. -/
theorem rate_distortion_nonachievability
    (P : PMF X) (d : Distortion (X := X) (Y := Y)) (D : ENNReal)
    (R : ℝ)
    (hR : ENNReal.ofReal R < RateDistortionFunction P d D) :
    ¬ isAchievablePointwise P d R D := by
  intro hA
  exact (not_le_of_gt hR) (rate_distortion_converse P d D R hA)

-- ===========================================================================
--                     END OF MANUSCRIPT MAIN THEOREMS
-- ===========================================================================

/-!
===============================================================================
                 THEOREMS WITH AN ASYMPTOTIC RATE REQUIREMENT
===============================================================================
These statements use isAchievable, which bounds the limsup of the code rates.
The direct theorem includes R = R_I(D). It does not claim a pointwise rate
bound at equality. The converse holds at every distortion level.
===============================================================================
-/

/-- No distortion threshold is needed: a finite upper bound on RI(D)
already supplies a feasible test channel and a nonempty reproduction alphabet. -/
theorem rate_distortion_achievability_asymptotic
    (P : PMF X) (d : Distortion (X := X) (Y := Y))
    (D : ENNReal) (R : ℝ) (hR : 0 ≤ R)
    (hRD : RateDistortionFunction P d D ≤ ENNReal.ofReal R) :
    isAchievable P d R D := by
  by_cases hDtop : D = ⊤
  · subst D
    have hstrict : RateDistortionFunction P d ⊤ < ENNReal.ofReal (R + 1) :=
      hRD.trans_lt ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg hR).mpr (by linarith))
    obtain ⟨W, _, _⟩ := exists_testChannel_of_RateDistortionFunction_lt_ofReal
      P d ⊤ (R + 1) hstrict
    letI : Nonempty Y := nonempty_reproduction_of_source_channel P W
    exact isAchievable_top_of_nonneg_rate P d R hR
  · exact rate_distortion_achievability_of_finite_distortion P d D R hDtop hR hRD

-- ==================== CONVERSE ====================
-- Scope: every distortion threshold D : ENNReal.
theorem rate_distortion_converse_asymptotic
    (P : PMF X) (d : Distortion (X := X) (Y := Y)) (D : ENNReal)
    (R : ℝ)
    (hA : isAchievable P d R D) :
    RateDistortionFunction P d D ≤ ENNReal.ofReal R := by
  exact rate_distortion_converse_of_rightContinuousAt P d D R
    (rateDistortionRightContinuousAt_all P d D) hA

-- The strict converse form follows from `rate_distortion_converse_asymptotic`.
theorem rate_distortion_nonachievability_asymptotic
    (P : PMF X) (d : Distortion (X := X) (Y := Y)) (D : ENNReal)
    (R : ℝ)
    (hR : ENNReal.ofReal R < RateDistortionFunction P d D) :
    ¬ isAchievable P d R D := by
  intro hA
  exact (not_le_of_gt hR) (rate_distortion_converse_asymptotic P d D R hA)

-- ===========================================================================
--                 END OF ASYMPTOTIC RATE THEOREMS
-- ===========================================================================

/-- Equality-rate achievability with every code satisfying the prescribed rate bound.
The distortion constraint remains asymptotic, as in the manuscript definition. -/
theorem rate_distortion_achievability_at_boundary
    (P : PMF X) (d : Distortion (X := X) (Y := Y)) (D : ENNReal)
    (hfinite : RateDistortionFunction P d D ≠ ⊤) :
    isAchievablePointwise P d (RateDistortionFunction P d D).toReal D := by
  exact rate_distortion_achievability_at_boundary_pointwise P d D hfinite

/-- Compatibility interface for equality-rate achievability with a limsup rate bound. -/
theorem rate_distortion_achievability_at_boundary_asymptotic
    (P : PMF X) (d : Distortion (X := X) (Y := Y)) (D : ENNReal)
    (hfinite : RateDistortionFunction P d D ≠ ⊤) :
    isAchievable P d (RateDistortionFunction P d D).toReal D := by
  exact isAchievablePointwise_imp_isAchievable P d _ D
    (rate_distortion_achievability_at_boundary P d D hfinite)

/-- The operational characterization also holds with a rate bound on every code. -/
theorem rate_distortion_achievable_iff_pointwise
    (P : PMF X) (d : Distortion (X := X) (Y := Y))
    (D : ENNReal) (R : ℝ) (hR : 0 ≤ R) :
    isAchievablePointwise P d R D ↔
      RateDistortionFunction P d D ≤ ENNReal.ofReal R := by
  exact ⟨rate_distortion_converse P d D R,
    rate_distortion_achievability_pointwise P d D R hR⟩

/-- A modular equivalence interface with an explicit right-continuity argument. -/
theorem rate_distortion_achievable_iff_of_rightContinuousAt
    (P : PMF X) (d : Distortion (X := X) (Y := Y))
    (D : ENNReal) (R : ℝ) (hR : 0 ≤ R)
    (hcont : rateDistortionRightContinuousAt P d D) :
    isAchievable P d R D ↔ RateDistortionFunction P d D ≤ ENNReal.ofReal R := by
  exact ⟨rate_distortion_converse_of_rightContinuousAt P d D R hcont,
    rate_distortion_achievability_asymptotic P d D R hR⟩

/-- The full characterization under an asymptotic rate constraint, with no
additional continuity or interior-distortion hypothesis. -/
theorem rate_distortion_achievable_iff
    (P : PMF X) (d : Distortion (X := X) (Y := Y))
    (D : ENNReal) (R : ℝ) (hR : 0 ≤ R) :
    isAchievable P d R D ↔ RateDistortionFunction P d D ≤ ENNReal.ofReal R := by
  exact rate_distortion_achievable_iff_of_rightContinuousAt P d D R hR
    (rateDistortionRightContinuousAt_all P d D)

/-- A strictly feasible channel suffices for right continuity. Unlike the
older interior interface, this does not refer to either distortion threshold. -/
theorem rateDistortionRightContinuousAt_of_strictly_feasible
    (P : PMF X) (d : Distortion (X := X) (Y := Y)) (D : ENNReal)
    (hDtop : D ≠ ⊤) (W₀ : X → PMF Y)
    (hW₀ : expected_distortion_single P W₀ d < D) :
    rateDistortionRightContinuousAt P d D := by
  let D₀ := expected_distortion_single P W₀ d
  have hD₀ : D₀ < D := hW₀
  have hD₀feas : feasibleDistortion P d D₀ := ⟨W₀, le_rfl⟩
  have hDfeas : feasibleDistortion P d D := ⟨W₀, hW₀.le⟩
  have hRDtop : RateDistortionFunction P d D ≠ ⊤ :=
    RateDistortionFunction_ne_top_of_feasible P d D W₀ hW₀.le
  have hRD₀top : RateDistortionFunction P d D₀ ≠ ⊤ :=
    RateDistortionFunction_ne_top_of_feasible P d D₀ W₀ le_rfl
  have hc0 : D - D₀ ≠ 0 := (tsub_pos_iff_lt.mpr hD₀).ne'
  have hctop : D - D₀ ≠ ⊤ := ne_top_of_le_ne_top hDtop tsub_le_self
  have hlower := ennreal_tsub_barycentric_tendsto
    (RateDistortionFunction P d D) (RateDistortionFunction P d D₀)
    (D - D₀) hRDtop hRD₀top hc0 hctop
  have hupper : Tendsto (fun _ : ENNReal ↦ RateDistortionFunction P d D)
      (nhdsWithin (0 : ENNReal) (Set.Ioi 0))
      (𝓝 (RateDistortionFunction P d D)) := tendsto_const_nhds
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper
  · filter_upwards [self_mem_nhdsWithin,
      Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (Iio_mem_nhds (show (0 : ENNReal) < 1 by norm_num))] with ε hε hεsmall
    have hεtop : ε ≠ ⊤ := ne_top_of_lt hεsmall
    obtain ⟨hab, hbar, hb⟩ := ennreal_barycentric_weights D₀ D ε hD₀ hDtop hεtop
    have hDplus : feasibleDistortion P d (D + ε) :=
      feasibleDistortion_mono P d (le_add_right le_rfl) hDfeas
    have htsub := RateDistortionFunction_tsub_le_of_convex
      P d (ε / (D - D₀ + ε)) ((D - D₀) / (D - D₀ + ε)) hab
      D₀ (D + ε) hD₀feas hDplus hb
    rw [hbar] at htsub
    exact htsub
  · filter_upwards [] with ε
    exact RateDistortionFunction_antitone P d (le_add_right le_rfl)

/-- Once RI(D) is zero, monotonicity proves right continuity at D directly. -/
theorem rateDistortionRightContinuousAt_of_eq_zero
    (P : PMF X) (d : Distortion (X := X) (Y := Y)) (D : ENNReal)
    (hzero : RateDistortionFunction P d D = 0) :
    rateDistortionRightContinuousAt P d D := by
  have heq (ε : ENNReal) : RateDistortionFunction P d (D + ε) = 0 := by
    apply le_antisymm _ bot_le
    calc
      RateDistortionFunction P d (D + ε) ≤ RateDistortionFunction P d D :=
        RateDistortionFunction_antitone P d (le_add_right le_rfl)
      _ = 0 := hzero
  unfold rateDistortionRightContinuousAt
  simp_rw [heq, hzero]
  exact tendsto_const_nhds

/-- Zero rate is included in the equality-rate result. -/
theorem rate_distortion_zero_rate_achievable
    (P : PMF X) (d : Distortion (X := X) (Y := Y)) (D : ENNReal)
    (hzero : RateDistortionFunction P d D = 0) :
    isAchievable P d 0 D := by
  apply rate_distortion_achievability_asymptotic P d D 0 le_rfl
  simp [hzero]

end RateDistortion
