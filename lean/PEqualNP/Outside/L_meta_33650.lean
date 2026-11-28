import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.LinearAlgebra.Pi
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_33650

section Parity

open scoped BigOperators

private abbrev K := ZMod 2
private abbrev Column := K × K × K

private theorem univK : (Finset.univ : Finset K) = {0, 1} := by decide
private theorem twoK : (2 : K) = 0 := by decide
private theorem fourK : (4 : K) = 0 := by decide
private theorem eightK : (8 : K) = 0 := by decide

private def parity (f : K → K → K → K) : K :=
  ∑ t : K, ∑ r : K, ∑ s : K, f t r s

private def linear3 (a b c d t r s : K) : K :=
  a + b * t + c * r + d * s

private def det3 (x y z : Column) : K :=
  x.1 * y.2.1 * z.2.2 + x.1 * z.2.1 * y.2.2 +
  y.1 * x.2.1 * z.2.2 + y.1 * z.2.1 * x.2.2 +
  z.1 * x.2.1 * y.2.2 + z.1 * y.2.1 * x.2.2

private theorem parity_add (a b : K → K → K → K) :
    parity (fun t r s => a t r s + b t r s) = parity a + parity b := by
  simp only [parity, Finset.sum_add_distrib]

private theorem parity_mul_const (a : K) (f : K → K → K → K) :
    parity (fun t r s => a * f t r s) = a * parity f := by
  simp only [parity, Finset.mul_sum]

private theorem parity_sum {ι : Type*} (I : Finset ι) (f : ι → K → K → K → K) :
    parity (fun t r s => ∑ i ∈ I, f i t r s) = ∑ i ∈ I, parity (f i) := by
  simp [parity, univK, ← Finset.sum_add_distrib]

private theorem parity_linear (a b c d : K) :
    parity (linear3 a b c d) = 0 := by
  simp [parity, univK, linear3]
  ring_nf <;> simp only [twoK, fourK, eightK, mul_zero, add_zero, zero_add]

private theorem parity_quad (a b c d e f g h : K) :
    parity (fun t r s => linear3 a b c d t r s * linear3 e f g h t r s) = 0 := by
  simp [parity, univK, linear3]
  ring_nf <;> simp only [twoK, fourK, eightK, mul_zero, add_zero, zero_add]

private theorem parity_cubic (a b c : K) (x y z : Column) :
    parity (fun t r s =>
      linear3 a x.1 y.1 z.1 t r s *
      linear3 b x.2.1 y.2.1 z.2.1 t r s *
      linear3 c x.2.2 y.2.2 z.2.2 t r s) = det3 x y z := by
  simp [parity, univK, linear3, det3]
  ring_nf <;> simp only [twoK, fourK, eightK, mul_zero, add_zero, zero_add]

private theorem parity_trs : parity (fun t r s => t * r * s) = 1 := by decide

private def columnColour (c v : Column) : Fin 3 :=
  let pair :=
    if c.1 = 1 then (v.2.1 + v.1 * c.2.1, v.2.2 + v.1 * c.2.2)
    else if c.2.1 = 1 then (v.1 + v.2.1 * c.1, v.2.2 + v.2.1 * c.2.2)
    else (v.1, v.2.1)
  if pair.1 = 1 then (if pair.2 = 1 then 2 else 0)
  else if pair.2 = 1 then 1 else 0

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
private theorem colour_det_zero : ∀ c u v : Column,
    columnColour c u = columnColour c v → det3 c u v = 0 := by
  decide

end Parity

section ColorPolynomial

open scoped BigOperators

private abbrev F := ZMod 2
private abbrev Vec (n : ℕ) := Fin n → F

private def basisBit {n : ℕ} (i : Fin n) : Vec n :=
  fun j => if j = i then 1 else 0

private def tagX (c : Fin 3) : F :=
  if c = 1 then 0 else 1

private def tagY (c : Fin 3) : F :=
  if c = 0 then 0 else 1

private def colorPolynomial {k : ℕ} (col : Fin k → Fin 3) (z : Vec k) : F :=
  dotProduct (tagX ∘ col) z * dotProduct (tagY ∘ col) z +
    dotProduct (fun i => tagX (col i) * tagY (col i)) z

private theorem dot_basisBit {k : ℕ} (q : Vec k) (i : Fin k) :
    dotProduct q (basisBit i) = q i := by
  simp [dotProduct, basisBit, mul_ite]

private theorem dot_corner_tail {k : ℕ} (q : Vec k) (u v : Fin k) (r s : F) :
    dotProduct q (r • basisBit u + s • basisBit v) = r * q u + s * q v := by
  simp only [dotProduct_add, dotProduct_smul, dot_basisBit, smul_eq_mul]

private theorem tag_eval_table : ∀ (a b : Fin 3) (r s : F),
    (r * tagX a + s * tagX b) * (r * tagY a + s * tagY b) +
      (r * (tagX a * tagY a) + s * (tagX b * tagY b)) =
      if a = b then 0 else r * s := by decide

private theorem color_polynomial_corner {k : ℕ} (col : Fin k → Fin 3)
    (u v : Fin k) (r s : F) :
    colorPolynomial col (r • basisBit u + s • basisBit v) =
      if col u = col v then 0 else r * s := by
  simpa only [colorPolynomial, dot_corner_tail, Function.comp_apply] using
    tag_eval_table (col u) (col v) r s

private def colorAnswer {k : ℕ} (col : Fin k → Fin 3) (x y : Vec (k + 1)) : F :=
  dotProduct (Fin.tail x) (Fin.tail y) + y 0 * (x 0 + colorPolynomial col (Fin.tail y))

private theorem color_answer_split {k : ℕ} (col : Fin k → Fin 3)
    (x y : Vec (k + 1)) :
    colorAnswer col x y = dotProduct x y + y 0 * colorPolynomial col (Fin.tail y) := by
  simp only [colorAnswer, dotProduct, Fin.sum_univ_succ, Fin.tail]
  ring

private theorem color_answer_key {k : ℕ} (col : Fin k → Fin 3)
    (x : Vec (k + 1)) (z : Vec k) :
    colorAnswer col x (Fin.cons 0 z) = dotProduct x (Fin.cons 0 z) := by
  simp [color_answer_split]

private theorem color_answer_corner {k : ℕ} (col : Fin k → Fin 3)
    (x : Vec (k + 1)) (u v : Fin k) (t r s : F) :
    colorAnswer col x (Fin.cons t (r • basisBit u + s • basisBit v)) =
      dotProduct x (Fin.cons t (r • basisBit u + s • basisBit v)) +
         (if col u = col v then 0 else t * r * s) := by
  simp only [color_answer_split, Fin.tail_cons, Fin.cons_zero, color_polynomial_corner]
  split <;> simp_all [mul_assoc]

end ColorPolynomial

section Splitting

open scoped BigOperators

private abbrev SplitField := ZMod 2

private theorem split_bits (a : SplitField) : a = 0 ∨ a = 1 := by
  revert a
  decide

private theorem maps_one {X : Type*} [AddCommGroup X] [Module SplitField X]
    (f : X →ₗ[SplitField] SplitField) (hf : f ≠ 0) :
    ∃ v, f v = 1 := by
  by_contra h
  apply hf
  apply LinearMap.ext
  intro u
  rcases split_bits (f u) with he | he
  · exact he
  · exact (h ⟨u, he⟩).elim

private def splitEquiv {X : Type*} [AddCommGroup X] [Module SplitField X]
    (f : X →ₗ[SplitField] SplitField) (v : X) (hv : f v = 1) (b : SplitField) :
    X ≃ (SplitField × LinearMap.ker f) where
  toFun x := (f x + b, ⟨x - (f x) • v, by
    change f (x - (f x) • v) = 0
    simp [hv]⟩)
  invFun q := (q.1 - b) • v + (q.2 : X)
  left_inv x := by
    change (f x + b - b) • v + (x - (f x) • v) = x
    rw [add_sub_cancel_right]
    abel
  right_inv q := by
    have hk : f (q.2 : X) = 0 := q.2.2
    have hs : f ((q.1 - b) • v + (q.2 : X)) = q.1 - b := by simp [hv, hk]
    apply Prod.ext
    · change f ((q.1 - b) • v + (q.2 : X)) + b = q.1
      rw [hs, sub_add_cancel]
    · apply Subtype.ext
      change ((q.1 - b) • v + (q.2 : X)) -
        f ((q.1 - b) • v + (q.2 : X)) • v = (q.2 : X)
      rw [hs]
      abel

private theorem split_eval {X : Type*} [AddCommGroup X] [Module SplitField X]
    (f : X →ₗ[SplitField] SplitField) (v : X) (hv : f v = 1)
    (b c : SplitField) (z : LinearMap.ker f) :
    f ((splitEquiv f v hv b).symm (c, z)) + b = c := by
  have h := congrArg Prod.fst ((splitEquiv f v hv b).apply_symm_apply (c, z))
  exact h

private theorem split_card {X : Type*} [AddCommGroup X] [Module SplitField X] [Fintype X]
    (f : X →ₗ[SplitField] SplitField) (v : X) (hv : f v = 1)
    [Fintype (LinearMap.ker f)] :
    Fintype.card X = 2 * Fintype.card (LinearMap.ker f) := by
  rw [Fintype.card_congr (splitEquiv f v hv 0), Fintype.card_prod, ZMod.card]

private theorem split_sum {X : Type*} [AddCommGroup X] [Module SplitField X] [Fintype X]
    (f : X →ₗ[SplitField] SplitField) (v : X) (hv : f v = 1)
    [Fintype (LinearMap.ker f)] (b : SplitField) (q : X → ℝ) :
    (∑ x, q x) = (∑ x : LinearMap.ker f, q ((0 - b) • v + (x : X))) +
      (∑ x : LinearMap.ker f, q ((1 - b) • v + (x : X))) := by
  let equiv := splitEquiv f v hv b
  have changeEnum :
      (∑ x, q x) = ∑ p : SplitField × LinearMap.ker f, q (equiv.symm p) :=
    Fintype.sum_equiv equiv q (fun p => q (equiv.symm p)) (fun x => by simp)
  rw [changeEnum, Fintype.sum_prod_type]
  have two : (Finset.univ : Finset SplitField) = {0, 1} := by decide
  rw [two]
  simp [equiv, splitEquiv]

private theorem split_mean {X : Type*} [AddCommGroup X] [Module SplitField X] [Fintype X]
    (f : X →ₗ[SplitField] SplitField) (v : X) (hv : f v = 1)
    [Fintype (LinearMap.ker f)] (b : SplitField) (q : X → ℝ) :
    (∑ x, q x) / (Fintype.card X : ℝ) =
      ((∑ x : LinearMap.ker f, q ((0 - b) • v + (x : X))) / Fintype.card (LinearMap.ker f) +
        (∑ x : LinearMap.ker f, q ((1 - b) • v + (x : X))) / Fintype.card (LinearMap.ker f)) / 2 := by
  rw [split_sum f v hv, split_card f v hv]
  push_cast
  ring

end Splitting

section PureFeatures

private abbrev FeatField := ZMod 2

private abbrev AffineBit (Y : Type*) [AddCommGroup Y] [Module FeatField Y] :=
  FeatField × (Y →ₗ[FeatField] FeatField)

private def affineBit {Y : Type*} [AddCommGroup Y] [Module FeatField Y]
    (a : AffineBit Y) (y : Y) : FeatField :=
  a.1 + a.2 y

private def featureSpace {Y : Type*} [AddCommGroup Y] [Module FeatField Y]
    (p : Y → FeatField) : Submodule FeatField (Y → FeatField) := by
  refine
    { carrier := {f | ∃ a : AffineBit Y, ∃ q : FeatField, ∀ y, f y = affineBit a y + q * p y}
      zero_mem' := ?containsZero, add_mem' := ?closedUnderSum, smul_mem' := ?closedUnderScalar }
  case containsZero =>
    refine ⟨(0, 0), 0, ?_⟩
    intro y
    simp [affineBit]
  case closedUnderSum =>
    rintro f g ⟨a, q, hf⟩ ⟨b, r, hg⟩
    refine ⟨(a.1 + b.1, a.2 + b.2), q + r, ?_⟩
    intro y
    simp [affineBit, hf y, hg y]
    ring
  case closedUnderScalar =>
    rintro c f ⟨a, q, hf⟩
    refine ⟨(c * a.1, c • a.2), c * q, ?_⟩
    intro y
    simp [affineBit, hf y, smul_eq_mul]
    ring

private def features {Y : Type*} [AddCommGroup Y] [Module FeatField Y]
    (r : ℕ) (p : Y → FeatField) : Submodule FeatField (Y → FeatField) :=
  if r ≤ 1 then featureSpace p else ⊤

private def pureOK {Y : Type*} [AddCommGroup Y] [Module FeatField Y]
    (r : ℕ) (p : Y → FeatField) : Prop :=
  (r = 0 → p = 0) ∧
    (r = 1 → ∃ a b : AffineBit Y, ∀ y, p y = affineBit a y * affineBit b y)

private theorem features_affine {Y : Type*} [AddCommGroup Y] [Module FeatField Y]
    (r : ℕ) (p : Y → FeatField) (a : AffineBit Y) :
    affineBit a ∈ features r p := by
  by_cases h : r ≤ 1
  · rw [features, if_pos h]
    change ∃ b : AffineBit Y, ∃ q : FeatField, _
    exact ⟨a, 0, fun y => by simp⟩
  · simp [features, h]

private theorem features_const {Y : Type*} [AddCommGroup Y] [Module FeatField Y]
    (r : ℕ) (p : Y → FeatField) (c : FeatField) :
    (fun _ : Y => c) ∈ features r p := by
  have h : affineBit (c, (0 : Y →ₗ[FeatField] FeatField)) = fun _ : Y => c := by
    funext y
    simp [affineBit]
  rw [← h]
  exact features_affine _ _ _

private theorem features_linear {Y : Type*} [AddCommGroup Y] [Module FeatField Y]
    (r : ℕ) (p : Y → FeatField) (a : Y →ₗ[FeatField] FeatField) :
    (fun y => a y) ∈ features r p := by
  have h : affineBit (0, a) = fun y => a y := by
    funext y
    simp [affineBit]
  rw [← h]
  exact features_affine _ _ _

private theorem one_feature {Y : Type*} [AddCommGroup Y] [Module FeatField Y]
    (r : ℕ) (hr : r ≤ 1) (p f : Y → FeatField) (hf : f ∈ features r p) :
    ∃ a : AffineBit Y, ∃ q : FeatField, ∀ y, f y = affineBit a y + q * p y := by
  rw [features, if_pos hr] at hf
  change ∃ a : AffineBit Y, ∃ q : FeatField, ∀ y, f y = affineBit a y + q * p y at hf
  exact hf

private theorem add_pure_feature {Y : Type*} [AddCommGroup Y] [Module FeatField Y]
    (r : ℕ) (p a b : Y → FeatField) (hp : pureOK r p)
    (ha : a ∈ features r p) (hb : b ∈ features r p) :
    ∃ q : Y → FeatField, pureOK (r + 1) q ∧ features r p ≤ features (r + 1) q ∧
      (fun y => a y * b y) ∈ features (r + 1) q := by
  cases r with
  | zero =>
    have hzero := hp.1 rfl
    subst p
    obtain ⟨A, c, hA⟩ := one_feature 0 (by omega) (0 : Y → FeatField) a ha
    obtain ⟨B, d, hB⟩ := one_feature 0 (by omega) (0 : Y → FeatField) b hb
    refine ⟨fun y => a y * b y, ⟨by omega, ?_⟩, ?_, ?_⟩
    · intro _
      refine ⟨A, B, ?_⟩
      intro y
      simp [hA y, hB y]
    · intro f hf
      obtain ⟨C, e, hC⟩ := one_feature 0 (by omega) (0 : Y → FeatField) f hf
      rw [features, if_pos (by omega)]
      change ∃ D : AffineBit Y, ∃ c : FeatField, _
      exact ⟨C, 0, fun y => by simp [hC y]⟩
    · rw [features, if_pos (by omega)]
      change ∃ C : AffineBit Y, ∃ c : FeatField, _
      exact ⟨(0, 0), 1, fun y => by simp [affineBit]⟩
  | succ r =>
    have hlarge : ¬ r.succ + 1 ≤ 1 := by omega
    refine ⟨0, ⟨by omega, by omega⟩, ?_, ?_⟩ <;> simp only [features, if_neg hlarge,
      le_top, Submodule.mem_top]

end PureFeatures

section GateSemantics

open scoped BigOperators
open PEqualNP.CircuitLowerBounds

private abbrev BitField := ZMod 2
private abbrev BitVec (n : ℕ) := Fin n → BitField

private def toScalar (b : Bool) : BitField :=
  if b then 1 else 0

private def toBoolean (a : BitField) : Bool :=
  decide (a = 1)

private theorem scalar_boolean : ∀ a, toScalar (toBoolean a) = a := by decide

private theorem boolean_scalar : ∀ b, toBoolean (toScalar b) = b := by decide

private def gateAllowed (g : Gate) : Prop :=
  g.inputs.length ≤ 2 ∧
    (g.op = .and ∨ g.op = .or ∨ g.op = .mod 2 ∨ (g.op = .not ∧ g.inputs.length = 1))

private def gateCharge (g : Gate) : Prop :=
  (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2

private noncomputable def isPaid (g : Gate) : Bool :=
  @decide (gateCharge g) (Classical.propDecidable _)

private def gateAffine (g : Gate) : BitField × BitField × BitField :=
  match g.op, g.inputs with
  | .and, [] => (1, 0, 0)
  | .and, [_] => (0, 1, 0)
  | .and, _ => (0, 0, 0)
  | .or, [] => (0, 0, 0)
  | .or, [_] => (0, 1, 0)
  | .or, _ => (0, 1, 1)
  | .mod _, [] => (1, 0, 0)
  | .mod _, [_] => (1, 1, 0)
  | .mod _, _ => (1, 1, 1)
  | .not, _ => (1, 1, 0)
  | .maj, _ => (0, 0, 0)

private def gateInputs (g : Gate) (w : ℕ → BitField) : BitField × BitField :=
  ((g.inputs[0]?.map w).getD 0, (g.inputs[1]?.map w).getD 0)

private noncomputable def gateValue (g : Gate) (w : ℕ → BitField) : BitField :=
  let p := gateInputs g w
  let c := gateAffine g
  c.1 + c.2.1 * p.1 + c.2.2 * p.2 + if isPaid g then p.1 * p.2 else 0

private theorem gate_evaluation (g : Gate) (legal : gateAllowed g) (w : ℕ → Bool) :
    toScalar (g.op.eval (g.inputs.map w)) = gateValue g (toScalar ∘ w) := by
  classical
  rcases g with ⟨op, ins⟩
  rcases legal with ⟨hsize, hop⟩
  cases ins with
  | nil =>
    rcases hop with h | h | h | ⟨h, hh⟩
    · cases h
      simp [GateOp.eval, gateValue, gateInputs, gateAffine, isPaid, gateCharge, toScalar]
    · cases h
      simp [GateOp.eval, gateValue, gateInputs, gateAffine, isPaid, gateCharge, toScalar]
    · cases h
      simp [GateOp.eval, gateValue, gateInputs, gateAffine, isPaid, gateCharge, toScalar]
    · exact (by simpa using hh : False).elim
  | cons u rest =>
    cases rest with
    | nil =>
      rcases hop with h | h | h | ⟨h, _⟩ <;> cases h <;> cases hval : w u <;>
        simp [GateOp.eval, gateValue, gateInputs, gateAffine, isPaid, gateCharge,
          toScalar, Function.comp_apply, hval]
        <;> decide
    | cons v rt =>
      have hrt : rt = [] := by
        cases rt with
        | nil => rfl
        | cons x xs => simp at hsize
      subst rt
      rcases hop with h | h | h | ⟨h, hh⟩
      · cases h
        cases hu : w u <;> cases hv : w v <;>
          simp [GateOp.eval, gateValue, gateInputs, gateAffine, isPaid, gateCharge,
            toScalar, Function.comp_apply, hu, hv]
      · cases h
        cases hu : w u <;> cases hv : w v <;>
          simp [GateOp.eval, gateValue, gateInputs, gateAffine, isPaid, gateCharge,
            toScalar, Function.comp_apply, hu, hv]
          <;> decide
      · cases h
        cases hu : w u <;> cases hv : w v <;>
          simp [GateOp.eval, gateValue, gateInputs, gateAffine, isPaid, gateCharge,
            toScalar, Function.comp_apply, hu, hv]
          <;> decide
      · exact (by simpa using hh : False).elim

private def encodedBits {n : ℕ} (x : BitVec n) : List Bool :=
  List.ofFn (fun i => toBoolean (x i))

private noncomputable def fieldWires (G : List Gate) (x : List BitField) : List BitField :=
  G.foldl (fun w g => w ++ [gateValue g (fun i => w.getD i 0)]) x

private theorem scalar_getD (w : List Bool) (i : ℕ) :
    (w.map toScalar).getD i 0 = toScalar (w.getD i false) := by
  change ((w.map toScalar)[i]?).getD 0 = toScalar (w[i]?.getD false)
  rw [List.getElem?_map]
  cases w[i]? <;> rfl

private theorem scalar_wires (G : List Gate) (w : List Bool)
    (legal : ∀ g ∈ G, gateAllowed g) :
    (G.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).map toScalar =
      fieldWires G (w.map toScalar) := by
  induction G generalizing w with
  | nil => rfl
  | cons g G ih =>
    have hg := legal g (List.mem_cons_self ..)
    have hG : ∀ a ∈ G, gateAllowed a := fun a h => legal a (List.mem_cons_of_mem _ h)
    simp only [fieldWires, List.foldl_cons]
    rw [ih _ hG]
    simp only [List.map_append, List.map_cons, List.map_nil, scalar_getD]
    rw [gate_evaluation g hg]
    rfl

private theorem encoded_eval {n : ℕ} (C : Circuit) (legal : ∀ g ∈ C.gates, gateAllowed g)
    (x y : BitVec n) :
    toScalar (C.eval (encodedBits x ++ encodedBits y)) =
      (fieldWires C.gates (List.ofFn x ++ List.ofFn y)).getD C.output 0 := by
  rw [Circuit.eval, ← scalar_getD]
  unfold Circuit.wires
  rw [scalar_wires _ _ legal]
  simp [encodedBits, List.map_ofFn, Function.comp_def, scalar_boolean]

end GateSemantics

section NormalForm

open scoped BigOperators
open PEqualNP.CircuitLowerBounds

private abbrev AffVec (m : ℕ) := BitField × BitVec m

private def runAff {m : ℕ} (a : AffVec m) (v : BitVec m) : BitField :=
  a.1 + dotProduct a.2 v

private def slotProgram : ℕ → ℕ → Type
  | m, 0 => AffVec m
  | m, r + 1 => AffVec m × AffVec m × slotProgram (m + 1) r

private noncomputable def programFinite : (m r : ℕ) → Fintype (slotProgram m r)
  | m, 0 => inferInstanceAs (Fintype (AffVec m))
  | m, r + 1 =>
    letI := programFinite (m + 1) r
    inferInstanceAs (Fintype (AffVec m × AffVec m × slotProgram (m + 1) r))

private def runProgram : (m r : ℕ) → slotProgram m r → BitVec m → BitField
  | _, 0, p, x => runAff p x
  | m, r + 1, p, x =>
    runProgram (m + 1) r p.2.2 (Fin.snoc x (runAff p.1 x * runAff p.2.1 x))

private theorem affine_card (m : ℕ) : Fintype.card (AffVec m) = 2 ^ (m + 1) := by
  simp [Fintype.card_prod, Fintype.card_fun, ZMod.card, pow_succ, mul_comm]

private theorem program_card (m r : ℕ) :
    @Fintype.card (slotProgram m r) (programFinite m r) ≤ 2 ^ ((2 * r + 1) * (m + r + 1)) := by
  induction r generalizing m with
  | zero =>
    change Fintype.card (AffVec m) ≤ _
    rw [affine_card]
    simp
  | succ r ih =>
    letI := programFinite (m + 1) r
    change Fintype.card (AffVec m × AffVec m × slotProgram (m + 1) r) ≤ _
    simp only [Fintype.card_prod, Fintype.card_fun, ZMod.card, Fintype.card_fin, ← pow_succ']
    calc
      _ ≤ 2 ^ (m + 1) * (2 ^ (m + 1) * 2 ^ ((2 * r + 1) * ((m + 1) + r + 1))) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (ih (m + 1)))
      _ = 2 ^ ((m + 1) + (m + 1) + (2 * r + 1) * (m + r + 2)) := by
        rw [← pow_add, ← pow_add]
        congr 1
        ring
      _ ≤ _ := by
        apply Nat.pow_le_pow_right (by decide)
        nlinarith

private theorem normal_forms_card (n : ℕ) (hn : 0 < n) :
    @Fintype.card (slotProgram (n + n) (n + 1)) (programFinite (n + n) (n + 1))
      ≤ 2 ^ (25 * n ^ 2) := by
  apply (program_card (n + n) (n + 1)).trans
  apply Nat.pow_le_pow_right (by decide)
  have hsq : n ≤ n ^ 2 := by nlinarith
  nlinarith

private def affExtra {m : ℕ} (a : AffVec m) (d : BitField) : AffVec (m + 1) :=
  (a.1, Fin.snoc a.2 d)

private theorem eval_extra {m : ℕ} (a : AffVec m) (d p : BitField) (x : BitVec m) :
    runAff (affExtra a d) (Fin.snoc x p) = runAff a x + d * p := by
  simp [runAff, affExtra, dotProduct, Fin.sum_univ_castSucc, add_assoc]

private theorem free_representation (m r : ℕ) (a : AffVec m) :
    ∃ p : slotProgram m r, ∀ x, runProgram m r p x = runAff a x := by
  induction r generalizing m with
  | zero => exact ⟨a, fun _ => rfl⟩
  | succ r ih =>
    obtain ⟨p, hp⟩ := ih (m + 1) (affExtra a 0)
    refine ⟨(0, 0, p), ?_⟩
    intro x
    simp [runProgram, hp, eval_extra]

private def mergeAffine {m : ℕ} (c : BitField × BitField × BitField)
    (a b : AffVec m) : AffVec m :=
  (c.1 + c.2.1 * a.1 + c.2.2 * b.1, c.2.1 • a.2 + c.2.2 • b.2)

private theorem eval_aff_zero {m : ℕ} (x : BitVec m) :
    runAff (0 : AffVec m) x = 0 := by
  simp [runAff]

private theorem eval_mergeAffine {m : ℕ} (c : BitField × BitField × BitField)
    (a b : AffVec m) (x : BitVec m) :
    runAff (mergeAffine c a b) x = c.1 + c.2.1 * runAff a x + c.2.2 * runAff b x := by
  simp only [mergeAffine, runAff, add_dotProduct, smul_dotProduct, smul_eq_mul]
  ring

private theorem eval_aff_getD {m : ℕ} (W : List (AffVec m)) (x : BitVec m) (i : ℕ) :
    (W.map (fun a => runAff a x)).getD i 0 = runAff (W.getD i 0) x := by
  change ((W.map (fun a => runAff a x))[i]?).getD 0 = runAff (W[i]?.getD 0) x
  rw [List.getElem?_map]
  cases W[i]? <;> simp [eval_aff_zero]

private def affineArgument {m : ℕ} (g : Gate) (W : List (AffVec m)) (i : ℕ) : AffVec m :=
  (g.inputs[i]?.map fun j => W.getD j 0).getD 0

private theorem eval_aff_argument {m : ℕ} (g : Gate) (W : List (AffVec m)) (x : BitVec m)
    (i : ℕ) :
    (g.inputs[i]?.map fun j => (W.map (fun a => runAff a x)).getD j 0).getD 0 =
      runAff (affineArgument g W i) x := by
  cases hi : g.inputs[i]? with
  | none => simp [affineArgument, hi, eval_aff_zero]
  | some j =>
    simpa only [affineArgument, hi, Option.map_some, Option.getD_some] using
      eval_aff_getD W x j

private theorem eval_encoded_gate {m : ℕ} (g : Gate) (W : List (AffVec m)) (x : BitVec m) :
    gateValue g (fun j => (W.map (fun a => runAff a x)).getD j 0) =
    runAff (mergeAffine (gateAffine g) (affineArgument g W 0) (affineArgument g W 1)) x +
      if isPaid g then runAff (affineArgument g W 0) x * runAff (affineArgument g W 1) x else 0 := by
  simp only [gateValue, gateInputs, eval_aff_argument, eval_mergeAffine]

private theorem fieldWires_cons (g : Gate) (G : List Gate) (w : List BitField) :
    fieldWires (g :: G) w =
      fieldWires G (w ++ [gateValue g (fun j => w.getD j 0)]) := rfl

private theorem represent_wires (G : List Gate) (m r : ℕ)
    (W : List (AffVec m)) (output : ℕ) (h : G.countP isPaid ≤ r) :
    ∃ p : slotProgram m r, ∀ x,
      runProgram m r p x = (fieldWires G (W.map (fun a => runAff a x))).getD output 0 := by
  induction G generalizing m r with
  | nil =>
    obtain ⟨p, hp⟩ := free_representation m r (W.getD output 0)
    exact ⟨p, fun x => (hp x).trans (eval_aff_getD W x output).symm⟩
  | cons g G ih =>
    let a := affineArgument g W 0
    let b := affineArgument g W 1
    let newBit := mergeAffine (gateAffine g) a b
    cases hp : isPaid g with
    | false =>
      have hG : G.countP isPaid ≤ r := by simpa [hp] using h
      obtain ⟨p, H⟩ := ih m r (W ++ [newBit]) hG
      refine ⟨p, fun x => ?_⟩
      rw [H, fieldWires_cons, eval_encoded_gate]
      simp [hp, newBit, a, b]
    | true =>
      cases r with
      | zero => simp [hp] at h
      | succ r =>
        have hG : G.countP isPaid ≤ r := by simpa [hp] using h
        let ext := W.map (fun a => affExtra a 0) ++ [affExtra newBit 1]
        obtain ⟨p, H⟩ := ih (m + 1) r ext hG
        refine ⟨(a, b, p), fun x => ?_⟩
        change runProgram (m + 1) r p (Fin.snoc x (runAff a x * runAff b x)) = _
        rw [H, fieldWires_cons, eval_encoded_gate]
        simp [ext, newBit, a, b, hp, List.map_map, Function.comp_def, eval_extra]

private def initialAffine {m : ℕ} (i : Fin m) : AffVec m :=
  (0, fun j => if j = i then 1 else 0)

private theorem eval_initialAffine {m : ℕ} (i : Fin m) (x : BitVec m) :
    runAff (initialAffine i) x = x i := by
  simp [runAff, initialAffine, dotProduct, ite_mul]

private theorem circuit_normal_form (n : ℕ) (C : Circuit)
    (legal : ∀ g ∈ C.gates, gateAllowed g) (hc : C.gates.countP isPaid ≤ n + 1) :
    ∃ p : slotProgram (n + n) (n + 1), ∀ x y : BitVec n,
      toScalar (C.eval (encodedBits x ++ encodedBits y)) =
        runProgram (n + n) (n + 1) p (Fin.append x y) := by
  obtain ⟨p, hp⟩ := represent_wires C.gates (n + n) (n + 1) (List.ofFn initialAffine) C.output hc
  refine ⟨p, fun x y => ?_⟩
  rw [encoded_eval C legal]
  symm
  simpa only [List.map_ofFn, Function.comp_def, eval_initialAffine, List.ofFn_fin_append] using
    hp (Fin.append x y)

end NormalForm

section Concentration

open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory

private noncomputable def mean {A : Type*} [Fintype A] (f : A → ℝ) : ℝ :=
  (∑ x, f x) / Fintype.card A

private theorem bounded_exp_mean {A : Type*} [Fintype A] [Nonempty A]
    (f : A → ℝ) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (s : ℝ) :
    mean (fun x => Real.exp (s * (mean f - f x))) ≤ Real.exp (s ^ 2 / 8) := by
  classical
  letI : MeasurableSpace A := ⊤
  letI : MeasurableSingletonClass A := ⟨fun _ => trivial⟩
  let μ : Measure A := (↑(Fintype.card A) : ℝ≥0∞)⁻¹ • Measure.count
  have hpos : 0 < Fintype.card A := Fintype.card_pos
  have hne : (↑(Fintype.card A) : ℝ≥0∞) ≠ 0 := by exact_mod_cast hpos.ne'
  letI : IsProbabilityMeasure μ := by
    constructor
    simpa [μ, Measure.count_univ, ENat.card_eq_coe_fintype_card] using
      ENNReal.inv_mul_cancel hne (by simp)
  have hIntegral (g : A → ℝ) : (∫ x, g x ∂μ) = mean g := by
    simp [μ, integral_smul_measure, mean, div_eq_mul_inv, mul_comm]
  have hn : ∀ x, -f x ∈ Set.Icc (-1 : ℝ) 0 := fun x =>
    ⟨neg_le_neg (hf x).2, neg_nonpos.mpr (hf x).1⟩
  have hm : AEMeasurable (fun x => -f x) μ := (measurable_of_finite _).aemeasurable
  have hs := (hasSubgaussianMGF_of_mem_Icc hm (ae_of_all μ hn)).mgf_le s
  have hneg : (∫ x, -f x ∂μ) = -mean f := by
    rw [integral_neg, hIntegral]
  rw [mgf, hIntegral, hneg] at hs
  convert hs using 1
  · congr 1
    funext x
    congr 1
    ring
  · norm_num
    ring

private theorem finite_lower_tail {A : Type*} [Fintype A] [Nonempty A]
    (N : ℕ) (hN : 0 < N) (f : A → ℝ) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
    (ε : ℝ) (hε : 0 ≤ ε) :
    ((Finset.univ.filter
      (fun p : Fin N → A => mean (fun i => f (p i)) + ε < mean f)).card : ℝ) /
      Fintype.card (Fin N → A) ≤ Real.exp (-2 * N * ε ^ 2) := by
  classical
  let σ : ℝ := 4 * ε
  let bad : Finset (Fin N → A) := Finset.univ.filter
    (fun p : Fin N → A => mean (fun i => f (p i)) + ε < mean f)
  let g (x : A) := Real.exp (σ * (mean f - f x))
  let G (p : Fin N → A) := Real.exp (∑ i : Fin N, σ * (mean f - f (p i)))
  have ha : (0 : ℝ) < Fintype.card A := by exact_mod_cast (Fintype.card_pos : 0 < Fintype.card A)
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hs : 0 ≤ σ := mul_nonneg (by norm_num) hε
  have hOne : (∑ x, g x) ≤ Real.exp (σ ^ 2 / 8) * Fintype.card A := by
    exact (div_le_iff₀ ha).mp (bounded_exp_mean f hf σ)
  have hAll : ∑ p, G p ≤ (Fintype.card A : ℝ) ^ N * Real.exp (N * (σ ^ 2 / 8)) := by
    calc
      ∑ p, G p = (∑ x, g x) ^ N := by
        simp_rw [G, Real.exp_sum]
        exact (Fintype.sum_pow g N).symm
      _ ≤ (Real.exp (σ ^ 2 / 8) * (Fintype.card A : ℝ)) ^ N :=
        pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le) hOne N
      _ = (Fintype.card A : ℝ) ^ N * Real.exp (N * (σ ^ 2 / 8)) := by
        rw [mul_pow, Real.exp_nat_mul, mul_comm]
  have hBad : (bad.card : ℝ) * Real.exp (σ * N * ε) ≤ ∑ p, G p := by
    calc
      _ = ∑ _p ∈ bad, Real.exp (σ * N * ε) := by simp
      _ ≤ ∑ p ∈ bad, G p := by
        apply Finset.sum_le_sum
        intro p hp
        have hval : mean (fun i => f (p i)) + ε < mean f :=
          (Finset.mem_filter.mp hp).2
        have hSum : (∑ i : Fin N, f (p i)) + ε * N < mean f * N := by
          have h := mul_lt_mul_of_pos_right hval hn
          simpa [mean, Finset.card_univ, Fintype.card_fin, add_mul, div_mul_cancel₀, hn.ne'] using h
        have hdev : (N : ℝ) * ε ≤ ∑ i : Fin N, (mean f - f (p i)) := by
          simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul]
          nlinarith
        unfold G
        rw [← Finset.mul_sum]
        apply Real.exp_le_exp.mpr
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hdev hs
      _ ≤ ∑ p, G p :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun p _ _ => (Real.exp_pos _).le
  have hCard : (Fintype.card (Fin N → A) : ℝ) = (Fintype.card A : ℝ) ^ N := by
    simp [Fintype.card_fun]
  apply (div_le_iff₀ (by rw [hCard]; exact pow_pos ha _)).mpr
  rw [hCard]
  calc
    (bad.card : ℝ) ≤
        ((Fintype.card A : ℝ) ^ N * Real.exp (N * (σ ^ 2 / 8))) / Real.exp (σ * N * ε) :=
      (le_div_iff₀ (Real.exp_pos _)).mpr (hBad.trans hAll)
    _ = Real.exp (-2 * N * ε ^ 2) * (Fintype.card A : ℝ) ^ N := by
      rw [mul_div_assoc, ← Real.exp_sub, mul_comm]
      congr 1
      congr 1
      unfold σ
      ring

private noncomputable def tailFailures {A I : Type*} [Fintype A] [Fintype I]
    (N : ℕ) (f : I → A → ℝ) (ε : ℝ) : Finset (Fin N → A) := by
  classical
  exact Finset.univ.biUnion fun i =>
    Finset.univ.filter (fun p : Fin N → A => mean (fun j => f i (p j)) + ε < mean (f i))

private theorem mem_tail_failures {A I : Type*} [Fintype A] [Fintype I]
    (N : ℕ) (f : I → A → ℝ) (ε : ℝ) (p : Fin N → A) :
    p ∈ tailFailures N f ε ↔ ∃ i, mean (fun j => f i (p j)) + ε < mean (f i) := by
  classical
  simp [tailFailures]

private theorem finite_tail_union {A I : Type*} [Fintype A] [Nonempty A] [Fintype I]
    (N : ℕ) (hN : 0 < N) (f : I → A → ℝ)
    (hf : ∀ i x, 0 ≤ f i x ∧ f i x ≤ 1) (ε : ℝ) (hε : 0 ≤ ε) :
    ((tailFailures N f ε).card : ℝ) / Fintype.card (Fin N → A) ≤
      (Fintype.card I : ℝ) * Real.exp (-2 * N * ε ^ 2) := by
  classical
  let P := fun i : I =>
    Finset.univ.filter (fun p : Fin N → A => mean (fun j => f i (p j)) + ε < mean (f i))
  have h := Finset.card_biUnion_le (s := (Finset.univ : Finset I)) (t := P)
  have hcard : ((tailFailures N f ε).card : ℝ) ≤ ∑ i, ((P i).card : ℝ) := by
    exact_mod_cast h
  calc
    _ ≤ (∑ i, ((P i).card : ℝ)) / Fintype.card (Fin N → A) :=
      div_le_div_of_nonneg_right hcard (by positivity)
    _ = ∑ i, ((P i).card : ℝ) / Fintype.card (Fin N → A) :=
      Finset.sum_div _ _ _
    _ ≤ ∑ _ : I, Real.exp (-2 * N * ε ^ 2) :=
      Finset.sum_le_sum (fun i _ => finite_lower_tail N hN (f i) (hf i) ε hε)
    _ = _ := by simp

private theorem exponential_union_small (M : ℕ) (u : ℝ) (h : (M : ℝ) + 3 ≤ u) :
    (2 : ℝ) ^ M * Real.exp (-u) ≤ 1 / 8 := by
  have he : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have h3 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) he 3
  rw [← Real.exp_nat_mul] at h3
  have h8 : (8 : ℝ) ≤ Real.exp 3 := by norm_num at h3 ⊢; simpa using h3
  calc
    _ ≤ Real.exp 1 ^ M * Real.exp (-u) :=
      mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (by norm_num) he M) (Real.exp_pos _).le
    _ = Real.exp ((M : ℝ) - u) := by
      rw [← Real.exp_nat_mul, mul_one, ← Real.exp_add, sub_eq_add_neg]
    _ ≤ Real.exp (-3) := Real.exp_le_exp.mpr (by linarith)
    _ = (Real.exp 3)⁻¹ := Real.exp_neg 3
    _ ≤ 1 / 8 := by
      rw [one_div]
      exact (inv_le_inv₀ (Real.exp_pos _) (by norm_num)).mpr h8

private theorem tails_size_small {A I : Type*} [Fintype A] [Nonempty A] [Fintype I]
    (N M : ℕ) (hN : 0 < N) (f : I → A → ℝ)
    (hf : ∀ i x, 0 ≤ f i x ∧ f i x ≤ 1) (ε : ℝ) (hε : 0 ≤ ε)
    (hI : Fintype.card I ≤ 2 ^ M) (hlarge : (M : ℝ) + 3 ≤ 2 * N * ε ^ 2) :
    ((tailFailures N f ε).card : ℝ) / Fintype.card (Fin N → A) ≤ 1 / 8 := by
  apply (finite_tail_union N hN f hf ε hε).trans
  have hIr : (Fintype.card I : ℝ) ≤ (2 : ℝ) ^ M := by exact_mod_cast hI
  have heq : (-2 : ℝ) * N * ε ^ 2 = -(2 * N * ε ^ 2) := by ring
  rw [heq]
  exact (mul_le_mul_of_nonneg_right hIr (Real.exp_pos _).le).trans
    (exponential_union_small M _ hlarge)

end Concentration

section Panels

open scoped BigOperators
open PEqualNP.CircuitLowerBounds

private def keyFunctional {k : ℕ} (v : BitVec k) : BitVec k →ₗ[BitField] BitField where
  toFun := dotProduct v
  map_add' a b := dotProduct_add v a b
  map_smul' c x := dotProduct_smul c v x

private noncomputable def hit {A : Type*} (p : A → Prop) (x : A) : ℝ :=
  if @decide (p x) (Classical.propDecidable _) then 1 else 0

private theorem hit_range {A : Type*} (p : A → Prop) (x : A) :
    0 ≤ hit p x ∧ hit p x ≤ 1 := by
  unfold hit
  split <;> norm_num

private theorem key_average {k : ℕ} (v : BitVec k) (hv : v ≠ 0) (c : BitField) :
    mean (hit (fun s => dotProduct v s = c)) = 1 / 2 := by
  classical
  let f := keyFunctional v
  have hf : f ≠ 0 := by
    intro h
    apply hv
    funext i
    have z := LinearMap.congr_fun h (basisBit i)
    simpa [f, keyFunctional, dot_basisBit] using z
  obtain ⟨u, hu⟩ := maps_one f hf
  letI : Fintype (LinearMap.ker f) := Fintype.ofFinite _
  have hcardNat : Fintype.card (LinearMap.ker f) ≠ 0 := Fintype.card_ne_zero
  have hcard : ((Fintype.card (LinearMap.ker f) : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast hcardNat
  let q := hit (fun s => dotProduct v s = c)
  have hs (b : BitField) (z : LinearMap.ker f) :
      dotProduct v ((b - 0) • u + (z : BitVec k)) = b := by
    change f ((b - 0) • u + (z : BitVec k)) = b
    have hz : f (z : BitVec k) = 0 := z.2
    simp [hu, hz]
  have h := split_mean f u hu 0 q
  have hvalue (b : BitField) (z : LinearMap.ker f) :
      q ((b - 0) • u + (z : BitVec k)) = hit (fun x : BitField => x = c) b := by
    change hit (fun x : BitField => x = c) (dotProduct v ((b - 0) • u + (z : BitVec k))) = _
    rw [hs]
  rw [mean]
  change (∑ s, q s) / _ = _
  rw [h]
  simp only [hvalue, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  letI : Nonempty { z : BitVec k // f z = 0 } := ⟨⟨0, by simp⟩⟩
  rcases split_bits c with hc | hc
  · norm_num [hit, hc, hcard, hcardNat] <;> exact Fintype.card_ne_zero
  · norm_num [hit, hc, hcard, hcardNat] <;> exact Fintype.card_ne_zero

private abbrev KeyIndex (k : ℕ) := BitVec k × BitField

private noncomputable def keyProbe (k : ℕ) (w : KeyIndex k) (s : BitVec k) : ℝ :=
  if w.1 = 0 then 0 else hit (fun z => dotProduct w.1 z = w.2) s

private noncomputable def keyFailures (k : ℕ) : Finset (Fin (32 * (k + 1)) → BitVec k) :=
  tailFailures (32 * (k + 1)) (keyProbe k) (1 / 4)

private theorem vec_card (n : ℕ) : Fintype.card (BitVec n) = 2 ^ n := by
  simp [ZMod.card]

private theorem key_failures_bound (k : ℕ) :
    ((keyFailures k).card : ℝ) / Fintype.card (Fin (32 * (k + 1)) → BitVec k) ≤ 1 / 8 := by
  unfold keyFailures
  apply tails_size_small _ (k + 1) (by omega)
  · intro i s
    by_cases hi : i.1 = 0
    · simp [keyProbe, hi]
    · simpa [keyProbe, hi] using hit_range (fun z => dotProduct i.1 z = i.2) s
  · norm_num
  · simp [KeyIndex, Fintype.card_prod, vec_card, ZMod.card, pow_succ]
  · push_cast
    linarith [Nat.cast_nonneg (α := ℝ) k]

private theorem key_good {k : ℕ} (P : Fin (32 * (k + 1)) → BitVec k)
    (hp : P ∉ keyFailures k) (v : BitVec k) (hv : v ≠ 0) (c : BitField) :
    (1 / 4 : ℝ) ≤ mean (fun j => hit (fun s => dotProduct v s = c) (P j)) := by
  by_contra! h
  apply hp
  unfold keyFailures
  apply (mem_tail_failures _ _ _ _).mpr
  refine ⟨(v, c), ?_⟩
  have same : keyProbe k (v,c) = hit (fun s => dotProduct v s = c) := by
    funext s
    simp [keyProbe, hv]
  rw [same, key_average v hv]
  linarith

private abbrev ErrorIndex (n : ℕ) := slotProgram (n + n) (n + 1) × BitVec n × BitField

private noncomputable def errorProbe (n : ℕ) (v : ErrorIndex n) (x : BitVec n) : ℝ :=
  hit (fun z => runProgram (n + n) (n + 1) v.1 (Fin.append z v.2.1) ≠
    dotProduct z v.2.1 + v.2.2) x

private noncomputable def errorFailures (n d : ℕ) :
    Finset (Fin (2048 * n ^ 2 * d ^ 2) → BitVec n) := by
  letI := programFinite (n + n) (n + 1)
  exact tailFailures (2048 * n ^ 2 * d ^ 2) (errorProbe n) (1 / (12 * d))

private theorem error_index_card (n : ℕ) (hn : 0 < n) :
    letI := programFinite (n + n) (n + 1)
    Fintype.card (ErrorIndex n) ≤ 2 ^ (25 * n ^ 2 + n + 1) := by
  letI := programFinite (n + n) (n + 1)
  change Fintype.card (ErrorIndex n) ≤ _
  rw [Fintype.card_prod, Fintype.card_prod, vec_card, ZMod.card]
  simp only [pow_add, pow_one]
  rw [mul_assoc]
  exact Nat.mul_le_mul_right _ (normal_forms_card n hn)

private theorem error_failures_bound (n d : ℕ) (hn : 2 ≤ n) (hd : 0 < d) :
    ((errorFailures n d).card : ℝ) / Fintype.card (Fin (2048 * n ^ 2 * d ^ 2) → BitVec n) ≤ 1 / 8 := by
  letI := programFinite (n + n) (n + 1)
  change ((tailFailures _ (errorProbe n) _).card : ℝ) / _ ≤ _
  apply tails_size_small _ (25 * n ^ 2 + n + 1) (by positivity)
  · intro i s
    exact hit_range _ _
  · positivity
  · exact error_index_card n (by omega)
  · have hnr : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hdr : (0 : ℝ) < d := by exact_mod_cast hd
    push_cast
    have h : (2 : ℝ) * (2048 * (n : ℝ)^2 * (d : ℝ)^2) * (1 / (12 * (d : ℝ)))^2 =
        (256 / 9 : ℝ) * (n : ℝ)^2 := by
      field_simp [hdr.ne']
      <;> ring
    rw [h]
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ n by positivity) (sub_nonneg.mpr hnr)]

private theorem error_good {n d : ℕ} (P : Fin (2048 * n ^ 2 * d ^ 2) → BitVec n)
    (hp : P ∉ errorFailures n d) (i : ErrorIndex n) :
    mean (errorProbe n i) ≤ mean (fun j => errorProbe n i (P j)) + 1 / (12 * d) := by
  letI := programFinite (n + n) (n + 1)
  by_contra! h
  apply hp
  change P ∈ tailFailures _ (errorProbe n) _
  exact (mem_tail_failures _ _ _ _).mpr ⟨i, h⟩

private theorem panels_card_good {A B : Type*} [Fintype A] [Nonempty A]
    [Fintype B] [Nonempty B] (badA : Finset A) (badB : Finset B)
    (ha : (badA.card : ℝ) / Fintype.card A ≤ 1 / 8)
    (hb : (badB.card : ℝ) / Fintype.card B ≤ 1 / 8)
    (g : Finset (A × B)) (hg : ∀ a b, a ∉ badA → b ∉ badB → (a,b) ∈ g) :
    3 * Fintype.card (A × B) ≤ 4 * g.card := by
  classical
  have hA : (0 : ℝ) < Fintype.card A := by exact_mod_cast (Fintype.card_pos : 0 < Fintype.card A)
  have hB : (0 : ℝ) < Fintype.card B := by exact_mod_cast (Fintype.card_pos : 0 < Fintype.card B)
  have ha' : 8 * badA.card ≤ Fintype.card A := by
    have h : (8 : ℝ) * badA.card ≤ Fintype.card A := by linarith [(div_le_iff₀ hA).mp ha]
    exact_mod_cast h
  have hb' : 8 * badB.card ≤ Fintype.card B := by
    have h : (8 : ℝ) * badB.card ≤ Fintype.card B := by linarith [(div_le_iff₀ hB).mp hb]
    exact_mod_cast h
  have la : 7 * Fintype.card A ≤ 8 * badAᶜ.card := by
    rw [Finset.card_compl]
    omega
  have lb : 7 * Fintype.card B ≤ 8 * badBᶜ.card := by
    rw [Finset.card_compl]
    omega
  have hsub : badAᶜ ×ˢ badBᶜ ⊆ g := fun p h =>
    hg p.1 p.2 (Finset.mem_compl.mp (Finset.mem_product.mp h).1)
      (Finset.mem_compl.mp (Finset.mem_product.mp h).2)
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_product] at hcard
  rw [Fintype.card_prod]
  have hh := Nat.mul_le_mul la lb
  ring_nf at hh ⊢
  omega

end Panels

section Compiler

open scoped BigOperators
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

private def backOK : ℕ → List Gate → Prop
  | _, [] => True
  | n, g :: G => (∀ i ∈ g.inputs, i < n) ∧ backOK (n + 1) G

private def validTape (n : ℕ) (G : List Gate) : Prop :=
  backOK n G ∧ ∀ g ∈ G, gateAllowed g

private theorem back_snoc (n : ℕ) (G : List Gate) (g : Gate)
    (hG : backOK n G) (hg : ∀ i ∈ g.inputs, i < n + G.length) :
    backOK n (G ++ [g]) := by
  induction G generalizing n with
  | nil => simpa [backOK] using hg
  | cons k K ih =>
    exact ⟨hG.1, ih (n + 1) hG.2 (fun i hi => by
      have h := hg i hi
      simp only [List.length_cons] at h
      omega)⟩

private theorem index_back (n : ℕ) (G : List Gate) (hG : backOK n G)
    (j : ℕ) (hj : j < G.length) :
    ∀ i ∈ (G.getD j ⟨.or, []⟩).inputs, i < n + j := by
  induction G generalizing n j with
  | nil => simp at hj
  | cons g G ih =>
    cases j with
    | zero =>
      exact fun i hi => hG.1 i hi
    | succ j =>
      intro i hi
      have hj' : j < G.length := by simpa using hj
      have h := ih (n + 1) hG.2 j hj' i hi
      omega

private theorem tape_readsBack (n : ℕ) (G : List Gate) (out : ℕ) (h : validTape n G) :
    ReadsBack n ⟨G, out⟩ := fun j hj i hi => index_back n G h.1 j hj i hi

private theorem tape_snoc (n : ℕ) (G : List Gate) (g : Gate) (hG : validTape n G)
    (legal : gateAllowed g) (hargs : ∀ i ∈ g.inputs, i < n + G.length) :
    validTape n (G ++ [g]) := by
  refine ⟨back_snoc n G g hG.1 hargs, ?_⟩
  intro a ha
  rcases List.mem_append.mp ha with h | h
  · exact hG.2 a h
  · simpa using (List.mem_singleton.mp h ▸ legal)

private theorem wires_append (G H : List Gate) (w : List BitField) :
    fieldWires (G ++ H) w = fieldWires H (fieldWires G w) := by
  simp [fieldWires, List.foldl_append]

private theorem wires_length (G : List Gate) (w : List BitField) :
    (fieldWires G w).length = w.length + G.length := by
  induction G generalizing w with
  | nil => simp [fieldWires]
  | cons g G ih =>
    rw [fieldWires_cons, ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

private theorem reads_input (G : List Gate) (w : List BitField) (i : ℕ) (hi : i < w.length) :
    (fieldWires G w).getD i 0 = w.getD i 0 := by
  induction G generalizing w with
  | nil => rfl
  | cons g G ih =>
    rw [fieldWires_cons, ih _ (by simp; omega)]
    change (w ++ _)[i]?.getD 0 = w[i]?.getD 0
    rw [List.getElem?_append_left hi]

private noncomputable def readWire {n : ℕ} (G : List Gate) (i : ℕ) (x : BitVec n) : BitField :=
  (fieldWires G (List.ofFn x)).getD i 0

private def hasWire {n : ℕ} (G : List Gate) (i : ℕ) (f : BitVec n → BitField) : Prop :=
  i < n + G.length ∧ ∀ x, readWire G i x = f x

private theorem hasWire_ext {n : ℕ} (G H : List Gate) (i : ℕ) (f : BitVec n → BitField)
    (h : hasWire G i f) : hasWire (G ++ H) i f := by
  refine ⟨by have hi := h.1; simp; omega, ?_⟩
  intro x
  unfold readWire
  rw [wires_append, reads_input H _ _ (by rw [wires_length, List.length_ofFn]; exact h.1)]
  exact h.2 x

private theorem hasInput {n : ℕ} (i : Fin n) :
    hasWire ([] : List Gate) i (fun x : BitVec n => x i) := by
  refine ⟨by simpa using i.isLt, ?_⟩
  intro x
  change (List.ofFn x)[i.val]?.getD 0 = x i
  simp [i.isLt]

private theorem hasNewGate {n : ℕ} (G : List Gate) (g : Gate) :
    hasWire (G ++ [g]) (n + G.length) (fun x : BitVec n => gateValue g (fun i => readWire G i x)) := by
  refine ⟨by simp, ?_⟩
  intro x
  unfold readWire
  rw [wires_append]
  let state := fieldWires G (List.ofFn x)
  have hlen : state.length = n + G.length := by simp [state, wires_length]
  change (state ++ [gateValue g (fun i => state.getD i 0)]).getD (n + G.length) 0 = _
  rw [← hlen]
  change (state ++ [_])[state.length]?.getD 0 = _
  simp [List.getElem?_append_right le_rfl]
  rfl

private theorem scalar_add_one_one (a : BitField) : 1 + (1 + a) = a := by
  revert a
  decide

private theorem two_gate_and (a b : ℕ) (w : ℕ → BitField) :
    gateValue ⟨.and,[a,b]⟩ w = w a * w b := by
  simp [gateValue, gateInputs, gateAffine, isPaid, gateCharge]

private theorem two_gate_parity (a b : ℕ) (w : ℕ → BitField) :
    gateValue ⟨.mod 2,[a,b]⟩ w = 1 + w a + w b := by
  simp [gateValue, gateInputs, gateAffine, isPaid, gateCharge]

private theorem one_gate_not (a : ℕ) (w : ℕ → BitField) :
    gateValue ⟨.not,[a]⟩ w = 1 + w a := by
  simp [gateValue, gateInputs, gateAffine, isPaid, gateCharge]

private theorem zero_gate_false (w : ℕ → BitField) : gateValue ⟨.or,[]⟩ w = 0 := by
  simp [gateValue, gateInputs, gateAffine, isPaid, gateCharge]

private theorem zero_gate_true (w : ℕ → BitField) : gateValue ⟨.and,[]⟩ w = 1 := by
  simp [gateValue, gateInputs, gateAffine, isPaid, gateCharge]

private def extendsBy (G H : List Gate) (budget : ℕ) : Prop :=
  ∃ T, H = G ++ T ∧ T.countP isPaid ≤ budget

private theorem extend_original {n : ℕ} {G H : List Gate} {b i : ℕ}
    {f : BitVec n → BitField} (h : extendsBy G H b) (hi : hasWire G i f) :
    hasWire H i f := by
  obtain ⟨T, rfl, _⟩ := h
  exact hasWire_ext G T i f hi

private theorem extend_trans {G H I : List Gate} {b c : ℕ}
    (h : extendsBy G H b) (hh : extendsBy H I c) : extendsBy G I (b + c) := by
  obtain ⟨T, rfl, hT⟩ := h
  obtain ⟨S, rfl, hS⟩ := hh
  exact ⟨T ++ S, by simp [List.append_assoc], by simpa using Nat.add_le_add hT hS⟩

private theorem emit_constant {n : ℕ} (G : List Gate) (hG : validTape n G)
    (c : BitField) :
    ∃ H i, extendsBy G H 0 ∧ validTape n H ∧ hasWire H i (fun _ : BitVec n => c) := by
  rcases split_bits c with rfl | rfl
  · let g : Gate := ⟨.or, []⟩
    refine ⟨G ++ [g], n + G.length, ⟨[g], rfl, ?_⟩, tape_snoc n G g hG ?_ ?_, ?_⟩
    · simp [g, isPaid, gateCharge]
    · simp [g, gateAllowed]
    · simp [g]
    · simpa only [g, zero_gate_false] using (hasNewGate (n := n) G g)
  · let g : Gate := ⟨.and, []⟩
    refine ⟨G ++ [g], n + G.length, ⟨[g], rfl, ?_⟩, tape_snoc n G g hG ?_ ?_, ?_⟩
    · simp [g, isPaid, gateCharge]
    · simp [g, gateAllowed]
    · simp [g]
    · simpa only [g, zero_gate_true] using (hasNewGate (n := n) G g)

private theorem emit_product {n : ℕ} (G : List Gate) (hG : validTape n G)
    (a b : ℕ) (A B : BitVec n → BitField) (ha : hasWire G a A) (hb : hasWire G b B) :
    ∃ H i, extendsBy G H 1 ∧ validTape n H ∧ hasWire H i (fun x => A x * B x) := by
  let g : Gate := ⟨.and, [a, b]⟩
  refine ⟨G ++ [g], n + G.length, ⟨[g], rfl, ?_⟩, tape_snoc n G g hG ?_ ?_, ?_⟩
  · simp [g, isPaid, gateCharge]
  · simp [g, gateAllowed]
  · simpa [g] using ⟨ha.1, hb.1⟩
  · have h := hasNewGate (n := n) G g
    refine ⟨h.1, fun x => ?_⟩
    simpa only [g, two_gate_and, ha.2 x, hb.2 x] using h.2 x

private theorem emit_addition {n : ℕ} (G : List Gate) (hG : validTape n G)
    (a b : ℕ) (A B : BitVec n → BitField) (ha : hasWire G a A) (hb : hasWire G b B) :
    ∃ H i, extendsBy G H 0 ∧ validTape n H ∧ hasWire H i (fun x => A x + B x) := by
  let p : Gate := ⟨.mod 2, [a,b]⟩
  let K := G ++ [p]
  let c := n + G.length
  let q : Gate := ⟨.not,[c]⟩
  have hK : validTape n K := tape_snoc n G p hG (by simp [p, gateAllowed])
    (by simpa [p] using ⟨ha.1, hb.1⟩)
  have hSum : hasWire K c (fun x => 1 + A x + B x) := by
    have h := hasNewGate (n := n) G p
    refine ⟨h.1, fun x => ?_⟩
    simpa only [p, two_gate_parity, ha.2 x, hb.2 x] using h.2 x
  refine ⟨K ++ [q], n + K.length, ⟨[p,q], by simp [K, List.append_assoc], ?_⟩,
    tape_snoc n K q hK (by simp [q, gateAllowed]) (by simpa [q] using hSum.1), ?_⟩
  · simp [p, q, isPaid, gateCharge]
  · have h := hasNewGate (n := n) K q
    refine ⟨h.1, fun x => ?_⟩
    calc
      _ = 1 + (1 + A x + B x) := by simpa only [q, one_gate_not, hSum.2 x] using h.2 x
      _ = 1 + (1 + (A x + B x)) := by ring
      _ = _ := scalar_add_one_one _

private theorem emit_sum {n : ℕ} {ι : Type*} (S : Finset ι)
    (G : List Gate) (hG : validTape n G) (wire : ι → ℕ) (F : ι → BitVec n → BitField)
    (hwire : ∀ i ∈ S, hasWire G (wire i) (F i)) :
    ∃ H j, extendsBy G H 0 ∧ validTape n H ∧ hasWire H j (fun x => ∑ i ∈ S, F i x) := by
  classical
  induction S using Finset.induction_on generalizing G with
  | empty =>
    simpa using emit_constant G hG 0
  | @insert i S hi ih =>
    have hiWire := hwire i (Finset.mem_insert_self i S)
    have hsWire : ∀ j ∈ S, hasWire G (wire j) (F j) :=
      fun j hj => hwire j (Finset.mem_insert_of_mem hj)
    obtain ⟨K, j, hg, hk, hw⟩ := ih G hG hsWire
    obtain ⟨H, w, e, hh, hval⟩ := emit_addition K hk (wire i) j _ _ (extend_original hg hiWire) hw
    exact ⟨H, w, by simpa using extend_trans hg e, hh, by simpa [Finset.sum_insert hi] using hval⟩

private theorem emit_linear {n k : ℕ} (G : List Gate) (hG : validTape n G)
    (wire : Fin k → ℕ) (F : BitVec n → BitVec k) (coeff : BitVec k)
    (hw : ∀ i, hasWire G (wire i) (fun x => F x i)) :
    ∃ H j, extendsBy G H 0 ∧ validTape n H ∧ hasWire H j (fun x => dotProduct coeff (F x)) := by
  classical
  let S := Finset.univ.filter (fun i => coeff i = 1)
  obtain ⟨H,j,ext,hok,he⟩ := emit_sum S G hG wire (fun i x => F x i) (fun i _ => hw i)
  refine ⟨H,j,ext,hok,he.1,?_⟩
  intro x
  rw [he.2]
  change (∑ i ∈ Finset.univ.filter (fun i => coeff i = 1), F x i) =
    ∑ i, coeff i * F x i
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  rcases split_bits (coeff i) with h | h <;> simp [h]

private theorem emit_dot_sum {n : ℕ} {ι : Type*} (S : Finset ι)
    (G : List Gate) (hG : validTape n G) (left right : ι → ℕ)
    (A B : ι → BitVec n → BitField)
    (ha : ∀ i ∈ S, hasWire G (left i) (A i)) (hb : ∀ i ∈ S, hasWire G (right i) (B i)) :
    ∃ H j, extendsBy G H S.card ∧ validTape n H ∧
      hasWire H j (fun x => ∑ i ∈ S, A i x * B i x) := by
  classical
  induction S using Finset.induction_on generalizing G with
  | empty => simpa using emit_constant G hG 0
  | @insert i S hi ih =>
    obtain ⟨K,j,extK,hK,Hk⟩ := ih G hG
      (fun x hx => ha x (Finset.mem_insert_of_mem hx)) (fun x hx => hb x (Finset.mem_insert_of_mem hx))
    obtain ⟨Q,f,extQ,hQ,Hq⟩ := emit_product K hK (left i) (right i) (A i) (B i)
      (extend_original extK (ha i (Finset.mem_insert_self i S)))
      (extend_original extK (hb i (Finset.mem_insert_self i S)))
    obtain ⟨H,w,extH,hH,Hh⟩ := emit_addition Q hQ f j _ _ Hq (extend_original extQ Hk)
    refine ⟨H,w,?_,hH,?_⟩
    · simpa [Finset.card_insert_of_notMem hi] using extend_trans (extend_trans extK extQ) extH
    · simpa [Finset.sum_insert hi] using Hh

private def takeLeft {n : ℕ} (z : BitVec (n + n)) : BitVec n :=
  fun i => z (Fin.castAdd n i)

private def takeRight {n : ℕ} (z : BitVec (n + n)) : BitVec n :=
  fun i => z (Fin.natAdd n i)

private theorem color_circuit (k : ℕ) (col : Fin k → Fin 3) :
    ∃ C : Circuit, ReadsBack (2 * (k + 1)) C ∧ (∀ g ∈ C.gates, gateAllowed g) ∧
      C.gates.countP isPaid ≤ k + 2 ∧ ∀ x y : BitVec (k + 1),
        toScalar (C.eval (encodedBits x ++ encodedBits y)) = colorAnswer col x y := by
  let n := k + 1
  let N := n + n
  let LX (i : Fin n) : Fin N := Fin.castAdd n i
  let RY (i : Fin n) : Fin N := Fin.natAdd n i
  let X (z : BitVec N) : BitVec n := takeLeft z
  let Y (z : BitVec N) : BitVec n := takeRight z
  let XL (i : Fin k) : ℕ := (LX i.succ).val
  let YR (i : Fin k) : ℕ := (RY i.succ).val
  have hX (i : Fin n) : hasWire [] (LX i).val (fun z => X z i) := hasInput (LX i)
  have hY (i : Fin n) : hasWire [] (RY i).val (fun z => Y z i) := hasInput (RY i)
  have hEmpty : validTape N [] := by simp [validTape, backOK]
  obtain ⟨D, dot, extD', hD, dotD'⟩ := emit_dot_sum Finset.univ [] hEmpty XL YR
    (fun i z => X z i.succ) (fun i z => Y z i.succ) (fun i _ => hX i.succ) (fun i _ => hY i.succ)
  have extD : extendsBy [] D k := by simpa using extD'
  have dotD : hasWire D dot (fun z => dotProduct (Fin.tail (X z)) (Fin.tail (Y z))) := by
    simpa [dotProduct, Fin.tail] using dotD'
  obtain ⟨L,l,extL,hL,lL⟩ := emit_linear D hD YR (fun z => Fin.tail (Y z)) (tagX ∘ col)
    (fun i => extend_original extD (hY i.succ))
  have extL' : extendsBy [] L k := by simpa using extend_trans extD extL
  obtain ⟨M,r,extM,hM,rM⟩ := emit_linear L hL YR (fun z => Fin.tail (Y z)) (tagY ∘ col)
    (fun i => extend_original extL' (hY i.succ))
  have extM' : extendsBy [] M k := by simpa using extend_trans extL' extM
  obtain ⟨R,d,extR,hR,dR⟩ := emit_linear M hM YR (fun z => Fin.tail (Y z))
    (fun i => tagX (col i) * tagY (col i)) (fun i => extend_original extM' (hY i.succ))
  have extR' : extendsBy [] R k := by simpa using extend_trans extM' extR
  obtain ⟨P,p,extP,hP,pP⟩ := emit_product R hR l r _ _
    (extend_original (extend_trans extM extR) lL) (extend_original extR rM)
  obtain ⟨Q,q,extQ,hQ,qQ'⟩ := emit_addition P hP p d _ _ pP (extend_original extP dR)
  have qQ : hasWire Q q (fun z => colorPolynomial col (Fin.tail (Y z))) := qQ'
  have extQ' : extendsBy [] Q (k+1) := by simpa using extend_trans (extend_trans extR' extP) extQ
  obtain ⟨U,b,extU,hU,bU⟩ := emit_addition Q hQ (LX 0).val q _ _
    (extend_original extQ' (hX 0)) qQ
  have extU' : extendsBy [] U (k+1) := by simpa using extend_trans extQ' extU
  obtain ⟨V,t,extV,hV,tV⟩ := emit_product U hU (RY 0).val b _ _
    (extend_original extU' (hY 0)) bU
  have extDV := extend_trans (extend_trans (extend_trans (extend_trans (extend_trans extL extM) extR)
    extP) extQ) (extend_trans extU extV)
  obtain ⟨H,out,extH,hH,hans⟩ := emit_addition V hV dot t _ _ (extend_original extDV dotD) tV
  obtain ⟨tail,hTail,hCount⟩ := extend_trans (extend_trans extU' extV) extH
  refine ⟨⟨H,out⟩, ?_, hH.2, ?_, ?_⟩
  · simpa [N, n, two_mul] using tape_readsBack N H out hH
  · simpa [hTail, Nat.add_assoc] using hCount
  · intro x y
    rw [encoded_eval _ hH.2]
    have h := hans.2 (Fin.append x y)
    have lx : X (Fin.append x y) = x := by
      funext i
      exact Fin.append_left x y i
    have ry : Y (Fin.append x y) = y := by
      funext i
      exact Fin.append_right x y i
    change (fieldWires H (List.ofFn (Fin.append x y))).getD out 0 =
      colorAnswer col (X (Fin.append x y)) (Y (Fin.append x y)) at h
    rwa [List.ofFn_fin_append, lx, ry] at h

end Compiler

section Loss

open scoped BigOperators

private theorem mean_pointwise {A : Type*} [Fintype A] {f g : A → ℝ}
    (h : ∀ a, f a = g a) : mean f = mean g := by
  congr 1
  funext a
  exact h a

private theorem mean_nonneg_fn {A : Type*} [Fintype A] {f : A → ℝ}
    (h : ∀ a, 0 ≤ f a) : 0 ≤ mean f :=
  div_nonneg (Finset.sum_nonneg fun a _ => h a) (by positivity)

private theorem mean_mono_fn {A : Type*} [Fintype A] {f g : A → ℝ}
    (h : ∀ a, f a ≤ g a) : mean f ≤ mean g :=
  div_le_div_of_nonneg_right (Finset.sum_le_sum fun a _ => h a) (by positivity)

private theorem mean_constant {A : Type*} [Fintype A] [Nonempty A] (q : ℝ) :
    mean (fun _ : A => q) = q := by
  have h : (Fintype.card A : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [mean, mul_comm, h]

private theorem mean_add_fn {A : Type*} [Fintype A] (f g : A → ℝ) :
    mean (fun a => f a + g a) = mean f + mean g := by
  simp [mean, Finset.sum_add_distrib, add_div]

private theorem mean_scale_fn {A : Type*} [Fintype A] (c : ℝ) (f : A → ℝ) :
    mean (fun a => c * f a) = c * mean f := by
  unfold mean
  rw [← Finset.mul_sum, mul_div_assoc]

private theorem mean_sum_fn {A I : Type*} [Fintype A] (S : Finset I) (f : I → A → ℝ) :
    mean (fun a => ∑ i ∈ S, f i a) = ∑ i ∈ S, mean (f i) := by
  unfold mean
  rw [Finset.sum_comm, Finset.sum_div]

private theorem hit_eq_one {A : Type*} {p : A → Prop} {a : A} (h : p a) :
    hit p a = 1 := by simp [hit, h]

private theorem hit_eq_zero {A : Type*} {p : A → Prop} {a : A} (h : ¬ p a) :
    hit p a = 0 := by simp [hit, h]

private theorem scalar_ne_add_ne : ∀ a b : BitField, (a ≠ b) ↔ (a + b ≠ 0) := by decide

private theorem same_bit_toggle : ∀ a : BitField, a + (a + 1) = 1 := by decide

private theorem hit_toggle (a : BitField) :
    hit (fun b : BitField => b ≠ 0) a + hit (fun b : BitField => b ≠ 0) (a + 1) = 1 := by
  rcases split_bits a with rfl | rfl <;> norm_num [hit] <;> decide

private theorem mean_toggle_half {X : Type*} [AddCommGroup X] [Fintype X]
    (δ : X) (p : X → BitField) (h : ∀ z, p (z + δ) = p z + 1) :
    mean (hit (fun z => p z ≠ 0)) = 1 / 2 := by
  let f : X → ℝ := hit (fun z => p z ≠ 0)
  have hshift : mean (fun z => f (z + δ)) = mean f := by
    unfold mean
    congr 1
    exact Fintype.sum_equiv (Equiv.addRight δ) (fun z => f (z + δ)) f (fun _ => rfl)
  have htwo : mean f + mean f = 1 := by
    calc
      _ = mean (fun z => f (z + δ)) + mean f := by rw [hshift]
      _ = mean (fun z => f (z + δ) + f z) := (mean_add_fn _ _).symm
      _ = mean (fun _ : X => (1 : ℝ)) := by
        apply mean_pointwise
        intro z
        change hit (fun b : BitField => b ≠ 0) (p (z + δ)) +
          hit (fun b : BitField => b ≠ 0) (p z) = 1
        rw [h z, add_comm]
        exact hit_toggle (p z)
      _ = _ := mean_constant 1
  change mean f = _
  linarith

private noncomputable def sliceError {X : Type*} [Fintype X] {n : ℕ}
    (inputs : X → BitVec n → BitVec n) (value : X → BitVec n → BitField)
    (y : BitVec n) (h : BitField) : ℝ :=
  mean (hit fun z => value z y ≠ dotProduct (inputs z y) y + h)

private theorem slice_error_nonneg {X : Type*} [Fintype X] {n : ℕ}
    (inputs : X → BitVec n → BitVec n) (value : X → BitVec n → BitField)
    (y : BitVec n) (h : BitField) : 0 ≤ sliceError inputs value y h :=
  mean_nonneg_fn fun a => (hit_range _ a).1

private theorem slice_half {X : Type*} [AddCommGroup X] [Fintype X] {n : ℕ}
    (inputs : X → BitVec n → BitVec n) (value : X → BitVec n → BitField)
    (y : BitVec n) (h : BitField) (δ : X) (v : BitVec n) (d : BitField)
    (hx : ∀ z, inputs (z + δ) y = inputs z y + v)
    (hc : ∀ z, value (z + δ) y = value z y + d)
    (hs : d + dotProduct v y = 1) :
    sliceError inputs value y h = 1 / 2 := by
  let p := fun z => value z y + (dotProduct (inputs z y) y + h)
  have heq : sliceError inputs value y h = mean (hit (fun z => p z ≠ 0)) := by
    have eq : (fun z => value z y ≠ dotProduct (inputs z y) y + h) = (fun z => p z ≠ 0) :=
      funext fun z => propext (scalar_ne_add_ne _ _)
    unfold sliceError
    rw [eq]
  rw [heq]
  apply mean_toggle_half δ
  intro z
  change value (z + δ) y + (dotProduct (inputs (z + δ) y) y + h) = _
  rw [hx, hc, add_dotProduct]
  calc
    _ = p z + (d + dotProduct v y) := by unfold p; ring
    _ = _ := by rw [hs]

private def edgeAddress {k : ℕ} (u v : Fin k) (t r s : BitField) : BitVec (k + 1) :=
  Fin.cons t (r • basisBit u + s • basisBit v)

private noncomputable def cornerSum {k : ℕ} (u v : Fin k)
    (E : BitVec (k + 1) → BitField → ℝ) : ℝ :=
  ∑ t : BitField, ∑ r : BitField, ∑ s : BitField, E (edgeAddress u v t r s) (t * r * s)

private noncomputable def keyTerm {k : ℕ} (P : Fin (32 * (k + 1)) → BitVec k)
    (E : BitVec (k + 1) → BitField → ℝ) : ℝ :=
  4 * mean (fun j => E (Fin.cons 0 (P j)) 0)

private noncomputable def weightedLoss {k m : ℕ} (P : Fin (32 * (k + 1)) → BitVec k)
    (u v : Fin m → Fin k) (w : Fin m → ℝ) (E : BitVec (k + 1) → BitField → ℝ) : ℝ :=
  ∑ i, w i * (keyTerm P E + cornerSum (u i) (v i) E)

private noncomputable def badWeight {k m : ℕ} (u v : Fin m → Fin k)
    (w : Fin m → ℝ) (col : Fin k → Fin 3) : ℝ :=
  ∑ i, if col (u i) = col (v i) then w i else 0

private theorem corner_nonneg {k : ℕ} (u v : Fin k) (E : BitVec (k + 1) → BitField → ℝ)
    (hE : ∀ y h, 0 ≤ E y h) : 0 ≤ cornerSum u v E :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => hE _ _

private theorem key_term_nonneg {k : ℕ} (P : Fin (32 * (k + 1)) → BitVec k)
    (E : BitVec (k + 1) → BitField → ℝ) (hE : ∀ y h, 0 ≤ E y h) :
    0 ≤ keyTerm P E :=
  mul_nonneg (by norm_num) (mean_nonneg_fn fun _ => hE _ _)

private theorem bad_le_total {k m : ℕ} (u v : Fin m → Fin k) (w : Fin m → ℝ)
    (hw : ∀ i, 0 ≤ w i) (col : Fin k → Fin 3) : badWeight u v w col ≤ ∑ i, w i := by
  unfold badWeight
  apply Finset.sum_le_sum
  intro i hi
  split <;> simp [hw i]

private theorem sum_lower_term {I : Type*} [Fintype I] (f : I → ℝ)
    (hf : ∀ i, 0 ≤ f i) (i : I) : f i ≤ ∑ j, f j := by
  classical
  exact Finset.single_le_sum (f := f) (fun j _ => hf j) (Finset.mem_univ i)

private theorem sum_two_bits (c : ℝ) : (∑ _ : BitField, c) = 2*c := by
  simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, Nat.cast_ofNat]

private def twoColour (b : BitField) : Fin 3 := if b = 0 then 0 else 1

private theorem two_colour_eq : ∀ a b : BitField, twoColour a = twoColour b ↔ a = b := by decide

private theorem weight_mean {k m : ℕ} (u v : Fin m → Fin k) (w : Fin m → ℝ)
    (huv : ∀ i, u i ≠ v i) :
    mean (fun col : BitVec k => badWeight u v w (twoColour ∘ col)) = (∑ i, w i) / 2 := by
  unfold badWeight
  rw [mean_sum_fn, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  let e : BitVec k → BitField := fun b => b (u i) + b (v i)
  have hshift (z : BitVec k) : e (z + basisBit (u i)) = e z + 1 := by
    simp [e, basisBit, Pi.add_apply, Ne.symm (huv i)]
    ring
  have hhalf := mean_toggle_half (basisBit (u i)) e hshift
  have term_eq (z : BitVec k) :
      (if (twoColour ∘ z) (u i) = (twoColour ∘ z) (v i) then w i else 0) =
        w i * (1 - hit (fun b => e b ≠ 0) z) := by
    by_cases hz : z (u i) = z (v i)
    · have h0 : ¬ e z ≠ 0 := by
        intro ne
        exact (scalar_ne_add_ne ..).mpr ne hz
      rw [hit_eq_zero (p := fun b : BitVec k => e b ≠ 0) h0]
      simp [Function.comp_apply, two_colour_eq, hz]
    · have h1 : e z ≠ 0 := (scalar_ne_add_ne ..).mp hz
      rw [hit_eq_one (p := fun b : BitVec k => e b ≠ 0) h1]
      simp [Function.comp_apply, two_colour_eq, hz]
  calc
    _ = mean (fun z => w i * (1 - hit (fun b => e b ≠ 0) z)) := mean_pointwise term_eq
    _ = w i * (1 - 1 / 2) := by
      rw [mean_scale_fn]
      unfold mean at hhalf ⊢
      simp only [Finset.sum_sub_distrib, sub_div]
      rw [hhalf]
      have h1 := mean_constant (A := BitVec k) 1
      exact congrArg (fun x => w i * (x - 1 / 2)) h1
    _ = _ := by ring

private theorem some_half_bad {k m : ℕ} (u v : Fin m → Fin k) (w : Fin m → ℝ)
    (huv : ∀ i, u i ≠ v i) : ∃ col, badWeight u v w col ≤ (∑ i, w i) / 2 := by
  classical
  by_contra! h
  have hsum :
      ∑ _ : BitVec k, (∑ i, w i) / 2 <
        ∑ col : BitVec k, badWeight u v w (twoColour ∘ col) :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun c _ => h (twoColour ∘ c)
  have hcard : (0 : ℝ) < Fintype.card (BitVec k) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (BitVec k))
  have havg := div_lt_div_of_pos_right hsum hcard
  change mean (fun _ : BitVec k => (∑ i, w i) / 2) <
    mean (fun c : BitVec k => badWeight u v w (twoColour ∘ c)) at havg
  rw [mean_constant, weight_mean u v w huv] at havg
  exact (lt_irrefl _ havg)

private theorem dot_cons {k : ℕ} (v : BitVec (k+1)) (t : BitField) (z : BitVec k) :
    dotProduct v (Fin.cons t z) = v 0 * t + dotProduct (Fin.tail v) z := by
  simp [dotProduct, Fin.sum_univ_succ, Fin.tail]

set_option maxHeartbeats 1000000 in
private theorem shift_rounds {X : Type*} [AddCommGroup X] [Fintype X] {k m : ℕ}
    (P : Fin (32*(k+1)) → BitVec k) (good : P ∉ keyFailures k)
    (u v : Fin m → Fin k) (w : Fin m → ℝ) (hw : ∀ i, 0 ≤ w i) (huv : ∀ i, u i ≠ v i)
    (inputs : X → BitVec (k+1) → BitVec (k+1)) (value : X → BitVec (k+1) → BitField)
    (δ : X) (direction : BitVec (k+1)) (hdir : direction ≠ 0) (slope : BitField)
    (hx : ∀ z y, inputs (z+δ) y = inputs z y + direction)
    (hv : ∀ z y, value (z+δ) y = value z y + slope) :
    ∃ col, badWeight u v w col ≤ weightedLoss P u v w (sliceError inputs value) := by
  let E := sliceError inputs value
  have hnonneg : ∀ y h, 0 ≤ E y h := slice_error_nonneg inputs value
  let b := slope + 1
  by_cases tail : Fin.tail direction = 0
  · have first : direction 0 = 1 := by
      rcases split_bits (direction 0) with hz | h1
      · have he : direction = 0 := by
          funext i
          refine Fin.cases hz ?_ i
          intro j
          exact congrFun tail j
        exact (hdir he).elim
      · exact h1
    have corner_half (i : Fin m) (r s : BitField) :
        E (edgeAddress (u i) (v i) b r s) (b*r*s) = 1/2 := by
      apply slice_half inputs value _ _ δ direction slope (fun z => hx z _) (fun z => hv z _)
      simp only [edgeAddress, dot_cons, first, tail, one_mul, zero_dotProduct, add_zero, b]
      exact same_bit_toggle slope
    have lower (i : Fin m) : 1 ≤ cornerSum (u i) (v i) E := by
      unfold cornerSum
      calc
        _ ≤ ∑ r : BitField, ∑ s : BitField, E (edgeAddress (u i) (v i) b r s) (b*r*s) := by
          have eq : (∑ r : BitField, ∑ s : BitField, E (edgeAddress (u i) (v i) b r s) (b*r*s)) =
              ∑ _ : BitField, ∑ _ : BitField, (1/2 : ℝ) := by
            apply Finset.sum_congr rfl
            intro r _
            exact Finset.sum_congr rfl (fun s _ => corner_half i r s)
          rw [eq, sum_two_bits, sum_two_bits]
          norm_num
        _ ≤ _ := sum_lower_term
          (fun t : BitField => ∑ r : BitField, ∑ s : BitField,
            E (edgeAddress (u i) (v i) t r s) (t*r*s))
          (fun _ => Finset.sum_nonneg fun r _ => Finset.sum_nonneg fun s _ => hnonneg _ _) b
    refine ⟨fun _ => 0, (bad_le_total u v w hw _).trans ?_⟩
    unfold weightedLoss
    apply Finset.sum_le_sum
    intro i _
    have bound : 1 ≤ keyTerm P E + cornerSum (u i) (v i) E :=
      (lower i).trans (le_add_of_nonneg_left (key_term_nonneg P E hnonneg))
    calc
      w i = w i * 1 := (mul_one (w i)).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left bound (hw i)
  · let q := fun j => hit (fun z => dotProduct (Fin.tail direction) z = b) (P j)
    have hq : 1 / 4 ≤ mean q := key_good P good (Fin.tail direction) tail b
    have point (j : Fin (32*(k+1))) : (1 / 2 : ℝ) * q j ≤ E (Fin.cons 0 (P j)) 0 := by
      by_cases h : dotProduct (Fin.tail direction) (P j) = b
      · have hs : slope + dotProduct direction (Fin.cons 0 (P j)) = 1 := by
          rw [dot_cons, mul_zero, zero_add, h]
          exact same_bit_toggle slope
        change (1 / 2 : ℝ) * q j ≤ sliceError inputs value (Fin.cons 0 (P j)) 0
        rw [slice_half inputs value _ 0 δ direction slope (fun z => hx z _) (fun z => hv z _) hs]
        unfold q
        rw [hit_eq_one (p := fun z => dotProduct (Fin.tail direction) z = b) h, mul_one]
      · unfold q
        rw [hit_eq_zero (p := fun z => dotProduct (Fin.tail direction) z = b) h, mul_zero]
        exact hnonneg _ _
    have hkey : 1 / 2 ≤ keyTerm P E := by
      have he := mean_mono_fn point
      rw [mean_scale_fn] at he
      unfold keyTerm
      linarith
    obtain ⟨col, hcol⟩ := some_half_bad u v w huv
    refine ⟨col, hcol.trans ?_⟩
    unfold weightedLoss
    rw [Finset.sum_div]
    apply Finset.sum_le_sum
    intro i _
    calc
      w i / 2 = w i * (1 / 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (by linarith [hkey, corner_nonneg (u i) (v i) E hnonneg]) (hw i)

private theorem loss_mono {k m : ℕ} (P : Fin (32*(k+1)) → BitVec k)
    (u v : Fin m → Fin k) (w : Fin m → ℝ) (hw : ∀ i, 0 ≤ w i)
    (E F : BitVec (k+1) → BitField → ℝ) (h : ∀ y t, E y t ≤ F y t) :
    weightedLoss P u v w E ≤ weightedLoss P u v w F := by
  unfold weightedLoss
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_left _ (hw i)
  apply add_le_add
  · exact mul_le_mul_of_nonneg_left (mean_mono_fn fun j => h _ _) (by norm_num)
  · exact Finset.sum_le_sum fun _ _ => Finset.sum_le_sum fun _ _ =>
      Finset.sum_le_sum fun _ _ => h _ _

private theorem loss_add {k m : ℕ} (P : Fin (32*(k+1)) → BitVec k)
    (u v : Fin m → Fin k) (w : Fin m → ℝ) (E F : BitVec (k+1) → BitField → ℝ) :
    weightedLoss P u v w (fun y t => E y t + F y t) =
      weightedLoss P u v w E + weightedLoss P u v w F := by
  unfold weightedLoss
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [keyTerm, cornerSum, mean_add_fn, Finset.sum_add_distrib]
  ring

private theorem loss_scale {k m : ℕ} (P : Fin (32*(k+1)) → BitVec k)
    (u v : Fin m → Fin k) (w : Fin m → ℝ) (E : BitVec (k+1) → BitField → ℝ) (c : ℝ) :
    weightedLoss P u v w (fun y t => c * E y t) = c * weightedLoss P u v w E := by
  unfold weightedLoss
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [keyTerm, cornerSum, mean_scale_fn, ← Finset.mul_sum]
  ring

private theorem loss_const {k m : ℕ} (P : Fin (32*(k+1)) → BitVec k)
    (u v : Fin m → Fin k) (w : Fin m → ℝ) (c : ℝ) :
    weightedLoss P u v w (fun _ _ => c) = (∑ i, w i) * (12*c) := by
  letI : Nonempty (Fin (32*(k+1))) := ⟨⟨0, by omega⟩⟩
  unfold weightedLoss
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  simp only [keyTerm, cornerSum, mean_constant, Finset.sum_const, Finset.card_univ,
    ZMod.card, nsmul_eq_mul, Nat.cast_ofNat]
  ring

end Loss

section PointFiber

open scoped BigOperators

private def coordinateAffine {n : ℕ} (i : Fin n) : AffineBit (BitVec n) :=
  (0, { toFun := fun y => y i, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl })

private theorem coordinate_affine {n : ℕ} (i : Fin n) (y : BitVec n) :
    affineBit (coordinateAffine i) y = y i := by simp [affineBit, coordinateAffine]

private theorem corner_basis {k : ℕ} (u v : Fin k) (t r s : BitField) :
    edgeAddress u v t r s = t • basisBit 0 + r • basisBit u.succ + s • basisBit v.succ := by
  funext i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [edgeAddress, basisBit, smul_eq_mul, (Fin.succ_ne_zero u).symm, (Fin.succ_ne_zero v).symm]
  · simp [edgeAddress, basisBit, smul_eq_mul]

private theorem affine_on_corners {k : ℕ} (a : AffineBit (BitVec (k+1)))
    (u v : Fin k) (t r s : BitField) :
    affineBit a (edgeAddress u v t r s) =
      linear3 a.1 (a.2 (basisBit 0)) (a.2 (basisBit u.succ)) (a.2 (basisBit v.succ)) t r s := by
  rw [corner_basis]
  simp [affineBit, linear3, smul_eq_mul]
  ring

private theorem quadratic_part_zero {k : ℕ} (a b : AffineBit (BitVec (k+1))) (u v : Fin k) :
    parity (fun t r s => affineBit a (edgeAddress u v t r s) *
      affineBit b (edgeAddress u v t r s)) = 0 := by
  simp_rw [affine_on_corners]
  exact parity_quad ..

private theorem affine_part_zero {k : ℕ} (a : AffineBit (BitVec (k+1))) (u v : Fin k) :
    parity (fun t r s => affineBit a (edgeAddress u v t r s)) = 0 := by
  simp_rw [affine_on_corners]
  exact parity_linear ..

private noncomputable def pointError {n : ℕ} (x : BitVec n → BitVec n)
    (out : BitVec n → BitField) (y : BitVec n) (h : BitField) : ℝ :=
  hit (fun z => out z ≠ dotProduct (x z) z + h) y

private theorem point_error_nonneg {n : ℕ} (x : BitVec n → BitVec n)
    (out : BitVec n → BitField) (y : BitVec n) (h : BitField) :
    0 ≤ pointError x out y h := (hit_range _ _).1

private theorem any_corner_error {k : ℕ} (x : BitVec (k+1) → BitVec (k+1))
    (out : BitVec (k+1) → BitField) (u v : Fin k) (t r s : BitField)
    (h : out (edgeAddress u v t r s) ≠ dotProduct (x (edgeAddress u v t r s))
      (edgeAddress u v t r s) + t*r*s) :
    1 ≤ cornerSum u v (pointError x out) := by
  let E := pointError x out
  have nonneg := point_error_nonneg x out
  unfold cornerSum
  calc
    1 = E (edgeAddress u v t r s) (t*r*s) :=
      (hit_eq_one (p := fun z => out z ≠ dotProduct (x z) z + t*r*s) h).symm
    _ ≤ ∑ j : BitField, E (edgeAddress u v t r j) (t*r*j) :=
      sum_lower_term (fun j : BitField => E (edgeAddress u v t r j) (t*r*j))
        (fun _ => nonneg _ _) s
    _ ≤ ∑ i : BitField, ∑ j : BitField, E (edgeAddress u v t i j) (t*i*j) :=
      sum_lower_term (fun i : BitField => ∑ j : BitField, E (edgeAddress u v t i j) (t*i*j))
        (fun _ => Finset.sum_nonneg fun _ _ => nonneg _ _) r
    _ ≤ ∑ c : BitField, ∑ i : BitField, ∑ j : BitField, E (edgeAddress u v c i j) (c*i*j) :=
      sum_lower_term (fun c : BitField => ∑ i : BitField, ∑ j : BitField,
        E (edgeAddress u v c i j) (c*i*j))
        (fun _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => nonneg _ _) t

private theorem coord_residual {n : ℕ} (x : BitVec n → BitVec n) (out p : BitVec n → BitField)
    (a : Fin n → AffineBit (BitVec n)) (c : BitVec n) (o : AffineBit (BitVec n)) (d : BitField)
    (ha : ∀ i y, x y i = affineBit (a i) y + c i * p y)
    (ho : ∀ y, out y = affineBit o y + d * p y) (y : BitVec n) :
    out y + dotProduct (x y) y = (affineBit o y + ∑ i, affineBit (a i) y * y i) +
      p y * affineBit (d, keyFunctional c) y := by
  simp only [ho, dotProduct, ha, affineBit, keyFunctional, LinearMap.coe_mk, AddHom.coe_mk, add_mul,
    Finset.sum_add_distrib, mul_add, Finset.mul_sum]
  have h : (∑ i, c i * p y * y i) = ∑ i, p y * (c i * y i) := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [h]
  ring

private theorem add_self_bit : ∀ a : BitField, a+a=0 := by decide

set_option maxHeartbeats 2000000 in
private theorem point_rounds {k m : ℕ}
    (P : Fin (32*(k+1)) → BitVec k) (u v : Fin m → Fin k) (w : Fin m → ℝ)
    (hw : ∀ i, 0 ≤ w i)
    (x : BitVec (k+1) → BitVec (k+1)) (out p : BitVec (k+1) → BitField)
    (count : ℕ) (limit : count ≤ 1) (hp : pureOK count p)
    (hx : ∀ i, (fun y => x y i) ∈ features count p) (hout : out ∈ features count p) :
    ∃ col, badWeight u v w col ≤ weightedLoss P u v w (pointError x out) := by
  classical
  have pdesc : ∃ a b : AffineBit (BitVec (k+1)), ∀ y, p y = affineBit a y * affineBit b y := by
    by_cases h : count = 0
    · refine ⟨(0,0), (0,0), ?_⟩
      simp [hp.1 h, affineBit]
    · exact hp.2 (by omega)
  obtain ⟨A,B,hab⟩ := pdesc
  choose a c hcoord using (fun i => one_feature count limit p _ (hx i))
  obtain ⟨o,d,hout'⟩ := one_feature count limit p out hout
  let C : AffineBit (BitVec (k+1)) := (d,keyFunctional c)
  let vector (i : Fin (k+1)) : Column := (A.2 (basisBit i), B.2 (basisBit i), C.2 (basisBit i))
  let col (i : Fin k) : Fin 3 := columnColour (vector 0) (vector i.succ)
  let residual (y : BitVec (k+1)) := out y + dotProduct (x y) y
  have equality (y : BitVec (k+1)) :
      residual y = (affineBit o y + ∑ i, affineBit (a i) y * y i) +
        affineBit A y * affineBit B y * affineBit C y := by
    unfold residual C
    rw [coord_residual x out p a c o d hcoord hout', hab]
  have cube (i : Fin m) : parity (fun t r s => residual (edgeAddress (u i) (v i) t r s)) =
      det3 (vector 0) (vector (u i).succ) (vector (v i).succ) := by
    have quad (j : Fin (k+1)) :
        parity (fun t r s => affineBit (a j) (edgeAddress (u i) (v i) t r s) *
          edgeAddress (u i) (v i) t r s j) = 0 := by
      simpa only [coordinate_affine] using
        quadratic_part_zero (a j) (coordinateAffine j) (u i) (v i)
    have hq : parity (fun t r s => ∑ j, affineBit (a j) (edgeAddress (u i) (v i) t r s) *
          edgeAddress (u i) (v i) t r s j) = 0 := by
      rw [parity_sum]
      exact Finset.sum_eq_zero (fun j _ => quad j)
    have hc : parity (fun t r s => affineBit A (edgeAddress (u i) (v i) t r s) *
        affineBit B (edgeAddress (u i) (v i) t r s) *
        affineBit C (edgeAddress (u i) (v i) t r s)) =
        det3 (vector 0) (vector (u i).succ) (vector (v i).succ) := by
      simp_rw [affine_on_corners]
      exact parity_cubic _ _ _ (vector 0) (vector (u i).succ) (vector (v i).succ)
    simp_rw [equality]
    rw [parity_add, parity_add, affine_part_zero, hq, hc, zero_add, zero_add]
  refine ⟨col, ?_⟩
  unfold badWeight weightedLoss
  apply Finset.sum_le_sum
  intro i _
  have hnon := point_error_nonneg x out
  split
  · rename_i mono
    have failure : ∃ t r s : BitField, out (edgeAddress (u i) (v i) t r s) ≠
      dotProduct (x (edgeAddress (u i) (v i) t r s)) (edgeAddress (u i) (v i) t r s) + t*r*s := by
      by_contra! he
      have er (t r s : BitField) :
          residual (edgeAddress (u i) (v i) t r s) = t*r*s := by
        unfold residual
        rw [he]
        calc
          _ = (dotProduct (x (edgeAddress (u i) (v i) t r s)) (edgeAddress (u i) (v i) t r s) +
              dotProduct (x (edgeAddress (u i) (v i) t r s)) (edgeAddress (u i) (v i) t r s)) + t*r*s := by ring
          _ = _ := by simp only [add_self_bit, zero_add]
      have eq := cube i
      simp_rw [er] at eq
      rw [parity_trs, colour_det_zero _ _ _ mono] at eq
      exact (by decide : (1 : BitField) ≠ 0) eq
    obtain ⟨t,r,s,err⟩ := failure
    have lo := any_corner_error x out (u i) (v i) t r s err
    calc
      w i = w i * 1 := (mul_one _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith [key_term_nonneg P (pointError x out) hnon]) (hw i)
  · exact mul_nonneg (hw i) (add_nonneg (key_term_nonneg P (pointError x out) hnon)
      (corner_nonneg (u i) (v i) (pointError x out) hnon))

end PointFiber

section FiberRepresentation

open scoped BigOperators

private def fiberWire {X Y : Type*} [AddCommGroup X] [Module BitField X]
    (M : Submodule BitField (Y → BitField)) (g : X → Y → BitField) : Prop :=
  ∃ l : X →ₗ[BitField] BitField, ∃ h ∈ M, ∀ x y, g x y = l x + h y

private theorem fiber_intercept {X Y : Type*} [AddCommGroup X] [Module BitField X]
    (M : Submodule BitField (Y → BitField)) (f : Y → BitField) (h : f ∈ M) :
    fiberWire M (fun _ : X => f) :=
  ⟨0, f, h, fun _ _ => by simp⟩

private theorem fiber_linear {X Y : Type*} [AddCommGroup X] [Module BitField X]
    (M : Submodule BitField (Y → BitField)) (l : X →ₗ[BitField] BitField) :
    fiberWire M (fun (x : X) (_ : Y) => l x) :=
  ⟨l, 0, M.zero_mem, fun _ _ => by simp⟩

private theorem fiber_weak {X Y : Type*} [AddCommGroup X] [Module BitField X]
    {M N : Submodule BitField (Y → BitField)} {g : X → Y → BitField}
    (h : M ≤ N) (hg : fiberWire M g) : fiberWire N g := by
  obtain ⟨l, b, hb, heq⟩ := hg
  exact ⟨l, b, h hb, heq⟩

private theorem fiber_scale {X Y : Type*} [AddCommGroup X] [Module BitField X]
    {M : Submodule BitField (Y → BitField)} {g : X → Y → BitField}
    (c : BitField) (hg : fiberWire M g) : fiberWire M (fun x y => c * g x y) := by
  obtain ⟨l,b,hb,hval⟩ := hg
  refine ⟨c • l, c • b, M.smul_mem c hb, ?_⟩
  intro x y
  simp [hval, smul_eq_mul, mul_add]

private theorem fiber_affine {X Y : Type*} [AddCommGroup X] [Module BitField X] {m : ℕ}
    (M : Submodule BitField (Y → BitField)) (constant : ∀ c : BitField, (fun _ : Y => c) ∈ M)
    (W : X → Y → BitVec m) (hw : ∀ i, fiberWire M (fun x y => W x y i)) (a : AffVec m) :
    fiberWire M (fun x y => runAff a (W x y)) := by
  classical
  choose l b hm he using hw
  let D : X →ₗ[BitField] BitField := ∑ i, a.2 i • l i
  let B : Y → BitField := (fun _ => a.1) + ∑ i, a.2 i • b i
  have hB : B ∈ M := M.add_mem (constant a.1) (M.sum_mem fun i _ => M.smul_mem _ (hm i))
  refine ⟨D,B,hB,?_⟩
  intro x y
  simp only [runAff, dotProduct, he, mul_add, Finset.sum_add_distrib,
    B, D, LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_apply,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

private def slicePoint {X Y : Type*} [AddCommGroup X] [Module BitField X]
    (f : X →ₗ[BitField] BitField) (v : X) (b : Y → BitField)
    (c : BitField) (z : LinearMap.ker f) (y : Y) : X :=
  (c - b y) • v + (z : X)

private theorem restrict_fiber {X Y : Type*} [AddCommGroup X] [Module BitField X]
    {M : Submodule BitField (Y → BitField)} (constant : ∀ c : BitField, (fun _ : Y => c) ∈ M)
    (f : X →ₗ[BitField] BitField) (v : X) (b : Y → BitField) (hb : b ∈ M)
    (c : BitField) {g : X → Y → BitField} (hg : fiberWire M g) :
    fiberWire M (fun z y => g (slicePoint f v b c z y) y) := by
  obtain ⟨l,u,hu,he⟩ := hg
  let newB : Y → BitField := (l v) • ((fun _ : Y => c) - b) + u
  refine ⟨l.comp (LinearMap.ker f).subtype, newB,
    M.add_mem (M.smul_mem _ (M.sub_mem (constant c) hb)) hu, ?_⟩
  intro z y
  change g (slicePoint f v b c z y) y = _
  rw [he]
  simp [slicePoint, newB, smul_eq_mul]
  ring

private theorem restrict_fixed {X Y : Type*} [AddCommGroup X] [Module BitField X]
    (f : X →ₗ[BitField] BitField) (v : X) (hv : f v = 1) (b : Y → BitField)
    (c : BitField) (z : LinearMap.ker f) (y : Y) :
    f (slicePoint f v b c z y) + b y = c :=
  split_eval f v hv (b y) c z

private def shiftedInput {X Y : Type*} [AddCommGroup X] [Module BitField X] {n : ℕ}
    (embed : X →ₗ[BitField] BitVec n) (off : Y → BitVec n) (v : X)
    (b : Y → BitField) (c : BitField) (y : Y) : BitVec n :=
  (c - b y) • embed v + off y

private theorem shifted_input_mem {X Y : Type*} [AddCommGroup X] [Module BitField X] {n : ℕ}
    {M : Submodule BitField (Y → BitField)} (constant : ∀ c : BitField, (fun _ : Y => c) ∈ M)
    (embed : X →ₗ[BitField] BitVec n) (off : Y → BitVec n)
    (hoff : ∀ i, (fun y => off y i) ∈ M) (v : X)
    (b : Y → BitField) (hb : b ∈ M) (c : BitField) (i : Fin n) :
    (fun y => shiftedInput embed off v b c y i) ∈ M := by
  have h := M.add_mem (M.smul_mem (embed v i) (M.sub_mem (constant c) hb)) (hoff i)
  convert h using 1
  funext y
  simp [shiftedInput, smul_eq_mul, mul_comm]

private theorem shifted_input_eq {X Y : Type*} [AddCommGroup X] [Module BitField X] {n : ℕ}
    (embed : X →ₗ[BitField] BitVec n) (off : Y → BitVec n)
    (f : X →ₗ[BitField] BitField) (v : X) (b : Y → BitField)
    (c : BitField) (z : LinearMap.ker f) (y : Y) :
    embed (slicePoint f v b c z y) + off y =
      (embed.comp (LinearMap.ker f).subtype) z + shiftedInput embed off v b c y := by
  simp [slicePoint, shiftedInput]
  abel

private theorem error_splits {X : Type*} [AddCommGroup X] [Module BitField X] [Fintype X]
    {n : ℕ} (inputs : X → BitVec n → BitVec n) (value : X → BitVec n → BitField)
    (f : X →ₗ[BitField] BitField) (v : X) (hv : f v = 1)
    [Fintype (LinearMap.ker f)] (b : BitVec n → BitField) (y : BitVec n) (h : BitField) :
    sliceError inputs value y h =
      (sliceError (fun z y => inputs (slicePoint f v b 0 z y) y)
          (fun z y => value (slicePoint f v b 0 z y) y) y h +
        sliceError (fun z y => inputs (slicePoint f v b 1 z y) y)
          (fun z y => value (slicePoint f v b 1 z y) y) y h) / 2 :=
  split_mean f v hv (b y) (hit fun z => value z y ≠ dotProduct (inputs z y) y + h)

end FiberRepresentation

section Rounding

open scoped BigOperators

set_option maxHeartbeats 700000 in
private theorem terminal_rounds {k m : ℕ} (P : Fin (32*(k+1)) → BitVec k)
    (good : P ∉ keyFailures k) (u v : Fin m → Fin k) (w : Fin m → ℝ)
    (hw : ∀ i, 0 ≤ w i) (huv : ∀ i, u i ≠ v i)
    (X : Type) [AddCommGroup X] [Module BitField X] [Fintype X]
    (embed : X →ₗ[BitField] BitVec (k+1)) (injective : Function.Injective embed)
    (off : BitVec (k+1) → BitVec (k+1)) (response : X → BitVec (k+1) → BitField)
    (e count : ℕ) (p : BitVec (k+1) → BitField)
    (budget : e + count ≤ k+2) (cardinal : Fintype.card X * 2^e = 2^(k+1))
    (hp : pureOK count p) (hoff : ∀ i, (fun y => off y i) ∈ features count p)
    (hr : fiberWire (features count p) response) :
    ∃ col, badWeight u v w col ≤ weightedLoss P u v w
      (sliceError (fun z y => embed z + off y) response) := by
  classical
  obtain ⟨l,b,hb,he⟩ := hr
  by_cases hasShift : ∃ δ : X, δ ≠ 0
  · obtain ⟨δ,hδ⟩ := hasShift
    have bitDirection : embed δ ≠ 0 := by
      intro heq
      apply hδ
      apply injective
      rw [heq, map_zero]
    apply shift_rounds P good u v w hw huv _ _ δ (embed δ) bitDirection (l δ)
    · intro z y
      rw [map_add]
      abel
    · intro z y
      rw [he, he, map_add]
      abel
  · have onlyZero (z : X) : z = 0 := by
      by_contra hz
      exact hasShift ⟨z,hz⟩
    letI : Unique X := ⟨⟨0⟩, onlyZero⟩
    have unitCard : Fintype.card X = 1 := Fintype.card_unique
    have used : e = k+1 := by
      apply pow_right_injective₀ (by decide : (0 : ℕ) < 2) (by decide)
      simpa only [unitCard, one_mul] using cardinal
    have rest : count ≤ 1 := by omega
    have errors : sliceError (fun z y => embed z + off y) response = pointError off b := by
      funext y h
      have pointwise : (fun z : X => response z y ≠ dotProduct (embed z + off y) y + h) =
          fun _ : X => b y ≠ dotProduct (off y) y + h := by
        funext z
        simp [onlyZero z, he]
      unfold sliceError
      rw [pointwise]
      change mean (fun _ : X => pointError off b y h) = pointError off b y h
      exact mean_constant _
    rw [errors]
    exact point_rounds P u v w hw off b p count rest hp hoff hb

set_option maxHeartbeats 3000000 in
private theorem trace_rounds {k m : ℕ} (P : Fin (32*(k+1)) → BitVec k)
    (good : P ∉ keyFailures k) (u v : Fin m → Fin k) (w : Fin m → ℝ)
    (hw : ∀ i, 0 ≤ w i) (huv : ∀ i, u i ≠ v i) (r : ℕ) :
    ∀ (width : ℕ) (prog : slotProgram width r)
      (X : Type) [AddCommGroup X] [Module BitField X] [Fintype X]
      (embed : X →ₗ[BitField] BitVec (k+1)), Function.Injective embed →
      ∀ (off : BitVec (k+1) → BitVec (k+1)) (W : X → BitVec (k+1) → BitVec width)
        (e count : ℕ) (p : BitVec (k+1) → BitField),
        e + count + r ≤ k+2 → Fintype.card X * 2^e = 2^(k+1) →
        pureOK count p → (∀ i, (fun y => off y i) ∈ features count p) →
        (∀ j, fiberWire (features count p) (fun z y => W z y j)) →
        ∃ col, badWeight u v w col ≤ weightedLoss P u v w
          (sliceError (fun z y => embed z + off y) (fun z y => runProgram width r prog (W z y))) := by
  classical
  induction r with
  | zero =>
    intro width prog X _ _ _ embed injective off W e count p bound card hp hoff hW
    apply terminal_rounds P good u v w hw huv X embed injective off _ e count p (by omega)
      card hp hoff
    exact fiber_affine _ (features_const count p) W hW prog
  | succ r ih =>
    intro width prog X _ _ _ embed injective off W e count p bound card hp hoff hW
    change AffVec width × AffVec width × slotProgram (width+1) r at prog
    obtain ⟨a,b,rest⟩ := prog
    let M : Submodule BitField (BitVec (k+1) → BitField) := features count p
    let A (z : X) (y : BitVec (k+1)) := runAff a (W z y)
    let B (z : X) (y : BitVec (k+1)) := runAff b (W z y)
    let response (z : X) (y : BitVec (k+1)) :=
      runProgram (width+1) r rest (Fin.snoc (W z y) (A z y * B z y))
    change ∃ col, badWeight u v w col ≤ weightedLoss P u v w
      (sliceError (fun z y => embed z + off y) response)
    have hAf : fiberWire M A := fiber_affine M (features_const count p) W hW a
    have hBf : fiberWire M B := fiber_affine M (features_const count p) W hW b
    obtain ⟨fa,ba,hba,ha⟩ := hAf
    obtain ⟨fb,bb,hbb,hb⟩ := hBf
    by_cases both : fa = 0 ∧ fb = 0
    · obtain ⟨q,hq,more,mem⟩ := add_pure_feature count p ba bb hp hba hbb
      let W' (z : X) (y : BitVec (k+1)) : BitVec (width+1) := Fin.snoc (W z y) (ba y * bb y)
      have hW' (i : Fin (width+1)) :
          fiberWire (features (count+1) q) (fun z y => W' z y i) := by
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simpa only [W', Fin.snoc_last] using
            (fiber_intercept (X := X) _ (fun y => ba y * bb y) mem)
        · simpa only [W', Fin.snoc_castSucc] using fiber_weak more (hW j)
      have eq : response = fun z y => runProgram (width+1) r rest (W' z y) := by
        funext z y
        simp [response, W', ha z y, hb z y, both.1, both.2]
      rw [eq]
      exact ih (width+1) rest X embed injective off W' e (count+1) q
        (by omega) card hq (fun i => more (hoff i)) hW'
    · have choice :
          ∃ f : X →ₗ[BitField] BitField, ∃ offset ∈ M,
            ∃ other : X → BitVec (k+1) → BitField, f ≠ 0 ∧ fiberWire M other ∧
              ∀ z y, A z y * B z y = (f z + offset y) * other z y := by
        by_cases h : fa = 0
        · refine ⟨fb,bb,hbb,A,fun hf => both ⟨h,hf⟩,⟨fa,ba,hba,ha⟩,?_⟩
          intro z y
          rw [hb, mul_comm]
        · exact ⟨fa,ba,hba,B,h,⟨fb,bb,hbb,hb⟩,fun z y => by rw [ha]⟩
      obtain ⟨f,offset,hOffset,other,hf,hother,product⟩ := choice
      obtain ⟨δ,hδ⟩ := maps_one f hf
      letI : Fintype (LinearMap.ker f) := Fintype.ofFinite _
      let embed' : LinearMap.ker f →ₗ[BitField] BitVec (k+1) :=
        embed.comp (LinearMap.ker f).subtype
      have hinj : Function.Injective embed' := fun x y h => Subtype.ext (injective h)
      let off' := shiftedInput embed off δ offset
      let W' (c : BitField) (z : LinearMap.ker f) (y : BitVec (k+1)) : BitVec (width+1) :=
        Fin.snoc (W (slicePoint f δ offset c z y) y) (c * other (slicePoint f δ offset c z y) y)
      have card' : Fintype.card (LinearMap.ker f) * 2^(e+1) = 2^(k+1) := by
        calc
          _ = Fintype.card X * 2^e := by rw [split_card f δ hδ, pow_succ]; ring
          _ = _ := card
      have invariants (c : BitField) (j : Fin (width+1)) :
          fiberWire M (fun z y => W' c z y j) := by
        refine Fin.lastCases ?_ (fun i => ?_) j
        · simp only [W', Fin.snoc_last]
          exact fiber_scale c (restrict_fiber (features_const count p) f δ offset hOffset c hother)
        · simp only [W', Fin.snoc_castSucc]
          exact restrict_fiber (features_const count p) f δ offset hOffset c (hW i)
      let E (c : BitField) := sliceError (fun z y => embed' z + off' c y)
        (fun z y => runProgram (width+1) r rest (W' c z y))
      let loss (c : BitField) := weightedLoss P u v w (E c)
      have branch (c : BitField) : ∃ col, badWeight u v w col ≤ loss c :=
        ih (width+1) rest (LinearMap.ker f) embed' hinj (off' c) (W' c) (e+1) count p
          (by omega) card' hp (shifted_input_mem (features_const count p) embed off hoff δ offset hOffset c)
          (invariants c)
      have eval' (c : BitField) (z : LinearMap.ker f) (y : BitVec (k+1)) :
          response (slicePoint f δ offset c z y) y = runProgram (width+1) r rest (W' c z y) := by
        unfold response W'
        rw [product, restrict_fixed f δ hδ]
      have avgEq : sliceError (fun z y => embed z + off y) response =
          fun y h => (1/2 : ℝ) * (E 0 y h + E 1 y h) := by
        funext y h
        rw [error_splits _ _ f δ hδ offset]
        simp only [shifted_input_eq, eval', E, off', embed']
        ring
      have avgLoss : weightedLoss P u v w (sliceError (fun z y => embed z + off y) response) =
          (loss 0 + loss 1) / 2 := by
        rw [avgEq, loss_scale, loss_add]
        unfold loss
        ring
      obtain ⟨c0,h0⟩ := branch 0
      obtain ⟨c1,h1⟩ := branch 1
      rw [avgLoss]
      rcases le_total (loss 0) (loss 1) with hh | hh
      · exact ⟨c0, h0.trans (by linarith)⟩
      · exact ⟨c1, h1.trans (by linarith)⟩

private theorem normal_program_rounds {k m : ℕ} (P : Fin (32*(k+1)) → BitVec k)
    (good : P ∉ keyFailures k) (u v : Fin m → Fin k) (w : Fin m → ℝ)
    (hw : ∀ i, 0 ≤ w i) (huv : ∀ i, u i ≠ v i)
    (prog : slotProgram ((k+1)+(k+1)) (k+2)) :
    ∃ col, badWeight u v w col ≤ weightedLoss P u v w
      (sliceError (fun x _ => x)
        (fun x y => runProgram ((k+1)+(k+1)) (k+2) prog (Fin.append x y))) := by
  let Y := BitVec (k+1)
  let M := features 0 (0 : Y → BitField)
  have hW (i : Fin ((k+1)+(k+1))) :
      fiberWire M (fun (x y : Y) => Fin.append x y i) := by
    refine Fin.addCases ?_ ?_ i
    · intro j
      simpa only [Fin.append_left, coordinateAffine, LinearMap.coe_mk, AddHom.coe_mk] using
        fiber_linear (Y := Y) M (coordinateAffine j).2
    · intro j
      simpa only [Fin.append_right] using
        (fiber_intercept (X := Y) M (fun y => y j)
          (features_linear 0 (0 : Y → BitField) (coordinateAffine j).2))
  have hr := trace_rounds P good u v w hw huv (k+2) _ prog Y LinearMap.id
    (fun _ _ h => h) (fun _ => 0) (fun x y => Fin.append x y)
    0 0 0 (by omega) (by simp [Y, vec_card]) ⟨fun _ => rfl, by omega⟩
    (fun _ => features_const 0 (0 : Y → BitField) 0) hW
  simpa only [LinearMap.id_apply, add_zero] using hr

end Rounding

section PanelStatement

open scoped BigOperators
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

private abbrev sampleSize (n d : ℕ) := 2048*n^2*d^2

private def fieldLegal (n : ℕ) (C : Circuit) : Prop :=
  ReadsBack (2*n) C ∧ (∀ g ∈ C.gates, gateAllowed g) ∧ C.gates.countP isPaid ≤ n+1

private noncomputable def sampleError {n d : ℕ}
    (P : Fin (sampleSize n d) → BitVec n) (C : Circuit)
    (y : BitVec n) (h : BitField) : ℝ :=
  mean fun j => hit (fun x => toScalar (C.eval (encodedBits x ++ encodedBits y)) ≠
    dotProduct x y + h) (P j)

private theorem sampleSize_pos {n d : ℕ} (hn : 0 < n) (hd : 0 < d) : 0 < sampleSize n d := by
  unfold sampleSize
  positivity

private theorem scalar_eq_bool_eq : ∀ (b : Bool) (a : BitField),
    toScalar b = a ↔ b = toBoolean a := by decide

private theorem target_shift_ne : ∀ a b : BitField, a ≠ a+b ↔ b ≠ 0 := by decide

private theorem oneCorner :
    (∑ t : BitField, ∑ r : BitField, ∑ s : BitField,
      hit (fun b : BitField => b ≠ 0) (t*r*s)) = 1 := by
  have sumBits (f : BitField → ℝ) : (∑ a, f a) = f 0 + f 1 := by
    rw [univK, Finset.sum_pair (by decide : (0 : BitField) ≠ 1)]
  have h0 : ¬ ((0 : BitField) ≠ 0) := fun h => h rfl
  have h1 : (1 : BitField) ≠ 0 := by decide
  simp only [sumBits, zero_mul, mul_zero, one_mul, mul_one,
    hit_eq_zero (p := fun b : BitField => b ≠ 0) h0,
    hit_eq_one (p := fun b : BitField => b ≠ 0) h1, zero_add, add_zero]

set_option maxHeartbeats 900000 in
private theorem colour_compiled_loss {k d m : ℕ} (hd : 0 < d)
    (P : Fin (32 * (k+1)) → BitVec k) (Q : Fin (sampleSize (k+1) d) → BitVec (k+1))
    (u v : Fin m → Fin k) (w : Fin m → ℝ) (col : Fin k → Fin 3) :
    ∃ C : Circuit, fieldLegal (k+1) C ∧ weightedLoss P u v w (sampleError Q C) = badWeight u v w col := by
  obtain ⟨C,hback,hg,hbudget,ev⟩ := color_circuit k col
  letI : Nonempty (Fin (sampleSize (k+1) d)) := ⟨⟨0,sampleSize_pos (by omega) hd⟩⟩
  let E := sampleError Q C
  have key_zero (s : BitVec k) : E (Fin.cons 0 s) 0 = 0 := by
    unfold E sampleError
    simp_rw [ev, color_answer_key]
    simp [hit, mean]
  have key0 : keyTerm P E = 0 := by unfold keyTerm; simp [key_zero, mean]
  have mon (i : Fin m) (h : col (u i) = col (v i)) (t r s : BitField) :
      E (edgeAddress (u i) (v i) t r s) (t*r*s) =
        hit (fun b : BitField => b ≠ 0) (t*r*s) := by
    unfold E sampleError
    simp_rw [ev, edgeAddress, color_answer_corner, h, if_true, add_zero, target_shift_ne]
    exact mean_constant _
  have dis (i : Fin m) (h : col (u i) ≠ col (v i)) (t r s : BitField) :
      E (edgeAddress (u i) (v i) t r s) (t*r*s) = 0 := by
    unfold E sampleError
    simp_rw [ev, edgeAddress, color_answer_corner, if_neg h]
    simp [hit, mean]
  refine ⟨C, ⟨hback,hg,hbudget⟩, ?_⟩
  change weightedLoss P u v w E = _
  unfold weightedLoss badWeight
  apply Finset.sum_congr rfl
  intro i _
  rw [key0, zero_add]
  by_cases h : col (u i) = col (v i)
  · rw [if_pos h]
    have hc : cornerSum (u i) (v i) E = 1 := by
      unfold cornerSum
      simp_rw [mon i h]
      exact oneCorner
    rw [hc, mul_one]
  · rw [if_neg h]
    have hc : cornerSum (u i) (v i) E = 0 := by
      unfold cornerSum
      simp [dis i h]
    rw [hc, mul_zero]

set_option maxHeartbeats 1000000 in
private theorem sampled_rounds {k d m : ℕ} (hd : 0 < d)
    (P : Fin (32 * (k+1)) → BitVec k) (Q : Fin (sampleSize (k+1) d) → BitVec (k+1))
    (hp : P ∉ keyFailures k) (hq : Q ∉ errorFailures (k+1) d)
    (u v : Fin m → Fin k) (w : Fin m → ℝ) (hne : ∀ i, u i ≠ v i) (hw : ∀ i, 0 ≤ w i)
    (C : Circuit) (hC : fieldLegal (k+1) C) :
    ∃ col, badWeight u v w col ≤ weightedLoss P u v w (sampleError Q C) + (∑ i, w i) / d := by
  obtain ⟨prog,hprog⟩ := circuit_normal_form (k+1) C hC.2.1 hC.2.2
  let f := fun (x y : BitVec (k+1)) =>
    runProgram ((k+1)+(k+1)) (k+2) prog (Fin.append x y)
  let trueError := sliceError (fun x _ => x) f
  have point (y : BitVec (k+1)) (h : BitField) :
      trueError y h ≤ sampleError Q C y h + 1 / (12 * d) := by
    have he := error_good Q hq (prog,y,h)
    have sample : sampleError Q C y h = mean (fun j => errorProbe (k+1) (prog,y,h) (Q j)) := by
      unfold sampleError errorProbe
      simp_rw [hprog]
    rw [sample]
    exact he
  obtain ⟨col, hcol⟩ := normal_program_rounds P hp u v w hw hne prog
  refine ⟨col, hcol.trans ?_⟩
  calc
    weightedLoss P u v w trueError ≤
        weightedLoss P u v w (fun y h => sampleError Q C y h + 1 / (12 * d)) :=
      loss_mono P u v w hw _ _ point
    _ = _ := by
      rw [loss_add, loss_const]
      have d0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
      have e : (12 : ℝ) * (1 / (12 * (d : ℝ))) = 1 / d := by
        field_simp [d0]
      rw [e]
      ring

private abbrev PanelType (k d : ℕ) :=
  (Fin (32*(k+1)) → BitVec k) × (Fin (sampleSize (k+1) d) → BitVec (k+1))

private def qualifies (k d : ℕ) (panel : PanelType k d) : Prop :=
  ∀ (m : ℕ) (u v : Fin m → Fin k) (w : Fin m → ℝ),
    (∀ i, u i ≠ v i) → (∀ i, 0 ≤ w i) → ∀ q : ℝ,
    ((∃ col, badWeight u v w col ≤ q) → ∃ C : Circuit, fieldLegal (k+1) C ∧
       weightedLoss panel.1 u v w (sampleError panel.2 C) ≤ q) ∧
    ((∃ C : Circuit, fieldLegal (k+1) C ∧ weightedLoss panel.1 u v w (sampleError panel.2 C) ≤ q) →
      ∃ col, badWeight u v w col ≤ q + (∑ i, w i) / d)

private theorem panel_qualifies (k d : ℕ) (hd : 0 < d) (panel : PanelType k d)
    (hp : panel.1 ∉ keyFailures k) (hq : panel.2 ∉ errorFailures (k+1) d) :
    qualifies k d panel := by
  intro m u v w neq weights q
  constructor
  · rintro ⟨c,hc⟩
    obtain ⟨C,hC,hL⟩ := colour_compiled_loss hd panel.1 panel.2 u v w c
    exact ⟨C,hC,hL.le.trans hc⟩
  · rintro ⟨C,hC,hL⟩
    obtain ⟨c,hc⟩ := sampled_rounds hd panel.1 panel.2 hp hq u v w neq weights C hC
    exact ⟨c,hc.trans (add_le_add hL le_rfl)⟩

private theorem zero_qualifies (d : ℕ) (hd : 0 < d) (panel : PanelType 0 d) :
    qualifies 0 d panel := by
  intro m u v w neq weights q
  have hm : m = 0 := by
    by_contra h
    exact Fin.elim0 (u ⟨0,Nat.pos_of_ne_zero h⟩)
  subst m
  constructor
  · rintro ⟨c,hc⟩
    obtain ⟨C,hC,hL⟩ := colour_compiled_loss hd panel.1 panel.2 u v w c
    exact ⟨C,hC,hL.le.trans hc⟩
  · rintro ⟨C,hC,hL⟩
    refine ⟨fun i => Fin.elim0 i, ?_⟩
    simpa [badWeight, weightedLoss] using hL

private noncomputable def listedError {n d : ℕ}
    (Q : Fin (sampleSize n d) → BitVec n) (C : Circuit) (y : BitVec n) (h : BitField) : ℝ :=
  (∑ j, if C.eval (encodedBits (Q j) ++ encodedBits y) = toBoolean (dotProduct (Q j) y+h)
    then (0 : ℝ) else 1) / sampleSize n d

private theorem sample_error_formula {n d : ℕ}
    (Q : Fin (sampleSize n d) → BitVec n) (C : Circuit) (y : BitVec n) (h : BitField) :
    sampleError Q C y h = listedError Q C y h := by
  unfold sampleError mean listedError
  simp only [Fintype.card_fin]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  by_cases he : toScalar (C.eval (encodedBits (Q j) ++ encodedBits y)) = dotProduct (Q j) y+h
  · have hb := (scalar_eq_bool_eq _ _).mp he
    exact (hit_eq_zero (p := fun x => toScalar (C.eval (encodedBits x ++ encodedBits y)) ≠
      dotProduct x y + h) (a := Q j) (fun hn => hn he)).trans (if_pos hb).symm
  · have hb : C.eval (encodedBits (Q j) ++ encodedBits y) ≠ toBoolean (dotProduct (Q j) y+h) :=
      fun hb => he ((scalar_eq_bool_eq _ _).mpr hb)
    exact (hit_eq_one (p := fun x => toScalar (C.eval (encodedBits x ++ encodedBits y)) ≠
      dotProduct x y + h) (a := Q j) he).trans (if_neg hb).symm

private noncomputable def listedLoss {k d m : ℕ} (p : PanelType k d)
    (u v : Fin m → Fin k) (w : Fin m → ℝ) (C : Circuit) : ℝ :=
  ∑ i, w i * (4 * (∑ j, listedError p.2 C (Fin.cons 0 (p.1 j)) 0) / (32 * (k+1) : ℕ) +
    ∑ t : BitField, ∑ r : BitField, ∑ s : BitField,
      listedError p.2 C (Fin.cons t (r • basisBit (u i) + s • basisBit (v i))) (t*r*s))

private theorem listedLoss_eq {k d m : ℕ} (p : PanelType k d)
    (u v : Fin m → Fin k) (w : Fin m → ℝ) (C : Circuit) :
    listedLoss p u v w C = weightedLoss p.1 u v w (sampleError p.2 C) := by
  simp only [listedLoss, weightedLoss, keyTerm, cornerSum, mean, Fintype.card_fin,
    sample_error_formula, edgeAddress, mul_div_assoc]

private def listedQualifies (k d : ℕ) (p : PanelType k d) : Prop :=
  ∀ (m : ℕ) (u v : Fin m → Fin k) (w : Fin m → ℝ),
    (∀ i, u i ≠ v i) → (∀ i, 0 ≤ w i) → ∀ q : ℝ,
    ((∃ col, badWeight u v w col ≤ q) →
      ∃ C : Circuit, fieldLegal (k+1) C ∧ listedLoss p u v w C ≤ q) ∧
    ((∃ C : Circuit, fieldLegal (k+1) C ∧ listedLoss p u v w C ≤ q) →
      ∃ col, badWeight u v w col ≤ q + (∑ i, w i) / d)

private theorem listedQualifies_eq (k d : ℕ) (p : PanelType k d) :
    listedQualifies k d p = qualifies k d p := by
  simp only [listedQualifies, qualifies, listedLoss_eq]

private noncomputable def acceptedPanels (k d : ℕ) : Finset (PanelType k d) :=
  Finset.univ.filter fun p => @decide (listedQualifies k d p) (Classical.propDecidable _)

private theorem listed_good_panel_card (k d : ℕ) (hd : 0 < d) :
    3 * Fintype.card (PanelType k d) ≤ 4 * (acceptedPanels k d).card := by
  classical
  cases k with
  | zero =>
    have all : acceptedPanels 0 d = Finset.univ := by
      ext p
      have good := (listedQualifies_eq 0 d p).mpr (zero_qualifies d hd p)
      simp [acceptedPanels, good]
    rw [all, Finset.card_univ]
    omega
  | succ k =>
    let BadA := keyFailures (k+1)
    let BadB := errorFailures (k+2) d
    apply panels_card_good BadA BadB (key_failures_bound _) (error_failures_bound _ _ (by omega) hd)
    intro p q hp hq
    have good := (listedQualifies_eq (k+1) d (p,q)).mpr (panel_qualifies (k+1) d hd (p,q) hp hq)
    simp [acceptedPanels, good]

end PanelStatement

end PEqualNP.Outside.L_meta_33650

open scoped BigOperators

set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.L_meta_33650 : (
∀ (k d : ℕ), 0 < d →
  let n := k+1
  let F := ZMod 2
  let S := Fin k → F
  let V := Fin (k+1) → F
  let e := fun (i j : Fin k) => if j = i then (1 : F) else 0
  let bits := fun (x : V) => List.ofFn (fun i => decide (x i = 1))
  let Circ := PEqualNP.CircuitLowerBounds.Circuit
  let legal := fun (C : Circ) =>
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (2*n) C ∧
    (∀ g ∈ C.gates, g.inputs.length ≤ 2 ∧
      (g.op = .and ∨ g.op = .or ∨ g.op = .mod 2 ∨ (g.op = .not ∧ g.inputs.length = 1))) ∧
    C.gates.countP (fun g => @decide
      ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) (Classical.propDecidable _)) ≤ n+1
  let a := 32*n
  let b := 2048*n^2*d^2
  let panels := (Fin a → S) × (Fin b → V)
  let good := fun (P : panels) =>
    let err := fun (C : Circ) (y : V) (h : F) =>
      (∑ j, if C.eval (bits (P.2 j) ++ bits y) = decide (dotProduct (P.2 j) y+h = 1)
        then (0 : ℝ) else 1) / b
    ∀ (m : ℕ) (u v : Fin m → Fin k) (w : Fin m → ℝ), (∀ i, u i ≠ v i) → (∀ i, 0 ≤ w i) →
      let loss := fun (C : Circ) =>
        ∑ i, w i * (4*(∑ j, err C (Fin.cons 0 (P.1 j)) 0) / a +
          ∑ t : F, ∑ r : F, ∑ s : F, err C (Fin.cons t (r • e (u i) + s • e (v i))) (t*r*s))
      let bad := fun (col : Fin k → Fin 3) =>
        ∑ i, if col (u i) = col (v i) then w i else 0
      ∀ q : ℝ,
        ((∃ col, bad col ≤ q) → ∃ C : Circ, legal C ∧ loss C ≤ q) ∧
        ((∃ C : Circ, legal C ∧ loss C ≤ q) → ∃ col, bad col ≤ q + (∑ i, w i) / d)
  let accepted := (Finset.univ : Finset panels).filter
    (fun P => @decide (good P) (Classical.propDecidable _))
  3*Fintype.card panels ≤ 4*accepted.card
) := by
  intro k d hd
  exact PEqualNP.Outside.L_meta_33650.listed_good_panel_card k d hd
