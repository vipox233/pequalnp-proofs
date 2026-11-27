import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Ring.Finset
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_580.Arithmetic

def pack {n : ℕ} (B : ℕ) (v : Fin n → ℕ) : ℕ := ∑ i, v i * B ^ i.val

theorem pack_succ {n B : ℕ} (v : Fin (n + 1) → ℕ) :
    pack B v = v 0 + B * pack B (fun i => v i.succ) := by
  unfold pack
  rw [Fin.sum_univ_succ, Finset.mul_sum]
  simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem pack_lt {n B : ℕ} (_hB : 0 < B) (v : Fin n → ℕ) (hv : ∀ i, v i < B) :
    pack B v < B ^ n := by
  induction n with
  | zero => simp [pack]
  | succ n ih =>
    rw [pack_succ, pow_succ]
    have ht := ih (fun i => v i.succ) (fun i => hv i.succ)
    have hm := Nat.mul_le_mul_left B (show pack B (fun i => v i.succ) + 1 ≤ B^n from ht)
    have h0 := hv 0
    nlinarith

theorem pack_unique {n B : ℕ} (hB : 0 < B) (v w : Fin n → ℕ)
    (hv : ∀ i, v i < B) (hw : ∀ i, w i < B) (he : pack B v = pack B w) : v = w := by
  induction n with
  | zero => funext i; exact Fin.elim0 i
  | succ n ih =>
    rw [pack_succ, pack_succ] at he
    have h0 := congrArg (fun a => a % B) he
    simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hv 0), Nat.mod_eq_of_lt (hw 0)] at h0
    have htail : pack B (fun i => v i.succ) = pack B (fun i => w i.succ) := by
      rw [h0] at he
      exact Nat.eq_of_mul_eq_mul_left hB (Nat.add_left_cancel he)
    have ht := ih (fun i => v i.succ) (fun i => w i.succ) (fun i => hv i.succ) (fun i => hw i.succ) htail
    funext i
    exact Fin.cases h0 (fun j => congrFun ht j) i

theorem pack_add {n B : ℕ} (v w : Fin n → ℕ) :
    pack B (fun i => v i + w i) = pack B v + pack B w := by
  simp [pack, add_mul, Finset.sum_add_distrib]

def bitDigit {t b : ℕ} (raw : Fin (t*b) → Bool) (i : Fin t) : ℕ :=
  ∑ j : Fin b, if (List.ofFn raw).getD (i.val*b+j.val) false then 2^j.val else 0

theorem digit_pack {t b : ℕ} (raw : Fin (t*b) → Bool) (i : Fin t) :
    bitDigit raw i = pack 2 (fun j : Fin b => ((List.ofFn raw).getD (i.val*b+j.val) false).toNat) := by
  unfold bitDigit pack
  apply Finset.sum_congr rfl
  intro j _
  have bitValue (q : Bool) (p : ℕ) : (if q then p else 0) = q.toNat*p := by
    cases q <;> simp
  exact bitValue _ _

theorem digit_lt {t b : ℕ} (raw : Fin (t*b) → Bool) (i : Fin t) :
    bitDigit raw i < 2 ^ b := by
  rw [digit_pack]
  apply pack_lt (by decide)
  intro j
  cases (List.ofFn raw).getD (i.val*b+j.val) false <;> decide

theorem digit_unique {t b : ℕ} (hb : 0 < b) (x y : Fin (t*b) → Bool)
    (hd : bitDigit x = bitDigit y) : x = y := by
  funext k
  let i : Fin t := ⟨k.val / b, (Nat.div_lt_iff_lt_mul hb).2 k.isLt⟩
  let j : Fin b := ⟨k.val % b, Nat.mod_lt _ hb⟩
  have he := congrFun hd i
  rw [digit_pack, digit_pack] at he
  have digits := pack_unique (by decide) _ _ (fun p => by cases (List.ofFn x).getD (i.val*b+p.val) false <;> decide)
    (fun p => by cases (List.ofFn y).getD (i.val*b+p.val) false <;> decide) he
  have eq := congrFun digits j
  have hk : i.val*b+j.val = k.val := Nat.div_add_mod' _ _
  have bool_inj (a b : Bool) : a.toNat = b.toNat → a = b := by
    cases a <;> cases b <;> decide
  apply bool_inj
  simpa [hk, k.isLt] using eq

theorem square_midpoint {a b c : ℕ} (h : a+c=2*b) :
    2*b^2 ≤ a^2+c^2 ∧ (2*b^2 = a^2+c^2 → a=b ∧ b=c) := by
  have hz : (a:ℤ) + c = 2*(b:ℤ) := by exact_mod_cast h
  have hsq := congrArg (fun z : ℤ => z^2) hz
  change ((a:ℤ) + c)^2 = (2*(b:ℤ))^2 at hsq
  constructor
  · exact_mod_cast (show 2*(b:ℤ)^2 ≤ (a:ℤ)^2 + (c:ℤ)^2 by
      nlinarith [sq_nonneg ((a:ℤ) - c)])
  · intro he
    have he' : 2*(b:ℤ)^2 = (a:ℤ)^2 + (c:ℤ)^2 := by exact_mod_cast he
    have hd : ((a:ℤ) - c)^2 = 0 := by nlinarith
    have hac : (a:ℤ) = c := sub_eq_zero.mp (sq_eq_zero_iff.mp hd)
    omega

def enc {t : ℕ} (b : ℕ) (v : Fin t → ℕ) : ℕ :=
  pack (2^(b+1)) v + (2^(b+1))^t * ∑ i, (v i)^2

theorem pack_pair_lt {t b : ℕ} (v w : Fin t → ℕ)
    (hv : ∀ i, v i < 2^b) (hw : ∀ i, w i < 2^b) :
    pack (2^(b+1)) v + pack (2^(b+1)) w < (2^(b+1))^t := by
  rw [← pack_add]
  apply pack_lt (by positivity)
  intro i
  rw [pow_succ]
  have := hv i
  have := hw i
  omega

theorem enc_bound {t b : ℕ} (ht : 0 < t) (v : Fin t → ℕ) (hv : ∀ i, v i < 2^b) :
    2 * enc b v < 2^(t*(b+1)+2*b+Nat.clog 2 t+1) := by
  have square_lt (i : Fin t) : (v i)^2 < (2^b)^2 := by
    simpa only [pow_two] using Nat.mul_self_lt_mul_self (hv i)
  have hsum : (∑ i, (v i)^2) < t*(2^b)^2 := by
    have hn := Finset.sum_lt_sum (s := (Finset.univ : Finset (Fin t)))
      (f := fun i => (v i)^2) (g := fun _ => (2^b)^2)
      (fun i _ => (square_lt i).le) ⟨⟨0, ht⟩, Finset.mem_univ _, square_lt _⟩
    simpa using hn
  have hnorm : (∑ i, (v i)^2) < 2^(2*b+Nat.clog 2 t) := by
    refine hsum.trans_le ((Nat.mul_le_mul_right ((2^b)^2) (Nat.le_pow_clog (by decide : 1 < 2) t)).trans_eq ?_)
    rw [← pow_mul, ← pow_add]
    congr 1
    omega
  have hp := pack_pair_lt v v hv hv
  have hs := Nat.mul_le_mul_left ((2^(b+1))^t)
    (show 2 * (∑ i, (v i)^2) + 1 ≤ 2 ^ (2*b+Nat.clog 2 t) * 2 by omega)
  have he : 2^(t*(b+1)+2*b+Nat.clog 2 t+1) =
      (2^(b+1))^t * (2^(2*b+Nat.clog 2 t)*2) := by
    rw [← pow_mul, ← pow_succ, ← pow_add]
    congr 1
    rw [Nat.mul_comm (b+1)]
    omega
  rw [he]
  unfold enc
  nlinarith

theorem split_unique {P a c u w : ℕ} (hP : 0 < P) (ha : a < P) (hc : c < P)
    (he : a+P*u = c+P*w) : a=c ∧ u=w := by
  have hr := congrArg (fun n => n % P) he
  simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hc] at hr
  refine ⟨hr, ?_⟩
  rw [hr] at he
  exact Nat.eq_of_mul_eq_mul_left hP (Nat.add_left_cancel he)

theorem enc_ap {t b : ℕ} (v w u : Fin t → ℕ)
    (hv : ∀ i, v i < 2^b) (hw : ∀ i, w i < 2^b) (hu : ∀ i, u i < 2^b)
    (he : enc b v + enc b u = 2*enc b w) : v=w ∧ w=u := by
  let B := 2^(b+1)
  let P := B^t
  have hsplit : pack B v + pack B u + P*((∑ i, (v i)^2) + ∑ i, (u i)^2) =
      pack B w + pack B w + P*(2*∑ i, (w i)^2) := by
    dsimp [P,B]
    unfold enc at he
    linarith only [he]
  obtain ⟨hl,hh⟩ := split_unique (by positivity)
    (pack_pair_lt v u hv hu) (pack_pair_lt w w hw hw) hsplit
  rw [← pack_add, ← pack_add] at hl
  have below (a c : ℕ) (ha : a < 2^b) (hc : c < 2^b) : a+c < B := by
    dsimp [B]
    rw [pow_succ]
    omega
  have hd := pack_unique (show 0 < B by dsimp [B]; positivity) _ _
    (fun i => below _ _ (hv i) (hu i)) (fun i => below _ _ (hw i) (hw i)) hl
  have hm (i) : v i + u i = 2*w i := by
    simpa [two_mul] using congrFun hd i
  have hsum : (∑ i, 2*(w i)^2) = ∑ i, ((v i)^2+(u i)^2) := by
    rw [← Finset.mul_sum, Finset.sum_add_distrib]
    exact hh.symm
  have issquare (i : Fin t) : 2*(w i)^2 = (v i)^2 + (u i)^2 := by
    by_contra hn
    have := Finset.sum_lt_sum (s := (Finset.univ : Finset (Fin t)))
      (f := fun j => 2*(w j)^2) (g := fun j => (v j)^2+(u j)^2)
      (fun j _ => (square_midpoint (hm j)).1)
      ⟨i, Finset.mem_univ _, lt_of_le_of_ne (square_midpoint (hm i)).1 hn⟩
    omega
  have same (i) := (square_midpoint (hm i)).2 (issquare i)
  exact ⟨funext (fun i => (same i).1), funext (fun i => (same i).2)⟩

theorem arithmetic (t b : ℕ) (ht : 0<t) (hb : 0<b) :
    let m := t*b
    let X := Fin m → Bool
    let low := t*(b+1)
    let h := low+2*b+Nat.clog 2 t+1
    let digit := fun (raw : X) (i : Fin t) => ∑ j : Fin b,
      if (List.ofFn raw).getD (i.val*b+j.val) false then 2^j.val else 0
    let lift := fun payload : X =>
      (∑ i : Fin t, digit payload i * 2^((b+1)*i.val)) + 2^low * ∑ i : Fin t, (digit payload i)^2
    (∀ x : X, 2*lift x < 2^h) ∧ Function.Injective lift ∧
    (∀ x y z : X, lift x + lift z = 2*lift y → x=y ∧ y=z) := by
  let E := fun (x : Fin (t*b) → Bool) => enc b (bitDigit x)
  have e_eq (x : Fin (t*b) → Bool) :
      (∑ i, bitDigit x i * 2^((b+1)*i.val)) + 2^(t*(b+1)) * ∑ i, (bitDigit x i)^2 = E x := by
    simp only [E, enc, pack, ← pow_mul, Nat.mul_comm t (b+1)]
  dsimp only
  change (∀ x, 2*((∑ i, bitDigit x i * 2^((b+1)*i.val)) + 2^(t*(b+1)) * ∑ i, (bitDigit x i)^2)
    < 2^(t*(b+1)+2*b+Nat.clog 2 t+1)) ∧ Function.Injective _ ∧ _
  have ap (x y z : Fin (t*b) → Bool) (he : E x + E z = 2 * E y) : x=y ∧ y=z := by
    obtain ⟨h1,h2⟩ := enc_ap (bitDigit x) (bitDigit y) (bitDigit z)
      (digit_lt x) (digit_lt y) (digit_lt z) he
    exact ⟨digit_unique hb _ _ h1, digit_unique hb _ _ h2⟩
  refine ⟨fun x => (e_eq x) ▸ enc_bound ht (bitDigit x) (digit_lt x), ?_, ?_⟩
  · intro x y hxy
    change _ = _ at hxy
    change (∑ i, bitDigit x i * 2^((b+1)*i.val)) + 2^(t*(b+1)) * ∑ i, (bitDigit x i)^2 =
      (∑ i, bitDigit y i * 2^((b+1)*i.val)) + 2^(t*(b+1)) * ∑ i, (bitDigit y i)^2 at hxy
    rw [e_eq, e_eq] at hxy
    exact (ap x y x (by omega)).1
  · intro x y z he
    apply ap
    simpa only [← e_eq, bitDigit] using he

end PEqualNP.Outside.L_lib_580.Arithmetic

namespace PEqualNP.Outside.L_lib_580.Expansion

theorem weightedBits (t b : ℕ) (bit : Fin t → Fin b → Bool) :
    (∑ i : Fin t, (∑ j : Fin b, if bit i j then 2 ^ j.val else 0) * 2 ^ ((b + 1) * i.val)) +
      2 ^ (t * (b + 1)) * ∑ i : Fin t, (∑ j : Fin b, if bit i j then 2 ^ j.val else 0) ^ 2 =
    (∑ i : Fin t, ∑ j : Fin b, if bit i j then 2 ^ ((b + 1) * i.val + j.val) else 0) +
      ∑ i : Fin t, ∑ j : Fin b, ∑ k : Fin b,
        if bit i j && bit i k then 2 ^ (t * (b + 1) + j.val + k.val) else (0 : ℕ) := by
  simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    cases bit i j <;> simp [pow_add, Nat.mul_comm]
  · apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    cases bit i j <;> cases bit i k <;> simp [pow_add, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]

end PEqualNP.Outside.L_lib_580.Expansion

namespace PEqualNP.Outside.L_lib_580.CircuitProof

def gather {n : ℕ} {α : Type} (f : Fin n → List α) : List α := (List.ofFn f).flatten

theorem gatherSum {n : ℕ} {α : Type} (f : Fin n → List α) (v : α → ℕ) :
    ((gather f).map v).sum = ∑ i : Fin n, ((f i).map v).sum := by
  simp [gather, List.map_ofFn, Fin.sum_ofFn, Function.comp_def]

theorem gatherLen {n : ℕ} {α : Type} (f : Fin n → List α) :
    (gather f).length = ∑ i : Fin n, (f i).length := by
  simp [gather, List.length_flatten, List.map_ofFn, Fin.sum_ofFn, Function.comp_def]

theorem gatherMem {n : ℕ} {α : Type} (f : Fin n → List α) (x : α) :
    x ∈ gather f ↔ ∃ i : Fin n, x ∈ f i := by
  simp [gather, List.mem_flatten, List.mem_ofFn]

def inputSpecs (t b : ℕ) : List (ℕ × ℕ × ℕ) :=
  gather (fun i : Fin t => List.ofFn fun j : Fin b =>
    ((b + 1) * i.val + j.val, i.val * b + j.val, i.val * b + j.val)) ++
  gather (fun i : Fin t => gather fun j : Fin b => List.ofFn fun k : Fin b =>
    (t * (b + 1) + j.val + k.val, i.val * b + j.val, i.val * b + k.val))

theorem inputSpecs_size (t b : ℕ) : (inputSpecs t b).length = t*b + t*b*b := by
  simp [inputSpecs, gatherLen, Nat.mul_assoc]

theorem rawBound {t b : ℕ} (i : Fin t) (j : Fin b) : i.val*b+j.val < t*b := by
  have h := Nat.mul_le_mul_right b i.isLt
  rw [Nat.succ_mul] at h
  omega

theorem inputSpecs_valid (t b : ℕ) (p : ℕ × ℕ × ℕ) (hp : p ∈ inputSpecs t b) :
    p.2.1 < t*b ∧ p.2.2 < t*b := by
  simp only [inputSpecs, List.mem_append, gatherMem, List.mem_ofFn] at hp
  rcases hp with ⟨i, j, rfl⟩ | ⟨i, j, k, rfl⟩
  · exact ⟨rawBound i j, rawBound i j⟩
  · exact ⟨rawBound i j, rawBound i k⟩

def specVal (x : List Bool) (p : ℕ × ℕ × ℕ) : ℕ :=
  ((x.getD p.2.1 false) && (x.getD p.2.2 false)).toNat * 2^p.1

theorem toNatWeight (v : Bool) (e : ℕ) : v.toNat * 2^e = if v then 2^e else 0 := by
  cases v <;> simp

theorem inputSpecs_value (t b : ℕ) (x : List Bool) :
    let bit := fun (i : Fin t) (j : Fin b) => x.getD (i.val*b+j.val) false
    ((inputSpecs t b).map (specVal x)).sum =
      (∑ i : Fin t, ∑ j : Fin b, if bit i j then 2^((b+1)*i.val+j.val) else 0) +
      ∑ i : Fin t, ∑ j : Fin b, ∑ k : Fin b,
        if bit i j && bit i k then 2^(t*(b+1)+j.val+k.val) else 0 := by
  simp [inputSpecs, List.map_append, gatherSum, List.map_ofFn, Fin.sum_ofFn,
    Function.comp_def, specVal, toNatWeight]

end PEqualNP.Outside.L_lib_580.CircuitProof

namespace PEqualNP.Outside.L_lib_580.CircuitProof

open PEqualNP.CircuitLowerBounds

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def evalW (x : List Bool) (gs : List Gate) : List Bool :=
  gs.foldl stepWire x

def wireVal (x : List Bool) (gs : List Gate) (idx : Nat) : Bool :=
  (evalW x gs).getD idx false

def GoodGates (inputs : Nat) (gs : List Gate) : Prop :=
  (∀ g ∈ gs, ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) ∨ (g.op = .not ∧ g.inputs.length = 1)) ∧
  (∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < inputs + j)

def Extends (gs gs' : List Gate) : Prop :=
  ∃ ext, gs' = gs ++ ext

theorem Extends_refl (gs : List Gate) : Extends gs gs :=
  ⟨[], by simp⟩

theorem Extends_trans {a b c : List Gate} (h1 : Extends a b) (h2 : Extends b c) :
    Extends a c := by
  rcases h1 with ⟨e1, rfl⟩
  rcases h2 with ⟨e2, rfl⟩
  exact ⟨e1 ++ e2, by simp [List.append_assoc]⟩

theorem Extends_len {a b : List Gate} (h : Extends a b) : a.length ≤ b.length := by
  rcases h with ⟨e, rfl⟩
  simp

theorem evalW_len (x : List Bool) (gs : List Gate) :
    (evalW x gs).length = x.length + gs.length := by
  unfold evalW
  induction gs generalizing x with
  | nil => simp
  | cons g tl ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih (stepWire x g)]
    simp [stepWire]
    omega

theorem evalW_append (x : List Bool) (gs1 gs2 : List Gate) :
    evalW x (gs1 ++ gs2) = evalW (evalW x gs1) gs2 := by
  unfold evalW
  rw [List.foldl_append]

theorem stepWire_getD_lt (w : List Bool) (g : Gate) {i : Nat} (hi : i < w.length) :
    (stepWire w g).getD i false = w.getD i false := by
  simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem stepWire_getD_self (w : List Bool) (g : Gate) :
    (stepWire w g).getD w.length false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  simp [stepWire, List.getD_eq_getElem?_getD]

theorem wireVal_extends {x : List Bool} {gs1 gs2 : List Gate} {idx : Nat}
    (hext : Extends gs1 gs2) (hidx : idx < x.length + gs1.length) :
    wireVal x gs2 idx = wireVal x gs1 idx := by
  rcases hext with ⟨ext, rfl⟩
  unfold wireVal
  rw [evalW_append]
  have hlen : idx < (evalW x gs1).length := by rw [evalW_len]; exact hidx
  generalize evalW x gs1 = w at hlen ⊢
  unfold evalW
  induction ext generalizing w with
  | nil => rfl
  | cons g tl ih =>
    simp only [List.foldl_cons]
    have hlen' : idx < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlen', stepWire_getD_lt w g hlen]

theorem wireVal_snoc_self (x : List Bool) (gs : List Gate) (g : Gate) :
    wireVal x (gs ++ [g]) (x.length + gs.length) =
      g.op.eval (g.inputs.map (wireVal x gs)) := by
  unfold wireVal
  rw [evalW_append]
  unfold evalW
  simp only [List.foldl_cons, List.foldl_nil]
  have hlen : x.length + gs.length = (gs.foldl stepWire x).length := (evalW_len x gs).symm
  rw [hlen, stepWire_getD_self]

theorem GoodGates_nil (inputs : Nat) : GoodGates inputs [] :=
  ⟨fun _ h => (by cases h), fun _ h => (by simp at h)⟩

theorem GoodGates_snoc {inputs : Nat} {gs : List Gate} {g : Gate}
    (hg : GoodGates inputs gs)
    (hshape : ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) ∨ (g.op = .not ∧ g.inputs.length = 1))
    (hback : ∀ i ∈ g.inputs, i < inputs + gs.length) :
    GoodGates inputs (gs ++ [g]) := by
  refine ⟨?_, ?_⟩
  · intro g' hg'
    rcases List.mem_append.mp hg' with h1 | h2
    · exact hg.1 g' h1
    · rw [List.mem_singleton.mp h2]
      exact hshape
  · intro j hj i hi
    simp only [List.length_append, List.length_singleton] at hj
    by_cases hlt : j < gs.length
    · have hget : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
      rw [hget] at hi
      exact hg.2 j hlt i hi
    · have heq : j = gs.length := by omega
      subst heq
      have hget : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      rw [hget] at hi
      exact hback i hi

def addAnd (inputs : Nat) (gs : List Gate) (a b : Nat) : List Gate × Nat :=
  (gs ++ [⟨.and, [a, b]⟩], inputs + gs.length)

def addOr (inputs : Nat) (gs : List Gate) (a b : Nat) : List Gate × Nat :=
  (gs ++ [⟨.or, [a, b]⟩], inputs + gs.length)

def addNot (inputs : Nat) (gs : List Gate) (a : Nat) : List Gate × Nat :=
  (gs ++ [⟨.not, [a]⟩], inputs + gs.length)

theorem addAnd_spec {inputs : Nat} {gs : List Gate} {a b : Nat}
    (hg : GoodGates inputs gs) (ha : a < inputs + gs.length) (hb : b < inputs + gs.length) :
    let r := addAnd inputs gs a b
    Extends gs r.1 ∧ r.1.length = gs.length + 1 ∧ GoodGates inputs r.1 ∧ r.2 < inputs + r.1.length ∧
    ∀ x : List Bool, x.length = inputs →
      wireVal x r.1 r.2 = (wireVal x gs a && wireVal x gs b) := by
  refine ⟨⟨[⟨.and, [a, b]⟩], rfl⟩, by simp [addAnd],
    GoodGates_snoc hg (by simp) (fun i hi => by simp at hi; rcases hi with rfl | rfl <;> omega),
    by simp [addAnd], ?_⟩
  intro x hx
  dsimp only [addAnd]
  rw [← hx, wireVal_snoc_self]
  simp [GateOp.eval]

theorem addOr_spec {inputs : Nat} {gs : List Gate} {a b : Nat}
    (hg : GoodGates inputs gs) (ha : a < inputs + gs.length) (hb : b < inputs + gs.length) :
    let r := addOr inputs gs a b
    Extends gs r.1 ∧ r.1.length = gs.length + 1 ∧ GoodGates inputs r.1 ∧ r.2 < inputs + r.1.length ∧
    ∀ x : List Bool, x.length = inputs →
      wireVal x r.1 r.2 = (wireVal x gs a || wireVal x gs b) := by
  refine ⟨⟨[⟨.or, [a, b]⟩], rfl⟩, by simp [addOr],
    GoodGates_snoc hg (by simp) (fun i hi => by simp at hi; rcases hi with rfl | rfl <;> omega),
    by simp [addOr], ?_⟩
  intro x hx
  dsimp only [addOr]
  rw [← hx, wireVal_snoc_self]
  simp [GateOp.eval]

theorem addNot_spec {inputs : Nat} {gs : List Gate} {a : Nat}
    (hg : GoodGates inputs gs) (ha : a < inputs + gs.length) :
    let r := addNot inputs gs a
    Extends gs r.1 ∧ r.1.length = gs.length + 1 ∧ GoodGates inputs r.1 ∧ r.2 < inputs + r.1.length ∧
    ∀ x : List Bool, x.length = inputs →
      wireVal x r.1 r.2 = !(wireVal x gs a) := by
  refine ⟨⟨[⟨.not, [a]⟩], rfl⟩, by simp [addNot],
    GoodGates_snoc hg (by simp) (fun i hi => by simp at hi; subst hi; exact ha),
    by simp [addNot], ?_⟩
  intro x hx
  dsimp only [addNot]
  rw [← hx, wireVal_snoc_self]
  simp [GateOp.eval]

def addFullAdder (inputs : Nat) (gs : List Gate) (a b cin : Nat) :
    List Gate × Nat × Nat :=
  let p := inputs + gs.length
  let g1 := gs ++ [⟨.or, [a, b]⟩]
  let g2 := g1 ++ [⟨.and, [a, b]⟩]
  let g3 := g2 ++ [⟨.not, [p + 1]⟩]
  let g4 := g3 ++ [⟨.and, [p, p + 2]⟩]
  let g5 := g4 ++ [⟨.or, [p + 3, cin]⟩]
  let g6 := g5 ++ [⟨.and, [p + 3, cin]⟩]
  let g7 := g6 ++ [⟨.not, [p + 5]⟩]
  let g8 := g7 ++ [⟨.and, [p + 4, p + 6]⟩]
  let g9 := g8 ++ [⟨.or, [p + 1, p + 5]⟩]
  (g9, p + 7, p + 8)

theorem fullAdder_bool (a b c : Bool) :
    let s1 := (a || b) && !(a && b)
    let sum := (s1 || c) && !(s1 && c)
    let cout := (a && b) || (s1 && c)
    a.toNat + b.toNat + c.toNat = sum.toNat + 2 * cout.toNat := by
  cases a <;> cases b <;> cases c <;> rfl

theorem addFullAdder_spec {inputs : Nat} {gs : List Gate} {a b cin : Nat}
    (hg : GoodGates inputs gs)
    (ha : a < inputs + gs.length) (hb : b < inputs + gs.length) (hc : cin < inputs + gs.length) :
    let r := addFullAdder inputs gs a b cin
    Extends gs r.1 ∧ r.1.length = gs.length + 9 ∧ GoodGates inputs r.1 ∧
    r.2.1 < inputs + r.1.length ∧ r.2.2 < inputs + r.1.length ∧
    ∀ x : List Bool, x.length = inputs →
      (wireVal x gs a).toNat + (wireVal x gs b).toNat + (wireVal x gs cin).toNat =
        (wireVal x r.1 r.2.1).toNat + 2 * (wireVal x r.1 r.2.2).toNat := by
  unfold addFullAdder
  set p := inputs + gs.length
  set g1 := gs ++ [⟨.or, [a, b]⟩]
  set g2 := g1 ++ [⟨.and, [a, b]⟩]
  set g3 := g2 ++ [⟨.not, [p + 1]⟩]
  set g4 := g3 ++ [⟨.and, [p, p + 2]⟩]
  set g5 := g4 ++ [⟨.or, [p + 3, cin]⟩]
  set g6 := g5 ++ [⟨.and, [p + 3, cin]⟩]
  set g7 := g6 ++ [⟨.not, [p + 5]⟩]
  set g8 := g7 ++ [⟨.and, [p + 4, p + 6]⟩]
  set g9 := g8 ++ [⟨.or, [p + 1, p + 5]⟩]
  have hl1 : g1.length = gs.length + 1 := by simp [g1]
  have hl2 : g2.length = gs.length + 2 := by simp [g2, hl1]
  have hl3 : g3.length = gs.length + 3 := by simp [g3, hl2]
  have hl4 : g4.length = gs.length + 4 := by simp [g4, hl3]
  have hl5 : g5.length = gs.length + 5 := by simp [g5, hl4]
  have hl6 : g6.length = gs.length + 6 := by simp [g6, hl5]
  have hl7 : g7.length = gs.length + 7 := by simp [g7, hl6]
  have hl8 : g8.length = gs.length + 8 := by simp [g8, hl7]
  have hl9 : g9.length = gs.length + 9 := by simp [g9, hl8]
  have he1 : Extends gs g1 := ⟨_, rfl⟩
  have he2 : Extends g1 g2 := ⟨_, rfl⟩
  have he3 : Extends g2 g3 := ⟨_, rfl⟩
  have he4 : Extends g3 g4 := ⟨_, rfl⟩
  have he5 : Extends g4 g5 := ⟨_, rfl⟩
  have he6 : Extends g5 g6 := ⟨_, rfl⟩
  have he7 : Extends g6 g7 := ⟨_, rfl⟩
  have he8 : Extends g7 g8 := ⟨_, rfl⟩
  have he9 : Extends g8 g9 := ⟨_, rfl⟩
  have hg1 : GoodGates inputs g1 := GoodGates_snoc hg (by simp) (by intro i hi; simp at hi; rcases hi with rfl | rfl <;> omega)
  have hg2 : GoodGates inputs g2 := GoodGates_snoc hg1 (by simp) (by intro i hi; simp at hi; rcases hi with rfl | rfl <;> omega)
  have hg3 : GoodGates inputs g3 := GoodGates_snoc hg2 (by simp) (by intro i hi; simp at hi; subst hi; omega)
  have hg4 : GoodGates inputs g4 := GoodGates_snoc hg3 (by simp) (by intro i hi; simp at hi; rcases hi with rfl | rfl <;> omega)
  have hg5 : GoodGates inputs g5 := GoodGates_snoc hg4 (by simp) (by intro i hi; simp at hi; rcases hi with rfl | rfl <;> omega)
  have hg6 : GoodGates inputs g6 := GoodGates_snoc hg5 (by simp) (by intro i hi; simp at hi; rcases hi with rfl | rfl <;> omega)
  have hg7 : GoodGates inputs g7 := GoodGates_snoc hg6 (by simp) (by intro i hi; simp at hi; subst hi; omega)
  have hg8 : GoodGates inputs g8 := GoodGates_snoc hg7 (by simp) (by intro i hi; simp at hi; rcases hi with rfl | rfl <;> omega)
  have hg9 : GoodGates inputs g9 := GoodGates_snoc hg8 (by simp) (by intro i hi; simp at hi; rcases hi with rfl | rfl <;> omega)
  refine ⟨Extends_trans he1 (Extends_trans he2 (Extends_trans he3 (Extends_trans he4
    (Extends_trans he5 (Extends_trans he6 (Extends_trans he7 (Extends_trans he8 he9))))))),
    hl9, hg9, by change p + 7 < inputs + g9.length; omega, by change p + 8 < inputs + g9.length; omega, ?_⟩
  intro x hx
  set va := wireVal x gs a
  set vb := wireVal x gs b
  set vc := wireVal x gs cin
  have hp : x.length + gs.length = p := by omega
  have w0 : wireVal x g1 p = (va || vb) := by
    rw [← hp]; change wireVal x (gs ++ [⟨.or, [a, b]⟩]) (x.length + gs.length) = _
    rw [wireVal_snoc_self]; simp [GateOp.eval, va, vb]
  have w1 : wireVal x g2 (p + 1) = (va && vb) := by
    have hq : x.length + g1.length = p + 1 := by omega
    rw [← hq]; change wireVal x (g1 ++ [⟨.and, [a, b]⟩]) (x.length + g1.length) = _
    rw [wireVal_snoc_self]
    simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true]
    rw [wireVal_extends he1 (by omega), wireVal_extends he1 (by omega)]
  have w2 : wireVal x g3 (p + 2) = !(va && vb) := by
    have hq : x.length + g2.length = p + 2 := by omega
    rw [← hq]; change wireVal x (g2 ++ [⟨.not, [p + 1]⟩]) (x.length + g2.length) = _
    rw [wireVal_snoc_self]; simp [GateOp.eval, w1]
  have w3 : wireVal x g4 (p + 3) = ((va || vb) && !(va && vb)) := by
    have hq : x.length + g3.length = p + 3 := by omega
    rw [← hq]; change wireVal x (g3 ++ [⟨.and, [p, p + 2]⟩]) (x.length + g3.length) = _
    rw [wireVal_snoc_self]
    simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true]
    rw [wireVal_extends (Extends_trans he2 he3) (by omega), w0, w2]
  have w4 : wireVal x g5 (p + 4) = (((va || vb) && !(va && vb)) || vc) := by
    have hq : x.length + g4.length = p + 4 := by omega
    rw [← hq]; change wireVal x (g4 ++ [⟨.or, [p + 3, cin]⟩]) (x.length + g4.length) = _
    rw [wireVal_snoc_self]
    simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false]
    rw [w3, wireVal_extends (Extends_trans he1 (Extends_trans he2 (Extends_trans he3 he4))) (by omega)]
  have w5 : wireVal x g6 (p + 5) = (((va || vb) && !(va && vb)) && vc) := by
    have hq : x.length + g5.length = p + 5 := by omega
    rw [← hq]; change wireVal x (g5 ++ [⟨.and, [p + 3, cin]⟩]) (x.length + g5.length) = _
    rw [wireVal_snoc_self]
    simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true]
    rw [wireVal_extends he5 (by omega), w3,
        wireVal_extends (Extends_trans he1 (Extends_trans he2 (Extends_trans he3 (Extends_trans he4 he5)))) (by omega)]
  have w6 : wireVal x g7 (p + 6) = !(((va || vb) && !(va && vb)) && vc) := by
    have hq : x.length + g6.length = p + 6 := by omega
    rw [← hq]; change wireVal x (g6 ++ [⟨.not, [p + 5]⟩]) (x.length + g6.length) = _
    rw [wireVal_snoc_self]; simp [GateOp.eval, w5]
  have w7 : wireVal x g8 (p + 7) =
      ((((va || vb) && !(va && vb)) || vc) && !(((va || vb) && !(va && vb)) && vc)) := by
    have hq : x.length + g7.length = p + 7 := by omega
    rw [← hq]; change wireVal x (g7 ++ [⟨.and, [p + 4, p + 6]⟩]) (x.length + g7.length) = _
    rw [wireVal_snoc_self]
    simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true]
    rw [wireVal_extends (Extends_trans he6 he7) (by omega), w4, w6]
  have w8 : wireVal x g9 (p + 8) = ((va && vb) || (((va || vb) && !(va && vb)) && vc)) := by
    have hq : x.length + g8.length = p + 8 := by omega
    rw [← hq]; change wireVal x (g8 ++ [⟨.or, [p + 1, p + 5]⟩]) (x.length + g8.length) = _
    rw [wireVal_snoc_self]
    simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false]
    rw [wireVal_extends (Extends_trans he3 (Extends_trans he4 (Extends_trans he5 (Extends_trans he6 (Extends_trans he7 he8))))) (by omega),
        w1, wireVal_extends (Extends_trans he7 he8) (by omega), w5]
  have w7' : wireVal x g9 (p + 7) =
      ((((va || vb) && !(va && vb)) || vc) && !(((va || vb) && !(va && vb)) && vc)) := by
    rw [wireVal_extends he9 (by omega), w7]
  rw [w7', w8]
  exact fullAdder_bool va vb vc

end PEqualNP.Outside.L_lib_580.CircuitProof

namespace PEqualNP.Outside.L_lib_580.CircuitProof

open PEqualNP.CircuitLowerBounds

theorem inputValue (x : List Bool) (gs : List Gate) (i : ℕ) (hi : i < x.length) :
    wireVal x gs i = x.getD i false := by
  change wireVal x gs i = wireVal x [] i
  exact wireVal_extends (show Extends [] gs from ⟨gs, by simp⟩) (by simpa)

theorem falseSeed (m : ℕ) (hm : 0 < m) :
    ∃ (gs : List Gate) (z : ℕ), GoodGates m gs ∧ gs.length = 2 ∧ z < m + gs.length ∧
      ∀ x : List Bool, x.length = m → wireVal x gs z = false := by
  let a := addNot m [] 0
  have hbase : GoodGates m [] := by simp [GoodGates]
  obtain ⟨_, haLen, haGood, haValid, haVal⟩ := addNot_spec hbase (show 0 < m + [].length from by simpa)
  let b := addAnd m a.1 0 a.2
  obtain ⟨_, hbLen, hbGood, hbValid, hbVal⟩ := addAnd_spec haGood (show 0 < m + a.1.length from by omega) haValid
  refine ⟨b.1, b.2, hbGood, ?_, hbValid, ?_⟩
  · change a.1.length = 1 at haLen
    change b.1.length = a.1.length + 1 at hbLen
    omega
  · intro x hx
    rw [hbVal x hx, haVal x hx, inputValue x _ 0 (by omega)]
    change (x.getD 0 false && !(x.getD 0 false)) = false
    cases x.getD 0 false <;> rfl

theorem inputWeightedExt {x : List Bool} {gs gs' : List Gate} (terms : List (ℕ × ℕ))
    (he : Extends gs gs') (hv : ∀ p ∈ terms, p.2 < x.length + gs.length) :
    (terms.map fun p => (wireVal x gs' p.2).toNat * 2^p.1).sum =
      (terms.map fun p => (wireVal x gs p.2).toNat * 2^p.1).sum := by
  congr 1
  apply List.map_congr_left
  intro p hp
  rw [wireVal_extends he (hv p hp)]

theorem buildInputs (m : ℕ) (hm : 0 < m) (l : List (ℕ × ℕ × ℕ))
    (valid : ∀ p ∈ l, p.2.1 < m ∧ p.2.2 < m) :
    ∃ (gs : List Gate) (z : ℕ) (terms : List (ℕ × ℕ)),
      GoodGates m gs ∧ gs.length = l.length + 2 ∧ z < m + gs.length ∧
      (∀ x : List Bool, x.length = m → wireVal x gs z = false) ∧ terms.length = l.length ∧
      (∀ p ∈ terms, p.2 < m + gs.length) ∧ ∀ x : List Bool, x.length = m →
        (terms.map fun p => (wireVal x gs p.2).toNat * 2^p.1).sum = (l.map (specVal x)).sum := by
  induction l with
  | nil =>
    obtain ⟨gs, z, hg, hlen, hz, hzero⟩ := falseSeed m hm
    exact ⟨gs, z, [], hg, hlen, hz, hzero, rfl, by simp, by simp⟩
  | cons p l ih =>
    obtain ⟨gs, z, ts, hg, hlen, hz, hzero, hts, htv, hval⟩ :=
      ih (fun q h => valid q (by simp [h]))
    obtain ⟨ha, hb⟩ := valid p (by simp)
    let r := addAnd m gs p.2.1 p.2.2
    obtain ⟨he, hrlen, hgood, hidx, hout⟩ := addAnd_spec hg
      (show p.2.1 < m + gs.length from by omega) (show p.2.2 < m + gs.length from by omega)
    change r.1.length = gs.length + 1 at hrlen
    refine ⟨r.1, z, (p.1,r.2) :: ts, hgood, ?_, by omega, ?_, by simpa using hts, ?_, ?_⟩
    · simp only [List.length_cons]; omega
    · intro x hx
      rw [wireVal_extends he (show z < x.length + gs.length from by omega), hzero x hx]
    · intro q hq
      rcases List.mem_cons.mp hq with h | h
      · subst q; exact hidx
      · have := htv q h; omega
    · intro x hx
      simp only [List.map_cons, List.sum_cons]
      rw [inputWeightedExt ts he (fun q h => by simpa [hx] using htv q h), hval x hx, hout x hx]
      rw [inputValue x gs _ (by omega), inputValue x gs _ (by omega)]
      rfl

end PEqualNP.Outside.L_lib_580.CircuitProof

namespace PEqualNP.Outside.L_lib_580.CircuitProof
open PEqualNP.CircuitLowerBounds

def weighted (x : List Bool) (gs : List Gate) (ts : List (Nat × Nat)) : Nat :=
  (ts.map fun p => (wireVal x gs p.2).toNat * 2 ^ p.1).sum

def countW (x : List Bool) (gs : List Gate) (ws : List Nat) : Nat :=
  (ws.map fun w => (wireVal x gs w).toNat).sum

theorem countW_cons (x : List Bool) (gs : List Gate) (w : Nat) (ws : List Nat) :
    countW x gs (w :: ws) = (wireVal x gs w).toNat + countW x gs ws := by
  simp [countW]

theorem countW_ext {x : List Bool} {a b : List Gate} {ws : List Nat}
    (he : Extends a b) (hw : ∀ w ∈ ws, w < x.length + a.length) :
    countW x b ws = countW x a ws := by
  unfold countW
  congr 1
  apply List.map_congr_left
  intro w hm
  rw [wireVal_extends he (hw w hm)]

theorem weighted_ext {x : List Bool} {a b : List Gate} {ts : List (Nat × Nat)}
    (he : Extends a b) (hw : ∀ p ∈ ts, p.2 < x.length + a.length) :
    weighted x b ts = weighted x a ts := by
  unfold weighted
  congr 1
  apply List.map_congr_left
  intro p hm
  rw [wireVal_extends he (hw p hm)]

def lowWeights : List (Nat × Nat) → List Nat
  | [] => []
  | (0,w) :: tl => w :: lowWeights tl
  | (_+1,_) :: tl => lowWeights tl

def highWeights : List (Nat × Nat) → List (Nat × Nat)
  | [] => []
  | (0,_) :: tl => highWeights tl
  | (n+1,w) :: tl => (n,w) :: highWeights tl

theorem split_val (x : List Bool) (gs : List Gate) (ts : List (Nat × Nat)) :
    weighted x gs ts = countW x gs (lowWeights ts) + 2 * weighted x gs (highWeights ts) := by
  induction ts with
  | nil => simp [weighted, countW, lowWeights, highWeights]
  | cons p tl ih =>
    obtain ⟨k,w⟩ := p
    cases k with
    | zero => simpa [weighted, countW, lowWeights, highWeights, Nat.add_assoc] using
        congrArg ((wireVal x gs w).toNat + ·) ih
    | succ k =>
      change (wireVal x gs w).toNat * 2 ^ (k+1) + weighted x gs tl =
        countW x gs (lowWeights tl) + 2 * ((wireVal x gs w).toNat * 2^k + weighted x gs (highWeights tl))
      rw [ih, pow_succ]
      ring

theorem split_len (ts : List (Nat × Nat)) :
    (lowWeights ts).length + (highWeights ts).length = ts.length := by
  induction ts with
  | nil => rfl
  | cons p tl ih =>
    obtain ⟨k,w⟩ := p
    cases k <;> simp only [lowWeights, highWeights, List.length_cons] <;> omega

theorem split_bounded {lim : Nat} {ts : List (Nat × Nat)} (ht : ∀ p ∈ ts, p.2 < lim) :
    (∀ w ∈ lowWeights ts, w < lim) ∧ (∀ p ∈ highWeights ts, p.2 < lim) := by
  induction ts with
  | nil => simp [lowWeights, highWeights]
  | cons p tl ih =>
    obtain ⟨k,w⟩ := p
    have hw := ht (k,w) (by simp)
    have ⟨hl,hh⟩ := ih (fun p hp => ht p (by simp [hp]))
    cases k <;> simp_all [lowWeights, highWeights] <;> assumption

theorem wZeroList (x : List Bool) (gs : List Gate) (ws : List Nat) :
    weighted x gs (ws.map (fun w => (0,w))) = countW x gs ws := by
  simp [weighted, countW, List.map_map, Function.comp_def]

theorem column (inputs : Nat) (gs : List Gate) (z : Nat) (ws : List Nat)
    (hg : GoodGates inputs gs) (hz : z < inputs+gs.length)
    (hzero : ∀ x : List Bool, x.length=inputs → wireVal x gs z=false)
    (ht : ∀ w ∈ ws, w < inputs+gs.length) :
    ∃ (gs' : List Gate) (s : Nat) (cs : List Nat),
      Extends gs gs' ∧ GoodGates inputs gs' ∧ gs'.length + 9*cs.length ≤ gs.length+9*ws.length ∧
      s < inputs + gs'.length ∧ (∀ w ∈ cs, w < inputs+gs'.length) ∧
      ∀ x : List Bool, x.length=inputs →
        countW x gs ws = (wireVal x gs' s).toNat + 2*countW x gs' cs := by
  match ws with
  | [] =>
    refine ⟨gs,z,[],Extends_refl _,hg,by simp,hz,by simp,?_⟩
    intro x hx
    simp [countW, hzero x hx]
  | [a] =>
    refine ⟨gs,a,[],Extends_refl _,hg,by simp,ht a (by simp),by simp,?_⟩
    intro x hx
    simp [countW]
  | [a,b] =>
    let r := addFullAdder inputs gs a b z
    obtain ⟨he,hl,hg',hs,hc,hval⟩ := addFullAdder_spec hg (ht a (by simp)) (ht b (by simp)) hz
    refine ⟨r.1,r.2.1,[r.2.2],he,hg',?_,hs,by simpa using hc,?_⟩
    · change r.1.length + 9*1 ≤ gs.length+9*2
      change r.1.length = gs.length + 9 at hl
      omega
    · intro x hx
      have eqv := hval x hx
      simpa [countW, hzero x hx, r] using eqv
  | a::b::c::tl =>
    let r := addFullAdder inputs gs a b c
    obtain ⟨he,hl,hg',hs,hc,hval⟩ := addFullAdder_spec hg (ht a (by simp)) (ht b (by simp)) (ht c (by simp))
    change Extends gs r.1 at he
    change r.1.length = gs.length + 9 at hl
    change r.2.1 < inputs+r.1.length at hs
    change r.2.2 < inputs+r.1.length at hc
    have htl : ∀ w ∈ tl, w < inputs+gs.length := fun w hw => ht w (by simp [hw])
    have hws : ∀ w ∈ r.2.1::tl, w < inputs+r.1.length := by
      intro w hw
      rcases List.mem_cons.mp hw with rfl | h
      · exact hs
      · have := htl w h; omega
    obtain ⟨gs',s,cs,he',hg'',hl',hs',hc',hval'⟩ := column inputs r.1 z (r.2.1::tl) hg' (by omega)
      (fun x hx => by rw [wireVal_extends he (by omega), hzero x hx]) hws
    have hle := Extends_len he'
    refine ⟨gs',s,r.2.2::cs,Extends_trans he he',hg'',?_,hs',?_,?_⟩
    · simp only [List.length_cons] at hl' ⊢
      omega
    · intro w hw
      rcases List.mem_cons.mp hw with rfl | h
      · omega
      · exact hc' w h
    · intro x hx
      have e1 := hval x hx
      change _ = (wireVal x r.1 r.2.1).toNat + 2*(wireVal x r.1 r.2.2).toNat at e1
      have e2 := hval' x hx
      rw [countW_cons, countW_ext he (fun w hw => by have := htl w hw; omega)] at e2
      simp only [countW_cons]
      rw [wireVal_extends (idx := r.2.2) he' (by omega)]
      omega
termination_by ws.length
decreasing_by simp_wf

theorem testBit_low (f : Bool) (n : Nat) : (f.toNat + 2*n).testBit 0 = f := by
  cases f <;> simp [Nat.testBit_zero]

theorem testBit_high (f : Bool) (n j : Nat) : (f.toNat + 2*n).testBit (j+1) = n.testBit j := by
  rw [Nat.testBit_succ]
  have : (f.toNat + 2*n)/2 = n := by cases f <;> simp <;> omega
  rw [this]

theorem compress (inputs h : Nat) (gs : List Gate) (z : Nat) (ts : List (Nat × Nat))
    (hg : GoodGates inputs gs) (hz : z < inputs+gs.length)
    (hzero : ∀ x : List Bool, x.length=inputs → wireVal x gs z=false)
    (ht : ∀ p∈ts,p.2 < inputs+gs.length) :
    ∃ (gs' : List Gate) (outs : List Nat), Extends gs gs' ∧ GoodGates inputs gs' ∧
      gs'.length ≤ gs.length + 9*(ts.length+h) ∧ outs.length=h ∧
      (∀ w∈outs,w < inputs+gs'.length) ∧ ∀ x : List Bool, x.length=inputs → ∀ j<h,
      wireVal x gs' (outs.getD j 0)=(weighted x gs ts).testBit j := by
  induction h generalizing gs ts with
  | zero =>
    exact ⟨gs,[],Extends_refl _,hg,by omega,rfl,by simp,by simp⟩
  | succ h ih =>
    obtain ⟨lo,hi⟩ := split_bounded ht
    obtain ⟨g,s,cs,ext,good,cost,hs,hcs,hval⟩ := column inputs gs z (lowWeights ts) hg hz hzero lo
    let more := cs.map (fun w => (0,w)) ++ highWeights ts
    have hle := Extends_len ext
    have hm : ∀ p ∈ more, p.2 < inputs+g.length := by
      intro p hp
      rcases List.mem_append.mp hp with hm | hk
      · obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hm
        exact hcs w hw
      · have := hi p hk; omega
    obtain ⟨g',ws,e2,good2,cost2,len,hws,v2⟩ := ih g more good (by omega)
      (fun x hx => by rw [wireVal_extends ext (by omega), hzero x hx]) hm
    have hle2 := Extends_len e2
    refine ⟨g',s::ws,Extends_trans ext e2,good2,?_,by simp [len],?_,?_⟩
    · have hlen := split_len ts
      simp only [more,List.length_append,List.length_map] at cost2
      omega
    · intro w hw
      rcases List.mem_cons.mp hw with rfl | h
      · omega
      · exact hws w h
    · intro x hx j hj
      have eqv : weighted x gs ts = (wireVal x g s).toNat + 2*weighted x g more := by
        rw [split_val, hval x hx]
        have sumEq : weighted x g more = countW x g cs + weighted x gs (highWeights ts) := by
          change (List.map _ (_ ++ _)).sum = _
          rw [List.map_append,List.sum_append]
          change weighted x g (cs.map fun w => (0,w)) + weighted x g (highWeights ts) = _
          rw [wZeroList, weighted_ext ext (fun p hp => by have := hi p hp; omega)]
        rw [sumEq]
        omega
      cases j with
      | zero =>
        change wireVal x g' s = _
        rw [wireVal_extends e2 (by omega), eqv, testBit_low]
      | succ j =>
        change wireVal x g' (ws.getD j 0) = _
        rw [v2 x hx j (by omega), eqv, testBit_high]

end PEqualNP.Outside.L_lib_580.CircuitProof

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_lib_580.CircuitProof

theorem PEqualNP.Outside.L_lib_580 : (∀ (t b : ℕ), 0 < t → 0 < b →
  let m := t*b
  let X := Fin m → Bool
  let low := t*(b+1)
  let h := low + 2*b + Nat.clog 2 t + 1
  let digit := fun (raw : X) (i : Fin t) => ∑ j : Fin b,
    if (List.ofFn raw).getD (i.val*b+j.val) false then 2^j.val else 0
  let lift := fun payload : X =>
    (∑ i : Fin t, digit payload i * 2^((b+1)*i.val)) + 2^low * ∑ i : Fin t, (digit payload i)^2
  (∀ x : X, 2 * lift x < 2^h) ∧ Function.Injective lift ∧
  (∀ x y z : X, lift x + lift z = 2 * lift y → x = y ∧ y = z) ∧
  ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (out : Fin h → Fin (m+C.size)),
    PEqualNP.MetaComplexity.NestedCover.ReadsBack m C ∧
    (∀ g ∈ C.gates, ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) ∨
      (g.op = .not ∧ g.inputs.length = 1)) ∧
    C.size ≤ 256*(t*b*b+h+1) ∧ ∀ (word : X) (j : Fin h),
      (C.wires (List.ofFn word)).getD (out j).val false = (lift word).testBit j.val) := by
  intro t b ht hb
  dsimp only
  obtain ⟨width, injective, progression⟩ := PEqualNP.Outside.L_lib_580.Arithmetic.arithmetic t b ht hb
  refine ⟨width, injective, progression, ?_⟩
  let m := t*b
  let h := t*(b+1)+2*b+Nat.clog 2 t+1
  obtain ⟨gs,z,terms,hgood,hglen,hz,hzero,htlen,hterms,hvalue⟩ :=
    buildInputs m (Nat.mul_pos ht hb) (inputSpecs t b) (inputSpecs_valid t b)
  obtain ⟨gates,outs,_,hgood',hcost,hlen,houts,hbits⟩ :=
    compress m h gs z terms hgood hz hzero hterms
  let C : Circuit := ⟨gates,z⟩
  let out (j : Fin h) : Fin (m+C.size) :=
    ⟨outs.getD j.val 0, by
      apply houts
      have hj : j.val < outs.length := by rw [hlen]; exact j.isLt
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
      exact List.getElem_mem hj⟩
  refine ⟨C,out,hgood'.2,hgood'.1,?_,?_⟩
  · change gates.length ≤ 256*(t*b*b+h+1)
    rw [inputSpecs_size] at hglen htlen
    have hfactor : t*b ≤ t*b*b := Nat.le_mul_of_pos_right _ hb
    omega
  · intro word j
    have hx : (List.ofFn word).length = m := by simp [m]
    change wireVal (List.ofFn word) gates (outs.getD j.val 0) = _
    rw [hbits _ hx j.val j.isLt]
    apply congrArg (fun q : ℕ => q.testBit j.val)
    unfold weighted
    rw [hvalue _ hx]
    exact (inputSpecs_value t b (List.ofFn word)).trans
      (PEqualNP.Outside.L_lib_580.Expansion.weightedBits t b
        (fun i j => (List.ofFn word).getD (i.val*b+j.val) false)).symm
