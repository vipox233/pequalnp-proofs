import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_29725

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity.NestedCover (ReadsBack gateAt)

private def val (p : List Gate) (x : List Bool) (i : ℕ) : Bool :=
  (Circuit.mk p i).eval x

private noncomputable def ands (p : List Gate) : ℕ :=
  p.countP (fun g => @decide (g.op = .and) (Classical.propDecidable _))

private def Allowed (g : Gate) : Prop :=
  (g.op = .and ∧ g.inputs.length = 2) ∨
  (g.op = .mod 2 ∧ g.inputs.length ≤ 2) ∨
  (g.op = .not ∧ g.inputs.length = 1)

private def WellFormed (k : ℕ) (p : List Gate) : Prop :=
  ReadsBack k ⟨p, 0⟩ ∧ ∀ g ∈ p, Allowed g

private structure Ext (k : ℕ) (p q : List Gate) (b a : ℕ) : Prop where
  old_le : p.length ≤ q.length
  length_le : q.length ≤ p.length + b
  ands_le : ands q ≤ ands p + a
  wf : WellFormed k p → WellFormed k q
  keep : ∀ x : List Bool, x.length = k → ∀ i, i < k + p.length →
    val q x i = val p x i

private theorem Ext.refl (k : ℕ) (p : List Gate) : Ext k p p 0 0 :=
  ⟨le_rfl, by simp, by simp, id, fun _ _ _ _ => rfl⟩

private theorem Ext.trans {k : ℕ} {p q r : List Gate} {b a b' a' : ℕ}
    (h : Ext k p q b a) (h' : Ext k q r b' a') : Ext k p r (b + b') (a + a') where
  old_le := h.old_le.trans h'.old_le
  length_le := by have := h.length_le; have := h'.length_le; omega
  ands_le := by have := h.ands_le; have := h'.ands_le; omega
  wf hw := h'.wf (h.wf hw)
  keep x hx i hi := by
    have hi' := h.old_le
    rw [h'.keep x hx i (by omega), h.keep x hx i hi]

private theorem Ext.weaken {k : ℕ} {p q : List Gate} {b a b' a' : ℕ}
    (h : Ext k p q b a) (hb : b ≤ b') (ha : a ≤ a') : Ext k p q b' a' where
  old_le := h.old_le
  length_le := by have := h.length_le; omega
  ands_le := by have := h.ands_le; omega
  wf := h.wf
  keep := h.keep

private theorem wires_length (p : List Gate) (x : List Bool) (o : ℕ) :
    ((Circuit.mk p o).wires x).length = x.length + p.length := by
  induction p generalizing x with
  | nil => simp [Circuit.wires]
  | cons g p ih =>
    simp only [Circuit.wires, List.foldl_cons] at ih ⊢
    rw [ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

private theorem wires_snoc (p : List Gate) (x : List Bool) (o : ℕ) (g : Gate) :
    (Circuit.mk (p ++ [g]) o).wires x =
      (Circuit.mk p o).wires x ++ [g.op.eval (g.inputs.map (val p x))] := by
  simp only [Circuit.wires, List.foldl_append, List.foldl_cons, List.foldl_nil]
  rfl

private theorem emitGate (k : ℕ) (p : List Gate) (g : Gate)
    (hread : ∀ i ∈ g.inputs, i < k + p.length)
    (hallow : Allowed g) (a : ℕ) (hcost : ands [g] ≤ a) :
    ∃ q o, Ext k p q 1 a ∧ o < k + q.length ∧
      ∀ x, x.length = k → val q x o = g.op.eval (g.inputs.map (val p x)) := by
  refine ⟨p ++ [g], k + p.length, ?_, by simp, ?_⟩
  · refine ⟨by simp, by simp, ?_, ?_, ?_⟩
    · simpa [ands, List.countP_append] using (Nat.add_le_add_left hcost (ands p))
    · rintro ⟨hback, hallowed⟩
      constructor
      · intro j hj i hi
        by_cases h : j < p.length
        · have heq : gateAt ⟨p ++ [g], 0⟩ j = gateAt ⟨p, 0⟩ j :=
            List.getD_append _ _ _ _ h
          rw [heq] at hi
          exact hback j h i hi
        · have hlen : j < p.length+1 := by simpa using hj
          have heq : j = p.length := by omega
          subst j
          simp [gateAt] at hi
          exact hread i hi
      · intro g' hg'
        rcases List.mem_append.mp hg' with hp | hg
        · exact hallowed g' hp
        · have := List.mem_singleton.mp hg
          simpa [this] using hallow
    · intro x hx i hi
      unfold val Circuit.eval
      rw [wires_snoc]
      exact List.getD_append _ _ _ _ (by simpa [wires_length, hx] using hi)
  · intro x hx
    change ((Circuit.mk (p ++ [g]) (k + p.length)).wires x).getD (k + p.length)
      false = g.op.eval (g.inputs.map (val p x))
    rw [wires_snoc, List.getD_append_right, wires_length, hx]
    · simp
    · simp [wires_length, hx]

private theorem emitAnd (k : ℕ) (p : List Gate) (i j : ℕ)
    (hi : i < k+p.length) (hj : j < k+p.length) :
    ∃ q o, Ext k p q 1 1 ∧ o < k+q.length ∧
      ∀ x, x.length=k → val q x o = (val p x i && val p x j) := by
  obtain ⟨q, o, he, ho, hv⟩ := emitGate k p ⟨.and, [i,j]⟩
    (by simp [hi, hj]) (by simp [Allowed]) 1 (by simp [ands])
  exact ⟨q, o, he, ho, fun x hx => by simpa [GateOp.eval] using hv x hx⟩

private theorem emitNot (k : ℕ) (p : List Gate) (i : ℕ) (hi : i < k+p.length) :
    ∃ q o, Ext k p q 1 0 ∧ o < k+q.length ∧
      ∀ x, x.length=k → val q x o = !val p x i := by
  obtain ⟨q, o, he, ho, hv⟩ := emitGate k p ⟨.not, [i]⟩
    (by simpa using hi) (by simp [Allowed]) 0 (by simp [ands])
  exact ⟨q, o, he, ho, fun x hx => by simpa [GateOp.eval] using hv x hx⟩

private theorem mod_xor (a b : Bool) :
    GateOp.eval (.mod 2) [a,b] = !(a ^^ b) := by
  cases a <;> cases b <;> rfl

private theorem emitXor (k : ℕ) (p : List Gate) (i j : ℕ)
    (hi : i < k+p.length) (hj : j < k+p.length) :
    ∃ q o, Ext k p q 2 0 ∧ o < k+q.length ∧
      ∀ x, x.length=k → val q x o = (val p x i ^^ val p x j) := by
  obtain ⟨p', s, he, hs, hv⟩ := emitGate k p ⟨.mod 2, [i,j]⟩
    (by simp [hi, hj]) (by simp [Allowed]) 0 (by simp [ands])
  obtain ⟨q, o, he', ho, hv'⟩ := emitNot k p' s hs
  refine ⟨q, o, he.trans he', ho, ?_⟩
  intro x hx
  simp only [List.map_cons, List.map_nil, mod_xor] at hv
  simp [hv' x hx, hv x hx]

private theorem emitConst (k : ℕ) (p : List Gate) (c : Bool) :
    ∃ q o, Ext k p q 2 0 ∧ o < k+q.length ∧ ∀ x, x.length=k → val q x o = c := by
  obtain ⟨p', s, he, hs, hv⟩ := emitGate k p ⟨.mod 2, []⟩
    (by simp) (by simp [Allowed]) 0 (by simp [ands])
  have ht (x : List Bool) (hx : x.length = k) : val p' x s = true := by
    simpa [GateOp.eval] using hv x hx
  cases c
  · obtain ⟨q, o, he', ho, hv'⟩ := emitNot k p' s hs
    exact ⟨q, o, he.trans he', ho, fun x hx => by simp [hv' x hx, ht x hx]⟩
  · exact ⟨p', s, he.weaken (by decide) le_rfl, hs, ht⟩

private theorem val_input (k : ℕ) (p : List Gate) (x : List Bool)
    (hx : x.length = k) (i : ℕ) (hi : i < k) : val p x i = x.getD i false := by
  have hfold (gs : List Gate) (w : List Bool) (h : i < w.length) :
      (Circuit.mk gs i).eval w = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      let w' := w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]
      change (Circuit.mk gs i).eval w' = w.getD i false
      rw [ih w' (by simp [w']; omega)]
      exact List.getD_append _ _ _ _ h
  exact hfold p x (hx ▸ hi)

private def bitWeight (b : Bool) : Nat := b.toNat

private def weight (xs : List Bool) : Nat := (xs.map bitWeight).sum

private def tripleSum (a b c : Bool) : Bool := (a ^^ b) ^^ c

private def tripleCarry (a b c : Bool) : Bool := a ^^ ((a ^^ b) && (a ^^ c))

private def pairCarry (odd a b : Bool) : Bool :=
  if odd then (a ^^ b) ^^ (a && b) else a && b

private def compress (odd : Bool) : List Bool → List Bool
  | [] => []
  | [a] => if odd then [a] else []
  | [a, b] => [pairCarry odd a b]
  | a :: b :: c :: rest =>
      tripleCarry a b c :: compress odd (tripleSum a b c :: rest)
termination_by xs => xs.length

@[simp] private theorem weight_nil : weight [] = 0 := rfl

@[simp] private theorem weight_cons (b : Bool) (xs : List Bool) :
    weight (b :: xs) = bitWeight b + weight xs := rfl

private theorem triple_weight (a b c : Bool) :
    bitWeight a + bitWeight b + bitWeight c =
      bitWeight (tripleSum a b c) + 2 * bitWeight (tripleCarry a b c) := by
  cases a <;> cases b <;> cases c <;> decide

private theorem pair_weight (odd a b : Bool) :
    bitWeight (pairCarry odd a b) = (bitWeight a + bitWeight b + bitWeight odd) / 2 := by
  cases odd <;> cases a <;> cases b <;> decide

private theorem compress_weight (odd : Bool) (xs : List Bool) :
    weight (compress odd xs) = (weight xs + bitWeight odd) / 2 := by
  match xs with
  | [] => cases odd <;> simp [compress, bitWeight, Bool.toNat]
  | [a] => cases odd <;> cases a <;> simp [compress, bitWeight, Bool.toNat]
  | [a, b] => simpa [compress] using pair_weight odd a b
  | a :: b :: c :: rest =>
      rw [compress, weight_cons, compress_weight]
      simp only [weight_cons]
      have h := triple_weight a b c
      omega
termination_by xs.length

private theorem threshold_step (T : Nat) (xs : List Bool) :
    T ≤ weight xs ↔ (T + 1) / 2 ≤ weight (compress (decide (T % 2 = 1)) xs) := by
  rw [compress_weight]
  by_cases h : T % 2 = 1
  · simp [h, bitWeight, Bool.toNat]
    omega
  · simp [h, bitWeight, Bool.toNat]
    omega

private theorem weight_ofFn_decide {m : Nat} (p : Fin m → Prop) [DecidablePred p] :
    weight (List.ofFn fun j => decide (p j)) = (Finset.univ.filter p).card := by
  rw [weight, List.map_ofFn, List.sum_ofFn]
  simpa only [Function.comp_apply, Nat.cast_id] using
    (show (∑ j : Fin m, bitWeight (decide (p j))) = (Finset.univ.filter p).card from by
      have hb (j : Fin m) : bitWeight (decide (p j)) = if p j then 1 else 0 := by
        by_cases h : p j <;> simp [h, bitWeight]
      simp_rw [hb]
      exact Finset.sum_boole p Finset.univ)

private def affineWires {k : Nat} (v : Fin k → ZMod 2) : List (Fin k) :=
  (List.finRange k).filter (fun i => decide (v i = 1))

private theorem affineWires_length {k : Nat} (v : Fin k → ZMod 2) :
    (affineWires v).length ≤ k := by
  unfold affineWires
  simpa using List.length_filter_le (fun i => decide (v i = 1)) (List.finRange k)

private theorem add_bit (a b : ZMod 2) :
    decide (a + b = 1) = Bool.xor (decide (a = 1)) (decide (b = 1)) := by
  have h : ∀ x y : ZMod 2,
      decide (x + y = 1) = Bool.xor (decide (x = 1)) (decide (y = 1)) := by decide
  exact h a b

private theorem coeff_mul {I : Type*} (v x : I → ZMod 2) (i : I) :
    (if v i = 1 then x i else 0) = v i * x i := by
  have h : ∀ a b : ZMod 2, (if a = 1 then b else 0) = a * b := by decide
  exact h (v i) (x i)

private theorem affine_fold_list {I : Type*} (v x : I → ZMod 2) (L : List I) (e : ZMod 2) :
    (L.filter (fun i => decide (v i = 1))).foldl
      (fun a i => Bool.xor a (decide (x i = 1))) (decide (e = 1)) =
      decide (e + (L.map (fun i => v i * x i)).sum = 1) := by
  induction L generalizing e with
  | nil => simp
  | cons i L ih =>
    by_cases hi : v i = 1
    · simp only [List.filter_cons, hi, decide_true, ite_true, List.foldl_cons, List.map_cons,
        List.sum_cons, one_mul]
      rw [← add_bit, ih, add_assoc]
    · simp only [List.filter_cons, hi, decide_false, Bool.false_eq_true, ite_false,
        List.map_cons, List.sum_cons]
      rw [ih, ← coeff_mul, ite_eq_right hi, zero_add]

private theorem affine_fold {k : Nat} (v x : Fin k → ZMod 2) (e : ZMod 2) :
    (affineWires v).foldl (fun a i => Bool.xor a (decide (x i = 1))) (decide (e = 1)) =
      decide (dotProduct v x + e = 1) := by
  rw [affineWires, affine_fold_list]
  rw [← List.sum_toFinset _ (List.nodup_finRange k), List.toFinset_finRange, dotProduct, add_comm]

private theorem emitFoldXor (k : ℕ) (L : List (Fin k)) (p : List Gate) (i : ℕ)
    (hi : i < k+p.length) :
    ∃ q o, Ext k p q (2*L.length) 0 ∧ o < k+q.length ∧
      ∀ x, x.length = k → val q x o =
        L.foldl (fun a j => a ^^ val p x j.val) (val p x i) := by
  induction L generalizing p i with
  | nil =>
    exact ⟨p,i,Ext.refl k p,hi,fun _ _ => rfl⟩
  | cons j L ih =>
    obtain ⟨q,t,hpq,ht,he⟩ := emitXor k p i j.val hi (by omega)
    obtain ⟨r,o,hqr,ho,hout⟩ := ih q t ht
    have budget : 2 + 2*L.length ≤ 2*(j::L).length := by
      simp only [List.length_cons]
      omega
    refine ⟨r,o,(hpq.trans hqr).weaken budget (by simp),ho,?_⟩
    intro x hx
    rw [hout x hx, he x hx, List.foldl_cons]
    have keep (a : Fin k) : val q x a.val = val p x a.val := hpq.keep x hx a.val (by omega)
    simp only [keep]

private theorem emitAffine (k : ℕ) (p : List Gate) (v : Fin k → ZMod 2) (e : ZMod 2) :
    ∃ q o, Ext k p q (2*k+2) 0 ∧ o < k+q.length ∧
      ∀ x : Fin k → ZMod 2,
        val q (List.ofFn (fun j => decide (x j = 1))) o = decide (dotProduct v x + e = 1) := by
  obtain ⟨q,i,hpq,hi,he⟩ := emitConst k p (decide (e = 1))
  obtain ⟨r,o,hqr,ho,hout⟩ := emitFoldXor k (affineWires v) q i hi
  have budget : 2 + 2*(affineWires v).length ≤ 2*k+2 := by
    have := affineWires_length v
    omega
  refine ⟨r,o,(hpq.trans hqr).weaken budget (by simp),ho,?_⟩
  intro x
  let xs := List.ofFn (fun j => decide (x j = 1))
  have hx : xs.length = k := by simp [xs]
  rw [hout xs hx, he xs hx]
  have get (j : Fin k) : val q xs j.val = decide (x j = 1) := by
    rw [val_input k q xs hx j.val j.isLt]
    simp [xs, j.isLt]
  simpa only [get] using affine_fold v x e

private theorem emitAffineList (k m : ℕ) (p : List Gate) (v : Fin m → Fin k → ZMod 2)
    (e : Fin m → ZMod 2) :
    ∃ (q : List Gate) (ws : List Nat), Ext k p q ((2*k+2)*m) 0 ∧ ws.length = m ∧
      (∀ i ∈ ws, i < k+q.length) ∧
      ∀ x : Fin k → ZMod 2,
        ws.map (val q (List.ofFn fun j => decide (x j = 1))) =
          List.ofFn (fun j => decide (dotProduct (v j) x + e j = 1)) := by
  induction m generalizing p with
  | zero =>
    exact ⟨p,[],by simpa using Ext.refl k p,rfl,by simp,by simp⟩
  | succ m ih =>
    obtain ⟨q,i,hpq,hi,hfirst⟩ := emitAffine k p (v 0) (e 0)
    obtain ⟨r,ws,hqr,hlen,hread,htail⟩ :=
      ih q (fun j => v j.succ) (fun j => e j.succ)
    have hi' : i < k+r.length := by
      have := hqr.old_le
      omega
    have hb : 2*k+2+(2*k+2)*m ≤ (2*k+2)*(m+1) := by
      simp [Nat.mul_succ, Nat.add_comm]
    refine ⟨r,i::ws,(hpq.trans hqr).weaken hb (by simp),by simp [hlen],?_,?_⟩
    · intro j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · exact hi'
      · exact hread j hj
    · intro x
      have hx : (List.ofFn (fun j => decide (x j = 1))).length = k := by simp
      rw [List.map_cons, hqr.keep _ hx i hi, hfirst x, htail x, List.ofFn_succ]

private theorem liftIndex {k b a i : ℕ} {p q : List Gate}
    (h : Ext k p q b a) (hi : i < k + p.length) : i < k + q.length := by
  have := h.old_le
  omega

private def wireValues (p : List Gate) (x : List Bool) (xs : List ℕ) : List Bool :=
  xs.map (val p x)

private theorem keepWireValues {k gb ab : ℕ} {p q : List Gate} (h : Ext k p q gb ab)
    (x : List Bool) (hx : x.length = k) (xs : List ℕ)
    (hb : ∀ i ∈ xs, i < k + p.length) :
    wireValues q x xs = wireValues p x xs :=
  List.map_congr_left (fun i hi => h.keep x hx i (hb i hi))

private theorem emitPairCarry (k : ℕ) (p : List Gate) (odd : Bool) (a b : ℕ)
    (ha : a < k+p.length) (hb : b < k+p.length) :
    ∃ q o, Ext k p q 5 1 ∧ o < k+q.length ∧
      ∀ x, x.length = k → val q x o = pairCarry odd (val p x a) (val p x b) := by
  cases odd
  · obtain ⟨q, o, h, ho, hv⟩ := emitAnd k p a b ha hb
    exact ⟨q, o, h.weaken (by decide) le_rfl, ho, hv⟩
  · obtain ⟨p₁, u, e₁, hu, vu⟩ := emitXor k p a b ha hb
    obtain ⟨p₂, v, e₂, hv, vv⟩ :=
      emitAnd k p₁ a b (liftIndex e₁ ha) (liftIndex e₁ hb)
    obtain ⟨p₃, t, e₃, ht, vt⟩ := emitXor k p₂ u v (liftIndex e₂ hu) hv
    refine ⟨p₃, t, e₁.trans (e₂.trans e₃), ht, ?_⟩
    intro x hx
    rw [vt x hx, e₂.keep x hx u hu, vu x hx, vv x hx,
      e₁.keep x hx a ha, e₁.keep x hx b hb]
    rfl

private theorem emitTriple (k : ℕ) (p : List Gate) (a b c : ℕ)
    (ha : a < k+p.length) (hb : b < k+p.length) (hc : c < k+p.length) :
    ∃ q s t, Ext k p q 9 1 ∧ s < k+q.length ∧ t < k+q.length ∧
      ∀ x, x.length = k →
        val q x s = tripleSum (val p x a) (val p x b) (val p x c) ∧
        val q x t = tripleCarry (val p x a) (val p x b) (val p x c) := by
  obtain ⟨p₁, u, e₁, hu, vu⟩ := emitXor k p a b ha hb
  obtain ⟨p₂, v, e₂, hv, vv⟩ :=
    emitXor k p₁ a c (liftIndex e₁ ha) (liftIndex e₁ hc)
  obtain ⟨p₃, w, e₃, hw, vw⟩ := emitAnd k p₂ u v (liftIndex e₂ hu) hv
  have e₁₃ := e₁.trans (e₂.trans e₃)
  obtain ⟨p₄, t, e₄, ht, vt⟩ := emitXor k p₃ a w (liftIndex e₁₃ ha) hw
  have e₁₄ := e₁₃.trans e₄
  have e₂₄ := e₂.trans (e₃.trans e₄)
  obtain ⟨p₅, s, e₅, hs, vs⟩ := emitXor k p₄ u c (liftIndex e₂₄ hu) (liftIndex e₁₄ hc)
  refine ⟨p₅, s, t, e₁₄.trans e₅, hs, liftIndex e₅ ht, ?_⟩
  intro x hx
  constructor
  · rw [vs x hx, e₂₄.keep x hx u hu, e₁₄.keep x hx c hc, vu x hx]
    rfl
  · rw [e₅.keep x hx t ht, vt x hx, e₁₃.keep x hx a ha, vw x hx,
      e₂.keep x hx u hu, vv x hx, vu x hx, e₁.keep x hx a ha, e₁.keep x hx c hc]
    rfl

private theorem compileCompress (k : ℕ) (p : List Gate) (odd : Bool) (xs : List ℕ)
    (hx : ∀ i ∈ xs, i < k+p.length) :
    ∃ q ys, Ext k p q (9*(xs.length/2)) (xs.length/2) ∧
      ys.length ≤ (xs.length+1)/2 ∧
      (2 ≤ xs.length → 0 < ys.length) ∧
      (∀ i ∈ ys, i < k+q.length) ∧
      ∀ x, x.length = k → wireValues q x ys = compress odd (wireValues p x xs) := by
  match xs with
  | [] =>
      exact ⟨p, [], Ext.refl k p, by simp, by simp, by simp, by simp [wireValues, compress]⟩
  | [a] =>
      cases odd
      · exact ⟨p, [], by simpa using Ext.refl k p, by simp, by simp, by simp,
          by simp [wireValues, compress]⟩
      · exact ⟨p, [a], by simpa using Ext.refl k p, by simp, by simp, hx,
          by simp [wireValues, compress]⟩
  | [a, b] =>
      have ha := hx a (by simp)
      have hb := hx b (by simp)
      obtain ⟨q, o, e, ho, hv⟩ := emitPairCarry k p odd a b ha hb
      exact ⟨q, [o], e.weaken (by norm_num) (by norm_num), by simp, by simp, by simpa,
        fun x hlen => by simp [wireValues, compress, hv x hlen]⟩
  | a :: b :: c :: tail =>
      obtain ⟨q, s, t, e, hs, ht, hv⟩ :=
        emitTriple k p a b c (hx a (by simp)) (hx b (by simp)) (hx c (by simp))
      have hTail (i : ℕ) (hi : i ∈ tail) : i < k+p.length := hx i (by simp [hi])
      have hNext (i : ℕ) (hi : i ∈ s :: tail) : i < k+q.length := by
        rcases List.mem_cons.mp hi with he | hi
        · simpa [he] using hs
        · exact liftIndex e (hTail i hi)
      obtain ⟨r, ys, er, hlen, _, hy, hval⟩ := compileCompress k q odd (s :: tail) hNext
      refine ⟨r, t :: ys, (e.trans er).weaken ?_ ?_, ?_, by simp, ?_, ?_⟩
      · simp only [List.length_cons]
        omega
      · simp only [List.length_cons]
        omega
      · simp only [List.length_cons] at hlen ⊢
        omega
      · intro i hi
        rcases List.mem_cons.mp hi with he | hi
        · simpa [he] using liftIndex er ht
        · exact hy i hi
      · intro x hLen
        have hv' := hv x hLen
        simp only [wireValues, List.map_cons] at hval ⊢
        rw [compress, er.keep x hLen t ht, hv'.2, hval x hLen, hv'.1]
        change _ :: compress _ (_ :: wireValues q x tail) =
          _ :: compress _ (_ :: wireValues p x tail)
        rw [keepWireValues e x hLen tail hTail]
termination_by xs.length
decreasing_by simp only [List.length_cons]; omega

private theorem compileThreshold (k : ℕ) (p : List Gate) (xs : List ℕ) (T : ℕ)
    (hx : ∀ i ∈ xs, i < k+p.length) :
    ∃ q o, Ext k p q (9*xs.length+2) (xs.length-1) ∧ o < k+q.length ∧
      ∀ x, x.length = k → val q x o = decide (T ≤ weight (wireValues p x xs)) := by
  match xs with
  | [] =>
    obtain ⟨q, o, e, ho, hv⟩ := emitConst k p (decide (T ≤ 0))
    exact ⟨q, o, e, ho, fun x hLen => by simpa [wireValues] using hv x hLen⟩
  | [a] =>
    by_cases hT : T = 1
    · refine ⟨p, a, (Ext.refl k p).weaken (Nat.zero_le _) le_rfl, hx a (by simp), ?_⟩
      intro x _
      cases h : val p x a <;> simp [hT, wireValues, bitWeight, h]
    · obtain ⟨q, o, e, ho, hv⟩ := emitConst k p (decide (T = 0))
      refine ⟨q, o, e.weaken (by norm_num) (by norm_num), ho, ?_⟩
      intro x hLen
      rw [hv x hLen]
      cases h : val p x a <;> simp [wireValues, bitWeight, h]
      omega
  | a :: b :: tail =>
    obtain ⟨q, ys, e, hlen, hypos, hy, hval⟩ :=
      compileCompress k p (decide (T % 2 = 1)) (a :: b :: tail) hx
    have ypos := hypos (by simp)
    have ylt : ys.length < (a :: b :: tail).length := by
      simp only [List.length_cons] at hlen ⊢
      omega
    obtain ⟨r, o, er, ho, ev⟩ := compileThreshold k q ys ((T+1)/2) hy
    refine ⟨r, o, (e.trans er).weaken ?_ ?_, ho, ?_⟩
    · simp only [List.length_cons] at hlen ⊢
      omega
    · simp only [List.length_cons] at hlen ⊢
      omega
    · intro x hLen
      rw [ev x hLen, hval x hLen]
      simp only [← threshold_step T (wireValues p x (a :: b :: tail))]
termination_by xs.length
decreasing_by exact ylt

end PEqualNP.Outside.L_meta_29725

open PEqualNP.Outside.L_meta_29725 in
theorem PEqualNP.Outside.L_meta_29725 : (∀ (k m T : ℕ),
  let F := ZMod 2
  let V := Fin k → F
  ∀ (v : Fin m → V) (e : Fin m → F),
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.NestedCover.ReadsBack k C ∧
      C.output < k+C.size ∧ C.size ≤ (2*k+20)*(m+1) ∧
      (∀ g ∈ C.gates,
        (g.op = .and ∧ g.inputs.length = 2) ∨
        (g.op = .mod 2 ∧ g.inputs.length ≤ 2) ∨
        (g.op = .not ∧ g.inputs.length = 1)) ∧
      C.gates.countP (fun g => @decide (g.op = .and) (Classical.propDecidable _)) ≤ m-1 ∧
      ∀ x : V, C.eval (List.ofFn (fun i : Fin k => decide (x i = 1))) =
        decide (T ≤ ((Finset.univ : Finset (Fin m)).filter
          (fun j => dotProduct (v j) x + e j = 1)).card)) := by
  intro k m T
  dsimp only
  intro v e
  obtain ⟨p, ws, he, hlen, hws, hval⟩ := emitAffineList k m [] v e
  obtain ⟨q, o, hf, ho, hthreshold⟩ := compileThreshold k p ws T hws
  let C : PEqualNP.CircuitLowerBounds.Circuit := ⟨q, o⟩
  have hw := hf.wf (he.wf (by simp [WellFormed, PEqualNP.MetaComplexity.NestedCover.ReadsBack]))
  refine ⟨C, hw.1, ho, ?_, hw.2, ?_, ?_⟩
  · change q.length ≤ (2*k+20)*(m+1)
    have hp := he.length_le
    have hq := hf.length_le
    simp only [List.length_nil, Nat.zero_add] at hp
    rw [hlen] at hq
    simp only [Nat.mul_succ, Nat.add_mul] at hp ⊢
    omega
  · change ands q ≤ m-1
    have hp := he.ands_le
    have hq := hf.ands_le
    have hzero : ands [] = 0 := rfl
    rw [hzero, Nat.add_zero] at hp
    rw [hlen] at hq
    omega
  · intro x
    change val q _ o = _
    rw [hthreshold _ (by simp)]
    change decide (T ≤ weight (ws.map (val p _))) = _
    rw [hval, weight_ofFn_decide]
