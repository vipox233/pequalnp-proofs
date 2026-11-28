import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_30579

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents

private def b2z (b : Bool) : ZMod 2 := if b then 1 else 0

private lemma zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  match a with
  | ⟨0, _⟩ => exact Or.inl rfl
  | ⟨1, _⟩ => exact Or.inr rfl

private lemma zmod2_add_self (a : ZMod 2) : a + a = 0 := by
  rcases zmod2_cases a with rfl | rfl <;> decide

private lemma zmod2_sub_eq_add (a b : ZMod 2) : a - b = a + b := by
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl <;> decide

private lemma b2z_xor (a b : Bool) : b2z (xor a b) = b2z a + b2z b := by
  cases a <;> cases b <;> decide

private lemma b2z_decide_ne_zero (a : ZMod 2) [Decidable (a ≠ 0)] : b2z (decide (a ≠ 0)) = a := by
  rcases zmod2_cases a with rfl | rfl <;> simp [b2z]

private lemma b2z_parity_succ (m : ℕ) :
    b2z (((m + 1) % 2) == 1) = 1 + b2z ((m % 2) == 1) := by
  have h : m % 2 = 0 ∨ m % 2 = 1 := by omega
  rcases h with h0 | h1
  · have h' : (m + 1) % 2 = 1 := by omega
    rw [h0, h']; decide
  · have h' : (m + 1) % 2 = 0 := by omega
    rw [h1, h']; decide

private lemma b2z_filter_parity {α : Type*} (S : Finset α) (p : α → Bool) :
    b2z (((S.filter (fun i => p i)).card % 2) == 1) = ∑ i ∈ S, b2z (p i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [b2z]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.filter_insert]
    cases hpa : p a
    · simp only [Bool.false_eq_true, ↓reduceIte, b2z, zero_add]
      exact ih
    · simp only [↓reduceIte]
      have hna : a ∉ s.filter (fun i => p i = true) := fun h => ha (Finset.mem_filter.mp h).1
      rw [Finset.card_insert_of_notMem hna, b2z_parity_succ, ih]
      rfl

private def nonlin (g : Gate) : Bool :=
  (g.inputs.length == 2) &&
  xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
      (xor (g.op.eval [true, false]) (g.op.eval [true, true]))

private def depthsOf (width : ℕ) (gs : List Gate) : List ℕ :=
  gs.foldl (fun (ds : List ℕ) g =>
    ds ++ [(g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nonlin g).toNat])
    (List.replicate width 0)

private def wiresOf (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

private lemma depthsOf_length (width : ℕ) (gs : List Gate) :
    (depthsOf width gs).length = width + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [depthsOf]
  | append_singleton gs g ih =>
    simp only [depthsOf, List.foldl_append, List.foldl_cons, List.foldl_nil,
      List.length_append, List.length_singleton] at ih ⊢
    omega

private lemma wiresOf_length (gs : List Gate) (x : List Bool) :
    (wiresOf gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [wiresOf]
  | append_singleton gs g ih =>
    simp only [wiresOf, List.foldl_append, List.foldl_cons, List.foldl_nil,
      List.length_append, List.length_singleton] at ih ⊢
    omega

private lemma getD_append_left {α : Type*} (l₁ l₂ : List α) (i : ℕ) (d : α) (hi : i < l₁.length) :
    (l₁ ++ l₂).getD i d = l₁.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

private lemma getD_append_last {α : Type*} (l : List α) (a d : α) :
    (l ++ [a]).getD l.length d = a := by
  simp [List.getD_eq_getElem?_getD]

private lemma getD_of_ge_length {α : Type*} (l : List α) (i : ℕ) (d : α) (hi : l.length ≤ i) :
    l.getD i d = d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

private lemma oneEach_length {n m : ℕ} (x : Fin n) (y : Fin m) :
    (oneEach x y).length = n + m := by
  simp [oneEach]

private lemma b2z_unary_affine (f : Bool → Bool) :
    ∃ c0 c1 : ZMod 2, ∀ u : Bool, b2z (f u) = c0 + c1 * b2z u := by
  refine ⟨b2z (f false), b2z (f true) + b2z (f false), ?_⟩
  intro u
  cases h0 : f false <;> cases h1 : f true <;> cases u <;> simp only [h0, h1, b2z] <;> decide

private lemma b2z_binary_poly (f : Bool → Bool → Bool) :
    ∃ c0 c1 c2 : ZMod 2, ∀ u v : Bool,
      b2z (f u v) = c0 + c1 * b2z u + c2 * b2z v +
        b2z (xor (xor (f false false) (f false true)) (xor (f true false) (f true true))) *
          (b2z u * b2z v) := by
  refine ⟨b2z (f false false),
    b2z (f true false) + b2z (f false false),
    b2z (f false true) + b2z (f false false), ?_⟩
  intro u v
  cases h00 : f false false <;> cases h01 : f false true <;>
    cases h10 : f true false <;> cases h11 : f true true <;>
    cases u <;> cases v <;> simp only [h00, h01, h10, h11, b2z] <;> decide

private abbrev Quad (n : ℕ) :=
  (Fin n → ZMod 2) × (Fin n → ZMod 2) × (Fin n → ZMod 2) × (Fin n → ZMod 2)

private def evalQuad {n : ℕ} (q : Quad n) (x y : Fin n) : ZMod 2 :=
  q.1 x * q.2.1 y + q.2.2.1 x * q.2.2.2 y

private lemma circuit_depth1_decomp (n : ℕ) (gs : List Gate)
    (hfan : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    ∃ qs : List (Quad n),
      qs.length ≤ gs.countP nonlin ∧
      (∀ idx : ℕ, (depthsOf (n + n) gs).getD idx 0 = 0 →
        ∃ α β : Fin n → ZMod 2,
          ∀ x y : Fin n, b2z ((wiresOf gs (oneEach x y)).getD idx false) = α x + β y) ∧
      (∀ idx : ℕ, (depthsOf (n + n) gs).getD idx 0 ≤ 1 →
        ∃ (mask : Fin qs.length → ZMod 2) (α β : Fin n → ZMod 2),
          ∀ x y : Fin n, b2z ((wiresOf gs (oneEach x y)).getD idx false) =
            α x + β y + ∑ p : Fin qs.length, mask p * evalQuad (qs.get p) x y) := by
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨[], by simp, ?_, ?_⟩
    · intro idx _
      by_cases h1 : idx < n
      · refine ⟨fun x => b2z (decide (x.val = idx)), fun _ => 0, fun x y => ?_⟩
        simp only [wiresOf, List.foldl_nil, oneEach, add_zero]
        have hlen : (List.ofFn (fun i : Fin n => decide (i = x))).length = n := by simp
        rw [getD_append_left _ _ _ _ (by omega)]
        simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos h1, Option.getD_some]
        have hiff : ((⟨idx, h1⟩ : Fin n) = x) ↔ x.val = idx := by
          constructor
          · intro h; rw [← h]
          · intro h; exact Fin.ext h.symm
        simp [hiff]
      · by_cases h2 : idx < n + n
        · refine ⟨fun _ => 0, fun y => b2z (decide (y.val = idx - n)), fun x y => ?_⟩
          simp only [wiresOf, List.foldl_nil, oneEach, zero_add]
          have hlen1 : (List.ofFn (fun i : Fin n => decide (i = x))).length = n := by simp
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [hlen1]; omega)]
          simp only [hlen1, List.getElem?_ofFn, dif_pos (by omega : idx - n < n), Option.getD_some]
          have hiff : ((⟨idx - n, by omega⟩ : Fin n) = y) ↔ y.val = idx - n := by
            constructor
            · intro h; rw [← h]
            · intro h; exact Fin.ext h.symm
          simp [hiff]
        · refine ⟨fun _ => 0, fun _ => 0, fun x y => ?_⟩
          simp only [wiresOf, List.foldl_nil, add_zero]
          rw [getD_of_ge_length _ _ _ (by rw [oneEach_length]; omega)]
          rfl
    · intro idx _
      by_cases h1 : idx < n
      · refine ⟨Fin.elim0, fun x => b2z (decide (x.val = idx)), fun _ => 0, fun x y => ?_⟩
        simp only [wiresOf, List.foldl_nil, oneEach, Finset.univ_eq_empty, Finset.sum_empty, add_zero]
        have hlen : (List.ofFn (fun i : Fin n => decide (i = x))).length = n := by simp
        rw [getD_append_left _ _ _ _ (by omega)]
        simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos h1, Option.getD_some]
        have hiff : ((⟨idx, h1⟩ : Fin n) = x) ↔ x.val = idx := by
          constructor
          · intro h; rw [← h]
          · intro h; exact Fin.ext h.symm
        simp [hiff]
      · by_cases h2 : idx < n + n
        · refine ⟨Fin.elim0, fun _ => 0, fun y => b2z (decide (y.val = idx - n)), fun x y => ?_⟩
          simp only [wiresOf, List.foldl_nil, oneEach, Finset.univ_eq_empty, Finset.sum_empty,
            zero_add, add_zero]
          have hlen1 : (List.ofFn (fun i : Fin n => decide (i = x))).length = n := by simp
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [hlen1]; omega)]
          simp only [hlen1, List.getElem?_ofFn, dif_pos (by omega : idx - n < n), Option.getD_some]
          have hiff : ((⟨idx - n, by omega⟩ : Fin n) = y) ↔ y.val = idx - n := by
            constructor
            · intro h; rw [← h]
            · intro h; exact Fin.ext h.symm
          simp [hiff]
        · refine ⟨Fin.elim0, fun _ => 0, fun _ => 0, fun x y => ?_⟩
          simp only [wiresOf, List.foldl_nil, Finset.univ_eq_empty, Finset.sum_empty, add_zero]
          rw [getD_of_ge_length _ _ _ (by rw [oneEach_length]; omega)]
          rfl
  | append_singleton gs g ih =>
    have hfan_gs : ∀ g' ∈ gs, g'.inputs.length ≤ 2 :=
      fun g' hg' => hfan g' (List.mem_append_left _ hg')
    have hfan_g : g.inputs.length ≤ 2 := hfan g (List.mem_append_right _ List.mem_cons_self)
    rcases ih hfan_gs with ⟨qs, hqs_len, ih0, ih1⟩
    set curLen := (n + n) + gs.length
    have hd_len : (depthsOf (n + n) gs).length = curLen := depthsOf_length (n + n) gs
    have hw_len : ∀ x y : Fin n, (wiresOf gs (oneEach x y)).length = curLen := fun x y => by
      rw [wiresOf_length, oneEach_length]
    have hd_step : depthsOf (n + n) (gs ++ [g]) =
        depthsOf (n + n) gs ++
          [(g.inputs.map (fun a => (depthsOf (n + n) gs).getD a 0)).foldr max 0 + (nonlin g).toNat] := by
      simp [depthsOf, List.foldl_append]
    have hw_step : ∀ x y : Fin n, wiresOf (gs ++ [g]) (oneEach x y) =
        wiresOf gs (oneEach x y) ++
          [g.op.eval (g.inputs.map fun i => (wiresOf gs (oneEach x y)).getD i false)] := by
      intro x y; simp [wiresOf, List.foldl_append]
    have hcount : (gs ++ [g]).countP nonlin = gs.countP nonlin + (nonlin g).toNat := by
      rw [List.countP_append, List.countP_cons, List.countP_nil]
      cases nonlin g <;> simp
    let d_in := (g.inputs.map (fun a => (depthsOf (n + n) gs).getD a 0)).foldr max 0
    have hd_new : (depthsOf (n + n) (gs ++ [g])).getD curLen 0 = d_in + (nonlin g).toNat := by
      rw [hd_step, ← hd_len, getD_append_last]
    have hw_new : ∀ x y : Fin n,
        (wiresOf (gs ++ [g]) (oneEach x y)).getD curLen false =
          g.op.eval (g.inputs.map fun i => (wiresOf gs (oneEach x y)).getD i false) := by
      intro x y
      rw [hw_step x y, ← hw_len x y, getD_append_last]
    have hd_old : ∀ idx < curLen,
        (depthsOf (n + n) (gs ++ [g])).getD idx 0 = (depthsOf (n + n) gs).getD idx 0 := by
      intro idx hlt
      rw [hd_step, getD_append_left _ _ _ _ (by omega)]
    have hw_old : ∀ idx < curLen, ∀ x y : Fin n,
        (wiresOf (gs ++ [g]) (oneEach x y)).getD idx false =
          (wiresOf gs (oneEach x y)).getD idx false := by
      intro idx hlt x y
      rw [hw_step x y, getD_append_left _ _ _ _ (by rw [hw_len x y]; omega)]
    have hw_hi : ∀ idx, curLen < idx → ∀ x y : Fin n,
        (wiresOf (gs ++ [g]) (oneEach x y)).getD idx false = false := by
      intro idx hgt x y
      rw [getD_of_ge_length _ _ _ (by rw [wiresOf_length, oneEach_length, List.length_append, List.length_singleton]; omega)]
    cases hnl : nonlin g
    · refine ⟨qs, by rw [hcount, hnl]; simp; exact hqs_len, ?_, ?_⟩
      · intro idx hdep0
        by_cases hlt : idx < curLen
        · rw [hd_old idx hlt] at hdep0
          rcases ih0 idx hdep0 with ⟨α, β, hαβ⟩
          exact ⟨α, β, fun x y => by rw [hw_old idx hlt x y, hαβ x y]⟩
        · by_cases hgt : curLen < idx
          · exact ⟨fun _ => 0, fun _ => 0, fun x y => by rw [hw_hi idx hgt x y]; simp [b2z]⟩
          · have heq : idx = curLen := by omega
            subst heq
            rw [hd_new, hnl] at hdep0
            simp only [Bool.toNat_false, add_zero] at hdep0
            rcases hgs_in : g.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
            · refine ⟨fun _ => b2z (g.op.eval []), fun _ => 0, fun x y => ?_⟩
              rw [hw_new x y, hgs_in]; simp
            · have ha0 : (depthsOf (n + n) gs).getD a 0 = 0 := by
                simp only [d_in, hgs_in, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil] at hdep0
                omega
              rcases ih0 a ha0 with ⟨α, β, hαβ⟩
              rcases b2z_unary_affine (fun u => g.op.eval [u]) with ⟨c0, c1, haff⟩
              refine ⟨fun x => c0 + c1 * α x, fun y => c1 * β y, fun x y => ?_⟩
              rw [hw_new x y, hgs_in, List.map_cons, List.map_nil, haff, hαβ x y]
              ring
            · have hab0 : max ((depthsOf (n + n) gs).getD a 0) ((depthsOf (n + n) gs).getD b 0) = 0 := by
                simp only [d_in, hgs_in, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil] at hdep0
                omega
              have ha0 : (depthsOf (n + n) gs).getD a 0 = 0 := by omega
              have hb0 : (depthsOf (n + n) gs).getD b 0 = 0 := by omega
              rcases ih0 a ha0 with ⟨α1, β1, h1⟩
              rcases ih0 b hb0 with ⟨α2, β2, h2⟩
              rcases b2z_binary_poly (fun u v => g.op.eval [u, v]) with ⟨c0, c1, c2, hpoly⟩
              have hnl0 : xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
                  (xor (g.op.eval [true, false]) (g.op.eval [true, true])) = false := by
                cases h : xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
                    (xor (g.op.eval [true, false]) (g.op.eval [true, true]))
                · rfl
                · simp [nonlin, hgs_in, h] at hnl
              refine ⟨fun x => c0 + c1 * α1 x + c2 * α2 x, fun y => c1 * β1 y + c2 * β2 y, fun x y => ?_⟩
              rw [hw_new x y, hgs_in, List.map_cons, List.map_cons, List.map_nil, hpoly, hnl0, h1 x y, h2 x y]
              simp only [b2z, Bool.false_eq_true, ↓reduceIte, zero_mul, add_zero]
              ring
            · rw [hgs_in] at hfan_g; simp at hfan_g
      · intro idx hdep1
        by_cases hlt : idx < curLen
        · rw [hd_old idx hlt] at hdep1
          rcases ih1 idx hdep1 with ⟨mask, α, β, hαβ⟩
          exact ⟨mask, α, β, fun x y => by rw [hw_old idx hlt x y, hαβ x y]⟩
        · by_cases hgt : curLen < idx
          · exact ⟨fun _ => 0, fun _ => 0, fun _ => 0, fun x y => by rw [hw_hi idx hgt x y]; simp [b2z]⟩
          · have heq : idx = curLen := by omega
            subst heq
            rw [hd_new, hnl] at hdep1
            simp only [Bool.toNat_false, add_zero] at hdep1
            rcases hgs_in : g.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
            · refine ⟨fun _ => 0, fun _ => b2z (g.op.eval []), fun _ => 0, fun x y => ?_⟩
              rw [hw_new x y, hgs_in]; simp
            · have ha1 : (depthsOf (n + n) gs).getD a 0 ≤ 1 := by
                simp only [d_in, hgs_in, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil] at hdep1
                omega
              rcases ih1 a ha1 with ⟨m1, α1, β1, h1⟩
              rcases b2z_unary_affine (fun u => g.op.eval [u]) with ⟨c0, c1, haff⟩
              refine ⟨fun p => c1 * m1 p, fun x => c0 + c1 * α1 x, fun y => c1 * β1 y, fun x y => ?_⟩
              rw [hw_new x y, hgs_in, List.map_cons, List.map_nil, haff, h1 x y]
              simp only [mul_assoc, ← Finset.mul_sum]
              ring
            · have hab1 : max ((depthsOf (n + n) gs).getD a 0) ((depthsOf (n + n) gs).getD b 0) ≤ 1 := by
                simp only [d_in, hgs_in, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil] at hdep1
                omega
              have ha1 : (depthsOf (n + n) gs).getD a 0 ≤ 1 := by omega
              have hb1 : (depthsOf (n + n) gs).getD b 0 ≤ 1 := by omega
              rcases ih1 a ha1 with ⟨m1, α1, β1, h1⟩
              rcases ih1 b hb1 with ⟨m2, α2, β2, h2⟩
              rcases b2z_binary_poly (fun u v => g.op.eval [u, v]) with ⟨c0, c1, c2, hpoly⟩
              have hnl0 : xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
                  (xor (g.op.eval [true, false]) (g.op.eval [true, true])) = false := by
                cases h : xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
                    (xor (g.op.eval [true, false]) (g.op.eval [true, true]))
                · rfl
                · simp [nonlin, hgs_in, h] at hnl
              refine ⟨fun p => c1 * m1 p + c2 * m2 p,
                fun x => c0 + c1 * α1 x + c2 * α2 x, fun y => c1 * β1 y + c2 * β2 y, fun x y => ?_⟩
              rw [hw_new x y, hgs_in, List.map_cons, List.map_cons, List.map_nil, hpoly, hnl0, h1 x y, h2 x y]
              simp only [b2z, Bool.false_eq_true, ↓reduceIte, zero_mul, add_zero]
              have hsum_eq : ∑ p : Fin qs.length, (c1 * m1 p + c2 * m2 p) * evalQuad (qs.get p) x y =
                  c1 * (∑ p : Fin qs.length, m1 p * evalQuad (qs.get p) x y) +
                  c2 * (∑ p : Fin qs.length, m2 p * evalQuad (qs.get p) x y) := by
                simp only [add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
              rw [hsum_eq]
              ring
            · rw [hgs_in] at hfan_g; simp at hfan_g
    · have hlen2 : g.inputs.length = 2 := by
        simp only [nonlin, Bool.and_eq_true, beq_iff_eq] at hnl
        exact hnl.1
      have hnl1 : xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
          (xor (g.op.eval [true, false]) (g.op.eval [true, true])) = true := by
        simp only [nonlin, Bool.and_eq_true, beq_iff_eq] at hnl
        exact hnl.2
      by_cases hdin0 : d_in = 0
      · rcases hgs_in : g.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
        · simp [hgs_in] at hlen2
        · simp [hgs_in] at hlen2
        · have hab0 : max ((depthsOf (n + n) gs).getD a 0) ((depthsOf (n + n) gs).getD b 0) = 0 := by
            simp only [d_in, hgs_in, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil] at hdin0
            omega
          have ha0 : (depthsOf (n + n) gs).getD a 0 = 0 := by omega
          have hb0 : (depthsOf (n + n) gs).getD b 0 = 0 := by omega
          rcases ih0 a ha0 with ⟨α1, β1, h1⟩
          rcases ih0 b hb0 with ⟨α2, β2, h2⟩
          rcases b2z_binary_poly (fun u v => g.op.eval [u, v]) with ⟨c0, c1, c2, hpoly⟩
          let qNew : Quad n := (α1, β2, α2, β1)
          let qs' := qs ++ [qNew]
          have hqs'_len : qs'.length = qs.length + 1 := by simp [qs']
          refine ⟨qs', by rw [hcount, hnl, hqs'_len]; simp; exact hqs_len, ?_, ?_⟩
          · intro idx hdep0
            by_cases hlt : idx < curLen
            · rw [hd_old idx hlt] at hdep0
              rcases ih0 idx hdep0 with ⟨α, β, hαβ⟩
              exact ⟨α, β, fun x y => by rw [hw_old idx hlt x y, hαβ x y]⟩
            · by_cases hgt : curLen < idx
              · exact ⟨fun _ => 0, fun _ => 0, fun x y => by rw [hw_hi idx hgt x y]; simp [b2z]⟩
              · have heq : idx = curLen := by omega
                subst heq
                rw [hd_new, hnl] at hdep0
                simp at hdep0
          · intro idx hdep1
            by_cases hlt : idx < curLen
            · rw [hd_old idx hlt] at hdep1
              rcases ih1 idx hdep1 with ⟨mask, α, β, hαβ⟩
              let mask' : Fin qs'.length → ZMod 2 := fun p =>
                if hp : p.val < qs.length then mask ⟨p.val, hp⟩ else 0
              refine ⟨mask', α, β, fun x y => ?_⟩
              rw [hw_old idx hlt x y, hαβ x y]
              congr 1
              have hsum_eq : ∑ p : Fin qs'.length, mask' p * evalQuad (qs'.get p) x y =
                  ∑ p : Fin qs.length, mask p * evalQuad (qs.get p) x y := by
                have hfin : ∑ p : Fin (qs.length + 1),
                    mask' ⟨p.val, by omega⟩ * evalQuad (qs'.get ⟨p.val, by omega⟩) x y =
                    ∑ p : Fin qs'.length, mask' p * evalQuad (qs'.get p) x y :=
                  Finset.sum_bij (fun p _ => ⟨p.val, by omega⟩) (fun _ _ => Finset.mem_univ _)
                    (fun _ _ _ _ h => Fin.ext (Fin.mk.inj h))
                    (fun p _ => ⟨⟨p.val, by omega⟩, Finset.mem_univ _, Fin.ext rfl⟩)
                    (fun _ _ => rfl)
                rw [← hfin, Fin.sum_univ_castSucc]
                have hlast : mask' ⟨(Fin.last qs.length).val, by omega⟩ = 0 := by simp [mask']
                rw [hlast, zero_mul, add_zero]
                refine Finset.sum_congr rfl fun p _ => ?_
                have hget : qs'.get ⟨p.val, by omega⟩ = qs.get p := by
                  simp [qs', List.get_eq_getElem, List.getElem_append_left p.isLt]
                change mask' ⟨p.val, by omega⟩ * evalQuad (qs'.get ⟨p.val, by omega⟩) x y =
                  mask p * evalQuad (qs.get p) x y
                rw [hget]
                simp [mask', p.isLt]
              exact hsum_eq.symm
            · by_cases hgt : curLen < idx
              · exact ⟨fun _ => 0, fun _ => 0, fun _ => 0, fun x y => by rw [hw_hi idx hgt x y]; simp [b2z]⟩
              · have heq : idx = curLen := by omega
                subst heq
                let pLast : Fin qs'.length := ⟨qs.length, by omega⟩
                refine ⟨fun p => if p = pLast then 1 else 0,
                  fun x => c0 + c1 * α1 x + c2 * α2 x + α1 x * α2 x,
                  fun y => c1 * β1 y + c2 * β2 y + β1 y * β2 y, fun x y => ?_⟩
                rw [hw_new x y, hgs_in, List.map_cons, List.map_cons, List.map_nil, hpoly, hnl1, h1 x y, h2 x y]
                have hsum_single : ∑ p : Fin qs'.length,
                    (if p = pLast then (1 : ZMod 2) else 0) * evalQuad (qs'.get p) x y =
                    evalQuad qNew x y := by
                  rw [Finset.sum_eq_single pLast]
                  · simp only [↓reduceIte, one_mul]
                    have hget : qs'.get pLast = qNew := by
                      simp [qs', pLast, List.get_eq_getElem]
                    rw [hget]
                  · intro p _ hne
                    simp [hne]
                  · intro h; exact (h (Finset.mem_univ pLast)).elim
                rw [hsum_single]
                simp only [b2z, ↓reduceIte, one_mul, evalQuad, qNew]
                ring
        · simp [hgs_in] at hlen2
      · refine ⟨qs, by rw [hcount, hnl]; simp; omega, ?_, ?_⟩
        · intro idx hdep0
          by_cases hlt : idx < curLen
          · rw [hd_old idx hlt] at hdep0
            rcases ih0 idx hdep0 with ⟨α, β, hαβ⟩
            exact ⟨α, β, fun x y => by rw [hw_old idx hlt x y, hαβ x y]⟩
          · by_cases hgt : curLen < idx
            · exact ⟨fun _ => 0, fun _ => 0, fun x y => by rw [hw_hi idx hgt x y]; simp [b2z]⟩
            · have heq : idx = curLen := by omega
              subst heq
              rw [hd_new, hnl] at hdep0
              simp at hdep0
        · intro idx hdep1
          by_cases hlt : idx < curLen
          · rw [hd_old idx hlt] at hdep1
            rcases ih1 idx hdep1 with ⟨mask, α, β, hαβ⟩
            exact ⟨mask, α, β, fun x y => by rw [hw_old idx hlt x y, hαβ x y]⟩
          · by_cases hgt : curLen < idx
            · exact ⟨fun _ => 0, fun _ => 0, fun _ => 0, fun x y => by rw [hw_hi idx hgt x y]; simp [b2z]⟩
            · have heq : idx = curLen := by omega
              subst heq
              rw [hd_new, hnl] at hdep1
              simp only [Bool.toNat_true] at hdep1
              omega

private def deltaMat {k : ℕ} (f : Fin (k + 1) → Fin (k + 1) → ZMod 2)
    (i j : Fin k) : ZMod 2 :=
  f i.succ j.succ + f i.succ 0 + f 0 j.succ + f 0 0

private lemma deltaMat_add {k : ℕ} (f g : Fin (k + 1) → Fin (k + 1) → ZMod 2) (i j : Fin k) :
    deltaMat (fun x y => f x y + g x y) i j = deltaMat f i j + deltaMat g i j := by
  simp only [deltaMat]; ring

private lemma deltaMat_aff {k : ℕ} (α β : Fin (k + 1) → ZMod 2) (i j : Fin k) :
    deltaMat (fun x y => α x + β y) i j = 0 := by
  simp only [deltaMat]
  have h1 : α i.succ + β j.succ + (α i.succ + β 0) + (α 0 + β j.succ) + (α 0 + β 0) =
      (α i.succ + α i.succ) + (α 0 + α 0) + (β j.succ + β j.succ) + (β 0 + β 0) := by ring
  rw [h1]
  simp only [zmod2_add_self, add_zero]

private lemma deltaMat_outer {k : ℕ} (u v : Fin (k + 1) → ZMod 2) (i j : Fin k) :
    deltaMat (fun x y => u x * v y) i j = (u i.succ + u 0) * (v j.succ + v 0) := by
  simp only [deltaMat]; ring

private lemma deltaMat_quad {k : ℕ} (q : Quad (k + 1)) (i j : Fin k) :
    deltaMat (evalQuad q) i j =
      (q.1 i.succ + q.1 0) * (q.2.1 j.succ + q.2.1 0) +
      (q.2.2.1 i.succ + q.2.2.1 0) * (q.2.2.2 j.succ + q.2.2.2 0) := by
  unfold evalQuad
  rw [deltaMat_add, deltaMat_outer, deltaMat_outer]

private lemma deltaMat_sum {k : ℕ} {ι : Type*} (s : Finset ι)
    (f : ι → Fin (k + 1) → Fin (k + 1) → ZMod 2) (i j : Fin k) :
    deltaMat (fun x y => ∑ p ∈ s, f p x y) i j = ∑ p ∈ s, deltaMat (f p) i j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [deltaMat]
  | insert a t ha ih =>
    simp only [Finset.sum_insert ha]
    rw [deltaMat_add, ih]

private lemma deltaMat_smul {k : ℕ} (c : ZMod 2) (f : Fin (k + 1) → Fin (k + 1) → ZMod 2)
    (i j : Fin k) :
    deltaMat (fun x y => c * f x y) i j = c * deltaMat f i j := by
  simp only [deltaMat]; ring

private def quadToPairs {k : ℕ} (q : Quad (k + 1)) :
    List ((Fin k → ZMod 2) × (Fin k → ZMod 2)) :=
  [(fun i => q.1 i.succ + q.1 0, fun j => q.2.1 j.succ + q.2.1 0),
   (fun i => q.2.2.1 i.succ + q.2.2.1 0, fun j => q.2.2.2 j.succ + q.2.2.2 0)]

private lemma sum_fin_list {α β : Type*} [AddCommMonoid β] (l : List α) (f : α → β) :
    (∑ r : Fin l.length, f (l.get r)) = (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have h1 : (∑ r : Fin (a :: t).length, f ((a :: t).get r)) =
        ∑ r : Fin (t.length + 1), f ((a :: t).get r) := rfl
    rw [h1, Fin.sum_univ_succ, List.map_cons, List.sum_cons, ← ih]
    rfl

private lemma card_filter_add_not {α : Type*} (s : Finset α) (p : α → Prop) [DecidablePred p] :
    (s.filter p).card + (s.filter (fun x => ¬ p x)).card = s.card := by
  rw [Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
  have h : ∀ x ∈ s, (if p x then 1 else 0) + (if ¬ p x then 1 else 0) = 1 := by
    intro x _
    by_cases hx : p x <;> simp [hx]
  rw [Finset.sum_congr rfl h]
  simp

private lemma sum_quad_mask_as_pairs {k : ℕ} (qs : List (Quad (k + 1)))
    (mask : Fin qs.length → ZMod 2) :
    ∃ pairs : List ((Fin k → ZMod 2) × (Fin k → ZMod 2)),
      pairs.length = 2 * (Finset.univ.filter (fun p : Fin qs.length => mask p ≠ 0)).card ∧
      ∀ i j : Fin k,
        (∑ p : Fin qs.length, mask p * deltaMat (evalQuad (qs.get p)) i j) =
          ∑ r : Fin pairs.length, (pairs.get r).1 i * (pairs.get r).2 j := by
  classical
  let act : List (Fin qs.length) := (List.finRange qs.length).filter (fun p => decide (mask p ≠ 0))
  let pairs : List ((Fin k → ZMod 2) × (Fin k → ZMod 2)) :=
    act.flatMap (fun p => quadToPairs (qs.get p))
  have hact_nodup : act.Nodup := (List.nodup_finRange qs.length).filter _
  have hact_len : act.length = (Finset.univ.filter (fun p : Fin qs.length => mask p ≠ 0)).card := by
    rw [← List.toFinset_card_of_nodup hact_nodup]
    congr 1
    ext p
    simp [act]
  have hpairs_len : pairs.length = 2 * act.length := by
    have hflat : ∀ l : List (Fin qs.length), (l.flatMap (fun p => quadToPairs (qs.get p))).length = 2 * l.length := by
      intro l
      induction l with
      | nil => simp
      | cons a t ih => simp [quadToPairs, ih]; omega
    exact hflat act
  refine ⟨pairs, by rw [hpairs_len, hact_len], ?_⟩
  intro i j
  rw [sum_fin_list pairs (fun ab => ab.1 i * ab.2 j)]
  have hflat_sum : ∀ l : List (Fin qs.length),
      ((l.flatMap (fun p => quadToPairs (qs.get p))).map (fun ab => ab.1 i * ab.2 j)).sum =
        (l.map (fun p => deltaMat (evalQuad (qs.get p)) i j)).sum := by
    intro l
    induction l with
    | nil => simp
    | cons a t ih =>
      rw [List.flatMap_cons, List.map_append, List.sum_append, ih, List.map_cons, List.sum_cons]
      simp only [quadToPairs, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, deltaMat_quad]
  rw [hflat_sum]
  have hsum_nodup : (act.map (fun p => deltaMat (evalQuad (qs.get p)) i j)).sum =
      ∑ p ∈ act.toFinset, deltaMat (evalQuad (qs.get p)) i j := by
    rw [List.sum_toFinset _ hact_nodup]
  rw [hsum_nodup]
  have hset_eq : act.toFinset = Finset.univ.filter (fun p : Fin qs.length => mask p ≠ 0) := by
    ext p; simp [act]
  rw [hset_eq]
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin qs.length)) (fun p => mask p ≠ 0)]
  have hzero : ∑ p ∈ Finset.univ.filter (fun p : Fin qs.length => ¬ mask p ≠ 0),
      mask p * deltaMat (evalQuad (qs.get p)) i j = 0 := by
    apply Finset.sum_eq_zero
    intro p hp
    have h0 : mask p = 0 := not_not.mp (Finset.mem_filter.mp hp).2
    rw [h0, zero_mul]
  rw [hzero, add_zero]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hne : mask p ≠ 0 := (Finset.mem_filter.mp hp).2
  rcases zmod2_cases (mask p) with h0 | h1
  · exact (hne h0).elim
  · rw [h1, one_mul]

private lemma row_inj_le_outer_len {k : ℕ} (A : Fin k → Fin k → ZMod 2)
    (hinj : ∀ v : Fin k → ZMod 2, (∀ j, ∑ i : Fin k, v i * A i j = 0) → v = 0)
    (terms : List ((Fin k → ZMod 2) × (Fin k → ZMod 2)))
    (hA : ∀ i j, A i j = ∑ p : Fin terms.length, (terms.get p).1 i * (terms.get p).2 j) :
    k ≤ terms.length := by
  let Φ : (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin terms.length → ZMod 2) :=
    { toFun := fun v p => ∑ i : Fin k, v i * (terms.get p).1 i
      map_add' := fun v w => by funext p; simp [add_mul, Finset.sum_add_distrib]
      map_smul' := fun c v => by funext p; simp [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc] }
  have hΦ : Function.Injective Φ := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    apply hinj v
    intro j
    have h1 : ∑ i : Fin k, v i * A i j =
        ∑ p : Fin terms.length, (∑ i : Fin k, v i * (terms.get p).1 i) * (terms.get p).2 j := by
      simp_rw [hA, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => by ring
    rw [h1]
    apply Finset.sum_eq_zero
    intro p _
    have hp : (∑ i : Fin k, v i * (terms.get p).1 i) = 0 := congr_fun hv p
    rw [hp, zero_mul]
  have hle := LinearMap.finrank_le_finrank_of_injective hΦ
  simpa [Module.finrank_pi] using hle

private lemma mult_mat_row_inj {K : Type} [Field K] [Algebra (ZMod 2) K] [FiniteDimensional (ZMod 2) K]
    {k : ℕ} (basis : Module.Basis (Fin k) (ZMod 2) K) (bit : K →ₗ[ZMod 2] ZMod 2)
    (hbit : bit ≠ 0) (w : K) (hw : w ≠ 0) :
    ∀ v : Fin k → ZMod 2,
      (∀ j : Fin k, ∑ i : Fin k, v i * bit (w * basis i * basis j) = 0) → v = 0 := by
  intro v hv
  let x : K := ∑ i : Fin k, v i • basis i
  have hbx : ∀ j : Fin k, bit (w * x * basis j) = 0 := by
    intro j
    have heq : w * x * basis j = ∑ i : Fin k, v i • (w * basis i * basis j) := by
      simp only [x, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
    rw [heq, map_sum]
    simpa only [map_smul, smul_eq_mul] using hv j
  have hball : ∀ y : K, bit (w * x * y) = 0 := by
    intro y
    have hy := (basis.sum_repr y).symm
    have heq : w * x * y = ∑ j : Fin k, basis.repr y j • (w * x * basis j) := by
      conv_lhs => rw [hy]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Algebra.mul_smul_comm]
    rw [heq, map_sum]
    apply Finset.sum_eq_zero
    intro j _
    rw [map_smul, hbx j, smul_zero]
  have hwx : w * x = 0 := by
    by_contra hne
    have hex : ∃ a : K, bit a ≠ 0 := by
      by_contra hall
      apply hbit
      apply LinearMap.ext
      intro a
      by_contra ha
      exact hall ⟨a, ha⟩
    rcases hex with ⟨a, ha⟩
    have h0 := hball ((w * x)⁻¹ * a)
    rw [← mul_assoc, mul_inv_cancel₀ hne, one_mul] at h0
    exact ha h0
  have hx0 : x = 0 := (mul_eq_zero.mp hwx).resolve_left hw
  have hli := (Fintype.linearIndependent_iff.mp basis.linearIndependent) v hx0
  funext i
  exact hli i

private def hdist {N : ℕ} (a b : Fin N → ZMod 2) : ℕ :=
  (Finset.univ.filter (fun p : Fin N => a p ≠ b p)).card

private lemma cauchy_sq_nat {N : ℕ} (f : Fin N → ℕ) :
    (∑ p : Fin N, f p) ^ 2 ≤ N * ∑ p : Fin N, (f p) ^ 2 := by
  have hz : ((∑ p : Fin N, (f p : ℤ)) ^ 2 : ℤ) ≤ (N : ℤ) * ∑ p : Fin N, (f p : ℤ) ^ 2 := by
    have hnonneg : (0 : ℤ) ≤ ∑ p : Fin N, ∑ q : Fin N, ((f p : ℤ) - (f q : ℤ)) ^ 2 :=
      Finset.sum_nonneg fun p _ => Finset.sum_nonneg fun q _ => sq_nonneg _
    have hexp : ∑ p : Fin N, ∑ q : Fin N, ((f p : ℤ) - (f q : ℤ)) ^ 2 =
        2 * ((N : ℤ) * ∑ p : Fin N, (f p : ℤ) ^ 2 - (∑ p : Fin N, (f p : ℤ)) ^ 2) := by
      have h1 : ∀ p q : Fin N, ((f p : ℤ) - (f q : ℤ)) ^ 2 =
          (f p : ℤ) ^ 2 + (f q : ℤ) ^ 2 - 2 * ((f p : ℤ) * (f q : ℤ)) := fun p q => by ring
      simp_rw [h1, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum, ← Finset.sum_mul]
      ring
    linarith
  exact_mod_cast hz

private lemma johnson_shell_bound {N r d : ℕ}
    (C : Finset (Fin N → ZMod 2))
    (hdist_min : ∀ a ∈ C, ∀ b ∈ C, a ≠ b → d ≤ hdist a b)
    (c : Fin N → ZMod 2)
    (hr : r ≤ N) :
    let S := C.filter (fun a => hdist a c = r)
    S.card * (N * d - 2 * r * (N - r)) ≤ N * d := by
  classical
  intro S
  set M := S.card
  by_cases hM0 : M = 0
  · simp [hM0]
  let Dtot : ℕ := ∑ a ∈ S, ∑ b ∈ S, hdist a b
  have hlower : M * M * d ≤ Dtot + M * d := by
    have hpair : ∀ a ∈ S, ∀ b ∈ S, d ≤ hdist a b + (if a = b then d else 0) := by
      intro a ha b hb
      by_cases hab : a = b
      · subst hab; simp
      · simp only [hab, ↓reduceIte, add_zero]
        exact hdist_min a (Finset.mem_filter.mp ha).1 b (Finset.mem_filter.mp hb).1 hab
    have hsum1 : ∑ a ∈ S, ∑ b ∈ S, d ≤ ∑ a ∈ S, ∑ b ∈ S, (hdist a b + if a = b then d else 0) :=
      Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun b hb => hpair a ha b hb
    have hlhs : ∑ a ∈ S, ∑ b ∈ S, d = M * M * d := by
      simp [M, mul_assoc]
    have hdiag : ∑ a ∈ S, ∑ b ∈ S, (if a = b then d else 0) = M * d := by
      have hinner : ∀ a ∈ S, ∑ b ∈ S, (if a = b then d else 0) = d := fun a ha => by
        rw [Finset.sum_eq_single a]
        · simp
        · intro b _ hba; simp [Ne.symm hba]
        · intro h; exact (h ha).elim
      rw [Finset.sum_congr rfl hinner]
      simp [M]
    simp only [Finset.sum_add_distrib] at hsum1
    rw [hlhs, hdiag] at hsum1
    exact hsum1
  let kp : Fin N → ℕ := fun p => (S.filter (fun a => a p ≠ c p)).card
  have hkp_le : ∀ p : Fin N, kp p ≤ M := fun p => Finset.card_le_card (Finset.filter_subset _ _)
  have hkp_sum : ∑ p : Fin N, kp p = M * r := by
    have h1 : ∑ p : Fin N, kp p = ∑ p : Fin N, ∑ a ∈ S, if a p ≠ c p then 1 else 0 := by
      refine Finset.sum_congr rfl fun p _ => ?_
      dsimp only [kp]
      rw [Finset.card_filter]
    rw [h1, Finset.sum_comm]
    have h2 : ∀ a ∈ S, (∑ p : Fin N, if a p ≠ c p then 1 else 0) = r := fun a ha => by
      have hcard : (∑ p : Fin N, if a p ≠ c p then 1 else 0) = hdist a c := by
        rw [hdist, Finset.card_filter]
      rw [hcard]
      exact (Finset.mem_filter.mp ha).2
    rw [Finset.sum_congr rfl h2]
    simp [M]
  have hDtot_eq : Dtot = ∑ p : Fin N, 2 * kp p * (M - kp p) := by
    have h1 : Dtot = ∑ p : Fin N, ∑ a ∈ S, ∑ b ∈ S, if a p ≠ b p then 1 else 0 := by
      have hinner : ∀ a ∈ S, ∑ b ∈ S, hdist a b =
          ∑ b ∈ S, ∑ p : Fin N, if a p ≠ b p then 1 else 0 := fun a _ =>
        Finset.sum_congr rfl fun b _ => by rw [hdist, Finset.card_filter]
      calc Dtot
          = ∑ a ∈ S, ∑ b ∈ S, ∑ p : Fin N, if a p ≠ b p then 1 else 0 :=
              Finset.sum_congr rfl hinner
        _ = ∑ a ∈ S, ∑ p : Fin N, ∑ b ∈ S, if a p ≠ b p then 1 else 0 :=
              Finset.sum_congr rfl fun a _ => Finset.sum_comm
        _ = ∑ p : Fin N, ∑ a ∈ S, ∑ b ∈ S, if a p ≠ b p then 1 else 0 := Finset.sum_comm
    rw [h1]
    refine Finset.sum_congr rfl fun p _ => ?_
    let S1 := S.filter (fun a => a p ≠ c p)
    let S0 := S.filter (fun a => a p = c p)
    have hS0_card : S0.card = M - kp p := by
      have htot := card_filter_add_not S (fun a => a p ≠ c p)
      have hS0eq : S0 = S.filter (fun a => ¬ a p ≠ c p) := by
        ext a; simp [S0]
      rw [← hS0eq] at htot
      change kp p + S0.card = M at htot
      omega
    have hdiff_iff : ∀ a b : Fin N → ZMod 2, a p ≠ b p ↔
        (a p ≠ c p ∧ b p = c p) ∨ (a p = c p ∧ b p ≠ c p) := by
      intro a b
      rcases zmod2_cases (a p) with ha | ha <;>
        rcases zmod2_cases (b p) with hb | hb <;>
        rcases zmod2_cases (c p) with hc | hc <;>
        simp [ha, hb, hc]
    have hsplit : ∀ a ∈ S, (∑ b ∈ S, if a p ≠ b p then 1 else 0) =
        if a p ≠ c p then S0.card else S1.card := by
      intro a _
      by_cases ha : a p ≠ c p
      · rw [if_pos ha]
        have hcongr : ∀ b ∈ S, (if a p ≠ b p then 1 else 0) = (if b p = c p then 1 else 0) := by
          intro b _
          have hiff : a p ≠ b p ↔ b p = c p := by
            rw [hdiff_iff]; tauto
          simp [hiff]
        rw [Finset.sum_congr rfl hcongr, ← Finset.card_filter]
      · rw [if_neg ha]
        have haeq : a p = c p := not_not.mp ha
        have hcongr : ∀ b ∈ S, (if a p ≠ b p then 1 else 0) = (if b p ≠ c p then 1 else 0) := by
          intro b _
          have hiff : a p ≠ b p ↔ b p ≠ c p := by
            rw [hdiff_iff]; tauto
          simp [hiff]
        rw [Finset.sum_congr rfl hcongr, ← Finset.card_filter]
    rw [Finset.sum_congr rfl hsplit]
    rw [← Finset.sum_filter_add_sum_filter_not S (fun a => a p ≠ c p)]
    have hA : ∑ a ∈ S.filter (fun a => a p ≠ c p), (if a p ≠ c p then S0.card else S1.card) =
        S1.card * S0.card := by
      have hc : ∀ a ∈ S1, (if a p ≠ c p then S0.card else S1.card) = S0.card :=
        fun a ha => if_pos (Finset.mem_filter.mp ha).2
      change ∑ a ∈ S1, _ = _
      rw [Finset.sum_congr rfl hc, Finset.sum_const, smul_eq_mul]
    have hB : ∑ a ∈ S.filter (fun a => ¬ a p ≠ c p), (if a p ≠ c p then S0.card else S1.card) =
        S0.card * S1.card := by
      have hS0eq : S.filter (fun a => ¬ a p ≠ c p) = S0 := by ext a; simp [S0]
      rw [hS0eq]
      have hc : ∀ a ∈ S0, (if a p ≠ c p then S0.card else S1.card) = S1.card :=
        fun a ha => if_neg (not_not.mpr (Finset.mem_filter.mp ha).2)
      rw [Finset.sum_congr rfl hc, Finset.sum_const, smul_eq_mul]
    rw [hA, hB, hS0_card]
    change kp p * (M - kp p) + (M - kp p) * kp p = 2 * kp p * (M - kp p)
    ring
  have hDtot_add : Dtot + 2 * ∑ p : Fin N, (kp p) ^ 2 = 2 * M * M * r := by
    rw [hDtot_eq, Finset.mul_sum, ← Finset.sum_add_distrib]
    have hterm : ∀ p : Fin N, 2 * kp p * (M - kp p) + 2 * (kp p) ^ 2 = 2 * M * kp p := by
      intro p
      have hle := hkp_le p
      zify [hle]
      ring
    rw [Finset.sum_congr rfl (fun p _ => hterm p), ← Finset.mul_sum, hkp_sum]
    ring
  have hcauchy : (M * r) ^ 2 ≤ N * ∑ p : Fin N, (kp p) ^ 2 := by
    rw [← hkp_sum]
    exact cauchy_sq_nat kp
  have hupper : N * Dtot ≤ 2 * M * M * r * (N - r) := by
    have h1 : N * Dtot + 2 * (N * ∑ p : Fin N, (kp p) ^ 2) = 2 * M * M * r * N := by
      have hmul := congrArg (fun x => N * x) hDtot_add
      linarith
    have h2 : 2 * (M * r) ^ 2 ≤ 2 * (N * ∑ p : Fin N, (kp p) ^ 2) := Nat.mul_le_mul_left 2 hcauchy
    have h3 : 2 * M * M * r * N = 2 * M * M * r * (N - r) + 2 * (M * r) ^ 2 := by
      zify [hr]
      ring
    omega
  have hcomb : M * M * (N * d) ≤ 2 * M * M * r * (N - r) + M * (N * d) := by
    have h1 := Nat.mul_le_mul_left N hlower
    have h2 : N * (M * M * d) = M * M * (N * d) := by ring
    have h3 : N * (Dtot + M * d) = N * Dtot + M * (N * d) := by ring
    rw [h2, h3] at h1
    omega
  have hfinal : M * (M * (N * d - 2 * r * (N - r))) ≤ M * (N * d) := by
    by_cases hlt : 2 * r * (N - r) ≤ N * d
    · have hsub : M * (M * (N * d - 2 * r * (N - r))) + 2 * M * M * r * (N - r) = M * M * (N * d) := by
        zify [hlt]
        ring
      omega
    · have h0 : N * d - 2 * r * (N - r) = 0 := by omega
      simp [h0]
  exact Nat.le_of_mul_le_mul_left hfinal (Nat.pos_of_ne_zero hM0)

private lemma card_sphere {N r : ℕ} (a : Fin N → ZMod 2) :
    (Finset.univ.filter (fun c : Fin N → ZMod 2 => hdist a c = r)).card = Nat.choose N r := by
  classical
  have hbij : (Finset.univ.filter (fun c : Fin N → ZMod 2 => hdist a c = r)).card =
      ((Finset.univ : Finset (Fin N)).powersetCard r).card := by
    refine Finset.card_bij
      (fun c _ => Finset.univ.filter (fun p : Fin N => a p ≠ c p))
      (fun c hc => ?_)
      (fun c1 _ c2 _ heq => ?_)
      (fun s hs => ?_)
    · rw [Finset.mem_powersetCard]
      exact ⟨Finset.subset_univ _, (Finset.mem_filter.mp hc).2⟩
    · funext p
      have hmem : (p ∈ Finset.univ.filter (fun q : Fin N => a q ≠ c1 q)) ↔
          (p ∈ Finset.univ.filter (fun q : Fin N => a q ≠ c2 q)) := by rw [heq]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
      rcases zmod2_cases (a p) with ha | ha <;>
        rcases zmod2_cases (c1 p) with h1 | h1 <;>
        rcases zmod2_cases (c2 p) with h2 | h2 <;>
        simp_all
    · rw [Finset.mem_powersetCard] at hs
      let c : Fin N → ZMod 2 := fun p => if p ∈ s then a p + 1 else a p
      have hfilt : Finset.univ.filter (fun p : Fin N => a p ≠ c p) = s := by
        ext p
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, c]
        by_cases hp : p ∈ s
        · simp only [hp, ↓reduceIte, iff_true]
          rcases zmod2_cases (a p) with ha | ha <;> rw [ha] <;> decide
        · simp [hp]
      refine ⟨c, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [hdist, hfilt, hs.2]⟩, hfilt⟩
  rw [hbij, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

end PEqualNP.Outside.L_meta_30579

open PEqualNP.Outside.L_meta_30579 in
theorem PEqualNP.Outside.L_meta_30579 :
    let nonlinear := fun (g : PEqualNP.CircuitLowerBounds.Gate) =>
      (g.inputs.length == 2) &&
      xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
          (xor (g.op.eval [true, false]) (g.op.eval [true, true]))
    let depths := fun (width : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) =>
      C.gates.foldl (fun (ds : List ℕ) g =>
        ds ++ [(g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nonlinear g).toNat])
        (List.replicate width 0)
    let fits := fun (n m q : ℕ) (G : Fin q → Fin n → Fin m → Bool) (t : ℕ) =>
      ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin q → ℕ),
        PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+m) C ∧
        (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧ C.gates.countP nonlinear ≤ t ∧
        ∀ j : Fin q, (depths (n+m) C).getD (tap j) 0 ≤ 1 ∧
          PEqualNP.Represents.Represents (G j) ⟨C.gates, tap j⟩

    let F := ZMod 2
    ∀ (K : Type) [Field K] [Algebra F K] [FiniteDimensional F K]
        (k : ℕ) (basis : Module.Basis (Fin k) F K) (bit : K →ₗ[F] F), bit ≠ 0 →
      let n := k+1
      let point : Fin n → K := Fin.cases 0 basis
      let mult := fun (z : K) (x y : Fin n) => decide (bit (z * point x * point y) ≠ 0)
      let residual := fun {g : ℕ} (T : Fin g → Fin n → Fin n → Bool) (S : Finset (Fin g))
          (z : K) (x y : Fin n) => xor (mult z x y) (((S.filter (fun i => T i x y)).card % 2) == 1)


      ∀ (g s N r u : ℕ) (T : Fin g → Fin n → Fin n → Bool) (Z : Finset K) (t : K → ℕ),
        fits n n g T s →
        (∀ z ∈ Z, ∃ S : Finset (Fin g), fits n n 1 (fun _ => residual T S z) (t z)) →
        s ≤ N → r ≤ N →
        let d := (k - 4*u + 1)/2
        2*r*(N-r) < N*d →
          ((u+1)*Z.card - ∑ z ∈ Z, t z) * Nat.choose N r * (N*d - 2*r*(N-r))
            ≤ (u+1) * 2^N * N*d := by
  classical
  intro nonlinear depths fits F K _ _ _ k basis bit hbit n point mult residual
    g s N r u T Z t hfit_sh hfit_res hsN hrN d hNd
  rcases hfit_sh with ⟨Csh, tapSh, _, hfanSh, hcntSh, hrepSh⟩
  have hnl_eq : nonlinear = nonlin := rfl
  rcases circuit_depth1_decomp n Csh.gates hfanSh with ⟨qsSh, hqsSh_len, _, hqsSh_rep⟩
  have hqsSh_leN : qsSh.length ≤ N := by
    rw [hnl_eq] at hcntSh
    exact hqsSh_len.trans (hcntSh.trans hsN)
  have hT_mask : ∀ i : Fin g, ∃ mask : Fin qsSh.length → ZMod 2,
      ∀ a b : Fin k, deltaMat (fun x y => b2z (T i x y)) a b =
        ∑ p : Fin qsSh.length, mask p * deltaMat (evalQuad (qsSh.get p)) a b := by
    intro i
    rcases hrepSh i with ⟨hdep, hrep⟩
    rcases hqsSh_rep (tapSh i) hdep with ⟨mask, α, β, heval⟩
    refine ⟨mask, fun a b => ?_⟩
    have hf : (fun x y => b2z (T i x y)) =
        fun x y => (α x + β y) + ∑ p : Fin qsSh.length, mask p * evalQuad (qsSh.get p) x y := by
      funext x y
      have hr := hrep x y
      change (wiresOf Csh.gates (PEqualNP.Represents.oneEach x y)).getD (tapSh i) false = T i x y at hr
      rw [← hr]
      exact heval x y
    rw [hf, deltaMat_add, deltaMat_aff, zero_add, deltaMat_sum]
    refine Finset.sum_congr rfl fun p _ => deltaMat_smul _ _ a b
  let maskT : Fin g → Fin qsSh.length → ZMod 2 := fun i => Classical.choose (hT_mask i)
  have hmaskT : ∀ (i : Fin g) (a b : Fin k),
      deltaMat (fun x y => b2z (T i x y)) a b =
        ∑ p : Fin qsSh.length, maskT i p * deltaMat (evalQuad (qsSh.get p)) a b :=
    fun i => Classical.choose_spec (hT_mask i)
  let Zgood : Finset K := Z.filter (fun z => t z ≤ u)
  have hz_data : ∀ z ∈ Zgood,
      ∃ (σ : Fin N → ZMod 2) (pairs : List ((Fin k → ZMod 2) × (Fin k → ZMod 2))),
        (∀ p : Fin N, qsSh.length ≤ p.val → σ p = 0) ∧
        pairs.length ≤ 2 * u ∧
        ∀ a b : Fin k,
          bit (z * basis a * basis b) =
            (∑ p : Fin qsSh.length, σ ⟨p.val, lt_of_lt_of_le p.isLt hqsSh_leN⟩ *
              deltaMat (evalQuad (qsSh.get p)) a b) +
            ∑ q : Fin pairs.length, (pairs.get q).1 a * (pairs.get q).2 b := by
    intro z hz
    have hzZ : z ∈ Z := (Finset.mem_filter.mp hz).1
    have htz : t z ≤ u := (Finset.mem_filter.mp hz).2
    rcases hfit_res z hzZ with ⟨Sz, Cpriv, tapPriv, _, hfanP, hcntP, hrepP⟩
    rw [hnl_eq] at hcntP
    rcases circuit_depth1_decomp n Cpriv.gates hfanP with ⟨qsP, hqsP_len, _, hqsP_rep⟩
    rcases hrepP 0 with ⟨hdepP, hrepP0⟩
    rcases hqsP_rep (tapPriv 0) hdepP with ⟨maskP, αP, βP, hevalP⟩
    rcases sum_quad_mask_as_pairs qsP maskP with ⟨pairs, hpairs_len, hpairs_eq⟩
    have hpairs_le : pairs.length ≤ 2 * u := by
      have hc : (Finset.univ.filter (fun p : Fin qsP.length => maskP p ≠ 0)).card ≤ qsP.length := by
        simpa using Finset.card_le_card (Finset.filter_subset _ (Finset.univ : Finset (Fin qsP.length)))
      omega
    let σ : Fin N → ZMod 2 := fun p =>
      if hp : p.val < qsSh.length then ∑ i ∈ Sz, maskT i ⟨p.val, hp⟩ else 0
    refine ⟨σ, pairs, fun p hp => dif_neg (by omega), hpairs_le, ?_⟩
    intro a b
    have hres_delta : deltaMat (fun x y => b2z (residual T Sz z x y)) a b =
        ∑ q : Fin pairs.length, (pairs.get q).1 a * (pairs.get q).2 b := by
      have hf : (fun x y => b2z (residual T Sz z x y)) =
          fun x y => (αP x + βP y) + ∑ p : Fin qsP.length, maskP p * evalQuad (qsP.get p) x y := by
        funext x y
        have hr := hrepP0 x y
        change (wiresOf Cpriv.gates (PEqualNP.Represents.oneEach x y)).getD (tapPriv 0) false = residual T Sz z x y at hr
        rw [← hr]
        exact hevalP x y
      rw [hf, deltaMat_add, deltaMat_aff, zero_add, deltaMat_sum]
      have hsm : (∑ p : Fin qsP.length, deltaMat (fun x y => maskP p * evalQuad (qsP.get p) x y) a b) =
          ∑ p : Fin qsP.length, maskP p * deltaMat (evalQuad (qsP.get p)) a b :=
        Finset.sum_congr rfl fun p _ => deltaMat_smul _ _ a b
      rw [hsm, hpairs_eq a b]
    have hres_lhs : deltaMat (fun x y => b2z (residual T Sz z x y)) a b =
        bit (z * basis a * basis b) +
          ∑ p : Fin qsSh.length, σ ⟨p.val, lt_of_lt_of_le p.isLt hqsSh_leN⟩ *
            deltaMat (evalQuad (qsSh.get p)) a b := by
      have hres_fun : (fun x y => b2z (residual T Sz z x y)) =
          fun x y => b2z (mult z x y) + ∑ i ∈ Sz, b2z (T i x y) := by
        funext x y
        simp only [residual, b2z_xor, b2z_filter_parity]
      rw [hres_fun, deltaMat_add, deltaMat_sum]
      have hmult_d : deltaMat (fun x y => b2z (mult z x y)) a b = bit (z * basis a * basis b) := by
        simp only [deltaMat, mult, point, Fin.cases_zero, Fin.cases_succ,
          mul_zero, zero_mul, map_zero]
        rcases zmod2_cases (bit (z * basis a * basis b)) with h0 | h1
        · simp [h0, b2z]
        · simp [h1, b2z]
      rw [hmult_d]
      congr 1
      have hswap : (∑ i ∈ Sz, deltaMat (fun x y => b2z (T i x y)) a b) =
          ∑ p : Fin qsSh.length, (∑ i ∈ Sz, maskT i p) * deltaMat (evalQuad (qsSh.get p)) a b := by
        simp_rw [hmaskT]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun p _ => (Finset.sum_mul _ _ _).symm
      rw [hswap]
      refine Finset.sum_congr rfl fun p _ => ?_
      simp [σ, p.isLt]
    rw [hres_lhs] at hres_delta
    have hadd := congrArg (fun v => v + ∑ p : Fin qsSh.length,
        σ ⟨p.val, lt_of_lt_of_le p.isLt hqsSh_leN⟩ * deltaMat (evalQuad (qsSh.get p)) a b) hres_delta
    have hl : bit (z * basis a * basis b) +
        (∑ p : Fin qsSh.length, σ ⟨p.val, lt_of_lt_of_le p.isLt hqsSh_leN⟩ *
          deltaMat (evalQuad (qsSh.get p)) a b) +
        (∑ p : Fin qsSh.length, σ ⟨p.val, lt_of_lt_of_le p.isLt hqsSh_leN⟩ *
          deltaMat (evalQuad (qsSh.get p)) a b) =
        bit (z * basis a * basis b) := by
      rw [add_assoc, zmod2_add_self, add_zero]
    rw [hl] at hadd
    rw [hadd, add_comm]
  let σOf : K → (Fin N → ZMod 2) := fun z =>
    if hz : z ∈ Zgood then Classical.choose (hz_data z hz) else 0
  have hdist_pair : ∀ z1 ∈ Zgood, ∀ z2 ∈ Zgood, z1 ≠ z2 → d ≤ hdist (σOf z1) (σOf z2) := by
    intro z1 hz1 z2 hz2 hne
    rcases Classical.choose_spec (hz_data z1 hz1) with ⟨P1, hσ1_pad, hP1_len, hP1_eq⟩
    rcases Classical.choose_spec (hz_data z2 hz2) with ⟨P2, hσ2_pad, hP2_len, hP2_eq⟩
    set σ1 := Classical.choose (hz_data z1 hz1)
    set σ2 := Classical.choose (hz_data z2 hz2)
    have hσ1_eq : σOf z1 = σ1 := dif_pos hz1
    have hσ2_eq : σOf z2 = σ2 := dif_pos hz2
    rw [hσ1_eq, hσ2_eq]
    let diffMask : Fin qsSh.length → ZMod 2 := fun p =>
      σ1 ⟨p.val, lt_of_lt_of_le p.isLt hqsSh_leN⟩ + σ2 ⟨p.val, lt_of_lt_of_le p.isLt hqsSh_leN⟩
    rcases sum_quad_mask_as_pairs qsSh diffMask with ⟨Pdiff, hPdiff_len, hPdiff_eq⟩
    have hdiff_card : (Finset.univ.filter (fun p : Fin qsSh.length => diffMask p ≠ 0)).card ≤ hdist σ1 σ2 := by
      unfold hdist
      refine Finset.card_le_card_of_injOn (fun p : Fin qsSh.length => ⟨p.val, lt_of_lt_of_le p.isLt hqsSh_leN⟩)
        (fun p hp => ?_) (fun p1 _ p2 _ heq => Fin.ext (Fin.mk.inj heq))
      have hne0 : diffMask p ≠ 0 := (Finset.mem_filter.mp hp).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun heq => hne0 ?_⟩
      simp only [diffMask, heq, zmod2_add_self]
    let allPairs := Pdiff ++ P1 ++ P2
    have hall_len : allPairs.length ≤ 4 * u + 2 * hdist σ1 σ2 := by
      simp only [allPairs, List.length_append]
      omega
    let A : Fin k → Fin k → ZMod 2 := fun a b => bit ((z1 - z2) * basis a * basis b)
    have hA_eq : ∀ a b : Fin k, A a b =
        ∑ q : Fin allPairs.length, (allPairs.get q).1 a * (allPairs.get q).2 b := by
      intro a b
      have hA_sum : A a b = bit (z1 * basis a * basis b) + bit (z2 * basis a * basis b) := by
        have hsub : (z1 - z2) * basis a * basis b = z1 * basis a * basis b - z2 * basis a * basis b := by ring
        rw [show A a b = bit ((z1 - z2) * basis a * basis b) from rfl, hsub, map_sub, zmod2_sub_eq_add]
      rw [hA_sum, hP1_eq a b, hP2_eq a b]
      have hrearr :
          ((∑ p : Fin qsSh.length, σ1 ⟨p.val, lt_of_lt_of_le p.isLt hqsSh_leN⟩ *
              deltaMat (evalQuad (qsSh.get p)) a b) +
            ∑ q : Fin P1.length, (P1.get q).1 a * (P1.get q).2 b) +
          ((∑ p : Fin qsSh.length, σ2 ⟨p.val, lt_of_lt_of_le p.isLt hqsSh_leN⟩ *
              deltaMat (evalQuad (qsSh.get p)) a b) +
            ∑ q : Fin P2.length, (P2.get q).1 a * (P2.get q).2 b) =
          (∑ p : Fin qsSh.length, diffMask p * deltaMat (evalQuad (qsSh.get p)) a b) +
          (∑ q : Fin P1.length, (P1.get q).1 a * (P1.get q).2 b) +
          (∑ q : Fin P2.length, (P2.get q).1 a * (P2.get q).2 b) := by
        have hdm : ∑ p : Fin qsSh.length, diffMask p * deltaMat (evalQuad (qsSh.get p)) a b =
            (∑ p : Fin qsSh.length, σ1 ⟨p.val, lt_of_lt_of_le p.isLt hqsSh_leN⟩ *
              deltaMat (evalQuad (qsSh.get p)) a b) +
            (∑ p : Fin qsSh.length, σ2 ⟨p.val, lt_of_lt_of_le p.isLt hqsSh_leN⟩ *
              deltaMat (evalQuad (qsSh.get p)) a b) := by
          simp only [diffMask, add_mul, Finset.sum_add_distrib]
        rw [hdm]; ring
      rw [hrearr, hPdiff_eq a b,
        sum_fin_list allPairs (fun ab => ab.1 a * ab.2 b),
        sum_fin_list Pdiff (fun ab => ab.1 a * ab.2 b),
        sum_fin_list P1 (fun ab => ab.1 a * ab.2 b),
        sum_fin_list P2 (fun ab => ab.1 a * ab.2 b)]
      simp [allPairs, List.map_append, List.sum_append, add_assoc]
    have hkle : k ≤ allPairs.length :=
      row_inj_le_outer_len A (mult_mat_row_inj basis bit hbit (z1 - z2) (sub_ne_zero.mpr hne)) allPairs hA_eq
    have h2d : k - 4 * u ≤ 2 * hdist σ1 σ2 := by omega
    change (k - 4 * u + 1) / 2 ≤ hdist σ1 σ2
    omega
  have hd_pos : 0 < d := by
    by_contra h0
    have hd0 : d = 0 := by omega
    rw [hd0, mul_zero] at hNd
    exact Nat.not_lt_zero _ hNd
  have hσ_inj : Set.InjOn σOf (Zgood : Set K) := by
    intro z1 hz1 z2 hz2 heq
    by_contra hne
    have hd := hdist_pair z1 hz1 z2 hz2 hne
    have h0 : hdist (σOf z1) (σOf z2) = 0 := by
      rw [heq]; simp [hdist]
    omega
  let C : Finset (Fin N → ZMod 2) := Zgood.image σOf
  have hC_card : C.card = Zgood.card := Finset.card_image_of_injOn hσ_inj
  have hC_dist : ∀ a ∈ C, ∀ b ∈ C, a ≠ b → d ≤ hdist a b := by
    intro a ha b hb hab
    rcases Finset.mem_image.mp ha with ⟨z1, hz1, rfl⟩
    rcases Finset.mem_image.mp hb with ⟨z2, hz2, rfl⟩
    exact hdist_pair z1 hz1 z2 hz2 (fun h => hab (congrArg σOf h))
  have hshell_sum : ∑ c : Fin N → ZMod 2,
      (C.filter (fun a => hdist a c = r)).card * (N * d - 2 * r * (N - r)) ≤
      2 ^ N * (N * d) := by
    have hle : ∑ c : Fin N → ZMod 2,
        (C.filter (fun a => hdist a c = r)).card * (N * d - 2 * r * (N - r)) ≤
        ∑ _c : Fin N → ZMod 2, N * d :=
      Finset.sum_le_sum fun c _ => johnson_shell_bound C hC_dist c hrN
    have hrhs : ∑ _c : Fin N → ZMod 2, N * d = 2 ^ N * (N * d) := by
      simp [Fintype.card_pi, ZMod.card]
    exact hle.trans (le_of_eq hrhs)
  have hdouble : ∑ c : Fin N → ZMod 2, (C.filter (fun a => hdist a c = r)).card =
      C.card * Nat.choose N r := by
    have h1 : ∑ c : Fin N → ZMod 2, (C.filter (fun a => hdist a c = r)).card =
        ∑ c : Fin N → ZMod 2, ∑ a ∈ C, if hdist a c = r then 1 else 0 :=
      Finset.sum_congr rfl fun c _ => by simp
    rw [h1, Finset.sum_comm]
    have h2 : ∀ a ∈ C, (∑ c : Fin N → ZMod 2, if hdist a c = r then 1 else 0) = Nat.choose N r := by
      intro a _
      have hcard : (∑ c : Fin N → ZMod 2, if hdist a c = r then 1 else 0) =
          (Finset.univ.filter (fun c : Fin N → ZMod 2 => hdist a c = r)).card := by simp
      rw [hcard, card_sphere a]
    rw [Finset.sum_congr rfl h2]
    simp
  have hZgood_bound : Zgood.card * Nat.choose N r * (N * d - 2 * r * (N - r)) ≤ 2 ^ N * (N * d) := by
    rw [← Finset.sum_mul, hdouble, hC_card] at hshell_sum
    exact hshell_sum
  have hZ_split : (u + 1) * Z.card - ∑ z ∈ Z, t z ≤ (u + 1) * Zgood.card := by
    let Zbad := Z.filter (fun z => ¬ t z ≤ u)
    have hcard_split : Zgood.card + Zbad.card = Z.card :=
      card_filter_add_not Z (fun z => t z ≤ u)
    have hsum_bad : (u + 1) * Zbad.card ≤ ∑ z ∈ Zbad, t z := by
      have h1 : ∑ _z ∈ Zbad, (u + 1) ≤ ∑ z ∈ Zbad, t z :=
        Finset.sum_le_sum fun z hz => by
          have hgt : ¬ t z ≤ u := (Finset.mem_filter.mp hz).2
          omega
      simpa [mul_comm] using h1
    have hsum_le : ∑ z ∈ Zbad, t z ≤ ∑ z ∈ Z, t z :=
      Finset.sum_le_sum_of_subset (Finset.filter_subset _ Z)
    have hmul_split : (u + 1) * Z.card = (u + 1) * Zgood.card + (u + 1) * Zbad.card := by
      rw [← hcard_split, mul_add]
    omega
  calc ((u + 1) * Z.card - ∑ z ∈ Z, t z) * Nat.choose N r * (N * d - 2 * r * (N - r))
      ≤ ((u + 1) * Zgood.card) * Nat.choose N r * (N * d - 2 * r * (N - r)) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hZ_split)
    _ = (u + 1) * (Zgood.card * Nat.choose N r * (N * d - 2 * r * (N - r))) := by ring
    _ ≤ (u + 1) * (2 ^ N * (N * d)) := Nat.mul_le_mul_left _ hZgood_bound
    _ = (u + 1) * 2 ^ N * N * d := by ring
