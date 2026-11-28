import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_32033

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents

private def b2z (b : Bool) : ZMod 2 := if b then 1 else 0

private lemma zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 :=
  match a with
  | ⟨0, _⟩ => Or.inl rfl
  | ⟨1, _⟩ => Or.inr rfl

private lemma zmod2_add_self (a : ZMod 2) : a + a = 0 := by
  rcases zmod2_cases a with rfl | rfl <;> decide

private lemma b2z_inj {a b : Bool} (h : b2z a = b2z b) : a = b := by
  cases a <;> cases b <;> simp [b2z] at h ⊢

private lemma b2z_xor (a b : Bool) : b2z (xor a b) = b2z a + b2z b := by
  cases a <;> cases b <;> decide

private lemma b2z_and (a b : Bool) : b2z (a && b) = b2z a * b2z b := by
  cases a <;> cases b <;> decide

private lemma b2z_not (a : Bool) : b2z (!a) = 1 + b2z a := by
  cases a <;> decide

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

private lemma wiresOf_append_prefix (gs₁ gs₂ : List Gate) (x : List Bool) (w : ℕ)
    (hw : w < x.length + gs₁.length) :
    (wiresOf (gs₁ ++ gs₂) x).getD w false = (wiresOf gs₁ x).getD w false := by
  induction gs₂ using List.reverseRecOn with
  | nil => simp
  | append_singleton gs₂ g ih =>
    have h1 : gs₁ ++ (gs₂ ++ [g]) = (gs₁ ++ gs₂) ++ [g] := (List.append_assoc _ _ _).symm
    have hstep : wiresOf ((gs₁ ++ gs₂) ++ [g]) x =
        wiresOf (gs₁ ++ gs₂) x ++ [g.op.eval (g.inputs.map fun i => (wiresOf (gs₁ ++ gs₂) x).getD i false)] := by
      simp [wiresOf, List.foldl_append]
    rw [h1, hstep, getD_append_left _ _ _ _ (by rw [wiresOf_length, List.length_append]; omega)]
    exact ih

private lemma depthsOf_append_prefix (width : ℕ) (gs₁ gs₂ : List Gate) (w : ℕ)
    (hw : w < width + gs₁.length) :
    (depthsOf width (gs₁ ++ gs₂)).getD w 0 = (depthsOf width gs₁).getD w 0 := by
  induction gs₂ using List.reverseRecOn with
  | nil => simp
  | append_singleton gs₂ g ih =>
    have h1 : gs₁ ++ (gs₂ ++ [g]) = (gs₁ ++ gs₂) ++ [g] := (List.append_assoc _ _ _).symm
    have hstep : depthsOf width ((gs₁ ++ gs₂) ++ [g]) =
        depthsOf width (gs₁ ++ gs₂) ++
          [(g.inputs.map (fun a => (depthsOf width (gs₁ ++ gs₂)).getD a 0)).foldr max 0 + (nonlin g).toNat] := by
      simp [depthsOf, List.foldl_append]
    rw [h1, hstep, getD_append_left _ _ _ _ (by rw [depthsOf_length, List.length_append]; omega)]
    exact ih

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

private abbrev Quad (n m : ℕ) :=
  (Fin n → ZMod 2) × (Fin m → ZMod 2) × (Fin n → ZMod 2) × (Fin m → ZMod 2)

private def evalQuad {n m : ℕ} (q : Quad n m) (x : Fin n) (y : Fin m) : ZMod 2 :=
  q.1 x * q.2.1 y + q.2.2.1 x * q.2.2.2 y

private lemma circuit_depth1_decomp (n m : ℕ) (gs : List Gate)
    (hfan : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    ∃ qs : List (Quad n m),
      qs.length ≤ gs.countP nonlin ∧
      (∀ idx : ℕ, (depthsOf (n + m) gs).getD idx 0 = 0 →
        ∃ (α : Fin n → ZMod 2) (β : Fin m → ZMod 2),
          ∀ (x : Fin n) (y : Fin m), b2z ((wiresOf gs (oneEach x y)).getD idx false) = α x + β y) ∧
      (∀ idx : ℕ, (depthsOf (n + m) gs).getD idx 0 ≤ 1 →
        ∃ (mask : Fin qs.length → ZMod 2) (α : Fin n → ZMod 2) (β : Fin m → ZMod 2),
          ∀ (x : Fin n) (y : Fin m), b2z ((wiresOf gs (oneEach x y)).getD idx false) =
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
        have hiff : ((⟨idx, h1⟩ : Fin n) = x) ↔ x.val = idx :=
          ⟨fun h => by rw [← h], fun h => Fin.ext h.symm⟩
        simp [hiff]
      · by_cases h2 : idx < n + m
        · refine ⟨fun _ => 0, fun y => b2z (decide (y.val = idx - n)), fun x y => ?_⟩
          simp only [wiresOf, List.foldl_nil, oneEach, zero_add]
          have hlen1 : (List.ofFn (fun i : Fin n => decide (i = x))).length = n := by simp
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [hlen1]; omega)]
          simp only [hlen1, List.getElem?_ofFn, dif_pos (by omega : idx - n < m), Option.getD_some]
          have hiff : ((⟨idx - n, by omega⟩ : Fin m) = y) ↔ y.val = idx - n :=
            ⟨fun h => by rw [← h], fun h => Fin.ext h.symm⟩
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
        have hiff : ((⟨idx, h1⟩ : Fin n) = x) ↔ x.val = idx :=
          ⟨fun h => by rw [← h], fun h => Fin.ext h.symm⟩
        simp [hiff]
      · by_cases h2 : idx < n + m
        · refine ⟨Fin.elim0, fun _ => 0, fun y => b2z (decide (y.val = idx - n)), fun x y => ?_⟩
          simp only [wiresOf, List.foldl_nil, oneEach, Finset.univ_eq_empty, Finset.sum_empty,
            zero_add, add_zero]
          have hlen1 : (List.ofFn (fun i : Fin n => decide (i = x))).length = n := by simp
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [hlen1]; omega)]
          simp only [hlen1, List.getElem?_ofFn, dif_pos (by omega : idx - n < m), Option.getD_some]
          have hiff : ((⟨idx - n, by omega⟩ : Fin m) = y) ↔ y.val = idx - n :=
            ⟨fun h => by rw [← h], fun h => Fin.ext h.symm⟩
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
    set curLen := (n + m) + gs.length
    have hd_len : (depthsOf (n + m) gs).length = curLen := depthsOf_length (n + m) gs
    have hw_len : ∀ (x : Fin n) (y : Fin m), (wiresOf gs (oneEach x y)).length = curLen := fun x y => by
      rw [wiresOf_length, oneEach_length]
    have hd_step : depthsOf (n + m) (gs ++ [g]) =
        depthsOf (n + m) gs ++
          [(g.inputs.map (fun a => (depthsOf (n + m) gs).getD a 0)).foldr max 0 + (nonlin g).toNat] := by
      simp [depthsOf, List.foldl_append]
    have hw_step : ∀ (x : Fin n) (y : Fin m), wiresOf (gs ++ [g]) (oneEach x y) =
        wiresOf gs (oneEach x y) ++
          [g.op.eval (g.inputs.map fun i => (wiresOf gs (oneEach x y)).getD i false)] := by
      intro x y; simp [wiresOf, List.foldl_append]
    have hcount : (gs ++ [g]).countP nonlin = gs.countP nonlin + (nonlin g).toNat := by
      rw [List.countP_append, List.countP_cons, List.countP_nil]
      cases nonlin g <;> simp
    let d_in := (g.inputs.map (fun a => (depthsOf (n + m) gs).getD a 0)).foldr max 0
    have hd_new : (depthsOf (n + m) (gs ++ [g])).getD curLen 0 = d_in + (nonlin g).toNat := by
      rw [hd_step, ← hd_len, getD_append_last]
    have hw_new : ∀ (x : Fin n) (y : Fin m),
        (wiresOf (gs ++ [g]) (oneEach x y)).getD curLen false =
          g.op.eval (g.inputs.map fun i => (wiresOf gs (oneEach x y)).getD i false) := by
      intro x y
      rw [hw_step x y, ← hw_len x y, getD_append_last]
    have hd_old : ∀ idx < curLen,
        (depthsOf (n + m) (gs ++ [g])).getD idx 0 = (depthsOf (n + m) gs).getD idx 0 := by
      intro idx hlt
      rw [hd_step, getD_append_left _ _ _ _ (by omega)]
    have hw_old : ∀ idx < curLen, ∀ (x : Fin n) (y : Fin m),
        (wiresOf (gs ++ [g]) (oneEach x y)).getD idx false =
          (wiresOf gs (oneEach x y)).getD idx false := by
      intro idx hlt x y
      rw [hw_step x y, getD_append_left _ _ _ _ (by rw [hw_len x y]; omega)]
    have hw_hi : ∀ idx, curLen < idx → ∀ (x : Fin n) (y : Fin m),
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
            · have ha0 : (depthsOf (n + m) gs).getD a 0 = 0 := by
                simp only [d_in, hgs_in, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil] at hdep0
                omega
              rcases ih0 a ha0 with ⟨α, β, hαβ⟩
              rcases b2z_unary_affine (fun u => g.op.eval [u]) with ⟨c0, c1, haff⟩
              refine ⟨fun x => c0 + c1 * α x, fun y => c1 * β y, fun x y => ?_⟩
              rw [hw_new x y, hgs_in, List.map_cons, List.map_nil, haff, hαβ x y]
              ring
            · have hab0 : max ((depthsOf (n + m) gs).getD a 0) ((depthsOf (n + m) gs).getD b 0) = 0 := by
                simp only [d_in, hgs_in, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil] at hdep0
                omega
              have ha0 : (depthsOf (n + m) gs).getD a 0 = 0 := by omega
              have hb0 : (depthsOf (n + m) gs).getD b 0 = 0 := by omega
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
            · have ha1 : (depthsOf (n + m) gs).getD a 0 ≤ 1 := by
                simp only [d_in, hgs_in, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil] at hdep1
                omega
              rcases ih1 a ha1 with ⟨m1, α1, β1, h1⟩
              rcases b2z_unary_affine (fun u => g.op.eval [u]) with ⟨c0, c1, haff⟩
              refine ⟨fun p => c1 * m1 p, fun x => c0 + c1 * α1 x, fun y => c1 * β1 y, fun x y => ?_⟩
              rw [hw_new x y, hgs_in, List.map_cons, List.map_nil, haff, h1 x y]
              simp only [mul_assoc, ← Finset.mul_sum]
              ring
            · have hab1 : max ((depthsOf (n + m) gs).getD a 0) ((depthsOf (n + m) gs).getD b 0) ≤ 1 := by
                simp only [d_in, hgs_in, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil] at hdep1
                omega
              have ha1 : (depthsOf (n + m) gs).getD a 0 ≤ 1 := by omega
              have hb1 : (depthsOf (n + m) gs).getD b 0 ≤ 1 := by omega
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
        · have hab0 : max ((depthsOf (n + m) gs).getD a 0) ((depthsOf (n + m) gs).getD b 0) = 0 := by
            simp only [d_in, hgs_in, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil] at hdin0
            omega
          have ha0 : (depthsOf (n + m) gs).getD a 0 = 0 := by omega
          have hb0 : (depthsOf (n + m) gs).getD b 0 = 0 := by omega
          rcases ih0 a ha0 with ⟨α1, β1, h1⟩
          rcases ih0 b hb0 with ⟨α2, β2, h2⟩
          rcases b2z_binary_poly (fun u v => g.op.eval [u, v]) with ⟨c0, c1, c2, hpoly⟩
          let qNew : Quad n m := (α1, β2, α2, β1)
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

private def deltaMat {n m : ℕ} (f : Fin (n + 1) → Fin (m + 1) → ZMod 2)
    (i : Fin n) (j : Fin m) : ZMod 2 :=
  f i.succ j.succ + f i.succ 0 + f 0 j.succ + f 0 0

private lemma deltaMat_add {n m : ℕ} (f g : Fin (n + 1) → Fin (m + 1) → ZMod 2)
    (i : Fin n) (j : Fin m) :
    deltaMat (fun x y => f x y + g x y) i j = deltaMat f i j + deltaMat g i j := by
  simp only [deltaMat]; ring

private lemma deltaMat_aff {n m : ℕ} (α : Fin (n + 1) → ZMod 2) (β : Fin (m + 1) → ZMod 2)
    (i : Fin n) (j : Fin m) :
    deltaMat (fun x y => α x + β y) i j = 0 := by
  simp only [deltaMat]
  have h1 : α i.succ + β j.succ + (α i.succ + β 0) + (α 0 + β j.succ) + (α 0 + β 0) =
      (α i.succ + α i.succ) + (α 0 + α 0) + (β j.succ + β j.succ) + (β 0 + β 0) := by ring
  rw [h1]
  simp only [zmod2_add_self, add_zero]

private lemma deltaMat_outer {n m : ℕ} (u : Fin (n + 1) → ZMod 2) (v : Fin (m + 1) → ZMod 2)
    (i : Fin n) (j : Fin m) :
    deltaMat (fun x y => u x * v y) i j = (u i.succ + u 0) * (v j.succ + v 0) := by
  simp only [deltaMat]; ring

private lemma deltaMat_quad {n m : ℕ} (q : Quad (n + 1) (m + 1)) (i : Fin n) (j : Fin m) :
    deltaMat (evalQuad q) i j =
      (q.1 i.succ + q.1 0) * (q.2.1 j.succ + q.2.1 0) +
      (q.2.2.1 i.succ + q.2.2.1 0) * (q.2.2.2 j.succ + q.2.2.2 0) := by
  unfold evalQuad
  rw [deltaMat_add, deltaMat_outer, deltaMat_outer]

private lemma deltaMat_sum {n m : ℕ} {ι : Type*} (s : Finset ι)
    (f : ι → Fin (n + 1) → Fin (m + 1) → ZMod 2) (i : Fin n) (j : Fin m) :
    deltaMat (fun x y => ∑ p ∈ s, f p x y) i j = ∑ p ∈ s, deltaMat (f p) i j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [deltaMat]
  | insert a t ha ih =>
    simp only [Finset.sum_insert ha]
    rw [deltaMat_add, ih]

private lemma deltaMat_smul {n m : ℕ} (c : ZMod 2)
    (f : Fin (n + 1) → Fin (m + 1) → ZMod 2) (i : Fin n) (j : Fin m) :
    deltaMat (fun x y => c * f x y) i j = c * deltaMat f i j := by
  simp only [deltaMat]; ring

private def goodGates (w : ℕ) (gs : List Gate) : Prop :=
  (∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < w + j) ∧
  (∀ g ∈ gs, g.inputs.length ≤ 2)

private lemma append_gate_good (w : ℕ) (gs : List Gate) (g : Gate)
    (hgood : goodGates w gs) (hfan : g.inputs.length ≤ 2)
    (hback : ∀ i ∈ g.inputs, i < w + gs.length) :
    goodGates w (gs ++ [g]) := by
  refine ⟨?_, ?_⟩
  · intro j hj i hi
    simp only [List.length_append, List.length_singleton] at hj
    by_cases hlt : j < gs.length
    · rw [getD_append_left _ _ _ _ hlt] at hi
      exact hgood.1 j hlt i hi
    · have heq : j = gs.length := by omega
      subst heq
      rw [getD_append_last] at hi
      exact hback i hi
  · intro g' hg'
    simp only [List.mem_append, List.mem_singleton] at hg'
    rcases hg' with h | rfl
    · exact hgood.2 g' h
    · exact hfan

private lemma append_constFalse (w : ℕ) (gs : List Gate) (hgood : goodGates w gs) :
    let gs' := gs ++ [⟨GateOp.or, []⟩]
    let out := w + gs.length
    gs.length ≤ gs'.length ∧ goodGates w gs' ∧
    gs'.countP nonlin = gs.countP nonlin ∧
    out < w + gs'.length ∧
    (depthsOf w gs').getD out 0 = 0 ∧
    (∀ u < w + gs.length, (depthsOf w gs').getD u 0 = (depthsOf w gs).getD u 0) ∧
    (∀ (x : List Bool), x.length = w →
      (∀ u < w + gs.length, (wiresOf gs' x).getD u false = (wiresOf gs x).getD u false) ∧
      (wiresOf gs' x).getD out false = false) := by
  intro gs' out
  have hnl : nonlin ⟨GateOp.or, []⟩ = false := by decide
  refine ⟨by simp [gs'], append_gate_good w gs _ hgood (by simp) (fun _ h => by cases h),
    by simp [gs', List.countP_append, hnl], by simp [gs', out], ?_, ?_, ?_⟩
  · simp only [gs', out, depthsOf, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (depthsOf w gs).length = w + gs.length := depthsOf_length w gs
    change ((depthsOf w gs) ++ [_]).getD (w + gs.length) 0 = 0
    rw [← hlen, getD_append_last]
    simp [hnl]
  · intro u hu
    exact depthsOf_append_prefix w gs _ u hu
  · intro x hx
    refine ⟨fun u hu => wiresOf_append_prefix gs _ x u (by omega), ?_⟩
    simp only [gs', out, wiresOf, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (wiresOf gs x).length = w + gs.length := by rw [wiresOf_length, hx]
    change ((wiresOf gs x) ++ [_]).getD (w + gs.length) false = false
    rw [← hlen, getD_append_last]
    rfl

private lemma append_xor2 (w : ℕ) (gs : List Gate) (u v : ℕ)
    (hgood : goodGates w gs) (hu : u < w + gs.length) (hv : v < w + gs.length) :
    let gs' := gs ++ [⟨GateOp.mod 2, [u, v]⟩, ⟨GateOp.not, [w + gs.length]⟩]
    let out := w + gs.length + 1
    gs.length ≤ gs'.length ∧ goodGates w gs' ∧
    gs'.countP nonlin = gs.countP nonlin ∧
    out < w + gs'.length ∧
    (depthsOf w gs').getD out 0 = max ((depthsOf w gs).getD u 0) ((depthsOf w gs).getD v 0) ∧
    (∀ k < w + gs.length, (depthsOf w gs').getD k 0 = (depthsOf w gs).getD k 0) ∧
    (∀ (x : List Bool), x.length = w →
      (∀ k < w + gs.length, (wiresOf gs' x).getD k false = (wiresOf gs x).getD k false) ∧
      (wiresOf gs' x).getD out false = xor ((wiresOf gs x).getD u false) ((wiresOf gs x).getD v false)) := by
  intro gs' out
  have hnl1 : nonlin ⟨GateOp.mod 2, [u, v]⟩ = false := by simp [nonlin]; decide
  have hnl2 : nonlin ⟨GateOp.not, [w + gs.length]⟩ = false := by simp [nonlin]
  have hgs'_eq : gs' = (gs ++ [⟨GateOp.mod 2, [u, v]⟩]) ++ [⟨GateOp.not, [w + gs.length]⟩] := by
    simp [gs']
  have hgood1 : goodGates w (gs ++ [⟨GateOp.mod 2, [u, v]⟩]) :=
    append_gate_good w gs _ hgood (by simp) (fun i hi => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> omega)
  have hgood2 : goodGates w gs' := by
    rw [hgs'_eq]
    exact append_gate_good w _ _ hgood1 (by simp) (fun i hi => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rw [hi, List.length_append, List.length_singleton]; omega)
  refine ⟨by simp [gs'], hgood2, by simp [gs', List.countP_append, hnl1, hnl2],
    by simp [gs', out]; omega, ?_, ?_, ?_⟩
  · rw [hgs'_eq]
    set gs1 := gs ++ [⟨GateOp.mod 2, [u, v]⟩]
    have hd1_len : (depthsOf w gs1).length = w + gs.length + 1 := by
      rw [depthsOf_length]; simp [gs1]; omega
    have hd0_len : (depthsOf w gs).length = w + gs.length := depthsOf_length w gs
    have hd_mid : (depthsOf w gs1).getD (w + gs.length) 0 =
        max ((depthsOf w gs).getD u 0) ((depthsOf w gs).getD v 0) := by
      have hstep : depthsOf w gs1 = depthsOf w gs ++
          [(([u, v]).map (fun a => (depthsOf w gs).getD a 0)).foldr max 0 + (nonlin ⟨GateOp.mod 2, [u, v]⟩).toNat] := by
        simp [gs1, depthsOf, List.foldl_append]
      rw [hstep, ← hd0_len, getD_append_last, hnl1]
      simp
    have hstep2 : depthsOf w (gs1 ++ [⟨GateOp.not, [w + gs.length]⟩]) = depthsOf w gs1 ++
        [(([w + gs.length]).map (fun a => (depthsOf w gs1).getD a 0)).foldr max 0 +
          (nonlin ⟨GateOp.not, [w + gs.length]⟩).toNat] := by
      simp [depthsOf, List.foldl_append]
    rw [hstep2]
    change (depthsOf w gs1 ++ _).getD (w + gs.length + 1) 0 = _
    rw [← hd1_len, getD_append_last, hnl2]
    simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, Bool.toNat_false, add_zero]
    rw [hd_mid]
    omega
  · intro k hk
    exact depthsOf_append_prefix w gs _ k hk
  · intro x hx
    refine ⟨fun k hk => wiresOf_append_prefix gs _ x k (by omega), ?_⟩
    rw [hgs'_eq]
    set gs1 := gs ++ [⟨GateOp.mod 2, [u, v]⟩]
    have hw0_len : (wiresOf gs x).length = w + gs.length := by rw [wiresOf_length, hx]
    have hw1_len : (wiresOf gs1 x).length = w + gs.length + 1 := by
      rw [wiresOf_length, hx]; simp [gs1]; omega
    have hmid : (wiresOf gs1 x).getD (w + gs.length) false =
        (GateOp.mod 2).eval [(wiresOf gs x).getD u false, (wiresOf gs x).getD v false] := by
      have hstep : wiresOf gs1 x = wiresOf gs x ++
          [(GateOp.mod 2).eval (([u, v]).map fun i => (wiresOf gs x).getD i false)] := by
        simp [gs1, wiresOf, List.foldl_append]
      rw [hstep, ← hw0_len, getD_append_last]
      rfl
    have hstep2 : wiresOf (gs1 ++ [⟨GateOp.not, [w + gs.length]⟩]) x = wiresOf gs1 x ++
        [GateOp.not.eval (([w + gs.length]).map fun i => (wiresOf gs1 x).getD i false)] := by
      simp [wiresOf, List.foldl_append]
    rw [hstep2]
    change (wiresOf gs1 x ++ _).getD (w + gs.length + 1) false = _
    rw [← hw1_len, getD_append_last]
    simp only [List.map_cons, List.map_nil]
    rw [hmid]
    generalize (wiresOf gs x).getD u false = bu
    generalize (wiresOf gs x).getD v false = bv
    cases bu <;> cases bv <;> decide

private lemma append_and2 (w : ℕ) (gs : List Gate) (u v : ℕ)
    (hgood : goodGates w gs) (hu : u < w + gs.length) (hv : v < w + gs.length) :
    let gs' := gs ++ [⟨GateOp.and, [u, v]⟩]
    let out := w + gs.length
    gs.length ≤ gs'.length ∧ goodGates w gs' ∧
    gs'.countP nonlin = gs.countP nonlin + 1 ∧
    out < w + gs'.length ∧
    (depthsOf w gs').getD out 0 = max ((depthsOf w gs).getD u 0) ((depthsOf w gs).getD v 0) + 1 ∧
    (∀ k < w + gs.length, (depthsOf w gs').getD k 0 = (depthsOf w gs).getD k 0) ∧
    (∀ (x : List Bool), x.length = w →
      (∀ k < w + gs.length, (wiresOf gs' x).getD k false = (wiresOf gs x).getD k false) ∧
      (wiresOf gs' x).getD out false = ((wiresOf gs x).getD u false && (wiresOf gs x).getD v false)) := by
  intro gs' out
  have hnl : nonlin ⟨GateOp.and, [u, v]⟩ = true := by simp [nonlin]; decide
  refine ⟨by simp [gs'], append_gate_good w gs _ hgood (by simp) (fun i hi => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> omega),
    by simp [gs', List.countP_append, hnl], by simp [gs', out], ?_, ?_, ?_⟩
  · have hstep : depthsOf w gs' = depthsOf w gs ++
        [(([u, v]).map (fun a => (depthsOf w gs).getD a 0)).foldr max 0 + (nonlin ⟨GateOp.and, [u, v]⟩).toNat] := by
      simp [gs', depthsOf, List.foldl_append]
    have hlen : (depthsOf w gs).length = w + gs.length := depthsOf_length w gs
    rw [hstep]
    change (depthsOf w gs ++ _).getD (w + gs.length) 0 = _
    rw [← hlen, getD_append_last, hnl]
    simp
  · intro k hk
    exact depthsOf_append_prefix w gs _ k hk
  · intro x hx
    refine ⟨fun k hk => wiresOf_append_prefix gs _ x k (by omega), ?_⟩
    have hstep : wiresOf gs' x = wiresOf gs x ++
        [GateOp.and.eval (([u, v]).map fun i => (wiresOf gs x).getD i false)] := by
      simp [gs', wiresOf, List.foldl_append]
    have hlen : (wiresOf gs x).length = w + gs.length := by rw [wiresOf_length, hx]
    rw [hstep]
    change (wiresOf gs x ++ _).getD (w + gs.length) false = _
    rw [← hlen, getD_append_last]
    simp only [List.map_cons, List.map_nil]
    generalize (wiresOf gs x).getD u false = bu
    generalize (wiresOf gs x).getD v false = bv
    cases bu <;> cases bv <;> decide

private lemma exists_xorList (w : ℕ) (gs : List Gate) (ws : List ℕ) (D : ℕ)
    (hgood : goodGates w gs) (hws : ∀ u ∈ ws, u < w + gs.length)
    (hdep : ∀ u ∈ ws, (depthsOf w gs).getD u 0 ≤ D) :
    ∃ (gs' : List Gate) (out : ℕ),
      gs.length ≤ gs'.length ∧ goodGates w gs' ∧
      gs'.countP nonlin = gs.countP nonlin ∧
      out < w + gs'.length ∧
      (depthsOf w gs').getD out 0 ≤ D ∧
      (∀ k < w + gs.length, (depthsOf w gs').getD k 0 = (depthsOf w gs).getD k 0) ∧
      (∀ (x : List Bool), x.length = w →
        (∀ k < w + gs.length, (wiresOf gs' x).getD k false = (wiresOf gs x).getD k false) ∧
        b2z ((wiresOf gs' x).getD out false) = (ws.map (fun u => b2z ((wiresOf gs x).getD u false))).sum) := by
  induction ws with
  | nil =>
    have h := append_constFalse w gs hgood
    refine ⟨_, _, h.1, h.2.1, h.2.2.1, h.2.2.2.1, by rw [h.2.2.2.2.1]; omega, h.2.2.2.2.2.1,
      fun x hx => ⟨(h.2.2.2.2.2.2 x hx).1, by rw [(h.2.2.2.2.2.2 x hx).2]; simp [b2z]⟩⟩
  | cons a t ih =>
    have ha : a < w + gs.length := hws a List.mem_cons_self
    have ha_dep : (depthsOf w gs).getD a 0 ≤ D := hdep a List.mem_cons_self
    rcases ih (fun u hu => hws u (List.mem_cons_of_mem a hu))
      (fun u hu => hdep u (List.mem_cons_of_mem a hu)) with
      ⟨gs1, out1, hlen1, hgood1, hcnt1, hout1, hdep1, hdpref1, hval1⟩
    have h2 := append_xor2 w gs1 a out1 hgood1 (by omega) hout1
    refine ⟨_, _, by omega, h2.2.1, by rw [h2.2.2.1, hcnt1], h2.2.2.2.1, ?_, ?_, ?_⟩
    · rw [h2.2.2.2.2.1, hdpref1 a ha]
      exact max_le ha_dep hdep1
    · intro k hk
      rw [h2.2.2.2.2.2.1 k (by omega), hdpref1 k hk]
    · intro x hx
      refine ⟨fun k hk => by rw [(h2.2.2.2.2.2.2 x hx).1 k (by omega), (hval1 x hx).1 k hk], ?_⟩
      rw [(h2.2.2.2.2.2.2 x hx).2, b2z_xor, (hval1 x hx).1 a ha, (hval1 x hx).2]
      simp

private lemma synth_depth1_quads (n m q : ℕ) (qs : List (Quad n m))
    (mask : Fin q → Fin qs.length → ZMod 2)
    (α : Fin q → Fin n → ZMod 2) (β : Fin q → Fin m → ZMod 2) :
    ∃ (C : Circuit) (tap : Fin q → ℕ),
      ReadsBack (n + m) C ∧
      (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧
      C.gates.countP nonlin ≤ qs.length ∧
      ∀ j : Fin q, (depthsOf (n + m) C.gates).getD (tap j) 0 ≤ 1 ∧
        ∀ (x : Fin n) (y : Fin m),
          b2z ((wiresOf C.gates (oneEach x y)).getD (tap j) false) =
            α j x + β j y + ∑ p : Fin qs.length, mask j p * evalQuad (qs.get p) x y := by
  classical
  have hbase_in : ∀ (gs : List Gate) (x : Fin n) (y : Fin m),
      (∀ i : Fin n, (wiresOf gs (oneEach x y)).getD i.val false = decide (i = x)) ∧
      (∀ j : Fin m, (wiresOf gs (oneEach x y)).getD (n + j.val) false = decide (j = y)) := by
    intro gs x y
    constructor
    · intro i
      have h1 := wiresOf_append_prefix [] gs (oneEach x y) i.val (by rw [oneEach_length]; simp; omega)
      change (wiresOf gs (oneEach x y)).getD i.val false = (oneEach x y).getD i.val false at h1
      rw [h1]
      simp only [oneEach]
      have hlen : (List.ofFn (fun i' : Fin n => decide (i' = x))).length = n := by simp
      rw [getD_append_left _ _ _ _ (by omega)]
      simp [List.getD_eq_getElem?_getD, List.getElem?_ofFn, i.isLt]
    · intro j
      have h1 := wiresOf_append_prefix [] gs (oneEach x y) (n + j.val) (by rw [oneEach_length]; simp)
      change (wiresOf gs (oneEach x y)).getD (n + j.val) false = (oneEach x y).getD (n + j.val) false at h1
      rw [h1]
      simp only [oneEach]
      have hlen : (List.ofFn (fun i' : Fin n => decide (i' = x))).length = n := by simp
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [hlen]; omega)]
      simp only [hlen, Nat.add_sub_cancel_left, List.getElem?_ofFn, dif_pos j.isLt, Option.getD_some]
  have hbase_dep : ∀ (gs : List Gate) (u : ℕ), u < n + m → (depthsOf (n + m) gs).getD u 0 = 0 := by
    intro gs u hu
    have h1 := depthsOf_append_prefix (n + m) [] gs u (by simp; omega)
    change (depthsOf (n + m) gs).getD u 0 = (List.replicate (n + m) 0).getD u 0 at h1
    rw [h1]
    simp [List.getD_eq_getElem?_getD, hu]
  have hbuild_aff : ∀ (gs : List Gate) (f : Fin n → ZMod 2) (h : Fin m → ZMod 2),
      goodGates (n + m) gs →
      ∃ (gs' : List Gate) (out : ℕ),
        gs.length ≤ gs'.length ∧ goodGates (n + m) gs' ∧
        gs'.countP nonlin = gs.countP nonlin ∧
        out < (n + m) + gs'.length ∧
        (depthsOf (n + m) gs').getD out 0 = 0 ∧
        (∀ k < (n + m) + gs.length, (depthsOf (n + m) gs').getD k 0 = (depthsOf (n + m) gs).getD k 0) ∧
        (∀ (x : Fin n) (y : Fin m),
          (∀ k < (n + m) + gs.length, (wiresOf gs' (oneEach x y)).getD k false = (wiresOf gs (oneEach x y)).getD k false) ∧
          b2z ((wiresOf gs' (oneEach x y)).getD out false) = f x + h y) := by
    intro gs f h hgood
    let wsX : List ℕ := ((List.finRange n).filter (fun i => decide (f i = 1))).map Fin.val
    let wsY : List ℕ := ((List.finRange m).filter (fun j => decide (h j = 1))).map (fun j => n + j.val)
    let ws := wsX ++ wsY
    have hws_lt : ∀ u ∈ ws, u < (n + m) + gs.length := by
      intro u hu
      simp only [ws, wsX, wsY, List.mem_append, List.mem_map, List.mem_filter] at hu
      rcases hu with ⟨i, _, rfl⟩ | ⟨j, _, rfl⟩ <;> omega
    have hws_dep : ∀ u ∈ ws, (depthsOf (n + m) gs).getD u 0 ≤ 0 := by
      intro u hu
      simp only [ws, wsX, wsY, List.mem_append, List.mem_map, List.mem_filter] at hu
      rcases hu with ⟨i, _, rfl⟩ | ⟨j, _, rfl⟩
      · rw [hbase_dep gs i.val (by omega)]
      · rw [hbase_dep gs (n + j.val) (by omega)]
    rcases exists_xorList (n + m) gs ws 0 hgood hws_lt hws_dep with
      ⟨gs', out, hlen, hgood', hcnt, hout, hdep, hdpref, hval⟩
    refine ⟨gs', out, hlen, hgood', hcnt, hout, by omega, hdpref, fun x y => ?_⟩
    have hv := hval (oneEach x y) (oneEach_length x y)
    refine ⟨hv.1, ?_⟩
    rw [hv.2]
    simp only [ws, List.map_append, List.sum_append]
    have hsumX : (wsX.map (fun u => b2z ((wiresOf gs (oneEach x y)).getD u false))).sum = f x := by
      have h1 : wsX.map (fun u => b2z ((wiresOf gs (oneEach x y)).getD u false)) =
          ((List.finRange n).filter (fun i => decide (f i = 1))).map (fun i => b2z (decide (i = x))) := by
        simp only [wsX, List.map_map]
        refine List.map_congr_left fun i _ => ?_
        dsimp only [Function.comp]
        rw [(hbase_in gs x y).1 i]
      rw [h1]
      have hnodup : ((List.finRange n).filter (fun i => decide (f i = 1))).Nodup :=
        (List.nodup_finRange n).filter _
      have htoF : ((List.finRange n).filter (fun i => decide (f i = 1))).toFinset =
          Finset.univ.filter (fun i : Fin n => f i = 1) := by ext i; simp
      rw [← List.sum_toFinset _ hnodup, htoF]
      by_cases hfx : f x = 1
      · rw [Finset.sum_eq_single x]
        · simp [hfx, b2z]
        · intro i _ hix; simp [hix, b2z]
        · intro h; exact (h (Finset.mem_filter.mpr ⟨Finset.mem_univ x, hfx⟩)).elim
      · have hfx0 : f x = 0 := by rcases zmod2_cases (f x) with h0 | h1; exact h0; exact (hfx h1).elim
        rw [hfx0]
        apply Finset.sum_eq_zero
        intro i hi
        have hne : i ≠ x := fun heq => hfx (heq ▸ (Finset.mem_filter.mp hi).2)
        simp [hne, b2z]
    have hsumY : (wsY.map (fun u => b2z ((wiresOf gs (oneEach x y)).getD u false))).sum = h y := by
      have h1 : wsY.map (fun u => b2z ((wiresOf gs (oneEach x y)).getD u false)) =
          ((List.finRange m).filter (fun j => decide (h j = 1))).map (fun j => b2z (decide (j = y))) := by
        simp only [wsY, List.map_map]
        refine List.map_congr_left fun j _ => ?_
        dsimp only [Function.comp]
        rw [(hbase_in gs x y).2 j]
      rw [h1]
      have hnodup : ((List.finRange m).filter (fun j => decide (h j = 1))).Nodup :=
        (List.nodup_finRange m).filter _
      have htoF : ((List.finRange m).filter (fun j => decide (h j = 1))).toFinset =
          Finset.univ.filter (fun j : Fin m => h j = 1) := by ext j; simp
      rw [← List.sum_toFinset _ hnodup, htoF]
      by_cases hhy : h y = 1
      · rw [Finset.sum_eq_single y]
        · simp [hhy, b2z]
        · intro j _ hjy; simp [hjy, b2z]
        · intro hm; exact (hm (Finset.mem_filter.mpr ⟨Finset.mem_univ y, hhy⟩)).elim
      · have hhy0 : h y = 0 := by rcases zmod2_cases (h y) with h0 | h1; exact h0; exact (hhy h1).elim
        rw [hhy0]
        apply Finset.sum_eq_zero
        intro j hj
        have hne : j ≠ y := fun heq => hhy (heq ▸ (Finset.mem_filter.mp hj).2)
        simp [hne, b2z]
    rw [hsumX, hsumY]
  have hstage1 : ∀ (k : ℕ) (hk : k ≤ qs.length),
      ∃ (gs : List Gate) (prodW : Fin k → ℕ),
        goodGates (n + m) gs ∧
        gs.countP nonlin = k ∧
        (∀ p : Fin k, prodW p < (n + m) + gs.length) ∧
        (∀ p : Fin k, (depthsOf (n + m) gs).getD (prodW p) 0 ≤ 1) ∧
        (∀ (p : Fin k) (x : Fin n) (y : Fin m),
          b2z ((wiresOf gs (oneEach x y)).getD (prodW p) false) =
            let qp := qs.get ⟨p.val, by omega⟩
            (qp.1 x + qp.2.2.2 y) * (qp.2.2.1 x + qp.2.1 y)) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨[], Fin.elim0, ⟨fun j hj => by simp at hj, fun _ h => by cases h⟩, rfl,
        fun p => Fin.elim0 p, fun p => Fin.elim0 p, fun p => Fin.elim0 p⟩
    | succ k ih =>
      intro hk
      rcases ih (by omega) with ⟨gs, prodW, hgood, hcnt, hlt, hdep, heval⟩
      let qk := qs.get ⟨k, by omega⟩
      rcases hbuild_aff gs qk.1 qk.2.2.2 hgood with
        ⟨gs1, w1, hlen1, hgood1, hcnt1, hw1, hdep1, hdpref1, hval1⟩
      rcases hbuild_aff gs1 qk.2.2.1 qk.2.1 hgood1 with
        ⟨gs2, w2, hlen2, hgood2, hcnt2, hw2, hdep2, hdpref2, hval2⟩
      have h3 := append_and2 (n + m) gs2 w1 w2 hgood2 (by omega) hw2
      let gs3 := gs2 ++ [⟨GateOp.and, [w1, w2]⟩]
      let out := (n + m) + gs2.length
      let prodW' : Fin (k + 1) → ℕ := fun p => if hp : p.val < k then prodW ⟨p.val, hp⟩ else out
      refine ⟨gs3, prodW', h3.2.1, by rw [h3.2.2.1, hcnt2, hcnt1, hcnt], ?_, ?_, ?_⟩
      · intro p
        by_cases hp : p.val < k
        · simp only [prodW', dif_pos hp]
          have h1 := hlt ⟨p.val, hp⟩
          have hlen3 : gs3.length = gs2.length + 1 := by simp [gs3]
          omega
        · simp only [prodW', dif_neg hp]; exact h3.2.2.2.1
      · intro p
        by_cases hp : p.val < k
        · simp only [prodW', dif_pos hp]
          rw [h3.2.2.2.2.2.1 _ (by have := hlt ⟨p.val, hp⟩; omega),
            hdpref2 _ (by have := hlt ⟨p.val, hp⟩; omega),
            hdpref1 _ (hlt ⟨p.val, hp⟩)]
          exact hdep ⟨p.val, hp⟩
        · simp only [prodW', dif_neg hp]
          rw [h3.2.2.2.2.1, hdpref2 w1 hw1, hdep1, hdep2]
          decide
      · intro p x y
        by_cases hp : p.val < k
        · simp only [prodW', dif_pos hp]
          have hltp := hlt ⟨p.val, hp⟩
          rw [(h3.2.2.2.2.2.2 (oneEach x y) (oneEach_length x y)).1 _ (by omega),
            (hval2 x y).1 _ (by omega), (hval1 x y).1 _ hltp]
          exact heval ⟨p.val, hp⟩ x y
        · have hpk : p.val = k := by omega
          simp only [prodW', dif_neg hp]
          rw [(h3.2.2.2.2.2.2 (oneEach x y) (oneEach_length x y)).2, b2z_and,
            (hval2 x y).1 w1 hw1, (hval1 x y).2, (hval2 x y).2]
          have hqeq : qs.get ⟨p.val, by omega⟩ = qk := by
            dsimp only [qk]; congr 1; exact Fin.ext (by dsimp only; omega)
          rw [hqeq]
  rcases hstage1 qs.length le_rfl with ⟨gs1, prodW, hgood1, hcnt1, hplt1, hpdep1, hpeval1⟩
  have hstage2 : ∀ (k : ℕ) (hk : k ≤ q),
      ∃ (gs : List Gate) (tap : Fin k → ℕ),
        gs1.length ≤ gs.length ∧
        goodGates (n + m) gs ∧
        gs.countP nonlin = qs.length ∧
        (∀ p : Fin qs.length, (depthsOf (n + m) gs).getD (prodW p) 0 ≤ 1) ∧
        (∀ (p : Fin qs.length) (x : Fin n) (y : Fin m),
          b2z ((wiresOf gs (oneEach x y)).getD (prodW p) false) =
            let qp := qs.get p
            (qp.1 x + qp.2.2.2 y) * (qp.2.2.1 x + qp.2.1 y)) ∧
        (∀ j : Fin k, tap j < (n + m) + gs.length) ∧
        (∀ j : Fin k, (depthsOf (n + m) gs).getD (tap j) 0 ≤ 1) ∧
        (∀ (j : Fin k) (x : Fin n) (y : Fin m),
          b2z ((wiresOf gs (oneEach x y)).getD (tap j) false) =
            α ⟨j.val, by omega⟩ x + β ⟨j.val, by omega⟩ y +
              ∑ p : Fin qs.length, mask ⟨j.val, by omega⟩ p * evalQuad (qs.get p) x y) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨gs1, Fin.elim0, le_rfl, hgood1, hcnt1, hpdep1, hpeval1,
        fun j => Fin.elim0 j, fun j => Fin.elim0 j, fun j => Fin.elim0 j⟩
    | succ k ih =>
      intro hk
      rcases ih (by omega) with ⟨gs, tap, hlen, hgood, hcnt, hpdep, hpeval, htlt, htdep, hteval⟩
      let jk : Fin q := ⟨k, by omega⟩
      let α' : Fin n → ZMod 2 := fun x =>
        α jk x + ∑ p : Fin qs.length, mask jk p * ((qs.get p).1 x * (qs.get p).2.2.1 x)
      let β' : Fin m → ZMod 2 := fun y =>
        β jk y + ∑ p : Fin qs.length, mask jk p * ((qs.get p).2.2.2 y * (qs.get p).2.1 y)
      rcases hbuild_aff gs α' β' hgood with
        ⟨gsA, wA, hlenA, hgoodA, hcntA, hwA, hdepA, hdprefA, hvalA⟩
      let maskPs : List (Fin qs.length) := (List.finRange qs.length).filter (fun p => decide (mask jk p = 1))
      let inW : List ℕ := wA :: maskPs.map prodW
      have hinW_lt : ∀ u ∈ inW, u < (n + m) + gsA.length := by
        intro u hu
        simp only [inW, List.mem_cons, List.mem_map] at hu
        rcases hu with rfl | ⟨p, _, rfl⟩
        · exact hwA
        · have := hplt1 p; omega
      have hinW_dep : ∀ u ∈ inW, (depthsOf (n + m) gsA).getD u 0 ≤ 1 := by
        intro u hu
        simp only [inW, List.mem_cons, List.mem_map] at hu
        rcases hu with rfl | ⟨p, _, rfl⟩
        · omega
        · rw [hdprefA (prodW p) (by have := hplt1 p; omega)]
          exact hpdep p
      rcases exists_xorList (n + m) gsA inW 1 hgoodA hinW_lt hinW_dep with
        ⟨gsB, out, hlenB, hgoodB, hcntB, houtB, hdepB, hdprefB, hvalB⟩
      let tap' : Fin (k + 1) → ℕ := fun j => if hj : j.val < k then tap ⟨j.val, hj⟩ else out
      refine ⟨gsB, tap', by omega, hgoodB, by rw [hcntB, hcntA, hcnt], ?_, ?_, ?_, ?_, ?_⟩
      · intro p
        have hltp := hplt1 p
        rw [hdprefB (prodW p) (by omega), hdprefA (prodW p) (by omega)]
        exact hpdep p
      · intro p x y
        have hltp := hplt1 p
        rw [(hvalB (oneEach x y) (oneEach_length x y)).1 (prodW p) (by omega),
          (hvalA x y).1 (prodW p) (by omega)]
        exact hpeval p x y
      · intro j
        by_cases hj : j.val < k
        · simp only [tap', dif_pos hj]; have := htlt ⟨j.val, hj⟩; omega
        · simp only [tap', dif_neg hj]; exact houtB
      · intro j
        by_cases hj : j.val < k
        · simp only [tap', dif_pos hj]
          have hltj := htlt ⟨j.val, hj⟩
          rw [hdprefB _ (by omega), hdprefA _ hltj]
          exact htdep ⟨j.val, hj⟩
        · simp only [tap', dif_neg hj]; exact hdepB
      · intro j x y
        by_cases hj : j.val < k
        · simp only [tap', dif_pos hj]
          have hltj := htlt ⟨j.val, hj⟩
          rw [(hvalB (oneEach x y) (oneEach_length x y)).1 _ (by omega),
            (hvalA x y).1 _ hltj]
          exact hteval ⟨j.val, hj⟩ x y
        · have hjk_eq : (⟨j.val, by omega⟩ : Fin q) = jk := Fin.ext (by dsimp only [jk]; omega)
          simp only [tap', dif_neg hj, hjk_eq]
          rw [(hvalB (oneEach x y) (oneEach_length x y)).2]
          simp only [inW, List.map_cons, List.sum_cons, List.map_map]
          rw [(hvalA x y).2]
          have hmap_eq : maskPs.map ((fun u => b2z ((wiresOf gsA (oneEach x y)).getD u false)) ∘ prodW) =
              maskPs.map (fun p =>
                let qp := qs.get p
                (qp.1 x + qp.2.2.2 y) * (qp.2.2.1 x + qp.2.1 y)) := by
            refine List.map_congr_left fun p _ => ?_
            dsimp only [Function.comp]
            have hltp := hplt1 p
            rw [(hvalA x y).1 (prodW p) (by omega)]
            exact hpeval p x y
          rw [hmap_eq]
          have hnodup : maskPs.Nodup := (List.nodup_finRange qs.length).filter _
          have htoF : maskPs.toFinset = Finset.univ.filter (fun p : Fin qs.length => mask jk p = 1) := by
            ext p; simp [maskPs]
          rw [← List.sum_toFinset _ hnodup, htoF]
          have hfilt_sum : ∑ p ∈ Finset.univ.filter (fun p : Fin qs.length => mask jk p = 1),
              ((qs.get p).1 x + (qs.get p).2.2.2 y) * ((qs.get p).2.2.1 x + (qs.get p).2.1 y) =
              ∑ p : Fin qs.length, mask jk p *
                (((qs.get p).1 x + (qs.get p).2.2.2 y) * ((qs.get p).2.2.1 x + (qs.get p).2.1 y)) := by
            rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun p : Fin qs.length => mask jk p = 1)]
            have hleft : ∑ p ∈ Finset.univ.filter (fun p : Fin qs.length => mask jk p = 1),
                mask jk p * (((qs.get p).1 x + (qs.get p).2.2.2 y) * ((qs.get p).2.2.1 x + (qs.get p).2.1 y)) =
                ∑ p ∈ Finset.univ.filter (fun p : Fin qs.length => mask jk p = 1),
                  ((qs.get p).1 x + (qs.get p).2.2.2 y) * ((qs.get p).2.2.1 x + (qs.get p).2.1 y) := by
              refine Finset.sum_congr rfl fun p hp => ?_
              rw [(Finset.mem_filter.mp hp).2, one_mul]
            have hright : ∑ p ∈ Finset.univ.filter (fun p : Fin qs.length => ¬ mask jk p = 1),
                mask jk p * (((qs.get p).1 x + (qs.get p).2.2.2 y) * ((qs.get p).2.2.1 x + (qs.get p).2.1 y)) = 0 := by
              apply Finset.sum_eq_zero
              intro p hp
              have hne : mask jk p ≠ 1 := (Finset.mem_filter.mp hp).2
              have h0 : mask jk p = 0 := by rcases zmod2_cases (mask jk p) with h | h; exact h; exact (hne h).elim
              rw [h0, zero_mul]
            rw [hleft, hright, add_zero]
          rw [hfilt_sum]
          dsimp only [α', β']
          have hcomb : (α jk x + ∑ p : Fin qs.length, mask jk p * ((qs.get p).1 x * (qs.get p).2.2.1 x)) +
              (β jk y + ∑ p : Fin qs.length, mask jk p * ((qs.get p).2.2.2 y * (qs.get p).2.1 y)) +
              ∑ p : Fin qs.length, mask jk p *
                (((qs.get p).1 x + (qs.get p).2.2.2 y) * ((qs.get p).2.2.1 x + (qs.get p).2.1 y)) =
              α jk x + β jk y + ∑ p : Fin qs.length, mask jk p * evalQuad (qs.get p) x y := by
            have hsum_eq : (∑ p : Fin qs.length, mask jk p * ((qs.get p).1 x * (qs.get p).2.2.1 x)) +
                (∑ p : Fin qs.length, mask jk p * ((qs.get p).2.2.2 y * (qs.get p).2.1 y)) +
                ∑ p : Fin qs.length, mask jk p *
                  (((qs.get p).1 x + (qs.get p).2.2.2 y) * ((qs.get p).2.2.1 x + (qs.get p).2.1 y)) =
                ∑ p : Fin qs.length, mask jk p * evalQuad (qs.get p) x y := by
              rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
              refine Finset.sum_congr rfl fun p _ => ?_
              dsimp only [evalQuad]
              have h1 := zmod2_add_self (mask jk p * ((qs.get p).1 x * (qs.get p).2.2.1 x))
              have h2 := zmod2_add_self (mask jk p * ((qs.get p).2.2.2 y * (qs.get p).2.1 y))
              calc mask jk p * ((qs.get p).1 x * (qs.get p).2.2.1 x) +
                    mask jk p * ((qs.get p).2.2.2 y * (qs.get p).2.1 y) +
                    mask jk p * (((qs.get p).1 x + (qs.get p).2.2.2 y) * ((qs.get p).2.2.1 x + (qs.get p).2.1 y))
                  = (mask jk p * ((qs.get p).1 x * (qs.get p).2.2.1 x) +
                      mask jk p * ((qs.get p).1 x * (qs.get p).2.2.1 x)) +
                    (mask jk p * ((qs.get p).2.2.2 y * (qs.get p).2.1 y) +
                      mask jk p * ((qs.get p).2.2.2 y * (qs.get p).2.1 y)) +
                    mask jk p * ((qs.get p).1 x * (qs.get p).2.1 y + (qs.get p).2.2.1 x * (qs.get p).2.2.2 y) := by ring
                _ = mask jk p * ((qs.get p).1 x * (qs.get p).2.1 y + (qs.get p).2.2.1 x * (qs.get p).2.2.2 y) := by
                      rw [h1, h2, zero_add, zero_add]
            calc (α jk x + ∑ p : Fin qs.length, mask jk p * ((qs.get p).1 x * (qs.get p).2.2.1 x)) +
                  (β jk y + ∑ p : Fin qs.length, mask jk p * ((qs.get p).2.2.2 y * (qs.get p).2.1 y)) +
                  ∑ p : Fin qs.length, mask jk p *
                    (((qs.get p).1 x + (qs.get p).2.2.2 y) * ((qs.get p).2.2.1 x + (qs.get p).2.1 y))
                = α jk x + β jk y +
                    ((∑ p : Fin qs.length, mask jk p * ((qs.get p).1 x * (qs.get p).2.2.1 x)) +
                      (∑ p : Fin qs.length, mask jk p * ((qs.get p).2.2.2 y * (qs.get p).2.1 y)) +
                      ∑ p : Fin qs.length, mask jk p *
                        (((qs.get p).1 x + (qs.get p).2.2.2 y) * ((qs.get p).2.2.1 x + (qs.get p).2.1 y))) := by ring
              _ = α jk x + β jk y + ∑ p : Fin qs.length, mask jk p * evalQuad (qs.get p) x y := by rw [hsum_eq]
          exact hcomb
  rcases hstage2 q le_rfl with ⟨gs2, tap, _, hgood2, hcnt2, _, _, _, htdep2, hteval2⟩
  refine ⟨⟨gs2, 0⟩, tap, hgood2.1, hgood2.2, le_of_eq hcnt2, fun j => ⟨htdep2 j, hteval2 j⟩⟩

private def pullQuad {n m k : ℕ}
    (coefA : Fin (k + 1) → Fin n → ZMod 2)
    (coefB : Fin (k + 1) → Fin m → ZMod 2)
    (q : Quad (n + 1) (m + 1)) : Quad (k + 1) (k + 1) :=
  (fun x => ∑ idx : Fin n, coefA x idx * (q.1 idx.succ + q.1 0),
   fun y => ∑ idy : Fin m, coefB y idy * (q.2.1 idy.succ + q.2.1 0),
   fun x => ∑ idx : Fin n, coefA x idx * (q.2.2.1 idx.succ + q.2.2.1 0),
   fun y => ∑ idy : Fin m, coefB y idy * (q.2.2.2 idy.succ + q.2.2.2 0))

private lemma pullZ_evalQuad {n m k : ℕ}
    (coefA : Fin (k + 1) → Fin n → ZMod 2)
    (coefB : Fin (k + 1) → Fin m → ZMod 2)
    (q : Quad (n + 1) (m + 1)) (x y : Fin (k + 1)) :
    ∑ idx : Fin n, ∑ idy : Fin m, coefA x idx * coefB y idy * deltaMat (evalQuad q) idx idy =
      evalQuad (pullQuad coefA coefB q) x y := by
  have hfact : ∀ (u : Fin n → ZMod 2) (v : Fin m → ZMod 2),
      ∑ idx : Fin n, ∑ idy : Fin m, coefA x idx * coefB y idy * (u idx * v idy) =
        (∑ idx : Fin n, coefA x idx * u idx) * (∑ idy : Fin m, coefB y idy * v idy) := by
    intro u v
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun idx _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun idy _ => by ring
  have hadd : ∀ (idx : Fin n) (idy : Fin m),
      coefA x idx * coefB y idy * deltaMat (evalQuad q) idx idy =
        coefA x idx * coefB y idy * ((q.1 idx.succ + q.1 0) * (q.2.1 idy.succ + q.2.1 0)) +
        coefA x idx * coefB y idy * ((q.2.2.1 idx.succ + q.2.2.1 0) * (q.2.2.2 idy.succ + q.2.2.2 0)) := by
    intro idx idy
    rw [deltaMat_quad, mul_add]
  simp_rw [hadd, Finset.sum_add_distrib]
  rw [hfact, hfact]
  rfl

private lemma sq_sum_le_card_mul_sum_sq {α : Type*} (s : Finset α) (f : α → ℕ) :
    (∑ i ∈ s, f i) ^ 2 ≤ s.card * ∑ i ∈ s, (f i) ^ 2 := by
  zify
  have h0 : (0 : ℤ) ≤ ∑ i ∈ s, ∑ j ∈ s, ((f i : ℤ) - f j) ^ 2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  have hexp : ∑ i ∈ s, ∑ j ∈ s, ((f i : ℤ) - f j) ^ 2 =
      2 * (s.card : ℤ) * (∑ i ∈ s, (f i : ℤ) ^ 2) - 2 * (∑ i ∈ s, (f i : ℤ)) ^ 2 := by
    have hpt : ∀ i j : α, ((f i : ℤ) - f j) ^ 2 = (f i : ℤ) ^ 2 + (f j : ℤ) ^ 2 - 2 * ((f i : ℤ) * f j) := by
      intro i j; ring
    simp_rw [hpt, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    have h1 : ∑ i ∈ s, ∑ _j ∈ s, (f i : ℤ) ^ 2 = (s.card : ℤ) * ∑ i ∈ s, (f i : ℤ) ^ 2 := by
      simp [Finset.sum_const, Finset.mul_sum]
    have h2 : ∑ _i ∈ s, ∑ j ∈ s, (f j : ℤ) ^ 2 = (s.card : ℤ) * ∑ j ∈ s, (f j : ℤ) ^ 2 := by
      simp [Finset.sum_const]
    have h3 : ∑ i ∈ s, ∑ j ∈ s, (2 : ℤ) * ((f i : ℤ) * f j) = 2 * (∑ i ∈ s, (f i : ℤ)) ^ 2 := by
      rw [sq, Finset.sum_mul]
      simp_rw [Finset.mul_sum]
    rw [h1, h2, h3]; ring
  linarith

private lemma card_eval_zero_exact {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {r c : ℕ} (hr : 0 < r) (hc : 0 < c) (A : Matrix (Fin r) (Fin c) K) :
    let Q := Fintype.card K
    Q * ((Finset.univ : Finset ((Fin r → K) × (Fin c → K))).filter
      (fun ab => ∑ i : Fin r, ∑ j : Fin c, ab.1 i * A i j * ab.2 j = 0)).card =
      Q ^ (r + c) + Q ^ (r + c - A.rank) * (Q - 1) := by
  classical
  intro Q
  have hQ_pos : 1 ≤ Q := Fintype.card_pos
  have hpart : ((Finset.univ : Finset ((Fin r → K) × (Fin c → K))).filter
      (fun ab => ∑ i : Fin r, ∑ j : Fin c, ab.1 i * A i j * ab.2 j = 0)).card =
      ∑ b : Fin c → K,
        ((Finset.univ : Finset (Fin r → K)).filter
          (fun a => ∑ i : Fin r, a i * A.mulVec b i = 0)).card := by
    have hbiU : (Finset.univ : Finset ((Fin r → K) × (Fin c → K))).filter
        (fun ab => ∑ i : Fin r, ∑ j : Fin c, ab.1 i * A i j * ab.2 j = 0) =
        (Finset.univ : Finset (Fin c → K)).biUnion (fun b =>
          ((Finset.univ : Finset (Fin r → K)).filter
            (fun a => ∑ i : Fin r, a i * A.mulVec b i = 0)).image (fun a => (a, b))) := by
      ext ⟨a, b⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion, Finset.mem_image,
        Prod.mk.injEq]
      have heq_sum : (∑ i : Fin r, ∑ j : Fin c, a i * A i j * b j) = ∑ i : Fin r, a i * A.mulVec b i := by
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
      constructor
      · intro h; exact ⟨b, a, heq_sum ▸ h, rfl, rfl⟩
      · rintro ⟨b', a', ha', rfl, rfl⟩; exact heq_sum.symm ▸ ha'
    rw [hbiU, Finset.card_biUnion]
    · refine Finset.sum_congr rfl fun b _ => ?_
      exact Finset.card_image_of_injective _ (fun a1 a2 h => (Prod.mk.inj h).1)
    · intro b1 _ b2 _ hne
      change Disjoint _ _
      rw [Finset.disjoint_left]
      intro p hp1 hp2
      rcases Finset.mem_image.mp hp1 with ⟨a1, _, rfl⟩
      rcases Finset.mem_image.mp hp2 with ⟨a2, _, h⟩
      exact hne (Prod.mk.inj h).2.symm
  have hfiber_zero : ∀ b : Fin c → K, A.mulVec b = 0 →
      ((Finset.univ : Finset (Fin r → K)).filter
        (fun a => ∑ i : Fin r, a i * A.mulVec b i = 0)).card = Q ^ r := by
    intro b hb
    have hall : (Finset.univ : Finset (Fin r → K)).filter (fun a => ∑ i : Fin r, a i * A.mulVec b i = 0) =
        Finset.univ := by
      ext a; simp [hb]
    rw [hall, Finset.card_univ, Fintype.card_fun, Fintype.card_fin]
  have hfiber_ne : ∀ b : Fin c → K, A.mulVec b ≠ 0 →
      ((Finset.univ : Finset (Fin r → K)).filter
        (fun a => ∑ i : Fin r, a i * A.mulVec b i = 0)).card = Q ^ (r - 1) := by
    intro b hb
    let φ : (Fin r → K) →ₗ[K] K :=
      { toFun := fun a => ∑ i : Fin r, a i * A.mulVec b i
        map_add' := fun a1 a2 => by simp [add_mul, Finset.sum_add_distrib]
        map_smul' := fun s a => by simp [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc] }
    have hsurj : Function.Surjective φ := by
      have hex : ∃ i0 : Fin r, A.mulVec b i0 ≠ 0 := by
        by_contra hall; push Not at hall; exact hb (funext hall)
      rcases hex with ⟨i0, hi0⟩
      intro z
      refine ⟨fun i => if i = i0 then z * (A.mulVec b i0)⁻¹ else 0, ?_⟩
      change ∑ i : Fin r, (if i = i0 then z * (A.mulVec b i0)⁻¹ else 0) * A.mulVec b i = z
      rw [Finset.sum_eq_single i0]
      · simp [inv_mul_cancel_right₀ hi0]
      · intro i _ hne; simp [hne]
      · intro h; exact (h (Finset.mem_univ i0)).elim
    have hker_dim : Module.finrank K ↥(LinearMap.ker φ) = r - 1 := by
      have hrk := LinearMap.finrank_range_add_finrank_ker φ
      rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self,
        Module.finrank_pi, Fintype.card_fin] at hrk
      omega
    have hcard_ker : Fintype.card ↥(LinearMap.ker φ) = Q ^ (r - 1) := by
      have h1 := Module.card_eq_pow_finrank (K := K) (V := LinearMap.ker φ)
      rwa [hker_dim] at h1
    have hbij : ((Finset.univ : Finset (Fin r → K)).filter
        (fun a => ∑ i : Fin r, a i * A.mulVec b i = 0)).card = Fintype.card ↥(LinearMap.ker φ) := by
      rw [← Finset.card_univ]
      refine Finset.card_bij (fun a ha => ⟨a, (Finset.mem_filter.mp ha).2⟩)
        (fun _ _ => Finset.mem_univ _)
        (fun _ _ _ _ h => congrArg Subtype.val h)
        (fun u _ => ⟨u.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, u.2⟩, Subtype.ext rfl⟩)
    rw [hbij, hcard_ker]
  have hkerA_dim : Module.finrank K ↥(LinearMap.ker A.mulVecLin) = c - A.rank := by
    have hrk := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
    rw [Module.finrank_pi, Fintype.card_fin] at hrk
    change A.rank + Module.finrank K ↥(LinearMap.ker A.mulVecLin) = c at hrk
    omega
  have hrk_le_c : A.rank ≤ c := by
    have hrk := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
    rw [Module.finrank_pi, Fintype.card_fin] at hrk
    change A.rank + Module.finrank K ↥(LinearMap.ker A.mulVecLin) = c at hrk
    omega
  let K0 := (Finset.univ : Finset (Fin c → K)).filter (fun b => A.mulVec b = 0)
  have hK0_card : K0.card = Q ^ (c - A.rank) := by
    have hbij : K0.card = Fintype.card ↥(LinearMap.ker A.mulVecLin) := by
      rw [← Finset.card_univ]
      refine Finset.card_bij (fun b hb => ⟨b, (Finset.mem_filter.mp hb).2⟩)
        (fun _ _ => Finset.mem_univ _)
        (fun _ _ _ _ h => congrArg Subtype.val h)
        (fun u _ => ⟨u.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, u.2⟩, Subtype.ext rfl⟩)
    have h1 := Module.card_eq_pow_finrank (K := K) (V := LinearMap.ker A.mulVecLin)
    rw [hbij, h1, hkerA_dim]
  let K1 := (Finset.univ : Finset (Fin c → K)).filter (fun b => ¬ A.mulVec b = 0)
  have hK1_card : K0.card + K1.card = Q ^ c := by
    have hunion : K0 ∪ K1 = Finset.univ := by
      ext b; simp only [K0, K1, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      exact em _
    have hdisj : Disjoint K0 K1 := by
      rw [Finset.disjoint_left]
      intro b h0 h1
      exact (Finset.mem_filter.mp h1).2 (Finset.mem_filter.mp h0).2
    have h := congrArg Finset.card hunion
    rw [Finset.card_union_of_disjoint hdisj, Finset.card_univ, Fintype.card_fun, Fintype.card_fin] at h
    exact h
  have hsum_val : ((Finset.univ : Finset ((Fin r → K) × (Fin c → K))).filter
      (fun ab => ∑ i : Fin r, ∑ j : Fin c, ab.1 i * A i j * ab.2 j = 0)).card =
      K0.card * Q ^ r + K1.card * Q ^ (r - 1) := by
    rw [hpart, ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun b : Fin c → K => A.mulVec b = 0)]
    have h0 : ∑ b ∈ K0, ((Finset.univ : Finset (Fin r → K)).filter
        (fun a => ∑ i : Fin r, a i * A.mulVec b i = 0)).card = K0.card * Q ^ r := by
      calc ∑ b ∈ K0, _ = ∑ _b ∈ K0, Q ^ r := Finset.sum_congr rfl fun b hb => hfiber_zero b (Finset.mem_filter.mp hb).2
        _ = K0.card * Q ^ r := by simp
    have h1 : ∑ b ∈ K1, ((Finset.univ : Finset (Fin r → K)).filter
        (fun a => ∑ i : Fin r, a i * A.mulVec b i = 0)).card = K1.card * Q ^ (r - 1) := by
      calc ∑ b ∈ K1, _ = ∑ _b ∈ K1, Q ^ (r - 1) := Finset.sum_congr rfl fun b hb => hfiber_ne b (Finset.mem_filter.mp hb).2
        _ = K1.card * Q ^ (r - 1) := by simp
    exact congrArg₂ (· + ·) h0 h1
  rw [hsum_val]
  have hQr : Q * Q ^ (r - 1) = Q ^ r := by
    have : r = (r - 1) + 1 := by omega
    conv_rhs => rw [this, pow_succ, mul_comm]
  have hQrc : Q ^ (c - A.rank) * Q ^ r = Q ^ (r + c - A.rank) := by
    rw [← pow_add]; congr 1; omega
  have hQrc2 : Q ^ c * Q ^ r = Q ^ (r + c) := by
    rw [← pow_add]; congr 1; omega
  have hcalc : Q * (K0.card * Q ^ r + K1.card * Q ^ (r - 1)) =
      K0.card * Q ^ r * Q + K1.card * Q ^ r := by
    calc Q * (K0.card * Q ^ r + K1.card * Q ^ (r - 1))
        = K0.card * Q ^ r * Q + K1.card * (Q * Q ^ (r - 1)) := by ring
      _ = K0.card * Q ^ r * Q + K1.card * Q ^ r := by rw [hQr]
  rw [hcalc]
  zify [hQ_pos] at hK1_card hK0_card hQrc hQrc2 ⊢
  have hK1_z : (K1.card : ℤ) = (Q : ℤ) ^ c - (K0.card : ℤ) := by linarith
  rw [hK1_z, hK0_card]
  calc (Q : ℤ) ^ (c - A.rank) * (Q : ℤ) ^ r * (Q : ℤ) + ((Q : ℤ) ^ c - (Q : ℤ) ^ (c - A.rank)) * (Q : ℤ) ^ r
      = (Q : ℤ) ^ c * (Q : ℤ) ^ r + ((Q : ℤ) ^ (c - A.rank) * (Q : ℤ) ^ r) * ((Q : ℤ) - 1) := by ring
    _ = (Q : ℤ) ^ (r + c) + (Q : ℤ) ^ (r + c - A.rank) * ((Q : ℤ) - 1) := by rw [hQrc, hQrc2]

private lemma matrix_eq_zero_of_rank_zero {K : Type*} [Field K] {r c : ℕ}
    (A : Matrix (Fin r) (Fin c) K) (h : A.rank = 0) : A = 0 := by
  have hbot : LinearMap.range A.mulVecLin = ⊥ :=
    Submodule.finrank_eq_zero.mp h
  ext i j
  have hmem : A.mulVec (fun l => if l = j then (1 : K) else 0) ∈ LinearMap.range A.mulVecLin :=
    ⟨fun l => if l = j then 1 else 0, rfl⟩
  rw [hbot, Submodule.mem_bot] at hmem
  have hi := congr_fun hmem i
  simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at hi
  rw [Finset.sum_eq_single j] at hi
  · simpa using hi
  · intro l _ hne; simp [hne]
  · intro hm; exact (hm (Finset.mem_univ j)).elim

private lemma exists_good_ab_cover (K : Type) [Field K] [DecidableEq K] [Algebra (ZMod 2) K]
    [FiniteDimensional (ZMod 2) K]
    (k : ℕ) (basis : Module.Basis (Fin k) (ZMod 2) K) (bit : K →ₗ[ZMod 2] ZMod 2) (hbit : bit ≠ 0)
    (r c : ℕ) (hr : 0 < r) (hc : 0 < c)
    (D : Finset (Matrix (Fin r) (Fin c) K))
    (hineq :
      (((D.product D).filter (fun pair => (pair.1 - pair.2).rank = 1)).card + D.card * (2 ^ k + 1)) *
        (2 ^ k - 1) ^ 2 < D.card ^ 2 * ((2 ^ k) ^ 2 - 2 ^ k + 1)) :
    ∃ (a : Fin r → K) (b : Fin c → K),
      ∀ z : K, ∃ M ∈ D, ∃ N ∈ D, z = (∑ i, ∑ j, a i * M i j * b j) + (∑ i, ∑ j, a i * N i j * b j) := by
  classical
  let Q := 2 ^ k
  let Mat := Matrix (Fin r) (Fin c) K
  let eval : (Fin r → K) → (Fin c → K) → Mat → K := fun a b M => ∑ i, ∑ j, a i * M i j * b j
  let m := D.card
  let e := ((D.product D).filter (fun pair => (pair.1 - pair.2).rank = 1)).card
  letI : Fintype K := Fintype.ofEquiv (Fin k → ZMod 2) basis.equivFun.symm
  have hcardK : Fintype.card K = Q := by
    have h1 := Fintype.card_congr basis.equivFun.toEquiv
    simpa [Q, Fintype.card_fun, ZMod.card, Fintype.card_fin] using h1
  have hk_pos : 0 < k := by
    by_contra hk0
    have hkz : k = 0 := by omega
    subst hkz
    apply hbit
    apply LinearMap.ext
    intro x
    have hx0 : x = 0 := by
      have h1 := (basis.sum_repr x).symm
      simpa using h1
    rw [hx0, map_zero, LinearMap.zero_apply]
  have hQ_ge2 : 2 ≤ Q := by
    have h1 : 2 ^ 1 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk_pos
    simpa [Q] using h1
  have hm_pos : 0 < m := by
    by_contra hm0
    have hmz : m = 0 := by omega
    change (e + m * (Q + 1)) * (Q - 1) ^ 2 < m ^ 2 * (Q ^ 2 - Q + 1) at hineq
    rw [hmz] at hineq
    simp at hineq
  have hK_add_self : ∀ x : K, x + x = 0 := by
    have h2 : (1 : K) + 1 = 0 := by
      have h := map_add (algebraMap (ZMod 2) K) 1 1
      rw [show (1 : ZMod 2) + 1 = 0 by decide, map_zero, map_one] at h
      exact h.symm
    intro x
    calc x + x = (1 + 1) * x := by ring
      _ = 0 := by rw [h2, zero_mul]
  let Z : Mat → ℕ := fun A =>
    ((Finset.univ : Finset ((Fin r → K) × (Fin c → K))).filter (fun ab => eval ab.1 ab.2 A = 0)).card
  have hZ_exact : ∀ A : Mat, Q * Z A = Q ^ (r + c) + Q ^ (r + c - A.rank) * (Q - 1) := by
    intro A
    have h := card_eval_zero_exact hr hc A
    simpa [Z, eval, hcardK] using h
  have hZ0 : Q ^ 3 * Z 0 = Q ^ (r + c) * Q ^ 3 := by
    have h := hZ_exact 0
    have hr0 : (0 : Mat).rank = 0 := by
      change Module.finrank K ↥(LinearMap.range (0 : Mat).mulVecLin) = 0
      simp [Matrix.mulVecLin_zero]
    rw [hr0, Nat.sub_zero] at h
    have h1 : Q ^ 3 * Z 0 = Q ^ 2 * (Q * Z 0) := by ring
    rw [h1, h]
    have hQ1 : 1 ≤ Q := by omega
    zify [hQ1]; ring
  have hZ1 : ∀ A : Mat, A.rank = 1 → Q ^ 3 * Z A = Q ^ (r + c) * (Q * (2 * Q - 1)) := by
    intro A hA1
    have h := hZ_exact A
    rw [hA1] at h
    have h1 : Q ^ 3 * Z A = Q ^ 2 * (Q * Z A) := by ring
    rw [h1, h]
    have hpow : Q ^ 2 * Q ^ (r + c - 1) = Q ^ (r + c) * Q := by
      rw [← pow_add, ← pow_succ]; congr 1; omega
    have hQ1 : 1 ≤ Q := by omega
    have h2Q1 : 1 ≤ 2 * Q := by omega
    zify [hQ1, h2Q1] at hpow ⊢
    calc (Q : ℤ) ^ 2 * ((Q : ℤ) ^ (r + c) + (Q : ℤ) ^ (r + c - 1) * ((Q : ℤ) - 1))
        = (Q : ℤ) ^ (r + c) * (Q : ℤ) ^ 2 + ((Q : ℤ) ^ 2 * (Q : ℤ) ^ (r + c - 1)) * ((Q : ℤ) - 1) := by ring
      _ = (Q : ℤ) ^ (r + c) * (Q : ℤ) ^ 2 + ((Q : ℤ) ^ (r + c) * (Q : ℤ)) * ((Q : ℤ) - 1) := by rw [hpow]
      _ = (Q : ℤ) ^ (r + c) * ((Q : ℤ) * (2 * (Q : ℤ) - 1)) := by ring
  have hZ2 : ∀ A : Mat, 2 ≤ A.rank → Q ^ 3 * Z A ≤ Q ^ (r + c) * (Q ^ 2 + Q - 1) := by
    intro A hA2
    have h := hZ_exact A
    have h1 : Q ^ 3 * Z A = Q ^ 2 * (Q * Z A) := by ring
    rw [h1, h]
    have hpow_le : Q ^ 2 * Q ^ (r + c - A.rank) ≤ Q ^ (r + c) := by
      rw [← pow_add]
      exact Nat.pow_le_pow_right (by omega) (by omega)
    have hQ1 : 1 ≤ Q := by omega
    have hQ2 : 1 ≤ Q ^ 2 + Q := by nlinarith
    zify [hQ1, hQ2] at hpow_le ⊢
    have hQ1z : (0 : ℤ) ≤ (Q : ℤ) - 1 := by omega
    have hmul : (Q : ℤ) ^ 2 * (Q : ℤ) ^ (r + c - A.rank) * ((Q : ℤ) - 1) ≤
        (Q : ℤ) ^ (r + c) * ((Q : ℤ) - 1) := mul_le_mul_of_nonneg_right hpow_le hQ1z
    linarith
  let P0 := (D.product D).filter (fun p => p.1 = p.2)
  let P1 := (D.product D).filter (fun p => (p.1 - p.2).rank = 1)
  let P2 := (D.product D).filter (fun p => p.1 ≠ p.2 ∧ (p.1 - p.2).rank ≠ 1)
  have hP0_card : P0.card = m := by
    refine Finset.card_bij (fun p _ => p.1)
      (fun p hp => (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1)
      (fun p1 hp1 p2 hp2 heq => Prod.ext heq ((Finset.mem_filter.mp hp1).2.symm.trans (heq.trans (Finset.mem_filter.mp hp2).2)))
      (fun M hM => ⟨(M, M), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hM, hM⟩, rfl⟩, rfl⟩)
  have hP1_card : P1.card = e := rfl
  have hpart_DD : D.product D = P0 ∪ P1 ∪ P2 := by
    ext p
    simp only [P0, P1, P2, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hp
      by_cases h1 : p.1 = p.2
      · exact Or.inl (Or.inl ⟨hp, h1⟩)
      · by_cases h2 : (p.1 - p.2).rank = 1
        · exact Or.inl (Or.inr ⟨hp, h2⟩)
        · exact Or.inr ⟨hp, h1, h2⟩
    · rintro ((⟨hp, _⟩ | ⟨hp, _⟩) | ⟨hp, _⟩) <;> exact hp
  have hdisj01 : Disjoint P0 P1 := by
    rw [Finset.disjoint_left]
    intro p hp0 hp1
    have h1 := (Finset.mem_filter.mp hp0).2
    have h2 := (Finset.mem_filter.mp hp1).2
    rw [h1, sub_self] at h2
    have hr0 : (0 : Mat).rank = 0 := by
      change Module.finrank K ↥(LinearMap.range (0 : Mat).mulVecLin) = 0
      simp [Matrix.mulVecLin_zero]
    omega
  have hdisj01_2 : Disjoint (P0 ∪ P1) P2 := by
    rw [Finset.disjoint_left]
    intro p hp01 hp2
    rcases (Finset.mem_filter.mp hp2).2 with ⟨hne, hrne⟩
    rcases Finset.mem_union.mp hp01 with hp0 | hp1
    · exact hne (Finset.mem_filter.mp hp0).2
    · exact hrne (Finset.mem_filter.mp hp1).2
  have hcard_DD : m + e + P2.card = m ^ 2 := by
    have h1 := congrArg Finset.card hpart_DD
    rw [Finset.card_union_of_disjoint hdisj01_2, Finset.card_union_of_disjoint hdisj01,
      hP0_card, hP1_card] at h1
    have hprod : (D.product D).card = m * m := Finset.card_product D D
    rw [hprod] at h1
    rw [sq]; exact h1.symm
  have hsum_Z_le : Q ^ 3 * ∑ p ∈ D.product D, Z (p.1 - p.2) < Q ^ (r + c) * (2 * m ^ 2 * Q ^ 2) := by
    rw [hpart_DD, Finset.sum_union hdisj01_2, Finset.sum_union hdisj01, mul_add, mul_add]
    have hS0 : Q ^ 3 * ∑ p ∈ P0, Z (p.1 - p.2) = Q ^ (r + c) * (m * Q ^ 3) := by
      rw [Finset.mul_sum]
      have hcongr : ∑ p ∈ P0, Q ^ 3 * Z (p.1 - p.2) = ∑ _p ∈ P0, Q ^ (r + c) * Q ^ 3 :=
        Finset.sum_congr rfl fun p hp => by rw [(Finset.mem_filter.mp hp).2, sub_self, hZ0]
      rw [hcongr, Finset.sum_const, smul_eq_mul, hP0_card]; ring
    have hS1 : Q ^ 3 * ∑ p ∈ P1, Z (p.1 - p.2) = Q ^ (r + c) * (e * (Q * (2 * Q - 1))) := by
      rw [Finset.mul_sum]
      have hcongr : ∑ p ∈ P1, Q ^ 3 * Z (p.1 - p.2) = ∑ _p ∈ P1, Q ^ (r + c) * (Q * (2 * Q - 1)) :=
        Finset.sum_congr rfl fun p hp => hZ1 _ (Finset.mem_filter.mp hp).2
      rw [hcongr, Finset.sum_const, smul_eq_mul, hP1_card]; ring
    have hS2 : Q ^ 3 * ∑ p ∈ P2, Z (p.1 - p.2) ≤ Q ^ (r + c) * (P2.card * (Q ^ 2 + Q - 1)) := by
      rw [Finset.mul_sum]
      calc ∑ p ∈ P2, Q ^ 3 * Z (p.1 - p.2)
          ≤ ∑ _p ∈ P2, Q ^ (r + c) * (Q ^ 2 + Q - 1) := by
            refine Finset.sum_le_sum fun p hp => hZ2 _ ?_
            rcases (Finset.mem_filter.mp hp).2 with ⟨hne, hrne⟩
            have hne0 : (p.1 - p.2).rank ≠ 0 := fun hr0 => hne (sub_eq_zero.mp (matrix_eq_zero_of_rank_zero _ hr0))
            omega
        _ = Q ^ (r + c) * (P2.card * (Q ^ 2 + Q - 1)) := by rw [Finset.sum_const, smul_eq_mul]; ring
    have hnum_lt : m * Q ^ 3 + e * (Q * (2 * Q - 1)) + P2.card * (Q ^ 2 + Q - 1) < 2 * m ^ 2 * Q ^ 2 := by
      have hQ1 : 1 ≤ Q := by omega
      have h2Q1 : 1 ≤ 2 * Q := by omega
      have hQ2 : 1 ≤ Q ^ 2 + Q := by nlinarith
      have hQ3 : Q ≤ Q ^ 2 := by nlinarith
      change (e + m * (Q + 1)) * (Q - 1) ^ 2 < m ^ 2 * (Q ^ 2 - Q + 1) at hineq
      zify [hQ1, h2Q1, hQ2, hQ3] at hineq hcard_DD ⊢
      have hP2_z : (P2.card : ℤ) = (m : ℤ) ^ 2 - (m : ℤ) - (e : ℤ) := by linarith
      have hid : 2 * (m : ℤ) ^ 2 * (Q : ℤ) ^ 2 -
          ((m : ℤ) * (Q : ℤ) ^ 3 + (e : ℤ) * ((Q : ℤ) * (2 * (Q : ℤ) - 1)) + (P2.card : ℤ) * ((Q : ℤ) ^ 2 + (Q : ℤ) - 1)) =
          (m : ℤ) ^ 2 * ((Q : ℤ) ^ 2 - (Q : ℤ) + 1) - ((e : ℤ) + (m : ℤ) * ((Q : ℤ) + 1)) * ((Q : ℤ) - 1) ^ 2 := by
        rw [hP2_z]; ring
      linarith
    have hQrc_pos : 0 < Q ^ (r + c) := pow_pos (by omega) _
    have htot_le : Q ^ 3 * ∑ p ∈ P0, Z (p.1 - p.2) + Q ^ 3 * ∑ p ∈ P1, Z (p.1 - p.2) +
        Q ^ 3 * ∑ p ∈ P2, Z (p.1 - p.2) ≤
        Q ^ (r + c) * (m * Q ^ 3 + e * (Q * (2 * Q - 1)) + P2.card * (Q ^ 2 + Q - 1)) := by
      rw [hS0, hS1]
      have hdist : Q ^ (r + c) * (m * Q ^ 3) + Q ^ (r + c) * (e * (Q * (2 * Q - 1))) +
          Q ^ (r + c) * (P2.card * (Q ^ 2 + Q - 1)) =
          Q ^ (r + c) * (m * Q ^ 3 + e * (Q * (2 * Q - 1)) + P2.card * (Q ^ 2 + Q - 1)) := by ring
      rw [← hdist]
      exact Nat.add_le_add_left hS2 _
    exact lt_of_le_of_lt htot_le (Nat.mul_lt_mul_of_pos_left hnum_lt hQrc_pos)
  have hsum_swap : ∑ p ∈ D.product D, Z (p.1 - p.2) =
      ∑ ab : (Fin r → K) × (Fin c → K),
        ((D.product D).filter (fun p => eval ab.1 ab.2 p.1 = eval ab.1 ab.2 p.2)).card := by
    simp only [Z, Finset.card_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ab _ => Finset.sum_congr rfl fun p _ => ?_
    have hiff : eval ab.1 ab.2 (p.1 - p.2) = 0 ↔ eval ab.1 ab.2 p.1 = eval ab.1 ab.2 p.2 := by
      have hlin : eval ab.1 ab.2 (p.1 - p.2) = eval ab.1 ab.2 p.1 - eval ab.1 ab.2 p.2 := by
        dsimp only [eval]
        simp only [Matrix.sub_apply, mul_sub, sub_mul, Finset.sum_sub_distrib]
      rw [hlin, sub_eq_zero]
    simp [hiff]
  have hsum_ab_lt : Q * ∑ ab : (Fin r → K) × (Fin c → K),
      ((D.product D).filter (fun p => eval ab.1 ab.2 p.1 = eval ab.1 ab.2 p.2)).card <
      Q ^ (r + c) * (2 * m ^ 2) := by
    rw [← hsum_swap]
    have h1 : Q ^ 2 * (Q * ∑ p ∈ D.product D, Z (p.1 - p.2)) < Q ^ 2 * (Q ^ (r + c) * (2 * m ^ 2)) := by
      calc Q ^ 2 * (Q * ∑ p ∈ D.product D, Z (p.1 - p.2))
          = Q ^ 3 * ∑ p ∈ D.product D, Z (p.1 - p.2) := by ring
        _ < Q ^ (r + c) * (2 * m ^ 2 * Q ^ 2) := hsum_Z_le
        _ = Q ^ 2 * (Q ^ (r + c) * (2 * m ^ 2)) := by ring
    exact Nat.lt_of_mul_lt_mul_left h1
  have hex_ab : ∃ ab : (Fin r → K) × (Fin c → K),
      Q * ((D.product D).filter (fun p => eval ab.1 ab.2 p.1 = eval ab.1 ab.2 p.2)).card < 2 * m ^ 2 := by
    by_contra hall
    push Not at hall
    have hcard_pair : Fintype.card ((Fin r → K) × (Fin c → K)) = Q ^ (r + c) := by
      rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
        hcardK, pow_add]
    have hge : Q ^ (r + c) * (2 * m ^ 2) ≤ Q * ∑ ab : (Fin r → K) × (Fin c → K),
        ((D.product D).filter (fun p => eval ab.1 ab.2 p.1 = eval ab.1 ab.2 p.2)).card := by
      rw [Finset.mul_sum]
      calc Q ^ (r + c) * (2 * m ^ 2) = ∑ _ab : (Fin r → K) × (Fin c → K), (2 * m ^ 2) := by
            rw [Finset.sum_const, Finset.card_univ, hcard_pair, smul_eq_mul]
        _ ≤ _ := Finset.sum_le_sum fun ab _ => hall ab
    omega
  rcases hex_ab with ⟨⟨a, b⟩, hab_lt⟩
  let Im := D.image (eval a b)
  have hIm_big : Q < 2 * Im.card := by
    let cnt : K → ℕ := fun y => (D.filter (fun M => eval a b M = y)).card
    have hsum_cnt : ∑ y ∈ Im, cnt y = m := by
      have hbiU : D = Im.biUnion (fun y => D.filter (fun M => eval a b M = y)) := by
        ext M
        simp only [Finset.mem_biUnion, Finset.mem_filter, Im, Finset.mem_image]
        exact ⟨fun hM => ⟨eval a b M, ⟨M, hM, rfl⟩, hM, rfl⟩, fun ⟨_, _, hM, _⟩ => hM⟩
      have hcard := congrArg Finset.card hbiU
      rw [Finset.card_biUnion] at hcard
      · exact hcard.symm
      · intro y1 _ y2 _ hne
        change Disjoint _ _
        rw [Finset.disjoint_left]
        intro M h1 h2
        exact hne ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)
    have hsum_sq : ∑ y ∈ Im, (cnt y) ^ 2 =
        ((D.product D).filter (fun p => eval a b p.1 = eval a b p.2)).card := by
      have hbiU : (D.product D).filter (fun p => eval a b p.1 = eval a b p.2) =
          Im.biUnion (fun y => (D.filter (fun M => eval a b M = y)).product (D.filter (fun M => eval a b M = y))) := by
        ext ⟨M, N⟩
        simp only [Finset.product_eq_sprod, Finset.mem_filter, Finset.mem_product, Finset.mem_biUnion,
          Im, Finset.mem_image]
        constructor
        · rintro ⟨⟨hM, hN⟩, heq⟩
          exact ⟨eval a b M, ⟨M, hM, rfl⟩, ⟨hM, rfl⟩, ⟨hN, heq.symm⟩⟩
        · rintro ⟨y, _, ⟨hM, hMy⟩, ⟨hN, hNy⟩⟩
          exact ⟨⟨hM, hN⟩, hMy.trans hNy.symm⟩
      rw [hbiU, Finset.card_biUnion]
      · refine Finset.sum_congr rfl fun y _ => ?_
        rw [Finset.product_eq_sprod, Finset.card_product, sq]
      · intro y1 _ y2 _ hne
        change Disjoint _ _
        rw [Finset.disjoint_left]
        rintro ⟨M, N⟩ h1 h2
        have h1' := (Finset.mem_filter.mp (Finset.mem_product.mp h1).1).2
        have h2' := (Finset.mem_filter.mp (Finset.mem_product.mp h2).1).2
        exact hne (h1'.symm.trans h2')
    have hcs := sq_sum_le_card_mul_sum_sq Im cnt
    rw [hsum_cnt, hsum_sq] at hcs
    have h1 : Q * m ^ 2 < Im.card * (2 * m ^ 2) := by
      calc Q * m ^ 2 ≤ Q * (Im.card * ((D.product D).filter (fun p => eval a b p.1 = eval a b p.2)).card) :=
            Nat.mul_le_mul_left Q hcs
        _ = Im.card * (Q * ((D.product D).filter (fun p => eval a b p.1 = eval a b p.2)).card) := by ring
        _ < Im.card * (2 * m ^ 2) := by
            have hIm_pos : 0 < Im.card := Finset.card_pos.mpr (Finset.Nonempty.image (Finset.card_pos.mp hm_pos) _)
            exact Nat.mul_lt_mul_of_pos_left hab_lt hIm_pos
    have h2 : Q * m ^ 2 < (2 * Im.card) * m ^ 2 := by
      calc Q * m ^ 2 < Im.card * (2 * m ^ 2) := h1
        _ = (2 * Im.card) * m ^ 2 := by ring
    exact Nat.lt_of_mul_lt_mul_right h2
  refine ⟨a, b, fun z => ?_⟩
  let ImZ := Im.image (fun y => z + y)
  have hImZ_card : ImZ.card = Im.card :=
    Finset.card_image_of_injective Im (fun y1 y2 h => add_left_cancel h)
  have hnot_disj : ¬ Disjoint Im ImZ := by
    intro hdisj
    have hcard_u : (Im ∪ ImZ).card = Im.card + ImZ.card := Finset.card_union_of_disjoint hdisj
    have hle_Q : (Im ∪ ImZ).card ≤ Q := by
      rw [← hcardK]; exact Finset.card_le_univ _
    omega
  rw [Finset.not_disjoint_iff] at hnot_disj
  rcases hnot_disj with ⟨y1, hy1_Im, hy1_ImZ⟩
  rcases Finset.mem_image.mp hy1_Im with ⟨M, hM, hMy1⟩
  rcases Finset.mem_image.mp hy1_ImZ with ⟨y2, hy2_Im, hy2_eq⟩
  rcases Finset.mem_image.mp hy2_Im with ⟨N, hN, hNy2⟩
  refine ⟨M, hM, N, hN, ?_⟩
  have heq : z + eval a b N = eval a b M := by rw [hNy2, hy2_eq, hMy1]
  calc z = z + (eval a b N + eval a b N) := by rw [hK_add_self, add_zero]
    _ = (z + eval a b N) + eval a b N := by ring
    _ = eval a b M + eval a b N := by rw [heq]

end PEqualNP.Outside.L_meta_32033

open PEqualNP.Outside.L_meta_32033 in
theorem PEqualNP.Outside.L_meta_32033 :
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
    ∀ (K : Type) [Field K] [DecidableEq K] [Algebra F K] [FiniteDimensional F K]
        (k : ℕ) (basis : Module.Basis (Fin k) F K) (bit : K →ₗ[F] F), bit ≠ 0 →
      ∀ (r c : ℕ), 0 < r → 0 < c →
        let Q := 2^k
        let Mat := Matrix (Fin r) (Fin c) K
        let bank : (d : ℕ) → Fin (d*k+1) → Fin d → K := fun d => Fin.cases (0 : Fin d → K)
          (fun idx : Fin (d*k) => fun j : Fin d =>
            if j = (finProdFinEquiv.symm idx : Fin d × Fin k).1 then
              basis (finProdFinEquiv.symm idx : Fin d × Fin k).2 else 0)
        let eval := fun (a : Fin r → K) (b : Fin c → K) (M : Mat) =>
          ∑ i, ∑ j, a i * M i j * b j
        let target := fun (M : Mat) (x : Fin (r*k+1)) (y : Fin (c*k+1)) =>
          decide (bit (eval (bank r x) (bank c y) M) ≠ 0)
        let point : Fin (k+1) → K := Fin.cases 0 basis
        let scalar := fun (z : K) (x y : Fin (k+1)) => decide (bit (z * point x * point y) ≠ 0)
        let readMask := fun {n m g : ℕ} (T : Fin g → Fin n → Fin m → Bool)
            (S : Finset (Fin g)) (x : Fin n) (y : Fin m) =>
          (((S.filter (fun j => T j x y)).card % 2) == 1)
        ∀ (g s : ℕ) (T : Fin g → Fin (r*k+1) → Fin (c*k+1) → Bool)
            (D : Finset Mat) (mask : Mat → Finset (Fin g)) (t : Mat → ℕ),
          fits (r*k+1) (c*k+1) g T s →
          (∀ M ∈ D, fits (r*k+1) (c*k+1) 1
            (fun _ x y => xor (target M x y) (readMask T (mask M) x y)) (t M)) →
          let m := D.card
          let e := ((D.product D).filter (fun pair => (pair.1-pair.2).rank = 1)).card
          (e + m*(Q+1)) * (Q-1)^2 < m^2 * (Q^2-Q+1) →
          ∃ (a : Fin r → K) (b : Fin c → K) (V : Fin g → Fin (k+1) → Fin (k+1) → Bool),
            fits (k+1) (k+1) g V s ∧
            ∀ z : K, ∃ M ∈ D, ∃ N ∈ D, z = eval a b M + eval a b N ∧
              fits (k+1) (k+1) 1 (fun _ x y =>
                xor (scalar z x y) (xor (readMask V (mask M) x y) (readMask V (mask N) x y)))
                (t M + t N) := by
  classical
  intro nonlinear depths fits F K _ _ _ _ k basis bit hbit r c hr hc Q Mat bank eval target point scalar readMask
    g s T D mask t hfitsT hfitsD m e hineq
  rcases exists_good_ab_cover K k basis bit hbit r c hr hc D hineq with ⟨a, b, hsum_cover⟩
  let coefA : Fin (k + 1) → Fin (r * k) → ZMod 2 := fun x idx =>
    basis.repr (point x * a (finProdFinEquiv.symm idx).1) (finProdFinEquiv.symm idx).2
  let coefB : Fin (k + 1) → Fin (c * k) → ZMod 2 := fun y idy =>
    basis.repr (point y * b (finProdFinEquiv.symm idy).1) (finProdFinEquiv.symm idy).2
  have hspan_a : ∀ (x : Fin (k + 1)) (i : Fin r),
      point x * a i = ∑ idx : Fin (r * k), coefA x idx • bank r idx.succ i := by
    intro x i
    have hrepr := (basis.sum_repr (point x * a i)).symm
    rw [hrepr]
    have hbij : ∑ t : Fin k, basis.repr (point x * a i) t • basis t =
        ∑ p : Fin r × Fin k, basis.repr (point x * a p.1) p.2 • (if i = p.1 then basis p.2 else 0) := by
      rw [Fintype.sum_prod_type]
      rw [Finset.sum_eq_single i]
      · simp
      · intro i' _ hne; apply Finset.sum_eq_zero; intro t _; simp [hne.symm]
      · intro h; exact (h (Finset.mem_univ i)).elim
    rw [hbij]
    refine Fintype.sum_equiv finProdFinEquiv _ _ fun p => ?_
    simp only [coefA, bank, Fin.cases_succ, Equiv.symm_apply_apply]
  have hspan_b : ∀ (y : Fin (k + 1)) (j : Fin c),
      point y * b j = ∑ idy : Fin (c * k), coefB y idy • bank c idy.succ j := by
    intro y j
    have hrepr := (basis.sum_repr (point y * b j)).symm
    rw [hrepr]
    have hbij : ∑ t : Fin k, basis.repr (point y * b j) t • basis t =
        ∑ p : Fin c × Fin k, basis.repr (point y * b p.1) p.2 • (if j = p.1 then basis p.2 else 0) := by
      rw [Fintype.sum_prod_type]
      rw [Finset.sum_eq_single j]
      · simp
      · intro j' _ hne; apply Finset.sum_eq_zero; intro t _; simp [hne.symm]
      · intro h; exact (h (Finset.mem_univ j)).elim
    rw [hbij]
    refine Fintype.sum_equiv finProdFinEquiv _ _ fun p => ?_
    simp only [coefB, bank, Fin.cases_succ, Equiv.symm_apply_apply]
  let pullZ : (Fin (r * k + 1) → Fin (c * k + 1) → Bool) → Fin (k + 1) → Fin (k + 1) → ZMod 2 :=
    fun G x y => ∑ idx : Fin (r * k), ∑ idy : Fin (c * k),
      coefA x idx * coefB y idy * deltaMat (fun x' y' => b2z (G x' y')) idx idy
  let pull : (Fin (r * k + 1) → Fin (c * k + 1) → Bool) → Fin (k + 1) → Fin (k + 1) → Bool :=
    fun G x y => decide (pullZ G x y ≠ 0)
  have hb2z_pull : ∀ G x y, b2z (pull G x y) = pullZ G x y := fun G x y => b2z_decide_ne_zero _
  have hpull_target : ∀ (M : Mat) (x y : Fin (k + 1)),
      pullZ (target M) x y = b2z (scalar (eval a b M) x y) := by
    intro M x y
    have hdelta_t : ∀ (idx : Fin (r * k)) (idy : Fin (c * k)),
        deltaMat (fun x' y' => b2z (target M x' y')) idx idy =
          bit (eval (bank r idx.succ) (bank c idy.succ) M) := by
      intro idx idy
      have h0r : ∀ y', eval (bank r 0) (bank c y') M = 0 := fun y' => by
        simp [eval, bank]
      have h0c : ∀ x', eval (bank r x') (bank c 0) M = 0 := fun x' => by
        simp [eval, bank]
      simp only [deltaMat, target, h0r, h0c, map_zero, ne_eq, not_true_eq_false, decide_false,
        b2z, Bool.false_eq_true, ↓reduceIte, add_zero]
      exact b2z_decide_ne_zero _
    simp_rw [pullZ, hdelta_t]
    have hsmul_mul : ∀ (s1 s2 : ZMod 2) (v : K),
        s1 * s2 * bit v = bit ((s1 * s2) • v) := fun s1 s2 v => by
      rw [map_smul, smul_eq_mul]
    have heval_bilin : eval a b M * point x * point y =
        ∑ idx : Fin (r * k), ∑ idy : Fin (c * k),
          (coefA x idx * coefB y idy) • eval (bank r idx.succ) (bank c idy.succ) M := by
      have h1 : eval a b M * point x * point y =
          ∑ i : Fin r, ∑ j : Fin c, (point x * a i) * M i j * (point y * b j) := by
        dsimp only [eval]
        rw [Finset.sum_mul, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_mul, Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => by ring
      rw [h1]
      simp_rw [hspan_a x, hspan_b y]
      have hinner : ∀ (i : Fin r) (j : Fin c),
          (∑ idx : Fin (r * k), coefA x idx • bank r idx.succ i) * M i j *
            (∑ idy : Fin (c * k), coefB y idy • bank c idy.succ j) =
          ∑ idx : Fin (r * k), ∑ idy : Fin (c * k),
            (coefA x idx * coefB y idy) • (bank r idx.succ i * M i j * bank c idy.succ j) := by
        intro i j
        rw [Finset.sum_mul, Finset.sum_mul]
        refine Finset.sum_congr rfl fun idx _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun idy _ => ?_
        simp only [Algebra.smul_def, map_mul]
        ring
      simp_rw [hinner]
      have hswap_j : ∀ (i : Fin r),
          (∑ j : Fin c, ∑ idx : Fin (r * k), ∑ idy : Fin (c * k),
            (coefA x idx * coefB y idy) • (bank r idx.succ i * M i j * bank c idy.succ j)) =
          ∑ idx : Fin (r * k), ∑ j : Fin c, ∑ idy : Fin (c * k),
            (coefA x idx * coefB y idy) • (bank r idx.succ i * M i j * bank c idy.succ j) :=
        fun _ => Finset.sum_comm
      simp_rw [hswap_j]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun idx _ => ?_
      have hswap : ∀ (i : Fin r),
          (∑ j : Fin c, ∑ idy : Fin (c * k),
            (coefA x idx * coefB y idy) • (bank r idx.succ i * M i j * bank c idy.succ j)) =
          ∑ idy : Fin (c * k), ∑ j : Fin c,
            (coefA x idx * coefB y idy) • (bank r idx.succ i * M i j * bank c idy.succ j) :=
        fun _ => Finset.sum_comm
      simp_rw [hswap]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun idy _ => ?_
      dsimp only [eval]
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.smul_sum]
    rw [show b2z (scalar (eval a b M) x y) = bit (eval a b M * point x * point y) from b2z_decide_ne_zero _]
    rw [heval_bilin, map_sum]
    refine Finset.sum_congr rfl fun idx _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun idy _ => ?_
    exact hsmul_mul _ _ _
  have hpull_xor : ∀ (G1 G2 : Fin (r * k + 1) → Fin (c * k + 1) → Bool) (x y : Fin (k + 1)),
      pullZ (fun x' y' => xor (G1 x' y') (G2 x' y')) x y = pullZ G1 x y + pullZ G2 x y := by
    intro G1 G2 x y
    simp only [pullZ, b2z_xor, deltaMat_add, mul_add, Finset.sum_add_distrib]
  let V : Fin g → Fin (k + 1) → Fin (k + 1) → Bool := fun j => pull (T j)
  have hpull_readMask : ∀ (S : Finset (Fin g)) (x y : Fin (k + 1)),
      pullZ (readMask T S) x y = b2z (readMask V S x y) := by
    intro S x y
    dsimp only [pullZ, readMask, V]
    simp_rw [b2z_filter_parity, deltaMat_sum, Finset.mul_sum]
    have h1 : ∀ (idx : Fin (r * k)),
        (∑ idy : Fin (c * k), ∑ j ∈ S,
          coefA x idx * coefB y idy * deltaMat (fun x' y' => b2z (T j x' y')) idx idy) =
        ∑ j ∈ S, ∑ idy : Fin (c * k),
          coefA x idx * coefB y idy * deltaMat (fun x' y' => b2z (T j x' y')) idx idy :=
      fun _ => Finset.sum_comm
    simp_rw [h1]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact (hb2z_pull (T j) x y).symm
  have hpull_extract : ∀ (q : ℕ) (G : Fin q → Fin (r * k + 1) → Fin (c * k + 1) → Bool) (u : ℕ),
      fits (r * k + 1) (c * k + 1) q G u →
      ∃ (qs : List (Quad (k + 1) (k + 1))) (w : Fin q → Fin qs.length → ZMod 2),
        qs.length ≤ u ∧
        ∀ (j : Fin q) (x y : Fin (k + 1)),
          pullZ (G j) x y = ∑ p : Fin qs.length, w j p * evalQuad (qs.get p) x y := by
    intro q G u ⟨C, tap, _, hfan, hcnt, htaps⟩
    rcases circuit_depth1_decomp (r * k + 1) (c * k + 1) C.gates hfan with ⟨qs0, hqs0_le, _, hdec1⟩
    have hnonlin_eq : nonlinear = nonlin := rfl
    rw [hnonlin_eq] at hcnt
    have hdep_eq : depths (r * k + 1 + (c * k + 1)) C = depthsOf (r * k + 1 + (c * k + 1)) C.gates := rfl
    have htap_dec : ∀ j : Fin q,
        ∃ (mj : Fin qs0.length → ZMod 2) (αj : Fin (r * k + 1) → ZMod 2) (βj : Fin (c * k + 1) → ZMod 2),
          ∀ x' y', b2z (G j x' y') = αj x' + βj y' + ∑ p : Fin qs0.length, mj p * evalQuad (qs0.get p) x' y' := by
      intro j
      have hdj : (depthsOf (r * k + 1 + (c * k + 1)) C.gates).getD (tap j) 0 ≤ 1 := by
        rw [← hdep_eq]; exact (htaps j).1
      rcases hdec1 (tap j) hdj with ⟨mj, αj, βj, hev⟩
      refine ⟨mj, αj, βj, fun x' y' => ?_⟩
      have hrep : (wiresOf C.gates (PEqualNP.Represents.oneEach x' y')).getD (tap j) false = G j x' y' := (htaps j).2 x' y'
      rw [← hrep]
      exact hev x' y'
    let qs := qs0.map (pullQuad coefA coefB)
    have hqs_len : qs.length = qs0.length := by simp [qs]
    let w : Fin q → Fin qs.length → ZMod 2 := fun j p =>
      Classical.choose (htap_dec j) ⟨p.val, by omega⟩
    refine ⟨qs, w, by omega, fun j x y => ?_⟩
    let mj := Classical.choose (htap_dec j)
    let αj := Classical.choose (Classical.choose_spec (htap_dec j))
    let βj := Classical.choose (Classical.choose_spec (Classical.choose_spec (htap_dec j)))
    have hGj : ∀ x' y', b2z (G j x' y') = αj x' + βj y' + ∑ p : Fin qs0.length, mj p * evalQuad (qs0.get p) x' y' :=
      Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (htap_dec j)))
    have hdelta_G : ∀ idx idy,
        deltaMat (fun x' y' => b2z (G j x' y')) idx idy =
          ∑ p : Fin qs0.length, mj p * deltaMat (evalQuad (qs0.get p)) idx idy := by
      intro idx idy
      have hfn : (fun x' y' => b2z (G j x' y')) =
          (fun x' y' => (αj x' + βj y') + ∑ p : Fin qs0.length, mj p * evalQuad (qs0.get p) x' y') := by
        funext x' y'; exact hGj x' y'
      rw [hfn, deltaMat_add, deltaMat_aff, zero_add, deltaMat_sum]
      refine Finset.sum_congr rfl fun p _ => deltaMat_smul _ _ _ _
    dsimp only [pullZ]
    simp_rw [hdelta_G, Finset.mul_sum]
    have hswap1 : ∀ idx : Fin (r * k),
        (∑ idy : Fin (c * k), ∑ p : Fin qs0.length,
          coefA x idx * coefB y idy * (mj p * deltaMat (evalQuad (qs0.get p)) idx idy)) =
        ∑ p : Fin qs0.length, ∑ idy : Fin (c * k),
          coefA x idx * coefB y idy * (mj p * deltaMat (evalQuad (qs0.get p)) idx idy) :=
      fun _ => Finset.sum_comm
    simp_rw [hswap1]
    rw [Finset.sum_comm]
    have hsum0 : ∑ p : Fin qs0.length, ∑ idx : Fin (r * k), ∑ idy : Fin (c * k),
        coefA x idx * coefB y idy * (mj p * deltaMat (evalQuad (qs0.get p)) idx idy) =
        ∑ p : Fin qs0.length, mj p * evalQuad (pullQuad coefA coefB (qs0.get p)) x y := by
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [← pullZ_evalQuad coefA coefB (qs0.get p) x y, Finset.mul_sum]
      refine Finset.sum_congr rfl fun idx _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun idy _ => by ring
    rw [hsum0]
    refine Finset.sum_bij (fun p _ => ⟨p.val, by omega⟩) (fun _ _ => Finset.mem_univ _)
      (fun _ _ _ _ h => Fin.ext (Fin.mk.inj h))
      (fun p _ => ⟨⟨p.val, by omega⟩, Finset.mem_univ _, Fin.ext rfl⟩)
      (fun p _ => ?_)
    have hget : qs.get ⟨p.val, by omega⟩ = pullQuad coefA coefB (qs0.get p) := by
      simp [qs, List.get_eq_getElem]
    rw [hget]
  have hfitsV : fits (k + 1) (k + 1) g V s := by
    rcases hpull_extract g T s hfitsT with ⟨qs, w, hqs_le, hval⟩
    rcases synth_depth1_quads (k + 1) (k + 1) g qs w (fun _ _ => 0) (fun _ _ => 0) with
      ⟨C, tap, hrb, hfan, hcnt, htaps⟩
    refine ⟨C, tap, hrb, hfan, hcnt.trans hqs_le, fun j => ⟨(htaps j).1, fun x y => ?_⟩⟩
    apply b2z_inj
    have h1 := (htaps j).2 x y
    simp only [zero_add] at h1
    change b2z ((wiresOf C.gates (PEqualNP.Represents.oneEach x y)).getD (tap j) false) = b2z (V j x y)
    rw [h1, hb2z_pull, hval j x y]
  refine ⟨a, b, V, hfitsV, fun z => ?_⟩
  rcases hsum_cover z with ⟨M, hM, N, hN, hz_eq⟩
  refine ⟨M, hM, N, hN, hz_eq, ?_⟩
  rcases hpull_extract 1 (fun _ x y => xor (target M x y) (readMask T (mask M) x y)) (t M) (hfitsD M hM) with
    ⟨qsM, wM, hqsM_le, hvalM⟩
  rcases hpull_extract 1 (fun _ x y => xor (target N x y) (readMask T (mask N) x y)) (t N) (hfitsD N hN) with
    ⟨qsN, wN, hqsN_le, hvalN⟩
  let qsMN := qsM ++ qsN
  have hqsMN_len : qsMN.length = qsM.length + qsN.length := List.length_append
  let wMN : Fin 1 → Fin qsMN.length → ZMod 2 := fun _ p =>
    if hp : p.val < qsM.length then wM 0 ⟨p.val, hp⟩ else wN 0 ⟨p.val - qsM.length, by omega⟩
  rcases synth_depth1_quads (k + 1) (k + 1) 1 qsMN wMN (fun _ _ => 0) (fun _ _ => 0) with
    ⟨C, tap, hrb, hfan, hcnt, htaps⟩
  have hcnt' : C.gates.countP nonlinear ≤ qsMN.length := hcnt
  refine ⟨C, tap, hrb, hfan, by omega, fun j => ⟨(htaps j).1, fun x y => ?_⟩⟩
  apply b2z_inj
  have h1 := (htaps j).2 x y
  simp only [zero_add] at h1
  change b2z ((wiresOf C.gates (PEqualNP.Represents.oneEach x y)).getD (tap j) false) =
    b2z (xor (scalar z x y) (xor (readMask V (mask M) x y) (readMask V (mask N) x y)))
  rw [h1]
  have hsum_split : ∑ p : Fin qsMN.length, wMN j p * evalQuad (qsMN.get p) x y =
      (∑ p : Fin qsM.length, wM 0 p * evalQuad (qsM.get p) x y) +
      (∑ p : Fin qsN.length, wN 0 p * evalQuad (qsN.get p) x y) := by
    have hbij : ∑ p : Fin (qsM.length + qsN.length),
        wMN j ⟨p.val, by omega⟩ * evalQuad (qsMN.get ⟨p.val, by omega⟩) x y =
        ∑ p : Fin qsMN.length, wMN j p * evalQuad (qsMN.get p) x y :=
      Finset.sum_bij (fun p _ => ⟨p.val, by omega⟩) (fun _ _ => Finset.mem_univ _)
        (fun _ _ _ _ h => Fin.ext (Fin.mk.inj h))
        (fun p _ => ⟨⟨p.val, by omega⟩, Finset.mem_univ _, Fin.ext rfl⟩)
        (fun _ _ => rfl)
    rw [← hbij, Fin.sum_univ_add]
    congr 1
    · refine Finset.sum_congr rfl fun p _ => ?_
      have hget : qsMN.get ⟨p.val, by omega⟩ = qsM.get p := by
        simp [qsMN, List.get_eq_getElem, List.getElem_append_left p.isLt]
      change wMN j ⟨p.val, by omega⟩ * evalQuad (qsMN.get ⟨p.val, by omega⟩) x y = _
      rw [hget]
      simp [wMN, p.isLt]
    · refine Finset.sum_congr rfl fun p _ => ?_
      have hget : qsMN.get ⟨qsM.length + p.val, by omega⟩ = qsN.get p := by
        simp [qsMN, List.get_eq_getElem, List.getElem_append_right (Nat.le_add_right qsM.length p.val)]
      change wMN j ⟨qsM.length + p.val, by omega⟩ * evalQuad (qsMN.get ⟨qsM.length + p.val, by omega⟩) x y = _
      rw [hget]
      simp [wMN, show ¬ qsM.length + p.val < qsM.length by omega]
  rw [hsum_split, ← hvalM 0 x y, ← hvalN 0 x y, hpull_xor, hpull_xor,
    hpull_target M x y, hpull_target N x y, hpull_readMask (mask M) x y, hpull_readMask (mask N) x y]
  have hscalar_add : b2z (scalar z x y) = b2z (scalar (eval a b M) x y) + b2z (scalar (eval a b N) x y) := by
    simp only [scalar]
    rw [b2z_decide_ne_zero, b2z_decide_ne_zero, b2z_decide_ne_zero, hz_eq, add_mul, add_mul, map_add]
  rw [b2z_xor, b2z_xor, hscalar_add]
  ring

