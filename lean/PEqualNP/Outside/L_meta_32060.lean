import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_32060

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents
open scoped Matrix

private def b2z (b : Bool) : ZMod 2 := if b then 1 else 0

private lemma zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 :=
  match a with
  | ⟨0, _⟩ => Or.inl rfl
  | ⟨1, _⟩ => Or.inr rfl

private lemma zmod2_add_self (a : ZMod 2) : a + a = 0 := by
  rcases zmod2_cases a with rfl | rfl <;> decide

private lemma zmod2_sub_eq_add (a b : ZMod 2) : a - b = a + b := by
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl <;> decide

private lemma b2z_inj {a b : Bool} (h : b2z a = b2z b) : a = b := by
  cases a <;> cases b <;> simp [b2z] at h ⊢

private lemma b2z_xor (a b : Bool) : b2z (xor a b) = b2z a + b2z b := by
  cases a <;> cases b <;> decide

private lemma b2z_and (a b : Bool) : b2z (a && b) = b2z a * b2z b := by
  cases a <;> cases b <;> decide

private lemma b2z_decide_ne_zero (a : ZMod 2) [Decidable (a ≠ 0)] : b2z (decide (a ≠ 0)) = a := by
  rcases zmod2_cases a with rfl | rfl <;> simp [b2z]

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
        simp only [wiresOf, List.foldl_nil, oneEach, Finset.sum_empty, add_zero]
        have hlen : (List.ofFn (fun i : Fin n => decide (i = x))).length = n := by simp
        rw [getD_append_left _ _ _ _ (by omega)]
        simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos h1, Option.getD_some]
        have hiff : ((⟨idx, h1⟩ : Fin n) = x) ↔ x.val = idx :=
          ⟨fun h => by rw [← h], fun h => Fin.ext h.symm⟩
        simp [hiff]
      · by_cases h2 : idx < n + m
        · refine ⟨Fin.elim0, fun _ => 0, fun y => b2z (decide (y.val = idx - n)), fun x y => ?_⟩
          simp only [wiresOf, List.foldl_nil, oneEach, Finset.sum_empty, zero_add, add_zero]
          have hlen1 : (List.ofFn (fun i : Fin n => decide (i = x))).length = n := by simp
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [hlen1]; omega)]
          simp only [hlen1, List.getElem?_ofFn, dif_pos (by omega : idx - n < m), Option.getD_some]
          have hiff : ((⟨idx - n, by omega⟩ : Fin m) = y) ↔ y.val = idx - n :=
            ⟨fun h => by rw [← h], fun h => Fin.ext h.symm⟩
          simp [hiff]
        · refine ⟨Fin.elim0, fun _ => 0, fun _ => 0, fun x y => ?_⟩
          simp only [wiresOf, List.foldl_nil, Finset.sum_empty, add_zero]
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
  rcases hstage2 q le_rfl with ⟨gs2, tap, _, hgood2, hcnt2, _, _, _, htdep2, hteval2⟩
  refine ⟨⟨gs2, 0⟩, tap, hgood2.1, hgood2.2, le_of_eq hcnt2, fun j => ⟨htdep2 j, hteval2 j⟩⟩

private def isAlt {d : ℕ} (M : Matrix (Fin d) (Fin d) (ZMod 2)) : Prop :=
  Mᵀ = M ∧ ∀ i, M i i = 0

private lemma isAlt_symm {d : ℕ} {M : Matrix (Fin d) (Fin d) (ZMod 2)} (hM : isAlt M) (i j : Fin d) :
    M j i = M i j := by
  have h := congrFun (congrFun hM.1 i) j
  simpa [Matrix.transpose_apply] using h

private lemma dot_mulVec_eq {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2))
    (y : Fin m → ZMod 2) (x : Fin n → ZMod 2) :
    dotProduct y (A *ᵥ x) = dotProduct (Aᵀ *ᵥ y) x := by
  simp only [dotProduct, Matrix.mulVec, Matrix.transpose_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring

private lemma alt_quad_zero {d : ℕ} {H : Matrix (Fin d) (Fin d) (ZMod 2)} (hH : isAlt H)
    (v : Fin d → ZMod 2) : dotProduct v (H *ᵥ v) = 0 := by
  classical
  have hsum : dotProduct v (H *ᵥ v) =
      ∑ p : Fin d × Fin d, v p.1 * H p.1 p.2 * v p.2 := by
    rw [Fintype.sum_prod_type]
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [hsum]
  let f : Fin d × Fin d → ZMod 2 := fun p => v p.1 * H p.1 p.2 * v p.2
  let Slt := (Finset.univ : Finset (Fin d × Fin d)).filter (fun p => p.1 < p.2)
  let Sgt := (Finset.univ : Finset (Fin d × Fin d)).filter (fun p => p.2 < p.1)
  let Seq := (Finset.univ : Finset (Fin d × Fin d)).filter (fun p => p.1 = p.2)
  have hunion : (Finset.univ : Finset (Fin d × Fin d)) = (Slt ∪ Sgt) ∪ Seq := by
    ext ⟨i, j⟩
    simp only [Slt, Sgt, Seq, Finset.mem_univ, Finset.mem_union, Finset.mem_filter, true_and, true_iff]
    rcases lt_trichotomy i j with h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inr h
    · exact Or.inl (Or.inr h)
  have hd1 : Disjoint Slt Sgt := by
    rw [Finset.disjoint_left]
    intro p h1 h2
    have a := (Finset.mem_filter.mp h1).2
    have b := (Finset.mem_filter.mp h2).2
    exact lt_asymm a b
  have hd2 : Disjoint (Slt ∪ Sgt) Seq := by
    rw [Finset.disjoint_left]
    intro p h1 h2
    have heq := (Finset.mem_filter.mp h2).2
    rcases Finset.mem_union.mp h1 with hlt | hgt
    · exact (ne_of_lt (Finset.mem_filter.mp hlt).2) heq
    · exact (ne_of_gt (Finset.mem_filter.mp hgt).2) heq
  change ∑ p ∈ Finset.univ, f p = 0
  rw [hunion, Finset.sum_union hd2, Finset.sum_union hd1]
  have hEq0 : ∑ p ∈ Seq, f p = 0 := by
    apply Finset.sum_eq_zero
    intro p hp
    have heq : p.1 = p.2 := (Finset.mem_filter.mp hp).2
    simp only [f, heq, hH.2, mul_zero, zero_mul]
  have hSwap : ∑ p ∈ Slt, f p = ∑ p ∈ Sgt, f p := by
    refine Finset.sum_bij (fun p _ => (p.2, p.1))
      (fun p hp => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hp).2⟩)
      (fun p1 _ p2 _ h => Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h))
      (fun p hp => ⟨(p.2, p.1), Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hp).2⟩, rfl⟩)
      (fun p _ => ?_)
    dsimp only [f]
    rw [isAlt_symm hH p.1 p.2]
    ring
  rw [hEq0, hSwap, zmod2_add_self, add_zero]

private lemma isAlt_conj {d : ℕ} (A H : Matrix (Fin d) (Fin d) (ZMod 2)) (hH : isAlt H) :
    isAlt (A * H * Aᵀ) := by
  refine ⟨?_, ?_⟩
  · rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hH.1, Matrix.mul_assoc]
  · intro i
    have hq := alt_quad_zero hH (fun j => A i j)
    have heq : (A * H * Aᵀ) i i = dotProduct (fun j => A i j) (H *ᵥ (fun j => A i j)) := by
      simp only [Matrix.mul_apply, Matrix.transpose_apply, dotProduct, Matrix.mulVec,
        Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
    rw [heq, hq]

private lemma isAlt_add {d : ℕ} {A B : Matrix (Fin d) (Fin d) (ZMod 2)}
    (hA : isAlt A) (hB : isAlt B) : isAlt (A + B) := by
  refine ⟨by rw [Matrix.transpose_add, hA.1, hB.1], fun i => ?_⟩
  simp [hA.2 i, hB.2 i]

private def altOuter {d : ℕ} (u v : Fin d → ZMod 2) : Matrix (Fin d) (Fin d) (ZMod 2) :=
  fun i j => u i * v j + v i * u j

private lemma isAlt_altOuter {d : ℕ} (u v : Fin d → ZMod 2) : isAlt (altOuter u v) := by
  refine ⟨?_, fun i => ?_⟩
  · ext i j; simp only [Matrix.transpose_apply, altOuter]; ring
  · simp only [altOuter]; rw [mul_comm (v i) (u i)]; exact zmod2_add_self _

private lemma altOuter_mulVec {d : ℕ} (u v x : Fin d → ZMod 2) :
    altOuter u v *ᵥ x = (dotProduct v x) • u + (dotProduct u x) • v := by
  funext i
  simp only [Matrix.mulVec, dotProduct, altOuter, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul,
    Finset.sum_add_distrib, Finset.sum_mul]
  congr 1 <;> refine Finset.sum_congr rfl fun j _ => by ring

private lemma altOuter_conj {d : ℕ} (U : Matrix (Fin d) (Fin d) (ZMod 2)) (u v : Fin d → ZMod 2) :
    U * altOuter u v * Uᵀ = altOuter (U *ᵥ u) (U *ᵥ v) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, altOuter, Matrix.mulVec, dotProduct]
  have h1 : ∀ q : Fin d, (∑ p : Fin d, U i p * (u p * v q + v p * u q)) * U j q =
      (∑ p : Fin d, U i p * u p * (U j q * v q)) + (∑ p : Fin d, U i p * v p * (U j q * u q)) := by
    intro q
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => by ring
  simp_rw [h1, Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_mul, Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => by rw [Finset.mul_sum]
  · rw [Finset.sum_mul, Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => by rw [Finset.mul_sum]

private lemma alt_decomp_aux : ∀ (n : ℕ) {d : ℕ} (M : Matrix (Fin d) (Fin d) (ZMod 2)),
    M.rank = n → isAlt M →
    ∃ (k : ℕ) (a b : Fin k → Fin d → ZMod 2),
      M.rank = 2 * k ∧ ∀ i j : Fin d, M i j = ∑ p : Fin k, (a p i * b p j + b p i * a p j) := by
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro d M hrank hM
    by_cases hM0 : M = 0
    · subst hM0
      refine ⟨0, Fin.elim0, Fin.elim0, by simp [Matrix.rank], fun i j => by simp⟩
    · have hex : ∃ i0 j0 : Fin d, M i0 j0 ≠ 0 := by
        by_contra hall
        push_neg at hall
        apply hM0
        ext i j
        exact hall i j
      rcases hex with ⟨i0, j0, hne⟩
      have hMij : M i0 j0 = 1 := by
        rcases zmod2_cases (M i0 j0) with h0 | h1
        · exact (hne h0).elim
        · exact h1
      have hMji : M j0 i0 = 1 := by rw [isAlt_symm hM, hMij]
      let u : Fin d → ZMod 2 := fun i => M i j0
      let v : Fin d → ZMod 2 := fun i => M i i0
      have hu_i0 : u i0 = 1 := hMij
      have hu_j0 : u j0 = 0 := hM.2 j0
      have hv_i0 : v i0 = 0 := hM.2 i0
      have hv_j0 : v j0 = 1 := hMji
      let M' : Matrix (Fin d) (Fin d) (ZMod 2) := M + altOuter u v
      have hM'_alt : isAlt M' := isAlt_add hM (isAlt_altOuter u v)
      have hM'_row_i0 : ∀ j : Fin d, M' i0 j = 0 := fun j => by
        simp only [M', Matrix.add_apply, altOuter, hu_i0, hv_i0, one_mul, zero_mul, add_zero]
        have hvj : v j = M i0 j := isAlt_symm hM i0 j
        rw [hvj]
        exact zmod2_add_self _
      have hM'_row_j0 : ∀ j : Fin d, M' j0 j = 0 := fun j => by
        simp only [M', Matrix.add_apply, altOuter, hu_j0, hv_j0, one_mul, zero_mul, zero_add]
        have huj : u j = M j0 j := isAlt_symm hM j0 j
        rw [huj]
        exact zmod2_add_self _
      let R : Submodule (ZMod 2) (Fin d → ZMod 2) := LinearMap.range M.mulVecLin
      let R' : Submodule (ZMod 2) (Fin d → ZMod 2) := LinearMap.range M'.mulVecLin
      let S : Submodule (ZMod 2) (Fin d → ZMod 2) := Submodule.span (ZMod 2) ({u, v} : Set (Fin d → ZMod 2))
      have huR : u ∈ R := ⟨Pi.single j0 1, by
        funext i
        change (M *ᵥ Pi.single j0 1) i = u i
        simp [Matrix.mulVec, dotProduct, u, Pi.single_apply]⟩
      have hvR : v ∈ R := ⟨Pi.single i0 1, by
        funext i
        change (M *ᵥ Pi.single i0 1) i = v i
        simp [Matrix.mulVec, dotProduct, v, Pi.single_apply]⟩
      have hR_eq : R = R' ⊔ S := by
        apply le_antisymm
        · rintro w ⟨x, rfl⟩
          change M *ᵥ x ∈ R' ⊔ S
          have hdecomp : M *ᵥ x = M' *ᵥ x + ((dotProduct v x) • u + (dotProduct u x) • v) := by
            funext i
            have h1 := congrFun (altOuter_mulVec u v x) i
            simp only [M', Matrix.add_mulVec, Pi.add_apply]
            rw [h1]
            simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
            have h2 := zmod2_add_self ((v ⬝ᵥ x) * u i + (u ⬝ᵥ x) * v i)
            calc (M *ᵥ x) i = (M *ᵥ x) i + (((v ⬝ᵥ x) * u i + (u ⬝ᵥ x) * v i) +
                  ((v ⬝ᵥ x) * u i + (u ⬝ᵥ x) * v i)) := by rw [h2, add_zero]
              _ = ((M *ᵥ x) i + ((v ⬝ᵥ x) * u i + (u ⬝ᵥ x) * v i)) +
                  ((v ⬝ᵥ x) * u i + (u ⬝ᵥ x) * v i) := by ring
          rw [hdecomp]
          refine Submodule.mem_sup.mpr ⟨M' *ᵥ x, ⟨x, rfl⟩,
            (dotProduct v x) • u + (dotProduct u x) • v, ?_, rfl⟩
          exact Submodule.add_mem S
            (Submodule.smul_mem S _ (Submodule.subset_span (Set.mem_insert u _)))
            (Submodule.smul_mem S _ (Submodule.subset_span (Set.mem_insert_of_mem u (Set.mem_singleton v))))
        · refine sup_le ?_ ?_
          · rintro w ⟨x, rfl⟩
            change M' *ᵥ x ∈ R
            have hdecomp : M' *ᵥ x = M *ᵥ x + ((dotProduct v x) • u + (dotProduct u x) • v) := by
              simp only [M', Matrix.add_mulVec, altOuter_mulVec]
            rw [hdecomp]
            exact Submodule.add_mem R ⟨x, rfl⟩
              (Submodule.add_mem R (Submodule.smul_mem R _ huR) (Submodule.smul_mem R _ hvR))
          · refine Submodule.span_le.mpr ?_
            intro w hw
            rcases hw with rfl | rfl
            · exact huR
            · exact hvR
      have hinf : R' ⊓ S = ⊥ := by
        rw [eq_bot_iff]
        rintro w ⟨⟨x, rfl⟩, hwS⟩
        rcases Submodule.mem_span_pair.mp hwS with ⟨c1, c2, hc⟩
        have hw_i0 : (M' *ᵥ x) i0 = 0 := by
          simp only [Matrix.mulVec, dotProduct]
          exact Finset.sum_eq_zero fun j _ => by rw [hM'_row_i0 j, zero_mul]
        have hw_j0 : (M' *ᵥ x) j0 = 0 := by
          simp only [Matrix.mulVec, dotProduct]
          exact Finset.sum_eq_zero fun j _ => by rw [hM'_row_j0 j, zero_mul]
        have hc1 : c1 = 0 := by
          have h := congrFun hc i0
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hu_i0, hv_i0, mul_one, mul_zero, add_zero] at h
          change c1 = (M' *ᵥ x) i0 at h
          rw [h, hw_i0]
        have hc2 : c2 = 0 := by
          have h := congrFun hc j0
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hu_j0, hv_j0, mul_one, mul_zero, zero_add] at h
          change c2 = (M' *ᵥ x) j0 at h
          rw [h, hw_j0]
        rw [hc1, hc2, zero_smul, zero_smul, add_zero] at hc
        exact hc.symm
      have hS_rank : Module.finrank (ZMod 2) S = 2 := by
        let φ : (Fin 2 → ZMod 2) →ₗ[ZMod 2] S :=
          { toFun := fun c => ⟨c 0 • u + c 1 • v, Submodule.add_mem S
              (Submodule.smul_mem S _ (Submodule.subset_span (Set.mem_insert u _)))
              (Submodule.smul_mem S _ (Submodule.subset_span (Set.mem_insert_of_mem u (Set.mem_singleton v))))⟩
            map_add' := fun c1 c2 => by ext i; simp [add_mul]; ring
            map_smul' := fun r c => by ext i; simp [mul_add, mul_assoc] }
        have hinj : Function.Injective φ := by
          intro c1 c2 heq
          have hval : c1 0 • u + c1 1 • v = c2 0 • u + c2 1 • v := congrArg Subtype.val heq
          funext t
          fin_cases t
          · have h := congrFun hval i0
            simpa [hu_i0, hv_i0] using h
          · have h := congrFun hval j0
            simpa [hu_j0, hv_j0] using h
        have hsurj : Function.Surjective φ := by
          rintro ⟨w, hw⟩
          rcases Submodule.mem_span_pair.mp hw with ⟨c0, c1, hc⟩
          exact ⟨![c0, c1], Subtype.ext (by simpa [φ] using hc)⟩
        have heq_fr := LinearEquiv.finrank_eq (LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩)
        rw [Module.finrank_fin_fun] at heq_fr
        exact heq_fr.symm
      have hrank_drop : M.rank = M'.rank + 2 := by
        have hsum := Submodule.finrank_sup_add_finrank_inf_eq R' S
        rw [← hR_eq, hinf, finrank_bot, add_zero, hS_rank] at hsum
        exact hsum
      rcases ih M'.rank (by omega) M' rfl hM'_alt with ⟨k', a', b', hM'_rk, hM'_eq⟩
      let a : Fin (k' + 1) → Fin d → ZMod 2 := fun p => if hp : p.val < k' then a' ⟨p.val, hp⟩ else u
      let b : Fin (k' + 1) → Fin d → ZMod 2 := fun p => if hp : p.val < k' then b' ⟨p.val, hp⟩ else v
      refine ⟨k' + 1, a, b, by omega, fun i j => ?_⟩
      rw [Fin.sum_univ_castSucc]
      have hlast : a (Fin.last k') i * b (Fin.last k') j + b (Fin.last k') i * a (Fin.last k') j =
          u i * v j + v i * u j := by simp [a, b]
      have hpref : ∑ p : Fin k', (a p.castSucc i * b p.castSucc j + b p.castSucc i * a p.castSucc j) = M' i j := by
        rw [hM'_eq i j]
        refine Finset.sum_congr rfl fun p _ => ?_
        simp [a, b, p.isLt]
      rw [hpref, hlast]
      simp only [M', Matrix.add_apply, altOuter]
      have h2 := zmod2_add_self (u i * v j + v i * u j)
      calc M i j = M i j + ((u i * v j + v i * u j) + (u i * v j + v i * u j)) := by rw [h2, add_zero]
        _ = M i j + (u i * v j + v i * u j) + (u i * v j + v i * u j) := by ring

private lemma alt_decomp {d : ℕ} (M : Matrix (Fin d) (Fin d) (ZMod 2)) (hM : isAlt M) :
    ∃ (k : ℕ) (a b : Fin k → Fin d → ZMod 2),
      M.rank = 2 * k ∧ ∀ i j : Fin d, M i j = ∑ p : Fin k, (a p i * b p j + b p i * a p j) :=
  alt_decomp_aux M.rank M rfl hM

private def mkTable {d : ℕ} (H : Matrix (Fin d) (Fin d) (ZMod 2)) (x y : Fin (d + 1)) : Bool :=
  Fin.cases false (fun i => Fin.cases false (fun j => decide (H i j ≠ 0)) y) x

private lemma b2z_mkTable_succ {d : ℕ} (H : Matrix (Fin d) (Fin d) (ZMod 2)) (i j : Fin d) :
    b2z (mkTable H i.succ j.succ) = H i j := by
  simp only [mkTable, Fin.cases_succ]
  exact b2z_decide_ne_zero (H i j)

private lemma deltaMat_mkTable {d : ℕ} (H : Matrix (Fin d) (Fin d) (ZMod 2)) (i j : Fin d) :
    deltaMat (fun x y => b2z (mkTable H x y)) i j = H i j := by
  simp only [deltaMat, mkTable, Fin.cases_zero, Fin.cases_succ, b2z, Bool.false_eq_true, ↓reduceIte, add_zero]
  exact b2z_decide_ne_zero (H i j)

private lemma fit_depth1_of_alt {d : ℕ} (M : Matrix (Fin d) (Fin d) (ZMod 2)) (hM : isAlt M)
    (t : ℕ) (ht : M.rank / 2 ≤ t) :
    ∃ C : Circuit,
      ReadsBack ((d + 1) + (d + 1)) C ∧
      (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧
      C.gates.countP nonlin ≤ t ∧
      (depthsOf ((d + 1) + (d + 1)) C.gates).getD C.output 0 ≤ 1 ∧
      Represents (mkTable M) C := by
  rcases alt_decomp M hM with ⟨k, a, b, hrank, hMeq⟩
  have hk_le : k ≤ t := by omega
  let pad : (Fin d → ZMod 2) → Fin (d + 1) → ZMod 2 := fun v => Fin.cases 0 v
  let qs : List (Quad (d + 1) (d + 1)) :=
    List.ofFn (fun p : Fin k => (pad (a p), pad (b p), pad (b p), pad (a p)))
  have hqs_len : qs.length = k := by simp [qs]
  rcases synth_depth1_quads (d + 1) (d + 1) 1 qs (fun _ _ => 1) (fun _ _ => 0) (fun _ _ => 0) with
    ⟨C0, tap, hrb, hfan, hcnt, htaps⟩
  refine ⟨⟨C0.gates, tap 0⟩, hrb, hfan, by dsimp only; omega, (htaps 0).1, fun x y => ?_⟩
  apply b2z_inj
  have h1 := (htaps 0).2 x y
  simp only [zero_add, one_mul] at h1
  change b2z ((wiresOf C0.gates (oneEach x y)).getD (tap 0) false) = b2z (mkTable M x y)
  rw [h1]
  have hsum_k : ∑ p : Fin qs.length, evalQuad (qs.get p) x y =
      ∑ p : Fin k, (pad (a p) x * pad (b p) y + pad (b p) x * pad (a p) y) := by
    refine Finset.sum_bij (fun p _ => ⟨p.val, by omega⟩) (fun _ _ => Finset.mem_univ _)
      (fun _ _ _ _ h => Fin.ext (Fin.mk.inj h))
      (fun p _ => ⟨⟨p.val, by omega⟩, Finset.mem_univ _, Fin.ext rfl⟩)
      (fun p _ => ?_)
    have hget : qs.get p = (pad (a ⟨p.val, by omega⟩), pad (b ⟨p.val, by omega⟩),
        pad (b ⟨p.val, by omega⟩), pad (a ⟨p.val, by omega⟩)) := by
      simp [qs, List.get_eq_getElem]
    rw [hget]; rfl
  rw [hsum_k]
  cases x using Fin.cases with
  | zero => simp [pad, mkTable, b2z]
  | succ i =>
    cases y using Fin.cases with
    | zero => simp [pad, mkTable, b2z]
    | succ j =>
      rw [b2z_mkTable_succ, hMeq i j]
      simp [pad]

private lemma rank_le_two_mul_of_fit_depth1 {d : ℕ} (M : Matrix (Fin d) (Fin d) (ZMod 2)) (t : ℕ)
    (C : Circuit) (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hcnt : C.gates.countP nonlin ≤ t)
    (hdep : (depthsOf ((d + 1) + (d + 1)) C.gates).getD C.output 0 ≤ 1)
    (hrep : Represents (mkTable M) C) :
    M.rank ≤ 2 * t := by
  rcases circuit_depth1_decomp (d + 1) (d + 1) C.gates hfan with ⟨qs, hqs_le, _, hdec1⟩
  rcases hdec1 C.output hdep with ⟨mask, α, β, hev⟩
  have hM_eq : ∀ i j : Fin d, M i j =
      ∑ p : Fin qs.length, mask p *
        (((qs.get p).1 i.succ + (qs.get p).1 0) * ((qs.get p).2.1 j.succ + (qs.get p).2.1 0) +
         ((qs.get p).2.2.1 i.succ + (qs.get p).2.2.1 0) * ((qs.get p).2.2.2 j.succ + (qs.get p).2.2.2 0)) := by
    intro i j
    rw [← deltaMat_mkTable M i j]
    have hfn : (fun x y => b2z (mkTable M x y)) =
        (fun x y => (α x + β y) + ∑ p : Fin qs.length, mask p * evalQuad (qs.get p) x y) := by
      funext x y
      have hr : (wiresOf C.gates (oneEach x y)).getD C.output false = mkTable M x y := hrep x y
      rw [← hr]
      exact hev x y
    rw [hfn, deltaMat_add, deltaMat_aff, zero_add, deltaMat_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [deltaMat_smul, deltaMat_quad]
  let u1 : Fin qs.length → Fin d → ZMod 2 := fun p i => (qs.get p).1 i.succ + (qs.get p).1 0
  let u2 : Fin qs.length → Fin d → ZMod 2 := fun p i => (qs.get p).2.2.1 i.succ + (qs.get p).2.2.1 0
  let Ψ : (Fin qs.length ⊕ Fin qs.length → ZMod 2) →ₗ[ZMod 2] (Fin d → ZMod 2) :=
    { toFun := fun c => ∑ p : Fin qs.length, (c (Sum.inl p) • u1 p + c (Sum.inr p) • u2 p)
      map_add' := fun c1 c2 => by
        funext i
        simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib]
        ring
      map_smul' := fun s c => by
        funext i
        simp only [Pi.smul_apply, Pi.add_apply, Finset.sum_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl fun p _ => by ring }
  have hle_range : LinearMap.range M.mulVecLin ≤ LinearMap.range Ψ := by
    rintro _ ⟨v, rfl⟩
    let c : Fin qs.length ⊕ Fin qs.length → ZMod 2 :=
      Sum.elim
        (fun p => mask p * ∑ j : Fin d, ((qs.get p).2.1 j.succ + (qs.get p).2.1 0) * v j)
        (fun p => mask p * ∑ j : Fin d, ((qs.get p).2.2.2 j.succ + (qs.get p).2.2.2 0) * v j)
    refine ⟨c, ?_⟩
    funext i
    change (Ψ c) i = (M *ᵥ v) i
    simp only [Ψ, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, c, Sum.elim_inl, Sum.elim_inr, Matrix.mulVec, dotProduct, u1, u2]
    simp_rw [hM_eq i, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => by ring
  have h1 : M.rank ≤ Module.finrank (ZMod 2) (LinearMap.range Ψ) := Submodule.finrank_mono hle_range
  have h2 : Module.finrank (ZMod 2) (LinearMap.range Ψ) ≤
      Module.finrank (ZMod 2) (Fin qs.length ⊕ Fin qs.length → ZMod 2) := by
    have hkn := LinearMap.finrank_range_add_finrank_ker Ψ
    omega
  have h3 : Module.finrank (ZMod 2) (Fin qs.length ⊕ Fin qs.length → ZMod 2) = 2 * qs.length := by
    rw [Module.finrank_pi_fintype]
    simp [Fintype.card_sum, Fintype.card_fin]
    omega
  omega

private lemma rank_mul_le_left {m n k : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2))
    (B : Matrix (Fin n) (Fin k) (ZMod 2)) : (A * B).rank ≤ A.rank := by
  change Module.finrank (ZMod 2) (LinearMap.range (A * B).mulVecLin) ≤
    Module.finrank (ZMod 2) (LinearMap.range A.mulVecLin)
  apply Submodule.finrank_mono
  rw [Matrix.mulVecLin_mul]
  exact LinearMap.range_comp_le_range _ _

private lemma rank_mul_le_right {m n k : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2))
    (B : Matrix (Fin n) (Fin k) (ZMod 2)) : (A * B).rank ≤ B.rank := by
  change Module.finrank (ZMod 2) (LinearMap.range (A * B).mulVecLin) ≤
    Module.finrank (ZMod 2) (LinearMap.range B.mulVecLin)
  rw [Matrix.mulVecLin_mul, LinearMap.range_comp]
  exact Submodule.finrank_map_le _ _

private lemma rank_add_le {m n : ℕ} (A B : Matrix (Fin m) (Fin n) (ZMod 2)) :
    (A + B).rank ≤ A.rank + B.rank := by
  have hle : LinearMap.range (A + B).mulVecLin ≤
      LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin := by
    rintro _ ⟨x, rfl⟩
    change (A + B) *ᵥ x ∈ _
    rw [Matrix.add_mulVec]
    exact Submodule.mem_sup.mpr ⟨A *ᵥ x, ⟨x, rfl⟩, B *ᵥ x, ⟨x, rfl⟩, rfl⟩
  have h1 : (A + B).rank ≤ Module.finrank (ZMod 2)
      ↥(LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin) := Submodule.finrank_mono hle
  have h2 := Submodule.finrank_sup_add_finrank_inf_eq
    (LinearMap.range A.mulVecLin) (LinearMap.range B.mulVecLin)
  have hA : A.rank = Module.finrank (ZMod 2) (LinearMap.range A.mulVecLin) := rfl
  have hB : B.rank = Module.finrank (ZMod 2) (LinearMap.range B.mulVecLin) := rfl
  omega

private lemma rank_involution_diff_le {d : ℕ} (U H : Matrix (Fin d) (Fin d) (ZMod 2))
    (hU : U * U = 1) (hH : isAlt H) :
    let r := (U - 1).rank
    let w := if d = 2 * r ∧ r % 2 = 1 then r - 1 else r
    (U * H * Uᵀ + H).rank ≤ 2 * w := by
  intro r w
  let N := U - 1
  let D := U * H * Uᵀ + H
  have hU_eq : U = N + 1 := by
    ext i j
    simp only [N, Matrix.sub_apply, Matrix.add_apply, zmod2_sub_eq_add]
    have h2 := zmod2_add_self ((1 : Matrix (Fin d) (Fin d) (ZMod 2)) i j)
    calc U i j = U i j + ((1 : Matrix (Fin d) (Fin d) (ZMod 2)) i j +
          (1 : Matrix (Fin d) (Fin d) (ZMod 2)) i j) := by rw [h2, add_zero]
      _ = U i j + (1 : Matrix (Fin d) (Fin d) (ZMod 2)) i j +
          (1 : Matrix (Fin d) (Fin d) (ZMod 2)) i j := by ring
  have hN2 : N * N = 0 := by
    have h1 : N * N = U * U - U - U + 1 := by
      simp only [N]
      rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one]
      ext i j; simp; ring
    rw [h1, hU]
    ext i j
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.zero_apply, zmod2_sub_eq_add]
    have ha := zmod2_add_self ((1 : Matrix (Fin d) (Fin d) (ZMod 2)) i j)
    have hb := zmod2_add_self (U i j)
    calc (1 : Matrix (Fin d) (Fin d) (ZMod 2)) i j + U i j + U i j +
          (1 : Matrix (Fin d) (Fin d) (ZMod 2)) i j
        = ((1 : Matrix (Fin d) (Fin d) (ZMod 2)) i j + (1 : Matrix (Fin d) (Fin d) (ZMod 2)) i j) +
          (U i j + U i j) := by ring
      _ = 0 := by rw [ha, hb, add_zero]
  have hD_eq : D = N * (H * Uᵀ) + H * Nᵀ := by
    have hUt : Uᵀ = Nᵀ + 1 := by rw [hU_eq, Matrix.transpose_add, Matrix.transpose_one]
    have hHH : H + H = 0 := by ext i j; exact zmod2_add_self (H i j)
    calc D = (N + 1) * H * Uᵀ + H := by simp only [D]; rw [← hU_eq]
      _ = N * (H * Uᵀ) + H * Uᵀ + H := by rw [Matrix.add_mul, Matrix.one_mul, Matrix.add_mul, Matrix.mul_assoc]
      _ = N * (H * Uᵀ) + H * (Nᵀ + 1) + H := by rw [hUt]
      _ = N * (H * Uᵀ) + (H * Nᵀ + H) + H := by rw [Matrix.mul_add, Matrix.mul_one]
      _ = N * (H * Uᵀ) + H * Nᵀ + (H + H) := by abel
      _ = N * (H * Uᵀ) + H * Nᵀ := by rw [hHH, add_zero]
  have hle2r : D.rank ≤ 2 * r := by
    have h1 := rank_add_le (N * (H * Uᵀ)) (H * Nᵀ)
    rw [← hD_eq] at h1
    have h2 : (N * (H * Uᵀ)).rank ≤ N.rank := rank_mul_le_left N (H * Uᵀ)
    have h3 : (H * Nᵀ).rank ≤ Nᵀ.rank := rank_mul_le_right H Nᵀ
    have h4 : Nᵀ.rank = N.rank := Matrix.rank_transpose N
    have hNr : N.rank = r := rfl
    omega
  by_cases hexc : d = 2 * r ∧ r % 2 = 1
  · have hw_eq : w = r - 1 := if_pos hexc
    rw [hw_eq]
    have hD_alt : isAlt D := isAlt_add (isAlt_conj U H hH) hH
    rcases alt_decomp D hD_alt with ⟨kD, _, _, hD_even, _⟩
    let K : Submodule (ZMod 2) (Fin d → ZMod 2) := LinearMap.ker Nᵀ.mulVecLin
    have hfinK : Module.finrank (ZMod 2) K = r := by
      have hkn := LinearMap.finrank_range_add_finrank_ker Nᵀ.mulVecLin
      rw [Module.finrank_fin_fun] at hkn
      have hNt : Module.finrank (ZMod 2) (LinearMap.range Nᵀ.mulVecLin) = r := by
        change Nᵀ.rank = r
        rw [Matrix.rank_transpose N]
      have hKeq : Module.finrank (ZMod 2) K = Module.finrank (ZMod 2) (LinearMap.ker Nᵀ.mulVecLin) := rfl
      omega
    let eK : Module.Basis (Fin r) (ZMod 2) K := (Module.finBasis (ZMod 2) K).reindex (finCongr hfinK)
    let bK : Fin r → (Fin d → ZMod 2) := fun a => (eK a).1
    let A : Matrix (Fin r) (Fin r) (ZMod 2) := fun a b => dotProduct (bK a) (H *ᵥ bK b)
    have hA_alt : isAlt A := by
      refine ⟨?_, fun a => alt_quad_zero hH (bK a)⟩
      ext a b
      change dotProduct (bK b) (H *ᵥ bK a) = dotProduct (bK a) (H *ᵥ bK b)
      rw [dot_mulVec_eq H (bK b) (bK a), hH.1, dotProduct_comm]
    rcases alt_decomp A hA_alt with ⟨kA, _, _, hA_even, _⟩
    have hA_le : A.rank ≤ r := by
      have hkn := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
      rw [Module.finrank_fin_fun] at hkn
      change A.rank + _ = r at hkn
      omega
    have hA_lt : A.rank < r := by omega
    have hkerA_pos : 0 < Module.finrank (ZMod 2) (LinearMap.ker A.mulVecLin) := by
      have hkn := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
      rw [Module.finrank_fin_fun] at hkn
      change A.rank + _ = r at hkn
      omega
    have hkerA_ne : LinearMap.ker A.mulVecLin ≠ ⊥ := by
      intro hbot
      rw [hbot, finrank_bot] at hkerA_pos
      omega
    have hex_c : ∃ c : Fin r → ZMod 2, c ≠ 0 ∧ A *ᵥ c = 0 := by
      rcases Submodule.exists_mem_ne_zero_of_ne_bot hkerA_ne with ⟨c, hc_mem, hc_ne⟩
      exact ⟨c, hc_ne, hc_mem⟩
    rcases hex_c with ⟨c, hc_ne, hAc⟩
    let x0K : K := ∑ b : Fin r, c b • eK b
    let x0 : Fin d → ZMod 2 := x0K.1
    have hx0_ne : x0 ≠ 0 := by
      intro hx0
      apply hc_ne
      have h0K : x0K = 0 := Subtype.ext hx0
      have h0 := (Fintype.linearIndependent_iff.mp eK.linearIndependent) c h0K
      funext b
      exact h0 b
    have hx0_sum : x0 = ∑ b : Fin r, c b • bK b := by
      change (∑ b : Fin r, c b • eK b : K).1 = _
      simp [bK]
    have hHx0_perp : ∀ a : Fin r, dotProduct (bK a) (H *ᵥ x0) = 0 := by
      intro a
      rw [hx0_sum]
      have h1 : H *ᵥ (∑ b : Fin r, c b • bK b) = ∑ b : Fin r, c b • (H *ᵥ bK b) := by
        change H.mulVecLin (∑ b : Fin r, c b • bK b) = _
        simp [map_sum, map_smul]
      rw [h1]
      have h2 : dotProduct (bK a) (∑ b : Fin r, c b • (H *ᵥ bK b)) = (A *ᵥ c) a := by
        simp only [dotProduct, Matrix.mulVec, A, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
          Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun j _ => by ring
      rw [h2, hAc]
      rfl
    let MK : Matrix (Fin r) (Fin d) (ZMod 2) := fun a j => bK a j
    have hMKt_inj : Function.Injective MKᵀ.mulVecLin := by
      intro v1 v2 heq
      have hdiff : MKᵀ *ᵥ (v1 - v2) = 0 := by
        change MKᵀ.mulVecLin (v1 - v2) = 0
        rw [map_sub, heq, sub_self]
      have hsum0 : ∑ a : Fin r, (v1 a - v2 a) • eK a = 0 := by
        apply Subtype.ext
        have hcoe : (∑ a : Fin r, (v1 a - v2 a) • eK a : K).1 = ∑ a : Fin r, (v1 a - v2 a) • bK a := by
          simp [bK]
        rw [hcoe]
        funext j
        have hj := congrFun hdiff j
        simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, MK, Pi.sub_apply, Pi.zero_apply] at hj
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ZeroMemClass.coe_zero, Pi.zero_apply]
        rw [← hj]
        refine Finset.sum_congr rfl fun a _ => ?_
        change (v1 a - v2 a) * bK a j = bK a j * (v1 a - v2 a)
        ring
      have h0 := (Fintype.linearIndependent_iff.mp eK.linearIndependent) (fun a => v1 a - v2 a) hsum0
      funext a
      exact sub_eq_zero.mp (h0 a)
    have hMK_rank : MK.rank = r := by
      rw [← Matrix.rank_transpose MK]
      have hkn := LinearMap.finrank_range_add_finrank_ker MKᵀ.mulVecLin
      rw [LinearMap.ker_eq_bot.mpr hMKt_inj, finrank_bot, add_zero, Module.finrank_fin_fun] at hkn
      exact hkn
    have hR_le_kerMK : LinearMap.range N.mulVecLin ≤ LinearMap.ker MK.mulVecLin := by
      rintro _ ⟨u, rfl⟩
      change MK *ᵥ (N *ᵥ u) = 0
      funext a
      change dotProduct (bK a) (N *ᵥ u) = 0
      rw [dot_mulVec_eq N (bK a) u]
      have hNt0 : Nᵀ *ᵥ bK a = 0 := (eK a).2
      rw [hNt0, zero_dotProduct]
    have hfin_kerMK : Module.finrank (ZMod 2) (LinearMap.ker MK.mulVecLin) = r := by
      have hkn := LinearMap.finrank_range_add_finrank_ker MK.mulVecLin
      rw [Module.finrank_fin_fun] at hkn
      change MK.rank + _ = d at hkn
      omega
    have hR_eq_kerMK : LinearMap.range N.mulVecLin = LinearMap.ker MK.mulVecLin :=
      Submodule.eq_of_le_of_finrank_eq hR_le_kerMK (by change r = _; omega)
    have hHx0_in_R : H *ᵥ x0 ∈ LinearMap.range N.mulVecLin := by
      rw [hR_eq_kerMK]
      change MK *ᵥ (H *ᵥ x0) = 0
      funext a
      exact hHx0_perp a
    rcases hHx0_in_R with ⟨u, hu⟩
    have hNHx0 : N *ᵥ (H *ᵥ x0) = 0 := by
      change N *ᵥ (H *ᵥ x0) = 0
      rw [← hu]
      change N *ᵥ (N *ᵥ u) = 0
      rw [Matrix.mulVec_mulVec, hN2, Matrix.zero_mulVec]
    have hNtx0 : Nᵀ *ᵥ x0 = 0 := x0K.2
    have hUtx0 : Uᵀ *ᵥ x0 = x0 := by
      have hUt : Uᵀ = Nᵀ + 1 := by rw [hU_eq, Matrix.transpose_add, Matrix.transpose_one]
      rw [hUt, Matrix.add_mulVec, hNtx0, zero_add, Matrix.one_mulVec]
    have hDx0 : D *ᵥ x0 = 0 := by
      rw [hD_eq, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        ← Matrix.mulVec_mulVec, hUtx0, hNHx0, hNtx0, Matrix.mulVec_zero, add_zero]
    have hkerD_pos : 0 < Module.finrank (ZMod 2) (LinearMap.ker D.mulVecLin) := by
      let ψ : (Fin 1 → ZMod 2) →ₗ[ZMod 2] LinearMap.ker D.mulVecLin :=
        { toFun := fun s => ⟨s 0 • x0, by
            change D.mulVecLin (s 0 • x0) = 0
            rw [map_smul]
            change s 0 • (D *ᵥ x0) = 0
            rw [hDx0, smul_zero]⟩
          map_add' := fun s1 s2 => by apply Subtype.ext; simp [add_smul]
          map_smul' := fun r0 s => by apply Subtype.ext; simp [smul_smul] }
      have hψ_inj : Function.Injective ψ := by
        intro s1 s2 h
        have hv : s1 0 • x0 = s2 0 • x0 := congrArg Subtype.val h
        have hsub : (s1 0 - s2 0) • x0 = 0 := by rw [sub_smul, hv, sub_self]
        rcases smul_eq_zero.mp hsub with h0 | hx
        · funext i; fin_cases i; exact sub_eq_zero.mp h0
        · exact (hx0_ne hx).elim
      have hle := LinearMap.finrank_le_finrank_of_injective hψ_inj
      rw [Module.finrank_fin_fun] at hle
      omega
    have hD_lt : D.rank < d := by
      have hkn := LinearMap.finrank_range_add_finrank_ker D.mulVecLin
      rw [Module.finrank_fin_fun] at hkn
      change D.rank + _ = d at hkn
      omega
    have hd_eq : d = 2 * r := hexc.1
    have hr_odd : r % 2 = 1 := hexc.2
    change D.rank ≤ 2 * (r - 1)
    omega
  · have hw_eq : w = r := if_neg hexc
    rw [hw_eq]
    exact hle2r

private lemma exists_adapted_basis {d r : ℕ} (N : Matrix (Fin d) (Fin d) (ZMod 2))
    (hN2 : N * N = 0) (hr : N.rank = r) :
    2 * r ≤ d ∧
    ∃ (a b : Fin r → Fin d → ZMod 2) (c : Fin (d - 2 * r) → Fin d → ZMod 2),
      (∀ i : Fin r, N *ᵥ b i = a i) ∧
      (∀ i : Fin r, N *ᵥ a i = 0) ∧
      (∀ l : Fin (d - 2 * r), N *ᵥ c l = 0) ∧
      LinearIndependent (ZMod 2)
        (fun p : Fin r ⊕ Fin r ⊕ Fin (d - 2 * r) =>
          match p with
          | Sum.inl i => a i
          | Sum.inr (Sum.inl i) => b i
          | Sum.inr (Sum.inr l) => c l) := by
  let R : Submodule (ZMod 2) (Fin d → ZMod 2) := LinearMap.range N.mulVecLin
  let K : Submodule (ZMod 2) (Fin d → ZMod 2) := LinearMap.ker N.mulVecLin
  have hRK : R ≤ K := by
    rintro _ ⟨x, rfl⟩
    change N *ᵥ (N *ᵥ x) = 0
    rw [Matrix.mulVec_mulVec, hN2, Matrix.zero_mulVec]
  have hfinR : Module.finrank (ZMod 2) R = r := hr
  have hfinK : Module.finrank (ZMod 2) K = d - r := by
    have hkn := LinearMap.finrank_range_add_finrank_ker N.mulVecLin
    rw [Module.finrank_fin_fun] at hkn
    have hKeq : Module.finrank (ZMod 2) K = Module.finrank (ZMod 2) (LinearMap.ker N.mulVecLin) := rfl
    have hReq : Module.finrank (ZMod 2) (LinearMap.range N.mulVecLin) = r := hr
    omega
  have h2r_le : 2 * r ≤ d := by
    have hle := Submodule.finrank_mono hRK
    omega
  refine ⟨h2r_le, ?_⟩
  let eR : Module.Basis (Fin r) (ZMod 2) R := (Module.finBasis (ZMod 2) R).reindex (finCongr hfinR)
  let a : Fin r → Fin d → ZMod 2 := fun i => (eR i).1
  have ha_mem : ∀ i : Fin r, a i ∈ R := fun i => (eR i).2
  let b : Fin r → Fin d → ZMod 2 := fun i => Classical.choose (ha_mem i)
  have hNb : ∀ i : Fin r, N *ᵥ b i = a i := fun i => Classical.choose_spec (ha_mem i)
  have hNa : ∀ i : Fin r, N *ᵥ a i = 0 := fun i => hRK (ha_mem i)
  let RinK : Submodule (ZMod 2) K := R.comap K.subtype
  have hRinK_map : RinK.map K.subtype = R := by
    rw [Submodule.map_comap_eq, Submodule.range_subtype]
    exact inf_eq_right.mpr hRK
  rcases Submodule.exists_isCompl RinK with ⟨CinK, hcompl⟩
  let C : Submodule (ZMod 2) (Fin d → ZMod 2) := CinK.map K.subtype
  have hCK : C ≤ K := by
    rintro x ⟨y, _, rfl⟩; exact y.2
  have hRC_sup : R ⊔ C = K := by
    have h1 : (RinK ⊔ CinK).map K.subtype = RinK.map K.subtype ⊔ CinK.map K.subtype :=
      Submodule.map_sup RinK CinK K.subtype
    rw [hcompl.sup_eq_top, hRinK_map, Submodule.map_top, Submodule.range_subtype] at h1
    exact h1.symm
  have hRC_inf : R ⊓ C = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxR, hxC⟩
    rcases hxC with ⟨y, hyC, rfl⟩
    have hyR : y ∈ RinK := hxR
    have hy0 : y ∈ RinK ⊓ CinK := ⟨hyR, hyC⟩
    rw [hcompl.inf_eq_bot, Submodule.mem_bot] at hy0
    simp [hy0]
  have hfinC : Module.finrank (ZMod 2) C = d - 2 * r := by
    have hsum := Submodule.finrank_sup_add_finrank_inf_eq R C
    rw [hRC_sup, hRC_inf, finrank_bot, add_zero, hfinR, hfinK] at hsum
    omega
  let eC : Module.Basis (Fin (d - 2 * r)) (ZMod 2) C :=
    (Module.finBasis (ZMod 2) C).reindex (finCongr hfinC)
  let c : Fin (d - 2 * r) → Fin d → ZMod 2 := fun l => (eC l).1
  have hc_mem : ∀ l : Fin (d - 2 * r), c l ∈ C := fun l => (eC l).2
  have hNc : ∀ l : Fin (d - 2 * r), N *ᵥ c l = 0 := fun l => hCK (hc_mem l)
  refine ⟨a, b, c, hNb, hNa, hNc, ?_⟩
  let v : Fin r ⊕ Fin r ⊕ Fin (d - 2 * r) → Fin d → ZMod 2 := fun p =>
    match p with
    | Sum.inl i => a i
    | Sum.inr (Sum.inl i) => b i
    | Sum.inr (Sum.inr l) => c l
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hsplit : ∑ i : Fin r, g (Sum.inl i) • a i +
      ∑ i : Fin r, g (Sum.inr (Sum.inl i)) • b i +
      ∑ l : Fin (d - 2 * r), g (Sum.inr (Sum.inr l)) • c l = 0 := by
    have h1 := hg
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type] at h1
    simpa [v, add_assoc] using h1
  have hgy : ∀ i : Fin r, g (Sum.inr (Sum.inl i)) = 0 := by
    have hN0 : N *ᵥ (∑ i : Fin r, g (Sum.inl i) • a i +
        ∑ i : Fin r, g (Sum.inr (Sum.inl i)) • b i +
        ∑ l : Fin (d - 2 * r), g (Sum.inr (Sum.inr l)) • c l) = 0 := by
      rw [hsplit, Matrix.mulVec_zero]
    have hNb_sum : ∑ i : Fin r, g (Sum.inr (Sum.inl i)) • a i = 0 := by
      change N.mulVecLin _ = 0 at hN0
      simp only [map_add, map_sum, map_smul] at hN0
      have hA0 : ∑ i : Fin r, g (Sum.inl i) • N.mulVecLin (a i) = 0 :=
        Finset.sum_eq_zero fun i _ => by change g (Sum.inl i) • (N *ᵥ a i) = 0; rw [hNa i, smul_zero]
      have hC0 : ∑ l : Fin (d - 2 * r), g (Sum.inr (Sum.inr l)) • N.mulVecLin (c l) = 0 :=
        Finset.sum_eq_zero fun l _ => by change g (Sum.inr (Sum.inr l)) • (N *ᵥ c l) = 0; rw [hNc l, smul_zero]
      have hB_eq : ∑ i : Fin r, g (Sum.inr (Sum.inl i)) • N.mulVecLin (b i) =
          ∑ i : Fin r, g (Sum.inr (Sum.inl i)) • a i :=
        Finset.sum_congr rfl fun i _ => by change g _ • (N *ᵥ b i) = _; rw [hNb i]
      rw [hA0, hC0, hB_eq, zero_add, add_zero] at hN0
      exact hN0
    have h0R : ∑ i : Fin r, g (Sum.inr (Sum.inl i)) • eR i = 0 := by
      apply Subtype.ext; simpa [a] using hNb_sum
    exact (Fintype.linearIndependent_iff.mp eR.linearIndependent) (fun i => g (Sum.inr (Sum.inl i))) h0R
  have hB0 : ∑ i : Fin r, g (Sum.inr (Sum.inl i)) • b i = 0 :=
    Finset.sum_eq_zero fun i _ => by rw [hgy i, zero_smul]
  rw [hB0, add_zero] at hsplit
  let sumA : Fin d → ZMod 2 := ∑ i : Fin r, g (Sum.inl i) • a i
  let sumC : Fin d → ZMod 2 := ∑ l : Fin (d - 2 * r), g (Sum.inr (Sum.inr l)) • c l
  have hsumA_in : sumA ∈ R := Submodule.sum_mem R fun i _ => Submodule.smul_mem R _ (ha_mem i)
  have hsumC_in : sumC ∈ C := Submodule.sum_mem C fun l _ => Submodule.smul_mem C _ (hc_mem l)
  have hsumA_eq_C : sumA = sumC := by
    have h2 : sumA + sumA = 0 := by funext j; exact zmod2_add_self _
    calc sumA = sumA + (sumA + sumC) := by rw [hsplit, add_zero]
      _ = (sumA + sumA) + sumC := by rw [add_assoc]
      _ = sumC := by rw [h2, zero_add]
  have hsumA0 : sumA = 0 := by
    have hmem : sumA ∈ R ⊓ C := ⟨hsumA_in, hsumA_eq_C ▸ hsumC_in⟩
    rw [hRC_inf, Submodule.mem_bot] at hmem
    exact hmem
  have hsumC0 : sumC = 0 := by rw [← hsumA_eq_C, hsumA0]
  have hgx : ∀ i : Fin r, g (Sum.inl i) = 0 := by
    have h0R : ∑ i : Fin r, g (Sum.inl i) • eR i = 0 := by
      apply Subtype.ext; simpa [sumA, a] using hsumA0
    exact (Fintype.linearIndependent_iff.mp eR.linearIndependent) (fun i => g (Sum.inl i)) h0R
  have hgz : ∀ l : Fin (d - 2 * r), g (Sum.inr (Sum.inr l)) = 0 := by
    have h0C : ∑ l : Fin (d - 2 * r), g (Sum.inr (Sum.inr l)) • eC l = 0 := by
      apply Subtype.ext; simpa [sumC, c] using hsumC0
    exact (Fintype.linearIndependent_iff.mp eC.linearIndependent) (fun l => g (Sum.inr (Sum.inr l))) h0C
  intro p
  rcases p with i | (i | l)
  · exact hgx i
  · exact hgy i
  · exact hgz l

private lemma exists_alt_involution_rank_ge {d : ℕ} (U : Matrix (Fin d) (Fin d) (ZMod 2))
    (hU : U * U = 1) :
    let r := (U - 1).rank
    let w := if d = 2 * r ∧ r % 2 = 1 then r - 1 else r
    ∃ H : Matrix (Fin d) (Fin d) (ZMod 2), isAlt H ∧ 2 * w ≤ (U * H * Uᵀ + H).rank := by
  classical
  intro r w
  let N := U - 1
  have hU_eq : U = N + 1 := by
    ext i j
    simp only [N, Matrix.sub_apply, Matrix.add_apply, zmod2_sub_eq_add]
    have h2 := zmod2_add_self ((1 : Matrix (Fin d) (Fin d) (ZMod 2)) i j)
    calc U i j = U i j + ((1 : Matrix (Fin d) (Fin d) (ZMod 2)) i j +
          (1 : Matrix (Fin d) (Fin d) (ZMod 2)) i j) := by rw [h2, add_zero]
      _ = U i j + (1 : Matrix (Fin d) (Fin d) (ZMod 2)) i j +
          (1 : Matrix (Fin d) (Fin d) (ZMod 2)) i j := by ring
  have hN2 : N * N = 0 := by
    have h1 : N * N = U * U - U - U + 1 := by
      simp only [N]
      rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one]
      ext i j; simp; ring
    rw [h1, hU]
    ext i j
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.zero_apply, zmod2_sub_eq_add]
    have ha := zmod2_add_self ((1 : Matrix (Fin d) (Fin d) (ZMod 2)) i j)
    have hb := zmod2_add_self (U i j)
    calc (1 : Matrix (Fin d) (Fin d) (ZMod 2)) i j + U i j + U i j +
          (1 : Matrix (Fin d) (Fin d) (ZMod 2)) i j
        = ((1 : Matrix (Fin d) (Fin d) (ZMod 2)) i j + (1 : Matrix (Fin d) (Fin d) (ZMod 2)) i j) +
          (U i j + U i j) := by ring
      _ = 0 := by rw [ha, hb, add_zero]
  rcases exists_adapted_basis (r := r) N hN2 rfl with ⟨h2r_le, a, b, c, hNb, hNa, hNc, hlin⟩
  let I := Fin r ⊕ Fin r ⊕ Fin (d - 2 * r)
  let v : I → Fin d → ZMod 2 := fun p =>
    match p with
    | Sum.inl i => a i
    | Sum.inr (Sum.inl i) => b i
    | Sum.inr (Sum.inr l) => c l
  have hlin' : LinearIndependent (ZMod 2) v := hlin
  have hcardI : Fintype.card I = d := by
    simp only [I, Fintype.card_sum, Fintype.card_fin]
    omega
  have hdual_ex : ∀ p0 : I, ∃ x : Fin d → ZMod 2, ∀ p : I, dotProduct (v p) x = if p = p0 then 1 else 0 := by
    let Mv : Matrix I (Fin d) (ZMod 2) := fun p j => v p j
    have hMvt_inj : Function.Injective Mvᵀ.mulVecLin := by
      intro g1 g2 heq
      have hdiff : Mvᵀ *ᵥ (g1 - g2) = 0 := by
        change Mvᵀ.mulVecLin (g1 - g2) = 0
        rw [map_sub, heq, sub_self]
      have hsum0 : ∑ p : I, (g1 p - g2 p) • v p = 0 := by
        funext j
        have hj := congrFun hdiff j
        simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Mv, Pi.zero_apply] at hj
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
        rw [← hj]
        refine Finset.sum_congr rfl fun p _ => ?_
        change (g1 p - g2 p) * v p j = v p j * (g1 p - g2 p)
        ring
      have h0 := (Fintype.linearIndependent_iff.mp hlin') (fun p => g1 p - g2 p) hsum0
      funext p
      exact sub_eq_zero.mp (h0 p)
    have hMv_rank : Mv.rank = d := by
      rw [← Matrix.rank_transpose Mv]
      have hkn := LinearMap.finrank_range_add_finrank_ker Mvᵀ.mulVecLin
      rw [LinearMap.ker_eq_bot.mpr hMvt_inj, finrank_bot, add_zero, Module.finrank_pi_fintype] at hkn
      change Module.finrank (ZMod 2) (LinearMap.range Mvᵀ.mulVecLin) = d
      simp [hcardI] at hkn
      exact hkn
    have hMv_top : LinearMap.range Mv.mulVecLin = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      change Mv.rank = Module.finrank (ZMod 2) (I → ZMod 2)
      rw [hMv_rank, Module.finrank_pi_fintype]
      simp [hcardI]
    intro p0
    have hmem : Pi.single p0 (1 : ZMod 2) ∈ LinearMap.range Mv.mulVecLin := by rw [hMv_top]; trivial
    rcases hmem with ⟨x, hx⟩
    refine ⟨x, fun p => ?_⟩
    have hp := congrFun hx p
    change (Mv *ᵥ x) p = (Pi.single p0 (1 : ZMod 2) : I → ZMod 2) p at hp
    simpa [Mv, Matrix.mulVec, Pi.single_apply] using hp
  let dual : I → Fin d → ZMod 2 := fun p0 => Classical.choose (hdual_ex p0)
  have hdual : ∀ p p0 : I, dotProduct (v p) (dual p0) = if p = p0 then 1 else 0 :=
    fun p p0 => Classical.choose_spec (hdual_ex p0) p
  have hUa : ∀ i : Fin r, U *ᵥ a i = a i := fun i => by
    rw [hU_eq, Matrix.add_mulVec, hNa i, zero_add, Matrix.one_mulVec]
  have hUb : ∀ i : Fin r, U *ᵥ b i = a i + b i := fun i => by
    rw [hU_eq, Matrix.add_mulVec, hNb i, Matrix.one_mulVec]
  have hUc : ∀ l : Fin (d - 2 * r), U *ᵥ c l = c l := fun l => by
    rw [hU_eq, Matrix.add_mulVec, hNc l, zero_add, Matrix.one_mulVec]
  let k := r / 2
  have hk_def : k = r / 2 := rfl
  let i0 : Fin k → Fin r := fun j => ⟨2 * j.val, by omega⟩
  let i1 : Fin k → Fin r := fun j => ⟨2 * j.val + 1, by omega⟩
  let Hpair : Matrix (Fin d) (Fin d) (ZMod 2) := ∑ j : Fin k, altOuter (b (i0 j)) (b (i1 j))
  let Hextra : Matrix (Fin d) (Fin d) (ZMod 2) :=
    if h : r % 2 = 1 ∧ 2 * r < d then altOuter (b ⟨2 * k, by omega⟩) (c ⟨0, by omega⟩) else 0
  let H : Matrix (Fin d) (Fin d) (ZMod 2) := Hpair + Hextra
  have hHpair_alt : isAlt Hpair := by
    refine ⟨?_, fun x => ?_⟩
    · simp only [Hpair, Matrix.transpose_sum]
      exact Finset.sum_congr rfl fun j _ => (isAlt_altOuter _ _).1
    · simp only [Hpair, Matrix.sum_apply]
      exact Finset.sum_eq_zero fun j _ => (isAlt_altOuter _ _).2 x
  have hHextra_alt : isAlt Hextra := by
    by_cases h : r % 2 = 1 ∧ 2 * r < d
    · simp only [Hextra, dif_pos h]; exact isAlt_altOuter _ _
    · simp only [Hextra, dif_neg h]; exact ⟨by simp, fun _ => rfl⟩
  have hH_alt : isAlt H := isAlt_add hHpair_alt hHextra_alt
  refine ⟨H, hH_alt, ?_⟩
  let D := U * H * Uᵀ + H
  have hD_pair : ∀ j : Fin k,
      U * altOuter (b (i0 j)) (b (i1 j)) * Uᵀ + altOuter (b (i0 j)) (b (i1 j)) =
      altOuter (a (i0 j)) (a (i1 j)) + altOuter (a (i0 j)) (b (i1 j)) + altOuter (b (i0 j)) (a (i1 j)) := by
    intro j
    rw [altOuter_conj, hUb, hUb]
    ext x y
    simp only [Matrix.add_apply, altOuter, Pi.add_apply]
    have h2 := zmod2_add_self (b (i0 j) x * b (i1 j) y + b (i1 j) x * b (i0 j) y)
    calc (a (i0 j) x + b (i0 j) x) * (a (i1 j) y + b (i1 j) y) +
          (a (i1 j) x + b (i1 j) x) * (a (i0 j) y + b (i0 j) y) +
          (b (i0 j) x * b (i1 j) y + b (i1 j) x * b (i0 j) y)
        = (a (i0 j) x * a (i1 j) y + a (i1 j) x * a (i0 j) y) +
          (a (i0 j) x * b (i1 j) y + b (i1 j) x * a (i0 j) y) +
          (b (i0 j) x * a (i1 j) y + a (i1 j) x * b (i0 j) y) +
          ((b (i0 j) x * b (i1 j) y + b (i1 j) x * b (i0 j) y) +
           (b (i0 j) x * b (i1 j) y + b (i1 j) x * b (i0 j) y)) := by ring
      _ = _ := by rw [h2, add_zero]
  have hD_extra : U * Hextra * Uᵀ + Hextra =
      if h : r % 2 = 1 ∧ 2 * r < d then altOuter (a ⟨2 * k, by omega⟩) (c ⟨0, by omega⟩) else 0 := by
    by_cases h : r % 2 = 1 ∧ 2 * r < d
    · simp only [Hextra, dif_pos h]
      rw [altOuter_conj, hUb, hUc]
      ext x y
      simp only [Matrix.add_apply, altOuter, Pi.add_apply]
      have h2 := zmod2_add_self (b ⟨2 * k, by omega⟩ x * c ⟨0, by omega⟩ y +
        c ⟨0, by omega⟩ x * b ⟨2 * k, by omega⟩ y)
      calc (a ⟨2 * k, by omega⟩ x + b ⟨2 * k, by omega⟩ x) * c ⟨0, by omega⟩ y +
            c ⟨0, by omega⟩ x * (a ⟨2 * k, by omega⟩ y + b ⟨2 * k, by omega⟩ y) +
            (b ⟨2 * k, by omega⟩ x * c ⟨0, by omega⟩ y + c ⟨0, by omega⟩ x * b ⟨2 * k, by omega⟩ y)
          = a ⟨2 * k, by omega⟩ x * c ⟨0, by omega⟩ y + c ⟨0, by omega⟩ x * a ⟨2 * k, by omega⟩ y +
            ((b ⟨2 * k, by omega⟩ x * c ⟨0, by omega⟩ y + c ⟨0, by omega⟩ x * b ⟨2 * k, by omega⟩ y) +
             (b ⟨2 * k, by omega⟩ x * c ⟨0, by omega⟩ y + c ⟨0, by omega⟩ x * b ⟨2 * k, by omega⟩ y)) := by ring
        _ = _ := by rw [h2, add_zero]
    · simp only [Hextra, dif_neg h, Matrix.mul_zero, Matrix.zero_mul, add_zero]
  have hD_decomp : D = (∑ j : Fin k,
      (altOuter (a (i0 j)) (a (i1 j)) + altOuter (a (i0 j)) (b (i1 j)) + altOuter (b (i0 j)) (a (i1 j)))) +
      (if h : r % 2 = 1 ∧ 2 * r < d then altOuter (a ⟨2 * k, by omega⟩) (c ⟨0, by omega⟩) else 0) := by
    have hsum_conj : U * Hpair * Uᵀ + Hpair = ∑ j : Fin k,
        (altOuter (a (i0 j)) (a (i1 j)) + altOuter (a (i0 j)) (b (i1 j)) + altOuter (b (i0 j)) (a (i1 j))) := by
      simp only [Hpair, Matrix.mul_sum, Matrix.sum_mul, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => hD_pair j
    calc D = (U * Hpair * Uᵀ + Hpair) + (U * Hextra * Uᵀ + Hextra) := by
          simp only [D, H, Matrix.mul_add, Matrix.add_mul]; abel
      _ = _ := by rw [hsum_conj, hD_extra]
  have hD_mulVec : ∀ x : Fin d → ZMod 2,
      D *ᵥ x = (∑ j : Fin k,
        (((dotProduct (a (i1 j)) x + dotProduct (b (i1 j)) x) • a (i0 j) +
          (dotProduct (a (i0 j)) x + dotProduct (b (i0 j)) x) • a (i1 j)) +
         (dotProduct (a (i1 j)) x • b (i0 j) + dotProduct (a (i0 j)) x • b (i1 j)))) +
        (if h : r % 2 = 1 ∧ 2 * r < d then
          dotProduct (c ⟨0, by omega⟩) x • a ⟨2 * k, by omega⟩ +
          dotProduct (a ⟨2 * k, by omega⟩) x • c ⟨0, by omega⟩ else 0) := by
    intro x
    rw [hD_decomp, Matrix.add_mulVec]
    congr 1
    · change (∑ j : Fin k,
          (altOuter (a (i0 j)) (a (i1 j)) + altOuter (a (i0 j)) (b (i1 j)) +
            altOuter (b (i0 j)) (a (i1 j)))).mulVecLin x = _
      simp only [map_sum, LinearMap.coe_sum, Finset.sum_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      change (altOuter (a (i0 j)) (a (i1 j)) + altOuter (a (i0 j)) (b (i1 j)) +
        altOuter (b (i0 j)) (a (i1 j))) *ᵥ x = _
      simp only [Matrix.add_mulVec, altOuter_mulVec]
      funext t
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    · by_cases h : r % 2 = 1 ∧ 2 * r < d
      · simp only [dif_pos h, altOuter_mulVec]
      · simp only [dif_neg h, Matrix.zero_mulVec]
  let R_D : Submodule (ZMod 2) (Fin d → ZMod 2) := LinearMap.range D.mulVecLin
  have h_in_RD_pair : ∀ j : Fin k,
      a (i0 j) ∈ R_D ∧ a (i1 j) ∈ R_D ∧ b (i0 j) ∈ R_D ∧ b (i1 j) ∈ R_D := by
    intro j
    have ha_i1 : a (i1 j) ∈ R_D := by
      refine ⟨dual (Sum.inr (Sum.inl (i0 j))), ?_⟩
      change D *ᵥ dual (Sum.inr (Sum.inl (i0 j))) = a (i1 j)
      rw [hD_mulVec]
      have hex0 : (if h : r % 2 = 1 ∧ 2 * r < d then
          dotProduct (c ⟨0, by omega⟩) (dual (Sum.inr (Sum.inl (i0 j)))) • a ⟨2 * k, by omega⟩ +
          dotProduct (a ⟨2 * k, by omega⟩) (dual (Sum.inr (Sum.inl (i0 j)))) • c ⟨0, by omega⟩ else 0) = 0 := by
        split_ifs with h
        · have h1 := hdual (Sum.inr (Sum.inr ⟨0, by omega⟩)) (Sum.inr (Sum.inl (i0 j)))
          have h2 := hdual (Sum.inl ⟨2 * k, by omega⟩) (Sum.inr (Sum.inl (i0 j)))
          simp [I, v] at h1 h2
          rw [h1, h2, zero_smul, zero_smul, add_zero]
        · rfl
      rw [hex0, add_zero, Finset.sum_eq_single j]
      · have h1 := hdual (Sum.inl (i1 j)) (Sum.inr (Sum.inl (i0 j)))
        have h2 := hdual (Sum.inr (Sum.inl (i1 j))) (Sum.inr (Sum.inl (i0 j)))
        have h3 := hdual (Sum.inl (i0 j)) (Sum.inr (Sum.inl (i0 j)))
        have h4 := hdual (Sum.inr (Sum.inl (i0 j))) (Sum.inr (Sum.inl (i0 j)))
        have hne : i1 j ≠ i0 j := by intro heq; have := congrArg Fin.val heq; dsimp [i0, i1] at this; omega
        simp [I, v, hne] at h1 h2 h3 h4
        rw [h1, h2, h3, h4]
        simp
      · intro j' _ hne
        have h1 := hdual (Sum.inl (i1 j')) (Sum.inr (Sum.inl (i0 j)))
        have h2 := hdual (Sum.inr (Sum.inl (i1 j'))) (Sum.inr (Sum.inl (i0 j)))
        have h3 := hdual (Sum.inl (i0 j')) (Sum.inr (Sum.inl (i0 j)))
        have h4 := hdual (Sum.inr (Sum.inl (i0 j'))) (Sum.inr (Sum.inl (i0 j)))
        have hne1 : i1 j' ≠ i0 j := by intro heq; have := congrArg Fin.val heq; dsimp [i0, i1] at this; omega
        have hne2 : i0 j' ≠ i0 j := by intro heq; apply hne; exact Fin.ext (by have := congrArg Fin.val heq; dsimp [i0] at this; omega)
        simp [I, v, hne1, hne2] at h1 h2 h3 h4
        rw [h1, h2, h3, h4]
        simp
      · intro h; exact (h (Finset.mem_univ j)).elim
    have ha_i0 : a (i0 j) ∈ R_D := by
      refine ⟨dual (Sum.inr (Sum.inl (i1 j))), ?_⟩
      change D *ᵥ dual (Sum.inr (Sum.inl (i1 j))) = a (i0 j)
      rw [hD_mulVec]
      have hex0 : (if h : r % 2 = 1 ∧ 2 * r < d then
          dotProduct (c ⟨0, by omega⟩) (dual (Sum.inr (Sum.inl (i1 j)))) • a ⟨2 * k, by omega⟩ +
          dotProduct (a ⟨2 * k, by omega⟩) (dual (Sum.inr (Sum.inl (i1 j)))) • c ⟨0, by omega⟩ else 0) = 0 := by
        split_ifs with h
        · have h1 := hdual (Sum.inr (Sum.inr ⟨0, by omega⟩)) (Sum.inr (Sum.inl (i1 j)))
          have h2 := hdual (Sum.inl ⟨2 * k, by omega⟩) (Sum.inr (Sum.inl (i1 j)))
          simp [I, v] at h1 h2
          rw [h1, h2, zero_smul, zero_smul, add_zero]
        · rfl
      rw [hex0, add_zero, Finset.sum_eq_single j]
      · have h1 := hdual (Sum.inl (i1 j)) (Sum.inr (Sum.inl (i1 j)))
        have h2 := hdual (Sum.inr (Sum.inl (i1 j))) (Sum.inr (Sum.inl (i1 j)))
        have h3 := hdual (Sum.inl (i0 j)) (Sum.inr (Sum.inl (i1 j)))
        have h4 := hdual (Sum.inr (Sum.inl (i0 j))) (Sum.inr (Sum.inl (i1 j)))
        have hne : i0 j ≠ i1 j := by intro heq; have := congrArg Fin.val heq; dsimp [i0, i1] at this; omega
        simp [I, v, hne] at h1 h2 h3 h4
        rw [h1, h2, h3, h4]
        simp
      · intro j' _ hne
        have h1 := hdual (Sum.inl (i1 j')) (Sum.inr (Sum.inl (i1 j)))
        have h2 := hdual (Sum.inr (Sum.inl (i1 j'))) (Sum.inr (Sum.inl (i1 j)))
        have h3 := hdual (Sum.inl (i0 j')) (Sum.inr (Sum.inl (i1 j)))
        have h4 := hdual (Sum.inr (Sum.inl (i0 j'))) (Sum.inr (Sum.inl (i1 j)))
        have hne1 : i1 j' ≠ i1 j := by intro heq; apply hne; exact Fin.ext (by have := congrArg Fin.val heq; dsimp [i1] at this; omega)
        have hne2 : i0 j' ≠ i1 j := by intro heq; have := congrArg Fin.val heq; dsimp [i0, i1] at this; omega
        simp [I, v, hne1, hne2] at h1 h2 h3 h4
        rw [h1, h2, h3, h4]
        simp
      · intro h; exact (h (Finset.mem_univ j)).elim
    have hab_i1 : a (i1 j) + b (i1 j) ∈ R_D := by
      refine ⟨dual (Sum.inl (i0 j)), ?_⟩
      change D *ᵥ dual (Sum.inl (i0 j)) = a (i1 j) + b (i1 j)
      rw [hD_mulVec]
      have hex0 : (if h : r % 2 = 1 ∧ 2 * r < d then
          dotProduct (c ⟨0, by omega⟩) (dual (Sum.inl (i0 j))) • a ⟨2 * k, by omega⟩ +
          dotProduct (a ⟨2 * k, by omega⟩) (dual (Sum.inl (i0 j))) • c ⟨0, by omega⟩ else 0) = 0 := by
        split_ifs with h
        · have h1 := hdual (Sum.inr (Sum.inr ⟨0, by omega⟩)) (Sum.inl (i0 j))
          have h2 := hdual (Sum.inl ⟨2 * k, by omega⟩) (Sum.inl (i0 j))
          have hne : (⟨2 * k, by omega⟩ : Fin r) ≠ i0 j := by
            intro heq; have := congrArg Fin.val heq; dsimp [i0] at this; omega
          simp [I, v, hne] at h1 h2
          rw [h1, h2, zero_smul, zero_smul, add_zero]
        · rfl
      rw [hex0, add_zero, Finset.sum_eq_single j]
      · have h1 := hdual (Sum.inl (i1 j)) (Sum.inl (i0 j))
        have h2 := hdual (Sum.inr (Sum.inl (i1 j))) (Sum.inl (i0 j))
        have h3 := hdual (Sum.inl (i0 j)) (Sum.inl (i0 j))
        have h4 := hdual (Sum.inr (Sum.inl (i0 j))) (Sum.inl (i0 j))
        have hne : i1 j ≠ i0 j := by intro heq; have := congrArg Fin.val heq; dsimp [i0, i1] at this; omega
        simp [I, v, hne] at h1 h2 h3 h4
        rw [h1, h2, h3, h4]
        simp
      · intro j' _ hne
        have h1 := hdual (Sum.inl (i1 j')) (Sum.inl (i0 j))
        have h2 := hdual (Sum.inr (Sum.inl (i1 j'))) (Sum.inl (i0 j))
        have h3 := hdual (Sum.inl (i0 j')) (Sum.inl (i0 j))
        have h4 := hdual (Sum.inr (Sum.inl (i0 j'))) (Sum.inl (i0 j))
        have hne1 : i1 j' ≠ i0 j := by intro heq; have := congrArg Fin.val heq; dsimp [i0, i1] at this; omega
        have hne2 : i0 j' ≠ i0 j := by intro heq; apply hne; exact Fin.ext (by have := congrArg Fin.val heq; dsimp [i0] at this; omega)
        simp [I, v, hne1, hne2] at h1 h2 h3 h4
        rw [h1, h2, h3, h4]
        simp
      · intro h; exact (h (Finset.mem_univ j)).elim
    have hab_i0 : a (i0 j) + b (i0 j) ∈ R_D := by
      refine ⟨dual (Sum.inl (i1 j)), ?_⟩
      change D *ᵥ dual (Sum.inl (i1 j)) = a (i0 j) + b (i0 j)
      rw [hD_mulVec]
      have hex0 : (if h : r % 2 = 1 ∧ 2 * r < d then
          dotProduct (c ⟨0, by omega⟩) (dual (Sum.inl (i1 j))) • a ⟨2 * k, by omega⟩ +
          dotProduct (a ⟨2 * k, by omega⟩) (dual (Sum.inl (i1 j))) • c ⟨0, by omega⟩ else 0) = 0 := by
        split_ifs with h
        · have h1 := hdual (Sum.inr (Sum.inr ⟨0, by omega⟩)) (Sum.inl (i1 j))
          have h2 := hdual (Sum.inl ⟨2 * k, by omega⟩) (Sum.inl (i1 j))
          have hne : (⟨2 * k, by omega⟩ : Fin r) ≠ i1 j := by
            intro heq; have := congrArg Fin.val heq; dsimp [i1] at this; omega
          simp [I, v, hne] at h1 h2
          rw [h1, h2, zero_smul, zero_smul, add_zero]
        · rfl
      rw [hex0, add_zero, Finset.sum_eq_single j]
      · have h1 := hdual (Sum.inl (i1 j)) (Sum.inl (i1 j))
        have h2 := hdual (Sum.inr (Sum.inl (i1 j))) (Sum.inl (i1 j))
        have h3 := hdual (Sum.inl (i0 j)) (Sum.inl (i1 j))
        have h4 := hdual (Sum.inr (Sum.inl (i0 j))) (Sum.inl (i1 j))
        have hne : i0 j ≠ i1 j := by intro heq; have := congrArg Fin.val heq; dsimp [i0, i1] at this; omega
        simp [I, v, hne] at h1 h2 h3 h4
        rw [h1, h2, h3, h4]
        simp
      · intro j' _ hne
        have h1 := hdual (Sum.inl (i1 j')) (Sum.inl (i1 j))
        have h2 := hdual (Sum.inr (Sum.inl (i1 j'))) (Sum.inl (i1 j))
        have h3 := hdual (Sum.inl (i0 j')) (Sum.inl (i1 j))
        have h4 := hdual (Sum.inr (Sum.inl (i0 j'))) (Sum.inl (i1 j))
        have hne1 : i1 j' ≠ i1 j := by intro heq; apply hne; exact Fin.ext (by have := congrArg Fin.val heq; dsimp [i1] at this; omega)
        have hne2 : i0 j' ≠ i1 j := by intro heq; have := congrArg Fin.val heq; dsimp [i0, i1] at this; omega
        simp [I, v, hne1, hne2] at h1 h2 h3 h4
        rw [h1, h2, h3, h4]
        simp
      · intro h; exact (h (Finset.mem_univ j)).elim
    have hb_i1 : b (i1 j) ∈ R_D := by
      have h1 := Submodule.add_mem R_D ha_i1 hab_i1
      have heq : a (i1 j) + (a (i1 j) + b (i1 j)) = b (i1 j) := by
        funext t; simp only [Pi.add_apply]; rw [← add_assoc, zmod2_add_self, zero_add]
      rwa [heq] at h1
    have hb_i0 : b (i0 j) ∈ R_D := by
      have h1 := Submodule.add_mem R_D ha_i0 hab_i0
      have heq : a (i0 j) + (a (i0 j) + b (i0 j)) = b (i0 j) := by
        funext t; simp only [Pi.add_apply]; rw [← add_assoc, zmod2_add_self, zero_add]
      rwa [heq] at h1
    exact ⟨ha_i0, ha_i1, hb_i0, hb_i1⟩
  have h_in_RD_extra : ∀ h : r % 2 = 1 ∧ 2 * r < d,
      a ⟨2 * k, by omega⟩ ∈ R_D ∧ c ⟨0, by omega⟩ ∈ R_D := by
    intro h
    constructor
    · refine ⟨dual (Sum.inr (Sum.inr ⟨0, by omega⟩)), ?_⟩
      change D *ᵥ dual (Sum.inr (Sum.inr ⟨0, by omega⟩)) = a ⟨2 * k, by omega⟩
      rw [hD_mulVec]
      have hsum0 : ∑ j : Fin k,
          (((dotProduct (a (i1 j)) (dual (Sum.inr (Sum.inr ⟨0, by omega⟩))) +
             dotProduct (b (i1 j)) (dual (Sum.inr (Sum.inr ⟨0, by omega⟩)))) • a (i0 j) +
            (dotProduct (a (i0 j)) (dual (Sum.inr (Sum.inr ⟨0, by omega⟩))) +
             dotProduct (b (i0 j)) (dual (Sum.inr (Sum.inr ⟨0, by omega⟩)))) • a (i1 j)) +
           (dotProduct (a (i1 j)) (dual (Sum.inr (Sum.inr ⟨0, by omega⟩))) • b (i0 j) +
            dotProduct (a (i0 j)) (dual (Sum.inr (Sum.inr ⟨0, by omega⟩))) • b (i1 j))) = 0 := by
        apply Finset.sum_eq_zero
        intro j _
        have h1 := hdual (Sum.inl (i1 j)) (Sum.inr (Sum.inr ⟨0, by omega⟩))
        have h2 := hdual (Sum.inr (Sum.inl (i1 j))) (Sum.inr (Sum.inr ⟨0, by omega⟩))
        have h3 := hdual (Sum.inl (i0 j)) (Sum.inr (Sum.inr ⟨0, by omega⟩))
        have h4 := hdual (Sum.inr (Sum.inl (i0 j))) (Sum.inr (Sum.inr ⟨0, by omega⟩))
        simp [I, v] at h1 h2 h3 h4
        rw [h1, h2, h3, h4]; simp
      rw [hsum0, zero_add, dif_pos h]
      have hc1 := hdual (Sum.inr (Sum.inr ⟨0, by omega⟩)) (Sum.inr (Sum.inr ⟨0, by omega⟩))
      have ha0 := hdual (Sum.inl ⟨2 * k, by omega⟩) (Sum.inr (Sum.inr ⟨0, by omega⟩))
      simp [I, v] at hc1 ha0
      rw [hc1, ha0]; simp
    · refine ⟨dual (Sum.inl ⟨2 * k, by omega⟩), ?_⟩
      change D *ᵥ dual (Sum.inl ⟨2 * k, by omega⟩) = c ⟨0, by omega⟩
      rw [hD_mulVec]
      have hsum0 : ∑ j : Fin k,
          (((dotProduct (a (i1 j)) (dual (Sum.inl ⟨2 * k, by omega⟩)) +
             dotProduct (b (i1 j)) (dual (Sum.inl ⟨2 * k, by omega⟩))) • a (i0 j) +
            (dotProduct (a (i0 j)) (dual (Sum.inl ⟨2 * k, by omega⟩)) +
             dotProduct (b (i0 j)) (dual (Sum.inl ⟨2 * k, by omega⟩))) • a (i1 j)) +
           (dotProduct (a (i1 j)) (dual (Sum.inl ⟨2 * k, by omega⟩)) • b (i0 j) +
            dotProduct (a (i0 j)) (dual (Sum.inl ⟨2 * k, by omega⟩)) • b (i1 j))) = 0 := by
        apply Finset.sum_eq_zero
        intro j _
        have h1 := hdual (Sum.inl (i1 j)) (Sum.inl ⟨2 * k, by omega⟩)
        have h2 := hdual (Sum.inr (Sum.inl (i1 j))) (Sum.inl ⟨2 * k, by omega⟩)
        have h3 := hdual (Sum.inl (i0 j)) (Sum.inl ⟨2 * k, by omega⟩)
        have h4 := hdual (Sum.inr (Sum.inl (i0 j))) (Sum.inl ⟨2 * k, by omega⟩)
        have hne1 : i1 j ≠ ⟨2 * k, by omega⟩ := by intro heq; have := congrArg Fin.val heq; dsimp [i1] at this; omega
        have hne2 : i0 j ≠ ⟨2 * k, by omega⟩ := by intro heq; have := congrArg Fin.val heq; dsimp [i0] at this; omega
        simp [I, v, hne1, hne2] at h1 h2 h3 h4
        rw [h1, h2, h3, h4]; simp
      rw [hsum0, zero_add, dif_pos h]
      have hc0 := hdual (Sum.inr (Sum.inr ⟨0, by omega⟩)) (Sum.inl ⟨2 * k, by omega⟩)
      have ha1 := hdual (Sum.inl ⟨2 * k, by omega⟩) (Sum.inl ⟨2 * k, by omega⟩)
      simp [I, v] at hc0 ha1
      rw [hc0, ha1]; simp
  let S_pair : Finset I := Finset.univ.filter (fun p : I =>
    match p with
    | Sum.inl i => i.val < 2 * k
    | Sum.inr (Sum.inl i) => i.val < 2 * k
    | Sum.inr (Sum.inr _) => False)
  let S_extra : Finset I :=
    if h : r % 2 = 1 ∧ 2 * r < d then {Sum.inl ⟨2 * k, by omega⟩, Sum.inr (Sum.inr ⟨0, by omega⟩)} else ∅
  let S_I : Finset I := S_pair ∪ S_extra
  have hS_disj : Disjoint S_pair S_extra := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    by_cases h : r % 2 = 1 ∧ 2 * r < d
    · simp only [S_extra, dif_pos h, Finset.mem_insert, Finset.mem_singleton] at hp2
      simp only [S_pair, Finset.mem_filter, Finset.mem_univ, true_and] at hp1
      rcases hp2 with rfl | rfl
      · dsimp only at hp1; omega
      · exact hp1
    · simp only [S_extra, dif_neg h, Finset.notMem_empty] at hp2
  have hSpair_card : S_pair.card = 4 * k := by
    let Sa : Finset I := (Finset.univ.filter (fun i : Fin r => i.val < 2 * k)).map
      ⟨Sum.inl, Sum.inl_injective⟩
    let Sb : Finset I := (Finset.univ.filter (fun i : Fin r => i.val < 2 * k)).map
      ⟨fun i => Sum.inr (Sum.inl i), fun _ _ h => Sum.inl.inj (Sum.inr.inj h)⟩
    have hEq : S_pair = Sa ∪ Sb := by
      ext p
      simp only [S_pair, Sa, Sb, Finset.mem_union, Finset.mem_map, Finset.mem_filter,
        Finset.mem_univ, true_and]
      rcases p with i | (i | l)
      · constructor
        · intro h; exact Or.inl ⟨i, h, rfl⟩
        · rintro (⟨a, ha, h⟩ | ⟨_, _, h⟩)
          · exact (Sum.inl.inj h) ▸ ha
          · cases h
      · constructor
        · intro h; exact Or.inr ⟨i, h, rfl⟩
        · rintro (⟨_, _, h⟩ | ⟨a, ha, h⟩)
          · cases h
          · exact (Sum.inl.inj (Sum.inr.inj h)) ▸ ha
      · constructor
        · exact False.elim
        · rintro (⟨_, _, h⟩ | ⟨_, _, h⟩)
          · cases h
          · cases Sum.inr.inj h
    have hDisj : Disjoint Sa Sb := by
      rw [Finset.disjoint_left]
      intro p h1 h2
      simp only [Sa, Sb, Finset.mem_map, Function.Embedding.coeFn_mk] at h1 h2
      rcases h1 with ⟨_, _, rfl⟩
      rcases h2 with ⟨_, _, h2⟩
      cases h2
    have hflt : (Finset.univ.filter (fun i : Fin r => i.val < 2 * k)).card = 2 * k := by
      have hbij : (Finset.univ.filter (fun i : Fin r => i.val < 2 * k)).card =
          (Finset.univ : Finset (Fin (2 * k))).card := by
        refine Finset.card_bij (fun i hi => ⟨i.val, (Finset.mem_filter.mp hi).2⟩)
          (fun _ _ => Finset.mem_univ _)
          (fun _ _ _ _ h => Fin.ext (Fin.mk.inj h))
          (fun t _ => ⟨⟨t.val, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, t.isLt⟩, Fin.ext rfl⟩)
      rw [hbij, Finset.card_fin]
    rw [hEq, Finset.card_union_of_disjoint hDisj, Finset.card_map, Finset.card_map, hflt]
    omega
  have hSI_card : S_I.card = 2 * w := by
    rw [Finset.card_union_of_disjoint hS_disj, hSpair_card]
    by_cases h : r % 2 = 1 ∧ 2 * r < d
    · have hcardE : S_extra.card = 2 := by
        simp only [S_extra, dif_pos h]
        rw [Finset.card_pair]
        intro heq; cases heq
      have hnot : ¬ (d = 2 * r ∧ r % 2 = 1) := by omega
      have hw_eq : w = r := if_neg hnot
      rw [hcardE, hw_eq]; omega
    · have hcardE : S_extra.card = 0 := by simp [S_extra, h]
      rw [hcardE, add_zero]
      by_cases hexc : d = 2 * r ∧ r % 2 = 1
      · have hw_eq : w = r - 1 := if_pos hexc
        rw [hw_eq]; omega
      · have hw_eq : w = r := if_neg hexc
        rw [hw_eq]; omega
  have hSI_mem : ∀ p ∈ S_I, v p ∈ R_D := by
    intro p hp
    rcases Finset.mem_union.mp hp with hp1 | hp2
    · simp only [S_pair, Finset.mem_filter, Finset.mem_univ, true_and] at hp1
      rcases p with i | (i | l)
      · let j : Fin k := ⟨i.val / 2, by omega⟩
        by_cases hev : i.val % 2 = 0
        · have hi : i = i0 j := Fin.ext (by dsimp [i0, j]; omega)
          rw [hi]; exact (h_in_RD_pair j).1
        · have hi : i = i1 j := Fin.ext (by dsimp [i1, j]; omega)
          rw [hi]; exact (h_in_RD_pair j).2.1
      · let j : Fin k := ⟨i.val / 2, by omega⟩
        by_cases hev : i.val % 2 = 0
        · have hi : i = i0 j := Fin.ext (by dsimp [i0, j]; omega)
          rw [hi]; exact (h_in_RD_pair j).2.2.1
        · have hi : i = i1 j := Fin.ext (by dsimp [i1, j]; omega)
          rw [hi]; exact (h_in_RD_pair j).2.2.2
      · exact False.elim hp1
    · by_cases h : r % 2 = 1 ∧ 2 * r < d
      · simp only [S_extra, dif_pos h, Finset.mem_insert, Finset.mem_singleton] at hp2
        rcases hp2 with rfl | rfl
        · exact (h_in_RD_extra h).1
        · exact (h_in_RD_extra h).2
      · simp only [S_extra, dif_neg h, Finset.notMem_empty] at hp2
  let Φ : (S_I → ZMod 2) →ₗ[ZMod 2] R_D :=
    { toFun := fun f => ⟨∑ p : S_I, f p • v p.1, Submodule.sum_mem R_D fun p _ =>
        Submodule.smul_mem R_D _ (hSI_mem p.1 p.2)⟩
      map_add' := fun f1 f2 => by
        apply Subtype.ext; funext t
        simp [add_mul, Finset.sum_add_distrib]
      map_smul' := fun c0 f => by
        apply Subtype.ext; funext t
        simp [Finset.mul_sum, mul_assoc] }
  have hΦ_inj : Function.Injective Φ := by
    intro f1 f2 heq
    have hval : ∑ p : S_I, (f1 p - f2 p) • v p.1 = 0 := by
      have h1 : (Φ f1).1 = (Φ f2).1 := congrArg Subtype.val heq
      have h2 : ∑ p : S_I, f1 p • v p.1 - ∑ p : S_I, f2 p • v p.1 = 0 := sub_eq_zero.mpr h1
      rw [← Finset.sum_sub_distrib] at h2
      simpa [sub_smul] using h2
    let g : I → ZMod 2 := fun p => if hp : p ∈ S_I then f1 ⟨p, hp⟩ - f2 ⟨p, hp⟩ else 0
    have hsum_g : ∑ p : I, g p • v p = 0 := by
      rw [← hval]
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun p : I => p ∈ S_I)]
      have h0 : ∑ p ∈ Finset.univ.filter (fun p : I => p ∉ S_I), g p • v p = 0 :=
        Finset.sum_eq_zero fun p hp => by
          have hnm := (Finset.mem_filter.mp hp).2
          simp [g, hnm]
      rw [h0, add_zero]
      refine Finset.sum_bij (fun p hp => ⟨p, (Finset.mem_filter.mp hp).2⟩)
        (fun _ _ => Finset.mem_univ _)
        (fun _ _ _ _ h => congrArg Subtype.val h)
        (fun p _ => ⟨p.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, p.2⟩, Subtype.ext rfl⟩)
        (fun p hp => by simp [g, (Finset.mem_filter.mp hp).2])
    have hg0 := (Fintype.linearIndependent_iff.mp hlin') g hsum_g
    funext p
    have hp0 := hg0 p.1
    simp only [g, dif_pos p.2] at hp0
    exact sub_eq_zero.mp hp0
  have hrank_le := LinearMap.finrank_le_finrank_of_injective hΦ_inj
  rw [Module.finrank_pi_fintype] at hrank_le
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, hSI_card, Module.finrank_self,
    smul_eq_mul, mul_one] at hrank_le
  exact hrank_le

private def shiftWire (W shift i : ℕ) : ℕ := if i < W then i else i + shift

private def shiftGate (W shift : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (shiftWire W shift)⟩

private lemma nonlin_shiftGate (W shift : ℕ) (g : Gate) :
    nonlin (shiftGate W shift g) = nonlin g := by
  simp [nonlin, shiftGate]

private lemma shift_append_props (W : ℕ) (gs1 gs2 : List Gate)
    (h1 : goodGates W gs1) (h2 : goodGates W gs2) :
    let s1 := gs1.length
    let gs12 := gs1 ++ gs2.map (shiftGate W s1)
    goodGates W gs12 ∧
    gs12.countP nonlin = gs1.countP nonlin + gs2.countP nonlin ∧
    (∀ k < W + gs2.length,
      (depthsOf W gs12).getD (shiftWire W s1 k) 0 = (depthsOf W gs2).getD k 0) ∧
    (∀ (x : List Bool), x.length = W → ∀ k < W + gs2.length,
      (wiresOf gs12 x).getD (shiftWire W s1 k) false = (wiresOf gs2 x).getD k false) := by
  induction gs2 using List.reverseRecOn with
  | nil =>
    refine ⟨by simpa using h1, by simp, ?_, ?_⟩
    · intro k hk
      simp only [List.length_nil, add_zero] at hk
      simp only [List.map_nil, List.append_nil, shiftWire, if_pos hk]
      have h := depthsOf_append_prefix W [] gs1 k (by simp; omega)
      simpa [depthsOf] using h
    · intro x hx k hk
      simp only [List.length_nil, add_zero] at hk
      simp only [List.map_nil, List.append_nil, shiftWire, if_pos hk]
      have h := wiresOf_append_prefix [] gs1 x k (by simp [hx]; omega)
      simpa [wiresOf] using h
  | append_singleton gs2 g ih =>
    have h2_pref : goodGates W gs2 := by
      refine ⟨fun j hj i hi => ?_, fun g' hg' => h2.2 g' (List.mem_append_left _ hg')⟩
      have h := h2.1 j (by simp; omega) i
      rw [getD_append_left _ _ _ _ hj] at h
      exact h hi
    have hg_fan : g.inputs.length ≤ 2 := h2.2 g (List.mem_append_right _ List.mem_cons_self)
    have hg_back : ∀ i ∈ g.inputs, i < W + gs2.length := by
      intro i hi
      have h := h2.1 gs2.length (by simp) i
      rw [getD_append_last] at h
      exact h hi
    rcases ih h2_pref with ⟨hgood_prev, hcnt_prev, hdep_prev, hval_prev⟩
    set s1 := gs1.length
    set gs_prev := gs1 ++ gs2.map (shiftGate W s1)
    set g' := shiftGate W s1 g
    have hgs12_eq : gs1 ++ (gs2 ++ [g]).map (shiftGate W s1) = gs_prev ++ [g'] := by
      simp [gs_prev, g', List.append_assoc]
    have hlen_prev : gs_prev.length = s1 + gs2.length := by simp [gs_prev, s1]
    have hg'_back : ∀ i' ∈ g'.inputs, i' < W + gs_prev.length := by
      intro i' hi'
      simp only [g', shiftGate, List.mem_map] at hi'
      rcases hi' with ⟨i, hi, rfl⟩
      have hilt := hg_back i hi
      simp only [shiftWire]
      split_ifs <;> omega
    have hgood_new : goodGates W (gs_prev ++ [g']) :=
      append_gate_good W gs_prev g' hgood_prev (by simp [g', shiftGate]; exact hg_fan) hg'_back
    have hcnt_new : (gs_prev ++ [g']).countP nonlin = gs1.countP nonlin + (gs2 ++ [g]).countP nonlin := by
      have h1 : (gs_prev ++ [g']).countP nonlin = gs_prev.countP nonlin + (nonlin g').toNat := by
        rw [List.countP_append, List.countP_cons, List.countP_nil]; cases nonlin g' <;> simp
      have h2 : (gs2 ++ [g]).countP nonlin = gs2.countP nonlin + (nonlin g).toNat := by
        rw [List.countP_append, List.countP_cons, List.countP_nil]; cases nonlin g <;> simp
      rw [h1, h2, hcnt_prev, nonlin_shiftGate]
      omega
    refine ⟨by rw [hgs12_eq]; exact hgood_new, by rw [hgs12_eq]; exact hcnt_new, ?_, ?_⟩
    · intro k hk
      rw [hgs12_eq]
      simp only [List.length_append, List.length_singleton] at hk
      by_cases hlt : k < W + gs2.length
      · have hsw_lt : shiftWire W s1 k < W + gs_prev.length := by
          simp only [shiftWire]; split_ifs <;> omega
        rw [depthsOf_append_prefix W gs_prev [g'] _ hsw_lt,
          depthsOf_append_prefix W gs2 [g] k hlt]
        exact hdep_prev k hlt
      · have hk_eq : k = W + gs2.length := by omega
        subst hk_eq
        have hsw_eq : shiftWire W s1 (W + gs2.length) = W + gs_prev.length := by
          simp only [shiftWire, if_neg (show ¬ W + gs2.length < W by omega)]
          omega
        rw [hsw_eq]
        have hstep1 : depthsOf W (gs_prev ++ [g']) = depthsOf W gs_prev ++
            [(g'.inputs.map (fun a => (depthsOf W gs_prev).getD a 0)).foldr max 0 + (nonlin g').toNat] := by
          simp [depthsOf, List.foldl_append]
        have hstep2 : depthsOf W (gs2 ++ [g]) = depthsOf W gs2 ++
            [(g.inputs.map (fun a => (depthsOf W gs2).getD a 0)).foldr max 0 + (nonlin g).toNat] := by
          simp [depthsOf, List.foldl_append]
        have hl1 : (depthsOf W gs_prev).length = W + gs_prev.length := depthsOf_length W gs_prev
        have hl2 : (depthsOf W gs2).length = W + gs2.length := depthsOf_length W gs2
        rw [hstep1, ← hl1, getD_append_last, hstep2, ← hl2, getD_append_last, nonlin_shiftGate]
        congr 2
        simp only [g', shiftGate, List.map_map]
        refine List.map_congr_left fun i hi => ?_
        exact hdep_prev i (hg_back i hi)
    · intro x hx k hk
      rw [hgs12_eq]
      simp only [List.length_append, List.length_singleton] at hk
      by_cases hlt : k < W + gs2.length
      · have hsw_lt : shiftWire W s1 k < x.length + gs_prev.length := by
          rw [hx]; simp only [shiftWire]; split_ifs <;> omega
        rw [wiresOf_append_prefix gs_prev [g'] x _ hsw_lt,
          wiresOf_append_prefix gs2 [g] x k (by rw [hx]; exact hlt)]
        exact hval_prev x hx k hlt
      · have hk_eq : k = W + gs2.length := by omega
        subst hk_eq
        have hsw_eq : shiftWire W s1 (W + gs2.length) = W + gs_prev.length := by
          simp only [shiftWire, if_neg (show ¬ W + gs2.length < W by omega)]
          omega
        rw [hsw_eq]
        have hstep1 : wiresOf (gs_prev ++ [g']) x = wiresOf gs_prev x ++
            [g'.op.eval (g'.inputs.map fun i => (wiresOf gs_prev x).getD i false)] := by
          simp [wiresOf, List.foldl_append]
        have hstep2 : wiresOf (gs2 ++ [g]) x = wiresOf gs2 x ++
            [g.op.eval (g.inputs.map fun i => (wiresOf gs2 x).getD i false)] := by
          simp [wiresOf, List.foldl_append]
        have hl1 : (wiresOf gs_prev x).length = W + gs_prev.length := by rw [wiresOf_length, hx]
        have hl2 : (wiresOf gs2 x).length = W + gs2.length := by rw [wiresOf_length, hx]
        rw [hstep1, ← hl1, getD_append_last, hstep2, ← hl2, getD_append_last]
        simp only [g', shiftGate, List.map_map]
        congr 1
        refine List.map_congr_left fun i hi => ?_
        exact hval_prev x hx i (hg_back i hi)

private lemma normalize_circuit (W : ℕ) (C : Circuit)
    (hrb : ReadsBack W C) (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2) :
    ∃ (gs : List Gate) (out : ℕ),
      goodGates W gs ∧
      gs.countP nonlin = C.gates.countP nonlin ∧
      out < W + gs.length ∧
      (depthsOf W gs).getD out 0 = (depthsOf W C.gates).getD C.output 0 ∧
      (∀ (x : List Bool), x.length = W →
        (wiresOf gs x).getD out false = (wiresOf C.gates x).getD C.output false) := by
  have hgood : goodGates W C.gates := ⟨hrb, hfan⟩
  by_cases hlt : C.output < W + C.gates.length
  · exact ⟨C.gates, C.output, hgood, rfl, hlt, rfl, fun _ _ => rfl⟩
  · have h := append_constFalse W C.gates hgood
    refine ⟨_, _, h.2.1, h.2.2.1, h.2.2.2.1, ?_, ?_⟩
    · rw [h.2.2.2.2.1]
      symm
      exact getD_of_ge_length _ _ _ (by rw [depthsOf_length]; omega)
    · intro x hx
      rw [(h.2.2.2.2.2.2 x hx).2]
      symm
      exact getD_of_ge_length _ _ _ (by rw [wiresOf_length, hx]; omega)

private lemma combine_xor_circuits {d : ℕ} (H1 H2 : Matrix (Fin d) (Fin d) (ZMod 2))
    (b1 b2 t1 t2 : ℕ) (C1 C2 : Circuit)
    (hrb1 : ReadsBack ((d + 1) + (d + 1)) C1) (hfan1 : ∀ g ∈ C1.gates, g.inputs.length ≤ 2)
    (hcnt1 : C1.gates.countP nonlin ≤ t1)
    (hdep1 : (depthsOf ((d + 1) + (d + 1)) C1.gates).getD C1.output 0 ≤ b1)
    (hrep1 : Represents (mkTable H1) C1)
    (hrb2 : ReadsBack ((d + 1) + (d + 1)) C2) (hfan2 : ∀ g ∈ C2.gates, g.inputs.length ≤ 2)
    (hcnt2 : C2.gates.countP nonlin ≤ t2)
    (hdep2 : (depthsOf ((d + 1) + (d + 1)) C2.gates).getD C2.output 0 ≤ b2)
    (hrep2 : Represents (mkTable H2) C2) :
    ∃ C : Circuit,
      ReadsBack ((d + 1) + (d + 1)) C ∧
      (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧
      C.gates.countP nonlin ≤ t1 + t2 ∧
      (depthsOf ((d + 1) + (d + 1)) C.gates).getD C.output 0 ≤ max b1 b2 ∧
      Represents (mkTable (H1 + H2)) C := by
  let W := (d + 1) + (d + 1)
  rcases normalize_circuit W C1 hrb1 hfan1 with ⟨gs1, out1, hgood1, hcnt1', hout1, hdep1', hval1'⟩
  rcases normalize_circuit W C2 hrb2 hfan2 with ⟨gs2, out2, hgood2, hcnt2', hout2, hdep2', hval2'⟩
  have hsh := shift_append_props W gs1 gs2 hgood1 hgood2
  let gs12 := gs1 ++ gs2.map (shiftGate W gs1.length)
  let out2' := shiftWire W gs1.length out2
  have hout1_12 : out1 < W + gs12.length := by simp [gs12]; omega
  have hout2_12 : out2' < W + gs12.length := by
    simp only [out2', shiftWire, gs12, List.length_append, List.length_map]
    split_ifs <;> omega
  have hxor := append_xor2 W gs12 out1 out2' hsh.1 hout1_12 hout2_12
  refine ⟨⟨_, W + gs12.length + 1⟩, hxor.2.1.1, hxor.2.1.2, ?_, ?_, ?_⟩
  · rw [hxor.2.2.1, hsh.2.1, hcnt1', hcnt2']; omega
  · rw [hxor.2.2.2.2.1, depthsOf_append_prefix W gs1 _ out1 hout1,
      hsh.2.2.1 out2 hout2, hdep1', hdep2']
    exact max_le_max hdep1 hdep2
  · intro x y
    apply b2z_inj
    change b2z ((wiresOf _ (oneEach x y)).getD _ false) = b2z (mkTable (H1 + H2) x y)
    have hlen_in : (oneEach x y).length = W := oneEach_length x y
    rw [(hxor.2.2.2.2.2.2 (oneEach x y) hlen_in).2, b2z_xor,
      wiresOf_append_prefix gs1 _ (oneEach x y) out1 (by rw [hlen_in]; exact hout1),
      hsh.2.2.2 (oneEach x y) hlen_in out2 hout2,
      hval1' (oneEach x y) hlen_in, hval2' (oneEach x y) hlen_in]
    have hv1 : (wiresOf C1.gates (oneEach x y)).getD C1.output false = mkTable H1 x y := hrep1 x y
    have hv2 : (wiresOf C2.gates (oneEach x y)).getD C2.output false = mkTable H2 x y := hrep2 x y
    rw [hv1, hv2]
    cases x using Fin.cases with
    | zero => simp [mkTable, b2z]
    | succ i =>
      cases y using Fin.cases with
      | zero => simp [mkTable, b2z]
      | succ j =>
        rw [b2z_mkTable_succ, b2z_mkTable_succ, b2z_mkTable_succ]
        rfl

end PEqualNP.Outside.L_meta_32060

open PEqualNP.Outside.L_meta_32060 in
theorem PEqualNP.Outside.L_meta_32060 :
    let nonlinear := fun (g : PEqualNP.CircuitLowerBounds.Gate) =>
      (g.inputs.length == 2) &&
      xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
          (xor (g.op.eval [true, false]) (g.op.eval [true, true]))
    let depths := fun (width : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) =>
      C.gates.foldl (fun (ds : List ℕ) g =>
        ds ++ [(g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nonlinear g).toNat])
        (List.replicate width 0)
    let F := ZMod 2
    ∀ (d : ℕ) (U : Matrix (Fin d) (Fin d) F), U*U = 1 →
      let Mat := Matrix (Fin d) (Fin d) F
      let alt := fun (H : Mat) => H.transpose = H ∧ ∀ i, H i i = 0
      let r := (U-1).rank
      let table := fun (H : Mat) (x y : Fin (d+1)) =>
        Fin.cases false (fun i => Fin.cases false (fun j => decide (H i j ≠ 0)) y) x
      let w := if d = 2*r ∧ r % 2 = 1 then r-1 else r
      let fit := fun (H : Mat) (b t : ℕ) =>
        ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
          PEqualNP.MetaComplexity.NestedCover.ReadsBack ((d+1)+(d+1)) C ∧
          (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧ C.gates.countP nonlinear ≤ t ∧
          (depths ((d+1)+(d+1)) C).getD C.output 0 ≤ b ∧
          PEqualNP.Represents.Represents (table H) C
      (∀ t : ℕ, (∀ H : Mat, alt H → fit (U*H*U.transpose + H) 1 t) ↔ w ≤ t) ∧
        (∀ (H : Mat) (b t : ℕ), alt H → 1 ≤ b → fit H b t → fit (U*H*U.transpose) b (t+w)) := by
  intro nonlinear depths F d U hU Mat alt r table w fit
  have htable_eq : table = mkTable := rfl
  have hnonlin_eq : nonlinear = nonlin := rfl
  constructor
  · intro t
    constructor
    · intro hall
      rcases exists_alt_involution_rank_ge U hU with ⟨H0, hH0_alt, hH0_rk⟩
      rcases hall H0 hH0_alt with ⟨C, _, hfan, hcnt, hdep, hrep⟩
      have hle := rank_le_two_mul_of_fit_depth1 (U * H0 * U.transpose + H0) t C hfan hcnt hdep hrep
      have hw_rk : 2 * w ≤ (U * H0 * U.transpose + H0).rank := hH0_rk
      omega
    · intro hwt H hH
      have hD_alt : isAlt (U * H * U.transpose + H) := isAlt_add (isAlt_conj U H hH) hH
      have hD_rk : (U * H * U.transpose + H).rank ≤ 2 * w := rank_involution_diff_le U H hU hH
      exact fit_depth1_of_alt (U * H * U.transpose + H) hD_alt t (by omega)
  · intro H b t hH hb ⟨C1, hrb1, hfan1, hcnt1, hdep1, hrep1⟩
    have hD_alt : isAlt (U * H * U.transpose + H) := isAlt_add (isAlt_conj U H hH) hH
    have hD_rk : (U * H * U.transpose + H).rank ≤ 2 * w := rank_involution_diff_le U H hU hH
    rcases fit_depth1_of_alt (U * H * U.transpose + H) hD_alt w (by omega) with
      ⟨C2, hrb2, hfan2, hcnt2, hdep2, hrep2⟩
    rcases combine_xor_circuits H (U * H * U.transpose + H) b 1 t w C1 C2
        hrb1 hfan1 hcnt1 hdep1 hrep1 hrb2 hfan2 hcnt2 hdep2 hrep2 with
      ⟨C, hrb, hfan, hcnt, hdep, hrep⟩
    have hsum_eq : H + (U * H * U.transpose + H) = U * H * U.transpose := by
      ext i j
      change H i j + ((U * H * U.transpose) i j + H i j) = (U * H * U.transpose) i j
      have h2 := zmod2_add_self (H i j)
      calc H i j + ((U * H * U.transpose) i j + H i j) = (U * H * U.transpose) i j + (H i j + H i j) := by ring
        _ = (U * H * U.transpose) i j := by rw [h2, add_zero]
    rw [hsum_eq] at hrep
    have hdep_eq : depths ((d + 1) + (d + 1)) C = depthsOf ((d + 1) + (d + 1)) C.gates := rfl
    exact ⟨C, hrb, hfan, hcnt, by rw [hdep_eq]; omega, hrep⟩
