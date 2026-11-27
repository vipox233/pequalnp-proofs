import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25487

open PEqualNP.CircuitLowerBounds

-- helpers stp, getD_snoc, getD_ge, pre, vgate, run, oe_len, allP, anyP, p1and, p1or copied from our parked Pre_L_meta_25458

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem getD_snoc (l : List Bool) (b : Bool) (w : ℕ) :
    (l ++ [b]).getD w false = if w < l.length then l.getD w false else if w = l.length then b else false := by
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2; simp
  · rw [List.getElem?_eq_none (by simp; omega)]; simp

theorem getD_ge (l : List Bool) (i : ℕ) (h : l.length ≤ i) : l.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem stp_len (W : List Bool) (g : Gate) : (stp W g).length = W.length + 1 := by
  simp [stp]

theorem stp_getD (W : List Bool) (g : Gate) (j : ℕ) : (stp W g).getD j false =
    if j < W.length then W.getD j false else if j = W.length then
      g.op.eval (g.inputs.map fun i => W.getD i false) else false := getD_snoc _ _ _

theorem flen : ∀ (gs : List Gate) (W : List Bool), (gs.foldl stp W).length = W.length + gs.length := by
  intro gs
  induction gs with
  | nil => intro W; simp
  | cons g t ih => intro W; rw [List.foldl_cons, ih, stp_len]; simp; omega

theorem pre : ∀ (gs : List Gate) (W : List Bool) (j : ℕ), j < W.length →
    (gs.foldl stp W).getD j false = W.getD j false := by
  intro gs
  induction gs with
  | nil => intro W j _; rfl
  | cons g t ih =>
    intro W j hj
    rw [List.foldl_cons, ih _ _ (by rw [stp_len]; omega), stp_getD, if_pos hj]

theorem vgate : ∀ (gs : List Gate) (W : List Bool) (r : ℕ) (h : r < gs.length),
    (gs.foldl stp W).getD (W.length + r) false = gs[r].op.eval (gs[r].inputs.map fun a =>
      if a < W.length + r then (gs.foldl stp W).getD a false else false) := by
  intro gs
  induction gs with
  | nil => intro W r h; simp at h
  | cons g t ih =>
    intro W r h
    cases r with
    | zero =>
      simp only [List.foldl_cons, List.getElem_cons_zero, Nat.add_zero]
      rw [pre t (stp W g) W.length (by rw [stp_len]; omega), stp_getD, if_neg (lt_irrefl _), if_pos rfl]
      congr 1
      apply List.map_congr_left
      intro a _
      split_ifs with ha
      · rw [pre t _ a (by rw [stp_len]; omega), stp_getD, if_pos ha]
      · exact getD_ge W a (by omega)
    | succ r =>
      simp only [List.foldl_cons, List.getElem_cons_succ]
      have := ih (stp W g) r (by simp at h; omega)
      rw [stp_len] at this
      rw [show W.length + (r + 1) = W.length + 1 + r by omega]
      exact this

theorem run (R : ℕ → Bool → Prop) : ∀ (gs : List Gate) (W : List Bool),
    (∀ j < W.length, R j (W.getD j false)) →
    (∀ r (h : r < gs.length) (w : List Bool), w.length = W.length + r →
      (∀ j < W.length + r, R j (w.getD j false)) →
      R (W.length + r) (gs[r].op.eval (gs[r].inputs.map fun a => w.getD a false))) →
    ∀ j < W.length + gs.length, R j ((gs.foldl stp W).getD j false) := by
  intro gs
  induction gs with
  | nil => intro W hW _ j hj; exact hW j (by simpa using hj)
  | cons g t ih =>
    intro W hW H j hj
    rw [List.foldl_cons]
    apply ih (stp W g)
    · intro j' hj'
      rw [stp_len] at hj'
      rw [stp_getD]
      by_cases h1 : j' < W.length
      · rw [if_pos h1]; exact hW j' h1
      · have e : j' = W.length := by omega
        rw [if_neg h1, if_pos e]
        subst e
        have := H 0 (by simp) W (by simp) (by intro j2 hj2; exact hW j2 (by omega))
        simpa using this
    · intro r hr w hw hrel
      rw [stp_len] at hw hrel ⊢
      have := H (r + 1) (by simp; omega) w (by omega) (by intro j2 hj2; exact hrel j2 (by omega))
      rw [show W.length + 1 + r = W.length + (r + 1) by omega]
      simpa using this
    · rw [stp_len]; simp at hj; omega
theorem allP (P : Bool → Bool → Prop) (ht : P true true)
    (hand : ∀ a b c d : Bool, P a b → P c d → P (a && c) (b && d)) :
    ∀ (l : List ℕ) (f1 f2 : ℕ → Bool), (∀ a ∈ l, P (f1 a) (f2 a)) →
      P ((l.map f1).all id) ((l.map f2).all id) := by
  intro l
  induction l with
  | nil => intro f1 f2 _; simpa using ht
  | cons x l ih =>
    intro f1 f2 h
    simp only [List.map_cons, List.all_cons, id]
    exact hand _ _ _ _ (h x (by simp)) (by simpa using ih f1 f2 (fun a ha => h a (by simp [ha])))

theorem anyP (P : Bool → Bool → Prop) (hf : P false false)
    (hor : ∀ a b c d : Bool, P a b → P c d → P (a || c) (b || d)) :
    ∀ (l : List ℕ) (f1 f2 : ℕ → Bool), (∀ a ∈ l, P (f1 a) (f2 a)) →
      P ((l.map f1).any id) ((l.map f2).any id) := by
  intro l
  induction l with
  | nil => intro f1 f2 _; simpa using hf
  | cons x l ih =>
    intro f1 f2 h
    simp only [List.map_cons, List.any_cons, id]
    exact hor _ _ _ _ (h x (by simp)) (by simpa using ih f1 f2 (fun a ha => h a (by simp [ha])))


theorem oe_len {n m : ℕ} (u : Fin n) (v : Fin m) : (PEqualNP.Represents.oneEach u v).length = n + m := by
  simp [PEqualNP.Represents.oneEach]


theorem p1and : ∀ a b c d : Bool, (a = true → b = true) → (c = true → d = true) →
    (a && c) = true → (b && d) = true := by decide

theorem p1or : ∀ a b c d : Bool, (a = true → b = true) → (c = true → d = true) →
    (a || c) = true → (b || d) = true := by decide


theorem all_mem_true (l : List ℕ) (f : ℕ → Bool) (a : ℕ) (ha : a ∈ l)
    (h : GateOp.and.eval (l.map f) = true) : f a = true := by
  have h' : (l.map f).all id = true := h
  rw [List.all_eq_true] at h'
  exact h' (f a) (List.mem_map.2 ⟨a, ha, rfl⟩)

theorem any_mem_true (l : List ℕ) (f : ℕ → Bool) (a : ℕ) (ha : a ∈ l) (h : f a = true) :
    GateOp.or.eval (l.map f) = true := by
  show (l.map f).any id = true
  rw [List.any_eq_true]
  exact ⟨f a, List.mem_map.2 ⟨a, ha, rfl⟩, h⟩


theorem oe_get {n m : ℕ} (u : Fin n) (v : Fin m) (i : ℕ) :
    (PEqualNP.Represents.oneEach u v).getD i false = decide (i = u.val ∨ i = n + v.val) := by
  unfold PEqualNP.Represents.oneEach
  rw [List.getD_eq_getElem?_getD]
  rcases lt_or_ge i n with h | h
  · rw [List.getElem?_append_left (by simp; omega)]
    simp only [List.getElem?_ofFn, h, dite_true, Option.getD_some, Fin.ext_iff]
    apply decide_eq_decide.2
    constructor <;> intro hh <;> omega
  · rw [List.getElem?_append_right (by simp; omega)]
    simp only [List.length_ofFn, List.getElem?_ofFn]
    by_cases h2 : i - n < m
    · simp only [h2, dite_true, Option.getD_some, Fin.ext_iff]
      apply decide_eq_decide.2
      constructor <;> intro hh <;> omega
    · simp only [h2, dite_false, Option.getD_none]
      symm
      apply decide_eq_false
      omega

theorem col_get {m : ℕ} (v : Fin m) (n i : ℕ) :
    (List.replicate n false ++ List.ofFn (fun c₀ : Fin m => decide (c₀ = v))).getD i false =
      decide (i = n + v.val) := by
  rw [List.getD_eq_getElem?_getD]
  rcases lt_or_ge i n with h | h
  · rw [List.getElem?_append_left (by simp; omega)]
    simp only [List.getElem?_replicate, h, if_true, Option.getD_some]
    symm
    apply decide_eq_false
    omega
  · rw [List.getElem?_append_right (by simp; omega)]
    simp only [List.length_replicate, List.getElem?_ofFn]
    by_cases h2 : i - n < m
    · simp only [h2, dite_true, Option.getD_some, Fin.ext_iff]
      apply decide_eq_decide.2
      constructor <;> intro hh <;> omega
    · simp only [h2, dite_false, Option.getD_none]
      symm
      apply decide_eq_false
      omega


theorem gval (C : Circuit) (N : ℕ) (hrb : PEqualNP.MetaComplexity.NestedCover.ReadsBack N C)
    (X : List Bool) (hX : X.length = N) (k : ℕ) (hk : k < C.gates.length) :
    (C.wires X).getD (N + k) false =
      (C.gates[k]).op.eval ((C.gates[k]).inputs.map fun a => (C.wires X).getD a false) := by
  have hv := vgate C.gates X k hk
  rw [hX] at hv
  show (C.gates.foldl stp X).getD (N + k) false = _
  rw [hv]
  congr 1
  apply List.map_congr_left
  intro a ha
  have : a < N + k := by
    apply hrb k hk a
    unfold PEqualNP.MetaComplexity.NestedCover.gateAt
    rw [List.getD_eq_getElem _ _ hk]
    exact ha
  rw [if_pos this]
  rfl

theorem dom (C : Circuit) (hC : PEqualNP.MetaComplexity.Monotone2 C) (X Y : List Bool)
    (hl : X.length = Y.length) (T : ℕ → Prop) (O : ℕ)
    (hin : ∀ i < X.length, ¬ T i → X.getD i false = true → Y.getD i false = true)
    (hcl : ∀ r (hr : r < C.gates.length), X.length + r ≠ O → ¬ T (X.length + r) →
      ∀ a ∈ (C.gates[r]).inputs, ¬ T a)
    (hO : (C.wires X).getD O false = true → (C.wires Y).getD O false = true) (t : ℕ) (ht : ¬ T t) :
    (C.wires X).getD t false = true → (C.wires Y).getD t false = true := by
  show (C.gates.foldl stp X).getD t false = true → (C.gates.foldl stp Y).getD t false = true
  have hO' : (C.gates.foldl stp X).getD O false = true →
      (C.gates.foldl stp Y).getD O false = true := hO
  have hrun := run (fun j bb => bb = (C.gates.foldl stp X).getD j false ∧
      (¬ T j → bb = true → (C.gates.foldl stp Y).getD j false = true)) C.gates X
    (by
      intro j hj
      refine ⟨(pre _ _ _ hj).symm, fun hT h => ?_⟩
      rw [pre _ _ _ (by omega)]
      exact hin j hj hT h)
    (by
      intro r hr w hw hrel
      have hvX := vgate C.gates X r hr
      have hvY := vgate C.gates Y r hr
      rw [← hl] at hvY
      have heq : (C.gates[r]).op.eval ((C.gates[r]).inputs.map fun a => w.getD a false) =
          (C.gates.foldl stp X).getD (X.length + r) false := by
        rw [hvX]
        congr 1
        apply List.map_congr_left
        intro a _
        by_cases hlt : a < X.length + r
        · rw [if_pos hlt]; exact (hrel a hlt).1
        · rw [if_neg hlt]; exact getD_ge w a (by omega)
      refine ⟨heq, fun hT h => ?_⟩
      by_cases hrO : X.length + r = O
      · rw [heq] at h
        rw [hrO] at h ⊢
        exact hO' h
      rw [hvY]
      have hna := hcl r hr hrO hT
      have key : ∀ a ∈ (C.gates[r]).inputs, (fun p q : Bool => p = true → q = true) (w.getD a false)
          (if a < X.length + r then (C.gates.foldl stp Y).getD a false else false) := by
        intro a ha
        by_cases hlt : a < X.length + r
        · rw [if_pos hlt]; exact (hrel a hlt).2 (hna a ha)
        · rw [getD_ge w a (by omega)]; intro h; exact absurd h (by simp)
      have hop := (hC _ (List.getElem_mem hr)).1
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
      rcases hop with e | e
      · rw [e] at h ⊢
        simp only [GateOp.eval] at h ⊢
        exact allP (fun p q : Bool => p = true → q = true) (fun h => h) p1and _ _ _ key h
      · rw [e] at h ⊢
        simp only [GateOp.eval] at h ⊢
        exact anyP (fun p q : Bool => p = true → q = true) (fun h => h) p1or _ _ _ key h)
  intro h
  by_cases hj : t < X.length + C.gates.length
  · exact (hrun t hj).2 ht h
  · rw [getD_ge _ _ (by rw [flen]; omega)] at h
    exact absurd h (by simp)

theorem hga (C : Circuit) (r : ℕ) (hr : r < C.gates.length) :
    PEqualNP.MetaComplexity.NestedCover.gateAt C r = C.gates[r] := by
  unfold PEqualNP.MetaComplexity.NestedCover.gateAt
  rw [List.getD_eq_getElem _ _ hr]

theorem avoid_ne (C : Circuit) (n m z s a : ℕ) (hs : s ≠ z)
    (h : Relation.ReflTransGen (fun prev next : ℕ => prev ≠ z ∧ next ≠ z ∧
      ∃ idx : Fin C.gates.length, next = n + m + idx.val ∧
        prev ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C idx.val).inputs) s a) : a ≠ z := by
  induction h with
  | refl => exact hs
  | tail _ hb _ => exact hb.2.1

theorem mono2 (C : Circuit) (hC : PEqualNP.MetaComplexity.Monotone2 C) (X Y : List Bool)
    (hl : X.length = Y.length) (hXY : ∀ i < X.length, X.getD i false = true → Y.getD i false = true)
    (t : ℕ) : (C.wires X).getD t false = true → (C.wires Y).getD t false = true := by
  apply dom C hC X Y hl (fun _ => False) (X.length + C.gates.length)
    (fun i hi _ h => hXY i hi h) (fun _ _ _ _ _ _ h => h) ?_ t (fun h => h)
  intro h
  have e : (C.wires X).getD (X.length + C.gates.length) false = false := by
    show (C.gates.foldl stp X).getD _ false = false
    exact getD_ge _ _ (by rw [flen])
  rw [e] at h
  exact absurd h (by simp)

end PEqualNP.Outside.L_meta_25487

open PEqualNP.Outside.L_meta_25487 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_25487 : ∀ (n m : ℕ) (G : Fin n → Fin m → Bool)
    (C : PEqualNP.CircuitLowerBounds.Circuit) (u v : Fin n)
    (j : Fin C.gates.length) (q : ℕ),
  let gate := PEqualNP.MetaComplexity.NestedCover.gateAt C
  let g := n + m + j.val
  let edge := fun source target : ℕ => ∃ idx : Fin C.gates.length,
    target = n + m + idx.val ∧ source ∈ (gate idx.val).inputs
  let cuts := fun (z start : ℕ) =>
    ¬ (start ≠ z ∧ C.output ≠ z ∧ Relation.ReflTransGen
      (fun prev next : ℕ => prev ≠ z ∧ next ≠ z ∧ edge prev next) start C.output)
  PEqualNP.MetaComplexity.Monotone2 C →
  PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) C →
  PEqualNP.Represents.Represents G C → u ≠ v →
  (gate j.val).op = PEqualNP.CircuitLowerBounds.GateOp.and →
  q ∈ (gate j.val).inputs →
  cuts g u.val → cuts q v.val → ¬ Relation.ReflTransGen edge u.val q →
  ∀ c : Fin m, (∃ w : Fin n, G w c = false) →
    let col := List.replicate n false ++ List.ofFn (fun b : Fin m => decide (b = c))
    let value := (C.wires col).getD q false
    (G u c = true → value = true) ∧ (G v c = true → value = false) := by
  intro n m G C u v j q gate g edge cuts hC hrb hrep huv hop hq hcu hcv hnr c hw col value
  obtain ⟨w0, hw0⟩ := hw
  have hu1 := u.2
  have hv1 := v.2
  have hc1 := c.2
  have hj1 := j.2
  have hvu : u.val ≠ v.val := fun e => huv (Fin.ext e)
  have hcolg : ∀ i, col.getD i false = decide (i = n + c.val) := fun i => col_get c n i
  have hcoll : col.length = n + m := by simp [col]
  have hgj : PEqualNP.MetaComplexity.NestedCover.gateAt C j.val = C.gates[j.val] := hga C j.val j.2
  have hop' : (C.gates[j.val]).op = GateOp.and := by rw [← hgj]; exact hop
  have hq' : q ∈ (C.gates[j.val]).inputs := by rw [← hgj]; exact hq
  have hqlt : q < n + m + j.val := by
    apply hrb j.val j.2 q
    exact hq
  have hcolW : ∀ t, (C.wires col).getD t false = true →
      (C.wires (PEqualNP.Represents.oneEach w0 c)).getD t false = true := by
    intro t
    apply mono2 C hC col _ (by rw [hcoll, oe_len])
    intro i _ h
    rw [hcolg] at h
    rw [oe_get]
    simp only [decide_eq_true_eq] at h ⊢
    omega
  have hWo : (C.wires (PEqualNP.Represents.oneEach w0 c)).getD C.output false = true → False := by
    intro h
    have e : C.eval (PEqualNP.Represents.oneEach w0 c) = true := h
    rw [hrep, hw0] at e
    exact absurd e (by simp)
  refine ⟨fun hu => ?_, fun hv => ?_⟩
  · have hXl : (PEqualNP.Represents.oneEach u c).length = n + m := oe_len u c
    have hXc : (PEqualNP.Represents.oneEach u c).length = col.length := by rw [hXl, hcoll]
    have hinX : ∀ T : ℕ → Prop, T u.val → ∀ i' < (PEqualNP.Represents.oneEach u c).length, ¬ T i' →
        (PEqualNP.Represents.oneEach u c).getD i' false = true → col.getD i' false = true := by
      intro T hTu i' _ hT h
      have : i' ≠ u.val := fun e => hT (e ▸ hTu)
      rw [oe_get] at h
      rw [hcolg]
      simp only [decide_eq_true_eq] at h ⊢
      omega
    have hXo : (C.wires (PEqualNP.Represents.oneEach u c)).getD C.output false = true := by
      show C.eval _ = true
      rw [hrep]; exact hu
    have hXg : (C.wires (PEqualNP.Represents.oneEach u c)).getD (n + m + j.val) false = true := by
      by_contra hne
      rw [Bool.not_eq_true] at hne
      by_cases hog : C.output = n + m + j.val
      · rw [hog, hne] at hXo
        exact absurd hXo (by simp)
      apply hWo
      apply hcolW
      refine dom C hC _ _ hXc (fun t => Relation.ReflTransGen
          (fun prev next : ℕ => prev ≠ n + m + j.val ∧ next ≠ n + m + j.val ∧ edge prev next)
          u.val t) (n + m + j.val) (hinX _ Relation.ReflTransGen.refl) ?_
        (fun h => by rw [hne] at h; exact absurd h (by simp)) C.output
        (fun h => hcu ⟨by show u.val ≠ n + m + j.val; omega, hog, h⟩) hXo
      intro r hr hrO hnT a ha hTa
      rw [hXl] at hrO hnT
      apply hnT
      exact Relation.ReflTransGen.tail hTa
        ⟨avoid_ne C n m _ u.val a (by omega) hTa, hrO, ⟨r, hr⟩, rfl,
          by show a ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C r).inputs; rw [hga C r hr]; exact ha⟩
    have hXq : (C.wires (PEqualNP.Represents.oneEach u c)).getD q false = true := by
      rw [gval C (n + m) hrb _ hXl j.val j.2, hop'] at hXg
      exact all_mem_true _ _ q hq' hXg
    show (C.wires col).getD q false = true
    refine dom C hC _ _ hXc (fun t => Relation.ReflTransGen edge u.val t)
      (n + m + C.gates.length) (hinX _ Relation.ReflTransGen.refl) ?_ ?_ q hnr hXq
    · intro r hr _ hnT a ha hTa
      rw [hXl] at hnT
      apply hnT
      exact Relation.ReflTransGen.tail hTa
        ⟨⟨r, hr⟩, rfl, by show a ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C r).inputs; rw [hga C r hr]; exact ha⟩
    · intro h
      have e : (C.wires (PEqualNP.Represents.oneEach u c)).getD (n + m + C.gates.length) false = false := by
        show (C.gates.foldl stp _).getD _ false = false
        exact getD_ge _ _ (by rw [flen, hXl])
      rw [e] at h
      exact absurd h (by simp)
  · show (C.wires col).getD q false = false
    by_contra hne
    rw [Bool.not_eq_false] at hne
    by_cases hqv : q = v.val
    · have e : (C.wires col).getD q false = col.getD q false := pre _ _ _ (by rw [hcoll]; omega)
      rw [e, hcolg] at hne
      simp only [decide_eq_true_eq] at hne
      omega
    by_cases hoq : C.output = q
    · apply hWo
      rw [hoq]
      exact hcolW q hne
    have hYl : (PEqualNP.Represents.oneEach v c).length = n + m := oe_len v c
    have hYW : (PEqualNP.Represents.oneEach v c).length =
        (PEqualNP.Represents.oneEach w0 c).length := by rw [hYl, oe_len]
    have hYo : (C.wires (PEqualNP.Represents.oneEach v c)).getD C.output false = true := by
      show C.eval _ = true
      rw [hrep]; exact hv
    apply hWo
    refine dom C hC _ _ hYW (fun t => Relation.ReflTransGen
        (fun prev next : ℕ => prev ≠ q ∧ next ≠ q ∧ edge prev next) v.val t) q ?_ ?_
      (fun _ => hcolW q hne) C.output (fun h => hcv ⟨fun e => hqv e.symm, hoq, h⟩) hYo
    · intro i' _ hT h
      have : i' ≠ v.val := fun e => hT (by subst e; exact Relation.ReflTransGen.refl)
      rw [oe_get] at h ⊢
      simp only [decide_eq_true_eq] at h ⊢
      omega
    · intro r hr hrO hnT a ha hTa
      rw [hYl] at hrO hnT
      apply hnT
      exact Relation.ReflTransGen.tail hTa
        ⟨avoid_ne C n m _ v.val a (fun e => hqv e.symm) hTa, hrO, ⟨r, hr⟩, rfl,
          by show a ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C r).inputs; rw [hga C r hr]; exact ha⟩
