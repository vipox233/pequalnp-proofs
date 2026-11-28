import PEqualNP.Defs
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

namespace PEqualNP.Outside.L_meta_53209

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def val (x : List Bool) (g : List Gate) (w : ℕ) : Bool :=
  ((⟨g, 0⟩ : Circuit).wires x).getD w false

def Ok (n : ℕ) (g : List Gate) : Prop :=
  (∀ h ∈ g, (h.op = GateOp.and ∨ h.op = GateOp.or) ∧ h.inputs.length ≤ 2) ∧
  (∀ j (hj : j < g.length), ∀ i ∈ (g[j]).inputs, i < n + j)

def Ext (n : ℕ) (g g' : List Gate) : Prop :=
  Ok n g' ∧ g.length ≤ g'.length ∧ ∀ x : List Bool, x.length = n → ∀ w < n + g.length, val x g' w = val x g w

lemma wires_snoc (x : List Bool) (g : List Gate) (h : Gate) :
    (⟨g ++ [h], 0⟩ : Circuit).wires x =
      (⟨g, 0⟩ : Circuit).wires x ++ [h.op.eval (h.inputs.map fun i => val x g i)] := by
  simp [Circuit.wires, val, List.foldl_append]

lemma wires_length (x : List Bool) (g : List Gate) : ((⟨g, 0⟩ : Circuit).wires x).length = x.length + g.length := by
  induction g using List.reverseRecOn with
  | nil => simp [Circuit.wires]
  | append_singleton g h ih => rw [wires_snoc]; simp [ih]; omega

lemma Ext.refl {n g} (h : Ok n g) : Ext n g g := ⟨h, le_rfl, fun _ _ _ _ => rfl⟩

lemma Ext.trans {n g g' g''} (a : Ext n g g') (b : Ext n g' g'') : Ext n g g'' :=
  ⟨b.1, a.2.1.trans b.2.1, fun x hx w hw => by
    rw [b.2.2 x hx w (by have := a.2.1; omega), a.2.2 x hx w hw]⟩

lemma add_gate {n g} (hg : Ok n g) (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (a b : ℕ)
    (ha : a < n + g.length) (hb : b < n + g.length) :
    Ext n g (g ++ [⟨op, [a, b]⟩]) ∧ n + g.length < n + (g ++ [(⟨op, [a, b]⟩ : Gate)]).length ∧
      ∀ x : List Bool, x.length = n → val x (g ++ [⟨op, [a, b]⟩]) (n + g.length) = op.eval [val x g a, val x g b] := by
  refine ⟨⟨⟨?_, ?_⟩, by simp, ?_⟩, by simp, ?_⟩
  · intro h hh
    rcases List.mem_append.1 hh with hh | hh
    · exact hg.1 h hh
    · rw [List.mem_singleton.1 hh]; exact ⟨hop, by simp⟩
  · intro j hj i hi
    by_cases hlt : j < g.length
    · rw [List.getElem_append_left hlt] at hi
      exact hg.2 j hlt i hi
    · have : j = g.length := by simp at hj; omega
      subst this
      simp at hi
      rcases hi with rfl | rfl <;> assumption
  · intro x hx w hw
    unfold val
    rw [wires_snoc, List.getD_append _ _ _ _ (by rw [wires_length, hx]; exact hw)]
  · intro x hx
    have hl : ((⟨g, 0⟩ : Circuit).wires x).length = n + g.length := by rw [wires_length, hx]
    unfold val
    rw [wires_snoc, List.getD_append_right _ _ _ _ (by rw [hl])]
    simp [hl, val]

lemma chain_and {n g} (hg : Ok n g) (acc : ℕ) (l : List ℕ) (ha : acc < n + g.length) (hl : ∀ i ∈ l, i < n) :
    ∃ g' w, Ext n g g' ∧ w < n + g'.length ∧
      ∀ x : List Bool, x.length = n → val x g' w = (val x g acc && l.all (fun i => val x g i)) := by
  induction l generalizing g acc with
  | nil => exact ⟨g, acc, Ext.refl hg, ha, fun x _ => by simp⟩
  | cons i l ih =>
    have hi : i < n + g.length := by have := hl i (by simp); omega
    obtain ⟨e, hw, hv⟩ := add_gate hg GateOp.and (Or.inl rfl) acc i ha hi
    obtain ⟨g', w, e', hw', hv'⟩ := ih e.1 (n + g.length) hw (fun j hj => hl j (by simp [hj]))
    refine ⟨g', w, e.trans e', hw', fun x hx => ?_⟩
    rw [hv' x hx, hv x hx]
    have : l.all (fun j => val x (g ++ [⟨GateOp.and, [acc, i]⟩]) j) = l.all (fun j => val x g j) := by
      rw [Bool.eq_iff_iff]
      simp only [List.all_eq_true]
      constructor <;> intro H j hj
      · rw [← e.2.2 x hx j (by have := hl j (by simp [hj]); omega)]; exact H j hj
      · rw [e.2.2 x hx j (by have := hl j (by simp [hj]); omega)]; exact H j hj
    rw [this]
    simp [GateOp.eval, Bool.and_assoc]

def dnf (x : List Bool) (T : List (List ℕ)) : Bool := T.any (fun t => t.all (fun i => x.getD i false))

lemma val_input (x : List Bool) (g : List Gate) (i : ℕ) (hi : i < x.length) : val x g i = x.getD i false := by
  induction g using List.reverseRecOn with
  | nil => simp [val, Circuit.wires]
  | append_singleton g h ih =>
    unfold val at ih ⊢
    rw [wires_snoc, List.getD_append _ _ _ _ (by rw [wires_length]; omega)]
    exact ih

lemma build_dnf {n g} (hg : Ok n g) (f t : ℕ) (hf : f < n) (ht : t < n) (T : List (List ℕ))
    (hT : ∀ term ∈ T, ∀ i ∈ term, i < n) :
    ∃ g' w, Ext n g g' ∧ w < n + g'.length ∧
      ∀ x : List Bool, x.length = n → x.getD f false = false → x.getD t false = true → val x g' w = dnf x T := by
  induction T generalizing g with
  | nil =>
    refine ⟨g, f, Ext.refl hg, by omega, fun x hx h0 _ => ?_⟩
    rw [val_input x g f (by omega), h0]; simp [dnf]
  | cons term T ih =>
    obtain ⟨g1, r, e1, hr, hv1⟩ := ih hg (fun s hs => hT s (by simp [hs]))
    obtain ⟨g2, a, e2, ha, hv2⟩ := chain_and e1.1 t term (by omega) (hT term (by simp))
    have hr2 : r < n + g2.length := by have := e2.2.1; omega
    obtain ⟨e3, hw, hv3⟩ := add_gate e2.1 GateOp.or (Or.inr rfl) a r ha hr2
    refine ⟨_, _, (e1.trans e2).trans e3, hw, fun x hx h0 h1 => ?_⟩
    have hterm : term.all (fun i => val x g1 i) = term.all (fun i => x.getD i false) := by
      rw [Bool.eq_iff_iff]
      simp only [List.all_eq_true]
      constructor <;> intro H i hi
      · rw [← val_input x g1 i (by have := hT term (by simp) i hi; omega)]; exact H i hi
      · rw [val_input x g1 i (by have := hT term (by simp) i hi; omega)]; exact H i hi
    rw [hv3 x hx, hv2 x hx, e2.2.2 x hx r hr, hv1 x hx h0 h1, hterm, val_input x g1 t (by omega), h1]
    simp [GateOp.eval, dnf]

lemma build_many {n} (f t : ℕ) (hf : f < n) (ht : t < n) : ∀ (k : ℕ) (T : Fin k → List (List ℕ)),
    (∀ j, ∀ term ∈ T j, ∀ i ∈ term, i < n) → ∀ g, Ok n g →
    ∃ g' : List Gate, ∃ o : Fin k → ℕ, Ext n g g' ∧ (∀ j, o j < n + g'.length) ∧
      ∀ x : List Bool, x.length = n → x.getD f false = false → x.getD t false = true → ∀ j, val x g' (o j) = dnf x (T j) := by
  intro k
  induction k with
  | zero =>
    intro T _ g hg
    exact ⟨g, fun j => j.elim0, Ext.refl hg, fun j => j.elim0, fun _ _ _ _ j => j.elim0⟩
  | succ k ih =>
    intro T hT g hg
    obtain ⟨g1, w, e1, hw, hv1⟩ := build_dnf hg f t hf ht (T 0) (hT 0)
    obtain ⟨g2, o, e2, ho, hv2⟩ := ih (fun j => T j.succ) (fun j => hT j.succ) g1 e1.1
    refine ⟨g2, Fin.cases w o, e1.trans e2, ?_, ?_⟩
    · intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · have := e2.2.1; simp; omega
      · simpa using ho j
    · intro x hx h0 h1 j
      refine Fin.cases ?_ (fun j => ?_) j
      · simp only [Fin.cases_zero]
        rw [e2.2.2 x hx w hw, hv1 x hx h0 h1]
      · simpa using hv2 x hx h0 h1 j

lemma circuit_mono (g : List Gate) (hg : ∀ h ∈ g, (h.op = GateOp.and ∨ h.op = GateOp.or))
    (x y : List Bool) (hl : x.length = y.length) (hxy : ∀ w, x.getD w false = true → y.getD w false = true) :
    ∀ w, val x g w = true → val y g w = true := by
  induction g using List.reverseRecOn with
  | nil => simpa [val, Circuit.wires] using hxy
  | append_singleton g h ih =>
    have ih' := ih (fun k hk => hg k (by simp [hk]))
    intro w hw
    have lx : ((⟨g, 0⟩ : Circuit).wires x).length = x.length + g.length := wires_length x g
    have ly : ((⟨g, 0⟩ : Circuit).wires y).length = x.length + g.length := by rw [wires_length, hl]
    unfold val at hw ⊢
    rw [wires_snoc] at hw ⊢
    by_cases hlt : w < x.length + g.length
    · rw [List.getD_append _ _ _ _ (by omega)] at hw ⊢
      exact ih' w hw
    · rw [List.getD_append_right _ _ _ _ (by omega)] at hw ⊢
      rw [lx] at hw
      rw [ly]
      cases hk : w - (x.length + g.length) with
      | succ k => rw [hk] at hw; simp at hw
      | zero =>
        rw [hk] at hw
        simp only [List.getD_cons_zero] at hw ⊢
        rcases hg h (by simp) with hop | hop
        · rw [hop] at hw ⊢
          simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq] at hw ⊢
          rintro b ⟨i, hi, rfl⟩
          exact ih' i (hw _ ⟨i, hi, rfl⟩)
        · rw [hop] at hw ⊢
          simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq] at hw ⊢
          obtain ⟨b, ⟨i, hi, rfl⟩, hb⟩ := hw
          exact ⟨_, ⟨i, hi, rfl⟩, ih' i hb⟩

lemma reads_of_ok' {n : ℕ} {g : List Gate} (h : Ok n g) (o : ℕ) : ReadsBack n ⟨g, o⟩ := by
  intro j hj i hi
  have e : gateAt ⟨g, o⟩ j = g[j] := by
    simp [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  rw [e] at hi
  exact h.2 j hj i hi

open Finset

lemma identity (t : ℕ) (ht : 3 ≤ t) :
    2 * (∑ j ∈ (range t).filter (fun j => 1 ≤ j ∧ 2 * j + 1 < t), t.choose j) +
      (if t % 2 = 1 then t.choose (t / 2) else 0) + t.choose (t / 2) + 2 = 2 ^ t := by
  have first : ∀ K, 1 ≤ K → ∑ j ∈ range K, t.choose j = 1 + ∑ j ∈ Ico 1 K, t.choose j := by
    intro K hK
    rw [← sum_range_add_sum_Ico _ hK]
    simp [sum_range_succ]
  have total : ∑ j ∈ range (t + 1), t.choose j = 2 ^ t := Nat.sum_range_choose t
  rcases Nat.even_or_odd' t with ⟨k, hk | hk⟩
  · have hk2 : 1 ≤ k := by omega
    have e : (range t).filter (fun j => 1 ≤ j ∧ 2 * j + 1 < t) = Ico 1 k := by
      ext j
      simp only [mem_filter, mem_range, mem_Ico]
      omega
    have half : t / 2 = k := by omega
    have split : ∑ j ∈ range (t + 1), t.choose j = 2 * (∑ j ∈ range k, t.choose j) + t.choose k := by
      have a : t + 1 = (k + 1) + k := by omega
      rw [a, sum_range_add, sum_range_succ]
      have refl : ∑ x ∈ range k, t.choose (k + 1 + x) = ∑ j ∈ range k, t.choose j := by
        rw [← sum_range_reflect (fun j => t.choose j) k]
        refine sum_congr rfl (fun x hx => ?_)
        have := mem_range.1 hx
        rw [← Nat.choose_symm (by omega : k + 1 + x ≤ t)]
        congr 1
        omega
      rw [refl]
      ring
    rw [e, half, if_neg (by omega)]
    have f := first k hk2
    omega
  · have hk2 : 1 ≤ k := by omega
    have e : (range t).filter (fun j => 1 ≤ j ∧ 2 * j + 1 < t) = Ico 1 k := by
      ext j
      simp only [mem_filter, mem_range, mem_Ico]
      omega
    have half : t / 2 = k := by omega
    have split : ∑ j ∈ range (t + 1), t.choose j = 2 * (∑ j ∈ range k, t.choose j) + 2 * t.choose k := by
      have a : t + 1 = (k + 1) + (k + 1) := by omega
      rw [a, sum_range_add, sum_range_succ]
      have refl : ∑ x ∈ range (k + 1), t.choose (k + 1 + x) = ∑ j ∈ range (k + 1), t.choose j := by
        rw [← sum_range_reflect (fun j => t.choose j) (k + 1)]
        refine sum_congr rfl (fun x hx => ?_)
        have := mem_range.1 hx
        rw [← Nat.choose_symm (by omega : k + 1 + x ≤ t)]
        congr 1
        omega
      rw [refl, sum_range_succ]
      ring
    rw [e, half, if_pos (by omega)]
    have f := first k hk2
    omega

/-- 2e conjuntos distintos, en parejas disjuntas que no cubren todo, caben fuera de la capa central. -/
lemma pair_count {ι : Type} (E : Finset ι) (t : ℕ) (B G : ι → Finset (Fin t))
    (inj : ∀ a ∈ E, ∀ b ∈ E, (B a = B b → a = b) ∧ (G a = G b → a = b) ∧ B a ≠ G b)
    (ne : ∀ a ∈ E, (B a).Nonempty ∧ (G a).Nonempty) (dis : ∀ a ∈ E, Disjoint (B a) (G a))
    (small : ∀ a ∈ E, (B a).card + (G a).card + 1 ≤ t) (nonempty : E.Nonempty) :
    2 * E.card + t.choose (t / 2) + 2 ≤ 2 ^ t := by
  classical
  have ht : 3 ≤ t := by
    obtain ⟨a, ha⟩ := nonempty
    have h1 := card_pos.2 (ne a ha).1
    have h2 := card_pos.2 (ne a ha).2
    have := small a ha
    omega
  let w : Finset (Fin t) → ℕ := fun S =>
    if 1 ≤ S.card ∧ 2 * S.card + 1 < t then 2 else if 2 * S.card + 1 = t then 1 else 0
  have each : ∀ a ∈ E, 2 ≤ w (B a) + w (G a) := by
    intro a ha
    have h1 := card_pos.2 (ne a ha).1
    have h2 := card_pos.2 (ne a ha).2
    have := small a ha
    simp only [w]
    split_ifs <;> omega
  have disjImg : Disjoint (E.image B) (E.image G) := by
    rw [disjoint_left]
    intro S h1 h2
    obtain ⟨a, ha, e1⟩ := mem_image.1 h1
    obtain ⟨b, hb, e2⟩ := mem_image.1 h2
    exact (inj a ha b hb).2.2 (e1.trans e2.symm)
  have lower : 2 * E.card ≤ ∑ S ∈ E.image B ∪ E.image G, w S := by
    rw [sum_union disjImg, sum_image (fun a ha b hb h => (inj a ha b hb).1 h),
      sum_image (fun a ha b hb h => (inj a ha b hb).2.1 h), ← sum_add_distrib]
    have s := sum_le_sum each
    simpa [mul_comm] using s
  have upper : ∑ S ∈ E.image B ∪ E.image G, w S ≤ ∑ S : Finset (Fin t), w S :=
    sum_le_sum_of_subset (subset_univ _)
  have value : ∑ S : Finset (Fin t), w S =
      2 * (∑ j ∈ (range t).filter (fun j => 1 ≤ j ∧ 2 * j + 1 < t), t.choose j) +
        (if t % 2 = 1 then t.choose (t / 2) else 0) := by
    have grp : ∑ S : Finset (Fin t), w S = ∑ j ∈ range (t + 1), t.choose j *
        (if 1 ≤ j ∧ 2 * j + 1 < t then 2 else if 2 * j + 1 = t then 1 else 0) := by
      rw [← powerset_univ, sum_powerset_apply_card (fun j => if 1 ≤ j ∧ 2 * j + 1 < t then 2 else if 2 * j + 1 = t then 1 else 0)]
      simp
    rw [grp]
    have split : ∀ j ∈ range (t + 1), t.choose j * (if 1 ≤ j ∧ 2 * j + 1 < t then 2 else if 2 * j + 1 = t then 1 else 0) =
        (if 1 ≤ j ∧ 2 * j + 1 < t then 2 * t.choose j else 0) + (if 2 * j + 1 = t then t.choose j else 0) := by
      intro j _
      split_ifs <;> omega
    rw [sum_congr rfl split, sum_add_distrib]
    congr 1
    · rw [← sum_filter, mul_sum]
      refine sum_congr ?_ (fun _ _ => rfl)
      ext j
      simp only [mem_filter, mem_range]
      omega
    · split_ifs with h
      · rw [sum_eq_single (t / 2)]
        · rw [if_pos (by omega)]
        · intro j _ hj
          rw [if_neg (by omega)]
        · intro hn
          exact absurd (mem_range.2 (by omega)) hn
      · exact sum_eq_zero (fun j _ => if_neg (by omega))
  have idn := identity t ht
  omega

/-- Compuertas AND que leen solo entradas. -/
lemma and_wires (x : List Bool) (ps : List (ℕ × ℕ)) (h : ∀ p ∈ ps, p.1 < x.length ∧ p.2 < x.length) :
    (⟨ps.map (fun p => ⟨GateOp.and, [p.1, p.2]⟩), 0⟩ : Circuit).wires x =
      x ++ ps.map (fun p => x.getD p.1 false && x.getD p.2 false) := by
  induction ps using List.reverseRecOn with
  | nil => simp [Circuit.wires]
  | append_singleton ps p ih =>
    have ih' := ih (fun q hq => h q (by simp [hq]))
    obtain ⟨h1, h2⟩ := h p (by simp)
    rw [List.map_append, List.map_cons, List.map_nil, wires_snoc]
    unfold val
    rw [ih', List.map_append, ← List.append_assoc]
    congr 1
    simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true]
    rw [List.getD_append _ _ _ _ h1, List.getD_append _ _ _ _ h2]

lemma wire_of {α : Type} [DecidableEq (α → Bool)] (L : List (α → Bool)) (g : α → Bool) (hg : g ∈ L) (x : α) :
    L.idxOf g < L.length ∧ (L.map (fun h => h x)).getD (L.idxOf g) false = g x := by
  have lt := List.idxOf_lt_length_iff.2 hg
  refine ⟨lt, ?_⟩
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem lt]
  simp

lemma lado1 (M U V : Prop) (h : ¬ ((M ∧ ¬U) ↔ (M ∧ ¬V))) : M ∧ ¬ (U ↔ V) := by
  by_cases a : M <;> by_cases b : U <;> by_cases c : V <;> simp [a, b, c] at h ⊢

lemma lado2 (M U V : Prop) (h : ¬ ((U ∧ ¬M) ↔ (V ∧ ¬M))) : ¬M ∧ ¬ (U ↔ V) := by
  by_cases a : M <;> by_cases b : U <;> by_cases c : V <;> simp [a, b, c] at h ⊢

lemma medio (n k : ℕ) (h : k ≤ n) : k * (n - k) ≤ (n / 2) * (n - n / 2) := by
  obtain ⟨m, hm⟩ : ∃ m, n = k + m := ⟨n - k, by omega⟩
  have e : n - k = m := by omega
  rcases Nat.even_or_odd' n with ⟨t, ht | ht⟩
  · have a : n / 2 = t := by omega
    have b : n - n / 2 = t := by omega
    rw [e, b, a]
    have s : k + m = 2 * t := by omega
    zify at s ⊢
    nlinarith [sq_nonneg ((k : ℤ) - m)]
  · have a : n / 2 = t := by omega
    have b : n - n / 2 = t + 1 := by omega
    rw [e, b, a]
    have s : k + m = 2 * t + 1 := by omega
    have ne : (k : ℤ) - m ≠ 0 := by omega
    have one : 1 ≤ ((k : ℤ) - m) ^ 2 := by
      have := mul_self_pos.2 ne
      nlinarith
    zify at s ⊢
    nlinarith

lemma comun (s y z : Prop) [Decidable s] [Decidable y] [Decidable z] (h : ¬ (y ↔ z)) :
    1 ≤ (((if s then 1 else 0 : ℕ) + (if y then 1 else 0)) - ((if s then 1 else 0) + (if z then 1 else 0))) +
      (((if s then 1 else 0 : ℕ) + (if z then 1 else 0)) - ((if s then 1 else 0) + (if y then 1 else 0))) := by
  by_cases a : s <;> by_cases b : y <;> by_cases c : z <;> simp [a, b, c] at h ⊢

lemma dobles (a c : Prop) [Decidable a] [Decidable c] (h : ¬ (a ↔ c)) :
    1 ≤ (((if a then 1 else 0 : ℕ) + (if a then 1 else 0)) - ((if c then 1 else 0) + (if c then 1 else 0))) +
      (((if c then 1 else 0 : ℕ) + (if c then 1 else 0)) - ((if a then 1 else 0) + (if a then 1 else 0))) := by
  by_cases x : a <;> by_cases y : c <;> simp [x, y] at h ⊢

lemma doble (a c d : Prop) [Decidable a] [Decidable c] [Decidable d] (h : ¬ (c ↔ d)) :
    1 ≤ (((if a then 1 else 0 : ℕ) + (if a then 1 else 0)) - ((if c then 1 else 0) + (if d then 1 else 0))) +
      (((if c then 1 else 0 : ℕ) + (if d then 1 else 0)) - ((if a then 1 else 0) + (if a then 1 else 0))) := by
  by_cases x : a <;> by_cases y : c <;> by_cases z : d <;> simp [x, y, z] at h ⊢

lemma doble' (a b c : Prop) [Decidable a] [Decidable b] [Decidable c] (h : ¬ (a ↔ b)) :
    1 ≤ (((if a then 1 else 0 : ℕ) + (if b then 1 else 0)) - ((if c then 1 else 0) + (if c then 1 else 0))) +
      (((if c then 1 else 0 : ℕ) + (if c then 1 else 0)) - ((if a then 1 else 0) + (if b then 1 else 0))) := by
  by_cases x : a <;> by_cases y : b <;> by_cases z : c <;> simp [x, y, z] at h ⊢

lemma paralelo (v : ℕ) (a b c d : Prop) [Decidable a] [Decidable b] [Decidable c] [Decidable d]
    {i1 : Decidable (¬ (a ↔ c))} {i2 : Decidable (¬ (a ↔ d))} {i3 : Decidable (¬ (b ↔ c))} {i4 : Decidable (¬ (b ↔ d))}
    {i5 : Decidable (¬ (a ↔ b))} {i6 : Decidable (¬ (c ↔ d))} :
    (if ¬ (a ↔ c) then v else 0) + (if ¬ (a ↔ d) then v else 0) + (if ¬ (b ↔ c) then v else 0) + (if ¬ (b ↔ d) then v else 0) ≤
      (if ¬ (a ↔ b) then v else 0) + (if ¬ (c ↔ d) then v else 0) +
      2 * (v * ((((if a then 1 else 0 : ℕ) + (if b then 1 else 0)) - ((if c then 1 else 0) + (if d then 1 else 0))) +
        (((if c then 1 else 0 : ℕ) + (if d then 1 else 0)) - ((if a then 1 else 0) + (if b then 1 else 0))))) := by
  by_cases x : a <;> by_cases y : b <;> by_cases z : c <;> by_cases t : d <;> simp [x, y, z, t] <;> omega

lemma memF {α : Type} {p : α → Prop} {i : DecidablePred p} {s : Finset α} {x : α} : x ∈ s.filter p ↔ x ∈ s ∧ p x :=
  Finset.mem_filter

end PEqualNP.Outside.L_meta_53209

set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_53209 : ∀ (n : Nat) (E : Finset (Fin n × Fin n)), 2 ≤ n →
  (∀ e ∈ E, e.1 < e.2) →
  (∀ Z : Finset (Fin n), (∀ e ∈ E, e.1 ∈ Z ↔ e.2 ∈ Z) → Z = ∅ ∨ Z = Finset.univ) →
  letI : ∀ Q : Prop, Decidable Q := Classical.propDecidable
  let W := Finset (Fin n)
  let bit := fun (i : Fin n) (x : W) => decide (i ∈ x)
  let neg := fun (i : Fin n) (x : W) => !(bit i x)
  let same := fun (e : Fin n × Fin n) (x : W) => bit e.1 x == bit e.2 x
  let raw : Finset (W → Bool) := {fun _ => false,fun _ => true} ∪ Finset.univ.image bit ∪
    E.image same ∪ E.image (fun e x => !(same e x))
  let need := Finset.univ.image neg ∪ E.image (fun e x => neg e.1 x && neg e.2 x) ∪
    E.image (fun e x => bit e.1 x && neg e.2 x) ∪ E.image (fun e x => neg e.1 x && bit e.2 x)
  let keeps := fun A : Finset W => ∀ (S : W) (p : Nat),
    let L := (raw ∪ S.image neg).toList
    (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack L.length C ∧
      C.output < L.length+C.size ∧ C.size ≤ p ∧ ∀ f ∈ need, ∃ j < L.length+C.size,
        ∀ x ∈ A, (C.wires (L.map (fun g => g x))).getD j false = f x) ↔
    S.Nonempty ∧ n+3*E.card-S.card ≤ p
  let adj := fun i j : Fin n => (i,j) ∈ E ∨ (j,i) ∈ E
  let valid := fun (D : Nat) (w : W → Nat) =>
    ∀ lost : W → Nat, (∑ x, lost x) < D →
      keeps (Finset.univ.filter (fun x => lost x < w x))
  let pairs := (Finset.univ : Finset (Fin n × Fin n)).filter (fun e => e.1 < e.2)
  ∀ (v : Fin n) (D : Nat) (w : W → Nat),
    (∀ i, i ≠ v → adj i v) → 0 < D → valid D w →
    let lo := (Finset.univ : Finset W).filter (fun x => x ≠ ∅ ∧ v ∉ x)
    let hi := (Finset.univ : Finset W).filter (fun x => x ≠ Finset.univ ∧ v ∈ x)
    let F := if lo.sum w ≤ hi.sum w then lo else hi
    let dist := fun e : Fin n × Fin n =>
      (F.filter (fun x => ¬ (e.1 ∈ x ↔ e.2 ∈ x))).sum w
    let extra := ∑ e ∈ pairs, (dist e-D)
    let count := fun (e : Fin n × Fin n) (x : W) =>
      (if e.1 ∈ x then 1 else 0 : Nat) + (if e.2 ∈ x then 1 else 0)
    (∀ e ∈ pairs, D ≤ dist e) ∧
      extra + pairs.card*D ≤ F.sum w*((n/2)*(n-n/2)) ∧
      ∀ e f : Fin n × Fin n, e.1 ≤ e.2 → f.1 ≤ f.2 → e ≠ f →
        2*D ≤ extra + 2*F.sum (fun x => w x *
          ((count e x - count f x) + (count f x - count e x))) := by
  intro n E hn hE hconn W bit neg same raw need keeps adj valid pairs v D w hpiv hD hval lo hi F dist extra count
  letI dec : DecidableEq (W → Bool) := fun a b => Classical.propDecidable (a = b)
  have bitT : ∀ i x, bit i x = true ↔ i ∈ x := fun i x => by simp [bit]
  have negT : ∀ i x, neg i x = true ↔ i ∉ x := fun i x => by simp [neg, bit]
  have rawF : (fun _ => false : W → Bool) ∈ raw :=
    Finset.mem_union.2 (Or.inl (Finset.mem_union.2 (Or.inl (Finset.mem_union.2 (Or.inl (Finset.mem_insert_self _ _))))))
  have rawT : (fun _ => true : W → Bool) ∈ raw :=
    Finset.mem_union.2 (Or.inl (Finset.mem_union.2 (Or.inl (Finset.mem_union.2 (Or.inl
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))))))
  have rawB : ∀ i, bit i ∈ raw := fun i =>
    Finset.mem_union.2 (Or.inl (Finset.mem_union.2 (Or.inl (Finset.mem_union.2 (Or.inr
      (Finset.mem_image_of_mem _ (Finset.mem_univ _)))))))
  have hne : E.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    let v0 : Fin n := ⟨0, by omega⟩
    have := hconn {v0} (fun e he => by rw [h] at he; exact absurd he (Finset.notMem_empty e))
    rcases this with h1 | h1
    · exact Finset.singleton_ne_empty _ h1
    · have c1 := congrArg Finset.card h1
      rw [Finset.card_singleton, Finset.card_univ, Fintype.card_fin] at c1
      omega
  have universal : ∀ (A : Finset W) (L : List (W → Bool)), (fun _ => false) ∈ L → (fun _ => true) ∈ L →
      (∀ f ∈ need, ∀ x ∈ A, ∀ y ∈ A, (∀ g ∈ L, g x = true → g y = true) → f x = true → f y = true) →
      ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.Monotone2 C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack L.length C ∧
        C.output < L.length+C.size ∧ ∀ f ∈ need, ∃ j < L.length+C.size,
          ∀ x ∈ A, (C.wires (L.map (fun g => g x))).getD j false = f x := by
    intro A L hf ht mono
    have f0 := List.idxOf_lt_length_iff.2 hf
    have t0 := List.idxOf_lt_length_iff.2 ht
    let ord := need.equivFin
    let T : Fin need.card → List (List ℕ) := fun k =>
      (A.toList.filter (fun x => decide ((ord.symm k).1 x = true))).map
        (fun x => (List.range L.length).filter (fun i => (L.map (fun g => g x)).getD i false))
    have bnd : ∀ k, ∀ term ∈ T k, ∀ i ∈ term, i < L.length := by
      intro k term hterm i hi
      obtain ⟨x, -, rfl⟩ := List.mem_map.1 hterm
      exact List.mem_range.1 (List.mem_filter.1 hi).1
    have ok0 : PEqualNP.Outside.L_meta_53209.Ok L.length [] := ⟨by simp, by simp⟩
    obtain ⟨g, o, ext, ho, hv⟩ := PEqualNP.Outside.L_meta_53209.build_many (n := L.length) _ _ f0 t0 need.card T bnd [] ok0
    have f1 := List.idxOf_lt_length_iff.2 hf
    refine ⟨⟨g, L.idxOf (fun _ => false)⟩, ?_, PEqualNP.Outside.L_meta_53209.reads_of_ok' ext.1 _, ?_, ?_⟩
    · intro h hh
      have := ext.1.1 h hh
      exact ⟨by simpa using this.1, this.2⟩
    · show L.idxOf (fun _ => false) < L.length + g.length
      omega
    · intro f hfn
      refine ⟨o (ord ⟨f, hfn⟩), ho _, fun y hy => ?_⟩
      have len : (L.map (fun g => g y)).length = L.length := List.length_map _
      have e0 := (PEqualNP.Outside.L_meta_53209.wire_of L _ hf y).2
      have e1 := (PEqualNP.Outside.L_meta_53209.wire_of L _ ht y).2
      have key := hv _ len e0 e1 (ord ⟨f, hfn⟩)
      change PEqualNP.Outside.L_meta_53209.val (L.map (fun g => g y)) g (o (ord ⟨f, hfn⟩)) = f y
      rw [key, Bool.eq_iff_iff]
      unfold PEqualNP.Outside.L_meta_53209.dnf
      rw [List.any_eq_true]
      simp only [T, Equiv.symm_apply_apply]
      constructor
      · rintro ⟨term, hterm, hall⟩
        obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hterm
        obtain ⟨hxA, hfx⟩ := List.mem_filter.1 hx
        refine mono f hfn x (Finset.mem_toList.1 hxA) y hy (fun h hh hx1 => ?_) (of_decide_eq_true hfx)
        have wx := PEqualNP.Outside.L_meta_53209.wire_of L h hh x
        have wy := PEqualNP.Outside.L_meta_53209.wire_of L h hh y
        have := List.all_eq_true.1 hall (L.idxOf h) (List.mem_filter.2 ⟨List.mem_range.2 wx.1, by rw [wx.2]; exact hx1⟩)
        rw [wy.2] at this
        exact this
      · intro hfy
        refine ⟨_, List.mem_map.2 ⟨y, List.mem_filter.2 ⟨Finset.mem_toList.2 hy, decide_eq_true hfy⟩, rfl⟩, ?_⟩
        exact List.all_eq_true.2 (fun i hi => (List.mem_filter.1 hi).2)
  have good : ∀ A : Finset W, keeps A →
      ((∅ : Finset (Fin n)) ∈ A ∧ (Finset.univ : Finset (Fin n)) ∈ A) ∧
      (∀ e ∈ E, ∀ k : Fin 3, ∀ g : W → Bool,
        (g ∈ raw ∨ ∃ e' ∈ E, ∃ k' : Fin 3, (e', k') ≠ (e, k) ∧
          g = ![fun x => neg e'.1 x && neg e'.2 x, fun x => bit e'.1 x && neg e'.2 x, fun x => neg e'.1 x && bit e'.2 x] k') →
        ∃ x ∈ A, (![fun x => neg e.1 x && neg e.2 x, fun x => bit e.1 x && neg e.2 x, fun x => neg e.1 x && bit e.2 x] k) x ≠ g x) := by
    intro A hk
    constructor
    · by_contra hno
      let L := (raw ∪ (∅ : Finset (Fin n)).image neg).toList
      have mem : ∀ g, g ∈ raw → g ∈ L := fun g h => Finset.mem_toList.2 (Finset.mem_union.2 (Or.inl h))
      obtain ⟨C0, c1, c2, c3, c4⟩ := universal A L (mem _ rawF) (mem _ rawT) (by
        intro f _ x hx y hy hle hfx
        have hbit : ∀ i : Fin n, i ∈ (x : Finset (Fin n)) → i ∈ (y : Finset (Fin n)) := by
          intro i hi
          exact (bitT i y).1 (hle _ (mem _ (rawB i)) ((bitT i x).2 hi))
        have closed : ∀ e ∈ E, e.1 ∈ (y : Finset (Fin n)) \ x ↔ e.2 ∈ (y : Finset (Fin n)) \ x := by
          intro e he
          have m1 : same e ∈ raw :=
            Finset.mem_union.2 (Or.inl (Finset.mem_union.2 (Or.inr (Finset.mem_image.2 ⟨e, he, rfl⟩))))
          have m2 : (fun x => !(same e x)) ∈ raw :=
            Finset.mem_union.2 (Or.inr (Finset.mem_image.2 ⟨e, he, rfl⟩))
          have hs : same e x = same e y := by
            have a := hle _ (mem _ m1)
            have b := hle _ (mem _ m2)
            cases h1 : same e x
            · rw [h1] at b
              simp only [Bool.not_false, true_implies, Bool.not_eq_true'] at b
              exact b.symm
            · exact (a h1).symm
          have k : ∀ z : W, same e z = true ↔ (e.1 ∈ (z : Finset (Fin n)) ↔ e.2 ∈ (z : Finset (Fin n))) := by
            intro z
            simp only [same, beq_iff_eq]
            rw [Bool.eq_iff_iff, bitT, bitT]
          have s' : (e.1 ∈ (x : Finset (Fin n)) ↔ e.2 ∈ (x : Finset (Fin n))) ↔
              (e.1 ∈ (y : Finset (Fin n)) ↔ e.2 ∈ (y : Finset (Fin n))) := by
            rw [← k x, ← k y, hs]
          have a := hbit e.1
          have b := hbit e.2
          have m : ∀ i, i ∈ (y : Finset (Fin n)) \ x ↔ i ∈ (y : Finset (Fin n)) ∧ i ∉ (x : Finset (Fin n)) := fun i => Finset.mem_sdiff
          rw [m, m]
          clear k hs
          tauto
        have yx : y = x := by
          rcases hconn _ closed with h | h
          · refine Finset.Subset.antisymm (fun i hi => ?_) (fun i hi => hbit i hi)
            by_contra hix
            have : i ∈ (y : Finset (Fin n)) \ x := Finset.mem_sdiff.2 ⟨hi, hix⟩
            rw [h] at this
            exact Finset.notMem_empty _ this
          · exfalso
            have full : ∀ i : Fin n, i ∈ (y : Finset (Fin n)) \ x := fun i => by rw [h]; exact Finset.mem_univ i
            have x0 : (x : Finset (Fin n)) = ∅ :=
              Finset.eq_empty_of_forall_notMem (fun i => (Finset.mem_sdiff.1 (full i)).2)
            have y1 : (y : Finset (Fin n)) = Finset.univ :=
              Finset.eq_univ_of_forall (fun i => (Finset.mem_sdiff.1 (full i)).1)
            apply hno
            constructor
            · rw [← x0]; exact hx
            · rw [← y1]; exact hy
        rw [yx]; exact hfx)
      have res := (hk ∅ C0.size).1 ⟨C0, c1, c2, c3, le_rfl, c4⟩
      exact Finset.not_nonempty_empty res.1
    · intro e he k g hg
      let atom : (Fin n × Fin n) × Fin 3 → (W → Bool) := fun q =>
        ![fun x => neg q.1.1 x && neg q.1.2 x, fun x => bit q.1.1 x && neg q.1.2 x, fun x => neg q.1.1 x && bit q.1.2 x] q.2
      let first : (Fin n × Fin n) × Fin 3 → (W → Bool) := fun q => ![neg q.1.1, bit q.1.1, neg q.1.1] q.2
      let second : (Fin n × Fin n) × Fin 3 → (W → Bool) := fun q => ![neg q.1.2, neg q.1.2, bit q.1.2] q.2
      have atomEq : ∀ q x, atom q x = (first q x && second q x) := by
        rintro ⟨e, k⟩ x
        fin_cases k <;> rfl
      let Q := E ×ˢ (Finset.univ : Finset (Fin 3))
      have cardQ : Q.card = 3 * E.card := by simp [Q, mul_comm]
      have noCheap : ∀ q ∈ Q, ∀ g : W → Bool,
          (g ∈ raw ∨ g ∈ Finset.univ.image neg ∨ ∃ q' ∈ Q, q' ≠ q ∧ g = atom q') → ∃ x ∈ A, atom q x ≠ g x := by
        intro q hq g hg
        by_contra hall
        have eqA : ∀ x ∈ A, atom q x = g x := by
          intro x hx
          by_contra h
          exact hall ⟨x, hx, h⟩
        let L := (raw ∪ Finset.univ.image neg).toList
        have mem : ∀ g, g ∈ raw ∨ g ∈ Finset.univ.image neg → g ∈ L := fun g h => Finset.mem_toList.2 (Finset.mem_union.2 h)
        have negL : ∀ i, neg i ∈ L := fun i => mem _ (Or.inr (Finset.mem_image_of_mem _ (Finset.mem_univ _)))
        have bitL : ∀ i, bit i ∈ L := fun i => mem _ (Or.inl (rawB i))
        have firstL : ∀ q', first q' ∈ L := by
          rintro ⟨e, k⟩
          fin_cases k
          · exact negL _
          · exact bitL _
          · exact negL _
        have secondL : ∀ q', second q' ∈ L := by
          rintro ⟨e, k⟩
          fin_cases k
          · exact negL _
          · exact negL _
          · exact bitL _
        let R := (Q.erase q).toList
        let ps : List (ℕ × ℕ) := R.map (fun q' => (L.idxOf (first q'), L.idxOf (second q')))
        let gates : List PEqualNP.CircuitLowerBounds.Gate := ps.map (fun p => ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [p.1, p.2]⟩)
        let C : PEqualNP.CircuitLowerBounds.Circuit := ⟨gates, 0⟩
        have psb : ∀ p ∈ ps, p.1 < L.length ∧ p.2 < L.length := by
          intro p hp
          obtain ⟨q', -, rfl⟩ := List.mem_map.1 hp
          exact ⟨List.idxOf_lt_length_iff.2 (firstL q'), List.idxOf_lt_length_iff.2 (secondL q')⟩
        have size : C.size = 3 * E.card - 1 := by
          show gates.length = _
          simp only [gates, ps, R, List.length_map, Finset.length_toList]
          rw [Finset.card_erase_of_mem hq, cardQ]
        have epos : 0 < E.card := Finset.card_pos.2 hne
        have Lpos : 0 < L.length := lt_of_le_of_lt (Nat.zero_le _) (List.idxOf_lt_length_iff.2 (negL q.1.1))
        have wiresC : ∀ x : W, C.wires (L.map (fun g => g x)) =
            L.map (fun g => g x) ++ ps.map (fun p => (L.map (fun g => g x)).getD p.1 false && (L.map (fun g => g x)).getD p.2 false) := by
          intro x
          refine PEqualNP.Outside.L_meta_53209.and_wires _ ps (fun p hp => ?_)
          rw [List.length_map]
          exact psb p hp
        have atomWire : ∀ q' ∈ Q, q' ≠ q → ∃ j < L.length + C.size, ∀ x : W,
            (C.wires (L.map (fun g => g x))).getD j false = atom q' x := by
          intro q' hq' hne'
          have inR : q' ∈ R := Finset.mem_toList.2 (Finset.mem_erase.2 ⟨hne', hq'⟩)
          have m := List.idxOf_lt_length_iff.2 inR
          refine ⟨L.length + R.idxOf q', ?_, fun x => ?_⟩
          · have : C.size = R.length := by show gates.length = _; simp [gates, ps]
            omega
          · rw [wiresC, List.getD_append_right _ _ _ _ (by rw [List.length_map]; omega), List.length_map,
              Nat.add_sub_cancel_left, List.getD_eq_getElem?_getD]
            simp only [ps, List.map_map, List.getElem?_map, List.getElem?_eq_getElem m, List.getElem_idxOf, Option.map_some,
              Option.getD_some, Function.comp]
            rw [(PEqualNP.Outside.L_meta_53209.wire_of L _ (firstL q') x).2,
              (PEqualNP.Outside.L_meta_53209.wire_of L _ (secondL q') x).2, atomEq]
        have inputWire : ∀ h ∈ L, ∃ j < L.length + C.size, ∀ x : W, (C.wires (L.map (fun g => g x))).getD j false = h x := by
          intro h hh
          have w := List.idxOf_lt_length_iff.2 hh
          refine ⟨L.idxOf h, by omega, fun x => ?_⟩
          rw [wiresC, List.getD_append _ _ _ _ (by rw [List.length_map]; exact w)]
          exact (PEqualNP.Outside.L_meta_53209.wire_of L h hh x).2
        have res := (hk Finset.univ (3 * E.card - 1)).1 (by
          refine ⟨C, ?_, ?_, ?_, size.le, ?_⟩
          · intro h hh
            obtain ⟨p, -, rfl⟩ := List.mem_map.1 hh
            exact ⟨by simp, by simp⟩
          · intro j hj i hi
            have hj' : j < gates.length := hj
            have e : PEqualNP.MetaComplexity.NestedCover.gateAt C j = gates[j] := by
              simp [PEqualNP.MetaComplexity.NestedCover.gateAt, C, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj']
            rw [e] at hi
            have : gates[j] ∈ gates := List.getElem_mem _
            obtain ⟨p, hp, ep⟩ := List.mem_map.1 this
            rw [← ep] at hi
            simp at hi
            have := psb p hp
            change i < L.length + j
            omega
          · show 0 < L.length + C.size
            omega
          · intro f hfn
            have hfn' := hfn
            simp only [need, Finset.mem_union, Finset.mem_image] at hfn'
            have atomCase : ∀ q' ∈ Q, ∃ j < L.length + C.size, ∀ x ∈ A, (C.wires (L.map (fun g => g x))).getD j false = atom q' x := by
              intro q' hq'
              by_cases h : q' = q
              · subst h
                rcases hg with hg | hg | ⟨q2, hq2, hne2, rfl⟩
                · obtain ⟨j, hj, w⟩ := inputWire g (mem _ (Or.inl hg))
                  exact ⟨j, hj, fun x hx => (w x).trans (eqA x hx).symm⟩
                · obtain ⟨j, hj, w⟩ := inputWire g (mem _ (Or.inr hg))
                  exact ⟨j, hj, fun x hx => (w x).trans (eqA x hx).symm⟩
                · obtain ⟨j, hj, w⟩ := atomWire q2 hq2 hne2
                  exact ⟨j, hj, fun x hx => (w x).trans (eqA x hx).symm⟩
              · obtain ⟨j, hj, w⟩ := atomWire q' hq' h
                exact ⟨j, hj, fun x _ => w x⟩
            have inQ : ∀ e ∈ E, ∀ k : Fin 3, (e, k) ∈ Q := fun e he k => Finset.mem_product.2 ⟨he, Finset.mem_univ _⟩
            rcases hfn' with ((⟨i, -, rfl⟩ | ⟨e, he, rfl⟩) | ⟨e, he, rfl⟩) | ⟨e, he, rfl⟩
            · obtain ⟨j, hj, w⟩ := inputWire (neg i) (negL i)
              exact ⟨j, hj, fun x _ => w x⟩
            · exact atomCase (e, 0) (inQ e he 0)
            · exact atomCase (e, 1) (inQ e he 1)
            · exact atomCase (e, 2) (inQ e he 2))
        have := res.2
        rw [Finset.card_univ, Fintype.card_fin] at this
        omega
      have inQ : ∀ e ∈ E, ∀ k : Fin 3, (e, k) ∈ Q := fun e he k => Finset.mem_product.2 ⟨he, Finset.mem_univ _⟩
      refine noCheap (e, k) (inQ e he k) g ?_
      rcases hg with hg | ⟨e', he', k', ne', rfl⟩
      · exact Or.inl hg
      · exact Or.inr (Or.inr ⟨(e', k'), inQ e' he' k', ne', rfl⟩)
  have a1 : ∀ (e : Fin n × Fin n) (x : W), (bit e.1 x && neg e.2 x) = true ↔ e.1 ∈ (x : Finset (Fin n)) ∧ e.2 ∉ (x : Finset (Fin n)) :=
    fun e x => by rw [Bool.and_eq_true, bitT, negT]
  have a2 : ∀ (e : Fin n × Fin n) (x : W), (neg e.1 x && bit e.2 x) = true ↔ e.1 ∉ (x : Finset (Fin n)) ∧ e.2 ∈ (x : Finset (Fin n)) :=
    fun e x => by rw [Bool.and_eq_true, bitT, negT]
  let atom : (Fin n × Fin n) → Fin 3 → (W → Bool) := fun e k =>
    ![fun x => neg e.1 x && neg e.2 x, fun x => bit e.1 x && neg e.2 x, fun x => neg e.1 x && bit e.2 x] k
  have loop : ∀ i j, adj i j → i ≠ j := by
    intro i j h e
    subst e
    rcases h with h | h <;> exact lt_irrefl _ (hE _ h)
  have edge : ∀ u, u ≠ v → ∃ e ∈ E, (e.1 = v ∨ e.2 = v) ∧ (e.1 = u ∨ e.2 = u) ∧
      (∃ k : Fin 3, ∀ x : W, atom e k x = true ↔ v ∈ (x : Finset (Fin n)) ∧ u ∉ (x : Finset (Fin n))) ∧
      (∃ k : Fin 3, ∀ x : W, atom e k x = true ↔ u ∈ (x : Finset (Fin n)) ∧ v ∉ (x : Finset (Fin n))) := by
    intro u hu
    rcases hpiv u hu with h | h
    · refine ⟨(u, v), h, Or.inr rfl, Or.inl rfl, ⟨2, fun x => ?_⟩, ⟨1, fun x => a1 (u, v) x⟩⟩
      show (neg u x && bit v x) = true ↔ _
      rw [a2 (u, v) x]; exact and_comm
    · refine ⟨(v, u), h, Or.inl rfl, Or.inr rfl, ⟨1, fun x => a1 (v, u) x⟩, ⟨2, fun x => ?_⟩⟩
      show (neg v x && bit u x) = true ↔ _
      rw [a2 (v, u) x]; exact and_comm
  -- en cada mitad del pivote, todo par de vertices se separa en al menos D copias
  have core : ∀ (p : Fin n × Fin n), p.1 < p.2 → ∀ (side : Bool) (H : Finset W),
      (∀ x : W, (if side then v ∈ (x : Finset (Fin n)) else v ∉ (x : Finset (Fin n))) →
        ¬ (p.1 ∈ (x : Finset (Fin n)) ↔ p.2 ∈ (x : Finset (Fin n))) → x ∈ H) →
      ∀ T : Finset W, (∀ x : W, x ∈ H → ¬ (p.1 ∈ (x : Finset (Fin n)) ↔ p.2 ∈ (x : Finset (Fin n))) → x ∈ T) →
      D ≤ T.sum w := by
    intro p lt side H hH T hT
    by_contra hc
    let lost : W → ℕ := fun x => if x ∈ T then w x else 0
    have total : (∑ x, lost x) < D := by
      have : (∑ x, lost x) = T.sum w := by
        simp only [lost]
        rw [Finset.sum_ite_mem, Finset.univ_inter]
      omega
    have hk := hval lost total
    obtain ⟨-, cheapOk⟩ := good _ hk
    have absurdRow : ∀ x : W, lost x < w x →
        (if side then v ∈ (x : Finset (Fin n)) else v ∉ (x : Finset (Fin n))) →
        ¬ (p.1 ∈ (x : Finset (Fin n)) ↔ p.2 ∈ (x : Finset (Fin n))) → False := by
      intro x h s d
      have hxT := hT x (hH x s d) d
      simp only [lost, if_pos hxT] at h
      exact lt_irrefl _ h
    have ne12 : p.1 ≠ p.2 := ne_of_lt lt
    by_cases hv : p.1 = v ∨ p.2 = v
    · -- el par contiene al pivote: es una arista
      obtain ⟨u, hu, hpair⟩ : ∃ u, u ≠ v ∧ ∀ x : Finset (Fin n), (¬ (p.1 ∈ x ↔ p.2 ∈ x)) ↔ ¬ (u ∈ x ↔ v ∈ x) := by
        rcases hv with h | h
        · refine ⟨p.2, fun e => ne12 (h.trans e.symm), fun x => ?_⟩
          rw [h]; exact not_congr Iff.comm
        · exact ⟨p.1, fun e => ne12 (e.trans h.symm), fun x => by rw [h]⟩
      obtain ⟨e, eE, -, -, ⟨k1, ek1⟩, ⟨k2, ek2⟩⟩ := edge u hu
      cases side
      · obtain ⟨x, hx, ne⟩ := cheapOk e eE k2 (fun _ => false) (Or.inl rawF)
        have t : atom e k2 x = true := by
          have : atom e k2 x ≠ false := ne
          simpa using this
        have s := (ek2 x).1 t
        exact absurdRow x (PEqualNP.Outside.L_meta_53209.memF.1 hx).2 (by simpa using s.2) ((hpair x).2 (fun h => s.2 (h.1 s.1)))
      · obtain ⟨x, hx, ne⟩ := cheapOk e eE k1 (fun _ => false) (Or.inl rawF)
        have t : atom e k1 x = true := by
          have : atom e k1 x ≠ false := ne
          simpa using this
        have s := (ek1 x).1 t
        exact absurdRow x (PEqualNP.Outside.L_meta_53209.memF.1 hx).2 (by simpa using s.1) ((hpair x).2 (fun h => s.2 (h.2 s.1)))
    · -- el par no contiene al pivote: dos aristas por el pivote
      have n1 : p.1 ≠ v := fun h => hv (Or.inl h)
      have n2 : p.2 ≠ v := fun h => hv (Or.inr h)
      obtain ⟨e, eE, em, eu, ⟨k1, ek1⟩, ⟨k2, ek2⟩⟩ := edge p.1 n1
      obtain ⟨f, fE, fm, fu, ⟨l1, fl1⟩, ⟨l2, fl2⟩⟩ := edge p.2 n2
      have ef : e ≠ f := by
        intro h
        subst h
        rcases em with em | em <;> rcases eu with eu | eu <;> rcases fu with fu | fu
        all_goals first
          | exact ne12 (eu.symm.trans fu)
          | exact n1 (eu.symm.trans em)
          | exact n2 (fu.symm.trans em)
      have diff : ∀ (s t : Bool) (P Q : Prop), (s = true ↔ P) → (t = true ↔ Q) → s ≠ t → ¬ (P ↔ Q) := by
        intro s t P Q hs ht h
        rwa [← hs, ← ht, ← Bool.eq_iff_iff]
      cases side
      · obtain ⟨x, hx, ne⟩ := cheapOk e eE k2 (atom f l2)
          (Or.inr ⟨f, fE, l2, fun h => ef (Prod.mk.inj h).1.symm, rfl⟩)
        have s := PEqualNP.Outside.L_meta_53209.lado2 _ _ _ (diff _ _ _ _ (ek2 x) (fl2 x) ne)
        exact absurdRow x (PEqualNP.Outside.L_meta_53209.memF.1 hx).2 (by simpa using s.1) s.2
      · obtain ⟨x, hx, ne⟩ := cheapOk e eE k1 (atom f l1)
          (Or.inr ⟨f, fE, l1, fun h => ef (Prod.mk.inj h).1.symm, rfl⟩)
        have s := PEqualNP.Outside.L_meta_53209.lado1 _ _ _ (diff _ _ _ _ (ek1 x) (fl1 x) ne)
        exact absurdRow x (PEqualNP.Outside.L_meta_53209.memF.1 hx).2 (by simpa using s.1) s.2
  have memPairs : ∀ p : Fin n × Fin n, p ∈ pairs ↔ p.1 < p.2 := fun p => by
    simp only [pairs, Finset.mem_filter, Finset.mem_univ, true_and]
  have memLo : ∀ x : W, x ∈ lo ↔ x ≠ (∅ : Finset (Fin n)) ∧ v ∉ (x : Finset (Fin n)) := fun x => by
    simp only [lo, Finset.mem_filter, Finset.mem_univ, true_and]
  have memHi : ∀ x : W, x ∈ hi ↔ x ≠ (Finset.univ : Finset (Fin n)) ∧ v ∈ (x : Finset (Fin n)) := fun x => by
    simp only [hi, Finset.mem_filter, Finset.mem_univ, true_and]
  have half : ∃ side : Bool, ∀ x : W, (if side then v ∈ (x : Finset (Fin n)) else v ∉ (x : Finset (Fin n))) →
      (x : Finset (Fin n)) ≠ ∅ → (x : Finset (Fin n)) ≠ Finset.univ → x ∈ F := by
    by_cases h : lo.sum w ≤ hi.sum w
    · refine ⟨false, fun x s n0 _ => ?_⟩
      have : F = lo := by simp only [F]; exact if_pos h
      rw [this, memLo]
      exact ⟨n0, by simpa using s⟩
    · refine ⟨true, fun x s _ n1 => ?_⟩
      have : F = hi := by simp only [F]; exact if_neg h
      rw [this, memHi]
      exact ⟨n1, by simpa using s⟩
  obtain ⟨side, hside⟩ := half
  have lower : ∀ p ∈ pairs, D ≤ dist p := by
    intro p hp
    have lt := (memPairs p).1 hp
    refine core p lt side F (fun x s d => hside x s (fun e => ?_) (fun e => ?_)) _ (fun x hx d => ?_)
    · rw [e] at d
      exact d (iff_of_false (Finset.notMem_empty _) (Finset.notMem_empty _))
    · rw [e] at d
      exact d (iff_of_true (Finset.mem_univ _) (Finset.mem_univ _))
    · exact PEqualNP.Outside.L_meta_53209.memF.2 ⟨hx, d⟩
  have sumSplit : ∑ p ∈ pairs, dist p = extra + pairs.card * D := by
    have : ∑ p ∈ pairs, dist p = ∑ p ∈ pairs, ((dist p - D) + D) :=
      Finset.sum_congr rfl (fun p hp => (Nat.sub_add_cancel (lower p hp)).symm)
    rw [this, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul]
  refine ⟨lower, ?_, ?_⟩
  · rw [← sumSplit]
    have swap : ∑ p ∈ pairs, dist p = ∑ x ∈ F, w x * (pairs.filter (fun p => ¬ (p.1 ∈ (x : Finset (Fin n)) ↔ p.2 ∈ (x : Finset (Fin n))))).card := by
      simp only [dist, Finset.sum_filter]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [Finset.card_filter, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun p _ => ?_)
      split_ifs <;> omega
    rw [swap, Finset.sum_mul]
    refine Finset.sum_le_sum (fun x _ => Nat.mul_le_mul_left _ ?_)
    set Z : Finset (Fin n) := x with hZ
    have sub : pairs.filter (fun p => ¬ (p.1 ∈ Z ↔ p.2 ∈ Z)) ⊆
        (Z ×ˢ Zᶜ).image (fun q => if q.1 < q.2 then q else (q.2, q.1)) := by
      intro p hp
      obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hp
      have lt := (memPairs p).1 h1
      by_cases m : p.1 ∈ Z
      · have m2 : p.2 ∉ Z := fun h => h2 (iff_of_true m h)
        exact Finset.mem_image.2 ⟨p, Finset.mem_product.2 ⟨m, Finset.mem_compl.2 m2⟩, if_pos lt⟩
      · have m2 : p.2 ∈ Z := by
          by_contra h
          exact h2 (iff_of_false m h)
        exact Finset.mem_image.2 ⟨(p.2, p.1), Finset.mem_product.2 ⟨m2, Finset.mem_compl.2 m⟩, if_neg (not_lt.2 lt.le)⟩
    refine (Finset.card_le_card sub).trans (Finset.card_image_le.trans ?_)
    rw [Finset.card_product, Finset.card_compl, Fintype.card_fin]
    have le : Z.card ≤ n := by simpa using Finset.card_le_univ Z
    exact PEqualNP.Outside.L_meta_53209.medio _ _ le
  · intro e f he hf hef
    set L := F.sum (fun x => w x * ((count e x - count f x) + (count f x - count e x))) with hL
    have big : ∀ p : Fin n × Fin n, p.1 < p.2 →
        (∀ x : Finset (Fin n), ¬ (p.1 ∈ x ↔ p.2 ∈ x) → 1 ≤ (count e x - count f x) + (count f x - count e x)) → D ≤ L := by
      intro p lt point
      have h1 := lower p ((memPairs p).2 lt)
      refine h1.trans ?_
      simp only [dist, Finset.sum_filter, hL]
      refine Finset.sum_le_sum (fun x _ => ?_)
      split_ifs <;> first
        | exact Nat.zero_le _
        | exact Nat.le_mul_of_pos_right _ (point x (by assumption))
    have bigU : ∀ a b : Fin n, a ≠ b →
        (∀ x : Finset (Fin n), ¬ (a ∈ x ↔ b ∈ x) → 1 ≤ (count e x - count f x) + (count f x - count e x)) → D ≤ L := by
      intro a b ne point
      rcases lt_or_gt_of_ne ne with h | h
      · exact big (a, b) h point
      · exact big (b, a) h (fun x d => point x (fun i => d i.symm))
    have cnt : ∀ (g : Fin n × Fin n) (x : Finset (Fin n)),
        count g x = (if g.1 ∈ x then 1 else 0) + (if g.2 ∈ x then 1 else 0) := fun g x => by
      simp only [count]
      congr
    have easy : (e.1 = e.2 ∨ f.1 = f.2 ∨ e.1 = f.1 ∨ e.1 = f.2 ∨ e.2 = f.1 ∨ e.2 = f.2) → D ≤ L := by
      intro h
      obtain ⟨a, b⟩ := e
      obtain ⟨c, d⟩ := f
      simp only at h he hf hef
      -- un vertice comun: la diferencia es la de los otros dos
      have share : ∀ s y z : Fin n, (∀ x : Finset (Fin n), count (a, b) x = (if s ∈ x then 1 else 0) + (if y ∈ x then 1 else 0)) →
          (∀ x : Finset (Fin n), count (c, d) x = (if s ∈ x then 1 else 0) + (if z ∈ x then 1 else 0)) → y ≠ z → D ≤ L := by
        intro s y z h1 h2 ne
        refine bigU y z ne (fun x dif => ?_)
        rw [h1, h2]
        exact PEqualNP.Outside.L_meta_53209.comun _ _ _ dif
      have ca : ∀ x : Finset (Fin n), count (a, b) x = (if a ∈ x then 1 else 0) + (if b ∈ x then 1 else 0) := fun x => cnt _ x
      have cb : ∀ x : Finset (Fin n), count (a, b) x = (if b ∈ x then 1 else 0) + (if a ∈ x then 1 else 0) := fun x => by
        rw [ca, add_comm]
      have cc : ∀ x : Finset (Fin n), count (c, d) x = (if c ∈ x then 1 else 0) + (if d ∈ x then 1 else 0) := fun x => cnt _ x
      have cd : ∀ x : Finset (Fin n), count (c, d) x = (if d ∈ x then 1 else 0) + (if c ∈ x then 1 else 0) := fun x => by
        rw [cc, add_comm]
      by_cases s1 : a = c
      · refine share a b d ca (fun x => by rw [cc, s1]) (fun h => hef ?_)
        rw [s1, h]
      by_cases s2 : a = d
      · refine share a b c ca (fun x => by rw [cd, s2]) (fun h => hef ?_)
        have e1 : c ≤ d := hf
        have e2 : a ≤ b := he
        have : a = c := le_antisymm (by rw [← h]; exact e2) (by rw [s2]; exact e1)
        exact absurd this s1
      by_cases s3 : b = c
      · refine share b a d cb (fun x => by rw [cc, s3]) (fun h => ?_)
        exact s2 h
      by_cases s4 : b = d
      · refine share b a c cb (fun x => by rw [cd, s4]) (fun h => ?_)
        exact s1 h
      -- sin vertices comunes: uno de los dos pares es un vertice repetido
      rcases h with h | h | h | h | h | h
      · by_cases q : c = d
        · refine bigU a c s1 (fun x dif => ?_)
          rw [ca, cc, ← h, ← q]
          exact PEqualNP.Outside.L_meta_53209.dobles _ _ dif
        · refine bigU c d q (fun x dif => ?_)
          rw [ca, cc, ← h]
          exact PEqualNP.Outside.L_meta_53209.doble _ _ _ dif
      · by_cases q : a = b
        · refine bigU a c s1 (fun x dif => ?_)
          rw [ca, cc, ← h, ← q]
          exact PEqualNP.Outside.L_meta_53209.dobles _ _ dif
        · refine bigU a b q (fun x dif => ?_)
          rw [ca, cc, ← h]
          exact PEqualNP.Outside.L_meta_53209.doble' _ _ _ dif
      · exact absurd h s1
      · exact absurd h s2
      · exact absurd h s3
      · exact absurd h s4
    by_cases h : (e.1 = e.2 ∨ f.1 = f.2 ∨ e.1 = f.1 ∨ e.1 = f.2 ∨ e.2 = f.1 ∨ e.2 = f.2)
    · have := easy h
      omega
    · simp only [not_or] at h
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
      have e12 : e.1 < e.2 := lt_of_le_of_ne he h1
      have f12 : f.1 < f.2 := lt_of_le_of_ne hf h2
      -- cuatro vertices distintos: desigualdad del paralelogramo
      have dU : ∀ a b : Fin n, a ≠ b → D ≤ dist (a, b) := by
        intro a b ne
        rcases lt_or_gt_of_ne ne with h | h
        · exact lower (a, b) ((memPairs _).2 h)
        · refine (lower (b, a) ((memPairs _).2 h)).trans (le_of_eq ?_)
          simp only [dist]
          refine Finset.sum_congr (Finset.ext fun x => ?_) (fun _ _ => rfl)
          rw [PEqualNP.Outside.L_meta_53209.memF, PEqualNP.Outside.L_meta_53209.memF]
          exact and_congr_right fun _ => not_congr Iff.comm
      have par : ∀ a b c d : Fin n, dist (a, c) + dist (a, d) + dist (b, c) + dist (b, d) ≤ dist (a, b) + dist (c, d) +
          2 * F.sum (fun x => w x * ((count (a, b) x - count (c, d) x) + (count (c, d) x - count (a, b) x))) := by
        intro a b c d
        simp only [dist, Finset.sum_filter, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_le_sum (fun x _ => ?_)
        rw [cnt, cnt]
        exact PEqualNP.Outside.L_meta_53209.paralelo _ _ _ _ _
      have p := par e.1 e.2 f.1 f.2
      have q1 := dU e.1 f.1 h3
      have q2 := dU e.1 f.2 h4
      have q3 := dU e.2 f.1 h5
      have q4 := dU e.2 f.2 h6
      have x1 : dist e - D ≤ extra - (dist f - D) ∧ dist f - D ≤ extra := by
        have eP : e ∈ pairs := (memPairs e).2 e12
        have fP : f ∈ pairs := (memPairs f).2 f12
        have two : ({e, f} : Finset (Fin n × Fin n)) ⊆ pairs := by
          intro g hg
          rcases Finset.mem_insert.1 hg with h | h
          · rw [h]; exact eP
          · rw [Finset.mem_singleton.1 h]; exact fP
        have s := Finset.sum_le_sum_of_subset (f := fun p => dist p - D) two
        rw [Finset.sum_pair hef] at s
        change (dist e - D) + (dist f - D) ≤ extra at s
        omega
      have de := lower e ((memPairs e).2 e12)
      have df := lower f ((memPairs f).2 f12)
      change _ ≤ dist e + dist f + 2 * L at p
      omega
