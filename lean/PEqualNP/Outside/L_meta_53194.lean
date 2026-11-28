import PEqualNP.Defs
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

namespace PEqualNP.Outside.L_meta_53194

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

end PEqualNP.Outside.L_meta_53194

theorem PEqualNP.Outside.L_meta_53194 : ∀ (n c : Nat) (E : Finset (Fin n × Fin n)) (color : Fin n → Fin c),
  (∀ e ∈ E, e.1 < e.2) → Function.Surjective color →
  (∀ Z : Finset (Fin n), (∀ e ∈ E, e.1 ∈ Z ↔ e.2 ∈ Z) ↔
    ∀ i j, color i = color j → (i ∈ Z ↔ j ∈ Z)) →
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
    (∀ j, ∃ i ∈ S, color i = j) ∧ n+3*E.card-S.card ≤ p
  ∀ A : Finset W, keeps A → ∀ v : Fin n,
    let d := (E.filter (fun e => e.1 = v ∨ e.2 = v)).card
    0 < d → c+1 ≤ A.card ∧ d < 2^((A.card-c-1)/2) := by
  intro n c E color hE hsurj hcomp
  intro W bit neg same raw need keeps A hk v d hd
  have hne : E.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    simp [d, h] at hd
  letI dec : DecidableEq (W → Bool) := fun a b => Classical.propDecidable (a = b)
  have bitT : ∀ i x, bit i x = true ↔ i ∈ x := fun i x => by simp [bit]
  have negT : ∀ i x, neg i x = true ↔ i ∉ x := fun i x => by simp [neg, bit]
  -- las aristas unen vertices del mismo color
  have edgeColor : ∀ e ∈ E, color e.1 = color e.2 := by
    intro e he
    have := (hcomp (Finset.univ.filter (fun i => color i = color e.1))).2 (fun i j h => by simp [h]) e he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, true_iff] at this
    exact this.symm
  have rawF : (fun _ => false : W → Bool) ∈ raw :=
    Finset.mem_union.2 (Or.inl (Finset.mem_union.2 (Or.inl (Finset.mem_union.2 (Or.inl (Finset.mem_insert_self _ _))))))
  have rawT : (fun _ => true : W → Bool) ∈ raw :=
    Finset.mem_union.2 (Or.inl (Finset.mem_union.2 (Or.inl (Finset.mem_union.2 (Or.inl
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))))))
  have rawB : ∀ i, bit i ∈ raw := fun i =>
    Finset.mem_union.2 (Or.inl (Finset.mem_union.2 (Or.inl (Finset.mem_union.2 (Or.inr
      (Finset.mem_image_of_mem _ (Finset.mem_univ _)))))))
  -- construccion generica: si cada salida pedida es monotona en las entradas, hay circuito
  have universal : ∀ L : List (W → Bool), (fun _ => false) ∈ L → (fun _ => true) ∈ L →
      (∀ f ∈ need, ∀ x ∈ A, ∀ y ∈ A, (∀ g ∈ L, g x = true → g y = true) → f x = true → f y = true) →
      ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.Monotone2 C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack L.length C ∧
        C.output < L.length+C.size ∧ ∀ f ∈ need, ∃ j < L.length+C.size,
          ∀ x ∈ A, (C.wires (L.map (fun g => g x))).getD j false = f x := by
    intro L hf ht mono
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
    have ok0 : PEqualNP.Outside.L_meta_53194.Ok L.length [] := ⟨by simp, by simp⟩
    obtain ⟨g, o, ext, ho, hv⟩ := PEqualNP.Outside.L_meta_53194.build_many (n := L.length) _ _ f0 t0 need.card T bnd [] ok0
    have f1 := List.idxOf_lt_length_iff.2 hf
    refine ⟨⟨g, L.idxOf (fun _ => false)⟩, ?_, PEqualNP.Outside.L_meta_53194.reads_of_ok' ext.1 _, ?_, ?_⟩
    · intro h hh
      have := ext.1.1 h hh
      exact ⟨by simpa using this.1, this.2⟩
    · show L.idxOf (fun _ => false) < L.length + g.length
      omega
    · intro f hfn
      refine ⟨o (ord ⟨f, hfn⟩), ho _, fun y hy => ?_⟩
      have len : (L.map (fun g => g y)).length = L.length := List.length_map _
      have e0 := (PEqualNP.Outside.L_meta_53194.wire_of L _ hf y).2
      have e1 := (PEqualNP.Outside.L_meta_53194.wire_of L _ ht y).2
      have key := hv _ len e0 e1 (ord ⟨f, hfn⟩)
      change PEqualNP.Outside.L_meta_53194.val (L.map (fun g => g y)) g (o (ord ⟨f, hfn⟩)) = f y
      rw [key, Bool.eq_iff_iff]
      unfold PEqualNP.Outside.L_meta_53194.dnf
      rw [List.any_eq_true]
      simp only [T, Equiv.symm_apply_apply]
      constructor
      · rintro ⟨term, hterm, hall⟩
        obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hterm
        obtain ⟨hxA, hfx⟩ := List.mem_filter.1 hx
        refine mono f hfn x (Finset.mem_toList.1 hxA) y hy (fun h hh hx1 => ?_) (of_decide_eq_true hfx)
        have wx := PEqualNP.Outside.L_meta_53194.wire_of L h hh x
        have wy := PEqualNP.Outside.L_meta_53194.wire_of L h hh y
        have := List.all_eq_true.1 hall (L.idxOf h) (List.mem_filter.2 ⟨List.mem_range.2 wx.1, by rw [wx.2]; exact hx1⟩)
        rw [wy.2] at this
        exact this
      · intro hfy
        refine ⟨_, List.mem_map.2 ⟨y, List.mem_filter.2 ⟨Finset.mem_toList.2 hy, decide_eq_true hfy⟩, rfl⟩, ?_⟩
        exact List.all_eq_true.2 (fun i hi => (List.mem_filter.1 hi).2)
  have cpos : E.Nonempty := hne
  -- (1) cada componente se voltea entre dos asignaciones de la muestra
  have flip : ∀ j : Fin c, ∃ x ∈ A, Disjoint x (Finset.univ.filter (fun i => color i = j)) ∧
      x ∪ Finset.univ.filter (fun i => color i = j) ∈ A := by
    intro j
    by_contra hno
    set K := Finset.univ.filter (fun i => color i = j) with hK
    set S : Finset (Fin n) := Finset.univ.filter (fun i => color i ≠ j) with hS
    let L := (raw ∪ S.image neg).toList
    have mem : ∀ g, g ∈ raw ∨ g ∈ S.image neg → g ∈ L := fun g h => Finset.mem_toList.2 (Finset.mem_union.2 h)
    have hf : (fun _ => false : W → Bool) ∈ raw := rawF
    have ht : (fun _ => true : W → Bool) ∈ raw := rawT
    obtain ⟨C, c1, c2, c3, c4⟩ := universal L (mem _ (Or.inl hf)) (mem _ (Or.inl ht)) (by
      intro f hfn x hx y hy hle hfx
      have hbit : ∀ i, i ∈ x → i ∈ y := by
        intro i hi
        have m : bit i ∈ raw := rawB i
        exact (bitT i y).1 (hle _ (mem _ (Or.inl m)) ((bitT i x).2 hi))
      have hsame : ∀ e ∈ E, same e x = same e y := by
        intro e he
        have m1 : same e ∈ raw :=
          Finset.mem_union.2 (Or.inl (Finset.mem_union.2 (Or.inr (Finset.mem_image.2 ⟨e, he, rfl⟩))))
        have m2 : (fun x => !(same e x)) ∈ raw :=
          Finset.mem_union.2 (Or.inr (Finset.mem_image.2 ⟨e, he, rfl⟩))
        have a := hle _ (mem _ (Or.inl m1))
        have b := hle _ (mem _ (Or.inl m2))
        cases h1 : same e x
        · rw [h1] at b
          simp only [Bool.not_false, true_implies, Bool.not_eq_true'] at b
          exact b.symm
        · exact (a h1).symm
      have hS' : ∀ i, color i ≠ j → i ∈ y → i ∈ x := by
        intro i hi hy'
        by_contra hx'
        have m : neg i ∈ S.image neg := Finset.mem_image.2 ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩, rfl⟩
        exact (negT i y).1 (hle _ (mem _ (Or.inr m)) ((negT i x).2 hx')) hy'
      have closed : ∀ e ∈ E, e.1 ∈ y \ x ↔ e.2 ∈ y \ x := by
        intro e he
        have k : ∀ z : W, same e z = true ↔ (e.1 ∈ z ↔ e.2 ∈ z) := by
          intro z
          simp only [same, beq_iff_eq]
          rw [Bool.eq_iff_iff, bitT, bitT]
        have s' : (e.1 ∈ x ↔ e.2 ∈ x) ↔ (e.1 ∈ y ↔ e.2 ∈ y) := by
          rw [← k x, ← k y, hsame e he]
        have a := hbit e.1
        have b := hbit e.2
        have m : ∀ i, i ∈ y \ x ↔ i ∈ y ∧ i ∉ x := fun i => Finset.mem_sdiff
        rw [m, m]
        clear k hsame
        tauto
      have inv := (hcomp (y \ x)).1 closed
      have yx : y = x := by
        by_contra hne'
        have : (y \ x).Nonempty := by
          rw [Finset.sdiff_nonempty]
          intro sub
          exact hne' (Finset.Subset.antisymm sub (fun i hi => hbit i hi))
        obtain ⟨i, hi⟩ := this
        have ci : color i = j := by
          by_contra h
          obtain ⟨h1, h2⟩ := Finset.mem_sdiff.1 hi
          exact h2 (hS' i h h1)
        have all : ∀ i', color i' = j → i' ∈ y \ x := fun i' h => (inv i i' (ci.trans h.symm)).1 hi
        apply hno
        refine ⟨x, hx, ?_, ?_⟩
        · rw [Finset.disjoint_right]
          intro i' h
          exact (Finset.mem_sdiff.1 (all i' (Finset.mem_filter.1 h).2)).2
        · have : x ∪ K = y := by
            ext i'
            constructor
            · intro h
              rcases Finset.mem_union.1 h with h | h
              · exact hbit i' h
              · exact (Finset.mem_sdiff.1 (all i' (Finset.mem_filter.1 h).2)).1
            · intro h
              refine Finset.mem_union.2 ?_
              by_cases hx' : i' ∈ x
              · exact Or.inl hx'
              · right
                refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
                by_contra hc'
                exact hx' (hS' i' hc' h)
          rw [this]; exact hy
      rw [yx]; exact hfx)
    have res := (hk S C.size).1 ⟨C, c1, c2, c3, le_rfl, c4⟩
    obtain ⟨i, hi, hci⟩ := res.1 j
    exact (Finset.mem_filter.1 hi).2 hci
  -- (2) los 3e atomos son distintos entre si y de las entradas, sobre la muestra
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
      refine PEqualNP.Outside.L_meta_53194.and_wires _ ps (fun p hp => ?_)
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
        rw [(PEqualNP.Outside.L_meta_53194.wire_of L _ (firstL q') x).2,
          (PEqualNP.Outside.L_meta_53194.wire_of L _ (secondL q') x).2, atomEq]
    have inputWire : ∀ h ∈ L, ∃ j < L.length + C.size, ∀ x : W, (C.wires (L.map (fun g => g x))).getD j false = h x := by
      intro h hh
      have w := List.idxOf_lt_length_iff.2 hh
      refine ⟨L.idxOf h, by omega, fun x => ?_⟩
      rw [wiresC, List.getD_append _ _ _ _ (by rw [List.length_map]; exact w)]
      exact (PEqualNP.Outside.L_meta_53194.wire_of L h hh x).2
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
  -- (3) cociente de la muestra por los pares volteados
  choose xj hxj hdis hflip using flip
  let K : Fin c → Finset (Fin n) := fun j => Finset.univ.filter (fun i => color i = j)
  let Rel : Finset (Fin c) → ↥A → ↥A → Prop := fun J a b => ∃ j ∈ J, a.1 = xj j ∧ b.1 = xj j ∪ K j
  let ψ : Finset (Fin c) → Finset (Fin n) → Finset (Fin n) := fun J x => x.filter (fun i => color i ∉ J)
  have psiInv : ∀ J a b, Rel J a b → ψ J a.1 = ψ J b.1 := by
    rintro J a b ⟨j, hj, h1, h2⟩
    rw [h1, h2]
    ext i
    show i ∈ (xj j).filter (fun i => color i ∉ J) ↔ i ∈ (xj j ∪ K j).filter (fun i => color i ∉ J)
    rw [Finset.mem_filter, Finset.mem_filter]
    constructor
    · rintro ⟨h, hc'⟩; exact ⟨Finset.mem_union.2 (Or.inl h), hc'⟩
    · rintro ⟨h, hc'⟩
      rcases Finset.mem_union.1 h with h | h
      · exact ⟨h, hc'⟩
      · exact absurd ((Finset.mem_filter.1 h).2.symm ▸ hj) hc'
  have count : ∀ J : Finset (Fin c), Nat.card (Quot (Rel J)) + J.card ≤ A.card := by
    intro J
    induction J using Finset.induction with
    | empty =>
      have : Nat.card (Quot (Rel ∅)) ≤ Nat.card ↥A :=
        Nat.card_le_card_of_surjective (Quot.mk (Rel ∅)) Quot.mk_surjective
      simpa using this
    | insert k J hkJ ih =>
      let φ : Quot (Rel J) → Quot (Rel (insert k J)) :=
        Quot.map id (fun a b ⟨j, hj, h⟩ => ⟨j, Finset.mem_insert_of_mem hj, h⟩)
      have surj : Function.Surjective φ := by
        intro q
        obtain ⟨a, rfl⟩ := Quot.mk_surjective q
        exact ⟨Quot.mk _ a, rfl⟩
      have notinj : ¬ Function.Injective φ := by
        intro inj
        let a : ↥A := ⟨xj k, hxj k⟩
        let b : ↥A := ⟨xj k ∪ K k, hflip k⟩
        have e : φ (Quot.mk _ a) = φ (Quot.mk _ b) :=
          Quot.sound ⟨k, Finset.mem_insert_self _ _, rfl, rfl⟩
        have e' := inj e
        have := congrArg (Quot.lift (fun a : ↥A => ψ J a.1) (psiInv J)) e'
        change ψ J (xj k) = ψ J (xj k ∪ K k) at this
        obtain ⟨i, hi⟩ := hsurj k
        have h2 : i ∈ ψ J (xj k ∪ K k) := by
          refine Finset.mem_filter.2 ⟨Finset.mem_union_right _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩), ?_⟩
          rw [hi]; exact hkJ
        rw [← this] at h2
        exact Finset.disjoint_left.1 (hdis k) (Finset.mem_filter.1 h2).1 (Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩)
      have fin1 : Finite (Quot (Rel J)) := Finite.of_surjective _ Quot.mk_surjective
      have fin2 : Finite (Quot (Rel (insert k J))) := Finite.of_surjective _ Quot.mk_surjective
      have lt : Nat.card (Quot (Rel (insert k J))) < Nat.card (Quot (Rel J)) := by
        have i1 := Fintype.ofFinite (Quot (Rel J))
        have i2 := Fintype.ofFinite (Quot (Rel (insert k J)))
        rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
        exact Fintype.card_lt_of_surjective_not_injective φ surj notinj
      rw [Finset.card_insert_of_notMem hkJ]
      omega
  have total := count Finset.univ
  rw [Finset.card_univ, Fintype.card_fin] at total
  have cle : c ≤ A.card := by omega
  have cle1 : c + 1 ≤ A.card := by
    have fin1 : Finite (Quot (Rel Finset.univ)) := Finite.of_surjective _ Quot.mk_surjective
    have ne1 : Nonempty (Quot (Rel Finset.univ)) := ⟨Quot.mk _ ⟨xj (color v), hxj _⟩⟩
    have : 0 < Nat.card (Quot (Rel Finset.univ)) := Nat.card_pos
    omega
  refine ⟨cle1, ?_⟩
  obtain ⟨e0, he0⟩ := hne
  have finQ : Finite (Quot (Rel Finset.univ)) := Finite.of_surjective _ Quot.mk_surjective
  have neQ : Nonempty (Quot (Rel Finset.univ)) := ⟨Quot.mk _ ⟨xj (color e0.1), hxj _⟩⟩
  have surjg : ∃ g : Fin (A.card - c) → Quot (Rel Finset.univ), Function.Surjective g := by
    have i1 := Fintype.ofFinite (Quot (Rel Finset.univ))
    have le : Fintype.card (Quot (Rel Finset.univ)) ≤ Fintype.card (Fin (A.card - c)) := by
      rw [Fintype.card_fin, ← Nat.card_eq_fintype_card]; omega
    obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le le
    exact ⟨Function.invFun f, Function.invFun_surjective f.injective⟩
  obtain ⟨g, hg⟩ := surjg
  have lifts : ∀ (k : Fin 3), k ≠ 0 → ∀ e ∈ E, ∀ a b, Rel Finset.univ a b → atom (e, k) a.1 = atom (e, k) b.1 := by
    rintro k hk0 e he a b ⟨j, -, h1, h2⟩
    have col := edgeColor e he
    have zero : atom (e, k) (xj j) = atom (e, k) (xj j ∪ K j) := by
      have mK : ∀ i, i ∈ K j ↔ color i = j := fun i => by simp [K]
      have nx : ∀ i, color i = j → i ∉ xj j := fun i h hx =>
        Finset.disjoint_left.1 (hdis j) hx ((mK i).2 h)
      have dep : ∀ x y : W, bit e.1 x = bit e.1 y → bit e.2 x = bit e.2 y → atom (e, k) x = atom (e, k) y := by
        intro x y p q
        rw [atomEq, atomEq]
        have n1 : neg e.1 x = neg e.1 y := by show (!(bit e.1 x)) = !(bit e.1 y); rw [p]
        have n2 : neg e.2 x = neg e.2 y := by show (!(bit e.2 x)) = !(bit e.2 y); rw [q]
        fin_cases k
        · show (neg e.1 x && neg e.2 x) = (neg e.1 y && neg e.2 y); rw [n1, n2]
        · show (bit e.1 x && neg e.2 x) = (bit e.1 y && neg e.2 y); rw [p, n2]
        · show (neg e.1 x && bit e.2 x) = (neg e.1 y && bit e.2 y); rw [n1, q]
      by_cases h : color e.1 = j
      · have h' : color e.2 = j := col ▸ h
        have a1 := nx _ h
        have a2 := nx _ h'
        have b1 : e.1 ∈ xj j ∪ K j := Finset.mem_union.2 (Or.inr ((mK _).2 h))
        have b2 : e.2 ∈ xj j ∪ K j := Finset.mem_union.2 (Or.inr ((mK _).2 h'))
        have x1 : bit e.1 (xj j) = false := by rw [← Bool.not_eq_true, bitT]; exact a1
        have x2 : bit e.2 (xj j) = false := by rw [← Bool.not_eq_true, bitT]; exact a2
        have y1 : bit e.1 (xj j ∪ K j) = true := (bitT _ _).2 b1
        have y2 : bit e.2 (xj j ∪ K j) = true := (bitT _ _).2 b2
        rw [atomEq, atomEq]
        fin_cases k
        · exact absurd rfl hk0
        · show (bit e.1 (xj j) && !(bit e.2 (xj j))) = (bit e.1 (xj j ∪ K j) && !(bit e.2 (xj j ∪ K j)))
          rw [x1, x2, y1, y2]; rfl
        · show (!(bit e.1 (xj j)) && bit e.2 (xj j)) = (!(bit e.1 (xj j ∪ K j)) && bit e.2 (xj j ∪ K j))
          rw [x1, x2, y1, y2]; rfl
      · have h' : color e.2 ≠ j := col ▸ h
        have s1 : ∀ i, color i ≠ j → bit i (xj j) = bit i (xj j ∪ K j) := by
          intro i hi
          rw [Bool.eq_iff_iff, bitT, bitT]
          exact ⟨fun hh => Finset.mem_union.2 (Or.inl hh),
            fun hh => (Finset.mem_union.1 hh).resolve_right (fun hk' => hi ((mK _).1 hk'))⟩
        exact dep _ _ (s1 _ h) (s1 _ h')
    rw [h1, h2]; exact zero
  have inQ : ∀ e ∈ E, ∀ k : Fin 3, (e, k) ∈ Q := fun e he k => Finset.mem_product.2 ⟨he, Finset.mem_univ _⟩
  have invar : ∀ e ∈ E, ∀ k : Fin 3, k ≠ 0 → ∀ a b : ↥A, Quot.mk (Rel Finset.univ) a = Quot.mk (Rel Finset.univ) b →
      atom (e, k) a.1 = atom (e, k) b.1 := by
    intro e he k hk0 a b h
    exact congrArg (Quot.lift (fun a : ↥A => atom (e, k) a.1) (lifts k hk0 e he)) h
  let j := color v
  let a0 : ↥A := ⟨xj j, hxj j⟩
  obtain ⟨i0, hi0⟩ := hg (Quot.mk _ a0)
  have repEx : ∀ i, ∃ a : ↥A, Quot.mk (Rel Finset.univ) a = g i ∧ (g i = Quot.mk (Rel Finset.univ) a0 → a = a0) := by
    intro i
    by_cases h : g i = Quot.mk (Rel Finset.univ) a0
    · exact ⟨a0, h.symm, fun _ => rfl⟩
    · obtain ⟨a, ha⟩ := Quot.mk_surjective (g i)
      exact ⟨a, ha, fun h' => absurd h' h⟩
  choose rep hrep hrep0 using repEx
  let S : Finset (Fin (A.card - c)) := Finset.univ.filter (fun i => v ∈ (rep i).1)
  let D : Fin n × Fin n → Fin 3 → Finset (Fin (A.card - c)) := fun e k =>
    Finset.univ.filter (fun i => atom (e, k) (rep i).1 = true)
  have mD : ∀ e k i, i ∈ D e k ↔ atom (e, k) (rep i).1 = true := fun e k i => by
    simp only [D, Finset.mem_filter, Finset.mem_univ, true_and]
  let Ev := E.filter (fun e => e.1 = v ∨ e.2 = v)
  let K1 : Fin n × Fin n → Fin 3 := fun e => if e.1 = v then 1 else 2
  let K2 : Fin n × Fin n → Fin 3 := fun e => if e.1 = v then 2 else 1
  have K1ne : ∀ e, K1 e ≠ 0 := fun e => by
    show (if e.1 = v then (1 : Fin 3) else 2) ≠ 0
    split_ifs <;> decide
  have K2ne : ∀ e, K2 e ≠ 0 := fun e => by
    show (if e.1 = v then (2 : Fin 3) else 1) ≠ 0
    split_ifs <;> decide
  have b1 : ∀ (e : Fin n × Fin n) (x : W), atom (e, 1) x = true → e.1 ∈ x ∧ e.2 ∉ x := fun e x h => by
    change (bit e.1 x && neg e.2 x) = true at h
    rw [Bool.and_eq_true, bitT, negT] at h; exact h
  have b2 : ∀ (e : Fin n × Fin n) (x : W), atom (e, 2) x = true → e.1 ∉ x ∧ e.2 ∈ x := fun e x h => by
    change (neg e.1 x && bit e.2 x) = true at h
    rw [Bool.and_eq_true, negT, bitT] at h; exact h
  have orient : ∀ e ∈ Ev, ∀ x : W, (atom (e, K1 e) x = true → v ∈ x) ∧ (atom (e, K2 e) x = true → v ∉ x) := by
    intro e he x
    obtain ⟨-, hv⟩ := Finset.mem_filter.1 he
    by_cases h : e.1 = v
    · have k1 : K1 e = 1 := if_pos h
      have k2 : K2 e = 2 := if_pos h
      rw [k1, k2]
      exact ⟨fun t => h ▸ (b1 e x t).1, fun t => h ▸ (b2 e x t).1⟩
    · have h2 : e.2 = v := hv.resolve_left h
      have k1 : K1 e = 2 := if_neg h
      have k2 : K2 e = 1 := if_neg h
      rw [k1, k2]
      exact ⟨fun t => h2 ▸ (b2 e x t).2, fun t => h2 ▸ (b1 e x t).2⟩
  have inE : ∀ e ∈ Ev, e ∈ E := fun e he => (Finset.mem_filter.1 he).1
  have zero : ∀ e ∈ Ev, ∀ k : Fin 3, k ≠ 0 → atom (e, k) a0.1 = false := by
    intro e he k hk0
    have hcol : color e.1 = j ∧ color e.2 = j := by
      obtain ⟨heE, hv⟩ := Finset.mem_filter.1 he
      have c12 := edgeColor e heE
      rcases hv with h | h
      · have : color e.1 = j := by rw [h]
        exact ⟨this, c12 ▸ this⟩
      · have : color e.2 = j := by rw [h]
        exact ⟨c12.trans this, this⟩
    have a1' : e.1 ∉ xj j := fun h => Finset.disjoint_left.1 (hdis j) h (Finset.mem_filter.2 ⟨Finset.mem_univ _, hcol.1⟩)
    have a2' : e.2 ∉ xj j := fun h => Finset.disjoint_left.1 (hdis j) h (Finset.mem_filter.2 ⟨Finset.mem_univ _, hcol.2⟩)
    rw [← Bool.not_eq_true]
    intro t
    fin_cases k
    · exact hk0 rfl
    · exact a1' (b1 e _ t).1
    · exact a2' (b2 e _ t).2
  have f0 : (fun _ => false : W → Bool) ∈ raw := rawF
  have nonempty : ∀ e ∈ Ev, ∀ k : Fin 3, k ≠ 0 → (D e k).Nonempty := by
    intro e he k hk0
    obtain ⟨x, hx, h⟩ := noCheap (e, k) (inQ e (inE e he) k) _ (Or.inl f0)
    obtain ⟨i, hi⟩ := hg (Quot.mk _ ⟨x, hx⟩)
    refine ⟨i, (mD e k i).2 ?_⟩
    rw [invar e (inE e he) k hk0 (rep i) ⟨x, hx⟩ ((hrep i).trans hi)]
    simpa using h
  have separate : ∀ e ∈ Ev, ∀ f ∈ Ev, ∀ k l : Fin 3, k ≠ 0 → l ≠ 0 → D e k = D f l → e = f := by
    intro e he f hf k l hk0 hl0 heq
    by_contra hne'
    obtain ⟨x, hx, h⟩ := noCheap (e, k) (inQ e (inE e he) k) (atom (f, l))
      (Or.inr (Or.inr ⟨(f, l), inQ f (inE f hf) l, fun q => hne' (Prod.mk.inj q).1.symm, rfl⟩))
    obtain ⟨i, hi⟩ := hg (Quot.mk _ ⟨x, hx⟩)
    apply h
    have r := (hrep i).trans hi
    have p : atom (e, k) (rep i).1 = atom (e, k) x := invar e (inE e he) k hk0 (rep i) ⟨x, hx⟩ r
    have q : atom (f, l) (rep i).1 = atom (f, l) x := invar f (inE f hf) l hl0 (rep i) ⟨x, hx⟩ r
    rw [← p, ← q, Bool.eq_iff_iff, ← mD, ← mD, heq]
  have bound : ∀ (K : Fin n × Fin n → Fin 3) (T : Finset (Fin (A.card - c))), (∀ e, K e ≠ 0) →
      (∀ e ∈ Ev, D e (K e) ⊆ T) → Ev.card < 2 ^ T.card := by
    intro K T hK hsub
    have inj : Set.InjOn (fun e => D e (K e)) Ev := fun e he f hf h =>
      separate e he f hf (K e) (K f) (hK e) (hK f) h
    have le : (Ev.image (fun e => D e (K e))).card ≤ (T.powerset.erase ∅).card := by
      refine Finset.card_le_card (fun U hU => ?_)
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hU
      exact Finset.mem_erase.2 ⟨(nonempty e he (K e) (hK e)).ne_empty, Finset.mem_powerset.2 (hsub e he)⟩
    rw [Finset.card_image_of_injOn inj, Finset.card_erase_of_mem (Finset.empty_mem_powerset T), Finset.card_powerset] at le
    have : 0 < 2 ^ T.card := Nat.pow_pos (by omega)
    omega
  have i0S : i0 ∈ Sᶜ := by
    rw [Finset.mem_compl]
    intro h
    have hv := (Finset.mem_filter.1 h).2
    rw [hrep0 i0 hi0] at hv
    exact Finset.disjoint_left.1 (hdis j) hv (Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl⟩)
  have s1 : Ev.card < 2 ^ S.card := by
    refine bound K1 S K1ne (fun e he i hi => ?_)
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (orient e he _).1 ((mD _ _ _).1 hi)⟩
  have s2 : Ev.card < 2 ^ (Sᶜ.erase i0).card := by
    refine bound K2 _ K2ne (fun e he i hi => ?_)
    have t := (mD _ _ _).1 hi
    refine Finset.mem_erase.2 ⟨fun h => ?_, Finset.mem_compl.2 (fun hs => ?_)⟩
    · rw [h, hrep0 i0 hi0, zero e he _ (K2ne e)] at t
      exact Bool.false_ne_true t
    · exact (orient e he _).2 t (Finset.mem_filter.1 hs).2
  have sizes : S.card + (Sᶜ.erase i0).card + 1 = A.card - c := by
    rw [Finset.card_erase_of_mem i0S]
    have p : 0 < Sᶜ.card := Finset.card_pos.2 ⟨i0, i0S⟩
    have := Finset.card_add_card_compl S
    rw [Fintype.card_fin] at this
    omega
  have dEv : d = Ev.card := by
    simp only [d, Ev]
    congr
  rw [dEv]
  rcases le_total S.card (Sᶜ.erase i0).card with h | h
  · exact lt_of_lt_of_le s1 (Nat.pow_le_pow_right (by omega) (by omega))
  · exact lt_of_lt_of_le s2 (Nat.pow_le_pow_right (by omega) (by omega))
