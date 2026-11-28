import PEqualNP.Defs
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

namespace PEqualNP.Outside.L_meta_53196

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

/-- 2h sondas cuyas palabras sobre los vertices activos forman un conjunto de Sidon (x, x³ en GF(2^h)). -/
lemma sidon (n h : ℕ) (active : Finset (Fin n)) (hcard : active.card ≤ 2^h) :
    ∃ probe : Fin (2*h) → Finset (Fin n), ∀ u ∈ active, ∀ v ∈ active, ∀ u' ∈ active, ∀ v' ∈ active,
      (∀ j, (if u ∈ probe j then 1 else 0 : ℕ) + (if v ∈ probe j then 1 else 0) =
        (if u' ∈ probe j then 1 else 0) + (if v' ∈ probe j then 1 else 0)) →
      (u = u' ∧ v = v') ∨ (u = v' ∧ v = u') := by
  classical
  rcases Nat.eq_zero_or_pos h with h0 | hpos
  · refine ⟨fun _ => ∅, fun u hu v hv u' hu' v' hv' _ => ?_⟩
    have one : active.card ≤ 1 := by simpa [h0] using hcard
    have eq : ∀ a ∈ active, ∀ b ∈ active, a = b := fun a ha b hb => card_le_one.1 one a ha b hb
    exact Or.inl ⟨eq u hu u' hu', eq v hv v' hv'⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let F := GaloisField 2 h
  have : Finite F := inferInstance
  have : Fintype F := Fintype.ofFinite F
  have cardF : Fintype.card F = 2 ^ h := by
    rw [← Nat.card_eq_fintype_card]; exact GaloisField.card 2 h (by omega)
  obtain ⟨ι⟩ : Nonempty (↥active ↪ F) :=
    Function.Embedding.nonempty_of_card_le (by rw [Fintype.card_coe, cardF]; exact hcard)
  have rank : Module.finrank (ZMod 2) F = h := GaloisField.finrank 2 (by omega)
  let bs : Module.Basis (Fin h) (ZMod 2) F := Module.finBasisOfFinrankEq (ZMod 2) F rank
  let split : Fin (2*h) ≃ Fin h ⊕ Fin h := (finCongr (two_mul h)).trans finSumFinEquiv.symm
  let word : F → Fin h ⊕ Fin h → ZMod 2 := fun x => Sum.elim (fun i => bs.repr x i) (fun i => bs.repr (x^3) i)
  refine ⟨fun j => univ.filter (fun v => ∃ hv : v ∈ active, word (ι ⟨v, hv⟩) (split j) = 1), ?_⟩
  intro u hu v hv u' hu' v' hv' heq
  set a := ι ⟨u, hu⟩ with ha
  set b := ι ⟨v, hv⟩ with hb
  set c := ι ⟨u', hu'⟩ with hc
  set d := ι ⟨v', hv'⟩ with hd
  have mem : ∀ (w : Fin n) (hw : w ∈ active) (j : Fin (2*h)),
      ((if w ∈ univ.filter (fun v => ∃ hv : v ∈ active, word (ι ⟨v, hv⟩) (split j) = 1) then 1 else 0 : ℕ))
        = (word (ι ⟨w, hw⟩) (split j)).val := by
    intro w hw j
    have two : ∀ z : ZMod 2, (if z = 1 then 1 else 0 : ℕ) = z.val := by
      intro z
      fin_cases z <;> rfl
    rw [← two]
    refine if_congr ?_ rfl rfl
    simp only [mem_filter, mem_univ, true_and]
    exact ⟨fun ⟨_, e⟩ => e, fun e => ⟨hw, e⟩⟩
  have sums : ∀ k, (word a k).val + (word b k).val = (word c k).val + (word d k).val := by
    intro k
    have := heq (split.symm k)
    rw [mem u hu, mem v hv, mem u' hu', mem v' hv', Equiv.apply_symm_apply] at this
    exact this
  have mods : ∀ k, word a k + word b k = word c k + word d k := by
    intro k
    have := congrArg (fun m : ℕ => (m : ZMod 2)) (sums k)
    simpa [ZMod.natCast_zmod_val] using this
  have s1 : a + b = c + d := by
    apply bs.repr.injective
    ext i
    simpa [word] using mods (Sum.inl i)
  have s3 : a^3 + b^3 = c^3 + d^3 := by
    apply bs.repr.injective
    ext i
    simpa [word] using mods (Sum.inr i)
  have inj : ∀ (x y : Fin n) (hx : x ∈ active) (hy : y ∈ active), ι ⟨x, hx⟩ = ι ⟨y, hy⟩ → x = y :=
    fun x y hx hy e => congrArg Subtype.val (ι.injective e)
  have : CharP F 2 := inferInstance
  have add0 : ∀ x y : F, x + y = 0 ↔ x = y := fun x y => by
    rw [← CharTwo.sub_eq_add, sub_eq_zero]
  by_cases hab : a = b
  · have cd : c = d := by
      have : c + d = 0 := by rw [← s1, hab]; exact CharTwo.add_self_eq_zero b
      exact (add0 _ _).1 this
    have huv : u = v := inj u v hu hv hab
    have huv' : u' = v' := inj u' v' hu' hv' cd
    have ac : a = c := by
      apply bs.repr.injective
      ext i
      have e := sums (Sum.inl i)
      rw [← hab, ← cd] at e
      have : (word a (Sum.inl i)).val = (word c (Sum.inl i)).val := by omega
      simpa [word] using ZMod.val_injective 2 this
    have : u = u' := inj u u' hu hu' ac
    exact Or.inl ⟨this, by rw [← huv, ← huv', this]⟩
  · have two : (2 : F) = 0 := CharTwo.two_eq_zero
    have prod : (a + b) * ((a + c) * (b + c)) = 0 := by
      have dd : d = a + b + c := by
        linear_combination (-1 : F) * s1 - c * two
      rw [dd] at s3
      linear_combination s3 + (c^3 + 2*((a+b)*((a+c)*(b+c)))) * two
    have sne : a + b ≠ 0 := fun e => hab ((add0 _ _).1 e)
    rcases mul_eq_zero.1 prod with e | e
    · exact absurd e sne
    rcases mul_eq_zero.1 e with e | e
    · have ac : a = c := (add0 _ _).1 e
      have bd : b = d := by
        rw [ac] at s1; exact add_left_cancel s1
      exact Or.inl ⟨inj u u' hu hu' ac, inj v v' hv hv' bd⟩
    · have bc : b = c := (add0 _ _).1 e
      have ad : a = d := by
        rw [bc, add_comm a c] at s1; exact add_left_cancel s1
      exact Or.inr ⟨inj u v' hu hv' ad, inj v u' hv hu' bc⟩

lemma wire_of {α : Type} [DecidableEq (α → Bool)] (L : List (α → Bool)) (g : α → Bool) (hg : g ∈ L) (x : α) :
    L.idxOf g < L.length ∧ (L.map (fun h => h x)).getD (L.idxOf g) false = g x := by
  have lt := List.idxOf_lt_length_iff.2 hg
  refine ⟨lt, ?_⟩
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem lt]
  simp

/-- El circuito de entradas L tiene un cable que calcula f en todas las asignaciones. -/
def Has {α : Type} (L : List (α → Bool)) (g : List Gate) (f : α → Bool) : Prop :=
  ∃ w, w < L.length + g.length ∧ ∀ x : α, val (L.map (fun h => h x)) g w = f x

lemma Has.mono {α : Type} {L : List (α → Bool)} {g g' : List Gate} {f : α → Bool}
    (e : Ext L.length g g') (h : Has L g f) : Has L g' f := by
  obtain ⟨w, hw, hv⟩ := h
  refine ⟨w, by have := e.2.1; omega, fun x => ?_⟩
  rw [e.2.2 _ (List.length_map _) w hw]
  exact hv x

lemma Has.input {α : Type} [DecidableEq (α → Bool)] {L : List (α → Bool)} (g : List Gate) {f : α → Bool}
    (h : f ∈ L) : Has L g f := by
  refine ⟨L.idxOf f, by have := List.idxOf_lt_length_iff.2 h; omega, fun x => ?_⟩
  have w := wire_of L f h x
  rw [val_input _ g _ (by rw [List.length_map]; exact w.1)]
  exact w.2

lemma Has.gate {α : Type} {L : List (α → Bool)} {g : List Gate} (ok : Ok L.length g) (op : GateOp)
    (hop : op = GateOp.and ∨ op = GateOp.or) {a b f : α → Bool} (ha : Has L g a) (hb : Has L g b)
    (hf : ∀ x, op.eval [a x, b x] = f x) :
    ∃ g', Ext L.length g g' ∧ g'.length = g.length + 1 ∧ Has L g' f := by
  obtain ⟨i, hi, vi⟩ := ha
  obtain ⟨j, hj, vj⟩ := hb
  obtain ⟨e, hw, hv⟩ := add_gate ok op hop i j hi hj
  refine ⟨_, e, by simp, L.length + g.length, hw, fun x => ?_⟩
  rw [hv _ (List.length_map _), vi, vj]
  exact hf x

lemma sum_alpha (a b c d : Prop) [Decidable a] [Decidable b] [Decidable c] [Decidable d]
    (p : (¬a ∧ ¬b) ↔ (¬c ∧ ¬d)) (q : (¬¬a ∧ ¬¬b) ↔ (¬¬c ∧ ¬¬d)) :
    (if a then 1 else 0 : ℕ) + (if b then 1 else 0) = (if c then 1 else 0) + (if d then 1 else 0) := by
  by_cases ha : a <;> by_cases hb : b <;> by_cases hc : c <;> by_cases hd : d <;> simp [ha, hb, hc, hd] at p q ⊢

lemma sum_beta (a b c d : Prop) [Decidable a] [Decidable b] [Decidable c] [Decidable d]
    (p : (a ∧ ¬b) ↔ (c ∧ ¬d)) (q : (¬a ∧ ¬¬b) ↔ (¬c ∧ ¬¬d)) :
    (if a then 1 else 0 : ℕ) + (if d then 1 else 0) = (if c then 1 else 0) + (if b then 1 else 0) := by
  by_cases ha : a <;> by_cases hb : b <;> by_cases hc : c <;> by_cases hd : d <;> simp [ha, hb, hc, hd] at p q ⊢

lemma neg_alpha (v a b : Prop) (p : ¬v ↔ (¬a ∧ ¬b)) (q : ¬¬v ↔ (¬¬a ∧ ¬¬b)) : a ↔ b := by
  by_cases hv : v <;> by_cases ha : a <;> by_cases hb : b <;> simp [hv, ha, hb] at p q ⊢

lemma card4 {α : Type} {inst : DecidableEq α} {A B C D : Finset α} {a b c d : ℕ}
    (h1 : A.card ≤ a) (h2 : B.card ≤ b) (h3 : C.card ≤ c) (h4 : D.card ≤ d) :
    (A ∪ B ∪ (C ∪ D)).card ≤ a + b + (c + d) :=
  (Finset.card_union_le _ _).trans (Nat.add_le_add ((Finset.card_union_le _ _).trans (Nat.add_le_add h1 h2))
    ((Finset.card_union_le _ _).trans (Nat.add_le_add h3 h4)))

lemma memU {α : Type} {i : DecidableEq α} {A B : Finset α} {x : α} (h : x ∈ A ∨ x ∈ B) : x ∈ A ∪ B :=
  Finset.mem_union.2 h

lemma memI {α β : Type} {i : DecidableEq β} {s : Finset α} {f : α → β} {a : α} (h : a ∈ s) : f a ∈ s.image f :=
  Finset.mem_image_of_mem f h

lemma memSd {α : Type} {i : DecidableEq α} {s t : Finset α} {x : α} : x ∈ s \ t ↔ x ∈ s ∧ x ∉ t := Finset.mem_sdiff

lemma memF {α : Type} {p : α → Prop} {i : DecidablePred p} {s : Finset α} {x : α} : x ∈ s.filter p ↔ x ∈ s ∧ p x :=
  Finset.mem_filter

end PEqualNP.Outside.L_meta_53196

set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_53196 : ∀ (n h : Nat) (active : Finset (Fin n)), active.card ≤ 2^h →
  letI : ∀ Q : Prop, Decidable Q := Classical.propDecidable
  let W := Finset (Fin n)
  ∃ probe : Fin (2*h) → W,
    ∀ (c : Nat) (E : Finset (Fin n × Fin n)) (color : Fin n → Fin c),
      (∀ e ∈ E, e.1 < e.2 ∧ e.1 ∈ active ∧ e.2 ∈ active) →
      Function.Surjective color →
  (∀ Z : Finset (Fin n), (∀ e ∈ E, e.1 ∈ Z ↔ e.2 ∈ Z) ↔
    ∀ i j, color i = color j → (i ∈ Z ↔ j ∈ Z)) →
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
  let tests := (Finset.univ.image probe ∪
      Finset.univ.image (fun j => Finset.univ \ probe j)) ∪
    ({∅} ∪ Finset.univ.image (fun j : Fin c => Finset.univ.filter (fun i => color i = j)))
  keeps tests ∧ tests.card ≤ c+1+4*h := by
  intro n h active hcard
  intro W
  obtain ⟨probe, sid⟩ := PEqualNP.Outside.L_meta_53196.sidon n h active hcard
  refine ⟨probe, ?_⟩
  intro c E color hE hsurj hcomp bit neg same raw need keeps tests
  letI dec : DecidableEq (W → Bool) := fun a b => Classical.propDecidable (a = b)
  have bitT : ∀ i x, bit i x = true ↔ i ∈ x := fun i x => by simp [bit]
  have bitF : ∀ i x, bit i x = false ↔ i ∉ x := fun i x => by rw [← Bool.not_eq_true, bitT]
  have negT : ∀ i x, neg i x = true ↔ i ∉ x := fun i x => by simp [neg, bitF]
  have negF : ∀ i x, neg i x = false ↔ i ∈ x := fun i x => by simp [neg, bitT]
  have sameT : ∀ e x, same e x = true ↔ (e.1 ∈ x ↔ e.2 ∈ x) := by
    intro e x
    simp only [same, beq_iff_eq]
    rw [Bool.eq_iff_iff, bitT, bitT]
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
  have rawS : ∀ e ∈ E, same e ∈ raw := fun e he =>
    Finset.mem_union.2 (Or.inl (Finset.mem_union.2 (Or.inr (Finset.mem_image.2 ⟨e, he, rfl⟩))))
  have rawD : ∀ e ∈ E, (fun x => !(same e x)) ∈ raw := fun e he =>
    Finset.mem_union.2 (Or.inr (Finset.mem_image.2 ⟨e, he, rfl⟩))
  have tP : ∀ j, probe j ∈ tests := fun j => by
    simp only [tests, Finset.mem_union, Finset.mem_image, Finset.mem_singleton]
    exact Or.inl (Or.inl ⟨j, Finset.mem_univ _, rfl⟩)
  have tC' : ∀ j, ∃ y ∈ tests, ∀ i, i ∈ y ↔ i ∉ probe j := fun j =>
    ⟨_, PEqualNP.Outside.L_meta_53196.memU (Or.inl (PEqualNP.Outside.L_meta_53196.memU (Or.inr
      (PEqualNP.Outside.L_meta_53196.memI (Finset.mem_univ j))))),
      fun i => by rw [PEqualNP.Outside.L_meta_53196.memSd]; exact and_iff_right (Finset.mem_univ i)⟩
  choose co hco mC using tC'
  have t0 : (∅ : Finset (Fin n)) ∈ tests := by
    simp only [tests, Finset.mem_union, Finset.mem_image, Finset.mem_singleton]
    exact Or.inr (Or.inl (by simp))
  have tK' : ∀ j : Fin c, ∃ y ∈ tests, ∀ i, i ∈ y ↔ color i = j := fun j =>
    ⟨_, PEqualNP.Outside.L_meta_53196.memU (Or.inr (PEqualNP.Outside.L_meta_53196.memU (Or.inr
      (PEqualNP.Outside.L_meta_53196.memI (Finset.mem_univ j))))),
      fun i => by rw [PEqualNP.Outside.L_meta_53196.memF]; exact and_iff_right (Finset.mem_univ i)⟩
  choose K tK mK using tK'
  have notIn : ∀ i : Fin n, i ∉ (∅ : Finset (Fin n)) := fun i => Finset.notMem_empty i
  -- atomos
  let atom : (Fin n × Fin n) × Fin 3 → (W → Bool) := fun q =>
    ![fun x => neg q.1.1 x && neg q.1.2 x, fun x => bit q.1.1 x && neg q.1.2 x, fun x => neg q.1.1 x && bit q.1.2 x] q.2
  have a0 : ∀ e x, atom (e, 0) x = true ↔ e.1 ∉ x ∧ e.2 ∉ x := fun e x => by
    show (neg e.1 x && neg e.2 x) = true ↔ _
    rw [Bool.and_eq_true, negT, negT]
  have a1 : ∀ e x, atom (e, 1) x = true ↔ e.1 ∈ x ∧ e.2 ∉ x := fun e x => by
    show (bit e.1 x && neg e.2 x) = true ↔ _
    rw [Bool.and_eq_true, bitT, negT]
  have a2 : ∀ e x, atom (e, 2) x = true ↔ e.1 ∉ x ∧ e.2 ∈ x := fun e x => by
    show (neg e.1 x && bit e.2 x) = true ↔ _
    rw [Bool.and_eq_true, negT, bitT]
  have ends : ∀ e ∈ E, e.1 ∈ active ∧ e.2 ∈ active ∧ e.1 ≠ e.2 := fun e he =>
    ⟨(hE e he).2.1, (hE e he).2.2, ne_of_lt (hE e he).1⟩
  have sep : ∀ u ∈ active, ∀ v ∈ active, (∀ j, u ∈ probe j ↔ v ∈ probe j) → u = v := by
    intro u hu v hv hiff
    rcases sid u hu u hu v hv v hv (fun j => by simp only [hiff j]) with h | h
    · exact h.1
    · exact h.1
  -- los atomos beta y gamma no se anulan en las filas con una componente
  have zeroK : ∀ e ∈ E, ∀ x : W, (e.1 ∈ x ↔ e.2 ∈ x) → ∀ k : Fin 3, k ≠ 0 → atom (e, k) x = false := by
    intro e _ x hx k hk
    rw [← Bool.not_eq_true]
    fin_cases k
    · exact absurd rfl hk
    · show ¬ atom (e, 1) x = true
      rw [a1]; tauto
    · show ¬ atom (e, 2) x = true
      rw [a2]; tauto
  have zeroE : ∀ e ∈ E, ∀ k : Fin 3, k ≠ 0 → atom (e, k) ∅ = false := fun e he k hk =>
    zeroK e he ∅ (iff_of_false (notIn _) (notIn _)) k hk
  have sameK : ∀ e ∈ E, ∀ j, (e.1 ∈ K j ↔ e.2 ∈ K j) := fun e he j => by
    rw [mK, mK, edgeColor e he]
  have alpha0 : ∀ e : Fin n × Fin n, atom (e, 0) ∅ = true := fun e => (a0 e ∅).2 ⟨notIn _, notIn _⟩
  have alphaK : ∀ e : Fin n × Fin n, atom (e, 0) (K (color e.1)) = false := fun e => by
    rw [← Bool.not_eq_true, a0]
    exact fun h => h.1 ((mK _ _).2 rfl)
  have neg0 : ∀ v, neg v ∅ = true := fun v => (negT v ∅).2 (notIn _)
  have negK : ∀ v, neg v (K (color v)) = false := fun v => (negF _ _).2 ((mK _ _).2 rfl)
  -- distintos sobre las pruebas
  let Eq' : (W → Bool) → (W → Bool) → Prop := fun f g => ∀ x ∈ tests, f x = g x
  have negneg : ∀ v w, Eq' (neg v) (neg w) → v = w := by
    intro v w he
    by_contra hne
    by_cases hc : color v = color w
    · have act : ∀ a b : Fin n, color a = color b → a ≠ b → a ∈ active := by
        intro a b hab habne
        by_contra hna
        have closed : ∀ e ∈ E, e.1 ∈ ({a} : Finset (Fin n)) ↔ e.2 ∈ ({a} : Finset (Fin n)) := by
          intro e he
          have n1 : e.1 ≠ a := fun h => hna (h ▸ (ends e he).1)
          have n2 : e.2 ≠ a := fun h => hna (h ▸ (ends e he).2.1)
          exact iff_of_false (fun h => n1 (Finset.mem_singleton.1 h)) (fun h => n2 (Finset.mem_singleton.1 h))
        have := (hcomp {a}).1 (fun e he => closed e he) a b hab
        exact habne (Finset.mem_singleton.1 (this.1 (Finset.mem_singleton_self _))).symm
      have av := act v w hc hne
      have aw := act w v hc.symm (Ne.symm hne)
      apply hne
      refine sep v av w aw (fun j => ?_)
      have := he _ (tP j)
      rw [Bool.eq_iff_iff, negT, negT] at this
      exact not_iff_not.1 this
    · have := he _ (tK (color v))
      rw [negK] at this
      have h := (negF w _).1 this.symm
      exact hc ((mK _ _).1 h).symm
  have negAtom : ∀ v, ∀ e ∈ E, ∀ k, ¬ Eq' (neg v) (atom (e, k)) := by
    intro v e he k heq
    have hk : k = 0 := by
      by_contra hk
      have := heq _ t0
      rw [neg0, zeroE e he k hk] at this
      exact Bool.noConfusion this
    subst hk
    obtain ⟨u1, u2, une⟩ := ends e he
    apply une
    refine sep _ u1 _ u2 (fun j => ?_)
    have p := heq _ (tP j)
    have q := heq _ (hco j)
    rw [Bool.eq_iff_iff, negT, a0] at p q
    rw [mC, mC, mC] at q
    exact PEqualNP.Outside.L_meta_53196.neg_alpha _ _ _ p q
  have negRaw : ∀ v, ∀ g ∈ raw, ¬ Eq' (neg v) g := by
    intro v g hg heq
    have at0 := heq _ t0
    have atK := heq _ (tK (color v))
    rw [neg0] at at0
    rw [negK] at atK
    rcases Finset.mem_union.1 hg with hg | hg
    · rcases Finset.mem_union.1 hg with hg | hg
      · rcases Finset.mem_union.1 hg with hg | hg
        · rcases Finset.mem_insert.1 hg with rfl | hg
          · exact Bool.noConfusion at0
          · rw [Finset.mem_singleton.1 hg] at atK
            exact Bool.noConfusion atK
        · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hg
          exact notIn i ((bitT _ _).1 at0.symm)
      · obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hg
        have : same e (K (color v)) = true := (sameT _ _).2 (sameK e he _)
        rw [this] at atK
        exact Bool.noConfusion atK
    · obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hg
      have : same e ∅ = true := (sameT _ _).2 (iff_of_false (notIn _) (notIn _))
      simp only [this] at at0
      exact Bool.noConfusion at0
  have atomRaw : ∀ e ∈ E, ∀ k, ∀ g, g ∈ raw ∨ (∃ i, g = neg i) → ¬ Eq' (atom (e, k)) g := by
    intro e he k g hg heq
    rcases hg with hg | ⟨i, rfl⟩
    swap
    · exact negAtom i e he k (fun x hx => (heq x hx).symm)
    obtain ⟨u1, u2, une⟩ := ends e he
    have at0 := heq _ t0
    have atK := heq _ (tK (color e.1))
    have nonzero : k ≠ 0 → ¬ ∀ j, atom (e, k) (probe j) = false ∧ atom (e, k) (co j) = false := by
      intro hk hall
      apply une
      refine sep _ u1 _ u2 (fun j => ?_)
      obtain ⟨p, q⟩ := hall j
      rw [← Bool.not_eq_true] at p q
      fin_cases k
      · exact absurd rfl hk
      · change ¬ atom (e, 1) (probe j) = true at p
        change ¬ atom (e, 1) (co j) = true at q
        rw [a1] at p q; rw [mC, mC] at q; tauto
      · change ¬ atom (e, 2) (probe j) = true at p
        change ¬ atom (e, 2) (co j) = true at q
        rw [a2] at p q; rw [mC, mC] at q; tauto
    rcases Finset.mem_union.1 hg with hg | hg
    · rcases Finset.mem_union.1 hg with hg | hg
      · rcases Finset.mem_union.1 hg with hg | hg
        · rcases Finset.mem_insert.1 hg with rfl | hg
          · by_cases hk : k = 0
            · subst hk; rw [alpha0] at at0; exact Bool.noConfusion at0
            · exact nonzero hk (fun j => ⟨heq _ (tP j), heq _ (hco j)⟩)
          · rw [Finset.mem_singleton.1 hg] at at0 atK
            by_cases hk : k = 0
            · subst hk; rw [alphaK] at atK; exact Bool.noConfusion atK
            · rw [zeroE e he k hk] at at0; exact Bool.noConfusion at0
        · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hg
          by_cases hk : k = 0
          · subst hk
            rw [alpha0] at at0
            exact notIn i ((bitT _ _).1 at0.symm)
          · have z := heq _ (tK (color i))
            rw [zeroK e he _ (sameK e he _) k hk] at z
            have : bit i (K (color i)) = true := (bitT _ _).2 ((mK _ _).2 rfl)
            rw [this] at z
            exact Bool.noConfusion z
      · obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 hg
        have sk : same f (K (color e.1)) = true := (sameT _ _).2 (sameK f hf _)
        have s0 : same f ∅ = true := (sameT _ _).2 (iff_of_false (notIn _) (notIn _))
        by_cases hk : k = 0
        · subst hk; rw [alphaK, sk] at atK; exact Bool.noConfusion atK
        · rw [zeroE e he k hk, s0] at at0; exact Bool.noConfusion at0
    · obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 hg
      have s0 : same f ∅ = true := (sameT _ _).2 (iff_of_false (notIn _) (notIn _))
      by_cases hk : k = 0
      · subst hk
        rw [alpha0] at at0
        simp only [s0] at at0
        exact Bool.noConfusion at0
      · apply nonzero hk
        intro j
        have p := heq _ (tP j)
        have q := heq _ (hco j)
        have sc : same f (co j) = same f (probe j) := by
          rw [Bool.eq_iff_iff, sameT, sameT, mC, mC, not_iff_not]
        simp only [sc] at q
        have pq : atom (e, k) (probe j) = atom (e, k) (co j) := p.trans q.symm
        have excl : ¬ (atom (e, k) (probe j) = true ∧ atom (e, k) (co j) = true) := by
          fin_cases k
          · exact absurd rfl hk
          · change ¬ (atom (e, 1) (probe j) = true ∧ atom (e, 1) (co j) = true)
            rw [a1, a1, mC, mC]; tauto
          · change ¬ (atom (e, 2) (probe j) = true ∧ atom (e, 2) (co j) = true)
            rw [a2, a2, mC, mC]; tauto
        rw [← pq] at excl ⊢
        have : atom (e, k) (probe j) = false := by
          rw [← Bool.not_eq_true]; exact fun h => excl ⟨h, h⟩
        exact ⟨this, this⟩
  have atomAtom : ∀ e ∈ E, ∀ e' ∈ E, ∀ k k', Eq' (atom (e, k)) (atom (e', k')) → (e, k) = (e', k') := by
    intro e he e' he' k k' heq
    obtain ⟨u1, u2, une⟩ := ends e he
    obtain ⟨v1, v2, vne⟩ := ends e' he'
    have at0 := heq _ t0
    have ord := (hE e he).1
    have ord' := (hE e' he').1
    by_cases hk : k = 0
    · have hk' : k' = 0 := by
        by_contra hk'
        subst hk
        rw [alpha0, zeroE e' he' k' hk'] at at0
        exact Bool.noConfusion at0
      subst hk hk'
      have key : ∀ j, (if e.1 ∈ probe j then 1 else 0 : ℕ) + (if e.2 ∈ probe j then 1 else 0) =
          (if e'.1 ∈ probe j then 1 else 0) + (if e'.2 ∈ probe j then 1 else 0) := by
        intro j
        have p := heq _ (tP j)
        have q := heq _ (hco j)
        rw [Bool.eq_iff_iff, a0, a0] at p q
        rw [mC, mC, mC, mC] at q
        exact PEqualNP.Outside.L_meta_53196.sum_alpha _ _ _ _ p q
      rcases sid _ u1 _ u2 _ v1 _ v2 key with ⟨x, y⟩ | ⟨x, y⟩
      · rw [Prod.ext x y]
      · rw [x, y] at ord; exact absurd ord (lt_asymm ord')
    · have hk' : k' ≠ 0 := by
        intro hk'
        subst hk'
        rw [alpha0, zeroE e he k hk] at at0
        exact Bool.noConfusion at0
      -- orientar: beta usa (e.1, e.2), gamma (e.2, e.1)
      have orient : ∀ f ∈ E, ∀ m : Fin 3, m ≠ 0 → ∃ s t : Fin n, ((m = 1 ∧ s = f.1 ∧ t = f.2) ∨ (m = 2 ∧ s = f.2 ∧ t = f.1)) ∧
          ∀ x : W, atom (f, m) x = true ↔ s ∈ x ∧ t ∉ x := by
        intro f _ m hm
        fin_cases m
        · exact absurd rfl hm
        · exact ⟨f.1, f.2, Or.inl ⟨rfl, rfl, rfl⟩, fun x => a1 f x⟩
        · exact ⟨f.2, f.1, Or.inr ⟨rfl, rfl, rfl⟩, fun x => by
            show atom (f, 2) x = true ↔ _
            rw [a2]; exact and_comm⟩
      obtain ⟨s, t, o, hs⟩ := orient e he k hk
      obtain ⟨s', t', o', hs'⟩ := orient e' he' k' hk'
      have ss : s ∈ active ∧ t ∈ active ∧ s ≠ t := by
        rcases o with ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩
        exacts [⟨u1, u2, une⟩, ⟨u2, u1, une.symm⟩]
      have ss' : s' ∈ active ∧ t' ∈ active := by
        rcases o' with ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩
        exacts [⟨v1, v2⟩, ⟨v2, v1⟩]
      have key : ∀ j, (if s ∈ probe j then 1 else 0 : ℕ) + (if t' ∈ probe j then 1 else 0) =
          (if s' ∈ probe j then 1 else 0) + (if t ∈ probe j then 1 else 0) := by
        intro j
        have p := heq _ (tP j)
        have q := heq _ (hco j)
        rw [Bool.eq_iff_iff, hs, hs'] at p q
        rw [mC, mC, mC, mC] at q
        exact PEqualNP.Outside.L_meta_53196.sum_beta _ _ _ _ p q
      rcases sid _ ss.1 _ ss'.2 _ ss'.1 _ ss.2.1 key with ⟨x, y⟩ | ⟨x, -⟩
      swap
      · exact absurd x ss.2.2
      -- s = s' y t' = t
      rcases o with ⟨m, r1, r2⟩ | ⟨m, r1, r2⟩ <;> rcases o' with ⟨m', r1', r2'⟩ | ⟨m', r1', r2'⟩
      · have : e = e' := Prod.ext (by rw [← r1, x, r1']) (by rw [← r2, ← y, r2'])
        rw [this, m, m']
      · exfalso
        have h1 : e.1 = e'.2 := by rw [← r1, x, r1']
        have h2 : e.2 = e'.1 := by rw [← r2, ← y, r2']
        rw [h1, h2] at ord; exact lt_asymm ord ord'
      · exfalso
        have h1 : e.2 = e'.1 := by rw [← r1, x, r1']
        have h2 : e.1 = e'.2 := by rw [← r2, ← y, r2']
        rw [h1, h2] at ord; exact lt_asymm ord ord'
      · have : e = e' := Prod.ext (by rw [← r2, ← y, r2']) (by rw [← r1, x, r1'])
        rw [this, m, m']
  refine ⟨?_, ?_⟩
  swap
  · simp only [tests]
    have img : ∀ {α β : Type} {i : DecidableEq β} [Fintype α] (f : α → β) (m : ℕ), Fintype.card α = m →
        (Finset.image f Finset.univ).card ≤ m := fun f m e => Finset.card_image_le.trans (le_of_eq (by rw [Finset.card_univ, e]))
    refine le_trans (PEqualNP.Outside.L_meta_53196.card4 (a := 2*h) (b := 2*h) (c := 1) (d := c)
      (img _ _ (Fintype.card_fin _)) (img _ _ (Fintype.card_fin _)) (le_of_eq (Finset.card_singleton _))
      (img _ _ (Fintype.card_fin _))) (by omega)
  intro S p
  intro L
  have inL : ∀ g, g ∈ raw ∨ g ∈ S.image neg → g ∈ L := fun g h => Finset.mem_toList.2 (Finset.mem_union.2 h)
  have ofL : ∀ g ∈ L, g ∈ raw ∨ ∃ s ∈ S, neg s = g := fun g hg =>
    (Finset.mem_union.1 (Finset.mem_toList.1 hg)).imp id Finset.mem_image.1
  have needNeg : ∀ v, neg v ∈ need := fun v =>
    Finset.mem_union.2 (Or.inl (Finset.mem_union.2 (Or.inl (Finset.mem_union.2 (Or.inl
      (Finset.mem_image_of_mem _ (Finset.mem_univ _)))))))
  have needAtom : ∀ e ∈ E, ∀ k, atom (e, k) ∈ need := by
    intro e he k
    fin_cases k
    · exact Finset.mem_union.2 (Or.inl (Finset.mem_union.2 (Or.inl (Finset.mem_union.2 (Or.inr (Finset.mem_image.2 ⟨e, he, rfl⟩))))))
    · exact Finset.mem_union.2 (Or.inl (Finset.mem_union.2 (Or.inr (Finset.mem_image.2 ⟨e, he, rfl⟩))))
    · exact Finset.mem_union.2 (Or.inr (Finset.mem_image.2 ⟨e, he, rfl⟩))
  constructor
  · rintro ⟨C, mono, -, -, size, comp⟩
    have meets : ∀ j, ∃ i ∈ S, color i = j := by
      intro j
      by_contra hno
      obtain ⟨v, hv⟩ := hsurj j
      obtain ⟨w, -, hw⟩ := comp (neg v) (needNeg v)
      have r0 := hw _ t0
      have r1 := hw _ (tK j)
      rw [neg0] at r0
      have nv : neg v (K j) = false := (negF _ _).2 ((mK _ _).2 hv)
      rw [nv] at r1
      have up : ∀ i, (L.map (fun g => g (∅ : Finset (Fin n)))).getD i false = true →
          (L.map (fun g => g (K j))).getD i false = true := by
        intro i hi
        by_cases hlt : i < L.length
        swap
        · rw [List.getD_eq_default _ _ (by rw [List.length_map]; omega)] at hi
          exact Bool.noConfusion hi
        rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hlt] at hi ⊢
        change L[i] ∅ = true at hi
        change L[i] (K j) = true
        rcases ofL _ (List.getElem_mem hlt) with hg | ⟨s, hs, e⟩
        · rcases Finset.mem_union.1 hg with hg | hg
          · rcases Finset.mem_union.1 hg with hg | hg
            · rcases Finset.mem_union.1 hg with hg | hg
              · rcases Finset.mem_insert.1 hg with e | hg
                · rw [e] at hi; exact Bool.noConfusion hi
                · rw [Finset.mem_singleton.1 hg]
              · obtain ⟨i', -, e⟩ := Finset.mem_image.1 hg
                rw [← e] at hi
                exact absurd ((bitT _ _).1 hi) (notIn _)
            · obtain ⟨f, hf, e⟩ := Finset.mem_image.1 hg
              rw [← e]; exact (sameT _ _).2 (sameK f hf _)
          · obtain ⟨f, hf, e⟩ := Finset.mem_image.1 hg
            rw [← e] at hi
            have : same f ∅ = true := (sameT _ _).2 (iff_of_false (notIn _) (notIn _))
            simp only [this] at hi
            exact Bool.noConfusion hi
        · rw [← e]
          exact (negT _ _).2 (fun h => hno ⟨s, hs, (mK _ _).1 h⟩)
      have gk : ∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or :=
        fun g hg => by simpa using (mono g hg).1
      have := PEqualNP.Outside.L_meta_53196.circuit_mono C.gates gk
        (L.map (fun g : W → Bool => g (∅ : Finset (Fin n)))) (L.map (fun g : W → Bool => g (K j)))
        (by rw [List.length_map, List.length_map]) up w r0
      have h3 : (C.wires (L.map (fun g => g (K j)))).getD w false = true := this
      rw [r1] at h3
      exact Bool.noConfusion h3
    refine ⟨meets, ?_⟩
    let N : Finset (Fin n ⊕ ((Fin n × Fin n) × Fin 3)) := (Sᶜ).disjSum (E ×ˢ (Finset.univ : Finset (Fin 3)))
    let fn : Fin n ⊕ ((Fin n × Fin n) × Fin 3) → (W → Bool) := Sum.elim neg atom
    have fnNeed : ∀ q ∈ N, fn q ∈ need := by
      rintro (v | ⟨e, k⟩) hq
      · exact needNeg v
      · exact needAtom e (Finset.mem_product.1 (Finset.inr_mem_disjSum.1 hq)).1 k
    have notInput : ∀ q ∈ N, ∀ g ∈ L, ¬ Eq' (fn q) g := by
      rintro (v | ⟨e, k⟩) hq g hg heq
      · have vS : v ∉ S := Finset.mem_compl.1 (Finset.inl_mem_disjSum.1 hq)
        rcases ofL g hg with h | ⟨s, hs, rfl⟩
        · exact negRaw v g h heq
        · exact vS ((negneg v s heq) ▸ hs)
      · have he := (Finset.mem_product.1 (Finset.inr_mem_disjSum.1 hq)).1
        rcases ofL g hg with h | ⟨s, -, rfl⟩
        · exact atomRaw e he k g (Or.inl h) heq
        · exact atomRaw e he k _ (Or.inr ⟨s, rfl⟩) heq
    have distinct : ∀ q ∈ N, ∀ q' ∈ N, Eq' (fn q) (fn q') → q = q' := by
      rintro (v | ⟨e, k⟩) hq (w | ⟨e', k'⟩) hq' heq
      · rw [negneg v w heq]
      · exact absurd heq (negAtom v e' (Finset.mem_product.1 (Finset.inr_mem_disjSum.1 hq')).1 k')
      · exact absurd (fun x hx => (heq x hx).symm)
          (negAtom w e (Finset.mem_product.1 (Finset.inr_mem_disjSum.1 hq)).1 k)
      · rw [atomAtom e (Finset.mem_product.1 (Finset.inr_mem_disjSum.1 hq)).1 e'
          (Finset.mem_product.1 (Finset.inr_mem_disjSum.1 hq')).1 k k' heq]
    have wire : ∀ q : ↥N, ∃ j, j < L.length + C.size ∧ ∀ x ∈ tests, (C.wires (L.map (fun g => g x))).getD j false = fn q.1 x :=
      fun q => comp _ (fnNeed q.1 q.2)
    choose wj hlt hval using wire
    have high : ∀ q, L.length ≤ wj q := by
      intro q
      by_contra hc
      have hc' : wj q < L.length := not_le.1 hc
      refine notInput q.1 q.2 (L[wj q]) (List.getElem_mem hc') (fun x hx => ?_)
      rw [← hval q x hx]
      have := PEqualNP.Outside.L_meta_53196.val_input (L.map (fun g => g x)) C.gates (wj q) (by rw [List.length_map]; exact hc')
      change (C.wires (L.map (fun g => g x))).getD (wj q) false = _ at this
      rw [this, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hc']
      rfl
    let slot : ↥N → Fin C.size := fun q => ⟨wj q - L.length, by have := hlt q; have := high q; omega⟩
    have inj : Function.Injective slot := by
      intro q q' e
      have e' : wj q = wj q' := by
        have := congrArg Fin.val e
        have h1 := high q
        have h2 := high q'
        simp only [slot] at this
        omega
      exact Subtype.ext (distinct q.1 q.2 q'.1 q'.2 (fun x hx => by rw [← hval q x hx, ← hval q' x hx, e']))
    have count := Fintype.card_le_of_injective slot inj
    rw [Fintype.card_coe, Fintype.card_fin] at count
    have cardN : N.card = (n - S.card) + 3 * E.card := by
      simp only [N, Finset.card_disjSum, Finset.card_product, Finset.card_univ, Fintype.card_fin]
      rw [Finset.card_compl, Fintype.card_fin]
      ring
    have : S.card ≤ n := by simpa using Finset.card_le_univ S
    omega
  · rintro ⟨meets, budget⟩
    have inRaw : ∀ g ∈ raw, g ∈ L := fun g h => inL g (Or.inl h)
    have ok0 : PEqualNP.Outside.L_meta_53196.Ok L.length [] := ⟨by simp, by simp⟩
    let Has := fun (g : List PEqualNP.CircuitLowerBounds.Gate) (f : W → Bool) => PEqualNP.Outside.L_meta_53196.Has L g f
    -- tres atomos de una arista con cuatro entradas disponibles
    have three : ∀ g, PEqualNP.Outside.L_meta_53196.Ok L.length g → ∀ e : Fin n × Fin n, ∀ a b c' d e' f' : W → Bool,
        Has g a → Has g b → Has g c' → Has g d → Has g e' → Has g f' →
        (∀ x, (a x && b x) = atom (e, 0) x) → (∀ x, (c' x && d x) = atom (e, 1) x) → (∀ x, (e' x && f' x) = atom (e, 2) x) →
        ∃ g', PEqualNP.Outside.L_meta_53196.Ext L.length g g' ∧ g'.length = g.length + 3 ∧ ∀ k, Has g' (atom (e, k)) := by
      intro g ok e a b c' d e' f' ha hb hc hd he hf q0 q1 q2
      obtain ⟨g1, x1, l1, h1⟩ := PEqualNP.Outside.L_meta_53196.Has.gate ok PEqualNP.CircuitLowerBounds.GateOp.and (Or.inl rfl) ha hb
        (f := atom (e, 0)) (fun x => by rw [← q0]; simp [PEqualNP.CircuitLowerBounds.GateOp.eval])
      obtain ⟨g2, x2, l2, h2⟩ := PEqualNP.Outside.L_meta_53196.Has.gate x1.1 PEqualNP.CircuitLowerBounds.GateOp.and (Or.inl rfl)
        (hc.mono x1) (hd.mono x1) (f := atom (e, 1)) (fun x => by rw [← q1]; simp [PEqualNP.CircuitLowerBounds.GateOp.eval])
      obtain ⟨g3, x3, l3, h3⟩ := PEqualNP.Outside.L_meta_53196.Has.gate x2.1 PEqualNP.CircuitLowerBounds.GateOp.and (Or.inl rfl)
        (he.mono (x1.trans x2)) (hf.mono (x1.trans x2)) (f := atom (e, 2)) (fun x => by rw [← q2]; simp [PEqualNP.CircuitLowerBounds.GateOp.eval])
      refine ⟨g3, (x1.trans x2).trans x3, by omega, fun k => ?_⟩
      fin_cases k
      · exact h1.mono (x2.trans x3)
      · exact h2.mono x3
      · exact h3
    have val3 : ∀ (e : Fin n × Fin n) (x : W), atom (e, 0) x = (!(bit e.1 x) && !(bit e.2 x)) ∧
        atom (e, 1) x = (bit e.1 x && !(bit e.2 x)) ∧ atom (e, 2) x = (!(bit e.1 x) && bit e.2 x) :=
      fun e x => ⟨rfl, rfl, rfl⟩
    have sameBit : ∀ (e : Fin n × Fin n) (x : W), same e x = (bit e.1 x == bit e.2 x) := by
      intro e x
      rw [Bool.eq_iff_iff, sameT, beq_iff_eq, Bool.eq_iff_iff, bitT, bitT]
    have grow : ∀ m, ∀ (T : Finset (Fin n)) (F : Finset (Fin n × Fin n)) (g : List PEqualNP.CircuitLowerBounds.Gate),
        (Tᶜ).card = m → S ⊆ T → F ⊆ E → (∀ e ∈ F, e.1 ∈ T ∧ e.2 ∈ T) → PEqualNP.Outside.L_meta_53196.Ok L.length g →
        (∀ v ∈ T, Has g (neg v)) → (∀ e ∈ F, ∀ k, Has g (atom (e, k))) → g.length + S.card = 3 * F.card + T.card →
        ∃ (F' : Finset (Fin n × Fin n)) (g' : List PEqualNP.CircuitLowerBounds.Gate), F' ⊆ E ∧
          PEqualNP.Outside.L_meta_53196.Ok L.length g' ∧ (∀ v, Has g' (neg v)) ∧ (∀ e ∈ F', ∀ k, Has g' (atom (e, k))) ∧
          g'.length + S.card = 3 * F'.card + n := by
      intro m
      induction m with
      | zero =>
        intro T F g hm _ hF _ ok hn ha len
        have full : T = Finset.univ := by
          rw [Finset.card_eq_zero, Finset.compl_eq_empty_iff] at hm
          · exact hm
        refine ⟨F, g, hF, ok, fun v => hn v (full ▸ Finset.mem_univ v), ha, ?_⟩
        rw [full, Finset.card_univ, Fintype.card_fin] at len
        exact len
      | succ m ih =>
        intro T F g hm hS hF hFT ok hn ha len
        have cross : ∃ e ∈ E, ¬ (e.1 ∈ T ↔ e.2 ∈ T) := by
          by_contra hno
          have closed : ∀ e ∈ E, e.1 ∈ T ↔ e.2 ∈ T := fun e he => by
            by_contra h
            exact hno ⟨e, he, h⟩
          have inv := (hcomp T).1 closed
          have : T = Finset.univ := by
            refine Finset.eq_univ_of_forall (fun v => ?_)
            obtain ⟨s, hs, cs⟩ := meets (color v)
            exact (inv s v cs).1 (hS hs)
          rw [this, Finset.compl_univ, Finset.card_empty] at hm
          omega
        obtain ⟨e, he, hx⟩ := cross
        have eF : e ∉ F := fun h => hx (iff_of_true (hFT e h).1 (hFT e h).2)
        have bitHas : ∀ i, Has g (bit i) := fun i => PEqualNP.Outside.L_meta_53196.Has.input g (inRaw _ (rawB i))
        have sHas : Has g (same e) := PEqualNP.Outside.L_meta_53196.Has.input g (inRaw _ (rawS e he))
        have dHas : Has g (fun x => !(same e x)) := PEqualNP.Outside.L_meta_53196.Has.input g (inRaw _ (rawD e he))
        have step : ∀ v, v ∉ T → (v = e.1 ∨ v = e.2) → (∀ w, (w = e.1 ∨ w = e.2) → w ≠ v → w ∈ T) →
            ∀ g3 : List PEqualNP.CircuitLowerBounds.Gate, PEqualNP.Outside.L_meta_53196.Ext L.length g g3 → g3.length = g.length + 3 →
            (∀ k, Has g3 (atom (e, k))) → ∀ i j : Fin 3, (∀ x, (atom (e, i) x || atom (e, j) x) = neg v x) →
            ∃ (F' : Finset (Fin n × Fin n)) (g' : List PEqualNP.CircuitLowerBounds.Gate), F' ⊆ E ∧
              PEqualNP.Outside.L_meta_53196.Ok L.length g' ∧ (∀ v, Has g' (neg v)) ∧ (∀ e ∈ F', ∀ k, Has g' (atom (e, k))) ∧
              g'.length + S.card = 3 * F'.card + n := by
          intro v vT vend other g3 x3 l3 h3 i j hor
          obtain ⟨g4, x4, l4, h4⟩ := PEqualNP.Outside.L_meta_53196.Has.gate x3.1 PEqualNP.CircuitLowerBounds.GateOp.or (Or.inr rfl)
            (h3 i) (h3 j) (f := neg v) (fun x => by rw [← hor]; simp [PEqualNP.CircuitLowerBounds.GateOp.eval])
          have inT : ∀ w, (w = e.1 ∨ w = e.2) → w ∈ insert v T := by
            intro w hw
            by_cases h : w = v
            · rw [h]; exact Finset.mem_insert_self _ _
            · exact Finset.mem_insert_of_mem (other w hw h)
          have cm : ((insert v T)ᶜ).card = m := by
            rw [Finset.compl_insert, Finset.card_erase_of_mem (Finset.mem_compl.2 vT), hm]
            rfl
          refine ih (insert v T) (insert e F) g4 cm (hS.trans (Finset.subset_insert _ _)) (Finset.insert_subset he hF) ?_ x4.1 ?_ ?_ ?_
          · intro f hf
            rcases Finset.mem_insert.1 hf with rfl | hf
            · exact ⟨inT _ (Or.inl rfl), inT _ (Or.inr rfl)⟩
            · exact ⟨Finset.mem_insert_of_mem (hFT f hf).1, Finset.mem_insert_of_mem (hFT f hf).2⟩
          · intro w hw
            rcases Finset.mem_insert.1 hw with rfl | hw
            · exact h4
            · exact (hn w hw).mono (x3.trans x4)
          · intro f hf k
            rcases Finset.mem_insert.1 hf with rfl | hf
            · exact (h3 k).mono x4
            · exact (ha f hf k).mono (x3.trans x4)
          · rw [Finset.card_insert_of_notMem eF, Finset.card_insert_of_notMem vT, l4, l3]
            omega
        by_cases h1 : e.1 ∈ T
        · have h2 : e.2 ∉ T := fun h => hx (iff_of_true h1 h)
          have nu := hn _ h1
          obtain ⟨g3, x3, l3, h3⟩ := three g ok e (same e) (neg e.1) (fun x => !(same e x)) (bit e.1) (fun x => !(same e x)) (neg e.1)
            sHas nu dHas (bitHas _) dHas nu
            (fun x => by
              rw [(val3 e x).1, sameBit]; show ((bit e.1 x == bit e.2 x) && !(bit e.1 x)) = _
              cases bit e.1 x <;> cases bit e.2 x <;> rfl)
            (fun x => by
              rw [(val3 e x).2.1, sameBit]
              cases bit e.1 x <;> cases bit e.2 x <;> rfl)
            (fun x => by
              rw [(val3 e x).2.2, sameBit]; show ((!(bit e.1 x == bit e.2 x)) && !(bit e.1 x)) = _
              cases bit e.1 x <;> cases bit e.2 x <;> rfl)
          refine step e.2 h2 (Or.inr rfl) (fun w hw hne => ?_) g3 x3 l3 h3 0 1 (fun x => ?_)
          · rcases hw with rfl | rfl
            · exact h1
            · exact absurd rfl hne
          · rw [(val3 e x).1, (val3 e x).2.1]
            show _ = !(bit e.2 x)
            cases bit e.1 x <;> cases bit e.2 x <;> rfl
        · have h2 : e.2 ∈ T := by
            by_contra h
            exact hx (iff_of_false h1 h)
          have nv := hn _ h2
          obtain ⟨g3, x3, l3, h3⟩ := three g ok e (same e) (neg e.2) (fun x => !(same e x)) (neg e.2) (fun x => !(same e x)) (bit e.2)
            sHas nv dHas nv dHas (bitHas _)
            (fun x => by
              rw [(val3 e x).1, sameBit]; show ((bit e.1 x == bit e.2 x) && !(bit e.2 x)) = _
              cases bit e.1 x <;> cases bit e.2 x <;> rfl)
            (fun x => by
              rw [(val3 e x).2.1, sameBit]; show ((!(bit e.1 x == bit e.2 x)) && !(bit e.2 x)) = _
              cases bit e.1 x <;> cases bit e.2 x <;> rfl)
            (fun x => by
              rw [(val3 e x).2.2, sameBit]
              cases bit e.1 x <;> cases bit e.2 x <;> rfl)
          refine step e.1 h1 (Or.inl rfl) (fun w hw hne => ?_) g3 x3 l3 h3 0 2 (fun x => ?_)
          · rcases hw with rfl | rfl
            · exact absurd rfl hne
            · exact h2
          · rw [(val3 e x).1, (val3 e x).2.2]
            show _ = !(bit e.1 x)
            cases bit e.1 x <;> cases bit e.2 x <;> rfl
    obtain ⟨F, g, hF, ok, hn, ha, len⟩ := grow _ S ∅ [] rfl (Finset.Subset.refl _) (Finset.empty_subset _) (by simp) ok0
      (fun v hv => PEqualNP.Outside.L_meta_53196.Has.input [] (inL _ (Or.inr (Finset.mem_image_of_mem _ hv))))
      (by simp) (by simp)
    have rest : ∀ R : Finset (Fin n × Fin n), R ⊆ E → Disjoint F R →
        ∃ g', PEqualNP.Outside.L_meta_53196.Ok L.length g' ∧ (∀ v, Has g' (neg v)) ∧ (∀ e ∈ F ∪ R, ∀ k, Has g' (atom (e, k))) ∧
          g'.length + S.card = 3 * (F ∪ R).card + n := by
      intro R
      induction R using Finset.induction with
      | empty =>
        intro _ _
        exact ⟨g, ok, hn, by simpa using ha, by simpa using len⟩
      | insert e R heR ih =>
        intro hsub hdis
        obtain ⟨g1, ok1, n1, at1, l1⟩ := ih ((Finset.subset_insert _ _).trans hsub)
          (Finset.disjoint_of_subset_right (Finset.subset_insert _ _) hdis)
        have he : e ∈ E := hsub (Finset.mem_insert_self _ _)
        have eF : e ∉ F := fun h => Finset.disjoint_left.1 hdis h (Finset.mem_insert_self _ _)
        have bitHas : ∀ i, Has g1 (bit i) := fun i => PEqualNP.Outside.L_meta_53196.Has.input g1 (inRaw _ (rawB i))
        obtain ⟨g3, x3, l3, h3⟩ := three g1 ok1 e (neg e.1) (neg e.2) (bit e.1) (neg e.2) (neg e.1) (bit e.2)
          (n1 _) (n1 _) (bitHas _) (n1 _) (n1 _) (bitHas _) (fun x => rfl) (fun x => rfl) (fun x => rfl)
        refine ⟨g3, x3.1, fun v => (n1 v).mono x3, ?_, ?_⟩
        · intro f hf k
          rcases Finset.mem_union.1 hf with hf | hf
          · exact (at1 f (Finset.mem_union_left _ hf) k).mono x3
          rcases Finset.mem_insert.1 hf with rfl | hf
          · exact h3 k
          · exact (at1 f (Finset.mem_union_right _ hf) k).mono x3
        · have ne : e ∉ F ∪ R := fun h => (Finset.mem_union.1 h).elim eF heR
          rw [Finset.union_insert, Finset.card_insert_of_notMem ne, l3]
          omega
    obtain ⟨g', ok', hn', ha', len'⟩ := rest (E \ F) Finset.sdiff_subset Finset.disjoint_sdiff
    have all : F ∪ (E \ F) = E := Finset.union_sdiff_of_subset hF
    rw [all] at ha' len'
    have Lpos : 0 < L.length := lt_of_le_of_lt (Nat.zero_le _) (List.idxOf_lt_length_iff.2 (inRaw _ rawF))
    have Sn : S.card ≤ n := by simpa using Finset.card_le_univ S
    refine ⟨⟨g', 0⟩, ?_, PEqualNP.Outside.L_meta_53196.reads_of_ok' ok' 0, ?_, ?_, ?_⟩
    · intro x hx
      have := ok'.1 x hx
      exact ⟨by simpa using this.1, this.2⟩
    · show 0 < L.length + g'.length
      omega
    · show g'.length ≤ p
      omega
    · intro f hf
      have out : Has g' f := by
        rcases Finset.mem_union.1 hf with hf | hf
        · rcases Finset.mem_union.1 hf with hf | hf
          · rcases Finset.mem_union.1 hf with hf | hf
            · obtain ⟨v, -, rfl⟩ := Finset.mem_image.1 hf
              exact hn' v
            · obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hf
              exact ha' e he 0
          · obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hf
            exact ha' e he 1
        · obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hf
          exact ha' e he 2
      obtain ⟨w, hw, hv⟩ := out
      exact ⟨w, hw, fun x _ => hv x⟩
