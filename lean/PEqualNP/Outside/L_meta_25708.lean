import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25708

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover
open scoped BigOperators

/-! ### Part 1: Fan-in-two ReadsBack Circuit Framework (`Extends`) -/

abbrev Sig (n : ℕ) := (Fin n → Bool) → Bool

def HasWire {n : ℕ} (C : Circuit) (f : Sig n) : Prop :=
  ∃ w : Fin (n + C.size), ∀ x : Fin n → Bool,
    (C.wires (List.ofFn x)).getD w.val false = f x

def Extends (n : ℕ) (S T : Set (Sig n)) (cost : ℕ) : Prop :=
  ∀ (C : Circuit), FanInTwo C → ReadsBack n C → (∀ f ∈ S, HasWire C f) →
    ∃ (C' : Circuit), FanInTwo C' ∧ ReadsBack n C' ∧ C'.size ≤ C.size + cost ∧
      (∀ f : Sig n, HasWire C f → HasWire C' f) ∧ (∀ f ∈ T, HasWire C' f)

lemma wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length := by
  unfold Circuit.wires
  induction C.gates generalizing x with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih]
    simp only [List.length_append, List.length_singleton]
    omega

lemma wires_append (gs₁ gs₂ : List Gate) (x : List Bool) :
    (Circuit.mk (gs₁ ++ gs₂) 0).wires x =
      (Circuit.mk gs₂ 0).wires ((Circuit.mk gs₁ 0).wires x) := by
  unfold Circuit.wires
  simp [List.foldl_append]

lemma wires_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    (Circuit.mk (gs ++ [g]) 0).wires x =
      (Circuit.mk gs 0).wires x ++
        [g.op.eval (g.inputs.map fun i => ((Circuit.mk gs 0).wires x).getD i false)] := by
  rw [wires_append]
  simp [Circuit.wires]

lemma getD_append_left_lt {α : Type*} (l₁ l₂ : List α) (i : ℕ) (d : α) (h : i < l₁.length) :
    (l₁ ++ l₂).getD i d = l₁.getD i d := by
  simp [List.getD, List.getElem?_append_left h]

lemma getD_append_right_eq {α : Type*} (l₁ : List α) (a : α) (d : α) :
    (l₁ ++ [a]).getD l₁.length d = a := by
  simp [List.getD]

lemma push_gate {n : ℕ} (C : Circuit) (hFan : FanInTwo C) (hBack : ReadsBack n C)
    (g : Gate)
    (hgFan : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hgBack : ∀ i ∈ g.inputs, i < n + C.size) :
    let C' : Circuit := ⟨C.gates ++ [g], 0⟩
    FanInTwo C' ∧ ReadsBack n C' ∧ C'.size = C.size + 1 ∧
      (∀ f : Sig n, HasWire C f → HasWire C' f) ∧
      (∀ x : Fin n → Bool,
        (C'.wires (List.ofFn x)).getD (n + C.size) false =
          g.op.eval (g.inputs.map fun i => (C.wires (List.ofFn x)).getD i false)) := by
  intro C'
  have hsize : C'.size = C.size + 1 := by simp [C', Circuit.size]
  have hFan' : FanInTwo C' := by
    intro g' hg'
    simp only [C', List.mem_append, List.mem_singleton] at hg'
    rcases hg' with hg' | rfl
    · exact hFan g' hg'
    · exact hgFan
  have hBack' : ReadsBack n C' := by
    intro j hj i hi
    simp only [C', List.length_append, List.length_singleton] at hj
    by_cases hlt : j < C.gates.length
    · have hget : gateAt C' j = gateAt C j := by
        unfold gateAt
        exact getD_append_left_lt C.gates [g] j _ hlt
      rw [hget] at hi
      exact hBack j hlt i hi
    · have hjeq : j = C.gates.length := by omega
      subst hjeq
      have hget : gateAt C' C.gates.length = g := by
        unfold gateAt
        exact getD_append_right_eq C.gates g _
      rw [hget] at hi
      exact hgBack i hi
  have hkeep : ∀ f : Sig n, HasWire C f → HasWire C' f := by
    rintro f ⟨w, hw⟩
    refine ⟨⟨w.val, by rw [hsize]; omega⟩, fun x => ?_⟩
    have hlen : (C.wires (List.ofFn x)).length = n + C.size := by
      rw [wires_length, List.length_ofFn]; rfl
    have hCeq : (Circuit.mk C.gates 0).wires (List.ofFn x) = C.wires (List.ofFn x) := rfl
    change ((Circuit.mk (C.gates ++ [g]) 0).wires (List.ofFn x)).getD w.val false = f x
    rw [wires_snoc, hCeq, getD_append_left_lt _ _ _ _ (by omega)]
    exact hw x
  have hnew : ∀ x : Fin n → Bool,
      (C'.wires (List.ofFn x)).getD (n + C.size) false =
        g.op.eval (g.inputs.map fun i => (C.wires (List.ofFn x)).getD i false) := by
    intro x
    have hlen : (C.wires (List.ofFn x)).length = n + C.size := by
      rw [wires_length, List.length_ofFn]; rfl
    have hCeq : (Circuit.mk C.gates 0).wires (List.ofFn x) = C.wires (List.ofFn x) := rfl
    change ((Circuit.mk (C.gates ++ [g]) 0).wires (List.ofFn x)).getD (n + C.size) false = _
    rw [wires_snoc, hCeq, ← hlen, getD_append_right_eq]
  exact ⟨hFan', hBack', hsize, hkeep, hnew⟩

lemma base_circuit (n : ℕ) :
    let C0 : Circuit := ⟨[], 0⟩
    FanInTwo C0 ∧ ReadsBack n C0 ∧ C0.size = 0 ∧
      ∀ i : Fin n, HasWire C0 (fun x => x i) := by
  refine ⟨?_, ?_, rfl, ?_⟩
  · intro g hg; simp at hg
  · intro j hj; simp at hj
  · intro i
    refine ⟨⟨i.val, by simp [Circuit.size]⟩, fun x => ?_⟩
    simp [Circuit.wires, List.getD]

lemma Extends.empty {n : ℕ} (S : Set (Sig n)) : Extends n S ∅ 0 := by
  intro C hF hB _
  exact ⟨C, hF, hB, by omega, fun _ h => h, fun _ h => h.elim⟩

lemma Extends.of_subset {n : ℕ} {S T : Set (Sig n)} (h : T ⊆ S) : Extends n S T 0 := by
  intro C hF hB hS
  exact ⟨C, hF, hB, by omega, fun _ hw => hw, fun f hf => hS f (h hf)⟩

lemma Extends.mono {n : ℕ} {S S' T T' : Set (Sig n)} {c c' : ℕ}
    (hS : S ⊆ S') (hT : T' ⊆ T) (hc : c ≤ c') (h : Extends n S T c) :
    Extends n S' T' c' := by
  intro C hF hB hW
  obtain ⟨C', hF', hB', hsz, hkeep, hT'⟩ := h C hF hB (fun f hf => hW f (hS hf))
  exact ⟨C', hF', hB', by omega, hkeep, fun f hf => hT' f (hT hf)⟩

lemma Extends.trans {n : ℕ} {S T₁ T₂ : Set (Sig n)} {c₁ c₂ : ℕ}
    (h₁ : Extends n S T₁ c₁) (h₂ : Extends n (S ∪ T₁) T₂ c₂) :
    Extends n S (T₁ ∪ T₂) (c₁ + c₂) := by
  intro C hF hB hS
  obtain ⟨C₁, hF₁, hB₁, hsz₁, hkeep₁, hT₁⟩ := h₁ C hF hB hS
  have hST₁ : ∀ f ∈ S ∪ T₁, HasWire C₁ f := by
    rintro f (hf | hf)
    · exact hkeep₁ f (hS f hf)
    · exact hT₁ f hf
  obtain ⟨C₂, hF₂, hB₂, hsz₂, hkeep₂, hT₂⟩ := h₂ C₁ hF₁ hB₁ hST₁
  refine ⟨C₂, hF₂, hB₂, by omega, fun f hw => hkeep₂ f (hkeep₁ f hw), ?_⟩
  rintro f (hf | hf)
  · exact hkeep₂ f (hT₁ f hf)
  · exact hT₂ f hf

lemma Extends.seq {n : ℕ} {S T₁ T₂ : Set (Sig n)} {c₁ c₂ : ℕ}
    (h₁ : Extends n S T₁ c₁) (h₂ : Extends n (S ∪ T₁) T₂ c₂) :
    Extends n S T₂ (c₁ + c₂) :=
  (h₁.trans h₂).mono Set.Subset.rfl Set.subset_union_right le_rfl

lemma Extends.union {n : ℕ} {S T₁ T₂ : Set (Sig n)} {c₁ c₂ : ℕ}
    (h₁ : Extends n S T₁ c₁) (h₂ : Extends n S T₂ c₂) :
    Extends n S (T₁ ∪ T₂) (c₁ + c₂) :=
  h₁.trans (h₂.mono Set.subset_union_left Set.Subset.rfl le_rfl)

lemma Extends.parallel_fin {n k : ℕ} {S : Set (Sig n)}
    {T : Fin k → Set (Sig n)} {c : Fin k → ℕ}
    (h : ∀ i : Fin k, Extends n S (T i) (c i)) :
    Extends n S (⋃ i : Fin k, T i) (∑ i : Fin k, c i) := by
  induction k with
  | zero =>
    simpa using Extends.empty S
  | succ k ih =>
    have h1 := ih (T := fun i : Fin k => T i.castSucc) (c := fun i : Fin k => c i.castSucc)
      (fun i => h i.castSucc)
    have h2 := h (Fin.last k)
    have hu := h1.union h2
    refine hu.mono Set.Subset.rfl ?_ ?_
    · intro f hf
      rcases Set.mem_iUnion.mp hf with ⟨i, hi⟩
      refine Fin.lastCases ?_ ?_ i hi
      · intro hl; exact Or.inr hl
      · intro j hj; exact Or.inl (Set.mem_iUnion.mpr ⟨j, hj⟩)
    · rw [Fin.sum_univ_castSucc]

lemma Extends.parallel_fin_const {n k : ℕ} {S : Set (Sig n)}
    {T : Fin k → Set (Sig n)} {c : ℕ}
    (h : ∀ i : Fin k, Extends n S (T i) c) :
    Extends n S (⋃ i : Fin k, T i) (k * c) := by
  have h1 := Extends.parallel_fin (c := fun _ => c) h
  simpa using h1

lemma Extends.fold_nat {n : ℕ} (k : ℕ) (A : ℕ → Set (Sig n)) (c : ℕ → ℕ)
    (hstep : ∀ i < k, Extends n (A i) (A (i + 1)) (c i)) :
    Extends n (A 0) (A k) (∑ i ∈ Finset.range k, c i) := by
  induction k with
  | zero =>
    simpa using Extends.of_subset (S := A 0) (T := A 0) Set.Subset.rfl
  | succ k ih =>
    have h1 := ih (fun i hi => hstep i (Nat.lt_succ_of_lt hi))
    have h2 := hstep k (Nat.lt_succ_self k)
    have h3 := h1.seq (h2.mono Set.subset_union_right Set.Subset.rfl le_rfl)
    rw [Finset.sum_range_succ]
    exact h3

lemma Extends.fold_nat_const {n : ℕ} (k : ℕ) (A : ℕ → Set (Sig n)) (c : ℕ)
    (hstep : ∀ i < k, Extends n (A i) (A (i + 1)) c) :
    Extends n (A 0) (A k) (k * c) := by
  have h1 := Extends.fold_nat k A (fun _ => c) hstep
  simpa using h1

lemma Extends.const_bool {n : ℕ} (b : Bool) : Extends n ∅ {fun _ => b} 1 := by
  intro C hF hB _
  let g : Gate := ⟨if b then GateOp.and else GateOp.or, []⟩
  have hgFan : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
    cases b <;> simp [g]
  have hgBack : ∀ i ∈ g.inputs, i < n + C.size := by intro i hi; simp [g] at hi
  obtain ⟨hF', hB', hsz, hkeep, hnew⟩ := push_gate C hF hB g hgFan hgBack
  refine ⟨⟨C.gates ++ [g], 0⟩, hF', hB', by omega, hkeep, ?_⟩
  rintro f rfl
  refine ⟨⟨n + C.size, by rw [hsz]; omega⟩, fun x => ?_⟩
  rw [hnew x]
  cases b <;> simp [g, GateOp.eval]

lemma Extends.not_gate {n : ℕ} (f : Sig n) : Extends n {f} {fun x => !f x} 1 := by
  intro C hF hB hS
  obtain ⟨w, hw⟩ := hS f rfl
  let g : Gate := ⟨GateOp.not, [w.val]⟩
  have hgFan : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
    simp [g]
  have hgBack : ∀ i ∈ g.inputs, i < n + C.size := by
    intro i hi; simp [g] at hi; subst hi; exact w.isLt
  obtain ⟨hF', hB', hsz, hkeep, hnew⟩ := push_gate C hF hB g hgFan hgBack
  refine ⟨⟨C.gates ++ [g], 0⟩, hF', hB', by omega, hkeep, ?_⟩
  rintro f' rfl
  refine ⟨⟨n + C.size, by rw [hsz]; omega⟩, fun x => ?_⟩
  rw [hnew x]; simp only [g, GateOp.eval, List.map_cons, List.map_nil, hw x, List.headD_cons]

lemma Extends.and_gate {n : ℕ} (f₁ f₂ : Sig n) :
    Extends n {f₁, f₂} {fun x => f₁ x && f₂ x} 1 := by
  intro C hF hB hS
  obtain ⟨w₁, hw₁⟩ := hS f₁ (by simp)
  obtain ⟨w₂, hw₂⟩ := hS f₂ (by simp)
  let g : Gate := ⟨GateOp.and, [w₁.val, w₂.val]⟩
  have hgFan : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
    simp [g]
  have hgBack : ∀ i ∈ g.inputs, i < n + C.size := by
    intro i hi; simp [g] at hi; rcases hi with rfl | rfl; exact w₁.isLt; exact w₂.isLt
  obtain ⟨hF', hB', hsz, hkeep, hnew⟩ := push_gate C hF hB g hgFan hgBack
  refine ⟨⟨C.gates ++ [g], 0⟩, hF', hB', by omega, hkeep, ?_⟩
  rintro f' rfl
  refine ⟨⟨n + C.size, by rw [hsz]; omega⟩, fun x => ?_⟩
  rw [hnew x]; simp only [g, GateOp.eval, List.map_cons, List.map_nil, hw₁ x, hw₂ x, List.all_cons, List.all_nil, Bool.and_true, id_eq]

lemma Extends.or_gate {n : ℕ} (f₁ f₂ : Sig n) :
    Extends n {f₁, f₂} {fun x => f₁ x || f₂ x} 1 := by
  intro C hF hB hS
  obtain ⟨w₁, hw₁⟩ := hS f₁ (by simp)
  obtain ⟨w₂, hw₂⟩ := hS f₂ (by simp)
  let g : Gate := ⟨GateOp.or, [w₁.val, w₂.val]⟩
  have hgFan : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
    simp [g]
  have hgBack : ∀ i ∈ g.inputs, i < n + C.size := by
    intro i hi; simp [g] at hi; rcases hi with rfl | rfl; exact w₁.isLt; exact w₂.isLt
  obtain ⟨hF', hB', hsz, hkeep, hnew⟩ := push_gate C hF hB g hgFan hgBack
  refine ⟨⟨C.gates ++ [g], 0⟩, hF', hB', by omega, hkeep, ?_⟩
  rintro f' rfl
  refine ⟨⟨n + C.size, by rw [hsz]; omega⟩, fun x => ?_⟩
  rw [hnew x]; simp only [g, GateOp.eval, List.map_cons, List.map_nil, hw₁ x, hw₂ x, List.any_cons, List.any_nil, Bool.or_false, id_eq]

lemma Extends.xor_gate {n : ℕ} (f₁ f₂ : Sig n) :
    Extends n {f₁, f₂} {fun x => xor (f₁ x) (f₂ x)} 4 := by
  let a : Sig n := fun x => f₁ x || f₂ x
  let b : Sig n := fun x => f₁ x && f₂ x
  let nb : Sig n := fun x => !b x
  have h1 : Extends n {f₁, f₂} {a} 1 := Extends.or_gate f₁ f₂
  have h2 : Extends n {f₁, f₂} {b} 1 := Extends.and_gate f₁ f₂
  have h12 : Extends n {f₁, f₂} {a, b} 2 :=
    (h1.union h2).mono Set.Subset.rfl (by intro z hz; simp at hz ⊢; exact hz.symm) le_rfl
  have h3 : Extends n ({f₁, f₂} ∪ {a, b}) {nb} 1 :=
    (Extends.not_gate b).mono (by intro z hz; simp at hz; subst hz; simp) Set.Subset.rfl le_rfl
  have h123 : Extends n {f₁, f₂} ({a, b} ∪ {nb}) 3 := h12.trans h3
  have h4 : Extends n ({f₁, f₂} ∪ ({a, b} ∪ {nb})) {fun x => a x && nb x} 1 :=
    (Extends.and_gate a nb).mono (by intro z hz; simp at hz; rcases hz with rfl | rfl <;> simp) Set.Subset.rfl le_rfl
  have heq : (fun x => a x && nb x) = (fun x => xor (f₁ x) (f₂ x)) := by
    funext x; simp [a, b, nb]; cases f₁ x <;> cases f₂ x <;> rfl
  rw [heq] at h4
  exact h123.seq h4

lemma Extends.mux_gate {n : ℕ} (s f₁ f₂ : Sig n) :
    Extends n {s, f₁, f₂} {fun x => if s x then f₁ x else f₂ x} 4 := by
  let ns : Sig n := fun x => !s x
  let p₁ : Sig n := fun x => s x && f₁ x
  let p₂ : Sig n := fun x => ns x && f₂ x
  have h1 : Extends n {s, f₁, f₂} {ns} 1 :=
    (Extends.not_gate s).mono (by intro z hz; simp at hz; subst hz; simp) Set.Subset.rfl le_rfl
  have h2 : Extends n {s, f₁, f₂} {p₁} 1 :=
    (Extends.and_gate s f₁).mono (by intro z hz; simp at hz; rcases hz with rfl | rfl <;> simp) Set.Subset.rfl le_rfl
  have h12 := h1.union h2
  have h3 : Extends n ({s, f₁, f₂} ∪ ({ns} ∪ {p₁})) {p₂} 1 :=
    (Extends.and_gate ns f₂).mono (by intro z hz; simp at hz; rcases hz with rfl | rfl <;> simp) Set.Subset.rfl le_rfl
  have h123 := h12.trans h3
  have h4 : Extends n ({s, f₁, f₂} ∪ (({ns} ∪ {p₁}) ∪ {p₂})) {fun x => p₁ x || p₂ x} 1 :=
    (Extends.or_gate p₁ p₂).mono (by intro z hz; simp at hz; rcases hz with rfl | rfl <;> simp) Set.Subset.rfl le_rfl
  have heq : (fun x => p₁ x || p₂ x) = (fun x => if s x then f₁ x else f₂ x) := by
    funext x; simp [p₁, p₂, ns]; cases s x <;> cases f₁ x <;> cases f₂ x <;> rfl
  rw [heq] at h4
  exact (h123.seq h4).mono Set.Subset.rfl Set.Subset.rfl (by omega)

lemma Extends.any_fin {n k : ℕ} (f : Fin k → Sig n) :
    Extends n (Set.range f) {fun x => (List.finRange k).any (fun i => f i x)} (k + 1) := by
  induction k with
  | zero =>
    have h0 : (fun x : Fin n → Bool => (List.finRange 0).any (fun i => f i x)) = fun _ => false := by
      funext x; simp
    rw [h0]
    exact (Extends.const_bool false).mono (Set.empty_subset _) Set.Subset.rfl le_rfl
  | succ k ih =>
    have hih := ih (fun i : Fin k => f i.castSucc)
    have hsub : Set.range (fun i : Fin k => f i.castSucc) ⊆ Set.range f := by
      rintro _ ⟨i, rfl⟩; exact ⟨i.castSucc, rfl⟩
    have h1 : Extends n (Set.range f) {fun x => (List.finRange k).any (fun i => f i.castSucc x)} (k + 1) :=
      hih.mono hsub Set.Subset.rfl le_rfl
    have h2 : Extends n (Set.range f ∪ {fun x => (List.finRange k).any (fun i => f i.castSucc x)})
        {fun x => (List.finRange k).any (fun i => f i.castSucc x) || f (Fin.last k) x} 1 :=
      (Extends.or_gate _ _).mono (by
        intro z hz; simp at hz; rcases hz with rfl | rfl
        · exact Or.inr rfl
        · exact Or.inl ⟨Fin.last k, rfl⟩) Set.Subset.rfl le_rfl
    have heq : (fun x => (List.finRange k).any (fun i => f i.castSucc x) || f (Fin.last k) x) =
        (fun x => (List.finRange (k + 1)).any (fun i => f i x)) := by
      funext x
      rw [Bool.eq_iff_iff]
      simp only [Bool.or_eq_true, List.any_eq_true, List.mem_finRange, true_and]
      constructor
      · rintro (⟨i, hi⟩ | h)
        · exact ⟨i.castSucc, hi⟩
        · exact ⟨Fin.last k, h⟩
      · rintro ⟨i, hi⟩
        refine Fin.lastCases ?_ ?_ i hi
        · intro hl; exact Or.inr hl
        · intro j hj; exact Or.inl ⟨j, hj⟩
    rw [heq] at h2
    exact (h1.seq h2).mono Set.Subset.rfl Set.Subset.rfl (by omega)

lemma Extends.all_fin {n k : ℕ} (f : Fin k → Sig n) :
    Extends n (Set.range f) {fun x => (List.finRange k).all (fun i => f i x)} (k + 1) := by
  induction k with
  | zero =>
    have h0 : (fun x : Fin n → Bool => (List.finRange 0).all (fun i => f i x)) = fun _ => true := by
      funext x; simp
    rw [h0]
    exact (Extends.const_bool true).mono (Set.empty_subset _) Set.Subset.rfl le_rfl
  | succ k ih =>
    have hih := ih (fun i : Fin k => f i.castSucc)
    have hsub : Set.range (fun i : Fin k => f i.castSucc) ⊆ Set.range f := by
      rintro _ ⟨i, rfl⟩; exact ⟨i.castSucc, rfl⟩
    have h1 : Extends n (Set.range f) {fun x => (List.finRange k).all (fun i => f i.castSucc x)} (k + 1) :=
      hih.mono hsub Set.Subset.rfl le_rfl
    have h2 : Extends n (Set.range f ∪ {fun x => (List.finRange k).all (fun i => f i.castSucc x)})
        {fun x => (List.finRange k).all (fun i => f i.castSucc x) && f (Fin.last k) x} 1 :=
      (Extends.and_gate _ _).mono (by
        intro z hz; simp at hz; rcases hz with rfl | rfl
        · exact Or.inr rfl
        · exact Or.inl ⟨Fin.last k, rfl⟩) Set.Subset.rfl le_rfl
    have heq : (fun x => (List.finRange k).all (fun i => f i.castSucc x) && f (Fin.last k) x) =
        (fun x => (List.finRange (k + 1)).all (fun i => f i x)) := by
      funext x
      rw [Bool.eq_iff_iff]
      simp only [Bool.and_eq_true, List.all_eq_true, List.mem_finRange, forall_const]
      constructor
      · rintro ⟨h, hl⟩ i
        exact Fin.lastCases hl h i
      · intro h
        exact ⟨fun i => h i.castSucc, h (Fin.last k)⟩
    rw [heq] at h2
    exact (h1.seq h2).mono Set.Subset.rfl Set.Subset.rfl (by omega)

lemma Extends.add_const {n : ℕ} {S : Set (Sig n)} (b : Bool) : Extends n S {fun _ => b} 1 :=
  (Extends.const_bool b).mono (Set.empty_subset _) Set.Subset.rfl le_rfl

lemma Extends.add_not {n : ℕ} {S : Set (Sig n)} {f : Sig n} (hf : f ∈ S) :
    Extends n S {fun x => !f x} 1 :=
  (Extends.not_gate f).mono (by simpa using hf) Set.Subset.rfl le_rfl

lemma Extends.add_and {n : ℕ} {S : Set (Sig n)} {f g : Sig n} (hf : f ∈ S) (hg : g ∈ S) :
    Extends n S {fun x => f x && g x} 1 :=
  (Extends.and_gate f g).mono
    (by intro z hz; simp at hz; rcases hz with rfl | rfl; exact hf; exact hg) Set.Subset.rfl le_rfl

lemma Extends.add_or {n : ℕ} {S : Set (Sig n)} {f g : Sig n} (hf : f ∈ S) (hg : g ∈ S) :
    Extends n S {fun x => f x || g x} 1 :=
  (Extends.or_gate f g).mono
    (by intro z hz; simp at hz; rcases hz with rfl | rfl; exact hf; exact hg) Set.Subset.rfl le_rfl

lemma Extends.add_xor {n : ℕ} {S : Set (Sig n)} {f g : Sig n} (hf : f ∈ S) (hg : g ∈ S) :
    Extends n S {fun x => xor (f x) (g x)} 4 :=
  (Extends.xor_gate f g).mono
    (by intro z hz; simp at hz; rcases hz with rfl | rfl; exact hf; exact hg) Set.Subset.rfl le_rfl

lemma Extends.add_mux {n : ℕ} {S : Set (Sig n)} {s f g : Sig n}
    (hs : s ∈ S) (hf : f ∈ S) (hg : g ∈ S) :
    Extends n S {fun x => if s x then f x else g x} 4 :=
  (Extends.mux_gate s f g).mono
    (by intro z hz; simp at hz; rcases hz with rfl | rfl | rfl; exact hs; exact hf; exact hg)
    Set.Subset.rfl le_rfl

lemma Extends.add_xor_and {n : ℕ} {S : Set (Sig n)} {a c b : Sig n}
    (ha : a ∈ S) (hc : c ∈ S) (hb : b ∈ S) :
    Extends n S {fun x => if c x then xor (a x) (b x) else a x} 5 := by
  have h1 := Extends.add_and hc hb
  have h2 := Extends.add_xor (S := S ∪ {fun x => c x && b x}) (Or.inl ha) (Or.inr rfl)
  have heq : (fun x => xor (a x) (c x && b x)) = (fun x => if c x then xor (a x) (b x) else a x) := by
    funext x; cases c x <;> cases a x <;> cases b x <;> rfl
  rw [heq] at h2
  exact h1.seq h2

lemma Extends.add_any_fin {n k : ℕ} {S : Set (Sig n)} (f : Fin k → Sig n)
    (hf : ∀ i, f i ∈ S) :
    Extends n S {fun x => (List.finRange k).any (fun i => f i x)} (k + 1) :=
  (Extends.any_fin f).mono (by rintro _ ⟨i, rfl⟩; exact hf i) Set.Subset.rfl le_rfl

lemma Extends.add_all_fin {n k : ℕ} {S : Set (Sig n)} (f : Fin k → Sig n)
    (hf : ∀ i, f i ∈ S) :
    Extends n S {fun x => (List.finRange k).all (fun i => f i x)} (k + 1) :=
  (Extends.all_fin f).mono (by rintro _ ⟨i, rfl⟩; exact hf i) Set.Subset.rfl le_rfl

lemma Extends.add_and_any_fin {n k : ℕ} {S : Set (Sig n)} (f g : Fin k → Sig n)
    (hf : ∀ i, f i ∈ S) (hg : ∀ i, g i ∈ S) :
    Extends n S {fun x => (List.finRange k).any (fun i => f i x && g i x)} (2 * k + 1) := by
  let p (i : Fin k) : Sig n := fun x => f i x && g i x
  have hp : Extends n S (Set.range p) k := by
    have h := Extends.parallel_fin_const (k := k) (S := S) (T := fun i => {p i}) (c := 1)
      (fun i => Extends.add_and (hf i) (hg i))
    refine h.mono Set.Subset.rfl ?_ (by omega)
    rintro _ ⟨i, rfl⟩; exact Set.mem_iUnion.mpr ⟨i, rfl⟩
  have hany : Extends n (S ∪ Set.range p) {fun x => (List.finRange k).any (fun i => p i x)} (k + 1) :=
    Extends.add_any_fin p (fun i => Or.inr ⟨i, rfl⟩)
  exact (hp.seq hany).mono Set.Subset.rfl Set.Subset.rfl (by omega)

lemma Extends.add_range_fin {n k : ℕ} {S : Set (Sig n)} {f : Fin k → Sig n} {c : ℕ}
    (h : ∀ i : Fin k, Extends n S {f i} c) :
    Extends n S (Set.range f) (k * c) := by
  have hp := Extends.parallel_fin_const (k := k) (S := S) (T := fun i => {f i}) (c := c) h
  refine hp.mono Set.Subset.rfl ?_ le_rfl
  rintro _ ⟨i, rfl⟩; exact Set.mem_iUnion.mpr ⟨i, rfl⟩

lemma Extends.add_range_prod {n R C : ℕ} {S : Set (Sig n)} {f : Fin R → Fin C → Sig n} {c : ℕ}
    (h : ∀ (r : Fin R) (j : Fin C), Extends n S {f r j} c) :
    Extends n S (Set.range (fun p : Fin R × Fin C => f p.1 p.2)) (R * (C * c)) := by
  have hp := Extends.parallel_fin_const (k := R) (S := S)
    (T := fun r : Fin R => Set.range (fun j : Fin C => f r j)) (c := C * c)
    (fun r => Extends.add_range_fin (h r))
  refine hp.mono Set.Subset.rfl ?_ le_rfl
  rintro _ ⟨⟨r, j⟩, rfl⟩; exact Set.mem_iUnion.mpr ⟨r, ⟨j, rfl⟩⟩

lemma Extends.maj_gate {n : ℕ} (a b c : Sig n) :
    Extends n {a, b, c} {fun x => (a x && b x) || ((a x && c x) || (b x && c x))} 5 := by
  let ab : Sig n := fun x => a x && b x
  let ac : Sig n := fun x => a x && c x
  let bc : Sig n := fun x => b x && c x
  have h1 : Extends n {a, b, c} {ab} 1 :=
    (Extends.and_gate a b).mono (by intro z hz; simp at hz; rcases hz with rfl | rfl <;> simp) Set.Subset.rfl le_rfl
  have h2 : Extends n {a, b, c} {ac} 1 :=
    (Extends.and_gate a c).mono (by intro z hz; simp at hz; rcases hz with rfl | rfl <;> simp) Set.Subset.rfl le_rfl
  have h3 : Extends n {a, b, c} {bc} 1 :=
    (Extends.and_gate b c).mono (by intro z hz; simp at hz; rcases hz with rfl | rfl <;> simp) Set.Subset.rfl le_rfl
  have h123 := (h1.union h2).union h3
  have h4 : Extends n ({a, b, c} ∪ (({ab} ∪ {ac}) ∪ {bc})) {fun x => ac x || bc x} 1 :=
    (Extends.or_gate ac bc).mono (by intro z hz; simp at hz; rcases hz with rfl | rfl <;> simp) Set.Subset.rfl le_rfl
  have h1234 := h123.trans h4
  have h5 : Extends n ({a, b, c} ∪ ((({ab} ∪ {ac}) ∪ {bc}) ∪ {fun x => ac x || bc x}))
      {fun x => ab x || (ac x || bc x)} 1 :=
    (Extends.or_gate ab (fun x => ac x || bc x)).mono
      (by intro z hz; simp at hz; rcases hz with rfl | rfl <;> simp) Set.Subset.rfl le_rfl
  exact (h1234.seq h5).mono Set.Subset.rfl Set.Subset.rfl (by omega)

/-! ### Part 1b: Bit-level `ZMod (2^B)` Arithmetic -/

abbrev WordSig (n B : ℕ) := (Fin n → Bool) → ZMod (2 ^ B)

def wordBits {n B : ℕ} (f : WordSig n B) : Set (Sig n) :=
  Set.range (fun j : Fin B => fun x => (f x).val.testBit j.val)

def rippleCarry (B : ℕ) (c0 : Bool) (u v : Fin B → Bool) : ℕ → Bool
  | 0 => c0
  | k + 1 =>
    if h : k < B then
      let a := u ⟨k, h⟩
      let b := v ⟨k, h⟩
      let c := rippleCarry B c0 u v k
      (a && b) || ((a && c) || (b && c))
    else false

def rippleSum (B : ℕ) (c0 : Bool) (u v : Fin B → Bool) (j : Fin B) : Bool :=
  xor (xor (u j) (v j)) (rippleCarry B c0 u v j.val)

def natOfBits {B : ℕ} (u : Fin B → Bool) : ℕ :=
  ∑ j : Fin B, (u j).toNat * 2 ^ j.val

lemma natOfBits_lt {B : ℕ} (u : Fin B → Bool) : natOfBits u < 2 ^ B := by
  unfold natOfBits
  induction B with
  | zero => simp
  | succ B ih =>
    rw [Fin.sum_univ_castSucc]
    have h1 := ih (fun j => u j.castSucc)
    have h2 : (u (Fin.last B)).toNat ≤ 1 := by cases u (Fin.last B) <;> decide
    have hmul : (u (Fin.last B)).toNat * 2 ^ B ≤ 1 * 2 ^ B := Nat.mul_le_mul_right (2 ^ B) h2
    have hpow : 2 ^ (B + 1) = 2 ^ B + 2 ^ B := by ring
    simp only [Fin.val_castSucc, Fin.val_last]
    omega

lemma natOfBits_testBit {B : ℕ} (u : Fin B → Bool) (j : Fin B) :
    (natOfBits u).testBit j.val = u j := by
  induction B with
  | zero => exact j.elim0
  | succ B ih =>
    unfold natOfBits
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    have hlt : (∑ i : Fin B, (u i.castSucc).toNat * 2 ^ i.val) < 2 ^ B :=
      natOfBits_lt (fun i => u i.castSucc)
    by_cases hj : j.val < B
    · have htb : ∀ (a b : ℕ), (a + b * 2 ^ B).testBit j.val = a.testBit j.val := fun a b => by
        simp only [Nat.testBit, Nat.shiftRight_eq_div_pow]
        have hpow : 2 ^ B = 2 ^ (B - j.val) * 2 ^ j.val := by
          rw [← pow_add, Nat.sub_add_cancel (le_of_lt hj)]
        have hmul : b * 2 ^ B = (b * 2 ^ (B - j.val)) * 2 ^ j.val := by rw [hpow]; ring
        rw [hmul, Nat.add_mul_div_right _ _ (by positivity)]
        have h2dvd : 2 ∣ b * 2 ^ (B - j.val) := by
          have : 2 ^ (B - j.val) = 2 * 2 ^ (B - j.val - 1) := by
            conv_lhs => rw [show B - j.val = (B - j.val - 1) + 1 by omega, pow_succ, mul_comm]
          rw [this]; exact ⟨b * 2 ^ (B - j.val - 1), by ring⟩
        rcases h2dvd with ⟨q, hq⟩
        rw [hq, Nat.and_comm 1, Nat.and_comm 1, Nat.and_one_is_mod, Nat.and_one_is_mod, Nat.add_mul_mod_self_left]
      rw [htb]
      exact ih (fun i => u i.castSucc) ⟨j.val, hj⟩
    · have hjeq : j = Fin.last B := Fin.ext (by have := j.isLt; simp only [Fin.val_last]; omega)
      subst hjeq
      simp only [Fin.val_last]
      rw [Nat.testBit, Nat.shiftRight_eq_div_pow]
      have hdiv : (∑ i : Fin B, (u i.castSucc).toNat * 2 ^ i.val + (u (Fin.last B)).toNat * 2 ^ B) / 2 ^ B =
          (u (Fin.last B)).toNat := by
        rw [Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hlt, zero_add]
      rw [hdiv]
      cases u (Fin.last B) <;> decide

lemma natOfBits_of_testBit {B : ℕ} (m : ℕ) (hm : m < 2 ^ B) :
    natOfBits (fun j : Fin B => m.testBit j.val) = m := by
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k < B
  · exact natOfBits_testBit (fun j : Fin B => m.testBit j.val) ⟨k, hk⟩
  · have hlt := natOfBits_lt (fun j : Fin B => m.testBit j.val)
    rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by decide) (by omega)))]
    rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hm (Nat.pow_le_pow_right (by decide) (by omega)))]

lemma ripple_inv (B : ℕ) (c0 : Bool) (u v : Fin B → Bool) :
    ∀ k ≤ B,
      (∑ i ∈ Finset.range k, (if h : i < B then (rippleSum B c0 u v ⟨i, h⟩).toNat * 2 ^ i else 0)) +
        (rippleCarry B c0 u v k).toNat * 2 ^ k =
      c0.toNat +
        (∑ i ∈ Finset.range k, (if h : i < B then (u ⟨i, h⟩).toNat * 2 ^ i else 0)) +
        (∑ i ∈ Finset.range k, (if h : i < B then (v ⟨i, h⟩).toNat * 2 ^ i else 0)) := by
  intro k hk
  induction k with
  | zero => simp [rippleCarry]
  | succ k ih =>
    have hlt : k < B := by omega
    have hih := ih (by omega)
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
    simp only [hlt, dite_true]
    have hstep : (rippleSum B c0 u v ⟨k, hlt⟩).toNat + 2 * (rippleCarry B c0 u v (k + 1)).toNat =
        (u ⟨k, hlt⟩).toNat + (v ⟨k, hlt⟩).toNat + (rippleCarry B c0 u v k).toNat := by
      simp only [rippleSum, rippleCarry, hlt, dite_true]
      cases u ⟨k, hlt⟩ <;> cases v ⟨k, hlt⟩ <;> cases rippleCarry B c0 u v k <;> decide
    have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
    rw [hpow]
    linarith [congrArg (· * 2 ^ k) hstep]

lemma rippleSum_zmod_add {B : ℕ} (a b : ZMod (2 ^ B)) (j : Fin B) :
    rippleSum B false (fun i => a.val.testBit i.val) (fun i => b.val.testBit i.val) j =
      (a + b).val.testBit j.val := by
  haveI : NeZero (2 ^ B) := ⟨by positivity⟩
  have hinv := ripple_inv B false (fun i => a.val.testBit i.val) (fun i => b.val.testBit i.val) B le_rfl
  have hsum_eq (f : Fin B → ℕ) :
      (∑ i ∈ Finset.range B, if h : i < B then f ⟨i, h⟩ else 0) = ∑ i : Fin B, f i := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => if h : i < B then f ⟨i, h⟩ else 0)]
    refine Finset.sum_congr rfl fun i _ => by simp [i.isLt]
  rw [hsum_eq (fun i => (rippleSum B false (fun i => a.val.testBit i.val) (fun i => b.val.testBit i.val) i).toNat * 2 ^ i.val),
    hsum_eq (fun i => (a.val.testBit i.val).toNat * 2 ^ i.val),
    hsum_eq (fun i => (b.val.testBit i.val).toNat * 2 ^ i.val)] at hinv
  change natOfBits (rippleSum B false _ _) + (rippleCarry B false _ _ B).toNat * 2 ^ B =
    0 + natOfBits (fun i : Fin B => a.val.testBit i.val) +
      natOfBits (fun i : Fin B => b.val.testBit i.val) at hinv
  rw [natOfBits_of_testBit a.val (ZMod.val_lt a), natOfBits_of_testBit b.val (ZMod.val_lt b), zero_add] at hinv
  have hmod : natOfBits (rippleSum B false (fun i => a.val.testBit i.val) (fun i => b.val.testBit i.val)) =
      (a + b).val := by
    rw [ZMod.val_add]
    have hlt := natOfBits_lt (rippleSum B false (fun i => a.val.testBit i.val) (fun i => b.val.testBit i.val))
    have h1 := congrArg (· % 2 ^ B) hinv
    simp only [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlt] at h1
    exact h1
  rw [← hmod, natOfBits_testBit]

lemma Extends.ripple {n B : ℕ} (c0 : Bool) (u v : Fin B → Sig n) :
    Extends n (Set.range u ∪ Set.range v)
      (Set.range (fun j : Fin B => fun x => rippleSum B c0 (fun i => u i x) (fun i => v i x) j))
      (14 * B + 1) := by
  let carrySig (k : ℕ) : Sig n := fun x => rippleCarry B c0 (fun i => u i x) (fun i => v i x) k
  let Base : Set (Sig n) := Set.range u ∪ Set.range v
  let A (k : ℕ) : Set (Sig n) := Base ∪ {carrySig k}
  have h0 : Extends n Base (A 0) 1 := by
    have hc : Extends n ∅ {carrySig 0} 1 := by
      change Extends n ∅ {fun _ => c0} 1
      exact Extends.const_bool c0
    exact (Extends.of_subset Set.Subset.rfl).union (hc.mono (Set.empty_subset _) Set.Subset.rfl le_rfl)
  have hstep : ∀ (k : ℕ) (hk : k < B), Extends n (A k) (A (k + 1) ∪ {fun x => rippleSum B c0 (fun i => u i x) (fun i => v i x) ⟨k, hk⟩}) 13 := by
    intro k hk
    let uk : Sig n := u ⟨k, hk⟩
    let vk : Sig n := v ⟨k, hk⟩
    let ck : Sig n := carrySig k
    have hmaj : Extends n (A k) {carrySig (k + 1)} 5 := by
      have heq : carrySig (k + 1) = (fun x => (uk x && vk x) || ((uk x && ck x) || (vk x && ck x))) := by
        funext x; simp [carrySig, rippleCarry, hk, uk, vk, ck]
      rw [heq]
      exact (Extends.maj_gate uk vk ck).mono (by
        intro z hz; simp at hz; rcases hz with rfl | rfl | rfl
        · exact Or.inl (Or.inl ⟨⟨k, hk⟩, rfl⟩)
        · exact Or.inl (Or.inr ⟨⟨k, hk⟩, rfl⟩)
        · exact Or.inr rfl) Set.Subset.rfl le_rfl
    have hxor1 : Extends n (A k) {fun x => xor (uk x) (vk x)} 4 :=
      (Extends.xor_gate uk vk).mono (by
        intro z hz; simp at hz; rcases hz with rfl | rfl
        · exact Or.inl (Or.inl ⟨⟨k, hk⟩, rfl⟩)
        · exact Or.inl (Or.inr ⟨⟨k, hk⟩, rfl⟩)) Set.Subset.rfl le_rfl
    have hxor2 : Extends n (A k ∪ {fun x => xor (uk x) (vk x)})
        {fun x => rippleSum B c0 (fun i => u i x) (fun i => v i x) ⟨k, hk⟩} 4 :=
      (Extends.xor_gate (fun x => xor (uk x) (vk x)) ck).mono (by
        intro z hz; simp at hz; rcases hz with rfl | rfl
        · exact Or.inr rfl
        · exact Or.inl (Or.inr rfl)) Set.Subset.rfl le_rfl
    have hsum := hxor1.seq hxor2
    have hall := hmaj.union hsum
    have hbase : Extends n (A k) Base 0 := Extends.of_subset Set.subset_union_left
    have hcomb := hbase.union hall
    exact hcomb.mono Set.Subset.rfl (by
      intro z hz
      rcases hz with (hb | rfl) | rfl
      · exact Or.inl hb
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)) (by omega)
  let Inv (k : ℕ) : Set (Sig n) :=
    A k ∪ {f | ∃ i : Fin B, i.val < k ∧ f = fun x => rippleSum B c0 (fun r => u r x) (fun r => v r x) i}
  have hfold := Extends.fold_nat_const B Inv 13 (fun k hk => by
    have hs := (hstep k hk).mono (Set.subset_union_left : A k ⊆ Inv k) Set.Subset.rfl le_rfl
    have hkeep : Extends n (Inv k) (Inv k) 0 := Extends.of_subset Set.Subset.rfl
    refine (hkeep.union hs).mono Set.Subset.rfl ?_ (by omega)
    intro z hz
    rcases hz with hA | ⟨i, hi, rfl⟩
    · exact Or.inr (Or.inl hA)
    · by_cases hlt : i.val < k
      · exact Or.inl (Or.inr ⟨i, hlt, rfl⟩)
      · have hieq : i = ⟨k, hk⟩ := Fin.ext (by dsimp only; omega)
        subst hieq
        exact Or.inr (Or.inr rfl))
  have hstart : Extends n Base (Inv 0) 1 :=
    h0.mono Set.Subset.rfl (by intro z hz; rcases hz with h | ⟨i, hi, _⟩; exact h; omega) le_rfl
  refine (hstart.seq (hfold.mono Set.subset_union_right Set.Subset.rfl le_rfl)).mono Set.Subset.rfl ?_ (by omega)
  rintro z ⟨i, rfl⟩
  exact Or.inr ⟨i, i.isLt, rfl⟩

lemma Extends.word_add {n B : ℕ} (a b : WordSig n B) :
    Extends n (wordBits a ∪ wordBits b) (wordBits (fun x => a x + b x)) (14 * B + 1) := by
  have h := Extends.ripple false
    (fun i : Fin B => fun x => (a x).val.testBit i.val)
    (fun i : Fin B => fun x => (b x).val.testBit i.val)
  refine h.mono Set.Subset.rfl ?_ le_rfl
  rintro _ ⟨j, rfl⟩
  refine ⟨j, ?_⟩
  funext x
  exact rippleSum_zmod_add (a x) (b x) j

lemma Extends.word_const {n B : ℕ} (c : ZMod (2 ^ B)) :
    Extends n ∅ (wordBits (fun _ => c)) B := by
  have hp := Extends.parallel_fin_const (n := n) (k := B) (S := ∅)
    (T := fun j : Fin B => {fun _ : Fin n → Bool => c.val.testBit j.val}) (c := 1)
    (fun j => Extends.const_bool (n := n) (c.val.testBit j.val))
  refine hp.mono Set.Subset.rfl ?_ (by omega)
  rintro _ ⟨j, rfl⟩; exact Set.mem_iUnion.mpr ⟨j, rfl⟩

lemma Extends.word_mux {n B : ℕ} (s : Sig n) (a b : WordSig n B) :
    Extends n ({s} ∪ wordBits a ∪ wordBits b)
      (wordBits (fun x => if s x then a x else b x)) (4 * B) := by
  have hp := Extends.parallel_fin_const (k := B)
    (S := {s} ∪ wordBits a ∪ wordBits b)
    (T := fun j : Fin B => {fun x => (if s x then a x else b x).val.testBit j.val}) (c := 4)
    (fun j => by
      have hm := Extends.mux_gate s (fun x => (a x).val.testBit j.val) (fun x => (b x).val.testBit j.val)
      have heq : (fun x => if s x then (a x).val.testBit j.val else (b x).val.testBit j.val) =
          (fun x => (if s x then a x else b x).val.testBit j.val) := by
        funext x; cases s x <;> rfl
      rw [heq] at hm
      exact hm.mono (by
        intro z hz; simp at hz; rcases hz with rfl | rfl | rfl
        · exact Or.inl (Or.inl rfl)
        · exact Or.inl (Or.inr ⟨j, rfl⟩)
        · exact Or.inr ⟨j, rfl⟩) Set.Subset.rfl le_rfl)
  refine hp.mono Set.Subset.rfl ?_ (by omega)
  rintro _ ⟨j, rfl⟩; exact Set.mem_iUnion.mpr ⟨j, rfl⟩


/-! ### Part 1c: One-hot small counters (`Fin (L + 1) → Bool`) -/

def popCount {L : ℕ} (v : Fin L → Bool) : ℕ :=
  (Finset.univ.filter (fun i : Fin L => v i = true)).card

lemma popCount_le {L : ℕ} (v : Fin L → Bool) : popCount v ≤ L := by
  calc popCount v ≤ (Finset.univ : Finset (Fin L)).card := Finset.card_filter_le _ _
    _ = L := Fintype.card_fin L

def popCountStep {L : ℕ} (v : Fin L → Bool) : ℕ → Fin (L + 1) → Bool
  | 0, k => decide (k.val = 0)
  | m + 1, k =>
    if hm : m < L then
      if v ⟨m, hm⟩ then
        if hk : 0 < k.val then popCountStep v m ⟨k.val - 1, by omega⟩ else false
      else popCountStep v m k
    else popCountStep v m k

lemma popCountStep_spec {L : ℕ} (v : Fin L → Bool) :
    ∀ m ≤ L, ∀ k : Fin (L + 1),
      popCountStep v m k = decide ((Finset.univ.filter (fun i : Fin L => i.val < m ∧ v i = true)).card = k.val) := by
  intro m hm
  induction m with
  | zero =>
    intro k
    simp only [popCountStep, Nat.not_lt_zero, false_and, Finset.filter_false, Finset.card_empty]
    by_cases hk : k.val = 0 <;> simp [hk, eq_comm]
  | succ m ih =>
    intro k
    have hlt : m < L := by omega
    let prev := Finset.univ.filter (fun i : Fin L => i.val < m ∧ v i = true)
    have hnotmem : (⟨m, hlt⟩ : Fin L) ∉ prev := by simp [prev]
    simp only [popCountStep, hlt, dite_true]
    by_cases hv : v ⟨m, hlt⟩ = true
    · have hset : Finset.univ.filter (fun i : Fin L => i.val < m + 1 ∧ v i = true) = insert ⟨m, hlt⟩ prev := by
        ext i; simp only [prev, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
        constructor
        · rintro ⟨hi, hvi⟩
          by_cases h : i.val < m
          · exact Or.inr ⟨h, hvi⟩
          · exact Or.inl (Fin.ext (by dsimp only; omega))
        · rintro (rfl | ⟨hi, hvi⟩)
          · exact ⟨by dsimp only; omega, hv⟩
          · exact ⟨by omega, hvi⟩
      rw [hset, Finset.card_insert_of_notMem hnotmem, if_pos hv]
      by_cases hk : 0 < k.val
      · rw [dif_pos hk, ih (by omega)]
        by_cases hcard : prev.card = k.val - 1
        · rw [decide_eq_true hcard, decide_eq_true (by omega)]
        · rw [decide_eq_false hcard, decide_eq_false (by omega)]
      · rw [dif_neg hk, decide_eq_false (by omega)]
    · have hset : Finset.univ.filter (fun i : Fin L => i.val < m + 1 ∧ v i = true) = prev := by
        ext i; simp only [prev, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨hi, hvi⟩
          refine ⟨?_, hvi⟩
          by_contra h
          have heq : i = ⟨m, hlt⟩ := Fin.ext (by dsimp only; omega)
          subst heq; exact hv hvi
        · rintro ⟨hi, hvi⟩; exact ⟨by omega, hvi⟩
      rw [hset, if_neg hv, ih (by omega)]

lemma popCountStep_end {L : ℕ} (v : Fin L → Bool) (k : Fin (L + 1)) :
    popCountStep v L k = decide (popCount v = k.val) := by
  rw [popCountStep_spec v L le_rfl k]
  have h : Finset.univ.filter (fun i : Fin L => i.val < L ∧ v i = true) =
      Finset.univ.filter (fun i : Fin L => v i = true) := by
    ext i; simp [i.isLt]
  unfold popCount; rw [h]

lemma Extends.popCountOH {n L : ℕ} (v : Fin L → Sig n) :
    Extends n (Set.range v)
      (Set.range (fun k : Fin (L + 1) => fun x => decide (popCount (fun i => v i x) = k.val)))
      (4 * (L + 1) * (L + 1) + 2) := by
  let Inv (m : ℕ) : Set (Sig n) :=
    Set.range v ∪ {fun _ => false} ∪
      Set.range (fun k : Fin (L + 1) => fun x => popCountStep (fun i => v i x) m k)
  have h0 : Extends n (Set.range v) (Inv 0) (L + 2) := by
    have hf := (Extends.const_bool false).mono (Set.empty_subset (Set.range v)) Set.Subset.rfl le_rfl
    have hinit : Extends n (Set.range v)
        (Set.range (fun k : Fin (L + 1) => fun x => popCountStep (fun i => v i x) 0 k)) (L + 1) := by
      have hp := Extends.parallel_fin_const (k := L + 1) (S := Set.range v)
        (T := fun k : Fin (L + 1) => {fun _ => decide (k.val = 0)}) (c := 1)
        (fun k => (Extends.const_bool _).mono (Set.empty_subset _) Set.Subset.rfl le_rfl)
      refine hp.mono Set.Subset.rfl ?_ (by omega)
      rintro _ ⟨k, rfl⟩; exact Set.mem_iUnion.mpr ⟨k, rfl⟩
    exact (((Extends.of_subset Set.Subset.rfl).union hf).union hinit).mono
      Set.Subset.rfl Set.Subset.rfl (by omega)
  have hstep : ∀ m < L, Extends n (Inv m) (Inv (m + 1)) (4 * (L + 1)) := by
    intro m hm
    have hnext : Extends n (Inv m)
        (Set.range (fun k : Fin (L + 1) => fun x => popCountStep (fun i => v i x) (m + 1) k))
        (4 * (L + 1)) := by
      have hp := Extends.parallel_fin_const (k := L + 1) (S := Inv m)
        (T := fun k : Fin (L + 1) => {fun x => popCountStep (fun i => v i x) (m + 1) k}) (c := 4)
        (fun k => by
          by_cases hk : 0 < k.val
          · have heq : (fun x => popCountStep (fun i => v i x) (m + 1) k) =
                (fun x => if v ⟨m, hm⟩ x then popCountStep (fun i => v i x) m ⟨k.val - 1, by omega⟩
                  else popCountStep (fun i => v i x) m k) := by
              funext x; simp [popCountStep, hm, hk]
            rw [heq]
            exact (Extends.mux_gate _ _ _).mono (by
              intro z hz; simp at hz; rcases hz with rfl | rfl | rfl
              · exact Or.inl (Or.inl ⟨⟨m, hm⟩, rfl⟩)
              · exact Or.inr ⟨⟨k.val - 1, by omega⟩, rfl⟩
              · exact Or.inr ⟨k, rfl⟩) Set.Subset.rfl le_rfl
          · have heq : (fun x => popCountStep (fun i => v i x) (m + 1) k) =
                (fun x => if v ⟨m, hm⟩ x then false else popCountStep (fun i => v i x) m k) := by
              funext x; simp [popCountStep, hm, hk]
            rw [heq]
            exact (Extends.mux_gate _ _ _).mono (by
              intro z hz; simp at hz; rcases hz with rfl | rfl | rfl
              · exact Or.inl (Or.inl ⟨⟨m, hm⟩, rfl⟩)
              · exact Or.inl (Or.inr rfl)
              · exact Or.inr ⟨k, rfl⟩) Set.Subset.rfl le_rfl)
      refine hp.mono Set.Subset.rfl ?_ (by omega)
      rintro _ ⟨k, rfl⟩; exact Set.mem_iUnion.mpr ⟨k, rfl⟩
    exact ((Extends.of_subset Set.subset_union_left).union hnext).mono Set.Subset.rfl Set.Subset.rfl (by omega)
  have hfold := Extends.fold_nat_const L Inv (4 * (L + 1)) hstep
  refine (h0.seq (hfold.mono Set.subset_union_right Set.Subset.rfl le_rfl)).mono
    Set.Subset.rfl ?_ ?_
  · rintro _ ⟨k, rfl⟩
    right
    refine ⟨k, ?_⟩
    funext x; exact popCountStep_end (fun i => v i x) k
  · nlinarith

/-! ### Part 2: `Bool`/`ZMod 2` Linear Algebra Primitives (`rrefAug`, `kernel`, `greedyBasis`, `compact`, `gaussFactor`) -/

abbrev F2 := ZMod 2

def b2f (b : Bool) : F2 := if b then 1 else 0
def f2b (x : F2) : Bool := decide (x ≠ 0)

@[simp] lemma b2f_false : b2f false = 0 := rfl
@[simp] lemma b2f_true : b2f true = 1 := rfl
@[simp] lemma f2b_b2f (b : Bool) : f2b (b2f b) = b := by cases b <;> decide
@[simp] lemma b2f_f2b (x : F2) : b2f (f2b x) = x := by rcases x with ⟨v, hv⟩; interval_cases v <;> rfl

lemma b2f_xor (a b : Bool) : b2f (xor a b) = b2f a + b2f b := by
  cases a <;> cases b <;> decide

lemma b2f_and (a b : Bool) : b2f (a && b) = b2f a * b2f b := by
  cases a <;> cases b <;> decide

lemma f2_add_self (x : F2) : x + x = 0 := by fin_cases x <;> decide

lemma b2f_inj {a b : Bool} (h : b2f a = b2f b) : a = b := by
  have := congrArg f2b h; simpa using this


-- Extra combinator: fold XOR over Fin k
lemma Extends.xor_fin {n k : ℕ} (f : Fin k → Sig n) :
    Extends n (Set.range f)
      {fun x => (List.finRange k).foldl (fun acc i => xor acc (f i x)) false}
      (4 * k + 1) := by
  let accSig (m : ℕ) : Sig n := fun x =>
    ((List.finRange k).take m).foldl (fun acc i => xor acc (f i x)) false
  let Inv (m : ℕ) : Set (Sig n) := Set.range f ∪ {accSig m}
  have h0 : Extends n (Set.range f) (Inv 0) 1 := by
    have hc : Extends n (Set.range f) {accSig 0} 1 := by
      have : accSig 0 = fun _ => false := by funext x; simp [accSig]
      rw [this]; exact Extends.add_const false
    exact ((Extends.of_subset Set.Subset.rfl).union hc).mono Set.Subset.rfl Set.Subset.rfl (by omega)
  have hstep : ∀ m < k, Extends n (Inv m) (Inv (m + 1)) 4 := by
    intro m hm
    have htake : (List.finRange k).take (m + 1) = (List.finRange k).take m ++ [⟨m, hm⟩] := by
      rw [List.take_succ_eq_append_getElem (by simp [hm])]
      simp [List.getElem_finRange]
    have heq : accSig (m + 1) = fun x => xor (accSig m x) (f ⟨m, hm⟩ x) := by
      funext x; simp [accSig, htake, List.foldl_append]
    have hx : Extends n (Inv m) {accSig (m + 1)} 4 := by
      rw [heq]; exact Extends.add_xor (Or.inr rfl) (Or.inl ⟨⟨m, hm⟩, rfl⟩)
    exact ((Extends.of_subset Set.subset_union_left).union hx).mono Set.Subset.rfl Set.Subset.rfl (by omega)
  have hfold := Extends.fold_nat_const k Inv 4 hstep
  have hend : accSig k = fun x => (List.finRange k).foldl (fun acc i => xor acc (f i x)) false := by
    funext x; dsimp only [accSig]; rw [List.take_of_length_le (by simp)]
  dsimp only [Inv] at hfold
  rw [hend] at hfold
  exact (h0.seq (hfold.mono Set.subset_union_right Set.Subset.rfl le_rfl)).mono
    Set.Subset.rfl Set.subset_union_right (by omega)

lemma Extends.add_xor_fin {n k : ℕ} {S : Set (Sig n)} (f : Fin k → Sig n)
    (hf : ∀ i, f i ∈ S) :
    Extends n S {fun x => (List.finRange k).foldl (fun acc i => xor acc (f i x)) false} (4 * k + 1) :=
  (Extends.xor_fin f).mono (by rintro _ ⟨i, rfl⟩; exact hf i) Set.Subset.rfl le_rfl

lemma b2f_foldl_xor {ι : Type*} (l : List ι) (f : ι → Bool) (init : Bool) :
    b2f (l.foldl (fun acc i => xor acc (f i)) init) = b2f init + (l.map (fun i => b2f (f i))).sum := by
  induction l generalizing init with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih, b2f_xor]
    ring

lemma b2f_finRange_xor {k : ℕ} (f : Fin k → Bool) :
    b2f ((List.finRange k).foldl (fun acc i => xor acc (f i)) false) = ∑ i : Fin k, b2f (f i) := by
  rw [b2f_foldl_xor, b2f_false, zero_add]
  have h1 : ((List.finRange k).map (fun i => b2f (f i))).sum =
      ((Finset.univ : Finset (Fin k)).val.map (fun i => b2f (f i))).sum := by
    rw [← Multiset.sum_coe, ← Multiset.map_coe]
    rfl
  exact h1

lemma f2_sub_eq_add (x y : F2) : x - y = x + y := by
  fin_cases x <;> fin_cases y <;> decide

lemma f2b_add (x y : F2) : f2b (x + y) = xor (f2b x) (f2b y) := by
  fin_cases x <;> fin_cases y <;> decide

lemma f2b_mul (x y : F2) : f2b (x * y) = (f2b x && f2b y) := by
  fin_cases x <;> fin_cases y <;> decide

lemma f2_cases (x : F2) : x = 0 ∨ x = 1 := by
  rcases x with ⟨v, hv⟩; interval_cases v
  · exact Or.inl rfl
  · exact Or.inr rfl

/-! ### Part 2: Incremental Echelon / RREF Pivot Table (`PTab N`) -/

structure PTab (N : ℕ) where
  hasPiv : Fin N → Bool
  row : Fin N → Fin N → Bool

def PTab.empty (N : ℕ) : PTab N := ⟨fun _ => false, fun _ _ => false⟩

def PTab.redStep {N : ℕ} (T : PTab N) (p : Fin N) (w : Fin N → Bool) : Fin N → Bool :=
  fun j => if T.hasPiv p && w p then xor (w j) (T.row p j) else w j

def PTab.reduce {N : ℕ} (T : PTab N) (w : Fin N → Bool) : Fin N → Bool :=
  (List.finRange N).foldl (fun acc p => T.redStep p acc) w

def pFirstTrue {N : ℕ} (w : Fin N → Bool) (p : Fin N) : Bool :=
  w p && (List.finRange N).all (fun q => !decide (q < p) || !w q)

def PTab.insert {N : ℕ} (T : PTab N) (v : Fin N → Bool) : PTab N :=
  let w := T.reduce v
  let ft := pFirstTrue w
  ⟨fun p => T.hasPiv p || ft p,
   fun p j => if ft p then w j else T.row p j⟩

def PTab.IsEchelon {N : ℕ} (T : PTab N) : Prop :=
  ∀ p : Fin N, T.hasPiv p = true →
    T.row p p = true ∧ ∀ q : Fin N, q < p → T.row p q = false

def PTab.toSub {N : ℕ} (T : PTab N) : Submodule F2 (Fin N → F2) :=
  Submodule.span F2 { u : Fin N → F2 | ∃ p : Fin N, T.hasPiv p = true ∧ u = fun j => b2f (T.row p j) }

lemma PTab.empty_isEchelon (N : ℕ) : (PTab.empty N).IsEchelon := by
  intro p hp; simp [PTab.empty] at hp

lemma PTab.empty_toSub (N : ℕ) : (PTab.empty N).toSub = ⊥ := by
  simp [PTab.toSub, PTab.empty]

lemma pFirstTrue_iff {N : ℕ} (w : Fin N → Bool) (p : Fin N) :
    pFirstTrue w p = true ↔ w p = true ∧ ∀ q : Fin N, q < p → w q = false := by
  simp only [pFirstTrue, Bool.and_eq_true, List.all_eq_true, List.mem_finRange, true_implies,
    Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, not_lt]
  constructor
  · rintro ⟨hp, hall⟩
    refine ⟨hp, fun q hq => ?_⟩
    rcases hall q with hle | hwf
    · exact absurd hq (not_lt.mpr hle)
    · exact hwf
  · rintro ⟨hp, hall⟩
    refine ⟨hp, fun q => ?_⟩
    by_cases hq : q < p
    · exact Or.inr (hall q hq)
    · exact Or.inl (not_lt.mp hq)

lemma pFirstTrue_unique {N : ℕ} (w : Fin N → Bool) {p₁ p₂ : Fin N}
    (h1 : pFirstTrue w p₁ = true) (h2 : pFirstTrue w p₂ = true) : p₁ = p₂ := by
  rw [pFirstTrue_iff] at h1 h2
  rcases lt_trichotomy p₁ p₂ with hlt | heq | hgt
  · have := h2.2 p₁ hlt; rw [h1.1] at this; exact absurd this (by decide)
  · exact heq
  · have := h1.2 p₂ hgt; rw [h2.1] at this; exact absurd this (by decide)

lemma exists_pFirstTrue_of_ne_false {N : ℕ} (w : Fin N → Bool) (h : ∃ p : Fin N, w p = true) :
    ∃ p : Fin N, pFirstTrue w p = true := by
  let S := Finset.univ.filter (fun p : Fin N => w p = true)
  have hne : S.Nonempty := by
    rcases h with ⟨p, hp⟩
    exact ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩⟩
  refine ⟨S.min' hne, (pFirstTrue_iff w _).mpr ⟨(Finset.mem_filter.mp (S.min'_mem hne)).2, ?_⟩⟩
  intro q hq
  by_contra hqt
  have hqt' : w q = true := by cases h : w q <;> simp_all
  have hmem : q ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hqt'⟩
  exact absurd hq (not_lt.mpr (S.min'_le q hmem))

lemma PTab.redStep_xor {N : ℕ} (T : PTab N) (p : Fin N) (w₁ w₂ : Fin N → Bool) :
    T.redStep p (fun j => xor (w₁ j) (w₂ j)) =
      fun j => xor (T.redStep p w₁ j) (T.redStep p w₂ j) := by
  funext j
  dsimp only [PTab.redStep]
  have h : ∀ a b c d e r : Bool,
      (if a && xor b c then xor (xor d e) r else xor d e) =
      xor (if a && b then xor d r else d) (if a && c then xor e r else e) := by decide
  exact h (T.hasPiv p) (w₁ p) (w₂ p) (w₁ j) (w₂ j) (T.row p j)

lemma PTab.redStep_zero {N : ℕ} (T : PTab N) (p : Fin N) :
    T.redStep p (fun _ => false) = fun _ => false := by
  funext j; simp [PTab.redStep]

lemma PTab.reduce_xor {N : ℕ} (T : PTab N) (w₁ w₂ : Fin N → Bool) :
    T.reduce (fun j => xor (w₁ j) (w₂ j)) =
      fun j => xor (T.reduce w₁ j) (T.reduce w₂ j) := by
  unfold PTab.reduce
  suffices h : ∀ (l : List (Fin N)) (a b : Fin N → Bool),
      l.foldl (fun acc p => T.redStep p acc) (fun j => xor (a j) (b j)) =
        fun j => xor (l.foldl (fun acc p => T.redStep p acc) a j)
          (l.foldl (fun acc p => T.redStep p acc) b j) from h _ w₁ w₂
  intro l
  induction l with
  | nil => intro a b; rfl
  | cons p l ih =>
    intro a b
    simp only [List.foldl_cons, PTab.redStep_xor]
    exact ih _ _

lemma PTab.reduce_zero {N : ℕ} (T : PTab N) :
    T.reduce (fun _ => false) = fun _ => false := by
  unfold PTab.reduce
  suffices h : ∀ (l : List (Fin N)), l.foldl (fun acc p => T.redStep p acc) (fun _ => false) = fun _ => false from h _
  intro l
  induction l with
  | nil => rfl
  | cons p l ih => simp only [List.foldl_cons, PTab.redStep_zero, ih]

lemma PTab.redStep_sub_mem {N : ℕ} (T : PTab N) (p : Fin N) (w : Fin N → Bool) :
    (fun j => b2f (T.redStep p w j) + b2f (w j)) ∈ T.toSub := by
  by_cases h : T.hasPiv p = true ∧ w p = true
  · have heq : (fun j => b2f (T.redStep p w j) + b2f (w j)) = fun j => b2f (T.row p j) := by
      funext j
      simp only [PTab.redStep, h.1, h.2, Bool.and_self, ↓reduceIte, b2f_xor]
      have := f2_add_self (b2f (w j))
      linear_combination this
    rw [heq]
    exact Submodule.subset_span ⟨p, h.1, rfl⟩
  · have hcond : (T.hasPiv p && w p) = false := by
      cases hp : T.hasPiv p <;> cases hw : w p <;> simp_all
    have heq : (fun j => b2f (T.redStep p w j) + b2f (w j)) = 0 := by
      funext j
      simp only [PTab.redStep, hcond, Bool.false_eq_true, ↓reduceIte, Pi.zero_apply]
      exact f2_add_self _
    rw [heq]
    exact T.toSub.zero_mem

lemma PTab.reduce_sub_mem {N : ℕ} (T : PTab N) (w : Fin N → Bool) :
    (fun j => b2f (T.reduce w j) + b2f (w j)) ∈ T.toSub := by
  unfold PTab.reduce
  suffices h : ∀ (l : List (Fin N)) (a : Fin N → Bool),
      (fun j => b2f (l.foldl (fun acc p => T.redStep p acc) a j) + b2f (a j)) ∈ T.toSub from h _ w
  intro l
  induction l with
  | nil =>
    intro a
    have : (fun j => b2f (a j) + b2f (a j)) = 0 := by funext j; exact f2_add_self _
    simp [this]
  | cons p l ih =>
    intro a
    simp only [List.foldl_cons]
    have h1 := ih (T.redStep p a)
    have h2 := T.redStep_sub_mem p a
    have hadd := T.toSub.add_mem h1 h2
    have heq : (fun j => b2f (l.foldl (fun acc p => T.redStep p acc) (T.redStep p a) j) + b2f (a j)) =
        (fun j => b2f (l.foldl (fun acc p => T.redStep p acc) (T.redStep p a) j) + b2f (T.redStep p a j)) +
        (fun j => b2f (T.redStep p a j) + b2f (a j)) := by
      funext j
      simp only [Pi.add_apply]
      have := f2_add_self (b2f (T.redStep p a j))
      linear_combination -this
    rw [heq]
    exact hadd

lemma PTab.reduce_piv_zero {N : ℕ} (T : PTab N) (hE : T.IsEchelon) (w : Fin N → Bool)
    (p : Fin N) (hp : T.hasPiv p = true) : T.reduce w p = false := by
  unfold PTab.reduce
  have hinv : ∀ (m : ℕ), m ≤ N →
      ∀ (q : Fin N), q.val < m → T.hasPiv q = true →
        ((List.finRange N).take m).foldl (fun acc r => T.redStep r acc) w q = false := by
    intro m hm
    induction m with
    | zero => intro q hq; omega
    | succ m ih =>
      intro q hq hqp
      have hm_lt : m < N := by omega
      have htake : (List.finRange N).take (m + 1) = (List.finRange N).take m ++ [⟨m, hm_lt⟩] := by
        rw [List.take_succ_eq_append_getElem (by simp [hm_lt])]
        simp [List.getElem_finRange]
      rw [htake, List.foldl_append, List.foldl_cons, List.foldl_nil]
      set acc := ((List.finRange N).take m).foldl (fun acc r => T.redStep r acc) w
      by_cases hqm : q.val < m
      · have hprev := ih (by omega) q hqm hqp
        dsimp only [PTab.redStep]
        split_ifs with hc
        · have hlt : q < ⟨m, hm_lt⟩ := hqm
          have hr0 := (hE ⟨m, hm_lt⟩ (Bool.and_eq_true_iff.mp hc).1).2 q hlt
          rw [hprev, hr0]; rfl
        · exact hprev
      · have hqeq : q = ⟨m, hm_lt⟩ := Fin.ext (by dsimp only; omega)
        subst hqeq
        dsimp only [PTab.redStep]
        by_cases hacc : acc ⟨m, hm_lt⟩ = true
        · have h1 := (hE ⟨m, hm_lt⟩ hqp).1
          simp [hqp, hacc, h1]
        · have haccf : acc ⟨m, hm_lt⟩ = false := by cases h : acc ⟨m, hm_lt⟩ <;> simp_all
          simp [hqp, haccf]
  have h1 := hinv N (le_refl N) p p.isLt hp
  rw [List.take_of_length_le (by simp)] at h1
  exact h1

lemma PTab.echelon_piv_indep {N : ℕ} (T : PTab N) (hE : T.IsEchelon) :
    LinearIndependent F2 (fun p : {p : Fin N // T.hasPiv p = true} => fun j : Fin N => b2f (T.row p.val j)) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hzero : ∀ (m : ℕ), m ≤ N → ∀ p : {p : Fin N // T.hasPiv p = true}, p.val.val < m → c p = 0 := by
    intro m hm
    induction m with
    | zero => intro p hp; omega
    | succ m ih =>
      intro p hp
      by_cases hpm : p.val.val < m
      · exact ih (by omega) p hpm
      · have hpeq : p.val.val = m := by omega
        have hval := congrFun hc p.val
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hval
        have hsingle : (∑ q : {q : Fin N // T.hasPiv q = true}, c q * b2f (T.row q.val p.val)) =
            c p * b2f (T.row p.val p.val) := by
          refine Finset.sum_eq_single p (fun q _ hne => ?_) (fun h => absurd (Finset.mem_univ _) h)
          by_cases hlt : q.val.val < m
          · rw [ih (by omega) q hlt, zero_mul]
          · have hgt : p.val < q.val := by
              have hne' : q.val.val ≠ p.val.val := fun he => hne (Subtype.ext (Fin.ext he))
              exact Fin.lt_def.mpr (by omega)
            rw [(hE q.val q.property).2 p.val hgt, b2f_false, mul_zero]
        rw [hsingle, (hE p.val p.property).1] at hval
        simpa [b2f] using hval
  intro p
  exact hzero N (le_refl N) p p.val.isLt

lemma PTab.zero_of_mem_of_piv_zero {N : ℕ} (T : PTab N) (hE : T.IsEchelon)
    (u : Fin N → F2) (hu : u ∈ T.toSub) (hpiv : ∀ p : Fin N, T.hasPiv p = true → u p = 0) :
    u = 0 := by
  have hspan : T.toSub = Submodule.span F2 (Set.range (fun p : {p : Fin N // T.hasPiv p = true} => fun j => b2f (T.row p.val j))) := by
    unfold PTab.toSub; congr 1; ext v
    constructor
    · rintro ⟨p, hp, rfl⟩; exact ⟨⟨p, hp⟩, rfl⟩
    · rintro ⟨⟨p, hp⟩, rfl⟩; exact ⟨p, hp, rfl⟩
  rw [hspan, Submodule.mem_span_range_iff_exists_fun] at hu
  rcases hu with ⟨c, rfl⟩
  have hc0 : ∀ p : {p : Fin N // T.hasPiv p = true}, c p = 0 := by
    have hzero : ∀ (m : ℕ), m ≤ N → ∀ p : {p : Fin N // T.hasPiv p = true}, p.val.val < m → c p = 0 := by
      intro m hm
      induction m with
      | zero => intro p hp; omega
      | succ m ih =>
        intro p hp
        by_cases hpm : p.val.val < m
        · exact ih (by omega) p hpm
        · have hpeq : p.val.val = m := by omega
          have hval := hpiv p.val p.property
          simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hval
          have hsingle : (∑ q : {q : Fin N // T.hasPiv q = true}, c q * b2f (T.row q.val p.val)) =
              c p * b2f (T.row p.val p.val) := by
            refine Finset.sum_eq_single p (fun q _ hne => ?_) (fun h => absurd (Finset.mem_univ _) h)
            by_cases hlt : q.val.val < m
            · rw [ih (by omega) q hlt, zero_mul]
            · have hgt : p.val < q.val := by
                have hne' : q.val.val ≠ p.val.val := fun he => hne (Subtype.ext (Fin.ext he))
                exact Fin.lt_def.mpr (by omega)
              rw [(hE q.val q.property).2 p.val hgt, b2f_false, mul_zero]
          rw [hsingle, (hE p.val p.property).1] at hval
          simpa [b2f] using hval
    intro p; exact hzero N (le_refl N) p p.val.isLt
  simp [hc0]

lemma PTab.reduce_eq_zero_iff {N : ℕ} (T : PTab N) (hE : T.IsEchelon) (w : Fin N → Bool) :
    (∀ j : Fin N, T.reduce w j = false) ↔ (fun j => b2f (w j)) ∈ T.toSub := by
  constructor
  · intro h0
    have hmem := T.reduce_sub_mem w
    have heq : (fun j => b2f (T.reduce w j) + b2f (w j)) = fun j => b2f (w j) := by
      funext j; rw [h0 j, b2f_false, zero_add]
    rwa [heq] at hmem
  · intro hw
    have hmem : (fun j => b2f (T.reduce w j)) ∈ T.toSub := by
      have h1 := T.toSub.add_mem (T.reduce_sub_mem w) hw
      have heq : (fun j => b2f (T.reduce w j)) =
          (fun j => b2f (T.reduce w j) + b2f (w j)) + (fun j => b2f (w j)) := by
        funext j; simp only [Pi.add_apply]; have := f2_add_self (b2f (w j)); linear_combination -this
      rw [heq]; exact h1
    have hu0 := T.zero_of_mem_of_piv_zero hE (fun j => b2f (T.reduce w j)) hmem
      (fun p hp => by rw [T.reduce_piv_zero hE w p hp, b2f_false])
    intro j
    have hj := congrFun hu0 j
    exact b2f_inj (by simpa [b2f_false] using hj)

lemma PTab.insert_isEchelon {N : ℕ} (T : PTab N) (hE : T.IsEchelon) (v : Fin N → Bool) :
    (T.insert v).IsEchelon := by
  intro p hp
  dsimp only [PTab.insert] at hp ⊢
  by_cases hft : pFirstTrue (T.reduce v) p = true
  · simp only [if_pos hft]
    exact (pFirstTrue_iff _ _).mp hft
  · have hftf : pFirstTrue (T.reduce v) p = false := by cases h : pFirstTrue (T.reduce v) p <;> simp_all
    simp only [if_neg hft]
    have hpT : T.hasPiv p = true := by simp [hftf] at hp; exact hp
    exact hE p hpT

lemma PTab.insert_toSub {N : ℕ} (T : PTab N) (hE : T.IsEchelon) (v : Fin N → Bool) :
    (T.insert v).toSub = T.toSub ⊔ Submodule.span F2 {fun j => b2f (v j)} := by
  set w := T.reduce v
  by_cases hw0 : ∀ j : Fin N, w j = false
  · have hft0 : ∀ p : Fin N, pFirstTrue w p = false := fun p => by
      simp [pFirstTrue, hw0 p]
    have hTeq : T.insert v = T := by
      cases T; simp [PTab.insert, w, hft0]
    rw [hTeq]
    have hvmem : (fun j => b2f (v j)) ∈ T.toSub := (T.reduce_eq_zero_iff hE v).mp hw0
    exact (sup_eq_left.mpr (Submodule.span_le.mpr (by simpa using hvmem))).symm
  · push_neg at hw0
    have hex : ∃ p : Fin N, w p = true := by
      rcases hw0 with ⟨p, hp⟩
      exact ⟨p, by cases h : w p <;> simp_all⟩
    obtain ⟨p₀, hp₀⟩ := exists_pFirstTrue_of_ne_false w hex
    have hnotpiv : T.hasPiv p₀ = false := by
      by_contra hpt
      have hpt' : T.hasPiv p₀ = true := by cases h : T.hasPiv p₀ <;> simp_all
      have h0 : w p₀ = false := T.reduce_piv_zero hE v p₀ hpt'
      have h1 := ((pFirstTrue_iff w p₀).mp hp₀).1
      rw [h0] at h1; exact absurd h1 (by decide)
    have hset : { u : Fin N → F2 | ∃ p : Fin N, (T.insert v).hasPiv p = true ∧ u = fun j => b2f ((T.insert v).row p j) } =
        { u : Fin N → F2 | ∃ p : Fin N, T.hasPiv p = true ∧ u = fun j => b2f (T.row p j) } ∪ {fun j => b2f (w j)} := by
      ext u
      simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_singleton_iff, PTab.insert]
      constructor
      · rintro ⟨p, hp, rfl⟩
        by_cases hpp : p = p₀
        · subst hpp; right; simp [w, hp₀]
        · have hftf : pFirstTrue w p = false := by
            by_contra h1
            have h1' : pFirstTrue w p = true := by cases h : pFirstTrue w p <;> simp_all
            exact hpp (pFirstTrue_unique w h1' hp₀)
          left
          refine ⟨p, ?_, ?_⟩
          · simp [w, hftf] at hp; exact hp
          · simp [w, hftf]
      · rintro (⟨p, hp, rfl⟩ | rfl)
        · have hpp : p ≠ p₀ := fun h => by rw [h, hnotpiv] at hp; exact absurd hp (by decide)
          have hftf : pFirstTrue w p = false := by
            by_contra h1
            have h1' : pFirstTrue w p = true := by cases h : pFirstTrue w p <;> simp_all
            exact hpp (pFirstTrue_unique w h1' hp₀)
          exact ⟨p, by simp [hp], by simp [w, hftf]⟩
        · exact ⟨p₀, by simp [w, hp₀], by simp [w, hp₀]⟩
    have hspan_w : (T.insert v).toSub = T.toSub ⊔ Submodule.span F2 {fun j => b2f (w j)} := by
      unfold PTab.toSub
      rw [hset, Submodule.span_union]
    rw [hspan_w]
    have hsub := T.reduce_sub_mem v
    apply le_antisymm
    · refine sup_le le_sup_left (Submodule.span_le.mpr ?_)
      rintro u rfl
      have heq : (fun j => b2f (w j)) = (fun j => b2f (w j) + b2f (v j)) + (fun j => b2f (v j)) := by
        funext j; simp only [Pi.add_apply]; have := f2_add_self (b2f (v j)); linear_combination -this
      rw [heq]
      exact Submodule.add_mem _ (Submodule.mem_sup_left hsub) (Submodule.mem_sup_right (Submodule.subset_span rfl))
    · refine sup_le le_sup_left (Submodule.span_le.mpr ?_)
      rintro u rfl
      have heq : (fun j => b2f (v j)) = (fun j => b2f (w j) + b2f (v j)) + (fun j => b2f (w j)) := by
        funext j; simp only [Pi.add_apply]; have := f2_add_self (b2f (w j)); linear_combination -this
      rw [heq]
      exact Submodule.add_mem _ (Submodule.mem_sup_left hsub) (Submodule.mem_sup_right (Submodule.subset_span rfl))

lemma PTab.finrank_toSub {N : ℕ} (T : PTab N) (hE : T.IsEchelon) :
    Module.finrank F2 T.toSub = popCount T.hasPiv := by
  let f : {p : Fin N // T.hasPiv p = true} → (Fin N → F2) := fun p j => b2f (T.row p.val j)
  have hspan : T.toSub = Submodule.span F2 (Set.range f) := by
    unfold PTab.toSub; congr 1; ext v
    constructor
    · rintro ⟨p, hp, rfl⟩; exact ⟨⟨p, hp⟩, rfl⟩
    · rintro ⟨⟨p, hp⟩, rfl⟩; exact ⟨p, hp, rfl⟩
  rw [hspan]
  let b : Module.Basis {p : Fin N // T.hasPiv p = true} F2 (Submodule.span F2 (Set.range f)) :=
    Module.Basis.span (T.echelon_piv_indep hE)
  rw [Module.finrank_eq_card_basis b, Fintype.card_subtype]
  rfl


-- Circuit Extends lemmas for PTab
def PTabSig (n N : ℕ) := (Fin n → Bool) → PTab N

def ptabBits {n N : ℕ} (T : PTabSig n N) : Set (Sig n) :=
  Set.range (fun p : Fin N => fun x => (T x).hasPiv p) ∪
  Set.range (fun pq : Fin N × Fin N => fun x => (T x).row pq.1 pq.2)

lemma Extends.ptab_empty {n N : ℕ} :
    Extends n ∅ (ptabBits (fun _ : Fin n → Bool => PTab.empty N)) (N + N * N) := by
  have h1 : Extends n ∅ (Set.range (fun _ : Fin N => fun _ : Fin n → Bool => false)) N := by
    simpa [mul_one] using Extends.add_range_fin (n := n) (k := N) (S := ∅)
      (f := fun _ : Fin N => fun _ : Fin n → Bool => false) (c := 1) (fun _ => Extends.add_const false)
  have h2 : Extends n ∅ (Set.range (fun _ : Fin N × Fin N => fun _ : Fin n → Bool => false)) (N * N) := by
    have := Extends.add_range_prod (n := n) (R := N) (C := N) (S := ∅)
      (f := fun (_ : Fin N) (_ : Fin N) => fun _ : Fin n → Bool => false) (c := 1)
      (fun _ _ => Extends.add_const false)
    simpa [mul_one] using this
  exact (h1.union h2).mono Set.Subset.rfl Set.Subset.rfl le_rfl

lemma Extends.ptab_reduce {n N : ℕ} (T : PTabSig n N) (w : Fin N → Sig n) :
    Extends n (ptabBits T ∪ Set.range w)
      (Set.range (fun j : Fin N => fun x => (T x).reduce (fun i => w i x) j))
      (6 * N * N) := by
  let acc (m : ℕ) (j : Fin N) : Sig n := fun x =>
    ((List.finRange N).take m).foldl (fun a p => (T x).redStep p a) (fun i => w i x) j
  let Inv (m : ℕ) : Set (Sig n) := ptabBits T ∪ Set.range (acc m)
  have h0 : Extends n (ptabBits T ∪ Set.range w) (Inv 0) 0 := by
    have : acc 0 = w := by funext j x; simp [acc]
    dsimp only [Inv]; rw [this]; exact Extends.of_subset Set.Subset.rfl
  have hstep : ∀ m < N, Extends n (Inv m) (Inv (m + 1)) (6 * N) := by
    intro m hm
    let pm : Fin N := ⟨m, hm⟩
    let cSig : Sig n := fun x => (T x).hasPiv pm && acc m pm x
    have hc : Extends n (Inv m) {cSig} 1 :=
      Extends.add_and (Or.inl (Or.inl ⟨pm, rfl⟩)) (Or.inr ⟨pm, rfl⟩)
    have htake : (List.finRange N).take (m + 1) = (List.finRange N).take m ++ [pm] := by
      rw [List.take_succ_eq_append_getElem (by simp [hm])]; simp [List.getElem_finRange, pm]
    have hnext : Extends n (Inv m ∪ {cSig}) (Set.range (acc (m + 1))) (5 * N) := by
      have hr := Extends.add_range_fin (S := Inv m ∪ {cSig}) (f := acc (m + 1)) (c := 5) (fun j => by
        have heq : acc (m + 1) j = fun x => if cSig x then xor (acc m j x) ((T x).row pm j) else acc m j x := by
          funext x; simp [acc, htake, List.foldl_append, PTab.redStep, cSig]
        rw [heq]
        exact Extends.add_xor_and (Or.inl (Or.inr ⟨j, rfl⟩)) (Or.inr rfl) (Or.inl (Or.inl (Or.inr ⟨(pm, j), rfl⟩))))
      exact hr.mono Set.Subset.rfl Set.Subset.rfl (by omega)
    have hkeep : Extends n (Inv m) (ptabBits T) 0 := Extends.of_subset Set.subset_union_left
    exact (hkeep.union (hc.seq hnext)).mono Set.Subset.rfl Set.Subset.rfl (by omega)
  have hfold := Extends.fold_nat_const N Inv (6 * N) hstep
  have hend : acc N = fun j x => (T x).reduce (fun i => w i x) j := by
    funext j x; dsimp only [acc, PTab.reduce]; rw [List.take_of_length_le (by simp)]
  dsimp only [Inv] at hfold
  rw [hend] at hfold
  exact (h0.seq (hfold.mono Set.subset_union_right Set.Subset.rfl le_rfl)).mono
    Set.Subset.rfl Set.subset_union_right (by nlinarith)

lemma Extends.pFirstTrue_sig {n N : ℕ} (w : Fin N → Sig n) :
    Extends n (Set.range w) (Set.range (fun p : Fin N => fun x => pFirstTrue (fun i => w i x) p))
      (3 * N * N + 2 * N) := by
  have hp := Extends.add_range_fin (S := Set.range w)
    (f := fun p : Fin N => fun x => pFirstTrue (fun i => w i x) p) (c := 3 * N + 2) (fun p => by
      let term (q : Fin N) : Sig n := fun x => !decide (q < p) || !w q x
      have ht : Extends n (Set.range w) (Set.range term) (2 * N) := by
        have h := Extends.add_range_fin (S := Set.range w) (f := term) (c := 2) (fun q => by
          by_cases hq : q < p
          · have heq : term q = fun x => !w q x := by funext x; simp [term, hq]
            rw [heq]; exact (Extends.add_not (S := Set.range w) ⟨q, rfl⟩).mono Set.Subset.rfl Set.Subset.rfl (by omega)
          · have heq : term q = fun _ => true := by funext x; simp [term, hq]
            rw [heq]; exact (Extends.add_const true).mono Set.Subset.rfl Set.Subset.rfl (by omega))
        exact h.mono Set.Subset.rfl Set.Subset.rfl (by omega)
      have hall : Extends n (Set.range w ∪ Set.range term)
          {fun x => (List.finRange N).all (fun q => term q x)} (N + 1) :=
        Extends.add_all_fin term (fun q => Or.inr ⟨q, rfl⟩)
      have hand : Extends n (Set.range w ∪ (Set.range term ∪ {fun x => (List.finRange N).all (fun q => term q x)}))
          {fun x => pFirstTrue (fun i => w i x) p} 1 :=
        Extends.add_and (Or.inl ⟨p, rfl⟩) (Or.inr (Or.inr rfl))
      exact ((ht.trans hall).seq hand).mono Set.Subset.rfl Set.Subset.rfl (by omega))
  exact hp.mono Set.Subset.rfl Set.Subset.rfl (by nlinarith)

lemma Extends.ptab_insert {n N : ℕ} (T : PTabSig n N) (v : Fin N → Sig n) :
    Extends n (ptabBits T ∪ Set.range v)
      (ptabBits (fun x => (T x).insert (fun i => v i x)))
      (13 * N * N + 3 * N) := by
  let w : Fin N → Sig n := fun j x => (T x).reduce (fun i => v i x) j
  let ft : Fin N → Sig n := fun p x => pFirstTrue (fun i => w i x) p
  have hred : Extends n (ptabBits T ∪ Set.range v) (Set.range w) (6 * N * N) :=
    Extends.ptab_reduce T v
  have hft : Extends n ((ptabBits T ∪ Set.range v) ∪ Set.range w) (Set.range ft) (3 * N * N + 2 * N) :=
    (Extends.pFirstTrue_sig w).mono Set.subset_union_right Set.Subset.rfl le_rfl
  let S2 := (ptabBits T ∪ Set.range v) ∪ (Set.range w ∪ Set.range ft)
  have hhp : Extends n S2 (Set.range (fun p : Fin N => fun x => ((T x).insert (fun i => v i x)).hasPiv p)) N := by
    have := Extends.add_range_fin (S := S2)
      (f := fun p : Fin N => fun x => ((T x).insert (fun i => v i x)).hasPiv p) (c := 1) (fun p =>
        Extends.add_or (Or.inl (Or.inl (Or.inl ⟨p, rfl⟩))) (Or.inr (Or.inr ⟨p, rfl⟩)))
    exact this.mono Set.Subset.rfl Set.Subset.rfl (by omega)
  have hrow : Extends n S2 (Set.range (fun pq : Fin N × Fin N => fun x => ((T x).insert (fun i => v i x)).row pq.1 pq.2))
      (4 * N * N) := by
    have := Extends.add_range_prod (S := S2)
      (f := fun (p j : Fin N) => fun x => ((T x).insert (fun i => v i x)).row p j) (c := 4) (fun p j =>
        Extends.add_mux (Or.inr (Or.inr ⟨p, rfl⟩)) (Or.inr (Or.inl ⟨j, rfl⟩))
          (Or.inl (Or.inl (Or.inr ⟨(p, j), rfl⟩))))
    exact this.mono Set.Subset.rfl Set.Subset.rfl (by nlinarith)
  exact ((hred.trans hft).seq (hhp.union hrow)).mono Set.Subset.rfl Set.Subset.rfl (by nlinarith)


lemma card_sub_eq_pow_finrank {V : Type*} [AddCommGroup V] [Module F2 V] [Finite V]
    (S : Submodule F2 V) :
    Nat.card S = 2 ^ Module.finrank F2 S := by
  haveI : Fintype S := Fintype.ofFinite S
  rw [Nat.card_eq_fintype_card]
  have hb := Module.finBasis F2 S
  have h1 := Fintype.card_congr hb.equivFun.toEquiv
  rw [Fintype.card_fun, Fintype.card_fin] at h1
  have hf2 : Fintype.card F2 = 2 := by decide
  rw [hf2] at h1
  exact h1

/-! ### Part 2: Extra Word Arithmetic (`word_sub_ge`, `word_shl_oh`, `word_sum_bools`) -/

lemma natOfBits_not {B : ℕ} (u : Fin B → Bool) :
    natOfBits (fun i => !u i) + natOfBits u + 1 = 2 ^ B := by
  unfold natOfBits
  induction B with
  | zero => simp
  | succ B ih =>
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
    have h1 := ih (fun i => u i.castSucc)
    have hlast : (!u (Fin.last B)).toNat + (u (Fin.last B)).toNat = 1 := by
      cases u (Fin.last B) <;> decide
    have hpow : 2 ^ (B + 1) = 2 ^ B + 2 ^ B := by ring
    simp only [Fin.val_castSucc, Fin.val_last] at h1 ⊢
    have hmul : (!u (Fin.last B)).toNat * 2 ^ B + (u (Fin.last B)).toNat * 2 ^ B = 2 ^ B := by
      rw [← add_mul, hlast, one_mul]
    omega

lemma ripple_sub_spec {B : ℕ} (a b : ZMod (2 ^ B)) :
    rippleCarry B true (fun i => a.val.testBit i.val) (fun i => !(b.val.testBit i.val)) B =
      decide (b.val ≤ a.val) ∧
    ∀ j : Fin B,
      rippleSum B true (fun i => a.val.testBit i.val) (fun i => !(b.val.testBit i.val)) j =
        (a - b).val.testBit j.val := by
  haveI : NeZero (2 ^ B) := ⟨by positivity⟩
  let u : Fin B → Bool := fun i => a.val.testBit i.val
  let v : Fin B → Bool := fun i => b.val.testBit i.val
  have hinv := ripple_inv B true u (fun i => !v i) B le_rfl
  have hsum_eq (f : Fin B → ℕ) :
      (∑ i ∈ Finset.range B, if h : i < B then f ⟨i, h⟩ else 0) = ∑ i : Fin B, f i := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => if h : i < B then f ⟨i, h⟩ else 0)]
    refine Finset.sum_congr rfl fun i _ => by simp [i.isLt]
  rw [hsum_eq (fun i => (rippleSum B true u (fun j => !v j) i).toNat * 2 ^ i.val),
    hsum_eq (fun i => (u i).toNat * 2 ^ i.val),
    hsum_eq (fun i => (!v i).toNat * 2 ^ i.val)] at hinv
  change natOfBits (rippleSum B true u (fun j => !v j)) +
      (rippleCarry B true u (fun j => !v j) B).toNat * 2 ^ B =
    1 + natOfBits u + natOfBits (fun j => !v j) at hinv
  have hnot := natOfBits_not v
  have hu : natOfBits u = a.val := natOfBits_of_testBit a.val (ZMod.val_lt a)
  have hv : natOfBits v = b.val := natOfBits_of_testBit b.val (ZMod.val_lt b)
  have hlt_s := natOfBits_lt (rippleSum B true u (fun j => !v j))
  have ha_lt := ZMod.val_lt a
  have hb_lt := ZMod.val_lt b
  have hrel : natOfBits (rippleSum B true u (fun j => !v j)) +
      (rippleCarry B true u (fun j => !v j) B).toNat * 2 ^ B + b.val = a.val + 2 ^ B := by
    omega
  constructor
  · cases hc : rippleCarry B true u (fun j => !v j) B
    · rw [hc] at hrel; simp only [Bool.toNat_false, zero_mul, add_zero] at hrel
      exact (decide_eq_false (by omega)).symm
    · rw [hc] at hrel; simp only [Bool.toNat_true, one_mul] at hrel
      exact (decide_eq_true (by omega)).symm
  · intro j
    have hval_sub : natOfBits (rippleSum B true u (fun j => !v j)) = (a - b).val := by
      have hcast : ((natOfBits (rippleSum B true u (fun j => !v j)) : ℕ) : ZMod (2 ^ B)) = a - b := by
        have h1 : ((natOfBits (rippleSum B true u (fun j => !v j)) +
            (rippleCarry B true u (fun j => !v j) B).toNat * 2 ^ B + b.val : ℕ) : ZMod (2 ^ B)) =
            ((a.val + 2 ^ B : ℕ) : ZMod (2 ^ B)) := congrArg Nat.cast hrel
        rw [Nat.cast_add, Nat.cast_add, Nat.cast_mul, Nat.cast_add, ZMod.natCast_self,
          ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at h1
        simp only [mul_zero, add_zero] at h1
        exact eq_sub_of_add_eq h1
      have h2 := congrArg ZMod.val hcast
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt hlt_s] at h2
      exact h2
    rw [← hval_sub, natOfBits_testBit]

lemma Extends.ripple_with_carry {n B : ℕ} (c0 : Bool) (u v : Fin B → Sig n) :
    Extends n (Set.range u ∪ Set.range v)
      ({fun x => rippleCarry B c0 (fun i => u i x) (fun i => v i x) B} ∪
       Set.range (fun j : Fin B => fun x => rippleSum B c0 (fun i => u i x) (fun i => v i x) j))
      (14 * B + 1) := by
  let carrySig (k : ℕ) : Sig n := fun x => rippleCarry B c0 (fun i => u i x) (fun i => v i x) k
  let Base : Set (Sig n) := Set.range u ∪ Set.range v
  let A (k : ℕ) : Set (Sig n) := Base ∪ {carrySig k}
  have h0 : Extends n Base (A 0) 1 := by
    have hc : Extends n ∅ {carrySig 0} 1 := by
      change Extends n ∅ {fun _ => c0} 1
      exact Extends.const_bool c0
    exact (Extends.of_subset Set.Subset.rfl).union (hc.mono (Set.empty_subset _) Set.Subset.rfl le_rfl)
  have hstep : ∀ (k : ℕ) (hk : k < B),
      Extends n (A k) (A (k + 1) ∪ {fun x => rippleSum B c0 (fun i => u i x) (fun i => v i x) ⟨k, hk⟩}) 13 := by
    intro k hk
    let uk : Sig n := u ⟨k, hk⟩
    let vk : Sig n := v ⟨k, hk⟩
    let ck : Sig n := carrySig k
    have hmaj : Extends n (A k) {carrySig (k + 1)} 5 := by
      have heq : carrySig (k + 1) = (fun x => (uk x && vk x) || ((uk x && ck x) || (vk x && ck x))) := by
        funext x; simp [carrySig, rippleCarry, hk, uk, vk, ck]
      rw [heq]
      exact (Extends.maj_gate uk vk ck).mono (by
        intro z hz; simp at hz; rcases hz with rfl | rfl | rfl
        · exact Or.inl (Or.inl ⟨⟨k, hk⟩, rfl⟩)
        · exact Or.inl (Or.inr ⟨⟨k, hk⟩, rfl⟩)
        · exact Or.inr rfl) Set.Subset.rfl le_rfl
    have hxor1 : Extends n (A k) {fun x => xor (uk x) (vk x)} 4 :=
      (Extends.xor_gate uk vk).mono (by
        intro z hz; simp at hz; rcases hz with rfl | rfl
        · exact Or.inl (Or.inl ⟨⟨k, hk⟩, rfl⟩)
        · exact Or.inl (Or.inr ⟨⟨k, hk⟩, rfl⟩)) Set.Subset.rfl le_rfl
    have hxor2 : Extends n (A k ∪ {fun x => xor (uk x) (vk x)})
        {fun x => rippleSum B c0 (fun i => u i x) (fun i => v i x) ⟨k, hk⟩} 4 :=
      (Extends.xor_gate (fun x => xor (uk x) (vk x)) ck).mono (by
        intro z hz; simp at hz; rcases hz with rfl | rfl
        · exact Or.inr rfl
        · exact Or.inl (Or.inr rfl)) Set.Subset.rfl le_rfl
    have hsum := hxor1.seq hxor2
    have hall := hmaj.union hsum
    have hbase : Extends n (A k) Base 0 := Extends.of_subset Set.subset_union_left
    exact (hbase.union hall).mono Set.Subset.rfl (by
      intro z hz
      rcases hz with (hb | rfl) | rfl
      · exact Or.inl hb
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)) (by omega)
  let Inv (k : ℕ) : Set (Sig n) :=
    A k ∪ {f | ∃ i : Fin B, i.val < k ∧ f = fun x => rippleSum B c0 (fun r => u r x) (fun r => v r x) i}
  have hfold := Extends.fold_nat_const B Inv 13 (fun k hk => by
    have hs := (hstep k hk).mono (Set.subset_union_left : A k ⊆ Inv k) Set.Subset.rfl le_rfl
    have hkeep : Extends n (Inv k) (Inv k) 0 := Extends.of_subset Set.Subset.rfl
    refine (hkeep.union hs).mono Set.Subset.rfl ?_ (by omega)
    intro z hz
    rcases hz with hA | ⟨i, hi, rfl⟩
    · exact Or.inr (Or.inl hA)
    · by_cases hlt : i.val < k
      · exact Or.inl (Or.inr ⟨i, hlt, rfl⟩)
      · have hieq : i = ⟨k, hk⟩ := Fin.ext (by dsimp only; omega)
        subst hieq; exact Or.inr (Or.inr rfl))
  have hstart : Extends n Base (Inv 0) 1 :=
    h0.mono Set.Subset.rfl (by intro z hz; rcases hz with h | ⟨i, hi, _⟩; exact h; omega) le_rfl
  refine (hstart.seq (hfold.mono Set.subset_union_right Set.Subset.rfl le_rfl)).mono Set.Subset.rfl ?_ (by omega)
  rintro z (rfl | ⟨i, rfl⟩)
  · exact Or.inl (Or.inr rfl)
  · exact Or.inr ⟨i, i.isLt, rfl⟩

lemma Extends.word_sub_ge {n B : ℕ} (a b : WordSig n B) :
    Extends n (wordBits a ∪ wordBits b)
      ({fun x => decide ((b x).val ≤ (a x).val)} ∪ wordBits (fun x => a x - b x))
      (15 * B + 1) := by
  let nb : Fin B → Sig n := fun i x => !((b x).val.testBit i.val)
  have hnb : Extends n (wordBits a ∪ wordBits b) (Set.range nb) B := by
    have := Extends.add_range_fin (S := wordBits a ∪ wordBits b) (f := nb) (c := 1)
      (fun i => Extends.add_not (Or.inr ⟨i, rfl⟩))
    simpa [mul_one] using this
  have hrip := Extends.ripple_with_carry (n := n) (B := B) true
    (fun i x => (a x).val.testBit i.val) nb
  have hrip' : Extends n ((wordBits a ∪ wordBits b) ∪ Set.range nb)
      ({fun x => decide ((b x).val ≤ (a x).val)} ∪ wordBits (fun x => a x - b x)) (14 * B + 1) := by
    refine hrip.mono ?_ ?_ le_rfl
    · rintro z (⟨i, rfl⟩ | ⟨i, rfl⟩)
      · exact Or.inl (Or.inl ⟨i, rfl⟩)
      · exact Or.inr ⟨i, rfl⟩
    · rintro z (rfl | ⟨j, rfl⟩)
      · left; funext x; exact (ripple_sub_spec (a x) (b x)).1.symm
      · right; refine ⟨j, ?_⟩; funext x; exact (ripple_sub_spec (a x) (b x)).2 j
  exact (hnb.seq hrip').mono Set.Subset.rfl Set.Subset.rfl (by omega)

lemma Extends.word_shl_oh {n B : ℕ} (w : WordSig n B) (sh : (Fin n → Bool) → ℕ)
    (hsh : ∀ x, sh x < B) :
    Extends n (wordBits w ∪ Set.range (fun d : Fin B => fun x => decide (sh x = d.val)))
      (wordBits (fun x => (((w x).val * 2 ^ (sh x) : ℕ) : ZMod (2 ^ B))))
      (2 * B * B + 2 * B + 1) := by
  let S0 := wordBits w ∪ Set.range (fun d : Fin B => fun x => decide (sh x = d.val))
  have hf : Extends n S0 {fun _ => false} 1 := Extends.add_const false
  have hbits : Extends n (S0 ∪ {fun _ => false})
      (wordBits (fun x => (((w x).val * 2 ^ (sh x) : ℕ) : ZMod (2 ^ B))))
      (B * (2 * B + 1)) := by
    have hp := Extends.add_range_fin (S := S0 ∪ {fun _ => false})
      (f := fun j : Fin B => fun x => ((((w x).val * 2 ^ (sh x) : ℕ) : ZMod (2 ^ B))).val.testBit j.val)
      (c := 2 * B + 1) (fun j => by
        let g1 : Fin B → Sig n := fun d x => decide (sh x = d.val)
        let g2 : Fin B → Sig n := fun d x =>
          if d.val ≤ j.val then (w x).val.testBit (j.val - d.val) else false
        have hg1 : ∀ d, g1 d ∈ S0 ∪ {fun _ => false} := fun d => Or.inl (Or.inr ⟨d, rfl⟩)
        have hg2 : ∀ d, g2 d ∈ S0 ∪ {fun _ => false} := fun d => by
          by_cases hd : d.val ≤ j.val
          · have : g2 d = fun x => (w x).val.testBit (j.val - d.val) := by
              funext x; dsimp only [g2]; rw [if_pos hd]
            rw [this]; exact Or.inl (Or.inl ⟨⟨j.val - d.val, by omega⟩, rfl⟩)
          · have : g2 d = fun _ => false := by
              funext x; dsimp only [g2]; rw [if_neg hd]
            rw [this]; exact Or.inr rfl
        have hcomp := Extends.add_and_any_fin g1 g2 hg1 hg2
        have heq : (fun x => (List.finRange B).any (fun d => g1 d x && g2 d x)) =
            (fun x => ((((w x).val * 2 ^ (sh x) : ℕ) : ZMod (2 ^ B))).val.testBit j.val) := by
          funext x
          haveI : NeZero (2 ^ B) := ⟨by positivity⟩
          rw [ZMod.val_natCast, Nat.testBit_mod_two_pow, decide_eq_true j.isLt, Bool.true_and,
            ← Nat.shiftLeft_eq, Nat.testBit_shiftLeft]
          rw [Bool.eq_iff_iff]
          simp only [List.any_eq_true, List.mem_finRange, true_and, Bool.and_eq_true,
            g1, g2, decide_eq_true_eq]
          constructor
          · rintro ⟨d, hd_eq, hd_val⟩
            rw [hd_eq]
            by_cases hle : d.val ≤ j.val
            · simp [hle] at hd_val ⊢; exact hd_val
            · simp [hle] at hd_val
          · intro h
            refine ⟨⟨sh x, hsh x⟩, rfl, ?_⟩
            by_cases hle : sh x ≤ j.val
            · simp [hle] at h ⊢; exact h
            · simp [hle] at h
        rw [heq] at hcomp; exact hcomp)
    exact hp
  exact (hf.seq hbits).mono Set.Subset.rfl Set.Subset.rfl (by nlinarith)

lemma Extends.word_sum_bools {n S B : ℕ} (hB : 0 < B) (f : Fin S → Sig n) :
    Extends n (Set.range f)
      (wordBits (fun x => (((Finset.univ.filter (fun i : Fin S => f i x = true)).card : ℕ) : ZMod (2 ^ B))))
      (S * (14 * B + 1) + B + 1) := by
  let accW (t : ℕ) : WordSig n B := fun x =>
    (((Finset.univ.filter (fun i : Fin S => i.val < t ∧ f i x = true)).card : ℕ) : ZMod (2 ^ B))
  let Inv (t : ℕ) : Set (Sig n) := Set.range f ∪ {fun _ => false} ∪ wordBits (accW t)
  have h0 : Extends n (Set.range f) (Inv 0) (B + 1) := by
    have hf := Extends.add_const (n := n) (S := Set.range f) false
    have hwc : Extends n (Set.range f) (wordBits (accW 0)) B := by
      have hacc0 : accW 0 = fun _ => (0 : ZMod (2 ^ B)) := by
        funext x; simp [accW]
      rw [hacc0]
      exact (Extends.word_const 0).mono (Set.empty_subset _) Set.Subset.rfl le_rfl
    exact (((Extends.of_subset Set.Subset.rfl).union hf).union hwc).mono
      Set.Subset.rfl Set.Subset.rfl (by omega)
  have hstep : ∀ t < S, Extends n (Inv t) (Inv (t + 1)) (14 * B + 1) := by
    intro t ht
    let incW : WordSig n B := fun x => if f ⟨t, ht⟩ x then 1 else 0
    have hinc_sub : wordBits incW ⊆ Inv t := by
      rintro _ ⟨j, rfl⟩
      dsimp only
      by_cases hj : j.val = 0
      · have heq : (fun x => (incW x).val.testBit j.val) = f ⟨t, ht⟩ := by
          funext x; rw [hj]; dsimp only [incW]
          have h2 : 2 ≤ 2 ^ B := by
            have := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hB; simpa using this
          cases f ⟨t, ht⟩ x
          · simp
          · have h1 : (1 : ZMod (2 ^ B)).val = 1 := ZMod.val_one'' (by omega)
            simp [h1]
        rw [heq]; exact Or.inl (Or.inl ⟨⟨t, ht⟩, rfl⟩)
      · have heq : (fun x => (incW x).val.testBit j.val) = fun _ => false := by
          funext x; dsimp only [incW]
          have h2 : 2 ≤ 2 ^ B := by
            have := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hB; simpa using this
          cases f ⟨t, ht⟩ x
          · simp
          · have h1 : (1 : ZMod (2 ^ B)).val = 1 := ZMod.val_one'' (by omega)
            simp only [↓reduceIte, h1]
            exact Nat.testBit_eq_false_of_lt (by
              have : 2 ≤ 2 ^ j.val := by
                have := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (show 1 ≤ j.val by omega); simpa using this
              omega)
        rw [heq]; exact Or.inl (Or.inr rfl)
    have hacc_eq : accW (t + 1) = fun x => accW t x + incW x := by
      funext x; dsimp only [accW, incW]
      let prev := Finset.univ.filter (fun i : Fin S => i.val < t ∧ f i x = true)
      have hnm : (⟨t, ht⟩ : Fin S) ∉ prev := by simp [prev]
      cases hft : f ⟨t, ht⟩ x
      · have hset : Finset.univ.filter (fun i : Fin S => i.val < t + 1 ∧ f i x = true) = prev := by
          ext i; simp only [prev, Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · rintro ⟨hi, hfi⟩
            refine ⟨?_, hfi⟩
            by_contra h
            have hieq : i = ⟨t, ht⟩ := Fin.ext (by dsimp only; omega)
            rw [hieq, hft] at hfi; exact absurd hfi (by decide)
          · rintro ⟨hi, hfi⟩; exact ⟨by omega, hfi⟩
        rw [hset]; simp [prev]
      · have hset : Finset.univ.filter (fun i : Fin S => i.val < t + 1 ∧ f i x = true) = insert ⟨t, ht⟩ prev := by
          ext i; simp only [prev, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
          constructor
          · rintro ⟨hi, hfi⟩
            by_cases hlt : i.val < t
            · exact Or.inr ⟨hlt, hfi⟩
            · exact Or.inl (Fin.ext (by dsimp only; omega))
          · rintro (rfl | ⟨hi, hfi⟩)
            · exact ⟨by dsimp only; omega, hft⟩
            · exact ⟨by omega, hfi⟩
        rw [hset, Finset.card_insert_of_notMem hnm]; simp [prev]
    have hadd : Extends n (Inv t) (wordBits (accW (t + 1))) (14 * B + 1) := by
      rw [hacc_eq]
      exact (Extends.word_add (accW t) incW).mono
        (Set.union_subset Set.subset_union_right hinc_sub) Set.Subset.rfl le_rfl
    exact ((Extends.of_subset Set.subset_union_left).union hadd).mono
      Set.Subset.rfl Set.Subset.rfl (by omega)
  have hfold := Extends.fold_nat_const S Inv (14 * B + 1) hstep
  have hend : accW S = fun x =>
      (((Finset.univ.filter (fun i : Fin S => f i x = true)).card : ℕ) : ZMod (2 ^ B)) := by
    funext x; dsimp only [accW]; congr 2; ext i; simp [i.isLt]
  dsimp only [Inv] at hfold
  rw [hend] at hfold
  exact (h0.seq (hfold.mono Set.subset_union_right Set.Subset.rfl le_rfl)).mono
    Set.Subset.rfl Set.subset_union_right (by omega)

/-! ### Part 3: Input Packing & Bit-Vector Cipher Equivalence -/

def nIn (k r m : ℕ) : ℕ :=
  2 * r * k + 3 * k + 2 * ((k + 1) / 2) + m * (k + 1)

def inSched {k r m : ℕ} (x : Fin (nIn k r m) → Bool) (idx : Fin (2 * r)) (j : Fin k) : Bool :=
  x ⟨idx.val * k + j.val, by
    dsimp only [nIn]
    have h1 : (idx.val + 1) * k ≤ 2 * r * k := Nat.mul_le_mul_right k (by omega)
    have h2 : (idx.val + 1) * k = idx.val * k + k := by ring
    omega⟩

def inLeft {k r m : ℕ} (x : Fin (nIn k r m) → Bool) (j : Fin k) : Bool :=
  x ⟨2 * r * k + j.val, by dsimp only [nIn]; omega⟩

def inRight {k r m : ℕ} (x : Fin (nIn k r m) → Bool) (j : Fin k) : Bool :=
  x ⟨(2 * r + 1) * k + j.val, by
    dsimp only [nIn]
    have : (2 * r + 1) * k = 2 * r * k + k := by ring
    omega⟩

def inA {k r m : ℕ} (x : Fin (nIn k r m) → Bool) (i : Fin ((k + 1) / 2)) : Bool :=
  x ⟨(2 * r + 2) * k + i.val, by
    dsimp only [nIn]
    have : (2 * r + 2) * k = 2 * r * k + 2 * k := by ring
    omega⟩

def inB {k r m : ℕ} (x : Fin (nIn k r m) → Bool) (i : Fin ((k + 1) / 2)) : Bool :=
  x ⟨(2 * r + 2) * k + (k + 1) / 2 + i.val, by
    dsimp only [nIn]
    have : (2 * r + 2) * k = 2 * r * k + 2 * k := by ring
    omega⟩

def inMat {k r m : ℕ} (x : Fin (nIn k r m) → Bool) (i : Fin m) (j : Fin k) : Bool :=
  x ⟨(2 * r + 2) * k + 2 * ((k + 1) / 2) + i.val * k + j.val, by
    dsimp only [nIn]
    have h1 : (i.val + 1) * k ≤ m * k := Nat.mul_le_mul_right k (by omega)
    have h2 : (i.val + 1) * k = i.val * k + k := by ring
    have h3 : (2 * r + 2) * k = 2 * r * k + 2 * k := by ring
    have h4 : m * (k + 1) = m * k + m := by ring
    omega⟩

def inRhs {k r m : ℕ} (x : Fin (nIn k r m) → Bool) (i : Fin m) : Bool :=
  x ⟨(2 * r + 2) * k + 2 * ((k + 1) / 2) + m * k + i.val, by
    dsimp only [nIn]
    have h3 : (2 * r + 2) * k = 2 * r * k + 2 * k := by ring
    have h4 : m * (k + 1) = m * k + m := by ring
    omega⟩

def inRank {k r m : ℕ} (x : Fin (nIn k r m) → Bool) (j : Fin k) : Bool :=
  x ⟨(2 * r + 2) * k + 2 * ((k + 1) / 2) + m * k + m + j.val, by
    dsimp only [nIn]
    have h3 : (2 * r + 2) * k = 2 * r * k + 2 * k := by ring
    have h4 : m * (k + 1) = m * k + m := by ring
    omega⟩

def bitsList (len data : ℕ) : List Bool :=
  (List.range len).map (fun pos => data.testBit pos)

lemma bitsList_length (len data : ℕ) : (bitsList len data).length = len := by
  simp [bitsList]

lemma getD_bitsList {len data p : ℕ} (hp : p < len) :
    (bitsList len data).getD p false = data.testBit p := by
  simp [bitsList, List.getD, hp]

lemma length_flatMap_const {α β : Type*} (l : List α) (f : α → List β) (c : ℕ)
    (hf : ∀ a ∈ l, (f a).length = c) : (l.flatMap f).length = l.length * c := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons,
      hf a List.mem_cons_self, ih (fun b hb => hf b (List.mem_cons_of_mem a hb))]
    ring

lemma getD_flatMap_const {α β : Type*} (l : List α) (f : α → List β) (c : ℕ) (d : β)
    (hf : ∀ a ∈ l, (f a).length = c) (i j : ℕ) (hi : i < l.length) (hj : j < c) :
    (l.flatMap f).getD (i * c + j) d = (f (l[i]'hi)).getD j d := by
  induction l generalizing i with
  | nil => simp at hi
  | cons a l ih =>
    cases i with
    | zero =>
      simp only [List.flatMap_cons, zero_mul, zero_add, List.getElem_cons_zero]
      rw [getD_append_left_lt _ _ _ _ (by rw [hf a List.mem_cons_self]; exact hj)]
    | succ i =>
      simp only [List.flatMap_cons, List.getElem_cons_succ]
      have hlen : (f a).length = c := hf a List.mem_cons_self
      have hge : (f a).length ≤ (i + 1) * c + j := by
        rw [hlen]
        have : (i + 1) * c = i * c + c := by ring
        omega
      have hsub : (i + 1) * c + j - (f a).length = i * c + j := by
        rw [hlen]
        have : (i + 1) * c = i * c + c := by ring
        omega
      simp only [List.getD, List.getElem?_append_right hge, hsub]
      exact ih (fun b hb => hf b (List.mem_cons_of_mem a hb)) i (by simp at hi; omega)

lemma getD_append_right_ge {α : Type*} (l₁ l₂ : List α) (i : ℕ) (d : α) (h : l₁.length ≤ i) :
    (l₁ ++ l₂).getD i d = l₂.getD (i - l₁.length) d := by
  simp [List.getD, List.getElem?_append_right h]

lemma input_pack_spec (k r m : ℕ) (schedule : ℕ → Fin (2 ^ k))
    (leftName rightName : Fin (2 ^ k)) (a b : Fin (2 ^ ((k + 1) / 2)))
    (A : Fin m → Fin (2 ^ k)) (rhs : Fin m → Bool) (rank : Fin (2 ^ k)) :
    let h := (k + 1) / 2
    let inp : List Bool :=
      (List.range (2 * r)).flatMap (fun idx => bitsList k (schedule (idx + 1)).val) ++
      bitsList k leftName.val ++ bitsList k rightName.val ++
      bitsList h a.val ++ bitsList h b.val ++
      (List.ofFn A).flatMap (fun entry => bitsList k entry.val) ++
      List.ofFn rhs ++ bitsList k rank.val
    ∃ x : Fin (nIn k r m) → Bool,
      List.ofFn x = inp ∧
      (∀ idx j, inSched x idx j = (schedule (idx.val + 1)).val.testBit j.val) ∧
      (∀ j, inLeft x j = leftName.val.testBit j.val) ∧
      (∀ j, inRight x j = rightName.val.testBit j.val) ∧
      (∀ i, inA x i = a.val.testBit i.val) ∧
      (∀ i, inB x i = b.val.testBit i.val) ∧
      (∀ i j, inMat x i j = (A i).val.testBit j.val) ∧
      (∀ i, inRhs x i = rhs i) ∧
      (∀ j, inRank x j = rank.val.testBit j.val) := by
  intro h inp
  have hL0 : ((List.range (2 * r)).flatMap (fun idx => bitsList k (schedule (idx + 1)).val)).length = 2 * r * k := by
    rw [length_flatMap_const _ _ k (fun _ _ => bitsList_length _ _), List.length_range]
  have hL5 : ((List.ofFn A).flatMap (fun entry => bitsList k entry.val)).length = m * k := by
    rw [length_flatMap_const _ _ k (fun _ _ => bitsList_length _ _), List.length_ofFn]
  have hinp_len : inp.length = nIn k r m := by
    simp only [inp, List.length_append, hL0, hL5, bitsList_length, List.length_ofFn, nIn, h]
    ring
  let x : Fin (nIn k r m) → Bool := fun p => inp.getD p.val false
  have hof : List.ofFn x = inp := by
    apply List.ext_getElem
    · rw [List.length_ofFn, hinp_len]
    · intro p hp1 hp2
      simp only [List.getElem_ofFn, x, List.getD, List.getElem?_eq_getElem hp2, Option.getD_some]
  have hrk1 : (2 * r + 1) * k = 2 * r * k + k := by ring
  have hrk2 : (2 * r + 2) * k = 2 * r * k + k + k := by ring
  refine ⟨x, hof, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro idx j
    dsimp only [inSched, x, inp]
    have hlt : idx.val * k + j.val < 2 * r * k := by
      have h1 : (idx.val + 1) * k ≤ 2 * r * k := Nat.mul_le_mul_right k (by omega)
      have h2 : (idx.val + 1) * k = idx.val * k + k := by ring
      omega
    simp only [List.append_assoc]
    rw [getD_append_left_lt _ _ _ _ (by rw [hL0]; exact hlt)]
    rw [getD_flatMap_const _ _ k false (fun _ _ => bitsList_length _ _) idx.val j.val (by simp) j.isLt]
    simp only [List.getElem_range]
    exact getD_bitsList j.isLt
  · intro j
    dsimp only [inLeft, x, inp]
    simp only [List.append_assoc]
    rw [getD_append_right_ge _ _ _ _ (by rw [hL0]; omega)]
    rw [hL0, show 2 * r * k + j.val - 2 * r * k = j.val by omega]
    rw [getD_append_left_lt _ _ _ _ (by rw [bitsList_length]; exact j.isLt)]
    exact getD_bitsList j.isLt
  · intro j
    dsimp only [inRight, x, inp]
    simp only [List.append_assoc]
    rw [getD_append_right_ge _ _ _ _ (by rw [hL0]; omega)]
    rw [hL0, getD_append_right_ge _ _ _ _ (by rw [bitsList_length]; omega)]
    rw [bitsList_length, show (2 * r + 1) * k + j.val - 2 * r * k - k = j.val by omega]
    rw [getD_append_left_lt _ _ _ _ (by rw [bitsList_length]; exact j.isLt)]
    exact getD_bitsList j.isLt
  · intro i
    dsimp only [inA, x, inp]
    simp only [List.append_assoc]
    rw [getD_append_right_ge _ _ _ _ (by rw [hL0]; omega)]
    rw [hL0, getD_append_right_ge _ _ _ _ (by rw [bitsList_length]; omega)]
    rw [bitsList_length, getD_append_right_ge _ _ _ _ (by rw [bitsList_length]; omega)]
    rw [bitsList_length, show (2 * r + 2) * k + i.val - 2 * r * k - k - k = i.val by omega]
    rw [getD_append_left_lt _ _ _ _ (by rw [bitsList_length]; exact i.isLt)]
    exact getD_bitsList i.isLt
  · intro i
    dsimp only [inB, x, inp]
    simp only [List.append_assoc]
    rw [getD_append_right_ge _ _ _ _ (by rw [hL0]; omega)]
    rw [hL0, getD_append_right_ge _ _ _ _ (by rw [bitsList_length]; omega)]
    rw [bitsList_length, getD_append_right_ge _ _ _ _ (by rw [bitsList_length]; omega)]
    rw [bitsList_length, getD_append_right_ge _ _ _ _ (by rw [bitsList_length]; dsimp only [h]; omega)]
    rw [bitsList_length, show (2 * r + 2) * k + h + i.val - 2 * r * k - k - k - h = i.val by omega]
    rw [getD_append_left_lt _ _ _ _ (by rw [bitsList_length]; exact i.isLt)]
    exact getD_bitsList i.isLt
  · intro i j
    dsimp only [inMat, x, inp]
    simp only [List.append_assoc]
    rw [getD_append_right_ge _ _ _ _ (by rw [hL0]; omega)]
    rw [hL0, getD_append_right_ge _ _ _ _ (by rw [bitsList_length]; omega)]
    rw [bitsList_length, getD_append_right_ge _ _ _ _ (by rw [bitsList_length]; omega)]
    rw [bitsList_length, getD_append_right_ge _ _ _ _ (by rw [bitsList_length]; dsimp only [h]; omega)]
    rw [bitsList_length, getD_append_right_ge _ _ _ _ (by rw [bitsList_length]; dsimp only [h]; omega)]
    rw [bitsList_length, show (2 * r + 2) * k + 2 * h + i.val * k + j.val - 2 * r * k - k - k - h - h =
      i.val * k + j.val by omega]
    have hlt : i.val * k + j.val < m * k := by
      have h1 : (i.val + 1) * k ≤ m * k := Nat.mul_le_mul_right k (by omega)
      have h2 : (i.val + 1) * k = i.val * k + k := by ring
      omega
    rw [getD_append_left_lt _ _ _ _ (by rw [hL5]; exact hlt)]
    rw [getD_flatMap_const _ _ k false (fun _ _ => bitsList_length _ _) i.val j.val (by simp) j.isLt]
    simp only [List.getElem_ofFn]
    exact getD_bitsList j.isLt
  · intro i
    dsimp only [inRhs, x, inp]
    simp only [List.append_assoc]
    rw [getD_append_right_ge _ _ _ _ (by rw [hL0]; omega)]
    rw [hL0, getD_append_right_ge _ _ _ _ (by rw [bitsList_length]; omega)]
    rw [bitsList_length, getD_append_right_ge _ _ _ _ (by rw [bitsList_length]; omega)]
    rw [bitsList_length, getD_append_right_ge _ _ _ _ (by rw [bitsList_length]; dsimp only [h]; omega)]
    rw [bitsList_length, getD_append_right_ge _ _ _ _ (by rw [bitsList_length]; dsimp only [h]; omega)]
    rw [bitsList_length, getD_append_right_ge _ _ _ _ (by rw [hL5]; dsimp only [h]; omega)]
    rw [hL5, show (2 * r + 2) * k + 2 * h + m * k + i.val - 2 * r * k - k - k - h - h - m * k = i.val by omega]
    rw [getD_append_left_lt _ _ _ _ (by simp [i.isLt])]
    simp [List.getD, i.isLt]
  · intro j
    dsimp only [inRank, x, inp]
    simp only [List.append_assoc]
    rw [getD_append_right_ge _ _ _ _ (by rw [hL0]; omega)]
    rw [hL0, getD_append_right_ge _ _ _ _ (by rw [bitsList_length]; omega)]
    rw [bitsList_length, getD_append_right_ge _ _ _ _ (by rw [bitsList_length]; omega)]
    rw [bitsList_length, getD_append_right_ge _ _ _ _ (by rw [bitsList_length]; dsimp only [h]; omega)]
    rw [bitsList_length, getD_append_right_ge _ _ _ _ (by rw [bitsList_length]; dsimp only [h]; omega)]
    rw [bitsList_length, getD_append_right_ge _ _ _ _ (by rw [hL5]; dsimp only [h]; omega)]
    rw [hL5, getD_append_right_ge _ _ _ _ (by simp; dsimp only [h]; omega)]
    rw [List.length_ofFn,
      show (2 * r + 2) * k + 2 * h + m * k + m + j.val - 2 * r * k - k - k - h - h - m * k - m = j.val by omega]
    exact getD_bitsList j.isLt

/-! #### Bit-vector cipher definitions & equivalence with `Nat` definitions -/

def rotN (k offset x : ℕ) : ℕ :=
  ((x <<< (offset % k)) ||| (x >>> (k - offset % k))) % 2 ^ k

def mixN (k gap value : ℕ) : ℕ :=
  value ^^^ rotN k gap value ^^^ rotN k (k - gap) value

def chiN (k word : ℕ) : ℕ :=
  (List.range k).foldl (fun acc site =>
    acc ||| ((xor (word.testBit site)
      (!(word.testBit ((site + 1) % k)) && word.testBit ((site + 2) % k))).toNat <<< site)) 0

def stepN (k r : ℕ) (constants : ℕ → Fin (2 ^ k)) (col : Bool) (raw prev t : ℕ) : ℕ :=
  chiN k (mixN k (if col then 2 else 1) prev) ^^^
    rotN k (if col then 3 * t + 1 else 2 * (t - 1)) raw ^^^
    (constants (if col then r + t else t)).val

def stateN (k r : ℕ) (c : ℕ → Fin (2 ^ k)) (side : Bool) (key name : ℕ) : ℕ :=
  (List.range r).foldl (fun v tick => stepN k r c side key v (tick + 1))
    (rotN k (if side then 3 else 1) key ^^^ name)

def parityN (k natWord : ℕ) : Bool :=
  (List.range k).foldl (fun total bitPos => xor total (natWord.testBit bitPos)) false

def rotV {k : ℕ} (hk : 0 < k) (offset : ℕ) (v : Fin k → Bool) : Fin k → Bool :=
  fun j => v ⟨(j.val + k - offset % k) % k, Nat.mod_lt _ hk⟩

def mixV {k : ℕ} (hk : 0 < k) (gap : ℕ) (v : Fin k → Bool) : Fin k → Bool :=
  fun j => xor (xor (v j) (rotV hk gap v j)) (rotV hk (k - gap) v j)

def chiV {k : ℕ} (hk : 0 < k) (v : Fin k → Bool) : Fin k → Bool :=
  fun j => xor (v j) (!(v ⟨(j.val + 1) % k, Nat.mod_lt _ hk⟩) && v ⟨(j.val + 2) % k, Nat.mod_lt _ hk⟩)

def stepV {k : ℕ} (hk : 0 < k) (r : ℕ) (c : ℕ → Fin k → Bool) (col : Bool)
    (raw prev : Fin k → Bool) (t : ℕ) : Fin k → Bool :=
  let cm := chiV hk (mixV hk (if col then 2 else 1) prev)
  let rf := rotV hk (if col then 3 * t + 1 else 2 * (t - 1)) raw
  fun j => xor (xor (cm j) (rf j)) (c (if col then r + t else t) j)

def stateVSteps {k : ℕ} (hk : 0 < k) (r : ℕ) (c : ℕ → Fin k → Bool) (col : Bool)
    (raw name : Fin k → Bool) : ℕ → Fin k → Bool
  | 0 => fun j => xor (rotV hk (if col then 3 else 1) raw j) (name j)
  | t + 1 => stepV hk r c col raw (stateVSteps hk r c col raw name t) (t + 1)

def stateV {k : ℕ} (hk : 0 < k) (r : ℕ) (c : ℕ → Fin k → Bool) (col : Bool)
    (raw name : Fin k → Bool) : Fin k → Bool :=
  stateVSteps hk r c col raw name r

def stateNoLastFeedV {k : ℕ} (hk : 0 < k) (r : ℕ) (c : ℕ → Fin k → Bool) (col : Bool)
    (raw name : Fin k → Bool) : Fin k → Bool :=
  let prev := stateVSteps hk r c col raw name (r - 1)
  let cm := chiV hk (mixV hk (if col then 2 else 1) prev)
  fun j => xor (cm j) (c (if col then r + r else r) j)

lemma stateV_eq_xor_lastFeed {k : ℕ} (hk : 0 < k) {r : ℕ} (hr : 1 ≤ r)
    (c : ℕ → Fin k → Bool) (col : Bool) (raw name : Fin k → Bool) (j : Fin k) :
    stateV hk r c col raw name j =
      xor (stateNoLastFeedV hk r c col raw name j)
        (rotV hk (if col then 3 * r + 1 else 2 * (r - 1)) raw j) := by
  have hr_eq : r = (r - 1) + 1 := by omega
  unfold stateV stateNoLastFeedV
  conv_lhs => rw [hr_eq]
  simp only [stateVSteps, stepV, ← hr_eq]
  cases chiV hk (mixV hk (if col then 2 else 1) (stateVSteps hk r c col raw name (r - 1))) j <;>
  cases rotV hk (if col then 3 * r + 1 else 2 * (r - 1)) raw j <;>
  cases c (if col then r + r else r) j <;> decide

lemma rotN_lt {k : ℕ} (offset x : ℕ) : rotN k offset x < 2 ^ k :=
  Nat.mod_lt _ (by positivity)

lemma testBit_rotN {k : ℕ} (hk : 0 < k) (offset x : ℕ) (hx : x < 2 ^ k) (j : Fin k) :
    (rotN k offset x).testBit j.val = x.testBit ((j.val + k - offset % k) % k) := by
  unfold rotN
  rw [Nat.testBit_mod_two_pow, decide_eq_true j.isLt, Bool.true_and,
    Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
  have hmod : offset % k < k := Nat.mod_lt offset hk
  by_cases hle : offset % k ≤ j.val
  · have hge : k ≤ k - offset % k + j.val := by omega
    have hfalse : x.testBit (k - offset % k + j.val) = false :=
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) hge))
    have hidx : (j.val + k - offset % k) % k = j.val - offset % k := by
      have : j.val + k - offset % k = (j.val - offset % k) + k := by omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    simp [hle, hfalse, hidx]
  · have hlt : k - offset % k + j.val < k := by omega
    have hidx : (j.val + k - offset % k) % k = k - offset % k + j.val := by
      rw [show j.val + k - offset % k = k - offset % k + j.val by omega, Nat.mod_eq_of_lt hlt]
    simp [hle, hidx]

lemma mixN_lt {k : ℕ} (gap value : ℕ) (hv : value < 2 ^ k) : mixN k gap value < 2 ^ k :=
  Nat.xor_lt_two_pow (Nat.xor_lt_two_pow hv (rotN_lt _ _)) (rotN_lt _ _)

lemma testBit_mixN {k : ℕ} (hk : 0 < k) (gap value : ℕ) (hv : value < 2 ^ k) (j : Fin k) :
    (mixN k gap value).testBit j.val =
      mixV hk gap (fun i => value.testBit i.val) j := by
  unfold mixN mixV rotV
  rw [Nat.testBit_xor, Nat.testBit_xor, testBit_rotN hk gap value hv j,
    testBit_rotN hk (k - gap) value hv j]

lemma chiN_pref_spec {k : ℕ} (hk : 0 < k) (word : ℕ) :
    ∀ t ≤ k,
      let acc := (List.range t).foldl (fun acc site =>
        acc ||| ((xor (word.testBit site)
          (!(word.testBit ((site + 1) % k)) && word.testBit ((site + 2) % k))).toNat <<< site)) 0
      acc < 2 ^ t ∧
      (∀ j < t, acc.testBit j =
        xor (word.testBit j) (!(word.testBit ((j + 1) % k)) && word.testBit ((j + 2) % k))) ∧
      (∀ j, t ≤ j → acc.testBit j = false) := by
  intro t ht
  induction t with
  | zero => simp
  | succ t ih =>
    obtain ⟨hlt, hlo, hhi⟩ := ih (by omega)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    set acc := (List.range t).foldl (fun acc site =>
      acc ||| ((xor (word.testBit site)
        (!(word.testBit ((site + 1) % k)) && word.testBit ((site + 2) % k))).toNat <<< site)) 0
    set bit := xor (word.testBit t) (!(word.testBit ((t + 1) % k)) && word.testBit ((t + 2) % k))
    have hbit_lt : bit.toNat <<< t < 2 ^ (t + 1) := by
      rw [Nat.shiftLeft_eq]
      have hb : bit.toNat ≤ 1 := by cases bit <;> decide
      have hpow : 2 ^ (t + 1) = 2 * 2 ^ t := by ring
      have := Nat.mul_le_mul_right (2 ^ t) hb
      have hpos : 0 < 2 ^ t := by positivity
      omega
    have hlt' : acc ||| (bit.toNat <<< t) < 2 ^ (t + 1) :=
      Nat.or_lt_two_pow (lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by decide) (by omega))) hbit_lt
    refine ⟨hlt', ?_, ?_⟩
    · intro j hj
      rw [Nat.testBit_or, Nat.testBit_shiftLeft]
      by_cases hjt : j < t
      · rw [hlo j hjt, decide_eq_false (by omega)]; simp
      · have hjeq : j = t := by omega
        subst hjeq
        rw [hhi j (le_refl j), decide_eq_true (le_refl j), Bool.true_and, Nat.sub_self, Bool.false_or]
        change bit.toNat.testBit 0 = bit
        cases bit <;> decide
    · intro j hj
      exact Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hlt' (Nat.pow_le_pow_right (by decide) hj))

lemma chiN_lt {k : ℕ} (hk : 0 < k) (word : ℕ) : chiN k word < 2 ^ k :=
  (chiN_pref_spec hk word k le_rfl).1

lemma testBit_chiN {k : ℕ} (hk : 0 < k) (word : ℕ) (j : Fin k) :
    (chiN k word).testBit j.val = chiV hk (fun i => word.testBit i.val) j :=
  (chiN_pref_spec hk word k le_rfl).2.1 j.val j.isLt

lemma stepN_lt {k : ℕ} (hk : 0 < k) (r : ℕ) (c : ℕ → Fin (2 ^ k)) (col : Bool)
    (raw prev t : ℕ) : stepN k r c col raw prev t < 2 ^ k :=
  Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (chiN_lt hk _) (rotN_lt _ _)) (c _).isLt

lemma testBit_stepN {k : ℕ} (hk : 0 < k) (r : ℕ) (c : ℕ → Fin (2 ^ k)) (col : Bool)
    (raw prev t : ℕ) (hraw : raw < 2 ^ k) (hprev : prev < 2 ^ k) (j : Fin k) :
    (stepN k r c col raw prev t).testBit j.val =
      stepV hk r (fun idx i => (c idx).val.testBit i.val) col
        (fun i => raw.testBit i.val) (fun i => prev.testBit i.val) t j := by
  unfold stepN stepV
  rw [Nat.testBit_xor, Nat.testBit_xor, testBit_chiN hk, testBit_rotN hk _ raw hraw j]
  have hmix : (fun i : Fin k => (mixN k (if col then 2 else 1) prev).testBit i.val) =
      mixV hk (if col then 2 else 1) (fun i => prev.testBit i.val) :=
    funext (testBit_mixN hk _ prev hprev)
  rw [hmix]
  rfl

lemma stateN_spec {k : ℕ} (hk : 0 < k) (r : ℕ) (c : ℕ → Fin (2 ^ k)) (col : Bool)
    (key name : ℕ) (hkey : key < 2 ^ k) (hname : name < 2 ^ k) :
    ∀ t : ℕ,
      let v := (List.range t).foldl (fun v tick => stepN k r c col key v (tick + 1))
        (rotN k (if col then 3 else 1) key ^^^ name)
      v < 2 ^ k ∧
      ∀ j : Fin k, v.testBit j.val =
        stateVSteps hk r (fun idx i => (c idx).val.testBit i.val) col
          (fun i => key.testBit i.val) (fun i => name.testBit i.val) t j := by
  intro t
  induction t with
  | zero =>
    refine ⟨Nat.xor_lt_two_pow (rotN_lt _ _) hname, fun j => ?_⟩
    simp only [List.range_zero, List.foldl_nil, stateVSteps, Nat.testBit_xor,
      testBit_rotN hk _ key hkey j, rotV]
  | succ t ih =>
    obtain ⟨hlt, hbits⟩ := ih
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    refine ⟨stepN_lt hk r c col key _ (t + 1), fun j => ?_⟩
    rw [testBit_stepN hk r c col key _ (t + 1) hkey hlt j]
    simp only [stateVSteps]
    congr 2
    funext i; exact hbits i

lemma stateN_lt {k : ℕ} (hk : 0 < k) (r : ℕ) (c : ℕ → Fin (2 ^ k)) (col : Bool)
    (key name : ℕ) (hkey : key < 2 ^ k) (hname : name < 2 ^ k) :
    stateN k r c col key name < 2 ^ k :=
  (stateN_spec hk r c col key name hkey hname r).1

lemma testBit_stateN {k : ℕ} (hk : 0 < k) (r : ℕ) (c : ℕ → Fin (2 ^ k)) (col : Bool)
    (key name : ℕ) (hkey : key < 2 ^ k) (hname : name < 2 ^ k) (j : Fin k) :
    (stateN k r c col key name).testBit j.val =
      stateV hk r (fun idx i => (c idx).val.testBit i.val) col
        (fun i => key.testBit i.val) (fun i => name.testBit i.val) j :=
  (stateN_spec hk r c col key name hkey hname r).2 j

lemma state_shr_eq_iff {k : ℕ} (v : ℕ) (hv : v < 2 ^ k) (t : Fin (2 ^ ((k + 1) / 2))) :
    let h := (k + 1) / 2
    let z := k - h
    v >>> z = t.val ↔ ∀ i : Fin h, v.testBit (z + i.val) = t.val.testBit i.val := by
  intro h z
  have hzh : z + h = k := by dsimp only [z, h]; omega
  constructor
  · intro heq i
    rw [← heq, Nat.testBit_shiftRight]
  · intro hall
    apply Nat.eq_of_testBit_eq
    intro p
    rw [Nat.testBit_shiftRight]
    by_cases hp : p < h
    · exact hall ⟨p, hp⟩
    · have h1 : v.testBit (z + p) = false :=
        Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hv (Nat.pow_le_pow_right (by decide) (by omega)))
      have h2 : t.val.testBit p = false :=
        Nat.testBit_eq_false_of_lt (lt_of_lt_of_le t.isLt (Nat.pow_le_pow_right (by decide) (by omega)))
      rw [h1, h2]

lemma parityN_eq_finRange {k : ℕ} (w a : ℕ) :
    parityN k (w &&& a) =
      (List.finRange k).foldl (fun acc j => xor acc (w.testBit j.val && a.testBit j.val)) false := by
  unfold parityN
  have h : ∀ t ≤ k,
      (List.range t).foldl (fun total bitPos => xor total ((w &&& a).testBit bitPos)) false =
      ((List.finRange k).take t).foldl (fun acc j => xor acc (w.testBit j.val && a.testBit j.val)) false := by
    intro t ht
    induction t with
    | zero => simp
    | succ t ih =>
      have ht_lt : t < k := by omega
      have htake : (List.finRange k).take (t + 1) = (List.finRange k).take t ++ [⟨t, ht_lt⟩] := by
        rw [List.take_succ_eq_append_getElem (by simp [ht_lt])]; simp [List.getElem_finRange]
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
        htake, List.foldl_append, List.foldl_cons, List.foldl_nil, ih (by omega), Nat.testBit_and]
  have h1 := h k le_rfl
  rwa [List.take_of_length_le (by simp)] at h1
/-! ### Part 4: Cone Locality & Exact Joint Sweep Reconstruction -/

def ixMod {k : ℕ} (hk : 0 < k) (z : ℤ) : Fin k :=
  ⟨(z % (k : ℤ)).toNat, by
    have h1 : 0 ≤ z % (k : ℤ) := Int.emod_nonneg z (by omega)
    have h2 : z % (k : ℤ) < (k : ℤ) := Int.emod_lt_of_pos z (by omega)
    omega⟩

lemma ixMod_val_coe {k : ℕ} (hk : 0 < k) (z : ℤ) :
    ((ixMod hk z).val : ℤ) = z % (k : ℤ) := by
  dsimp only [ixMod]
  exact Int.toNat_of_nonneg (Int.emod_nonneg z (by omega))

lemma ixMod_eq_iff {k : ℕ} (hk : 0 < k) (z₁ z₂ : ℤ) :
    ixMod hk z₁ = ixMod hk z₂ ↔ z₁ % (k : ℤ) = z₂ % (k : ℤ) := by
  constructor
  · intro h
    have hv := congrArg (fun p : Fin k => (p.val : ℤ)) h
    rwa [ixMod_val_coe, ixMod_val_coe] at hv
  · intro h
    apply Fin.ext
    dsimp only [ixMod]
    rw [h]

lemma ixMod_of_fin {k : ℕ} (hk : 0 < k) (j : Fin k) : ixMod hk (j.val : ℤ) = j := by
  apply Fin.ext
  dsimp only [ixMod]
  have h1 : (j.val : ℤ) % (k : ℤ) = (j.val : ℤ) := Int.emod_eq_of_lt (by omega) (by omega)
  rw [h1]; simp

lemma ixMod_add_val {k : ℕ} (hk : 0 < k) (z d : ℤ) :
    ixMod hk (((ixMod hk z).val : ℤ) + d) = ixMod hk (z + d) := by
  rw [ixMod_eq_iff, ixMod_val_coe, Int.add_emod, Int.emod_emod, ← Int.add_emod]

lemma ixMod_sub_val {k : ℕ} (hk : 0 < k) (z d : ℤ) :
    ixMod hk (((ixMod hk z).val : ℤ) - d) = ixMod hk (z - d) := by
  rw [ixMod_eq_iff, ixMod_val_coe, Int.sub_emod, Int.emod_emod, ← Int.sub_emod]

lemma rotV_idx_eq_ixMod {k : ℕ} (hk : 0 < k) (offset : ℕ) (j : Fin k) :
    (⟨(j.val + k - offset % k) % k, Nat.mod_lt _ hk⟩ : Fin k) =
      ixMod hk ((j.val : ℤ) - (offset : ℤ)) := by
  apply Fin.ext
  have h1 : (((j.val + k - offset % k) % k : ℕ) : ℤ) =
      ((j.val : ℤ) - (offset : ℤ)) % (k : ℤ) := by
    have hmod : offset % k < k := Nat.mod_lt offset hk
    have hsub : ((j.val + k - offset % k : ℕ) : ℤ) = (j.val : ℤ) + (k : ℤ) - ((offset % k : ℕ) : ℤ) := by
      omega
    rw [Int.natCast_emod, hsub]
    have h1' : ((offset % k : ℕ) : ℤ) = (offset : ℤ) % (k : ℤ) := Int.natCast_emod offset k
    rw [h1']
    rw [Int.sub_emod, Int.add_emod, Int.emod_self, add_zero, Int.emod_emod, Int.emod_emod, ← Int.sub_emod]
  have h2 := ixMod_val_coe hk ((j.val : ℤ) - (offset : ℤ))
  dsimp only; omega

lemma rotV_gap_rev_eq_ixMod {k : ℕ} (hk : 0 < k) {gap : ℕ} (hgap : gap < k) (j : Fin k) :
    (⟨(j.val + k - (k - gap) % k) % k, Nat.mod_lt _ hk⟩ : Fin k) =
      ixMod hk ((j.val : ℤ) + (gap : ℤ)) := by
  rw [rotV_idx_eq_ixMod hk (k - gap) j, ixMod_eq_iff]
  have hsub : (j.val : ℤ) - ((k - gap : ℕ) : ℤ) = ((j.val : ℤ) + (gap : ℤ)) - (k : ℤ) := by omega
  rw [hsub, Int.sub_emod_right]

lemma add_mod_eq_ixMod {k : ℕ} (hk : 0 < k) (j : Fin k) (d : ℕ) :
    (⟨(j.val + d) % k, Nat.mod_lt _ hk⟩ : Fin k) = ixMod hk ((j.val : ℤ) + (d : ℤ)) := by
  apply Fin.ext
  have h1 : (((j.val + d) % k : ℕ) : ℤ) = ((j.val : ℤ) + (d : ℤ)) % (k : ℤ) := by
    rw [Int.natCast_emod]; push_cast; rfl
  have h2 := ixMod_val_coe hk ((j.val : ℤ) + (d : ℤ))
  dsimp only; omega

def coneLo (col : Bool) (t : ℕ) : ℤ :=
  if col then -((max (2 * t + 3) (3 * t + 1) : ℕ) : ℤ)
  else -((if t = 0 then 1 else max (t + 1) (2 * t - 2) : ℕ) : ℤ)

def coneHi (col : Bool) (t : ℕ) : ℤ :=
  if col then (4 * t : ℤ) - 3 else (3 * t : ℤ) - 1

lemma stateVSteps_congr {k : ℕ} (hk : 0 < k) (hk2 : 2 < k) (r : ℕ)
    (c : ℕ → Fin k → Bool) (col : Bool) (raw₁ raw₂ name : Fin k → Bool) :
    ∀ (t : ℕ) (s : Fin k),
      (∀ d : ℤ, coneLo col t ≤ d → d ≤ coneHi col t →
        raw₁ (ixMod hk ((s.val : ℤ) + d)) = raw₂ (ixMod hk ((s.val : ℤ) + d))) →
      stateVSteps hk r c col raw₁ name t s = stateVSteps hk r c col raw₂ name t s := by
  intro t
  induction t with
  | zero =>
    intro s hagree
    dsimp only [stateVSteps, rotV]
    rw [rotV_idx_eq_ixMod hk]
    have hidx : ixMod hk ((s.val : ℤ) - ((if col then 3 else 1 : ℕ) : ℤ)) =
        ixMod hk ((s.val : ℤ) + (if col then (-3 : ℤ) else (-1 : ℤ))) := by
      cases col <;> simp [sub_eq_add_neg]
    rw [hidx]
    have h1 := hagree (if col then -3 else -1)
      (by cases col <;> simp [coneLo]) (by cases col <;> simp [coneHi])
    rw [h1]
  | succ t ih =>
    intro s hagree
    dsimp only [stateVSteps, stepV]
    have hfeed : rotV hk (if col then 3 * (t + 1) + 1 else 2 * (t + 1 - 1)) raw₁ s =
        rotV hk (if col then 3 * (t + 1) + 1 else 2 * (t + 1 - 1)) raw₂ s := by
      dsimp only [rotV]; rw [rotV_idx_eq_ixMod hk]
      let fd : ℤ := -((if col then 3 * (t + 1) + 1 else 2 * (t + 1 - 1) : ℕ) : ℤ)
      have heq : ((s.val : ℤ) - ((if col then 3 * (t + 1) + 1 else 2 * (t + 1 - 1) : ℕ) : ℤ)) =
          (s.val : ℤ) + fd := by dsimp only [fd]; omega
      rw [heq]
      apply hagree fd
      · cases col <;> simp [coneLo, fd] <;> omega
      · cases col <;> simp [coneHi, fd] <;> omega
    have hgap : (if col then 2 else 1) < k := by cases col <;> simp <;> omega
    have hprev_eq : ∀ d1 : ℤ,
        -(if col then (2 : ℤ) else 1) ≤ d1 → d1 ≤ (if col then (4 : ℤ) else 3) →
        stateVSteps hk r c col raw₁ name t (ixMod hk ((s.val : ℤ) + d1)) =
        stateVSteps hk r c col raw₂ name t (ixMod hk ((s.val : ℤ) + d1)) := by
      intro d1 hd1_lo hd1_hi
      apply ih (ixMod hk ((s.val : ℤ) + d1))
      intro d2 hd2_lo hd2_hi
      rw [ixMod_add_val, add_assoc]
      apply hagree (d1 + d2)
      · cases col
        · simp only [coneLo, Bool.false_eq_true, ↓reduceIte] at hd1_lo hd2_lo ⊢
          by_cases ht0 : t = 0 <;> simp [ht0] at hd2_lo ⊢ <;> omega
        · simp only [coneLo, ↓reduceIte] at hd1_lo hd2_lo ⊢; omega
      · cases col <;> simp only [coneHi, ↓reduceIte, Bool.false_eq_true] at hd1_hi hd2_hi ⊢ <;> omega
    have hmix_eq : ∀ off : ℕ, off ≤ 2 →
        mixV hk (if col then 2 else 1) (stateVSteps hk r c col raw₁ name t)
          (⟨(s.val + off) % k, Nat.mod_lt _ hk⟩) =
        mixV hk (if col then 2 else 1) (stateVSteps hk r c col raw₂ name t)
          (⟨(s.val + off) % k, Nat.mod_lt _ hk⟩) := by
      intro off hoff
      set p : Fin k := ⟨(s.val + off) % k, Nat.mod_lt _ hk⟩
      have hp : p = ixMod hk ((s.val : ℤ) + (off : ℤ)) := add_mod_eq_ixMod hk s off
      dsimp only [mixV, rotV]
      rw [rotV_idx_eq_ixMod hk _ p, rotV_gap_rev_eq_ixMod hk hgap p, hp, ixMod_sub_val, ixMod_add_val]
      have h0 := hprev_eq (off : ℤ) (by cases col <;> simp <;> omega) (by cases col <;> simp <;> omega)
      have h1 := hprev_eq ((off : ℤ) - ((if col then 2 else 1 : ℕ) : ℤ))
        (by cases col <;> simp <;> omega) (by cases col <;> simp <;> omega)
      have h2 := hprev_eq ((off : ℤ) + ((if col then 2 else 1 : ℕ) : ℤ))
        (by cases col <;> simp <;> omega) (by cases col <;> simp <;> omega)
      have heq1 : (s.val : ℤ) + (off : ℤ) - ((if col then 2 else 1 : ℕ) : ℤ) =
          (s.val : ℤ) + ((off : ℤ) - ((if col then 2 else 1 : ℕ) : ℤ)) := by ring
      have heq2 : (s.val : ℤ) + (off : ℤ) + ((if col then 2 else 1 : ℕ) : ℤ) =
          (s.val : ℤ) + ((off : ℤ) + ((if col then 2 else 1 : ℕ) : ℤ)) := by ring
      rw [heq1, heq2, h0, h1, h2]
    have hchi_eq : chiV hk (mixV hk (if col then 2 else 1) (stateVSteps hk r c col raw₁ name t)) s =
        chiV hk (mixV hk (if col then 2 else 1) (stateVSteps hk r c col raw₂ name t)) s := by
      dsimp only [chiV]
      have h0 : s = ⟨(s.val + 0) % k, Nat.mod_lt _ hk⟩ := by
        apply Fin.ext; simp [Nat.mod_eq_of_lt s.isLt]
      rw [h0, hmix_eq 0 (by omega), ← h0, hmix_eq 1 (by omega), hmix_eq 2 (by omega)]
    rw [hchi_eq, hfeed]

lemma stateNoLastFeedV_congr {k : ℕ} (hk : 0 < k) (hk2 : 2 < k) {r : ℕ} (hr : 4 ≤ r)
    (c : ℕ → Fin k → Bool) (col : Bool) (raw₁ raw₂ name : Fin k → Bool) (s : Fin k)
    (hagree : ∀ d : ℤ,
      (if col then -(3 * r : ℤ) else -(2 * r - 3 : ℤ)) ≤ d →
      d ≤ (if col then (4 * r - 3 : ℤ) else (3 * r - 1 : ℤ)) →
      raw₁ (ixMod hk ((s.val : ℤ) + d)) = raw₂ (ixMod hk ((s.val : ℤ) + d))) :
    stateNoLastFeedV hk r c col raw₁ name s = stateNoLastFeedV hk r c col raw₂ name s := by
  dsimp only [stateNoLastFeedV]
  have hgap : (if col then 2 else 1) < k := by cases col <;> simp <;> omega
  have hprev_eq : ∀ d1 : ℤ,
      -(if col then (2 : ℤ) else 1) ≤ d1 → d1 ≤ (if col then (4 : ℤ) else 3) →
      stateVSteps hk r c col raw₁ name (r - 1) (ixMod hk ((s.val : ℤ) + d1)) =
      stateVSteps hk r c col raw₂ name (r - 1) (ixMod hk ((s.val : ℤ) + d1)) := by
    intro d1 hd1_lo hd1_hi
    apply stateVSteps_congr hk hk2 r c col raw₁ raw₂ name (r - 1) (ixMod hk ((s.val : ℤ) + d1))
    intro d2 hd2_lo hd2_hi
    rw [ixMod_add_val, add_assoc]
    apply hagree (d1 + d2)
    · cases col
      · simp only [coneLo, Bool.false_eq_true, ↓reduceIte] at hd1_lo hd2_lo ⊢
        have hr1 : r - 1 ≠ 0 := by omega
        simp only [hr1, ↓reduceIte] at hd2_lo
        omega
      · simp only [coneLo, ↓reduceIte] at hd1_lo hd2_lo ⊢; omega
    · cases col <;> simp only [coneHi, ↓reduceIte, Bool.false_eq_true] at hd1_hi hd2_hi ⊢ <;> omega
  have hmix_eq : ∀ off : ℕ, off ≤ 2 →
      mixV hk (if col then 2 else 1) (stateVSteps hk r c col raw₁ name (r - 1))
        (⟨(s.val + off) % k, Nat.mod_lt _ hk⟩) =
      mixV hk (if col then 2 else 1) (stateVSteps hk r c col raw₂ name (r - 1))
        (⟨(s.val + off) % k, Nat.mod_lt _ hk⟩) := by
    intro off hoff
    set p : Fin k := ⟨(s.val + off) % k, Nat.mod_lt _ hk⟩
    have hp : p = ixMod hk ((s.val : ℤ) + (off : ℤ)) := add_mod_eq_ixMod hk s off
    dsimp only [mixV, rotV]
    rw [rotV_idx_eq_ixMod hk _ p, rotV_gap_rev_eq_ixMod hk hgap p, hp, ixMod_sub_val, ixMod_add_val]
    have h0 := hprev_eq (off : ℤ) (by cases col <;> simp <;> omega) (by cases col <;> simp <;> omega)
    have h1 := hprev_eq ((off : ℤ) - ((if col then 2 else 1 : ℕ) : ℤ))
      (by cases col <;> simp <;> omega) (by cases col <;> simp <;> omega)
    have h2 := hprev_eq ((off : ℤ) + ((if col then 2 else 1 : ℕ) : ℤ))
      (by cases col <;> simp <;> omega) (by cases col <;> simp <;> omega)
    have heq1 : (s.val : ℤ) + (off : ℤ) - ((if col then 2 else 1 : ℕ) : ℤ) =
        (s.val : ℤ) + ((off : ℤ) - ((if col then 2 else 1 : ℕ) : ℤ)) := by ring
    have heq2 : (s.val : ℤ) + (off : ℤ) + ((if col then 2 else 1 : ℕ) : ℤ) =
        (s.val : ℤ) + ((off : ℤ) + ((if col then 2 else 1 : ℕ) : ℤ)) := by ring
    rw [heq1, heq2, h0, h1, h2]
  have hchi_eq : chiV hk (mixV hk (if col then 2 else 1) (stateVSteps hk r c col raw₁ name (r - 1))) s =
      chiV hk (mixV hk (if col then 2 else 1) (stateVSteps hk r c col raw₂ name (r - 1))) s := by
    dsimp only [chiV]
    have h0 : s = ⟨(s.val + 0) % k, Nat.mod_lt _ hk⟩ := by
      apply Fin.ext; simp [Nat.mod_eq_of_lt s.isLt]
    rw [h0, hmix_eq 0 (by omega), ← h0, hmix_eq 1 (by omega), hmix_eq 2 (by omega)]
  rw [hchi_eq]

/-! #### Seed positions, free positions, and joint sweep reconstruction -/

def hOf (k : ℕ) : ℕ := (k + 1) / 2
def zOf (k : ℕ) : ℕ := k - (k + 1) / 2
def uOf (r : ℕ) : ℕ := 5 * r - 3
def extraOf (k r : ℕ) : ℕ := min (r - 2) (zOf k - 6 * r)
def seedWidthOf (k r : ℕ) : ℕ := min k (uOf r) + extraOf k r
def seedLen (k r : ℕ) : ℕ := if k ≤ uOf r then k else uOf r + extraOf k r

lemma seedLen_le_seedWidth (k r : ℕ) : seedLen k r ≤ seedWidthOf k r := by
  unfold seedLen seedWidthOf; split_ifs <;> omega

lemma seedLen_le_k {k r : ℕ} (hr : 4 ≤ r) : seedLen k r ≤ k := by
  unfold seedLen uOf extraOf zOf
  split_ifs with h
  · exact le_rfl
  · omega

def isFree (k r : ℕ) (j : Fin k) : Bool :=
  decide (uOf r < k ∧ 4 * r - 3 ≤ j.val ∧ j.val + 3 * r + 2 ≤ zOf k)

def isSeed (k r : ℕ) (j : Fin k) : Bool :=
  if k ≤ uOf r then true
  else decide (k - (2 * r - 2) ≤ j.val ∨ j.val < 3 * r - 1 + extraOf k r)

def seedPos (k r : ℕ) (hr : 4 ≤ r) (i : Fin (seedLen k r)) : Fin k :=
  if h : k ≤ uOf r then ⟨i.val, by have := i.isLt; simp only [seedLen, h, ↓reduceIte] at this; exact this⟩
  else if hi : i.val < 2 * r - 2 then ⟨k - (2 * r - 2) + i.val, by
    have := i.isLt; simp only [seedLen, h, ↓reduceIte] at this; unfold uOf at h; omega⟩
  else ⟨i.val - (2 * r - 2), by
    have := i.isLt; simp only [seedLen, h, ↓reduceIte] at this; unfold uOf extraOf zOf at *; omega⟩

def seedIdxOf (k r : ℕ) (hr : 4 ≤ r) (j : Fin k) : Option (Fin (seedLen k r)) :=
  if h : k ≤ uOf r then some ⟨j.val, by simp only [seedLen, h, ↓reduceIte]; exact j.isLt⟩
  else if hhi : k - (2 * r - 2) ≤ j.val then
    some ⟨j.val - (k - (2 * r - 2)), by simp only [seedLen, h, ↓reduceIte]; unfold uOf at h ⊢; omega⟩
  else if hlo : j.val < 3 * r - 1 + extraOf k r then
    some ⟨2 * r - 2 + j.val, by simp only [seedLen, h, ↓reduceIte]; unfold uOf at h ⊢; omega⟩
  else none

lemma seedIdxOf_seedPos (k r : ℕ) (hr : 4 ≤ r) (i : Fin (seedLen k r)) :
    seedIdxOf k r hr (seedPos k r hr i) = some i := by
  by_cases h : k ≤ uOf r
  · simp only [seedPos, seedIdxOf, h, ↓reduceDIte]
  · by_cases hi : i.val < 2 * r - 2
    · have hhi : k - (2 * r - 2) ≤ k - (2 * r - 2) + i.val := by omega
      simp only [seedPos, seedIdxOf, h, hi, hhi, ↓reduceDIte]
      congr 1; apply Fin.ext; dsimp only; omega
    · have hi_lt : i.val < uOf r + extraOf k r := by
        have := i.isLt; simp only [seedLen, h, ↓reduceIte] at this; exact this
      have hnhi : ¬ k - (2 * r - 2) ≤ i.val - (2 * r - 2) := by
        unfold uOf extraOf zOf at *; omega
      have hlo : i.val - (2 * r - 2) < 3 * r - 1 + extraOf k r := by
        unfold uOf at *; omega
      simp only [seedPos, seedIdxOf, h, hi, hnhi, hlo, ↓reduceDIte]
      congr 1; apply Fin.ext; dsimp only; omega

lemma seedPos_of_seedIdxOf {k r : ℕ} (hr : 4 ≤ r) {j : Fin k} {i : Fin (seedLen k r)}
    (h : seedIdxOf k r hr j = some i) : seedPos k r hr i = j := by
  unfold seedIdxOf at h
  by_cases hku : k ≤ uOf r
  · simp only [hku, ↓reduceDIte, Option.some.injEq] at h
    subst h; simp only [seedPos, hku, ↓reduceDIte]
  · simp only [hku, ↓reduceDIte] at h
    by_cases hhi : k - (2 * r - 2) ≤ j.val
    · simp only [hhi, ↓reduceDIte, Option.some.injEq] at h
      subst h
      have hlt : j.val - (k - (2 * r - 2)) < 2 * r - 2 := by omega
      simp only [seedPos, hku, hlt, ↓reduceDIte]
      apply Fin.ext; dsimp only; unfold uOf at hku; omega
    · simp only [hhi, ↓reduceDIte] at h
      by_cases hlo : j.val < 3 * r - 1 + extraOf k r
      · simp only [hlo, ↓reduceDIte, Option.some.injEq] at h
        subst h
        have hge : ¬ (2 * r - 2 + j.val < 2 * r - 2) := by omega
        simp only [seedPos, hku, hge, ↓reduceDIte]
        apply Fin.ext; dsimp only; omega
      · simp only [hlo, ↓reduceDIte] at h; cases h

lemma seedIdxOf_isSome_iff (k r : ℕ) (hr : 4 ≤ r) (j : Fin k) :
    (seedIdxOf k r hr j).isSome = isSeed k r j := by
  unfold seedIdxOf isSeed
  split_ifs with hku hhi hlo <;> simp_all

lemma isSeed_false_of_isFree {k r : ℕ} (hr : 4 ≤ r) (j : Fin k) (hf : isFree k r j = true) :
    isSeed k r j = false := by
  simp only [isFree, decide_eq_true_eq] at hf
  rcases hf with ⟨hku, h1, h2⟩
  unfold isSeed
  rw [if_neg (by omega)]
  simp only [decide_eq_false_iff_not, not_or, not_le, not_lt]
  unfold extraOf zOf uOf at *
  omega

def schedVec {k r m : ℕ} (x : Fin (nIn k r m) → Bool) (idx : ℕ) (j : Fin k) : Bool :=
  if h : 1 ≤ idx ∧ idx ≤ 2 * r then inSched x ⟨idx - 1, by omega⟩ j else false

def sweepStepA {k r m : ℕ} (hk : 0 < k) (hr : 4 ≤ r) (x : Fin (nIn k r m) → Bool)
    (t : ℕ) (w : Fin k → Bool) : Fin k → Bool :=
  if ht : t < hOf k then
    if hku : uOf r < k then
      let sVal := k - 1 - t
      let pivVal := sVal - (2 * r - 2)
      if hpiv : 3 * r - 1 + extraOf k r ≤ pivVal ∧ pivVal < k then
        let bit := xor (stateNoLastFeedV hk r (schedVec x) false w (inLeft x) ⟨sVal, by omega⟩)
                       (inA x ⟨sVal - zOf k, by unfold hOf zOf at *; omega⟩)
        fun j => if j.val = pivVal then bit else w j
      else w
    else w
  else w

def sweepStepB {k r m : ℕ} (hk : 0 < k) (hr : 4 ≤ r) (x : Fin (nIn k r m) → Bool)
    (t : ℕ) (w : Fin k → Bool) : Fin k → Bool :=
  if hku : uOf r < k then
    let sStart := min (k - 1) (zOf k + r + 2)
    if ht : t ≤ sStart - zOf k then
      let sVal := sStart - t
      if hs : 3 * r + 1 ≤ sVal then
        let pivVal := sVal - (3 * r + 1)
        if hpiv : 3 * r - 1 + extraOf k r ≤ pivVal ∧ pivVal + 2 * r - 1 ≤ zOf k then
          let bit := xor (stateNoLastFeedV hk r (schedVec x) true w (inRight x) ⟨sVal, by omega⟩)
                         (inB x ⟨sVal - zOf k, by unfold zOf at *; dsimp only [sVal, sStart] at *; omega⟩)
          fun j => if j.val = pivVal then bit else w j
        else w
      else w
    else w
  else w

def seedInit {k r : ℕ} (hr : 4 ≤ r) (sd : Fin (seedLen k r) → Bool) (j : Fin k) : Bool :=
  match seedIdxOf k r hr j with
  | some idx => sd idx
  | none => false

def sweepAfterA {k r m : ℕ} (hk : 0 < k) (hr : 4 ≤ r) (x : Fin (nIn k r m) → Bool)
    (sd : Fin (seedLen k r) → Bool) (nSteps : ℕ) : Fin k → Bool :=
  (List.range nSteps).foldl (fun w t => sweepStepA hk hr x t w) (seedInit hr sd)

def sweepAfterB {k r m : ℕ} (hk : 0 < k) (hr : 4 ≤ r) (x : Fin (nIn k r m) → Bool)
    (sd : Fin (seedLen k r) → Bool) (nSteps : ℕ) : Fin k → Bool :=
  (List.range nSteps).foldl (fun w t => sweepStepB hk hr x t w) (sweepAfterA hk hr x sd (hOf k))

def sweepW0 {k r m : ℕ} (hk : 0 < k) (hr : 4 ≤ r) (x : Fin (nIn k r m) → Bool)
    (sd : Fin (seedLen k r) → Bool) : Fin k → Bool :=
  sweepAfterB hk hr x sd (r + 3)

def okSeed {k r m : ℕ} (hk : 0 < k) (hr : 4 ≤ r) (x : Fin (nIn k r m) → Bool)
    (sd : Fin (seedLen k r) → Bool) : Bool :=
  let w := sweepW0 hk hr x sd
  (List.finRange (hOf k)).all (fun i =>
    stateV hk r (schedVec x) false w (inLeft x) ⟨zOf k + i.val, by unfold hOf zOf; omega⟩ == inA x i) &&
  (List.finRange (hOf k)).all (fun i =>
    stateV hk r (schedVec x) true w (inRight x) ⟨zOf k + i.val, by unfold hOf zOf; omega⟩ == inB x i)

lemma sweepW0_preserves_seed {k r m : ℕ} (hk : 0 < k) (hr : 4 ≤ r)
    (x : Fin (nIn k r m) → Bool) (sd : Fin (seedLen k r) → Bool) (i : Fin (seedLen k r)) :
    sweepW0 hk hr x sd (seedPos k r hr i) = sd i := by
  have hseed : isSeed k r (seedPos k r hr i) = true := by
    rw [← seedIdxOf_isSome_iff k r hr, seedIdxOf_seedPos]; rfl
  have hpresA : ∀ t (w : Fin k → Bool), sweepStepA hk hr x t w (seedPos k r hr i) = w (seedPos k r hr i) := by
    intro t w; unfold sweepStepA
    by_cases ht : t < hOf k
    · rw [dif_pos ht]
      by_cases hku : uOf r < k
      · rw [dif_pos hku]
        by_cases hpiv : 3 * r - 1 + extraOf k r ≤ (k - 1 - t) - (2 * r - 2) ∧ (k - 1 - t) - (2 * r - 2) < k
        · rw [dif_pos hpiv]
          rw [if_neg]
          intro heq
          simp only [isSeed, if_neg (show ¬ k ≤ uOf r by omega), decide_eq_true_eq] at hseed
          rw [heq] at hseed; unfold uOf at hku; omega
        · rw [dif_neg hpiv]
      · rw [dif_neg hku]
    · rw [dif_neg ht]
  have hpresB : ∀ t (w : Fin k → Bool), sweepStepB hk hr x t w (seedPos k r hr i) = w (seedPos k r hr i) := by
    intro t w; unfold sweepStepB
    by_cases hku : uOf r < k
    · rw [dif_pos hku]
      by_cases ht : t ≤ min (k - 1) (zOf k + r + 2) - zOf k
      · rw [dif_pos ht]
        by_cases hs : 3 * r + 1 ≤ min (k - 1) (zOf k + r + 2) - t
        · rw [dif_pos hs]
          by_cases hpiv : 3 * r - 1 + extraOf k r ≤ (min (k - 1) (zOf k + r + 2) - t) - (3 * r + 1) ∧
              (min (k - 1) (zOf k + r + 2) - t) - (3 * r + 1) + 2 * r - 1 ≤ zOf k
          · rw [dif_pos hpiv]
            rw [if_neg]
            intro heq
            simp only [isSeed, if_neg (show ¬ k ≤ uOf r by omega), decide_eq_true_eq] at hseed
            rw [heq] at hseed; unfold uOf zOf at *; omega
          · rw [dif_neg hpiv]
        · rw [dif_neg hs]
      · rw [dif_neg ht]
    · rw [dif_neg hku]
  have hfoldB : ∀ n w, ((List.range n).foldl (fun w t => sweepStepB hk hr x t w) w) (seedPos k r hr i) =
      w (seedPos k r hr i) := by
    intro n; induction n with
    | zero => intro w; rfl
    | succ n ih => intro w; rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, hpresB, ih]
  have hfoldA : ∀ n w, ((List.range n).foldl (fun w t => sweepStepA hk hr x t w) w) (seedPos k r hr i) =
      w (seedPos k r hr i) := by
    intro n; induction n with
    | zero => intro w; rfl
    | succ n ih => intro w; rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, hpresA, ih]
  unfold sweepW0 sweepAfterB sweepAfterA
  rw [hfoldB, hfoldA]
  simp [seedInit, seedIdxOf_seedPos]

lemma sweepW0_free_zero {k r m : ℕ} (hk : 0 < k) (hr : 4 ≤ r)
    (x : Fin (nIn k r m) → Bool) (sd : Fin (seedLen k r) → Bool) (j : Fin k)
    (hf : isFree k r j = true) :
    sweepW0 hk hr x sd j = false := by
  have hfree_bounds : uOf r < k ∧ 4 * r - 3 ≤ j.val ∧ j.val + 3 * r + 2 ≤ zOf k := by
    simpa [isFree] using hf
  have hpresA : ∀ t (w : Fin k → Bool), sweepStepA hk hr x t w j = w j := by
    intro t w; unfold sweepStepA
    by_cases ht : t < hOf k
    · rw [dif_pos ht]
      by_cases hku : uOf r < k
      · rw [dif_pos hku]
        by_cases hpiv : 3 * r - 1 + extraOf k r ≤ (k - 1 - t) - (2 * r - 2) ∧ (k - 1 - t) - (2 * r - 2) < k
        · rw [dif_pos hpiv]; rw [if_neg]; intro heq; unfold hOf zOf at *; omega
        · rw [dif_neg hpiv]
      · rw [dif_neg hku]
    · rw [dif_neg ht]
  have hpresB : ∀ t (w : Fin k → Bool), sweepStepB hk hr x t w j = w j := by
    intro t w; unfold sweepStepB
    by_cases hku : uOf r < k
    · rw [dif_pos hku]
      by_cases ht : t ≤ min (k - 1) (zOf k + r + 2) - zOf k
      · rw [dif_pos ht]
        by_cases hs : 3 * r + 1 ≤ min (k - 1) (zOf k + r + 2) - t
        · rw [dif_pos hs]
          by_cases hpiv : 3 * r - 1 + extraOf k r ≤ (min (k - 1) (zOf k + r + 2) - t) - (3 * r + 1) ∧
              (min (k - 1) (zOf k + r + 2) - t) - (3 * r + 1) + 2 * r - 1 ≤ zOf k
          · rw [dif_pos hpiv]; rw [if_neg]; intro heq; unfold zOf at *; omega
          · rw [dif_neg hpiv]
        · rw [dif_neg hs]
      · rw [dif_neg ht]
    · rw [dif_neg hku]
  have hfoldB : ∀ n w, ((List.range n).foldl (fun w t => sweepStepB hk hr x t w) w) j = w j := by
    intro n; induction n with
    | zero => intro w; rfl
    | succ n ih => intro w; rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, hpresB, ih]
  have hfoldA : ∀ n w, ((List.range n).foldl (fun w t => sweepStepA hk hr x t w) w) j = w j := by
    intro n; induction n with
    | zero => intro w; rfl
    | succ n ih => intro w; rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, hpresA, ih]
  unfold sweepW0 sweepAfterB sweepAfterA
  rw [hfoldB, hfoldA]
  have hns := isSeed_false_of_isFree hr j hf
  rw [← seedIdxOf_isSome_iff k r hr] at hns
  unfold seedInit
  cases hopt : seedIdxOf k r hr j
  · rfl
  · rw [hopt] at hns; simp at hns

lemma stateV_congr_nonFree {k r m : ℕ} (hk : 0 < k) (hr : 4 ≤ r)
    (x : Fin (nIn k r m) → Bool) (w₁ w₂ : Fin k → Bool)
    (hagree : ∀ j : Fin k, isFree k r j = false → w₁ j = w₂ j) (col : Bool) (i : Fin (hOf k)) :
    stateV hk r (schedVec x) col w₁ (if col then inRight x else inLeft x)
      ⟨zOf k + i.val, by unfold hOf zOf; omega⟩ =
    stateV hk r (schedVec x) col w₂ (if col then inRight x else inLeft x)
      ⟨zOf k + i.val, by unfold hOf zOf; omega⟩ := by
  by_cases hku : k ≤ uOf r
  · have hweq : w₁ = w₂ := funext fun j => hagree j (by simp [isFree]; omega)
    rw [hweq]
  · push_neg at hku
    have hk2 : 2 < k := by unfold uOf at hku; omega
    let s : Fin k := ⟨zOf k + i.val, by unfold hOf zOf; omega⟩
    rw [stateV_eq_xor_lastFeed hk (by omega), stateV_eq_xor_lastFeed hk (by omega)]
    have hnotFree : ∀ d : ℤ,
        (if col then -(3 * r + 1 : ℤ) else -(2 * r - 2 : ℤ)) ≤ d →
        d ≤ (if col then (4 * r - 3 : ℤ) else (3 * r - 1 : ℤ)) →
        isFree k r (ixMod hk ((s.val : ℤ) + d)) = false := by
      intro d hd_lo hd_hi
      simp only [isFree, decide_eq_false_iff_not, not_and, not_le]
      intro _ hge
      have hval : ((ixMod hk ((s.val : ℤ) + d)).val : ℤ) =
          (((zOf k + i.val : ℕ) : ℤ) + d) % (k : ℤ) := ixMod_val_coe hk ((s.val : ℤ) + d)
      have hsum_lo : ((zOf k + i.val : ℕ) : ℤ) + d ≥ -(k : ℤ) := by
        unfold zOf hOf uOf at *; cases col <;> simp at hd_lo <;> omega
      have hsum_hi : ((zOf k + i.val : ℕ) : ℤ) + d < 2 * (k : ℤ) := by
        unfold zOf hOf uOf at *; cases col <;> simp at hd_hi <;> omega
      by_cases hneg : ((zOf k + i.val : ℕ) : ℤ) + d < 0
      · have hmod : (((zOf k + i.val : ℕ) : ℤ) + d) % (k : ℤ) = ((zOf k + i.val : ℕ) : ℤ) + d + (k : ℤ) := by
          rw [← Int.add_emod_right, Int.emod_eq_of_lt (by omega) (by omega)]
        rw [hmod] at hval
        unfold zOf hOf uOf at *; cases col <;> simp at hd_lo hd_hi <;> omega
      · by_cases hlt : ((zOf k + i.val : ℕ) : ℤ) + d < (k : ℤ)
        · have hmod : (((zOf k + i.val : ℕ) : ℤ) + d) % (k : ℤ) = ((zOf k + i.val : ℕ) : ℤ) + d :=
            Int.emod_eq_of_lt (by omega) hlt
          rw [hmod] at hval
          unfold zOf hOf uOf at *; cases col <;> simp at hd_lo hd_hi <;> omega
        · have hmod : (((zOf k + i.val : ℕ) : ℤ) + d) % (k : ℤ) = ((zOf k + i.val : ℕ) : ℤ) + d - (k : ℤ) := by
            rw [← Int.sub_emod_right, Int.emod_eq_of_lt (by omega) (by omega)]
          rw [hmod] at hval
          unfold zOf hOf uOf at *; cases col <;> simp at hd_lo hd_hi <;> omega
    have hnlf : stateNoLastFeedV hk r (schedVec x) col w₁ (if col then inRight x else inLeft x) s =
        stateNoLastFeedV hk r (schedVec x) col w₂ (if col then inRight x else inLeft x) s := by
      apply stateNoLastFeedV_congr hk hk2 hr
      intro d hd_lo hd_hi
      exact hagree _ (hnotFree d (by cases col <;> simp at hd_lo ⊢ <;> omega) hd_hi)
    have hfeed : rotV hk (if col then 3 * r + 1 else 2 * (r - 1)) w₁ s =
        rotV hk (if col then 3 * r + 1 else 2 * (r - 1)) w₂ s := by
      dsimp only [rotV]; rw [rotV_idx_eq_ixMod hk]
      let fd : ℤ := -((if col then 3 * r + 1 else 2 * (r - 1) : ℕ) : ℤ)
      have heq : (s.val : ℤ) - ((if col then 3 * r + 1 else 2 * (r - 1) : ℕ) : ℤ) = (s.val : ℤ) + fd := by
        dsimp only [fd]; omega
      rw [heq]
      exact hagree _ (hnotFree fd (by cases col <;> simp [fd] <;> omega)
        (by cases col <;> simp [fd] <;> omega))
    rw [hnlf, hfeed]

lemma sweep_reconstructs_of_valid {k r m : ℕ} (hk : 0 < k) (hr : 4 ≤ r)
    (x : Fin (nIn k r m) → Bool) (w : Fin k → Bool)
    (hA : ∀ i : Fin (hOf k), stateV hk r (schedVec x) false w (inLeft x)
      ⟨zOf k + i.val, by unfold hOf zOf; omega⟩ = inA x i)
    (hB : ∀ i : Fin (hOf k), stateV hk r (schedVec x) true w (inRight x)
      ⟨zOf k + i.val, by unfold hOf zOf; omega⟩ = inB x i) :
    let sd : Fin (seedLen k r) → Bool := fun i => w (seedPos k r hr i)
    (∀ j : Fin k, isFree k r j = false → sweepW0 hk hr x sd j = w j) ∧
    okSeed hk hr x sd = true := by
  intro sd
  have hmain : ∀ j : Fin k, isFree k r j = false → sweepW0 hk hr x sd j = w j := by
    by_cases hku : k ≤ uOf r
    · intro j _
      let idx : Fin (seedLen k r) := ⟨j.val, by simp [seedLen, hku]⟩
      have hidx : seedPos k r hr idx = j := by
        apply Fin.ext; simp [seedPos, hku, idx]
      have h1 := sweepW0_preserves_seed hk hr x sd idx
      dsimp only [sd] at h1
      rwa [hidx] at h1
    · push_neg at hku
      have hk2 : 2 < k := by unfold uOf at hku; omega
      -- Step A invariant: after t steps (t ≤ hOf k), sweepAfterA agrees with w on all j with
      -- j.val < 3*r - 1 + extraOf k r ∨ k - (2*r - 2) - t ≤ j.val!
      have hInvA : ∀ t ≤ hOf k, ∀ j : Fin k,
          (j.val < 3 * r - 1 + extraOf k r ∨ k - (2 * r - 2) - t ≤ j.val) →
          sweepAfterA hk hr x sd t j = w j := by
        intro t ht
        induction t with
        | zero =>
          intro j hj
          have hsd : isSeed k r j = true := by
            unfold isSeed; rw [if_neg (by omega)]; simp only [decide_eq_true_eq]; omega
          rw [← seedIdxOf_isSome_iff k r hr] at hsd
          rcases Option.isSome_iff_exists.mp hsd with ⟨idx, hidx⟩
          unfold sweepAfterA
          simp only [List.range_zero, List.foldl_nil, seedInit, hidx, sd]
          rw [seedPos_of_seedIdxOf hr hidx]
        | succ t ih =>
          intro j hj
          have ht_lt : t < hOf k := by omega
          unfold sweepAfterA
          rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
          change sweepStepA hk hr x t (sweepAfterA hk hr x sd t) j = w j
          unfold sweepStepA
          rw [dif_pos ht_lt, dif_pos hku]
          let sVal := k - 1 - t
          let pivVal := sVal - (2 * r - 2)
          have hpiv_eq : pivVal = k - (2 * r - 2) - (t + 1) := by
            dsimp only [pivVal, sVal]; unfold hOf uOf at *; omega
          by_cases hpiv : 3 * r - 1 + extraOf k r ≤ pivVal ∧ pivVal < k
          · rw [dif_pos hpiv]
            by_cases hjeq : j.val = pivVal
            · rw [if_pos hjeq]
              -- Prove stateNoLastFeedV on sweepAfterA t equals stateNoLastFeedV on w at sVal!
              let sFin : Fin k := ⟨sVal, by omega⟩
              have hnlf : stateNoLastFeedV hk r (schedVec x) false (sweepAfterA hk hr x sd t) (inLeft x) sFin =
                  stateNoLastFeedV hk r (schedVec x) false w (inLeft x) sFin := by
                apply stateNoLastFeedV_congr hk hk2 hr
                intro d hd_lo hd_hi
                simp only [Bool.false_eq_true, ↓reduceIte] at hd_lo hd_hi
                apply ih (by omega)
                have hval : ((ixMod hk ((sFin.val : ℤ) + d)).val : ℤ) =
                    ((sVal : ℤ) + d) % (k : ℤ) := ixMod_val_coe hk ((sFin.val : ℤ) + d)
                have hlo : (0 : ℤ) ≤ (sVal : ℤ) + d := by
                  dsimp only [sVal]; unfold hOf uOf at *; omega
                have hhi : (sVal : ℤ) + d < 2 * (k : ℤ) := by
                  dsimp only [sVal]; unfold hOf uOf at *; omega
                by_cases hlt : (sVal : ℤ) + d < (k : ℤ)
                · have hmod : ((sVal : ℤ) + d) % (k : ℤ) = (sVal : ℤ) + d :=
                    Int.emod_eq_of_lt hlo hlt
                  rw [hmod] at hval; right; dsimp only [sVal] at hval; omega
                · have hmod : ((sVal : ℤ) + d) % (k : ℤ) = (sVal : ℤ) + d - (k : ℤ) := by
                    rw [← Int.sub_emod_right, Int.emod_eq_of_lt (by omega) (by omega)]
                  rw [hmod] at hval; left; dsimp only [sVal] at hval; omega
              rw [hnlf]
              have hs_eq : sFin = ⟨zOf k + (sVal - zOf k), by unfold zOf hOf at *; omega⟩ := by
                apply Fin.ext; dsimp only [sFin, sVal]; unfold zOf hOf at *; omega
              have hst := hA ⟨sVal - zOf k, by unfold zOf hOf at *; omega⟩
              rw [← hs_eq, stateV_eq_xor_lastFeed hk (by omega)] at hst
              have hrot : rotV hk (2 * (r - 1)) w sFin = w j := by
                dsimp only [rotV]; congr 1
                rw [rotV_idx_eq_ixMod hk]
                have hsub : (sFin.val : ℤ) - ((2 * (r - 1) : ℕ) : ℤ) = (j.val : ℤ) := by
                  dsimp only [sFin, sVal, pivVal] at hjeq ⊢; unfold hOf uOf at *; omega
                rw [hsub, ixMod_of_fin]
              simp only [Bool.false_eq_true, ↓reduceIte] at hst
              rw [hrot] at hst
              dsimp only [sVal] at hst
              have heqA : inA x ⟨k - 1 - t - zOf k, by unfold hOf zOf at *; omega⟩ =
                  (stateNoLastFeedV hk r (schedVec x) false w (inLeft x) sFin ^^ w j) := hst.symm
              rw [heqA]
              cases stateNoLastFeedV hk r (schedVec x) false w (inLeft x) sFin <;> cases w j <;> decide
            · rw [if_neg hjeq]
              exact ih (by omega) j (by omega)
          · rw [dif_neg hpiv]
            apply ih (by omega) j
            have : j.val < 3 * r - 1 + extraOf k r ∨ k - (2 * r - 2) - t ≤ j.val := by
              unfold hOf uOf at *; omega
            exact this
      have hAfterA : ∀ j : Fin k,
          (j.val < 3 * r - 1 + extraOf k r ∨ zOf k - (2 * r - 2) ≤ j.val) →
          sweepAfterA hk hr x sd (hOf k) j = w j := by
        intro j hj
        apply hInvA (hOf k) le_rfl j
        have hkz : k - (2 * r - 2) - hOf k = zOf k - (2 * r - 2) := by unfold hOf zOf; omega
        rwa [hkz]
      -- Step B invariant: after t steps (t ≤ r + 3), sweepAfterB agrees with w on all j with
      -- j.val < 3*r - 1 + extraOf k r ∨ zOf k - (2*r - 2) - t ≤ j.val (Wait: specifically if sStart = min (k-1) (z+r+2))
      have hInvB : ∀ t ≤ r + 3, ∀ j : Fin k,
          (j.val < 3 * r - 1 + extraOf k r ∨
            (min (k - 1) (zOf k + r + 2) + 1 - min t (min (k - 1) (zOf k + r + 2) - zOf k + 1)) - (3 * r + 1) ≤ j.val ∨
            zOf k - (2 * r - 2) ≤ j.val) →
          sweepAfterB hk hr x sd t j = w j := by
        intro t ht
        induction t with
        | zero =>
          intro j hj
          unfold sweepAfterB; simp only [List.range_zero, List.foldl_nil]
          apply hAfterA j
          rcases hj with h1 | h2 | h3
          · exact Or.inl h1
          · right; unfold zOf at *; omega
          · exact Or.inr h3
        | succ t ih =>
          intro j hj
          unfold sweepAfterB
          rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
          change sweepStepB hk hr x t (sweepAfterB hk hr x sd t) j = w j
          unfold sweepStepB
          rw [dif_pos hku]
          let sStart := min (k - 1) (zOf k + r + 2)
          by_cases htle : t ≤ sStart - zOf k
          · rw [dif_pos htle]
            let sVal := sStart - t
            by_cases hs : 3 * r + 1 ≤ sVal
            · rw [dif_pos hs]
              let pivVal := sVal - (3 * r + 1)
              by_cases hpiv : 3 * r - 1 + extraOf k r ≤ pivVal ∧ pivVal + 2 * r - 1 ≤ zOf k
              · rw [dif_pos hpiv]
                by_cases hjeq : j.val = pivVal
                · rw [if_pos hjeq]
                  -- Notice hpiv implies 3*r - 1 ≤ zOf k - (2*r - 1), so zOf k ≥ 5*r - 2 and k ≥ 10*r - 4!
                  have hz5 : 5 * r - 2 ≤ zOf k := by omega
                  have hk10 : 10 * r - 4 ≤ k := by unfold zOf hOf at *; omega
                  let sFin : Fin k := ⟨sVal, by omega⟩
                  have hnlf : stateNoLastFeedV hk r (schedVec x) true (sweepAfterB hk hr x sd t) (inRight x) sFin =
                      stateNoLastFeedV hk r (schedVec x) true w (inRight x) sFin := by
                    apply stateNoLastFeedV_congr hk hk2 hr
                    intro d hd_lo hd_hi
                    simp only [↓reduceIte] at hd_lo hd_hi
                    apply ih (by omega)
                    have hval : ((ixMod hk ((sFin.val : ℤ) + d)).val : ℤ) =
                        ((sVal : ℤ) + d) % (k : ℤ) := ixMod_val_coe hk ((sFin.val : ℤ) + d)
                    have hlo : (0 : ℤ) ≤ (sVal : ℤ) + d := by
                      dsimp only [sVal] at *; omega
                    have hhi : (sVal : ℤ) + d < 2 * (k : ℤ) := by
                      dsimp only [sVal] at *; omega
                    by_cases hlt : (sVal : ℤ) + d < (k : ℤ)
                    · have hmod : ((sVal : ℤ) + d) % (k : ℤ) = (sVal : ℤ) + d :=
                        Int.emod_eq_of_lt hlo hlt
                      rw [hmod] at hval; right; left
                      dsimp only [sVal, sStart] at hval htle ⊢; omega
                    · have hmod : ((sVal : ℤ) + d) % (k : ℤ) = (sVal : ℤ) + d - (k : ℤ) := by
                        rw [← Int.sub_emod_right, Int.emod_eq_of_lt (by omega) (by omega)]
                      rw [hmod] at hval; left
                      dsimp only [sVal, sStart] at hval ⊢; unfold zOf hOf extraOf at *; omega
                  rw [hnlf]
                  have hs_eq : sFin = ⟨zOf k + (sVal - zOf k), by unfold zOf hOf at *; omega⟩ := by
                    apply Fin.ext; dsimp only [sFin, sVal, sStart]; unfold zOf hOf at *; omega
                  have hst := hB ⟨sVal - zOf k, by unfold zOf hOf at *; dsimp only [sVal, sStart]; omega⟩
                  rw [← hs_eq, stateV_eq_xor_lastFeed hk (by omega)] at hst
                  have hrot : rotV hk (3 * r + 1) w sFin = w j := by
                    dsimp only [rotV]; congr 1
                    rw [rotV_idx_eq_ixMod hk]
                    have hsub : (sFin.val : ℤ) - ((3 * r + 1 : ℕ) : ℤ) = (j.val : ℤ) := by
                      dsimp only [sFin, sVal, pivVal] at hjeq ⊢; omega
                    rw [hsub, ixMod_of_fin]
                  simp only [↓reduceIte] at hst
                  rw [hrot] at hst
                  dsimp only [sVal, sStart] at hst
                  have heqB : inB x ⟨min (k - 1) (zOf k + r + 2) - t - zOf k, by unfold zOf at *; omega⟩ =
                      (stateNoLastFeedV hk r (schedVec x) true w (inRight x) sFin ^^ w j) := hst.symm
                  rw [heqB]
                  cases stateNoLastFeedV hk r (schedVec x) true w (inRight x) sFin <;> cases w j <;> decide
                · rw [if_neg hjeq]
                  apply ih (by omega) j
                  dsimp only [sStart, sVal, pivVal] at htle hs hpiv hjeq ⊢; omega
              · rw [dif_neg hpiv]
                apply ih (by omega) j
                dsimp only [sStart, sVal, pivVal] at htle hs hpiv ⊢; omega
            · rw [dif_neg hs]
              apply ih (by omega) j
              dsimp only [sStart, sVal] at htle hs ⊢; omega
          · rw [dif_neg htle]
            apply ih (by omega) j
            dsimp only [sStart] at htle ⊢
            rcases hj with h1 | h2 | h3
            · exact Or.inl h1
            · right; left; omega
            · exact Or.inr (Or.inr h3)
      intro j hnf
      simp only [isFree, decide_eq_false_iff_not, not_and, not_le] at hnf
      apply hInvB (r + 3) le_rfl j
      by_cases hlt : j.val < 3 * r - 1 + extraOf k r
      · exact Or.inl hlt
      · by_cases hbig : zOf k - (2 * r - 2) ≤ j.val
        · exact Or.inr (Or.inr hbig)
        · right; left
          have hz5 : 5 * r - 2 ≤ zOf k := by omega
          have hh5 : 5 * r - 2 ≤ hOf k := by unfold hOf zOf at *; omega
          have hmin : min (k - 1) (zOf k + r + 2) = zOf k + r + 2 := by
            unfold hOf zOf at *; omega
          rw [hmin]
          have hnotf := hnf hku
          unfold extraOf at hlt
          omega
  refine ⟨hmain, ?_⟩
  unfold okSeed
  rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true]
  constructor
  · intro i _
    simp only [beq_iff_eq]
    have h := stateV_congr_nonFree hk hr x (sweepW0 hk hr x sd) w hmain false i
    exact h.trans (hA i)
  · intro i _
    simp only [beq_iff_eq]
    have h := stateV_congr_nonFree hk hr x (sweepW0 hk hr x sd) w hmain true i
    exact h.trans (hB i)

/-! #### Part 5: `PTab m` Column-Space Counting & Binary Search Specification -/

def freeBelow (k r : ℕ) (b : ℕ) (j : Fin k) : Bool :=
  isFree k r j && decide (j.val < b)

def colVec {k r m : ℕ} (x : Fin (nIn k r m) → Bool) (b : ℕ) (j : Fin k) (i : Fin m) : Bool :=
  if freeBelow k r b j then inMat x i j else false

def colTabSteps {k r m : ℕ} (x : Fin (nIn k r m) → Bool) (b : ℕ) : ℕ → PTab m
  | 0 => PTab.empty m
  | t + 1 =>
    if ht : t < k then (colTabSteps x b t).insert (colVec x b ⟨t, ht⟩)
    else colTabSteps x b t

def colTab {k r m : ℕ} (x : Fin (nIn k r m) → Bool) (b : ℕ) : PTab m :=
  colTabSteps x b k

def freeBelowCard (k r b : ℕ) : ℕ :=
  (Finset.univ.filter (fun j : Fin k => freeBelow k r b j = true)).card

def nullityOf {k r m : ℕ} (x : Fin (nIn k r m) → Bool) (b : ℕ) : ℕ :=
  freeBelowCard k r b - popCount (colTab x b).hasPiv

def linMapFree {k r m : ℕ} (x : Fin (nIn k r m) → Bool) (b : ℕ) :
    ({j : Fin k // freeBelow k r b j = true} → F2) →ₗ[F2] (Fin m → F2) where
  toFun v i := ∑ j : {j : Fin k // freeBelow k r b j = true}, b2f (inMat x i j.val) * v j
  map_add' u v := by
    funext i; simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' a v := by
    funext i; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => by ring

lemma colTabSteps_spec {k r m : ℕ} (x : Fin (nIn k r m) → Bool) (b : ℕ) :
    ∀ t ≤ k,
      (colTabSteps x b t).IsEchelon ∧
      (colTabSteps x b t).toSub =
        Submodule.span F2 {u : Fin m → F2 | ∃ j : Fin k, j.val < t ∧ freeBelow k r b j = true ∧
          u = fun i => b2f (inMat x i j)} := by
  intro t ht
  induction t with
  | zero =>
    refine ⟨PTab.empty_isEchelon m, ?_⟩
    rw [colTabSteps, PTab.empty_toSub]
    simp
  | succ t ih =>
    have ht_lt : t < k := by omega
    obtain ⟨hE, hSub⟩ := ih (by omega)
    simp only [colTabSteps, ht_lt, ↓reduceDIte]
    refine ⟨(colTabSteps x b t).insert_isEchelon hE _, ?_⟩
    rw [(colTabSteps x b t).insert_toSub hE, hSub]
    by_cases hfb : freeBelow k r b ⟨t, ht_lt⟩ = true
    · have hvec : (fun i => b2f (colVec x b ⟨t, ht_lt⟩ i)) = fun i => b2f (inMat x i ⟨t, ht_lt⟩) := by
        funext i; simp [colVec, hfb]
      rw [hvec, ← Submodule.span_union]
      congr 1; ext u; simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_singleton_iff]
      constructor
      · rintro (⟨j, hj, hfj, rfl⟩ | rfl)
        · exact ⟨j, by omega, hfj, rfl⟩
        · exact ⟨⟨t, ht_lt⟩, by dsimp only; omega, hfb, rfl⟩
      · rintro ⟨j, hj, hfj, rfl⟩
        by_cases hjt : j.val < t
        · exact Or.inl ⟨j, hjt, hfj, rfl⟩
        · right; have heq : j = ⟨t, ht_lt⟩ := Fin.ext (by dsimp only; omega); subst heq; rfl
    · have hfb' : freeBelow k r b ⟨t, ht_lt⟩ = false := by
        cases h : freeBelow k r b ⟨t, ht_lt⟩ <;> simp_all
      have hvec : (fun i => b2f (colVec x b ⟨t, ht_lt⟩ i)) = 0 := by
        funext i; simp [colVec, hfb']
      rw [hvec, Submodule.span_zero_singleton, sup_bot_eq]
      congr 1; ext u; simp only [Set.mem_setOf_eq]
      constructor
      · rintro ⟨j, hj, hfj, rfl⟩; exact ⟨j, by omega, hfj, rfl⟩
      · rintro ⟨j, hj, hfj, rfl⟩
        refine ⟨j, ?_, hfj, rfl⟩
        by_contra hge
        have heq : j = ⟨t, ht_lt⟩ := Fin.ext (by dsimp only; omega)
        rw [heq, hfb'] at hfj; exact absurd hfj (by decide)

lemma colTab_spec {k r m : ℕ} (x : Fin (nIn k r m) → Bool) (b : ℕ) :
    (colTab x b).IsEchelon ∧
    (colTab x b).toSub = LinearMap.range (linMapFree x b) ∧
    popCount (colTab x b).hasPiv ≤ freeBelowCard k r b ∧
    Module.finrank F2 (LinearMap.ker (linMapFree x b)) = nullityOf x b := by
  obtain ⟨hE, hSub⟩ := colTabSteps_spec x b k le_rfl
  have hrange : (colTab x b).toSub = LinearMap.range (linMapFree x b) := by
    rw [colTab, hSub]
    apply le_antisymm
    · refine Submodule.span_le.mpr ?_
      rintro u ⟨j, _, hfj, rfl⟩
      refine ⟨fun j' => if j'.val = j then 1 else 0, ?_⟩
      funext i; simp only [linMapFree, LinearMap.coe_mk, AddHom.coe_mk]
      rw [Finset.sum_eq_single ⟨j, hfj⟩]
      · simp
      · intro j' _ hne; have : j'.val ≠ j := fun h => hne (Subtype.ext h); simp [this]
      · intro h; exact absurd (Finset.mem_univ _) h
    · rintro u ⟨v, rfl⟩
      have hlin : linMapFree x b v = ∑ j : {j : Fin k // freeBelow k r b j = true},
          v j • (fun i => b2f (inMat x i j.val)) := by
        funext i; simp only [linMapFree, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply,
          Pi.smul_apply, smul_eq_mul]
        refine Finset.sum_congr rfl fun j _ => mul_comm _ _
      rw [hlin]
      exact Submodule.sum_mem _ fun j _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨j.val, j.val.isLt, j.property, rfl⟩)
  have hrank : Module.finrank F2 (LinearMap.range (linMapFree x b)) = popCount (colTab x b).hasPiv := by
    rw [← hrange]; exact (colTab x b).finrank_toSub hE
  have hrn := LinearMap.finrank_range_add_finrank_ker (linMapFree x b)
  have hdom : Module.finrank F2 ({j : Fin k // freeBelow k r b j = true} → F2) = freeBelowCard k r b := by
    simp [Module.finrank_pi_fintype, Module.finrank_self, Fintype.card_subtype, freeBelowCard]
  rw [hdom, hrank] at hrn
  exact ⟨hE, hrange, by omega, by unfold nullityOf; omega⟩

def linOk {k r m : ℕ} (x : Fin (nIn k r m) → Bool) (b : ℕ) (y : Fin m → Bool) : Bool :=
  (List.finRange m).all (fun i => !((colTab x b).reduce y i))

lemma card_free_solutions {k r m : ℕ} (x : Fin (nIn k r m) → Bool) (b : ℕ) (y : Fin m → Bool) :
    (Finset.univ.filter (fun v : Fin k → Bool =>
      (∀ j : Fin k, freeBelow k r b j = false → v j = false) ∧
      ∀ i : Fin m, (List.finRange k).foldl (fun acc j => xor acc (v j && inMat x i j)) false = y i)).card =
    if linOk x b y = true then 2 ^ nullityOf x b else 0 := by
  obtain ⟨hE, hrange, _, hker⟩ := colTab_spec x b
  let S := Finset.univ.filter (fun v : Fin k → Bool =>
    (∀ j : Fin k, freeBelow k r b j = false → v j = false) ∧
    ∀ i : Fin m, (List.finRange k).foldl (fun acc j => xor acc (v j && inMat x i j)) false = y i)
  let yf : Fin m → F2 := fun i => b2f (y i)
  let T := Finset.univ.filter (fun u : {j : Fin k // freeBelow k r b j = true} → F2 =>
    linMapFree x b u = yf)
  have hST : S.card = T.card := by
    refine Finset.card_bij
      (fun v _ j => b2f (v j.val))
      (fun v hv => ?_) (fun v₁ hv₁ v₂ hv₂ heq => ?_) (fun u hu => ?_)
    · rcases (Finset.mem_filter.mp hv).2 with ⟨hsupp, hmat⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      funext i
      have hi := congrArg b2f (hmat i)
      rw [b2f_finRange_xor] at hi
      dsimp only [linMapFree, LinearMap.coe_mk, AddHom.coe_mk, yf]
      rw [← hi]
      have hfilt : (∑ j : Fin k, b2f (v j && inMat x i j)) =
          ∑ j ∈ Finset.univ.filter (fun j : Fin k => freeBelow k r b j = true), b2f (v j && inMat x i j) := by
        rw [← Finset.sum_subset (Finset.filter_subset (fun j : Fin k => freeBelow k r b j = true) Finset.univ)]
        intro j _ hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
        have hfb : freeBelow k r b j = false := by cases h : freeBelow k r b j <;> simp_all
        rw [hsupp j hfb]; simp
      rw [hfilt]
      refine Finset.sum_bij (fun j _ => j.val)
        (fun j _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, j.property⟩)
        (fun j₁ _ j₂ _ heq => Subtype.ext heq)
        (fun j hj => ⟨⟨j, (Finset.mem_filter.mp hj).2⟩, Finset.mem_univ _, rfl⟩)
        (fun j _ => by rw [b2f_and, mul_comm])
    · rcases (Finset.mem_filter.mp hv₁).2 with ⟨hs₁, _⟩
      rcases (Finset.mem_filter.mp hv₂).2 with ⟨hs₂, _⟩
      funext j
      by_cases hfb : freeBelow k r b j = true
      · exact b2f_inj (congrFun heq ⟨j, hfb⟩)
      · have hfb' : freeBelow k r b j = false := by cases h : freeBelow k r b j <;> simp_all
        rw [hs₁ j hfb', hs₂ j hfb']
    · have hu_eq : linMapFree x b u = yf := (Finset.mem_filter.mp hu).2
      let v : Fin k → Bool := fun j => if h : freeBelow k r b j = true then f2b (u ⟨j, h⟩) else false
      refine ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩, ?_⟩
      · intro j hfb; simp [v, hfb]
      · intro i
        apply b2f_inj
        rw [b2f_finRange_xor]
        have hhi := congrFun hu_eq i
        dsimp only [linMapFree, LinearMap.coe_mk, AddHom.coe_mk, yf] at hhi
        rw [← hhi]
        have hfilt : (∑ j : Fin k, b2f (v j && inMat x i j)) =
            ∑ j ∈ Finset.univ.filter (fun j : Fin k => freeBelow k r b j = true), b2f (v j && inMat x i j) := by
          rw [← Finset.sum_subset (Finset.filter_subset (fun j : Fin k => freeBelow k r b j = true) Finset.univ)]
          intro j _ hj
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
          have hfb : freeBelow k r b j = false := by cases h : freeBelow k r b j <;> simp_all
          simp [v, hfb]
        rw [hfilt]
        refine Finset.sum_bij (fun j hj => ⟨j, (Finset.mem_filter.mp hj).2⟩)
          (fun _ _ => Finset.mem_univ _)
          (fun j₁ _ j₂ _ heq => congrArg Subtype.val heq)
          (fun j _ => ⟨j.val, Finset.mem_filter.mpr ⟨Finset.mem_univ _, j.property⟩, rfl⟩)
          (fun j hj => by
            have hjb : freeBelow k r b j = true := (Finset.mem_filter.mp hj).2
            simp only [v, hjb, ↓reduceDIte, b2f_and, b2f_f2b, mul_comm])
      · funext j; simp [v, j.property]
  change S.card = _
  rw [hST]
  have hlinOk_iff : linOk x b y = true ↔ yf ∈ LinearMap.range (linMapFree x b) := by
    rw [← hrange, ← (colTab x b).reduce_eq_zero_iff hE y]
    simp only [linOk, List.all_eq_true, List.mem_finRange, true_implies, Bool.not_eq_true']
  by_cases hok : linOk x b y = true
  · rw [if_pos hok]
    obtain ⟨u₀, hu₀⟩ := hlinOk_iff.mp hok
    have hbij : T.card = Nat.card (LinearMap.ker (linMapFree x b)) := by
      haveI : Fintype (LinearMap.ker (linMapFree x b)) := Fintype.ofFinite _
      rw [Nat.card_eq_fintype_card]
      refine Finset.card_bij (fun u hu => ⟨u + u₀, ?_⟩) ?_ ?_ ?_
      · have hu' : linMapFree x b u = yf := (Finset.mem_filter.mp hu).2
        rw [LinearMap.mem_ker, map_add, hu', hu₀]
        funext i; exact f2_add_self _
      · intro u hu; exact Finset.mem_univ _
      · intro u₁ _ u₂ _ heq
        have h1 : u₁ + u₀ = u₂ + u₀ := congrArg Subtype.val heq
        funext j
        have h2 := congrFun h1 j
        simp only [Pi.add_apply] at h2
        exact add_right_cancel h2
      · intro w _
        refine ⟨w.val + u₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
        · rw [map_add, LinearMap.mem_ker.mp w.property, zero_add, hu₀]
        · apply Subtype.ext; funext j; simp only [Pi.add_apply]
          rw [add_assoc, f2_add_self, add_zero]
    rw [hbij, card_sub_eq_pow_finrank, hker]
  · rw [if_neg hok]
    have hnotmem : yf ∉ LinearMap.range (linMapFree x b) := fun h => hok (hlinOk_iff.mpr h)
    have hempty : T = ∅ := by
      ext u; simp only [T, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      intro h; exact hnotmem ⟨u, h⟩
    rw [hempty, Finset.card_empty]

/-! #### Exact Top-Bit Counting & Binary Search Selection -/

def seedRhs {k r m : ℕ} (hk : 0 < k) (hr : 4 ≤ r) (x : Fin (nIn k r m) → Bool)
    (sd : Fin (seedLen k r) → Bool) (i : Fin m) : Bool :=
  xor (inRhs x i) ((List.finRange k).foldl (fun acc j => xor acc (sweepW0 hk hr x sd j && inMat x i j)) false)

def topFreeRhs {k r m : ℕ} (x : Fin (nIn k r m) → Bool) (b : ℕ) (key : Fin k → Bool) (i : Fin m) : Bool :=
  (List.finRange k).foldl (fun acc j =>
    xor acc (if isFree k r j && decide (b ≤ j.val) && key j then inMat x i j else false)) false

def isSolVec {k r m : ℕ} (hk : 0 < k) (x : Fin (nIn k r m) → Bool) (w : Fin k → Bool) : Bool :=
  (List.finRange (hOf k)).all (fun i =>
    stateV hk r (schedVec x) false w (inLeft x) ⟨zOf k + i.val, by unfold hOf zOf; omega⟩ == inA x i) &&
  (List.finRange (hOf k)).all (fun i =>
    stateV hk r (schedVec x) true w (inRight x) ⟨zOf k + i.val, by unfold hOf zOf; omega⟩ == inB x i) &&
  (List.finRange m).all (fun i =>
    (List.finRange k).foldl (fun acc j => xor acc (w j && inMat x i j)) false == inRhs x i)

def topSolSet {k r m : ℕ} (hk : 0 < k) (x : Fin (nIn k r m) → Bool)
    (b : ℕ) (key : Fin k → Bool) : Finset (Fin k → Bool) :=
  Finset.univ.filter (fun w => isSolVec hk x w = true ∧ ∀ j : Fin k, b ≤ j.val → w j = key j)

def seedMatchTop {k r m : ℕ} (hk : 0 < k) (hr : 4 ≤ r) (x : Fin (nIn k r m) → Bool)
    (b : ℕ) (key : Fin k → Bool) (sd : Fin (seedLen k r) → Bool) : Bool :=
  okSeed hk hr x sd &&
  (List.finRange k).all (fun j => !decide (b ≤ j.val) || isFree k r j || (sweepW0 hk hr x sd j == key j))

lemma card_topSolSet {k r m : ℕ} (hk : 0 < k) (hr : 4 ≤ r) (x : Fin (nIn k r m) → Bool)
    (b : ℕ) (hb : b ≤ k) (key : Fin k → Bool) :
    (topSolSet hk x b key).card =
      (Finset.univ.filter (fun sd : Fin (seedLen k r) → Bool =>
        seedMatchTop hk hr x b key sd &&
        linOk x b (fun i => xor (seedRhs hk hr x sd i) (topFreeRhs x b key i)))).card *
      2 ^ nullityOf x b := by
  -- Fiber decomposition by sd := fun i => w (seedPos i)
  let SdSet := Finset.univ.filter (fun sd : Fin (seedLen k r) → Bool =>
    seedMatchTop hk hr x b key sd &&
    linOk x b (fun i => xor (seedRhs hk hr x sd i) (topFreeRhs x b key i)))
  let fiber (sd : Fin (seedLen k r) → Bool) : Finset (Fin k → Bool) :=
    (topSolSet hk x b key).filter (fun w => (fun i => w (seedPos k r hr i)) = sd)
  have hpart : (topSolSet hk x b key).card = ∑ sd : Fin (seedLen k r) → Bool, (fiber sd).card := by
    rw [← Finset.card_biUnion]
    · congr 1; ext w; simp [fiber]
    · intro sd₁ _ sd₂ _ hne
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]; intro w h1 h2
      exact hne ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)
  rw [hpart]
  have hfiber_card : ∀ sd : Fin (seedLen k r) → Bool,
      (fiber sd).card =
        if seedMatchTop hk hr x b key sd &&
           linOk x b (fun i => xor (seedRhs hk hr x sd i) (topFreeRhs x b key i)) then
          2 ^ nullityOf x b
        else 0 := by
    intro sd
    by_cases hmt : seedMatchTop hk hr x b key sd = true
    · simp only [hmt, Bool.true_and]
      have hmt' : okSeed hk hr x sd = true ∧
          ∀ j : Fin k, b ≤ j.val → isFree k r j = false → sweepW0 hk hr x sd j = key j := by
        simp only [seedMatchTop, Bool.and_eq_true, List.all_eq_true, List.mem_finRange, true_implies,
          Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, beq_iff_eq] at hmt
        refine ⟨hmt.1, fun j hjb hnf => ?_⟩
        rcases hmt.2 j with (h | h) | h
        · exact absurd hjb h
        · rw [hnf] at h; exact absurd h (by decide)
        · exact h
      rw [← card_free_solutions x b (fun i => xor (seedRhs hk hr x sd i) (topFreeRhs x b key i))]
      -- Biject fiber sd with free solutions v (supported on freeBelow b) via w j = xor (w0 j) (if free&j>=b then key j else v j)
      refine Finset.card_bij
        (fun w _ j => if freeBelow k r b j then w j else false)
        (fun w hw => ?_) (fun w₁ hw₁ w₂ hw₂ heq => ?_) (fun v hv => ?_)
      · rcases Finset.mem_filter.mp hw with ⟨hwS, hsd_eq⟩
        rcases (Finset.mem_filter.mp hwS).2 with ⟨hsol, htop⟩
        simp only [isSolVec, Bool.and_eq_true, List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at hsol
        have hrec := sweep_reconstructs_of_valid hk hr x w hsol.1.1 hsol.1.2
        have hnf_eq : ∀ j : Fin k, isFree k r j = false → sweepW0 hk hr x sd j = w j := by
          rw [← hsd_eq]; exact hrec.1
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun j hfb => by simp [hfb], fun i => ?_⟩
        apply b2f_inj
        rw [b2f_finRange_xor, b2f_xor, seedRhs, topFreeRhs, b2f_xor, b2f_finRange_xor, b2f_finRange_xor]
        have hm_i := congrArg b2f (hsol.2 i)
        rw [b2f_finRange_xor] at hm_i
        rw [← hm_i]
        have hsum : ∀ j : Fin k,
            b2f ((if freeBelow k r b j = true then w j else false) && inMat x i j) =
            b2f (w j && inMat x i j) + b2f (sweepW0 hk hr x sd j && inMat x i j) +
            b2f (if isFree k r j && decide (b ≤ j.val) && key j then inMat x i j else false) := by
          intro j
          by_cases hf : isFree k r j = true
          · rw [sweepW0_free_zero hk hr x sd j hf]
            by_cases hjb : j.val < b
            · have hfb : freeBelow k r b j = true := by simp [freeBelow, hf, hjb]
              have hge : ¬ b ≤ j.val := by omega
              simp [hfb, hge]
            · have hfb : freeBelow k r b j = false := by simp [freeBelow, hf, hjb]
              have hge : b ≤ j.val := by omega
              have hwj : w j = key j := htop j hge
              simp only [hfb, Bool.false_eq_true, ↓reduceIte, Bool.false_and, b2f_false, zero_add, add_zero,
                hf, hge, decide_true, Bool.and_self, Bool.true_and, hwj]
              cases key j <;> cases inMat x i j <;> decide
          · have hff : isFree k r j = false := by cases h : isFree k r j <;> simp_all
            have hfb : freeBelow k r b j = false := by simp [freeBelow, hff]
            rw [hnf_eq j hff]
            simp only [hfb, hff, Bool.false_eq_true, ↓reduceIte, Bool.false_and, b2f_false, add_zero]
            exact (f2_add_self _).symm
        simp_rw [hsum, Finset.sum_add_distrib]
      · rcases Finset.mem_filter.mp hw₁ with ⟨hw₁S, hsd₁⟩
        rcases Finset.mem_filter.mp hw₂ with ⟨hw₂S, hsd₂⟩
        rcases (Finset.mem_filter.mp hw₁S).2 with ⟨hs₁, ht₁⟩
        rcases (Finset.mem_filter.mp hw₂S).2 with ⟨hs₂, ht₂⟩
        simp only [isSolVec, Bool.and_eq_true, List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at hs₁ hs₂
        have hr₁ := (sweep_reconstructs_of_valid hk hr x w₁ hs₁.1.1 hs₁.1.2).1
        have hr₂ := (sweep_reconstructs_of_valid hk hr x w₂ hs₂.1.1 hs₂.1.2).1
        rw [hsd₁] at hr₁; rw [hsd₂] at hr₂
        funext j
        by_cases hf : isFree k r j = true
        · by_cases hjb : j.val < b
          · have hfb : freeBelow k r b j = true := by simp [freeBelow, hf, hjb]
            have h := congrFun heq j; simpa [hfb] using h
          · rw [ht₁ j (by omega), ht₂ j (by omega)]
        · have hff : isFree k r j = false := by cases h : isFree k r j <;> simp_all
          rw [← hr₁ j hff, ← hr₂ j hff]
      · rcases (Finset.mem_filter.mp hv).2 with ⟨hv_supp, hv_mat⟩
        let w : Fin k → Bool := fun j =>
          if isFree k r j then (if b ≤ j.val then key j else v j)
          else sweepW0 hk hr x sd j
        have hnf : ∀ j : Fin k, isFree k r j = false → w j = sweepW0 hk hr x sd j := by
          intro j hff; simp [w, hff]
        have hok_sd := hmt'.1
        simp only [okSeed, Bool.and_eq_true, List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at hok_sd
        refine ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩, ?_⟩, ?_⟩
        · simp only [isSolVec, Bool.and_eq_true, List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq]
          refine ⟨⟨fun i => ?_, fun i => ?_⟩, fun i => ?_⟩
          · have h := stateV_congr_nonFree hk hr x w (sweepW0 hk hr x sd) hnf false i
            exact h.trans (hok_sd.1 i)
          · have h := stateV_congr_nonFree hk hr x w (sweepW0 hk hr x sd) hnf true i
            exact h.trans (hok_sd.2 i)
          · apply b2f_inj
            rw [b2f_finRange_xor]
            have hvi := congrArg b2f (hv_mat i)
            rw [b2f_finRange_xor, b2f_xor, seedRhs, topFreeRhs, b2f_xor, b2f_finRange_xor, b2f_finRange_xor] at hvi
            have hsum : ∀ j : Fin k,
                b2f (w j && inMat x i j) =
                b2f (v j && inMat x i j) + b2f (sweepW0 hk hr x sd j && inMat x i j) +
                b2f (if isFree k r j && decide (b ≤ j.val) && key j then inMat x i j else false) := by
              intro j
              by_cases hf : isFree k r j = true
              · rw [sweepW0_free_zero hk hr x sd j hf]
                by_cases hjb : b ≤ j.val
                · have hfb : freeBelow k r b j = false := by simp [freeBelow, hf]; omega
                  rw [hv_supp j hfb]
                  simp only [w, hf, hjb, ↓reduceIte, Bool.false_and, b2f_false, zero_add, decide_true, Bool.and_self, Bool.true_and]
                  cases key j <;> cases inMat x i j <;> decide
                · simp [w, hf, hjb]
              · have hff : isFree k r j = false := by cases h : isFree k r j <;> simp_all
                have hfb : freeBelow k r b j = false := by simp [freeBelow, hff]
                rw [hv_supp j hfb]
                simp [w, hff]
            simp_rw [hsum, Finset.sum_add_distrib]
            have h1 := f2_add_self (∑ j : Fin k, b2f (sweepW0 hk hr x sd j && inMat x i j))
            have h2 := f2_add_self (∑ j : Fin k, b2f (if isFree k r j && decide (b ≤ j.val) && key j then inMat x i j else false))
            linear_combination hvi + h1 + h2
        · intro j hjb
          by_cases hf : isFree k r j = true
          · simp [w, hf, hjb]
          · have hff : isFree k r j = false := by cases h : isFree k r j <;> simp_all
            simp [w, hff, hmt'.2 j hjb hff]
        · funext i
          have hnf_s : isFree k r (seedPos k r hr i) = false := by
            by_contra h
            have hft : isFree k r (seedPos k r hr i) = true := by
              cases h' : isFree k r (seedPos k r hr i) <;> simp_all
            have hs0 := isSeed_false_of_isFree hr (seedPos k r hr i) hft
            rw [← seedIdxOf_isSome_iff k r hr, seedIdxOf_seedPos] at hs0
            simp at hs0
          simp [w, hnf_s, sweepW0_preserves_seed]
        · funext j
          by_cases hfb : freeBelow k r b j = true
          · have hf : isFree k r j = true := (Bool.and_eq_true_iff.mp hfb).1
            have hlt : j.val < b := of_decide_eq_true (Bool.and_eq_true_iff.mp hfb).2
            have hnge : ¬ b ≤ j.val := by omega
            simp [w, hfb, hf, hnge]
          · have hfb' : freeBelow k r b j = false := by cases h : freeBelow k r b j <;> simp_all
            rw [hv_supp j hfb']; simp [hfb']
    · have hmtf : seedMatchTop hk hr x b key sd = false := by
        cases h : seedMatchTop hk hr x b key sd <;> simp_all
      simp only [hmtf, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      have hempty : fiber sd = ∅ := by
        ext w; simp only [fiber, Finset.mem_filter, topSolSet, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
        rintro ⟨⟨hsol, htop⟩, rfl⟩
        simp only [isSolVec, Bool.and_eq_true, List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at hsol
        have hrec := sweep_reconstructs_of_valid hk hr x w hsol.1.1 hsol.1.2
        have hmtt : seedMatchTop hk hr x b key (fun i => w (seedPos k r hr i)) = true := by
          simp only [seedMatchTop, hrec.2, Bool.true_and, List.all_eq_true, List.mem_finRange, true_implies,
            Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, beq_iff_eq]
          intro j
          by_cases hjb : b ≤ j.val
          · by_cases hf : isFree k r j = true
            · exact Or.inl (Or.inr hf)
            · have hff : isFree k r j = false := by cases h : isFree k r j <;> simp_all
              exact Or.inr ((hrec.1 j hff).trans (htop j hjb))
          · exact Or.inl (Or.inl hjb)
        rw [hmtt] at hmtf; exact absurd hmtf (by decide)
      rw [hempty, Finset.card_empty]
  simp_rw [hfiber_card]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul]

/-! #### Binary Search Step & Correctness for `solutions.getD rank 0` -/

lemma nat_lt_of_msb_diff {k a b : ℕ} (ha : a < 2 ^ k) (hb : b < 2 ^ k) (p : Fin k)
    (hhi : ∀ j : Fin k, p.val < j.val → a.testBit j.val = b.testBit j.val)
    (ha0 : a.testBit p.val = false) (hb1 : b.testBit p.val = true) : a < b := by
  rw [← natOfBits_of_testBit a ha, ← natOfBits_of_testBit b hb]
  unfold natOfBits
  have hsplit (u : Fin k → Bool) :
      (∑ j : Fin k, (u j).toNat * 2 ^ j.val) =
      (∑ j ∈ Finset.univ.filter (fun j : Fin k => j.val < p.val), (u j).toNat * 2 ^ j.val) +
      (u p).toNat * 2 ^ p.val +
      (∑ j ∈ Finset.univ.filter (fun j : Fin k => p.val < j.val), (u j).toNat * 2 ^ j.val) := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j : Fin k => p.val < j.val)]
    have hle : Finset.univ.filter (fun j : Fin k => ¬ p.val < j.val) =
        insert p (Finset.univ.filter (fun j : Fin k => j.val < p.val)) := by
      ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
      omega
    have hpnm : p ∉ Finset.univ.filter (fun j : Fin k => j.val < p.val) := by simp
    rw [hle, Finset.sum_insert hpnm]
    ring
  rw [hsplit (fun j => a.testBit j.val), hsplit (fun j => b.testBit j.val)]
  have hhi_sum :
      (∑ j ∈ Finset.univ.filter (fun j : Fin k => p.val < j.val), (a.testBit j.val).toNat * 2 ^ j.val) =
      (∑ j ∈ Finset.univ.filter (fun j : Fin k => p.val < j.val), (b.testBit j.val).toNat * 2 ^ j.val) := by
    refine Finset.sum_congr rfl fun j hj => by rw [hhi j (Finset.mem_filter.mp hj).2]
  have hlo_lt : (∑ j ∈ Finset.univ.filter (fun j : Fin k => j.val < p.val), (a.testBit j.val).toNat * 2 ^ j.val) <
      2 ^ p.val := by
    have hbij : (∑ j ∈ Finset.univ.filter (fun j : Fin k => j.val < p.val), (a.testBit j.val).toNat * 2 ^ j.val) =
        natOfBits (fun j : Fin p.val => a.testBit j.val) := by
      unfold natOfBits
      refine Finset.sum_bij (fun j hj => ⟨j.val, (Finset.mem_filter.mp hj).2⟩)
        (fun _ _ => Finset.mem_univ _)
        (fun j₁ _ j₂ _ heq => Fin.ext (Fin.mk.inj heq))
        (fun i _ => ⟨⟨i.val, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, i.isLt⟩, rfl⟩)
        (fun _ _ => rfl)
    rw [hbij]; exact natOfBits_lt _
  rw [hhi_sum, ha0, hb1]
  simp only [Bool.toNat_false, zero_mul, add_zero, Bool.toNat_true, one_mul]
  omega

lemma filter_or_eq_append_of_pairwise {l : List ℕ} (hpw : l.Pairwise (· < ·))
    (P₀ P₁ : ℕ → Bool) (hord : ∀ a b, P₀ a = true → P₁ b = true → a < b) :
    l.filter (fun a => P₀ a || P₁ a) = l.filter P₀ ++ l.filter P₁ := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.pairwise_cons] at hpw
    have iht := ih hpw.2
    cases h0 : P₀ a
    · cases h1 : P₁ a
      · simp [h0, h1, iht]
      · have ht0 : t.filter P₀ = [] := by
          rw [List.filter_eq_nil_iff]
          intro b hb h0b
          have hlt1 : a < b := hpw.1 b hb
          have hlt2 : b < a := hord b a h0b h1
          omega
        simp [h0, h1, iht, ht0]
    · cases h1 : P₁ a
      · simp [h0, h1, iht]
      · exfalso; have := hord a a h0 h1; omega

def solNatList {k r m : ℕ} (hk : 0 < k) (x : Fin (nIn k r m) → Bool) : List ℕ :=
  (List.range (2 ^ k)).filter (fun w => isSolVec hk x (fun j => w.testBit j.val))

def topNatList {k r m : ℕ} (hk : 0 < k) (x : Fin (nIn k r m) → Bool)
    (b : ℕ) (key : Fin k → Bool) : List ℕ :=
  (solNatList hk x).filter (fun w => (List.finRange k).all (fun j => !decide (b ≤ j.val) || (w.testBit j.val == key j)))

lemma solNatList_pairwise {k r m : ℕ} (hk : 0 < k) (x : Fin (nIn k r m) → Bool) :
    (solNatList hk x).Pairwise (· < ·) :=
  List.Pairwise.filter _ List.pairwise_lt_range

lemma topNatList_length {k r m : ℕ} (hk : 0 < k) (x : Fin (nIn k r m) → Bool)
    (b : ℕ) (key : Fin k → Bool) :
    (topNatList hk x b key).length = (topSolSet hk x b key).card := by
  have hnd : (topNatList hk x b key).Nodup :=
    ((solNatList_pairwise hk x).filter _).imp (fun h => ne_of_lt h)
  rw [← List.toFinset_card_of_nodup hnd]
  refine Finset.card_bij
    (fun w _ j => w.testBit j.val)
    (fun w hw => ?_) (fun w₁ hw₁ w₂ hw₂ heq => ?_) (fun v hv => ?_)
  · simp only [List.mem_toFinset, topNatList, solNatList, List.mem_filter, List.mem_range,
      List.all_eq_true, List.mem_finRange, true_implies, Bool.or_eq_true, Bool.not_eq_true',
      decide_eq_false_iff_not, beq_iff_eq] at hw
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw.1.2, fun j hjb => ?_⟩
    rcases hw.2 j with hlt | heq
    · exact absurd hjb hlt
    · exact heq
  · simp only [List.mem_toFinset, topNatList, solNatList, List.mem_filter, List.mem_range] at hw₁ hw₂
    rw [← natOfBits_of_testBit w₁ hw₁.1.1, ← natOfBits_of_testBit w₂ hw₂.1.1]
    exact congrArg natOfBits heq
  · rcases (Finset.mem_filter.mp hv).2 with ⟨hsol, htop⟩
    refine ⟨natOfBits v, ?_, funext (natOfBits_testBit v)⟩
    simp only [List.mem_toFinset, topNatList, solNatList, List.mem_filter, List.mem_range,
      List.all_eq_true, List.mem_finRange, true_implies, Bool.or_eq_true, Bool.not_eq_true',
      decide_eq_false_iff_not, beq_iff_eq]
    refine ⟨⟨natOfBits_lt v, ?_⟩, fun j => ?_⟩
    · convert hsol using 2; funext j; exact natOfBits_testBit v j
    · by_cases hjb : b ≤ j.val
      · right; rw [natOfBits_testBit]; exact htop j hjb
      · left; exact hjb

lemma topNatList_split {k r m : ℕ} (hk : 0 < k) (x : Fin (nIn k r m) → Bool)
    (b : Fin k) (key : Fin k → Bool) :
    let key0 : Fin k → Bool := fun j => if j = b then false else key j
    let key1 : Fin k → Bool := fun j => if j = b then true else key j
    topNatList hk x (b.val + 1) key =
      topNatList hk x b.val key0 ++ topNatList hk x b.val key1 := by
  intro key0 key1
  unfold topNatList
  let P₀ : ℕ → Bool := fun w => (List.finRange k).all (fun j => !decide (b.val ≤ j.val) || (w.testBit j.val == key0 j))
  let P₁ : ℕ → Bool := fun w => (List.finRange k).all (fun j => !decide (b.val ≤ j.val) || (w.testBit j.val == key1 j))
  have hor : (solNatList hk x).filter (fun w => (List.finRange k).all (fun j => !decide (b.val + 1 ≤ j.val) || (w.testBit j.val == key j))) =
      (solNatList hk x).filter (fun w => P₀ w || P₁ w) := by
    refine List.filter_congr fun w _ => ?_
    rw [Bool.eq_iff_iff]
    simp only [P₀, P₁, Bool.or_eq_true, List.all_eq_true, List.mem_finRange, true_implies,
      Bool.not_eq_true', decide_eq_false_iff_not, beq_iff_eq]
    constructor
    · intro h
      cases hwb : w.testBit b.val
      · left; intro j
        by_cases hjb : b.val ≤ j.val
        · by_cases hjeq : j = b
          · subst hjeq; right; simp [key0, hwb]
          · have hgt : b.val + 1 ≤ j.val := by
              have : j.val ≠ b.val := fun he => hjeq (Fin.ext he); omega
            rcases h j with hlt | heq
            · exact absurd hgt hlt
            · right; simp [key0, hjeq, heq]
        · exact Or.inl hjb
      · right; intro j
        by_cases hjb : b.val ≤ j.val
        · by_cases hjeq : j = b
          · subst hjeq; right; simp [key1, hwb]
          · have hgt : b.val + 1 ≤ j.val := by
              have : j.val ≠ b.val := fun he => hjeq (Fin.ext he); omega
            rcases h j with hlt | heq
            · exact absurd hgt hlt
            · right; simp [key1, hjeq, heq]
        · exact Or.inl hjb
    · rintro (h | h) j
      · by_cases hgt : b.val + 1 ≤ j.val
        · have hne : j ≠ b := fun he => by subst he; omega
          rcases h j with hlt | heq
          · exact absurd (by omega) hlt
          · right; simpa [key0, hne] using heq
        · exact Or.inl hgt
      · by_cases hgt : b.val + 1 ≤ j.val
        · have hne : j ≠ b := fun he => by subst he; omega
          rcases h j with hlt | heq
          · exact absurd (by omega) hlt
          · right; simpa [key1, hne] using heq
        · exact Or.inl hgt
  rw [hor]
  -- Apply filter_or_eq_append_of_pairwise on solNatList!
  have hmem_lt : ∀ w ∈ solNatList hk x, w < 2 ^ k := fun w hw => by
    simp [solNatList] at hw; exact hw.1
  -- Restrict pairwise helper to elements in solNatList
  have hgen : ∀ l : List ℕ, l.Pairwise (· < ·) → (∀ w ∈ l, w < 2 ^ k) →
      l.filter (fun a => P₀ a || P₁ a) = l.filter P₀ ++ l.filter P₁ := by
    intro l hpw hlt
    induction l with
    | nil => simp
    | cons a t ih =>
      rw [List.pairwise_cons] at hpw
      have iht := ih hpw.2 (fun w hw => hlt w (List.mem_cons_of_mem a hw))
      have hord : ∀ u v, u < 2 ^ k → v < 2 ^ k → P₀ u = true → P₁ v = true → u < v := by
        intro u v hu hv h0 h1
        simp only [P₀, P₁, List.all_eq_true, List.mem_finRange, true_implies, Bool.or_eq_true,
          Bool.not_eq_true', decide_eq_false_iff_not, beq_iff_eq] at h0 h1
        apply nat_lt_of_msb_diff hu hv b
        · intro j hj
          have hne : j ≠ b := fun he => by subst he; omega
          have hu_j : u.testBit j.val = key j := by
            rcases h0 j with hbad | heq
            · exact absurd (by omega) hbad
            · simpa [key0, hne] using heq
          have hv_j : v.testBit j.val = key j := by
            rcases h1 j with hbad | heq
            · exact absurd (by omega) hbad
            · simpa [key1, hne] using heq
          rw [hu_j, hv_j]
        · rcases h0 b with hbad | heq
          · exact absurd le_rfl hbad
          · simpa [key0] using heq
        · rcases h1 b with hbad | heq
          · exact absurd le_rfl hbad
          · simpa [key1] using heq
      cases h0 : P₀ a
      · cases h1 : P₁ a
        · simp [h0, h1, iht]
        · have ht0 : t.filter P₀ = [] := by
            rw [List.filter_eq_nil_iff]
            intro c hc h0c
            have hlt1 : a < c := hpw.1 c hc
            have hlt2 : c < a := hord c a (hlt c (List.mem_cons_of_mem a hc)) (hlt a List.mem_cons_self) h0c h1
            omega
          simp [h0, h1, iht, ht0]
      · cases h1 : P₁ a
        · simp [h0, h1, iht]
        · exfalso; have := hord a a (hlt a List.mem_cons_self) (hlt a List.mem_cons_self) h0 h1; omega
  exact hgen (solNatList hk x) (solNatList_pairwise hk x) hmem_lt

structure BSState (k : ℕ) where
  key : Fin k → Bool
  rem : ZMod (2 ^ (k + 1))

def totalCountW {k r m : ℕ} (hk : 0 < k) (hr : 4 ≤ r) (x : Fin (nIn k r m) → Bool) : ZMod (2 ^ (k + 1)) :=
  let numSeeds : ZMod (2 ^ (k + 1)) :=
    ((Finset.univ.filter (fun sd : Fin (seedLen k r) → Bool =>
      okSeed hk hr x sd && linOk x k (seedRhs hk hr x sd))).card : ZMod (2 ^ (k + 1)))
  ((numSeeds.val * 2 ^ (nullityOf x k) : ℕ) : ZMod (2 ^ (k + 1)))

lemma totalCountW_val {k r m : ℕ} (hk : 0 < k) (hr : 4 ≤ r) (x : Fin (nIn k r m) → Bool) :
    (totalCountW hk hr x).val = (solNatList hk x).length := by
  haveI : NeZero (2 ^ (k + 1)) := ⟨by positivity⟩
  have hlen : (solNatList hk x).length = (topSolSet hk x k (fun _ => false)).card := by
    rw [← topNatList_length hk x k (fun _ => false)]
    congr 1; unfold topNatList
    have htriv : ∀ w : ℕ, (List.finRange k).all (fun j : Fin k => !decide (k ≤ j.val) || (w.testBit j.val == false)) = true := by
      intro w; simp only [List.all_eq_true, List.mem_finRange, true_implies, Bool.or_eq_true, Bool.not_eq_true',
        decide_eq_false_iff_not]; intro j; left; omega
    exact (List.filter_eq_self.mpr (fun w _ => htriv w)).symm
  have hcard := card_topSolSet hk hr x k le_rfl (fun _ => false)
  have hmt_eq : ∀ sd : Fin (seedLen k r) → Bool,
      seedMatchTop hk hr x k (fun _ => false) sd = okSeed hk hr x sd := by
    intro sd; unfold seedMatchTop
    have htriv : (List.finRange k).all (fun j : Fin k => !decide (k ≤ j.val) || isFree k r j || (sweepW0 hk hr x sd j == false)) = true := by
      simp only [List.all_eq_true, List.mem_finRange, true_implies, Bool.or_eq_true, Bool.not_eq_true',
        decide_eq_false_iff_not]; intro j; left; left; omega
    rw [htriv, Bool.and_true]
  have htop_eq : ∀ i : Fin m, topFreeRhs x k (fun _ => false) i = false := by
    intro i; unfold topFreeRhs
    have h0 : ∀ l : List (Fin k), l.foldl (fun acc j => xor acc (if isFree k r j && decide (k ≤ j.val) && false then inMat x i j else false)) false = false := by
      intro l; induction l with
      | nil => rfl
      | cons a t ih => simpa using ih
    exact h0 _
  have hfilt_eq : Finset.univ.filter (fun sd : Fin (seedLen k r) → Bool =>
        seedMatchTop hk hr x k (fun _ => false) sd &&
        linOk x k (fun i => xor (seedRhs hk hr x sd i) (topFreeRhs x k (fun _ => false) i))) =
      Finset.univ.filter (fun sd : Fin (seedLen k r) → Bool =>
        okSeed hk hr x sd && linOk x k (seedRhs hk hr x sd)) := by
    ext sd; simp [hmt_eq, htop_eq]
  rw [hfilt_eq] at hcard
  have hnum_lt : (Finset.univ.filter (fun sd : Fin (seedLen k r) → Bool =>
      okSeed hk hr x sd && linOk x k (seedRhs hk hr x sd))).card < 2 ^ (k + 1) := by
    have h1 : (Finset.univ.filter (fun sd : Fin (seedLen k r) → Bool =>
        okSeed hk hr x sd && linOk x k (seedRhs hk hr x sd))).card ≤ 2 ^ (seedLen k r) := by
      calc _ ≤ (Finset.univ : Finset (Fin (seedLen k r) → Bool)).card := Finset.card_filter_le _ _
        _ = 2 ^ (seedLen k r) := by simp [Fintype.card_fun, Fintype.card_bool]
    have h2 : 2 ^ (seedLen k r) ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) (seedLen_le_k hr)
    have h3 : 2 ^ k < 2 ^ (k + 1) := Nat.pow_lt_pow_right (by decide) (by omega)
    omega
  have htot_lt : (topSolSet hk x k (fun _ => false)).card < 2 ^ (k + 1) := by
    have h1 : (topSolSet hk x k (fun _ => false)).card ≤ 2 ^ k := by
      calc _ ≤ (Finset.univ : Finset (Fin k → Bool)).card := Finset.card_filter_le _ _
        _ = 2 ^ k := by simp [Fintype.card_fun, Fintype.card_bool]
    have h2 : 2 ^ k < 2 ^ (k + 1) := Nat.pow_lt_pow_right (by decide) (by omega)
    omega
  unfold totalCountW
  rw [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt hnum_lt, ← hcard, Nat.mod_eq_of_lt htot_lt, hlen]

def bsCntZeroW {k r m : ℕ} (hk : 0 < k) (hr : 4 ≤ r) (x : Fin (nIn k r m) → Bool)
    (b : Fin k) (key : Fin k → Bool) : ZMod (2 ^ (k + 1)) :=
  let key0 : Fin k → Bool := fun j => if j = b then false else key j
  let numSeeds : ZMod (2 ^ (k + 1)) :=
    ((Finset.univ.filter (fun sd : Fin (seedLen k r) → Bool =>
      seedMatchTop hk hr x b.val key0 sd &&
      linOk x b.val (fun i => xor (seedRhs hk hr x sd i) (topFreeRhs x b.val key0 i)))).card : ZMod (2 ^ (k + 1)))
  ((numSeeds.val * 2 ^ (nullityOf x b.val) : ℕ) : ZMod (2 ^ (k + 1)))

lemma bsCntZeroW_val {k r m : ℕ} (hk : 0 < k) (hr : 4 ≤ r) (x : Fin (nIn k r m) → Bool)
    (b : Fin k) (key : Fin k → Bool) :
    (bsCntZeroW hk hr x b key).val =
      (topNatList hk x b.val (fun j => if j = b then false else key j)).length := by
  haveI : NeZero (2 ^ (k + 1)) := ⟨by positivity⟩
  let key0 : Fin k → Bool := fun j => if j = b then false else key j
  have hcard := card_topSolSet hk hr x b.val (le_of_lt b.isLt) key0
  have hnum_lt : (Finset.univ.filter (fun sd : Fin (seedLen k r) → Bool =>
      seedMatchTop hk hr x b.val key0 sd &&
      linOk x b.val (fun i => xor (seedRhs hk hr x sd i) (topFreeRhs x b.val key0 i)))).card < 2 ^ (k + 1) := by
    have h1 : (Finset.univ.filter (fun sd : Fin (seedLen k r) → Bool =>
        seedMatchTop hk hr x b.val key0 sd &&
        linOk x b.val (fun i => xor (seedRhs hk hr x sd i) (topFreeRhs x b.val key0 i)))).card ≤ 2 ^ (seedLen k r) := by
      calc _ ≤ (Finset.univ : Finset (Fin (seedLen k r) → Bool)).card := Finset.card_filter_le _ _
        _ = 2 ^ (seedLen k r) := by simp
    have h2 : 2 ^ (seedLen k r) ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) (seedLen_le_k hr)
    have h3 : 2 ^ k < 2 ^ (k + 1) := Nat.pow_lt_pow_right (by decide) (by omega)
    omega
  have htot_lt : (topSolSet hk x b.val key0).card < 2 ^ (k + 1) := by
    have h1 : (topSolSet hk x b.val key0).card ≤ 2 ^ k := by
      calc _ ≤ (Finset.univ : Finset (Fin k → Bool)).card := Finset.card_filter_le _ _
        _ = 2 ^ k := by simp
    have h2 : 2 ^ k < 2 ^ (k + 1) := Nat.pow_lt_pow_right (by decide) (by omega)
    omega
  unfold bsCntZeroW
  rw [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt hnum_lt, ← hcard, Nat.mod_eq_of_lt htot_lt,
    topNatList_length]

def bsStep {k r m : ℕ} (hk : 0 < k) (hr : 4 ≤ r) (x : Fin (nIn k r m) → Bool)
    (b : Fin k) (st : BSState k) : BSState k :=
  let c0 := bsCntZeroW hk hr x b st.key
  let go1 := decide (c0.val ≤ st.rem.val)
  ⟨fun j => if j = b then go1 else st.key j,
   if go1 then st.rem - c0 else st.rem⟩

def bsRun {k r m : ℕ} (hk : 0 < k) (hr : 4 ≤ r) (x : Fin (nIn k r m) → Bool)
    (rankW : ZMod (2 ^ (k + 1))) : ℕ → BSState k
  | 0 => ⟨fun _ => false, rankW⟩
  | t + 1 =>
    if ht : t < k then bsStep hk hr x ⟨k - 1 - t, by omega⟩ (bsRun hk hr x rankW t)
    else bsRun hk hr x rankW t

lemma bsRun_spec {k r m : ℕ} (hk : 0 < k) (hr : 4 ≤ r) (x : Fin (nIn k r m) → Bool)
    (rank : Fin (2 ^ k)) (hvalid : rank.val < (solNatList hk x).length) :
    let rankW : ZMod (2 ^ (k + 1)) := (rank.val : ZMod (2 ^ (k + 1)))
    ∀ t ≤ k,
      let st := bsRun hk hr x rankW t
      st.rem.val < (topNatList hk x (k - t) st.key).length ∧
      (solNatList hk x).getD rank.val 0 = (topNatList hk x (k - t) st.key).getD st.rem.val 0 := by
  intro rankW t ht
  haveI : NeZero (2 ^ (k + 1)) := ⟨by positivity⟩
  have hrk_val : rankW.val = rank.val := by
    dsimp only [rankW]
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (lt_trans rank.isLt (Nat.pow_lt_pow_right (by decide) (by omega)))]
  induction t with
  | zero =>
    dsimp only [bsRun, Nat.sub_zero]
    have htop : topNatList hk x k (fun _ => false) = solNatList hk x := by
      unfold topNatList
      have htriv : ∀ w : ℕ, (List.finRange k).all (fun j : Fin k => !decide (k ≤ j.val) || (w.testBit j.val == false)) = true := by
        intro w; simp only [List.all_eq_true, List.mem_finRange, true_implies, Bool.or_eq_true, Bool.not_eq_true',
          decide_eq_false_iff_not]; intro j; left; omega
      exact List.filter_eq_self.mpr (fun w _ => htriv w)
    rw [htop, hrk_val]
    exact ⟨hvalid, rfl⟩
  | succ t ih =>
    have ht_lt : t < k := by omega
    obtain ⟨hrem_lt, hget⟩ := ih (by omega)
    set st := bsRun hk hr x rankW t
    set b : Fin k := ⟨k - 1 - t, by omega⟩
    have hb_succ : b.val + 1 = k - t := by dsimp only [b]; omega
    have hb_eq : k - (t + 1) = b.val := by dsimp only [b]; omega
    have hsplit := topNatList_split hk x b st.key
    dsimp only at hsplit
    rw [hb_succ] at hsplit
    have hc0 := bsCntZeroW_val hk hr x b st.key
    dsimp only [bsRun]
    rw [dif_pos ht_lt]
    change (bsStep hk hr x b st).rem.val < (topNatList hk x (k - (t + 1)) (bsStep hk hr x b st).key).length ∧
      (solNatList hk x).getD rank.val 0 = (topNatList hk x (k - (t + 1)) (bsStep hk hr x b st).key).getD (bsStep hk hr x b st).rem.val 0
    dsimp only [bsStep]
    rw [hb_eq]
    by_cases hgo : (bsCntZeroW hk hr x b st.key).val ≤ st.rem.val
    · rw [decide_eq_true hgo, if_pos rfl]
      have hsub_val : (st.rem - bsCntZeroW hk hr x b st.key).val =
          st.rem.val - (bsCntZeroW hk hr x b st.key).val := by
        have hlt1 := ZMod.val_lt st.rem
        have hcast : ((st.rem.val - (bsCntZeroW hk hr x b st.key).val : ℕ) : ZMod (2 ^ (k + 1))) =
            st.rem - bsCntZeroW hk hr x b st.key := by
          rw [Nat.cast_sub hgo, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
        have hv := congrArg ZMod.val hcast
        rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)] at hv
        exact hv.symm
      rw [hsub_val]
      rw [hsplit, List.length_append] at hrem_lt
      refine ⟨by omega, ?_⟩
      rw [hget, hsplit, getD_append_right_ge _ _ _ _ (by omega), hc0]
    · rw [decide_eq_false hgo, if_neg (by decide)]
      refine ⟨by omega, ?_⟩
      rw [hget, hsplit, getD_append_left_lt _ _ _ _ (by omega)]

lemma bsRun_end_testBit {k r m : ℕ} (hk : 0 < k) (hr : 4 ≤ r) (x : Fin (nIn k r m) → Bool)
    (rank : Fin (2 ^ k)) (hvalid : rank.val < (solNatList hk x).length) (d : Fin k) :
    let st := bsRun hk hr x (rank.val : ZMod (2 ^ (k + 1))) k
    ((solNatList hk x).getD rank.val 0).testBit d.val = st.key d := by
  intro st
  obtain ⟨hrem_lt, hget⟩ := bsRun_spec hk hr x rank hvalid k le_rfl
  rw [Nat.sub_self] at hrem_lt hget
  have hmem : (topNatList hk x 0 st.key)[st.rem.val]'hrem_lt ∈ topNatList hk x 0 st.key :=
    List.getElem_mem hrem_lt
  have hget_eq : (topNatList hk x 0 st.key).getD st.rem.val 0 = (topNatList hk x 0 st.key)[st.rem.val]'hrem_lt := by
    dsimp only [st]; simp [List.getD, List.getElem?_eq_getElem hrem_lt]
  rw [hget, hget_eq]
  simp only [topNatList, List.mem_filter, List.all_eq_true, List.mem_finRange, true_implies,
    Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, beq_iff_eq] at hmem
  rcases hmem.2 d with hbad | heq
  · exact absurd (Nat.zero_le _) hbad
  · exact heq

/-! ### Part 6: `Extends` Circuit Constructions & Size Bound -/

lemma Extends.add_beq {n : ℕ} {S : Set (Sig n)} {f g : Sig n} (hf : f ∈ S) (hg : g ∈ S) :
    Extends n S {fun x => f x == g x} 5 := by
  have hx := Extends.add_xor hf hg
  have hn := Extends.add_not (S := S ∪ {fun x => xor (f x) (g x)}) (Or.inr rfl)
  have heq : (fun x => !(xor (f x) (g x))) = fun x => f x == g x := by
    funext x; cases f x <;> cases g x <;> decide
  rw [heq] at hn
  exact hx.seq hn

lemma Extends.rotV_sig {n k : ℕ} (hk : 0 < k) (offset : ℕ) (v : Fin k → Sig n) :
    Extends n (Set.range v) (Set.range (fun j : Fin k => fun x => rotV hk offset (fun i => v i x) j)) 0 := by
  apply Extends.of_subset
  rintro _ ⟨j, rfl⟩
  exact ⟨⟨(j.val + k - offset % k) % k, Nat.mod_lt _ hk⟩, rfl⟩

lemma Extends.mixV_sig {n k : ℕ} (hk : 0 < k) (gap : ℕ) (v : Fin k → Sig n) :
    Extends n (Set.range v) (Set.range (fun j : Fin k => fun x => mixV hk gap (fun i => v i x) j)) (8 * k) := by
  have hp := Extends.add_range_fin (S := Set.range v)
    (f := fun j : Fin k => fun x => mixV hk gap (fun i => v i x) j) (c := 8) (fun j => by
      let i1 : Fin k := ⟨(j.val + k - gap % k) % k, Nat.mod_lt _ hk⟩
      let i2 : Fin k := ⟨(j.val + k - (k - gap) % k) % k, Nat.mod_lt _ hk⟩
      have h1 : Extends n (Set.range v) {fun x => xor (v j x) (v i1 x)} 4 :=
        Extends.add_xor ⟨j, rfl⟩ ⟨i1, rfl⟩
      have h2 : Extends n (Set.range v ∪ {fun x => xor (v j x) (v i1 x)})
          {fun x => xor (xor (v j x) (v i1 x)) (v i2 x)} 4 :=
        Extends.add_xor (Or.inr rfl) (Or.inl ⟨i2, rfl⟩)
      exact h1.seq h2)
  exact hp.mono Set.Subset.rfl Set.Subset.rfl (by omega)

lemma Extends.chiV_sig {n k : ℕ} (hk : 0 < k) (v : Fin k → Sig n) :
    Extends n (Set.range v) (Set.range (fun j : Fin k => fun x => chiV hk (fun i => v i x) j)) (6 * k) := by
  have hp := Extends.add_range_fin (S := Set.range v)
    (f := fun j : Fin k => fun x => chiV hk (fun i => v i x) j) (c := 6) (fun j => by
      let i1 : Fin k := ⟨(j.val + 1) % k, Nat.mod_lt _ hk⟩
      let i2 : Fin k := ⟨(j.val + 2) % k, Nat.mod_lt _ hk⟩
      have h1 : Extends n (Set.range v) {fun x => !v i1 x} 1 := Extends.add_not ⟨i1, rfl⟩
      have h2 : Extends n (Set.range v ∪ {fun x => !v i1 x}) {fun x => !v i1 x && v i2 x} 1 :=
        Extends.add_and (Or.inr rfl) (Or.inl ⟨i2, rfl⟩)
      have h3 : Extends n (Set.range v ∪ {fun x => !v i1 x && v i2 x})
          {fun x => xor (v j x) (!v i1 x && v i2 x)} 4 :=
        Extends.add_xor (Or.inl ⟨j, rfl⟩) (Or.inr rfl)
      exact (h1.seq h2).seq h3)
  exact hp.mono Set.Subset.rfl Set.Subset.rfl (by omega)

lemma Extends.stepV_sig {n k : ℕ} (hk : 0 < k) (r : ℕ) (c : ℕ → Fin k → Sig n)
    (col : Bool) (raw prev : Fin k → Sig n) (t : ℕ) :
    Extends n (Set.range raw ∪ Set.range prev ∪ Set.range (c (if col then r + t else t)))
      (Set.range (fun j : Fin k => fun x => stepV hk r (fun idx i => c idx i x) col
        (fun i => raw i x) (fun i => prev i x) t j))
      (22 * k) := by
  let Base := Set.range raw ∪ Set.range prev ∪ Set.range (c (if col then r + t else t))
  let mv : Fin k → Sig n := fun j x => mixV hk (if col then 2 else 1) (fun i => prev i x) j
  let cv : Fin k → Sig n := fun j x => chiV hk (fun i => mv i x) j
  have hm : Extends n Base (Set.range mv) (8 * k) :=
    (Extends.mixV_sig hk _ prev).mono (fun _ h => Or.inl (Or.inr h)) Set.Subset.rfl le_rfl
  have hc : Extends n (Base ∪ Set.range mv) (Set.range cv) (6 * k) :=
    (Extends.chiV_sig hk mv).mono Set.subset_union_right Set.Subset.rfl le_rfl
  have hx : Extends n (Base ∪ Set.range cv)
      (Set.range (fun j : Fin k => fun x => stepV hk r (fun idx i => c idx i x) col
        (fun i => raw i x) (fun i => prev i x) t j)) (8 * k) := by
    have hp := Extends.add_range_fin (S := Base ∪ Set.range cv)
      (f := fun j : Fin k => fun x => stepV hk r (fun idx i => c idx i x) col
        (fun i => raw i x) (fun i => prev i x) t j) (c := 8) (fun j => by
        let iR : Fin k := ⟨(j.val + k - (if col then 3 * t + 1 else 2 * (t - 1)) % k) % k, Nat.mod_lt _ hk⟩
        have h1 : Extends n (Base ∪ Set.range cv) {fun x => xor (cv j x) (raw iR x)} 4 :=
          Extends.add_xor (Or.inr ⟨j, rfl⟩) (Or.inl (Or.inl (Or.inl ⟨iR, rfl⟩)))
        have h2 : Extends n ((Base ∪ Set.range cv) ∪ {fun x => xor (cv j x) (raw iR x)})
            {fun x => xor (xor (cv j x) (raw iR x)) (c (if col then r + t else t) j x)} 4 :=
          Extends.add_xor (Or.inr rfl) (Or.inl (Or.inl (Or.inr ⟨j, rfl⟩)))
        exact h1.seq h2)
    exact hp.mono Set.Subset.rfl Set.Subset.rfl (by omega)
  exact ((hm.seq hc).seq hx).mono Set.Subset.rfl Set.Subset.rfl (by omega)

def baseInputSigs (k r m : ℕ) : Set (Sig (nIn k r m)) :=
  Set.range (fun p : Fin (nIn k r m) => fun x => x p)

lemma inSched_mem_base {k r m : ℕ} (idx : Fin (2 * r)) (j : Fin k) :
    (fun x : Fin (nIn k r m) → Bool => inSched x idx j) ∈ baseInputSigs k r m :=
  ⟨_, rfl⟩

lemma inLeft_mem_base {k r m : ℕ} (j : Fin k) :
    (fun x : Fin (nIn k r m) → Bool => inLeft x j) ∈ baseInputSigs k r m := ⟨_, rfl⟩

lemma inRight_mem_base {k r m : ℕ} (j : Fin k) :
    (fun x : Fin (nIn k r m) → Bool => inRight x j) ∈ baseInputSigs k r m := ⟨_, rfl⟩

lemma inA_mem_base {k r m : ℕ} (i : Fin (hOf k)) :
    (fun x : Fin (nIn k r m) → Bool => inA x i) ∈ baseInputSigs k r m := ⟨_, rfl⟩

lemma inB_mem_base {k r m : ℕ} (i : Fin (hOf k)) :
    (fun x : Fin (nIn k r m) → Bool => inB x i) ∈ baseInputSigs k r m := ⟨_, rfl⟩

lemma inMat_mem_base {k r m : ℕ} (i : Fin m) (j : Fin k) :
    (fun x : Fin (nIn k r m) → Bool => inMat x i j) ∈ baseInputSigs k r m := ⟨_, rfl⟩

lemma inRhs_mem_base {k r m : ℕ} (i : Fin m) :
    (fun x : Fin (nIn k r m) → Bool => inRhs x i) ∈ baseInputSigs k r m := ⟨_, rfl⟩

lemma inRank_mem_base {k r m : ℕ} (j : Fin k) :
    (fun x : Fin (nIn k r m) → Bool => inRank x j) ∈ baseInputSigs k r m := ⟨_, rfl⟩

lemma Extends.stateVSteps_sig {k r m : ℕ} (hk : 0 < k) (col : Bool)
    (raw : Fin k → Sig (nIn k r m)) (name : Fin k → Sig (nIn k r m))
    (hname : ∀ j, name j ∈ baseInputSigs k r m) (steps : ℕ) (hsteps : steps ≤ r) :
    Extends (nIn k r m) (baseInputSigs k r m ∪ Set.range raw)
      (Set.range (fun j : Fin k => fun x =>
        stateVSteps hk r (schedVec x) col (fun i => raw i x) (fun i => name i x) steps j))
      (4 * k + steps * (22 * k)) := by
  let Base := baseInputSigs k r m ∪ Set.range raw
  let stSig (t : ℕ) (j : Fin k) : Sig (nIn k r m) := fun x =>
    stateVSteps hk r (schedVec x) col (fun i => raw i x) (fun i => name i x) t j
  have h0 : Extends (nIn k r m) Base (Set.range (stSig 0)) (4 * k) := by
    have hp := Extends.add_range_fin (S := Base) (f := stSig 0) (c := 4) (fun j => by
      let iR : Fin k := ⟨(j.val + k - (if col then 3 else 1) % k) % k, Nat.mod_lt _ hk⟩
      exact Extends.add_xor (Or.inr ⟨iR, rfl⟩) (Or.inl (hname j)))
    exact hp.mono Set.Subset.rfl Set.Subset.rfl (by omega)
  let Inv (t : ℕ) : Set (Sig (nIn k r m)) := Base ∪ Set.range (stSig t)
  have hstep : ∀ t < steps, Extends (nIn k r m) (Inv t) (Inv (t + 1)) (22 * k) := by
    intro t ht
    have hidx_ok : 1 ≤ (if col then r + (t + 1) else t + 1) ∧
        (if col then r + (t + 1) else t + 1) ≤ 2 * r := by cases col <;> simp <;> omega
    have hc_sub : Set.range (fun j : Fin k => fun x : Fin (nIn k r m) → Bool =>
        schedVec x (if col then r + (t + 1) else t + 1) j) ⊆ baseInputSigs k r m := by
      rintro _ ⟨j, rfl⟩
      have heq : (fun x : Fin (nIn k r m) → Bool => schedVec x (if col then r + (t + 1) else t + 1) j) =
          fun x => inSched x ⟨(if col then r + (t + 1) else t + 1) - 1, by omega⟩ j := by
        funext x; simp [schedVec, hidx_ok]
      dsimp only; rw [heq]; exact inSched_mem_base _ j
    have hs := Extends.stepV_sig (n := nIn k r m) hk r (fun idx j x => schedVec x idx j) col raw (stSig t) (t + 1)
    have hs' : Extends (nIn k r m) (Inv t) (Set.range (stSig (t + 1))) (22 * k) :=
      hs.mono (by
        rintro z ((h | h) | h)
        · exact Or.inl (Or.inr h)
        · exact Or.inr h
        · exact Or.inl (Or.inl (hc_sub h))) Set.Subset.rfl le_rfl
    exact ((Extends.of_subset Set.subset_union_left).union hs').mono Set.Subset.rfl Set.Subset.rfl (by omega)
  have hfold := Extends.fold_nat_const steps Inv (22 * k) hstep
  have hstart : Extends (nIn k r m) Base (Inv 0) (4 * k) :=
    ((Extends.of_subset Set.Subset.rfl).union h0).mono Set.Subset.rfl Set.Subset.rfl (by omega)
  exact (hstart.seq (hfold.mono Set.subset_union_right Set.Subset.rfl le_rfl)).mono
    Set.Subset.rfl Set.subset_union_right (by omega)

lemma Extends.stateNoLastFeedV_sig {k r m : ℕ} (hk : 0 < k) (hr : 1 ≤ r) (col : Bool)
    (raw name : Fin k → Sig (nIn k r m)) (hname : ∀ j, name j ∈ baseInputSigs k r m) :
    Extends (nIn k r m) (baseInputSigs k r m ∪ Set.range raw)
      (Set.range (fun j : Fin k => fun x =>
        stateNoLastFeedV hk r (schedVec x) col (fun i => raw i x) (fun i => name i x) j))
      (22 * k * r + 4 * k) := by
  let Base := baseInputSigs k r m ∪ Set.range raw
  let prev : Fin k → Sig (nIn k r m) := fun j x =>
    stateVSteps hk r (schedVec x) col (fun i => raw i x) (fun i => name i x) (r - 1) j
  have hprev := Extends.stateVSteps_sig hk col raw name hname (r - 1) (by omega)
  let mv : Fin k → Sig (nIn k r m) := fun j x => mixV hk (if col then 2 else 1) (fun i => prev i x) j
  let cv : Fin k → Sig (nIn k r m) := fun j x => chiV hk (fun i => mv i x) j
  have hm : Extends (nIn k r m) (Base ∪ Set.range prev) (Set.range mv) (8 * k) :=
    (Extends.mixV_sig hk _ prev).mono Set.subset_union_right Set.Subset.rfl le_rfl
  have hc : Extends (nIn k r m) (Base ∪ Set.range mv) (Set.range cv) (6 * k) :=
    (Extends.chiV_sig hk mv).mono Set.subset_union_right Set.Subset.rfl le_rfl
  have hidx_ok : 1 ≤ (if col then r + r else r) ∧ (if col then r + r else r) ≤ 2 * r := by
    cases col <;> simp <;> omega
  have hx : Extends (nIn k r m) (Base ∪ Set.range cv)
      (Set.range (fun j : Fin k => fun x =>
        stateNoLastFeedV hk r (schedVec x) col (fun i => raw i x) (fun i => name i x) j)) (4 * k) := by
    have hp := Extends.add_range_fin (S := Base ∪ Set.range cv)
      (f := fun j : Fin k => fun x =>
        stateNoLastFeedV hk r (schedVec x) col (fun i => raw i x) (fun i => name i x) j)
      (c := 4) (fun j => by
        have hcj : (fun x : Fin (nIn k r m) → Bool => schedVec x (if col then r + r else r) j) ∈ Base := by
          left
          have heq : (fun x : Fin (nIn k r m) → Bool => schedVec x (if col then r + r else r) j) =
              fun x => inSched x ⟨(if col then r + r else r) - 1, by omega⟩ j := by
            funext x; simp [schedVec, hidx_ok]
          rw [heq]; exact inSched_mem_base _ j
        exact Extends.add_xor (Or.inr ⟨j, rfl⟩) (Or.inl hcj))
    exact hp.mono Set.Subset.rfl Set.Subset.rfl (by omega)
  have hcomb := ((hprev.seq hm).seq hc).seq hx
  refine hcomb.mono Set.Subset.rfl Set.Subset.rfl ?_
  have hr1 : (r - 1) * (22 * k) + 18 * k ≤ 22 * k * r := by
    have : (r - 1) + 1 = r := by omega
    nlinarith
  omega

lemma Extends.sweepW0_sig {k r m : ℕ} (hk : 0 < k) (hr : 4 ≤ r)
    (sd : Fin (seedLen k r) → Bool) :
    Extends (nIn k r m) (baseInputSigs k r m)
      (Set.range (fun j : Fin k => fun x => sweepW0 hk hr x sd j))
      (if k ≤ uOf r then k else (hOf k + (r + 3)) * (22 * k * r + 4 * k + 4) + k) := by
  by_cases hku : k ≤ uOf r
  · rw [if_pos hku]
    have hconst : ∀ j : Fin k, ∀ x : Fin (nIn k r m) → Bool,
        sweepW0 hk hr x sd j = seedInit hr sd j := by
      intro j x
      have hA : ∀ t w, sweepStepA hk hr x t w = w := fun t w => by
        unfold sweepStepA; split_ifs with ht hlt <;> [omega; rfl; rfl]
      have hB : ∀ t w, sweepStepB hk hr x t w = w := fun t w => by
        unfold sweepStepB; split_ifs with hlt <;> [omega; rfl]
      have hfB : ∀ n w, (List.range n).foldl (fun w t => sweepStepB hk hr x t w) w = w := fun n => by
        induction n with
        | zero => intro w; rfl
        | succ n ih => intro w; rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, hB, ih]
      have hfA : ∀ n w, (List.range n).foldl (fun w t => sweepStepA hk hr x t w) w = w := fun n => by
        induction n with
        | zero => intro w; rfl
        | succ n ih => intro w; rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, hA, ih]
      unfold sweepW0 sweepAfterB sweepAfterA
      rw [hfB, hfA]
    have hp := Extends.add_range_fin (S := baseInputSigs k r m)
      (f := fun j : Fin k => fun x => sweepW0 hk hr x sd j) (c := 1) (fun j => by
        have : (fun x : Fin (nIn k r m) → Bool => sweepW0 hk hr x sd j) = fun _ => seedInit hr sd j := by
          funext x; exact hconst j x
        rw [this]; exact Extends.add_const _)
    exact hp.mono Set.Subset.rfl Set.Subset.rfl (by omega)
  · rw [if_neg hku]
    have hinit : Extends (nIn k r m) (baseInputSigs k r m)
        (baseInputSigs k r m ∪ Set.range (fun j : Fin k => fun x : Fin (nIn k r m) → Bool => sweepAfterA hk hr x sd 0 j)) k := by
      have hp := Extends.add_range_fin (S := baseInputSigs k r m)
        (f := fun j : Fin k => fun x : Fin (nIn k r m) → Bool => sweepAfterA hk hr x sd 0 j) (c := 1)
        (fun j => Extends.add_const (seedInit hr sd j))
      exact ((Extends.of_subset Set.Subset.rfl).union hp).mono Set.Subset.rfl Set.Subset.rfl (by omega)
    let InvA (t : ℕ) : Set (Sig (nIn k r m)) :=
      baseInputSigs k r m ∪ Set.range (fun j : Fin k => fun x => sweepAfterA hk hr x sd t j)
    have hstepA : ∀ t < hOf k, Extends (nIn k r m) (InvA t) (InvA (t + 1)) (22 * k * r + 4 * k + 4) := by
      intro t ht
      have hfold_eq : ∀ x : Fin (nIn k r m) → Bool, sweepAfterA hk hr x sd (t + 1) = sweepStepA hk hr x t (sweepAfterA hk hr x sd t) := by
        intro x; unfold sweepAfterA; rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      let wCur : Fin k → Sig (nIn k r m) := fun j x => sweepAfterA hk hr x sd t j
      let sVal := k - 1 - t
      let pivVal := sVal - (2 * r - 2)
      by_cases hpiv : 3 * r - 1 + extraOf k r ≤ pivVal ∧ pivVal < k
      · have hnlf := Extends.stateNoLastFeedV_sig hk (by omega) false wCur (fun j x => inLeft x j)
          (fun j => inLeft_mem_base j)
        let bitSig : Sig (nIn k r m) := fun x =>
          xor (stateNoLastFeedV hk r (schedVec x) false (fun i => wCur i x) (inLeft x) ⟨sVal, by omega⟩)
              (inA x ⟨sVal - zOf k, by unfold hOf zOf at *; omega⟩)
        have hxor : Extends (nIn k r m) (InvA t ∪ Set.range (fun j : Fin k => fun x =>
            stateNoLastFeedV hk r (schedVec x) false (fun i => wCur i x) (inLeft x) j)) {bitSig} 4 :=
          Extends.add_xor (Or.inr ⟨⟨sVal, by omega⟩, rfl⟩) (Or.inl (Or.inl (inA_mem_base _)))
        have hstep1 := hnlf.seq hxor
        refine ((Extends.of_subset Set.Subset.rfl).union hstep1).mono Set.Subset.rfl ?_ (by omega)
        rintro z (hb | ⟨j, rfl⟩)
        · exact Or.inl (Or.inl hb)
        · by_cases hjeq : j.val = pivVal
          · right
            have heq : (fun x => sweepAfterA hk hr x sd (t + 1) j) = bitSig := by
              funext x; rw [hfold_eq]; unfold sweepStepA
              have hku' : uOf r < k := by omega
              dsimp only [sVal, pivVal] at hpiv hjeq
              rw [dif_pos ht, dif_pos hku', dif_pos hpiv, if_pos hjeq]
            dsimp only; rw [heq]; rfl
          · left; right
            refine ⟨j, ?_⟩
            funext x; dsimp only [wCur]; rw [hfold_eq]; unfold sweepStepA
            have hku' : uOf r < k := by omega
            dsimp only [sVal, pivVal] at hpiv hjeq
            rw [dif_pos ht, dif_pos hku', dif_pos hpiv, if_neg hjeq]
      · refine (Extends.of_subset (S := InvA t) (T := InvA (t + 1)) ?_).mono Set.Subset.rfl Set.Subset.rfl (by omega)
        rintro z (hb | ⟨j, rfl⟩)
        · exact Or.inl hb
        · right; refine ⟨j, ?_⟩; funext x; dsimp only; rw [hfold_eq]; unfold sweepStepA
          have hku' : uOf r < k := by omega
          dsimp only [sVal, pivVal] at hpiv
          simp only [ht, hku', hpiv, ↓reduceDIte]
    have hfoldA := Extends.fold_nat_const (hOf k) InvA (22 * k * r + 4 * k + 4) hstepA
    let InvB (t : ℕ) : Set (Sig (nIn k r m)) :=
      baseInputSigs k r m ∪ Set.range (fun j : Fin k => fun x => sweepAfterB hk hr x sd t j)
    have hstepB : ∀ t < r + 3, Extends (nIn k r m) (InvB t) (InvB (t + 1)) (22 * k * r + 4 * k + 4) := by
      intro t _
      have hfold_eq : ∀ x : Fin (nIn k r m) → Bool, sweepAfterB hk hr x sd (t + 1) = sweepStepB hk hr x t (sweepAfterB hk hr x sd t) := by
        intro x; unfold sweepAfterB; rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      let wCur : Fin k → Sig (nIn k r m) := fun j x => sweepAfterB hk hr x sd t j
      let sStart := min (k - 1) (zOf k + r + 2)
      let sVal := sStart - t
      let pivVal := sVal - (3 * r + 1)
      by_cases hcond : t ≤ sStart - zOf k ∧ 3 * r + 1 ≤ sVal ∧
          3 * r - 1 + extraOf k r ≤ pivVal ∧ pivVal + 2 * r - 1 ≤ zOf k
      · rcases hcond with ⟨htle, hs, hpiv1, hpiv2⟩
        have hnlf := Extends.stateNoLastFeedV_sig hk (by omega) true wCur (fun j x => inRight x j)
          (fun j => inRight_mem_base j)
        let bitSig : Sig (nIn k r m) := fun x =>
          xor (stateNoLastFeedV hk r (schedVec x) true (fun i => wCur i x) (inRight x) ⟨sVal, by omega⟩)
              (inB x ⟨sVal - zOf k, by unfold hOf zOf at *; dsimp only [sVal, sStart] at *; omega⟩)
        have hxor : Extends (nIn k r m) (InvB t ∪ Set.range (fun j : Fin k => fun x =>
            stateNoLastFeedV hk r (schedVec x) true (fun i => wCur i x) (inRight x) j)) {bitSig} 4 :=
          Extends.add_xor (Or.inr ⟨⟨sVal, by omega⟩, rfl⟩) (Or.inl (Or.inl (inB_mem_base _)))
        have hstep1 := hnlf.seq hxor
        refine ((Extends.of_subset Set.Subset.rfl).union hstep1).mono Set.Subset.rfl ?_ (by omega)
        rintro z (hb | ⟨j, rfl⟩)
        · exact Or.inl (Or.inl hb)
        · by_cases hjeq : j.val = pivVal
          · right
            have heq : (fun x => sweepAfterB hk hr x sd (t + 1) j) = bitSig := by
              funext x; rw [hfold_eq]; unfold sweepStepB
              have hku' : uOf r < k := by omega
              have hpiv : 3 * r - 1 + extraOf k r ≤ pivVal ∧ pivVal + 2 * r - 1 ≤ zOf k := ⟨hpiv1, hpiv2⟩
              dsimp only [sStart, sVal, pivVal] at htle hs hpiv hjeq
              rw [dif_pos hku', dif_pos htle, dif_pos hs, dif_pos hpiv, if_pos hjeq]
            dsimp only; rw [heq]; rfl
          · left; right; refine ⟨j, ?_⟩
            funext x; dsimp only [wCur]; rw [hfold_eq]; unfold sweepStepB
            have hku' : uOf r < k := by omega
            have hpiv : 3 * r - 1 + extraOf k r ≤ pivVal ∧ pivVal + 2 * r - 1 ≤ zOf k := ⟨hpiv1, hpiv2⟩
            dsimp only [sStart, sVal, pivVal] at htle hs hpiv hjeq
            rw [dif_pos hku', dif_pos htle, dif_pos hs, dif_pos hpiv, if_neg hjeq]
      · refine (Extends.of_subset (S := InvB t) (T := InvB (t + 1)) ?_).mono Set.Subset.rfl Set.Subset.rfl (by omega)
        rintro z (hb | ⟨j, rfl⟩)
        · exact Or.inl hb
        · right; refine ⟨j, ?_⟩; funext x; dsimp only; rw [hfold_eq]; unfold sweepStepB
          have hku' : uOf r < k := by omega
          rw [dif_pos hku']
          by_cases h1 : t ≤ sStart - zOf k
          · dsimp only [sStart] at h1; rw [dif_pos h1]
            by_cases h2 : 3 * r + 1 ≤ sVal
            · dsimp only [sStart, sVal] at h2; rw [dif_pos h2]
              have h3 : ¬ (3 * r - 1 + extraOf k r ≤ pivVal ∧ pivVal + 2 * r - 1 ≤ zOf k) := by
                intro h3; exact hcond ⟨h1, h2, h3.1, h3.2⟩
              dsimp only [sStart, sVal, pivVal] at h3; rw [dif_neg h3]
            · dsimp only [sStart, sVal] at h2; rw [dif_neg h2]
          · dsimp only [sStart] at h1; rw [dif_neg h1]
    have hfoldB := Extends.fold_nat_const (r + 3) InvB (22 * k * r + 4 * k + 4) hstepB
    have hAB : InvA (hOf k) = InvB 0 := by rfl
    rw [hAB] at hfoldA
    have hall := (hinit.seq (hfoldA.mono Set.subset_union_right Set.Subset.rfl le_rfl)).seq
      (hfoldB.mono Set.subset_union_right Set.Subset.rfl le_rfl)
    refine hall.mono Set.Subset.rfl Set.subset_union_right ?_
    ring_nf; omega

lemma Extends.perSeed_sig {k r m : ℕ} (hk : 0 < k) (hr : 4 ≤ r)
    (sd : Fin (seedLen k r) → Bool) :
    Extends (nIn k r m) (baseInputSigs k r m)
      (Set.range (fun j : Fin k => fun x => sweepW0 hk hr x sd j) ∪
       {fun x => okSeed hk hr x sd} ∪
       Set.range (fun i : Fin m => fun x => seedRhs hk hr x sd i))
      ((if k ≤ uOf r then k else (hOf k + (r + 3)) * (22 * k * r + 4 * k + 4) + k) +
        (44 * k * r + 20 * k + 5) + m * (5 * k + 5)) := by
  let wSig : Fin k → Sig (nIn k r m) := fun j x => sweepW0 hk hr x sd j
  have hw := Extends.sweepW0_sig (m := m) hk hr sd
  -- okSeed from Base ∪ range wSig
  let S1 := baseInputSigs k r m ∪ Set.range wSig
  have hok : Extends (nIn k r m) S1 {fun x => okSeed hk hr x sd} (44 * k * r + 20 * k + 5) := by
    let stF : Fin k → Sig (nIn k r m) := fun j x => stateV hk r (schedVec x) false (fun i => wSig i x) (inLeft x) j
    let stT : Fin k → Sig (nIn k r m) := fun j x => stateV hk r (schedVec x) true (fun i => wSig i x) (inRight x) j
    have hF : Extends (nIn k r m) S1 (Set.range stF) (4 * k + r * (22 * k)) :=
      Extends.stateVSteps_sig hk false wSig (fun j x => inLeft x j) (fun j => inLeft_mem_base j) r le_rfl
    have hT : Extends (nIn k r m) S1 (Set.range stT) (4 * k + r * (22 * k)) :=
      Extends.stateVSteps_sig hk true wSig (fun j x => inRight x j) (fun j => inRight_mem_base j) r le_rfl
    let eqA (i : Fin (hOf k)) : Sig (nIn k r m) := fun x =>
      stF ⟨zOf k + i.val, by unfold hOf zOf; omega⟩ x == inA x i
    let eqB (i : Fin (hOf k)) : Sig (nIn k r m) := fun x =>
      stT ⟨zOf k + i.val, by unfold hOf zOf; omega⟩ x == inB x i
    let S2 := S1 ∪ (Set.range stF ∪ Set.range stT)
    have heqA : Extends (nIn k r m) S2 (Set.range eqA) (hOf k * 5) :=
      Extends.add_range_fin (fun i => Extends.add_beq (Or.inr (Or.inl ⟨_, rfl⟩)) (Or.inl (Or.inl (inA_mem_base i))))
    have heqB : Extends (nIn k r m) S2 (Set.range eqB) (hOf k * 5) :=
      Extends.add_range_fin (fun i => Extends.add_beq (Or.inr (Or.inr ⟨_, rfl⟩)) (Or.inl (Or.inl (inB_mem_base i))))
    let allA : Sig (nIn k r m) := fun x => (List.finRange (hOf k)).all (fun i => eqA i x)
    let allB : Sig (nIn k r m) := fun x => (List.finRange (hOf k)).all (fun i => eqB i x)
    have haA : Extends (nIn k r m) (S2 ∪ (Set.range eqA ∪ Set.range eqB)) {allA} (hOf k + 1) :=
      Extends.add_all_fin eqA (fun i => Or.inr (Or.inl ⟨i, rfl⟩))
    have haB : Extends (nIn k r m) (S2 ∪ (Set.range eqA ∪ Set.range eqB)) {allB} (hOf k + 1) :=
      Extends.add_all_fin eqB (fun i => Or.inr (Or.inr ⟨i, rfl⟩))
    have hand : Extends (nIn k r m) ((S2 ∪ (Set.range eqA ∪ Set.range eqB)) ∪ ({allA} ∪ {allB}))
        {fun x => okSeed hk hr x sd} 1 :=
      Extends.add_and (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl))
    have hcomb := ((hF.union hT).seq ((heqA.union heqB).seq ((haA.union haB).seq hand)))
    refine hcomb.mono Set.Subset.rfl Set.Subset.rfl ?_
    have hh : 2 * hOf k ≤ k + 1 := by unfold hOf; omega
    nlinarith
  -- seedRhs from S1
  have hrhs : Extends (nIn k r m) S1 (Set.range (fun i : Fin m => fun x => seedRhs hk hr x sd i))
      (m * (5 * k + 5)) := by
    have hp := Extends.add_range_fin (S := S1)
      (f := fun i : Fin m => fun x => seedRhs hk hr x sd i) (c := 5 * k + 5) (fun i => by
        let prod (j : Fin k) : Sig (nIn k r m) := fun x => wSig j x && inMat x i j
        have hpr : Extends (nIn k r m) S1 (Set.range prod) k := by
          simpa [mul_one] using Extends.add_range_fin (S := S1) (f := prod) (c := 1)
            (fun j => Extends.add_and (Or.inr ⟨j, rfl⟩) (Or.inl (inMat_mem_base i j)))
        have hxf : Extends (nIn k r m) (S1 ∪ Set.range prod)
            {fun x => (List.finRange k).foldl (fun acc j => xor acc (prod j x)) false} (4 * k + 1) :=
          Extends.add_xor_fin prod (fun j => Or.inr ⟨j, rfl⟩)
        have hxr : Extends (nIn k r m) (S1 ∪
            {fun x => (List.finRange k).foldl (fun acc j => xor acc (prod j x)) false})
            {fun x => seedRhs hk hr x sd i} 4 :=
          Extends.add_xor (Or.inl (Or.inl (inRhs_mem_base i))) (Or.inr rfl)
        exact ((hpr.seq hxf).seq hxr).mono Set.Subset.rfl Set.Subset.rfl (by omega))
    exact hp
  have hall := hw.trans ((hok.union hrhs).mono Set.Subset.rfl Set.Subset.rfl le_rfl)
  refine hall.mono Set.Subset.rfl ?_ (by omega)
  rintro z ((h1 | h2) | h3)
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr h3)

def sdOfIdx {S : ℕ} (idx : Fin (2 ^ S)) : Fin S → Bool :=
  fun i => idx.val.testBit i.val

lemma card_filter_seed_eq {S : ℕ} (P : (Fin S → Bool) → Bool) :
    (Finset.univ.filter (fun sd : Fin S → Bool => P sd = true)).card =
    (Finset.univ.filter (fun idx : Fin (2 ^ S) => P (sdOfIdx idx) = true)).card := by
  refine Finset.card_bij
    (fun sd _ => ⟨natOfBits sd, natOfBits_lt sd⟩)
    (fun sd hsd => ?_) (fun sd₁ _ sd₂ _ heq => ?_) (fun idx hidx => ?_)
  · have hP := (Finset.mem_filter.mp hsd).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    have hsd_eq : sdOfIdx ⟨natOfBits sd, natOfBits_lt sd⟩ = sd :=
      funext (natOfBits_testBit sd)
    rwa [hsd_eq]
  · have hv : natOfBits sd₁ = natOfBits sd₂ := Fin.mk.inj heq
    funext i; rw [← natOfBits_testBit sd₁ i, ← natOfBits_testBit sd₂ i, hv]
  · refine ⟨sdOfIdx idx, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hidx).2⟩, ?_⟩
    apply Fin.ext; dsimp only [sdOfIdx]; exact natOfBits_of_testBit idx.val idx.isLt

lemma Extends.colTab_and_nullOH {k r m : ℕ} (b : ℕ) (hb : b ≤ k) :
    Extends (nIn k r m) (baseInputSigs k r m)
      (ptabBits (fun x => colTab x b) ∪
       Set.range (fun d : Fin (k + 1) => fun x => decide (nullityOf x b = d.val)))
      ((m + m * m + 1) + k * (13 * m * m + 3 * m) + (4 * (m + 1) * (m + 1) + 2)) := by
  let Base := baseInputSigs k r m
  have hf : Extends (nIn k r m) Base {fun _ => false} 1 := Extends.add_const false
  have hemp : Extends (nIn k r m) Base (ptabBits (fun x : Fin (nIn k r m) → Bool => colTabSteps x b 0)) (m + m * m) :=
    (Extends.ptab_empty (n := nIn k r m) (N := m)).mono (Set.empty_subset _) Set.Subset.rfl le_rfl
  let Inv (t : ℕ) : Set (Sig (nIn k r m)) :=
    (Base ∪ {fun _ => false}) ∪ ptabBits (fun x => colTabSteps x b t)
  have hstart : Extends (nIn k r m) Base (Inv 0) (m + m * m + 1) :=
    (((Extends.of_subset Set.Subset.rfl).union hf).union hemp).mono Set.Subset.rfl Set.Subset.rfl (by omega)
  have hstep : ∀ t < k, Extends (nIn k r m) (Inv t) (Inv (t + 1)) (13 * m * m + 3 * m) := by
    intro t ht
    have hcv_sub : Set.range (fun i : Fin m => fun x => colVec x b ⟨t, ht⟩ i) ⊆ Base ∪ {fun _ => false} := by
      rintro _ ⟨i, rfl⟩
      by_cases hfb : freeBelow k r b ⟨t, ht⟩ = true
      · left; have : (fun x : Fin (nIn k r m) → Bool => colVec x b ⟨t, ht⟩ i) = fun x => inMat x i ⟨t, ht⟩ := by
          funext x; simp [colVec, hfb]
        dsimp only; rw [this]; exact inMat_mem_base i ⟨t, ht⟩
      · right; funext x; simp [colVec, hfb]
    have hins := Extends.ptab_insert (n := nIn k r m) (N := m)
      (fun x : Fin (nIn k r m) → Bool => colTabSteps x b t)
      (fun (i : Fin m) (x : Fin (nIn k r m) → Bool) => colVec x b ⟨t, ht⟩ i)
    have hins' : Extends (nIn k r m) (Inv t) (ptabBits (fun x => colTabSteps x b (t + 1))) (13 * m * m + 3 * m) := by
      have heq : (fun x : Fin (nIn k r m) → Bool => (colTabSteps x b t).insert (colVec x b ⟨t, ht⟩)) =
          fun x => colTabSteps x b (t + 1) := by funext x; simp [colTabSteps, ht]
      rw [heq] at hins
      exact hins.mono (by rintro z (h | h); exact Or.inr h; exact Or.inl (hcv_sub h)) Set.Subset.rfl le_rfl
    exact ((Extends.of_subset Set.subset_union_left).union hins').mono Set.Subset.rfl Set.Subset.rfl (by omega)
  have hfold := Extends.fold_nat_const k Inv (13 * m * m + 3 * m) hstep
  have htab := hstart.seq (hfold.mono Set.subset_union_right Set.Subset.rfl le_rfl)
  -- Now popCountOH of (colTab x b).hasPiv!
  have hpop : Extends (nIn k r m) (Inv k)
      (Set.range (fun p : Fin (m + 1) => fun x => decide (popCount (colTab x b).hasPiv = p.val)))
      (4 * (m + 1) * (m + 1) + 2) :=
    (Extends.popCountOH (fun i x => (colTab x b).hasPiv i)).mono
      (fun _ h => Or.inr (Or.inl h)) Set.Subset.rfl le_rfl
  have hcomb := htab.trans (hpop.mono Set.subset_union_right Set.Subset.rfl le_rfl)
  refine hcomb.mono Set.Subset.rfl ?_ (by omega)
  rintro z (htab_z | ⟨d, rfl⟩)
  · exact Or.inl (Or.inr htab_z)
  · by_cases hle : d.val ≤ freeBelowCard k r b ∧ freeBelowCard k r b - d.val ≤ m
    · right
      refine ⟨⟨freeBelowCard k r b - d.val, by omega⟩, ?_⟩
      funext x
      have hpop_le : popCount (colTab x b).hasPiv ≤ freeBelowCard k r b := (colTab_spec x b).2.2.1
      unfold nullityOf
      dsimp only
      by_cases heq : popCount (colTab x b).hasPiv = freeBelowCard k r b - d.val
      · rw [decide_eq_true heq, decide_eq_true (by omega)]
      · rw [decide_eq_false heq, decide_eq_false (by omega)]
    · left; left; right
      funext x
      have hpop_le : popCount (colTab x b).hasPiv ≤ freeBelowCard k r b := (colTab_spec x b).2.2.1
      have hpop_m : popCount (colTab x b).hasPiv ≤ m := popCount_le _
      unfold nullityOf
      dsimp only
      exact decide_eq_false (by omega)

lemma Extends.linOk_sig {k r m : ℕ} (b : ℕ) (y : Fin m → Sig (nIn k r m)) :
    Extends (nIn k r m) (ptabBits (fun x => colTab x b) ∪ Set.range y)
      {fun x => linOk x b (fun i => y i x)}
      (6 * m * m + 2 * m + 1) := by
  let red : Fin m → Sig (nIn k r m) := fun i x => (colTab x b).reduce (fun j => y j x) i
  have hred := Extends.ptab_reduce (fun x => colTab x b) y
  let nred : Fin m → Sig (nIn k r m) := fun i x => !red i x
  have hnred : Extends (nIn k r m) ((ptabBits (fun x => colTab x b) ∪ Set.range y) ∪ Set.range red)
      (Set.range nred) m := by
    simpa [mul_one] using Extends.add_range_fin (f := nred) (c := 1)
      (fun i => Extends.add_not (Or.inr ⟨i, rfl⟩))
  have hall : Extends (nIn k r m) ((ptabBits (fun x => colTab x b) ∪ Set.range y) ∪ Set.range nred)
      {fun x => linOk x b (fun i => y i x)} (m + 1) :=
    Extends.add_all_fin nred (fun i => Or.inr ⟨i, rfl⟩)
  exact ((hred.seq hnred).seq hall).mono Set.Subset.rfl Set.Subset.rfl (by omega)

def precompSet {k r m : ℕ} (hk : 0 < k) (hr : 4 ≤ r) : Set (Sig (nIn k r m)) :=
  baseInputSigs k r m ∪
  (⋃ idx : Fin (2 ^ (seedLen k r)),
    Set.range (fun j : Fin k => fun x => sweepW0 hk hr x (sdOfIdx idx) j) ∪
    {fun x => okSeed hk hr x (sdOfIdx idx)} ∪
    Set.range (fun i : Fin m => fun x => seedRhs hk hr x (sdOfIdx idx) i)) ∪
  (⋃ b : Fin (k + 1),
    ptabBits (fun x => colTab x b.val) ∪
    Set.range (fun d : Fin (k + 1) => fun x => decide (nullityOf x b.val = d.val)))

lemma mem_precomp_base {k r m : ℕ} (hk : 0 < k) (hr : 4 ≤ r) {z : Sig (nIn k r m)}
    (hz : z ∈ baseInputSigs k r m) : z ∈ precompSet hk hr :=
  Or.inl (Or.inl hz)

lemma mem_precomp_sweep {k r m : ℕ} (hk : 0 < k) (hr : 4 ≤ r)
    (idx : Fin (2 ^ (seedLen k r))) (j : Fin k) :
    (fun x : Fin (nIn k r m) → Bool => sweepW0 hk hr x (sdOfIdx idx) j) ∈ precompSet hk hr := by
  unfold precompSet
  exact Or.inl (Or.inr (Set.mem_iUnion.mpr ⟨idx, Or.inl (Or.inl ⟨j, rfl⟩)⟩))

lemma mem_precomp_ok {k r m : ℕ} (hk : 0 < k) (hr : 4 ≤ r)
    (idx : Fin (2 ^ (seedLen k r))) :
    (fun x : Fin (nIn k r m) → Bool => okSeed hk hr x (sdOfIdx idx)) ∈ precompSet hk hr := by
  unfold precompSet
  exact Or.inl (Or.inr (Set.mem_iUnion.mpr ⟨idx, Or.inl (Or.inr rfl)⟩))

lemma mem_precomp_rhs {k r m : ℕ} (hk : 0 < k) (hr : 4 ≤ r)
    (idx : Fin (2 ^ (seedLen k r))) (i : Fin m) :
    (fun x : Fin (nIn k r m) → Bool => seedRhs hk hr x (sdOfIdx idx) i) ∈ precompSet hk hr := by
  unfold precompSet
  exact Or.inl (Or.inr (Set.mem_iUnion.mpr ⟨idx, Or.inr ⟨i, rfl⟩⟩))

lemma mem_precomp_tab {k r m : ℕ} (hk : 0 < k) (hr : 4 ≤ r)
    (b : Fin (k + 1)) {z : Sig (nIn k r m)} (hz : z ∈ ptabBits (fun x => colTab x b.val)) :
    z ∈ precompSet hk hr := by
  unfold precompSet
  exact Or.inr (Set.mem_iUnion.mpr ⟨b, Or.inl hz⟩)

lemma mem_precomp_null {k r m : ℕ} (hk : 0 < k) (hr : 4 ≤ r)
    (b : Fin (k + 1)) (d : Fin (k + 1)) :
    (fun x : Fin (nIn k r m) → Bool => decide (nullityOf x b.val = d.val)) ∈ precompSet hk hr := by
  unfold precompSet
  exact Or.inr (Set.mem_iUnion.mpr ⟨b, Or.inr ⟨d, rfl⟩⟩)

lemma Extends.totalCountW_sig {k r m : ℕ} (hk : 0 < k) (hr : 4 ≤ r) :
    Extends (nIn k r m) (precompSet hk hr)
      (wordBits (fun x => totalCountW hk hr x))
      (2 ^ (seedLen k r) * (6 * m * m + 2 * m + 14 * (k + 1) + 3) +
        (2 * (k + 1) * (k + 1) + 3 * (k + 1) + 2)) := by
  let S := seedLen k r
  let pred (idx : Fin (2 ^ S)) : Sig (nIn k r m) := fun x =>
    okSeed hk hr x (sdOfIdx idx) && linOk x k (seedRhs hk hr x (sdOfIdx idx))
  have hpreds : Extends (nIn k r m) (precompSet hk hr) (Set.range pred)
      (2 ^ S * (6 * m * m + 2 * m + 2)) := by
    have hp := Extends.add_range_fin (S := precompSet hk hr) (f := pred) (c := 6 * m * m + 2 * m + 2)
      (fun idx => by
        have hlin := (Extends.linOk_sig (k := k) (r := r) (m := m) k (fun i x => seedRhs hk hr x (sdOfIdx idx) i)).mono
          (by
            rintro z (h | ⟨i, rfl⟩)
            · exact mem_precomp_tab hk hr ⟨k, by omega⟩ h
            · exact mem_precomp_rhs hk hr idx i) Set.Subset.rfl le_rfl
        have hand := Extends.add_and (n := nIn k r m)
          (S := precompSet (m := m) hk hr ∪ {fun x => linOk x k (seedRhs hk hr x (sdOfIdx idx))})
          (Or.inl (mem_precomp_ok (m := m) hk hr idx)) (Or.inr rfl)
        exact (hlin.seq hand).mono Set.Subset.rfl Set.Subset.rfl (by omega))
    exact hp
  let sumW : WordSig (nIn k r m) (k + 1) := fun x =>
    ((Finset.univ.filter (fun idx : Fin (2 ^ S) => pred idx x = true)).card : ZMod (2 ^ (k + 1)))
  have hsum : Extends (nIn k r m) (precompSet hk hr ∪ Set.range pred) (wordBits sumW)
      (2 ^ S * (14 * (k + 1) + 1) + (k + 1) + 1) :=
    (Extends.word_sum_bools (B := k + 1) (by omega) pred).mono Set.subset_union_right Set.Subset.rfl le_rfl
  have hshl_lt : ∀ x : Fin (nIn k r m) → Bool, nullityOf x k < k + 1 := fun x => by
    unfold nullityOf freeBelowCard
    have : (Finset.univ.filter (fun j : Fin k => freeBelow k r k j = true)).card ≤ k :=
      (Finset.card_filter_le _ _).trans (by simp)
    omega
  have hshl : Extends (nIn k r m) (precompSet hk hr ∪ wordBits sumW)
      (wordBits (fun x => (((sumW x).val * 2 ^ (nullityOf x k) : ℕ) : ZMod (2 ^ (k + 1)))))
      (2 * (k + 1) * (k + 1) + 2 * (k + 1) + 1) :=
    (Extends.word_shl_oh sumW (fun x => nullityOf x k) hshl_lt).mono (by
      rintro z (h | ⟨d, rfl⟩)
      · exact Or.inr h
      · exact Or.inl (mem_precomp_null hk hr ⟨k, by omega⟩ d)) Set.Subset.rfl le_rfl
  have hEq : (fun x => (((sumW x).val * 2 ^ (nullityOf x k) : ℕ) : ZMod (2 ^ (k + 1)))) =
      fun x => totalCountW hk hr x := by
    funext x; unfold totalCountW; dsimp only [sumW]
    rw [card_filter_seed_eq (fun sd => okSeed hk hr x sd && linOk x k (seedRhs hk hr x sd))]
  rw [hEq] at hshl
  exact ((hpreds.seq hsum).seq hshl).mono Set.Subset.rfl Set.Subset.rfl (by
    dsimp only [S]; ring_nf; omega)

def bsStateSigs {k r m : ℕ} (st : (Fin (nIn k r m) → Bool) → BSState k) : Set (Sig (nIn k r m)) :=
  Set.range (fun j : Fin k => fun x => (st x).key j) ∪ wordBits (fun x => (st x).rem)

lemma Extends.bsStep_sig {k r m : ℕ} (hk : 0 < k) (hr : 4 ≤ r) (b : Fin k)
    (st : (Fin (nIn k r m) → Bool) → BSState k) :
    Extends (nIn k r m) (precompSet hk hr ∪ bsStateSigs st)
      (bsStateSigs (fun x => bsStep hk hr x b (st x)))
      (m * (5 * k + 3) +
        2 ^ (seedLen k r) * (6 * k + 6 * m * m + 6 * m + 14 * (k + 1) + 6) +
        (2 * (k + 1) * (k + 1) + 22 * (k + 1) + 5)) := by
  let S := seedLen k r
  let Base := precompSet hk hr ∪ bsStateSigs st
  have hfalse : Extends (nIn k r m) Base {fun _ => false} 1 := Extends.add_const false
  have htrue : Extends (nIn k r m) Base {fun _ => true} 1 := Extends.add_const true
  let S0 := Base ∪ ({fun _ => false} ∪ {fun _ => true})
  let key0 : Fin k → Sig (nIn k r m) := fun j x => if j = b then false else (st x).key j
  have hkey0_mem : ∀ j : Fin k, key0 j ∈ S0 := fun j => by
    by_cases hjb : j = b
    · have : key0 j = fun _ => false := by funext x; simp [key0, hjb]
      rw [this]; exact Or.inr (Or.inl rfl)
    · have : key0 j = fun x => (st x).key j := by funext x; simp [key0, hjb]
      rw [this]; exact Or.inl (Or.inr (Or.inl ⟨j, rfl⟩))
  -- 1. topFreeRhs x b.val (key0 · x) i
  let tfr : Fin m → Sig (nIn k r m) := fun i x => topFreeRhs x b.val (fun j => key0 j x) i
  have htfr : Extends (nIn k r m) S0 (Set.range tfr) (m * (5 * k + 1)) := by
    have hp := Extends.add_range_fin (S := S0) (f := tfr) (c := 5 * k + 1) (fun i => by
      let term (j : Fin k) : Sig (nIn k r m) := fun x =>
        if isFree k r j && decide (b.val ≤ j.val) && key0 j x then inMat x i j else false
      have hterm : Extends (nIn k r m) S0 (Set.range term) k := by
        simpa [mul_one] using Extends.add_range_fin (S := S0) (f := term) (c := 1) (fun j => by
          by_cases hc : isFree k r j = true ∧ b.val ≤ j.val
          · have heq : term j = fun x => key0 j x && inMat x i j := by
              funext x; simp only [term, hc.1, hc.2, decide_true, Bool.and_self, Bool.true_and]
              cases key0 j x <;> cases inMat x i j <;> rfl
            rw [heq]; exact Extends.add_and (hkey0_mem j) (Or.inl (Or.inl (Or.inl (Or.inl (inMat_mem_base i j)))))
          · have heq : term j = fun _ => false := by
              funext x
              have hf : (isFree k r j && decide (b.val ≤ j.val)) = false := by
                cases h1 : isFree k r j <;> simp_all
              dsimp only [term]; rw [hf, Bool.false_and]; rfl
            rw [heq]; exact (Extends.of_subset (by intro z hz; simp at hz; subst hz; exact Or.inr (Or.inl rfl))).mono
              Set.Subset.rfl Set.Subset.rfl (by omega))
      have hxf : Extends (nIn k r m) (S0 ∪ Set.range term) {tfr i} (4 * k + 1) :=
        Extends.add_xor_fin term (fun j => Or.inr ⟨j, rfl⟩)
      exact (hterm.seq hxf).mono Set.Subset.rfl Set.Subset.rfl (by omega))
    exact hp
  -- 2. Per-seed predicate pred idx
  let pred (idx : Fin (2 ^ S)) : Sig (nIn k r m) := fun x =>
    seedMatchTop hk hr x b.val (fun j => key0 j x) (sdOfIdx idx) &&
    linOk x b.val (fun i => xor (seedRhs hk hr x (sdOfIdx idx) i) (tfr i x))
  have hpreds : Extends (nIn k r m) (S0 ∪ Set.range tfr) (Set.range pred)
      (2 ^ S * (6 * k + 6 * m * m + 6 * m + 5)) := by
    let S1 := S0 ∪ Set.range tfr
    have hp := Extends.add_range_fin (S := S1) (f := pred) (c := 6 * k + 6 * m * m + 6 * m + 5)
      (fun idx => by
        -- 2a. seedMatchTop
        let bitOk (j : Fin k) : Sig (nIn k r m) := fun x =>
          !decide (b.val ≤ j.val) || isFree k r j || (sweepW0 hk hr x (sdOfIdx idx) j == key0 j x)
        have hbitOk : Extends (nIn k r m) S1 (Set.range bitOk) (5 * k) := by
          have := Extends.add_range_fin (S := S1) (f := bitOk) (c := 5) (fun j => by
            by_cases hc : b.val ≤ j.val ∧ isFree k r j = false
            · have heq : bitOk j = fun x => sweepW0 hk hr x (sdOfIdx idx) j == key0 j x := by
                funext x; dsimp only [bitOk]; rw [decide_eq_true hc.1, hc.2]; rfl
              rw [heq]
              exact Extends.add_beq
                (Or.inl (Or.inl (Or.inl (mem_precomp_sweep hk hr idx j))))
                (Or.inl (hkey0_mem j))
            · have heq : bitOk j = fun _ => true := by
                funext x; unfold bitOk
                by_cases h1 : b.val ≤ j.val
                · have h2 : isFree k r j = true := by cases h : isFree k r j <;> simp_all
                  simp [h1, h2]
                · simp [h1]
              rw [heq]
              exact (Extends.of_subset (by intro z hz; simp at hz; subst hz; exact Or.inl (Or.inr (Or.inr rfl)))).mono
                Set.Subset.rfl Set.Subset.rfl (by omega))
          exact this.mono Set.Subset.rfl Set.Subset.rfl (by omega)
        have hallB : Extends (nIn k r m) (S1 ∪ Set.range bitOk)
            {fun x => (List.finRange k).all (fun j => bitOk j x)} (k + 1) :=
          Extends.add_all_fin bitOk (fun j => Or.inr ⟨j, rfl⟩)
        have hmt : Extends (nIn k r m) S1
            {fun x => seedMatchTop hk hr x b.val (fun j => key0 j x) (sdOfIdx idx)} (6 * k + 2) := by
          have hand := Extends.add_and (S := S1 ∪ {fun x => (List.finRange k).all (fun j => bitOk j x)})
            (Or.inl (Or.inl (Or.inl (Or.inl (mem_precomp_ok hk hr idx)))))
            (Or.inr rfl)
          exact ((hbitOk.seq hallB).seq hand).mono Set.Subset.rfl Set.Subset.rfl (by omega)
        -- 2b. xor seedRhs tfr + linOk
        let ytot : Fin m → Sig (nIn k r m) := fun i x => xor (seedRhs hk hr x (sdOfIdx idx) i) (tfr i x)
        have hytot : Extends (nIn k r m) S1 (Set.range ytot) (4 * m) := by
          have := Extends.add_range_fin (S := S1) (f := ytot) (c := 4) (fun i =>
            Extends.add_xor
              (Or.inl (Or.inl (Or.inl (mem_precomp_rhs hk hr idx i))))
              (Or.inr ⟨i, rfl⟩))
          exact this.mono Set.Subset.rfl Set.Subset.rfl (by omega)
        have hlin : Extends (nIn k r m) (S1 ∪ Set.range ytot)
            {fun x => linOk x b.val (fun i => ytot i x)} (6 * m * m + 2 * m + 1) :=
          (Extends.linOk_sig b.val ytot).mono (by
            rintro z (h | h)
            · exact Or.inl (Or.inl (Or.inl (Or.inl (mem_precomp_tab hk hr ⟨b.val, by omega⟩ h))))
            · exact Or.inr h) Set.Subset.rfl le_rfl
        have hlin' := hytot.seq hlin
        have hboth := hmt.union hlin'
        have hand2 : Extends (nIn k r m) (S1 ∪ ({fun x => seedMatchTop hk hr x b.val (fun j => key0 j x) (sdOfIdx idx)} ∪
            {fun x => linOk x b.val (fun i => ytot i x)})) {pred idx} 1 :=
          Extends.add_and (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl))
        exact (hboth.seq hand2).mono Set.Subset.rfl Set.Subset.rfl (by omega))
    exact hp
  -- 3. Sum + shift + sub_ge + mux!
  let sumW : WordSig (nIn k r m) (k + 1) := fun x =>
    ((Finset.univ.filter (fun idx : Fin (2 ^ S) => pred idx x = true)).card : ZMod (2 ^ (k + 1)))
  have hsum : Extends (nIn k r m) (S0 ∪ Set.range pred) (wordBits sumW)
      (2 ^ S * (14 * (k + 1) + 1) + (k + 1) + 1) :=
    (Extends.word_sum_bools (B := k + 1) (by omega) pred).mono Set.subset_union_right Set.Subset.rfl le_rfl
  have hshl_lt : ∀ x : Fin (nIn k r m) → Bool, nullityOf x b.val < k + 1 := fun x => by
    unfold nullityOf freeBelowCard
    have : (Finset.univ.filter (fun j : Fin k => freeBelow k r b.val j = true)).card ≤ k :=
      (Finset.card_filter_le _ _).trans (by simp)
    omega
  let c0W : WordSig (nIn k r m) (k + 1) := fun x => bsCntZeroW hk hr x b (st x).key
  have hshl : Extends (nIn k r m) (S0 ∪ wordBits sumW) (wordBits c0W)
      (2 * (k + 1) * (k + 1) + 2 * (k + 1) + 1) := by
    have h1 := (Extends.word_shl_oh sumW (fun x => nullityOf x b.val) hshl_lt).mono
      (S' := S0 ∪ wordBits sumW) (by
      rintro z (h | ⟨d, rfl⟩)
      · exact Or.inr h
      · exact Or.inl (Or.inl (Or.inl (mem_precomp_null hk hr ⟨b.val, by omega⟩ d))))
      Set.Subset.rfl le_rfl
    have heq : (fun x => (((sumW x).val * 2 ^ (nullityOf x b.val) : ℕ) : ZMod (2 ^ (k + 1)))) = c0W := by
      funext x; unfold c0W bsCntZeroW; dsimp only [sumW, pred, tfr, key0]
      rw [card_filter_seed_eq (fun sd =>
        seedMatchTop hk hr x b.val (fun j => if j = b then false else (st x).key j) sd &&
        linOk x b.val (fun i => xor (seedRhs hk hr x sd i)
          (topFreeRhs x b.val (fun j => if j = b then false else (st x).key j) i)))]
    rwa [heq] at h1
  let go1Sig : Sig (nIn k r m) := fun x => decide ((c0W x).val ≤ ((st x).rem).val)
  let diffW : WordSig (nIn k r m) (k + 1) := fun x => (st x).rem - c0W x
  have hsub : Extends (nIn k r m) (S0 ∪ wordBits c0W) ({go1Sig} ∪ wordBits diffW) (15 * (k + 1) + 1) :=
    (Extends.word_sub_ge (fun x => (st x).rem) c0W).mono (by
      rintro z (h | h)
      · exact Or.inl (Or.inl (Or.inr (Or.inr h)))
      · exact Or.inr h) Set.Subset.rfl le_rfl
  let rem' : WordSig (nIn k r m) (k + 1) := fun x => if go1Sig x then diffW x else (st x).rem
  have hmux : Extends (nIn k r m) (S0 ∪ ({go1Sig} ∪ wordBits diffW)) (wordBits rem') (4 * (k + 1)) :=
    (Extends.word_mux go1Sig diffW (fun x => (st x).rem)).mono (by
      rintro z ((h | h) | h)
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
      · exact Or.inl (Or.inl (Or.inr (Or.inr h)))) Set.Subset.rfl le_rfl
  have hstage1 := (hfalse.union htrue)
  have hstage2 := ((htfr.seq hpreds).seq hsum).seq hshl
  have hstage3 := hsub.trans (hmux.mono (by
    rintro z (h | h)
    · exact Or.inl (Or.inl h)
    · exact Or.inr h) Set.Subset.rfl le_rfl)
  have hall := hstage1.seq (hstage2.seq hstage3)
  refine ((Extends.of_subset Set.Subset.rfl).union hall).mono Set.Subset.rfl ?_ ?_
  · rintro z (⟨j, rfl⟩ | ⟨j, rfl⟩)
    · by_cases hjb : j = b
      · right; left; left
        have : (fun x => (bsStep hk hr x b (st x)).key j) = go1Sig := by
          funext x; simp [bsStep, hjb, go1Sig, c0W]
        dsimp only; rw [this]; rfl
      · left; right; left
        refine ⟨j, ?_⟩; funext x; simp [bsStep, hjb]
    · right; right; exact ⟨j, rfl⟩
  · dsimp only [S]; ring_nf; omega

/-! ### Part 7: `k = 0` Case & Final Theorem `PEqualNP.Outside.L_meta_25708` -/

lemma solve_k_zero (r m : ℕ) (hr : 4 ≤ r) :
    let k := 0
    let h := (k + 1) / 2
    let z := k - h
    let u := 5 * r - 3
    let extra := min (r - 2) (z - 6 * r)
    let seedWidth := min k u + extra
    let n := 2 * r * k + 3 * k + 2 * h + m * (k + 1)
    let bits := fun (len data : ℕ) => (List.range len).map (fun pos => data.testBit pos)
    let parity := fun (natWord : ℕ) => (List.range k).foldl
      (fun total bitPos => xor total (natWord.testBit bitPos)) false
    ∃ (C : Circuit)
      (countWire : Fin (k + 1) → Fin (n + C.size)) (keyWire : Fin k → Fin (n + C.size)),
      FanInTwo C ∧ ReadsBack n C ∧
      C.output < n + C.size ∧ C.size ≤ 1048576 * (k + m + 1) ^ 5 * (r + 1) * 2 ^ seedWidth ∧
      ∀ (schedule : ℕ → Fin (2 ^ k)) (leftName rightName : Fin (2 ^ k))
          (a b : Fin (2 ^ h)) (A : Fin m → Fin (2 ^ k)) (rhs : Fin m → Bool)
          (rank : Fin (2 ^ k)),
        let input := (List.range (2 * r)).flatMap (fun idx => bits k (schedule (idx + 1)).val) ++
          bits k leftName.val ++ bits k rightName.val ++ bits h a.val ++ bits h b.val ++
          (List.ofFn A).flatMap (fun entry => bits k entry.val) ++ List.ofFn rhs ++ bits k rank.val
        let solutions := (List.range (2 ^ k)).filter (fun w => decide (
          stateN k r schedule false w leftName.val >>> z = a.val ∧
          stateN k r schedule true w rightName.val >>> z = b.val ∧
          ∀ i : Fin m, parity (w &&& (A i).val) = rhs i))
        C.eval input = decide (rank.val < solutions.length) ∧
        (∀ j : Fin (k + 1), (C.wires input).getD (countWire j).val false = solutions.length.testBit j.val) ∧
        (∀ d : Fin k, (C.wires input).getD (keyWire d).val false =
          ((solutions.getD rank.val 0).testBit d.val)) := by
  intro k h z u extra seedWidth n bits parity
  have hn_eq : n = m := by dsimp only [n, k, h]; omega
  let Base : Set (Sig m) := Set.range (fun i : Fin m => fun x => x i)
  let notRhs : Fin m → Sig m := fun i x => !x i
  have hnot : Extends m Base (Set.range notRhs) m := by
    simpa [mul_one] using Extends.add_range_fin (S := Base) (f := notRhs) (c := 1)
      (fun i => Extends.add_not ⟨i, rfl⟩)
  let allZero : Sig m := fun x => (List.finRange m).all (fun i => !x i)
  have hall : Extends m (Base ∪ Set.range notRhs) {allZero} (m + 1) :=
    Extends.add_all_fin notRhs (fun i => Or.inr ⟨i, rfl⟩)
  have hext := hnot.seq hall
  obtain ⟨hF0, hB0, hsz0, hbase0⟩ := base_circuit m
  obtain ⟨C0, hF, hB, hsz, _, hout⟩ := hext ⟨[], 0⟩ hF0 hB0 (by rintro _ ⟨i, rfl⟩; exact hbase0 i)
  obtain ⟨wOut, hwOut⟩ := hout allZero rfl
  let C : Circuit := ⟨C0.gates, wOut.val⟩
  have hsz_eq : C.size = C0.size := rfl
  have hbound : C.size ≤ 1048576 * (k + m + 1) ^ 5 * (r + 1) * 2 ^ seedWidth := by
    have h1 : C.size ≤ 2 * m + 1 := by rw [hsz_eq]; omega
    have h2 : 1 ≤ 2 ^ seedWidth := Nat.one_le_pow _ _ (by decide)
    have h3 : m + 1 ≤ (k + m + 1) ^ 5 := by
      have : m + 1 ≤ (k + m + 1) ^ 1 := by dsimp only [k]; simp
      exact this.trans (Nat.pow_le_pow_right (by omega) (by decide))
    have h4 : 1 ≤ r + 1 := by omega
    have h5 : 1048576 * (m + 1) * 1 * 1 ≤ 1048576 * (k + m + 1) ^ 5 * (r + 1) * 2 ^ seedWidth :=
      Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left 1048576 h3) h4) h2
    omega
  refine ⟨C, fun _ => ⟨wOut.val, by rw [hn_eq, hsz_eq]; exact wOut.isLt⟩, fun d => d.elim0,
    hF, by rw [hn_eq]; exact hB, by rw [hn_eq, hsz_eq]; exact wOut.isLt, hbound, ?_⟩
  intro schedule leftName rightName a b A rhs rank input solutions
  have hinp : input = List.ofFn rhs := by
    have hflat : ∀ (l : List ℕ), l.flatMap (fun idx => bits 0 (schedule (idx + 1)).val) = [] := by
      intro l; induction l with | nil => rfl | cons _ _ ih => simp [bits, ih]
    have hflatA : ∀ (l : List (Fin (2 ^ 0))), l.flatMap (fun entry => bits 0 entry.val) = [] := by
      intro l; induction l with | nil => rfl | cons _ _ ih => simp [bits, ih]
    dsimp only [input, k, h]
    rw [hflat, hflatA]
    simp [bits]
  have hsol_len : solutions.length = if allZero rhs then 1 else 0 := by
    have hst : ∀ col name, stateN 0 r schedule col 0 name = 0 := by
      intro col name
      have h0 : ∀ t, (List.range t).foldl (fun v tick => stepN 0 r schedule col 0 v (tick + 1))
          (rotN 0 (if col then 3 else 1) 0 ^^^ name) = if t = 0 then (0 ^^^ name) else 0 := by
        intro t; induction t with
        | zero => simp [rotN]
        | succ t _ =>
          rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
          have hc0 : (schedule (if col then r + (t + 1) else t + 1)).val = 0 :=
            Nat.lt_one_iff.mp (by simpa [k] using (schedule (if col then r + (t + 1) else t + 1)).isLt)
          simp [stepN, chiN, rotN, hc0]
      have h1 := h0 r
      simp [show r ≠ 0 by omega] at h1
      exact h1
    have ha0 : a.val = 0 := Nat.lt_one_iff.mp (by simpa [h, k] using a.isLt)
    have hb0 : b.val = 0 := Nat.lt_one_iff.mp (by simpa [h, k] using b.isLt)
    dsimp only [solutions, k, z, parity]
    simp only [pow_zero, List.range_one, List.filter_cons, List.filter_nil, hst, ha0, hb0,
      Nat.zero_shiftRight, List.range_zero, List.foldl_nil, true_and]
    by_cases hall_f : ∀ i : Fin m, rhs i = false
    · have haT : allZero rhs = true := by
        simp only [allZero, List.all_eq_true, List.mem_finRange, true_implies, Bool.not_eq_true']
        exact hall_f
      simp [hall_f, haT]
    · have haF : allZero rhs = false := by
        rw [Bool.eq_false_iff]; intro hT
        apply hall_f; intro i
        simp only [allZero, List.all_eq_true, List.mem_finRange, true_implies, Bool.not_eq_true'] at hT
        exact hT i
      have hall_f' : ¬ ∀ i : Fin m, false = rhs i := fun H => hall_f (fun i => (H i).symm)
      simp only [haF, Bool.false_eq_true, ↓reduceIte, decide_eq_false hall_f', List.length_nil]
  have hrk0 : rank.val = 0 := Nat.lt_one_iff.mp (by simpa [k] using rank.isLt)
  have heval : (C.wires input).getD wOut.val false = allZero rhs := by
    rw [hinp]; exact hwOut rhs
  refine ⟨?_, ?_, fun d => d.elim0⟩
  · change (C.wires input).getD wOut.val false = decide (rank.val < solutions.length)
    rw [heval, hsol_len, hrk0]
    cases allZero rhs <;> decide
  · intro j
    have hj0 : j.val = 0 := by have := j.isLt; dsimp only [k] at this; omega
    dsimp only
    rw [heval, hsol_len, hj0]
    cases allZero rhs <;> decide

lemma size_bound_main (k r m : ℕ) (hk : 0 < k) (hr : 4 ≤ r) :
    let S := seedLen k r
    let perSeed := (if k ≤ uOf r then k else (hOf k + (r + 3)) * (22 * k * r + 4 * k + 4) + k) +
      (44 * k * r + 20 * k + 5) + m * (5 * k + 5)
    let perTab := (m + m * m + 1) + k * (13 * m * m + 3 * m) + (4 * (m + 1) * (m + 1) + 2)
    let cntCost := 2 ^ S * (6 * m * m + 2 * m + 14 * (k + 1) + 3) +
      (2 * (k + 1) * (k + 1) + 3 * (k + 1) + 2)
    let bsStepCost := m * (5 * k + 3) +
      2 ^ S * (6 * k + 6 * m * m + 6 * m + 14 * (k + 1) + 6) +
      (2 * (k + 1) * (k + 1) + 22 * (k + 1) + 5)
    let finalCost := (1 + (k + 1)) + (15 * (k + 1) + 2) + k
    2 ^ S * perSeed + (k + 1) * perTab + cntCost + k * bsStepCost + finalCost ≤
      1048576 * (k + m + 1) ^ 5 * (r + 1) * 2 ^ (seedWidthOf k r) := by
  intro S perSeed perTab cntCost bsStepCost finalCost
  set M := k + m + 1
  set R := r + 1
  set P := 2 ^ S
  have hM1 : 1 ≤ M := by omega
  have hR1 : 1 ≤ R := by omega
  have hP1 : 1 ≤ P := Nat.one_le_pow _ _ (by decide)
  have hP_le : P ≤ 2 ^ (seedWidthOf k r) :=
    Nat.pow_le_pow_right (by decide) (seedLen_le_seedWidth k r)
  have hM_le2 : M ≤ M ^ 2 := by rw [pow_two]; exact Nat.le_mul_self M
  have hM2_le3 : M ^ 2 ≤ M ^ 3 := by rw [pow_succ]; exact Nat.le_mul_of_pos_right _ hM1
  have hM3_le4 : M ^ 3 ≤ M ^ 4 := by rw [pow_succ]; exact Nat.le_mul_of_pos_right _ hM1
  have hM4_le5 : M ^ 4 ≤ M ^ 5 := by rw [pow_succ]; exact Nat.le_mul_of_pos_right _ hM1
  have hkM : k ≤ M := by omega
  have hmM : m ≤ M := by omega
  have hk1M : k + 1 ≤ M := by omega
  have hm1M : m + 1 ≤ M := by omega
  have hrR : r ≤ R := by omega
  have hperSeed : perSeed ≤ 200 * M ^ 3 * R := by
    have hsw : (if k ≤ uOf r then k else (hOf k + (r + 3)) * (22 * k * r + 4 * k + 4) + k) ≤
        100 * M ^ 2 * R := by
      split_ifs with hku
      · have h3 : k ≤ M ^ 2 * R := le_trans (le_trans hkM hM_le2) (Nat.le_mul_of_pos_right _ hR1)
        linarith
      · have hrk : r + 3 ≤ 2 * M := by unfold uOf at hku; omega
        have hhM : hOf k ≤ M := by unfold hOf; omega
        have hfac1 : hOf k + (r + 3) ≤ 3 * M := by omega
        have hfac2 : 22 * k * r + 4 * k + 4 ≤ 30 * M * R := by nlinarith
        have hprod := Nat.mul_le_mul hfac1 hfac2
        have hkm : k ≤ M ^ 2 * R := le_trans (le_trans hkM hM_le2) (Nat.le_mul_of_pos_right _ hR1)
        nlinarith
    have h2 : 44 * k * r + 20 * k + 5 ≤ 70 * M * R := by nlinarith
    have h3 : m * (5 * k + 5) ≤ 10 * M ^ 2 := by nlinarith [pow_two M]
    have h1 : 100 * M ^ 2 * R ≤ 100 * M ^ 3 * R :=
      Nat.mul_le_mul_right R (Nat.mul_le_mul_left 100 hM2_le3)
    have h2' : 70 * M * R ≤ 70 * M ^ 3 * R :=
      Nat.mul_le_mul_right R (Nat.mul_le_mul_left 70 (le_trans hM_le2 hM2_le3))
    have h3' : 10 * M ^ 2 ≤ 10 * M ^ 3 * R :=
      le_trans (Nat.mul_le_mul_left 10 hM2_le3) (Nat.le_mul_of_pos_right _ hR1)
    dsimp only [perSeed]; linarith
  have hperTab : (k + 1) * perTab ≤ 50 * M ^ 4 := by
    have h1 : perTab ≤ 50 * M ^ 3 := by
      have ha : m + m * m + 1 ≤ 3 * M ^ 2 := by nlinarith [pow_two M]
      have hb : k * (13 * m * m + 3 * m) ≤ 16 * M ^ 3 := by
        have : 13 * m * m + 3 * m ≤ 16 * M ^ 2 := by nlinarith [pow_two M]
        have := Nat.mul_le_mul hkM this
        nlinarith [pow_succ M 2]
      have hc : 4 * (m + 1) * (m + 1) + 2 ≤ 6 * M ^ 2 := by nlinarith [pow_two M]
      dsimp only [perTab]; linarith
    have hprod := Nat.mul_le_mul hk1M h1
    nlinarith [pow_succ M 3]
  have hcnt : cntCost ≤ 50 * M ^ 2 * P := by
    have h1 : 6 * m * m + 2 * m + 14 * (k + 1) + 3 ≤ 30 * M ^ 2 := by
      have hm2 : m * m ≤ M * M := Nat.mul_le_mul hmM hmM
      have h6 : 6 * m * m = 6 * (m * m) := by ring
      have hM12 : M ≤ M * M := Nat.le_mul_self M
      have hM2 : M ^ 2 = M * M := pow_two M
      omega
    have h2 : 2 * (k + 1) * (k + 1) + 3 * (k + 1) + 2 ≤ 10 * M ^ 2 := by
      have hk2 : (k + 1) * (k + 1) ≤ M * M := Nat.mul_le_mul hk1M hk1M
      have h2k : 2 * (k + 1) * (k + 1) = 2 * ((k + 1) * (k + 1)) := by ring
      have hM12 : M ≤ M * M := Nat.le_mul_self M
      have hM2 : M ^ 2 = M * M := pow_two M
      omega
    have h1' : P * (6 * m * m + 2 * m + 14 * (k + 1) + 3) ≤ 30 * M ^ 2 * P := by
      rw [mul_comm]; exact Nat.mul_le_mul_right P h1
    have h2' : 2 * (k + 1) * (k + 1) + 3 * (k + 1) + 2 ≤ 10 * M ^ 2 * P :=
      le_trans h2 (Nat.le_mul_of_pos_right _ hP1)
    have hadd := Nat.add_le_add h1' h2'
    have hsum_eq : 30 * M ^ 2 * P + 10 * M ^ 2 * P ≤ 50 * M ^ 2 * P := by
      have : 30 * M ^ 2 * P + 10 * M ^ 2 * P = 40 * (M ^ 2 * P) := by ring
      have : 50 * M ^ 2 * P = 50 * (M ^ 2 * P) := by ring
      omega
    exact le_trans hadd hsum_eq
  have hbs : k * bsStepCost ≤ 100 * M ^ 3 * P := by
    have h1 : bsStepCost ≤ 100 * M ^ 2 * P := by
      have hM2 : M ^ 2 = M * M := pow_two M
      have hM12 : M ≤ M * M := Nat.le_mul_self M
      have hmk : m * (5 * k + 3) ≤ 10 * M ^ 2 := by
        have : m * (5 * k + 3) ≤ M * (5 * M + 3 * M) := Nat.mul_le_mul hmM (by omega)
        have : M * (5 * M + 3 * M) = 8 * (M * M) := by ring
        omega
      have hb : 6 * k + 6 * m * m + 6 * m + 14 * (k + 1) + 6 ≤ 40 * M ^ 2 := by
        have hm2 : m * m ≤ M * M := Nat.mul_le_mul hmM hmM
        have h6 : 6 * m * m = 6 * (m * m) := by ring
        omega
      have hc : 2 * (k + 1) * (k + 1) + 22 * (k + 1) + 5 ≤ 30 * M ^ 2 := by
        have hk2 : (k + 1) * (k + 1) ≤ M * M := Nat.mul_le_mul hk1M hk1M
        have h2k : 2 * (k + 1) * (k + 1) = 2 * ((k + 1) * (k + 1)) := by ring
        omega
      have ha' : m * (5 * k + 3) ≤ 10 * M ^ 2 * P := le_trans hmk (Nat.le_mul_of_pos_right _ hP1)
      have hb' : P * (6 * k + 6 * m * m + 6 * m + 14 * (k + 1) + 6) ≤ 40 * M ^ 2 * P := by
        rw [mul_comm]; exact Nat.mul_le_mul_right P hb
      have hc' : 2 * (k + 1) * (k + 1) + 22 * (k + 1) + 5 ≤ 30 * M ^ 2 * P :=
        le_trans hc (Nat.le_mul_of_pos_right _ hP1)
      have hadd := Nat.add_le_add (Nat.add_le_add ha' hb') hc'
      have hle : 10 * M ^ 2 * P + 40 * M ^ 2 * P + 30 * M ^ 2 * P ≤ 100 * M ^ 2 * P := by
        have : 10 * M ^ 2 * P + 40 * M ^ 2 * P + 30 * M ^ 2 * P = 80 * (M ^ 2 * P) := by ring
        have : 100 * M ^ 2 * P = 100 * (M ^ 2 * P) := by ring
        omega
      exact le_trans hadd hle
    have hprod := Nat.mul_le_mul hkM h1
    have hpow : M * (100 * M ^ 2 * P) = 100 * M ^ 3 * P := by ring
    rw [hpow] at hprod; exact hprod
  have hfin : finalCost ≤ 30 * M := by dsimp only [finalCost]; omega
  have t1 : P * perSeed ≤ 200 * M ^ 5 * R * P := by
    have h1 := Nat.mul_le_mul_left P hperSeed
    have h2 : P * (200 * M ^ 3 * R) = 200 * M ^ 3 * R * P := by ring
    have h3 : M ^ 3 ≤ M ^ 5 := le_trans hM3_le4 hM4_le5
    have h4 := Nat.mul_le_mul_right P (Nat.mul_le_mul_right R (Nat.mul_le_mul_left 200 h3))
    rw [h2] at h1; exact le_trans h1 h4
  have t2 : (k + 1) * perTab ≤ 50 * M ^ 5 * R * P := by
    have h1 : 50 * M ^ 4 ≤ 50 * M ^ 5 := Nat.mul_le_mul_left 50 hM4_le5
    have h2 : 50 * M ^ 5 ≤ 50 * M ^ 5 * R := Nat.le_mul_of_pos_right _ hR1
    have h3 : 50 * M ^ 5 * R ≤ 50 * M ^ 5 * R * P := Nat.le_mul_of_pos_right _ hP1
    exact le_trans hperTab (le_trans h1 (le_trans h2 h3))
  have t3 : cntCost ≤ 50 * M ^ 5 * R * P := by
    have h1 : M ^ 2 ≤ M ^ 5 := le_trans hM2_le3 (le_trans hM3_le4 hM4_le5)
    have h2 : 50 * M ^ 2 * P ≤ 50 * M ^ 5 * P := Nat.mul_le_mul_right P (Nat.mul_le_mul_left 50 h1)
    have h3 : 50 * M ^ 5 * P ≤ 50 * M ^ 5 * R * P := by
      have := Nat.mul_le_mul_right P (Nat.le_mul_of_pos_right (50 * M ^ 5) hR1)
      simpa [mul_assoc] using this
    exact le_trans hcnt (le_trans h2 h3)
  have t4 : k * bsStepCost ≤ 100 * M ^ 5 * R * P := by
    have h1 : M ^ 3 ≤ M ^ 5 := le_trans hM3_le4 hM4_le5
    have h2 : 100 * M ^ 3 * P ≤ 100 * M ^ 5 * P := Nat.mul_le_mul_right P (Nat.mul_le_mul_left 100 h1)
    have h3 : 100 * M ^ 5 * P ≤ 100 * M ^ 5 * R * P := by
      have := Nat.mul_le_mul_right P (Nat.le_mul_of_pos_right (100 * M ^ 5) hR1)
      simpa [mul_assoc] using this
    exact le_trans hbs (le_trans h2 h3)
  have t5 : finalCost ≤ 30 * M ^ 5 * R * P := by
    have h1 : M ≤ M ^ 5 := le_trans hM_le2 (le_trans hM2_le3 (le_trans hM3_le4 hM4_le5))
    have h2 : 30 * M ≤ 30 * M ^ 5 := Nat.mul_le_mul_left 30 h1
    have h3 : 30 * M ^ 5 ≤ 30 * M ^ 5 * R * P :=
      le_trans (Nat.le_mul_of_pos_right _ hR1) (Nat.le_mul_of_pos_right _ hP1)
    exact le_trans hfin (le_trans h2 h3)
  have hsum : 2 ^ S * perSeed + (k + 1) * perTab + cntCost + k * bsStepCost + finalCost ≤
      430 * M ^ 5 * R * P := by
    have hadd := Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add t1 t2) t3) t4) t5
    have heq : 200 * M ^ 5 * R * P + 50 * M ^ 5 * R * P + 50 * M ^ 5 * R * P +
        100 * M ^ 5 * R * P + 30 * M ^ 5 * R * P = 430 * M ^ 5 * R * P := by ring
    rw [heq] at hadd; exact hadd
  have hbig : 430 * M ^ 5 * R * P ≤ 1048576 * M ^ 5 * R * 2 ^ (seedWidthOf k r) :=
    Nat.mul_le_mul (Nat.mul_le_mul_right R (Nat.mul_le_mul_right (M ^ 5) (by omega : 430 ≤ 1048576))) hP_le
  exact le_trans hsum hbig

end PEqualNP.Outside.L_meta_25708

open PEqualNP.Outside.L_meta_25708 in
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover in
theorem PEqualNP.Outside.L_meta_25708 :
∀ (k r m : Nat), 4 ≤ r →
  let h := (k+1)/2
  let z := k-h
  let u := 5*r-3
  let extra := min (r-2) (z-6*r)
  let seedWidth := min k u + extra
  let rot := fun (offset x : Nat) =>
    ((x <<< (offset % k)) ||| (x >>> (k-offset % k))) % 2^k
  let mix := fun (gap value : Nat) => value ^^^ rot gap value ^^^ rot (k-gap) value
  let chi := fun (word : Nat) => (List.range k).foldl (fun acc site =>
    acc ||| ((xor (word.testBit site)
      (!(word.testBit ((site+1) % k)) && word.testBit ((site+2) % k))).toNat <<< site)) 0
  let step := fun (constants : Nat → Fin (2^k)) (col : Bool) (raw prev t : Nat) =>
    chi (mix (if col then 2 else 1) prev) ^^^ rot (if col then 3*t+1 else 2*(t-1)) raw ^^^
      (constants (if col then r+t else t)).val
  let state := fun (c : Nat → Fin (2^k)) (side : Bool) (key name : Nat) =>
    (List.range r).foldl (fun v tick => step c side key v (tick+1))
      (rot (if side then 3 else 1) key ^^^ name)
  let n := 2*r*k+3*k+2*h+m*(k+1)
  let bits := fun (len data : Nat) => (List.range len).map (fun pos => data.testBit pos)
  let parity := fun (natWord : Nat) => (List.range k).foldl
    (fun total bitPos => xor total (natWord.testBit bitPos)) false
  ∃ (C : PEqualNP.CircuitLowerBounds.Circuit)
      (countWire : Fin (k+1) → Fin (n+C.size)) (keyWire : Fin k → Fin (n+C.size)),
    PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack n C ∧
    C.output < n+C.size ∧ C.size ≤ 1048576*(k+m+1)^5*(r+1)*2^seedWidth ∧
    ∀ (schedule : Nat → Fin (2^k)) (leftName rightName : Fin (2^k))
        (a b : Fin (2^h)) (A : Fin m → Fin (2^k)) (rhs : Fin m → Bool)
        (rank : Fin (2^k)),
      let input := (List.range (2*r)).flatMap (fun idx => bits k (schedule (idx+1)).val) ++
        bits k leftName.val ++ bits k rightName.val ++ bits h a.val ++ bits h b.val ++
        (List.ofFn A).flatMap (fun entry => bits k entry.val) ++ List.ofFn rhs ++ bits k rank.val
      let solutions := (List.range (2^k)).filter (fun w => decide (
        state schedule false w leftName.val >>> z = a.val ∧
        state schedule true w rightName.val >>> z = b.val ∧
        ∀ i : Fin m, parity (w &&& (A i).val) = rhs i))
      C.eval input = decide (rank.val < solutions.length) ∧
      (∀ j : Fin (k+1), (C.wires input).getD (countWire j).val false = solutions.length.testBit j.val) ∧
      (∀ d : Fin k, (C.wires input).getD (keyWire d).val false =
        ((solutions.getD rank.val 0).testBit d.val)) := by
  intro k r m hr
  by_cases hk0 : k = 0
  · subst hk0
    exact solve_k_zero r m hr
  · have hk : 0 < k := by omega
    intro h z u extra seedWidth rot mix chi step state n bits parity
    let S := seedLen k r
    let perSeed := (if k ≤ uOf r then k else (hOf k + (r + 3)) * (22 * k * r + 4 * k + 4) + k) +
      (44 * k * r + 20 * k + 5) + m * (5 * k + 5)
    let perTab := (m + m * m + 1) + k * (13 * m * m + 3 * m) + (4 * (m + 1) * (m + 1) + 2)
    let cntCost := 2 ^ S * (6 * m * m + 2 * m + 14 * (k + 1) + 3) +
      (2 * (k + 1) * (k + 1) + 3 * (k + 1) + 2)
    let bsStepCost := m * (5 * k + 3) +
      2 ^ S * (6 * k + 6 * m * m + 6 * m + 14 * (k + 1) + 6) +
      (2 * (k + 1) * (k + 1) + 22 * (k + 1) + 5)
    let finalCost := (1 + (k + 1)) + (15 * (k + 1) + 2) + k
    -- 1. Build precompSet
    have hSeeds := Extends.parallel_fin_const (k := 2 ^ S) (S := baseInputSigs k r m)
      (T := fun idx : Fin (2 ^ S) =>
        Set.range (fun j : Fin k => fun x => sweepW0 hk hr x (sdOfIdx idx) j) ∪
        {fun x => okSeed hk hr x (sdOfIdx idx)} ∪
        Set.range (fun i : Fin m => fun x => seedRhs hk hr x (sdOfIdx idx) i))
      (c := perSeed) (fun idx => Extends.perSeed_sig hk hr (sdOfIdx idx))
    have hTabs := Extends.parallel_fin_const (k := k + 1) (S := baseInputSigs k r m)
      (T := fun b : Fin (k + 1) =>
        ptabBits (fun x => colTab x b.val) ∪
        Set.range (fun d : Fin (k + 1) => fun x => decide (nullityOf x b.val = d.val)))
      (c := perTab) (fun b => Extends.colTab_and_nullOH b.val (by omega))
    have hPre : Extends (nIn k r m) (baseInputSigs k r m) (precompSet hk hr)
        (2 ^ S * perSeed + (k + 1) * perTab) :=
      (((Extends.of_subset Set.Subset.rfl).union hSeeds).union hTabs).mono
        Set.Subset.rfl Set.Subset.rfl (by omega)
    -- 2. Total count
    have hCnt : Extends (nIn k r m) (precompSet hk hr) (wordBits (fun x => totalCountW hk hr x)) cntCost :=
      Extends.totalCountW_sig hk hr
    -- 3. Rank word + initial BSState + k steps of bsRun
    let rankW : WordSig (nIn k r m) (k + 1) := fun x => (natOfBits (inRank x) : ZMod (2 ^ (k + 1)))
    have hRankW : Extends (nIn k r m) (baseInputSigs k r m) (wordBits rankW) 1 := by
      have hf : Extends (nIn k r m) (baseInputSigs k r m) {fun _ => false} 1 := Extends.add_const false
      refine ((Extends.of_subset Set.Subset.rfl).union hf).mono Set.Subset.rfl ?_ (by omega)
      rintro _ ⟨j, rfl⟩
      by_cases hjk : j.val < k
      · left
        have heq : (fun x : Fin (nIn k r m) → Bool => (rankW x).val.testBit j.val) =
            fun x => inRank x ⟨j.val, hjk⟩ := by
          funext x; dsimp only [rankW]
          haveI : NeZero (2 ^ (k + 1)) := ⟨by positivity⟩
          have hlt : natOfBits (inRank x) < 2 ^ (k + 1) :=
            lt_trans (natOfBits_lt _) (Nat.pow_lt_pow_right (by decide) (by omega))
          rw [ZMod.val_natCast, Nat.mod_eq_of_lt hlt, natOfBits_testBit (inRank x) ⟨j.val, hjk⟩]
        dsimp only; rw [heq]; exact inRank_mem_base ⟨j.val, hjk⟩
      · right
        funext x; dsimp only [rankW]
        haveI : NeZero (2 ^ (k + 1)) := ⟨by positivity⟩
        have hlt : natOfBits (inRank x) < 2 ^ (k + 1) :=
          lt_trans (natOfBits_lt _) (Nat.pow_lt_pow_right (by decide) (by omega))
        rw [ZMod.val_natCast, Nat.mod_eq_of_lt hlt]
        exact Nat.testBit_eq_false_of_lt
          (lt_of_lt_of_le (natOfBits_lt (inRank x)) (Nat.pow_le_pow_right (by decide) (by omega)))
    have hBS0 : Extends (nIn k r m) (precompSet hk hr)
        (precompSet hk hr ∪ bsStateSigs (fun x => bsRun hk hr x (rankW x) 0)) (1 + (k + 1)) := by
      have hf : Extends (nIn k r m) (precompSet hk hr)
          (Set.range (fun _ : Fin k => fun _ : Fin (nIn k r m) → Bool => false)) (k + 1) := by
        have := Extends.add_range_fin (S := precompSet hk hr)
          (f := fun _ : Fin k => fun _ : Fin (nIn k r m) → Bool => false) (c := 1)
          (fun _ => Extends.add_const false)
        exact this.mono Set.Subset.rfl Set.Subset.rfl (by omega)
      have hrw := hRankW.mono (fun _ h => mem_precomp_base hk hr h) Set.Subset.rfl le_rfl
      exact (((Extends.of_subset Set.Subset.rfl).union hf).union hrw).mono Set.Subset.rfl
        (by rintro z (h | (h | h)); exact Or.inl (Or.inl h); exact Or.inl (Or.inr h); exact Or.inr h) (by omega)
    let InvBS (t : ℕ) : Set (Sig (nIn k r m)) :=
      precompSet hk hr ∪ bsStateSigs (fun x => bsRun hk hr x (rankW x) t)
    have hBS_step : ∀ t < k, Extends (nIn k r m) (InvBS t) (InvBS (t + 1)) bsStepCost := by
      intro t ht
      have hs := Extends.bsStep_sig hk hr ⟨k - 1 - t, by omega⟩ (fun x => bsRun hk hr x (rankW x) t)
      have heq : (fun x => bsStep hk hr x ⟨k - 1 - t, by omega⟩ (bsRun hk hr x (rankW x) t)) =
          fun x => bsRun hk hr x (rankW x) (t + 1) := by
        funext x; simp [bsRun, ht]
      rw [heq] at hs
      exact ((Extends.of_subset Set.subset_union_left).union hs).mono Set.Subset.rfl Set.Subset.rfl
        (by dsimp only [bsStepCost, S]; omega)
    have hBS_fold := Extends.fold_nat_const k InvBS bsStepCost hBS_step
    have hBS := hBS0.seq (hBS_fold.mono Set.subset_union_right Set.Subset.rfl le_rfl)
    -- 4. validRank + masked keyWire!
    let validSig : Sig (nIn k r m) := fun x => decide ((rankW x).val < (totalCountW hk hr x).val)
    let keyOut : Fin k → Sig (nIn k r m) := fun d x => validSig x && (bsRun hk hr x (rankW x) k).key d
    have hValid : Extends (nIn k r m) (wordBits (fun x => totalCountW hk hr x) ∪ wordBits rankW)
        {validSig} (15 * (k + 1) + 2) := by
      have hge := Extends.word_sub_ge rankW (fun x => totalCountW hk hr x)
      have hnot := Extends.add_not
        (S := (wordBits (fun x => totalCountW hk hr x) ∪ wordBits rankW) ∪
          ({fun x => decide ((totalCountW hk hr x).val ≤ (rankW x).val)} ∪
           wordBits (fun x => rankW x - totalCountW hk hr x)))
        (Or.inr (Or.inl rfl))
      have heq : (fun x => !decide ((totalCountW hk hr x).val ≤ (rankW x).val)) = validSig := by
        funext x; dsimp only [validSig]; rw [Bool.eq_iff_iff]; simp
      rw [heq] at hnot
      exact ((hge.mono (by rintro z (h | h); exact Or.inr h; exact Or.inl h) Set.Subset.rfl le_rfl).seq hnot).mono
        Set.Subset.rfl Set.Subset.rfl (by omega)
    -- Combine: hPre -> (hCnt ∪ (hBS0.trans hBS_fold)) -> hValid -> keyOut!
    have hBS_keep : Extends (nIn k r m) (precompSet hk hr)
        (wordBits rankW ∪ InvBS k) (1 + (k + 1) + k * bsStepCost) := by
      have h0 : Extends (nIn k r m) (precompSet hk hr) (InvBS 0) (1 + (k + 1)) := hBS0
      have h1 : Extends (nIn k r m) (precompSet hk hr) (InvBS 0 ∪ InvBS k) (1 + (k + 1) + k * bsStepCost) :=
        h0.trans (hBS_fold.mono Set.subset_union_right Set.Subset.rfl le_rfl)
      refine h1.mono Set.Subset.rfl ?_ le_rfl
      rintro z (hrw | hk_mem)
      · exact Or.inl (Or.inr (Or.inr hrw))
      · exact Or.inr hk_mem
    have hMid : Extends (nIn k r m) (baseInputSigs k r m)
        (wordBits (fun x => totalCountW hk hr x) ∪ (wordBits rankW ∪ InvBS k))
        (2 ^ S * perSeed + (k + 1) * perTab + (cntCost + (1 + (k + 1) + k * bsStepCost))) :=
      hPre.seq ((hCnt.union hBS_keep).mono Set.subset_union_right Set.Subset.rfl le_rfl)
    have hValStep : Extends (nIn k r m)
        (baseInputSigs k r m ∪ (wordBits (fun x => totalCountW hk hr x) ∪ (wordBits rankW ∪ InvBS k)))
        {validSig} (15 * (k + 1) + 2) :=
      hValid.mono (by
        rintro z (h | h)
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h))) Set.Subset.rfl le_rfl
    have hWithVal := hMid.trans hValStep
    have hKeyStep : Extends (nIn k r m)
        (baseInputSigs k r m ∪
          ((wordBits (fun x => totalCountW hk hr x) ∪ (wordBits rankW ∪ InvBS k)) ∪ {validSig}))
        (Set.range keyOut) k := by
      simpa [mul_one] using Extends.add_range_fin
        (S := baseInputSigs k r m ∪
          ((wordBits (fun x => totalCountW hk hr x) ∪ (wordBits rankW ∪ InvBS k)) ∪ {validSig}))
        (f := keyOut) (c := 1) (fun d => by
          have hd_mem : (fun x => (bsRun hk hr x (rankW x) k).key d) ∈ InvBS k :=
            Or.inr (Or.inl ⟨d, rfl⟩)
          exact Extends.add_and (Or.inr (Or.inr rfl)) (Or.inr (Or.inl (Or.inr (Or.inr hd_mem)))))
    have hFinal := hWithVal.trans hKeyStep
    obtain ⟨hF0, hB0, hsz0, hbase0⟩ := base_circuit (nIn k r m)
    obtain ⟨C0, hF, hB, hsz, _, hOuts⟩ := hFinal ⟨[], 0⟩ hF0 hB0 (by rintro _ ⟨p, rfl⟩; exact hbase0 p)
    obtain ⟨wOut, hwOut⟩ := hOuts validSig (Or.inl (Or.inr rfl))
    have hex_cnt : ∃ cntW : Fin (k + 1) → Fin (nIn k r m + C0.size),
        ∀ j x, (C0.wires (List.ofFn x)).getD (cntW j).val false = (totalCountW hk hr x).val.testBit j.val :=
      ⟨fun j => (hOuts _ (Or.inl (Or.inl (Or.inl ⟨j, rfl⟩)))).choose,
       fun j => (hOuts _ (Or.inl (Or.inl (Or.inl ⟨j, rfl⟩)))).choose_spec⟩
    obtain ⟨cntW, hcntW⟩ := hex_cnt
    have hex_key : ∃ keyW : Fin k → Fin (nIn k r m + C0.size),
        ∀ d x, (C0.wires (List.ofFn x)).getD (keyW d).val false = keyOut d x :=
      ⟨fun d => (hOuts _ (Or.inr ⟨d, rfl⟩)).choose,
       fun d => (hOuts _ (Or.inr ⟨d, rfl⟩)).choose_spec⟩
    obtain ⟨keyW, hkeyW⟩ := hex_key
    let C : Circuit := ⟨C0.gates, wOut.val⟩
    have hsz_eq : C.size = C0.size := rfl
    have hn_eq : n = nIn k r m := rfl
    have hC_bound : C.size ≤ 1048576 * (k + m + 1) ^ 5 * (r + 1) * 2 ^ seedWidth := by
      have hsb := size_bound_main k r m hk hr
      dsimp only [S, perSeed, perTab, cntCost, bsStepCost, finalCost] at hsz hsb ⊢
      have : seedWidth = seedWidthOf k r := rfl
      rw [this, hsz_eq]; omega
    refine ⟨C, cntW, keyW, hF, hB, wOut.isLt, hC_bound, ?_⟩
    intro schedule leftName rightName a b A rhs rank input solutions
    obtain ⟨x, hx_ofFn, hx_sched, hx_left, hx_right, hx_a, hx_b, hx_mat, hx_rhs, hx_rank⟩ :=
      input_pack_spec k r m schedule leftName rightName a b A rhs rank
    have hsched_congr : ∀ col raw name (t : ℕ), t ≤ r →
        stateVSteps hk r (fun idx i => (schedule idx).val.testBit i.val) col raw name t =
        stateVSteps hk r (schedVec x) col raw name t := by
      intro col raw name t ht
      induction t with
      | zero => rfl
      | succ t ih =>
        dsimp only [stateVSteps, stepV]
        rw [ih (by omega)]
        funext j
        have hidx_ok : 1 ≤ (if col then r + (t + 1) else t + 1) ∧
            (if col then r + (t + 1) else t + 1) ≤ 2 * r := by cases col <;> simp <;> omega
        have hc_eq : (schedule (if col then r + (t + 1) else t + 1)).val.testBit j.val =
            schedVec x (if col then r + (t + 1) else t + 1) j := by
          unfold schedVec; rw [dif_pos hidx_ok, hx_sched]
          have harg : (if col then r + (t + 1) else t + 1) - 1 + 1 =
              if col then r + (t + 1) else t + 1 := by cases col <;> simp <;> omega
          rw [harg]
        rw [hc_eq]
    have hsol_eq : solutions = solNatList hk x := by
      unfold solNatList
      refine List.filter_congr fun w hw => ?_
      have hw_lt : w < 2 ^ k := List.mem_range.mp hw
      rw [Bool.eq_iff_iff, decide_eq_true_eq]
      simp only [isSolVec, Bool.and_eq_true, List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq]
      have hleft_eq : inLeft x = fun j => leftName.val.testBit j.val := funext hx_left
      have hright_eq : inRight x = fun j => rightName.val.testBit j.val := funext hx_right
      have hstF : state schedule false w leftName.val >>> z = a.val ↔
          ∀ i : Fin (hOf k),
            stateV hk r (schedVec x) false (fun j => w.testBit j.val) (inLeft x)
              ⟨zOf k + i.val, by unfold hOf zOf; omega⟩ = inA x i := by
        change stateN k r schedule false w leftName.val >>> z = a.val ↔ _
        have hshr := state_shr_eq_iff _ (stateN_lt hk r schedule false w leftName.val hw_lt leftName.isLt) a
        dsimp only at hshr
        refine hshr.trans ⟨fun H i => ?_, fun H i => ?_⟩
        · let idx : Fin k := ⟨zOf k + i.val, by unfold hOf zOf; omega⟩
          have hi : (stateN k r schedule false w leftName.val).testBit idx.val = a.val.testBit i.val := H i
          rw [testBit_stateN hk r schedule false w leftName.val hw_lt leftName.isLt idx] at hi
          unfold stateV at hi ⊢
          rw [hsched_congr false _ _ r le_rfl] at hi
          rw [hx_a i, hleft_eq, hi]
        · let idx : Fin k := ⟨zOf k + i.val, by unfold zOf; omega⟩
          have hi := H i
          change (stateN k r schedule false w leftName.val).testBit idx.val = a.val.testBit i.val
          rw [testBit_stateN hk r schedule false w leftName.val hw_lt leftName.isLt idx]
          unfold stateV at hi ⊢
          rw [hsched_congr false _ _ r le_rfl, ← hx_a i, ← hleft_eq, hi]
      have hstT : state schedule true w rightName.val >>> z = b.val ↔
          ∀ i : Fin (hOf k),
            stateV hk r (schedVec x) true (fun j => w.testBit j.val) (inRight x)
              ⟨zOf k + i.val, by unfold hOf zOf; omega⟩ = inB x i := by
        change stateN k r schedule true w rightName.val >>> z = b.val ↔ _
        have hshr := state_shr_eq_iff _ (stateN_lt hk r schedule true w rightName.val hw_lt rightName.isLt) b
        dsimp only at hshr
        refine hshr.trans ⟨fun H i => ?_, fun H i => ?_⟩
        · let idx : Fin k := ⟨zOf k + i.val, by unfold hOf zOf; omega⟩
          have hi : (stateN k r schedule true w rightName.val).testBit idx.val = b.val.testBit i.val := H i
          rw [testBit_stateN hk r schedule true w rightName.val hw_lt rightName.isLt idx] at hi
          unfold stateV at hi ⊢
          rw [hsched_congr true _ _ r le_rfl] at hi
          rw [hx_b i, hright_eq, hi]
        · let idx : Fin k := ⟨zOf k + i.val, by unfold zOf; omega⟩
          have hi := H i
          change (stateN k r schedule true w rightName.val).testBit idx.val = b.val.testBit i.val
          rw [testBit_stateN hk r schedule true w rightName.val hw_lt rightName.isLt idx]
          unfold stateV at hi ⊢
          rw [hsched_congr true _ _ r le_rfl, ← hx_b i, ← hright_eq, hi]
      have hpar : (∀ i : Fin m, parity (w &&& (A i).val) = rhs i) ↔
          ∀ i : Fin m, (List.finRange k).foldl (fun acc j => xor acc (w.testBit j.val && inMat x i j)) false = inRhs x i := by
        constructor <;> intro H i
        · have hi := H i
          change parityN k (w &&& (A i).val) = rhs i at hi
          rw [parityN_eq_finRange] at hi
          simp only [hx_rhs i, hx_mat i, hi]
        · have hi := H i
          change parityN k (w &&& (A i).val) = rhs i
          rw [parityN_eq_finRange]
          simp only [hx_rhs i, hx_mat i] at hi
          exact hi
      rw [hstF, hstT, hpar, and_assoc]
    have hrankW_eq : rankW x = (rank.val : ZMod (2 ^ (k + 1))) := by
      dsimp only [rankW]
      have h1 : natOfBits (inRank x) = rank.val := by
        have : inRank x = fun j : Fin k => rank.val.testBit j.val := funext hx_rank
        rw [this]; exact natOfBits_of_testBit rank.val rank.isLt
      rw [h1]
    have hrankW_val : (rankW x).val = rank.val := by
      haveI : NeZero (2 ^ (k + 1)) := ⟨by positivity⟩
      rw [hrankW_eq, ZMod.val_natCast,
        Nat.mod_eq_of_lt (lt_trans rank.isLt (Nat.pow_lt_pow_right (by decide) (by omega)))]
    have hcnt_val : (totalCountW hk hr x).val = solutions.length := by
      rw [hsol_eq]; exact totalCountW_val hk hr x
    have hC_wires : C.wires input = C0.wires (List.ofFn x) := by
      rw [hx_ofFn]; rfl
    refine ⟨?_, ?_, ?_⟩
    · change (C.wires input).getD wOut.val false = decide (rank.val < solutions.length)
      rw [hC_wires, hwOut x]
      simp only [validSig, hrankW_val, hcnt_val]
    · intro j
      rw [hC_wires, hcntW j x, hcnt_val]
    · intro d
      rw [hC_wires, hkeyW d x]
      dsimp only [keyOut, validSig]
      rw [hrankW_val, hcnt_val]
      by_cases hlt : rank.val < solutions.length
      · rw [decide_eq_true hlt, Bool.true_and, hrankW_eq, hsol_eq]
        rw [hsol_eq] at hlt
        exact (bsRun_end_testBit hk hr x rank hlt d).symm
      · rw [decide_eq_false hlt, Bool.false_and]
        have hdef : solutions.getD rank.val 0 = 0 := by
          have hge : solutions.length ≤ rank.val := by omega
          rw [List.getD, List.getElem?_eq_none hge]; rfl
        rw [hdef]; simp

