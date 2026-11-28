import Mathlib
import PEqualNP.Defs
import PEqualNP.Library.Helpers.FiniteGateBank

namespace PEqualNP.Outside.L_meta_53188

open Classical

private theorem countSupports {slots : Nat} {Arrow : Type} [Fintype Arrow]
    (support : Arrow → Finset (Fin slots)) (rev : Arrow → Arrow)
    (distinct : Function.Injective support) (undo : Function.Injective rev)
    (used : ∀ edge, (support edge).Nonempty)
    (room : ∀ edge, support edge ⊂ (support (rev edge))ᶜ) (hasEdge : Nonempty Arrow) :
    Fintype.card Arrow + slots.choose (slots / 2) + 2 ≤ 2 ^ slots := by
  let code := fun edge => if (support edge).card < slots / 2 then support edge else (support (rev edge))ᶜ
  have large (edge) (h : ¬(support edge).card < slots / 2) : slots / 2 < (code edge).card := by
    have := Finset.card_lt_card (room edge)
    simp only [code, if_neg h]
    omega
  have small (edge) (h : (support edge).card < slots / 2) : (code edge).card < slots / 2 := by
    simpa only [code, if_pos h] using h
  have inj : Function.Injective code := by
    intro left right heq
    by_cases hl : (support left).card < slots / 2 <;> by_cases hr : (support right).card < slots / 2
    · apply distinct
      simpa only [code, if_pos hl, if_pos hr] using heq
    · have := small left hl
      rw [heq] at this
      exact False.elim (Nat.lt_asymm this (large right hr))
    · have := small right hr
      rw [← heq] at this
      exact False.elim (Nat.lt_asymm this (large left hl))
    · apply undo
      apply distinct
      apply compl_injective
      simpa only [code, if_neg hl, if_neg hr] using heq
  have middle (edge) : (code edge).card ≠ slots / 2 := by
    by_cases h : (support edge).card < slots / 2
    · exact (small edge h).ne
    · exact (large edge h).ne'
  have occupied (edge) : (code edge).Nonempty := by
    dsimp only [code]
    split
    · exact used _
    · exact (used edge).mono (room edge).le
  have proper (edge) : code edge ≠ Finset.univ := by
    intro h
    dsimp only [code] at h
    split at h
    · rename_i hs
      rw [h, Finset.card_univ, Fintype.card_fin] at hs
      omega
    · have he := (used (rev edge)).ne_empty
      exact he (by simpa using congrArg (fun s : Finset (Fin slots) => sᶜ) h)
  obtain ⟨edge⟩ := hasEdge
  have hpos := (used edge).card_pos
  have hstrict := Finset.card_lt_card (room edge)
  have hbound := Finset.card_le_univ ((support (rev edge))ᶜ)
  rw [Fintype.card_fin] at hbound
  have hslots : 1 < slots := by omega
  let codes := Finset.univ.image code
  let centers := (Finset.univ : Finset (Fin slots)).powersetCard (slots / 2)
  have dis : Disjoint codes centers := by
    rw [Finset.disjoint_left]
    rintro s hs hm
    obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hs
    exact middle _ (Finset.mem_powersetCard.mp hm).2
  have hzero : ∅ ∉ codes ∪ centers := by
    simp only [Finset.mem_union, not_or]
    constructor
    · rintro h
      obtain ⟨e, _, he⟩ := Finset.mem_image.mp h
      exact (occupied e).ne_empty he
    · intro h
      have := (Finset.mem_powersetCard.mp h).2
      simp only [Finset.card_empty] at this
      omega
  have hfull : Finset.univ ∉ insert ∅ (codes ∪ centers) := by
    simp only [Finset.mem_insert, Finset.mem_union, not_or]
    refine ⟨?_, ?_, ?_⟩
    · intro h
      have := congrArg Finset.card h
      simp at this
      omega
    · rintro h
      obtain ⟨e, _, he⟩ := Finset.mem_image.mp h
      exact proper e he
    · intro h
      have := (Finset.mem_powersetCard.mp h).2
      simp only [Finset.card_univ, Fintype.card_fin] at this
      omega
  have total := Finset.card_le_univ (insert Finset.univ (insert ∅ (codes ∪ centers)))
  rw [Finset.card_insert_of_notMem hfull, Finset.card_insert_of_notMem hzero, Finset.card_union_of_disjoint dis] at total
  simpa [codes, centers, Finset.card_image_of_injective _ inj, Finset.card_powersetCard, Fintype.card_finset, Nat.add_assoc] using total

private theorem shrinkRows {Row Key : Type} {colors : Nat} (rows : Finset Row)
    (key : Row → Key) (mark : Row → Finset (Fin colors))
    (switch : ∀ color, ∃ x ∈ rows, ∃ y ∈ rows, key x = key y ∧ color ∉ mark x ∧
      mark y = insert color (mark x)) : (rows.image key).card + colors ≤ rows.card := by
  classical
  let view := fun (seen : Finset (Fin colors)) (x : Row) => (key x, mark x ∩ seen)
  have bound (seen : Finset (Fin colors)) : (rows.image key).card + seen.card ≤ (rows.image (view seen)).card := by
    induction seen using Finset.induction_on with
    | empty =>
      have h := Finset.card_image_le (s := rows.image (view ∅)) (f := Prod.fst)
      simpa [Finset.image_image, Function.comp_def, view] using h
    | @insert color seen fresh ih =>
      obtain ⟨x, hx, y, hy, same, absent, add⟩ := switch color
      let cut := fun p : Key × Finset (Fin colors) => (p.1, p.2 ∩ seen)
      let next := rows.image (view (insert color seen))
      have image : next.image cut = rows.image (view seen) := by
        rw [Finset.image_image]
        congr 1
        funext z
        refine Prod.ext (by rfl) ?_
        ext j
        simp [cut, view]
      have drop : (next.image cut).card < next.card := by
        apply lt_of_le_of_ne Finset.card_image_le
        intro heq
        have inj := Finset.card_image_iff.mp heq
        have ceq : cut (view (insert color seen) x) = cut (view (insert color seen) y) := by
          apply Prod.ext same
          ext j
          by_cases h : j = color <;> simp_all [cut, view]
        have eq := inj (Finset.mem_image_of_mem _ hx) (Finset.mem_image_of_mem _ hy) ceq
        have diff := congrArg (fun p : Key × Finset (Fin colors) => color ∈ p.2) eq
        simp [view, absent, add] at diff
      rw [image] at drop
      dsimp only [next] at drop
      rw [Finset.card_insert_of_notMem fresh]
      omega
  have h := bound Finset.univ
  simpa using h.trans Finset.card_image_le

open PEqualNP.FiniteGateBank PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def goodNet {width : Nat} (net : Net width) (cost : net.cost = 0) :
    Monotone2 ⟨net.gates, 0⟩ := by
  intro gate hg
  obtain ⟨ops, fan⟩ := net.fan gate hg
  simp only [Net.cost, PEqualNP.NotBracket.notCount, List.length_eq_zero_iff, List.filter_eq_nil_iff] at cost
  have noNot : gate.op ≠ .not := by
    intro h
    simpa [h] using cost gate hg
  exact ⟨by simpa [Set.mem_insert_iff, Set.mem_singleton_iff, noNot] using ops, fan⟩

private def inputRows {X : Type} (inputs : List (X → Bool)) (x : X) := inputs.map (fun f => f x)

private theorem initHas {X : Type} {inputs : List (X → Bool)} {f : X → Bool} (h : f ∈ inputs) :
    (empty inputs.length).has (inputRows inputs) f := by
  obtain ⟨i,hi,eq⟩ := List.getElem_of_mem h
  refine ⟨i, by simpa [empty] using hi, fun x => ?_⟩
  change (inputs.map (fun g => g x)).getD i false = _
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem, hi, eq]

private theorem allTerms {X J : Type} {w : Nat} {raw : X → List Bool} (width : ∀ x, (raw x).length=w)
    (p : Net w) (one : p.has raw (fun _ => true)) (l : List J) (f : J → X → Bool)
    (known : ∀ i ∈ l, p.has raw (f i)) :
    ∃ q, Grow raw p q l.length 0 ∧ q.has raw (fun x => l.all (fun j => f j x)) := by
  induction l with
  | nil => exact ⟨p, start _ _, one⟩
  | cons j l ih =>
    obtain ⟨q,gq,old⟩ := ih (fun i hi => known i (by simp [hi]))
    obtain ⟨r,gr,ans⟩ := binary width q _ _ (gq.1 _ (known j (by simp))) old true
    exact ⟨r,chain gq gr,by simpa [List.all_cons] using ans⟩

private theorem interpolate {X : Type} [Fintype X] (inputs : List (X → Bool)) (goals : Finset (X → Bool))
    (zero : (fun _ => false) ∈ inputs) (one : (fun _ => true) ∈ inputs)
    (mono : ∀ x y, (∀ f ∈ inputs, f x = true → f y = true) → ∀ g ∈ goals, g x = true → g y = true) :
    ∃ p : Net inputs.length, p.cost = 0 ∧ ∀ f ∈ goals, p.has (inputRows inputs) f := by
  classical
  let raw := inputRows inputs
  let startNet := empty inputs.length
  have width (x) : (raw x).length = inputs.length := by simp [raw, inputRows]
  let conjunction := fun row y => (inputs.filter (fun f => f row)).all (fun f => f y)
  obtain ⟨net, grow, reaches⟩ := batch (raw := raw) startNet goals.toList id
    (Fintype.card X * inputs.length + Fintype.card X) 0 (by
      intro target ht p preserve
      let positives := (Finset.univ.filter (fun row => target row = true)).toList
      obtain ⟨q, growQ, terms⟩ := batch (raw := raw) p positives conjunction inputs.length 0 (by
        intro x hx q lifted
        obtain ⟨r, gr, attained⟩ := allTerms width q (lifted _ (preserve _ (initHas one)))
          (inputs.filter (fun f => f x)) id (fun f hf => lifted _ (preserve _ (initHas (List.mem_filter.mp hf).1)))
        exact ⟨r, allowance gr (List.length_filter_le ..), attained⟩)
      obtain ⟨r, growR, attained⟩ := anyList width q (growQ.1 _ (preserve _ (initHas zero))) positives conjunction terms
      have lengthBound : positives.length ≤ Fintype.card X := by simp [positives, Finset.card_le_univ]
      refine ⟨r, ?_, ?_⟩
      · have step := chain growQ growR
        simp only [Nat.mul_zero, Nat.add_zero] at step
        exact allowance step (Nat.add_le_add (Nat.mul_le_mul_right _ lengthBound) lengthBound)
      · convert attained using 2 with y
        apply Bool.eq_iff_iff.mpr
        simp only [id_eq, List.any_eq_true, conjunction, List.all_eq_true, List.mem_filter,
          positives, Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro hy
          exact ⟨y, hy, fun _ h => h.2⟩
        · rintro ⟨x,hx,step⟩
          exact mono x y (fun f hf h => step f ⟨hf,h⟩) target (Finset.mem_toList.mp ht) hx)
  exact ⟨net, by simpa [startNet, empty, Net.cost, PEqualNP.NotBracket.notCount] using grow.2.2,
    fun f hf => reaches f (Finset.mem_toList.mpr hf)⟩

private abbrev Row (n : Nat) := Finset (Fin n)
private abbrev Edges (n : Nat) := Finset (Fin n × Fin n)
private noncomputable def bit {n} (i : Fin n) (x : Row n) :=
  letI : ∀ Q : Prop, Decidable Q := Classical.propDecidable
  decide (i ∈ x)
private noncomputable def neg {n} (i : Fin n) (x : Row n) := !(bit i x)
private noncomputable def same {n} (e : Fin n × Fin n) (x : Row n) := bit e.1 x == bit e.2 x
private noncomputable def low {n} (e : Fin n × Fin n) (x : Row n) := neg e.1 x && neg e.2 x
private noncomputable def forward {n} (e : Fin n × Fin n) (x : Row n) := bit e.1 x && neg e.2 x
private noncomputable def backward {n} (e : Fin n × Fin n) (x : Row n) := neg e.1 x && bit e.2 x
private noncomputable def raw {n} (edges : Edges n) : Finset (Row n → Bool) :=
  letI : ∀ Q : Prop, Decidable Q := Classical.propDecidable
  {fun _ => false,fun _ => true} ∪ Finset.univ.image bit ∪ edges.image same ∪ edges.image (fun e x => !(same e x))
private noncomputable def need {n} (edges : Edges n) :=
  letI : ∀ Q : Prop, Decidable Q := Classical.propDecidable
  Finset.univ.image neg ∪ edges.image low ∪ edges.image forward ∪ edges.image backward
private noncomputable def seeds {n} (edges : Edges n) (s : Row n) :=
  letI : ∀ Q : Prop, Decidable Q := Classical.propDecidable
  (raw edges ∪ s.image neg).toList
private def Can {X : Type} (rows : Finset X) (inputs : List (X → Bool)) (goals : Finset (X → Bool)) (budget : Nat) :=
  ∃ C : Circuit, Monotone2 C ∧ NestedCover.ReadsBack inputs.length C ∧ C.output < inputs.length+C.size ∧
    C.size ≤ budget ∧ ∀ f ∈ goals, ∃ j < inputs.length+C.size, ∀ x ∈ rows, (C.wires (inputs.map (fun g => g x))).getD j false = f x

private def Keeps {n c} (edges : Edges n) (color : Fin n → Fin c) (rows : Finset (Row n)) :=
  ∀ s p, Can rows (seeds edges s) (need edges) p ↔ (∀ j, ∃ i ∈ s, color i = j) ∧ n+3*edges.card-s.card ≤ p

private def restrictF {X : Type} (rows : Finset X) (f : X → Bool) (x : ↥rows) := f x.val

private theorem fromNet {X : Type} {rows : Finset X} {inputs : List (X → Bool)} {goals : Finset (X → Bool)}
    {p : Net ((inputs.map (restrictF rows)).length)} (hn : p.cost = 0) (nonempty : inputs ≠ [])
    (achieves : ∀ f ∈ goals, p.has (inputRows (inputs.map (restrictF rows))) (restrictF rows f)) :
    Can rows inputs goals p.gates.length := by
  refine ⟨⟨p.gates,0⟩, goodNet p hn, ?_, ?_, le_rfl, ?_⟩
  · simpa using p.readsBack
  · have := List.length_pos_iff.mpr nonempty
    change 0 < inputs.length + p.gates.length
    omega
  · intro f hf
    obtain ⟨j,hj,he⟩ := achieves f hf
    refine ⟨j,by simpa [Circuit.size] using hj,fun x hx => ?_⟩
    simpa [inputRows, restrictF, List.map_map, Function.comp_def, Circuit.wires, CoverCircuit.run] using he ⟨x,hx⟩

private theorem forbiddenPair {X : Type} (rows : Finset X) (inputs : List (X → Bool)) (goals : Finset (X → Bool))
    (zero : (fun _ => false) ∈ inputs) (one : (fun _ => true) ∈ inputs)
    (impossible : ∀ budget, ¬Can rows inputs goals budget) :
    ∃ x ∈ rows, ∃ y ∈ rows, x ≠ y ∧ ∀ f ∈ inputs, f x = true → f y = true := by
  classical
  by_contra! h
  let restricted := inputs.map (restrictF rows)
  have monotone (x y : ↥rows) (ord : ∀ f ∈ restricted, f x = true → f y = true) : x = y := by
    by_contra neq
    obtain ⟨f,hf,hx,hy⟩ := h x x.property y y.property (fun eq => neq (Subtype.ext eq))
    have lift := ord _ (List.mem_map.mpr ⟨f,hf,rfl⟩) hx
    exact hy lift
  obtain ⟨p,hp,has⟩ := interpolate restricted (goals.image (restrictF rows))
    (List.mem_map.mpr ⟨_,zero,rfl⟩) (List.mem_map.mpr ⟨_,one,rfl⟩) (by
      intro x y ord f hf hx
      exact monotone x y ord ▸ hx)
  exact impossible _ (fromNet hp (fun eq => by simp [eq] at one) (fun f hf => has _ (Finset.mem_image_of_mem _ hf)))

private def Connect {n c} (E : Edges n) (color : Fin n → Fin c) :=
  ∀ Z : Row n, (∀ e ∈ E, e.1 ∈ Z ↔ e.2 ∈ Z) ↔ ∀ i j, color i = color j → (i ∈ Z ↔ j ∈ Z)

private theorem edgeColor {n c} {E : Edges n} {color : Fin n → Fin c} (h : Connect E color)
    {e} (he : e ∈ E) : color e.1 = color e.2 := by
  let fiber := Finset.univ.filter (fun i => color i = color e.1)
  have constant : ∀ i j, color i = color j → (i ∈ fiber ↔ j ∈ fiber) := by intro i j eq; simp [fiber,eq]
  have := ((h fiber).mpr constant e he).mp (by simp [fiber])
  simpa [fiber, eq_comm] using this

private theorem seedRaw {n} {E : Edges n} {s : Row n} {f} (h : f ∈ raw E) : f ∈ seeds E s := by
  simp [seeds,h]

private theorem switchPair {n c} {E : Edges n} {color : Fin n → Fin c} {A : Finset (Row n)}
    (components : Connect E color) (keeps : Keeps E color A) (j : Fin c) :
    ∃ x ∈ A, ∃ y ∈ A, (∀ i, color i = j → i ∉ x ∧ i ∈ y) ∧ (∀ i, color i ≠ j → (i ∈ x ↔ i ∈ y)) := by
  classical
  let s := Finset.univ.filter (fun i => color i ≠ j)
  obtain ⟨x,hx,y,hy,neq,ord⟩ := forbiddenPair A (seeds E s) (need E)
    (seedRaw (by simp [raw])) (seedRaw (by simp [raw])) (by
      intro budget hc
      obtain ⟨i,hi,eq⟩ := ((keeps s budget).mp hc).1 j
      simpa [s, eq] using hi)
  have sub (i) (h : i ∈ x) : i ∈ y := by
    have hw := ord (bit i) (seedRaw (by simp [raw, Finset.mem_image_of_mem])) (by simpa [bit] using h)
    simpa [bit] using hw
  have outside (i) (hj : color i ≠ j) : i ∈ x ↔ i ∈ y := by
    refine ⟨sub i, fun hi => ?_⟩
    by_contra hn
    have hw := ord (neg i) (by simp only [seeds,Finset.mem_toList,Finset.mem_union,Finset.mem_image]; exact Or.inr ⟨i,by simp [s,hj],rfl⟩) (by simp [neg, bit, hn])
    simp [neg,bit,hi] at hw
  have equalEdge (e) (he : e ∈ E) : same e x = same e y := by
    have hpos := ord (same e) (seedRaw (by simp only [raw,Finset.mem_union,Finset.mem_image]; exact Or.inl (Or.inr ⟨e,he,rfl⟩)))
    have hneg := ord (fun z => !(same e z)) (seedRaw (by simp only [raw,Finset.mem_union,Finset.mem_image]; exact Or.inr ⟨e,he,rfl⟩))
    cases h1 : same e x <;> cases h2 : same e y <;> simp_all
  have closed : ∀ e ∈ E, e.1 ∈ y \ x ↔ e.2 ∈ y \ x := by
    intro e he
    have eq := equalEdge e he
    have h1 := sub e.1
    have h2 := sub e.2
    by_cases a : e.1 ∈ x <;> by_cases b : e.1 ∈ y <;> by_cases d : e.2 ∈ x <;> by_cases k : e.2 ∈ y <;>
      simp_all [same,bit]
  obtain ⟨v,hv⟩ : (y \ x).Nonempty := by
    by_contra! empty
    apply neq
    ext i
    specialize sub i
    have := Finset.ext_iff.mp empty i
    simp at this
    exact ⟨sub,this⟩
  have changed := Finset.mem_sdiff.mp hv
  have target : color v = j := by by_contra hn; exact changed.2 ((outside v hn).mpr changed.1)
  refine ⟨x,hx,y,hy,?_,outside⟩
  intro i hi
  exact (Finset.mem_sdiff.mp (((components _).mp closed v i (target.trans hi.symm)).mp hv)).symm

private abbrev Arrows {n} (E : Edges n) := ↥E × Bool
private abbrev Tags {n} (E : Edges n) := Sum (↥E) (Arrows E)
private noncomputable def atom {n} {E : Edges n} (d : Arrows E) :=
  if d.2 then forward d.1.val else backward d.1.val
private noncomputable def signal {n} {E : Edges n} (t : Tags E) :=
  Sum.elim (fun e : ↥E => low e.val) atom t

private theorem exactColumns {n c} {E : Edges n} {color : Fin n → Fin c} {A : Finset (Row n)}
    (keeps : Keeps E color A) : Function.Injective (fun d : Arrows E => restrictF A (atom d)) ∧
    ∀ d : Arrows E, restrictF A (atom d) ≠ fun _ => false := by
  classical
  let inputs := seeds E Finset.univ
  let L := inputs.map (restrictF A)
  let rawIn := inputRows L
  let col := fun t : Tags E => restrictF A (signal t)
  let full := Finset.univ.image col
  let zero : ↥A → Bool := fun _ => false
  let pool := full.erase zero
  let init := empty L.length
  have rawHas (f : Row n → Bool) (hf : f ∈ inputs) : init.has rawIn (restrictF A f) :=
    initHas (List.mem_map.mpr ⟨f,hf,rfl⟩)
  have rawBit (i : Fin n) := rawHas (bit i) (seedRaw (by simp [raw,Finset.mem_image_of_mem]))
  have rawNeg (i : Fin n) := rawHas (neg i) (by simp [inputs,seeds])
  have rawZero : init.has rawIn zero := rawHas (fun _ => false) (seedRaw (by simp [raw]))
  have nonempty : inputs ≠ [] := by
    have hz : (fun _ => false) ∈ inputs := seedRaw (by simp [raw])
    intro eq; simp [eq] at hz
  obtain ⟨p,grows,has⟩ := batch (raw := rawIn) init pool.toList id 1 0 (by
    intro f hf q ext
    have member := Finset.mem_of_mem_erase (Finset.mem_toList.mp hf)
    obtain ⟨tag,_,rfl⟩ := Finset.mem_image.mp member
    have width (x) : (rawIn x).length = L.length := by simp [rawIn,inputRows]
    cases tag with
    | inl e => exact binary width q _ _ (ext _ (rawNeg e.val.1)) (ext _ (rawNeg e.val.2)) true
    | inr d =>
      rcases d with ⟨e,b⟩
      cases b
      · exact binary width q _ _ (ext _ (rawNeg e.val.1)) (ext _ (rawBit e.val.2)) true
      · exact binary width q _ _ (ext _ (rawBit e.val.1)) (ext _ (rawNeg e.val.2)) true)
  have allTags (t : Tags E) : p.has rawIn (col t) := by
    by_cases h : col t = zero
    · exact h ▸ grows.1 _ rawZero
    · exact has _ (Finset.mem_toList.mpr (Finset.mem_erase.mpr ⟨h,Finset.mem_image_of_mem _ (Finset.mem_univ t)⟩))
  have built : Can A inputs (need E) p.gates.length := by
    refine fromNet (by simpa [init, empty, Net.cost, PEqualNP.NotBracket.notCount] using grows.2.2) nonempty ?_
    intro f hf
    simp only [need,Finset.mem_union,Finset.mem_image,Finset.mem_univ,true_and] at hf
    rcases hf with (((⟨i,rfl⟩ | ⟨e,he,rfl⟩) | ⟨e,he,rfl⟩) | ⟨e,he,rfl⟩)
    · exact grows.1 _ (rawNeg i)
    · exact allTags (.inl ⟨e,he⟩)
    · exact allTags (.inr (⟨e,he⟩, true))
    · exact allTags (.inr (⟨e,he⟩, false))
  have minSize := ((keeps Finset.univ _).mp built).2
  have upper := grows.2.1
  simp [init,empty] at upper
  simp only [Finset.card_univ,Fintype.card_fin] at minSize
  have ht : Fintype.card (Tags E) = 3 * E.card := by simp [Tags,Arrows]; omega
  have imageBound : full.card ≤ Fintype.card (Tags E) := Finset.card_image_le.trans_eq Finset.card_univ
  have eraseBound : pool.card ≤ full.card := Finset.card_le_card (Finset.erase_subset ..)
  have fullSize : full.card = (Finset.univ : Finset (Tags E)).card := by rw [Finset.card_univ]; omega
  have inject := Finset.card_image_iff.mp fullSize
  refine ⟨fun d e h => Sum.inr.inj (inject (x₁ := Sum.inr d) (x₂ := Sum.inr e) (Finset.mem_univ _) (Finset.mem_univ _) h), ?_⟩
  intro d hz
  have hz' : zero ∈ full := Finset.mem_image.mpr ⟨Sum.inr d,Finset.mem_univ _,hz⟩
  have drop : pool.card < full.card := Finset.card_erase_lt_of_mem hz'
  omega

private theorem bound {n c} {E : Edges n} {color : Fin n → Fin c} {A : Finset (Row n)}
    (onto : Function.Surjective color) (components : Connect E color) (existsEdge : E.Nonempty) (keeps : Keeps E color A) :
    c ≤ A.card ∧ 2*E.card + Nat.choose (A.card-c) ((A.card-c)/2) + 2 ≤ 2^(A.card-c) := by
  classical
  let key := fun (x : Row n) (d : Arrows E) => atom d x
  let mark := fun (x : Row n) => Finset.univ.filter (fun j => (onto j).choose ∈ x)
  have collapse := shrinkRows A key mark (by
    intro j
    obtain ⟨x,hx,y,hy,flip,stable⟩ := switchPair components keeps j
    refine ⟨x,hx,y,hy,?_,?_,?_⟩
    · funext d
      rcases d with ⟨e,b⟩
      have sameColor := edgeColor components e.property
      by_cases h : color e.val.1 = j
      · obtain ⟨a,aa⟩ := flip _ h
        obtain ⟨b',bb⟩ := flip _ (sameColor.symm.trans h)
        cases b <;> simp [key,atom,forward,backward,bit,neg,a,aa,b',bb]
      · have a := stable _ h
        have b' := stable _ (fun eq => h (sameColor.trans eq))
        cases b <;> simp [key,atom,forward,backward,bit,neg,a,b'] <;> congr!
    · simp [mark,(flip _ (onto j).choose_spec).1]
    · ext k
      by_cases eq : k = j
      · subst k; simp [mark,(flip _ (onto j).choose_spec).2]
      · have stableRep := stable _ (fun h => eq ((onto k).choose_spec.symm.trans h))
        simp [mark,eq,stableRep])
  refine ⟨by omega, ?_⟩
  let patterns := A.image key
  have reduced : patterns.card + c ≤ A.card := by
    dsimp only [patterns]
    convert collapse using 0 <;> congr!
  let idx (x : Row n) (hx : x ∈ A) : ↥patterns := ⟨key x,Finset.mem_image_of_mem key hx⟩
  obtain ⟨place⟩ := Function.Embedding.nonempty_of_card_le (α := ↥patterns) (β := Fin (A.card-c)) (by
    simp only [Fintype.card_coe,Fintype.card_fin]
    omega)
  let support := fun d : Arrows E => (Finset.univ.filter (fun p : ↥patterns => p.val d = true)).map place
  have member (d : Arrows E) (p : ↥patterns) : place p ∈ support d ↔ p.val d = true := by simp [support]
  let reverse := fun d : Arrows E => (d.1, !d.2)
  have reverseInj : Function.Injective reverse := by rintro ⟨ea,ba⟩ ⟨eb,bb⟩ h; simpa [reverse] using h
  obtain ⟨different, used⟩ := exactColumns keeps
  have differentSet : Function.Injective support := by
    intro d e eq
    apply different
    funext x
    apply Bool.eq_iff_iff.mpr
    exact (member d (idx x x.property)).symm.trans (eq ▸ member e (idx x x.property))
  have setUsed (d) : (support d).Nonempty := by
    by_contra nh
    apply used d
    funext x
    have h : place (idx x x.property) ∉ support d := fun hm => nh ⟨_,hm⟩
    have hn := mt (member d _).mpr h
    exact Bool.eq_false_iff.mpr hn
  have room (d : Arrows E) : support d ⊂ (support (reverse d))ᶜ := by
    apply lt_of_le_of_ne
    · intro i hi
      obtain ⟨p,hp,rfl⟩ := Finset.mem_map.mp hi
      have positive := (Finset.mem_filter.mp hp).2
      apply Finset.mem_compl.mpr
      intro both
      have negative := (member _ _).mp both
      obtain ⟨x,_,he⟩ := Finset.mem_image.mp p.property
      rw [← he] at positive negative
      rcases d with ⟨e,b⟩
      cases b <;> by_cases h : e.val.1 ∈ x <;> simp [key,reverse,atom,forward,backward,neg,bit,h] at positive negative
    · intro eq
      obtain ⟨x,hx,y,hy,flip,_⟩ := switchPair components keeps (color d.1.val.1)
      obtain ⟨a,_⟩ := flip _ rfl
      obtain ⟨b,_⟩ := flip _ (edgeColor components d.1.property).symm
      have neither (flag : Bool) : place (idx x hx) ∉ support (d.1,flag) := by
        rw [member]
        cases flag <;> simp [idx,key,atom,forward,backward,bit,neg,a,b]
      have hm : place (idx x hx) ∈ support d := eq ▸ Finset.mem_compl.mpr (neither (!d.2))
      exact neither d.2 hm
  obtain ⟨e,he⟩ := existsEdge
  have total := countSupports support reverse differentSet reverseInj setUsed room ⟨(⟨e,he⟩,true)⟩
  simpa [Arrows, Nat.mul_comm] using total

end PEqualNP.Outside.L_meta_53188

theorem PEqualNP.Outside.L_meta_53188 : (∀ (n c : Nat) (E : Finset (Fin n × Fin n)) (color : Fin n → Fin c),
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
  ∀ A : Finset W, E.Nonempty → keeps A →
    c ≤ A.card ∧ 2*E.card + Nat.choose (A.card-c) ((A.card-c)/2) + 2 ≤ 2^(A.card-c)) := by
  intro n c E color ordered onto connected
  dsimp only
  intro A nonempty keeps
  have normalized : PEqualNP.Outside.L_meta_53188.Keeps E color A := by
    unfold PEqualNP.Outside.L_meta_53188.Keeps PEqualNP.Outside.L_meta_53188.Can PEqualNP.Outside.L_meta_53188.seeds PEqualNP.Outside.L_meta_53188.need PEqualNP.Outside.L_meta_53188.raw PEqualNP.Outside.L_meta_53188.backward PEqualNP.Outside.L_meta_53188.forward PEqualNP.Outside.L_meta_53188.low PEqualNP.Outside.L_meta_53188.same PEqualNP.Outside.L_meta_53188.neg PEqualNP.Outside.L_meta_53188.bit
    convert keeps using 0 <;> congr!
  exact PEqualNP.Outside.L_meta_53188.bound onto connected nonempty normalized
