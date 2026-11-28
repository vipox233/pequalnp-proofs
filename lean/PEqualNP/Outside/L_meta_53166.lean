import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53166

/-! ### Part 1: Initial Masks and Underlying 8-Vertex, 11-Edge C₄-Free Graph -/

def BAD : BitVec 21 := 2095104#21
def REQ : BitVec 21 := 2047#21

def M (i : Fin 8) : BitVec 21 :=
  match i.val with
  | 0 => 63491#21
  | 1 => 151748#21
  | 2 => 235568#21
  | 3 => 287504#21
  | 4 => 558408#21
  | 5 => 1246721#21
  | 6 => 1386508#21
  | _ => 1835170#21

def initList : List (BitVec 21) :=
  ([63491, 1386508, 235568, 0, 151748, 287504, 0, 0,
    558408, 1246721, 1835170, 0, 1246721, 1835170, 0, 0] : List Nat).map (BitVec.ofNat 21)

def adj (i j : Fin 8) : Bool := (M i &&& M j &&& BAD) == 0#21
def bitOf (i : Fin 8) : BitVec 8 := 1#8 <<< i.val
def hasBit (S : BitVec 8) (i : Fin 8) : Bool := S.getLsbD i.val
def sub8 (A B : BitVec 8) : Bool := (A &&& ~~~B) == 0#8
def pop8 (S : BitVec 8) : Nat := (List.finRange 8).countP (fun i => hasBit S i)

def nbrs (v : Fin 8) : BitVec 8 :=
  (List.finRange 8).foldl (fun acc u => if adj v u then acc ||| bitOf u else acc) 0#8

def orMask (S : BitVec 8) : BitVec 21 :=
  (List.finRange 8).foldl (fun acc i => if hasBit S i then acc ||| M i else acc) 0#21

def edgeU (e : Fin 11) : Fin 8 :=
  match e.val with
  | 0 => ⟨0, by decide⟩
  | 1 => ⟨0, by decide⟩
  | 2 => ⟨1, by decide⟩
  | 3 => ⟨4, by decide⟩
  | 4 => ⟨2, by decide⟩
  | 5 => ⟨2, by decide⟩
  | 6 => ⟨1, by decide⟩
  | 7 => ⟨1, by decide⟩
  | 8 => ⟨3, by decide⟩
  | 9 => ⟨3, by decide⟩
  | _ => ⟨4, by decide⟩

def edgeV (e : Fin 11) : Fin 8 :=
  match e.val with
  | 0 => ⟨5, by decide⟩
  | 1 => ⟨7, by decide⟩
  | 2 => ⟨6, by decide⟩
  | 3 => ⟨6, by decide⟩
  | 4 => ⟨3, by decide⟩
  | 5 => ⟨7, by decide⟩
  | 6 => ⟨4, by decide⟩
  | 7 => ⟨7, by decide⟩
  | 8 => ⟨4, by decide⟩
  | 9 => ⟨5, by decide⟩
  | _ => ⟨5, by decide⟩

lemma adj_symm : ∀ i j : Fin 8, adj i j = adj j i := by decide
lemma adj_irrefl : ∀ i : Fin 8, adj i i = false := by decide
lemma adj_c4_free : ∀ u v a b : Fin 8, u ≠ v → a ≠ b →
    adj u a = true → adj u b = true → adj v a = true → adj v b = true → False := by decide

lemma hasBit_nbrs : ∀ v u : Fin 8, hasBit (nbrs v) u = adj v u := by decide
lemma M_not_clean : ∀ i : Fin 8, (M i &&& BAD) ≠ 0#21 := by decide
lemma deg_le_4 : ∀ v : Fin 8, pop8 (nbrs v) ≤ 4 := by decide

lemma edge_ne : ∀ e : Fin 11, edgeU e ≠ edgeV e := by decide
lemma edge_adj : ∀ e : Fin 11, adj (edgeU e) (edgeV e) = true := by decide
lemma edge_M_bit : ∀ (e : Fin 11) (i : Fin 8),
    (M i).getLsbD e.val = (i == edgeU e || i == edgeV e) := by decide
lemma edge_inj : ∀ e1 e2 : Fin 11,
    ((edgeU e1 = edgeU e2 ∧ edgeV e1 = edgeV e2) ∨
     (edgeU e1 = edgeV e2 ∧ edgeV e1 = edgeU e2)) → e1 = e2 := by decide
lemma edge_exists : ∀ u v : Fin 8, adj u v = true →
    ∃ e : Fin 11, (edgeU e = u ∧ edgeV e = v) ∨ (edgeU e = v ∧ edgeV e = u) := by decide

lemma hasBit_bitOf : ∀ i j : Fin 8, hasBit (bitOf i) j = (i == j) := by decide
lemma hasBit_zero : ∀ i : Fin 8, hasBit 0#8 i = false := by decide
lemma hasBit_or (A B : BitVec 8) (i : Fin 8) :
    hasBit (A ||| B) i = (hasBit A i || hasBit B i) := by simp [hasBit]
lemma hasBit_and (A B : BitVec 8) (i : Fin 8) :
    hasBit (A &&& B) i = (hasBit A i && hasBit B i) := by simp [hasBit]
lemma hasBit_not (A : BitVec 8) (i : Fin 8) :
    hasBit (~~~A) i = !hasBit A i := by simp [hasBit, i.isLt]

lemma sub8_iff (A B : BitVec 8) :
    sub8 A B = true ↔ ∀ i : Fin 8, hasBit A i = true → hasBit B i = true := by
  simp only [sub8, beq_iff_eq, hasBit]
  constructor
  · intro h i hi
    have h0 : (A &&& ~~~B).getLsbD i.val = false := by rw [h]; simp
    simp [i.isLt, hi] at h0; exact h0
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    have hki : hasBit A ⟨k, hk⟩ = true → hasBit B ⟨k, hk⟩ = true := h ⟨k, hk⟩
    simp only [hasBit] at hki
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_zero, hk, decide_true, Bool.true_and]
    cases ha : A.getLsbD k
    · simp
    · simp [hki ha]

lemma sub8_refl (A : BitVec 8) : sub8 A A = true := (sub8_iff A A).mpr fun _ h => h

lemma eq_zero_of_no_bit (S : BitVec 8) (h : ∀ i : Fin 8, hasBit S i = false) : S = 0#8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  simpa [hasBit] using h ⟨k, hk⟩

lemma exists_bit_of_ne_zero (S : BitVec 8) (h : S ≠ 0#8) : ∃ i : Fin 8, hasBit S i = true := by
  by_contra hno
  apply h; apply eq_zero_of_no_bit; intro i
  cases hb : hasBit S i
  · rfl
  · exact absurd ⟨i, hb⟩ hno

lemma orMask_zero : orMask 0#8 = 0#21 := by decide
lemma orMask_bitOf : ∀ i : Fin 8, orMask (bitOf i) = M i := by decide

lemma foldl_or_getLsbD (l : List (Fin 8)) (S : BitVec 8) (acc : BitVec 21) (k : Nat) :
    (l.foldl (fun a i => if hasBit S i then a ||| M i else a) acc).getLsbD k =
      (acc.getLsbD k || l.any (fun i => hasBit S i && (M i).getLsbD k)) := by
  induction l generalizing acc with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, List.any_cons, ih]
    cases hasBit S x <;> simp [Bool.or_assoc]

lemma orMask_getLsbD (S : BitVec 8) (k : Nat) :
    (orMask S).getLsbD k = (List.finRange 8).any (fun i => hasBit S i && (M i).getLsbD k) := by
  unfold orMask; rw [foldl_or_getLsbD]; simp

lemma orMask_or (A B : BitVec 8) : orMask (A ||| B) = orMask A ||| orMask B := by
  apply BitVec.eq_of_getLsbD_eq
  intro k _
  rw [BitVec.getLsbD_or, orMask_getLsbD, orMask_getLsbD, orMask_getLsbD]
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, Bool.and_eq_true, Bool.or_eq_true, hasBit_or]
  constructor
  · rintro ⟨i, hi, (ha | hb), hm⟩
    · exact Or.inl ⟨i, hi, ha, hm⟩
    · exact Or.inr ⟨i, hi, hb, hm⟩
  · rintro (⟨i, hi, ha, hm⟩ | ⟨i, hi, hb, hm⟩)
    · exact ⟨i, hi, Or.inl ha, hm⟩
    · exact ⟨i, hi, Or.inr hb, hm⟩

lemma orMask_mono_bit (S : BitVec 8) (i : Fin 8) (hi : hasBit S i = true) (k : Nat)
    (hm : (M i).getLsbD k = true) : (orMask S).getLsbD k = true := by
  rw [orMask_getLsbD, List.any_eq_true]
  exact ⟨i, List.mem_finRange i, by simp [hi, hm]⟩

lemma orMask_and_of_sub (A B : BitVec 8) (h : sub8 A B = true) :
    orMask A &&& orMask B = orMask A := by
  rw [sub8_iff] at h
  apply BitVec.eq_of_getLsbD_eq
  intro k _
  rw [BitVec.getLsbD_and]
  cases ha : (orMask A).getLsbD k
  · simp
  · rw [orMask_getLsbD, List.any_eq_true] at ha
    rcases ha with ⟨i, _, hi⟩
    simp only [Bool.and_eq_true] at hi
    rw [orMask_mono_bit B i (h i hi.1) k hi.2]; rfl

lemma orMask_edge_bit (S : BitVec 8) (e : Fin 11) :
    (orMask S).getLsbD e.val = (hasBit S (edgeU e) || hasBit S (edgeV e)) := by
  rw [orMask_getLsbD]
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, Bool.and_eq_true, Bool.or_eq_true, edge_M_bit, beq_iff_eq]
  constructor
  · rintro ⟨i, _, hi, rfl | rfl⟩
    · exact Or.inl hi
    · exact Or.inr hi
  · rintro (hu | hv)
    · exact ⟨edgeU e, List.mem_finRange _, hu, Or.inl rfl⟩
    · exact ⟨edgeV e, List.mem_finRange _, hv, Or.inr rfl⟩

/-! ### Part 2: Clean Pair and Clean Triple Structural Lemmas -/

lemma clean_pair_adj (A B : BitVec 8) (hclean : (orMask A &&& orMask B &&& BAD) = 0#21) :
    ∀ a b : Fin 8, hasBit A a = true → hasBit B b = true → adj a b = true := by
  intro a b ha hb
  simp only [adj, beq_iff_eq]
  apply BitVec.eq_of_getLsbD_eq
  intro k _
  rw [BitVec.getLsbD_and, BitVec.getLsbD_and, BitVec.getLsbD_zero]
  cases hma : (M a).getLsbD k
  · simp
  · cases hmb : (M b).getLsbD k
    · simp
    · cases hbd : BAD.getLsbD k
      · simp
      · have h0 : (orMask A &&& orMask B &&& BAD).getLsbD k = false := by rw [hclean]; simp
        rw [BitVec.getLsbD_and, BitVec.getLsbD_and, orMask_mono_bit A a ha k hma,
          orMask_mono_bit B b hb k hmb, hbd] at h0
        simp at h0

lemma pop8_eq_zero_iff (S : BitVec 8) : pop8 S = 0 ↔ S = 0#8 := by
  constructor
  · intro h
    apply eq_zero_of_no_bit; intro i
    have h0 : ∀ x ∈ List.finRange 8, hasBit S x = false := by
      simpa [pop8, List.countP_eq_zero] using h
    exact h0 i (List.mem_finRange i)
  · rintro rfl; decide

lemma pop8_le_one_iff (S : BitVec 8) :
    pop8 S ≤ 1 ↔ ∀ a b : Fin 8, hasBit S a = true → hasBit S b = true → a = b := by
  constructor
  · intro h a b ha hb
    by_contra hne
    have hge : 2 ≤ pop8 S := by
      have hsub : ∀ l : List (Fin 8), l.Nodup → a ∈ l → b ∈ l → a ≠ b →
          2 ≤ l.countP (fun i => hasBit S i) := by
        intro l hnd ha' hb' hne'
        induction l with
        | nil => simp at ha'
        | cons x xs ih =>
          rw [List.nodup_cons] at hnd
          simp only [List.mem_cons] at ha' hb'
          simp only [List.countP_cons]
          rcases ha' with rfl | hax
          · rcases hb' with rfl | hbx
            · exact absurd rfl hne'
            · simp only [ha, ↓reduceIte]
              have h1 : 0 < xs.countP (fun i => hasBit S i) := List.countP_pos_iff.mpr ⟨b, hbx, hb⟩
              omega
          · rcases hb' with rfl | hbx
            · simp only [hb, ↓reduceIte]
              have h1 : 0 < xs.countP (fun i => hasBit S i) := List.countP_pos_iff.mpr ⟨a, hax, ha⟩
              omega
            · have := ih hnd.2 hax hbx
              cases hx : hasBit S x <;> simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero] <;> omega
      exact hsub (List.finRange 8) (List.nodup_finRange 8) (List.mem_finRange a) (List.mem_finRange b) hne
    omega
  · intro h
    by_cases h0 : S = 0#8
    · rw [h0]; decide
    · obtain ⟨a, ha⟩ := exists_bit_of_ne_zero S h0
      have hS : S = bitOf a := by
        apply BitVec.eq_of_getLsbD_eq
        intro k hk
        change hasBit S ⟨k, hk⟩ = hasBit (bitOf a) ⟨k, hk⟩
        rw [hasBit_bitOf]
        cases hb : hasBit S ⟨k, hk⟩
        · exact (beq_false_of_ne fun heq => by rw [← heq] at hb; rw [ha] at hb; contradiction).symm
        · simp [h a ⟨k, hk⟩ ha hb]
      rw [hS]
      have hpop1 : ∀ i : Fin 8, pop8 (bitOf i) = 1 := by decide
      rw [hpop1 a]

lemma exists_two_of_pop8_ge_2 (S : BitVec 8) (h : 2 ≤ pop8 S) :
    ∃ a b : Fin 8, a ≠ b ∧ hasBit S a = true ∧ hasBit S b = true := by
  by_contra hno
  have hle : pop8 S ≤ 1 := (pop8_le_one_iff S).mpr fun a b ha hb => by
    by_contra hne; exact hno ⟨a, b, hne, ha, hb⟩
  omega

lemma pop8_eq_one_iff (S : BitVec 8) : pop8 S = 1 ↔ ∃ a : Fin 8, S = bitOf a := by
  constructor
  · intro h
    have hne : S ≠ 0#8 := fun hz => by rw [hz] at h; exact absurd h (by decide)
    obtain ⟨a, ha⟩ := exists_bit_of_ne_zero S hne
    refine ⟨a, ?_⟩
    have huniq := (pop8_le_one_iff S).mp (by omega)
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    change hasBit S ⟨k, hk⟩ = hasBit (bitOf a) ⟨k, hk⟩
    rw [hasBit_bitOf]
    cases hb : hasBit S ⟨k, hk⟩
    · exact (beq_false_of_ne fun heq => by rw [← heq] at hb; rw [ha] at hb; contradiction).symm
    · simp [huniq a ⟨k, hk⟩ ha hb]
  · rintro ⟨a, rfl⟩
    have hpop1 : ∀ i : Fin 8, pop8 (bitOf i) = 1 := by decide
    exact hpop1 a

lemma pop8_le_of_sub (A B : BitVec 8) (h : sub8 A B = true) : pop8 A ≤ pop8 B := by
  rw [sub8_iff] at h; unfold pop8
  have hgen : ∀ l : List (Fin 8), l.countP (fun i => hasBit A i) ≤ l.countP (fun i => hasBit B i) := by
    intro l; induction l with
    | nil => simp
    | cons x xs ih =>
      simp only [List.countP_cons]
      cases ha : hasBit A x
      · cases hb : hasBit B x <;> simp [ha, hb] <;> omega
      · have hb := h x ha; simp [ha, hb]; omega
  exact hgen (List.finRange 8)

lemma pop8_split (A B : BitVec 8) :
    pop8 (A &&& B) + pop8 (A &&& ~~~B) = pop8 A := by
  unfold pop8
  have hgen : ∀ l : List (Fin 8),
      l.countP (fun i => hasBit (A &&& B) i) + l.countP (fun i => hasBit (A &&& ~~~B) i) =
      l.countP (fun i => hasBit A i) := by
    intro l; induction l with
    | nil => simp
    | cons x xs ih =>
      rw [List.countP_cons, List.countP_cons, List.countP_cons, hasBit_and, hasBit_and, hasBit_not]
      cases ha : hasBit A x <;> cases hb : hasBit B x <;>
        simp only [Bool.false_and, Bool.true_and, Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] <;>
        omega
  exact hgen (List.finRange 8)

lemma pop8_lt_of_not_sub (A B : BitVec 8) (h : sub8 A B = false) :
    pop8 (A &&& B) + 1 ≤ pop8 A := by
  have hne : (A &&& ~~~B) ≠ 0#8 := by
    intro hz; simp [sub8, hz] at h
  have hpos : 1 ≤ pop8 (A &&& ~~~B) := by
    by_contra hlt
    have h0 : pop8 (A &&& ~~~B) = 0 := by omega
    exact hne ((pop8_eq_zero_iff _).mp h0)
  have hsp := pop8_split A B
  omega

lemma pop8_or_le (A B : BitVec 8) : pop8 (A ||| B) ≤ pop8 A + pop8 B := by
  unfold pop8
  have hgen : ∀ l : List (Fin 8),
      l.countP (fun i => hasBit (A ||| B) i) ≤
        l.countP (fun i => hasBit A i) + l.countP (fun i => hasBit B i) := by
    intro l; induction l with
    | nil => simp
    | cons x xs ih =>
      rw [List.countP_cons, List.countP_cons, List.countP_cons, hasBit_or]
      cases ha : hasBit A x <;> cases hb : hasBit B x <;>
        simp only [Bool.false_or, Bool.true_or, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] <;>
        omega
  exact hgen (List.finRange 8)

lemma pop8_inter_nbrs_le_one (u v : Fin 8) (hne : u ≠ v) :
    pop8 (nbrs u &&& nbrs v) ≤ 1 := by
  rw [pop8_le_one_iff]
  intro a b ha hb
  simp only [hasBit_and, Bool.and_eq_true, hasBit_nbrs] at ha hb
  by_contra hab
  exact adj_c4_free u v a b hne hab ha.1 hb.1 ha.2 hb.2

lemma star_center_unique (S : BitVec 8) (hge : 2 ≤ pop8 S) (u v : Fin 8)
    (hu : sub8 S (nbrs u) = true) (hv : sub8 S (nbrs v) = true) : u = v := by
  obtain ⟨a, b, hab, ha, hb⟩ := exists_two_of_pop8_ge_2 S hge
  rw [sub8_iff] at hu hv
  by_contra huv
  exact adj_c4_free u v a b huv hab
    (by simpa [hasBit_nbrs] using hu a ha)
    (by simpa [hasBit_nbrs] using hu b hb)
    (by simpa [hasBit_nbrs] using hv a ha)
    (by simpa [hasBit_nbrs] using hv b hb)

lemma clean_pair_is_star (A B : BitVec 8) (hclean : (orMask A &&& orMask B &&& BAD) = 0#21)
    (hA : A ≠ 0#8) (hB : B ≠ 0#8) :
    (∃ u : Fin 8, A = bitOf u ∧ sub8 B (nbrs u) = true) ∨
    (∃ v : Fin 8, B = bitOf v ∧ sub8 A (nbrs v) = true) := by
  have hadj := clean_pair_adj A B hclean
  by_cases hA1 : pop8 A ≤ 1
  · left
    have hAeq : pop8 A = 1 := by
      have hne0 : pop8 A ≠ 0 := fun hz => hA ((pop8_eq_zero_iff A).mp hz)
      omega
    obtain ⟨u, rfl⟩ := (pop8_eq_one_iff A).mp hAeq
    refine ⟨u, rfl, (sub8_iff B (nbrs u)).mpr fun b hb => ?_⟩
    rw [hasBit_nbrs]; exact hadj u b (by simp [hasBit_bitOf]) hb
  · right
    have hA2 : 2 ≤ pop8 A := by omega
    obtain ⟨a1, a2, ha12, ha1, ha2⟩ := exists_two_of_pop8_ge_2 A hA2
    have hB1 : pop8 B ≤ 1 := (pop8_le_one_iff B).mpr fun b1 b2 hb1 hb2 => by
      by_contra hb12
      exact adj_c4_free a1 a2 b1 b2 ha12 hb12 (hadj a1 b1 ha1 hb1) (hadj a1 b2 ha1 hb2)
        (hadj a2 b1 ha2 hb1) (hadj a2 b2 ha2 hb2)
    have hBeq : pop8 B = 1 := by
      have hne0 : pop8 B ≠ 0 := fun hz => hB ((pop8_eq_zero_iff B).mp hz)
      omega
    obtain ⟨v, rfl⟩ := (pop8_eq_one_iff B).mp hBeq
    refine ⟨v, rfl, (sub8_iff A (nbrs v)).mpr fun a ha => ?_⟩
    rw [hasBit_nbrs, adj_symm]; exact hadj a v ha (by simp [hasBit_bitOf])

lemma clean_triple_disj (A B C : BitVec 8)
    (hclean : (orMask A &&& orMask B &&& orMask C &&& BAD) = 0#21) :
    ∀ i : Fin 8, ¬ (hasBit A i = true ∧ hasBit B i = true ∧ hasBit C i = true) := by
  intro i ⟨ha, hb, hc⟩
  apply M_not_clean i
  apply BitVec.eq_of_getLsbD_eq
  intro k _
  rw [BitVec.getLsbD_and, BitVec.getLsbD_zero]
  cases hm : (M i).getLsbD k
  · simp
  · cases hbd : BAD.getLsbD k
    · simp
    · have h0 : (orMask A &&& orMask B &&& orMask C &&& BAD).getLsbD k = false := by
        rw [hclean]; simp
      rw [BitVec.getLsbD_and, BitVec.getLsbD_and, BitVec.getLsbD_and,
        orMask_mono_bit A i ha k hm, orMask_mono_bit B i hb k hm,
        orMask_mono_bit C i hc k hm, hbd] at h0
      simp at h0

lemma clean_triple_adj_AB (A B C : BitVec 8)
    (hclean : (orMask A &&& orMask B &&& orMask C &&& BAD) = 0#21) :
    ∀ x c : Fin 8, hasBit A x = true → hasBit B x = true → hasBit C c = true → adj x c = true := by
  intro x c hax hbx hcc
  simp only [adj, beq_iff_eq]
  apply BitVec.eq_of_getLsbD_eq
  intro k _
  rw [BitVec.getLsbD_and, BitVec.getLsbD_and, BitVec.getLsbD_zero]
  cases hmx : (M x).getLsbD k
  · simp
  · cases hmc : (M c).getLsbD k
    · simp
    · cases hbd : BAD.getLsbD k
      · simp
      · have h0 : (orMask A &&& orMask B &&& orMask C &&& BAD).getLsbD k = false := by
          rw [hclean]; simp
        rw [BitVec.getLsbD_and, BitVec.getLsbD_and, BitVec.getLsbD_and,
          orMask_mono_bit A x hax k hmx, orMask_mono_bit B x hbx k hmx,
          orMask_mono_bit C c hcc k hmc, hbd] at h0
        simp at h0

lemma clean_triple_adj_AC (A B C : BitVec 8)
    (hclean : (orMask A &&& orMask B &&& orMask C &&& BAD) = 0#21) :
    ∀ y b : Fin 8, hasBit A y = true → hasBit C y = true → hasBit B b = true → adj y b = true := by
  intro y b hay hcy hbb
  have hclean' : (orMask A &&& orMask C &&& orMask B &&& BAD) = 0#21 := by
    rw [← hclean]; apply BitVec.eq_of_getLsbD_eq; intro k _
    simp [Bool.and_left_comm, Bool.and_comm, Bool.and_assoc]
  exact clean_triple_adj_AB A C B hclean' y b hay hcy hbb

lemma clean_triple_adj_BC (A B C : BitVec 8)
    (hclean : (orMask A &&& orMask B &&& orMask C &&& BAD) = 0#21) :
    ∀ z a : Fin 8, hasBit B z = true → hasBit C z = true → hasBit A a = true → adj z a = true := by
  intro z a hbz hcz haa
  have hclean' : (orMask B &&& orMask C &&& orMask A &&& BAD) = 0#21 := by
    rw [← hclean]; apply BitVec.eq_of_getLsbD_eq; intro k _
    simp [Bool.and_left_comm, Bool.and_comm, Bool.and_assoc]
  exact clean_triple_adj_AB B C A hclean' z a hbz hcz haa

lemma clean_triple_edge_decomp (A B C : BitVec 8)
    (hclean : (orMask A &&& orMask B &&& orMask C &&& BAD) = 0#21)
    (e : Fin 11) (he : (orMask A &&& orMask B &&& orMask C).getLsbD e.val = true) :
    (∃ x : Fin 8, hasBit A x = true ∧ hasBit B x = true ∧
      ((edgeU e = x ∧ hasBit C (edgeV e) = true) ∨ (edgeV e = x ∧ hasBit C (edgeU e) = true))) ∨
    (∃ y : Fin 8, hasBit A y = true ∧ hasBit C y = true ∧
      ((edgeU e = y ∧ hasBit B (edgeV e) = true) ∨ (edgeV e = y ∧ hasBit B (edgeU e) = true))) ∨
    (∃ z : Fin 8, hasBit B z = true ∧ hasBit C z = true ∧
      ((edgeU e = z ∧ hasBit A (edgeV e) = true) ∨ (edgeV e = z ∧ hasBit A (edgeU e) = true))) := by
  simp only [BitVec.getLsbD_and, Bool.and_eq_true, orMask_edge_bit, Bool.or_eq_true] at he
  rcases he with ⟨⟨hAu | hAv, hBu | hBv⟩, hCu | hCv⟩
  · exact absurd ⟨hAu, hBu, hCu⟩ (clean_triple_disj A B C hclean (edgeU e))
  · exact Or.inl ⟨edgeU e, hAu, hBu, Or.inl ⟨rfl, hCv⟩⟩
  · exact Or.inr (Or.inl ⟨edgeU e, hAu, hCu, Or.inl ⟨rfl, hBv⟩⟩)
  · exact Or.inr (Or.inr ⟨edgeV e, hBv, hCv, Or.inr ⟨rfl, hAu⟩⟩)
  · exact Or.inr (Or.inr ⟨edgeU e, hBu, hCu, Or.inl ⟨rfl, hAv⟩⟩)
  · exact Or.inr (Or.inl ⟨edgeV e, hAv, hCv, Or.inr ⟨rfl, hBu⟩⟩)
  · exact Or.inl ⟨edgeV e, hAv, hBv, Or.inr ⟨rfl, hCu⟩⟩
  · exact absurd ⟨hAv, hBv, hCv⟩ (clean_triple_disj A B C hclean (edgeV e))

/-! ### Part 3: Generalized Partition (Component-Merging) Counting Infrastructure -/

def firstBit (S : BitVec 8) : Fin 8 :=
  match (List.finRange 8).find? (fun i => hasBit S i) with
  | some i => i
  | none => ⟨0, by decide⟩

lemma firstBit_mem (S : BitVec 8) (h : S ≠ 0#8) : hasBit S (firstBit S) = true := by
  unfold firstBit
  cases hf : (List.finRange 8).find? (fun i => hasBit S i) with
  | some i => exact List.find?_some hf
  | none =>
    obtain ⟨j, hj⟩ := exists_bit_of_ne_zero S h
    have hnone := List.find?_eq_none.mp hf j (List.mem_finRange j)
    simp [hj] at hnone

def isMergeIn (mask : BitVec 8) (p : BitVec 8 × BitVec 8) : Bool :=
  (p.1 != 0#8) && (p.2 != 0#8) && decide (2 ≤ pop8 (p.1 ||| p.2)) && sub8 (p.1 ||| p.2) mask

def isMergeFor (v : Fin 8) (p : BitVec 8 × BitVec 8) : Bool := isMergeIn (nbrs v) p

def mergeStepIn (mask : BitVec 8) (c : Fin 8 → Fin 8) (p : BitVec 8 × BitVec 8) : Fin 8 → Fin 8 :=
  if isMergeIn mask p then
    let c1 := c (firstBit p.1)
    let c2 := c (firstBit p.2)
    fun u => if c u == c2 then c1 else c u
  else c

def buildCompIn (mask : BitVec 8) (gs : List (BitVec 8 × BitVec 8)) : Fin 8 → Fin 8 :=
  gs.foldl (mergeStepIn mask) id

def buildComp (v : Fin 8) (gs : List (BitVec 8 × BitVec 8)) : Fin 8 → Fin 8 :=
  buildCompIn (nbrs v) gs

def dedup {α : Type} [BEq α] : List α → List α
  | [] => []
  | a :: l => if l.any (fun x => x == a) then dedup l else a :: dedup l

lemma mem_dedup {α : Type} [BEq α] [LawfulBEq α] (l : List α) (y : α) :
    y ∈ dedup l ↔ y ∈ l := by
  induction l with
  | nil => simp [dedup]
  | cons a as ih =>
    simp only [dedup]
    cases ha : as.any (fun x => x == a)
    · simp only [Bool.false_eq_true, ↓reduceIte, List.mem_cons, ih]
    · simp only [↓reduceIte, List.mem_cons, ih]
      have hmem : a ∈ as := by
        rw [List.any_eq_true] at ha; rcases ha with ⟨x, hx, hxe⟩
        rw [beq_iff_eq] at hxe; exact hxe ▸ hx
      constructor
      · intro hy; exact Or.inr hy
      · rintro (rfl | hy); exact hmem; exact hy

lemma nodup_dedup {α : Type} [BEq α] [LawfulBEq α] (l : List α) : (dedup l).Nodup := by
  induction l with
  | nil => simp [dedup]
  | cons a as ih =>
    simp only [dedup]
    cases ha : as.any (fun x => x == a)
    · simp only [Bool.false_eq_true, ↓reduceIte, List.nodup_cons]
      refine ⟨fun hm => ?_, ih⟩
      have hmem : a ∈ as := (mem_dedup as a).mp hm
      have ht : as.any (fun x => x == a) = true := List.any_eq_true.mpr ⟨a, hmem, by simp⟩
      rw [ht] at ha; contradiction
    · simp only [↓reduceIte]; exact ih

lemma dedup_eq_self_of_nodup {α : Type} [BEq α] [LawfulBEq α] (l : List α) (h : l.Nodup) :
    dedup l = l := by
  induction l with
  | nil => simp [dedup]
  | cons a as ih =>
    rw [List.nodup_cons] at h
    have hfa : as.any (fun x => x == a) = false := by
      cases hf : as.any (fun x => x == a)
      · rfl
      · exfalso; rw [List.any_eq_true] at hf; rcases hf with ⟨x, hx, hxe⟩
        rw [beq_iff_eq] at hxe; exact h.1 (hxe ▸ hx)
    simp only [dedup, hfa, Bool.false_eq_true, ↓reduceIte, ih h.2]

def imgLenIn (mask : BitVec 8) (c : Fin 8 → Fin 8) : Nat :=
  (dedup (((List.finRange 8).filter (fun u => hasBit mask u)).map c)).length

def imgLen (v : Fin 8) (c : Fin 8 → Fin 8) : Nat := imgLenIn (nbrs v) c

lemma countP_add_not {α : Type} (l : List α) (p : α → Bool) :
    l.countP p + l.countP (fun x => !p x) = l.length := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.countP_cons, List.length_cons]
    cases hx : p x <;> simp [hx] <;> omega

lemma countP_le_sub_one {α : Type} (l : List α) (p : α → Bool) (x : α) (hx : x ∈ l) (hf : p x = false) :
    l.countP p + 1 ≤ l.length := by
  have hs := countP_add_not l p
  have hpos : 0 < l.countP (fun y => !p y) := List.countP_pos_iff.mpr ⟨x, hx, by simp [hf]⟩
  omega

lemma countP_le_sub_two_idx {α : Type} (l : List α) (p : α → Bool) (a b : Nat)
    (ha : a < l.length) (hb : b < l.length) (hne : a ≠ b)
    (hfa : p l[a] = false) (hfb : p l[b] = false) :
    l.countP p + 2 ≤ l.length := by
  induction l generalizing a b with
  | nil => simp at ha
  | cons x xs ih =>
    simp only [List.countP_cons, List.length_cons]
    cases a with
    | zero =>
      cases b with
      | zero => exact absurd rfl hne
      | succ b' =>
        have hb' : b' < xs.length := by simpa using hb
        have hfb' : p xs[b'] = false := by simpa using hfb
        have hfa' : p x = false := by simpa using hfa
        have h1 := countP_le_sub_one xs p xs[b'] (List.getElem_mem hb') hfb'
        rw [hfa']; simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]; omega
    | succ a' =>
      cases b with
      | zero =>
        have ha' : a' < xs.length := by simpa using ha
        have hfa' : p xs[a'] = false := by simpa using hfa
        have hfb' : p x = false := by simpa using hfb
        have h1 := countP_le_sub_one xs p xs[a'] (List.getElem_mem ha') hfa'
        rw [hfb']; simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]; omega
      | succ b' =>
        have h2 := ih a' b' (by simpa using ha) (by simpa using hb) (by omega)
          (by simpa using hfa) (by simpa using hfb)
        cases hx : p x <;> simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero] <;> omega

lemma countP_le_sub_two_mem {α : Type} (l : List α) (p : α → Bool) (x y : α)
    (hx : x ∈ l) (hy : y ∈ l) (hne : x ≠ y) (hfx : p x = false) (hfy : p y = false) :
    l.countP p + 2 ≤ l.length := by
  obtain ⟨a, ha, rfl⟩ := List.mem_iff_getElem.mp hx
  obtain ⟨b, hb, rfl⟩ := List.mem_iff_getElem.mp hy
  exact countP_le_sub_two_idx l p a b ha hb (fun hab => hne (by subst hab; rfl)) hfx hfy

lemma sum_ite_eq_zero_of_all_false {α : Type} (l : List α) (p : α → Bool)
    (h : ∀ x ∈ l, p x = false) : (l.map (fun x => if p x then 1 else 0)).sum = 0 := by
  induction l with
  | nil => simp
  | cons a as ih =>
    simp only [List.map_cons, List.sum_cons, h a List.mem_cons_self, Bool.false_eq_true, ↓reduceIte,
      Nat.zero_add]
    exact ih (fun y hy => h y (List.mem_cons_of_mem a hy))

lemma count_le_sum_countP_aux {α : Type} (l : List α) (f : Fin 8 → α → Bool)
    (hdisj : ∀ x ∈ l, ∀ u v : Fin 8, f u x = true → f v x = true → u = v) :
    ((List.finRange 8).map (fun v => l.countP (f v))).sum ≤ l.length := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    have hxs := ih (fun y hy => hdisj y (List.mem_cons_of_mem x hy))
    have hx1 : ((List.finRange 8).map (fun v => if f v x then 1 else 0)).sum ≤ 1 := by
      have huniq := hdisj x List.mem_cons_self
      have hgen : ∀ (L : List (Fin 8)), L.Nodup →
          (L.map (fun v => if f v x then 1 else 0)).sum ≤ 1 := by
        intro L hnd
        induction L with
        | nil => simp
        | cons a as iha =>
          rw [List.nodup_cons] at hnd
          simp only [List.map_cons, List.sum_cons]
          cases hfa : f a x
          · simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add]; exact iha hnd.2
          · simp only [↓reduceIte]
            have hzero : (as.map (fun v => if f v x then 1 else 0)).sum = 0 :=
              sum_ite_eq_zero_of_all_false as (fun v => f v x) fun b hb => by
                cases hfb : f b x
                · rfl
                · exact absurd (huniq a b hfa hfb ▸ hb) hnd.1
            omega
      exact hgen (List.finRange 8) (List.nodup_finRange 8)
    have hsplit : ∀ (L : List (Fin 8)),
        (L.map (fun v => (x :: xs).countP (f v))).sum =
        (L.map (fun v => if f v x then 1 else 0)).sum + (L.map (fun v => xs.countP (f v))).sum := by
      intro L; induction L with
      | nil => simp
      | cons a as iha =>
        simp only [List.map_cons, List.sum_cons, List.countP_cons]
        cases f a x <;> simp <;> omega
    rw [hsplit (List.finRange 8), List.length_cons]
    omega

lemma isMergeFor_unique (p : BitVec 8 × BitVec 8) (u v : Fin 8)
    (hu : isMergeFor u p = true) (hv : isMergeFor v p = true) : u = v := by
  simp only [isMergeFor, isMergeIn, Bool.and_eq_true, decide_eq_true_eq] at hu hv
  exact star_center_unique (p.1 ||| p.2) hu.1.2 u v hu.2 hv.2

lemma sum_isMergeFor_le_countP (gs : List (BitVec 8 × BitVec 8)) (pPred : (BitVec 8 × BitVec 8) → Bool)
    (himp : ∀ p ∈ gs, ∀ v : Fin 8, isMergeFor v p = true → pPred p = true) :
    ((List.finRange 8).map (fun v => gs.countP (isMergeFor v))).sum ≤ gs.countP pPred := by
  have hfilt : ∀ v : Fin 8, gs.countP (isMergeFor v) = (gs.filter pPred).countP (isMergeFor v) := by
    intro v
    have hgen : ∀ l : List (BitVec 8 × BitVec 8),
        (∀ p ∈ l, isMergeFor v p = true → pPred p = true) →
        l.countP (isMergeFor v) = (l.filter pPred).countP (isMergeFor v) := by
      intro l hl; induction l with
      | nil => simp
      | cons x xs ih =>
        simp only [List.countP_cons, List.filter_cons]
        have hxs := ih (fun p hp => hl p (List.mem_cons_of_mem x hp))
        cases hx : isMergeFor v x
        · cases pPred x <;> simp [hx, hxs]
        · have hp : pPred x = true := hl x List.mem_cons_self hx
          simp [hp, hx, hxs]
    exact hgen gs (fun p hp => himp p hp v)
  have hsum_eq : ((List.finRange 8).map (fun v => gs.countP (isMergeFor v))).sum =
      ((List.finRange 8).map (fun v => (gs.filter pPred).countP (isMergeFor v))).sum := by
    congr 1; apply List.map_congr_left; intro v _; exact hfilt v
  rw [hsum_eq, List.countP_eq_length_filter]
  exact count_le_sum_countP_aux (gs.filter pPred) isMergeFor (fun p _ => isMergeFor_unique p)

lemma sum_isMergeFor_le (gs : List (BitVec 8 × BitVec 8)) :
    ((List.finRange 8).map (fun v => gs.countP (isMergeFor v))).sum ≤ gs.length :=
  count_le_sum_countP_aux gs isMergeFor (fun p _ => isMergeFor_unique p)

lemma sum_isMergeFor_filtered_le (gs : List (BitVec 8 × BitVec 8)) (vPred : Fin 8 → Bool)
    (pPred : (BitVec 8 × BitVec 8) → Bool)
    (himp : ∀ p ∈ gs, ∀ v : Fin 8, vPred v = true → isMergeFor v p = true → pPred p = true) :
    (((List.finRange 8).filter vPred).map (fun v => gs.countP (isMergeFor v))).sum ≤ gs.countP pPred := by
  let f : Fin 8 → (BitVec 8 × BitVec 8) → Bool := fun v p => vPred v && isMergeFor v p
  have h1 : (((List.finRange 8).filter vPred).map (fun v => gs.countP (isMergeFor v))).sum =
      ((List.finRange 8).map (fun v => gs.countP (f v))).sum := by
    have hgen : ∀ L : List (Fin 8),
        ((L.filter vPred).map (fun v => gs.countP (isMergeFor v))).sum =
        (L.map (fun v => gs.countP (f v))).sum := by
      intro L; induction L with
      | nil => simp
      | cons x xs ih =>
        simp only [List.filter_cons, List.map_cons, List.sum_cons]
        cases hx : vPred x
        · have hz : gs.countP (f x) = 0 := by simp [f, hx]
          simp [hz, ih]
        · have heq : gs.countP (f x) = gs.countP (isMergeFor x) := by simp [f, hx]
          simp [heq, ih]
    exact hgen (List.finRange 8)
  rw [h1]
  have hfilt : ∀ v : Fin 8, gs.countP (f v) = (gs.filter pPred).countP (f v) := by
    intro v
    have hgen : ∀ l : List (BitVec 8 × BitVec 8),
        (∀ p ∈ l, f v p = true → pPred p = true) →
        l.countP (f v) = (l.filter pPred).countP (f v) := by
      intro l hl; induction l with
      | nil => simp
      | cons x xs ih =>
        simp only [List.countP_cons, List.filter_cons]
        have hxs := ih (fun p hp => hl p (List.mem_cons_of_mem x hp))
        cases hx : f v x
        · cases pPred x <;> simp [hx, hxs]
        · have hp : pPred x = true := hl x List.mem_cons_self hx
          simp [hp, hx, hxs]
    exact hgen gs (fun p hp hf => by
      simp only [f, Bool.and_eq_true] at hf; exact himp p hp v hf.1 hf.2)
  have hsum_eq : ((List.finRange 8).map (fun v => gs.countP (f v))).sum =
      ((List.finRange 8).map (fun v => (gs.filter pPred).countP (f v))).sum := by
    congr 1; apply List.map_congr_left; intro v _; exact hfilt v
  rw [hsum_eq, List.countP_eq_length_filter]
  apply count_le_sum_countP_aux (gs.filter pPred) f
  intro p _ u v hu hv
  simp only [f, Bool.and_eq_true] at hu hv
  exact isMergeFor_unique p u v hu.2 hv.2

lemma eraseDups_length_le_add_one {α : Type} [BEq α] [LawfulBEq α]
    (l : List α) (c1 c2 : α) :
    (dedup l).length ≤ (dedup (l.map (fun x => if x == c2 then c1 else x))).length + 1 := by
  let f : α → α := fun x => if x == c2 then c1 else x
  have hnodup : ∀ xs : List α, xs.Nodup → xs.length ≤ (dedup (xs.map f)).length + 1 := by
    intro xs hnd
    induction xs with
    | nil => simp
    | cons a as ih =>
      rw [List.nodup_cons] at hnd
      by_cases ha : a = c2
      · subst ha
        have hmap_id : ∀ ys : List α, a ∉ ys → ys.map f = ys := by
          intro ys; induction ys with
          | nil => intro _; simp
          | cons y yt ihy =>
            intro hnot
            have hne : y ≠ a := fun h => hnot (h ▸ List.mem_cons_self)
            simp only [List.map_cons, f, beq_false_of_ne hne, ↓reduceIte]
            congr 1; exact ihy (fun hm => hnot (List.mem_cons_of_mem y hm))
        have hlen : (dedup (as.map f)).length = as.length := by
          rw [hmap_id as hnd.1, dedup_eq_self_of_nodup as hnd.2]
        have hsub : (dedup (as.map f)).length ≤ (dedup ((a :: as).map f)).length := by
          refine List.Subperm.length_le (List.Nodup.subperm (nodup_dedup _) ?_)
          intro y hy
          exact (mem_dedup _ y).mpr (List.mem_cons_of_mem (f a) ((mem_dedup _ y).mp hy))
        simp only [List.length_cons]; omega
      · by_cases hmem : a ∈ as.map f
        · have hc2_mem : c2 ∈ as ∧ c1 = a := by
            rw [List.mem_map] at hmem
            rcases hmem with ⟨x, hx, hfx⟩
            by_cases hxc : x = c2
            · subst hxc; simp [f] at hfx; exact ⟨hx, hfx⟩
            · simp [f, hxc] at hfx; exact absurd (hfx ▸ hx) hnd.1
          have hmap_nd : (as.map f).Nodup := by
            refine List.Nodup.map_on ?_ hnd.2
            intro x hx y hy hxy
            by_cases hxc : x = c2 <;> by_cases hyc : y = c2
            · rw [hxc, hyc]
            · subst hxc; simp [f, hyc, hc2_mem.2] at hxy; exact absurd (hxy ▸ hy) hnd.1
            · subst hyc; simp [f, hxc, hc2_mem.2] at hxy; exact absurd (hxy.symm ▸ hx) hnd.1
            · simp [f, hxc, hyc] at hxy; exact hxy
          have hlen : (dedup (as.map f)).length = as.length := by
            rw [dedup_eq_self_of_nodup _ hmap_nd, List.length_map]
          have hsub : (dedup (as.map f)).length ≤ (dedup ((a :: as).map f)).length := by
            refine List.Subperm.length_le (List.Nodup.subperm (nodup_dedup _) ?_)
            intro y hy
            exact (mem_dedup _ y).mpr (List.mem_cons_of_mem (f a) ((mem_dedup _ y).mp hy))
          simp only [List.length_cons]; omega
        · have hfa : f a = a := by simp [f, ha]
          have hlen_cons : (dedup ((a :: as).map f)).length = (dedup (as.map f)).length + 1 := by
            simp only [List.map_cons, hfa]
            have hnot : a ∉ dedup (as.map f) := fun hm => hmem ((mem_dedup _ a).mp hm)
            have hperm : (dedup (a :: as.map f)).Perm (a :: dedup (as.map f)) := by
              refine (List.perm_ext_iff_of_nodup (nodup_dedup _)
                (List.nodup_cons.mpr ⟨hnot, nodup_dedup _⟩)).mpr fun y => ?_
              simp [mem_dedup]
            rw [hperm.length_eq, List.length_cons]
          have ih' := ih hnd.2
          simp only [List.length_cons]; omega
  have h1 := hnodup (dedup l) (nodup_dedup l)
  have h2 : (dedup ((dedup l).map f)).length ≤ (dedup (l.map f)).length := by
    refine List.Subperm.length_le (List.Nodup.subperm (nodup_dedup _) ?_)
    intro y hy
    rw [mem_dedup, List.mem_map] at hy ⊢
    rcases hy with ⟨x, hx, rfl⟩
    exact ⟨x, (mem_dedup _ x).mp hx, rfl⟩
  dsimp only [f] at h1 h2
  omega

lemma eraseDups_length_of_nodup {α : Type} [BEq α] [LawfulBEq α] (l : List α) (h : l.Nodup) :
    (dedup l).length = l.length := by
  rw [dedup_eq_self_of_nodup l h]

lemma imgLenIn_id (mask : BitVec 8) : imgLenIn mask id = pop8 mask := by
  unfold imgLenIn pop8
  have hnd : ((List.finRange 8).filter (fun u => hasBit mask u)).Nodup :=
    List.Nodup.filter _ (List.nodup_finRange 8)
  rw [List.map_id, eraseDups_length_of_nodup _ hnd, List.countP_eq_length_filter]

lemma imgLenIn_mergeStepIn (mask : BitVec 8) (c : Fin 8 → Fin 8) (p : BitVec 8 × BitVec 8) :
    imgLenIn mask c ≤ imgLenIn mask (mergeStepIn mask c p) + (if isMergeIn mask p then 1 else 0) := by
  unfold mergeStepIn
  cases hm : isMergeIn mask p
  · simp
  · simp only [↓reduceIte]; unfold imgLenIn
    have hmap : (((List.finRange 8).filter (fun u => hasBit mask u)).map
        (fun u => if c u == c (firstBit p.2) then c (firstBit p.1) else c u)) =
        (((List.finRange 8).filter (fun u => hasBit mask u)).map c).map
        (fun x => if x == c (firstBit p.2) then c (firstBit p.1) else x) := by
      rw [List.map_map]; rfl
    rw [hmap]
    exact eraseDups_length_le_add_one _ (c (firstBit p.1)) (c (firstBit p.2))

lemma imgLenIn_buildCompIn_lb (mask : BitVec 8) (gs : List (BitVec 8 × BitVec 8)) :
    pop8 mask ≤ imgLenIn mask (buildCompIn mask gs) + gs.countP (isMergeIn mask) := by
  have hgen : ∀ (l : List (BitVec 8 × BitVec 8)) (c : Fin 8 → Fin 8),
      imgLenIn mask c ≤ imgLenIn mask (l.foldl (mergeStepIn mask) c) + l.countP (isMergeIn mask) := by
    intro l; induction l with
    | nil => intro c; simp
    | cons p ps ih =>
      intro c; simp only [List.foldl_cons, List.countP_cons]
      have h1 := imgLenIn_mergeStepIn mask c p
      have h2 := ih (mergeStepIn mask c p)
      cases hm : isMergeIn mask p <;> simp [hm] at h1 ⊢ <;> omega
  rw [← imgLenIn_id mask]
  exact hgen gs id

lemma imgLen_buildComp_lb (v : Fin 8) (gs : List (BitVec 8 × BitVec 8)) :
    pop8 (nbrs v) ≤ imgLen v (buildComp v gs) + gs.countP (isMergeFor v) :=
  imgLenIn_buildCompIn_lb (nbrs v) gs

lemma imgLenIn_le_one_of_const (mask : BitVec 8) (c : Fin 8 → Fin 8)
    (hconst : ∀ x y : Fin 8, hasBit mask x = true → hasBit mask y = true → c x = c y) :
    imgLenIn mask c ≤ 1 := by
  unfold imgLenIn
  by_cases h0 : mask = 0#8
  · subst h0
    have hf : (List.finRange 8).filter (fun u => hasBit 0#8 u) = [] := by decide
    rw [hf]; simp [dedup]
  · obtain ⟨x0, hx0⟩ := exists_bit_of_ne_zero mask h0
    have hsub : ∀ y ∈ dedup (((List.finRange 8).filter (fun u => hasBit mask u)).map c),
        y ∈ [c x0] := by
      intro y hy
      rw [mem_dedup, List.mem_map] at hy
      rcases hy with ⟨u, hu, rfl⟩
      rw [List.mem_singleton]
      exact hconst u x0 (List.mem_filter.mp hu).2 hx0
    have hle := List.Subperm.length_le (List.Nodup.subperm (nodup_dedup _) hsub)
    simpa using hle

lemma mergeStepIn_preserves_eq (mask : BitVec 8) (c : Fin 8 → Fin 8) (p : BitVec 8 × BitVec 8)
    (x y : Fin 8) (hxy : c x = c y) : mergeStepIn mask c p x = mergeStepIn mask c p y := by
  unfold mergeStepIn; split <;> simp [hxy]

/-! ### Part 4: Master Cover Bound Lemmas -/

def coversClass (comp : Fin 8 → Fin 8 → Fin 8) (vc : Fin 8 × Fin 8) (e : Fin 11) : Bool :=
  (vc.1 == edgeU e && comp (edgeU e) (edgeV e) == vc.2) ||
  (vc.1 == edgeV e && comp (edgeV e) (edgeU e) == vc.2)

def hitCountAt (comp : Fin 8 → Fin 8 → Fin 8) (H : List (Fin 8 × Fin 8)) (v : Fin 8) : Nat :=
  (List.finRange 8).countP (fun u => adj v u && H.any (fun vc => vc.1 == v && comp v u == vc.2))

lemma hitCountAt_le (comp : Fin 8 → Fin 8 → Fin 8) (H : List (Fin 8 × Fin 8)) (v : Fin 8) :
    hitCountAt comp H v + imgLen v (comp v) ≤
      pop8 (nbrs v) + H.countP (fun vc => vc.1 == v) := by
  let Nv := (List.finRange 8).filter (fun u => hasBit (nbrs v) u)
  let Hv := (H.filter (fun vc => vc.1 == v)).map Prod.snd
  let hitPred : Fin 8 → Bool := fun u => H.any (fun vc => vc.1 == v && comp v u == vc.2)
  have hNv_len : Nv.length = pop8 (nbrs v) := by rw [← List.countP_eq_length_filter]; rfl
  have hhit_eq : hitCountAt comp H v = (Nv.filter hitPred).length := by
    unfold hitCountAt Nv hitPred
    rw [← List.countP_eq_length_filter, List.countP_filter]
    exact List.countP_congr fun u _ => by rw [Bool.and_comm, hasBit_nbrs]
  have hunhit_eq : (Nv.filter (fun u => !hitPred u)).length + (Nv.filter hitPred).length = Nv.length := by
    have hgen : ∀ l : List (Fin 8),
        (l.filter (fun u => !hitPred u)).length + (l.filter hitPred).length = l.length := by
      intro l; induction l with
      | nil => simp
      | cons x xs ih => simp only [List.filter_cons, List.length_cons]; cases hitPred x <;> simp <;> omega
    exact hgen Nv
  have hsub : ∀ y ∈ dedup (Nv.map (comp v)),
      y ∈ Hv ++ (Nv.filter (fun u => !hitPred u)).map (comp v) := by
    intro y hy
    rw [mem_dedup, List.mem_map] at hy
    rcases hy with ⟨u, hu, rfl⟩
    rw [List.mem_append]
    cases hpu : hitPred u
    · right; exact List.mem_map.mpr ⟨u, List.mem_filter.mpr ⟨hu, by simp [hpu]⟩, rfl⟩
    · left
      simp only [hitPred, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at hpu
      rcases hpu with ⟨vc, hvc, h1, h2⟩
      exact List.mem_map.mpr ⟨vc, List.mem_filter.mpr ⟨hvc, by simp [h1]⟩, h2.symm⟩
  have himg_le : imgLen v (comp v) ≤ (Hv ++ (Nv.filter (fun u => !hitPred u)).map (comp v)).length :=
    List.Subperm.length_le (List.Nodup.subperm (nodup_dedup _) hsub)
  have hHv_len : Hv.length = H.countP (fun vc => vc.1 == v) := by
    simp [Hv, List.countP_eq_length_filter]
  simp only [List.length_append, List.length_map, hHv_len] at himg_le
  omega

lemma countP_le_sum_countP_edges (comp : Fin 8 → Fin 8 → Fin 8) (H : List (Fin 8 × Fin 8))
    (edgePred : Fin 11 → Bool) (vPred : Fin 8 → Bool)
    (hcover : ∀ e : Fin 11, edgePred e = true →
      ∃ v : Fin 8, vPred v = true ∧
        ((edgeU e = v ∧ H.any (fun vc => vc.1 == v && comp v (edgeV e) == vc.2) = true) ∨
         (edgeV e = v ∧ H.any (fun vc => vc.1 == v && comp v (edgeU e) == vc.2) = true))) :
    (List.finRange 11).countP edgePred ≤
      (((List.finRange 8).filter vPred).map (hitCountAt comp H)).sum := by
  let allPairs : List (Fin 8 × Fin 8) :=
    ((List.finRange 8).filter vPred).flatMap fun v =>
      ((List.finRange 8).filter (fun u => adj v u && H.any (fun vc => vc.1 == v && comp v u == vc.2))).map
        (fun u => (v, u))
  have hall_len : allPairs.length = (((List.finRange 8).filter vPred).map (hitCountAt comp H)).sum := by
    unfold allPairs; rw [List.length_flatMap]; congr 1
    apply List.map_congr_left; intro v _; rw [List.length_map, ← List.countP_eq_length_filter]; rfl
  let wit : Fin 11 → Fin 8 × Fin 8 := fun e =>
    if vPred (edgeU e) && H.any (fun vc => vc.1 == edgeU e && comp (edgeU e) (edgeV e) == vc.2) then
      (edgeU e, edgeV e)
    else (edgeV e, edgeU e)
  have hwit_mem : ∀ e : Fin 11, edgePred e = true → wit e ∈ allPairs := by
    intro e he
    obtain ⟨v, hv, hcase⟩ := hcover e he
    unfold wit allPairs; rw [List.mem_flatMap]
    by_cases h1 : (vPred (edgeU e) && H.any (fun vc => vc.1 == edgeU e && comp (edgeU e) (edgeV e) == vc.2)) = true
    · rw [if_pos h1]; simp only [Bool.and_eq_true] at h1
      refine ⟨edgeU e, List.mem_filter.mpr ⟨List.mem_finRange _, h1.1⟩, ?_⟩
      exact List.mem_map.mpr ⟨edgeV e, List.mem_filter.mpr ⟨List.mem_finRange _, by simp [edge_adj e, h1.2]⟩, rfl⟩
    · rw [if_neg h1]
      have h2 : vPred (edgeV e) = true ∧ H.any (fun vc => vc.1 == edgeV e && comp (edgeV e) (edgeU e) == vc.2) = true := by
        rcases hcase with ⟨rfl, hh⟩ | ⟨rfl, hh⟩
        · exact absurd (by simp [hv, hh]) h1
        · exact ⟨hv, hh⟩
      refine ⟨edgeV e, List.mem_filter.mpr ⟨List.mem_finRange _, h2.1⟩, ?_⟩
      exact List.mem_map.mpr ⟨edgeU e, List.mem_filter.mpr ⟨List.mem_finRange _, by rw [adj_symm]; simp [edge_adj e, h2.2]⟩, rfl⟩
  have hwit_inj : ∀ e1 e2 : Fin 11, wit e1 = wit e2 → e1 = e2 := by
    intro e1 e2 heq; unfold wit at heq
    split at heq <;> split at heq <;> simp only [Prod.mk.injEq] at heq
    · exact edge_inj e1 e2 (Or.inl heq)
    · exact edge_inj e1 e2 (Or.inr heq)
    · exact edge_inj e1 e2 (Or.inr ⟨heq.2, heq.1⟩)
    · exact edge_inj e1 e2 (Or.inl ⟨heq.2, heq.1⟩)
  let eList := ((List.finRange 11).filter edgePred).map wit
  have heList_nd : eList.Nodup :=
    List.Nodup.map hwit_inj (List.Nodup.filter _ (List.nodup_finRange 11))
  have hsub : ∀ p ∈ eList, p ∈ allPairs := by
    intro p hp; rw [List.mem_map] at hp; rcases hp with ⟨e, he, rfl⟩
    exact hwit_mem e (List.mem_filter.mp he).2
  have hle := List.Subperm.length_le (List.Nodup.subperm heList_nd hsub)
  rw [hall_len, List.length_map, ← List.countP_eq_length_filter] at hle
  exact hle

lemma countP_add_one_le_sum_with_overlap (comp : Fin 8 → Fin 8 → Fin 8) (H : List (Fin 8 × Fin 8))
    (edgePred : Fin 11 → Bool)
    (hcover : ∀ e : Fin 11, edgePred e = true →
      H.any (fun vc => coversClass comp vc e) = true)
    (e0 : Fin 11) (he0 : edgePred e0 = true)
    (h0U : H.any (fun vc => vc.1 == edgeU e0 && comp (edgeU e0) (edgeV e0) == vc.2) = true)
    (h0V : H.any (fun vc => vc.1 == edgeV e0 && comp (edgeV e0) (edgeU e0) == vc.2) = true) :
    (List.finRange 11).countP edgePred + 1 ≤
      ((List.finRange 8).map (hitCountAt comp H)).sum := by
  let allPairs : List (Fin 8 × Fin 8) :=
    (List.finRange 8).flatMap fun v =>
      ((List.finRange 8).filter (fun u => adj v u && H.any (fun vc => vc.1 == v && comp v u == vc.2))).map
        (fun u => (v, u))
  have hall_len : allPairs.length = ((List.finRange 8).map (hitCountAt comp H)).sum := by
    unfold allPairs; rw [List.length_flatMap]; congr 1
    apply List.map_congr_left; intro v _; rw [List.length_map, ← List.countP_eq_length_filter]; rfl
  let wit : Fin 11 → Fin 8 × Fin 8 := fun e =>
    if H.any (fun vc => vc.1 == edgeU e && comp (edgeU e) (edgeV e) == vc.2) then
      (edgeU e, edgeV e)
    else (edgeV e, edgeU e)
  have hwit_mem : ∀ e : Fin 11, edgePred e = true → wit e ∈ allPairs := by
    intro e he
    have hc := hcover e he
    simp only [List.any_eq_true, coversClass, Bool.or_eq_true] at hc
    unfold wit allPairs; rw [List.mem_flatMap]
    by_cases h1 : H.any (fun vc => vc.1 == edgeU e && comp (edgeU e) (edgeV e) == vc.2) = true
    · rw [if_pos h1]
      refine ⟨edgeU e, List.mem_finRange _, ?_⟩
      exact List.mem_map.mpr ⟨edgeV e, List.mem_filter.mpr ⟨List.mem_finRange _, by simp [edge_adj e, h1]⟩, rfl⟩
    · rw [if_neg h1]
      have h2 : H.any (fun vc => vc.1 == edgeV e && comp (edgeV e) (edgeU e) == vc.2) = true := by
        rcases hc with ⟨vc, hvc, hU | hV⟩
        · exact absurd (List.any_eq_true.mpr ⟨vc, hvc, hU⟩) h1
        · exact List.any_eq_true.mpr ⟨vc, hvc, hV⟩
      refine ⟨edgeV e, List.mem_finRange _, ?_⟩
      exact List.mem_map.mpr ⟨edgeU e, List.mem_filter.mpr ⟨List.mem_finRange _, by rw [adj_symm]; simp [edge_adj e, h2]⟩, rfl⟩
  have hwit_inj : ∀ e1 e2 : Fin 11, wit e1 = wit e2 → e1 = e2 := by
    intro e1 e2 heq; unfold wit at heq
    split at heq <;> split at heq <;> simp only [Prod.mk.injEq] at heq
    · exact edge_inj e1 e2 (Or.inl heq)
    · exact edge_inj e1 e2 (Or.inr heq)
    · exact edge_inj e1 e2 (Or.inr ⟨heq.2, heq.1⟩)
    · exact edge_inj e1 e2 (Or.inl ⟨heq.2, heq.1⟩)
  let extra : Fin 8 × Fin 8 := (edgeV e0, edgeU e0)
  have hextra_mem : extra ∈ allPairs := by
    unfold extra allPairs; rw [List.mem_flatMap]
    refine ⟨edgeV e0, List.mem_finRange _, ?_⟩
    exact List.mem_map.mpr ⟨edgeU e0, List.mem_filter.mpr ⟨List.mem_finRange _, by rw [adj_symm]; simp [edge_adj e0, h0V]⟩, rfl⟩
  let eList := ((List.finRange 11).filter edgePred).map wit
  have hextra_notin : extra ∉ eList := by
    intro hm; rw [List.mem_map] at hm; rcases hm with ⟨e, _, heq⟩
    have heeq : e = e0 := by
      unfold wit extra at heq; split at heq <;> simp only [Prod.mk.injEq] at heq
      · exact edge_inj e e0 (Or.inr heq)
      · exact edge_inj e e0 (Or.inl ⟨heq.2, heq.1⟩)
    subst heeq; unfold wit extra at heq; rw [if_pos h0U] at heq
    simp only [Prod.mk.injEq] at heq; exact edge_ne e heq.1
  have hnd : (extra :: eList).Nodup :=
    List.nodup_cons.mpr ⟨hextra_notin, List.Nodup.map hwit_inj (List.Nodup.filter _ (List.nodup_finRange 11))⟩
  have hsub : ∀ p ∈ extra :: eList, p ∈ allPairs := by
    intro p hp; simp only [List.mem_cons] at hp
    rcases hp with rfl | hpe
    · exact hextra_mem
    · rw [List.mem_map] at hpe; rcases hpe with ⟨e, he, rfl⟩
      exact hwit_mem e (List.mem_filter.mp he).2
  have hle := List.Subperm.length_le (List.Nodup.subperm hnd hsub)
  rw [hall_len, List.length_cons, List.length_map, ← List.countP_eq_length_filter] at hle
  exact hle

lemma sum_hitCountAt_le_filtered (gs : List (BitVec 8 × BitVec 8))
    (H : List (Fin 8 × Fin 8)) (vPred : Fin 8 → Bool) :
    (((List.finRange 8).filter vPred).map (hitCountAt (fun v => buildComp v gs) H)).sum ≤
      (((List.finRange 8).filter vPred).map (fun v => gs.countP (isMergeFor v))).sum +
      (((List.finRange 8).filter vPred).map (fun v => H.countP (fun vc => vc.1 == v))).sum := by
  have hgen : ∀ L : List (Fin 8),
      (L.map (hitCountAt (fun v => buildComp v gs) H)).sum ≤
      (L.map (fun v => gs.countP (isMergeFor v))).sum +
      (L.map (fun v => H.countP (fun vc => vc.1 == v))).sum := by
    intro L; induction L with
    | nil => simp
    | cons v vs ih =>
      simp only [List.map_cons, List.sum_cons]
      have h1 := hitCountAt_le (fun w => buildComp w gs) H v
      have h2 := imgLen_buildComp_lb v gs
      omega
  exact hgen ((List.finRange 8).filter vPred)

lemma sum_H_countP_le (H : List (Fin 8 × Fin 8)) (vPred : Fin 8 → Bool) :
    (((List.finRange 8).filter vPred).map (fun v => H.countP (fun vc => vc.1 == v))).sum ≤ H.length := by
  have hsub : ∀ L : List (Fin 8), L.Nodup →
      (L.map (fun v => H.countP (fun vc => vc.1 == v))).sum ≤ H.length := by
    intro L hnd; induction H with
    | nil => simp
    | cons a as ih =>
      have hsplit : ∀ K : List (Fin 8),
          (K.map (fun v => (a :: as).countP (fun vc => vc.1 == v))).sum =
          (K.map (fun v => if a.1 == v then 1 else 0)).sum +
          (K.map (fun v => as.countP (fun vc => vc.1 == v))).sum := by
        intro K; induction K with
        | nil => simp
        | cons x xs ihk => simp only [List.map_cons, List.sum_cons, List.countP_cons]; cases a.1 == x <;> simp <;> omega
      rw [hsplit L, List.length_cons]
      have ha1 : (L.map (fun v => if a.1 == v then 1 else 0)).sum ≤ 1 := by
        clear ih hsplit
        induction L with
        | nil => simp
        | cons x xs ihx =>
          rw [List.nodup_cons] at hnd
          simp only [List.map_cons, List.sum_cons]
          cases hax : (a.1 == x)
          · simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add]; exact ihx hnd.2
          · simp only [↓reduceIte]
            have hax' : a.1 = x := beq_iff_eq.mp hax
            have hz : (xs.map (fun v => if a.1 == v then 1 else 0)).sum = 0 :=
              sum_ite_eq_zero_of_all_false xs (fun v => a.1 == v) fun y hy => by
                have hne : a.1 ≠ y := fun h => hnd.1 (hax' ▸ h ▸ hy)
                exact beq_false_of_ne hne
            omega
      omega
  exact hsub ((List.finRange 8).filter vPred) (List.Nodup.filter _ (List.nodup_finRange 8))

lemma master_cover_bound (gs : List (BitVec 8 × BitVec 8)) (H : List (Fin 8 × Fin 8))
    (hcover : ∀ e : Fin 11, H.any (fun vc => coversClass (fun v => buildComp v gs) vc e) = true) :
    11 ≤ (((List.finRange 8).map (fun v => gs.countP (isMergeFor v))).sum) + H.length := by
  have h11 : (List.finRange 11).countP (fun _ => true) = 11 := by decide
  rw [← h11]
  have hle1 : (List.finRange 11).countP (fun _ => true) ≤
      (((List.finRange 8).filter (fun _ => true)).map (hitCountAt (fun v => buildComp v gs) H)).sum := by
    apply countP_le_sum_countP_edges (fun v => buildComp v gs) H (fun _ => true) (fun _ => true)
    intro e _
    have hc := hcover e
    simp only [List.any_eq_true, coversClass, Bool.or_eq_true] at hc
    rcases hc with ⟨vc, hvc, hU | hV⟩
    · exact ⟨edgeU e, rfl, Or.inl ⟨rfl, List.any_eq_true.mpr ⟨vc, hvc, hU⟩⟩⟩
    · exact ⟨edgeV e, rfl, Or.inr ⟨rfl, List.any_eq_true.mpr ⟨vc, hvc, hV⟩⟩⟩
  have hle2 := sum_hitCountAt_le_filtered gs H (fun _ => true)
  have hle3 := sum_H_countP_le H (fun _ => true)
  simp only [List.filter_true] at hle1 hle2 hle3
  omega

lemma master_cover_bound_overlap (gs : List (BitVec 8 × BitVec 8)) (H : List (Fin 8 × Fin 8))
    (hcover : ∀ e : Fin 11, H.any (fun vc => coversClass (fun v => buildComp v gs) vc e) = true)
    (e0 : Fin 11)
    (h0U : H.any (fun vc => vc.1 == edgeU e0 && buildComp (edgeU e0) gs (edgeV e0) == vc.2) = true)
    (h0V : H.any (fun vc => vc.1 == edgeV e0 && buildComp (edgeV e0) gs (edgeU e0) == vc.2) = true) :
    12 ≤ (((List.finRange 8).map (fun v => gs.countP (isMergeFor v))).sum) + H.length := by
  have h11 : (List.finRange 11).countP (fun _ => true) = 11 := by decide
  have hle1 := countP_add_one_le_sum_with_overlap (fun v => buildComp v gs) H (fun _ => true)
    (fun e _ => hcover e) e0 rfl h0U h0V
  have hle2 := sum_hitCountAt_le_filtered gs H (fun _ => true)
  have hle3 := sum_H_countP_le H (fun _ => true)
  simp only [List.filter_true] at hle2 hle3
  omega

lemma master_cover_bound_avoid_subset (gs : List (BitVec 8 × BitVec 8)) (H : List (Fin 8 × Fin 8))
    (v0 : Fin 8) (L0 : BitVec 8)
    (hcover : ∀ e : Fin 11,
      ¬ ((edgeU e = v0 ∧ hasBit L0 (edgeV e) = true) ∨ (edgeV e = v0 ∧ hasBit L0 (edgeU e) = true)) →
      H.any (fun vc => coversClass (fun v => buildComp v gs) vc e) = true) :
    11 - pop8 L0 ≤
      (((List.finRange 8).map (fun v => gs.countP (isMergeFor v))).sum) + H.length := by
  let avoidPred : Fin 11 → Bool := fun e =>
    !((edgeU e == v0 && hasBit L0 (edgeV e)) || (edgeV e == v0 && hasBit L0 (edgeU e)))
  have hcnt : 11 - pop8 L0 ≤ (List.finRange 11).countP avoidPred := by
    have hcomp : (List.finRange 11).countP (fun e => !avoidPred e) ≤ pop8 L0 := by
      let other : Fin 11 → Fin 8 := fun e => if edgeU e == v0 then edgeV e else edgeU e
      let badEdges := (List.finRange 11).filter (fun e => !avoidPred e)
      have hinj : ∀ e1 ∈ badEdges, ∀ e2 ∈ badEdges, other e1 = other e2 → e1 = e2 := by
        intro e1 h1 e2 h2 heq
        have hb1 := (List.mem_filter.mp h1).2
        have hb2 := (List.mem_filter.mp h2).2
        simp only [avoidPred, Bool.not_not, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hb1 hb2
        unfold other at heq
        rcases hb1 with ⟨h1u, _⟩ | ⟨h1v, _⟩ <;> rcases hb2 with ⟨h2u, _⟩ | ⟨h2v, _⟩
        · simp [h1u, h2u] at heq; exact edge_inj e1 e2 (Or.inl ⟨h1u.trans h2u.symm, heq⟩)
        · have hne2 : edgeU e2 ≠ v0 := fun h => edge_ne e2 (h.trans h2v.symm)
          simp [h1u, hne2] at heq; exact edge_inj e1 e2 (Or.inr ⟨h1u.trans h2v.symm, heq⟩)
        · have hne1 : edgeU e1 ≠ v0 := fun h => edge_ne e1 (h.trans h1v.symm)
          simp [hne1, h2u] at heq; exact edge_inj e1 e2 (Or.inr ⟨heq, h1v.trans h2u.symm⟩)
        · have hne1 : edgeU e1 ≠ v0 := fun h => edge_ne e1 (h.trans h1v.symm)
          have hne2 : edgeU e2 ≠ v0 := fun h => edge_ne e2 (h.trans h2v.symm)
          simp [hne1, hne2] at heq; exact edge_inj e1 e2 (Or.inl ⟨heq, h1v.trans h2v.symm⟩)
      have hnd : (badEdges.map other).Nodup :=
        List.Nodup.map_on hinj (List.Nodup.filter _ (List.nodup_finRange 11))
      have hsub : ∀ u ∈ badEdges.map other, u ∈ (List.finRange 8).filter (fun i => hasBit L0 i) := by
        intro u hu
        rw [List.mem_map] at hu; rcases hu with ⟨e, he, rfl⟩
        have hb := (List.mem_filter.mp he).2
        simp only [avoidPred, Bool.not_not, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hb
        refine List.mem_filter.mpr ⟨List.mem_finRange _, ?_⟩
        unfold other
        rcases hb with ⟨hu, hv⟩ | ⟨hv, hu⟩
        · simp [hu, hv]
        · have hne : edgeU e ≠ v0 := fun h => edge_ne e (h.trans hv.symm)
          simp [hne, hu]
      have hle := List.Subperm.length_le (List.Nodup.subperm hnd hsub)
      rw [List.length_map, ← List.countP_eq_length_filter, ← List.countP_eq_length_filter] at hle
      exact hle
    have hsum : (List.finRange 11).countP avoidPred + (List.finRange 11).countP (fun e => !avoidPred e) = 11 := by
      have hgen : ∀ l : List (Fin 11),
          l.countP avoidPred + l.countP (fun e => !avoidPred e) = l.length := by
        intro l; induction l with
        | nil => simp
        | cons x xs ih => simp only [List.countP_cons, List.length_cons]; cases avoidPred x <;> simp <;> omega
      simpa using hgen (List.finRange 11)
    omega
  have hle1 : (List.finRange 11).countP avoidPred ≤
      (((List.finRange 8).filter (fun _ => true)).map (hitCountAt (fun v => buildComp v gs) H)).sum := by
    apply countP_le_sum_countP_edges (fun v => buildComp v gs) H avoidPred (fun _ => true)
    intro e he
    have hnot : ¬ ((edgeU e = v0 ∧ hasBit L0 (edgeV e) = true) ∨ (edgeV e = v0 ∧ hasBit L0 (edgeU e) = true)) := by
      rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> simp [avoidPred, h1, h2] at he
    have hc := hcover e hnot
    simp only [List.any_eq_true, coversClass, Bool.or_eq_true] at hc
    rcases hc with ⟨vc, hvc, hU | hV⟩
    · exact ⟨edgeU e, rfl, Or.inl ⟨rfl, List.any_eq_true.mpr ⟨vc, hvc, hU⟩⟩⟩
    · exact ⟨edgeV e, rfl, Or.inr ⟨rfl, List.any_eq_true.mpr ⟨vc, hvc, hV⟩⟩⟩
  have hle2 := sum_hitCountAt_le_filtered gs H (fun _ => true)
  have hle3 := sum_H_countP_le H (fun _ => true)
  simp only [List.filter_true] at hle1 hle2 hle3
  omega

lemma master_cover_bound_avoid_star (gs : List (BitVec 8 × BitVec 8)) (H : List (Fin 8 × Fin 8))
    (v0 : Fin 8)
    (hcover : ∀ e : Fin 11, edgeU e ≠ v0 → edgeV e ≠ v0 →
      H.any (fun vc => coversClass (fun v => buildComp v gs) vc e) = true) :
    11 - pop8 (nbrs v0) ≤
      (((List.finRange 8).filter (fun v => v != v0)).map (fun v => gs.countP (isMergeFor v))).sum +
      H.length := by
  let nonInc : Fin 11 → Bool := fun e => (edgeU e != v0) && (edgeV e != v0)
  have hcnt : (List.finRange 11).countP nonInc = 11 - pop8 (nbrs v0) := by
    have hall : ∀ v : Fin 8,
        (List.finRange 11).countP (fun e => (edgeU e != v) && (edgeV e != v)) = 11 - pop8 (nbrs v) := by
      decide
    exact hall v0
  rw [← hcnt]
  have hle1 : (List.finRange 11).countP nonInc ≤
      (((List.finRange 8).filter (fun v => v != v0)).map (hitCountAt (fun v => buildComp v gs) H)).sum := by
    apply countP_le_sum_countP_edges (fun v => buildComp v gs) H nonInc (fun v => v != v0)
    intro e he
    simp only [nonInc, Bool.and_eq_true, bne_iff_ne] at he
    have hc := hcover e he.1 he.2
    simp only [List.any_eq_true, coversClass, Bool.or_eq_true] at hc
    rcases hc with ⟨vc, hvc, hU | hV⟩
    · exact ⟨edgeU e, bne_iff_ne.mpr he.1, Or.inl ⟨rfl, List.any_eq_true.mpr ⟨vc, hvc, hU⟩⟩⟩
    · exact ⟨edgeV e, bne_iff_ne.mpr he.2, Or.inr ⟨rfl, List.any_eq_true.mpr ⟨vc, hvc, hV⟩⟩⟩
  have hle2 := sum_hitCountAt_le_filtered gs H (fun v => v != v0)
  have hle3 := sum_H_countP_le H (fun v => v != v0)
  omega

/-! ### Part 5: Bank Semantics and Wire Representation Tracking -/

def readBank (bank : List (BitVec 21)) (index : BitVec 5) : BitVec 21 :=
  bank.foldr (fun wire (rest : BitVec 5 → BitVec 21) idx =>
    if idx = 0 then wire else rest (idx - 1)) (fun _ => 0#21) index

lemma readBank_eq_getD (bank : List (BitVec 21)) (idx : BitVec 5) :
    readBank bank idx = bank.getD idx.toNat 0#21 := by
  unfold readBank
  induction bank generalizing idx with
  | nil => simp
  | cons w ws ih =>
    simp only [List.foldr_cons]
    by_cases h0 : idx = 0
    · subst h0; simp
    · rw [if_neg h0, ih (idx - 1)]
      have hpos : 0 < idx.toNat := by
        have hne : idx.toNat ≠ 0 := fun hz => h0 (BitVec.eq_of_toNat_eq hz)
        omega
      have hsub : (idx - 1).toNat = idx.toNat - 1 := by
        rw [BitVec.toNat_sub]; simp; omega
      rw [hsub]
      cases hk : idx.toNat with
      | zero => omega
      | succ m => simp

lemma affordable_count_and (prog : List (Bool × BitVec 5 × BitVec 5)) :
    (prog.foldr (fun gate (rest : Bool → Bool) used =>
      (!(used && gate.1)) && rest (used || gate.1)) (fun _ => true) false = true) ↔
    prog.countP (fun g => g.1) ≤ 1 := by
  have hgen : ∀ (l : List (Bool × BitVec 5 × BitVec 5)) (used : Bool),
      (l.foldr (fun gate (rest : Bool → Bool) u =>
        (!(u && gate.1)) && rest (u || gate.1)) (fun _ => true) used = true) ↔
      (if used then l.countP (fun g => g.1) = 0 else l.countP (fun g => g.1) ≤ 1) := by
    intro l; induction l with
    | nil => intro used; cases used <;> simp
    | cons g gs ih =>
      intro used
      simp only [List.foldr_cons, List.countP_cons, Bool.and_eq_true, Bool.not_eq_true']
      cases used <;> cases hg : g.1
      · simpa [hg] using ih false
      · simp only [hg, Bool.false_and, Bool.not_false, Bool.false_or, true_and, ↓reduceIte,
          Bool.false_eq_true]
        rw [ih true]; simp
      · simpa [hg] using ih true
      · simp [hg]
  simpa using hgen prog false

def evalWire (gVal : BitVec 21) (r : Bool × BitVec 8) : BitVec 21 :=
  (if r.1 then gVal else 0#21) ||| orMask r.2

lemma evalWire_or (gVal : BitVec 21) (r1 r2 : Bool × BitVec 8) :
    evalWire gVal r1 ||| evalWire gVal r2 = evalWire gVal (r1.1 || r2.1, r1.2 ||| r2.2) := by
  unfold evalWire; rw [orMask_or]
  cases r1.1 <;> cases r2.1 <;> apply BitVec.eq_of_getLsbD_eq <;> intro k _ <;>
    simp [Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]

def initReps : List (Bool × BitVec 8) :=
  [ (false, bitOf ⟨0, by decide⟩), (false, bitOf ⟨6, by decide⟩),
    (false, bitOf ⟨2, by decide⟩), (false, 0#8),
    (false, bitOf ⟨1, by decide⟩), (false, bitOf ⟨3, by decide⟩),
    (false, 0#8), (false, 0#8),
    (false, bitOf ⟨4, by decide⟩), (false, bitOf ⟨5, by decide⟩),
    (false, bitOf ⟨7, by decide⟩), (false, 0#8),
    (false, bitOf ⟨5, by decide⟩), (false, bitOf ⟨7, by decide⟩),
    (false, 0#8), (false, 0#8) ]

lemma initReps_spec :
    initReps.map (evalWire 0#21) = initList ∧
    ∀ r ∈ initReps, r.1 = false ∧ pop8 r.2 ≤ 1 := by decide

def GsChain (gs : List (BitVec 8 × BitVec 8)) : Prop :=
  ∀ (i : Nat) (hi : i < gs.length),
    (pop8 (gs[i].1) ≤ 1 ∨ ∃ j : Nat, ∃ hj : j < i, gs[j].1 ||| gs[j].2 = gs[i].1) ∧
    (pop8 (gs[i].2) ≤ 1 ∨ ∃ j : Nat, ∃ hj : j < i, gs[j].1 ||| gs[j].2 = gs[i].2)

lemma track_program (prog : List (Bool × BitVec 5 × BitVec 5))
    (haff : prog.countP (fun g => g.1) ≤ 1) :
    ∃ (gVal : BitVec 21) (A B : BitVec 8)
      (reps : List (Bool × BitVec 8))
      (gs : List (BitVec 8 × BitVec 8))
      (zeroGates : List (BitVec 8)),
      let hasAnd := decide (0 < prog.countP (fun g => g.1))
      let bank := prog.foldl (fun b gate => b ++
        [if gate.1 then readBank b gate.2.1 &&& readBank b gate.2.2
         else readBank b gate.2.1 ||| readBank b gate.2.2]) initList
      bank = reps.map (evalWire gVal) ∧
      (hasAnd = false → gVal = 0#21 ∧ ∀ r ∈ reps, r.1 = false) ∧
      (hasAnd = true → gVal = orMask A &&& orMask B ∧
        (pop8 A ≤ 1 ∨ ∃ p ∈ gs, p.1 ||| p.2 = A) ∧
        (pop8 B ≤ 1 ∨ ∃ p ∈ gs, p.1 ||| p.2 = B) ∧
        (∀ mask : BitVec 8, sub8 A mask = true →
          ∀ x y : Fin 8, hasBit A x = true → hasBit A y = true →
            buildCompIn mask gs x = buildCompIn mask gs y) ∧
        (∀ mask : BitVec 8, sub8 B mask = true →
          ∀ x y : Fin 8, hasBit B x = true → hasBit B y = true →
            buildCompIn mask gs x = buildCompIn mask gs y)) ∧
      gs.length + zeroGates.length + (if hasAnd then 1 else 0) ≤ prog.length ∧
      (∀ z ∈ zeroGates, z ≠ 0#8) ∧
      (∀ r ∈ reps, r.1 = true → r.2 ≠ 0#8 → ∃ z ∈ zeroGates, sub8 z r.2 = true) ∧
      (∀ r ∈ reps, ∀ mask : BitVec 8, sub8 r.2 mask = true →
        ∀ x y : Fin 8, hasBit r.2 x = true → hasBit r.2 y = true →
          buildCompIn mask gs x = buildCompIn mask gs y) ∧
      (∀ r ∈ reps, pop8 r.2 ≤ 1 ∨ ∃ p ∈ gs, p.1 ||| p.2 = r.2) ∧
      GsChain gs := by
  induction prog using List.reverseRecOn with
  | nil =>
    refine ⟨0#21, 0#8, 0#8, initReps, [], [], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact initReps_spec.1.symm
    · intro _; exact ⟨rfl, fun r hr => (initReps_spec.2 r hr).1⟩
    · intro h; simp at h
    · simp
    · intro z hz; simp at hz
    · intro r hr h1; exact absurd (initReps_spec.2 r hr).1 (by simp [h1])
    · intro r hr _ _ x y hx hy
      rw [(pop8_le_one_iff r.2).mp (initReps_spec.2 r hr).2 x y hx hy]
    · intro r hr; exact Or.inl (initReps_spec.2 r hr).2
    · intro i hi; simp at hi
  | append_singleton ps g ih =>
    rw [List.countP_append, List.countP_singleton] at haff
    have hps : ps.countP (fun x => x.1) ≤ 1 := by omega
    obtain ⟨gVal, A, B, reps, gs, zeroGates,
      hbank, hnoAnd, hyesAnd, hlen, hzne, hzeroAnc, hcomp, hmemGs, hchain⟩ := ih hps
    let bank := ps.foldl (fun b gate => b ++
      [if gate.1 then readBank b gate.2.1 &&& readBank b gate.2.2
       else readBank b gate.2.1 ||| readBank b gate.2.2]) initList
    have hbank_eq : bank = reps.map (evalWire gVal) := hbank
    let r1 : Bool × BitVec 8 := reps.getD g.2.1.toNat (false, 0#8)
    let r2 : Bool × BitVec 8 := reps.getD g.2.2.toNat (false, 0#8)
    have hread1 : readBank bank g.2.1 = evalWire gVal r1 := by
      rw [readBank_eq_getD, hbank_eq]; dsimp only [r1]
      by_cases hlt : g.2.1.toNat < reps.length
      · rw [List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hlt),
          List.getD_eq_getElem _ _ hlt, List.getElem_map]
      · rw [List.getD_eq_default _ _ (by rw [List.length_map]; omega),
          List.getD_eq_default _ _ (by omega)]
        simp [evalWire, orMask_zero]
    have hread2 : readBank bank g.2.2 = evalWire gVal r2 := by
      rw [readBank_eq_getD, hbank_eq]; dsimp only [r2]
      by_cases hlt : g.2.2.toNat < reps.length
      · rw [List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hlt),
          List.getD_eq_getElem _ _ hlt, List.getElem_map]
      · rw [List.getD_eq_default _ _ (by rw [List.length_map]; omega),
          List.getD_eq_default _ _ (by omega)]
        simp [evalWire, orMask_zero]
    have hr1_in : r1 ∈ reps ∨ r1 = (false, 0#8) := by
      dsimp only [r1]
      by_cases hlt : g.2.1.toNat < reps.length
      · left; rw [List.getD_eq_getElem _ _ hlt]; exact List.getElem_mem hlt
      · right; rw [List.getD_eq_default _ _ (by omega)]
    have hr2_in : r2 ∈ reps ∨ r2 = (false, 0#8) := by
      dsimp only [r2]
      by_cases hlt : g.2.2.toNat < reps.length
      · left; rw [List.getD_eq_getElem _ _ hlt]; exact List.getElem_mem hlt
      · right; rw [List.getD_eq_default _ _ (by omega)]
    have hfold_step : (ps ++ [g]).foldl (fun b gate => b ++
        [if gate.1 then readBank b gate.2.1 &&& readBank b gate.2.2
         else readBank b gate.2.1 ||| readBank b gate.2.2]) initList =
        bank ++ [if g.1 then evalWire gVal r1 &&& evalWire gVal r2
                 else evalWire gVal r1 ||| evalWire gVal r2] := by
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil, hread1, hread2]
    cases hg : g.1
    · have hcnt_eq : (ps ++ [g]).countP (fun x => x.1) = ps.countP (fun x => x.1) := by
        rw [List.countP_append, List.countP_singleton]; simp [hg]
      simp only [hg, Bool.false_eq_true, ↓reduceIte] at hfold_step
      rw [evalWire_or] at hfold_step
      let rNew : Bool × BitVec 8 := (r1.1 || r2.1, r1.2 ||| r2.2)
      by_cases hboth : r1.2 ≠ 0#8 ∧ r2.2 ≠ 0#8
      · refine ⟨gVal, A, B, reps ++ [rNew], gs ++ [(r1.2, r2.2)], zeroGates,
          ?_, ?_, ?_, ?_, hzne, ?_, ?_, ?_, ?_⟩
        · rw [hfold_step, hbank_eq, List.map_append, List.map_singleton]
        · intro hna; rw [hcnt_eq] at hna
          obtain ⟨hgv, hallf⟩ := hnoAnd hna
          refine ⟨hgv, fun r hr => ?_⟩
          rw [List.mem_append, List.mem_singleton] at hr
          rcases hr with hr | rfl
          · exact hallf r hr
          · have hf1 : r1.1 = false := by rcases hr1_in with h | h; exact hallf r1 h; simp [h]
            have hf2 : r2.1 = false := by rcases hr2_in with h | h; exact hallf r2 h; simp [h]
            simp [rNew, hf1, hf2]
        · intro hya; rw [hcnt_eq] at hya
          obtain ⟨hgv, hA, hB, hcA, hcB⟩ := hyesAnd hya
          refine ⟨hgv, ?_, ?_, ?_, ?_⟩
          · rcases hA with h | ⟨p, hp, hpe⟩
            · exact Or.inl h
            · exact Or.inr ⟨p, List.mem_append_left _ hp, hpe⟩
          · rcases hB with h | ⟨p, hp, hpe⟩
            · exact Or.inl h
            · exact Or.inr ⟨p, List.mem_append_left _ hp, hpe⟩
          · intro mask hsub x y hx hy
            unfold buildCompIn; rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
            exact mergeStepIn_preserves_eq mask _ _ x y (hcA mask hsub x y hx hy)
          · intro mask hsub x y hx hy
            unfold buildCompIn; rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
            exact mergeStepIn_preserves_eq mask _ _ x y (hcB mask hsub x y hx hy)
        · simp only [hcnt_eq, List.length_append, List.length_singleton]; omega
        · intro r hr hr1 hr2
          rw [List.mem_append, List.mem_singleton] at hr
          rcases hr with hr | rfl
          · exact hzeroAnc r hr hr1 hr2
          · dsimp only [rNew] at hr1; rw [Bool.or_eq_true] at hr1
            rcases hr1 with h1t | h2t
            · have hr1m : r1 ∈ reps := by rcases hr1_in with h | h; exact h; simp [h] at h1t
              obtain ⟨z, hz, hsub⟩ := hzeroAnc r1 hr1m h1t hboth.1
              refine ⟨z, hz, (sub8_iff z (r1.2 ||| r2.2)).mpr fun i hi => ?_⟩
              rw [hasBit_or, (sub8_iff z r1.2).mp hsub i hi]; simp
            · have hr2m : r2 ∈ reps := by rcases hr2_in with h | h; exact h; simp [h] at h2t
              obtain ⟨z, hz, hsub⟩ := hzeroAnc r2 hr2m h2t hboth.2
              refine ⟨z, hz, (sub8_iff z (r1.2 ||| r2.2)).mpr fun i hi => ?_⟩
              rw [hasBit_or, (sub8_iff z r2.2).mp hsub i hi]; simp
        · intro r hr mask hsub x y hx hy
          have hcomp_step : ∀ u : Fin 8,
              buildCompIn mask (gs ++ [(r1.2, r2.2)]) u =
              mergeStepIn mask (buildCompIn mask gs) (r1.2, r2.2) u := fun u => by
            unfold buildCompIn; rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
          rw [hcomp_step x, hcomp_step y]
          rw [List.mem_append, List.mem_singleton] at hr
          rcases hr with hr | rfl
          · exact mergeStepIn_preserves_eq mask _ _ x y (hcomp r hr mask hsub x y hx hy)
          · by_cases hpop1 : pop8 (r1.2 ||| r2.2) ≤ 1
            · rw [(pop8_le_one_iff (r1.2 ||| r2.2)).mp hpop1 x y hx hy]
            · have hm : isMergeIn mask (r1.2, r2.2) = true := by
                simp only [isMergeIn, Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq]
                exact ⟨⟨⟨hboth.1, hboth.2⟩, by omega⟩, hsub⟩
              have hsub1 : sub8 r1.2 mask = true := (sub8_iff _ _).mpr fun i hi =>
                (sub8_iff _ _).mp hsub i (by rw [hasBit_or, hi]; simp)
              have hsub2 : sub8 r2.2 mask = true := (sub8_iff _ _).mpr fun i hi =>
                (sub8_iff _ _).mp hsub i (by rw [hasBit_or, hi]; simp)
              have hr1m : r1 ∈ reps := by rcases hr1_in with h | h; exact h; simp [h] at hboth
              have hr2m : r2 ∈ reps := by rcases hr2_in with h | h; exact h; simp [h] at hboth
              have hfb1 := firstBit_mem r1.2 hboth.1
              have hfb2 := firstBit_mem r2.2 hboth.2
              have hval : ∀ w : Fin 8, hasBit (r1.2 ||| r2.2) w = true →
                  mergeStepIn mask (buildCompIn mask gs) (r1.2, r2.2) w =
                  buildCompIn mask gs (firstBit r1.2) := by
                intro w hw; rw [hasBit_or, Bool.or_eq_true] at hw
                unfold mergeStepIn; rw [if_pos hm]
                rcases hw with hw1 | hw2
                · rw [hcomp r1 hr1m mask hsub1 w (firstBit r1.2) hw1 hfb1]; split <;> simp_all
                · rw [hcomp r2 hr2m mask hsub2 w (firstBit r2.2) hw2 hfb2]; simp
              rw [hval x hx, hval y hy]
        · intro r hr
          rw [List.mem_append, List.mem_singleton] at hr
          rcases hr with hr | rfl
          · rcases hmemGs r hr with h | ⟨p, hp, hpe⟩
            · exact Or.inl h
            · exact Or.inr ⟨p, List.mem_append_left _ hp, hpe⟩
          · exact Or.inr ⟨(r1.2, r2.2), List.mem_append_right _ List.mem_cons_self, rfl⟩
        · intro i hi
          simp only [List.length_append, List.length_singleton] at hi
          by_cases hlt : i < gs.length
          · have hgi : (gs ++ [(r1.2, r2.2)])[i] = gs[i] := List.getElem_append_left hlt
            rw [hgi]
            obtain ⟨h1, h2⟩ := hchain i hlt
            constructor
            · rcases h1 with h | ⟨j, hj, heq⟩
              · exact Or.inl h
              · exact Or.inr ⟨j, hj, by rw [List.getElem_append_left (by omega)]; exact heq⟩
            · rcases h2 with h | ⟨j, hj, heq⟩
              · exact Or.inl h
              · exact Or.inr ⟨j, hj, by rw [List.getElem_append_left (by omega)]; exact heq⟩
          · have hieq : i = gs.length := by omega
            subst hieq
            have hgi : (gs ++ [(r1.2, r2.2)])[gs.length] = (r1.2, r2.2) := by
              rw [List.getElem_append_right (le_refl _)]; simp
            rw [hgi]
            have hr1m : r1 ∈ reps := by rcases hr1_in with h | h; exact h; simp [h] at hboth
            have hr2m : r2 ∈ reps := by rcases hr2_in with h | h; exact h; simp [h] at hboth
            constructor
            · rcases hmemGs r1 hr1m with h | ⟨p, hp, hpe⟩
              · exact Or.inl h
              · obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hp
                exact Or.inr ⟨j, hj, by rw [List.getElem_append_left hj]; exact hpe⟩
            · rcases hmemGs r2 hr2m with h | ⟨p, hp, hpe⟩
              · exact Or.inl h
              · obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hp
                exact Or.inr ⟨j, hj, by rw [List.getElem_append_left hj]; exact hpe⟩
      · have hzero_side : r1.2 = 0#8 ∨ r2.2 = 0#8 := by
          by_cases h1 : r1.2 = 0#8
          · exact Or.inl h1
          · by_cases h2 : r2.2 = 0#8
            · exact Or.inr h2
            · exact absurd ⟨h1, h2⟩ hboth
        have hS_eq : rNew.2 = r1.2 ∨ rNew.2 = r2.2 := by
          rcases hzero_side with h1z | h2z
          · right; simp [rNew, h1z]
          · left; simp [rNew, h2z]
        by_cases hzg : rNew.1 = true ∧ rNew.2 ≠ 0#8
        · refine ⟨gVal, A, B, reps ++ [rNew], gs, zeroGates ++ [rNew.2],
            ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hchain⟩
          · rw [hfold_step, hbank_eq, List.map_append, List.map_singleton]
          · intro hna; rw [hcnt_eq] at hna
            obtain ⟨_, hallf⟩ := hnoAnd hna
            have hf1 : r1.1 = false := by rcases hr1_in with h | h; exact hallf r1 h; simp [h]
            have hf2 : r2.1 = false := by rcases hr2_in with h | h; exact hallf r2 h; simp [h]
            simp [rNew, hf1, hf2] at hzg
          · intro hya; rw [hcnt_eq] at hya; exact hyesAnd hya
          · simp only [hcnt_eq, List.length_append, List.length_singleton]; omega
          · intro z hz; rw [List.mem_append, List.mem_singleton] at hz
            rcases hz with hz | rfl; exact hzne z hz; exact hzg.2
          · intro r hr hr1 hr2; rw [List.mem_append, List.mem_singleton] at hr
            rcases hr with hr | rfl
            · obtain ⟨z, hz, hsub⟩ := hzeroAnc r hr hr1 hr2
              exact ⟨z, List.mem_append_left _ hz, hsub⟩
            · exact ⟨rNew.2, List.mem_append_right _ List.mem_cons_self, sub8_refl _⟩
          · intro r hr mask hsub x y hx hy; rw [List.mem_append, List.mem_singleton] at hr
            rcases hr with hr | rfl
            · exact hcomp r hr mask hsub x y hx hy
            · rcases hS_eq with hEq | hEq
              · rw [hEq] at hsub hx hy; rcases hr1_in with hm | h0
                · exact hcomp r1 hm mask hsub x y hx hy
                · simp [h0, hasBit_zero] at hx
              · rw [hEq] at hsub hx hy; rcases hr2_in with hm | h0
                · exact hcomp r2 hm mask hsub x y hx hy
                · simp [h0, hasBit_zero] at hx
          · intro r hr; rw [List.mem_append, List.mem_singleton] at hr
            rcases hr with hr | rfl
            · exact hmemGs r hr
            · rcases hS_eq with hEq | hEq
              · rw [hEq]; rcases hr1_in with hm | h0; exact hmemGs r1 hm; left; simp [h0]; decide
              · rw [hEq]; rcases hr2_in with hm | h0; exact hmemGs r2 hm; left; simp [h0]; decide
        · refine ⟨gVal, A, B, reps ++ [rNew], gs, zeroGates,
            ?_, ?_, ?_, ?_, hzne, ?_, ?_, ?_, hchain⟩
          · rw [hfold_step, hbank_eq, List.map_append, List.map_singleton]
          · intro hna; rw [hcnt_eq] at hna
            obtain ⟨hgv, hallf⟩ := hnoAnd hna
            refine ⟨hgv, fun r hr => ?_⟩
            rw [List.mem_append, List.mem_singleton] at hr
            rcases hr with hr | rfl
            · exact hallf r hr
            · have hf1 : r1.1 = false := by rcases hr1_in with h | h; exact hallf r1 h; simp [h]
              have hf2 : r2.1 = false := by rcases hr2_in with h | h; exact hallf r2 h; simp [h]
              simp [rNew, hf1, hf2]
          · intro hya; rw [hcnt_eq] at hya; exact hyesAnd hya
          · simp only [hcnt_eq, List.length_append, List.length_singleton]; omega
          · intro r hr hr1 hr2; rw [List.mem_append, List.mem_singleton] at hr
            rcases hr with hr | rfl
            · exact hzeroAnc r hr hr1 hr2
            · exact absurd ⟨hr1, hr2⟩ hzg
          · intro r hr mask hsub x y hx hy; rw [List.mem_append, List.mem_singleton] at hr
            rcases hr with hr | rfl
            · exact hcomp r hr mask hsub x y hx hy
            · rcases hS_eq with hEq | hEq
              · rw [hEq] at hsub hx hy; rcases hr1_in with hm | h0
                · exact hcomp r1 hm mask hsub x y hx hy
                · simp [h0, hasBit_zero] at hx
              · rw [hEq] at hsub hx hy; rcases hr2_in with hm | h0
                · exact hcomp r2 hm mask hsub x y hx hy
                · simp [h0, hasBit_zero] at hx
          · intro r hr; rw [List.mem_append, List.mem_singleton] at hr
            rcases hr with hr | rfl
            · exact hmemGs r hr
            · rcases hS_eq with hEq | hEq
              · rw [hEq]; rcases hr1_in with hm | h0; exact hmemGs r1 hm; left; simp [h0]; decide
              · rw [hEq]; rcases hr2_in with hm | h0; exact hmemGs r2 hm; left; simp [h0]; decide
    · -- AND gate!
      simp only [hg, ↓reduceIte] at haff hfold_step
      have hps0 : ps.countP (fun x => x.1) = 0 := by omega
      have hna : decide (0 < ps.countP (fun x => x.1)) = false := by simp [hps0]
      obtain ⟨_, hallf⟩ := hnoAnd hna
      have hf1 : r1.1 = false := by rcases hr1_in with h | h; exact hallf r1 h; simp [h]
      have hf2 : r2.1 = false := by rcases hr2_in with h | h; exact hallf r2 h; simp [h]
      have hev1 : evalWire gVal r1 = orMask r1.2 := by simp [evalWire, hf1]
      have hev2 : evalWire gVal r2 = orMask r2.2 := by simp [evalWire, hf2]
      let gNew : BitVec 21 := orMask r1.2 &&& orMask r2.2
      have hmap_eq : reps.map (evalWire gVal) = reps.map (evalWire gNew) := by
        apply List.map_congr_left; intro r hr
        simp [evalWire, hallf r hr]
      have hcnt1 : decide (0 < (ps ++ [g]).countP (fun x => x.1)) = true := by
        rw [List.countP_append, List.countP_singleton]; simp [hg]
      refine ⟨gNew, r1.2, r2.2, reps ++ [(true, 0#8)], gs, zeroGates,
        ?_, ?_, ?_, ?_, hzne, ?_, ?_, ?_, hchain⟩
      · rw [hfold_step, hbank_eq, hmap_eq, hev1, hev2, List.map_append, List.map_singleton]
        simp [evalWire, gNew, orMask_zero]
      · intro h; simp only [hcnt1] at h; contradiction
      · intro _
        refine ⟨rfl, ?_, ?_, ?_, ?_⟩
        · rcases hr1_in with hm | h0; exact hmemGs r1 hm; left; simp [h0]; decide
        · rcases hr2_in with hm | h0; exact hmemGs r2 hm; left; simp [h0]; decide
        · intro mask hsub x y hx hy
          rcases hr1_in with hm | h0
          · exact hcomp r1 hm mask hsub x y hx hy
          · simp [h0, hasBit_zero] at hx
        · intro mask hsub x y hx hy
          rcases hr2_in with hm | h0
          · exact hcomp r2 hm mask hsub x y hx hy
          · simp [h0, hasBit_zero] at hx
      · simp only [hcnt1, ↓reduceIte, List.length_append, List.length_singleton]
        simp only [hna, Bool.false_eq_true, ↓reduceIte] at hlen
        omega
      · intro r hr hr1 hr2; rw [List.mem_append, List.mem_singleton] at hr
        rcases hr with hr | rfl
        · exact absurd (hallf r hr) (by simp [hr1])
        · exact absurd rfl hr2
      · intro r hr mask hsub x y hx hy; rw [List.mem_append, List.mem_singleton] at hr
        rcases hr with hr | rfl
        · exact hcomp r hr mask hsub x y hx hy
        · simp [hasBit_zero] at hx
      · intro r hr; rw [List.mem_append, List.mem_singleton] at hr
        rcases hr with hr | rfl
        · exact hmemGs r hr
        · left; decide

/-! ### Part 6: Modular Subcase Proofs for 1-AND-Gate Circuits -/

def purePairClass (gs : List (BitVec 8 × BitVec 8)) (S1 S2 : BitVec 8) : Option (Fin 8 × Fin 8) :=
  if S1 == 0#8 || S2 == 0#8 then none
  else if pop8 S1 == 1 then
    let u := firstBit S1
    some (u, buildComp u gs (firstBit S2))
  else
    let v := firstBit S2
    some (v, buildComp v gs (firstBit S1))

lemma purePairClass_covers (gs : List (BitVec 8 × BitVec 8)) (S1 S2 : BitVec 8)
    (hclean : (orMask S1 &&& orMask S2 &&& BAD) = 0#21)
    (hconst1 : ∀ v : Fin 8, sub8 S1 (nbrs v) = true →
      ∀ x y : Fin 8, hasBit S1 x = true → hasBit S1 y = true → buildComp v gs x = buildComp v gs y)
    (hconst2 : ∀ v : Fin 8, sub8 S2 (nbrs v) = true →
      ∀ x y : Fin 8, hasBit S2 x = true → hasBit S2 y = true → buildComp v gs x = buildComp v gs y)
    (e : Fin 11) (he : (orMask S1 &&& orMask S2).getLsbD e.val = true) :
    ∃ vc : Fin 8 × Fin 8, purePairClass gs S1 S2 = some vc ∧
      coversClass (fun v => buildComp v gs) vc e = true := by
  have hS1ne : S1 ≠ 0#8 := fun h => by rw [h, orMask_zero] at he; simp at he
  have hS2ne : S2 ≠ 0#8 := fun h => by rw [h, orMask_zero] at he; simp at he
  have hne_or : (S1 == 0#8 || S2 == 0#8) = false := by
    simp [beq_false_of_ne hS1ne, beq_false_of_ne hS2ne]
  have hstar := clean_pair_is_star S1 S2 hclean hS1ne hS2ne
  simp only [BitVec.getLsbD_and, Bool.and_eq_true, orMask_edge_bit, Bool.or_eq_true] at he
  unfold purePairClass; rw [hne_or]; simp only [Bool.false_eq_true, ↓reduceIte]
  by_cases h1 : pop8 S1 == 1
  · rw [if_pos h1]
    obtain ⟨u, rfl⟩ := (pop8_eq_one_iff S1).mp (beq_iff_eq.mp h1)
    have hfb : firstBit (bitOf u) = u := by
      have hm := firstBit_mem (bitOf u) (by intro hz; rw [hz] at h1; exact absurd h1 (by decide))
      rw [hasBit_bitOf, beq_iff_eq] at hm; exact hm.symm
    rw [hfb]
    have hsub2 : sub8 S2 (nbrs u) = true := (sub8_iff S2 (nbrs u)).mpr fun b hb => by
      rw [hasBit_nbrs]; exact clean_pair_adj (bitOf u) S2 hclean u b (by simp [hasBit_bitOf]) hb
    refine ⟨(u, buildComp u gs (firstBit S2)), rfl, ?_⟩
    have hfb2 := firstBit_mem S2 hS2ne
    rcases he.1 with hu | hv
    · rw [hasBit_bitOf, beq_iff_eq] at hu; subst hu
      have hv2 : hasBit S2 (edgeV e) = true := by
        rcases he.2 with h | h
        · exact absurd (clean_pair_adj (bitOf (edgeU e)) S2 hclean (edgeU e) (edgeU e)
            (by simp [hasBit_bitOf]) h) (by simp [adj_irrefl])
        · exact h
      have hc := hconst2 (edgeU e) hsub2 (edgeV e) (firstBit S2) hv2 hfb2
      simp [coversClass, hc]
    · rw [hasBit_bitOf, beq_iff_eq] at hv; subst hv
      have hu2 : hasBit S2 (edgeU e) = true := by
        rcases he.2 with h | h
        · exact h
        · exact absurd (clean_pair_adj (bitOf (edgeV e)) S2 hclean (edgeV e) (edgeV e)
            (by simp [hasBit_bitOf]) h) (by simp [adj_irrefl])
      have hc := hconst2 (edgeV e) hsub2 (edgeU e) (firstBit S2) hu2 hfb2
      simp [coversClass, hc]
  · rw [if_neg h1]
    have hS2eq : ∃ v : Fin 8, S2 = bitOf v ∧ sub8 S1 (nbrs v) = true := by
      rcases hstar with ⟨u, rfl, _⟩ | h
      · have hp : pop8 (bitOf u) = 1 := (pop8_eq_one_iff (bitOf u)).mpr ⟨u, rfl⟩
        exact absurd (beq_iff_eq.mpr hp) h1
      · exact h
    rcases hS2eq with ⟨v, rfl, hsub1⟩
    have hfb : firstBit (bitOf v) = v := by
      have hm := firstBit_mem (bitOf v) hS2ne
      rw [hasBit_bitOf, beq_iff_eq] at hm; exact hm.symm
    rw [hfb]
    refine ⟨(v, buildComp v gs (firstBit S1)), rfl, ?_⟩
    have hfb1 := firstBit_mem S1 hS1ne
    rcases he.2 with hu | hv
    · rw [hasBit_bitOf, beq_iff_eq] at hu; subst hu
      have hv1 : hasBit S1 (edgeV e) = true := by
        rcases he.1 with h | h
        · exact absurd (clean_pair_adj S1 (bitOf (edgeU e)) hclean (edgeU e) (edgeU e)
            h (by simp [hasBit_bitOf])) (by simp [adj_irrefl])
        · exact h
      have hc := hconst1 (edgeU e) hsub1 (edgeV e) (firstBit S1) hv1 hfb1
      simp [coversClass, hc]
    · rw [hasBit_bitOf, beq_iff_eq] at hv; subst hv
      have hu1 : hasBit S1 (edgeU e) = true := by
        rcases he.1 with h | h
        · exact h
        · exact absurd (clean_pair_adj S1 (bitOf (edgeV e)) hclean (edgeV e) (edgeV e)
            h (by simp [hasBit_bitOf])) (by simp [adj_irrefl])
      have hc := hconst1 (edgeV e) hsub1 (edgeU e) (firstBit S1) hu1 hfb1
      simp [coversClass, hc]

lemma foldl_or_bit (l : List (BitVec 21)) (acc : BitVec 21) (k : Nat) :
    (l.foldl (fun a b => a ||| b) acc).getLsbD k =
      (acc.getLsbD k || l.any (fun b => b.getLsbD k)) := by
  induction l generalizing acc with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, List.any_cons, ih, BitVec.getLsbD_or, Bool.or_assoc]

lemma bit_and_bad_zero_of_or_left (x y : BitVec 21) (h : ((x ||| y) &&& BAD) = 0#21) :
    (x &&& BAD) = 0#21 ∧ (y &&& BAD) = 0#21 := by
  constructor <;> apply BitVec.eq_of_getLsbD_eq <;> intro k _
  · have h0 : ((x ||| y) &&& BAD).getLsbD k = false := by rw [h]; simp
    rw [BitVec.getLsbD_and, BitVec.getLsbD_or] at h0
    rw [BitVec.getLsbD_and, BitVec.getLsbD_zero]
    cases hx : x.getLsbD k <;> cases hb : BAD.getLsbD k <;> simp_all
  · have h0 : ((x ||| y) &&& BAD).getLsbD k = false := by rw [h]; simp
    rw [BitVec.getLsbD_and, BitVec.getLsbD_or] at h0
    rw [BitVec.getLsbD_and, BitVec.getLsbD_zero]
    cases hy : y.getLsbD k <;> cases hb : BAD.getLsbD k <;> simp_all

lemma evalWire_and_expand (gVal : BitVec 21) (r1 r2 : Bool × BitVec 8) :
    evalWire gVal r1 &&& evalWire gVal r2 =
      (if r1.1 && r2.1 then gVal else 0#21) |||
      (if r1.1 then gVal &&& orMask r2.2 else 0#21) |||
      (if r2.1 then gVal &&& orMask r1.2 else 0#21) |||
      (orMask r1.2 &&& orMask r2.2) := by
  unfold evalWire
  cases r1.1 <;> cases r2.1 <;> apply BitVec.eq_of_getLsbD_eq <;> intro k _ <;>
    simp only [Bool.and_true, Bool.and_false, ↓reduceIte, Bool.false_eq_true,
      BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_zero] <;>
    cases gVal.getLsbD k <;> cases (orMask r1.2).getLsbD k <;> cases (orMask r2.2).getLsbD k <;> rfl

lemma option_toList_length {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

lemma flatMap_option_length_le {α β : Type} (l : List α) (f : α → Option β) :
    (l.flatMap (fun x => (f x).toList)).length ≤ l.length := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    have := option_toList_length (f x); omega

lemma flatMap_option_length_le_countP {α β : Type} (l : List α) (f : α → Option β) (p : α → Bool)
    (hnone : ∀ x ∈ l, p x = false → f x = none) :
    (l.flatMap (fun x => (f x).toList)).length ≤ l.countP p := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.length_append, List.countP_cons]
    have ih' := ih (fun y hy => hnone y (List.mem_cons_of_mem x hy))
    cases hx : p x
    · rw [hnone x List.mem_cons_self hx]; simp only [Option.toList_none, List.length_nil, Nat.zero_add,
        hx, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]; omega
    · have h1 := option_toList_length (f x); simp only [hx, ↓reduceIte]; omega

structure Setup where
  gVal : BitVec 21
  A : BitVec 8
  B : BitVec 8
  reps : List (Bool × BitVec 8)
  gs : List (BitVec 8 × BitVec 8)
  zeroGates : List (BitVec 8)
  terminals : List (BitVec 5 × BitVec 5)
  hterm_len : terminals.length = 5
  hlen4 : gs.length + zeroGates.length ≤ 4
  hgVal : gVal = orMask A &&& orMask B
  hA_gs : pop8 A ≤ 1 ∨ ∃ p ∈ gs, p.1 ||| p.2 = A
  hB_gs : pop8 B ≤ 1 ∨ ∃ p ∈ gs, p.1 ||| p.2 = B
  hA_comp : ∀ mask : BitVec 8, sub8 A mask = true →
    ∀ x y : Fin 8, hasBit A x = true → hasBit A y = true → buildCompIn mask gs x = buildCompIn mask gs y
  hB_comp : ∀ mask : BitVec 8, sub8 B mask = true →
    ∀ x y : Fin 8, hasBit B x = true → hasBit B y = true → buildCompIn mask gs x = buildCompIn mask gs y
  hzne : ∀ z ∈ zeroGates, z ≠ 0#8
  hzeroAnc : ∀ r ∈ reps, r.1 = true → r.2 ≠ 0#8 → ∃ z ∈ zeroGates, sub8 z r.2 = true
  hcomp : ∀ r ∈ reps, ∀ mask : BitVec 8, sub8 r.2 mask = true →
    ∀ x y : Fin 8, hasBit r.2 x = true → hasBit r.2 y = true → buildCompIn mask gs x = buildCompIn mask gs y
  hchain : GsChain gs
  hedge_cov : ∀ e : Fin 11, ∃ pair ∈ terminals,
    (evalWire gVal (reps.getD pair.1.toNat (false, 0#8)) &&&
     evalWire gVal (reps.getD pair.2.toNat (false, 0#8))).getLsbD e.val = true
  hpair_clean : ∀ pair ∈ terminals,
    ((evalWire gVal (reps.getD pair.1.toNat (false, 0#8)) &&&
      evalWire gVal (reps.getD pair.2.toNat (false, 0#8))) &&& BAD) = 0#21

def Setup.repOf (S : Setup) (idx : BitVec 5) : Bool × BitVec 8 :=
  S.reps.getD idx.toNat (false, 0#8)

lemma Setup.rep_in (S : Setup) (idx : BitVec 5) : S.repOf idx ∈ S.reps ∨ S.repOf idx = (false, 0#8) := by
  dsimp only [Setup.repOf]
  by_cases hlt : idx.toNat < S.reps.length
  · left; rw [List.getD_eq_getElem _ _ hlt]; exact List.getElem_mem hlt
  · right; rw [List.getD_eq_default _ _ (by omega)]

lemma Setup.rep_const (S : Setup) (idx : BitVec 5) (v : Fin 8) (hsub : sub8 (S.repOf idx).2 (nbrs v) = true)
    (x y : Fin 8) (hx : hasBit (S.repOf idx).2 x = true) (hy : hasBit (S.repOf idx).2 y = true) :
    buildComp v S.gs x = buildComp v S.gs y := by
  rcases S.rep_in idx with hm | h0
  · exact S.hcomp (S.repOf idx) hm (nbrs v) hsub x y hx hy
  · simp [h0, hasBit_zero] at hx

lemma Setup.clean_parts (S : Setup) (pair : BitVec 5 × BitVec 5) (hp : pair ∈ S.terminals) :
    let r1 := S.repOf pair.1; let r2 := S.repOf pair.2
    ((if r1.1 && r2.1 then S.gVal else 0#21) &&& BAD = 0#21) ∧
    ((if r1.1 then S.gVal &&& orMask r2.2 else 0#21) &&& BAD = 0#21) ∧
    ((if r2.1 then S.gVal &&& orMask r1.2 else 0#21) &&& BAD = 0#21) ∧
    ((orMask r1.2 &&& orMask r2.2) &&& BAD = 0#21) := by
  have hc := S.hpair_clean pair hp
  change ((evalWire S.gVal (S.repOf pair.1) &&& evalWire S.gVal (S.repOf pair.2)) &&& BAD) = 0#21 at hc
  rw [evalWire_and_expand] at hc
  obtain ⟨h123, h4⟩ := bit_and_bad_zero_of_or_left _ _ hc
  obtain ⟨h12, h3⟩ := bit_and_bad_zero_of_or_left _ _ h123
  obtain ⟨h1, h2⟩ := bit_and_bad_zero_of_or_left _ _ h12
  exact ⟨h1, h2, h3, h4⟩

lemma Setup.zero_rep_eq_zero (S : Setup) (hz0 : S.zeroGates.length = 0) (idx : BitVec 5)
    (h1 : (S.repOf idx).1 = true) : (S.repOf idx).2 = 0#8 := by
  by_contra h2
  rcases S.rep_in idx with hm | h0
  · obtain ⟨z, hz, _⟩ := S.hzeroAnc (S.repOf idx) hm h1 h2
    have := List.length_pos_iff.mpr (List.ne_nil_of_mem hz); omega
  · simp [h0] at h1

lemma Setup.pure_only_contra (S : Setup)
    (hallf : ∀ pair ∈ S.terminals, (S.repOf pair.1).1 = false ∧ (S.repOf pair.2).1 = false) : False := by
  let H : List (Fin 8 × Fin 8) :=
    S.terminals.flatMap fun pair => (purePairClass S.gs (S.repOf pair.1).2 (S.repOf pair.2).2).toList
  have hHlen : H.length ≤ 5 := by
    have h1 := flatMap_option_length_le S.terminals (fun pair => purePairClass S.gs (S.repOf pair.1).2 (S.repOf pair.2).2)
    have h2 := S.hterm_len; dsimp only [H]; omega
  have hcov : ∀ e : Fin 11, H.any (fun vc => coversClass (fun v => buildComp v S.gs) vc e) = true := by
    intro e
    obtain ⟨pair, hp, he⟩ := S.hedge_cov e
    obtain ⟨hf1, hf2⟩ := hallf pair hp
    change (evalWire S.gVal (S.repOf pair.1) &&& evalWire S.gVal (S.repOf pair.2)).getLsbD e.val = true at he
    simp only [evalWire, hf1, hf2, Bool.false_eq_true, ↓reduceIte, BitVec.zero_or] at he
    have hc := (S.clean_parts pair hp).2.2.2
    obtain ⟨vc, hvc, hce⟩ := purePairClass_covers S.gs (S.repOf pair.1).2 (S.repOf pair.2).2 hc
      (S.rep_const pair.1) (S.rep_const pair.2) e he
    rw [List.any_eq_true]
    exact ⟨vc, List.mem_flatMap.mpr ⟨pair, hp, by simp [hvc]⟩, hce⟩
  have hbound := master_cover_bound S.gs H hcov
  have hsum := sum_isMergeFor_le S.gs
  have h4 := S.hlen4
  omega

lemma Setup.pure_len_z0 (S : Setup) (hz0 : S.zeroGates.length = 0)
    (hex : ∃ pair ∈ S.terminals, ((S.repOf pair.1).1 || (S.repOf pair.2).1) = true) :
    (S.terminals.flatMap fun pair => (purePairClass S.gs (S.repOf pair.1).2 (S.repOf pair.2).2).toList).length ≤ 4 := by
  have hle := flatMap_option_length_le_countP S.terminals
    (fun pair => purePairClass S.gs (S.repOf pair.1).2 (S.repOf pair.2).2)
    (fun pair => !((S.repOf pair.1).1 || (S.repOf pair.2).1))
    (fun pair _ hf => by
      simp only [Bool.not_eq_false', Bool.or_eq_true] at hf
      rcases hf with h1 | h2
      · simp [purePairClass, S.zero_rep_eq_zero hz0 pair.1 h1]
      · simp [purePairClass, S.zero_rep_eq_zero hz0 pair.2 h2])
  rcases hex with ⟨p0, hp0, hpg0⟩
  have hsub := countP_le_sub_one S.terminals (fun pair => !((S.repOf pair.1).1 || (S.repOf pair.2).1))
    p0 hp0 (by simp [hpg0])
  have hlen := S.hterm_len; omega

-- Lemma 1: gVal is clean!
lemma solve_g_clean (S : Setup) (hgClean : (S.gVal &&& BAD) = 0#21) : False := by
  have hgCleanAB : (orMask S.A &&& orMask S.B &&& BAD) = 0#21 := by rw [← S.hgVal]; exact hgClean
  let gCls := purePairClass S.gs S.A S.B
  by_cases hzg0 : S.zeroGates.length = 0
  · let pairCls : BitVec 5 × BitVec 5 → Option (Fin 8 × Fin 8) := fun pair =>
      if (S.repOf pair.1).1 || (S.repOf pair.2).1 then gCls
      else purePairClass S.gs (S.repOf pair.1).2 (S.repOf pair.2).2
    let H : List (Fin 8 × Fin 8) := S.terminals.flatMap fun pair => (pairCls pair).toList
    have hHlen : H.length ≤ 5 := by
      have h1 := flatMap_option_length_le S.terminals pairCls; have h2 := S.hterm_len; dsimp only [H]; omega
    have hcov : ∀ e : Fin 11, H.any (fun vc => coversClass (fun v => buildComp v S.gs) vc e) = true := by
      intro e
      obtain ⟨pair, hp, he⟩ := S.hedge_cov e
      change (evalWire S.gVal (S.repOf pair.1) &&& evalWire S.gVal (S.repOf pair.2)).getLsbD e.val = true at he
      by_cases hu : ((S.repOf pair.1).1 || (S.repOf pair.2).1) = true
      · rw [evalWire_and_expand] at he
        have hp0 : orMask (S.repOf pair.1).2 &&& orMask (S.repOf pair.2).2 = 0#21 := by
          have hu' := hu; simp only [Bool.or_eq_true] at hu'
          rcases hu' with h1 | h2
          · rw [S.zero_rep_eq_zero hzg0 pair.1 h1, orMask_zero]; simp
          · rw [S.zero_rep_eq_zero hzg0 pair.2 h2, orMask_zero]; simp
        rw [hp0] at he
        have hge : (orMask S.A &&& orMask S.B).getLsbD e.val = true := by
          rw [← S.hgVal]
          cases h1 : (S.repOf pair.1).1 <;> cases h2 : (S.repOf pair.2).1 <;> simp [h1, h2] at hu he ⊢
          · exact he.1
          · exact he.1
          · rcases he with (h | h) | h; exact h; exact h.1; exact h.1
        obtain ⟨vc, hvc, hce⟩ := purePairClass_covers S.gs S.A S.B hgCleanAB
          (fun v h => S.hA_comp (nbrs v) h) (fun v h => S.hB_comp (nbrs v) h) e hge
        rw [List.any_eq_true]
        refine ⟨vc, List.mem_flatMap.mpr ⟨pair, hp, ?_⟩, hce⟩
        dsimp only [pairCls]; rw [if_pos hu]; simp [gCls, hvc]
      · simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hu
        simp only [evalWire, hu.1, hu.2, Bool.false_eq_true, ↓reduceIte, BitVec.zero_or] at he
        obtain ⟨vc, hvc, hce⟩ := purePairClass_covers S.gs (S.repOf pair.1).2 (S.repOf pair.2).2
          (S.clean_parts pair hp).2.2.2 (S.rep_const pair.1) (S.rep_const pair.2) e he
        rw [List.any_eq_true]
        refine ⟨vc, List.mem_flatMap.mpr ⟨pair, hp, ?_⟩, hce⟩
        dsimp only [pairCls]; simp [hu.1, hu.2, hvc]
    have hbound := master_cover_bound S.gs H hcov
    have hsum := sum_isMergeFor_le S.gs
    have h4 := S.hlen4; omega
  · let H : List (Fin 8 × Fin 8) :=
      gCls.toList ++ S.terminals.flatMap fun pair => (purePairClass S.gs (S.repOf pair.1).2 (S.repOf pair.2).2).toList
    have hHlen : H.length ≤ 6 := by
      rw [List.length_append]
      have h1 := option_toList_length gCls
      have h2 := flatMap_option_length_le S.terminals (fun pair => purePairClass S.gs (S.repOf pair.1).2 (S.repOf pair.2).2)
      have h3 := S.hterm_len; omega
    have hcov : ∀ e : Fin 11, H.any (fun vc => coversClass (fun v => buildComp v S.gs) vc e) = true := by
      intro e
      obtain ⟨pair, hp, he⟩ := S.hedge_cov e
      change (evalWire S.gVal (S.repOf pair.1) &&& evalWire S.gVal (S.repOf pair.2)).getLsbD e.val = true at he
      rw [evalWire_and_expand] at he
      by_cases hpure : (orMask (S.repOf pair.1).2 &&& orMask (S.repOf pair.2).2).getLsbD e.val = true
      · obtain ⟨vc, hvc, hce⟩ := purePairClass_covers S.gs (S.repOf pair.1).2 (S.repOf pair.2).2
          (S.clean_parts pair hp).2.2.2 (S.rep_const pair.1) (S.rep_const pair.2) e hpure
        rw [List.any_eq_true]
        exact ⟨vc, List.mem_append_right _ (List.mem_flatMap.mpr ⟨pair, hp, by simp [hvc]⟩), hce⟩
      · have hge : (orMask S.A &&& orMask S.B).getLsbD e.val = true := by
          rw [← S.hgVal]
          cases h1 : (S.repOf pair.1).1 <;> cases h2 : (S.repOf pair.2).1 <;> simp [h1, h2, hpure] at he ⊢
          · exact he.1
          · exact he.1
          · rcases he with (h | h) | h; exact h; exact h.1; exact h.1
        obtain ⟨vc, hvc, hce⟩ := purePairClass_covers S.gs S.A S.B hgCleanAB
          (fun v h => S.hA_comp (nbrs v) h) (fun v h => S.hB_comp (nbrs v) h) e hge
        rw [List.any_eq_true]
        exact ⟨vc, List.mem_append_left _ (by simp [gCls, hvc]), hce⟩
    have hbound := master_cover_bound S.gs H hcov
    have hsum := sum_isMergeFor_le S.gs
    have := S.hlen4; omega

-- Lemma 2: gVal = orMask W (covers sub8 A B or sub8 B A) when gVal is NOT clean!
lemma solve_g_eq_orMask (S : Setup) (hgClean : (S.gVal &&& BAD) ≠ 0#21)
    (W : BitVec 8) (hgW : S.gVal = orMask W)
    (hW_comp : ∀ v : Fin 8, sub8 W (nbrs v) = true →
      ∀ x y : Fin 8, hasBit W x = true → hasBit W y = true → buildComp v S.gs x = buildComp v S.gs y) :
    False := by
  have hnot_both : ∀ pair ∈ S.terminals, ¬ ((S.repOf pair.1).1 = true ∧ (S.repOf pair.2).1 = true) := by
    intro pair hp ⟨h1, h2⟩
    have h := (S.clean_parts pair hp).1; simp [h1, h2] at h; exact hgClean h
  have hWne : W ≠ 0#8 := fun h => hgClean (by rw [hgW, h, orMask_zero]; simp)
  by_cases hW1 : pop8 W ≤ 1
  · have hWeq : pop8 W = 1 := by
      have hne0 : pop8 W ≠ 0 := fun hz => hWne ((pop8_eq_zero_iff W).mp hz); omega
    obtain ⟨w0, rfl⟩ := (pop8_eq_one_iff W).mp hWeq
    let pairCls : BitVec 5 × BitVec 5 → Option (Fin 8 × Fin 8) := fun pair =>
      if (S.repOf pair.1).1 && ((S.repOf pair.1).2 == 0#8) then purePairClass S.gs (bitOf w0) (S.repOf pair.2).2
      else if (S.repOf pair.2).1 && ((S.repOf pair.2).2 == 0#8) then purePairClass S.gs (bitOf w0) (S.repOf pair.1).2
      else purePairClass S.gs (S.repOf pair.1).2 (S.repOf pair.2).2
    let H_pure : List (Fin 8 × Fin 8) := S.terminals.flatMap fun pair => (pairCls pair).toList
    let H_zero : List (Fin 8 × Fin 8) :=
      S.zeroGates.flatMap fun z =>
        match (List.finRange 8).find? (fun c => adj (firstBit z) c && adj w0 c) with
        | some c => [(w0, buildComp w0 S.gs c)]
        | none => []
    let H := H_pure ++ H_zero
    have hHlen : H.length ≤ 5 + S.zeroGates.length := by
      rw [List.length_append]
      have h1 := flatMap_option_length_le S.terminals pairCls
      have h2 : H_zero.length ≤ S.zeroGates.length := by
        dsimp only [H_zero]
        have hgen : ∀ l : List (BitVec 8), (l.flatMap fun z =>
            match (List.finRange 8).find? (fun c => adj (firstBit z) c && adj w0 c) with
            | some c => [(w0, buildComp w0 S.gs c)]
            | none => []).length ≤ l.length := by
          intro l; induction l with
          | nil => simp
          | cons x xs ih =>
            simp only [List.flatMap_cons, List.length_append, List.length_cons]
            cases (List.finRange 8).find? (fun c => adj (firstBit x) c && adj w0 c) <;>
              simp only [List.length_nil, List.length_singleton, Nat.zero_add] <;> omega
        exact hgen S.zeroGates
      have h3 := S.hterm_len; dsimp only [H_pure]; omega
    -- Symmetric helper when uIdx has usesG = true, vIdx has usesG = false!
    have hmixed : ∀ (e : Fin 11) (pair : BitVec 5 × BitVec 5) (hp : pair ∈ S.terminals)
        (uIdx vIdx : BitVec 5),
        (S.repOf uIdx).1 = true → (S.repOf vIdx).1 = false →
        (orMask (bitOf w0) &&& orMask (S.repOf vIdx).2 &&& BAD) = 0#21 →
        (orMask (S.repOf uIdx).2 &&& orMask (S.repOf vIdx).2 &&& BAD) = 0#21 →
        ((orMask (bitOf w0) &&& orMask (S.repOf vIdx).2) |||
         (orMask (S.repOf uIdx).2 &&& orMask (S.repOf vIdx).2)).getLsbD e.val = true →
        (∀ vc, (S.repOf uIdx).2 = 0#8 → purePairClass S.gs (bitOf w0) (S.repOf vIdx).2 = some vc →
          vc ∈ H_pure) →
        (∀ vc, (S.repOf uIdx).2 ≠ 0#8 → purePairClass S.gs (S.repOf pair.1).2 (S.repOf pair.2).2 = some vc →
          vc ∈ H_pure) →
        ((S.repOf uIdx).2 = (S.repOf pair.1).2 ∧ (S.repOf vIdx).2 = (S.repOf pair.2).2 ∨
         (S.repOf uIdx).2 = (S.repOf pair.2).2 ∧ (S.repOf vIdx).2 = (S.repOf pair.1).2) →
        H.any (fun vc => coversClass (fun v => buildComp v S.gs) vc e) = true := by
      intro e pair hp uIdx vIdx hu1 _ hcW hcP heUV hIn0 hInP hSym
      by_cases hu0 : (S.repOf uIdx).2 = 0#8
      · simp only [hu0, orMask_zero, BitVec.zero_and, BitVec.or_zero] at heUV
        obtain ⟨vc, hvc, hce⟩ := purePairClass_covers S.gs (bitOf w0) (S.repOf vIdx).2 hcW
          hW_comp (S.rep_const vIdx) e heUV
        rw [List.any_eq_true]
        exact ⟨vc, List.mem_append_left _ (hIn0 vc hu0 hvc), hce⟩
      · by_cases hpure : (orMask (S.repOf uIdx).2 &&& orMask (S.repOf vIdx).2).getLsbD e.val = true
        · have hpure' : (orMask (S.repOf pair.1).2 &&& orMask (S.repOf pair.2).2).getLsbD e.val = true := by
            rcases hSym with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · rw [← h1, ← h2]; exact hpure
            · rw [← h1, ← h2, BitVec.and_comm]; exact hpure
          obtain ⟨vc, hvc, hce⟩ := purePairClass_covers S.gs (S.repOf pair.1).2 (S.repOf pair.2).2
            (S.clean_parts pair hp).2.2.2 (S.rep_const pair.1) (S.rep_const pair.2) e hpure'
          rw [List.any_eq_true]
          exact ⟨vc, List.mem_append_left _ (hInP vc hu0 hvc), hce⟩
        · have hge : (orMask (bitOf w0) &&& orMask (S.repOf vIdx).2).getLsbD e.val = true := by
            rw [BitVec.getLsbD_or, Bool.or_eq_true] at heUV
            rcases heUV with h | h; exact h; exact absurd h hpure
          have hCne : (S.repOf vIdx).2 ≠ 0#8 := fun hz => by rw [hz, orMask_zero] at hge; simp at hge
          by_cases hC2 : 2 ≤ pop8 (S.repOf vIdx).2
          · exfalso
            have hDC := clean_pair_is_star (S.repOf uIdx).2 (S.repOf vIdx).2 hcP hu0 hCne
            have hD1 : ∃ d : Fin 8, (S.repOf uIdx).2 = bitOf d ∧ sub8 (S.repOf vIdx).2 (nbrs d) = true := by
              rcases hDC with h | ⟨v, hv, _⟩
              · exact h
              · have : pop8 (S.repOf vIdx).2 = 1 := (pop8_eq_one_iff _).mpr ⟨v, hv⟩; omega
            rcases hD1 with ⟨d, hDeq, hCsubD⟩
            have hCsubW : sub8 (S.repOf vIdx).2 (nbrs w0) = true := (sub8_iff _ _).mpr fun c hc => by
              rw [hasBit_nbrs]; exact clean_pair_adj (bitOf w0) _ hcW w0 c (by simp [hasBit_bitOf]) hc
            have hdw : d = w0 := star_center_unique (S.repOf vIdx).2 hC2 d w0 hCsubD hCsubW
            subst hdw; rw [hDeq] at hpure; exact hpure hge
          · have hCeq : pop8 (S.repOf vIdx).2 = 1 := by
              have hne0 : pop8 (S.repOf vIdx).2 ≠ 0 := fun hz => hCne ((pop8_eq_zero_iff _).mp hz); omega
            obtain ⟨c, hCbit⟩ := (pop8_eq_one_iff _).mp hCeq
            by_cases hw0D : hasBit (S.repOf uIdx).2 w0 = true
            · exfalso; apply hpure; rw [hCbit] at hge ⊢
              simp only [BitVec.getLsbD_and, Bool.and_eq_true, orMask_edge_bit, Bool.or_eq_true,
                hasBit_bitOf, beq_iff_eq] at hge ⊢
              refine ⟨?_, hge.2⟩
              rcases hge.1 with rfl | rfl; exact Or.inl hw0D; exact Or.inr hw0D
            · have hum : S.repOf uIdx ∈ S.reps := by
                rcases S.rep_in uIdx with hm | h0; exact hm; simp [h0] at hu1
              obtain ⟨z, hz, hzsub⟩ := S.hzeroAnc (S.repOf uIdx) hum hu1 hu0
              let d0 := firstBit z
              have hd0D : hasBit (S.repOf uIdx).2 d0 = true :=
                (sub8_iff _ _).mp hzsub d0 (firstBit_mem z (S.hzne z hz))
              have hd0ne : d0 ≠ w0 := fun h => by subst h; simp [hd0D] at hw0D
              have hadj_dc : adj d0 c = true :=
                clean_pair_adj (S.repOf uIdx).2 (S.repOf vIdx).2 hcP d0 c hd0D (by rw [hCbit]; simp [hasBit_bitOf])
              have hadj_wc : adj w0 c = true :=
                clean_pair_adj (bitOf w0) (S.repOf vIdx).2 hcW w0 c (by simp [hasBit_bitOf]) (by rw [hCbit]; simp [hasBit_bitOf])
              have hfind : (List.finRange 8).find? (fun x => adj d0 x && adj w0 x) = some c := by
                cases hf : (List.finRange 8).find? (fun x => adj d0 x && adj w0 x) with
                | none => have := List.find?_eq_none.mp hf c (List.mem_finRange c); simp [hadj_dc, hadj_wc] at this
                | some c' =>
                  have hsm := List.find?_some hf; simp only [Bool.and_eq_true] at hsm
                  have hcc' : c' = c := by by_contra hne; exact adj_c4_free d0 w0 c' c hd0ne hne hsm.1 hadj_dc hsm.2 hadj_wc
                  rw [hcc']
              rw [hCbit] at hge
              simp only [BitVec.getLsbD_and, Bool.and_eq_true, orMask_edge_bit, Bool.or_eq_true,
                hasBit_bitOf, beq_iff_eq] at hge
              rw [List.any_eq_true]
              refine ⟨(w0, buildComp w0 S.gs c),
                List.mem_append_right _ (List.mem_flatMap.mpr ⟨z, hz, by simp [d0, hfind]⟩), ?_⟩
              rcases hge with ⟨rfl | rfl, h2 | h2⟩
              · rw [← h2] at hadj_wc; simp [adj_irrefl] at hadj_wc
              · rw [h2]; simp [coversClass]
              · rw [h2]; simp [coversClass]
              · rw [← h2] at hadj_wc; simp [adj_irrefl] at hadj_wc
    have hcov : ∀ e : Fin 11, H.any (fun vc => coversClass (fun v => buildComp v S.gs) vc e) = true := by
      intro e
      obtain ⟨pair, hp, he⟩ := S.hedge_cov e
      change (evalWire S.gVal (S.repOf pair.1) &&& evalWire S.gVal (S.repOf pair.2)).getLsbD e.val = true at he
      have hcp := S.clean_parts pair hp
      cases h1 : (S.repOf pair.1).1 <;> cases h2 : (S.repOf pair.2).1
      · simp only [evalWire, h1, h2, Bool.false_eq_true, ↓reduceIte, BitVec.zero_or] at he
        obtain ⟨vc, hvc, hce⟩ := purePairClass_covers S.gs (S.repOf pair.1).2 (S.repOf pair.2).2 hcp.2.2.2
          (S.rep_const pair.1) (S.rep_const pair.2) e he
        rw [List.any_eq_true]
        refine ⟨vc, List.mem_append_left _ (List.mem_flatMap.mpr ⟨pair, hp, ?_⟩), hce⟩
        dsimp only [pairCls]; simp [h1, h2, hvc]
      · rw [evalWire_and_expand] at he
        simp only [h1, h2, Bool.false_and, Bool.false_eq_true, ↓reduceIte, BitVec.zero_or, hgW] at he
        have hcW := hcp.2.2.1; simp [h2, hgW] at hcW
        have hcP : (orMask (S.repOf pair.2).2 &&& orMask (S.repOf pair.1).2 &&& BAD) = 0#21 := by
          rw [← hcp.2.2.2]; apply BitVec.eq_of_getLsbD_eq; intro k _; simp [Bool.and_comm, Bool.and_left_comm]
        have he' : ((orMask (bitOf w0) &&& orMask (S.repOf pair.1).2) |||
            (orMask (S.repOf pair.2).2 &&& orMask (S.repOf pair.1).2)).getLsbD e.val = true := by
          rw [BitVec.and_comm (orMask (S.repOf pair.2).2) (orMask (S.repOf pair.1).2)]; exact he
        apply hmixed e pair hp pair.2 pair.1 h2 h1 hcW hcP he'
        · intro vc h20 hvc
          refine List.mem_flatMap.mpr ⟨pair, hp, ?_⟩
          dsimp only [pairCls]; simp [h1, h2, h20, hvc]
        · intro vc h2ne hvc
          refine List.mem_flatMap.mpr ⟨pair, hp, ?_⟩
          dsimp only [pairCls]; simp [h1, h2, h2ne, hvc]
        · exact Or.inr ⟨rfl, rfl⟩
      · rw [evalWire_and_expand] at he
        simp only [h1, h2, Bool.and_false, Bool.false_eq_true, ↓reduceIte, BitVec.zero_or, BitVec.or_zero, hgW] at he
        have hcW := hcp.2.1; simp [h1, hgW] at hcW
        apply hmixed e pair hp pair.1 pair.2 h1 h2 hcW hcp.2.2.2 he
        · intro vc h10 hvc
          refine List.mem_flatMap.mpr ⟨pair, hp, ?_⟩
          dsimp only [pairCls]; simp [h1, h10, hvc]
        · intro vc h1ne hvc
          refine List.mem_flatMap.mpr ⟨pair, hp, ?_⟩
          dsimp only [pairCls]; simp [h1, h2, h1ne, hvc]
        · exact Or.inl ⟨rfl, rfl⟩
      · exact absurd ⟨h1, h2⟩ (hnot_both pair hp)
    have hbound := master_cover_bound S.gs H hcov
    have hsum := sum_isMergeFor_le S.gs
    have h4 := S.hlen4; omega
  · have hW2 : 2 ≤ pop8 W := by omega
    let gWCls : Option (Fin 8 × Fin 8) :=
      match (List.finRange 8).find? (fun z => sub8 W (nbrs z)) with
      | some zW => some (zW, buildComp zW S.gs (firstBit W))
      | none => none
    have hWC_cov : ∀ (C : BitVec 8) (e : Fin 11),
        (orMask W &&& orMask C &&& BAD) = 0#21 →
        (orMask W &&& orMask C).getLsbD e.val = true →
        ∃ vc : Fin 8 × Fin 8, gWCls = some vc ∧ coversClass (fun v => buildComp v S.gs) vc e = true := by
      intro C e hcWC heWC
      have hCne : C ≠ 0#8 := fun h => by rw [h, orMask_zero] at heWC; simp at heWC
      have hzC : ∃ zW : Fin 8, C = bitOf zW ∧ sub8 W (nbrs zW) = true := by
        rcases clean_pair_is_star W C hcWC hWne hCne with ⟨u, hu, _⟩ | h
        · have : pop8 W = 1 := (pop8_eq_one_iff W).mpr ⟨u, hu⟩; omega
        · exact h
      rcases hzC with ⟨zW, rfl, hWsub⟩
      have hfind : (List.finRange 8).find? (fun z => sub8 W (nbrs z)) = some zW := by
        cases hf : (List.finRange 8).find? (fun z => sub8 W (nbrs z)) with
        | none => have := List.find?_eq_none.mp hf zW (List.mem_finRange zW); simp [hWsub] at this
        | some z' =>
          have hsm : sub8 W (nbrs z') = true := List.find?_some (p := fun z => sub8 W (nbrs z)) hf
          rw [star_center_unique W hW2 z' zW hsm hWsub]
      refine ⟨(zW, buildComp zW S.gs (firstBit W)), by simp [gWCls, hfind], ?_⟩
      simp only [BitVec.getLsbD_and, Bool.and_eq_true, orMask_edge_bit, Bool.or_eq_true,
        hasBit_bitOf, beq_iff_eq] at heWC
      have hfbW := firstBit_mem W hWne
      rcases heWC with ⟨h1 | h1, h2 | h2⟩
      · subst h2
        exact absurd (clean_pair_adj W (bitOf (edgeU e)) hcWC (edgeU e) (edgeU e) h1 (by simp [hasBit_bitOf]))
          (by simp [adj_irrefl])
      · subst h2; dsimp only [coversClass]; rw [hW_comp (edgeV e) hWsub (edgeU e) (firstBit W) h1 hfbW]; simp
      · subst h2; dsimp only [coversClass]; rw [hW_comp (edgeU e) hWsub (edgeV e) (firstBit W) h1 hfbW]; simp
      · subst h2
        exact absurd (clean_pair_adj W (bitOf (edgeV e)) hcWC (edgeV e) (edgeV e) h1 (by simp [hasBit_bitOf]))
          (by simp [adj_irrefl])
    by_cases hzg0 : S.zeroGates.length = 0
    · let pairCls : BitVec 5 × BitVec 5 → Option (Fin 8 × Fin 8) := fun pair =>
        if (S.repOf pair.1).1 || (S.repOf pair.2).1 then gWCls
        else purePairClass S.gs (S.repOf pair.1).2 (S.repOf pair.2).2
      let H : List (Fin 8 × Fin 8) := S.terminals.flatMap fun pair => (pairCls pair).toList
      have hHlen : H.length ≤ 5 := by
        have h1 := flatMap_option_length_le S.terminals pairCls; have h2 := S.hterm_len; dsimp only [H]; omega
      have hcov : ∀ e : Fin 11, H.any (fun vc => coversClass (fun v => buildComp v S.gs) vc e) = true := by
        intro e
        obtain ⟨pair, hp, he⟩ := S.hedge_cov e
        change (evalWire S.gVal (S.repOf pair.1) &&& evalWire S.gVal (S.repOf pair.2)).getLsbD e.val = true at he
        have hcp := S.clean_parts pair hp
        by_cases hu : ((S.repOf pair.1).1 || (S.repOf pair.2).1) = true
        · have hWC : ∃ C : BitVec 8, (orMask W &&& orMask C &&& BAD) = 0#21 ∧
              (orMask W &&& orMask C).getLsbD e.val = true := by
            have hu' := hu; simp only [Bool.or_eq_true] at hu'
            rcases hu' with h1 | h2
            · have h2f : (S.repOf pair.2).1 = false := by
                cases h : (S.repOf pair.2).1; rfl; exact absurd ⟨h1, h⟩ (hnot_both pair hp)
              have h1z := S.zero_rep_eq_zero hzg0 pair.1 h1
              simp only [evalWire, h1, h2f, h1z, ↓reduceIte, Bool.false_eq_true, orMask_zero,
                BitVec.or_zero, BitVec.zero_or, hgW] at he
              have hc := hcp.2.1; simp [h1, hgW] at hc
              exact ⟨(S.repOf pair.2).2, hc, he⟩
            · have h1f : (S.repOf pair.1).1 = false := by
                cases h : (S.repOf pair.1).1; rfl; exact absurd ⟨h, h2⟩ (hnot_both pair hp)
              have h2z := S.zero_rep_eq_zero hzg0 pair.2 h2
              simp only [evalWire, h1f, h2, h2z, ↓reduceIte, Bool.false_eq_true, orMask_zero,
                BitVec.or_zero, BitVec.zero_or, hgW] at he
              have hc := hcp.2.2.1; simp [h2, hgW] at hc
              exact ⟨(S.repOf pair.1).2, hc, by rw [BitVec.and_comm]; exact he⟩
          rcases hWC with ⟨C, hcWC, heWC⟩
          obtain ⟨vc, hvc, hce⟩ := hWC_cov C e hcWC heWC
          rw [List.any_eq_true]
          refine ⟨vc, List.mem_flatMap.mpr ⟨pair, hp, ?_⟩, hce⟩
          dsimp only [pairCls]; rw [if_pos hu]; simp [hvc]
        · simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hu
          simp only [evalWire, hu.1, hu.2, Bool.false_eq_true, ↓reduceIte, BitVec.zero_or] at he
          obtain ⟨vc, hvc, hce⟩ := purePairClass_covers S.gs (S.repOf pair.1).2 (S.repOf pair.2).2 hcp.2.2.2
            (S.rep_const pair.1) (S.rep_const pair.2) e he
          rw [List.any_eq_true]
          refine ⟨vc, List.mem_flatMap.mpr ⟨pair, hp, ?_⟩, hce⟩
          dsimp only [pairCls]; simp [hu.1, hu.2, hvc]
      have hbound := master_cover_bound S.gs H hcov
      have hsum := sum_isMergeFor_le S.gs
      have h4 := S.hlen4; omega
    · let H : List (Fin 8 × Fin 8) :=
        gWCls.toList ++ S.terminals.flatMap fun pair => (purePairClass S.gs (S.repOf pair.1).2 (S.repOf pair.2).2).toList
      have hHlen : H.length ≤ 6 := by
        rw [List.length_append]
        have h1 := option_toList_length gWCls
        have h2 := flatMap_option_length_le S.terminals (fun pair => purePairClass S.gs (S.repOf pair.1).2 (S.repOf pair.2).2)
        have h3 := S.hterm_len; omega
      have hcov : ∀ e : Fin 11, H.any (fun vc => coversClass (fun v => buildComp v S.gs) vc e) = true := by
        intro e
        obtain ⟨pair, hp, he⟩ := S.hedge_cov e
        change (evalWire S.gVal (S.repOf pair.1) &&& evalWire S.gVal (S.repOf pair.2)).getLsbD e.val = true at he
        have hcp := S.clean_parts pair hp
        rw [evalWire_and_expand] at he
        by_cases hpure : (orMask (S.repOf pair.1).2 &&& orMask (S.repOf pair.2).2).getLsbD e.val = true
        · obtain ⟨vc, hvc, hce⟩ := purePairClass_covers S.gs (S.repOf pair.1).2 (S.repOf pair.2).2 hcp.2.2.2
            (S.rep_const pair.1) (S.rep_const pair.2) e hpure
          rw [List.any_eq_true]
          exact ⟨vc, List.mem_append_right _ (List.mem_flatMap.mpr ⟨pair, hp, by simp [hvc]⟩), hce⟩
        · have hWC : ∃ C : BitVec 8, (orMask W &&& orMask C &&& BAD) = 0#21 ∧
              (orMask W &&& orMask C).getLsbD e.val = true := by
            cases h1 : (S.repOf pair.1).1 <;> cases h2 : (S.repOf pair.2).1
            · simp only [h1, h2, Bool.false_and, Bool.false_eq_true, ↓reduceIte, BitVec.zero_or] at he
              exact absurd he hpure
            · simp only [h1, h2, Bool.false_and, Bool.false_eq_true, ↓reduceIte, BitVec.zero_or, hgW] at he
              rw [BitVec.getLsbD_or, Bool.or_eq_true] at he
              have hc := hcp.2.2.1; simp [h2, hgW] at hc
              exact ⟨(S.repOf pair.1).2, hc, he.resolve_right hpure⟩
            · simp only [h1, h2, Bool.and_false, Bool.false_eq_true, ↓reduceIte, BitVec.zero_or, BitVec.or_zero, hgW] at he
              rw [BitVec.getLsbD_or, Bool.or_eq_true] at he
              have hc := hcp.2.1; simp [h1, hgW] at hc
              exact ⟨(S.repOf pair.2).2, hc, he.resolve_right hpure⟩
            · exact absurd ⟨h1, h2⟩ (hnot_both pair hp)
          rcases hWC with ⟨C, hcWC, heWC⟩
          obtain ⟨vc, hvc, hce⟩ := hWC_cov C e hcWC heWC
          rw [List.any_eq_true]
          exact ⟨vc, List.mem_append_left _ (by simp [hvc]), hce⟩
      have hbound := master_cover_bound S.gs H hcov
      have hsum := sum_isMergeFor_le S.gs
      have h4 := S.hlen4; omega

-- Lemma 3: pop8 X = 1, X ⊄ Y, gVal = orMask X &&& orMask Y not clean!
lemma solve_pop1 (S : Setup) (hgClean : (S.gVal &&& BAD) ≠ 0#21)
    (X Y : BitVec 8) (hgXY : S.gVal = orMask X &&& orMask Y)
    (hX1 : pop8 X = 1) (hnotXY : sub8 X Y = false)
    (hY_gs : pop8 Y ≤ 1 ∨ ∃ p ∈ S.gs, p.1 ||| p.2 = Y)
    (hY_comp : ∀ mask : BitVec 8, sub8 Y mask = true →
      ∀ x y : Fin 8, hasBit Y x = true → hasBit Y y = true → buildCompIn mask S.gs x = buildCompIn mask S.gs y) :
    False := by
  have hnot_both : ∀ pair ∈ S.terminals, ¬ ((S.repOf pair.1).1 = true ∧ (S.repOf pair.2).1 = true) := by
    intro pair hp ⟨h1, h2⟩
    have h := (S.clean_parts pair hp).1; simp [h1, h2] at h; exact hgClean h
  obtain ⟨a0, rfl⟩ := (pop8_eq_one_iff X).mp hX1
  have ha0_notY : hasBit Y a0 = false := by
    cases h : hasBit Y a0
    · rfl
    · have hs : sub8 (bitOf a0) Y = true := (sub8_iff _ _).mpr fun i hi => by
        rw [hasBit_bitOf, beq_iff_eq] at hi; rw [← hi]; exact h
      rw [hs] at hnotXY; contradiction
  have hY_notN : sub8 Y (nbrs a0) = false := by
    cases h : sub8 Y (nbrs a0)
    · rfl
    · exfalso; apply hgClean; rw [hgXY]
      apply BitVec.eq_of_getLsbD_eq; intro k _
      rw [BitVec.getLsbD_and, BitVec.getLsbD_and, BitVec.getLsbD_zero]
      cases h1 : (orMask (bitOf a0)).getLsbD k
      · simp
      · cases h2 : (orMask Y).getLsbD k
        · simp
        · cases hbd : BAD.getLsbD k
          · simp
          · rw [orMask_bitOf] at h1
            rw [orMask_getLsbD, List.any_eq_true] at h2
            rcases h2 with ⟨y, _, hy⟩; simp only [Bool.and_eq_true] at hy
            have hadj : adj a0 y = true := by simpa [hasBit_nbrs] using (sub8_iff _ _).mp h y hy.1
            simp only [adj, beq_iff_eq] at hadj
            have h0 : (M a0 &&& M y &&& BAD).getLsbD k = false := by rw [hadj]; simp
            rw [BitVec.getLsbD_and, BitVec.getLsbD_and, h1, hy.2, hbd] at h0; simp at h0
  let L0 : BitVec 8 := Y &&& nbrs a0
  have hL0_sub : sub8 L0 (nbrs a0) = true := (sub8_iff _ _).mpr fun i hi => by
    simp only [L0, hasBit_and, Bool.and_eq_true] at hi; exact hi.2
  have hg_in_L0 : ∀ (C : BitVec 8) (e : Fin 11),
      (S.gVal &&& orMask C &&& BAD) = 0#21 → (S.gVal &&& orMask C).getLsbD e.val = true →
      (edgeU e = a0 ∧ hasBit L0 (edgeV e) = true) ∨ (edgeV e = a0 ∧ hasBit L0 (edgeU e) = true) := by
    intro C e hc he; rw [hgXY] at hc he
    rcases clean_triple_edge_decomp (bitOf a0) Y C hc e he with
      ⟨x, hxA, hxY, _⟩ | ⟨y, hyA, hyC, _⟩ | ⟨z, hzY, hzC, hzE⟩
    · rw [hasBit_bitOf, beq_iff_eq] at hxA; subst hxA; simp [ha0_notY] at hxY
    · rw [hasBit_bitOf, beq_iff_eq] at hyA; subst hyA
      have hYn : sub8 Y (nbrs a0) = true := (sub8_iff _ _).mpr fun b hb => by
        rw [hasBit_nbrs]; exact clean_triple_adj_AC (bitOf a0) Y C hc a0 b (by simp [hasBit_bitOf]) hyC hb
      rw [hYn] at hY_notN; contradiction
    · have hadj : adj a0 z = true := by
        rw [adj_symm]; exact clean_triple_adj_BC (bitOf a0) Y C hc z a0 hzY hzC (by simp [hasBit_bitOf])
      rcases hzE with ⟨rfl, hA⟩ | ⟨rfl, hA⟩
      · rw [hasBit_bitOf, beq_iff_eq] at hA; subst hA
        exact Or.inr ⟨rfl, by simp [L0, hasBit_and, hzY, hasBit_nbrs, hadj]⟩
      · rw [hasBit_bitOf, beq_iff_eq] at hA; subst hA
        exact Or.inl ⟨rfl, by simp [L0, hasBit_and, hzY, hasBit_nbrs, hadj]⟩
  let H_pure : List (Fin 8 × Fin 8) :=
    S.terminals.flatMap fun pair => (purePairClass S.gs (S.repOf pair.1).2 (S.repOf pair.2).2).toList
  have hH_pure_cov : ∀ e : Fin 11,
      ¬ ((edgeU e = a0 ∧ hasBit L0 (edgeV e) = true) ∨ (edgeV e = a0 ∧ hasBit L0 (edgeU e) = true)) →
      H_pure.any (fun vc => coversClass (fun v => buildComp v S.gs) vc e) = true := by
    intro e hnot
    obtain ⟨pair, hp, he⟩ := S.hedge_cov e
    change (evalWire S.gVal (S.repOf pair.1) &&& evalWire S.gVal (S.repOf pair.2)).getLsbD e.val = true at he
    have hcp := S.clean_parts pair hp
    rw [evalWire_and_expand] at he
    have hpure : (orMask (S.repOf pair.1).2 &&& orMask (S.repOf pair.2).2).getLsbD e.val = true := by
      by_contra hnp
      cases h1 : (S.repOf pair.1).1 <;> cases h2 : (S.repOf pair.2).1
      · simp only [h1, h2, Bool.false_and, Bool.false_eq_true, ↓reduceIte, BitVec.zero_or] at he
        exact hnp he
      · simp only [h1, h2, Bool.false_and, Bool.false_eq_true, ↓reduceIte, BitVec.zero_or] at he
        rw [BitVec.getLsbD_or, Bool.or_eq_true] at he
        have hc := hcp.2.2.1; simp [h2] at hc; exact hnot (hg_in_L0 (S.repOf pair.1).2 e hc (he.resolve_right hnp))
      · simp only [h1, h2, Bool.and_false, Bool.false_eq_true, ↓reduceIte, BitVec.zero_or, BitVec.or_zero] at he
        rw [BitVec.getLsbD_or, Bool.or_eq_true] at he
        have hc := hcp.2.1; simp [h1] at hc; exact hnot (hg_in_L0 (S.repOf pair.2).2 e hc (he.resolve_right hnp))
      · exact absurd ⟨h1, h2⟩ (hnot_both pair hp)
    obtain ⟨vc, hvc, hce⟩ := purePairClass_covers S.gs (S.repOf pair.1).2 (S.repOf pair.2).2 hcp.2.2.2
      (S.rep_const pair.1) (S.rep_const pair.2) e hpure
    rw [List.any_eq_true]
    exact ⟨vc, List.mem_flatMap.mpr ⟨pair, hp, by simp [hvc]⟩, hce⟩
  by_cases hanyG : S.terminals.any (fun pair => (S.repOf pair.1).1 || (S.repOf pair.2).1) = false
  · apply S.pure_only_contra
    intro pair hp; have h := List.any_eq_false.mp hanyG pair hp
    simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at h; exact h
  have hexG : ∃ pair ∈ S.terminals, ((S.repOf pair.1).1 || (S.repOf pair.2).1) = true := by
    have ht : S.terminals.any (fun pair => (S.repOf pair.1).1 || (S.repOf pair.2).1) = true := by
      cases h : S.terminals.any (fun pair => (S.repOf pair.1).1 || (S.repOf pair.2).1)
      · exact absurd h hanyG
      · rfl
    exact List.any_eq_true.mp ht
  have hH5 : H_pure.length ≤ 5 := by
    have h1 := flatMap_option_length_le S.terminals (fun pair => purePairClass S.gs (S.repOf pair.1).2 (S.repOf pair.2).2)
    have h2 := S.hterm_len; dsimp only [H_pure]; omega
  by_cases hYstar : ∃ w : Fin 8, sub8 Y (nbrs w) = true
  · rcases hYstar with ⟨w, hYw⟩
    have hne_wa : w ≠ a0 := fun h => by subst h; rw [hYw] at hY_notN; contradiction
    have hL0_le1 : pop8 L0 ≤ 1 := by
      have hsub : sub8 L0 (nbrs w &&& nbrs a0) = true := (sub8_iff _ _).mpr fun i hi => by
        simp only [L0, hasBit_and, Bool.and_eq_true] at hi ⊢
        exact ⟨(sub8_iff _ _).mp hYw i hi.1, hi.2⟩
      exact le_trans (pop8_le_of_sub _ _ hsub) (pop8_inter_nbrs_le_one w a0 hne_wa)
    have hbound := master_cover_bound_avoid_subset S.gs H_pure a0 L0 hH_pure_cov
    have hsum := sum_isMergeFor_le S.gs
    have h4 := S.hlen4
    by_cases hz0 : S.zeroGates.length = 0
    · have hH4 : H_pure.length ≤ 4 := S.pure_len_z0 hz0 hexG; omega
    · omega
  · have hY_ge2 : 2 ≤ pop8 Y := by
      by_contra hlt
      by_cases hY0 : Y = 0#8
      · exact hYstar ⟨⟨0, by decide⟩, by rw [hY0]; decide⟩
      · have hY1 : pop8 Y = 1 := by
          have hne0 : pop8 Y ≠ 0 := fun hz => hY0 ((pop8_eq_zero_iff Y).mp hz); omega
        obtain ⟨y0, rfl⟩ := (pop8_eq_one_iff Y).mp hY1
        have hexNbr : ∀ y : Fin 8, ∃ w : Fin 8, sub8 (bitOf y) (nbrs w) = true := by decide
        exact hYstar (hexNbr y0)
    have hpY_ex : ∃ pY ∈ S.gs, pY.1 ||| pY.2 = Y := by rcases hY_gs with h1 | h; omega; exact h
    rcases hpY_ex with ⟨pY, hpY_mem, hpY_eq⟩
    have hsum_le : ((List.finRange 8).map (fun v => S.gs.countP (isMergeFor v))).sum + 1 ≤ S.gs.length := by
      have h1 := sum_isMergeFor_le_countP S.gs (fun p => decide (p.1 ||| p.2 ≠ Y))
        (fun p _ v hv => by
          simp only [decide_eq_true_eq]; intro heq
          simp only [isMergeFor, isMergeIn, Bool.and_eq_true, heq] at hv; exact hYstar ⟨v, hv.2⟩)
      have hsub := countP_le_sub_one S.gs (fun p => decide (p.1 ||| p.2 ≠ Y)) pY hpY_mem
        (by simp [hpY_eq])
      omega
    have hpopY_le : pop8 Y ≤ 1 + S.gs.countP (isMergeIn Y) := by
      have hlb := imgLenIn_buildCompIn_lb Y S.gs
      have hub := imgLenIn_le_one_of_const Y (buildCompIn Y S.gs) (hY_comp Y (sub8_refl Y))
      omega
    have hcntY_le : S.gs.countP (isMergeIn Y) ≤ S.gs.length := List.countP_le_length
    have hL0_lt : pop8 L0 + 1 ≤ pop8 Y := pop8_lt_of_not_sub Y (nbrs a0) hY_notN
    have h4 := S.hlen4
    by_cases hz0 : S.zeroGates.length = 0
    · have hH4 : H_pure.length ≤ 4 := S.pure_len_z0 hz0 hexG
      by_cases hL0_3 : pop8 L0 ≤ 3
      · have hbound := master_cover_bound_avoid_subset S.gs H_pure a0 L0 hH_pure_cov; omega
      · have hdeg4 := deg_le_4 a0
        have hL0_le4 : pop8 L0 ≤ pop8 (nbrs a0) := pop8_le_of_sub L0 (nbrs a0) hL0_sub
        have hL0_eq4 : pop8 L0 = 4 := by omega
        have hpopY5 : pop8 Y = 5 := by omega
        have hgs4 : S.gs.length = 4 := by omega
        have hall_in_Y : ∀ p ∈ S.gs, isMergeIn Y p = true := by
          have hcnt4 : S.gs.countP (isMergeIn Y) = 4 := by omega
          intro p hp; by_contra hf
          have hbf : isMergeIn Y p = false := by cases h : isMergeIn Y p; rfl; exact absurd h hf
          have hsub := countP_le_sub_one S.gs (isMergeIn Y) p hp hbf
          omega
        have hpop_other_le2 : ∀ p ∈ S.gs, ∀ v : Fin 8, v ≠ a0 → isMergeFor v p = true →
            pop8 (p.1 ||| p.2) ≤ 2 := by
          intro p hp v hv hmv
          have hpY := hall_in_Y p hp
          simp only [isMergeIn, Bool.and_eq_true] at hpY
          simp only [isMergeFor, isMergeIn, Bool.and_eq_true] at hmv
          let T := p.1 ||| p.2
          have hsp := pop8_split T (nbrs a0)
          have h1 : pop8 (T &&& nbrs a0) ≤ 1 := by
            have hsub : sub8 (T &&& nbrs a0) (nbrs v &&& nbrs a0) = true := (sub8_iff _ _).mpr fun i hi => by
              simp only [hasBit_and, Bool.and_eq_true] at hi ⊢
              exact ⟨(sub8_iff _ _).mp hmv.2 i hi.1, hi.2⟩
            exact le_trans (pop8_le_of_sub _ _ hsub) (pop8_inter_nbrs_le_one v a0 hv)
          have h2 : pop8 (T &&& ~~~nbrs a0) ≤ 1 := by
            have hsub : sub8 (T &&& ~~~nbrs a0) (Y &&& ~~~nbrs a0) = true := (sub8_iff _ _).mpr fun i hi => by
              simp only [hasBit_and, hasBit_not, Bool.and_eq_true] at hi ⊢
              exact ⟨(sub8_iff _ _).mp hpY.2 i hi.1, hi.2⟩
            have hYsp := pop8_split Y (nbrs a0)
            have hYout : pop8 (Y &&& ~~~nbrs a0) = 1 := by change pop8 L0 + _ = pop8 Y at hYsp; omega
            exact le_trans (pop8_le_of_sub _ _ hsub) (by omega)
          change pop8 T ≤ 2; omega
        have hsum_other_le2 :
            (((List.finRange 8).filter (fun v => v != a0)).map (fun v => S.gs.countP (isMergeFor v))).sum ≤ 2 := by
          let otherPred : (BitVec 8 × BitVec 8) → Bool := fun p =>
            (List.finRange 8).any (fun v => (v != a0) && isMergeFor v p)
          have hle_cnt := sum_isMergeFor_filtered_le S.gs (fun v => v != a0) otherPred
            (fun p _ v hv hmv => List.any_eq_true.mpr ⟨v, List.mem_finRange v, by simp [hv, hmv]⟩)
          by_contra hgt
          have hcnt3 : 3 ≤ S.gs.countP otherPred := by omega
          obtain ⟨iY, hiY, hgiY⟩ := List.mem_iff_getElem.mp hpY_mem
          have hnotOther_iY : otherPred S.gs[iY] = false := by
            cases h : otherPred S.gs[iY]
            · rfl
            · rw [List.any_eq_true] at h; rcases h with ⟨v, _, hvm⟩
              simp only [Bool.and_eq_true, bne_iff_ne] at hvm
              have hle2 := hpop_other_le2 S.gs[iY] (List.getElem_mem hiY) v hvm.1 hvm.2
              rw [hgiY, hpY_eq, hpopY5] at hle2; omega
          have hall_other : ∀ (j : Nat) (hj : j < S.gs.length), j ≠ iY → pop8 (S.gs[j].1 ||| S.gs[j].2) ≤ 2 := by
            intro j hj hne
            have htrue_j : otherPred S.gs[j] = true := by
              by_contra hfj
              have hbf : otherPred S.gs[j] = false := by cases h : otherPred S.gs[j]; rfl; exact absurd h hfj
              have h2 := countP_le_sub_two_idx S.gs otherPred j iY hj hiY hne hbf hnotOther_iY
              omega
            rw [List.any_eq_true] at htrue_j; rcases htrue_j with ⟨v, _, hvm⟩
            simp only [Bool.and_eq_true, bne_iff_ne] at hvm
            exact hpop_other_le2 S.gs[j] (List.getElem_mem hj) v hvm.1 hvm.2
          obtain ⟨hc1, hc2⟩ := S.hchain iY hiY
          have hp1 : pop8 S.gs[iY].1 ≤ 2 := by
            rcases hc1 with h | ⟨j, hj, heq⟩; omega; rw [← heq]; exact hall_other j (by omega) (by omega)
          have hp2 : pop8 S.gs[iY].2 ≤ 2 := by
            rcases hc2 with h | ⟨j, hj, heq⟩; omega; rw [← heq]; exact hall_other j (by omega) (by omega)
          have hor := pop8_or_le S.gs[iY].1 S.gs[iY].2
          rw [hgiY] at hp1 hp2 hor
          rw [hpY_eq, hpopY5] at hor; omega
        have hbound := master_cover_bound_avoid_star S.gs H_pure a0 (fun e hu hv =>
          hH_pure_cov e (by rintro (⟨h, _⟩ | ⟨h, _⟩); exact hu h; exact hv h))
        omega
    · have hbound := master_cover_bound_avoid_subset S.gs H_pure a0 L0 hH_pure_cov; omega

-- Lemma 4: pop8 A ≥ 2, pop8 B ≥ 2, A ≠ B, pop8 (A &&& B) ≥ 2!
lemma solve_AB_ge2 (S : Setup) (hgClean : (S.gVal &&& BAD) ≠ 0#21)
    (hA2 : 2 ≤ pop8 S.A) (hB2 : 2 ≤ pop8 S.B) (hABne : S.A ≠ S.B)
    (hAB2 : 2 ≤ pop8 (S.A &&& S.B)) : False := by
  have hnot_both : ∀ pair ∈ S.terminals, ¬ ((S.repOf pair.1).1 = true ∧ (S.repOf pair.2).1 = true) := by
    intro pair hp ⟨h1, h2⟩
    have h := (S.clean_parts pair hp).1; simp [h1, h2] at h; exact hgClean h
  let H_pure : List (Fin 8 × Fin 8) :=
    S.terminals.flatMap fun pair => (purePairClass S.gs (S.repOf pair.1).2 (S.repOf pair.2).2).toList
  have hH5 : H_pure.length ≤ 5 := by
    have h1 := flatMap_option_length_le S.terminals (fun pair => purePairClass S.gs (S.repOf pair.1).2 (S.repOf pair.2).2)
    have h2 := S.hterm_len; dsimp only [H_pure]; omega
  by_cases hexC : ∃ pair ∈ S.terminals,
      ((S.repOf pair.1).1 = true ∧ (S.gVal &&& orMask (S.repOf pair.2).2) ≠ 0#21) ∨
      ((S.repOf pair.2).1 = true ∧ (S.gVal &&& orMask (S.repOf pair.1).2) ≠ 0#21)
  · have hex_c0 : ∃ c0 : Fin 8, sub8 (S.A &&& S.B) (nbrs c0) = true := by
      rcases hexC with ⟨pair, hp, ⟨h1, hne⟩ | ⟨h2, hne⟩⟩
      · have hc := (S.clean_parts pair hp).2.1; simp [h1, S.hgVal] at hc
        have hCne : (S.repOf pair.2).2 ≠ 0#8 := fun hz => hne (by rw [hz, orMask_zero]; simp)
        obtain ⟨c0, hc0⟩ := exists_bit_of_ne_zero _ hCne
        refine ⟨c0, (sub8_iff _ _).mpr fun x hx => ?_⟩
        simp only [hasBit_and, Bool.and_eq_true] at hx; rw [hasBit_nbrs, adj_symm]
        exact clean_triple_adj_AB S.A S.B (S.repOf pair.2).2 hc x c0 hx.1 hx.2 hc0
      · have hc := (S.clean_parts pair hp).2.2.1; simp [h2, S.hgVal] at hc
        have hCne : (S.repOf pair.1).2 ≠ 0#8 := fun hz => hne (by rw [hz, orMask_zero]; simp)
        obtain ⟨c0, hc0⟩ := exists_bit_of_ne_zero _ hCne
        refine ⟨c0, (sub8_iff _ _).mpr fun x hx => ?_⟩
        simp only [hasBit_and, Bool.and_eq_true] at hx; rw [hasBit_nbrs, adj_symm]
        exact clean_triple_adj_AB S.A S.B (S.repOf pair.1).2 hc x c0 hx.1 hx.2 hc0
    rcases hex_c0 with ⟨c0, hc0_sub⟩
    have hg_inc_c0 : ∀ (C : BitVec 8) (e : Fin 11),
        (S.gVal &&& orMask C &&& BAD) = 0#21 → (S.gVal &&& orMask C).getLsbD e.val = true →
        edgeU e = c0 ∨ edgeV e = c0 := by
      intro C e hc he; rw [S.hgVal] at hc he
      have hC_eq : ∀ c : Fin 8, hasBit C c = true → c = c0 := by
        intro c hcc
        have hsubc : sub8 (S.A &&& S.B) (nbrs c) = true := (sub8_iff _ _).mpr fun x hx => by
          simp only [hasBit_and, Bool.and_eq_true] at hx; rw [hasBit_nbrs, adj_symm]
          exact clean_triple_adj_AB S.A S.B C hc x c hx.1 hx.2 hcc
        exact star_center_unique (S.A &&& S.B) hAB2 c c0 hsubc hc0_sub
      simp only [BitVec.getLsbD_and, Bool.and_eq_true, orMask_edge_bit, Bool.or_eq_true] at he
      rcases he.2 with hu | hv; exact Or.inl (hC_eq _ hu); exact Or.inr (hC_eq _ hv)
    have hcov : ∀ e : Fin 11, edgeU e ≠ c0 → edgeV e ≠ c0 →
        H_pure.any (fun vc => coversClass (fun v => buildComp v S.gs) vc e) = true := by
      intro e hu hv
      obtain ⟨pair, hp, he⟩ := S.hedge_cov e
      change (evalWire S.gVal (S.repOf pair.1) &&& evalWire S.gVal (S.repOf pair.2)).getLsbD e.val = true at he
      have hcp := S.clean_parts pair hp; rw [evalWire_and_expand] at he
      have hpure : (orMask (S.repOf pair.1).2 &&& orMask (S.repOf pair.2).2).getLsbD e.val = true := by
        by_contra hnp
        cases h1 : (S.repOf pair.1).1 <;> cases h2 : (S.repOf pair.2).1
        · simp only [h1, h2, Bool.false_and, Bool.false_eq_true, ↓reduceIte, BitVec.zero_or] at he
          exact hnp he
        · simp only [h1, h2, Bool.false_and, Bool.false_eq_true, ↓reduceIte, BitVec.zero_or] at he
          rw [BitVec.getLsbD_or, Bool.or_eq_true] at he
          have hc := hcp.2.2.1; simp [h2] at hc
          rcases hg_inc_c0 (S.repOf pair.1).2 e hc (he.resolve_right hnp) with h | h; exact hu h; exact hv h
        · simp only [h1, h2, Bool.and_false, Bool.false_eq_true, ↓reduceIte, BitVec.zero_or, BitVec.or_zero] at he
          rw [BitVec.getLsbD_or, Bool.or_eq_true] at he
          have hc := hcp.2.1; simp [h1] at hc
          rcases hg_inc_c0 (S.repOf pair.2).2 e hc (he.resolve_right hnp) with h | h; exact hu h; exact hv h
        · exact absurd ⟨h1, h2⟩ (hnot_both pair hp)
      obtain ⟨vc, hvc, hce⟩ := purePairClass_covers S.gs (S.repOf pair.1).2 (S.repOf pair.2).2 hcp.2.2.2
        (S.rep_const pair.1) (S.rep_const pair.2) e hpure
      rw [List.any_eq_true]
      exact ⟨vc, List.mem_flatMap.mpr ⟨pair, hp, by rw [hvc]; simp⟩, hce⟩
    have hpA_ex : ∃ pA ∈ S.gs, pA.1 ||| pA.2 = S.A := by rcases S.hA_gs with h | h; omega; exact h
    have hpB_ex : ∃ pB ∈ S.gs, pB.1 ||| pB.2 = S.B := by rcases S.hB_gs with h | h; omega; exact h
    rcases hpA_ex with ⟨pA, hpA_mem, hpA_eq⟩
    rcases hpB_ex with ⟨pB, hpB_mem, hpB_eq⟩
    have hpAB_ne : pA ≠ pB := fun h => hABne (by rw [← hpA_eq, h, hpB_eq])
    let pPred : (BitVec 8 × BitVec 8) → Bool := fun p => decide (p.1 ||| p.2 ≠ S.A ∧ p.1 ||| p.2 ≠ S.B)
    have hsum_le : (((List.finRange 8).filter (fun v => v != c0)).map (fun v => S.gs.countP (isMergeFor v))).sum + 2 ≤ S.gs.length := by
      have hle1 := sum_isMergeFor_filtered_le S.gs (fun v => v != c0) pPred (fun p _ v hv hmv => by
        simp only [bne_iff_ne] at hv; simp only [isMergeFor, isMergeIn, Bool.and_eq_true] at hmv
        simp only [pPred, decide_eq_true_eq]; constructor
        · intro hEq
          have hsub : sub8 (S.A &&& S.B) (nbrs v) = true := (sub8_iff _ _).mpr fun x hx => by
            simp only [hasBit_and, Bool.and_eq_true] at hx; exact (sub8_iff _ _).mp hmv.2 x (hEq ▸ hx.1)
          exact hv (star_center_unique (S.A &&& S.B) hAB2 v c0 hsub hc0_sub)
        · intro hEq
          have hsub : sub8 (S.A &&& S.B) (nbrs v) = true := (sub8_iff _ _).mpr fun x hx => by
            simp only [hasBit_and, Bool.and_eq_true] at hx; exact (sub8_iff _ _).mp hmv.2 x (hEq ▸ hx.2)
          exact hv (star_center_unique (S.A &&& S.B) hAB2 v c0 hsub hc0_sub))
      have h2false := countP_le_sub_two_mem S.gs pPred pA pB hpA_mem hpB_mem hpAB_ne
        (by simp [pPred, hpA_eq]) (by simp [pPred, hpB_eq])
      omega
    have hbound := master_cover_bound_avoid_star S.gs H_pure c0 hcov
    have hdeg4 := deg_le_4 c0
    have h4 := S.hlen4
    by_cases hz0 : S.zeroGates.length = 0
    · have hexG : ∃ pair ∈ S.terminals, ((S.repOf pair.1).1 || (S.repOf pair.2).1) = true := by
        rcases hexC with ⟨p0, hp0, ⟨h1, _⟩ | ⟨h2, _⟩⟩
        · exact ⟨p0, hp0, by simp [h1]⟩
        · exact ⟨p0, hp0, by simp [h2]⟩
      have hH4 : H_pure.length ≤ 4 := S.pure_len_z0 hz0 hexG; omega
    · omega
  · have hcov : ∀ e : Fin 11, H_pure.any (fun vc => coversClass (fun v => buildComp v S.gs) vc e) = true := by
      intro e
      obtain ⟨pair, hp, he⟩ := S.hedge_cov e
      change (evalWire S.gVal (S.repOf pair.1) &&& evalWire S.gVal (S.repOf pair.2)).getLsbD e.val = true at he
      have hcp := S.clean_parts pair hp; rw [evalWire_and_expand] at he
      have hpure : (orMask (S.repOf pair.1).2 &&& orMask (S.repOf pair.2).2).getLsbD e.val = true := by
        cases h1 : (S.repOf pair.1).1 <;> cases h2 : (S.repOf pair.2).1
        · simp only [h1, h2, Bool.false_and, Bool.false_eq_true, ↓reduceIte, BitVec.zero_or] at he; exact he
        · have hz : S.gVal &&& orMask (S.repOf pair.1).2 = 0#21 := by
            by_contra hne; exact hexC ⟨pair, hp, Or.inr ⟨h2, hne⟩⟩
          simp only [h1, h2, hz, Bool.false_and, Bool.false_eq_true, ↓reduceIte, BitVec.zero_or] at he; exact he
        · have hz : S.gVal &&& orMask (S.repOf pair.2).2 = 0#21 := by
            by_contra hne; exact hexC ⟨pair, hp, Or.inl ⟨h1, hne⟩⟩
          simp only [h1, h2, hz, Bool.and_false, Bool.false_eq_true, ↓reduceIte, BitVec.zero_or, BitVec.or_zero] at he; exact he
        · exact absurd ⟨h1, h2⟩ (hnot_both pair hp)
      obtain ⟨vc, hvc, hce⟩ := purePairClass_covers S.gs (S.repOf pair.1).2 (S.repOf pair.2).2 hcp.2.2.2
        (S.rep_const pair.1) (S.rep_const pair.2) e hpure
      rw [List.any_eq_true]
      exact ⟨vc, List.mem_flatMap.mpr ⟨pair, hp, by rw [hvc]; simp⟩, hce⟩
    have hbound := master_cover_bound S.gs H_pure hcov
    have hsum := sum_isMergeFor_le S.gs
    have h4 := S.hlen4; omega

-- Lemma 5: pop8 A ≥ 2, pop8 B ≥ 2, pop8 (A &&& B) ≤ 1!
lemma solve_AB_le1 (S : Setup) (hgClean : (S.gVal &&& BAD) ≠ 0#21)
    (hA2 : 2 ≤ pop8 S.A) (hB2 : 2 ≤ pop8 S.B) (hAB1 : pop8 (S.A &&& S.B) ≤ 1) : False := by
  have hnot_both : ∀ pair ∈ S.terminals, ¬ ((S.repOf pair.1).1 = true ∧ (S.repOf pair.2).1 = true) := by
    intro pair hp ⟨h1, h2⟩
    have h := (S.clean_parts pair hp).1; simp [h1, h2] at h; exact hgClean h
  have hAne : S.A ≠ 0#8 := fun h => by rw [h] at hA2; exact absurd hA2 (by decide)
  have hBne : S.B ≠ 0#8 := fun h => by rw [h] at hB2; exact absurd hB2 (by decide)
  let zA_opt : Option (Fin 8) := (List.finRange 8).find? (fun z => sub8 S.A (nbrs z) && hasBit S.B z)
  let yB_opt : Option (Fin 8) := (List.finRange 8).find? (fun y => sub8 S.B (nbrs y) && hasBit S.A y)
  let H_AB : List (Fin 8 × Fin 8) :=
    (zA_opt.map (fun z => (z, buildComp z S.gs (firstBit S.A)))).toList ++
    (yB_opt.map (fun y => (y, buildComp y S.gs (firstBit S.B)))).toList
  let x0_opt : Option (Fin 8) := (List.finRange 8).find? (fun x => hasBit (S.A &&& S.B) x)
  let H_zero : List (Fin 8 × Fin 8) :=
    match x0_opt with
    | none => []
    | some x0 =>
      S.zeroGates.flatMap fun z =>
        match (List.finRange 8).find? (fun c => adj (firstBit z) c && adj x0 c) with
        | some c => [(x0, buildComp x0 S.gs c)]
        | none => []
  let pairCls : BitVec 5 × BitVec 5 → Option (Fin 8 × Fin 8) := fun pair =>
    if (S.repOf pair.1).1 && ((S.repOf pair.1).2 == 0#8) then
      match x0_opt with
      | some x0 => if (S.repOf pair.2).2 == 0#8 then none else some (x0, buildComp x0 S.gs (firstBit (S.repOf pair.2).2))
      | none => none
    else if (S.repOf pair.2).1 && ((S.repOf pair.2).2 == 0#8) then
      match x0_opt with
      | some x0 => if (S.repOf pair.1).2 == 0#8 then none else some (x0, buildComp x0 S.gs (firstBit (S.repOf pair.1).2))
      | none => none
    else purePairClass S.gs (S.repOf pair.1).2 (S.repOf pair.2).2
  let H_pure : List (Fin 8 × Fin 8) := S.terminals.flatMap fun pair => (pairCls pair).toList
  let H : List (Fin 8 × Fin 8) := H_pure ++ H_AB ++ H_zero
  have hHpure_le : H_pure.length ≤ 5 := by
    have h1 := flatMap_option_length_le S.terminals pairCls; have h2 := S.hterm_len; dsimp only [H_pure]; omega
  have hHzero_le : H_zero.length ≤ S.zeroGates.length := by
    dsimp only [H_zero]
    cases x0_opt with
    | none => simp
    | some x0 =>
      have hgen : ∀ l : List (BitVec 8), (l.flatMap fun z =>
          match (List.finRange 8).find? (fun c => adj (firstBit z) c && adj x0 c) with
          | some c => [(x0, buildComp x0 S.gs c)]
          | none => []).length ≤ l.length := by
        intro l; induction l with
        | nil => simp
        | cons w ws ih =>
          simp only [List.flatMap_cons, List.length_append, List.length_cons]
          cases (List.finRange 8).find? (fun c => adj (firstBit w) c && adj x0 c) <;>
            simp only [List.length_nil, List.length_singleton, Nat.zero_add] <;> omega
      exact hgen S.zeroGates
  have htriple_piece : ∀ (C : BitVec 8) (e : Fin 11),
      (orMask S.A &&& orMask S.B &&& orMask C &&& BAD) = 0#21 →
      (orMask S.A &&& orMask S.B &&& orMask C).getLsbD e.val = true →
      H_AB.any (fun vc => coversClass (fun v => buildComp v S.gs) vc e) = true ∨
      (∃ x0 : Fin 8, x0_opt = some x0 ∧ hasBit S.A x0 = true ∧ hasBit S.B x0 = true ∧
        sub8 C (nbrs x0) = true ∧
        ((edgeU e = x0 ∧ hasBit C (edgeV e) = true) ∨ (edgeV e = x0 ∧ hasBit C (edgeU e) = true))) := by
    intro C e hc he
    rcases clean_triple_edge_decomp S.A S.B C hc e he with
      ⟨x, hxA, hxB, hxE⟩ | ⟨y, hyA, hyC, hyE⟩ | ⟨z, hzB, hzC, hzE⟩
    · right
      have hfind : x0_opt = some x := by
        dsimp only [x0_opt]
        cases hf : (List.finRange 8).find? (fun u => hasBit (S.A &&& S.B) u) with
        | none => have := List.find?_eq_none.mp hf x (List.mem_finRange x); simp [hasBit_and, hxA, hxB] at this
        | some u => rw [(pop8_le_one_iff (S.A &&& S.B)).mp hAB1 u x (List.find?_some hf) (by simp [hasBit_and, hxA, hxB])]
      have hCsub : sub8 C (nbrs x) = true := (sub8_iff _ _).mpr fun c hcc => by
        rw [hasBit_nbrs]; exact clean_triple_adj_AB S.A S.B C hc x c hxA hxB hcc
      exact ⟨x, hfind, hxA, hxB, hCsub, hxE⟩
    · left
      have hBsub : sub8 S.B (nbrs y) = true := (sub8_iff _ _).mpr fun b hbb => by
        rw [hasBit_nbrs]; exact clean_triple_adj_AC S.A S.B C hc y b hyA hyC hbb
      have hfind : yB_opt = some y := by
        dsimp only [yB_opt]
        cases hf : (List.finRange 8).find? (fun u => sub8 S.B (nbrs u) && hasBit S.A u) with
        | none => have := List.find?_eq_none.mp hf y (List.mem_finRange y); simp [hBsub, hyA] at this
        | some u =>
          have hu := List.find?_some hf; simp only [Bool.and_eq_true] at hu
          rw [star_center_unique S.B hB2 u y hu.1 hBsub]
      rw [List.any_eq_true]
      refine ⟨(y, buildComp y S.gs (firstBit S.B)), List.mem_append_right _ (by simp [hfind]), ?_⟩
      have hfbB := firstBit_mem S.B hBne
      rcases hyE with ⟨rfl, hBv⟩ | ⟨rfl, hBu⟩
      · dsimp only [coversClass, buildComp]; rw [S.hB_comp (nbrs (edgeU e)) hBsub (edgeV e) (firstBit S.B) hBv hfbB]; simp
      · dsimp only [coversClass, buildComp]; rw [S.hB_comp (nbrs (edgeV e)) hBsub (edgeU e) (firstBit S.B) hBu hfbB]; simp
    · left
      have hAsub : sub8 S.A (nbrs z) = true := (sub8_iff _ _).mpr fun a haa => by
        rw [hasBit_nbrs]; exact clean_triple_adj_BC S.A S.B C hc z a hzB hzC haa
      have hfind : zA_opt = some z := by
        dsimp only [zA_opt]
        cases hf : (List.finRange 8).find? (fun u => sub8 S.A (nbrs u) && hasBit S.B u) with
        | none => have := List.find?_eq_none.mp hf z (List.mem_finRange z); simp [hAsub, hzB] at this
        | some u =>
          have hu := List.find?_some hf; simp only [Bool.and_eq_true] at hu
          rw [star_center_unique S.A hA2 u z hu.1 hAsub]
      rw [List.any_eq_true]
      refine ⟨(z, buildComp z S.gs (firstBit S.A)), List.mem_append_left _ (by simp [hfind]), ?_⟩
      have hfbA := firstBit_mem S.A hAne
      rcases hzE with ⟨rfl, hAv⟩ | ⟨rfl, hAu⟩
      · dsimp only [coversClass, buildComp]; rw [S.hA_comp (nbrs (edgeU e)) hAsub (edgeV e) (firstBit S.A) hAv hfbA]; simp
      · dsimp only [coversClass, buildComp]; rw [S.hA_comp (nbrs (edgeV e)) hAsub (edgeU e) (firstBit S.A) hAu hfbA]; simp
  have hmixed : ∀ (e : Fin 11) (pair : BitVec 5 × BitVec 5) (hp : pair ∈ S.terminals)
      (uIdx vIdx : BitVec 5),
      (S.repOf uIdx).1 = true → (S.repOf vIdx).1 = false →
      (S.gVal &&& orMask (S.repOf vIdx).2 &&& BAD) = 0#21 →
      (orMask (S.repOf uIdx).2 &&& orMask (S.repOf vIdx).2 &&& BAD) = 0#21 →
      ((S.gVal &&& orMask (S.repOf vIdx).2) ||| (orMask (S.repOf uIdx).2 &&& orMask (S.repOf vIdx).2)).getLsbD e.val = true →
      (∀ (vc : Fin 8 × Fin 8) (x0 : Fin 8), (S.repOf uIdx).2 = 0#8 → x0_opt = some x0 →
        (if (S.repOf vIdx).2 == 0#8 then none else some (x0, buildComp x0 S.gs (firstBit (S.repOf vIdx).2))) = some vc →
        vc ∈ H_pure) →
      (∀ vc, (S.repOf uIdx).2 ≠ 0#8 → purePairClass S.gs (S.repOf pair.1).2 (S.repOf pair.2).2 = some vc →
        vc ∈ H_pure) →
      ((S.repOf uIdx).2 = (S.repOf pair.1).2 ∧ (S.repOf vIdx).2 = (S.repOf pair.2).2 ∨
       (S.repOf uIdx).2 = (S.repOf pair.2).2 ∧ (S.repOf vIdx).2 = (S.repOf pair.1).2) →
      H.any (fun vc => coversClass (fun v => buildComp v S.gs) vc e) = true := by
    intro e pair hp uIdx vIdx hu1 _ hcG hcP heUV hInZero hInPure hSym
    by_cases hu0 : (S.repOf uIdx).2 = 0#8
    · simp only [hu0, orMask_zero, BitVec.zero_and, BitVec.or_zero] at heUV
      rw [S.hgVal] at hcG heUV
      rcases htriple_piece (S.repOf vIdx).2 e hcG heUV with hAB | ⟨x0, hx0, _, _, hCsub, hxE⟩
      · rw [List.any_eq_true] at hAB ⊢
        rcases hAB with ⟨vc, hvc, hce⟩
        exact ⟨vc, List.mem_append_left _ (List.mem_append_right _ hvc), hce⟩
      · have hCne : (S.repOf vIdx).2 ≠ 0#8 := fun hz => by rw [hz, orMask_zero] at heUV; simp at heUV
        have hfbC := firstBit_mem (S.repOf vIdx).2 hCne
        let vc : Fin 8 × Fin 8 := (x0, buildComp x0 S.gs (firstBit (S.repOf vIdx).2))
        have hvc_mem : vc ∈ H_pure := hInZero vc x0 hu0 hx0 (by simp [beq_false_of_ne hCne, vc])
        rw [List.any_eq_true]
        refine ⟨vc, List.mem_append_left _ (List.mem_append_left _ hvc_mem), ?_⟩
        rcases hxE with ⟨rfl, hvC⟩ | ⟨rfl, huC⟩
        · dsimp only [coversClass, vc]; rw [S.rep_const vIdx (edgeU e) hCsub (edgeV e) (firstBit (S.repOf vIdx).2) hvC hfbC]; simp
        · dsimp only [coversClass, vc]; rw [S.rep_const vIdx (edgeV e) hCsub (edgeU e) (firstBit (S.repOf vIdx).2) huC hfbC]; simp
    · by_cases hpure : (orMask (S.repOf uIdx).2 &&& orMask (S.repOf vIdx).2).getLsbD e.val = true
      · have hpure' : (orMask (S.repOf pair.1).2 &&& orMask (S.repOf pair.2).2).getLsbD e.val = true := by
          rcases hSym with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · rw [← h1, ← h2]; exact hpure
          · rw [← h1, ← h2, BitVec.and_comm]; exact hpure
        obtain ⟨vc, hvc, hce⟩ := purePairClass_covers S.gs (S.repOf pair.1).2 (S.repOf pair.2).2
          (S.clean_parts pair hp).2.2.2 (S.rep_const pair.1) (S.rep_const pair.2) e hpure'
        rw [List.any_eq_true]
        exact ⟨vc, List.mem_append_left _ (List.mem_append_left _ (hInPure vc hu0 hvc)), hce⟩
      · have hge : (S.gVal &&& orMask (S.repOf vIdx).2).getLsbD e.val = true := by
          rw [BitVec.getLsbD_or, Bool.or_eq_true] at heUV
          rcases heUV with h | h; exact h; exact absurd h hpure
        rw [S.hgVal] at hcG hge
        rcases htriple_piece (S.repOf vIdx).2 e hcG hge with hAB | ⟨x0, hx0, _, _, hCsub, hxE⟩
        · rw [List.any_eq_true] at hAB ⊢
          rcases hAB with ⟨vc, hvc, hce⟩
          exact ⟨vc, List.mem_append_left _ (List.mem_append_right _ hvc), hce⟩
        · have hCne : (S.repOf vIdx).2 ≠ 0#8 := fun hz => by rw [hz, orMask_zero] at hge; simp at hge
          by_cases hC2 : 2 ≤ pop8 (S.repOf vIdx).2
          · exfalso; apply hpure
            have hDC := clean_pair_is_star (S.repOf uIdx).2 (S.repOf vIdx).2 hcP hu0 hCne
            have hD1 : ∃ d : Fin 8, (S.repOf uIdx).2 = bitOf d ∧ sub8 (S.repOf vIdx).2 (nbrs d) = true := by
              rcases hDC with h | ⟨v, hv, _⟩
              · exact h
              · have : pop8 (S.repOf vIdx).2 = 1 := (pop8_eq_one_iff _).mpr ⟨v, hv⟩; omega
            rcases hD1 with ⟨d, hDeq, hCsubD⟩
            have hdx : d = x0 := star_center_unique (S.repOf vIdx).2 hC2 d x0 hCsubD hCsub
            subst hdx; rw [hDeq]
            simp only [BitVec.getLsbD_and, Bool.and_eq_true, orMask_edge_bit, Bool.or_eq_true, hasBit_bitOf, beq_iff_eq]
            rcases hxE with ⟨rfl, hvC⟩ | ⟨rfl, huC⟩
            · exact ⟨Or.inl rfl, Or.inr hvC⟩
            · exact ⟨Or.inr rfl, Or.inl huC⟩
          · have hCeq : pop8 (S.repOf vIdx).2 = 1 := by
              have hne0 : pop8 (S.repOf vIdx).2 ≠ 0 := fun hz => hCne ((pop8_eq_zero_iff _).mp hz); omega
            obtain ⟨c, hCbit⟩ := (pop8_eq_one_iff _).mp hCeq
            by_cases hx0D : hasBit (S.repOf uIdx).2 x0 = true
            · exfalso; apply hpure
              simp only [BitVec.getLsbD_and, Bool.and_eq_true, orMask_edge_bit, Bool.or_eq_true]
              rcases hxE with ⟨rfl, hvC⟩ | ⟨rfl, huC⟩
              · exact ⟨Or.inl hx0D, Or.inr hvC⟩
              · exact ⟨Or.inr hx0D, Or.inl huC⟩
            · have hum : S.repOf uIdx ∈ S.reps := by
                rcases S.rep_in uIdx with hm | h0; exact hm; simp [h0] at hu1
              obtain ⟨z, hz, hzsub⟩ := S.hzeroAnc (S.repOf uIdx) hum hu1 hu0
              let d0 := firstBit z
              have hd0D : hasBit (S.repOf uIdx).2 d0 = true :=
                (sub8_iff _ _).mp hzsub d0 (firstBit_mem z (S.hzne z hz))
              have hd0ne : d0 ≠ x0 := fun h => by subst h; simp [hd0D] at hx0D
              have hadj_dc : adj d0 c = true :=
                clean_pair_adj (S.repOf uIdx).2 (S.repOf vIdx).2 hcP d0 c hd0D (by rw [hCbit]; simp [hasBit_bitOf])
              have hadj_xc : adj x0 c = true := by
                simpa [hasBit_nbrs] using (sub8_iff _ _).mp hCsub c (by rw [hCbit]; simp [hasBit_bitOf])
              have hfind : (List.finRange 8).find? (fun w => adj d0 w && adj x0 w) = some c := by
                cases hf : (List.finRange 8).find? (fun w => adj d0 w && adj x0 w) with
                | none => have := List.find?_eq_none.mp hf c (List.mem_finRange c); simp [hadj_dc, hadj_xc] at this
                | some c' =>
                  have hsm := List.find?_some hf; simp only [Bool.and_eq_true] at hsm
                  have hcc' : c' = c := by by_contra hne; exact adj_c4_free d0 x0 c' c hd0ne hne hsm.1 hadj_dc hsm.2 hadj_xc
                  rw [hcc']
              have hvc_mem : (x0, buildComp x0 S.gs c) ∈ H_zero := by
                dsimp only [H_zero]; rw [hx0]; exact List.mem_flatMap.mpr ⟨z, hz, by simp [d0, hfind]⟩
              rw [List.any_eq_true]
              refine ⟨(x0, buildComp x0 S.gs c), List.mem_append_right _ hvc_mem, ?_⟩
              rw [hCbit] at hxE
              rcases hxE with ⟨rfl, hvC⟩ | ⟨rfl, huC⟩
              · rw [hasBit_bitOf, beq_iff_eq] at hvC; rw [hvC]; simp [coversClass]
              · rw [hasBit_bitOf, beq_iff_eq] at huC; rw [huC]; simp [coversClass]
  have hcov : ∀ e : Fin 11, H.any (fun vc => coversClass (fun v => buildComp v S.gs) vc e) = true := by
    intro e
    obtain ⟨pair, hp, he⟩ := S.hedge_cov e
    change (evalWire S.gVal (S.repOf pair.1) &&& evalWire S.gVal (S.repOf pair.2)).getLsbD e.val = true at he
    have hcp := S.clean_parts pair hp
    cases h1 : (S.repOf pair.1).1 <;> cases h2 : (S.repOf pair.2).1
    · simp only [evalWire, h1, h2, Bool.false_eq_true, ↓reduceIte, BitVec.zero_or] at he
      obtain ⟨vc, hvc, hce⟩ := purePairClass_covers S.gs (S.repOf pair.1).2 (S.repOf pair.2).2 hcp.2.2.2
        (S.rep_const pair.1) (S.rep_const pair.2) e he
      rw [List.any_eq_true]
      refine ⟨vc, List.mem_append_left _ (List.mem_append_left _ (List.mem_flatMap.mpr ⟨pair, hp, ?_⟩)), hce⟩
      dsimp only [pairCls]; simp [h1, h2, hvc]
    · rw [evalWire_and_expand] at he
      simp only [h1, h2, Bool.false_and, Bool.false_eq_true, ↓reduceIte, BitVec.zero_or] at he
      have hcG := hcp.2.2.1; simp [h2] at hcG
      have hcP : (orMask (S.repOf pair.2).2 &&& orMask (S.repOf pair.1).2 &&& BAD) = 0#21 := by
        rw [← hcp.2.2.2]; apply BitVec.eq_of_getLsbD_eq; intro k _; simp [Bool.and_comm, Bool.and_left_comm]
      have he' : ((S.gVal &&& orMask (S.repOf pair.1).2) |||
          (orMask (S.repOf pair.2).2 &&& orMask (S.repOf pair.1).2)).getLsbD e.val = true := by
        rw [BitVec.and_comm (orMask (S.repOf pair.2).2) (orMask (S.repOf pair.1).2)]; exact he
      apply hmixed e pair hp pair.2 pair.1 h2 h1 hcG hcP he'
      · intro vc x0 h20 hx hsome
        refine List.mem_flatMap.mpr ⟨pair, hp, ?_⟩
        dsimp only [pairCls]; rw [h1, h2, h20, hx]
        simp only [Bool.false_and, Bool.true_and, beq_self_eq_true, Bool.false_eq_true, ↓reduceIte, hsome, Option.toList_some, List.mem_singleton]
      · intro vc h2ne hvc
        refine List.mem_flatMap.mpr ⟨pair, hp, ?_⟩
        dsimp only [pairCls]; simp [h1, h2, h2ne, hvc]
      · exact Or.inr ⟨rfl, rfl⟩
    · rw [evalWire_and_expand] at he
      simp only [h1, h2, Bool.and_false, Bool.false_eq_true, ↓reduceIte, BitVec.zero_or, BitVec.or_zero] at he
      have hcG := hcp.2.1; simp [h1] at hcG
      apply hmixed e pair hp pair.1 pair.2 h1 h2 hcG hcp.2.2.2 he
      · intro vc x0 h10 hx hsome
        refine List.mem_flatMap.mpr ⟨pair, hp, ?_⟩
        dsimp only [pairCls]; rw [h1, h10, hx]
        simp only [Bool.true_and, beq_self_eq_true, ↓reduceIte, hsome, Option.toList_some, List.mem_singleton]
      · intro vc h1ne hvc
        refine List.mem_flatMap.mpr ⟨pair, hp, ?_⟩
        dsimp only [pairCls]; simp [h1, h2, h1ne, hvc]
      · exact Or.inl ⟨rfl, rfl⟩
    · exact absurd ⟨h1, h2⟩ (hnot_both pair hp)
  have hsum := sum_isMergeFor_le S.gs
  have h4 := S.hlen4
  cases hzA : zA_opt with
  | none =>
    have hHAB_le : H_AB.length ≤ 1 := by
      dsimp only [H_AB]; rw [hzA, List.length_append]
      have h1 := option_toList_length (yB_opt.map fun y => (y, buildComp y S.gs (firstBit S.B)))
      simp only [Option.map_none, Option.toList_none, List.length_nil, Nat.zero_add]; omega
    have hHlen : H.length ≤ 6 + S.zeroGates.length := by simp only [H, List.length_append]; omega
    have hbound := master_cover_bound S.gs H hcov; omega
  | some zA =>
    cases hyB : yB_opt with
    | none =>
      have hHAB_le : H_AB.length ≤ 1 := by
        dsimp only [H_AB]; rw [hyB, List.length_append]
        have h1 := option_toList_length (zA_opt.map fun z => (z, buildComp z S.gs (firstBit S.A)))
        simp only [Option.map_none, Option.toList_none, List.length_nil, Nat.add_zero]; omega
      have hHlen : H.length ≤ 6 + S.zeroGates.length := by simp only [H, List.length_append]; omega
      have hbound := master_cover_bound S.gs H hcov; omega
    | some yB =>
      have hzA_spec := List.find?_some hzA
      have hyB_spec := List.find?_some hyB
      simp only [Bool.and_eq_true] at hzA_spec hyB_spec
      have hadj_zy : adj zA yB = true := by
        simpa [hasBit_nbrs] using (sub8_iff _ _).mp hzA_spec.1 yB hyB_spec.2
      obtain ⟨e0, he0⟩ := edge_exists zA yB hadj_zy
      have hfbA := firstBit_mem S.A hAne
      have hfbB := firstBit_mem S.B hBne
      have hcA : buildComp zA S.gs yB = buildComp zA S.gs (firstBit S.A) :=
        S.hA_comp (nbrs zA) hzA_spec.1 yB (firstBit S.A) hyB_spec.2 hfbA
      have hcB : buildComp yB S.gs zA = buildComp yB S.gs (firstBit S.B) :=
        S.hB_comp (nbrs yB) hyB_spec.1 zA (firstBit S.B) hzA_spec.2 hfbB
      have hmem_zA : (zA, buildComp zA S.gs (firstBit S.A)) ∈ H :=
        List.mem_append_left _ (List.mem_append_right _ (List.mem_append_left _ (by simp [hzA])))
      have hmem_yB : (yB, buildComp yB S.gs (firstBit S.B)) ∈ H :=
        List.mem_append_left _ (List.mem_append_right _ (List.mem_append_right _ (by simp [hyB])))
      have h0U : H.any (fun vc => vc.1 == edgeU e0 && buildComp (edgeU e0) S.gs (edgeV e0) == vc.2) = true := by
        rw [List.any_eq_true]
        rcases he0 with ⟨hU, hV⟩ | ⟨hU, hV⟩
        · rw [hU, hV]; exact ⟨(zA, buildComp zA S.gs (firstBit S.A)), hmem_zA, by simp [hcA]⟩
        · rw [hU, hV]; exact ⟨(yB, buildComp yB S.gs (firstBit S.B)), hmem_yB, by simp [hcB]⟩
      have h0V : H.any (fun vc => vc.1 == edgeV e0 && buildComp (edgeV e0) S.gs (edgeU e0) == vc.2) = true := by
        rw [List.any_eq_true]
        rcases he0 with ⟨hU, hV⟩ | ⟨hU, hV⟩
        · rw [hU, hV]; exact ⟨(yB, buildComp yB S.gs (firstBit S.B)), hmem_yB, by simp [hcB]⟩
        · rw [hU, hV]; exact ⟨(zA, buildComp zA S.gs (firstBit S.A)), hmem_zA, by simp [hcA]⟩
      have hHAB_le : H_AB.length ≤ 2 := by dsimp only [H_AB]; rw [hzA, hyB]; simp
      have hHlen : H.length ≤ 7 + S.zeroGates.length := by simp only [H, List.length_append]; omega
      have hbound := master_cover_bound_overlap S.gs H hcov e0 h0U h0V
      omega

/-! ### Part 7: Main Theorem Wrapper -/

theorem solve_53166 :
  ∀ (gates : Fin 5 → Bool × BitVec 5 × BitVec 5)
    (pairs : Fin 5 → BitVec 5 × BitVec 5),
  let read := fun (bank : List (BitVec 21)) =>
    bank.foldr (fun wire (rest : BitVec 5 → BitVec 21) index =>
      if index = 0 then wire else rest (index - 1)) (fun _ => 0)
  let product := fun (bank : List (BitVec 21)) (pair : BitVec 5 × BitVec 5) =>
    read bank pair.1 &&& read bank pair.2
  let program := List.ofFn gates
  let bank := program.foldl (fun bank gate => bank ++
    [if gate.1 then product bank gate.2 else read bank gate.2.1 ||| read bank gate.2.2])
    (([63491,1386508,235568,0,151748,287504,0,0,558408,1246721,1835170,0,1246721,1835170,0,0] : List Nat).map (BitVec.ofNat 21))
  let affordable := program.foldr (fun gate (rest : Bool → Bool) used =>
    (!(used && gate.1)) && rest (used || gate.1)) (fun _ => true) false
  let terminals := List.ofFn pairs
  (affordable && terminals.all (fun pair => (product bank pair &&& 2095104) == 0) &&
    ((terminals.foldl (fun acc pair => acc ||| product bank pair) 0 &&& 2047) == 2047)) = false := by
  intro gates pairs read product program bank affordable terminals
  by_contra hne
  have htrue : (affordable && terminals.all (fun pair => (product bank pair &&& 2095104) == 0) &&
      ((terminals.foldl (fun acc pair => acc ||| product bank pair) 0 &&& 2047) == 2047)) = true := by
    cases h : (affordable && terminals.all (fun pair => (product bank pair &&& 2095104) == 0) &&
      ((terminals.foldl (fun acc pair => acc ||| product bank pair) 0 &&& 2047) == 2047))
    · exact absurd h hne
    · rfl
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at htrue
  rcases htrue with ⟨⟨haff_bool, hall_clean⟩, hcov_all⟩
  have haff : program.countP (fun g => g.1) ≤ 1 := (affordable_count_and program).mp haff_bool
  have hprog_len : program.length = 5 := by simp [program]
  have hterm_len : terminals.length = 5 := by simp [terminals]
  obtain ⟨gVal, A, B, reps, gs, zeroGates,
    hbank_eq, hnoAnd, hyesAnd, hlen, hzne, hzeroAnc, hcomp, _, hchain⟩ :=
    track_program program haff
  have hbank_same : bank = reps.map (evalWire gVal) := hbank_eq
  have hread_eq : ∀ idx : BitVec 5,
      read bank idx = evalWire gVal (reps.getD idx.toNat (false, 0#8)) := fun idx => by
    change readBank bank idx = _
    rw [readBank_eq_getD, hbank_same]
    by_cases hlt : idx.toNat < reps.length
    · rw [List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hlt),
        List.getD_eq_getElem _ _ hlt, List.getElem_map]
    · rw [List.getD_eq_default _ _ (by rw [List.length_map]; omega),
        List.getD_eq_default _ _ (by omega)]
      simp [evalWire, orMask_zero]
  have hprod_eq : ∀ pair : BitVec 5 × BitVec 5,
      product bank pair =
        evalWire gVal (reps.getD pair.1.toNat (false, 0#8)) &&&
        evalWire gVal (reps.getD pair.2.toNat (false, 0#8)) := fun pair => by
    dsimp only [product]; rw [hread_eq pair.1, hread_eq pair.2]
  have hedge_cov : ∀ e : Fin 11, ∃ pair ∈ terminals,
      (evalWire gVal (reps.getD pair.1.toNat (false, 0#8)) &&&
       evalWire gVal (reps.getD pair.2.toNat (false, 0#8))).getLsbD e.val = true := by
    intro e
    have hbit : (terminals.foldl (fun acc pair => acc ||| product bank pair) 0 &&& 2047).getLsbD e.val = true := by
      rw [hcov_all]
      have h2047 : ∀ i : Fin 11, (2047 : BitVec 21).getLsbD i.val = true := by decide
      exact h2047 e
    rw [BitVec.getLsbD_and, Bool.and_eq_true] at hbit
    have hf := hbit.1
    have hmap : terminals.foldl (fun acc pair => acc ||| product bank pair) 0 =
        (terminals.map (product bank)).foldl (fun a b => a ||| b) 0#21 := by
      have hgen : ∀ (l : List (BitVec 5 × BitVec 5)) (acc : BitVec 21),
          l.foldl (fun a pair => a ||| product bank pair) acc =
          (l.map (product bank)).foldl (fun a b => a ||| b) acc := by
        intro l; induction l with
        | nil => intro acc; simp
        | cons x xs ih => intro acc; simp [ih]
      exact hgen terminals 0#21
    rw [hmap, foldl_or_bit] at hf
    simp only [BitVec.getLsbD_zero, Bool.false_or, List.any_eq_true, List.mem_map] at hf
    rcases hf with ⟨w, ⟨pair, hp, rfl⟩, hwb⟩
    rw [hprod_eq pair] at hwb
    exact ⟨pair, hp, hwb⟩
  have hpair_clean : ∀ pair ∈ terminals,
      ((evalWire gVal (reps.getD pair.1.toNat (false, 0#8)) &&&
        evalWire gVal (reps.getD pair.2.toNat (false, 0#8))) &&& BAD) = 0#21 := by
    intro pair hp
    have hc := hall_clean pair hp
    rw [hprod_eq pair] at hc; exact hc
  by_cases hand : decide (0 < program.countP (fun g => g.1)) = false
  · -- 0 AND gates! Pure OR cover!
    obtain ⟨_, hallf⟩ := hnoAnd hand
    let H : List (Fin 8 × Fin 8) :=
      terminals.flatMap fun pair =>
        (purePairClass gs (reps.getD pair.1.toNat (false, 0#8)).2 (reps.getD pair.2.toNat (false, 0#8)).2).toList
    have hHlen : H.length ≤ 5 := by
      have := flatMap_option_length_le terminals (fun pair =>
        purePairClass gs (reps.getD pair.1.toNat (false, 0#8)).2 (reps.getD pair.2.toNat (false, 0#8)).2)
      dsimp only [H]; omega
    have hrep_f : ∀ idx : BitVec 5, (reps.getD idx.toNat (false, 0#8)).1 = false := fun idx => by
      by_cases hlt : idx.toNat < reps.length
      · rw [List.getD_eq_getElem _ _ hlt]; exact hallf _ (List.getElem_mem hlt)
      · rw [List.getD_eq_default _ _ (by omega)]
    have hrep_c : ∀ idx : BitVec 5, ∀ v : Fin 8, sub8 (reps.getD idx.toNat (false, 0#8)).2 (nbrs v) = true →
        ∀ x y : Fin 8, hasBit (reps.getD idx.toNat (false, 0#8)).2 x = true →
          hasBit (reps.getD idx.toNat (false, 0#8)).2 y = true → buildComp v gs x = buildComp v gs y := by
      intro idx v hsub x y hx hy
      by_cases hlt : idx.toNat < reps.length
      · rw [List.getD_eq_getElem _ _ hlt] at hsub hx hy
        exact hcomp _ (List.getElem_mem hlt) (nbrs v) hsub x y hx hy
      · rw [List.getD_eq_default _ _ (by omega)] at hx; simp [hasBit_zero] at hx
    have hcov : ∀ e : Fin 11, H.any (fun vc => coversClass (fun v => buildComp v gs) vc e) = true := by
      intro e
      obtain ⟨pair, hp, he⟩ := hedge_cov e
      have hf1 := hrep_f pair.1; have hf2 := hrep_f pair.2
      simp only [evalWire, hf1, hf2, Bool.false_eq_true, ↓reduceIte, BitVec.zero_or] at he
      have hc := hpair_clean pair hp
      simp only [evalWire, hf1, hf2, Bool.false_eq_true, ↓reduceIte, BitVec.zero_or] at hc
      obtain ⟨vc, hvc, hce⟩ := purePairClass_covers gs _ _ hc (hrep_c pair.1) (hrep_c pair.2) e he
      rw [List.any_eq_true]
      exact ⟨vc, List.mem_flatMap.mpr ⟨pair, hp, by rw [hvc]; simp⟩, hce⟩
    have hbound := master_cover_bound gs H hcov
    have hsum := sum_isMergeFor_le gs
    simp only [hand, Bool.false_eq_true, ↓reduceIte, hprog_len] at hlen
    omega
  · have handT : decide (0 < program.countP (fun g => g.1)) = true := by
      cases h : decide (0 < program.countP (fun g => g.1)); exact absurd h hand; rfl
    obtain ⟨hgVal, hA_gs, hB_gs, hA_comp, hB_comp⟩ := hyesAnd handT
    have hlen4 : gs.length + zeroGates.length ≤ 4 := by
      simp only [handT, ↓reduceIte, hprog_len] at hlen; omega
    let S : Setup := {
      gVal, A, B, reps, gs, zeroGates, terminals, hterm_len, hlen4,
      hgVal, hA_gs, hB_gs, hA_comp, hB_comp, hzne, hzeroAnc, hcomp, hchain,
      hedge_cov, hpair_clean
    }
    by_cases hgClean : (S.gVal &&& BAD) = 0#21
    · exact solve_g_clean S hgClean
    by_cases hsubAB : sub8 S.A S.B = true
    · exact solve_g_eq_orMask S hgClean S.A (by rw [S.hgVal, orMask_and_of_sub S.A S.B hsubAB])
        (fun v h => S.hA_comp (nbrs v) h)
    by_cases hsubBA : sub8 S.B S.A = true
    · exact solve_g_eq_orMask S hgClean S.B
        (by rw [S.hgVal, BitVec.and_comm, orMask_and_of_sub S.B S.A hsubBA])
        (fun v h => S.hB_comp (nbrs v) h)
    have hnotAB : sub8 S.A S.B = false := by cases h : sub8 S.A S.B; rfl; exact absurd h hsubAB
    have hnotBA : sub8 S.B S.A = false := by cases h : sub8 S.B S.A; rfl; exact absurd h hsubBA
    have hAne : S.A ≠ 0#8 := fun h => hgClean (by rw [S.hgVal, h, orMask_zero]; simp)
    have hBne : S.B ≠ 0#8 := fun h => hgClean (by rw [S.hgVal, h, orMask_zero]; simp)
    by_cases hA1 : pop8 S.A = 1
    · exact solve_pop1 S hgClean S.A S.B S.hgVal hA1 hnotAB S.hB_gs S.hB_comp
    by_cases hB1 : pop8 S.B = 1
    · exact solve_pop1 S hgClean S.B S.A (by rw [S.hgVal, BitVec.and_comm]) hB1 hnotBA S.hA_gs S.hA_comp
    have hA2 : 2 ≤ pop8 S.A := by
      have hne0 : pop8 S.A ≠ 0 := fun hz => hAne ((pop8_eq_zero_iff S.A).mp hz); omega
    have hB2 : 2 ≤ pop8 S.B := by
      have hne0 : pop8 S.B ≠ 0 := fun hz => hBne ((pop8_eq_zero_iff S.B).mp hz); omega
    have hABne : S.A ≠ S.B := fun h => by rw [h, sub8_refl] at hnotAB; contradiction
    by_cases hAB2 : 2 ≤ pop8 (S.A &&& S.B)
    · exact solve_AB_ge2 S hgClean hA2 hB2 hABne hAB2
    · exact solve_AB_le1 S hgClean hA2 hB2 (by omega)

end PEqualNP.Outside.L_meta_53166

theorem PEqualNP.Outside.L_meta_53166 :
  ∀ (gates : Fin 5 → Bool × BitVec 5 × BitVec 5)
    (pairs : Fin 5 → BitVec 5 × BitVec 5),
  let read := fun (bank : List (BitVec 21)) =>
    bank.foldr (fun wire (rest : BitVec 5 → BitVec 21) index =>
      if index = 0 then wire else rest (index - 1)) (fun _ => 0)
  let product := fun (bank : List (BitVec 21)) (pair : BitVec 5 × BitVec 5) =>
    read bank pair.1 &&& read bank pair.2
  let program := List.ofFn gates
  let bank := program.foldl (fun bank gate => bank ++
    [if gate.1 then product bank gate.2 else read bank gate.2.1 ||| read bank gate.2.2])
    (([63491,1386508,235568,0,151748,287504,0,0,558408,1246721,1835170,0,1246721,1835170,0,0] : List Nat).map (BitVec.ofNat 21))
  let affordable := program.foldr (fun gate (rest : Bool → Bool) used =>
    (!(used && gate.1)) && rest (used || gate.1)) (fun _ => true) false
  let terminals := List.ofFn pairs
  (affordable && terminals.all (fun pair => (product bank pair &&& 2095104) == 0) &&
    ((terminals.foldl (fun acc pair => acc ||| product bank pair) 0 &&& 2047) == 2047)) = false :=
  PEqualNP.Outside.L_meta_53166.solve_53166
