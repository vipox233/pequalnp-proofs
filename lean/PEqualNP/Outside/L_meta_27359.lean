import Mathlib.Data.Finset.Max
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Push
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_27359_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def perm3 (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) ||
  (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6)

def emb (y : Fin 7 → Bool) : Fin 9 → Bool
  | ⟨0, _⟩ => false
  | ⟨1, _⟩ => y 0
  | ⟨2, _⟩ => y 1
  | ⟨3, _⟩ => y 2
  | ⟨4, _⟩ => y 3
  | ⟨5, _⟩ => y 4
  | ⟨6, _⟩ => y 5
  | ⟨7, _⟩ => y 6
  | ⟨8, _⟩ => false

def embIdx : Fin 7 → ℕ
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 2
  | ⟨2, _⟩ => 3
  | ⟨3, _⟩ => 4
  | ⟨4, _⟩ => 5
  | ⟨5, _⟩ => 6
  | ⟨6, _⟩ => 7

def f7 (y : Fin 7 → Bool) : Bool :=
  (y 0 && y 4 && y 5) || (y 1 && y 2 && y 6) || (y 1 && y 3 && y 5)

lemma perm3_emb (y : Fin 7 → Bool) : perm3 (emb y) = f7 y := by
  simp only [perm3, emb, f7]
  cases y 0 <;> cases y 1 <;> cases y 2 <;> cases y 3 <;> cases y 4 <;> cases y 5 <;> cases y 6 <;> rfl

lemma emb_embIdx (y : Fin 7 → Bool) (i : Fin 7) :
    emb y ⟨embIdx i, by fin_cases i <;> decide⟩ = y i := by
  fin_cases i <;> rfl

lemma embIdx_lt9 (i : Fin 7) : embIdx i < 9 := by
  fin_cases i <;> decide

lemma embIdx_inj : Function.Injective embIdx := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp [embIdx] at h ⊢

def inputs7 : Finset ℕ := Finset.univ.image embIdx

lemma inputs7_card : inputs7.card = 7 := by
  rw [inputs7, Finset.card_image_of_injective _ embIdx_inj, Finset.card_univ, Fintype.card_fin]

lemma mem_inputs7_of_lt9 (w : ℕ) (hw : w < 9) (h0 : w ≠ 0) (h8 : w ≠ 8) : w ∈ inputs7 := by
  have : w = 1 ∨ w = 2 ∨ w = 3 ∨ w = 4 ∨ w = 5 ∨ w = 6 ∨ w = 7 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨1, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨2, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨3, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨4, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨5, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨6, Finset.mem_univ _, rfl⟩

def f7b (b0 b1 b2 b3 b4 b5 b6 : Bool) : Bool :=
  (b0 && b4 && b5) || (b1 && b2 && b6) || (b1 && b3 && b5)

abbrev B7 := Bool × Bool × Bool × Bool × Bool × Bool × Bool

def vec7B (t : B7) : Fin 7 → Bool
  | ⟨0, _⟩ => t.1
  | ⟨1, _⟩ => t.2.1
  | ⟨2, _⟩ => t.2.2.1
  | ⟨3, _⟩ => t.2.2.2.1
  | ⟨4, _⟩ => t.2.2.2.2.1
  | ⟨5, _⟩ => t.2.2.2.2.2.1
  | ⟨6, _⟩ => t.2.2.2.2.2.2

def f7t (t : B7) : Bool :=
  f7b t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2.1 t.2.2.2.2.2.2

def mixB7 (p y z : B7) : B7 :=
  (if p.1 then y.1 else z.1,
   if p.2.1 then y.2.1 else z.2.1,
   if p.2.2.1 then y.2.2.1 else z.2.2.1,
   if p.2.2.2.1 then y.2.2.2.1 else z.2.2.2.1,
   if p.2.2.2.2.1 then y.2.2.2.2.1 else z.2.2.2.2.1,
   if p.2.2.2.2.2.1 then y.2.2.2.2.2.1 else z.2.2.2.2.2.1,
   if p.2.2.2.2.2.2 then y.2.2.2.2.2.2 else z.2.2.2.2.2.2)

lemma vec7B_mix (p y z : B7) :
    (fun i => if vec7B p i then vec7B y i else vec7B z i) = vec7B (mixB7 p y z) := by
  funext i
  fin_cases i <;> rfl

def andW : List B7 :=
  [(false, true, false, true, false, true, false),
   (true, false, false, false, true, true, false),
   (false, true, true, false, false, false, true)]

def orW : List B7 :=
  [(true, true, true, true, true, false, false),
   (true, true, true, false, false, true, false),
   (false, true, true, false, true, true, false),
   (true, true, false, true, true, false, true),
   (true, false, true, true, true, false, true),
   (true, true, false, false, false, true, true),
   (true, false, true, true, false, true, true),
   (false, true, false, false, true, true, true),
   (false, false, true, true, true, true, true)]

def checkAndP (p0 p1 p2 p3 p4 p5 p6 : Bool) : Bool :=
  let p : B7 := (p0, p1, p2, p3, p4, p5, p6)
  andW.any fun y => andW.any fun z =>
    f7t y && f7t z && !(f7t (mixB7 p y z))

def checkOrP (p0 p1 p2 p3 p4 p5 p6 : Bool) : Bool :=
  let p : B7 := (p0, p1, p2, p3, p4, p5, p6)
  orW.any fun y => orW.any fun z =>
    !(f7t y) && !(f7t z) && f7t (mixB7 p y z)

lemma all_and_p (p0 p1 p2 p3 p4 p5 p6 : Bool)
    (ht : (p0 || p1 || p2 || p3 || p4 || p5 || p6) = true)
    (hf : (p0 && p1 && p2 && p3 && p4 && p5 && p6) = false) :
    checkAndP p0 p1 p2 p3 p4 p5 p6 = true := by
  cases p0 <;> cases p1 <;> cases p2 <;> cases p3 <;> cases p4 <;> cases p5 <;> cases p6 <;>
    first | rfl | exact absurd ht (by decide) | exact absurd hf (by decide)

lemma all_or_p (p0 p1 p2 p3 p4 p5 p6 : Bool)
    (ht : (p0 || p1 || p2 || p3 || p4 || p5 || p6) = true)
    (hf : (p0 && p1 && p2 && p3 && p4 && p5 && p6) = false) :
    checkOrP p0 p1 p2 p3 p4 p5 p6 = true := by
  cases p0 <;> cases p1 <;> cases p2 <;> cases p3 <;> cases p4 <;> cases p5 <;> cases p6 <;>
    first | rfl | exact absurd ht (by decide) | exact absurd hf (by decide)

lemma vec7B_eq (p : Fin 7 → Bool) : vec7B (p 0, p 1, p 2, p 3, p 4, p 5, p 6) = p := by
  funext i
  fin_cases i <;> rfl

lemma exists_and_break (p : Fin 7 → Bool) (ht : ∃ i, p i = true) (hf : ∃ j, p j = false) :
    ∃ y z : Fin 7 → Bool, f7 y = true ∧ f7 z = true ∧
      f7 (fun i => if p i then y i else z i) = false := by
  have ht' : (p 0 || p 1 || p 2 || p 3 || p 4 || p 5 || p 6) = true := by
    rcases ht with ⟨i, hi⟩
    fin_cases i <;> dsimp at hi <;> simp [hi]
  have hf' : (p 0 && p 1 && p 2 && p 3 && p 4 && p 5 && p 6) = false := by
    rcases hf with ⟨j, hj⟩
    fin_cases j <;> dsimp at hj <;> simp [hj]
  have hc := all_and_p (p 0) (p 1) (p 2) (p 3) (p 4) (p 5) (p 6) ht' hf'
  simp only [checkAndP, List.any_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at hc
  rcases hc with ⟨y, _, z, _, ⟨hy, hz⟩, hmix⟩
  refine ⟨vec7B y, vec7B z, hy, hz, ?_⟩
  have hp : p = vec7B (p 0, p 1, p 2, p 3, p 4, p 5, p 6) := (vec7B_eq p).symm
  rw [hp, vec7B_mix]
  exact hmix

lemma exists_or_break (p : Fin 7 → Bool) (ht : ∃ i, p i = true) (hf : ∃ j, p j = false) :
    ∃ y z : Fin 7 → Bool, f7 y = false ∧ f7 z = false ∧
      f7 (fun i => if p i then y i else z i) = true := by
  have ht' : (p 0 || p 1 || p 2 || p 3 || p 4 || p 5 || p 6) = true := by
    rcases ht with ⟨i, hi⟩
    fin_cases i <;> dsimp at hi <;> simp [hi]
  have hf' : (p 0 && p 1 && p 2 && p 3 && p 4 && p 5 && p 6) = false := by
    rcases hf with ⟨j, hj⟩
    fin_cases j <;> dsimp at hj <;> simp [hj]
  have hc := all_or_p (p 0) (p 1) (p 2) (p 3) (p 4) (p 5) (p 6) ht' hf'
  simp only [checkOrP, List.any_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at hc
  rcases hc with ⟨y, _, z, _, ⟨hy, hz⟩, hmix⟩
  refine ⟨vec7B y, vec7B z, hy, hz, ?_⟩
  have hp : p = vec7B (p 0, p 1, p 2, p 3, p 4, p 5, p 6) := (vec7B_eq p).symm
  rw [hp, vec7B_mix]
  exact hmix

lemma card_filter_add_not {α : Type*} [DecidableEq α] (s : Finset α) (p : α → Prop)
    [DecidablePred p] :
    (s.filter p).card + (s.filter (fun x => ¬ p x)).card = s.card := by
  rw [← Finset.card_union_of_disjoint (Finset.disjoint_filter.mpr fun _ _ h1 h2 => h2 h1)]
  congr 1
  ext x
  simp only [Finset.mem_union, Finset.mem_filter]
  by_cases h : p x <;> simp [h]

lemma f7_essential (i : Fin 7) :
    ∃ y z : Fin 7 → Bool, (∀ j : Fin 7, j ≠ i → y j = z j) ∧ f7 y ≠ f7 z := by
  fin_cases i
  · exact ⟨vec7B (false, false, false, false, true, true, false),
      vec7B (true, false, false, false, true, true, false),
      by intro j hj; fin_cases j <;> simp_all [vec7B], by decide⟩
  · exact ⟨vec7B (false, false, false, true, false, true, false),
      vec7B (false, true, false, true, false, true, false),
      by intro j hj; fin_cases j <;> simp_all [vec7B], by decide⟩
  · exact ⟨vec7B (false, true, false, false, false, false, true),
      vec7B (false, true, true, false, false, false, true),
      by intro j hj; fin_cases j <;> simp_all [vec7B], by decide⟩
  · exact ⟨vec7B (false, true, false, false, false, true, false),
      vec7B (false, true, false, true, false, true, false),
      by intro j hj; fin_cases j <;> simp_all [vec7B], by decide⟩
  · exact ⟨vec7B (true, false, false, false, false, true, false),
      vec7B (true, false, false, false, true, true, false),
      by intro j hj; fin_cases j <;> simp_all [vec7B], by decide⟩
  · exact ⟨vec7B (false, true, false, true, false, false, false),
      vec7B (false, true, false, true, false, true, false),
      by intro j hj; fin_cases j <;> simp_all [vec7B], by decide⟩
  · exact ⟨vec7B (false, true, true, false, false, false, false),
      vec7B (false, true, true, false, false, false, true),
      by intro j hj; fin_cases j <;> simp_all [vec7B], by decide⟩

structure SmallDAG where
  S : Finset ℕ
  hdisj : Disjoint inputs7 S
  hScard : S.card ≤ 6
  children : ℕ → List ℕ
  op : ℕ → GateOp
  val : ℕ → (Fin 7 → Bool) → Bool
  hchild_lt : ∀ u ∈ S, ∀ c ∈ children u, c < u
  hchild_mem : ∀ u ∈ S, ∀ c ∈ children u, c ∈ inputs7 ∪ S
  hchild_nf : ∀ u ∈ S,
    (op u = GateOp.not ∧ (children u).length = 1) ∨
    ((op u = GateOp.and ∨ op u = GateOp.or) ∧ (children u).length = 2)
  heval_in : ∀ i : Fin 7, ∀ y, val (embIdx i) y = y i
  heval_gate : ∀ u ∈ S, ∀ y, val u y = (op u).eval ((children u).map fun c => val c y)
  hnc : ∀ u ∈ inputs7 ∪ S, ∃ y z, val u y ≠ val u z

def SmallDAG.reach (D : SmallDAG) (u : ℕ) : Finset ℕ :=
  if hu : u ∈ D.S then
    insert u ((D.children u).attach.foldr (fun ⟨c, hc⟩ acc =>
      have : c < u := D.hchild_lt u hu c hc
      D.reach c ∪ acc) ∅)
  else {u}
termination_by u

lemma SmallDAG.self_mem_reach (D : SmallDAG) (u : ℕ) : u ∈ D.reach u := by
  rw [SmallDAG.reach]
  split_ifs <;> simp

lemma SmallDAG.reach_le (D : SmallDAG) (u : ℕ) : ∀ w ∈ D.reach u, w ≤ u := by
  induction u using Nat.strong_induction_on with
  | ind u ih =>
    intro w hw
    rw [SmallDAG.reach] at hw
    split_ifs at hw with hu
    · rcases Finset.mem_insert.mp hw with rfl | hw
      · exact le_refl _
      · have hfold : ∀ (l : List {c // c ∈ D.children u}),
            w ∈ l.foldr (fun ⟨c, hc⟩ acc => D.reach c ∪ acc) ∅ →
            ∃ c, ∃ hc : c ∈ D.children u, w ∈ D.reach c := by
          intro l hl
          induction l with
          | nil => simp at hl
          | cons hd tl ihtl =>
            simp only [List.foldr_cons, Finset.mem_union] at hl
            rcases hl with hhd | htl
            · exact ⟨hd.1, hd.2, hhd⟩
            · exact ihtl htl
        rcases hfold _ hw with ⟨c, hc, hwc⟩
        have hlt := D.hchild_lt u hu c hc
        exact le_trans (ih c hlt w hwc) (le_of_lt hlt)
    · simp at hw
      omega

lemma SmallDAG.child_subset_reach (D : SmallDAG) (u : ℕ) (hu : u ∈ D.S) (c : ℕ)
    (hc : c ∈ D.children u) : D.reach c ⊆ D.reach u := by
  intro w hw
  rw [SmallDAG.reach]
  simp only [hu, ↓reduceDIte, Finset.mem_insert]
  right
  have hfold : ∀ (l : List {x // x ∈ D.children u}),
      ⟨c, hc⟩ ∈ l → w ∈ l.foldr (fun ⟨x, _⟩ acc => D.reach x ∪ acc) ∅ := by
    intro l hl
    induction l with
    | nil => simp at hl
    | cons hd tl ihtl =>
      simp only [List.foldr_cons, Finset.mem_union]
      rcases List.mem_cons.mp hl with rfl | htl
      · left; exact hw
      · right; exact ihtl htl
  exact hfold (D.children u).attach (List.mem_attach _ ⟨c, hc⟩)

lemma SmallDAG.reach_subset_V (D : SmallDAG) (u : ℕ) (huV : u ∈ inputs7 ∪ D.S) :
    D.reach u ⊆ inputs7 ∪ D.S := by
  induction u using Nat.strong_induction_on with
  | ind u ih =>
    intro w hw
    rw [SmallDAG.reach] at hw
    split_ifs at hw with hu
    · rcases Finset.mem_insert.mp hw with rfl | hw
      · exact huV
      · have hfold : ∀ (l : List {c // c ∈ D.children u}),
            w ∈ l.foldr (fun ⟨c, hc⟩ acc => D.reach c ∪ acc) ∅ →
            ∃ c, ∃ hc : c ∈ D.children u, w ∈ D.reach c := by
          intro l hl
          induction l with
          | nil => simp at hl
          | cons hd tl ihtl =>
            simp only [List.foldr_cons, Finset.mem_union] at hl
            rcases hl with hhd | htl
            · exact ⟨hd.1, hd.2, hhd⟩
            · exact ihtl htl
        rcases hfold _ hw with ⟨c, hc, hwc⟩
        exact ih c (D.hchild_lt u hu c hc) (D.hchild_mem u hu c hc) hwc
    · simp at hw
      subst hw
      exact huV

lemma SmallDAG.reach_parent (D : SmallDAG) (u : ℕ) :
    ∀ w ∈ D.reach u, w ≠ u → ∃ p ∈ D.reach u ∩ D.S, w ∈ D.children p := by
  induction u using Nat.strong_induction_on with
  | ind u ih =>
    intro w hw hne
    rw [SmallDAG.reach] at hw
    split_ifs at hw with hu
    · rcases Finset.mem_insert.mp hw with rfl | hw
      · exact (hne rfl).elim
      · have hfold : ∀ (l : List {c // c ∈ D.children u}),
            w ∈ l.foldr (fun ⟨c, hc⟩ acc => D.reach c ∪ acc) ∅ →
            ∃ c, ∃ hc : c ∈ D.children u, w ∈ D.reach c := by
          intro l hl
          induction l with
          | nil => simp at hl
          | cons hd tl ihtl =>
            simp only [List.foldr_cons, Finset.mem_union] at hl
            rcases hl with hhd | htl
            · exact ⟨hd.1, hd.2, hhd⟩
            · exact ihtl htl
        rcases hfold _ hw with ⟨c, hc, hwc⟩
        by_cases hwc_eq : w = c
        · subst hwc_eq
          exact ⟨u, Finset.mem_inter.mpr ⟨D.self_mem_reach u, hu⟩, hc⟩
        · rcases ih c (D.hchild_lt u hu c hc) w hwc hwc_eq with ⟨p, hp, hwp⟩
          refine ⟨p, Finset.mem_inter.mpr ⟨D.child_subset_reach u hu c hc (Finset.mem_inter.mp hp).1,
            (Finset.mem_inter.mp hp).2⟩, hwp⟩
    · simp at hw
      exact (hne hw).elim

lemma SmallDAG.val_depends_reach (D : SmallDAG) (u : ℕ) (huV : u ∈ inputs7 ∪ D.S)
    (y z : Fin 7 → Bool) (hagree : ∀ i : Fin 7, embIdx i ∈ D.reach u → y i = z i) :
    D.val u y = D.val u z := by
  induction u using Nat.strong_induction_on with
  | ind u ih =>
    by_cases hu : u ∈ D.S
    · rw [D.heval_gate u hu y, D.heval_gate u hu z]
      congr 1
      apply List.map_congr_left
      intro c hc
      exact ih c (D.hchild_lt u hu c hc) (D.hchild_mem u hu c hc)
        (fun i hi => hagree i (D.child_subset_reach u hu c hc hi))
    · have hu_in : u ∈ inputs7 := by
        rcases Finset.mem_union.mp huV with h1 | h2
        · exact h1
        · exact (hu h2).elim
      rcases Finset.mem_image.mp hu_in with ⟨i, _, rfl⟩
      rw [D.heval_in i y, D.heval_in i z]
      exact hagree i (D.self_mem_reach (embIdx i))

lemma no_small_dag (D : SmallDAG) (v : ℕ) (hvV : v ∈ inputs7 ∪ D.S)
    (hout : ∀ y : Fin 7 → Bool, D.val v y = f7 y) : False := by
  classical
  let A := D.reach v
  have hA_sub : A ⊆ inputs7 ∪ D.S := D.reach_subset_V v hvV
  have hin_sub_A : inputs7 ⊆ A := by
    intro w hw
    rcases Finset.mem_image.mp hw with ⟨i, _, rfl⟩
    by_contra hnot
    rcases f7_essential i with ⟨y, z, hagree, hneq⟩
    have heq : D.val v y = D.val v z := by
      apply D.val_depends_reach v hvV y z
      intro j hj
      have hji : j ≠ i := by
        intro heq
        subst heq
        exact hnot hj
      exact hagree j hji
    rw [hout y, hout z] at heq
    exact hneq heq
  let AS := A ∩ D.S
  have hA_eq : A = inputs7 ∪ AS := by
    ext w
    simp only [Finset.mem_union, Finset.mem_inter, AS]
    constructor
    · intro hw
      rcases Finset.mem_union.mp (hA_sub hw) with h1 | h2
      · left; exact h1
      · right; exact ⟨hw, h2⟩
    · rintro (h1 | ⟨h1, _⟩)
      · exact hin_sub_A h1
      · exact h1
  have hdisj_in_AS : Disjoint inputs7 AS :=
    Disjoint.mono_right Finset.inter_subset_right D.hdisj
  have hA_card : A.card = 7 + AS.card := by
    rw [hA_eq, Finset.card_union_of_disjoint hdisj_in_AS, inputs7_card]
  have hv_in_A : v ∈ A := D.self_mem_reach v
  have hA_erase : (A.erase v).card = 6 + AS.card := by
    rw [Finset.card_erase_of_mem hv_in_A, hA_card]
    omega
  have hcov : A.erase v ⊆ AS.biUnion (fun p => (D.children p).toFinset) := by
    intro w hw
    rcases Finset.mem_erase.mp hw with ⟨hne, hwA⟩
    rcases D.reach_parent v w hwA hne with ⟨p, hp, hwp⟩
    exact Finset.mem_biUnion.mpr ⟨p, hp, List.mem_toFinset.mpr hwp⟩
  let ABin := AS.filter (fun p => (D.children p).length = 2)
  have hsum_len : ∑ p ∈ AS, (D.children p).length = ABin.card + AS.card := by
    have hsplit := Finset.sum_filter_add_sum_filter_not AS (fun p => (D.children p).length = 2)
      (fun p => (D.children p).length)
    have h1 : ∑ p ∈ ABin, (D.children p).length = 2 * ABin.card := by
      calc ∑ p ∈ ABin, (D.children p).length = ∑ _p ∈ ABin, 2 := by
            apply Finset.sum_congr rfl
            intro p hp
            exact (Finset.mem_filter.mp hp).2
        _ = 2 * ABin.card := by simp [mul_comm]
    have h2 : ∑ p ∈ AS.filter (fun p => ¬ (D.children p).length = 2), (D.children p).length =
        (AS.filter (fun p => ¬ (D.children p).length = 2)).card := by
      calc ∑ p ∈ AS.filter (fun p => ¬ (D.children p).length = 2), (D.children p).length
          = ∑ _p ∈ AS.filter (fun p => ¬ (D.children p).length = 2), 1 := by
            apply Finset.sum_congr rfl
            intro p hp
            have hpS : p ∈ D.S := (Finset.mem_inter.mp (Finset.mem_filter.mp hp).1).2
            have hne2 : (D.children p).length ≠ 2 := (Finset.mem_filter.mp hp).2
            rcases D.hchild_nf p hpS with ⟨_, hlen1⟩ | ⟨_, hlen2⟩
            · exact hlen1
            · exact (hne2 hlen2).elim
        _ = (AS.filter (fun p => ¬ (D.children p).length = 2)).card := by simp
    have hcard_add := card_filter_add_not (s := AS) (p := fun p => (D.children p).length = 2)
    change ABin.card + (AS.filter (fun p => ¬ (D.children p).length = 2)).card = AS.card at hcard_add
    change ∑ p ∈ ABin, (D.children p).length +
      ∑ p ∈ AS.filter (fun p => ¬ (D.children p).length = 2), (D.children p).length =
      ∑ p ∈ AS, (D.children p).length at hsplit
    omega
  have hABin_le_6 : ABin.card ≤ 6 := by
    have h1 : ABin.card ≤ AS.card := Finset.card_le_card (Finset.filter_subset _ _)
    have h2 : AS.card ≤ D.S.card := Finset.card_le_card Finset.inter_subset_right
    have h3 := D.hScard
    omega
  have hchain1 : 6 + AS.card ≤ (AS.biUnion (fun p => (D.children p).toFinset)).card := by
    rw [← hA_erase]
    exact Finset.card_le_card hcov
  have hchain2 : (AS.biUnion (fun p => (D.children p).toFinset)).card ≤
      ∑ p ∈ AS, ((D.children p).toFinset).card := Finset.card_biUnion_le
  have hchain3 : ∑ p ∈ AS, ((D.children p).toFinset).card ≤
      ∑ p ∈ AS, (D.children p).length :=
    Finset.sum_le_sum (fun p _ => List.toFinset_card_le _)
  have hABin_eq_6 : ABin.card = 6 := by omega
  have hAS_eq_6 : AS.card = 6 := by
    have h1 : ABin.card ≤ AS.card := Finset.card_le_card (Finset.filter_subset _ _)
    have h2 : AS.card ≤ D.S.card := Finset.card_le_card Finset.inter_subset_right
    have h3 := D.hScard
    omega
  have hABin_eq_AS : ABin = AS :=
    Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by omega)
  have hbiUnion_eq_sum : (AS.biUnion (fun p => (D.children p).toFinset)).card =
      ∑ p ∈ AS, ((D.children p).toFinset).card := by omega
  have htoFinset_eq_len : ∑ p ∈ AS, ((D.children p).toFinset).card =
      ∑ p ∈ AS, (D.children p).length := by omega
  have hpw_disj : Set.PairwiseDisjoint (AS : Set ℕ) (fun p => (D.children p).toFinset) := by
    intro p1 hp1 p2 hp2 hne
    change Disjoint (D.children p1).toFinset (D.children p2).toFinset
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    have hlt : (AS.biUnion (fun p => (D.children p).toFinset)).card <
        ∑ p ∈ AS, ((D.children p).toFinset).card := by
      have hp2' : p2 ∈ AS.erase p1 := Finset.mem_erase.mpr ⟨hne.symm, hp2⟩
      have hdecomp : AS.biUnion (fun p => (D.children p).toFinset) =
          (D.children p1).toFinset ∪ (AS.erase p1).biUnion (fun p => (D.children p).toFinset) := by
        ext z
        simp only [Finset.mem_biUnion, Finset.mem_union, Finset.mem_erase]
        constructor
        · rintro ⟨p, hp, hzp⟩
          by_cases hpp1 : p = p1
          · left; subst hpp1; exact hzp
          · right; exact ⟨p, ⟨hpp1, hp⟩, hzp⟩
        · rintro (hz | ⟨p, ⟨_, hp⟩, hzp⟩)
          · exact ⟨p1, hp1, hz⟩
          · exact ⟨p, hp, hzp⟩
      have hx_in_rest : x ∈ (AS.erase p1).biUnion (fun p => (D.children p).toFinset) :=
        Finset.mem_biUnion.mpr ⟨p2, hp2', hx2⟩
      have hunion_lt : ((D.children p1).toFinset ∪ (AS.erase p1).biUnion (fun p => (D.children p).toFinset)).card <
          ((D.children p1).toFinset).card + ((AS.erase p1).biUnion (fun p => (D.children p).toFinset)).card := by
        have hadd := Finset.card_union_add_card_inter (D.children p1).toFinset
          ((AS.erase p1).biUnion (fun p => (D.children p).toFinset))
        have hinter_pos : 0 < ((D.children p1).toFinset ∩
            (AS.erase p1).biUnion (fun p => (D.children p).toFinset)).card :=
          Finset.card_pos.mpr ⟨x, Finset.mem_inter.mpr ⟨hx1, hx_in_rest⟩⟩
        omega
      have hrest_le : ((AS.erase p1).biUnion (fun p => (D.children p).toFinset)).card ≤
          ∑ p ∈ AS.erase p1, ((D.children p).toFinset).card := Finset.card_biUnion_le
      have hsum_split : ∑ p ∈ AS, ((D.children p).toFinset).card =
          ((D.children p1).toFinset).card + ∑ p ∈ AS.erase p1, ((D.children p).toFinset).card :=
        (Finset.add_sum_erase AS (fun p => ((D.children p).toFinset).card) hp1).symm
      rw [hdecomp, hsum_split]
      omega
    omega
  have hv_in_S : v ∈ D.S := by
    by_contra hv_not_S
    have hreach_v : D.reach v = {v} := by
      rw [SmallDAG.reach]
      simp [hv_not_S]
    have hcard1 : A.card = 1 := by simp [A, hreach_v]
    omega
  have hv_in_AS : v ∈ AS := Finset.mem_inter.mpr ⟨hv_in_A, hv_in_S⟩
  have hv_len2 : (D.children v).length = 2 := by
    have : v ∈ ABin := by rw [hABin_eq_AS]; exact hv_in_AS
    exact (Finset.mem_filter.mp this).2
  have hv_toFinset_card : ((D.children v).toFinset).card = 2 := by
    by_contra hne2
    have hlt_v : ((D.children v).toFinset).card < (D.children v).length := by
      have := List.toFinset_card_le (D.children v)
      omega
    have hsum_lt : ∑ p ∈ AS, ((D.children p).toFinset).card < ∑ p ∈ AS, (D.children p).length :=
      Finset.sum_lt_sum (fun p _ => List.toFinset_card_le _) ⟨v, hv_in_AS, hlt_v⟩
    omega
  rcases List.length_eq_two.mp hv_len2 with ⟨c1, c2, hcv⟩
  have hc1_ne_c2 : c1 ≠ c2 := by
    intro heq
    subst heq
    rw [hcv] at hv_toFinset_card
    simp at hv_toFinset_card
  have hc1_mem : c1 ∈ D.children v := by rw [hcv]; simp
  have hc2_mem : c2 ∈ D.children v := by rw [hcv]; simp
  have hreach_disj : Disjoint (D.reach c1) (D.reach c2) := by
    rw [Finset.disjoint_left]
    intro w0 hw0_1 hw0_2
    let common := D.reach c1 ∩ D.reach c2
    have hne : common.Nonempty := ⟨w0, Finset.mem_inter.mpr ⟨hw0_1, hw0_2⟩⟩
    let w := common.max' hne
    have hw_mem : w ∈ common := Finset.max'_mem common hne
    have hw1 : w ∈ D.reach c1 := (Finset.mem_inter.mp hw_mem).1
    have hw2 : w ∈ D.reach c2 := (Finset.mem_inter.mp hw_mem).2
    have hw_max : ∀ u ∈ common, u ≤ w := fun u hu => Finset.le_max' common u hu
    by_cases hwc1 : w = c1
    · rw [hwc1] at hw2
      rcases D.reach_parent c2 c1 hw2 hc1_ne_c2 with ⟨p, hp, hwp⟩
      have hp_in_AS : p ∈ AS :=
        Finset.mem_inter.mpr ⟨D.child_subset_reach v hv_in_S c2 hc2_mem (Finset.mem_inter.mp hp).1,
          (Finset.mem_inter.mp hp).2⟩
      have hp_lt_v : p < v := lt_of_le_of_lt (D.reach_le c2 p (Finset.mem_inter.mp hp).1)
        (D.hchild_lt v hv_in_S c2 hc2_mem)
      have hp_ne_v : p ≠ v := by omega
      have hdisj := hpw_disj hp_in_AS hv_in_AS hp_ne_v
      exact (Finset.disjoint_left.mp hdisj) (List.mem_toFinset.mpr hwp) (List.mem_toFinset.mpr hc1_mem)
    · by_cases hwc2 : w = c2
      · rw [hwc2] at hw1
        rcases D.reach_parent c1 c2 hw1 hc1_ne_c2.symm with ⟨p, hp, hwp⟩
        have hp_in_AS : p ∈ AS :=
          Finset.mem_inter.mpr ⟨D.child_subset_reach v hv_in_S c1 hc1_mem (Finset.mem_inter.mp hp).1,
            (Finset.mem_inter.mp hp).2⟩
        have hp_lt_v : p < v := lt_of_le_of_lt (D.reach_le c1 p (Finset.mem_inter.mp hp).1)
          (D.hchild_lt v hv_in_S c1 hc1_mem)
        have hp_ne_v : p ≠ v := by omega
        have hdisj := hpw_disj hp_in_AS hv_in_AS hp_ne_v
        exact (Finset.disjoint_left.mp hdisj) (List.mem_toFinset.mpr hwp) (List.mem_toFinset.mpr hc2_mem)
      · rcases D.reach_parent c1 w hw1 hwc1 with ⟨p1, hp1, hwp1⟩
        rcases D.reach_parent c2 w hw2 hwc2 with ⟨p2, hp2, hwp2⟩
        have hp1_AS : p1 ∈ AS :=
          Finset.mem_inter.mpr ⟨D.child_subset_reach v hv_in_S c1 hc1_mem (Finset.mem_inter.mp hp1).1,
            (Finset.mem_inter.mp hp1).2⟩
        have hp2_AS : p2 ∈ AS :=
          Finset.mem_inter.mpr ⟨D.child_subset_reach v hv_in_S c2 hc2_mem (Finset.mem_inter.mp hp2).1,
            (Finset.mem_inter.mp hp2).2⟩
        have hp1_gt_w : w < p1 := D.hchild_lt p1 (Finset.mem_inter.mp hp1).2 w hwp1
        have hp1_ne_p2 : p1 ≠ p2 := by
          intro heq
          subst heq
          have hp1_common : p1 ∈ common :=
            Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hp1).1, (Finset.mem_inter.mp hp2).1⟩
          have := hw_max p1 hp1_common
          omega
        have hdisj := hpw_disj hp1_AS hp2_AS hp1_ne_p2
        exact (Finset.disjoint_left.mp hdisj) (List.mem_toFinset.mpr hwp1) (List.mem_toFinset.mpr hwp2)
  let I1 : Finset (Fin 7) := Finset.univ.filter (fun i => embIdx i ∈ D.reach c1)
  let I2 : Finset (Fin 7) := Finset.univ.filter (fun i => embIdx i ∈ D.reach c2)
  have hI1_ne : I1.Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    rcases D.hnc c1 (D.hchild_mem v hv_in_S c1 hc1_mem) with ⟨y, z, hneq⟩
    have heq : D.val c1 y = D.val c1 z := by
      apply D.val_depends_reach c1 (D.hchild_mem v hv_in_S c1 hc1_mem) y z
      intro i hi
      have : i ∈ I1 := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
      rw [hemp] at this
      simp at this
    exact hneq heq
  have hI2_ne : I2.Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    rcases D.hnc c2 (D.hchild_mem v hv_in_S c2 hc2_mem) with ⟨y, z, hneq⟩
    have heq : D.val c2 y = D.val c2 z := by
      apply D.val_depends_reach c2 (D.hchild_mem v hv_in_S c2 hc2_mem) y z
      intro i hi
      have : i ∈ I2 := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
      rw [hemp] at this
      simp at this
    exact hneq heq
  have hI_disj : Disjoint I1 I2 := by
    rw [Finset.disjoint_left]
    intro i hi1 hi2
    exact (Finset.disjoint_left.mp hreach_disj)
      (Finset.mem_filter.mp hi1).2 (Finset.mem_filter.mp hi2).2
  let p : Fin 7 → Bool := fun i => decide (i ∈ I1)
  have hp_t : ∃ i, p i = true := by
    rcases hI1_ne with ⟨i0, hi0⟩
    exact ⟨i0, by simp [p, hi0]⟩
  have hp_f : ∃ j, p j = false := by
    rcases hI2_ne with ⟨i2, hi2⟩
    have hi2_not : i2 ∉ I1 := Finset.disjoint_right.mp hI_disj hi2
    exact ⟨i2, by simp [p, hi2_not]⟩
  have hmix_c1 : ∀ y z : Fin 7 → Bool,
      D.val c1 (fun i => if p i then y i else z i) = D.val c1 y := by
    intro y z
    apply D.val_depends_reach c1 (D.hchild_mem v hv_in_S c1 hc1_mem)
    intro i hi
    have hi1 : i ∈ I1 := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
    simp [p, hi1]
  have hmix_c2 : ∀ y z : Fin 7 → Bool,
      D.val c2 (fun i => if p i then y i else z i) = D.val c2 z := by
    intro y z
    apply D.val_depends_reach c2 (D.hchild_mem v hv_in_S c2 hc2_mem)
    intro i hi
    have hi2 : i ∈ I2 := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
    have hi1_not : i ∉ I1 := Finset.disjoint_right.mp hI_disj hi2
    simp [p, hi1_not]
  rcases D.hchild_nf v hv_in_S with ⟨_, hlen1⟩ | ⟨hop, _⟩
  · omega
  · rcases hop with hop_and | hop_or
    · rcases exists_and_break p hp_t hp_f with ⟨y, z, hy, hz, hmix⟩
      have hfy : (D.val c1 y && D.val c2 y) = true := by
        have := D.heval_gate v hv_in_S y
        rw [hout y, hop_and, hcv] at this
        simpa [GateOp.eval] using this.symm.trans hy
      have hfz : (D.val c1 z && D.val c2 z) = true := by
        have := D.heval_gate v hv_in_S z
        rw [hout z, hop_and, hcv] at this
        simpa [GateOp.eval] using this.symm.trans hz
      have hfm : (D.val c1 (fun i => if p i then y i else z i) &&
          D.val c2 (fun i => if p i then y i else z i)) = false := by
        have := D.heval_gate v hv_in_S (fun i => if p i then y i else z i)
        rw [hout _, hop_and, hcv] at this
        simpa [GateOp.eval] using this.symm.trans hmix
      rw [hmix_c1, hmix_c2] at hfm
      simp only [Bool.and_eq_true] at hfy hfz
      rw [hfy.1, hfz.2] at hfm
      simp at hfm
    · rcases exists_or_break p hp_t hp_f with ⟨y, z, hy, hz, hmix⟩
      have hfy : (D.val c1 y || D.val c2 y) = false := by
        have := D.heval_gate v hv_in_S y
        rw [hout y, hop_or, hcv] at this
        simpa [GateOp.eval] using this.symm.trans hy
      have hfz : (D.val c1 z || D.val c2 z) = false := by
        have := D.heval_gate v hv_in_S z
        rw [hout z, hop_or, hcv] at this
        simpa [GateOp.eval] using this.symm.trans hz
      have hfm : (D.val c1 (fun i => if p i then y i else z i) ||
          D.val c2 (fun i => if p i then y i else z i)) = true := by
        have := D.heval_gate v hv_in_S (fun i => if p i then y i else z i)
        rw [hout _, hop_or, hcv] at this
        simpa [GateOp.eval] using this.symm.trans hmix
      rw [hmix_c1, hmix_c2] at hfm
      simp only [Bool.or_eq_false_iff] at hfy hfz
      rw [hfy.1, hfz.2] at hfm
      simp at hfm

def foldWires (gs : List Gate) (acc : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) acc

lemma foldWires_cons (g : Gate) (gs : List Gate) (acc : List Bool) :
    foldWires (g :: gs) acc =
      foldWires gs (acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) := rfl

lemma foldWires_getD_lt (gs : List Gate) (acc : List Bool) (k : ℕ) (hk : k < acc.length) :
    (foldWires gs acc).getD k false = acc.getD k false := by
  induction gs generalizing acc with
  | nil => simp [foldWires]
  | cons g gs ih =>
    rw [foldWires_cons]
    have hk' : k < (acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]).length := by
      simp; omega
    rw [ih _ hk']
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hk]

lemma foldWires_getD_gate (gs : List Gate) (acc : List Bool) (j : ℕ) (hj : j < gs.length)
    (hpre : ∀ u ∈ gs[j].inputs, u < acc.length + j) :
    (foldWires gs acc).getD (acc.length + j) false =
      gs[j].op.eval (gs[j].inputs.map fun u => (foldWires gs acc).getD u false) := by
  induction gs generalizing acc j with
  | nil => simp at hj
  | cons g gs ih =>
    cases j with
    | zero =>
      rw [foldWires_cons]
      simp only [Nat.add_zero, List.getElem_cons_zero] at hpre ⊢
      let v := g.op.eval (g.inputs.map fun i => acc.getD i false)
      have hlen : acc.length < (acc ++ [v]).length := by simp
      rw [foldWires_getD_lt gs (acc ++ [v]) acc.length hlen]
      have hlhs : (acc ++ [v]).getD acc.length false = v := by
        simp [List.getD_eq_getElem?_getD]
      rw [hlhs]
      dsimp only [v]
      congr 1
      apply List.map_congr_left
      intro u hu
      have hu_lt : u < acc.length := hpre u hu
      have hu_lt' : u < (acc ++ [v]).length := by simp; omega
      rw [foldWires_getD_lt gs (acc ++ [v]) u hu_lt']
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hu_lt]
    | succ j' =>
      rw [foldWires_cons]
      simp only [List.getElem_cons_succ] at hpre ⊢
      let v := g.op.eval (g.inputs.map fun i => acc.getD i false)
      have hj' : j' < gs.length := by simp at hj; omega
      have hlen : (acc ++ [v]).length = acc.length + 1 := by simp
      have hidx : acc.length + (j' + 1) = (acc ++ [v]).length + j' := by omega
      rw [hidx]
      apply ih (acc ++ [v]) j' hj'
      intro u hu
      have := hpre u hu
      omega

def wireVal (C : Circuit) (x : Fin 9 → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma wireVal_input (C : Circuit) (x : Fin 9 → Bool) (i : Fin 9) :
    wireVal C x i.val = x i := by
  unfold wireVal Circuit.wires
  change (foldWires C.gates (List.ofFn x)).getD i.val false = x i
  have hi : i.val < (List.ofFn x).length := by simp
  rw [foldWires_getD_lt C.gates (List.ofFn x) i.val hi]
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp

lemma wireVal_gate (C : Circuit) (x : Fin 9 → Bool) (j : Fin C.gates.length)
    (hpre : ∀ u ∈ (C.gates.get j).inputs, u < 9 + j.val) :
    wireVal C x (9 + j.val) =
      (C.gates.get j).op.eval ((C.gates.get j).inputs.map (wireVal C x)) := by
  have hlen : (List.ofFn x).length = 9 := by simp
  have h := foldWires_getD_gate C.gates (List.ofFn x) j.val j.isLt (by
    intro u hu
    rw [hlen]
    exact hpre u hu)
  rw [hlen] at h
  change (foldWires C.gates (List.ofFn x)).getD (9 + j.val) false =
    (C.gates.get j).op.eval ((C.gates.get j).inputs.map fun u =>
      (foldWires C.gates (List.ofFn x)).getD u false)
  simpa [List.get_eq_getElem] using h

lemma get_zero_of_head? (l : List Gate) (g : Gate) (h : l.head? = some g) (hl : 0 < l.length) :
    l.get ⟨0, hl⟩ = g := by
  cases l with
  | nil => simp at h
  | cons a t => simp at h; simpa using h

lemma get_one_of_tail_head? (l : List Gate) (g : Gate) (h : l.tail.head? = some g) (hl : 1 < l.length) :
    l.get ⟨1, hl⟩ = g := by
  cases l with
  | nil => simp at hl
  | cons a t =>
    cases t with
    | nil => simp at h
    | cons b t' => simp at h; simpa using h

def isConstW (C : Circuit) (w : ℕ) : Prop :=
  ∃ b : Bool, ∀ y : Fin 7 → Bool, wireVal C (emb y) w = b

noncomputable def canonW (C : Circuit) (E : Finset (Fin C.gates.length)) (w : ℕ) : ℕ :=
  open Classical in
  if h : 9 ≤ w ∧ w < 9 + C.gates.length then
    let j : Fin C.gates.length := ⟨w - 9, by omega⟩
    if j ∈ E then
      match (C.gates.get j).inputs with
      | [a, b] =>
        if ha : a < w ∧ b < w then
          if isConstW C a then
            if isConstW C b then w else canonW C E b
          else if isConstW C b then canonW C E a else w
        else w
      | _ => w
    else w
  else w
termination_by w

lemma canonW_le (C : Circuit) (E : Finset (Fin C.gates.length)) (w : ℕ) :
    canonW C E w ≤ w := by
  classical
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    rw [canonW]
    split_ifs with h1
    · dsimp only
      split_ifs with h2
      · split
        · split_ifs with ha hca hcb hcb2
          · exact le_refl _
          · exact le_trans (ih _ ha.2) (le_of_lt ha.2)
          · exact le_trans (ih _ ha.1) (le_of_lt ha.1)
          · exact le_refl _
          · exact le_refl _
        · exact le_refl _
      · exact le_refl _
    · exact le_refl _

lemma main_proof :
    ¬ (∃ C : Circuit,
      FanInTwo C ∧ C.size ≤ 12 ∧
      (∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = perm3 x) ∧
      C.output + 1 = 9 + C.size ∧
      (∀ j : Fin C.gates.length,
        ((C.gates.get j).op = GateOp.not ∧
            ∃ a, a < 9 + j.val ∧ (C.gates.get j).inputs = [a]) ∨
        (((C.gates.get j).op = GateOp.and ∨
            (C.gates.get j).op = GateOp.or) ∧
            ∃ a b, a < b ∧ b < 9 + j.val ∧ (C.gates.get j).inputs = [a, b])) ∧
      (∀ j : Fin C.gates.length,
        (∃ x y : Fin 9 → Bool,
          (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn y)).getD (9 + j.val) false) ∧
        ∀ k, k < 9 + j.val → ∃ x : Fin 9 → Bool,
          (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn x)).getD k false) ∧
      (∀ j : Fin C.gates.length, j.val + 1 < C.gates.length →
        ∃ k : Fin C.gates.length, j.val < k.val ∧ 9 + j.val ∈ (C.gates.get k).inputs) ∧
      C.gates.head? = some ⟨GateOp.and, [0, 4]⟩ ∧
      C.gates.tail.head? = some ⟨GateOp.and, [1, 8]⟩) := by
  classical
  rintro ⟨C, hfan, hsize, heval, hout, hnf, _, hused, hg0, hg1⟩
  have hpre : ∀ (j : Fin C.gates.length) u, u ∈ (C.gates.get j).inputs → u < 9 + j.val := by
    intro j u hu
    rcases hnf j with ⟨_, a, ha, hin⟩ | ⟨_, a, b, hab, hb, hin⟩
    · rw [hin] at hu; simp at hu; omega
    · rw [hin] at hu; simp at hu; rcases hu with rfl | rfl <;> omega
  have hlen_ge_2 : 2 ≤ C.gates.length := by
    cases hgs : C.gates with
    | nil => simp [hgs] at hg0
    | cons a l =>
      cases l with
      | nil => simp [hgs] at hg1
      | cons b l' => simp
  have hget0 : C.gates.get ⟨0, by omega⟩ = ⟨GateOp.and, [0, 4]⟩ :=
    get_zero_of_head? C.gates _ hg0 (by omega)
  have hget1 : C.gates.get ⟨1, by omega⟩ = ⟨GateOp.and, [1, 8]⟩ :=
    get_one_of_tail_head? C.gates _ hg1 (by omega)
  have hlen_ge_3 : 3 ≤ C.gates.length := by
    by_contra hlt
    have hlen2 : C.gates.length = 2 := by omega
    have hout10 : C.output = 10 := by
      simp [Circuit.size] at hout
      omega
    let x0 : Fin 9 → Bool := fun i => decide (i.val = 1 ∨ i.val = 8)
    have h1 := heval x0
    unfold Circuit.eval at h1
    rw [hout10] at h1
    have h10 : wireVal C x0 10 = (x0 1 && x0 8) := by
      have hg := wireVal_gate C x0 ⟨1, by omega⟩ (hpre ⟨1, by omega⟩)
      rw [hget1] at hg
      have hx1 : wireVal C x0 1 = x0 1 := wireVal_input C x0 1
      have hx8 : wireVal C x0 8 = x0 8 := wireVal_input C x0 8
      simpa [GateOp.eval, hx1, hx8] using hg
    have h1' : wireVal C x0 10 = perm3 x0 := h1
    rw [h10] at h1'
    have hcontra : (x0 1 && x0 8) ≠ perm3 x0 := by decide
    exact hcontra h1'
  have hconst_0 : isConstW C 0 := by
    refine ⟨false, fun y => ?_⟩
    simpa [emb] using wireVal_input C (emb y) 0
  have hconst_8 : isConstW C 8 := by
    refine ⟨false, fun y => ?_⟩
    simpa [emb] using wireVal_input C (emb y) 8
  have hconst_9 : isConstW C 9 := by
    refine ⟨false, fun y => ?_⟩
    have hg := wireVal_gate C (emb y) ⟨0, by omega⟩ (hpre ⟨0, by omega⟩)
    rw [hget0] at hg
    have h0 : wireVal C (emb y) 0 = false := by simpa [emb] using wireVal_input C (emb y) 0
    simp [GateOp.eval, h0] at hg
    exact hg
  have hconst_10 : isConstW C 10 := by
    refine ⟨false, fun y => ?_⟩
    have hg := wireVal_gate C (emb y) ⟨1, by omega⟩ (hpre ⟨1, by omega⟩)
    rw [hget1] at hg
    have h8 : wireVal C (emb y) 8 = false := by simpa [emb] using wireVal_input C (emb y) 8
    simp [GateOp.eval, h8] at hg
    exact hg
  have hnot_const_out : ¬ isConstW C C.output := by
    rintro ⟨b, hb⟩
    have hfalse : wireVal C (emb (fun _ => false)) C.output = false := by
      change C.eval (List.ofFn (emb (fun _ => false))) = false
      rw [heval, perm3_emb]
      decide
    have htrue : wireVal C (emb (fun _ => true)) C.output = true := by
      change C.eval (List.ofFn (emb (fun _ => true))) = true
      rw [heval, perm3_emb]
      decide
    have h1 := hb (fun _ => false)
    have h2 := hb (fun _ => true)
    rw [hfalse] at h1
    rw [htrue] at h2
    exact Bool.false_ne_true (h1.trans h2.symm)
  have hconst_gate : ∀ j : Fin C.gates.length,
      (∀ u ∈ (C.gates.get j).inputs, isConstW C u) → isConstW C (9 + j.val) := by
    intro j hj
    rcases hnf j with ⟨hop, a, _, hin⟩ | ⟨hop, a, b, _, _, hin⟩
    · rcases hj a (by rw [hin]; simp) with ⟨ba, hba⟩
      refine ⟨!ba, fun y => ?_⟩
      rw [wireVal_gate C (emb y) j (hpre j), hop, hin]
      simp [GateOp.eval, hba y]
    · rcases hj a (by rw [hin]; simp) with ⟨ba, hba⟩
      rcases hj b (by rw [hin]; simp) with ⟨bb, hbb⟩
      rcases hop with hop | hop
      · refine ⟨ba && bb, fun y => ?_⟩
        rw [wireVal_gate C (emb y) j (hpre j), hop, hin]
        simp [GateOp.eval, hba y, hbb y]
      · refine ⟨ba || bb, fun y => ?_⟩
        rw [wireVal_gate C (emb y) j (hpre j), hop, hin]
        simp [GateOp.eval, hba y, hbb y]
  have hused_9 : ∃ k : Fin C.gates.length, 2 ≤ k.val ∧ 9 ∈ (C.gates.get k).inputs := by
    rcases hused ⟨0, by omega⟩ (by dsimp; omega) with ⟨k, hk, hmem⟩
    dsimp only at hk
    have hmem' : 9 ∈ (C.gates.get k).inputs := by simpa using hmem
    refine ⟨k, ?_, hmem'⟩
    by_contra hlt
    have hk1 : k = ⟨1, by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hk1, hget1] at hmem'
    simp at hmem'
  have hused_10 : ∃ k : Fin C.gates.length, 2 ≤ k.val ∧ 10 ∈ (C.gates.get k).inputs := by
    rcases hused ⟨1, by omega⟩ (by dsimp; omega) with ⟨k, hk, hmem⟩
    dsimp at hk hmem
    exact ⟨k, by omega, hmem⟩
  have hused_0 : ∃ k : Fin C.gates.length, 2 ≤ k.val ∧ 0 ∈ (C.gates.get k).inputs := by
    by_contra hno
    push Not at hno
    let xlo : Fin 9 → Bool := fun i => decide (i.val = 5 ∨ i.val = 7)
    let xhi : Fin 9 → Bool := fun i => decide (i.val = 0 ∨ i.val = 5 ∨ i.val = 7)
    have hagree : ∀ w : ℕ, w < 9 + C.gates.length → w ≠ 0 → wireVal C xlo w = wireVal C xhi w := by
      intro w
      induction w using Nat.strong_induction_on with
      | ind w ih =>
        intro hw hne0
        by_cases hw9 : w < 9
        · have h1 := wireVal_input C xlo ⟨w, hw9⟩
          have h2 := wireVal_input C xhi ⟨w, hw9⟩
          rw [h1, h2]
          simp [xlo, xhi, hne0]
        · by_cases hw_eq9 : w = 9
          · subst hw_eq9
            have h1 := wireVal_gate C xlo ⟨0, by omega⟩ (hpre ⟨0, by omega⟩)
            have h2 := wireVal_gate C xhi ⟨0, by omega⟩ (hpre ⟨0, by omega⟩)
            rw [hget0] at h1 h2
            have ha1 : wireVal C xlo 4 = false := by simpa [xlo] using wireVal_input C xlo 4
            have ha2 : wireVal C xhi 4 = false := by simpa [xhi] using wireVal_input C xhi 4
            simp [GateOp.eval, ha1, ha2] at h1 h2
            exact h1.trans h2.symm
          · by_cases hw_eq10 : w = 10
            · subst hw_eq10
              have h1 := wireVal_gate C xlo ⟨1, by omega⟩ (hpre ⟨1, by omega⟩)
              have h2 := wireVal_gate C xhi ⟨1, by omega⟩ (hpre ⟨1, by omega⟩)
              rw [hget1] at h1 h2
              have ha1 : wireVal C xlo 1 = false := by simpa [xlo] using wireVal_input C xlo 1
              have ha2 : wireVal C xhi 1 = false := by simpa [xhi] using wireVal_input C xhi 1
              simp [GateOp.eval, ha1, ha2] at h1 h2
              exact h1.trans h2.symm
            · let j : Fin C.gates.length := ⟨w - 9, by omega⟩
              have hj_ge2 : 2 ≤ j.val := by simp [j]; omega
              have hw_eq : w = 9 + j.val := by simp [j]; omega
              rw [hw_eq, wireVal_gate C xlo j (hpre j), wireVal_gate C xhi j (hpre j)]
              congr 1
              apply List.map_congr_left
              intro u hu
              have hu_lt : u < w := by
                have := hpre j u hu
                omega
              have hu_ne0 : u ≠ 0 := by
                intro heq
                subst heq
                exact hno j hj_ge2 hu
              exact ih u hu_lt (by omega) hu_ne0
    have hout_eq : C.output = 9 + C.gates.length - 1 := by
      simp [Circuit.size] at hout
      omega
    have heq : wireVal C xlo C.output = wireVal C xhi C.output :=
      hagree C.output (by omega) (by omega)
    have h1 : wireVal C xlo C.output = perm3 xlo := heval xlo
    have h2 : wireVal C xhi C.output = perm3 xhi := heval xhi
    rw [h1, h2] at heq
    have hneq : perm3 xlo ≠ perm3 xhi := by decide
    exact hneq heq
  have hused_8 : ∃ k : Fin C.gates.length, 2 ≤ k.val ∧ 8 ∈ (C.gates.get k).inputs := by
    by_contra hno
    push Not at hno
    let xlo : Fin 9 → Bool := fun i => decide (i.val = 0 ∨ i.val = 4)
    let xhi : Fin 9 → Bool := fun i => decide (i.val = 0 ∨ i.val = 4 ∨ i.val = 8)
    have hagree : ∀ w : ℕ, w < 9 + C.gates.length → w ≠ 8 → wireVal C xlo w = wireVal C xhi w := by
      intro w
      induction w using Nat.strong_induction_on with
      | ind w ih =>
        intro hw hne8
        by_cases hw9 : w < 9
        · have h1 := wireVal_input C xlo ⟨w, hw9⟩
          have h2 := wireVal_input C xhi ⟨w, hw9⟩
          rw [h1, h2]
          simp [xlo, xhi, hne8]
        · by_cases hw_eq9 : w = 9
          · subst hw_eq9
            have h1 := wireVal_gate C xlo ⟨0, by omega⟩ (hpre ⟨0, by omega⟩)
            have h2 := wireVal_gate C xhi ⟨0, by omega⟩ (hpre ⟨0, by omega⟩)
            rw [hget0] at h1 h2
            have ha1 : wireVal C xlo 0 = true := by simpa [xlo] using wireVal_input C xlo 0
            have ha2 : wireVal C xhi 0 = true := by simpa [xhi] using wireVal_input C xhi 0
            have hb1 : wireVal C xlo 4 = true := by simpa [xlo] using wireVal_input C xlo 4
            have hb2 : wireVal C xhi 4 = true := by simpa [xhi] using wireVal_input C xhi 4
            simp [GateOp.eval, ha1, ha2, hb1, hb2] at h1 h2
            exact h1.trans h2.symm
          · by_cases hw_eq10 : w = 10
            · subst hw_eq10
              have h1 := wireVal_gate C xlo ⟨1, by omega⟩ (hpre ⟨1, by omega⟩)
              have h2 := wireVal_gate C xhi ⟨1, by omega⟩ (hpre ⟨1, by omega⟩)
              rw [hget1] at h1 h2
              have ha1 : wireVal C xlo 1 = false := by simpa [xlo] using wireVal_input C xlo 1
              have ha2 : wireVal C xhi 1 = false := by simpa [xhi] using wireVal_input C xhi 1
              simp [GateOp.eval, ha1, ha2] at h1 h2
              exact h1.trans h2.symm
            · let j : Fin C.gates.length := ⟨w - 9, by omega⟩
              have hj_ge2 : 2 ≤ j.val := by simp [j]; omega
              have hw_eq : w = 9 + j.val := by simp [j]; omega
              rw [hw_eq, wireVal_gate C xlo j (hpre j), wireVal_gate C xhi j (hpre j)]
              congr 1
              apply List.map_congr_left
              intro u hu
              have hu_lt : u < w := by
                have := hpre j u hu
                omega
              have hu_ne8 : u ≠ 8 := by
                intro heq
                subst heq
                exact hno j hj_ge2 hu
              exact ih u hu_lt (by omega) hu_ne8
    have hout_eq : C.output = 9 + C.gates.length - 1 := by
      simp [Circuit.size] at hout
      omega
    have heq : wireVal C xlo C.output = wireVal C xhi C.output :=
      hagree C.output (by omega) (by omega)
    have h1 : wireVal C xlo C.output = perm3 xlo := heval xlo
    have h2 : wireVal C xhi C.output = perm3 xhi := heval xhi
    rw [h1, h2] at heq
    have hneq : perm3 xlo ≠ perm3 xhi := by decide
    exact hneq heq
  let E : Finset (Fin C.gates.length) :=
    Finset.univ.filter (fun j => 2 ≤ j.val ∧ ∃ u ∈ (C.gates.get j).inputs, isConstW C u)
  have hE_ge_4 : 4 ≤ E.card := by
    let Ec : Finset (Fin C.gates.length) := E.filter (fun j => isConstW C (9 + j.val))
    let Em : Finset (Fin C.gates.length) := E.filter (fun j => ¬ isConstW C (9 + j.val))
    let W0 : Finset ℕ := {0, 8, 9, 10}
    let Kused : Finset ℕ := W0 ∪ Ec.image (fun j => 9 + j.val)
    let allKIn : Finset ℕ := E.biUnion (fun j => ((C.gates.get j).inputs.toFinset).filter (isConstW C))
    have hdisj_WK : Disjoint W0 (Ec.image (fun j => 9 + j.val)) := by
      rw [Finset.disjoint_left]
      intro w hw0 hwE
      rcases Finset.mem_image.mp hwE with ⟨j, hjEc, rfl⟩
      have hj_ge2 : 2 ≤ j.val := (Finset.mem_filter.mp (Finset.mem_filter.mp hjEc).1).2.1
      simp only [W0, Finset.mem_insert, Finset.mem_singleton] at hw0
      omega
    have hW0_card : W0.card = 4 := by decide
    have hEc_img_card : (Ec.image (fun j => 9 + j.val)).card = Ec.card := by
      apply Finset.card_image_of_injective
      intro a b h
      dsimp at h
      exact Fin.ext (by omega)
    have hKused_card : Kused.card = 4 + Ec.card := by
      rw [Finset.card_union_of_disjoint hdisj_WK, hW0_card, hEc_img_card]
    have hKused_sub : Kused ⊆ allKIn := by
      intro w hw
      rcases Finset.mem_union.mp hw with hw0 | hwE
      · simp only [W0, Finset.mem_insert, Finset.mem_singleton] at hw0
        rcases hw0 with rfl | rfl | rfl | rfl
        · rcases hused_0 with ⟨k, hk, hmem⟩
          exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk, 0, hmem, hconst_0⟩,
            Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hmem, hconst_0⟩⟩
        · rcases hused_8 with ⟨k, hk, hmem⟩
          exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk, 8, hmem, hconst_8⟩,
            Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hmem, hconst_8⟩⟩
        · rcases hused_9 with ⟨k, hk, hmem⟩
          exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk, 9, hmem, hconst_9⟩,
            Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hmem, hconst_9⟩⟩
        · rcases hused_10 with ⟨k, hk, hmem⟩
          exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk, 10, hmem, hconst_10⟩,
            Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hmem, hconst_10⟩⟩
      · rcases Finset.mem_image.mp hwE with ⟨j, hjEc, rfl⟩
        have hjE : j ∈ E := (Finset.mem_filter.mp hjEc).1
        have hj_ge2 : 2 ≤ j.val := (Finset.mem_filter.mp hjE).2.1
        have hjc : isConstW C (9 + j.val) := (Finset.mem_filter.mp hjEc).2
        have hj_lt : j.val + 1 < C.gates.length := by
          by_contra hge
          have hlast : 9 + j.val = C.output := by
            simp [Circuit.size] at hout
            omega
          rw [hlast] at hjc
          exact hnot_const_out hjc
        rcases hused j hj_lt with ⟨r, hjr, hrmem⟩
        exact Finset.mem_biUnion.mpr ⟨r,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega, 9 + j.val, hrmem, hjc⟩,
          Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hrmem, hjc⟩⟩
    have hall_le : allKIn.card ≤ 2 * Ec.card + Em.card := by
      have h1 : allKIn.card ≤ ∑ j ∈ E, (((C.gates.get j).inputs.toFinset).filter (isConstW C)).card :=
        Finset.card_biUnion_le
      have hsplit := Finset.sum_filter_add_sum_filter_not E (fun j => isConstW C (9 + j.val))
        (fun j => (((C.gates.get j).inputs.toFinset).filter (isConstW C)).card)
      have hEc_le : ∑ j ∈ Ec, (((C.gates.get j).inputs.toFinset).filter (isConstW C)).card ≤ 2 * Ec.card := by
        calc ∑ j ∈ Ec, (((C.gates.get j).inputs.toFinset).filter (isConstW C)).card
            ≤ ∑ _j ∈ Ec, 2 := by
              apply Finset.sum_le_sum
              intro j _
              have hle1 := Finset.card_filter_le ((C.gates.get j).inputs.toFinset) (isConstW C)
              have hle2 := List.toFinset_card_le (C.gates.get j).inputs
              have hf := (hfan (C.gates.get j) (List.get_mem _ _)).2
              omega
          _ = 2 * Ec.card := by simp [mul_comm]
      have hEm_le : ∑ j ∈ Em, (((C.gates.get j).inputs.toFinset).filter (isConstW C)).card ≤ Em.card := by
        calc ∑ j ∈ Em, (((C.gates.get j).inputs.toFinset).filter (isConstW C)).card
            ≤ ∑ _j ∈ Em, 1 := by
              apply Finset.sum_le_sum
              intro j hjEm
              have hj_nc : ¬ isConstW C (9 + j.val) := (Finset.mem_filter.mp hjEm).2
              have hex_nc : ∃ u0 ∈ (C.gates.get j).inputs, ¬ isConstW C u0 := by
                by_contra hall
                push Not at hall
                exact hj_nc (hconst_gate j hall)
              rcases hex_nc with ⟨u0, hu0_mem, hu0_nc⟩
              have hlt : (((C.gates.get j).inputs.toFinset).filter (isConstW C)).card <
                  ((C.gates.get j).inputs.toFinset).card := by
                apply Finset.card_lt_card
                rw [Finset.ssubset_iff_subset_ne]
                refine ⟨Finset.filter_subset _ _, fun heq => ?_⟩
                have : u0 ∈ ((C.gates.get j).inputs.toFinset).filter (isConstW C) := by
                  rw [heq]; exact List.mem_toFinset.mpr hu0_mem
                exact hu0_nc (Finset.mem_filter.mp this).2
              have hlen_j : ((C.gates.get j).inputs.toFinset).card ≤ 2 :=
                le_trans (List.toFinset_card_le _) (hfan (C.gates.get j) (List.get_mem _ _)).2
              omega
          _ = Em.card := by simp
      change ∑ j ∈ Ec, (((C.gates.get j).inputs.toFinset).filter (isConstW C)).card +
        ∑ j ∈ Em, (((C.gates.get j).inputs.toFinset).filter (isConstW C)).card =
        ∑ j ∈ E, (((C.gates.get j).inputs.toFinset).filter (isConstW C)).card at hsplit
      omega
    have hE_split : Ec.card + Em.card = E.card :=
      card_filter_add_not E (fun j => isConstW C (9 + j.val))
    have hle := Finset.card_le_card hKused_sub
    omega
  let S : Finset (Fin C.gates.length) :=
    Finset.univ.filter (fun j => 2 ≤ j.val ∧ j ∉ E ∧ ¬ isConstW C (9 + j.val))
  have hS_le_6 : S.card ≤ 6 := by
    let G2 : Finset (Fin C.gates.length) := Finset.univ.filter (fun j => 2 ≤ j.val)
    have hG2_card : G2.card = C.gates.length - 2 := by
      have hcomp : (Finset.univ.filter (fun j : Fin C.gates.length => j.val < 2)).card = 2 := by
        have heq : Finset.univ.filter (fun j : Fin C.gates.length => j.val < 2) =
            {⟨0, by omega⟩, ⟨1, by omega⟩} := by
          ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
            Finset.mem_singleton, Fin.ext_iff]
          omega
        rw [heq, Finset.card_pair]
        simp [Fin.ext_iff]
      have hadd := card_filter_add_not (s := (Finset.univ : Finset (Fin C.gates.length)))
        (p := fun j => 2 ≤ j.val)
      have hneg : Finset.univ.filter (fun j : Fin C.gates.length => ¬ 2 ≤ j.val) =
          Finset.univ.filter (fun j : Fin C.gates.length => j.val < 2) := by
        ext j; simp
      rw [hneg, hcomp, Finset.card_univ, Fintype.card_fin] at hadd
      change G2.card + 2 = C.gates.length at hadd
      omega
    have hdisj : Disjoint S E := by
      rw [Finset.disjoint_left]
      intro j hjS hjE
      exact (Finset.mem_filter.mp hjS).2.2.1 hjE
    have hunion : S ∪ E ⊆ G2 := by
      intro j hj
      rcases Finset.mem_union.mp hj with hjS | hjE
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hjS).2.1⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hjE).2.1⟩
    have hle := Finset.card_le_card hunion
    rw [Finset.card_union_of_disjoint hdisj, hG2_card] at hle
    simp [Circuit.size] at hsize
    omega
  let Swires : Finset ℕ := S.image (fun j : Fin C.gates.length => 9 + j.val)
  have hSwires_card : Swires.card = S.card := by
    apply Finset.card_image_of_injective
    intro a b h
    dsimp at h
    exact Fin.ext (by omega)
  have hcanon_prop : ∀ w : ℕ, w < 9 + C.gates.length → ¬ isConstW C w →
      canonW C E w ∈ inputs7 ∪ Swires ∧
      ∀ y : Fin 7 → Bool, wireVal C (emb y) (canonW C E w) = wireVal C (emb y) w := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw hnc
      by_cases hw9 : w < 9
      · have hcw : canonW C E w = w := by
          rw [canonW]
          have : ¬ (9 ≤ w ∧ w < 9 + C.gates.length) := by omega
          simp [this]
        rw [hcw]
        refine ⟨Finset.mem_union_left _ (mem_inputs7_of_lt9 w hw9 (fun h => hnc (h ▸ hconst_0))
          (fun h => hnc (h ▸ hconst_8))), fun _ => rfl⟩
      · let j : Fin C.gates.length := ⟨w - 9, by omega⟩
        have hw_eq : w = 9 + j.val := by simp [j]; omega
        have hj_ge2 : 2 ≤ j.val := by
          by_contra hlt
          have : w = 9 ∨ w = 10 := by omega
          rcases this with rfl | rfl
          · exact hnc hconst_9
          · exact hnc hconst_10
        by_cases hjE : j ∈ E
        · rcases hnf j with ⟨hop, a, ha, hin⟩ | ⟨hop, a, b, hab, hb, hin⟩
          · have ha_c : isConstW C a := by
              rcases (Finset.mem_filter.mp hjE).2.2 with ⟨u, hu, huc⟩
              rw [hin] at hu
              simp at hu
              subst hu
              exact huc
            have hwc : isConstW C w := by
              rw [hw_eq]
              exact hconst_gate j (fun u hu => by rw [hin] at hu; simp at hu; subst hu; exact ha_c)
            exact (hnc hwc).elim
          · have hcw_step : canonW C E w =
                if isConstW C a then
                  if isConstW C b then w else canonW C E b
                else if isConstW C b then canonW C E a else w := by
              rw [canonW]
              have hcond : 9 ≤ w ∧ w < 9 + C.gates.length := ⟨by omega, hw⟩
              rw [dif_pos hcond]
              dsimp only
              have hjE' : (⟨w - 9, by omega⟩ : Fin C.gates.length) ∈ E := hjE
              rw [if_pos hjE']
              have hin' : (C.gates.get ⟨w - 9, by omega⟩).inputs = [a, b] := hin
              rw [hin']
              dsimp only
              have hab_w : a < w ∧ b < w := ⟨by omega, by omega⟩
              rw [dif_pos hab_w]
            rw [hcw_step]
            by_cases hca : isConstW C a
            · by_cases hcb : isConstW C b
              · have hwc : isConstW C w := by
                  rw [hw_eq]
                  exact hconst_gate j (fun u hu => by
                    rw [hin] at hu; simp at hu; rcases hu with rfl | rfl <;> assumption)
                exact (hnc hwc).elim
              · simp only [hca, hcb, ↓reduceIte]
                rcases hca with ⟨ba, hba⟩
                have hwb : ∀ y : Fin 7 → Bool, wireVal C (emb y) w = wireVal C (emb y) b := by
                  rcases hop with hop | hop
                  · cases ba with
                    | false =>
                      exfalso
                      apply hnc
                      refine ⟨false, fun y => ?_⟩
                      rw [hw_eq, wireVal_gate C (emb y) j (hpre j), hop, hin]
                      simp [GateOp.eval, hba y]
                    | true =>
                      intro y
                      rw [hw_eq, wireVal_gate C (emb y) j (hpre j), hop, hin]
                      simp [GateOp.eval, hba y]
                  · cases ba with
                    | true =>
                      exfalso
                      apply hnc
                      refine ⟨true, fun y => ?_⟩
                      rw [hw_eq, wireVal_gate C (emb y) j (hpre j), hop, hin]
                      simp [GateOp.eval, hba y]
                    | false =>
                      intro y
                      rw [hw_eq, wireVal_gate C (emb y) j (hpre j), hop, hin]
                      simp [GateOp.eval, hba y]
                rcases ih b (by omega) (by omega) hcb with ⟨hmem, hval⟩
                exact ⟨hmem, fun y => (hval y).trans (hwb y).symm⟩
            · by_cases hcb : isConstW C b
              · simp only [hca, hcb, ↓reduceIte]
                rcases hcb with ⟨bb, hbb⟩
                have hwa : ∀ y : Fin 7 → Bool, wireVal C (emb y) w = wireVal C (emb y) a := by
                  rcases hop with hop | hop
                  · cases bb with
                    | false =>
                      exfalso
                      apply hnc
                      refine ⟨false, fun y => ?_⟩
                      rw [hw_eq, wireVal_gate C (emb y) j (hpre j), hop, hin]
                      simp [GateOp.eval, hbb y]
                    | true =>
                      intro y
                      rw [hw_eq, wireVal_gate C (emb y) j (hpre j), hop, hin]
                      simp [GateOp.eval, hbb y]
                  · cases bb with
                    | true =>
                      exfalso
                      apply hnc
                      refine ⟨true, fun y => ?_⟩
                      rw [hw_eq, wireVal_gate C (emb y) j (hpre j), hop, hin]
                      simp [GateOp.eval, hbb y]
                    | false =>
                      intro y
                      rw [hw_eq, wireVal_gate C (emb y) j (hpre j), hop, hin]
                      simp [GateOp.eval, hbb y]
                rcases ih a (by omega) (by omega) hca with ⟨hmem, hval⟩
                exact ⟨hmem, fun y => (hval y).trans (hwa y).symm⟩
              · exfalso
                rcases (Finset.mem_filter.mp hjE).2.2 with ⟨u, hu, huc⟩
                rw [hin] at hu
                simp at hu
                rcases hu with rfl | rfl
                · exact hca huc
                · exact hcb huc
        · have hcw : canonW C E w = w := by
            rw [canonW]
            have hcond : 9 ≤ w ∧ w < 9 + C.gates.length := ⟨by omega, hw⟩
            rw [dif_pos hcond]
            dsimp only
            have hjE' : (⟨w - 9, by omega⟩ : Fin C.gates.length) ∉ E := hjE
            rw [if_neg hjE']
          rw [hcw]
          have hjS : j ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj_ge2, hjE, hw_eq ▸ hnc⟩
          exact ⟨Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j, hjS, hw_eq.symm⟩), fun _ => rfl⟩
  let D : SmallDAG := {
    S := Swires
    hdisj := by
      rw [Finset.disjoint_left]
      intro w hw1 hw2
      rcases Finset.mem_image.mp hw1 with ⟨i, _, rfl⟩
      rcases Finset.mem_image.mp hw2 with ⟨j, _, hj⟩
      have := embIdx_lt9 i
      omega
    hScard := by omega
    children := fun u =>
      if hu : 9 ≤ u ∧ u < 9 + C.gates.length then
        (C.gates.get ⟨u - 9, by omega⟩).inputs.map (canonW C E)
      else []
    op := fun u =>
      if hu : 9 ≤ u ∧ u < 9 + C.gates.length then
        (C.gates.get ⟨u - 9, by omega⟩).op
      else GateOp.and
    val := fun u y => wireVal C (emb y) u
    hchild_lt := by
      intro u hu c hc
      rcases Finset.mem_image.mp hu with ⟨j, _, rfl⟩
      have hcond : 9 ≤ 9 + j.val ∧ 9 + j.val < 9 + C.gates.length := ⟨by omega, by omega⟩
      rw [dif_pos hcond, List.mem_map] at hc
      rcases hc with ⟨a, ha, rfl⟩
      have hidx : (⟨9 + j.val - 9, by omega⟩ : Fin C.gates.length) = j := Fin.ext (by simp)
      rw [hidx] at ha
      exact lt_of_le_of_lt (canonW_le C E a) (hpre j a ha)
    hchild_mem := by
      intro u hu c hc
      rcases Finset.mem_image.mp hu with ⟨j, hjS, rfl⟩
      have hcond : 9 ≤ 9 + j.val ∧ 9 + j.val < 9 + C.gates.length := ⟨by omega, by omega⟩
      rw [dif_pos hcond, List.mem_map] at hc
      rcases hc with ⟨a, ha, rfl⟩
      have hidx : (⟨9 + j.val - 9, by omega⟩ : Fin C.gates.length) = j := Fin.ext (by simp)
      rw [hidx] at ha
      have ha_nc : ¬ isConstW C a := by
        intro hac
        have hj_ge2 : 2 ≤ j.val := (Finset.mem_filter.mp hjS).2.1
        have hj_notE : j ∉ E := (Finset.mem_filter.mp hjS).2.2.1
        exact hj_notE (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj_ge2, a, ha, hac⟩)
      have ha_lt : a < 9 + C.gates.length := lt_trans (hpre j a ha) (by omega)
      exact (hcanon_prop a ha_lt ha_nc).1
    hchild_nf := by
      intro u hu
      rcases Finset.mem_image.mp hu with ⟨j, _, rfl⟩
      have hcond : 9 ≤ 9 + j.val ∧ 9 + j.val < 9 + C.gates.length := ⟨by omega, by omega⟩
      have hidx : (⟨9 + j.val - 9, by omega⟩ : Fin C.gates.length) = j := Fin.ext (by simp)
      rw [dif_pos hcond,
          dif_pos hcond, List.length_map, hidx]
      rcases hnf j with ⟨hop, a, _, hin⟩ | ⟨hop, a, b, _, _, hin⟩
      · left; exact ⟨hop, by rw [hin]; rfl⟩
      · right; exact ⟨hop, by rw [hin]; rfl⟩
    heval_in := by
      intro i y
      simpa [emb_embIdx] using wireVal_input C (emb y) ⟨embIdx i, embIdx_lt9 i⟩
    heval_gate := by
      intro u hu y
      rcases Finset.mem_image.mp hu with ⟨j, hjS, rfl⟩
      have hcond : 9 ≤ 9 + j.val ∧ 9 + j.val < 9 + C.gates.length := ⟨by omega, by omega⟩
      have hidx : (⟨9 + j.val - 9, by omega⟩ : Fin C.gates.length) = j := Fin.ext (by simp)
      rw [dif_pos hcond,
          dif_pos hcond, List.map_map, hidx]
      rw [wireVal_gate C (emb y) j (hpre j)]
      congr 1
      apply List.map_congr_left
      intro a ha
      have ha_nc : ¬ isConstW C a := by
        intro hac
        have hj_ge2 : 2 ≤ j.val := (Finset.mem_filter.mp hjS).2.1
        have hj_notE : j ∉ E := (Finset.mem_filter.mp hjS).2.2.1
        exact hj_notE (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj_ge2, a, ha, hac⟩)
      have ha_lt : a < 9 + C.gates.length := lt_trans (hpre j a ha) (by omega)
      exact ((hcanon_prop a ha_lt ha_nc).2 y).symm
    hnc := by
      intro u hu
      have hnc_u : ¬ isConstW C u := by
        rcases Finset.mem_union.mp hu with h1 | h2
        · rcases Finset.mem_image.mp h1 with ⟨i, _, rfl⟩
          rintro ⟨b, hb⟩
          have h1 := hb (fun _ => false)
          have h2 := hb (fun _ => true)
          have hv1 : wireVal C (emb (fun _ => false)) (embIdx i) = false := by
            simpa [emb_embIdx] using wireVal_input C (emb (fun _ => false)) ⟨embIdx i, embIdx_lt9 i⟩
          have hv2 : wireVal C (emb (fun _ => true)) (embIdx i) = true := by
            simpa [emb_embIdx] using wireVal_input C (emb (fun _ => true)) ⟨embIdx i, embIdx_lt9 i⟩
          rw [hv1] at h1
          rw [hv2] at h2
          exact Bool.false_ne_true (h1.trans h2.symm)
        · rcases Finset.mem_image.mp h2 with ⟨j, hjS, rfl⟩
          exact (Finset.mem_filter.mp hjS).2.2.2
      by_contra hall
      push Not at hall
      exact hnc_u ⟨wireVal C (emb (fun _ => false)) u, fun y => hall y (fun _ => false)⟩
  }
  have hout_lt : C.output < 9 + C.gates.length := by
    simp [Circuit.size] at hout
    omega
  rcases hcanon_prop C.output hout_lt hnot_const_out with ⟨hv_mem, hv_val⟩
  exact no_small_dag D (canonW C E C.output) hv_mem (fun y => by
    change wireVal C (emb y) (canonW C E C.output) = f7 y
    rw [hv_val y]
    change C.eval (List.ofFn (emb y)) = f7 y
    rw [heval (emb y), perm3_emb y])

end PEqualNP.Outside.L_meta_27359_aux

theorem PEqualNP.Outside.L_meta_27359 : (¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧
    (∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))) ∧
    C.output + 1 = 9 + C.size ∧
    (∀ j : Fin C.gates.length,
      ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
          ∃ a, a < 9 + j.val ∧ (C.gates.get j).inputs = [a]) ∨
      (((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
          (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
          ∃ a b, a < b ∧ b < 9 + j.val ∧ (C.gates.get j).inputs = [a, b])) ∧
    (∀ j : Fin C.gates.length,
      (∃ x y : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn y)).getD (9 + j.val) false) ∧
      ∀ k, k < 9 + j.val → ∃ x : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn x)).getD k false) ∧
    (∀ j : Fin C.gates.length, j.val + 1 < C.gates.length →
      ∃ k : Fin C.gates.length, j.val < k.val ∧ 9 + j.val ∈ (C.gates.get k).inputs) ∧
    C.gates.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 4]⟩ ∧
    C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 8]⟩)) :=
  PEqualNP.Outside.L_meta_27359_aux.main_proof
