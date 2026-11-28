import PEqualNP.Defs
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Fintype.OfMap
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Prod
import Mathlib.Logic.Equiv.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace PEqualNP.Outside.L_lib_894_aux

open PEqualNP.Search

section Part1

def bits (w v : Nat) : List Bool := (List.range w).map (fun j => v.testBit j)

def header (n : Nat) : List Bool := List.replicate n true ++ [false]

def width (n : Nat) : Nat := n.log2 + 1

abbrev Ban := (Nat × Nat) × (Nat × Nat)

def legal (n : Nat) (B : List Ban) : Prop :=
  2 ≤ n ∧ ∀ e ∈ B, e.1.1 < e.2.1 ∧ e.2.1 < n ∧ e.1.2 < 3 ∧ e.2.2 < 3

def encBan (w : Nat) (e : Ban) : List Bool :=
  bits w e.1.1 ++ bits 2 e.1.2 ++ bits w e.2.1 ++ bits 2 e.2.2

def enc (n : Nat) (B : List Ban) : List Bool :=
  header n ++ B.flatMap (encBan (width n))

def valid (n : Nat) (B : List Ban) (a : Fin n → Fin 3) : Prop :=
  let v := List.ofFn (fun j => (a j).val)
  ∀ e ∈ B, v.getD e.1.1 3 ≠ e.1.2 ∨ v.getD e.2.1 3 ≠ e.2.2

theorem bits_injective : Function.Injective Nat.bits := by
  intro n m h
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_eq_inth, Nat.testBit_eq_inth, h]

theorem digits_append_inj : ∀ (ds ds' : List Bool) (b b' : Bool) (r r' : List Bool),
    (ds.flatMap fun d => [true, d]) ++ (false :: b :: r) =
      (ds'.flatMap fun d => [true, d]) ++ (false :: b' :: r') →
    ds = ds' ∧ b = b' ∧ r = r' := by
  intro ds
  induction ds with
  | nil =>
    intro ds' b b' r r' h
    cases ds' with
    | nil => simp_all
    | cons d ds' => simp at h
  | cons d ds ih =>
    intro ds' b b' r r' h
    cases ds' with
    | nil => simp at h
    | cons d' ds' =>
      simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.cons.injEq,
        true_and] at h
      obtain ⟨hd, h⟩ := h
      obtain ⟨h1, h2, h3⟩ := ih ds' b b' r r' h
      exact ⟨by rw [hd, h1], h2, h3⟩

theorem literal_append_inj (l l' : Literal) (r r' : List Bool)
    (h : encodeLiteral l ++ r = encodeLiteral l' ++ r') : l = l' ∧ r = r' := by
  obtain ⟨i, b⟩ := l
  obtain ⟨i', b'⟩ := l'
  simp only [encodeLiteral, List.cons_append, List.nil_append, List.append_assoc,
    List.cons.injEq, true_and] at h
  obtain ⟨hb, h⟩ := h
  obtain ⟨h1, -, h3⟩ := digits_append_inj _ _ true true r r' h
  exact ⟨by rw [bits_injective h1, hb], h3⟩

theorem encodeLiteral_head (l : Literal) (r : List Bool) :
    ∃ t, encodeLiteral l ++ r = true :: t := ⟨_, rfl⟩

theorem clause_append_inj : ∀ (c c' : Clause) (r r' : List Bool),
    encodeClause c ++ r = encodeClause c' ++ r' → c = c' ∧ r = r' := by
  intro c
  induction c with
  | nil =>
    intro c' r r' h
    cases c' with
    | nil => simpa [encodeClause] using h
    | cons l' c' =>
      exfalso
      obtain ⟨t, ht⟩ := encodeLiteral_head l' (c'.flatMap encodeLiteral ++ [false, false] ++ r')
      simp only [encodeClause, List.flatMap_cons, List.append_assoc] at h ht
      rw [ht] at h
      simp at h
  | cons l c ih =>
    intro c' r r' h
    cases c' with
    | nil =>
      exfalso
      obtain ⟨t, ht⟩ := encodeLiteral_head l (c.flatMap encodeLiteral ++ [false, false] ++ r)
      simp only [encodeClause, List.flatMap_cons, List.append_assoc] at h ht
      rw [ht] at h
      simp at h
    | cons l' c' =>
      simp only [encodeClause, List.flatMap_cons, List.append_assoc] at h
      obtain ⟨h1, h2⟩ := literal_append_inj l l' _ _ h
      have := ih c' r r' (by simpa [encodeClause, List.append_assoc] using h2)
      exact ⟨by rw [h1, this.1], this.2⟩

theorem encodeCNF_injective : Function.Injective encodeCNF := by
  intro φ
  induction φ with
  | nil =>
    intro φ' h
    cases φ' with
    | nil => rfl
    | cons c φ' => simp [encodeCNF, encodeClause] at h
  | cons c φ ih =>
    intro φ' h
    cases φ' with
    | nil => simp [encodeCNF, encodeClause] at h
    | cons c' φ' =>
      simp only [encodeCNF, List.flatMap_cons] at h
      obtain ⟨h1, h2⟩ := clause_append_inj c c' _ _ h
      rw [h1, ih h2]

def vcode (i : Nat) : List Bool := (i.bits.flatMap fun d => [true, d]) ++ [false, true]

inductive WS : Type
  | a | b | c | d | abT | abF | cT | cF | dead
  deriving DecidableEq

instance : Fintype WS :=
  Fintype.ofList [.a, .b, .c, .d, .abT, .abF, .cT, .cF, .dead]
    (by intro q; cases q <;> simp)

def wfD : WS → Bool → WS
  | .a, true => .abT
  | .a, false => .abF
  | .b, true => .abT
  | .b, false => .abF
  | .abT, _ => .c
  | .abF, false => .a
  | .abF, true => .dead
  | .c, true => .cT
  | .c, false => .cF
  | .d, true => .cT
  | .d, false => .dead
  | .cT, true => .c
  | .cT, false => .d
  | .cF, true => .b
  | .cF, false => .dead
  | .dead, _ => .dead

def wfB (x : List Bool) : Bool := decide (x.foldl wfD .a = .a)

theorem encodeLiteral_eq (l : Literal) : encodeLiteral l = true :: l.2 :: vcode l.1 := by
  simp [encodeLiteral, vcode]

theorem vcode_bit (b : Bool) (n : Nat) (h : n = 0 → b = true) :
    vcode (Nat.bit b n) = true :: b :: vcode n := by
  simp [vcode, Nat.bits_append_bit n b h]

theorem vcode_zero : vcode 0 = [false, true] := by simp [vcode]

theorem foldl_dead (s : List Bool) : s.foldl wfD .dead = .dead := by
  induction s with
  | nil => rfl
  | cons x s ih => simpa [wfD] using ih

theorem foldl_vcode (n : Nat) : ∀ r : List Bool,
    (vcode n ++ r).foldl wfD .c = r.foldl wfD .b ∧
      (n ≠ 0 → (vcode n ++ r).foldl wfD .d = r.foldl wfD .b) := by
  induction n using Nat.binaryRec' with
  | zero => intro r; simp [vcode_zero, wfD]
  | bit b n h ih =>
    intro r; obtain ⟨ih1, ih2⟩ := ih r; rw [vcode_bit b n h]
    cases b
    · have hn : n ≠ 0 := fun h0 => by simpa using h h0
      simp [wfD, ih2 hn]
    · simp [wfD, ih1]

theorem foldl_lit (l : Literal) (r : List Bool) :
    (encodeLiteral l ++ r).foldl wfD .a = r.foldl wfD .b ∧
      (encodeLiteral l ++ r).foldl wfD .b = r.foldl wfD .b := by
  simp [encodeLiteral_eq, wfD, (foldl_vcode l.1 r).1]

theorem foldl_clause (c : Clause) (r : List Bool) :
    (encodeClause c ++ r).foldl wfD .a = r.foldl wfD .a ∧
      (encodeClause c ++ r).foldl wfD .b = r.foldl wfD .a := by
  induction c with
  | nil => simp [encodeClause, wfD]
  | cons l c ih =>
    have e : encodeClause (l :: c) ++ r = encodeLiteral l ++ (encodeClause c ++ r) := by
      simp [encodeClause]
    rw [e, (foldl_lit l _).1, (foldl_lit l _).2, ih.2]; exact ⟨rfl, rfl⟩

theorem foldl_cnf (φ : CNF) : (encodeCNF φ).foldl wfD .a = .a := by
  induction φ with
  | nil => rfl
  | cons c φ ih =>
    have e : encodeCNF (c :: φ) = encodeClause c ++ encodeCNF φ := by simp [encodeCNF]
    rw [e, (foldl_clause c _).1, ih]

def Good : WS → List Bool → Prop
  | .a, s => ∃ φ : CNF, s = encodeCNF φ
  | .b, s => ∃ (c : Clause) (φ : CNF), s = encodeClause c ++ encodeCNF φ
  | .c, s => ∃ (n : Nat) (c : Clause) (φ : CNF), s = vcode n ++ (encodeClause c ++ encodeCNF φ)
  | .d, s => ∃ (n : Nat) (c : Clause) (φ : CNF), n ≠ 0 ∧ s = vcode n ++ (encodeClause c ++ encodeCNF φ)
  | _, _ => True

theorem enc_cons_cons (n : Nat) (p : Bool) (c : Clause) (φ : CNF) :
    true :: p :: (vcode n ++ (encodeClause c ++ encodeCNF φ)) =
      encodeClause ((n, p) :: c) ++ encodeCNF φ := by
  simp [encodeClause, encodeLiteral_eq]

theorem good_of_accept : ∀ (s : List Bool) (q : WS), s.foldl wfD q = .a → Good q s
  | [], q, h => by cases q <;> first | trivial | exact ⟨[], rfl⟩
  | [x], q, h => by cases q <;> first | trivial | (cases x <;> simp [wfD] at h)
  | x :: y :: r, q, h => by
    have ih := good_of_accept r
    cases q
    case abT | abF | cT | cF | dead => trivial
    case a =>
      cases x
      · cases y <;> simp only [List.foldl_cons, wfD, foldl_dead] at h
        · obtain ⟨φ, rfl⟩ := ih _ h; exact ⟨[] :: φ, by simp [encodeCNF, encodeClause]⟩
        · exact absurd h (by decide)
      · simp only [List.foldl_cons, wfD] at h
        obtain ⟨n, c, φ, rfl⟩ := ih _ h
        exact ⟨((n, y) :: c) :: φ, by rw [enc_cons_cons]; simp [encodeCNF]⟩
    case b =>
      cases x
      · cases y <;> simp only [List.foldl_cons, wfD, foldl_dead] at h
        · obtain ⟨φ, rfl⟩ := ih _ h; exact ⟨[], φ, by simp [encodeClause]⟩
        · exact absurd h (by decide)
      · simp only [List.foldl_cons, wfD] at h
        obtain ⟨n, c, φ, rfl⟩ := ih _ h; exact ⟨(n, y) :: c, φ, enc_cons_cons _ _ _ _⟩
    case c =>
      cases x <;> cases y <;> simp only [List.foldl_cons, wfD, foldl_dead] at h
      · exact absurd h (by decide)
      · obtain ⟨c, φ, rfl⟩ := ih _ h; exact ⟨0, c, φ, by simp [vcode_zero]⟩
      · obtain ⟨n, c, φ, hn, rfl⟩ := ih _ h
        exact ⟨Nat.bit false n, c, φ, by rw [vcode_bit false n (fun h0 => absurd h0 hn)]; rfl⟩
      · obtain ⟨n, c, φ, rfl⟩ := ih _ h
        exact ⟨Nat.bit true n, c, φ, by rw [vcode_bit true n (fun _ => rfl)]; rfl⟩
    case d =>
      cases x <;> cases y <;> simp only [List.foldl_cons, wfD, foldl_dead] at h
      · exact absurd h (by decide)
      · exact absurd h (by decide)
      · obtain ⟨n, c, φ, hn, rfl⟩ := ih _ h
        exact ⟨Nat.bit false n, c, φ, by simp [hn], by rw [vcode_bit false n (fun h0 => absurd h0 hn)]; rfl⟩
      · obtain ⟨n, c, φ, rfl⟩ := ih _ h
        exact ⟨Nat.bit true n, c, φ, by simp, by rw [vcode_bit true n (fun _ => rfl)]; rfl⟩

theorem wfB_iff (x : List Bool) : wfB x = true ↔ ∃ φ : CNF, encodeCNF φ = x := by
  rw [wfB, decide_eq_true_iff]
  constructor
  · intro h; obtain ⟨φ, rfl⟩ := good_of_accept x .a h; exact ⟨φ, rfl⟩
  · rintro ⟨φ, rfl⟩; exact foldl_cnf φ

def anchorBans : List Ban :=
  [((0, 0), (1, 1)), ((0, 0), (1, 2)),
   ((0, 1), (1, 0)), ((0, 1), (1, 1)), ((0, 1), (1, 2)),
   ((0, 2), (1, 0)), ((0, 2), (1, 1)), ((0, 2), (1, 2))]

def emptyBan (F : CNF) : List Ban :=
  if F.any List.isEmpty then [((0, 0), (1, 0))] else []

def boolBans (V : Nat) : List Ban :=
  (List.range V).map (fun i => ((0, 0), (2 + i, 2)))

def litBans (ord : List Nat) (u : Nat) (l : Literal) : List Ban :=
  let v := 2 + ord.idxOf l.1
  let tVal := if l.2 then 1 else 0
  let fVal := if l.2 then 0 else 1
  [((v, tVal), (u, 0)), ((v, fVal), (u, 1))]

def transBans (u : Nat) : List Ban :=
  [((u, 0), (u + 1, 2)),
   ((u, 1), (u + 1, 0)), ((u, 1), (u + 1, 1)),
   ((u, 2), (u + 1, 0)), ((u, 2), (u + 1, 1))]

def litsBans (ord : List Nat) : Nat → Clause → List Ban
  | _, [] => []
  | u, [l] => litBans ord u l ++ [((0, 0), (u, 0))]
  | u, l :: l' :: rest =>
    litBans ord u l ++ transBans u ++ litsBans ord (u + 1) (l' :: rest)

def clauseBans (ord : List Nat) (V off : Nat) : Clause → List Ban
  | [] => []
  | l :: rest => [((0, 0), (2 + V + off, 2))] ++ litsBans ord (2 + V + off) (l :: rest)

def clausesBans (ord : List Nat) (V : Nat) : Nat → CNF → List Ban
  | _, [] => []
  | off, c :: cs => clauseBans ord V off c ++ clausesBans ord V (off + c.length) cs

def makeB (F : CNF) : List Ban :=
  let ord := ((F.flatten).map Prod.fst).eraseDups
  anchorBans ++ emptyBan F ++ boolBans ord.length ++ clausesBans ord ord.length 0 F

theorem litsBans_length (ord : List Nat) : ∀ (u : Nat) (c : Clause),
    c ≠ [] → (litsBans ord u c).length + 4 = 7 * c.length := by
  intro u c
  induction c generalizing u with
  | nil => intro h; exact absurd rfl h
  | cons l rest ih =>
    intro _
    cases rest with
    | nil => simp [litsBans, litBans]
    | cons l' rest' =>
      have h := ih (u + 1) (by simp)
      simp only [litsBans, litBans, transBans, List.length_append, List.length_cons,
        List.length_nil] at h ⊢
      omega

theorem clauseBans_length (ord : List Nat) (V off : Nat) (c : Clause) :
    (clauseBans ord V off c).length ≤ 7 * c.length + 2 := by
  cases c with
  | nil => simp [clauseBans]
  | cons l rest =>
    have h := litsBans_length ord (2 + V + off) (l :: rest) (by simp)
    simp only [clauseBans, List.length_append, List.length_cons, List.length_nil] at h ⊢
    omega

theorem clausesBans_length (ord : List Nat) (V : Nat) : ∀ (off : Nat) (cs : CNF),
    (clausesBans ord V off cs).length ≤ 7 * cs.flatten.length + 2 * cs.length := by
  intro off cs
  induction cs generalizing off with
  | nil => simp [clausesBans]
  | cons c cs ih =>
    have h1 := clauseBans_length ord V off c
    have h2 := ih (off + c.length)
    simp only [clausesBans, List.length_append, List.flatten_cons, List.length_cons]
    omega

theorem makeB_length (F : CNF) :
    (makeB F).length ≤ 9 + ((F.flatten).map Prod.fst).eraseDups.length +
      7 * F.flatten.length + 2 * F.length := by
  unfold makeB
  simp only [List.length_append]
  have h1 : anchorBans.length = 8 := rfl
  have h2 : (emptyBan F).length ≤ 1 := by
    unfold emptyBan
    split <;> simp
  have h3 : (boolBans ((F.flatten).map Prod.fst).eraseDups.length).length =
      ((F.flatten).map Prod.fst).eraseDups.length := by
    simp [boolBans]
  have h4 := clausesBans_length ((F.flatten).map Prod.fst).eraseDups
    ((F.flatten).map Prod.fst).eraseDups.length 0 F
  omega

theorem mem_eraseDups_iff {α : Type} [BEq α] [LawfulBEq α] (x : α) (l : List α) :
    x ∈ l.eraseDups ↔ x ∈ l := by
  exact List.mem_eraseDups

theorem legal_litsBans (ord : List Nat) (n : Nat) : ∀ (u : Nat) (c : Clause),
    2 + ord.length ≤ u → u + c.length ≤ n → (∀ l ∈ c, l.1 ∈ ord) →
    ∀ e ∈ litsBans ord u c, e.1.1 < e.2.1 ∧ e.2.1 < n ∧ e.1.2 < 3 ∧ e.2.2 < 3 := by
  intro u c
  induction c generalizing u with
  | nil => intro _ _ _ e he; simp [litsBans] at he
  | cons l rest ih =>
    intro hu hlen hmem e he
    have hl : ord.idxOf l.1 < ord.length := List.idxOf_lt_length_of_mem (hmem l (by simp))
    cases rest with
    | nil =>
      simp only [litsBans, litBans, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with (rfl | rfl) | rfl
      · dsimp only
        refine ⟨by omega, by simp at hlen; omega, ?_, by omega⟩
        cases l.2 <;> simp
      · dsimp only
        refine ⟨by omega, by simp at hlen; omega, ?_, by omega⟩
        cases l.2 <;> simp
      · dsimp only; exact ⟨by omega, by simp at hlen; omega, by omega, by omega⟩
    | cons l' rest' =>
      simp only [litsBans, litBans, transBans, List.mem_append, List.mem_cons, List.not_mem_nil,
        or_false] at he
      simp only [List.length_cons] at hlen
      rcases he with ((rfl | rfl) | (rfl | rfl | rfl | rfl | rfl)) | he
      · dsimp only
        refine ⟨by omega, by omega, ?_, by omega⟩
        cases l.2 <;> simp
      · dsimp only
        refine ⟨by omega, by omega, ?_, by omega⟩
        cases l.2 <;> simp
      · dsimp only; exact ⟨by omega, by omega, by omega, by omega⟩
      · dsimp only; exact ⟨by omega, by omega, by omega, by omega⟩
      · dsimp only; exact ⟨by omega, by omega, by omega, by omega⟩
      · dsimp only; exact ⟨by omega, by omega, by omega, by omega⟩
      · dsimp only; exact ⟨by omega, by omega, by omega, by omega⟩
      · exact ih (u + 1) (by omega) (by simp; omega)
          (fun x hx => hmem x (List.mem_cons_of_mem _ hx)) e he

theorem legal_clausesBans (ord : List Nat) (n : Nat) : ∀ (off : Nat) (cs : CNF),
    2 + ord.length + off + cs.flatten.length ≤ n →
    (∀ c ∈ cs, ∀ l ∈ c, l.1 ∈ ord) →
    ∀ e ∈ clausesBans ord ord.length off cs,
      e.1.1 < e.2.1 ∧ e.2.1 < n ∧ e.1.2 < 3 ∧ e.2.2 < 3 := by
  intro off cs
  induction cs generalizing off with
  | nil => intro _ _ e he; simp [clausesBans] at he
  | cons c cs ih =>
    intro hlen hmem e he
    simp only [clausesBans, List.mem_append] at he
    simp only [List.flatten_cons, List.length_append] at hlen
    rcases he with he | he
    · cases c with
      | nil => simp [clauseBans] at he
      | cons l rest =>
        simp only [clauseBans, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | he
        · simp only [List.length_cons] at hlen
          dsimp only
          exact ⟨by omega, by omega, by omega, by omega⟩
        · exact legal_litsBans ord n (2 + ord.length + off) (l :: rest)
            (by omega) (by omega) (hmem _ (by simp)) e he
    · exact ih (off + c.length) (by omega)
        (fun c' hc' => hmem c' (List.mem_cons_of_mem _ hc')) e he

def insUniq {α : Type} [DecidableEq α] (s : List α) (a : α) : List α :=
  if a ∈ s then s else s ++ [a]

theorem eraseDupsBy_loop_eq {α : Type} [DecidableEq α] :
    ∀ (l acc : List α),
      List.eraseDupsBy.loop (· == ·) l acc = l.foldl insUniq acc.reverse := by
  intro l
  induction l with
  | nil => intro acc; rfl
  | cons a l ih =>
    intro acc
    simp only [List.eraseDupsBy.loop, List.foldl_cons, insUniq]
    have hmem : acc.any (fun b => a == b) = decide (a ∈ acc.reverse) := by
      cases h : acc.any (fun b => a == b)
      · symm
        rw [decide_eq_false_iff_not, List.mem_reverse]
        intro ha
        have h1 : acc.any (fun b => a == b) = true := List.any_eq_true.mpr ⟨a, ha, by simp⟩
        rw [h] at h1; cases h1
      · symm
        rw [decide_eq_true_eq, List.mem_reverse]
        obtain ⟨b, hb, hab⟩ := List.any_eq_true.mp h
        have : a = b := eq_of_beq hab
        rwa [this]
    rw [hmem]
    by_cases ha : a ∈ acc.reverse
    · simp only [ha, decide_true, ite_true]
      exact ih acc
    · simp only [ha, decide_false, ite_false]
      simpa [List.reverse_cons] using ih (a :: acc)

theorem eraseDups_eq_foldl {α : Type} [DecidableEq α] (l : List α) :
    l.eraseDups = l.foldl insUniq [] := by
  simpa [List.eraseDups, List.eraseDupsBy] using eraseDupsBy_loop_eq l []

theorem nodup_foldl_insUniq {α : Type} [DecidableEq α] :
    ∀ (l acc : List α), acc.Nodup → (l.foldl insUniq acc).Nodup := by
  intro l
  induction l with
  | nil => intro acc h; exact h
  | cons a l ih =>
    intro acc h
    simp only [List.foldl_cons, insUniq]
    split
    · exact ih acc h
    · next hna =>
      refine ih (acc ++ [a]) ?_
      rw [List.nodup_append]
      exact ⟨h, List.nodup_singleton a, fun x hx y hy => by
        simp only [List.mem_singleton] at hy
        subst hy
        exact fun e => hna (e ▸ hx)⟩

theorem nodup_eraseDups {α : Type} [DecidableEq α] (l : List α) : l.eraseDups.Nodup := by
  rw [eraseDups_eq_foldl]
  exact nodup_foldl_insUniq l [] List.nodup_nil

theorem makeB_legal (F : CNF) :
    let ord := ((F.flatten).map Prod.fst).eraseDups
    legal (ord.length + F.flatten.length + 2) (makeB F) := by
  intro ord
  have hord : ord = ((F.flatten).map Prod.fst).eraseDups := rfl
  refine ⟨by omega, ?_⟩
  intro e he
  unfold makeB at he
  simp only [List.mem_append] at he
  rcases he with ((he | he) | he) | he
  · simp only [anchorBans, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (dsimp only; omega)
  · unfold emptyBan at he
    split at he
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      subst he; dsimp only; omega
    · simp at he
  · simp only [boolBans, List.mem_map, List.mem_range] at he
    obtain ⟨i, hi, rfl⟩ := he
    dsimp only; rw [← hord] at hi; omega
  · refine legal_clausesBans ord (ord.length + F.flatten.length + 2) 0 F (by omega) ?_ e he
    intro c hc l hl
    rw [List.mem_eraseDups]
    exact List.mem_map.mpr ⟨l, List.mem_flatten.mpr ⟨c, hc, hl⟩, rfl⟩

theorem ofFn_getD {n : Nat} (a : Fin n → Fin 3) (k : Nat) (hk : k < n) :
    (List.ofFn (fun j => (a j).val)).getD k 3 = (a ⟨k, hk⟩).val := by
  simp [List.getD_eq_getElem?_getD, hk]

theorem valid_mem {n : Nat} {B : List Ban} {a : Fin n → Fin 3} (hv : valid n B a)
    {u1 c1 u2 c2 : Nat} (hmem : ((u1, c1), (u2, c2)) ∈ B) (h1 : u1 < n) (h2 : u2 < n) :
    (a ⟨u1, h1⟩).val ≠ c1 ∨ (a ⟨u2, h2⟩).val ≠ c2 := by
  have h := hv ((u1, c1), (u2, c2)) hmem
  rwa [ofFn_getD a u1 h1, ofFn_getD a u2 h2] at h

theorem valid_anchors {n : Nat} {B : List Ban} {a : Fin n → Fin 3} (hn : 2 ≤ n)
    (hsub : ∀ e ∈ anchorBans, e ∈ B) (hv : valid n B a) :
    (a ⟨0, by omega⟩).val = 0 ∧ (a ⟨1, by omega⟩).val = 0 := by
  have h0lt : (a ⟨0, by omega⟩).val < 3 := (a ⟨0, by omega⟩).isLt
  have h1lt : (a ⟨1, by omega⟩).val < 3 := (a ⟨1, by omega⟩).isLt
  have c1 : (a ⟨0, by omega⟩).val ≠ 0 ∨ (a ⟨1, by omega⟩).val ≠ 1 :=
    valid_mem hv (hsub ((0, 0), (1, 1)) (by simp [anchorBans])) (by omega) (by omega)
  have c2 : (a ⟨0, by omega⟩).val ≠ 0 ∨ (a ⟨1, by omega⟩).val ≠ 2 :=
    valid_mem hv (hsub ((0, 0), (1, 2)) (by simp [anchorBans])) (by omega) (by omega)
  have c3 : (a ⟨0, by omega⟩).val ≠ 1 ∨ (a ⟨1, by omega⟩).val ≠ 0 :=
    valid_mem hv (hsub ((0, 1), (1, 0)) (by simp [anchorBans])) (by omega) (by omega)
  have c4 : (a ⟨0, by omega⟩).val ≠ 1 ∨ (a ⟨1, by omega⟩).val ≠ 1 :=
    valid_mem hv (hsub ((0, 1), (1, 1)) (by simp [anchorBans])) (by omega) (by omega)
  have c5 : (a ⟨0, by omega⟩).val ≠ 1 ∨ (a ⟨1, by omega⟩).val ≠ 2 :=
    valid_mem hv (hsub ((0, 1), (1, 2)) (by simp [anchorBans])) (by omega) (by omega)
  have c6 : (a ⟨0, by omega⟩).val ≠ 2 ∨ (a ⟨1, by omega⟩).val ≠ 0 :=
    valid_mem hv (hsub ((0, 2), (1, 0)) (by simp [anchorBans])) (by omega) (by omega)
  have c7 : (a ⟨0, by omega⟩).val ≠ 2 ∨ (a ⟨1, by omega⟩).val ≠ 1 :=
    valid_mem hv (hsub ((0, 2), (1, 1)) (by simp [anchorBans])) (by omega) (by omega)
  have c8 : (a ⟨0, by omega⟩).val ≠ 2 ∨ (a ⟨1, by omega⟩).val ≠ 2 :=
    valid_mem hv (hsub ((0, 2), (1, 2)) (by simp [anchorBans])) (by omega) (by omega)
  omega

def evalLitOrd (ord : List Nat) (x : Fin ord.length → Bool) (l : Literal) : Bool :=
  if h : ord.idxOf l.1 < ord.length then (x ⟨ord.idxOf l.1, h⟩ == l.2) else false

def toRaw (ord : List Nat) (x : Fin ord.length → Bool) (v : Nat) : Bool :=
  if h : ord.idxOf v < ord.length then x ⟨ord.idxOf v, h⟩ else false

theorem toRaw_get (ord : List Nat) (hnd : ord.Nodup) (x : Fin ord.length → Bool)
    (i : Fin ord.length) : toRaw ord x (ord.get i) = x i := by
  unfold toRaw
  have hi : ord.idxOf ord[i.val] = i.val := List.Nodup.idxOf_getElem hnd i.val i.isLt
  simp only [List.get_eq_getElem, hi, i.isLt, dite_true, Fin.eta]

theorem evalLitOrd_eq_raw (ord : List Nat) (x : Fin ord.length → Bool) (raw : Nat → Bool)
    (hagree : ∀ i : Fin ord.length, x i = raw (ord.get i)) (l : Literal) (hl : l.1 ∈ ord) :
    evalLitOrd ord x l = Literal.eval raw l := by
  unfold evalLitOrd Literal.eval
  have hi : ord.idxOf l.1 < ord.length := List.idxOf_lt_length_of_mem hl
  simp only [hi, dite_true]
  rw [hagree ⟨ord.idxOf l.1, hi⟩]
  have hg : ord.get ⟨ord.idxOf l.1, hi⟩ = l.1 := List.getElem_idxOf hi
  rw [hg]

theorem list_any_congr {α : Type} {f g : α → Bool} : ∀ (l : List α),
    (∀ a ∈ l, f a = g a) → l.any f = l.any g := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a l ih =>
    intro h
    simp only [List.any_cons, h a (by simp), ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

theorem list_all_congr {α : Type} {f g : α → Bool} : ∀ (l : List α),
    (∀ a ∈ l, f a = g a) → l.all f = l.all g := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a l ih =>
    intro h
    simp only [List.all_cons, h a (by simp), ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

theorem cnf_eval_eq_ord (F : CNF) (x : Fin ((F.flatten).map Prod.fst).eraseDups.length → Bool)
    (raw : Nat → Bool)
    (hagree : ∀ i, x i = raw (((F.flatten).map Prod.fst).eraseDups.get i)) :
    CNF.eval raw F = F.all (fun c => c.any (evalLitOrd ((F.flatten).map Prod.fst).eraseDups x)) := by
  unfold CNF.eval Clause.eval
  refine list_all_congr F ?_
  intro c hc
  refine list_any_congr c ?_
  intro l hl
  have hmem : l.1 ∈ ((F.flatten).map Prod.fst).eraseDups := by
    rw [List.mem_eraseDups]
    exact List.mem_map.mpr ⟨l, List.mem_flatten.mpr ⟨c, hc, hl⟩, rfl⟩
  exact (evalLitOrd_eq_raw _ x raw hagree l hmem).symm

def clauseStates (evalL : Literal → Bool) : Bool → Clause → List Nat
  | _, [] => []
  | seen, l :: rest =>
    (if seen then 2 else if evalL l then 1 else 0) ::
      clauseStates evalL (seen || evalL l) rest

theorem clauseStates_length (evalL : Literal → Bool) : ∀ (seen : Bool) (c : Clause),
    (clauseStates evalL seen c).length = c.length := by
  intro seen c
  induction c generalizing seen with
  | nil => rfl
  | cons l rest ih => simp [clauseStates, ih]

theorem clauseStates_lt (evalL : Literal → Bool) : ∀ (seen : Bool) (c : Clause) (x : Nat),
    x ∈ clauseStates evalL seen c → x < 3 := by
  intro seen c
  induction c generalizing seen with
  | nil => intro x hx; simp [clauseStates] at hx
  | cons l rest ih =>
    intro x hx
    simp only [clauseStates, List.mem_cons] at hx
    rcases hx with rfl | hx
    · split <;> [omega; (split <;> omega)]
    · exact ih _ x hx

def allStates (evalL : Literal → Bool) (F : CNF) : List Nat :=
  F.flatMap (clauseStates evalL false)

theorem allStates_length (evalL : Literal → Bool) (F : CNF) :
    (allStates evalL F).length = F.flatten.length := by
  induction F with
  | nil => rfl
  | cons c cs ih =>
    simp [allStates, List.flatMap_cons, List.flatten_cons, clauseStates_length]

theorem allStates_lt (evalL : Literal → Bool) (F : CNF) (x : Nat) (hx : x ∈ allStates evalL F) :
    x < 3 := by
  obtain ⟨c, -, hxc⟩ := List.mem_flatMap.mp hx
  exact clauseStates_lt evalL false c x hxc

theorem valid_litsBans {n : Nat} (ord : List Nat) (a : Fin n → Fin 3) (evalL : Literal → Bool)
    (_ha0 : ∀ h0 : 0 < n, (a ⟨0, h0⟩).val = 0)
    (hlit : ∀ l : Literal, l.1 ∈ ord → ∀ hv : 2 + ord.idxOf l.1 < n,
      (a ⟨2 + ord.idxOf l.1, hv⟩).val = (if evalL l then (if l.2 then 1 else 0) else (if l.2 then 0 else 1))) :
    ∀ (u : Nat) (c : Clause) (seen : Bool) (_ : 2 + ord.length ≤ u) (hlen : u + c.length ≤ n),
      (∀ l ∈ c, l.1 ∈ ord) →
      (seen || c.any evalL) = true →
      (∀ (k : Nat) (hk : k < c.length),
        (a ⟨u + k, by omega⟩).val = (clauseStates evalL seen c).getD k 3) →
      valid n (litsBans ord u c) a := by
  intro u c
  induction c generalizing u with
  | nil =>
    intro seen _ _ _ _ _ e he
    simp [litsBans] at he
  | cons l rest ih =>
    intro seen hu hlen hmem hsat hst
    have hmeml : l.1 ∈ ord := hmem l (by simp)
    have hidx : ord.idxOf l.1 < ord.length := List.idxOf_lt_length_of_mem hmeml
    have hvlt : 2 + ord.idxOf l.1 < n := by simp at hlen; omega
    have hult : u < n := by simp at hlen; omega
    have hau : (a ⟨u, hult⟩).val = if seen then 2 else if evalL l then 1 else 0 := by
      have h0 := hst 0 (by simp)
      simpa [clauseStates] using h0
    have hav := hlit l hmeml hvlt
    have hlitValid : valid n (litBans ord u l) a := by
      intro e he
      simp only [litBans, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl
      · rw [ofFn_getD a _ hvlt, ofFn_getD a _ hult, hau, hav]
        cases seen <;> cases evalL l <;> cases l.2 <;> simp
      · rw [ofFn_getD a _ hvlt, ofFn_getD a _ hult, hau, hav]
        cases seen <;> cases evalL l <;> cases l.2 <;> simp
    cases rest with
    | nil =>
      intro e he
      simp only [litsBans, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with he | rfl
      · exact hlitValid e he
      · rw [ofFn_getD a 0 (by omega), ofFn_getD a u hult, hau]
        simp only [List.any_cons, List.any_nil, Bool.or_false] at hsat
        cases seen <;> cases h1 : evalL l <;> simp [h1] at hsat ⊢
    | cons l' rest' =>
      have hu1lt : u + 1 < n := by simp at hlen; omega
      have hau1 : (a ⟨u + 1, hu1lt⟩).val =
          if (seen || evalL l) then 2 else if evalL l' then 1 else 0 := by
        have h1 := hst 1 (by simp)
        simpa [clauseStates] using h1
      have htransValid : valid n (transBans u) a := by
        intro e he
        simp only [transBans, List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl | rfl | rfl | rfl <;>
        · rw [ofFn_getD a u hult, ofFn_getD a (u + 1) hu1lt, hau, hau1]
          cases seen <;> cases evalL l <;> cases evalL l' <;> simp
      have hrestValid : valid n (litsBans ord (u + 1) (l' :: rest')) a := by
        refine ih (u + 1) (seen || evalL l) (by omega) (by simp at hlen ⊢; omega)
          (fun x hx => hmem x (List.mem_cons_of_mem _ hx)) ?_ ?_
        · simp only [List.any_cons, Bool.or_assoc] at hsat ⊢
          exact hsat
        · intro k hk
          have hk' := hst (k + 1) (by simp at hk ⊢; omega)
          have heq : u + (k + 1) = u + 1 + k := by omega
          simpa [heq, clauseStates] using hk'
      intro e he
      simp only [litsBans, List.mem_append] at he
      rcases he with (he | he) | he
      · exact hlitValid e he
      · exact htransValid e he
      · exact hrestValid e he

theorem unique_litsBans {n : Nat} (ord : List Nat) (a : Fin n → Fin 3) (evalL : Literal → Bool)
    (ha0 : ∀ h0 : 0 < n, (a ⟨0, h0⟩).val = 0)
    (hbool : ∀ (i : Nat) (_hi : i < ord.length) (hv : 2 + i < n), (a ⟨2 + i, hv⟩).val < 2)
    (hlit : ∀ l : Literal, l.1 ∈ ord → ∀ hv : 2 + ord.idxOf l.1 < n,
      evalL l = (decide ((a ⟨2 + ord.idxOf l.1, hv⟩).val = 1) == l.2)) :
    ∀ (u : Nat) (c : Clause) (seen : Bool) (_ : 2 + ord.length ≤ u) (hlen : u + c.length ≤ n),
      (∀ l ∈ c, l.1 ∈ ord) →
      c ≠ [] →
      valid n (litsBans ord u c) a →
      (seen = false → ∀ hu : u < n, (a ⟨u, hu⟩).val ≠ 2) →
      (seen = true → ∀ hu : u < n, (a ⟨u, hu⟩).val = 2) →
      (seen || c.any evalL) = true ∧
        ∀ (k : Nat) (hk : k < c.length),
          (a ⟨u + k, by omega⟩).val = (clauseStates evalL seen c).getD k 3 := by
  intro u c
  induction c generalizing u with
  | nil => intro _ _ _ _ hne; exact absurd rfl hne
  | cons l rest ih =>
    intro seen hu hlen hmem _ hval hnf hst
    have hmeml : l.1 ∈ ord := hmem l (by simp)
    have hidx : ord.idxOf l.1 < ord.length := List.idxOf_lt_length_of_mem hmeml
    have hvlt : 2 + ord.idxOf l.1 < n := by simp at hlen; omega
    have hult : u < n := by simp at hlen; omega
    have hvb : (a ⟨2 + ord.idxOf l.1, hvlt⟩).val < 2 := hbool _ hidx hvlt
    have hub : (a ⟨u, hult⟩).val < 3 := (a ⟨u, hult⟩).isLt
    have hevl := hlit l hmeml hvlt
    have hlit0 : (a ⟨2 + ord.idxOf l.1, hvlt⟩).val ≠ (if l.2 then 1 else 0) ∨ (a ⟨u, hult⟩).val ≠ 0 := by
      cases rest with
      | nil => exact valid_mem hval (by simp [litsBans, litBans]) hvlt hult
      | cons _ _ => exact valid_mem hval (by simp [litsBans, litBans]) hvlt hult
    have hlit1 : (a ⟨2 + ord.idxOf l.1, hvlt⟩).val ≠ (if l.2 then 0 else 1) ∨ (a ⟨u, hult⟩).val ≠ 1 := by
      cases rest with
      | nil => exact valid_mem hval (by simp [litsBans, litBans]) hvlt hult
      | cons _ _ => exact valid_mem hval (by simp [litsBans, litBans]) hvlt hult
    have hau : (a ⟨u, hult⟩).val = if seen then 2 else if evalL l then 1 else 0 := by
      cases seen
      · have hne2 := hnf rfl hult
        cases hpol : l.2 <;> simp only [hpol, Bool.false_eq_true, ite_true, ite_false] at hevl hlit0 hlit1 ⊢
        · cases hvalv : (a ⟨2 + ord.idxOf l.1, hvlt⟩).val with
          | zero =>
            have : evalL l = true := by simp [hevl, hvalv]
            simp only [this, ite_true]
            omega
          | succ m =>
            have hm : m = 0 := by omega
            subst hm
            have : evalL l = false := by simp [hevl, hvalv]
            simp only [this, Bool.false_eq_true, ite_false]
            omega
        · cases hvalv : (a ⟨2 + ord.idxOf l.1, hvlt⟩).val with
          | zero =>
            have : evalL l = false := by simp [hevl, hvalv]
            simp only [this, Bool.false_eq_true, ite_false]
            omega
          | succ m =>
            have hm : m = 0 := by omega
            subst hm
            have : evalL l = true := by simp [hevl, hvalv]
            simp only [this, ite_true]
            omega
      · simp [hst rfl hult]
    cases rest with
    | nil =>
      have hend : (a ⟨0, by omega⟩).val ≠ 0 ∨ (a ⟨u, hult⟩).val ≠ 0 :=
        valid_mem hval (by simp [litsBans]) (by omega) hult
      have hne0 : (a ⟨u, hult⟩).val ≠ 0 := by
        have h0 := ha0 (by omega)
        omega
      refine ⟨?_, ?_⟩
      · simp only [List.any_cons, List.any_nil, Bool.or_false]
        cases seen <;> cases h1 : evalL l <;> simp_all
      · intro k hk
        have hk0 : k = 0 := by simp at hk; omega
        subst hk0
        simpa [clauseStates] using hau
    | cons l' rest' =>
      have hu1lt : u + 1 < n := by simp at hlen; omega
      have hu1b : (a ⟨u + 1, hu1lt⟩).val < 3 := (a ⟨u + 1, hu1lt⟩).isLt
      have h02 : (a ⟨u, hult⟩).val ≠ 0 ∨ (a ⟨u + 1, hu1lt⟩).val ≠ 2 :=
        valid_mem hval (by simp [litsBans, transBans]) hult hu1lt
      have h10 : (a ⟨u, hult⟩).val ≠ 1 ∨ (a ⟨u + 1, hu1lt⟩).val ≠ 0 :=
        valid_mem hval (by simp [litsBans, transBans]) hult hu1lt
      have h11 : (a ⟨u, hult⟩).val ≠ 1 ∨ (a ⟨u + 1, hu1lt⟩).val ≠ 1 :=
        valid_mem hval (by simp [litsBans, transBans]) hult hu1lt
      have h20 : (a ⟨u, hult⟩).val ≠ 2 ∨ (a ⟨u + 1, hu1lt⟩).val ≠ 0 :=
        valid_mem hval (by simp [litsBans, transBans]) hult hu1lt
      have h21 : (a ⟨u, hult⟩).val ≠ 2 ∨ (a ⟨u + 1, hu1lt⟩).val ≠ 1 :=
        valid_mem hval (by simp [litsBans, transBans]) hult hu1lt
      have hrestVal : valid n (litsBans ord (u + 1) (l' :: rest')) a := by
        intro e he
        exact hval e (by simp [litsBans, he])
      have ⟨hsat', hst'⟩ := ih (u + 1) (seen || evalL l) (by omega)
        (by simp at hlen ⊢; omega) (fun x hx => hmem x (List.mem_cons_of_mem _ hx))
        (by simp) hrestVal
        (by
          intro hsf hu1
          cases seen <;> cases h1 : evalL l <;> simp_all)
        (by
          intro hst1 hu1
          cases seen <;> cases h1 : evalL l <;> simp_all <;> omega)
      refine ⟨?_, ?_⟩
      · simp only [List.any_cons, Bool.or_assoc] at hsat' ⊢
        exact hsat'
      · intro k hk
        cases k with
        | zero => simpa [clauseStates] using hau
        | succ k' =>
          have hkk := hst' k' (by simp at hk ⊢; omega)
          have heq : u + (k' + 1) = u + 1 + k' := by omega
          simpa [heq, clauseStates] using hkk

theorem valid_clausesBans {n : Nat} (ord : List Nat) (a : Fin n → Fin 3) (evalL : Literal → Bool)
    (ha0 : ∀ h0 : 0 < n, (a ⟨0, h0⟩).val = 0)
    (hlit : ∀ l : Literal, l.1 ∈ ord → ∀ hv : 2 + ord.idxOf l.1 < n,
      (a ⟨2 + ord.idxOf l.1, hv⟩).val = (if evalL l then (if l.2 then 1 else 0) else (if l.2 then 0 else 1))) :
    ∀ (off : Nat) (cs : CNF) (hlen : 2 + ord.length + off + cs.flatten.length ≤ n),
      (∀ c ∈ cs, ∀ l ∈ c, l.1 ∈ ord) →
      (∀ c ∈ cs, c.any evalL = true) →
      (∀ (k : Nat) (hk : k < cs.flatten.length),
        (a ⟨2 + ord.length + off + k, by omega⟩).val = (allStates evalL cs).getD k 3) →
      valid n (clausesBans ord ord.length off cs) a := by
  intro off cs
  induction cs generalizing off with
  | nil => intro _ _ _ _ e he; simp [clausesBans] at he
  | cons c cs ih =>
    intro hlen hmem hsat hst
    simp only [List.flatten_cons, List.length_append] at hlen
    have hcValid : valid n (clauseBans ord ord.length off c) a := by
      cases c with
      | nil => intro e he; simp [clauseBans] at he
      | cons l rest =>
        intro e he
        simp only [clauseBans, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | he
        · have hu : 2 + ord.length + off < n := by simp at hlen; omega
          have h0 := hst 0 (by simp)
          simp only [Nat.add_zero, allStates, List.flatMap_cons, clauseStates, List.cons_append,
            List.getD_cons_zero] at h0
          rw [ofFn_getD a 0 (by omega), ofFn_getD a _ hu]
          right
          dsimp only
          rw [h0]
          simp only [Bool.false_eq_true, ite_false]
          split <;> omega
        · refine valid_litsBans ord a evalL ha0 hlit (2 + ord.length + off) (l :: rest) false
            (by omega) (by omega) (hmem (l :: rest) (by simp))
            (by simpa using hsat (l :: rest) (by simp)) ?_ e he
          intro k hk
          have hk' := hst k (by simp only [List.flatten_cons, List.length_append]; omega)
          have hlt : k < (clauseStates evalL false (l :: rest)).length := by
            rw [clauseStates_length]; exact hk
          simpa [allStates, List.flatMap_cons, List.getD_eq_getElem?_getD,
            List.getElem?_append_left hlt] using hk'
    have hcsValid : valid n (clausesBans ord ord.length (off + c.length) cs) a := by
      refine ih (off + c.length) (by omega)
        (fun c' hc' => hmem c' (List.mem_cons_of_mem _ hc'))
        (fun c' hc' => hsat c' (List.mem_cons_of_mem _ hc')) ?_
      intro k hk
      have hk' := hst (c.length + k) (by simp only [List.flatten_cons, List.length_append]; omega)
      have hle : (clauseStates evalL false c).length ≤ c.length + k := by
        rw [clauseStates_length]; omega
      have hsub : c.length + k - (clauseStates evalL false c).length = k := by
        rw [clauseStates_length]; omega
      have hfin : (⟨2 + ord.length + (off + c.length) + k, by omega⟩ : Fin n) =
          ⟨2 + ord.length + off + (c.length + k), by omega⟩ := Fin.ext (by dsimp only; omega)
      rw [hfin, hk']
      simp [allStates, List.flatMap_cons, List.getD_eq_getElem?_getD,
        List.getElem?_append_right hle, hsub]
    intro e he
    simp only [clausesBans, List.mem_append] at he
    rcases he with he | he
    · exact hcValid e he
    · exact hcsValid e he

theorem unique_clausesBans {n : Nat} (ord : List Nat) (a : Fin n → Fin 3) (evalL : Literal → Bool)
    (ha0 : ∀ h0 : 0 < n, (a ⟨0, h0⟩).val = 0)
    (hbool : ∀ (i : Nat) (_hi : i < ord.length) (hv : 2 + i < n), (a ⟨2 + i, hv⟩).val < 2)
    (hlit : ∀ l : Literal, l.1 ∈ ord → ∀ hv : 2 + ord.idxOf l.1 < n,
      evalL l = (decide ((a ⟨2 + ord.idxOf l.1, hv⟩).val = 1) == l.2)) :
    ∀ (off : Nat) (cs : CNF) (hlen : 2 + ord.length + off + cs.flatten.length ≤ n),
      (∀ c ∈ cs, ∀ l ∈ c, l.1 ∈ ord) →
      (∀ c ∈ cs, c ≠ []) →
      valid n (clausesBans ord ord.length off cs) a →
      (∀ c ∈ cs, c.any evalL = true) ∧
        ∀ (k : Nat) (hk : k < cs.flatten.length),
          (a ⟨2 + ord.length + off + k, by omega⟩).val = (allStates evalL cs).getD k 3 := by
  intro off cs
  induction cs generalizing off with
  | nil =>
    intro _ _ _ _
    exact ⟨fun c hc => by simp at hc, fun k hk => by simp at hk⟩
  | cons c cs ih =>
    intro hlen hmem hne hval
    simp only [List.flatten_cons, List.length_append] at hlen
    have hvalc : valid n (clauseBans ord ord.length off c) a :=
      fun e he => hval e (by simp [clausesBans, he])
    have hvalcs : valid n (clausesBans ord ord.length (off + c.length) cs) a :=
      fun e he => hval e (by simp [clausesBans, he])
    have hcne : c ≠ [] := hne c (by simp)
    obtain ⟨l, rest, rfl⟩ := List.exists_cons_of_ne_nil hcne
    have hstart : (a ⟨0, by omega⟩).val ≠ 0 ∨ (a ⟨2 + ord.length + off, by simp at hlen; omega⟩).val ≠ 2 :=
      valid_mem hvalc (by simp [clauseBans]) (by omega) (by simp at hlen; omega)
    have hne2 : ∀ hu : 2 + ord.length + off < n, (a ⟨2 + ord.length + off, hu⟩).val ≠ 2 := by
      intro hu
      have h0 := ha0 (by omega)
      omega
    have hvallits : valid n (litsBans ord (2 + ord.length + off) (l :: rest)) a :=
      fun e he => hvalc e (by simp [clauseBans, he])
    obtain ⟨hsatc, hstc⟩ := unique_litsBans ord a evalL ha0 hbool hlit
      (2 + ord.length + off) (l :: rest) false (by omega) (by omega)
      (hmem _ (by simp)) (by simp) hvallits (fun _ => hne2) (fun h => by simp at h)
    obtain ⟨hsatcs, hstcs⟩ := ih (off + (l :: rest).length) (by omega)
      (fun c' hc' => hmem c' (List.mem_cons_of_mem _ hc'))
      (fun c' hc' => hne c' (List.mem_cons_of_mem _ hc')) hvalcs
    refine ⟨?_, ?_⟩
    · intro c' hc'
      simp only [List.mem_cons] at hc'
      rcases hc' with rfl | hc'
      · simpa using hsatc
      · exact hsatcs c' hc'
    · intro k hk
      simp only [List.flatten_cons, List.length_append] at hk
      by_cases hkc : k < (l :: rest).length
      · have hlt : k < (clauseStates evalL false (l :: rest)).length := by
          rw [clauseStates_length]; exact hkc
        rw [hstc k hkc]
        simp [allStates, List.flatMap_cons, List.getD_eq_getElem?_getD,
          List.getElem?_append_left hlt]
      · have hge : (l :: rest).length ≤ k := by omega
        have hlt2 : k - (l :: rest).length < cs.flatten.length := by omega
        have heq : 2 + ord.length + off + k =
            2 + ord.length + (off + (l :: rest).length) + (k - (l :: rest).length) := by omega
        have hle : (clauseStates evalL false (l :: rest)).length ≤ k := by
          rw [clauseStates_length]; exact hge
        have hsub : k - (clauseStates evalL false (l :: rest)).length = k - (l :: rest).length := by
          rw [clauseStates_length]
        have hres := hstcs (k - (l :: rest).length) hlt2
        simp only [← heq] at hres
        rw [hres]
        simp [allStates, List.flatMap_cons, List.getD_eq_getElem?_getD,
          List.getElem?_append_right hle, hsub]

theorem bijection_exists (F : CNF) :
    let occ := F.flatten
    let ord := (occ.map Prod.fst).eraseDups
    let n := ord.length + occ.length + 2
    let Models := {a : Fin ord.length → Bool // ∃ raw : Nat → Bool,
      CNF.eval raw F = true ∧ ∀ i, a i = raw (ord.get i)}
    ∃ E : Models ≃ {a : Fin n → Fin 3 // valid n (makeB F) a},
      ∀ x i (j : Fin n), j.val = 2 + i.val → ((E x).val j).val = (x.val i).toNat := by
  intro occ ord n Models
  by_cases hemp : F.any List.isEmpty = true
  · have hEmptyMod : IsEmpty Models := by
      refine ⟨fun ⟨x, raw, hev, _⟩ => ?_⟩
      obtain ⟨c, hc, hce⟩ := List.any_eq_true.mp hemp
      have hc0 : c = [] := List.isEmpty_iff.mp hce
      subst hc0
      have hceval := List.all_eq_true.mp hev [] hc
      simp [Clause.eval] at hceval
    have hEmptyVal : IsEmpty {a : Fin n → Fin 3 // valid n (makeB F) a} := by
      refine ⟨fun ⟨a, hva⟩ => ?_⟩
      have hanc : (a ⟨0, by omega⟩).val = 0 ∧ (a ⟨1, by omega⟩).val = 0 :=
        valid_anchors (by omega) (fun e he => by simp [makeB, he]) hva
      have hmem : ((0, 0), (1, 0)) ∈ makeB F := by
        simp [makeB, emptyBan, hemp]
      have hcon := valid_mem hva hmem (by omega) (by omega)
      omega
    refine ⟨Equiv.equivOfIsEmpty Models {a : Fin n → Fin 3 // valid n (makeB F) a}, ?_⟩
    intro x
    exact hEmptyMod.elim x
  · have hnoemp : ∀ c ∈ F, c ≠ [] := by
      intro c hc hnil
      apply hemp
      exact List.any_eq_true.mpr ⟨c, hc, by simp [hnil]⟩
    have hmemOrd : ∀ c ∈ F, ∀ l ∈ c, l.1 ∈ ord := by
      intro c hc l hl
      rw [List.mem_eraseDups]
      exact List.mem_map.mpr ⟨l, List.mem_flatten.mpr ⟨c, hc, hl⟩, rfl⟩
    have hn_def : n = ord.length + F.flatten.length + 2 := rfl
    have hocc_def : occ = F.flatten := rfl
    let toVec (x : Fin ord.length → Bool) : List Nat :=
      [0, 0] ++ List.ofFn (fun i => (x i).toNat) ++ allStates (evalLitOrd ord x) F
    have hlenVec : ∀ x, (toVec x).length = n := by
      intro x
      simp only [toVec, List.length_append, List.length_cons, List.length_nil, List.length_ofFn,
        allStates_length]
      omega
    have hltVec : ∀ x (j : Fin n), (toVec x).getD j.val 0 < 3 := by
      intro x j
      have hj : j.val < (toVec x).length := by rw [hlenVec]; exact j.isLt
      have hmem : (toVec x).getD j.val 0 ∈ toVec x := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
        exact List.getElem_mem hj
      simp only [toVec, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
        List.mem_ofFn] at hmem
      rcases hmem with ((h | h) | ⟨i, h⟩) | hst
      · change _ < 3; rw [show (toVec x).getD j.val 0 = 0 from h]; omega
      · change _ < 3; rw [show (toVec x).getD j.val 0 = 0 from h]; omega
      · change _ < 3; rw [show (toVec x).getD j.val 0 = (x i).toNat from h.symm]
        cases x i <;> simp
      · exact allStates_lt _ _ _ hst
    let toA (x : Fin ord.length → Bool) : Fin n → Fin 3 :=
      fun j => ⟨(toVec x).getD j.val 0, hltVec x j⟩
    have htoA0 : ∀ x (h0 : 0 < n), (toA x ⟨0, h0⟩).val = 0 := by
      intro x h0; simp [toA, toVec]
    have htoA1 : ∀ x (h1 : 1 < n), (toA x ⟨1, h1⟩).val = 0 := by
      intro x h1; simp [toA, toVec]
    have htoAvar : ∀ x (i : Fin ord.length) (hv : 2 + i.val < n),
        (toA x ⟨2 + i.val, hv⟩).val = (x i).toNat := by
      intro x i hv
      have h1 : 2 + i.val < ([0, 0] ++ List.ofFn (fun k => (x k).toNat)).length := by
        simp; omega
      simp only [toA, toVec, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left h1]
      rw [List.getElem?_append_right (by simp)]
      simp
    have htoAst : ∀ x (k : Nat) (hk : k < occ.length),
        (toA x ⟨2 + ord.length + k, by omega⟩).val = (allStates (evalLitOrd ord x) F).getD k 3 := by
      intro x k hk
      have hlen1 : ([0, 0] ++ List.ofFn (fun i => (x i).toNat)).length = 2 + ord.length := by
        simp only [List.length_append, List.length_cons, List.length_nil, List.length_ofFn]
      have hlt2 : k < (allStates (evalLitOrd ord x) F).length := by
        rw [allStates_length]; exact hk
      simp only [toA, toVec, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_right (by omega), hlen1]
      have hsub : 2 + ord.length + k - (2 + ord.length) = k := by omega
      rw [hsub, List.getElem?_eq_getElem hlt2]
      rfl
    have htoValid : ∀ x : Models, valid n (makeB F) (toA x.val) := by
      rintro ⟨x, raw, hraw, hagree⟩
      have hsat : ∀ c ∈ F, c.any (evalLitOrd ord x) = true := by
        rw [cnf_eval_eq_ord F x raw hagree] at hraw
        exact List.all_eq_true.mp hraw
      intro e he
      unfold makeB at he
      simp only [List.mem_append] at he
      rcases he with ((he | he) | he) | he
      · simp only [anchorBans, List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        · rw [ofFn_getD _ 0 (by omega), ofFn_getD _ 1 (by omega), htoA0, htoA1]; decide
      · simp [emptyBan, hemp] at he
      · simp only [boolBans, List.mem_map, List.mem_range] at he
        obtain ⟨i, hi, rfl⟩ := he
        have hi' : i < ord.length := hi
        have h2i : 2 + i < n := by omega
        rw [ofFn_getD _ 0 (by omega), ofFn_getD _ (2 + i) h2i,
          htoAvar x ⟨i, hi'⟩ h2i]
        right
        cases x ⟨i, hi'⟩ <;> simp
      · refine valid_clausesBans ord (toA x) (evalLitOrd ord x) (htoA0 x) ?_ 0 F
          (by omega) hmemOrd hsat ?_ e he
        · intro l hl hv
          have hi : ord.idxOf l.1 < ord.length := List.idxOf_lt_length_of_mem hl
          rw [htoAvar x ⟨ord.idxOf l.1, hi⟩ hv]
          unfold evalLitOrd
          simp only [hi, dite_true]
          cases x ⟨ord.idxOf l.1, hi⟩ <;> cases l.2 <;> simp
        · intro k hk
          simpa using htoAst x k hk
    let invX (a : Fin n → Fin 3) : Fin ord.length → Bool :=
      fun i => decide ((a ⟨2 + i.val, by omega⟩).val = 1)
    have hinvValid : ∀ a : {a : Fin n → Fin 3 // valid n (makeB F) a},
        ∃ raw : Nat → Bool, CNF.eval raw F = true ∧ ∀ i, invX a.val i = raw (ord.get i) := by
      rintro ⟨a, hva⟩
      have hanc : (a ⟨0, by omega⟩).val = 0 ∧ (a ⟨1, by omega⟩).val = 0 :=
        valid_anchors (by omega) (fun e he => by simp only [makeB, List.mem_append]; left; left; left; exact he) hva
      have hbool : ∀ (i : Nat) (hi : i < ord.length) (hv : 2 + i < n), (a ⟨2 + i, hv⟩).val < 2 := by
        intro i hi hv
        have hmem : ((0, 0), (2 + i, 2)) ∈ makeB F := by
          simp only [makeB, List.mem_append, boolBans, List.mem_map, List.mem_range]
          left; right; exact ⟨i, hi, rfl⟩
        have hb := valid_mem hva hmem (by omega) hv
        have hlt := (a ⟨2 + i, hv⟩).isLt
        omega
      have hlit : ∀ l : Literal, l.1 ∈ ord → ∀ hv : 2 + ord.idxOf l.1 < n,
          evalLitOrd ord (invX a) l = (decide ((a ⟨2 + ord.idxOf l.1, hv⟩).val = 1) == l.2) := by
        intro l hl hv
        have hi : ord.idxOf l.1 < ord.length := List.idxOf_lt_length_of_mem hl
        simp [evalLitOrd, invX, hi]
      have hvalcl : valid n (clausesBans ord ord.length 0 F) a :=
        fun e he => hva e (by simp only [makeB, List.mem_append]; right; exact he)
      obtain ⟨hsat, _⟩ := unique_clausesBans ord a (evalLitOrd ord (invX a))
        (fun _ => hanc.1) hbool hlit 0 F (by omega) hmemOrd hnoemp hvalcl
      refine ⟨toRaw ord (invX a), ?_, ?_⟩
      · rw [cnf_eval_eq_ord F (invX a) (toRaw ord (invX a))
          (fun i => (toRaw_get ord (nodup_eraseDups _) (invX a) i).symm)]
        exact List.all_eq_true.mpr hsat
      · intro i
        exact (toRaw_get ord (nodup_eraseDups _) (invX a) i).symm
    let E : Models ≃ {a : Fin n → Fin 3 // valid n (makeB F) a} :=
      { toFun := fun x => ⟨toA x.val, htoValid x⟩
        invFun := fun a => ⟨invX a.val, hinvValid a⟩
        left_inv := by
          rintro ⟨x, _⟩
          apply Subtype.ext
          funext i
          simp only [invX]
          rw [htoAvar x i (by omega)]
          cases x i <;> simp
        right_inv := by
          rintro ⟨a, hva⟩
          apply Subtype.ext
          funext j
          apply Fin.ext
          have hanc : (a ⟨0, by omega⟩).val = 0 ∧ (a ⟨1, by omega⟩).val = 0 :=
            valid_anchors (by omega) (fun e he => by simp only [makeB, List.mem_append]; left; left; left; exact he) hva
          have hbool : ∀ (i : Nat) (hi : i < ord.length) (hv : 2 + i < n), (a ⟨2 + i, hv⟩).val < 2 := by
            intro i hi hv
            have hmem : ((0, 0), (2 + i, 2)) ∈ makeB F := by
              simp only [makeB, List.mem_append, boolBans, List.mem_map, List.mem_range]
              left; right; exact ⟨i, hi, rfl⟩
            have hb := valid_mem hva hmem (by omega) hv
            have hlt := (a ⟨2 + i, hv⟩).isLt
            omega
          by_cases hj0 : j.val = 0
          · have hjeq : j = ⟨0, by omega⟩ := Fin.ext hj0
            rw [hjeq]; exact (htoA0 (invX a) (by omega)).trans hanc.1.symm
          · by_cases hj1 : j.val = 1
            · have hjeq : j = ⟨1, by omega⟩ := Fin.ext hj1
              rw [hjeq]; exact (htoA1 (invX a) (by omega)).trans hanc.2.symm
            · by_cases hjv : j.val < 2 + ord.length
              · have hi : j.val - 2 < ord.length := by omega
                have h2i : 2 + (j.val - 2) < n := by omega
                have hj : j = ⟨2 + (j.val - 2), h2i⟩ := Fin.ext (by dsimp only; omega)
                rw [hj, htoAvar (invX a) ⟨j.val - 2, hi⟩ h2i]
                simp only [invX]
                have hb := hbool (j.val - 2) hi h2i
                cases hvalv : (a ⟨2 + (j.val - 2), h2i⟩).val with
                | zero => simp
                | succ m =>
                  have hm : m = 0 := by omega
                  subst hm; simp
              · have hk : j.val - (2 + ord.length) < occ.length := by omega
                have h2k : 2 + ord.length + (j.val - (2 + ord.length)) < n := by omega
                have hj : j = ⟨2 + ord.length + (j.val - (2 + ord.length)), h2k⟩ :=
                  Fin.ext (by dsimp only; omega)
                have hlit : ∀ l : Literal, l.1 ∈ ord → ∀ hv : 2 + ord.idxOf l.1 < n,
                    evalLitOrd ord (invX a) l = (decide ((a ⟨2 + ord.idxOf l.1, hv⟩).val = 1) == l.2) := by
                  intro l hl hv
                  have hi : ord.idxOf l.1 < ord.length := List.idxOf_lt_length_of_mem hl
                  simp [evalLitOrd, invX, hi]
                have hvalcl : valid n (clausesBans ord ord.length 0 F) a :=
                  fun e he => hva e (by simp only [makeB, List.mem_append]; right; exact he)
                obtain ⟨_, hst⟩ := unique_clausesBans ord a (evalLitOrd ord (invX a))
                  (fun _ => hanc.1) hbool hlit 0 F (by omega) hmemOrd hnoemp hvalcl
                have hst' := hst (j.val - (2 + ord.length)) hk
                simp only [Nat.add_zero] at hst'
                rw [hj, htoAst (invX a) (j.val - (2 + ord.length)) hk, ← hst'] }
    refine ⟨E, ?_⟩
    intro x i j hj
    have heq : j = ⟨2 + i.val, by omega⟩ := Fin.ext hj
    rw [heq]
    exact htoAvar x.val i (by omega)

end Part1

section GenericProg

open Turing

variable {K : Type} [DecidableEq K] {Γ : K → Type} {σ : Type}

inductive Prog (K : Type) (Γ : K → Type) (σ : Type) : Type
  | push (k : K) (f : σ → Γ k) : Prog K Γ σ
  | pop (k : K) (f : σ → Option (Γ k) → σ) : Prog K Γ σ
  | load (f : σ → σ) : Prog K Γ σ
  | seq (p q : Prog K Γ σ) : Prog K Γ σ
  | ite (c : σ → Bool) (p q : Prog K Γ σ) : Prog K Γ σ
  | loop (k : K) (f : σ → Option (Γ k) → σ) (c : σ → Bool) (b : Prog K Γ σ) : Prog K Γ σ

structure St (K : Type) (Γ : K → Type) (σ : Type) where
  var : σ
  stk : ∀ k, List (Γ k)

def loopExec (k : K) (f : σ → Option (Γ k) → σ) (c : σ → Bool) (body : St K Γ σ → St K Γ σ) :
    List (Γ k) → St K Γ σ → St K Γ σ
  | [], s => ⟨f s.var none, Function.update s.stk k []⟩
  | x :: l, s =>
    if c (f s.var (some x)) then
      loopExec k f c body l (body ⟨f s.var (some x), Function.update s.stk k l⟩)
    else ⟨f s.var (some x), Function.update s.stk k l⟩

def exec : Prog K Γ σ → St K Γ σ → St K Γ σ
  | .push k f, s => ⟨s.var, Function.update s.stk k (f s.var :: s.stk k)⟩
  | .pop k f, s => ⟨f s.var (s.stk k).head?, Function.update s.stk k (s.stk k).tail⟩
  | .load f, s => ⟨f s.var, s.stk⟩
  | .seq p q, s => exec q (exec p s)
  | .ite c p q, s => if c s.var then exec p s else exec q s
  | .loop k f c b, s => loopExec k f c (exec b) (s.stk k) s

def loopCost (k : K) (f : σ → Option (Γ k) → σ) (c : σ → Bool) (body : St K Γ σ → St K Γ σ)
    (bc : St K Γ σ → Nat) : List (Γ k) → St K Γ σ → Nat
  | [], _ => 1
  | x :: l, s =>
    if c (f s.var (some x)) then
      loopCost k f c body bc l (body ⟨f s.var (some x), Function.update s.stk k l⟩) +
        (bc ⟨f s.var (some x), Function.update s.stk k l⟩ + 1)
    else 1

def cost : Prog K Γ σ → St K Γ σ → Nat
  | .push _ _, _ => 1
  | .pop _ _, _ => 1
  | .load _, _ => 1
  | .seq p q, s => cost q (exec p s) + cost p s
  | .ite c p q, s => (if c s.var then cost p s else cost q s) + 1
  | .loop k f c b, s => loopCost k f c (exec b) (cost b) (s.stk k) s

def NoTouch (k : K) : Prog K Γ σ → Prop
  | .push k' _ => k' ≠ k
  | .pop k' _ => k' ≠ k
  | .load _ => True
  | .seq p q => NoTouch k p ∧ NoTouch k q
  | .ite _ p q => NoTouch k p ∧ NoTouch k q
  | .loop k' _ _ b => k' ≠ k ∧ NoTouch k b

def WF : Prog K Γ σ → Prop
  | .push _ _ => True
  | .pop _ _ => True
  | .load _ => True
  | .seq p q => WF p ∧ WF q
  | .ite _ p q => WF p ∧ WF q
  | .loop k f c b => (∀ v, c (f v none) = false) ∧ NoTouch k b ∧ WF b

def Pos : Prog K Γ σ → Type
  | .push _ _ => Unit
  | .pop _ _ => Unit
  | .load _ => Unit
  | .seq p q => Pos p ⊕ Pos q
  | .ite _ p q => Option (Pos p ⊕ Pos q)
  | .loop _ _ _ b => Option (Pos b)

def entry : (p : Prog K Γ σ) → Pos p
  | .push _ _ => ()
  | .pop _ _ => ()
  | .load _ => ()
  | .seq p _ => Sum.inl (entry p)
  | .ite _ _ _ => none
  | .loop _ _ _ _ => none

instance posFintype : (p : Prog K Γ σ) → Fintype (Pos p)
  | .push _ _ => inferInstanceAs (Fintype Unit)
  | .pop _ _ => inferInstanceAs (Fintype Unit)
  | .load _ => inferInstanceAs (Fintype Unit)
  | .seq p q => @instFintypeSum _ _ (posFintype p) (posFintype q)
  | .ite _ p q => @instFintypeOption _ (@instFintypeSum _ _ (posFintype p) (posFintype q))
  | .loop _ _ _ b => @instFintypeOption _ (posFintype b)

def stmt {Λ : Type} : (p : Prog K Γ σ) → (Pos p → Λ) → Λ → Pos p → TM2.Stmt Γ Λ σ
  | .push k f, _, cont, _ => .push k f (.goto fun _ => cont)
  | .pop k f, _, cont, _ => .pop k f (.goto fun _ => cont)
  | .load f, _, cont, _ => .load f (.goto fun _ => cont)
  | .seq p q, inj, cont, a =>
    match a with
    | Sum.inl a => stmt p (fun x => inj (Sum.inl x)) (inj (Sum.inr (entry q))) a
    | Sum.inr b => stmt q (fun x => inj (Sum.inr x)) cont b
  | .ite c p q, inj, cont, a =>
    match a with
    | none => .branch c (.goto fun _ => inj (some (Sum.inl (entry p))))
        (.goto fun _ => inj (some (Sum.inr (entry q))))
    | some (Sum.inl a) => stmt p (fun x => inj (some (Sum.inl x))) cont a
    | some (Sum.inr b) => stmt q (fun x => inj (some (Sum.inr x))) cont b
  | .loop k f c b, inj, cont, a =>
    match a with
    | none => .pop k f (.branch c (.goto fun _ => inj (some (entry b))) (.goto fun _ => cont))
    | some a => stmt b (fun x => inj (some x)) (inj none) a

theorem noTouch_exec (k : K) (p : Prog K Γ σ) (h : NoTouch k p) (s : St K Γ σ) :
    (exec p s).stk k = s.stk k := by
  induction p generalizing s with
  | push k' f => simp only [exec]; exact Function.update_of_ne (Ne.symm h) _ _
  | pop k' f => simp only [exec]; exact Function.update_of_ne (Ne.symm h) _ _
  | load f => rfl
  | seq p q ihp ihq => simp only [exec]; rw [ihq h.2, ihp h.1]
  | ite c p q ihp ihq =>
    simp only [exec]
    split
    · exact ihp h.1 s
    · exact ihq h.2 s
  | loop k' f c b ih =>
    simp only [exec]
    generalize s.stk k' = l
    induction l generalizing s with
    | nil => simp only [loopExec]; exact Function.update_of_ne (Ne.symm h.1) _ _
    | cons x l ihl =>
      simp only [loopExec]
      split
      · rw [ihl, ih h.2]; exact Function.update_of_ne (Ne.symm h.1) _ _
      · exact Function.update_of_ne (Ne.symm h.1) _ _

theorem exec_loop_nil (k : K) (f : σ → Option (Γ k) → σ) (c : σ → Bool) (b : Prog K Γ σ)
    (s : St K Γ σ) (h : s.stk k = []) :
    exec (Prog.loop k f c b) s = ⟨f s.var none, Function.update s.stk k []⟩ := by
  simp only [exec, h, loopExec]

theorem cost_loop_nil (k : K) (f : σ → Option (Γ k) → σ) (c : σ → Bool) (b : Prog K Γ σ)
    (s : St K Γ σ) (h : s.stk k = []) :
    cost (Prog.loop k f c b) s = 1 := by
  simp only [cost, h, loopCost]

theorem exec_loop_cons (k : K) (f : σ → Option (Γ k) → σ) (c : σ → Bool) (b : Prog K Γ σ)
    (s : St K Γ σ) (x : Γ k) (l : List (Γ k)) (h : s.stk k = x :: l)
    (hc : c (f s.var (some x)) = true) (hnt : NoTouch k b) :
    exec (Prog.loop k f c b) s =
      exec (Prog.loop k f c b) (exec b ⟨f s.var (some x), Function.update s.stk k l⟩) := by
  have hk : (exec b ⟨f s.var (some x), Function.update s.stk k l⟩).stk k = l := by
    rw [noTouch_exec k b hnt]; simp
  conv_lhs => simp only [exec, h, loopExec, hc, ite_true]
  simp only [exec, hk]

theorem cost_loop_cons (k : K) (f : σ → Option (Γ k) → σ) (c : σ → Bool) (b : Prog K Γ σ)
    (s : St K Γ σ) (x : Γ k) (l : List (Γ k)) (h : s.stk k = x :: l)
    (hc : c (f s.var (some x)) = true) (hnt : NoTouch k b) :
    cost (Prog.loop k f c b) s =
      cost (Prog.loop k f c b) (exec b ⟨f s.var (some x), Function.update s.stk k l⟩) +
        (cost b ⟨f s.var (some x), Function.update s.stk k l⟩ + 1) := by
  have hk : (exec b ⟨f s.var (some x), Function.update s.stk k l⟩).stk k = l := by
    rw [noTouch_exec k b hnt]; simp
  conv_lhs => simp only [cost, h, loopCost, hc, ite_true]
  simp only [cost, hk]

theorem iter_add {α : Type} (f : α → Option α) (m n : Nat) (a b : α) (c : Option α)
    (h1 : (flip bind f)^[n] (some a) = some b) (h2 : (flip bind f)^[m] (some b) = c) :
    (flip bind f)^[m + n] (some a) = c := by
  rw [Function.iterate_add_apply, h1, h2]

theorem one_step {Λ : Type} (M : Λ → TM2.Stmt Γ Λ σ) (l : Λ) (v : σ) (S : ∀ k, List (Γ k))
    (q : TM2.Stmt Γ Λ σ) (c : TM2.Cfg Γ Λ σ) (hq : M l = q) (hc : TM2.stepAux q v S = c) :
    (flip bind (TM2.step M))^[1] (some ⟨some l, v, S⟩) = some c := by
  subst hq hc; rfl

theorem compile_correct {Λ : Type} (M : Λ → TM2.Stmt Γ Λ σ) (p : Prog K Γ σ) (hwf : WF p) :
    ∀ (inj : Pos p → Λ) (cont : Λ), (∀ a, M (inj a) = stmt p inj cont a) → ∀ s : St K Γ σ,
    (flip bind (TM2.step M))^[cost p s] (some ⟨some (inj (entry p)), s.var, s.stk⟩) =
      some ⟨some cont, (exec p s).var, (exec p s).stk⟩ := by
  induction p with
  | push k f =>
    intro inj cont hM s
    exact one_step M _ _ _ _ _ (hM ()) rfl
  | pop k f =>
    intro inj cont hM s
    exact one_step M _ _ _ _ _ (hM ()) rfl
  | load f =>
    intro inj cont hM s
    exact one_step M _ _ _ _ _ (hM ()) rfl
  | seq p q ihp ihq =>
    intro inj cont hM s
    have h1 := ihp hwf.1 (fun x => inj (Sum.inl x)) (inj (Sum.inr (entry q)))
      (fun a => hM (Sum.inl a)) s
    have h2 := ihq hwf.2 (fun x => inj (Sum.inr x)) cont (fun a => hM (Sum.inr a)) (exec p s)
    exact iter_add _ _ _ _ _ _ h1 h2
  | ite c p q ihp ihq =>
    intro inj cont hM s
    have h0 := hM none
    by_cases hc : c s.var = true
    · have e1 : cost (Prog.ite c p q) s = cost p s + 1 := by simp [cost, hc]
      have e2 : exec (Prog.ite c p q) s = exec p s := by simp [exec, hc]
      rw [e1, e2]
      refine iter_add _ _ 1 _ _ _ ?_
        (ihp hwf.1 (fun x => inj (some (Sum.inl x))) cont (fun a => hM (some (Sum.inl a))) s)
      refine one_step M _ _ _ _ _ h0 ?_
      simp [stmt, TM2.stepAux, hc]
    · have e1 : cost (Prog.ite c p q) s = cost q s + 1 := by simp [cost, hc]
      have e2 : exec (Prog.ite c p q) s = exec q s := by simp [exec, hc]
      rw [e1, e2]
      refine iter_add _ _ 1 _ _ _ ?_
        (ihq hwf.2 (fun x => inj (some (Sum.inr x))) cont (fun a => hM (some (Sum.inr a))) s)
      refine one_step M _ _ _ _ _ h0 ?_
      simp [stmt, TM2.stepAux, hc]
  | loop k f c b ih =>
    intro inj cont hM s
    have h0 := hM none
    have key : ∀ (l : List (Γ k)) (s : St K Γ σ), s.stk k = l →
        (flip bind (TM2.step M))^[loopCost k f c (exec b) (cost b) l s]
          (some ⟨some (inj none), s.var, s.stk⟩) =
        some ⟨some cont, (loopExec k f c (exec b) l s).var,
          (loopExec k f c (exec b) l s).stk⟩ := by
      intro l
      induction l with
      | nil =>
        intro s hl
        refine one_step M _ _ _ _ _ h0 ?_
        simp [stmt, TM2.stepAux, hl, hwf.1, loopExec]
      | cons x l ihl =>
        intro s hl
        by_cases hc : c (f s.var (some x)) = true
        · have e1 : loopCost k f c (exec b) (cost b) (x :: l) s =
              loopCost k f c (exec b) (cost b) l
                (exec b ⟨f s.var (some x), Function.update s.stk k l⟩) +
              (cost b ⟨f s.var (some x), Function.update s.stk k l⟩ + 1) := by
            simp [loopCost, hc]
          have e2 : loopExec k f c (exec b) (x :: l) s =
              loopExec k f c (exec b) l
                (exec b ⟨f s.var (some x), Function.update s.stk k l⟩) := by
            simp [loopExec, hc]
          rw [e1, e2]
          have hb := ih hwf.2.2 (fun x => inj (some x)) (inj none) (fun a => hM (some a))
            ⟨f s.var (some x), Function.update s.stk k l⟩
          have hk : (exec b ⟨f s.var (some x), Function.update s.stk k l⟩).stk k = l := by
            rw [noTouch_exec k b hwf.2.1]; simp
          have hrest := ihl (exec b ⟨f s.var (some x), Function.update s.stk k l⟩) hk
          refine iter_add _ _ _ _ _ _ (iter_add _ _ 1 _ _ _ ?_ hb) hrest
          refine one_step M _ _ _ _ _ h0 ?_
          simp [stmt, TM2.stepAux, hl, hc]
        · have e1 : loopCost k f c (exec b) (cost b) (x :: l) s = 1 := by
            simp [loopCost, hc]
          have e2 : loopExec k f c (exec b) (x :: l) s =
              ⟨f s.var (some x), Function.update s.stk k l⟩ := by
            simp [loopExec, hc]
          rw [e1, e2]
          refine one_step M _ _ _ _ _ h0 ?_
          simp [stmt, TM2.stepAux, hl, hc]
    exact key (s.stk k) s rfl

end GenericProg

section MachineDefs

open Turing

inductive W : Type
  | X | Xrev | Mstk | Vstk | Nstk | Nb | Wstk | Wb | Q | Qb
  | Drev | CurV | CurVb | SeenV | SeenVb | Vidx | Uocc | Tmp | OutRev
  deriving DecidableEq

instance : Fintype W :=
  Fintype.ofList [.X, .Xrev, .Mstk, .Vstk, .Nstk, .Nb, .Wstk, .Wb, .Q, .Qb,
    .Drev, .CurV, .CurVb, .SeenV, .SeenVb, .Vidx, .Uocc, .Tmp, .OutRev]
    (by intro a; cases a <;> simp)

inductive K : Type
  | inp | out | w (a : W)
  deriving DecidableEq

noncomputable instance : Fintype K :=
  Fintype.ofInjective
    (fun k : K => match k with
      | .inp => (none : Option (Option W))
      | .out => some none
      | .w a => some (some a))
    (by intro a b h; cases a <;> cases b <;> simp_all)

def Γ : K → Type := fun _ => Bool

structure Reg where
  go : Bool
  u : Bool
  b0 : Bool
  half : Bool
  inLit : Bool
  inClause : Bool
  pol : Bool
  ws : WS
  hasEmpty : Bool
  expectData : Bool
  eqFlag : Bool
  found : Bool
  par : Bool
  deriving DecidableEq

noncomputable instance : Fintype Reg :=
  Fintype.ofInjective
    (fun r : Reg => (r.go, r.u, r.b0, r.half, r.inLit, r.inClause, r.pol,
      r.ws, r.hasEmpty, r.expectData, r.eqFlag, r.found, r.par))
    (by intro a b h; cases a; cases b; simp_all)

def regInit : Reg :=
  { go := false, u := false, b0 := false, half := false, inLit := false,
    inClause := false, pol := false, ws := .a, hasEmpty := false,
    expectData := false, eqFlag := false, found := false, par := false }

def nrm (v : Reg) : Reg := { v with go := false, u := false }

theorem nrm_nrm (v : Reg) : nrm (nrm v) = nrm v := by
  cases v; rfl

structure Stk where
  inp : List Bool
  out : List Bool
  X : List Bool
  Xrev : List Bool
  Mstk : List Bool
  Vstk : List Bool
  Nstk : List Bool
  Nb : List Bool
  Wstk : List Bool
  Wb : List Bool
  Q : List Bool
  Qb : List Bool
  Drev : List Bool
  CurV : List Bool
  CurVb : List Bool
  SeenV : List Bool
  SeenVb : List Bool
  Vidx : List Bool
  Uocc : List Bool
  Tmp : List Bool
  OutRev : List Bool

def Stk.get (s : Stk) : W → List Bool
  | .X => s.X
  | .Xrev => s.Xrev
  | .Mstk => s.Mstk
  | .Vstk => s.Vstk
  | .Nstk => s.Nstk
  | .Nb => s.Nb
  | .Wstk => s.Wstk
  | .Wb => s.Wb
  | .Q => s.Q
  | .Qb => s.Qb
  | .Drev => s.Drev
  | .CurV => s.CurV
  | .CurVb => s.CurVb
  | .SeenV => s.SeenV
  | .SeenVb => s.SeenVb
  | .Vidx => s.Vidx
  | .Uocc => s.Uocc
  | .Tmp => s.Tmp
  | .OutRev => s.OutRev

def Stk.set (s : Stk) : W → List Bool → Stk
  | .X, l => { s with X := l }
  | .Xrev, l => { s with Xrev := l }
  | .Mstk, l => { s with Mstk := l }
  | .Vstk, l => { s with Vstk := l }
  | .Nstk, l => { s with Nstk := l }
  | .Nb, l => { s with Nb := l }
  | .Wstk, l => { s with Wstk := l }
  | .Wb, l => { s with Wb := l }
  | .Q, l => { s with Q := l }
  | .Qb, l => { s with Qb := l }
  | .Drev, l => { s with Drev := l }
  | .CurV, l => { s with CurV := l }
  | .CurVb, l => { s with CurVb := l }
  | .SeenV, l => { s with SeenV := l }
  | .SeenVb, l => { s with SeenVb := l }
  | .Vidx, l => { s with Vidx := l }
  | .Uocc, l => { s with Uocc := l }
  | .Tmp, l => { s with Tmp := l }
  | .OutRev, l => { s with OutRev := l }

def toFun (s : Stk) : ∀ k, List (Γ k)
  | .inp => s.inp
  | .out => s.out
  | .w a => s.get a

def emp : Stk :=
  { inp := [], out := [], X := [], Xrev := [], Mstk := [], Vstk := [], Nstk := [], Nb := [],
    Wstk := [], Wb := [], Q := [], Qb := [], Drev := [], CurV := [], CurVb := [],
    SeenV := [], SeenVb := [], Vidx := [], Uocc := [], Tmp := [], OutRev := [] }

theorem get_set (s : Stk) (a b : W) (l : List Bool) :
    (s.set a l).get b = if b = a then l else s.get b := by
  cases a <;> cases b <;> rfl

theorem get_set_self (s : Stk) (a : W) (l : List Bool) : (s.set a l).get a = l := by
  rw [get_set]; simp

theorem get_set_ne (s : Stk) (a b : W) (l : List Bool) (h : b ≠ a) :
    (s.set a l).get b = s.get b := by
  rw [get_set]; simp [h]

theorem set_inp (s : Stk) (a : W) (l : List Bool) : (s.set a l).inp = s.inp := by
  cases a <;> rfl

theorem set_out (s : Stk) (a : W) (l : List Bool) : (s.set a l).out = s.out := by
  cases a <;> rfl

theorem Stk.ext_get (s s' : Stk) (hi : s.inp = s'.inp) (ho : s.out = s'.out)
    (h : ∀ a, s.get a = s'.get a) : s = s' := by
  cases s
  cases s'
  simp only [Stk.mk.injEq]
  exact ⟨hi, ho, h .X, h .Xrev, h .Mstk, h .Vstk, h .Nstk, h .Nb, h .Wstk, h .Wb, h .Q, h .Qb,
    h .Drev, h .CurV, h .CurVb, h .SeenV, h .SeenVb, h .Vidx, h .Uocc, h .Tmp, h .OutRev⟩

theorem set_set (s : Stk) (a : W) (l l' : List Bool) : (s.set a l).set a l' = s.set a l' := by
  apply Stk.ext_get
  · simp only [set_inp]
  · simp only [set_out]
  · intro b; simp only [get_set]; split <;> rfl

theorem set_get_self (s : Stk) (a : W) : s.set a (s.get a) = s := by
  apply Stk.ext_get
  · simp only [set_inp]
  · simp only [set_out]
  · intro b
    simp only [get_set]
    split
    · next h => rw [h]
    · rfl

theorem update_toFun (s : Stk) (a : W) (l : List Bool) :
    Function.update (toFun s) (K.w a) l = toFun (s.set a l) := by
  funext k
  cases k with
  | inp => simp [Function.update, toFun, set_inp]; rfl
  | out => simp [Function.update, toFun, set_out]; rfl
  | w b =>
    by_cases h : b = a
    · subst h; simp [Function.update, toFun, get_set_self]; rfl
    · simp [Function.update, toFun, get_set_ne _ _ _ _ h, h]; rfl

theorem update_toFun_inp (s : Stk) (l : List Bool) :
    Function.update (toFun s) K.inp l = toFun { s with inp := l } := by
  funext k
  cases k with
  | inp => simp [Function.update, toFun]; rfl
  | out => simp [Function.update, toFun]; rfl
  | w b => simp only [Function.update, toFun, reduceCtorEq]; cases b <;> rfl

theorem update_toFun_out (s : Stk) (l : List Bool) :
    Function.update (toFun s) K.out l = toFun { s with out := l } := by
  funext k
  cases k with
  | inp => simp [Function.update, toFun]; rfl
  | out => simp [Function.update, toFun]; rfl
  | w b => simp only [Function.update, toFun, reduceCtorEq]; cases b <;> rfl

theorem toFun_emp : toFun emp = fun _ => [] := by
  funext k
  cases k with
  | inp => rfl
  | out => rfl
  | w a => cases a <;> rfl

abbrev Pg := Prog K Γ Reg

def tt : Reg → Bool := fun _ => true

def ff : Reg → Bool := fun _ => false

def wpush (a : W) (f : Reg → Bool) : Pg := Prog.push (K.w a) f

def wpop (a : W) (f : Reg → Option Bool → Reg) : Pg := Prog.pop (K.w a) f

def popF (f : Reg → Bool → Reg) (g : Reg → Reg) (v : Reg) : Option Bool → Reg
  | some b => { f v b with go := true }
  | none => nrm (g v)

def forPop (a : W) (f : Reg → Bool → Reg) (g : Reg → Reg) (body : Pg) : Pg :=
  Prog.loop (K.w a) (popF f g) (fun v => v.go) body

def move (a b : W) : Pg :=
  forPop a (fun v c => { v with u := c }) id (wpush b (fun v => v.u))

def moveOut : Pg :=
  forPop .OutRev (fun v c => { v with u := c }) id (Prog.push K.out (fun v => v.u))

def drain (a : W) : Pg := forPop a (fun v _ => v) id (Prog.load id)

def forC (c cb : W) (body : Pg) : Pg :=
  Prog.seq (forPop c (fun v _ => v) id (Prog.seq (wpush cb tt) body)) (move cb c)

def copyS (a tmp dst : W) : Pg :=
  Prog.seq
    (forPop a (fun v c => { v with u := c }) id
      (Prog.seq (wpush tmp (fun v => v.u)) (wpush dst (fun v => v.u))))
    (move tmp a)

def Run (p : Pg) (v : Reg) (s : Stk) (v' : Reg) (s' : Stk) (B : Nat) : Prop :=
  exec p ⟨v, toFun s⟩ = ⟨v', toFun s'⟩ ∧ cost p ⟨v, toFun s⟩ ≤ B

theorem St_eq (v v' : Reg) (s s' : Stk) (hv : v = v') (hs : s = s') :
    (⟨v, toFun s⟩ : St K Γ Reg) = ⟨v', toFun s'⟩ := by
  subst hv hs; rfl

theorem exec_wpush (a : W) (f : Reg → Bool) (v : Reg) (s : Stk) :
    exec (wpush a f) ⟨v, toFun s⟩ = ⟨v, toFun (s.set a (f v :: s.get a))⟩ :=
  congrArg (St.mk v) (update_toFun s a (f v :: s.get a))

theorem exec_wpop (a : W) (f : Reg → Option Bool → Reg) (v : Reg) (s : Stk) :
    exec (wpop a f) ⟨v, toFun s⟩ = ⟨f v (s.get a).head?, toFun (s.set a (s.get a).tail)⟩ :=
  congrArg (St.mk (f v (s.get a).head?)) (update_toFun s a (s.get a).tail)

theorem exec_outpush (f : Reg → Bool) (v : Reg) (s : Stk) :
    exec (Prog.push K.out f) ⟨v, toFun s⟩ = ⟨v, toFun { s with out := f v :: s.out }⟩ :=
  congrArg (St.mk v) (update_toFun_out s (f v :: s.out))

theorem exec_forPop_nil (a : W) (f : Reg → Bool → Reg) (g : Reg → Reg) (body : Pg) (v : Reg)
    (s : Stk) (h : s.get a = []) :
    exec (forPop a f g body) ⟨v, toFun s⟩ = ⟨nrm (g v), toFun s⟩ := by
  have e := exec_loop_nil (K.w a) (popF f g) (fun v => v.go) body ⟨v, toFun s⟩ h
  refine e.trans (congrArg (St.mk (nrm (g v))) ?_)
  refine (update_toFun s a []).trans ?_
  rw [← h, set_get_self]

theorem cost_forPop_nil (a : W) (f : Reg → Bool → Reg) (g : Reg → Reg) (body : Pg) (v : Reg)
    (s : Stk) (h : s.get a = []) :
    cost (forPop a f g body) ⟨v, toFun s⟩ = 1 := by
  rw [forPop]
  exact cost_loop_nil (K.w a) (popF f g) (fun v => v.go) body ⟨v, toFun s⟩ h

theorem exec_forPop_cons (a : W) (f : Reg → Bool → Reg) (g : Reg → Reg) (body : Pg) (v : Reg)
    (s : Stk) (x : Bool) (l : List Bool) (h : s.get a = x :: l) (hnt : NoTouch (K.w a) body) :
    exec (forPop a f g body) ⟨v, toFun s⟩ =
      exec (forPop a f g body) (exec body ⟨{ f v x with go := true }, toFun (s.set a l)⟩) := by
  have e := exec_loop_cons (K.w a) (popF f g) (fun v => v.go) body ⟨v, toFun s⟩ x l h rfl hnt
  refine e.trans ?_
  exact congrArg (fun S => exec (forPop a f g body) (exec body ⟨{ f v x with go := true }, S⟩))
    (update_toFun s a l)

theorem cost_forPop_cons (a : W) (f : Reg → Bool → Reg) (g : Reg → Reg) (body : Pg) (v : Reg)
    (s : Stk) (x : Bool) (l : List Bool) (h : s.get a = x :: l) (hnt : NoTouch (K.w a) body) :
    cost (forPop a f g body) ⟨v, toFun s⟩ =
      cost (forPop a f g body) (exec body ⟨{ f v x with go := true }, toFun (s.set a l)⟩) +
        (cost body ⟨{ f v x with go := true }, toFun (s.set a l)⟩ + 1) := by
  have e := cost_loop_cons (K.w a) (popF f g) (fun v => v.go) body ⟨v, toFun s⟩ x l h rfl hnt
  refine e.trans ?_
  exact congrArg (fun S => cost (forPop a f g body) (exec body ⟨{ f v x with go := true }, S⟩) +
    (cost body ⟨{ f v x with go := true }, S⟩ + 1)) (update_toFun s a l)

theorem Run.conv {p : Pg} {v v' v'' : Reg} {s s' s'' : Stk} {B B' : Nat}
    (h : Run p v s v' s' B) (hv : v' = v'') (hs : s' = s'') (hB : B ≤ B') :
    Run p v s v'' s'' B' := by
  subst hv hs
  exact ⟨h.1, le_trans h.2 hB⟩

theorem Run.seq {p q : Pg} {v v1 v2 : Reg} {s s1 s2 : Stk} {B1 B2 : Nat}
    (h1 : Run p v s v1 s1 B1) (h2 : Run q v1 s1 v2 s2 B2) :
    Run (Prog.seq p q) v s v2 s2 (B1 + B2) := by
  refine ⟨?_, ?_⟩
  · simp only [exec, h1.1, h2.1]
  · simp only [cost, h1.1]
    have := h1.2
    have := h2.2
    omega

theorem Run.load (f : Reg → Reg) (v : Reg) (s : Stk) :
    Run (Prog.load f) v s (f v) s 1 := ⟨rfl, le_refl _⟩

theorem Run.wpush (a : W) (f : Reg → Bool) (v : Reg) (s : Stk) :
    Run (wpush a f) v s v (s.set a (f v :: s.get a)) 1 :=
  ⟨exec_wpush a f v s, le_refl _⟩

theorem Run.wpop (a : W) (f : Reg → Option Bool → Reg) (v : Reg) (s : Stk) :
    Run (wpop a f) v s (f v (s.get a).head?) (s.set a (s.get a).tail) 1 :=
  ⟨exec_wpop a f v s, le_refl _⟩

theorem Run.ite_true {c : Reg → Bool} {p q : Pg} {v v' : Reg} {s s' : Stk} {B : Nat}
    (hc : c v = true) (hp : Run p v s v' s' B) :
    Run (Prog.ite c p q) v s v' s' (B + 1) := by
  refine ⟨by simp [exec, hc, hp.1], ?_⟩
  simp only [cost, hc]
  exact Nat.add_le_add_right hp.2 1

theorem Run.ite_false {c : Reg → Bool} {p q : Pg} {v v' : Reg} {s s' : Stk} {B : Nat}
    (hc : c v = false) (hq : Run q v s v' s' B) :
    Run (Prog.ite c p q) v s v' s' (B + 1) := by
  refine ⟨by simp [exec, hc, hq.1], ?_⟩
  simp only [cost, hc, Bool.false_eq_true]
  exact Nat.add_le_add_right hq.2 1

theorem noTouch_wpush (k : K) (a : W) (f : Reg → Bool) : NoTouch k (wpush a f) ↔ K.w a ≠ k := Iff.rfl

theorem noTouch_wpop (k : K) (a : W) (f : Reg → Option Bool → Reg) :
    NoTouch k (wpop a f) ↔ K.w a ≠ k := Iff.rfl

theorem noTouch_load (k : K) (f : Reg → Reg) : NoTouch k (Prog.load f : Pg) ↔ True := Iff.rfl

theorem noTouch_seq (k : K) (p q : Pg) : NoTouch k (Prog.seq p q) ↔ NoTouch k p ∧ NoTouch k q :=
  Iff.rfl

theorem noTouch_ite (k : K) (c : Reg → Bool) (p q : Pg) :
    NoTouch k (Prog.ite c p q) ↔ NoTouch k p ∧ NoTouch k q := Iff.rfl

theorem noTouch_forPop (k : K) (a : W) (f : Reg → Bool → Reg) (g : Reg → Reg) (body : Pg) :
    NoTouch k (forPop a f g body) ↔ K.w a ≠ k ∧ NoTouch k body := Iff.rfl

theorem noTouch_move (k : K) (a b : W) : NoTouch k (move a b) ↔ K.w a ≠ k ∧ K.w b ≠ k := Iff.rfl

theorem noTouch_drain (k : K) (a : W) : NoTouch k (drain a) ↔ K.w a ≠ k := by
  simp [drain, noTouch_forPop, noTouch_load]

theorem noTouch_forC (k : K) (c cb : W) (body : Pg) :
    NoTouch k (forC c cb body) ↔
      (K.w c ≠ k ∧ K.w cb ≠ k ∧ NoTouch k body) ∧ K.w cb ≠ k ∧ K.w c ≠ k := Iff.rfl

theorem noTouch_copyS (k : K) (a tmp dst : W) :
    NoTouch k (copyS a tmp dst) ↔
      (K.w a ≠ k ∧ K.w tmp ≠ k ∧ K.w dst ≠ k) ∧ K.w tmp ≠ k ∧ K.w a ≠ k := Iff.rfl

theorem wf_wpush (a : W) (f : Reg → Bool) : WF (wpush a f) ↔ True := Iff.rfl

theorem wf_wpop (a : W) (f : Reg → Option Bool → Reg) : WF (wpop a f) ↔ True := Iff.rfl

theorem wf_load (f : Reg → Reg) : WF (Prog.load f : Pg) ↔ True := Iff.rfl

theorem wf_seq (p q : Pg) : WF (Prog.seq p q) ↔ WF p ∧ WF q := Iff.rfl

theorem wf_ite (c : Reg → Bool) (p q : Pg) : WF (Prog.ite c p q) ↔ WF p ∧ WF q := Iff.rfl

theorem wf_forPop (a : W) (f : Reg → Bool → Reg) (g : Reg → Reg) (body : Pg) :
    WF (forPop a f g body) ↔ NoTouch (K.w a) body ∧ WF body := by
  constructor
  · intro h; exact h.2
  · intro h; exact ⟨fun _ => rfl, h⟩

theorem wf_move (a b : W) : WF (move a b) ↔ K.w b ≠ K.w a := by
  rw [move, wf_forPop, noTouch_wpush, wf_wpush]; simp

theorem wf_drain (a : W) : WF (drain a) ↔ True := by
  rw [drain, wf_forPop, noTouch_load, wf_load]; simp

theorem wf_forC (c cb : W) (body : Pg) :
    WF (forC c cb body) ↔
      ((K.w cb ≠ K.w c ∧ NoTouch (K.w c) body) ∧ WF body) ∧ K.w c ≠ K.w cb := by
  rw [forC, wf_seq, wf_forPop, noTouch_seq, noTouch_wpush, wf_seq, wf_wpush, wf_move]; simp

theorem wf_copyS (a tmp dst : W) :
    WF (copyS a tmp dst) ↔ (K.w tmp ≠ K.w a ∧ K.w dst ≠ K.w a) ∧ K.w a ≠ K.w tmp := by
  rw [copyS, wf_seq, wf_forPop, noTouch_seq, noTouch_wpush, noTouch_wpush,
    wf_seq, wf_wpush, wf_wpush, wf_move]; simp

theorem move_spec (a b : W) (hab : a ≠ b) (l : List Bool) : ∀ (v : Reg) (s : Stk), s.get a = l →
    Run (move a b) v s (nrm v) ((s.set a []).set b (l.reverse ++ s.get b)) (2 * l.length + 1) := by
  have hnt : NoTouch (K.w a) (wpush b (fun v => v.u)) := by
    rw [noTouch_wpush]; exact fun e => hab (K.w.inj e).symm
  induction l with
  | nil =>
    intro v s h
    refine ⟨?_, ?_⟩
    · rw [move, exec_forPop_nil _ _ _ _ _ _ h]
      refine St_eq _ _ _ _ rfl ?_
      apply Stk.ext_get
      · simp [set_inp]
      · simp [set_out]
      · intro c
        simp only [get_set]
        by_cases h1 : c = b
        · simp [h1]
        · by_cases h2 : c = a
          · simp [h2, h, hab]
          · simp [h1, h2]
    · rw [move, cost_forPop_nil _ _ _ _ _ _ h]; omega
  | cons x l ih =>
    intro v s h
    have hs : ((s.set a l).set b (x :: (s.set a l).get b)).get a = l := by
      rw [get_set_ne _ _ _ _ hab, get_set_self]
    obtain ⟨e1, e2⟩ := ih { v with u := x, go := true }
      ((s.set a l).set b (x :: (s.set a l).get b)) hs
    refine ⟨?_, ?_⟩
    · rw [move, exec_forPop_cons _ _ _ _ _ _ x l h hnt, exec_wpush]
      rw [move] at e1
      rw [e1]
      refine St_eq _ _ _ _ rfl ?_
      apply Stk.ext_get
      · simp [set_inp]
      · simp [set_out]
      · intro c
        simp only [get_set]
        by_cases h1 : c = b
        · simp [h1, Ne.symm hab]
        · by_cases h2 : c = a
          · simp [h2, hab]
          · simp [h1, h2]
    · rw [move, cost_forPop_cons _ _ _ _ _ _ x l h hnt, exec_wpush]
      change cost (move a b) _ + (1 + 1) ≤ _
      simp only [List.length_cons]
      omega

theorem Run.move (a b : W) (hab : a ≠ b) (v : Reg) (s : Stk) :
    Run (move a b) v s (nrm v) ((s.set a []).set b ((s.get a).reverse ++ s.get b))
      (2 * (s.get a).length + 1) :=
  move_spec a b hab (s.get a) v s rfl

theorem moveOut_spec (l : List Bool) : ∀ (v : Reg) (s : Stk), s.OutRev = l →
    Run moveOut v s (nrm v) { s with OutRev := [], out := l.reverse ++ s.out } (2 * l.length + 1) := by
  have hnt : NoTouch (K.w .OutRev) (Prog.push K.out (fun v : Reg => v.u) : Pg) := by
    intro h; cases h
  induction l with
  | nil =>
    intro v s h
    have hg : s.get .OutRev = [] := h
    refine ⟨?_, ?_⟩
    · rw [moveOut, exec_forPop_nil _ _ _ _ _ _ hg]
      refine St_eq _ _ _ _ rfl ?_
      apply Stk.ext_get
      · rfl
      · simp
      · intro c; cases c <;> simp [Stk.get, h]
    · rw [moveOut, cost_forPop_nil _ _ _ _ _ _ hg]; omega
  | cons x l ih =>
    intro v s h
    have hg : s.get .OutRev = x :: l := h
    let s1 : Stk := { s with OutRev := l, out := x :: s.out }
    have hs1_eq : { s.set .OutRev l with out := x :: (s.set .OutRev l).out } = s1 := by
      apply Stk.ext_get
      · rfl
      · rfl
      · intro c; cases c <;> rfl
    obtain ⟨e1, e2⟩ := ih { v with u := x, go := true } s1 rfl
    refine ⟨?_, ?_⟩
    · rw [moveOut, exec_forPop_cons _ _ _ _ _ _ x l hg hnt, exec_outpush, hs1_eq]
      rw [moveOut] at e1
      rw [e1]
      refine St_eq _ _ _ _ rfl ?_
      apply Stk.ext_get
      · rfl
      · simp [s1]
      · intro c; cases c <;> rfl
    · rw [moveOut, cost_forPop_cons _ _ _ _ _ _ x l hg hnt, exec_outpush, hs1_eq]
      change cost moveOut _ + (1 + 1) ≤ _
      simp only [List.length_cons]
      omega

theorem drain_spec (a : W) (l : List Bool) : ∀ (v : Reg) (s : Stk), s.get a = l →
    Run (drain a) v s (nrm v) (s.set a []) (2 * l.length + 1) := by
  have hnt : NoTouch (K.w a) (Prog.load id : Pg) := trivial
  induction l with
  | nil =>
    intro v s h
    refine ⟨?_, ?_⟩
    · rw [drain, exec_forPop_nil _ _ _ _ _ _ h]
      refine St_eq _ _ _ _ rfl ?_
      rw [← h, set_get_self]
    · rw [drain, cost_forPop_nil _ _ _ _ _ _ h]; omega
  | cons x l ih =>
    intro v s h
    obtain ⟨e1, e2⟩ := ih { v with go := true } (s.set a l) (get_set_self s a l)
    refine ⟨?_, ?_⟩
    · rw [drain, exec_forPop_cons _ _ _ _ _ _ x l h hnt]
      change exec (drain a) ⟨{ v with go := true }, toFun (s.set a l)⟩ = _
      rw [e1]
      refine St_eq _ _ _ _ rfl ?_
      rw [set_set]
    · rw [drain, cost_forPop_cons _ _ _ _ _ _ x l h hnt]
      change cost (drain a) ⟨{ v with go := true }, toFun (s.set a l)⟩ + (1 + 1) ≤ _
      simp only [List.length_cons]
      omega

theorem Run.drain (a : W) (v : Reg) (s : Stk) :
    Run (drain a) v s (nrm v) (s.set a []) (2 * (s.get a).length + 1) :=
  drain_spec a (s.get a) v s rfl

theorem copyS_loop_spec (a tmp dst : W) (h1 : a ≠ tmp) (h2 : a ≠ dst) (h3 : tmp ≠ dst)
    (l : List Bool) : ∀ (v : Reg) (s : Stk), s.get a = l →
    Run (forPop a (fun v c => { v with u := c }) id
      (Prog.seq (wpush tmp (fun v => v.u)) (wpush dst (fun v => v.u)))) v s
      (nrm v) (((s.set a []).set tmp (l.reverse ++ s.get tmp)).set dst (l.reverse ++ s.get dst))
      (3 * l.length + 1) := by
  have hnt : NoTouch (K.w a) (Prog.seq (wpush tmp (fun v => v.u)) (wpush dst (fun v => v.u))) := by
    rw [noTouch_seq, noTouch_wpush, noTouch_wpush]
    exact ⟨fun e => h1 (K.w.inj e).symm, fun e => h2 (K.w.inj e).symm⟩
  induction l with
  | nil =>
    intro v s h
    refine ⟨?_, ?_⟩
    · rw [exec_forPop_nil _ _ _ _ _ _ h]
      refine St_eq _ _ _ _ rfl ?_
      apply Stk.ext_get
      · simp [set_inp]
      · simp [set_out]
      · intro c
        simp only [get_set]
        by_cases hd : c = dst
        · subst hd; simp
        · by_cases ht : c = tmp
          · subst ht; simp [h3]
          · by_cases ha : c = a
            · subst ha; simp [h1, h2, h]
            · simp [hd, ht, ha]
    · rw [cost_forPop_nil _ _ _ _ _ _ h]; omega
  | cons x l ih =>
    intro v s h
    let s1 := ((s.set a l).set tmp (x :: (s.set a l).get tmp)).set dst
      (x :: ((s.set a l).set tmp (x :: (s.set a l).get tmp)).get dst)
    have hs1 : s1.get a = l := by
      simp only [s1, get_set_ne _ _ _ _ h2, get_set_ne _ _ _ _ h1, get_set_self]
    obtain ⟨e1, e2⟩ := ih { v with u := x, go := true } s1 hs1
    refine ⟨?_, ?_⟩
    · rw [exec_forPop_cons _ _ _ _ _ _ x l h hnt]
      simp only [exec, exec_wpush]
      change exec _ ⟨{ v with u := x, go := true }, toFun s1⟩ = _
      rw [e1]
      refine St_eq _ _ _ _ rfl ?_
      apply Stk.ext_get
      · simp [s1, set_inp]
      · simp [s1, set_out]
      · intro c
        simp only [s1, get_set]
        by_cases hd : c = dst
        · subst hd; simp [Ne.symm h2, Ne.symm h3]
        · by_cases ht : c = tmp
          · subst ht; simp [h3, Ne.symm h1]
          · by_cases ha : c = a
            · subst ha; simp [h1, h2]
            · simp [hd, ht, ha]
    · rw [cost_forPop_cons _ _ _ _ _ _ x l h hnt]
      simp only [exec, cost, exec_wpush]
      change cost _ ⟨{ v with u := x, go := true }, toFun s1⟩ + (1 + 1 + 1) ≤ _
      simp only [List.length_cons]
      omega

theorem copyS_spec (a tmp dst : W) (h1 : a ≠ tmp) (h2 : a ≠ dst) (h3 : tmp ≠ dst)
    (v : Reg) (s : Stk) (htmp : s.get tmp = []) :
    Run (copyS a tmp dst) v s (nrm v) (s.set dst ((s.get a).reverse ++ s.get dst))
      (5 * (s.get a).length + 2) := by
  have p1 := copyS_loop_spec a tmp dst h1 h2 h3 (s.get a) v s rfl
  have p2 := Run.move tmp a (Ne.symm h1) (nrm v)
    (((s.set a []).set tmp ((s.get a).reverse ++ s.get tmp)).set dst ((s.get a).reverse ++ s.get dst))
  refine Run.conv (Run.seq p1 p2) (nrm_nrm v) ?_ ?_
  · apply Stk.ext_get
    · simp [set_inp]
    · simp [set_out]
    · intro c
      simp only [get_set, htmp, List.append_nil]
      by_cases ha : c = a
      · subst ha; simp [h1, h2, h3]
      · by_cases ht : c = tmp
        · subst ht; simp [Ne.symm h1, h3, htmp]
        · by_cases hd : c = dst
          · subst hd; simp [Ne.symm h2, Ne.symm h3]
          · simp [ha, ht, hd]
  · simp only [get_set_ne _ _ _ _ h3, get_set_self, htmp, List.append_nil, List.length_reverse]
    omega

def halveOnce (a b : W) : Pg :=
  Prog.seq (Prog.load fun v => { v with par := false })
    (forPop a (fun v _ => { v with par := !v.par }) id
      (Prog.ite (fun v => !v.par) (wpush b tt) (Prog.load id)))

theorem noTouch_halveOnce (k : K) (a b : W) :
    NoTouch k (halveOnce a b) ↔ True ∧ K.w a ≠ k ∧ K.w b ≠ k ∧ True := Iff.rfl

theorem wf_halveOnce (a b : W) : WF (halveOnce a b) ↔ K.w b ≠ K.w a := by
  rw [halveOnce, wf_seq, wf_load, wf_forPop, noTouch_ite, noTouch_wpush, noTouch_load,
    wf_ite, wf_wpush, wf_load]; simp

theorem halveOnce_loop_spec (a b : W) (hab : a ≠ b) (m : Nat) :
    ∀ (k : Nat) (p : Bool) (v : Reg) (s : Stk),
      v.par = p → s.get a = List.replicate m true → s.get b = List.replicate k true →
      Run (forPop a (fun v _ => { v with par := !v.par }) id
        (Prog.ite (fun v => !v.par) (wpush b tt) (Prog.load id))) v s
        (nrm { v with par := xor p (decide (m % 2 = 1)) })
        ((s.set a []).set b (List.replicate (k + (m + p.toNat) / 2) true))
        (3 * m + 1) := by
  have hnt : NoTouch (K.w a) (Prog.ite (fun v => !v.par) (wpush b tt) (Prog.load id)) := by
    rw [noTouch_ite, noTouch_wpush, noTouch_load]
    exact ⟨fun e => hab (K.w.inj e).symm, trivial⟩
  induction m with
  | zero =>
    intro k p v s hp ha hb
    refine ⟨?_, ?_⟩
    · rw [exec_forPop_nil _ _ _ _ _ _ ha]
      refine St_eq _ _ _ _ ?_ ?_
      · cases v; cases p <;> simp_all [nrm]
      · apply Stk.ext_get
        · simp [set_inp]
        · simp [set_out]
        · intro c
          simp only [get_set]
          by_cases h1 : c = b
          · subst h1; cases p <;> simp [hb]
          · by_cases h2 : c = a
            · subst h2; simp [h1, ha]
            · simp [h1, h2]
    · exact le_of_eq (cost_forPop_nil _ _ _ _ _ _ ha)
  | succ m ih =>
    intro k p v s hp ha hb
    cases p
    · have ha' : (s.set a (List.replicate m true)).get a = List.replicate m true :=
        get_set_self s a _
      have hb' : (s.set a (List.replicate m true)).get b = List.replicate k true := by
        rw [get_set_ne _ _ _ _ (Ne.symm hab), hb]
      obtain ⟨e1, e2⟩ := ih k true { v with par := true, go := true }
        (s.set a (List.replicate m true)) rfl ha' hb'
      refine ⟨?_, ?_⟩
      · rw [exec_forPop_cons _ _ _ _ _ _ true (List.replicate m true) ha hnt]
        simp only [hp, Bool.not_false, exec, Bool.not_true, Bool.false_eq_true, ite_false]
        change exec _ ⟨{ v with par := true, go := true }, toFun (s.set a (List.replicate m true))⟩ = _
        rw [e1]
        refine St_eq _ _ _ _ ?_ ?_
        · cases v
          simp only [nrm, Reg.mk.injEq, true_and]
          have : decide ((m + 1) % 2 = 1) = !decide (m % 2 = 1) := by
            by_cases hm : m % 2 = 1
            · have : (m + 1) % 2 = 0 := by omega
              simp [hm, this]
            · have : (m + 1) % 2 = 1 := by omega
              simp [hm, this]
          rw [this]
          cases decide (m % 2 = 1) <;> rfl
        · apply Stk.ext_get
          · simp [set_inp]
          · simp [set_out]
          · intro c
            simp only [get_set]
            by_cases h1 : c = b
            · subst h1; simp [show (m + 1) / 2 = (m + 1 + 0) / 2 by omega]
            · by_cases h2 : c = a
              · subst h2; simp [h1]
              · simp [h1, h2]
      · rw [cost_forPop_cons _ _ _ _ _ _ true (List.replicate m true) ha hnt]
        simp only [hp, Bool.not_false, exec, cost, Bool.not_true, Bool.false_eq_true, ite_false]
        change cost _ ⟨{ v with par := true, go := true }, toFun (s.set a (List.replicate m true))⟩ + (1 + 1 + 1) ≤ _
        omega
    · let s1 := (s.set a (List.replicate m true)).set b (List.replicate (k + 1) true)
      have ha' : s1.get a = List.replicate m true := by
        simp only [s1, get_set_ne _ _ _ _ hab, get_set_self]
      have hb' : s1.get b = List.replicate (k + 1) true := get_set_self _ b _
      obtain ⟨e1, e2⟩ := ih (k + 1) false { v with par := false, go := true } s1 rfl ha' hb'
      have hs1_eq : (s.set a (List.replicate m true)).set b
          (true :: (s.set a (List.replicate m true)).get b) = s1 := by
        simp only [s1, get_set_ne _ _ _ _ (Ne.symm hab), hb, List.replicate_succ]
      refine ⟨?_, ?_⟩
      · rw [exec_forPop_cons _ _ _ _ _ _ true (List.replicate m true) ha hnt]
        simp only [hp, Bool.not_true, exec, Bool.not_false, ite_true, exec_wpush, tt, hs1_eq]
        rw [e1]
        refine St_eq _ _ _ _ ?_ ?_
        · cases v
          simp only [nrm, Reg.mk.injEq, true_and]
          have : decide ((m + 1) % 2 = 1) = !decide (m % 2 = 1) := by
            by_cases hm : m % 2 = 1
            · have : (m + 1) % 2 = 0 := by omega
              simp [hm, this]
            · have : (m + 1) % 2 = 1 := by omega
              simp [hm, this]
          rw [this]
          cases decide (m % 2 = 1) <;> rfl
        · apply Stk.ext_get
          · simp [s1, set_inp]
          · simp [s1, set_out]
          · intro c
            simp only [s1, get_set]
            by_cases h1 : c = b
            · subst h1
              simp only [ite_true, Bool.toNat_true, Bool.toNat_false]
              congr 1; omega
            · by_cases h2 : c = a
              · subst h2; simp [h1]
              · simp [h1, h2]
      · rw [cost_forPop_cons _ _ _ _ _ _ true (List.replicate m true) ha hnt]
        simp only [hp, Bool.not_true, exec, cost, Bool.not_false, ite_true, exec_wpush, tt, hs1_eq]
        change cost _ ⟨{ v with par := false, go := true }, toFun s1⟩ + (1 + 1 + 1) ≤ _
        omega

theorem halveOnce_spec (a b : W) (hab : a ≠ b) (m : Nat) (v : Reg) (s : Stk)
    (ha : s.get a = List.replicate m true) (hb : s.get b = []) :
    Run (halveOnce a b) v s (nrm { v with par := m.testBit 0 })
      ((s.set a []).set b (List.replicate (m / 2) true)) (3 * m + 2) := by
  have h1 := Run.load (fun v => { v with par := false }) v s
  have h2 := halveOnce_loop_spec a b hab m 0 false { v with par := false } s rfl ha hb
  refine Run.conv (Run.seq h1 h2) ?_ ?_ (by omega)
  · cases v
    simp only [nrm, Bool.false_xor, Reg.mk.injEq, true_and]
    rw [Nat.testBit_zero]
  · simp

theorem bits_succ (w m : Nat) : bits (w + 1) m = m.testBit 0 :: bits w (m / 2) := by
  unfold bits
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  refine List.map_congr_left ?_
  intro j _
  simp only [Function.comp_apply, Nat.testBit_div_two]

def emitQStep : Pg :=
  Prog.seq (halveOnce .Q .Qb)
    (Prog.seq (wpush .OutRev (fun v => v.par)) (move .Qb .Q))

def emitQ : Pg :=
  Prog.seq (forC .Wstk .Wb emitQStep) (drain .Q)

theorem noTouch_emitQStep (k : K) :
    NoTouch k emitQStep ↔
      (True ∧ K.w .Q ≠ k ∧ K.w .Qb ≠ k ∧ True) ∧ K.w .OutRev ≠ k ∧ K.w .Qb ≠ k ∧ K.w .Q ≠ k :=
  Iff.rfl

theorem wf_emitQ : WF emitQ := by
  simp [emitQ, emitQStep, wf_seq, wf_forC, wf_drain, wf_halveOnce, wf_wpush, wf_move,
    noTouch_seq, noTouch_halveOnce, noTouch_wpush, noTouch_move]

theorem emitQStep_spec (m : Nat) (v : Reg) (s : Stk)
    (hQ : s.Q = List.replicate m true) (hQb : s.Qb = []) :
    Run emitQStep v s (nrm { v with par := m.testBit 0 })
      { s with Q := List.replicate (m / 2) true, OutRev := m.testBit 0 :: s.OutRev }
      (4 * m + 4) := by
  have p1 := halveOnce_spec .Q .Qb (by decide) m v s hQ hQb
  refine Run.conv (Run.seq p1 (Run.seq (Run.wpush .OutRev (fun v => v.par) _ _)
    (Run.move .Qb .Q (by decide) _ _))) ?_ ?_ ?_
  · cases v; simp [nrm]
  · apply Stk.ext_get
    · simp [set_inp]
    · simp [set_out]
    · intro c; cases c <;> simp [Stk.get, Stk.set, hQb, nrm]
  · simp [Stk.get, Stk.set]
    omega

theorem emitQ_loop_spec (w : Nat) : ∀ (k m : Nat) (v : Reg) (s : Stk),
    s.Wstk = List.replicate w true → s.Wb = List.replicate k true →
    s.Q = List.replicate m true → s.Qb = [] →
    ∃ m', m' ≤ m ∧
      Run (forPop .Wstk (fun v _ => v) id (Prog.seq (wpush .Wb tt) emitQStep)) v s
        (nrm { v with par := if w = 0 then v.par else (m / 2 ^ (w - 1)).testBit 0 })
        { s with Wstk := [], Wb := List.replicate (k + w) true, Q := List.replicate m' true, OutRev := (bits w m).reverse ++ s.OutRev }
        (w * (4 * m + 6) + 1) := by
  have hnt : NoTouch (K.w .Wstk) (Prog.seq (wpush .Wb tt) emitQStep) := by
    simp [emitQStep, noTouch_seq, noTouch_wpush, noTouch_halveOnce, noTouch_move]
  induction w with
  | zero =>
    intro k m v s hW hWb hQ hQb
    have hWg : s.get .Wstk = [] := hW
    refine ⟨m, le_refl _, ?_, ?_⟩
    · rw [exec_forPop_nil _ _ _ _ _ _ hWg]
      refine St_eq _ _ _ _ (by cases v; simp [nrm]) ?_
      apply Stk.ext_get
      · rfl
      · rfl
      · intro c; cases c <;> simp [Stk.get, hW, hWb, hQ, bits]
    · rw [cost_forPop_nil _ _ _ _ _ _ hWg]; simp
  | succ w ih =>
    intro k m v s hW hWb hQ hQb
    have hWg : s.get .Wstk = true :: List.replicate w true := by
      simpa [Stk.get, List.replicate_succ] using hW
    let v1 : Reg := { v with go := true }
    let s1 : Stk := { s with Wstk := List.replicate w true, Wb := List.replicate (k + 1) true }
    have hp1 : Run (wpush .Wb tt) v1 (s.set .Wstk (List.replicate w true)) v1 s1 1 := by
      refine Run.conv (Run.wpush .Wb tt v1 (s.set .Wstk (List.replicate w true)))
        rfl ?_ (le_refl _)
      apply Stk.ext_get
      · rfl
      · rfl
      · intro c; cases c <;> simp [s1, Stk.get, Stk.set, hWb, List.replicate_succ, tt]
    have hp2 := emitQStep_spec m v1 s1 hQ hQb
    have hbody := Run.seq hp1 hp2
    let s2 : Stk := { s1 with Q := List.replicate (m / 2) true, OutRev := m.testBit 0 :: s1.OutRev }
    obtain ⟨m', hm', e1, e2⟩ := ih (k + 1) (m / 2) (nrm { v with par := m.testBit 0 }) s2
      rfl rfl rfl hQb
    have hv_eq : nrm { v1 with par := m.testBit 0 } = nrm { v with par := m.testBit 0 } := by
      cases v; rfl
    refine ⟨m', le_trans hm' (Nat.div_le_self m 2), ?_, ?_⟩
    · rw [exec_forPop_cons _ _ _ _ _ _ true (List.replicate w true) hWg hnt]
      have hbd := hbody.1
      rw [hv_eq] at hbd
      change exec _ (exec _ ⟨v1, toFun (s.set .Wstk (List.replicate w true))⟩) = _
      rw [hbd, e1]
      refine St_eq _ _ _ _ ?_ ?_
      · cases w with
        | zero => cases v; simp [nrm]
        | succ w' =>
          cases v
          simp only [nrm, Nat.add_sub_cancel, Nat.succ_ne_zero, ite_false, Reg.mk.injEq,
            true_and]
          rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ']
      · apply Stk.ext_get
        · rfl
        · rfl
        · intro c
          cases c <;> simp [s2, s1, Stk.get, bits_succ, show k + 1 + w = k + (w + 1) by omega]
    · rw [cost_forPop_cons _ _ _ _ _ _ true (List.replicate w true) hWg hnt]
      have hbd := hbody.1
      have hbc := hbody.2
      rw [hv_eq] at hbd
      change cost _ (exec _ ⟨v1, toFun (s.set .Wstk (List.replicate w true))⟩) +
        (cost _ ⟨v1, toFun (s.set .Wstk (List.replicate w true))⟩ + 1) ≤ _
      rw [hbd]
      have hmdiv : m / 2 ≤ m := Nat.div_le_self m 2
      have hmul : w * (4 * (m / 2) + 6) ≤ w * (4 * m + 6) :=
        Nat.mul_le_mul_left w (by omega)
      have hstep : (w + 1) * (4 * m + 6) = w * (4 * m + 6) + (4 * m + 6) := by ring
      dsimp only [s2] at e2
      rw [hstep]
      omega

theorem emitQ_spec (w m : Nat) (v : Reg) (s : Stk)
    (hW : s.Wstk = List.replicate w true) (hWb : s.Wb = [])
    (hQ : s.Q = List.replicate m true) (hQb : s.Qb = []) :
    ∃ p' : Bool,
      Run emitQ v s (nrm { v with par := p' })
        ({ s with Q := [], OutRev := (bits w m).reverse ++ s.OutRev })
        ((w + 1) * (4 * m + 8) + 2 * m + 3) := by
  obtain ⟨m', hm', hloop⟩ := emitQ_loop_spec w 0 m v s hW hWb hQ hQb
  refine ⟨if w = 0 then v.par else (m / 2 ^ (w - 1)).testBit 0, ?_⟩
  refine Run.conv (Run.seq (Run.seq hloop (Run.move .Wb .Wstk (by decide) _ _)) (Run.drain .Q _ _)) ?_ ?_ ?_
  · cases v; simp [nrm]
  · apply Stk.ext_get
    · simp [set_inp]
    · simp [set_out]
    · intro c; cases c <;> simp [Stk.get, Stk.set, hW, hWb, hQb]
  · simp only [Stk.get, Stk.set, List.length_replicate, Nat.zero_add]
    have : (w + 1) * (4 * m + 8) = w * (4 * m + 6) + 2 * w + 4 * m + 8 := by ring
    omega

def halveSteps : Nat → Nat → Nat
  | 0, _ => 0
  | _ + 1, 0 => 0
  | s + 1, m + 1 => 1 + halveSteps s ((m + 1) / 2)

theorem halveSteps_eq_log2 : ∀ (m s : Nat), 1 ≤ m → m ≤ s → halveSteps s m = m.log2 + 1 := by
  intro m
  induction m using Nat.strong_induction_on with
  | ind m ih =>
    intro s hm hms
    cases s with
    | zero => omega
    | succ s' =>
      cases m with
      | zero => omega
      | succ m' =>
        simp only [halveSteps]
        by_cases h1 : m' = 0
        · subst h1
          have : halveSteps s' 0 = 0 := by cases s' <;> rfl
          rw [this]
          decide
        · have hge2 : 2 ≤ m' + 1 := by omega
          have hdiv_lt : (m' + 1) / 2 < m' + 1 := Nat.div_lt_self (by omega) (by omega)
          have hdiv_ge1 : 1 ≤ (m' + 1) / 2 := by omega
          have hdiv_le : (m' + 1) / 2 ≤ s' := by omega
          rw [ih ((m' + 1) / 2) hdiv_lt s' hdiv_ge1 hdiv_le]
          conv_rhs => rw [Nat.log2_def]
          simp only [hge2, ite_true]
          omega

def computeWStep : Pg :=
  Prog.seq (wpop .Q (fun v o => { v with u := o.isSome }))
    (Prog.ite (fun v => v.u)
      (Prog.seq (wpush .Q tt)
        (Prog.seq (wpush .Wstk tt)
          (Prog.seq (halveOnce .Q .Qb) (move .Qb .Q))))
      (Prog.load nrm))

def computeW : Pg :=
  Prog.seq (copyS .Nstk .Tmp .Q)
    (Prog.seq (forC .Nstk .Nb computeWStep) (drain .Q))

theorem wf_computeW : WF computeW := by
  simp [computeW, computeWStep, wf_seq, wf_copyS, wf_forC, wf_drain, wf_wpop, wf_ite,
    wf_wpush, wf_halveOnce, wf_move, wf_load, noTouch_seq, noTouch_wpop, noTouch_ite,
    noTouch_wpush, noTouch_halveOnce, noTouch_move, noTouch_load]

theorem computeWStep_spec (m k : Nat) (v : Reg) (s : Stk)
    (hQ : s.Q = List.replicate m true) (hQb : s.Qb = []) (hW : s.Wstk = List.replicate k true) :
    ∃ p' : Bool,
      Run computeWStep v s (nrm { v with par := p' })
        { s with Q := List.replicate (m / 2) true, Wstk := List.replicate (if m = 0 then k else k + 1) true }
        (4 * m + 8) := by
  cases m with
  | zero =>
    have p1 := Run.wpop .Q (fun v o => { v with u := o.isSome }) v s
    have p2 := Run.ite_false (c := fun v => v.u)
      (p := Prog.seq (wpush .Q tt) (Prog.seq (wpush .Wstk tt) (Prog.seq (halveOnce .Q .Qb) (move .Qb .Q))))
      (by simp [Stk.get, hQ]) (Run.load nrm ({ v with u := (s.get .Q).head?.isSome }) (s.set .Q (s.get .Q).tail))
    refine ⟨v.par, Run.conv (Run.seq p1 p2) ?_ ?_ (by omega)⟩
    · cases v; simp [nrm]
    · apply Stk.ext_get
      · simp [set_inp]
      · simp [set_out]
      · intro c; cases c <;> simp [Stk.get, Stk.set, hQ, hW]
  | succ m' =>
    have p1 := Run.wpop .Q (fun v o => { v with u := o.isSome }) v s
    have hpop : (s.get .Q).head? = some true := by simp [Stk.get, hQ, List.replicate_succ]
    let v1 : Reg := { v with u := (s.get .Q).head?.isSome }
    let s1 : Stk := s.set .Q (s.get .Q).tail
    let s2 : Stk := s1.set .Q (true :: s1.get .Q)
    let s3 : Stk := s2.set .Wstk (true :: s2.get .Wstk)
    have hQrest : s3.get .Q = List.replicate (m' + 1) true := by
      simp [s3, s2, s1, Stk.get, Stk.set, hQ, List.replicate_succ]
    have hQbrest : s3.get .Qb = [] := by
      simp [s3, s2, s1, Stk.get, Stk.set, hQb]
    have p2 := Run.wpush .Q tt v1 s1
    have p3 := Run.wpush .Wstk tt v1 s2
    have p4 := halveOnce_spec .Q .Qb (by decide) (m' + 1) v1 s3 hQrest hQbrest
    have hbranch := Run.ite_true (c := fun v => v.u) (q := Prog.load nrm)
      (by simp [v1, hpop]) (Run.seq p2 (Run.seq p3 (Run.seq p4 (Run.move .Qb .Q (by decide) _ _))))
    refine ⟨(m' + 1).testBit 0, Run.conv (Run.seq p1 hbranch) ?_ ?_ ?_⟩
    · cases v; simp [v1, nrm]
    · apply Stk.ext_get
      · simp [s3, s2, s1, set_inp]
      · simp [s3, s2, s1, set_out]
      · intro c; cases c <;> simp [s3, s2, s1, Stk.get, Stk.set, hQ, hQb, hW, List.replicate_succ]
    · simp only [s3, s2, s1, Stk.get, Stk.set, List.length_replicate]
      omega

theorem computeW_loop_spec (t : Nat) : ∀ (b k m : Nat) (v : Reg) (s : Stk),
    s.Nstk = List.replicate t true → s.Nb = List.replicate b true →
    s.Q = List.replicate m true → s.Qb = [] → s.Wstk = List.replicate k true →
    ∃ (m' : Nat) (p' : Bool), m' ≤ m ∧
      Run (forPop .Nstk (fun v _ => v) id (Prog.seq (wpush .Nb tt) computeWStep)) v s
        (nrm { v with par := p' })
        { s with Nstk := [], Nb := List.replicate (b + t) true, Q := List.replicate m' true, Wstk := List.replicate (k + halveSteps t m) true }
        (t * (4 * m + 10) + 1) := by
  have hnt : NoTouch (K.w .Nstk) (Prog.seq (wpush .Nb tt) computeWStep) := by
    simp [computeWStep, noTouch_seq, noTouch_wpush, noTouch_wpop, noTouch_ite,
      noTouch_halveOnce, noTouch_move, noTouch_load]
  induction t with
  | zero =>
    intro b k m v s hN hNb hQ hQb hW
    have hNg : s.get .Nstk = [] := hN
    refine ⟨m, v.par, le_refl _, ?_, ?_⟩
    · rw [exec_forPop_nil _ _ _ _ _ _ hNg]
      refine St_eq _ _ _ _ (by cases v; simp [nrm]) ?_
      apply Stk.ext_get
      · rfl
      · rfl
      · intro c; cases c <;> simp [Stk.get, hN, hNb, hQ, hW, halveSteps]
    · rw [cost_forPop_nil _ _ _ _ _ _ hNg]; simp
  | succ t ih =>
    intro b k m v s hN hNb hQ hQb hW
    have hNg : s.get .Nstk = true :: List.replicate t true := by
      simpa [Stk.get, List.replicate_succ] using hN
    let v1 : Reg := { v with go := true }
    let s1 : Stk := { s with Nstk := List.replicate t true, Nb := List.replicate (b + 1) true }
    have hp1 : Run (wpush .Nb tt) v1 (s.set .Nstk (List.replicate t true)) v1 s1 1 := by
      refine Run.conv (Run.wpush .Nb tt v1 (s.set .Nstk (List.replicate t true)))
        rfl ?_ (le_refl _)
      apply Stk.ext_get
      · rfl
      · rfl
      · intro c; cases c <;> simp [s1, Stk.get, Stk.set, hNb, List.replicate_succ, tt]
    obtain ⟨p1, hp2⟩ := computeWStep_spec m k v1 s1 hQ hQb hW
    have hbody := Run.seq hp1 hp2
    let s2 : Stk := { s1 with Q := List.replicate (m / 2) true, Wstk := List.replicate (if m = 0 then k else k + 1) true }
    obtain ⟨m', p2, hm', e1, e2⟩ := ih (b + 1) (if m = 0 then k else k + 1) (m / 2)
      (nrm { v with par := p1 }) s2 rfl rfl rfl hQb rfl
    have hv_eq : nrm { v1 with par := p1 } = nrm { v with par := p1 } := by cases v; rfl
    refine ⟨m', p2, le_trans hm' (Nat.div_le_self m 2), ?_, ?_⟩
    · rw [exec_forPop_cons _ _ _ _ _ _ true (List.replicate t true) hNg hnt]
      have hbd := hbody.1
      rw [hv_eq] at hbd
      change exec _ (exec _ ⟨v1, toFun (s.set .Nstk (List.replicate t true))⟩) = _
      rw [hbd, e1]
      refine St_eq _ _ _ _ (by cases v; simp [nrm]) ?_
      apply Stk.ext_get
      · rfl
      · rfl
      · intro c
        cases c with
        | Nb =>
          simp only [Stk.get]
          congr 1; omega
        | Wstk =>
          simp only [Stk.get]
          congr 1
          cases m with
          | zero =>
            have : halveSteps t 0 = 0 := by cases t <;> rfl
            simp [halveSteps, this]
          | succ m' =>
            simp [halveSteps]; omega
        | _ => rfl
    · rw [cost_forPop_cons _ _ _ _ _ _ true (List.replicate t true) hNg hnt]
      have hbd := hbody.1
      have hbc := hbody.2
      rw [hv_eq] at hbd
      change cost _ (exec _ ⟨v1, toFun (s.set .Nstk (List.replicate t true))⟩) +
        (cost _ ⟨v1, toFun (s.set .Nstk (List.replicate t true))⟩ + 1) ≤ _
      rw [hbd]
      have hmdiv : m / 2 ≤ m := Nat.div_le_self m 2
      have hmul : t * (4 * (m / 2) + 10) ≤ t * (4 * m + 10) :=
        Nat.mul_le_mul_left t (by omega)
      have hstep : (t + 1) * (4 * m + 10) = t * (4 * m + 10) + (4 * m + 10) := by ring
      dsimp only [s2] at e2
      rw [hstep]
      omega

theorem computeW_spec (n : Nat) (hn : 1 ≤ n) (v : Reg) (s : Stk)
    (hN : s.Nstk = List.replicate n true) (hNb : s.Nb = []) (hTmp : s.Tmp = [])
    (hQ : s.Q = []) (hQb : s.Qb = []) (hW : s.Wstk = []) :
    ∃ p' : Bool,
      Run computeW v s (nrm { v with par := p' })
        ({ s with Wstk := List.replicate (width n) true })
        (4 * n * n + 20 * n + 6) := by
  have p1 := copyS_spec .Nstk .Tmp .Q (by decide) (by decide) (by decide) v s hTmp
  let s1 := s.set .Q ((s.get .Nstk).reverse ++ s.get .Q)
  have hQ1 : s1.Q = List.replicate n true := by simp [s1, Stk.get, Stk.set, hN, hQ]
  obtain ⟨m', p', hm', p2⟩ := computeW_loop_spec n 0 0 n (nrm v) s1
    (by simp [s1, Stk.set, hN]) (by simp [s1, Stk.set, hNb]) hQ1 (by simp [s1, Stk.set, hQb])
    (by simp [s1, Stk.set, hW])
  refine ⟨p', Run.conv (Run.seq p1 (Run.seq (Run.seq p2 (Run.move .Nb .Nstk (by decide) _ _))
    (Run.drain .Q _ _))) ?_ ?_ ?_⟩
  · cases v; simp [nrm]
  · apply Stk.ext_get
    · simp [s1, set_inp]
    · simp [s1, set_out]
    · intro c
      cases c <;> simp [s1, Stk.get, Stk.set, hN, hNb, hTmp, hQ, hQb, hW,
        halveSteps_eq_log2 n n hn (le_refl n), width]
  · simp only [s1, Stk.get, Stk.set, hN, List.length_replicate, Nat.zero_add]
    nlinarith

def pushColor (c : Nat) : Pg :=
  Prog.seq (wpush .OutRev (fun _ => c.testBit 0)) (wpush .OutRev (fun _ => c.testBit 1))

theorem pushColor_spec (c : Nat) (v : Reg) (s : Stk) :
    Run (pushColor c) v s v ({ s with OutRev := (bits 2 c).reverse ++ s.OutRev }) 2 := by
  have p1 := Run.wpush .OutRev (fun _ => c.testBit 0) v s
  refine Run.conv (Run.seq p1 (Run.wpush .OutRev (fun _ => c.testBit 1) _ _)) rfl ?_ (by omega)
  apply Stk.ext_get
  · rfl
  · rfl
  · intro a; cases a <;> simp [Stk.get, Stk.set, bits, List.range_succ]

def emitConst01 (c1 c2 : Nat) : Pg :=
  Prog.seq emitQ
    (Prog.seq (pushColor c1)
      (Prog.seq (wpush .Q tt)
        (Prog.seq emitQ (pushColor c2))))

def emit0Stk (src : W) (c2 : Nat) : Pg :=
  Prog.seq emitQ
    (Prog.seq (pushColor 0)
      (Prog.seq (copyS src .Tmp .Q)
        (Prog.seq emitQ (pushColor c2))))

def emitLitBan (polFlip : Bool) (c2 : Nat) : Pg :=
  Prog.seq (copyS .Vidx .Tmp .Q)
    (Prog.seq emitQ
      (Prog.seq (wpush .OutRev (fun v => if polFlip then !v.pol else v.pol))
        (Prog.seq (wpush .OutRev ff)
          (Prog.seq (copyS .Uocc .Tmp .Q)
            (Prog.seq emitQ (pushColor c2))))))

def emitTransOne (c1 c2 : Nat) : Pg :=
  Prog.seq (copyS .Uocc .Tmp .Q)
    (Prog.seq emitQ
      (Prog.seq (pushColor c1)
        (Prog.seq (copyS .Uocc .Tmp .Q)
          (Prog.seq (wpush .Q tt)
            (Prog.seq emitQ (pushColor c2))))))

theorem emitConst01_spec (w c1 c2 : Nat) (v : Reg) (s : Stk)
    (hW : s.Wstk = List.replicate w true) (hWb : s.Wb = [])
    (hQ : s.Q = []) (hQb : s.Qb = []) :
    ∃ p' : Bool,
      Run (emitConst01 c1 c2) v s (nrm { v with par := p' })
        ({ s with OutRev := (encBan w ((0, c1), (1, c2))).reverse ++ s.OutRev })
        (20 * (w + 1) + 15) := by
  obtain ⟨p1, r1⟩ := emitQ_spec w 0 v s hW hWb hQ hQb
  let v1 := nrm { v with par := p1 }
  let s1 := { s with Q := [], OutRev := (bits w 0).reverse ++ s.OutRev }
  have r2 := pushColor_spec c1 v1 s1
  let s2 := { s1 with OutRev := (bits 2 c1).reverse ++ s1.OutRev }
  have r3 := Run.wpush .Q tt v1 s2
  let s3 := s2.set .Q (true :: s2.get .Q)
  obtain ⟨p2, r4⟩ := emitQ_spec w 1 v1 s3 (by simp [s3, s2, s1, Stk.set, hW])
    (by simp [s3, s2, s1, Stk.set, hWb]) (by simp [s3, s2, s1, Stk.get, Stk.set])
    (by simp [s3, s2, s1, Stk.set, hQb])
  refine ⟨p2, Run.conv (Run.seq r1 (Run.seq r2 (Run.seq r3 (Run.seq r4 (pushColor_spec c2 _ _))))) ?_ ?_ ?_⟩
  · cases v; simp [v1, nrm]
  · apply Stk.ext_get
    · simp [s3, s2, s1, set_inp]
    · simp [s3, s2, s1, set_out]
    · intro a; cases a <;> simp [s3, s2, s1, Stk.get, Stk.set, hQ, encBan, List.append_assoc]
  · omega

theorem emit0Stk_spec (src : W) (hs1 : src ≠ .Tmp) (hs2 : src ≠ .Q)
    (hs6 : src ≠ .OutRev)
    (w u c2 : Nat) (v : Reg) (s : Stk)
    (hW : s.Wstk = List.replicate w true) (hWb : s.Wb = [])
    (hQ : s.Q = []) (hQb : s.Qb = []) (hTmp : s.Tmp = [])
    (hsrc : s.get src = List.replicate u true) :
    ∃ p' : Bool,
      Run (emit0Stk src c2) v s (nrm { v with par := p' })
        ({ s with OutRev := (encBan w ((0, 0), (u, c2))).reverse ++ s.OutRev })
        ((w + 1) * (4 * u + 16) + 7 * u + 15) := by
  obtain ⟨p1, r1⟩ := emitQ_spec w 0 v s hW hWb hQ hQb
  let v1 := nrm { v with par := p1 }
  let s1 := { s with Q := [], OutRev := (bits w 0).reverse ++ s.OutRev }
  have r2 := pushColor_spec 0 v1 s1
  let s2 := { s1 with OutRev := (bits 2 0).reverse ++ s1.OutRev }
  have htmp2 : s2.get .Tmp = [] := by simpa [s2, s1, Stk.get] using hTmp
  have r3 := copyS_spec src .Tmp .Q hs1 hs2 (by decide) v1 s2 htmp2
  have hsrc2 : s2.get src = List.replicate u true := by
    cases src <;> first | exact absurd rfl hs2 | exact absurd rfl hs6 | simpa [s2, s1, Stk.get] using hsrc
  let s3 := s2.set .Q ((s2.get src).reverse ++ s2.get .Q)
  obtain ⟨p2, r4⟩ := emitQ_spec w u (nrm v1) s3
    (by simp [s3, s2, s1, Stk.set, hW]) (by simp [s3, s2, s1, Stk.set, hWb])
    (by simp only [s3, Stk.set, hsrc2, List.reverse_replicate]; simp [s2, s1, Stk.get])
    (by simp [s3, s2, s1, Stk.set, hQb])
  refine ⟨p2, Run.conv (Run.seq r1 (Run.seq r2 (Run.seq r3 (Run.seq r4 (pushColor_spec c2 _ _))))) ?_ ?_ ?_⟩
  · cases v; simp [v1, nrm]
  · apply Stk.ext_get
    · simp [s3, s2, s1, set_inp]
    · simp [s3, s2, s1, set_out]
    · intro a; cases a <;> simp [s3, s2, s1, Stk.get, Stk.set, hQ, encBan, List.append_assoc]
  · simp only [hsrc2, List.length_replicate]
    have : (w + 1) * (4 * u + 16) = (w + 1) * 8 + (w + 1) * (4 * u + 8) := by ring
    omega

theorem emitLitBan_spec (polFlip : Bool) (w vi u c2 : Nat) (v : Reg) (s : Stk)
    (hW : s.Wstk = List.replicate w true) (hWb : s.Wb = [])
    (hQ : s.Q = []) (hQb : s.Qb = []) (hTmp : s.Tmp = [])
    (hV : s.Vidx = List.replicate vi true) (hU : s.Uocc = List.replicate u true) :
    ∃ p' : Bool,
      Run (emitLitBan polFlip c2) v s (nrm { v with par := p' })
        ({ s with OutRev :=
          (encBan w ((vi, if polFlip then (if v.pol then 0 else 1) else (if v.pol then 1 else 0)),
            (u, c2))).reverse ++ s.OutRev })
        ((w + 1) * (4 * vi + 4 * u + 16) + 7 * vi + 7 * u + 16) := by
  have r1 := copyS_spec .Vidx .Tmp .Q (by decide) (by decide) (by decide) v s hTmp
  let s1 := s.set .Q ((s.get .Vidx).reverse ++ s.get .Q)
  obtain ⟨p1, r2⟩ := emitQ_spec w vi (nrm v) s1
    (by simp [s1, Stk.set, hW]) (by simp [s1, Stk.set, hWb])
    (by simp [s1, Stk.get, Stk.set, hV, hQ]) (by simp [s1, Stk.set, hQb])
  let v2 := nrm { nrm v with par := p1 }
  let s2 := { s1 with Q := [], OutRev := (bits w vi).reverse ++ s1.OutRev }
  have r3 := Run.wpush .OutRev (fun v => if polFlip then !v.pol else v.pol) v2 s2
  let s3 := s2.set .OutRev ((if polFlip then !v2.pol else v2.pol) :: s2.get .OutRev)
  have r4 := Run.wpush .OutRev ff v2 s3
  let s4 := s3.set .OutRev (false :: s3.get .OutRev)
  have r5 := copyS_spec .Uocc .Tmp .Q (by decide) (by decide) (by decide) v2 s4
    (by simp [s4, s3, s2, s1, Stk.get, Stk.set, hTmp])
  let s5 := s4.set .Q ((s4.get .Uocc).reverse ++ s4.get .Q)
  obtain ⟨p2, r6⟩ := emitQ_spec w u (nrm v2) s5
    (by simp [s5, s4, s3, s2, s1, Stk.set, hW]) (by simp [s5, s4, s3, s2, s1, Stk.set, hWb])
    (by simp [s5, s4, s3, s2, s1, Stk.get, Stk.set, hU]) (by simp [s5, s4, s3, s2, s1, Stk.set, hQb])
  refine ⟨p2, Run.conv (Run.seq r1 (Run.seq r2 (Run.seq r3 (Run.seq r4 (Run.seq r5
    (Run.seq r6 (pushColor_spec c2 _ _))))))) ?_ ?_ ?_⟩
  · cases v; simp [v2, nrm]
  · apply Stk.ext_get
    · simp [s5, s4, s3, s2, s1, set_inp]
    · simp [s5, s4, s3, s2, s1, set_out]
    · intro a
      cases a <;> simp only [s5, s4, s3, s2, s1, v2, Stk.get, Stk.set, hQ, encBan, nrm]
      cases polFlip <;> cases v.pol <;> simp [bits, List.range_succ, List.append_assoc] <;> decide
  · simp only [s4, s3, s2, s1, Stk.get, Stk.set, hV, hU, List.length_replicate]
    have : (w + 1) * (4 * vi + 4 * u + 16) = (w + 1) * (4 * vi + 8) + (w + 1) * (4 * u + 8) := by ring
    omega

theorem emitTransOne_spec (w u c1 c2 : Nat) (v : Reg) (s : Stk)
    (hW : s.Wstk = List.replicate w true) (hWb : s.Wb = [])
    (hQ : s.Q = []) (hQb : s.Qb = []) (hTmp : s.Tmp = [])
    (hU : s.Uocc = List.replicate u true) :
    ∃ p' : Bool,
      Run (emitTransOne c1 c2) v s (nrm { v with par := p' })
        ({ s with OutRev := (encBan w ((u, c1), (u + 1, c2))).reverse ++ s.OutRev })
        ((w + 1) * (8 * u + 20) + 14 * u + 20) := by
  have r1 := copyS_spec .Uocc .Tmp .Q (by decide) (by decide) (by decide) v s hTmp
  let s1 := s.set .Q ((s.get .Uocc).reverse ++ s.get .Q)
  obtain ⟨p1, r2⟩ := emitQ_spec w u (nrm v) s1
    (by simp [s1, Stk.set, hW]) (by simp [s1, Stk.set, hWb])
    (by simp [s1, Stk.get, Stk.set, hU, hQ]) (by simp [s1, Stk.set, hQb])
  let v2 := nrm { nrm v with par := p1 }
  let s2 := { s1 with Q := [], OutRev := (bits w u).reverse ++ s1.OutRev }
  have r3 := pushColor_spec c1 v2 s2
  let s3 := { s2 with OutRev := (bits 2 c1).reverse ++ s2.OutRev }
  have r4 := copyS_spec .Uocc .Tmp .Q (by decide) (by decide) (by decide) v2 s3
    (by simp [s3, s2, s1, Stk.get, Stk.set, hTmp])
  let s4 := s3.set .Q ((s3.get .Uocc).reverse ++ s3.get .Q)
  have r5 := Run.wpush .Q tt (nrm v2) s4
  let s5 := s4.set .Q (true :: s4.get .Q)
  obtain ⟨p2, r6⟩ := emitQ_spec w (u + 1) (nrm v2) s5
    (by simp [s5, s4, s3, s2, s1, Stk.set, hW]) (by simp [s5, s4, s3, s2, s1, Stk.set, hWb])
    (by simp [s5, s4, s3, s2, s1, Stk.get, Stk.set, hU, List.replicate_succ])
    (by simp [s5, s4, s3, s2, s1, Stk.set, hQb])
  refine ⟨p2, Run.conv (Run.seq r1 (Run.seq r2 (Run.seq r3 (Run.seq r4 (Run.seq r5
    (Run.seq r6 (pushColor_spec c2 _ _))))))) ?_ ?_ ?_⟩
  · cases v; simp [v2, nrm]
  · apply Stk.ext_get
    · simp [s5, s4, s3, s2, s1, set_inp]
    · simp [s5, s4, s3, s2, s1, set_out]
    · intro a; cases a <;> simp [s5, s4, s3, s2, s1, Stk.get, Stk.set, hQ, encBan, List.append_assoc]
  · simp only [s3, s2, s1, Stk.get, Stk.set, hU, List.length_replicate]
    have : (w + 1) * (8 * u + 20) = (w + 1) * (4 * u + 8) + (w + 1) * (4 * (u + 1) + 8) := by ring
    omega

end MachineDefs

section Phases1to3

open Turing

def encodeEntry (ds : List Bool) : List Bool :=
  (ds.flatMap fun d => [true, d]) ++ [false]

def encodeVars (vs : List (List Bool)) : List Bool :=
  vs.flatMap encodeEntry

theorem encodeEntry_length (ds : List Bool) : (encodeEntry ds).length = 2 * ds.length + 1 := by
  unfold encodeEntry
  induction ds with
  | nil => simp
  | cons d ds ih => simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.length_cons] at ih ⊢; omega

theorem encodeVars_append (vs : List (List Bool)) (q : List Bool) :
    encodeVars (vs ++ [q]) = encodeVars vs ++ encodeEntry q := by
  simp [encodeVars]

theorem sum_foldl_insUniq_le {α : Type} [DecidableEq α] (w : α → Nat) :
    ∀ (l acc : List α), ((l.foldl insUniq acc).map w).sum ≤ (acc.map w).sum + (l.map w).sum := by
  intro l
  induction l with
  | nil => intro acc; simp
  | cons a l ih =>
    intro acc
    simp only [List.foldl_cons, insUniq, List.map_cons, List.sum_cons]
    split
    · have h := ih acc; omega
    · have h := ih (acc ++ [a])
      simp only [List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
        List.sum_nil] at h
      omega

theorem sum_eraseDups_le {α : Type} [DecidableEq α] (w : α → Nat) (l : List α) :
    (l.eraseDups.map w).sum ≤ (l.map w).sum := by
  rw [eraseDups_eq_foldl]
  simpa using sum_foldl_insUniq_le w l []

theorem order_length_le_occ (F : CNF) :
    ((F.flatten).map Prod.fst).eraseDups.length ≤ F.flatten.length := by
  have h := sum_eraseDups_le (fun _ : Nat => 1) ((F.flatten).map Prod.fst)
  have h1 : ∀ (l : List Nat), (l.map (fun _ => 1)).sum = l.length := by
    intro l; induction l with | nil => rfl | cons _ _ ih => simp ; omega
  rw [h1, h1, List.length_map] at h
  exact h

theorem encodeLiteral_length (l : Literal) :
    (encodeLiteral l).length = 2 * l.1.bits.length + 4 := by
  rw [encodeLiteral_eq]
  simp only [List.length_cons, vcode, List.length_append, List.length_nil]
  have h : ∀ (ds : List Bool), (ds.flatMap fun d => [true, d]).length = 2 * ds.length := by
    intro ds; induction ds with | nil => rfl | cons _ _ ih => simp [ih]; omega
  rw [h]

theorem encodeClause_length (c : Clause) :
    (encodeClause c).length = (c.map (fun l => 2 * l.1.bits.length + 4)).sum + 2 := by
  unfold encodeClause
  simp only [List.length_append, List.length_cons, List.length_nil]
  congr 1
  induction c with
  | nil => rfl
  | cons l c ih =>
    simp only [List.flatMap_cons, List.length_append, encodeLiteral_length, List.map_cons,
      List.sum_cons, ih]

theorem encodeVars_order_len (F : CNF) :
    (encodeVars (((F.flatten).map Prod.fst).eraseDups.map Nat.bits)).length ≤ (encodeCNF F).length := by
  have hsum : ∀ (vs : List (List Bool)), (encodeVars vs).length = (vs.map (fun ds => 2 * ds.length + 1)).sum := by
    intro vs
    induction vs with
    | nil => rfl
    | cons ds vs ih =>
      simp only [encodeVars, List.flatMap_cons, List.length_append, encodeEntry_length,
        List.map_cons, List.sum_cons, ← ih]
  rw [hsum, List.map_map]
  have h1 := sum_eraseDups_le (fun v : Nat => 2 * v.bits.length + 1) ((F.flatten).map Prod.fst)
  refine le_trans h1 ?_
  clear h1 hsum
  induction F with
  | nil => simp [encodeCNF]
  | cons c cs ih =>
    have hc : ((c.map Prod.fst).map (fun v : Nat => 2 * v.bits.length + 1)).sum ≤
        (c.map (fun l : Literal => 2 * l.1.bits.length + 4)).sum := by
      induction c with
      | nil => simp
      | cons l c ihc =>
        simp only [List.map_cons, List.sum_cons]
        exact Nat.add_le_add (by omega) ihc
    have he : encodeCNF (c :: cs) = encodeClause c ++ encodeCNF cs := by simp [encodeCNF]
    rw [he]
    simp only [List.flatten_cons, List.map_append, List.sum_append, List.length_append,
      encodeClause_length]
    omega

theorem four_mul_occ_le (F : CNF) : 4 * F.flatten.length ≤ (encodeCNF F).length := by
  induction F with
  | nil => simp [encodeCNF]
  | cons c cs ih =>
    have hc : 4 * c.length ≤ (c.map (fun l : Literal => 2 * l.1.bits.length + 4)).sum := by
      induction c with
      | nil => simp
      | cons l c ihc =>
        simp only [List.length_cons, List.map_cons, List.sum_cons]
        exact Nat.le_trans (by omega : 4 * (c.length + 1) ≤ (2 * l.1.bits.length + 4) + 4 * c.length)
          (Nat.add_le_add_left ihc _)
    have he : encodeCNF (c :: cs) = encodeClause c ++ encodeCNF cs := by simp [encodeCNF]
    rw [he]
    simp only [List.flatten_cons, List.length_append, encodeClause_length]
    omega

theorem two_mul_clauses_le (F : CNF) : 2 * F.length ≤ (encodeCNF F).length := by
  induction F with
  | nil => simp [encodeCNF]
  | cons c cs ih =>
    have he : encodeCNF (c :: cs) = encodeClause c ++ encodeCNF cs := by simp [encodeCNF]
    rw [he]
    simp only [List.length_append, List.length_cons, encodeClause_length]
    omega

theorem width_le_self (n : Nat) (hn : 1 ≤ n) : width n ≤ n := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    unfold width
    by_cases h1 : n = 1
    · subst h1; decide
    · have hge2 : 2 ≤ n := by omega
      rw [Nat.log2_def]
      simp only [hge2, ite_true]
      have hdiv_lt : n / 2 < n := Nat.div_lt_self (by omega) (by omega)
      have hdiv_ge1 : 1 ≤ n / 2 := by omega
      have hih := ih (n / 2) hdiv_lt hdiv_ge1
      unfold width at hih
      omega

theorem foldl_insUniq_map {α β : Type} [DecidableEq α] [DecidableEq β] (g : α → β)
    (hg : Function.Injective g) :
    ∀ (l acc : List α), (l.map g).foldl insUniq (acc.map g) = (l.foldl insUniq acc).map g := by
  intro l
  induction l with
  | nil => intro acc; rfl
  | cons a l ih =>
    intro acc
    simp only [List.map_cons, List.foldl_cons, insUniq]
    have hmem : g a ∈ acc.map g ↔ a ∈ acc := by
      simp only [List.mem_map]
      constructor
      · rintro ⟨x, hx, hgx⟩; exact hg hgx ▸ hx
      · intro ha; exact ⟨a, ha, rfl⟩
    by_cases ha : a ∈ acc
    · simp only [ha, hmem.mpr ha, ite_true]
      exact ih acc
    · have hna : g a ∉ acc.map g := fun h => ha (hmem.mp h)
      simp only [ha, hna, ite_false]
      have hcat : acc.map g ++ [g a] = (acc ++ [a]).map g := by simp
      rw [hcat]
      exact ih (acc ++ [a])

theorem idxOf_map_injective {α β : Type} [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β] (g : α → β)
    (hg : Function.Injective g) :
    ∀ (l : List α) (a : α), (l.map g).idxOf (g a) = l.idxOf a := by
  intro l a
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [List.map_cons, List.idxOf_cons]
    by_cases h : x = a
    · subst h; simp
    · have h' : g x ≠ g a := fun e => h (hg e)
      simp [beq_false_of_ne h, beq_false_of_ne h', ih]

theorem vs_len_le_encodeVars (vs : List (List Bool)) : vs.length ≤ (encodeVars vs).length := by
  induction vs with
  | nil => simp [encodeVars]
  | cons ds vs ih =>
    simp only [encodeVars, List.flatMap_cons, List.length_append, List.length_cons,
      encodeEntry_length] at ih ⊢
    omega

def lookupBody : Pg :=
  Prog.seq (wpush .SeenVb (fun v => v.b0))
    (Prog.ite (fun v => v.expectData)
      (Prog.seq (Prog.load fun v => { v with expectData := false })
        (Prog.seq
          (wpop .CurV fun v o => match o with
            | some c => { v with u := true, eqFlag := v.eqFlag && (c == v.b0), par := c }
            | none => { v with u := false, eqFlag := false })
          (Prog.ite (fun v => v.u) (wpush .CurVb (fun v => v.par)) (Prog.load id))))
      (Prog.ite (fun v => v.b0)
        (Prog.load fun v => { v with expectData := true })
        (Prog.seq
          (wpop .CurV fun v o => match o with
            | some c => { v with u := true, par := c }
            | none => { v with u := false })
          (Prog.seq
            (Prog.ite (fun v => v.u) (wpush .CurV (fun v => v.par)) (Prog.load id))
            (Prog.seq
              (Prog.ite (fun v => v.eqFlag && !v.u)
                (Prog.load fun v => { v with found := true })
                (Prog.ite (fun v => !v.found) (wpush .Vidx tt) (Prog.load id)))
              (Prog.seq (move .CurVb .CurV)
                (Prog.load fun v => { v with eqFlag := true })))))))

def lookupLoop : Pg :=
  forPop .SeenV (fun v b => { v with b0 := b }) id lookupBody

def lookupP : Pg :=
  Prog.seq (Prog.load fun v => { v with expectData := false, eqFlag := true, found := false })
    lookupLoop

theorem noTouch_lookupP (k : K) (h1 : K.w .SeenV ≠ k) (h2 : K.w .SeenVb ≠ k)
    (h3 : K.w .CurV ≠ k) (h4 : K.w .CurVb ≠ k) (h5 : K.w .Vidx ≠ k) :
    NoTouch k lookupP := by
  simp [lookupP, lookupLoop, lookupBody, noTouch_seq, noTouch_load, noTouch_forPop, noTouch_wpush,
    noTouch_wpop, noTouch_ite, noTouch_move, h1, h2, h3, h4, h5]

theorem wf_lookupP : WF lookupP := by
  simp [lookupP, lookupLoop, lookupBody, wf_seq, wf_load, wf_forPop, wf_wpush, wf_wpop, wf_ite,
    wf_move, noTouch_seq, noTouch_load, noTouch_wpush, noTouch_wpop, noTouch_ite, noTouch_move]

theorem noTouch_lookupBody : NoTouch (K.w .SeenV) lookupBody := by
  simp [lookupBody, noTouch_seq, noTouch_wpush, noTouch_wpop, noTouch_ite, noTouch_load,
    noTouch_move]

theorem exec_lookupLoop_cons (v : Reg) (s : Stk) (x : Bool) (xs : List Bool)
    (h : s.get .SeenV = x :: xs) :
    exec lookupLoop ⟨v, toFun s⟩ =
      exec lookupLoop (exec lookupBody ⟨{ v with b0 := x, go := true }, toFun (s.set .SeenV xs)⟩) := by
  exact exec_forPop_cons .SeenV (fun v b => { v with b0 := b }) id lookupBody v s x xs h noTouch_lookupBody

theorem cost_lookupLoop_cons (v : Reg) (s : Stk) (x : Bool) (xs : List Bool)
    (h : s.get .SeenV = x :: xs) :
    cost lookupLoop ⟨v, toFun s⟩ =
      cost lookupLoop (exec lookupBody ⟨{ v with b0 := x, go := true }, toFun (s.set .SeenV xs)⟩) +
        (cost lookupBody ⟨{ v with b0 := x, go := true }, toFun (s.set .SeenV xs)⟩ + 1) := by
  exact cost_forPop_cons .SeenV (fun v b => { v with b0 := b }) id lookupBody v s x xs h noTouch_lookupBody

def cmpDrop : Bool → List Bool → List Bool → List Bool → Bool × List Bool × List Bool
  | eqf, [], cur, curB => (eqf, cur, curB)
  | _, _ :: ds, [], curB => cmpDrop false ds [] curB
  | eqf, d :: ds, c :: cur, curB => cmpDrop (eqf && (c == d)) ds cur (c :: curB)

theorem cmpDrop_inv : ∀ (ds cur curB : List Bool) (eqf : Bool),
    let r := cmpDrop eqf ds cur curB
    r.2.2.reverse ++ r.2.1 = curB.reverse ++ cur ∧
      r.2.2.length ≤ curB.length + ds.length ∧
      ((r.1 = true ∧ r.2.1 = []) ↔ (eqf = true ∧ cur = ds)) := by
  intro ds
  induction ds with
  | nil =>
    intro cur curB eqf
    simp [cmpDrop]
  | cons d ds ih =>
    intro cur curB eqf
    cases cur with
    | nil =>
      obtain ⟨h1, h2, h3⟩ := ih [] curB false
      refine ⟨h1, by simp only [cmpDrop, List.length_cons]; omega, ?_⟩
      simp only [cmpDrop]
      constructor
      · intro h; have := h3.mp h; simp at this
      · intro h; simp at h
    | cons c cur =>
      obtain ⟨h1, h2, h3⟩ := ih cur (c :: curB) (eqf && (c == d))
      refine ⟨by simpa [cmpDrop, List.reverse_cons, List.append_assoc] using h1,
        by simp only [cmpDrop, List.length_cons] at h2 ⊢; omega, ?_⟩
      simp only [cmpDrop]
      rw [h3]
      simp only [Bool.and_eq_true, beq_iff_eq, List.cons.injEq]
      tauto

theorem lookupLoop_digits (ds : List Bool) :
    ∀ (rest : List Bool) (v : Reg) (s : Stk),
      v.expectData = false →
      s.SeenV = (ds.flatMap fun d => [true, d]) ++ rest →
      ∃ (u' b0' par' : Bool),
        let r := cmpDrop v.eqFlag ds s.CurV s.CurVb
        let vEnd : Reg := { v with go := true, u := u', b0 := b0', expectData := false, eqFlag := r.1, par := par' }
        let sEnd : Stk := { s with SeenV := rest, SeenVb := (ds.flatMap fun d => [true, d]).reverse ++ s.SeenVb, CurV := r.2.1, CurVb := r.2.2 }
        exec lookupLoop ⟨v, toFun s⟩ = exec lookupLoop ⟨vEnd, toFun sEnd⟩ ∧
          cost lookupLoop ⟨v, toFun s⟩ ≤ cost lookupLoop ⟨vEnd, toFun sEnd⟩ + 16 * ds.length := by
  induction ds with
  | nil =>
    intro rest v s hexp hSV
    refine ⟨v.u, v.b0, v.par, ?_, ?_⟩
    · cases rest with
      | nil =>
        have hg : s.get .SeenV = [] := hSV
        rw [lookupLoop, exec_forPop_nil _ _ _ _ _ _ hg, exec_forPop_nil _ _ _ _ _ _ rfl]
        refine St_eq _ _ _ _ (by cases v; simp_all [nrm, cmpDrop]) ?_
        apply Stk.ext_get
        · rfl
        · rfl
        · intro a; cases a <;> simp [Stk.get, hSV, cmpDrop]
      | cons x xs =>
        have hg : s.get .SeenV = x :: xs := hSV
        rw [lookupLoop, exec_forPop_cons _ _ _ _ _ _ x xs hg noTouch_lookupBody,
          exec_forPop_cons _ _ _ _ _ _ x xs rfl noTouch_lookupBody]
        congr 2
        refine St_eq _ _ _ _ (by cases v; simp_all [cmpDrop]) ?_
        apply Stk.ext_get
        · simp [set_inp]
        · simp [set_out]
        · intro a; cases a <;> simp [Stk.get, Stk.set, cmpDrop]
    · cases rest with
      | nil =>
        have hg : s.get .SeenV = [] := hSV
        rw [lookupLoop, cost_forPop_nil _ _ _ _ _ _ hg, cost_forPop_nil _ _ _ _ _ _ rfl]
        omega
      | cons x xs =>
        have hg : s.get .SeenV = x :: xs := hSV
        rw [lookupLoop, cost_forPop_cons _ _ _ _ _ _ x xs hg noTouch_lookupBody,
          cost_forPop_cons _ _ _ _ _ _ x xs rfl noTouch_lookupBody]
        have heq : (⟨{ ({ v with b0 := x }) with go := true }, toFun (s.set .SeenV xs)⟩ : St K Γ Reg) =
            ⟨{ ({ ({ v with go := true, u := v.u, b0 := v.b0, expectData := false, eqFlag := v.eqFlag, par := v.par }) with b0 := x }) with go := true },
              toFun (({ s with SeenV := x :: xs, SeenVb := s.SeenVb, CurV := s.CurV, CurVb := s.CurVb }).set .SeenV xs)⟩ := by
          refine St_eq _ _ _ _ (by cases v; simp_all) ?_
          apply Stk.ext_get
          · simp [set_inp]
          · simp [set_out]
          · intro a; cases a <;> simp [Stk.get, Stk.set]
        simp only [List.flatMap_nil, List.reverse_nil, List.nil_append, cmpDrop, List.length_nil,
          Nat.mul_zero, Nat.add_zero]
        rw [heq]
  | cons d ds ih =>
    intro rest v s hexp hSV
    have hSV1 : s.get .SeenV = true :: (d :: ((ds.flatMap fun d => [true, d]) ++ rest)) := by
      simpa [Stk.get] using hSV
    let v1 : Reg := { v with go := true, b0 := true, expectData := true }
    let s1 : Stk := { s with SeenV := d :: ((ds.flatMap fun d => [true, d]) ++ rest), SeenVb := true :: s.SeenVb }
    have hSV2 : s1.get .SeenV = d :: ((ds.flatMap fun d => [true, d]) ++ rest) := rfl
    have hstep1 : exec lookupBody ⟨{ v with b0 := true, go := true }, toFun (s.set .SeenV (d :: ((ds.flatMap fun d => [true, d]) ++ rest)))⟩ =
        ⟨v1, toFun s1⟩ ∧
        cost lookupBody ⟨{ v with b0 := true, go := true }, toFun (s.set .SeenV (d :: ((ds.flatMap fun d => [true, d]) ++ rest)))⟩ ≤ 5 := by
      refine ⟨?_, ?_⟩
      · simp only [lookupBody, exec, exec_wpush, hexp, Bool.false_eq_true, ite_false, ite_true]
        refine St_eq _ _ _ _ (by cases v; rfl) ?_
        apply Stk.ext_get
        · simp [s1, set_inp]
        · simp [s1, set_out]
        · intro a; cases a <;> simp [s1, Stk.get, Stk.set]
      · simp [lookupBody, exec, cost, wpush, hexp]
    cases hcur : s.CurV with
    | nil =>
      let v2 : Reg := { v with go := true, u := false, b0 := d, expectData := false, eqFlag := false }
      let s2 : Stk := { s with SeenV := (ds.flatMap fun d => [true, d]) ++ rest, SeenVb := d :: true :: s.SeenVb }
      have hstep2 : exec lookupBody ⟨{ v1 with b0 := d, go := true }, toFun (s1.set .SeenV ((ds.flatMap fun d => [true, d]) ++ rest))⟩ =
          ⟨v2, toFun s2⟩ ∧
          cost lookupBody ⟨{ v1 with b0 := d, go := true }, toFun (s1.set .SeenV ((ds.flatMap fun d => [true, d]) ++ rest))⟩ ≤ 8 := by
        refine ⟨?_, ?_⟩
        · simp only [lookupBody, exec, exec_wpush, exec_wpop, v1, s1, Stk.get, Stk.set, hcur,
            List.head?_nil, List.tail_nil, ite_true, Bool.false_eq_true, ite_false]
          refine St_eq _ _ _ _ (by cases v; rfl) ?_
          apply Stk.ext_get
          · rfl
          · rfl
          · intro a; cases a <;> simp [s2, Stk.get, hcur]
        · simp [lookupBody, exec, cost, wpush, wpop, v1, s1, Stk.set, hcur]
      obtain ⟨u', b0', par', he, hc⟩ := ih rest v2 s2 rfl rfl
      refine ⟨u', b0', par', ?_, ?_⟩
      · rw [exec_lookupLoop_cons _ _ true _ hSV1, hstep1.1, exec_lookupLoop_cons _ _ d _ hSV2, hstep2.1, he]
        congr 1
        refine St_eq _ _ _ _ (by cases v; simp [v2, s2, cmpDrop, hcur]) ?_
        apply Stk.ext_get
        · rfl
        · rfl
        · intro a; cases a <;> simp [s2, v2, Stk.get, cmpDrop, hcur, List.append_assoc]
      · rw [cost_lookupLoop_cons _ _ true _ hSV1, hstep1.1, cost_lookupLoop_cons _ _ d _ hSV2, hstep2.1]
        have hce : cost lookupLoop ⟨{ v2 with go := true, u := u', b0 := b0', expectData := false, eqFlag := (cmpDrop v2.eqFlag ds s2.CurV s2.CurVb).1, par := par' },
            toFun { s2 with SeenV := rest, SeenVb := (ds.flatMap fun d => [true, d]).reverse ++ s2.SeenVb, CurV := (cmpDrop v2.eqFlag ds s2.CurV s2.CurVb).2.1, CurVb := (cmpDrop v2.eqFlag ds s2.CurV s2.CurVb).2.2 }⟩ =
            cost lookupLoop ⟨{ v with go := true, u := u', b0 := b0', expectData := false, eqFlag := (cmpDrop v.eqFlag (d :: ds) s.CurV s.CurVb).1, par := par' },
              toFun { s with SeenV := rest, SeenVb := ((d :: ds).flatMap fun d => [true, d]).reverse ++ s.SeenVb, CurV := (cmpDrop v.eqFlag (d :: ds) s.CurV s.CurVb).2.1, CurVb := (cmpDrop v.eqFlag (d :: ds) s.CurV s.CurVb).2.2 }⟩ := by
          congr 1
          refine St_eq _ _ _ _ (by cases v; simp [v2, s2, cmpDrop, hcur]) ?_
          apply Stk.ext_get
          · rfl
          · rfl
          · intro a; cases a <;> simp [s2, v2, Stk.get, cmpDrop, hcur, List.append_assoc]
        have hc' := hc
        rw [hce, hcur] at hc'
        have hs1 := hstep1.2
        have hs2 := hstep2.2
        have hlen : (d :: ds).length = ds.length + 1 := rfl
        omega
    | cons c cur =>
      let v2 : Reg := { v with go := true, u := true, b0 := d, expectData := false, eqFlag := v.eqFlag && (c == d), par := c }
      let s2 : Stk := { s with SeenV := (ds.flatMap fun d => [true, d]) ++ rest, SeenVb := d :: true :: s.SeenVb, CurV := cur, CurVb := c :: s.CurVb }
      have hstep2 : exec lookupBody ⟨{ v1 with b0 := d, go := true }, toFun (s1.set .SeenV ((ds.flatMap fun d => [true, d]) ++ rest))⟩ =
          ⟨v2, toFun s2⟩ ∧
          cost lookupBody ⟨{ v1 with b0 := d, go := true }, toFun (s1.set .SeenV ((ds.flatMap fun d => [true, d]) ++ rest))⟩ ≤ 8 := by
        refine ⟨?_, ?_⟩
        · simp only [lookupBody, exec, exec_wpush, exec_wpop, v1, s1, Stk.get, Stk.set, hcur,
            List.head?_cons, List.tail_cons, ite_true]
          refine St_eq _ _ _ _ (by cases v; rfl) ?_
          apply Stk.ext_get
          · rfl
          · rfl
          · intro a; cases a <;> simp [s2, Stk.get]
        · simp [lookupBody, exec, cost, wpush, wpop, v1, s1, Stk.set, hcur]
      obtain ⟨u', b0', par', he, hc⟩ := ih rest v2 s2 rfl rfl
      refine ⟨u', b0', par', ?_, ?_⟩
      · rw [exec_lookupLoop_cons _ _ true _ hSV1, hstep1.1, exec_lookupLoop_cons _ _ d _ hSV2, hstep2.1, he]
        congr 1
        refine St_eq _ _ _ _ (by cases v; simp [v2, s2, cmpDrop]) ?_
        apply Stk.ext_get
        · rfl
        · rfl
        · intro a; cases a <;> simp [s2, v2, Stk.get, cmpDrop, List.append_assoc]
      · rw [cost_lookupLoop_cons _ _ true _ hSV1, hstep1.1, cost_lookupLoop_cons _ _ d _ hSV2, hstep2.1]
        have hce : cost lookupLoop ⟨{ v2 with go := true, u := u', b0 := b0', expectData := false, eqFlag := (cmpDrop v2.eqFlag ds s2.CurV s2.CurVb).1, par := par' },
            toFun { s2 with SeenV := rest, SeenVb := (ds.flatMap fun d => [true, d]).reverse ++ s2.SeenVb, CurV := (cmpDrop v2.eqFlag ds s2.CurV s2.CurVb).2.1, CurVb := (cmpDrop v2.eqFlag ds s2.CurV s2.CurVb).2.2 }⟩ =
            cost lookupLoop ⟨{ v with go := true, u := u', b0 := b0', expectData := false, eqFlag := (cmpDrop v.eqFlag (d :: ds) s.CurV s.CurVb).1, par := par' },
              toFun { s with SeenV := rest, SeenVb := ((d :: ds).flatMap fun d => [true, d]).reverse ++ s.SeenVb, CurV := (cmpDrop v.eqFlag (d :: ds) s.CurV s.CurVb).2.1, CurVb := (cmpDrop v.eqFlag (d :: ds) s.CurV s.CurVb).2.2 }⟩ := by
          congr 1
          refine St_eq _ _ _ _ (by cases v; simp [v2, s2, cmpDrop, hcur]) ?_
          apply Stk.ext_get
          · rfl
          · rfl
          · intro a; cases a <;> simp [s2, v2, Stk.get, cmpDrop, hcur, List.append_assoc]
        have hc' := hc
        rw [hce, hcur] at hc'
        have hs1 := hstep1.2
        have hs2 := hstep2.2
        have hlen : (d :: ds).length = ds.length + 1 := rfl
        omega

theorem lookupBody_false_spec (q : List Bool) (v : Reg) (s : Stk)
    (hexp : v.expectData = false) (hb0 : v.b0 = false)
    (hinv : s.CurVb.reverse ++ s.CurV = q) :
    ∃ (par' : Bool),
      let hit : Bool := v.eqFlag && s.CurV.isEmpty
      Run lookupBody v s
        (nrm { v with expectData := false, eqFlag := true, found := v.found || hit, par := par' })
        { s with SeenVb := false :: s.SeenVb, CurV := q, CurVb := [], Vidx := if hit || v.found then s.Vidx else true :: s.Vidx }
        (2 * s.CurVb.length + 14) := by
  let s1 := s.set .SeenVb (false :: s.SeenVb)
  have r1 : Run (wpush .SeenVb (fun v => v.b0)) v s v s1 1 := by
    refine Run.conv (Run.wpush .SeenVb (fun v => v.b0) v s) rfl ?_ (le_refl _)
    simp [s1, Stk.get, hb0]
  have r2 := Run.wpop .CurV (fun v o => match o with
    | some c => { v with u := true, par := c }
    | none => { v with u := false }) v s1
  cases hcur : s.CurV with
  | nil =>
    let v2 : Reg := { v with u := false }
    let s2 : Stk := s1
    have r2' : Run (wpop .CurV (fun v o => match o with
        | some c => { v with u := true, par := c }
        | none => { v with u := false })) v s1 v2 s2 1 := by
      refine Run.conv r2 (by simp [v2, s1, Stk.get, Stk.set, hcur]) ?_ (le_refl _)
      apply Stk.ext_get
      · simp [s2, s1, set_inp]
      · simp [s2, s1, set_out]
      · intro a; cases a <;> simp [s2, s1, Stk.get, Stk.set, hcur]
    have r3 := Run.ite_false (c := fun v : Reg => v.u) (p := wpush .CurV (fun v => v.par))
      rfl (Run.load id v2 s2)
    have r4 : Run (Prog.ite (fun v => v.eqFlag && !v.u)
        (Prog.load fun v => { v with found := true })
        (Prog.ite (fun v => !v.found) (wpush .Vidx tt) (Prog.load id)))
        v2 s2 { v2 with found := v.found || v.eqFlag }
        { s2 with Vidx := if v.eqFlag || v.found then s2.Vidx else true :: s2.Vidx } 4 := by
      cases heq : v.eqFlag
      · cases hf : v.found
        · refine Run.conv (Run.ite_false (by simp [v2, heq]) (Run.ite_true (by simp [v2, hf])
            (Run.wpush .Vidx tt v2 s2))) ?_ ?_ (by omega)
          · cases v; simp_all [v2]
          · apply Stk.ext_get <;> (try rfl); intro a; cases a <;> simp [Stk.get, Stk.set, tt]
        · refine Run.conv (Run.ite_false (by simp [v2, heq]) (Run.ite_false (by simp [v2, hf])
            (Run.load id v2 s2))) ?_ ?_ (by omega)
          · cases v; simp_all [v2]
          · simp
      · refine Run.conv (Run.ite_true (by simp [v2, heq])
          (Run.load (fun v => { v with found := true }) v2 s2)) ?_ ?_ (by omega)
        · cases v; simp_all [v2]
        · simp
    have r5 := Run.move .CurVb .CurV (by decide) { v2 with found := v.found || v.eqFlag }
      { s2 with Vidx := if v.eqFlag || v.found then s2.Vidx else true :: s2.Vidx }
    have rInner := Run.seq r2' (Run.seq r3 (Run.seq r4 (Run.seq r5
      (Run.load (fun v => { v with eqFlag := true }) _ _))))
    refine ⟨v.par, Run.conv (Run.seq r1 (Run.ite_false hexp (Run.ite_false hb0 rInner))) ?_ ?_ ?_⟩
    · cases v; simp [v2, nrm, hexp]
    · apply Stk.ext_get
      · simp [s2, s1, set_inp]
      · simp [s2, s1, set_out]
      · rw [hcur, List.append_nil] at hinv
        intro a; cases a <;> simp [s2, s1, Stk.get, Stk.set, hcur, hinv]
    · simp only [s2, s1, Stk.get, Stk.set]
      omega
  | cons c cur =>
    let v2 : Reg := { v with u := true, par := c }
    let s2 : Stk := s1.set .CurV cur
    have r2' : Run (wpop .CurV (fun v o => match o with
        | some c => { v with u := true, par := c }
        | none => { v with u := false })) v s1 v2 s2 1 := by
      refine Run.conv r2 (by simp [v2, s1, Stk.get, Stk.set, hcur]) ?_ (le_refl _)
      apply Stk.ext_get
      · simp [s2, s1, set_inp]
      · simp [s2, s1, set_out]
      · intro a; cases a <;> simp [s2, s1, Stk.get, Stk.set, hcur]
    have r3 : Run (Prog.ite (fun v => v.u) (wpush .CurV (fun v => v.par)) (Prog.load id))
        v2 s2 v2 s1 2 := by
      refine Run.conv (Run.ite_true rfl (Run.wpush .CurV (fun v => v.par) v2 s2)) rfl ?_ (le_refl _)
      apply Stk.ext_get
      · simp [s2, s1, set_inp]
      · simp [s2, s1, set_out]
      · intro a; cases a <;> simp [s2, s1, v2, Stk.get, Stk.set, hcur]
    have r4 : Run (Prog.ite (fun v => v.eqFlag && !v.u)
        (Prog.load fun v => { v with found := true })
        (Prog.ite (fun v => !v.found) (wpush .Vidx tt) (Prog.load id)))
        v2 s1 v2 { s1 with Vidx := if v.found then s1.Vidx else true :: s1.Vidx } 4 := by
      cases hf : v.found
      · refine Run.conv (Run.ite_false (by simp [v2]) (Run.ite_true (by simp [v2, hf])
          (Run.wpush .Vidx tt v2 s1))) rfl ?_ (by omega)
        apply Stk.ext_get <;> (try rfl); intro a; cases a <;> simp [Stk.get, Stk.set, tt]
      · refine Run.conv (Run.ite_false (by simp [v2]) (Run.ite_false (by simp [v2, hf])
          (Run.load id v2 s1))) rfl ?_ (by omega)
        simp
    have r5 := Run.move .CurVb .CurV (by decide) v2
      { s1 with Vidx := if v.found then s1.Vidx else true :: s1.Vidx }
    have rInner := Run.seq r2' (Run.seq r3 (Run.seq r4 (Run.seq r5
      (Run.load (fun v => { v with eqFlag := true }) _ _))))
    refine ⟨c, Run.conv (Run.seq r1 (Run.ite_false hexp (Run.ite_false hb0 rInner))) ?_ ?_ ?_⟩
    · cases v; simp [v2, nrm, hexp]
    · apply Stk.ext_get
      · simp [s1, set_inp]
      · simp [s1, set_out]
      · rw [hcur] at hinv
        intro a; cases a <;> simp [s1, Stk.get, Stk.set, hcur, hinv]
    · simp only [s1, Stk.get, Stk.set]
      omega

theorem lookupLoop_spec (q : List Bool) (vs : List (List Bool)) :
    ∀ (fnd : Bool) (k : Nat) (sb : List Bool) (v : Reg) (s : Stk),
      v.expectData = false → v.eqFlag = true → v.found = fnd →
      s.SeenV = encodeVars vs → s.SeenVb = sb → s.CurV = q → s.CurVb = [] →
      s.Vidx = List.replicate k true →
      ∃ (b0' par' : Bool),
        Run lookupLoop v s
          (nrm { v with b0 := b0', expectData := false, eqFlag := true, found := fnd || decide (q ∈ vs), par := par' })
          { s with SeenV := [], SeenVb := (encodeVars vs).reverse ++ sb, Vidx := List.replicate (if fnd then k else k + vs.idxOf q) true }
          (20 * (encodeVars vs).length + 1) := by
  induction vs with
  | nil =>
    intro fnd k sb v s hexp heqf hfnd hSV hSVb hCV hCVb hVi
    have hSVg : s.get .SeenV = [] := hSV
    refine ⟨v.b0, v.par, ?_, ?_⟩
    · rw [lookupLoop, exec_forPop_nil _ _ _ _ _ _ hSVg]
      refine St_eq _ _ _ _ (by cases v; simp_all [nrm]) ?_
      apply Stk.ext_get
      · rfl
      · rfl
      · intro a; cases a <;> simp [Stk.get, hSV, hSVb, hVi, encodeVars]
    · exact le_of_eq (cost_forPop_nil _ _ _ _ _ _ hSVg)
  | cons ds vs ih =>
    intro fnd k sb v s hexp heqf hfnd hSV hSVb hCV hCVb hVi
    have hSV' : s.SeenV = (ds.flatMap fun d => [true, d]) ++ (false :: encodeVars vs) := by
      simpa [encodeVars, encodeEntry, List.append_assoc] using hSV
    obtain ⟨u1, b01, par1, hd_exec, hd_cost⟩ := lookupLoop_digits ds (false :: encodeVars vs) v s hexp hSV'
    obtain ⟨hinv, hlen, hmatch⟩ := cmpDrop_inv ds s.CurV s.CurVb v.eqFlag
    rw [heqf, hCV, hCVb] at hinv hlen hmatch
    simp only [List.reverse_nil, List.nil_append] at hinv
    let r := cmpDrop true ds q []
    have hr_eq : cmpDrop v.eqFlag ds s.CurV s.CurVb = r := by rw [heqf, hCV, hCVb]
    let vMid : Reg := { v with go := true, u := u1, b0 := b01, expectData := false, eqFlag := r.1, par := par1 }
    let sMid : Stk := { s with SeenV := false :: encodeVars vs, SeenVb := (ds.flatMap fun d => [true, d]).reverse ++ sb, CurV := r.2.1, CurVb := r.2.2 }
    have hd_exec' : exec lookupLoop ⟨v, toFun s⟩ = exec lookupLoop ⟨vMid, toFun sMid⟩ := by
      simpa [vMid, sMid, hr_eq, hSVb] using hd_exec
    have hd_cost' : cost lookupLoop ⟨v, toFun s⟩ ≤ cost lookupLoop ⟨vMid, toFun sMid⟩ + 16 * ds.length := by
      simpa [vMid, sMid, hr_eq, hSVb] using hd_cost
    have hhit : (r.1 && r.2.1.isEmpty) = decide (q = ds) := by
      cases hh : (r.1 && r.2.1.isEmpty)
      · symm; rw [decide_eq_false_iff_not]
        intro hq
        have ⟨h1, h2⟩ := hmatch.mpr ⟨rfl, hq⟩
        simp only [r, h1, h2, List.isEmpty_nil, Bool.and_self] at hh
        cases hh
      · symm; rw [decide_eq_true_eq]
        simp only [Bool.and_eq_true, List.isEmpty_iff] at hh
        exact (hmatch.mp hh).2
    let vMid0 : Reg := { vMid with b0 := false, go := true }
    let sMid0 : Stk := sMid.set .SeenV (encodeVars vs)
    obtain ⟨par2, hf_run⟩ := lookupBody_false_spec q vMid0 sMid0 rfl rfl hinv
    let fnd' : Bool := fnd || decide (q = ds)
    let k' : Nat := if fnd || decide (q = ds) then k else k + 1
    let vNext : Reg := nrm { vMid0 with expectData := false, eqFlag := true, found := fnd', par := par2 }
    let sNext : Stk := { sMid0 with SeenVb := (encodeEntry ds).reverse ++ sb, CurV := q, CurVb := [], Vidx := List.replicate k' true }
    have hf_run' : Run lookupBody vMid0 sMid0 vNext sNext (2 * ds.length + 14) := by
      refine Run.conv hf_run ?_ ?_ ?_
      · cases v; simp_all [vNext, vMid0, vMid, sMid0, sMid, Stk.set, nrm, fnd']
      · apply Stk.ext_get
        · rfl
        · rfl
        · intro a
          cases a <;> simp only [sNext, sMid0, sMid, Stk.get, Stk.set, encodeEntry,
            List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
            List.cons_append]
          by_cases h : (fnd || decide (q = ds)) = true
          · simp [h, hhit, hfnd, hVi, k', vMid0, vMid, Bool.or_comm]
          · simp [h, hhit, hfnd, hVi, k', vMid0, vMid, Bool.or_comm, List.replicate_succ]
      · simp only [sMid0, sMid, Stk.set]
        simp only [List.length_nil, Nat.zero_add] at hlen
        dsimp only [r]
        omega
    obtain ⟨b0f, parf, hrest⟩ := ih fnd' k' ((encodeEntry ds).reverse ++ sb) vNext sNext
      rfl rfl rfl rfl rfl rfl rfl rfl
    have hMidg : sMid.get .SeenV = false :: encodeVars vs := rfl
    refine ⟨b0f, parf, ?_, ?_⟩
    · rw [hd_exec', exec_lookupLoop_cons _ _ false (encodeVars vs) hMidg]
      change exec lookupLoop (exec lookupBody ⟨vMid0, toFun sMid0⟩) = _
      rw [hf_run'.1, hrest.1]
      refine St_eq _ _ _ _ ?_ ?_
      · cases v
        simp only [vNext, vMid0, vMid, nrm, fnd', Reg.mk.injEq, true_and, and_true, List.mem_cons]
        by_cases hq : q = ds <;> cases fnd <;> simp [hq]
      · apply Stk.ext_get
        · rfl
        · rfl
        · intro a
          cases a with
          | Vidx =>
            simp only [Stk.get, k', fnd', List.idxOf_cons]
            cases fnd
            · by_cases hq : q = ds
              · subst hq; simp
              · have hne : ds ≠ q := Ne.symm hq
                simp [hq, beq_false_of_ne hne, show k + 1 + vs.idxOf q = k + (vs.idxOf q + 1) by omega]
            · simp
          | _ =>
            simp [sNext, sMid0, sMid, Stk.get, Stk.set, hCV, hCVb, encodeVars, List.append_assoc]
    · have hstep : cost lookupLoop ⟨vMid, toFun sMid⟩ =
          cost lookupLoop (exec lookupBody ⟨vMid0, toFun sMid0⟩) + (cost lookupBody ⟨vMid0, toFun sMid0⟩ + 1) := by
        exact cost_lookupLoop_cons _ _ false (encodeVars vs) hMidg
      rw [hf_run'.1] at hstep
      have h1 := hrest.2
      have h2 := hf_run'.2
      simp only [encodeVars, List.flatMap_cons, List.length_append, encodeEntry_length] at h1 ⊢
      omega

theorem lookupP_spec (q : List Bool) (vs : List (List Bool)) (v : Reg) (s : Stk)
    (hSV : s.SeenV = encodeVars vs) (hSVb : s.SeenVb = [])
    (hCV : s.CurV = q) (hCVb : s.CurVb = []) (hVi : s.Vidx = []) :
    ∃ (b0' par' : Bool),
      Run lookupP v s
        (nrm { v with b0 := b0', expectData := false, eqFlag := true, found := decide (q ∈ vs), par := par' })
        { s with SeenV := [], SeenVb := (encodeVars vs).reverse, Vidx := List.replicate (vs.idxOf q) true }
        (20 * (encodeVars vs).length + 2) := by
  have r1 := Run.load (fun v => { v with expectData := false, eqFlag := true, found := false }) v s
  obtain ⟨b0', par', r2⟩ := lookupLoop_spec q vs false 0 []
    { v with expectData := false, eqFlag := true, found := false } s rfl rfl rfl hSV hSVb hCV hCVb hVi
  refine ⟨b0', par', Run.conv (Run.seq r1 r2) ?_ ?_ (by omega)⟩
  · cases v; simp [nrm]
  · simp

def phase1Step : Pg :=
  Prog.seq (wpush .Xrev (fun v => v.b0))
    (Prog.seq
      (Prog.ite (fun v => decide (v.ws = .abT)) (wpush .Mstk tt) (Prog.load id))
      (Prog.load fun v => { v with
        hasEmpty := v.hasEmpty || (decide (v.ws = .a) && !v.b0),
        ws := wfD v.ws v.b0 }))

def phase1Loop : Pg :=
  Prog.loop K.inp (fun v o => match o with
    | some b => { v with go := true, b0 := b }
    | none => nrm v) (fun v => v.go) phase1Step

def phase1P : Pg :=
  Prog.seq phase1Loop (move .Xrev .X)

theorem wf_phase1P : WF phase1P := by
  refine ⟨⟨fun _ => rfl, ?_, ?_⟩, ?_⟩
  · simp [phase1Step, noTouch_seq, noTouch_wpush, noTouch_ite, noTouch_load]
  · simp [phase1Step, wf_seq, wf_wpush, wf_ite, wf_load]
  · rw [wf_move]; decide

theorem noTouch_phase1Step : NoTouch K.inp phase1Step := by
  simp [phase1Step, noTouch_seq, noTouch_wpush, noTouch_ite, noTouch_load]

def p1Cnt : WS → List Bool → Nat
  | _, [] => 0
  | q, b :: r => (if q = .abT then 1 else 0) + p1Cnt (wfD q b) r

def p1Emp : WS → List Bool → Bool
  | _, [] => false
  | q, b :: r => (decide (q = .a) && !b) || p1Emp (wfD q b) r

theorem p1Cnt_le (q : WS) (l : List Bool) : p1Cnt q l ≤ l.length := by
  induction l generalizing q with
  | nil => simp [p1Cnt]
  | cons b l ih =>
    simp only [p1Cnt, List.length_cons]
    have := ih (wfD q b)
    split <;> omega

theorem p1Cnt_append (q : WS) (l1 l2 : List Bool) :
    p1Cnt q (l1 ++ l2) = p1Cnt q l1 + p1Cnt (l1.foldl wfD q) l2 := by
  induction l1 generalizing q with
  | nil => simp [p1Cnt]
  | cons b l1 ih => simp only [List.cons_append, p1Cnt, List.foldl_cons, ih, Nat.add_assoc]

theorem p1Emp_append (q : WS) (l1 l2 : List Bool) :
    p1Emp q (l1 ++ l2) = (p1Emp q l1 || p1Emp (l1.foldl wfD q) l2) := by
  induction l1 generalizing q with
  | nil => simp [p1Emp]
  | cons b l1 ih => simp only [List.cons_append, p1Emp, List.foldl_cons, ih, Bool.or_assoc]

theorem p1_vcode (n : Nat) :
    p1Cnt .c (vcode n) = 0 ∧ p1Emp .c (vcode n) = false ∧
      (n ≠ 0 → p1Cnt .d (vcode n) = 0 ∧ p1Emp .d (vcode n) = false) := by
  induction n using Nat.binaryRec' with
  | zero => simp [vcode_zero, p1Cnt, p1Emp, wfD]
  | bit b n h ih =>
    rw [vcode_bit b n h]
    cases b
    · have hn : n ≠ 0 := fun h0 => by simpa using h h0
      obtain ⟨h1, h2⟩ := ih.2.2 hn
      simp [p1Cnt, p1Emp, wfD, h1, h2]
    · simp [p1Cnt, p1Emp, wfD, ih.1, ih.2.1]

theorem p1_lit (l : Literal) :
    p1Cnt .a (encodeLiteral l) = 1 ∧ p1Emp .a (encodeLiteral l) = false ∧
      p1Cnt .b (encodeLiteral l) = 1 ∧ p1Emp .b (encodeLiteral l) = false := by
  have hv := p1_vcode l.1
  simp [encodeLiteral_eq, p1Cnt, p1Emp, wfD, hv.1, hv.2.1]

theorem p1_clause (c : Clause) :
    p1Cnt .a (encodeClause c) = c.length ∧ p1Emp .a (encodeClause c) = c.isEmpty ∧
      p1Cnt .b (encodeClause c) = c.length ∧ p1Emp .b (encodeClause c) = false := by
  induction c with
  | nil => simp [encodeClause, p1Cnt, p1Emp, wfD]
  | cons l c ih =>
    have e : encodeClause (l :: c) = encodeLiteral l ++ encodeClause c := by simp [encodeClause]
    have hl := p1_lit l
    have hf := foldl_lit l []
    simp only [List.append_nil, List.foldl_nil] at hf
    rw [e, p1Cnt_append, p1Cnt_append, p1Emp_append, p1Emp_append, hf.1, hf.2]
    simp [hl.1, hl.2.1, hl.2.2.1, hl.2.2.2, ih.2.2.1, ih.2.2.2]
    omega

theorem p1_cnf (F : CNF) :
    p1Cnt .a (encodeCNF F) = F.flatten.length ∧ p1Emp .a (encodeCNF F) = F.any List.isEmpty := by
  induction F with
  | nil => simp [encodeCNF, p1Cnt, p1Emp]
  | cons c F ih =>
    have e : encodeCNF (c :: F) = encodeClause c ++ encodeCNF F := by simp [encodeCNF]
    have hc := p1_clause c
    have hf := (foldl_clause c []).1
    simp only [List.append_nil, List.foldl_nil] at hf
    rw [e, p1Cnt_append, p1Emp_append, hf]
    simp [hc.1, hc.2.1, ih.1, ih.2]

theorem phase1Loop_spec (l : List Bool) :
    ∀ (m : Nat) (v : Reg) (s : Stk),
      s.inp = l → s.Mstk = List.replicate m true →
      ∃ b0' : Bool,
        Run phase1Loop v s
          (nrm { v with b0 := b0', ws := l.foldl wfD v.ws, hasEmpty := v.hasEmpty || p1Emp v.ws l })
          { s with inp := [], Xrev := l.reverse ++ s.Xrev, Mstk := List.replicate (m + p1Cnt v.ws l) true }
          (6 * l.length + 1) := by
  induction l with
  | nil =>
    intro m v s hinp hM
    refine ⟨v.b0, ?_, ?_⟩
    · rw [phase1Loop, exec_loop_nil K.inp _ _ _ ⟨v, toFun s⟩ hinp]
      dsimp only
      refine congrArg₂ St.mk (by cases v; simp [nrm, p1Emp]) ?_
      rw [show Function.update (toFun s) K.inp [] = toFun { s with inp := [] } from update_toFun_inp s []]
      congr 1
      apply Stk.ext_get
      · rfl
      · rfl
      · intro a; cases a <;> simp [Stk.get, hM, p1Cnt]
    · rw [phase1Loop, cost_loop_nil K.inp _ _ _ ⟨v, toFun s⟩ hinp]; omega
  | cons b l ih =>
    intro m v s hinp hM
    let v1 : Reg := { v with go := true, b0 := b, hasEmpty := v.hasEmpty || (decide (v.ws = .a) && !b), ws := wfD v.ws b }
    let s1 : Stk := { s with inp := l, Xrev := b :: s.Xrev, Mstk := List.replicate (m + if v.ws = .abT then 1 else 0) true }
    have hstep : exec phase1Step ⟨{ v with go := true, b0 := b }, toFun { s with inp := l }⟩ = ⟨v1, toFun s1⟩ ∧
        cost phase1Step ⟨{ v with go := true, b0 := b }, toFun { s with inp := l }⟩ ≤ 5 := by
      refine ⟨?_, ?_⟩
      · by_cases hw : v.ws = .abT
        · simp only [phase1Step, exec, exec_wpush, hw, decide_true, ite_true]
          refine St_eq _ _ _ _ (by cases v; simp_all [v1]) ?_
          apply Stk.ext_get
          · simp [s1, set_inp]
          · simp [s1, set_out]
          · intro a; cases a <;> simp [s1, Stk.get, Stk.set, hM, hw, List.replicate_succ, tt]
        · simp only [phase1Step, exec, exec_wpush, hw, decide_false, Bool.false_eq_true, ite_false]
          refine St_eq _ _ _ _ (by cases v; simp [v1]) ?_
          apply Stk.ext_get
          · simp [s1, set_inp]
          · simp [s1, set_out]
          · intro a; cases a <;> simp [s1, Stk.get, Stk.set, hM, hw]
      · by_cases hw : v.ws = .abT
        · simp [phase1Step, exec, cost, wpush, hw]
        · simp [phase1Step, exec, cost, wpush, hw]
    obtain ⟨b0', e1, e2⟩ := ih (m + if v.ws = .abT then 1 else 0) v1 s1 rfl rfl
    refine ⟨b0', ?_, ?_⟩
    · rw [phase1Loop, exec_loop_cons K.inp _ _ _ ⟨v, toFun s⟩ b l hinp rfl noTouch_phase1Step,
        update_toFun_inp]
      change exec phase1Loop (exec phase1Step ⟨{ v with go := true, b0 := b }, toFun { s with inp := l }⟩) = _
      rw [hstep.1, e1]
      refine St_eq _ _ _ _ (by cases v; simp [v1, nrm, p1Emp, Bool.or_assoc]) ?_
      apply Stk.ext_get
      · rfl
      · rfl
      · intro a; cases a <;> simp [s1, v1, Stk.get, p1Cnt, List.append_assoc, Nat.add_assoc]
    · rw [phase1Loop, cost_loop_cons K.inp _ _ _ ⟨v, toFun s⟩ b l hinp rfl noTouch_phase1Step,
        update_toFun_inp]
      change cost phase1Loop (exec phase1Step ⟨{ v with go := true, b0 := b }, toFun { s with inp := l }⟩) +
        (cost phase1Step ⟨{ v with go := true, b0 := b }, toFun { s with inp := l }⟩ + 1) ≤ _
      rw [hstep.1]
      have hs := hstep.2
      simp only [List.length_cons]
      omega

theorem phase1P_spec (x : List Bool) :
    ∃ b0' : Bool,
      Run phase1P regInit { emp with inp := x }
        (nrm { regInit with b0 := b0', ws := x.foldl wfD .a, hasEmpty := p1Emp .a x })
        { emp with X := x, Mstk := List.replicate (p1Cnt .a x) true }
        (8 * x.length + 2) := by
  obtain ⟨b0', r1⟩ := phase1Loop_spec x 0 regInit { emp with inp := x } rfl rfl
  let s0 : Stk := { emp with inp := x }
  let v1 := nrm { regInit with b0 := b0', ws := x.foldl wfD .a, hasEmpty := regInit.hasEmpty || p1Emp .a x }
  let s1 := { s0 with inp := [], Xrev := x.reverse ++ s0.Xrev, Mstk := List.replicate (0 + p1Cnt .a x) true }
  refine ⟨b0', Run.conv (Run.seq r1 (Run.move .Xrev .X (by decide) v1 s1)) ?_ ?_ ?_⟩
  · simp [v1, regInit, nrm]
  · apply Stk.ext_get
    · simp [s1, s0, emp, set_inp]
    · simp [s1, s0, emp, set_out]
    · intro a; cases a <;> simp [s1, s0, emp, Stk.get, Stk.set]
  · simp [s1, s0, emp, Stk.get]
    omega

def appendCurV : Pg :=
  Prog.seq
    (forPop .CurV (fun v b => { v with b0 := b }) id
      (Prog.seq (wpush .SeenVb tt) (wpush .SeenVb (fun v => v.b0))))
    (wpush .SeenVb ff)

theorem appendCurV_loop_spec (l : List Bool) :
    ∀ (sb : List Bool) (v : Reg) (s : Stk),
      s.CurV = l → s.SeenVb = sb →
      ∃ b0' : Bool,
        Run (forPop .CurV (fun v b => { v with b0 := b }) id
          (Prog.seq (wpush .SeenVb tt) (wpush .SeenVb (fun v => v.b0)))) v s
          (nrm { v with b0 := b0' })
          { s with CurV := [], SeenVb := (l.flatMap fun d => [true, d]).reverse ++ sb }
          (3 * l.length + 1) := by
  have hnt : NoTouch (K.w .CurV) (Prog.seq (wpush .SeenVb tt) (wpush .SeenVb (fun v => v.b0))) := by
    simp [noTouch_seq, noTouch_wpush]
  induction l with
  | nil =>
    intro sb v s hC hS
    have hCg : s.get .CurV = [] := hC
    refine ⟨v.b0, ?_, ?_⟩
    · rw [exec_forPop_nil _ _ _ _ _ _ hCg]
      refine St_eq _ _ _ _ (by cases v; simp [nrm]) ?_
      apply Stk.ext_get
      · rfl
      · rfl
      · intro a; cases a <;> simp [Stk.get, hC, hS]
    · exact le_of_eq (cost_forPop_nil _ _ _ _ _ _ hCg)
  | cons d l ih =>
    intro sb v s hC hS
    have hCg : s.get .CurV = d :: l := hC
    let v1 : Reg := { v with b0 := d, go := true }
    let s1 : Stk := { s with CurV := l, SeenVb := d :: true :: sb }
    have hbd : exec (Prog.seq (wpush .SeenVb tt) (wpush .SeenVb (fun v => v.b0)))
        ⟨v1, toFun (s.set .CurV l)⟩ = ⟨v1, toFun s1⟩ := by
      simp only [exec, exec_wpush]
      refine St_eq _ _ _ _ rfl ?_
      apply Stk.ext_get
      · simp [s1, set_inp]
      · simp [s1, set_out]
      · intro a; cases a <;> simp [s1, v1, Stk.get, Stk.set, hS, tt]
    obtain ⟨b0', e1, e2⟩ := ih (d :: true :: sb) v1 s1 rfl rfl
    refine ⟨b0', ?_, ?_⟩
    · rw [exec_forPop_cons _ _ _ _ _ _ d l hCg hnt]
      change exec _ (exec _ ⟨v1, toFun (s.set .CurV l)⟩) = _
      rw [hbd, e1]
      refine St_eq _ _ _ _ (by cases v; simp [v1, nrm]) ?_
      apply Stk.ext_get
      · rfl
      · rfl
      · intro a; cases a <;> simp [s1, Stk.get, List.flatMap_cons, List.reverse_cons, List.append_assoc]
    · rw [cost_forPop_cons _ _ _ _ _ _ d l hCg hnt]
      change cost _ (exec _ ⟨v1, toFun (s.set .CurV l)⟩) + (cost _ ⟨v1, toFun (s.set .CurV l)⟩ + 1) ≤ _
      rw [hbd]
      have hcb : cost (Prog.seq (wpush .SeenVb tt) (wpush .SeenVb (fun v => v.b0)))
          ⟨v1, toFun (s.set .CurV l)⟩ = 2 := by simp [cost, wpush]
      rw [hcb]
      simp only [List.length_cons]
      omega

theorem appendCurV_spec (q sb : List Bool) (v : Reg) (s : Stk)
    (hC : s.CurV = q) (hS : s.SeenVb = sb) :
    ∃ b0' : Bool,
      Run appendCurV v s (nrm { v with b0 := b0' })
        { s with CurV := [], SeenVb := (encodeEntry q).reverse ++ sb }
        (3 * q.length + 2) := by
  obtain ⟨b0', r1⟩ := appendCurV_loop_spec q sb v s hC hS
  refine ⟨b0', Run.conv (Run.seq r1 (Run.wpush .SeenVb ff _ _)) rfl ?_ (by omega)⟩
  apply Stk.ext_get
  · simp [set_inp]
  · simp [set_out]
  · intro a; cases a <;> simp [Stk.get, Stk.set, encodeEntry, ff]

def phase2Insert : Pg :=
  Prog.seq (move .Drev .CurV)
    (Prog.seq lookupP
      (Prog.seq
        (Prog.ite (fun v => !v.found)
          (Prog.seq appendCurV (wpush .Vstk tt))
          (drain .CurV))
        (Prog.seq (drain .Vidx) (move .SeenVb .SeenV))))

theorem phase2Insert_spec (q : List Bool) (vs : List (List Bool)) (v : Reg) (s : Stk)
    (hD : s.Drev = q.reverse) (hCV : s.CurV = []) (hCVb : s.CurVb = [])
    (hSV : s.SeenV = encodeVars vs) (hSVb : s.SeenVb = []) (hVi : s.Vidx = [])
    (hVs : s.Vstk = List.replicate vs.length true) :
    ∃ (b0' par' : Bool),
      Run phase2Insert v s
        (nrm { v with b0 := b0', expectData := false, eqFlag := true, found := decide (q ∈ vs), par := par' })
        { s with Drev := [], SeenV := encodeVars (insUniq vs q), Vstk := List.replicate (insUniq vs q).length true }
        (27 * (encodeVars (insUniq vs q)).length + 12 * q.length + 12) := by
  have r1 := Run.move .Drev .CurV (by decide) v s
  let s1 := (s.set .Drev []).set .CurV (q ++ [])
  have hs1 : ((s.set .Drev []).set .CurV ((s.get .Drev).reverse ++ s.get .CurV)) = s1 := by
    simp [s1, Stk.get, hD, hCV]
  rw [hs1] at r1
  obtain ⟨b01, par1, r2⟩ := lookupP_spec q vs (nrm v) s1
    (by simp [s1, Stk.set, hSV]) (by simp [s1, Stk.set, hSVb])
    (by simp [s1, Stk.set]) (by simp [s1, Stk.set, hCVb]) (by simp [s1, Stk.set, hVi])
  let v2 := nrm { nrm v with b0 := b01, expectData := false, eqFlag := true, found := decide (q ∈ vs), par := par1 }
  let s2 := { s1 with SeenV := [], SeenVb := (encodeVars vs).reverse, Vidx := List.replicate (vs.idxOf q) true }
  have hvle : vs.idxOf q ≤ vs.length := List.idxOf_le_length
  have hvlen : vs.length ≤ (encodeVars vs).length := vs_len_le_encodeVars vs
  by_cases hq : q ∈ vs
  · have r3 := Run.ite_false (c := fun v : Reg => !v.found)
      (p := Prog.seq appendCurV (wpush .Vstk tt))
      (by simp [v2, nrm, hq]) (Run.drain .CurV v2 s2)
    let s3 := s2.set .CurV []
    have r4 := Run.drain .Vidx (nrm v2) s3
    let s4 := s3.set .Vidx []
    have r5 := Run.move .SeenVb .SeenV (by decide) (nrm (nrm v2)) s4
    refine ⟨b01, par1, Run.conv (Run.seq r1 (Run.seq r2 (Run.seq r3 (Run.seq r4 r5)))) ?_ ?_ ?_⟩
    · cases v; simp [v2, nrm]
    · apply Stk.ext_get
      · simp [s4, s3, s2, s1, set_inp]
      · simp [s4, s3, s2, s1, set_out]
      · intro a; cases a <;> simp [s4, s3, s2, s1, Stk.get, Stk.set, hCV, hSVb, hVi, hVs, insUniq, hq]
    · simp only [s4, s3, s2, s1, Stk.get, Stk.set, hD, List.length_reverse, List.length_replicate,
        List.append_nil, insUniq, hq, ite_true]
      omega
  · obtain ⟨b02, r3a⟩ := appendCurV_spec q (encodeVars vs).reverse v2 s2
      (by simp [s2, s1, Stk.set]) rfl
    let v3 := nrm { v2 with b0 := b02 }
    let s3a := { s2 with CurV := [], SeenVb := (encodeEntry q).reverse ++ (encodeVars vs).reverse }
    have r3b := Run.wpush .Vstk tt v3 s3a
    have r3 := Run.ite_true (c := fun v : Reg => !v.found) (q := drain .CurV)
      (by simp [v2, nrm, hq]) (Run.seq r3a r3b)
    let s3 := s3a.set .Vstk (true :: s3a.get .Vstk)
    have r4 := Run.drain .Vidx v3 s3
    let s4 := s3.set .Vidx []
    have r5 := Run.move .SeenVb .SeenV (by decide) (nrm v3) s4
    refine ⟨b02, par1, Run.conv (Run.seq r1 (Run.seq r2 (Run.seq r3 (Run.seq r4 r5)))) ?_ ?_ ?_⟩
    · cases v; simp [v3, v2, nrm]
    · apply Stk.ext_get
      · simp [s4, s3, s3a, s2, s1, set_inp]
      · simp [s4, s3, s3a, s2, s1, set_out]
      · intro a
        cases a <;> simp [s4, s3, s3a, s2, s1, Stk.get, Stk.set, hCV, hSVb, hVi, hVs, insUniq, hq,
          encodeVars_append, List.replicate_succ]
    · simp only [s4, s3, s3a, s2, s1, Stk.get, Stk.set, hD, List.length_reverse,
        List.length_replicate, List.length_append, List.append_nil, insUniq, hq, ite_false,
        encodeVars_append, encodeEntry_length]
      omega

def phase2Step : Pg :=
  Prog.seq (wpush .Xrev (fun v => v.u))
    (Prog.ite (fun v => !v.half)
      (Prog.load fun v => { v with b0 := v.u, half := true })
      (Prog.seq (Prog.load fun v => { v with half := false })
        (Prog.ite (fun v => !v.inLit)
          (Prog.ite (fun v => v.b0)
            (Prog.load fun v => { v with inLit := true })
            (Prog.load id))
          (Prog.ite (fun v => v.b0)
            (wpush .Drev (fun v => v.u))
            (Prog.seq (Prog.load fun v => { v with inLit := false }) phase2Insert)))))

def phase2Loop : Pg :=
  forPop .X (fun v b => { v with u := b }) id phase2Step

def phase2P : Pg :=
  Prog.seq (Prog.load fun v => { v with half := false, inLit := false })
    (Prog.seq phase2Loop (move .Xrev .X))

theorem noTouch_phase2Step : NoTouch (K.w .X) phase2Step := by
  simp [phase2Step, phase2Insert, appendCurV, noTouch_seq, noTouch_wpush, noTouch_ite, noTouch_load,
    noTouch_move, noTouch_drain, noTouch_forPop, noTouch_lookupP]

theorem exec_phase2Loop_cons (v : Reg) (s : Stk) (x : Bool) (xs : List Bool)
    (h : s.get .X = x :: xs) :
    exec phase2Loop ⟨v, toFun s⟩ =
      exec phase2Loop (exec phase2Step ⟨{ v with u := x, go := true }, toFun (s.set .X xs)⟩) := by
  exact exec_forPop_cons .X (fun v b => { v with u := b }) id phase2Step v s x xs h noTouch_phase2Step

theorem cost_phase2Loop_cons (v : Reg) (s : Stk) (x : Bool) (xs : List Bool)
    (h : s.get .X = x :: xs) :
    cost phase2Loop ⟨v, toFun s⟩ =
      cost phase2Loop (exec phase2Step ⟨{ v with u := x, go := true }, toFun (s.set .X xs)⟩) +
        (cost phase2Step ⟨{ v with u := x, go := true }, toFun (s.set .X xs)⟩ + 1) := by
  exact cost_forPop_cons .X (fun v b => { v with u := b }) id phase2Step v s x xs h noTouch_phase2Step

theorem wf_phase2P : WF phase2P := by
  simp [phase2P, phase2Loop, phase2Step, phase2Insert, appendCurV, wf_seq, wf_load, wf_forPop,
    wf_move, wf_wpush, wf_ite, wf_drain, wf_lookupP, noTouch_seq, noTouch_wpush, noTouch_ite,
    noTouch_load, noTouch_move, noTouch_drain, noTouch_forPop, noTouch_lookupP]

theorem phase2_pair_inLit_true (d : Bool) (rest : List Bool) (v : Reg) (s : Stk)
    (hh : v.half = false) (hil : v.inLit = true) (hX : s.X = true :: d :: rest) :
    let v' : Reg := { v with go := true, u := d, b0 := true, half := false, inLit := true }
    let s' : Stk := { s with X := rest, Xrev := d :: true :: s.Xrev, Drev := d :: s.Drev }
    exec phase2Loop ⟨v, toFun s⟩ = exec phase2Loop ⟨v', toFun s'⟩ ∧
      cost phase2Loop ⟨v, toFun s⟩ ≤ cost phase2Loop ⟨v', toFun s'⟩ + 16 := by
  have hX1 : s.get .X = true :: d :: rest := hX
  let v1 : Reg := { v with go := true, u := true, b0 := true, half := true }
  let s1 : Stk := { s with X := d :: rest, Xrev := true :: s.Xrev }
  have hs1 : exec phase2Step ⟨{ v with u := true, go := true }, toFun (s.set .X (d :: rest))⟩ = ⟨v1, toFun s1⟩ ∧
      cost phase2Step ⟨{ v with u := true, go := true }, toFun (s.set .X (d :: rest))⟩ ≤ 5 := by
    refine ⟨?_, ?_⟩
    · simp only [phase2Step, exec, exec_wpush, hh, Bool.not_false, ite_true]
      refine St_eq _ _ _ _ (by cases v; rfl) ?_
      apply Stk.ext_get <;> simp [s1, set_inp, set_out]
      intro a; cases a <;> simp [Stk.get, Stk.set]
    · simp only [phase2Step, exec, cost, wpush, hh, Bool.not_false, ite_true]; omega
  let v2 : Reg := { v with go := true, u := d, b0 := true, half := false, inLit := true }
  let s2 : Stk := { s with X := rest, Xrev := d :: true :: s.Xrev, Drev := d :: s.Drev }
  have hs2 : exec phase2Step ⟨{ v1 with u := d, go := true }, toFun (s1.set .X rest)⟩ = ⟨v2, toFun s2⟩ ∧
      cost phase2Step ⟨{ v1 with u := d, go := true }, toFun (s1.set .X rest)⟩ ≤ 9 := by
    refine ⟨?_, ?_⟩
    · simp only [phase2Step, exec, exec_wpush, v1, hil, Bool.not_true, Bool.false_eq_true,
        ite_false, ite_true]
      refine St_eq _ _ _ _ (by cases v; simp [v2]) ?_
      apply Stk.ext_get <;> simp [s2, s1, set_inp, set_out]
      intro a; cases a <;> simp [Stk.get, Stk.set]
    · simp only [phase2Step, exec, cost, wpush, v1, hil, Bool.not_true, Bool.false_eq_true,
        ite_false, ite_true]
      omega
  have hX2 : s1.get .X = d :: rest := rfl
  refine ⟨?_, ?_⟩
  · rw [exec_phase2Loop_cons _ _ true (d :: rest) hX1, hs1.1, exec_phase2Loop_cons _ _ d rest hX2, hs2.1]
  · rw [cost_phase2Loop_cons _ _ true (d :: rest) hX1, hs1.1, cost_phase2Loop_cons _ _ d rest hX2, hs2.1]
    have h1 := hs1.2; have h2 := hs2.2
    dsimp only [v2, s2]
    omega

theorem phase2_digits (ds : List Bool) :
    ∀ (rest : List Bool) (v : Reg) (s : Stk),
      v.half = false → v.inLit = true →
      s.X = (ds.flatMap fun d => [true, d]) ++ rest →
      ∃ (u' b0' : Bool),
        let v' : Reg := { v with go := true, u := u', b0 := b0', half := false, inLit := true }
        let s' : Stk := { s with X := rest, Xrev := (ds.flatMap fun d => [true, d]).reverse ++ s.Xrev, Drev := ds.reverse ++ s.Drev }
        exec phase2Loop ⟨v, toFun s⟩ = exec phase2Loop ⟨v', toFun s'⟩ ∧
          cost phase2Loop ⟨v, toFun s⟩ ≤ cost phase2Loop ⟨v', toFun s'⟩ + 16 * ds.length := by
  induction ds with
  | nil =>
    intro rest v s hh hil hX
    refine ⟨v.u, v.b0, ?_, ?_⟩
    · cases rest with
      | nil =>
        have hXg : s.get .X = [] := hX
        rw [phase2Loop, exec_forPop_nil _ _ _ _ _ _ hXg, exec_forPop_nil _ _ _ _ _ _ rfl]
        refine St_eq _ _ _ _ (by cases v; simp_all [nrm]) ?_
        apply Stk.ext_get <;> (try rfl); intro a; cases a <;> simp [Stk.get, hX]
      | cons x xs =>
        have hXg : s.get .X = x :: xs := hX
        rw [phase2Loop, exec_forPop_cons _ _ _ _ _ _ x xs hXg noTouch_phase2Step,
          exec_forPop_cons _ _ _ _ _ _ x xs rfl noTouch_phase2Step]
        congr 2
        refine St_eq _ _ _ _ (by cases v; simp_all) ?_
        apply Stk.ext_get <;> simp [set_inp, set_out]
        intro a; cases a <;> simp [Stk.get, Stk.set]
    · cases rest with
      | nil =>
        have hXg : s.get .X = [] := hX
        rw [phase2Loop, cost_forPop_nil _ _ _ _ _ _ hXg, cost_forPop_nil _ _ _ _ _ _ rfl]; omega
      | cons x xs =>
        have hXg : s.get .X = x :: xs := hX
        rw [phase2Loop, cost_forPop_cons _ _ _ _ _ _ x xs hXg noTouch_phase2Step,
          cost_forPop_cons _ _ _ _ _ _ x xs rfl noTouch_phase2Step]
        have heq : (⟨{ ({ v with u := x }) with go := true }, toFun (s.set .X xs)⟩ : St K Γ Reg) =
            ⟨{ ({ ({ v with go := true, u := v.u, b0 := v.b0, half := false, inLit := true }) with u := x }) with go := true },
              toFun (({ s with X := x :: xs, Xrev := s.Xrev, Drev := s.Drev }).set .X xs)⟩ := by
          refine St_eq _ _ _ _ (by cases v; simp_all) ?_
          apply Stk.ext_get <;> (try simp [set_inp, set_out])
          intro a; cases a <;> simp [Stk.get, Stk.set]
        simp only [List.flatMap_nil, List.reverse_nil, List.nil_append, List.length_nil,
          Nat.mul_zero, Nat.add_zero]
        rw [heq]
  | cons d ds ih =>
    intro rest v s hh hil hX
    have hX' : s.X = true :: d :: ((ds.flatMap fun d => [true, d]) ++ rest) := by simpa using hX
    obtain ⟨he1, hc1⟩ := phase2_pair_inLit_true d ((ds.flatMap fun d => [true, d]) ++ rest) v s hh hil hX'
    let v1 : Reg := { v with go := true, u := d, b0 := true, half := false, inLit := true }
    let s1 : Stk := { s with X := (ds.flatMap fun d => [true, d]) ++ rest, Xrev := d :: true :: s.Xrev, Drev := d :: s.Drev }
    obtain ⟨u', b0', he2, hc2⟩ := ih rest v1 s1 rfl rfl rfl
    refine ⟨u', b0', ?_, ?_⟩
    · rw [he1, he2]
      congr 1
      refine St_eq _ _ _ _ (by cases v; rfl) ?_
      apply Stk.ext_get <;> (try rfl)
      intro a; cases a <;> simp [s1, Stk.get, List.flatMap_cons, List.append_assoc]
    · have hceq : cost phase2Loop ⟨{ v1 with go := true, u := u', b0 := b0', half := false, inLit := true },
          toFun { s1 with X := rest, Xrev := (ds.flatMap fun d => [true, d]).reverse ++ s1.Xrev, Drev := ds.reverse ++ s1.Drev }⟩ =
          cost phase2Loop ⟨{ v with go := true, u := u', b0 := b0', half := false, inLit := true },
            toFun { s with X := rest, Xrev := ((d :: ds).flatMap fun d => [true, d]).reverse ++ s.Xrev, Drev := (d :: ds).reverse ++ s.Drev }⟩ := by
        congr 1
        refine St_eq _ _ _ _ (by cases v; rfl) ?_
        apply Stk.ext_get <;> (try rfl)
        intro a; cases a <;> simp [s1, Stk.get, List.flatMap_cons, List.append_assoc]
      rw [hceq] at hc2
      dsimp only [v1, s1] at hc2
      simp only [List.length_cons]
      omega

theorem phase2_lit (l : Literal) (rest : List Bool) (vs : List (List Bool)) (v : Reg) (s : Stk)
    (hh : v.half = false) (hil : v.inLit = false)
    (hX : s.X = encodeLiteral l ++ rest)
    (hD : s.Drev = []) (hCV : s.CurV = []) (hCVb : s.CurVb = [])
    (hSV : s.SeenV = encodeVars vs) (hSVb : s.SeenVb = []) (hVi : s.Vidx = [])
    (hVs : s.Vstk = List.replicate vs.length true) :
    ∃ (b0' par' : Bool),
      let vs' := insUniq vs l.1.bits
      let v' : Reg := nrm { v with b0 := b0', half := false, inLit := false, expectData := false, eqFlag := true, found := decide (l.1.bits ∈ vs), par := par' }
      let s' : Stk := { s with X := rest, Xrev := (encodeLiteral l).reverse ++ s.Xrev, SeenV := encodeVars vs', Vstk := List.replicate vs'.length true }
      exec phase2Loop ⟨v, toFun s⟩ = exec phase2Loop ⟨v', toFun s'⟩ ∧
        cost phase2Loop ⟨v, toFun s⟩ ≤ cost phase2Loop ⟨v', toFun s'⟩ +
          (27 * (encodeVars vs').length + 28 * l.1.bits.length + 50) := by
  have hX1 : s.get .X = true :: l.2 :: (vcode l.1 ++ rest) := by
    simpa [Stk.get, encodeLiteral_eq] using hX
  let v1 : Reg := { v with go := true, u := true, b0 := true, half := true }
  let s1 : Stk := { s with X := l.2 :: (vcode l.1 ++ rest), Xrev := true :: s.Xrev }
  have hs1 : exec phase2Step ⟨{ v with u := true, go := true }, toFun (s.set .X (l.2 :: (vcode l.1 ++ rest)))⟩ = ⟨v1, toFun s1⟩ ∧
      cost phase2Step ⟨{ v with u := true, go := true }, toFun (s.set .X (l.2 :: (vcode l.1 ++ rest)))⟩ ≤ 5 := by
    refine ⟨?_, ?_⟩
    · simp only [phase2Step, exec, exec_wpush, hh, Bool.not_false, ite_true]
      refine St_eq _ _ _ _ (by cases v; rfl) ?_
      apply Stk.ext_get <;> simp [s1, set_inp, set_out]
      intro a; cases a <;> simp [Stk.get, Stk.set]
    · simp only [phase2Step, exec, cost, wpush, hh, Bool.not_false, ite_true]; omega
  let v2 : Reg := { v with go := true, u := l.2, b0 := true, half := false, inLit := true }
  let s2 : Stk := { s with X := vcode l.1 ++ rest, Xrev := l.2 :: true :: s.Xrev }
  have hs2 : exec phase2Step ⟨{ v1 with u := l.2, go := true }, toFun (s1.set .X (vcode l.1 ++ rest))⟩ = ⟨v2, toFun s2⟩ ∧
      cost phase2Step ⟨{ v1 with u := l.2, go := true }, toFun (s1.set .X (vcode l.1 ++ rest))⟩ ≤ 9 := by
    refine ⟨?_, ?_⟩
    · simp only [phase2Step, exec, exec_wpush, v1, hil, Bool.not_true, Bool.not_false,
        Bool.false_eq_true, ite_false, ite_true]
      refine St_eq _ _ _ _ (by cases v; rfl) ?_
      apply Stk.ext_get <;> simp [s2, s1, set_inp, set_out]
      intro a; cases a <;> simp [Stk.get, Stk.set]
    · simp only [phase2Step, exec, cost, wpush, v1, hil, Bool.not_true, Bool.not_false,
        Bool.false_eq_true, ite_false, ite_true]; omega
  obtain ⟨u3, b03, hd_exec, hd_cost⟩ := phase2_digits l.1.bits (false :: true :: rest) v2 s2 rfl rfl
    (by simp [s2, vcode, List.append_assoc])
  let v3 : Reg := { v2 with go := true, u := u3, b0 := b03, half := false, inLit := true }
  let s3 : Stk := { s2 with X := false :: true :: rest, Xrev := (l.1.bits.flatMap fun d => [true, d]).reverse ++ s2.Xrev, Drev := l.1.bits.reverse ++ s2.Drev }
  let v4 : Reg := { v3 with go := true, u := false, b0 := false, half := true }
  let s4 : Stk := { s3 with X := true :: rest, Xrev := false :: s3.Xrev }
  have hs4 : exec phase2Step ⟨{ v3 with u := false, go := true }, toFun (s3.set .X (true :: rest))⟩ = ⟨v4, toFun s4⟩ ∧
      cost phase2Step ⟨{ v3 with u := false, go := true }, toFun (s3.set .X (true :: rest))⟩ ≤ 5 := by
    refine ⟨?_, ?_⟩
    · simp only [phase2Step, exec, exec_wpush, v3, Bool.not_false, ite_true]
      refine St_eq _ _ _ _ (by cases v; rfl) ?_
      apply Stk.ext_get <;> simp [s4, s3, set_inp, set_out]
      intro a; cases a <;> simp [Stk.get, Stk.set]
    · simp only [phase2Step, exec, cost, wpush, v3, Bool.not_false, ite_true]; omega
  let v4' : Reg := { v4 with u := true, go := true, half := false, inLit := false }
  let s4' : Stk := { s4 with X := rest, Xrev := true :: s4.Xrev }
  obtain ⟨b05, par5, hins⟩ := phase2Insert_spec l.1.bits vs v4' s4'
    (by simp [s4', s4, s3, s2, hD]) (by simp [s4', s4, s3, s2, hCV])
    (by simp [s4', s4, s3, s2, hCVb]) (by simp [s4', s4, s3, s2, hSV])
    (by simp [s4', s4, s3, s2, hSVb]) (by simp [s4', s4, s3, s2, hVi])
    (by simp [s4', s4, s3, s2, hVs])
  let v5 : Reg := nrm { v4' with b0 := b05, expectData := false, eqFlag := true, found := decide (l.1.bits ∈ vs), par := par5 }
  let s5 : Stk := { s4' with Drev := [], SeenV := encodeVars (insUniq vs l.1.bits), Vstk := List.replicate (insUniq vs l.1.bits).length true }
  have hs5 : exec phase2Step ⟨{ v4 with u := true, go := true }, toFun (s4.set .X rest)⟩ = ⟨v5, toFun s5⟩ ∧
      cost phase2Step ⟨{ v4 with u := true, go := true }, toFun (s4.set .X rest)⟩ ≤
        27 * (encodeVars (insUniq vs l.1.bits)).length + 12 * l.1.bits.length + 22 := by
    have hs4_eq : (s4.set .X rest).set .Xrev (true :: (s4.set .X rest).get .Xrev) = s4' := by
      apply Stk.ext_get <;> simp [s4', set_inp, set_out]
      intro a; cases a <;> simp [Stk.get, Stk.set]
    have hcw : ∀ (v0 : Reg) (s0 : Stk), cost (wpush .Xrev (fun v => v.u)) ⟨v0, toFun s0⟩ = 1 := fun _ _ => rfl
    have hv4h : v4.half = true := rfl
    have hv4i : v4.inLit = true := rfl
    have hv4b : v4.b0 = false := rfl
    refine ⟨?_, ?_⟩
    · simp only [phase2Step, exec, exec_wpush, hv4h, hv4i, hv4b, Bool.not_true, Bool.false_eq_true,
        ite_false, hs4_eq]
      exact hins.1
    · simp only [phase2Step, exec, cost, hcw, exec_wpush, hv4h, hv4i, hv4b, Bool.not_true,
        Bool.false_eq_true, ite_false, hs4_eq]
      have h2 := hins.2
      change cost phase2Insert ⟨v4', toFun s4'⟩ ≤ _ at h2
      have hv4'_eq : ({ ({ ({ v4 with u := true, go := true }) with half := false }) with inLit := false } : Reg) = v4' := rfl
      rw [hv4'_eq]
      omega
  have hv5_eq : v5 = nrm { v with b0 := b05, half := false, inLit := false, expectData := false, eqFlag := true, found := decide (l.1.bits ∈ vs), par := par5 } := by
    cases v; rfl
  have hs5_eq : s5 = { s with X := rest, Xrev := (encodeLiteral l).reverse ++ s.Xrev, SeenV := encodeVars (insUniq vs l.1.bits), Vstk := List.replicate (insUniq vs l.1.bits).length true } := by
    apply Stk.ext_get <;> (try rfl)
    intro a; cases a <;> simp [s5, s4', s4, s3, s2, Stk.get, hD, encodeLiteral_eq, vcode, List.append_assoc]
  have hX2 : s1.get .X = l.2 :: (vcode l.1 ++ rest) := rfl
  have hX3 : s3.get .X = false :: true :: rest := rfl
  have hX4 : s4.get .X = true :: rest := rfl
  refine ⟨b05, par5, ?_, ?_⟩
  · rw [exec_phase2Loop_cons _ _ true _ hX1, hs1.1, exec_phase2Loop_cons _ _ l.2 _ hX2, hs2.1,
      hd_exec, exec_phase2Loop_cons _ _ false _ hX3, hs4.1, exec_phase2Loop_cons _ _ true _ hX4,
      hs5.1, hv5_eq, hs5_eq]
  · rw [cost_phase2Loop_cons _ _ true _ hX1, hs1.1, cost_phase2Loop_cons _ _ l.2 _ hX2, hs2.1]
    have hstep45 : cost phase2Loop ⟨v3, toFun s3⟩ ≤
        cost phase2Loop ⟨v5, toFun s5⟩ +
          (27 * (encodeVars (insUniq vs l.1.bits)).length + 12 * l.1.bits.length + 29) := by
      rw [cost_phase2Loop_cons _ _ false _ hX3, hs4.1, cost_phase2Loop_cons _ _ true _ hX4, hs5.1]
      have h4 := hs4.2; have h5 := hs5.2; omega
    rw [hv5_eq, hs5_eq] at hstep45
    have h1 := hs1.2; have h2 := hs2.2
    dsimp only [v3, s3] at hd_cost hstep45
    omega

theorem phase2_clause (c : Clause) :
    ∀ (rest : List Bool) (vs : List (List Bool)) (v : Reg) (s : Stk) (Z : Nat),
      v.half = false → v.inLit = false →
      s.X = encodeClause c ++ rest →
      s.Drev = [] → s.CurV = [] → s.CurVb = [] →
      s.SeenV = encodeVars vs → s.SeenVb = [] → s.Vidx = [] →
      s.Vstk = List.replicate vs.length true →
      (encodeVars ((c.map (fun l => l.1.bits)).foldl insUniq vs)).length ≤ Z →
      ∃ (b0' exp' eq' fnd' par' : Bool),
        let vs' := (c.map (fun l => l.1.bits)).foldl insUniq vs
        let v' : Reg := { v with go := false, u := false, b0 := b0', half := false, inLit := false, expectData := exp', eqFlag := eq', found := fnd', par := par' }
        let s' : Stk := { s with X := rest, Xrev := (encodeClause c).reverse ++ s.Xrev, SeenV := encodeVars vs', Vstk := List.replicate vs'.length true }
        exec phase2Loop ⟨v, toFun s⟩ = exec phase2Loop ⟨v', toFun s'⟩ ∧
          cost phase2Loop ⟨v, toFun s⟩ ≤ cost phase2Loop ⟨v', toFun s'⟩ +
            (c.length * (27 * Z + 50) + 14 * (encodeClause c).length + 16) := by
  induction c with
  | nil =>
    intro rest vs v s Z hh hil hX _ _ _ _ _ _ _ _
    have hX1 : s.get .X = false :: false :: rest := by simpa [Stk.get, encodeClause] using hX
    let v1 : Reg := { v with go := true, u := false, b0 := false, half := true }
    let s1 : Stk := { s with X := false :: rest, Xrev := false :: s.Xrev }
    have hs1 : exec phase2Step ⟨{ v with u := false, go := true }, toFun (s.set .X (false :: rest))⟩ = ⟨v1, toFun s1⟩ ∧
        cost phase2Step ⟨{ v with u := false, go := true }, toFun (s.set .X (false :: rest))⟩ ≤ 5 := by
      refine ⟨?_, ?_⟩
      · simp only [phase2Step, exec, exec_wpush, hh, Bool.not_false, ite_true]
        refine St_eq _ _ _ _ (by cases v; rfl) ?_
        apply Stk.ext_get <;> simp [s1, set_inp, set_out]
        intro a; cases a <;> simp [Stk.get, Stk.set]
      · simp only [phase2Step, exec, cost, wpush, hh, Bool.not_false, ite_true]; omega
    let v2 : Reg := { v with go := true, u := false, b0 := false, half := false, inLit := false }
    let s2 : Stk := { s with X := rest, Xrev := false :: false :: s.Xrev }
    have hs2 : exec phase2Step ⟨{ v1 with u := false, go := true }, toFun (s1.set .X rest)⟩ = ⟨v2, toFun s2⟩ ∧
        cost phase2Step ⟨{ v1 with u := false, go := true }, toFun (s1.set .X rest)⟩ ≤ 9 := by
      refine ⟨?_, ?_⟩
      · simp only [phase2Step, exec, exec_wpush, v1, hil, Bool.not_true, Bool.not_false,
          Bool.false_eq_true, ite_false, ite_true]
        refine St_eq _ _ _ _ (by cases v; simp [v2]) ?_
        apply Stk.ext_get <;> simp [s2, s1, set_inp, set_out]
        intro a; cases a <;> simp [Stk.get, Stk.set]
      · simp only [phase2Step, exec, cost, wpush, v1, hil, Bool.not_true, Bool.not_false,
          Bool.false_eq_true, ite_false, ite_true]; omega
    let v2' : Reg := { v with go := false, u := false, b0 := false, half := false, inLit := false, expectData := v.expectData, eqFlag := v.eqFlag, found := v.found, par := v.par }
    have hgo_eq : exec phase2Loop ⟨v2, toFun s2⟩ = exec phase2Loop ⟨v2', toFun s2⟩ ∧
        cost phase2Loop ⟨v2, toFun s2⟩ = cost phase2Loop ⟨v2', toFun s2⟩ := by
      cases rest with
      | nil =>
        rw [phase2Loop, exec_forPop_nil _ _ _ _ _ _ rfl, exec_forPop_nil _ _ _ _ _ _ rfl,
          cost_forPop_nil _ _ _ _ _ _ rfl, cost_forPop_nil _ _ _ _ _ _ rfl]
        exact ⟨St_eq _ _ _ _ (by cases v; simp [v2, v2', nrm]) rfl, rfl⟩
      | cons x xs =>
        rw [phase2Loop, exec_forPop_cons _ _ _ _ _ _ x xs rfl noTouch_phase2Step,
          exec_forPop_cons _ _ _ _ _ _ x xs rfl noTouch_phase2Step,
          cost_forPop_cons _ _ _ _ _ _ x xs rfl noTouch_phase2Step,
          cost_forPop_cons _ _ _ _ _ _ x xs rfl noTouch_phase2Step]
        have hv : ({ ({ v2 with u := x }) with go := true } : Reg) = { ({ v2' with u := x }) with go := true } := by
          cases v; rfl
        rw [hv]; exact ⟨rfl, rfl⟩
    have hX2 : s1.get .X = false :: rest := rfl
    refine ⟨false, v.expectData, v.eqFlag, v.found, v.par, ?_, ?_⟩
    · rw [exec_phase2Loop_cons _ _ false (false :: rest) hX1, hs1.1,
        exec_phase2Loop_cons _ _ false rest hX2, hs2.1, hgo_eq.1]
      congr 1
      refine St_eq _ _ _ _ rfl ?_
      apply Stk.ext_get <;> (try rfl)
      intro a; cases a <;> simp [s2, Stk.get, encodeClause, ‹s.SeenV = encodeVars vs›, ‹s.Vstk = List.replicate vs.length true›]
    · rw [cost_phase2Loop_cons _ _ false (false :: rest) hX1, hs1.1,
        cost_phase2Loop_cons _ _ false rest hX2, hs2.1, hgo_eq.2]
      have h1 := hs1.2; have h2 := hs2.2
      have hs2_eq : s2 = { s with X := rest, Xrev := (encodeClause []).reverse ++ s.Xrev, SeenV := encodeVars (([].map (fun l : Literal => l.1.bits)).foldl insUniq vs), Vstk := List.replicate (([].map (fun l : Literal => l.1.bits)).foldl insUniq vs).length true } := by
        apply Stk.ext_get <;> (try rfl)
        intro a; cases a <;> simp [s2, Stk.get, encodeClause, ‹s.SeenV = encodeVars vs›, ‹s.Vstk = List.replicate vs.length true›]
      have hcl : (encodeClause []).length = 2 := rfl
      have hnl : ([] : Clause).length = 0 := rfl
      rw [hs2_eq]
      dsimp only [v2']
      omega
  | cons l c ih =>
    intro rest vs v s Z hh hil hX hD hCV hCVb hSV hSVb hVi hVs hZ
    have hX' : s.X = encodeLiteral l ++ (encodeClause c ++ rest) := by
      simpa [encodeClause, List.append_assoc] using hX
    obtain ⟨b01, par1, hl_exec, hl_cost⟩ := phase2_lit l (encodeClause c ++ rest) vs v s
      hh hil hX' hD hCV hCVb hSV hSVb hVi hVs
    let vs1 := insUniq vs l.1.bits
    let v1 : Reg := nrm { v with b0 := b01, half := false, inLit := false, expectData := false, eqFlag := true, found := decide (l.1.bits ∈ vs), par := par1 }
    let s1 : Stk := { s with X := encodeClause c ++ rest, Xrev := (encodeLiteral l).reverse ++ s.Xrev, SeenV := encodeVars vs1, Vstk := List.replicate vs1.length true }
    have hvs1_le : (encodeVars vs1).length ≤ (encodeVars ((c.map (fun l => l.1.bits)).foldl insUniq vs1)).length := by
      have hmono : ∀ (ls acc : List (List Bool)),
          (encodeVars acc).length ≤ (encodeVars (ls.foldl insUniq acc)).length := by
        intro ls
        induction ls with
        | nil => intro acc; exact le_refl _
        | cons x ls ihls =>
          intro acc
          simp only [List.foldl_cons]
          refine le_trans ?_ (ihls (insUniq acc x))
          unfold insUniq
          split
          · exact le_refl _
          · simp [encodeVars_append]
      exact hmono _ _
    obtain ⟨b02, exp2, eq2, fnd2, par2, hc_exec, hc_cost⟩ := ih rest vs1 v1 s1 Z rfl rfl rfl
      hD hCV hCVb rfl hSVb hVi rfl (by simpa [vs1] using hZ)
    refine ⟨b02, exp2, eq2, fnd2, par2, ?_, ?_⟩
    · rw [hl_exec, hc_exec]
      congr 1
      refine St_eq _ _ _ _ (by cases v; rfl) ?_
      apply Stk.ext_get <;> (try rfl)
      intro a; cases a <;> simp [s1, vs1, Stk.get, encodeClause, List.append_assoc]
    · have hceq : cost phase2Loop ⟨{ v1 with go := false, u := false, b0 := b02, half := false, inLit := false, expectData := exp2, eqFlag := eq2, found := fnd2, par := par2 },
          toFun { s1 with X := rest, Xrev := (encodeClause c).reverse ++ s1.Xrev, SeenV := encodeVars ((c.map (fun l => l.1.bits)).foldl insUniq vs1), Vstk := List.replicate ((c.map (fun l => l.1.bits)).foldl insUniq vs1).length true }⟩ =
          cost phase2Loop ⟨{ v with go := false, u := false, b0 := b02, half := false, inLit := false, expectData := exp2, eqFlag := eq2, found := fnd2, par := par2 },
            toFun { s with X := rest, Xrev := (encodeClause (l :: c)).reverse ++ s.Xrev, SeenV := encodeVars (((l :: c).map (fun l => l.1.bits)).foldl insUniq vs), Vstk := List.replicate (((l :: c).map (fun l => l.1.bits)).foldl insUniq vs).length true }⟩ := by
        congr 1
        refine St_eq _ _ _ _ (by cases v; rfl) ?_
        apply Stk.ext_get <;> (try rfl)
        intro a; cases a <;> simp [s1, vs1, Stk.get, encodeClause, List.append_assoc]
      rw [hceq] at hc_cost
      dsimp only [v1, s1, vs1] at hc_cost hl_cost
      have hlen_c : (encodeClause (l :: c)).length = (encodeLiteral l).length + (encodeClause c).length := by
        simp [encodeClause]
      have hlen_l : 2 * l.1.bits.length + 4 = (encodeLiteral l).length := (encodeLiteral_length l).symm
      have hZ1 : (encodeVars (insUniq vs l.1.bits)).length ≤ Z := le_trans hvs1_le (by simpa [vs1] using hZ)
      have hmul : (l :: c).length * (27 * Z + 50) = c.length * (27 * Z + 50) + (27 * Z + 50) := by
        simp only [List.length_cons]; ring
      omega

theorem phase2_cnf (F : CNF) :
    ∀ (rest : List Bool) (vs : List (List Bool)) (v : Reg) (s : Stk) (Z : Nat),
      v.half = false → v.inLit = false →
      s.X = encodeCNF F ++ rest →
      s.Drev = [] → s.CurV = [] → s.CurVb = [] →
      s.SeenV = encodeVars vs → s.SeenVb = [] → s.Vidx = [] →
      s.Vstk = List.replicate vs.length true →
      (encodeVars (((F.flatten).map (fun l => l.1.bits)).foldl insUniq vs)).length ≤ Z →
      ∃ (b0' exp' eq' fnd' par' : Bool),
        let vs' := ((F.flatten).map (fun l => l.1.bits)).foldl insUniq vs
        let v' : Reg := { v with go := false, u := false, b0 := b0', half := false, inLit := false, expectData := exp', eqFlag := eq', found := fnd', par := par' }
        let s' : Stk := { s with X := rest, Xrev := (encodeCNF F).reverse ++ s.Xrev, SeenV := encodeVars vs', Vstk := List.replicate vs'.length true }
        exec phase2Loop ⟨v, toFun s⟩ = exec phase2Loop ⟨v', toFun s'⟩ ∧
          cost phase2Loop ⟨v, toFun s⟩ ≤ cost phase2Loop ⟨v', toFun s'⟩ +
            (F.flatten.length * (27 * Z + 50) + 14 * (encodeCNF F).length + 16 * F.length) := by
  induction F with
  | nil =>
    intro rest vs v s Z hh hil hX _ _ _ hSV _ _ hVs _
    refine ⟨v.b0, v.expectData, v.eqFlag, v.found, v.par, ?_, ?_⟩
    · cases rest with
      | nil =>
        have hXg : s.get .X = [] := hX
        rw [phase2Loop, exec_forPop_nil _ _ _ _ _ _ hXg, exec_forPop_nil _ _ _ _ _ _ rfl]
        refine St_eq _ _ _ _ (by cases v; simp_all [nrm]) ?_
        apply Stk.ext_get <;> (try rfl)
        intro a; cases a <;> simp [Stk.get, hX, hSV, hVs, encodeCNF]
      | cons x xs =>
        have hXg : s.get .X = x :: xs := hX
        rw [phase2Loop, exec_forPop_cons _ _ _ _ _ _ x xs hXg noTouch_phase2Step,
          exec_forPop_cons _ _ _ _ _ _ x xs rfl noTouch_phase2Step]
        congr 2
        refine St_eq _ _ _ _ (by cases v; simp_all) ?_
        apply Stk.ext_get <;> simp [set_inp, set_out]
        intro a; cases a <;> simp [Stk.get, Stk.set, hSV, hVs, encodeCNF]
    · cases rest with
      | nil =>
        have hXg : s.get .X = [] := hX
        rw [phase2Loop, cost_forPop_nil _ _ _ _ _ _ hXg, cost_forPop_nil _ _ _ _ _ _ rfl]; omega
      | cons x xs =>
        have hXg : s.get .X = x :: xs := hX
        rw [phase2Loop, cost_forPop_cons _ _ _ _ _ _ x xs hXg noTouch_phase2Step,
          cost_forPop_cons _ _ _ _ _ _ x xs rfl noTouch_phase2Step]
        have heq : (⟨{ ({ v with u := x }) with go := true }, toFun (s.set .X xs)⟩ : St K Γ Reg) =
            ⟨{ ({ ({ v with go := false, u := false, b0 := v.b0, half := false, inLit := false, expectData := v.expectData, eqFlag := v.eqFlag, found := v.found, par := v.par }) with u := x }) with go := true },
              toFun (({ s with X := x :: xs, Xrev := (encodeCNF []).reverse ++ s.Xrev, SeenV := encodeVars vs, Vstk := List.replicate vs.length true }).set .X xs)⟩ := by
          refine St_eq _ _ _ _ (by cases v; simp_all) ?_
          apply Stk.ext_get <;> (try simp [set_inp, set_out])
          intro a; cases a <;> simp [Stk.get, Stk.set, hSV, hVs, encodeCNF]
        simp only [List.flatten_nil, List.length_nil, List.map_nil, List.foldl_nil, Nat.zero_mul,
          Nat.mul_zero, Nat.add_zero]
        rw [heq]; exact le_refl _
  | cons c F ih =>
    intro rest vs v s Z hh hil hX hD hCV hCVb hSV hSVb hVi hVs hZ
    have hX' : s.X = encodeClause c ++ (encodeCNF F ++ rest) := by
      simpa [encodeCNF, List.append_assoc] using hX
    let vs1 := (c.map (fun l => l.1.bits)).foldl insUniq vs
    have hZ_eq : (((c :: F).flatten).map (fun l => l.1.bits)).foldl insUniq vs =
        ((F.flatten).map (fun l => l.1.bits)).foldl insUniq vs1 := by
      simp [vs1, List.flatten_cons, List.map_append, List.foldl_append]
    have hvs1_le : (encodeVars vs1).length ≤ (encodeVars (((F.flatten).map (fun l => l.1.bits)).foldl insUniq vs1)).length := by
      have hmono : ∀ (ls acc : List (List Bool)),
          (encodeVars acc).length ≤ (encodeVars (ls.foldl insUniq acc)).length := by
        intro ls
        induction ls with
        | nil => intro acc; exact le_refl _
        | cons x ls ihls =>
          intro acc; simp only [List.foldl_cons]
          refine le_trans ?_ (ihls (insUniq acc x))
          unfold insUniq; split
          · exact le_refl _
          · simp [encodeVars_append]
      exact hmono _ _
    obtain ⟨b01, exp1, eq1, fnd1, par1, hc_exec, hc_cost⟩ := phase2_clause c (encodeCNF F ++ rest)
      vs v s Z hh hil hX' hD hCV hCVb hSV hSVb hVi hVs (le_trans hvs1_le (by rwa [← hZ_eq]))
    let v1 : Reg := { v with go := false, u := false, b0 := b01, half := false, inLit := false, expectData := exp1, eqFlag := eq1, found := fnd1, par := par1 }
    let s1 : Stk := { s with X := encodeCNF F ++ rest, Xrev := (encodeClause c).reverse ++ s.Xrev, SeenV := encodeVars vs1, Vstk := List.replicate vs1.length true }
    obtain ⟨b02, exp2, eq2, fnd2, par2, hf_exec, hf_cost⟩ := ih rest vs1 v1 s1 Z rfl rfl rfl
      hD hCV hCVb rfl hSVb hVi rfl (by rwa [← hZ_eq])
    refine ⟨b02, exp2, eq2, fnd2, par2, ?_, ?_⟩
    · rw [hc_exec, hf_exec]
      congr 1
      refine St_eq _ _ _ _ (by cases v; rfl) ?_
      apply Stk.ext_get <;> (try rfl)
      intro a; cases a <;> simp [s1, vs1, Stk.get, encodeCNF, List.append_assoc]
    · have hceq : cost phase2Loop ⟨{ v1 with go := false, u := false, b0 := b02, half := false, inLit := false, expectData := exp2, eqFlag := eq2, found := fnd2, par := par2 },
          toFun { s1 with X := rest, Xrev := (encodeCNF F).reverse ++ s1.Xrev, SeenV := encodeVars (((F.flatten).map (fun l => l.1.bits)).foldl insUniq vs1), Vstk := List.replicate (((F.flatten).map (fun l => l.1.bits)).foldl insUniq vs1).length true }⟩ =
          cost phase2Loop ⟨{ v with go := false, u := false, b0 := b02, half := false, inLit := false, expectData := exp2, eqFlag := eq2, found := fnd2, par := par2 },
            toFun { s with X := rest, Xrev := (encodeCNF (c :: F)).reverse ++ s.Xrev, SeenV := encodeVars ((((c :: F).flatten).map (fun l => l.1.bits)).foldl insUniq vs), Vstk := List.replicate ((((c :: F).flatten).map (fun l => l.1.bits)).foldl insUniq vs).length true }⟩ := by
        congr 1
        refine St_eq _ _ _ _ (by cases v; rfl) ?_
        apply Stk.ext_get <;> (try rfl)
        intro a; cases a <;> simp [s1, vs1, Stk.get, encodeCNF, List.append_assoc]
      rw [hceq] at hf_cost
      dsimp only [v1, s1, vs1] at hf_cost hc_cost
      have hlen_f : (encodeCNF (c :: F)).length = (encodeClause c).length + (encodeCNF F).length := by
        simp [encodeCNF]
      have hclen : (c :: F).length = F.length + 1 := rfl
      have hmul : (c :: F).flatten.length * (27 * Z + 50) =
          c.length * (27 * Z + 50) + F.flatten.length * (27 * Z + 50) := by
        simp only [List.flatten_cons, List.length_append]; ring
      omega

theorem phase2P_spec (F : CNF) (v : Reg) (s : Stk)
    (hX : s.X = encodeCNF F) (hXr : s.Xrev = []) (hD : s.Drev = [])
    (hCV : s.CurV = []) (hCVb : s.CurVb = []) (hSV : s.SeenV = []) (hSVb : s.SeenVb = [])
    (hVi : s.Vidx = []) (hVs : s.Vstk = []) :
    let ord := ((F.flatten).map Prod.fst).eraseDups
    let z := (encodeCNF F).length
    ∃ (b0' exp' eq' fnd' par' : Bool),
      Run phase2P v s
        (nrm { v with b0 := b0', half := false, inLit := false, expectData := exp', eqFlag := eq', found := fnd', par := par' })
        { s with SeenV := encodeVars (ord.map Nat.bits), Vstk := List.replicate ord.length true }
        (F.flatten.length * (27 * z + 50) + 16 * z + 16 * F.length + 4) := by
  intro ord z
  have hvs_eq : ((F.flatten).map (fun l => l.1.bits)).foldl insUniq [] = ord.map Nat.bits := by
    have h1 : (F.flatten).map (fun l => l.1.bits) = ((F.flatten).map Prod.fst).map Nat.bits := by
      rw [List.map_map]; rfl
    rw [h1]
    have h2 := foldl_insUniq_map Nat.bits bits_injective ((F.flatten).map Prod.fst) []
    simpa [ord, eraseDups_eq_foldl] using h2
  have hZ : (encodeVars (((F.flatten).map (fun l => l.1.bits)).foldl insUniq [])).length ≤ z := by
    rw [hvs_eq]; exact encodeVars_order_len F
  have r1 := Run.load (fun v => { v with half := false, inLit := false }) v s
  obtain ⟨b0', exp', eq', fnd', par', he, hc⟩ := phase2_cnf F [] [] { v with half := false, inLit := false } s z rfl rfl
    (by simp [hX]) hD hCV hCVb hSV hSVb hVi hVs hZ
  have hnil_e : exec phase2Loop ⟨{ ({ v with half := false, inLit := false }) with go := false, u := false, b0 := b0', half := false, inLit := false, expectData := exp', eqFlag := eq', found := fnd', par := par' },
      toFun { s with X := [], Xrev := (encodeCNF F).reverse ++ s.Xrev, SeenV := encodeVars (ord.map Nat.bits), Vstk := List.replicate ord.length true }⟩ =
      ⟨nrm { v with b0 := b0', half := false, inLit := false, expectData := exp', eqFlag := eq', found := fnd', par := par' },
      toFun { s with X := [], Xrev := (encodeCNF F).reverse, SeenV := encodeVars (ord.map Nat.bits), Vstk := List.replicate ord.length true }⟩ := by
    rw [phase2Loop, exec_forPop_nil _ _ _ _ _ _ rfl]
    refine St_eq _ _ _ _ (by cases v; simp [nrm]) ?_
    apply Stk.ext_get <;> (try rfl)
    intro a; cases a <;> simp [Stk.get, hXr]
  have hnil_c : cost phase2Loop ⟨{ ({ v with half := false, inLit := false }) with go := false, u := false, b0 := b0', half := false, inLit := false, expectData := exp', eqFlag := eq', found := fnd', par := par' },
      toFun { s with X := [], Xrev := (encodeCNF F).reverse ++ s.Xrev, SeenV := encodeVars (ord.map Nat.bits), Vstk := List.replicate ord.length true }⟩ = 1 :=
    cost_forPop_nil _ _ _ _ _ _ rfl
  simp only [hvs_eq, List.length_map] at he hc
  have r2 : Run phase2Loop { v with half := false, inLit := false } s
      (nrm { v with b0 := b0', half := false, inLit := false, expectData := exp', eqFlag := eq', found := fnd', par := par' })
      { s with X := [], Xrev := (encodeCNF F).reverse, SeenV := encodeVars (ord.map Nat.bits), Vstk := List.replicate ord.length true }
      (F.flatten.length * (27 * z + 50) + 14 * z + 16 * F.length + 1) := by
    refine ⟨he.trans hnil_e, ?_⟩
    rw [hnil_c] at hc
    omega
  refine ⟨b0', exp', eq', fnd', par', Run.conv (Run.seq r1 (Run.seq r2 (Run.move .Xrev .X (by decide) _ _)))
    (by cases v; simp [nrm]) ?_ ?_⟩
  · apply Stk.ext_get
    · simp [set_inp]
    · simp [set_out]
    · intro a; cases a <;> simp [Stk.get, Stk.set, hX, hXr]
  · simp only [Stk.get, List.length_reverse]
    omega

def phase3P : Pg :=
  Prog.seq (copyS .Vstk .Tmp .Nstk)
    (Prog.seq (move .Mstk .Nstk)
      (Prog.seq (wpush .Nstk tt)
        (Prog.seq (wpush .Nstk tt)
          (Prog.seq (forC .Nstk .Nb (wpush .OutRev tt))
            (Prog.seq (wpush .OutRev ff) computeW)))))

theorem wf_phase3P : WF phase3P := by
  simp [phase3P, wf_seq, wf_copyS, wf_move, wf_wpush, wf_forC, wf_computeW, noTouch_wpush]

theorem pushHdr_loop_spec (t : Nat) : ∀ (b : Nat) (v : Reg) (s : Stk),
    s.Nstk = List.replicate t true → s.Nb = List.replicate b true →
    Run (forPop .Nstk (fun v _ => v) id (Prog.seq (wpush .Nb tt) (wpush .OutRev tt))) v s
      (nrm v) { s with Nstk := [], Nb := List.replicate (b + t) true, OutRev := List.replicate t true ++ s.OutRev }
      (3 * t + 1) := by
  have hnt : NoTouch (K.w .Nstk) (Prog.seq (wpush .Nb tt) (wpush .OutRev tt)) := by
    simp [noTouch_seq, noTouch_wpush]
  induction t with
  | zero =>
    intro b v s hN hNb
    have hNg : s.get .Nstk = [] := hN
    refine ⟨?_, ?_⟩
    · rw [exec_forPop_nil _ _ _ _ _ _ hNg]
      refine St_eq _ _ _ _ rfl ?_
      apply Stk.ext_get <;> (try rfl)
      intro a; cases a <;> simp [Stk.get, hN, hNb]
    · exact le_of_eq (cost_forPop_nil _ _ _ _ _ _ hNg)
  | succ t ih =>
    intro b v s hN hNb
    have hNg : s.get .Nstk = true :: List.replicate t true := by
      simpa [Stk.get, List.replicate_succ] using hN
    let v1 : Reg := { v with go := true }
    let s1 : Stk := { s with Nstk := List.replicate t true, Nb := List.replicate (b + 1) true, OutRev := true :: s.OutRev }
    have hbd : exec (Prog.seq (wpush .Nb tt) (wpush .OutRev tt))
        ⟨v1, toFun (s.set .Nstk (List.replicate t true))⟩ = ⟨v1, toFun s1⟩ := by
      simp only [exec, exec_wpush]
      refine St_eq _ _ _ _ rfl ?_
      apply Stk.ext_get <;> simp [s1, set_inp, set_out]
      intro a; cases a <;> simp [Stk.get, Stk.set, hNb, List.replicate_succ, tt]
    obtain ⟨e1, e2⟩ := ih (b + 1) v1 s1 rfl rfl
    refine ⟨?_, ?_⟩
    · rw [exec_forPop_cons _ _ _ _ _ _ true (List.replicate t true) hNg hnt]
      change exec _ (exec _ ⟨v1, toFun (s.set .Nstk (List.replicate t true))⟩) = _
      rw [hbd, e1]
      refine St_eq _ _ _ _ (by cases v; simp [v1, nrm]) ?_
      apply Stk.ext_get <;> (try rfl)
      intro a; cases a <;> simp only [s1, Stk.get]
      all_goals
        first
        | (simp [show b + 1 + t = b + (t + 1) by omega])
        | (rw [List.replicate_succ', List.append_assoc]; rfl)
    · rw [cost_forPop_cons _ _ _ _ _ _ true (List.replicate t true) hNg hnt]
      change cost _ (exec _ ⟨v1, toFun (s.set .Nstk (List.replicate t true))⟩) +
        (cost _ ⟨v1, toFun (s.set .Nstk (List.replicate t true))⟩ + 1) ≤ _
      rw [hbd]
      have hcb : cost (Prog.seq (wpush .Nb tt) (wpush .OutRev tt))
          ⟨v1, toFun (s.set .Nstk (List.replicate t true))⟩ = 2 := by simp [cost, wpush]
      rw [hcb]; omega

theorem phase3P_spec (V M : Nat) (v : Reg) (s : Stk)
    (hV : s.Vstk = List.replicate V true) (hM : s.Mstk = List.replicate M true)
    (hN : s.Nstk = []) (hNb : s.Nb = []) (hW : s.Wstk = []) (hQ : s.Q = [])
    (hQb : s.Qb = []) (hTmp : s.Tmp = []) (hOut : s.OutRev = []) :
    let n := V + M + 2
    ∃ p' : Bool,
      Run phase3P v s (nrm { v with par := p' })
        { s with Mstk := [], Nstk := List.replicate n true, Wstk := List.replicate (width n) true, OutRev := (header n).reverse }
        (4 * n * n + 35 * n + 20) := by
  intro n
  have r1 := copyS_spec .Vstk .Tmp .Nstk (by decide) (by decide) (by decide) v s hTmp
  let s1 := s.set .Nstk (List.replicate V true)
  have hs1 : s.set .Nstk ((s.get .Vstk).reverse ++ s.get .Nstk) = s1 := by
    simp [s1, Stk.get, hV, hN]
  rw [hs1] at r1
  have r2 := Run.move .Mstk .Nstk (by decide) (nrm v) s1
  let s2 := { s with Mstk := [], Nstk := List.replicate (V + M) true }
  have hs2 : ((s1.set .Mstk []).set .Nstk ((s1.get .Mstk).reverse ++ s1.get .Nstk)) = s2 := by
    apply Stk.ext_get <;> simp [s2, s1, set_inp, set_out]
    intro a; cases a <;> simp [Stk.get, Stk.set, hM, Nat.add_comm]
  rw [hs2] at r2
  have r3 := Run.wpush .Nstk tt (nrm (nrm v)) s2
  let s3 := { s2 with Nstk := List.replicate (V + M + 1) true }
  have hs3 : s2.set .Nstk (tt (nrm (nrm v)) :: s2.get .Nstk) = s3 := by
    apply Stk.ext_get <;> simp [s3, set_inp, set_out]
    intro a; cases a <;> simp [s2, Stk.get, Stk.set, List.replicate_succ, tt]
  rw [hs3] at r3
  have r4 := Run.wpush .Nstk tt (nrm (nrm v)) s3
  let s4 := { s2 with Nstk := List.replicate n true }
  have hs4 : s3.set .Nstk (tt (nrm (nrm v)) :: s3.get .Nstk) = s4 := by
    apply Stk.ext_get <;> simp [s4, s3, set_inp, set_out]
    intro a; cases a <;> simp [s2, Stk.get, Stk.set, List.replicate_succ, tt, n]
  rw [hs4] at r4
  have r5a := pushHdr_loop_spec n 0 (nrm (nrm v)) s4 rfl hNb
  let s5 := { s4 with OutRev := List.replicate n true }
  have r5 : Run (forC .Nstk .Nb (wpush .OutRev tt)) (nrm (nrm v)) s4 (nrm v) s5 (5 * n + 2) := by
    refine Run.conv (Run.seq r5a (Run.move .Nb .Nstk (by decide) _ _)) (by cases v; simp [nrm]) ?_ ?_
    · apply Stk.ext_get <;> simp [s5, s4, s2, set_inp, set_out]
      intro a; cases a <;> simp [Stk.get, Stk.set, hNb, hOut]
    · simp only [Stk.get, List.length_replicate, Nat.zero_add]; omega
  have r6 := Run.wpush .OutRev ff (nrm v) s5
  let s6 := { s4 with OutRev := (header n).reverse }
  have hs6 : s5.set .OutRev (ff (nrm v) :: s5.get .OutRev) = s6 := by
    apply Stk.ext_get <;> simp [s6, s5, set_inp, set_out]
    intro a; cases a <;> simp [Stk.get, Stk.set, header, ff]
  rw [hs6] at r6
  obtain ⟨p', r7⟩ := computeW_spec n (by omega) (nrm v) s6 rfl hNb hTmp hQ hQb hW
  refine ⟨p', Run.conv (Run.seq r1 (Run.seq r2 (Run.seq r3 (Run.seq r4 (Run.seq r5 (Run.seq r6 r7))))))
    (by cases v; simp [nrm]) ?_ ?_⟩
  · apply Stk.ext_get <;> (try rfl)
    intro a; cases a <;> simp [s6, s4, s2, Stk.get]
  · simp only [s1, Stk.get, Stk.set, hV, hM, List.length_replicate]
    have hn_def : n = V + M + 2 := rfl
    nlinarith

end Phases1to3

section Phase5AndFinal

open Turing

def emitAnchorsP : Pg :=
  Prog.seq (emitConst01 0 1)
    (Prog.seq (emitConst01 0 2)
      (Prog.seq (emitConst01 1 0)
        (Prog.seq (emitConst01 1 1)
          (Prog.seq (emitConst01 1 2)
            (Prog.seq (emitConst01 2 0)
              (Prog.seq (emitConst01 2 1) (emitConst01 2 2)))))))

def emitEmptyP : Pg :=
  Prog.ite (fun v => v.hasEmpty) (emitConst01 0 0) (Prog.load nrm)

def emitBoolBansP : Pg :=
  Prog.seq (wpush .Uocc tt)
    (Prog.seq (wpush .Uocc tt)
      (forPop .Vstk (fun v _ => v) id
        (Prog.seq (emit0Stk .Uocc 2) (wpush .Uocc tt))))

def emitTransAll : Pg :=
  Prog.seq (emitTransOne 0 2)
    (Prog.seq (emitTransOne 1 0)
      (Prog.seq (emitTransOne 1 1)
        (Prog.seq (emitTransOne 2 0) (emitTransOne 2 1))))

def emitLitLookup : Pg :=
  Prog.seq (move .Drev .CurV)
    (Prog.seq lookupP
      (Prog.seq (drain .CurV)
        (Prog.seq (move .SeenVb .SeenV)
          (Prog.seq (wpush .Vidx tt)
            (Prog.seq (wpush .Vidx tt)
              (Prog.seq (emitLitBan false 0)
                (Prog.seq (emitLitBan true 1) (drain .Vidx))))))))

def phase5Step : Pg :=
  Prog.ite (fun v => !v.half)
    (Prog.load fun v => { v with b0 := v.u, half := true })
    (Prog.seq (Prog.load fun v => { v with half := false })
      (Prog.ite (fun v => !v.inLit)
        (Prog.ite (fun v => v.b0)
          (Prog.seq (Prog.load fun v => { v with pol := v.u, inLit := true })
            (Prog.ite (fun v => !v.inClause)
              (Prog.seq (emit0Stk .Uocc 2) (Prog.load fun v => { v with inClause := true }))
              (Prog.seq emitTransAll (wpush .Uocc tt))))
          (Prog.ite (fun v => v.inClause)
            (Prog.seq (emit0Stk .Uocc 0)
              (Prog.seq (wpush .Uocc tt) (Prog.load fun v => { v with inClause := false })))
            (Prog.load id)))
        (Prog.ite (fun v => v.b0)
          (wpush .Drev (fun v => v.u))
          (Prog.seq (Prog.load fun v => { v with inLit := false }) emitLitLookup))))

def phase5Loop : Pg :=
  forPop .X (fun v b => { v with u := b }) id phase5Step

def emitClausesP : Pg :=
  Prog.seq (Prog.load fun v => { v with half := false, inLit := false, inClause := false })
    phase5Loop

def drainAll : Pg :=
  [.X, .Xrev, .Mstk, .Vstk, .Nstk, .Nb, .Wstk, .Wb, .Q, .Qb,
   .Drev, .CurV, .CurVb, .SeenV, .SeenVb, .Vidx, .Uocc, .Tmp, .OutRev].foldr
    (fun a p => Prog.seq (drain a) p) (Prog.load id)

def validBranch : Pg :=
  Prog.seq phase2P
    (Prog.seq phase3P
      (Prog.seq emitAnchorsP
        (Prog.seq emitEmptyP
          (Prog.seq emitBoolBansP
            (Prog.seq emitClausesP moveOut)))))

def prog : Pg :=
  Prog.seq phase1P
    (Prog.seq (Prog.ite (fun v => decide (v.ws = .a)) validBranch (Prog.load id))
      drainAll)

theorem noTouch_emitQ (k : K) (h1 : K.w .Wstk ≠ k) (h2 : K.w .Wb ≠ k)
    (h3 : K.w .Q ≠ k) (h4 : K.w .Qb ≠ k) (h5 : K.w .OutRev ≠ k) : NoTouch k emitQ := by
  simp [emitQ, emitQStep, noTouch_seq, noTouch_forC, noTouch_drain, noTouch_halveOnce,
    noTouch_wpush, noTouch_move, h1, h2, h3, h4, h5]

theorem noTouch_pushColor (k : K) (c : Nat) (h : K.w .OutRev ≠ k) : NoTouch k (pushColor c) := by
  simp [pushColor, noTouch_seq, noTouch_wpush, h]

theorem wf_pushColor (c : Nat) : WF (pushColor c) := by
  simp [pushColor, wf_seq, wf_wpush]

theorem wf_emitConst01 (c1 c2 : Nat) : WF (emitConst01 c1 c2) := by
  simp [emitConst01, wf_seq, wf_emitQ, wf_pushColor, wf_wpush]

theorem wf_emit0Stk (src : W) (h1 : src ≠ .Tmp) (h2 : src ≠ .Q) : WF (emit0Stk src c2) := by
  simp [emit0Stk, wf_seq, wf_emitQ, wf_pushColor, wf_copyS, h1, Ne.symm h1, Ne.symm h2]

theorem wf_emitLitBan (pf : Bool) (c2 : Nat) : WF (emitLitBan pf c2) := by
  simp [emitLitBan, wf_seq, wf_copyS, wf_emitQ, wf_wpush, wf_pushColor]

theorem wf_emitTransOne (c1 c2 : Nat) : WF (emitTransOne c1 c2) := by
  simp [emitTransOne, wf_seq, wf_copyS, wf_emitQ, wf_pushColor, wf_wpush]

theorem noTouch_emit0Stk (k : K) (src : W) (c2 : Nat)
    (hs : K.w src ≠ k) (h1 : K.w .Wstk ≠ k) (h2 : K.w .Wb ≠ k) (h3 : K.w .Q ≠ k)
    (h4 : K.w .Qb ≠ k) (h5 : K.w .Tmp ≠ k) (h6 : K.w .OutRev ≠ k) :
    NoTouch k (emit0Stk src c2) := by
  simp [emit0Stk, noTouch_seq, noTouch_emitQ, noTouch_pushColor, noTouch_copyS,
    hs, h1, h2, h3, h4, h5, h6]

theorem noTouch_phase5Step : NoTouch (K.w .X) phase5Step := by
  simp [phase5Step, emitTransAll, emitTransOne, emitLitLookup, emitLitBan, noTouch_seq,
    noTouch_ite, noTouch_load, noTouch_wpush, noTouch_move, noTouch_drain, noTouch_copyS,
    noTouch_emitQ, noTouch_pushColor, noTouch_lookupP, noTouch_emit0Stk]

theorem exec_phase5Loop_cons (v : Reg) (s : Stk) (x : Bool) (xs : List Bool)
    (h : s.get .X = x :: xs) :
    exec phase5Loop ⟨v, toFun s⟩ =
      exec phase5Loop (exec phase5Step ⟨{ v with u := x, go := true }, toFun (s.set .X xs)⟩) := by
  exact exec_forPop_cons .X (fun v b => { v with u := b }) id phase5Step v s x xs h noTouch_phase5Step

theorem cost_phase5Loop_cons (v : Reg) (s : Stk) (x : Bool) (xs : List Bool)
    (h : s.get .X = x :: xs) :
    cost phase5Loop ⟨v, toFun s⟩ =
      cost phase5Loop (exec phase5Step ⟨{ v with u := x, go := true }, toFun (s.set .X xs)⟩) +
        (cost phase5Step ⟨{ v with u := x, go := true }, toFun (s.set .X xs)⟩ + 1) := by
  exact cost_forPop_cons .X (fun v b => { v with u := b }) id phase5Step v s x xs h noTouch_phase5Step

theorem wf_moveOut : WF moveOut := by
  refine ⟨fun _ => rfl, ?_, trivial⟩
  intro h; cases h

theorem wf_phase5Loop : WF phase5Loop := by
  rw [phase5Loop, wf_forPop]
  refine ⟨noTouch_phase5Step, ?_⟩
  simp [phase5Step, emitTransAll, emitLitLookup, wf_seq, wf_ite, wf_load, wf_wpush, wf_move,
    wf_drain, wf_lookupP, wf_emit0Stk, wf_emitTransOne, wf_emitLitBan]

theorem wf_prog : WF prog := by
  simp [prog, validBranch, emitAnchorsP, emitEmptyP, emitBoolBansP, emitClausesP, drainAll,
    wf_seq, wf_ite, wf_load, wf_phase1P, wf_phase2P, wf_phase3P, wf_emitConst01, wf_emit0Stk,
    wf_forPop, wf_wpush, wf_drain, wf_phase5Loop, wf_moveOut, noTouch_seq, noTouch_wpush,
    noTouch_emit0Stk]

theorem emitAnchorsP_spec (w : Nat) (v : Reg) (s : Stk)
    (hW : s.Wstk = List.replicate w true) (hWb : s.Wb = []) (hQ : s.Q = []) (hQb : s.Qb = []) :
    ∃ p' : Bool,
      Run emitAnchorsP v s (nrm { v with par := p' })
        { s with OutRev := (anchorBans.flatMap (encBan w)).reverse ++ s.OutRev }
        (160 * (w + 1) + 120) := by
  obtain ⟨p1, r1⟩ := emitConst01_spec w 0 1 v s hW hWb hQ hQb
  let v1 := nrm { v with par := p1 }
  let s1 := { s with OutRev := (encBan w ((0, 0), (1, 1))).reverse ++ s.OutRev }
  obtain ⟨p2, r2⟩ := emitConst01_spec w 0 2 v1 s1 hW hWb hQ hQb
  let v2 := nrm { v1 with par := p2 }
  let s2 := { s1 with OutRev := (encBan w ((0, 0), (1, 2))).reverse ++ s1.OutRev }
  obtain ⟨p3, r3⟩ := emitConst01_spec w 1 0 v2 s2 hW hWb hQ hQb
  let v3 := nrm { v2 with par := p3 }
  let s3 := { s2 with OutRev := (encBan w ((0, 1), (1, 0))).reverse ++ s2.OutRev }
  obtain ⟨p4, r4⟩ := emitConst01_spec w 1 1 v3 s3 hW hWb hQ hQb
  let v4 := nrm { v3 with par := p4 }
  let s4 := { s3 with OutRev := (encBan w ((0, 1), (1, 1))).reverse ++ s3.OutRev }
  obtain ⟨p5, r5⟩ := emitConst01_spec w 1 2 v4 s4 hW hWb hQ hQb
  let v5 := nrm { v4 with par := p5 }
  let s5 := { s4 with OutRev := (encBan w ((0, 1), (1, 2))).reverse ++ s4.OutRev }
  obtain ⟨p6, r6⟩ := emitConst01_spec w 2 0 v5 s5 hW hWb hQ hQb
  let v6 := nrm { v5 with par := p6 }
  let s6 := { s5 with OutRev := (encBan w ((0, 2), (1, 0))).reverse ++ s5.OutRev }
  obtain ⟨p7, r7⟩ := emitConst01_spec w 2 1 v6 s6 hW hWb hQ hQb
  let v7 := nrm { v6 with par := p7 }
  let s7 := { s6 with OutRev := (encBan w ((0, 2), (1, 1))).reverse ++ s6.OutRev }
  obtain ⟨p8, r8⟩ := emitConst01_spec w 2 2 v7 s7 hW hWb hQ hQb
  refine ⟨p8, Run.conv (Run.seq r1 (Run.seq r2 (Run.seq r3 (Run.seq r4 (Run.seq r5 (Run.seq r6 (Run.seq r7 r8)))))))
    (by cases v; simp [v7, v6, v5, v4, v3, v2, v1, nrm]) ?_ (by omega)⟩
  apply Stk.ext_get <;> (try rfl)
  intro a; cases a <;> simp [s7, s6, s5, s4, s3, s2, s1, Stk.get, anchorBans, List.append_assoc]

theorem emitEmptyP_spec (F : CNF) (w : Nat) (v : Reg) (s : Stk)
    (hemp : v.hasEmpty = F.any List.isEmpty)
    (hW : s.Wstk = List.replicate w true) (hWb : s.Wb = []) (hQ : s.Q = []) (hQb : s.Qb = []) :
    ∃ p' : Bool,
      Run emitEmptyP v s (nrm { v with par := p' })
        { s with OutRev := ((emptyBan F).flatMap (encBan w)).reverse ++ s.OutRev }
        (20 * (w + 1) + 16) := by
  cases he : F.any List.isEmpty
  · refine ⟨v.par, Run.conv (Run.ite_false (c := fun v : Reg => v.hasEmpty) (p := emitConst01 0 0)
      (by simp [hemp, he]) (Run.load nrm v s)) ?_ ?_ (by omega)⟩
    · cases v; simp [nrm]
    · apply Stk.ext_get <;> (try rfl)
      intro a; cases a <;> simp [Stk.get, emptyBan, he]
  · obtain ⟨p1, r1⟩ := emitConst01_spec w 0 0 v s hW hWb hQ hQb
    refine ⟨p1, Run.conv (Run.ite_true (c := fun v : Reg => v.hasEmpty) (q := Prog.load nrm)
      (by simp [hemp, he]) r1) (by cases v; simp [nrm]) ?_ (by omega)⟩
    apply Stk.ext_get <;> (try rfl)
    intro a; cases a <;> simp [Stk.get, emptyBan, he]

theorem emitBoolBans_loop_spec (w n : Nat) (t : Nat) :
    ∀ (u : Nat) (v : Reg) (s : Stk),
      u + t ≤ n →
      s.Vstk = List.replicate t true → s.Uocc = List.replicate u true →
      s.Wstk = List.replicate w true → s.Wb = [] → s.Q = [] → s.Qb = [] → s.Tmp = [] →
      ∃ p' : Bool,
        Run (forPop .Vstk (fun v _ => v) id (Prog.seq (emit0Stk .Uocc 2) (wpush .Uocc tt))) v s
          (nrm { v with par := p' })
          { s with Vstk := [], Uocc := List.replicate (u + t) true, OutRev := (((List.range t).map (fun i => ((0, 0), (u + i, 2)))).flatMap (encBan w)).reverse ++ s.OutRev }
          (t * ((w + 1) * (4 * n + 16) + 7 * n + 18) + 1) := by
  have hnt : NoTouch (K.w .Vstk) (Prog.seq (emit0Stk .Uocc 2) (wpush .Uocc tt)) := by
    simp [emit0Stk, noTouch_seq, noTouch_emitQ, noTouch_pushColor, noTouch_copyS, noTouch_wpush]
  induction t with
  | zero =>
    intro u v s _ hV hU _ _ _ _ _
    have hVg : s.get .Vstk = [] := hV
    refine ⟨v.par, ?_, ?_⟩
    · rw [exec_forPop_nil _ _ _ _ _ _ hVg]
      refine St_eq _ _ _ _ (by cases v; simp [nrm]) ?_
      apply Stk.ext_get <;> (try rfl)
      intro a; cases a <;> simp [Stk.get, hV, hU]
    · rw [cost_forPop_nil _ _ _ _ _ _ hVg]; simp
  | succ t ih =>
    intro u v s hun hV hU hW hWb hQ hQb hTmp
    have hVg : s.get .Vstk = true :: List.replicate t true := by
      simpa [Stk.get, List.replicate_succ] using hV
    let v1 : Reg := { v with go := true }
    let s1 : Stk := s.set .Vstk (List.replicate t true)
    obtain ⟨p1, r1⟩ := emit0Stk_spec .Uocc (by decide) (by decide) (by decide) w u 2 v1 s1
      (by simp [s1, Stk.set, hW]) (by simp [s1, Stk.set, hWb])
      (by simp [s1, Stk.set, hQ]) (by simp [s1, Stk.set, hQb])
      (by simp [s1, Stk.set, hTmp]) (by simp [s1, Stk.get, Stk.set, hU])
    let v2 : Reg := nrm { v1 with par := p1 }
    let s2 : Stk := { s1 with OutRev := (encBan w ((0, 0), (u, 2))).reverse ++ s1.OutRev }
    have r2 := Run.wpush .Uocc tt v2 s2
    let s3 : Stk := { s2 with Uocc := List.replicate (u + 1) true }
    have hs3 : s2.set .Uocc (tt v2 :: s2.get .Uocc) = s3 := by
      apply Stk.ext_get <;> simp [s3, set_inp, set_out]
      intro a; cases a <;> simp [s2, s1, Stk.get, Stk.set, hU, List.replicate_succ, tt]
    rw [hs3] at r2
    have hbody := Run.seq r1 r2
    obtain ⟨p2, e1, e2⟩ := ih (u + 1) v2 s3 (by omega)
      (by simp [s3, s2, s1, Stk.set]) rfl (by simp [s3, s2, s1, Stk.set, hW])
      (by simp [s3, s2, s1, Stk.set, hWb]) (by simp [s3, s2, s1, Stk.set, hQ])
      (by simp [s3, s2, s1, Stk.set, hQb]) (by simp [s3, s2, s1, Stk.set, hTmp])
    refine ⟨p2, ?_, ?_⟩
    · rw [exec_forPop_cons _ _ _ _ _ _ true (List.replicate t true) hVg hnt]
      change exec _ (exec _ ⟨v1, toFun s1⟩) = _
      rw [hbody.1, e1]
      refine St_eq _ _ _ _ (by cases v; simp [v2, v1, nrm]) ?_
      apply Stk.ext_get <;> (try rfl)
      intro a
      cases a <;> simp only [s3, s2, s1, Stk.get, Stk.set]
      all_goals
        first
        | (simp [show u + 1 + t = u + (t + 1) by omega])
        | (rw [List.range_succ_eq_map, List.map_cons, List.flatMap_cons, List.reverse_append,
            List.map_map]; simp only [List.append_assoc]; congr 3; apply List.map_congr_left;
            intro i _; simp only [Function.comp_def, Prod.mk.injEq, true_and, and_true]; omega)
    · rw [cost_forPop_cons _ _ _ _ _ _ true (List.replicate t true) hVg hnt]
      change cost _ (exec _ ⟨v1, toFun s1⟩) + (cost _ ⟨v1, toFun s1⟩ + 1) ≤ _
      rw [hbody.1]
      have hbc := hbody.2
      have huw : (w + 1) * (4 * u + 16) ≤ (w + 1) * (4 * n + 16) :=
        Nat.mul_le_mul_left (w + 1) (by omega)
      have hstep : (t + 1) * ((w + 1) * (4 * n + 16) + 7 * n + 18) =
          t * ((w + 1) * (4 * n + 16) + 7 * n + 18) + ((w + 1) * (4 * n + 16) + 7 * n + 18) := by ring
      rw [hstep]
      omega

theorem emitBoolBansP_spec (V w n : Nat) (hVn : 2 + V ≤ n) (v : Reg) (s : Stk)
    (hV : s.Vstk = List.replicate V true) (hU : s.Uocc = [])
    (hW : s.Wstk = List.replicate w true) (hWb : s.Wb = [])
    (hQ : s.Q = []) (hQb : s.Qb = []) (hTmp : s.Tmp = []) :
    ∃ p' : Bool,
      Run emitBoolBansP v s (nrm { v with par := p' })
        { s with Vstk := [], Uocc := List.replicate (2 + V) true, OutRev := ((boolBans V).flatMap (encBan w)).reverse ++ s.OutRev }
        (V * ((w + 1) * (4 * n + 16) + 7 * n + 18) + 3) := by
  have r1 := Run.wpush .Uocc tt v s
  let s1 := s.set .Uocc [true]
  have hs1 : s.set .Uocc (tt v :: s.get .Uocc) = s1 := by simp [s1, Stk.get, hU, tt]
  rw [hs1] at r1
  have r2 := Run.wpush .Uocc tt v s1
  let s2 := { s with Uocc := List.replicate 2 true }
  have hs2 : s1.set .Uocc (tt v :: s1.get .Uocc) = s2 := by
    apply Stk.ext_get <;> simp [s2, s1, set_inp, set_out]
    intro a; cases a <;> simp [Stk.get, Stk.set, tt]
  rw [hs2] at r2
  obtain ⟨p', r3⟩ := emitBoolBans_loop_spec w n V 2 v s2 hVn hV rfl hW hWb hQ hQb hTmp
  refine ⟨p', Run.conv (Run.seq r1 (Run.seq r2 r3)) rfl ?_ (by omega)⟩
  apply Stk.ext_get <;> (try rfl)
  intro a; cases a <;> simp [s2, Stk.get, boolBans]

theorem emitTransAll_spec (w u : Nat) (v : Reg) (s : Stk)
    (hW : s.Wstk = List.replicate w true) (hWb : s.Wb = [])
    (hQ : s.Q = []) (hQb : s.Qb = []) (hTmp : s.Tmp = [])
    (hU : s.Uocc = List.replicate u true) :
    ∃ p' : Bool,
      Run emitTransAll v s (nrm { v with par := p' })
        { s with OutRev := ((transBans u).flatMap (encBan w)).reverse ++ s.OutRev }
        (5 * ((w + 1) * (8 * u + 20) + 14 * u + 20)) := by
  obtain ⟨p1, r1⟩ := emitTransOne_spec w u 0 2 v s hW hWb hQ hQb hTmp hU
  let v1 := nrm { v with par := p1 }
  let s1 := { s with OutRev := (encBan w ((u, 0), (u + 1, 2))).reverse ++ s.OutRev }
  obtain ⟨p2, r2⟩ := emitTransOne_spec w u 1 0 v1 s1 hW hWb hQ hQb hTmp hU
  let v2 := nrm { v1 with par := p2 }
  let s2 := { s1 with OutRev := (encBan w ((u, 1), (u + 1, 0))).reverse ++ s1.OutRev }
  obtain ⟨p3, r3⟩ := emitTransOne_spec w u 1 1 v2 s2 hW hWb hQ hQb hTmp hU
  let v3 := nrm { v2 with par := p3 }
  let s3 := { s2 with OutRev := (encBan w ((u, 1), (u + 1, 1))).reverse ++ s2.OutRev }
  obtain ⟨p4, r4⟩ := emitTransOne_spec w u 2 0 v3 s3 hW hWb hQ hQb hTmp hU
  let v4 := nrm { v3 with par := p4 }
  let s4 := { s3 with OutRev := (encBan w ((u, 2), (u + 1, 0))).reverse ++ s3.OutRev }
  obtain ⟨p5, r5⟩ := emitTransOne_spec w u 2 1 v4 s4 hW hWb hQ hQb hTmp hU
  refine ⟨p5, Run.conv (Run.seq r1 (Run.seq r2 (Run.seq r3 (Run.seq r4 r5))))
    (by cases v; simp [v4, v3, v2, v1, nrm]) ?_ (by omega)⟩
  apply Stk.ext_get <;> (try rfl)
  intro a; cases a <;> simp [s4, s3, s2, s1, Stk.get, transBans, List.append_assoc]

theorem emitLitLookup_spec (ord : List Nat) (l : Literal) (w u n z : Nat)
    (hlmem : l.1 ∈ ord) (hVn : 2 + ord.length ≤ n) (hun : u ≤ n)
    (hsz : (encodeVars (ord.map Nat.bits)).length ≤ z)
    (v : Reg) (s : Stk) (hpol : v.pol = l.2)
    (hD : s.Drev = l.1.bits.reverse) (hCV : s.CurV = []) (hCVb : s.CurVb = [])
    (hSV : s.SeenV = encodeVars (ord.map Nat.bits)) (hSVb : s.SeenVb = [])
    (hVi : s.Vidx = []) (hW : s.Wstk = List.replicate w true) (hWb : s.Wb = [])
    (hQ : s.Q = []) (hQb : s.Qb = []) (hTmp : s.Tmp = [])
    (hU : s.Uocc = List.replicate u true) :
    ∃ (b0' exp' eq' fnd' par' : Bool),
      Run emitLitLookup v s
        (nrm { v with b0 := b0', expectData := exp', eqFlag := eq', found := fnd', par := par' })
        { s with Drev := [], OutRev := ((litBans ord u l).flatMap (encBan w)).reverse ++ s.OutRev }
        (2 * ((w + 1) * (8 * n + 16) + 14 * n + 16) + 25 * z + 4 * l.1.bits.length + 20) := by
  have r1 := Run.move .Drev .CurV (by decide) v s
  let s1 := { s with Drev := [], CurV := l.1.bits }
  have hs1 : ((s.set .Drev []).set .CurV ((s.get .Drev).reverse ++ s.get .CurV)) = s1 := by
    apply Stk.ext_get <;> simp [s1, set_inp, set_out]
    intro a; cases a <;> simp [Stk.get, Stk.set, hD, hCV]
  rw [hs1] at r1
  obtain ⟨b01, par1, r2⟩ := lookupP_spec l.1.bits (ord.map Nat.bits) (nrm v) s1 hSV hSVb rfl hCVb hVi
  let v2 := nrm { nrm v with b0 := b01, expectData := false, eqFlag := true, found := decide (l.1.bits ∈ ord.map Nat.bits), par := par1 }
  let idx := ord.idxOf l.1
  have hidx_eq : (ord.map Nat.bits).idxOf l.1.bits = idx :=
    idxOf_map_injective Nat.bits bits_injective ord l.1
  have hidx_lt : idx < ord.length := List.idxOf_lt_length_of_mem hlmem
  let s2 := { s1 with SeenV := [], SeenVb := (encodeVars (ord.map Nat.bits)).reverse, Vidx := List.replicate idx true }
  have r2' : Run lookupP (nrm v) s1 v2 s2 (20 * (encodeVars (ord.map Nat.bits)).length + 2) := by
    simpa [v2, s2, hidx_eq] using r2
  have r3 := Run.drain .CurV v2 s2
  let s3 := { s2 with CurV := [] }
  have hs3 : s2.set .CurV [] = s3 := by
    apply Stk.ext_get <;> simp [s3, set_inp, set_out]
    intro a; cases a <;> simp [Stk.get, Stk.set]
  rw [hs3] at r3
  have r4 := Run.move .SeenVb .SeenV (by decide) (nrm v2) s3
  let s4 := { s with Drev := [], Vidx := List.replicate idx true }
  have hs4 : ((s3.set .SeenVb []).set .SeenV ((s3.get .SeenVb).reverse ++ s3.get .SeenV)) = s4 := by
    apply Stk.ext_get <;> simp [s4, s3, s2, s1, set_inp, set_out]
    intro a; cases a <;> simp [Stk.get, Stk.set, hCV, hSV, hSVb]
  rw [hs4] at r4
  have r5 := Run.wpush .Vidx tt (nrm (nrm v2)) s4
  let s5 := { s4 with Vidx := List.replicate (idx + 1) true }
  have hs5 : s4.set .Vidx (tt (nrm (nrm v2)) :: s4.get .Vidx) = s5 := by
    apply Stk.ext_get <;> simp [s5, set_inp, set_out]
    intro a; cases a <;> simp [s4, Stk.get, Stk.set, List.replicate_succ, tt]
  rw [hs5] at r5
  have r6 := Run.wpush .Vidx tt (nrm (nrm v2)) s5
  let s6 := { s with Drev := [], Vidx := List.replicate (2 + idx) true }
  have hs6 : s5.set .Vidx (tt (nrm (nrm v2)) :: s5.get .Vidx) = s6 := by
    apply Stk.ext_get <;> simp [s6, s5, s4, set_inp, set_out]
    have h2i : 2 + idx = (idx + 1) + 1 := by omega
    intro a; cases a <;> simp [Stk.get, Stk.set, h2i, List.replicate_succ, tt]
  rw [hs6] at r6
  obtain ⟨p7, r7⟩ := emitLitBan_spec false w (2 + idx) u 0 (nrm (nrm v2)) s6 hW hWb hQ hQb hTmp rfl hU
  let v7 := nrm { nrm (nrm v2) with par := p7 }
  let s7 := { s6 with OutRev := (encBan w ((2 + idx, if false then (if (nrm (nrm v2)).pol then 0 else 1) else (if (nrm (nrm v2)).pol then 1 else 0)), (u, 0))).reverse ++ s6.OutRev }
  obtain ⟨p8, r8⟩ := emitLitBan_spec true w (2 + idx) u 1 v7 s7 hW hWb hQ hQb hTmp rfl hU
  let v8 := nrm { v7 with par := p8 }
  let s8 := { s7 with OutRev := (encBan w ((2 + idx, if true then (if v7.pol then 0 else 1) else (if v7.pol then 1 else 0)), (u, 1))).reverse ++ s7.OutRev }
  have r9 := Run.drain .Vidx v8 s8
  refine ⟨b01, false, true, decide (l.1.bits ∈ ord.map Nat.bits), p8,
    Run.conv (Run.seq r1 (Run.seq r2' (Run.seq r3 (Run.seq r4 (Run.seq r5 (Run.seq r6 (Run.seq r7 (Run.seq r8 r9))))))))
      (by cases v; simp [v8, v7, v2, nrm]) ?_ ?_⟩
  · apply Stk.ext_get <;> simp [s8, s7, s6, set_inp, set_out]
    intro a
    cases a <;> simp only [v7, v2, Stk.get, Stk.set, hVi, nrm, hpol, litBans, idx]
    simp [List.append_assoc]
  · simp only [s8, s7, s6, s3, s2, s1, Stk.get, hD, List.length_reverse, List.length_replicate]
    have hvi_le : 2 + idx ≤ n := by omega
    have hidx_z : 2 + idx ≤ z + 2 := by
      have h1 : ord.length ≤ (encodeVars (ord.map Nat.bits)).length := by
        simpa using vs_len_le_encodeVars (ord.map Nat.bits)
      omega
    have hmul : (w + 1) * (4 * (2 + idx) + 4 * u + 16) ≤ (w + 1) * (8 * n + 16) :=
      Nat.mul_le_mul_left (w + 1) (by omega)
    omega

theorem phase5_pair_inLit_true (d : Bool) (rest : List Bool) (v : Reg) (s : Stk)
    (hh : v.half = false) (hil : v.inLit = true) (hX : s.X = true :: d :: rest) :
    let v' : Reg := { v with go := true, u := d, b0 := true, half := false, inLit := true }
    let s' : Stk := { s with X := rest, Drev := d :: s.Drev }
    exec phase5Loop ⟨v, toFun s⟩ = exec phase5Loop ⟨v', toFun s'⟩ ∧
      cost phase5Loop ⟨v, toFun s⟩ ≤ cost phase5Loop ⟨v', toFun s'⟩ + 14 := by
  have hX1 : s.get .X = true :: d :: rest := hX
  let v1 : Reg := { v with go := true, u := true, b0 := true, half := true }
  let s1 : Stk := { s with X := d :: rest }
  have hs1 : exec phase5Step ⟨{ v with u := true, go := true }, toFun (s.set .X (d :: rest))⟩ = ⟨v1, toFun s1⟩ ∧
      cost phase5Step ⟨{ v with u := true, go := true }, toFun (s.set .X (d :: rest))⟩ ≤ 4 := by
    refine ⟨?_, ?_⟩
    · simp only [phase5Step, exec, hh, Bool.not_false, ite_true]
      refine St_eq _ _ _ _ (by cases v; rfl) ?_
      apply Stk.ext_get <;> simp [s1, set_inp, set_out]
      intro a; cases a <;> simp [Stk.get, Stk.set]
    · simp [phase5Step, cost, hh]
  let v2 : Reg := { v with go := true, u := d, b0 := true, half := false, inLit := true }
  let s2 : Stk := { s with X := rest, Drev := d :: s.Drev }
  have hs2 : exec phase5Step ⟨{ v1 with u := d, go := true }, toFun (s1.set .X rest)⟩ = ⟨v2, toFun s2⟩ ∧
      cost phase5Step ⟨{ v1 with u := d, go := true }, toFun (s1.set .X rest)⟩ ≤ 8 := by
    refine ⟨?_, ?_⟩
    · simp only [phase5Step, exec, exec_wpush, v1, hil, Bool.not_true, Bool.false_eq_true, ite_false, ite_true]
      refine St_eq _ _ _ _ (by cases v; simp [v2]) ?_
      apply Stk.ext_get <;> simp [s2, s1, set_inp, set_out]
      intro a; cases a <;> simp [Stk.get, Stk.set]
    · simp [phase5Step, exec, cost, wpush, v1, hil]
  have hX2 : s1.get .X = d :: rest := rfl
  refine ⟨?_, ?_⟩
  · rw [exec_phase5Loop_cons _ _ true (d :: rest) hX1, hs1.1, exec_phase5Loop_cons _ _ d rest hX2, hs2.1]
  · rw [cost_phase5Loop_cons _ _ true (d :: rest) hX1, hs1.1, cost_phase5Loop_cons _ _ d rest hX2, hs2.1]
    have h1 := hs1.2; have h2 := hs2.2
    dsimp only [v2, s2]
    omega

theorem phase5_digits (ds : List Bool) :
    ∀ (rest : List Bool) (v : Reg) (s : Stk),
      v.half = false → v.inLit = true →
      s.X = (ds.flatMap fun d => [true, d]) ++ rest →
      ∃ (u' b0' : Bool),
        let v' : Reg := { v with go := true, u := u', b0 := b0', half := false, inLit := true }
        let s' : Stk := { s with X := rest, Drev := ds.reverse ++ s.Drev }
        exec phase5Loop ⟨v, toFun s⟩ = exec phase5Loop ⟨v', toFun s'⟩ ∧
          cost phase5Loop ⟨v, toFun s⟩ ≤ cost phase5Loop ⟨v', toFun s'⟩ + 14 * ds.length := by
  induction ds with
  | nil =>
    intro rest v s hh hil hX
    refine ⟨v.u, v.b0, ?_, ?_⟩
    · cases rest with
      | nil =>
        have hXg : s.get .X = [] := hX
        rw [phase5Loop, exec_forPop_nil _ _ _ _ _ _ hXg, exec_forPop_nil _ _ _ _ _ _ rfl]
        refine St_eq _ _ _ _ (by cases v; simp_all [nrm]) ?_
        apply Stk.ext_get <;> (try rfl); intro a; cases a <;> simp [Stk.get, hX]
      | cons x xs =>
        have hXg : s.get .X = x :: xs := hX
        rw [phase5Loop, exec_forPop_cons _ _ _ _ _ _ x xs hXg noTouch_phase5Step,
          exec_forPop_cons _ _ _ _ _ _ x xs rfl noTouch_phase5Step]
        congr 2
        refine St_eq _ _ _ _ (by cases v; simp_all) ?_
        apply Stk.ext_get <;> simp [set_inp, set_out]
        intro a; cases a <;> simp [Stk.get, Stk.set]
    · cases rest with
      | nil =>
        have hXg : s.get .X = [] := hX
        rw [phase5Loop, cost_forPop_nil _ _ _ _ _ _ hXg, cost_forPop_nil _ _ _ _ _ _ rfl]; omega
      | cons x xs =>
        have hXg : s.get .X = x :: xs := hX
        rw [phase5Loop, cost_forPop_cons _ _ _ _ _ _ x xs hXg noTouch_phase5Step,
          cost_forPop_cons _ _ _ _ _ _ x xs rfl noTouch_phase5Step]
        have heq : (⟨{ ({ v with u := x }) with go := true }, toFun (s.set .X xs)⟩ : St K Γ Reg) =
            ⟨{ ({ ({ v with go := true, u := v.u, b0 := v.b0, half := false, inLit := true }) with u := x }) with go := true },
              toFun (({ s with X := x :: xs, Drev := s.Drev }).set .X xs)⟩ := by
          refine St_eq _ _ _ _ (by cases v; simp_all) ?_
          apply Stk.ext_get <;> (try simp [set_inp, set_out])
          intro a; cases a <;> simp [Stk.get, Stk.set]
        simp only [List.reverse_nil, List.nil_append, List.length_nil,
          Nat.mul_zero, Nat.add_zero]
        rw [heq]
  | cons d ds ih =>
    intro rest v s hh hil hX
    have hX' : s.X = true :: d :: ((ds.flatMap fun d => [true, d]) ++ rest) := by simpa using hX
    obtain ⟨he1, hc1⟩ := phase5_pair_inLit_true d ((ds.flatMap fun d => [true, d]) ++ rest) v s hh hil hX'
    let v1 : Reg := { v with go := true, u := d, b0 := true, half := false, inLit := true }
    let s1 : Stk := { s with X := (ds.flatMap fun d => [true, d]) ++ rest, Drev := d :: s.Drev }
    obtain ⟨u', b0', he2, hc2⟩ := ih rest v1 s1 rfl rfl rfl
    refine ⟨u', b0', ?_, ?_⟩
    · rw [he1, he2]
      congr 1
      refine St_eq _ _ _ _ (by cases v; rfl) ?_
      apply Stk.ext_get <;> (try rfl)
      intro a; cases a <;> simp [s1, Stk.get, List.append_assoc]
    · have hceq : cost phase5Loop ⟨{ v1 with go := true, u := u', b0 := b0', half := false, inLit := true }, toFun { s1 with X := rest, Drev := ds.reverse ++ s1.Drev }⟩ =
          cost phase5Loop ⟨{ v with go := true, u := u', b0 := b0', half := false, inLit := true }, toFun { s with X := rest, Drev := (d :: ds).reverse ++ s.Drev }⟩ := by
        congr 1
        refine St_eq _ _ _ _ (by cases v; rfl) ?_
        apply Stk.ext_get <;> (try rfl)
        intro a; cases a <;> simp [s1, Stk.get, List.append_assoc]
      rw [hceq] at hc2
      dsimp only [v1, s1] at hc2
      simp only [List.length_cons]
      omega

theorem phase5_lit (ord : List Nat) (l : Literal) (rest : List Bool) (w u n z : Nat)
    (inC : Bool) (hlmem : l.1 ∈ ord) (hVn : 2 + ord.length ≤ n)
    (hun : (if inC then u + 1 else u) ≤ n)
    (hsz : (encodeVars (ord.map Nat.bits)).length ≤ z)
    (v : Reg) (s : Stk)
    (hh : v.half = false) (hil : v.inLit = false) (hic : v.inClause = inC)
    (hX : s.X = encodeLiteral l ++ rest)
    (hD : s.Drev = []) (hCV : s.CurV = []) (hCVb : s.CurVb = [])
    (hSV : s.SeenV = encodeVars (ord.map Nat.bits)) (hSVb : s.SeenVb = [])
    (hVi : s.Vidx = []) (hW : s.Wstk = List.replicate w true) (hWb : s.Wb = [])
    (hQ : s.Q = []) (hQb : s.Qb = []) (hTmp : s.Tmp = [])
    (hU : s.Uocc = List.replicate u true) :
    let u' := if inC then u + 1 else u
    let preBans : List Ban := if inC then transBans u else [((0, 0), (u, 2))]
    ∃ (b0' exp' eq' fnd' par' : Bool),
      let v' : Reg := nrm { v with b0 := b0', half := false, inLit := false, inClause := true, pol := l.2, expectData := exp', eqFlag := eq', found := fnd', par := par' }
      let s' : Stk := { s with X := rest, Uocc := List.replicate u' true, OutRev := ((preBans ++ litBans ord u' l).flatMap (encBan w)).reverse ++ s.OutRev }
      exec phase5Loop ⟨v, toFun s⟩ = exec phase5Loop ⟨v', toFun s'⟩ ∧
        cost phase5Loop ⟨v, toFun s⟩ ≤ cost phase5Loop ⟨v', toFun s'⟩ +
          (60 * (w + 1) * (n + 3) + 120 * n + 25 * z + 18 * l.1.bits.length + 180) := by
  intro u' preBans
  have hX1 : s.get .X = true :: l.2 :: (vcode l.1 ++ rest) := by
    simpa [Stk.get, encodeLiteral_eq] using hX
  let v1 : Reg := { v with go := true, u := true, b0 := true, half := true }
  let s1 : Stk := { s with X := l.2 :: (vcode l.1 ++ rest) }
  have hs1 : exec phase5Step ⟨{ v with u := true, go := true }, toFun (s.set .X (l.2 :: (vcode l.1 ++ rest)))⟩ = ⟨v1, toFun s1⟩ ∧
      cost phase5Step ⟨{ v with u := true, go := true }, toFun (s.set .X (l.2 :: (vcode l.1 ++ rest)))⟩ ≤ 4 := by
    refine ⟨?_, ?_⟩
    · simp only [phase5Step, exec, hh, Bool.not_false, ite_true]
      refine St_eq _ _ _ _ (by cases v; rfl) ?_
      apply Stk.ext_get <;> simp [s1, set_inp, set_out]
      intro a; cases a <;> simp [Stk.get, Stk.set]
    · simp [phase5Step, cost, hh]
  let v1a : Reg := { v1 with u := l.2, go := true, half := false, pol := l.2, inLit := true }
  let s1a : Stk := s1.set .X (vcode l.1 ++ rest)
  have hs2_ex : ∃ (p2 : Bool),
      let v2 : Reg := nrm { v1a with inClause := true, par := p2 }
      let s2 : Stk := { s with X := vcode l.1 ++ rest, Uocc := List.replicate u' true, OutRev := (preBans.flatMap (encBan w)).reverse ++ s.OutRev }
      exec phase5Step ⟨{ v1 with u := l.2, go := true }, toFun s1a⟩ = ⟨v2, toFun s2⟩ ∧
        cost phase5Step ⟨{ v1 with u := l.2, go := true }, toFun s1a⟩ ≤
          5 * ((w + 1) * (8 * n + 20) + 14 * n + 20) + 15 := by
    have hv1h : v1.half = true := rfl
    have hv1i : v1.inLit = false := hil
    have hv1b : v1.b0 = true := rfl
    have hv1c : v1.inClause = inC := hic
    cases inC
    · obtain ⟨p2, r2a⟩ := emit0Stk_spec .Uocc (by decide) (by decide) (by decide) w u 2 v1a s1a
        (by simp [s1a, s1, Stk.set, hW]) (by simp [s1a, s1, Stk.set, hWb])
        (by simp [s1a, s1, Stk.set, hQ]) (by simp [s1a, s1, Stk.set, hQb])
        (by simp [s1a, s1, Stk.set, hTmp]) (by simp [s1a, s1, Stk.get, Stk.set, hU])
      have hreq : ({ go := true, u := l.2, b0 := true, half := false, inLit := true, inClause := false, pol := l.2, ws := v1.ws, hasEmpty := v1.hasEmpty, expectData := v1.expectData, eqFlag := v1.eqFlag, found := v1.found, par := v1.par } : Reg) = v1a := by
        cases v; simp_all [v1a, v1]
      refine ⟨p2, ?_, ?_⟩
      · simp only [phase5Step, exec, hv1h, hv1i, hv1b, hv1c, Bool.not_true, Bool.not_false,
          Bool.false_eq_true, ite_false, ite_true]
        rw [hreq, r2a.1]
        refine St_eq _ _ _ _ (by cases v; simp [v1a, v1, nrm]) ?_
        apply Stk.ext_get <;> simp [s1a, s1, set_inp, set_out]
        intro a; cases a <;> simp [Stk.get, Stk.set, hU, u', preBans]
      · simp only [phase5Step, exec, cost, hv1h, hv1i, hv1b, hv1c, Bool.not_true, Bool.not_false,
          Bool.false_eq_true, ite_false, ite_true]
        rw [hreq]
        have h2 := r2a.2
        have hmul : (w + 1) * (4 * u + 16) ≤ (w + 1) * (8 * n + 20) :=
          Nat.mul_le_mul_left (w + 1) (by simp at hun; omega)
        simp at hun
        omega
    · obtain ⟨p2, r2a⟩ := emitTransAll_spec w u v1a s1a
        (by simp [s1a, s1, Stk.set, hW]) (by simp [s1a, s1, Stk.set, hWb])
        (by simp [s1a, s1, Stk.set, hQ]) (by simp [s1a, s1, Stk.set, hQb])
        (by simp [s1a, s1, Stk.set, hTmp]) (by simp [s1a, s1, Stk.set, hU])
      have hreq : ({ go := true, u := l.2, b0 := true, half := false, inLit := true, inClause := true, pol := l.2, ws := v1.ws, hasEmpty := v1.hasEmpty, expectData := v1.expectData, eqFlag := v1.eqFlag, found := v1.found, par := v1.par } : Reg) = v1a := by
        cases v; simp_all [v1a, v1]
      refine ⟨p2, ?_, ?_⟩
      · simp only [phase5Step, exec, hv1h, hv1i, hv1b, hv1c, Bool.not_true, Bool.not_false,
          Bool.false_eq_true, ite_false, ite_true]
        rw [hreq, r2a.1, exec_wpush]
        refine St_eq _ _ _ _ (by simp only [v1a, v1, nrm, hic]) ?_
        apply Stk.ext_get <;> simp [s1a, s1, set_inp, set_out]
        intro a; cases a <;> simp [Stk.get, Stk.set, hU, u', preBans, List.replicate_succ, tt]
      · simp only [phase5Step, exec, cost, hv1h, hv1i, hv1b, hv1c, Bool.not_true, Bool.not_false,
          Bool.false_eq_true, ite_false, ite_true]
        rw [hreq]
        have hcw : ∀ st, cost (wpush .Uocc tt) st = 1 := fun _ => rfl
        rw [hcw]
        have h2 := r2a.2
        have hmul : (w + 1) * (8 * u + 20) ≤ (w + 1) * (8 * n + 20) :=
          Nat.mul_le_mul_left (w + 1) (by simp at hun; omega)
        simp at hun
        omega
  obtain ⟨p2, hs2_e, hs2_c⟩ := hs2_ex
  let v2 : Reg := nrm { v1a with inClause := true, par := p2 }
  let s2 : Stk := { s with X := vcode l.1 ++ rest, Uocc := List.replicate u' true, OutRev := (preBans.flatMap (encBan w)).reverse ++ s.OutRev }
  obtain ⟨u3, b03, hd_exec, hd_cost⟩ := phase5_digits l.1.bits (false :: true :: rest) v2 s2 rfl rfl
    (by simp [s2, vcode, List.append_assoc])
  let v3 : Reg := { v2 with go := true, u := u3, b0 := b03, half := false, inLit := true }
  let s3 : Stk := { s2 with X := false :: true :: rest, Drev := l.1.bits.reverse ++ s2.Drev }
  let v4 : Reg := { v3 with go := true, u := false, b0 := false, half := true }
  let s4 : Stk := { s3 with X := true :: rest }
  have hs4 : exec phase5Step ⟨{ v3 with u := false, go := true }, toFun (s3.set .X (true :: rest))⟩ = ⟨v4, toFun s4⟩ ∧
      cost phase5Step ⟨{ v3 with u := false, go := true }, toFun (s3.set .X (true :: rest))⟩ ≤ 4 := by
    refine ⟨?_, ?_⟩
    · simp only [phase5Step, exec, v3, Bool.not_false, ite_true]
      refine St_eq _ _ _ _ (by cases v; rfl) ?_
      apply Stk.ext_get <;> simp [s4, s3, set_inp, set_out]
      intro a; cases a <;> simp [Stk.get, Stk.set]
    · simp [phase5Step, cost, v3]
  let v4' : Reg := { v4 with u := true, go := true, half := false, inLit := false }
  let s4' : Stk := s4.set .X rest
  obtain ⟨b05, exp5, eq5, fnd5, par5, hlk⟩ := emitLitLookup_spec ord l w u' n z hlmem hVn hun hsz
    v4' s4' rfl (by simp [s4', s4, s3, s2, Stk.set, hD]) (by simp [s4', s4, s3, s2, Stk.set, hCV])
    (by simp [s4', s4, s3, s2, Stk.set, hCVb]) (by simp [s4', s4, s3, s2, Stk.set, hSV])
    (by simp [s4', s4, s3, s2, Stk.set, hSVb]) (by simp [s4', s4, s3, s2, Stk.set, hVi])
    (by simp [s4', s4, s3, s2, Stk.set, hW]) (by simp [s4', s4, s3, s2, Stk.set, hWb])
    (by simp [s4', s4, s3, s2, Stk.set, hQ]) (by simp [s4', s4, s3, s2, Stk.set, hQb])
    (by simp [s4', s4, s3, s2, Stk.set, hTmp]) (by simp [s4', s4, s3, s2, Stk.set])
  let v5 : Reg := nrm { v4' with b0 := b05, expectData := exp5, eqFlag := eq5, found := fnd5, par := par5 }
  let s5 : Stk := { s4' with Drev := [], OutRev := ((litBans ord u' l).flatMap (encBan w)).reverse ++ s4'.OutRev }
  have hs5 : exec phase5Step ⟨{ v4 with u := true, go := true }, toFun s4'⟩ = ⟨v5, toFun s5⟩ ∧
      cost phase5Step ⟨{ v4 with u := true, go := true }, toFun s4'⟩ ≤
        2 * ((w + 1) * (8 * n + 16) + 14 * n + 16) + 25 * z + 4 * l.1.bits.length + 28 := by
    have hv4h : v4.half = true := rfl
    have hv4i : v4.inLit = true := rfl
    have hv4b : v4.b0 = false := rfl
    have hv4'_eq : ({ ({ ({ v4 with u := true, go := true }) with half := false }) with inLit := false } : Reg) = v4' := rfl
    refine ⟨?_, ?_⟩
    · simp only [phase5Step, exec, hv4h, hv4i, hv4b, Bool.not_true, Bool.false_eq_true, ite_false]
      rw [hv4'_eq]
      exact hlk.1
    · simp only [phase5Step, exec, cost, hv4h, hv4i, hv4b, Bool.not_true, Bool.false_eq_true, ite_false]
      rw [hv4'_eq]
      have h2 := hlk.2
      omega
  have hv5_eq : v5 = nrm { v with b0 := b05, half := false, inLit := false, inClause := true, pol := l.2, expectData := exp5, eqFlag := eq5, found := fnd5, par := par5 } := by
    cases v; rfl
  have hs5_eq : s5 = { s with X := rest, Uocc := List.replicate u' true, OutRev := ((preBans ++ litBans ord u' l).flatMap (encBan w)).reverse ++ s.OutRev } := by
    apply Stk.ext_get <;> simp [s5, s4', s4, s3, s2, set_inp, set_out]
    intro a; cases a <;> simp [Stk.get, Stk.set, hD]
  have hX2 : s1.get .X = l.2 :: (vcode l.1 ++ rest) := rfl
  have hX3 : s3.get .X = false :: true :: rest := rfl
  have hX4 : s4.get .X = true :: rest := rfl
  refine ⟨b05, exp5, eq5, fnd5, par5, ?_, ?_⟩
  · rw [exec_phase5Loop_cons _ _ true _ hX1, hs1.1, exec_phase5Loop_cons _ _ l.2 _ hX2, hs2_e,
      hd_exec, exec_phase5Loop_cons _ _ false _ hX3, hs4.1, exec_phase5Loop_cons _ _ true _ hX4,
      hs5.1, hv5_eq, hs5_eq]
  · rw [cost_phase5Loop_cons _ _ true _ hX1, hs1.1, cost_phase5Loop_cons _ _ l.2 _ hX2, hs2_e]
    have hstep45 : cost phase5Loop ⟨v3, toFun s3⟩ ≤
        cost phase5Loop ⟨v5, toFun s5⟩ +
          (2 * ((w + 1) * (8 * n + 16) + 14 * n + 16) + 25 * z + 4 * l.1.bits.length + 34) := by
      rw [cost_phase5Loop_cons _ _ false _ hX3, hs4.1, cost_phase5Loop_cons _ _ true _ hX4, hs5.1]
      have h4 := hs4.2; have h5 := hs5.2
      dsimp only [s4'] at h5
      omega
    rw [hv5_eq, hs5_eq] at hstep45
    have h1 := hs1.2
    dsimp only [v2, s2, v3, s3] at hd_cost hstep45
    dsimp only [s1a] at hs2_c
    have hmul : 5 * ((w + 1) * (8 * n + 20)) + 2 * ((w + 1) * (8 * n + 16)) ≤ 60 * (w + 1) * (n + 3) := by
      have : 5 * ((w + 1) * (8 * n + 20)) + 2 * ((w + 1) * (8 * n + 16)) = (w + 1) * (56 * n + 132) := by ring
      have : 60 * (w + 1) * (n + 3) = (w + 1) * (60 * n + 180) := by ring
      nlinarith
    have h5a : 5 * ((w + 1) * (8 * n + 20) + 14 * n + 20) = 5 * ((w + 1) * (8 * n + 20)) + 70 * n + 100 := by ring
    have h2a : 2 * ((w + 1) * (8 * n + 16) + 14 * n + 16) = 2 * ((w + 1) * (8 * n + 16)) + 28 * n + 32 := by ring
    omega

theorem phase5_endClause (rest : List Bool) (w u n : Nat) (inC : Bool) (hun : u ≤ n)
    (v : Reg) (s : Stk)
    (hh : v.half = false) (hil : v.inLit = false) (hic : v.inClause = inC)
    (hX : s.X = false :: false :: rest)
    (hW : s.Wstk = List.replicate w true) (hWb : s.Wb = [])
    (hQ : s.Q = []) (hQb : s.Qb = []) (hTmp : s.Tmp = [])
    (hU : s.Uocc = List.replicate u true) :
    let u' := if inC then u + 1 else u
    let endBans : List Ban := if inC then [((0, 0), (u, 0))] else []
    ∃ par' : Bool,
      let v' : Reg := nrm { v with b0 := false, half := false, inLit := false, inClause := false, par := par' }
      let s' : Stk := { s with X := rest, Uocc := List.replicate u' true, OutRev := (endBans.flatMap (encBan w)).reverse ++ s.OutRev }
      exec phase5Loop ⟨v, toFun s⟩ = exec phase5Loop ⟨v', toFun s'⟩ ∧
        cost phase5Loop ⟨v, toFun s⟩ ≤ cost phase5Loop ⟨v', toFun s'⟩ +
          ((w + 1) * (4 * n + 16) + 7 * n + 30) := by
  intro u' endBans
  have hX1 : s.get .X = false :: false :: rest := hX
  let v1 : Reg := { v with go := true, u := false, b0 := false, half := true }
  let s1 : Stk := { s with X := false :: rest }
  have hs1 : exec phase5Step ⟨{ v with u := false, go := true }, toFun (s.set .X (false :: rest))⟩ = ⟨v1, toFun s1⟩ ∧
      cost phase5Step ⟨{ v with u := false, go := true }, toFun (s.set .X (false :: rest))⟩ ≤ 4 := by
    refine ⟨?_, ?_⟩
    · simp only [phase5Step, exec, hh, Bool.not_false, ite_true]
      refine St_eq _ _ _ _ (by cases v; rfl) ?_
      apply Stk.ext_get <;> simp [s1, set_inp, set_out]
      intro a; cases a <;> simp [Stk.get, Stk.set]
    · simp [phase5Step, cost, hh]
  let s1a : Stk := s1.set .X rest
  have hX2 : s1.get .X = false :: rest := rfl
  cases inC
  · let v2 : Reg := { v1 with u := false, go := true, half := false }
    have hs2 : exec phase5Step ⟨{ v1 with u := false, go := true }, toFun s1a⟩ = ⟨v2, toFun s1a⟩ ∧
        cost phase5Step ⟨{ v1 with u := false, go := true }, toFun s1a⟩ ≤ 8 := by
      refine ⟨?_, ?_⟩
      · simp only [phase5Step, exec, v1, hil, hic, Bool.not_true, Bool.not_false, Bool.false_eq_true, ite_false, ite_true]
        refine St_eq _ _ _ _ (by cases v; simp_all [v2, v1]) rfl
      · simp [phase5Step, exec, cost, v1, hil, hic]
    let v2' : Reg := nrm { v with b0 := false, half := false, inLit := false, inClause := false, par := v.par }
    have hs1a_eq : s1a = { s with X := rest, Uocc := List.replicate u' true, OutRev := (endBans.flatMap (encBan w)).reverse ++ s.OutRev } := by
      apply Stk.ext_get <;> simp [s1a, s1, set_inp, set_out]
      intro a; cases a <;> simp [Stk.get, Stk.set, hU, u', endBans]
    have hv2_eq : exec phase5Loop ⟨v2, toFun s1a⟩ = exec phase5Loop ⟨v2', toFun s1a⟩ ∧
        cost phase5Loop ⟨v2, toFun s1a⟩ = cost phase5Loop ⟨v2', toFun s1a⟩ := by
      have hsr : s1a.get .X = rest := by simp [s1a, Stk.get, Stk.set]
      cases rest with
      | nil =>
        rw [phase5Loop, exec_forPop_nil _ _ _ _ _ _ hsr, exec_forPop_nil _ _ _ _ _ _ hsr,
          cost_forPop_nil _ _ _ _ _ _ hsr, cost_forPop_nil _ _ _ _ _ _ hsr]
        exact ⟨St_eq _ _ _ _ (by cases v; simp_all [v2, v2', v1, nrm]) rfl, rfl⟩
      | cons x xs =>
        rw [exec_phase5Loop_cons _ _ x xs hsr, exec_phase5Loop_cons _ _ x xs hsr,
          cost_phase5Loop_cons _ _ x xs hsr, cost_phase5Loop_cons _ _ x xs hsr]
        have hv : ({ v2 with u := x, go := true } : Reg) = { v2' with u := x, go := true } := by
          cases v; simp_all [v2, v2', v1, nrm]
        rw [hv]; exact ⟨rfl, rfl⟩
    refine ⟨v.par, ?_, ?_⟩
    · rw [exec_phase5Loop_cons _ _ false (false :: rest) hX1, hs1.1,
        exec_phase5Loop_cons _ _ false rest hX2, hs2.1, hv2_eq.1, hs1a_eq]
    · rw [cost_phase5Loop_cons _ _ false (false :: rest) hX1, hs1.1,
        cost_phase5Loop_cons _ _ false rest hX2, hs2.1, hv2_eq.2, hs1a_eq]
      have h1 := hs1.2; have h2 := hs2.2
      dsimp only [v2', s1a] at h2 ⊢
      omega
  · let v1a : Reg := { v1 with u := false, go := true, half := false }
    obtain ⟨p2, r2a⟩ := emit0Stk_spec .Uocc (by decide) (by decide) (by decide) w u 0 v1a s1a
      (by simp [s1a, s1, Stk.set, hW]) (by simp [s1a, s1, Stk.set, hWb])
      (by simp [s1a, s1, Stk.set, hQ]) (by simp [s1a, s1, Stk.set, hQb])
      (by simp [s1a, s1, Stk.set, hTmp]) (by simp [s1a, s1, Stk.get, Stk.set, hU])
    let v2 : Reg := nrm { v with b0 := false, half := false, inLit := false, inClause := false, par := p2 }
    let s2 : Stk := { s with X := rest, Uocc := List.replicate u' true, OutRev := (endBans.flatMap (encBan w)).reverse ++ s.OutRev }
    have hs2 : exec phase5Step ⟨{ v1 with u := false, go := true }, toFun s1a⟩ = ⟨v2, toFun s2⟩ ∧
        cost phase5Step ⟨{ v1 with u := false, go := true }, toFun s1a⟩ ≤
          (w + 1) * (4 * n + 16) + 7 * n + 24 := by
      have hv1h : v1.half = true := rfl
      have hv1i : v1.inLit = false := hil
      have hv1b : v1.b0 = false := rfl
      have hv1c : v1.inClause = true := hic
      have hreq : ({ go := true, u := false, b0 := false, half := false, inLit := false, inClause := true, pol := v1.pol, ws := v1.ws, hasEmpty := v1.hasEmpty, expectData := v1.expectData, eqFlag := v1.eqFlag, found := v1.found, par := v1.par } : Reg) = v1a := by
        cases v; simp_all [v1a, v1]
      refine ⟨?_, ?_⟩
      · simp only [phase5Step, exec, hv1h, hv1i, hv1b, hv1c, Bool.not_true, Bool.not_false,
          Bool.false_eq_true, ite_false, ite_true]
        rw [hreq, r2a.1, exec_wpush]
        refine St_eq _ _ _ _ (by cases v; simp [v2, v1a, v1, nrm, hil]) ?_
        apply Stk.ext_get <;> simp [s2, s1a, s1, set_inp, set_out]
        intro a; cases a <;> simp [Stk.get, Stk.set, hU, u', endBans, List.replicate_succ, tt]
      · simp only [phase5Step, exec, cost, hv1h, hv1i, hv1b, hv1c, Bool.not_true, Bool.not_false,
          Bool.false_eq_true, ite_false, ite_true]
        rw [hreq]
        have hcw : ∀ st, cost (wpush .Uocc tt) st = 1 := fun _ => rfl
        rw [hcw]
        have h2 := r2a.2
        have hmul : (w + 1) * (4 * u + 16) ≤ (w + 1) * (4 * n + 16) :=
          Nat.mul_le_mul_left (w + 1) (by omega)
        omega
    refine ⟨p2, ?_, ?_⟩
    · rw [exec_phase5Loop_cons _ _ false (false :: rest) hX1, hs1.1,
        exec_phase5Loop_cons _ _ false rest hX2, hs2.1]
    · rw [cost_phase5Loop_cons _ _ false (false :: rest) hX1, hs1.1,
        cost_phase5Loop_cons _ _ false rest hX2, hs2.1]
      have h1 := hs1.2; have h2 := hs2.2
      dsimp only [v2, s2, s1a] at h2 ⊢
      omega

def tailBansFn (ord : List Nat) (u : Nat) : Clause → List Ban
  | [] => [((0, 0), (u, 0))]
  | l' :: rest' => transBans u ++ litsBans ord (u + 1) (l' :: rest')

theorem phase5_tail (ord : List Nat) (w n z : Nat) (hVn : 2 + ord.length ≤ n)
    (hsz : (encodeVars (ord.map Nat.bits)).length ≤ z) :
    ∀ (restC : Clause) (_ : Literal) (u : Nat) (rest : List Bool) (v : Reg) (s : Stk),
      (∀ l ∈ restC, l.1 ∈ ord) → u + restC.length < n →
      v.half = false → v.inLit = false → v.inClause = true →
      s.X = encodeClause restC ++ rest →
      s.Drev = [] → s.CurV = [] → s.CurVb = [] →
      s.SeenV = encodeVars (ord.map Nat.bits) → s.SeenVb = [] → s.Vidx = [] →
      s.Wstk = List.replicate w true → s.Wb = [] → s.Q = [] → s.Qb = [] → s.Tmp = [] →
      s.Uocc = List.replicate u true →
      ∃ (b0' pol' exp' eq' fnd' par' : Bool),
        let v' : Reg := nrm { v with b0 := b0', half := false, inLit := false, inClause := false, pol := pol', expectData := exp', eqFlag := eq', found := fnd', par := par' }
        let s' : Stk := { s with X := rest, Uocc := List.replicate (u + restC.length + 1) true, OutRev := ((tailBansFn ord u restC).flatMap (encBan w)).reverse ++ s.OutRev }
        exec phase5Loop ⟨v, toFun s⟩ = exec phase5Loop ⟨v', toFun s'⟩ ∧
          cost phase5Loop ⟨v, toFun s⟩ ≤ cost phase5Loop ⟨v', toFun s'⟩ +
            (restC.length * (60 * (w + 1) * (n + 3) + 120 * n + 25 * z + 180) +
              9 * (encodeClause restC).length + (w + 1) * (4 * n + 16) + 7 * n + 30) := by
  intro restC
  induction restC with
  | nil =>
    intro l0 u rest v s _ hun hh hil hic hX _ _ _ _ _ _ hW hWb hQ hQb hTmp hU
    obtain ⟨par', he, hc⟩ := phase5_endClause rest w u n true (by simp at hun; omega) v s
      hh hil hic (by simpa [encodeClause] using hX) hW hWb hQ hQb hTmp hU
    simp only [ite_true] at he hc
    refine ⟨false, v.pol, v.expectData, v.eqFlag, v.found, par', ?_, ?_⟩
    · simpa [tailBansFn] using he
    · have hcl : (encodeClause []).length = 2 := rfl
      have hmul0 : ([] : Clause).length * (60 * (w + 1) * (n + 3) + 120 * n + 25 * z + 180) = 0 := by simp
      have hceq : cost phase5Loop ⟨nrm { v with b0 := false, half := false, inLit := false, inClause := false, par := par' },
          toFun { s with X := rest, Uocc := List.replicate (u + 1) true, OutRev := ([((0, 0), (u, 0))].flatMap (encBan w)).reverse ++ s.OutRev }⟩ =
          cost phase5Loop ⟨nrm { v with b0 := false, half := false, inLit := false, inClause := false, pol := v.pol, expectData := v.expectData, eqFlag := v.eqFlag, found := v.found, par := par' },
            toFun { s with X := rest, Uocc := List.replicate (u + ([] : Clause).length + 1) true, OutRev := ((tailBansFn ord u []).flatMap (encBan w)).reverse ++ s.OutRev }⟩ := rfl
      rw [hceq] at hc
      omega
  | cons l' rest' ih =>
    intro l0 u rest v s hmem hun hh hil hic hX hD hCV hCVb hSV hSVb hVi hW hWb hQ hQb hTmp hU
    have hX' : s.X = encodeLiteral l' ++ (encodeClause rest' ++ rest) := by
      simpa [encodeClause, List.append_assoc] using hX
    obtain ⟨b01, exp1, eq1, fnd1, par1, hl_e, hl_c⟩ := phase5_lit ord l' (encodeClause rest' ++ rest)
      w u n z true (hmem l' (by simp)) hVn (by simp only [List.length_cons] at hun; simp only [ite_true]; omega) hsz v s hh hil hic hX'
      hD hCV hCVb hSV hSVb hVi hW hWb hQ hQb hTmp hU
    simp only [ite_true] at hl_e hl_c
    let v1 : Reg := nrm { v with b0 := b01, half := false, inLit := false, inClause := true, pol := l'.2, expectData := exp1, eqFlag := eq1, found := fnd1, par := par1 }
    let s1 : Stk := { s with X := encodeClause rest' ++ rest, Uocc := List.replicate (u + 1) true, OutRev := ((transBans u ++ litBans ord (u + 1) l').flatMap (encBan w)).reverse ++ s.OutRev }
    obtain ⟨b02, pol2, exp2, eq2, fnd2, par2, ht_e, ht_c⟩ := ih l' (u + 1) rest v1 s1
      (fun x hx => hmem x (List.mem_cons_of_mem _ hx)) (by simp at hun ⊢; omega)
      rfl rfl rfl rfl hD hCV hCVb hSV hSVb hVi hW hWb hQ hQb hTmp rfl
    refine ⟨b02, pol2, exp2, eq2, fnd2, par2, ?_, ?_⟩
    · rw [hl_e, ht_e]
      congr 1
      refine St_eq _ _ _ _ (by cases v; simp [v1, nrm]) ?_
      apply Stk.ext_get <;> (try rfl)
      intro a
      cases a <;> simp only [s1, Stk.get]
      all_goals
        first
        | (congr 1; simp only [List.length_cons]; omega)
        | (cases rest' <;> simp [tailBansFn, litsBans, List.append_assoc])
    · have hceq : cost phase5Loop ⟨nrm { v1 with b0 := b02, half := false, inLit := false, inClause := false, pol := pol2, expectData := exp2, eqFlag := eq2, found := fnd2, par := par2 },
          toFun { s1 with X := rest, Uocc := List.replicate (u + 1 + rest'.length + 1) true, OutRev := ((tailBansFn ord (u + 1) rest').flatMap (encBan w)).reverse ++ s1.OutRev }⟩ =
          cost phase5Loop ⟨nrm { v with b0 := b02, half := false, inLit := false, inClause := false, pol := pol2, expectData := exp2, eqFlag := eq2, found := fnd2, par := par2 },
            toFun { s with X := rest, Uocc := List.replicate (u + (l' :: rest').length + 1) true, OutRev := ((tailBansFn ord u (l' :: rest')).flatMap (encBan w)).reverse ++ s.OutRev }⟩ := by
        congr 1
        refine St_eq _ _ _ _ (by cases v; simp [v1, nrm]) ?_
        apply Stk.ext_get <;> (try rfl)
        intro a
        cases a <;> simp only [s1, Stk.get]
        all_goals
          first
          | (congr 1; simp only [List.length_cons]; omega)
          | (cases rest' <;> simp [tailBansFn, litsBans, List.append_assoc])
      rw [hceq] at ht_c
      dsimp only [v1, s1] at ht_c hl_c
      have hlen_c : (encodeClause (l' :: rest')).length = (encodeLiteral l').length + (encodeClause rest').length := by
        simp [encodeClause]
      have hlen_l : 2 * l'.1.bits.length + 4 = (encodeLiteral l').length := (encodeLiteral_length l').symm
      have hmul : (l' :: rest').length * (60 * (w + 1) * (n + 3) + 120 * n + 25 * z + 180) =
          rest'.length * (60 * (w + 1) * (n + 3) + 120 * n + 25 * z + 180) +
          (60 * (w + 1) * (n + 3) + 120 * n + 25 * z + 180) := by
        simp only [List.length_cons]; ring
      omega

theorem phase5_clause (ord : List Nat) (w n z : Nat) (hVn : 2 + ord.length ≤ n)
    (hsz : (encodeVars (ord.map Nat.bits)).length ≤ z)
    (c : Clause) (off : Nat) (rest : List Bool) (v : Reg) (s : Stk)
    (hmem : ∀ l ∈ c, l.1 ∈ ord) (hlen : 2 + ord.length + off + c.length ≤ n)
    (hh : v.half = false) (hil : v.inLit = false) (hic : v.inClause = false)
    (hX : s.X = encodeClause c ++ rest)
    (hD : s.Drev = []) (hCV : s.CurV = []) (hCVb : s.CurVb = [])
    (hSV : s.SeenV = encodeVars (ord.map Nat.bits)) (hSVb : s.SeenVb = [])
    (hVi : s.Vidx = []) (hW : s.Wstk = List.replicate w true) (hWb : s.Wb = [])
    (hQ : s.Q = []) (hQb : s.Qb = []) (hTmp : s.Tmp = [])
    (hU : s.Uocc = List.replicate (2 + ord.length + off) true) :
    ∃ (b0' pol' exp' eq' fnd' par' : Bool),
      let v' : Reg := nrm { v with b0 := b0', half := false, inLit := false, inClause := false, pol := pol', expectData := exp', eqFlag := eq', found := fnd', par := par' }
      let s' : Stk := { s with X := rest, Uocc := List.replicate (2 + ord.length + (off + c.length)) true, OutRev := ((clauseBans ord ord.length off c).flatMap (encBan w)).reverse ++ s.OutRev }
      exec phase5Loop ⟨v, toFun s⟩ = exec phase5Loop ⟨v', toFun s'⟩ ∧
        cost phase5Loop ⟨v, toFun s⟩ ≤ cost phase5Loop ⟨v', toFun s'⟩ +
          (c.length * (60 * (w + 1) * (n + 3) + 120 * n + 25 * z + 180) +
            9 * (encodeClause c).length + (w + 1) * (4 * n + 16) + 7 * n + 30) := by
  cases c with
  | nil =>
    obtain ⟨par', he, hc⟩ := phase5_endClause rest w (2 + ord.length + off) n false (by omega) v s
      hh hil hic (by simpa [encodeClause] using hX) hW hWb hQ hQb hTmp hU
    simp only [Bool.false_eq_true, ite_false] at he hc
    refine ⟨false, v.pol, v.expectData, v.eqFlag, v.found, par', ?_, ?_⟩
    · simpa [clauseBans] using he
    · have hcl : (encodeClause []).length = 2 := rfl
      have hmul0 : ([] : Clause).length * (60 * (w + 1) * (n + 3) + 120 * n + 25 * z + 180) = 0 := by simp
      have hceq : cost phase5Loop ⟨nrm { v with b0 := false, half := false, inLit := false, inClause := false, par := par' },
          toFun { s with X := rest, Uocc := List.replicate (2 + ord.length + off) true, OutRev := (([] : List Ban).flatMap (encBan w)).reverse ++ s.OutRev }⟩ =
          cost phase5Loop ⟨nrm { v with b0 := false, half := false, inLit := false, inClause := false, pol := v.pol, expectData := v.expectData, eqFlag := v.eqFlag, found := v.found, par := par' },
            toFun { s with X := rest, Uocc := List.replicate (2 + ord.length + (off + ([] : Clause).length)) true, OutRev := ((clauseBans ord ord.length off []).flatMap (encBan w)).reverse ++ s.OutRev }⟩ := rfl
      rw [hceq] at hc
      omega
  | cons l restC =>
    have hX' : s.X = encodeLiteral l ++ (encodeClause restC ++ rest) := by
      simpa [encodeClause, List.append_assoc] using hX
    obtain ⟨b01, exp1, eq1, fnd1, par1, hl_e, hl_c⟩ := phase5_lit ord l (encodeClause restC ++ rest)
      w (2 + ord.length + off) n z false (hmem l (by simp)) hVn (by simp only [List.length_cons] at hlen; simp only [Bool.false_eq_true, ite_false]; omega) hsz v s
      hh hil hic hX' hD hCV hCVb hSV hSVb hVi hW hWb hQ hQb hTmp hU
    simp only [Bool.false_eq_true, ite_false] at hl_e hl_c
    let v1 : Reg := nrm { v with b0 := b01, half := false, inLit := false, inClause := true, pol := l.2, expectData := exp1, eqFlag := eq1, found := fnd1, par := par1 }
    let s1 : Stk := { s with X := encodeClause restC ++ rest, Uocc := List.replicate (2 + ord.length + off) true, OutRev := (([((0, 0), (2 + ord.length + off, 2))] ++ litBans ord (2 + ord.length + off) l).flatMap (encBan w)).reverse ++ s.OutRev }
    obtain ⟨b02, pol2, exp2, eq2, fnd2, par2, ht_e, ht_c⟩ := phase5_tail ord w n z hVn hsz restC l
      (2 + ord.length + off) rest v1 s1 (fun x hx => hmem x (List.mem_cons_of_mem _ hx))
      (by simp at hlen; omega) rfl rfl rfl rfl hD hCV hCVb hSV hSVb hVi hW hWb hQ hQb hTmp rfl
    refine ⟨b02, pol2, exp2, eq2, fnd2, par2, ?_, ?_⟩
    · rw [hl_e, ht_e]
      congr 1
      refine St_eq _ _ _ _ (by cases v; simp [v1, nrm]) ?_
      apply Stk.ext_get <;> (try rfl)
      intro a
      cases a <;> simp only [s1, Stk.get]
      all_goals
        first
        | (congr 1; simp only [List.length_cons]; omega)
        | (cases restC <;> simp [tailBansFn, clauseBans, litsBans, List.append_assoc])
    · have hceq : cost phase5Loop ⟨nrm { v1 with b0 := b02, half := false, inLit := false, inClause := false, pol := pol2, expectData := exp2, eqFlag := eq2, found := fnd2, par := par2 },
          toFun { s1 with X := rest, Uocc := List.replicate (2 + ord.length + off + restC.length + 1) true, OutRev := ((tailBansFn ord (2 + ord.length + off) restC).flatMap (encBan w)).reverse ++ s1.OutRev }⟩ =
          cost phase5Loop ⟨nrm { v with b0 := b02, half := false, inLit := false, inClause := false, pol := pol2, expectData := exp2, eqFlag := eq2, found := fnd2, par := par2 },
            toFun { s with X := rest, Uocc := List.replicate (2 + ord.length + (off + (l :: restC).length)) true, OutRev := ((clauseBans ord ord.length off (l :: restC)).flatMap (encBan w)).reverse ++ s.OutRev }⟩ := by
        congr 1
        refine St_eq _ _ _ _ (by cases v; simp [v1, nrm]) ?_
        apply Stk.ext_get <;> (try rfl)
        intro a
        cases a <;> simp only [s1, Stk.get]
        all_goals
          first
          | (congr 1; simp only [List.length_cons]; omega)
          | (cases restC <;> simp [tailBansFn, clauseBans, litsBans, List.append_assoc])
      rw [hceq] at ht_c
      dsimp only [v1, s1] at ht_c hl_c
      have hlen_c : (encodeClause (l :: restC)).length = (encodeLiteral l).length + (encodeClause restC).length := by
        simp [encodeClause]
      have hlen_l : 2 * l.1.bits.length + 4 = (encodeLiteral l).length := (encodeLiteral_length l).symm
      have hmul : (l :: restC).length * (60 * (w + 1) * (n + 3) + 120 * n + 25 * z + 180) =
          restC.length * (60 * (w + 1) * (n + 3) + 120 * n + 25 * z + 180) +
          (60 * (w + 1) * (n + 3) + 120 * n + 25 * z + 180) := by
        simp only [List.length_cons]; ring
      omega

theorem phase5_cnf (ord : List Nat) (w n z : Nat) (hVn : 2 + ord.length ≤ n)
    (hsz : (encodeVars (ord.map Nat.bits)).length ≤ z) :
    ∀ (cs : CNF) (off : Nat) (rest : List Bool) (v : Reg) (s : Stk),
      (∀ c ∈ cs, ∀ l ∈ c, l.1 ∈ ord) → 2 + ord.length + off + cs.flatten.length ≤ n →
      v.half = false → v.inLit = false → v.inClause = false →
      s.X = encodeCNF cs ++ rest →
      s.Drev = [] → s.CurV = [] → s.CurVb = [] →
      s.SeenV = encodeVars (ord.map Nat.bits) → s.SeenVb = [] → s.Vidx = [] →
      s.Wstk = List.replicate w true → s.Wb = [] → s.Q = [] → s.Qb = [] → s.Tmp = [] →
      s.Uocc = List.replicate (2 + ord.length + off) true →
      ∃ (b0' pol' exp' eq' fnd' par' : Bool),
        let v' : Reg := nrm { v with b0 := b0', half := false, inLit := false, inClause := false, pol := pol', expectData := exp', eqFlag := eq', found := fnd', par := par' }
        let s' : Stk := { s with X := rest, Uocc := List.replicate (2 + ord.length + (off + cs.flatten.length)) true, OutRev := ((clausesBans ord ord.length off cs).flatMap (encBan w)).reverse ++ s.OutRev }
        exec phase5Loop ⟨v, toFun s⟩ = exec phase5Loop ⟨v', toFun s'⟩ ∧
          cost phase5Loop ⟨v, toFun s⟩ ≤ cost phase5Loop ⟨v', toFun s'⟩ +
            (cs.flatten.length * (60 * (w + 1) * (n + 3) + 120 * n + 25 * z + 180) +
              9 * (encodeCNF cs).length + cs.length * ((w + 1) * (4 * n + 16) + 7 * n + 30)) := by
  intro cs
  induction cs with
  | nil =>
    intro off rest v s _ _ hh hil hic hX _ _ _ _ _ _ _ _ _ _ _ hU
    refine ⟨v.b0, v.pol, v.expectData, v.eqFlag, v.found, v.par, ?_, ?_⟩
    · cases rest with
      | nil =>
        have hXg : s.get .X = [] := hX
        rw [phase5Loop, exec_forPop_nil _ _ _ _ _ _ hXg, exec_forPop_nil _ _ _ _ _ _ rfl]
        refine St_eq _ _ _ _ (by cases v; simp_all [nrm]) ?_
        apply Stk.ext_get <;> (try rfl)
        intro a; cases a <;> simp [Stk.get, hX, hU, clausesBans, encodeCNF]
      | cons x xs =>
        have hXg : s.get .X = x :: xs := hX
        rw [phase5Loop, exec_forPop_cons _ _ _ _ _ _ x xs hXg noTouch_phase5Step,
          exec_forPop_cons _ _ _ _ _ _ x xs rfl noTouch_phase5Step]
        congr 2
        refine St_eq _ _ _ _ (by cases v; simp_all [nrm]) ?_
        apply Stk.ext_get <;> simp [set_inp, set_out]
        intro a; cases a <;> simp [Stk.get, Stk.set, hU, clausesBans]
    · cases rest with
      | nil =>
        have hXg : s.get .X = [] := hX
        rw [phase5Loop, cost_forPop_nil _ _ _ _ _ _ hXg, cost_forPop_nil _ _ _ _ _ _ rfl]; omega
      | cons x xs =>
        have hXg : s.get .X = x :: xs := hX
        rw [phase5Loop, cost_forPop_cons _ _ _ _ _ _ x xs hXg noTouch_phase5Step,
          cost_forPop_cons _ _ _ _ _ _ x xs rfl noTouch_phase5Step]
        have heq : (⟨{ ({ v with u := x }) with go := true }, toFun (s.set .X xs)⟩ : St K Γ Reg) =
            ⟨{ ({ nrm { v with b0 := v.b0, half := false, inLit := false, inClause := false, pol := v.pol, expectData := v.expectData, eqFlag := v.eqFlag, found := v.found, par := v.par } with u := x }) with go := true },
              toFun (({ s with X := x :: xs, Uocc := List.replicate (2 + ord.length + (off + 0)) true, OutRev := ((clausesBans ord ord.length off []).flatMap (encBan w)).reverse ++ s.OutRev }).set .X xs)⟩ := by
          refine St_eq _ _ _ _ (by cases v; simp_all [nrm]) ?_
          apply Stk.ext_get <;> simp [set_inp, set_out]
          intro a; cases a <;> simp [Stk.get, Stk.set, hU, clausesBans]
        simp only [List.flatten_nil, List.length_nil, Nat.zero_mul, Nat.add_zero]
        rw [heq]; exact le_refl _
  | cons c cs ih =>
    intro off rest v s hmem hlen hh hil hic hX hD hCV hCVb hSV hSVb hVi hW hWb hQ hQb hTmp hU
    have hX' : s.X = encodeClause c ++ (encodeCNF cs ++ rest) := by
      simpa [encodeCNF, List.append_assoc] using hX
    simp only [List.flatten_cons, List.length_append] at hlen
    obtain ⟨b01, pol1, exp1, eq1, fnd1, par1, hc_e, hc_c⟩ := phase5_clause ord w n z hVn hsz c off
      (encodeCNF cs ++ rest) v s (hmem c (by simp)) (by omega) hh hil hic hX'
      hD hCV hCVb hSV hSVb hVi hW hWb hQ hQb hTmp hU
    let v1 : Reg := nrm { v with b0 := b01, half := false, inLit := false, inClause := false, pol := pol1, expectData := exp1, eqFlag := eq1, found := fnd1, par := par1 }
    let s1 : Stk := { s with X := encodeCNF cs ++ rest, Uocc := List.replicate (2 + ord.length + (off + c.length)) true, OutRev := ((clauseBans ord ord.length off c).flatMap (encBan w)).reverse ++ s.OutRev }
    obtain ⟨b02, pol2, exp2, eq2, fnd2, par2, hf_e, hf_c⟩ := ih (off + c.length) rest v1 s1
      (fun c' hc' => hmem c' (List.mem_cons_of_mem _ hc')) (by omega) rfl rfl rfl rfl
      hD hCV hCVb hSV hSVb hVi hW hWb hQ hQb hTmp rfl
    refine ⟨b02, pol2, exp2, eq2, fnd2, par2, ?_, ?_⟩
    · rw [hc_e, hf_e]
      congr 1
      refine St_eq _ _ _ _ (by cases v; simp [v1, nrm]) ?_
      apply Stk.ext_get <;> (try rfl)
      intro a
      cases a <;> simp only [s1, Stk.get]
      all_goals
        first
        | (congr 1; simp only [List.flatten_cons, List.length_append]; omega)
        | (simp only [clausesBans, List.flatMap_append, List.reverse_append, List.append_assoc])
    · have hceq : cost phase5Loop ⟨nrm { v1 with b0 := b02, half := false, inLit := false, inClause := false, pol := pol2, expectData := exp2, eqFlag := eq2, found := fnd2, par := par2 },
          toFun { s1 with X := rest, Uocc := List.replicate (2 + ord.length + (off + c.length + cs.flatten.length)) true, OutRev := ((clausesBans ord ord.length (off + c.length) cs).flatMap (encBan w)).reverse ++ s1.OutRev }⟩ =
          cost phase5Loop ⟨nrm { v with b0 := b02, half := false, inLit := false, inClause := false, pol := pol2, expectData := exp2, eqFlag := eq2, found := fnd2, par := par2 },
            toFun { s with X := rest, Uocc := List.replicate (2 + ord.length + (off + (c :: cs).flatten.length)) true, OutRev := ((clausesBans ord ord.length off (c :: cs)).flatMap (encBan w)).reverse ++ s.OutRev }⟩ := by
        congr 1
        refine St_eq _ _ _ _ (by cases v; simp [v1, nrm]) ?_
        apply Stk.ext_get <;> (try rfl)
        intro a
        cases a <;> simp only [s1, Stk.get]
        all_goals
          first
          | (congr 1; simp only [List.flatten_cons, List.length_append]; omega)
          | (simp only [clausesBans, List.flatMap_append, List.reverse_append, List.append_assoc])
      rw [hceq] at hf_c
      dsimp only [v1, s1] at hf_c hc_c
      have hlen_f : (encodeCNF (c :: cs)).length = (encodeClause c).length + (encodeCNF cs).length := by
        simp [encodeCNF]
      have hmul1 : (c :: cs).flatten.length * (60 * (w + 1) * (n + 3) + 120 * n + 25 * z + 180) =
          c.length * (60 * (w + 1) * (n + 3) + 120 * n + 25 * z + 180) +
          cs.flatten.length * (60 * (w + 1) * (n + 3) + 120 * n + 25 * z + 180) := by
        simp only [List.flatten_cons, List.length_append]; ring
      have hmul2 : (c :: cs).length * ((w + 1) * (4 * n + 16) + 7 * n + 30) =
          cs.length * ((w + 1) * (4 * n + 16) + 7 * n + 30) +
          ((w + 1) * (4 * n + 16) + 7 * n + 30) := by
        simp only [List.length_cons]; ring
      omega

theorem emitClausesP_spec (F : CNF) (v : Reg) (s : Stk)
    (hX : s.X = encodeCNF F)
    (hD : s.Drev = []) (hCV : s.CurV = []) (hCVb : s.CurVb = [])
    (hSV : s.SeenV = encodeVars (((F.flatten).map Prod.fst).eraseDups.map Nat.bits))
    (hSVb : s.SeenVb = []) (hVi : s.Vidx = [])
    (hW : s.Wstk = List.replicate (width (((F.flatten).map Prod.fst).eraseDups.length + F.flatten.length + 2)) true)
    (hWb : s.Wb = []) (hQ : s.Q = []) (hQb : s.Qb = []) (hTmp : s.Tmp = [])
    (hU : s.Uocc = List.replicate (2 + ((F.flatten).map Prod.fst).eraseDups.length) true) :
    let ord := ((F.flatten).map Prod.fst).eraseDups
    let n := ord.length + F.flatten.length + 2
    let w := width n
    let z := (encodeCNF F).length
    ∃ (b0' pol' exp' eq' fnd' par' : Bool),
      Run emitClausesP v s
        (nrm { v with b0 := b0', half := false, inLit := false, inClause := false, pol := pol', expectData := exp', eqFlag := eq', found := fnd', par := par' })
        { s with X := [], Uocc := List.replicate n true, OutRev := ((clausesBans ord ord.length 0 F).flatMap (encBan w)).reverse ++ s.OutRev }
        (F.flatten.length * (60 * (w + 1) * (n + 3) + 120 * n + 25 * z + 180) +
          9 * z + F.length * ((w + 1) * (4 * n + 16) + 7 * n + 30) + 2) := by
  intro ord n w z
  have r1 := Run.load (fun v : Reg => { v with half := false, inLit := false, inClause := false }) v s
  have hmem : ∀ c ∈ F, ∀ l ∈ c, l.1 ∈ ord := by
    intro c hc l hl
    rw [List.mem_eraseDups]
    exact List.mem_map.mpr ⟨l, List.mem_flatten.mpr ⟨c, hc, hl⟩, rfl⟩
  obtain ⟨b0', pol', exp', eq', fnd', par', he, hc⟩ := phase5_cnf ord w n z (by omega)
    (encodeVars_order_len F) F 0 [] { v with half := false, inLit := false, inClause := false } s
    hmem (by omega) rfl rfl rfl (by simp [hX]) hD hCV hCVb hSV hSVb hVi hW hWb hQ hQb hTmp hU
  let vEnd : Reg := nrm { v with b0 := b0', half := false, inLit := false, inClause := false, pol := pol', expectData := exp', eqFlag := eq', found := fnd', par := par' }
  let sEnd : Stk := { s with X := [], Uocc := List.replicate n true, OutRev := ((clausesBans ord ord.length 0 F).flatMap (encBan w)).reverse ++ s.OutRev }
  have hfn : 2 + ord.length + (0 + F.flatten.length) = n := by omega
  have hnil_e : exec phase5Loop ⟨nrm { ({ v with half := false, inLit := false, inClause := false }) with b0 := b0', half := false, inLit := false, inClause := false, pol := pol', expectData := exp', eqFlag := eq', found := fnd', par := par' },
      toFun { s with X := [], Uocc := List.replicate (2 + ord.length + (0 + F.flatten.length)) true, OutRev := ((clausesBans ord ord.length 0 F).flatMap (encBan w)).reverse ++ s.OutRev }⟩ =
      ⟨vEnd, toFun sEnd⟩ := by
    rw [phase5Loop, exec_forPop_nil _ _ _ _ _ _ rfl]
    refine St_eq _ _ _ _ (by cases v; simp [vEnd, nrm]) ?_
    apply Stk.ext_get <;> (try rfl)
    intro a; cases a <;> simp only [sEnd, Stk.get, hfn]
  have hnil_c : cost phase5Loop ⟨nrm { ({ v with half := false, inLit := false, inClause := false }) with b0 := b0', half := false, inLit := false, inClause := false, pol := pol', expectData := exp', eqFlag := eq', found := fnd', par := par' },
      toFun { s with X := [], Uocc := List.replicate (2 + ord.length + (0 + F.flatten.length)) true, OutRev := ((clausesBans ord ord.length 0 F).flatMap (encBan w)).reverse ++ s.OutRev }⟩ = 1 :=
    cost_forPop_nil _ _ _ _ _ _ rfl
  have r2 : Run phase5Loop { v with half := false, inLit := false, inClause := false } s vEnd sEnd
      (F.flatten.length * (60 * (w + 1) * (n + 3) + 120 * n + 25 * z + 180) +
        9 * z + F.length * ((w + 1) * (4 * n + 16) + 7 * n + 30) + 1) := by
    refine ⟨he.trans hnil_e, ?_⟩
    rw [hnil_c] at hc
    omega
  exact ⟨b0', pol', exp', eq', fnd', par', Run.conv (Run.seq r1 r2) rfl rfl (by omega)⟩

def sizeAll (s : Stk) : Nat :=
  s.X.length + s.Xrev.length + s.Mstk.length + s.Vstk.length + s.Nstk.length + s.Nb.length +
  s.Wstk.length + s.Wb.length + s.Q.length + s.Qb.length + s.Drev.length + s.CurV.length +
  s.CurVb.length + s.SeenV.length + s.SeenVb.length + s.Vidx.length + s.Uocc.length +
  s.Tmp.length + s.OutRev.length

theorem drainAll_spec (v : Reg) (s : Stk) :
    Run drainAll v s (nrm v) { emp with inp := s.inp, out := s.out } (2 * sizeAll s + 39) := by
  simp only [drainAll, List.foldr]
  refine Run.conv
    (Run.seq (Run.drain .X _ _)
    (Run.seq (Run.drain .Xrev _ _)
    (Run.seq (Run.drain .Mstk _ _)
    (Run.seq (Run.drain .Vstk _ _)
    (Run.seq (Run.drain .Nstk _ _)
    (Run.seq (Run.drain .Nb _ _)
    (Run.seq (Run.drain .Wstk _ _)
    (Run.seq (Run.drain .Wb _ _)
    (Run.seq (Run.drain .Q _ _)
    (Run.seq (Run.drain .Qb _ _)
    (Run.seq (Run.drain .Drev _ _)
    (Run.seq (Run.drain .CurV _ _)
    (Run.seq (Run.drain .CurVb _ _)
    (Run.seq (Run.drain .SeenV _ _)
    (Run.seq (Run.drain .SeenVb _ _)
    (Run.seq (Run.drain .Vidx _ _)
    (Run.seq (Run.drain .Uocc _ _)
    (Run.seq (Run.drain .Tmp _ _)
    (Run.seq (Run.drain .OutRev _ _)
    (Run.load id _ _)))))))))))))))))))) ?_ ?_ ?_
  · cases v; simp [nrm]
  · simp only [Stk.set, emp]
  · simp only [Stk.set, Stk.get]
    unfold sizeAll
    omega

theorem encBan_length (w : Nat) (e : Ban) : (encBan w e).length = 2 * w + 4 := by
  simp [encBan, bits]
  omega

theorem enc_length (n : Nat) (B : List Ban) :
    (enc n B).length = n + 1 + B.length * (2 * width n + 4) := by
  unfold enc header
  simp only [List.length_append, List.length_replicate, List.length_cons, List.length_nil]
  congr 1
  induction B with
  | nil => simp
  | cons e B ih =>
    simp only [List.flatMap_cons, List.length_append, encBan_length, List.length_cons, ih]
    ring

open Classical in
noncomputable def specFn (x : List Bool) : List Bool :=
  if h : ∃ F : CNF, encodeCNF F = x then
    let F := Classical.choose h
    let ord := ((F.flatten).map Prod.fst).eraseDups
    enc (ord.length + F.flatten.length + 2) (makeB F)
  else []

theorem specFn_encodeCNF (F : CNF) :
    let ord := ((F.flatten).map Prod.fst).eraseDups
    specFn (encodeCNF F) = enc (ord.length + F.flatten.length + 2) (makeB F) := by
  unfold specFn
  have hex : ∃ F' : CNF, encodeCNF F' = encodeCNF F := ⟨F, rfl⟩
  simp only [hex, dite_true]
  have heq : Classical.choose hex = F := encodeCNF_injective (Classical.choose_spec hex)
  rw [heq]

theorem specFn_invalid (x : List Bool) (h : ¬ ∃ F : CNF, encodeCNF F = x) : specFn x = [] := by
  simp [specFn, h]

def tB (z : Nat) : Nat := 30000 * (z + 1) ^ 4

theorem arith_valid (z V M K n w B : Nat)
    (hV : V ≤ z) (hM : M ≤ z) (hK : K ≤ z) (hn : n ≤ z + 2) (hw : w ≤ n)
    (hB : B ≤ 9 + V + 7 * M + 2 * K) :
    1 + ((8 * z + 2) + (((M * (27 * z + 50) + 16 * z + 16 * K + 4) +
      ((4 * n * n + 35 * n + 20) +
      ((160 * (w + 1) + 120) +
      ((20 * (w + 1) + 16) +
      ((V * ((w + 1) * (4 * n + 16) + 7 * n + 18) + 3) +
      ((M * (60 * (w + 1) * (n + 3) + 120 * n + 25 * z + 180) + 9 * z +
        K * ((w + 1) * (4 * n + 16) + 7 * n + 30) + 2) +
      (2 * (n + 1 + B * (2 * w + 4)) + 1)))))) + 1) +
      (2 * (n + w + z + n) + 39))) ≤ tB z := by
  unfold tB
  set Z := z + 1
  have hZ : 1 ≤ Z := by omega
  have hZ2 : Z ≤ Z * Z := Nat.le_mul_self Z
  have hZ3 : Z * Z ≤ Z * Z * Z := Nat.le_mul_of_pos_right _ hZ
  have hZ4 : Z * Z * Z ≤ Z * Z * Z * Z := Nat.le_mul_of_pos_right _ hZ
  have hZpow : Z ^ 4 = Z * Z * Z * Z := by ring
  have h1 : n ≤ 3 * Z := by omega
  have h2 : w + 1 ≤ 3 * Z := by omega
  have h3 : n + 3 ≤ 5 * Z := by omega
  have h4 : B ≤ 20 * Z := by omega
  have hp1 : M * (27 * z + 50) ≤ 50 * (Z * Z) :=
    le_trans (Nat.mul_le_mul (show M ≤ Z by omega) (show 27 * z + 50 ≤ 50 * Z by omega))
      (by rw [show Z * (50 * Z) = 50 * (Z * Z) by ring])
  have hp2 : n * n ≤ 9 * (Z * Z) :=
    le_trans (Nat.mul_le_mul h1 h1) (by rw [show (3 * Z) * (3 * Z) = 9 * (Z * Z) by ring])
  have hp2' : 4 * n * n = 4 * (n * n) := by ring
  have hp3 : (w + 1) * (4 * n + 16) ≤ 84 * (Z * Z) :=
    le_trans (Nat.mul_le_mul h2 (show 4 * n + 16 ≤ 28 * Z by omega))
      (by rw [show (3 * Z) * (28 * Z) = 84 * (Z * Z) by ring])
  have hp4 : V * ((w + 1) * (4 * n + 16) + 7 * n + 18) ≤ 130 * (Z * Z * Z) :=
    le_trans (Nat.mul_le_mul (show V ≤ Z by omega) (show (w + 1) * (4 * n + 16) + 7 * n + 18 ≤ 130 * (Z * Z) by omega))
      (by rw [show Z * (130 * (Z * Z)) = 130 * (Z * Z * Z) by ring])
  have hp5 : (w + 1) * (n + 3) ≤ 15 * (Z * Z) :=
    le_trans (Nat.mul_le_mul h2 h3) (by rw [show (3 * Z) * (5 * Z) = 15 * (Z * Z) by ring])
  have hp5' : 60 * (w + 1) * (n + 3) = 60 * ((w + 1) * (n + 3)) := by ring
  have hp6 : M * (60 * (w + 1) * (n + 3) + 120 * n + 25 * z + 180) ≤ 1500 * (Z * Z * Z) :=
    le_trans (Nat.mul_le_mul (show M ≤ Z by omega) (show 60 * (w + 1) * (n + 3) + 120 * n + 25 * z + 180 ≤ 1500 * (Z * Z) by omega))
      (by rw [show Z * (1500 * (Z * Z)) = 1500 * (Z * Z * Z) by ring])
  have hp7 : K * ((w + 1) * (4 * n + 16) + 7 * n + 30) ≤ 150 * (Z * Z * Z) :=
    le_trans (Nat.mul_le_mul (show K ≤ Z by omega) (show (w + 1) * (4 * n + 16) + 7 * n + 30 ≤ 150 * (Z * Z) by omega))
      (by rw [show Z * (150 * (Z * Z)) = 150 * (Z * Z * Z) by ring])
  have hp8 : B * (2 * w + 4) ≤ 200 * (Z * Z) :=
    le_trans (Nat.mul_le_mul h4 (show 2 * w + 4 ≤ 10 * Z by omega))
      (by rw [show (20 * Z) * (10 * Z) = 200 * (Z * Z) by ring])
  rw [hZpow]
  omega

theorem prog_spec (x : List Bool) :
    ∃ v' : Reg,
      exec prog ⟨regInit, toFun { emp with inp := x }⟩ = ⟨v', toFun { emp with out := specFn x }⟩ ∧
        1 + cost prog ⟨regInit, toFun { emp with inp := x }⟩ ≤ tB x.length := by
  obtain ⟨b01, r1⟩ := phase1P_spec x
  let v1 := nrm { regInit with b0 := b01, ws := x.foldl wfD .a, hasEmpty := p1Emp .a x }
  let s1 := { emp with X := x, Mstk := List.replicate (p1Cnt .a x) true }
  by_cases hwf : x.foldl wfD .a = .a
  · have hwfB : wfB x = true := by simp [wfB, hwf]
    obtain ⟨F, rfl⟩ := (wfB_iff x).mp hwfB
    set ord := ((F.flatten).map Prod.fst).eraseDups
    set V := ord.length
    set M := F.flatten.length
    set n := V + M + 2
    set w := width n
    set z := (encodeCNF F).length
    have hp1 := p1_cnf F
    have hVM : V ≤ M := order_length_le_occ F
    have h4M : 4 * M ≤ z := four_mul_occ_le F
    have h2K : 2 * F.length ≤ z := two_mul_clauses_le F
    have hV_le : V ≤ z := by omega
    have hM_le : M ≤ z := by omega
    have hK_le : F.length ≤ z := by omega
    have hn_le : n ≤ z + 2 := by omega
    have hw_le : w ≤ n := width_le_self n (by omega)
    have hs1_eq : s1 = { emp with X := encodeCNF F, Mstk := List.replicate M true } := by
      simp [s1, hp1.1, M]
    change Run phase1P regInit { emp with inp := encodeCNF F } v1 s1 _ at r1
    rw [hs1_eq] at r1
    obtain ⟨b02, exp2, eq2, fnd2, par2, r2⟩ := phase2P_spec F v1
      { emp with X := encodeCNF F, Mstk := List.replicate M true } rfl rfl rfl rfl rfl rfl rfl rfl rfl
    let v2 := nrm { v1 with b0 := b02, half := false, inLit := false, expectData := exp2, eqFlag := eq2, found := fnd2, par := par2 }
    let s2 := { emp with X := encodeCNF F, Mstk := List.replicate M true, SeenV := encodeVars (ord.map Nat.bits), Vstk := List.replicate V true }
    obtain ⟨p3, r3⟩ := phase3P_spec V M v2 s2 rfl rfl rfl rfl rfl rfl rfl rfl rfl
    let v3 := nrm { v2 with par := p3 }
    let s3 := { s2 with Mstk := [], Nstk := List.replicate n true, Wstk := List.replicate w true, OutRev := (header n).reverse }
    obtain ⟨p4, r4⟩ := emitAnchorsP_spec w v3 s3 rfl rfl rfl rfl
    let v4 := nrm { v3 with par := p4 }
    let s4 := { s3 with OutRev := (anchorBans.flatMap (encBan w)).reverse ++ s3.OutRev }
    have hv4_emp : v4.hasEmpty = F.any List.isEmpty := by
      simp [v4, v3, v2, v1, nrm, hp1.2]
    obtain ⟨p5, r5⟩ := emitEmptyP_spec F w v4 s4 hv4_emp rfl rfl rfl rfl
    let v5 := nrm { v4 with par := p5 }
    let s5 := { s4 with OutRev := ((emptyBan F).flatMap (encBan w)).reverse ++ s4.OutRev }
    obtain ⟨p6, r6⟩ := emitBoolBansP_spec V w n (by omega) v5 s5 rfl rfl rfl rfl rfl rfl rfl
    let v6 := nrm { v5 with par := p6 }
    let s6 := { s5 with Vstk := [], Uocc := List.replicate (2 + V) true, OutRev := ((boolBans V).flatMap (encBan w)).reverse ++ s5.OutRev }
    obtain ⟨b07, pol7, exp7, eq7, fnd7, par7, r7⟩ := emitClausesP_spec F v6 s6 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    let v7 := nrm { v6 with b0 := b07, half := false, inLit := false, inClause := false, pol := pol7, expectData := exp7, eqFlag := eq7, found := fnd7, par := par7 }
    let s7 := { s6 with X := [], Uocc := List.replicate n true, OutRev := ((clausesBans ord V 0 F).flatMap (encBan w)).reverse ++ s6.OutRev }
    have hs7_out : s7.OutRev = (enc n (makeB F)).reverse := by
      simp only [s7, s6, s5, s4, s3, enc, makeB, ord, V, w, List.flatMap_append, List.reverse_append,
        List.append_assoc]
    have r8 := moveOut_spec (enc n (makeB F)).reverse v7 s7 hs7_out
    let v8 := nrm v7
    let s8 := { s7 with OutRev := [], out := (enc n (makeB F)).reverse.reverse ++ s7.out }
    have rValid := Run.seq r2 (Run.seq r3 (Run.seq r4 (Run.seq r5 (Run.seq r6 (Run.seq r7 r8)))))
    have rIte := Run.ite_true (c := fun v : Reg => decide (v.ws = .a)) (q := Prog.load id)
      (by simp [v1, nrm, hwf]) rValid
    have rDrain := drainAll_spec v8 s8
    have rAll := Run.seq r1 (Run.seq rIte rDrain)
    refine ⟨nrm v8, ?_, ?_⟩
    · have h1 := rAll.1
      unfold prog validBranch
      rw [h1]
      refine St_eq _ _ _ _ rfl ?_
      apply Stk.ext_get <;> simp [s8, s7, s6, s5, s4, s3, s2, emp, specFn_encodeCNF, ord, V, M, n]
    · have h2 := rAll.2
      unfold prog validBranch
      have hsz8 : sizeAll s8 ≤ n + w + z + n := by
        have hsv : (encodeVars (ord.map Nat.bits)).length ≤ z := encodeVars_order_len F
        simp only [sizeAll, s8, s7, s6, s5, s4, s3, s2, emp, List.length_nil,
          List.length_replicate, Nat.zero_add, Nat.add_zero]
        omega
      have hlen_enc : (enc n (makeB F)).reverse.length = n + 1 + (makeB F).length * (2 * w + 4) := by
        rw [List.length_reverse, enc_length]
      rw [hlen_enc] at h2
      have hB := makeB_length F
      have htot := arith_valid z V M F.length n w (makeB F).length hV_le hM_le hK_le hn_le hw_le hB
      change cost (Prog.seq phase1P (Prog.seq (Prog.ite (fun v => decide (v.ws = .a)) (Prog.seq phase2P (Prog.seq phase3P (Prog.seq emitAnchorsP (Prog.seq emitEmptyP (Prog.seq emitBoolBansP (Prog.seq emitClausesP moveOut)))))) (Prog.load id)) drainAll)) _ ≤
        (8 * z + 2) + (((M * (27 * z + 50) + 16 * z + 16 * F.length + 4) +
          ((4 * n * n + 35 * n + 20) +
          ((160 * (w + 1) + 120) +
          ((20 * (w + 1) + 16) +
          ((V * ((w + 1) * (4 * n + 16) + 7 * n + 18) + 3) +
          ((M * (60 * (w + 1) * (n + 3) + 120 * n + 25 * z + 180) + 9 * z +
            F.length * ((w + 1) * (4 * n + 16) + 7 * n + 30) + 2) +
          (2 * (n + 1 + (makeB F).length * (2 * w + 4)) + 1)))))) + 1) +
          (2 * sizeAll s8 + 39)) at h2
      omega
  · have hnot : ¬ ∃ F : CNF, encodeCNF F = x := by
      intro ⟨F, hF⟩
      exact hwf (by rw [← hF]; exact foldl_cnf F)
    have rIte := Run.ite_false (c := fun v : Reg => decide (v.ws = .a)) (p := validBranch)
      (by simp [v1, nrm, hwf]) (Run.load id v1 s1)
    have rDrain := drainAll_spec v1 s1
    have rAll := Run.seq r1 (Run.seq rIte rDrain)
    refine ⟨nrm v1, ?_, ?_⟩
    · have h1 := rAll.1
      unfold prog
      rw [h1]
      refine St_eq _ _ _ _ rfl ?_
      apply Stk.ext_get <;> simp [s1, emp, specFn_invalid x hnot]
    · have h2 := rAll.2
      unfold prog
      have hcnt : p1Cnt .a x ≤ x.length := p1Cnt_le .a x
      have hsz1 : sizeAll s1 ≤ 2 * x.length := by
        simp only [sizeAll, s1, emp, List.length_nil, List.length_replicate, Nat.add_zero]
        omega
      unfold tB
      have hZ : 1 ≤ x.length + 1 := by omega
      have hZ2 : x.length + 1 ≤ (x.length + 1) * (x.length + 1) := Nat.le_mul_self _
      have hZ3 : (x.length + 1) * (x.length + 1) ≤ (x.length + 1) * (x.length + 1) * (x.length + 1) :=
        Nat.le_mul_of_pos_right _ hZ
      have hZ4 : (x.length + 1) * (x.length + 1) * (x.length + 1) ≤
          (x.length + 1) * (x.length + 1) * (x.length + 1) * (x.length + 1) :=
        Nat.le_mul_of_pos_right _ hZ
      have hpow : (x.length + 1) ^ 4 = (x.length + 1) * (x.length + 1) * (x.length + 1) * (x.length + 1) := by ring
      rw [hpow]
      nlinarith

def finalStmt : TM2.Stmt Γ (Option (Pos prog)) Reg :=
  TM2.Stmt.load (fun _ => regInit) TM2.Stmt.halt

noncomputable def tm894 : FinTM2 where
  K := K
  k₀ := K.inp
  k₁ := K.out
  Γ := Γ
  Λ := Option (Pos prog)
  main := some (entry prog)
  σ := Reg
  initialState := regInit
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m := fun l => match l with
    | some a => stmt prog some none a
    | none => finalStmt

theorem tm894_run (x : List Bool) (v' : Reg)
    (h : exec prog ⟨regInit, toFun { emp with inp := x }⟩ = ⟨v', toFun { emp with out := specFn x }⟩) :
    (flip bind tm894.step)^[1 + cost prog ⟨regInit, toFun { emp with inp := x }⟩]
        (some (initList tm894 x)) = some (haltList tm894 (specFn x)) := by
  have h0 : initList tm894 x =
      (⟨some (some (entry prog)), regInit, toFun { emp with inp := x }⟩ :
        TM2.Cfg Γ (Option (Pos prog)) Reg) := by
    unfold initList
    congr 1
    funext k
    cases k with
    | inp => rfl
    | out => rfl
    | w a => cases a <;> rfl
  have h1 : (flip bind (TM2.step tm894.m))^[cost prog ⟨regInit, toFun { emp with inp := x }⟩]
      (some (⟨some (some (entry prog)), regInit, toFun { emp with inp := x }⟩ :
        TM2.Cfg Γ (Option (Pos prog)) Reg)) =
      some ⟨some none, (exec prog ⟨regInit, toFun { emp with inp := x }⟩).var,
        (exec prog ⟨regInit, toFun { emp with inp := x }⟩).stk⟩ :=
    compile_correct (M := tm894.m) prog wf_prog some none (fun _ => rfl)
      ⟨regInit, toFun { emp with inp := x }⟩
  rw [h] at h1
  rw [h0]
  refine iter_add _ 1 _ _ _ _ h1 ?_
  refine (one_step tm894.m none v' (toFun { emp with out := specFn x }) finalStmt _ rfl rfl).trans ?_
  unfold haltList
  simp only [finalStmt, TM2.stepAux]
  congr 1
  congr 1
  funext k
  cases k with
  | inp => rfl
  | out => rfl
  | w a => cases a <;> rfl

noncomputable def comp894 :
    TM2ComputableInTime (fun x : List Bool => x) (fun x : List Bool => x) specFn where
  tm := tm894
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := tB
  outputsFun := fun x =>
    { steps := 1 + cost prog ⟨regInit, toFun { emp with inp := x }⟩
      evals_in_steps := by
        obtain ⟨v', e1, -⟩ := prog_spec x
        have hmap0 : ∀ l : List Bool, (List.map (Equiv.refl Bool).invFun l : List (tm894.Γ tm894.k₀)) = l := by
          intro l
          induction l with
          | nil => rfl
          | cons a l ih => exact congrArg (List.cons a) ih
        have hmap1 : ∀ l : List Bool, (List.map (Equiv.refl Bool).invFun l : List (tm894.Γ tm894.k₁)) = l := by
          intro l
          induction l with
          | nil => rfl
          | cons a l ih => exact congrArg (List.cons a) ih
        simp only [Option.map_some]
        rw [hmap0, hmap1]
        exact tm894_run x v' e1
      steps_le_m := by
        obtain ⟨-, -, h3⟩ := prog_spec x
        exact h3 }

end Phase5AndFinal

end PEqualNP.Outside.L_lib_894_aux

theorem PEqualNP.Outside.L_lib_894 : (let bits := fun (w v : Nat) => (List.range w).map (fun j => v.testBit j)
let header := fun n : Nat => List.replicate n true ++ [false]
let width := fun n : Nat => n.log2+1
let Ban := (Nat × Nat) × (Nat × Nat)
let legal := fun (n : Nat) (B : List Ban) => 2 ≤ n ∧ ∀ e ∈ B,
  e.1.1 < e.2.1 ∧ e.2.1 < n ∧ e.1.2 < 3 ∧ e.2.2 < 3
let enc := fun (n : Nat) (B : List Ban) =>
  header n ++ B.flatMap (fun e => bits (width n) e.1.1 ++ bits 2 e.1.2 ++
    bits (width n) e.2.1 ++ bits 2 e.2.2)
let valid := fun (n : Nat) (B : List Ban) (a : Fin n → Fin 3) =>
  let v := List.ofFn (fun j => (a j).val)
  ∀ e ∈ B, v.getD e.1.1 3 ≠ e.1.2 ∨ v.getD e.2.1 3 ≠ e.2.2
∃ (f : List Bool → List Bool) (C : Nat),
  (∃ M : Turing.TM2ComputableInTime (fun x : List Bool => x) (fun x : List Bool => x) f,
    (∀ j, Finite (M.tm.Γ j)) ∧ ∀ z, M.time z ≤ C*(z+1)^4) ∧
  (∀ x : List Bool, (¬ ∃ F : PEqualNP.Search.CNF, PEqualNP.Search.encodeCNF F = x) → f x = []) ∧
  ∀ F : PEqualNP.Search.CNF,
    let occ := F.flatten
    let order := (occ.map Prod.fst).eraseDups
    let n := order.length+occ.length+2
    let Models := {a : Fin order.length → Bool // ∃ raw : Nat → Bool,
      PEqualNP.Search.CNF.eval raw F = true ∧ ∀ i, a i = raw (order.get i)}
    ∃ B : List Ban, legal n B ∧ f (PEqualNP.Search.encodeCNF F) = enc n B ∧
      B.length ≤ 9+order.length+7*occ.length+2*F.length ∧
      ∃ E : Models ≃ {a : Fin n → Fin 3 // valid n B a}, ∀ x i (j : Fin n),
        j.val = 2+i.val → ((E x).val j).val = (x.val i).toNat) := by
  refine ⟨PEqualNP.Outside.L_lib_894_aux.specFn, 30000, ?_, ?_, ?_⟩
  · refine ⟨PEqualNP.Outside.L_lib_894_aux.comp894, ?_, ?_⟩
    · intro j
      exact inferInstanceAs (Finite Bool)
    · intro z
      exact le_refl _
  · exact PEqualNP.Outside.L_lib_894_aux.specFn_invalid
  · intro F
    refine ⟨PEqualNP.Outside.L_lib_894_aux.makeB F,
      PEqualNP.Outside.L_lib_894_aux.makeB_legal F,
      PEqualNP.Outside.L_lib_894_aux.specFn_encodeCNF F,
      PEqualNP.Outside.L_lib_894_aux.makeB_length F,
      PEqualNP.Outside.L_lib_894_aux.bijection_exists F⟩
