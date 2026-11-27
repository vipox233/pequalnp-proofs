import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_28330.Frame
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def edges : List ℕ := [0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7]
def target (x : Fin 8 → Bool) := decide (∃ i < edges.length / 2,
  (List.ofFn x).getD (edges.getD (2*i) 0) false = true ∧
  (List.ofFn x).getD (edges.getD (2*i+1) 0) false = true)

def witness : List Gate := [
  ⟨.and, [6, 7]⟩,
  ⟨.or, [6, 7]⟩,
  ⟨.or, [0, 1]⟩,
  ⟨.or, [0, 7]⟩,
  ⟨.or, [3, 10]⟩,
  ⟨.or, [9, 10]⟩,
  ⟨.and, [4, 13]⟩,
  ⟨.or, [2, 11]⟩,
  ⟨.and, [9, 12]⟩,
  ⟨.or, [5, 8]⟩,
  ⟨.or, [14, 16]⟩,
  ⟨.and, [15, 17]⟩,
  ⟨.or, [18, 19]⟩]

theorem good : ∀ g ∈ witness, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
  simp [witness]

theorem correct : ∀ x : Fin 8 → Bool, Circuit.eval ⟨witness,20⟩ (List.ofFn x) = target x := by
  decide +kernel

theorem finish (lower : ∀ (gs : List Gate) (o : ℕ), FanInTwo ⟨gs,o⟩ →
    (∀ x : Fin 8 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = target x) →
    (∃ g ∈ gs, g.op = .not) → 13 ≤ gs.length) : (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) := by
  intro gs o fan _ computes
  by_cases hn : ∃ g ∈ gs, g.op = .not
  · exact ⟨witness, 20, good, lower gs o fan computes hn, correct⟩
  · refine ⟨gs, o, ?_, le_rfl, computes⟩
    intro g hg
    obtain ⟨op, len⟩ := fan g hg
    exact ⟨op.imp_right (fun h => h.resolve_right (fun e => hn ⟨g,hg,e⟩)),len⟩

end PEqualNP.Outside.L_meta_28330.Frame

namespace PEqualNP.Outside.L_meta_28330.Reduce
variable {m : Nat}
def canon (w : BitVec (m+1)) := if w.getLsbD 0 then ~~~w else w
def signed (d : Bool) (w : BitVec (m+1)) := if d then ~~~w else w
def gate (s t : Bool) (a b : BitVec (m+1)) := canon (signed s a &&& signed t b)
def Path (goal : BitVec (m+1)) (k : Nat) (S : Finset (BitVec (m+1))) : Prop :=
  ∀ P : Nat → Finset (BitVec (m+1)) → Prop, P 0 {goal} →
    (∀ {k a b U} (s t : Bool), a ≠ b → gate s t a b ∉ insert a (insert b U) →
      gate s t a b ≠ 0 → P k (insert (gate s t a b) U) → P (k+1) (insert a (insert b U))) →
    P k S
theorem Path.done {g : BitVec (m+1)} : Path g 0 {g} := fun _ d _ => d
theorem Path.binary {g : BitVec (m+1)} {k a b U} (s t : Bool) (ne : a ≠ b)
    (fresh : gate s t a b ∉ insert a (insert b U)) (proper : gate s t a b ≠ 0)
    (tail : Path g k (insert (gate s t a b) U)) : Path g (k+1) (insert a (insert b U)) :=
  fun P d f => f s t ne fresh proper (tail P d f)
theorem canon_not (x : BitVec (m+1)) : canon (~~~x) = canon x := by
  unfold canon
  simp only [BitVec.getLsbD_not, Nat.zero_lt_succ,decide_true, Bool.true_and]
  cases x.getLsbD 0 <;> simp

theorem canon_canon (x : BitVec (m+1)) : canon (canon x) = canon x := by
  by_cases h : x.getLsbD 0 = true
  · rw [show canon x = ~~~x from if_pos h,canon_not,show canon x = ~~~x from if_pos h]
  · rw [show canon x = x from if_neg h]
    exact if_neg h

theorem sign_back (x : BitVec (m+1)) : signed (x.getLsbD 0) (canon x) = x := by
  unfold signed canon
  cases x.getLsbD 0 <;> simp

theorem canon_zero : canon (0 : BitVec (m+1)) = 0 := by simp [canon]
theorem gate_left_zero (s t : Bool) (x : BitVec (m+1)) :
    gate s t 0 x = 0 ∨ gate s t 0 x = canon x := by
  cases s with
  | false => exact Or.inl ((congrArg canon (BitVec.zero_and (x := signed t x))).trans canon_zero)
  | true =>
    cases t with
    | false => right; simp [gate,signed]
    | true => right; simp [gate,signed,canon_not]

theorem gate_right_zero (s t : Bool) (x : BitVec (m+1)) :
    gate s t x 0 = 0 ∨ gate s t x 0 = canon x := by
  rw [show gate s t x 0 = gate t s 0 x from congrArg canon (BitVec.and_comm ..)]
  exact gate_left_zero _ _ _

theorem gate_same (s t : Bool) (x : BitVec (m+1)) : gate s t x x = 0 ∨ gate s t x x = canon x := by
  cases s <;> cases t
  · exact Or.inr (congrArg canon (BitVec.and_self (x := x)))
  · exact Or.inl ((congrArg canon (BitVec.and_not_self x)).trans canon_zero)
  · exact Or.inl ((congrArg canon (BitVec.not_and_self x)).trans canon_zero)
  · exact Or.inr ((congrArg canon (BitVec.and_self (x := ~~~x))).trans (canon_not x))

variable {A : Type} [DecidableEq A] (pin : A → BitVec (m+1))
def avail (S : Finset A) := (S.image pin).erase 0
def lost (S : Finset A) := (S.filter fun x => pin x = 0).card
theorem avail_mem {S : Finset A} {x : BitVec (m+1)} :
    x ∈ avail pin S ↔ x ≠ 0 ∧ ∃ a ∈ S, pin a = x := by simp [avail]

theorem avail_mono {S T : Finset A} (h : S ⊆ T) : avail pin S ⊆ avail pin T := by
  intro y hy
  obtain ⟨hn,x,hx,rfl⟩ := (avail_mem pin).mp hy
  exact (avail_mem pin).mpr ⟨hn,x,h hx,rfl⟩

theorem avail_cases {S : Finset A} {c : A} {x : BitVec (m+1)} (h : x ∈ avail pin (insert c S)) :
    x = pin c ∨ x ∈ avail pin S := by
  obtain ⟨hn,y,hy,rfl⟩ := (avail_mem pin).mp h
  rcases Finset.mem_insert.mp hy with rfl|hy
  · exact Or.inl rfl
  · exact Or.inr ((avail_mem pin).mpr ⟨hn,y,hy,rfl⟩)

theorem lost_insert (c : A) (S : Finset A) :
    lost pin (insert c S) = lost pin S + (if pin c = 0 ∧ c ∉ S then 1 else 0) := by
  by_cases mem : c ∈ S
  · rw [Finset.insert_eq_of_mem mem,if_neg (fun q => q.2 mem),Nat.add_zero]
  · by_cases h : pin c = 0
    · rw [if_pos ⟨h,mem⟩]
      unfold lost
      rw [Finset.filter_insert,if_pos h,Finset.card_insert_of_notMem]
      exact fun q => mem (Finset.mem_filter.mp q).1
    · rw [if_neg (fun q => h q.1),Nat.add_zero]
      unfold lost
      rw [Finset.filter_insert,if_neg h]

theorem cost_skip (a b c : A) (U : Finset A) (fresh : c ∉ U)
    (both : pin a = 0 → pin b = 0 → pin c = 0) :
    lost pin (insert a (insert b U)) ≤ lost pin (insert c U) + 1 := by
  simp only [lost_insert]
  split_ifs <;> grind

def Proj (goal : BitVec (m+1)) (limit extra : Nat) (S : Finset A) : Prop :=
  ∃ k, k + lost pin S + extra ≤ limit ∧ ∃ T ⊆ avail pin S, Path goal k T

theorem proj_done (x : A) (nz : pin x ≠ 0) : Proj pin (pin x) 0 0 {x} := by
  refine ⟨0,?_,{pin x},?_,Path.done⟩ <;> simp [lost,avail] <;> exact nz
theorem proj_inv {g : BitVec (m+1)} {limit extra : Nat} (a c : A) (U : Finset A)
    (newc : c ∉ U) (eq : pin c = pin a) (tail : Proj pin g limit extra (insert c U)) :
    Proj pin g limit extra (insert a U) := by
  obtain ⟨k,hle,T,sub,path⟩ := tail
  refine ⟨k,?_,T,?_,path⟩
  · simp only [lost_insert,eq] at hle ⊢
    split_ifs at * <;> grind
  · intro x hx
    rcases avail_cases pin (sub hx) with eq'|old
    · exact (avail_mem pin).mpr ⟨((avail_mem pin).mp (sub hx)).1,a,by simp,(eq'.trans eq).symm⟩
    · exact avail_mono pin (Finset.subset_insert _ _) old

theorem proj_strong {g : BitVec (m+1)} {limit : Nat} (a b c : A) (U : Finset A)
    (newc : c ∉ U) (hc : pin c = 0) (one : pin a ≠ 0 ∨ pin b ≠ 0)
    (tail : Proj pin g limit 0 (insert c U)) : Proj pin g (limit+1) 1 (insert a (insert b U)) := by
  obtain ⟨k,le,T,sub,path⟩ := tail
  refine ⟨k,?_,T,?_,path⟩
  · simp only [lost_insert,hc] at le ⊢
    split_ifs at * <;> grind
  · intro x hx
    rcases avail_cases pin (sub hx) with eq|old
    · exact (((avail_mem pin).mp (sub hx)).1 (eq.trans hc)).elim
    · exact avail_mono pin (by intro _ mem; simp [mem]) old

theorem proj_bin {g : BitVec (m+1)} {b extra : Nat} (a x c : A) (U : Finset A)
    (can : ∀ v, canon (pin v) = pin v) (cnew : c ∉ U) (s t : Bool)
    (repr : pin c = gate s t (pin a) (pin x))
    (tail : Proj pin g b extra (insert c U)) : Proj pin g (b+1) extra (insert a (insert x U)) := by
  let prev := insert a (insert x U)
  obtain ⟨k,hle,T,sub,path⟩ := tail
  change k + lost pin (insert c U) + extra ≤ b at hle
  change T ⊆ avail pin (insert c U) at sub
  have both (ha : pin a = 0) (hx : pin x = 0) : pin c = 0 := by
    rw [repr,ha,hx]
    exact (gate_same s t 0).elim id (fun q => q.trans canon_zero)
  have skipcost := cost_skip pin a x c U cnew both
  have liftU : avail pin U ⊆ avail pin prev := avail_mono pin (by intro u hu; simp [prev,hu])
  by_cases useful : pin c ∈ T ∧ pin c ∉ avail pin prev
  · have nz := ((avail_mem pin).mp (sub useful.1)).1
    have df (v : A) (hv : v ∈ prev) : pin c ≠ pin v := by
      intro e
      exact useful.2 ((avail_mem pin).mpr ⟨nz,v,hv,e.symm⟩)
    have da := df a (by simp [prev])
    have dx := df x (by simp [prev])
    have ha : pin a ≠ 0 := by
      intro h
      have drop := gate_left_zero s t (pin x)
      rw [h] at repr
      rw [←repr,can] at drop
      exact drop.elim nz dx
    have hx : pin x ≠ 0 := by
      intro h
      have drop := gate_right_zero s t (pin a)
      rw [h] at repr
      rw [←repr,can] at drop
      exact drop.elim nz da
    have distinct : pin a ≠ pin x := by
      intro e
      have drop := gate_same s t (pin x)
      rw [e] at repr
      rw [←repr,can] at drop
      exact drop.elim nz dx
    have vcost : lost pin prev ≤ lost pin (insert c U) := by
      simp only [prev,lost_insert]
      split_ifs <;> grind
    let V := T.erase (pin c)
    have old (v : BitVec (m+1)) (hv : v ∈ V) : v ∈ avail pin U :=
      (avail_cases pin (sub (Finset.mem_erase.mp hv).2)).resolve_left (Finset.mem_erase.mp hv).1
    refine ⟨k+1,by change k+1+lost pin prev + extra ≤ b+1; omega,insert (pin a) (insert (pin x) V),?_,?_⟩
    · intro v hv
      rcases Finset.mem_insert.mp hv with rfl|hv
      · exact (avail_mem pin).mpr ⟨ha,a,by simp [prev],rfl⟩
      rcases Finset.mem_insert.mp hv with rfl|hv
      · exact (avail_mem pin).mpr ⟨hx,x,by simp [prev],rfl⟩
      exact liftU (old _ hv)
    · apply Path.binary s t distinct
      · rw [←repr]
        simp [V,da,dx]
      · rwa [←repr]
      · rwa [←repr,show insert (pin c) V = T from Finset.insert_erase useful.1]
  · refine ⟨k,by change k+lost pin (insert a (insert x U)) + extra ≤ b+1; omega,T,?_,path⟩
    intro v hv
    rcases avail_cases pin (sub hv) with rfl|old
    · by_contra miss
      exact useful ⟨hv,miss⟩
    · exact liftU old
end PEqualNP.Outside.L_meta_28330.Reduce

namespace PEqualNP.Outside.L_meta_28330
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev Word := BitVec 256
def ones : Word := BitVec.allOnes 256
def goal : Word := 0xfffffffffffffffffffffffefffeee00fffffffffffeeeaafffffffefffeee00
def roots : List Word := [
  0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,
  0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,
  0xffffffffffffffffffffffffffffffff00000000000000000000000000000000,
  0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,
  0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,
  0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,
  0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,
  0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000]
def join (d : Bool) (a b : Word) : Word := if d then a ||| b else a &&& b

def Live (b n : Nat) (S : Finset Word) : Prop :=
  ∀ (P : Nat → Nat → Finset Word → Prop),
    P 0 0 {goal} →
    (∀ {i j : Nat} {a x : Word} {U : Finset Word} (d : Bool), a ≠ x →
      join d a x ∉ insert a (insert x U) → (join d a x ≠ 0 ∧ join d a x ≠ ones) →
      P i j (insert (join d a x) U) → P (i+1) j (insert a (insert x U))) →
    (∀ {i j : Nat} {a : Word} {U : Finset Word},
      ~~~a ∉ insert a U → (~~~a ≠ 0 ∧ ~~~a ≠ ones) →
      P i j (insert (~~~a) U) → P i (j+1) (insert a U)) →
    P b n S

theorem Live.done : Live 0 0 {goal} :=
  fun _ done _ _ => done

theorem Live.binary {b n : Nat} {a x : Word} {U : Finset Word} (d : Bool) (ne : a ≠ x)
    (fresh : join d a x ∉ insert a (insert x U))
    (proper : join d a x ≠ 0 ∧ join d a x ≠ ones)
    (tail : Live b n (insert (join d a x) U)) :
    Live (b+1) n (insert a (insert x U)) :=
  fun P done binary inversion => binary d ne fresh proper (tail P done binary inversion)

theorem Live.inversion {b n : Nat} {a : Word} {U : Finset Word}
    (fresh : ~~~a ∉ insert a U) (proper : ~~~a ≠ 0 ∧ ~~~a ≠ ones)
    (tail : Live b n (insert (~~~a) U)) : Live b (n+1) (insert a U) :=
  fun P done binary inversion => inversion fresh proper (tail P done binary inversion)

theorem Live.recPlain {motive : ∀ {b n S}, Live b n S → Prop}
    (done : motive Live.done)
    (binary : ∀ {b n : Nat} {a x : Word} {U : Finset Word} (d : Bool) (ne : a ≠ x)
      (fresh : join d a x ∉ insert a (insert x U))
      (proper : join d a x ≠ 0 ∧ join d a x ≠ ones)
      (tail : Live b n (insert (join d a x) U)),
      motive tail → motive (Live.binary d ne fresh proper tail))
    (inversion : ∀ {b n : Nat} {a : Word} {U : Finset Word}
      (fresh : ~~~a ∉ insert a U) (proper : ~~~a ≠ 0 ∧ ~~~a ≠ ones)
      (tail : Live b n (insert (~~~a) U)),
      motive tail → motive (Live.inversion fresh proper tail))
    {b n : Nat} {S : Finset Word} (h : Live b n S) : motive h := by
  let P (b n : Nat) (S : Finset Word) : Prop := ∃ p : Live b n S, motive p
  have result : P b n S := by
    apply h P
    · exact ⟨Live.done,done⟩
    · intro i j a x U d ne fresh proper tail
      obtain ⟨p,ih⟩ := tail
      exact ⟨Live.binary d ne fresh proper p,binary d ne fresh proper p ih⟩
    · intro i j a U fresh proper tail
      obtain ⟨p,ih⟩ := tail
      exact ⟨Live.inversion fresh proper p,inversion fresh proper p ih⟩
  obtain ⟨_,proof⟩ := result
  exact proof

theorem Live.casesPlain {motive : ∀ {b n S}, Live b n S → Prop}
    (done : motive Live.done)
    (binary : ∀ {b n : Nat} {a x : Word} {U : Finset Word} (d : Bool) (ne : a ≠ x)
      (fresh : join d a x ∉ insert a (insert x U))
      (proper : join d a x ≠ 0 ∧ join d a x ≠ ones)
      (tail : Live b n (insert (join d a x) U)), motive (Live.binary d ne fresh proper tail))
    (inversion : ∀ {b n : Nat} {a : Word} {U : Finset Word}
      (fresh : ~~~a ∉ insert a U) (proper : ~~~a ≠ 0 ∧ ~~~a ≠ ones)
      (tail : Live b n (insert (~~~a) U)), motive (Live.inversion fresh proper tail))
    {b n : Nat} {S : Finset Word} (h : Live b n S) : motive h := by
  apply Live.recPlain (motive := @motive) done _ _ h
  · intro i j a x U d ne fresh proper tail _
    exact binary d ne fresh proper tail
  · intro i j a U fresh proper tail _
    exact inversion fresh proper tail

theorem goal_proper : goal ≠ 0 ∧ goal ≠ ones := by decide +kernel

def assignment (r : Fin 256) : Fin 8 → Bool := fun i => r.val.testBit (([0,1,7,2,3,6,4,5] : List Nat).get i)
def readBit (r : Fin 256) (v : Word) := v.getLsbD r
@[local simp] theorem read_ones (r : Fin 256) : readBit r ones = true := by
  exact (BitVec.getLsbD_allOnes).trans (decide_eq_true r.isLt)
@[local simp] theorem read_zero (r : Fin 256) : readBit r 0 = false := by simp [readBit]
@[local simp] theorem ones_and (a : Word) : ones &&& a = a := BitVec.allOnes_and
@[local simp] theorem and_ones (a : Word) : a &&& ones = a := BitVec.and_allOnes
@[local simp] theorem ones_or (a : Word) : ones ||| a = ones := BitVec.allOnes_or
@[local simp] theorem or_ones (a : Word) : a ||| ones = ones := BitVec.or_allOnes

theorem roots_bits : ∀ r : Fin 256, roots.map (readBit r) = List.ofFn (assignment r) := by decide +kernel
abbrev graph := Frame.target
theorem row_flags : ∀ r : Fin 256, graph (assignment r) = readBit r goal := by decide +kernel

theorem getD_map {α β} (f : α → β) (s : List α) (i : Nat) (a : α) :
    (s.map f).getD i (f a) = f (s.getD i a) := by
  induction s generalizing i with
  | nil => simp
  | cons x s ih => cases i with
    | zero => rfl
    | succ i => exact ih i

theorem getD_mem_or (w : List Word) (i : Nat) : w.getD i 0 ∈ w ∨ w.getD i 0 = 0 := by
  by_cases h : i < w.length
  · left
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
    exact List.getElem_mem h
  · right
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    rfl

def binaryWord (w : List Word) (g : Gate) : Word :=
  let d := match g.op with | .or => true | _ => false
  match g.inputs with
  | [] => if d then 0 else ones
  | [a] => w.getD a 0
  | a::b::_ => join d (w.getD a 0) (w.getD b 0)

def gateWord (w : List Word) (g : Gate) : Word :=
  match g.op with
  | .not => match g.inputs with | [] => ones | a::_ => ~~~(w.getD a 0)
  | _ => binaryWord w g

def binCost (g : Gate) : Nat :=
  match g.op, g.inputs with | .and, _::_::_ | .or, _::_::_ => 1 | _, _ => 0
def invCost (g : Gate) : Nat := match g.op with | .not => 1 | _ => 0

def binaryCount : List Gate → Nat
  | [] => 0 | g::gs => binaryCount gs + binCost g
def inversionCount : List Gate → Nat
  | [] => 0 | g::gs => inversionCount gs + invCost g

def stepWord (w : List Word) (g : Gate) := w ++ [gateWord w g]
def stepBit (w : List Bool) (g : Gate) :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def allowed (g : Gate) := (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

theorem step_correct (r : Fin 256) (w : List Word) (g : Gate) (h : allowed g) :
    (stepWord w g).map (readBit r) = stepBit (w.map (readBit r)) g := by
  have get (j : Nat) : (w[j]?.map (readBit r)).getD false = readBit r (w[j]?.getD 0) := by
    cases w[j]? <;> simp [readBit]
  rcases g with ⟨op,ins⟩
  rcases h with ⟨hOp, hlen⟩
  change op = .and ∨ op = .or ∨ op = .not at hOp
  change ins.length ≤ 2 at hlen
  rcases hOp with rfl|rfl|rfl <;> cases ins with
  | nil => simp [stepWord,stepBit,gateWord,binaryWord,GateOp.eval] <;> exact read_zero r
  | cons a rest =>
    cases rest with
    | nil => simp [stepWord,stepBit,gateWord,binaryWord,get,GateOp.eval,readBit]
    | cons b tail =>
      cases tail with
      | nil => simp [stepWord,stepBit,gateWord,binaryWord,get,GateOp.eval,join,readBit]
      | cons c rest => simp at hlen

theorem fold_correct (r : Fin 256) (gs : List Gate) (w : List Word)
    (h : ∀ g ∈ gs, allowed g) :
    (gs.foldl stepWord w).map (readBit r) = gs.foldl stepBit (w.map (readBit r)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih _ (by grind), step_correct r w g (h _ (by simp))]

theorem sampled_circuit (C : Circuit) (hp : ∀ g ∈ C.gates, allowed g)
    (accept : ∀ r : Fin 256, C.eval (List.ofFn (assignment r)) = readBit r goal) :
    (C.gates.foldl stepWord roots).getD C.output 0 = goal := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  let r : Fin 256 := ⟨i,hi⟩
  change readBit r ((C.gates.foldl stepWord roots).getD C.output 0) = readBit r goal
  rw [← getD_map (readBit r) (C.gates.foldl stepWord roots) C.output 0]
  rw [fold_correct r C.gates roots hp, roots_bits]
  rw [read_zero]
  exact accept r

theorem nontrivial_join (d : Bool) (a b : Word)
    (haa : join d a b ≠ a) (hbb : join d a b ≠ b)
    (h0 : join d a b ≠ 0) (h1 : join d a b ≠ ones) :
    a ≠ 0 ∧ b ≠ 0 ∧ a ≠ ones ∧ b ≠ ones ∧ a ≠ b := by
  refine ⟨?_,?_,?_,?_,?_⟩ <;> rintro rfl <;> cases d <;> simp_all [join]

theorem not_ones : ~~~ones = (0 : Word) := by decide +kernel
theorem not_zero : ~~~(0 : Word) = ones := by decide +kernel

def Parents (w : List Word) (g : Gate) (c : Word) : Prop :=
  (∃ d a b, c = join d a b ∧ binCost g = 1 ∧ a ∈ w ∧ b ∈ w ∧
    a ≠ 0 ∧ b ≠ 0 ∧ a ≠ ones ∧ b ≠ ones ∧ a ≠ b) ∨
  (∃ a, c = ~~~a ∧ invCost g = 1 ∧ a ∈ w ∧ a ≠ 0 ∧ a ≠ ones)

theorem binary_parents (w : List Word) (op : GateOp) (opok : op = .and ∨ op = .or)
    (ins : List Nat) (missing : binaryWord w ⟨op,ins⟩ ∉ w)
    (p0 : binaryWord w ⟨op,ins⟩ ≠ 0) (p1 : binaryWord w ⟨op,ins⟩ ≠ ones) :
    Parents w ⟨op,ins⟩ (binaryWord w ⟨op,ins⟩) := by
  let d := match op with | .or => true | _ => false
  cases ins with
  | nil =>
    change (if d then 0 else ones) ≠ 0 at p0
    change (if d then 0 else ones) ≠ ones at p1
    cases d <;> simp_all
  | cons i rest =>
    cases rest with
    | nil =>
      change w.getD i 0 ∉ w at missing
      change w.getD i 0 ≠ 0 at p0
      exact (getD_mem_or w i).elim (fun h => (missing h).elim) (fun h => (p0 h).elim)
    | cons j tail =>
      let a := w.getD i 0
      let b := w.getD j 0
      change join d a b ∉ w at missing
      change join d a b ≠ 0 at p0
      change join d a b ≠ ones at p1
      have absent (u : Word) (mem : u ∈ w ∨ u = 0) : join d a b ≠ u := by
        intro e
        exact mem.elim (fun m => missing (e ▸ m)) (fun z => p0 (e.trans z))
      have parts := nontrivial_join d a b (absent _ (getD_mem_or w i))
        (absent _ (getD_mem_or w j)) p0 p1

      have cost : binCost ⟨op,i::j::tail⟩ = 1 := by rcases opok with rfl|rfl <;> rfl
      exact Or.inl ⟨d,a,b,rfl,cost,(getD_mem_or w i).resolve_right parts.1,
        (getD_mem_or w j).resolve_right parts.2.1,parts⟩

theorem gate_parents (w : List Word) (g : Gate) (okay : allowed g)
    (missing : gateWord w g ∉ w) (p0 : gateWord w g ≠ 0) (p1 : gateWord w g ≠ ones) :
    Parents w g (gateWord w g) := by
  rcases g with ⟨op,ins⟩
  have ops : op = .and ∨ op = .or ∨ op = .not := okay.1
  rcases ops with h|h|h
  · subst op
    exact binary_parents w _ (.inl rfl) ins missing p0 p1
  · subst op
    exact binary_parents w _ (.inr rfl) ins missing p0 p1
  · subst op
    cases ins with
    | nil => exact (p1 rfl).elim
    | cons i rest =>
      let a := w.getD i 0
      change ~~~a ≠ 0 at p0
      change ~~~a ≠ ones at p1
      have a0 : a ≠ 0 := fun e => p1 (e ▸ not_zero)
      have a1 : a ≠ ones := fun e => p0 (e ▸ not_ones)
      exact Or.inr ⟨a,rfl,rfl,(getD_mem_or w i).resolve_right a0,a0,a1⟩

def Trace (b n : Nat) (w : List Word) : Prop :=
  ∃ (k j : Nat) (S : Finset Word), k ≤ b ∧ j ≤ n ∧
    (∀ x ∈ S, x ∈ w ∧ x ≠ 0 ∧ x ≠ ones) ∧ Live k j S

theorem unwind (b n : Nat) (w : List Word) (g : Gate) (okay : allowed g)
    (t : Trace b n (stepWord w g)) : Trace (b + binCost g) (n + invCost g) w := by
  obtain ⟨k,j,S,hk,hj,valid,live⟩ := t
  let c := gateWord w g
  have prev (x : Word) (hx : x ∈ S) : (x ∈ w ∨ x = c) ∧ x ≠ 0 ∧ x ≠ ones := by
    simpa [c,stepWord] using valid x hx
  by_cases used : c ∈ S
  · by_cases old : c ∈ w
    · exact ⟨k,j,S,by omega,by omega,fun x hx => by have h := prev x hx; grind,live⟩
    · let U := S.erase c
      have uc : c ∉ U := Finset.notMem_erase _ _
      have sub (x : Word) (hx : x ∈ U) : x ∈ w ∧ x ≠ 0 ∧ x ≠ ones := by
        have hx' := Finset.mem_erase.mp hx
        have h := prev x hx'.2
        exact ⟨h.1.resolve_right hx'.1,h.2⟩
      have back : insert c U = S := Finset.insert_erase used
      rcases gate_parents w g okay old (valid c used).2.1 (valid c used).2.2 with binary|inv
      · obtain ⟨d,a,x,eqc,cost,ha,hx,a0,x0,a1,x1,ne⟩ := binary
        change c = join d a x at eqc
        have ca : c ≠ a := fun e => old (e ▸ ha)
        have cx : c ≠ x := fun e => old (e ▸ hx)
        refine ⟨k+1,j,insert a (insert x U),by omega,by omega,?_,?_⟩
        · intro y hy
          rcases Finset.mem_insert.mp hy with rfl|hy
          · exact ⟨ha,a0,a1⟩
          rcases Finset.mem_insert.mp hy with rfl|hy
          · exact ⟨hx,x0,x1⟩
          exact sub _ hy
        · apply Live.binary d ne
          · simpa [← eqc,ca,cx] using uc
          · exact eqc ▸ (valid c used).2
          · rwa [← eqc,back]
      · obtain ⟨a,eqc,cost,ha,a0,a1⟩ := inv
        change c = ~~~a at eqc
        have ca : c ≠ a := fun e => old (e ▸ ha)
        refine ⟨k,j+1,insert a U,by omega,by omega,?_,?_⟩
        · intro y hy
          rcases Finset.mem_insert.mp hy with rfl|hy
          · exact ⟨ha,a0,a1⟩
          exact sub _ hy
        · apply Live.inversion
          · simpa [←eqc,ca] using uc
          · exact eqc ▸ (valid c used).2
          · rwa [←eqc,back]
  · exact ⟨k,j,S,by omega,by omega,fun x hx => by have h := prev x hx; grind,live⟩

theorem trace_aux (gs : List Gate) (w : List Word) (out : Nat) (hp : ∀ g ∈ gs, allowed g)
    (success : (gs.foldl stepWord w).getD out 0 = goal) :
    Trace (binaryCount gs) (inversionCount gs) w := by
  induction gs generalizing w with
  | nil =>
    change w.getD out 0 = goal at success
    have h := (getD_mem_or w out).resolve_right (success ▸ goal_proper.1)
    rw [success] at h
    refine ⟨0,0,{goal},by simp [binaryCount],by simp [inversionCount],?_,Live.done⟩
    simpa using And.intro h goal_proper
  | cons g gs ih => exact unwind _ _ w g (hp _ (by simp)) (ih _ (by grind) success)

theorem circuit_live (C : Circuit) (legal : ∀ g ∈ C.gates, allowed g)
    (correct : ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = graph x) :
    ∃ b ≤ binaryCount C.gates, ∃ n ≤ inversionCount C.gates, ∃ S ⊆ roots.toFinset, Live b n S := by
  have accept (r : Fin 256) : C.eval (List.ofFn (assignment r)) = readBit r goal :=
    (correct _).trans (row_flags r)
  obtain ⟨b,n,S,hb,hn,incl,live⟩ := trace_aux _ _ _ legal (sampled_circuit C legal accept)
  exact ⟨b,hb,n,hn,S,fun x hx => List.mem_toFinset.mpr (incl x hx).1,live⟩

theorem agree_join (p q : Fin 256) (d : Bool) (a x : Word)
    (ha : readBit p a = readBit q a) (hx : readBit p x = readBit q x) :
    readBit p (join d a x) = readBit q (join d a x) := by
  cases d <;> simp_all [join,readBit]

theorem agree_not (p q : Fin 256) (a : Word) (ha : readBit p a = readBit q a) :
    readBit p (~~~a) = readBit q (~~~a) := by simp_all [readBit]

theorem live_agrees {b n S} (live : Live b n S) (p q : Fin 256)
    (same : ∀ x ∈ S, readBit p x = readBit q x) : readBit p goal = readBit q goal := by
  induction live using Live.recPlain with
  | done => exact same goal (by simp)
  | @binary b n a x U d _ _ _ _ ih =>
    apply ih
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl|hy
    · exact agree_join p q d a x (same _ (by simp)) (same _ (by simp))
    · exact same _ (by simp [hy])
  | @inversion b n a U _ _ _ ih =>
    apply ih
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl|hy
    · exact agree_not p q a (same _ (by simp))
    · exact same _ (by simp [hy])

def witnesses (i : Fin 8) : Fin 256 × Fin 256 := ([(8,9),(8,10),(64,192),(16,20),(1,9),(1,65),(1,17),(1,33)] : List (Fin 256 × Fin 256)).get i
theorem witness_correct : ∀ i : Fin 8,
    readBit (witnesses i).1 goal ≠ readBit (witnesses i).2 goal ∧
    ∀ j : Fin 8, readBit (witnesses i).1 (roots.get j) =
      readBit (witnesses i).2 (roots.get j) ∨ j = i := by decide +kernel

theorem roots_full {b n S} (live : Live b n S) (sub : S ⊆ roots.toFinset) :
    S = roots.toFinset := by
  apply Finset.Subset.antisymm sub
  intro x hx
  obtain ⟨i,rfl⟩ := List.mem_iff_get.mp (List.mem_toFinset.mp hx)
  obtain ⟨distinct,only⟩ := witness_correct i
  by_contra missing
  apply distinct (live_agrees live _ _ ?_)
  intro w hw
  obtain ⟨j,rfl⟩ := List.mem_iff_get.mp (List.mem_toFinset.mp (sub hw))
  exact (only j).resolve_right (by rintro rfl; exact missing hw)

theorem cost_bound (gs : List Gate) : binaryCount gs + inversionCount gs ≤ gs.length := by
  induction gs with
  | nil => simp [binaryCount,inversionCount]
  | cons g gs ih =>
    have hg : binCost g + invCost g ≤ 1 := by
      rcases g with ⟨op,ins⟩
      cases op <;> cases ins with
      | nil => simp [binCost,invCost]
      | cons i tail => cases tail <;> simp [binCost,invCost]
    simp only [binaryCount,inversionCount,List.length_cons]
    omega

theorem zero_inversions (gs : List Gate) (none : ∀ g ∈ gs, g.op ≠ .not) :
    inversionCount gs = 0 := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    have ng := none g (by simp)
    have cost : invCost g = 0 := by rcases g with ⟨op,ins⟩; cases op <;> simp_all [invCost]
    rw [inversionCount,cost,ih (by grind),Nat.add_zero]

theorem unique_inversion (gs : List Gate)
    (uniq : ∀ i j : Fin gs.length, (gs.get i).op = .not → (gs.get j).op = .not → i=j) :
    inversionCount gs ≤ 1 := by
  induction gs with
  | nil => decide
  | cons g gs ih =>
    by_cases head : g.op = .not
    · have none (x : Gate) (hx : x ∈ gs) : x.op ≠ .not := by
        obtain ⟨j,rfl⟩ := List.mem_iff_get.mp hx
        intro nj
        have eq := uniq ⟨0,by simp⟩ j.succ head nj
        have e := congrArg Fin.val eq
        simp at e
      have one : invCost g = 1 := by simp [invCost,head]
      rw [inversionCount,zero_inversions gs none,one]
    · have zero : invCost g = 0 := by rcases g with ⟨op,ins⟩; cases op <;> simp_all [invCost]
      rw [inversionCount,zero,Nat.add_zero]
      apply ih
      intro i j ni nj
      exact Fin.succ_injective _ (uniq i.succ j.succ ni nj)

theorem full_chain (gates : List Gate) (out : Nat)
    (legal : ∀ g ∈ gates, allowed g)
    (uniq : ∀ i j : Fin gates.length, (gates.get i).op = .not → (gates.get j).op = .not → i=j)
    (correct : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates,out⟩ (List.ofFn x) = graph x) :
    ∃ b n, b+n ≤ gates.length ∧ n ≤ 1 ∧ Live b n roots.toFinset := by
  obtain ⟨b,hb,n,hn,S,sub,live⟩ := circuit_live ⟨gates,out⟩ legal correct
  rw [roots_full live sub] at live
  exact ⟨b,n,(Nat.add_le_add hb hn).trans (cost_bound gates),hn.trans (unique_inversion gates uniq),live⟩

theorem has_inversion_cost (gates : List Gate) (hasNot : ∃ g ∈ gates, g.op = .not) :
    1 ≤ inversionCount gates := by
  induction gates with
  | nil => simp at hasNot
  | cons g gs ih =>
    by_cases top : g.op = .not
    · simp [inversionCount, invCost, top]
    · obtain ⟨f,hf,inv⟩ := hasNot
      have hin : f ∈ gs := (List.mem_cons.mp hf).resolve_left (fun eq => top (eq ▸ inv))
      have tail := ih ⟨f,hin,inv⟩
      rw [inversionCount]
      omega

theorem signed_chain {gates : List Gate} {out : Nat}
    (legal : ∀ g ∈ gates, allowed g)
    (uniq : ∀ i j : Fin gates.length, (gates.get i).op = .not → (gates.get j).op = .not → i=j)
    (correct : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates,out⟩ (List.ofFn x) = graph x)
    (hasNot : ∃ g ∈ gates, g.op = .not) :
    ∃ b n, b+1 ≤ gates.length ∧ n ≤ 1 ∧ Live b n roots.toFinset := by
  obtain ⟨b,hb,n,hn,S,sub,live⟩ := circuit_live ⟨gates,out⟩ legal correct
  rw [roots_full live sub] at live
  exact ⟨b,n,(Nat.add_le_add hb (has_inversion_cost gates hasNot)).trans (cost_bound gates),
    hn.trans (unique_inversion gates uniq),live⟩

def counted (g : Gate) : Bool := match g.op with | .not => false | _ => true

theorem binaryCount_le_countP (gs : List Gate) :
    binaryCount gs ≤ gs.countP counted := by
  induction gs with
  | nil => simp [binaryCount]
  | cons g gs ih =>
    have cap : binCost g ≤ (counted g).toNat := by
      obtain ⟨op, inputs⟩ := g
      cases op <;> cases inputs with
      | nil => simp [binCost, counted]
      | cons a rest => cases rest <;> simp [binCost, counted]
    rw [binaryCount, List.countP_cons]
    cases h : counted g <;> simp [h] at cap ⊢ <;> omega

theorem circuit_chain (gs : List Gate) (o : Nat)
    (legal : FanInTwo ⟨gs,o⟩)
    (correct : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = Frame.target x) :
    ∃ b n, b ≤ gs.countP counted ∧ Live b n roots.toFinset := by
  obtain ⟨b,hb,n,_,S,sub,live⟩ := circuit_live ⟨gs,o⟩ legal correct
  rw [roots_full live sub] at live
  exact ⟨b,n,hb.trans (binaryCount_le_countP gs),live⟩

theorem freely_chain (gs : List Gate) (o : Nat)
    (legal : FanInTwo ⟨gs,o⟩)
    (correct : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = Frame.target x)
    (hasNot : ∃ g ∈ gs, g.op = .not) :
    ∃ b n, b+1 ≤ gs.length ∧ Live b n roots.toFinset := by
  obtain ⟨b,hb,n,_,S,sub,live⟩ := circuit_live ⟨gs,o⟩ legal correct
  rw [roots_full live sub] at live
  exact ⟨b,n,(Nat.add_le_add hb (has_inversion_cost gs hasNot)).trans (cost_bound gs),live⟩

end PEqualNP.Outside.L_meta_28330

namespace PEqualNP.Outside.L_meta_28330.Reduce
open PEqualNP.Outside.L_meta_28330

def half (b : Bool) (w : Word) : BitVec 128 :=
  if b then w.extractLsb' 128 128 else w.extractLsb' 0 128
def pin128 (b : Bool) (w : Word) := canon (half b w)
def lit : Word := 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000
def literal (w : Word) := w = lit ∨ w = ~~~lit
def indep (w : Word) := half false w = half true w
def safe (w : Word) : Prop := literal w ∨ indep w ∧ pin128 false w ≠ 0

theorem half_not (b : Bool) (v : Word) : half b (~~~v) = ~~~half b v := by
  cases b <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj <;>
    simp [half,BitVec.getLsbD_not,hj,show 128+j < 256 by omega,show j < 256 by omega]
theorem half_and (b : Bool) (v w : Word) : half b (v &&& w) = half b v &&& half b w := by
  cases b <;> exact BitVec.extractLsb'_and
theorem half_or (b : Bool) (v w : Word) : half b (v ||| w) = half b v ||| half b w := by
  cases b <;> exact BitVec.extractLsb'_or
theorem indep_nz (w : Word) (h : indep w) (hp : w ≠ 0 ∧ w ≠ ones) : pin128 false w ≠ 0 := by
  change half false w = half true w at h
  have rebuild : half true w ++ half false w = w := BitVec.extractLsb'_append_extractLsb'
  rw [←h] at rebuild
  unfold pin128 canon
  intro bad
  split at bad
  · have both := congrArg (fun x : BitVec 128 => ~~~x) bad
    simp only [BitVec.not_not,BitVec.not_zero] at both
    rw [both] at rebuild
    exact hp.2 (rebuild.symm.trans (by decide))
  · rw [bad] at rebuild
    exact hp.1 (rebuild.symm.trans (by decide))

theorem safe_not (v : Word) (h : safe v) : safe (~~~v) := by
  rcases h with (rfl|rfl)|⟨e,q⟩
  · exact Or.inl (Or.inr rfl)
  · exact Or.inl (Or.inl BitVec.not_not)
  · right
    exact ⟨by simpa only [indep,half_not] using congrArg (fun t => ~~~t) e,
      by simpa only [pin128,half_not,canon_not] using q⟩
theorem indep_join (d : Bool) {a b : Word} (ha : indep a) (hb : indep b) :
    indep (join d a b) := by
  unfold indep at *
  cases d <;> simp [join,half_or,half_and,ha,hb]
theorem p128neg (b : Bool) (w : Word) : pin128 b (~~~w) = pin128 b w := by
  simp [pin128,half_not,canon_not]
theorem p128repr (e d : Bool) (a b : Word) :
    ∃ s t, pin128 e (join d a b) = gate s t (pin128 e a) (pin128 e b) := by
  cases d
  · exact ⟨(half e a).getLsbD 0,(half e b).getLsbD 0,by simp only [pin128,gate,sign_back]; exact congrArg canon (half_and _ _ _)⟩
  · refine ⟨(~~~(half e a)).getLsbD 0,(~~~(half e b)).getLsbD 0,?_⟩
    unfold gate pin128
    rw [←canon_not (half e a),←canon_not (half e b),sign_back,sign_back,←BitVec.not_or,canon_not]
    exact congrArg canon (half_or _ _ _)
theorem pin128goal (e : Bool) : pin128 e goal ≠ 0 := by cases e <;> decide +kernel
theorem ordinary {b n S} (h : Live b n S) (e : Bool) : Proj (pin128 e) (pin128 e goal) b 0 S := by
  induction h using Live.recPlain with
  | done => exact proj_done _ _ (pin128goal _)
  | @inversion b n a U fresh proper tail ih =>
    exact proj_inv _ _ _ _ (fun h => fresh (by simp [h])) (p128neg e a) ih
  | @binary b n a x U d ne fresh proper tail ih =>
    obtain ⟨s,t,rep⟩ := p128repr e d a x
    exact proj_bin _ _ _ _ _ (fun v => canon_canon _) (fun h => fresh (by simp [h])) s t rep ih

theorem choose_kill (d : Bool) (v w : Word) (h : literal v) :
    ∃ e, pin128 e (join d v w) = 0 := by
  rcases h with rfl|rfl <;> cases d
  · exact ⟨false,by rw [pin128,show join false lit w = lit &&& w from rfl,half_and,show half false lit = 0 by decide]; simp only [show ∀ v : BitVec 128, (0 : BitVec 128) &&& v = 0 from fun v => BitVec.zero_and]; decide⟩
  · exact ⟨true,by rw [pin128,show join true lit w = lit ||| w from rfl,half_or,show half true lit = BitVec.allOnes 128 by decide,BitVec.allOnes_or]; decide⟩
  · exact ⟨true,by rw [pin128,show join false (~~~lit) w = (~~~lit) &&& w from rfl,half_and,show half true (~~~lit) = 0 by decide]; simp only [show ∀ v : BitVec 128, (0 : BitVec 128) &&& v = 0 from fun v => BitVec.zero_and]; decide⟩
  · exact ⟨false,by rw [pin128,show join true (~~~lit) w = (~~~lit) ||| w from rfl,half_or,show half false (~~~lit) = BitVec.allOnes 128 by decide,BitVec.allOnes_or]; decide⟩
theorem nz_else {w : Word} (h : indep w) (nz : pin128 false w ≠ 0) (e : Bool) : pin128 e w ≠ 0 := by
  cases e
  · exact nz
  · change half false w = half true w at h
    simpa only [pin128,←h] using nz
theorem impossible_lits (d : Bool) (a x : Word) (ha : literal a) (hx : literal x)
    (ne : a ≠ x) (proper : join d a x ≠ 0 ∧ join d a x ≠ ones) : False := by
  rcases ha with rfl|rfl <;> rcases hx with rfl|rfl <;> cases d <;>
    first | exact ne rfl | exact proper.1 (by decide) | exact proper.2 (by decide)
theorem join_comm (d : Bool) (a b : Word) : join d a b = join d b a := by
  cases d <;> simp [join,BitVec.and_comm,BitVec.or_comm]

theorem chooseFirst {b n S} (h : Live b n S) :
    (∀ v ∈ S, safe v) → ∃ e, Proj (pin128 e) (pin128 e goal) b 1 S := by
  induction h using Live.recPlain with
  | done =>
    intro ok
    exact (show ¬ safe goal by unfold safe literal indep; decide +kernel) (ok _ (by simp)) |>.elim
  | @inversion b n a U fresh proper tail ih =>
    intro ok
    have ta : ∀ v ∈ insert (~~~a) U, safe v := by
      intro v hv
      rcases Finset.mem_insert.mp hv with rfl|vU
      · exact safe_not a (ok a (by simp))
      · exact ok v (by simp [vU])
    obtain ⟨e,good⟩ := ih ta
    exact ⟨e,proj_inv _ _ _ _ (fun h => fresh (by simp [h])) (p128neg e a) good⟩
  | @binary b n a x U d ne fresh proper tail ih =>
    intro ok
    have freshU : join d a x ∉ U := fun h => fresh (by simp [h])
    rcases ok a (by simp) with ha|⟨ea,na⟩ <;> rcases ok x (by simp) with hx|⟨ex,nx⟩
    · exact (impossible_lits d a x ha hx ne proper).elim
    · obtain ⟨e,kill⟩ := choose_kill d a x ha
      exact ⟨e,proj_strong _ _ _ _ _ freshU kill (Or.inr (nz_else ex nx e)) (ordinary tail e)⟩
    · obtain ⟨e,kill⟩ := choose_kill d x a hx
      rw [join_comm d x a] at kill
      exact ⟨e,proj_strong _ _ _ _ _ freshU kill (Or.inl (nz_else ea na e)) (ordinary tail e)⟩
    · have ec := indep_join d ea ex
      have ta : ∀ v ∈ insert (join d a x) U, safe v := by
        intro v hv
        rcases Finset.mem_insert.mp hv with rfl|vU
        · exact Or.inr ⟨ec,indep_nz _ ec proper⟩
        · exact ok v (by simp [vU])
      obtain ⟨e,good⟩ := ih ta
      obtain ⟨s,t,rep⟩ := p128repr e d a x
      exact ⟨e,proj_bin _ _ _ _ _ (fun v => canon_canon _) freshU s t rep good⟩
end PEqualNP.Outside.L_meta_28330.Reduce

namespace PEqualNP.Outside.L_meta_28330.Reduce
open PEqualNP.Outside.L_meta_28330

def sixPin (w : BitVec 128) : BitVec 64 := canon (w.setWidth 64)
theorem sixPin_not (w : BitVec 128) : sixPin (~~~w) = sixPin w := by
  unfold sixPin; rw [BitVec.setWidth_not (by decide),canon_not]
theorem sixPin_canon (w : BitVec 128) : sixPin (canon w) = sixPin w := by
  by_cases h : w.getLsbD 0 = true
  · rw [show canon w = ~~~w from if_pos h,sixPin_not]
  · rw [show canon w = w from if_neg h]
theorem sixPin_signed (s : Bool) (w : BitVec 128) : sixPin (signed s w) = sixPin w := by
  cases s; rfl; exact sixPin_not _
theorem six_repr (s t : Bool) (a b : BitVec 128) :
    ∃ u v, sixPin (gate s t a b) = gate u v (sixPin a) (sixPin b) := by
  let x := signed s a; let y := signed t b
  change ∃ u v, sixPin (canon (x &&& y)) = gate u v (sixPin a) (sixPin b)
  rw [sixPin_canon,← sixPin_signed s a,← sixPin_signed t b]
  refine ⟨(x.setWidth 64).getLsbD 0,(y.setWidth 64).getLsbD 0,?_⟩
  change canon ((x &&& y).setWidth 64) = gate ((x.setWidth 64).getLsbD 0) ((y.setWidth 64).getLsbD 0) (canon (x.setWidth 64)) (canon (y.setWidth 64))
  simp only [gate,sign_back]; exact congrArg canon BitVec.setWidth_and
theorem second {g : BitVec 128} {k S} (h : Path g k S) (nz : sixPin g ≠ 0) :
    Proj sixPin (sixPin g) k 0 S := by
  apply h (fun k S => Proj sixPin (sixPin g) k 0 S) (proj_done _ _ nz)
  intro j a b U s t ne fresh proper tail
  obtain ⟨u,v,rep⟩ := six_repr s t a b
  exact proj_bin _ _ _ _ _ (fun w => canon_canon _) (fun q => fresh (by simp [q])) u v rep tail

def sevenRaw : List (BitVec 128) := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000]
def cliqueRaw : List (BitVec 64) := [0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000]
def cliqueGoal : BitVec 64 := 0xfffffffefffeee00
theorem path_equal {m : Nat} {g : BitVec (m+1)} {k S} (h : Path g k S) (p q : Fin (m+1))
    (same : ∀ x ∈ S, x.getLsbD p = x.getLsbD q) : g.getLsbD p = g.getLsbD q := by
  apply h (fun _ T => (∀ x ∈ T, x.getLsbD p = x.getLsbD q) → g.getLsbD p = g.getLsbD q) ?_ ?_ same
  · exact fun h => h _ (by simp)
  · intro i a b U s t ne fresh proper ih eq
    apply ih; intro w hw; rcases Finset.mem_insert.mp hw with rfl|old
    · have ea := eq a (by simp); have eb := eq b (by simp); unfold gate canon
      split <;> cases s <;> cases t <;> simp only [signed,Bool.false_eq_true,reduceIte,BitVec.getLsbD_not,BitVec.getLsbD_and,decide_eq_true p.isLt,decide_eq_true q.isLt,ea,eb]
    · exact eq _ (by simp [old])
def sevenPairs (e : Bool) (v : Fin 7) : Fin 128 × Fin 128 :=
  if e then ([(8,9),(8,10),(16,20),(1,9),(0,64),(1,17),(1,33)] : List _).get v
  else ([(8,9),(8,10),(16,20),(1,9),(1,65),(1,17),(1,33)] : List _).get v
theorem exclusive7 : ∀ e (i : Fin 7),
    (pin128 e goal).getLsbD (sevenPairs e i).1 ≠ (pin128 e goal).getLsbD (sevenPairs e i).2 ∧
    ∀ j : Fin 7, (sevenRaw.get j).getLsbD (sevenPairs e i).1 = (sevenRaw.get j).getLsbD (sevenPairs e i).2 ∨ j = i := by decide +kernel
theorem seven_full {e k T} (hp : Path (pin128 e goal) k T) (sub : T ⊆ sevenRaw.toFinset) :
    T = sevenRaw.toFinset := by
  apply Finset.Subset.antisymm sub; intro x hx
  obtain ⟨i,rfl⟩ := List.mem_iff_get.mp (List.mem_toFinset.mp hx)
  obtain ⟨distinct,only⟩ := exclusive7 e i; by_contra missing
  apply distinct (path_equal hp _ _ ?_); intro w hw
  obtain ⟨j,rfl⟩ := List.mem_iff_get.mp (List.mem_toFinset.mp (sub hw))
  exact (only j).resolve_right (by rintro rfl; exact missing hw)
theorem to_six {b n} (h : Live b n roots.toFinset) :
    ∃ k, k+3 ≤ b ∧ ∃ T ⊆ cliqueRaw.toFinset, Path cliqueGoal k T := by
  have ok : ∀ v ∈ roots.toFinset, safe v := by
    simp only [List.mem_toFinset,roots,List.mem_cons,List.not_mem_nil,or_false]
    intro v hv; rcases hv with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> unfold safe literal indep <;> decide +kernel
  obtain ⟨e,k,hk,T,sub,hp⟩ := chooseFirst h ok
  have av : avail (pin128 e) roots.toFinset = sevenRaw.toFinset := by cases e <;> decide +kernel
  have ls : lost (pin128 e) roots.toFinset = 1 := by cases e <;> decide +kernel
  rw [av] at sub; rw [seven_full hp sub] at hp
  have geq : sixPin (pin128 e goal) = cliqueGoal := by cases e <;> decide +kernel
  have nz : sixPin (pin128 e goal) ≠ 0 := by rw [geq]; decide
  obtain ⟨j,hj,U,sub6,hr⟩ := second hp nz
  have av6 : avail sixPin sevenRaw.toFinset = cliqueRaw.toFinset := by decide +kernel
  have ls6 : lost sixPin sevenRaw.toFinset = 1 := by decide +kernel
  rw [av6] at sub6; rw [geq] at hr; exact ⟨j,by omega,U,sub6,hr⟩
end PEqualNP.Outside.L_meta_28330.Reduce

namespace PEqualNP.Outside.L_meta_28330.ArchivedClique
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
abbrev Wire := Bool × ℕ
def zero : Wire := (false,0)
def flip (a : Wire) : Wire := (!a.1,a.2)
def combine (d a b : ℕ) : ℕ :=
  match d with
  | 0 => a &&& b
  | 1 => a ||| b
  | 2 => a ^^^ (a &&& b)
  | _ => b ^^^ (a &&& b)
def opIndex (a b : Bool) : ℕ :=
  if a then (if b then 1 else 3) else (if b then 2 else 0)
def meet (a b : Wire) : Wire := (a.1 && b.1,combine (opIndex a.1 b.1) a.2 b.2)
def join (a b : Wire) : Wire := flip (meet (flip a) (flip b))
def read (j : ℕ) (a : Wire) : Bool := a.1 != a.2.testBit j
lemma read_zero (j : ℕ) : read j zero=false := by simp [read,zero]
lemma read_flip (j : ℕ) (a : Wire) : read j (flip a)=!(read j a) := by
  cases a with | mk s a => cases s <;> cases h : a.testBit j <;> simp [read,flip,h]
lemma read_meet (j : ℕ) (a b : Wire) : read j (meet a b) = (read j a && read j b) := by
  obtain ⟨s,a⟩ := a;obtain ⟨t,b⟩ := b
  cases s <;> cases t <;> cases h : a.testBit j <;> cases g : b.testBit j <;>
    simp [read,meet,combine,opIndex,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,h,g]
lemma read_join (j : ℕ) (a b : Wire) : read j (join a b) = (read j a || read j b) := by
  simp only [join,read_flip,read_meet];cases read j a <;> cases read j b <;> rfl

def gate (w : List Wire) (g : Gate) : Wire :=
  let arg := fun i => w.getD i zero
  match g.op,g.inputs with
  | .not, xs => flip (arg (xs.headD w.length))
  | .and, [] => flip zero
  | .or, [] => zero
  | .and, [i] | .or, [i] => arg i
  | .and, i::j::_ => meet (arg i) (arg j)
  | .or, i::j::_ => join (arg i) (arg j)
  | _,_ => zero
def execute (gs : List Gate) (w : List Wire) : List Wire :=
  gs.foldl (fun w g => w++[gate w g]) w
def boolRun (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w++[g.op.eval (g.inputs.map fun i => w.getD i false)]) w
lemma read_get (j : ℕ) (w : List Wire) (i : ℕ) :
    (w.map (read j)).getD i false = read j (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases h : w[i]? with
  | none => exact (read_zero j).symm
  | some a => rfl
lemma gate_read (w : List Wire) (g : Gate) (legal : g.op ∈ ({.and,.or,.not} : Set GateOp) ∧ g.inputs.length ≤ 2) (j : ℕ) :
    read j (gate w g) = g.op.eval (g.inputs.map fun i => (w.map (read j)).getD i false) := by
  simp_rw [read_get]
  obtain ⟨op,xs⟩ := g
  obtain ⟨ops,len⟩ := legal
  change op ∈ ({.and,.or,.not} : Set GateOp) at ops
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at ops
  rcases ops with rfl|rfl|rfl <;>
    rcases xs with _|⟨i,_|⟨k,_|⟨h,rest⟩⟩⟩ <;>
    simp_all [gate,GateOp.eval,read_flip,read_meet,read_join,read_get,read_zero,List.getD_eq_default]
lemma execute_read (j : ℕ) (gs : List Gate) (w : List Wire) (legal : ∀ g ∈ gs,
    g.op ∈ ({.and,.or,.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    (execute gs w).map (read j) = boolRun gs (w.map (read j)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (execute gs (w++[gate w g])).map (read j) = boolRun gs (_++[_])
    rw [ih _ (fun v hv => legal v (.tail _ hv))]
    simp [gate_read w g (legal g List.mem_cons_self) j]

def counted (g : Gate) : Bool := match g.op with | .not => false | _ => true
def reps (w : List Wire) := w.map Prod.snd
def simple (w : List Wire) (z : ℕ) := z=0 ∨ z∈reps w
def priced (w : List Wire) (paid : Bool) (z : ℕ) := simple w z ∨
    (paid = true ∧ ∃ d < 4, ∃ a ∈ reps w, ∃ b ∈ reps w, a≠0 ∧ b≠0 ∧ a≠b ∧ z=combine d a b)
lemma get_simple (w : List Wire) (i : ℕ) : simple w (w.getD i zero).2 := by
  simp only [List.getD_eq_getElem?_getD]
  cases eq : w[i]? with
  | none => exact Or.inl rfl
  | some a => exact Or.inr (List.mem_map.mpr ⟨a,List.mem_of_getElem? eq,rfl⟩)
lemma combine_eq_cases (d a b : ℕ) (hd : d<4) (h : a=0 ∨ b=0 ∨ a=b) :
    combine d a b=0 ∨ combine d a b=a ∨ combine d a b=b := by
  rcases h with h|h|h <;> subst_vars <;> interval_cases d <;> simp [combine]
lemma made (w : List Wire) (d : ℕ) (a b : Wire) (hd : d<4) (pa : simple w a.2) (pb : simple w b.2) :
    priced w true (combine d a.2 b.2) := by
  by_cases h : a.2=0 ∨ b.2=0 ∨ a.2=b.2
  · rcases combine_eq_cases _ _ _ hd h with e|e|e
    · exact Or.inl (Or.inl e)
    · apply Or.inl; rw [e]; exact pa
    · apply Or.inl; rw [e]; exact pb
  · push Not at h
    exact Or.inr ⟨rfl,d,hd,a.2,pa.resolve_left h.1,b.2,pb.resolve_left h.2.1,h.1,h.2.1,h.2.2,rfl⟩
lemma op_lt (s t : Bool) : opIndex s t < 4 := by cases s <;> cases t <;> decide
lemma gate_priced (w : List Wire) (g : Gate) : priced w (counted g) (gate w g).2 := by
  obtain ⟨op,xs⟩ := g
  cases op with
  | and =>
    rcases xs with _|⟨i,_|⟨j,t⟩⟩
    · exact Or.inl (Or.inl rfl)
    · exact Or.inl (get_simple w i)
    · exact made w _ _ _ (op_lt _ _) (get_simple w i) (get_simple w j)
  | or =>
    rcases xs with _|⟨i,_|⟨j,t⟩⟩
    · exact Or.inl (Or.inl rfl)
    · exact Or.inl (get_simple w i)
    · exact made w _ _ _ (op_lt _ _) (get_simple w i) (get_simple w j)
  | mod _ | maj => exact Or.inl (Or.inl rfl)
  | _ => exact Or.inl (get_simple w _)

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def Good (m a : ℕ) := ∀ i<m, a.testBit i ≠ a.testBit (m+i)

def Live (m : ℕ) : ℕ → Finset ℕ → Prop
  | 0, S => ∃ a, S = {a} ∧ Good m a ∧ a ≠ 0
  | k+1, S => ∃ (U : Finset ℕ) (a b d : ℕ),
      S = insert a (insert b U) ∧
      d < 4 ∧ a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b ∧
      combine d a b ∉ insert a (insert b U) ∧
      Live m k (insert (combine d a b) U)

namespace Live

lemma done {m a : ℕ} (hg : Good m a) (nonzero : a ≠ 0) : Live m 0 {a} := by
  rw [Live]
  exact ⟨a, rfl, hg, nonzero⟩

lemma step {m k : ℕ} {U : Finset ℕ} {a b d : ℕ}
    (hd : d < 4) (ha : a ≠ 0) (hb : b ≠ 0) (diff : a ≠ b)
    (fresh : combine d a b ∉ insert a (insert b U))
    (next : Live m k (insert (combine d a b) U)) :
    Live m (k+1) (insert a (insert b U)) := by
  rw [Live]
  exact ⟨U, a, b, d, rfl, hd, ha, hb, diff, fresh, next⟩

end Live

lemma liveNonzero {m k S} (h : Live m k S) : ∀ a∈S,a≠0 := by
  induction k generalizing S with
  | zero =>
    rw [Live] at h
    obtain ⟨a, rfl, _, hn⟩ := h
    simpa using hn
  | succ k ih =>
    rw [Live] at h
    obtain ⟨U, a, b, d, rfl, _, ha, hb, _, _, tail⟩ := h
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl|hx
    · exact ha
    rcases Finset.mem_insert.mp hx with rfl|hx
    · exact hb
    exact ih tail x (Finset.mem_insert_of_mem hx)
lemma liveSize {m k S} (h : Live m k S) : S.card≤k+1 := by
  induction k generalizing S with
  | zero =>
    rw [Live] at h
    obtain ⟨a, rfl, _, _⟩ := h
    simp
  | succ k ih =>
    rw [Live] at h
    obtain ⟨U, a, b, d, rfl, _, _, _, _, fresh, tail⟩ := h
    have bound := ih tail
    have z : combine d a b ∉ U := fun m => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem m))
    rw [Finset.card_insert_of_notMem z] at bound
    have u := Finset.card_insert_le a (insert b U)
    have v := Finset.card_insert_le b U
    omega
lemma combine_congr_bits (d a b i j : ℕ) (p : a.testBit i=a.testBit j) (q : b.testBit i=b.testBit j) :
    (combine d a b).testBit i=(combine d a b).testBit j := by
  rcases d with _|(_|(_|d)) <;> simp [combine,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,p,q]
lemma liveSeparates {m k S} (h : Live m k S) (i : ℕ) (hi : i<m) :
    ∃ a∈S,a.testBit i≠a.testBit (m+i) := by
  induction k generalizing S with
  | zero =>
    rw [Live] at h
    obtain ⟨a, rfl, hg, _⟩ := h
    exact ⟨a, Finset.mem_singleton_self a, hg i hi⟩
  | succ k ih =>
    rw [Live] at h
    obtain ⟨U, a, b, d, rfl, _, _, _, _, _, tail⟩ := h
    obtain ⟨x,hx,dist⟩ := ih tail
    rcases Finset.mem_insert.mp hx with rfl|hx
    · by_cases v : a.testBit i=a.testBit (m+i)
      · exact ⟨b,Finset.mem_insert_of_mem (Finset.mem_insert_self _ _),fun u => dist (combine_congr_bits _ _ _ _ _ v u)⟩
      · exact ⟨a,Finset.mem_insert_self _ _,v⟩
    · exact ⟨x,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx),dist⟩

lemma pull {m k S w z p} (h : Live m k S) (op : priced w p z)
    (sub : ∀ a∈S, a∈reps w ++ [z]) :
    ∃ l T, l ≤ k + p.toNat ∧ Live m l T ∧ ∀ a∈T, a∈reps w := by
  by_cases needed : z∈S
  · by_cases available : z∈reps w
    · refine ⟨k,S,by omega,h,?_⟩
      intro a ha
      rcases (by simpa using sub a ha : a∈reps w ∨ a=z) with old|rfl
      · exact old
      · exact available
    · rcases op with easy|⟨rfl,d,hd,a,xa,b,xb,na,nb,ab,rfl⟩
      · rcases easy with e|e
        · exact ((liveNonzero h z needed) e).elim
        · exact (available e).elim
      · let g := combine d a b
        let U := S.erase g
        have tail : Live m k (insert g U) := by change Live m k (insert g (S.erase g)); rw [Finset.insert_erase (show g∈S from needed)]; exact h
        have old (x : ℕ) (hx : x∈U) : x∈reps w := by
          obtain ⟨ne,mem⟩ := Finset.mem_erase.mp hx
          have h' : x∈reps w ∨ x=g := by simpa using sub x mem
          exact h'.resolve_right ne
        have fresh : g ∉ insert a (insert b U) := by
          intro eq
          rcases Finset.mem_insert.mp eq with e|h'
          · exact available (show g∈reps w by rw [e];exact xa)
          rcases Finset.mem_insert.mp h' with e|u
          · exact available (show g∈reps w by rw [e];exact xb)
          · exact available (old _ u)
        refine ⟨k+1,insert a (insert b U),by simp,Live.step hd na nb ab fresh tail,?_⟩
        simpa using And.intro xa (And.intro xb old)
  · refine ⟨k,S,by omega,h,?_⟩
    intro a ha
    have ne : a≠z := fun e => needed (e ▸ ha)
    simpa [ne] using sub a ha

lemma extract {m out} (hg : Good m out) (hn : out≠0) (gs : List Gate) (w : List Wire)
    (found : out∈reps (execute gs w)) :
    ∃ k S, k≤gs.countP counted ∧ Live m k S ∧ ∀ a∈S, a∈reps w := by
  induction gs generalizing w with
  | nil => exact ⟨0,{out},by simp,Live.done hg hn,by simpa [execute] using found⟩
  | cons g gs ih =>
    obtain ⟨k,S,lim,h,sub⟩ := ih (w++[gate w g]) found
    have sub' : ∀ a∈S,a∈reps w ++ [(gate w g).2] := by simpa [reps] using sub
    obtain ⟨l,T,cost,ht,raw⟩ := pull h (gate_priced w g) sub'
    refine ⟨l,T,?_,ht,raw⟩
    cases e : counted g <;> simp [e,Bool.toNat] at cost ⊢ <;> omega
def separation (m a : ℕ) := a ^^^ (a >>> m)
def cover (m : ℕ) : List ℕ → ℕ
  | [] => 0
  | a::t => separation m a ||| cover m t
def full (m : ℕ) := (1 <<< m)-1
def enough (m c : ℕ) := (c &&& full m) == full m
lemma coverBit (m i : ℕ) (v : List ℕ) : (cover m v).testBit i=true ↔
    ∃ a∈v,a.testBit i≠a.testBit (m+i) := by
  induction v with
  | nil => simp [cover]
  | cons a t ih =>
    simp only [cover,Nat.testBit_or,Bool.or_eq_true,ih,List.mem_cons,separation,Nat.testBit_xor,Nat.testBit_shiftRight]
    cases v1 : a.testBit i <;> cases v2 : a.testBit (m+i) <;> simp [v1,v2] <;> aesop
lemma enoughLive {m k S} (h : Live m k S) (v : List ℕ) (rep : v.toFinset=S) : enough m (cover m v)=true := by
  apply beq_iff_eq.mpr
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  have bit : (full m).testBit i=decide (i<m) := by simp [full,Nat.shiftLeft_eq,Nat.testBit_two_pow_sub_one]
  by_cases hi : i<m
  · have ⟨x,hx,good⟩ := liveSeparates h i hi
    have xc : x∈v := List.mem_toFinset.mp (rep ▸ hx)
    have mark := (coverBit m i v).2 ⟨x,xc,good⟩
    simp [mark,bit,hi]
  · simp [bit,hi]

def save (keep : Bool) (a : ℕ) (rest : List ℕ) := if keep then a::rest else rest
def without (v : List ℕ) (a b : ℕ) := v.filter (fun x => x != a && x != b)
def optionStep (m fuel : ℕ) (go : List ℕ → Bool) (rest : List ℕ) (n cv a b z : ℕ) (ka kb : Bool) : Bool :=
  let len := 1+n+ka.toNat+kb.toNat
  len ≤ fuel+1 && enough m (((separation m z ||| cv) ||| (if ka then separation m a else 0)) |||
    (if kb then separation m b else 0)) && go (z::save ka a (save kb b rest))
def gateStep (m fuel : ℕ) (go : List ℕ → Bool) (v rest : List ℕ) (n cv a b z : ℕ) : Bool :=
  z != 0 && !(v.contains z) &&
  (optionStep m fuel go rest n cv a b z false false || optionStep m fuel go rest n cv a b z true false ||
   optionStep m fuel go rest n cv a b z false true || optionStep m fuel go rest n cv a b z true true)
def pairStep (m fuel : ℕ) (go : List ℕ → Bool) (v : List ℕ) (a b : ℕ) : Bool :=
  if a<b then
    let rest := without v a b
    let check := gateStep m fuel go v rest rest.length (cover m rest) a b
    check (a &&& b) || check (a ||| b) || check (a ^^^ (a &&& b)) || check (b ^^^ (a &&& b))
  else false
def anyGate (m fuel : ℕ) (go : List ℕ → Bool) (v : List ℕ) : Bool :=
  v.any (fun a => v.any (fun b => pairStep m fuel go v a b))
def terminal (m : ℕ) (v : List ℕ) := v.any (fun a => enough m (separation m a))
def search (m : ℕ) : ℕ → List ℕ → Bool
  | 0, v => terminal m v
  | fuel+1, v => terminal m v || anyGate m fuel (search m fuel) v

lemma surface (m a i : ℕ) : (separation m a).testBit i=true ↔ a.testBit i≠a.testBit (m+i) := by
  simp only [separation,Nat.testBit_xor,Nat.testBit_shiftRight]
  cases a.testBit i <;> cases a.testBit (m+i) <;> decide
lemma ends {m a} (h : Good m a) (v : List ℕ) (mem : a∈v) : terminal m v=true := by
  apply List.any_eq_true.mpr;refine ⟨a,mem,?_⟩
  apply beq_iff_eq.mpr;apply Nat.eq_of_testBit_eq;intro i;rw [Nat.testBit_and]
  have e : (full m).testBit i=decide (i<m) := by simp [full,Nat.shiftLeft_eq,Nat.testBit_two_pow_sub_one]
  by_cases l : i<m
  · simp [e,l,(surface _ _ _).2 (h i l)]
  · simp [e,l]
lemma option_ok {m fuel go rest a b z ka kb} (lim : (z::save ka a (save kb b rest)).length≤fuel+1)
    (cov : enough m (cover m (z::save ka a (save kb b rest)))=true)
    (next : go (z::save ka a (save kb b rest))=true) :
    optionStep m fuel go rest rest.length (cover m rest) a b z ka kb=true := by
  have size : 1+rest.length+ka.toNat+kb.toNat≤fuel+1 := by
    cases ka <;> cases kb <;> simp [save,Bool.toNat] at lim ⊢ <;> omega
  have eq : enough m (((separation m z ||| cover m rest) ||| (if ka then separation m a else 0)) ||| (if kb then separation m b else 0))=true := by
    cases ka <;> cases kb <;> simpa [save,cover,Nat.or_assoc,Nat.or_left_comm,Nat.or_comm] using cov
  simp [optionStep,size,eq,next]
lemma gate_ok {m fuel go v rest n cv a b z ka kb} (nz : z≠0) (fresh : z∉v)
    (which : optionStep m fuel go rest n cv a b z ka kb=true) :
    gateStep m fuel go v rest n cv a b z=true := by
  cases ka <;> cases kb <;> simp [gateStep,nz,fresh,which]
lemma pair_ok {m fuel go v a b d} (ordered : a<b) (hd : d<4)
    (step : let rest := without v a b;gateStep m fuel go v rest rest.length (cover m rest) a b (combine d a b)=true) :
    pairStep m fuel go v a b=true := by
  interval_cases d <;> simp only [combine] at step <;> simp [pairStep,ordered,step]
lemma swapOp (d a b : ℕ) (hd : d<4) : ∃ e<4,combine d a b=combine e b a := by
  interval_cases d
  · exact ⟨0,by decide,Nat.and_comm a b⟩
  · exact ⟨1,by decide,Nat.or_comm a b⟩
  · exact ⟨3,by decide,by simp [combine,Nat.and_comm]⟩
  · exact ⟨2,by decide,by simp [combine,Nat.and_comm]⟩
lemma listNext {v : List ℕ} {a b z : ℕ} {U : Finset ℕ} (rep : v.toFinset=insert a (insert b U))
    (ab : a≠b) (fz : z∉insert a (insert b U)) (nd : v.Nodup) :
    let rest := without v a b
    let next := z::save (decide (a∈U)) a (save (decide (b∈U)) b rest)
    next.toFinset=insert z U ∧ next.Nodup := by
  dsimp only
  have mem (x : ℕ) : x∈without v a b ↔ x∈U ∧ x≠a ∧ x≠b := by
    simp only [without,List.mem_filter,Bool.and_eq_true,bne_iff_ne]
    have e : x∈v ↔ x=a ∨ x=b ∨ x∈U := by rw [← List.mem_toFinset,rep];simp
    tauto
  have nr := nd.filter (fun x => x != a && x != b)
  change (without v a b).Nodup at nr
  have md (x : ℕ) : (x∈save (decide (a∈U)) a (save (decide (b∈U)) b (without v a b))) ↔ x∈U := by
    by_cases xa : x=a
    · subst x; by_cases ka : a∈U <;> by_cases kb : b∈U <;> simp [save,ka,kb,mem,ab]
    by_cases xb : x=b
    · subst x; by_cases ka : a∈U <;> by_cases kb : b∈U <;> simp [save,ka,kb,mem,Ne.symm ab]
    by_cases ka : a∈U <;> by_cases kb : b∈U <;> simp [save,ka,kb,mem,xa,xb]
  constructor
  · ext x;simp [md]
  · simp only [List.nodup_cons,md]
    refine ⟨fun m => fz (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem m)),?_⟩
    have an : a∉without v a b := fun x => (mem _).1 x |>.2.1 rfl
    have bn : b∉without v a b := fun x => (mem _).1 x |>.2.2 rfl
    by_cases ka : a∈U <;> by_cases kb : b∈U <;> simp [save,ka,kb,nr,ab,an,bn]
lemma orderedStep {m fuel n U a b d v} {go : List ℕ→Bool} (hd : d<4)
    (lt : a<b) (nz : combine d a b≠0) (fresh : combine d a b∉insert a (insert b U))
    (rep : List.toFinset v=insert a (insert b U)) (nd : v.Nodup) (lim : n≤fuel)
    (tail : Live m n (insert (combine d a b) U))
    (nextOK : ∀ v : List ℕ, v.toFinset=insert (combine d a b) U → v.Nodup → go v=true) :
    pairStep m fuel go v a b=true := by
  let z := combine d a b
  let rest := without v a b
  let next := z::save (decide (a∈U)) a (save (decide (b∈U)) b rest)
  obtain ⟨r,nu⟩ := listNext (z:=z) rep (Nat.ne_of_lt lt) fresh nd
  have small := liveSize tail
  change (insert z U).card≤n+1 at small
  have length : next.length=(insert z U).card := by rw [←r,List.toFinset_card_of_nodup nu]
  have bound : next.length≤fuel+1 := by omega
  have coverOK := enoughLive tail next r
  have ok := option_ok bound coverOK (nextOK next r nu)
  apply pair_ok lt hd
  exact gate_ok nz (fun h => fresh (rep ▸ List.mem_toFinset.mpr h)) ok
lemma transition {m fuel n U a b d v} {go : List ℕ→Bool} (hd : d<4)
    (ab : a≠b) (fresh : combine d a b∉insert a (insert b U))
    (rep : List.toFinset v=insert a (insert b U)) (nd : v.Nodup) (lim : n≤fuel)
    (tail : Live m n (insert (combine d a b) U))
    (nextOK : ∀ v : List ℕ, v.toFinset=insert (combine d a b) U → v.Nodup → go v=true) :
    anyGate m fuel go v=true := by
  have ma : a∈v := List.mem_toFinset.mp (rep ▸ Finset.mem_insert_self _ _)
  have mb : b∈v := List.mem_toFinset.mp (rep ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  have nz := liveNonzero tail _ (Finset.mem_insert_self _ _)
  rcases lt_or_gt_of_ne ab with lt|gt
  · exact List.any_eq_true.mpr ⟨a,ma,List.any_eq_true.mpr ⟨b,mb,orderedStep hd lt nz fresh rep nd lim tail nextOK⟩⟩
  · obtain ⟨e,he,eq⟩ := swapOp d a b hd
    have rev : insert a (insert b U)=insert b (insert a U) := Finset.insert_comm a b U
    rw [rev] at fresh rep
    rw [eq] at fresh nz tail nextOK
    exact List.any_eq_true.mpr ⟨b,mb,List.any_eq_true.mpr ⟨a,ma,orderedStep he gt nz fresh rep nd lim tail nextOK⟩⟩

theorem complete (m fuel : ℕ) {n S} (h : Live m n S) (lim : n≤fuel)
    (v : List ℕ) (rep : v.toFinset=S) (nd : v.Nodup) : search m fuel v=true := by
  induction fuel generalizing n S v with
  | zero =>
    cases n with
    | zero =>
      rw [Live] at h
      obtain ⟨a, rfl, hg, _⟩ := h
      exact ends hg v (List.mem_toFinset.mp (rep ▸ Finset.mem_singleton_self a))
    | succ n => omega
  | succ k ih =>
    rw [search,Bool.or_eq_true]
    cases n with
    | zero =>
      rw [Live] at h
      obtain ⟨a, rfl, hg, _⟩ := h
      exact Or.inl (ends hg v (List.mem_toFinset.mp (rep ▸ Finset.mem_singleton_self a)))
    | succ n =>
      rw [Live] at h
      obtain ⟨U, a, b, d, rfl, hd, _, _, ab, fresh, tail⟩ := h
      exact Or.inr (transition hd ab fresh rep nd (by omega) tail (fun v hv nv => ih tail (by omega) v hv nv))

abbrev Projection (m h : ℕ) := { f : ℕ → ℕ //
  f 0 = 0 ∧ (∀ d a b, d < 4 → f (combine d a b) = combine d (f a) (f b)) ∧
  (∀ a, Good m a → Good h (f a)) ∧ 0 < h }

namespace Projection
def toFun {m h : ℕ} (p : Projection m h) : ℕ → ℕ := p.val
theorem atZero {m h : ℕ} (p : Projection m h) : p.toFun 0 = 0 := p.property.1
theorem combineEq {m h : ℕ} (p : Projection m h) (d a b : ℕ) (hd : d < 4) :
    p.toFun (combine d a b) = combine d (p.toFun a) (p.toFun b) :=
  p.property.2.1 d a b hd
theorem good {m h : ℕ} (p : Projection m h) (a : ℕ) (ha : Good m a) :
    Good h (p.toFun a) := p.property.2.2.1 a ha
theorem someRow {m h : ℕ} (p : Projection m h) : 0 < h := p.property.2.2.2
end Projection

def Possible (m k : ℕ) (av : List ℕ) :=
  ∃ j S, j≤k ∧ Live m j S ∧ ∀ x∈S,x∈av
def charge (av : List ℕ) (z : ℕ) := z != 0 && !(av.contains z)
lemma pullPaid {m k d a b : ℕ} {av : List ℕ} (hd : d<4) (ha : a∈av) (hb : b∈av)
    (later : Possible m k (av++[combine d a b])) :
    Possible m (k+(charge av (combine d a b)).toNat) av := by
  let w := av.map (fun x => (false,x))
  have repr : reps w=av := by simp [w,reps,List.map_map,Function.comp_def]
  obtain ⟨j,S,lim,live,sub⟩ := later
  have needed : ∀ x∈S,x∈reps w++[combine d a b] := by simpa [repr] using sub
  have price : priced w (charge av (combine d a b)) (combine d a b) := by
    by_cases nz : combine d a b=0
    · exact Or.inl (Or.inl nz)
    by_cases old : combine d a b∈av
    · exact Or.inl (Or.inr (repr ▸ old))
    have paid : charge av (combine d a b)=true := by simp [charge,nz,old]
    have special : ¬(a=0 ∨ b=0 ∨ a=b) := by
      intro h
      rcases combine_eq_cases _ _ _ hd h with zero|rfl'|rfl'
      · exact nz zero
      · exact old (by rw [rfl'];exact ha)
      · exact old (by rw [rfl'];exact hb)
    exact Or.inr ⟨paid,d,hd,a,repr ▸ ha,b,repr ▸ hb,
      fun x => special (Or.inl x),fun x => special (Or.inr (Or.inl x)),fun x => special (Or.inr (Or.inr x)),rfl⟩
  obtain ⟨l,T,le,ok,sub'⟩ := pull live price needed
  exact ⟨l,T,by omega,ok,by simpa [repr] using sub'⟩

def dead (p : ℕ→ℕ) (S : Finset ℕ) := (S.filter (fun x => p x=0)).card
lemma deadStay {p : ℕ→ℕ} {a : ℕ} {S : Finset ℕ} (h : p a≠0) : dead p (insert a S)=dead p S := by
  simp [dead,Finset.filter_insert,h]
lemma deadLimit (p : ℕ→ℕ) (a : ℕ) (S : Finset ℕ) : dead p (insert a S)≤dead p S+1 := by
  by_cases x : p a=0
  · simpa [dead,Finset.filter_insert,x] using Finset.card_insert_le a (S.filter (fun x => p x=0))
  · simp [deadStay x]
lemma deadMono (p : ℕ→ℕ) (a : ℕ) (S : Finset ℕ) : dead p S ≤ dead p (insert a S) := by
  exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_insert _ _))
lemma deadGrow {p : ℕ→ℕ} {a : ℕ} {S : Finset ℕ} (z : p a=0) (fresh : a∉S) :
    dead p (insert a S)=dead p S+1 := by
  have nf : a∉S.filter (fun x => p x=0) := fun h => fresh (Finset.mem_filter.mp h).1
  simp [dead,Finset.filter_insert,z,Finset.card_insert_of_notMem nf]
lemma countCharge {m h d a b : ℕ} (p : Projection m h) (hd : d<4) (U : Finset ℕ)
    (fz : combine d a b∉insert a (insert b U)) (av : List ℕ) (ma : p.toFun a∈av) (mb : p.toFun b∈av) :
    (charge av (p.toFun (combine d a b))).toNat + dead p.toFun (insert a (insert b U)) ≤
      1+dead p.toFun (insert (combine d a b) U) := by
  have up := deadMono p.toFun (combine d a b) U
  have la := deadLimit p.toFun a (insert b U)
  have lb := deadLimit p.toFun b U
  have free (bad : p.toFun a=0 ∨ p.toFun b=0) : charge av (p.toFun (combine d a b))=false := by
    rw [p.combineEq _ _ _ hd]
    rcases combine_eq_cases _ _ _ hd (bad.imp_right Or.inl) with e|e|e <;> simp [charge,e,ma,mb]
  by_cases az : p.toFun a=0
  · rw [free (Or.inl az)];simp only [Bool.toNat_false,Nat.zero_add]
    by_cases bz : p.toFun b=0
    · have zz : p.toFun (combine d a b)=0 := by
        rw [p.combineEq _ _ _ hd,az,bz];interval_cases d <;> decide
      have fresh : combine d a b∉U := fun m => fz (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem m))
      rw [deadGrow zz fresh];omega
    · rw [deadStay bz] at la;omega
  · rw [deadStay az]
    by_cases bz : p.toFun b=0
    · rw [free (Or.inr bz)];simp only [Bool.toNat_false,Nat.zero_add];omega
    · rw [deadStay bz];cases charge av (p.toFun (combine d a b)) <;> simp [Bool.toNat] <;> omega

theorem projectLive {m h k S} (p : Projection m h) (live : Live m k S) :
    ∃ j T,j+dead p.toFun S≤k ∧ Live h j T ∧ ∀ x∈T,x∈S.image p.toFun := by
  induction k generalizing S with
  | zero =>
    rw [Live] at live
    obtain ⟨a, rfl, hg, _⟩ := live
    have gp := p.good a hg
    have nz : p.toFun a≠0 := by intro e;have x := gp 0 p.someRow;simp [e] at x
    exact ⟨0,{p.toFun a},by simp [dead,nz],Live.done gp nz,by simp⟩
  | succ k ih =>
    rw [Live] at live
    obtain ⟨U, a, b, d, rfl, hd, ha, hb, ab, fz, tail⟩ := live
    obtain ⟨j,T,cost,ok,raw⟩ := ih tail
    let av := ((insert a (insert b U)).image p.toFun).toList
    have ma : p.toFun a∈av := by simp [av]
    have mb : p.toFun b∈av := by simp [av]
    have later : Possible h j (av++[combine d (p.toFun a) (p.toFun b)]) := by
      refine ⟨j,T,le_rfl,ok,?_⟩
      intro z hz
      have has := raw _ hz
      simp only [Finset.image_insert,Finset.mem_insert] at has
      rcases has with rfl|old
      · simp [p.combineEq d a b hd]
      · have inav : z∈av := by simpa [av] using (Or.inr (Or.inr old) : z=p.toFun a ∨ z=p.toFun b ∨ z∈U.image p.toFun)
        simp [inav]
    obtain ⟨l,V,lim,good,sub⟩ := pullPaid hd ma mb later
    rw [←p.combineEq d a b hd] at lim
    have bound := countCharge p hd U fz av ma mb
    exact ⟨l,V,by omega,good,by simpa [av] using sub⟩

lemma full_bit (m i : ℕ) : (full m).testBit i=decide (i<m) := by
  simp [full,Nat.shiftLeft_eq,Nat.testBit_two_pow_sub_one]

lemma enoughSup {m k S} (h : Live m k S) (v : List ℕ) (sub : ∀ x∈S,x∈v) : enough m (cover m v)=true := by
  apply beq_iff_eq.mpr;apply Nat.eq_of_testBit_eq;intro i
  rw [Nat.testBit_and,full_bit]
  by_cases hi : i<m
  · obtain ⟨x,hx,g⟩ := liveSeparates h i hi
    have bit := (coverBit m i v).2 ⟨x,sub _ hx,g⟩
    simp [bit,hi]
  · simp [hi]
def start (m fuel : ℕ) (av : List ℕ) :=
  let v := av.eraseDups.filter (fun x => x != 0)
  let needed := fun a => !(enough m (cover m (v.filter (fun x => x != a))))
  let must := v.filter needed
  let extra := v.filter (fun x => !needed x)
  extra.sublists.any (fun t =>
    let s := (must++t).dedup
    s.length≤fuel+1 && enough m (cover m s) && search m fuel s)

theorem start_complete {m k S} (h : Live m k S) (av : List ℕ) (sub : ∀ x∈S,x∈av)
    (fuel : ℕ) (lim : k≤fuel) : start m fuel av=true := by
  let v := av.eraseDups.filter (fun x => x != 0)
  let needed := fun a => !(enough m (cover m (v.filter (fun x => x != a))))
  let must := v.filter needed
  let extra := v.filter (fun x => !needed x)
  let t := extra.filter (fun x => decide (x∈S))
  let s := (must++t).dedup
  have inV (x : ℕ) (hx : x∈S) : x∈v := by simp [v,sub x hx,liveNonzero h x hx]
  have fixed (a : ℕ) (ha : a∈must) : a∈S := by
    by_contra absent
    have no := (List.mem_filter.mp ha).2
    have all (x : ℕ) (hx : x∈S) : x∈v.filter (fun y => y != a) := by
      have ne : x≠a := by rintro rfl;exact absent hx
      simp [inV x hx,ne]
    have yes := enoughSup h _ all
    simpa [needed,yes] using no
  have eq : s.toFinset=S := by
    ext x
    constructor
    · intro mem
      have e : x∈must ∨ x∈t := by simpa [s] using mem
      rcases e with l|r
      · exact fixed x l
      · simpa using (List.mem_filter.mp r).2
    · intro mem
      have raw := inV x mem
      cases H : needed x <;> simp [s,must,t,extra,H,raw,mem]
  have nd : s.Nodup := List.nodup_dedup _
  have size : s.length≤fuel+1 := by
    have vsize := liveSize h
    rw [←eq,List.toFinset_card_of_nodup nd] at vsize;omega
  have test := complete m fuel h lim s eq nd
  have cov := enoughLive h s eq
  apply List.any_eq_true.mpr
  refine ⟨t,List.mem_sublists.mpr (List.filter_sublist),?_⟩
  change (decide (s.length≤fuel+1) && enough m (cover m s) && search m fuel s)=true
  simp [size,cov,test]

def actL : List ℕ → ℕ → ℕ
  | [], _ => 0
  | p :: ps, w => Nat.bit (w.testBit p) (actL ps w)

theorem actL_testBit : ∀ (pi : List ℕ) (w k : ℕ),
    (actL pi w).testBit k = (pi[k]?.map w.testBit).getD false
  | [], w, k => by simp [actL]
  | p :: ps, w, 0 => by simp [actL, Nat.testBit_bit_zero]
  | p :: ps, w, k + 1 => by simp [actL, Nat.testBit_bit_succ, actL_testBit ps w k]

theorem actL_and (pi : List ℕ) (a b : ℕ) : actL pi (a &&& b) = actL pi a &&& actL pi b := by
  apply Nat.eq_of_testBit_eq; intro k
  rw [Nat.testBit_and, actL_testBit, actL_testBit, actL_testBit]
  cases pi[k]? <;> simp [Nat.testBit_and]

theorem actL_or (pi : List ℕ) (a b : ℕ) : actL pi (a ||| b) = actL pi a ||| actL pi b := by
  apply Nat.eq_of_testBit_eq; intro k
  rw [Nat.testBit_or, actL_testBit, actL_testBit, actL_testBit]
  cases pi[k]? <;> simp [Nat.testBit_or]

theorem actL_xor (pi : List ℕ) (a b : ℕ) : actL pi (a ^^^ b) = actL pi a ^^^ actL pi b := by
  apply Nat.eq_of_testBit_eq; intro k
  rw [Nat.testBit_xor, actL_testBit, actL_testBit, actL_testBit]
  cases pi[k]? <;> simp [Nat.testBit_xor]

def coord (m : ℕ) (r : List ℕ) := actL (r ++ r.map (m+·))

theorem coordC (m : ℕ) (r : List ℕ) (d a b : ℕ) (hd : d < 4) :
    coord m r (combine d a b) = combine d (coord m r a) (coord m r b) := by
  interval_cases d <;> simp [combine,coord,actL_and,actL_or,actL_xor]

def pick {m h : ℕ} (r : List ℕ) (len : r.length=h) (small : ∀ i∈r,i<m) (pos : 0<h) : Projection m h := by
  refine ⟨coord m r, ?_, coordC m r, ?_, pos⟩
  · apply Nat.eq_of_testBit_eq
    intro i
    simp only [coord,actL_testBit,Nat.zero_testBit]
    cases (r ++ r.map (m+·))[i]? <;> simp
  · intro a ha i hi
    have ir : i<r.length := by omega
    have b := ha r[i] (small _ (List.getElem_mem ir))
    have H₁ : (r ++ r.map (m+·))[i]? = some r[i] := by simp [List.getElem?_append,ir]
    have H₂ : (r ++ r.map (m+·))[h+i]? = some (m+r[i]) := by
      have ne : ¬h+i<r.length := by omega
      have sub : h+i-r.length=i := by omega
      simp [List.getElem?_append,ne,sub,ir]
    simpa [coord,actL_testBit,H₁,H₂] using b

def Ban (m fuel : ℕ) (v : List ℕ) := ∀ n, n ≤ fuel → ¬Live m n v.toFinset
def Wide (m fuel : ℕ) (v : List ℕ) := ¬Possible m fuel v

theorem viaSearch {m fuel v} (test : start m fuel v=false) : Wide m fuel v := by
  rintro ⟨k,S,le,live,sub⟩
  have := start_complete live v sub fuel le
  simp_all

theorem viaCut {m h f t : ℕ} {v w : List ℕ} (p : Projection m h)
    (bound : Wide h t w) (nd : v.Nodup)
    (mem : ∀ a∈v, p.toFun a=0 ∨ p.toFun a∈w)
    (cost : f≤t+(v.map p.toFun).count 0) : Ban m f v := by
  intro k lim run
  obtain ⟨j,T,c,ok,incl⟩ := projectLive p run
  have fixed : dead p.toFun v.toFinset=(v.map p.toFun).count 0 := by
    dsimp [dead]
    have E : v.toFinset.filter (fun x => p.toFun x=0) = (v.filter (fun x => decide (p.toFun x=0))).toFinset := by ext x;simp
    rw [E,List.toFinset_card_of_nodup (nd.filter _)]
    simp only [List.count_eq_countP,List.countP_map,Function.comp_apply]
    rw [List.countP_eq_length_filter]
    congr 2
  rw [fixed] at c
  apply bound
  refine ⟨j,T,by omega,ok,?_⟩
  intro x hx
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp (incl _ hx)
  exact (mem y (List.mem_toFinset.mp hy)).resolve_left (liveNonzero ok _ hx)

theorem renameLive {m h k S} (p : Projection m h) (q : Projection h m)
    (run : Live m k S) (rec : ∀ x∈S, q.toFun (p.toFun x)=x) : Live h k (S.image p.toFun) := by
  induction k generalizing S with
  | zero =>
    rw [Live] at run
    obtain ⟨a,rfl,good,nz⟩ := run
    simp only [Finset.image_singleton]
    apply Live.done (p.good a good)
    intro e
    have := rec a (Finset.mem_singleton_self a)
    rw [e,q.atZero] at this
    exact nz this.symm
  | succ k ih =>
    rw [Live] at run
    obtain ⟨U,a,b,d,rfl,hd,ha,hb,ab,fr,tail⟩ := run
    let z := combine d a b
    have ra := rec a (Finset.mem_insert_self _ _)
    have rb := rec b (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have rz : q.toFun (p.toFun z)=z := by simp only [z,p.combineEq _ _ _ hd,q.combineEq _ _ _ hd,ra,rb]
    have ru (x) (hx : x∈U) := rec x (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx))
    have nr := ih tail (by intro x hx; rcases Finset.mem_insert.mp hx with rfl|h; exact rz; exact ru _ h)
    have eqz : p.toFun z=combine d (p.toFun a) (p.toFun b) := p.combineEq _ _ _ hd
    simp only [Finset.image_insert] at nr ⊢
    apply Live.step hd
    · intro e;rw [e,q.atZero] at ra;exact ha ra.symm
    · intro e;rw [e,q.atZero] at rb;exact hb rb.symm
    · intro e;rw [e,rb] at ra;exact ab ra.symm
    · rw [←eqz]
      intro bad
      rcases Finset.mem_insert.mp bad with e|bad
      · have hza := congrArg q.toFun e
        rw [rz,ra] at hza
        exact fr (Finset.mem_insert.mpr (Or.inl hza))
      rcases Finset.mem_insert.mp bad with e|bad
      · have hzb := congrArg q.toFun e
        rw [rz,rb] at hzb
        exact fr (Finset.mem_insert_of_mem (Finset.mem_insert.mpr (Or.inl hzb)))
      obtain ⟨x,hx,e⟩ := Finset.mem_image.mp bad
      have eq := congrArg q.toFun e
      rw [ru x hx,rz] at eq
      exact fr (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (eq ▸ hx : z ∈ U)))
    · simpa only [p.combineEq _ _ _ hd] using nr

theorem viaPerm {m h f v w} (p : Projection m h) (q : Projection h m)
    (ban : Ban h f w) (rec : ∀ a∈v, q.toFun (p.toFun a)=a)
    (eq : (v.map p.toFun).toFinset=w.toFinset) : Ban m f v := by
  intro n hn live
  have ok := renameLive p q live (by simpa using rec)
  apply ban n hn
  have E : (v.map p.toFun).toFinset=v.toFinset.image p.toFun := by ext x;simp
  rw [←eq,E];exact ok

def ordered (v : List ℕ) := v.insertionSort (· ≤ ·)
theorem ord_eq (v : List ℕ) : (ordered v).toFinset=v.toFinset := by
  ext x;simp [ordered,List.mem_insertionSort]
def banList (m f : ℕ) (vs : List (List ℕ)) := ∀ v∈vs, Ban m f v
theorem consBan {m f a l} (h : Ban m f a) (t : banList m f l) : banList m f (a::l) := by
  intro v hv;rcases List.mem_cons.mp hv with rfl|e;exact h;exact t _ e
theorem nilBan (m f) : banList m f [] := by simp [banList]

theorem viaBranch {m f : ℕ} {v : List ℕ} {ws : List (List ℕ)} (closed : banList m f ws)
    (nd : v.Nodup) (no : terminal m v=false)
    (test : anyGate m f (fun u => !ws.contains (ordered u)) v=false) : Ban m (f+1) v := by
  intro n lim live
  cases n with
  | zero =>
    rw [Live] at live
    obtain ⟨a,rep,g,_⟩ := live
    have ev := ends g v (List.mem_toFinset.mp (rep ▸ Finset.mem_singleton_self a))
    simp_all
  | succ n =>
    rw [Live] at live
    obtain ⟨U,a,b,d,rep,hd,_,_,ab,fr,tail⟩ := live
    have yes := @transition m f n U a b d v (fun u => !ws.contains (ordered u)) hd ab fr rep nd (by omega) tail (by
      intro u hu nu
      change (!ws.contains (ordered u))=true
      simp
      intro found
      have hv := closed _ found n (by omega)
      rw [ord_eq,hu] at hv
      exact hv tail)
    simp_all

theorem widen {m f v} (ess : ∀ a∈v, ∃ i : Fin m, ∀ b∈v, b.testBit i.val≠b.testBit (m+i.val) → b=a)
    (h : Ban m f v) : Wide m f v := by
  rintro ⟨n,S,le,live,sub⟩
  have eq : S=v.toFinset := by
    apply Finset.Subset.antisymm (fun x hx => List.mem_toFinset.mpr (sub _ hx))
    intro a ha
    obtain ⟨i,hi⟩ := ess a (List.mem_toFinset.mp ha)
    obtain ⟨b,hb,sep⟩ := liveSeparates live i.val i.isLt
    exact hi b (sub b hb) sep ▸ hb
  exact h n le (eq ▸ live)

theorem viaSmall {m f v} (ex : search m f v=false) (nd : v.Nodup) : Ban m f v := by
  intro n le live
  have := complete m f live le v rfl nd
  simp_all

theorem viaSub {m f v ws} (bs : banList m f ws) (nd : v.Nodup)
    (check : v.sublists.all (fun u => !(u.length≤f+1 && enough m (cover m u)) || ws.contains u)=true) :
    Wide m f v := by
  rintro ⟨n,S,lim,live,sub⟩
  let u := v.filter (fun x => decide (x∈S))
  have eq : u.toFinset=S := by ext x; simp [u]; exact fun hx => sub _ hx
  have nd' : u.Nodup := nd.filter _
  have len := liveSize live
  rw [←eq,List.toFinset_card_of_nodup nd'] at len
  have ok := List.all_eq_true.mp check u (List.mem_sublists.mpr List.filter_sublist)
  have cap : u.length≤f+1 := by omega
  have cov := enoughLive live u eq
  simp [cap,cov] at ok
  exact bs u ok n lim (eq ▸ live)

def projTopP0 : Projection 89 89 := pick [0,1,2,3,4,5,7,6,8,9,10,11,12,13,15,14,48,49,50,51,52,53,55,54,56,57,58,59,60,61,63,62,64,65,66,67,68,70,69,71,72,73,74,75,76,77,79,78,16,17,18,19,20,21,23,22,24,25,26,27,28,29,31,30,32,33,34,35,36,38,37,39,40,41,42,43,44,45,47,46,80,81,82,83,84,85,86,88,87] rfl (by decide +kernel) (by decide)
def projTopPInv0 : Projection 89 89 := pick [0,1,2,3,4,5,7,6,8,9,10,11,12,13,15,14,48,49,50,51,52,53,55,54,56,57,58,59,60,61,63,62,64,65,66,67,68,70,69,71,72,73,74,75,76,77,79,78,16,17,18,19,20,21,23,22,24,25,26,27,28,29,31,30,32,33,34,35,36,38,37,39,40,41,42,43,44,45,47,46,80,81,82,83,84,85,86,88,87] rfl (by decide +kernel) (by decide)
def projTopP1 : Projection 89 89 := pick [8,9,10,11,12,13,14,15,0,1,2,3,4,5,6,7,24,25,26,27,28,29,30,31,16,17,18,19,20,21,22,23,32,34,33,35,36,37,38,39,40,42,41,43,44,45,46,47,56,57,58,59,60,61,62,63,48,49,50,51,52,53,54,55,64,66,65,67,68,69,70,71,72,74,73,75,76,77,78,79,80,81,83,82,84,85,86,87,88] rfl (by decide +kernel) (by decide)
def projTopPInv1 : Projection 89 89 := pick [8,9,10,11,12,13,14,15,0,1,2,3,4,5,6,7,24,25,26,27,28,29,30,31,16,17,18,19,20,21,22,23,32,34,33,35,36,37,38,39,40,42,41,43,44,45,46,47,56,57,58,59,60,61,62,63,48,49,50,51,52,53,54,55,64,66,65,67,68,69,70,71,72,74,73,75,76,77,78,79,80,81,83,82,84,85,86,87,88] rfl (by decide +kernel) (by decide)
def projTopP2 : Projection 89 89 := pick [8,9,10,11,12,13,15,14,0,1,2,3,4,5,7,6,56,57,58,59,60,61,63,62,48,49,50,51,52,53,55,54,64,66,65,67,68,70,69,71,72,74,73,75,76,77,79,78,24,25,26,27,28,29,31,30,16,17,18,19,20,21,23,22,32,34,33,35,36,38,37,39,40,42,41,43,44,45,47,46,80,81,83,82,84,85,86,88,87] rfl (by decide +kernel) (by decide)
def projTopPInv2 : Projection 89 89 := pick [8,9,10,11,12,13,15,14,0,1,2,3,4,5,7,6,56,57,58,59,60,61,63,62,48,49,50,51,52,53,55,54,64,66,65,67,68,70,69,71,72,74,73,75,76,77,79,78,24,25,26,27,28,29,31,30,16,17,18,19,20,21,23,22,32,34,33,35,36,38,37,39,40,42,41,43,44,45,47,46,80,81,83,82,84,85,86,88,87] rfl (by decide +kernel) (by decide)
def projC0P0 : Projection 40 40 := pick [0,1,3,2,4,10,11,13,12,14,5,6,8,7,9,20,21,23,22,24,15,16,18,17,19,30,31,33,32,34,25,26,28,27,29,35,36,38,37,39] rfl (by decide +kernel) (by decide)
def projC0PInv0 : Projection 40 40 := pick [0,1,3,2,4,10,11,13,12,14,5,6,8,7,9,20,21,23,22,24,15,16,18,17,19,30,31,33,32,34,25,26,28,27,29,35,36,38,37,39] rfl (by decide +kernel) (by decide)
def projC0P1 : Projection 40 40 := pick [1,0,2,3,4,26,25,27,28,29,31,30,32,33,34,16,15,17,18,19,21,20,22,23,24,6,5,7,8,9,11,10,12,13,14,36,35,37,38,39] rfl (by decide +kernel) (by decide)
def projC0PInv1 : Projection 40 40 := pick [1,0,2,3,4,26,25,27,28,29,31,30,32,33,34,16,15,17,18,19,21,20,22,23,24,6,5,7,8,9,11,10,12,13,14,36,35,37,38,39] rfl (by decide +kernel) (by decide)
def projC0P2 : Projection 40 40 := pick [1,0,3,2,4,31,30,33,32,34,26,25,28,27,29,21,20,23,22,24,16,15,18,17,19,11,10,13,12,14,6,5,8,7,9,36,35,38,37,39] rfl (by decide +kernel) (by decide)
def projC0PInv2 : Projection 40 40 := pick [1,0,3,2,4,31,30,33,32,34,26,25,28,27,29,21,20,23,22,24,16,15,18,17,19,11,10,13,12,14,6,5,8,7,9,36,35,38,37,39] rfl (by decide +kernel) (by decide)
def projC1P0 : Projection 40 40 := pick [0,1,3,2,4,10,11,13,12,14,5,6,8,7,9,20,21,23,22,24,15,16,18,17,19,30,31,33,32,34,25,26,28,27,29,35,36,38,37,39] rfl (by decide +kernel) (by decide)
def projC1PInv0 : Projection 40 40 := pick [0,1,3,2,4,10,11,13,12,14,5,6,8,7,9,20,21,23,22,24,15,16,18,17,19,30,31,33,32,34,25,26,28,27,29,35,36,38,37,39] rfl (by decide +kernel) (by decide)
def projC1P1 : Projection 40 40 := pick [1,0,2,3,4,26,25,27,28,29,31,30,32,33,34,16,15,17,18,19,21,20,22,23,24,6,5,7,8,9,11,10,12,13,14,36,35,37,38,39] rfl (by decide +kernel) (by decide)
def projC1PInv1 : Projection 40 40 := pick [1,0,2,3,4,26,25,27,28,29,31,30,32,33,34,16,15,17,18,19,21,20,22,23,24,6,5,7,8,9,11,10,12,13,14,36,35,37,38,39] rfl (by decide +kernel) (by decide)
def projC1P2 : Projection 40 40 := pick [1,0,3,2,4,31,30,33,32,34,26,25,28,27,29,21,20,23,22,24,16,15,18,17,19,11,10,13,12,14,6,5,8,7,9,36,35,38,37,39] rfl (by decide +kernel) (by decide)
def projC1PInv2 : Projection 40 40 := pick [1,0,3,2,4,31,30,33,32,34,26,25,28,27,29,21,20,23,22,24,16,15,18,17,19,11,10,13,12,14,6,5,8,7,9,36,35,38,37,39] rfl (by decide +kernel) (by decide)
def projC2P0 : Projection 45 45 := pick [0,1,3,2,4,10,11,13,12,14,5,6,8,7,9,15,16,18,17,19,25,26,28,27,29,20,21,23,22,24,35,36,38,37,39,30,31,33,32,34,40,41,43,42,44] rfl (by decide +kernel) (by decide)
def projC2PInv0 : Projection 45 45 := pick [0,1,3,2,4,10,11,13,12,14,5,6,8,7,9,15,16,18,17,19,25,26,28,27,29,20,21,23,22,24,35,36,38,37,39,30,31,33,32,34,40,41,43,42,44] rfl (by decide +kernel) (by decide)
def projC2P1 : Projection 45 45 := pick [5,7,6,8,9,0,2,1,3,4,10,12,11,13,14,20,22,21,23,24,15,17,16,18,19,25,27,26,28,29,30,32,31,33,34,40,42,41,43,44,35,37,36,38,39] rfl (by decide +kernel) (by decide)
def projC2PInv1 : Projection 45 45 := pick [5,7,6,8,9,0,2,1,3,4,10,12,11,13,14,20,22,21,23,24,15,17,16,18,19,25,27,26,28,29,30,32,31,33,34,40,42,41,43,44,35,37,36,38,39] rfl (by decide +kernel) (by decide)
def projC2P2 : Projection 45 45 := pick [5,7,8,6,9,10,12,13,11,14,0,2,3,1,4,20,22,23,21,24,25,27,28,26,29,15,17,18,16,19,40,42,43,41,44,30,32,33,31,34,35,37,38,36,39] rfl (by decide +kernel) (by decide)
def projC2PInv2 : Projection 45 45 := pick [10,13,11,12,14,0,3,1,2,4,5,8,6,7,9,25,28,26,27,29,15,18,16,17,19,20,23,21,22,24,35,38,36,37,39,40,43,41,42,44,30,33,31,32,34] rfl (by decide +kernel) (by decide)
def projC2P3 : Projection 45 45 := pick [10,13,11,12,14,0,3,1,2,4,5,8,6,7,9,25,28,26,27,29,15,18,16,17,19,20,23,21,22,24,35,38,36,37,39,40,43,41,42,44,30,33,31,32,34] rfl (by decide +kernel) (by decide)
def projC2PInv3 : Projection 45 45 := pick [5,7,8,6,9,10,12,13,11,14,0,2,3,1,4,20,22,23,21,24,25,27,28,26,29,15,17,18,16,19,40,42,43,41,44,30,32,33,31,34,35,37,38,36,39] rfl (by decide +kernel) (by decide)
def projC2P4 : Projection 45 45 := pick [10,13,12,11,14,5,8,7,6,9,0,3,2,1,4,25,28,27,26,29,20,23,22,21,24,15,18,17,16,19,40,43,42,41,44,35,38,37,36,39,30,33,32,31,34] rfl (by decide +kernel) (by decide)
def projC2PInv4 : Projection 45 45 := pick [10,13,12,11,14,5,8,7,6,9,0,3,2,1,4,25,28,27,26,29,20,23,22,21,24,15,18,17,16,19,40,43,42,41,44,35,38,37,36,39,30,33,32,31,34] rfl (by decide +kernel) (by decide)
def projC2P5 : Projection 45 45 := pick [15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44] rfl (by decide +kernel) (by decide)
def projC2PInv5 : Projection 45 45 := pick [15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44] rfl (by decide +kernel) (by decide)
def projC2P6 : Projection 45 45 := pick [15,16,18,17,19,25,26,28,27,29,20,21,23,22,24,0,1,3,2,4,10,11,13,12,14,5,6,8,7,9,35,36,38,37,39,30,31,33,32,34,40,41,43,42,44] rfl (by decide +kernel) (by decide)
def projC2PInv6 : Projection 45 45 := pick [15,16,18,17,19,25,26,28,27,29,20,21,23,22,24,0,1,3,2,4,10,11,13,12,14,5,6,8,7,9,35,36,38,37,39,30,31,33,32,34,40,41,43,42,44] rfl (by decide +kernel) (by decide)
def projC2P7 : Projection 45 45 := pick [20,22,21,23,24,15,17,16,18,19,25,27,26,28,29,5,7,6,8,9,0,2,1,3,4,10,12,11,13,14,30,32,31,33,34,40,42,41,43,44,35,37,36,38,39] rfl (by decide +kernel) (by decide)
def projC2PInv7 : Projection 45 45 := pick [20,22,21,23,24,15,17,16,18,19,25,27,26,28,29,5,7,6,8,9,0,2,1,3,4,10,12,11,13,14,30,32,31,33,34,40,42,41,43,44,35,37,36,38,39] rfl (by decide +kernel) (by decide)
def projC2P8 : Projection 45 45 := pick [20,22,23,21,24,25,27,28,26,29,15,17,18,16,19,5,7,8,6,9,10,12,13,11,14,0,2,3,1,4,40,42,43,41,44,30,32,33,31,34,35,37,38,36,39] rfl (by decide +kernel) (by decide)
def projC2PInv8 : Projection 45 45 := pick [25,28,26,27,29,15,18,16,17,19,20,23,21,22,24,10,13,11,12,14,0,3,1,2,4,5,8,6,7,9,35,38,36,37,39,40,43,41,42,44,30,33,31,32,34] rfl (by decide +kernel) (by decide)
def projC2P9 : Projection 45 45 := pick [25,28,26,27,29,15,18,16,17,19,20,23,21,22,24,10,13,11,12,14,0,3,1,2,4,5,8,6,7,9,35,38,36,37,39,40,43,41,42,44,30,33,31,32,34] rfl (by decide +kernel) (by decide)
def projC2PInv9 : Projection 45 45 := pick [20,22,23,21,24,25,27,28,26,29,15,17,18,16,19,5,7,8,6,9,10,12,13,11,14,0,2,3,1,4,40,42,43,41,44,30,32,33,31,34,35,37,38,36,39] rfl (by decide +kernel) (by decide)
def projC2P10 : Projection 45 45 := pick [25,28,27,26,29,20,23,22,21,24,15,18,17,16,19,10,13,12,11,14,5,8,7,6,9,0,3,2,1,4,40,43,42,41,44,35,38,37,36,39,30,33,32,31,34] rfl (by decide +kernel) (by decide)
def projC2PInv10 : Projection 45 45 := pick [25,28,27,26,29,20,23,22,21,24,15,18,17,16,19,10,13,12,11,14,5,8,7,6,9,0,3,2,1,4,40,43,42,41,44,35,38,37,36,39,30,33,32,31,34] rfl (by decide +kernel) (by decide)
def projC3P0 : Projection 28 28 := pick [4,6,5,7,0,2,1,3,12,14,13,15,8,10,9,11,20,22,21,23,16,18,17,19,24,26,25,27] rfl (by decide +kernel) (by decide)
def projC3PInv0 : Projection 28 28 := pick [4,6,5,7,0,2,1,3,12,14,13,15,8,10,9,11,20,22,21,23,16,18,17,19,24,26,25,27] rfl (by decide +kernel) (by decide)
def projC3P1 : Projection 28 28 := pick [0,1,2,3,4,5,6,7,16,17,18,19,20,21,22,23,8,9,10,11,12,13,14,15,24,25,26,27] rfl (by decide +kernel) (by decide)
def projC3PInv1 : Projection 28 28 := pick [0,1,2,3,4,5,6,7,16,17,18,19,20,21,22,23,8,9,10,11,12,13,14,15,24,25,26,27] rfl (by decide +kernel) (by decide)
def projC3P2 : Projection 28 28 := pick [4,6,5,7,0,2,1,3,20,22,21,23,16,18,17,19,12,14,13,15,8,10,9,11,24,26,25,27] rfl (by decide +kernel) (by decide)
def projC3PInv2 : Projection 28 28 := pick [4,6,5,7,0,2,1,3,20,22,21,23,16,18,17,19,12,14,13,15,8,10,9,11,24,26,25,27] rfl (by decide +kernel) (by decide)
def projC3P3 : Projection 28 28 := pick [8,9,10,11,12,13,14,15,0,1,2,3,4,5,6,7,16,17,18,19,20,21,22,23,24,25,26,27] rfl (by decide +kernel) (by decide)
def projC3PInv3 : Projection 28 28 := pick [8,9,10,11,12,13,14,15,0,1,2,3,4,5,6,7,16,17,18,19,20,21,22,23,24,25,26,27] rfl (by decide +kernel) (by decide)
def projC3P4 : Projection 28 28 := pick [12,14,13,15,8,10,9,11,4,6,5,7,0,2,1,3,20,22,21,23,16,18,17,19,24,26,25,27] rfl (by decide +kernel) (by decide)
def projC3PInv4 : Projection 28 28 := pick [12,14,13,15,8,10,9,11,4,6,5,7,0,2,1,3,20,22,21,23,16,18,17,19,24,26,25,27] rfl (by decide +kernel) (by decide)
def projC3P5 : Projection 28 28 := pick [8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,0,1,2,3,4,5,6,7,24,25,26,27] rfl (by decide +kernel) (by decide)
def projC3PInv5 : Projection 28 28 := pick [16,17,18,19,20,21,22,23,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,24,25,26,27] rfl (by decide +kernel) (by decide)
def projC3P6 : Projection 28 28 := pick [12,14,13,15,8,10,9,11,20,22,21,23,16,18,17,19,4,6,5,7,0,2,1,3,24,26,25,27] rfl (by decide +kernel) (by decide)
def projC3PInv6 : Projection 28 28 := pick [20,22,21,23,16,18,17,19,4,6,5,7,0,2,1,3,12,14,13,15,8,10,9,11,24,26,25,27] rfl (by decide +kernel) (by decide)
def projC3P7 : Projection 28 28 := pick [16,17,18,19,20,21,22,23,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,24,25,26,27] rfl (by decide +kernel) (by decide)
def projC3PInv7 : Projection 28 28 := pick [8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,0,1,2,3,4,5,6,7,24,25,26,27] rfl (by decide +kernel) (by decide)
def projC3P8 : Projection 28 28 := pick [20,22,21,23,16,18,17,19,4,6,5,7,0,2,1,3,12,14,13,15,8,10,9,11,24,26,25,27] rfl (by decide +kernel) (by decide)
def projC3PInv8 : Projection 28 28 := pick [12,14,13,15,8,10,9,11,20,22,21,23,16,18,17,19,4,6,5,7,0,2,1,3,24,26,25,27] rfl (by decide +kernel) (by decide)
def projC3P9 : Projection 28 28 := pick [16,17,18,19,20,21,22,23,8,9,10,11,12,13,14,15,0,1,2,3,4,5,6,7,24,25,26,27] rfl (by decide +kernel) (by decide)
def projC3PInv9 : Projection 28 28 := pick [16,17,18,19,20,21,22,23,8,9,10,11,12,13,14,15,0,1,2,3,4,5,6,7,24,25,26,27] rfl (by decide +kernel) (by decide)
def projC3P10 : Projection 28 28 := pick [20,22,21,23,16,18,17,19,12,14,13,15,8,10,9,11,4,6,5,7,0,2,1,3,24,26,25,27] rfl (by decide +kernel) (by decide)
def projC3PInv10 : Projection 28 28 := pick [20,22,21,23,16,18,17,19,12,14,13,15,8,10,9,11,4,6,5,7,0,2,1,3,24,26,25,27] rfl (by decide +kernel) (by decide)
def projC4P0 : Projection 24 24 := pick [8,9,10,11,12,13,14,15,0,1,2,3,4,5,6,7,16,17,18,19,20,21,22,23] rfl (by decide +kernel) (by decide)
def projC4PInv0 : Projection 24 24 := pick [8,9,10,11,12,13,14,15,0,1,2,3,4,5,6,7,16,17,18,19,20,21,22,23] rfl (by decide +kernel) (by decide)
def projC5P0 : Projection 24 24 := pick [8,9,10,11,12,13,14,15,0,1,2,3,4,5,6,7,16,17,18,19,20,21,22,23] rfl (by decide +kernel) (by decide)
def projC5PInv0 : Projection 24 24 := pick [8,9,10,11,12,13,14,15,0,1,2,3,4,5,6,7,16,17,18,19,20,21,22,23] rfl (by decide +kernel) (by decide)
def projC6P0 : Projection 20 20 := pick [4,6,5,7,0,2,1,3,12,14,13,15,8,10,9,11,16,18,17,19] rfl (by decide +kernel) (by decide)
def projC6PInv0 : Projection 20 20 := pick [4,6,5,7,0,2,1,3,12,14,13,15,8,10,9,11,16,18,17,19] rfl (by decide +kernel) (by decide)
def projC6P1 : Projection 20 20 := pick [8,9,10,11,12,13,14,15,0,1,2,3,4,5,6,7,16,17,18,19] rfl (by decide +kernel) (by decide)
def projC6PInv1 : Projection 20 20 := pick [8,9,10,11,12,13,14,15,0,1,2,3,4,5,6,7,16,17,18,19] rfl (by decide +kernel) (by decide)
def projC6P2 : Projection 20 20 := pick [12,14,13,15,8,10,9,11,4,6,5,7,0,2,1,3,16,18,17,19] rfl (by decide +kernel) (by decide)
def projC6PInv2 : Projection 20 20 := pick [12,14,13,15,8,10,9,11,4,6,5,7,0,2,1,3,16,18,17,19] rfl (by decide +kernel) (by decide)
def projC6P3 : Projection 20 20 := pick [4,6,5,7,0,2,1,3,12,14,13,15,8,10,9,11,16,18,17,19] rfl (by decide +kernel) (by decide)
def projC6PInv3 : Projection 20 20 := pick [4,6,5,7,0,2,1,3,12,14,13,15,8,10,9,11,16,18,17,19] rfl (by decide +kernel) (by decide)
def projC6P4 : Projection 20 20 := pick [8,9,10,11,12,13,14,15,0,1,2,3,4,5,6,7,16,17,18,19] rfl (by decide +kernel) (by decide)
def projC6PInv4 : Projection 20 20 := pick [8,9,10,11,12,13,14,15,0,1,2,3,4,5,6,7,16,17,18,19] rfl (by decide +kernel) (by decide)
def projC6P5 : Projection 20 20 := pick [12,14,13,15,8,10,9,11,4,6,5,7,0,2,1,3,16,18,17,19] rfl (by decide +kernel) (by decide)
def projC6PInv5 : Projection 20 20 := pick [12,14,13,15,8,10,9,11,4,6,5,7,0,2,1,3,16,18,17,19] rfl (by decide +kernel) (by decide)
def projC7P0 : Projection 20 20 := pick [4,6,5,7,0,2,1,3,12,14,13,15,8,10,9,11,16,18,17,19] rfl (by decide +kernel) (by decide)
def projC7PInv0 : Projection 20 20 := pick [4,6,5,7,0,2,1,3,12,14,13,15,8,10,9,11,16,18,17,19] rfl (by decide +kernel) (by decide)
def projC7P1 : Projection 20 20 := pick [8,9,10,11,12,13,14,15,0,1,2,3,4,5,6,7,16,17,18,19] rfl (by decide +kernel) (by decide)
def projC7PInv1 : Projection 20 20 := pick [8,9,10,11,12,13,14,15,0,1,2,3,4,5,6,7,16,17,18,19] rfl (by decide +kernel) (by decide)
def projC7P2 : Projection 20 20 := pick [12,14,13,15,8,10,9,11,4,6,5,7,0,2,1,3,16,18,17,19] rfl (by decide +kernel) (by decide)
def projC7PInv2 : Projection 20 20 := pick [12,14,13,15,8,10,9,11,4,6,5,7,0,2,1,3,16,18,17,19] rfl (by decide +kernel) (by decide)
def projC7P3 : Projection 20 20 := pick [4,6,5,7,0,2,1,3,12,14,13,15,8,10,9,11,16,18,17,19] rfl (by decide +kernel) (by decide)
def projC7PInv3 : Projection 20 20 := pick [4,6,5,7,0,2,1,3,12,14,13,15,8,10,9,11,16,18,17,19] rfl (by decide +kernel) (by decide)
def projC7P4 : Projection 20 20 := pick [8,9,10,11,12,13,14,15,0,1,2,3,4,5,6,7,16,17,18,19] rfl (by decide +kernel) (by decide)
def projC7PInv4 : Projection 20 20 := pick [8,9,10,11,12,13,14,15,0,1,2,3,4,5,6,7,16,17,18,19] rfl (by decide +kernel) (by decide)
def projC7P5 : Projection 20 20 := pick [12,14,13,15,8,10,9,11,4,6,5,7,0,2,1,3,16,18,17,19] rfl (by decide +kernel) (by decide)
def projC7PInv5 : Projection 20 20 := pick [12,14,13,15,8,10,9,11,4,6,5,7,0,2,1,3,16,18,17,19] rfl (by decide +kernel) (by decide)
def projC8P0 : Projection 16 16 := pick [1,0,2,3,13,12,14,15,9,8,10,11,5,4,6,7] rfl (by decide +kernel) (by decide)
def projC8PInv0 : Projection 16 16 := pick [1,0,2,3,13,12,14,15,9,8,10,11,5,4,6,7] rfl (by decide +kernel) (by decide)
def projC8P1 : Projection 16 16 := pick [1,0,2,3,13,12,14,15,9,8,10,11,5,4,6,7] rfl (by decide +kernel) (by decide)
def projC8PInv1 : Projection 16 16 := pick [1,0,2,3,13,12,14,15,9,8,10,11,5,4,6,7] rfl (by decide +kernel) (by decide)
def projC9P0 : Projection 16 16 := pick [1,0,2,3,13,12,14,15,9,8,10,11,5,4,6,7] rfl (by decide +kernel) (by decide)
def projC9PInv0 : Projection 16 16 := pick [1,0,2,3,13,12,14,15,9,8,10,11,5,4,6,7] rfl (by decide +kernel) (by decide)
def projC9P1 : Projection 16 16 := pick [1,0,2,3,13,12,14,15,9,8,10,11,5,4,6,7] rfl (by decide +kernel) (by decide)
def projC9PInv1 : Projection 16 16 := pick [1,0,2,3,13,12,14,15,9,8,10,11,5,4,6,7] rfl (by decide +kernel) (by decide)
def projC10P0 : Projection 20 20 := pick [4,6,5,7,0,2,1,3,12,14,13,15,8,10,9,11,16,18,17,19] rfl (by decide +kernel) (by decide)
def projC10PInv0 : Projection 20 20 := pick [4,6,5,7,0,2,1,3,12,14,13,15,8,10,9,11,16,18,17,19] rfl (by decide +kernel) (by decide)
def projC10P1 : Projection 20 20 := pick [4,6,5,7,0,2,1,3,12,14,13,15,8,10,9,11,16,18,17,19] rfl (by decide +kernel) (by decide)
def projC10PInv1 : Projection 20 20 := pick [4,6,5,7,0,2,1,3,12,14,13,15,8,10,9,11,16,18,17,19] rfl (by decide +kernel) (by decide)
def projC10P2 : Projection 20 20 := pick [8,9,10,11,12,13,14,15,0,1,2,3,4,5,6,7,16,17,18,19] rfl (by decide +kernel) (by decide)
def projC10PInv2 : Projection 20 20 := pick [8,9,10,11,12,13,14,15,0,1,2,3,4,5,6,7,16,17,18,19] rfl (by decide +kernel) (by decide)
def projC10P3 : Projection 20 20 := pick [12,14,13,15,8,10,9,11,4,6,5,7,0,2,1,3,16,18,17,19] rfl (by decide +kernel) (by decide)
def projC10PInv3 : Projection 20 20 := pick [12,14,13,15,8,10,9,11,4,6,5,7,0,2,1,3,16,18,17,19] rfl (by decide +kernel) (by decide)
def projC10P4 : Projection 20 20 := pick [8,9,10,11,12,13,14,15,0,1,2,3,4,5,6,7,16,17,18,19] rfl (by decide +kernel) (by decide)
def projC10PInv4 : Projection 20 20 := pick [8,9,10,11,12,13,14,15,0,1,2,3,4,5,6,7,16,17,18,19] rfl (by decide +kernel) (by decide)
def projC10P5 : Projection 20 20 := pick [12,14,13,15,8,10,9,11,4,6,5,7,0,2,1,3,16,18,17,19] rfl (by decide +kernel) (by decide)
def projC10PInv5 : Projection 20 20 := pick [12,14,13,15,8,10,9,11,4,6,5,7,0,2,1,3,16,18,17,19] rfl (by decide +kernel) (by decide)
def projC11P0 : Projection 16 16 := pick [1,0,2,3,13,12,14,15,9,8,10,11,5,4,6,7] rfl (by decide +kernel) (by decide)
def projC11PInv0 : Projection 16 16 := pick [1,0,2,3,13,12,14,15,9,8,10,11,5,4,6,7] rfl (by decide +kernel) (by decide)
def projC11P1 : Projection 16 16 := pick [1,0,2,3,13,12,14,15,9,8,10,11,5,4,6,7] rfl (by decide +kernel) (by decide)
def projC11PInv1 : Projection 16 16 := pick [1,0,2,3,13,12,14,15,9,8,10,11,5,4,6,7] rfl (by decide +kernel) (by decide)
def projC12P0 : Projection 16 16 := pick [1,0,2,3,13,12,14,15,9,8,10,11,5,4,6,7] rfl (by decide +kernel) (by decide)
def projC12PInv0 : Projection 16 16 := pick [1,0,2,3,13,12,14,15,9,8,10,11,5,4,6,7] rfl (by decide +kernel) (by decide)
def projC12P1 : Projection 16 16 := pick [1,0,2,3,13,12,14,15,9,8,10,11,5,4,6,7] rfl (by decide +kernel) (by decide)
def projC12PInv1 : Projection 16 16 := pick [1,0,2,3,13,12,14,15,9,8,10,11,5,4,6,7] rfl (by decide +kernel) (by decide)
def projC13P0 : Projection 20 20 := pick [4,6,5,7,0,2,1,3,12,14,13,15,8,10,9,11,16,18,17,19] rfl (by decide +kernel) (by decide)
def projC13PInv0 : Projection 20 20 := pick [4,6,5,7,0,2,1,3,12,14,13,15,8,10,9,11,16,18,17,19] rfl (by decide +kernel) (by decide)
def projC13P1 : Projection 20 20 := pick [4,6,5,7,0,2,1,3,12,14,13,15,8,10,9,11,16,18,17,19] rfl (by decide +kernel) (by decide)
def projC13PInv1 : Projection 20 20 := pick [4,6,5,7,0,2,1,3,12,14,13,15,8,10,9,11,16,18,17,19] rfl (by decide +kernel) (by decide)
def projC13P2 : Projection 20 20 := pick [8,9,10,11,12,13,14,15,0,1,2,3,4,5,6,7,16,17,18,19] rfl (by decide +kernel) (by decide)
def projC13PInv2 : Projection 20 20 := pick [8,9,10,11,12,13,14,15,0,1,2,3,4,5,6,7,16,17,18,19] rfl (by decide +kernel) (by decide)
def projC13P3 : Projection 20 20 := pick [12,14,13,15,8,10,9,11,4,6,5,7,0,2,1,3,16,18,17,19] rfl (by decide +kernel) (by decide)
def projC13PInv3 : Projection 20 20 := pick [12,14,13,15,8,10,9,11,4,6,5,7,0,2,1,3,16,18,17,19] rfl (by decide +kernel) (by decide)
def projC13P4 : Projection 20 20 := pick [8,9,10,11,12,13,14,15,0,1,2,3,4,5,6,7,16,17,18,19] rfl (by decide +kernel) (by decide)
def projC13PInv4 : Projection 20 20 := pick [8,9,10,11,12,13,14,15,0,1,2,3,4,5,6,7,16,17,18,19] rfl (by decide +kernel) (by decide)
def projC13P5 : Projection 20 20 := pick [12,14,13,15,8,10,9,11,4,6,5,7,0,2,1,3,16,18,17,19] rfl (by decide +kernel) (by decide)
def projC13PInv5 : Projection 20 20 := pick [12,14,13,15,8,10,9,11,4,6,5,7,0,2,1,3,16,18,17,19] rfl (by decide +kernel) (by decide)
def projC14P0 : Projection 20 20 := pick [4,6,5,7,0,2,1,3,12,14,13,15,8,10,9,11,16,18,17,19] rfl (by decide +kernel) (by decide)
def projC14PInv0 : Projection 20 20 := pick [4,6,5,7,0,2,1,3,12,14,13,15,8,10,9,11,16,18,17,19] rfl (by decide +kernel) (by decide)
def projC14P1 : Projection 20 20 := pick [4,6,5,7,0,2,1,3,12,14,13,15,8,10,9,11,16,18,17,19] rfl (by decide +kernel) (by decide)
def projC14PInv1 : Projection 20 20 := pick [4,6,5,7,0,2,1,3,12,14,13,15,8,10,9,11,16,18,17,19] rfl (by decide +kernel) (by decide)
def projC14P2 : Projection 20 20 := pick [8,9,10,11,12,13,14,15,0,1,2,3,4,5,6,7,16,17,18,19] rfl (by decide +kernel) (by decide)
def projC14PInv2 : Projection 20 20 := pick [8,9,10,11,12,13,14,15,0,1,2,3,4,5,6,7,16,17,18,19] rfl (by decide +kernel) (by decide)
def projC14P3 : Projection 20 20 := pick [12,14,13,15,8,10,9,11,4,6,5,7,0,2,1,3,16,18,17,19] rfl (by decide +kernel) (by decide)
def projC14PInv3 : Projection 20 20 := pick [12,14,13,15,8,10,9,11,4,6,5,7,0,2,1,3,16,18,17,19] rfl (by decide +kernel) (by decide)
def projC14P4 : Projection 20 20 := pick [8,9,10,11,12,13,14,15,0,1,2,3,4,5,6,7,16,17,18,19] rfl (by decide +kernel) (by decide)
def projC14PInv4 : Projection 20 20 := pick [8,9,10,11,12,13,14,15,0,1,2,3,4,5,6,7,16,17,18,19] rfl (by decide +kernel) (by decide)
def projC14P5 : Projection 20 20 := pick [12,14,13,15,8,10,9,11,4,6,5,7,0,2,1,3,16,18,17,19] rfl (by decide +kernel) (by decide)
def projC14PInv5 : Projection 20 20 := pick [12,14,13,15,8,10,9,11,4,6,5,7,0,2,1,3,16,18,17,19] rfl (by decide +kernel) (by decide)
def projC15P0 : Projection 20 20 := pick [4,6,5,7,0,2,1,3,12,14,13,15,8,10,9,11,16,18,17,19] rfl (by decide +kernel) (by decide)
def projC15PInv0 : Projection 20 20 := pick [4,6,5,7,0,2,1,3,12,14,13,15,8,10,9,11,16,18,17,19] rfl (by decide +kernel) (by decide)
def projC15P1 : Projection 20 20 := pick [4,6,5,7,0,2,1,3,12,14,13,15,8,10,9,11,16,18,17,19] rfl (by decide +kernel) (by decide)
def projC15PInv1 : Projection 20 20 := pick [4,6,5,7,0,2,1,3,12,14,13,15,8,10,9,11,16,18,17,19] rfl (by decide +kernel) (by decide)
def projC15P2 : Projection 20 20 := pick [8,9,10,11,12,13,14,15,0,1,2,3,4,5,6,7,16,17,18,19] rfl (by decide +kernel) (by decide)
def projC15PInv2 : Projection 20 20 := pick [8,9,10,11,12,13,14,15,0,1,2,3,4,5,6,7,16,17,18,19] rfl (by decide +kernel) (by decide)
def projC15P3 : Projection 20 20 := pick [12,14,13,15,8,10,9,11,4,6,5,7,0,2,1,3,16,18,17,19] rfl (by decide +kernel) (by decide)
def projC15PInv3 : Projection 20 20 := pick [12,14,13,15,8,10,9,11,4,6,5,7,0,2,1,3,16,18,17,19] rfl (by decide +kernel) (by decide)
def projC15P4 : Projection 20 20 := pick [8,9,10,11,12,13,14,15,0,1,2,3,4,5,6,7,16,17,18,19] rfl (by decide +kernel) (by decide)
def projC15PInv4 : Projection 20 20 := pick [8,9,10,11,12,13,14,15,0,1,2,3,4,5,6,7,16,17,18,19] rfl (by decide +kernel) (by decide)
def projC15P5 : Projection 20 20 := pick [12,14,13,15,8,10,9,11,4,6,5,7,0,2,1,3,16,18,17,19] rfl (by decide +kernel) (by decide)
def projC15PInv5 : Projection 20 20 := pick [12,14,13,15,8,10,9,11,4,6,5,7,0,2,1,3,16,18,17,19] rfl (by decide +kernel) (by decide)
def projC16P0 : Projection 9 9 := pick [0,1,2,6,7,8,3,4,5] rfl (by decide +kernel) (by decide)
def projC16PInv0 : Projection 9 9 := pick [0,1,2,6,7,8,3,4,5] rfl (by decide +kernel) (by decide)
def projC16P1 : Projection 9 9 := pick [0,1,2,6,7,8,3,4,5] rfl (by decide +kernel) (by decide)
def projC16PInv1 : Projection 9 9 := pick [0,1,2,6,7,8,3,4,5] rfl (by decide +kernel) (by decide)
def projC16P2 : Projection 9 9 := pick [3,4,5,0,1,2,6,7,8] rfl (by decide +kernel) (by decide)
def projC16PInv2 : Projection 9 9 := pick [3,4,5,0,1,2,6,7,8] rfl (by decide +kernel) (by decide)
def projC16P3 : Projection 9 9 := pick [3,4,5,0,1,2,6,7,8] rfl (by decide +kernel) (by decide)
def projC16PInv3 : Projection 9 9 := pick [3,4,5,0,1,2,6,7,8] rfl (by decide +kernel) (by decide)
def projC16P4 : Projection 9 9 := pick [3,4,5,6,7,8,0,1,2] rfl (by decide +kernel) (by decide)
def projC16PInv4 : Projection 9 9 := pick [6,7,8,0,1,2,3,4,5] rfl (by decide +kernel) (by decide)
def projC16P5 : Projection 9 9 := pick [3,4,5,6,7,8,0,1,2] rfl (by decide +kernel) (by decide)
def projC16PInv5 : Projection 9 9 := pick [6,7,8,0,1,2,3,4,5] rfl (by decide +kernel) (by decide)
def projC16P6 : Projection 9 9 := pick [6,7,8,0,1,2,3,4,5] rfl (by decide +kernel) (by decide)
def projC16PInv6 : Projection 9 9 := pick [3,4,5,6,7,8,0,1,2] rfl (by decide +kernel) (by decide)
def projC16P7 : Projection 9 9 := pick [6,7,8,0,1,2,3,4,5] rfl (by decide +kernel) (by decide)
def projC16PInv7 : Projection 9 9 := pick [3,4,5,6,7,8,0,1,2] rfl (by decide +kernel) (by decide)
def projC16P8 : Projection 9 9 := pick [6,7,8,3,4,5,0,1,2] rfl (by decide +kernel) (by decide)
def projC16PInv8 : Projection 9 9 := pick [6,7,8,3,4,5,0,1,2] rfl (by decide +kernel) (by decide)
def projC16P9 : Projection 9 9 := pick [6,7,8,3,4,5,0,1,2] rfl (by decide +kernel) (by decide)
def projC16PInv9 : Projection 9 9 := pick [6,7,8,3,4,5,0,1,2] rfl (by decide +kernel) (by decide)
def projC17P0 : Projection 9 9 := pick [0,1,2,6,7,8,3,4,5] rfl (by decide +kernel) (by decide)
def projC17PInv0 : Projection 9 9 := pick [0,1,2,6,7,8,3,4,5] rfl (by decide +kernel) (by decide)
def projC17P1 : Projection 9 9 := pick [0,1,2,6,7,8,3,4,5] rfl (by decide +kernel) (by decide)
def projC17PInv1 : Projection 9 9 := pick [0,1,2,6,7,8,3,4,5] rfl (by decide +kernel) (by decide)
def projC17P2 : Projection 9 9 := pick [3,4,5,0,1,2,6,7,8] rfl (by decide +kernel) (by decide)
def projC17PInv2 : Projection 9 9 := pick [3,4,5,0,1,2,6,7,8] rfl (by decide +kernel) (by decide)
def projC17P3 : Projection 9 9 := pick [3,4,5,0,1,2,6,7,8] rfl (by decide +kernel) (by decide)
def projC17PInv3 : Projection 9 9 := pick [3,4,5,0,1,2,6,7,8] rfl (by decide +kernel) (by decide)
def projC17P4 : Projection 9 9 := pick [3,4,5,6,7,8,0,1,2] rfl (by decide +kernel) (by decide)
def projC17PInv4 : Projection 9 9 := pick [6,7,8,0,1,2,3,4,5] rfl (by decide +kernel) (by decide)
def projC17P5 : Projection 9 9 := pick [3,4,5,6,7,8,0,1,2] rfl (by decide +kernel) (by decide)
def projC17PInv5 : Projection 9 9 := pick [6,7,8,0,1,2,3,4,5] rfl (by decide +kernel) (by decide)
def projC17P6 : Projection 9 9 := pick [6,7,8,0,1,2,3,4,5] rfl (by decide +kernel) (by decide)
def projC17PInv6 : Projection 9 9 := pick [3,4,5,6,7,8,0,1,2] rfl (by decide +kernel) (by decide)
def projC17P7 : Projection 9 9 := pick [6,7,8,0,1,2,3,4,5] rfl (by decide +kernel) (by decide)
def projC17PInv7 : Projection 9 9 := pick [3,4,5,6,7,8,0,1,2] rfl (by decide +kernel) (by decide)
def projC17P8 : Projection 9 9 := pick [6,7,8,3,4,5,0,1,2] rfl (by decide +kernel) (by decide)
def projC17PInv8 : Projection 9 9 := pick [6,7,8,3,4,5,0,1,2] rfl (by decide +kernel) (by decide)
def projC17P9 : Projection 9 9 := pick [6,7,8,3,4,5,0,1,2] rfl (by decide +kernel) (by decide)
def projC17PInv9 : Projection 9 9 := pick [6,7,8,3,4,5,0,1,2] rfl (by decide +kernel) (by decide)
def projC18P0 : Projection 12 12 := pick [4,6,5,7,0,2,1,3,8,10,9,11] rfl (by decide +kernel) (by decide)
def projC18PInv0 : Projection 12 12 := pick [4,6,5,7,0,2,1,3,8,10,9,11] rfl (by decide +kernel) (by decide)
def projC18P1 : Projection 12 12 := pick [1,0,2,3,9,8,10,11,5,4,6,7] rfl (by decide +kernel) (by decide)
def projC18PInv1 : Projection 12 12 := pick [1,0,2,3,9,8,10,11,5,4,6,7] rfl (by decide +kernel) (by decide)
def projC18P2 : Projection 12 12 := pick [9,10,8,11,1,2,0,3,5,6,4,7] rfl (by decide +kernel) (by decide)
def projC18PInv2 : Projection 12 12 := pick [6,4,5,7,10,8,9,11,2,0,1,3] rfl (by decide +kernel) (by decide)
def projC18P3 : Projection 12 12 := pick [6,4,5,7,10,8,9,11,2,0,1,3] rfl (by decide +kernel) (by decide)
def projC18PInv3 : Projection 12 12 := pick [9,10,8,11,1,2,0,3,5,6,4,7] rfl (by decide +kernel) (by decide)
def projC18P4 : Projection 12 12 := pick [10,9,8,11,6,5,4,7,2,1,0,3] rfl (by decide +kernel) (by decide)
def projC18PInv4 : Projection 12 12 := pick [10,9,8,11,6,5,4,7,2,1,0,3] rfl (by decide +kernel) (by decide)
def projC18P5 : Projection 12 12 := pick [4,6,5,7,0,2,1,3,8,10,9,11] rfl (by decide +kernel) (by decide)
def projC18PInv5 : Projection 12 12 := pick [4,6,5,7,0,2,1,3,8,10,9,11] rfl (by decide +kernel) (by decide)
def projC18P6 : Projection 12 12 := pick [1,0,2,3,9,8,10,11,5,4,6,7] rfl (by decide +kernel) (by decide)
def projC18PInv6 : Projection 12 12 := pick [1,0,2,3,9,8,10,11,5,4,6,7] rfl (by decide +kernel) (by decide)
def projC18P7 : Projection 12 12 := pick [9,10,8,11,1,2,0,3,5,6,4,7] rfl (by decide +kernel) (by decide)
def projC18PInv7 : Projection 12 12 := pick [6,4,5,7,10,8,9,11,2,0,1,3] rfl (by decide +kernel) (by decide)
def projC18P8 : Projection 12 12 := pick [6,4,5,7,10,8,9,11,2,0,1,3] rfl (by decide +kernel) (by decide)
def projC18PInv8 : Projection 12 12 := pick [9,10,8,11,1,2,0,3,5,6,4,7] rfl (by decide +kernel) (by decide)
def projC18P9 : Projection 12 12 := pick [10,9,8,11,6,5,4,7,2,1,0,3] rfl (by decide +kernel) (by decide)
def projC18PInv9 : Projection 12 12 := pick [10,9,8,11,6,5,4,7,2,1,0,3] rfl (by decide +kernel) (by decide)
def projC18P10 : Projection 12 12 := pick [4,6,5,7,0,2,1,3,8,10,9,11] rfl (by decide +kernel) (by decide)
def projC18PInv10 : Projection 12 12 := pick [4,6,5,7,0,2,1,3,8,10,9,11] rfl (by decide +kernel) (by decide)
def projC18P11 : Projection 12 12 := pick [1,0,2,3,9,8,10,11,5,4,6,7] rfl (by decide +kernel) (by decide)
def projC18PInv11 : Projection 12 12 := pick [1,0,2,3,9,8,10,11,5,4,6,7] rfl (by decide +kernel) (by decide)
def projC18P12 : Projection 12 12 := pick [9,10,8,11,1,2,0,3,5,6,4,7] rfl (by decide +kernel) (by decide)
def projC18PInv12 : Projection 12 12 := pick [6,4,5,7,10,8,9,11,2,0,1,3] rfl (by decide +kernel) (by decide)
def projC18P13 : Projection 12 12 := pick [6,4,5,7,10,8,9,11,2,0,1,3] rfl (by decide +kernel) (by decide)
def projC18PInv13 : Projection 12 12 := pick [9,10,8,11,1,2,0,3,5,6,4,7] rfl (by decide +kernel) (by decide)
def projC18P14 : Projection 12 12 := pick [10,9,8,11,6,5,4,7,2,1,0,3] rfl (by decide +kernel) (by decide)
def projC18PInv14 : Projection 12 12 := pick [10,9,8,11,6,5,4,7,2,1,0,3] rfl (by decide +kernel) (by decide)
def projC18P15 : Projection 12 12 := pick [4,6,5,7,0,2,1,3,8,10,9,11] rfl (by decide +kernel) (by decide)
def projC18PInv15 : Projection 12 12 := pick [4,6,5,7,0,2,1,3,8,10,9,11] rfl (by decide +kernel) (by decide)
def projC18P16 : Projection 12 12 := pick [1,0,2,3,9,8,10,11,5,4,6,7] rfl (by decide +kernel) (by decide)
def projC18PInv16 : Projection 12 12 := pick [1,0,2,3,9,8,10,11,5,4,6,7] rfl (by decide +kernel) (by decide)
def projC18P17 : Projection 12 12 := pick [9,10,8,11,1,2,0,3,5,6,4,7] rfl (by decide +kernel) (by decide)
def projC18PInv17 : Projection 12 12 := pick [6,4,5,7,10,8,9,11,2,0,1,3] rfl (by decide +kernel) (by decide)
def projC18P18 : Projection 12 12 := pick [6,4,5,7,10,8,9,11,2,0,1,3] rfl (by decide +kernel) (by decide)
def projC18PInv18 : Projection 12 12 := pick [9,10,8,11,1,2,0,3,5,6,4,7] rfl (by decide +kernel) (by decide)
def projC18P19 : Projection 12 12 := pick [10,9,8,11,6,5,4,7,2,1,0,3] rfl (by decide +kernel) (by decide)
def projC18PInv19 : Projection 12 12 := pick [10,9,8,11,6,5,4,7,2,1,0,3] rfl (by decide +kernel) (by decide)
def projC18P20 : Projection 12 12 := pick [4,6,5,7,0,2,1,3,8,10,9,11] rfl (by decide +kernel) (by decide)
def projC18PInv20 : Projection 12 12 := pick [4,6,5,7,0,2,1,3,8,10,9,11] rfl (by decide +kernel) (by decide)
def projC18P21 : Projection 12 12 := pick [1,0,2,3,9,8,10,11,5,4,6,7] rfl (by decide +kernel) (by decide)
def projC18PInv21 : Projection 12 12 := pick [1,0,2,3,9,8,10,11,5,4,6,7] rfl (by decide +kernel) (by decide)
def projC18P22 : Projection 12 12 := pick [9,10,8,11,1,2,0,3,5,6,4,7] rfl (by decide +kernel) (by decide)
def projC18PInv22 : Projection 12 12 := pick [6,4,5,7,10,8,9,11,2,0,1,3] rfl (by decide +kernel) (by decide)
def projC18P23 : Projection 12 12 := pick [6,4,5,7,10,8,9,11,2,0,1,3] rfl (by decide +kernel) (by decide)
def projC18PInv23 : Projection 12 12 := pick [9,10,8,11,1,2,0,3,5,6,4,7] rfl (by decide +kernel) (by decide)
def projC18P24 : Projection 12 12 := pick [10,9,8,11,6,5,4,7,2,1,0,3] rfl (by decide +kernel) (by decide)
def projC18PInv24 : Projection 12 12 := pick [10,9,8,11,6,5,4,7,2,1,0,3] rfl (by decide +kernel) (by decide)
def projC18P25 : Projection 12 12 := pick [4,6,5,7,0,2,1,3,8,10,9,11] rfl (by decide +kernel) (by decide)
def projC18PInv25 : Projection 12 12 := pick [4,6,5,7,0,2,1,3,8,10,9,11] rfl (by decide +kernel) (by decide)
def projC18P26 : Projection 12 12 := pick [1,0,2,3,9,8,10,11,5,4,6,7] rfl (by decide +kernel) (by decide)
def projC18PInv26 : Projection 12 12 := pick [1,0,2,3,9,8,10,11,5,4,6,7] rfl (by decide +kernel) (by decide)
def projC18P27 : Projection 12 12 := pick [9,10,8,11,1,2,0,3,5,6,4,7] rfl (by decide +kernel) (by decide)
def projC18PInv27 : Projection 12 12 := pick [6,4,5,7,10,8,9,11,2,0,1,3] rfl (by decide +kernel) (by decide)
def projC18P28 : Projection 12 12 := pick [6,4,5,7,10,8,9,11,2,0,1,3] rfl (by decide +kernel) (by decide)
def projC18PInv28 : Projection 12 12 := pick [9,10,8,11,1,2,0,3,5,6,4,7] rfl (by decide +kernel) (by decide)
def projC18P29 : Projection 12 12 := pick [10,9,8,11,6,5,4,7,2,1,0,3] rfl (by decide +kernel) (by decide)
def projC18PInv29 : Projection 12 12 := pick [10,9,8,11,6,5,4,7,2,1,0,3] rfl (by decide +kernel) (by decide)
def projC19P0 : Projection 6 6 := pick [3,4,5,0,1,2] rfl (by decide +kernel) (by decide)
def projC19PInv0 : Projection 6 6 := pick [3,4,5,0,1,2] rfl (by decide +kernel) (by decide)
def projC19P1 : Projection 6 6 := pick [3,4,5,0,1,2] rfl (by decide +kernel) (by decide)
def projC19PInv1 : Projection 6 6 := pick [3,4,5,0,1,2] rfl (by decide +kernel) (by decide)
def projC19P2 : Projection 6 6 := pick [3,4,5,0,1,2] rfl (by decide +kernel) (by decide)
def projC19PInv2 : Projection 6 6 := pick [3,4,5,0,1,2] rfl (by decide +kernel) (by decide)
def projC19P3 : Projection 6 6 := pick [3,4,5,0,1,2] rfl (by decide +kernel) (by decide)
def projC19PInv3 : Projection 6 6 := pick [3,4,5,0,1,2] rfl (by decide +kernel) (by decide)
def projC19P4 : Projection 6 6 := pick [3,4,5,0,1,2] rfl (by decide +kernel) (by decide)
def projC19PInv4 : Projection 6 6 := pick [3,4,5,0,1,2] rfl (by decide +kernel) (by decide)
def projC19P5 : Projection 6 6 := pick [3,4,5,0,1,2] rfl (by decide +kernel) (by decide)
def projC19PInv5 : Projection 6 6 := pick [3,4,5,0,1,2] rfl (by decide +kernel) (by decide)
def projC20P0 : Projection 6 6 := pick [3,4,5,0,1,2] rfl (by decide +kernel) (by decide)
def projC20PInv0 : Projection 6 6 := pick [3,4,5,0,1,2] rfl (by decide +kernel) (by decide)
def projC20P1 : Projection 6 6 := pick [3,4,5,0,1,2] rfl (by decide +kernel) (by decide)
def projC20PInv1 : Projection 6 6 := pick [3,4,5,0,1,2] rfl (by decide +kernel) (by decide)
def projC20P2 : Projection 6 6 := pick [3,4,5,0,1,2] rfl (by decide +kernel) (by decide)
def projC20PInv2 : Projection 6 6 := pick [3,4,5,0,1,2] rfl (by decide +kernel) (by decide)
def projC20P3 : Projection 6 6 := pick [3,4,5,0,1,2] rfl (by decide +kernel) (by decide)
def projC20PInv3 : Projection 6 6 := pick [3,4,5,0,1,2] rfl (by decide +kernel) (by decide)
def projC20P4 : Projection 6 6 := pick [3,4,5,0,1,2] rfl (by decide +kernel) (by decide)
def projC20PInv4 : Projection 6 6 := pick [3,4,5,0,1,2] rfl (by decide +kernel) (by decide)
def projC20P5 : Projection 6 6 := pick [3,4,5,0,1,2] rfl (by decide +kernel) (by decide)
def projC20PInv5 : Projection 6 6 := pick [3,4,5,0,1,2] rfl (by decide +kernel) (by decide)
def projC21P0 : Projection 6 6 := pick [3,4,5,0,1,2] rfl (by decide +kernel) (by decide)
def projC21PInv0 : Projection 6 6 := pick [3,4,5,0,1,2] rfl (by decide +kernel) (by decide)
def projC21P1 : Projection 6 6 := pick [3,4,5,0,1,2] rfl (by decide +kernel) (by decide)
def projC21PInv1 : Projection 6 6 := pick [3,4,5,0,1,2] rfl (by decide +kernel) (by decide)
def projC21P2 : Projection 6 6 := pick [3,4,5,0,1,2] rfl (by decide +kernel) (by decide)
def projC21PInv2 : Projection 6 6 := pick [3,4,5,0,1,2] rfl (by decide +kernel) (by decide)
def projC21P3 : Projection 6 6 := pick [3,4,5,0,1,2] rfl (by decide +kernel) (by decide)
def projC21PInv3 : Projection 6 6 := pick [3,4,5,0,1,2] rfl (by decide +kernel) (by decide)
def projC21P4 : Projection 6 6 := pick [3,4,5,0,1,2] rfl (by decide +kernel) (by decide)
def projC21PInv4 : Projection 6 6 := pick [3,4,5,0,1,2] rfl (by decide +kernel) (by decide)
def projC21P5 : Projection 6 6 := pick [3,4,5,0,1,2] rfl (by decide +kernel) (by decide)
def projC21PInv5 : Projection 6 6 := pick [3,4,5,0,1,2] rfl (by decide +kernel) (by decide)
def projC22P0 : Projection 6 6 := pick [3,4,5,0,1,2] rfl (by decide +kernel) (by decide)
def projC22PInv0 : Projection 6 6 := pick [3,4,5,0,1,2] rfl (by decide +kernel) (by decide)
def projC22P1 : Projection 6 6 := pick [3,4,5,0,1,2] rfl (by decide +kernel) (by decide)
def projC22PInv1 : Projection 6 6 := pick [3,4,5,0,1,2] rfl (by decide +kernel) (by decide)
def projC22P2 : Projection 6 6 := pick [3,4,5,0,1,2] rfl (by decide +kernel) (by decide)
def projC22PInv2 : Projection 6 6 := pick [3,4,5,0,1,2] rfl (by decide +kernel) (by decide)
def projC22P3 : Projection 6 6 := pick [3,4,5,0,1,2] rfl (by decide +kernel) (by decide)
def projC22PInv3 : Projection 6 6 := pick [3,4,5,0,1,2] rfl (by decide +kernel) (by decide)
def projC22P4 : Projection 6 6 := pick [3,4,5,0,1,2] rfl (by decide +kernel) (by decide)
def projC22PInv4 : Projection 6 6 := pick [3,4,5,0,1,2] rfl (by decide +kernel) (by decide)
def projC22P5 : Projection 6 6 := pick [3,4,5,0,1,2] rfl (by decide +kernel) (by decide)
def projC22PInv5 : Projection 6 6 := pick [3,4,5,0,1,2] rfl (by decide +kernel) (by decide)
def projC23P0 : Projection 3 3 := pick [1,0,2] rfl (by decide +kernel) (by decide)
def projC23PInv0 : Projection 3 3 := pick [1,0,2] rfl (by decide +kernel) (by decide)
def projC23P1 : Projection 3 3 := pick [1,0,2] rfl (by decide +kernel) (by decide)
def projC23PInv1 : Projection 3 3 := pick [1,0,2] rfl (by decide +kernel) (by decide)
def projC23P2 : Projection 3 3 := pick [1,0,2] rfl (by decide +kernel) (by decide)
def projC23PInv2 : Projection 3 3 := pick [1,0,2] rfl (by decide +kernel) (by decide)
def projC23P3 : Projection 3 3 := pick [1,0,2] rfl (by decide +kernel) (by decide)
def projC23PInv3 : Projection 3 3 := pick [1,0,2] rfl (by decide +kernel) (by decide)
def projC23P4 : Projection 3 3 := pick [1,0,2] rfl (by decide +kernel) (by decide)
def projC23PInv4 : Projection 3 3 := pick [1,0,2] rfl (by decide +kernel) (by decide)
def projC23P5 : Projection 3 3 := pick [1,0,2] rfl (by decide +kernel) (by decide)
def projC23PInv5 : Projection 3 3 := pick [1,0,2] rfl (by decide +kernel) (by decide)
def projC24P0 : Projection 6 6 := pick [3,4,5,0,1,2] rfl (by decide +kernel) (by decide)
def projC24PInv0 : Projection 6 6 := pick [3,4,5,0,1,2] rfl (by decide +kernel) (by decide)
def projC24P1 : Projection 6 6 := pick [3,4,5,0,1,2] rfl (by decide +kernel) (by decide)
def projC24PInv1 : Projection 6 6 := pick [3,4,5,0,1,2] rfl (by decide +kernel) (by decide)
def projC24P2 : Projection 6 6 := pick [3,4,5,0,1,2] rfl (by decide +kernel) (by decide)
def projC24PInv2 : Projection 6 6 := pick [3,4,5,0,1,2] rfl (by decide +kernel) (by decide)
def projC24P3 : Projection 6 6 := pick [3,4,5,0,1,2] rfl (by decide +kernel) (by decide)
def projC24PInv3 : Projection 6 6 := pick [3,4,5,0,1,2] rfl (by decide +kernel) (by decide)
def projC24P4 : Projection 6 6 := pick [3,4,5,0,1,2] rfl (by decide +kernel) (by decide)
def projC24PInv4 : Projection 6 6 := pick [3,4,5,0,1,2] rfl (by decide +kernel) (by decide)
def projC24P5 : Projection 6 6 := pick [3,4,5,0,1,2] rfl (by decide +kernel) (by decide)
def projC24PInv5 : Projection 6 6 := pick [3,4,5,0,1,2] rfl (by decide +kernel) (by decide)
def projC25P0 : Projection 6 6 := pick [3,4,5,0,1,2] rfl (by decide +kernel) (by decide)
def projC25PInv0 : Projection 6 6 := pick [3,4,5,0,1,2] rfl (by decide +kernel) (by decide)
def projC25P1 : Projection 6 6 := pick [3,4,5,0,1,2] rfl (by decide +kernel) (by decide)
def projC25PInv1 : Projection 6 6 := pick [3,4,5,0,1,2] rfl (by decide +kernel) (by decide)
def projC25P2 : Projection 6 6 := pick [3,4,5,0,1,2] rfl (by decide +kernel) (by decide)
def projC25PInv2 : Projection 6 6 := pick [3,4,5,0,1,2] rfl (by decide +kernel) (by decide)
def projC25P3 : Projection 6 6 := pick [3,4,5,0,1,2] rfl (by decide +kernel) (by decide)
def projC25PInv3 : Projection 6 6 := pick [3,4,5,0,1,2] rfl (by decide +kernel) (by decide)
def projC25P4 : Projection 6 6 := pick [3,4,5,0,1,2] rfl (by decide +kernel) (by decide)
def projC25PInv4 : Projection 6 6 := pick [3,4,5,0,1,2] rfl (by decide +kernel) (by decide)
def projC25P5 : Projection 6 6 := pick [3,4,5,0,1,2] rfl (by decide +kernel) (by decide)
def projC25PInv5 : Projection 6 6 := pick [3,4,5,0,1,2] rfl (by decide +kernel) (by decide)
def projC26P0 : Projection 3 3 := pick [1,0,2] rfl (by decide +kernel) (by decide)
def projC26PInv0 : Projection 3 3 := pick [1,0,2] rfl (by decide +kernel) (by decide)
def projC26P1 : Projection 3 3 := pick [1,0,2] rfl (by decide +kernel) (by decide)
def projC26PInv1 : Projection 3 3 := pick [1,0,2] rfl (by decide +kernel) (by decide)
def projC26P2 : Projection 3 3 := pick [1,0,2] rfl (by decide +kernel) (by decide)
def projC26PInv2 : Projection 3 3 := pick [1,0,2] rfl (by decide +kernel) (by decide)
def projC26P3 : Projection 3 3 := pick [1,0,2] rfl (by decide +kernel) (by decide)
def projC26PInv3 : Projection 3 3 := pick [1,0,2] rfl (by decide +kernel) (by decide)
def projC26P4 : Projection 3 3 := pick [1,0,2] rfl (by decide +kernel) (by decide)
def projC26PInv4 : Projection 3 3 := pick [1,0,2] rfl (by decide +kernel) (by decide)
def projC26P5 : Projection 3 3 := pick [1,0,2] rfl (by decide +kernel) (by decide)
def projC26PInv5 : Projection 3 3 := pick [1,0,2] rfl (by decide +kernel) (by decide)
def projC27P0 : Projection 6 6 := pick [3,4,5,0,1,2] rfl (by decide +kernel) (by decide)
def projC27PInv0 : Projection 6 6 := pick [3,4,5,0,1,2] rfl (by decide +kernel) (by decide)
def projC27P1 : Projection 6 6 := pick [3,4,5,0,1,2] rfl (by decide +kernel) (by decide)
def projC27PInv1 : Projection 6 6 := pick [3,4,5,0,1,2] rfl (by decide +kernel) (by decide)
def projC27P2 : Projection 6 6 := pick [3,4,5,0,1,2] rfl (by decide +kernel) (by decide)
def projC27PInv2 : Projection 6 6 := pick [3,4,5,0,1,2] rfl (by decide +kernel) (by decide)
def projC27P3 : Projection 6 6 := pick [3,4,5,0,1,2] rfl (by decide +kernel) (by decide)
def projC27PInv3 : Projection 6 6 := pick [3,4,5,0,1,2] rfl (by decide +kernel) (by decide)
def projC27P4 : Projection 6 6 := pick [3,4,5,0,1,2] rfl (by decide +kernel) (by decide)
def projC27PInv4 : Projection 6 6 := pick [3,4,5,0,1,2] rfl (by decide +kernel) (by decide)
def projC27P5 : Projection 6 6 := pick [3,4,5,0,1,2] rfl (by decide +kernel) (by decide)
def projC27PInv5 : Projection 6 6 := pick [3,4,5,0,1,2] rfl (by decide +kernel) (by decide)
def projC28P0 : Projection 6 6 := pick [3,4,5,0,1,2] rfl (by decide +kernel) (by decide)
def projC28PInv0 : Projection 6 6 := pick [3,4,5,0,1,2] rfl (by decide +kernel) (by decide)
def projC28P1 : Projection 6 6 := pick [3,4,5,0,1,2] rfl (by decide +kernel) (by decide)
def projC28PInv1 : Projection 6 6 := pick [3,4,5,0,1,2] rfl (by decide +kernel) (by decide)
def projC28P2 : Projection 6 6 := pick [3,4,5,0,1,2] rfl (by decide +kernel) (by decide)
def projC28PInv2 : Projection 6 6 := pick [3,4,5,0,1,2] rfl (by decide +kernel) (by decide)
def projC28P3 : Projection 6 6 := pick [3,4,5,0,1,2] rfl (by decide +kernel) (by decide)
def projC28PInv3 : Projection 6 6 := pick [3,4,5,0,1,2] rfl (by decide +kernel) (by decide)
def projC28P4 : Projection 6 6 := pick [3,4,5,0,1,2] rfl (by decide +kernel) (by decide)
def projC28PInv4 : Projection 6 6 := pick [3,4,5,0,1,2] rfl (by decide +kernel) (by decide)
def projC28P5 : Projection 6 6 := pick [3,4,5,0,1,2] rfl (by decide +kernel) (by decide)
def projC28PInv5 : Projection 6 6 := pick [3,4,5,0,1,2] rfl (by decide +kernel) (by decide)
def projC29P0 : Projection 6 6 := pick [3,4,5,0,1,2] rfl (by decide +kernel) (by decide)
def projC29PInv0 : Projection 6 6 := pick [3,4,5,0,1,2] rfl (by decide +kernel) (by decide)
def projC29P1 : Projection 6 6 := pick [3,4,5,0,1,2] rfl (by decide +kernel) (by decide)
def projC29PInv1 : Projection 6 6 := pick [3,4,5,0,1,2] rfl (by decide +kernel) (by decide)
def projC29P2 : Projection 6 6 := pick [3,4,5,0,1,2] rfl (by decide +kernel) (by decide)
def projC29PInv2 : Projection 6 6 := pick [3,4,5,0,1,2] rfl (by decide +kernel) (by decide)
def projC29P3 : Projection 6 6 := pick [3,4,5,0,1,2] rfl (by decide +kernel) (by decide)
def projC29PInv3 : Projection 6 6 := pick [3,4,5,0,1,2] rfl (by decide +kernel) (by decide)
def projC29P4 : Projection 6 6 := pick [3,4,5,0,1,2] rfl (by decide +kernel) (by decide)
def projC29PInv4 : Projection 6 6 := pick [3,4,5,0,1,2] rfl (by decide +kernel) (by decide)
def projC29P5 : Projection 6 6 := pick [3,4,5,0,1,2] rfl (by decide +kernel) (by decide)
def projC29PInv5 : Projection 6 6 := pick [3,4,5,0,1,2] rfl (by decide +kernel) (by decide)
def projCut_top_0 : Projection 89 40 := pick [10,13,14,15,8,26,29,30,31,24,58,61,62,63,56,34,36,37,38,32,66,68,69,70,64,42,45,46,47,39,74,77,78,79,71,83,86,87,88,80] rfl (by decide +kernel) (by decide)
def projCut_top_1 : Projection 89 40 := pick [2,5,6,7,0,18,21,22,23,16,50,53,54,55,48,33,36,37,38,32,65,68,69,70,64,41,45,46,47,39,73,77,78,79,71,82,86,87,88,80] rfl (by decide +kernel) (by decide)
def projCut_top_2 : Projection 89 45 := pick [1,4,6,7,0,17,20,22,23,16,49,52,54,55,48,9,12,14,15,8,25,28,30,31,24,57,60,62,63,56,40,44,46,47,39,72,76,78,79,71,81,85,87,88,80] rfl (by decide +kernel) (by decide)
def projCut_top_3 : Projection 89 28 := pick [19,22,23,16,51,54,55,48,27,30,31,24,59,62,63,56,35,37,38,32,67,69,70,64,84,87,88,80] rfl (by decide +kernel) (by decide)
def projCut_top_4 : Projection 89 24 := pick [3,5,7,0,51,53,55,48,11,13,15,8,59,61,63,56,67,68,70,64,75,77,79,71] rfl (by decide +kernel) (by decide)
def projCut_top_5 : Projection 89 24 := pick [3,5,6,0,19,21,22,16,11,13,14,8,27,29,30,24,35,36,37,32,43,45,46,39] rfl (by decide +kernel) (by decide)
def projCut_top_6 : Projection 89 20 := pick [36,37,38,32,68,69,70,64,45,46,47,39,77,78,79,71,86,87,88,80] rfl (by decide +kernel) (by decide)
def projCut_top_7 : Projection 89 20 := pick [26,30,31,24,58,62,63,56,34,37,38,32,66,69,70,64,83,87,88,80] rfl (by decide +kernel) (by decide)
def projCut_top_8 : Projection 89 16 := pick [10,13,15,8,58,61,63,56,66,68,70,64,74,77,79,71] rfl (by decide +kernel) (by decide)
def projCut_top_9 : Projection 89 16 := pick [10,13,14,8,26,29,30,24,34,36,37,32,42,45,46,39] rfl (by decide +kernel) (by decide)
def projCut_top_10 : Projection 89 20 := pick [18,22,23,16,50,54,55,48,33,37,38,32,65,69,70,64,82,87,88,80] rfl (by decide +kernel) (by decide)
def projCut_top_11 : Projection 89 16 := pick [2,5,7,0,50,53,55,48,65,68,70,64,73,77,79,71] rfl (by decide +kernel) (by decide)
def projCut_top_12 : Projection 89 16 := pick [2,5,6,0,18,21,22,16,33,36,37,32,41,45,46,39] rfl (by decide +kernel) (by decide)
def projCut_top_13 : Projection 89 20 := pick [17,22,23,16,49,54,55,48,25,30,31,24,57,62,63,56,81,87,88,80] rfl (by decide +kernel) (by decide)
def projCut_top_14 : Projection 89 20 := pick [1,4,7,0,49,52,55,48,9,12,15,8,57,60,63,56,72,76,79,71] rfl (by decide +kernel) (by decide)
def projCut_top_15 : Projection 89 20 := pick [1,4,6,0,17,20,22,16,9,12,14,8,25,28,30,24,40,44,46,39] rfl (by decide +kernel) (by decide)
def projCut_top_16 : Projection 89 9 := pick [51,55,48,59,63,56,67,70,64] rfl (by decide +kernel) (by decide)
def projCut_top_17 : Projection 89 9 := pick [19,22,16,27,30,24,35,37,32] rfl (by decide +kernel) (by decide)
def projCut_top_18 : Projection 89 12 := pick [44,46,47,39,76,78,79,71,85,87,88,80] rfl (by decide +kernel) (by decide)
def projCut_top_19 : Projection 89 6 := pick [68,70,64,77,79,71] rfl (by decide +kernel) (by decide)
def projCut_top_20 : Projection 89 6 := pick [36,37,32,45,46,39] rfl (by decide +kernel) (by decide)
def projCut_top_21 : Projection 89 6 := pick [58,63,56,66,70,64] rfl (by decide +kernel) (by decide)
def projCut_top_22 : Projection 89 6 := pick [26,30,24,34,37,32] rfl (by decide +kernel) (by decide)
def projCut_top_23 : Projection 89 3 := pick [10,13,8] rfl (by decide +kernel) (by decide)
def projCut_top_24 : Projection 89 6 := pick [50,55,48,65,70,64] rfl (by decide +kernel) (by decide)
def projCut_top_25 : Projection 89 6 := pick [18,22,16,33,37,32] rfl (by decide +kernel) (by decide)
def projCut_top_26 : Projection 89 3 := pick [2,5,0] rfl (by decide +kernel) (by decide)
def projCut_top_27 : Projection 89 6 := pick [49,55,48,57,63,56] rfl (by decide +kernel) (by decide)
def projCut_top_28 : Projection 89 6 := pick [17,22,16,25,30,24] rfl (by decide +kernel) (by decide)
def projCut_top_29 : Projection 89 6 := pick [1,4,0,9,12,8] rfl (by decide +kernel) (by decide)
def projCut_7_21 : Projection 20 6 := pick [4,6,7,12,14,15] rfl (by decide +kernel) (by decide)
def projCut_7_22 : Projection 20 6 := pick [0,1,3,8,9,11] rfl (by decide +kernel) (by decide)
def projCut_15_28 : Projection 20 6 := pick [4,6,7,12,14,15] rfl (by decide +kernel) (by decide)
def projCut_15_29 : Projection 20 6 := pick [0,1,3,8,9,11] rfl (by decide +kernel) (by decide)
def projCut_14_27 : Projection 20 6 := pick [4,6,7,12,14,15] rfl (by decide +kernel) (by decide)
def projCut_14_29 : Projection 20 6 := pick [0,1,3,8,9,11] rfl (by decide +kernel) (by decide)
def projCut_13_27 : Projection 20 6 := pick [4,6,7,12,14,15] rfl (by decide +kernel) (by decide)
def projCut_13_28 : Projection 20 6 := pick [0,1,3,8,9,11] rfl (by decide +kernel) (by decide)
def projCut_10_24 : Projection 20 6 := pick [4,6,7,12,14,15] rfl (by decide +kernel) (by decide)
def projCut_10_25 : Projection 20 6 := pick [0,1,3,8,9,11] rfl (by decide +kernel) (by decide)
def projCut_6_19 : Projection 20 6 := pick [4,6,7,12,14,15] rfl (by decide +kernel) (by decide)
def projCut_6_20 : Projection 20 6 := pick [0,1,3,8,9,11] rfl (by decide +kernel) (by decide)
def projCut_11_19 : Projection 16 6 := pick [9,10,11,13,14,15] rfl (by decide +kernel) (by decide)
def projCut_11_24 : Projection 16 6 := pick [4,6,7,8,10,11] rfl (by decide +kernel) (by decide)
def projCut_11_26 : Projection 16 3 := pick [0,1,3] rfl (by decide +kernel) (by decide)
def projCut_8_19 : Projection 16 6 := pick [9,10,11,13,14,15] rfl (by decide +kernel) (by decide)
def projCut_8_21 : Projection 16 6 := pick [4,6,7,8,10,11] rfl (by decide +kernel) (by decide)
def projCut_8_23 : Projection 16 3 := pick [0,1,3] rfl (by decide +kernel) (by decide)
def projCut_9_20 : Projection 16 6 := pick [9,10,11,13,14,15] rfl (by decide +kernel) (by decide)
def projCut_9_22 : Projection 16 6 := pick [4,6,7,8,10,11] rfl (by decide +kernel) (by decide)
def projCut_9_23 : Projection 16 3 := pick [0,1,3] rfl (by decide +kernel) (by decide)
def projCut_12_20 : Projection 16 6 := pick [9,10,11,13,14,15] rfl (by decide +kernel) (by decide)
def projCut_12_25 : Projection 16 6 := pick [4,6,7,8,10,11] rfl (by decide +kernel) (by decide)
def projCut_12_26 : Projection 16 3 := pick [0,1,3] rfl (by decide +kernel) (by decide)
def projCut_3_16 : Projection 28 9 := pick [4,6,7,12,14,15,20,22,23] rfl (by decide +kernel) (by decide)
def projCut_3_17 : Projection 28 9 := pick [0,1,3,8,9,11,16,17,19] rfl (by decide +kernel) (by decide)
def projCut_2_13 : Projection 45 20 := pick [5,7,8,9,10,12,13,14,20,22,23,24,25,27,28,29,40,42,43,44] rfl (by decide +kernel) (by decide)
def projCut_2_14 : Projection 45 20 := pick [0,1,3,4,10,11,13,14,15,16,18,19,25,26,28,29,35,36,38,39] rfl (by decide +kernel) (by decide)
def projCut_2_15 : Projection 45 20 := pick [0,1,2,4,5,6,7,9,15,16,17,19,20,21,22,24,30,31,32,34] rfl (by decide +kernel) (by decide)
def projCut_2_18 : Projection 45 12 := pick [31,32,33,34,36,37,38,39,41,42,43,44] rfl (by decide +kernel) (by decide)
def projCut_2_27 : Projection 45 6 := pick [10,13,14,25,28,29] rfl (by decide +kernel) (by decide)
def projCut_2_28 : Projection 45 6 := pick [5,7,9,20,22,24] rfl (by decide +kernel) (by decide)
def projCut_2_29 : Projection 45 6 := pick [0,1,4,15,16,19] rfl (by decide +kernel) (by decide)
def projCut_1_6 : Projection 40 20 := pick [16,17,18,19,21,22,23,24,26,27,28,29,31,32,33,34,36,37,38,39] rfl (by decide +kernel) (by decide)
def projCut_1_10 : Projection 40 20 := pick [5,7,8,9,10,12,13,14,15,17,18,19,20,22,23,24,35,37,38,39] rfl (by decide +kernel) (by decide)
def projCut_1_11 : Projection 40 16 := pick [0,1,3,4,10,11,13,14,20,21,23,24,30,31,33,34] rfl (by decide +kernel) (by decide)
def projCut_1_12 : Projection 40 16 := pick [0,1,2,4,5,6,7,9,15,16,17,19,25,26,27,29] rfl (by decide +kernel) (by decide)
def projCut_1_19 : Projection 40 6 := pick [21,23,24,31,33,34] rfl (by decide +kernel) (by decide)
def projCut_1_20 : Projection 40 6 := pick [16,17,19,26,27,29] rfl (by decide +kernel) (by decide)
def projCut_1_24 : Projection 40 6 := pick [10,13,14,20,23,24] rfl (by decide +kernel) (by decide)
def projCut_1_25 : Projection 40 6 := pick [5,7,9,15,17,19] rfl (by decide +kernel) (by decide)
def projCut_1_26 : Projection 40 3 := pick [0,1,4] rfl (by decide +kernel) (by decide)
def projCut_5_17 : Projection 24 9 := pick [4,6,7,12,14,15,16,18,19] rfl (by decide +kernel) (by decide)
def projCut_5_20 : Projection 24 6 := pick [17,18,19,21,22,23] rfl (by decide +kernel) (by decide)
def projCut_4_16 : Projection 24 9 := pick [4,6,7,12,14,15,16,18,19] rfl (by decide +kernel) (by decide)
def projCut_4_19 : Projection 24 6 := pick [17,18,19,21,22,23] rfl (by decide +kernel) (by decide)
def projCut_0_6 : Projection 40 20 := pick [16,17,18,19,21,22,23,24,26,27,28,29,31,32,33,34,36,37,38,39] rfl (by decide +kernel) (by decide)
def projCut_0_7 : Projection 40 20 := pick [5,7,8,9,10,12,13,14,15,17,18,19,20,22,23,24,35,37,38,39] rfl (by decide +kernel) (by decide)
def projCut_0_8 : Projection 40 16 := pick [0,1,3,4,10,11,13,14,20,21,23,24,30,31,33,34] rfl (by decide +kernel) (by decide)
def projCut_0_9 : Projection 40 16 := pick [0,1,2,4,5,6,7,9,15,16,17,19,25,26,27,29] rfl (by decide +kernel) (by decide)
def projCut_0_19 : Projection 40 6 := pick [21,23,24,31,33,34] rfl (by decide +kernel) (by decide)
def projCut_0_20 : Projection 40 6 := pick [16,17,19,26,27,29] rfl (by decide +kernel) (by decide)
def projCut_0_21 : Projection 40 6 := pick [10,13,14,20,23,24] rfl (by decide +kernel) (by decide)
def projCut_0_22 : Projection 40 6 := pick [5,7,9,15,17,19] rfl (by decide +kernel) (by decide)
def projCut_0_23 : Projection 40 3 := pick [0,1,4] rfl (by decide +kernel) (by decide)
def fil0 : ℕ := 0x1110f0
def fil1 : ℕ := 0x1110ff
def fil2 : ℕ := 0x222f0f
def fil3 : ℕ := 0x444ff0
def fil4 : ℕ := 0xff
def fil5 : ℕ := 0x111110ff00
def fil6 : ℕ := 0x22222f0f0f
def fil7 : ℕ := 0x44444ff0f0
def fil8 : ℕ := 0x11111000ff
def fil9 : ℕ := 0x111110ffff
def fil10 : ℕ := 0x22222f0fff
def fil11 : ℕ := 0x22222f0f00
def fil12 : ℕ := 0x44444ff0ff
def fil13 : ℕ := 0x44444ff000
def fil14 : ℕ := 0x24121014141210141414140000000000000000000000
def fil15 : ℕ := 0x2c1614141c1614141c141c00000000ff000000ff00ff
def fil16 : ℕ := 0x341a181c141a181c141c14000000ff000000ff00ff00
def fil17 : ℕ := 0xb85c3c58585c3c5858585800007f0000007f00000000
def fil18 : ℕ := 0xc06020606060206060606000ff800000ff800000ffff
def fil19 : ℕ := 0x10080408080804080808081ff00000000ffffffff0000
def fil20 : ℕ := 0x20100810101008101010101ffffffffff000000000000
def fil21 : ℕ := 0x111110f0f0
def fil22 : ℕ := 0xffff
def fil23 : ℕ := 0x11111110ff0000
def fil24 : ℕ := 0x2222222f0f0f0f
def fil25 : ℕ := 0x4444444ff0f0f0
def fil26 : ℕ := 0x1111111000ffff
def fil27 : ℕ := 0x11111110ffffff
def fil28 : ℕ := 0x2222222f0fffff
def fil29 : ℕ := 0x2222222f0f0000
def fil30 : ℕ := 0x4444444ff0ffff
def fil31 : ℕ := 0x4444444ff00000
def fil32 : ℕ := 0xf801f
def fil33 : ℕ := 0x210842108420003fffffff
def fil34 : ℕ := 0x421084210840ffc00f801f
def fil35 : ℕ := 0x84210842109f07c1f003e0
def fil36 : ℕ := 0x108421084211ff83e007c00
def fil37 : ℕ := 0x6318c6318c60ffffffffff
def fil38 : ℕ := 0x210842108420003ff07fe0
def fil39 : ℕ := 0x421084210840ffc0000000
def fil40 : ℕ := 0x1f003e0
def fil41 : ℕ := 0xa5294a5294bf07ffffffff
def fil42 : ℕ := 0x210842108420003e0ffc1f
def fil43 : ℕ := 0x84210842109f07c0000000
def fil44 : ℕ := 0x3e007c00
def fil45 : ℕ := 0x1294a5294a53ff83fffffff
def fil46 : ℕ := 0x2108421084200001ff83ff
def fil47 : ℕ := 0x108421084211ff800000000
def fil48 : ℕ := 0x7c0000000
def fil49 : ℕ := 0xc6318c6318dfffc1ff83ff
def fil50 : ℕ := 0x421084210840f8000f801f
def fil51 : ℕ := 0x84210842109f0001f003e0
def fil52 : ℕ := 0xf800000000
def fil53 : ℕ := 0x14a5294a5295ffffe0ffc1f
def fil54 : ℕ := 0x42108421084007c00f801f
def fil55 : ℕ := 0x108421084211f003e007c00
def fil56 : ℕ := 0x1f0000000000
def fil57 : ℕ := 0x18c6318c6319ffffff07fe0
def fil58 : ℕ := 0x84210842108007c1f003e0
def fil59 : ℕ := 0x1084210842100f83e007c00
def fil60 : ℕ := 0x3c1e1c1c1c1e1c1c1c1c1c000000ffff0000ffffffff
def fil61 : ℕ := 0xff00
def fil62 : ℕ := 0x33333f0f0f
def fil63 : ℕ := 0x55555ff0f0
def fil64 : ℕ := 0xf
def fil65 : ℕ := 0x111100ff
def fil66 : ℕ := 0x2222f00f
def fil67 : ℕ := 0x33330f00
def fil68 : ℕ := 0x1f
def fil69 : ℕ := 0x8421084210000007fff
def fil70 : ℕ := 0x108421084207fe00001f
def fil71 : ℕ := 0x18c6318c630001ff8000
def fil72 : ℕ := 0x2108421084f83e0f83e0
def fil73 : ℕ := 0x4210842108ffc1f07c00
def fil74 : ℕ := 0x7fe007fff
def fil75 : ℕ := 0x18c6318c6307fe007fff
def fil76 : ℕ := 0x39ce739ce7f83e0f83e0
def fil77 : ℕ := 0x5ad6b5ad6bffc1f07c00
def fil78 : ℕ := 0x7fff
def fil79 : ℕ := 0x210842108420003fff8000
def fil80 : ℕ := 0xf8000
def fil81 : ℕ := 0x6318c6318c60ffffff801f
def fil82 : ℕ := 0x210842108420003ff00000
def fil83 : ℕ := 0x421084210840ffc000001f
def fil84 : ℕ := 0x1f00000
def fil85 : ℕ := 0xa5294a5294bf07ffff83e0
def fil86 : ℕ := 0x210842108420003e0f8000
def fil87 : ℕ := 0x84210842109f07c00003e0
def fil88 : ℕ := 0x3e000000
def fil89 : ℕ := 0x1294a5294a53ff83ffffc00
def fil90 : ℕ := 0x2108421084200001ff8000
def fil91 : ℕ := 0x108421084211ff800007c00
def fil92 : ℕ := 0xff0000
def fil93 : ℕ := 0x3333333f0f0f0f
def fil94 : ℕ := 0x5555555ff0f0f0
def fil95 : ℕ := 0x421084210840ffc00fffff
def fil96 : ℕ := 0x7fe0
def fil97 : ℕ := 0x421084210840ffc00f8000
def fil98 : ℕ := 0x3e0
def fil99 : ℕ := 0x84210842109f07c1f07fff
def fil100 : ℕ := 0x7c1f
def fil101 : ℕ := 0x84210842109f07c1f00000
def fil102 : ℕ := 0x7c00
def fil103 : ℕ := 0x108421084211ff83e007fff
def fil104 : ℕ := 0x3ff
def fil105 : ℕ := 0x108421084211ff83e000000
def fil106 : ℕ := 0x80404000804040008000800000000ff000000ff00ff
def fil107 : ℕ := 0x1008080800080808000800000000ff000000ff00ff00
def fil108 : ℕ := 0x28141410181414101810180000000000000000000000
def fil109 : ℕ := 0x10842108420000000000
def fil110 : ℕ := 0x18c6318c630001ffffff
def fil111 : ℕ := 0x18c6318c6307ffff801f
def fil112 : ℕ := 0x7fe00001f
def fil113 : ℕ := 0x18c6318c6307ffffffff
def fil114 : ℕ := 0x7fe000000
def fil115 : ℕ := 0x18c6318c630001ffffe0
def fil116 : ℕ := 0x2108421084fffe0f83ff
def fil117 : ℕ := 0x7c000001f
def fil118 : ℕ := 0x2108421084f8000f83e0
def fil119 : ℕ := 0x4210842108fffff07c1f
def fil120 : ℕ := 0x3e00001f
def fil121 : ℕ := 0x4210842108f801f07c00
def fil122 : ℕ := 0x2108421084200000000000
def fil123 : ℕ := 0x2108421084200000007fff
def fil124 : ℕ := 0x3fff8000
def fil125 : ℕ := 0x6318c6318c60ffc00fffff
def fil126 : ℕ := 0x2108421084200000007fe0
def fil127 : ℕ := 0xa5294a5294bf07c1f07fff
def fil128 : ℕ := 0x2108421084200000007c1f
def fil129 : ℕ := 0x1294a5294a53ff83e007fff
def fil130 : ℕ := 0x21084210842000000003ff
def fil131 : ℕ := 0xbc5e3c5c5c5e3c5c5c5c5c00007f00ff007f00ff00ff
def fil132 : ℕ := 0x2222f000
def fil133 : ℕ := 0x33330fff
def fil134 : ℕ := 0x4444fff0
def fil135 : ℕ := 0x8421084210000007fe0
def fil136 : ℕ := 0x108421084207fe000000
def fil137 : ℕ := 0x10842108420001ff8000
def fil138 : ℕ := 0x294a5294a5f83e0fffff
def fil139 : ℕ := 0x8421084210000007c1f
def fil140 : ℕ := 0x2108421084f83e0f8000
def fil141 : ℕ := 0x4a5294a529ffc1f07fff
def fil142 : ℕ := 0x84210842100000003ff
def fil143 : ℕ := 0x4210842108ffc1f00000
def fil144 : ℕ := 0x1084210842000000001f
def fil145 : ℕ := 0x8421084210001ffffe0
def fil146 : ℕ := 0x318c6318c6fffe0f83ff
def fil147 : ℕ := 0x108421084207c000001f
def fil148 : ℕ := 0x5294a5294afffff07c1f
def fil149 : ℕ := 0x1084210842003e00001f
def fil150 : ℕ := 0xf83e0
def fil151 : ℕ := 0x39ce739ce7f83fffffff
def fil152 : ℕ := 0x18c6318c630001f07c1f
def fil153 : ℕ := 0x2108421084f83e000000
def fil154 : ℕ := 0x1f07c00
def fil155 : ℕ := 0x5ad6b5ad6bffc1ffffff
def fil156 : ℕ := 0x18c6318c6300000f83ff
def fil157 : ℕ := 0x4210842108ffc0000000
def fil158 : ℕ := 0x6318c6318cffffffffe0
def fil159 : ℕ := 0x2108421084003e0f83e0
def fil160 : ℕ := 0x421084210807c1f07c00
def fil161 : ℕ := 0x247
def fil162 : ℕ := 0x278
def fil163 : ℕ := 0xf0
def fil164 : ℕ := 0x108421084207fe007fff
def fil165 : ℕ := 0x2108421084f83e0fffff
def fil166 : ℕ := 0x4210842108ffc1f07fff
def fil167 : ℕ := 0x18c6318c6307ffff8000
def fil168 : ℕ := 0x40200040402000404040400000000ff000000ff00ff
def fil169 : ℕ := 0x11111110ff00ff
def fil170 : ℕ := 0xff00ff
def fil171 : ℕ := 0x1111111000ff00
def fil172 : ℕ := 0x108421084207ffff801f
def fil173 : ℕ := 0x1ff8000
def fil174 : ℕ := 0x318c6318c6f83fff83e0
def fil175 : ℕ := 0x10842108420001f00000
def fil176 : ℕ := 0x2108421084f83e0003e0
def fil177 : ℕ := 0x5294a5294affc1fffc00
def fil178 : ℕ := 0x108421084200000f8000
def fil179 : ℕ := 0x4210842108ffc0007c00
def fil180 : ℕ := 0x904828484048284840484000007f0000007f00000000
def fil181 : ℕ := 0x33333f0fff
def fil182 : ℕ := 0x21084210842000000f8000
def fil183 : ℕ := 0x3ff00000
def fil184 : ℕ := 0x421084210840ffc0007fff
def fil185 : ℕ := 0x7c00003e0
def fil186 : ℕ := 0xe739ce739cffffc1ffffff
def fil187 : ℕ := 0x6318c6318c60f8000ffc1f
def fil188 : ℕ := 0x84210842109f0001f00000
def fil189 : ℕ := 0xf800007c00
def fil190 : ℕ := 0x16b5ad6b5ad7ffffe0fffff
def fil191 : ℕ := 0x6318c6318c6007c00f83ff
def fil192 : ℕ := 0x108421084211f003e000000
def fil193 : ℕ := 0xec7634747c7634747c747c00ff8000ffff8000ffffff
def fil194 : ℕ := 0x2c1614141c1614141c141c00000000ff000000ff0000
def fil195 : ℕ := 0x33333f0f00
def fil196 : ℕ := 0x7
def fil197 : ℕ := 0x9238
def fil198 : ℕ := 0x93c0
def fil199 : ℕ := 0x111111100000ff
def fil200 : ℕ := 0x6318c6318c60ffffff8000
def fil201 : ℕ := 0xc6318c6318dfffc1ff83e0
def fil202 : ℕ := 0x421084210840f8000f8000
def fil203 : ℕ := 0x14a5294a5295ffffe0ffc00
def fil204 : ℕ := 0x42108421084007c00f8000
def fil205 : ℕ := 0xc06020606060206060606000ff800000ff800000ff00
def fil206 : ℕ := 0x55555ff0ff
def fil207 : ℕ := 0x3333333f0f0fff
def fil208 : ℕ := 0x2222222f0f0fff
def fil209 : ℕ := 0x39ce739ce7f83e0fffff
def fil210 : ℕ := 0x12c9654949c9654949c949dff000000ffffffffff00ff
def fil211 : ℕ := 0x111111000000
def fil212 : ℕ := 0x1111110000ff
def fil213 : ℕ := 0x11111100ff00
def fil214 : ℕ := 0x222222f00f0f
def fil215 : ℕ := 0x3333330f0000
def fil216 : ℕ := 0xf0f
def fil217 : ℕ := 0x11111100ffff
def fil218 : ℕ := 0x2108421084200001f00000
def fil219 : ℕ := 0x3e0f8000
def fil220 : ℕ := 0x84210842109f07c0007fff
def fil221 : ℕ := 0xa5294a5294bf0001f07fe0
def fil222 : ℕ := 0x1f0000007c00
def fil223 : ℕ := 0x1ad6b5ad6b5bffffff07fff
def fil224 : ℕ := 0xa5294a5294a007c1f003ff
def fil225 : ℕ := 0x1084210842100f83e000000
def fil226 : ℕ := 0x2c1614141c1614141c141c00000000ff0000000000ff
def fil227 : ℕ := 0x55555ff000
def fil228 : ℕ := 0x2222222f0f0f00
def fil229 : ℕ := 0x3333333f0f0f00
def fil230 : ℕ := 0x39ce739ce7f83e0f8000
def fil231 : ℕ := 0x10080408080804080808081ff00000000ffffff000000
def fil232 : ℕ := 0xff000000000000
def fil233 : ℕ := 0x22d1695151d1695151d151dffffffffff000000ff00ff
def fil234 : ℕ := 0x2c1614141c1614141c141c0000000000000000ff00ff
def fil235 : ℕ := 0x20100810101008101010101ffffffff00000000000000
def fil236 : ℕ := 0x30181818101818181018100000000000000000000000
def fil237 : ℕ := 0xbc5e3c5c5c5e3c5c5c5c5c00007fff00007fff00ff00
def fil238 : ℕ := 0x402000404020004040404000000ff000000ff00ff00
def fil239 : ℕ := 0x884424404844244048404800007f0000007f00000000
def fil240 : ℕ := 0xf47a387c747a387c747c7400ff80ff00ff80ff00ffff
def fil241 : ℕ := 0x341a181c141a181c141c14000000ff000000ff000000
def fil242 : ℕ := 0xc06020606060206060606000ff800000ff80000000ff
def fil243 : ℕ := 0xff000000
def fil244 : ℕ := 0x1349a589c949a589c949c95ff0000ff00ffffffffff00
def fil245 : ℕ := 0x341a181c141a181c141c14000000ff0000000000ff00
def fil246 : ℕ := 0x10080408080804080808081ff00000000ffff00ff0000
def fil247 : ℕ := 0xff00000000000000
def fil248 : ℕ := 0x2351a991d151a991d151d15ffffffffff0000ff00ff00
def fil249 : ℕ := 0x341a181c141a181c141c1400000000000000ff00ff00
def fil250 : ℕ := 0x20100810101008101010101ffffff00ff000000000000
def fil251 : ℕ := 0x80402040404020404040400000000000000000000000
def fil252 : ℕ := 0x111100f0
def fil253 : ℕ := 0x3333ff0f
def fil254 : ℕ := 0xf87c3c78787c3c7878787800ffff0000ffff0000ffff
def fil255 : ℕ := 0x8421084210000000000
def fil256 : ℕ := 0x1111110f0000
def fil257 : ℕ := 0x444444fff0f0
def fil258 : ℕ := 0xf0000
def fil259 : ℕ := 0x333333f00f0f
def fil260 : ℕ := 0x555555fff0f0
def fil261 : ℕ := 0x8421084210001ff8000
def fil262 : ℕ := 0x381c1c18181c1c1818181800007f0000007f00000000
def fil263 : ℕ := 0xf000
def fil264 : ℕ := 0x9207
def fil265 : ℕ := 0xf00f00
def fil266 : ℕ := 0x111111f00fff
def fil267 : ℕ := 0x1111110000f0
def fil268 : ℕ := 0x111111f0ff0f
def fil269 : ℕ := 0x84210842107fe007fff
def fil270 : ℕ := 0x22222fff0f
def fil271 : ℕ := 0x402000202020002020202000ff800000ff800000ffff
def fil272 : ℕ := 0x7f00000000
def fil273 : ℕ := 0x33333fff0f
def fil274 : ℕ := 0x3333333fff0f0f
def fil275 : ℕ := 0x2222222fff0f0f
def fil276 : ℕ := 0x39ce739ce7f83fff83e0
def fil277 : ℕ := 0x2108421084f83fff83e0
def fil278 : ℕ := 0x1b8dc7cd8d8dc7cd8d8d8d9ff007f0000ffffffff0000
def fil279 : ℕ := 0xb85c3c58585c3c5858585800007f0000000000000000
def fil280 : ℕ := 0x22222f000f
def fil281 : ℕ := 0x33333f000f
def fil282 : ℕ := 0x2222222f000f0f
def fil283 : ℕ := 0x3333333f000f0f
def fil284 : ℕ := 0x39ce739ce7f83e0003e0
def fil285 : ℕ := 0x10080408080804080808081ff00000000ff80ffff0000
def fil286 : ℕ := 0x7f0000000000000000
def fil287 : ℕ := 0x2b95cbd59595cbd59595959ffffffffff007f00000000
def fil288 : ℕ := 0xb85c3c58585c3c585858580000000000007f00000000
def fil289 : ℕ := 0x20100810101008101010101ffff80ffff000000000000
def fil290 : ℕ := 0xff8000000000
def fil291 : ℕ := 0x2108421084200000007c00
def fil292 : ℕ := 0xc6318c6318dfffc1ff8000
def fil293 : ℕ := 0xe739ce739cffffffff83ff
def fil294 : ℕ := 0x210842108420003e000000
def fil295 : ℕ := 0xc6318c6318dfffc00003ff
def fil296 : ℕ := 0x1ff800000000
def fil297 : ℕ := 0x1ce739ce739dfffffffffff
def fil298 : ℕ := 0xc6318c6318c007c1ff83ff
def fil299 : ℕ := 0x1084210842100003e007c00
def fil300 : ℕ := 0x1c0e060e0e0e060e0e0e0e1ffff800000ffffffffffff
def fil301 : ℕ := 0xc06020606060206060606000ff80000000000000ffff
def fil302 : ℕ := 0x10080408080804080808081ff00000000007fffff0000
def fil303 : ℕ := 0xff800000000000000000
def fil304 : ℕ := 0x2c160a1616160a161616161ffffffffffff800000ffff
def fil305 : ℕ := 0xc0602060606020606060600000000000ff800000ffff
def fil306 : ℕ := 0x20100810101008101010101ff007fffff000000000000
def fil307 : ℕ := 0x1ff00000000000000000000
def fil308 : ℕ := 0x30180c1818180c181818181ffffffffffffffffff0000
def fil309 : ℕ := 0x100804080808040808080800000000000ffffffff0000
def fil310 : ℕ := 0x2010081010100810101010000ffffffff000000000000
def etat0 : List ℕ := [fil0,fil1,fil2,fil3]
def etat1 : List ℕ := [fil4,fil5,fil6,fil7]
def etat2 : List ℕ := [fil8,fil9,fil6,fil7]
def etat3 : List ℕ := [fil8,fil5,fil10,fil7]
def etat4 : List ℕ := [fil8,fil5,fil11,fil7]
def etat5 : List ℕ := [fil8,fil5,fil6,fil12]
def etat6 : List ℕ := [fil8,fil5,fil6,fil13]
def etat7 : List ℕ := [fil4,fil9,fil6,fil7]
def etat8 : List ℕ := [fil1,fil2,fil3]
def etat9 : List ℕ := [fil14,fil15,fil16,fil17,fil18,fil19,fil20]
def etat10 : List ℕ := [fil21,fil9,fil6,fil7]
def etat11 : List ℕ := [fil22,fil23,fil24,fil25]
def etat12 : List ℕ := [fil26,fil27,fil24,fil25]
def etat13 : List ℕ := [fil26,fil23,fil28,fil25]
def etat14 : List ℕ := [fil26,fil23,fil29,fil25]
def etat15 : List ℕ := [fil26,fil23,fil24,fil30]
def etat16 : List ℕ := [fil26,fil23,fil24,fil31]
def etat17 : List ℕ := [fil22,fil27,fil24,fil25]
def etat18 : List ℕ := [fil32,fil33,fil34,fil35,fil36]
def etat19 : List ℕ := [fil33,fil34,fil37,fil35,fil36]
def etat20 : List ℕ := [fil38,fil33,fil34,fil35,fil36]
def etat21 : List ℕ := [fil33,fil39,fil34,fil35,fil36]
def etat22 : List ℕ := [fil40,fil33,fil34,fil35,fil36]
def etat23 : List ℕ := [fil33,fil34,fil35,fil41,fil36]
def etat24 : List ℕ := [fil42,fil33,fil34,fil35,fil36]
def etat25 : List ℕ := [fil33,fil34,fil43,fil35,fil36]
def etat26 : List ℕ := [fil44,fil33,fil34,fil35,fil36]
def etat27 : List ℕ := [fil33,fil34,fil35,fil36,fil45]
def etat28 : List ℕ := [fil46,fil33,fil34,fil35,fil36]
def etat29 : List ℕ := [fil33,fil34,fil35,fil47,fil36]
def etat30 : List ℕ := [fil48,fil33,fil34,fil35,fil36]
def etat31 : List ℕ := [fil33,fil34,fil35,fil49,fil36]
def etat32 : List ℕ := [fil33,fil50,fil34,fil35,fil36]
def etat33 : List ℕ := [fil33,fil34,fil51,fil35,fil36]
def etat34 : List ℕ := [fil52,fil33,fil34,fil35,fil36]
def etat35 : List ℕ := [fil33,fil34,fil35,fil36,fil53]
def etat36 : List ℕ := [fil33,fil54,fil34,fil35,fil36]
def etat37 : List ℕ := [fil33,fil34,fil35,fil55,fil36]
def etat38 : List ℕ := [fil56,fil33,fil34,fil35,fil36]
def etat39 : List ℕ := [fil33,fil34,fil35,fil36,fil57]
def etat40 : List ℕ := [fil33,fil34,fil58,fil35,fil36]
def etat41 : List ℕ := [fil33,fil34,fil35,fil59,fil36]
def etat42 : List ℕ := [fil33,fil34,fil35,fil36]
def etat43 : List ℕ := [fil60,fil17,fil18,fil19,fil20]
def etat44 : List ℕ := [fil61,fil8,fil6,fil7]
def etat45 : List ℕ := [fil8,fil5,fil62,fil7]
def etat46 : List ℕ := [fil8,fil5,fil6,fil63]
def etat47 : List ℕ := [fil64,fil65,fil66,fil67]
def etat48 : List ℕ := [fil68,fil69,fil70,fil71,fil72,fil73]
def etat49 : List ℕ := [fil74,fil71,fil72,fil73]
def etat50 : List ℕ := [fil71,fil75,fil76,fil73]
def etat51 : List ℕ := [fil71,fil75,fil72,fil77]
def etat52 : List ℕ := [fil78,fil33,fil34,fil35,fil36]
def etat53 : List ℕ := [fil78,fil79,fil34,fil35,fil36]
def etat54 : List ℕ := [fil78,fil79,fil33,fil34,fil35,fil36]
def etat55 : List ℕ := [fil80,fil33,fil34,fil35,fil36]
def etat56 : List ℕ := [fil80,fil79,fil33,fil34,fil35,fil36]
def etat57 : List ℕ := [fil33,fil34,fil81,fil35,fil36]
def etat58 : List ℕ := [fil79,fil33,fil34,fil81,fil35,fil36]
def etat59 : List ℕ := [fil82,fil33,fil34,fil35,fil36]
def etat60 : List ℕ := [fil82,fil79,fil33,fil34,fil35,fil36]
def etat61 : List ℕ := [fil33,fil83,fil34,fil35,fil36]
def etat62 : List ℕ := [fil79,fil33,fil83,fil34,fil35,fil36]
def etat63 : List ℕ := [fil84,fil33,fil34,fil35,fil36]
def etat64 : List ℕ := [fil84,fil79,fil33,fil34,fil35,fil36]
def etat65 : List ℕ := [fil33,fil34,fil35,fil85,fil36]
def etat66 : List ℕ := [fil79,fil33,fil34,fil35,fil85,fil36]
def etat67 : List ℕ := [fil86,fil33,fil34,fil35,fil36]
def etat68 : List ℕ := [fil86,fil79,fil33,fil34,fil35,fil36]
def etat69 : List ℕ := [fil33,fil34,fil87,fil35,fil36]
def etat70 : List ℕ := [fil79,fil33,fil34,fil87,fil35,fil36]
def etat71 : List ℕ := [fil88,fil33,fil34,fil35,fil36]
def etat72 : List ℕ := [fil88,fil79,fil33,fil34,fil35,fil36]
def etat73 : List ℕ := [fil33,fil34,fil35,fil36,fil89]
def etat74 : List ℕ := [fil79,fil33,fil34,fil35,fil36,fil89]
def etat75 : List ℕ := [fil90,fil33,fil34,fil35,fil36]
def etat76 : List ℕ := [fil90,fil79,fil33,fil34,fil35,fil36]
def etat77 : List ℕ := [fil33,fil34,fil35,fil91,fil36]
def etat78 : List ℕ := [fil79,fil33,fil34,fil35,fil91,fil36]
def etat79 : List ℕ := [fil32,fil79,fil33,fil34,fil35,fil36]
def etat80 : List ℕ := [fil79,fil33,fil34,fil37,fil35,fil36]
def etat81 : List ℕ := [fil38,fil79,fil33,fil34,fil35,fil36]
def etat82 : List ℕ := [fil79,fil33,fil39,fil34,fil35,fil36]
def etat83 : List ℕ := [fil40,fil79,fil33,fil34,fil35,fil36]
def etat84 : List ℕ := [fil79,fil33,fil34,fil35,fil41,fil36]
def etat85 : List ℕ := [fil42,fil79,fil33,fil34,fil35,fil36]
def etat86 : List ℕ := [fil79,fil33,fil34,fil43,fil35,fil36]
def etat87 : List ℕ := [fil44,fil79,fil33,fil34,fil35,fil36]
def etat88 : List ℕ := [fil79,fil33,fil34,fil35,fil36,fil45]
def etat89 : List ℕ := [fil46,fil79,fil33,fil34,fil35,fil36]
def etat90 : List ℕ := [fil79,fil33,fil34,fil35,fil47,fil36]
def etat91 : List ℕ := [fil48,fil79,fil33,fil34,fil35,fil36]
def etat92 : List ℕ := [fil79,fil33,fil34,fil35,fil49,fil36]
def etat93 : List ℕ := [fil79,fil33,fil50,fil34,fil35,fil36]
def etat94 : List ℕ := [fil79,fil33,fil34,fil51,fil35,fil36]
def etat95 : List ℕ := [fil52,fil79,fil33,fil34,fil35,fil36]
def etat96 : List ℕ := [fil79,fil33,fil34,fil35,fil36,fil53]
def etat97 : List ℕ := [fil79,fil33,fil54,fil34,fil35,fil36]
def etat98 : List ℕ := [fil79,fil33,fil34,fil35,fil55,fil36]
def etat99 : List ℕ := [fil56,fil79,fil33,fil34,fil35,fil36]
def etat100 : List ℕ := [fil79,fil33,fil34,fil35,fil36,fil57]
def etat101 : List ℕ := [fil79,fil33,fil34,fil58,fil35,fil36]
def etat102 : List ℕ := [fil79,fil33,fil34,fil35,fil59,fil36]
def etat103 : List ℕ := [fil79,fil33,fil34,fil35,fil36]
def etat104 : List ℕ := [fil16,fil60,fil17,fil18,fil19,fil20]
def etat105 : List ℕ := [fil15,fil60,fil17,fil18,fil19,fil20]
def etat106 : List ℕ := [fil15,fil16,fil60,fil17,fil18,fil19,fil20]
def etat107 : List ℕ := [fil92,fil26,fil24,fil25]
def etat108 : List ℕ := [fil26,fil23,fil93,fil25]
def etat109 : List ℕ := [fil26,fil23,fil24,fil94]
def etat110 : List ℕ := [fil68,fil78,fil79,fil34,fil35,fil36]
def etat111 : List ℕ := [fil78,fil79,fil95,fil35,fil36]
def etat112 : List ℕ := [fil78,fil79,fil34,fil95,fil35,fil36]
def etat113 : List ℕ := [fil96,fil78,fil79,fil34,fil35,fil36]
def etat114 : List ℕ := [fil78,fil79,fil97,fil35,fil36]
def etat115 : List ℕ := [fil78,fil79,fil97,fil34,fil35,fil36]
def etat116 : List ℕ := [fil98,fil78,fil79,fil34,fil35,fil36]
def etat117 : List ℕ := [fil78,fil79,fil34,fil99,fil36]
def etat118 : List ℕ := [fil78,fil79,fil34,fil35,fil99,fil36]
def etat119 : List ℕ := [fil100,fil78,fil79,fil34,fil35,fil36]
def etat120 : List ℕ := [fil78,fil79,fil34,fil101,fil36]
def etat121 : List ℕ := [fil78,fil79,fil34,fil101,fil35,fil36]
def etat122 : List ℕ := [fil102,fil78,fil79,fil34,fil35,fil36]
def etat123 : List ℕ := [fil78,fil79,fil34,fil35,fil103]
def etat124 : List ℕ := [fil78,fil79,fil34,fil35,fil36,fil103]
def etat125 : List ℕ := [fil104,fil78,fil79,fil34,fil35,fil36]
def etat126 : List ℕ := [fil78,fil79,fil34,fil35,fil105]
def etat127 : List ℕ := [fil78,fil79,fil34,fil35,fil105,fil36]
def etat128 : List ℕ := [fil78,fil80,fil79,fil34,fil35,fil36]
def etat129 : List ℕ := [fil78,fil79,fil34,fil81,fil35,fil36]
def etat130 : List ℕ := [fil78,fil82,fil79,fil34,fil35,fil36]
def etat131 : List ℕ := [fil78,fil79,fil83,fil34,fil35,fil36]
def etat132 : List ℕ := [fil78,fil84,fil79,fil34,fil35,fil36]
def etat133 : List ℕ := [fil78,fil79,fil34,fil35,fil85,fil36]
def etat134 : List ℕ := [fil78,fil86,fil79,fil34,fil35,fil36]
def etat135 : List ℕ := [fil78,fil79,fil34,fil87,fil35,fil36]
def etat136 : List ℕ := [fil78,fil88,fil79,fil34,fil35,fil36]
def etat137 : List ℕ := [fil78,fil79,fil34,fil35,fil36,fil89]
def etat138 : List ℕ := [fil78,fil90,fil79,fil34,fil35,fil36]
def etat139 : List ℕ := [fil78,fil79,fil34,fil35,fil91,fil36]
def etat140 : List ℕ := [fil78,fil48,fil79,fil34,fil35,fil36]
def etat141 : List ℕ := [fil78,fil79,fil34,fil35,fil49,fil36]
def etat142 : List ℕ := [fil78,fil79,fil50,fil34,fil35,fil36]
def etat143 : List ℕ := [fil78,fil79,fil34,fil51,fil35,fil36]
def etat144 : List ℕ := [fil78,fil52,fil79,fil34,fil35,fil36]
def etat145 : List ℕ := [fil78,fil79,fil34,fil35,fil36,fil53]
def etat146 : List ℕ := [fil78,fil79,fil54,fil34,fil35,fil36]
def etat147 : List ℕ := [fil78,fil79,fil34,fil35,fil55,fil36]
def etat148 : List ℕ := [fil78,fil56,fil79,fil34,fil35,fil36]
def etat149 : List ℕ := [fil78,fil79,fil34,fil35,fil36,fil57]
def etat150 : List ℕ := [fil78,fil79,fil34,fil58,fil35,fil36]
def etat151 : List ℕ := [fil78,fil79,fil34,fil35,fil59,fil36]
def etat152 : List ℕ := [fil106,fil16,fil17,fil18,fil19,fil20]
def etat153 : List ℕ := [fil106,fil15,fil16,fil17,fil18,fil19,fil20]
def etat154 : List ℕ := [fil107,fil15,fil17,fil18,fil19,fil20]
def etat155 : List ℕ := [fil107,fil15,fil16,fil17,fil18,fil19,fil20]
def etat156 : List ℕ := [fil108,fil15,fil16,fil17,fil18,fil19,fil20]
def etat157 : List ℕ := [fil109,fil70,fil110,fil72,fil73]
def etat158 : List ℕ := [fil109,fil70,fil71,fil110,fil72,fil73]
def etat159 : List ℕ := [fil71,fil110,fil111,fil72,fil73]
def etat160 : List ℕ := [fil70,fil71,fil110,fil111,fil72,fil73]
def etat161 : List ℕ := [fil68,fil112,fil110,fil72,fil73]
def etat162 : List ℕ := [fil112,fil113,fil72,fil73]
def etat163 : List ℕ := [fil112,fil110,fil113,fil72,fil73]
def etat164 : List ℕ := [fil114,fil112,fil110,fil72,fil73]
def etat165 : List ℕ := [fil112,fil115,fil72,fil73]
def etat166 : List ℕ := [fil112,fil115,fil110,fil72,fil73]
def etat167 : List ℕ := [fil88,fil112,fil110,fil72,fil73]
def etat168 : List ℕ := [fil112,fil110,fil116,fil73]
def etat169 : List ℕ := [fil112,fil110,fil72,fil116,fil73]
def etat170 : List ℕ := [fil117,fil112,fil110,fil72,fil73]
def etat171 : List ℕ := [fil112,fil110,fil118,fil73]
def etat172 : List ℕ := [fil112,fil110,fil118,fil72,fil73]
def etat173 : List ℕ := [fil48,fil112,fil110,fil72,fil73]
def etat174 : List ℕ := [fil112,fil110,fil72,fil119]
def etat175 : List ℕ := [fil112,fil110,fil72,fil73,fil119]
def etat176 : List ℕ := [fil120,fil112,fil110,fil72,fil73]
def etat177 : List ℕ := [fil112,fil110,fil72,fil121]
def etat178 : List ℕ := [fil112,fil110,fil72,fil121,fil73]
def etat179 : List ℕ := [fil9,fil6,fil7]
def etat180 : List ℕ := [fil122,fil123,fil79,fil34,fil35,fil36]
def etat181 : List ℕ := [fil123,fil33,fil34,fil35,fil36]
def etat182 : List ℕ := [fil123,fil79,fil33,fil34,fil35,fil36]
def etat183 : List ℕ := [fil78,fil123,fil79,fil34,fil35,fil36]
def etat184 : List ℕ := [fil124,fil123,fil34,fil35,fil36]
def etat185 : List ℕ := [fil124,fil123,fil79,fil34,fil35,fil36]
def etat186 : List ℕ := [fil68,fil123,fil79,fil34,fil35,fil36]
def etat187 : List ℕ := [fil123,fil79,fil125,fil35,fil36]
def etat188 : List ℕ := [fil123,fil79,fil34,fil125,fil35,fil36]
def etat189 : List ℕ := [fil126,fil123,fil79,fil34,fil35,fil36]
def etat190 : List ℕ := [fil123,fil79,fil97,fil35,fil36]
def etat191 : List ℕ := [fil123,fil79,fil97,fil34,fil35,fil36]
def etat192 : List ℕ := [fil98,fil123,fil79,fil34,fil35,fil36]
def etat193 : List ℕ := [fil123,fil79,fil34,fil127,fil36]
def etat194 : List ℕ := [fil123,fil79,fil34,fil35,fil127,fil36]
def etat195 : List ℕ := [fil128,fil123,fil79,fil34,fil35,fil36]
def etat196 : List ℕ := [fil123,fil79,fil34,fil101,fil36]
def etat197 : List ℕ := [fil123,fil79,fil34,fil101,fil35,fil36]
def etat198 : List ℕ := [fil102,fil123,fil79,fil34,fil35,fil36]
def etat199 : List ℕ := [fil123,fil79,fil34,fil35,fil129]
def etat200 : List ℕ := [fil123,fil79,fil34,fil35,fil36,fil129]
def etat201 : List ℕ := [fil130,fil123,fil79,fil34,fil35,fil36]
def etat202 : List ℕ := [fil123,fil79,fil34,fil35,fil105]
def etat203 : List ℕ := [fil123,fil79,fil34,fil35,fil105,fil36]
def etat204 : List ℕ := [fil80,fil123,fil79,fil34,fil35,fil36]
def etat205 : List ℕ := [fil123,fil79,fil81,fil35,fil36]
def etat206 : List ℕ := [fil123,fil79,fil34,fil81,fil35,fil36]
def etat207 : List ℕ := [fil123,fil82,fil79,fil34,fil35,fil36]
def etat208 : List ℕ := [fil123,fil79,fil83,fil35,fil36]
def etat209 : List ℕ := [fil123,fil79,fil83,fil34,fil35,fil36]
def etat210 : List ℕ := [fil84,fil123,fil79,fil34,fil35,fil36]
def etat211 : List ℕ := [fil123,fil79,fil34,fil85,fil36]
def etat212 : List ℕ := [fil123,fil79,fil34,fil35,fil85,fil36]
def etat213 : List ℕ := [fil123,fil86,fil79,fil34,fil35,fil36]
def etat214 : List ℕ := [fil123,fil79,fil34,fil87,fil36]
def etat215 : List ℕ := [fil123,fil79,fil34,fil87,fil35,fil36]
def etat216 : List ℕ := [fil88,fil123,fil79,fil34,fil35,fil36]
def etat217 : List ℕ := [fil123,fil79,fil34,fil35,fil89]
def etat218 : List ℕ := [fil123,fil79,fil34,fil35,fil36,fil89]
def etat219 : List ℕ := [fil123,fil90,fil79,fil34,fil35,fil36]
def etat220 : List ℕ := [fil123,fil79,fil34,fil35,fil91]
def etat221 : List ℕ := [fil123,fil79,fil34,fil35,fil91,fil36]
def etat222 : List ℕ := [fil48,fil123,fil79,fil34,fil35,fil36]
def etat223 : List ℕ := [fil123,fil79,fil34,fil35,fil49,fil36]
def etat224 : List ℕ := [fil123,fil79,fil50,fil34,fil35,fil36]
def etat225 : List ℕ := [fil123,fil79,fil34,fil51,fil35,fil36]
def etat226 : List ℕ := [fil52,fil123,fil79,fil34,fil35,fil36]
def etat227 : List ℕ := [fil123,fil79,fil34,fil35,fil36,fil53]
def etat228 : List ℕ := [fil123,fil79,fil54,fil34,fil35,fil36]
def etat229 : List ℕ := [fil123,fil79,fil34,fil35,fil55,fil36]
def etat230 : List ℕ := [fil56,fil123,fil79,fil34,fil35,fil36]
def etat231 : List ℕ := [fil123,fil79,fil34,fil35,fil36,fil57]
def etat232 : List ℕ := [fil123,fil79,fil34,fil58,fil35,fil36]
def etat233 : List ℕ := [fil123,fil79,fil34,fil35,fil59,fil36]
def etat234 : List ℕ := [fil123,fil79,fil34,fil35,fil36]
def etat235 : List ℕ := [fil16,fil17,fil131,fil18,fil19,fil20]
def etat236 : List ℕ := [fil132,fil66,fil133,fil134]
def etat237 : List ℕ := [fil68,fil70,fil110,fil72,fil73]
def etat238 : List ℕ := [fil68,fil69,fil70,fil110,fil72,fil73]
def etat239 : List ℕ := [fil69,fil70,fil110,fil75,fil72,fil73]
def etat240 : List ℕ := [fil135,fil69,fil70,fil110,fil72,fil73]
def etat241 : List ℕ := [fil136,fil70,fil110,fil72,fil73]
def etat242 : List ℕ := [fil69,fil136,fil70,fil110,fil72,fil73]
def etat243 : List ℕ := [fil137,fil70,fil110,fil72,fil73]
def etat244 : List ℕ := [fil69,fil137,fil70,fil72,fil73]
def etat245 : List ℕ := [fil69,fil137,fil70,fil110,fil72,fil73]
def etat246 : List ℕ := [fil98,fil69,fil70,fil110,fil72,fil73]
def etat247 : List ℕ := [fil70,fil110,fil72,fil138,fil73]
def etat248 : List ℕ := [fil69,fil70,fil110,fil72,fil138,fil73]
def etat249 : List ℕ := [fil139,fil70,fil110,fil72,fil73]
def etat250 : List ℕ := [fil139,fil69,fil70,fil110,fil72,fil73]
def etat251 : List ℕ := [fil69,fil70,fil110,fil140,fil72,fil73]
def etat252 : List ℕ := [fil102,fil69,fil70,fil110,fil72,fil73]
def etat253 : List ℕ := [fil70,fil110,fil72,fil73,fil141]
def etat254 : List ℕ := [fil69,fil70,fil110,fil72,fil73,fil141]
def etat255 : List ℕ := [fil142,fil70,fil110,fil72,fil73]
def etat256 : List ℕ := [fil142,fil69,fil70,fil110,fil72,fil73]
def etat257 : List ℕ := [fil69,fil70,fil110,fil72,fil143,fil73]
def etat258 : List ℕ := [fil69,fil144,fil70,fil110,fil72,fil73]
def etat259 : List ℕ := [fil69,fil70,fil113,fil72,fil73]
def etat260 : List ℕ := [fil69,fil70,fil110,fil113,fil72,fil73]
def etat261 : List ℕ := [fil114,fil69,fil70,fil110,fil72,fil73]
def etat262 : List ℕ := [fil69,fil145,fil70,fil72,fil73]
def etat263 : List ℕ := [fil69,fil145,fil70,fil110,fil72,fil73]
def etat264 : List ℕ := [fil88,fil69,fil70,fil110,fil72,fil73]
def etat265 : List ℕ := [fil69,fil70,fil110,fil146,fil73]
def etat266 : List ℕ := [fil69,fil70,fil110,fil72,fil146,fil73]
def etat267 : List ℕ := [fil69,fil147,fil70,fil110,fil72,fil73]
def etat268 : List ℕ := [fil69,fil70,fil110,fil118,fil73]
def etat269 : List ℕ := [fil69,fil70,fil110,fil118,fil72,fil73]
def etat270 : List ℕ := [fil48,fil69,fil70,fil110,fil72,fil73]
def etat271 : List ℕ := [fil69,fil70,fil110,fil72,fil148]
def etat272 : List ℕ := [fil69,fil70,fil110,fil72,fil73,fil148]
def etat273 : List ℕ := [fil69,fil149,fil70,fil110,fil72,fil73]
def etat274 : List ℕ := [fil69,fil70,fil110,fil72,fil121]
def etat275 : List ℕ := [fil69,fil70,fil110,fil72,fil121,fil73]
def etat276 : List ℕ := [fil150,fil69,fil70,fil110,fil72,fil73]
def etat277 : List ℕ := [fil69,fil70,fil110,fil72,fil151,fil73]
def etat278 : List ℕ := [fil69,fil70,fil152,fil110,fil72,fil73]
def etat279 : List ℕ := [fil69,fil70,fil110,fil153,fil72,fil73]
def etat280 : List ℕ := [fil154,fil69,fil70,fil110,fil72,fil73]
def etat281 : List ℕ := [fil69,fil70,fil110,fil72,fil73,fil155]
def etat282 : List ℕ := [fil69,fil70,fil156,fil110,fil72,fil73]
def etat283 : List ℕ := [fil69,fil70,fil110,fil72,fil157,fil73]
def etat284 : List ℕ := [fil52,fil69,fil70,fil110,fil72,fil73]
def etat285 : List ℕ := [fil69,fil70,fil110,fil72,fil73,fil158]
def etat286 : List ℕ := [fil69,fil70,fil110,fil159,fil72,fil73]
def etat287 : List ℕ := [fil69,fil70,fil110,fil72,fil160,fil73]
def etat288 : List ℕ := [fil69,fil70,fil110,fil72,fil73]
def etat289 : List ℕ := [fil15,fil16,fil131,fil18,fil19,fil20]
def etat290 : List ℕ := [fil15,fil16,fil17,fil131,fil18,fil19,fil20]
def etat291 : List ℕ := [fil161,fil162]
def etat292 : List ℕ := [fil163,fil66,fil67,fil134]
def etat293 : List ℕ := [fil68,fil78,fil70,fil71,fil72,fil73]
def etat294 : List ℕ := [fil164,fil71,fil72,fil73]
def etat295 : List ℕ := [fil70,fil164,fil71,fil72,fil73]
def etat296 : List ℕ := [fil8,fil5,fil6,fil7]
def etat297 : List ℕ := [fil78,fil164,fil71,fil72,fil73]
def etat298 : List ℕ := [fil78,fil70,fil164,fil71,fil72,fil73]
def etat299 : List ℕ := [fil96,fil70,fil71,fil72,fil73]
def etat300 : List ℕ := [fil96,fil78,fil70,fil71,fil72,fil73]
def etat301 : List ℕ := [fil78,fil136,fil71,fil72,fil73]
def etat302 : List ℕ := [fil78,fil136,fil70,fil71,fil72,fil73]
def etat303 : List ℕ := [fil70,fil71,fil110,fil72,fil73]
def etat304 : List ℕ := [fil78,fil70,fil110,fil72,fil73]
def etat305 : List ℕ := [fil78,fil70,fil71,fil110,fil72,fil73]
def etat306 : List ℕ := [fil98,fil78,fil70,fil71,fil72,fil73]
def etat307 : List ℕ := [fil78,fil70,fil71,fil165,fil73]
def etat308 : List ℕ := [fil78,fil70,fil71,fil72,fil165,fil73]
def etat309 : List ℕ := [fil100,fil78,fil70,fil71,fil72,fil73]
def etat310 : List ℕ := [fil78,fil70,fil71,fil140,fil73]
def etat311 : List ℕ := [fil78,fil70,fil71,fil140,fil72,fil73]
def etat312 : List ℕ := [fil102,fil78,fil70,fil71,fil72,fil73]
def etat313 : List ℕ := [fil78,fil70,fil71,fil72,fil166]
def etat314 : List ℕ := [fil78,fil70,fil71,fil72,fil73,fil166]
def etat315 : List ℕ := [fil104,fil78,fil70,fil71,fil72,fil73]
def etat316 : List ℕ := [fil78,fil70,fil71,fil72,fil143]
def etat317 : List ℕ := [fil78,fil70,fil71,fil72,fil143,fil73]
def etat318 : List ℕ := [fil78,fil109,fil70,fil71,fil72,fil73]
def etat319 : List ℕ := [fil68,fil78,fil111,fil72,fil73]
def etat320 : List ℕ := [fil78,fil113,fil72,fil73]
def etat321 : List ℕ := [fil78,fil111,fil113,fil72,fil73]
def etat322 : List ℕ := [fil96,fil78,fil111,fil72,fil73]
def etat323 : List ℕ := [fil78,fil167,fil72,fil73]
def etat324 : List ℕ := [fil78,fil167,fil111,fil72,fil73]
def etat325 : List ℕ := [fil98,fil78,fil111,fil72,fil73]
def etat326 : List ℕ := [fil78,fil111,fil165,fil73]
def etat327 : List ℕ := [fil78,fil111,fil72,fil165,fil73]
def etat328 : List ℕ := [fil100,fil78,fil111,fil72,fil73]
def etat329 : List ℕ := [fil78,fil111,fil140,fil73]
def etat330 : List ℕ := [fil78,fil111,fil140,fil72,fil73]
def etat331 : List ℕ := [fil102,fil78,fil111,fil72,fil73]
def etat332 : List ℕ := [fil78,fil111,fil72,fil166]
def etat333 : List ℕ := [fil78,fil111,fil72,fil73,fil166]
def etat334 : List ℕ := [fil104,fil78,fil111,fil72,fil73]
def etat335 : List ℕ := [fil78,fil111,fil72,fil143]
def etat336 : List ℕ := [fil78,fil111,fil72,fil143,fil73]
def etat337 : List ℕ := [fil168,fil16,fil17,fil18,fil19,fil20]
def etat338 : List ℕ := [fil168,fil15,fil16,fil17,fil18,fil19,fil20]
def etat339 : List ℕ := [fil61,fil169,fil24,fil25]
def etat340 : List ℕ := [fil170,fil171,fil24,fil25]
def etat341 : List ℕ := [fil171,fil169,fil93,fil25]
def etat342 : List ℕ := [fil171,fil169,fil24,fil94]
def etat343 : List ℕ := [fil68,fil69,fil137,fil70,fil72,fil73]
def etat344 : List ℕ := [fil137,fil70,fil75,fil72,fil73]
def etat345 : List ℕ := [fil69,fil137,fil70,fil75,fil72,fil73]
def etat346 : List ℕ := [fil135,fil137,fil70,fil72,fil73]
def etat347 : List ℕ := [fil135,fil69,fil137,fil70,fil72,fil73]
def etat348 : List ℕ := [fil69,fil137,fil136,fil70,fil72,fil73]
def etat349 : List ℕ := [fil98,fil69,fil137,fil70,fil72,fil73]
def etat350 : List ℕ := [fil69,fil137,fil70,fil72,fil138,fil73]
def etat351 : List ℕ := [fil139,fil69,fil137,fil70,fil72,fil73]
def etat352 : List ℕ := [fil69,fil137,fil70,fil140,fil72,fil73]
def etat353 : List ℕ := [fil102,fil69,fil137,fil70,fil72,fil73]
def etat354 : List ℕ := [fil69,fil137,fil70,fil72,fil73,fil141]
def etat355 : List ℕ := [fil142,fil69,fil137,fil70,fil72,fil73]
def etat356 : List ℕ := [fil69,fil137,fil70,fil72,fil143,fil73]
def etat357 : List ℕ := [fil69,fil109,fil137,fil70,fil72,fil73]
def etat358 : List ℕ := [fil69,fil172,fil72,fil73]
def etat359 : List ℕ := [fil69,fil70,fil172,fil72,fil73]
def etat360 : List ℕ := [fil69,fil137,fil172,fil72,fil73]
def etat361 : List ℕ := [fil69,fil137,fil70,fil172,fil72,fil73]
def etat362 : List ℕ := [fil173,fil69,fil70,fil72,fil73]
def etat363 : List ℕ := [fil173,fil69,fil137,fil70,fil72,fil73]
def etat364 : List ℕ := [fil112,fil69,fil137,fil72,fil73]
def etat365 : List ℕ := [fil112,fil69,fil137,fil70,fil72,fil73]
def etat366 : List ℕ := [fil80,fil69,fil137,fil70,fil72,fil73]
def etat367 : List ℕ := [fil69,fil137,fil70,fil174,fil73]
def etat368 : List ℕ := [fil69,fil137,fil70,fil72,fil174,fil73]
def etat369 : List ℕ := [fil69,fil175,fil137,fil70,fil72,fil73]
def etat370 : List ℕ := [fil69,fil137,fil70,fil176,fil73]
def etat371 : List ℕ := [fil69,fil137,fil70,fil176,fil72,fil73]
def etat372 : List ℕ := [fil84,fil69,fil137,fil70,fil72,fil73]
def etat373 : List ℕ := [fil69,fil137,fil70,fil72,fil177]
def etat374 : List ℕ := [fil69,fil137,fil70,fil72,fil73,fil177]
def etat375 : List ℕ := [fil69,fil178,fil137,fil70,fil72,fil73]
def etat376 : List ℕ := [fil69,fil137,fil70,fil72,fil179]
def etat377 : List ℕ := [fil69,fil137,fil70,fil72,fil179,fil73]
def etat378 : List ℕ := [fil88,fil69,fil137,fil70,fil72,fil73]
def etat379 : List ℕ := [fil69,fil137,fil70,fil146,fil73]
def etat380 : List ℕ := [fil69,fil137,fil70,fil72,fil146,fil73]
def etat381 : List ℕ := [fil69,fil137,fil147,fil70,fil72,fil73]
def etat382 : List ℕ := [fil69,fil137,fil70,fil118,fil73]
def etat383 : List ℕ := [fil69,fil137,fil70,fil118,fil72,fil73]
def etat384 : List ℕ := [fil48,fil69,fil137,fil70,fil72,fil73]
def etat385 : List ℕ := [fil69,fil137,fil70,fil72,fil148]
def etat386 : List ℕ := [fil69,fil137,fil70,fil72,fil73,fil148]
def etat387 : List ℕ := [fil69,fil137,fil149,fil70,fil72,fil73]
def etat388 : List ℕ := [fil69,fil137,fil70,fil72,fil121]
def etat389 : List ℕ := [fil69,fil137,fil70,fil72,fil121,fil73]
def etat390 : List ℕ := [fil52,fil69,fil137,fil70,fil72,fil73]
def etat391 : List ℕ := [fil69,fil137,fil70,fil72,fil73,fil158]
def etat392 : List ℕ := [fil69,fil137,fil70,fil159,fil72,fil73]
def etat393 : List ℕ := [fil69,fil137,fil70,fil72,fil160,fil73]
def etat394 : List ℕ := [fil15,fil16,fil180,fil18,fil19,fil20]
def etat395 : List ℕ := [fil15,fil16,fil180,fil17,fil18,fil19,fil20]
def etat396 : List ℕ := [fil4,fil15,fil16,fil17,fil18,fil19,fil20]
def etat397 : List ℕ := [fil8,fil5,fil181,fil63]
def etat398 : List ℕ := [fil122,fil123,fil79,fil125,fil35,fil36]
def etat399 : List ℕ := [fil123,fil79,fil33,fil125,fil35,fil36]
def etat400 : List ℕ := [fil78,fil123,fil79,fil125,fil35,fil36]
def etat401 : List ℕ := [fil124,fil123,fil79,fil125,fil35,fil36]
def etat402 : List ℕ := [fil79,fil97,fil125,fil35,fil36]
def etat403 : List ℕ := [fil123,fil79,fil97,fil125,fil35,fil36]
def etat404 : List ℕ := [fil98,fil123,fil79,fil125,fil35,fil36]
def etat405 : List ℕ := [fil79,fil125,fil127,fil36]
def etat406 : List ℕ := [fil79,fil125,fil35,fil127,fil36]
def etat407 : List ℕ := [fil123,fil79,fil125,fil127,fil36]
def etat408 : List ℕ := [fil123,fil79,fil125,fil35,fil127,fil36]
def etat409 : List ℕ := [fil128,fil79,fil125,fil35,fil36]
def etat410 : List ℕ := [fil128,fil123,fil79,fil125,fil35,fil36]
def etat411 : List ℕ := [fil123,fil79,fil125,fil101,fil36]
def etat412 : List ℕ := [fil123,fil79,fil125,fil101,fil35,fil36]
def etat413 : List ℕ := [fil102,fil123,fil79,fil125,fil35,fil36]
def etat414 : List ℕ := [fil79,fil125,fil35,fil129]
def etat415 : List ℕ := [fil79,fil125,fil35,fil36,fil129]
def etat416 : List ℕ := [fil123,fil79,fil125,fil35,fil129]
def etat417 : List ℕ := [fil123,fil79,fil125,fil35,fil36,fil129]
def etat418 : List ℕ := [fil130,fil79,fil125,fil35,fil36]
def etat419 : List ℕ := [fil130,fil123,fil79,fil125,fil35,fil36]
def etat420 : List ℕ := [fil123,fil79,fil125,fil35,fil105]
def etat421 : List ℕ := [fil123,fil79,fil125,fil35,fil105,fil36]
def etat422 : List ℕ := [fil123,fil182,fil79,fil125,fil35,fil36]
def etat423 : List ℕ := [fil123,fil79,fil37,fil35,fil36]
def etat424 : List ℕ := [fil123,fil79,fil125,fil37,fil35,fil36]
def etat425 : List ℕ := [fil183,fil123,fil79,fil125,fil35,fil36]
def etat426 : List ℕ := [fil123,fil79,fil184,fil35,fil36]
def etat427 : List ℕ := [fil123,fil79,fil184,fil125,fil35,fil36]
def etat428 : List ℕ := [fil84,fil123,fil79,fil125,fil35,fil36]
def etat429 : List ℕ := [fil123,fil79,fil125,fil85,fil36]
def etat430 : List ℕ := [fil123,fil79,fil125,fil35,fil85,fil36]
def etat431 : List ℕ := [fil123,fil86,fil79,fil125,fil35,fil36]
def etat432 : List ℕ := [fil123,fil79,fil125,fil87,fil36]
def etat433 : List ℕ := [fil123,fil79,fil125,fil87,fil35,fil36]
def etat434 : List ℕ := [fil88,fil123,fil79,fil125,fil35,fil36]
def etat435 : List ℕ := [fil123,fil79,fil125,fil35,fil89]
def etat436 : List ℕ := [fil123,fil79,fil125,fil35,fil36,fil89]
def etat437 : List ℕ := [fil123,fil90,fil79,fil125,fil35,fil36]
def etat438 : List ℕ := [fil123,fil79,fil125,fil35,fil91]
def etat439 : List ℕ := [fil123,fil79,fil125,fil35,fil91,fil36]
def etat440 : List ℕ := [fil185,fil123,fil79,fil125,fil35,fil36]
def etat441 : List ℕ := [fil123,fil79,fil125,fil35,fil186,fil36]
def etat442 : List ℕ := [fil123,fil79,fil187,fil125,fil35,fil36]
def etat443 : List ℕ := [fil123,fil79,fil125,fil188,fil35,fil36]
def etat444 : List ℕ := [fil189,fil123,fil79,fil125,fil35,fil36]
def etat445 : List ℕ := [fil123,fil79,fil125,fil35,fil36,fil190]
def etat446 : List ℕ := [fil123,fil79,fil191,fil125,fil35,fil36]
def etat447 : List ℕ := [fil123,fil79,fil125,fil35,fil192,fil36]
def etat448 : List ℕ := [fil56,fil123,fil79,fil125,fil35,fil36]
def etat449 : List ℕ := [fil123,fil79,fil125,fil35,fil36,fil57]
def etat450 : List ℕ := [fil123,fil79,fil125,fil58,fil35,fil36]
def etat451 : List ℕ := [fil123,fil79,fil125,fil35,fil59,fil36]
def etat452 : List ℕ := [fil15,fil16,fil17,fil193,fil19,fil20]
def etat453 : List ℕ := [fil15,fil16,fil17,fil18,fil193,fil19,fil20]
def etat454 : List ℕ := [fil194,fil15,fil16,fil17,fil18,fil19,fil20]
def etat455 : List ℕ := [fil4,fil5,fil11,fil7]
def etat456 : List ℕ := [fil8,fil5,fil195,fil7]
def etat457 : List ℕ := [fil8,fil5,fil11,fil63]
def etat458 : List ℕ := [fil196,fil197,fil198]
def etat459 : List ℕ := [fil4,fil171,fil23,fil24,fil25]
def etat460 : List ℕ := [fil61,fil199,fil23,fil24,fil25]
def etat461 : List ℕ := [fil92,fil199,fil171,fil24,fil25]
def etat462 : List ℕ := [fil199,fil171,fil23,fil93,fil25]
def etat463 : List ℕ := [fil199,fil171,fil23,fil24,fil94]
def etat464 : List ℕ := [fil122,fil123,fil79,fil97,fil35,fil36]
def etat465 : List ℕ := [fil79,fil33,fil97,fil35,fil36]
def etat466 : List ℕ := [fil123,fil79,fil33,fil97,fil35,fil36]
def etat467 : List ℕ := [fil78,fil123,fil79,fil97,fil35,fil36]
def etat468 : List ℕ := [fil124,fil123,fil79,fil97,fil35,fil36]
def etat469 : List ℕ := [fil98,fil123,fil79,fil97,fil35,fil36]
def etat470 : List ℕ := [fil123,fil79,fil97,fil127,fil36]
def etat471 : List ℕ := [fil123,fil79,fil97,fil35,fil127,fil36]
def etat472 : List ℕ := [fil128,fil123,fil79,fil97,fil35,fil36]
def etat473 : List ℕ := [fil123,fil79,fil97,fil101,fil36]
def etat474 : List ℕ := [fil123,fil79,fil97,fil101,fil35,fil36]
def etat475 : List ℕ := [fil102,fil123,fil79,fil97,fil35,fil36]
def etat476 : List ℕ := [fil123,fil79,fil97,fil35,fil129]
def etat477 : List ℕ := [fil123,fil79,fil97,fil35,fil36,fil129]
def etat478 : List ℕ := [fil130,fil123,fil79,fil97,fil35,fil36]
def etat479 : List ℕ := [fil123,fil79,fil97,fil35,fil105]
def etat480 : List ℕ := [fil123,fil79,fil97,fil35,fil105,fil36]
def etat481 : List ℕ := [fil80,fil123,fil79,fil97,fil35,fil36]
def etat482 : List ℕ := [fil123,fil79,fil200,fil35,fil36]
def etat483 : List ℕ := [fil123,fil79,fil97,fil200,fil35,fil36]
def etat484 : List ℕ := [fil123,fil82,fil79,fil97,fil35,fil36]
def etat485 : List ℕ := [fil123,fil79,fil39,fil35,fil36]
def etat486 : List ℕ := [fil123,fil79,fil39,fil97,fil35,fil36]
def etat487 : List ℕ := [fil84,fil123,fil79,fil97,fil35,fil36]
def etat488 : List ℕ := [fil123,fil79,fil97,fil85,fil36]
def etat489 : List ℕ := [fil123,fil79,fil97,fil35,fil85,fil36]
def etat490 : List ℕ := [fil123,fil86,fil79,fil97,fil35,fil36]
def etat491 : List ℕ := [fil123,fil79,fil97,fil87,fil36]
def etat492 : List ℕ := [fil123,fil79,fil97,fil87,fil35,fil36]
def etat493 : List ℕ := [fil88,fil123,fil79,fil97,fil35,fil36]
def etat494 : List ℕ := [fil123,fil79,fil97,fil35,fil89]
def etat495 : List ℕ := [fil123,fil79,fil97,fil35,fil36,fil89]
def etat496 : List ℕ := [fil123,fil90,fil79,fil97,fil35,fil36]
def etat497 : List ℕ := [fil123,fil79,fil97,fil35,fil91]
def etat498 : List ℕ := [fil123,fil79,fil97,fil35,fil91,fil36]
def etat499 : List ℕ := [fil48,fil123,fil79,fil97,fil35,fil36]
def etat500 : List ℕ := [fil123,fil79,fil97,fil35,fil201,fil36]
def etat501 : List ℕ := [fil123,fil79,fil202,fil97,fil35,fil36]
def etat502 : List ℕ := [fil123,fil79,fil97,fil51,fil35,fil36]
def etat503 : List ℕ := [fil52,fil123,fil79,fil97,fil35,fil36]
def etat504 : List ℕ := [fil123,fil79,fil97,fil35,fil36,fil203]
def etat505 : List ℕ := [fil123,fil79,fil204,fil97,fil35,fil36]
def etat506 : List ℕ := [fil123,fil79,fil97,fil35,fil55,fil36]
def etat507 : List ℕ := [fil56,fil123,fil79,fil97,fil35,fil36]
def etat508 : List ℕ := [fil123,fil79,fil97,fil35,fil36,fil57]
def etat509 : List ℕ := [fil123,fil79,fil97,fil58,fil35,fil36]
def etat510 : List ℕ := [fil123,fil79,fil97,fil35,fil59,fil36]
def etat511 : List ℕ := [fil15,fil16,fil17,fil205,fil19,fil20]
def etat512 : List ℕ := [fil15,fil16,fil17,fil205,fil18,fil19,fil20]
def etat513 : List ℕ := [fil92,fil15,fil16,fil17,fil18,fil19,fil20]
def etat514 : List ℕ := [fil8,fil5,fil62,fil206]
def etat515 : List ℕ := [fil4,fil171,fil23,fil207,fil25]
def etat516 : List ℕ := [fil61,fil199,fil23,fil207,fil25]
def etat517 : List ℕ := [fil92,fil199,fil171,fil207,fil25]
def etat518 : List ℕ := [fil199,fil171,fil23,fil208,fil25]
def etat519 : List ℕ := [fil199,fil171,fil23,fil207,fil94]
def etat520 : List ℕ := [fil26,fil23,fil208,fil25]
def etat521 : List ℕ := [fil26,fil23,fil207,fil94]
def etat522 : List ℕ := [fil68,fil69,fil70,fil71,fil138,fil73]
def etat523 : List ℕ := [fil71,fil75,fil209,fil73]
def etat524 : List ℕ := [fil71,fil75,fil165,fil73]
def etat525 : List ℕ := [fil71,fil75,fil138,fil77]
def etat526 : List ℕ := [fil15,fil16,fil17,fil18,fil210,fil20]
def etat527 : List ℕ := [fil211,fil212,fil213,fil214,fil215]
def etat528 : List ℕ := [fil216,fil217,fil214,fil215]
def etat529 : List ℕ := [fil33,fil34,fil35,fil127,fil36]
def etat530 : List ℕ := [fil79,fil33,fil34,fil35,fil127,fil36]
def etat531 : List ℕ := [fil123,fil33,fil34,fil35,fil127,fil36]
def etat532 : List ℕ := [fil78,fil79,fil34,fil35,fil127,fil36]
def etat533 : List ℕ := [fil124,fil123,fil34,fil35,fil127,fil36]
def etat534 : List ℕ := [fil79,fil34,fil125,fil35,fil127,fil36]
def etat535 : List ℕ := [fil126,fil79,fil34,fil35,fil127,fil36]
def etat536 : List ℕ := [fil98,fil79,fil34,fil35,fil127,fil36]
def etat537 : List ℕ := [fil98,fil123,fil79,fil34,fil127,fil36]
def etat538 : List ℕ := [fil128,fil123,fil79,fil34,fil127,fil36]
def etat539 : List ℕ := [fil79,fil34,fil101,fil127,fil36]
def etat540 : List ℕ := [fil79,fil34,fil101,fil35,fil127,fil36]
def etat541 : List ℕ := [fil123,fil79,fil34,fil101,fil127,fil36]
def etat542 : List ℕ := [fil79,fil34,fil35,fil127,fil129]
def etat543 : List ℕ := [fil79,fil34,fil35,fil127,fil36,fil129]
def etat544 : List ℕ := [fil123,fil79,fil34,fil35,fil127,fil129]
def etat545 : List ℕ := [fil130,fil79,fil34,fil35,fil127,fil36]
def etat546 : List ℕ := [fil123,fil79,fil34,fil35,fil127,fil105]
def etat547 : List ℕ := [fil123,fil79,fil81,fil35,fil127,fil36]
def etat548 : List ℕ := [fil123,fil79,fil83,fil35,fil127,fil36]
def etat549 : List ℕ := [fil84,fil123,fil79,fil34,fil127,fil36]
def etat550 : List ℕ := [fil123,fil79,fil34,fil127,fil85,fil36]
def etat551 : List ℕ := [fil123,fil86,fil79,fil34,fil127,fil36]
def etat552 : List ℕ := [fil123,fil79,fil34,fil87,fil127,fil36]
def etat553 : List ℕ := [fil123,fil218,fil79,fil34,fil35,fil36]
def etat554 : List ℕ := [fil123,fil79,fil34,fil35,fil41,fil36]
def etat555 : List ℕ := [fil219,fil123,fil79,fil34,fil35,fil36]
def etat556 : List ℕ := [fil123,fil79,fil34,fil220,fil35,fil36]
def etat557 : List ℕ := [fil123,fil79,fil34,fil35,fil127,fil89]
def etat558 : List ℕ := [fil123,fil79,fil34,fil35,fil127,fil91]
def etat559 : List ℕ := [fil48,fil123,fil79,fil34,fil127,fil36]
def etat560 : List ℕ := [fil123,fil79,fil34,fil127,fil49,fil36]
def etat561 : List ℕ := [fil123,fil79,fil50,fil34,fil127,fil36]
def etat562 : List ℕ := [fil123,fil79,fil34,fil51,fil127,fil36]
def etat563 : List ℕ := [fil117,fil123,fil79,fil34,fil35,fil36]
def etat564 : List ℕ := [fil123,fil79,fil34,fil35,fil186,fil36]
def etat565 : List ℕ := [fil123,fil79,fil202,fil34,fil35,fil36]
def etat566 : List ℕ := [fil123,fil79,fil34,fil35,fil221,fil36]
def etat567 : List ℕ := [fil56,fil123,fil79,fil34,fil127,fil36]
def etat568 : List ℕ := [fil123,fil79,fil34,fil127,fil36,fil57]
def etat569 : List ℕ := [fil123,fil79,fil34,fil58,fil127,fil36]
def etat570 : List ℕ := [fil123,fil79,fil34,fil127,fil59,fil36]
def etat571 : List ℕ := [fil222,fil123,fil79,fil34,fil35,fil36]
def etat572 : List ℕ := [fil123,fil79,fil34,fil35,fil36,fil223]
def etat573 : List ℕ := [fil123,fil79,fil34,fil35,fil224,fil36]
def etat574 : List ℕ := [fil123,fil79,fil34,fil35,fil225,fil36]
def etat575 : List ℕ := [fil15,fil16,fil17,fil18,fil19,fil210,fil20]
def etat576 : List ℕ := [fil226,fil15,fil16,fil17,fil18,fil19,fil20]
def etat577 : List ℕ := [fil4,fil5,fil6,fil13]
def etat578 : List ℕ := [fil8,fil5,fil62,fil13]
def etat579 : List ℕ := [fil8,fil5,fil6,fil227]
def etat580 : List ℕ := [fil4,fil171,fil23,fil228,fil25]
def etat581 : List ℕ := [fil61,fil199,fil23,fil228,fil25]
def etat582 : List ℕ := [fil92,fil199,fil171,fil228,fil25]
def etat583 : List ℕ := [fil199,fil171,fil23,fil229,fil25]
def etat584 : List ℕ := [fil199,fil171,fil23,fil228,fil94]
def etat585 : List ℕ := [fil22,fil23,fil228,fil25]
def etat586 : List ℕ := [fil26,fil23,fil229,fil25]
def etat587 : List ℕ := [fil26,fil23,fil228,fil94]
def etat588 : List ℕ := [fil68,fil69,fil70,fil71,fil140,fil73]
def etat589 : List ℕ := [fil74,fil71,fil140,fil73]
def etat590 : List ℕ := [fil71,fil75,fil230,fil73]
def etat591 : List ℕ := [fil71,fil75,fil140,fil77]
def etat592 : List ℕ := [fil15,fil16,fil17,fil18,fil231,fil20]
def etat593 : List ℕ := [fil15,fil16,fil17,fil18,fil231,fil19,fil20]
def etat594 : List ℕ := [fil232,fil15,fil16,fil17,fil18,fil19,fil20]
def etat595 : List ℕ := [fil15,fil16,fil17,fil18,fil19,fil233]
def etat596 : List ℕ := [fil15,fil16,fil17,fil18,fil19,fil20,fil233]
def etat597 : List ℕ := [fil234,fil15,fil16,fil17,fil18,fil19,fil20]
def etat598 : List ℕ := [fil15,fil16,fil17,fil18,fil19,fil235]
def etat599 : List ℕ := [fil15,fil16,fil17,fil18,fil19,fil235,fil20]
def etat600 : List ℕ := [fil15,fil236,fil16,fil17,fil18,fil19,fil20]
def etat601 : List ℕ := [fil15,fil17,fil237,fil18,fil19,fil20]
def etat602 : List ℕ := [fil15,fil16,fil237,fil18,fil19,fil20]
def etat603 : List ℕ := [fil15,fil16,fil17,fil237,fil18,fil19,fil20]
def etat604 : List ℕ := [fil238,fil15,fil17,fil18,fil19,fil20]
def etat605 : List ℕ := [fil238,fil15,fil16,fil17,fil18,fil19,fil20]
def etat606 : List ℕ := [fil15,fil16,fil239,fil18,fil19,fil20]
def etat607 : List ℕ := [fil15,fil16,fil239,fil17,fil18,fil19,fil20]
def etat608 : List ℕ := [fil61,fil15,fil16,fil17,fil18,fil19,fil20]
def etat609 : List ℕ := [fil15,fil16,fil17,fil240,fil19,fil20]
def etat610 : List ℕ := [fil15,fil16,fil17,fil18,fil240,fil19,fil20]
def etat611 : List ℕ := [fil15,fil241,fil16,fil17,fil18,fil19,fil20]
def etat612 : List ℕ := [fil15,fil16,fil17,fil242,fil19,fil20]
def etat613 : List ℕ := [fil15,fil16,fil17,fil242,fil18,fil19,fil20]
def etat614 : List ℕ := [fil243,fil15,fil16,fil17,fil18,fil19,fil20]
def etat615 : List ℕ := [fil15,fil16,fil17,fil18,fil244,fil20]
def etat616 : List ℕ := [fil15,fil16,fil17,fil18,fil19,fil244,fil20]
def etat617 : List ℕ := [fil15,fil245,fil16,fil17,fil18,fil19,fil20]
def etat618 : List ℕ := [fil15,fil16,fil17,fil18,fil246,fil20]
def etat619 : List ℕ := [fil15,fil16,fil17,fil18,fil246,fil19,fil20]
def etat620 : List ℕ := [fil247,fil15,fil16,fil17,fil18,fil19,fil20]
def etat621 : List ℕ := [fil15,fil16,fil17,fil18,fil19,fil248]
def etat622 : List ℕ := [fil15,fil16,fil17,fil18,fil19,fil20,fil248]
def etat623 : List ℕ := [fil15,fil249,fil16,fil17,fil18,fil19,fil20]
def etat624 : List ℕ := [fil15,fil16,fil17,fil18,fil19,fil250]
def etat625 : List ℕ := [fil15,fil16,fil17,fil18,fil19,fil250,fil20]
def etat626 : List ℕ := [fil15,fil16,fil251,fil17,fil18,fil19,fil20]
def etat627 : List ℕ := [fil252,fil65,fil253,fil134]
def etat628 : List ℕ := [fil69,fil70,fil111,fil72,fil73]
def etat629 : List ℕ := [fil15,fil16,fil18,fil254,fil19,fil20]
def etat630 : List ℕ := [fil255,fil69,fil111,fil72,fil73]
def etat631 : List ℕ := [fil255,fil69,fil71,fil111,fil72,fil73]
def etat632 : List ℕ := [fil69,fil71,fil110,fil111,fil72,fil73]
def etat633 : List ℕ := [fil15,fil16,fil17,fil254,fil19,fil20]
def etat634 : List ℕ := [fil15,fil16,fil17,fil18,fil254,fil19,fil20]
def etat635 : List ℕ := [fil4,fil213,fil256,fil214,fil257]
def etat636 : List ℕ := [fil61,fil212,fil256,fil214,fil257]
def etat637 : List ℕ := [fil258,fil212,fil213,fil214,fil257]
def etat638 : List ℕ := [fil212,fil213,fil256,fil259,fil257]
def etat639 : List ℕ := [fil212,fil213,fil256,fil214,fil260]
def etat640 : List ℕ := [fil69,fil261,fil70,fil72,fil73]
def etat641 : List ℕ := [fil15,fil16,fil262,fil18,fil19,fil20]
def etat642 : List ℕ := [fil15,fil16,fil262,fil17,fil18,fil19,fil20]
def etat643 : List ℕ := [fil263,fil65,fil67,fil134]
def etat644 : List ℕ := [fil264,fil197,fil198]
def etat645 : List ℕ := [fil265,fil212,fil213,fil215,fil257]
def etat646 : List ℕ := [fil213,fil266,fil215,fil257]
def etat647 : List ℕ := [fil267,fil268,fil215,fil257]
def etat648 : List ℕ := [fil68,fil112,fil69,fil71,fil72,fil73]
def etat649 : List ℕ := [fil269,fil71,fil72,fil73]
def etat650 : List ℕ := [fil69,fil269,fil71,fil72,fil73]
def etat651 : List ℕ := [fil112,fil269,fil71,fil72,fil73]
def etat652 : List ℕ := [fil112,fil69,fil269,fil71,fil72,fil73]
def etat653 : List ℕ := [fil114,fil69,fil71,fil72,fil73]
def etat654 : List ℕ := [fil114,fil112,fil69,fil71,fil72,fil73]
def etat655 : List ℕ := [fil112,fil135,fil71,fil72,fil73]
def etat656 : List ℕ := [fil112,fil135,fil69,fil71,fil72,fil73]
def etat657 : List ℕ := [fil69,fil71,fil111,fil72,fil73]
def etat658 : List ℕ := [fil112,fil69,fil111,fil72,fil73]
def etat659 : List ℕ := [fil112,fil69,fil71,fil111,fil72,fil73]
def etat660 : List ℕ := [fil88,fil112,fil69,fil71,fil72,fil73]
def etat661 : List ℕ := [fil112,fil69,fil71,fil116,fil73]
def etat662 : List ℕ := [fil112,fil69,fil71,fil72,fil116,fil73]
def etat663 : List ℕ := [fil117,fil112,fil69,fil71,fil72,fil73]
def etat664 : List ℕ := [fil112,fil69,fil71,fil118,fil73]
def etat665 : List ℕ := [fil112,fil69,fil71,fil118,fil72,fil73]
def etat666 : List ℕ := [fil48,fil112,fil69,fil71,fil72,fil73]
def etat667 : List ℕ := [fil112,fil69,fil71,fil72,fil119]
def etat668 : List ℕ := [fil112,fil69,fil71,fil72,fil73,fil119]
def etat669 : List ℕ := [fil120,fil112,fil69,fil71,fil72,fil73]
def etat670 : List ℕ := [fil112,fil69,fil71,fil72,fil121]
def etat671 : List ℕ := [fil112,fil69,fil71,fil72,fil121,fil73]
def etat672 : List ℕ := [fil112,fil255,fil69,fil71,fil72,fil73]
def etat673 : List ℕ := [fil61,fil8,fil270,fil7]
def etat674 : List ℕ := [fil15,fil16,fil271,fil17,fil19,fil20]
def etat675 : List ℕ := [fil15,fil16,fil271,fil17,fil18,fil19,fil20]
def etat676 : List ℕ := [fil272,fil15,fil16,fil17,fil18,fil19,fil20]
def etat677 : List ℕ := [fil8,fil5,fil270,fil7]
def etat678 : List ℕ := [fil8,fil5,fil273,fil63]
def etat679 : List ℕ := [fil4,fil171,fil23,fil274,fil25]
def etat680 : List ℕ := [fil61,fil199,fil23,fil274,fil25]
def etat681 : List ℕ := [fil92,fil199,fil171,fil274,fil25]
def etat682 : List ℕ := [fil199,fil171,fil23,fil275,fil25]
def etat683 : List ℕ := [fil199,fil171,fil23,fil274,fil94]
def etat684 : List ℕ := [fil26,fil23,fil275,fil25]
def etat685 : List ℕ := [fil26,fil23,fil274,fil94]
def etat686 : List ℕ := [fil68,fil69,fil70,fil71,fil276,fil73]
def etat687 : List ℕ := [fil71,fil75,fil277,fil73]
def etat688 : List ℕ := [fil71,fil75,fil276,fil77]
def etat689 : List ℕ := [fil15,fil16,fil17,fil18,fil278,fil20]
def etat690 : List ℕ := [fil15,fil16,fil17,fil18,fil19,fil278,fil20]
def etat691 : List ℕ := [fil15,fil16,fil279,fil17,fil18,fil19,fil20]
def etat692 : List ℕ := [fil61,fil8,fil280,fil7]
def etat693 : List ℕ := [fil8,fil5,fil281,fil7]
def etat694 : List ℕ := [fil8,fil5,fil280,fil63]
def etat695 : List ℕ := [fil4,fil171,fil23,fil282,fil25]
def etat696 : List ℕ := [fil61,fil199,fil23,fil282,fil25]
def etat697 : List ℕ := [fil92,fil199,fil171,fil282,fil25]
def etat698 : List ℕ := [fil199,fil171,fil23,fil283,fil25]
def etat699 : List ℕ := [fil199,fil171,fil23,fil282,fil94]
def etat700 : List ℕ := [fil92,fil26,fil282,fil25]
def etat701 : List ℕ := [fil26,fil23,fil283,fil25]
def etat702 : List ℕ := [fil26,fil23,fil282,fil94]
def etat703 : List ℕ := [fil68,fil69,fil70,fil71,fil176,fil73]
def etat704 : List ℕ := [fil71,fil75,fil284,fil73]
def etat705 : List ℕ := [fil71,fil75,fil176,fil77]
def etat706 : List ℕ := [fil15,fil16,fil17,fil18,fil285,fil20]
def etat707 : List ℕ := [fil15,fil16,fil17,fil18,fil285,fil19,fil20]
def etat708 : List ℕ := [fil286,fil15,fil16,fil17,fil18,fil19,fil20]
def etat709 : List ℕ := [fil15,fil16,fil17,fil18,fil19,fil287]
def etat710 : List ℕ := [fil15,fil16,fil17,fil18,fil19,fil20,fil287]
def etat711 : List ℕ := [fil15,fil16,fil288,fil17,fil18,fil19,fil20]
def etat712 : List ℕ := [fil15,fil16,fil17,fil18,fil19,fil289]
def etat713 : List ℕ := [fil15,fil16,fil17,fil18,fil19,fil289,fil20]
def etat714 : List ℕ := [fil290,fil15,fil16,fil17,fil18,fil19,fil20]
def etat715 : List ℕ := [fil123,fil33,fil34,fil35,fil49,fil36]
def etat716 : List ℕ := [fil124,fil123,fil34,fil35,fil49,fil36]
def etat717 : List ℕ := [fil123,fil79,fil125,fil35,fil49,fil36]
def etat718 : List ℕ := [fil123,fil79,fil97,fil35,fil49,fil36]
def etat719 : List ℕ := [fil123,fil79,fil34,fil101,fil49,fil36]
def etat720 : List ℕ := [fil104,fil123,fil79,fil34,fil35,fil36]
def etat721 : List ℕ := [fil291,fil123,fil79,fil34,fil35,fil36]
def etat722 : List ℕ := [fil123,fil79,fil34,fil35,fil292,fil36]
def etat723 : List ℕ := [fil123,fil79,fil34,fil35,fil49,fil129]
def etat724 : List ℕ := [fil123,fil79,fil34,fil35,fil49,fil105]
def etat725 : List ℕ := [fil123,fil79,fil81,fil35,fil49,fil36]
def etat726 : List ℕ := [fil123,fil79,fil83,fil35,fil49,fil36]
def etat727 : List ℕ := [fil123,fil79,fil34,fil85,fil49,fil36]
def etat728 : List ℕ := [fil123,fil79,fil34,fil87,fil49,fil36]
def etat729 : List ℕ := [fil173,fil123,fil79,fil34,fil35,fil36]
def etat730 : List ℕ := [fil123,fil79,fil34,fil35,fil293,fil36]
def etat731 : List ℕ := [fil123,fil294,fil79,fil34,fil35,fil36]
def etat732 : List ℕ := [fil123,fil79,fil34,fil35,fil295,fil36]
def etat733 : List ℕ := [fil123,fil79,fil34,fil35,fil49,fil89]
def etat734 : List ℕ := [fil123,fil79,fil34,fil35,fil49,fil91]
def etat735 : List ℕ := [fil48,fil123,fil79,fil49,fil36]
def etat736 : List ℕ := [fil48,fil123,fil79,fil35,fil49,fil36]
def etat737 : List ℕ := [fil48,fil123,fil79,fil34,fil49,fil36]
def etat738 : List ℕ := [fil123,fil79,fil50,fil34,fil49,fil36]
def etat739 : List ℕ := [fil123,fil79,fil51,fil35,fil49,fil36]
def etat740 : List ℕ := [fil123,fil79,fil35,fil49,fil36,fil53]
def etat741 : List ℕ := [fil123,fil79,fil54,fil35,fil49,fil36]
def etat742 : List ℕ := [fil123,fil79,fil34,fil49,fil36,fil57]
def etat743 : List ℕ := [fil123,fil79,fil34,fil58,fil49,fil36]
def etat744 : List ℕ := [fil296,fil123,fil79,fil34,fil35]
def etat745 : List ℕ := [fil296,fil123,fil79,fil34,fil35,fil36]
def etat746 : List ℕ := [fil296,fil123,fil79,fil34,fil35,fil49]
def etat747 : List ℕ := [fil123,fil79,fil34,fil35,fil36,fil297]
def etat748 : List ℕ := [fil123,fil79,fil34,fil35,fil298]
def etat749 : List ℕ := [fil123,fil79,fil34,fil35,fil298,fil36]
def etat750 : List ℕ := [fil123,fil79,fil34,fil35,fil298,fil49]
def etat751 : List ℕ := [fil123,fil79,fil34,fil35,fil299,fil36]
def etat752 : List ℕ := [fil15,fil16,fil17,fil18,fil19,fil300,fil20]
def etat753 : List ℕ := [fil15,fil16,fil17,fil301,fil18,fil19,fil20]
def etat754 : List ℕ := [fil15,fil16,fil17,fil18,fil302,fil19,fil20]
def etat755 : List ℕ := [fil303,fil15,fil16,fil17,fil18,fil19,fil20]
def etat756 : List ℕ := [fil15,fil16,fil17,fil18,fil19,fil20,fil304]
def etat757 : List ℕ := [fil15,fil16,fil17,fil305,fil18,fil19,fil20]
def etat758 : List ℕ := [fil15,fil16,fil17,fil18,fil19,fil306,fil20]
def etat759 : List ℕ := [fil307,fil15,fil16,fil17,fil18,fil19,fil20]
def etat760 : List ℕ := [fil15,fil16,fil17,fil18,fil19,fil20,fil308]
def etat761 : List ℕ := [fil15,fil16,fil17,fil18,fil309,fil19,fil20]
def etat762 : List ℕ := [fil15,fil16,fil17,fil18,fil19,fil310,fil20]
def etat763 : List ℕ := [fil15,fil16,fil17,fil18,fil19,fil20]
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban0 : Ban 12 3 etat0 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban1 : Ban 20 4 etat1 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban2 : Ban 20 3 etat2 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban3 : Ban 20 3 etat3 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban4 : Ban 20 3 etat4 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban5 : Ban 20 3 etat5 := viaPerm projC7P0 projC7PInv0 ban3 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban6 : Ban 20 3 etat6 := viaPerm projC7P0 projC7PInv0 ban4 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban7 : Ban 20 3 etat7 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban8 : Ban 20 4 etat1 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban9 : Ban 20 3 etat2 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban10 : Ban 20 3 etat3 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban11 : Ban 20 3 etat4 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban12 : Ban 20 3 etat5 := viaPerm projC15P0 projC15PInv0 ban10 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban13 : Ban 20 3 etat6 := viaPerm projC15P0 projC15PInv0 ban11 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban14 : Ban 20 3 etat7 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban15 : Ban 20 4 etat1 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban16 : Ban 20 3 etat2 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban17 : Ban 20 3 etat3 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban18 : Ban 20 3 etat4 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban19 : Ban 20 3 etat5 := viaPerm projC14P0 projC14PInv0 ban17 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban20 : Ban 20 3 etat6 := viaPerm projC14P0 projC14PInv0 ban18 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban21 : Ban 20 3 etat7 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban22 : Ban 20 4 etat1 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban23 : Ban 20 3 etat2 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban24 : Ban 20 3 etat3 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban25 : Ban 20 3 etat4 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban26 : Ban 20 3 etat5 := viaPerm projC13P0 projC13PInv0 ban24 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban27 : Ban 20 3 etat6 := viaPerm projC13P0 projC13PInv0 ban25 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban28 : Ban 20 3 etat7 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban29 : Ban 20 4 etat1 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban30 : Ban 20 3 etat2 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban31 : Ban 20 3 etat3 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban32 : Ban 20 3 etat4 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban33 : Ban 20 3 etat5 := viaPerm projC10P0 projC10PInv0 ban31 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban34 : Ban 20 3 etat6 := viaPerm projC10P0 projC10PInv0 ban32 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban35 : Ban 20 3 etat7 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban36 : Ban 20 4 etat1 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban37 : Ban 20 3 etat2 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban38 : Ban 20 3 etat3 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban39 : Ban 20 3 etat4 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban40 : Ban 20 3 etat5 := viaPerm projC6P0 projC6PInv0 ban38 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban41 : Ban 20 3 etat6 := viaPerm projC6P0 projC6PInv0 ban39 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban42 : Ban 20 3 etat7 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban43 : Ban 12 3 etat8 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem wide44 : Wide 12 3 etat8 := widen (by decide +kernel) ban43
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban45 : Ban 89 7 etat9 := viaCut projCut_top_18 wide44 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban46 : Ban 20 3 etat10 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban47 : Ban 20 3 etat10 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban48 : Ban 20 3 etat10 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban49 : Ban 28 4 etat11 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban50 : Ban 28 3 etat12 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban51 : Ban 28 3 etat13 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban52 : Ban 28 3 etat14 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban53 : Ban 28 3 etat15 := viaPerm projC3P0 projC3PInv0 ban51 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban54 : Ban 28 3 etat16 := viaPerm projC3P0 projC3PInv0 ban52 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban55 : Ban 28 3 etat17 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban56 : Ban 45 5 etat18 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban57 : Ban 45 5 etat19 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban58 : Ban 45 5 etat20 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban59 : Ban 45 5 etat21 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban60 : Ban 45 5 etat22 := viaPerm projC2P1 projC2PInv1 ban56 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban61 : Ban 45 5 etat23 := viaPerm projC2P1 projC2PInv1 ban57 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban62 : Ban 45 5 etat24 := viaPerm projC2P1 projC2PInv1 ban58 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban63 : Ban 45 5 etat25 := viaPerm projC2P1 projC2PInv1 ban59 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban64 : Ban 45 5 etat26 := viaPerm projC2P0 projC2PInv0 ban60 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban65 : Ban 45 5 etat27 := viaPerm projC2P0 projC2PInv0 ban61 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban66 : Ban 45 5 etat28 := viaPerm projC2P0 projC2PInv0 ban62 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban67 : Ban 45 5 etat29 := viaPerm projC2P0 projC2PInv0 ban63 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban68 : Ban 45 5 etat30 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban69 : Ban 45 5 etat31 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban70 : Ban 45 5 etat32 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban71 : Ban 45 5 etat33 := viaPerm projC2P1 projC2PInv1 ban70 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban72 : Ban 45 5 etat34 := viaPerm projC2P0 projC2PInv0 ban68 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban73 : Ban 45 5 etat35 := viaPerm projC2P0 projC2PInv0 ban69 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban74 : Ban 45 5 etat36 := viaPerm projC2P0 projC2PInv0 ban70 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban75 : Ban 45 5 etat37 := viaPerm projC2P0 projC2PInv0 ban71 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban76 : Ban 45 5 etat38 := viaPerm projC2P1 projC2PInv1 ban72 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban77 : Ban 45 5 etat39 := viaPerm projC2P1 projC2PInv1 ban73 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban78 : Ban 45 5 etat40 := viaPerm projC2P1 projC2PInv1 ban74 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban79 : Ban 45 5 etat41 := viaPerm projC2P0 projC2PInv0 ban78 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban80 : Ban 45 6 etat42 := viaBranch (ws := [etat18,etat19,etat20,etat21,etat22,etat23,etat24,etat25,etat26,etat27,etat28,etat29,etat30,etat31,etat32,etat33,etat34,etat35,etat36,etat37,etat38,etat39,etat40,etat41]) (consBan ban56 (consBan ban57 (consBan ban58 (consBan ban59 (consBan ban60 (consBan ban61 (consBan ban62 (consBan ban63 (consBan ban64 (consBan ban65 (consBan ban66 (consBan ban67 (consBan ban68 (consBan ban69 (consBan ban70 (consBan ban71 (consBan ban72 (consBan ban73 (consBan ban74 (consBan ban75 (consBan ban76 (consBan ban77 (consBan ban78 (consBan ban79 (nilBan _ _))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem wide81 : Wide 45 6 etat42 := widen (by decide +kernel) ban80
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban82 : Ban 89 7 etat43 := viaCut projCut_top_2 wide81 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban83 : Ban 20 3 etat1 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban84 : Ban 20 3 etat44 := viaPerm projC6P1 projC6PInv1 ban83 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban85 : Ban 20 3 etat45 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban86 : Ban 20 3 etat46 := viaPerm projC6P0 projC6PInv0 ban85 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban87 : Ban 20 3 etat1 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban88 : Ban 20 3 etat44 := viaPerm projC10P2 projC10PInv2 ban87 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban89 : Ban 20 3 etat45 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban90 : Ban 20 3 etat46 := viaPerm projC10P0 projC10PInv0 ban89 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban91 : Ban 16 4 etat47 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban92 : Ban 16 4 etat47 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban93 : Ban 40 5 etat48 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban94 : Ban 40 3 etat49 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban95 : Ban 40 3 etat50 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban96 : Ban 40 3 etat51 := viaPerm projC1P0 projC1PInv0 ban95 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban97 : Ban 45 5 etat52 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban98 : Ban 45 5 etat53 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban99 : Ban 45 5 etat54 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban100 : Ban 45 5 etat55 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban101 : Ban 45 5 etat56 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban102 : Ban 45 5 etat57 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban103 : Ban 45 5 etat58 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban104 : Ban 45 5 etat59 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban105 : Ban 45 5 etat60 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban106 : Ban 45 5 etat61 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban107 : Ban 45 5 etat62 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban108 : Ban 45 5 etat63 := viaPerm projC2P1 projC2PInv1 ban100 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban109 : Ban 45 5 etat64 := viaPerm projC2P1 projC2PInv1 ban101 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban110 : Ban 45 5 etat65 := viaPerm projC2P1 projC2PInv1 ban102 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban111 : Ban 45 5 etat66 := viaPerm projC2P1 projC2PInv1 ban103 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban112 : Ban 45 5 etat67 := viaPerm projC2P1 projC2PInv1 ban104 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban113 : Ban 45 5 etat68 := viaPerm projC2P1 projC2PInv1 ban105 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban114 : Ban 45 5 etat69 := viaPerm projC2P1 projC2PInv1 ban106 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban115 : Ban 45 5 etat70 := viaPerm projC2P1 projC2PInv1 ban107 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban116 : Ban 45 5 etat71 := viaPerm projC2P0 projC2PInv0 ban108 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban117 : Ban 45 5 etat72 := viaPerm projC2P0 projC2PInv0 ban109 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban118 : Ban 45 5 etat73 := viaPerm projC2P0 projC2PInv0 ban110 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban119 : Ban 45 5 etat74 := viaPerm projC2P0 projC2PInv0 ban111 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban120 : Ban 45 5 etat75 := viaPerm projC2P0 projC2PInv0 ban112 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban121 : Ban 45 5 etat76 := viaPerm projC2P0 projC2PInv0 ban113 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban122 : Ban 45 5 etat77 := viaPerm projC2P0 projC2PInv0 ban114 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban123 : Ban 45 5 etat78 := viaPerm projC2P0 projC2PInv0 ban115 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban124 : Ban 45 5 etat79 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban125 : Ban 45 5 etat80 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban126 : Ban 45 5 etat81 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban127 : Ban 45 5 etat82 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban128 : Ban 45 5 etat83 := viaPerm projC2P1 projC2PInv1 ban124 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban129 : Ban 45 5 etat84 := viaPerm projC2P1 projC2PInv1 ban125 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban130 : Ban 45 5 etat85 := viaPerm projC2P1 projC2PInv1 ban126 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban131 : Ban 45 5 etat86 := viaPerm projC2P1 projC2PInv1 ban127 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban132 : Ban 45 5 etat87 := viaPerm projC2P0 projC2PInv0 ban128 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban133 : Ban 45 5 etat88 := viaPerm projC2P0 projC2PInv0 ban129 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban134 : Ban 45 5 etat89 := viaPerm projC2P0 projC2PInv0 ban130 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban135 : Ban 45 5 etat90 := viaPerm projC2P0 projC2PInv0 ban131 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban136 : Ban 45 5 etat91 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban137 : Ban 45 5 etat92 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban138 : Ban 45 5 etat93 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban139 : Ban 45 5 etat94 := viaPerm projC2P1 projC2PInv1 ban138 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban140 : Ban 45 5 etat95 := viaPerm projC2P0 projC2PInv0 ban136 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban141 : Ban 45 5 etat96 := viaPerm projC2P0 projC2PInv0 ban137 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban142 : Ban 45 5 etat97 := viaPerm projC2P0 projC2PInv0 ban138 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban143 : Ban 45 5 etat98 := viaPerm projC2P0 projC2PInv0 ban139 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban144 : Ban 45 5 etat99 := viaPerm projC2P1 projC2PInv1 ban140 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban145 : Ban 45 5 etat100 := viaPerm projC2P1 projC2PInv1 ban141 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban146 : Ban 45 5 etat101 := viaPerm projC2P1 projC2PInv1 ban142 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban147 : Ban 45 5 etat102 := viaPerm projC2P0 projC2PInv0 ban146 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban148 : Ban 45 6 etat103 := viaBranch (ws := [etat52,etat53,etat54,etat55,etat56,etat57,etat58,etat59,etat60,etat61,etat62,etat63,etat64,etat65,etat66,etat67,etat68,etat69,etat70,etat71,etat72,etat73,etat74,etat75,etat76,etat77,etat78,etat79,etat80,etat81,etat82,etat83,etat84,etat85,etat86,etat87,etat88,etat89,etat90,etat91,etat92,etat93,etat94,etat95,etat96,etat97,etat98,etat99,etat100,etat101,etat102]) (consBan ban97 (consBan ban98 (consBan ban99 (consBan ban100 (consBan ban101 (consBan ban102 (consBan ban103 (consBan ban104 (consBan ban105 (consBan ban106 (consBan ban107 (consBan ban108 (consBan ban109 (consBan ban110 (consBan ban111 (consBan ban112 (consBan ban113 (consBan ban114 (consBan ban115 (consBan ban116 (consBan ban117 (consBan ban118 (consBan ban119 (consBan ban120 (consBan ban121 (consBan ban122 (consBan ban123 (consBan ban124 (consBan ban125 (consBan ban126 (consBan ban127 (consBan ban128 (consBan ban129 (consBan ban130 (consBan ban131 (consBan ban132 (consBan ban133 (consBan ban134 (consBan ban135 (consBan ban136 (consBan ban137 (consBan ban138 (consBan ban139 (consBan ban140 (consBan ban141 (consBan ban142 (consBan ban143 (consBan ban144 (consBan ban145 (consBan ban146 (consBan ban147 (nilBan _ _)))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem wide149 : Wide 45 6 etat103 := viaSub (ws := [etat42,etat103]) (consBan ban80 (consBan ban148 (nilBan _ _))) (by decide) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban150 : Ban 89 7 etat104 := viaCut projCut_top_2 wide149 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban151 : Ban 89 7 etat105 := viaPerm projTopP1 projTopPInv1 ban150 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban152 : Ban 89 7 etat106 := viaCut projCut_top_18 wide44 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban153 : Ban 20 3 etat1 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban154 : Ban 20 3 etat44 := viaPerm projC7P1 projC7PInv1 ban153 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban155 : Ban 20 3 etat45 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban156 : Ban 20 3 etat46 := viaPerm projC7P0 projC7PInv0 ban155 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban157 : Ban 28 3 etat11 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban158 : Ban 28 3 etat107 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban159 : Ban 28 3 etat108 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban160 : Ban 28 3 etat109 := viaPerm projC3P0 projC3PInv0 ban159 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban161 : Ban 16 4 etat47 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban162 : Ban 16 4 etat47 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban163 : Ban 40 5 etat48 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban164 : Ban 40 3 etat49 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban165 : Ban 40 3 etat50 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban166 : Ban 40 3 etat51 := viaPerm projC0P0 projC0PInv0 ban165 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban167 : Ban 45 5 etat42 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban168 : Ban 45 5 etat103 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban169 : Ban 45 5 etat110 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban170 : Ban 45 5 etat111 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban171 : Ban 45 5 etat112 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban172 : Ban 45 5 etat113 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban173 : Ban 45 5 etat114 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban174 : Ban 45 5 etat115 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban175 : Ban 45 5 etat116 := viaPerm projC2P1 projC2PInv1 ban169 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban176 : Ban 45 5 etat117 := viaPerm projC2P1 projC2PInv1 ban170 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban177 : Ban 45 5 etat118 := viaPerm projC2P1 projC2PInv1 ban171 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban178 : Ban 45 5 etat119 := viaPerm projC2P1 projC2PInv1 ban172 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban179 : Ban 45 5 etat120 := viaPerm projC2P1 projC2PInv1 ban173 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban180 : Ban 45 5 etat121 := viaPerm projC2P1 projC2PInv1 ban174 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban181 : Ban 45 5 etat122 := viaPerm projC2P0 projC2PInv0 ban175 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban182 : Ban 45 5 etat123 := viaPerm projC2P0 projC2PInv0 ban176 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban183 : Ban 45 5 etat124 := viaPerm projC2P0 projC2PInv0 ban177 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban184 : Ban 45 5 etat125 := viaPerm projC2P0 projC2PInv0 ban178 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban185 : Ban 45 5 etat126 := viaPerm projC2P0 projC2PInv0 ban179 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban186 : Ban 45 5 etat127 := viaPerm projC2P0 projC2PInv0 ban180 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban187 : Ban 45 5 etat128 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban188 : Ban 45 5 etat129 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban189 : Ban 45 5 etat130 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban190 : Ban 45 5 etat131 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban191 : Ban 45 5 etat132 := viaPerm projC2P1 projC2PInv1 ban187 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban192 : Ban 45 5 etat133 := viaPerm projC2P1 projC2PInv1 ban188 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban193 : Ban 45 5 etat134 := viaPerm projC2P1 projC2PInv1 ban189 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban194 : Ban 45 5 etat135 := viaPerm projC2P1 projC2PInv1 ban190 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban195 : Ban 45 5 etat136 := viaPerm projC2P0 projC2PInv0 ban191 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban196 : Ban 45 5 etat137 := viaPerm projC2P0 projC2PInv0 ban192 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban197 : Ban 45 5 etat138 := viaPerm projC2P0 projC2PInv0 ban193 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban198 : Ban 45 5 etat139 := viaPerm projC2P0 projC2PInv0 ban194 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban199 : Ban 45 5 etat140 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban200 : Ban 45 5 etat141 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban201 : Ban 45 5 etat142 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban202 : Ban 45 5 etat143 := viaPerm projC2P1 projC2PInv1 ban201 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban203 : Ban 45 5 etat144 := viaPerm projC2P0 projC2PInv0 ban199 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban204 : Ban 45 5 etat145 := viaPerm projC2P0 projC2PInv0 ban200 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban205 : Ban 45 5 etat146 := viaPerm projC2P0 projC2PInv0 ban201 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban206 : Ban 45 5 etat147 := viaPerm projC2P0 projC2PInv0 ban202 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban207 : Ban 45 5 etat148 := viaPerm projC2P1 projC2PInv1 ban203 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban208 : Ban 45 5 etat149 := viaPerm projC2P1 projC2PInv1 ban204 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban209 : Ban 45 5 etat150 := viaPerm projC2P1 projC2PInv1 ban205 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban210 : Ban 45 5 etat151 := viaPerm projC2P0 projC2PInv0 ban209 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban211 : Ban 45 6 etat53 := viaBranch (ws := [etat42,etat103,etat52,etat54,etat110,etat111,etat112,etat113,etat114,etat115,etat116,etat117,etat118,etat119,etat120,etat121,etat122,etat123,etat124,etat125,etat126,etat127,etat128,etat129,etat130,etat131,etat132,etat133,etat134,etat135,etat136,etat137,etat138,etat139,etat140,etat141,etat142,etat143,etat144,etat145,etat146,etat147,etat148,etat149,etat150,etat151]) (consBan ban167 (consBan ban168 (consBan ban97 (consBan ban99 (consBan ban169 (consBan ban170 (consBan ban171 (consBan ban172 (consBan ban173 (consBan ban174 (consBan ban175 (consBan ban176 (consBan ban177 (consBan ban178 (consBan ban179 (consBan ban180 (consBan ban181 (consBan ban182 (consBan ban183 (consBan ban184 (consBan ban185 (consBan ban186 (consBan ban187 (consBan ban188 (consBan ban189 (consBan ban190 (consBan ban191 (consBan ban192 (consBan ban193 (consBan ban194 (consBan ban195 (consBan ban196 (consBan ban197 (consBan ban198 (consBan ban199 (consBan ban200 (consBan ban201 (consBan ban202 (consBan ban203 (consBan ban204 (consBan ban205 (consBan ban206 (consBan ban207 (consBan ban208 (consBan ban209 (consBan ban210 (nilBan _ _))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem wide212 : Wide 45 6 etat53 := widen (by decide +kernel) ban211
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban213 : Ban 89 7 etat152 := viaCut projCut_top_2 wide212 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban214 : Ban 89 7 etat153 := viaCut projCut_top_18 wide44 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban215 : Ban 89 7 etat154 := viaPerm projTopP1 projTopPInv1 ban213 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban216 : Ban 89 7 etat155 := viaPerm projTopP1 projTopPInv1 ban214 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban217 : Ban 89 7 etat156 := viaCut projCut_top_18 wide44 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban218 : Ban 20 3 etat1 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban219 : Ban 20 3 etat44 := viaPerm projC15P2 projC15PInv2 ban218 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban220 : Ban 20 3 etat45 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban221 : Ban 20 3 etat46 := viaPerm projC15P0 projC15PInv0 ban220 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban222 : Ban 20 3 etat1 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban223 : Ban 20 3 etat44 := viaPerm projC14P2 projC14PInv2 ban222 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban224 : Ban 20 3 etat45 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban225 : Ban 20 3 etat46 := viaPerm projC14P0 projC14PInv0 ban224 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban226 : Ban 20 3 etat1 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban227 : Ban 20 3 etat44 := viaPerm projC13P2 projC13PInv2 ban226 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban228 : Ban 20 3 etat45 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban229 : Ban 20 3 etat46 := viaPerm projC13P0 projC13PInv0 ban228 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban230 : Ban 20 3 etat10 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban231 : Ban 40 5 etat157 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban232 : Ban 40 5 etat158 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban233 : Ban 40 5 etat159 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban234 : Ban 40 5 etat160 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban235 : Ban 40 4 etat161 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban236 : Ban 40 4 etat162 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban237 : Ban 40 4 etat163 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban238 : Ban 40 4 etat164 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban239 : Ban 40 4 etat165 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban240 : Ban 40 4 etat166 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban241 : Ban 40 4 etat167 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban242 : Ban 40 4 etat168 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban243 : Ban 40 4 etat169 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban244 : Ban 40 4 etat170 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban245 : Ban 40 4 etat171 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban246 : Ban 40 4 etat172 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban247 : Ban 40 4 etat173 := viaPerm projC1P0 projC1PInv0 ban241 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban248 : Ban 40 4 etat174 := viaPerm projC1P0 projC1PInv0 ban242 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban249 : Ban 40 4 etat175 := viaPerm projC1P0 projC1PInv0 ban243 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban250 : Ban 40 4 etat176 := viaPerm projC1P0 projC1PInv0 ban244 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban251 : Ban 40 4 etat177 := viaPerm projC1P0 projC1PInv0 ban245 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban252 : Ban 40 4 etat178 := viaPerm projC1P0 projC1PInv0 ban246 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban253 : Ban 20 3 etat179 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban254 : Ban 45 5 etat180 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban255 : Ban 45 5 etat181 := viaPerm projC2P5 projC2PInv5 ban168 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban256 : Ban 45 5 etat182 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban257 : Ban 45 5 etat183 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban258 : Ban 45 5 etat184 := viaPerm projC2P5 projC2PInv5 ban98 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban259 : Ban 45 5 etat185 := viaPerm projC2P5 projC2PInv5 ban257 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban260 : Ban 45 5 etat186 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban261 : Ban 45 5 etat187 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban262 : Ban 45 5 etat188 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban263 : Ban 45 5 etat189 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban264 : Ban 45 5 etat190 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban265 : Ban 45 5 etat191 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban266 : Ban 45 5 etat192 := viaPerm projC2P1 projC2PInv1 ban260 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban267 : Ban 45 5 etat193 := viaPerm projC2P1 projC2PInv1 ban261 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban268 : Ban 45 5 etat194 := viaPerm projC2P1 projC2PInv1 ban262 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban269 : Ban 45 5 etat195 := viaPerm projC2P1 projC2PInv1 ban263 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban270 : Ban 45 5 etat196 := viaPerm projC2P1 projC2PInv1 ban264 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban271 : Ban 45 5 etat197 := viaPerm projC2P1 projC2PInv1 ban265 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban272 : Ban 45 5 etat198 := viaPerm projC2P0 projC2PInv0 ban266 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban273 : Ban 45 5 etat199 := viaPerm projC2P0 projC2PInv0 ban267 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban274 : Ban 45 5 etat200 := viaPerm projC2P0 projC2PInv0 ban268 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban275 : Ban 45 5 etat201 := viaPerm projC2P0 projC2PInv0 ban269 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban276 : Ban 45 5 etat202 := viaPerm projC2P0 projC2PInv0 ban270 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban277 : Ban 45 5 etat203 := viaPerm projC2P0 projC2PInv0 ban271 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban278 : Ban 45 5 etat204 := viaPerm projC2P5 projC2PInv5 ban260 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban279 : Ban 45 5 etat205 := viaPerm projC2P5 projC2PInv5 ban261 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban280 : Ban 45 5 etat206 := viaPerm projC2P5 projC2PInv5 ban262 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban281 : Ban 45 5 etat207 := viaPerm projC2P5 projC2PInv5 ban263 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban282 : Ban 45 5 etat208 := viaPerm projC2P5 projC2PInv5 ban264 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban283 : Ban 45 5 etat209 := viaPerm projC2P5 projC2PInv5 ban265 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban284 : Ban 45 5 etat210 := viaPerm projC2P1 projC2PInv1 ban278 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban285 : Ban 45 5 etat211 := viaPerm projC2P1 projC2PInv1 ban279 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban286 : Ban 45 5 etat212 := viaPerm projC2P1 projC2PInv1 ban280 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban287 : Ban 45 5 etat213 := viaPerm projC2P1 projC2PInv1 ban281 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban288 : Ban 45 5 etat214 := viaPerm projC2P1 projC2PInv1 ban282 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban289 : Ban 45 5 etat215 := viaPerm projC2P1 projC2PInv1 ban283 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban290 : Ban 45 5 etat216 := viaPerm projC2P0 projC2PInv0 ban284 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban291 : Ban 45 5 etat217 := viaPerm projC2P0 projC2PInv0 ban285 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban292 : Ban 45 5 etat218 := viaPerm projC2P0 projC2PInv0 ban286 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban293 : Ban 45 5 etat219 := viaPerm projC2P0 projC2PInv0 ban287 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban294 : Ban 45 5 etat220 := viaPerm projC2P0 projC2PInv0 ban288 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban295 : Ban 45 5 etat221 := viaPerm projC2P0 projC2PInv0 ban289 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban296 : Ban 45 5 etat222 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban297 : Ban 45 5 etat223 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban298 : Ban 45 5 etat224 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban299 : Ban 45 5 etat225 := viaPerm projC2P1 projC2PInv1 ban298 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban300 : Ban 45 5 etat226 := viaPerm projC2P0 projC2PInv0 ban296 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban301 : Ban 45 5 etat227 := viaPerm projC2P0 projC2PInv0 ban297 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban302 : Ban 45 5 etat228 := viaPerm projC2P0 projC2PInv0 ban298 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban303 : Ban 45 5 etat229 := viaPerm projC2P0 projC2PInv0 ban299 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban304 : Ban 45 5 etat230 := viaPerm projC2P1 projC2PInv1 ban300 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban305 : Ban 45 5 etat231 := viaPerm projC2P1 projC2PInv1 ban301 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban306 : Ban 45 5 etat232 := viaPerm projC2P1 projC2PInv1 ban302 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban307 : Ban 45 5 etat233 := viaPerm projC2P0 projC2PInv0 ban306 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban308 : Ban 45 6 etat234 := viaBranch (ws := [etat180,etat42,etat103,etat181,etat182,etat53,etat183,etat184,etat185,etat186,etat187,etat188,etat189,etat190,etat191,etat192,etat193,etat194,etat195,etat196,etat197,etat198,etat199,etat200,etat201,etat202,etat203,etat204,etat205,etat206,etat207,etat208,etat209,etat210,etat211,etat212,etat213,etat214,etat215,etat216,etat217,etat218,etat219,etat220,etat221,etat222,etat223,etat224,etat225,etat226,etat227,etat228,etat229,etat230,etat231,etat232,etat233]) (consBan ban254 (consBan ban167 (consBan ban168 (consBan ban255 (consBan ban256 (consBan ban98 (consBan ban257 (consBan ban258 (consBan ban259 (consBan ban260 (consBan ban261 (consBan ban262 (consBan ban263 (consBan ban264 (consBan ban265 (consBan ban266 (consBan ban267 (consBan ban268 (consBan ban269 (consBan ban270 (consBan ban271 (consBan ban272 (consBan ban273 (consBan ban274 (consBan ban275 (consBan ban276 (consBan ban277 (consBan ban278 (consBan ban279 (consBan ban280 (consBan ban281 (consBan ban282 (consBan ban283 (consBan ban284 (consBan ban285 (consBan ban286 (consBan ban287 (consBan ban288 (consBan ban289 (consBan ban290 (consBan ban291 (consBan ban292 (consBan ban293 (consBan ban294 (consBan ban295 (consBan ban296 (consBan ban297 (consBan ban298 (consBan ban299 (consBan ban300 (consBan ban301 (consBan ban302 (consBan ban303 (consBan ban304 (consBan ban305 (consBan ban306 (consBan ban307 (nilBan _ _)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem wide309 : Wide 45 6 etat234 := widen (by decide +kernel) ban308
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban310 : Ban 89 7 etat235 := viaCut projCut_top_2 wide309 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban311 : Ban 16 3 etat236 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban312 : Ban 16 3 etat236 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban313 : Ban 40 5 etat237 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban314 : Ban 40 5 etat238 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban315 : Ban 40 5 etat239 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban316 : Ban 40 5 etat240 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban317 : Ban 40 5 etat241 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban318 : Ban 40 5 etat242 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban319 : Ban 40 5 etat243 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban320 : Ban 40 5 etat244 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban321 : Ban 40 5 etat245 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban322 : Ban 40 5 etat246 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban323 : Ban 40 5 etat247 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban324 : Ban 40 5 etat248 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban325 : Ban 40 5 etat249 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban326 : Ban 40 5 etat250 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban327 : Ban 40 5 etat251 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban328 : Ban 40 5 etat252 := viaPerm projC1P0 projC1PInv0 ban322 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban329 : Ban 40 5 etat253 := viaPerm projC1P0 projC1PInv0 ban323 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban330 : Ban 40 5 etat254 := viaPerm projC1P0 projC1PInv0 ban324 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban331 : Ban 40 5 etat255 := viaPerm projC1P0 projC1PInv0 ban325 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban332 : Ban 40 5 etat256 := viaPerm projC1P0 projC1PInv0 ban326 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban333 : Ban 40 5 etat257 := viaPerm projC1P0 projC1PInv0 ban327 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban334 : Ban 40 5 etat258 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban335 : Ban 40 5 etat259 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban336 : Ban 40 5 etat260 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban337 : Ban 40 5 etat261 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban338 : Ban 40 5 etat262 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban339 : Ban 40 5 etat263 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban340 : Ban 40 5 etat264 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban341 : Ban 40 5 etat265 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban342 : Ban 40 5 etat266 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban343 : Ban 40 5 etat267 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban344 : Ban 40 5 etat268 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban345 : Ban 40 5 etat269 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban346 : Ban 40 5 etat270 := viaPerm projC1P0 projC1PInv0 ban340 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban347 : Ban 40 5 etat271 := viaPerm projC1P0 projC1PInv0 ban341 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban348 : Ban 40 5 etat272 := viaPerm projC1P0 projC1PInv0 ban342 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban349 : Ban 40 5 etat273 := viaPerm projC1P0 projC1PInv0 ban343 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban350 : Ban 40 5 etat274 := viaPerm projC1P0 projC1PInv0 ban344 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban351 : Ban 40 5 etat275 := viaPerm projC1P0 projC1PInv0 ban345 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban352 : Ban 40 5 etat276 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban353 : Ban 40 5 etat277 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban354 : Ban 40 5 etat278 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban355 : Ban 40 5 etat279 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban356 : Ban 40 5 etat280 := viaPerm projC1P0 projC1PInv0 ban352 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban357 : Ban 40 5 etat281 := viaPerm projC1P0 projC1PInv0 ban353 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban358 : Ban 40 5 etat282 := viaPerm projC1P0 projC1PInv0 ban354 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban359 : Ban 40 5 etat283 := viaPerm projC1P0 projC1PInv0 ban355 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban360 : Ban 40 5 etat284 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban361 : Ban 40 5 etat285 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban362 : Ban 40 5 etat286 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban363 : Ban 40 5 etat287 := viaPerm projC1P0 projC1PInv0 ban362 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban364 : Ban 40 6 etat288 := viaBranch (ws := [etat237,etat238,etat239,etat240,etat241,etat242,etat243,etat244,etat245,etat246,etat247,etat248,etat249,etat250,etat251,etat252,etat253,etat254,etat255,etat256,etat257,etat258,etat259,etat260,etat261,etat262,etat263,etat264,etat265,etat266,etat267,etat268,etat269,etat270,etat271,etat272,etat273,etat274,etat275,etat276,etat277,etat278,etat279,etat280,etat281,etat282,etat283,etat284,etat285,etat286,etat287]) (consBan ban313 (consBan ban314 (consBan ban315 (consBan ban316 (consBan ban317 (consBan ban318 (consBan ban319 (consBan ban320 (consBan ban321 (consBan ban322 (consBan ban323 (consBan ban324 (consBan ban325 (consBan ban326 (consBan ban327 (consBan ban328 (consBan ban329 (consBan ban330 (consBan ban331 (consBan ban332 (consBan ban333 (consBan ban334 (consBan ban335 (consBan ban336 (consBan ban337 (consBan ban338 (consBan ban339 (consBan ban340 (consBan ban341 (consBan ban342 (consBan ban343 (consBan ban344 (consBan ban345 (consBan ban346 (consBan ban347 (consBan ban348 (consBan ban349 (consBan ban350 (consBan ban351 (consBan ban352 (consBan ban353 (consBan ban354 (consBan ban355 (consBan ban356 (consBan ban357 (consBan ban358 (consBan ban359 (consBan ban360 (consBan ban361 (consBan ban362 (consBan ban363 (nilBan _ _)))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem wide365 : Wide 40 6 etat288 := widen (by decide +kernel) ban364
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban366 : Ban 89 7 etat289 := viaCut projCut_top_1 wide365 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban367 : Ban 89 7 etat290 := viaCut projCut_top_18 wide44 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban368 : Ban 6 2 etat291 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban369 : Ban 16 3 etat292 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban370 : Ban 6 2 etat291 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban371 : Ban 16 3 etat292 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban372 : Ban 40 5 etat293 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban373 : Ban 40 5 etat294 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban374 : Ban 40 5 etat295 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban375 : Ban 20 4 etat296 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem wide376 : Wide 20 4 etat296 := widen (by decide +kernel) ban375
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban377 : Ban 40 5 etat297 := viaCut projCut_1_6 wide376 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban378 : Ban 40 5 etat298 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban379 : Ban 40 5 etat299 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban380 : Ban 40 5 etat300 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban381 : Ban 40 5 etat301 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban382 : Ban 40 5 etat302 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban383 : Ban 40 5 etat303 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban384 : Ban 40 5 etat304 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban385 : Ban 40 5 etat305 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban386 : Ban 40 5 etat306 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban387 : Ban 40 5 etat307 := viaCut projCut_1_6 wide376 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban388 : Ban 40 5 etat308 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban389 : Ban 40 5 etat309 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban390 : Ban 40 5 etat310 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban391 : Ban 40 5 etat311 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban392 : Ban 40 5 etat312 := viaPerm projC1P0 projC1PInv0 ban386 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban393 : Ban 40 5 etat313 := viaPerm projC1P0 projC1PInv0 ban387 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban394 : Ban 40 5 etat314 := viaPerm projC1P0 projC1PInv0 ban388 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban395 : Ban 40 5 etat315 := viaPerm projC1P0 projC1PInv0 ban389 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban396 : Ban 40 5 etat316 := viaPerm projC1P0 projC1PInv0 ban390 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban397 : Ban 40 5 etat317 := viaPerm projC1P0 projC1PInv0 ban391 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban398 : Ban 40 5 etat318 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban399 : Ban 40 4 etat319 := viaPerm projC1P1 projC1PInv1 ban235 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban400 : Ban 40 4 etat320 := viaPerm projC1P1 projC1PInv1 ban236 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban401 : Ban 40 4 etat321 := viaPerm projC1P1 projC1PInv1 ban237 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban402 : Ban 40 4 etat322 := viaPerm projC1P1 projC1PInv1 ban238 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban403 : Ban 40 4 etat323 := viaPerm projC1P1 projC1PInv1 ban239 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban404 : Ban 40 4 etat324 := viaPerm projC1P1 projC1PInv1 ban240 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban405 : Ban 40 4 etat325 := viaPerm projC1P1 projC1PInv1 ban241 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban406 : Ban 40 4 etat326 := viaPerm projC1P1 projC1PInv1 ban242 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban407 : Ban 40 4 etat327 := viaPerm projC1P1 projC1PInv1 ban243 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban408 : Ban 40 4 etat328 := viaPerm projC1P1 projC1PInv1 ban244 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban409 : Ban 40 4 etat329 := viaPerm projC1P1 projC1PInv1 ban245 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban410 : Ban 40 4 etat330 := viaPerm projC1P1 projC1PInv1 ban246 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban411 : Ban 40 4 etat331 := viaPerm projC1P0 projC1PInv0 ban405 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban412 : Ban 40 4 etat332 := viaPerm projC1P0 projC1PInv0 ban406 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban413 : Ban 40 4 etat333 := viaPerm projC1P0 projC1PInv0 ban407 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban414 : Ban 40 4 etat334 := viaPerm projC1P0 projC1PInv0 ban408 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban415 : Ban 40 4 etat335 := viaPerm projC1P0 projC1PInv0 ban409 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban416 : Ban 40 4 etat336 := viaPerm projC1P0 projC1PInv0 ban410 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban417 : Ban 20 3 etat179 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban418 : Ban 89 7 etat337 := viaCut projCut_top_2 wide309 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban419 : Ban 89 7 etat338 := viaCut projCut_top_18 wide44 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban420 : Ban 28 3 etat339 := viaPerm projC3P1 projC3PInv1 ban158 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban421 : Ban 28 3 etat340 := viaPerm projC3P1 projC3PInv1 ban157 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban422 : Ban 28 3 etat341 := viaPerm projC3P1 projC3PInv1 ban159 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban423 : Ban 28 3 etat342 := viaPerm projC3P0 projC3PInv0 ban422 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban424 : Ban 40 5 etat288 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban425 : Ban 40 5 etat343 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban426 : Ban 40 5 etat344 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban427 : Ban 40 5 etat345 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban428 : Ban 40 5 etat346 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban429 : Ban 40 5 etat347 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban430 : Ban 40 5 etat348 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban431 : Ban 40 5 etat349 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban432 : Ban 40 5 etat350 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban433 : Ban 40 5 etat351 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban434 : Ban 40 5 etat352 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban435 : Ban 40 5 etat353 := viaPerm projC1P0 projC1PInv0 ban431 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban436 : Ban 40 5 etat354 := viaPerm projC1P0 projC1PInv0 ban432 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban437 : Ban 40 5 etat355 := viaPerm projC1P0 projC1PInv0 ban433 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban438 : Ban 40 5 etat356 := viaPerm projC1P0 projC1PInv0 ban434 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban439 : Ban 40 5 etat357 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban440 : Ban 40 5 etat358 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban441 : Ban 40 5 etat359 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban442 : Ban 40 5 etat360 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban443 : Ban 40 5 etat361 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban444 : Ban 40 5 etat362 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban445 : Ban 40 5 etat363 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban446 : Ban 40 5 etat364 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban447 : Ban 40 5 etat365 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban448 : Ban 40 5 etat366 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban449 : Ban 40 5 etat367 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban450 : Ban 40 5 etat368 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban451 : Ban 40 5 etat369 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban452 : Ban 40 5 etat370 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban453 : Ban 40 5 etat371 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban454 : Ban 40 5 etat372 := viaPerm projC1P0 projC1PInv0 ban448 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban455 : Ban 40 5 etat373 := viaPerm projC1P0 projC1PInv0 ban449 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban456 : Ban 40 5 etat374 := viaPerm projC1P0 projC1PInv0 ban450 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban457 : Ban 40 5 etat375 := viaPerm projC1P0 projC1PInv0 ban451 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban458 : Ban 40 5 etat376 := viaPerm projC1P0 projC1PInv0 ban452 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban459 : Ban 40 5 etat377 := viaPerm projC1P0 projC1PInv0 ban453 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban460 : Ban 40 5 etat378 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban461 : Ban 40 5 etat379 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban462 : Ban 40 5 etat380 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban463 : Ban 40 5 etat381 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban464 : Ban 40 5 etat382 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban465 : Ban 40 5 etat383 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban466 : Ban 40 5 etat384 := viaPerm projC1P0 projC1PInv0 ban460 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban467 : Ban 40 5 etat385 := viaPerm projC1P0 projC1PInv0 ban461 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban468 : Ban 40 5 etat386 := viaPerm projC1P0 projC1PInv0 ban462 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban469 : Ban 40 5 etat387 := viaPerm projC1P0 projC1PInv0 ban463 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban470 : Ban 40 5 etat388 := viaPerm projC1P0 projC1PInv0 ban464 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban471 : Ban 40 5 etat389 := viaPerm projC1P0 projC1PInv0 ban465 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban472 : Ban 40 5 etat390 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban473 : Ban 40 5 etat391 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban474 : Ban 40 5 etat392 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban475 : Ban 40 5 etat393 := viaPerm projC1P0 projC1PInv0 ban474 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban476 : Ban 40 6 etat244 := viaBranch (ws := [etat243,etat288,etat245,etat343,etat344,etat345,etat346,etat347,etat348,etat349,etat350,etat351,etat352,etat353,etat354,etat355,etat356,etat357,etat358,etat359,etat360,etat361,etat362,etat363,etat364,etat365,etat366,etat367,etat368,etat369,etat370,etat371,etat372,etat373,etat374,etat375,etat376,etat377,etat378,etat379,etat380,etat381,etat382,etat383,etat384,etat385,etat386,etat387,etat388,etat389,etat390,etat391,etat392,etat393]) (consBan ban319 (consBan ban424 (consBan ban321 (consBan ban425 (consBan ban426 (consBan ban427 (consBan ban428 (consBan ban429 (consBan ban430 (consBan ban431 (consBan ban432 (consBan ban433 (consBan ban434 (consBan ban435 (consBan ban436 (consBan ban437 (consBan ban438 (consBan ban439 (consBan ban440 (consBan ban441 (consBan ban442 (consBan ban443 (consBan ban444 (consBan ban445 (consBan ban446 (consBan ban447 (consBan ban448 (consBan ban449 (consBan ban450 (consBan ban451 (consBan ban452 (consBan ban453 (consBan ban454 (consBan ban455 (consBan ban456 (consBan ban457 (consBan ban458 (consBan ban459 (consBan ban460 (consBan ban461 (consBan ban462 (consBan ban463 (consBan ban464 (consBan ban465 (consBan ban466 (consBan ban467 (consBan ban468 (consBan ban469 (consBan ban470 (consBan ban471 (consBan ban472 (consBan ban473 (consBan ban474 (consBan ban475 (nilBan _ _))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem wide477 : Wide 40 6 etat244 := widen (by decide +kernel) ban476
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban478 : Ban 89 7 etat394 := viaCut projCut_top_1 wide477 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban479 : Ban 89 7 etat395 := viaCut projCut_top_18 wide44 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban480 : Ban 89 7 etat396 := viaCut projCut_top_18 wide44 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban481 : Ban 20 3 etat397 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban482 : Ban 20 3 etat397 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban483 : Ban 45 5 etat398 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban484 : Ban 45 5 etat399 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban485 : Ban 45 5 etat400 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban486 : Ban 45 5 etat401 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban487 : Ban 45 5 etat402 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban488 : Ban 45 5 etat403 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban489 : Ban 45 5 etat404 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban490 : Ban 45 5 etat405 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban491 : Ban 45 5 etat406 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban492 : Ban 45 5 etat407 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban493 : Ban 45 5 etat408 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban494 : Ban 45 5 etat409 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban495 : Ban 45 5 etat410 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban496 : Ban 45 5 etat411 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban497 : Ban 45 5 etat412 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban498 : Ban 45 5 etat413 := viaPerm projC2P0 projC2PInv0 ban489 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban499 : Ban 45 5 etat414 := viaPerm projC2P0 projC2PInv0 ban490 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban500 : Ban 45 5 etat415 := viaPerm projC2P0 projC2PInv0 ban491 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban501 : Ban 45 5 etat416 := viaPerm projC2P0 projC2PInv0 ban492 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban502 : Ban 45 5 etat417 := viaPerm projC2P0 projC2PInv0 ban493 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban503 : Ban 45 5 etat418 := viaPerm projC2P0 projC2PInv0 ban494 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban504 : Ban 45 5 etat419 := viaPerm projC2P0 projC2PInv0 ban495 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban505 : Ban 45 5 etat420 := viaPerm projC2P0 projC2PInv0 ban496 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban506 : Ban 45 5 etat421 := viaPerm projC2P0 projC2PInv0 ban497 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban507 : Ban 45 5 etat422 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban508 : Ban 45 5 etat423 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban509 : Ban 45 5 etat424 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban510 : Ban 45 5 etat425 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban511 : Ban 45 5 etat426 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban512 : Ban 45 5 etat427 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban513 : Ban 45 5 etat428 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban514 : Ban 45 5 etat429 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban515 : Ban 45 5 etat430 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban516 : Ban 45 5 etat431 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban517 : Ban 45 5 etat432 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban518 : Ban 45 5 etat433 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban519 : Ban 45 5 etat434 := viaPerm projC2P0 projC2PInv0 ban513 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban520 : Ban 45 5 etat435 := viaPerm projC2P0 projC2PInv0 ban514 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban521 : Ban 45 5 etat436 := viaPerm projC2P0 projC2PInv0 ban515 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban522 : Ban 45 5 etat437 := viaPerm projC2P0 projC2PInv0 ban516 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban523 : Ban 45 5 etat438 := viaPerm projC2P0 projC2PInv0 ban517 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban524 : Ban 45 5 etat439 := viaPerm projC2P0 projC2PInv0 ban518 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban525 : Ban 45 5 etat440 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban526 : Ban 45 5 etat441 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban527 : Ban 45 5 etat442 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban528 : Ban 45 5 etat443 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban529 : Ban 45 5 etat444 := viaPerm projC2P0 projC2PInv0 ban525 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban530 : Ban 45 5 etat445 := viaPerm projC2P0 projC2PInv0 ban526 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban531 : Ban 45 5 etat446 := viaPerm projC2P0 projC2PInv0 ban527 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban532 : Ban 45 5 etat447 := viaPerm projC2P0 projC2PInv0 ban528 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban533 : Ban 45 5 etat448 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban534 : Ban 45 5 etat449 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban535 : Ban 45 5 etat450 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban536 : Ban 45 5 etat451 := viaPerm projC2P0 projC2PInv0 ban535 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban537 : Ban 45 6 etat187 := viaBranch (ws := [etat398,etat399,etat400,etat401,etat402,etat190,etat403,etat404,etat405,etat406,etat407,etat408,etat409,etat410,etat411,etat412,etat413,etat414,etat415,etat416,etat417,etat418,etat419,etat420,etat421,etat422,etat423,etat424,etat425,etat426,etat427,etat428,etat429,etat430,etat431,etat432,etat433,etat434,etat435,etat436,etat437,etat438,etat439,etat440,etat441,etat442,etat443,etat444,etat445,etat446,etat447,etat448,etat449,etat450,etat451]) (consBan ban483 (consBan ban484 (consBan ban485 (consBan ban486 (consBan ban487 (consBan ban264 (consBan ban488 (consBan ban489 (consBan ban490 (consBan ban491 (consBan ban492 (consBan ban493 (consBan ban494 (consBan ban495 (consBan ban496 (consBan ban497 (consBan ban498 (consBan ban499 (consBan ban500 (consBan ban501 (consBan ban502 (consBan ban503 (consBan ban504 (consBan ban505 (consBan ban506 (consBan ban507 (consBan ban508 (consBan ban509 (consBan ban510 (consBan ban511 (consBan ban512 (consBan ban513 (consBan ban514 (consBan ban515 (consBan ban516 (consBan ban517 (consBan ban518 (consBan ban519 (consBan ban520 (consBan ban521 (consBan ban522 (consBan ban523 (consBan ban524 (consBan ban525 (consBan ban526 (consBan ban527 (consBan ban528 (consBan ban529 (consBan ban530 (consBan ban531 (consBan ban532 (consBan ban533 (consBan ban534 (consBan ban535 (consBan ban536 (nilBan _ _)))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem wide538 : Wide 45 6 etat187 := widen (by decide +kernel) ban537
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban539 : Ban 89 7 etat452 := viaCut projCut_top_2 wide538 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban540 : Ban 20 4 etat296 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem wide541 : Wide 20 4 etat296 := widen (by decide +kernel) ban540
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban542 : Ban 89 7 etat453 := viaCut projCut_top_7 wide541 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban543 : Ban 89 7 etat454 := viaCut projCut_top_18 wide44 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban544 : Ban 20 3 etat455 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban545 : Ban 20 3 etat456 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban546 : Ban 20 3 etat457 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban547 : Ban 20 3 etat455 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban548 : Ban 20 3 etat456 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban549 : Ban 20 3 etat457 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban550 : Ban 9 3 etat458 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban551 : Ban 9 3 etat458 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban552 : Ban 28 4 etat459 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban553 : Ban 28 4 etat460 := viaPerm projC3P3 projC3PInv3 ban552 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban554 : Ban 28 4 etat461 := viaPerm projC3P1 projC3PInv1 ban553 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban555 : Ban 28 4 etat462 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban556 : Ban 28 4 etat463 := viaPerm projC3P0 projC3PInv0 ban555 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban557 : Ban 45 5 etat464 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban558 : Ban 45 5 etat465 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban559 : Ban 45 5 etat466 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban560 : Ban 45 5 etat467 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban561 : Ban 45 5 etat468 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban562 : Ban 45 5 etat469 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban563 : Ban 45 5 etat470 := viaPerm projC2P1 projC2PInv1 ban496 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban564 : Ban 45 5 etat471 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban565 : Ban 45 5 etat472 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban566 : Ban 45 5 etat473 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban567 : Ban 45 5 etat474 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban568 : Ban 45 5 etat475 := viaPerm projC2P0 projC2PInv0 ban562 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban569 : Ban 45 5 etat476 := viaPerm projC2P0 projC2PInv0 ban563 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban570 : Ban 45 5 etat477 := viaPerm projC2P0 projC2PInv0 ban564 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban571 : Ban 45 5 etat478 := viaPerm projC2P0 projC2PInv0 ban565 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban572 : Ban 45 5 etat479 := viaPerm projC2P0 projC2PInv0 ban566 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban573 : Ban 45 5 etat480 := viaPerm projC2P0 projC2PInv0 ban567 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban574 : Ban 45 5 etat481 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban575 : Ban 45 5 etat482 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban576 : Ban 45 5 etat483 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban577 : Ban 45 5 etat484 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban578 : Ban 45 5 etat485 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban579 : Ban 45 5 etat486 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban580 : Ban 45 5 etat487 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban581 : Ban 45 5 etat488 := viaPerm projC2P7 projC2PInv7 ban517 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban582 : Ban 45 5 etat489 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban583 : Ban 45 5 etat490 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban584 : Ban 45 5 etat491 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban585 : Ban 45 5 etat492 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban586 : Ban 45 5 etat493 := viaPerm projC2P0 projC2PInv0 ban580 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban587 : Ban 45 5 etat494 := viaPerm projC2P0 projC2PInv0 ban581 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban588 : Ban 45 5 etat495 := viaPerm projC2P0 projC2PInv0 ban582 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban589 : Ban 45 5 etat496 := viaPerm projC2P0 projC2PInv0 ban583 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban590 : Ban 45 5 etat497 := viaPerm projC2P0 projC2PInv0 ban584 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban591 : Ban 45 5 etat498 := viaPerm projC2P0 projC2PInv0 ban585 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban592 : Ban 45 5 etat499 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban593 : Ban 45 5 etat500 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban594 : Ban 45 5 etat501 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban595 : Ban 45 5 etat502 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban596 : Ban 45 5 etat503 := viaPerm projC2P0 projC2PInv0 ban592 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban597 : Ban 45 5 etat504 := viaPerm projC2P0 projC2PInv0 ban593 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban598 : Ban 45 5 etat505 := viaPerm projC2P0 projC2PInv0 ban594 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban599 : Ban 45 5 etat506 := viaPerm projC2P0 projC2PInv0 ban595 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban600 : Ban 45 5 etat507 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban601 : Ban 45 5 etat508 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban602 : Ban 45 5 etat509 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban603 : Ban 45 5 etat510 := viaPerm projC2P0 projC2PInv0 ban602 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban604 : Ban 45 6 etat190 := viaBranch (ws := [etat464,etat465,etat466,etat114,etat467,etat468,etat402,etat187,etat403,etat469,etat470,etat471,etat472,etat473,etat474,etat475,etat476,etat477,etat478,etat479,etat480,etat481,etat482,etat483,etat484,etat485,etat486,etat487,etat488,etat489,etat490,etat491,etat492,etat493,etat494,etat495,etat496,etat497,etat498,etat499,etat500,etat501,etat502,etat503,etat504,etat505,etat506,etat507,etat508,etat509,etat510]) (consBan ban557 (consBan ban558 (consBan ban559 (consBan ban173 (consBan ban560 (consBan ban561 (consBan ban487 (consBan ban261 (consBan ban488 (consBan ban562 (consBan ban563 (consBan ban564 (consBan ban565 (consBan ban566 (consBan ban567 (consBan ban568 (consBan ban569 (consBan ban570 (consBan ban571 (consBan ban572 (consBan ban573 (consBan ban574 (consBan ban575 (consBan ban576 (consBan ban577 (consBan ban578 (consBan ban579 (consBan ban580 (consBan ban581 (consBan ban582 (consBan ban583 (consBan ban584 (consBan ban585 (consBan ban586 (consBan ban587 (consBan ban588 (consBan ban589 (consBan ban590 (consBan ban591 (consBan ban592 (consBan ban593 (consBan ban594 (consBan ban595 (consBan ban596 (consBan ban597 (consBan ban598 (consBan ban599 (consBan ban600 (consBan ban601 (consBan ban602 (consBan ban603 (nilBan _ _)))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem wide605 : Wide 45 6 etat190 := widen (by decide +kernel) ban604
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban606 : Ban 89 7 etat511 := viaCut projCut_top_2 wide605 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban607 : Ban 20 4 etat296 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem wide608 : Wide 20 4 etat296 := widen (by decide +kernel) ban607
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban609 : Ban 89 7 etat512 := viaCut projCut_top_13 wide608 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban610 : Ban 89 7 etat513 := viaCut projCut_top_18 wide44 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban611 : Ban 20 3 etat514 := viaPerm projC15P0 projC15PInv0 ban482 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban612 : Ban 20 3 etat397 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban613 : Ban 20 3 etat397 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban614 : Ban 28 4 etat515 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban615 : Ban 28 4 etat516 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban616 : Ban 28 4 etat517 := viaPerm projC3P1 projC3PInv1 ban615 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban617 : Ban 28 4 etat518 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban618 : Ban 28 4 etat519 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban619 : Ban 28 3 etat520 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban620 : Ban 28 3 etat521 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban621 : Ban 40 5 etat522 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban622 : Ban 40 3 etat523 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban623 : Ban 40 3 etat524 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban624 : Ban 40 3 etat525 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban625 : Ban 45 6 etat193 := viaPerm projC2P1 projC2PInv1 ban537 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem wide626 : Wide 45 6 etat193 := widen (by decide +kernel) ban625
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban627 : Ban 89 7 etat526 := viaCut projCut_top_2 wide626 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban628 : Ban 16 3 etat47 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem wide629 : Wide 6 2 etat291 := widen (by decide +kernel) ban370
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban630 : Ban 24 5 etat527 := viaCut projCut_5_20 wide629 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban631 : Ban 24 4 etat528 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem wide632 : Wide 6 2 etat291 := widen (by decide +kernel) ban368
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban633 : Ban 24 5 etat527 := viaCut projCut_4_19 wide632 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban634 : Ban 24 4 etat528 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban635 : Ban 45 5 etat529 := viaPerm projC2P5 projC2PInv5 ban110 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban636 : Ban 45 5 etat530 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban637 : Ban 45 5 etat531 := viaPerm projC2P5 projC2PInv5 ban111 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban638 : Ban 45 5 etat532 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban639 : Ban 45 5 etat533 := viaPerm projC2P5 projC2PInv5 ban192 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban640 : Ban 45 5 etat534 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban641 : Ban 45 5 etat535 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban642 : Ban 45 5 etat536 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban643 : Ban 45 5 etat537 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban644 : Ban 45 5 etat538 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban645 : Ban 45 5 etat539 := viaPerm projC2P1 projC2PInv1 ban487 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban646 : Ban 45 5 etat540 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban647 : Ban 45 5 etat541 := viaPerm projC2P1 projC2PInv1 ban488 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban648 : Ban 45 5 etat542 := viaPerm projC2P3 projC2PInv3 ban500 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban649 : Ban 45 5 etat543 := viaPerm projC2P2 projC2PInv2 ban640 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban650 : Ban 45 5 etat544 := viaPerm projC2P3 projC2PInv3 ban502 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban651 : Ban 45 5 etat545 := viaPerm projC2P4 projC2PInv4 ban641 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban652 : Ban 45 5 etat546 := viaPerm projC2P3 projC2PInv3 ban570 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban653 : Ban 45 5 etat547 := viaPerm projC2P5 projC2PInv5 ban515 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban654 : Ban 45 5 etat548 := viaPerm projC2P5 projC2PInv5 ban582 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban655 : Ban 45 5 etat549 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban656 : Ban 45 5 etat550 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban657 : Ban 45 5 etat551 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban658 : Ban 45 5 etat552 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban659 : Ban 45 5 etat553 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban660 : Ban 45 5 etat554 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban661 : Ban 45 5 etat555 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban662 : Ban 45 5 etat556 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban663 : Ban 45 5 etat557 := viaPerm projC2P4 projC2PInv4 ban653 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban664 : Ban 45 5 etat558 := viaPerm projC2P4 projC2PInv4 ban654 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban665 : Ban 45 5 etat559 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban666 : Ban 45 5 etat560 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban667 : Ban 45 5 etat561 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban668 : Ban 45 5 etat562 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban669 : Ban 45 5 etat563 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban670 : Ban 45 5 etat564 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban671 : Ban 45 5 etat565 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban672 : Ban 45 5 etat566 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban673 : Ban 45 5 etat567 := viaPerm projC2P4 projC2PInv4 ban665 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban674 : Ban 45 5 etat568 := viaPerm projC2P4 projC2PInv4 ban666 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban675 : Ban 45 5 etat569 := viaPerm projC2P4 projC2PInv4 ban668 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban676 : Ban 45 5 etat570 := viaPerm projC2P4 projC2PInv4 ban667 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban677 : Ban 45 5 etat571 := viaPerm projC2P4 projC2PInv4 ban669 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban678 : Ban 45 5 etat572 := viaPerm projC2P2 projC2PInv2 ban670 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban679 : Ban 45 5 etat573 := viaPerm projC2P4 projC2PInv4 ban672 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban680 : Ban 45 5 etat574 := viaPerm projC2P4 projC2PInv4 ban671 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban681 : Ban 45 6 etat194 := viaBranch (ws := [etat529,etat530,etat531,etat532,etat533,etat406,etat534,etat408,etat535,etat471,etat536,etat537,etat538,etat539,etat540,etat541,etat197,etat542,etat543,etat544,etat545,etat546,etat547,etat548,etat549,etat550,etat551,etat552,etat553,etat554,etat555,etat556,etat557,etat558,etat559,etat560,etat561,etat562,etat563,etat564,etat565,etat566,etat195,etat567,etat568,etat569,etat570,etat571,etat572,etat573,etat574]) (consBan ban635 (consBan ban636 (consBan ban637 (consBan ban638 (consBan ban639 (consBan ban491 (consBan ban640 (consBan ban493 (consBan ban641 (consBan ban564 (consBan ban642 (consBan ban643 (consBan ban644 (consBan ban645 (consBan ban646 (consBan ban647 (consBan ban271 (consBan ban648 (consBan ban649 (consBan ban650 (consBan ban651 (consBan ban652 (consBan ban653 (consBan ban654 (consBan ban655 (consBan ban656 (consBan ban657 (consBan ban658 (consBan ban659 (consBan ban660 (consBan ban661 (consBan ban662 (consBan ban663 (consBan ban664 (consBan ban665 (consBan ban666 (consBan ban667 (consBan ban668 (consBan ban669 (consBan ban670 (consBan ban671 (consBan ban672 (consBan ban269 (consBan ban673 (consBan ban674 (consBan ban675 (consBan ban676 (consBan ban677 (consBan ban678 (consBan ban679 (consBan ban680 (nilBan _ _)))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem wide682 : Wide 45 6 etat194 := viaSub (ws := [etat234,etat193,etat194]) (consBan ban308 (consBan ban625 (consBan ban681 (nilBan _ _)))) (by decide) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban683 : Ban 89 7 etat575 := viaCut projCut_top_2 wide682 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban684 : Ban 89 7 etat576 := viaCut projCut_top_18 wide44 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban685 : Ban 20 3 etat577 := viaPerm projC15P0 projC15PInv0 ban544 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban686 : Ban 20 3 etat578 := viaPerm projC15P0 projC15PInv0 ban546 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban687 : Ban 20 3 etat579 := viaPerm projC15P0 projC15PInv0 ban545 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban688 : Ban 20 3 etat455 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban689 : Ban 20 3 etat456 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban690 : Ban 20 3 etat457 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban691 : Ban 20 3 etat455 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban692 : Ban 20 3 etat456 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban693 : Ban 20 3 etat457 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban694 : Ban 28 4 etat580 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban695 : Ban 28 4 etat581 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban696 : Ban 28 4 etat582 := viaPerm projC3P1 projC3PInv1 ban695 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban697 : Ban 28 4 etat583 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban698 : Ban 28 4 etat584 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban699 : Ban 28 3 etat585 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban700 : Ban 28 3 etat586 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban701 : Ban 28 3 etat587 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban702 : Ban 40 5 etat588 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban703 : Ban 40 3 etat589 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban704 : Ban 40 3 etat590 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban705 : Ban 40 3 etat591 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban706 : Ban 45 6 etat196 := viaPerm projC2P1 projC2PInv1 ban604 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem wide707 : Wide 45 6 etat196 := widen (by decide +kernel) ban706
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban708 : Ban 89 7 etat592 := viaCut projCut_top_2 wide707 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban709 : Ban 20 4 etat296 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem wide710 : Wide 20 4 etat296 := widen (by decide +kernel) ban709
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban711 : Ban 89 7 etat593 := viaCut projCut_top_14 wide710 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban712 : Ban 89 7 etat594 := viaPerm projTopP0 projTopPInv0 ban610 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban713 : Ban 89 7 etat595 := viaPerm projTopP0 projTopPInv0 ban627 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban714 : Ban 89 7 etat596 := viaPerm projTopP0 projTopPInv0 ban683 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban715 : Ban 89 7 etat597 := viaPerm projTopP0 projTopPInv0 ban684 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban716 : Ban 89 7 etat598 := viaPerm projTopP0 projTopPInv0 ban708 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban717 : Ban 89 7 etat599 := viaPerm projTopP0 projTopPInv0 ban711 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban718 : Ban 89 7 etat600 := viaPerm projTopP1 projTopPInv1 ban217 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban719 : Ban 89 7 etat601 := viaPerm projTopP1 projTopPInv1 ban310 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban720 : Ban 89 7 etat602 := viaPerm projTopP1 projTopPInv1 ban366 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban721 : Ban 89 7 etat603 := viaPerm projTopP1 projTopPInv1 ban367 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban722 : Ban 89 7 etat604 := viaPerm projTopP1 projTopPInv1 ban418 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban723 : Ban 89 7 etat605 := viaPerm projTopP1 projTopPInv1 ban419 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban724 : Ban 89 7 etat606 := viaPerm projTopP1 projTopPInv1 ban478 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban725 : Ban 89 7 etat607 := viaPerm projTopP1 projTopPInv1 ban479 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban726 : Ban 89 7 etat608 := viaPerm projTopP1 projTopPInv1 ban480 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban727 : Ban 89 7 etat609 := viaPerm projTopP1 projTopPInv1 ban539 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban728 : Ban 89 7 etat610 := viaPerm projTopP1 projTopPInv1 ban542 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban729 : Ban 89 7 etat611 := viaPerm projTopP1 projTopPInv1 ban543 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban730 : Ban 89 7 etat612 := viaPerm projTopP1 projTopPInv1 ban606 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban731 : Ban 89 7 etat613 := viaPerm projTopP1 projTopPInv1 ban609 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban732 : Ban 89 7 etat614 := viaPerm projTopP1 projTopPInv1 ban610 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban733 : Ban 89 7 etat615 := viaPerm projTopP1 projTopPInv1 ban627 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban734 : Ban 89 7 etat616 := viaPerm projTopP1 projTopPInv1 ban683 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban735 : Ban 89 7 etat617 := viaPerm projTopP1 projTopPInv1 ban684 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban736 : Ban 89 7 etat618 := viaPerm projTopP1 projTopPInv1 ban708 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban737 : Ban 89 7 etat619 := viaPerm projTopP1 projTopPInv1 ban711 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban738 : Ban 89 7 etat620 := viaPerm projTopP0 projTopPInv0 ban732 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban739 : Ban 89 7 etat621 := viaPerm projTopP0 projTopPInv0 ban733 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban740 : Ban 89 7 etat622 := viaPerm projTopP0 projTopPInv0 ban734 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban741 : Ban 89 7 etat623 := viaPerm projTopP0 projTopPInv0 ban735 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban742 : Ban 89 7 etat624 := viaPerm projTopP0 projTopPInv0 ban736 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban743 : Ban 89 7 etat625 := viaPerm projTopP0 projTopPInv0 ban737 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban744 : Ban 89 7 etat626 := viaCut projCut_top_18 wide44 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban745 : Ban 16 3 etat627 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban746 : Ban 16 3 etat627 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban747 : Ban 16 3 etat627 := viaPerm projC11P0 projC11PInv0 ban312 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban748 : Ban 16 3 etat627 := viaPerm projC12P0 projC12PInv0 ban311 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban749 : Ban 40 6 etat628 := viaPerm projC1P1 projC1PInv1 ban364 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem wide750 : Wide 40 6 etat628 := widen (by decide +kernel) ban749
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban751 : Ban 89 7 etat629 := viaCut projCut_top_1 wide750 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban752 : Ban 20 3 etat10 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban753 : Ban 40 5 etat630 := viaPerm projC1P1 projC1PInv1 ban231 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban754 : Ban 40 5 etat631 := viaPerm projC1P1 projC1PInv1 ban232 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban755 : Ban 40 5 etat632 := viaPerm projC1P1 projC1PInv1 ban234 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban756 : Ban 40 5 etat630 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban757 : Ban 40 5 etat631 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban758 : Ban 40 5 etat159 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban759 : Ban 40 5 etat632 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban760 : Ban 40 4 etat319 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban761 : Ban 40 4 etat320 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban762 : Ban 40 4 etat321 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban763 : Ban 40 4 etat322 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban764 : Ban 40 4 etat323 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban765 : Ban 40 4 etat324 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban766 : Ban 40 4 etat325 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban767 : Ban 40 4 etat326 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban768 : Ban 40 4 etat327 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban769 : Ban 40 4 etat328 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban770 : Ban 40 4 etat329 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban771 : Ban 40 4 etat330 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban772 : Ban 40 4 etat331 := viaPerm projC0P0 projC0PInv0 ban766 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban773 : Ban 40 4 etat332 := viaPerm projC0P0 projC0PInv0 ban767 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban774 : Ban 40 4 etat333 := viaPerm projC0P0 projC0PInv0 ban768 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban775 : Ban 40 4 etat334 := viaPerm projC0P0 projC0PInv0 ban769 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban776 : Ban 40 4 etat335 := viaPerm projC0P0 projC0PInv0 ban770 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban777 : Ban 40 4 etat336 := viaPerm projC0P0 projC0PInv0 ban771 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban778 : Ban 89 7 etat633 := viaCut projCut_top_2 wide309 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban779 : Ban 89 7 etat634 := viaCut projCut_top_13 wide608 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban780 : Ban 24 4 etat635 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban781 : Ban 24 4 etat636 := viaPerm projC4P0 projC4PInv0 ban780 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban782 : Ban 24 4 etat637 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban783 : Ban 24 4 etat638 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban784 : Ban 24 4 etat639 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban785 : Ban 24 4 etat635 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban786 : Ban 24 4 etat636 := viaPerm projC5P0 projC5PInv0 ban785 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban787 : Ban 24 4 etat637 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban788 : Ban 24 4 etat638 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban789 : Ban 24 4 etat639 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban790 : Ban 40 6 etat640 := viaPerm projC1P1 projC1PInv1 ban476 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem wide791 : Wide 40 6 etat640 := widen (by decide +kernel) ban790
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban792 : Ban 89 7 etat641 := viaCut projCut_top_1 wide791 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban793 : Ban 89 7 etat642 := viaCut projCut_top_18 wide44 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban794 : Ban 6 2 etat291 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban795 : Ban 16 3 etat643 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban796 : Ban 6 2 etat291 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban797 : Ban 16 3 etat643 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban798 : Ban 6 2 etat291 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban799 : Ban 16 3 etat643 := viaPerm projC11P0 projC11PInv0 ban369 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban800 : Ban 6 2 etat291 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban801 : Ban 16 3 etat643 := viaPerm projC12P0 projC12PInv0 ban371 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban802 : Ban 9 3 etat644 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban803 : Ban 24 4 etat645 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban804 : Ban 24 3 etat646 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban805 : Ban 24 3 etat647 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban806 : Ban 9 3 etat644 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban807 : Ban 24 4 etat645 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban808 : Ban 24 3 etat646 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban809 : Ban 24 3 etat647 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban810 : Ban 40 5 etat648 := viaPerm projC1P1 projC1PInv1 ban372 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban811 : Ban 40 5 etat649 := viaPerm projC1P1 projC1PInv1 ban373 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban812 : Ban 40 5 etat650 := viaPerm projC1P1 projC1PInv1 ban374 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban813 : Ban 40 5 etat651 := viaPerm projC1P1 projC1PInv1 ban377 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban814 : Ban 40 5 etat652 := viaPerm projC1P1 projC1PInv1 ban378 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban815 : Ban 40 5 etat653 := viaPerm projC1P1 projC1PInv1 ban379 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban816 : Ban 40 5 etat654 := viaPerm projC1P1 projC1PInv1 ban380 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban817 : Ban 40 5 etat655 := viaPerm projC1P1 projC1PInv1 ban381 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban818 : Ban 40 5 etat656 := viaPerm projC1P1 projC1PInv1 ban382 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban819 : Ban 40 5 etat657 := viaPerm projC1P1 projC1PInv1 ban383 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban820 : Ban 40 5 etat658 := viaPerm projC1P1 projC1PInv1 ban384 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban821 : Ban 40 5 etat659 := viaPerm projC1P1 projC1PInv1 ban385 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban822 : Ban 40 5 etat660 := viaPerm projC1P1 projC1PInv1 ban386 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban823 : Ban 40 5 etat661 := viaPerm projC1P1 projC1PInv1 ban387 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban824 : Ban 40 5 etat662 := viaPerm projC1P1 projC1PInv1 ban388 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban825 : Ban 40 5 etat663 := viaPerm projC1P1 projC1PInv1 ban389 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban826 : Ban 40 5 etat664 := viaPerm projC1P1 projC1PInv1 ban390 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban827 : Ban 40 5 etat665 := viaPerm projC1P1 projC1PInv1 ban391 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban828 : Ban 40 5 etat666 := viaPerm projC1P0 projC1PInv0 ban822 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban829 : Ban 40 5 etat667 := viaPerm projC1P0 projC1PInv0 ban823 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban830 : Ban 40 5 etat668 := viaPerm projC1P0 projC1PInv0 ban824 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban831 : Ban 40 5 etat669 := viaPerm projC1P0 projC1PInv0 ban825 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban832 : Ban 40 5 etat670 := viaPerm projC1P0 projC1PInv0 ban826 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban833 : Ban 40 5 etat671 := viaPerm projC1P0 projC1PInv0 ban827 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban834 : Ban 40 5 etat672 := viaPerm projC1P1 projC1PInv1 ban398 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban835 : Ban 40 5 etat648 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban836 : Ban 40 5 etat649 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban837 : Ban 40 5 etat650 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban838 : Ban 40 5 etat651 := viaCut projCut_0_7 wide541 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban839 : Ban 40 5 etat652 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban840 : Ban 40 5 etat653 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban841 : Ban 40 5 etat654 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban842 : Ban 40 5 etat655 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban843 : Ban 40 5 etat656 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban844 : Ban 40 5 etat657 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban845 : Ban 40 5 etat658 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban846 : Ban 40 5 etat659 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban847 : Ban 40 5 etat660 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban848 : Ban 20 4 etat673 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem wide849 : Wide 20 4 etat673 := widen (by decide +kernel) ban848
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban850 : Ban 40 5 etat661 := viaCut projCut_0_6 wide849 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban851 : Ban 40 5 etat662 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban852 : Ban 40 5 etat663 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban853 : Ban 40 5 etat664 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban854 : Ban 40 5 etat665 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban855 : Ban 40 5 etat666 := viaPerm projC0P0 projC0PInv0 ban847 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban856 : Ban 40 5 etat667 := viaPerm projC0P0 projC0PInv0 ban850 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban857 : Ban 40 5 etat668 := viaPerm projC0P0 projC0PInv0 ban851 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban858 : Ban 40 5 etat669 := viaPerm projC0P0 projC0PInv0 ban852 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban859 : Ban 40 5 etat670 := viaPerm projC0P0 projC0PInv0 ban853 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban860 : Ban 40 5 etat671 := viaPerm projC0P0 projC0PInv0 ban854 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban861 : Ban 40 5 etat672 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban862 : Ban 40 4 etat161 := viaPerm projC0P1 projC0PInv1 ban760 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban863 : Ban 40 4 etat162 := viaPerm projC0P1 projC0PInv1 ban761 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban864 : Ban 40 4 etat163 := viaPerm projC0P1 projC0PInv1 ban762 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban865 : Ban 40 4 etat164 := viaPerm projC0P1 projC0PInv1 ban763 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban866 : Ban 40 4 etat165 := viaPerm projC0P1 projC0PInv1 ban764 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban867 : Ban 40 4 etat166 := viaPerm projC0P1 projC0PInv1 ban765 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban868 : Ban 40 4 etat167 := viaPerm projC0P1 projC0PInv1 ban766 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban869 : Ban 40 4 etat168 := viaPerm projC0P1 projC0PInv1 ban767 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban870 : Ban 40 4 etat169 := viaPerm projC0P1 projC0PInv1 ban768 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban871 : Ban 40 4 etat170 := viaPerm projC0P1 projC0PInv1 ban769 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban872 : Ban 40 4 etat171 := viaPerm projC0P1 projC0PInv1 ban770 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban873 : Ban 40 4 etat172 := viaPerm projC0P1 projC0PInv1 ban771 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban874 : Ban 40 4 etat173 := viaPerm projC0P0 projC0PInv0 ban868 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban875 : Ban 40 4 etat174 := viaPerm projC0P0 projC0PInv0 ban869 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban876 : Ban 40 4 etat175 := viaPerm projC0P0 projC0PInv0 ban870 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban877 : Ban 40 4 etat176 := viaPerm projC0P0 projC0PInv0 ban871 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban878 : Ban 40 4 etat177 := viaPerm projC0P0 projC0PInv0 ban872 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban879 : Ban 40 4 etat178 := viaPerm projC0P0 projC0PInv0 ban873 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban880 : Ban 20 3 etat179 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban881 : Ban 89 7 etat674 := viaCut projCut_top_2 wide309 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban882 : Ban 89 7 etat675 := viaCut projCut_top_13 wide608 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban883 : Ban 89 7 etat676 := viaCut projCut_top_18 wide44 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban884 : Ban 20 3 etat397 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban885 : Ban 20 3 etat677 := viaPerm projC7P1 projC7PInv1 ban3 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban886 : Ban 20 3 etat678 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban887 : Ban 20 3 etat677 := viaPerm projC10P2 projC10PInv2 ban31 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban888 : Ban 20 3 etat678 := viaPerm projC10P2 projC10PInv2 ban613 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban889 : Ban 28 4 etat679 := viaPerm projC3P7 projC3PInv7 ban615 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban890 : Ban 28 4 etat680 := viaPerm projC3P3 projC3PInv3 ban889 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban891 : Ban 28 4 etat681 := viaPerm projC3P7 projC3PInv7 ban614 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban892 : Ban 28 4 etat682 := viaPerm projC3P7 projC3PInv7 ban617 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban893 : Ban 28 4 etat683 := viaPerm projC3P7 projC3PInv7 ban618 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban894 : Ban 28 3 etat684 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban895 : Ban 28 3 etat685 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban896 : Ban 40 5 etat686 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban897 : Ban 40 3 etat687 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban898 : Ban 40 3 etat688 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban899 : Ban 40 5 etat686 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban900 : Ban 40 3 etat687 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban901 : Ban 40 3 etat688 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban902 : Ban 89 7 etat689 := viaCut projCut_top_2 wide309 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban903 : Ban 89 7 etat690 := viaCut projCut_top_14 wide710 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban904 : Ban 89 7 etat691 := viaCut projCut_top_18 wide44 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban905 : Ban 20 3 etat455 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban906 : Ban 20 3 etat456 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban907 : Ban 20 3 etat457 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban908 : Ban 20 3 etat692 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban909 : Ban 20 3 etat693 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban910 : Ban 20 3 etat694 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban911 : Ban 20 3 etat692 := viaPerm projC10P2 projC10PInv2 ban691 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban912 : Ban 20 3 etat693 := viaPerm projC10P2 projC10PInv2 ban692 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban913 : Ban 20 3 etat694 := viaPerm projC10P2 projC10PInv2 ban693 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban914 : Ban 28 4 etat695 := viaPerm projC3P7 projC3PInv7 ban695 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban915 : Ban 28 4 etat696 := viaPerm projC3P3 projC3PInv3 ban914 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban916 : Ban 28 4 etat697 := viaPerm projC3P7 projC3PInv7 ban694 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban917 : Ban 28 4 etat698 := viaPerm projC3P7 projC3PInv7 ban697 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban918 : Ban 28 4 etat699 := viaPerm projC3P7 projC3PInv7 ban698 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban919 : Ban 28 3 etat700 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban920 : Ban 28 3 etat701 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban921 : Ban 28 3 etat702 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban922 : Ban 40 5 etat703 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban923 : Ban 40 3 etat704 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban924 : Ban 40 3 etat705 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban925 : Ban 40 5 etat703 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban926 : Ban 40 3 etat704 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban927 : Ban 40 3 etat705 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban928 : Ban 89 7 etat706 := viaCut projCut_top_2 wide309 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban929 : Ban 89 7 etat707 := viaCut projCut_top_14 wide710 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban930 : Ban 89 7 etat708 := viaPerm projTopP0 projTopPInv0 ban883 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban931 : Ban 89 7 etat709 := viaPerm projTopP0 projTopPInv0 ban902 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban932 : Ban 89 7 etat710 := viaPerm projTopP0 projTopPInv0 ban903 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban933 : Ban 89 7 etat711 := viaPerm projTopP0 projTopPInv0 ban904 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban934 : Ban 89 7 etat712 := viaPerm projTopP0 projTopPInv0 ban928 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban935 : Ban 89 7 etat713 := viaPerm projTopP0 projTopPInv0 ban929 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban936 : Ban 89 7 etat714 := viaCut projCut_top_7 wide541 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban937 : Ban 45 5 etat715 := viaPerm projC2P5 projC2PInv5 ban137 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban938 : Ban 45 5 etat716 := viaPerm projC2P5 projC2PInv5 ban200 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban939 : Ban 45 5 etat717 := viaPerm projC2P1 projC2PInv1 ban666 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban940 : Ban 45 5 etat718 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban941 : Ban 45 5 etat719 := viaPerm projC2P1 projC2PInv1 ban940 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban942 : Ban 45 5 etat720 := viaPerm projC2P6 projC2PInv6 ban661 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban943 : Ban 45 5 etat721 := viaPerm projC2P6 projC2PInv6 ban659 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban944 : Ban 45 5 etat722 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban945 : Ban 45 5 etat723 := viaPerm projC2P3 projC2PInv3 ban534 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban946 : Ban 45 5 etat724 := viaPerm projC2P3 projC2PInv3 ban601 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban947 : Ban 45 5 etat725 := viaPerm projC2P5 projC2PInv5 ban939 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban948 : Ban 45 5 etat726 := viaPerm projC2P5 projC2PInv5 ban940 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban949 : Ban 45 5 etat727 := viaPerm projC2P1 projC2PInv1 ban947 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban950 : Ban 45 5 etat728 := viaPerm projC2P1 projC2PInv1 ban948 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban951 : Ban 45 5 etat729 := viaPerm projC2P0 projC2PInv0 ban661 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban952 : Ban 45 5 etat730 := viaPerm projC2P5 projC2PInv5 ban670 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban953 : Ban 45 5 etat731 := viaPerm projC2P0 projC2PInv0 ban659 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban954 : Ban 45 5 etat732 := viaPerm projC2P5 projC2PInv5 ban944 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban955 : Ban 45 5 etat733 := viaPerm projC2P5 projC2PInv5 ban945 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban956 : Ban 45 5 etat734 := viaPerm projC2P5 projC2PInv5 ban946 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban957 : Ban 45 5 etat735 := viaCut projCut_2_13 wide608 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban958 : Ban 45 5 etat736 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban959 : Ban 45 5 etat737 := viaPerm projC2P1 projC2PInv1 ban958 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban960 : Ban 45 5 etat738 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban961 : Ban 45 5 etat739 := viaPerm projC2P1 projC2PInv1 ban960 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban962 : Ban 45 5 etat740 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban963 : Ban 45 5 etat741 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban964 : Ban 45 5 etat742 := viaPerm projC2P1 projC2PInv1 ban962 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban965 : Ban 45 5 etat743 := viaPerm projC2P1 projC2PInv1 ban963 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban966 : Ban 6 2 etat291 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem wide967 : Wide 6 2 etat291 := widen (by decide +kernel) ban966
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban968 : Ban 45 5 etat744 := viaCut projCut_2_27 wide967 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban969 : Ban 20 3 etat296 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem wide970 : Wide 20 3 etat296 := widen (by decide +kernel) ban969
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban971 : Ban 45 5 etat745 := viaCut projCut_2_15 wide970 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban972 : Ban 45 5 etat746 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban973 : Ban 45 5 etat747 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban974 : Ban 45 5 etat748 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban975 : Ban 45 5 etat749 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban976 : Ban 45 5 etat750 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban977 : Ban 45 5 etat751 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban978 : Ban 45 6 etat223 := viaBranch (ws := [etat31,etat92,etat715,etat141,etat716,etat717,etat718,etat560,etat719,etat720,etat564,etat721,etat722,etat723,etat724,etat725,etat726,etat727,etat728,etat729,etat730,etat731,etat732,etat733,etat734,etat735,etat736,etat737,etat738,etat739,etat225,etat740,etat741,etat224,etat742,etat743,etat744,etat745,etat746,etat747,etat748,etat749,etat750,etat751]) (consBan ban69 (consBan ban137 (consBan ban937 (consBan ban200 (consBan ban938 (consBan ban939 (consBan ban940 (consBan ban666 (consBan ban941 (consBan ban942 (consBan ban670 (consBan ban943 (consBan ban944 (consBan ban945 (consBan ban946 (consBan ban947 (consBan ban948 (consBan ban949 (consBan ban950 (consBan ban951 (consBan ban952 (consBan ban953 (consBan ban954 (consBan ban955 (consBan ban956 (consBan ban957 (consBan ban958 (consBan ban959 (consBan ban960 (consBan ban961 (consBan ban299 (consBan ban962 (consBan ban963 (consBan ban298 (consBan ban964 (consBan ban965 (consBan ban968 (consBan ban971 (consBan ban972 (consBan ban973 (consBan ban974 (consBan ban975 (consBan ban976 (consBan ban977 (nilBan _ _))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem wide979 : Wide 45 6 etat223 := viaSub (ws := [etat234,etat223]) (consBan ban308 (consBan ban978 (nilBan _ _))) (by decide) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban980 : Ban 89 7 etat752 := viaCut projCut_top_2 wide979 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban981 : Ban 89 7 etat753 := viaCut projCut_top_7 wide541 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban982 : Ban 89 7 etat754 := viaCut projCut_top_14 wide710 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban983 : Ban 89 7 etat755 := viaPerm projTopP0 projTopPInv0 ban936 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban984 : Ban 89 7 etat756 := viaPerm projTopP0 projTopPInv0 ban980 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban985 : Ban 89 7 etat757 := viaPerm projTopP0 projTopPInv0 ban981 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban986 : Ban 89 7 etat758 := viaPerm projTopP0 projTopPInv0 ban982 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban987 : Ban 20 4 etat296 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem wide988 : Wide 20 4 etat296 := widen (by decide +kernel) ban987
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban989 : Ban 89 7 etat759 := viaCut projCut_top_15 wide988 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban990 : Ban 45 6 etat231 := viaPerm projC2P2 projC2PInv2 ban978 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem wide991 : Wide 45 6 etat231 := viaSub (ws := [etat234,etat231]) (consBan ban308 (consBan ban990 (nilBan _ _))) (by decide) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban992 : Ban 89 7 etat760 := viaCut projCut_top_2 wide991 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban993 : Ban 89 7 etat761 := viaCut projCut_top_14 wide710 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban994 : Ban 89 7 etat762 := viaPerm projTopP0 projTopPInv0 ban993 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem ban995 : Ban 89 8 etat763 := viaBranch (ws := [etat9,etat43,etat104,etat105,etat106,etat152,etat153,etat154,etat155,etat156,etat235,etat289,etat290,etat337,etat338,etat394,etat395,etat396,etat452,etat453,etat454,etat511,etat512,etat513,etat526,etat575,etat576,etat592,etat593,etat594,etat595,etat596,etat597,etat598,etat599,etat600,etat601,etat602,etat603,etat604,etat605,etat606,etat607,etat608,etat609,etat610,etat611,etat612,etat613,etat614,etat615,etat616,etat617,etat618,etat619,etat620,etat621,etat622,etat623,etat624,etat625,etat626,etat629,etat633,etat634,etat641,etat642,etat674,etat675,etat676,etat689,etat690,etat691,etat706,etat707,etat708,etat709,etat710,etat711,etat712,etat713,etat714,etat752,etat753,etat754,etat755,etat756,etat757,etat758,etat759,etat760,etat761,etat762]) (consBan ban45 (consBan ban82 (consBan ban150 (consBan ban151 (consBan ban152 (consBan ban213 (consBan ban214 (consBan ban215 (consBan ban216 (consBan ban217 (consBan ban310 (consBan ban366 (consBan ban367 (consBan ban418 (consBan ban419 (consBan ban478 (consBan ban479 (consBan ban480 (consBan ban539 (consBan ban542 (consBan ban543 (consBan ban606 (consBan ban609 (consBan ban610 (consBan ban627 (consBan ban683 (consBan ban684 (consBan ban708 (consBan ban711 (consBan ban712 (consBan ban713 (consBan ban714 (consBan ban715 (consBan ban716 (consBan ban717 (consBan ban718 (consBan ban719 (consBan ban720 (consBan ban721 (consBan ban722 (consBan ban723 (consBan ban724 (consBan ban725 (consBan ban726 (consBan ban727 (consBan ban728 (consBan ban729 (consBan ban730 (consBan ban731 (consBan ban732 (consBan ban733 (consBan ban734 (consBan ban735 (consBan ban736 (consBan ban737 (consBan ban738 (consBan ban739 (consBan ban740 (consBan ban741 (consBan ban742 (consBan ban743 (consBan ban744 (consBan ban751 (consBan ban778 (consBan ban779 (consBan ban792 (consBan ban793 (consBan ban881 (consBan ban882 (consBan ban883 (consBan ban902 (consBan ban903 (consBan ban904 (consBan ban928 (consBan ban929 (consBan ban930 (consBan ban931 (consBan ban932 (consBan ban933 (consBan ban934 (consBan ban935 (consBan ban936 (consBan ban980 (consBan ban981 (consBan ban982 (consBan ban983 (consBan ban984 (consBan ban985 (consBan ban986 (consBan ban989 (consBan ban992 (consBan ban993 (consBan ban994 (nilBan _ _)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem sixWide : Wide 89 8 etat763 := widen (by decide +kernel) ban995
def certRows : List Nat := [9,9,9,9,9,9,9,9,10,10,10,10,10,10,10,10,17,17,17,17,17,17,17,17,18,18,18,18,18,18,18,18,20,20,20,20,20,20,20,24,24,24,24,24,24,24,24,24,33,33,33,33,33,33,33,33,34,34,34,34,34,34,34,34,36,36,36,36,36,36,36,40,40,40,40,40,40,40,40,40,48,48,48,48,48,48,48,48,48,0,3,5,7,8,12,16,32,0,3,6,7,8,12,16,32,0,3,5,7,8,12,16,32,0,3,6,7,8,12,16,32,0,5,6,7,12,16,32,0,3,5,6,7,8,12,16,32,0,3,5,7,8,12,16,32,0,3,6,7,8,12,16,32,0,5,6,7,12,16,32,0,3,5,6,7,8,12,16,32,0,3,5,6,7,8,12,16,32]
def certEtat : List ℕ := etat763
def certM : Nat := 89
def certFuel : Nat := 8

end PEqualNP.Outside.L_meta_28330.ArchivedClique

namespace PEqualNP.Outside.L_meta_28330.Reduce
namespace CliqueCertificate
open PEqualNP.Outside.L_meta_28330.ArchivedClique
def rows : List Nat := certRows
def pack (w : BitVec 64) := actL rows (canon w).toNat
private def mix (s t : Bool) (a b : BitVec 64) : BitVec 64 :=
  if s then (if t then a ||| b else b ^^^ (a &&& b))
  else if t then a ^^^ (a &&& b) else a &&& b
private theorem mix_correct (x y : BitVec 64) :
    canon (x &&& y) = mix (x.getLsbD 0) (y.getLsbD 0) (canon x) (canon y) := by
  cases hx : x.getLsbD 0 <;> cases hy : y.getLsbD 0 <;>
    apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
    cases hp : x.getLsbD i <;> cases hq : y.getLsbD i <;>
    simp only [canon, mix, BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_xor,
      BitVec.getLsbD_or, hx, hy, hp, hq, decide_eq_true hi, Bool.false_and, Bool.true_and, ite_false, ite_true, Bool.false_eq_true] <;> rfl
private theorem pack_mix (s t : Bool) (a b : BitVec 64) :
    actL rows (mix s t a b).toNat = combine (opIndex s t) (actL rows a.toNat) (actL rows b.toNat) := by
  cases s <;> cases t <;> simp [mix, opIndex, combine, BitVec.toNat_xor, BitVec.toNat_and, BitVec.toNat_or, actL_and, actL_or, actL_xor]
private theorem canon_signed (s : Bool) (x : BitVec 64) : canon (signed s x) = canon x := by
  cases s; rfl; exact canon_not x
private theorem pack_gate (s t : Bool) (a b : BitVec 64) :
    ∃ d < 4, pack (gate s t a b) = combine d (pack a) (pack b) := by
  let x := signed s a; let y := signed t b
  refine ⟨opIndex (x.getLsbD 0) (y.getLsbD 0), op_lt _ _, ?_⟩
  change actL rows (canon (canon (x &&& y))).toNat = _
  rw [canon_canon, mix_correct, pack_mix]; simp [x, y, pack, canon_signed]
private theorem word_sep : Good certM (pack cliqueGoal) := by
  intro i hi
  have h : ∀ j : Fin certM, (pack cliqueGoal).testBit j.val ≠ (pack cliqueGoal).testBit (certM+j.val) := by decide +kernel
  exact h ⟨i,hi⟩
theorem possible {k S} (h : Path cliqueGoal k S) {av : List Nat}
    (carry : ∀ w∈S, pack w ∈ av) : Possible certM k av := by
  apply h (fun n T => ∀ av : List Nat, (∀ w∈T, pack w ∈ av) → Possible certM n av) ?_ ?_ av carry
  · intro v yes; refine ⟨0,{pack cliqueGoal},le_rfl,?_,?_⟩
    · exact PEqualNP.Outside.L_meta_28330.ArchivedClique.Live.done word_sep (by decide +kernel)
    · simpa using yes cliqueGoal (by simp)
  · intro k a b U s t _ _ _ ih v yes
    obtain ⟨d,hd,hop⟩ := pack_gate s t a b
    have future : Possible certM k (v ++ [combine d (pack a) (pack b)]) := by
      apply ih; intro w hw; rcases Finset.mem_insert.mp hw with rfl | old
      · simp [hop]
      · exact List.mem_append_left _ (yes w (by simp [old]))
    obtain ⟨n,T,le,live,mem⟩ := pullPaid hd (yes _ (by simp)) (yes _ (by simp)) future
    refine ⟨n,T,?_,live,mem⟩; cases h : charge v (combine d (pack a) (pack b)) <;> simp [h] at le <;> omega
theorem lower (k : Nat) (T : Finset (BitVec 64)) (raw : T ⊆ cliqueRaw.toFinset)
    (path : Path cliqueGoal k T) : 9 ≤ k := by
  by_contra! short
  have tick : ∀ w∈cliqueRaw, pack w ∈ certEtat := by simp [cliqueRaw]; decide +kernel
  obtain ⟨n,S,le,live,inc⟩ := possible path (fun w hw => tick w (List.mem_toFinset.mp (raw hw)))
  exact sixWide ⟨n,S,by omega,live,inc⟩
end CliqueCertificate
end PEqualNP.Outside.L_meta_28330.Reduce

theorem PEqualNP.Outside.L_meta_28330 : (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) := by
  apply PEqualNP.Outside.L_meta_28330.Frame.finish
  intro gs o legal computes hn
  obtain ⟨b,n,hlen,live⟩ := PEqualNP.Outside.L_meta_28330.freely_chain gs o legal computes hn
  obtain ⟨k,hk,T,sub,path⟩ := PEqualNP.Outside.L_meta_28330.Reduce.to_six live
  have low := PEqualNP.Outside.L_meta_28330.Reduce.CliqueCertificate.lower k T sub path
  omega
